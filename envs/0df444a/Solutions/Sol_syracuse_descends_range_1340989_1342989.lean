-- Prove2me | solution 1 for syracuse_descends_range_1340989_1342989
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:45.336056+00:00
-- url     : https://prove2.me/submissions/ff062256-5aee-41ab-9def-0ba66cac2da9

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


theorem B2547749 : Blo 1340989 2547749 := bbase (se 4 (by rfl) ⟨238851, by rfl⟩ : syracuseStep 2547749 = 477703) (by norm_num)
theorem B8601653 : Blo 1340989 8601653 := bbase (se 5 (by rfl) ⟨403202, by rfl⟩ : syracuseStep 8601653 = 806405) (by norm_num)
theorem B10190933 : Blo 1340989 10190933 := bbase (se 8 (by rfl) ⟨59712, by rfl⟩ : syracuseStep 10190933 = 119425) (by norm_num)
theorem B4358261 : Blo 1340989 4358261 := bbase (se 5 (by rfl) ⟨204293, by rfl⟩ : syracuseStep 4358261 = 408587) (by norm_num)
theorem B1433801 : Blo 1340989 1433801 := bbase (se 2 (by rfl) ⟨537675, by rfl⟩ : syracuseStep 1433801 = 1075351) (by norm_num)
theorem B4079861 : Blo 1340989 4079861 := bbase (se 5 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 4079861 = 382487) (by norm_num)
theorem B7258357 : Blo 1340989 7258357 := bbase (se 5 (by rfl) ⟨340235, by rfl⟩ : syracuseStep 7258357 = 680471) (by norm_num)
theorem B4530437 : Blo 1340989 4530437 := bbase (se 4 (by rfl) ⟨424728, by rfl⟩ : syracuseStep 4530437 = 849457) (by norm_num)
theorem B4079909 : Blo 1340989 4079909 := bbase (se 4 (by rfl) ⟨382491, by rfl⟩ : syracuseStep 4079909 = 764983) (by norm_num)
theorem B6447397 : Blo 1340989 6447397 := bbase (se 4 (by rfl) ⟨604443, by rfl⟩ : syracuseStep 6447397 = 1208887) (by norm_num)
theorem B6447413 : Blo 1340989 6447413 := bbase (se 5 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 6447413 = 604445) (by norm_num)
theorem B5734709 : Blo 1340989 5734709 := bbase (se 5 (by rfl) ⟨268814, by rfl⟩ : syracuseStep 5734709 = 537629) (by norm_num)
theorem B2548037 : Blo 1340989 2548037 := bbase (se 4 (by rfl) ⟨238878, by rfl⟩ : syracuseStep 2548037 = 477757) (by norm_num)
theorem B6791525 : Blo 1340989 6791525 := bbase (se 4 (by rfl) ⟨636705, by rfl⟩ : syracuseStep 6791525 = 1273411) (by norm_num)
theorem B2417045 : Blo 1340989 2417045 := bbase (se 6 (by rfl) ⟨56649, by rfl⟩ : syracuseStep 2417045 = 113299) (by norm_num)
theorem B2580893 : Blo 1340989 2580893 := bbase (se 3 (by rfl) ⟨483917, by rfl⟩ : syracuseStep 2580893 = 967835) (by norm_num)
theorem B4301237 : Blo 1340989 4301237 := bbase (se 5 (by rfl) ⟨201620, by rfl⟩ : syracuseStep 4301237 = 403241) (by norm_num)
theorem B10887605 : Blo 1340989 10887605 := bbase (se 5 (by rfl) ⟨510356, by rfl⟩ : syracuseStep 10887605 = 1020713) (by norm_num)
theorem B5439941 : Blo 1340989 5439941 := bbase (se 4 (by rfl) ⟨509994, by rfl⟩ : syracuseStep 5439941 = 1019989) (by norm_num)
theorem B2867653 : Blo 1340989 2867653 := bbase (se 4 (by rfl) ⟨268842, by rfl⟩ : syracuseStep 2867653 = 537685) (by norm_num)
theorem B2548189 : Blo 1340989 2548189 := bbase (se 3 (by rfl) ⟨477785, by rfl⟩ : syracuseStep 2548189 = 955571) (by norm_num)
theorem B10183157 : Blo 1340989 10183157 := bbase (se 5 (by rfl) ⟨477335, by rfl⟩ : syracuseStep 10183157 = 954671) (by norm_num)
theorem B27927125 : Blo 1340989 27927125 := bbase (se 8 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 27927125 = 327271) (by norm_num)
theorem B10887797 : Blo 1340989 10887797 := bbase (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) (by norm_num)
theorem B1360549 : Blo 1340989 1360549 := bbase (se 4 (by rfl) ⟨127551, by rfl⟩ : syracuseStep 1360549 = 255103) (by norm_num)
theorem B4530869 : Blo 1340989 4530869 := bbase (se 5 (by rfl) ⟨212384, by rfl⟩ : syracuseStep 4530869 = 424769) (by norm_num)
theorem B2179813 : Blo 1340989 2179813 := bbase (se 4 (by rfl) ⟨204357, by rfl⟩ : syracuseStep 2179813 = 408715) (by norm_num)
theorem B2548493 : Blo 1340989 2548493 := bbase (se 3 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 2548493 = 955685) (by norm_num)
theorem B2720621 : Blo 1340989 2720621 := bbase (se 3 (by rfl) ⟨510116, by rfl⟩ : syracuseStep 2720621 = 1020233) (by norm_num)
theorem B2040709 : Blo 1340989 2040709 := bbase (se 4 (by rfl) ⟨191316, by rfl⟩ : syracuseStep 2040709 = 382633) (by norm_num)
theorem B1909661 : Blo 1340989 1909661 := bbase (se 3 (by rfl) ⟨358061, by rfl⟩ : syracuseStep 1909661 = 716123) (by norm_num)
theorem B2868149 : Blo 1340989 2868149 := bbase (se 5 (by rfl) ⟨134444, by rfl⟩ : syracuseStep 2868149 = 268889) (by norm_num)
theorem B2040781 : Blo 1340989 2040781 := bbase (se 3 (by rfl) ⟨382646, by rfl⟩ : syracuseStep 2040781 = 765293) (by norm_num)
theorem B6202325 : Blo 1340989 6202325 := bbase (se 7 (by rfl) ⟨72683, by rfl⟩ : syracuseStep 6202325 = 145367) (by norm_num)
theorem B9675733 : Blo 1340989 9675733 := bbase (se 7 (by rfl) ⟨113387, by rfl⟩ : syracuseStep 9675733 = 226775) (by norm_num)
theorem B1721417 : Blo 1340989 1721417 := bbase (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) (by norm_num)
theorem B4531301 : Blo 1340989 4531301 := bbase (se 4 (by rfl) ⟨424809, by rfl⟩ : syracuseStep 4531301 = 849619) (by norm_num)
theorem B4359413 : Blo 1340989 4359413 := bbase (se 5 (by rfl) ⟨204347, by rfl⟩ : syracuseStep 4359413 = 408695) (by norm_num)
theorem B1508629 : Blo 1340989 1508629 := bbase (se 6 (by rfl) ⟨35358, by rfl⟩ : syracuseStep 1508629 = 70717) (by norm_num)
theorem B5735717 : Blo 1340989 5735717 := bbase (se 4 (by rfl) ⟨537723, by rfl⟩ : syracuseStep 5735717 = 1075447) (by norm_num)
theorem B1508665 : Blo 1340989 1508665 := bbase (se 2 (by rfl) ⟨565749, by rfl⟩ : syracuseStep 1508665 = 1131499) (by norm_num)
theorem B3818821 : Blo 1340989 3818821 := bbase (se 4 (by rfl) ⟨358014, by rfl⟩ : syracuseStep 3818821 = 716029) (by norm_num)
theorem B5096789 : Blo 1340989 5096789 := bbase (se 12 (by rfl) ⟨1866, by rfl⟩ : syracuseStep 5096789 = 3733) (by norm_num)
theorem B1508701 : Blo 1340989 1508701 := bbase (se 3 (by rfl) ⟨282881, by rfl⟩ : syracuseStep 1508701 = 565763) (by norm_num)
theorem B1508737 : Blo 1340989 1508737 := bbase (se 2 (by rfl) ⟨565776, by rfl⟩ : syracuseStep 1508737 = 1131553) (by norm_num)
theorem B1508773 : Blo 1340989 1508773 := bbase (se 4 (by rfl) ⟨141447, by rfl⟩ : syracuseStep 1508773 = 282895) (by norm_num)
theorem B1697213 : Blo 1340989 1697213 := bbase (se 3 (by rfl) ⟨318227, by rfl⟩ : syracuseStep 1697213 = 636455) (by norm_num)
theorem B1508809 : Blo 1340989 1508809 := bbase (se 2 (by rfl) ⟨565803, by rfl⟩ : syracuseStep 1508809 = 1131607) (by norm_num)
theorem B4253141 : Blo 1340989 4253141 := bbase (se 7 (by rfl) ⟨49841, by rfl⟩ : syracuseStep 4253141 = 99683) (by norm_num)
theorem B3818981 : Blo 1340989 3818981 := bbase (se 4 (by rfl) ⟨358029, by rfl⟩ : syracuseStep 3818981 = 716059) (by norm_num)
theorem B1508845 : Blo 1340989 1508845 := bbase (se 3 (by rfl) ⟨282908, by rfl⟩ : syracuseStep 1508845 = 565817) (by norm_num)
theorem B1697269 : Blo 1340989 1697269 := bbase (se 5 (by rfl) ⟨79559, by rfl⟩ : syracuseStep 1697269 = 159119) (by norm_num)
theorem B9799157 : Blo 1340989 9799157 := bbase (se 5 (by rfl) ⟨459335, by rfl⟩ : syracuseStep 9799157 = 918671) (by norm_num)
theorem B4302325 : Blo 1340989 4302325 := bbase (se 5 (by rfl) ⟨201671, by rfl⟩ : syracuseStep 4302325 = 403343) (by norm_num)
theorem B2549245 : Blo 1340989 2549245 := bbase (se 3 (by rfl) ⟨477983, by rfl⟩ : syracuseStep 2549245 = 955967) (by norm_num)
theorem B1508881 : Blo 1340989 1508881 := bbase (se 2 (by rfl) ⟨565830, by rfl⟩ : syracuseStep 1508881 = 1131661) (by norm_num)
theorem B4531733 : Blo 1340989 4531733 := bbase (se 6 (by rfl) ⟨106212, by rfl⟩ : syracuseStep 4531733 = 212425) (by norm_num)
theorem B1508917 : Blo 1340989 1508917 := bbase (se 5 (by rfl) ⟨70730, by rfl⟩ : syracuseStep 1508917 = 141461) (by norm_num)
theorem B1697365 : Blo 1340989 1697365 := bbase (se 8 (by rfl) ⟨9945, by rfl⟩ : syracuseStep 1697365 = 19891) (by norm_num)
theorem B19613269 : Blo 1340989 19613269 := bbase (se 8 (by rfl) ⟨114921, by rfl⟩ : syracuseStep 19613269 = 229843) (by norm_num)
theorem B1508953 : Blo 1340989 1508953 := bbase (se 2 (by rfl) ⟨565857, by rfl⟩ : syracuseStep 1508953 = 1131715) (by norm_num)
theorem B6792821 : Blo 1340989 6792821 := bbase (se 5 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 6792821 = 636827) (by norm_num)
theorem B5097077 : Blo 1340989 5097077 := bbase (se 5 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 5097077 = 477851) (by norm_num)
theorem B1508989 : Blo 1340989 1508989 := bbase (se 3 (by rfl) ⟨282935, by rfl⟩ : syracuseStep 1508989 = 565871) (by norm_num)
theorem B1910413 : Blo 1340989 1910413 := bbase (se 3 (by rfl) ⟨358202, by rfl⟩ : syracuseStep 1910413 = 716405) (by norm_num)
theorem B2549389 : Blo 1340989 2549389 := bbase (se 3 (by rfl) ⟨478010, by rfl⟩ : syracuseStep 2549389 = 956021) (by norm_num)
theorem B1509025 : Blo 1340989 1509025 := bbase (se 2 (by rfl) ⟨565884, by rfl⟩ : syracuseStep 1509025 = 1131769) (by norm_num)
theorem B1509061 : Blo 1340989 1509061 := bbase (se 4 (by rfl) ⟨141474, by rfl⟩ : syracuseStep 1509061 = 282949) (by norm_num)
theorem B3819221 : Blo 1340989 3819221 := bbase (se 7 (by rfl) ⟨44756, by rfl⟩ : syracuseStep 3819221 = 89513) (by norm_num)
theorem B1509097 : Blo 1340989 1509097 := bbase (se 2 (by rfl) ⟨565911, by rfl⟩ : syracuseStep 1509097 = 1131823) (by norm_num)
theorem B1697537 : Blo 1340989 1697537 := bbase (se 2 (by rfl) ⟨636576, by rfl⟩ : syracuseStep 1697537 = 1273153) (by norm_num)
theorem B1509133 : Blo 1340989 1509133 := bbase (se 3 (by rfl) ⟨282962, by rfl⟩ : syracuseStep 1509133 = 565925) (by norm_num)
theorem B2549549 : Blo 1340989 2549549 := bbase (se 3 (by rfl) ⟨478040, by rfl⟩ : syracuseStep 2549549 = 956081) (by norm_num)
theorem B1509169 : Blo 1340989 1509169 := bbase (se 2 (by rfl) ⟨565938, by rfl⟩ : syracuseStep 1509169 = 1131877) (by norm_num)
theorem B1697593 : Blo 1340989 1697593 := bbase (se 2 (by rfl) ⟨636597, by rfl⟩ : syracuseStep 1697593 = 1273195) (by norm_num)
theorem B1509205 : Blo 1340989 1509205 := bbase (se 9 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 1509205 = 8843) (by norm_num)
theorem B1509241 : Blo 1340989 1509241 := bbase (se 2 (by rfl) ⟨565965, by rfl⟩ : syracuseStep 1509241 = 1131931) (by norm_num)
theorem B3819413 : Blo 1340989 3819413 := bbase (se 6 (by rfl) ⟨89517, by rfl⟩ : syracuseStep 3819413 = 179035) (by norm_num)
theorem B1697689 : Blo 1340989 1697689 := bbase (se 2 (by rfl) ⟨636633, by rfl⟩ : syracuseStep 1697689 = 1273267) (by norm_num)
theorem B1509277 : Blo 1340989 1509277 := bbase (se 3 (by rfl) ⟨282989, by rfl⟩ : syracuseStep 1509277 = 565979) (by norm_num)
theorem B1509313 : Blo 1340989 1509313 := bbase (se 2 (by rfl) ⟨565992, by rfl⟩ : syracuseStep 1509313 = 1131985) (by norm_num)
theorem B4532165 : Blo 1340989 4532165 := bbase (se 4 (by rfl) ⟨424890, by rfl⟩ : syracuseStep 4532165 = 849781) (by norm_num)
theorem B4900837 : Blo 1340989 4900837 := bbase (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) (by norm_num)
theorem B1509349 : Blo 1340989 1509349 := bbase (se 4 (by rfl) ⟨141501, by rfl⟩ : syracuseStep 1509349 = 283003) (by norm_num)
theorem B2263045 : Blo 1340989 2263045 := bbase (se 4 (by rfl) ⟨212160, by rfl⟩ : syracuseStep 2263045 = 424321) (by norm_num)
theorem B1509385 : Blo 1340989 1509385 := bbase (se 2 (by rfl) ⟨566019, by rfl⟩ : syracuseStep 1509385 = 1132039) (by norm_num)
theorem B7645205 : Blo 1340989 7645205 := bbase (se 6 (by rfl) ⟨179184, by rfl⟩ : syracuseStep 7645205 = 358369) (by norm_num)
theorem B1509421 : Blo 1340989 1509421 := bbase (se 3 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 1509421 = 566033) (by norm_num)
theorem B1697861 : Blo 1340989 1697861 := bbase (se 4 (by rfl) ⟨159174, by rfl⟩ : syracuseStep 1697861 = 318349) (by norm_num)
theorem B1812557 : Blo 1340989 1812557 := bbase (se 3 (by rfl) ⟨339854, by rfl⟩ : syracuseStep 1812557 = 679709) (by norm_num)
theorem B1509457 : Blo 1340989 1509457 := bbase (se 2 (by rfl) ⟨566046, by rfl⟩ : syracuseStep 1509457 = 1132093) (by norm_num)
theorem B2263133 : Blo 1340989 2263133 := bbase (se 3 (by rfl) ⟨424337, by rfl⟩ : syracuseStep 2263133 = 848675) (by norm_num)
theorem B1509493 : Blo 1340989 1509493 := bbase (se 5 (by rfl) ⟨70757, by rfl⟩ : syracuseStep 1509493 = 141515) (by norm_num)
theorem B1697917 : Blo 1340989 1697917 := bbase (se 3 (by rfl) ⟨318359, by rfl⟩ : syracuseStep 1697917 = 636719) (by norm_num)
theorem B1509529 : Blo 1340989 1509529 := bbase (se 2 (by rfl) ⟨566073, by rfl⟩ : syracuseStep 1509529 = 1132147) (by norm_num)
theorem B5728421 : Blo 1340989 5728421 := bbase (se 4 (by rfl) ⟨537039, by rfl⟩ : syracuseStep 5728421 = 1074079) (by norm_num)
theorem B1509565 : Blo 1340989 1509565 := bbase (se 3 (by rfl) ⟨283043, by rfl⟩ : syracuseStep 1509565 = 566087) (by norm_num)
theorem B2582741 : Blo 1340989 2582741 := bbase (se 7 (by rfl) ⟨30266, by rfl⟩ : syracuseStep 2582741 = 60533) (by norm_num)
theorem B2263261 : Blo 1340989 2263261 := bbase (se 3 (by rfl) ⟨424361, by rfl⟩ : syracuseStep 2263261 = 848723) (by norm_num)
theorem B1698013 : Blo 1340989 1698013 := bbase (se 3 (by rfl) ⟨318377, by rfl⟩ : syracuseStep 1698013 = 636755) (by norm_num)
theorem B1509601 : Blo 1340989 1509601 := bbase (se 2 (by rfl) ⟨566100, by rfl⟩ : syracuseStep 1509601 = 1132201) (by norm_num)
theorem B1509637 : Blo 1340989 1509637 := bbase (se 4 (by rfl) ⟨141528, by rfl⟩ : syracuseStep 1509637 = 283057) (by norm_num)
theorem B1509673 : Blo 1340989 1509673 := bbase (se 2 (by rfl) ⟨566127, by rfl⟩ : syracuseStep 1509673 = 1132255) (by norm_num)
theorem B2263349 : Blo 1340989 2263349 := bbase (se 5 (by rfl) ⟨106094, by rfl⟩ : syracuseStep 2263349 = 212189) (by norm_num)
theorem B2148677 : Blo 1340989 2148677 := bbase (se 4 (by rfl) ⟨201438, by rfl⟩ : syracuseStep 2148677 = 402877) (by norm_num)
theorem B1509709 : Blo 1340989 1509709 := bbase (se 3 (by rfl) ⟨283070, by rfl⟩ : syracuseStep 1509709 = 566141) (by norm_num)
theorem B1509745 : Blo 1340989 1509745 := bbase (se 2 (by rfl) ⟨566154, by rfl⟩ : syracuseStep 1509745 = 1132309) (by norm_num)
theorem B1698185 : Blo 1340989 1698185 := bbase (se 2 (by rfl) ⟨636819, by rfl⟩ : syracuseStep 1698185 = 1273639) (by norm_num)
theorem B1509781 : Blo 1340989 1509781 := bbase (se 6 (by rfl) ⟨35385, by rfl⟩ : syracuseStep 1509781 = 70771) (by norm_num)
theorem B2148773 : Blo 1340989 2148773 := bbase (se 4 (by rfl) ⟨201447, by rfl⟩ : syracuseStep 2148773 = 402895) (by norm_num)
theorem B1911205 : Blo 1340989 1911205 := bbase (se 4 (by rfl) ⟨179175, by rfl⟩ : syracuseStep 1911205 = 358351) (by norm_num)
theorem B1550765 : Blo 1340989 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B2263477 : Blo 1340989 2263477 := bbase (se 5 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 2263477 = 212201) (by norm_num)
theorem B1509817 : Blo 1340989 1509817 := bbase (se 2 (by rfl) ⟨566181, by rfl⟩ : syracuseStep 1509817 = 1132363) (by norm_num)
theorem B1698241 : Blo 1340989 1698241 := bbase (se 2 (by rfl) ⟨636840, by rfl⟩ : syracuseStep 1698241 = 1273681) (by norm_num)
theorem B2148805 : Blo 1340989 2148805 := bbase (se 4 (by rfl) ⟨201450, by rfl⟩ : syracuseStep 2148805 = 402901) (by norm_num)
theorem B1509853 : Blo 1340989 1509853 := bbase (se 3 (by rfl) ⟨283097, by rfl⟩ : syracuseStep 1509853 = 566195) (by norm_num)
theorem B1509889 : Blo 1340989 1509889 := bbase (se 2 (by rfl) ⟨566208, by rfl⟩ : syracuseStep 1509889 = 1132417) (by norm_num)
theorem B2263565 : Blo 1340989 2263565 := bbase (se 3 (by rfl) ⟨424418, by rfl⟩ : syracuseStep 2263565 = 848837) (by norm_num)
theorem B8595989 : Blo 1340989 8595989 := bbase (se 6 (by rfl) ⟨201468, by rfl⟩ : syracuseStep 8595989 = 402937) (by norm_num)
theorem B1698337 : Blo 1340989 1698337 := bbase (se 2 (by rfl) ⟨636876, by rfl⟩ : syracuseStep 1698337 = 1273753) (by norm_num)
theorem B1509925 : Blo 1340989 1509925 := bbase (se 4 (by rfl) ⟨141555, by rfl⟩ : syracuseStep 1509925 = 283111) (by norm_num)
theorem B3017285 : Blo 1340989 3017285 := bbase (se 4 (by rfl) ⟨282870, by rfl⟩ : syracuseStep 3017285 = 565741) (by norm_num)
theorem B1509961 : Blo 1340989 1509961 := bbase (se 2 (by rfl) ⟨566235, by rfl⟩ : syracuseStep 1509961 = 1132471) (by norm_num)
theorem B1509997 : Blo 1340989 1509997 := bbase (se 3 (by rfl) ⟨283124, by rfl⟩ : syracuseStep 1509997 = 566249) (by norm_num)
theorem B6449797 : Blo 1340989 6449797 := bbase (se 4 (by rfl) ⟨604668, by rfl⟩ : syracuseStep 6449797 = 1209337) (by norm_num)
theorem B3017357 : Blo 1340989 3017357 := bbase (se 3 (by rfl) ⟨565754, by rfl⟩ : syracuseStep 3017357 = 1131509) (by norm_num)
theorem B2263693 : Blo 1340989 2263693 := bbase (se 3 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 2263693 = 848885) (by norm_num)
theorem B1510033 : Blo 1340989 1510033 := bbase (se 2 (by rfl) ⟨566262, by rfl⟩ : syracuseStep 1510033 = 1132525) (by norm_num)
theorem B1813141 : Blo 1340989 1813141 := bbase (se 6 (by rfl) ⟨42495, by rfl⟩ : syracuseStep 1813141 = 84991) (by norm_num)
theorem B1510069 : Blo 1340989 1510069 := bbase (se 5 (by rfl) ⟨70784, by rfl⟩ : syracuseStep 1510069 = 141569) (by norm_num)
theorem B1698509 : Blo 1340989 1698509 := bbase (se 3 (by rfl) ⟨318470, by rfl⟩ : syracuseStep 1698509 = 636941) (by norm_num)
theorem B3017429 : Blo 1340989 3017429 := bbase (se 7 (by rfl) ⟨35360, by rfl⟩ : syracuseStep 3017429 = 70721) (by norm_num)
theorem B39217877 : Blo 1340989 39217877 := bbase (se 7 (by rfl) ⟨459584, by rfl⟩ : syracuseStep 39217877 = 919169) (by norm_num)
theorem B12896981 : Blo 1340989 12896981 := bbase (se 7 (by rfl) ⟨151136, by rfl⟩ : syracuseStep 12896981 = 302273) (by norm_num)
theorem B1510105 : Blo 1340989 1510105 := bbase (se 2 (by rfl) ⟨566289, by rfl⟩ : syracuseStep 1510105 = 1132579) (by norm_num)
theorem B2263781 : Blo 1340989 2263781 := bbase (se 4 (by rfl) ⟨212229, by rfl⟩ : syracuseStep 2263781 = 424459) (by norm_num)
theorem B1911541 : Blo 1340989 1911541 := bbase (se 5 (by rfl) ⟨89603, by rfl⟩ : syracuseStep 1911541 = 179207) (by norm_num)
theorem B1510141 : Blo 1340989 1510141 := bbase (se 3 (by rfl) ⟨283151, by rfl⟩ : syracuseStep 1510141 = 566303) (by norm_num)
theorem B1698565 : Blo 1340989 1698565 := bbase (se 4 (by rfl) ⟨159240, by rfl⟩ : syracuseStep 1698565 = 318481) (by norm_num)
theorem B5098261 : Blo 1340989 5098261 := bbase (se 6 (by rfl) ⟨119490, by rfl⟩ : syracuseStep 5098261 = 238981) (by norm_num)
theorem B3017501 : Blo 1340989 3017501 := bbase (se 3 (by rfl) ⟨565781, by rfl⟩ : syracuseStep 3017501 = 1131563) (by norm_num)
theorem B1510177 : Blo 1340989 1510177 := bbase (se 2 (by rfl) ⟨566316, by rfl⟩ : syracuseStep 1510177 = 1132633) (by norm_num)
theorem B11627317 : Blo 1340989 11627317 := bbase (se 5 (by rfl) ⟨545030, by rfl⟩ : syracuseStep 11627317 = 1090061) (by norm_num)
theorem B1510213 : Blo 1340989 1510213 := bbase (se 4 (by rfl) ⟨141582, by rfl⟩ : syracuseStep 1510213 = 283165) (by norm_num)
theorem B3017573 : Blo 1340989 3017573 := bbase (se 4 (by rfl) ⟨282897, by rfl⟩ : syracuseStep 3017573 = 565795) (by norm_num)
theorem B2263909 : Blo 1340989 2263909 := bbase (se 4 (by rfl) ⟨212241, by rfl⟩ : syracuseStep 2263909 = 424483) (by norm_num)
theorem B1698661 : Blo 1340989 1698661 := bbase (se 4 (by rfl) ⟨159249, by rfl⟩ : syracuseStep 1698661 = 318499) (by norm_num)
theorem B1510249 : Blo 1340989 1510249 := bbase (se 2 (by rfl) ⟨566343, by rfl⟩ : syracuseStep 1510249 = 1132687) (by norm_num)
theorem B3820405 : Blo 1340989 3820405 := bbase (se 5 (by rfl) ⟨179081, by rfl⟩ : syracuseStep 3820405 = 358163) (by norm_num)
theorem B6794117 : Blo 1340989 6794117 := bbase (se 4 (by rfl) ⟨636948, by rfl⟩ : syracuseStep 6794117 = 1273897) (by norm_num)
theorem B1510285 : Blo 1340989 1510285 := bbase (se 3 (by rfl) ⟨283178, by rfl⟩ : syracuseStep 1510285 = 566357) (by norm_num)
theorem B3017645 : Blo 1340989 3017645 := bbase (se 3 (by rfl) ⟨565808, by rfl⟩ : syracuseStep 3017645 = 1131617) (by norm_num)
theorem B1510321 : Blo 1340989 1510321 := bbase (se 2 (by rfl) ⟨566370, by rfl⟩ : syracuseStep 1510321 = 1132741) (by norm_num)
theorem B2263997 : Blo 1340989 2263997 := bbase (se 3 (by rfl) ⟨424499, by rfl⟩ : syracuseStep 2263997 = 848999) (by norm_num)
theorem B1911757 : Blo 1340989 1911757 := bbase (se 3 (by rfl) ⟨358454, by rfl⟩ : syracuseStep 1911757 = 716909) (by norm_num)
theorem B1510357 : Blo 1340989 1510357 := bbase (se 7 (by rfl) ⟨17699, by rfl⟩ : syracuseStep 1510357 = 35399) (by norm_num)
theorem B3017717 : Blo 1340989 3017717 := bbase (se 5 (by rfl) ⟨141455, by rfl⟩ : syracuseStep 3017717 = 282911) (by norm_num)
theorem B1510393 : Blo 1340989 1510393 := bbase (se 2 (by rfl) ⟨566397, by rfl⟩ : syracuseStep 1510393 = 1132795) (by norm_num)
theorem B1698833 : Blo 1340989 1698833 := bbase (se 2 (by rfl) ⟨637062, by rfl⟩ : syracuseStep 1698833 = 1274125) (by norm_num)
theorem B1510429 : Blo 1340989 1510429 := bbase (se 3 (by rfl) ⟨283205, by rfl⟩ : syracuseStep 1510429 = 566411) (by norm_num)
theorem B2419741 : Blo 1340989 2419741 := bbase (se 3 (by rfl) ⟨453701, by rfl⟩ : syracuseStep 2419741 = 907403) (by norm_num)
theorem B3017789 : Blo 1340989 3017789 := bbase (se 3 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 3017789 = 1131671) (by norm_num)
theorem B2264125 : Blo 1340989 2264125 := bbase (se 3 (by rfl) ⟨424523, by rfl⟩ : syracuseStep 2264125 = 849047) (by norm_num)
theorem B1510465 : Blo 1340989 1510465 := bbase (se 2 (by rfl) ⟨566424, by rfl⟩ : syracuseStep 1510465 = 1132849) (by norm_num)
theorem B5098565 : Blo 1340989 5098565 := bbase (se 4 (by rfl) ⟨477990, by rfl⟩ : syracuseStep 5098565 = 955981) (by norm_num)
theorem B1698889 : Blo 1340989 1698889 := bbase (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) (by norm_num)
theorem B31009877 : Blo 1340989 31009877 := bbase (se 8 (by rfl) ⟨181698, by rfl⟩ : syracuseStep 31009877 = 363397) (by norm_num)
theorem B1510501 : Blo 1340989 1510501 := bbase (se 4 (by rfl) ⟨141609, by rfl⟩ : syracuseStep 1510501 = 283219) (by norm_num)
theorem B2419813 : Blo 1340989 2419813 := bbase (se 4 (by rfl) ⟨226857, by rfl⟩ : syracuseStep 2419813 = 453715) (by norm_num)
theorem B3394669 : Blo 1340989 3394669 := bbase (se 3 (by rfl) ⟨636500, by rfl⟩ : syracuseStep 3394669 = 1273001) (by norm_num)
theorem B3017861 : Blo 1340989 3017861 := bbase (se 4 (by rfl) ⟨282924, by rfl⟩ : syracuseStep 3017861 = 565849) (by norm_num)
theorem B1510537 : Blo 1340989 1510537 := bbase (se 2 (by rfl) ⟨566451, by rfl⟩ : syracuseStep 1510537 = 1132903) (by norm_num)
theorem B2264213 : Blo 1340989 2264213 := bbase (se 6 (by rfl) ⟨53067, by rfl⟩ : syracuseStep 2264213 = 106135) (by norm_num)
theorem B10890389 : Blo 1340989 10890389 := bbase (se 6 (by rfl) ⟨255243, by rfl⟩ : syracuseStep 10890389 = 510487) (by norm_num)
theorem B1698985 : Blo 1340989 1698985 := bbase (se 2 (by rfl) ⟨637119, by rfl⟩ : syracuseStep 1698985 = 1274239) (by norm_num)
theorem B1510573 : Blo 1340989 1510573 := bbase (se 3 (by rfl) ⟨283232, by rfl⟩ : syracuseStep 1510573 = 566465) (by norm_num)
theorem B3017933 : Blo 1340989 3017933 := bbase (se 3 (by rfl) ⟨565862, by rfl⟩ : syracuseStep 3017933 = 1131725) (by norm_num)
theorem B1510609 : Blo 1340989 1510609 := bbase (se 2 (by rfl) ⟨566478, by rfl⟩ : syracuseStep 1510609 = 1132957) (by norm_num)
theorem B3058901 : Blo 1340989 3058901 := bbase (se 7 (by rfl) ⟨35846, by rfl⟩ : syracuseStep 3058901 = 71693) (by norm_num)
theorem B3394781 : Blo 1340989 3394781 := bbase (se 3 (by rfl) ⟨636521, by rfl⟩ : syracuseStep 3394781 = 1273043) (by norm_num)
theorem B1510645 : Blo 1340989 1510645 := bbase (se 5 (by rfl) ⟨70811, by rfl⟩ : syracuseStep 1510645 = 141623) (by norm_num)
theorem B3018005 : Blo 1340989 3018005 := bbase (se 6 (by rfl) ⟨70734, by rfl⟩ : syracuseStep 3018005 = 141469) (by norm_num)
theorem B2264341 : Blo 1340989 2264341 := bbase (se 6 (by rfl) ⟨53070, by rfl⟩ : syracuseStep 2264341 = 106141) (by norm_num)
theorem B1510681 : Blo 1340989 1510681 := bbase (se 2 (by rfl) ⟨566505, by rfl⟩ : syracuseStep 1510681 = 1133011) (by norm_num)
theorem B1510717 : Blo 1340989 1510717 := bbase (se 3 (by rfl) ⟨283259, by rfl⟩ : syracuseStep 1510717 = 566519) (by norm_num)
theorem B1912133 : Blo 1340989 1912133 := bbase (se 4 (by rfl) ⟨179262, by rfl⟩ : syracuseStep 1912133 = 358525) (by norm_num)
theorem B1699157 : Blo 1340989 1699157 := bbase (se 11 (by rfl) ⟨1244, by rfl⟩ : syracuseStep 1699157 = 2489) (by norm_num)
theorem B3018077 : Blo 1340989 3018077 := bbase (se 3 (by rfl) ⟨565889, by rfl⟩ : syracuseStep 3018077 = 1131779) (by norm_num)
theorem B1510753 : Blo 1340989 1510753 := bbase (se 2 (by rfl) ⟨566532, by rfl⟩ : syracuseStep 1510753 = 1133065) (by norm_num)
theorem B2264429 : Blo 1340989 2264429 := bbase (se 3 (by rfl) ⟨424580, by rfl⟩ : syracuseStep 2264429 = 849161) (by norm_num)
theorem B1510789 : Blo 1340989 1510789 := bbase (se 4 (by rfl) ⟨141636, by rfl⟩ : syracuseStep 1510789 = 283273) (by norm_num)
theorem B1699213 : Blo 1340989 1699213 := bbase (se 3 (by rfl) ⟨318602, by rfl⟩ : syracuseStep 1699213 = 637205) (by norm_num)
theorem B1813909 : Blo 1340989 1813909 := bbase (se 6 (by rfl) ⟨42513, by rfl⟩ : syracuseStep 1813909 = 85027) (by norm_num)
theorem B3394973 : Blo 1340989 3394973 := bbase (se 3 (by rfl) ⟨636557, by rfl⟩ : syracuseStep 3394973 = 1273115) (by norm_num)
theorem B3018149 : Blo 1340989 3018149 := bbase (se 4 (by rfl) ⟨282951, by rfl⟩ : syracuseStep 3018149 = 565903) (by norm_num)
theorem B1510825 : Blo 1340989 1510825 := bbase (se 2 (by rfl) ⟨566559, by rfl⟩ : syracuseStep 1510825 = 1133119) (by norm_num)
theorem B1510861 : Blo 1340989 1510861 := bbase (se 3 (by rfl) ⟨283286, by rfl⟩ : syracuseStep 1510861 = 566573) (by norm_num)
theorem B4296149 : Blo 1340989 4296149 := bbase (se 7 (by rfl) ⟨50345, by rfl⟩ : syracuseStep 4296149 = 100691) (by norm_num)
theorem B3018221 : Blo 1340989 3018221 := bbase (se 3 (by rfl) ⟨565916, by rfl⟩ : syracuseStep 3018221 = 1131833) (by norm_num)
theorem B2264557 : Blo 1340989 2264557 := bbase (se 3 (by rfl) ⟨424604, by rfl⟩ : syracuseStep 2264557 = 849209) (by norm_num)
theorem B1699309 : Blo 1340989 1699309 := bbase (se 3 (by rfl) ⟨318620, by rfl⟩ : syracuseStep 1699309 = 637241) (by norm_num)
theorem B4083205 : Blo 1340989 4083205 := bbase (se 4 (by rfl) ⟨382800, by rfl⟩ : syracuseStep 4083205 = 765601) (by norm_num)
theorem B3059221 : Blo 1340989 3059221 := bbase (se 6 (by rfl) ⟨71700, by rfl⟩ : syracuseStep 3059221 = 143401) (by norm_num)
theorem B5443109 : Blo 1340989 5443109 := bbase (se 4 (by rfl) ⟨510291, by rfl⟩ : syracuseStep 5443109 = 1020583) (by norm_num)
theorem B3018293 : Blo 1340989 3018293 := bbase (se 5 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 3018293 = 282965) (by norm_num)
theorem B2264645 : Blo 1340989 2264645 := bbase (se 4 (by rfl) ⟨212310, by rfl⟩ : syracuseStep 2264645 = 424621) (by norm_num)
theorem B3018365 : Blo 1340989 3018365 := bbase (se 3 (by rfl) ⟨565943, by rfl⟩ : syracuseStep 3018365 = 1131887) (by norm_num)
theorem B1699481 : Blo 1340989 1699481 := bbase (se 2 (by rfl) ⟨637305, by rfl⟩ : syracuseStep 1699481 = 1274611) (by norm_num)
theorem B3018437 : Blo 1340989 3018437 := bbase (se 4 (by rfl) ⟨282978, by rfl⟩ : syracuseStep 3018437 = 565957) (by norm_num)
theorem B2264773 : Blo 1340989 2264773 := bbase (se 4 (by rfl) ⟨212322, by rfl⟩ : syracuseStep 2264773 = 424645) (by norm_num)
theorem B1699537 : Blo 1340989 1699537 := bbase (se 2 (by rfl) ⟨637326, by rfl⟩ : syracuseStep 1699537 = 1274653) (by norm_num)
theorem B6123221 : Blo 1340989 6123221 := bbase (se 7 (by rfl) ⟨71756, by rfl⟩ : syracuseStep 6123221 = 143513) (by norm_num)
theorem B3395317 : Blo 1340989 3395317 := bbase (se 5 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 3395317 = 318311) (by norm_num)
theorem B3018509 : Blo 1340989 3018509 := bbase (se 3 (by rfl) ⟨565970, by rfl⟩ : syracuseStep 3018509 = 1131941) (by norm_num)
theorem B2264861 : Blo 1340989 2264861 := bbase (se 3 (by rfl) ⟨424661, by rfl⟩ : syracuseStep 2264861 = 849323) (by norm_num)
theorem B1699633 : Blo 1340989 1699633 := bbase (se 2 (by rfl) ⟨637362, by rfl⟩ : syracuseStep 1699633 = 1274725) (by norm_num)
theorem B4083509 : Blo 1340989 4083509 := bbase (se 5 (by rfl) ⟨191414, by rfl⟩ : syracuseStep 4083509 = 382829) (by norm_num)
theorem B3018581 : Blo 1340989 3018581 := bbase (se 9 (by rfl) ⟨8843, by rfl⟩ : syracuseStep 3018581 = 17687) (by norm_num)
theorem B3395429 : Blo 1340989 3395429 := bbase (se 4 (by rfl) ⟨318321, by rfl⟩ : syracuseStep 3395429 = 636643) (by norm_num)
theorem B3018653 : Blo 1340989 3018653 := bbase (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) (by norm_num)
theorem B2264989 : Blo 1340989 2264989 := bbase (se 3 (by rfl) ⟨424685, by rfl⟩ : syracuseStep 2264989 = 849371) (by norm_num)
theorem B2150317 : Blo 1340989 2150317 := bbase (se 3 (by rfl) ⟨403184, by rfl⟩ : syracuseStep 2150317 = 806369) (by norm_num)
theorem B3821509 : Blo 1340989 3821509 := bbase (se 4 (by rfl) ⟨358266, by rfl⟩ : syracuseStep 3821509 = 716533) (by norm_num)
theorem B3018725 : Blo 1340989 3018725 := bbase (se 4 (by rfl) ⟨283005, by rfl⟩ : syracuseStep 3018725 = 566011) (by norm_num)
theorem B2265077 : Blo 1340989 2265077 := bbase (se 5 (by rfl) ⟨106175, by rfl⟩ : syracuseStep 2265077 = 212351) (by norm_num)
theorem B4526117 : Blo 1340989 4526117 := bbase (se 4 (by rfl) ⟨424323, by rfl⟩ : syracuseStep 4526117 = 848647) (by norm_num)
theorem B3395621 : Blo 1340989 3395621 := bbase (se 4 (by rfl) ⟨318339, by rfl⟩ : syracuseStep 3395621 = 636679) (by norm_num)
theorem B3018797 : Blo 1340989 3018797 := bbase (se 3 (by rfl) ⟨566024, by rfl⟩ : syracuseStep 3018797 = 1132049) (by norm_num)
theorem B3018869 : Blo 1340989 3018869 := bbase (se 5 (by rfl) ⟨141509, by rfl⟩ : syracuseStep 3018869 = 283019) (by norm_num)
theorem B5165173 : Blo 1340989 5165173 := bbase (se 5 (by rfl) ⟨242117, by rfl⟩ : syracuseStep 5165173 = 484235) (by norm_num)
theorem B2265205 : Blo 1340989 2265205 := bbase (se 5 (by rfl) ⟨106181, by rfl⟩ : syracuseStep 2265205 = 212363) (by norm_num)
theorem B6795413 : Blo 1340989 6795413 := bbase (se 6 (by rfl) ⟨159267, by rfl⟩ : syracuseStep 6795413 = 318535) (by norm_num)
theorem B3018941 : Blo 1340989 3018941 := bbase (se 3 (by rfl) ⟨566051, by rfl⟩ : syracuseStep 3018941 = 1132103) (by norm_num)
theorem B2265293 : Blo 1340989 2265293 := bbase (se 3 (by rfl) ⟨424742, by rfl⟩ : syracuseStep 2265293 = 849485) (by norm_num)
theorem B3019013 : Blo 1340989 3019013 := bbase (se 4 (by rfl) ⟨283032, by rfl⟩ : syracuseStep 3019013 = 566065) (by norm_num)
theorem B4837637 : Blo 1340989 4837637 := bbase (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) (by norm_num)
theorem B3019085 : Blo 1340989 3019085 := bbase (se 3 (by rfl) ⟨566078, by rfl⟩ : syracuseStep 3019085 = 1132157) (by norm_num)
theorem B2265421 : Blo 1340989 2265421 := bbase (se 3 (by rfl) ⟨424766, by rfl⟩ : syracuseStep 2265421 = 849533) (by norm_num)
theorem B4297045 : Blo 1340989 4297045 := bbase (se 10 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 4297045 = 12589) (by norm_num)
theorem B2011493 : Blo 1340989 2011493 := bbase (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) (by norm_num)
theorem B2011517 : Blo 1340989 2011517 := bbase (se 3 (by rfl) ⟨377159, by rfl⟩ : syracuseStep 2011517 = 754319) (by norm_num)
theorem B3395965 : Blo 1340989 3395965 := bbase (se 3 (by rfl) ⟨636743, by rfl⟩ : syracuseStep 3395965 = 1273487) (by norm_num)
theorem B2011541 : Blo 1340989 2011541 := bbase (se 6 (by rfl) ⟨47145, by rfl⟩ : syracuseStep 2011541 = 94291) (by norm_num)
theorem B3223957 : Blo 1340989 3223957 := bbase (se 6 (by rfl) ⟨75561, by rfl⟩ : syracuseStep 3223957 = 151123) (by norm_num)
theorem B3019157 : Blo 1340989 3019157 := bbase (se 6 (by rfl) ⟨70761, by rfl⟩ : syracuseStep 3019157 = 141523) (by norm_num)
theorem B4837781 : Blo 1340989 4837781 := bbase (se 6 (by rfl) ⟨113385, by rfl⟩ : syracuseStep 4837781 = 226771) (by norm_num)
theorem B2265509 : Blo 1340989 2265509 := bbase (se 4 (by rfl) ⟨212391, by rfl⟩ : syracuseStep 2265509 = 424783) (by norm_num)
theorem B2011565 : Blo 1340989 2011565 := bbase (se 3 (by rfl) ⟨377168, by rfl⟩ : syracuseStep 2011565 = 754337) (by norm_num)
theorem B2011589 : Blo 1340989 2011589 := bbase (se 4 (by rfl) ⟨188586, by rfl⟩ : syracuseStep 2011589 = 377173) (by norm_num)
theorem B4526549 : Blo 1340989 4526549 := bbase (se 7 (by rfl) ⟨53045, by rfl⟩ : syracuseStep 4526549 = 106091) (by norm_num)
theorem B7746005 : Blo 1340989 7746005 := bbase (se 7 (by rfl) ⟨90773, by rfl⟩ : syracuseStep 7746005 = 181547) (by norm_num)
theorem B2011613 : Blo 1340989 2011613 := bbase (se 3 (by rfl) ⟨377177, by rfl⟩ : syracuseStep 2011613 = 754355) (by norm_num)
theorem B3019229 : Blo 1340989 3019229 := bbase (se 3 (by rfl) ⟨566105, by rfl⟩ : syracuseStep 3019229 = 1132211) (by norm_num)
theorem B3396077 : Blo 1340989 3396077 := bbase (se 3 (by rfl) ⟨636764, by rfl⟩ : syracuseStep 3396077 = 1273529) (by norm_num)
theorem B2011637 : Blo 1340989 2011637 := bbase (se 5 (by rfl) ⟨94295, by rfl⟩ : syracuseStep 2011637 = 188591) (by norm_num)
theorem B2011661 : Blo 1340989 2011661 := bbase (se 3 (by rfl) ⟨377186, by rfl⟩ : syracuseStep 2011661 = 754373) (by norm_num)
theorem B2011685 : Blo 1340989 2011685 := bbase (se 4 (by rfl) ⟨188595, by rfl⟩ : syracuseStep 2011685 = 377191) (by norm_num)
theorem B3019301 : Blo 1340989 3019301 := bbase (se 4 (by rfl) ⟨283059, by rfl⟩ : syracuseStep 3019301 = 566119) (by norm_num)
theorem B2265637 : Blo 1340989 2265637 := bbase (se 4 (by rfl) ⟨212403, by rfl⟩ : syracuseStep 2265637 = 424807) (by norm_num)
theorem B2011709 : Blo 1340989 2011709 := bbase (se 3 (by rfl) ⟨377195, by rfl⟩ : syracuseStep 2011709 = 754391) (by norm_num)
theorem B2011733 : Blo 1340989 2011733 := bbase (se 8 (by rfl) ⟨11787, by rfl⟩ : syracuseStep 2011733 = 23575) (by norm_num)
theorem B2011757 : Blo 1340989 2011757 := bbase (se 3 (by rfl) ⟨377204, by rfl⟩ : syracuseStep 2011757 = 754409) (by norm_num)
theorem B3019373 : Blo 1340989 3019373 := bbase (se 3 (by rfl) ⟨566132, by rfl⟩ : syracuseStep 3019373 = 1132265) (by norm_num)
theorem B2151029 : Blo 1340989 2151029 := bbase (se 5 (by rfl) ⟨100829, by rfl⟩ : syracuseStep 2151029 = 201659) (by norm_num)
theorem B2265725 : Blo 1340989 2265725 := bbase (se 3 (by rfl) ⟨424823, by rfl⟩ : syracuseStep 2265725 = 849647) (by norm_num)
theorem B2011781 : Blo 1340989 2011781 := bbase (se 4 (by rfl) ⟨188604, by rfl⟩ : syracuseStep 2011781 = 377209) (by norm_num)
theorem B2011805 : Blo 1340989 2011805 := bbase (se 3 (by rfl) ⟨377213, by rfl⟩ : syracuseStep 2011805 = 754427) (by norm_num)
theorem B3396269 : Blo 1340989 3396269 := bbase (se 3 (by rfl) ⟨636800, by rfl⟩ : syracuseStep 3396269 = 1273601) (by norm_num)
theorem B2011829 : Blo 1340989 2011829 := bbase (se 5 (by rfl) ⟨94304, by rfl⟩ : syracuseStep 2011829 = 188609) (by norm_num)
theorem B3019445 : Blo 1340989 3019445 := bbase (se 5 (by rfl) ⟨141536, by rfl⟩ : syracuseStep 3019445 = 283073) (by norm_num)
theorem B2011853 : Blo 1340989 2011853 := bbase (se 3 (by rfl) ⟨377222, by rfl⟩ : syracuseStep 2011853 = 754445) (by norm_num)
theorem B2011877 : Blo 1340989 2011877 := bbase (se 4 (by rfl) ⟨188613, by rfl⟩ : syracuseStep 2011877 = 377227) (by norm_num)
theorem B4297445 : Blo 1340989 4297445 := bbase (se 4 (by rfl) ⟨402885, by rfl⟩ : syracuseStep 4297445 = 805771) (by norm_num)
theorem B2011901 : Blo 1340989 2011901 := bbase (se 3 (by rfl) ⟨377231, by rfl⟩ : syracuseStep 2011901 = 754463) (by norm_num)
theorem B3019517 : Blo 1340989 3019517 := bbase (se 3 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 3019517 = 1132319) (by norm_num)
theorem B2265853 : Blo 1340989 2265853 := bbase (se 3 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 2265853 = 849695) (by norm_num)
theorem B1635073 : Blo 1340989 1635073 := bbase (se 2 (by rfl) ⟨613152, by rfl⟩ : syracuseStep 1635073 = 1226305) (by norm_num)
theorem B2011925 : Blo 1340989 2011925 := bbase (se 6 (by rfl) ⟨47154, by rfl⟩ : syracuseStep 2011925 = 94309) (by norm_num)
theorem B7639829 : Blo 1340989 7639829 := bbase (se 6 (by rfl) ⟨179058, by rfl⟩ : syracuseStep 7639829 = 358117) (by norm_num)
theorem B2011949 : Blo 1340989 2011949 := bbase (se 3 (by rfl) ⟨377240, by rfl⟩ : syracuseStep 2011949 = 754481) (by norm_num)
theorem B2011973 : Blo 1340989 2011973 := bbase (se 4 (by rfl) ⟨188622, by rfl⟩ : syracuseStep 2011973 = 377245) (by norm_num)
theorem B3019589 : Blo 1340989 3019589 := bbase (se 4 (by rfl) ⟨283086, by rfl⟩ : syracuseStep 3019589 = 566173) (by norm_num)
theorem B2265941 : Blo 1340989 2265941 := bbase (se 9 (by rfl) ⟨6638, by rfl⟩ : syracuseStep 2265941 = 13277) (by norm_num)
theorem B2011997 : Blo 1340989 2011997 := bbase (se 3 (by rfl) ⟨377249, by rfl⟩ : syracuseStep 2011997 = 754499) (by norm_num)
theorem B2012021 : Blo 1340989 2012021 := bbase (se 5 (by rfl) ⟨94313, by rfl⟩ : syracuseStep 2012021 = 188627) (by norm_num)
theorem B4526981 : Blo 1340989 4526981 := bbase (se 4 (by rfl) ⟨424404, by rfl⟩ : syracuseStep 4526981 = 848809) (by norm_num)
theorem B2012045 : Blo 1340989 2012045 := bbase (se 3 (by rfl) ⟨377258, by rfl⟩ : syracuseStep 2012045 = 754517) (by norm_num)
theorem B3019661 : Blo 1340989 3019661 := bbase (se 3 (by rfl) ⟨566186, by rfl⟩ : syracuseStep 3019661 = 1132373) (by norm_num)
theorem B11465621 : Blo 1340989 11465621 := bbase (se 6 (by rfl) ⟨268725, by rfl⟩ : syracuseStep 11465621 = 537451) (by norm_num)
theorem B2012069 : Blo 1340989 2012069 := bbase (se 4 (by rfl) ⟨188631, by rfl⟩ : syracuseStep 2012069 = 377263) (by norm_num)
theorem B2012093 : Blo 1340989 2012093 := bbase (se 3 (by rfl) ⟨377267, by rfl⟩ : syracuseStep 2012093 = 754535) (by norm_num)
theorem B2012117 : Blo 1340989 2012117 := bbase (se 7 (by rfl) ⟨23579, by rfl⟩ : syracuseStep 2012117 = 47159) (by norm_num)
theorem B3019733 : Blo 1340989 3019733 := bbase (se 7 (by rfl) ⟨35387, by rfl⟩ : syracuseStep 3019733 = 70775) (by norm_num)
theorem B2266069 : Blo 1340989 2266069 := bbase (se 7 (by rfl) ⟨26555, by rfl⟩ : syracuseStep 2266069 = 53111) (by norm_num)
theorem B2012141 : Blo 1340989 2012141 := bbase (se 3 (by rfl) ⟨377276, by rfl⟩ : syracuseStep 2012141 = 754553) (by norm_num)
theorem B3224573 : Blo 1340989 3224573 := bbase (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) (by norm_num)
theorem B2012165 : Blo 1340989 2012165 := bbase (se 4 (by rfl) ⟨188640, by rfl⟩ : syracuseStep 2012165 = 377281) (by norm_num)
theorem B3396613 : Blo 1340989 3396613 := bbase (se 4 (by rfl) ⟨318432, by rfl⟩ : syracuseStep 3396613 = 636865) (by norm_num)
theorem B11457557 : Blo 1340989 11457557 := bbase (se 6 (by rfl) ⟨268536, by rfl⟩ : syracuseStep 11457557 = 537073) (by norm_num)
theorem B2012189 : Blo 1340989 2012189 := bbase (se 3 (by rfl) ⟨377285, by rfl⟩ : syracuseStep 2012189 = 754571) (by norm_num)
theorem B3019805 : Blo 1340989 3019805 := bbase (se 3 (by rfl) ⟨566213, by rfl⟩ : syracuseStep 3019805 = 1132427) (by norm_num)
theorem B2266157 : Blo 1340989 2266157 := bbase (se 3 (by rfl) ⟨424904, by rfl⟩ : syracuseStep 2266157 = 849809) (by norm_num)
theorem B2012213 : Blo 1340989 2012213 := bbase (se 5 (by rfl) ⟨94322, by rfl⟩ : syracuseStep 2012213 = 188645) (by norm_num)
theorem B3224629 : Blo 1340989 3224629 := bbase (se 5 (by rfl) ⟨151154, by rfl⟩ : syracuseStep 3224629 = 302309) (by norm_num)
theorem B2012237 : Blo 1340989 2012237 := bbase (se 3 (by rfl) ⟨377294, by rfl⟩ : syracuseStep 2012237 = 754589) (by norm_num)
theorem B2012261 : Blo 1340989 2012261 := bbase (se 4 (by rfl) ⟨188649, by rfl⟩ : syracuseStep 2012261 = 377299) (by norm_num)
theorem B3019877 : Blo 1340989 3019877 := bbase (se 4 (by rfl) ⟨283113, by rfl⟩ : syracuseStep 3019877 = 566227) (by norm_num)
theorem B3396725 : Blo 1340989 3396725 := bbase (se 5 (by rfl) ⟨159221, by rfl⟩ : syracuseStep 3396725 = 318443) (by norm_num)
theorem B2012285 : Blo 1340989 2012285 := bbase (se 3 (by rfl) ⟨377303, by rfl⟩ : syracuseStep 2012285 = 754607) (by norm_num)
theorem B2012309 : Blo 1340989 2012309 := bbase (se 6 (by rfl) ⟨47163, by rfl⟩ : syracuseStep 2012309 = 94327) (by norm_num)
theorem B2012333 : Blo 1340989 2012333 := bbase (se 3 (by rfl) ⟨377312, by rfl⟩ : syracuseStep 2012333 = 754625) (by norm_num)
theorem B3019949 : Blo 1340989 3019949 := bbase (se 3 (by rfl) ⟨566240, by rfl⟩ : syracuseStep 3019949 = 1132481) (by norm_num)
theorem B2266285 : Blo 1340989 2266285 := bbase (se 3 (by rfl) ⟨424928, by rfl⟩ : syracuseStep 2266285 = 849857) (by norm_num)
theorem B2012357 : Blo 1340989 2012357 := bbase (se 4 (by rfl) ⟨188658, by rfl⟩ : syracuseStep 2012357 = 377317) (by norm_num)
theorem B2012381 : Blo 1340989 2012381 := bbase (se 3 (by rfl) ⟨377321, by rfl⟩ : syracuseStep 2012381 = 754643) (by norm_num)
theorem B2012405 : Blo 1340989 2012405 := bbase (se 5 (by rfl) ⟨94331, by rfl⟩ : syracuseStep 2012405 = 188663) (by norm_num)
theorem B3020021 : Blo 1340989 3020021 := bbase (se 5 (by rfl) ⟨141563, by rfl⟩ : syracuseStep 3020021 = 283127) (by norm_num)
theorem B2012429 : Blo 1340989 2012429 := bbase (se 3 (by rfl) ⟨377330, by rfl⟩ : syracuseStep 2012429 = 754661) (by norm_num)
theorem B3626261 : Blo 1340989 3626261 := bbase (se 6 (by rfl) ⟨84990, by rfl⟩ : syracuseStep 3626261 = 169981) (by norm_num)
theorem B2012453 : Blo 1340989 2012453 := bbase (se 4 (by rfl) ⟨188667, by rfl⟩ : syracuseStep 2012453 = 377335) (by norm_num)
theorem B4527413 : Blo 1340989 4527413 := bbase (se 5 (by rfl) ⟨212222, by rfl⟩ : syracuseStep 4527413 = 424445) (by norm_num)
theorem B3396917 : Blo 1340989 3396917 := bbase (se 5 (by rfl) ⟨159230, by rfl⟩ : syracuseStep 3396917 = 318461) (by norm_num)
theorem B2012477 : Blo 1340989 2012477 := bbase (se 3 (by rfl) ⟨377339, by rfl⟩ : syracuseStep 2012477 = 754679) (by norm_num)
theorem B3020093 : Blo 1340989 3020093 := bbase (se 3 (by rfl) ⟨566267, by rfl⟩ : syracuseStep 3020093 = 1132535) (by norm_num)
theorem B2012501 : Blo 1340989 2012501 := bbase (se 13 (by rfl) ⟨368, by rfl⟩ : syracuseStep 2012501 = 737) (by norm_num)
theorem B2012525 : Blo 1340989 2012525 := bbase (se 3 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 2012525 = 754697) (by norm_num)
theorem B2012549 : Blo 1340989 2012549 := bbase (se 4 (by rfl) ⟨188676, by rfl⟩ : syracuseStep 2012549 = 377353) (by norm_num)
theorem B5731717 : Blo 1340989 5731717 := bbase (se 4 (by rfl) ⟨537348, by rfl⟩ : syracuseStep 5731717 = 1074697) (by norm_num)
theorem B3020165 : Blo 1340989 3020165 := bbase (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) (by norm_num)
theorem B4838789 : Blo 1340989 4838789 := bbase (se 4 (by rfl) ⟨453636, by rfl⟩ : syracuseStep 4838789 = 907273) (by norm_num)
theorem B2012573 : Blo 1340989 2012573 := bbase (se 3 (by rfl) ⟨377357, by rfl⟩ : syracuseStep 2012573 = 754715) (by norm_num)
theorem B3823013 : Blo 1340989 3823013 := bbase (se 4 (by rfl) ⟨358407, by rfl⟩ : syracuseStep 3823013 = 716815) (by norm_num)
theorem B6796709 : Blo 1340989 6796709 := bbase (se 4 (by rfl) ⟨637191, by rfl⟩ : syracuseStep 6796709 = 1274383) (by norm_num)
theorem B1611181 : Blo 1340989 1611181 := bbase (se 3 (by rfl) ⟨302096, by rfl⟩ : syracuseStep 1611181 = 604193) (by norm_num)
theorem B3061165 : Blo 1340989 3061165 := bbase (se 3 (by rfl) ⟨573968, by rfl⟩ : syracuseStep 3061165 = 1147937) (by norm_num)
theorem B2012597 : Blo 1340989 2012597 := bbase (se 5 (by rfl) ⟨94340, by rfl⟩ : syracuseStep 2012597 = 188681) (by norm_num)
theorem B2012621 : Blo 1340989 2012621 := bbase (se 3 (by rfl) ⟨377366, by rfl⟩ : syracuseStep 2012621 = 754733) (by norm_num)
theorem B3020237 : Blo 1340989 3020237 := bbase (se 3 (by rfl) ⟨566294, by rfl⟩ : syracuseStep 3020237 = 1132589) (by norm_num)
theorem B2012645 : Blo 1340989 2012645 := bbase (se 4 (by rfl) ⟨188685, by rfl⟩ : syracuseStep 2012645 = 377371) (by norm_num)
theorem B2864621 : Blo 1340989 2864621 := bbase (se 3 (by rfl) ⟨537116, by rfl⟩ : syracuseStep 2864621 = 1074233) (by norm_num)
theorem B2012669 : Blo 1340989 2012669 := bbase (se 3 (by rfl) ⟨377375, by rfl⟩ : syracuseStep 2012669 = 754751) (by norm_num)
theorem B2012693 : Blo 1340989 2012693 := bbase (se 6 (by rfl) ⟨47172, by rfl⟩ : syracuseStep 2012693 = 94345) (by norm_num)
theorem B3020309 : Blo 1340989 3020309 := bbase (se 6 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 3020309 = 141577) (by norm_num)
theorem B5092901 : Blo 1340989 5092901 := bbase (se 4 (by rfl) ⟨477459, by rfl⟩ : syracuseStep 5092901 = 954919) (by norm_num)
theorem B2012717 : Blo 1340989 2012717 := bbase (se 3 (by rfl) ⟨377384, by rfl⟩ : syracuseStep 2012717 = 754769) (by norm_num)
theorem B2012741 : Blo 1340989 2012741 := bbase (se 4 (by rfl) ⟨188694, by rfl⟩ : syracuseStep 2012741 = 377389) (by norm_num)
theorem B2012765 : Blo 1340989 2012765 := bbase (se 3 (by rfl) ⟨377393, by rfl⟩ : syracuseStep 2012765 = 754787) (by norm_num)
theorem B3020381 : Blo 1340989 3020381 := bbase (se 3 (by rfl) ⟨566321, by rfl⟩ : syracuseStep 3020381 = 1132643) (by norm_num)
theorem B2012789 : Blo 1340989 2012789 := bbase (se 5 (by rfl) ⟨94349, by rfl⟩ : syracuseStep 2012789 = 188699) (by norm_num)
theorem B2864765 : Blo 1340989 2864765 := bbase (se 3 (by rfl) ⟨537143, by rfl⟩ : syracuseStep 2864765 = 1074287) (by norm_num)
theorem B2012813 : Blo 1340989 2012813 := bbase (se 3 (by rfl) ⟨377402, by rfl⟩ : syracuseStep 2012813 = 754805) (by norm_num)
theorem B3397261 : Blo 1340989 3397261 := bbase (se 3 (by rfl) ⟨636986, by rfl⟩ : syracuseStep 3397261 = 1273973) (by norm_num)
theorem B2012837 : Blo 1340989 2012837 := bbase (se 4 (by rfl) ⟨188703, by rfl⟩ : syracuseStep 2012837 = 377407) (by norm_num)
theorem B3020453 : Blo 1340989 3020453 := bbase (se 4 (by rfl) ⟨283167, by rfl⟩ : syracuseStep 3020453 = 566335) (by norm_num)
theorem B10327733 : Blo 1340989 10327733 := bbase (se 5 (by rfl) ⟨484112, by rfl⟩ : syracuseStep 10327733 = 968225) (by norm_num)
theorem B2012861 : Blo 1340989 2012861 := bbase (se 3 (by rfl) ⟨377411, by rfl⟩ : syracuseStep 2012861 = 754823) (by norm_num)
theorem B1611469 : Blo 1340989 1611469 := bbase (se 3 (by rfl) ⟨302150, by rfl⟩ : syracuseStep 1611469 = 604301) (by norm_num)
theorem B2012885 : Blo 1340989 2012885 := bbase (se 7 (by rfl) ⟨23588, by rfl⟩ : syracuseStep 2012885 = 47177) (by norm_num)
theorem B4527845 : Blo 1340989 4527845 := bbase (se 4 (by rfl) ⟨424485, by rfl⟩ : syracuseStep 4527845 = 848971) (by norm_num)
theorem B2012909 : Blo 1340989 2012909 := bbase (se 3 (by rfl) ⟨377420, by rfl⟩ : syracuseStep 2012909 = 754841) (by norm_num)
theorem B3020525 : Blo 1340989 3020525 := bbase (se 3 (by rfl) ⟨566348, by rfl⟩ : syracuseStep 3020525 = 1132697) (by norm_num)
theorem B3397373 : Blo 1340989 3397373 := bbase (se 3 (by rfl) ⟨637007, by rfl⟩ : syracuseStep 3397373 = 1274015) (by norm_num)
theorem B2012933 : Blo 1340989 2012933 := bbase (se 4 (by rfl) ⟨188712, by rfl⟩ : syracuseStep 2012933 = 377425) (by norm_num)
theorem B2012957 : Blo 1340989 2012957 := bbase (se 3 (by rfl) ⟨377429, by rfl⟩ : syracuseStep 2012957 = 754859) (by norm_num)
theorem B2012981 : Blo 1340989 2012981 := bbase (se 5 (by rfl) ⟨94358, by rfl⟩ : syracuseStep 2012981 = 188717) (by norm_num)
theorem B3020597 : Blo 1340989 3020597 := bbase (se 5 (by rfl) ⟨141590, by rfl⟩ : syracuseStep 3020597 = 283181) (by norm_num)
theorem B6788933 : Blo 1340989 6788933 := bbase (se 4 (by rfl) ⟨636462, by rfl⟩ : syracuseStep 6788933 = 1272925) (by norm_num)
theorem B5093189 : Blo 1340989 5093189 := bbase (se 4 (by rfl) ⟨477486, by rfl⟩ : syracuseStep 5093189 = 954973) (by norm_num)
theorem B2013005 : Blo 1340989 2013005 := bbase (se 3 (by rfl) ⟨377438, by rfl⟩ : syracuseStep 2013005 = 754877) (by norm_num)
theorem B2013029 : Blo 1340989 2013029 := bbase (se 4 (by rfl) ⟨188721, by rfl⟩ : syracuseStep 2013029 = 377443) (by norm_num)
theorem B2013053 : Blo 1340989 2013053 := bbase (se 3 (by rfl) ⟨377447, by rfl⟩ : syracuseStep 2013053 = 754895) (by norm_num)
theorem B3020669 : Blo 1340989 3020669 := bbase (se 3 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 3020669 = 1132751) (by norm_num)
theorem B2013077 : Blo 1340989 2013077 := bbase (se 6 (by rfl) ⟨47181, by rfl⟩ : syracuseStep 2013077 = 94363) (by norm_num)
theorem B4306853 : Blo 1340989 4306853 := bbase (se 4 (by rfl) ⟨403767, by rfl⟩ : syracuseStep 4306853 = 807535) (by norm_num)
theorem B2013101 : Blo 1340989 2013101 := bbase (se 3 (by rfl) ⟨377456, by rfl⟩ : syracuseStep 2013101 = 754913) (by norm_num)
theorem B7641013 : Blo 1340989 7641013 := bbase (se 5 (by rfl) ⟨358172, by rfl⟩ : syracuseStep 7641013 = 716345) (by norm_num)
theorem B3397565 : Blo 1340989 3397565 := bbase (se 3 (by rfl) ⟨637043, by rfl⟩ : syracuseStep 3397565 = 1274087) (by norm_num)
theorem B2013125 : Blo 1340989 2013125 := bbase (se 4 (by rfl) ⟨188730, by rfl⟩ : syracuseStep 2013125 = 377461) (by norm_num)
theorem B3020741 : Blo 1340989 3020741 := bbase (se 4 (by rfl) ⟨283194, by rfl⟩ : syracuseStep 3020741 = 566389) (by norm_num)
theorem B2013149 : Blo 1340989 2013149 := bbase (se 3 (by rfl) ⟨377465, by rfl⟩ : syracuseStep 2013149 = 754931) (by norm_num)
theorem B2865125 : Blo 1340989 2865125 := bbase (se 4 (by rfl) ⟨268605, by rfl⟩ : syracuseStep 2865125 = 537211) (by norm_num)
theorem B2013173 : Blo 1340989 2013173 := bbase (se 5 (by rfl) ⟨94367, by rfl⟩ : syracuseStep 2013173 = 188735) (by norm_num)
theorem B2013197 : Blo 1340989 2013197 := bbase (se 3 (by rfl) ⟨377474, by rfl⟩ : syracuseStep 2013197 = 754949) (by norm_num)
theorem B3020813 : Blo 1340989 3020813 := bbase (se 3 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 3020813 = 1132805) (by norm_num)
theorem B3225629 : Blo 1340989 3225629 := bbase (se 3 (by rfl) ⟨604805, by rfl⟩ : syracuseStep 3225629 = 1209611) (by norm_num)
theorem B2013221 : Blo 1340989 2013221 := bbase (se 4 (by rfl) ⟨188739, by rfl⟩ : syracuseStep 2013221 = 377479) (by norm_num)
theorem B2013245 : Blo 1340989 2013245 := bbase (se 3 (by rfl) ⟨377483, by rfl⟩ : syracuseStep 2013245 = 754967) (by norm_num)
theorem B2013269 : Blo 1340989 2013269 := bbase (se 8 (by rfl) ⟨11796, by rfl⟩ : syracuseStep 2013269 = 23593) (by norm_num)
theorem B3020885 : Blo 1340989 3020885 := bbase (se 8 (by rfl) ⟨17700, by rfl⟩ : syracuseStep 3020885 = 35401) (by norm_num)
theorem B4356197 : Blo 1340989 4356197 := bbase (se 4 (by rfl) ⟨408393, by rfl⟩ : syracuseStep 4356197 = 816787) (by norm_num)
theorem B2013293 : Blo 1340989 2013293 := bbase (se 3 (by rfl) ⟨377492, by rfl⟩ : syracuseStep 2013293 = 754985) (by norm_num)
theorem B2013317 : Blo 1340989 2013317 := bbase (se 4 (by rfl) ⟨188748, by rfl⟩ : syracuseStep 2013317 = 377497) (by norm_num)
theorem B2545805 : Blo 1340989 2545805 := bbase (se 3 (by rfl) ⟨477338, by rfl⟩ : syracuseStep 2545805 = 954677) (by norm_num)
theorem B4528277 : Blo 1340989 4528277 := bbase (se 6 (by rfl) ⟨106131, by rfl⟩ : syracuseStep 4528277 = 212263) (by norm_num)
theorem B2013341 : Blo 1340989 2013341 := bbase (se 3 (by rfl) ⟨377501, by rfl⟩ : syracuseStep 2013341 = 755003) (by norm_num)
theorem B3020957 : Blo 1340989 3020957 := bbase (se 3 (by rfl) ⟨566429, by rfl⟩ : syracuseStep 3020957 = 1132859) (by norm_num)
theorem B2013365 : Blo 1340989 2013365 := bbase (se 5 (by rfl) ⟨94376, by rfl⟩ : syracuseStep 2013365 = 188753) (by norm_num)
theorem B2013389 : Blo 1340989 2013389 := bbase (se 3 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 2013389 = 755021) (by norm_num)
theorem B1530085 : Blo 1340989 1530085 := bbase (se 4 (by rfl) ⟨143445, by rfl⟩ : syracuseStep 1530085 = 286891) (by norm_num)
theorem B2013413 : Blo 1340989 2013413 := bbase (se 4 (by rfl) ⟨188757, by rfl⟩ : syracuseStep 2013413 = 377515) (by norm_num)
theorem B3021029 : Blo 1340989 3021029 := bbase (se 4 (by rfl) ⟨283221, by rfl⟩ : syracuseStep 3021029 = 566443) (by norm_num)
theorem B2013437 : Blo 1340989 2013437 := bbase (se 3 (by rfl) ⟨377519, by rfl⟩ : syracuseStep 2013437 = 755039) (by norm_num)
theorem B2013461 : Blo 1340989 2013461 := bbase (se 6 (by rfl) ⟨47190, by rfl⟩ : syracuseStep 2013461 = 94381) (by norm_num)
theorem B3397909 : Blo 1340989 3397909 := bbase (se 6 (by rfl) ⟨79638, by rfl⟩ : syracuseStep 3397909 = 159277) (by norm_num)
theorem B2013485 : Blo 1340989 2013485 := bbase (se 3 (by rfl) ⟨377528, by rfl⟩ : syracuseStep 2013485 = 755057) (by norm_num)
theorem B3021101 : Blo 1340989 3021101 := bbase (se 3 (by rfl) ⟨566456, by rfl⟩ : syracuseStep 3021101 = 1132913) (by norm_num)
theorem B1530181 : Blo 1340989 1530181 := bbase (se 4 (by rfl) ⟨143454, by rfl⟩ : syracuseStep 1530181 = 286909) (by norm_num)
theorem B2013509 : Blo 1340989 2013509 := bbase (se 4 (by rfl) ⟨188766, by rfl⟩ : syracuseStep 2013509 = 377533) (by norm_num)
theorem B2013533 : Blo 1340989 2013533 := bbase (se 3 (by rfl) ⟨377537, by rfl⟩ : syracuseStep 2013533 = 755075) (by norm_num)
theorem B2013557 : Blo 1340989 2013557 := bbase (se 5 (by rfl) ⟨94385, by rfl⟩ : syracuseStep 2013557 = 188771) (by norm_num)
theorem B3021173 : Blo 1340989 3021173 := bbase (se 5 (by rfl) ⟨141617, by rfl⟩ : syracuseStep 3021173 = 283235) (by norm_num)
theorem B3398021 : Blo 1340989 3398021 := bbase (se 4 (by rfl) ⟨318564, by rfl⟩ : syracuseStep 3398021 = 637129) (by norm_num)
theorem B2906501 : Blo 1340989 2906501 := bbase (se 4 (by rfl) ⟨272484, by rfl⟩ : syracuseStep 2906501 = 544969) (by norm_num)
theorem B2013581 : Blo 1340989 2013581 := bbase (se 3 (by rfl) ⟨377546, by rfl⟩ : syracuseStep 2013581 = 755093) (by norm_num)
theorem B2013605 : Blo 1340989 2013605 := bbase (se 4 (by rfl) ⟨188775, by rfl⟩ : syracuseStep 2013605 = 377551) (by norm_num)
theorem B2546093 : Blo 1340989 2546093 := bbase (se 3 (by rfl) ⟨477392, by rfl⟩ : syracuseStep 2546093 = 954785) (by norm_num)
theorem B6445493 : Blo 1340989 6445493 := bbase (se 5 (by rfl) ⟨302132, by rfl⟩ : syracuseStep 6445493 = 604265) (by norm_num)
theorem B2013629 : Blo 1340989 2013629 := bbase (se 3 (by rfl) ⟨377555, by rfl⟩ : syracuseStep 2013629 = 755111) (by norm_num)
theorem B3021245 : Blo 1340989 3021245 := bbase (se 3 (by rfl) ⟨566483, by rfl⟩ : syracuseStep 3021245 = 1132967) (by norm_num)
theorem B2013653 : Blo 1340989 2013653 := bbase (se 7 (by rfl) ⟨23597, by rfl⟩ : syracuseStep 2013653 = 47195) (by norm_num)
theorem B1432037 : Blo 1340989 1432037 := bbase (se 4 (by rfl) ⟨134253, by rfl⟩ : syracuseStep 1432037 = 268507) (by norm_num)
theorem B2013677 : Blo 1340989 2013677 := bbase (se 3 (by rfl) ⟨377564, by rfl⟩ : syracuseStep 2013677 = 755129) (by norm_num)
theorem B2013701 : Blo 1340989 2013701 := bbase (se 4 (by rfl) ⟨188784, by rfl⟩ : syracuseStep 2013701 = 377569) (by norm_num)
theorem B3021317 : Blo 1340989 3021317 := bbase (se 4 (by rfl) ⟨283248, by rfl⟩ : syracuseStep 3021317 = 566497) (by norm_num)
theorem B2013725 : Blo 1340989 2013725 := bbase (se 3 (by rfl) ⟨377573, by rfl⟩ : syracuseStep 2013725 = 755147) (by norm_num)
theorem B2013749 : Blo 1340989 2013749 := bbase (se 5 (by rfl) ⟨94394, by rfl⟩ : syracuseStep 2013749 = 188789) (by norm_num)
theorem B2546245 : Blo 1340989 2546245 := bbase (se 4 (by rfl) ⟨238710, by rfl⟩ : syracuseStep 2546245 = 477421) (by norm_num)
theorem B4528709 : Blo 1340989 4528709 := bbase (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) (by norm_num)
theorem B3398213 : Blo 1340989 3398213 := bbase (se 4 (by rfl) ⟨318582, by rfl⟩ : syracuseStep 3398213 = 637165) (by norm_num)
theorem B5167685 : Blo 1340989 5167685 := bbase (se 4 (by rfl) ⟨484470, by rfl⟩ : syracuseStep 5167685 = 968941) (by norm_num)
theorem B2013773 : Blo 1340989 2013773 := bbase (se 3 (by rfl) ⟨377582, by rfl⟩ : syracuseStep 2013773 = 755165) (by norm_num)
theorem B3021389 : Blo 1340989 3021389 := bbase (se 3 (by rfl) ⟨566510, by rfl⟩ : syracuseStep 3021389 = 1133021) (by norm_num)
theorem B2013797 : Blo 1340989 2013797 := bbase (se 4 (by rfl) ⟨188793, by rfl⟩ : syracuseStep 2013797 = 377587) (by norm_num)
theorem B2013821 : Blo 1340989 2013821 := bbase (se 3 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 2013821 = 755183) (by norm_num)
theorem B2013845 : Blo 1340989 2013845 := bbase (se 6 (by rfl) ⟨47199, by rfl⟩ : syracuseStep 2013845 = 94399) (by norm_num)
theorem B3021461 : Blo 1340989 3021461 := bbase (se 6 (by rfl) ⟨70815, by rfl⟩ : syracuseStep 3021461 = 141631) (by norm_num)
theorem B2013869 : Blo 1340989 2013869 := bbase (se 3 (by rfl) ⟨377600, by rfl⟩ : syracuseStep 2013869 = 755201) (by norm_num)
theorem B6798005 : Blo 1340989 6798005 := bbase (se 5 (by rfl) ⟨318656, by rfl⟩ : syracuseStep 6798005 = 637313) (by norm_num)
theorem B2013893 : Blo 1340989 2013893 := bbase (se 4 (by rfl) ⟨188802, by rfl⟩ : syracuseStep 2013893 = 377605) (by norm_num)
theorem B2013917 : Blo 1340989 2013917 := bbase (se 3 (by rfl) ⟨377609, by rfl⟩ : syracuseStep 2013917 = 755219) (by norm_num)
theorem B3021533 : Blo 1340989 3021533 := bbase (se 3 (by rfl) ⟨566537, by rfl⟩ : syracuseStep 3021533 = 1133075) (by norm_num)
theorem B1432289 : Blo 1340989 1432289 := bbase (se 2 (by rfl) ⟨537108, by rfl⟩ : syracuseStep 1432289 = 1074217) (by norm_num)
theorem B2013941 : Blo 1340989 2013941 := bbase (se 5 (by rfl) ⟨94403, by rfl⟩ : syracuseStep 2013941 = 188807) (by norm_num)
theorem B2013965 : Blo 1340989 2013965 := bbase (se 3 (by rfl) ⟨377618, by rfl⟩ : syracuseStep 2013965 = 755237) (by norm_num)
theorem B3873557 : Blo 1340989 3873557 := bbase (se 6 (by rfl) ⟨90786, by rfl⟩ : syracuseStep 3873557 = 181573) (by norm_num)
theorem B2013989 : Blo 1340989 2013989 := bbase (se 4 (by rfl) ⟨188811, by rfl⟩ : syracuseStep 2013989 = 377623) (by norm_num)
theorem B3021605 : Blo 1340989 3021605 := bbase (se 4 (by rfl) ⟨283275, by rfl⟩ : syracuseStep 3021605 = 566551) (by norm_num)
theorem B2014013 : Blo 1340989 2014013 := bbase (se 3 (by rfl) ⟨377627, by rfl⟩ : syracuseStep 2014013 = 755255) (by norm_num)
theorem B2014037 : Blo 1340989 2014037 := bbase (se 9 (by rfl) ⟨5900, by rfl⟩ : syracuseStep 2014037 = 11801) (by norm_num)
theorem B2866013 : Blo 1340989 2866013 := bbase (se 3 (by rfl) ⟨537377, by rfl⟩ : syracuseStep 2866013 = 1074755) (by norm_num)
theorem B2014061 : Blo 1340989 2014061 := bbase (se 3 (by rfl) ⟨377636, by rfl⟩ : syracuseStep 2014061 = 755273) (by norm_num)
theorem B3021677 : Blo 1340989 3021677 := bbase (se 3 (by rfl) ⟨566564, by rfl⟩ : syracuseStep 3021677 = 1133129) (by norm_num)
theorem B2546549 : Blo 1340989 2546549 := bbase (se 5 (by rfl) ⟨119369, by rfl⟩ : syracuseStep 2546549 = 238739) (by norm_num)
theorem B2014085 : Blo 1340989 2014085 := bbase (se 4 (by rfl) ⟨188820, by rfl⟩ : syracuseStep 2014085 = 377641) (by norm_num)
theorem B3398557 : Blo 1340989 3398557 := bbase (se 3 (by rfl) ⟨637229, by rfl⟩ : syracuseStep 3398557 = 1274459) (by norm_num)
theorem B2014109 : Blo 1340989 2014109 := bbase (se 3 (by rfl) ⟨377645, by rfl⟩ : syracuseStep 2014109 = 755291) (by norm_num)
theorem B2014133 : Blo 1340989 2014133 := bbase (se 5 (by rfl) ⟨94412, by rfl⟩ : syracuseStep 2014133 = 188825) (by norm_num)
theorem B2014157 : Blo 1340989 2014157 := bbase (se 3 (by rfl) ⟨377654, by rfl⟩ : syracuseStep 2014157 = 755309) (by norm_num)
theorem B1612757 : Blo 1340989 1612757 := bbase (se 7 (by rfl) ⟨18899, by rfl⟩ : syracuseStep 1612757 = 37799) (by norm_num)
theorem B5094373 : Blo 1340989 5094373 := bbase (se 4 (by rfl) ⟨477597, by rfl⟩ : syracuseStep 5094373 = 955195) (by norm_num)
theorem B2014181 : Blo 1340989 2014181 := bbase (se 4 (by rfl) ⟨188829, by rfl⟩ : syracuseStep 2014181 = 377659) (by norm_num)
theorem B4529141 : Blo 1340989 4529141 := bbase (se 5 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 4529141 = 424607) (by norm_num)
theorem B2014205 : Blo 1340989 2014205 := bbase (se 3 (by rfl) ⟨377663, by rfl⟩ : syracuseStep 2014205 = 755327) (by norm_num)
theorem B3398669 : Blo 1340989 3398669 := bbase (se 3 (by rfl) ⟨637250, by rfl⟩ : syracuseStep 3398669 = 1274501) (by norm_num)
theorem B2014229 : Blo 1340989 2014229 := bbase (se 6 (by rfl) ⟨47208, by rfl⟩ : syracuseStep 2014229 = 94417) (by norm_num)
theorem B3103789 : Blo 1340989 3103789 := bbase (se 3 (by rfl) ⟨581960, by rfl⟩ : syracuseStep 3103789 = 1163921) (by norm_num)
theorem B2014253 : Blo 1340989 2014253 := bbase (se 3 (by rfl) ⟨377672, by rfl⟩ : syracuseStep 2014253 = 755345) (by norm_num)
theorem B2014277 : Blo 1340989 2014277 := bbase (se 4 (by rfl) ⟨188838, by rfl⟩ : syracuseStep 2014277 = 377677) (by norm_num)
theorem B6790229 : Blo 1340989 6790229 := bbase (se 8 (by rfl) ⟨39786, by rfl⟩ : syracuseStep 6790229 = 79573) (by norm_num)
theorem B2866261 : Blo 1340989 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B2014301 : Blo 1340989 2014301 := bbase (se 3 (by rfl) ⟨377681, by rfl⟩ : syracuseStep 2014301 = 755363) (by norm_num)
theorem B2014325 : Blo 1340989 2014325 := bbase (se 5 (by rfl) ⟨94421, by rfl⟩ : syracuseStep 2014325 = 188843) (by norm_num)
theorem B2014349 : Blo 1340989 2014349 := bbase (se 3 (by rfl) ⟨377690, by rfl⟩ : syracuseStep 2014349 = 755381) (by norm_num)
theorem B1432733 : Blo 1340989 1432733 := bbase (se 3 (by rfl) ⟨268637, by rfl⟩ : syracuseStep 1432733 = 537275) (by norm_num)
theorem B2014373 : Blo 1340989 2014373 := bbase (se 4 (by rfl) ⟨188847, by rfl⟩ : syracuseStep 2014373 = 377695) (by norm_num)
theorem B2014397 : Blo 1340989 2014397 := bbase (se 3 (by rfl) ⟨377699, by rfl⟩ : syracuseStep 2014397 = 755399) (by norm_num)
theorem B3398861 : Blo 1340989 3398861 := bbase (se 3 (by rfl) ⟨637286, by rfl⟩ : syracuseStep 3398861 = 1274573) (by norm_num)
theorem B2014421 : Blo 1340989 2014421 := bbase (se 7 (by rfl) ⟨23606, by rfl⟩ : syracuseStep 2014421 = 47213) (by norm_num)
theorem B2014445 : Blo 1340989 2014445 := bbase (se 3 (by rfl) ⟨377708, by rfl⟩ : syracuseStep 2014445 = 755417) (by norm_num)
theorem B2014469 : Blo 1340989 2014469 := bbase (se 4 (by rfl) ⟨188856, by rfl⟩ : syracuseStep 2014469 = 377713) (by norm_num)
theorem B5094677 : Blo 1340989 5094677 := bbase (se 6 (by rfl) ⟨119406, by rfl⟩ : syracuseStep 5094677 = 238813) (by norm_num)
theorem B1989965 : Blo 1340989 1989965 := bbase (se 3 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 1989965 = 746237) (by norm_num)
theorem B1531225 : Blo 1340989 1531225 := bbase (se 2 (by rfl) ⟨574209, by rfl⟩ : syracuseStep 1531225 = 1148419) (by norm_num)
theorem B1432981 : Blo 1340989 1432981 := bbase (se 6 (by rfl) ⟨33585, by rfl⟩ : syracuseStep 1432981 = 67171) (by norm_num)
theorem B4529573 : Blo 1340989 4529573 := bbase (se 4 (by rfl) ⟨424647, by rfl⟩ : syracuseStep 4529573 = 849295) (by norm_num)
theorem B18357781 : Blo 1340989 18357781 := bbase (se 6 (by rfl) ⟨430260, by rfl⟩ : syracuseStep 18357781 = 860521) (by norm_num)
theorem B1359385 : Blo 1340989 1359385 := bbase (se 2 (by rfl) ⟨509769, by rfl⟩ : syracuseStep 1359385 = 1019539) (by norm_num)
theorem B3399205 : Blo 1340989 3399205 := bbase (se 4 (by rfl) ⟨318675, by rfl⟩ : syracuseStep 3399205 = 637351) (by norm_num)
theorem B1613353 : Blo 1340989 1613353 := bbase (se 2 (by rfl) ⟨605007, by rfl⟩ : syracuseStep 1613353 = 1210015) (by norm_num)
theorem B2866765 : Blo 1340989 2866765 := bbase (se 3 (by rfl) ⟨537518, by rfl⟩ : syracuseStep 2866765 = 1075037) (by norm_num)
theorem B2547301 : Blo 1340989 2547301 := bbase (se 4 (by rfl) ⟨238809, by rfl⟩ : syracuseStep 2547301 = 477619) (by norm_num)
theorem B3399317 : Blo 1340989 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B2547445 : Blo 1340989 2547445 := bbase (se 5 (by rfl) ⟨119411, by rfl⟩ : syracuseStep 2547445 = 238823) (by norm_num)
theorem B1433425 : Blo 1340989 1433425 := bbase (se 2 (by rfl) ⟨537534, by rfl⟩ : syracuseStep 1433425 = 1075069) (by norm_num)
theorem B4530005 : Blo 1340989 4530005 := bbase (se 9 (by rfl) ⟨13271, by rfl⟩ : syracuseStep 4530005 = 26543) (by norm_num)
theorem B7642997 : Blo 1340989 7642997 := bbase (se 5 (by rfl) ⟨358265, by rfl⟩ : syracuseStep 7642997 = 716531) (by norm_num)
theorem B1433485 : Blo 1340989 1433485 := bbase (se 3 (by rfl) ⟨268778, by rfl⟩ : syracuseStep 1433485 = 537557) (by norm_num)
theorem B2547605 : Blo 1340989 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B4833253 : Blo 1340989 4833253 := bbase (se 4 (by rfl) ⟨453117, by rfl⟩ : syracuseStep 4833253 = 906235) (by norm_num)
theorem B5734435 : Blo 1340989 5734435 := bstep (se 1 (by rfl) ⟨4300826, by rfl⟩ : syracuseStep 5734435 = 8601653) B8601653
theorem B4530221 : Blo 1340989 4530221 := bstep (se 3 (by rfl) ⟨849416, by rfl⟩ : syracuseStep 4530221 = 1698833) B1698833
theorem B8601677 : Blo 1340989 8601677 := bstep (se 3 (by rfl) ⟨1612814, by rfl⟩ : syracuseStep 8601677 = 3225629) B3225629
theorem B4530275 : Blo 1340989 4530275 := bstep (se 1 (by rfl) ⟨3397706, by rfl⟩ : syracuseStep 4530275 = 6795413) B6795413
theorem B2719907 : Blo 1340989 2719907 := bstep (se 1 (by rfl) ⟨2039930, by rfl⟩ : syracuseStep 2719907 = 4079861) B4079861
theorem B4833485 : Blo 1340989 4833485 := bstep (se 3 (by rfl) ⟨906278, by rfl⟩ : syracuseStep 4833485 = 1812557) B1812557
theorem B1720595 : Blo 1340989 1720595 := bstep (se 1 (by rfl) ⟨1290446, by rfl⟩ : syracuseStep 1720595 = 2580893) B2580893
theorem B2867491 : Blo 1340989 2867491 := bstep (se 1 (by rfl) ⟨2150618, by rfl⟩ : syracuseStep 2867491 = 4301237) B4301237
theorem B7258403 : Blo 1340989 7258403 := bstep (se 1 (by rfl) ⟨5443802, by rfl⟩ : syracuseStep 7258403 = 10887605) B10887605
theorem B2040113 : Blo 1340989 2040113 := bstep (se 2 (by rfl) ⟨765042, by rfl⟩ : syracuseStep 2040113 = 1530085) B1530085
theorem B4530545 : Blo 1340989 4530545 := bstep (se 2 (by rfl) ⟨1698954, by rfl⟩ : syracuseStep 4530545 = 3397909) B3397909
theorem B29041037 : Blo 1340989 29041037 := bstep (se 3 (by rfl) ⟨5445194, by rfl⟩ : syracuseStep 29041037 = 10890389) B10890389
theorem B7258531 : Blo 1340989 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B1434019 : Blo 1340989 1434019 := bstep (se 1 (by rfl) ⟨1075514, by rfl⟩ : syracuseStep 1434019 = 2151029) B2151029
theorem B2040241 : Blo 1340989 2040241 := bstep (se 2 (by rfl) ⟨765090, by rfl⟩ : syracuseStep 2040241 = 1530181) B1530181
theorem B29000213 : Blo 1340989 29000213 := bstep (se 6 (by rfl) ⟨679692, by rfl⟩ : syracuseStep 29000213 = 1359385) B1359385
theorem B2548273 : Blo 1340989 2548273 := bstep (se 2 (by rfl) ⟨955602, by rfl⟩ : syracuseStep 2548273 = 1911205) B1911205
theorem B7643747 : Blo 1340989 7643747 := bstep (se 1 (by rfl) ⟨5732810, by rfl⟩ : syracuseStep 7643747 = 11465621) B11465621
theorem B10879757 : Blo 1340989 10879757 := bstep (se 3 (by rfl) ⟨2039954, by rfl⟩ : syracuseStep 10879757 = 4079909) B4079909
theorem B2417507 : Blo 1340989 2417507 := bstep (se 1 (by rfl) ⟨1813130, by rfl⟩ : syracuseStep 2417507 = 3626261) B3626261
theorem B2417521 : Blo 1340989 2417521 := bstep (se 2 (by rfl) ⟨906570, by rfl⟩ : syracuseStep 2417521 = 1813141) B1813141
theorem B4531085 : Blo 1340989 4531085 := bstep (se 3 (by rfl) ⟨849578, by rfl⟩ : syracuseStep 4531085 = 1699157) B1699157
theorem B2548675 : Blo 1340989 2548675 := bstep (se 1 (by rfl) ⟨1911506, by rfl⟩ : syracuseStep 2548675 = 3823013) B3823013
theorem B4531139 : Blo 1340989 4531139 := bstep (se 1 (by rfl) ⟨3398354, by rfl⟩ : syracuseStep 4531139 = 6796709) B6796709
theorem B2835427 : Blo 1340989 2835427 := bstep (se 1 (by rfl) ⟨2126570, by rfl⟩ : syracuseStep 2835427 = 4253141) B4253141
theorem B2548721 : Blo 1340989 2548721 := bstep (se 2 (by rfl) ⟨955770, by rfl⟩ : syracuseStep 2548721 = 1911541) B1911541
theorem B1909747 : Blo 1340989 1909747 := bstep (se 1 (by rfl) ⟨1432310, by rfl⟩ : syracuseStep 1909747 = 2864621) B2864621
theorem B7750669 : Blo 1340989 7750669 := bstep (se 3 (by rfl) ⟨1453250, by rfl⟩ : syracuseStep 7750669 = 2906501) B2906501
theorem B12903437 : Blo 1340989 12903437 := bstep (se 3 (by rfl) ⟨2419394, by rfl⟩ : syracuseStep 12903437 = 4838789) B4838789
theorem B2720945 : Blo 1340989 2720945 := bstep (se 2 (by rfl) ⟨1020354, by rfl⟩ : syracuseStep 2720945 = 2040709) B2040709
theorem B4531409 : Blo 1340989 4531409 := bstep (se 2 (by rfl) ⟨1699278, by rfl⟩ : syracuseStep 4531409 = 3398557) B3398557
theorem B3818765 : Blo 1340989 3818765 := bstep (se 3 (by rfl) ⟨716018, by rfl⟩ : syracuseStep 3818765 = 1432037) B1432037
theorem B2721041 : Blo 1340989 2721041 := bstep (se 2 (by rfl) ⟨1020390, by rfl⟩ : syracuseStep 2721041 = 2040781) B2040781
theorem B2549009 : Blo 1340989 2549009 := bstep (se 2 (by rfl) ⟨955878, by rfl⟩ : syracuseStep 2549009 = 1911757) B1911757
theorem B6792497 : Blo 1340989 6792497 := bstep (se 2 (by rfl) ⟨2547186, by rfl⟩ : syracuseStep 6792497 = 5094373) B5094373
theorem B1910083 : Blo 1340989 1910083 := bstep (se 1 (by rfl) ⟨1432562, by rfl⟩ : syracuseStep 1910083 = 2865125) B2865125
theorem B5096803 : Blo 1340989 5096803 := bstep (se 1 (by rfl) ⟨3822602, by rfl⟩ : syracuseStep 5096803 = 7645205) B7645205
theorem B4138385 : Blo 1340989 4138385 := bstep (se 2 (by rfl) ⟨1551894, by rfl⟩ : syracuseStep 4138385 = 3103789) B3103789
theorem B1508755 : Blo 1340989 1508755 := bstep (se 1 (by rfl) ⟨1131566, by rfl⟩ : syracuseStep 1508755 = 2263133) B2263133
theorem B1697203 : Blo 1340989 1697203 := bstep (se 1 (by rfl) ⟨1272902, by rfl⟩ : syracuseStep 1697203 = 2545805) B2545805
theorem B3818947 : Blo 1340989 3818947 := bstep (se 1 (by rfl) ⟨2864210, by rfl⟩ : syracuseStep 3818947 = 5728421) B5728421
theorem B1721827 : Blo 1340989 1721827 := bstep (se 1 (by rfl) ⟨1291370, by rfl⟩ : syracuseStep 1721827 = 2582741) B2582741
theorem B13780493 : Blo 1340989 13780493 := bstep (se 3 (by rfl) ⟨2583842, by rfl⟩ : syracuseStep 13780493 = 5167685) B5167685
theorem B1508899 : Blo 1340989 1508899 := bstep (se 1 (by rfl) ⟨1131674, by rfl⟩ : syracuseStep 1508899 = 2263349) B2263349
theorem B25781813 : Blo 1340989 25781813 := bstep (se 5 (by rfl) ⟨1208522, by rfl⟩ : syracuseStep 25781813 = 2417045) B2417045
theorem B1509043 : Blo 1340989 1509043 := bstep (se 1 (by rfl) ⟨1131782, by rfl⟩ : syracuseStep 1509043 = 2263565) B2263565
theorem B4531949 : Blo 1340989 4531949 := bstep (se 3 (by rfl) ⟨849740, by rfl⟩ : syracuseStep 4531949 = 1699481) B1699481
theorem B2041633 : Blo 1340989 2041633 := bstep (se 2 (by rfl) ⟨765612, by rfl⟩ : syracuseStep 2041633 = 1531225) B1531225
theorem B4532003 : Blo 1340989 4532003 := bstep (se 1 (by rfl) ⟨3399002, by rfl⟩ : syracuseStep 4532003 = 6798005) B6798005
theorem B1509187 : Blo 1340989 1509187 := bstep (se 1 (by rfl) ⟨1131890, by rfl⟩ : syracuseStep 1509187 = 2263781) B2263781
theorem B2582371 : Blo 1340989 2582371 := bstep (se 1 (by rfl) ⟨1936778, by rfl⟩ : syracuseStep 2582371 = 3873557) B3873557
theorem B1910641 : Blo 1340989 1910641 := bstep (se 2 (by rfl) ⟨716490, by rfl⟩ : syracuseStep 1910641 = 1432981) B1432981
theorem B2418545 : Blo 1340989 2418545 := bstep (se 2 (by rfl) ⟨906954, by rfl⟩ : syracuseStep 2418545 = 1813909) B1813909
theorem B4081553 : Blo 1340989 4081553 := bstep (se 2 (by rfl) ⟨1530582, by rfl⟩ : syracuseStep 4081553 = 3061165) B3061165
theorem B1910675 : Blo 1340989 1910675 := bstep (se 1 (by rfl) ⟨1433006, by rfl⟩ : syracuseStep 1910675 = 2866013) B2866013
theorem B1697699 : Blo 1340989 1697699 := bstep (se 1 (by rfl) ⟨1273274, by rfl⟩ : syracuseStep 1697699 = 2546549) B2546549
theorem B3819437 : Blo 1340989 3819437 := bstep (se 3 (by rfl) ⟨716144, by rfl⟩ : syracuseStep 3819437 = 1432289) B1432289
theorem B1509331 : Blo 1340989 1509331 := bstep (se 1 (by rfl) ⟨1131998, by rfl⟩ : syracuseStep 1509331 = 2263997) B2263997
theorem B2263025 : Blo 1340989 2263025 := bstep (se 2 (by rfl) ⟨848634, by rfl⟩ : syracuseStep 2263025 = 1697269) B1697269
theorem B5736433 : Blo 1340989 5736433 := bstep (se 2 (by rfl) ⟨2151162, by rfl⟩ : syracuseStep 5736433 = 4302325) B4302325
theorem B4532273 : Blo 1340989 4532273 := bstep (se 2 (by rfl) ⟨1699602, by rfl⟩ : syracuseStep 4532273 = 3399205) B3399205
theorem B1509475 : Blo 1340989 1509475 := bstep (se 1 (by rfl) ⟨1132106, by rfl⟩ : syracuseStep 1509475 = 2264213) B2264213
theorem B2263153 : Blo 1340989 2263153 := bstep (se 2 (by rfl) ⟨848682, by rfl⟩ : syracuseStep 2263153 = 1697365) B1697365
theorem B26151025 : Blo 1340989 26151025 := bstep (se 2 (by rfl) ⟨9806634, by rfl⟩ : syracuseStep 26151025 = 19613269) B19613269
theorem B2263187 : Blo 1340989 2263187 := bstep (se 1 (by rfl) ⟨1697390, by rfl⟩ : syracuseStep 2263187 = 3394781) B3394781
theorem B1509619 : Blo 1340989 1509619 := bstep (se 1 (by rfl) ⟨1132214, by rfl⟩ : syracuseStep 1509619 = 2264429) B2264429
theorem B2148625 : Blo 1340989 2148625 := bstep (se 2 (by rfl) ⟨805734, by rfl⟩ : syracuseStep 2148625 = 1611469) B1611469
theorem B2263315 : Blo 1340989 2263315 := bstep (se 1 (by rfl) ⟨1697486, by rfl⟩ : syracuseStep 2263315 = 3394973) B3394973
theorem B1509763 : Blo 1340989 1509763 := bstep (se 1 (by rfl) ⟨1132322, by rfl⟩ : syracuseStep 1509763 = 2264645) B2264645
theorem B10185101 : Blo 1340989 10185101 := bstep (se 3 (by rfl) ⟨1909706, by rfl⟩ : syracuseStep 10185101 = 3819413) B3819413
theorem B2263457 : Blo 1340989 2263457 := bstep (se 2 (by rfl) ⟨848796, by rfl⟩ : syracuseStep 2263457 = 1697593) B1697593
theorem B1911233 : Blo 1340989 1911233 := bstep (se 2 (by rfl) ⟨716712, by rfl⟩ : syracuseStep 1911233 = 1433425) B1433425
theorem B4082147 : Blo 1340989 4082147 := bstep (se 1 (by rfl) ⟨3061610, by rfl⟩ : syracuseStep 4082147 = 6123221) B6123221
theorem B1911313 : Blo 1340989 1911313 := bstep (se 2 (by rfl) ⟨716742, by rfl⟩ : syracuseStep 1911313 = 1433485) B1433485
theorem B1509907 : Blo 1340989 1509907 := bstep (se 1 (by rfl) ⟨1132430, by rfl⟩ : syracuseStep 1509907 = 2264861) B2264861
theorem B2263585 : Blo 1340989 2263585 := bstep (se 2 (by rfl) ⟨848844, by rfl⟩ : syracuseStep 2263585 = 1697689) B1697689
theorem B2722339 : Blo 1340989 2722339 := bstep (se 1 (by rfl) ⟨2041754, by rfl⟩ : syracuseStep 2722339 = 4083509) B4083509
theorem B2263619 : Blo 1340989 2263619 := bstep (se 1 (by rfl) ⟨1697714, by rfl⟩ : syracuseStep 2263619 = 3395429) B3395429
theorem B1698403 : Blo 1340989 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B1510051 : Blo 1340989 1510051 := bstep (se 1 (by rfl) ⟨1132538, by rfl⟩ : syracuseStep 1510051 = 2265077) B2265077
theorem B3017393 : Blo 1340989 3017393 := bstep (se 2 (by rfl) ⟨1131522, by rfl⟩ : syracuseStep 3017393 = 2263045) B2263045
theorem B3017411 : Blo 1340989 3017411 := bstep (se 1 (by rfl) ⟨2263058, by rfl⟩ : syracuseStep 3017411 = 4526117) B4526117
theorem B2263747 : Blo 1340989 2263747 := bstep (se 1 (by rfl) ⟨1697810, by rfl⟩ : syracuseStep 2263747 = 3395621) B3395621
theorem B1698499 : Blo 1340989 1698499 := bstep (se 1 (by rfl) ⟨1273874, by rfl⟩ : syracuseStep 1698499 = 2547749) B2547749
theorem B6793955 : Blo 1340989 6793955 := bstep (se 1 (by rfl) ⟨5095466, by rfl⟩ : syracuseStep 6793955 = 10190933) B10190933
theorem B1510195 : Blo 1340989 1510195 := bstep (se 1 (by rfl) ⟨1132646, by rfl⟩ : syracuseStep 1510195 = 2265293) B2265293
theorem B2263889 : Blo 1340989 2263889 := bstep (se 2 (by rfl) ⟨848958, by rfl⟩ : syracuseStep 2263889 = 1697917) B1697917
theorem B4590445 : Blo 1340989 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B1510339 : Blo 1340989 1510339 := bstep (se 1 (by rfl) ⟨1132754, by rfl⟩ : syracuseStep 1510339 = 2265509) B2265509
theorem B17198021 : Blo 1340989 17198021 := bstep (se 4 (by rfl) ⟨1612314, by rfl⟩ : syracuseStep 17198021 = 3224629) B3224629
theorem B3017681 : Blo 1340989 3017681 := bstep (se 2 (by rfl) ⟨1131630, by rfl⟩ : syracuseStep 3017681 = 2263261) B2263261
theorem B2264017 : Blo 1340989 2264017 := bstep (se 2 (by rfl) ⟨849006, by rfl⟩ : syracuseStep 2264017 = 1698013) B1698013
theorem B3017699 : Blo 1340989 3017699 := bstep (se 1 (by rfl) ⟨2263274, by rfl⟩ : syracuseStep 3017699 = 4526549) B4526549
theorem B5164003 : Blo 1340989 5164003 := bstep (se 1 (by rfl) ⟨3873002, by rfl⟩ : syracuseStep 5164003 = 7746005) B7746005
theorem B9677809 : Blo 1340989 9677809 := bstep (se 2 (by rfl) ⟨3629178, by rfl⟩ : syracuseStep 9677809 = 7258357) B7258357
theorem B2264051 : Blo 1340989 2264051 := bstep (se 1 (by rfl) ⟨1698038, by rfl⟩ : syracuseStep 2264051 = 3396077) B3396077
theorem B8596529 : Blo 1340989 8596529 := bstep (se 2 (by rfl) ⟨3223698, by rfl⟩ : syracuseStep 8596529 = 6447397) B6447397
theorem B3820621 : Blo 1340989 3820621 := bstep (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) B1432733
theorem B1510483 : Blo 1340989 1510483 := bstep (se 1 (by rfl) ⟨1132862, by rfl⟩ : syracuseStep 1510483 = 2265725) B2265725
theorem B5729393 : Blo 1340989 5729393 := bstep (se 2 (by rfl) ⟨2148522, by rfl⟩ : syracuseStep 5729393 = 4297045) B4297045
theorem B2264179 : Blo 1340989 2264179 := bstep (se 1 (by rfl) ⟨1698134, by rfl⟩ : syracuseStep 2264179 = 3396269) B3396269
theorem B1698995 : Blo 1340989 1698995 := bstep (se 1 (by rfl) ⟨1274246, by rfl⟩ : syracuseStep 1698995 = 2548493) B2548493
theorem B12905669 : Blo 1340989 12905669 := bstep (se 4 (by rfl) ⟨1209906, by rfl⟩ : syracuseStep 12905669 = 2419813) B2419813
theorem B1510627 : Blo 1340989 1510627 := bstep (se 1 (by rfl) ⟨1132970, by rfl⟩ : syracuseStep 1510627 = 2265941) B2265941
theorem B3017969 : Blo 1340989 3017969 := bstep (se 2 (by rfl) ⟨1131738, by rfl⟩ : syracuseStep 3017969 = 2263477) B2263477
theorem B1813747 : Blo 1340989 1813747 := bstep (se 1 (by rfl) ⟨1360310, by rfl⟩ : syracuseStep 1813747 = 2720621) B2720621
theorem B2264321 : Blo 1340989 2264321 := bstep (se 2 (by rfl) ⟨849120, by rfl⟩ : syracuseStep 2264321 = 1698241) B1698241
theorem B3017987 : Blo 1340989 3017987 := bstep (se 1 (by rfl) ⟨2263490, by rfl⟩ : syracuseStep 3017987 = 4526981) B4526981
theorem B1912099 : Blo 1340989 1912099 := bstep (se 1 (by rfl) ⟨1434074, by rfl⟩ : syracuseStep 1912099 = 2868149) B2868149
theorem B2149715 : Blo 1340989 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B7638371 : Blo 1340989 7638371 := bstep (se 1 (by rfl) ⟨5728778, by rfl⟩ : syracuseStep 7638371 = 11457557) B11457557
theorem B1510771 : Blo 1340989 1510771 := bstep (se 1 (by rfl) ⟨1133078, by rfl⟩ : syracuseStep 1510771 = 2266157) B2266157
theorem B2264449 : Blo 1340989 2264449 := bstep (se 2 (by rfl) ⟨849168, by rfl⟩ : syracuseStep 2264449 = 1698337) B1698337
theorem B2264483 : Blo 1340989 2264483 := bstep (se 1 (by rfl) ⟨1698362, by rfl⟩ : syracuseStep 2264483 = 3396725) B3396725
theorem B3394993 : Blo 1340989 3394993 := bstep (se 2 (by rfl) ⟨1273122, by rfl⟩ : syracuseStep 3394993 = 2546245) B2546245
theorem B6794765 : Blo 1340989 6794765 := bstep (se 3 (by rfl) ⟨1274018, by rfl⟩ : syracuseStep 6794765 = 2548037) B2548037
theorem B5099021 : Blo 1340989 5099021 := bstep (se 3 (by rfl) ⟨956066, by rfl⟩ : syracuseStep 5099021 = 1912133) B1912133
theorem B3018257 : Blo 1340989 3018257 := bstep (se 2 (by rfl) ⟨1131846, by rfl⟩ : syracuseStep 3018257 = 2263693) B2263693
theorem B3018275 : Blo 1340989 3018275 := bstep (se 1 (by rfl) ⟨2263706, by rfl⟩ : syracuseStep 3018275 = 4527413) B4527413
theorem B2264611 : Blo 1340989 2264611 := bstep (se 1 (by rfl) ⟨1698458, by rfl⟩ : syracuseStep 2264611 = 3396917) B3396917
theorem B6532771 : Blo 1340989 6532771 := bstep (se 1 (by rfl) ⟨4899578, by rfl⟩ : syracuseStep 6532771 = 9799157) B9799157
theorem B2264753 : Blo 1340989 2264753 := bstep (se 2 (by rfl) ⟨849282, by rfl⟩ : syracuseStep 2264753 = 1698565) B1698565
theorem B3395267 : Blo 1340989 3395267 := bstep (se 1 (by rfl) ⟨2546450, by rfl⟩ : syracuseStep 3395267 = 5092901) B5092901
theorem B15503089 : Blo 1340989 15503089 := bstep (se 2 (by rfl) ⟨5813658, by rfl⟩ : syracuseStep 15503089 = 11627317) B11627317
theorem B5730061 : Blo 1340989 5730061 := bstep (se 3 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 5730061 = 2148773) B2148773
theorem B6885155 : Blo 1340989 6885155 := bstep (se 1 (by rfl) ⟨5163866, by rfl⟩ : syracuseStep 6885155 = 10327733) B10327733
theorem B3018545 : Blo 1340989 3018545 := bstep (se 2 (by rfl) ⟨1131954, by rfl⟩ : syracuseStep 3018545 = 2263909) B2263909
theorem B2264881 : Blo 1340989 2264881 := bstep (se 2 (by rfl) ⟨849330, by rfl⟩ : syracuseStep 2264881 = 1698661) B1698661
theorem B3018563 : Blo 1340989 3018563 := bstep (se 1 (by rfl) ⟨2263922, by rfl⟩ : syracuseStep 3018563 = 4527845) B4527845
theorem B4525901 : Blo 1340989 4525901 := bstep (se 3 (by rfl) ⟨848606, by rfl⟩ : syracuseStep 4525901 = 1697213) B1697213
theorem B2264915 : Blo 1340989 2264915 := bstep (se 1 (by rfl) ⟨1698686, by rfl⟩ : syracuseStep 2264915 = 3397373) B3397373
theorem B1699699 : Blo 1340989 1699699 := bstep (se 1 (by rfl) ⟨1274774, by rfl⟩ : syracuseStep 1699699 = 2549549) B2549549
theorem B4525955 : Blo 1340989 4525955 := bstep (se 1 (by rfl) ⟨3394466, by rfl⟩ : syracuseStep 4525955 = 6788933) B6788933
theorem B3395459 : Blo 1340989 3395459 := bstep (se 1 (by rfl) ⟨2546594, by rfl⟩ : syracuseStep 3395459 = 5093189) B5093189
theorem B2871235 : Blo 1340989 2871235 := bstep (se 1 (by rfl) ⟨2153426, by rfl⟩ : syracuseStep 2871235 = 4306853) B4306853
theorem B2265043 : Blo 1340989 2265043 := bstep (se 1 (by rfl) ⟨1698782, by rfl⟩ : syracuseStep 2265043 = 3397565) B3397565
theorem B8720389 : Blo 1340989 8720389 := bstep (se 4 (by rfl) ⟨817536, by rfl⟩ : syracuseStep 8720389 = 1635073) B1635073
theorem B2904131 : Blo 1340989 2904131 := bstep (se 1 (by rfl) ⟨2178098, by rfl⟩ : syracuseStep 2904131 = 4356197) B4356197
theorem B3018833 : Blo 1340989 3018833 := bstep (se 2 (by rfl) ⟨1132062, by rfl⟩ : syracuseStep 3018833 = 2264125) B2264125
theorem B2265185 : Blo 1340989 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B3018851 : Blo 1340989 3018851 := bstep (se 1 (by rfl) ⟨2264138, by rfl⟩ : syracuseStep 3018851 = 4528277) B4528277
theorem B3821681 : Blo 1340989 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B4526225 : Blo 1340989 4526225 := bstep (se 2 (by rfl) ⟨1697334, by rfl⟩ : syracuseStep 4526225 = 3394669) B3394669
theorem B2265313 : Blo 1340989 2265313 := bstep (se 2 (by rfl) ⟨849492, by rfl⟩ : syracuseStep 2265313 = 1698985) B1698985
theorem B2265347 : Blo 1340989 2265347 := bstep (se 1 (by rfl) ⟨1699010, by rfl⟩ : syracuseStep 2265347 = 3398021) B3398021
theorem B4296995 : Blo 1340989 4296995 := bstep (se 1 (by rfl) ⟨3222746, by rfl⟩ : syracuseStep 4296995 = 6445493) B6445493
theorem B7639373 : Blo 1340989 7639373 := bstep (se 3 (by rfl) ⟨1432382, by rfl⟩ : syracuseStep 7639373 = 2864765) B2864765
theorem B5730659 : Blo 1340989 5730659 := bstep (se 1 (by rfl) ⟨4297994, by rfl⟩ : syracuseStep 5730659 = 8595989) B8595989
theorem B2011505 : Blo 1340989 2011505 := bstep (se 2 (by rfl) ⟨754314, by rfl⟩ : syracuseStep 2011505 = 1508629) B1508629
theorem B3019121 : Blo 1340989 3019121 := bstep (se 2 (by rfl) ⟨1132170, by rfl⟩ : syracuseStep 3019121 = 2264341) B2264341
theorem B2011523 : Blo 1340989 2011523 := bstep (se 1 (by rfl) ⟨1508642, by rfl⟩ : syracuseStep 2011523 = 3017285) B3017285
theorem B3019139 : Blo 1340989 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B2265475 : Blo 1340989 2265475 := bstep (se 1 (by rfl) ⟨1699106, by rfl⟩ : syracuseStep 2265475 = 3398213) B3398213
theorem B2011553 : Blo 1340989 2011553 := bstep (se 2 (by rfl) ⟨754332, by rfl⟩ : syracuseStep 2011553 = 1508665) B1508665
theorem B5091761 : Blo 1340989 5091761 := bstep (se 2 (by rfl) ⟨1909410, by rfl⟩ : syracuseStep 5091761 = 3818821) B3818821
theorem B2011571 : Blo 1340989 2011571 := bstep (se 1 (by rfl) ⟨1508678, by rfl⟩ : syracuseStep 2011571 = 3017357) B3017357
theorem B2011601 : Blo 1340989 2011601 := bstep (se 2 (by rfl) ⟨754350, by rfl⟩ : syracuseStep 2011601 = 1508701) B1508701
theorem B2011619 : Blo 1340989 2011619 := bstep (se 1 (by rfl) ⟨1508714, by rfl⟩ : syracuseStep 2011619 = 3017429) B3017429
theorem B26145251 : Blo 1340989 26145251 := bstep (se 1 (by rfl) ⟨19608938, by rfl⟩ : syracuseStep 26145251 = 39217877) B39217877
theorem B8597987 : Blo 1340989 8597987 := bstep (se 1 (by rfl) ⟨6448490, by rfl⟩ : syracuseStep 8597987 = 12896981) B12896981
theorem B2011649 : Blo 1340989 2011649 := bstep (se 2 (by rfl) ⟨754368, by rfl⟩ : syracuseStep 2011649 = 1508737) B1508737
theorem B2265617 : Blo 1340989 2265617 := bstep (se 2 (by rfl) ⟨849606, by rfl⟩ : syracuseStep 2265617 = 1699213) B1699213
theorem B2011667 : Blo 1340989 2011667 := bstep (se 1 (by rfl) ⟨1508750, by rfl⟩ : syracuseStep 2011667 = 3017501) B3017501
theorem B2011697 : Blo 1340989 2011697 := bstep (se 2 (by rfl) ⟨754386, by rfl⟩ : syracuseStep 2011697 = 1508773) B1508773
theorem B2011715 : Blo 1340989 2011715 := bstep (se 1 (by rfl) ⟨1508786, by rfl⟩ : syracuseStep 2011715 = 3017573) B3017573
theorem B2011745 : Blo 1340989 2011745 := bstep (se 2 (by rfl) ⟨754404, by rfl⟩ : syracuseStep 2011745 = 1508809) B1508809
theorem B2011763 : Blo 1340989 2011763 := bstep (se 1 (by rfl) ⟨1508822, by rfl⟩ : syracuseStep 2011763 = 3017645) B3017645
theorem B2011793 : Blo 1340989 2011793 := bstep (se 2 (by rfl) ⟨754422, by rfl⟩ : syracuseStep 2011793 = 1508845) B1508845
theorem B3019409 : Blo 1340989 3019409 := bstep (se 2 (by rfl) ⟨1132278, by rfl⟩ : syracuseStep 3019409 = 2264557) B2264557
theorem B2265745 : Blo 1340989 2265745 := bstep (se 2 (by rfl) ⟨849654, by rfl⟩ : syracuseStep 2265745 = 1699309) B1699309
theorem B2011811 : Blo 1340989 2011811 := bstep (se 1 (by rfl) ⟨1508858, by rfl⟩ : syracuseStep 2011811 = 3017717) B3017717
theorem B3019427 : Blo 1340989 3019427 := bstep (se 1 (by rfl) ⟨2264570, by rfl⟩ : syracuseStep 3019427 = 4529141) B4529141
theorem B4526765 : Blo 1340989 4526765 := bstep (se 3 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 4526765 = 1697537) B1697537
theorem B5444273 : Blo 1340989 5444273 := bstep (se 2 (by rfl) ⟨2041602, by rfl⟩ : syracuseStep 5444273 = 4083205) B4083205
theorem B2265779 : Blo 1340989 2265779 := bstep (se 1 (by rfl) ⟨1699334, by rfl⟩ : syracuseStep 2265779 = 3398669) B3398669
theorem B2011841 : Blo 1340989 2011841 := bstep (se 2 (by rfl) ⟨754440, by rfl⟩ : syracuseStep 2011841 = 1508881) B1508881
theorem B2011859 : Blo 1340989 2011859 := bstep (se 1 (by rfl) ⟨1508894, by rfl⟩ : syracuseStep 2011859 = 3017789) B3017789
theorem B2151137 : Blo 1340989 2151137 := bstep (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) B1613353
theorem B4526819 : Blo 1340989 4526819 := bstep (se 1 (by rfl) ⟨3395114, by rfl⟩ : syracuseStep 4526819 = 6790229) B6790229
theorem B20673251 : Blo 1340989 20673251 := bstep (se 1 (by rfl) ⟨15504938, by rfl⟩ : syracuseStep 20673251 = 31009877) B31009877
theorem B2011889 : Blo 1340989 2011889 := bstep (se 2 (by rfl) ⟨754458, by rfl⟩ : syracuseStep 2011889 = 1508917) B1508917
theorem B2011907 : Blo 1340989 2011907 := bstep (se 1 (by rfl) ⟨1508930, by rfl⟩ : syracuseStep 2011907 = 3017861) B3017861
theorem B3822353 : Blo 1340989 3822353 := bstep (se 2 (by rfl) ⟨1433382, by rfl⟩ : syracuseStep 3822353 = 2866765) B2866765
theorem B2011937 : Blo 1340989 2011937 := bstep (se 2 (by rfl) ⟨754476, by rfl⟩ : syracuseStep 2011937 = 1508953) B1508953
theorem B3396401 : Blo 1340989 3396401 := bstep (se 2 (by rfl) ⟨1273650, by rfl⟩ : syracuseStep 3396401 = 2547301) B2547301
theorem B2011955 : Blo 1340989 2011955 := bstep (se 1 (by rfl) ⟨1508966, by rfl⟩ : syracuseStep 2011955 = 3017933) B3017933
theorem B2265907 : Blo 1340989 2265907 := bstep (se 1 (by rfl) ⟨1699430, by rfl⟩ : syracuseStep 2265907 = 3398861) B3398861
theorem B2011985 : Blo 1340989 2011985 := bstep (se 2 (by rfl) ⟨754494, by rfl⟩ : syracuseStep 2011985 = 1508989) B1508989
theorem B2012003 : Blo 1340989 2012003 := bstep (se 1 (by rfl) ⟨1509002, by rfl⟩ : syracuseStep 2012003 = 3018005) B3018005
theorem B3396451 : Blo 1340989 3396451 := bstep (se 1 (by rfl) ⟨2547338, by rfl⟩ : syracuseStep 3396451 = 5094677) B5094677
theorem B2012033 : Blo 1340989 2012033 := bstep (se 2 (by rfl) ⟨754512, by rfl⟩ : syracuseStep 2012033 = 1509025) B1509025
theorem B2012051 : Blo 1340989 2012051 := bstep (se 1 (by rfl) ⟨1509038, by rfl⟩ : syracuseStep 2012051 = 3018077) B3018077
theorem B2012081 : Blo 1340989 2012081 := bstep (se 2 (by rfl) ⟨754530, by rfl⟩ : syracuseStep 2012081 = 1509061) B1509061
theorem B3019697 : Blo 1340989 3019697 := bstep (se 2 (by rfl) ⟨1132386, by rfl⟩ : syracuseStep 3019697 = 2264773) B2264773
theorem B2266049 : Blo 1340989 2266049 := bstep (se 2 (by rfl) ⟨849768, by rfl⟩ : syracuseStep 2266049 = 1699537) B1699537
theorem B2012099 : Blo 1340989 2012099 := bstep (se 1 (by rfl) ⟨1509074, by rfl⟩ : syracuseStep 2012099 = 3018149) B3018149
theorem B3019715 : Blo 1340989 3019715 := bstep (se 1 (by rfl) ⟨2264786, by rfl⟩ : syracuseStep 3019715 = 4529573) B4529573
theorem B2012129 : Blo 1340989 2012129 := bstep (se 2 (by rfl) ⟨754548, by rfl⟩ : syracuseStep 2012129 = 1509097) B1509097
theorem B2864099 : Blo 1340989 2864099 := bstep (se 1 (by rfl) ⟨2148074, by rfl⟩ : syracuseStep 2864099 = 4296149) B4296149
theorem B4527089 : Blo 1340989 4527089 := bstep (se 2 (by rfl) ⟨1697658, by rfl⟩ : syracuseStep 4527089 = 3395317) B3395317
theorem B3396593 : Blo 1340989 3396593 := bstep (se 2 (by rfl) ⟨1273722, by rfl⟩ : syracuseStep 3396593 = 2547445) B2547445
theorem B2012147 : Blo 1340989 2012147 := bstep (se 1 (by rfl) ⟨1509110, by rfl⟩ : syracuseStep 2012147 = 3018221) B3018221
theorem B2012177 : Blo 1340989 2012177 := bstep (se 2 (by rfl) ⟨754566, by rfl⟩ : syracuseStep 2012177 = 1509133) B1509133
theorem B2012195 : Blo 1340989 2012195 := bstep (se 1 (by rfl) ⟨1509146, by rfl⟩ : syracuseStep 2012195 = 3018293) B3018293
theorem B2012225 : Blo 1340989 2012225 := bstep (se 2 (by rfl) ⟨754584, by rfl⟩ : syracuseStep 2012225 = 1509169) B1509169
theorem B2266177 : Blo 1340989 2266177 := bstep (se 2 (by rfl) ⟨849816, by rfl⟩ : syracuseStep 2266177 = 1699633) B1699633
theorem B5092429 : Blo 1340989 5092429 := bstep (se 3 (by rfl) ⟨954830, by rfl⟩ : syracuseStep 5092429 = 1909661) B1909661
theorem B2012243 : Blo 1340989 2012243 := bstep (se 1 (by rfl) ⟨1509182, by rfl⟩ : syracuseStep 2012243 = 3018365) B3018365
theorem B2266211 : Blo 1340989 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B2012273 : Blo 1340989 2012273 := bstep (se 2 (by rfl) ⟨754602, by rfl⟩ : syracuseStep 2012273 = 1509205) B1509205
theorem B2012291 : Blo 1340989 2012291 := bstep (se 1 (by rfl) ⟨1509218, by rfl⟩ : syracuseStep 2012291 = 3018437) B3018437
theorem B2012321 : Blo 1340989 2012321 := bstep (se 2 (by rfl) ⟨754620, by rfl⟩ : syracuseStep 2012321 = 1509241) B1509241
theorem B2012339 : Blo 1340989 2012339 := bstep (se 1 (by rfl) ⟨1509254, by rfl⟩ : syracuseStep 2012339 = 3018509) B3018509
theorem B25777349 : Blo 1340989 25777349 := bstep (se 4 (by rfl) ⟨2416626, by rfl⟩ : syracuseStep 25777349 = 4833253) B4833253
theorem B2012369 : Blo 1340989 2012369 := bstep (se 2 (by rfl) ⟨754638, by rfl⟩ : syracuseStep 2012369 = 1509277) B1509277
theorem B3019985 : Blo 1340989 3019985 := bstep (se 2 (by rfl) ⟨1132494, by rfl⟩ : syracuseStep 3019985 = 2264989) B2264989
theorem B2012387 : Blo 1340989 2012387 := bstep (se 1 (by rfl) ⟨1509290, by rfl⟩ : syracuseStep 2012387 = 3018581) B3018581
theorem B3020003 : Blo 1340989 3020003 := bstep (se 1 (by rfl) ⟨2265002, by rfl⟩ : syracuseStep 3020003 = 4530005) B4530005
theorem B10188017 : Blo 1340989 10188017 := bstep (se 2 (by rfl) ⟨3820506, by rfl⟩ : syracuseStep 10188017 = 7641013) B7641013
theorem B2012417 : Blo 1340989 2012417 := bstep (se 2 (by rfl) ⟨754656, by rfl⟩ : syracuseStep 2012417 = 1509313) B1509313
theorem B2012435 : Blo 1340989 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B6534449 : Blo 1340989 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B2012465 : Blo 1340989 2012465 := bstep (se 2 (by rfl) ⟨754674, by rfl⟩ : syracuseStep 2012465 = 1509349) B1509349
theorem B2012483 : Blo 1340989 2012483 := bstep (se 1 (by rfl) ⟨1509362, by rfl⟩ : syracuseStep 2012483 = 3018725) B3018725
theorem B2012513 : Blo 1340989 2012513 := bstep (se 2 (by rfl) ⟨754692, by rfl⟩ : syracuseStep 2012513 = 1509385) B1509385
theorem B2012531 : Blo 1340989 2012531 := bstep (se 1 (by rfl) ⟨1509398, by rfl⟩ : syracuseStep 2012531 = 3018797) B3018797
theorem B2012561 : Blo 1340989 2012561 := bstep (se 2 (by rfl) ⟨754710, by rfl⟩ : syracuseStep 2012561 = 1509421) B1509421
theorem B2012579 : Blo 1340989 2012579 := bstep (se 1 (by rfl) ⟨1509434, by rfl⟩ : syracuseStep 2012579 = 3018869) B3018869
theorem B2905507 : Blo 1340989 2905507 := bstep (se 1 (by rfl) ⟨2179130, by rfl⟩ : syracuseStep 2905507 = 4358261) B4358261
theorem B2012609 : Blo 1340989 2012609 := bstep (se 2 (by rfl) ⟨754728, by rfl⟩ : syracuseStep 2012609 = 1509457) B1509457
theorem B2012627 : Blo 1340989 2012627 := bstep (se 1 (by rfl) ⟨1509470, by rfl⟩ : syracuseStep 2012627 = 3018941) B3018941
theorem B2012657 : Blo 1340989 2012657 := bstep (se 2 (by rfl) ⟨754746, by rfl⟩ : syracuseStep 2012657 = 1509493) B1509493
theorem B3020273 : Blo 1340989 3020273 := bstep (se 2 (by rfl) ⟨1132602, by rfl⟩ : syracuseStep 3020273 = 2265205) B2265205
theorem B2012675 : Blo 1340989 2012675 := bstep (se 1 (by rfl) ⟨1509506, by rfl⟩ : syracuseStep 2012675 = 3019013) B3019013
theorem B3225091 : Blo 1340989 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B3020291 : Blo 1340989 3020291 := bstep (se 1 (by rfl) ⟨2265218, by rfl⟩ : syracuseStep 3020291 = 4530437) B4530437
theorem B4527629 : Blo 1340989 4527629 := bstep (se 3 (by rfl) ⟨848930, by rfl⟩ : syracuseStep 4527629 = 1697861) B1697861
theorem B2012705 : Blo 1340989 2012705 := bstep (se 2 (by rfl) ⟨754764, by rfl⟩ : syracuseStep 2012705 = 1509529) B1509529
theorem B4298275 : Blo 1340989 4298275 := bstep (se 1 (by rfl) ⟨3223706, by rfl⟩ : syracuseStep 4298275 = 6447413) B6447413
theorem B3823139 : Blo 1340989 3823139 := bstep (se 1 (by rfl) ⟨2867354, by rfl⟩ : syracuseStep 3823139 = 5734709) B5734709
theorem B2012723 : Blo 1340989 2012723 := bstep (se 1 (by rfl) ⟨1509542, by rfl⟩ : syracuseStep 2012723 = 3019085) B3019085
theorem B1340995 : Blo 1340989 1340995 := bstep (se 1 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 1340995 = 2011493) B2011493
theorem B4527683 : Blo 1340989 4527683 := bstep (se 1 (by rfl) ⟨3395762, by rfl⟩ : syracuseStep 4527683 = 6791525) B6791525
theorem B2012753 : Blo 1340989 2012753 := bstep (se 2 (by rfl) ⟨754782, by rfl⟩ : syracuseStep 2012753 = 1509565) B1509565
theorem B1341011 : Blo 1340989 1341011 := bstep (se 1 (by rfl) ⟨1005758, by rfl⟩ : syracuseStep 1341011 = 2011517) B2011517
theorem B1341027 : Blo 1340989 1341027 := bstep (se 1 (by rfl) ⟨1005770, by rfl⟩ : syracuseStep 1341027 = 2011541) B2011541
theorem B2012771 : Blo 1340989 2012771 := bstep (se 1 (by rfl) ⟨1509578, by rfl⟩ : syracuseStep 2012771 = 3019157) B3019157
theorem B3225187 : Blo 1340989 3225187 := bstep (se 1 (by rfl) ⟨2418890, by rfl⟩ : syracuseStep 3225187 = 4837781) B4837781
theorem B1341043 : Blo 1340989 1341043 := bstep (se 1 (by rfl) ⟨1005782, by rfl⟩ : syracuseStep 1341043 = 2011565) B2011565
theorem B2012801 : Blo 1340989 2012801 := bstep (se 2 (by rfl) ⟨754800, by rfl⟩ : syracuseStep 2012801 = 1509601) B1509601
theorem B1341059 : Blo 1340989 1341059 := bstep (se 1 (by rfl) ⟨1005794, by rfl⟩ : syracuseStep 1341059 = 2011589) B2011589
theorem B3626627 : Blo 1340989 3626627 := bstep (se 1 (by rfl) ⟨2719970, by rfl⟩ : syracuseStep 3626627 = 5439941) B5439941
theorem B1341075 : Blo 1340989 1341075 := bstep (se 1 (by rfl) ⟨1005806, by rfl⟩ : syracuseStep 1341075 = 2011613) B2011613
theorem B2012819 : Blo 1340989 2012819 := bstep (se 1 (by rfl) ⟨1509614, by rfl⟩ : syracuseStep 2012819 = 3019229) B3019229
theorem B6788771 : Blo 1340989 6788771 := bstep (se 1 (by rfl) ⟨5091578, by rfl⟩ : syracuseStep 6788771 = 10183157) B10183157
theorem B1341091 : Blo 1340989 1341091 := bstep (se 1 (by rfl) ⟨1005818, by rfl⟩ : syracuseStep 1341091 = 2011637) B2011637
theorem B2012849 : Blo 1340989 2012849 := bstep (se 2 (by rfl) ⟨754818, by rfl⟩ : syracuseStep 2012849 = 1509637) B1509637
theorem B1341107 : Blo 1340989 1341107 := bstep (se 1 (by rfl) ⟨1005830, by rfl⟩ : syracuseStep 1341107 = 2011661) B2011661
theorem B1341123 : Blo 1340989 1341123 := bstep (se 1 (by rfl) ⟨1005842, by rfl⟩ : syracuseStep 1341123 = 2011685) B2011685
theorem B2012867 : Blo 1340989 2012867 := bstep (se 1 (by rfl) ⟨1509650, by rfl⟩ : syracuseStep 2012867 = 3019301) B3019301
theorem B1341139 : Blo 1340989 1341139 := bstep (se 1 (by rfl) ⟨1005854, by rfl⟩ : syracuseStep 1341139 = 2011709) B2011709
theorem B2012897 : Blo 1340989 2012897 := bstep (se 2 (by rfl) ⟨754836, by rfl⟩ : syracuseStep 2012897 = 1509673) B1509673
theorem B1341155 : Blo 1340989 1341155 := bstep (se 1 (by rfl) ⟨1005866, by rfl⟩ : syracuseStep 1341155 = 2011733) B2011733
theorem B18618083 : Blo 1340989 18618083 := bstep (se 1 (by rfl) ⟨13963562, by rfl⟩ : syracuseStep 18618083 = 27927125) B27927125
theorem B1341171 : Blo 1340989 1341171 := bstep (se 1 (by rfl) ⟨1005878, by rfl⟩ : syracuseStep 1341171 = 2011757) B2011757
theorem B2012915 : Blo 1340989 2012915 := bstep (se 1 (by rfl) ⟨1509686, by rfl⟩ : syracuseStep 2012915 = 3019373) B3019373
theorem B1341187 : Blo 1340989 1341187 := bstep (se 1 (by rfl) ⟨1005890, by rfl⟩ : syracuseStep 1341187 = 2011781) B2011781
theorem B2012945 : Blo 1340989 2012945 := bstep (se 2 (by rfl) ⟨754854, by rfl⟩ : syracuseStep 2012945 = 1509709) B1509709
theorem B3020561 : Blo 1340989 3020561 := bstep (se 2 (by rfl) ⟨1132710, by rfl⟩ : syracuseStep 3020561 = 2265421) B2265421
theorem B1341203 : Blo 1340989 1341203 := bstep (se 1 (by rfl) ⟨1005902, by rfl⟩ : syracuseStep 1341203 = 2011805) B2011805
theorem B1341219 : Blo 1340989 1341219 := bstep (se 1 (by rfl) ⟨1005914, by rfl⟩ : syracuseStep 1341219 = 2011829) B2011829
theorem B2012963 : Blo 1340989 2012963 := bstep (se 1 (by rfl) ⟨1509722, by rfl⟩ : syracuseStep 2012963 = 3019445) B3019445
theorem B3020579 : Blo 1340989 3020579 := bstep (se 1 (by rfl) ⟨2265434, by rfl⟩ : syracuseStep 3020579 = 4530869) B4530869
theorem B1341235 : Blo 1340989 1341235 := bstep (se 1 (by rfl) ⟨1005926, by rfl⟩ : syracuseStep 1341235 = 2011853) B2011853
theorem B2012993 : Blo 1340989 2012993 := bstep (se 2 (by rfl) ⟨754872, by rfl⟩ : syracuseStep 2012993 = 1509745) B1509745
theorem B1341251 : Blo 1340989 1341251 := bstep (se 1 (by rfl) ⟨1005938, by rfl⟩ : syracuseStep 1341251 = 2011877) B2011877
theorem B2864963 : Blo 1340989 2864963 := bstep (se 1 (by rfl) ⟨2148722, by rfl⟩ : syracuseStep 2864963 = 4297445) B4297445
theorem B4527953 : Blo 1340989 4527953 := bstep (se 2 (by rfl) ⟨1697982, by rfl⟩ : syracuseStep 4527953 = 3395965) B3395965
theorem B1341267 : Blo 1340989 1341267 := bstep (se 1 (by rfl) ⟨1005950, by rfl⟩ : syracuseStep 1341267 = 2011901) B2011901
theorem B2013011 : Blo 1340989 2013011 := bstep (se 1 (by rfl) ⟨1509758, by rfl⟩ : syracuseStep 2013011 = 3019517) B3019517
theorem B1341283 : Blo 1340989 1341283 := bstep (se 1 (by rfl) ⟨1005962, by rfl⟩ : syracuseStep 1341283 = 2011925) B2011925
theorem B5093219 : Blo 1340989 5093219 := bstep (se 1 (by rfl) ⟨3819914, by rfl⟩ : syracuseStep 5093219 = 7639829) B7639829
theorem B3823469 : Blo 1340989 3823469 := bstep (se 3 (by rfl) ⟨716900, by rfl⟩ : syracuseStep 3823469 = 1433801) B1433801
theorem B4298609 : Blo 1340989 4298609 := bstep (se 2 (by rfl) ⟨1611978, by rfl⟩ : syracuseStep 4298609 = 3223957) B3223957
theorem B2013041 : Blo 1340989 2013041 := bstep (se 2 (by rfl) ⟨754890, by rfl⟩ : syracuseStep 2013041 = 1509781) B1509781
theorem B1341299 : Blo 1340989 1341299 := bstep (se 1 (by rfl) ⟨1005974, by rfl⟩ : syracuseStep 1341299 = 2011949) B2011949
theorem B1341315 : Blo 1340989 1341315 := bstep (se 1 (by rfl) ⟨1005986, by rfl⟩ : syracuseStep 1341315 = 2011973) B2011973
theorem B2013059 : Blo 1340989 2013059 := bstep (se 1 (by rfl) ⟨1509794, by rfl⟩ : syracuseStep 2013059 = 3019589) B3019589
theorem B1341331 : Blo 1340989 1341331 := bstep (se 1 (by rfl) ⟨1005998, by rfl⟩ : syracuseStep 1341331 = 2011997) B2011997
theorem B2013089 : Blo 1340989 2013089 := bstep (se 2 (by rfl) ⟨754908, by rfl⟩ : syracuseStep 2013089 = 1509817) B1509817
theorem B1341347 : Blo 1340989 1341347 := bstep (se 1 (by rfl) ⟨1006010, by rfl⟩ : syracuseStep 1341347 = 2012021) B2012021
theorem B2865073 : Blo 1340989 2865073 := bstep (se 2 (by rfl) ⟨1074402, by rfl⟩ : syracuseStep 2865073 = 2148805) B2148805
theorem B3823537 : Blo 1340989 3823537 := bstep (se 2 (by rfl) ⟨1433826, by rfl⟩ : syracuseStep 3823537 = 2867653) B2867653
theorem B1341363 : Blo 1340989 1341363 := bstep (se 1 (by rfl) ⟨1006022, by rfl⟩ : syracuseStep 1341363 = 2012045) B2012045
theorem B2013107 : Blo 1340989 2013107 := bstep (se 1 (by rfl) ⟨1509830, by rfl⟩ : syracuseStep 2013107 = 3019661) B3019661
theorem B1341379 : Blo 1340989 1341379 := bstep (se 1 (by rfl) ⟨1006034, by rfl⟩ : syracuseStep 1341379 = 2012069) B2012069
theorem B27547589 : Blo 1340989 27547589 := bstep (se 4 (by rfl) ⟨2582586, by rfl⟩ : syracuseStep 27547589 = 5165173) B5165173
theorem B2013137 : Blo 1340989 2013137 := bstep (se 2 (by rfl) ⟨754926, by rfl⟩ : syracuseStep 2013137 = 1509853) B1509853
theorem B3397585 : Blo 1340989 3397585 := bstep (se 2 (by rfl) ⟨1274094, by rfl⟩ : syracuseStep 3397585 = 2548189) B2548189
theorem B1341395 : Blo 1340989 1341395 := bstep (se 1 (by rfl) ⟨1006046, by rfl⟩ : syracuseStep 1341395 = 2012093) B2012093
theorem B1341411 : Blo 1340989 1341411 := bstep (se 1 (by rfl) ⟨1006058, by rfl⟩ : syracuseStep 1341411 = 2012117) B2012117
theorem B4134883 : Blo 1340989 4134883 := bstep (se 1 (by rfl) ⟨3101162, by rfl⟩ : syracuseStep 4134883 = 6202325) B6202325
theorem B2013155 : Blo 1340989 2013155 := bstep (se 1 (by rfl) ⟨1509866, by rfl⟩ : syracuseStep 2013155 = 3019733) B3019733
theorem B1341427 : Blo 1340989 1341427 := bstep (se 1 (by rfl) ⟨1006070, by rfl⟩ : syracuseStep 1341427 = 2012141) B2012141
theorem B2013185 : Blo 1340989 2013185 := bstep (se 2 (by rfl) ⟨754944, by rfl⟩ : syracuseStep 2013185 = 1509889) B1509889
theorem B1341443 : Blo 1340989 1341443 := bstep (se 1 (by rfl) ⟨1006082, by rfl⟩ : syracuseStep 1341443 = 2012165) B2012165
theorem B1341459 : Blo 1340989 1341459 := bstep (se 1 (by rfl) ⟨1006094, by rfl⟩ : syracuseStep 1341459 = 2012189) B2012189
theorem B2013203 : Blo 1340989 2013203 := bstep (se 1 (by rfl) ⟨1509902, by rfl⟩ : syracuseStep 2013203 = 3019805) B3019805
theorem B1341475 : Blo 1340989 1341475 := bstep (se 1 (by rfl) ⟨1006106, by rfl⟩ : syracuseStep 1341475 = 2012213) B2012213
theorem B2013233 : Blo 1340989 2013233 := bstep (se 2 (by rfl) ⟨754962, by rfl⟩ : syracuseStep 2013233 = 1509925) B1509925
theorem B3020849 : Blo 1340989 3020849 := bstep (se 2 (by rfl) ⟨1132818, by rfl⟩ : syracuseStep 3020849 = 2265637) B2265637
theorem B1341491 : Blo 1340989 1341491 := bstep (se 1 (by rfl) ⟨1006118, by rfl⟩ : syracuseStep 1341491 = 2012237) B2012237
theorem B1341507 : Blo 1340989 1341507 := bstep (se 1 (by rfl) ⟨1006130, by rfl⟩ : syracuseStep 1341507 = 2012261) B2012261
theorem B2013251 : Blo 1340989 2013251 := bstep (se 1 (by rfl) ⟨1509938, by rfl⟩ : syracuseStep 2013251 = 3019877) B3019877
theorem B3020867 : Blo 1340989 3020867 := bstep (se 1 (by rfl) ⟨2265650, by rfl⟩ : syracuseStep 3020867 = 4531301) B4531301
theorem B1341523 : Blo 1340989 1341523 := bstep (se 1 (by rfl) ⟨1006142, by rfl⟩ : syracuseStep 1341523 = 2012285) B2012285
theorem B2013281 : Blo 1340989 2013281 := bstep (se 2 (by rfl) ⟨754980, by rfl⟩ : syracuseStep 2013281 = 1509961) B1509961
theorem B1341539 : Blo 1340989 1341539 := bstep (se 1 (by rfl) ⟨1006154, by rfl⟩ : syracuseStep 1341539 = 2012309) B2012309
theorem B1341555 : Blo 1340989 1341555 := bstep (se 1 (by rfl) ⟨1006166, by rfl⟩ : syracuseStep 1341555 = 2012333) B2012333
theorem B2013299 : Blo 1340989 2013299 := bstep (se 1 (by rfl) ⟨1509974, by rfl⟩ : syracuseStep 2013299 = 3019949) B3019949
theorem B1341571 : Blo 1340989 1341571 := bstep (se 1 (by rfl) ⟨1006178, by rfl⟩ : syracuseStep 1341571 = 2012357) B2012357
theorem B2013329 : Blo 1340989 2013329 := bstep (se 2 (by rfl) ⟨754998, by rfl⟩ : syracuseStep 2013329 = 1509997) B1509997
theorem B1341587 : Blo 1340989 1341587 := bstep (se 1 (by rfl) ⟨1006190, by rfl⟩ : syracuseStep 1341587 = 2012381) B2012381
theorem B1341603 : Blo 1340989 1341603 := bstep (se 1 (by rfl) ⟨1006202, by rfl⟩ : syracuseStep 1341603 = 2012405) B2012405
theorem B2013347 : Blo 1340989 2013347 := bstep (se 1 (by rfl) ⟨1510010, by rfl⟩ : syracuseStep 2013347 = 3020021) B3020021
theorem B2906275 : Blo 1340989 2906275 := bstep (se 1 (by rfl) ⟨2179706, by rfl⟩ : syracuseStep 2906275 = 4359413) B4359413
theorem B8599729 : Blo 1340989 8599729 := bstep (se 2 (by rfl) ⟨3224898, by rfl⟩ : syracuseStep 8599729 = 6449797) B6449797
theorem B1341619 : Blo 1340989 1341619 := bstep (se 1 (by rfl) ⟨1006214, by rfl⟩ : syracuseStep 1341619 = 2012429) B2012429
theorem B2013377 : Blo 1340989 2013377 := bstep (se 2 (by rfl) ⟨755016, by rfl⟩ : syracuseStep 2013377 = 1510033) B1510033
theorem B1341635 : Blo 1340989 1341635 := bstep (se 1 (by rfl) ⟨1006226, by rfl⟩ : syracuseStep 1341635 = 2012453) B2012453
theorem B3823811 : Blo 1340989 3823811 := bstep (se 1 (by rfl) ⟨2867858, by rfl⟩ : syracuseStep 3823811 = 5735717) B5735717
theorem B7256261 : Blo 1340989 7256261 := bstep (se 4 (by rfl) ⟨680274, by rfl⟩ : syracuseStep 7256261 = 1360549) B1360549
theorem B5306573 : Blo 1340989 5306573 := bstep (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) B1989965
theorem B1341651 : Blo 1340989 1341651 := bstep (se 1 (by rfl) ⟨1006238, by rfl⟩ : syracuseStep 1341651 = 2012477) B2012477
theorem B2013395 : Blo 1340989 2013395 := bstep (se 1 (by rfl) ⟨1510046, by rfl⟩ : syracuseStep 2013395 = 3020093) B3020093
theorem B1341667 : Blo 1340989 1341667 := bstep (se 1 (by rfl) ⟨1006250, by rfl⟩ : syracuseStep 1341667 = 2012501) B2012501
theorem B3397859 : Blo 1340989 3397859 := bstep (se 1 (by rfl) ⟨2548394, by rfl⟩ : syracuseStep 3397859 = 5096789) B5096789
theorem B2013425 : Blo 1340989 2013425 := bstep (se 2 (by rfl) ⟨755034, by rfl⟩ : syracuseStep 2013425 = 1510069) B1510069
theorem B1341683 : Blo 1340989 1341683 := bstep (se 1 (by rfl) ⟨1006262, by rfl⟩ : syracuseStep 1341683 = 2012525) B2012525
theorem B1341699 : Blo 1340989 1341699 := bstep (se 1 (by rfl) ⟨1006274, by rfl⟩ : syracuseStep 1341699 = 2012549) B2012549
theorem B2013443 : Blo 1340989 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B1341715 : Blo 1340989 1341715 := bstep (se 1 (by rfl) ⟨1006286, by rfl⟩ : syracuseStep 1341715 = 2012573) B2012573
theorem B2013473 : Blo 1340989 2013473 := bstep (se 2 (by rfl) ⟨755052, by rfl⟩ : syracuseStep 2013473 = 1510105) B1510105
theorem B1341731 : Blo 1340989 1341731 := bstep (se 1 (by rfl) ⟨1006298, by rfl⟩ : syracuseStep 1341731 = 2012597) B2012597
theorem B2906417 : Blo 1340989 2906417 := bstep (se 2 (by rfl) ⟨1089906, by rfl⟩ : syracuseStep 2906417 = 2179813) B2179813
theorem B1341747 : Blo 1340989 1341747 := bstep (se 1 (by rfl) ⟨1006310, by rfl⟩ : syracuseStep 1341747 = 2012621) B2012621
theorem B2013491 : Blo 1340989 2013491 := bstep (se 1 (by rfl) ⟨1510118, by rfl⟩ : syracuseStep 2013491 = 3020237) B3020237
theorem B2545987 : Blo 1340989 2545987 := bstep (se 1 (by rfl) ⟨1909490, by rfl⟩ : syracuseStep 2545987 = 3818981) B3818981
theorem B1341763 : Blo 1340989 1341763 := bstep (se 1 (by rfl) ⟨1006322, by rfl⟩ : syracuseStep 1341763 = 2012645) B2012645
theorem B2013521 : Blo 1340989 2013521 := bstep (se 2 (by rfl) ⟨755070, by rfl⟩ : syracuseStep 2013521 = 1510141) B1510141
theorem B3021137 : Blo 1340989 3021137 := bstep (se 2 (by rfl) ⟨1132926, by rfl⟩ : syracuseStep 3021137 = 2265853) B2265853
theorem B1341779 : Blo 1340989 1341779 := bstep (se 1 (by rfl) ⟨1006334, by rfl⟩ : syracuseStep 1341779 = 2012669) B2012669
theorem B1341795 : Blo 1340989 1341795 := bstep (se 1 (by rfl) ⟨1006346, by rfl⟩ : syracuseStep 1341795 = 2012693) B2012693
theorem B2013539 : Blo 1340989 2013539 := bstep (se 1 (by rfl) ⟨1510154, by rfl⟩ : syracuseStep 2013539 = 3020309) B3020309
theorem B3021155 : Blo 1340989 3021155 := bstep (se 1 (by rfl) ⟨2265866, by rfl⟩ : syracuseStep 3021155 = 4531733) B4531733
theorem B4528493 : Blo 1340989 4528493 := bstep (se 3 (by rfl) ⟨849092, by rfl⟩ : syracuseStep 4528493 = 1698185) B1698185
theorem B6797681 : Blo 1340989 6797681 := bstep (se 2 (by rfl) ⟨2549130, by rfl⟩ : syracuseStep 6797681 = 5098261) B5098261
theorem B1341811 : Blo 1340989 1341811 := bstep (se 1 (by rfl) ⟨1006358, by rfl⟩ : syracuseStep 1341811 = 2012717) B2012717
theorem B2013569 : Blo 1340989 2013569 := bstep (se 2 (by rfl) ⟨755088, by rfl⟩ : syracuseStep 2013569 = 1510177) B1510177
theorem B1341827 : Blo 1340989 1341827 := bstep (se 1 (by rfl) ⟨1006370, by rfl⟩ : syracuseStep 1341827 = 2012741) B2012741
theorem B1341843 : Blo 1340989 1341843 := bstep (se 1 (by rfl) ⟨1006382, by rfl⟩ : syracuseStep 1341843 = 2012765) B2012765
theorem B2013587 : Blo 1340989 2013587 := bstep (se 1 (by rfl) ⟨1510190, by rfl⟩ : syracuseStep 2013587 = 3020381) B3020381
theorem B4528547 : Blo 1340989 4528547 := bstep (se 1 (by rfl) ⟨3396410, by rfl⟩ : syracuseStep 4528547 = 6792821) B6792821
theorem B1341859 : Blo 1340989 1341859 := bstep (se 1 (by rfl) ⟨1006394, by rfl⟩ : syracuseStep 1341859 = 2012789) B2012789
theorem B3398051 : Blo 1340989 3398051 := bstep (se 1 (by rfl) ⟨2548538, by rfl⟩ : syracuseStep 3398051 = 5097077) B5097077
theorem B2013617 : Blo 1340989 2013617 := bstep (se 2 (by rfl) ⟨755106, by rfl⟩ : syracuseStep 2013617 = 1510213) B1510213
theorem B1341875 : Blo 1340989 1341875 := bstep (se 1 (by rfl) ⟨1006406, by rfl⟩ : syracuseStep 1341875 = 2012813) B2012813
theorem B1341891 : Blo 1340989 1341891 := bstep (se 1 (by rfl) ⟨1006418, by rfl⟩ : syracuseStep 1341891 = 2012837) B2012837
theorem B2013635 : Blo 1340989 2013635 := bstep (se 1 (by rfl) ⟨1510226, by rfl⟩ : syracuseStep 2013635 = 3020453) B3020453
theorem B6789581 : Blo 1340989 6789581 := bstep (se 3 (by rfl) ⟨1273046, by rfl⟩ : syracuseStep 6789581 = 2546093) B2546093
theorem B4135373 : Blo 1340989 4135373 := bstep (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) B1550765
theorem B1341907 : Blo 1340989 1341907 := bstep (se 1 (by rfl) ⟨1006430, by rfl⟩ : syracuseStep 1341907 = 2012861) B2012861
theorem B2013665 : Blo 1340989 2013665 := bstep (se 2 (by rfl) ⟨755124, by rfl⟩ : syracuseStep 2013665 = 1510249) B1510249
theorem B2546147 : Blo 1340989 2546147 := bstep (se 1 (by rfl) ⟨1909610, by rfl⟩ : syracuseStep 2546147 = 3819221) B3819221
theorem B1341923 : Blo 1340989 1341923 := bstep (se 1 (by rfl) ⟨1006442, by rfl⟩ : syracuseStep 1341923 = 2012885) B2012885
theorem B5093873 : Blo 1340989 5093873 := bstep (se 2 (by rfl) ⟨1910202, by rfl⟩ : syracuseStep 5093873 = 3820405) B3820405
theorem B1341939 : Blo 1340989 1341939 := bstep (se 1 (by rfl) ⟨1006454, by rfl⟩ : syracuseStep 1341939 = 2012909) B2012909
theorem B2013683 : Blo 1340989 2013683 := bstep (se 1 (by rfl) ⟨1510262, by rfl⟩ : syracuseStep 2013683 = 3020525) B3020525
theorem B1341955 : Blo 1340989 1341955 := bstep (se 1 (by rfl) ⟨1006466, by rfl⟩ : syracuseStep 1341955 = 2012933) B2012933
theorem B2013713 : Blo 1340989 2013713 := bstep (se 2 (by rfl) ⟨755142, by rfl⟩ : syracuseStep 2013713 = 1510285) B1510285
theorem B1341971 : Blo 1340989 1341971 := bstep (se 1 (by rfl) ⟨1006478, by rfl⟩ : syracuseStep 1341971 = 2012957) B2012957
theorem B1341987 : Blo 1340989 1341987 := bstep (se 1 (by rfl) ⟨1006490, by rfl⟩ : syracuseStep 1341987 = 2012981) B2012981
theorem B2013731 : Blo 1340989 2013731 := bstep (se 1 (by rfl) ⟨1510298, by rfl⟩ : syracuseStep 2013731 = 3020597) B3020597
theorem B1342003 : Blo 1340989 1342003 := bstep (se 1 (by rfl) ⟨1006502, by rfl⟩ : syracuseStep 1342003 = 2013005) B2013005
theorem B2013761 : Blo 1340989 2013761 := bstep (se 2 (by rfl) ⟨755160, by rfl⟩ : syracuseStep 2013761 = 1510321) B1510321
theorem B1342019 : Blo 1340989 1342019 := bstep (se 1 (by rfl) ⟨1006514, by rfl⟩ : syracuseStep 1342019 = 2013029) B2013029
theorem B1342035 : Blo 1340989 1342035 := bstep (se 1 (by rfl) ⟨1006526, by rfl⟩ : syracuseStep 1342035 = 2013053) B2013053
theorem B2013779 : Blo 1340989 2013779 := bstep (se 1 (by rfl) ⟨1510334, by rfl⟩ : syracuseStep 2013779 = 3020669) B3020669
theorem B1342051 : Blo 1340989 1342051 := bstep (se 1 (by rfl) ⟨1006538, by rfl⟩ : syracuseStep 1342051 = 2013077) B2013077
theorem B12900977 : Blo 1340989 12900977 := bstep (se 2 (by rfl) ⟨4837866, by rfl⟩ : syracuseStep 12900977 = 9675733) B9675733
theorem B2013809 : Blo 1340989 2013809 := bstep (se 2 (by rfl) ⟨755178, by rfl⟩ : syracuseStep 2013809 = 1510357) B1510357
theorem B1342067 : Blo 1340989 1342067 := bstep (se 1 (by rfl) ⟨1006550, by rfl⟩ : syracuseStep 1342067 = 2013101) B2013101
theorem B3021425 : Blo 1340989 3021425 := bstep (se 2 (by rfl) ⟨1133034, by rfl⟩ : syracuseStep 3021425 = 2266069) B2266069
theorem B1342083 : Blo 1340989 1342083 := bstep (se 1 (by rfl) ⟨1006562, by rfl⟩ : syracuseStep 1342083 = 2013125) B2013125
theorem B2013827 : Blo 1340989 2013827 := bstep (se 1 (by rfl) ⟨1510370, by rfl⟩ : syracuseStep 2013827 = 3020741) B3020741
theorem B3021443 : Blo 1340989 3021443 := bstep (se 1 (by rfl) ⟨2266082, by rfl⟩ : syracuseStep 3021443 = 4532165) B4532165
theorem B1342099 : Blo 1340989 1342099 := bstep (se 1 (by rfl) ⟨1006574, by rfl⟩ : syracuseStep 1342099 = 2013149) B2013149
theorem B2013857 : Blo 1340989 2013857 := bstep (se 2 (by rfl) ⟨755196, by rfl⟩ : syracuseStep 2013857 = 1510393) B1510393
theorem B1342115 : Blo 1340989 1342115 := bstep (se 1 (by rfl) ⟨1006586, by rfl⟩ : syracuseStep 1342115 = 2013173) B2013173
theorem B4528817 : Blo 1340989 4528817 := bstep (se 2 (by rfl) ⟨1698306, by rfl⟩ : syracuseStep 4528817 = 3396613) B3396613
theorem B1342131 : Blo 1340989 1342131 := bstep (se 1 (by rfl) ⟨1006598, by rfl⟩ : syracuseStep 1342131 = 2013197) B2013197
theorem B2013875 : Blo 1340989 2013875 := bstep (se 1 (by rfl) ⟨1510406, by rfl⟩ : syracuseStep 2013875 = 3020813) B3020813
theorem B1342147 : Blo 1340989 1342147 := bstep (se 1 (by rfl) ⟨1006610, by rfl⟩ : syracuseStep 1342147 = 2013221) B2013221
theorem B2013905 : Blo 1340989 2013905 := bstep (se 2 (by rfl) ⟨755214, by rfl⟩ : syracuseStep 2013905 = 1510429) B1510429
theorem B3226321 : Blo 1340989 3226321 := bstep (se 2 (by rfl) ⟨1209870, by rfl⟩ : syracuseStep 3226321 = 2419741) B2419741
theorem B1342163 : Blo 1340989 1342163 := bstep (se 1 (by rfl) ⟨1006622, by rfl⟩ : syracuseStep 1342163 = 2013245) B2013245
theorem B1342179 : Blo 1340989 1342179 := bstep (se 1 (by rfl) ⟨1006634, by rfl⟩ : syracuseStep 1342179 = 2013269) B2013269
theorem B2013923 : Blo 1340989 2013923 := bstep (se 1 (by rfl) ⟨1510442, by rfl⟩ : syracuseStep 2013923 = 3020885) B3020885
theorem B1342195 : Blo 1340989 1342195 := bstep (se 1 (by rfl) ⟨1006646, by rfl⟩ : syracuseStep 1342195 = 2013293) B2013293
theorem B2013953 : Blo 1340989 2013953 := bstep (se 2 (by rfl) ⟨755232, by rfl⟩ : syracuseStep 2013953 = 1510465) B1510465
theorem B1342211 : Blo 1340989 1342211 := bstep (se 1 (by rfl) ⟨1006658, by rfl⟩ : syracuseStep 1342211 = 2013317) B2013317
theorem B1342227 : Blo 1340989 1342227 := bstep (se 1 (by rfl) ⟨1006670, by rfl⟩ : syracuseStep 1342227 = 2013341) B2013341
theorem B2013971 : Blo 1340989 2013971 := bstep (se 1 (by rfl) ⟨1510478, by rfl⟩ : syracuseStep 2013971 = 3020957) B3020957
theorem B1342243 : Blo 1340989 1342243 := bstep (se 1 (by rfl) ⟨1006682, by rfl⟩ : syracuseStep 1342243 = 2013365) B2013365
theorem B2014001 : Blo 1340989 2014001 := bstep (se 2 (by rfl) ⟨755250, by rfl⟩ : syracuseStep 2014001 = 1510501) B1510501
theorem B1342259 : Blo 1340989 1342259 := bstep (se 1 (by rfl) ⟨1006694, by rfl⟩ : syracuseStep 1342259 = 2013389) B2013389
theorem B1342275 : Blo 1340989 1342275 := bstep (se 1 (by rfl) ⟨1006706, by rfl⟩ : syracuseStep 1342275 = 2013413) B2013413
theorem B2014019 : Blo 1340989 2014019 := bstep (se 1 (by rfl) ⟨1510514, by rfl⟩ : syracuseStep 2014019 = 3021029) B3021029
theorem B1342291 : Blo 1340989 1342291 := bstep (se 1 (by rfl) ⟨1006718, by rfl⟩ : syracuseStep 1342291 = 2013437) B2013437
theorem B2014049 : Blo 1340989 2014049 := bstep (se 2 (by rfl) ⟨755268, by rfl⟩ : syracuseStep 2014049 = 1510537) B1510537
theorem B1342307 : Blo 1340989 1342307 := bstep (se 1 (by rfl) ⟨1006730, by rfl⟩ : syracuseStep 1342307 = 2013461) B2013461
theorem B1342323 : Blo 1340989 1342323 := bstep (se 1 (by rfl) ⟨1006742, by rfl⟩ : syracuseStep 1342323 = 2013485) B2013485
theorem B2014067 : Blo 1340989 2014067 := bstep (se 1 (by rfl) ⟨1510550, by rfl⟩ : syracuseStep 2014067 = 3021101) B3021101
theorem B1432451 : Blo 1340989 1432451 := bstep (se 1 (by rfl) ⟨1074338, by rfl⟩ : syracuseStep 1432451 = 2148677) B2148677
theorem B1342339 : Blo 1340989 1342339 := bstep (se 1 (by rfl) ⟨1006754, by rfl⟩ : syracuseStep 1342339 = 2013509) B2013509
theorem B2014097 : Blo 1340989 2014097 := bstep (se 2 (by rfl) ⟨755286, by rfl⟩ : syracuseStep 2014097 = 1510573) B1510573
theorem B3021713 : Blo 1340989 3021713 := bstep (se 2 (by rfl) ⟨1133142, by rfl⟩ : syracuseStep 3021713 = 2266285) B2266285
theorem B1342355 : Blo 1340989 1342355 := bstep (se 1 (by rfl) ⟨1006766, by rfl⟩ : syracuseStep 1342355 = 2013533) B2013533
theorem B1342371 : Blo 1340989 1342371 := bstep (se 1 (by rfl) ⟨1006778, by rfl⟩ : syracuseStep 1342371 = 2013557) B2013557
theorem B2014115 : Blo 1340989 2014115 := bstep (se 1 (by rfl) ⟨1510586, by rfl⟩ : syracuseStep 2014115 = 3021173) B3021173
theorem B1342387 : Blo 1340989 1342387 := bstep (se 1 (by rfl) ⟨1006790, by rfl⟩ : syracuseStep 1342387 = 2013581) B2013581
theorem B2014145 : Blo 1340989 2014145 := bstep (se 2 (by rfl) ⟨755304, by rfl⟩ : syracuseStep 2014145 = 1510609) B1510609
theorem B1342403 : Blo 1340989 1342403 := bstep (se 1 (by rfl) ⟨1006802, by rfl⟩ : syracuseStep 1342403 = 2013605) B2013605
theorem B1342419 : Blo 1340989 1342419 := bstep (se 1 (by rfl) ⟨1006814, by rfl⟩ : syracuseStep 1342419 = 2013629) B2013629
theorem B2014163 : Blo 1340989 2014163 := bstep (se 1 (by rfl) ⟨1510622, by rfl⟩ : syracuseStep 2014163 = 3021245) B3021245
theorem B1342435 : Blo 1340989 1342435 := bstep (se 1 (by rfl) ⟨1006826, by rfl⟩ : syracuseStep 1342435 = 2013653) B2013653
theorem B2014193 : Blo 1340989 2014193 := bstep (se 2 (by rfl) ⟨755322, by rfl⟩ : syracuseStep 2014193 = 1510645) B1510645
theorem B1342451 : Blo 1340989 1342451 := bstep (se 1 (by rfl) ⟨1006838, by rfl⟩ : syracuseStep 1342451 = 2013677) B2013677
theorem B1342467 : Blo 1340989 1342467 := bstep (se 1 (by rfl) ⟨1006850, by rfl⟩ : syracuseStep 1342467 = 2013701) B2013701
theorem B2014211 : Blo 1340989 2014211 := bstep (se 1 (by rfl) ⟨1510658, by rfl⟩ : syracuseStep 2014211 = 3021317) B3021317
theorem B1342483 : Blo 1340989 1342483 := bstep (se 1 (by rfl) ⟨1006862, by rfl⟩ : syracuseStep 1342483 = 2013725) B2013725
theorem B2014241 : Blo 1340989 2014241 := bstep (se 2 (by rfl) ⟨755340, by rfl⟩ : syracuseStep 2014241 = 1510681) B1510681
theorem B1342499 : Blo 1340989 1342499 := bstep (se 1 (by rfl) ⟨1006874, by rfl⟩ : syracuseStep 1342499 = 2013749) B2013749
theorem B1342515 : Blo 1340989 1342515 := bstep (se 1 (by rfl) ⟨1006886, by rfl⟩ : syracuseStep 1342515 = 2013773) B2013773
theorem B2014259 : Blo 1340989 2014259 := bstep (se 1 (by rfl) ⟨1510694, by rfl⟩ : syracuseStep 2014259 = 3021389) B3021389
theorem B1342531 : Blo 1340989 1342531 := bstep (se 1 (by rfl) ⟨1006898, by rfl⟩ : syracuseStep 1342531 = 2013797) B2013797
theorem B2014289 : Blo 1340989 2014289 := bstep (se 2 (by rfl) ⟨755358, by rfl⟩ : syracuseStep 2014289 = 1510717) B1510717
theorem B1342547 : Blo 1340989 1342547 := bstep (se 1 (by rfl) ⟨1006910, by rfl⟩ : syracuseStep 1342547 = 2013821) B2013821
theorem B1342563 : Blo 1340989 1342563 := bstep (se 1 (by rfl) ⟨1006922, by rfl⟩ : syracuseStep 1342563 = 2013845) B2013845
theorem B2014307 : Blo 1340989 2014307 := bstep (se 1 (by rfl) ⟨1510730, by rfl⟩ : syracuseStep 2014307 = 3021461) B3021461
theorem B1342579 : Blo 1340989 1342579 := bstep (se 1 (by rfl) ⟨1006934, by rfl⟩ : syracuseStep 1342579 = 2013869) B2013869
theorem B1342595 : Blo 1340989 1342595 := bstep (se 1 (by rfl) ⟨1006946, by rfl⟩ : syracuseStep 1342595 = 2013893) B2013893
theorem B2014337 : Blo 1340989 2014337 := bstep (se 2 (by rfl) ⟨755376, by rfl⟩ : syracuseStep 2014337 = 1510753) B1510753
theorem B1342611 : Blo 1340989 1342611 := bstep (se 1 (by rfl) ⟨1006958, by rfl⟩ : syracuseStep 1342611 = 2013917) B2013917
theorem B2014355 : Blo 1340989 2014355 := bstep (se 1 (by rfl) ⟨1510766, by rfl⟩ : syracuseStep 2014355 = 3021533) B3021533
theorem B1342627 : Blo 1340989 1342627 := bstep (se 1 (by rfl) ⟨1006970, by rfl⟩ : syracuseStep 1342627 = 2013941) B2013941
theorem B7642289 : Blo 1340989 7642289 := bstep (se 2 (by rfl) ⟨2865858, by rfl⟩ : syracuseStep 7642289 = 5731717) B5731717
theorem B1342643 : Blo 1340989 1342643 := bstep (se 1 (by rfl) ⟨1006982, by rfl⟩ : syracuseStep 1342643 = 2013965) B2013965
theorem B2014385 : Blo 1340989 2014385 := bstep (se 2 (by rfl) ⟨755394, by rfl⟩ : syracuseStep 2014385 = 1510789) B1510789
theorem B1342659 : Blo 1340989 1342659 := bstep (se 1 (by rfl) ⟨1006994, by rfl⟩ : syracuseStep 1342659 = 2013989) B2013989
theorem B2014403 : Blo 1340989 2014403 := bstep (se 1 (by rfl) ⟨1510802, by rfl⟩ : syracuseStep 2014403 = 3021605) B3021605
theorem B4529357 : Blo 1340989 4529357 := bstep (se 3 (by rfl) ⟨849254, by rfl⟩ : syracuseStep 4529357 = 1698509) B1698509
theorem B1342675 : Blo 1340989 1342675 := bstep (se 1 (by rfl) ⟨1007006, by rfl⟩ : syracuseStep 1342675 = 2014013) B2014013
theorem B2014433 : Blo 1340989 2014433 := bstep (se 2 (by rfl) ⟨755412, by rfl⟩ : syracuseStep 2014433 = 1510825) B1510825
theorem B1342691 : Blo 1340989 1342691 := bstep (se 1 (by rfl) ⟨1007018, by rfl⟩ : syracuseStep 1342691 = 2014037) B2014037
theorem B1342707 : Blo 1340989 1342707 := bstep (se 1 (by rfl) ⟨1007030, by rfl⟩ : syracuseStep 1342707 = 2014061) B2014061
theorem B2014451 : Blo 1340989 2014451 := bstep (se 1 (by rfl) ⟨1510838, by rfl⟩ : syracuseStep 2014451 = 3021677) B3021677
theorem B4529411 : Blo 1340989 4529411 := bstep (se 1 (by rfl) ⟨3397058, by rfl⟩ : syracuseStep 4529411 = 6794117) B6794117
theorem B1342723 : Blo 1340989 1342723 := bstep (se 1 (by rfl) ⟨1007042, by rfl⟩ : syracuseStep 1342723 = 2014085) B2014085
theorem B2014481 : Blo 1340989 2014481 := bstep (se 2 (by rfl) ⟨755430, by rfl⟩ : syracuseStep 2014481 = 1510861) B1510861
theorem B1342739 : Blo 1340989 1342739 := bstep (se 1 (by rfl) ⟨1007054, by rfl⟩ : syracuseStep 1342739 = 2014109) B2014109
theorem B1342755 : Blo 1340989 1342755 := bstep (se 1 (by rfl) ⟨1007066, by rfl⟩ : syracuseStep 1342755 = 2014133) B2014133
theorem B1342771 : Blo 1340989 1342771 := bstep (se 1 (by rfl) ⟨1007078, by rfl⟩ : syracuseStep 1342771 = 2014157) B2014157
theorem B1342787 : Blo 1340989 1342787 := bstep (se 1 (by rfl) ⟨1007090, by rfl⟩ : syracuseStep 1342787 = 2014181) B2014181
theorem B3398993 : Blo 1340989 3398993 := bstep (se 2 (by rfl) ⟨1274622, by rfl⟩ : syracuseStep 3398993 = 2549245) B2549245
theorem B1342803 : Blo 1340989 1342803 := bstep (se 1 (by rfl) ⟨1007102, by rfl⟩ : syracuseStep 1342803 = 2014205) B2014205
theorem B1342819 : Blo 1340989 1342819 := bstep (se 1 (by rfl) ⟨1007114, by rfl⟩ : syracuseStep 1342819 = 2014229) B2014229
theorem B4078961 : Blo 1340989 4078961 := bstep (se 2 (by rfl) ⟨1529610, by rfl⟩ : syracuseStep 4078961 = 3059221) B3059221
theorem B24477041 : Blo 1340989 24477041 := bstep (se 2 (by rfl) ⟨9178890, by rfl⟩ : syracuseStep 24477041 = 18357781) B18357781
theorem B1342835 : Blo 1340989 1342835 := bstep (se 1 (by rfl) ⟨1007126, by rfl⟩ : syracuseStep 1342835 = 2014253) B2014253
theorem B3399043 : Blo 1340989 3399043 := bstep (se 1 (by rfl) ⟨2549282, by rfl⟩ : syracuseStep 3399043 = 5098565) B5098565
theorem B1342851 : Blo 1340989 1342851 := bstep (se 1 (by rfl) ⟨1007138, by rfl⟩ : syracuseStep 1342851 = 2014277) B2014277
theorem B1342867 : Blo 1340989 1342867 := bstep (se 1 (by rfl) ⟨1007150, by rfl⟩ : syracuseStep 1342867 = 2014301) B2014301
theorem B1342883 : Blo 1340989 1342883 := bstep (se 1 (by rfl) ⟨1007162, by rfl⟩ : syracuseStep 1342883 = 2014325) B2014325
theorem B1342899 : Blo 1340989 1342899 := bstep (se 1 (by rfl) ⟨1007174, by rfl⟩ : syracuseStep 1342899 = 2014349) B2014349
theorem B1342915 : Blo 1340989 1342915 := bstep (se 1 (by rfl) ⟨1007186, by rfl⟩ : syracuseStep 1342915 = 2014373) B2014373
theorem B1342931 : Blo 1340989 1342931 := bstep (se 1 (by rfl) ⟨1007198, by rfl⟩ : syracuseStep 1342931 = 2014397) B2014397
theorem B2039267 : Blo 1340989 2039267 := bstep (se 1 (by rfl) ⟨1529450, by rfl⟩ : syracuseStep 2039267 = 3058901) B3058901
theorem B1342947 : Blo 1340989 1342947 := bstep (se 1 (by rfl) ⟨1007210, by rfl⟩ : syracuseStep 1342947 = 2014421) B2014421
theorem B1342963 : Blo 1340989 1342963 := bstep (se 1 (by rfl) ⟨1007222, by rfl⟩ : syracuseStep 1342963 = 2014445) B2014445
theorem B1342979 : Blo 1340989 1342979 := bstep (se 1 (by rfl) ⟨1007234, by rfl⟩ : syracuseStep 1342979 = 2014469) B2014469
theorem B2547217 : Blo 1340989 2547217 := bstep (se 2 (by rfl) ⟨955206, by rfl⟩ : syracuseStep 2547217 = 1910413) B1910413
theorem B4529681 : Blo 1340989 4529681 := bstep (se 2 (by rfl) ⟨1698630, by rfl⟩ : syracuseStep 4529681 = 3397261) B3397261
theorem B3399185 : Blo 1340989 3399185 := bstep (se 2 (by rfl) ⟨1274694, by rfl⟩ : syracuseStep 3399185 = 2549389) B2549389
theorem B8592965 : Blo 1340989 8592965 := bstep (se 4 (by rfl) ⟨805590, by rfl⟩ : syracuseStep 8592965 = 1611181) B1611181
theorem B3628739 : Blo 1340989 3628739 := bstep (se 1 (by rfl) ⟨2721554, by rfl⟩ : syracuseStep 3628739 = 5443109) B5443109
theorem B4300685 : Blo 1340989 4300685 := bstep (se 3 (by rfl) ⟨806378, by rfl⟩ : syracuseStep 4300685 = 1612757) B1612757
theorem B2867089 : Blo 1340989 2867089 := bstep (se 2 (by rfl) ⟨1075158, by rfl⟩ : syracuseStep 2867089 = 2150317) B2150317
theorem B5095331 : Blo 1340989 5095331 := bstep (se 1 (by rfl) ⟨3821498, by rfl⟩ : syracuseStep 5095331 = 7642997) B7642997
theorem B5095345 : Blo 1340989 5095345 := bstep (se 2 (by rfl) ⟨1910754, by rfl⟩ : syracuseStep 5095345 = 3821509) B3821509
theorem B5734451 : Blo 1340989 5734451 := bstep (se 1 (by rfl) ⟨4300838, by rfl⟩ : syracuseStep 5734451 = 8601677) B8601677
theorem B2547787 : Blo 1340989 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B1360075 : Blo 1340989 1360075 := bstep (se 1 (by rfl) ⟨1020056, by rfl⟩ : syracuseStep 1360075 = 2040113) B2040113
theorem B3875033 : Blo 1340989 3875033 := bstep (se 2 (by rfl) ⟨1453137, by rfl⟩ : syracuseStep 3875033 = 2906275) B2906275
theorem B15278381 : Blo 1340989 15278381 := bstep (se 3 (by rfl) ⟨2864696, by rfl⟩ : syracuseStep 15278381 = 5729393) B5729393
theorem B19333475 : Blo 1340989 19333475 := bstep (se 1 (by rfl) ⟨14500106, by rfl⟩ : syracuseStep 19333475 = 29000213) B29000213
theorem B5095831 : Blo 1340989 5095831 := bstep (se 1 (by rfl) ⟨3821873, by rfl⟩ : syracuseStep 5095831 = 7643747) B7643747
theorem B3629515 : Blo 1340989 3629515 := bstep (se 1 (by rfl) ⟨2722136, by rfl⟩ : syracuseStep 3629515 = 5444273) B5444273
theorem B4530653 : Blo 1340989 4530653 := bstep (se 3 (by rfl) ⟨849497, by rfl⟩ : syracuseStep 4530653 = 1698995) B1698995
theorem B2548235 : Blo 1340989 2548235 := bstep (se 1 (by rfl) ⟨1911176, by rfl⟩ : syracuseStep 2548235 = 3822353) B3822353
theorem B19350029 : Blo 1340989 19350029 := bstep (se 3 (by rfl) ⟨3628130, by rfl⟩ : syracuseStep 19350029 = 7256261) B7256261
theorem B2720321 : Blo 1340989 2720321 := bstep (se 2 (by rfl) ⟨1020120, by rfl⟩ : syracuseStep 2720321 = 2040241) B2040241
theorem B8602291 : Blo 1340989 8602291 := bstep (se 1 (by rfl) ⟨6451718, by rfl⟩ : syracuseStep 8602291 = 12903437) B12903437
theorem B2548417 : Blo 1340989 2548417 := bstep (se 2 (by rfl) ⟨955656, by rfl⟩ : syracuseStep 2548417 = 1911313) B1911313
theorem B3629785 : Blo 1340989 3629785 := bstep (se 2 (by rfl) ⟨1361169, by rfl⟩ : syracuseStep 3629785 = 2722339) B2722339
theorem B4588253 : Blo 1340989 4588253 := bstep (se 3 (by rfl) ⟨860297, by rfl⟩ : syracuseStep 4588253 = 1720595) B1720595
theorem B6792011 : Blo 1340989 6792011 := bstep (se 1 (by rfl) ⟨5094008, by rfl⟩ : syracuseStep 6792011 = 10188017) B10188017
theorem B4301761 : Blo 1340989 4301761 := bstep (se 2 (by rfl) ⟨1613160, by rfl⟩ : syracuseStep 4301761 = 3226321) B3226321
theorem B2548759 : Blo 1340989 2548759 := bstep (se 1 (by rfl) ⟨1911569, by rfl⟩ : syracuseStep 2548759 = 3823139) B3823139
theorem B17187875 : Blo 1340989 17187875 := bstep (se 1 (by rfl) ⟨12890906, by rfl⟩ : syracuseStep 17187875 = 25781813) B25781813
theorem B11035693 : Blo 1340989 11035693 := bstep (se 3 (by rfl) ⟨2069192, by rfl⟩ : syracuseStep 11035693 = 4138385) B4138385
theorem B6120593 : Blo 1340989 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B12412055 : Blo 1340989 12412055 := bstep (se 1 (by rfl) ⟨9309041, by rfl⟩ : syracuseStep 12412055 = 18618083) B18618083
theorem B5096621 : Blo 1340989 5096621 := bstep (se 3 (by rfl) ⟨955616, by rfl⟩ : syracuseStep 5096621 = 1911233) B1911233
theorem B1909975 : Blo 1340989 1909975 := bstep (se 1 (by rfl) ⟨1432481, by rfl⟩ : syracuseStep 1909975 = 2864963) B2864963
theorem B2548979 : Blo 1340989 2548979 := bstep (se 1 (by rfl) ⟨1911734, by rfl⟩ : syracuseStep 2548979 = 3823469) B3823469
theorem B2721035 : Blo 1340989 2721035 := bstep (se 1 (by rfl) ⟨2040776, by rfl⟩ : syracuseStep 2721035 = 4081553) B4081553
theorem B12903745 : Blo 1340989 12903745 := bstep (se 2 (by rfl) ⟨4838904, by rfl⟩ : syracuseStep 12903745 = 9677809) B9677809
theorem B1508683 : Blo 1340989 1508683 := bstep (se 1 (by rfl) ⟨1131512, by rfl⟩ : syracuseStep 1508683 = 2263025) B2263025
theorem B1508791 : Blo 1340989 1508791 := bstep (se 1 (by rfl) ⟨1131593, by rfl⟩ : syracuseStep 1508791 = 2263187) B2263187
theorem B2549207 : Blo 1340989 2549207 := bstep (se 1 (by rfl) ⟨1911905, by rfl⟩ : syracuseStep 2549207 = 3823811) B3823811
theorem B4531787 : Blo 1340989 4531787 := bstep (se 1 (by rfl) ⟨3398840, by rfl⟩ : syracuseStep 4531787 = 6797681) B6797681
theorem B1508971 : Blo 1340989 1508971 := bstep (se 1 (by rfl) ⟨1131728, by rfl⟩ : syracuseStep 1508971 = 2263457) B2263457
theorem B1697431 : Blo 1340989 1697431 := bstep (se 1 (by rfl) ⟨1273073, by rfl⟩ : syracuseStep 1697431 = 2546147) B2546147
theorem B2721431 : Blo 1340989 2721431 := bstep (se 1 (by rfl) ⟨2041073, by rfl⟩ : syracuseStep 2721431 = 4082147) B4082147
theorem B2418329 : Blo 1340989 2418329 := bstep (se 2 (by rfl) ⟨906873, by rfl⟩ : syracuseStep 2418329 = 1813747) B1813747
theorem B1509079 : Blo 1340989 1509079 := bstep (se 1 (by rfl) ⟨1131809, by rfl⟩ : syracuseStep 1509079 = 2263619) B2263619
theorem B2549465 : Blo 1340989 2549465 := bstep (se 2 (by rfl) ⟨956049, by rfl⟩ : syracuseStep 2549465 = 1912099) B1912099
theorem B4532057 : Blo 1340989 4532057 := bstep (se 2 (by rfl) ⟨1699521, by rfl⟩ : syracuseStep 4532057 = 3399043) B3399043
theorem B1509259 : Blo 1340989 1509259 := bstep (se 1 (by rfl) ⟨1131944, by rfl⟩ : syracuseStep 1509259 = 2263889) B2263889
theorem B2262937 : Blo 1340989 2262937 := bstep (se 2 (by rfl) ⟨848601, by rfl⟩ : syracuseStep 2262937 = 1697203) B1697203
theorem B5736365 : Blo 1340989 5736365 := bstep (se 3 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 5736365 = 2151137) B2151137
theorem B1509367 : Blo 1340989 1509367 := bstep (se 1 (by rfl) ⟨1132025, by rfl⟩ : syracuseStep 1509367 = 2264051) B2264051
theorem B8603779 : Blo 1340989 8603779 := bstep (se 1 (by rfl) ⟨6452834, by rfl⟩ : syracuseStep 8603779 = 12905669) B12905669
theorem B1509547 : Blo 1340989 1509547 := bstep (se 1 (by rfl) ⟨1132160, by rfl⟩ : syracuseStep 1509547 = 2264321) B2264321
theorem B8710361 : Blo 1340989 8710361 := bstep (se 2 (by rfl) ⟨3266385, by rfl⟩ : syracuseStep 8710361 = 6532771) B6532771
theorem B1509655 : Blo 1340989 1509655 := bstep (se 1 (by rfl) ⟨1132241, by rfl⟩ : syracuseStep 1509655 = 2264483) B2264483
theorem B11462957 : Blo 1340989 11462957 := bstep (se 3 (by rfl) ⟨2149304, by rfl⟩ : syracuseStep 11462957 = 4298609) B4298609
theorem B6449453 : Blo 1340989 6449453 := bstep (se 3 (by rfl) ⟨1209272, by rfl⟩ : syracuseStep 6449453 = 2418545) B2418545
theorem B20670785 : Blo 1340989 20670785 := bstep (se 2 (by rfl) ⟨7751544, by rfl⟩ : syracuseStep 20670785 = 15503089) B15503089
theorem B3819869 : Blo 1340989 3819869 := bstep (se 3 (by rfl) ⟨716225, by rfl⟩ : syracuseStep 3819869 = 1432451) B1432451
theorem B2722177 : Blo 1340989 2722177 := bstep (se 2 (by rfl) ⟨1020816, by rfl⟩ : syracuseStep 2722177 = 2041633) B2041633
theorem B5728643 : Blo 1340989 5728643 := bstep (se 1 (by rfl) ⟨4296482, by rfl⟩ : syracuseStep 5728643 = 8592965) B8592965
theorem B1509835 : Blo 1340989 1509835 := bstep (se 1 (by rfl) ⟨1132376, by rfl⟩ : syracuseStep 1509835 = 2264753) B2264753
theorem B2263511 : Blo 1340989 2263511 := bstep (se 1 (by rfl) ⟨1697633, by rfl⟩ : syracuseStep 2263511 = 3395267) B3395267
theorem B2419159 : Blo 1340989 2419159 := bstep (se 1 (by rfl) ⟨1814369, by rfl⟩ : syracuseStep 2419159 = 3628739) B3628739
theorem B3443161 : Blo 1340989 3443161 := bstep (se 2 (by rfl) ⟨1291185, by rfl⟩ : syracuseStep 3443161 = 2582371) B2582371
theorem B4590103 : Blo 1340989 4590103 := bstep (se 1 (by rfl) ⟨3442577, by rfl⟩ : syracuseStep 4590103 = 6885155) B6885155
theorem B3017267 : Blo 1340989 3017267 := bstep (se 1 (by rfl) ⟨2262950, by rfl⟩ : syracuseStep 3017267 = 4525901) B4525901
theorem B1509943 : Blo 1340989 1509943 := bstep (se 1 (by rfl) ⟨1132457, by rfl⟩ : syracuseStep 1509943 = 2264915) B2264915
theorem B3820097 : Blo 1340989 3820097 := bstep (se 2 (by rfl) ⟨1432536, by rfl⟩ : syracuseStep 3820097 = 2865073) B2865073
theorem B6793793 : Blo 1340989 6793793 := bstep (se 2 (by rfl) ⟨2547672, by rfl⟩ : syracuseStep 6793793 = 5095345) B5095345
theorem B5098049 : Blo 1340989 5098049 := bstep (se 2 (by rfl) ⟨1911768, by rfl⟩ : syracuseStep 5098049 = 3823537) B3823537
theorem B3017303 : Blo 1340989 3017303 := bstep (se 1 (by rfl) ⟨2262977, by rfl⟩ : syracuseStep 3017303 = 4525955) B4525955
theorem B2263639 : Blo 1340989 2263639 := bstep (se 1 (by rfl) ⟨1697729, by rfl⟩ : syracuseStep 2263639 = 3395459) B3395459
theorem B3828313 : Blo 1340989 3828313 := bstep (se 2 (by rfl) ⟨1435617, by rfl⟩ : syracuseStep 3828313 = 2871235) B2871235
theorem B7637597 : Blo 1340989 7637597 := bstep (se 3 (by rfl) ⟨1432049, by rfl⟩ : syracuseStep 7637597 = 2864099) B2864099
theorem B11627185 : Blo 1340989 11627185 := bstep (se 2 (by rfl) ⟨4360194, by rfl⟩ : syracuseStep 11627185 = 8720389) B8720389
theorem B7645913 : Blo 1340989 7645913 := bstep (se 2 (by rfl) ⟨2867217, by rfl⟩ : syracuseStep 7645913 = 5734435) B5734435
theorem B1510123 : Blo 1340989 1510123 := bstep (se 1 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 1510123 = 2265185) B2265185
theorem B3017483 : Blo 1340989 3017483 := bstep (se 1 (by rfl) ⟨2263112, by rfl⟩ : syracuseStep 3017483 = 4526225) B4526225
theorem B1813271 : Blo 1340989 1813271 := bstep (se 1 (by rfl) ⟨1359953, by rfl⟩ : syracuseStep 1813271 = 2719907) B2719907
theorem B3222323 : Blo 1340989 3222323 := bstep (se 1 (by rfl) ⟨2416742, by rfl⟩ : syracuseStep 3222323 = 4833485) B4833485
theorem B3017537 : Blo 1340989 3017537 := bstep (se 2 (by rfl) ⟨1131576, by rfl⟩ : syracuseStep 3017537 = 2263153) B2263153
theorem B34868033 : Blo 1340989 34868033 := bstep (se 2 (by rfl) ⟨13075512, by rfl⟩ : syracuseStep 34868033 = 26151025) B26151025
theorem B1510231 : Blo 1340989 1510231 := bstep (se 1 (by rfl) ⟨1132673, by rfl⟩ : syracuseStep 1510231 = 2265347) B2265347
theorem B7744349 : Blo 1340989 7744349 := bstep (se 3 (by rfl) ⟨1452065, by rfl⟩ : syracuseStep 7744349 = 2904131) B2904131
theorem B22924133 : Blo 1340989 22924133 := bstep (se 4 (by rfl) ⟨2149137, by rfl⟩ : syracuseStep 22924133 = 4298275) B4298275
theorem B3820439 : Blo 1340989 3820439 := bstep (se 1 (by rfl) ⟨2865329, by rfl⟩ : syracuseStep 3820439 = 5730659) B5730659
theorem B19360691 : Blo 1340989 19360691 := bstep (se 1 (by rfl) ⟨14520518, by rfl⟩ : syracuseStep 19360691 = 29041037) B29041037
theorem B3394507 : Blo 1340989 3394507 := bstep (se 1 (by rfl) ⟨2545880, by rfl⟩ : syracuseStep 3394507 = 5091761) B5091761
theorem B1510411 : Blo 1340989 1510411 := bstep (se 1 (by rfl) ⟨1132808, by rfl⟩ : syracuseStep 1510411 = 2265617) B2265617
theorem B3017753 : Blo 1340989 3017753 := bstep (se 2 (by rfl) ⟨1131657, by rfl⟩ : syracuseStep 3017753 = 2263315) B2263315
theorem B3394649 : Blo 1340989 3394649 := bstep (se 2 (by rfl) ⟨1272993, by rfl⟩ : syracuseStep 3394649 = 2545987) B2545987
theorem B3017843 : Blo 1340989 3017843 := bstep (se 1 (by rfl) ⟨2263382, by rfl⟩ : syracuseStep 3017843 = 4526765) B4526765
theorem B1510519 : Blo 1340989 1510519 := bstep (se 1 (by rfl) ⟨1132889, by rfl⟩ : syracuseStep 1510519 = 2265779) B2265779
theorem B3017879 : Blo 1340989 3017879 := bstep (se 1 (by rfl) ⟨2263409, by rfl⟩ : syracuseStep 3017879 = 4526819) B4526819
theorem B13782167 : Blo 1340989 13782167 := bstep (se 1 (by rfl) ⟨10336625, by rfl⟩ : syracuseStep 13782167 = 20673251) B20673251
theorem B7253171 : Blo 1340989 7253171 := bstep (se 1 (by rfl) ⟨5439878, by rfl⟩ : syracuseStep 7253171 = 10879757) B10879757
theorem B2264267 : Blo 1340989 2264267 := bstep (se 1 (by rfl) ⟨1698200, by rfl⟩ : syracuseStep 2264267 = 3396401) B3396401
theorem B14150861 : Blo 1340989 14150861 := bstep (se 3 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 14150861 = 5306573) B5306573
theorem B9678041 : Blo 1340989 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B1912025 : Blo 1340989 1912025 := bstep (se 2 (by rfl) ⟨717009, by rfl⟩ : syracuseStep 1912025 = 1434019) B1434019
theorem B1510699 : Blo 1340989 1510699 := bstep (se 1 (by rfl) ⟨1133024, by rfl⟩ : syracuseStep 1510699 = 2266049) B2266049
theorem B3018059 : Blo 1340989 3018059 := bstep (se 1 (by rfl) ⟨2263544, by rfl⟩ : syracuseStep 3018059 = 4527089) B4527089
theorem B2264395 : Blo 1340989 2264395 := bstep (se 1 (by rfl) ⟨1698296, by rfl⟩ : syracuseStep 2264395 = 3396593) B3396593
theorem B1699147 : Blo 1340989 1699147 := bstep (se 1 (by rfl) ⟨1274360, by rfl⟩ : syracuseStep 1699147 = 2548721) B2548721
theorem B3018113 : Blo 1340989 3018113 := bstep (se 2 (by rfl) ⟨1131792, by rfl⟩ : syracuseStep 3018113 = 2263585) B2263585
theorem B1510807 : Blo 1340989 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B1813963 : Blo 1340989 1813963 := bstep (se 1 (by rfl) ⟨1360472, by rfl⟩ : syracuseStep 1813963 = 2720945) B2720945
theorem B2264537 : Blo 1340989 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B1814027 : Blo 1340989 1814027 := bstep (se 1 (by rfl) ⟨1360520, by rfl⟩ : syracuseStep 1814027 = 2721041) B2721041
theorem B3018329 : Blo 1340989 3018329 := bstep (se 2 (by rfl) ⟨1131873, by rfl⟩ : syracuseStep 3018329 = 2263747) B2263747
theorem B2264665 : Blo 1340989 2264665 := bstep (se 2 (by rfl) ⟨849249, by rfl⟩ : syracuseStep 2264665 = 1698499) B1698499
theorem B3018419 : Blo 1340989 3018419 := bstep (se 1 (by rfl) ⟨2263814, by rfl⟩ : syracuseStep 3018419 = 4527629) B4527629
theorem B9186995 : Blo 1340989 9186995 := bstep (se 1 (by rfl) ⟨6890246, by rfl⟩ : syracuseStep 9186995 = 13780493) B13780493
theorem B3018455 : Blo 1340989 3018455 := bstep (se 1 (by rfl) ⟨2263841, by rfl⟩ : syracuseStep 3018455 = 4527683) B4527683
theorem B4525847 : Blo 1340989 4525847 := bstep (se 1 (by rfl) ⟨3394385, by rfl⟩ : syracuseStep 4525847 = 6788771) B6788771
theorem B3223361 : Blo 1340989 3223361 := bstep (se 2 (by rfl) ⟨1208760, by rfl⟩ : syracuseStep 3223361 = 2417521) B2417521
theorem B3018635 : Blo 1340989 3018635 := bstep (se 1 (by rfl) ⟨2263976, by rfl⟩ : syracuseStep 3018635 = 4527953) B4527953
theorem B3395479 : Blo 1340989 3395479 := bstep (se 1 (by rfl) ⟨2546609, by rfl⟩ : syracuseStep 3395479 = 5093219) B5093219
theorem B3018689 : Blo 1340989 3018689 := bstep (se 2 (by rfl) ⟨1132008, by rfl⟩ : syracuseStep 3018689 = 2264017) B2264017
theorem B6885337 : Blo 1340989 6885337 := bstep (se 2 (by rfl) ⟨2582001, by rfl⟩ : syracuseStep 6885337 = 5164003) B5164003
theorem B3780569 : Blo 1340989 3780569 := bstep (se 2 (by rfl) ⟨1417713, by rfl⟩ : syracuseStep 3780569 = 2835427) B2835427
theorem B10334225 : Blo 1340989 10334225 := bstep (se 2 (by rfl) ⟨3875334, by rfl⟩ : syracuseStep 10334225 = 7750669) B7750669
theorem B2265239 : Blo 1340989 2265239 := bstep (se 1 (by rfl) ⟨1698929, by rfl⟩ : syracuseStep 2265239 = 3397859) B3397859
theorem B3018905 : Blo 1340989 3018905 := bstep (se 2 (by rfl) ⟨1132089, by rfl⟩ : syracuseStep 3018905 = 2264179) B2264179
theorem B1937611 : Blo 1340989 1937611 := bstep (se 1 (by rfl) ⟨1453208, by rfl⟩ : syracuseStep 1937611 = 2906417) B2906417
theorem B3018995 : Blo 1340989 3018995 := bstep (se 1 (by rfl) ⟨2264246, by rfl⟩ : syracuseStep 3018995 = 4528493) B4528493
theorem B3019031 : Blo 1340989 3019031 := bstep (se 1 (by rfl) ⟨2264273, by rfl⟩ : syracuseStep 3019031 = 4528547) B4528547
theorem B2265367 : Blo 1340989 2265367 := bstep (se 1 (by rfl) ⟨1699025, by rfl⟩ : syracuseStep 2265367 = 3398051) B3398051
theorem B4526387 : Blo 1340989 4526387 := bstep (se 1 (by rfl) ⟨3394790, by rfl⟩ : syracuseStep 4526387 = 6789581) B6789581
theorem B2756915 : Blo 1340989 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B3395915 : Blo 1340989 3395915 := bstep (se 1 (by rfl) ⟨2546936, by rfl⟩ : syracuseStep 3395915 = 5093873) B5093873
theorem B9671005 : Blo 1340989 9671005 := bstep (se 3 (by rfl) ⟨1813313, by rfl⟩ : syracuseStep 9671005 = 3626627) B3626627
theorem B2011595 : Blo 1340989 2011595 := bstep (se 1 (by rfl) ⟨1508696, by rfl⟩ : syracuseStep 2011595 = 3017393) B3017393
theorem B3019211 : Blo 1340989 3019211 := bstep (se 1 (by rfl) ⟨2264408, by rfl⟩ : syracuseStep 3019211 = 4528817) B4528817
theorem B2011607 : Blo 1340989 2011607 := bstep (se 1 (by rfl) ⟨1508705, by rfl⟩ : syracuseStep 2011607 = 3017411) B3017411
theorem B6795737 : Blo 1340989 6795737 := bstep (se 2 (by rfl) ⟨2548401, by rfl⟩ : syracuseStep 6795737 = 5096803) B5096803
theorem B3019265 : Blo 1340989 3019265 := bstep (se 2 (by rfl) ⟨1132224, by rfl⟩ : syracuseStep 3019265 = 2264449) B2264449
theorem B2011673 : Blo 1340989 2011673 := bstep (se 2 (by rfl) ⟨754377, by rfl⟩ : syracuseStep 2011673 = 1508755) B1508755
theorem B4526657 : Blo 1340989 4526657 := bstep (se 2 (by rfl) ⟨1697496, by rfl⟩ : syracuseStep 4526657 = 3394993) B3394993
theorem B5091929 : Blo 1340989 5091929 := bstep (se 2 (by rfl) ⟨1909473, by rfl⟩ : syracuseStep 5091929 = 3818947) B3818947
theorem B11465347 : Blo 1340989 11465347 := bstep (se 1 (by rfl) ⟨8599010, by rfl⟩ : syracuseStep 11465347 = 17198021) B17198021
theorem B2011787 : Blo 1340989 2011787 := bstep (se 1 (by rfl) ⟨1508840, by rfl⟩ : syracuseStep 2011787 = 3017681) B3017681
theorem B2011799 : Blo 1340989 2011799 := bstep (se 1 (by rfl) ⟨1508849, by rfl⟩ : syracuseStep 2011799 = 3017699) B3017699
theorem B3396289 : Blo 1340989 3396289 := bstep (se 2 (by rfl) ⟨1273608, by rfl⟩ : syracuseStep 3396289 = 2547217) B2547217
theorem B5731019 : Blo 1340989 5731019 := bstep (se 1 (by rfl) ⟨4298264, by rfl⟩ : syracuseStep 5731019 = 8596529) B8596529
theorem B2011865 : Blo 1340989 2011865 := bstep (se 2 (by rfl) ⟨754449, by rfl⟩ : syracuseStep 2011865 = 1508899) B1508899
theorem B3019481 : Blo 1340989 3019481 := bstep (se 2 (by rfl) ⟨1132305, by rfl⟩ : syracuseStep 3019481 = 2264611) B2264611
theorem B3019571 : Blo 1340989 3019571 := bstep (se 1 (by rfl) ⟨2264678, by rfl⟩ : syracuseStep 3019571 = 4529357) B4529357
theorem B2011979 : Blo 1340989 2011979 := bstep (se 1 (by rfl) ⟨1508984, by rfl⟩ : syracuseStep 2011979 = 3017969) B3017969
theorem B2011991 : Blo 1340989 2011991 := bstep (se 1 (by rfl) ⟨1508993, by rfl⟩ : syracuseStep 2011991 = 3017987) B3017987
theorem B3019607 : Blo 1340989 3019607 := bstep (se 1 (by rfl) ⟨2264705, by rfl⟩ : syracuseStep 3019607 = 4529411) B4529411
theorem B2265995 : Blo 1340989 2265995 := bstep (se 1 (by rfl) ⟨1699496, by rfl⟩ : syracuseStep 2265995 = 3398993) B3398993
theorem B5092247 : Blo 1340989 5092247 := bstep (se 1 (by rfl) ⟨3819185, by rfl⟩ : syracuseStep 5092247 = 7638371) B7638371
theorem B2012057 : Blo 1340989 2012057 := bstep (se 2 (by rfl) ⟨754521, by rfl⟩ : syracuseStep 2012057 = 1509043) B1509043
theorem B2012171 : Blo 1340989 2012171 := bstep (se 1 (by rfl) ⟨1509128, by rfl⟩ : syracuseStep 2012171 = 3018257) B3018257
theorem B3019787 : Blo 1340989 3019787 := bstep (se 1 (by rfl) ⟨2264840, by rfl⟩ : syracuseStep 3019787 = 4529681) B4529681
theorem B2266123 : Blo 1340989 2266123 := bstep (se 1 (by rfl) ⟨1699592, by rfl⟩ : syracuseStep 2266123 = 3399185) B3399185
theorem B7640081 : Blo 1340989 7640081 := bstep (se 2 (by rfl) ⟨2865030, by rfl⟩ : syracuseStep 7640081 = 5730061) B5730061
theorem B2012183 : Blo 1340989 2012183 := bstep (se 1 (by rfl) ⟨1509137, by rfl⟩ : syracuseStep 2012183 = 3018275) B3018275
theorem B3019841 : Blo 1340989 3019841 := bstep (se 2 (by rfl) ⟨1132440, by rfl⟩ : syracuseStep 3019841 = 2264881) B2264881
theorem B2012249 : Blo 1340989 2012249 := bstep (se 2 (by rfl) ⟨754593, by rfl⟩ : syracuseStep 2012249 = 1509187) B1509187
theorem B4527197 : Blo 1340989 4527197 := bstep (se 3 (by rfl) ⟨848849, by rfl⟩ : syracuseStep 4527197 = 1697699) B1697699
theorem B2266265 : Blo 1340989 2266265 := bstep (se 2 (by rfl) ⟨849849, by rfl⟩ : syracuseStep 2266265 = 1699699) B1699699
theorem B3822785 : Blo 1340989 3822785 := bstep (se 2 (by rfl) ⟨1433544, by rfl⟩ : syracuseStep 3822785 = 2867089) B2867089
theorem B2012363 : Blo 1340989 2012363 := bstep (se 1 (by rfl) ⟨1509272, by rfl⟩ : syracuseStep 2012363 = 3018545) B3018545
theorem B2012375 : Blo 1340989 2012375 := bstep (se 1 (by rfl) ⟨1509281, by rfl⟩ : syracuseStep 2012375 = 3018563) B3018563
theorem B3396887 : Blo 1340989 3396887 := bstep (se 1 (by rfl) ⟨2547665, by rfl⟩ : syracuseStep 3396887 = 5095331) B5095331
theorem B2012441 : Blo 1340989 2012441 := bstep (se 2 (by rfl) ⟨754665, by rfl⟩ : syracuseStep 2012441 = 1509331) B1509331
theorem B3020057 : Blo 1340989 3020057 := bstep (se 2 (by rfl) ⟨1132521, by rfl⟩ : syracuseStep 3020057 = 2265043) B2265043
theorem B7648577 : Blo 1340989 7648577 := bstep (se 2 (by rfl) ⟨2868216, by rfl⟩ : syracuseStep 7648577 = 5736433) B5736433
theorem B3020147 : Blo 1340989 3020147 := bstep (se 1 (by rfl) ⟨2265110, by rfl⟩ : syracuseStep 3020147 = 4530221) B4530221
theorem B2012555 : Blo 1340989 2012555 := bstep (se 1 (by rfl) ⟨1509416, by rfl⟩ : syracuseStep 2012555 = 3018833) B3018833
theorem B2012567 : Blo 1340989 2012567 := bstep (se 1 (by rfl) ⟨1509425, by rfl⟩ : syracuseStep 2012567 = 3018851) B3018851
theorem B3020183 : Blo 1340989 3020183 := bstep (se 1 (by rfl) ⟨2265137, by rfl⟩ : syracuseStep 3020183 = 4530275) B4530275
theorem B2012633 : Blo 1340989 2012633 := bstep (se 2 (by rfl) ⟨754737, by rfl⟩ : syracuseStep 2012633 = 1509475) B1509475
theorem B2864663 : Blo 1340989 2864663 := bstep (se 1 (by rfl) ⟨2148497, by rfl⟩ : syracuseStep 2864663 = 4296995) B4296995
theorem B4838935 : Blo 1340989 4838935 := bstep (se 1 (by rfl) ⟨3629201, by rfl⟩ : syracuseStep 4838935 = 7258403) B7258403
theorem B5092915 : Blo 1340989 5092915 := bstep (se 1 (by rfl) ⟨3819686, by rfl⟩ : syracuseStep 5092915 = 7639373) B7639373
theorem B11466305 : Blo 1340989 11466305 := bstep (se 2 (by rfl) ⟨4299864, by rfl⟩ : syracuseStep 11466305 = 8599729) B8599729
theorem B1341003 : Blo 1340989 1341003 := bstep (se 1 (by rfl) ⟨1005752, by rfl⟩ : syracuseStep 1341003 = 2011505) B2011505
theorem B2012747 : Blo 1340989 2012747 := bstep (se 1 (by rfl) ⟨1509560, by rfl⟩ : syracuseStep 2012747 = 3019121) B3019121
theorem B3020363 : Blo 1340989 3020363 := bstep (se 1 (by rfl) ⟨2265272, by rfl⟩ : syracuseStep 3020363 = 4530545) B4530545
theorem B1341015 : Blo 1340989 1341015 := bstep (se 1 (by rfl) ⟨1005761, by rfl⟩ : syracuseStep 1341015 = 2011523) B2011523
theorem B2012759 : Blo 1340989 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B1341035 : Blo 1340989 1341035 := bstep (se 1 (by rfl) ⟨1005776, by rfl⟩ : syracuseStep 1341035 = 2011553) B2011553
theorem B1341047 : Blo 1340989 1341047 := bstep (se 1 (by rfl) ⟨1005785, by rfl⟩ : syracuseStep 1341047 = 2011571) B2011571
theorem B3020417 : Blo 1340989 3020417 := bstep (se 2 (by rfl) ⟨1132656, by rfl⟩ : syracuseStep 3020417 = 2265313) B2265313
theorem B1341067 : Blo 1340989 1341067 := bstep (se 1 (by rfl) ⟨1005800, by rfl⟩ : syracuseStep 1341067 = 2011601) B2011601
theorem B1341079 : Blo 1340989 1341079 := bstep (se 1 (by rfl) ⟨1005809, by rfl⟩ : syracuseStep 1341079 = 2011619) B2011619
theorem B17430167 : Blo 1340989 17430167 := bstep (se 1 (by rfl) ⟨13072625, by rfl⟩ : syracuseStep 17430167 = 26145251) B26145251
theorem B2012825 : Blo 1340989 2012825 := bstep (se 2 (by rfl) ⟨754809, by rfl⟩ : syracuseStep 2012825 = 1509619) B1509619
theorem B5731991 : Blo 1340989 5731991 := bstep (se 1 (by rfl) ⟨4298993, by rfl⟩ : syracuseStep 5731991 = 8597987) B8597987
theorem B1341099 : Blo 1340989 1341099 := bstep (se 1 (by rfl) ⟨1005824, by rfl⟩ : syracuseStep 1341099 = 2011649) B2011649
theorem B1341111 : Blo 1340989 1341111 := bstep (se 1 (by rfl) ⟨1005833, by rfl⟩ : syracuseStep 1341111 = 2011667) B2011667
theorem B1341131 : Blo 1340989 1341131 := bstep (se 1 (by rfl) ⟨1005848, by rfl⟩ : syracuseStep 1341131 = 2011697) B2011697
theorem B1341143 : Blo 1340989 1341143 := bstep (se 1 (by rfl) ⟨1005857, by rfl⟩ : syracuseStep 1341143 = 2011715) B2011715
theorem B3823321 : Blo 1340989 3823321 := bstep (se 2 (by rfl) ⟨1433745, by rfl⟩ : syracuseStep 3823321 = 2867491) B2867491
theorem B1341163 : Blo 1340989 1341163 := bstep (se 1 (by rfl) ⟨1005872, by rfl⟩ : syracuseStep 1341163 = 2011745) B2011745
theorem B1341175 : Blo 1340989 1341175 := bstep (se 1 (by rfl) ⟨1005881, by rfl⟩ : syracuseStep 1341175 = 2011763) B2011763
theorem B1341195 : Blo 1340989 1341195 := bstep (se 1 (by rfl) ⟨1005896, by rfl⟩ : syracuseStep 1341195 = 2011793) B2011793
theorem B2012939 : Blo 1340989 2012939 := bstep (se 1 (by rfl) ⟨1509704, by rfl⟩ : syracuseStep 2012939 = 3019409) B3019409
theorem B1341207 : Blo 1340989 1341207 := bstep (se 1 (by rfl) ⟨1005905, by rfl⟩ : syracuseStep 1341207 = 2011811) B2011811
theorem B2012951 : Blo 1340989 2012951 := bstep (se 1 (by rfl) ⟨1509713, by rfl⟩ : syracuseStep 2012951 = 3019427) B3019427
theorem B1341227 : Blo 1340989 1341227 := bstep (se 1 (by rfl) ⟨1005920, by rfl⟩ : syracuseStep 1341227 = 2011841) B2011841
theorem B1341239 : Blo 1340989 1341239 := bstep (se 1 (by rfl) ⟨1005929, by rfl⟩ : syracuseStep 1341239 = 2011859) B2011859
theorem B1341259 : Blo 1340989 1341259 := bstep (se 1 (by rfl) ⟨1005944, by rfl⟩ : syracuseStep 1341259 = 2011889) B2011889
theorem B1341271 : Blo 1340989 1341271 := bstep (se 1 (by rfl) ⟨1005953, by rfl⟩ : syracuseStep 1341271 = 2011907) B2011907
theorem B2013017 : Blo 1340989 2013017 := bstep (se 2 (by rfl) ⟨754881, by rfl⟩ : syracuseStep 2013017 = 1509763) B1509763
theorem B3020633 : Blo 1340989 3020633 := bstep (se 2 (by rfl) ⟨1132737, by rfl⟩ : syracuseStep 3020633 = 2265475) B2265475
theorem B17200997 : Blo 1340989 17200997 := bstep (se 4 (by rfl) ⟨1612593, by rfl⟩ : syracuseStep 17200997 = 3225187) B3225187
theorem B1341291 : Blo 1340989 1341291 := bstep (se 1 (by rfl) ⟨1005968, by rfl⟩ : syracuseStep 1341291 = 2011937) B2011937
theorem B1341303 : Blo 1340989 1341303 := bstep (se 1 (by rfl) ⟨1005977, by rfl⟩ : syracuseStep 1341303 = 2011955) B2011955
theorem B1341323 : Blo 1340989 1341323 := bstep (se 1 (by rfl) ⟨1005992, by rfl⟩ : syracuseStep 1341323 = 2011985) B2011985
theorem B1341335 : Blo 1340989 1341335 := bstep (se 1 (by rfl) ⟨1006001, by rfl⟩ : syracuseStep 1341335 = 2012003) B2012003
theorem B1611671 : Blo 1340989 1611671 := bstep (se 1 (by rfl) ⟨1208753, by rfl⟩ : syracuseStep 1611671 = 2417507) B2417507
theorem B1341355 : Blo 1340989 1341355 := bstep (se 1 (by rfl) ⟨1006016, by rfl⟩ : syracuseStep 1341355 = 2012033) B2012033
theorem B3020723 : Blo 1340989 3020723 := bstep (se 1 (by rfl) ⟨2265542, by rfl⟩ : syracuseStep 3020723 = 4531085) B4531085
theorem B1341367 : Blo 1340989 1341367 := bstep (se 1 (by rfl) ⟨1006025, by rfl⟩ : syracuseStep 1341367 = 2012051) B2012051
theorem B1341387 : Blo 1340989 1341387 := bstep (se 1 (by rfl) ⟨1006040, by rfl⟩ : syracuseStep 1341387 = 2012081) B2012081
theorem B2013131 : Blo 1340989 2013131 := bstep (se 1 (by rfl) ⟨1509848, by rfl⟩ : syracuseStep 2013131 = 3019697) B3019697
theorem B1341399 : Blo 1340989 1341399 := bstep (se 1 (by rfl) ⟨1006049, by rfl⟩ : syracuseStep 1341399 = 2012099) B2012099
theorem B2013143 : Blo 1340989 2013143 := bstep (se 1 (by rfl) ⟨1509857, by rfl⟩ : syracuseStep 2013143 = 3019715) B3019715
theorem B3020759 : Blo 1340989 3020759 := bstep (se 1 (by rfl) ⟨2265569, by rfl⟩ : syracuseStep 3020759 = 4531139) B4531139
theorem B1341419 : Blo 1340989 1341419 := bstep (se 1 (by rfl) ⟨1006064, by rfl⟩ : syracuseStep 1341419 = 2012129) B2012129
theorem B1341431 : Blo 1340989 1341431 := bstep (se 1 (by rfl) ⟨1006073, by rfl⟩ : syracuseStep 1341431 = 2012147) B2012147
theorem B1341451 : Blo 1340989 1341451 := bstep (se 1 (by rfl) ⟨1006088, by rfl⟩ : syracuseStep 1341451 = 2012177) B2012177
theorem B1341463 : Blo 1340989 1341463 := bstep (se 1 (by rfl) ⟨1006097, by rfl⟩ : syracuseStep 1341463 = 2012195) B2012195
theorem B2013209 : Blo 1340989 2013209 := bstep (se 2 (by rfl) ⟨754953, by rfl⟩ : syracuseStep 2013209 = 1509907) B1509907
theorem B1341483 : Blo 1340989 1341483 := bstep (se 1 (by rfl) ⟨1006112, by rfl⟩ : syracuseStep 1341483 = 2012225) B2012225
theorem B6797357 : Blo 1340989 6797357 := bstep (se 3 (by rfl) ⟨1274504, by rfl⟩ : syracuseStep 6797357 = 2549009) B2549009
theorem B1341495 : Blo 1340989 1341495 := bstep (se 1 (by rfl) ⟨1006121, by rfl⟩ : syracuseStep 1341495 = 2012243) B2012243
theorem B3397697 : Blo 1340989 3397697 := bstep (se 2 (by rfl) ⟨1274136, by rfl⟩ : syracuseStep 3397697 = 2548273) B2548273
theorem B1341515 : Blo 1340989 1341515 := bstep (se 1 (by rfl) ⟨1006136, by rfl⟩ : syracuseStep 1341515 = 2012273) B2012273
theorem B1341527 : Blo 1340989 1341527 := bstep (se 1 (by rfl) ⟨1006145, by rfl⟩ : syracuseStep 1341527 = 2012291) B2012291
theorem B1341547 : Blo 1340989 1341547 := bstep (se 1 (by rfl) ⟨1006160, by rfl⟩ : syracuseStep 1341547 = 2012321) B2012321
theorem B1341559 : Blo 1340989 1341559 := bstep (se 1 (by rfl) ⟨1006169, by rfl⟩ : syracuseStep 1341559 = 2012339) B2012339
theorem B17184899 : Blo 1340989 17184899 := bstep (se 1 (by rfl) ⟨12888674, by rfl⟩ : syracuseStep 17184899 = 25777349) B25777349
theorem B1341579 : Blo 1340989 1341579 := bstep (se 1 (by rfl) ⟨1006184, by rfl⟩ : syracuseStep 1341579 = 2012369) B2012369
theorem B2013323 : Blo 1340989 2013323 := bstep (se 1 (by rfl) ⟨1509992, by rfl⟩ : syracuseStep 2013323 = 3019985) B3019985
theorem B3020939 : Blo 1340989 3020939 := bstep (se 1 (by rfl) ⟨2265704, by rfl⟩ : syracuseStep 3020939 = 4531409) B4531409
theorem B1341591 : Blo 1340989 1341591 := bstep (se 1 (by rfl) ⟨1006193, by rfl⟩ : syracuseStep 1341591 = 2012387) B2012387
theorem B2013335 : Blo 1340989 2013335 := bstep (se 1 (by rfl) ⟨1510001, by rfl⟩ : syracuseStep 2013335 = 3020003) B3020003
theorem B1341611 : Blo 1340989 1341611 := bstep (se 1 (by rfl) ⟨1006208, by rfl⟩ : syracuseStep 1341611 = 2012417) B2012417
theorem B2545843 : Blo 1340989 2545843 := bstep (se 1 (by rfl) ⟨1909382, by rfl⟩ : syracuseStep 2545843 = 3818765) B3818765
theorem B1341623 : Blo 1340989 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B3020993 : Blo 1340989 3020993 := bstep (se 2 (by rfl) ⟨1132872, by rfl⟩ : syracuseStep 3020993 = 2265745) B2265745
theorem B4356299 : Blo 1340989 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B1341643 : Blo 1340989 1341643 := bstep (se 1 (by rfl) ⟨1006232, by rfl⟩ : syracuseStep 1341643 = 2012465) B2012465
theorem B4528331 : Blo 1340989 4528331 := bstep (se 1 (by rfl) ⟨3396248, by rfl⟩ : syracuseStep 4528331 = 6792497) B6792497
theorem B1341655 : Blo 1340989 1341655 := bstep (se 1 (by rfl) ⟨1006241, by rfl⟩ : syracuseStep 1341655 = 2012483) B2012483
theorem B2013401 : Blo 1340989 2013401 := bstep (se 2 (by rfl) ⟨755025, by rfl⟩ : syracuseStep 2013401 = 1510051) B1510051
theorem B1341675 : Blo 1340989 1341675 := bstep (se 1 (by rfl) ⟨1006256, by rfl⟩ : syracuseStep 1341675 = 2012513) B2012513
theorem B1341687 : Blo 1340989 1341687 := bstep (se 1 (by rfl) ⟨1006265, by rfl⟩ : syracuseStep 1341687 = 2012531) B2012531
theorem B1341707 : Blo 1340989 1341707 := bstep (se 1 (by rfl) ⟨1006280, by rfl⟩ : syracuseStep 1341707 = 2012561) B2012561
theorem B1341719 : Blo 1340989 1341719 := bstep (se 1 (by rfl) ⟨1006289, by rfl⟩ : syracuseStep 1341719 = 2012579) B2012579
theorem B1341739 : Blo 1340989 1341739 := bstep (se 1 (by rfl) ⟨1006304, by rfl⟩ : syracuseStep 1341739 = 2012609) B2012609
theorem B1341751 : Blo 1340989 1341751 := bstep (se 1 (by rfl) ⟨1006313, by rfl⟩ : syracuseStep 1341751 = 2012627) B2012627
theorem B1341771 : Blo 1340989 1341771 := bstep (se 1 (by rfl) ⟨1006328, by rfl⟩ : syracuseStep 1341771 = 2012657) B2012657
theorem B2013515 : Blo 1340989 2013515 := bstep (se 1 (by rfl) ⟨1510136, by rfl⟩ : syracuseStep 2013515 = 3020273) B3020273
theorem B1341783 : Blo 1340989 1341783 := bstep (se 1 (by rfl) ⟨1006337, by rfl⟩ : syracuseStep 1341783 = 2012675) B2012675
theorem B2013527 : Blo 1340989 2013527 := bstep (se 1 (by rfl) ⟨1510145, by rfl⟩ : syracuseStep 2013527 = 3020291) B3020291
theorem B1341803 : Blo 1340989 1341803 := bstep (se 1 (by rfl) ⟨1006352, by rfl⟩ : syracuseStep 1341803 = 2012705) B2012705
theorem B1341815 : Blo 1340989 1341815 := bstep (se 1 (by rfl) ⟨1006361, by rfl⟩ : syracuseStep 1341815 = 2012723) B2012723
theorem B1341835 : Blo 1340989 1341835 := bstep (se 1 (by rfl) ⟨1006376, by rfl⟩ : syracuseStep 1341835 = 2012753) B2012753
theorem B1341847 : Blo 1340989 1341847 := bstep (se 1 (by rfl) ⟨1006385, by rfl⟩ : syracuseStep 1341847 = 2012771) B2012771
theorem B2013593 : Blo 1340989 2013593 := bstep (se 2 (by rfl) ⟨755097, by rfl⟩ : syracuseStep 2013593 = 1510195) B1510195
theorem B3021209 : Blo 1340989 3021209 := bstep (se 2 (by rfl) ⟨1132953, by rfl⟩ : syracuseStep 3021209 = 2265907) B2265907
theorem B1341867 : Blo 1340989 1341867 := bstep (se 1 (by rfl) ⟨1006400, by rfl⟩ : syracuseStep 1341867 = 2012801) B2012801
theorem B1341879 : Blo 1340989 1341879 := bstep (se 1 (by rfl) ⟨1006409, by rfl⟩ : syracuseStep 1341879 = 2012819) B2012819
theorem B1341899 : Blo 1340989 1341899 := bstep (se 1 (by rfl) ⟨1006424, by rfl⟩ : syracuseStep 1341899 = 2012849) B2012849
theorem B1341911 : Blo 1340989 1341911 := bstep (se 1 (by rfl) ⟨1006433, by rfl⟩ : syracuseStep 1341911 = 2012867) B2012867
theorem B4528601 : Blo 1340989 4528601 := bstep (se 2 (by rfl) ⟨1698225, by rfl⟩ : syracuseStep 4528601 = 3396451) B3396451
theorem B1341931 : Blo 1340989 1341931 := bstep (se 1 (by rfl) ⟨1006448, by rfl⟩ : syracuseStep 1341931 = 2012897) B2012897
theorem B3021299 : Blo 1340989 3021299 := bstep (se 1 (by rfl) ⟨2265974, by rfl⟩ : syracuseStep 3021299 = 4531949) B4531949
theorem B1341943 : Blo 1340989 1341943 := bstep (se 1 (by rfl) ⟨1006457, by rfl⟩ : syracuseStep 1341943 = 2012915) B2012915
theorem B1341963 : Blo 1340989 1341963 := bstep (se 1 (by rfl) ⟨1006472, by rfl⟩ : syracuseStep 1341963 = 2012945) B2012945
theorem B2013707 : Blo 1340989 2013707 := bstep (se 1 (by rfl) ⟨1510280, by rfl⟩ : syracuseStep 2013707 = 3020561) B3020561
theorem B1341975 : Blo 1340989 1341975 := bstep (se 1 (by rfl) ⟨1006481, by rfl⟩ : syracuseStep 1341975 = 2012963) B2012963
theorem B2013719 : Blo 1340989 2013719 := bstep (se 1 (by rfl) ⟨1510289, by rfl⟩ : syracuseStep 2013719 = 3020579) B3020579
theorem B3021335 : Blo 1340989 3021335 := bstep (se 1 (by rfl) ⟨2266001, by rfl⟩ : syracuseStep 3021335 = 4532003) B4532003
theorem B1341995 : Blo 1340989 1341995 := bstep (se 1 (by rfl) ⟨1006496, by rfl⟩ : syracuseStep 1341995 = 2012993) B2012993
theorem B1342007 : Blo 1340989 1342007 := bstep (se 1 (by rfl) ⟨1006505, by rfl⟩ : syracuseStep 1342007 = 2013011) B2013011
theorem B1342027 : Blo 1340989 1342027 := bstep (se 1 (by rfl) ⟨1006520, by rfl⟩ : syracuseStep 1342027 = 2013041) B2013041
theorem B1342039 : Blo 1340989 1342039 := bstep (se 1 (by rfl) ⟨1006529, by rfl⟩ : syracuseStep 1342039 = 2013059) B2013059
theorem B3398233 : Blo 1340989 3398233 := bstep (se 2 (by rfl) ⟨1274337, by rfl⟩ : syracuseStep 3398233 = 2548675) B2548675
theorem B2013785 : Blo 1340989 2013785 := bstep (se 2 (by rfl) ⟨755169, by rfl⟩ : syracuseStep 2013785 = 1510339) B1510339
theorem B1342059 : Blo 1340989 1342059 := bstep (se 1 (by rfl) ⟨1006544, by rfl⟩ : syracuseStep 1342059 = 2013089) B2013089
theorem B2546291 : Blo 1340989 2546291 := bstep (se 1 (by rfl) ⟨1909718, by rfl⟩ : syracuseStep 2546291 = 3819437) B3819437
theorem B1342071 : Blo 1340989 1342071 := bstep (se 1 (by rfl) ⟨1006553, by rfl⟩ : syracuseStep 1342071 = 2013107) B2013107
theorem B18365059 : Blo 1340989 18365059 := bstep (se 1 (by rfl) ⟨13773794, by rfl⟩ : syracuseStep 18365059 = 27547589) B27547589
theorem B1342091 : Blo 1340989 1342091 := bstep (se 1 (by rfl) ⟨1006568, by rfl⟩ : syracuseStep 1342091 = 2013137) B2013137
theorem B1342103 : Blo 1340989 1342103 := bstep (se 1 (by rfl) ⟨1006577, by rfl⟩ : syracuseStep 1342103 = 2013155) B2013155
theorem B2546329 : Blo 1340989 2546329 := bstep (se 2 (by rfl) ⟨954873, by rfl⟩ : syracuseStep 2546329 = 1909747) B1909747
theorem B1342123 : Blo 1340989 1342123 := bstep (se 1 (by rfl) ⟨1006592, by rfl⟩ : syracuseStep 1342123 = 2013185) B2013185
theorem B1342135 : Blo 1340989 1342135 := bstep (se 1 (by rfl) ⟨1006601, by rfl⟩ : syracuseStep 1342135 = 2013203) B2013203
theorem B1342155 : Blo 1340989 1342155 := bstep (se 1 (by rfl) ⟨1006616, by rfl⟩ : syracuseStep 1342155 = 2013233) B2013233
theorem B2013899 : Blo 1340989 2013899 := bstep (se 1 (by rfl) ⟨1510424, by rfl⟩ : syracuseStep 2013899 = 3020849) B3020849
theorem B3021515 : Blo 1340989 3021515 := bstep (se 1 (by rfl) ⟨2266136, by rfl⟩ : syracuseStep 3021515 = 4532273) B4532273
theorem B1342167 : Blo 1340989 1342167 := bstep (se 1 (by rfl) ⟨1006625, by rfl⟩ : syracuseStep 1342167 = 2013251) B2013251
theorem B2013911 : Blo 1340989 2013911 := bstep (se 1 (by rfl) ⟨1510433, by rfl⟩ : syracuseStep 2013911 = 3020867) B3020867
theorem B1342187 : Blo 1340989 1342187 := bstep (se 1 (by rfl) ⟨1006640, by rfl⟩ : syracuseStep 1342187 = 2013281) B2013281
theorem B1342199 : Blo 1340989 1342199 := bstep (se 1 (by rfl) ⟨1006649, by rfl⟩ : syracuseStep 1342199 = 2013299) B2013299
theorem B3021569 : Blo 1340989 3021569 := bstep (se 2 (by rfl) ⟨1133088, by rfl⟩ : syracuseStep 3021569 = 2266177) B2266177
theorem B11459333 : Blo 1340989 11459333 := bstep (se 4 (by rfl) ⟨1074312, by rfl⟩ : syracuseStep 11459333 = 2148625) B2148625
theorem B1342219 : Blo 1340989 1342219 := bstep (se 1 (by rfl) ⟨1006664, by rfl⟩ : syracuseStep 1342219 = 2013329) B2013329
theorem B6789905 : Blo 1340989 6789905 := bstep (se 2 (by rfl) ⟨2546214, by rfl⟩ : syracuseStep 6789905 = 5092429) B5092429
theorem B5094161 : Blo 1340989 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B1342231 : Blo 1340989 1342231 := bstep (se 1 (by rfl) ⟨1006673, by rfl⟩ : syracuseStep 1342231 = 2013347) B2013347
theorem B2013977 : Blo 1340989 2013977 := bstep (se 2 (by rfl) ⟨755241, by rfl⟩ : syracuseStep 2013977 = 1510483) B1510483
theorem B1342251 : Blo 1340989 1342251 := bstep (se 1 (by rfl) ⟨1006688, by rfl⟩ : syracuseStep 1342251 = 2013377) B2013377
theorem B1342263 : Blo 1340989 1342263 := bstep (se 1 (by rfl) ⟨1006697, by rfl⟩ : syracuseStep 1342263 = 2013395) B2013395
theorem B1342283 : Blo 1340989 1342283 := bstep (se 1 (by rfl) ⟨1006712, by rfl⟩ : syracuseStep 1342283 = 2013425) B2013425
theorem B1342295 : Blo 1340989 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B1342315 : Blo 1340989 1342315 := bstep (se 1 (by rfl) ⟨1006736, by rfl⟩ : syracuseStep 1342315 = 2013473) B2013473
theorem B1342327 : Blo 1340989 1342327 := bstep (se 1 (by rfl) ⟨1006745, by rfl⟩ : syracuseStep 1342327 = 2013491) B2013491
theorem B1342347 : Blo 1340989 1342347 := bstep (se 1 (by rfl) ⟨1006760, by rfl⟩ : syracuseStep 1342347 = 2013521) B2013521
theorem B2014091 : Blo 1340989 2014091 := bstep (se 1 (by rfl) ⟨1510568, by rfl⟩ : syracuseStep 2014091 = 3021137) B3021137
theorem B1342359 : Blo 1340989 1342359 := bstep (se 1 (by rfl) ⟨1006769, by rfl⟩ : syracuseStep 1342359 = 2013539) B2013539
theorem B2014103 : Blo 1340989 2014103 := bstep (se 1 (by rfl) ⟨1510577, by rfl⟩ : syracuseStep 2014103 = 3021155) B3021155
theorem B1342379 : Blo 1340989 1342379 := bstep (se 1 (by rfl) ⟨1006784, by rfl⟩ : syracuseStep 1342379 = 2013569) B2013569
theorem B6790067 : Blo 1340989 6790067 := bstep (se 1 (by rfl) ⟨5092550, by rfl⟩ : syracuseStep 6790067 = 10185101) B10185101
theorem B1342391 : Blo 1340989 1342391 := bstep (se 1 (by rfl) ⟨1006793, by rfl⟩ : syracuseStep 1342391 = 2013587) B2013587
theorem B1342411 : Blo 1340989 1342411 := bstep (se 1 (by rfl) ⟨1006808, by rfl⟩ : syracuseStep 1342411 = 2013617) B2013617
theorem B1342423 : Blo 1340989 1342423 := bstep (se 1 (by rfl) ⟨1006817, by rfl⟩ : syracuseStep 1342423 = 2013635) B2013635
theorem B2014169 : Blo 1340989 2014169 := bstep (se 2 (by rfl) ⟨755313, by rfl⟩ : syracuseStep 2014169 = 1510627) B1510627
theorem B1342443 : Blo 1340989 1342443 := bstep (se 1 (by rfl) ⟨1006832, by rfl⟩ : syracuseStep 1342443 = 2013665) B2013665
theorem B1342455 : Blo 1340989 1342455 := bstep (se 1 (by rfl) ⟨1006841, by rfl⟩ : syracuseStep 1342455 = 2013683) B2013683
theorem B1342475 : Blo 1340989 1342475 := bstep (se 1 (by rfl) ⟨1006856, by rfl⟩ : syracuseStep 1342475 = 2013713) B2013713
theorem B1342487 : Blo 1340989 1342487 := bstep (se 1 (by rfl) ⟨1006865, by rfl⟩ : syracuseStep 1342487 = 2013731) B2013731
theorem B1342507 : Blo 1340989 1342507 := bstep (se 1 (by rfl) ⟨1006880, by rfl⟩ : syracuseStep 1342507 = 2013761) B2013761
theorem B1342519 : Blo 1340989 1342519 := bstep (se 1 (by rfl) ⟨1006889, by rfl⟩ : syracuseStep 1342519 = 2013779) B2013779
theorem B8600651 : Blo 1340989 8600651 := bstep (se 1 (by rfl) ⟨6450488, by rfl⟩ : syracuseStep 8600651 = 12900977) B12900977
theorem B1342539 : Blo 1340989 1342539 := bstep (se 1 (by rfl) ⟨1006904, by rfl⟩ : syracuseStep 1342539 = 2013809) B2013809
theorem B2014283 : Blo 1340989 2014283 := bstep (se 1 (by rfl) ⟨1510712, by rfl⟩ : syracuseStep 2014283 = 3021425) B3021425
theorem B1342551 : Blo 1340989 1342551 := bstep (se 1 (by rfl) ⟨1006913, by rfl⟩ : syracuseStep 1342551 = 2013827) B2013827
theorem B2546777 : Blo 1340989 2546777 := bstep (se 2 (by rfl) ⟨955041, by rfl⟩ : syracuseStep 2546777 = 1910083) B1910083
theorem B2014295 : Blo 1340989 2014295 := bstep (se 1 (by rfl) ⟨1510721, by rfl⟩ : syracuseStep 2014295 = 3021443) B3021443
theorem B1342571 : Blo 1340989 1342571 := bstep (se 1 (by rfl) ⟨1006928, by rfl⟩ : syracuseStep 1342571 = 2013857) B2013857
theorem B1342583 : Blo 1340989 1342583 := bstep (se 1 (by rfl) ⟨1006937, by rfl⟩ : syracuseStep 1342583 = 2013875) B2013875
theorem B1342603 : Blo 1340989 1342603 := bstep (se 1 (by rfl) ⟨1006952, by rfl⟩ : syracuseStep 1342603 = 2013905) B2013905
theorem B4529303 : Blo 1340989 4529303 := bstep (se 1 (by rfl) ⟨3396977, by rfl⟩ : syracuseStep 4529303 = 6793955) B6793955
theorem B1342615 : Blo 1340989 1342615 := bstep (se 1 (by rfl) ⟨1006961, by rfl⟩ : syracuseStep 1342615 = 2013923) B2013923
theorem B2014361 : Blo 1340989 2014361 := bstep (se 2 (by rfl) ⟨755385, by rfl⟩ : syracuseStep 2014361 = 1510771) B1510771
theorem B1342635 : Blo 1340989 1342635 := bstep (se 1 (by rfl) ⟨1006976, by rfl⟩ : syracuseStep 1342635 = 2013953) B2013953
theorem B1342647 : Blo 1340989 1342647 := bstep (se 1 (by rfl) ⟨1006985, by rfl⟩ : syracuseStep 1342647 = 2013971) B2013971
theorem B1342667 : Blo 1340989 1342667 := bstep (se 1 (by rfl) ⟨1007000, by rfl⟩ : syracuseStep 1342667 = 2014001) B2014001
theorem B1342679 : Blo 1340989 1342679 := bstep (se 1 (by rfl) ⟨1007009, by rfl⟩ : syracuseStep 1342679 = 2014019) B2014019
theorem B3874009 : Blo 1340989 3874009 := bstep (se 2 (by rfl) ⟨1452753, by rfl⟩ : syracuseStep 3874009 = 2905507) B2905507
theorem B1342699 : Blo 1340989 1342699 := bstep (se 1 (by rfl) ⟨1007024, by rfl⟩ : syracuseStep 1342699 = 2014049) B2014049
theorem B1342711 : Blo 1340989 1342711 := bstep (se 1 (by rfl) ⟨1007033, by rfl⟩ : syracuseStep 1342711 = 2014067) B2014067
theorem B1342731 : Blo 1340989 1342731 := bstep (se 1 (by rfl) ⟨1007048, by rfl⟩ : syracuseStep 1342731 = 2014097) B2014097
theorem B2014475 : Blo 1340989 2014475 := bstep (se 1 (by rfl) ⟨1510856, by rfl⟩ : syracuseStep 2014475 = 3021713) B3021713
theorem B1342743 : Blo 1340989 1342743 := bstep (se 1 (by rfl) ⟨1007057, by rfl⟩ : syracuseStep 1342743 = 2014115) B2014115
theorem B1342763 : Blo 1340989 1342763 := bstep (se 1 (by rfl) ⟨1007072, by rfl⟩ : syracuseStep 1342763 = 2014145) B2014145
theorem B1342775 : Blo 1340989 1342775 := bstep (se 1 (by rfl) ⟨1007081, by rfl⟩ : syracuseStep 1342775 = 2014163) B2014163
theorem B1342795 : Blo 1340989 1342795 := bstep (se 1 (by rfl) ⟨1007096, by rfl⟩ : syracuseStep 1342795 = 2014193) B2014193
theorem B1342807 : Blo 1340989 1342807 := bstep (se 1 (by rfl) ⟨1007105, by rfl⟩ : syracuseStep 1342807 = 2014211) B2014211
theorem B4300121 : Blo 1340989 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B1342827 : Blo 1340989 1342827 := bstep (se 1 (by rfl) ⟨1007120, by rfl⟩ : syracuseStep 1342827 = 2014241) B2014241
theorem B1342839 : Blo 1340989 1342839 := bstep (se 1 (by rfl) ⟨1007129, by rfl⟩ : syracuseStep 1342839 = 2014259) B2014259
theorem B1342859 : Blo 1340989 1342859 := bstep (se 1 (by rfl) ⟨1007144, by rfl⟩ : syracuseStep 1342859 = 2014289) B2014289
theorem B1342871 : Blo 1340989 1342871 := bstep (se 1 (by rfl) ⟨1007153, by rfl⟩ : syracuseStep 1342871 = 2014307) B2014307
theorem B1342891 : Blo 1340989 1342891 := bstep (se 1 (by rfl) ⟨1007168, by rfl⟩ : syracuseStep 1342891 = 2014337) B2014337
theorem B1342903 : Blo 1340989 1342903 := bstep (se 1 (by rfl) ⟨1007177, by rfl⟩ : syracuseStep 1342903 = 2014355) B2014355
theorem B5094859 : Blo 1340989 5094859 := bstep (se 1 (by rfl) ⟨3821144, by rfl⟩ : syracuseStep 5094859 = 7642289) B7642289
theorem B1342923 : Blo 1340989 1342923 := bstep (se 1 (by rfl) ⟨1007192, by rfl⟩ : syracuseStep 1342923 = 2014385) B2014385
theorem B1342935 : Blo 1340989 1342935 := bstep (se 1 (by rfl) ⟨1007201, by rfl⟩ : syracuseStep 1342935 = 2014403) B2014403
theorem B1342955 : Blo 1340989 1342955 := bstep (se 1 (by rfl) ⟨1007216, by rfl⟩ : syracuseStep 1342955 = 2014433) B2014433
theorem B1342967 : Blo 1340989 1342967 := bstep (se 1 (by rfl) ⟨1007225, by rfl⟩ : syracuseStep 1342967 = 2014451) B2014451
theorem B1342987 : Blo 1340989 1342987 := bstep (se 1 (by rfl) ⟨1007240, by rfl⟩ : syracuseStep 1342987 = 2014481) B2014481
theorem B1433143 : Blo 1340989 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B2719307 : Blo 1340989 2719307 := bstep (se 1 (by rfl) ⟨2039480, by rfl⟩ : syracuseStep 2719307 = 4078961) B4078961
theorem B16318027 : Blo 1340989 16318027 := bstep (se 1 (by rfl) ⟨12238520, by rfl⟩ : syracuseStep 16318027 = 24477041) B24477041
theorem B1359511 : Blo 1340989 1359511 := bstep (se 1 (by rfl) ⟨1019633, by rfl⟩ : syracuseStep 1359511 = 2039267) B2039267
theorem B4529843 : Blo 1340989 4529843 := bstep (se 1 (by rfl) ⟨3397382, by rfl⟩ : syracuseStep 4529843 = 6794765) B6794765
theorem B3399347 : Blo 1340989 3399347 := bstep (se 1 (by rfl) ⟨2549510, by rfl⟩ : syracuseStep 3399347 = 5099021) B5099021
theorem B5095133 : Blo 1340989 5095133 := bstep (se 3 (by rfl) ⟨955337, by rfl⟩ : syracuseStep 5095133 = 1910675) B1910675
theorem B2547521 : Blo 1340989 2547521 := bstep (se 2 (by rfl) ⟨955320, by rfl⟩ : syracuseStep 2547521 = 1910641) B1910641
theorem B9183077 : Blo 1340989 9183077 := bstep (se 4 (by rfl) ⟨860913, by rfl⟩ : syracuseStep 9183077 = 1721827) B1721827
theorem B2867123 : Blo 1340989 2867123 := bstep (se 1 (by rfl) ⟨2150342, by rfl⟩ : syracuseStep 2867123 = 4300685) B4300685
theorem B4530113 : Blo 1340989 4530113 := bstep (se 2 (by rfl) ⟨1698792, by rfl⟩ : syracuseStep 4530113 = 3397585) B3397585
theorem B5513177 : Blo 1340989 5513177 := bstep (se 2 (by rfl) ⟨2067441, by rfl⟩ : syracuseStep 5513177 = 4134883) B4134883
theorem B6889483 : Blo 1340989 6889483 := bstep (se 1 (by rfl) ⟨5167112, by rfl⟩ : syracuseStep 6889483 = 10334225) B10334225
theorem B7643429 : Blo 1340989 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B4530491 : Blo 1340989 4530491 := bstep (se 1 (by rfl) ⟨3397868, by rfl⟩ : syracuseStep 4530491 = 6795737) B6795737
theorem B12894673 : Blo 1340989 12894673 := bstep (se 2 (by rfl) ⟨4835502, by rfl⟩ : syracuseStep 12894673 = 9671005) B9671005
theorem B11616797 : Blo 1340989 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B6120137 : Blo 1340989 6120137 := bstep (se 2 (by rfl) ⟨2295051, by rfl⟩ : syracuseStep 6120137 = 4590103) B4590103
theorem B4080395 : Blo 1340989 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B8274703 : Blo 1340989 8274703 := bstep (se 1 (by rfl) ⟨6206027, by rfl⟩ : syracuseStep 8274703 = 12412055) B12412055
theorem B5104417 : Blo 1340989 5104417 := bstep (se 2 (by rfl) ⟨1914156, by rfl⟩ : syracuseStep 5104417 = 3828313) B3828313
theorem B4530977 : Blo 1340989 4530977 := bstep (se 2 (by rfl) ⟨1699116, by rfl⟩ : syracuseStep 4530977 = 3398233) B3398233
theorem B7250725 : Blo 1340989 7250725 := bstep (se 4 (by rfl) ⟨679755, by rfl⟩ : syracuseStep 7250725 = 1359511) B1359511
theorem B2548523 : Blo 1340989 2548523 := bstep (se 1 (by rfl) ⟨1911392, by rfl⟩ : syracuseStep 2548523 = 3822785) B3822785
theorem B24486745 : Blo 1340989 24486745 := bstep (se 2 (by rfl) ⟨9182529, by rfl⟩ : syracuseStep 24486745 = 18365059) B18365059
theorem B15287129 : Blo 1340989 15287129 := bstep (se 2 (by rfl) ⟨5732673, by rfl⟩ : syracuseStep 15287129 = 11465347) B11465347
theorem B11469721 : Blo 1340989 11469721 := bstep (se 2 (by rfl) ⟨4301145, by rfl⟩ : syracuseStep 11469721 = 8602291) B8602291
theorem B1909775 : Blo 1340989 1909775 := bstep (se 1 (by rfl) ⟨1432331, by rfl⟩ : syracuseStep 1909775 = 2864663) B2864663
theorem B7644203 : Blo 1340989 7644203 := bstep (se 1 (by rfl) ⟨5733152, by rfl⟩ : syracuseStep 7644203 = 11466305) B11466305
theorem B5735681 : Blo 1340989 5735681 := bstep (se 2 (by rfl) ⟨2150880, by rfl⟩ : syracuseStep 5735681 = 4301761) B4301761
theorem B4531571 : Blo 1340989 4531571 := bstep (se 1 (by rfl) ⟨3398678, by rfl⟩ : syracuseStep 4531571 = 6797357) B6797357
theorem B14714257 : Blo 1340989 14714257 := bstep (se 2 (by rfl) ⟨5517846, by rfl⟩ : syracuseStep 14714257 = 11035693) B11035693
theorem B13780523 : Blo 1340989 13780523 := bstep (se 1 (by rfl) ⟨10335392, by rfl⟩ : syracuseStep 13780523 = 20670785) B20670785
theorem B3819095 : Blo 1340989 3819095 := bstep (se 1 (by rfl) ⟨2864321, by rfl⟩ : syracuseStep 3819095 = 5728643) B5728643
theorem B1509007 : Blo 1340989 1509007 := bstep (se 1 (by rfl) ⟨1131755, by rfl⟩ : syracuseStep 1509007 = 2263511) B2263511
theorem B1697527 : Blo 1340989 1697527 := bstep (se 1 (by rfl) ⟨1273145, by rfl⟩ : syracuseStep 1697527 = 2546291) B2546291
theorem B17204993 : Blo 1340989 17204993 := bstep (se 2 (by rfl) ⟨6451872, by rfl⟩ : syracuseStep 17204993 = 12903745) B12903745
theorem B5097275 : Blo 1340989 5097275 := bstep (se 1 (by rfl) ⟨3822956, by rfl⟩ : syracuseStep 5097275 = 7645913) B7645913
theorem B2148215 : Blo 1340989 2148215 := bstep (se 1 (by rfl) ⟨1611161, by rfl⟩ : syracuseStep 2148215 = 3222323) B3222323
theorem B5162899 : Blo 1340989 5162899 := bstep (se 1 (by rfl) ⟨3872174, by rfl⟩ : syracuseStep 5162899 = 7744349) B7744349
theorem B6793145 : Blo 1340989 6793145 := bstep (se 2 (by rfl) ⟨2547429, by rfl⟩ : syracuseStep 6793145 = 5094859) B5094859
theorem B2418617 : Blo 1340989 2418617 := bstep (se 2 (by rfl) ⟨906981, by rfl⟩ : syracuseStep 2418617 = 1813963) B1813963
theorem B14518277 : Blo 1340989 14518277 := bstep (se 4 (by rfl) ⟨1361088, by rfl⟩ : syracuseStep 14518277 = 2722177) B2722177
theorem B2263099 : Blo 1340989 2263099 := bstep (se 1 (by rfl) ⟨1697324, by rfl⟩ : syracuseStep 2263099 = 3394649) B3394649
theorem B1697851 : Blo 1340989 1697851 := bstep (se 1 (by rfl) ⟨1273388, by rfl⟩ : syracuseStep 1697851 = 2546777) B2546777
theorem B4835389 : Blo 1340989 4835389 := bstep (se 3 (by rfl) ⟨906635, by rfl⟩ : syracuseStep 4835389 = 1813271) B1813271
theorem B4835447 : Blo 1340989 4835447 := bstep (se 1 (by rfl) ⟨3626585, by rfl⟩ : syracuseStep 4835447 = 7253171) B7253171
theorem B1509511 : Blo 1340989 1509511 := bstep (se 1 (by rfl) ⟨1132133, by rfl⟩ : syracuseStep 1509511 = 2264267) B2264267
theorem B8595629 : Blo 1340989 8595629 := bstep (se 3 (by rfl) ⟨1611680, by rfl⟩ : syracuseStep 8595629 = 3223361) B3223361
theorem B2263241 : Blo 1340989 2263241 := bstep (se 2 (by rfl) ⟨848715, by rfl⟩ : syracuseStep 2263241 = 1697431) B1697431
theorem B5097761 : Blo 1340989 5097761 := bstep (se 2 (by rfl) ⟨1911660, by rfl⟩ : syracuseStep 5097761 = 3823321) B3823321
theorem B1509691 : Blo 1340989 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B1812871 : Blo 1340989 1812871 := bstep (se 1 (by rfl) ⟨1359653, by rfl⟩ : syracuseStep 1812871 = 2719307) B2719307
theorem B7645661 : Blo 1340989 7645661 := bstep (se 3 (by rfl) ⟨1433561, by rfl⟩ : syracuseStep 7645661 = 2867123) B2867123
theorem B3017231 : Blo 1340989 3017231 := bstep (se 1 (by rfl) ⟨2262923, by rfl⟩ : syracuseStep 3017231 = 4525847) B4525847
theorem B3017249 : Blo 1340989 3017249 := bstep (se 2 (by rfl) ⟨1131468, by rfl⟩ : syracuseStep 3017249 = 2262937) B2262937
theorem B1698347 : Blo 1340989 1698347 := bstep (se 1 (by rfl) ⟨1273760, by rfl⟩ : syracuseStep 1698347 = 2547521) B2547521
theorem B6122051 : Blo 1340989 6122051 := bstep (se 1 (by rfl) ⟨4591538, by rfl⟩ : syracuseStep 6122051 = 9183077) B9183077
theorem B1510159 : Blo 1340989 1510159 := bstep (se 1 (by rfl) ⟨1132619, by rfl⟩ : syracuseStep 1510159 = 2265239) B2265239
theorem B11471705 : Blo 1340989 11471705 := bstep (se 2 (by rfl) ⟨4301889, by rfl⟩ : syracuseStep 11471705 = 8603779) B8603779
theorem B10185587 : Blo 1340989 10185587 := bstep (se 1 (by rfl) ⟨7639190, by rfl⟩ : syracuseStep 10185587 = 15278381) B15278381
theorem B3017591 : Blo 1340989 3017591 := bstep (se 1 (by rfl) ⟨2263193, by rfl⟩ : syracuseStep 3017591 = 4526387) B4526387
theorem B2263943 : Blo 1340989 2263943 := bstep (se 1 (by rfl) ⟨1697957, by rfl⟩ : syracuseStep 2263943 = 3395915) B3395915
theorem B12888983 : Blo 1340989 12888983 := bstep (se 1 (by rfl) ⟨9666737, by rfl⟩ : syracuseStep 12888983 = 19333475) B19333475
theorem B3394457 : Blo 1340989 3394457 := bstep (se 2 (by rfl) ⟨1272921, by rfl⟩ : syracuseStep 3394457 = 2545843) B2545843
theorem B1813433 : Blo 1340989 1813433 := bstep (se 2 (by rfl) ⟨680037, by rfl⟩ : syracuseStep 1813433 = 1360075) B1360075
theorem B1698823 : Blo 1340989 1698823 := bstep (se 1 (by rfl) ⟨1274117, by rfl⟩ : syracuseStep 1698823 = 2548235) B2548235
theorem B3017771 : Blo 1340989 3017771 := bstep (se 1 (by rfl) ⟨2263328, by rfl⟩ : syracuseStep 3017771 = 4526657) B4526657
theorem B1813547 : Blo 1340989 1813547 := bstep (se 1 (by rfl) ⟨1360160, by rfl⟩ : syracuseStep 1813547 = 2720321) B2720321
theorem B3394619 : Blo 1340989 3394619 := bstep (se 1 (by rfl) ⟨2545964, by rfl⟩ : syracuseStep 3394619 = 5091929) B5091929
theorem B3820679 : Blo 1340989 3820679 := bstep (se 1 (by rfl) ⟨2865509, by rfl⟩ : syracuseStep 3820679 = 5731019) B5731019
theorem B3058835 : Blo 1340989 3058835 := bstep (se 1 (by rfl) ⟨2294126, by rfl⟩ : syracuseStep 3058835 = 4588253) B4588253
theorem B6794441 : Blo 1340989 6794441 := bstep (se 2 (by rfl) ⟨2547915, by rfl⟩ : syracuseStep 6794441 = 5095831) B5095831
theorem B10333421 : Blo 1340989 10333421 := bstep (se 3 (by rfl) ⟨1937516, by rfl⟩ : syracuseStep 10333421 = 3875033) B3875033
theorem B5098733 : Blo 1340989 5098733 := bstep (se 3 (by rfl) ⟨956012, by rfl⟩ : syracuseStep 5098733 = 1912025) B1912025
theorem B1510663 : Blo 1340989 1510663 := bstep (se 1 (by rfl) ⟨1132997, by rfl⟩ : syracuseStep 1510663 = 2265995) B2265995
theorem B3394831 : Blo 1340989 3394831 := bstep (se 1 (by rfl) ⟨2546123, by rfl⟩ : syracuseStep 3394831 = 5092247) B5092247
theorem B4590881 : Blo 1340989 4590881 := bstep (se 2 (by rfl) ⟨1721580, by rfl⟩ : syracuseStep 4590881 = 3443161) B3443161
theorem B3018131 : Blo 1340989 3018131 := bstep (se 1 (by rfl) ⟨2263598, by rfl⟩ : syracuseStep 3018131 = 4527197) B4527197
theorem B1510843 : Blo 1340989 1510843 := bstep (se 1 (by rfl) ⟨1133132, by rfl⟩ : syracuseStep 1510843 = 2266265) B2266265
theorem B3018185 : Blo 1340989 3018185 := bstep (se 2 (by rfl) ⟨1131819, by rfl⟩ : syracuseStep 3018185 = 2263639) B2263639
theorem B1699319 : Blo 1340989 1699319 := bstep (se 1 (by rfl) ⟨1274489, by rfl⟩ : syracuseStep 1699319 = 2548979) B2548979
theorem B1814023 : Blo 1340989 1814023 := bstep (se 1 (by rfl) ⟨1360517, by rfl⟩ : syracuseStep 1814023 = 2721035) B2721035
theorem B2264591 : Blo 1340989 2264591 := bstep (se 1 (by rfl) ⟨1698443, by rfl⟩ : syracuseStep 2264591 = 3396887) B3396887
theorem B3395105 : Blo 1340989 3395105 := bstep (se 2 (by rfl) ⟨1273164, by rfl⟩ : syracuseStep 3395105 = 2546329) B2546329
theorem B5099051 : Blo 1340989 5099051 := bstep (se 1 (by rfl) ⟨3824288, by rfl⟩ : syracuseStep 5099051 = 7648577) B7648577
theorem B15502913 : Blo 1340989 15502913 := bstep (se 2 (by rfl) ⟨5813592, by rfl⟩ : syracuseStep 15502913 = 11627185) B11627185
theorem B1699471 : Blo 1340989 1699471 := bstep (se 1 (by rfl) ⟨1274603, by rfl⟩ : syracuseStep 1699471 = 2549207) B2549207
theorem B10333925 : Blo 1340989 10333925 := bstep (se 4 (by rfl) ⟨968805, by rfl⟩ : syracuseStep 10333925 = 1937611) B1937611
theorem B3821327 : Blo 1340989 3821327 := bstep (se 1 (by rfl) ⟨2865995, by rfl⟩ : syracuseStep 3821327 = 5731991) B5731991
theorem B1814287 : Blo 1340989 1814287 := bstep (se 1 (by rfl) ⟨1360715, by rfl⟩ : syracuseStep 1814287 = 2721431) B2721431
theorem B1699643 : Blo 1340989 1699643 := bstep (se 1 (by rfl) ⟨1274732, by rfl⟩ : syracuseStep 1699643 = 2549465) B2549465
theorem B4526009 : Blo 1340989 4526009 := bstep (se 2 (by rfl) ⟨1697253, by rfl⟩ : syracuseStep 4526009 = 3394507) B3394507
theorem B4837405 : Blo 1340989 4837405 := bstep (se 3 (by rfl) ⟨907013, by rfl⟩ : syracuseStep 4837405 = 1814027) B1814027
theorem B2265131 : Blo 1340989 2265131 := bstep (se 1 (by rfl) ⟨1698848, by rfl⟩ : syracuseStep 2265131 = 3397697) B3397697
theorem B11456599 : Blo 1340989 11456599 := bstep (se 1 (by rfl) ⟨8592449, by rfl⟩ : syracuseStep 11456599 = 17184899) B17184899
theorem B3018887 : Blo 1340989 3018887 := bstep (se 1 (by rfl) ⟨2264165, by rfl⟩ : syracuseStep 3018887 = 4528331) B4528331
theorem B5165345 : Blo 1340989 5165345 := bstep (se 2 (by rfl) ⟨1937004, by rfl⟩ : syracuseStep 5165345 = 3874009) B3874009
theorem B3019067 : Blo 1340989 3019067 := bstep (se 1 (by rfl) ⟨2264300, by rfl⟩ : syracuseStep 3019067 = 4528601) B4528601
theorem B2011511 : Blo 1340989 2011511 := bstep (se 1 (by rfl) ⟨1508633, by rfl⟩ : syracuseStep 2011511 = 3017267) B3017267
theorem B2011535 : Blo 1340989 2011535 := bstep (se 1 (by rfl) ⟨1508651, by rfl⟩ : syracuseStep 2011535 = 3017303) B3017303
theorem B5091731 : Blo 1340989 5091731 := bstep (se 1 (by rfl) ⟨3818798, by rfl⟩ : syracuseStep 5091731 = 7637597) B7637597
theorem B2011577 : Blo 1340989 2011577 := bstep (se 2 (by rfl) ⟨754341, by rfl⟩ : syracuseStep 2011577 = 1508683) B1508683
theorem B3019193 : Blo 1340989 3019193 := bstep (se 2 (by rfl) ⟨1132197, by rfl⟩ : syracuseStep 3019193 = 2264395) B2264395
theorem B2265529 : Blo 1340989 2265529 := bstep (se 2 (by rfl) ⟨849573, by rfl⟩ : syracuseStep 2265529 = 1699147) B1699147
theorem B7639555 : Blo 1340989 7639555 := bstep (se 1 (by rfl) ⟨5729666, by rfl⟩ : syracuseStep 7639555 = 11459333) B11459333
theorem B2011655 : Blo 1340989 2011655 := bstep (se 1 (by rfl) ⟨1508741, by rfl⟩ : syracuseStep 2011655 = 3017483) B3017483
theorem B4526603 : Blo 1340989 4526603 := bstep (se 1 (by rfl) ⟨3394952, by rfl⟩ : syracuseStep 4526603 = 6789905) B6789905
theorem B3396107 : Blo 1340989 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B2011691 : Blo 1340989 2011691 := bstep (se 1 (by rfl) ⟨1508768, by rfl⟩ : syracuseStep 2011691 = 3017537) B3017537
theorem B23245355 : Blo 1340989 23245355 := bstep (se 1 (by rfl) ⟨17434016, by rfl⟩ : syracuseStep 23245355 = 34868033) B34868033
theorem B15282755 : Blo 1340989 15282755 := bstep (se 1 (by rfl) ⟨11462066, by rfl⟩ : syracuseStep 15282755 = 22924133) B22924133
theorem B2011721 : Blo 1340989 2011721 := bstep (se 2 (by rfl) ⟨754395, by rfl⟩ : syracuseStep 2011721 = 1508791) B1508791
theorem B4526711 : Blo 1340989 4526711 := bstep (se 1 (by rfl) ⟨3395033, by rfl⟩ : syracuseStep 4526711 = 6790067) B6790067
theorem B12907127 : Blo 1340989 12907127 := bstep (se 1 (by rfl) ⟨9680345, by rfl⟩ : syracuseStep 12907127 = 19360691) B19360691
theorem B2011835 : Blo 1340989 2011835 := bstep (se 1 (by rfl) ⟨1508876, by rfl⟩ : syracuseStep 2011835 = 3017753) B3017753
theorem B6451913 : Blo 1340989 6451913 := bstep (se 2 (by rfl) ⟨2419467, by rfl⟩ : syracuseStep 6451913 = 4838935) B4838935
theorem B2011895 : Blo 1340989 2011895 := bstep (se 1 (by rfl) ⟨1508921, by rfl⟩ : syracuseStep 2011895 = 3017843) B3017843
theorem B2011919 : Blo 1340989 2011919 := bstep (se 1 (by rfl) ⟨1508939, by rfl⟩ : syracuseStep 2011919 = 3017879) B3017879
theorem B3019535 : Blo 1340989 3019535 := bstep (se 1 (by rfl) ⟨2264651, by rfl⟩ : syracuseStep 3019535 = 4529303) B4529303
theorem B9188111 : Blo 1340989 9188111 := bstep (se 1 (by rfl) ⟨6891083, by rfl⟩ : syracuseStep 9188111 = 13782167) B13782167
theorem B3019553 : Blo 1340989 3019553 := bstep (se 2 (by rfl) ⟨1132332, by rfl⟩ : syracuseStep 3019553 = 2264665) B2264665
theorem B9433907 : Blo 1340989 9433907 := bstep (se 1 (by rfl) ⟨7075430, by rfl⟩ : syracuseStep 9433907 = 14150861) B14150861
theorem B2011961 : Blo 1340989 2011961 := bstep (se 2 (by rfl) ⟨754485, by rfl⟩ : syracuseStep 2011961 = 1508971) B1508971
theorem B6452027 : Blo 1340989 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B2012039 : Blo 1340989 2012039 := bstep (se 1 (by rfl) ⟨1509029, by rfl⟩ : syracuseStep 2012039 = 3018059) B3018059
theorem B2012075 : Blo 1340989 2012075 := bstep (se 1 (by rfl) ⟨1509056, by rfl⟩ : syracuseStep 2012075 = 3018113) B3018113
theorem B2012105 : Blo 1340989 2012105 := bstep (se 2 (by rfl) ⟨754539, by rfl⟩ : syracuseStep 2012105 = 1509079) B1509079
theorem B2012219 : Blo 1340989 2012219 := bstep (se 1 (by rfl) ⟨1509164, by rfl⟩ : syracuseStep 2012219 = 3018329) B3018329
theorem B4297789 : Blo 1340989 4297789 := bstep (se 3 (by rfl) ⟨805835, by rfl⟩ : syracuseStep 4297789 = 1611671) B1611671
theorem B2012279 : Blo 1340989 2012279 := bstep (se 1 (by rfl) ⟨1509209, by rfl⟩ : syracuseStep 2012279 = 3018419) B3018419
theorem B3019895 : Blo 1340989 3019895 := bstep (se 1 (by rfl) ⟨2264921, by rfl⟩ : syracuseStep 3019895 = 4529843) B4529843
theorem B6124663 : Blo 1340989 6124663 := bstep (se 1 (by rfl) ⟨4593497, by rfl⟩ : syracuseStep 6124663 = 9186995) B9186995
theorem B2266231 : Blo 1340989 2266231 := bstep (se 1 (by rfl) ⟨1699673, by rfl⟩ : syracuseStep 2266231 = 3399347) B3399347
theorem B2012303 : Blo 1340989 2012303 := bstep (se 1 (by rfl) ⟨1509227, by rfl⟩ : syracuseStep 2012303 = 3018455) B3018455
theorem B3396755 : Blo 1340989 3396755 := bstep (se 1 (by rfl) ⟨2547566, by rfl⟩ : syracuseStep 3396755 = 5095133) B5095133
theorem B2012345 : Blo 1340989 2012345 := bstep (se 2 (by rfl) ⟨754629, by rfl⟩ : syracuseStep 2012345 = 1509259) B1509259
theorem B4527305 : Blo 1340989 4527305 := bstep (se 2 (by rfl) ⟨1697739, by rfl⟩ : syracuseStep 4527305 = 3395479) B3395479
theorem B2012423 : Blo 1340989 2012423 := bstep (se 1 (by rfl) ⟨1509317, by rfl⟩ : syracuseStep 2012423 = 3018635) B3018635
theorem B9180449 : Blo 1340989 9180449 := bstep (se 2 (by rfl) ⟨3442668, by rfl⟩ : syracuseStep 9180449 = 6885337) B6885337
theorem B2012459 : Blo 1340989 2012459 := bstep (se 1 (by rfl) ⟨1509344, by rfl⟩ : syracuseStep 2012459 = 3018689) B3018689
theorem B3020075 : Blo 1340989 3020075 := bstep (se 1 (by rfl) ⟨2265056, by rfl⟩ : syracuseStep 3020075 = 4530113) B4530113
theorem B3675451 : Blo 1340989 3675451 := bstep (se 1 (by rfl) ⟨2756588, by rfl⟩ : syracuseStep 3675451 = 5513177) B5513177
theorem B2520379 : Blo 1340989 2520379 := bstep (se 1 (by rfl) ⟨1890284, by rfl⟩ : syracuseStep 2520379 = 3780569) B3780569
theorem B2012489 : Blo 1340989 2012489 := bstep (se 2 (by rfl) ⟨754683, by rfl⟩ : syracuseStep 2012489 = 1509367) B1509367
theorem B3822967 : Blo 1340989 3822967 := bstep (se 1 (by rfl) ⟨2867225, by rfl⟩ : syracuseStep 3822967 = 5734451) B5734451
theorem B3397049 : Blo 1340989 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B2012603 : Blo 1340989 2012603 := bstep (se 1 (by rfl) ⟨1509452, by rfl⟩ : syracuseStep 2012603 = 3018905) B3018905
theorem B2012663 : Blo 1340989 2012663 := bstep (se 1 (by rfl) ⟨1509497, by rfl⟩ : syracuseStep 2012663 = 3018995) B3018995
theorem B2012687 : Blo 1340989 2012687 := bstep (se 1 (by rfl) ⟨1509515, by rfl⟩ : syracuseStep 2012687 = 3019031) B3019031
theorem B2012729 : Blo 1340989 2012729 := bstep (se 2 (by rfl) ⟨754773, by rfl⟩ : syracuseStep 2012729 = 1509547) B1509547
theorem B1341063 : Blo 1340989 1341063 := bstep (se 1 (by rfl) ⟨1005797, by rfl⟩ : syracuseStep 1341063 = 2011595) B2011595
theorem B2012807 : Blo 1340989 2012807 := bstep (se 1 (by rfl) ⟨1509605, by rfl⟩ : syracuseStep 2012807 = 3019211) B3019211
theorem B1341071 : Blo 1340989 1341071 := bstep (se 1 (by rfl) ⟨1005803, by rfl⟩ : syracuseStep 1341071 = 2011607) B2011607
theorem B3020435 : Blo 1340989 3020435 := bstep (se 1 (by rfl) ⟨2265326, by rfl⟩ : syracuseStep 3020435 = 4530653) B4530653
theorem B2012843 : Blo 1340989 2012843 := bstep (se 1 (by rfl) ⟨1509632, by rfl⟩ : syracuseStep 2012843 = 3019265) B3019265
theorem B12900019 : Blo 1340989 12900019 := bstep (se 1 (by rfl) ⟨9675014, by rfl⟩ : syracuseStep 12900019 = 19350029) B19350029
theorem B1341115 : Blo 1340989 1341115 := bstep (se 1 (by rfl) ⟨1005836, by rfl⟩ : syracuseStep 1341115 = 2011673) B2011673
theorem B2012873 : Blo 1340989 2012873 := bstep (se 2 (by rfl) ⟨754827, by rfl⟩ : syracuseStep 2012873 = 1509655) B1509655
theorem B3020489 : Blo 1340989 3020489 := bstep (se 2 (by rfl) ⟨1132683, by rfl⟩ : syracuseStep 3020489 = 2265367) B2265367
theorem B1341191 : Blo 1340989 1341191 := bstep (se 1 (by rfl) ⟨1005893, by rfl⟩ : syracuseStep 1341191 = 2011787) B2011787
theorem B1341199 : Blo 1340989 1341199 := bstep (se 1 (by rfl) ⟨1005899, by rfl⟩ : syracuseStep 1341199 = 2011799) B2011799
theorem B1341243 : Blo 1340989 1341243 := bstep (se 1 (by rfl) ⟨1005932, by rfl⟩ : syracuseStep 1341243 = 2011865) B2011865
theorem B2012987 : Blo 1340989 2012987 := bstep (se 1 (by rfl) ⟨1509740, by rfl⟩ : syracuseStep 2012987 = 3019481) B3019481
theorem B29407093 : Blo 1340989 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B2013047 : Blo 1340989 2013047 := bstep (se 1 (by rfl) ⟨1509785, by rfl⟩ : syracuseStep 2013047 = 3019571) B3019571
theorem B1341319 : Blo 1340989 1341319 := bstep (se 1 (by rfl) ⟨1005989, by rfl⟩ : syracuseStep 1341319 = 2011979) B2011979
theorem B4528007 : Blo 1340989 4528007 := bstep (se 1 (by rfl) ⟨3396005, by rfl⟩ : syracuseStep 4528007 = 6792011) B6792011
theorem B1341327 : Blo 1340989 1341327 := bstep (se 1 (by rfl) ⟨1005995, by rfl⟩ : syracuseStep 1341327 = 2011991) B2011991
theorem B2013071 : Blo 1340989 2013071 := bstep (se 1 (by rfl) ⟨1509803, by rfl⟩ : syracuseStep 2013071 = 3019607) B3019607
theorem B2013113 : Blo 1340989 2013113 := bstep (se 2 (by rfl) ⟨754917, by rfl⟩ : syracuseStep 2013113 = 1509835) B1509835
theorem B4839353 : Blo 1340989 4839353 := bstep (se 2 (by rfl) ⟨1814757, by rfl⟩ : syracuseStep 4839353 = 3629515) B3629515
theorem B1341371 : Blo 1340989 1341371 := bstep (se 1 (by rfl) ⟨1006028, by rfl⟩ : syracuseStep 1341371 = 2012057) B2012057
theorem B3225545 : Blo 1340989 3225545 := bstep (se 2 (by rfl) ⟨1209579, by rfl⟩ : syracuseStep 3225545 = 2419159) B2419159
theorem B1341447 : Blo 1340989 1341447 := bstep (se 1 (by rfl) ⟨1006085, by rfl⟩ : syracuseStep 1341447 = 2012171) B2012171
theorem B2013191 : Blo 1340989 2013191 := bstep (se 1 (by rfl) ⟨1509893, by rfl⟩ : syracuseStep 2013191 = 3019787) B3019787
theorem B5093387 : Blo 1340989 5093387 := bstep (se 1 (by rfl) ⟨3820040, by rfl⟩ : syracuseStep 5093387 = 7640081) B7640081
theorem B1341455 : Blo 1340989 1341455 := bstep (se 1 (by rfl) ⟨1006091, by rfl⟩ : syracuseStep 1341455 = 2012183) B2012183
theorem B11458583 : Blo 1340989 11458583 := bstep (se 1 (by rfl) ⟨8593937, by rfl⟩ : syracuseStep 11458583 = 17187875) B17187875
theorem B2013227 : Blo 1340989 2013227 := bstep (se 1 (by rfl) ⟨1509920, by rfl⟩ : syracuseStep 2013227 = 3019841) B3019841
theorem B1341499 : Blo 1340989 1341499 := bstep (se 1 (by rfl) ⟨1006124, by rfl⟩ : syracuseStep 1341499 = 2012249) B2012249
theorem B2013257 : Blo 1340989 2013257 := bstep (se 2 (by rfl) ⟨754971, by rfl⟩ : syracuseStep 2013257 = 1509943) B1509943
theorem B3397747 : Blo 1340989 3397747 := bstep (se 1 (by rfl) ⟨2548310, by rfl⟩ : syracuseStep 3397747 = 5096621) B5096621
theorem B1341575 : Blo 1340989 1341575 := bstep (se 1 (by rfl) ⟨1006181, by rfl⟩ : syracuseStep 1341575 = 2012363) B2012363
theorem B1341583 : Blo 1340989 1341583 := bstep (se 1 (by rfl) ⟨1006187, by rfl⟩ : syracuseStep 1341583 = 2012375) B2012375
theorem B1341627 : Blo 1340989 1341627 := bstep (se 1 (by rfl) ⟨1006220, by rfl⟩ : syracuseStep 1341627 = 2012441) B2012441
theorem B2013371 : Blo 1340989 2013371 := bstep (se 1 (by rfl) ⟨1510028, by rfl⟩ : syracuseStep 2013371 = 3020057) B3020057
theorem B2013431 : Blo 1340989 2013431 := bstep (se 1 (by rfl) ⟨1510073, by rfl⟩ : syracuseStep 2013431 = 3020147) B3020147
theorem B4528385 : Blo 1340989 4528385 := bstep (se 2 (by rfl) ⟨1698144, by rfl⟩ : syracuseStep 4528385 = 3396289) B3396289
theorem B3397889 : Blo 1340989 3397889 := bstep (se 2 (by rfl) ⟨1274208, by rfl⟩ : syracuseStep 3397889 = 2548417) B2548417
theorem B1341703 : Blo 1340989 1341703 := bstep (se 1 (by rfl) ⟨1006277, by rfl⟩ : syracuseStep 1341703 = 2012555) B2012555
theorem B1341711 : Blo 1340989 1341711 := bstep (se 1 (by rfl) ⟨1006283, by rfl⟩ : syracuseStep 1341711 = 2012567) B2012567
theorem B2013455 : Blo 1340989 2013455 := bstep (se 1 (by rfl) ⟨1510091, by rfl⟩ : syracuseStep 2013455 = 3020183) B3020183
theorem B4839713 : Blo 1340989 4839713 := bstep (se 2 (by rfl) ⟨1814892, by rfl⟩ : syracuseStep 4839713 = 3629785) B3629785
theorem B2013497 : Blo 1340989 2013497 := bstep (se 2 (by rfl) ⟨755061, by rfl⟩ : syracuseStep 2013497 = 1510123) B1510123
theorem B1341755 : Blo 1340989 1341755 := bstep (se 1 (by rfl) ⟨1006316, by rfl⟩ : syracuseStep 1341755 = 2012633) B2012633
theorem B1341831 : Blo 1340989 1341831 := bstep (se 1 (by rfl) ⟨1006373, by rfl⟩ : syracuseStep 1341831 = 2012747) B2012747
theorem B2013575 : Blo 1340989 2013575 := bstep (se 1 (by rfl) ⟨1510181, by rfl⟩ : syracuseStep 2013575 = 3020363) B3020363
theorem B3021191 : Blo 1340989 3021191 := bstep (se 1 (by rfl) ⟨2265893, by rfl⟩ : syracuseStep 3021191 = 4531787) B4531787
theorem B1341839 : Blo 1340989 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B2013611 : Blo 1340989 2013611 := bstep (se 1 (by rfl) ⟨1510208, by rfl⟩ : syracuseStep 2013611 = 3020417) B3020417
theorem B1341883 : Blo 1340989 1341883 := bstep (se 1 (by rfl) ⟨1006412, by rfl⟩ : syracuseStep 1341883 = 2012825) B2012825
theorem B1612219 : Blo 1340989 1612219 := bstep (se 1 (by rfl) ⟨1209164, by rfl⟩ : syracuseStep 1612219 = 2418329) B2418329
theorem B2013641 : Blo 1340989 2013641 := bstep (se 2 (by rfl) ⟨755115, by rfl⟩ : syracuseStep 2013641 = 1510231) B1510231
theorem B1341959 : Blo 1340989 1341959 := bstep (se 1 (by rfl) ⟨1006469, by rfl⟩ : syracuseStep 1341959 = 2012939) B2012939
theorem B1341967 : Blo 1340989 1341967 := bstep (se 1 (by rfl) ⟨1006475, by rfl⟩ : syracuseStep 1341967 = 2012951) B2012951
theorem B1342011 : Blo 1340989 1342011 := bstep (se 1 (by rfl) ⟨1006508, by rfl⟩ : syracuseStep 1342011 = 2013017) B2013017
theorem B2013755 : Blo 1340989 2013755 := bstep (se 1 (by rfl) ⟨1510316, by rfl⟩ : syracuseStep 2013755 = 3020633) B3020633
theorem B3021371 : Blo 1340989 3021371 := bstep (se 1 (by rfl) ⟨2266028, by rfl⟩ : syracuseStep 3021371 = 4532057) B4532057
theorem B11467331 : Blo 1340989 11467331 := bstep (se 1 (by rfl) ⟨8600498, by rfl⟩ : syracuseStep 11467331 = 17200997) B17200997
theorem B2013815 : Blo 1340989 2013815 := bstep (se 1 (by rfl) ⟨1510361, by rfl⟩ : syracuseStep 2013815 = 3020723) B3020723
theorem B3824243 : Blo 1340989 3824243 := bstep (se 1 (by rfl) ⟨2868182, by rfl⟩ : syracuseStep 3824243 = 5736365) B5736365
theorem B1342087 : Blo 1340989 1342087 := bstep (se 1 (by rfl) ⟨1006565, by rfl⟩ : syracuseStep 1342087 = 2013131) B2013131
theorem B1342095 : Blo 1340989 1342095 := bstep (se 1 (by rfl) ⟨1006571, by rfl⟩ : syracuseStep 1342095 = 2013143) B2013143
theorem B2013839 : Blo 1340989 2013839 := bstep (se 1 (by rfl) ⟨1510379, by rfl⟩ : syracuseStep 2013839 = 3020759) B3020759
theorem B2013881 : Blo 1340989 2013881 := bstep (se 2 (by rfl) ⟨755205, by rfl⟩ : syracuseStep 2013881 = 1510411) B1510411
theorem B3021497 : Blo 1340989 3021497 := bstep (se 2 (by rfl) ⟨1133061, by rfl⟩ : syracuseStep 3021497 = 2266123) B2266123
theorem B1342139 : Blo 1340989 1342139 := bstep (se 1 (by rfl) ⟨1006604, by rfl⟩ : syracuseStep 1342139 = 2013209) B2013209
theorem B3398345 : Blo 1340989 3398345 := bstep (se 2 (by rfl) ⟨1274379, by rfl⟩ : syracuseStep 3398345 = 2548759) B2548759
theorem B1342215 : Blo 1340989 1342215 := bstep (se 1 (by rfl) ⟨1006661, by rfl⟩ : syracuseStep 1342215 = 2013323) B2013323
theorem B2013959 : Blo 1340989 2013959 := bstep (se 1 (by rfl) ⟨1510469, by rfl⟩ : syracuseStep 2013959 = 3020939) B3020939
theorem B1342223 : Blo 1340989 1342223 := bstep (se 1 (by rfl) ⟨1006667, by rfl⟩ : syracuseStep 1342223 = 2013335) B2013335
theorem B2013995 : Blo 1340989 2013995 := bstep (se 1 (by rfl) ⟨1510496, by rfl⟩ : syracuseStep 2013995 = 3020993) B3020993
theorem B5806907 : Blo 1340989 5806907 := bstep (se 1 (by rfl) ⟨4355180, by rfl⟩ : syracuseStep 5806907 = 8710361) B8710361
theorem B1342267 : Blo 1340989 1342267 := bstep (se 1 (by rfl) ⟨1006700, by rfl⟩ : syracuseStep 1342267 = 2013401) B2013401
theorem B2014025 : Blo 1340989 2014025 := bstep (se 2 (by rfl) ⟨755259, by rfl⟩ : syracuseStep 2014025 = 1510519) B1510519
theorem B7641971 : Blo 1340989 7641971 := bstep (se 1 (by rfl) ⟨5731478, by rfl⟩ : syracuseStep 7641971 = 11462957) B11462957
theorem B4299635 : Blo 1340989 4299635 := bstep (se 1 (by rfl) ⟨3224726, by rfl⟩ : syracuseStep 4299635 = 6449453) B6449453
theorem B1342343 : Blo 1340989 1342343 := bstep (se 1 (by rfl) ⟨1006757, by rfl⟩ : syracuseStep 1342343 = 2013515) B2013515
theorem B1342351 : Blo 1340989 1342351 := bstep (se 1 (by rfl) ⟨1006763, by rfl⟩ : syracuseStep 1342351 = 2013527) B2013527
theorem B2546579 : Blo 1340989 2546579 := bstep (se 1 (by rfl) ⟨1909934, by rfl⟩ : syracuseStep 2546579 = 3819869) B3819869
theorem B1342395 : Blo 1340989 1342395 := bstep (se 1 (by rfl) ⟨1006796, by rfl⟩ : syracuseStep 1342395 = 2013593) B2013593
theorem B2014139 : Blo 1340989 2014139 := bstep (se 1 (by rfl) ⟨1510604, by rfl⟩ : syracuseStep 2014139 = 3021209) B3021209
theorem B2546633 : Blo 1340989 2546633 := bstep (se 2 (by rfl) ⟨954987, by rfl⟩ : syracuseStep 2546633 = 1909975) B1909975
theorem B2014199 : Blo 1340989 2014199 := bstep (se 1 (by rfl) ⟨1510649, by rfl⟩ : syracuseStep 2014199 = 3021299) B3021299
theorem B1342471 : Blo 1340989 1342471 := bstep (se 1 (by rfl) ⟨1006853, by rfl⟩ : syracuseStep 1342471 = 2013707) B2013707
theorem B1342479 : Blo 1340989 1342479 := bstep (se 1 (by rfl) ⟨1006859, by rfl⟩ : syracuseStep 1342479 = 2013719) B2013719
theorem B2014223 : Blo 1340989 2014223 := bstep (se 1 (by rfl) ⟨1510667, by rfl⟩ : syracuseStep 2014223 = 3021335) B3021335
theorem B2546731 : Blo 1340989 2546731 := bstep (se 1 (by rfl) ⟨1910048, by rfl⟩ : syracuseStep 2546731 = 3820097) B3820097
theorem B4529195 : Blo 1340989 4529195 := bstep (se 1 (by rfl) ⟨3396896, by rfl⟩ : syracuseStep 4529195 = 6793793) B6793793
theorem B3398699 : Blo 1340989 3398699 := bstep (se 1 (by rfl) ⟨2549024, by rfl⟩ : syracuseStep 3398699 = 5098049) B5098049
theorem B2014265 : Blo 1340989 2014265 := bstep (se 2 (by rfl) ⟨755349, by rfl⟩ : syracuseStep 2014265 = 1510699) B1510699
theorem B1342523 : Blo 1340989 1342523 := bstep (se 1 (by rfl) ⟨1006892, by rfl⟩ : syracuseStep 1342523 = 2013785) B2013785
theorem B46480445 : Blo 1340989 46480445 := bstep (se 3 (by rfl) ⟨8715083, by rfl⟩ : syracuseStep 46480445 = 17430167) B17430167
theorem B1342599 : Blo 1340989 1342599 := bstep (se 1 (by rfl) ⟨1006949, by rfl⟩ : syracuseStep 1342599 = 2013899) B2013899
theorem B2014343 : Blo 1340989 2014343 := bstep (se 1 (by rfl) ⟨1510757, by rfl⟩ : syracuseStep 2014343 = 3021515) B3021515
theorem B1342607 : Blo 1340989 1342607 := bstep (se 1 (by rfl) ⟨1006955, by rfl⟩ : syracuseStep 1342607 = 2013911) B2013911
theorem B2014379 : Blo 1340989 2014379 := bstep (se 1 (by rfl) ⟨1510784, by rfl⟩ : syracuseStep 2014379 = 3021569) B3021569
theorem B1342651 : Blo 1340989 1342651 := bstep (se 1 (by rfl) ⟨1006988, by rfl⟩ : syracuseStep 1342651 = 2013977) B2013977
theorem B2014409 : Blo 1340989 2014409 := bstep (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) B1510807
theorem B1342727 : Blo 1340989 1342727 := bstep (se 1 (by rfl) ⟨1007045, by rfl⟩ : syracuseStep 1342727 = 2014091) B2014091
theorem B2546959 : Blo 1340989 2546959 := bstep (se 1 (by rfl) ⟨1910219, by rfl⟩ : syracuseStep 2546959 = 3820439) B3820439
theorem B1342735 : Blo 1340989 1342735 := bstep (se 1 (by rfl) ⟨1007051, by rfl⟩ : syracuseStep 1342735 = 2014103) B2014103
theorem B1342779 : Blo 1340989 1342779 := bstep (se 1 (by rfl) ⟨1007084, by rfl⟩ : syracuseStep 1342779 = 2014169) B2014169
theorem B5733767 : Blo 1340989 5733767 := bstep (se 1 (by rfl) ⟨4300325, by rfl⟩ : syracuseStep 5733767 = 8600651) B8600651
theorem B1342855 : Blo 1340989 1342855 := bstep (se 1 (by rfl) ⟨1007141, by rfl⟩ : syracuseStep 1342855 = 2014283) B2014283
theorem B1342863 : Blo 1340989 1342863 := bstep (se 1 (by rfl) ⟨1007147, by rfl⟩ : syracuseStep 1342863 = 2014295) B2014295
theorem B6790553 : Blo 1340989 6790553 := bstep (se 2 (by rfl) ⟨2546457, by rfl⟩ : syracuseStep 6790553 = 5092915) B5092915
theorem B21757369 : Blo 1340989 21757369 := bstep (se 2 (by rfl) ⟨8159013, by rfl⟩ : syracuseStep 21757369 = 16318027) B16318027
theorem B1342907 : Blo 1340989 1342907 := bstep (se 1 (by rfl) ⟨1007180, by rfl⟩ : syracuseStep 1342907 = 2014361) B2014361
theorem B1342983 : Blo 1340989 1342983 := bstep (se 1 (by rfl) ⟨1007237, by rfl⟩ : syracuseStep 1342983 = 2014475) B2014475
theorem B2866747 : Blo 1340989 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B6447185 : Blo 1340989 6447185 := bstep (se 2 (by rfl) ⟨2417694, by rfl⟩ : syracuseStep 6447185 = 4835389) B4835389
theorem B4530329 : Blo 1340989 4530329 := bstep (se 2 (by rfl) ⟨1698873, by rfl⟩ : syracuseStep 4530329 = 3397747) B3397747
theorem B5095619 : Blo 1340989 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B4301275 : Blo 1340989 4301275 := bstep (se 1 (by rfl) ⟨3225956, by rfl⟩ : syracuseStep 4301275 = 6451913) B6451913
theorem B4301351 : Blo 1340989 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B10191419 : Blo 1340989 10191419 := bstep (se 1 (by rfl) ⟨7643564, by rfl⟩ : syracuseStep 10191419 = 15287129) B15287129
theorem B5096135 : Blo 1340989 5096135 := bstep (se 1 (by rfl) ⟨3822101, by rfl⟩ : syracuseStep 5096135 = 7644203) B7644203
theorem B6120299 : Blo 1340989 6120299 := bstep (se 1 (by rfl) ⟨4590224, by rfl⟩ : syracuseStep 6120299 = 9180449) B9180449
theorem B11469995 : Blo 1340989 11469995 := bstep (se 1 (by rfl) ⟨8602496, by rfl⟩ : syracuseStep 11469995 = 17204993) B17204993
theorem B4531517 : Blo 1340989 4531517 := bstep (se 3 (by rfl) ⟨849659, by rfl⟩ : syracuseStep 4531517 = 1699319) B1699319
theorem B1508827 : Blo 1340989 1508827 := bstep (se 1 (by rfl) ⟨1131620, by rfl⟩ : syracuseStep 1508827 = 2263241) B2263241
theorem B5097107 : Blo 1340989 5097107 := bstep (se 1 (by rfl) ⟨3822830, by rfl⟩ : syracuseStep 5097107 = 7645661) B7645661
theorem B4081367 : Blo 1340989 4081367 := bstep (se 1 (by rfl) ⟨3061025, by rfl⟩ : syracuseStep 4081367 = 6122051) B6122051
theorem B7644887 : Blo 1340989 7644887 := bstep (se 1 (by rfl) ⟨5733665, by rfl⟩ : syracuseStep 7644887 = 11467331) B11467331
theorem B2549495 : Blo 1340989 2549495 := bstep (se 1 (by rfl) ⟨1912121, by rfl⟩ : syracuseStep 2549495 = 3824243) B3824243
theorem B4900601 : Blo 1340989 4900601 := bstep (se 2 (by rfl) ⟨1837725, by rfl⟩ : syracuseStep 4900601 = 3675451) B3675451
theorem B3360505 : Blo 1340989 3360505 := bstep (se 2 (by rfl) ⟨1260189, by rfl⟩ : syracuseStep 3360505 = 2520379) B2520379
theorem B5097289 : Blo 1340989 5097289 := bstep (se 2 (by rfl) ⟨1911483, by rfl⟩ : syracuseStep 5097289 = 3822967) B3822967
theorem B16320365 : Blo 1340989 16320365 := bstep (se 3 (by rfl) ⟨3060068, by rfl⟩ : syracuseStep 16320365 = 6120137) B6120137
theorem B29009825 : Blo 1340989 29009825 := bstep (se 2 (by rfl) ⟨10878684, by rfl⟩ : syracuseStep 29009825 = 21757369) B21757369
theorem B1509295 : Blo 1340989 1509295 := bstep (se 1 (by rfl) ⟨1131971, by rfl⟩ : syracuseStep 1509295 = 2263943) B2263943
theorem B19343285 : Blo 1340989 19343285 := bstep (se 5 (by rfl) ⟨906716, by rfl⟩ : syracuseStep 19343285 = 1813433) B1813433
theorem B2262971 : Blo 1340989 2262971 := bstep (se 1 (by rfl) ⟨1697228, by rfl⟩ : syracuseStep 2262971 = 3394457) B3394457
theorem B1697755 : Blo 1340989 1697755 := bstep (se 1 (by rfl) ⟨1273316, by rfl⟩ : syracuseStep 1697755 = 2546633) B2546633
theorem B2418697 : Blo 1340989 2418697 := bstep (se 2 (by rfl) ⟨907011, by rfl⟩ : syracuseStep 2418697 = 1814023) B1814023
theorem B10881053 : Blo 1340989 10881053 := bstep (se 3 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 10881053 = 4080395) B4080395
theorem B9668645 : Blo 1340989 9668645 := bstep (se 4 (by rfl) ⟨906435, by rfl⟩ : syracuseStep 9668645 = 1812871) B1812871
theorem B2263079 : Blo 1340989 2263079 := bstep (se 1 (by rfl) ⟨1697309, by rfl⟩ : syracuseStep 2263079 = 3394619) B3394619
theorem B4532381 : Blo 1340989 4532381 := bstep (se 3 (by rfl) ⟨849821, by rfl⟩ : syracuseStep 4532381 = 1699643) B1699643
theorem B5728573 : Blo 1340989 5728573 := bstep (se 3 (by rfl) ⟨1074107, by rfl⟩ : syracuseStep 5728573 = 2148215) B2148215
theorem B2263369 : Blo 1340989 2263369 := bstep (se 2 (by rfl) ⟨848763, by rfl⟩ : syracuseStep 2263369 = 1697527) B1697527
theorem B1509727 : Blo 1340989 1509727 := bstep (se 1 (by rfl) ⟨1132295, by rfl⟩ : syracuseStep 1509727 = 2264591) B2264591
theorem B2419049 : Blo 1340989 2419049 := bstep (se 2 (by rfl) ⟨907143, by rfl⟩ : syracuseStep 2419049 = 1814287) B1814287
theorem B2263403 : Blo 1340989 2263403 := bstep (se 1 (by rfl) ⟨1697552, by rfl⟩ : syracuseStep 2263403 = 3395105) B3395105
theorem B6449645 : Blo 1340989 6449645 := bstep (se 3 (by rfl) ⟨1209308, by rfl⟩ : syracuseStep 6449645 = 2418617) B2418617
theorem B6883865 : Blo 1340989 6883865 := bstep (se 2 (by rfl) ⟨2581449, by rfl⟩ : syracuseStep 6883865 = 5162899) B5162899
theorem B3017339 : Blo 1340989 3017339 := bstep (se 1 (by rfl) ⟨2263004, by rfl⟩ : syracuseStep 3017339 = 4526009) B4526009
theorem B9185977 : Blo 1340989 9185977 := bstep (se 2 (by rfl) ⟨3444741, by rfl⟩ : syracuseStep 9185977 = 6889483) B6889483
theorem B1510087 : Blo 1340989 1510087 := bstep (se 1 (by rfl) ⟨1132565, by rfl⟩ : syracuseStep 1510087 = 2265131) B2265131
theorem B6449873 : Blo 1340989 6449873 := bstep (se 2 (by rfl) ⟨2418702, by rfl⟩ : syracuseStep 6449873 = 4837405) B4837405
theorem B3017465 : Blo 1340989 3017465 := bstep (se 2 (by rfl) ⟨1131549, by rfl⟩ : syracuseStep 3017465 = 2263099) B2263099
theorem B2263801 : Blo 1340989 2263801 := bstep (se 2 (by rfl) ⟨848925, by rfl⟩ : syracuseStep 2263801 = 1697851) B1697851
theorem B4836125 : Blo 1340989 4836125 := bstep (se 3 (by rfl) ⟨906773, by rfl⟩ : syracuseStep 4836125 = 1813547) B1813547
theorem B3443563 : Blo 1340989 3443563 := bstep (se 1 (by rfl) ⟨2582672, by rfl⟩ : syracuseStep 3443563 = 5165345) B5165345
theorem B3394487 : Blo 1340989 3394487 := bstep (se 1 (by rfl) ⟨2545865, by rfl⟩ : syracuseStep 3394487 = 5091731) B5091731
theorem B3017735 : Blo 1340989 3017735 := bstep (se 1 (by rfl) ⟨2263301, by rfl⟩ : syracuseStep 3017735 = 4526603) B4526603
theorem B2264071 : Blo 1340989 2264071 := bstep (se 1 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 2264071 = 3396107) B3396107
theorem B3017807 : Blo 1340989 3017807 := bstep (se 1 (by rfl) ⟨2263355, by rfl⟩ : syracuseStep 3017807 = 4526711) B4526711
theorem B2149625 : Blo 1340989 2149625 := bstep (se 2 (by rfl) ⟨806109, by rfl⟩ : syracuseStep 2149625 = 1612219) B1612219
theorem B10186073 : Blo 1340989 10186073 := bstep (se 2 (by rfl) ⟨3819777, by rfl⟩ : syracuseStep 10186073 = 7639555) B7639555
theorem B2264503 : Blo 1340989 2264503 := bstep (se 1 (by rfl) ⟨1698377, by rfl⟩ : syracuseStep 2264503 = 3396755) B3396755
theorem B3018203 : Blo 1340989 3018203 := bstep (se 1 (by rfl) ⟨2263652, by rfl⟩ : syracuseStep 3018203 = 4527305) B4527305
theorem B2264699 : Blo 1340989 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B15290045 : Blo 1340989 15290045 := bstep (se 3 (by rfl) ⟨2866883, by rfl⟩ : syracuseStep 15290045 = 5733767) B5733767
theorem B9187015 : Blo 1340989 9187015 := bstep (se 1 (by rfl) ⟨6890261, by rfl⟩ : syracuseStep 9187015 = 13780523) B13780523
theorem B32648993 : Blo 1340989 32648993 := bstep (se 2 (by rfl) ⟨12243372, by rfl⟩ : syracuseStep 32648993 = 24486745) B24486745
theorem B3018671 : Blo 1340989 3018671 := bstep (se 1 (by rfl) ⟨2264003, by rfl⟩ : syracuseStep 3018671 = 4528007) B4528007
theorem B2150363 : Blo 1340989 2150363 := bstep (se 1 (by rfl) ⟨1612772, by rfl⟩ : syracuseStep 2150363 = 3225545) B3225545
theorem B9678851 : Blo 1340989 9678851 := bstep (se 1 (by rfl) ⟨7259138, by rfl⟩ : syracuseStep 9678851 = 14518277) B14518277
theorem B3395591 : Blo 1340989 3395591 := bstep (se 1 (by rfl) ⟨2546693, by rfl⟩ : syracuseStep 3395591 = 5093387) B5093387
theorem B2265097 : Blo 1340989 2265097 := bstep (se 2 (by rfl) ⟨849411, by rfl⟩ : syracuseStep 2265097 = 1698823) B1698823
theorem B7639055 : Blo 1340989 7639055 := bstep (se 1 (by rfl) ⟨5729291, by rfl⟩ : syracuseStep 7639055 = 11458583) B11458583
theorem B3395641 : Blo 1340989 3395641 := bstep (se 2 (by rfl) ⟨1273365, by rfl⟩ : syracuseStep 3395641 = 2546731) B2546731
theorem B30978125 : Blo 1340989 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B3223631 : Blo 1340989 3223631 := bstep (se 1 (by rfl) ⟨2417723, by rfl⟩ : syracuseStep 3223631 = 4835447) B4835447
theorem B5730385 : Blo 1340989 5730385 := bstep (se 2 (by rfl) ⟨2148894, by rfl⟩ : syracuseStep 5730385 = 4297789) B4297789
theorem B5730419 : Blo 1340989 5730419 := bstep (se 1 (by rfl) ⟨4297814, by rfl⟩ : syracuseStep 5730419 = 8595629) B8595629
theorem B3018923 : Blo 1340989 3018923 := bstep (se 1 (by rfl) ⟨2264192, by rfl⟩ : syracuseStep 3018923 = 4528385) B4528385
theorem B2265259 : Blo 1340989 2265259 := bstep (se 1 (by rfl) ⟨1698944, by rfl⟩ : syracuseStep 2265259 = 3397889) B3397889
theorem B38670533 : Blo 1340989 38670533 := bstep (se 4 (by rfl) ⟨3625362, by rfl⟩ : syracuseStep 38670533 = 7250725) B7250725
theorem B34419005 : Blo 1340989 34419005 := bstep (se 3 (by rfl) ⟨6453563, by rfl⟩ : syracuseStep 34419005 = 12907127) B12907127
theorem B2011487 : Blo 1340989 2011487 := bstep (se 1 (by rfl) ⟨1508615, by rfl⟩ : syracuseStep 2011487 = 3017231) B3017231
theorem B4526441 : Blo 1340989 4526441 := bstep (se 2 (by rfl) ⟨1697415, by rfl⟩ : syracuseStep 4526441 = 3394831) B3394831
theorem B2011499 : Blo 1340989 2011499 := bstep (se 1 (by rfl) ⟨1508624, by rfl⟩ : syracuseStep 2011499 = 3017249) B3017249
theorem B3395945 : Blo 1340989 3395945 := bstep (se 2 (by rfl) ⟨1273479, by rfl⟩ : syracuseStep 3395945 = 2546959) B2546959
theorem B2265563 : Blo 1340989 2265563 := bstep (se 1 (by rfl) ⟨1699172, by rfl⟩ : syracuseStep 2265563 = 3398345) B3398345
theorem B3871271 : Blo 1340989 3871271 := bstep (se 1 (by rfl) ⟨2903453, by rfl⟩ : syracuseStep 3871271 = 5806907) B5806907
theorem B7647803 : Blo 1340989 7647803 := bstep (se 1 (by rfl) ⟨5735852, by rfl⟩ : syracuseStep 7647803 = 11471705) B11471705
theorem B2011727 : Blo 1340989 2011727 := bstep (se 1 (by rfl) ⟨1508795, by rfl⟩ : syracuseStep 2011727 = 3017591) B3017591
theorem B2011847 : Blo 1340989 2011847 := bstep (se 1 (by rfl) ⟨1508885, by rfl⟩ : syracuseStep 2011847 = 3017771) B3017771
theorem B3019463 : Blo 1340989 3019463 := bstep (se 1 (by rfl) ⟨2264597, by rfl⟩ : syracuseStep 3019463 = 4529195) B4529195
theorem B2265799 : Blo 1340989 2265799 := bstep (se 1 (by rfl) ⟨1699349, by rfl⟩ : syracuseStep 2265799 = 3398699) B3398699
theorem B30986963 : Blo 1340989 30986963 := bstep (se 1 (by rfl) ⟨23240222, by rfl⟩ : syracuseStep 30986963 = 46480445) B46480445
theorem B3822329 : Blo 1340989 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B6796061 : Blo 1340989 6796061 := bstep (se 3 (by rfl) ⟨1274261, by rfl⟩ : syracuseStep 6796061 = 2548523) B2548523
theorem B2012009 : Blo 1340989 2012009 := bstep (se 2 (by rfl) ⟨754503, by rfl⟩ : syracuseStep 2012009 = 1509007) B1509007
theorem B3060587 : Blo 1340989 3060587 := bstep (se 1 (by rfl) ⟨2295440, by rfl⟩ : syracuseStep 3060587 = 4590881) B4590881
theorem B2265961 : Blo 1340989 2265961 := bstep (se 2 (by rfl) ⟨849735, by rfl⟩ : syracuseStep 2265961 = 1699471) B1699471
theorem B17200025 : Blo 1340989 17200025 := bstep (se 2 (by rfl) ⟨6450009, by rfl⟩ : syracuseStep 17200025 = 12900019) B12900019
theorem B2012087 : Blo 1340989 2012087 := bstep (se 1 (by rfl) ⟨1509065, by rfl⟩ : syracuseStep 2012087 = 3018131) B3018131
theorem B4527035 : Blo 1340989 4527035 := bstep (se 1 (by rfl) ⟨3395276, by rfl⟩ : syracuseStep 4527035 = 6790553) B6790553
theorem B2012123 : Blo 1340989 2012123 := bstep (se 1 (by rfl) ⟨1509092, by rfl⟩ : syracuseStep 2012123 = 3018185) B3018185
theorem B10335275 : Blo 1340989 10335275 := bstep (se 1 (by rfl) ⟨7751456, by rfl⟩ : syracuseStep 10335275 = 15502913) B15502913
theorem B5092733 : Blo 1340989 5092733 := bstep (se 3 (by rfl) ⟨954887, by rfl⟩ : syracuseStep 5092733 = 1909775) B1909775
theorem B2012591 : Blo 1340989 2012591 := bstep (se 1 (by rfl) ⟨1509443, by rfl⟩ : syracuseStep 2012591 = 3018887) B3018887
theorem B15275465 : Blo 1340989 15275465 := bstep (se 2 (by rfl) ⟨5728299, by rfl⟩ : syracuseStep 15275465 = 11456599) B11456599
theorem B2012681 : Blo 1340989 2012681 := bstep (se 2 (by rfl) ⟨754755, by rfl⟩ : syracuseStep 2012681 = 1509511) B1509511
theorem B2012711 : Blo 1340989 2012711 := bstep (se 1 (by rfl) ⟨1509533, by rfl⟩ : syracuseStep 2012711 = 3019067) B3019067
theorem B3020327 : Blo 1340989 3020327 := bstep (se 1 (by rfl) ⟨2265245, by rfl⟩ : syracuseStep 3020327 = 4530491) B4530491
theorem B1341007 : Blo 1340989 1341007 := bstep (se 1 (by rfl) ⟨1005755, by rfl⟩ : syracuseStep 1341007 = 2011511) B2011511
theorem B1341023 : Blo 1340989 1341023 := bstep (se 1 (by rfl) ⟨1005767, by rfl⟩ : syracuseStep 1341023 = 2011535) B2011535
theorem B1341051 : Blo 1340989 1341051 := bstep (se 1 (by rfl) ⟨1005788, by rfl⟩ : syracuseStep 1341051 = 2011577) B2011577
theorem B2012795 : Blo 1340989 2012795 := bstep (se 1 (by rfl) ⟨1509596, by rfl⟩ : syracuseStep 2012795 = 3019193) B3019193
theorem B1341103 : Blo 1340989 1341103 := bstep (se 1 (by rfl) ⟨1005827, by rfl⟩ : syracuseStep 1341103 = 2011655) B2011655
theorem B1341127 : Blo 1340989 1341127 := bstep (se 1 (by rfl) ⟨1005845, by rfl⟩ : syracuseStep 1341127 = 2011691) B2011691
theorem B15496903 : Blo 1340989 15496903 := bstep (se 1 (by rfl) ⟨11622677, by rfl⟩ : syracuseStep 15496903 = 23245355) B23245355
theorem B10188503 : Blo 1340989 10188503 := bstep (se 1 (by rfl) ⟨7641377, by rfl⟩ : syracuseStep 10188503 = 15282755) B15282755
theorem B1341147 : Blo 1340989 1341147 := bstep (se 1 (by rfl) ⟨1005860, by rfl⟩ : syracuseStep 1341147 = 2011721) B2011721
theorem B2012921 : Blo 1340989 2012921 := bstep (se 2 (by rfl) ⟨754845, by rfl⟩ : syracuseStep 2012921 = 1509691) B1509691
theorem B1341223 : Blo 1340989 1341223 := bstep (se 1 (by rfl) ⟨1005917, by rfl⟩ : syracuseStep 1341223 = 2011835) B2011835
theorem B1341263 : Blo 1340989 1341263 := bstep (se 1 (by rfl) ⟨1005947, by rfl⟩ : syracuseStep 1341263 = 2011895) B2011895
theorem B1341279 : Blo 1340989 1341279 := bstep (se 1 (by rfl) ⟨1005959, by rfl⟩ : syracuseStep 1341279 = 2011919) B2011919
theorem B2013023 : Blo 1340989 2013023 := bstep (se 1 (by rfl) ⟨1509767, by rfl⟩ : syracuseStep 2013023 = 3019535) B3019535
theorem B2013035 : Blo 1340989 2013035 := bstep (se 1 (by rfl) ⟨1509776, by rfl⟩ : syracuseStep 2013035 = 3019553) B3019553
theorem B3020651 : Blo 1340989 3020651 := bstep (se 1 (by rfl) ⟨2265488, by rfl⟩ : syracuseStep 3020651 = 4530977) B4530977
theorem B6289271 : Blo 1340989 6289271 := bstep (se 1 (by rfl) ⟨4716953, by rfl⟩ : syracuseStep 6289271 = 9433907) B9433907
theorem B1341307 : Blo 1340989 1341307 := bstep (se 1 (by rfl) ⟨1005980, by rfl⟩ : syracuseStep 1341307 = 2011961) B2011961
theorem B3020705 : Blo 1340989 3020705 := bstep (se 2 (by rfl) ⟨1132764, by rfl⟩ : syracuseStep 3020705 = 2265529) B2265529
theorem B1341359 : Blo 1340989 1341359 := bstep (se 1 (by rfl) ⟨1006019, by rfl⟩ : syracuseStep 1341359 = 2012039) B2012039
theorem B17192897 : Blo 1340989 17192897 := bstep (se 2 (by rfl) ⟨6447336, by rfl⟩ : syracuseStep 17192897 = 12894673) B12894673
theorem B1341383 : Blo 1340989 1341383 := bstep (se 1 (by rfl) ⟨1006037, by rfl⟩ : syracuseStep 1341383 = 2012075) B2012075
theorem B1341403 : Blo 1340989 1341403 := bstep (se 1 (by rfl) ⟨1006052, by rfl⟩ : syracuseStep 1341403 = 2012105) B2012105
theorem B1341479 : Blo 1340989 1341479 := bstep (se 1 (by rfl) ⟨1006109, by rfl⟩ : syracuseStep 1341479 = 2012219) B2012219
theorem B1341519 : Blo 1340989 1341519 := bstep (se 1 (by rfl) ⟨1006139, by rfl⟩ : syracuseStep 1341519 = 2012279) B2012279
theorem B2013263 : Blo 1340989 2013263 := bstep (se 1 (by rfl) ⟨1509947, by rfl⟩ : syracuseStep 2013263 = 3019895) B3019895
theorem B1341535 : Blo 1340989 1341535 := bstep (se 1 (by rfl) ⟨1006151, by rfl⟩ : syracuseStep 1341535 = 2012303) B2012303
theorem B1341563 : Blo 1340989 1341563 := bstep (se 1 (by rfl) ⟨1006172, by rfl⟩ : syracuseStep 1341563 = 2012345) B2012345
theorem B3823787 : Blo 1340989 3823787 := bstep (se 1 (by rfl) ⟨2867840, by rfl⟩ : syracuseStep 3823787 = 5735681) B5735681
theorem B1341615 : Blo 1340989 1341615 := bstep (se 1 (by rfl) ⟨1006211, by rfl⟩ : syracuseStep 1341615 = 2012423) B2012423
theorem B1341639 : Blo 1340989 1341639 := bstep (se 1 (by rfl) ⟨1006229, by rfl⟩ : syracuseStep 1341639 = 2012459) B2012459
theorem B2013383 : Blo 1340989 2013383 := bstep (se 1 (by rfl) ⟨1510037, by rfl⟩ : syracuseStep 2013383 = 3020075) B3020075
theorem B1341659 : Blo 1340989 1341659 := bstep (se 1 (by rfl) ⟨1006244, by rfl⟩ : syracuseStep 1341659 = 2012489) B2012489
theorem B3021047 : Blo 1340989 3021047 := bstep (se 1 (by rfl) ⟨2265785, by rfl⟩ : syracuseStep 3021047 = 4531571) B4531571
theorem B1341735 : Blo 1340989 1341735 := bstep (se 1 (by rfl) ⟨1006301, by rfl⟩ : syracuseStep 1341735 = 2012603) B2012603
theorem B1341775 : Blo 1340989 1341775 := bstep (se 1 (by rfl) ⟨1006331, by rfl⟩ : syracuseStep 1341775 = 2012663) B2012663
theorem B1341791 : Blo 1340989 1341791 := bstep (se 1 (by rfl) ⟨1006343, by rfl⟩ : syracuseStep 1341791 = 2012687) B2012687
theorem B11032937 : Blo 1340989 11032937 := bstep (se 2 (by rfl) ⟨4137351, by rfl⟩ : syracuseStep 11032937 = 8274703) B8274703
theorem B2013545 : Blo 1340989 2013545 := bstep (se 2 (by rfl) ⟨755079, by rfl⟩ : syracuseStep 2013545 = 1510159) B1510159
theorem B1341819 : Blo 1340989 1341819 := bstep (se 1 (by rfl) ⟨1006364, by rfl⟩ : syracuseStep 1341819 = 2012729) B2012729
theorem B6805889 : Blo 1340989 6805889 := bstep (se 2 (by rfl) ⟨2552208, by rfl⟩ : syracuseStep 6805889 = 5104417) B5104417
theorem B2546063 : Blo 1340989 2546063 := bstep (se 1 (by rfl) ⟨1909547, by rfl⟩ : syracuseStep 2546063 = 3819095) B3819095
theorem B1341871 : Blo 1340989 1341871 := bstep (se 1 (by rfl) ⟨1006403, by rfl⟩ : syracuseStep 1341871 = 2012807) B2012807
theorem B2013623 : Blo 1340989 2013623 := bstep (se 1 (by rfl) ⟨1510217, by rfl⟩ : syracuseStep 2013623 = 3020435) B3020435
theorem B1341895 : Blo 1340989 1341895 := bstep (se 1 (by rfl) ⟨1006421, by rfl⟩ : syracuseStep 1341895 = 2012843) B2012843
theorem B1341915 : Blo 1340989 1341915 := bstep (se 1 (by rfl) ⟨1006436, by rfl⟩ : syracuseStep 1341915 = 2012873) B2012873
theorem B2013659 : Blo 1340989 2013659 := bstep (se 1 (by rfl) ⟨1510244, by rfl⟩ : syracuseStep 2013659 = 3020489) B3020489
theorem B15292961 : Blo 1340989 15292961 := bstep (se 2 (by rfl) ⟨5734860, by rfl⟩ : syracuseStep 15292961 = 11469721) B11469721
theorem B1341991 : Blo 1340989 1341991 := bstep (se 1 (by rfl) ⟨1006493, by rfl⟩ : syracuseStep 1341991 = 2012987) B2012987
theorem B3398183 : Blo 1340989 3398183 := bstep (se 1 (by rfl) ⟨2548637, by rfl⟩ : syracuseStep 3398183 = 5097275) B5097275
theorem B1342031 : Blo 1340989 1342031 := bstep (se 1 (by rfl) ⟨1006523, by rfl⟩ : syracuseStep 1342031 = 2013047) B2013047
theorem B1342047 : Blo 1340989 1342047 := bstep (se 1 (by rfl) ⟨1006535, by rfl⟩ : syracuseStep 1342047 = 2013071) B2013071
theorem B4528763 : Blo 1340989 4528763 := bstep (se 1 (by rfl) ⟨3396572, by rfl⟩ : syracuseStep 4528763 = 6793145) B6793145
theorem B1342075 : Blo 1340989 1342075 := bstep (se 1 (by rfl) ⟨1006556, by rfl⟩ : syracuseStep 1342075 = 2013113) B2013113
theorem B3226235 : Blo 1340989 3226235 := bstep (se 1 (by rfl) ⟨2419676, by rfl⟩ : syracuseStep 3226235 = 4839353) B4839353
theorem B1342127 : Blo 1340989 1342127 := bstep (se 1 (by rfl) ⟨1006595, by rfl⟩ : syracuseStep 1342127 = 2013191) B2013191
theorem B1342151 : Blo 1340989 1342151 := bstep (se 1 (by rfl) ⟨1006613, by rfl⟩ : syracuseStep 1342151 = 2013227) B2013227
theorem B1342171 : Blo 1340989 1342171 := bstep (se 1 (by rfl) ⟨1006628, by rfl⟩ : syracuseStep 1342171 = 2013257) B2013257
theorem B4528925 : Blo 1340989 4528925 := bstep (se 3 (by rfl) ⟨849173, by rfl⟩ : syracuseStep 4528925 = 1698347) B1698347
theorem B1342247 : Blo 1340989 1342247 := bstep (se 1 (by rfl) ⟨1006685, by rfl⟩ : syracuseStep 1342247 = 2013371) B2013371
theorem B8166217 : Blo 1340989 8166217 := bstep (se 2 (by rfl) ⟨3062331, by rfl⟩ : syracuseStep 8166217 = 6124663) B6124663
theorem B3021641 : Blo 1340989 3021641 := bstep (se 2 (by rfl) ⟨1133115, by rfl⟩ : syracuseStep 3021641 = 2266231) B2266231
theorem B1342287 : Blo 1340989 1342287 := bstep (se 1 (by rfl) ⟨1006715, by rfl⟩ : syracuseStep 1342287 = 2013431) B2013431
theorem B1342303 : Blo 1340989 1342303 := bstep (se 1 (by rfl) ⟨1006727, by rfl⟩ : syracuseStep 1342303 = 2013455) B2013455
theorem B3398507 : Blo 1340989 3398507 := bstep (se 1 (by rfl) ⟨2548880, by rfl⟩ : syracuseStep 3398507 = 5097761) B5097761
theorem B3226475 : Blo 1340989 3226475 := bstep (se 1 (by rfl) ⟨2419856, by rfl⟩ : syracuseStep 3226475 = 4839713) B4839713
theorem B32627573 : Blo 1340989 32627573 := bstep (se 5 (by rfl) ⟨1529417, by rfl⟩ : syracuseStep 32627573 = 3058835) B3058835
theorem B1342331 : Blo 1340989 1342331 := bstep (se 1 (by rfl) ⟨1006748, by rfl⟩ : syracuseStep 1342331 = 2013497) B2013497
theorem B1342383 : Blo 1340989 1342383 := bstep (se 1 (by rfl) ⟨1006787, by rfl⟩ : syracuseStep 1342383 = 2013575) B2013575
theorem B2014127 : Blo 1340989 2014127 := bstep (se 1 (by rfl) ⟨1510595, by rfl⟩ : syracuseStep 2014127 = 3021191) B3021191
theorem B1342407 : Blo 1340989 1342407 := bstep (se 1 (by rfl) ⟨1006805, by rfl⟩ : syracuseStep 1342407 = 2013611) B2013611
theorem B1342427 : Blo 1340989 1342427 := bstep (se 1 (by rfl) ⟨1006820, by rfl⟩ : syracuseStep 1342427 = 2013641) B2013641
theorem B2014217 : Blo 1340989 2014217 := bstep (se 2 (by rfl) ⟨755331, by rfl⟩ : syracuseStep 2014217 = 1510663) B1510663
theorem B1342503 : Blo 1340989 1342503 := bstep (se 1 (by rfl) ⟨1006877, by rfl⟩ : syracuseStep 1342503 = 2013755) B2013755
theorem B2014247 : Blo 1340989 2014247 := bstep (se 1 (by rfl) ⟨1510685, by rfl⟩ : syracuseStep 2014247 = 3021371) B3021371
theorem B1342543 : Blo 1340989 1342543 := bstep (se 1 (by rfl) ⟨1006907, by rfl⟩ : syracuseStep 1342543 = 2013815) B2013815
theorem B1342559 : Blo 1340989 1342559 := bstep (se 1 (by rfl) ⟨1006919, by rfl⟩ : syracuseStep 1342559 = 2013839) B2013839
theorem B1342587 : Blo 1340989 1342587 := bstep (se 1 (by rfl) ⟨1006940, by rfl⟩ : syracuseStep 1342587 = 2013881) B2013881
theorem B2014331 : Blo 1340989 2014331 := bstep (se 1 (by rfl) ⟨1510748, by rfl⟩ : syracuseStep 2014331 = 3021497) B3021497
theorem B1342639 : Blo 1340989 1342639 := bstep (se 1 (by rfl) ⟨1006979, by rfl⟩ : syracuseStep 1342639 = 2013959) B2013959
theorem B19619009 : Blo 1340989 19619009 := bstep (se 2 (by rfl) ⟨7357128, by rfl⟩ : syracuseStep 19619009 = 14714257) B14714257
theorem B1342663 : Blo 1340989 1342663 := bstep (se 1 (by rfl) ⟨1006997, by rfl⟩ : syracuseStep 1342663 = 2013995) B2013995
theorem B1342683 : Blo 1340989 1342683 := bstep (se 1 (by rfl) ⟨1007012, by rfl⟩ : syracuseStep 1342683 = 2014025) B2014025
theorem B6790391 : Blo 1340989 6790391 := bstep (se 1 (by rfl) ⟨5092793, by rfl⟩ : syracuseStep 6790391 = 10185587) B10185587
theorem B5094647 : Blo 1340989 5094647 := bstep (se 1 (by rfl) ⟨3820985, by rfl⟩ : syracuseStep 5094647 = 7641971) B7641971
theorem B2866423 : Blo 1340989 2866423 := bstep (se 1 (by rfl) ⟨2149817, by rfl⟩ : syracuseStep 2866423 = 4299635) B4299635
theorem B2014457 : Blo 1340989 2014457 := bstep (se 2 (by rfl) ⟨755421, by rfl⟩ : syracuseStep 2014457 = 1510843) B1510843
theorem B8592655 : Blo 1340989 8592655 := bstep (se 1 (by rfl) ⟨6444491, by rfl⟩ : syracuseStep 8592655 = 12888983) B12888983
theorem B1342759 : Blo 1340989 1342759 := bstep (se 1 (by rfl) ⟨1007069, by rfl⟩ : syracuseStep 1342759 = 2014139) B2014139
theorem B1342799 : Blo 1340989 1342799 := bstep (se 1 (by rfl) ⟨1007099, by rfl⟩ : syracuseStep 1342799 = 2014199) B2014199
theorem B1342815 : Blo 1340989 1342815 := bstep (se 1 (by rfl) ⟨1007111, by rfl⟩ : syracuseStep 1342815 = 2014223) B2014223
theorem B1342843 : Blo 1340989 1342843 := bstep (se 1 (by rfl) ⟨1007132, by rfl⟩ : syracuseStep 1342843 = 2014265) B2014265
theorem B24501629 : Blo 1340989 24501629 := bstep (se 3 (by rfl) ⟨4594055, by rfl⟩ : syracuseStep 24501629 = 9188111) B9188111
theorem B2547119 : Blo 1340989 2547119 := bstep (se 1 (by rfl) ⟨1910339, by rfl⟩ : syracuseStep 2547119 = 3820679) B3820679
theorem B1342895 : Blo 1340989 1342895 := bstep (se 1 (by rfl) ⟨1007171, by rfl⟩ : syracuseStep 1342895 = 2014343) B2014343
theorem B1342919 : Blo 1340989 1342919 := bstep (se 1 (by rfl) ⟨1007189, by rfl⟩ : syracuseStep 1342919 = 2014379) B2014379
theorem B4529627 : Blo 1340989 4529627 := bstep (se 1 (by rfl) ⟨3397220, by rfl⟩ : syracuseStep 4529627 = 6794441) B6794441
theorem B1342939 : Blo 1340989 1342939 := bstep (se 1 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 1342939 = 2014409) B2014409
theorem B6888947 : Blo 1340989 6888947 := bstep (se 1 (by rfl) ⟨5166710, by rfl⟩ : syracuseStep 6888947 = 10333421) B10333421
theorem B3399155 : Blo 1340989 3399155 := bstep (se 1 (by rfl) ⟨2549366, by rfl⟩ : syracuseStep 3399155 = 5098733) B5098733
theorem B3399367 : Blo 1340989 3399367 := bstep (se 1 (by rfl) ⟨2549525, by rfl⟩ : syracuseStep 3399367 = 5099051) B5099051
theorem B6790877 : Blo 1340989 6790877 := bstep (se 3 (by rfl) ⟨1273289, by rfl⟩ : syracuseStep 6790877 = 2546579) B2546579
theorem B627351317 : Blo 1340989 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B6889283 : Blo 1340989 6889283 := bstep (se 1 (by rfl) ⟨5166962, by rfl⟩ : syracuseStep 6889283 = 10333925) B10333925
theorem B2547551 : Blo 1340989 2547551 := bstep (se 1 (by rfl) ⟨1910663, by rfl⟩ : syracuseStep 2547551 = 3821327) B3821327
theorem B20652083 : Blo 1340989 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B25780355 : Blo 1340989 25780355 := bstep (se 1 (by rfl) ⟨19335266, by rfl⟩ : syracuseStep 25780355 = 38670533) B38670533
theorem B22946003 : Blo 1340989 22946003 := bstep (se 1 (by rfl) ⟨17209502, by rfl⟩ : syracuseStep 22946003 = 34419005) B34419005
theorem B2867567 : Blo 1340989 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B4530707 : Blo 1340989 4530707 := bstep (se 1 (by rfl) ⟨3398030, by rfl⟩ : syracuseStep 4530707 = 6796061) B6796061
theorem B2040391 : Blo 1340989 2040391 := bstep (se 1 (by rfl) ⟨1530293, by rfl⟩ : syracuseStep 2040391 = 3060587) B3060587
theorem B5735033 : Blo 1340989 5735033 := bstep (se 2 (by rfl) ⟨2150637, by rfl⟩ : syracuseStep 5735033 = 4301275) B4301275
theorem B6890183 : Blo 1340989 6890183 := bstep (se 1 (by rfl) ⟨5167637, by rfl⟩ : syracuseStep 6890183 = 10335275) B10335275
theorem B10183643 : Blo 1340989 10183643 := bstep (se 1 (by rfl) ⟨7637732, by rfl⟩ : syracuseStep 10183643 = 15275465) B15275465
theorem B10888289 : Blo 1340989 10888289 := bstep (se 2 (by rfl) ⟨4083108, by rfl⟩ : syracuseStep 10888289 = 8166217) B8166217
theorem B6792335 : Blo 1340989 6792335 := bstep (se 1 (by rfl) ⟨5094251, by rfl⟩ : syracuseStep 6792335 = 10188503) B10188503
theorem B5096591 : Blo 1340989 5096591 := bstep (se 1 (by rfl) ⟨3822443, by rfl⟩ : syracuseStep 5096591 = 7644887) B7644887
theorem B10880243 : Blo 1340989 10880243 := bstep (se 1 (by rfl) ⟨8160182, by rfl⟩ : syracuseStep 10880243 = 16320365) B16320365
theorem B12895523 : Blo 1340989 12895523 := bstep (se 1 (by rfl) ⟨9671642, by rfl⟩ : syracuseStep 12895523 = 19343285) B19343285
theorem B1508647 : Blo 1340989 1508647 := bstep (se 1 (by rfl) ⟨1131485, by rfl⟩ : syracuseStep 1508647 = 2262971) B2262971
theorem B11461931 : Blo 1340989 11461931 := bstep (se 1 (by rfl) ⟨8596448, by rfl⟩ : syracuseStep 11461931 = 17192897) B17192897
theorem B1508719 : Blo 1340989 1508719 := bstep (se 1 (by rfl) ⟨1131539, by rfl⟩ : syracuseStep 1508719 = 2263079) B2263079
theorem B10323389 : Blo 1340989 10323389 := bstep (se 3 (by rfl) ⟨1935635, by rfl⟩ : syracuseStep 10323389 = 3871271) B3871271
theorem B1508935 : Blo 1340989 1508935 := bstep (se 1 (by rfl) ⟨1131701, by rfl⟩ : syracuseStep 1508935 = 2263403) B2263403
theorem B1697375 : Blo 1340989 1697375 := bstep (se 1 (by rfl) ⟨1273031, by rfl⟩ : syracuseStep 1697375 = 2546063) B2546063
theorem B8603293 : Blo 1340989 8603293 := bstep (se 3 (by rfl) ⟨1613117, by rfl⟩ : syracuseStep 8603293 = 3226235) B3226235
theorem B4589243 : Blo 1340989 4589243 := bstep (se 1 (by rfl) ⟨3441932, by rfl⟩ : syracuseStep 4589243 = 6883865) B6883865
theorem B21751715 : Blo 1340989 21751715 := bstep (se 1 (by rfl) ⟨16313786, by rfl⟩ : syracuseStep 21751715 = 32627573) B32627573
theorem B2262991 : Blo 1340989 2262991 := bstep (se 1 (by rfl) ⟨1697243, by rfl⟩ : syracuseStep 2262991 = 3394487) B3394487
theorem B10192877 : Blo 1340989 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B6793469 : Blo 1340989 6793469 := bstep (se 3 (by rfl) ⟨1273775, by rfl⟩ : syracuseStep 6793469 = 2547551) B2547551
theorem B20662537 : Blo 1340989 20662537 := bstep (se 2 (by rfl) ⟨7748451, by rfl⟩ : syracuseStep 20662537 = 15496903) B15496903
theorem B12249353 : Blo 1340989 12249353 := bstep (se 2 (by rfl) ⟨4593507, by rfl⟩ : syracuseStep 12249353 = 9187015) B9187015
theorem B4532489 : Blo 1340989 4532489 := bstep (se 2 (by rfl) ⟨1699683, by rfl⟩ : syracuseStep 4532489 = 3399367) B3399367
theorem B16320797 : Blo 1340989 16320797 := bstep (se 3 (by rfl) ⟨3060149, by rfl⟩ : syracuseStep 16320797 = 6120299) B6120299
theorem B1698079 : Blo 1340989 1698079 := bstep (se 1 (by rfl) ⟨1273559, by rfl⟩ : syracuseStep 1698079 = 2547119) B2547119
theorem B1509799 : Blo 1340989 1509799 := bstep (se 1 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 1509799 = 2264699) B2264699
theorem B10193363 : Blo 1340989 10193363 := bstep (se 1 (by rfl) ⟨7645022, by rfl⟩ : syracuseStep 10193363 = 15290045) B15290045
theorem B71690773 : Blo 1340989 71690773 := bstep (se 6 (by rfl) ⟨1680252, by rfl⟩ : syracuseStep 71690773 = 3360505) B3360505
theorem B2263673 : Blo 1340989 2263673 := bstep (se 2 (by rfl) ⟨848877, by rfl⟩ : syracuseStep 2263673 = 1697755) B1697755
theorem B2263727 : Blo 1340989 2263727 := bstep (se 1 (by rfl) ⟨1697795, by rfl⟩ : syracuseStep 2263727 = 3395591) B3395591
theorem B2149087 : Blo 1340989 2149087 := bstep (se 1 (by rfl) ⟨1611815, by rfl⟩ : syracuseStep 2149087 = 3223631) B3223631
theorem B3820279 : Blo 1340989 3820279 := bstep (se 1 (by rfl) ⟨2865209, by rfl⟩ : syracuseStep 3820279 = 5730419) B5730419
theorem B3017627 : Blo 1340989 3017627 := bstep (se 1 (by rfl) ⟨2263220, by rfl⟩ : syracuseStep 3017627 = 4526441) B4526441
theorem B2263963 : Blo 1340989 2263963 := bstep (se 1 (by rfl) ⟨1697972, by rfl⟩ : syracuseStep 2263963 = 3395945) B3395945
theorem B1510375 : Blo 1340989 1510375 := bstep (se 1 (by rfl) ⟨1132781, by rfl⟩ : syracuseStep 1510375 = 2265563) B2265563
theorem B6794279 : Blo 1340989 6794279 := bstep (se 1 (by rfl) ⟨5095709, by rfl⟩ : syracuseStep 6794279 = 10191419) B10191419
theorem B5098535 : Blo 1340989 5098535 := bstep (se 1 (by rfl) ⟨3823901, by rfl⟩ : syracuseStep 5098535 = 7647803) B7647803
theorem B7638097 : Blo 1340989 7638097 := bstep (se 2 (by rfl) ⟨2864286, by rfl⟩ : syracuseStep 7638097 = 5728573) B5728573
theorem B3017825 : Blo 1340989 3017825 := bstep (se 2 (by rfl) ⟨1131684, by rfl⟩ : syracuseStep 3017825 = 2263369) B2263369
theorem B3018023 : Blo 1340989 3018023 := bstep (se 1 (by rfl) ⟨2263517, by rfl⟩ : syracuseStep 3018023 = 4527035) B4527035
theorem B7646663 : Blo 1340989 7646663 := bstep (se 1 (by rfl) ⟨5734997, by rfl⟩ : syracuseStep 7646663 = 11469995) B11469995
theorem B3395155 : Blo 1340989 3395155 := bstep (se 1 (by rfl) ⟨2546366, by rfl⟩ : syracuseStep 3395155 = 5092733) B5092733
theorem B48991877 : Blo 1340989 48991877 := bstep (se 4 (by rfl) ⟨4592988, by rfl⟩ : syracuseStep 48991877 = 9185977) B9185977
theorem B3018401 : Blo 1340989 3018401 := bstep (se 2 (by rfl) ⟨1131900, by rfl⟩ : syracuseStep 3018401 = 2263801) B2263801
theorem B4591417 : Blo 1340989 4591417 := bstep (se 2 (by rfl) ⟨1721781, by rfl⟩ : syracuseStep 4591417 = 3443563) B3443563
theorem B18370525 : Blo 1340989 18370525 := bstep (se 3 (by rfl) ⟨3444473, by rfl⟩ : syracuseStep 18370525 = 6888947) B6888947
theorem B3018761 : Blo 1340989 3018761 := bstep (se 2 (by rfl) ⟨1132035, by rfl⟩ : syracuseStep 3018761 = 2264071) B2264071
theorem B7254035 : Blo 1340989 7254035 := bstep (se 1 (by rfl) ⟨5440526, by rfl⟩ : syracuseStep 7254035 = 10881053) B10881053
theorem B3821897 : Blo 1340989 3821897 := bstep (se 2 (by rfl) ⟨1433211, by rfl⟩ : syracuseStep 3821897 = 2866423) B2866423
theorem B11456873 : Blo 1340989 11456873 := bstep (se 2 (by rfl) ⟨4296327, by rfl⟩ : syracuseStep 11456873 = 8592655) B8592655
theorem B10195307 : Blo 1340989 10195307 := bstep (se 1 (by rfl) ⟨7646480, by rfl⟩ : syracuseStep 10195307 = 15292961) B15292961
theorem B2265455 : Blo 1340989 2265455 := bstep (se 1 (by rfl) ⟨1699091, by rfl⟩ : syracuseStep 2265455 = 3398183) B3398183
theorem B2011559 : Blo 1340989 2011559 := bstep (se 1 (by rfl) ⟨1508669, by rfl⟩ : syracuseStep 2011559 = 3017339) B3017339
theorem B3019175 : Blo 1340989 3019175 := bstep (se 1 (by rfl) ⟨2264381, by rfl⟩ : syracuseStep 3019175 = 4528763) B4528763
theorem B2011643 : Blo 1340989 2011643 := bstep (se 1 (by rfl) ⟨1508732, by rfl⟩ : syracuseStep 2011643 = 3017465) B3017465
theorem B3224083 : Blo 1340989 3224083 := bstep (se 1 (by rfl) ⟨2418062, by rfl⟩ : syracuseStep 3224083 = 4836125) B4836125
theorem B3019283 : Blo 1340989 3019283 := bstep (se 1 (by rfl) ⟨2264462, by rfl⟩ : syracuseStep 3019283 = 4528925) B4528925
theorem B17199661 : Blo 1340989 17199661 := bstep (se 3 (by rfl) ⟨3224936, by rfl⟩ : syracuseStep 17199661 = 6449873) B6449873
theorem B10883645 : Blo 1340989 10883645 := bstep (se 3 (by rfl) ⟨2040683, by rfl⟩ : syracuseStep 10883645 = 4081367) B4081367
theorem B2265671 : Blo 1340989 2265671 := bstep (se 1 (by rfl) ⟨1699253, by rfl⟩ : syracuseStep 2265671 = 3398507) B3398507
theorem B2150983 : Blo 1340989 2150983 := bstep (se 1 (by rfl) ⟨1613237, by rfl⟩ : syracuseStep 2150983 = 3226475) B3226475
theorem B3019337 : Blo 1340989 3019337 := bstep (se 2 (by rfl) ⟨1132251, by rfl⟩ : syracuseStep 3019337 = 2264503) B2264503
theorem B2011769 : Blo 1340989 2011769 := bstep (se 2 (by rfl) ⟨754413, by rfl⟩ : syracuseStep 2011769 = 1508827) B1508827
theorem B2011823 : Blo 1340989 2011823 := bstep (se 1 (by rfl) ⟨1508867, by rfl⟩ : syracuseStep 2011823 = 3017735) B3017735
theorem B2011871 : Blo 1340989 2011871 := bstep (se 1 (by rfl) ⟨1508903, by rfl⟩ : syracuseStep 2011871 = 3017807) B3017807
theorem B13079339 : Blo 1340989 13079339 := bstep (se 1 (by rfl) ⟨9809504, by rfl⟩ : syracuseStep 13079339 = 19619009) B19619009
theorem B4526927 : Blo 1340989 4526927 := bstep (se 1 (by rfl) ⟨3395195, by rfl⟩ : syracuseStep 4526927 = 6790391) B6790391
theorem B3396431 : Blo 1340989 3396431 := bstep (se 1 (by rfl) ⟨2547323, by rfl⟩ : syracuseStep 3396431 = 5094647) B5094647
theorem B2012135 : Blo 1340989 2012135 := bstep (se 1 (by rfl) ⟨1509101, by rfl⟩ : syracuseStep 2012135 = 3018203) B3018203
theorem B3019751 : Blo 1340989 3019751 := bstep (se 1 (by rfl) ⟨2264813, by rfl⟩ : syracuseStep 3019751 = 4529627) B4529627
theorem B2266103 : Blo 1340989 2266103 := bstep (se 1 (by rfl) ⟨1699577, by rfl⟩ : syracuseStep 2266103 = 3399155) B3399155
theorem B6796385 : Blo 1340989 6796385 := bstep (se 2 (by rfl) ⟨2548644, by rfl⟩ : syracuseStep 6796385 = 5097289) B5097289
theorem B4527251 : Blo 1340989 4527251 := bstep (se 1 (by rfl) ⟨3395438, by rfl⟩ : syracuseStep 4527251 = 6790877) B6790877
theorem B4592855 : Blo 1340989 4592855 := bstep (se 1 (by rfl) ⟨3444641, by rfl⟩ : syracuseStep 4592855 = 6889283) B6889283
theorem B2012393 : Blo 1340989 2012393 := bstep (se 2 (by rfl) ⟨754647, by rfl⟩ : syracuseStep 2012393 = 1509295) B1509295
theorem B2012447 : Blo 1340989 2012447 := bstep (se 1 (by rfl) ⟨1509335, by rfl⟩ : syracuseStep 2012447 = 3018671) B3018671
theorem B6452567 : Blo 1340989 6452567 := bstep (se 1 (by rfl) ⟨4839425, by rfl⟩ : syracuseStep 6452567 = 9678851) B9678851
theorem B5092703 : Blo 1340989 5092703 := bstep (se 1 (by rfl) ⟨3819527, by rfl⟩ : syracuseStep 5092703 = 7639055) B7639055
theorem B3224929 : Blo 1340989 3224929 := bstep (se 2 (by rfl) ⟨1209348, by rfl⟩ : syracuseStep 3224929 = 2418697) B2418697
theorem B3020129 : Blo 1340989 3020129 := bstep (se 2 (by rfl) ⟨1132548, by rfl⟩ : syracuseStep 3020129 = 2265097) B2265097
theorem B4298123 : Blo 1340989 4298123 := bstep (se 1 (by rfl) ⟨3223592, by rfl⟩ : syracuseStep 4298123 = 6447185) B6447185
theorem B4527521 : Blo 1340989 4527521 := bstep (se 2 (by rfl) ⟨1697820, by rfl⟩ : syracuseStep 4527521 = 3395641) B3395641
theorem B3020219 : Blo 1340989 3020219 := bstep (se 1 (by rfl) ⟨2265164, by rfl⟩ : syracuseStep 3020219 = 4530329) B4530329
theorem B7640513 : Blo 1340989 7640513 := bstep (se 2 (by rfl) ⟨2865192, by rfl⟩ : syracuseStep 7640513 = 5730385) B5730385
theorem B2012615 : Blo 1340989 2012615 := bstep (se 1 (by rfl) ⟨1509461, by rfl⟩ : syracuseStep 2012615 = 3018923) B3018923
theorem B3397079 : Blo 1340989 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B3020345 : Blo 1340989 3020345 := bstep (se 2 (by rfl) ⟨1132629, by rfl⟩ : syracuseStep 3020345 = 2265259) B2265259
theorem B1340991 : Blo 1340989 1340991 := bstep (se 1 (by rfl) ⟨1005743, by rfl⟩ : syracuseStep 1340991 = 2011487) B2011487
theorem B1340999 : Blo 1340989 1340999 := bstep (se 1 (by rfl) ⟨1005749, by rfl⟩ : syracuseStep 1340999 = 2011499) B2011499
theorem B1341151 : Blo 1340989 1341151 := bstep (se 1 (by rfl) ⟨1005863, by rfl⟩ : syracuseStep 1341151 = 2011727) B2011727
theorem B10196765 : Blo 1340989 10196765 := bstep (se 3 (by rfl) ⟨1911893, by rfl⟩ : syracuseStep 10196765 = 3823787) B3823787
theorem B2012969 : Blo 1340989 2012969 := bstep (se 2 (by rfl) ⟨754863, by rfl⟩ : syracuseStep 2012969 = 1509727) B1509727
theorem B1341231 : Blo 1340989 1341231 := bstep (se 1 (by rfl) ⟨1005923, by rfl⟩ : syracuseStep 1341231 = 2011847) B2011847
theorem B2012975 : Blo 1340989 2012975 := bstep (se 1 (by rfl) ⟨1509731, by rfl⟩ : syracuseStep 2012975 = 3019463) B3019463
theorem B3397423 : Blo 1340989 3397423 := bstep (se 1 (by rfl) ⟨2548067, by rfl⟩ : syracuseStep 3397423 = 5096135) B5096135
theorem B20657975 : Blo 1340989 20657975 := bstep (se 1 (by rfl) ⟨15493481, by rfl⟩ : syracuseStep 20657975 = 30986963) B30986963
theorem B1341339 : Blo 1340989 1341339 := bstep (se 1 (by rfl) ⟨1006004, by rfl⟩ : syracuseStep 1341339 = 2012009) B2012009
theorem B11466683 : Blo 1340989 11466683 := bstep (se 1 (by rfl) ⟨8600012, by rfl⟩ : syracuseStep 11466683 = 17200025) B17200025
theorem B1341391 : Blo 1340989 1341391 := bstep (se 1 (by rfl) ⟨1006043, by rfl⟩ : syracuseStep 1341391 = 2012087) B2012087
theorem B1341415 : Blo 1340989 1341415 := bstep (se 1 (by rfl) ⟨1006061, by rfl⟩ : syracuseStep 1341415 = 2012123) B2012123
theorem B5732333 : Blo 1340989 5732333 := bstep (se 3 (by rfl) ⟨1074812, by rfl⟩ : syracuseStep 5732333 = 2149625) B2149625
theorem B3021011 : Blo 1340989 3021011 := bstep (se 1 (by rfl) ⟨2265758, by rfl⟩ : syracuseStep 3021011 = 4531517) B4531517
theorem B2013449 : Blo 1340989 2013449 := bstep (se 2 (by rfl) ⟨755043, by rfl⟩ : syracuseStep 2013449 = 1510087) B1510087
theorem B3021065 : Blo 1340989 3021065 := bstep (se 2 (by rfl) ⟨1132899, by rfl⟩ : syracuseStep 3021065 = 2265799) B2265799
theorem B1341727 : Blo 1340989 1341727 := bstep (se 1 (by rfl) ⟨1006295, by rfl⟩ : syracuseStep 1341727 = 2012591) B2012591
theorem B1341787 : Blo 1340989 1341787 := bstep (se 1 (by rfl) ⟨1006340, by rfl⟩ : syracuseStep 1341787 = 2012681) B2012681
theorem B1341807 : Blo 1340989 1341807 := bstep (se 1 (by rfl) ⟨1006355, by rfl⟩ : syracuseStep 1341807 = 2012711) B2012711
theorem B2013551 : Blo 1340989 2013551 := bstep (se 1 (by rfl) ⟨1510163, by rfl⟩ : syracuseStep 2013551 = 3020327) B3020327
theorem B1341863 : Blo 1340989 1341863 := bstep (se 1 (by rfl) ⟨1006397, by rfl⟩ : syracuseStep 1341863 = 2012795) B2012795
theorem B3398071 : Blo 1340989 3398071 := bstep (se 1 (by rfl) ⟨2548553, by rfl⟩ : syracuseStep 3398071 = 5097107) B5097107
theorem B3021281 : Blo 1340989 3021281 := bstep (se 2 (by rfl) ⟨1132980, by rfl⟩ : syracuseStep 3021281 = 2265961) B2265961
theorem B3267067 : Blo 1340989 3267067 := bstep (se 1 (by rfl) ⟨2450300, by rfl⟩ : syracuseStep 3267067 = 4900601) B4900601
theorem B1341947 : Blo 1340989 1341947 := bstep (se 1 (by rfl) ⟨1006460, by rfl⟩ : syracuseStep 1341947 = 2012921) B2012921
theorem B1342015 : Blo 1340989 1342015 := bstep (se 1 (by rfl) ⟨1006511, by rfl⟩ : syracuseStep 1342015 = 2013023) B2013023
theorem B1342023 : Blo 1340989 1342023 := bstep (se 1 (by rfl) ⟨1006517, by rfl⟩ : syracuseStep 1342023 = 2013035) B2013035
theorem B2013767 : Blo 1340989 2013767 := bstep (se 1 (by rfl) ⟨1510325, by rfl⟩ : syracuseStep 2013767 = 3020651) B3020651
theorem B4192847 : Blo 1340989 4192847 := bstep (se 1 (by rfl) ⟨3144635, by rfl⟩ : syracuseStep 4192847 = 6289271) B6289271
theorem B19339883 : Blo 1340989 19339883 := bstep (se 1 (by rfl) ⟨14504912, by rfl⟩ : syracuseStep 19339883 = 29009825) B29009825
theorem B2013803 : Blo 1340989 2013803 := bstep (se 1 (by rfl) ⟨1510352, by rfl⟩ : syracuseStep 2013803 = 3020705) B3020705
theorem B6445763 : Blo 1340989 6445763 := bstep (se 1 (by rfl) ⟨4834322, by rfl⟩ : syracuseStep 6445763 = 9668645) B9668645
theorem B1342175 : Blo 1340989 1342175 := bstep (se 1 (by rfl) ⟨1006631, by rfl⟩ : syracuseStep 1342175 = 2013263) B2013263
theorem B3021587 : Blo 1340989 3021587 := bstep (se 1 (by rfl) ⟨2266190, by rfl⟩ : syracuseStep 3021587 = 4532381) B4532381
theorem B1342255 : Blo 1340989 1342255 := bstep (se 1 (by rfl) ⟨1006691, by rfl⟩ : syracuseStep 1342255 = 2013383) B2013383
theorem B2014031 : Blo 1340989 2014031 := bstep (se 1 (by rfl) ⟨1510523, by rfl⟩ : syracuseStep 2014031 = 3021047) B3021047
theorem B7355291 : Blo 1340989 7355291 := bstep (se 1 (by rfl) ⟨5516468, by rfl⟩ : syracuseStep 7355291 = 11032937) B11032937
theorem B1342363 : Blo 1340989 1342363 := bstep (se 1 (by rfl) ⟨1006772, by rfl⟩ : syracuseStep 1342363 = 2013545) B2013545
theorem B1612699 : Blo 1340989 1612699 := bstep (se 1 (by rfl) ⟨1209524, by rfl⟩ : syracuseStep 1612699 = 2419049) B2419049
theorem B4537259 : Blo 1340989 4537259 := bstep (se 1 (by rfl) ⟨3402944, by rfl⟩ : syracuseStep 4537259 = 6805889) B6805889
theorem B1342415 : Blo 1340989 1342415 := bstep (se 1 (by rfl) ⟨1006811, by rfl⟩ : syracuseStep 1342415 = 2013623) B2013623
theorem B1342439 : Blo 1340989 1342439 := bstep (se 1 (by rfl) ⟨1006829, by rfl⟩ : syracuseStep 1342439 = 2013659) B2013659
theorem B4299763 : Blo 1340989 4299763 := bstep (se 1 (by rfl) ⟨3224822, by rfl⟩ : syracuseStep 4299763 = 6449645) B6449645
theorem B2014427 : Blo 1340989 2014427 := bstep (se 1 (by rfl) ⟨1510820, by rfl⟩ : syracuseStep 2014427 = 3021641) B3021641
theorem B1342751 : Blo 1340989 1342751 := bstep (se 1 (by rfl) ⟨1007063, by rfl⟩ : syracuseStep 1342751 = 2014127) B2014127
theorem B6798653 : Blo 1340989 6798653 := bstep (se 3 (by rfl) ⟨1274747, by rfl⟩ : syracuseStep 6798653 = 2549495) B2549495
theorem B1342811 : Blo 1340989 1342811 := bstep (se 1 (by rfl) ⟨1007108, by rfl⟩ : syracuseStep 1342811 = 2014217) B2014217
theorem B1342831 : Blo 1340989 1342831 := bstep (se 1 (by rfl) ⟨1007123, by rfl⟩ : syracuseStep 1342831 = 2014247) B2014247
theorem B1342887 : Blo 1340989 1342887 := bstep (se 1 (by rfl) ⟨1007165, by rfl⟩ : syracuseStep 1342887 = 2014331) B2014331
theorem B1342971 : Blo 1340989 1342971 := bstep (se 1 (by rfl) ⟨1007228, by rfl⟩ : syracuseStep 1342971 = 2014457) B2014457
theorem B6790715 : Blo 1340989 6790715 := bstep (se 1 (by rfl) ⟨5093036, by rfl⟩ : syracuseStep 6790715 = 10186073) B10186073
theorem B16334419 : Blo 1340989 16334419 := bstep (se 1 (by rfl) ⟨12250814, by rfl⟩ : syracuseStep 16334419 = 24501629) B24501629
theorem B418234211 : Blo 1340989 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B21765995 : Blo 1340989 21765995 := bstep (se 1 (by rfl) ⟨16324496, by rfl⟩ : syracuseStep 21765995 = 32648993) B32648993
theorem B1433575 : Blo 1340989 1433575 := bstep (se 1 (by rfl) ⟨1075181, by rfl⟩ : syracuseStep 1433575 = 2150363) B2150363
theorem B17186903 : Blo 1340989 17186903 := bstep (se 1 (by rfl) ⟨12890177, by rfl⟩ : syracuseStep 17186903 = 25780355) B25780355
theorem B2547931 : Blo 1340989 2547931 := bstep (se 1 (by rfl) ⟨1910948, by rfl⟩ : syracuseStep 2547931 = 3821897) B3821897
theorem B27550049 : Blo 1340989 27550049 := bstep (se 2 (by rfl) ⟨10331268, by rfl⟩ : syracuseStep 27550049 = 20662537) B20662537
theorem B4530761 : Blo 1340989 4530761 := bstep (se 2 (by rfl) ⟨1699035, by rfl⟩ : syracuseStep 4530761 = 3398071) B3398071
theorem B4530923 : Blo 1340989 4530923 := bstep (se 1 (by rfl) ⟨3398192, by rfl⟩ : syracuseStep 4530923 = 6796385) B6796385
theorem B7258859 : Blo 1340989 7258859 := bstep (se 1 (by rfl) ⟨5444144, by rfl⟩ : syracuseStep 7258859 = 10888289) B10888289
theorem B2867977 : Blo 1340989 2867977 := bstep (se 2 (by rfl) ⟨1075491, by rfl⟩ : syracuseStep 2867977 = 2150983) B2150983
theorem B4301711 : Blo 1340989 4301711 := bstep (se 1 (by rfl) ⟨3226283, by rfl⟩ : syracuseStep 4301711 = 6452567) B6452567
theorem B6882259 : Blo 1340989 6882259 := bstep (se 1 (by rfl) ⟨5161694, by rfl⟩ : syracuseStep 6882259 = 10323389) B10323389
theorem B14501143 : Blo 1340989 14501143 := bstep (se 1 (by rfl) ⟨10875857, by rfl⟩ : syracuseStep 14501143 = 21751715) B21751715
theorem B7644455 : Blo 1340989 7644455 := bstep (se 1 (by rfl) ⟨5733341, by rfl⟩ : syracuseStep 7644455 = 11466683) B11466683
theorem B10184129 : Blo 1340989 10184129 := bstep (se 2 (by rfl) ⟨3819048, by rfl⟩ : syracuseStep 10184129 = 7638097) B7638097
theorem B10880531 : Blo 1340989 10880531 := bstep (se 1 (by rfl) ⟨8160398, by rfl⟩ : syracuseStep 10880531 = 16320797) B16320797
theorem B2795231 : Blo 1340989 2795231 := bstep (se 1 (by rfl) ⟨2096423, by rfl⟩ : syracuseStep 2795231 = 4192847) B4192847
theorem B1509115 : Blo 1340989 1509115 := bstep (se 1 (by rfl) ⟨1131836, by rfl⟩ : syracuseStep 1509115 = 2263673) B2263673
theorem B1509151 : Blo 1340989 1509151 := bstep (se 1 (by rfl) ⟨1131863, by rfl⟩ : syracuseStep 1509151 = 2263727) B2263727
theorem B11471057 : Blo 1340989 11471057 := bstep (se 2 (by rfl) ⟨4301646, by rfl⟩ : syracuseStep 11471057 = 8603293) B8603293
theorem B4532435 : Blo 1340989 4532435 := bstep (se 1 (by rfl) ⟨3399326, by rfl⟩ : syracuseStep 4532435 = 6798653) B6798653
theorem B5097775 : Blo 1340989 5097775 := bstep (se 1 (by rfl) ⟨3823331, by rfl⟩ : syracuseStep 5097775 = 7646663) B7646663
theorem B19614109 : Blo 1340989 19614109 := bstep (se 3 (by rfl) ⟨3677645, by rfl⟩ : syracuseStep 19614109 = 7355291) B7355291
theorem B6121889 : Blo 1340989 6121889 := bstep (se 2 (by rfl) ⟨2295708, by rfl⟩ : syracuseStep 6121889 = 4591417) B4591417
theorem B14510663 : Blo 1340989 14510663 := bstep (se 1 (by rfl) ⟨10882997, by rfl⟩ : syracuseStep 14510663 = 21765995) B21765995
theorem B3017321 : Blo 1340989 3017321 := bstep (se 2 (by rfl) ⟨1131495, by rfl⟩ : syracuseStep 3017321 = 2262991) B2262991
theorem B1911433 : Blo 1340989 1911433 := bstep (se 2 (by rfl) ⟨716787, by rfl⟩ : syracuseStep 1911433 = 1433575) B1433575
theorem B4836023 : Blo 1340989 4836023 := bstep (se 1 (by rfl) ⟨3627017, by rfl⟩ : syracuseStep 4836023 = 7254035) B7254035
theorem B15297335 : Blo 1340989 15297335 := bstep (se 1 (by rfl) ⟨11473001, by rfl⟩ : syracuseStep 15297335 = 22946003) B22946003
theorem B7637915 : Blo 1340989 7637915 := bstep (se 1 (by rfl) ⟨5728436, by rfl⟩ : syracuseStep 7637915 = 11456873) B11456873
theorem B1510303 : Blo 1340989 1510303 := bstep (se 1 (by rfl) ⟨1132727, by rfl⟩ : syracuseStep 1510303 = 2265455) B2265455
theorem B10882085 : Blo 1340989 10882085 := bstep (se 4 (by rfl) ⟨1020195, by rfl⟩ : syracuseStep 10882085 = 2040391) B2040391
theorem B2264105 : Blo 1340989 2264105 := bstep (se 2 (by rfl) ⟨849039, by rfl⟩ : syracuseStep 2264105 = 1698079) B1698079
theorem B1510447 : Blo 1340989 1510447 := bstep (se 1 (by rfl) ⟨1132835, by rfl⟩ : syracuseStep 1510447 = 2265671) B2265671
theorem B8719559 : Blo 1340989 8719559 := bstep (se 1 (by rfl) ⟨6539669, by rfl⟩ : syracuseStep 8719559 = 13079339) B13079339
theorem B3017951 : Blo 1340989 3017951 := bstep (se 1 (by rfl) ⟨2263463, by rfl⟩ : syracuseStep 3017951 = 4526927) B4526927
theorem B2264287 : Blo 1340989 2264287 := bstep (se 1 (by rfl) ⟨1698215, by rfl⟩ : syracuseStep 2264287 = 3396431) B3396431
theorem B1510735 : Blo 1340989 1510735 := bstep (se 1 (by rfl) ⟨1133051, by rfl⟩ : syracuseStep 1510735 = 2266103) B2266103
theorem B32664941 : Blo 1340989 32664941 := bstep (se 3 (by rfl) ⟨6124676, by rfl⟩ : syracuseStep 32664941 = 12249353) B12249353
theorem B95587697 : Blo 1340989 95587697 := bstep (se 2 (by rfl) ⟨35845386, by rfl⟩ : syracuseStep 95587697 = 71690773) B71690773
theorem B22932881 : Blo 1340989 22932881 := bstep (se 2 (by rfl) ⟨8599830, by rfl⟩ : syracuseStep 22932881 = 17199661) B17199661
theorem B3018167 : Blo 1340989 3018167 := bstep (se 1 (by rfl) ⟨2263625, by rfl⟩ : syracuseStep 3018167 = 4527251) B4527251
theorem B7253495 : Blo 1340989 7253495 := bstep (se 1 (by rfl) ⟨5440121, by rfl⟩ : syracuseStep 7253495 = 10880243) B10880243
theorem B8597015 : Blo 1340989 8597015 := bstep (se 1 (by rfl) ⟨6447761, by rfl⟩ : syracuseStep 8597015 = 12895523) B12895523
theorem B3395135 : Blo 1340989 3395135 := bstep (se 1 (by rfl) ⟨2546351, by rfl⟩ : syracuseStep 3395135 = 5092703) B5092703
theorem B3018347 : Blo 1340989 3018347 := bstep (se 1 (by rfl) ⟨2263760, by rfl⟩ : syracuseStep 3018347 = 4527521) B4527521
theorem B7646845 : Blo 1340989 7646845 := bstep (se 3 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 7646845 = 2867567) B2867567
theorem B2264719 : Blo 1340989 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B3059495 : Blo 1340989 3059495 := bstep (se 1 (by rfl) ⟨2294621, by rfl⟩ : syracuseStep 3059495 = 4589243) B4589243
theorem B3018617 : Blo 1340989 3018617 := bstep (se 2 (by rfl) ⟨1131981, by rfl⟩ : syracuseStep 3018617 = 2263963) B2263963
theorem B3821555 : Blo 1340989 3821555 := bstep (se 1 (by rfl) ⟨2866166, by rfl⟩ : syracuseStep 3821555 = 5732333) B5732333
theorem B6795251 : Blo 1340989 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B4526333 : Blo 1340989 4526333 := bstep (se 3 (by rfl) ⟨848687, by rfl⟩ : syracuseStep 4526333 = 1697375) B1697375
theorem B6795575 : Blo 1340989 6795575 := bstep (se 1 (by rfl) ⟨5096681, by rfl⟩ : syracuseStep 6795575 = 10193363) B10193363
theorem B2011529 : Blo 1340989 2011529 := bstep (se 2 (by rfl) ⟨754323, by rfl⟩ : syracuseStep 2011529 = 1508647) B1508647
theorem B4297175 : Blo 1340989 4297175 := bstep (se 1 (by rfl) ⟨3222881, by rfl⟩ : syracuseStep 4297175 = 6445763) B6445763
theorem B2011625 : Blo 1340989 2011625 := bstep (se 2 (by rfl) ⟨754359, by rfl⟩ : syracuseStep 2011625 = 1508719) B1508719
theorem B2011751 : Blo 1340989 2011751 := bstep (se 1 (by rfl) ⟨1508813, by rfl⟩ : syracuseStep 2011751 = 3017627) B3017627
theorem B2011883 : Blo 1340989 2011883 := bstep (se 1 (by rfl) ⟨1508912, by rfl⟩ : syracuseStep 2011883 = 3017825) B3017825
theorem B2011913 : Blo 1340989 2011913 := bstep (se 2 (by rfl) ⟨754467, by rfl⟩ : syracuseStep 2011913 = 1508935) B1508935
theorem B4526873 : Blo 1340989 4526873 := bstep (se 2 (by rfl) ⟨1697577, by rfl⟩ : syracuseStep 4526873 = 3395155) B3395155
theorem B21779225 : Blo 1340989 21779225 := bstep (se 2 (by rfl) ⟨8167209, by rfl⟩ : syracuseStep 21779225 = 16334419) B16334419
theorem B55087933 : Blo 1340989 55087933 := bstep (se 3 (by rfl) ⟨10328987, by rfl⟩ : syracuseStep 55087933 = 20657975) B20657975
theorem B2012015 : Blo 1340989 2012015 := bstep (se 1 (by rfl) ⟨1509011, by rfl⟩ : syracuseStep 2012015 = 3018023) B3018023
theorem B4527143 : Blo 1340989 4527143 := bstep (se 1 (by rfl) ⟨3395357, by rfl⟩ : syracuseStep 4527143 = 6790715) B6790715
theorem B2012267 : Blo 1340989 2012267 := bstep (se 1 (by rfl) ⟨1509200, by rfl⟩ : syracuseStep 2012267 = 3018401) B3018401
theorem B2012507 : Blo 1340989 2012507 := bstep (se 1 (by rfl) ⟨1509380, by rfl⟩ : syracuseStep 2012507 = 3018761) B3018761
theorem B13768055 : Blo 1340989 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B6796871 : Blo 1340989 6796871 := bstep (se 1 (by rfl) ⟨5097653, by rfl⟩ : syracuseStep 6796871 = 10195307) B10195307
theorem B1341039 : Blo 1340989 1341039 := bstep (se 1 (by rfl) ⟨1005779, by rfl⟩ : syracuseStep 1341039 = 2011559) B2011559
theorem B2012783 : Blo 1340989 2012783 := bstep (se 1 (by rfl) ⟨1509587, by rfl⟩ : syracuseStep 2012783 = 3019175) B3019175
theorem B1341095 : Blo 1340989 1341095 := bstep (se 1 (by rfl) ⟨1005821, by rfl⟩ : syracuseStep 1341095 = 2011643) B2011643
theorem B2012855 : Blo 1340989 2012855 := bstep (se 1 (by rfl) ⟨1509641, by rfl⟩ : syracuseStep 2012855 = 3019283) B3019283
theorem B3020471 : Blo 1340989 3020471 := bstep (se 1 (by rfl) ⟨2265353, by rfl⟩ : syracuseStep 3020471 = 4530707) B4530707
theorem B7255763 : Blo 1340989 7255763 := bstep (se 1 (by rfl) ⟨5441822, by rfl⟩ : syracuseStep 7255763 = 10883645) B10883645
theorem B2012891 : Blo 1340989 2012891 := bstep (se 1 (by rfl) ⟨1509668, by rfl⟩ : syracuseStep 2012891 = 3019337) B3019337
theorem B1341179 : Blo 1340989 1341179 := bstep (se 1 (by rfl) ⟨1005884, by rfl⟩ : syracuseStep 1341179 = 2011769) B2011769
theorem B3823355 : Blo 1340989 3823355 := bstep (se 1 (by rfl) ⟨2867516, by rfl⟩ : syracuseStep 3823355 = 5735033) B5735033
theorem B1341215 : Blo 1340989 1341215 := bstep (se 1 (by rfl) ⟨1005911, by rfl⟩ : syracuseStep 1341215 = 2011823) B2011823
theorem B4593455 : Blo 1340989 4593455 := bstep (se 1 (by rfl) ⟨3445091, by rfl⟩ : syracuseStep 4593455 = 6890183) B6890183
theorem B1341247 : Blo 1340989 1341247 := bstep (se 1 (by rfl) ⟨1005935, by rfl⟩ : syracuseStep 1341247 = 2011871) B2011871
theorem B2013065 : Blo 1340989 2013065 := bstep (se 2 (by rfl) ⟨754899, by rfl⟩ : syracuseStep 2013065 = 1509799) B1509799
theorem B6789095 : Blo 1340989 6789095 := bstep (se 1 (by rfl) ⟨5091821, by rfl⟩ : syracuseStep 6789095 = 10183643) B10183643
theorem B1341423 : Blo 1340989 1341423 := bstep (se 1 (by rfl) ⟨1006067, by rfl⟩ : syracuseStep 1341423 = 2012135) B2012135
theorem B2013167 : Blo 1340989 2013167 := bstep (se 1 (by rfl) ⟨1509875, by rfl⟩ : syracuseStep 2013167 = 3019751) B3019751
theorem B4356089 : Blo 1340989 4356089 := bstep (se 2 (by rfl) ⟨1633533, by rfl⟩ : syracuseStep 4356089 = 3267067) B3267067
theorem B4298777 : Blo 1340989 4298777 := bstep (se 2 (by rfl) ⟨1612041, by rfl⟩ : syracuseStep 4298777 = 3224083) B3224083
theorem B4528223 : Blo 1340989 4528223 := bstep (se 1 (by rfl) ⟨3396167, by rfl⟩ : syracuseStep 4528223 = 6792335) B6792335
theorem B3397727 : Blo 1340989 3397727 := bstep (se 1 (by rfl) ⟨2548295, by rfl⟩ : syracuseStep 3397727 = 5096591) B5096591
theorem B3061903 : Blo 1340989 3061903 := bstep (se 1 (by rfl) ⟨2296427, by rfl⟩ : syracuseStep 3061903 = 4592855) B4592855
theorem B1341595 : Blo 1340989 1341595 := bstep (se 1 (by rfl) ⟨1006196, by rfl⟩ : syracuseStep 1341595 = 2012393) B2012393
theorem B1341631 : Blo 1340989 1341631 := bstep (se 1 (by rfl) ⟨1006223, by rfl⟩ : syracuseStep 1341631 = 2012447) B2012447
theorem B7641287 : Blo 1340989 7641287 := bstep (se 1 (by rfl) ⟨5730965, by rfl⟩ : syracuseStep 7641287 = 11461931) B11461931
theorem B2013419 : Blo 1340989 2013419 := bstep (se 1 (by rfl) ⟨1510064, by rfl⟩ : syracuseStep 2013419 = 3020129) B3020129
theorem B2865415 : Blo 1340989 2865415 := bstep (se 1 (by rfl) ⟨2149061, by rfl⟩ : syracuseStep 2865415 = 4298123) B4298123
theorem B2013479 : Blo 1340989 2013479 := bstep (se 1 (by rfl) ⟨1510109, by rfl⟩ : syracuseStep 2013479 = 3020219) B3020219
theorem B2865449 : Blo 1340989 2865449 := bstep (se 2 (by rfl) ⟨1074543, by rfl⟩ : syracuseStep 2865449 = 2149087) B2149087
theorem B5093675 : Blo 1340989 5093675 := bstep (se 1 (by rfl) ⟨3820256, by rfl⟩ : syracuseStep 5093675 = 7640513) B7640513
theorem B1341743 : Blo 1340989 1341743 := bstep (se 1 (by rfl) ⟨1006307, by rfl⟩ : syracuseStep 1341743 = 2012615) B2012615
theorem B5093705 : Blo 1340989 5093705 := bstep (se 2 (by rfl) ⟨1910139, by rfl⟩ : syracuseStep 5093705 = 3820279) B3820279
theorem B2013563 : Blo 1340989 2013563 := bstep (se 1 (by rfl) ⟨1510172, by rfl⟩ : syracuseStep 2013563 = 3020345) B3020345
theorem B6797843 : Blo 1340989 6797843 := bstep (se 1 (by rfl) ⟨5098382, by rfl⟩ : syracuseStep 6797843 = 10196765) B10196765
theorem B1341979 : Blo 1340989 1341979 := bstep (se 1 (by rfl) ⟨1006484, by rfl⟩ : syracuseStep 1341979 = 2012969) B2012969
theorem B1341983 : Blo 1340989 1341983 := bstep (se 1 (by rfl) ⟨1006487, by rfl⟩ : syracuseStep 1341983 = 2012975) B2012975
theorem B2013833 : Blo 1340989 2013833 := bstep (se 2 (by rfl) ⟨755187, by rfl⟩ : syracuseStep 2013833 = 1510375) B1510375
theorem B5733017 : Blo 1340989 5733017 := bstep (se 2 (by rfl) ⟨2149881, by rfl⟩ : syracuseStep 5733017 = 4299763) B4299763
theorem B2014007 : Blo 1340989 2014007 := bstep (se 1 (by rfl) ⟨1510505, by rfl⟩ : syracuseStep 2014007 = 3021011) B3021011
theorem B4528979 : Blo 1340989 4528979 := bstep (se 1 (by rfl) ⟨3396734, by rfl⟩ : syracuseStep 4528979 = 6793469) B6793469
theorem B1342299 : Blo 1340989 1342299 := bstep (se 1 (by rfl) ⟨1006724, by rfl⟩ : syracuseStep 1342299 = 2013449) B2013449
theorem B2014043 : Blo 1340989 2014043 := bstep (se 1 (by rfl) ⟨1510532, by rfl⟩ : syracuseStep 2014043 = 3021065) B3021065
theorem B3021659 : Blo 1340989 3021659 := bstep (se 1 (by rfl) ⟨2266244, by rfl⟩ : syracuseStep 3021659 = 4532489) B4532489
theorem B1342367 : Blo 1340989 1342367 := bstep (se 1 (by rfl) ⟨1006775, by rfl⟩ : syracuseStep 1342367 = 2013551) B2013551
theorem B2014187 : Blo 1340989 2014187 := bstep (se 1 (by rfl) ⟨1510640, by rfl⟩ : syracuseStep 2014187 = 3021281) B3021281
theorem B1342511 : Blo 1340989 1342511 := bstep (se 1 (by rfl) ⟨1006883, by rfl⟩ : syracuseStep 1342511 = 2013767) B2013767
theorem B12893255 : Blo 1340989 12893255 := bstep (se 1 (by rfl) ⟨9669941, by rfl⟩ : syracuseStep 12893255 = 19339883) B19339883
theorem B1342535 : Blo 1340989 1342535 := bstep (se 1 (by rfl) ⟨1006901, by rfl⟩ : syracuseStep 1342535 = 2013803) B2013803
theorem B48397429 : Blo 1340989 48397429 := bstep (se 5 (by rfl) ⟨2268629, by rfl⟩ : syracuseStep 48397429 = 4537259) B4537259
theorem B4299905 : Blo 1340989 4299905 := bstep (se 2 (by rfl) ⟨1612464, by rfl⟩ : syracuseStep 4299905 = 3224929) B3224929
theorem B2014391 : Blo 1340989 2014391 := bstep (se 1 (by rfl) ⟨1510793, by rfl⟩ : syracuseStep 2014391 = 3021587) B3021587
theorem B1342687 : Blo 1340989 1342687 := bstep (se 1 (by rfl) ⟨1007015, by rfl⟩ : syracuseStep 1342687 = 2014031) B2014031
theorem B4529519 : Blo 1340989 4529519 := bstep (se 1 (by rfl) ⟨3397139, by rfl⟩ : syracuseStep 4529519 = 6794279) B6794279
theorem B3399023 : Blo 1340989 3399023 := bstep (se 1 (by rfl) ⟨2549267, by rfl⟩ : syracuseStep 3399023 = 5098535) B5098535
theorem B8601061 : Blo 1340989 8601061 := bstep (se 4 (by rfl) ⟨806349, by rfl⟩ : syracuseStep 8601061 = 1612699) B1612699
theorem B1342951 : Blo 1340989 1342951 := bstep (se 1 (by rfl) ⟨1007213, by rfl⟩ : syracuseStep 1342951 = 2014427) B2014427
theorem B4529897 : Blo 1340989 4529897 := bstep (se 2 (by rfl) ⟨1698711, by rfl⟩ : syracuseStep 4529897 = 3397423) B3397423
theorem B32661251 : Blo 1340989 32661251 := bstep (se 1 (by rfl) ⟨24495938, by rfl⟩ : syracuseStep 32661251 = 48991877) B48991877
theorem B278822807 : Blo 1340989 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B24494033 : Blo 1340989 24494033 := bstep (se 2 (by rfl) ⟨9185262, by rfl⟩ : syracuseStep 24494033 = 18370525) B18370525
theorem B4530383 : Blo 1340989 4530383 := bstep (se 1 (by rfl) ⟨3397787, by rfl⟩ : syracuseStep 4530383 = 6795575) B6795575
theorem B2867807 : Blo 1340989 2867807 := bstep (se 1 (by rfl) ⟨2150855, by rfl⟩ : syracuseStep 2867807 = 4301711) B4301711
theorem B2548577 : Blo 1340989 2548577 := bstep (se 2 (by rfl) ⟨955716, by rfl⟩ : syracuseStep 2548577 = 1911433) B1911433
theorem B5096303 : Blo 1340989 5096303 := bstep (se 1 (by rfl) ⟨3822227, by rfl⟩ : syracuseStep 5096303 = 7644455) B7644455
theorem B73466797 : Blo 1340989 73466797 := bstep (se 3 (by rfl) ⟨13775024, by rfl⟩ : syracuseStep 73466797 = 27550049) B27550049
theorem B4531247 : Blo 1340989 4531247 := bstep (se 1 (by rfl) ⟨3398435, by rfl⟩ : syracuseStep 4531247 = 6796871) B6796871
theorem B73450577 : Blo 1340989 73450577 := bstep (se 2 (by rfl) ⟨27543966, by rfl⟩ : syracuseStep 73450577 = 55087933) B55087933
theorem B2548903 : Blo 1340989 2548903 := bstep (se 1 (by rfl) ⟨1911677, by rfl⟩ : syracuseStep 2548903 = 3823355) B3823355
theorem B9176345 : Blo 1340989 9176345 := bstep (se 2 (by rfl) ⟨3441129, by rfl⟩ : syracuseStep 9176345 = 6882259) B6882259
theorem B15295877 : Blo 1340989 15295877 := bstep (se 4 (by rfl) ⟨1433988, by rfl⟩ : syracuseStep 15295877 = 2867977) B2867977
theorem B64529905 : Blo 1340989 64529905 := bstep (se 2 (by rfl) ⟨24198714, by rfl⟩ : syracuseStep 64529905 = 48397429) B48397429
theorem B1910299 : Blo 1340989 1910299 := bstep (se 1 (by rfl) ⟨1432724, by rfl⟩ : syracuseStep 1910299 = 2865449) B2865449
theorem B4081259 : Blo 1340989 4081259 := bstep (se 1 (by rfl) ⟨3060944, by rfl⟩ : syracuseStep 4081259 = 6121889) B6121889
theorem B4531895 : Blo 1340989 4531895 := bstep (se 1 (by rfl) ⟨3398921, by rfl⟩ : syracuseStep 4531895 = 6797843) B6797843
theorem B19334857 : Blo 1340989 19334857 := bstep (se 2 (by rfl) ⟨7250571, by rfl⟩ : syracuseStep 19334857 = 14501143) B14501143
theorem B1509403 : Blo 1340989 1509403 := bstep (se 1 (by rfl) ⟨1132052, by rfl⟩ : syracuseStep 1509403 = 2264105) B2264105
theorem B8595503 : Blo 1340989 8595503 := bstep (se 1 (by rfl) ⟨6446627, by rfl⟩ : syracuseStep 8595503 = 12893255) B12893255
theorem B4530167 : Blo 1340989 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B21776627 : Blo 1340989 21776627 := bstep (se 1 (by rfl) ⟨16332470, by rfl⟩ : syracuseStep 21776627 = 32664941) B32664941
theorem B15288587 : Blo 1340989 15288587 := bstep (se 1 (by rfl) ⟨11466440, by rfl⟩ : syracuseStep 15288587 = 22932881) B22932881
theorem B4835663 : Blo 1340989 4835663 := bstep (se 1 (by rfl) ⟨3626747, by rfl⟩ : syracuseStep 4835663 = 7253495) B7253495
theorem B2263423 : Blo 1340989 2263423 := bstep (se 1 (by rfl) ⟨1697567, by rfl⟩ : syracuseStep 2263423 = 3395135) B3395135
theorem B65317421 : Blo 1340989 65317421 := bstep (se 3 (by rfl) ⟨12247016, by rfl⟩ : syracuseStep 65317421 = 24494033) B24494033
theorem B29018893 : Blo 1340989 29018893 := bstep (se 3 (by rfl) ⟨5441042, by rfl⟩ : syracuseStep 29018893 = 10882085) B10882085
theorem B3017555 : Blo 1340989 3017555 := bstep (se 1 (by rfl) ⟨2263166, by rfl⟩ : syracuseStep 3017555 = 4526333) B4526333
theorem B4082537 : Blo 1340989 4082537 := bstep (se 2 (by rfl) ⟨1530951, by rfl⟩ : syracuseStep 4082537 = 3061903) B3061903
theorem B3820553 : Blo 1340989 3820553 := bstep (se 2 (by rfl) ⟨1432707, by rfl⟩ : syracuseStep 3820553 = 2865415) B2865415
theorem B3017915 : Blo 1340989 3017915 := bstep (se 1 (by rfl) ⟨2263436, by rfl⟩ : syracuseStep 3017915 = 4526873) B4526873
theorem B14519483 : Blo 1340989 14519483 := bstep (se 1 (by rfl) ⟨10889612, by rfl⟩ : syracuseStep 14519483 = 21779225) B21779225
theorem B26152145 : Blo 1340989 26152145 := bstep (se 2 (by rfl) ⟨9807054, by rfl⟩ : syracuseStep 26152145 = 19614109) B19614109
theorem B3018095 : Blo 1340989 3018095 := bstep (se 1 (by rfl) ⟨2263571, by rfl⟩ : syracuseStep 3018095 = 4527143) B4527143
theorem B9178703 : Blo 1340989 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B7253687 : Blo 1340989 7253687 := bstep (se 1 (by rfl) ⟨5440265, by rfl⟩ : syracuseStep 7253687 = 10880531) B10880531
theorem B4837175 : Blo 1340989 4837175 := bstep (se 1 (by rfl) ⟨3627881, by rfl⟩ : syracuseStep 4837175 = 7255763) B7255763
theorem B4526063 : Blo 1340989 4526063 := bstep (se 1 (by rfl) ⟨3394547, by rfl⟩ : syracuseStep 4526063 = 6789095) B6789095
theorem B2904059 : Blo 1340989 2904059 := bstep (se 1 (by rfl) ⟨2178044, by rfl⟩ : syracuseStep 2904059 = 4356089) B4356089
theorem B3018815 : Blo 1340989 3018815 := bstep (se 1 (by rfl) ⟨2264111, by rfl⟩ : syracuseStep 3018815 = 4528223) B4528223
theorem B2265151 : Blo 1340989 2265151 := bstep (se 1 (by rfl) ⟨1698863, by rfl⟩ : syracuseStep 2265151 = 3397727) B3397727
theorem B7647371 : Blo 1340989 7647371 := bstep (se 1 (by rfl) ⟨5735528, by rfl⟩ : syracuseStep 7647371 = 11471057) B11471057
theorem B3395783 : Blo 1340989 3395783 := bstep (se 1 (by rfl) ⟨2546837, by rfl⟩ : syracuseStep 3395783 = 5093675) B5093675
theorem B3395803 : Blo 1340989 3395803 := bstep (se 1 (by rfl) ⟨2546852, by rfl⟩ : syracuseStep 3395803 = 5093705) B5093705
theorem B3019049 : Blo 1340989 3019049 := bstep (se 2 (by rfl) ⟨1132143, by rfl⟩ : syracuseStep 3019049 = 2264287) B2264287
theorem B2011547 : Blo 1340989 2011547 := bstep (se 1 (by rfl) ⟨1508660, by rfl⟩ : syracuseStep 2011547 = 3017321) B3017321
theorem B3822011 : Blo 1340989 3822011 := bstep (se 1 (by rfl) ⟨2866508, by rfl⟩ : syracuseStep 3822011 = 5733017) B5733017
theorem B3224015 : Blo 1340989 3224015 := bstep (se 1 (by rfl) ⟨2418011, by rfl⟩ : syracuseStep 3224015 = 4836023) B4836023
theorem B3019319 : Blo 1340989 3019319 := bstep (se 1 (by rfl) ⟨2264489, by rfl⟩ : syracuseStep 3019319 = 4528979) B4528979
theorem B5091943 : Blo 1340989 5091943 := bstep (se 1 (by rfl) ⟨3818957, by rfl⟩ : syracuseStep 5091943 = 7637915) B7637915
theorem B5813039 : Blo 1340989 5813039 := bstep (se 1 (by rfl) ⟨4359779, by rfl⟩ : syracuseStep 5813039 = 8719559) B8719559
theorem B2011967 : Blo 1340989 2011967 := bstep (se 1 (by rfl) ⟨1508975, by rfl⟩ : syracuseStep 2011967 = 3017951) B3017951
theorem B10195793 : Blo 1340989 10195793 := bstep (se 2 (by rfl) ⟨3823422, by rfl⟩ : syracuseStep 10195793 = 7646845) B7646845
theorem B3019625 : Blo 1340989 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B3019679 : Blo 1340989 3019679 := bstep (se 1 (by rfl) ⟨2264759, by rfl⟩ : syracuseStep 3019679 = 4529519) B4529519
theorem B2266015 : Blo 1340989 2266015 := bstep (se 1 (by rfl) ⟨1699511, by rfl⟩ : syracuseStep 2266015 = 3399023) B3399023
theorem B2012111 : Blo 1340989 2012111 := bstep (se 1 (by rfl) ⟨1509083, by rfl⟩ : syracuseStep 2012111 = 3018167) B3018167
theorem B2012153 : Blo 1340989 2012153 := bstep (se 2 (by rfl) ⟨754557, by rfl⟩ : syracuseStep 2012153 = 1509115) B1509115
theorem B5731343 : Blo 1340989 5731343 := bstep (se 1 (by rfl) ⟨4298507, by rfl⟩ : syracuseStep 5731343 = 8597015) B8597015
theorem B2012201 : Blo 1340989 2012201 := bstep (se 2 (by rfl) ⟨754575, by rfl⟩ : syracuseStep 2012201 = 1509151) B1509151
theorem B2012231 : Blo 1340989 2012231 := bstep (se 1 (by rfl) ⟨1509173, by rfl⟩ : syracuseStep 2012231 = 3018347) B3018347
theorem B3019931 : Blo 1340989 3019931 := bstep (se 1 (by rfl) ⟨2264948, by rfl⟩ : syracuseStep 3019931 = 4529897) B4529897
theorem B2012411 : Blo 1340989 2012411 := bstep (se 1 (by rfl) ⟨1509308, by rfl⟩ : syracuseStep 2012411 = 3018617) B3018617
theorem B185881871 : Blo 1340989 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B11457935 : Blo 1340989 11457935 := bstep (se 1 (by rfl) ⟨8593451, by rfl⟩ : syracuseStep 11457935 = 17186903) B17186903
theorem B1341019 : Blo 1340989 1341019 := bstep (se 1 (by rfl) ⟨1005764, by rfl⟩ : syracuseStep 1341019 = 2011529) B2011529
theorem B3397241 : Blo 1340989 3397241 := bstep (se 2 (by rfl) ⟨1273965, by rfl⟩ : syracuseStep 3397241 = 2547931) B2547931
theorem B2864783 : Blo 1340989 2864783 := bstep (se 1 (by rfl) ⟨2148587, by rfl⟩ : syracuseStep 2864783 = 4297175) B4297175
theorem B1341083 : Blo 1340989 1341083 := bstep (se 1 (by rfl) ⟨1005812, by rfl⟩ : syracuseStep 1341083 = 2011625) B2011625
theorem B3020507 : Blo 1340989 3020507 := bstep (se 1 (by rfl) ⟨2265380, by rfl⟩ : syracuseStep 3020507 = 4530761) B4530761
theorem B6797033 : Blo 1340989 6797033 := bstep (se 2 (by rfl) ⟨2548887, by rfl⟩ : syracuseStep 6797033 = 5097775) B5097775
theorem B1341167 : Blo 1340989 1341167 := bstep (se 1 (by rfl) ⟨1005875, by rfl⟩ : syracuseStep 1341167 = 2011751) B2011751
theorem B1341255 : Blo 1340989 1341255 := bstep (se 1 (by rfl) ⟨1005941, by rfl⟩ : syracuseStep 1341255 = 2011883) B2011883
theorem B3020615 : Blo 1340989 3020615 := bstep (se 1 (by rfl) ⟨2265461, by rfl⟩ : syracuseStep 3020615 = 4530923) B4530923
theorem B4839239 : Blo 1340989 4839239 := bstep (se 1 (by rfl) ⟨3629429, by rfl⟩ : syracuseStep 4839239 = 7258859) B7258859
theorem B1341275 : Blo 1340989 1341275 := bstep (se 1 (by rfl) ⟨1005956, by rfl⟩ : syracuseStep 1341275 = 2011913) B2011913
theorem B1341343 : Blo 1340989 1341343 := bstep (se 1 (by rfl) ⟨1006007, by rfl⟩ : syracuseStep 1341343 = 2012015) B2012015
theorem B1341511 : Blo 1340989 1341511 := bstep (se 1 (by rfl) ⟨1006133, by rfl⟩ : syracuseStep 1341511 = 2012267) B2012267
theorem B1341671 : Blo 1340989 1341671 := bstep (se 1 (by rfl) ⟨1006253, by rfl⟩ : syracuseStep 1341671 = 2012507) B2012507
theorem B6789419 : Blo 1340989 6789419 := bstep (se 1 (by rfl) ⟨5092064, by rfl⟩ : syracuseStep 6789419 = 10184129) B10184129
theorem B1341855 : Blo 1340989 1341855 := bstep (se 1 (by rfl) ⟨1006391, by rfl⟩ : syracuseStep 1341855 = 2012783) B2012783
theorem B1341903 : Blo 1340989 1341903 := bstep (se 1 (by rfl) ⟨1006427, by rfl⟩ : syracuseStep 1341903 = 2012855) B2012855
theorem B2013647 : Blo 1340989 2013647 := bstep (se 1 (by rfl) ⟨1510235, by rfl⟩ : syracuseStep 2013647 = 3020471) B3020471
theorem B1341927 : Blo 1340989 1341927 := bstep (se 1 (by rfl) ⟨1006445, by rfl⟩ : syracuseStep 1341927 = 2012891) B2012891
theorem B3062303 : Blo 1340989 3062303 := bstep (se 1 (by rfl) ⟨2296727, by rfl⟩ : syracuseStep 3062303 = 4593455) B4593455
theorem B2013737 : Blo 1340989 2013737 := bstep (se 2 (by rfl) ⟨755151, by rfl⟩ : syracuseStep 2013737 = 1510303) B1510303
theorem B1342043 : Blo 1340989 1342043 := bstep (se 1 (by rfl) ⟨1006532, by rfl⟩ : syracuseStep 1342043 = 2013065) B2013065
theorem B1342111 : Blo 1340989 1342111 := bstep (se 1 (by rfl) ⟨1006583, by rfl⟩ : syracuseStep 1342111 = 2013167) B2013167
theorem B2865851 : Blo 1340989 2865851 := bstep (se 1 (by rfl) ⟨2149388, by rfl⟩ : syracuseStep 2865851 = 4298777) B4298777
theorem B2013929 : Blo 1340989 2013929 := bstep (se 2 (by rfl) ⟨755223, by rfl⟩ : syracuseStep 2013929 = 1510447) B1510447
theorem B5094191 : Blo 1340989 5094191 := bstep (se 1 (by rfl) ⟨3820643, by rfl⟩ : syracuseStep 5094191 = 7641287) B7641287
theorem B3021623 : Blo 1340989 3021623 := bstep (se 1 (by rfl) ⟨2266217, by rfl⟩ : syracuseStep 3021623 = 4532435) B4532435
theorem B1342279 : Blo 1340989 1342279 := bstep (se 1 (by rfl) ⟨1006709, by rfl⟩ : syracuseStep 1342279 = 2013419) B2013419
theorem B1342319 : Blo 1340989 1342319 := bstep (se 1 (by rfl) ⟨1006739, by rfl⟩ : syracuseStep 1342319 = 2013479) B2013479
theorem B1342375 : Blo 1340989 1342375 := bstep (se 1 (by rfl) ⟨1006781, by rfl⟩ : syracuseStep 1342375 = 2013563) B2013563
theorem B9673775 : Blo 1340989 9673775 := bstep (se 1 (by rfl) ⟨7255331, by rfl⟩ : syracuseStep 9673775 = 14510663) B14510663
theorem B1342555 : Blo 1340989 1342555 := bstep (se 1 (by rfl) ⟨1006916, by rfl⟩ : syracuseStep 1342555 = 2013833) B2013833
theorem B2014313 : Blo 1340989 2014313 := bstep (se 2 (by rfl) ⟨755367, by rfl⟩ : syracuseStep 2014313 = 1510735) B1510735
theorem B1342671 : Blo 1340989 1342671 := bstep (se 1 (by rfl) ⟨1007003, by rfl⟩ : syracuseStep 1342671 = 2014007) B2014007
theorem B10198223 : Blo 1340989 10198223 := bstep (se 1 (by rfl) ⟨7648667, by rfl⟩ : syracuseStep 10198223 = 15297335) B15297335
theorem B1342695 : Blo 1340989 1342695 := bstep (se 1 (by rfl) ⟨1007021, by rfl⟩ : syracuseStep 1342695 = 2014043) B2014043
theorem B2014439 : Blo 1340989 2014439 := bstep (se 1 (by rfl) ⟨1510829, by rfl⟩ : syracuseStep 2014439 = 3021659) B3021659
theorem B7453949 : Blo 1340989 7453949 := bstep (se 3 (by rfl) ⟨1397615, by rfl⟩ : syracuseStep 7453949 = 2795231) B2795231
theorem B11468081 : Blo 1340989 11468081 := bstep (se 2 (by rfl) ⟨4300530, by rfl⟩ : syracuseStep 11468081 = 8601061) B8601061
theorem B1342791 : Blo 1340989 1342791 := bstep (se 1 (by rfl) ⟨1007093, by rfl⟩ : syracuseStep 1342791 = 2014187) B2014187
theorem B2866603 : Blo 1340989 2866603 := bstep (se 1 (by rfl) ⟨2149952, by rfl⟩ : syracuseStep 2866603 = 4299905) B4299905
theorem B1342927 : Blo 1340989 1342927 := bstep (se 1 (by rfl) ⟨1007195, by rfl⟩ : syracuseStep 1342927 = 2014391) B2014391
theorem B63725131 : Blo 1340989 63725131 := bstep (se 1 (by rfl) ⟨47793848, by rfl⟩ : syracuseStep 63725131 = 95587697) B95587697
theorem B21774167 : Blo 1340989 21774167 := bstep (se 1 (by rfl) ⟨16330625, by rfl⟩ : syracuseStep 21774167 = 32661251) B32661251
theorem B2039663 : Blo 1340989 2039663 := bstep (se 1 (by rfl) ⟨1529747, by rfl⟩ : syracuseStep 2039663 = 3059495) B3059495
theorem B2547703 : Blo 1340989 2547703 := bstep (se 1 (by rfl) ⟨1910777, by rfl⟩ : syracuseStep 2547703 = 3821555) B3821555
theorem B2548007 : Blo 1340989 2548007 := bstep (se 1 (by rfl) ⟨1911005, by rfl⟩ : syracuseStep 2548007 = 3822011) B3822011
theorem B3875359 : Blo 1340989 3875359 := bstep (se 1 (by rfl) ⟨2906519, by rfl⟩ : syracuseStep 3875359 = 5813039) B5813039
theorem B123921247 : Blo 1340989 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B38691857 : Blo 1340989 38691857 := bstep (se 2 (by rfl) ⟨14509446, by rfl⟩ : syracuseStep 38691857 = 29018893) B29018893
theorem B2720839 : Blo 1340989 2720839 := bstep (se 1 (by rfl) ⟨2040629, by rfl⟩ : syracuseStep 2720839 = 4081259) B4081259
theorem B1909855 : Blo 1340989 1909855 := bstep (se 1 (by rfl) ⟨1432391, by rfl⟩ : syracuseStep 1909855 = 2864783) B2864783
theorem B4531355 : Blo 1340989 4531355 := bstep (se 1 (by rfl) ⟨3398516, by rfl⟩ : syracuseStep 4531355 = 6797033) B6797033
theorem B14517751 : Blo 1340989 14517751 := bstep (se 1 (by rfl) ⟨10888313, by rfl⟩ : syracuseStep 14517751 = 21776627) B21776627
theorem B10192391 : Blo 1340989 10192391 := bstep (se 1 (by rfl) ⟨7644293, by rfl⟩ : syracuseStep 10192391 = 15288587) B15288587
theorem B2041535 : Blo 1340989 2041535 := bstep (se 1 (by rfl) ⟨1531151, by rfl⟩ : syracuseStep 2041535 = 3062303) B3062303
theorem B1910567 : Blo 1340989 1910567 := bstep (se 1 (by rfl) ⟨1432925, by rfl⟩ : syracuseStep 1910567 = 2865851) B2865851
theorem B2721691 : Blo 1340989 2721691 := bstep (se 1 (by rfl) ⟨2041268, by rfl⟩ : syracuseStep 2721691 = 4082537) B4082537
theorem B6449183 : Blo 1340989 6449183 := bstep (se 1 (by rfl) ⟨4836887, by rfl⟩ : syracuseStep 6449183 = 9673775) B9673775
theorem B17434763 : Blo 1340989 17434763 := bstep (se 1 (by rfl) ⟨13076072, by rfl⟩ : syracuseStep 17434763 = 26152145) B26152145
theorem B7645387 : Blo 1340989 7645387 := bstep (se 1 (by rfl) ⟨5734040, by rfl⟩ : syracuseStep 7645387 = 11468081) B11468081
theorem B4835791 : Blo 1340989 4835791 := bstep (se 1 (by rfl) ⟨3626843, by rfl⟩ : syracuseStep 4835791 = 7253687) B7253687
theorem B7744157 : Blo 1340989 7744157 := bstep (se 3 (by rfl) ⟨1452029, by rfl⟩ : syracuseStep 7744157 = 2904059) B2904059
theorem B3017375 : Blo 1340989 3017375 := bstep (se 1 (by rfl) ⟨2263031, by rfl⟩ : syracuseStep 3017375 = 4526063) B4526063
theorem B5098247 : Blo 1340989 5098247 := bstep (se 1 (by rfl) ⟨3823685, by rfl⟩ : syracuseStep 5098247 = 7647371) B7647371
theorem B2263855 : Blo 1340989 2263855 := bstep (se 1 (by rfl) ⟨1697891, by rfl⟩ : syracuseStep 2263855 = 3395783) B3395783
theorem B2149343 : Blo 1340989 2149343 := bstep (se 1 (by rfl) ⟨1612007, by rfl⟩ : syracuseStep 2149343 = 3224015) B3224015
theorem B1911871 : Blo 1340989 1911871 := bstep (se 1 (by rfl) ⟨1433903, by rfl⟩ : syracuseStep 1911871 = 2867807) B2867807
theorem B3017897 : Blo 1340989 3017897 := bstep (se 2 (by rfl) ⟨1131711, by rfl⟩ : syracuseStep 3017897 = 2263423) B2263423
theorem B1699051 : Blo 1340989 1699051 := bstep (se 1 (by rfl) ⟨1274288, by rfl⟩ : syracuseStep 1699051 = 2548577) B2548577
theorem B3820895 : Blo 1340989 3820895 := bstep (se 1 (by rfl) ⟨2865671, by rfl⟩ : syracuseStep 3820895 = 5731343) B5731343
theorem B48967051 : Blo 1340989 48967051 := bstep (se 1 (by rfl) ⟨36725288, by rfl⟩ : syracuseStep 48967051 = 73450577) B73450577
theorem B7638623 : Blo 1340989 7638623 := bstep (se 1 (by rfl) ⟨5728967, by rfl⟩ : syracuseStep 7638623 = 11457935) B11457935
theorem B2264827 : Blo 1340989 2264827 := bstep (se 1 (by rfl) ⟨1698620, by rfl⟩ : syracuseStep 2264827 = 3397241) B3397241
theorem B97955729 : Blo 1340989 97955729 := bstep (se 2 (by rfl) ⟨36733398, by rfl⟩ : syracuseStep 97955729 = 73466797) B73466797
theorem B5730335 : Blo 1340989 5730335 := bstep (se 1 (by rfl) ⟨4297751, by rfl⟩ : syracuseStep 5730335 = 8595503) B8595503
theorem B4526279 : Blo 1340989 4526279 := bstep (se 1 (by rfl) ⟨3394709, by rfl⟩ : syracuseStep 4526279 = 6789419) B6789419
theorem B3223775 : Blo 1340989 3223775 := bstep (se 1 (by rfl) ⟨2417831, by rfl⟩ : syracuseStep 3223775 = 4835663) B4835663
theorem B43544947 : Blo 1340989 43544947 := bstep (se 1 (by rfl) ⟨32658710, by rfl⟩ : syracuseStep 43544947 = 65317421) B65317421
theorem B3396127 : Blo 1340989 3396127 := bstep (se 1 (by rfl) ⟨2547095, by rfl⟩ : syracuseStep 3396127 = 5094191) B5094191
theorem B2011703 : Blo 1340989 2011703 := bstep (se 1 (by rfl) ⟨1508777, by rfl⟩ : syracuseStep 2011703 = 3017555) B3017555
theorem B3822137 : Blo 1340989 3822137 := bstep (se 2 (by rfl) ⟨1433301, by rfl⟩ : syracuseStep 3822137 = 2866603) B2866603
theorem B2011943 : Blo 1340989 2011943 := bstep (se 1 (by rfl) ⟨1508957, by rfl⟩ : syracuseStep 2011943 = 3017915) B3017915
theorem B9679655 : Blo 1340989 9679655 := bstep (se 1 (by rfl) ⟨7259741, by rfl⟩ : syracuseStep 9679655 = 14519483) B14519483
theorem B2012063 : Blo 1340989 2012063 := bstep (se 1 (by rfl) ⟨1509047, by rfl⟩ : syracuseStep 2012063 = 3018095) B3018095
theorem B3224783 : Blo 1340989 3224783 := bstep (se 1 (by rfl) ⟨2418587, by rfl⟩ : syracuseStep 3224783 = 4837175) B4837175
theorem B79508789 : Blo 1340989 79508789 := bstep (se 5 (by rfl) ⟨3726974, by rfl⟩ : syracuseStep 79508789 = 7453949) B7453949
theorem B3396937 : Blo 1340989 3396937 := bstep (se 2 (by rfl) ⟨1273851, by rfl⟩ : syracuseStep 3396937 = 2547703) B2547703
theorem B3020111 : Blo 1340989 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B2012537 : Blo 1340989 2012537 := bstep (se 2 (by rfl) ⟨754701, by rfl⟩ : syracuseStep 2012537 = 1509403) B1509403
theorem B2012543 : Blo 1340989 2012543 := bstep (se 1 (by rfl) ⟨1509407, by rfl⟩ : syracuseStep 2012543 = 3018815) B3018815
theorem B3020201 : Blo 1340989 3020201 := bstep (se 2 (by rfl) ⟨1132575, by rfl⟩ : syracuseStep 3020201 = 2265151) B2265151
theorem B3020255 : Blo 1340989 3020255 := bstep (se 1 (by rfl) ⟨2265191, by rfl⟩ : syracuseStep 3020255 = 4530383) B4530383
theorem B2012699 : Blo 1340989 2012699 := bstep (se 1 (by rfl) ⟨1509524, by rfl⟩ : syracuseStep 2012699 = 3019049) B3019049
theorem B1341031 : Blo 1340989 1341031 := bstep (se 1 (by rfl) ⟨1005773, by rfl⟩ : syracuseStep 1341031 = 2011547) B2011547
theorem B4527737 : Blo 1340989 4527737 := bstep (se 2 (by rfl) ⟨1697901, by rfl⟩ : syracuseStep 4527737 = 3395803) B3395803
theorem B2012879 : Blo 1340989 2012879 := bstep (se 1 (by rfl) ⟨1509659, by rfl⟩ : syracuseStep 2012879 = 3019319) B3019319
theorem B1341311 : Blo 1340989 1341311 := bstep (se 1 (by rfl) ⟨1005983, by rfl⟩ : syracuseStep 1341311 = 2011967) B2011967
theorem B6797195 : Blo 1340989 6797195 := bstep (se 1 (by rfl) ⟨5097896, by rfl⟩ : syracuseStep 6797195 = 10195793) B10195793
theorem B2013083 : Blo 1340989 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B3397535 : Blo 1340989 3397535 := bstep (se 1 (by rfl) ⟨2548151, by rfl⟩ : syracuseStep 3397535 = 5096303) B5096303
theorem B2013119 : Blo 1340989 2013119 := bstep (se 1 (by rfl) ⟨1509839, by rfl⟩ : syracuseStep 2013119 = 3019679) B3019679
theorem B1341407 : Blo 1340989 1341407 := bstep (se 1 (by rfl) ⟨1006055, by rfl⟩ : syracuseStep 1341407 = 2012111) B2012111
theorem B1341435 : Blo 1340989 1341435 := bstep (se 1 (by rfl) ⟨1006076, by rfl⟩ : syracuseStep 1341435 = 2012153) B2012153
theorem B1341467 : Blo 1340989 1341467 := bstep (se 1 (by rfl) ⟨1006100, by rfl⟩ : syracuseStep 1341467 = 2012201) B2012201
theorem B3020831 : Blo 1340989 3020831 := bstep (se 1 (by rfl) ⟨2265623, by rfl⟩ : syracuseStep 3020831 = 4531247) B4531247
theorem B1341487 : Blo 1340989 1341487 := bstep (se 1 (by rfl) ⟨1006115, by rfl⟩ : syracuseStep 1341487 = 2012231) B2012231
theorem B2013287 : Blo 1340989 2013287 := bstep (se 1 (by rfl) ⟨1509965, by rfl⟩ : syracuseStep 2013287 = 3019931) B3019931
theorem B6789257 : Blo 1340989 6789257 := bstep (se 2 (by rfl) ⟨2545971, by rfl⟩ : syracuseStep 6789257 = 5091943) B5091943
theorem B1341607 : Blo 1340989 1341607 := bstep (se 1 (by rfl) ⟨1006205, by rfl⟩ : syracuseStep 1341607 = 2012411) B2012411
theorem B6117563 : Blo 1340989 6117563 := bstep (se 1 (by rfl) ⟨4588172, by rfl⟩ : syracuseStep 6117563 = 9176345) B9176345
theorem B10197251 : Blo 1340989 10197251 := bstep (se 1 (by rfl) ⟨7647938, by rfl⟩ : syracuseStep 10197251 = 15295877) B15295877
theorem B3021263 : Blo 1340989 3021263 := bstep (se 1 (by rfl) ⟨2265947, by rfl⟩ : syracuseStep 3021263 = 4531895) B4531895
theorem B2013671 : Blo 1340989 2013671 := bstep (se 1 (by rfl) ⟨1510253, by rfl⟩ : syracuseStep 2013671 = 3020507) B3020507
theorem B3021353 : Blo 1340989 3021353 := bstep (se 2 (by rfl) ⟨1133007, by rfl⟩ : syracuseStep 3021353 = 2266015) B2266015
theorem B2013743 : Blo 1340989 2013743 := bstep (se 1 (by rfl) ⟨1510307, by rfl⟩ : syracuseStep 2013743 = 3020615) B3020615
theorem B3226159 : Blo 1340989 3226159 := bstep (se 1 (by rfl) ⟨2419619, by rfl⟩ : syracuseStep 3226159 = 4839239) B4839239
theorem B3398537 : Blo 1340989 3398537 := bstep (se 2 (by rfl) ⟨1274451, by rfl⟩ : syracuseStep 3398537 = 2548903) B2548903
theorem B1342431 : Blo 1340989 1342431 := bstep (se 1 (by rfl) ⟨1006823, by rfl⟩ : syracuseStep 1342431 = 2013647) B2013647
theorem B1342491 : Blo 1340989 1342491 := bstep (se 1 (by rfl) ⟨1006868, by rfl⟩ : syracuseStep 1342491 = 2013737) B2013737
theorem B1342619 : Blo 1340989 1342619 := bstep (se 1 (by rfl) ⟨1006964, by rfl⟩ : syracuseStep 1342619 = 2013929) B2013929
theorem B2014415 : Blo 1340989 2014415 := bstep (se 1 (by rfl) ⟨1510811, by rfl⟩ : syracuseStep 2014415 = 3021623) B3021623
theorem B86039873 : Blo 1340989 86039873 := bstep (se 2 (by rfl) ⟨32264952, by rfl⟩ : syracuseStep 86039873 = 64529905) B64529905
theorem B2547035 : Blo 1340989 2547035 := bstep (se 1 (by rfl) ⟨1910276, by rfl⟩ : syracuseStep 2547035 = 3820553) B3820553
theorem B2547065 : Blo 1340989 2547065 := bstep (se 2 (by rfl) ⟨955149, by rfl⟩ : syracuseStep 2547065 = 1910299) B1910299
theorem B1342875 : Blo 1340989 1342875 := bstep (se 1 (by rfl) ⟨1007156, by rfl⟩ : syracuseStep 1342875 = 2014313) B2014313
theorem B84966841 : Blo 1340989 84966841 := bstep (se 2 (by rfl) ⟨31862565, by rfl⟩ : syracuseStep 84966841 = 63725131) B63725131
theorem B6798815 : Blo 1340989 6798815 := bstep (se 1 (by rfl) ⟨5099111, by rfl⟩ : syracuseStep 6798815 = 10198223) B10198223
theorem B1342959 : Blo 1340989 1342959 := bstep (se 1 (by rfl) ⟨1007219, by rfl⟩ : syracuseStep 1342959 = 2014439) B2014439
theorem B25779809 : Blo 1340989 25779809 := bstep (se 2 (by rfl) ⟨9667428, by rfl⟩ : syracuseStep 25779809 = 19334857) B19334857
theorem B6119135 : Blo 1340989 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B14516111 : Blo 1340989 14516111 := bstep (se 1 (by rfl) ⟨10887083, by rfl⟩ : syracuseStep 14516111 = 21774167) B21774167
theorem B1359775 : Blo 1340989 1359775 := bstep (se 1 (by rfl) ⟨1019831, by rfl⟩ : syracuseStep 1359775 = 2039663) B2039663
theorem B2548091 : Blo 1340989 2548091 := bstep (se 1 (by rfl) ⟨1911068, by rfl⟩ : syracuseStep 2548091 = 3822137) B3822137
theorem B6447721 : Blo 1340989 6447721 := bstep (se 2 (by rfl) ⟨2417895, by rfl⟩ : syracuseStep 6447721 = 4835791) B4835791
theorem B4301545 : Blo 1340989 4301545 := bstep (se 2 (by rfl) ⟨1613079, by rfl⟩ : syracuseStep 4301545 = 3226159) B3226159
theorem B6792173 : Blo 1340989 6792173 := bstep (se 3 (by rfl) ⟨1273532, by rfl⟩ : syracuseStep 6792173 = 2547065) B2547065
theorem B4531463 : Blo 1340989 4531463 := bstep (se 1 (by rfl) ⟨3398597, by rfl⟩ : syracuseStep 4531463 = 6797195) B6797195
theorem B2549161 : Blo 1340989 2549161 := bstep (se 2 (by rfl) ⟨955935, by rfl⟩ : syracuseStep 2549161 = 1911871) B1911871
theorem B5162771 : Blo 1340989 5162771 := bstep (se 1 (by rfl) ⟨3872078, by rfl⟩ : syracuseStep 5162771 = 7744157) B7744157
theorem B113289121 : Blo 1340989 113289121 := bstep (se 2 (by rfl) ⟨42483420, by rfl⟩ : syracuseStep 113289121 = 84966841) B84966841
theorem B1698023 : Blo 1340989 1698023 := bstep (se 1 (by rfl) ⟨1273517, by rfl⟩ : syracuseStep 1698023 = 2547035) B2547035
theorem B4532543 : Blo 1340989 4532543 := bstep (se 1 (by rfl) ⟨3399407, by rfl⟩ : syracuseStep 4532543 = 6798815) B6798815
theorem B1813033 : Blo 1340989 1813033 := bstep (se 2 (by rfl) ⟨679887, by rfl⟩ : syracuseStep 1813033 = 1359775) B1359775
theorem B9677407 : Blo 1340989 9677407 := bstep (se 1 (by rfl) ⟨7258055, by rfl⟩ : syracuseStep 9677407 = 14516111) B14516111
theorem B3820223 : Blo 1340989 3820223 := bstep (se 1 (by rfl) ⟨2865167, by rfl⟩ : syracuseStep 3820223 = 5730335) B5730335
theorem B3017519 : Blo 1340989 3017519 := bstep (se 1 (by rfl) ⟨2263139, by rfl⟩ : syracuseStep 3017519 = 4526279) B4526279
theorem B2149183 : Blo 1340989 2149183 := bstep (se 1 (by rfl) ⟨1611887, by rfl⟩ : syracuseStep 2149183 = 3223775) B3223775
theorem B1698671 : Blo 1340989 1698671 := bstep (se 1 (by rfl) ⟨1274003, by rfl⟩ : syracuseStep 1698671 = 2548007) B2548007
theorem B10193849 : Blo 1340989 10193849 := bstep (se 2 (by rfl) ⟨3822693, by rfl⟩ : syracuseStep 10193849 = 7645387) B7645387
theorem B58059929 : Blo 1340989 58059929 := bstep (se 2 (by rfl) ⟨21772473, by rfl⟩ : syracuseStep 58059929 = 43544947) B43544947
theorem B16313501 : Blo 1340989 16313501 := bstep (se 3 (by rfl) ⟨3058781, by rfl⟩ : syracuseStep 16313501 = 6117563) B6117563
theorem B53005859 : Blo 1340989 53005859 := bstep (se 1 (by rfl) ⟨39754394, by rfl⟩ : syracuseStep 53005859 = 79508789) B79508789
theorem B6794927 : Blo 1340989 6794927 := bstep (se 1 (by rfl) ⟨5096195, by rfl⟩ : syracuseStep 6794927 = 10192391) B10192391
theorem B3018473 : Blo 1340989 3018473 := bstep (se 2 (by rfl) ⟨1131927, by rfl⟩ : syracuseStep 3018473 = 2263855) B2263855
theorem B3018491 : Blo 1340989 3018491 := bstep (se 1 (by rfl) ⟨2263868, by rfl⟩ : syracuseStep 3018491 = 4527737) B4527737
theorem B165228329 : Blo 1340989 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B2265023 : Blo 1340989 2265023 := bstep (se 1 (by rfl) ⟨1698767, by rfl⟩ : syracuseStep 2265023 = 3397535) B3397535
theorem B4526171 : Blo 1340989 4526171 := bstep (se 1 (by rfl) ⟨3394628, by rfl⟩ : syracuseStep 4526171 = 6789257) B6789257
theorem B2265401 : Blo 1340989 2265401 := bstep (se 2 (by rfl) ⟨849525, by rfl⟩ : syracuseStep 2265401 = 1699051) B1699051
theorem B2011583 : Blo 1340989 2011583 := bstep (se 1 (by rfl) ⟨1508687, by rfl⟩ : syracuseStep 2011583 = 3017375) B3017375
theorem B5444093 : Blo 1340989 5444093 := bstep (se 3 (by rfl) ⟨1020767, by rfl⟩ : syracuseStep 5444093 = 2041535) B2041535
theorem B2265691 : Blo 1340989 2265691 := bstep (se 1 (by rfl) ⟨1699268, by rfl⟩ : syracuseStep 2265691 = 3398537) B3398537
theorem B2011931 : Blo 1340989 2011931 := bstep (se 1 (by rfl) ⟨1508948, by rfl⟩ : syracuseStep 2011931 = 3017897) B3017897
theorem B3019769 : Blo 1340989 3019769 := bstep (se 2 (by rfl) ⟨1132413, by rfl⟩ : syracuseStep 3019769 = 2264827) B2264827
theorem B5092415 : Blo 1340989 5092415 := bstep (se 1 (by rfl) ⟨3819311, by rfl⟩ : syracuseStep 5092415 = 7638623) B7638623
theorem B65303819 : Blo 1340989 65303819 := bstep (se 1 (by rfl) ⟨48977864, by rfl⟩ : syracuseStep 65303819 = 97955729) B97955729
theorem B1341135 : Blo 1340989 1341135 := bstep (se 1 (by rfl) ⟨1005851, by rfl⟩ : syracuseStep 1341135 = 2011703) B2011703
theorem B1341295 : Blo 1340989 1341295 := bstep (se 1 (by rfl) ⟨1005971, by rfl⟩ : syracuseStep 1341295 = 2011943) B2011943
theorem B6453103 : Blo 1340989 6453103 := bstep (se 1 (by rfl) ⟨4839827, by rfl⟩ : syracuseStep 6453103 = 9679655) B9679655
theorem B8599421 : Blo 1340989 8599421 := bstep (se 3 (by rfl) ⟨1612391, by rfl⟩ : syracuseStep 8599421 = 3224783) B3224783
theorem B1341375 : Blo 1340989 1341375 := bstep (se 1 (by rfl) ⟨1006031, by rfl⟩ : syracuseStep 1341375 = 2012063) B2012063
theorem B25794571 : Blo 1340989 25794571 := bstep (se 1 (by rfl) ⟨19345928, by rfl⟩ : syracuseStep 25794571 = 38691857) B38691857
theorem B4528169 : Blo 1340989 4528169 := bstep (se 2 (by rfl) ⟨1698063, by rfl⟩ : syracuseStep 4528169 = 3396127) B3396127
theorem B5167145 : Blo 1340989 5167145 := bstep (se 2 (by rfl) ⟨1937679, by rfl⟩ : syracuseStep 5167145 = 3875359) B3875359
theorem B3020903 : Blo 1340989 3020903 := bstep (se 1 (by rfl) ⟨2265677, by rfl⟩ : syracuseStep 3020903 = 4531355) B4531355
theorem B2013407 : Blo 1340989 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B1341691 : Blo 1340989 1341691 := bstep (se 1 (by rfl) ⟨1006268, by rfl⟩ : syracuseStep 1341691 = 2012537) B2012537
theorem B1341695 : Blo 1340989 1341695 := bstep (se 1 (by rfl) ⟨1006271, by rfl⟩ : syracuseStep 1341695 = 2012543) B2012543
theorem B2013467 : Blo 1340989 2013467 := bstep (se 1 (by rfl) ⟨1510100, by rfl⟩ : syracuseStep 2013467 = 3020201) B3020201
theorem B2013503 : Blo 1340989 2013503 := bstep (se 1 (by rfl) ⟨1510127, by rfl⟩ : syracuseStep 2013503 = 3020255) B3020255
theorem B1341799 : Blo 1340989 1341799 := bstep (se 1 (by rfl) ⟨1006349, by rfl⟩ : syracuseStep 1341799 = 2012699) B2012699
theorem B1341919 : Blo 1340989 1341919 := bstep (se 1 (by rfl) ⟨1006439, by rfl⟩ : syracuseStep 1341919 = 2012879) B2012879
theorem B1342055 : Blo 1340989 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B1342079 : Blo 1340989 1342079 := bstep (se 1 (by rfl) ⟨1006559, by rfl⟩ : syracuseStep 1342079 = 2013119) B2013119
theorem B4299455 : Blo 1340989 4299455 := bstep (se 1 (by rfl) ⟨3224591, by rfl⟩ : syracuseStep 4299455 = 6449183) B6449183
theorem B2013887 : Blo 1340989 2013887 := bstep (se 1 (by rfl) ⟨1510415, by rfl⟩ : syracuseStep 2013887 = 3020831) B3020831
theorem B1342191 : Blo 1340989 1342191 := bstep (se 1 (by rfl) ⟨1006643, by rfl⟩ : syracuseStep 1342191 = 2013287) B2013287
theorem B11623175 : Blo 1340989 11623175 := bstep (se 1 (by rfl) ⟨8717381, by rfl⟩ : syracuseStep 11623175 = 17434763) B17434763
theorem B3627785 : Blo 1340989 3627785 := bstep (se 2 (by rfl) ⟨1360419, by rfl⟩ : syracuseStep 3627785 = 2720839) B2720839
theorem B2546473 : Blo 1340989 2546473 := bstep (se 2 (by rfl) ⟨954927, by rfl⟩ : syracuseStep 2546473 = 1909855) B1909855
theorem B6798167 : Blo 1340989 6798167 := bstep (se 1 (by rfl) ⟨5098625, by rfl⟩ : syracuseStep 6798167 = 10197251) B10197251
theorem B2014175 : Blo 1340989 2014175 := bstep (se 1 (by rfl) ⟨1510631, by rfl⟩ : syracuseStep 2014175 = 3021263) B3021263
theorem B1342447 : Blo 1340989 1342447 := bstep (se 1 (by rfl) ⟨1006835, by rfl⟩ : syracuseStep 1342447 = 2013671) B2013671
theorem B2014235 : Blo 1340989 2014235 := bstep (se 1 (by rfl) ⟨1510676, by rfl⟩ : syracuseStep 2014235 = 3021353) B3021353
theorem B1342495 : Blo 1340989 1342495 := bstep (se 1 (by rfl) ⟨1006871, by rfl⟩ : syracuseStep 1342495 = 2013743) B2013743
theorem B4529249 : Blo 1340989 4529249 := bstep (se 2 (by rfl) ⟨1698468, by rfl⟩ : syracuseStep 4529249 = 3396937) B3396937
theorem B3398831 : Blo 1340989 3398831 := bstep (se 1 (by rfl) ⟨2549123, by rfl⟩ : syracuseStep 3398831 = 5098247) B5098247
theorem B65289401 : Blo 1340989 65289401 := bstep (se 2 (by rfl) ⟨24483525, by rfl⟩ : syracuseStep 65289401 = 48967051) B48967051
theorem B1432895 : Blo 1340989 1432895 := bstep (se 1 (by rfl) ⟨1074671, by rfl⟩ : syracuseStep 1432895 = 2149343) B2149343
theorem B19357001 : Blo 1340989 19357001 := bstep (se 2 (by rfl) ⟨7258875, by rfl⟩ : syracuseStep 19357001 = 14517751) B14517751
theorem B5094845 : Blo 1340989 5094845 := bstep (se 3 (by rfl) ⟨955283, by rfl⟩ : syracuseStep 5094845 = 1910567) B1910567
theorem B1342943 : Blo 1340989 1342943 := bstep (se 1 (by rfl) ⟨1007207, by rfl⟩ : syracuseStep 1342943 = 2014415) B2014415
theorem B57359915 : Blo 1340989 57359915 := bstep (se 1 (by rfl) ⟨43019936, by rfl⟩ : syracuseStep 57359915 = 86039873) B86039873
theorem B2547263 : Blo 1340989 2547263 := bstep (se 1 (by rfl) ⟨1910447, by rfl⟩ : syracuseStep 2547263 = 3820895) B3820895
theorem B17186539 : Blo 1340989 17186539 := bstep (se 1 (by rfl) ⟨12889904, by rfl⟩ : syracuseStep 17186539 = 25779809) B25779809
theorem B4079423 : Blo 1340989 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B3628921 : Blo 1340989 3628921 := bstep (se 2 (by rfl) ⟨1360845, by rfl⟩ : syracuseStep 3628921 = 2721691) B2721691
theorem B3629395 : Blo 1340989 3629395 := bstep (se 1 (by rfl) ⟨2722046, by rfl⟩ : syracuseStep 3629395 = 5444093) B5444093
theorem B2417377 : Blo 1340989 2417377 := bstep (se 2 (by rfl) ⟨906516, by rfl⟩ : syracuseStep 2417377 = 1813033) B1813033
theorem B12903209 : Blo 1340989 12903209 := bstep (se 2 (by rfl) ⟨4838703, by rfl⟩ : syracuseStep 12903209 = 9677407) B9677407
theorem B5735393 : Blo 1340989 5735393 := bstep (se 2 (by rfl) ⟨2150772, by rfl⟩ : syracuseStep 5735393 = 4301545) B4301545
theorem B3441847 : Blo 1340989 3441847 := bstep (se 1 (by rfl) ⟨2581385, by rfl⟩ : syracuseStep 3441847 = 5162771) B5162771
theorem B11462309 : Blo 1340989 11462309 := bstep (se 4 (by rfl) ⟨1074591, by rfl⟩ : syracuseStep 11462309 = 2149183) B2149183
theorem B4532111 : Blo 1340989 4532111 := bstep (se 1 (by rfl) ⟨3399083, by rfl⟩ : syracuseStep 4532111 = 6798167) B6798167
theorem B43526267 : Blo 1340989 43526267 := bstep (se 1 (by rfl) ⟨32644700, by rfl⟩ : syracuseStep 43526267 = 65289401) B65289401
theorem B12904667 : Blo 1340989 12904667 := bstep (se 1 (by rfl) ⟨9678500, by rfl⟩ : syracuseStep 12904667 = 19357001) B19357001
theorem B22915385 : Blo 1340989 22915385 := bstep (se 2 (by rfl) ⟨8593269, by rfl⟩ : syracuseStep 22915385 = 17186539) B17186539
theorem B1698175 : Blo 1340989 1698175 := bstep (se 1 (by rfl) ⟨1273631, by rfl⟩ : syracuseStep 1698175 = 2547263) B2547263
theorem B8604137 : Blo 1340989 8604137 := bstep (se 2 (by rfl) ⟨3226551, by rfl⟩ : syracuseStep 8604137 = 6453103) B6453103
theorem B110152219 : Blo 1340989 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B1510015 : Blo 1340989 1510015 := bstep (se 1 (by rfl) ⟨1132511, by rfl⟩ : syracuseStep 1510015 = 2265023) B2265023
theorem B34392761 : Blo 1340989 34392761 := bstep (se 2 (by rfl) ⟨12897285, by rfl⟩ : syracuseStep 34392761 = 25794571) B25794571
theorem B3017447 : Blo 1340989 3017447 := bstep (se 1 (by rfl) ⟨2263085, by rfl⟩ : syracuseStep 3017447 = 4526171) B4526171
theorem B1510267 : Blo 1340989 1510267 := bstep (se 1 (by rfl) ⟨1132700, by rfl⟩ : syracuseStep 1510267 = 2265401) B2265401
theorem B1698727 : Blo 1340989 1698727 := bstep (se 1 (by rfl) ⟨1274045, by rfl⟩ : syracuseStep 1698727 = 2548091) B2548091
theorem B3394943 : Blo 1340989 3394943 := bstep (se 1 (by rfl) ⟨2546207, by rfl⟩ : syracuseStep 3394943 = 5092415) B5092415
theorem B8596961 : Blo 1340989 8596961 := bstep (se 2 (by rfl) ⟨3223860, by rfl⟩ : syracuseStep 8596961 = 6447721) B6447721
theorem B43535879 : Blo 1340989 43535879 := bstep (se 1 (by rfl) ⟨32651909, by rfl⟩ : syracuseStep 43535879 = 65303819) B65303819
theorem B3395297 : Blo 1340989 3395297 := bstep (se 2 (by rfl) ⟨1273236, by rfl⟩ : syracuseStep 3395297 = 2546473) B2546473
theorem B3018779 : Blo 1340989 3018779 := bstep (se 1 (by rfl) ⟨2264084, by rfl⟩ : syracuseStep 3018779 = 4528169) B4528169
theorem B3444763 : Blo 1340989 3444763 := bstep (se 1 (by rfl) ⟨2583572, by rfl⟩ : syracuseStep 3444763 = 5167145) B5167145
theorem B2011679 : Blo 1340989 2011679 := bstep (se 1 (by rfl) ⟨1508759, by rfl⟩ : syracuseStep 2011679 = 3017519) B3017519
theorem B6795899 : Blo 1340989 6795899 := bstep (se 1 (by rfl) ⟨5096924, by rfl⟩ : syracuseStep 6795899 = 10193849) B10193849
theorem B3019499 : Blo 1340989 3019499 := bstep (se 1 (by rfl) ⟨2264624, by rfl⟩ : syracuseStep 3019499 = 4529249) B4529249
theorem B10875667 : Blo 1340989 10875667 := bstep (se 1 (by rfl) ⟨8156750, by rfl⟩ : syracuseStep 10875667 = 16313501) B16313501
theorem B2265887 : Blo 1340989 2265887 := bstep (se 1 (by rfl) ⟨1699415, by rfl⟩ : syracuseStep 2265887 = 3398831) B3398831
theorem B3396563 : Blo 1340989 3396563 := bstep (se 1 (by rfl) ⟨2547422, by rfl⟩ : syracuseStep 3396563 = 5094845) B5094845
theorem B35337239 : Blo 1340989 35337239 := bstep (se 1 (by rfl) ⟨26502929, by rfl⟩ : syracuseStep 35337239 = 53005859) B53005859
theorem B2012315 : Blo 1340989 2012315 := bstep (se 1 (by rfl) ⟨1509236, by rfl⟩ : syracuseStep 2012315 = 3018473) B3018473
theorem B4838561 : Blo 1340989 4838561 := bstep (se 2 (by rfl) ⟨1814460, by rfl⟩ : syracuseStep 4838561 = 3628921) B3628921
theorem B2012327 : Blo 1340989 2012327 := bstep (se 1 (by rfl) ⟨1509245, by rfl⟩ : syracuseStep 2012327 = 3018491) B3018491
theorem B1341055 : Blo 1340989 1341055 := bstep (se 1 (by rfl) ⟨1005791, by rfl⟩ : syracuseStep 1341055 = 2011583) B2011583
theorem B1341287 : Blo 1340989 1341287 := bstep (se 1 (by rfl) ⟨1005965, by rfl⟩ : syracuseStep 1341287 = 2011931) B2011931
theorem B4528061 : Blo 1340989 4528061 := bstep (se 3 (by rfl) ⟨849011, by rfl⟩ : syracuseStep 4528061 = 1698023) B1698023
theorem B4528115 : Blo 1340989 4528115 := bstep (se 1 (by rfl) ⟨3396086, by rfl⟩ : syracuseStep 4528115 = 6792173) B6792173
theorem B15284213 : Blo 1340989 15284213 := bstep (se 5 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 15284213 = 1432895) B1432895
theorem B2013179 : Blo 1340989 2013179 := bstep (se 1 (by rfl) ⟨1509884, by rfl⟩ : syracuseStep 2013179 = 3019769) B3019769
theorem B3020921 : Blo 1340989 3020921 := bstep (se 2 (by rfl) ⟨1132845, by rfl⟩ : syracuseStep 3020921 = 2265691) B2265691
theorem B3020975 : Blo 1340989 3020975 := bstep (se 1 (by rfl) ⟨2265731, by rfl⟩ : syracuseStep 3020975 = 4531463) B4531463
theorem B5732947 : Blo 1340989 5732947 := bstep (se 1 (by rfl) ⟨4299710, by rfl⟩ : syracuseStep 5732947 = 8599421) B8599421
theorem B2013935 : Blo 1340989 2013935 := bstep (se 1 (by rfl) ⟨1510451, by rfl⟩ : syracuseStep 2013935 = 3020903) B3020903
theorem B1342271 : Blo 1340989 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B1342311 : Blo 1340989 1342311 := bstep (se 1 (by rfl) ⟨1006733, by rfl⟩ : syracuseStep 1342311 = 2013467) B2013467
theorem B1342335 : Blo 1340989 1342335 := bstep (se 1 (by rfl) ⟨1006751, by rfl⟩ : syracuseStep 1342335 = 2013503) B2013503
theorem B3021695 : Blo 1340989 3021695 := bstep (se 1 (by rfl) ⟨2266271, by rfl⟩ : syracuseStep 3021695 = 4532543) B4532543
theorem B2546815 : Blo 1340989 2546815 := bstep (se 1 (by rfl) ⟨1910111, by rfl⟩ : syracuseStep 2546815 = 3820223) B3820223
theorem B2866303 : Blo 1340989 2866303 := bstep (se 1 (by rfl) ⟨2149727, by rfl⟩ : syracuseStep 2866303 = 4299455) B4299455
theorem B1342591 : Blo 1340989 1342591 := bstep (se 1 (by rfl) ⟨1006943, by rfl⟩ : syracuseStep 1342591 = 2013887) B2013887
theorem B7748783 : Blo 1340989 7748783 := bstep (se 1 (by rfl) ⟨5811587, by rfl⟩ : syracuseStep 7748783 = 11623175) B11623175
theorem B3398881 : Blo 1340989 3398881 := bstep (se 2 (by rfl) ⟨1274580, by rfl⟩ : syracuseStep 3398881 = 2549161) B2549161
theorem B1342783 : Blo 1340989 1342783 := bstep (se 1 (by rfl) ⟨1007087, by rfl⟩ : syracuseStep 1342783 = 2014175) B2014175
theorem B1342823 : Blo 1340989 1342823 := bstep (se 1 (by rfl) ⟨1007117, by rfl⟩ : syracuseStep 1342823 = 2014235) B2014235
theorem B9674093 : Blo 1340989 9674093 := bstep (se 3 (by rfl) ⟨1813892, by rfl⟩ : syracuseStep 9674093 = 3627785) B3627785
theorem B38706619 : Blo 1340989 38706619 := bstep (se 1 (by rfl) ⟨29029964, by rfl⟩ : syracuseStep 38706619 = 58059929) B58059929
theorem B4529789 : Blo 1340989 4529789 := bstep (se 3 (by rfl) ⟨849335, by rfl⟩ : syracuseStep 4529789 = 1698671) B1698671
theorem B38239943 : Blo 1340989 38239943 := bstep (se 1 (by rfl) ⟨28679957, by rfl⟩ : syracuseStep 38239943 = 57359915) B57359915
theorem B4529951 : Blo 1340989 4529951 := bstep (se 1 (by rfl) ⟨3397463, by rfl⟩ : syracuseStep 4529951 = 6794927) B6794927
theorem B2719615 : Blo 1340989 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B151052161 : Blo 1340989 151052161 := bstep (se 2 (by rfl) ⟨56644560, by rfl⟩ : syracuseStep 151052161 = 113289121) B113289121
theorem B4530599 : Blo 1340989 4530599 := bstep (se 1 (by rfl) ⟨3397949, by rfl⟩ : syracuseStep 4530599 = 6795899) B6795899
theorem B8602139 : Blo 1340989 8602139 := bstep (se 1 (by rfl) ⟨6451604, by rfl⟩ : syracuseStep 8602139 = 12903209) B12903209
theorem B7643929 : Blo 1340989 7643929 := bstep (se 2 (by rfl) ⟨2866473, by rfl⟩ : syracuseStep 7643929 = 5732947) B5732947
theorem B14500889 : Blo 1340989 14500889 := bstep (se 2 (by rfl) ⟨5437833, by rfl⟩ : syracuseStep 14500889 = 10875667) B10875667
theorem B29017511 : Blo 1340989 29017511 := bstep (se 1 (by rfl) ⟨21763133, by rfl⟩ : syracuseStep 29017511 = 43526267) B43526267
theorem B8603111 : Blo 1340989 8603111 := bstep (se 1 (by rfl) ⟨6452333, by rfl⟩ : syracuseStep 8603111 = 12904667) B12904667
theorem B4589129 : Blo 1340989 4589129 := bstep (se 2 (by rfl) ⟨1720923, by rfl⟩ : syracuseStep 4589129 = 3441847) B3441847
theorem B4531841 : Blo 1340989 4531841 := bstep (se 2 (by rfl) ⟨1699440, by rfl⟩ : syracuseStep 4531841 = 3398881) B3398881
theorem B5736091 : Blo 1340989 5736091 := bstep (se 1 (by rfl) ⟨4302068, by rfl⟩ : syracuseStep 5736091 = 8604137) B8604137
theorem B6449395 : Blo 1340989 6449395 := bstep (se 1 (by rfl) ⟨4837046, by rfl⟩ : syracuseStep 6449395 = 9674093) B9674093
theorem B2263295 : Blo 1340989 2263295 := bstep (se 1 (by rfl) ⟨1697471, by rfl⟩ : syracuseStep 2263295 = 3394943) B3394943
theorem B2263531 : Blo 1340989 2263531 := bstep (se 1 (by rfl) ⟨1697648, by rfl⟩ : syracuseStep 2263531 = 3395297) B3395297
theorem B201402881 : Blo 1340989 201402881 := bstep (se 2 (by rfl) ⟨75526080, by rfl⟩ : syracuseStep 201402881 = 151052161) B151052161
theorem B2264233 : Blo 1340989 2264233 := bstep (se 2 (by rfl) ⟨849087, by rfl⟩ : syracuseStep 2264233 = 1698175) B1698175
theorem B1510591 : Blo 1340989 1510591 := bstep (se 1 (by rfl) ⟨1132943, by rfl⟩ : syracuseStep 1510591 = 2265887) B2265887
theorem B2264375 : Blo 1340989 2264375 := bstep (se 1 (by rfl) ⟨1698281, by rfl⟩ : syracuseStep 2264375 = 3396563) B3396563
theorem B146869625 : Blo 1340989 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B3223169 : Blo 1340989 3223169 := bstep (se 2 (by rfl) ⟨1208688, by rfl⟩ : syracuseStep 3223169 = 2417377) B2417377
theorem B2264969 : Blo 1340989 2264969 := bstep (se 2 (by rfl) ⟨849363, by rfl⟩ : syracuseStep 2264969 = 1698727) B1698727
theorem B3018707 : Blo 1340989 3018707 := bstep (se 1 (by rfl) ⟨2264030, by rfl⟩ : syracuseStep 3018707 = 4528061) B4528061
theorem B3018743 : Blo 1340989 3018743 := bstep (se 1 (by rfl) ⟨2264057, by rfl⟩ : syracuseStep 3018743 = 4528115) B4528115
theorem B3395753 : Blo 1340989 3395753 := bstep (se 2 (by rfl) ⟨1273407, by rfl⟩ : syracuseStep 3395753 = 2546815) B2546815
theorem B3821737 : Blo 1340989 3821737 := bstep (se 2 (by rfl) ⟨1433151, by rfl⟩ : syracuseStep 3821737 = 2866303) B2866303
theorem B2011631 : Blo 1340989 2011631 := bstep (se 1 (by rfl) ⟨1508723, by rfl⟩ : syracuseStep 2011631 = 3017447) B3017447
theorem B5165855 : Blo 1340989 5165855 := bstep (se 1 (by rfl) ⟨3874391, by rfl⟩ : syracuseStep 5165855 = 7748783) B7748783
theorem B5731307 : Blo 1340989 5731307 := bstep (se 1 (by rfl) ⟨4298480, by rfl⟩ : syracuseStep 5731307 = 8596961) B8596961
theorem B3019859 : Blo 1340989 3019859 := bstep (se 1 (by rfl) ⟨2264894, by rfl⟩ : syracuseStep 3019859 = 4529789) B4529789
theorem B3626153 : Blo 1340989 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B3019967 : Blo 1340989 3019967 := bstep (se 1 (by rfl) ⟨2264975, by rfl⟩ : syracuseStep 3019967 = 4529951) B4529951
theorem B2012519 : Blo 1340989 2012519 := bstep (se 1 (by rfl) ⟨1509389, by rfl⟩ : syracuseStep 2012519 = 3018779) B3018779
theorem B4593017 : Blo 1340989 4593017 := bstep (se 2 (by rfl) ⟨1722381, by rfl⟩ : syracuseStep 4593017 = 3444763) B3444763
theorem B1341119 : Blo 1340989 1341119 := bstep (se 1 (by rfl) ⟨1005839, by rfl⟩ : syracuseStep 1341119 = 2011679) B2011679
theorem B4839193 : Blo 1340989 4839193 := bstep (se 2 (by rfl) ⟨1814697, by rfl⟩ : syracuseStep 4839193 = 3629395) B3629395
theorem B2012999 : Blo 1340989 2012999 := bstep (se 1 (by rfl) ⟨1509749, by rfl⟩ : syracuseStep 2012999 = 3019499) B3019499
theorem B3823595 : Blo 1340989 3823595 := bstep (se 1 (by rfl) ⟨2867696, by rfl⟩ : syracuseStep 3823595 = 5735393) B5735393
theorem B23558159 : Blo 1340989 23558159 := bstep (se 1 (by rfl) ⟨17668619, by rfl⟩ : syracuseStep 23558159 = 35337239) B35337239
theorem B1341543 : Blo 1340989 1341543 := bstep (se 1 (by rfl) ⟨1006157, by rfl⟩ : syracuseStep 1341543 = 2012315) B2012315
theorem B3225707 : Blo 1340989 3225707 := bstep (se 1 (by rfl) ⟨2419280, by rfl⟩ : syracuseStep 3225707 = 4838561) B4838561
theorem B1341551 : Blo 1340989 1341551 := bstep (se 1 (by rfl) ⟨1006163, by rfl⟩ : syracuseStep 1341551 = 2012327) B2012327
theorem B2013353 : Blo 1340989 2013353 := bstep (se 2 (by rfl) ⟨755007, by rfl⟩ : syracuseStep 2013353 = 1510015) B1510015
theorem B7641539 : Blo 1340989 7641539 := bstep (se 1 (by rfl) ⟨5731154, by rfl⟩ : syracuseStep 7641539 = 11462309) B11462309
theorem B2013689 : Blo 1340989 2013689 := bstep (se 2 (by rfl) ⟨755133, by rfl⟩ : syracuseStep 2013689 = 1510267) B1510267
theorem B3021407 : Blo 1340989 3021407 := bstep (se 1 (by rfl) ⟨2266055, by rfl⟩ : syracuseStep 3021407 = 4532111) B4532111
theorem B10189475 : Blo 1340989 10189475 := bstep (se 1 (by rfl) ⟨7642106, by rfl⟩ : syracuseStep 10189475 = 15284213) B15284213
theorem B1342119 : Blo 1340989 1342119 := bstep (se 1 (by rfl) ⟨1006589, by rfl⟩ : syracuseStep 1342119 = 2013179) B2013179
theorem B2013947 : Blo 1340989 2013947 := bstep (se 1 (by rfl) ⟨1510460, by rfl⟩ : syracuseStep 2013947 = 3020921) B3020921
theorem B2013983 : Blo 1340989 2013983 := bstep (se 1 (by rfl) ⟨1510487, by rfl⟩ : syracuseStep 2013983 = 3020975) B3020975
theorem B15276923 : Blo 1340989 15276923 := bstep (se 1 (by rfl) ⟨11457692, by rfl⟩ : syracuseStep 15276923 = 22915385) B22915385
theorem B22928507 : Blo 1340989 22928507 := bstep (se 1 (by rfl) ⟨17196380, by rfl⟩ : syracuseStep 22928507 = 34392761) B34392761
theorem B1342623 : Blo 1340989 1342623 := bstep (se 1 (by rfl) ⟨1006967, by rfl⟩ : syracuseStep 1342623 = 2013935) B2013935
theorem B101973181 : Blo 1340989 101973181 := bstep (se 3 (by rfl) ⟨19119971, by rfl⟩ : syracuseStep 101973181 = 38239943) B38239943
theorem B51608825 : Blo 1340989 51608825 := bstep (se 2 (by rfl) ⟨19353309, by rfl⟩ : syracuseStep 51608825 = 38706619) B38706619
theorem B2014463 : Blo 1340989 2014463 := bstep (se 1 (by rfl) ⟨1510847, by rfl⟩ : syracuseStep 2014463 = 3021695) B3021695
theorem B29023919 : Blo 1340989 29023919 := bstep (se 1 (by rfl) ⟨21767939, by rfl⟩ : syracuseStep 29023919 = 43535879) B43535879
theorem B5095649 : Blo 1340989 5095649 := bstep (se 2 (by rfl) ⟨1910868, by rfl⟩ : syracuseStep 5095649 = 3821737) B3821737
theorem B5734759 : Blo 1340989 5734759 := bstep (se 1 (by rfl) ⟨4301069, by rfl⟩ : syracuseStep 5734759 = 8602139) B8602139
theorem B9667259 : Blo 1340989 9667259 := bstep (se 1 (by rfl) ⟨7250444, by rfl⟩ : syracuseStep 9667259 = 14500889) B14500889
theorem B2417435 : Blo 1340989 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B10191905 : Blo 1340989 10191905 := bstep (se 2 (by rfl) ⟨3821964, by rfl⟩ : syracuseStep 10191905 = 7643929) B7643929
theorem B2549063 : Blo 1340989 2549063 := bstep (se 1 (by rfl) ⟨1911797, by rfl⟩ : syracuseStep 2549063 = 3823595) B3823595
theorem B1508863 : Blo 1340989 1508863 := bstep (se 1 (by rfl) ⟨1131647, by rfl⟩ : syracuseStep 1508863 = 2263295) B2263295
theorem B135964241 : Blo 1340989 135964241 := bstep (se 2 (by rfl) ⟨50986590, by rfl⟩ : syracuseStep 135964241 = 101973181) B101973181
theorem B134268587 : Blo 1340989 134268587 := bstep (se 1 (by rfl) ⟨100701440, by rfl⟩ : syracuseStep 134268587 = 201402881) B201402881
theorem B6792983 : Blo 1340989 6792983 := bstep (se 1 (by rfl) ⟨5094737, by rfl⟩ : syracuseStep 6792983 = 10189475) B10189475
theorem B10184615 : Blo 1340989 10184615 := bstep (se 1 (by rfl) ⟨7638461, by rfl⟩ : syracuseStep 10184615 = 15276923) B15276923
theorem B1509583 : Blo 1340989 1509583 := bstep (se 1 (by rfl) ⟨1132187, by rfl⟩ : syracuseStep 1509583 = 2264375) B2264375
theorem B97913083 : Blo 1340989 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B2148779 : Blo 1340989 2148779 := bstep (se 1 (by rfl) ⟨1611584, by rfl⟩ : syracuseStep 2148779 = 3223169) B3223169
theorem B1509979 : Blo 1340989 1509979 := bstep (se 1 (by rfl) ⟨1132484, by rfl⟩ : syracuseStep 1509979 = 2264969) B2264969
theorem B2263835 : Blo 1340989 2263835 := bstep (se 1 (by rfl) ⟨1697876, by rfl⟩ : syracuseStep 2263835 = 3395753) B3395753
theorem B3443903 : Blo 1340989 3443903 := bstep (se 1 (by rfl) ⟨2582927, by rfl⟩ : syracuseStep 3443903 = 5165855) B5165855
theorem B3018041 : Blo 1340989 3018041 := bstep (se 2 (by rfl) ⟨1131765, by rfl⟩ : syracuseStep 3018041 = 2263531) B2263531
theorem B3820871 : Blo 1340989 3820871 := bstep (se 1 (by rfl) ⟨2865653, by rfl⟩ : syracuseStep 3820871 = 5731307) B5731307
theorem B19345007 : Blo 1340989 19345007 := bstep (se 1 (by rfl) ⟨14508755, by rfl⟩ : syracuseStep 19345007 = 29017511) B29017511
theorem B3059419 : Blo 1340989 3059419 := bstep (se 1 (by rfl) ⟨2294564, by rfl⟩ : syracuseStep 3059419 = 4589129) B4589129
theorem B22941629 : Blo 1340989 22941629 := bstep (se 3 (by rfl) ⟨4301555, by rfl⟩ : syracuseStep 22941629 = 8603111) B8603111
theorem B2150471 : Blo 1340989 2150471 := bstep (se 1 (by rfl) ⟨1612853, by rfl⟩ : syracuseStep 2150471 = 3225707) B3225707
theorem B25809029 : Blo 1340989 25809029 := bstep (se 4 (by rfl) ⟨2419596, by rfl⟩ : syracuseStep 25809029 = 4839193) B4839193
theorem B3018977 : Blo 1340989 3018977 := bstep (se 2 (by rfl) ⟨1132116, by rfl⟩ : syracuseStep 3018977 = 2264233) B2264233
theorem B7648121 : Blo 1340989 7648121 := bstep (se 2 (by rfl) ⟨2868045, by rfl⟩ : syracuseStep 7648121 = 5736091) B5736091
theorem B2012471 : Blo 1340989 2012471 := bstep (se 1 (by rfl) ⟨1509353, by rfl⟩ : syracuseStep 2012471 = 3018707) B3018707
theorem B2012495 : Blo 1340989 2012495 := bstep (se 1 (by rfl) ⟨1509371, by rfl⟩ : syracuseStep 2012495 = 3018743) B3018743
theorem B62821757 : Blo 1340989 62821757 := bstep (se 3 (by rfl) ⟨11779079, by rfl⟩ : syracuseStep 62821757 = 23558159) B23558159
theorem B3020399 : Blo 1340989 3020399 := bstep (se 1 (by rfl) ⟨2265299, by rfl⟩ : syracuseStep 3020399 = 4530599) B4530599
theorem B8599193 : Blo 1340989 8599193 := bstep (se 2 (by rfl) ⟨3224697, by rfl⟩ : syracuseStep 8599193 = 6449395) B6449395
theorem B1341087 : Blo 1340989 1341087 := bstep (se 1 (by rfl) ⟨1005815, by rfl⟩ : syracuseStep 1341087 = 2011631) B2011631
theorem B2013239 : Blo 1340989 2013239 := bstep (se 1 (by rfl) ⟨1509929, by rfl⟩ : syracuseStep 2013239 = 3019859) B3019859
theorem B2013311 : Blo 1340989 2013311 := bstep (se 1 (by rfl) ⟨1509983, by rfl⟩ : syracuseStep 2013311 = 3019967) B3019967
theorem B1341679 : Blo 1340989 1341679 := bstep (se 1 (by rfl) ⟨1006259, by rfl⟩ : syracuseStep 1341679 = 2012519) B2012519
theorem B3062011 : Blo 1340989 3062011 := bstep (se 1 (by rfl) ⟨2296508, by rfl⟩ : syracuseStep 3062011 = 4593017) B4593017
theorem B3021227 : Blo 1340989 3021227 := bstep (se 1 (by rfl) ⟨2265920, by rfl⟩ : syracuseStep 3021227 = 4531841) B4531841
theorem B1341999 : Blo 1340989 1341999 := bstep (se 1 (by rfl) ⟨1006499, by rfl⟩ : syracuseStep 1341999 = 2012999) B2012999
theorem B1342235 : Blo 1340989 1342235 := bstep (se 1 (by rfl) ⟨1006676, by rfl⟩ : syracuseStep 1342235 = 2013353) B2013353
theorem B2014121 : Blo 1340989 2014121 := bstep (se 2 (by rfl) ⟨755295, by rfl⟩ : syracuseStep 2014121 = 1510591) B1510591
theorem B5094359 : Blo 1340989 5094359 := bstep (se 1 (by rfl) ⟨3820769, by rfl⟩ : syracuseStep 5094359 = 7641539) B7641539
theorem B1342459 : Blo 1340989 1342459 := bstep (se 1 (by rfl) ⟨1006844, by rfl⟩ : syracuseStep 1342459 = 2013689) B2013689
theorem B2014271 : Blo 1340989 2014271 := bstep (se 1 (by rfl) ⟨1510703, by rfl⟩ : syracuseStep 2014271 = 3021407) B3021407
theorem B1342631 : Blo 1340989 1342631 := bstep (se 1 (by rfl) ⟨1006973, by rfl⟩ : syracuseStep 1342631 = 2013947) B2013947
theorem B1342655 : Blo 1340989 1342655 := bstep (se 1 (by rfl) ⟨1006991, by rfl⟩ : syracuseStep 1342655 = 2013983) B2013983
theorem B15285671 : Blo 1340989 15285671 := bstep (se 1 (by rfl) ⟨11464253, by rfl⟩ : syracuseStep 15285671 = 22928507) B22928507
theorem B34405883 : Blo 1340989 34405883 := bstep (se 1 (by rfl) ⟨25804412, by rfl⟩ : syracuseStep 34405883 = 51608825) B51608825
theorem B1342975 : Blo 1340989 1342975 := bstep (se 1 (by rfl) ⟨1007231, by rfl⟩ : syracuseStep 1342975 = 2014463) B2014463
theorem B19349279 : Blo 1340989 19349279 := bstep (se 1 (by rfl) ⟨14511959, by rfl⟩ : syracuseStep 19349279 = 29023919) B29023919
theorem B1433647 : Blo 1340989 1433647 := bstep (se 1 (by rfl) ⟨1075235, by rfl⟩ : syracuseStep 1433647 = 2150471) B2150471
theorem B1509223 : Blo 1340989 1509223 := bstep (se 1 (by rfl) ⟨1131917, by rfl⟩ : syracuseStep 1509223 = 2263835) B2263835
theorem B2295935 : Blo 1340989 2295935 := bstep (se 1 (by rfl) ⟨1721951, by rfl⟩ : syracuseStep 2295935 = 3443903) B3443903
theorem B12896671 : Blo 1340989 12896671 := bstep (se 1 (by rfl) ⟨9672503, by rfl⟩ : syracuseStep 12896671 = 19345007) B19345007
theorem B17206019 : Blo 1340989 17206019 := bstep (se 1 (by rfl) ⟨12904514, by rfl⟩ : syracuseStep 17206019 = 25809029) B25809029
theorem B130550777 : Blo 1340989 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B4082681 : Blo 1340989 4082681 := bstep (se 2 (by rfl) ⟨1531005, by rfl⟩ : syracuseStep 4082681 = 3062011) B3062011
theorem B7646345 : Blo 1340989 7646345 := bstep (se 2 (by rfl) ⟨2867379, by rfl⟩ : syracuseStep 7646345 = 5734759) B5734759
theorem B5098747 : Blo 1340989 5098747 := bstep (se 1 (by rfl) ⟨3824060, by rfl⟩ : syracuseStep 5098747 = 7648121) B7648121
theorem B6794603 : Blo 1340989 6794603 := bstep (se 1 (by rfl) ⟨5095952, by rfl⟩ : syracuseStep 6794603 = 10191905) B10191905
theorem B1699375 : Blo 1340989 1699375 := bstep (se 1 (by rfl) ⟨1274531, by rfl⟩ : syracuseStep 1699375 = 2549063) B2549063
theorem B41881171 : Blo 1340989 41881171 := bstep (se 1 (by rfl) ⟨31410878, by rfl⟩ : syracuseStep 41881171 = 62821757) B62821757
theorem B5730077 : Blo 1340989 5730077 := bstep (se 3 (by rfl) ⟨1074389, by rfl⟩ : syracuseStep 5730077 = 2148779) B2148779
theorem B3396239 : Blo 1340989 3396239 := bstep (se 1 (by rfl) ⟨2547179, by rfl⟩ : syracuseStep 3396239 = 5094359) B5094359
theorem B2011817 : Blo 1340989 2011817 := bstep (se 2 (by rfl) ⟨754431, by rfl⟩ : syracuseStep 2011817 = 1508863) B1508863
theorem B2012027 : Blo 1340989 2012027 := bstep (se 1 (by rfl) ⟨1509020, by rfl⟩ : syracuseStep 2012027 = 3018041) B3018041
theorem B12899519 : Blo 1340989 12899519 := bstep (se 1 (by rfl) ⟨9674639, by rfl⟩ : syracuseStep 12899519 = 19349279) B19349279
theorem B2012651 : Blo 1340989 2012651 := bstep (se 1 (by rfl) ⟨1509488, by rfl⟩ : syracuseStep 2012651 = 3018977) B3018977
theorem B3397099 : Blo 1340989 3397099 := bstep (se 1 (by rfl) ⟨2547824, by rfl⟩ : syracuseStep 3397099 = 5095649) B5095649
theorem B2012777 : Blo 1340989 2012777 := bstep (se 2 (by rfl) ⟨754791, by rfl⟩ : syracuseStep 2012777 = 1509583) B1509583
theorem B6444839 : Blo 1340989 6444839 := bstep (se 1 (by rfl) ⟨4833629, by rfl⟩ : syracuseStep 6444839 = 9667259) B9667259
theorem B1611623 : Blo 1340989 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B2013305 : Blo 1340989 2013305 := bstep (se 2 (by rfl) ⟨754989, by rfl⟩ : syracuseStep 2013305 = 1509979) B1509979
theorem B10188989 : Blo 1340989 10188989 := bstep (se 3 (by rfl) ⟨1910435, by rfl⟩ : syracuseStep 10188989 = 3820871) B3820871
theorem B1341647 : Blo 1340989 1341647 := bstep (se 1 (by rfl) ⟨1006235, by rfl⟩ : syracuseStep 1341647 = 2012471) B2012471
theorem B1341663 : Blo 1340989 1341663 := bstep (se 1 (by rfl) ⟨1006247, by rfl⟩ : syracuseStep 1341663 = 2012495) B2012495
theorem B90642827 : Blo 1340989 90642827 := bstep (se 1 (by rfl) ⟨67982120, by rfl⟩ : syracuseStep 90642827 = 135964241) B135964241
theorem B2013599 : Blo 1340989 2013599 := bstep (se 1 (by rfl) ⟨1510199, by rfl⟩ : syracuseStep 2013599 = 3020399) B3020399
theorem B5732795 : Blo 1340989 5732795 := bstep (se 1 (by rfl) ⟨4299596, by rfl⟩ : syracuseStep 5732795 = 8599193) B8599193
theorem B89512391 : Blo 1340989 89512391 := bstep (se 1 (by rfl) ⟨67134293, by rfl⟩ : syracuseStep 89512391 = 134268587) B134268587
theorem B4528655 : Blo 1340989 4528655 := bstep (se 1 (by rfl) ⟨3396491, by rfl⟩ : syracuseStep 4528655 = 6792983) B6792983
theorem B6789743 : Blo 1340989 6789743 := bstep (se 1 (by rfl) ⟨5092307, by rfl⟩ : syracuseStep 6789743 = 10184615) B10184615
theorem B1342159 : Blo 1340989 1342159 := bstep (se 1 (by rfl) ⟨1006619, by rfl⟩ : syracuseStep 1342159 = 2013239) B2013239
theorem B1342207 : Blo 1340989 1342207 := bstep (se 1 (by rfl) ⟨1006655, by rfl⟩ : syracuseStep 1342207 = 2013311) B2013311
theorem B2014151 : Blo 1340989 2014151 := bstep (se 1 (by rfl) ⟨1510613, by rfl⟩ : syracuseStep 2014151 = 3021227) B3021227
theorem B1342747 : Blo 1340989 1342747 := bstep (se 1 (by rfl) ⟨1007060, by rfl⟩ : syracuseStep 1342747 = 2014121) B2014121
theorem B1342847 : Blo 1340989 1342847 := bstep (se 1 (by rfl) ⟨1007135, by rfl⟩ : syracuseStep 1342847 = 2014271) B2014271
theorem B10190447 : Blo 1340989 10190447 := bstep (se 1 (by rfl) ⟨7642835, by rfl⟩ : syracuseStep 10190447 = 15285671) B15285671
theorem B4079225 : Blo 1340989 4079225 := bstep (se 2 (by rfl) ⟨1529709, by rfl⟩ : syracuseStep 4079225 = 3059419) B3059419
theorem B22937255 : Blo 1340989 22937255 := bstep (se 1 (by rfl) ⟨17202941, by rfl⟩ : syracuseStep 22937255 = 34405883) B34405883
theorem B15294419 : Blo 1340989 15294419 := bstep (se 1 (by rfl) ⟨11470814, by rfl⟩ : syracuseStep 15294419 = 22941629) B22941629
theorem B17195561 : Blo 1340989 17195561 := bstep (se 2 (by rfl) ⟨6448335, by rfl⟩ : syracuseStep 17195561 = 12896671) B12896671
theorem B6792659 : Blo 1340989 6792659 := bstep (se 1 (by rfl) ⟨5094494, by rfl⟩ : syracuseStep 6792659 = 10188989) B10188989
theorem B11470679 : Blo 1340989 11470679 := bstep (se 1 (by rfl) ⟨8603009, by rfl⟩ : syracuseStep 11470679 = 17206019) B17206019
theorem B87033851 : Blo 1340989 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B5097563 : Blo 1340989 5097563 := bstep (se 1 (by rfl) ⟨3823172, by rfl⟩ : syracuseStep 5097563 = 7646345) B7646345
theorem B6793631 : Blo 1340989 6793631 := bstep (se 1 (by rfl) ⟨5095223, by rfl⟩ : syracuseStep 6793631 = 10190447) B10190447
theorem B3820051 : Blo 1340989 3820051 := bstep (se 1 (by rfl) ⟨2865038, by rfl⟩ : syracuseStep 3820051 = 5730077) B5730077
theorem B1911529 : Blo 1340989 1911529 := bstep (se 2 (by rfl) ⟨716823, by rfl⟩ : syracuseStep 1911529 = 1433647) B1433647
theorem B2264159 : Blo 1340989 2264159 := bstep (se 1 (by rfl) ⟨1698119, by rfl⟩ : syracuseStep 2264159 = 3396239) B3396239
theorem B4296559 : Blo 1340989 4296559 := bstep (se 1 (by rfl) ⟨3222419, by rfl⟩ : syracuseStep 4296559 = 6444839) B6444839
theorem B60428551 : Blo 1340989 60428551 := bstep (se 1 (by rfl) ⟨45321413, by rfl⟩ : syracuseStep 60428551 = 90642827) B90642827
theorem B3821863 : Blo 1340989 3821863 := bstep (se 1 (by rfl) ⟨2866397, by rfl⟩ : syracuseStep 3821863 = 5732795) B5732795
theorem B59674927 : Blo 1340989 59674927 := bstep (se 1 (by rfl) ⟨44756195, by rfl⟩ : syracuseStep 59674927 = 89512391) B89512391
theorem B3019103 : Blo 1340989 3019103 := bstep (se 1 (by rfl) ⟨2264327, by rfl⟩ : syracuseStep 3019103 = 4528655) B4528655
theorem B4526495 : Blo 1340989 4526495 := bstep (se 1 (by rfl) ⟨3394871, by rfl⟩ : syracuseStep 4526495 = 6789743) B6789743
theorem B2265833 : Blo 1340989 2265833 := bstep (se 2 (by rfl) ⟨849687, by rfl⟩ : syracuseStep 2265833 = 1699375) B1699375
theorem B55841561 : Blo 1340989 55841561 := bstep (se 2 (by rfl) ⟨20940585, by rfl⟩ : syracuseStep 55841561 = 41881171) B41881171
theorem B4297661 : Blo 1340989 4297661 := bstep (se 3 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 4297661 = 1611623) B1611623
theorem B15291503 : Blo 1340989 15291503 := bstep (se 1 (by rfl) ⟨11468627, by rfl⟩ : syracuseStep 15291503 = 22937255) B22937255
theorem B2012297 : Blo 1340989 2012297 := bstep (se 2 (by rfl) ⟨754611, by rfl⟩ : syracuseStep 2012297 = 1509223) B1509223
theorem B10196279 : Blo 1340989 10196279 := bstep (se 1 (by rfl) ⟨7647209, by rfl⟩ : syracuseStep 10196279 = 15294419) B15294419
theorem B1341211 : Blo 1340989 1341211 := bstep (se 1 (by rfl) ⟨1005908, by rfl⟩ : syracuseStep 1341211 = 2011817) B2011817
theorem B1341351 : Blo 1340989 1341351 := bstep (se 1 (by rfl) ⟨1006013, by rfl⟩ : syracuseStep 1341351 = 2012027) B2012027
theorem B8599679 : Blo 1340989 8599679 := bstep (se 1 (by rfl) ⟨6449759, by rfl⟩ : syracuseStep 8599679 = 12899519) B12899519
theorem B1341767 : Blo 1340989 1341767 := bstep (se 1 (by rfl) ⟨1006325, by rfl⟩ : syracuseStep 1341767 = 2012651) B2012651
theorem B1341851 : Blo 1340989 1341851 := bstep (se 1 (by rfl) ⟨1006388, by rfl⟩ : syracuseStep 1341851 = 2012777) B2012777
theorem B1342203 : Blo 1340989 1342203 := bstep (se 1 (by rfl) ⟨1006652, by rfl⟩ : syracuseStep 1342203 = 2013305) B2013305
theorem B1530623 : Blo 1340989 1530623 := bstep (se 1 (by rfl) ⟨1147967, by rfl⟩ : syracuseStep 1530623 = 2295935) B2295935
theorem B1342399 : Blo 1340989 1342399 := bstep (se 1 (by rfl) ⟨1006799, by rfl⟩ : syracuseStep 1342399 = 2013599) B2013599
theorem B10877933 : Blo 1340989 10877933 := bstep (se 3 (by rfl) ⟨2039612, by rfl⟩ : syracuseStep 10877933 = 4079225) B4079225
theorem B6798329 : Blo 1340989 6798329 := bstep (se 2 (by rfl) ⟨2549373, by rfl⟩ : syracuseStep 6798329 = 5098747) B5098747
theorem B1342767 : Blo 1340989 1342767 := bstep (se 1 (by rfl) ⟨1007075, by rfl⟩ : syracuseStep 1342767 = 2014151) B2014151
theorem B4529465 : Blo 1340989 4529465 := bstep (se 2 (by rfl) ⟨1698549, by rfl⟩ : syracuseStep 4529465 = 3397099) B3397099
theorem B4529735 : Blo 1340989 4529735 := bstep (se 1 (by rfl) ⟨3397301, by rfl⟩ : syracuseStep 4529735 = 6794603) B6794603
theorem B10887149 : Blo 1340989 10887149 := bstep (se 3 (by rfl) ⟨2041340, by rfl⟩ : syracuseStep 10887149 = 4082681) B4082681
theorem B5095817 : Blo 1340989 5095817 := bstep (se 2 (by rfl) ⟨1910931, by rfl⟩ : syracuseStep 5095817 = 3821863) B3821863
theorem B4532219 : Blo 1340989 4532219 := bstep (se 1 (by rfl) ⟨3399164, by rfl⟩ : syracuseStep 4532219 = 6798329) B6798329
theorem B4081661 : Blo 1340989 4081661 := bstep (se 3 (by rfl) ⟨765311, by rfl⟩ : syracuseStep 4081661 = 1530623) B1530623
theorem B1509439 : Blo 1340989 1509439 := bstep (se 1 (by rfl) ⟨1132079, by rfl⟩ : syracuseStep 1509439 = 2264159) B2264159
theorem B5728745 : Blo 1340989 5728745 := bstep (se 2 (by rfl) ⟨2148279, by rfl⟩ : syracuseStep 5728745 = 4296559) B4296559
theorem B3017663 : Blo 1340989 3017663 := bstep (se 1 (by rfl) ⟨2263247, by rfl⟩ : syracuseStep 3017663 = 4526495) B4526495
theorem B80571401 : Blo 1340989 80571401 := bstep (se 2 (by rfl) ⟨30214275, by rfl⟩ : syracuseStep 80571401 = 60428551) B60428551
theorem B11463707 : Blo 1340989 11463707 := bstep (se 1 (by rfl) ⟨8597780, by rfl⟩ : syracuseStep 11463707 = 17195561) B17195561
theorem B1510555 : Blo 1340989 1510555 := bstep (se 1 (by rfl) ⟨1132916, by rfl⟩ : syracuseStep 1510555 = 2265833) B2265833
theorem B37227707 : Blo 1340989 37227707 := bstep (se 1 (by rfl) ⟨27920780, by rfl⟩ : syracuseStep 37227707 = 55841561) B55841561
theorem B10194335 : Blo 1340989 10194335 := bstep (se 1 (by rfl) ⟨7645751, by rfl⟩ : syracuseStep 10194335 = 15291503) B15291503
theorem B10194821 : Blo 1340989 10194821 := bstep (se 4 (by rfl) ⟨955764, by rfl⟩ : syracuseStep 10194821 = 1911529) B1911529
theorem B7647119 : Blo 1340989 7647119 := bstep (se 1 (by rfl) ⟨5735339, by rfl⟩ : syracuseStep 7647119 = 11470679) B11470679
theorem B3019643 : Blo 1340989 3019643 := bstep (se 1 (by rfl) ⟨2264732, by rfl⟩ : syracuseStep 3019643 = 4529465) B4529465
theorem B3019823 : Blo 1340989 3019823 := bstep (se 1 (by rfl) ⟨2264867, by rfl⟩ : syracuseStep 3019823 = 4529735) B4529735
theorem B2012735 : Blo 1340989 2012735 := bstep (se 1 (by rfl) ⟨1509551, by rfl⟩ : syracuseStep 2012735 = 3019103) B3019103
theorem B79566569 : Blo 1340989 79566569 := bstep (se 2 (by rfl) ⟨29837463, by rfl⟩ : syracuseStep 79566569 = 59674927) B59674927
theorem B2865107 : Blo 1340989 2865107 := bstep (se 1 (by rfl) ⟨2148830, by rfl⟩ : syracuseStep 2865107 = 4297661) B4297661
theorem B5093401 : Blo 1340989 5093401 := bstep (se 2 (by rfl) ⟨1910025, by rfl⟩ : syracuseStep 5093401 = 3820051) B3820051
theorem B1341531 : Blo 1340989 1341531 := bstep (se 1 (by rfl) ⟨1006148, by rfl⟩ : syracuseStep 1341531 = 2012297) B2012297
theorem B6797519 : Blo 1340989 6797519 := bstep (se 1 (by rfl) ⟨5098139, by rfl⟩ : syracuseStep 6797519 = 10196279) B10196279
theorem B4528439 : Blo 1340989 4528439 := bstep (se 1 (by rfl) ⟨3396329, by rfl⟩ : syracuseStep 4528439 = 6792659) B6792659
theorem B58022567 : Blo 1340989 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B3398375 : Blo 1340989 3398375 := bstep (se 1 (by rfl) ⟨2548781, by rfl⟩ : syracuseStep 3398375 = 5097563) B5097563
theorem B5733119 : Blo 1340989 5733119 := bstep (se 1 (by rfl) ⟨4299839, by rfl⟩ : syracuseStep 5733119 = 8599679) B8599679
theorem B4529087 : Blo 1340989 4529087 := bstep (se 1 (by rfl) ⟨3396815, by rfl⟩ : syracuseStep 4529087 = 6793631) B6793631
theorem B29007821 : Blo 1340989 29007821 := bstep (se 3 (by rfl) ⟨5438966, by rfl⟩ : syracuseStep 29007821 = 10877933) B10877933
theorem B7258099 : Blo 1340989 7258099 := bstep (se 1 (by rfl) ⟨5443574, by rfl⟩ : syracuseStep 7258099 = 10887149) B10887149
theorem B6791201 : Blo 1340989 6791201 := bstep (se 2 (by rfl) ⟨2546700, by rfl⟩ : syracuseStep 6791201 = 5093401) B5093401
theorem B53044379 : Blo 1340989 53044379 := bstep (se 1 (by rfl) ⟨39783284, by rfl⟩ : syracuseStep 53044379 = 79566569) B79566569
theorem B1910071 : Blo 1340989 1910071 := bstep (se 1 (by rfl) ⟨1432553, by rfl⟩ : syracuseStep 1910071 = 2865107) B2865107
theorem B2721107 : Blo 1340989 2721107 := bstep (se 1 (by rfl) ⟨2040830, by rfl⟩ : syracuseStep 2721107 = 4081661) B4081661
theorem B4531679 : Blo 1340989 4531679 := bstep (se 1 (by rfl) ⟨3398759, by rfl⟩ : syracuseStep 4531679 = 6797519) B6797519
theorem B3819163 : Blo 1340989 3819163 := bstep (se 1 (by rfl) ⟨2864372, by rfl⟩ : syracuseStep 3819163 = 5728745) B5728745
theorem B5098079 : Blo 1340989 5098079 := bstep (se 1 (by rfl) ⟨3823559, by rfl⟩ : syracuseStep 5098079 = 7647119) B7647119
theorem B9677465 : Blo 1340989 9677465 := bstep (se 2 (by rfl) ⟨3629049, by rfl⟩ : syracuseStep 9677465 = 7258099) B7258099
theorem B3018959 : Blo 1340989 3018959 := bstep (se 1 (by rfl) ⟨2264219, by rfl⟩ : syracuseStep 3018959 = 4528439) B4528439
theorem B2265583 : Blo 1340989 2265583 := bstep (se 1 (by rfl) ⟨1699187, by rfl⟩ : syracuseStep 2265583 = 3398375) B3398375
theorem B3822079 : Blo 1340989 3822079 := bstep (se 1 (by rfl) ⟨2866559, by rfl⟩ : syracuseStep 3822079 = 5733119) B5733119
theorem B2011775 : Blo 1340989 2011775 := bstep (se 1 (by rfl) ⟨1508831, by rfl⟩ : syracuseStep 2011775 = 3017663) B3017663
theorem B3019391 : Blo 1340989 3019391 := bstep (se 1 (by rfl) ⟨2264543, by rfl⟩ : syracuseStep 3019391 = 4529087) B4529087
theorem B24818471 : Blo 1340989 24818471 := bstep (se 1 (by rfl) ⟨18613853, by rfl⟩ : syracuseStep 24818471 = 37227707) B37227707
theorem B6796223 : Blo 1340989 6796223 := bstep (se 1 (by rfl) ⟨5097167, by rfl⟩ : syracuseStep 6796223 = 10194335) B10194335
theorem B77354189 : Blo 1340989 77354189 := bstep (se 3 (by rfl) ⟨14503910, by rfl⟩ : syracuseStep 77354189 = 29007821) B29007821
theorem B6796547 : Blo 1340989 6796547 := bstep (se 1 (by rfl) ⟨5097410, by rfl⟩ : syracuseStep 6796547 = 10194821) B10194821
theorem B2012585 : Blo 1340989 2012585 := bstep (se 2 (by rfl) ⟨754719, by rfl⟩ : syracuseStep 2012585 = 1509439) B1509439
theorem B3397211 : Blo 1340989 3397211 := bstep (se 1 (by rfl) ⟨2547908, by rfl⟩ : syracuseStep 3397211 = 5095817) B5095817
theorem B2013095 : Blo 1340989 2013095 := bstep (se 1 (by rfl) ⟨1509821, by rfl⟩ : syracuseStep 2013095 = 3019643) B3019643
theorem B2013215 : Blo 1340989 2013215 := bstep (se 1 (by rfl) ⟨1509911, by rfl⟩ : syracuseStep 2013215 = 3019823) B3019823
theorem B1341823 : Blo 1340989 1341823 := bstep (se 1 (by rfl) ⟨1006367, by rfl⟩ : syracuseStep 1341823 = 2012735) B2012735
theorem B3021479 : Blo 1340989 3021479 := bstep (se 1 (by rfl) ⟨2266109, by rfl⟩ : syracuseStep 3021479 = 4532219) B4532219
theorem B2014073 : Blo 1340989 2014073 := bstep (se 2 (by rfl) ⟨755277, by rfl⟩ : syracuseStep 2014073 = 1510555) B1510555
theorem B38681711 : Blo 1340989 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B53714267 : Blo 1340989 53714267 := bstep (se 1 (by rfl) ⟨40285700, by rfl⟩ : syracuseStep 53714267 = 80571401) B80571401
theorem B7642471 : Blo 1340989 7642471 := bstep (se 1 (by rfl) ⟨5731853, by rfl⟩ : syracuseStep 7642471 = 11463707) B11463707
theorem B4530815 : Blo 1340989 4530815 := bstep (se 1 (by rfl) ⟨3398111, by rfl⟩ : syracuseStep 4530815 = 6796223) B6796223
theorem B5096105 : Blo 1340989 5096105 := bstep (se 2 (by rfl) ⟨1911039, by rfl⟩ : syracuseStep 5096105 = 3822079) B3822079
theorem B51569459 : Blo 1340989 51569459 := bstep (se 1 (by rfl) ⟨38677094, by rfl⟩ : syracuseStep 51569459 = 77354189) B77354189
theorem B4531031 : Blo 1340989 4531031 := bstep (se 1 (by rfl) ⟨3398273, by rfl⟩ : syracuseStep 4531031 = 6796547) B6796547
theorem B35809511 : Blo 1340989 35809511 := bstep (se 1 (by rfl) ⟨26857133, by rfl⟩ : syracuseStep 35809511 = 53714267) B53714267
theorem B1814071 : Blo 1340989 1814071 := bstep (se 1 (by rfl) ⟨1360553, by rfl⟩ : syracuseStep 1814071 = 2721107) B2721107
theorem B2264807 : Blo 1340989 2264807 := bstep (se 1 (by rfl) ⟨1698605, by rfl⟩ : syracuseStep 2264807 = 3397211) B3397211
theorem B10187045 : Blo 1340989 10187045 := bstep (se 4 (by rfl) ⟨955035, by rfl⟩ : syracuseStep 10187045 = 1910071) B1910071
theorem B6451643 : Blo 1340989 6451643 := bstep (se 1 (by rfl) ⟨4838732, by rfl⟩ : syracuseStep 6451643 = 9677465) B9677465
theorem B5092217 : Blo 1340989 5092217 := bstep (se 2 (by rfl) ⟨1909581, by rfl⟩ : syracuseStep 5092217 = 3819163) B3819163
theorem B4527467 : Blo 1340989 4527467 := bstep (se 1 (by rfl) ⟨3395600, by rfl⟩ : syracuseStep 4527467 = 6791201) B6791201
theorem B2012639 : Blo 1340989 2012639 := bstep (se 1 (by rfl) ⟨1509479, by rfl⟩ : syracuseStep 2012639 = 3018959) B3018959
theorem B1341183 : Blo 1340989 1341183 := bstep (se 1 (by rfl) ⟨1005887, by rfl⟩ : syracuseStep 1341183 = 2011775) B2011775
theorem B2012927 : Blo 1340989 2012927 := bstep (se 1 (by rfl) ⟨1509695, by rfl⟩ : syracuseStep 2012927 = 3019391) B3019391
theorem B16545647 : Blo 1340989 16545647 := bstep (se 1 (by rfl) ⟨12409235, by rfl⟩ : syracuseStep 16545647 = 24818471) B24818471
theorem B3020777 : Blo 1340989 3020777 := bstep (se 2 (by rfl) ⟨1132791, by rfl⟩ : syracuseStep 3020777 = 2265583) B2265583
theorem B35362919 : Blo 1340989 35362919 := bstep (se 1 (by rfl) ⟨26522189, by rfl⟩ : syracuseStep 35362919 = 53044379) B53044379
theorem B1341723 : Blo 1340989 1341723 := bstep (se 1 (by rfl) ⟨1006292, by rfl⟩ : syracuseStep 1341723 = 2012585) B2012585
theorem B3021119 : Blo 1340989 3021119 := bstep (se 1 (by rfl) ⟨2265839, by rfl⟩ : syracuseStep 3021119 = 4531679) B4531679
theorem B1342063 : Blo 1340989 1342063 := bstep (se 1 (by rfl) ⟨1006547, by rfl⟩ : syracuseStep 1342063 = 2013095) B2013095
theorem B1342143 : Blo 1340989 1342143 := bstep (se 1 (by rfl) ⟨1006607, by rfl⟩ : syracuseStep 1342143 = 2013215) B2013215
theorem B3398719 : Blo 1340989 3398719 := bstep (se 1 (by rfl) ⟨2549039, by rfl⟩ : syracuseStep 3398719 = 5098079) B5098079
theorem B2014319 : Blo 1340989 2014319 := bstep (se 1 (by rfl) ⟨1510739, by rfl⟩ : syracuseStep 2014319 = 3021479) B3021479
theorem B10189961 : Blo 1340989 10189961 := bstep (se 2 (by rfl) ⟨3821235, by rfl⟩ : syracuseStep 10189961 = 7642471) B7642471
theorem B1342715 : Blo 1340989 1342715 := bstep (se 1 (by rfl) ⟨1007036, by rfl⟩ : syracuseStep 1342715 = 2014073) B2014073
theorem B25787807 : Blo 1340989 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B6791363 : Blo 1340989 6791363 := bstep (se 1 (by rfl) ⟨5093522, by rfl⟩ : syracuseStep 6791363 = 10187045) B10187045
theorem B4301095 : Blo 1340989 4301095 := bstep (se 1 (by rfl) ⟨3225821, by rfl⟩ : syracuseStep 4301095 = 6451643) B6451643
theorem B4531625 : Blo 1340989 4531625 := bstep (se 2 (by rfl) ⟨1699359, by rfl⟩ : syracuseStep 4531625 = 3398719) B3398719
theorem B2418761 : Blo 1340989 2418761 := bstep (se 2 (by rfl) ⟨907035, by rfl⟩ : syracuseStep 2418761 = 1814071) B1814071
theorem B6793307 : Blo 1340989 6793307 := bstep (se 1 (by rfl) ⟨5094980, by rfl⟩ : syracuseStep 6793307 = 10189961) B10189961
theorem B1509871 : Blo 1340989 1509871 := bstep (se 1 (by rfl) ⟨1132403, by rfl⟩ : syracuseStep 1509871 = 2264807) B2264807
theorem B94301117 : Blo 1340989 94301117 := bstep (se 3 (by rfl) ⟨17681459, by rfl⟩ : syracuseStep 94301117 = 35362919) B35362919
theorem B3394811 : Blo 1340989 3394811 := bstep (se 1 (by rfl) ⟨2546108, by rfl⟩ : syracuseStep 3394811 = 5092217) B5092217
theorem B3018311 : Blo 1340989 3018311 := bstep (se 1 (by rfl) ⟨2263733, by rfl⟩ : syracuseStep 3018311 = 4527467) B4527467
theorem B11030431 : Blo 1340989 11030431 := bstep (se 1 (by rfl) ⟨8272823, by rfl⟩ : syracuseStep 11030431 = 16545647) B16545647
theorem B17191871 : Blo 1340989 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B3020543 : Blo 1340989 3020543 := bstep (se 1 (by rfl) ⟨2265407, by rfl⟩ : syracuseStep 3020543 = 4530815) B4530815
theorem B3397403 : Blo 1340989 3397403 := bstep (se 1 (by rfl) ⟨2548052, by rfl⟩ : syracuseStep 3397403 = 5096105) B5096105
theorem B34379639 : Blo 1340989 34379639 := bstep (se 1 (by rfl) ⟨25784729, by rfl⟩ : syracuseStep 34379639 = 51569459) B51569459
theorem B3020687 : Blo 1340989 3020687 := bstep (se 1 (by rfl) ⟨2265515, by rfl⟩ : syracuseStep 3020687 = 4531031) B4531031
theorem B95492029 : Blo 1340989 95492029 := bstep (se 3 (by rfl) ⟨17904755, by rfl⟩ : syracuseStep 95492029 = 35809511) B35809511
theorem B1341759 : Blo 1340989 1341759 := bstep (se 1 (by rfl) ⟨1006319, by rfl⟩ : syracuseStep 1341759 = 2012639) B2012639
theorem B1341951 : Blo 1340989 1341951 := bstep (se 1 (by rfl) ⟨1006463, by rfl⟩ : syracuseStep 1341951 = 2012927) B2012927
theorem B2013851 : Blo 1340989 2013851 := bstep (se 1 (by rfl) ⟨1510388, by rfl⟩ : syracuseStep 2013851 = 3020777) B3020777
theorem B2014079 : Blo 1340989 2014079 := bstep (se 1 (by rfl) ⟨1510559, by rfl⟩ : syracuseStep 2014079 = 3021119) B3021119
theorem B1342879 : Blo 1340989 1342879 := bstep (se 1 (by rfl) ⟨1007159, by rfl⟩ : syracuseStep 1342879 = 2014319) B2014319
theorem B5734793 : Blo 1340989 5734793 := bstep (se 2 (by rfl) ⟨2150547, by rfl⟩ : syracuseStep 5734793 = 4301095) B4301095
theorem B11461247 : Blo 1340989 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B62867411 : Blo 1340989 62867411 := bstep (se 1 (by rfl) ⟨47150558, by rfl⟩ : syracuseStep 62867411 = 94301117) B94301117
theorem B2263207 : Blo 1340989 2263207 := bstep (se 1 (by rfl) ⟨1697405, by rfl⟩ : syracuseStep 2263207 = 3394811) B3394811
theorem B14707241 : Blo 1340989 14707241 := bstep (se 2 (by rfl) ⟨5515215, by rfl⟩ : syracuseStep 14707241 = 11030431) B11030431
theorem B127322705 : Blo 1340989 127322705 := bstep (se 2 (by rfl) ⟨47746014, by rfl⟩ : syracuseStep 127322705 = 95492029) B95492029
theorem B6450029 : Blo 1340989 6450029 := bstep (se 3 (by rfl) ⟨1209380, by rfl⟩ : syracuseStep 6450029 = 2418761) B2418761
theorem B2264935 : Blo 1340989 2264935 := bstep (se 1 (by rfl) ⟨1698701, by rfl⟩ : syracuseStep 2264935 = 3397403) B3397403
theorem B2012207 : Blo 1340989 2012207 := bstep (se 1 (by rfl) ⟨1509155, by rfl⟩ : syracuseStep 2012207 = 3018311) B3018311
theorem B4527575 : Blo 1340989 4527575 := bstep (se 1 (by rfl) ⟨3395681, by rfl⟩ : syracuseStep 4527575 = 6791363) B6791363
theorem B2013161 : Blo 1340989 2013161 := bstep (se 2 (by rfl) ⟨754935, by rfl⟩ : syracuseStep 2013161 = 1509871) B1509871
theorem B3021083 : Blo 1340989 3021083 := bstep (se 1 (by rfl) ⟨2265812, by rfl⟩ : syracuseStep 3021083 = 4531625) B4531625
theorem B2013695 : Blo 1340989 2013695 := bstep (se 1 (by rfl) ⟨1510271, by rfl⟩ : syracuseStep 2013695 = 3020543) B3020543
theorem B22919759 : Blo 1340989 22919759 := bstep (se 1 (by rfl) ⟨17189819, by rfl⟩ : syracuseStep 22919759 = 34379639) B34379639
theorem B2013791 : Blo 1340989 2013791 := bstep (se 1 (by rfl) ⟨1510343, by rfl⟩ : syracuseStep 2013791 = 3020687) B3020687
theorem B4528871 : Blo 1340989 4528871 := bstep (se 1 (by rfl) ⟨3396653, by rfl⟩ : syracuseStep 4528871 = 6793307) B6793307
theorem B1342567 : Blo 1340989 1342567 := bstep (se 1 (by rfl) ⟨1006925, by rfl⟩ : syracuseStep 1342567 = 2013851) B2013851
theorem B1342719 : Blo 1340989 1342719 := bstep (se 1 (by rfl) ⟨1007039, by rfl⟩ : syracuseStep 1342719 = 2014079) B2014079
theorem B41911607 : Blo 1340989 41911607 := bstep (se 1 (by rfl) ⟨31433705, by rfl⟩ : syracuseStep 41911607 = 62867411) B62867411
theorem B15279839 : Blo 1340989 15279839 := bstep (se 1 (by rfl) ⟨11459879, by rfl⟩ : syracuseStep 15279839 = 22919759) B22919759
theorem B3017609 : Blo 1340989 3017609 := bstep (se 2 (by rfl) ⟨1131603, by rfl⟩ : syracuseStep 3017609 = 2263207) B2263207
theorem B3018383 : Blo 1340989 3018383 := bstep (se 1 (by rfl) ⟨2263787, by rfl⟩ : syracuseStep 3018383 = 4527575) B4527575
theorem B84881803 : Blo 1340989 84881803 := bstep (se 1 (by rfl) ⟨63661352, by rfl⟩ : syracuseStep 84881803 = 127322705) B127322705
theorem B3019247 : Blo 1340989 3019247 := bstep (se 1 (by rfl) ⟨2264435, by rfl⟩ : syracuseStep 3019247 = 4528871) B4528871
theorem B3019913 : Blo 1340989 3019913 := bstep (se 2 (by rfl) ⟨1132467, by rfl⟩ : syracuseStep 3019913 = 2264935) B2264935
theorem B3823195 : Blo 1340989 3823195 := bstep (se 1 (by rfl) ⟨2867396, by rfl⟩ : syracuseStep 3823195 = 5734793) B5734793
theorem B7640831 : Blo 1340989 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B1341471 : Blo 1340989 1341471 := bstep (se 1 (by rfl) ⟨1006103, by rfl⟩ : syracuseStep 1341471 = 2012207) B2012207
theorem B1342107 : Blo 1340989 1342107 := bstep (se 1 (by rfl) ⟨1006580, by rfl⟩ : syracuseStep 1342107 = 2013161) B2013161
theorem B2014055 : Blo 1340989 2014055 := bstep (se 1 (by rfl) ⟨1510541, by rfl⟩ : syracuseStep 2014055 = 3021083) B3021083
theorem B1342463 : Blo 1340989 1342463 := bstep (se 1 (by rfl) ⟨1006847, by rfl⟩ : syracuseStep 1342463 = 2013695) B2013695
theorem B9804827 : Blo 1340989 9804827 := bstep (se 1 (by rfl) ⟨7353620, by rfl⟩ : syracuseStep 9804827 = 14707241) B14707241
theorem B1342527 : Blo 1340989 1342527 := bstep (se 1 (by rfl) ⟨1006895, by rfl⟩ : syracuseStep 1342527 = 2013791) B2013791
theorem B4300019 : Blo 1340989 4300019 := bstep (se 1 (by rfl) ⟨3225014, by rfl⟩ : syracuseStep 4300019 = 6450029) B6450029
theorem B5097593 : Blo 1340989 5097593 := bstep (se 2 (by rfl) ⟨1911597, by rfl⟩ : syracuseStep 5097593 = 3823195) B3823195
theorem B113175737 : Blo 1340989 113175737 := bstep (se 2 (by rfl) ⟨42440901, by rfl⟩ : syracuseStep 113175737 = 84881803) B84881803
theorem B10186559 : Blo 1340989 10186559 := bstep (se 1 (by rfl) ⟨7639919, by rfl⟩ : syracuseStep 10186559 = 15279839) B15279839
theorem B2011739 : Blo 1340989 2011739 := bstep (se 1 (by rfl) ⟨1508804, by rfl⟩ : syracuseStep 2011739 = 3017609) B3017609
theorem B2012255 : Blo 1340989 2012255 := bstep (se 1 (by rfl) ⟨1509191, by rfl⟩ : syracuseStep 2012255 = 3018383) B3018383
theorem B2012831 : Blo 1340989 2012831 := bstep (se 1 (by rfl) ⟨1509623, by rfl⟩ : syracuseStep 2012831 = 3019247) B3019247
theorem B2013275 : Blo 1340989 2013275 := bstep (se 1 (by rfl) ⟨1509956, by rfl⟩ : syracuseStep 2013275 = 3019913) B3019913
theorem B27941071 : Blo 1340989 27941071 := bstep (se 1 (by rfl) ⟨20955803, by rfl⟩ : syracuseStep 27941071 = 41911607) B41911607
theorem B5093887 : Blo 1340989 5093887 := bstep (se 1 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 5093887 = 7640831) B7640831
theorem B1342703 : Blo 1340989 1342703 := bstep (se 1 (by rfl) ⟨1007027, by rfl⟩ : syracuseStep 1342703 = 2014055) B2014055
theorem B6536551 : Blo 1340989 6536551 := bstep (se 1 (by rfl) ⟨4902413, by rfl⟩ : syracuseStep 6536551 = 9804827) B9804827
theorem B2866679 : Blo 1340989 2866679 := bstep (se 1 (by rfl) ⟨2150009, by rfl⟩ : syracuseStep 2866679 = 4300019) B4300019
theorem B6791849 : Blo 1340989 6791849 := bstep (se 2 (by rfl) ⟨2546943, by rfl⟩ : syracuseStep 6791849 = 5093887) B5093887
theorem B75450491 : Blo 1340989 75450491 := bstep (se 1 (by rfl) ⟨56587868, by rfl⟩ : syracuseStep 75450491 = 113175737) B113175737
theorem B1911119 : Blo 1340989 1911119 := bstep (se 1 (by rfl) ⟨1433339, by rfl⟩ : syracuseStep 1911119 = 2866679) B2866679
theorem B37254761 : Blo 1340989 37254761 := bstep (se 2 (by rfl) ⟨13970535, by rfl⟩ : syracuseStep 37254761 = 27941071) B27941071
theorem B1341159 : Blo 1340989 1341159 := bstep (se 1 (by rfl) ⟨1005869, by rfl⟩ : syracuseStep 1341159 = 2011739) B2011739
theorem B1341503 : Blo 1340989 1341503 := bstep (se 1 (by rfl) ⟨1006127, by rfl⟩ : syracuseStep 1341503 = 2012255) B2012255
theorem B1341887 : Blo 1340989 1341887 := bstep (se 1 (by rfl) ⟨1006415, by rfl⟩ : syracuseStep 1341887 = 2012831) B2012831
theorem B1342183 : Blo 1340989 1342183 := bstep (se 1 (by rfl) ⟨1006637, by rfl⟩ : syracuseStep 1342183 = 2013275) B2013275
theorem B3398395 : Blo 1340989 3398395 := bstep (se 1 (by rfl) ⟨2548796, by rfl⟩ : syracuseStep 3398395 = 5097593) B5097593
theorem B8715401 : Blo 1340989 8715401 := bstep (se 2 (by rfl) ⟨3268275, by rfl⟩ : syracuseStep 8715401 = 6536551) B6536551
theorem B6791039 : Blo 1340989 6791039 := bstep (se 1 (by rfl) ⟨5093279, by rfl⟩ : syracuseStep 6791039 = 10186559) B10186559
theorem B5096317 : Blo 1340989 5096317 := bstep (se 3 (by rfl) ⟨955559, by rfl⟩ : syracuseStep 5096317 = 1911119) B1911119
theorem B4531193 : Blo 1340989 4531193 := bstep (se 2 (by rfl) ⟨1699197, by rfl⟩ : syracuseStep 4531193 = 3398395) B3398395
theorem B5810267 : Blo 1340989 5810267 := bstep (se 1 (by rfl) ⟨4357700, by rfl⟩ : syracuseStep 5810267 = 8715401) B8715401
theorem B4527359 : Blo 1340989 4527359 := bstep (se 1 (by rfl) ⟨3395519, by rfl⟩ : syracuseStep 4527359 = 6791039) B6791039
theorem B4527899 : Blo 1340989 4527899 := bstep (se 1 (by rfl) ⟨3395924, by rfl⟩ : syracuseStep 4527899 = 6791849) B6791849
theorem B24836507 : Blo 1340989 24836507 := bstep (se 1 (by rfl) ⟨18627380, by rfl⟩ : syracuseStep 24836507 = 37254761) B37254761
theorem B804805237 : Blo 1340989 804805237 := bstep (se 5 (by rfl) ⟨37725245, by rfl⟩ : syracuseStep 804805237 = 75450491) B75450491
theorem B16557671 : Blo 1340989 16557671 := bstep (se 1 (by rfl) ⟨12418253, by rfl⟩ : syracuseStep 16557671 = 24836507) B24836507
theorem B3018239 : Blo 1340989 3018239 := bstep (se 1 (by rfl) ⟨2263679, by rfl⟩ : syracuseStep 3018239 = 4527359) B4527359
theorem B6795089 : Blo 1340989 6795089 := bstep (se 2 (by rfl) ⟨2548158, by rfl⟩ : syracuseStep 6795089 = 5096317) B5096317
theorem B3018599 : Blo 1340989 3018599 := bstep (se 1 (by rfl) ⟨2263949, by rfl⟩ : syracuseStep 3018599 = 4527899) B4527899
theorem B4292294597 : Blo 1340989 4292294597 := bstep (se 4 (by rfl) ⟨402402618, by rfl⟩ : syracuseStep 4292294597 = 804805237) B804805237
theorem B3020795 : Blo 1340989 3020795 := bstep (se 1 (by rfl) ⟨2265596, by rfl⟩ : syracuseStep 3020795 = 4531193) B4531193
theorem B3873511 : Blo 1340989 3873511 := bstep (se 1 (by rfl) ⟨2905133, by rfl⟩ : syracuseStep 3873511 = 5810267) B5810267
theorem B5164681 : Blo 1340989 5164681 := bstep (se 2 (by rfl) ⟨1936755, by rfl⟩ : syracuseStep 5164681 = 3873511) B3873511
theorem B11038447 : Blo 1340989 11038447 := bstep (se 1 (by rfl) ⟨8278835, by rfl⟩ : syracuseStep 11038447 = 16557671) B16557671
theorem B2012159 : Blo 1340989 2012159 := bstep (se 1 (by rfl) ⟨1509119, by rfl⟩ : syracuseStep 2012159 = 3018239) B3018239
theorem B2012399 : Blo 1340989 2012399 := bstep (se 1 (by rfl) ⟨1509299, by rfl⟩ : syracuseStep 2012399 = 3018599) B3018599
theorem B2861529731 : Blo 1340989 2861529731 := bstep (se 1 (by rfl) ⟨2146147298, by rfl⟩ : syracuseStep 2861529731 = 4292294597) B4292294597
theorem B2013863 : Blo 1340989 2013863 := bstep (se 1 (by rfl) ⟨1510397, by rfl⟩ : syracuseStep 2013863 = 3020795) B3020795
theorem B4530059 : Blo 1340989 4530059 := bstep (se 1 (by rfl) ⟨3397544, by rfl⟩ : syracuseStep 4530059 = 6795089) B6795089
theorem B58871717 : Blo 1340989 58871717 := bstep (se 4 (by rfl) ⟨5519223, by rfl⟩ : syracuseStep 58871717 = 11038447) B11038447
theorem B6886241 : Blo 1340989 6886241 := bstep (se 2 (by rfl) ⟨2582340, by rfl⟩ : syracuseStep 6886241 = 5164681) B5164681
theorem B3020039 : Blo 1340989 3020039 := bstep (se 1 (by rfl) ⟨2265029, by rfl⟩ : syracuseStep 3020039 = 4530059) B4530059
theorem B1341439 : Blo 1340989 1341439 := bstep (se 1 (by rfl) ⟨1006079, by rfl⟩ : syracuseStep 1341439 = 2012159) B2012159
theorem B1341599 : Blo 1340989 1341599 := bstep (se 1 (by rfl) ⟨1006199, by rfl⟩ : syracuseStep 1341599 = 2012399) B2012399
theorem B1907686487 : Blo 1340989 1907686487 := bstep (se 1 (by rfl) ⟨1430764865, by rfl⟩ : syracuseStep 1907686487 = 2861529731) B2861529731
theorem B1342575 : Blo 1340989 1342575 := bstep (se 1 (by rfl) ⟨1006931, by rfl⟩ : syracuseStep 1342575 = 2013863) B2013863
theorem B4590827 : Blo 1340989 4590827 := bstep (se 1 (by rfl) ⟨3443120, by rfl⟩ : syracuseStep 4590827 = 6886241) B6886241
theorem B2013359 : Blo 1340989 2013359 := bstep (se 1 (by rfl) ⟨1510019, by rfl⟩ : syracuseStep 2013359 = 3020039) B3020039
theorem B1271790991 : Blo 1340989 1271790991 := bstep (se 1 (by rfl) ⟨953843243, by rfl⟩ : syracuseStep 1271790991 = 1907686487) B1907686487
theorem B39247811 : Blo 1340989 39247811 := bstep (se 1 (by rfl) ⟨29435858, by rfl⟩ : syracuseStep 39247811 = 58871717) B58871717
theorem B1695721321 : Blo 1340989 1695721321 := bstep (se 2 (by rfl) ⟨635895495, by rfl⟩ : syracuseStep 1695721321 = 1271790991) B1271790991
theorem B3060551 : Blo 1340989 3060551 := bstep (se 1 (by rfl) ⟨2295413, by rfl⟩ : syracuseStep 3060551 = 4590827) B4590827
theorem B1342239 : Blo 1340989 1342239 := bstep (se 1 (by rfl) ⟨1006679, by rfl⟩ : syracuseStep 1342239 = 2013359) B2013359
theorem B26165207 : Blo 1340989 26165207 := bstep (se 1 (by rfl) ⟨19623905, by rfl⟩ : syracuseStep 26165207 = 39247811) B39247811
theorem B8161469 : Blo 1340989 8161469 := bstep (se 3 (by rfl) ⟨1530275, by rfl⟩ : syracuseStep 8161469 = 3060551) B3060551
theorem B2260961761 : Blo 1340989 2260961761 := bstep (se 2 (by rfl) ⟨847860660, by rfl⟩ : syracuseStep 2260961761 = 1695721321) B1695721321
theorem B17443471 : Blo 1340989 17443471 := bstep (se 1 (by rfl) ⟨13082603, by rfl⟩ : syracuseStep 17443471 = 26165207) B26165207
theorem B3014615681 : Blo 1340989 3014615681 := bstep (se 2 (by rfl) ⟨1130480880, by rfl⟩ : syracuseStep 3014615681 = 2260961761) B2260961761
theorem B23257961 : Blo 1340989 23257961 := bstep (se 2 (by rfl) ⟨8721735, by rfl⟩ : syracuseStep 23257961 = 17443471) B17443471
theorem B5440979 : Blo 1340989 5440979 := bstep (se 1 (by rfl) ⟨4080734, by rfl⟩ : syracuseStep 5440979 = 8161469) B8161469
theorem B2009743787 : Blo 1340989 2009743787 := bstep (se 1 (by rfl) ⟨1507307840, by rfl⟩ : syracuseStep 2009743787 = 3014615681) B3014615681
theorem B14509277 : Blo 1340989 14509277 := bstep (se 3 (by rfl) ⟨2720489, by rfl⟩ : syracuseStep 14509277 = 5440979) B5440979
theorem B15505307 : Blo 1340989 15505307 := bstep (se 1 (by rfl) ⟨11628980, by rfl⟩ : syracuseStep 15505307 = 23257961) B23257961
theorem B1339829191 : Blo 1340989 1339829191 := bstep (se 1 (by rfl) ⟨1004871893, by rfl⟩ : syracuseStep 1339829191 = 2009743787) B2009743787
theorem B9672851 : Blo 1340989 9672851 := bstep (se 1 (by rfl) ⟨7254638, by rfl⟩ : syracuseStep 9672851 = 14509277) B14509277
theorem B10336871 : Blo 1340989 10336871 := bstep (se 1 (by rfl) ⟨7752653, by rfl⟩ : syracuseStep 10336871 = 15505307) B15505307
theorem B1786438921 : Blo 1340989 1786438921 := bstep (se 2 (by rfl) ⟨669914595, by rfl⟩ : syracuseStep 1786438921 = 1339829191) B1339829191
theorem B6448567 : Blo 1340989 6448567 := bstep (se 1 (by rfl) ⟨4836425, by rfl⟩ : syracuseStep 6448567 = 9672851) B9672851
theorem B6891247 : Blo 1340989 6891247 := bstep (se 1 (by rfl) ⟨5168435, by rfl⟩ : syracuseStep 6891247 = 10336871) B10336871
theorem B2381918561 : Blo 1340989 2381918561 := bstep (se 2 (by rfl) ⟨893219460, by rfl⟩ : syracuseStep 2381918561 = 1786438921) B1786438921
theorem B8598089 : Blo 1340989 8598089 := bstep (se 2 (by rfl) ⟨3224283, by rfl⟩ : syracuseStep 8598089 = 6448567) B6448567
theorem B9188329 : Blo 1340989 9188329 := bstep (se 2 (by rfl) ⟨3445623, by rfl⟩ : syracuseStep 9188329 = 6891247) B6891247
theorem B1587945707 : Blo 1340989 1587945707 := bstep (se 1 (by rfl) ⟨1190959280, by rfl⟩ : syracuseStep 1587945707 = 2381918561) B2381918561
theorem B12251105 : Blo 1340989 12251105 := bstep (se 2 (by rfl) ⟨4594164, by rfl⟩ : syracuseStep 12251105 = 9188329) B9188329
theorem B5732059 : Blo 1340989 5732059 := bstep (se 1 (by rfl) ⟨4299044, by rfl⟩ : syracuseStep 5732059 = 8598089) B8598089
theorem B1058630471 : Blo 1340989 1058630471 := bstep (se 1 (by rfl) ⟨793972853, by rfl⟩ : syracuseStep 1058630471 = 1587945707) B1587945707
theorem B7642745 : Blo 1340989 7642745 := bstep (se 2 (by rfl) ⟨2866029, by rfl⟩ : syracuseStep 7642745 = 5732059) B5732059
theorem B8167403 : Blo 1340989 8167403 := bstep (se 1 (by rfl) ⟨6125552, by rfl⟩ : syracuseStep 8167403 = 12251105) B12251105
theorem B705753647 : Blo 1340989 705753647 := bstep (se 1 (by rfl) ⟨529315235, by rfl⟩ : syracuseStep 705753647 = 1058630471) B1058630471
theorem B21779741 : Blo 1340989 21779741 := bstep (se 3 (by rfl) ⟨4083701, by rfl⟩ : syracuseStep 21779741 = 8167403) B8167403
theorem B5095163 : Blo 1340989 5095163 := bstep (se 1 (by rfl) ⟨3821372, by rfl⟩ : syracuseStep 5095163 = 7642745) B7642745
theorem B470502431 : Blo 1340989 470502431 := bstep (se 1 (by rfl) ⟨352876823, by rfl⟩ : syracuseStep 470502431 = 705753647) B705753647
theorem B14519827 : Blo 1340989 14519827 := bstep (se 1 (by rfl) ⟨10889870, by rfl⟩ : syracuseStep 14519827 = 21779741) B21779741
theorem B3396775 : Blo 1340989 3396775 := bstep (se 1 (by rfl) ⟨2547581, by rfl⟩ : syracuseStep 3396775 = 5095163) B5095163
theorem B19359769 : Blo 1340989 19359769 := bstep (se 2 (by rfl) ⟨7259913, by rfl⟩ : syracuseStep 19359769 = 14519827) B14519827
theorem B313668287 : Blo 1340989 313668287 := bstep (se 1 (by rfl) ⟨235251215, by rfl⟩ : syracuseStep 313668287 = 470502431) B470502431
theorem B4529033 : Blo 1340989 4529033 := bstep (se 2 (by rfl) ⟨1698387, by rfl⟩ : syracuseStep 4529033 = 3396775) B3396775
theorem B25813025 : Blo 1340989 25813025 := bstep (se 2 (by rfl) ⟨9679884, by rfl⟩ : syracuseStep 25813025 = 19359769) B19359769
theorem B209112191 : Blo 1340989 209112191 := bstep (se 1 (by rfl) ⟨156834143, by rfl⟩ : syracuseStep 209112191 = 313668287) B313668287
theorem B3019355 : Blo 1340989 3019355 := bstep (se 1 (by rfl) ⟨2264516, by rfl⟩ : syracuseStep 3019355 = 4529033) B4529033
theorem B139408127 : Blo 1340989 139408127 := bstep (se 1 (by rfl) ⟨104556095, by rfl⟩ : syracuseStep 139408127 = 209112191) B209112191
theorem B17208683 : Blo 1340989 17208683 := bstep (se 1 (by rfl) ⟨12906512, by rfl⟩ : syracuseStep 17208683 = 25813025) B25813025
theorem B2012903 : Blo 1340989 2012903 := bstep (se 1 (by rfl) ⟨1509677, by rfl⟩ : syracuseStep 2012903 = 3019355) B3019355
theorem B92938751 : Blo 1340989 92938751 := bstep (se 1 (by rfl) ⟨69704063, by rfl⟩ : syracuseStep 92938751 = 139408127) B139408127
theorem B11472455 : Blo 1340989 11472455 := bstep (se 1 (by rfl) ⟨8604341, by rfl⟩ : syracuseStep 11472455 = 17208683) B17208683
theorem B1341935 : Blo 1340989 1341935 := bstep (se 1 (by rfl) ⟨1006451, by rfl⟩ : syracuseStep 1341935 = 2012903) B2012903
theorem B61959167 : Blo 1340989 61959167 := bstep (se 1 (by rfl) ⟨46469375, by rfl⟩ : syracuseStep 61959167 = 92938751) B92938751
theorem B7648303 : Blo 1340989 7648303 := bstep (se 1 (by rfl) ⟨5736227, by rfl⟩ : syracuseStep 7648303 = 11472455) B11472455
theorem B41306111 : Blo 1340989 41306111 := bstep (se 1 (by rfl) ⟨30979583, by rfl⟩ : syracuseStep 41306111 = 61959167) B61959167
theorem B10197737 : Blo 1340989 10197737 := bstep (se 2 (by rfl) ⟨3824151, by rfl⟩ : syracuseStep 10197737 = 7648303) B7648303
theorem B27537407 : Blo 1340989 27537407 := bstep (se 1 (by rfl) ⟨20653055, by rfl⟩ : syracuseStep 27537407 = 41306111) B41306111
theorem B6798491 : Blo 1340989 6798491 := bstep (se 1 (by rfl) ⟨5098868, by rfl⟩ : syracuseStep 6798491 = 10197737) B10197737
theorem B4532327 : Blo 1340989 4532327 := bstep (se 1 (by rfl) ⟨3399245, by rfl⟩ : syracuseStep 4532327 = 6798491) B6798491
theorem B18358271 : Blo 1340989 18358271 := bstep (se 1 (by rfl) ⟨13768703, by rfl⟩ : syracuseStep 18358271 = 27537407) B27537407
theorem B12238847 : Blo 1340989 12238847 := bstep (se 1 (by rfl) ⟨9179135, by rfl⟩ : syracuseStep 12238847 = 18358271) B18358271
theorem B3021551 : Blo 1340989 3021551 := bstep (se 1 (by rfl) ⟨2266163, by rfl⟩ : syracuseStep 3021551 = 4532327) B4532327
theorem B8159231 : Blo 1340989 8159231 := bstep (se 1 (by rfl) ⟨6119423, by rfl⟩ : syracuseStep 8159231 = 12238847) B12238847
theorem B2014367 : Blo 1340989 2014367 := bstep (se 1 (by rfl) ⟨1510775, by rfl⟩ : syracuseStep 2014367 = 3021551) B3021551
theorem B5439487 : Blo 1340989 5439487 := bstep (se 1 (by rfl) ⟨4079615, by rfl⟩ : syracuseStep 5439487 = 8159231) B8159231
theorem B1342911 : Blo 1340989 1342911 := bstep (se 1 (by rfl) ⟨1007183, by rfl⟩ : syracuseStep 1342911 = 2014367) B2014367
theorem B7252649 : Blo 1340989 7252649 := bstep (se 2 (by rfl) ⟨2719743, by rfl⟩ : syracuseStep 7252649 = 5439487) B5439487
theorem B4835099 : Blo 1340989 4835099 := bstep (se 1 (by rfl) ⟨3626324, by rfl⟩ : syracuseStep 4835099 = 7252649) B7252649
theorem B3223399 : Blo 1340989 3223399 := bstep (se 1 (by rfl) ⟨2417549, by rfl⟩ : syracuseStep 3223399 = 4835099) B4835099
theorem B4297865 : Blo 1340989 4297865 := bstep (se 2 (by rfl) ⟨1611699, by rfl⟩ : syracuseStep 4297865 = 3223399) B3223399
theorem B11460973 : Blo 1340989 11460973 := bstep (se 3 (by rfl) ⟨2148932, by rfl⟩ : syracuseStep 11460973 = 4297865) B4297865
theorem B15281297 : Blo 1340989 15281297 := bstep (se 2 (by rfl) ⟨5730486, by rfl⟩ : syracuseStep 15281297 = 11460973) B11460973
theorem B10187531 : Blo 1340989 10187531 := bstep (se 1 (by rfl) ⟨7640648, by rfl⟩ : syracuseStep 10187531 = 15281297) B15281297
theorem B6791687 : Blo 1340989 6791687 := bstep (se 1 (by rfl) ⟨5093765, by rfl⟩ : syracuseStep 6791687 = 10187531) B10187531
theorem B4527791 : Blo 1340989 4527791 := bstep (se 1 (by rfl) ⟨3395843, by rfl⟩ : syracuseStep 4527791 = 6791687) B6791687
theorem B3018527 : Blo 1340989 3018527 := bstep (se 1 (by rfl) ⟨2263895, by rfl⟩ : syracuseStep 3018527 = 4527791) B4527791
theorem B2012351 : Blo 1340989 2012351 := bstep (se 1 (by rfl) ⟨1509263, by rfl⟩ : syracuseStep 2012351 = 3018527) B3018527
theorem B1341567 : Blo 1340989 1341567 := bstep (se 1 (by rfl) ⟨1006175, by rfl⟩ : syracuseStep 1341567 = 2012351) B2012351

theorem C0 (j : ℕ) (h1 : 335247 ≤ j) (h2 : j ≤ 335746) : Blo 1340989 (4 * j + 3) := by
  interval_cases j
  · exact B1340991
  · exact B1340995
  · exact B1340999
  · exact B1341003
  · exact B1341007
  · exact B1341011
  · exact B1341015
  · exact B1341019
  · exact B1341023
  · exact B1341027
  · exact B1341031
  · exact B1341035
  · exact B1341039
  · exact B1341043
  · exact B1341047
  · exact B1341051
  · exact B1341055
  · exact B1341059
  · exact B1341063
  · exact B1341067
  · exact B1341071
  · exact B1341075
  · exact B1341079
  · exact B1341083
  · exact B1341087
  · exact B1341091
  · exact B1341095
  · exact B1341099
  · exact B1341103
  · exact B1341107
  · exact B1341111
  · exact B1341115
  · exact B1341119
  · exact B1341123
  · exact B1341127
  · exact B1341131
  · exact B1341135
  · exact B1341139
  · exact B1341143
  · exact B1341147
  · exact B1341151
  · exact B1341155
  · exact B1341159
  · exact B1341163
  · exact B1341167
  · exact B1341171
  · exact B1341175
  · exact B1341179
  · exact B1341183
  · exact B1341187
  · exact B1341191
  · exact B1341195
  · exact B1341199
  · exact B1341203
  · exact B1341207
  · exact B1341211
  · exact B1341215
  · exact B1341219
  · exact B1341223
  · exact B1341227
  · exact B1341231
  · exact B1341235
  · exact B1341239
  · exact B1341243
  · exact B1341247
  · exact B1341251
  · exact B1341255
  · exact B1341259
  · exact B1341263
  · exact B1341267
  · exact B1341271
  · exact B1341275
  · exact B1341279
  · exact B1341283
  · exact B1341287
  · exact B1341291
  · exact B1341295
  · exact B1341299
  · exact B1341303
  · exact B1341307
  · exact B1341311
  · exact B1341315
  · exact B1341319
  · exact B1341323
  · exact B1341327
  · exact B1341331
  · exact B1341335
  · exact B1341339
  · exact B1341343
  · exact B1341347
  · exact B1341351
  · exact B1341355
  · exact B1341359
  · exact B1341363
  · exact B1341367
  · exact B1341371
  · exact B1341375
  · exact B1341379
  · exact B1341383
  · exact B1341387
  · exact B1341391
  · exact B1341395
  · exact B1341399
  · exact B1341403
  · exact B1341407
  · exact B1341411
  · exact B1341415
  · exact B1341419
  · exact B1341423
  · exact B1341427
  · exact B1341431
  · exact B1341435
  · exact B1341439
  · exact B1341443
  · exact B1341447
  · exact B1341451
  · exact B1341455
  · exact B1341459
  · exact B1341463
  · exact B1341467
  · exact B1341471
  · exact B1341475
  · exact B1341479
  · exact B1341483
  · exact B1341487
  · exact B1341491
  · exact B1341495
  · exact B1341499
  · exact B1341503
  · exact B1341507
  · exact B1341511
  · exact B1341515
  · exact B1341519
  · exact B1341523
  · exact B1341527
  · exact B1341531
  · exact B1341535
  · exact B1341539
  · exact B1341543
  · exact B1341547
  · exact B1341551
  · exact B1341555
  · exact B1341559
  · exact B1341563
  · exact B1341567
  · exact B1341571
  · exact B1341575
  · exact B1341579
  · exact B1341583
  · exact B1341587
  · exact B1341591
  · exact B1341595
  · exact B1341599
  · exact B1341603
  · exact B1341607
  · exact B1341611
  · exact B1341615
  · exact B1341619
  · exact B1341623
  · exact B1341627
  · exact B1341631
  · exact B1341635
  · exact B1341639
  · exact B1341643
  · exact B1341647
  · exact B1341651
  · exact B1341655
  · exact B1341659
  · exact B1341663
  · exact B1341667
  · exact B1341671
  · exact B1341675
  · exact B1341679
  · exact B1341683
  · exact B1341687
  · exact B1341691
  · exact B1341695
  · exact B1341699
  · exact B1341703
  · exact B1341707
  · exact B1341711
  · exact B1341715
  · exact B1341719
  · exact B1341723
  · exact B1341727
  · exact B1341731
  · exact B1341735
  · exact B1341739
  · exact B1341743
  · exact B1341747
  · exact B1341751
  · exact B1341755
  · exact B1341759
  · exact B1341763
  · exact B1341767
  · exact B1341771
  · exact B1341775
  · exact B1341779
  · exact B1341783
  · exact B1341787
  · exact B1341791
  · exact B1341795
  · exact B1341799
  · exact B1341803
  · exact B1341807
  · exact B1341811
  · exact B1341815
  · exact B1341819
  · exact B1341823
  · exact B1341827
  · exact B1341831
  · exact B1341835
  · exact B1341839
  · exact B1341843
  · exact B1341847
  · exact B1341851
  · exact B1341855
  · exact B1341859
  · exact B1341863
  · exact B1341867
  · exact B1341871
  · exact B1341875
  · exact B1341879
  · exact B1341883
  · exact B1341887
  · exact B1341891
  · exact B1341895
  · exact B1341899
  · exact B1341903
  · exact B1341907
  · exact B1341911
  · exact B1341915
  · exact B1341919
  · exact B1341923
  · exact B1341927
  · exact B1341931
  · exact B1341935
  · exact B1341939
  · exact B1341943
  · exact B1341947
  · exact B1341951
  · exact B1341955
  · exact B1341959
  · exact B1341963
  · exact B1341967
  · exact B1341971
  · exact B1341975
  · exact B1341979
  · exact B1341983
  · exact B1341987
  · exact B1341991
  · exact B1341995
  · exact B1341999
  · exact B1342003
  · exact B1342007
  · exact B1342011
  · exact B1342015
  · exact B1342019
  · exact B1342023
  · exact B1342027
  · exact B1342031
  · exact B1342035
  · exact B1342039
  · exact B1342043
  · exact B1342047
  · exact B1342051
  · exact B1342055
  · exact B1342059
  · exact B1342063
  · exact B1342067
  · exact B1342071
  · exact B1342075
  · exact B1342079
  · exact B1342083
  · exact B1342087
  · exact B1342091
  · exact B1342095
  · exact B1342099
  · exact B1342103
  · exact B1342107
  · exact B1342111
  · exact B1342115
  · exact B1342119
  · exact B1342123
  · exact B1342127
  · exact B1342131
  · exact B1342135
  · exact B1342139
  · exact B1342143
  · exact B1342147
  · exact B1342151
  · exact B1342155
  · exact B1342159
  · exact B1342163
  · exact B1342167
  · exact B1342171
  · exact B1342175
  · exact B1342179
  · exact B1342183
  · exact B1342187
  · exact B1342191
  · exact B1342195
  · exact B1342199
  · exact B1342203
  · exact B1342207
  · exact B1342211
  · exact B1342215
  · exact B1342219
  · exact B1342223
  · exact B1342227
  · exact B1342231
  · exact B1342235
  · exact B1342239
  · exact B1342243
  · exact B1342247
  · exact B1342251
  · exact B1342255
  · exact B1342259
  · exact B1342263
  · exact B1342267
  · exact B1342271
  · exact B1342275
  · exact B1342279
  · exact B1342283
  · exact B1342287
  · exact B1342291
  · exact B1342295
  · exact B1342299
  · exact B1342303
  · exact B1342307
  · exact B1342311
  · exact B1342315
  · exact B1342319
  · exact B1342323
  · exact B1342327
  · exact B1342331
  · exact B1342335
  · exact B1342339
  · exact B1342343
  · exact B1342347
  · exact B1342351
  · exact B1342355
  · exact B1342359
  · exact B1342363
  · exact B1342367
  · exact B1342371
  · exact B1342375
  · exact B1342379
  · exact B1342383
  · exact B1342387
  · exact B1342391
  · exact B1342395
  · exact B1342399
  · exact B1342403
  · exact B1342407
  · exact B1342411
  · exact B1342415
  · exact B1342419
  · exact B1342423
  · exact B1342427
  · exact B1342431
  · exact B1342435
  · exact B1342439
  · exact B1342443
  · exact B1342447
  · exact B1342451
  · exact B1342455
  · exact B1342459
  · exact B1342463
  · exact B1342467
  · exact B1342471
  · exact B1342475
  · exact B1342479
  · exact B1342483
  · exact B1342487
  · exact B1342491
  · exact B1342495
  · exact B1342499
  · exact B1342503
  · exact B1342507
  · exact B1342511
  · exact B1342515
  · exact B1342519
  · exact B1342523
  · exact B1342527
  · exact B1342531
  · exact B1342535
  · exact B1342539
  · exact B1342543
  · exact B1342547
  · exact B1342551
  · exact B1342555
  · exact B1342559
  · exact B1342563
  · exact B1342567
  · exact B1342571
  · exact B1342575
  · exact B1342579
  · exact B1342583
  · exact B1342587
  · exact B1342591
  · exact B1342595
  · exact B1342599
  · exact B1342603
  · exact B1342607
  · exact B1342611
  · exact B1342615
  · exact B1342619
  · exact B1342623
  · exact B1342627
  · exact B1342631
  · exact B1342635
  · exact B1342639
  · exact B1342643
  · exact B1342647
  · exact B1342651
  · exact B1342655
  · exact B1342659
  · exact B1342663
  · exact B1342667
  · exact B1342671
  · exact B1342675
  · exact B1342679
  · exact B1342683
  · exact B1342687
  · exact B1342691
  · exact B1342695
  · exact B1342699
  · exact B1342703
  · exact B1342707
  · exact B1342711
  · exact B1342715
  · exact B1342719
  · exact B1342723
  · exact B1342727
  · exact B1342731
  · exact B1342735
  · exact B1342739
  · exact B1342743
  · exact B1342747
  · exact B1342751
  · exact B1342755
  · exact B1342759
  · exact B1342763
  · exact B1342767
  · exact B1342771
  · exact B1342775
  · exact B1342779
  · exact B1342783
  · exact B1342787
  · exact B1342791
  · exact B1342795
  · exact B1342799
  · exact B1342803
  · exact B1342807
  · exact B1342811
  · exact B1342815
  · exact B1342819
  · exact B1342823
  · exact B1342827
  · exact B1342831
  · exact B1342835
  · exact B1342839
  · exact B1342843
  · exact B1342847
  · exact B1342851
  · exact B1342855
  · exact B1342859
  · exact B1342863
  · exact B1342867
  · exact B1342871
  · exact B1342875
  · exact B1342879
  · exact B1342883
  · exact B1342887
  · exact B1342891
  · exact B1342895
  · exact B1342899
  · exact B1342903
  · exact B1342907
  · exact B1342911
  · exact B1342915
  · exact B1342919
  · exact B1342923
  · exact B1342927
  · exact B1342931
  · exact B1342935
  · exact B1342939
  · exact B1342943
  · exact B1342947
  · exact B1342951
  · exact B1342955
  · exact B1342959
  · exact B1342963
  · exact B1342967
  · exact B1342971
  · exact B1342975
  · exact B1342979
  · exact B1342983
  · exact B1342987

theorem solution (m : ℕ) (hlo : 1340989 ≤ m) (hhi : m ≤ 1342989) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 335247 ≤ j := by omega
    have hj2 : j ≤ 335746 := by omega
    have hb : Blo 1340989 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
