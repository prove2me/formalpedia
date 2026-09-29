-- Prove2me | solution 1 for syracuse_descends_range_1112627_1116627
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:40.480281+00:00
-- url     : https://prove2.me/submissions/d4aee49c-371a-401f-880b-a242b0ceb3d8

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


theorem B1671173 : Blo 1112627 1671173 := bbase (se 4 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 1671173 = 313345) (by norm_num)
theorem B2818061 : Blo 1112627 2818061 := bbase (se 3 (by rfl) ⟨528386, by rfl⟩ : syracuseStep 2818061 = 1056773) (by norm_num)
theorem B1671197 : Blo 1112627 1671197 := bbase (se 3 (by rfl) ⟨313349, by rfl⟩ : syracuseStep 1671197 = 626699) (by norm_num)
theorem B1671221 : Blo 1112627 1671221 := bbase (se 5 (by rfl) ⟨78338, by rfl⟩ : syracuseStep 1671221 = 156677) (by norm_num)
theorem B3768389 : Blo 1112627 3768389 := bbase (se 4 (by rfl) ⟨353286, by rfl⟩ : syracuseStep 3768389 = 706573) (by norm_num)
theorem B1671245 : Blo 1112627 1671245 := bbase (se 3 (by rfl) ⟨313358, by rfl⟩ : syracuseStep 1671245 = 626717) (by norm_num)
theorem B1671269 : Blo 1112627 1671269 := bbase (se 4 (by rfl) ⟨156681, by rfl⟩ : syracuseStep 1671269 = 313363) (by norm_num)
theorem B1671293 : Blo 1112627 1671293 := bbase (se 3 (by rfl) ⟨313367, by rfl⟩ : syracuseStep 1671293 = 626735) (by norm_num)
theorem B1671317 : Blo 1112627 1671317 := bbase (se 6 (by rfl) ⟨39171, by rfl⟩ : syracuseStep 1671317 = 78343) (by norm_num)
theorem B1409177 : Blo 1112627 1409177 := bbase (se 2 (by rfl) ⟨528441, by rfl⟩ : syracuseStep 1409177 = 1056883) (by norm_num)
theorem B3571877 : Blo 1112627 3571877 := bbase (se 4 (by rfl) ⟨334863, by rfl⟩ : syracuseStep 3571877 = 669727) (by norm_num)
theorem B1671341 : Blo 1112627 1671341 := bbase (se 3 (by rfl) ⟨313376, by rfl⟩ : syracuseStep 1671341 = 626753) (by norm_num)
theorem B1671365 : Blo 1112627 1671365 := bbase (se 4 (by rfl) ⟨156690, by rfl⟩ : syracuseStep 1671365 = 313381) (by norm_num)
theorem B2818253 : Blo 1112627 2818253 := bbase (se 3 (by rfl) ⟨528422, by rfl⟩ : syracuseStep 2818253 = 1056845) (by norm_num)
theorem B1409233 : Blo 1112627 1409233 := bbase (se 2 (by rfl) ⟨528462, by rfl⟩ : syracuseStep 1409233 = 1056925) (by norm_num)
theorem B1671389 : Blo 1112627 1671389 := bbase (se 3 (by rfl) ⟨313385, by rfl⟩ : syracuseStep 1671389 = 626771) (by norm_num)
theorem B1671413 : Blo 1112627 1671413 := bbase (se 5 (by rfl) ⟨78347, by rfl⟩ : syracuseStep 1671413 = 156695) (by norm_num)
theorem B1671437 : Blo 1112627 1671437 := bbase (se 3 (by rfl) ⟨313394, by rfl⟩ : syracuseStep 1671437 = 626789) (by norm_num)
theorem B4227349 : Blo 1112627 4227349 := bbase (se 6 (by rfl) ⟨99078, by rfl⟩ : syracuseStep 4227349 = 198157) (by norm_num)
theorem B1671461 : Blo 1112627 1671461 := bbase (se 4 (by rfl) ⟨156699, by rfl⟩ : syracuseStep 1671461 = 313399) (by norm_num)
theorem B1507621 : Blo 1112627 1507621 := bbase (se 4 (by rfl) ⟨141339, by rfl⟩ : syracuseStep 1507621 = 282679) (by norm_num)
theorem B1409329 : Blo 1112627 1409329 := bbase (se 2 (by rfl) ⟨528498, by rfl⟩ : syracuseStep 1409329 = 1056997) (by norm_num)
theorem B1671485 : Blo 1112627 1671485 := bbase (se 3 (by rfl) ⟨313403, by rfl⟩ : syracuseStep 1671485 = 626807) (by norm_num)
theorem B1671509 : Blo 1112627 1671509 := bbase (se 10 (by rfl) ⟨2448, by rfl⟩ : syracuseStep 1671509 = 4897) (by norm_num)
theorem B1671533 : Blo 1112627 1671533 := bbase (se 3 (by rfl) ⟨313412, by rfl⟩ : syracuseStep 1671533 = 626825) (by norm_num)
theorem B1671557 : Blo 1112627 1671557 := bbase (se 4 (by rfl) ⟨156708, by rfl⟩ : syracuseStep 1671557 = 313417) (by norm_num)
theorem B3178885 : Blo 1112627 3178885 := bbase (se 4 (by rfl) ⟨298020, by rfl⟩ : syracuseStep 3178885 = 596041) (by norm_num)
theorem B1671581 : Blo 1112627 1671581 := bbase (se 3 (by rfl) ⟨313421, by rfl⟩ : syracuseStep 1671581 = 626843) (by norm_num)
theorem B1671605 : Blo 1112627 1671605 := bbase (se 5 (by rfl) ⟨78356, by rfl⟩ : syracuseStep 1671605 = 156713) (by norm_num)
theorem B1671629 : Blo 1112627 1671629 := bbase (se 3 (by rfl) ⟨313430, by rfl⟩ : syracuseStep 1671629 = 626861) (by norm_num)
theorem B1409501 : Blo 1112627 1409501 := bbase (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) (by norm_num)
theorem B1671653 : Blo 1112627 1671653 := bbase (se 4 (by rfl) ⟨156717, by rfl⟩ : syracuseStep 1671653 = 313435) (by norm_num)
theorem B1671677 : Blo 1112627 1671677 := bbase (se 3 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 1671677 = 626879) (by norm_num)
theorem B1409557 : Blo 1112627 1409557 := bbase (se 6 (by rfl) ⟨33036, by rfl⟩ : syracuseStep 1409557 = 66073) (by norm_num)
theorem B1671701 : Blo 1112627 1671701 := bbase (se 6 (by rfl) ⟨39180, by rfl⟩ : syracuseStep 1671701 = 78361) (by norm_num)
theorem B2818597 : Blo 1112627 2818597 := bbase (se 4 (by rfl) ⟨264243, by rfl⟩ : syracuseStep 2818597 = 528487) (by norm_num)
theorem B1671725 : Blo 1112627 1671725 := bbase (se 3 (by rfl) ⟨313448, by rfl⟩ : syracuseStep 1671725 = 626897) (by norm_num)
theorem B4227653 : Blo 1112627 4227653 := bbase (se 4 (by rfl) ⟨396342, by rfl⟩ : syracuseStep 4227653 = 792685) (by norm_num)
theorem B1671749 : Blo 1112627 1671749 := bbase (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) (by norm_num)
theorem B1671773 : Blo 1112627 1671773 := bbase (se 3 (by rfl) ⟨313457, by rfl⟩ : syracuseStep 1671773 = 626915) (by norm_num)
theorem B1409653 : Blo 1112627 1409653 := bbase (se 5 (by rfl) ⟨66077, by rfl⟩ : syracuseStep 1409653 = 132155) (by norm_num)
theorem B1671797 : Blo 1112627 1671797 := bbase (se 5 (by rfl) ⟨78365, by rfl⟩ : syracuseStep 1671797 = 156731) (by norm_num)
theorem B1671821 : Blo 1112627 1671821 := bbase (se 3 (by rfl) ⟨313466, by rfl⟩ : syracuseStep 1671821 = 626933) (by norm_num)
theorem B2818709 : Blo 1112627 2818709 := bbase (se 6 (by rfl) ⟨66063, by rfl⟩ : syracuseStep 2818709 = 132127) (by norm_num)
theorem B1671845 : Blo 1112627 1671845 := bbase (se 4 (by rfl) ⟨156735, by rfl⟩ : syracuseStep 1671845 = 313471) (by norm_num)
theorem B5636789 : Blo 1112627 5636789 := bbase (se 5 (by rfl) ⟨264224, by rfl⟩ : syracuseStep 5636789 = 528449) (by norm_num)
theorem B1671869 : Blo 1112627 1671869 := bbase (se 3 (by rfl) ⟨313475, by rfl⟩ : syracuseStep 1671869 = 626951) (by norm_num)
theorem B1671893 : Blo 1112627 1671893 := bbase (se 7 (by rfl) ⟨19592, by rfl⟩ : syracuseStep 1671893 = 39185) (by norm_num)
theorem B1671917 : Blo 1112627 1671917 := bbase (se 3 (by rfl) ⟨313484, by rfl⟩ : syracuseStep 1671917 = 626969) (by norm_num)
theorem B1671941 : Blo 1112627 1671941 := bbase (se 4 (by rfl) ⟨156744, by rfl⟩ : syracuseStep 1671941 = 313489) (by norm_num)
theorem B1671965 : Blo 1112627 1671965 := bbase (se 3 (by rfl) ⟨313493, by rfl⟩ : syracuseStep 1671965 = 626987) (by norm_num)
theorem B1409825 : Blo 1112627 1409825 := bbase (se 2 (by rfl) ⟨528684, by rfl⟩ : syracuseStep 1409825 = 1057369) (by norm_num)
theorem B1671989 : Blo 1112627 1671989 := bbase (se 5 (by rfl) ⟨78374, by rfl⟩ : syracuseStep 1671989 = 156749) (by norm_num)
theorem B1672013 : Blo 1112627 1672013 := bbase (se 3 (by rfl) ⟨313502, by rfl⟩ : syracuseStep 1672013 = 627005) (by norm_num)
theorem B2818901 : Blo 1112627 2818901 := bbase (se 9 (by rfl) ⟨8258, by rfl⟩ : syracuseStep 2818901 = 16517) (by norm_num)
theorem B1409881 : Blo 1112627 1409881 := bbase (se 2 (by rfl) ⟨528705, by rfl⟩ : syracuseStep 1409881 = 1057411) (by norm_num)
theorem B1672037 : Blo 1112627 1672037 := bbase (se 4 (by rfl) ⟨156753, by rfl⟩ : syracuseStep 1672037 = 313507) (by norm_num)
theorem B1672061 : Blo 1112627 1672061 := bbase (se 3 (by rfl) ⟨313511, by rfl⟩ : syracuseStep 1672061 = 627023) (by norm_num)
theorem B1672085 : Blo 1112627 1672085 := bbase (se 6 (by rfl) ⟨39189, by rfl⟩ : syracuseStep 1672085 = 78379) (by norm_num)
theorem B3015589 : Blo 1112627 3015589 := bbase (se 4 (by rfl) ⟨282711, by rfl⟩ : syracuseStep 3015589 = 565423) (by norm_num)
theorem B1672109 : Blo 1112627 1672109 := bbase (se 3 (by rfl) ⟨313520, by rfl⟩ : syracuseStep 1672109 = 627041) (by norm_num)
theorem B1409977 : Blo 1112627 1409977 := bbase (se 2 (by rfl) ⟨528741, by rfl⟩ : syracuseStep 1409977 = 1057483) (by norm_num)
theorem B1672133 : Blo 1112627 1672133 := bbase (se 4 (by rfl) ⟨156762, by rfl⟩ : syracuseStep 1672133 = 313525) (by norm_num)
theorem B6357973 : Blo 1112627 6357973 := bbase (se 7 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 6357973 = 149015) (by norm_num)
theorem B1672157 : Blo 1112627 1672157 := bbase (se 3 (by rfl) ⟨313529, by rfl⟩ : syracuseStep 1672157 = 627059) (by norm_num)
theorem B1672181 : Blo 1112627 1672181 := bbase (se 5 (by rfl) ⟨78383, by rfl⟩ : syracuseStep 1672181 = 156767) (by norm_num)
theorem B1672205 : Blo 1112627 1672205 := bbase (se 3 (by rfl) ⟨313538, by rfl⟩ : syracuseStep 1672205 = 627077) (by norm_num)
theorem B1672229 : Blo 1112627 1672229 := bbase (se 4 (by rfl) ⟨156771, by rfl⟩ : syracuseStep 1672229 = 313543) (by norm_num)
theorem B1672253 : Blo 1112627 1672253 := bbase (se 3 (by rfl) ⟨313547, by rfl⟩ : syracuseStep 1672253 = 627095) (by norm_num)
theorem B1672277 : Blo 1112627 1672277 := bbase (se 8 (by rfl) ⟨9798, by rfl⟩ : syracuseStep 1672277 = 19597) (by norm_num)
theorem B1410149 : Blo 1112627 1410149 := bbase (se 4 (by rfl) ⟨132201, by rfl⟩ : syracuseStep 1410149 = 264403) (by norm_num)
theorem B1672301 : Blo 1112627 1672301 := bbase (se 3 (by rfl) ⟨313556, by rfl⟩ : syracuseStep 1672301 = 627113) (by norm_num)
theorem B1672325 : Blo 1112627 1672325 := bbase (se 4 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 1672325 = 313561) (by norm_num)
theorem B1410205 : Blo 1112627 1410205 := bbase (se 3 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 1410205 = 528827) (by norm_num)
theorem B1672349 : Blo 1112627 1672349 := bbase (se 3 (by rfl) ⟨313565, by rfl⟩ : syracuseStep 1672349 = 627131) (by norm_num)
theorem B2819245 : Blo 1112627 2819245 := bbase (se 3 (by rfl) ⟨528608, by rfl⟩ : syracuseStep 2819245 = 1057217) (by norm_num)
theorem B1672373 : Blo 1112627 1672373 := bbase (se 5 (by rfl) ⟨78392, by rfl⟩ : syracuseStep 1672373 = 156785) (by norm_num)
theorem B1672397 : Blo 1112627 1672397 := bbase (se 3 (by rfl) ⟨313574, by rfl⟩ : syracuseStep 1672397 = 627149) (by norm_num)
theorem B1672421 : Blo 1112627 1672421 := bbase (se 4 (by rfl) ⟨156789, by rfl⟩ : syracuseStep 1672421 = 313579) (by norm_num)
theorem B1410301 : Blo 1112627 1410301 := bbase (se 3 (by rfl) ⟨264431, by rfl⟩ : syracuseStep 1410301 = 528863) (by norm_num)
theorem B1672445 : Blo 1112627 1672445 := bbase (se 3 (by rfl) ⟨313583, by rfl⟩ : syracuseStep 1672445 = 627167) (by norm_num)
theorem B4818197 : Blo 1112627 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B1672469 : Blo 1112627 1672469 := bbase (se 6 (by rfl) ⟨39198, by rfl⟩ : syracuseStep 1672469 = 78397) (by norm_num)
theorem B2819357 : Blo 1112627 2819357 := bbase (se 3 (by rfl) ⟨528629, by rfl⟩ : syracuseStep 2819357 = 1057259) (by norm_num)
theorem B1672493 : Blo 1112627 1672493 := bbase (se 3 (by rfl) ⟨313592, by rfl⟩ : syracuseStep 1672493 = 627185) (by norm_num)
theorem B1672517 : Blo 1112627 1672517 := bbase (se 4 (by rfl) ⟨156798, by rfl⟩ : syracuseStep 1672517 = 313597) (by norm_num)
theorem B1672541 : Blo 1112627 1672541 := bbase (se 3 (by rfl) ⟨313601, by rfl⟩ : syracuseStep 1672541 = 627203) (by norm_num)
theorem B1672565 : Blo 1112627 1672565 := bbase (se 5 (by rfl) ⟨78401, by rfl⟩ : syracuseStep 1672565 = 156803) (by norm_num)
theorem B1672589 : Blo 1112627 1672589 := bbase (se 3 (by rfl) ⟨313610, by rfl⟩ : syracuseStep 1672589 = 627221) (by norm_num)
theorem B1672613 : Blo 1112627 1672613 := bbase (se 4 (by rfl) ⟨156807, by rfl⟩ : syracuseStep 1672613 = 313615) (by norm_num)
theorem B1410473 : Blo 1112627 1410473 := bbase (se 2 (by rfl) ⟨528927, by rfl⟩ : syracuseStep 1410473 = 1057855) (by norm_num)
theorem B1672637 : Blo 1112627 1672637 := bbase (se 3 (by rfl) ⟨313619, by rfl⟩ : syracuseStep 1672637 = 627239) (by norm_num)
theorem B1672661 : Blo 1112627 1672661 := bbase (se 7 (by rfl) ⟨19601, by rfl⟩ : syracuseStep 1672661 = 39203) (by norm_num)
theorem B2819549 : Blo 1112627 2819549 := bbase (se 3 (by rfl) ⟨528665, by rfl⟩ : syracuseStep 2819549 = 1057331) (by norm_num)
theorem B1410529 : Blo 1112627 1410529 := bbase (se 2 (by rfl) ⟨528948, by rfl⟩ : syracuseStep 1410529 = 1057897) (by norm_num)
theorem B1672685 : Blo 1112627 1672685 := bbase (se 3 (by rfl) ⟨313628, by rfl⟩ : syracuseStep 1672685 = 627257) (by norm_num)
theorem B1672709 : Blo 1112627 1672709 := bbase (se 4 (by rfl) ⟨156816, by rfl⟩ : syracuseStep 1672709 = 313633) (by norm_num)
theorem B1672733 : Blo 1112627 1672733 := bbase (se 3 (by rfl) ⟨313637, by rfl⟩ : syracuseStep 1672733 = 627275) (by norm_num)
theorem B2033189 : Blo 1112627 2033189 := bbase (se 4 (by rfl) ⟨190611, by rfl⟩ : syracuseStep 2033189 = 381223) (by norm_num)
theorem B1672757 : Blo 1112627 1672757 := bbase (se 5 (by rfl) ⟨78410, by rfl⟩ : syracuseStep 1672757 = 156821) (by norm_num)
theorem B1410625 : Blo 1112627 1410625 := bbase (se 2 (by rfl) ⟨528984, by rfl⟩ : syracuseStep 1410625 = 1057969) (by norm_num)
theorem B1672781 : Blo 1112627 1672781 := bbase (se 3 (by rfl) ⟨313646, by rfl⟩ : syracuseStep 1672781 = 627293) (by norm_num)
theorem B1672805 : Blo 1112627 1672805 := bbase (se 4 (by rfl) ⟨156825, by rfl⟩ : syracuseStep 1672805 = 313651) (by norm_num)
theorem B1672829 : Blo 1112627 1672829 := bbase (se 3 (by rfl) ⟨313655, by rfl⟩ : syracuseStep 1672829 = 627311) (by norm_num)
theorem B1672853 : Blo 1112627 1672853 := bbase (se 6 (by rfl) ⟨39207, by rfl⟩ : syracuseStep 1672853 = 78415) (by norm_num)
theorem B1672877 : Blo 1112627 1672877 := bbase (se 3 (by rfl) ⟨313664, by rfl⟩ : syracuseStep 1672877 = 627329) (by norm_num)
theorem B1672901 : Blo 1112627 1672901 := bbase (se 4 (by rfl) ⟨156834, by rfl⟩ : syracuseStep 1672901 = 313669) (by norm_num)
theorem B1672925 : Blo 1112627 1672925 := bbase (se 3 (by rfl) ⟨313673, by rfl⟩ : syracuseStep 1672925 = 627347) (by norm_num)
theorem B1410797 : Blo 1112627 1410797 := bbase (se 3 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 1410797 = 529049) (by norm_num)
theorem B1672949 : Blo 1112627 1672949 := bbase (se 5 (by rfl) ⟨78419, by rfl⟩ : syracuseStep 1672949 = 156839) (by norm_num)
theorem B1672973 : Blo 1112627 1672973 := bbase (se 3 (by rfl) ⟨313682, by rfl⟩ : syracuseStep 1672973 = 627365) (by norm_num)
theorem B19040021 : Blo 1112627 19040021 := bbase (se 6 (by rfl) ⟨446250, by rfl⟩ : syracuseStep 19040021 = 892501) (by norm_num)
theorem B1410853 : Blo 1112627 1410853 := bbase (se 4 (by rfl) ⟨132267, by rfl⟩ : syracuseStep 1410853 = 264535) (by norm_num)
theorem B1672997 : Blo 1112627 1672997 := bbase (se 4 (by rfl) ⟨156843, by rfl⟩ : syracuseStep 1672997 = 313687) (by norm_num)
theorem B2819893 : Blo 1112627 2819893 := bbase (se 5 (by rfl) ⟨132182, by rfl⟩ : syracuseStep 2819893 = 264365) (by norm_num)
theorem B1673021 : Blo 1112627 1673021 := bbase (se 3 (by rfl) ⟨313691, by rfl⟩ : syracuseStep 1673021 = 627383) (by norm_num)
theorem B1607509 : Blo 1112627 1607509 := bbase (se 9 (by rfl) ⟨4709, by rfl⟩ : syracuseStep 1607509 = 9419) (by norm_num)
theorem B1673045 : Blo 1112627 1673045 := bbase (se 9 (by rfl) ⟨4901, by rfl⟩ : syracuseStep 1673045 = 9803) (by norm_num)
theorem B1673069 : Blo 1112627 1673069 := bbase (se 3 (by rfl) ⟨313700, by rfl⟩ : syracuseStep 1673069 = 627401) (by norm_num)
theorem B1410949 : Blo 1112627 1410949 := bbase (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) (by norm_num)
theorem B1673093 : Blo 1112627 1673093 := bbase (se 4 (by rfl) ⟨156852, by rfl⟩ : syracuseStep 1673093 = 313705) (by norm_num)
theorem B1673117 : Blo 1112627 1673117 := bbase (se 3 (by rfl) ⟨313709, by rfl⟩ : syracuseStep 1673117 = 627419) (by norm_num)
theorem B2820005 : Blo 1112627 2820005 := bbase (se 4 (by rfl) ⟨264375, by rfl⟩ : syracuseStep 2820005 = 528751) (by norm_num)
theorem B1673141 : Blo 1112627 1673141 := bbase (se 5 (by rfl) ⟨78428, by rfl⟩ : syracuseStep 1673141 = 156857) (by norm_num)
theorem B5638085 : Blo 1112627 5638085 := bbase (se 4 (by rfl) ⟨528570, by rfl⟩ : syracuseStep 5638085 = 1057141) (by norm_num)
theorem B1673165 : Blo 1112627 1673165 := bbase (se 3 (by rfl) ⟨313718, by rfl⟩ : syracuseStep 1673165 = 627437) (by norm_num)
theorem B1673189 : Blo 1112627 1673189 := bbase (se 4 (by rfl) ⟨156861, by rfl⟩ : syracuseStep 1673189 = 313723) (by norm_num)
theorem B1673213 : Blo 1112627 1673213 := bbase (se 3 (by rfl) ⟨313727, by rfl⟩ : syracuseStep 1673213 = 627455) (by norm_num)
theorem B1673237 : Blo 1112627 1673237 := bbase (se 6 (by rfl) ⟨39216, by rfl⟩ : syracuseStep 1673237 = 78433) (by norm_num)
theorem B1673261 : Blo 1112627 1673261 := bbase (se 3 (by rfl) ⟨313736, by rfl⟩ : syracuseStep 1673261 = 627473) (by norm_num)
theorem B1411121 : Blo 1112627 1411121 := bbase (se 2 (by rfl) ⟨529170, by rfl⟩ : syracuseStep 1411121 = 1058341) (by norm_num)
theorem B1673285 : Blo 1112627 1673285 := bbase (se 4 (by rfl) ⟨156870, by rfl⟩ : syracuseStep 1673285 = 313741) (by norm_num)
theorem B1673309 : Blo 1112627 1673309 := bbase (se 3 (by rfl) ⟨313745, by rfl⟩ : syracuseStep 1673309 = 627491) (by norm_num)
theorem B2820197 : Blo 1112627 2820197 := bbase (se 4 (by rfl) ⟨264393, by rfl⟩ : syracuseStep 2820197 = 528787) (by norm_num)
theorem B1411177 : Blo 1112627 1411177 := bbase (se 2 (by rfl) ⟨529191, by rfl⟩ : syracuseStep 1411177 = 1058383) (by norm_num)
theorem B1673333 : Blo 1112627 1673333 := bbase (se 5 (by rfl) ⟨78437, by rfl⟩ : syracuseStep 1673333 = 156875) (by norm_num)
theorem B1673357 : Blo 1112627 1673357 := bbase (se 3 (by rfl) ⟨313754, by rfl⟩ : syracuseStep 1673357 = 627509) (by norm_num)
theorem B1673381 : Blo 1112627 1673381 := bbase (se 4 (by rfl) ⟨156879, by rfl⟩ : syracuseStep 1673381 = 313759) (by norm_num)
theorem B1673405 : Blo 1112627 1673405 := bbase (se 3 (by rfl) ⟨313763, by rfl⟩ : syracuseStep 1673405 = 627527) (by norm_num)
theorem B1411273 : Blo 1112627 1411273 := bbase (se 2 (by rfl) ⟨529227, by rfl⟩ : syracuseStep 1411273 = 1058455) (by norm_num)
theorem B1673429 : Blo 1112627 1673429 := bbase (se 7 (by rfl) ⟨19610, by rfl⟩ : syracuseStep 1673429 = 39221) (by norm_num)
theorem B9537749 : Blo 1112627 9537749 := bbase (se 7 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 9537749 = 223541) (by norm_num)
theorem B1673453 : Blo 1112627 1673453 := bbase (se 3 (by rfl) ⟨313772, by rfl⟩ : syracuseStep 1673453 = 627545) (by norm_num)
theorem B1673477 : Blo 1112627 1673477 := bbase (se 4 (by rfl) ⟨156888, by rfl⟩ : syracuseStep 1673477 = 313777) (by norm_num)
theorem B7145749 : Blo 1112627 7145749 := bbase (se 6 (by rfl) ⟨167478, by rfl⟩ : syracuseStep 7145749 = 334957) (by norm_num)
theorem B1673501 : Blo 1112627 1673501 := bbase (se 3 (by rfl) ⟨313781, by rfl⟩ : syracuseStep 1673501 = 627563) (by norm_num)
theorem B1673525 : Blo 1112627 1673525 := bbase (se 5 (by rfl) ⟨78446, by rfl⟩ : syracuseStep 1673525 = 156893) (by norm_num)
theorem B1673549 : Blo 1112627 1673549 := bbase (se 3 (by rfl) ⟨313790, by rfl⟩ : syracuseStep 1673549 = 627581) (by norm_num)
theorem B1673573 : Blo 1112627 1673573 := bbase (se 4 (by rfl) ⟨156897, by rfl⟩ : syracuseStep 1673573 = 313795) (by norm_num)
theorem B1411445 : Blo 1112627 1411445 := bbase (se 5 (by rfl) ⟨66161, by rfl⟩ : syracuseStep 1411445 = 132323) (by norm_num)
theorem B1673597 : Blo 1112627 1673597 := bbase (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) (by norm_num)
theorem B1673621 : Blo 1112627 1673621 := bbase (se 6 (by rfl) ⟨39225, by rfl⟩ : syracuseStep 1673621 = 78451) (by norm_num)
theorem B1411501 : Blo 1112627 1411501 := bbase (se 3 (by rfl) ⟨264656, by rfl⟩ : syracuseStep 1411501 = 529313) (by norm_num)
theorem B1673645 : Blo 1112627 1673645 := bbase (se 3 (by rfl) ⟨313808, by rfl⟩ : syracuseStep 1673645 = 627617) (by norm_num)
theorem B2820541 : Blo 1112627 2820541 := bbase (se 3 (by rfl) ⟨528851, by rfl⟩ : syracuseStep 2820541 = 1057703) (by norm_num)
theorem B1673669 : Blo 1112627 1673669 := bbase (se 4 (by rfl) ⟨156906, by rfl⟩ : syracuseStep 1673669 = 313813) (by norm_num)
theorem B1673693 : Blo 1112627 1673693 := bbase (se 3 (by rfl) ⟨313817, by rfl⟩ : syracuseStep 1673693 = 627635) (by norm_num)
theorem B1673717 : Blo 1112627 1673717 := bbase (se 5 (by rfl) ⟨78455, by rfl⟩ : syracuseStep 1673717 = 156911) (by norm_num)
theorem B1411597 : Blo 1112627 1411597 := bbase (se 3 (by rfl) ⟨264674, by rfl⟩ : syracuseStep 1411597 = 529349) (by norm_num)
theorem B1673741 : Blo 1112627 1673741 := bbase (se 3 (by rfl) ⟨313826, by rfl⟩ : syracuseStep 1673741 = 627653) (by norm_num)
theorem B1673765 : Blo 1112627 1673765 := bbase (se 4 (by rfl) ⟨156915, by rfl⟩ : syracuseStep 1673765 = 313831) (by norm_num)
theorem B2820653 : Blo 1112627 2820653 := bbase (se 3 (by rfl) ⟨528872, by rfl⟩ : syracuseStep 2820653 = 1057745) (by norm_num)
theorem B1673789 : Blo 1112627 1673789 := bbase (se 3 (by rfl) ⟨313835, by rfl⟩ : syracuseStep 1673789 = 627671) (by norm_num)
theorem B2263621 : Blo 1112627 2263621 := bbase (se 4 (by rfl) ⟨212214, by rfl⟩ : syracuseStep 2263621 = 424429) (by norm_num)
theorem B1673813 : Blo 1112627 1673813 := bbase (se 8 (by rfl) ⟨9807, by rfl⟩ : syracuseStep 1673813 = 19615) (by norm_num)
theorem B1673837 : Blo 1112627 1673837 := bbase (se 3 (by rfl) ⟨313844, by rfl⟩ : syracuseStep 1673837 = 627689) (by norm_num)
theorem B4229765 : Blo 1112627 4229765 := bbase (se 4 (by rfl) ⟨396540, by rfl⟩ : syracuseStep 4229765 = 793081) (by norm_num)
theorem B1673861 : Blo 1112627 1673861 := bbase (se 4 (by rfl) ⟨156924, by rfl⟩ : syracuseStep 1673861 = 313849) (by norm_num)
theorem B1673885 : Blo 1112627 1673885 := bbase (se 3 (by rfl) ⟨313853, by rfl⟩ : syracuseStep 1673885 = 627707) (by norm_num)
theorem B8456885 : Blo 1112627 8456885 := bbase (se 5 (by rfl) ⟨396416, by rfl⟩ : syracuseStep 8456885 = 792833) (by norm_num)
theorem B1673909 : Blo 1112627 1673909 := bbase (se 5 (by rfl) ⟨78464, by rfl⟩ : syracuseStep 1673909 = 156929) (by norm_num)
theorem B1411769 : Blo 1112627 1411769 := bbase (se 2 (by rfl) ⟨529413, by rfl⟩ : syracuseStep 1411769 = 1058827) (by norm_num)
theorem B1673933 : Blo 1112627 1673933 := bbase (se 3 (by rfl) ⟨313862, by rfl⟩ : syracuseStep 1673933 = 627725) (by norm_num)
theorem B1673957 : Blo 1112627 1673957 := bbase (se 4 (by rfl) ⟨156933, by rfl⟩ : syracuseStep 1673957 = 313867) (by norm_num)
theorem B2820845 : Blo 1112627 2820845 := bbase (se 3 (by rfl) ⟨528908, by rfl⟩ : syracuseStep 2820845 = 1057817) (by norm_num)
theorem B1411825 : Blo 1112627 1411825 := bbase (se 2 (by rfl) ⟨529434, by rfl⟩ : syracuseStep 1411825 = 1058869) (by norm_num)
theorem B1673981 : Blo 1112627 1673981 := bbase (se 3 (by rfl) ⟨313871, by rfl⟩ : syracuseStep 1673981 = 627743) (by norm_num)
theorem B1674005 : Blo 1112627 1674005 := bbase (se 6 (by rfl) ⟨39234, by rfl⟩ : syracuseStep 1674005 = 78469) (by norm_num)
theorem B1674029 : Blo 1112627 1674029 := bbase (se 3 (by rfl) ⟨313880, by rfl⟩ : syracuseStep 1674029 = 627761) (by norm_num)
theorem B1674053 : Blo 1112627 1674053 := bbase (se 4 (by rfl) ⟨156942, by rfl⟩ : syracuseStep 1674053 = 313885) (by norm_num)
theorem B1411921 : Blo 1112627 1411921 := bbase (se 2 (by rfl) ⟨529470, by rfl⟩ : syracuseStep 1411921 = 1058941) (by norm_num)
theorem B1674077 : Blo 1112627 1674077 := bbase (se 3 (by rfl) ⟨313889, by rfl⟩ : syracuseStep 1674077 = 627779) (by norm_num)
theorem B1674101 : Blo 1112627 1674101 := bbase (se 5 (by rfl) ⟨78473, by rfl⟩ : syracuseStep 1674101 = 156947) (by norm_num)
theorem B1674125 : Blo 1112627 1674125 := bbase (se 3 (by rfl) ⟨313898, by rfl⟩ : syracuseStep 1674125 = 627797) (by norm_num)
theorem B4230053 : Blo 1112627 4230053 := bbase (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) (by norm_num)
theorem B1674149 : Blo 1112627 1674149 := bbase (se 4 (by rfl) ⟨156951, by rfl⟩ : syracuseStep 1674149 = 313903) (by norm_num)
theorem B1674173 : Blo 1112627 1674173 := bbase (se 3 (by rfl) ⟨313907, by rfl⟩ : syracuseStep 1674173 = 627815) (by norm_num)
theorem B1674197 : Blo 1112627 1674197 := bbase (se 7 (by rfl) ⟨19619, by rfl⟩ : syracuseStep 1674197 = 39239) (by norm_num)
theorem B1674221 : Blo 1112627 1674221 := bbase (se 3 (by rfl) ⟨313916, by rfl⟩ : syracuseStep 1674221 = 627833) (by norm_num)
theorem B1412093 : Blo 1112627 1412093 := bbase (se 3 (by rfl) ⟨264767, by rfl⟩ : syracuseStep 1412093 = 529535) (by norm_num)
theorem B1674245 : Blo 1112627 1674245 := bbase (se 4 (by rfl) ⟨156960, by rfl⟩ : syracuseStep 1674245 = 313921) (by norm_num)
theorem B1674269 : Blo 1112627 1674269 := bbase (se 3 (by rfl) ⟨313925, by rfl⟩ : syracuseStep 1674269 = 627851) (by norm_num)
theorem B1412149 : Blo 1112627 1412149 := bbase (se 5 (by rfl) ⟨66194, by rfl⟩ : syracuseStep 1412149 = 132389) (by norm_num)
theorem B1674293 : Blo 1112627 1674293 := bbase (se 5 (by rfl) ⟨78482, by rfl⟩ : syracuseStep 1674293 = 156965) (by norm_num)
theorem B2821189 : Blo 1112627 2821189 := bbase (se 4 (by rfl) ⟨264486, by rfl⟩ : syracuseStep 2821189 = 528973) (by norm_num)
theorem B1674317 : Blo 1112627 1674317 := bbase (se 3 (by rfl) ⟨313934, by rfl⟩ : syracuseStep 1674317 = 627869) (by norm_num)
theorem B1674341 : Blo 1112627 1674341 := bbase (se 4 (by rfl) ⟨156969, by rfl⟩ : syracuseStep 1674341 = 313939) (by norm_num)
theorem B1674365 : Blo 1112627 1674365 := bbase (se 3 (by rfl) ⟨313943, by rfl⟩ : syracuseStep 1674365 = 627887) (by norm_num)
theorem B1412245 : Blo 1112627 1412245 := bbase (se 6 (by rfl) ⟨33099, by rfl⟩ : syracuseStep 1412245 = 66199) (by norm_num)
theorem B1674389 : Blo 1112627 1674389 := bbase (se 6 (by rfl) ⟨39243, by rfl⟩ : syracuseStep 1674389 = 78487) (by norm_num)
theorem B1674413 : Blo 1112627 1674413 := bbase (se 3 (by rfl) ⟨313952, by rfl⟩ : syracuseStep 1674413 = 627905) (by norm_num)
theorem B2821301 : Blo 1112627 2821301 := bbase (se 5 (by rfl) ⟨132248, by rfl⟩ : syracuseStep 2821301 = 264497) (by norm_num)
theorem B1674437 : Blo 1112627 1674437 := bbase (se 4 (by rfl) ⟨156978, by rfl⟩ : syracuseStep 1674437 = 313957) (by norm_num)
theorem B5639381 : Blo 1112627 5639381 := bbase (se 7 (by rfl) ⟨66086, by rfl⟩ : syracuseStep 5639381 = 132173) (by norm_num)
theorem B1674461 : Blo 1112627 1674461 := bbase (se 3 (by rfl) ⟨313961, by rfl⟩ : syracuseStep 1674461 = 627923) (by norm_num)
theorem B1674485 : Blo 1112627 1674485 := bbase (se 5 (by rfl) ⟨78491, by rfl⟩ : syracuseStep 1674485 = 156983) (by norm_num)
theorem B1674509 : Blo 1112627 1674509 := bbase (se 3 (by rfl) ⟨313970, by rfl⟩ : syracuseStep 1674509 = 627941) (by norm_num)
theorem B9506069 : Blo 1112627 9506069 := bbase (se 6 (by rfl) ⟨222798, by rfl⟩ : syracuseStep 9506069 = 445597) (by norm_num)
theorem B1674533 : Blo 1112627 1674533 := bbase (se 4 (by rfl) ⟨156987, by rfl⟩ : syracuseStep 1674533 = 313975) (by norm_num)
theorem B1674557 : Blo 1112627 1674557 := bbase (se 3 (by rfl) ⟨313979, by rfl⟩ : syracuseStep 1674557 = 627959) (by norm_num)
theorem B1412417 : Blo 1112627 1412417 := bbase (se 2 (by rfl) ⟨529656, by rfl⟩ : syracuseStep 1412417 = 1059313) (by norm_num)
theorem B1674581 : Blo 1112627 1674581 := bbase (se 11 (by rfl) ⟨1226, by rfl⟩ : syracuseStep 1674581 = 2453) (by norm_num)
theorem B1674605 : Blo 1112627 1674605 := bbase (se 3 (by rfl) ⟨313988, by rfl⟩ : syracuseStep 1674605 = 627977) (by norm_num)
theorem B2821493 : Blo 1112627 2821493 := bbase (se 5 (by rfl) ⟨132257, by rfl⟩ : syracuseStep 2821493 = 264515) (by norm_num)
theorem B1412473 : Blo 1112627 1412473 := bbase (se 2 (by rfl) ⟨529677, by rfl⟩ : syracuseStep 1412473 = 1059355) (by norm_num)
theorem B1674629 : Blo 1112627 1674629 := bbase (se 4 (by rfl) ⟨156996, by rfl⟩ : syracuseStep 1674629 = 313993) (by norm_num)
theorem B1674653 : Blo 1112627 1674653 := bbase (se 3 (by rfl) ⟨313997, by rfl⟩ : syracuseStep 1674653 = 627995) (by norm_num)
theorem B1674677 : Blo 1112627 1674677 := bbase (se 5 (by rfl) ⟨78500, by rfl⟩ : syracuseStep 1674677 = 157001) (by norm_num)
theorem B1674701 : Blo 1112627 1674701 := bbase (se 3 (by rfl) ⟨314006, by rfl⟩ : syracuseStep 1674701 = 628013) (by norm_num)
theorem B1412569 : Blo 1112627 1412569 := bbase (se 2 (by rfl) ⟨529713, by rfl⟩ : syracuseStep 1412569 = 1059427) (by norm_num)
theorem B4525541 : Blo 1112627 4525541 := bbase (se 4 (by rfl) ⟨424269, by rfl⟩ : syracuseStep 4525541 = 848539) (by norm_num)
theorem B1674725 : Blo 1112627 1674725 := bbase (se 4 (by rfl) ⟨157005, by rfl⟩ : syracuseStep 1674725 = 314011) (by norm_num)
theorem B4754933 : Blo 1112627 4754933 := bbase (se 5 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 4754933 = 445775) (by norm_num)
theorem B3575285 : Blo 1112627 3575285 := bbase (se 5 (by rfl) ⟨167591, by rfl⟩ : syracuseStep 3575285 = 335183) (by norm_num)
theorem B1674749 : Blo 1112627 1674749 := bbase (se 3 (by rfl) ⟨314015, by rfl⟩ : syracuseStep 1674749 = 628031) (by norm_num)
theorem B1674773 : Blo 1112627 1674773 := bbase (se 6 (by rfl) ⟨39252, by rfl⟩ : syracuseStep 1674773 = 78505) (by norm_num)
theorem B1674797 : Blo 1112627 1674797 := bbase (se 3 (by rfl) ⟨314024, by rfl⟩ : syracuseStep 1674797 = 628049) (by norm_num)
theorem B3018293 : Blo 1112627 3018293 := bbase (se 5 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 3018293 = 282965) (by norm_num)
theorem B1674821 : Blo 1112627 1674821 := bbase (se 4 (by rfl) ⟨157014, by rfl⟩ : syracuseStep 1674821 = 314029) (by norm_num)
theorem B1674845 : Blo 1112627 1674845 := bbase (se 3 (by rfl) ⟨314033, by rfl⟩ : syracuseStep 1674845 = 628067) (by norm_num)
theorem B1674869 : Blo 1112627 1674869 := bbase (se 5 (by rfl) ⟨78509, by rfl⟩ : syracuseStep 1674869 = 157019) (by norm_num)
theorem B1412741 : Blo 1112627 1412741 := bbase (se 4 (by rfl) ⟨132444, by rfl⟩ : syracuseStep 1412741 = 264889) (by norm_num)
theorem B1674893 : Blo 1112627 1674893 := bbase (se 3 (by rfl) ⟨314042, by rfl⟩ : syracuseStep 1674893 = 628085) (by norm_num)
theorem B1674917 : Blo 1112627 1674917 := bbase (se 4 (by rfl) ⟨157023, by rfl⟩ : syracuseStep 1674917 = 314047) (by norm_num)
theorem B1412797 : Blo 1112627 1412797 := bbase (se 3 (by rfl) ⟨264899, by rfl⟩ : syracuseStep 1412797 = 529799) (by norm_num)
theorem B1674941 : Blo 1112627 1674941 := bbase (se 3 (by rfl) ⟨314051, by rfl⟩ : syracuseStep 1674941 = 628103) (by norm_num)
theorem B2821837 : Blo 1112627 2821837 := bbase (se 3 (by rfl) ⟨529094, by rfl⟩ : syracuseStep 2821837 = 1058189) (by norm_num)
theorem B6786773 : Blo 1112627 6786773 := bbase (se 7 (by rfl) ⟨79532, by rfl⟩ : syracuseStep 6786773 = 159065) (by norm_num)
theorem B1412893 : Blo 1112627 1412893 := bbase (se 3 (by rfl) ⟨264917, by rfl⟩ : syracuseStep 1412893 = 529835) (by norm_num)
theorem B2821949 : Blo 1112627 2821949 := bbase (se 3 (by rfl) ⟨529115, by rfl⟩ : syracuseStep 2821949 = 1058231) (by norm_num)
theorem B1413065 : Blo 1112627 1413065 := bbase (se 2 (by rfl) ⟨529899, by rfl⟩ : syracuseStep 1413065 = 1059799) (by norm_num)
theorem B2854901 : Blo 1112627 2854901 := bbase (se 5 (by rfl) ⟨133823, by rfl⟩ : syracuseStep 2854901 = 267647) (by norm_num)
theorem B2822141 : Blo 1112627 2822141 := bbase (se 3 (by rfl) ⟨529151, by rfl⟩ : syracuseStep 2822141 = 1058303) (by norm_num)
theorem B1413121 : Blo 1112627 1413121 := bbase (se 2 (by rfl) ⟨529920, by rfl⟩ : syracuseStep 1413121 = 1059841) (by norm_num)
theorem B4231237 : Blo 1112627 4231237 := bbase (se 4 (by rfl) ⟨396678, by rfl⟩ : syracuseStep 4231237 = 793357) (by norm_num)
theorem B1413217 : Blo 1112627 1413217 := bbase (se 2 (by rfl) ⟨529956, by rfl⟩ : syracuseStep 1413217 = 1059913) (by norm_num)
theorem B2855125 : Blo 1112627 2855125 := bbase (se 7 (by rfl) ⟨33458, by rfl⟩ : syracuseStep 2855125 = 66917) (by norm_num)
theorem B2822485 : Blo 1112627 2822485 := bbase (se 10 (by rfl) ⟨4134, by rfl⟩ : syracuseStep 2822485 = 8269) (by norm_num)
theorem B4231541 : Blo 1112627 4231541 := bbase (se 5 (by rfl) ⟨198353, by rfl⟩ : syracuseStep 4231541 = 396707) (by norm_num)
theorem B2822597 : Blo 1112627 2822597 := bbase (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) (by norm_num)
theorem B4755941 : Blo 1112627 4755941 := bbase (se 4 (by rfl) ⟨445869, by rfl⟩ : syracuseStep 4755941 = 891739) (by norm_num)
theorem B5640677 : Blo 1112627 5640677 := bbase (se 4 (by rfl) ⟨528813, by rfl⟩ : syracuseStep 5640677 = 1057627) (by norm_num)
theorem B3215893 : Blo 1112627 3215893 := bbase (se 6 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 3215893 = 150745) (by norm_num)
theorem B1905277 : Blo 1112627 1905277 := bbase (se 3 (by rfl) ⟨357239, by rfl⟩ : syracuseStep 1905277 = 714479) (by norm_num)
theorem B2822789 : Blo 1112627 2822789 := bbase (se 4 (by rfl) ⟨264636, by rfl⟩ : syracuseStep 2822789 = 529273) (by norm_num)
theorem B3576565 : Blo 1112627 3576565 := bbase (se 5 (by rfl) ⟨167651, by rfl⟩ : syracuseStep 3576565 = 335303) (by norm_num)
theorem B4526885 : Blo 1112627 4526885 := bbase (se 4 (by rfl) ⟨424395, by rfl⟩ : syracuseStep 4526885 = 848791) (by norm_num)
theorem B2823133 : Blo 1112627 2823133 := bbase (se 3 (by rfl) ⟨529337, by rfl⟩ : syracuseStep 2823133 = 1058675) (by norm_num)
theorem B2823245 : Blo 1112627 2823245 := bbase (se 3 (by rfl) ⟨529358, by rfl⟩ : syracuseStep 2823245 = 1058717) (by norm_num)
theorem B2823437 : Blo 1112627 2823437 := bbase (se 3 (by rfl) ⟨529394, by rfl⟩ : syracuseStep 2823437 = 1058789) (by norm_num)
theorem B1611037 : Blo 1112627 1611037 := bbase (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) (by norm_num)
theorem B6198581 : Blo 1112627 6198581 := bbase (se 5 (by rfl) ⟨290558, by rfl⟩ : syracuseStep 6198581 = 581117) (by norm_num)
theorem B2823781 : Blo 1112627 2823781 := bbase (se 4 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 2823781 = 529459) (by norm_num)
theorem B2823893 : Blo 1112627 2823893 := bbase (se 7 (by rfl) ⟨33092, by rfl⟩ : syracuseStep 2823893 = 66185) (by norm_num)
theorem B5641973 : Blo 1112627 5641973 := bbase (se 5 (by rfl) ⟨264467, by rfl⟩ : syracuseStep 5641973 = 528935) (by norm_num)
theorem B5347205 : Blo 1112627 5347205 := bbase (se 4 (by rfl) ⟨501300, by rfl⟩ : syracuseStep 5347205 = 1002601) (by norm_num)
theorem B2824085 : Blo 1112627 2824085 := bbase (se 6 (by rfl) ⟨66189, by rfl⟩ : syracuseStep 2824085 = 132379) (by norm_num)
theorem B9050069 : Blo 1112627 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B6789109 : Blo 1112627 6789109 := bbase (se 5 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 6789109 = 636479) (by norm_num)
theorem B2857013 : Blo 1112627 2857013 := bbase (se 5 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 2857013 = 267845) (by norm_num)
theorem B5347397 : Blo 1112627 5347397 := bbase (se 4 (by rfl) ⟨501318, by rfl⟩ : syracuseStep 5347397 = 1002637) (by norm_num)
theorem B4757717 : Blo 1112627 4757717 := bbase (se 7 (by rfl) ⟨55754, by rfl⟩ : syracuseStep 4757717 = 111509) (by norm_num)
theorem B2824429 : Blo 1112627 2824429 := bbase (se 3 (by rfl) ⟨529580, by rfl⟩ : syracuseStep 2824429 = 1059161) (by norm_num)
theorem B2824541 : Blo 1112627 2824541 := bbase (se 3 (by rfl) ⟨529601, by rfl⟩ : syracuseStep 2824541 = 1059203) (by norm_num)
theorem B1251733 : Blo 1112627 1251733 := bbase (se 6 (by rfl) ⟨29337, by rfl⟩ : syracuseStep 1251733 = 58675) (by norm_num)
theorem B4233653 : Blo 1112627 4233653 := bbase (se 5 (by rfl) ⟨198452, by rfl⟩ : syracuseStep 4233653 = 396905) (by norm_num)
theorem B1251769 : Blo 1112627 1251769 := bbase (se 2 (by rfl) ⟨469413, by rfl⟩ : syracuseStep 1251769 = 938827) (by norm_num)
theorem B5347781 : Blo 1112627 5347781 := bbase (se 4 (by rfl) ⟨501354, by rfl⟩ : syracuseStep 5347781 = 1002709) (by norm_num)
theorem B1251805 : Blo 1112627 1251805 := bbase (se 3 (by rfl) ⟨234713, by rfl⟩ : syracuseStep 1251805 = 469427) (by norm_num)
theorem B1251841 : Blo 1112627 1251841 := bbase (se 2 (by rfl) ⟨469440, by rfl⟩ : syracuseStep 1251841 = 938881) (by norm_num)
theorem B2824733 : Blo 1112627 2824733 := bbase (se 3 (by rfl) ⟨529637, by rfl⟩ : syracuseStep 2824733 = 1059275) (by norm_num)
theorem B1251877 : Blo 1112627 1251877 := bbase (se 4 (by rfl) ⟨117363, by rfl⟩ : syracuseStep 1251877 = 234727) (by norm_num)
theorem B1251913 : Blo 1112627 1251913 := bbase (se 2 (by rfl) ⟨469467, by rfl⟩ : syracuseStep 1251913 = 938935) (by norm_num)
theorem B1251949 : Blo 1112627 1251949 := bbase (se 3 (by rfl) ⟨234740, by rfl⟩ : syracuseStep 1251949 = 469481) (by norm_num)
theorem B1251985 : Blo 1112627 1251985 := bbase (se 2 (by rfl) ⟨469494, by rfl⟩ : syracuseStep 1251985 = 938989) (by norm_num)
theorem B1252021 : Blo 1112627 1252021 := bbase (se 5 (by rfl) ⟨58688, by rfl⟩ : syracuseStep 1252021 = 117377) (by norm_num)
theorem B4233941 : Blo 1112627 4233941 := bbase (se 7 (by rfl) ⟨49616, by rfl⟩ : syracuseStep 4233941 = 99233) (by norm_num)
theorem B1252057 : Blo 1112627 1252057 := bbase (se 2 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 1252057 = 939043) (by norm_num)
theorem B1252093 : Blo 1112627 1252093 := bbase (se 3 (by rfl) ⟨234767, by rfl⟩ : syracuseStep 1252093 = 469535) (by norm_num)
theorem B3054341 : Blo 1112627 3054341 := bbase (se 4 (by rfl) ⟨286344, by rfl⟩ : syracuseStep 3054341 = 572689) (by norm_num)
theorem B1252129 : Blo 1112627 1252129 := bbase (se 2 (by rfl) ⟨469548, by rfl⟩ : syracuseStep 1252129 = 939097) (by norm_num)
theorem B1252165 : Blo 1112627 1252165 := bbase (se 4 (by rfl) ⟨117390, by rfl⟩ : syracuseStep 1252165 = 234781) (by norm_num)
theorem B1252201 : Blo 1112627 1252201 := bbase (se 2 (by rfl) ⟨469575, by rfl⟩ : syracuseStep 1252201 = 939151) (by norm_num)
theorem B2825077 : Blo 1112627 2825077 := bbase (se 5 (by rfl) ⟨132425, by rfl⟩ : syracuseStep 2825077 = 264851) (by norm_num)
theorem B1252237 : Blo 1112627 1252237 := bbase (se 3 (by rfl) ⟨234794, by rfl⟩ : syracuseStep 1252237 = 469589) (by norm_num)
theorem B1252273 : Blo 1112627 1252273 := bbase (se 2 (by rfl) ⟨469602, by rfl⟩ : syracuseStep 1252273 = 939205) (by norm_num)
theorem B1907645 : Blo 1112627 1907645 := bbase (se 3 (by rfl) ⟨357683, by rfl⟩ : syracuseStep 1907645 = 715367) (by norm_num)
theorem B1252309 : Blo 1112627 1252309 := bbase (se 7 (by rfl) ⟨14675, by rfl⟩ : syracuseStep 1252309 = 29351) (by norm_num)
theorem B2825189 : Blo 1112627 2825189 := bbase (se 4 (by rfl) ⟨264861, by rfl⟩ : syracuseStep 2825189 = 529723) (by norm_num)
theorem B1252345 : Blo 1112627 1252345 := bbase (se 2 (by rfl) ⟨469629, by rfl⟩ : syracuseStep 1252345 = 939259) (by norm_num)
theorem B5643269 : Blo 1112627 5643269 := bbase (se 4 (by rfl) ⟨529056, by rfl⟩ : syracuseStep 5643269 = 1058113) (by norm_num)
theorem B1252381 : Blo 1112627 1252381 := bbase (se 3 (by rfl) ⟨234821, by rfl⟩ : syracuseStep 1252381 = 469643) (by norm_num)
theorem B1252417 : Blo 1112627 1252417 := bbase (se 2 (by rfl) ⟨469656, by rfl⟩ : syracuseStep 1252417 = 939313) (by norm_num)
theorem B1252453 : Blo 1112627 1252453 := bbase (se 4 (by rfl) ⟨117417, by rfl⟩ : syracuseStep 1252453 = 234835) (by norm_num)
theorem B1252489 : Blo 1112627 1252489 := bbase (se 2 (by rfl) ⟨469683, by rfl⟩ : syracuseStep 1252489 = 939367) (by norm_num)
theorem B2825381 : Blo 1112627 2825381 := bbase (se 4 (by rfl) ⟨264879, by rfl⟩ : syracuseStep 2825381 = 529759) (by norm_num)
theorem B1252525 : Blo 1112627 1252525 := bbase (se 3 (by rfl) ⟨234848, by rfl⟩ : syracuseStep 1252525 = 469697) (by norm_num)
theorem B1252561 : Blo 1112627 1252561 := bbase (se 2 (by rfl) ⟨469710, by rfl⟩ : syracuseStep 1252561 = 939421) (by norm_num)
theorem B1252597 : Blo 1112627 1252597 := bbase (se 5 (by rfl) ⟨58715, by rfl⟩ : syracuseStep 1252597 = 117431) (by norm_num)
theorem B1252633 : Blo 1112627 1252633 := bbase (se 2 (by rfl) ⟨469737, by rfl⟩ : syracuseStep 1252633 = 939475) (by norm_num)
theorem B1252669 : Blo 1112627 1252669 := bbase (se 3 (by rfl) ⟨234875, by rfl⟩ : syracuseStep 1252669 = 469751) (by norm_num)
theorem B1252705 : Blo 1112627 1252705 := bbase (se 2 (by rfl) ⟨469764, by rfl⟩ : syracuseStep 1252705 = 939529) (by norm_num)
theorem B1252741 : Blo 1112627 1252741 := bbase (se 4 (by rfl) ⟨117444, by rfl⟩ : syracuseStep 1252741 = 234889) (by norm_num)
theorem B1252777 : Blo 1112627 1252777 := bbase (se 2 (by rfl) ⟨469791, by rfl⟩ : syracuseStep 1252777 = 939583) (by norm_num)
theorem B1252813 : Blo 1112627 1252813 := bbase (se 3 (by rfl) ⟨234902, by rfl⟩ : syracuseStep 1252813 = 469805) (by norm_num)
theorem B1252849 : Blo 1112627 1252849 := bbase (se 2 (by rfl) ⟨469818, by rfl⟩ : syracuseStep 1252849 = 939637) (by norm_num)
theorem B2825725 : Blo 1112627 2825725 := bbase (se 3 (by rfl) ⟨529823, by rfl⟩ : syracuseStep 2825725 = 1059647) (by norm_num)
theorem B1252885 : Blo 1112627 1252885 := bbase (se 6 (by rfl) ⟨29364, by rfl⟩ : syracuseStep 1252885 = 58729) (by norm_num)
theorem B1252921 : Blo 1112627 1252921 := bbase (se 2 (by rfl) ⟨469845, by rfl⟩ : syracuseStep 1252921 = 939691) (by norm_num)
theorem B1252957 : Blo 1112627 1252957 := bbase (se 3 (by rfl) ⟨234929, by rfl⟩ : syracuseStep 1252957 = 469859) (by norm_num)
theorem B2825837 : Blo 1112627 2825837 := bbase (se 3 (by rfl) ⟨529844, by rfl⟩ : syracuseStep 2825837 = 1059689) (by norm_num)
theorem B1252993 : Blo 1112627 1252993 := bbase (se 2 (by rfl) ⟨469872, by rfl⟩ : syracuseStep 1252993 = 939745) (by norm_num)
theorem B1253029 : Blo 1112627 1253029 := bbase (se 4 (by rfl) ⟨117471, by rfl⟩ : syracuseStep 1253029 = 234943) (by norm_num)
theorem B1253065 : Blo 1112627 1253065 := bbase (se 2 (by rfl) ⟨469899, by rfl⟩ : syracuseStep 1253065 = 939799) (by norm_num)
theorem B1253101 : Blo 1112627 1253101 := bbase (se 3 (by rfl) ⟨234956, by rfl⟩ : syracuseStep 1253101 = 469913) (by norm_num)
theorem B1253137 : Blo 1112627 1253137 := bbase (se 2 (by rfl) ⟨469926, by rfl⟩ : syracuseStep 1253137 = 939853) (by norm_num)
theorem B2826029 : Blo 1112627 2826029 := bbase (se 3 (by rfl) ⟨529880, by rfl⟩ : syracuseStep 2826029 = 1059761) (by norm_num)
theorem B1253173 : Blo 1112627 1253173 := bbase (se 5 (by rfl) ⟨58742, by rfl⟩ : syracuseStep 1253173 = 117485) (by norm_num)
theorem B1253209 : Blo 1112627 1253209 := bbase (se 2 (by rfl) ⟨469953, by rfl⟩ : syracuseStep 1253209 = 939907) (by norm_num)
theorem B4235125 : Blo 1112627 4235125 := bbase (se 5 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 4235125 = 397043) (by norm_num)
theorem B1253245 : Blo 1112627 1253245 := bbase (se 3 (by rfl) ⟨234983, by rfl⟩ : syracuseStep 1253245 = 469967) (by norm_num)
theorem B1253281 : Blo 1112627 1253281 := bbase (se 2 (by rfl) ⟨469980, by rfl⟩ : syracuseStep 1253281 = 939961) (by norm_num)
theorem B1253317 : Blo 1112627 1253317 := bbase (se 4 (by rfl) ⟨117498, by rfl⟩ : syracuseStep 1253317 = 234997) (by norm_num)
theorem B1253353 : Blo 1112627 1253353 := bbase (se 2 (by rfl) ⟨470007, by rfl⟩ : syracuseStep 1253353 = 940015) (by norm_num)
theorem B1253389 : Blo 1112627 1253389 := bbase (se 3 (by rfl) ⟨235010, by rfl⟩ : syracuseStep 1253389 = 470021) (by norm_num)
theorem B1253425 : Blo 1112627 1253425 := bbase (se 2 (by rfl) ⟨470034, by rfl⟩ : syracuseStep 1253425 = 940069) (by norm_num)
theorem B8036405 : Blo 1112627 8036405 := bbase (se 5 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 8036405 = 753413) (by norm_num)
theorem B68591701 : Blo 1112627 68591701 := bbase (se 8 (by rfl) ⟨401904, by rfl⟩ : syracuseStep 68591701 = 803809) (by norm_num)
theorem B1253461 : Blo 1112627 1253461 := bbase (se 8 (by rfl) ⟨7344, by rfl⟩ : syracuseStep 1253461 = 14689) (by norm_num)
theorem B1253497 : Blo 1112627 1253497 := bbase (se 2 (by rfl) ⟨470061, by rfl⟩ : syracuseStep 1253497 = 940123) (by norm_num)
theorem B3219589 : Blo 1112627 3219589 := bbase (se 4 (by rfl) ⟨301836, by rfl⟩ : syracuseStep 3219589 = 603673) (by norm_num)
theorem B2826373 : Blo 1112627 2826373 := bbase (se 4 (by rfl) ⟨264972, by rfl⟩ : syracuseStep 2826373 = 529945) (by norm_num)
theorem B1253533 : Blo 1112627 1253533 := bbase (se 3 (by rfl) ⟨235037, by rfl⟩ : syracuseStep 1253533 = 470075) (by norm_num)
theorem B4235429 : Blo 1112627 4235429 := bbase (se 4 (by rfl) ⟨397071, by rfl⟩ : syracuseStep 4235429 = 794143) (by norm_num)
theorem B1253569 : Blo 1112627 1253569 := bbase (se 2 (by rfl) ⟨470088, by rfl⟩ : syracuseStep 1253569 = 940177) (by norm_num)
theorem B1253605 : Blo 1112627 1253605 := bbase (se 4 (by rfl) ⟨117525, by rfl⟩ : syracuseStep 1253605 = 235051) (by norm_num)
theorem B1253641 : Blo 1112627 1253641 := bbase (se 2 (by rfl) ⟨470115, by rfl⟩ : syracuseStep 1253641 = 940231) (by norm_num)
theorem B5644565 : Blo 1112627 5644565 := bbase (se 6 (by rfl) ⟨132294, by rfl⟩ : syracuseStep 5644565 = 264589) (by norm_num)
theorem B1253677 : Blo 1112627 1253677 := bbase (se 3 (by rfl) ⟨235064, by rfl⟩ : syracuseStep 1253677 = 470129) (by norm_num)
theorem B1253713 : Blo 1112627 1253713 := bbase (se 2 (by rfl) ⟨470142, by rfl⟩ : syracuseStep 1253713 = 940285) (by norm_num)
theorem B1253749 : Blo 1112627 1253749 := bbase (se 5 (by rfl) ⟨58769, by rfl⟩ : syracuseStep 1253749 = 117539) (by norm_num)
theorem B1253785 : Blo 1112627 1253785 := bbase (se 2 (by rfl) ⟨470169, by rfl⟩ : syracuseStep 1253785 = 940339) (by norm_num)
theorem B1253821 : Blo 1112627 1253821 := bbase (se 3 (by rfl) ⟨235091, by rfl⟩ : syracuseStep 1253821 = 470183) (by norm_num)
theorem B1253857 : Blo 1112627 1253857 := bbase (se 2 (by rfl) ⟨470196, by rfl⟩ : syracuseStep 1253857 = 940393) (by norm_num)
theorem B1253893 : Blo 1112627 1253893 := bbase (se 4 (by rfl) ⟨117552, by rfl⟩ : syracuseStep 1253893 = 235105) (by norm_num)
theorem B1253929 : Blo 1112627 1253929 := bbase (se 2 (by rfl) ⟨470223, by rfl⟩ : syracuseStep 1253929 = 940447) (by norm_num)
theorem B3809845 : Blo 1112627 3809845 := bbase (se 5 (by rfl) ⟨178586, by rfl⟩ : syracuseStep 3809845 = 357173) (by norm_num)
theorem B4071989 : Blo 1112627 4071989 := bbase (se 5 (by rfl) ⟨190874, by rfl⟩ : syracuseStep 4071989 = 381749) (by norm_num)
theorem B1253965 : Blo 1112627 1253965 := bbase (se 3 (by rfl) ⟨235118, by rfl⟩ : syracuseStep 1253965 = 470237) (by norm_num)
theorem B2007661 : Blo 1112627 2007661 := bbase (se 3 (by rfl) ⟨376436, by rfl⟩ : syracuseStep 2007661 = 752873) (by norm_num)
theorem B1254001 : Blo 1112627 1254001 := bbase (se 2 (by rfl) ⟨470250, by rfl⟩ : syracuseStep 1254001 = 940501) (by norm_num)
theorem B1188481 : Blo 1112627 1188481 := bbase (se 2 (by rfl) ⟨445680, by rfl⟩ : syracuseStep 1188481 = 891361) (by norm_num)
theorem B1254037 : Blo 1112627 1254037 := bbase (se 6 (by rfl) ⟨29391, by rfl⟩ : syracuseStep 1254037 = 58783) (by norm_num)
theorem B1254073 : Blo 1112627 1254073 := bbase (se 2 (by rfl) ⟨470277, by rfl⟩ : syracuseStep 1254073 = 940555) (by norm_num)
theorem B1188541 : Blo 1112627 1188541 := bbase (se 3 (by rfl) ⟨222851, by rfl⟩ : syracuseStep 1188541 = 445703) (by norm_num)
theorem B1254109 : Blo 1112627 1254109 := bbase (se 3 (by rfl) ⟨235145, by rfl⟩ : syracuseStep 1254109 = 470291) (by norm_num)
theorem B1254145 : Blo 1112627 1254145 := bbase (se 2 (by rfl) ⟨470304, by rfl⟩ : syracuseStep 1254145 = 940609) (by norm_num)
theorem B1254181 : Blo 1112627 1254181 := bbase (se 4 (by rfl) ⟨117579, by rfl⟩ : syracuseStep 1254181 = 235159) (by norm_num)
theorem B1254217 : Blo 1112627 1254217 := bbase (se 2 (by rfl) ⟨470331, by rfl⟩ : syracuseStep 1254217 = 940663) (by norm_num)
theorem B1254253 : Blo 1112627 1254253 := bbase (se 3 (by rfl) ⟨235172, by rfl⟩ : syracuseStep 1254253 = 470345) (by norm_num)
theorem B2007949 : Blo 1112627 2007949 := bbase (se 3 (by rfl) ⟨376490, by rfl⟩ : syracuseStep 2007949 = 752981) (by norm_num)
theorem B1254289 : Blo 1112627 1254289 := bbase (se 2 (by rfl) ⟨470358, by rfl⟩ : syracuseStep 1254289 = 940717) (by norm_num)
theorem B1254325 : Blo 1112627 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B1254361 : Blo 1112627 1254361 := bbase (se 2 (by rfl) ⟨470385, by rfl⟩ : syracuseStep 1254361 = 940771) (by norm_num)
theorem B3220469 : Blo 1112627 3220469 := bbase (se 5 (by rfl) ⟨150959, by rfl⟩ : syracuseStep 3220469 = 301919) (by norm_num)
theorem B1188857 : Blo 1112627 1188857 := bbase (se 2 (by rfl) ⟨445821, by rfl⟩ : syracuseStep 1188857 = 891643) (by norm_num)
theorem B1254397 : Blo 1112627 1254397 := bbase (se 3 (by rfl) ⟨235199, by rfl⟩ : syracuseStep 1254397 = 470399) (by norm_num)
theorem B1254433 : Blo 1112627 1254433 := bbase (se 2 (by rfl) ⟨470412, by rfl⟩ : syracuseStep 1254433 = 940825) (by norm_num)
theorem B1254469 : Blo 1112627 1254469 := bbase (se 4 (by rfl) ⟨117606, by rfl⟩ : syracuseStep 1254469 = 235213) (by norm_num)
theorem B1254505 : Blo 1112627 1254505 := bbase (se 2 (by rfl) ⟨470439, by rfl⟩ : syracuseStep 1254505 = 940879) (by norm_num)
theorem B1254541 : Blo 1112627 1254541 := bbase (se 3 (by rfl) ⟨235226, by rfl⟩ : syracuseStep 1254541 = 470453) (by norm_num)
theorem B1254577 : Blo 1112627 1254577 := bbase (se 2 (by rfl) ⟨470466, by rfl⟩ : syracuseStep 1254577 = 940933) (by norm_num)
theorem B1254613 : Blo 1112627 1254613 := bbase (se 7 (by rfl) ⟨14702, by rfl⟩ : syracuseStep 1254613 = 29405) (by norm_num)
theorem B1254649 : Blo 1112627 1254649 := bbase (se 2 (by rfl) ⟨470493, by rfl⟩ : syracuseStep 1254649 = 940987) (by norm_num)
theorem B1254685 : Blo 1112627 1254685 := bbase (se 3 (by rfl) ⟨235253, by rfl⟩ : syracuseStep 1254685 = 470507) (by norm_num)
theorem B1254721 : Blo 1112627 1254721 := bbase (se 2 (by rfl) ⟨470520, by rfl⟩ : syracuseStep 1254721 = 941041) (by norm_num)
theorem B1254757 : Blo 1112627 1254757 := bbase (se 4 (by rfl) ⟨117633, by rfl⟩ : syracuseStep 1254757 = 235267) (by norm_num)
theorem B1254793 : Blo 1112627 1254793 := bbase (se 2 (by rfl) ⟨470547, by rfl⟩ : syracuseStep 1254793 = 941095) (by norm_num)
theorem B10855829 : Blo 1112627 10855829 := bbase (se 6 (by rfl) ⟨254433, by rfl⟩ : syracuseStep 10855829 = 508867) (by norm_num)
theorem B1254829 : Blo 1112627 1254829 := bbase (se 3 (by rfl) ⟨235280, by rfl⟩ : syracuseStep 1254829 = 470561) (by norm_num)
theorem B1189301 : Blo 1112627 1189301 := bbase (se 5 (by rfl) ⟨55748, by rfl⟩ : syracuseStep 1189301 = 111497) (by norm_num)
theorem B1254865 : Blo 1112627 1254865 := bbase (se 2 (by rfl) ⟨470574, by rfl⟩ : syracuseStep 1254865 = 941149) (by norm_num)
theorem B7153109 : Blo 1112627 7153109 := bbase (se 7 (by rfl) ⟨83825, by rfl⟩ : syracuseStep 7153109 = 167651) (by norm_num)
theorem B1189361 : Blo 1112627 1189361 := bbase (se 2 (by rfl) ⟨446010, by rfl⟩ : syracuseStep 1189361 = 892021) (by norm_num)
theorem B1254901 : Blo 1112627 1254901 := bbase (se 5 (by rfl) ⟨58823, by rfl⟩ : syracuseStep 1254901 = 117647) (by norm_num)
theorem B1254937 : Blo 1112627 1254937 := bbase (se 2 (by rfl) ⟨470601, by rfl⟩ : syracuseStep 1254937 = 941203) (by norm_num)
theorem B5645861 : Blo 1112627 5645861 := bbase (se 4 (by rfl) ⟨529299, by rfl⟩ : syracuseStep 5645861 = 1058599) (by norm_num)
theorem B10298933 : Blo 1112627 10298933 := bbase (se 5 (by rfl) ⟨482762, by rfl⟩ : syracuseStep 10298933 = 965525) (by norm_num)
theorem B1254973 : Blo 1112627 1254973 := bbase (se 3 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 1254973 = 470615) (by norm_num)
theorem B1877573 : Blo 1112627 1877573 := bbase (se 4 (by rfl) ⟨176022, by rfl⟩ : syracuseStep 1877573 = 352045) (by norm_num)
theorem B13542997 : Blo 1112627 13542997 := bbase (se 8 (by rfl) ⟨79353, by rfl⟩ : syracuseStep 13542997 = 158707) (by norm_num)
theorem B1255009 : Blo 1112627 1255009 := bbase (se 2 (by rfl) ⟨470628, by rfl⟩ : syracuseStep 1255009 = 941257) (by norm_num)
theorem B1189489 : Blo 1112627 1189489 := bbase (se 2 (by rfl) ⟨446058, by rfl⟩ : syracuseStep 1189489 = 892117) (by norm_num)
theorem B1255045 : Blo 1112627 1255045 := bbase (se 4 (by rfl) ⟨117660, by rfl⟩ : syracuseStep 1255045 = 235321) (by norm_num)
theorem B1255081 : Blo 1112627 1255081 := bbase (se 2 (by rfl) ⟨470655, by rfl⟩ : syracuseStep 1255081 = 941311) (by norm_num)
theorem B1877701 : Blo 1112627 1877701 := bbase (se 4 (by rfl) ⟨176034, by rfl⟩ : syracuseStep 1877701 = 352069) (by norm_num)
theorem B1255117 : Blo 1112627 1255117 := bbase (se 3 (by rfl) ⟨235334, by rfl⟩ : syracuseStep 1255117 = 470669) (by norm_num)
theorem B24094421 : Blo 1112627 24094421 := bbase (se 7 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 24094421 = 564713) (by norm_num)
theorem B1255153 : Blo 1112627 1255153 := bbase (se 2 (by rfl) ⟨470682, by rfl⟩ : syracuseStep 1255153 = 941365) (by norm_num)
theorem B1255189 : Blo 1112627 1255189 := bbase (se 6 (by rfl) ⟨29418, by rfl⟩ : syracuseStep 1255189 = 58837) (by norm_num)
theorem B1877789 : Blo 1112627 1877789 := bbase (se 3 (by rfl) ⟨352085, by rfl⟩ : syracuseStep 1877789 = 704171) (by norm_num)
theorem B1255225 : Blo 1112627 1255225 := bbase (se 2 (by rfl) ⟨470709, by rfl⟩ : syracuseStep 1255225 = 941419) (by norm_num)
theorem B1255261 : Blo 1112627 1255261 := bbase (se 3 (by rfl) ⟨235361, by rfl⟩ : syracuseStep 1255261 = 470723) (by norm_num)
theorem B1255297 : Blo 1112627 1255297 := bbase (se 2 (by rfl) ⟨470736, by rfl⟩ : syracuseStep 1255297 = 941473) (by norm_num)
theorem B1877917 : Blo 1112627 1877917 := bbase (se 3 (by rfl) ⟨352109, by rfl⟩ : syracuseStep 1877917 = 704219) (by norm_num)
theorem B1255333 : Blo 1112627 1255333 := bbase (se 4 (by rfl) ⟨117687, by rfl⟩ : syracuseStep 1255333 = 235375) (by norm_num)
theorem B1255369 : Blo 1112627 1255369 := bbase (se 2 (by rfl) ⟨470763, by rfl⟩ : syracuseStep 1255369 = 941527) (by norm_num)
theorem B12036053 : Blo 1112627 12036053 := bbase (se 7 (by rfl) ⟨141047, by rfl⟩ : syracuseStep 12036053 = 282095) (by norm_num)
theorem B2009045 : Blo 1112627 2009045 := bbase (se 7 (by rfl) ⟨23543, by rfl⟩ : syracuseStep 2009045 = 47087) (by norm_num)
theorem B1255405 : Blo 1112627 1255405 := bbase (se 3 (by rfl) ⟨235388, by rfl⟩ : syracuseStep 1255405 = 470777) (by norm_num)
theorem B1878005 : Blo 1112627 1878005 := bbase (se 5 (by rfl) ⟨88031, by rfl⟩ : syracuseStep 1878005 = 176063) (by norm_num)
theorem B1255441 : Blo 1112627 1255441 := bbase (se 2 (by rfl) ⟨470790, by rfl⟩ : syracuseStep 1255441 = 941581) (by norm_num)
theorem B1189933 : Blo 1112627 1189933 := bbase (se 3 (by rfl) ⟨223112, by rfl⟩ : syracuseStep 1189933 = 446225) (by norm_num)
theorem B1255477 : Blo 1112627 1255477 := bbase (se 5 (by rfl) ⟨58850, by rfl⟩ : syracuseStep 1255477 = 117701) (by norm_num)
theorem B1255513 : Blo 1112627 1255513 := bbase (se 2 (by rfl) ⟨470817, by rfl⟩ : syracuseStep 1255513 = 941635) (by norm_num)
theorem B1878133 : Blo 1112627 1878133 := bbase (se 5 (by rfl) ⟨88037, by rfl⟩ : syracuseStep 1878133 = 176075) (by norm_num)
theorem B1255549 : Blo 1112627 1255549 := bbase (se 3 (by rfl) ⟨235415, by rfl⟩ : syracuseStep 1255549 = 470831) (by norm_num)
theorem B1255585 : Blo 1112627 1255585 := bbase (se 2 (by rfl) ⟨470844, by rfl⟩ : syracuseStep 1255585 = 941689) (by norm_num)
theorem B1190053 : Blo 1112627 1190053 := bbase (se 4 (by rfl) ⟨111567, by rfl⟩ : syracuseStep 1190053 = 223135) (by norm_num)
theorem B1255621 : Blo 1112627 1255621 := bbase (se 4 (by rfl) ⟨117714, by rfl⟩ : syracuseStep 1255621 = 235429) (by norm_num)
theorem B1878221 : Blo 1112627 1878221 := bbase (se 3 (by rfl) ⟨352166, by rfl⟩ : syracuseStep 1878221 = 704333) (by norm_num)
theorem B4237541 : Blo 1112627 4237541 := bbase (se 4 (by rfl) ⟨397269, by rfl⟩ : syracuseStep 4237541 = 794539) (by norm_num)
theorem B1255657 : Blo 1112627 1255657 := bbase (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) (by norm_num)
theorem B1255693 : Blo 1112627 1255693 := bbase (se 3 (by rfl) ⟨235442, by rfl⟩ : syracuseStep 1255693 = 470885) (by norm_num)
theorem B8464661 : Blo 1112627 8464661 := bbase (se 6 (by rfl) ⟨198390, by rfl⟩ : syracuseStep 8464661 = 396781) (by norm_num)
theorem B1255729 : Blo 1112627 1255729 := bbase (se 2 (by rfl) ⟨470898, by rfl⟩ : syracuseStep 1255729 = 941797) (by norm_num)
theorem B1878349 : Blo 1112627 1878349 := bbase (se 3 (by rfl) ⟨352190, by rfl⟩ : syracuseStep 1878349 = 704381) (by norm_num)
theorem B1255765 : Blo 1112627 1255765 := bbase (se 10 (by rfl) ⟨1839, by rfl⟩ : syracuseStep 1255765 = 3679) (by norm_num)
theorem B1255801 : Blo 1112627 1255801 := bbase (se 2 (by rfl) ⟨470925, by rfl⟩ : syracuseStep 1255801 = 941851) (by norm_num)
theorem B4761989 : Blo 1112627 4761989 := bbase (se 4 (by rfl) ⟨446436, by rfl⟩ : syracuseStep 4761989 = 892873) (by norm_num)
theorem B12069269 : Blo 1112627 12069269 := bbase (se 6 (by rfl) ⟨282873, by rfl⟩ : syracuseStep 12069269 = 565747) (by norm_num)
theorem B1255837 : Blo 1112627 1255837 := bbase (se 3 (by rfl) ⟨235469, by rfl⟩ : syracuseStep 1255837 = 470939) (by norm_num)
theorem B1190305 : Blo 1112627 1190305 := bbase (se 2 (by rfl) ⟨446364, by rfl⟩ : syracuseStep 1190305 = 892729) (by norm_num)
theorem B1878437 : Blo 1112627 1878437 := bbase (se 4 (by rfl) ⟨176103, by rfl⟩ : syracuseStep 1878437 = 352207) (by norm_num)
theorem B1190309 : Blo 1112627 1190309 := bbase (se 4 (by rfl) ⟨111591, by rfl⟩ : syracuseStep 1190309 = 223183) (by norm_num)
theorem B1255873 : Blo 1112627 1255873 := bbase (se 2 (by rfl) ⟨470952, by rfl⟩ : syracuseStep 1255873 = 941905) (by norm_num)
theorem B22915541 : Blo 1112627 22915541 := bbase (se 7 (by rfl) ⟨268541, by rfl⟩ : syracuseStep 22915541 = 537083) (by norm_num)
theorem B1255909 : Blo 1112627 1255909 := bbase (se 4 (by rfl) ⟨117741, by rfl⟩ : syracuseStep 1255909 = 235483) (by norm_num)
theorem B4237829 : Blo 1112627 4237829 := bbase (se 4 (by rfl) ⟨397296, by rfl⟩ : syracuseStep 4237829 = 794593) (by norm_num)
theorem B1255945 : Blo 1112627 1255945 := bbase (se 2 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 1255945 = 941959) (by norm_num)
theorem B1878565 : Blo 1112627 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B1255981 : Blo 1112627 1255981 := bbase (se 3 (by rfl) ⟨235496, by rfl⟩ : syracuseStep 1255981 = 470993) (by norm_num)
theorem B1256017 : Blo 1112627 1256017 := bbase (se 2 (by rfl) ⟨471006, by rfl⟩ : syracuseStep 1256017 = 942013) (by norm_num)
theorem B1256053 : Blo 1112627 1256053 := bbase (se 5 (by rfl) ⟨58877, by rfl⟩ : syracuseStep 1256053 = 117755) (by norm_num)
theorem B1878653 : Blo 1112627 1878653 := bbase (se 3 (by rfl) ⟨352247, by rfl⟩ : syracuseStep 1878653 = 704495) (by norm_num)
theorem B5352085 : Blo 1112627 5352085 := bbase (se 6 (by rfl) ⟨125439, by rfl⟩ : syracuseStep 5352085 = 250879) (by norm_num)
theorem B1256089 : Blo 1112627 1256089 := bbase (se 2 (by rfl) ⟨471033, by rfl⟩ : syracuseStep 1256089 = 942067) (by norm_num)
theorem B1288885 : Blo 1112627 1288885 := bbase (se 5 (by rfl) ⟨60416, by rfl⟩ : syracuseStep 1288885 = 120833) (by norm_num)
theorem B1256125 : Blo 1112627 1256125 := bbase (se 3 (by rfl) ⟨235523, by rfl⟩ : syracuseStep 1256125 = 471047) (by norm_num)
theorem B1288921 : Blo 1112627 1288921 := bbase (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) (by norm_num)
theorem B1256161 : Blo 1112627 1256161 := bbase (se 2 (by rfl) ⟨471060, by rfl⟩ : syracuseStep 1256161 = 942121) (by norm_num)
theorem B1878781 : Blo 1112627 1878781 := bbase (se 3 (by rfl) ⟨352271, by rfl⟩ : syracuseStep 1878781 = 704543) (by norm_num)
theorem B1256197 : Blo 1112627 1256197 := bbase (se 4 (by rfl) ⟨117768, by rfl⟩ : syracuseStep 1256197 = 235537) (by norm_num)
theorem B5647157 : Blo 1112627 5647157 := bbase (se 5 (by rfl) ⟨264710, by rfl⟩ : syracuseStep 5647157 = 529421) (by norm_num)
theorem B1878869 : Blo 1112627 1878869 := bbase (se 9 (by rfl) ⟨5504, by rfl⟩ : syracuseStep 1878869 = 11009) (by norm_num)
theorem B6433685 : Blo 1112627 6433685 := bbase (se 6 (by rfl) ⟨150789, by rfl⟩ : syracuseStep 6433685 = 301579) (by norm_num)
theorem B1878997 : Blo 1112627 1878997 := bbase (se 7 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 1878997 = 44039) (by norm_num)
theorem B1190873 : Blo 1112627 1190873 := bbase (se 2 (by rfl) ⟨446577, by rfl⟩ : syracuseStep 1190873 = 893155) (by norm_num)
theorem B1879085 : Blo 1112627 1879085 := bbase (se 3 (by rfl) ⟨352328, by rfl⟩ : syracuseStep 1879085 = 704657) (by norm_num)
theorem B1191061 : Blo 1112627 1191061 := bbase (se 6 (by rfl) ⟨27915, by rfl⟩ : syracuseStep 1191061 = 55831) (by norm_num)
theorem B1879213 : Blo 1112627 1879213 := bbase (se 3 (by rfl) ⟨352352, by rfl⟩ : syracuseStep 1879213 = 704705) (by norm_num)
theorem B2010349 : Blo 1112627 2010349 := bbase (se 3 (by rfl) ⟨376940, by rfl⟩ : syracuseStep 2010349 = 753881) (by norm_num)
theorem B1879301 : Blo 1112627 1879301 := bbase (se 4 (by rfl) ⟨176184, by rfl⟩ : syracuseStep 1879301 = 352369) (by norm_num)
theorem B1224029 : Blo 1112627 1224029 := bbase (se 3 (by rfl) ⟨229505, by rfl⟩ : syracuseStep 1224029 = 459011) (by norm_num)
theorem B1879429 : Blo 1112627 1879429 := bbase (se 4 (by rfl) ⟨176196, by rfl⟩ : syracuseStep 1879429 = 352393) (by norm_num)
theorem B1879517 : Blo 1112627 1879517 := bbase (se 3 (by rfl) ⟨352409, by rfl⟩ : syracuseStep 1879517 = 704819) (by norm_num)
theorem B2207197 : Blo 1112627 2207197 := bbase (se 3 (by rfl) ⟨413849, by rfl⟩ : syracuseStep 2207197 = 827699) (by norm_num)
theorem B1584613 : Blo 1112627 1584613 := bbase (se 4 (by rfl) ⟨148557, by rfl⟩ : syracuseStep 1584613 = 297115) (by norm_num)
theorem B1879645 : Blo 1112627 1879645 := bbase (se 3 (by rfl) ⟨352433, by rfl⟩ : syracuseStep 1879645 = 704867) (by norm_num)
theorem B3059333 : Blo 1112627 3059333 := bbase (se 4 (by rfl) ⟨286812, by rfl⟩ : syracuseStep 3059333 = 573625) (by norm_num)
theorem B7614101 : Blo 1112627 7614101 := bbase (se 6 (by rfl) ⟨178455, by rfl⟩ : syracuseStep 7614101 = 356911) (by norm_num)
theorem B4239013 : Blo 1112627 4239013 := bbase (se 4 (by rfl) ⟨397407, by rfl⟩ : syracuseStep 4239013 = 794815) (by norm_num)
theorem B1879733 : Blo 1112627 1879733 := bbase (se 5 (by rfl) ⟨88112, by rfl⟩ : syracuseStep 1879733 = 176225) (by norm_num)
theorem B2010853 : Blo 1112627 2010853 := bbase (se 4 (by rfl) ⟨188517, by rfl⟩ : syracuseStep 2010853 = 377035) (by norm_num)
theorem B1584949 : Blo 1112627 1584949 := bbase (se 5 (by rfl) ⟨74294, by rfl⟩ : syracuseStep 1584949 = 148589) (by norm_num)
theorem B1879861 : Blo 1112627 1879861 := bbase (se 5 (by rfl) ⟨88118, by rfl⟩ : syracuseStep 1879861 = 176237) (by norm_num)
theorem B2862917 : Blo 1112627 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B1879949 : Blo 1112627 1879949 := bbase (se 3 (by rfl) ⟨352490, by rfl⟩ : syracuseStep 1879949 = 704981) (by norm_num)
theorem B1191881 : Blo 1112627 1191881 := bbase (se 2 (by rfl) ⟨446955, by rfl⟩ : syracuseStep 1191881 = 893911) (by norm_num)
theorem B4239317 : Blo 1112627 4239317 := bbase (se 7 (by rfl) ⟨49679, by rfl⟩ : syracuseStep 4239317 = 99359) (by norm_num)
theorem B1585165 : Blo 1112627 1585165 := bbase (se 3 (by rfl) ⟨297218, by rfl⟩ : syracuseStep 1585165 = 594437) (by norm_num)
theorem B1880077 : Blo 1112627 1880077 := bbase (se 3 (by rfl) ⟨352514, by rfl⟩ : syracuseStep 1880077 = 705029) (by norm_num)
theorem B5648453 : Blo 1112627 5648453 := bbase (se 4 (by rfl) ⟨529542, by rfl⟩ : syracuseStep 5648453 = 1059085) (by norm_num)
theorem B1880165 : Blo 1112627 1880165 := bbase (se 4 (by rfl) ⟨176265, by rfl⟩ : syracuseStep 1880165 = 352531) (by norm_num)
theorem B4763765 : Blo 1112627 4763765 := bbase (se 5 (by rfl) ⟨223301, by rfl⟩ : syracuseStep 4763765 = 446603) (by norm_num)
theorem B8564885 : Blo 1112627 8564885 := bbase (se 6 (by rfl) ⟨200739, by rfl⟩ : syracuseStep 8564885 = 401479) (by norm_num)
theorem B1880293 : Blo 1112627 1880293 := bbase (se 4 (by rfl) ⟨176277, by rfl⟩ : syracuseStep 1880293 = 352555) (by norm_num)
theorem B1880381 : Blo 1112627 1880381 := bbase (se 3 (by rfl) ⟨352571, by rfl⟩ : syracuseStep 1880381 = 705143) (by norm_num)
theorem B4764005 : Blo 1112627 4764005 := bbase (se 4 (by rfl) ⟨446625, by rfl⟩ : syracuseStep 4764005 = 893251) (by norm_num)
theorem B1585541 : Blo 1112627 1585541 := bbase (se 4 (by rfl) ⟨148644, by rfl⟩ : syracuseStep 1585541 = 297289) (by norm_num)
theorem B1192325 : Blo 1112627 1192325 := bbase (se 4 (by rfl) ⟨111780, by rfl⟩ : syracuseStep 1192325 = 223561) (by norm_num)
theorem B1880509 : Blo 1112627 1880509 := bbase (se 3 (by rfl) ⟨352595, by rfl⟩ : syracuseStep 1880509 = 705191) (by norm_num)
theorem B1880597 : Blo 1112627 1880597 := bbase (se 6 (by rfl) ⟨44076, by rfl⟩ : syracuseStep 1880597 = 88153) (by norm_num)
theorem B8041045 : Blo 1112627 8041045 := bbase (se 8 (by rfl) ⟨47115, by rfl⟩ : syracuseStep 8041045 = 94231) (by norm_num)
theorem B2011733 : Blo 1112627 2011733 := bbase (se 8 (by rfl) ⟨11787, by rfl⟩ : syracuseStep 2011733 = 23575) (by norm_num)
theorem B2142821 : Blo 1112627 2142821 := bbase (se 4 (by rfl) ⟨200889, by rfl⟩ : syracuseStep 2142821 = 401779) (by norm_num)
theorem B1880725 : Blo 1112627 1880725 := bbase (se 6 (by rfl) ⟨44079, by rfl⟩ : syracuseStep 1880725 = 88159) (by norm_num)
theorem B3388085 : Blo 1112627 3388085 := bbase (se 5 (by rfl) ⟨158816, by rfl⟩ : syracuseStep 3388085 = 317633) (by norm_num)
theorem B1880813 : Blo 1112627 1880813 := bbase (se 3 (by rfl) ⟨352652, by rfl⟩ : syracuseStep 1880813 = 705305) (by norm_num)
theorem B2503421 : Blo 1112627 2503421 := bbase (se 3 (by rfl) ⟨469391, by rfl⟩ : syracuseStep 2503421 = 938783) (by norm_num)
theorem B2503493 : Blo 1112627 2503493 := bbase (se 4 (by rfl) ⟨234702, by rfl⟩ : syracuseStep 2503493 = 469405) (by norm_num)
theorem B1880941 : Blo 1112627 1880941 := bbase (se 3 (by rfl) ⟨352676, by rfl⟩ : syracuseStep 1880941 = 705353) (by norm_num)
theorem B2503565 : Blo 1112627 2503565 := bbase (se 3 (by rfl) ⟨469418, by rfl⟩ : syracuseStep 2503565 = 938837) (by norm_num)
theorem B1881029 : Blo 1112627 1881029 := bbase (se 4 (by rfl) ⟨176346, by rfl⟩ : syracuseStep 1881029 = 352693) (by norm_num)
theorem B2503637 : Blo 1112627 2503637 := bbase (se 7 (by rfl) ⟨29339, by rfl⟩ : syracuseStep 2503637 = 58679) (by norm_num)
theorem B8565749 : Blo 1112627 8565749 := bbase (se 5 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 8565749 = 803039) (by norm_num)
theorem B2503709 : Blo 1112627 2503709 := bbase (se 3 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 2503709 = 938891) (by norm_num)
theorem B1881157 : Blo 1112627 1881157 := bbase (se 4 (by rfl) ⟨176358, by rfl⟩ : syracuseStep 1881157 = 352717) (by norm_num)
theorem B2503781 : Blo 1112627 2503781 := bbase (se 4 (by rfl) ⟨234729, by rfl⟩ : syracuseStep 2503781 = 469459) (by norm_num)
theorem B1782901 : Blo 1112627 1782901 := bbase (se 5 (by rfl) ⟨83573, by rfl⟩ : syracuseStep 1782901 = 167147) (by norm_num)
theorem B2864261 : Blo 1112627 2864261 := bbase (se 4 (by rfl) ⟨268524, by rfl⟩ : syracuseStep 2864261 = 537049) (by norm_num)
theorem B1881245 : Blo 1112627 1881245 := bbase (se 3 (by rfl) ⟨352733, by rfl⟩ : syracuseStep 1881245 = 705467) (by norm_num)
theorem B2503853 : Blo 1112627 2503853 := bbase (se 3 (by rfl) ⟨469472, by rfl⟩ : syracuseStep 2503853 = 938945) (by norm_num)
theorem B2503925 : Blo 1112627 2503925 := bbase (se 5 (by rfl) ⟨117371, by rfl⟩ : syracuseStep 2503925 = 234743) (by norm_num)
theorem B12694805 : Blo 1112627 12694805 := bbase (se 6 (by rfl) ⟨297534, by rfl⟩ : syracuseStep 12694805 = 595069) (by norm_num)
theorem B1881373 : Blo 1112627 1881373 := bbase (se 3 (by rfl) ⟨352757, by rfl⟩ : syracuseStep 1881373 = 705515) (by norm_num)
theorem B2503997 : Blo 1112627 2503997 := bbase (se 3 (by rfl) ⟨469499, by rfl⟩ : syracuseStep 2503997 = 938999) (by norm_num)
theorem B5649749 : Blo 1112627 5649749 := bbase (se 13 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 5649749 = 2069) (by norm_num)
theorem B1881461 : Blo 1112627 1881461 := bbase (se 5 (by rfl) ⟨88193, by rfl⟩ : syracuseStep 1881461 = 176387) (by norm_num)
theorem B2504069 : Blo 1112627 2504069 := bbase (se 4 (by rfl) ⟨234756, by rfl⟩ : syracuseStep 2504069 = 469513) (by norm_num)
theorem B2504141 : Blo 1112627 2504141 := bbase (se 3 (by rfl) ⟨469526, by rfl⟩ : syracuseStep 2504141 = 939053) (by norm_num)
theorem B14464469 : Blo 1112627 14464469 := bbase (se 7 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 14464469 = 339011) (by norm_num)
theorem B1881589 : Blo 1112627 1881589 := bbase (se 5 (by rfl) ⟨88199, by rfl⟩ : syracuseStep 1881589 = 176399) (by norm_num)
theorem B2504213 : Blo 1112627 2504213 := bbase (se 6 (by rfl) ⟨58692, by rfl⟩ : syracuseStep 2504213 = 117385) (by norm_num)
theorem B3814933 : Blo 1112627 3814933 := bbase (se 6 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 3814933 = 178825) (by norm_num)
theorem B1881677 : Blo 1112627 1881677 := bbase (se 3 (by rfl) ⟨352814, by rfl⟩ : syracuseStep 1881677 = 705629) (by norm_num)
theorem B2504285 : Blo 1112627 2504285 := bbase (se 3 (by rfl) ⟨469553, by rfl⟩ : syracuseStep 2504285 = 939107) (by norm_num)
theorem B2504357 : Blo 1112627 2504357 := bbase (se 4 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 2504357 = 469567) (by norm_num)
theorem B10303157 : Blo 1112627 10303157 := bbase (se 5 (by rfl) ⟨482960, by rfl⟩ : syracuseStep 10303157 = 965921) (by norm_num)
theorem B1881805 : Blo 1112627 1881805 := bbase (se 3 (by rfl) ⟨352838, by rfl⟩ : syracuseStep 1881805 = 705677) (by norm_num)
theorem B2504429 : Blo 1112627 2504429 := bbase (se 3 (by rfl) ⟨469580, by rfl⟩ : syracuseStep 2504429 = 939161) (by norm_num)
theorem B1586965 : Blo 1112627 1586965 := bbase (se 6 (by rfl) ⟨37194, by rfl⟩ : syracuseStep 1586965 = 74389) (by norm_num)
theorem B1881893 : Blo 1112627 1881893 := bbase (se 4 (by rfl) ⟨176427, by rfl⟩ : syracuseStep 1881893 = 352855) (by norm_num)
theorem B2504501 : Blo 1112627 2504501 := bbase (se 5 (by rfl) ⟨117398, by rfl⟩ : syracuseStep 2504501 = 234797) (by norm_num)
theorem B1783613 : Blo 1112627 1783613 := bbase (se 3 (by rfl) ⟨334427, by rfl⟩ : syracuseStep 1783613 = 668855) (by norm_num)
theorem B2504573 : Blo 1112627 2504573 := bbase (se 3 (by rfl) ⟨469607, by rfl⟩ : syracuseStep 2504573 = 939215) (by norm_num)
theorem B1882021 : Blo 1112627 1882021 := bbase (se 4 (by rfl) ⟨176439, by rfl⟩ : syracuseStep 1882021 = 352879) (by norm_num)
theorem B2504645 : Blo 1112627 2504645 := bbase (se 4 (by rfl) ⟨234810, by rfl⟩ : syracuseStep 2504645 = 469621) (by norm_num)
theorem B1882109 : Blo 1112627 1882109 := bbase (se 3 (by rfl) ⟨352895, by rfl⟩ : syracuseStep 1882109 = 705791) (by norm_num)
theorem B2504717 : Blo 1112627 2504717 := bbase (se 3 (by rfl) ⟨469634, by rfl⟩ : syracuseStep 2504717 = 939269) (by norm_num)
theorem B2504789 : Blo 1112627 2504789 := bbase (se 8 (by rfl) ⟨14676, by rfl⟩ : syracuseStep 2504789 = 29353) (by norm_num)
theorem B1882237 : Blo 1112627 1882237 := bbase (se 3 (by rfl) ⟨352919, by rfl⟩ : syracuseStep 1882237 = 705839) (by norm_num)
theorem B2504861 : Blo 1112627 2504861 := bbase (se 3 (by rfl) ⟨469661, by rfl⟩ : syracuseStep 2504861 = 939323) (by norm_num)
theorem B1882325 : Blo 1112627 1882325 := bbase (se 7 (by rfl) ⟨22058, by rfl⟩ : syracuseStep 1882325 = 44117) (by norm_num)
theorem B2504933 : Blo 1112627 2504933 := bbase (se 4 (by rfl) ⟨234837, by rfl⟩ : syracuseStep 2504933 = 469675) (by norm_num)
theorem B6338837 : Blo 1112627 6338837 := bbase (se 6 (by rfl) ⟨148566, by rfl⟩ : syracuseStep 6338837 = 297133) (by norm_num)
theorem B2505005 : Blo 1112627 2505005 := bbase (se 3 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 2505005 = 939377) (by norm_num)
theorem B1882453 : Blo 1112627 1882453 := bbase (se 10 (by rfl) ⟨2757, by rfl⟩ : syracuseStep 1882453 = 5515) (by norm_num)
theorem B1587557 : Blo 1112627 1587557 := bbase (se 4 (by rfl) ⟨148833, by rfl⟩ : syracuseStep 1587557 = 297667) (by norm_num)
theorem B2505077 : Blo 1112627 2505077 := bbase (se 5 (by rfl) ⟨117425, by rfl⟩ : syracuseStep 2505077 = 234851) (by norm_num)
theorem B1358245 : Blo 1112627 1358245 := bbase (se 4 (by rfl) ⟨127335, by rfl⟩ : syracuseStep 1358245 = 254671) (by norm_num)
theorem B1882541 : Blo 1112627 1882541 := bbase (se 3 (by rfl) ⟨352976, by rfl⟩ : syracuseStep 1882541 = 705953) (by norm_num)
theorem B1587637 : Blo 1112627 1587637 := bbase (se 5 (by rfl) ⟨74420, by rfl⟩ : syracuseStep 1587637 = 148841) (by norm_num)
theorem B2505149 : Blo 1112627 2505149 := bbase (se 3 (by rfl) ⟨469715, by rfl⟩ : syracuseStep 2505149 = 939431) (by norm_num)
theorem B1784285 : Blo 1112627 1784285 := bbase (se 3 (by rfl) ⟨334553, by rfl⟩ : syracuseStep 1784285 = 669107) (by norm_num)
theorem B2505221 : Blo 1112627 2505221 := bbase (se 4 (by rfl) ⟨234864, by rfl⟩ : syracuseStep 2505221 = 469729) (by norm_num)
theorem B1587757 : Blo 1112627 1587757 := bbase (se 3 (by rfl) ⟨297704, by rfl⟩ : syracuseStep 1587757 = 595409) (by norm_num)
theorem B1882669 : Blo 1112627 1882669 := bbase (se 3 (by rfl) ⟨353000, by rfl⟩ : syracuseStep 1882669 = 706001) (by norm_num)
theorem B2505293 : Blo 1112627 2505293 := bbase (se 3 (by rfl) ⟨469742, by rfl⟩ : syracuseStep 2505293 = 939485) (by norm_num)
theorem B1129037 : Blo 1112627 1129037 := bbase (se 3 (by rfl) ⟨211694, by rfl⟩ : syracuseStep 1129037 = 423389) (by norm_num)
theorem B4766293 : Blo 1112627 4766293 := bbase (se 8 (by rfl) ⟨27927, by rfl⟩ : syracuseStep 4766293 = 55855) (by norm_num)
theorem B5651045 : Blo 1112627 5651045 := bbase (se 4 (by rfl) ⟨529785, by rfl⟩ : syracuseStep 5651045 = 1059571) (by norm_num)
theorem B1882757 : Blo 1112627 1882757 := bbase (se 4 (by rfl) ⟨176508, by rfl⟩ : syracuseStep 1882757 = 353017) (by norm_num)
theorem B1587853 : Blo 1112627 1587853 := bbase (se 3 (by rfl) ⟨297722, by rfl⟩ : syracuseStep 1587853 = 595445) (by norm_num)
theorem B2505365 : Blo 1112627 2505365 := bbase (se 6 (by rfl) ⟨58719, by rfl⟩ : syracuseStep 2505365 = 117439) (by norm_num)
theorem B2505437 : Blo 1112627 2505437 := bbase (se 3 (by rfl) ⟨469769, by rfl⟩ : syracuseStep 2505437 = 939539) (by norm_num)
theorem B11451125 : Blo 1112627 11451125 := bbase (se 5 (by rfl) ⟨536771, by rfl⟩ : syracuseStep 11451125 = 1073543) (by norm_num)
theorem B1882885 : Blo 1112627 1882885 := bbase (se 4 (by rfl) ⟨176520, by rfl⟩ : syracuseStep 1882885 = 353041) (by norm_num)
theorem B2112293 : Blo 1112627 2112293 := bbase (se 4 (by rfl) ⟨198027, by rfl⟩ : syracuseStep 2112293 = 396055) (by norm_num)
theorem B2505509 : Blo 1112627 2505509 := bbase (se 4 (by rfl) ⟨234891, by rfl⟩ : syracuseStep 2505509 = 469783) (by norm_num)
theorem B1129297 : Blo 1112627 1129297 := bbase (se 2 (by rfl) ⟨423486, by rfl⟩ : syracuseStep 1129297 = 846973) (by norm_num)
theorem B1882973 : Blo 1112627 1882973 := bbase (se 3 (by rfl) ⟨353057, by rfl⟩ : syracuseStep 1882973 = 706115) (by norm_num)
theorem B2505581 : Blo 1112627 2505581 := bbase (se 3 (by rfl) ⟨469796, by rfl⟩ : syracuseStep 2505581 = 939593) (by norm_num)
theorem B1129345 : Blo 1112627 1129345 := bbase (se 2 (by rfl) ⟨423504, by rfl⟩ : syracuseStep 1129345 = 847009) (by norm_num)
theorem B2505653 : Blo 1112627 2505653 := bbase (se 5 (by rfl) ⟨117452, by rfl⟩ : syracuseStep 2505653 = 234905) (by norm_num)
theorem B5356469 : Blo 1112627 5356469 := bbase (se 5 (by rfl) ⟨251084, by rfl⟩ : syracuseStep 5356469 = 502169) (by norm_num)
theorem B1883101 : Blo 1112627 1883101 := bbase (se 3 (by rfl) ⟨353081, by rfl⟩ : syracuseStep 1883101 = 706163) (by norm_num)
theorem B1784797 : Blo 1112627 1784797 := bbase (se 3 (by rfl) ⟨334649, by rfl⟩ : syracuseStep 1784797 = 669299) (by norm_num)
theorem B2505725 : Blo 1112627 2505725 := bbase (se 3 (by rfl) ⟨469823, by rfl⟩ : syracuseStep 2505725 = 939647) (by norm_num)
theorem B1883189 : Blo 1112627 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B2112581 : Blo 1112627 2112581 := bbase (se 4 (by rfl) ⟨198054, by rfl⟩ : syracuseStep 2112581 = 396109) (by norm_num)
theorem B2505797 : Blo 1112627 2505797 := bbase (se 4 (by rfl) ⟨234918, by rfl⟩ : syracuseStep 2505797 = 469837) (by norm_num)
theorem B1588349 : Blo 1112627 1588349 := bbase (se 3 (by rfl) ⟨297815, by rfl⟩ : syracuseStep 1588349 = 595631) (by norm_num)
theorem B2505869 : Blo 1112627 2505869 := bbase (se 3 (by rfl) ⟨469850, by rfl⟩ : syracuseStep 2505869 = 939701) (by norm_num)
theorem B1129637 : Blo 1112627 1129637 := bbase (se 4 (by rfl) ⟨105903, by rfl⟩ : syracuseStep 1129637 = 211807) (by norm_num)
theorem B1883317 : Blo 1112627 1883317 := bbase (se 5 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 1883317 = 176561) (by norm_num)
theorem B2505941 : Blo 1112627 2505941 := bbase (se 7 (by rfl) ⟨29366, by rfl⟩ : syracuseStep 2505941 = 58733) (by norm_num)
theorem B2112733 : Blo 1112627 2112733 := bbase (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) (by norm_num)
theorem B1883405 : Blo 1112627 1883405 := bbase (se 3 (by rfl) ⟨353138, by rfl⟩ : syracuseStep 1883405 = 706277) (by norm_num)
theorem B2506013 : Blo 1112627 2506013 := bbase (se 3 (by rfl) ⟨469877, by rfl⟩ : syracuseStep 2506013 = 939755) (by norm_num)
theorem B2506085 : Blo 1112627 2506085 := bbase (se 4 (by rfl) ⟨234945, by rfl⟩ : syracuseStep 2506085 = 469891) (by norm_num)
theorem B1883533 : Blo 1112627 1883533 := bbase (se 3 (by rfl) ⟨353162, by rfl⟩ : syracuseStep 1883533 = 706325) (by norm_num)
theorem B1785253 : Blo 1112627 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B2506157 : Blo 1112627 2506157 := bbase (se 3 (by rfl) ⟨469904, by rfl⟩ : syracuseStep 2506157 = 939809) (by norm_num)
theorem B1883621 : Blo 1112627 1883621 := bbase (se 4 (by rfl) ⟨176589, by rfl⟩ : syracuseStep 1883621 = 353179) (by norm_num)
theorem B2506229 : Blo 1112627 2506229 := bbase (se 5 (by rfl) ⟨117479, by rfl⟩ : syracuseStep 2506229 = 234959) (by norm_num)
theorem B2113037 : Blo 1112627 2113037 := bbase (se 3 (by rfl) ⟨396194, by rfl⟩ : syracuseStep 2113037 = 792389) (by norm_num)
theorem B2506301 : Blo 1112627 2506301 := bbase (se 3 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 2506301 = 939863) (by norm_num)
theorem B1883749 : Blo 1112627 1883749 := bbase (se 4 (by rfl) ⟨176601, by rfl⟩ : syracuseStep 1883749 = 353203) (by norm_num)
theorem B2506373 : Blo 1112627 2506373 := bbase (se 4 (by rfl) ⟨234972, by rfl⟩ : syracuseStep 2506373 = 469945) (by norm_num)
theorem B1588901 : Blo 1112627 1588901 := bbase (se 4 (by rfl) ⟨148959, by rfl⟩ : syracuseStep 1588901 = 297919) (by norm_num)
theorem B1883837 : Blo 1112627 1883837 := bbase (se 3 (by rfl) ⟨353219, by rfl⟩ : syracuseStep 1883837 = 706439) (by norm_num)
theorem B2506445 : Blo 1112627 2506445 := bbase (se 3 (by rfl) ⟨469958, by rfl⟩ : syracuseStep 2506445 = 939917) (by norm_num)
theorem B1130221 : Blo 1112627 1130221 := bbase (se 3 (by rfl) ⟨211916, by rfl⟩ : syracuseStep 1130221 = 423833) (by norm_num)
theorem B2506517 : Blo 1112627 2506517 := bbase (se 6 (by rfl) ⟨58746, by rfl⟩ : syracuseStep 2506517 = 117493) (by norm_num)
theorem B1883965 : Blo 1112627 1883965 := bbase (se 3 (by rfl) ⟨353243, by rfl⟩ : syracuseStep 1883965 = 706487) (by norm_num)
theorem B2506589 : Blo 1112627 2506589 := bbase (se 3 (by rfl) ⟨469985, by rfl⟩ : syracuseStep 2506589 = 939971) (by norm_num)
theorem B5652341 : Blo 1112627 5652341 := bbase (se 5 (by rfl) ⟨264953, by rfl⟩ : syracuseStep 5652341 = 529907) (by norm_num)
theorem B1884053 : Blo 1112627 1884053 := bbase (se 6 (by rfl) ⟨44157, by rfl⟩ : syracuseStep 1884053 = 88315) (by norm_num)
theorem B2506661 : Blo 1112627 2506661 := bbase (se 4 (by rfl) ⟨234999, by rfl⟩ : syracuseStep 2506661 = 469999) (by norm_num)
theorem B2506733 : Blo 1112627 2506733 := bbase (se 3 (by rfl) ⟨470012, by rfl⟩ : syracuseStep 2506733 = 940025) (by norm_num)
theorem B8568821 : Blo 1112627 8568821 := bbase (se 5 (by rfl) ⟨401663, by rfl⟩ : syracuseStep 8568821 = 803327) (by norm_num)
theorem B1884181 : Blo 1112627 1884181 := bbase (se 6 (by rfl) ⟨44160, by rfl⟩ : syracuseStep 1884181 = 88321) (by norm_num)
theorem B10731541 : Blo 1112627 10731541 := bbase (se 6 (by rfl) ⟨251520, by rfl⟩ : syracuseStep 10731541 = 503041) (by norm_num)
theorem B4767781 : Blo 1112627 4767781 := bbase (se 4 (by rfl) ⟨446979, by rfl⟩ : syracuseStep 4767781 = 893959) (by norm_num)
theorem B2506805 : Blo 1112627 2506805 := bbase (se 5 (by rfl) ⟨117506, by rfl⟩ : syracuseStep 2506805 = 235013) (by norm_num)
theorem B4767797 : Blo 1112627 4767797 := bbase (se 5 (by rfl) ⟨223490, by rfl⟩ : syracuseStep 4767797 = 446981) (by norm_num)
theorem B5161013 : Blo 1112627 5161013 := bbase (se 5 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 5161013 = 483845) (by norm_num)
theorem B1785925 : Blo 1112627 1785925 := bbase (se 4 (by rfl) ⟨167430, by rfl⟩ : syracuseStep 1785925 = 334861) (by norm_num)
theorem B1884269 : Blo 1112627 1884269 := bbase (se 3 (by rfl) ⟨353300, by rfl⟩ : syracuseStep 1884269 = 706601) (by norm_num)
theorem B2506877 : Blo 1112627 2506877 := bbase (se 3 (by rfl) ⟨470039, by rfl⟩ : syracuseStep 2506877 = 940079) (by norm_num)
theorem B2506949 : Blo 1112627 2506949 := bbase (se 4 (by rfl) ⟨235026, by rfl⟩ : syracuseStep 2506949 = 470053) (by norm_num)
theorem B2113789 : Blo 1112627 2113789 := bbase (se 3 (by rfl) ⟨396335, by rfl⟩ : syracuseStep 2113789 = 792671) (by norm_num)
theorem B2507021 : Blo 1112627 2507021 := bbase (se 3 (by rfl) ⟨470066, by rfl⟩ : syracuseStep 2507021 = 940133) (by norm_num)
theorem B2507093 : Blo 1112627 2507093 := bbase (se 10 (by rfl) ⟨3672, by rfl⟩ : syracuseStep 2507093 = 7345) (by norm_num)
theorem B2113933 : Blo 1112627 2113933 := bbase (se 3 (by rfl) ⟨396362, by rfl⟩ : syracuseStep 2113933 = 792725) (by norm_num)
theorem B1589653 : Blo 1112627 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B2507165 : Blo 1112627 2507165 := bbase (se 3 (by rfl) ⟨470093, by rfl⟩ : syracuseStep 2507165 = 940187) (by norm_num)
theorem B2507237 : Blo 1112627 2507237 := bbase (se 4 (by rfl) ⟨235053, by rfl⟩ : syracuseStep 2507237 = 470107) (by norm_num)
theorem B1786349 : Blo 1112627 1786349 := bbase (se 3 (by rfl) ⟨334940, by rfl⟩ : syracuseStep 1786349 = 669881) (by norm_num)
theorem B2114093 : Blo 1112627 2114093 := bbase (se 3 (by rfl) ⟨396392, by rfl⟩ : syracuseStep 2114093 = 792785) (by norm_num)
theorem B2507309 : Blo 1112627 2507309 := bbase (se 3 (by rfl) ⟨470120, by rfl⟩ : syracuseStep 2507309 = 940241) (by norm_num)
theorem B2507381 : Blo 1112627 2507381 := bbase (se 5 (by rfl) ⟨117533, by rfl⟩ : syracuseStep 2507381 = 235067) (by norm_num)
theorem B2376373 : Blo 1112627 2376373 := bbase (se 5 (by rfl) ⟨111392, by rfl⟩ : syracuseStep 2376373 = 222785) (by norm_num)
theorem B2114237 : Blo 1112627 2114237 := bbase (se 3 (by rfl) ⟨396419, by rfl⟩ : syracuseStep 2114237 = 792839) (by norm_num)
theorem B2507453 : Blo 1112627 2507453 := bbase (se 3 (by rfl) ⟨470147, by rfl⟩ : syracuseStep 2507453 = 940295) (by norm_num)
theorem B2507525 : Blo 1112627 2507525 := bbase (se 4 (by rfl) ⟨235080, by rfl⟩ : syracuseStep 2507525 = 470161) (by norm_num)
theorem B1786637 : Blo 1112627 1786637 := bbase (se 3 (by rfl) ⟨334994, by rfl⟩ : syracuseStep 1786637 = 669989) (by norm_num)
theorem B2507597 : Blo 1112627 2507597 := bbase (se 3 (by rfl) ⟨470174, by rfl⟩ : syracuseStep 2507597 = 940349) (by norm_num)
theorem B1524629 : Blo 1112627 1524629 := bbase (se 6 (by rfl) ⟨35733, by rfl⟩ : syracuseStep 1524629 = 71467) (by norm_num)
theorem B2507669 : Blo 1112627 2507669 := bbase (se 6 (by rfl) ⟨58773, by rfl⟩ : syracuseStep 2507669 = 117547) (by norm_num)
theorem B2114525 : Blo 1112627 2114525 := bbase (se 3 (by rfl) ⟨396473, by rfl⟩ : syracuseStep 2114525 = 792947) (by norm_num)
theorem B2507741 : Blo 1112627 2507741 := bbase (se 3 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 2507741 = 940403) (by norm_num)
theorem B2507813 : Blo 1112627 2507813 := bbase (se 4 (by rfl) ⟨235107, by rfl⟩ : syracuseStep 2507813 = 470215) (by norm_num)
theorem B2507885 : Blo 1112627 2507885 := bbase (se 3 (by rfl) ⟨470228, by rfl⟩ : syracuseStep 2507885 = 940457) (by norm_num)
theorem B2114677 : Blo 1112627 2114677 := bbase (se 5 (by rfl) ⟨99125, by rfl⟩ : syracuseStep 2114677 = 198251) (by norm_num)
theorem B2376877 : Blo 1112627 2376877 := bbase (se 3 (by rfl) ⟨445664, by rfl⟩ : syracuseStep 2376877 = 891329) (by norm_num)
theorem B2507957 : Blo 1112627 2507957 := bbase (se 5 (by rfl) ⟨117560, by rfl⟩ : syracuseStep 2507957 = 235121) (by norm_num)
theorem B2508029 : Blo 1112627 2508029 := bbase (se 3 (by rfl) ⟨470255, by rfl⟩ : syracuseStep 2508029 = 940511) (by norm_num)
theorem B2508101 : Blo 1112627 2508101 := bbase (se 4 (by rfl) ⟨235134, by rfl⟩ : syracuseStep 2508101 = 470269) (by norm_num)
theorem B3818821 : Blo 1112627 3818821 := bbase (se 4 (by rfl) ⟨358014, by rfl⟩ : syracuseStep 3818821 = 716029) (by norm_num)
theorem B2508173 : Blo 1112627 2508173 := bbase (se 3 (by rfl) ⟨470282, by rfl⟩ : syracuseStep 2508173 = 940565) (by norm_num)
theorem B2114981 : Blo 1112627 2114981 := bbase (se 4 (by rfl) ⟨198279, by rfl⟩ : syracuseStep 2114981 = 396559) (by norm_num)
theorem B2508245 : Blo 1112627 2508245 := bbase (se 7 (by rfl) ⟨29393, by rfl⟩ : syracuseStep 2508245 = 58787) (by norm_num)
theorem B2508317 : Blo 1112627 2508317 := bbase (se 3 (by rfl) ⟨470309, by rfl⟩ : syracuseStep 2508317 = 940619) (by norm_num)
theorem B1787437 : Blo 1112627 1787437 := bbase (se 3 (by rfl) ⟨335144, by rfl⟩ : syracuseStep 1787437 = 670289) (by norm_num)
theorem B2508389 : Blo 1112627 2508389 := bbase (se 4 (by rfl) ⟨235161, by rfl⟩ : syracuseStep 2508389 = 470323) (by norm_num)
theorem B2508461 : Blo 1112627 2508461 := bbase (se 3 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 2508461 = 940673) (by norm_num)
theorem B2508533 : Blo 1112627 2508533 := bbase (se 5 (by rfl) ⟨117587, by rfl⟩ : syracuseStep 2508533 = 235175) (by norm_num)
theorem B4015909 : Blo 1112627 4015909 := bbase (se 4 (by rfl) ⟨376491, by rfl⟩ : syracuseStep 4015909 = 752983) (by norm_num)
theorem B2508605 : Blo 1112627 2508605 := bbase (se 3 (by rfl) ⟨470363, by rfl⟩ : syracuseStep 2508605 = 940727) (by norm_num)
theorem B8472437 : Blo 1112627 8472437 := bbase (se 5 (by rfl) ⟨397145, by rfl⟩ : syracuseStep 8472437 = 794291) (by norm_num)
theorem B2508677 : Blo 1112627 2508677 := bbase (se 4 (by rfl) ⟨235188, by rfl⟩ : syracuseStep 2508677 = 470377) (by norm_num)
theorem B2508749 : Blo 1112627 2508749 := bbase (se 3 (by rfl) ⟨470390, by rfl⟩ : syracuseStep 2508749 = 940781) (by norm_num)
theorem B2508821 : Blo 1112627 2508821 := bbase (se 6 (by rfl) ⟨58800, by rfl⟩ : syracuseStep 2508821 = 117601) (by norm_num)
theorem B2377765 : Blo 1112627 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B1787989 : Blo 1112627 1787989 := bbase (se 8 (by rfl) ⟨10476, by rfl⟩ : syracuseStep 1787989 = 20953) (by norm_num)
theorem B2508893 : Blo 1112627 2508893 := bbase (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) (by norm_num)
theorem B2115733 : Blo 1112627 2115733 := bbase (se 6 (by rfl) ⟨49587, by rfl⟩ : syracuseStep 2115733 = 99175) (by norm_num)
theorem B2508965 : Blo 1112627 2508965 := bbase (se 4 (by rfl) ⟨235215, by rfl⟩ : syracuseStep 2508965 = 470431) (by norm_num)
theorem B2509037 : Blo 1112627 2509037 := bbase (se 3 (by rfl) ⟨470444, by rfl⟩ : syracuseStep 2509037 = 940889) (by norm_num)
theorem B2115877 : Blo 1112627 2115877 := bbase (se 4 (by rfl) ⟨198363, by rfl⟩ : syracuseStep 2115877 = 396727) (by norm_num)
theorem B2509109 : Blo 1112627 2509109 := bbase (se 5 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 2509109 = 235229) (by norm_num)
theorem B1788245 : Blo 1112627 1788245 := bbase (se 10 (by rfl) ⟨2619, by rfl⟩ : syracuseStep 1788245 = 5239) (by norm_num)
theorem B1427809 : Blo 1112627 1427809 := bbase (se 2 (by rfl) ⟨535428, by rfl⟩ : syracuseStep 1427809 = 1070857) (by norm_num)
theorem B10701173 : Blo 1112627 10701173 := bbase (se 5 (by rfl) ⟨501617, by rfl⟩ : syracuseStep 10701173 = 1003235) (by norm_num)
theorem B2509181 : Blo 1112627 2509181 := bbase (se 3 (by rfl) ⟨470471, by rfl⟩ : syracuseStep 2509181 = 940943) (by norm_num)
theorem B2116037 : Blo 1112627 2116037 := bbase (se 4 (by rfl) ⟨198378, by rfl⟩ : syracuseStep 2116037 = 396757) (by norm_num)
theorem B2509253 : Blo 1112627 2509253 := bbase (se 4 (by rfl) ⟨235242, by rfl⟩ : syracuseStep 2509253 = 470485) (by norm_num)
theorem B2542085 : Blo 1112627 2542085 := bbase (se 4 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 2542085 = 476641) (by norm_num)
theorem B2509325 : Blo 1112627 2509325 := bbase (se 3 (by rfl) ⟨470498, by rfl⟩ : syracuseStep 2509325 = 940997) (by norm_num)
theorem B2378261 : Blo 1112627 2378261 := bbase (se 6 (by rfl) ⟨55740, by rfl⟩ : syracuseStep 2378261 = 111481) (by norm_num)
theorem B6015541 : Blo 1112627 6015541 := bbase (se 5 (by rfl) ⟨281978, by rfl⟩ : syracuseStep 6015541 = 563957) (by norm_num)
theorem B2116181 : Blo 1112627 2116181 := bbase (se 8 (by rfl) ⟨12399, by rfl⟩ : syracuseStep 2116181 = 24799) (by norm_num)
theorem B2509397 : Blo 1112627 2509397 := bbase (se 8 (by rfl) ⟨14703, by rfl⟩ : syracuseStep 2509397 = 29407) (by norm_num)
theorem B2509469 : Blo 1112627 2509469 := bbase (se 3 (by rfl) ⟨470525, by rfl⟩ : syracuseStep 2509469 = 941051) (by norm_num)
theorem B2509541 : Blo 1112627 2509541 := bbase (se 4 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 2509541 = 470539) (by norm_num)
theorem B2509613 : Blo 1112627 2509613 := bbase (se 3 (by rfl) ⟨470552, by rfl⟩ : syracuseStep 2509613 = 941105) (by norm_num)
theorem B1428301 : Blo 1112627 1428301 := bbase (se 3 (by rfl) ⟨267806, by rfl⟩ : syracuseStep 1428301 = 535613) (by norm_num)
theorem B2116469 : Blo 1112627 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B2509685 : Blo 1112627 2509685 := bbase (se 5 (by rfl) ⟨117641, by rfl⟩ : syracuseStep 2509685 = 235283) (by norm_num)
theorem B2509757 : Blo 1112627 2509757 := bbase (se 3 (by rfl) ⟨470579, by rfl⟩ : syracuseStep 2509757 = 941159) (by norm_num)
theorem B2509829 : Blo 1112627 2509829 := bbase (se 4 (by rfl) ⟨235296, by rfl⟩ : syracuseStep 2509829 = 470593) (by norm_num)
theorem B2116621 : Blo 1112627 2116621 := bbase (se 3 (by rfl) ⟨396866, by rfl⟩ : syracuseStep 2116621 = 793733) (by norm_num)
theorem B2509901 : Blo 1112627 2509901 := bbase (se 3 (by rfl) ⟨470606, by rfl⟩ : syracuseStep 2509901 = 941213) (by norm_num)
theorem B2673805 : Blo 1112627 2673805 := bbase (se 3 (by rfl) ⟨501338, by rfl⟩ : syracuseStep 2673805 = 1002677) (by norm_num)
theorem B1428629 : Blo 1112627 1428629 := bbase (se 6 (by rfl) ⟨33483, by rfl⟩ : syracuseStep 1428629 = 66967) (by norm_num)
theorem B2509973 : Blo 1112627 2509973 := bbase (se 6 (by rfl) ⟨58827, by rfl⟩ : syracuseStep 2509973 = 117655) (by norm_num)
theorem B2510045 : Blo 1112627 2510045 := bbase (se 3 (by rfl) ⟨470633, by rfl⟩ : syracuseStep 2510045 = 941267) (by norm_num)
theorem B16043285 : Blo 1112627 16043285 := bbase (se 6 (by rfl) ⟨376014, by rfl⟩ : syracuseStep 16043285 = 752029) (by norm_num)
theorem B4640021 : Blo 1112627 4640021 := bbase (se 6 (by rfl) ⟨108750, by rfl⟩ : syracuseStep 4640021 = 217501) (by norm_num)
theorem B2510117 : Blo 1112627 2510117 := bbase (se 4 (by rfl) ⟨235323, by rfl⟩ : syracuseStep 2510117 = 470647) (by norm_num)
theorem B2116925 : Blo 1112627 2116925 := bbase (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) (by norm_num)
theorem B2510189 : Blo 1112627 2510189 := bbase (se 3 (by rfl) ⟨470660, by rfl⟩ : syracuseStep 2510189 = 941321) (by norm_num)
theorem B2379149 : Blo 1112627 2379149 := bbase (se 3 (by rfl) ⟨446090, by rfl⟩ : syracuseStep 2379149 = 892181) (by norm_num)
theorem B3755429 : Blo 1112627 3755429 := bbase (se 4 (by rfl) ⟨352071, by rfl⟩ : syracuseStep 3755429 = 704143) (by norm_num)
theorem B2510261 : Blo 1112627 2510261 := bbase (se 5 (by rfl) ⟨117668, by rfl⟩ : syracuseStep 2510261 = 235337) (by norm_num)
theorem B2510333 : Blo 1112627 2510333 := bbase (se 3 (by rfl) ⟨470687, by rfl⟩ : syracuseStep 2510333 = 941375) (by norm_num)
theorem B2379269 : Blo 1112627 2379269 := bbase (se 4 (by rfl) ⟨223056, by rfl⟩ : syracuseStep 2379269 = 446113) (by norm_num)
theorem B5361157 : Blo 1112627 5361157 := bbase (se 4 (by rfl) ⟨502608, by rfl⟩ : syracuseStep 5361157 = 1005217) (by norm_num)
theorem B2510405 : Blo 1112627 2510405 := bbase (se 4 (by rfl) ⟨235350, by rfl⟩ : syracuseStep 2510405 = 470701) (by norm_num)
theorem B2510477 : Blo 1112627 2510477 := bbase (se 3 (by rfl) ⟨470714, by rfl⟩ : syracuseStep 2510477 = 941429) (by norm_num)
theorem B16076501 : Blo 1112627 16076501 := bbase (se 7 (by rfl) ⟨188396, by rfl⟩ : syracuseStep 16076501 = 376793) (by norm_num)
theorem B2510549 : Blo 1112627 2510549 := bbase (se 7 (by rfl) ⟨29420, by rfl⟩ : syracuseStep 2510549 = 58841) (by norm_num)
theorem B2674421 : Blo 1112627 2674421 := bbase (se 5 (by rfl) ⟨125363, by rfl⟩ : syracuseStep 2674421 = 250727) (by norm_num)
theorem B2510621 : Blo 1112627 2510621 := bbase (se 3 (by rfl) ⟨470741, by rfl⟩ : syracuseStep 2510621 = 941483) (by norm_num)
theorem B3755861 : Blo 1112627 3755861 := bbase (se 9 (by rfl) ⟨11003, by rfl⟩ : syracuseStep 3755861 = 22007) (by norm_num)
theorem B2510693 : Blo 1112627 2510693 := bbase (se 4 (by rfl) ⟨235377, by rfl⟩ : syracuseStep 2510693 = 470755) (by norm_num)
theorem B2543501 : Blo 1112627 2543501 := bbase (se 3 (by rfl) ⟨476906, by rfl⟩ : syracuseStep 2543501 = 953813) (by norm_num)
theorem B2510765 : Blo 1112627 2510765 := bbase (se 3 (by rfl) ⟨470768, by rfl⟩ : syracuseStep 2510765 = 941537) (by norm_num)
theorem B2510837 : Blo 1112627 2510837 := bbase (se 5 (by rfl) ⟨117695, by rfl⟩ : syracuseStep 2510837 = 235391) (by norm_num)
theorem B2117677 : Blo 1112627 2117677 := bbase (se 3 (by rfl) ⟨397064, by rfl⟩ : syracuseStep 2117677 = 794129) (by norm_num)
theorem B2510909 : Blo 1112627 2510909 := bbase (se 3 (by rfl) ⟨470795, by rfl⟩ : syracuseStep 2510909 = 941591) (by norm_num)
theorem B2379901 : Blo 1112627 2379901 := bbase (se 3 (by rfl) ⟨446231, by rfl⟩ : syracuseStep 2379901 = 892463) (by norm_num)
theorem B2510981 : Blo 1112627 2510981 := bbase (se 4 (by rfl) ⟨235404, by rfl⟩ : syracuseStep 2510981 = 470809) (by norm_num)
theorem B2117821 : Blo 1112627 2117821 := bbase (se 3 (by rfl) ⟨397091, by rfl⟩ : syracuseStep 2117821 = 794183) (by norm_num)
theorem B2511053 : Blo 1112627 2511053 := bbase (se 3 (by rfl) ⟨470822, by rfl⟩ : syracuseStep 2511053 = 941645) (by norm_num)
theorem B3756293 : Blo 1112627 3756293 := bbase (se 4 (by rfl) ⟨352152, by rfl⟩ : syracuseStep 3756293 = 704305) (by norm_num)
theorem B2511125 : Blo 1112627 2511125 := bbase (se 6 (by rfl) ⟨58854, by rfl⟩ : syracuseStep 2511125 = 117709) (by norm_num)
theorem B2117981 : Blo 1112627 2117981 := bbase (se 3 (by rfl) ⟨397121, by rfl⟩ : syracuseStep 2117981 = 794243) (by norm_num)
theorem B2511197 : Blo 1112627 2511197 := bbase (se 3 (by rfl) ⟨470849, by rfl⟩ : syracuseStep 2511197 = 941699) (by norm_num)
theorem B2511269 : Blo 1112627 2511269 := bbase (se 4 (by rfl) ⟨235431, by rfl⟩ : syracuseStep 2511269 = 470863) (by norm_num)
theorem B2118125 : Blo 1112627 2118125 := bbase (se 3 (by rfl) ⟨397148, by rfl⟩ : syracuseStep 2118125 = 794297) (by norm_num)
theorem B2511341 : Blo 1112627 2511341 := bbase (se 3 (by rfl) ⟨470876, by rfl⟩ : syracuseStep 2511341 = 941753) (by norm_num)
theorem B2675197 : Blo 1112627 2675197 := bbase (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) (by norm_num)
theorem B1692181 : Blo 1112627 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B2511413 : Blo 1112627 2511413 := bbase (se 5 (by rfl) ⟨117722, by rfl⟩ : syracuseStep 2511413 = 235445) (by norm_num)
theorem B2511485 : Blo 1112627 2511485 := bbase (se 3 (by rfl) ⟨470903, by rfl⟩ : syracuseStep 2511485 = 941807) (by norm_num)
theorem B3756725 : Blo 1112627 3756725 := bbase (se 5 (by rfl) ⟨176096, by rfl⟩ : syracuseStep 3756725 = 352193) (by norm_num)
theorem B2511557 : Blo 1112627 2511557 := bbase (se 4 (by rfl) ⟨235458, by rfl⟩ : syracuseStep 2511557 = 470917) (by norm_num)
theorem B1692389 : Blo 1112627 1692389 := bbase (se 4 (by rfl) ⟨158661, by rfl⟩ : syracuseStep 1692389 = 317323) (by norm_num)
theorem B2118413 : Blo 1112627 2118413 := bbase (se 3 (by rfl) ⟨397202, by rfl⟩ : syracuseStep 2118413 = 794405) (by norm_num)
theorem B2511629 : Blo 1112627 2511629 := bbase (se 3 (by rfl) ⟨470930, by rfl⟩ : syracuseStep 2511629 = 941861) (by norm_num)
theorem B6017813 : Blo 1112627 6017813 := bbase (se 6 (by rfl) ⟨141042, by rfl⟩ : syracuseStep 6017813 = 282085) (by norm_num)
theorem B1692461 : Blo 1112627 1692461 := bbase (se 3 (by rfl) ⟨317336, by rfl⟩ : syracuseStep 1692461 = 634673) (by norm_num)
theorem B7131989 : Blo 1112627 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B2511701 : Blo 1112627 2511701 := bbase (se 9 (by rfl) ⟨7358, by rfl⟩ : syracuseStep 2511701 = 14717) (by norm_num)
theorem B2511773 : Blo 1112627 2511773 := bbase (se 3 (by rfl) ⟨470957, by rfl⟩ : syracuseStep 2511773 = 941915) (by norm_num)
theorem B2118565 : Blo 1112627 2118565 := bbase (se 4 (by rfl) ⟨198615, by rfl⟩ : syracuseStep 2118565 = 397231) (by norm_num)
theorem B2511845 : Blo 1112627 2511845 := bbase (se 4 (by rfl) ⟨235485, by rfl⟩ : syracuseStep 2511845 = 470971) (by norm_num)
theorem B2380789 : Blo 1112627 2380789 := bbase (se 5 (by rfl) ⟨111599, by rfl⟩ : syracuseStep 2380789 = 223199) (by norm_num)
theorem B2511917 : Blo 1112627 2511917 := bbase (se 3 (by rfl) ⟨470984, by rfl⟩ : syracuseStep 2511917 = 941969) (by norm_num)
theorem B3757157 : Blo 1112627 3757157 := bbase (se 4 (by rfl) ⟨352233, by rfl⟩ : syracuseStep 3757157 = 704467) (by norm_num)
theorem B2380909 : Blo 1112627 2380909 := bbase (se 3 (by rfl) ⟨446420, by rfl⟩ : syracuseStep 2380909 = 892841) (by norm_num)
theorem B2544749 : Blo 1112627 2544749 := bbase (se 3 (by rfl) ⟨477140, by rfl⟩ : syracuseStep 2544749 = 954281) (by norm_num)
theorem B1430641 : Blo 1112627 1430641 := bbase (se 2 (by rfl) ⟨536490, by rfl⟩ : syracuseStep 1430641 = 1072981) (by norm_num)
theorem B2511989 : Blo 1112627 2511989 := bbase (se 5 (by rfl) ⟨117749, by rfl⟩ : syracuseStep 2511989 = 235499) (by norm_num)
theorem B2512061 : Blo 1112627 2512061 := bbase (se 3 (by rfl) ⟨471011, by rfl⟩ : syracuseStep 2512061 = 942023) (by norm_num)
theorem B2675909 : Blo 1112627 2675909 := bbase (se 4 (by rfl) ⟨250866, by rfl⟩ : syracuseStep 2675909 = 501733) (by norm_num)
theorem B2118869 : Blo 1112627 2118869 := bbase (se 7 (by rfl) ⟨24830, by rfl⟩ : syracuseStep 2118869 = 49661) (by norm_num)
theorem B2512133 : Blo 1112627 2512133 := bbase (se 4 (by rfl) ⟨235512, by rfl⟩ : syracuseStep 2512133 = 471025) (by norm_num)
theorem B2512205 : Blo 1112627 2512205 := bbase (se 3 (by rfl) ⟨471038, by rfl⟩ : syracuseStep 2512205 = 942077) (by norm_num)
theorem B2381165 : Blo 1112627 2381165 := bbase (se 3 (by rfl) ⟨446468, by rfl⟩ : syracuseStep 2381165 = 892937) (by norm_num)
theorem B2512277 : Blo 1112627 2512277 := bbase (se 6 (by rfl) ⟨58881, by rfl⟩ : syracuseStep 2512277 = 117763) (by norm_num)
theorem B2512349 : Blo 1112627 2512349 := bbase (se 3 (by rfl) ⟨471065, by rfl⟩ : syracuseStep 2512349 = 942131) (by norm_num)
theorem B3757589 : Blo 1112627 3757589 := bbase (se 6 (by rfl) ⟨88068, by rfl⟩ : syracuseStep 3757589 = 176137) (by norm_num)
theorem B2545253 : Blo 1112627 2545253 := bbase (se 4 (by rfl) ⟨238617, by rfl⟩ : syracuseStep 2545253 = 477235) (by norm_num)
theorem B4019861 : Blo 1112627 4019861 := bbase (se 6 (by rfl) ⟨94215, by rfl⟩ : syracuseStep 4019861 = 188431) (by norm_num)
theorem B1431217 : Blo 1112627 1431217 := bbase (se 2 (by rfl) ⟨536706, by rfl⟩ : syracuseStep 1431217 = 1073413) (by norm_num)
theorem B4511477 : Blo 1112627 4511477 := bbase (se 5 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 4511477 = 422951) (by norm_num)
theorem B2676581 : Blo 1112627 2676581 := bbase (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) (by norm_num)
theorem B3758021 : Blo 1112627 3758021 := bbase (se 4 (by rfl) ⟨352314, by rfl⟩ : syracuseStep 3758021 = 704629) (by norm_num)
theorem B2119621 : Blo 1112627 2119621 := bbase (se 4 (by rfl) ⟨198714, by rfl⟩ : syracuseStep 2119621 = 397429) (by norm_num)
theorem B2119765 : Blo 1112627 2119765 := bbase (se 8 (by rfl) ⟨12420, by rfl⟩ : syracuseStep 2119765 = 24841) (by norm_num)
theorem B2578645 : Blo 1112627 2578645 := bbase (se 7 (by rfl) ⟨30218, by rfl⟩ : syracuseStep 2578645 = 60437) (by norm_num)
theorem B2382053 : Blo 1112627 2382053 := bbase (se 4 (by rfl) ⟨223317, by rfl⟩ : syracuseStep 2382053 = 446635) (by norm_num)
theorem B3758453 : Blo 1112627 3758453 := bbase (se 5 (by rfl) ⟨176177, by rfl⟩ : syracuseStep 3758453 = 352355) (by norm_num)
theorem B6019541 : Blo 1112627 6019541 := bbase (se 7 (by rfl) ⟨70541, by rfl⟩ : syracuseStep 6019541 = 141083) (by norm_num)
theorem B2382293 : Blo 1112627 2382293 := bbase (se 7 (by rfl) ⟨27917, by rfl⟩ : syracuseStep 2382293 = 55835) (by norm_num)
theorem B3758885 : Blo 1112627 3758885 := bbase (se 4 (by rfl) ⟨352395, by rfl⟩ : syracuseStep 3758885 = 704791) (by norm_num)
theorem B2382797 : Blo 1112627 2382797 := bbase (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) (by norm_num)
theorem B2382805 : Blo 1112627 2382805 := bbase (se 7 (by rfl) ⟨27923, by rfl⟩ : syracuseStep 2382805 = 55847) (by norm_num)
theorem B2579653 : Blo 1112627 2579653 := bbase (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) (by norm_num)
theorem B4021445 : Blo 1112627 4021445 := bbase (se 4 (by rfl) ⟨377010, by rfl⟩ : syracuseStep 4021445 = 754021) (by norm_num)
theorem B3759317 : Blo 1112627 3759317 := bbase (se 7 (by rfl) ⟨44054, by rfl⟩ : syracuseStep 3759317 = 88109) (by norm_num)
theorem B3169829 : Blo 1112627 3169829 := bbase (se 4 (by rfl) ⟨297171, by rfl⟩ : syracuseStep 3169829 = 594343) (by norm_num)
theorem B2678341 : Blo 1112627 2678341 := bbase (se 4 (by rfl) ⟨251094, by rfl⟩ : syracuseStep 2678341 = 502189) (by norm_num)
theorem B5365349 : Blo 1112627 5365349 := bbase (se 4 (by rfl) ⟨503001, by rfl⟩ : syracuseStep 5365349 = 1006003) (by norm_num)
theorem B3759749 : Blo 1112627 3759749 := bbase (se 4 (by rfl) ⟨352476, by rfl⟩ : syracuseStep 3759749 = 704953) (by norm_num)
theorem B1269437 : Blo 1112627 1269437 := bbase (se 3 (by rfl) ⟨238019, by rfl⟩ : syracuseStep 1269437 = 476039) (by norm_num)
theorem B6348725 : Blo 1112627 6348725 := bbase (se 5 (by rfl) ⟨297596, by rfl⟩ : syracuseStep 6348725 = 595193) (by norm_num)
theorem B4513781 : Blo 1112627 4513781 := bbase (se 5 (by rfl) ⟨211583, by rfl⟩ : syracuseStep 4513781 = 423167) (by norm_num)
theorem B3760181 : Blo 1112627 3760181 := bbase (se 5 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 3760181 = 352517) (by norm_num)
theorem B2383933 : Blo 1112627 2383933 := bbase (se 3 (by rfl) ⟨446987, by rfl⟩ : syracuseStep 2383933 = 893975) (by norm_num)
theorem B4513877 : Blo 1112627 4513877 := bbase (se 8 (by rfl) ⟨26448, by rfl⟩ : syracuseStep 4513877 = 52897) (by norm_num)
theorem B2678957 : Blo 1112627 2678957 := bbase (se 3 (by rfl) ⟨502304, by rfl⟩ : syracuseStep 2678957 = 1004609) (by norm_num)
theorem B2384309 : Blo 1112627 2384309 := bbase (se 5 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 2384309 = 223529) (by norm_num)
theorem B20341205 : Blo 1112627 20341205 := bbase (se 7 (by rfl) ⟨238373, by rfl⟩ : syracuseStep 20341205 = 476747) (by norm_num)
theorem B3760613 : Blo 1112627 3760613 := bbase (se 4 (by rfl) ⟨352557, by rfl⟩ : syracuseStep 3760613 = 705115) (by norm_num)
theorem B1270669 : Blo 1112627 1270669 := bbase (se 3 (by rfl) ⟨238250, by rfl⟩ : syracuseStep 1270669 = 476501) (by norm_num)
theorem B3761045 : Blo 1112627 3761045 := bbase (se 6 (by rfl) ⟨88149, by rfl⟩ : syracuseStep 3761045 = 176299) (by norm_num)
theorem B2679725 : Blo 1112627 2679725 := bbase (se 3 (by rfl) ⟨502448, by rfl⟩ : syracuseStep 2679725 = 1004897) (by norm_num)
theorem B2679733 : Blo 1112627 2679733 := bbase (se 5 (by rfl) ⟨125612, by rfl⟩ : syracuseStep 2679733 = 251225) (by norm_num)
theorem B1270765 : Blo 1112627 1270765 := bbase (se 3 (by rfl) ⟨238268, by rfl⟩ : syracuseStep 1270765 = 476537) (by norm_num)
theorem B1270801 : Blo 1112627 1270801 := bbase (se 2 (by rfl) ⟨476550, by rfl⟩ : syracuseStep 1270801 = 953101) (by norm_num)
theorem B1696805 : Blo 1112627 1696805 := bbase (se 4 (by rfl) ⟨159075, by rfl⟩ : syracuseStep 1696805 = 318151) (by norm_num)
theorem B3171413 : Blo 1112627 3171413 := bbase (se 8 (by rfl) ⟨18582, by rfl⟩ : syracuseStep 3171413 = 37165) (by norm_num)
theorem B3761477 : Blo 1112627 3761477 := bbase (se 4 (by rfl) ⟨352638, by rfl⟩ : syracuseStep 3761477 = 705277) (by norm_num)
theorem B1860989 : Blo 1112627 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B5727653 : Blo 1112627 5727653 := bbase (se 4 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 5727653 = 1073935) (by norm_num)
theorem B11429365 : Blo 1112627 11429365 := bbase (se 5 (by rfl) ⟨535751, by rfl⟩ : syracuseStep 11429365 = 1071503) (by norm_num)
theorem B2680541 : Blo 1112627 2680541 := bbase (se 3 (by rfl) ⟨502601, by rfl⟩ : syracuseStep 2680541 = 1005203) (by norm_num)
theorem B3172085 : Blo 1112627 3172085 := bbase (se 5 (by rfl) ⟨148691, by rfl⟩ : syracuseStep 3172085 = 297383) (by norm_num)
theorem B3761909 : Blo 1112627 3761909 := bbase (se 5 (by rfl) ⟨176339, by rfl⟩ : syracuseStep 3761909 = 352679) (by norm_num)
theorem B1337137 : Blo 1112627 1337137 := bbase (se 2 (by rfl) ⟨501426, by rfl⟩ : syracuseStep 1337137 = 1002853) (by norm_num)
theorem B9168821 : Blo 1112627 9168821 := bbase (se 5 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 9168821 = 859577) (by norm_num)
theorem B3172517 : Blo 1112627 3172517 := bbase (se 4 (by rfl) ⟨297423, by rfl⟩ : syracuseStep 3172517 = 594847) (by norm_num)
theorem B3762341 : Blo 1112627 3762341 := bbase (se 4 (by rfl) ⟨352719, by rfl⟩ : syracuseStep 3762341 = 705439) (by norm_num)
theorem B36628949 : Blo 1112627 36628949 := bbase (se 7 (by rfl) ⟨429245, by rfl⟩ : syracuseStep 36628949 = 858491) (by norm_num)
theorem B3762773 : Blo 1112627 3762773 := bbase (se 8 (by rfl) ⟨22047, by rfl⟩ : syracuseStep 3762773 = 44095) (by norm_num)
theorem B1338017 : Blo 1112627 1338017 := bbase (se 2 (by rfl) ⟨501756, by rfl⟩ : syracuseStep 1338017 = 1003513) (by norm_num)
theorem B1338133 : Blo 1112627 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B3566405 : Blo 1112627 3566405 := bbase (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) (by norm_num)
theorem B3173269 : Blo 1112627 3173269 := bbase (se 6 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 3173269 = 148747) (by norm_num)
theorem B1338329 : Blo 1112627 1338329 := bbase (se 2 (by rfl) ⟨501873, by rfl⟩ : syracuseStep 1338329 = 1003747) (by norm_num)
theorem B3763205 : Blo 1112627 3763205 := bbase (se 4 (by rfl) ⟨352800, by rfl⟩ : syracuseStep 3763205 = 705601) (by norm_num)
theorem B8449109 : Blo 1112627 8449109 := bbase (se 8 (by rfl) ⟨49506, by rfl⟩ : syracuseStep 8449109 = 99013) (by norm_num)
theorem B3763637 : Blo 1112627 3763637 := bbase (se 5 (by rfl) ⟨176420, by rfl⟩ : syracuseStep 3763637 = 352841) (by norm_num)
theorem B4517365 : Blo 1112627 4517365 := bbase (se 5 (by rfl) ⟨211751, by rfl⟩ : syracuseStep 4517365 = 423503) (by norm_num)
theorem B2715125 : Blo 1112627 2715125 := bbase (se 5 (by rfl) ⟨127271, by rfl⟩ : syracuseStep 2715125 = 254543) (by norm_num)
theorem B1338877 : Blo 1112627 1338877 := bbase (se 3 (by rfl) ⟨251039, by rfl⟩ : syracuseStep 1338877 = 502079) (by norm_num)
theorem B2715245 : Blo 1112627 2715245 := bbase (se 3 (by rfl) ⟨509108, by rfl⟩ : syracuseStep 2715245 = 1018217) (by norm_num)
theorem B1339021 : Blo 1112627 1339021 := bbase (se 3 (by rfl) ⟨251066, by rfl⟩ : syracuseStep 1339021 = 502133) (by norm_num)
theorem B3534517 : Blo 1112627 3534517 := bbase (se 5 (by rfl) ⟨165680, by rfl⟩ : syracuseStep 3534517 = 331361) (by norm_num)
theorem B3764069 : Blo 1112627 3764069 := bbase (se 4 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 3764069 = 705763) (by norm_num)
theorem B3567493 : Blo 1112627 3567493 := bbase (se 4 (by rfl) ⟨334452, by rfl⟩ : syracuseStep 3567493 = 668905) (by norm_num)
theorem B3764501 : Blo 1112627 3764501 := bbase (se 6 (by rfl) ⟨88230, by rfl⟩ : syracuseStep 3764501 = 176461) (by norm_num)
theorem B8024437 : Blo 1112627 8024437 := bbase (se 5 (by rfl) ⟨376145, by rfl⟩ : syracuseStep 8024437 = 752291) (by norm_num)
theorem B15463061 : Blo 1112627 15463061 := bbase (se 6 (by rfl) ⟨362415, by rfl⟩ : syracuseStep 15463061 = 724831) (by norm_num)
theorem B1340069 : Blo 1112627 1340069 := bbase (se 4 (by rfl) ⟨125631, by rfl⟩ : syracuseStep 1340069 = 251263) (by norm_num)
theorem B3764933 : Blo 1112627 3764933 := bbase (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) (by norm_num)
theorem B2257645 : Blo 1112627 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B5632901 : Blo 1112627 5632901 := bbase (se 4 (by rfl) ⟨528084, by rfl⟩ : syracuseStep 5632901 = 1056169) (by norm_num)
theorem B1340401 : Blo 1112627 1340401 := bbase (se 2 (by rfl) ⟨502650, by rfl⟩ : syracuseStep 1340401 = 1005301) (by norm_num)
theorem B3568661 : Blo 1112627 3568661 := bbase (se 6 (by rfl) ⟨83640, by rfl⟩ : syracuseStep 3568661 = 167281) (by norm_num)
theorem B3765365 : Blo 1112627 3765365 := bbase (se 5 (by rfl) ⟨176501, by rfl⟩ : syracuseStep 3765365 = 353003) (by norm_num)
theorem B3765797 : Blo 1112627 3765797 := bbase (se 4 (by rfl) ⟨353043, by rfl⟩ : syracuseStep 3765797 = 706087) (by norm_num)
theorem B3012149 : Blo 1112627 3012149 := bbase (se 5 (by rfl) ⟨141194, by rfl⟩ : syracuseStep 3012149 = 282389) (by norm_num)
theorem B3176117 : Blo 1112627 3176117 := bbase (se 5 (by rfl) ⟨148880, by rfl⟩ : syracuseStep 3176117 = 297761) (by norm_num)
theorem B1668941 : Blo 1112627 1668941 := bbase (se 3 (by rfl) ⟨312926, by rfl⟩ : syracuseStep 1668941 = 625853) (by norm_num)
theorem B1668965 : Blo 1112627 1668965 := bbase (se 4 (by rfl) ⟨156465, by rfl⟩ : syracuseStep 1668965 = 312931) (by norm_num)
theorem B1341289 : Blo 1112627 1341289 := bbase (se 2 (by rfl) ⟨502983, by rfl⟩ : syracuseStep 1341289 = 1005967) (by norm_num)
theorem B1668989 : Blo 1112627 1668989 := bbase (se 3 (by rfl) ⟨312935, by rfl⟩ : syracuseStep 1668989 = 625871) (by norm_num)
theorem B2258813 : Blo 1112627 2258813 := bbase (se 3 (by rfl) ⟨423527, by rfl⟩ : syracuseStep 2258813 = 847055) (by norm_num)
theorem B1669013 : Blo 1112627 1669013 := bbase (se 6 (by rfl) ⟨39117, by rfl⟩ : syracuseStep 1669013 = 78235) (by norm_num)
theorem B2258837 : Blo 1112627 2258837 := bbase (se 6 (by rfl) ⟨52941, by rfl⟩ : syracuseStep 2258837 = 105883) (by norm_num)
theorem B1669037 : Blo 1112627 1669037 := bbase (se 3 (by rfl) ⟨312944, by rfl⟩ : syracuseStep 1669037 = 625889) (by norm_num)
theorem B1669061 : Blo 1112627 1669061 := bbase (se 4 (by rfl) ⟨156474, by rfl⟩ : syracuseStep 1669061 = 312949) (by norm_num)
theorem B3766229 : Blo 1112627 3766229 := bbase (se 7 (by rfl) ⟨44135, by rfl⟩ : syracuseStep 3766229 = 88271) (by norm_num)
theorem B1669085 : Blo 1112627 1669085 := bbase (se 3 (by rfl) ⟨312953, by rfl⟩ : syracuseStep 1669085 = 625907) (by norm_num)
theorem B1669109 : Blo 1112627 1669109 := bbase (se 5 (by rfl) ⟨78239, by rfl⟩ : syracuseStep 1669109 = 156479) (by norm_num)
theorem B1669133 : Blo 1112627 1669133 := bbase (se 3 (by rfl) ⟨312962, by rfl⟩ : syracuseStep 1669133 = 625925) (by norm_num)
theorem B1669157 : Blo 1112627 1669157 := bbase (se 4 (by rfl) ⟨156483, by rfl⟩ : syracuseStep 1669157 = 312967) (by norm_num)
theorem B1669181 : Blo 1112627 1669181 := bbase (se 3 (by rfl) ⟨312971, by rfl⟩ : syracuseStep 1669181 = 625943) (by norm_num)
theorem B1669205 : Blo 1112627 1669205 := bbase (se 8 (by rfl) ⟨9780, by rfl⟩ : syracuseStep 1669205 = 19561) (by norm_num)
theorem B1669229 : Blo 1112627 1669229 := bbase (se 3 (by rfl) ⟨312980, by rfl⟩ : syracuseStep 1669229 = 625961) (by norm_num)
theorem B1669253 : Blo 1112627 1669253 := bbase (se 4 (by rfl) ⟨156492, by rfl⟩ : syracuseStep 1669253 = 312985) (by norm_num)
theorem B5634197 : Blo 1112627 5634197 := bbase (se 6 (by rfl) ⟨132051, by rfl⟩ : syracuseStep 5634197 = 264103) (by norm_num)
theorem B9664661 : Blo 1112627 9664661 := bbase (se 6 (by rfl) ⟨226515, by rfl⟩ : syracuseStep 9664661 = 453031) (by norm_num)
theorem B1669277 : Blo 1112627 1669277 := bbase (se 3 (by rfl) ⟨312989, by rfl⟩ : syracuseStep 1669277 = 625979) (by norm_num)
theorem B1669301 : Blo 1112627 1669301 := bbase (se 5 (by rfl) ⟨78248, by rfl⟩ : syracuseStep 1669301 = 156497) (by norm_num)
theorem B1931453 : Blo 1112627 1931453 := bbase (se 3 (by rfl) ⟨362147, by rfl⟩ : syracuseStep 1931453 = 724295) (by norm_num)
theorem B1669325 : Blo 1112627 1669325 := bbase (se 3 (by rfl) ⟨312998, by rfl⟩ : syracuseStep 1669325 = 625997) (by norm_num)
theorem B3012821 : Blo 1112627 3012821 := bbase (se 7 (by rfl) ⟨35306, by rfl⟩ : syracuseStep 3012821 = 70613) (by norm_num)
theorem B13760725 : Blo 1112627 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B1669349 : Blo 1112627 1669349 := bbase (se 4 (by rfl) ⟨156501, by rfl⟩ : syracuseStep 1669349 = 313003) (by norm_num)
theorem B1669373 : Blo 1112627 1669373 := bbase (se 3 (by rfl) ⟨313007, by rfl⟩ : syracuseStep 1669373 = 626015) (by norm_num)
theorem B1669397 : Blo 1112627 1669397 := bbase (se 6 (by rfl) ⟨39126, by rfl⟩ : syracuseStep 1669397 = 78253) (by norm_num)
theorem B1669421 : Blo 1112627 1669421 := bbase (se 3 (by rfl) ⟨313016, by rfl⟩ : syracuseStep 1669421 = 626033) (by norm_num)
theorem B1669445 : Blo 1112627 1669445 := bbase (se 4 (by rfl) ⟨156510, by rfl⟩ : syracuseStep 1669445 = 313021) (by norm_num)
theorem B1669469 : Blo 1112627 1669469 := bbase (se 3 (by rfl) ⟨313025, by rfl⟩ : syracuseStep 1669469 = 626051) (by norm_num)
theorem B1669493 : Blo 1112627 1669493 := bbase (se 5 (by rfl) ⟨78257, by rfl⟩ : syracuseStep 1669493 = 156515) (by norm_num)
theorem B3766661 : Blo 1112627 3766661 := bbase (se 4 (by rfl) ⟨353124, by rfl⟩ : syracuseStep 3766661 = 706249) (by norm_num)
theorem B1669517 : Blo 1112627 1669517 := bbase (se 3 (by rfl) ⟨313034, by rfl⟩ : syracuseStep 1669517 = 626069) (by norm_num)
theorem B1669541 : Blo 1112627 1669541 := bbase (se 4 (by rfl) ⟨156519, by rfl⟩ : syracuseStep 1669541 = 313039) (by norm_num)
theorem B1669565 : Blo 1112627 1669565 := bbase (se 3 (by rfl) ⟨313043, by rfl⟩ : syracuseStep 1669565 = 626087) (by norm_num)
theorem B1669589 : Blo 1112627 1669589 := bbase (se 7 (by rfl) ⟨19565, by rfl⟩ : syracuseStep 1669589 = 39131) (by norm_num)
theorem B1669613 : Blo 1112627 1669613 := bbase (se 3 (by rfl) ⟨313052, by rfl⟩ : syracuseStep 1669613 = 626105) (by norm_num)
theorem B1669637 : Blo 1112627 1669637 := bbase (se 4 (by rfl) ⟨156528, by rfl⟩ : syracuseStep 1669637 = 313057) (by norm_num)
theorem B1669661 : Blo 1112627 1669661 := bbase (se 3 (by rfl) ⟨313061, by rfl⟩ : syracuseStep 1669661 = 626123) (by norm_num)
theorem B1505837 : Blo 1112627 1505837 := bbase (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) (by norm_num)
theorem B1669685 : Blo 1112627 1669685 := bbase (se 5 (by rfl) ⟨78266, by rfl⟩ : syracuseStep 1669685 = 156533) (by norm_num)
theorem B1669709 : Blo 1112627 1669709 := bbase (se 3 (by rfl) ⟨313070, by rfl⟩ : syracuseStep 1669709 = 626141) (by norm_num)
theorem B2259533 : Blo 1112627 2259533 := bbase (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) (by norm_num)
theorem B1669733 : Blo 1112627 1669733 := bbase (se 4 (by rfl) ⟨156537, by rfl⟩ : syracuseStep 1669733 = 313075) (by norm_num)
theorem B10156661 : Blo 1112627 10156661 := bbase (se 5 (by rfl) ⟨476093, by rfl⟩ : syracuseStep 10156661 = 952187) (by norm_num)
theorem B1669757 : Blo 1112627 1669757 := bbase (se 3 (by rfl) ⟨313079, by rfl⟩ : syracuseStep 1669757 = 626159) (by norm_num)
theorem B2816653 : Blo 1112627 2816653 := bbase (se 3 (by rfl) ⟨528122, by rfl⟩ : syracuseStep 2816653 = 1056245) (by norm_num)
theorem B1669781 : Blo 1112627 1669781 := bbase (se 6 (by rfl) ⟨39135, by rfl⟩ : syracuseStep 1669781 = 78271) (by norm_num)
theorem B1669805 : Blo 1112627 1669805 := bbase (se 3 (by rfl) ⟨313088, by rfl⟩ : syracuseStep 1669805 = 626177) (by norm_num)
theorem B1669829 : Blo 1112627 1669829 := bbase (se 4 (by rfl) ⟨156546, by rfl⟩ : syracuseStep 1669829 = 313093) (by norm_num)
theorem B1669853 : Blo 1112627 1669853 := bbase (se 3 (by rfl) ⟨313097, by rfl⟩ : syracuseStep 1669853 = 626195) (by norm_num)
theorem B1669877 : Blo 1112627 1669877 := bbase (se 5 (by rfl) ⟨78275, by rfl⟩ : syracuseStep 1669877 = 156551) (by norm_num)
theorem B9042677 : Blo 1112627 9042677 := bbase (se 5 (by rfl) ⟨423875, by rfl⟩ : syracuseStep 9042677 = 847751) (by norm_num)
theorem B2816765 : Blo 1112627 2816765 := bbase (se 3 (by rfl) ⟨528143, by rfl⟩ : syracuseStep 2816765 = 1056287) (by norm_num)
theorem B1669901 : Blo 1112627 1669901 := bbase (se 3 (by rfl) ⟨313106, by rfl⟩ : syracuseStep 1669901 = 626213) (by norm_num)
theorem B1669925 : Blo 1112627 1669925 := bbase (se 4 (by rfl) ⟨156555, by rfl⟩ : syracuseStep 1669925 = 313111) (by norm_num)
theorem B3767093 : Blo 1112627 3767093 := bbase (se 5 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 3767093 = 353165) (by norm_num)
theorem B1669949 : Blo 1112627 1669949 := bbase (se 3 (by rfl) ⟨313115, by rfl⟩ : syracuseStep 1669949 = 626231) (by norm_num)
theorem B4225877 : Blo 1112627 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B1669973 : Blo 1112627 1669973 := bbase (se 9 (by rfl) ⟨4892, by rfl⟩ : syracuseStep 1669973 = 9785) (by norm_num)
theorem B3570517 : Blo 1112627 3570517 := bbase (se 9 (by rfl) ⟨10460, by rfl⟩ : syracuseStep 3570517 = 20921) (by norm_num)
theorem B3177301 : Blo 1112627 3177301 := bbase (se 9 (by rfl) ⟨9308, by rfl⟩ : syracuseStep 3177301 = 18617) (by norm_num)
theorem B1669997 : Blo 1112627 1669997 := bbase (se 3 (by rfl) ⟨313124, by rfl⟩ : syracuseStep 1669997 = 626249) (by norm_num)
theorem B1670021 : Blo 1112627 1670021 := bbase (se 4 (by rfl) ⟨156564, by rfl⟩ : syracuseStep 1670021 = 313129) (by norm_num)
theorem B1670045 : Blo 1112627 1670045 := bbase (se 3 (by rfl) ⟨313133, by rfl⟩ : syracuseStep 1670045 = 626267) (by norm_num)
theorem B1670069 : Blo 1112627 1670069 := bbase (se 5 (by rfl) ⟨78284, by rfl⟩ : syracuseStep 1670069 = 156569) (by norm_num)
theorem B2816957 : Blo 1112627 2816957 := bbase (se 3 (by rfl) ⟨528179, by rfl⟩ : syracuseStep 2816957 = 1056359) (by norm_num)
theorem B1670093 : Blo 1112627 1670093 := bbase (se 3 (by rfl) ⟨313142, by rfl⟩ : syracuseStep 1670093 = 626285) (by norm_num)
theorem B1670117 : Blo 1112627 1670117 := bbase (se 4 (by rfl) ⟨156573, by rfl⟩ : syracuseStep 1670117 = 313147) (by norm_num)
theorem B3177461 : Blo 1112627 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B1670141 : Blo 1112627 1670141 := bbase (se 3 (by rfl) ⟨313151, by rfl⟩ : syracuseStep 1670141 = 626303) (by norm_num)
theorem B1670165 : Blo 1112627 1670165 := bbase (se 6 (by rfl) ⟨39144, by rfl⟩ : syracuseStep 1670165 = 78289) (by norm_num)
theorem B1670189 : Blo 1112627 1670189 := bbase (se 3 (by rfl) ⟨313160, by rfl⟩ : syracuseStep 1670189 = 626321) (by norm_num)
theorem B1670213 : Blo 1112627 1670213 := bbase (se 4 (by rfl) ⟨156582, by rfl⟩ : syracuseStep 1670213 = 313165) (by norm_num)
theorem B1670237 : Blo 1112627 1670237 := bbase (se 3 (by rfl) ⟨313169, by rfl⟩ : syracuseStep 1670237 = 626339) (by norm_num)
theorem B1670261 : Blo 1112627 1670261 := bbase (se 5 (by rfl) ⟨78293, by rfl⟩ : syracuseStep 1670261 = 156587) (by norm_num)
theorem B4226165 : Blo 1112627 4226165 := bbase (se 5 (by rfl) ⟨198101, by rfl⟩ : syracuseStep 4226165 = 396203) (by norm_num)
theorem B1670285 : Blo 1112627 1670285 := bbase (se 3 (by rfl) ⟨313178, by rfl⟩ : syracuseStep 1670285 = 626357) (by norm_num)
theorem B1670309 : Blo 1112627 1670309 := bbase (se 4 (by rfl) ⟨156591, by rfl⟩ : syracuseStep 1670309 = 313183) (by norm_num)
theorem B1670333 : Blo 1112627 1670333 := bbase (se 3 (by rfl) ⟨313187, by rfl⟩ : syracuseStep 1670333 = 626375) (by norm_num)
theorem B1408205 : Blo 1112627 1408205 := bbase (se 3 (by rfl) ⟨264038, by rfl⟩ : syracuseStep 1408205 = 528077) (by norm_num)
theorem B1670357 : Blo 1112627 1670357 := bbase (se 7 (by rfl) ⟨19574, by rfl⟩ : syracuseStep 1670357 = 39149) (by norm_num)
theorem B3177701 : Blo 1112627 3177701 := bbase (se 4 (by rfl) ⟨297909, by rfl⟩ : syracuseStep 3177701 = 595819) (by norm_num)
theorem B3767525 : Blo 1112627 3767525 := bbase (se 4 (by rfl) ⟨353205, by rfl⟩ : syracuseStep 3767525 = 706411) (by norm_num)
theorem B1670381 : Blo 1112627 1670381 := bbase (se 3 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 1670381 = 626393) (by norm_num)
theorem B1408261 : Blo 1112627 1408261 := bbase (se 4 (by rfl) ⟨132024, by rfl⟩ : syracuseStep 1408261 = 264049) (by norm_num)
theorem B1670405 : Blo 1112627 1670405 := bbase (se 4 (by rfl) ⟨156600, by rfl⟩ : syracuseStep 1670405 = 313201) (by norm_num)
theorem B2817301 : Blo 1112627 2817301 := bbase (se 6 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 2817301 = 132061) (by norm_num)
theorem B1670429 : Blo 1112627 1670429 := bbase (se 3 (by rfl) ⟨313205, by rfl⟩ : syracuseStep 1670429 = 626411) (by norm_num)
theorem B1670453 : Blo 1112627 1670453 := bbase (se 5 (by rfl) ⟨78302, by rfl⟩ : syracuseStep 1670453 = 156605) (by norm_num)
theorem B9534773 : Blo 1112627 9534773 := bbase (se 5 (by rfl) ⟨446942, by rfl⟩ : syracuseStep 9534773 = 893885) (by norm_num)
theorem B1670477 : Blo 1112627 1670477 := bbase (se 3 (by rfl) ⟨313214, by rfl⟩ : syracuseStep 1670477 = 626429) (by norm_num)
theorem B1408357 : Blo 1112627 1408357 := bbase (se 4 (by rfl) ⟨132033, by rfl⟩ : syracuseStep 1408357 = 264067) (by norm_num)
theorem B1670501 : Blo 1112627 1670501 := bbase (se 4 (by rfl) ⟨156609, by rfl⟩ : syracuseStep 1670501 = 313219) (by norm_num)
theorem B5078389 : Blo 1112627 5078389 := bbase (se 5 (by rfl) ⟨238049, by rfl⟩ : syracuseStep 5078389 = 476099) (by norm_num)
theorem B1670525 : Blo 1112627 1670525 := bbase (se 3 (by rfl) ⟨313223, by rfl⟩ : syracuseStep 1670525 = 626447) (by norm_num)
theorem B2817413 : Blo 1112627 2817413 := bbase (se 4 (by rfl) ⟨264132, by rfl⟩ : syracuseStep 2817413 = 528265) (by norm_num)
theorem B1670549 : Blo 1112627 1670549 := bbase (se 6 (by rfl) ⟨39153, by rfl⟩ : syracuseStep 1670549 = 78307) (by norm_num)
theorem B3177893 : Blo 1112627 3177893 := bbase (se 4 (by rfl) ⟨297927, by rfl⟩ : syracuseStep 3177893 = 595855) (by norm_num)
theorem B5635493 : Blo 1112627 5635493 := bbase (se 4 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 5635493 = 1056655) (by norm_num)
theorem B1670573 : Blo 1112627 1670573 := bbase (se 3 (by rfl) ⟨313232, by rfl⟩ : syracuseStep 1670573 = 626465) (by norm_num)
theorem B1670597 : Blo 1112627 1670597 := bbase (se 4 (by rfl) ⟨156618, by rfl⟩ : syracuseStep 1670597 = 313237) (by norm_num)
theorem B1670621 : Blo 1112627 1670621 := bbase (se 3 (by rfl) ⟨313241, by rfl⟩ : syracuseStep 1670621 = 626483) (by norm_num)
theorem B1670645 : Blo 1112627 1670645 := bbase (se 5 (by rfl) ⟨78311, by rfl⟩ : syracuseStep 1670645 = 156623) (by norm_num)
theorem B5078533 : Blo 1112627 5078533 := bbase (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) (by norm_num)
theorem B1670669 : Blo 1112627 1670669 := bbase (se 3 (by rfl) ⟨313250, by rfl⟩ : syracuseStep 1670669 = 626501) (by norm_num)
theorem B1408529 : Blo 1112627 1408529 := bbase (se 2 (by rfl) ⟨528198, by rfl⟩ : syracuseStep 1408529 = 1056397) (by norm_num)
theorem B1670693 : Blo 1112627 1670693 := bbase (se 4 (by rfl) ⟨156627, by rfl⟩ : syracuseStep 1670693 = 313255) (by norm_num)
theorem B1670717 : Blo 1112627 1670717 := bbase (se 3 (by rfl) ⟨313259, by rfl⟩ : syracuseStep 1670717 = 626519) (by norm_num)
theorem B2817605 : Blo 1112627 2817605 := bbase (se 4 (by rfl) ⟨264150, by rfl⟩ : syracuseStep 2817605 = 528301) (by norm_num)
theorem B1408585 : Blo 1112627 1408585 := bbase (se 2 (by rfl) ⟨528219, by rfl⟩ : syracuseStep 1408585 = 1056439) (by norm_num)
theorem B1670741 : Blo 1112627 1670741 := bbase (se 8 (by rfl) ⟨9789, by rfl⟩ : syracuseStep 1670741 = 19579) (by norm_num)
theorem B1670765 : Blo 1112627 1670765 := bbase (se 3 (by rfl) ⟨313268, by rfl⟩ : syracuseStep 1670765 = 626537) (by norm_num)
theorem B1670789 : Blo 1112627 1670789 := bbase (se 4 (by rfl) ⟨156636, by rfl⟩ : syracuseStep 1670789 = 313273) (by norm_num)
theorem B3767957 : Blo 1112627 3767957 := bbase (se 6 (by rfl) ⟨88311, by rfl⟩ : syracuseStep 3767957 = 176623) (by norm_num)
theorem B1670813 : Blo 1112627 1670813 := bbase (se 3 (by rfl) ⟨313277, by rfl⟩ : syracuseStep 1670813 = 626555) (by norm_num)
theorem B2260637 : Blo 1112627 2260637 := bbase (se 3 (by rfl) ⟨423869, by rfl⟩ : syracuseStep 2260637 = 847739) (by norm_num)
theorem B1408681 : Blo 1112627 1408681 := bbase (se 2 (by rfl) ⟨528255, by rfl⟩ : syracuseStep 1408681 = 1056511) (by norm_num)
theorem B1670837 : Blo 1112627 1670837 := bbase (se 5 (by rfl) ⟨78320, by rfl⟩ : syracuseStep 1670837 = 156641) (by norm_num)
theorem B2064061 : Blo 1112627 2064061 := bbase (se 3 (by rfl) ⟨387011, by rfl⟩ : syracuseStep 2064061 = 774023) (by norm_num)
theorem B1670861 : Blo 1112627 1670861 := bbase (se 3 (by rfl) ⟨313286, by rfl⟩ : syracuseStep 1670861 = 626573) (by norm_num)
theorem B1670885 : Blo 1112627 1670885 := bbase (se 4 (by rfl) ⟨156645, by rfl⟩ : syracuseStep 1670885 = 313291) (by norm_num)
theorem B1670909 : Blo 1112627 1670909 := bbase (se 3 (by rfl) ⟨313295, by rfl⟩ : syracuseStep 1670909 = 626591) (by norm_num)
theorem B1670933 : Blo 1112627 1670933 := bbase (se 6 (by rfl) ⟨39162, by rfl⟩ : syracuseStep 1670933 = 78325) (by norm_num)
theorem B1670957 : Blo 1112627 1670957 := bbase (se 3 (by rfl) ⟨313304, by rfl⟩ : syracuseStep 1670957 = 626609) (by norm_num)
theorem B10714933 : Blo 1112627 10714933 := bbase (se 5 (by rfl) ⟨502262, by rfl⟩ : syracuseStep 10714933 = 1004525) (by norm_num)
theorem B6356789 : Blo 1112627 6356789 := bbase (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) (by norm_num)
theorem B1670981 : Blo 1112627 1670981 := bbase (se 4 (by rfl) ⟨156654, by rfl⟩ : syracuseStep 1670981 = 313309) (by norm_num)
theorem B1408853 : Blo 1112627 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B1671005 : Blo 1112627 1671005 := bbase (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) (by norm_num)
theorem B1671029 : Blo 1112627 1671029 := bbase (se 5 (by rfl) ⟨78329, by rfl⟩ : syracuseStep 1671029 = 156659) (by norm_num)
theorem B1408909 : Blo 1112627 1408909 := bbase (se 3 (by rfl) ⟨264170, by rfl⟩ : syracuseStep 1408909 = 528341) (by norm_num)
theorem B1671053 : Blo 1112627 1671053 := bbase (se 3 (by rfl) ⟨313322, by rfl⟩ : syracuseStep 1671053 = 626645) (by norm_num)
theorem B2817949 : Blo 1112627 2817949 := bbase (se 3 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 2817949 = 1056731) (by norm_num)
theorem B1671077 : Blo 1112627 1671077 := bbase (se 4 (by rfl) ⟨156663, by rfl⟩ : syracuseStep 1671077 = 313327) (by norm_num)
theorem B1933229 : Blo 1112627 1933229 := bbase (se 3 (by rfl) ⟨362480, by rfl⟩ : syracuseStep 1933229 = 724961) (by norm_num)
theorem B1671101 : Blo 1112627 1671101 := bbase (se 3 (by rfl) ⟨313331, by rfl⟩ : syracuseStep 1671101 = 626663) (by norm_num)
theorem B1671125 : Blo 1112627 1671125 := bbase (se 7 (by rfl) ⟨19583, by rfl⟩ : syracuseStep 1671125 = 39167) (by norm_num)
theorem B1409005 : Blo 1112627 1409005 := bbase (se 3 (by rfl) ⟨264188, by rfl⟩ : syracuseStep 1409005 = 528377) (by norm_num)
theorem B1671149 : Blo 1112627 1671149 := bbase (se 3 (by rfl) ⟨313340, by rfl⟩ : syracuseStep 1671149 = 626681) (by norm_num)
theorem B1114115 : Blo 1112627 1114115 := bstep (se 1 (by rfl) ⟨835586, by rfl⟩ : syracuseStep 1114115 = 1671173) B1671173
theorem B1671185 : Blo 1112627 1671185 := bstep (se 2 (by rfl) ⟨626694, by rfl⟩ : syracuseStep 1671185 = 1253389) B1253389
theorem B1114131 : Blo 1112627 1114131 := bstep (se 1 (by rfl) ⟨835598, by rfl⟩ : syracuseStep 1114131 = 1671197) B1671197
theorem B1671203 : Blo 1112627 1671203 := bstep (se 1 (by rfl) ⟨1253402, by rfl⟩ : syracuseStep 1671203 = 2506805) B2506805
theorem B1114147 : Blo 1112627 1114147 := bstep (se 1 (by rfl) ⟨835610, by rfl⟩ : syracuseStep 1114147 = 1671221) B1671221
theorem B3178531 : Blo 1112627 3178531 := bstep (se 1 (by rfl) ⟨2383898, by rfl⟩ : syracuseStep 3178531 = 4767797) B4767797
theorem B3440675 : Blo 1112627 3440675 := bstep (se 1 (by rfl) ⟨2580506, by rfl⟩ : syracuseStep 3440675 = 5161013) B5161013
theorem B6357041 : Blo 1112627 6357041 := bstep (se 2 (by rfl) ⟨2383890, by rfl⟩ : syracuseStep 6357041 = 4767781) B4767781
theorem B1114163 : Blo 1112627 1114163 := bstep (se 1 (by rfl) ⟨835622, by rfl⟩ : syracuseStep 1114163 = 1671245) B1671245
theorem B1671233 : Blo 1112627 1671233 := bstep (se 2 (by rfl) ⟨626712, by rfl⟩ : syracuseStep 1671233 = 1253425) B1253425
theorem B1114179 : Blo 1112627 1114179 := bstep (se 1 (by rfl) ⟨835634, by rfl⟩ : syracuseStep 1114179 = 1671269) B1671269
theorem B3178577 : Blo 1112627 3178577 := bstep (se 2 (by rfl) ⟨1191966, by rfl⟩ : syracuseStep 3178577 = 2383933) B2383933
theorem B1671251 : Blo 1112627 1671251 := bstep (se 1 (by rfl) ⟨1253438, by rfl⟩ : syracuseStep 1671251 = 2506877) B2506877
theorem B1114195 : Blo 1112627 1114195 := bstep (se 1 (by rfl) ⟨835646, by rfl⟩ : syracuseStep 1114195 = 1671293) B1671293
theorem B1114211 : Blo 1112627 1114211 := bstep (se 1 (by rfl) ⟨835658, by rfl⟩ : syracuseStep 1114211 = 1671317) B1671317
theorem B91455601 : Blo 1112627 91455601 := bstep (se 2 (by rfl) ⟨34295850, by rfl⟩ : syracuseStep 91455601 = 68591701) B68591701
theorem B1671281 : Blo 1112627 1671281 := bstep (se 2 (by rfl) ⟨626730, by rfl⟩ : syracuseStep 1671281 = 1253461) B1253461
theorem B1114227 : Blo 1112627 1114227 := bstep (se 1 (by rfl) ⟨835670, by rfl⟩ : syracuseStep 1114227 = 1671341) B1671341
theorem B1671299 : Blo 1112627 1671299 := bstep (se 1 (by rfl) ⟨1253474, by rfl⟩ : syracuseStep 1671299 = 2506949) B2506949
theorem B1114243 : Blo 1112627 1114243 := bstep (se 1 (by rfl) ⟨835682, by rfl⟩ : syracuseStep 1114243 = 1671365) B1671365
theorem B1114259 : Blo 1112627 1114259 := bstep (se 1 (by rfl) ⟨835694, by rfl⟩ : syracuseStep 1114259 = 1671389) B1671389
theorem B1671329 : Blo 1112627 1671329 := bstep (se 2 (by rfl) ⟨626748, by rfl⟩ : syracuseStep 1671329 = 1253497) B1253497
theorem B1114275 : Blo 1112627 1114275 := bstep (se 1 (by rfl) ⟨835706, by rfl⟩ : syracuseStep 1114275 = 1671413) B1671413
theorem B4292785 : Blo 1112627 4292785 := bstep (se 2 (by rfl) ⟨1609794, by rfl⟩ : syracuseStep 4292785 = 3219589) B3219589
theorem B3768497 : Blo 1112627 3768497 := bstep (se 2 (by rfl) ⟨1413186, by rfl⟩ : syracuseStep 3768497 = 2826373) B2826373
theorem B1671347 : Blo 1112627 1671347 := bstep (se 1 (by rfl) ⟨1253510, by rfl⟩ : syracuseStep 1671347 = 2507021) B2507021
theorem B1114291 : Blo 1112627 1114291 := bstep (se 1 (by rfl) ⟨835718, by rfl⟩ : syracuseStep 1114291 = 1671437) B1671437
theorem B1114307 : Blo 1112627 1114307 := bstep (se 1 (by rfl) ⟨835730, by rfl⟩ : syracuseStep 1114307 = 1671461) B1671461
theorem B1671377 : Blo 1112627 1671377 := bstep (se 2 (by rfl) ⟨626766, by rfl⟩ : syracuseStep 1671377 = 1253533) B1253533
theorem B1114323 : Blo 1112627 1114323 := bstep (se 1 (by rfl) ⟨835742, by rfl⟩ : syracuseStep 1114323 = 1671485) B1671485
theorem B1671395 : Blo 1112627 1671395 := bstep (se 1 (by rfl) ⟨1253546, by rfl⟩ : syracuseStep 1671395 = 2507093) B2507093
theorem B1114339 : Blo 1112627 1114339 := bstep (se 1 (by rfl) ⟨835754, by rfl⟩ : syracuseStep 1114339 = 1671509) B1671509
theorem B1114355 : Blo 1112627 1114355 := bstep (se 1 (by rfl) ⟨835766, by rfl⟩ : syracuseStep 1114355 = 1671533) B1671533
theorem B1671425 : Blo 1112627 1671425 := bstep (se 2 (by rfl) ⟨626784, by rfl⟩ : syracuseStep 1671425 = 1253569) B1253569
theorem B1114371 : Blo 1112627 1114371 := bstep (se 1 (by rfl) ⟨835778, by rfl⟩ : syracuseStep 1114371 = 1671557) B1671557
theorem B1671443 : Blo 1112627 1671443 := bstep (se 1 (by rfl) ⟨1253582, by rfl⟩ : syracuseStep 1671443 = 2507165) B2507165
theorem B1114387 : Blo 1112627 1114387 := bstep (se 1 (by rfl) ⟨835790, by rfl⟩ : syracuseStep 1114387 = 1671581) B1671581
theorem B1114403 : Blo 1112627 1114403 := bstep (se 1 (by rfl) ⟨835802, by rfl⟩ : syracuseStep 1114403 = 1671605) B1671605
theorem B1671473 : Blo 1112627 1671473 := bstep (se 2 (by rfl) ⟨626802, by rfl⟩ : syracuseStep 1671473 = 1253605) B1253605
theorem B1114419 : Blo 1112627 1114419 := bstep (se 1 (by rfl) ⟨835814, by rfl⟩ : syracuseStep 1114419 = 1671629) B1671629
theorem B1671491 : Blo 1112627 1671491 := bstep (se 1 (by rfl) ⟨1253618, by rfl⟩ : syracuseStep 1671491 = 2507237) B2507237
theorem B1114435 : Blo 1112627 1114435 := bstep (se 1 (by rfl) ⟨835826, by rfl⟩ : syracuseStep 1114435 = 1671653) B1671653
theorem B2818385 : Blo 1112627 2818385 := bstep (se 2 (by rfl) ⟨1056894, by rfl⟩ : syracuseStep 2818385 = 2113789) B2113789
theorem B1114451 : Blo 1112627 1114451 := bstep (se 1 (by rfl) ⟨835838, by rfl⟩ : syracuseStep 1114451 = 1671677) B1671677
theorem B1671521 : Blo 1112627 1671521 := bstep (se 2 (by rfl) ⟨626820, by rfl⟩ : syracuseStep 1671521 = 1253641) B1253641
theorem B1114467 : Blo 1112627 1114467 := bstep (se 1 (by rfl) ⟨835850, by rfl⟩ : syracuseStep 1114467 = 1671701) B1671701
theorem B5636465 : Blo 1112627 5636465 := bstep (se 2 (by rfl) ⟨2113674, by rfl⟩ : syracuseStep 5636465 = 4227349) B4227349
theorem B1409395 : Blo 1112627 1409395 := bstep (se 1 (by rfl) ⟨1057046, by rfl⟩ : syracuseStep 1409395 = 2114093) B2114093
theorem B1671539 : Blo 1112627 1671539 := bstep (se 1 (by rfl) ⟨1253654, by rfl⟩ : syracuseStep 1671539 = 2507309) B2507309
theorem B1114483 : Blo 1112627 1114483 := bstep (se 1 (by rfl) ⟨835862, by rfl⟩ : syracuseStep 1114483 = 1671725) B1671725
theorem B2818435 : Blo 1112627 2818435 := bstep (se 1 (by rfl) ⟨2113826, by rfl⟩ : syracuseStep 2818435 = 4227653) B4227653
theorem B1114499 : Blo 1112627 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B1671569 : Blo 1112627 1671569 := bstep (se 2 (by rfl) ⟨626838, by rfl⟩ : syracuseStep 1671569 = 1253677) B1253677
theorem B1114515 : Blo 1112627 1114515 := bstep (se 1 (by rfl) ⟨835886, by rfl⟩ : syracuseStep 1114515 = 1671773) B1671773
theorem B1671587 : Blo 1112627 1671587 := bstep (se 1 (by rfl) ⟨1253690, by rfl⟩ : syracuseStep 1671587 = 2507381) B2507381
theorem B1114531 : Blo 1112627 1114531 := bstep (se 1 (by rfl) ⟨835898, by rfl⟩ : syracuseStep 1114531 = 1671797) B1671797
theorem B1114547 : Blo 1112627 1114547 := bstep (se 1 (by rfl) ⟨835910, by rfl⟩ : syracuseStep 1114547 = 1671821) B1671821
theorem B1671617 : Blo 1112627 1671617 := bstep (se 2 (by rfl) ⟨626856, by rfl⟩ : syracuseStep 1671617 = 1253713) B1253713
theorem B1114563 : Blo 1112627 1114563 := bstep (se 1 (by rfl) ⟨835922, by rfl⟩ : syracuseStep 1114563 = 1671845) B1671845
theorem B1409491 : Blo 1112627 1409491 := bstep (se 1 (by rfl) ⟨1057118, by rfl⟩ : syracuseStep 1409491 = 2114237) B2114237
theorem B1671635 : Blo 1112627 1671635 := bstep (se 1 (by rfl) ⟨1253726, by rfl⟩ : syracuseStep 1671635 = 2507453) B2507453
theorem B1114579 : Blo 1112627 1114579 := bstep (se 1 (by rfl) ⟨835934, by rfl⟩ : syracuseStep 1114579 = 1671869) B1671869
theorem B1114595 : Blo 1112627 1114595 := bstep (se 1 (by rfl) ⟨835946, by rfl⟩ : syracuseStep 1114595 = 1671893) B1671893
theorem B1671665 : Blo 1112627 1671665 := bstep (se 2 (by rfl) ⟨626874, by rfl⟩ : syracuseStep 1671665 = 1253749) B1253749
theorem B1114611 : Blo 1112627 1114611 := bstep (se 1 (by rfl) ⟨835958, by rfl⟩ : syracuseStep 1114611 = 1671917) B1671917
theorem B1671683 : Blo 1112627 1671683 := bstep (se 1 (by rfl) ⟨1253762, by rfl⟩ : syracuseStep 1671683 = 2507525) B2507525
theorem B1114627 : Blo 1112627 1114627 := bstep (se 1 (by rfl) ⟨835970, by rfl⟩ : syracuseStep 1114627 = 1671941) B1671941
theorem B2818577 : Blo 1112627 2818577 := bstep (se 2 (by rfl) ⟨1056966, by rfl⟩ : syracuseStep 2818577 = 2113933) B2113933
theorem B1114643 : Blo 1112627 1114643 := bstep (se 1 (by rfl) ⟨835982, by rfl⟩ : syracuseStep 1114643 = 1671965) B1671965
theorem B1671713 : Blo 1112627 1671713 := bstep (se 2 (by rfl) ⟨626892, by rfl⟩ : syracuseStep 1671713 = 1253785) B1253785
theorem B1114659 : Blo 1112627 1114659 := bstep (se 1 (by rfl) ⟨835994, by rfl⟩ : syracuseStep 1114659 = 1671989) B1671989
theorem B1671731 : Blo 1112627 1671731 := bstep (se 1 (by rfl) ⟨1253798, by rfl⟩ : syracuseStep 1671731 = 2507597) B2507597
theorem B1114675 : Blo 1112627 1114675 := bstep (se 1 (by rfl) ⟨836006, by rfl⟩ : syracuseStep 1114675 = 1672013) B1672013
theorem B1114691 : Blo 1112627 1114691 := bstep (se 1 (by rfl) ⟨836018, by rfl⟩ : syracuseStep 1114691 = 1672037) B1672037
theorem B1671761 : Blo 1112627 1671761 := bstep (se 2 (by rfl) ⟨626910, by rfl⟩ : syracuseStep 1671761 = 1253821) B1253821
theorem B1114707 : Blo 1112627 1114707 := bstep (se 1 (by rfl) ⟨836030, by rfl⟩ : syracuseStep 1114707 = 1672061) B1672061
theorem B1671779 : Blo 1112627 1671779 := bstep (se 1 (by rfl) ⟨1253834, by rfl⟩ : syracuseStep 1671779 = 2507669) B2507669
theorem B1114723 : Blo 1112627 1114723 := bstep (se 1 (by rfl) ⟨836042, by rfl⟩ : syracuseStep 1114723 = 1672085) B1672085
theorem B1114739 : Blo 1112627 1114739 := bstep (se 1 (by rfl) ⟨836054, by rfl⟩ : syracuseStep 1114739 = 1672109) B1672109
theorem B1671809 : Blo 1112627 1671809 := bstep (se 2 (by rfl) ⟨626928, by rfl⟩ : syracuseStep 1671809 = 1253857) B1253857
theorem B1114755 : Blo 1112627 1114755 := bstep (se 1 (by rfl) ⟨836066, by rfl⟩ : syracuseStep 1114755 = 1672133) B1672133
theorem B1671827 : Blo 1112627 1671827 := bstep (se 1 (by rfl) ⟨1253870, by rfl⟩ : syracuseStep 1671827 = 2507741) B2507741
theorem B1114771 : Blo 1112627 1114771 := bstep (se 1 (by rfl) ⟨836078, by rfl⟩ : syracuseStep 1114771 = 1672157) B1672157
theorem B1114787 : Blo 1112627 1114787 := bstep (se 1 (by rfl) ⟨836090, by rfl⟩ : syracuseStep 1114787 = 1672181) B1672181
theorem B1671857 : Blo 1112627 1671857 := bstep (se 2 (by rfl) ⟨626946, by rfl⟩ : syracuseStep 1671857 = 1253893) B1253893
theorem B1114803 : Blo 1112627 1114803 := bstep (se 1 (by rfl) ⟨836102, by rfl⟩ : syracuseStep 1114803 = 1672205) B1672205
theorem B1671875 : Blo 1112627 1671875 := bstep (se 1 (by rfl) ⟨1253906, by rfl⟩ : syracuseStep 1671875 = 2507813) B2507813
theorem B1114819 : Blo 1112627 1114819 := bstep (se 1 (by rfl) ⟨836114, by rfl⟩ : syracuseStep 1114819 = 1672229) B1672229
theorem B1114835 : Blo 1112627 1114835 := bstep (se 1 (by rfl) ⟨836126, by rfl⟩ : syracuseStep 1114835 = 1672253) B1672253
theorem B1671905 : Blo 1112627 1671905 := bstep (se 2 (by rfl) ⟨626964, by rfl⟩ : syracuseStep 1671905 = 1253929) B1253929
theorem B1114851 : Blo 1112627 1114851 := bstep (se 1 (by rfl) ⟨836138, by rfl⟩ : syracuseStep 1114851 = 1672277) B1672277
theorem B5079793 : Blo 1112627 5079793 := bstep (se 2 (by rfl) ⟨1904922, by rfl⟩ : syracuseStep 5079793 = 3809845) B3809845
theorem B1671923 : Blo 1112627 1671923 := bstep (se 1 (by rfl) ⟨1253942, by rfl⟩ : syracuseStep 1671923 = 2507885) B2507885
theorem B1114867 : Blo 1112627 1114867 := bstep (se 1 (by rfl) ⟨836150, by rfl⟩ : syracuseStep 1114867 = 1672301) B1672301
theorem B1114883 : Blo 1112627 1114883 := bstep (se 1 (by rfl) ⟨836162, by rfl⟩ : syracuseStep 1114883 = 1672325) B1672325
theorem B1671953 : Blo 1112627 1671953 := bstep (se 2 (by rfl) ⟨626982, by rfl⟩ : syracuseStep 1671953 = 1253965) B1253965
theorem B1114899 : Blo 1112627 1114899 := bstep (se 1 (by rfl) ⟨836174, by rfl⟩ : syracuseStep 1114899 = 1672349) B1672349
theorem B1671971 : Blo 1112627 1671971 := bstep (se 1 (by rfl) ⟨1253978, by rfl⟩ : syracuseStep 1671971 = 2507957) B2507957
theorem B1114915 : Blo 1112627 1114915 := bstep (se 1 (by rfl) ⟨836186, by rfl⟩ : syracuseStep 1114915 = 1672373) B1672373
theorem B1114931 : Blo 1112627 1114931 := bstep (se 1 (by rfl) ⟨836198, by rfl⟩ : syracuseStep 1114931 = 1672397) B1672397
theorem B1672001 : Blo 1112627 1672001 := bstep (se 2 (by rfl) ⟨627000, by rfl⟩ : syracuseStep 1672001 = 1254001) B1254001
theorem B1114947 : Blo 1112627 1114947 := bstep (se 1 (by rfl) ⟨836210, by rfl⟩ : syracuseStep 1114947 = 1672421) B1672421
theorem B1672019 : Blo 1112627 1672019 := bstep (se 1 (by rfl) ⟨1254014, by rfl⟩ : syracuseStep 1672019 = 2508029) B2508029
theorem B1114963 : Blo 1112627 1114963 := bstep (se 1 (by rfl) ⟨836222, by rfl⟩ : syracuseStep 1114963 = 1672445) B1672445
theorem B3212131 : Blo 1112627 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B1114979 : Blo 1112627 1114979 := bstep (se 1 (by rfl) ⟨836234, by rfl⟩ : syracuseStep 1114979 = 1672469) B1672469
theorem B1672049 : Blo 1112627 1672049 := bstep (se 2 (by rfl) ⟨627018, by rfl⟩ : syracuseStep 1672049 = 1254037) B1254037
theorem B1114995 : Blo 1112627 1114995 := bstep (se 1 (by rfl) ⟨836246, by rfl⟩ : syracuseStep 1114995 = 1672493) B1672493
theorem B1672067 : Blo 1112627 1672067 := bstep (se 1 (by rfl) ⟨1254050, by rfl⟩ : syracuseStep 1672067 = 2508101) B2508101
theorem B1115011 : Blo 1112627 1115011 := bstep (se 1 (by rfl) ⟨836258, by rfl⟩ : syracuseStep 1115011 = 1672517) B1672517
theorem B1115027 : Blo 1112627 1115027 := bstep (se 1 (by rfl) ⟨836270, by rfl⟩ : syracuseStep 1115027 = 1672541) B1672541
theorem B1672097 : Blo 1112627 1672097 := bstep (se 2 (by rfl) ⟨627036, by rfl⟩ : syracuseStep 1672097 = 1254073) B1254073
theorem B1115043 : Blo 1112627 1115043 := bstep (se 1 (by rfl) ⟨836282, by rfl⟩ : syracuseStep 1115043 = 1672565) B1672565
theorem B1672115 : Blo 1112627 1672115 := bstep (se 1 (by rfl) ⟨1254086, by rfl⟩ : syracuseStep 1672115 = 2508173) B2508173
theorem B1115059 : Blo 1112627 1115059 := bstep (se 1 (by rfl) ⟨836294, by rfl⟩ : syracuseStep 1115059 = 1672589) B1672589
theorem B1409987 : Blo 1112627 1409987 := bstep (se 1 (by rfl) ⟨1057490, by rfl⟩ : syracuseStep 1409987 = 2114981) B2114981
theorem B1115075 : Blo 1112627 1115075 := bstep (se 1 (by rfl) ⟨836306, by rfl⟩ : syracuseStep 1115075 = 1672613) B1672613
theorem B1672145 : Blo 1112627 1672145 := bstep (se 2 (by rfl) ⟨627054, by rfl⟩ : syracuseStep 1672145 = 1254109) B1254109
theorem B1115091 : Blo 1112627 1115091 := bstep (se 1 (by rfl) ⟨836318, by rfl⟩ : syracuseStep 1115091 = 1672637) B1672637
theorem B1672163 : Blo 1112627 1672163 := bstep (se 1 (by rfl) ⟨1254122, by rfl⟩ : syracuseStep 1672163 = 2508245) B2508245
theorem B1115107 : Blo 1112627 1115107 := bstep (se 1 (by rfl) ⟨836330, by rfl⟩ : syracuseStep 1115107 = 1672661) B1672661
theorem B1115123 : Blo 1112627 1115123 := bstep (se 1 (by rfl) ⟨836342, by rfl⟩ : syracuseStep 1115123 = 1672685) B1672685
theorem B1672193 : Blo 1112627 1672193 := bstep (se 2 (by rfl) ⟨627072, by rfl⟩ : syracuseStep 1672193 = 1254145) B1254145
theorem B1115139 : Blo 1112627 1115139 := bstep (se 1 (by rfl) ⟨836354, by rfl⟩ : syracuseStep 1115139 = 1672709) B1672709
theorem B4228109 : Blo 1112627 4228109 := bstep (se 3 (by rfl) ⟨792770, by rfl⟩ : syracuseStep 4228109 = 1585541) B1585541
theorem B1672211 : Blo 1112627 1672211 := bstep (se 1 (by rfl) ⟨1254158, by rfl⟩ : syracuseStep 1672211 = 2508317) B2508317
theorem B1115155 : Blo 1112627 1115155 := bstep (se 1 (by rfl) ⟨836366, by rfl⟩ : syracuseStep 1115155 = 1672733) B1672733
theorem B1115171 : Blo 1112627 1115171 := bstep (se 1 (by rfl) ⟨836378, by rfl⟩ : syracuseStep 1115171 = 1672757) B1672757
theorem B1672241 : Blo 1112627 1672241 := bstep (se 2 (by rfl) ⟨627090, by rfl⟩ : syracuseStep 1672241 = 1254181) B1254181
theorem B1115187 : Blo 1112627 1115187 := bstep (se 1 (by rfl) ⟨836390, by rfl⟩ : syracuseStep 1115187 = 1672781) B1672781
theorem B1672259 : Blo 1112627 1672259 := bstep (se 1 (by rfl) ⟨1254194, by rfl⟩ : syracuseStep 1672259 = 2508389) B2508389
theorem B1115203 : Blo 1112627 1115203 := bstep (se 1 (by rfl) ⟨836402, by rfl⟩ : syracuseStep 1115203 = 1672805) B1672805
theorem B1115219 : Blo 1112627 1115219 := bstep (se 1 (by rfl) ⟨836414, by rfl⟩ : syracuseStep 1115219 = 1672829) B1672829
theorem B1672289 : Blo 1112627 1672289 := bstep (se 2 (by rfl) ⟨627108, by rfl⟩ : syracuseStep 1672289 = 1254217) B1254217
theorem B1115235 : Blo 1112627 1115235 := bstep (se 1 (by rfl) ⟨836426, by rfl⟩ : syracuseStep 1115235 = 1672853) B1672853
theorem B1672307 : Blo 1112627 1672307 := bstep (se 1 (by rfl) ⟨1254230, by rfl⟩ : syracuseStep 1672307 = 2508461) B2508461
theorem B1115251 : Blo 1112627 1115251 := bstep (se 1 (by rfl) ⟨836438, by rfl⟩ : syracuseStep 1115251 = 1672877) B1672877
theorem B1115267 : Blo 1112627 1115267 := bstep (se 1 (by rfl) ⟨836450, by rfl⟩ : syracuseStep 1115267 = 1672901) B1672901
theorem B1672337 : Blo 1112627 1672337 := bstep (se 2 (by rfl) ⟨627126, by rfl⟩ : syracuseStep 1672337 = 1254253) B1254253
theorem B1115283 : Blo 1112627 1115283 := bstep (se 1 (by rfl) ⟨836462, by rfl⟩ : syracuseStep 1115283 = 1672925) B1672925
theorem B1672355 : Blo 1112627 1672355 := bstep (se 1 (by rfl) ⟨1254266, by rfl⟩ : syracuseStep 1672355 = 2508533) B2508533
theorem B1115299 : Blo 1112627 1115299 := bstep (se 1 (by rfl) ⟨836474, by rfl⟩ : syracuseStep 1115299 = 1672949) B1672949
theorem B1115315 : Blo 1112627 1115315 := bstep (se 1 (by rfl) ⟨836486, by rfl⟩ : syracuseStep 1115315 = 1672973) B1672973
theorem B1672385 : Blo 1112627 1672385 := bstep (se 2 (by rfl) ⟨627144, by rfl⟩ : syracuseStep 1672385 = 1254289) B1254289
theorem B1115331 : Blo 1112627 1115331 := bstep (se 1 (by rfl) ⟨836498, by rfl⟩ : syracuseStep 1115331 = 1672997) B1672997
theorem B1672403 : Blo 1112627 1672403 := bstep (se 1 (by rfl) ⟨1254302, by rfl⟩ : syracuseStep 1672403 = 2508605) B2508605
theorem B1115347 : Blo 1112627 1115347 := bstep (se 1 (by rfl) ⟨836510, by rfl⟩ : syracuseStep 1115347 = 1673021) B1673021
theorem B1115363 : Blo 1112627 1115363 := bstep (se 1 (by rfl) ⟨836522, by rfl⟩ : syracuseStep 1115363 = 1673045) B1673045
theorem B1672433 : Blo 1112627 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B1115379 : Blo 1112627 1115379 := bstep (se 1 (by rfl) ⟨836534, by rfl⟩ : syracuseStep 1115379 = 1673069) B1673069
theorem B1672451 : Blo 1112627 1672451 := bstep (se 1 (by rfl) ⟨1254338, by rfl⟩ : syracuseStep 1672451 = 2508677) B2508677
theorem B1115395 : Blo 1112627 1115395 := bstep (se 1 (by rfl) ⟨836546, by rfl⟩ : syracuseStep 1115395 = 1673093) B1673093
theorem B1115411 : Blo 1112627 1115411 := bstep (se 1 (by rfl) ⟨836558, by rfl⟩ : syracuseStep 1115411 = 1673117) B1673117
theorem B1672481 : Blo 1112627 1672481 := bstep (se 2 (by rfl) ⟨627180, by rfl⟩ : syracuseStep 1672481 = 1254361) B1254361
theorem B1115427 : Blo 1112627 1115427 := bstep (se 1 (by rfl) ⟨836570, by rfl⟩ : syracuseStep 1115427 = 1673141) B1673141
theorem B1672499 : Blo 1112627 1672499 := bstep (se 1 (by rfl) ⟨1254374, by rfl⟩ : syracuseStep 1672499 = 2508749) B2508749
theorem B1115443 : Blo 1112627 1115443 := bstep (se 1 (by rfl) ⟨836582, by rfl⟩ : syracuseStep 1115443 = 1673165) B1673165
theorem B1115459 : Blo 1112627 1115459 := bstep (se 1 (by rfl) ⟨836594, by rfl⟩ : syracuseStep 1115459 = 1673189) B1673189
theorem B1672529 : Blo 1112627 1672529 := bstep (se 2 (by rfl) ⟨627198, by rfl⟩ : syracuseStep 1672529 = 1254397) B1254397
theorem B1115475 : Blo 1112627 1115475 := bstep (se 1 (by rfl) ⟨836606, by rfl⟩ : syracuseStep 1115475 = 1673213) B1673213
theorem B1672547 : Blo 1112627 1672547 := bstep (se 1 (by rfl) ⟨1254410, by rfl⟩ : syracuseStep 1672547 = 2508821) B2508821
theorem B1115491 : Blo 1112627 1115491 := bstep (se 1 (by rfl) ⟨836618, by rfl⟩ : syracuseStep 1115491 = 1673237) B1673237
theorem B1115507 : Blo 1112627 1115507 := bstep (se 1 (by rfl) ⟨836630, by rfl⟩ : syracuseStep 1115507 = 1673261) B1673261
theorem B1672577 : Blo 1112627 1672577 := bstep (se 2 (by rfl) ⟨627216, by rfl⟩ : syracuseStep 1672577 = 1254433) B1254433
theorem B1115523 : Blo 1112627 1115523 := bstep (se 1 (by rfl) ⟨836642, by rfl⟩ : syracuseStep 1115523 = 1673285) B1673285
theorem B1672595 : Blo 1112627 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B1115539 : Blo 1112627 1115539 := bstep (se 1 (by rfl) ⟨836654, by rfl⟩ : syracuseStep 1115539 = 1673309) B1673309
theorem B1115555 : Blo 1112627 1115555 := bstep (se 1 (by rfl) ⟨836666, by rfl⟩ : syracuseStep 1115555 = 1673333) B1673333
theorem B1672625 : Blo 1112627 1672625 := bstep (se 2 (by rfl) ⟨627234, by rfl⟩ : syracuseStep 1672625 = 1254469) B1254469
theorem B1115571 : Blo 1112627 1115571 := bstep (se 1 (by rfl) ⟨836678, by rfl⟩ : syracuseStep 1115571 = 1673357) B1673357
theorem B1672643 : Blo 1112627 1672643 := bstep (se 1 (by rfl) ⟨1254482, by rfl⟩ : syracuseStep 1672643 = 2508965) B2508965
theorem B1115587 : Blo 1112627 1115587 := bstep (se 1 (by rfl) ⟨836690, by rfl⟩ : syracuseStep 1115587 = 1673381) B1673381
theorem B1115603 : Blo 1112627 1115603 := bstep (se 1 (by rfl) ⟨836702, by rfl⟩ : syracuseStep 1115603 = 1673405) B1673405
theorem B1672673 : Blo 1112627 1672673 := bstep (se 2 (by rfl) ⟨627252, by rfl⟩ : syracuseStep 1672673 = 1254505) B1254505
theorem B1115619 : Blo 1112627 1115619 := bstep (se 1 (by rfl) ⟨836714, by rfl⟩ : syracuseStep 1115619 = 1673429) B1673429
theorem B6358499 : Blo 1112627 6358499 := bstep (se 1 (by rfl) ⟨4768874, by rfl⟩ : syracuseStep 6358499 = 9537749) B9537749
theorem B2819569 : Blo 1112627 2819569 := bstep (se 2 (by rfl) ⟨1057338, by rfl⟩ : syracuseStep 2819569 = 2114677) B2114677
theorem B1115635 : Blo 1112627 1115635 := bstep (se 1 (by rfl) ⟨836726, by rfl⟩ : syracuseStep 1115635 = 1673453) B1673453
theorem B1672691 : Blo 1112627 1672691 := bstep (se 1 (by rfl) ⟨1254518, by rfl⟩ : syracuseStep 1672691 = 2509037) B2509037
theorem B1115651 : Blo 1112627 1115651 := bstep (se 1 (by rfl) ⟨836738, by rfl⟩ : syracuseStep 1115651 = 1673477) B1673477
theorem B1672721 : Blo 1112627 1672721 := bstep (se 2 (by rfl) ⟨627270, by rfl⟩ : syracuseStep 1672721 = 1254541) B1254541
theorem B1115667 : Blo 1112627 1115667 := bstep (se 1 (by rfl) ⟨836750, by rfl⟩ : syracuseStep 1115667 = 1673501) B1673501
theorem B1672739 : Blo 1112627 1672739 := bstep (se 1 (by rfl) ⟨1254554, by rfl⟩ : syracuseStep 1672739 = 2509109) B2509109
theorem B1115683 : Blo 1112627 1115683 := bstep (se 1 (by rfl) ⟨836762, by rfl⟩ : syracuseStep 1115683 = 1673525) B1673525
theorem B1115699 : Blo 1112627 1115699 := bstep (se 1 (by rfl) ⟨836774, by rfl⟩ : syracuseStep 1115699 = 1673549) B1673549
theorem B15238709 : Blo 1112627 15238709 := bstep (se 5 (by rfl) ⟨714314, by rfl⟩ : syracuseStep 15238709 = 1428629) B1428629
theorem B1672769 : Blo 1112627 1672769 := bstep (se 2 (by rfl) ⟨627288, by rfl⟩ : syracuseStep 1672769 = 1254577) B1254577
theorem B1115715 : Blo 1112627 1115715 := bstep (se 1 (by rfl) ⟨836786, by rfl⟩ : syracuseStep 1115715 = 1673573) B1673573
theorem B1672787 : Blo 1112627 1672787 := bstep (se 1 (by rfl) ⟨1254590, by rfl⟩ : syracuseStep 1672787 = 2509181) B2509181
theorem B1115731 : Blo 1112627 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B1115747 : Blo 1112627 1115747 := bstep (se 1 (by rfl) ⟨836810, by rfl⟩ : syracuseStep 1115747 = 1673621) B1673621
theorem B1672817 : Blo 1112627 1672817 := bstep (se 2 (by rfl) ⟨627306, by rfl⟩ : syracuseStep 1672817 = 1254613) B1254613
theorem B1115763 : Blo 1112627 1115763 := bstep (se 1 (by rfl) ⟨836822, by rfl⟩ : syracuseStep 1115763 = 1673645) B1673645
theorem B1410691 : Blo 1112627 1410691 := bstep (se 1 (by rfl) ⟨1058018, by rfl⟩ : syracuseStep 1410691 = 2116037) B2116037
theorem B1672835 : Blo 1112627 1672835 := bstep (se 1 (by rfl) ⟨1254626, by rfl⟩ : syracuseStep 1672835 = 2509253) B2509253
theorem B1115779 : Blo 1112627 1115779 := bstep (se 1 (by rfl) ⟨836834, by rfl⟩ : syracuseStep 1115779 = 1673669) B1673669
theorem B1115795 : Blo 1112627 1115795 := bstep (se 1 (by rfl) ⟨836846, by rfl⟩ : syracuseStep 1115795 = 1673693) B1673693
theorem B1672865 : Blo 1112627 1672865 := bstep (se 2 (by rfl) ⟨627324, by rfl⟩ : syracuseStep 1672865 = 1254649) B1254649
theorem B1115811 : Blo 1112627 1115811 := bstep (se 1 (by rfl) ⟨836858, by rfl⟩ : syracuseStep 1115811 = 1673717) B1673717
theorem B1672883 : Blo 1112627 1672883 := bstep (se 1 (by rfl) ⟨1254662, by rfl⟩ : syracuseStep 1672883 = 2509325) B2509325
theorem B1115827 : Blo 1112627 1115827 := bstep (se 1 (by rfl) ⟨836870, by rfl⟩ : syracuseStep 1115827 = 1673741) B1673741
theorem B1115843 : Blo 1112627 1115843 := bstep (se 1 (by rfl) ⟨836882, by rfl⟩ : syracuseStep 1115843 = 1673765) B1673765
theorem B1672913 : Blo 1112627 1672913 := bstep (se 2 (by rfl) ⟨627342, by rfl⟩ : syracuseStep 1672913 = 1254685) B1254685
theorem B1115859 : Blo 1112627 1115859 := bstep (se 1 (by rfl) ⟨836894, by rfl⟩ : syracuseStep 1115859 = 1673789) B1673789
theorem B1410787 : Blo 1112627 1410787 := bstep (se 1 (by rfl) ⟨1058090, by rfl⟩ : syracuseStep 1410787 = 2116181) B2116181
theorem B1672931 : Blo 1112627 1672931 := bstep (se 1 (by rfl) ⟨1254698, by rfl⟩ : syracuseStep 1672931 = 2509397) B2509397
theorem B1115875 : Blo 1112627 1115875 := bstep (se 1 (by rfl) ⟨836906, by rfl⟩ : syracuseStep 1115875 = 1673813) B1673813
theorem B1115891 : Blo 1112627 1115891 := bstep (se 1 (by rfl) ⟨836918, by rfl⟩ : syracuseStep 1115891 = 1673837) B1673837
theorem B1672961 : Blo 1112627 1672961 := bstep (se 2 (by rfl) ⟨627360, by rfl⟩ : syracuseStep 1672961 = 1254721) B1254721
theorem B2819843 : Blo 1112627 2819843 := bstep (se 1 (by rfl) ⟨2114882, by rfl⟩ : syracuseStep 2819843 = 4229765) B4229765
theorem B1115907 : Blo 1112627 1115907 := bstep (se 1 (by rfl) ⟨836930, by rfl⟩ : syracuseStep 1115907 = 1673861) B1673861
theorem B3573517 : Blo 1112627 3573517 := bstep (se 3 (by rfl) ⟨670034, by rfl⟩ : syracuseStep 3573517 = 1340069) B1340069
theorem B1672979 : Blo 1112627 1672979 := bstep (se 1 (by rfl) ⟨1254734, by rfl⟩ : syracuseStep 1672979 = 2509469) B2509469
theorem B1115923 : Blo 1112627 1115923 := bstep (se 1 (by rfl) ⟨836942, by rfl⟩ : syracuseStep 1115923 = 1673885) B1673885
theorem B5637923 : Blo 1112627 5637923 := bstep (se 1 (by rfl) ⟨4228442, by rfl⟩ : syracuseStep 5637923 = 8456885) B8456885
theorem B1115939 : Blo 1112627 1115939 := bstep (se 1 (by rfl) ⟨836954, by rfl⟩ : syracuseStep 1115939 = 1673909) B1673909
theorem B1673009 : Blo 1112627 1673009 := bstep (se 2 (by rfl) ⟨627378, by rfl⟩ : syracuseStep 1673009 = 1254757) B1254757
theorem B1115955 : Blo 1112627 1115955 := bstep (se 1 (by rfl) ⟨836966, by rfl⟩ : syracuseStep 1115955 = 1673933) B1673933
theorem B1673027 : Blo 1112627 1673027 := bstep (se 1 (by rfl) ⟨1254770, by rfl⟩ : syracuseStep 1673027 = 2509541) B2509541
theorem B1115971 : Blo 1112627 1115971 := bstep (se 1 (by rfl) ⟨836978, by rfl⟩ : syracuseStep 1115971 = 1673957) B1673957
theorem B1115987 : Blo 1112627 1115987 := bstep (se 1 (by rfl) ⟨836990, by rfl⟩ : syracuseStep 1115987 = 1673981) B1673981
theorem B1673057 : Blo 1112627 1673057 := bstep (se 2 (by rfl) ⟨627396, by rfl⟩ : syracuseStep 1673057 = 1254793) B1254793
theorem B1116003 : Blo 1112627 1116003 := bstep (se 1 (by rfl) ⟨837002, by rfl⟩ : syracuseStep 1116003 = 1674005) B1674005
theorem B1673075 : Blo 1112627 1673075 := bstep (se 1 (by rfl) ⟨1254806, by rfl⟩ : syracuseStep 1673075 = 2509613) B2509613
theorem B1116019 : Blo 1112627 1116019 := bstep (se 1 (by rfl) ⟨837014, by rfl⟩ : syracuseStep 1116019 = 1674029) B1674029
theorem B1116035 : Blo 1112627 1116035 := bstep (se 1 (by rfl) ⟨837026, by rfl⟩ : syracuseStep 1116035 = 1674053) B1674053
theorem B1673105 : Blo 1112627 1673105 := bstep (se 2 (by rfl) ⟨627414, by rfl⟩ : syracuseStep 1673105 = 1254829) B1254829
theorem B1116051 : Blo 1112627 1116051 := bstep (se 1 (by rfl) ⟨837038, by rfl⟩ : syracuseStep 1116051 = 1674077) B1674077
theorem B1673123 : Blo 1112627 1673123 := bstep (se 1 (by rfl) ⟨1254842, by rfl⟩ : syracuseStep 1673123 = 2509685) B2509685
theorem B1116067 : Blo 1112627 1116067 := bstep (se 1 (by rfl) ⟨837050, by rfl⟩ : syracuseStep 1116067 = 1674101) B1674101
theorem B1116083 : Blo 1112627 1116083 := bstep (se 1 (by rfl) ⟨837062, by rfl⟩ : syracuseStep 1116083 = 1674125) B1674125
theorem B1673153 : Blo 1112627 1673153 := bstep (se 2 (by rfl) ⟨627432, by rfl⟩ : syracuseStep 1673153 = 1254865) B1254865
theorem B2820035 : Blo 1112627 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B1116099 : Blo 1112627 1116099 := bstep (se 1 (by rfl) ⟨837074, by rfl⟩ : syracuseStep 1116099 = 1674149) B1674149
theorem B1673171 : Blo 1112627 1673171 := bstep (se 1 (by rfl) ⟨1254878, by rfl⟩ : syracuseStep 1673171 = 2509757) B2509757
theorem B1116115 : Blo 1112627 1116115 := bstep (se 1 (by rfl) ⟨837086, by rfl⟩ : syracuseStep 1116115 = 1674173) B1674173
theorem B1116131 : Blo 1112627 1116131 := bstep (se 1 (by rfl) ⟨837098, by rfl⟩ : syracuseStep 1116131 = 1674197) B1674197
theorem B15239153 : Blo 1112627 15239153 := bstep (se 2 (by rfl) ⟨5714682, by rfl⟩ : syracuseStep 15239153 = 11429365) B11429365
theorem B1673201 : Blo 1112627 1673201 := bstep (se 2 (by rfl) ⟨627450, by rfl⟩ : syracuseStep 1673201 = 1254901) B1254901
theorem B1116147 : Blo 1112627 1116147 := bstep (se 1 (by rfl) ⟨837110, by rfl⟩ : syracuseStep 1116147 = 1674221) B1674221
theorem B1673219 : Blo 1112627 1673219 := bstep (se 1 (by rfl) ⟨1254914, by rfl⟩ : syracuseStep 1673219 = 2509829) B2509829
theorem B1116163 : Blo 1112627 1116163 := bstep (se 1 (by rfl) ⟨837122, by rfl⟩ : syracuseStep 1116163 = 1674245) B1674245
theorem B1116179 : Blo 1112627 1116179 := bstep (se 1 (by rfl) ⟨837134, by rfl⟩ : syracuseStep 1116179 = 1674269) B1674269
theorem B1673249 : Blo 1112627 1673249 := bstep (se 2 (by rfl) ⟨627468, by rfl⟩ : syracuseStep 1673249 = 1254937) B1254937
theorem B1116195 : Blo 1112627 1116195 := bstep (se 1 (by rfl) ⟨837146, by rfl⟩ : syracuseStep 1116195 = 1674293) B1674293
theorem B1673267 : Blo 1112627 1673267 := bstep (se 1 (by rfl) ⟨1254950, by rfl⟩ : syracuseStep 1673267 = 2509901) B2509901
theorem B1116211 : Blo 1112627 1116211 := bstep (se 1 (by rfl) ⟨837158, by rfl⟩ : syracuseStep 1116211 = 1674317) B1674317
theorem B1116227 : Blo 1112627 1116227 := bstep (se 1 (by rfl) ⟨837170, by rfl⟩ : syracuseStep 1116227 = 1674341) B1674341
theorem B1673297 : Blo 1112627 1673297 := bstep (se 2 (by rfl) ⟨627486, by rfl⟩ : syracuseStep 1673297 = 1254973) B1254973
theorem B1116243 : Blo 1112627 1116243 := bstep (se 1 (by rfl) ⟨837182, by rfl⟩ : syracuseStep 1116243 = 1674365) B1674365
theorem B1673315 : Blo 1112627 1673315 := bstep (se 1 (by rfl) ⟨1254986, by rfl⟩ : syracuseStep 1673315 = 2509973) B2509973
theorem B1116259 : Blo 1112627 1116259 := bstep (se 1 (by rfl) ⟨837194, by rfl⟩ : syracuseStep 1116259 = 1674389) B1674389
theorem B18057329 : Blo 1112627 18057329 := bstep (se 2 (by rfl) ⟨6771498, by rfl⟩ : syracuseStep 18057329 = 13542997) B13542997
theorem B1116275 : Blo 1112627 1116275 := bstep (se 1 (by rfl) ⟨837206, by rfl⟩ : syracuseStep 1116275 = 1674413) B1674413
theorem B1673345 : Blo 1112627 1673345 := bstep (se 2 (by rfl) ⟨627504, by rfl⟩ : syracuseStep 1673345 = 1255009) B1255009
theorem B1116291 : Blo 1112627 1116291 := bstep (se 1 (by rfl) ⟨837218, by rfl⟩ : syracuseStep 1116291 = 1674437) B1674437
theorem B1673363 : Blo 1112627 1673363 := bstep (se 1 (by rfl) ⟨1255022, by rfl⟩ : syracuseStep 1673363 = 2510045) B2510045
theorem B1116307 : Blo 1112627 1116307 := bstep (se 1 (by rfl) ⟨837230, by rfl⟩ : syracuseStep 1116307 = 1674461) B1674461
theorem B1116323 : Blo 1112627 1116323 := bstep (se 1 (by rfl) ⟨837242, by rfl⟩ : syracuseStep 1116323 = 1674485) B1674485
theorem B1673393 : Blo 1112627 1673393 := bstep (se 2 (by rfl) ⟨627522, by rfl⟩ : syracuseStep 1673393 = 1255045) B1255045
theorem B1116339 : Blo 1112627 1116339 := bstep (se 1 (by rfl) ⟨837254, by rfl⟩ : syracuseStep 1116339 = 1674509) B1674509
theorem B1673411 : Blo 1112627 1673411 := bstep (se 1 (by rfl) ⟨1255058, by rfl⟩ : syracuseStep 1673411 = 2510117) B2510117
theorem B1116355 : Blo 1112627 1116355 := bstep (se 1 (by rfl) ⟨837266, by rfl⟩ : syracuseStep 1116355 = 1674533) B1674533
theorem B1411283 : Blo 1112627 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B1116371 : Blo 1112627 1116371 := bstep (se 1 (by rfl) ⟨837278, by rfl⟩ : syracuseStep 1116371 = 1674557) B1674557
theorem B1673441 : Blo 1112627 1673441 := bstep (se 2 (by rfl) ⟨627540, by rfl⟩ : syracuseStep 1673441 = 1255081) B1255081
theorem B1116387 : Blo 1112627 1116387 := bstep (se 1 (by rfl) ⟨837290, by rfl⟩ : syracuseStep 1116387 = 1674581) B1674581
theorem B1673459 : Blo 1112627 1673459 := bstep (se 1 (by rfl) ⟨1255094, by rfl⟩ : syracuseStep 1673459 = 2510189) B2510189
theorem B1116403 : Blo 1112627 1116403 := bstep (se 1 (by rfl) ⟨837302, by rfl⟩ : syracuseStep 1116403 = 1674605) B1674605
theorem B1116419 : Blo 1112627 1116419 := bstep (se 1 (by rfl) ⟨837314, by rfl⟩ : syracuseStep 1116419 = 1674629) B1674629
theorem B1673489 : Blo 1112627 1673489 := bstep (se 2 (by rfl) ⟨627558, by rfl⟩ : syracuseStep 1673489 = 1255117) B1255117
theorem B1116435 : Blo 1112627 1116435 := bstep (se 1 (by rfl) ⟨837326, by rfl⟩ : syracuseStep 1116435 = 1674653) B1674653
theorem B1673507 : Blo 1112627 1673507 := bstep (se 1 (by rfl) ⟨1255130, by rfl⟩ : syracuseStep 1673507 = 2510261) B2510261
theorem B1116451 : Blo 1112627 1116451 := bstep (se 1 (by rfl) ⟨837338, by rfl⟩ : syracuseStep 1116451 = 1674677) B1674677
theorem B1116467 : Blo 1112627 1116467 := bstep (se 1 (by rfl) ⟨837350, by rfl⟩ : syracuseStep 1116467 = 1674701) B1674701
theorem B1673537 : Blo 1112627 1673537 := bstep (se 2 (by rfl) ⟨627576, by rfl⟩ : syracuseStep 1673537 = 1255153) B1255153
theorem B3017027 : Blo 1112627 3017027 := bstep (se 1 (by rfl) ⟨2262770, by rfl⟩ : syracuseStep 3017027 = 4525541) B4525541
theorem B1116483 : Blo 1112627 1116483 := bstep (se 1 (by rfl) ⟨837362, by rfl⟩ : syracuseStep 1116483 = 1674725) B1674725
theorem B1673555 : Blo 1112627 1673555 := bstep (se 1 (by rfl) ⟨1255166, by rfl⟩ : syracuseStep 1673555 = 2510333) B2510333
theorem B1116499 : Blo 1112627 1116499 := bstep (se 1 (by rfl) ⟨837374, by rfl⟩ : syracuseStep 1116499 = 1674749) B1674749
theorem B1116515 : Blo 1112627 1116515 := bstep (se 1 (by rfl) ⟨837386, by rfl⟩ : syracuseStep 1116515 = 1674773) B1674773
theorem B1673585 : Blo 1112627 1673585 := bstep (se 2 (by rfl) ⟨627594, by rfl⟩ : syracuseStep 1673585 = 1255189) B1255189
theorem B1116531 : Blo 1112627 1116531 := bstep (se 1 (by rfl) ⟨837398, by rfl⟩ : syracuseStep 1116531 = 1674797) B1674797
theorem B1673603 : Blo 1112627 1673603 := bstep (se 1 (by rfl) ⟨1255202, by rfl⟩ : syracuseStep 1673603 = 2510405) B2510405
theorem B1116547 : Blo 1112627 1116547 := bstep (se 1 (by rfl) ⟨837410, by rfl⟩ : syracuseStep 1116547 = 1674821) B1674821
theorem B4065677 : Blo 1112627 4065677 := bstep (se 3 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 4065677 = 1524629) B1524629
theorem B1116563 : Blo 1112627 1116563 := bstep (se 1 (by rfl) ⟨837422, by rfl⟩ : syracuseStep 1116563 = 1674845) B1674845
theorem B1673633 : Blo 1112627 1673633 := bstep (se 2 (by rfl) ⟨627612, by rfl⟩ : syracuseStep 1673633 = 1255225) B1255225
theorem B1116579 : Blo 1112627 1116579 := bstep (se 1 (by rfl) ⟨837434, by rfl⟩ : syracuseStep 1116579 = 1674869) B1674869
theorem B1673651 : Blo 1112627 1673651 := bstep (se 1 (by rfl) ⟨1255238, by rfl⟩ : syracuseStep 1673651 = 2510477) B2510477
theorem B1116595 : Blo 1112627 1116595 := bstep (se 1 (by rfl) ⟨837446, by rfl⟩ : syracuseStep 1116595 = 1674893) B1674893
theorem B1116611 : Blo 1112627 1116611 := bstep (se 1 (by rfl) ⟨837458, by rfl⟩ : syracuseStep 1116611 = 1674917) B1674917
theorem B1673681 : Blo 1112627 1673681 := bstep (se 2 (by rfl) ⟨627630, by rfl⟩ : syracuseStep 1673681 = 1255261) B1255261
theorem B1116627 : Blo 1112627 1116627 := bstep (se 1 (by rfl) ⟨837470, by rfl⟩ : syracuseStep 1116627 = 1674941) B1674941
theorem B10717667 : Blo 1112627 10717667 := bstep (se 1 (by rfl) ⟨8038250, by rfl⟩ : syracuseStep 10717667 = 16076501) B16076501
theorem B1673699 : Blo 1112627 1673699 := bstep (se 1 (by rfl) ⟨1255274, by rfl⟩ : syracuseStep 1673699 = 2510549) B2510549
theorem B4524515 : Blo 1112627 4524515 := bstep (se 1 (by rfl) ⟨3393386, by rfl⟩ : syracuseStep 4524515 = 6786773) B6786773
theorem B1673729 : Blo 1112627 1673729 := bstep (se 2 (by rfl) ⟨627648, by rfl⟩ : syracuseStep 1673729 = 1255297) B1255297
theorem B1673747 : Blo 1112627 1673747 := bstep (se 1 (by rfl) ⟨1255310, by rfl⟩ : syracuseStep 1673747 = 2510621) B2510621
theorem B1673777 : Blo 1112627 1673777 := bstep (se 2 (by rfl) ⟨627666, by rfl⟩ : syracuseStep 1673777 = 1255333) B1255333
theorem B1673795 : Blo 1112627 1673795 := bstep (se 1 (by rfl) ⟨1255346, by rfl⟩ : syracuseStep 1673795 = 2510693) B2510693
theorem B5638733 : Blo 1112627 5638733 := bstep (se 3 (by rfl) ⟨1057262, by rfl⟩ : syracuseStep 5638733 = 2114525) B2114525
theorem B1673825 : Blo 1112627 1673825 := bstep (se 2 (by rfl) ⟨627684, by rfl⟩ : syracuseStep 1673825 = 1255369) B1255369
theorem B1673843 : Blo 1112627 1673843 := bstep (se 1 (by rfl) ⟨1255382, by rfl⟩ : syracuseStep 1673843 = 2510765) B2510765
theorem B1673873 : Blo 1112627 1673873 := bstep (se 2 (by rfl) ⟨627702, by rfl⟩ : syracuseStep 1673873 = 1255405) B1255405
theorem B1903267 : Blo 1112627 1903267 := bstep (se 1 (by rfl) ⟨1427450, by rfl⟩ : syracuseStep 1903267 = 2854901) B2854901
theorem B1673891 : Blo 1112627 1673891 := bstep (se 1 (by rfl) ⟨1255418, by rfl⟩ : syracuseStep 1673891 = 2510837) B2510837
theorem B1673921 : Blo 1112627 1673921 := bstep (se 2 (by rfl) ⟨627720, by rfl⟩ : syracuseStep 1673921 = 1255441) B1255441
theorem B1673939 : Blo 1112627 1673939 := bstep (se 1 (by rfl) ⟨1255454, by rfl⟩ : syracuseStep 1673939 = 2510909) B2510909
theorem B1673969 : Blo 1112627 1673969 := bstep (se 2 (by rfl) ⟨627738, by rfl⟩ : syracuseStep 1673969 = 1255477) B1255477
theorem B1673987 : Blo 1112627 1673987 := bstep (se 1 (by rfl) ⟨1255490, by rfl⟩ : syracuseStep 1673987 = 2510981) B2510981
theorem B1674017 : Blo 1112627 1674017 := bstep (se 2 (by rfl) ⟨627756, by rfl⟩ : syracuseStep 1674017 = 1255513) B1255513
theorem B1674035 : Blo 1112627 1674035 := bstep (se 1 (by rfl) ⟨1255526, by rfl⟩ : syracuseStep 1674035 = 2511053) B2511053
theorem B1674065 : Blo 1112627 1674065 := bstep (se 2 (by rfl) ⟨627774, by rfl⟩ : syracuseStep 1674065 = 1255549) B1255549
theorem B1674083 : Blo 1112627 1674083 := bstep (se 1 (by rfl) ⟨1255562, by rfl⟩ : syracuseStep 1674083 = 2511125) B2511125
theorem B2820977 : Blo 1112627 2820977 := bstep (se 2 (by rfl) ⟨1057866, by rfl⟩ : syracuseStep 2820977 = 2115733) B2115733
theorem B1674113 : Blo 1112627 1674113 := bstep (se 2 (by rfl) ⟨627792, by rfl⟩ : syracuseStep 1674113 = 1255585) B1255585
theorem B1411987 : Blo 1112627 1411987 := bstep (se 1 (by rfl) ⟨1058990, by rfl⟩ : syracuseStep 1411987 = 2117981) B2117981
theorem B1674131 : Blo 1112627 1674131 := bstep (se 1 (by rfl) ⟨1255598, by rfl⟩ : syracuseStep 1674131 = 2511197) B2511197
theorem B2821027 : Blo 1112627 2821027 := bstep (se 1 (by rfl) ⟨2115770, by rfl⟩ : syracuseStep 2821027 = 4231541) B4231541
theorem B1674161 : Blo 1112627 1674161 := bstep (se 2 (by rfl) ⟨627810, by rfl⟩ : syracuseStep 1674161 = 1255621) B1255621
theorem B1674179 : Blo 1112627 1674179 := bstep (se 1 (by rfl) ⟨1255634, by rfl⟩ : syracuseStep 1674179 = 2511269) B2511269
theorem B1674209 : Blo 1112627 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B1412083 : Blo 1112627 1412083 := bstep (se 1 (by rfl) ⟨1059062, by rfl⟩ : syracuseStep 1412083 = 2118125) B2118125
theorem B1674227 : Blo 1112627 1674227 := bstep (se 1 (by rfl) ⟨1255670, by rfl⟩ : syracuseStep 1674227 = 2511341) B2511341
theorem B1674257 : Blo 1112627 1674257 := bstep (se 2 (by rfl) ⟨627846, by rfl⟩ : syracuseStep 1674257 = 1255693) B1255693
theorem B1674275 : Blo 1112627 1674275 := bstep (se 1 (by rfl) ⟨1255706, by rfl⟩ : syracuseStep 1674275 = 2511413) B2511413
theorem B2821169 : Blo 1112627 2821169 := bstep (se 2 (by rfl) ⟨1057938, by rfl⟩ : syracuseStep 2821169 = 2115877) B2115877
theorem B1674305 : Blo 1112627 1674305 := bstep (se 2 (by rfl) ⟨627864, by rfl⟩ : syracuseStep 1674305 = 1255729) B1255729
theorem B1674323 : Blo 1112627 1674323 := bstep (se 1 (by rfl) ⟨1255742, by rfl⟩ : syracuseStep 1674323 = 2511485) B2511485
theorem B1674353 : Blo 1112627 1674353 := bstep (se 2 (by rfl) ⟨627882, by rfl⟩ : syracuseStep 1674353 = 1255765) B1255765
theorem B1903745 : Blo 1112627 1903745 := bstep (se 2 (by rfl) ⟨713904, by rfl⟩ : syracuseStep 1903745 = 1427809) B1427809
theorem B1674371 : Blo 1112627 1674371 := bstep (se 1 (by rfl) ⟨1255778, by rfl⟩ : syracuseStep 1674371 = 2511557) B2511557
theorem B1674401 : Blo 1112627 1674401 := bstep (se 2 (by rfl) ⟨627900, by rfl⟩ : syracuseStep 1674401 = 1255801) B1255801
theorem B1674419 : Blo 1112627 1674419 := bstep (se 1 (by rfl) ⟨1255814, by rfl⟩ : syracuseStep 1674419 = 2511629) B2511629
theorem B1674449 : Blo 1112627 1674449 := bstep (se 2 (by rfl) ⟨627918, by rfl⟩ : syracuseStep 1674449 = 1255837) B1255837
theorem B4754659 : Blo 1112627 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B1674467 : Blo 1112627 1674467 := bstep (se 1 (by rfl) ⟨1255850, by rfl⟩ : syracuseStep 1674467 = 2511701) B2511701
theorem B1674497 : Blo 1112627 1674497 := bstep (se 2 (by rfl) ⟨627936, by rfl⟩ : syracuseStep 1674497 = 1255873) B1255873
theorem B1674515 : Blo 1112627 1674515 := bstep (se 1 (by rfl) ⟨1255886, by rfl⟩ : syracuseStep 1674515 = 2511773) B2511773
theorem B1674545 : Blo 1112627 1674545 := bstep (se 2 (by rfl) ⟨627954, by rfl⟩ : syracuseStep 1674545 = 1255909) B1255909
theorem B1674563 : Blo 1112627 1674563 := bstep (se 1 (by rfl) ⟨1255922, by rfl⟩ : syracuseStep 1674563 = 2511845) B2511845
theorem B1674593 : Blo 1112627 1674593 := bstep (se 2 (by rfl) ⟨627972, by rfl⟩ : syracuseStep 1674593 = 1255945) B1255945
theorem B1674611 : Blo 1112627 1674611 := bstep (se 1 (by rfl) ⟨1255958, by rfl⟩ : syracuseStep 1674611 = 2511917) B2511917
theorem B1674641 : Blo 1112627 1674641 := bstep (se 2 (by rfl) ⟨627990, by rfl⟩ : syracuseStep 1674641 = 1255981) B1255981
theorem B1674659 : Blo 1112627 1674659 := bstep (se 1 (by rfl) ⟨1255994, by rfl⟩ : syracuseStep 1674659 = 2511989) B2511989
theorem B3018161 : Blo 1112627 3018161 := bstep (se 2 (by rfl) ⟨1131810, by rfl⟩ : syracuseStep 3018161 = 2263621) B2263621
theorem B1674689 : Blo 1112627 1674689 := bstep (se 2 (by rfl) ⟨628008, by rfl⟩ : syracuseStep 1674689 = 1256017) B1256017
theorem B1674707 : Blo 1112627 1674707 := bstep (se 1 (by rfl) ⟨1256030, by rfl⟩ : syracuseStep 1674707 = 2512061) B2512061
theorem B1412579 : Blo 1112627 1412579 := bstep (se 1 (by rfl) ⟨1059434, by rfl⟩ : syracuseStep 1412579 = 2118869) B2118869
theorem B1674737 : Blo 1112627 1674737 := bstep (se 2 (by rfl) ⟨628026, by rfl⟩ : syracuseStep 1674737 = 1256053) B1256053
theorem B1674755 : Blo 1112627 1674755 := bstep (se 1 (by rfl) ⟨1256066, by rfl⟩ : syracuseStep 1674755 = 2512133) B2512133
theorem B1674785 : Blo 1112627 1674785 := bstep (se 2 (by rfl) ⟨628044, by rfl⟩ : syracuseStep 1674785 = 1256089) B1256089
theorem B4132387 : Blo 1112627 4132387 := bstep (se 1 (by rfl) ⟨3099290, by rfl⟩ : syracuseStep 4132387 = 6198581) B6198581
theorem B1674803 : Blo 1112627 1674803 := bstep (se 1 (by rfl) ⟨1256102, by rfl⟩ : syracuseStep 1674803 = 2512205) B2512205
theorem B1674833 : Blo 1112627 1674833 := bstep (se 2 (by rfl) ⟨628062, by rfl⟩ : syracuseStep 1674833 = 1256125) B1256125
theorem B1674851 : Blo 1112627 1674851 := bstep (se 1 (by rfl) ⟨1256138, by rfl⟩ : syracuseStep 1674851 = 2512277) B2512277
theorem B1674881 : Blo 1112627 1674881 := bstep (se 2 (by rfl) ⟨628080, by rfl⟩ : syracuseStep 1674881 = 1256161) B1256161
theorem B1674899 : Blo 1112627 1674899 := bstep (se 1 (by rfl) ⟨1256174, by rfl⟩ : syracuseStep 1674899 = 2512349) B2512349
theorem B1674929 : Blo 1112627 1674929 := bstep (se 2 (by rfl) ⟨628098, by rfl⟩ : syracuseStep 1674929 = 1256197) B1256197
theorem B1904401 : Blo 1112627 1904401 := bstep (se 2 (by rfl) ⟨714150, by rfl⟩ : syracuseStep 1904401 = 1428301) B1428301
theorem B4231025 : Blo 1112627 4231025 := bstep (se 2 (by rfl) ⟨1586634, by rfl⟩ : syracuseStep 4231025 = 3173269) B3173269
theorem B19075013 : Blo 1112627 19075013 := bstep (se 4 (by rfl) ⟨1788282, by rfl⟩ : syracuseStep 19075013 = 3576565) B3576565
theorem B6033379 : Blo 1112627 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B2822161 : Blo 1112627 2822161 := bstep (se 2 (by rfl) ⟨1058310, by rfl⟩ : syracuseStep 2822161 = 2116621) B2116621
theorem B1904675 : Blo 1112627 1904675 := bstep (se 1 (by rfl) ⟨1428506, by rfl⟩ : syracuseStep 1904675 = 2857013) B2857013
theorem B12718133 : Blo 1112627 12718133 := bstep (se 5 (by rfl) ⟨596162, by rfl⟩ : syracuseStep 12718133 = 1192325) B1192325
theorem B2822435 : Blo 1112627 2822435 := bstep (se 1 (by rfl) ⟨2116826, by rfl⟩ : syracuseStep 2822435 = 4233653) B4233653
theorem B2822627 : Blo 1112627 2822627 := bstep (se 1 (by rfl) ⟨2116970, by rfl⟩ : syracuseStep 2822627 = 4233941) B4233941
theorem B2036227 : Blo 1112627 2036227 := bstep (se 1 (by rfl) ⟨1527170, by rfl⟩ : syracuseStep 2036227 = 3054341) B3054341
theorem B12030605 : Blo 1112627 12030605 := bstep (se 3 (by rfl) ⟨2255738, by rfl⟩ : syracuseStep 12030605 = 4511477) B4511477
theorem B14291909 : Blo 1112627 14291909 := bstep (se 4 (by rfl) ⟨1339866, by rfl⟩ : syracuseStep 14291909 = 2679733) B2679733
theorem B3576899 : Blo 1112627 3576899 := bstep (se 1 (by rfl) ⟨2682674, by rfl⟩ : syracuseStep 3576899 = 5365349) B5365349
theorem B4756657 : Blo 1112627 4756657 := bstep (se 2 (by rfl) ⟨1783746, by rfl⟩ : syracuseStep 4756657 = 3567493) B3567493
theorem B4232483 : Blo 1112627 4232483 := bstep (se 1 (by rfl) ⟨3174362, by rfl⟩ : syracuseStep 4232483 = 6348725) B6348725
theorem B2823569 : Blo 1112627 2823569 := bstep (se 2 (by rfl) ⟨1058838, by rfl⟩ : syracuseStep 2823569 = 2117677) B2117677
theorem B5641649 : Blo 1112627 5641649 := bstep (se 2 (by rfl) ⟨2115618, by rfl⟩ : syracuseStep 5641649 = 4231237) B4231237
theorem B2823619 : Blo 1112627 2823619 := bstep (se 1 (by rfl) ⟨2117714, by rfl⟩ : syracuseStep 2823619 = 4235429) B4235429
theorem B2823761 : Blo 1112627 2823761 := bstep (se 2 (by rfl) ⟨1058910, by rfl⟩ : syracuseStep 2823761 = 2117821) B2117821
theorem B3806833 : Blo 1112627 3806833 := bstep (se 2 (by rfl) ⟨1427562, by rfl⟩ : syracuseStep 3806833 = 2855125) B2855125
theorem B10721393 : Blo 1112627 10721393 := bstep (se 2 (by rfl) ⟨4020522, by rfl⟩ : syracuseStep 10721393 = 8041045) B8041045
theorem B4233485 : Blo 1112627 4233485 := bstep (se 3 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 4233485 = 1587557) B1587557
theorem B1251715 : Blo 1112627 1251715 := bstep (se 1 (by rfl) ⟨938786, by rfl⟩ : syracuseStep 1251715 = 1877573) B1877573
theorem B16062947 : Blo 1112627 16062947 := bstep (se 1 (by rfl) ⟨12047210, by rfl⟩ : syracuseStep 16062947 = 24094421) B24094421
theorem B1251859 : Blo 1112627 1251859 := bstep (se 1 (by rfl) ⟨938894, by rfl⟩ : syracuseStep 1251859 = 1877789) B1877789
theorem B2824753 : Blo 1112627 2824753 := bstep (se 2 (by rfl) ⟨1059282, by rfl⟩ : syracuseStep 2824753 = 2118565) B2118565
theorem B1252003 : Blo 1112627 1252003 := bstep (se 1 (by rfl) ⟨939002, by rfl⟩ : syracuseStep 1252003 = 1878005) B1878005
theorem B1252147 : Blo 1112627 1252147 := bstep (se 1 (by rfl) ⟨939110, by rfl⟩ : syracuseStep 1252147 = 1878221) B1878221
theorem B2825027 : Blo 1112627 2825027 := bstep (se 1 (by rfl) ⟨2118770, by rfl⟩ : syracuseStep 2825027 = 4237541) B4237541
theorem B5643107 : Blo 1112627 5643107 := bstep (se 1 (by rfl) ⟨4232330, by rfl⟩ : syracuseStep 5643107 = 8464661) B8464661
theorem B1252291 : Blo 1112627 1252291 := bstep (se 1 (by rfl) ⟨939218, by rfl⟩ : syracuseStep 1252291 = 1878437) B1878437
theorem B15277027 : Blo 1112627 15277027 := bstep (se 1 (by rfl) ⟨11457770, by rfl⟩ : syracuseStep 15277027 = 22915541) B22915541
theorem B2825219 : Blo 1112627 2825219 := bstep (se 1 (by rfl) ⟨2118914, by rfl⟩ : syracuseStep 2825219 = 4237829) B4237829
theorem B1252435 : Blo 1112627 1252435 := bstep (se 1 (by rfl) ⟨939326, by rfl⟩ : syracuseStep 1252435 = 1878653) B1878653
theorem B1252579 : Blo 1112627 1252579 := bstep (se 1 (by rfl) ⟨939434, by rfl⟩ : syracuseStep 1252579 = 1878869) B1878869
theorem B5086577 : Blo 1112627 5086577 := bstep (se 2 (by rfl) ⟨1907466, by rfl⟩ : syracuseStep 5086577 = 3814933) B3814933
theorem B1252723 : Blo 1112627 1252723 := bstep (se 1 (by rfl) ⟨939542, by rfl⟩ : syracuseStep 1252723 = 1879085) B1879085
theorem B1252867 : Blo 1112627 1252867 := bstep (se 1 (by rfl) ⟨939650, by rfl⟩ : syracuseStep 1252867 = 1879301) B1879301
theorem B1908289 : Blo 1112627 1908289 := bstep (se 2 (by rfl) ⟨715608, by rfl⟩ : syracuseStep 1908289 = 1431217) B1431217
theorem B5643917 : Blo 1112627 5643917 := bstep (se 3 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 5643917 = 2116469) B2116469
theorem B1253011 : Blo 1112627 1253011 := bstep (se 1 (by rfl) ⟨939758, by rfl⟩ : syracuseStep 1253011 = 1879517) B1879517
theorem B1810163 : Blo 1112627 1810163 := bstep (se 1 (by rfl) ⟨1357622, by rfl⟩ : syracuseStep 1810163 = 2715245) B2715245
theorem B2039555 : Blo 1112627 2039555 := bstep (se 1 (by rfl) ⟨1529666, by rfl⟩ : syracuseStep 2039555 = 3059333) B3059333
theorem B1253155 : Blo 1112627 1253155 := bstep (se 1 (by rfl) ⟨939866, by rfl⟩ : syracuseStep 1253155 = 1879733) B1879733
theorem B5087053 : Blo 1112627 5087053 := bstep (se 3 (by rfl) ⟨953822, by rfl⟩ : syracuseStep 5087053 = 1907645) B1907645
theorem B1908611 : Blo 1112627 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B2826161 : Blo 1112627 2826161 := bstep (se 2 (by rfl) ⟨1059810, by rfl⟩ : syracuseStep 2826161 = 2119621) B2119621
theorem B1253299 : Blo 1112627 1253299 := bstep (se 1 (by rfl) ⟨939974, by rfl⟩ : syracuseStep 1253299 = 1879949) B1879949
theorem B2826211 : Blo 1112627 2826211 := bstep (se 1 (by rfl) ⟨2119658, by rfl⟩ : syracuseStep 2826211 = 4239317) B4239317
theorem B9052145 : Blo 1112627 9052145 := bstep (se 2 (by rfl) ⟨3394554, by rfl⟩ : syracuseStep 9052145 = 6789109) B6789109
theorem B1253443 : Blo 1112627 1253443 := bstep (se 1 (by rfl) ⟨940082, by rfl⟩ : syracuseStep 1253443 = 1880165) B1880165
theorem B5709923 : Blo 1112627 5709923 := bstep (se 1 (by rfl) ⟨4282442, by rfl⟩ : syracuseStep 5709923 = 8564885) B8564885
theorem B2826353 : Blo 1112627 2826353 := bstep (se 2 (by rfl) ⟨1059882, by rfl⟩ : syracuseStep 2826353 = 2119765) B2119765
theorem B1253587 : Blo 1112627 1253587 := bstep (se 1 (by rfl) ⟨940190, by rfl⟩ : syracuseStep 1253587 = 1880381) B1880381
theorem B4235597 : Blo 1112627 4235597 := bstep (se 3 (by rfl) ⟨794174, by rfl⟩ : syracuseStep 4235597 = 1588349) B1588349
theorem B1253731 : Blo 1112627 1253731 := bstep (se 1 (by rfl) ⟨940298, by rfl⟩ : syracuseStep 1253731 = 1880597) B1880597
theorem B1253875 : Blo 1112627 1253875 := bstep (se 1 (by rfl) ⟨940406, by rfl⟩ : syracuseStep 1253875 = 1880813) B1880813
theorem B10723853 : Blo 1112627 10723853 := bstep (se 3 (by rfl) ⟨2010722, by rfl⟩ : syracuseStep 10723853 = 4021445) B4021445
theorem B1810993 : Blo 1112627 1810993 := bstep (se 2 (by rfl) ⟨679122, by rfl⟩ : syracuseStep 1810993 = 1358245) B1358245
theorem B1254019 : Blo 1112627 1254019 := bstep (se 1 (by rfl) ⟨940514, by rfl⟩ : syracuseStep 1254019 = 1881029) B1881029
theorem B5710499 : Blo 1112627 5710499 := bstep (se 1 (by rfl) ⟨4282874, by rfl⟩ : syracuseStep 5710499 = 8565749) B8565749
theorem B1909507 : Blo 1112627 1909507 := bstep (se 1 (by rfl) ⟨1432130, by rfl⟩ : syracuseStep 1909507 = 2864261) B2864261
theorem B1254163 : Blo 1112627 1254163 := bstep (se 1 (by rfl) ⟨940622, by rfl⟩ : syracuseStep 1254163 = 1881245) B1881245
theorem B8463203 : Blo 1112627 8463203 := bstep (se 1 (by rfl) ⟨6347402, by rfl⟩ : syracuseStep 8463203 = 12694805) B12694805
theorem B1254307 : Blo 1112627 1254307 := bstep (se 1 (by rfl) ⟨940730, by rfl⟩ : syracuseStep 1254307 = 1881461) B1881461
theorem B9642979 : Blo 1112627 9642979 := bstep (se 1 (by rfl) ⟨7232234, by rfl⟩ : syracuseStep 9642979 = 14464469) B14464469
theorem B2008099 : Blo 1112627 2008099 := bstep (se 1 (by rfl) ⟨1506074, by rfl⟩ : syracuseStep 2008099 = 3012149) B3012149
theorem B1254451 : Blo 1112627 1254451 := bstep (se 1 (by rfl) ⟨940838, by rfl⟩ : syracuseStep 1254451 = 1881677) B1881677
theorem B4760689 : Blo 1112627 4760689 := bstep (se 2 (by rfl) ⟨1785258, by rfl⟩ : syracuseStep 4760689 = 3570517) B3570517
theorem B4236401 : Blo 1112627 4236401 := bstep (se 2 (by rfl) ⟨1588650, by rfl⟩ : syracuseStep 4236401 = 3177301) B3177301
theorem B1254595 : Blo 1112627 1254595 := bstep (se 1 (by rfl) ⟨940946, by rfl⟩ : syracuseStep 1254595 = 1881893) B1881893
theorem B1189075 : Blo 1112627 1189075 := bstep (se 1 (by rfl) ⟨891806, by rfl⟩ : syracuseStep 1189075 = 1783613) B1783613
theorem B1254739 : Blo 1112627 1254739 := bstep (se 1 (by rfl) ⟨941054, by rfl⟩ : syracuseStep 1254739 = 1882109) B1882109
theorem B1287635 : Blo 1112627 1287635 := bstep (se 1 (by rfl) ⟨965726, by rfl⟩ : syracuseStep 1287635 = 1931453) B1931453
theorem B2008547 : Blo 1112627 2008547 := bstep (se 1 (by rfl) ⟨1506410, by rfl⟩ : syracuseStep 2008547 = 3012821) B3012821
theorem B1254883 : Blo 1112627 1254883 := bstep (se 1 (by rfl) ⟨941162, by rfl⟩ : syracuseStep 1254883 = 1882325) B1882325
theorem B1255027 : Blo 1112627 1255027 := bstep (se 1 (by rfl) ⟨941270, by rfl⟩ : syracuseStep 1255027 = 1882541) B1882541
theorem B1189523 : Blo 1112627 1189523 := bstep (se 1 (by rfl) ⟨892142, by rfl⟩ : syracuseStep 1189523 = 1784285) B1784285
theorem B1877681 : Blo 1112627 1877681 := bstep (se 2 (by rfl) ⟨704130, by rfl⟩ : syracuseStep 1877681 = 1408261) B1408261
theorem B1255171 : Blo 1112627 1255171 := bstep (se 1 (by rfl) ⟨941378, by rfl⟩ : syracuseStep 1255171 = 1882757) B1882757
theorem B4237069 : Blo 1112627 4237069 := bstep (se 3 (by rfl) ⟨794450, by rfl⟩ : syracuseStep 4237069 = 1588901) B1588901
theorem B1877809 : Blo 1112627 1877809 := bstep (se 2 (by rfl) ⟨704178, by rfl⟩ : syracuseStep 1877809 = 1408357) B1408357
theorem B3385165 : Blo 1112627 3385165 := bstep (se 3 (by rfl) ⟨634718, by rfl⟩ : syracuseStep 3385165 = 1269437) B1269437
theorem B1877843 : Blo 1112627 1877843 := bstep (se 1 (by rfl) ⟨1408382, by rfl⟩ : syracuseStep 1877843 = 2816765) B2816765
theorem B7153541 : Blo 1112627 7153541 := bstep (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) B1341289
theorem B1255315 : Blo 1112627 1255315 := bstep (se 1 (by rfl) ⟨941486, by rfl⟩ : syracuseStep 1255315 = 1882973) B1882973
theorem B1877971 : Blo 1112627 1877971 := bstep (se 1 (by rfl) ⟨1408478, by rfl⟩ : syracuseStep 1877971 = 2816957) B2816957
theorem B1255459 : Blo 1112627 1255459 := bstep (se 1 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 1255459 = 1883189) B1883189
theorem B1878113 : Blo 1112627 1878113 := bstep (se 2 (by rfl) ⟨704292, by rfl⟩ : syracuseStep 1878113 = 1408585) B1408585
theorem B1255603 : Blo 1112627 1255603 := bstep (se 1 (by rfl) ⟨941702, by rfl⟩ : syracuseStep 1255603 = 1883405) B1883405
theorem B1878241 : Blo 1112627 1878241 := bstep (se 2 (by rfl) ⟨704340, by rfl⟩ : syracuseStep 1878241 = 1408681) B1408681
theorem B1878275 : Blo 1112627 1878275 := bstep (se 1 (by rfl) ⟨1408706, by rfl⟩ : syracuseStep 1878275 = 2817413) B2817413
theorem B1255747 : Blo 1112627 1255747 := bstep (se 1 (by rfl) ⟨941810, by rfl⟩ : syracuseStep 1255747 = 1883621) B1883621
theorem B1878403 : Blo 1112627 1878403 := bstep (se 1 (by rfl) ⟨1408802, by rfl⟩ : syracuseStep 1878403 = 2817605) B2817605
theorem B1255891 : Blo 1112627 1255891 := bstep (se 1 (by rfl) ⟨941918, by rfl⟩ : syracuseStep 1255891 = 1883837) B1883837
theorem B5646833 : Blo 1112627 5646833 := bstep (se 2 (by rfl) ⟨2117562, by rfl⟩ : syracuseStep 5646833 = 4235125) B4235125
theorem B1878545 : Blo 1112627 1878545 := bstep (se 2 (by rfl) ⟨704454, by rfl⟩ : syracuseStep 1878545 = 1408909) B1408909
theorem B4237859 : Blo 1112627 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B1256035 : Blo 1112627 1256035 := bstep (se 1 (by rfl) ⟨942026, by rfl⟩ : syracuseStep 1256035 = 1884053) B1884053
theorem B1288819 : Blo 1112627 1288819 := bstep (se 1 (by rfl) ⟨966614, by rfl⟩ : syracuseStep 1288819 = 1933229) B1933229
theorem B1878673 : Blo 1112627 1878673 := bstep (se 2 (by rfl) ⟨704502, by rfl⟩ : syracuseStep 1878673 = 1409005) B1409005
theorem B5712547 : Blo 1112627 5712547 := bstep (se 1 (by rfl) ⟨4284410, by rfl⟩ : syracuseStep 5712547 = 8568821) B8568821
theorem B1878707 : Blo 1112627 1878707 := bstep (se 1 (by rfl) ⟨1409030, by rfl⟩ : syracuseStep 1878707 = 2818061) B2818061
theorem B1256179 : Blo 1112627 1256179 := bstep (se 1 (by rfl) ⟨942134, by rfl⟩ : syracuseStep 1256179 = 1884269) B1884269
theorem B1878835 : Blo 1112627 1878835 := bstep (se 1 (by rfl) ⟨1409126, by rfl⟩ : syracuseStep 1878835 = 2818253) B2818253
theorem B1878977 : Blo 1112627 1878977 := bstep (se 2 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 1878977 = 1409233) B1409233
theorem B1190899 : Blo 1112627 1190899 := bstep (se 1 (by rfl) ⟨893174, by rfl⟩ : syracuseStep 1190899 = 1786349) B1786349
theorem B2010161 : Blo 1112627 2010161 := bstep (se 2 (by rfl) ⟨753810, by rfl⟩ : syracuseStep 2010161 = 1507621) B1507621
theorem B1879105 : Blo 1112627 1879105 := bstep (se 2 (by rfl) ⟨704664, by rfl⟩ : syracuseStep 1879105 = 1409329) B1409329
theorem B1879139 : Blo 1112627 1879139 := bstep (se 1 (by rfl) ⟨1409354, by rfl⟩ : syracuseStep 1879139 = 2818709) B2818709
theorem B4238513 : Blo 1112627 4238513 := bstep (se 2 (by rfl) ⟨1589442, by rfl⟩ : syracuseStep 4238513 = 3178885) B3178885
theorem B1879267 : Blo 1112627 1879267 := bstep (se 1 (by rfl) ⟨1409450, by rfl⟩ : syracuseStep 1879267 = 2818901) B2818901
theorem B1879409 : Blo 1112627 1879409 := bstep (se 2 (by rfl) ⟨704778, by rfl⟩ : syracuseStep 1879409 = 1409557) B1409557
theorem B1879537 : Blo 1112627 1879537 := bstep (se 2 (by rfl) ⟨704826, by rfl⟩ : syracuseStep 1879537 = 1409653) B1409653
theorem B1584641 : Blo 1112627 1584641 := bstep (se 2 (by rfl) ⟨594240, by rfl⟩ : syracuseStep 1584641 = 1188481) B1188481
theorem B1879571 : Blo 1112627 1879571 := bstep (se 1 (by rfl) ⟨1409678, by rfl⟩ : syracuseStep 1879571 = 2819357) B2819357
theorem B1584721 : Blo 1112627 1584721 := bstep (se 2 (by rfl) ⟨594270, by rfl⟩ : syracuseStep 1584721 = 1188541) B1188541
theorem B1879699 : Blo 1112627 1879699 := bstep (se 1 (by rfl) ⟨1409774, by rfl⟩ : syracuseStep 1879699 = 2819549) B2819549
theorem B1355459 : Blo 1112627 1355459 := bstep (se 1 (by rfl) ⟨1016594, by rfl⟩ : syracuseStep 1355459 = 2033189) B2033189
theorem B1879841 : Blo 1112627 1879841 := bstep (se 2 (by rfl) ⟨704940, by rfl⟩ : syracuseStep 1879841 = 1409881) B1409881
theorem B12693347 : Blo 1112627 12693347 := bstep (se 1 (by rfl) ⟨9520010, by rfl⟩ : syracuseStep 12693347 = 19040021) B19040021
theorem B1879969 : Blo 1112627 1879969 := bstep (se 2 (by rfl) ⟨704988, by rfl⟩ : syracuseStep 1879969 = 1409977) B1409977
theorem B5648291 : Blo 1112627 5648291 := bstep (se 1 (by rfl) ⟨4236218, by rfl⟩ : syracuseStep 5648291 = 8472437) B8472437
theorem B1880003 : Blo 1112627 1880003 := bstep (se 1 (by rfl) ⟨1410002, by rfl⟩ : syracuseStep 1880003 = 2820005) B2820005
theorem B1880131 : Blo 1112627 1880131 := bstep (se 1 (by rfl) ⟨1410098, by rfl⟩ : syracuseStep 1880131 = 2820197) B2820197
theorem B10858637 : Blo 1112627 10858637 := bstep (se 3 (by rfl) ⟨2035994, by rfl⟩ : syracuseStep 10858637 = 4071989) B4071989
theorem B1880273 : Blo 1112627 1880273 := bstep (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) B1410205
theorem B1192163 : Blo 1112627 1192163 := bstep (se 1 (by rfl) ⟨894122, by rfl⟩ : syracuseStep 1192163 = 1788245) B1788245
theorem B5714189 : Blo 1112627 5714189 := bstep (se 3 (by rfl) ⟨1071410, by rfl⟩ : syracuseStep 5714189 = 2142821) B2142821
theorem B1880401 : Blo 1112627 1880401 := bstep (se 2 (by rfl) ⟨705150, by rfl⟩ : syracuseStep 1880401 = 1410301) B1410301
theorem B1585507 : Blo 1112627 1585507 := bstep (se 1 (by rfl) ⟨1189130, by rfl⟩ : syracuseStep 1585507 = 2378261) B2378261
theorem B1880435 : Blo 1112627 1880435 := bstep (se 1 (by rfl) ⟨1410326, by rfl⟩ : syracuseStep 1880435 = 2820653) B2820653
theorem B5091761 : Blo 1112627 5091761 := bstep (se 2 (by rfl) ⟨1909410, by rfl⟩ : syracuseStep 5091761 = 3818821) B3818821
theorem B1880563 : Blo 1112627 1880563 := bstep (se 1 (by rfl) ⟨1410422, by rfl⟩ : syracuseStep 1880563 = 2820845) B2820845
theorem B1880705 : Blo 1112627 1880705 := bstep (se 2 (by rfl) ⟨705264, by rfl⟩ : syracuseStep 1880705 = 1410529) B1410529
theorem B4764365 : Blo 1112627 4764365 := bstep (se 3 (by rfl) ⟨893318, by rfl⟩ : syracuseStep 4764365 = 1786637) B1786637
theorem B5649101 : Blo 1112627 5649101 := bstep (se 3 (by rfl) ⟨1059206, by rfl⟩ : syracuseStep 5649101 = 2118413) B2118413
theorem B1880833 : Blo 1112627 1880833 := bstep (se 2 (by rfl) ⟨705312, by rfl⟩ : syracuseStep 1880833 = 1410625) B1410625
theorem B12071693 : Blo 1112627 12071693 := bstep (se 3 (by rfl) ⟨2263442, by rfl⟩ : syracuseStep 12071693 = 4526885) B4526885
theorem B1880867 : Blo 1112627 1880867 := bstep (se 1 (by rfl) ⟨1410650, by rfl⟩ : syracuseStep 1880867 = 2821301) B2821301
theorem B1585985 : Blo 1112627 1585985 := bstep (se 2 (by rfl) ⟨594744, by rfl⟩ : syracuseStep 1585985 = 1189489) B1189489
theorem B6337379 : Blo 1112627 6337379 := bstep (se 1 (by rfl) ⟨4753034, by rfl⟩ : syracuseStep 6337379 = 9506069) B9506069
theorem B10695523 : Blo 1112627 10695523 := bstep (se 1 (by rfl) ⟨8021642, by rfl⟩ : syracuseStep 10695523 = 16043285) B16043285
theorem B3093347 : Blo 1112627 3093347 := bstep (se 1 (by rfl) ⟨2320010, by rfl⟩ : syracuseStep 3093347 = 4640021) B4640021
theorem B1880995 : Blo 1112627 1880995 := bstep (se 1 (by rfl) ⟨1410746, by rfl⟩ : syracuseStep 1880995 = 2821493) B2821493
theorem B2503601 : Blo 1112627 2503601 := bstep (se 2 (by rfl) ⟨938850, by rfl⟩ : syracuseStep 2503601 = 1877701) B1877701
theorem B1586099 : Blo 1112627 1586099 := bstep (se 1 (by rfl) ⟨1189574, by rfl⟩ : syracuseStep 1586099 = 2379149) B2379149
theorem B2503619 : Blo 1112627 2503619 := bstep (se 1 (by rfl) ⟨1877714, by rfl⟩ : syracuseStep 2503619 = 3755429) B3755429
theorem B1586179 : Blo 1112627 1586179 := bstep (se 1 (by rfl) ⟨1189634, by rfl⟩ : syracuseStep 1586179 = 2379269) B2379269
theorem B2012195 : Blo 1112627 2012195 := bstep (se 1 (by rfl) ⟨1509146, by rfl⟩ : syracuseStep 2012195 = 3018293) B3018293
theorem B1881137 : Blo 1112627 1881137 := bstep (se 2 (by rfl) ⟨705426, by rfl⟩ : syracuseStep 1881137 = 1410853) B1410853
theorem B2143345 : Blo 1112627 2143345 := bstep (se 2 (by rfl) ⟨803754, by rfl⟩ : syracuseStep 2143345 = 1607509) B1607509
theorem B1782947 : Blo 1112627 1782947 := bstep (se 1 (by rfl) ⟨1337210, by rfl⟩ : syracuseStep 1782947 = 2674421) B2674421
theorem B1881265 : Blo 1112627 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B2503889 : Blo 1112627 2503889 := bstep (se 2 (by rfl) ⟨938958, by rfl⟩ : syracuseStep 2503889 = 1877917) B1877917
theorem B1881299 : Blo 1112627 1881299 := bstep (se 1 (by rfl) ⟨1410974, by rfl⟩ : syracuseStep 1881299 = 2821949) B2821949
theorem B2503907 : Blo 1112627 2503907 := bstep (se 1 (by rfl) ⟨1877930, by rfl⟩ : syracuseStep 2503907 = 3755861) B3755861
theorem B1881427 : Blo 1112627 1881427 := bstep (se 1 (by rfl) ⟨1411070, by rfl⟩ : syracuseStep 1881427 = 2822141) B2822141
theorem B9024965 : Blo 1112627 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B1881569 : Blo 1112627 1881569 := bstep (se 2 (by rfl) ⟨705588, by rfl⟩ : syracuseStep 1881569 = 1411177) B1411177
theorem B2504177 : Blo 1112627 2504177 := bstep (se 2 (by rfl) ⟨939066, by rfl⟩ : syracuseStep 2504177 = 1878133) B1878133
theorem B2504195 : Blo 1112627 2504195 := bstep (se 1 (by rfl) ⟨1878146, by rfl⟩ : syracuseStep 2504195 = 3756293) B3756293
theorem B1586737 : Blo 1112627 1586737 := bstep (se 2 (by rfl) ⟨595026, by rfl⟩ : syracuseStep 1586737 = 1190053) B1190053
theorem B1881697 : Blo 1112627 1881697 := bstep (se 2 (by rfl) ⟨705636, by rfl⟩ : syracuseStep 1881697 = 1411273) B1411273
theorem B1881731 : Blo 1112627 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B1881859 : Blo 1112627 1881859 := bstep (se 1 (by rfl) ⟨1411394, by rfl⟩ : syracuseStep 1881859 = 2822789) B2822789
theorem B2504465 : Blo 1112627 2504465 := bstep (se 2 (by rfl) ⟨939174, by rfl⟩ : syracuseStep 2504465 = 1878349) B1878349
theorem B2504483 : Blo 1112627 2504483 := bstep (se 1 (by rfl) ⟨1878362, by rfl⟩ : syracuseStep 2504483 = 3756725) B3756725
theorem B1128259 : Blo 1112627 1128259 := bstep (se 1 (by rfl) ⟨846194, by rfl⟩ : syracuseStep 1128259 = 1692389) B1692389
theorem B4011875 : Blo 1112627 4011875 := bstep (se 1 (by rfl) ⟨3008906, by rfl⟩ : syracuseStep 4011875 = 6017813) B6017813
theorem B1882001 : Blo 1112627 1882001 := bstep (se 2 (by rfl) ⟨705750, by rfl⟩ : syracuseStep 1882001 = 1411501) B1411501
theorem B1882129 : Blo 1112627 1882129 := bstep (se 2 (by rfl) ⟨705798, by rfl⟩ : syracuseStep 1882129 = 1411597) B1411597
theorem B2504753 : Blo 1112627 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B1882163 : Blo 1112627 1882163 := bstep (se 1 (by rfl) ⟨1411622, by rfl⟩ : syracuseStep 1882163 = 2823245) B2823245
theorem B2504771 : Blo 1112627 2504771 := bstep (se 1 (by rfl) ⟨1878578, by rfl⟩ : syracuseStep 2504771 = 3757157) B3757157
theorem B8468549 : Blo 1112627 8468549 := bstep (se 4 (by rfl) ⟨793926, by rfl⟩ : syracuseStep 8468549 = 1587853) B1587853
theorem B1783939 : Blo 1112627 1783939 := bstep (se 1 (by rfl) ⟨1337954, by rfl⟩ : syracuseStep 1783939 = 2675909) B2675909
theorem B1882291 : Blo 1112627 1882291 := bstep (se 1 (by rfl) ⟨1411718, by rfl⟩ : syracuseStep 1882291 = 2823437) B2823437
theorem B1718513 : Blo 1112627 1718513 := bstep (se 2 (by rfl) ⟨644442, by rfl⟩ : syracuseStep 1718513 = 1288885) B1288885
theorem B1587443 : Blo 1112627 1587443 := bstep (se 1 (by rfl) ⟨1190582, by rfl⟩ : syracuseStep 1587443 = 2381165) B2381165
theorem B1718561 : Blo 1112627 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B1882433 : Blo 1112627 1882433 := bstep (se 2 (by rfl) ⟨705912, by rfl⟩ : syracuseStep 1882433 = 1411825) B1411825
theorem B4962637 : Blo 1112627 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B2505041 : Blo 1112627 2505041 := bstep (se 2 (by rfl) ⟨939390, by rfl⟩ : syracuseStep 2505041 = 1878781) B1878781
theorem B2505059 : Blo 1112627 2505059 := bstep (se 1 (by rfl) ⟨1878794, by rfl⟩ : syracuseStep 2505059 = 3757589) B3757589
theorem B1784177 : Blo 1112627 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B1882561 : Blo 1112627 1882561 := bstep (se 2 (by rfl) ⟨705960, by rfl⟩ : syracuseStep 1882561 = 1411921) B1411921
theorem B1882595 : Blo 1112627 1882595 := bstep (se 1 (by rfl) ⟨1411946, by rfl⟩ : syracuseStep 1882595 = 2823893) B2823893
theorem B1784387 : Blo 1112627 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B1882723 : Blo 1112627 1882723 := bstep (se 1 (by rfl) ⟨1412042, by rfl⟩ : syracuseStep 1882723 = 2824085) B2824085
theorem B2505329 : Blo 1112627 2505329 := bstep (se 2 (by rfl) ⟨939498, by rfl⟩ : syracuseStep 2505329 = 1878997) B1878997
theorem B2505347 : Blo 1112627 2505347 := bstep (se 1 (by rfl) ⟨1879010, by rfl⟩ : syracuseStep 2505347 = 3758021) B3758021
theorem B1882865 : Blo 1112627 1882865 := bstep (se 2 (by rfl) ⟨706074, by rfl⟩ : syracuseStep 1882865 = 1412149) B1412149
theorem B1588081 : Blo 1112627 1588081 := bstep (se 2 (by rfl) ⟨595530, by rfl⟩ : syracuseStep 1588081 = 1191061) B1191061
theorem B1882993 : Blo 1112627 1882993 := bstep (se 2 (by rfl) ⟨706122, by rfl⟩ : syracuseStep 1882993 = 1412245) B1412245
theorem B2505617 : Blo 1112627 2505617 := bstep (se 2 (by rfl) ⟨939606, by rfl⟩ : syracuseStep 2505617 = 1879213) B1879213
theorem B1883027 : Blo 1112627 1883027 := bstep (se 1 (by rfl) ⟨1412270, by rfl⟩ : syracuseStep 1883027 = 2824541) B2824541
theorem B2505635 : Blo 1112627 2505635 := bstep (se 1 (by rfl) ⟨1879226, by rfl⟩ : syracuseStep 2505635 = 3758453) B3758453
theorem B4013027 : Blo 1112627 4013027 := bstep (se 1 (by rfl) ⟨3009770, by rfl⟩ : syracuseStep 4013027 = 6019541) B6019541
theorem B1588195 : Blo 1112627 1588195 := bstep (se 1 (by rfl) ⟨1191146, by rfl⟩ : syracuseStep 1588195 = 2382293) B2382293
theorem B1883155 : Blo 1112627 1883155 := bstep (se 1 (by rfl) ⟨1412366, by rfl⟩ : syracuseStep 1883155 = 2824733) B2824733
theorem B27475085 : Blo 1112627 27475085 := bstep (se 3 (by rfl) ⟨5151578, by rfl⟩ : syracuseStep 27475085 = 10303157) B10303157
theorem B1883297 : Blo 1112627 1883297 := bstep (se 2 (by rfl) ⟨706236, by rfl⟩ : syracuseStep 1883297 = 1412473) B1412473
theorem B2505905 : Blo 1112627 2505905 := bstep (se 2 (by rfl) ⟨939714, by rfl⟩ : syracuseStep 2505905 = 1879429) B1879429
theorem B2505923 : Blo 1112627 2505923 := bstep (se 1 (by rfl) ⟨1879442, by rfl⟩ : syracuseStep 2505923 = 3758885) B3758885
theorem B1883425 : Blo 1112627 1883425 := bstep (se 2 (by rfl) ⟨706284, by rfl⟩ : syracuseStep 1883425 = 1412569) B1412569
theorem B2112817 : Blo 1112627 2112817 := bstep (se 2 (by rfl) ⟨792306, by rfl⟩ : syracuseStep 2112817 = 1584613) B1584613
theorem B1883459 : Blo 1112627 1883459 := bstep (se 1 (by rfl) ⟨1412594, by rfl⟩ : syracuseStep 1883459 = 2825189) B2825189
theorem B1785169 : Blo 1112627 1785169 := bstep (se 2 (by rfl) ⟨669438, by rfl⟩ : syracuseStep 1785169 = 1338877) B1338877
theorem B1883587 : Blo 1112627 1883587 := bstep (se 1 (by rfl) ⟨1412690, by rfl⟩ : syracuseStep 1883587 = 2825381) B2825381
theorem B2506193 : Blo 1112627 2506193 := bstep (se 2 (by rfl) ⟨939822, by rfl⟩ : syracuseStep 2506193 = 1879645) B1879645
theorem B2506211 : Blo 1112627 2506211 := bstep (se 1 (by rfl) ⟨1879658, by rfl⟩ : syracuseStep 2506211 = 3759317) B3759317
theorem B5652017 : Blo 1112627 5652017 := bstep (se 2 (by rfl) ⟨2119506, by rfl⟩ : syracuseStep 5652017 = 4239013) B4239013
theorem B1883729 : Blo 1112627 1883729 := bstep (se 2 (by rfl) ⟨706398, by rfl⟩ : syracuseStep 1883729 = 1412797) B1412797
theorem B2113219 : Blo 1112627 2113219 := bstep (se 1 (by rfl) ⟨1584914, by rfl⟩ : syracuseStep 2113219 = 3169829) B3169829
theorem B1883857 : Blo 1112627 1883857 := bstep (se 2 (by rfl) ⟨706446, by rfl⟩ : syracuseStep 1883857 = 1412893) B1412893
theorem B2113265 : Blo 1112627 2113265 := bstep (se 2 (by rfl) ⟨792474, by rfl⟩ : syracuseStep 2113265 = 1584949) B1584949
theorem B2506481 : Blo 1112627 2506481 := bstep (se 2 (by rfl) ⟨939930, by rfl⟩ : syracuseStep 2506481 = 1879861) B1879861
theorem B1883891 : Blo 1112627 1883891 := bstep (se 1 (by rfl) ⟨1412918, by rfl⟩ : syracuseStep 1883891 = 2825837) B2825837
theorem B2506499 : Blo 1112627 2506499 := bstep (se 1 (by rfl) ⟨1879874, by rfl⟩ : syracuseStep 2506499 = 3759749) B3759749
theorem B9518917 : Blo 1112627 9518917 := bstep (se 4 (by rfl) ⟨892398, by rfl⟩ : syracuseStep 9518917 = 1784797) B1784797
theorem B1884019 : Blo 1112627 1884019 := bstep (se 1 (by rfl) ⟨1413014, by rfl⟩ : syracuseStep 1884019 = 2826029) B2826029
theorem B1884161 : Blo 1112627 1884161 := bstep (se 2 (by rfl) ⟨706560, by rfl⟩ : syracuseStep 1884161 = 1413121) B1413121
theorem B2113553 : Blo 1112627 2113553 := bstep (se 2 (by rfl) ⟨792582, by rfl⟩ : syracuseStep 2113553 = 1585165) B1585165
theorem B2506769 : Blo 1112627 2506769 := bstep (se 2 (by rfl) ⟨940038, by rfl⟩ : syracuseStep 2506769 = 1880077) B1880077
theorem B2506787 : Blo 1112627 2506787 := bstep (se 1 (by rfl) ⟨1880090, by rfl⟩ : syracuseStep 2506787 = 3760181) B3760181
theorem B5357603 : Blo 1112627 5357603 := bstep (se 1 (by rfl) ⟨4018202, by rfl⟩ : syracuseStep 5357603 = 8036405) B8036405
theorem B1785971 : Blo 1112627 1785971 := bstep (se 1 (by rfl) ⟨1339478, by rfl⟩ : syracuseStep 1785971 = 2678957) B2678957
theorem B1884289 : Blo 1112627 1884289 := bstep (se 2 (by rfl) ⟨706608, by rfl⟩ : syracuseStep 1884289 = 1413217) B1413217
theorem B1589539 : Blo 1112627 1589539 := bstep (se 1 (by rfl) ⟨1192154, by rfl⟩ : syracuseStep 1589539 = 2384309) B2384309
theorem B2507057 : Blo 1112627 2507057 := bstep (se 2 (by rfl) ⟨940146, by rfl⟩ : syracuseStep 2507057 = 1880293) B1880293
theorem B2507075 : Blo 1112627 2507075 := bstep (se 1 (by rfl) ⟨1880306, by rfl⟩ : syracuseStep 2507075 = 3760613) B3760613
theorem B10699249 : Blo 1112627 10699249 := bstep (se 2 (by rfl) ⟨4012218, by rfl⟩ : syracuseStep 10699249 = 8024437) B8024437
theorem B2507345 : Blo 1112627 2507345 := bstep (se 2 (by rfl) ⟨940254, by rfl⟩ : syracuseStep 2507345 = 1880509) B1880509
theorem B2507363 : Blo 1112627 2507363 := bstep (se 1 (by rfl) ⟨1880522, by rfl⟩ : syracuseStep 2507363 = 3761045) B3761045
theorem B1786483 : Blo 1112627 1786483 := bstep (se 1 (by rfl) ⟨1339862, by rfl⟩ : syracuseStep 1786483 = 2679725) B2679725
theorem B2146979 : Blo 1112627 2146979 := bstep (se 1 (by rfl) ⟨1610234, by rfl⟩ : syracuseStep 2146979 = 3220469) B3220469
theorem B1131203 : Blo 1112627 1131203 := bstep (se 1 (by rfl) ⟨848402, by rfl⟩ : syracuseStep 1131203 = 1696805) B1696805
theorem B2114275 : Blo 1112627 2114275 := bstep (se 1 (by rfl) ⟨1585706, by rfl⟩ : syracuseStep 2114275 = 3171413) B3171413
theorem B2540369 : Blo 1112627 2540369 := bstep (se 2 (by rfl) ⟨952638, by rfl⟩ : syracuseStep 2540369 = 1905277) B1905277
theorem B2507633 : Blo 1112627 2507633 := bstep (se 2 (by rfl) ⟨940362, by rfl⟩ : syracuseStep 2507633 = 1880725) B1880725
theorem B2507651 : Blo 1112627 2507651 := bstep (se 1 (by rfl) ⟨1880738, by rfl⟩ : syracuseStep 2507651 = 3761477) B3761477
theorem B3818435 : Blo 1112627 3818435 := bstep (se 1 (by rfl) ⟨2863826, by rfl⟩ : syracuseStep 3818435 = 5727653) B5727653
theorem B4768739 : Blo 1112627 4768739 := bstep (se 1 (by rfl) ⟨3576554, by rfl⟩ : syracuseStep 4768739 = 7153109) B7153109
theorem B6865955 : Blo 1112627 6865955 := bstep (se 1 (by rfl) ⟨5149466, by rfl⟩ : syracuseStep 6865955 = 10298933) B10298933
theorem B2507921 : Blo 1112627 2507921 := bstep (se 2 (by rfl) ⟨940470, by rfl⟩ : syracuseStep 2507921 = 1880941) B1880941
theorem B1787027 : Blo 1112627 1787027 := bstep (se 1 (by rfl) ⟨1340270, by rfl⟩ : syracuseStep 1787027 = 2680541) B2680541
theorem B2114723 : Blo 1112627 2114723 := bstep (se 1 (by rfl) ⟨1586042, by rfl⟩ : syracuseStep 2114723 = 3172085) B3172085
theorem B2507939 : Blo 1112627 2507939 := bstep (se 1 (by rfl) ⟨1880954, by rfl⟩ : syracuseStep 2507939 = 3761909) B3761909
theorem B6112547 : Blo 1112627 6112547 := bstep (se 1 (by rfl) ⟨4584410, by rfl⟩ : syracuseStep 6112547 = 9168821) B9168821
theorem B1787201 : Blo 1112627 1787201 := bstep (se 2 (by rfl) ⟨670200, by rfl⟩ : syracuseStep 1787201 = 1340401) B1340401
theorem B2508209 : Blo 1112627 2508209 := bstep (se 2 (by rfl) ⟨940578, by rfl⟩ : syracuseStep 2508209 = 1881157) B1881157
theorem B2115011 : Blo 1112627 2115011 := bstep (se 1 (by rfl) ⟨1586258, by rfl⟩ : syracuseStep 2115011 = 3172517) B3172517
theorem B2508227 : Blo 1112627 2508227 := bstep (se 1 (by rfl) ⟨1881170, by rfl⟩ : syracuseStep 2508227 = 3762341) B3762341
theorem B4015565 : Blo 1112627 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B2377201 : Blo 1112627 2377201 := bstep (se 2 (by rfl) ⟨891450, by rfl⟩ : syracuseStep 2377201 = 1782901) B1782901
theorem B8046179 : Blo 1112627 8046179 := bstep (se 1 (by rfl) ⟨6034634, by rfl⟩ : syracuseStep 8046179 = 12069269) B12069269
theorem B2508497 : Blo 1112627 2508497 := bstep (se 2 (by rfl) ⟨940686, by rfl⟩ : syracuseStep 2508497 = 1881373) B1881373
theorem B2148049 : Blo 1112627 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B2508515 : Blo 1112627 2508515 := bstep (se 1 (by rfl) ⟨1881386, by rfl⟩ : syracuseStep 2508515 = 3762773) B3762773
theorem B2377603 : Blo 1112627 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B2508785 : Blo 1112627 2508785 := bstep (se 2 (by rfl) ⟨940794, by rfl⟩ : syracuseStep 2508785 = 1881589) B1881589
theorem B2508803 : Blo 1112627 2508803 := bstep (se 1 (by rfl) ⟨1881602, by rfl⟩ : syracuseStep 2508803 = 3763205) B3763205
theorem B2509073 : Blo 1112627 2509073 := bstep (se 2 (by rfl) ⟨940902, by rfl⟩ : syracuseStep 2509073 = 1881805) B1881805
theorem B2509091 : Blo 1112627 2509091 := bstep (se 1 (by rfl) ⟨1881818, by rfl⟩ : syracuseStep 2509091 = 3763637) B3763637
theorem B2115953 : Blo 1112627 2115953 := bstep (se 2 (by rfl) ⟨793482, by rfl⟩ : syracuseStep 2115953 = 1586965) B1586965
theorem B2509361 : Blo 1112627 2509361 := bstep (se 2 (by rfl) ⟨941010, by rfl⟩ : syracuseStep 2509361 = 1882021) B1882021
theorem B2509379 : Blo 1112627 2509379 := bstep (se 1 (by rfl) ⟨1882034, by rfl⟩ : syracuseStep 2509379 = 3764069) B3764069
theorem B28592837 : Blo 1112627 28592837 := bstep (se 4 (by rfl) ⟨2680578, by rfl⟩ : syracuseStep 28592837 = 5361157) B5361157
theorem B2509649 : Blo 1112627 2509649 := bstep (se 2 (by rfl) ⟨941118, by rfl⟩ : syracuseStep 2509649 = 1882237) B1882237
theorem B2509667 : Blo 1112627 2509667 := bstep (se 1 (by rfl) ⟨1882250, by rfl⟩ : syracuseStep 2509667 = 3764501) B3764501
theorem B10308707 : Blo 1112627 10308707 := bstep (se 1 (by rfl) ⟨7731530, by rfl⟩ : syracuseStep 10308707 = 15463061) B15463061
theorem B2509937 : Blo 1112627 2509937 := bstep (se 2 (by rfl) ⟨941226, by rfl⟩ : syracuseStep 2509937 = 1882453) B1882453
theorem B2509955 : Blo 1112627 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B3755213 : Blo 1112627 3755213 := bstep (se 3 (by rfl) ⟨704102, by rfl⟩ : syracuseStep 3755213 = 1408205) B1408205
theorem B2116849 : Blo 1112627 2116849 := bstep (se 2 (by rfl) ⟨793818, by rfl⟩ : syracuseStep 2116849 = 1587637) B1587637
theorem B3755267 : Blo 1112627 3755267 := bstep (se 1 (by rfl) ⟨2816450, by rfl⟩ : syracuseStep 3755267 = 5632901) B5632901
theorem B2379107 : Blo 1112627 2379107 := bstep (se 1 (by rfl) ⟨1784330, by rfl⟩ : syracuseStep 2379107 = 3568661) B3568661
theorem B2117009 : Blo 1112627 2117009 := bstep (se 2 (by rfl) ⟨793878, by rfl⟩ : syracuseStep 2117009 = 1587757) B1587757
theorem B2510225 : Blo 1112627 2510225 := bstep (se 2 (by rfl) ⟨941334, by rfl⟩ : syracuseStep 2510225 = 1882669) B1882669
theorem B2510243 : Blo 1112627 2510243 := bstep (se 1 (by rfl) ⟨1882682, by rfl⟩ : syracuseStep 2510243 = 3765365) B3765365
theorem B3755537 : Blo 1112627 3755537 := bstep (se 2 (by rfl) ⟨1408326, by rfl⟩ : syracuseStep 3755537 = 2816653) B2816653
theorem B3264077 : Blo 1112627 3264077 := bstep (se 3 (by rfl) ⟨612014, by rfl⟩ : syracuseStep 3264077 = 1224029) B1224029
theorem B2510513 : Blo 1112627 2510513 := bstep (se 2 (by rfl) ⟨941442, by rfl⟩ : syracuseStep 2510513 = 1882885) B1882885
theorem B2510531 : Blo 1112627 2510531 := bstep (se 1 (by rfl) ⟨1882898, by rfl⟩ : syracuseStep 2510531 = 3765797) B3765797
theorem B8474381 : Blo 1112627 8474381 := bstep (se 3 (by rfl) ⟨1588946, by rfl⟩ : syracuseStep 8474381 = 3177893) B3177893
theorem B2117411 : Blo 1112627 2117411 := bstep (se 1 (by rfl) ⟨1588058, by rfl⟩ : syracuseStep 2117411 = 3176117) B3176117
theorem B2510801 : Blo 1112627 2510801 := bstep (se 2 (by rfl) ⟨941550, by rfl⟩ : syracuseStep 2510801 = 1883101) B1883101
theorem B2510819 : Blo 1112627 2510819 := bstep (se 1 (by rfl) ⟨1883114, by rfl⟩ : syracuseStep 2510819 = 3766229) B3766229
theorem B3756077 : Blo 1112627 3756077 := bstep (se 3 (by rfl) ⟨704264, by rfl⟩ : syracuseStep 3756077 = 1408529) B1408529
theorem B3756131 : Blo 1112627 3756131 := bstep (se 1 (by rfl) ⟨2817098, by rfl⟩ : syracuseStep 3756131 = 5634197) B5634197
theorem B6443107 : Blo 1112627 6443107 := bstep (se 1 (by rfl) ⟨4832330, by rfl⟩ : syracuseStep 6443107 = 9664661) B9664661
theorem B21418181 : Blo 1112627 21418181 := bstep (se 4 (by rfl) ⟨2007954, by rfl⟩ : syracuseStep 21418181 = 4015909) B4015909
theorem B2511089 : Blo 1112627 2511089 := bstep (se 2 (by rfl) ⟨941658, by rfl⟩ : syracuseStep 2511089 = 1883317) B1883317
theorem B2511107 : Blo 1112627 2511107 := bstep (se 1 (by rfl) ⟨1883330, by rfl⟩ : syracuseStep 2511107 = 3766661) B3766661
theorem B7131397 : Blo 1112627 7131397 := bstep (se 4 (by rfl) ⟨668568, by rfl⟩ : syracuseStep 7131397 = 1337137) B1337137
theorem B3756401 : Blo 1112627 3756401 := bstep (se 2 (by rfl) ⟨1408650, by rfl⟩ : syracuseStep 3756401 = 2817301) B2817301
theorem B20304269 : Blo 1112627 20304269 := bstep (se 3 (by rfl) ⟨3807050, by rfl⟩ : syracuseStep 20304269 = 7614101) B7614101
theorem B6771107 : Blo 1112627 6771107 := bstep (se 1 (by rfl) ⟨5078330, by rfl⟩ : syracuseStep 6771107 = 10156661) B10156661
theorem B6771185 : Blo 1112627 6771185 := bstep (se 2 (by rfl) ⟨2539194, by rfl⟩ : syracuseStep 6771185 = 5078389) B5078389
theorem B2511377 : Blo 1112627 2511377 := bstep (se 2 (by rfl) ⟨941766, by rfl⟩ : syracuseStep 2511377 = 1883533) B1883533
theorem B2511395 : Blo 1112627 2511395 := bstep (se 1 (by rfl) ⟨1883546, by rfl⟩ : syracuseStep 2511395 = 3767093) B3767093
theorem B2380337 : Blo 1112627 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B2118307 : Blo 1112627 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B6771377 : Blo 1112627 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B2511665 : Blo 1112627 2511665 := bstep (se 2 (by rfl) ⟨941874, by rfl⟩ : syracuseStep 2511665 = 1883749) B1883749
theorem B2118467 : Blo 1112627 2118467 := bstep (se 1 (by rfl) ⟨1588850, by rfl⟩ : syracuseStep 2118467 = 3177701) B3177701
theorem B2511683 : Blo 1112627 2511683 := bstep (se 1 (by rfl) ⟨1883762, by rfl⟩ : syracuseStep 2511683 = 3767525) B3767525
theorem B3756941 : Blo 1112627 3756941 := bstep (se 3 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 3756941 = 1408853) B1408853
theorem B3756995 : Blo 1112627 3756995 := bstep (se 1 (by rfl) ⟨2817746, by rfl⟩ : syracuseStep 3756995 = 5635493) B5635493
theorem B2511953 : Blo 1112627 2511953 := bstep (se 2 (by rfl) ⟨941982, by rfl⟩ : syracuseStep 2511953 = 1883965) B1883965
theorem B2511971 : Blo 1112627 2511971 := bstep (se 1 (by rfl) ⟨1883978, by rfl⟩ : syracuseStep 2511971 = 3767957) B3767957
theorem B3757265 : Blo 1112627 3757265 := bstep (se 2 (by rfl) ⟨1408974, by rfl⟩ : syracuseStep 3757265 = 2817949) B2817949
theorem B2512241 : Blo 1112627 2512241 := bstep (se 2 (by rfl) ⟨942090, by rfl⟩ : syracuseStep 2512241 = 1884181) B1884181
theorem B14308721 : Blo 1112627 14308721 := bstep (se 2 (by rfl) ⟨5365770, by rfl⟩ : syracuseStep 14308721 = 10731541) B10731541
theorem B2512259 : Blo 1112627 2512259 := bstep (se 1 (by rfl) ⟨1884194, by rfl⟩ : syracuseStep 2512259 = 3768389) B3768389
theorem B2381233 : Blo 1112627 2381233 := bstep (se 2 (by rfl) ⟨892962, by rfl⟩ : syracuseStep 2381233 = 1785925) B1785925
theorem B2381251 : Blo 1112627 2381251 := bstep (se 1 (by rfl) ⟨1785938, by rfl⟩ : syracuseStep 2381251 = 3571877) B3571877
theorem B6346309 : Blo 1112627 6346309 := bstep (se 4 (by rfl) ⟨594966, by rfl⟩ : syracuseStep 6346309 = 1189933) B1189933
theorem B3757805 : Blo 1112627 3757805 := bstep (se 3 (by rfl) ⟨704588, by rfl⟩ : syracuseStep 3757805 = 1409177) B1409177
theorem B3757859 : Blo 1112627 3757859 := bstep (se 1 (by rfl) ⟨2818394, by rfl⟩ : syracuseStep 3757859 = 5636789) B5636789
theorem B2119537 : Blo 1112627 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B3758129 : Blo 1112627 3758129 := bstep (se 2 (by rfl) ⟨1409298, by rfl⟩ : syracuseStep 3758129 = 2818597) B2818597
theorem B2676881 : Blo 1112627 2676881 := bstep (se 2 (by rfl) ⟨1003830, by rfl⟩ : syracuseStep 2676881 = 2007661) B2007661
theorem B3168497 : Blo 1112627 3168497 := bstep (se 2 (by rfl) ⟨1188186, by rfl⟩ : syracuseStep 3168497 = 2376373) B2376373
theorem B13752773 : Blo 1112627 13752773 := bstep (se 4 (by rfl) ⟨1289322, by rfl⟩ : syracuseStep 13752773 = 2578645) B2578645
theorem B2677265 : Blo 1112627 2677265 := bstep (se 2 (by rfl) ⟨1003974, by rfl⟩ : syracuseStep 2677265 = 2007949) B2007949
theorem B1694225 : Blo 1112627 1694225 := bstep (se 2 (by rfl) ⟨635334, by rfl⟩ : syracuseStep 1694225 = 1270669) B1270669
theorem B4020785 : Blo 1112627 4020785 := bstep (se 2 (by rfl) ⟨1507794, by rfl⟩ : syracuseStep 4020785 = 3015589) B3015589
theorem B3758669 : Blo 1112627 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B8477297 : Blo 1112627 8477297 := bstep (se 2 (by rfl) ⟨3178986, by rfl⟩ : syracuseStep 8477297 = 6357973) B6357973
theorem B3758723 : Blo 1112627 3758723 := bstep (se 1 (by rfl) ⟨2819042, by rfl⟩ : syracuseStep 3758723 = 5638085) B5638085
theorem B1694353 : Blo 1112627 1694353 := bstep (se 2 (by rfl) ⟨635382, by rfl⟩ : syracuseStep 1694353 = 1270765) B1270765
theorem B1694401 : Blo 1112627 1694401 := bstep (se 2 (by rfl) ⟨635400, by rfl⟩ : syracuseStep 1694401 = 1270801) B1270801
theorem B3169169 : Blo 1112627 3169169 := bstep (se 2 (by rfl) ⟨1188438, by rfl⟩ : syracuseStep 3169169 = 2376877) B2376877
theorem B3758993 : Blo 1112627 3758993 := bstep (se 2 (by rfl) ⟨1409622, by rfl⟩ : syracuseStep 3758993 = 2819245) B2819245
theorem B7134115 : Blo 1112627 7134115 := bstep (se 1 (by rfl) ⟨5350586, by rfl⟩ : syracuseStep 7134115 = 10701173) B10701173
theorem B1694723 : Blo 1112627 1694723 := bstep (se 1 (by rfl) ⟨1271042, by rfl⟩ : syracuseStep 1694723 = 2542085) B2542085
theorem B3759533 : Blo 1112627 3759533 := bstep (se 3 (by rfl) ⟨704912, by rfl⟩ : syracuseStep 3759533 = 1409825) B1409825
theorem B4513229 : Blo 1112627 4513229 := bstep (se 3 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 4513229 = 1692461) B1692461
theorem B3759587 : Blo 1112627 3759587 := bstep (se 1 (by rfl) ⟨2819690, by rfl⟩ : syracuseStep 3759587 = 5639381) B5639381
theorem B6348293 : Blo 1112627 6348293 := bstep (se 4 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 6348293 = 1190305) B1190305
theorem B2383523 : Blo 1112627 2383523 := bstep (se 1 (by rfl) ⟨1787642, by rfl⟩ : syracuseStep 2383523 = 3575285) B3575285
theorem B3169955 : Blo 1112627 3169955 := bstep (se 1 (by rfl) ⟨2377466, by rfl⟩ : syracuseStep 3169955 = 4754933) B4754933
theorem B3759857 : Blo 1112627 3759857 := bstep (se 2 (by rfl) ⟨1409946, by rfl⟩ : syracuseStep 3759857 = 2819893) B2819893
theorem B1695667 : Blo 1112627 1695667 := bstep (se 1 (by rfl) ⟨1271750, by rfl⟩ : syracuseStep 1695667 = 2543501) B2543501
theorem B3170285 : Blo 1112627 3170285 := bstep (se 3 (by rfl) ⟨594428, by rfl⟩ : syracuseStep 3170285 = 1188857) B1188857
theorem B3170353 : Blo 1112627 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B2383985 : Blo 1112627 2383985 := bstep (se 2 (by rfl) ⟨893994, by rfl⟩ : syracuseStep 2383985 = 1787989) B1787989
theorem B3760397 : Blo 1112627 3760397 := bstep (se 3 (by rfl) ⟨705074, by rfl⟩ : syracuseStep 3760397 = 1410149) B1410149
theorem B3170627 : Blo 1112627 3170627 := bstep (se 1 (by rfl) ⟨2377970, by rfl⟩ : syracuseStep 3170627 = 4755941) B4755941
theorem B3760451 : Blo 1112627 3760451 := bstep (se 1 (by rfl) ⟨2820338, by rfl⟩ : syracuseStep 3760451 = 5640677) B5640677
theorem B9527665 : Blo 1112627 9527665 := bstep (se 2 (by rfl) ⟨3572874, by rfl⟩ : syracuseStep 9527665 = 7145749) B7145749
theorem B3760721 : Blo 1112627 3760721 := bstep (se 2 (by rfl) ⟨1410270, by rfl⟩ : syracuseStep 3760721 = 2820541) B2820541
theorem B8020721 : Blo 1112627 8020721 := bstep (se 2 (by rfl) ⟨3007770, by rfl⟩ : syracuseStep 8020721 = 6015541) B6015541
theorem B1696499 : Blo 1112627 1696499 := bstep (se 1 (by rfl) ⟨1272374, by rfl⟩ : syracuseStep 1696499 = 2544749) B2544749
theorem B7136113 : Blo 1112627 7136113 := bstep (se 2 (by rfl) ⟨2676042, by rfl⟩ : syracuseStep 7136113 = 5352085) B5352085
theorem B1696835 : Blo 1112627 1696835 := bstep (se 1 (by rfl) ⟨1272626, by rfl⟩ : syracuseStep 1696835 = 2545253) B2545253
theorem B2679907 : Blo 1112627 2679907 := bstep (se 1 (by rfl) ⟨2009930, by rfl⟩ : syracuseStep 2679907 = 4019861) B4019861
theorem B3761261 : Blo 1112627 3761261 := bstep (se 3 (by rfl) ⟨705236, by rfl⟩ : syracuseStep 3761261 = 1410473) B1410473
theorem B3171469 : Blo 1112627 3171469 := bstep (se 3 (by rfl) ⟨594650, by rfl⟩ : syracuseStep 3171469 = 1189301) B1189301
theorem B3761315 : Blo 1112627 3761315 := bstep (se 1 (by rfl) ⟨2820986, by rfl⟩ : syracuseStep 3761315 = 5641973) B5641973
theorem B3564803 : Blo 1112627 3564803 := bstep (se 1 (by rfl) ⟨2673602, by rfl⟩ : syracuseStep 3564803 = 5347205) B5347205
theorem B3171629 : Blo 1112627 3171629 := bstep (se 3 (by rfl) ⟨594680, by rfl⟩ : syracuseStep 3171629 = 1189361) B1189361
theorem B3564931 : Blo 1112627 3564931 := bstep (se 1 (by rfl) ⟨2673698, by rfl⟩ : syracuseStep 3564931 = 5347397) B5347397
theorem B3761585 : Blo 1112627 3761585 := bstep (se 2 (by rfl) ⟨1410594, by rfl⟩ : syracuseStep 3761585 = 2821189) B2821189
theorem B3171811 : Blo 1112627 3171811 := bstep (se 1 (by rfl) ⟨2378858, by rfl⟩ : syracuseStep 3171811 = 4757717) B4757717
theorem B3565073 : Blo 1112627 3565073 := bstep (se 2 (by rfl) ⟨1336902, by rfl⟩ : syracuseStep 3565073 = 2673805) B2673805
theorem B3565187 : Blo 1112627 3565187 := bstep (se 1 (by rfl) ⟨2673890, by rfl⟩ : syracuseStep 3565187 = 5347781) B5347781
theorem B2680465 : Blo 1112627 2680465 := bstep (se 2 (by rfl) ⟨1005174, by rfl⟩ : syracuseStep 2680465 = 2010349) B2010349
theorem B3762125 : Blo 1112627 3762125 := bstep (se 3 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 3762125 = 1410797) B1410797
theorem B2942929 : Blo 1112627 2942929 := bstep (se 2 (by rfl) ⟨1103598, by rfl⟩ : syracuseStep 2942929 = 2207197) B2207197
theorem B6023153 : Blo 1112627 6023153 := bstep (se 2 (by rfl) ⟨2258682, by rfl⟩ : syracuseStep 6023153 = 4517365) B4517365
theorem B3762179 : Blo 1112627 3762179 := bstep (se 1 (by rfl) ⟨2821634, by rfl⟩ : syracuseStep 3762179 = 5643269) B5643269
theorem B6023173 : Blo 1112627 6023173 := bstep (se 4 (by rfl) ⟨564672, by rfl⟩ : syracuseStep 6023173 = 1129345) B1129345
theorem B4712689 : Blo 1112627 4712689 := bstep (se 2 (by rfl) ⟨1767258, by rfl⟩ : syracuseStep 4712689 = 3534517) B3534517
theorem B3762449 : Blo 1112627 3762449 := bstep (se 2 (by rfl) ⟨1410918, by rfl⟩ : syracuseStep 3762449 = 2821837) B2821837
theorem B2681137 : Blo 1112627 2681137 := bstep (se 2 (by rfl) ⟨1005426, by rfl⟩ : syracuseStep 2681137 = 2010853) B2010853
theorem B28961333 : Blo 1112627 28961333 := bstep (se 5 (by rfl) ⟨1357562, by rfl⟩ : syracuseStep 28961333 = 2715125) B2715125
theorem B3009187 : Blo 1112627 3009187 := bstep (se 1 (by rfl) ⟨2256890, by rfl⟩ : syracuseStep 3009187 = 4513781) B4513781
theorem B3009251 : Blo 1112627 3009251 := bstep (se 1 (by rfl) ⟨2256938, by rfl⟩ : syracuseStep 3009251 = 4513877) B4513877
theorem B3762989 : Blo 1112627 3762989 := bstep (se 3 (by rfl) ⟨705560, by rfl⟩ : syracuseStep 3762989 = 1411121) B1411121
theorem B3173201 : Blo 1112627 3173201 := bstep (se 2 (by rfl) ⟨1189950, by rfl⟩ : syracuseStep 3173201 = 2379901) B2379901
theorem B3763043 : Blo 1112627 3763043 := bstep (se 1 (by rfl) ⟨2822282, by rfl⟩ : syracuseStep 3763043 = 5644565) B5644565
theorem B13560803 : Blo 1112627 13560803 := bstep (se 1 (by rfl) ⟨10170602, by rfl⟩ : syracuseStep 13560803 = 20341205) B20341205
theorem B3763313 : Blo 1112627 3763313 := bstep (se 2 (by rfl) ⟨1411242, by rfl⟩ : syracuseStep 3763313 = 2822485) B2822485
theorem B7630085 : Blo 1112627 7630085 := bstep (se 4 (by rfl) ⟨715320, by rfl⟩ : syracuseStep 7630085 = 1430641) B1430641
theorem B6352141 : Blo 1112627 6352141 := bstep (se 3 (by rfl) ⟨1191026, by rfl⟩ : syracuseStep 6352141 = 2382053) B2382053
theorem B3566929 : Blo 1112627 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B4287857 : Blo 1112627 4287857 := bstep (se 2 (by rfl) ⟨1607946, by rfl⟩ : syracuseStep 4287857 = 3215893) B3215893
theorem B7237219 : Blo 1112627 7237219 := bstep (se 1 (by rfl) ⟨5427914, by rfl⟩ : syracuseStep 7237219 = 10855829) B10855829
theorem B3763853 : Blo 1112627 3763853 := bstep (se 3 (by rfl) ⟨705722, by rfl⟩ : syracuseStep 3763853 = 1411445) B1411445
theorem B3010193 : Blo 1112627 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B3763907 : Blo 1112627 3763907 := bstep (se 1 (by rfl) ⟨2822930, by rfl⟩ : syracuseStep 3763907 = 5645861) B5645861
theorem B13758149 : Blo 1112627 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B3174157 : Blo 1112627 3174157 := bstep (se 3 (by rfl) ⟨595154, by rfl⟩ : syracuseStep 3174157 = 1190309) B1190309
theorem B97677197 : Blo 1112627 97677197 := bstep (se 3 (by rfl) ⟨18314474, by rfl⟩ : syracuseStep 97677197 = 36628949) B36628949
theorem B3764177 : Blo 1112627 3764177 := bstep (se 2 (by rfl) ⟨1411566, by rfl⟩ : syracuseStep 3764177 = 2823133) B2823133
theorem B8024035 : Blo 1112627 8024035 := bstep (se 1 (by rfl) ⟨6018026, by rfl⟩ : syracuseStep 8024035 = 12036053) B12036053
theorem B1339363 : Blo 1112627 1339363 := bstep (se 1 (by rfl) ⟨1004522, by rfl⟩ : syracuseStep 1339363 = 2009045) B2009045
theorem B3174385 : Blo 1112627 3174385 := bstep (se 2 (by rfl) ⟨1190394, by rfl⟩ : syracuseStep 3174385 = 2380789) B2380789
theorem B3174545 : Blo 1112627 3174545 := bstep (se 2 (by rfl) ⟨1190454, by rfl⟩ : syracuseStep 3174545 = 2380909) B2380909
theorem B3010765 : Blo 1112627 3010765 := bstep (se 3 (by rfl) ⟨564518, by rfl⟩ : syracuseStep 3010765 = 1129037) B1129037
theorem B6025421 : Blo 1112627 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B3174659 : Blo 1112627 3174659 := bstep (se 1 (by rfl) ⟨2380994, by rfl⟩ : syracuseStep 3174659 = 4761989) B4761989
theorem B3568045 : Blo 1112627 3568045 := bstep (se 3 (by rfl) ⟨669008, by rfl⟩ : syracuseStep 3568045 = 1338017) B1338017
theorem B3764717 : Blo 1112627 3764717 := bstep (se 3 (by rfl) ⟨705884, by rfl⟩ : syracuseStep 3764717 = 1411769) B1411769
theorem B3764771 : Blo 1112627 3764771 := bstep (se 1 (by rfl) ⟨2823578, by rfl⟩ : syracuseStep 3764771 = 5647157) B5647157
theorem B4289123 : Blo 1112627 4289123 := bstep (se 1 (by rfl) ⟨3216842, by rfl⟩ : syracuseStep 4289123 = 6433685) B6433685
theorem B5632739 : Blo 1112627 5632739 := bstep (se 1 (by rfl) ⟨4224554, by rfl⟩ : syracuseStep 5632739 = 8449109) B8449109
theorem B3765041 : Blo 1112627 3765041 := bstep (se 2 (by rfl) ⟨1411890, by rfl⟩ : syracuseStep 3765041 = 2823781) B2823781
theorem B6354125 : Blo 1112627 6354125 := bstep (se 3 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 6354125 = 2382797) B2382797
theorem B3568877 : Blo 1112627 3568877 := bstep (se 3 (by rfl) ⟨669164, by rfl⟩ : syracuseStep 3568877 = 1338329) B1338329
theorem B3175661 : Blo 1112627 3175661 := bstep (se 3 (by rfl) ⟨595436, by rfl⟩ : syracuseStep 3175661 = 1190873) B1190873
theorem B3765581 : Blo 1112627 3765581 := bstep (se 3 (by rfl) ⟨706046, by rfl⟩ : syracuseStep 3765581 = 1412093) B1412093
theorem B3765635 : Blo 1112627 3765635 := bstep (se 1 (by rfl) ⟨2824226, by rfl⟩ : syracuseStep 3765635 = 5648453) B5648453
theorem B3175843 : Blo 1112627 3175843 := bstep (se 1 (by rfl) ⟨2381882, by rfl⟩ : syracuseStep 3175843 = 4763765) B4763765
theorem B5633549 : Blo 1112627 5633549 := bstep (se 3 (by rfl) ⟨1056290, by rfl⟩ : syracuseStep 5633549 = 2112581) B2112581
theorem B3176003 : Blo 1112627 3176003 := bstep (se 1 (by rfl) ⟨2382002, by rfl⟩ : syracuseStep 3176003 = 4764005) B4764005
theorem B9532997 : Blo 1112627 9532997 := bstep (se 4 (by rfl) ⟨893718, by rfl⟩ : syracuseStep 9532997 = 1787437) B1787437
theorem B18347633 : Blo 1112627 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B3765905 : Blo 1112627 3765905 := bstep (se 2 (by rfl) ⟨1412214, by rfl⟩ : syracuseStep 3765905 = 2824429) B2824429
theorem B1341155 : Blo 1112627 1341155 := bstep (se 1 (by rfl) ⟨1005866, by rfl⟩ : syracuseStep 1341155 = 2011733) B2011733
theorem B3012365 : Blo 1112627 3012365 := bstep (se 3 (by rfl) ⟨564818, by rfl⟩ : syracuseStep 3012365 = 1129637) B1129637
theorem B2258723 : Blo 1112627 2258723 := bstep (se 1 (by rfl) ⟨1694042, by rfl⟩ : syracuseStep 2258723 = 3388085) B3388085
theorem B1668947 : Blo 1112627 1668947 := bstep (se 1 (by rfl) ⟨1251710, by rfl⟩ : syracuseStep 1668947 = 2503421) B2503421
theorem B1668977 : Blo 1112627 1668977 := bstep (se 2 (by rfl) ⟨625866, by rfl⟩ : syracuseStep 1668977 = 1251733) B1251733
theorem B1668995 : Blo 1112627 1668995 := bstep (se 1 (by rfl) ⟨1251746, by rfl⟩ : syracuseStep 1668995 = 2503493) B2503493
theorem B1669025 : Blo 1112627 1669025 := bstep (se 2 (by rfl) ⟨625884, by rfl⟩ : syracuseStep 1669025 = 1251769) B1251769
theorem B1669043 : Blo 1112627 1669043 := bstep (se 1 (by rfl) ⟨1251782, by rfl⟩ : syracuseStep 1669043 = 2503565) B2503565
theorem B1669073 : Blo 1112627 1669073 := bstep (se 2 (by rfl) ⟨625902, by rfl⟩ : syracuseStep 1669073 = 1251805) B1251805
theorem B1669091 : Blo 1112627 1669091 := bstep (se 1 (by rfl) ⟨1251818, by rfl⟩ : syracuseStep 1669091 = 2503637) B2503637
theorem B1669121 : Blo 1112627 1669121 := bstep (se 2 (by rfl) ⟨625920, by rfl⟩ : syracuseStep 1669121 = 1251841) B1251841
theorem B1669139 : Blo 1112627 1669139 := bstep (se 1 (by rfl) ⟨1251854, by rfl⟩ : syracuseStep 1669139 = 2503709) B2503709
theorem B1669169 : Blo 1112627 1669169 := bstep (se 2 (by rfl) ⟨625938, by rfl⟩ : syracuseStep 1669169 = 1251877) B1251877
theorem B1669187 : Blo 1112627 1669187 := bstep (se 1 (by rfl) ⟨1251890, by rfl⟩ : syracuseStep 1669187 = 2503781) B2503781
theorem B7141445 : Blo 1112627 7141445 := bstep (se 4 (by rfl) ⟨669510, by rfl⟩ : syracuseStep 7141445 = 1339021) B1339021
theorem B1669217 : Blo 1112627 1669217 := bstep (se 2 (by rfl) ⟨625956, by rfl⟩ : syracuseStep 1669217 = 1251913) B1251913
theorem B6355057 : Blo 1112627 6355057 := bstep (se 2 (by rfl) ⟨2383146, by rfl⟩ : syracuseStep 6355057 = 4766293) B4766293
theorem B1669235 : Blo 1112627 1669235 := bstep (se 1 (by rfl) ⟨1251926, by rfl⟩ : syracuseStep 1669235 = 2503853) B2503853
theorem B1669265 : Blo 1112627 1669265 := bstep (se 2 (by rfl) ⟨625974, by rfl⟩ : syracuseStep 1669265 = 1251949) B1251949
theorem B1669283 : Blo 1112627 1669283 := bstep (se 1 (by rfl) ⟨1251962, by rfl⟩ : syracuseStep 1669283 = 2503925) B2503925
theorem B3766445 : Blo 1112627 3766445 := bstep (se 3 (by rfl) ⟨706208, by rfl⟩ : syracuseStep 3766445 = 1412417) B1412417
theorem B1669313 : Blo 1112627 1669313 := bstep (se 2 (by rfl) ⟨625992, by rfl⟩ : syracuseStep 1669313 = 1251985) B1251985
theorem B1669331 : Blo 1112627 1669331 := bstep (se 1 (by rfl) ⟨1251998, by rfl⟩ : syracuseStep 1669331 = 2503997) B2503997
theorem B3766499 : Blo 1112627 3766499 := bstep (se 1 (by rfl) ⟨2824874, by rfl⟩ : syracuseStep 3766499 = 5649749) B5649749
theorem B1669361 : Blo 1112627 1669361 := bstep (se 2 (by rfl) ⟨626010, by rfl⟩ : syracuseStep 1669361 = 1252021) B1252021
theorem B1669379 : Blo 1112627 1669379 := bstep (se 1 (by rfl) ⟨1252034, by rfl⟩ : syracuseStep 1669379 = 2504069) B2504069
theorem B1669409 : Blo 1112627 1669409 := bstep (se 2 (by rfl) ⟨626028, by rfl⟩ : syracuseStep 1669409 = 1252057) B1252057
theorem B1669427 : Blo 1112627 1669427 := bstep (se 1 (by rfl) ⟨1252070, by rfl⟩ : syracuseStep 1669427 = 2504141) B2504141
theorem B11008325 : Blo 1112627 11008325 := bstep (se 4 (by rfl) ⟨1032030, by rfl⟩ : syracuseStep 11008325 = 2064061) B2064061
theorem B1669457 : Blo 1112627 1669457 := bstep (se 2 (by rfl) ⟨626046, by rfl⟩ : syracuseStep 1669457 = 1252093) B1252093
theorem B1669475 : Blo 1112627 1669475 := bstep (se 1 (by rfl) ⟨1252106, by rfl⟩ : syracuseStep 1669475 = 2504213) B2504213
theorem B1669505 : Blo 1112627 1669505 := bstep (se 2 (by rfl) ⟨626064, by rfl⟩ : syracuseStep 1669505 = 1252129) B1252129
theorem B1669523 : Blo 1112627 1669523 := bstep (se 1 (by rfl) ⟨1252142, by rfl⟩ : syracuseStep 1669523 = 2504285) B2504285
theorem B1669553 : Blo 1112627 1669553 := bstep (se 2 (by rfl) ⟨626082, by rfl⟩ : syracuseStep 1669553 = 1252165) B1252165
theorem B1505729 : Blo 1112627 1505729 := bstep (se 2 (by rfl) ⟨564648, by rfl⟩ : syracuseStep 1505729 = 1129297) B1129297
theorem B1669571 : Blo 1112627 1669571 := bstep (se 1 (by rfl) ⟨1252178, by rfl⟩ : syracuseStep 1669571 = 2504357) B2504357
theorem B1669601 : Blo 1112627 1669601 := bstep (se 2 (by rfl) ⟨626100, by rfl⟩ : syracuseStep 1669601 = 1252201) B1252201
theorem B3766769 : Blo 1112627 3766769 := bstep (se 2 (by rfl) ⟨1412538, by rfl⟩ : syracuseStep 3766769 = 2825077) B2825077
theorem B1669619 : Blo 1112627 1669619 := bstep (se 1 (by rfl) ⟨1252214, by rfl⟩ : syracuseStep 1669619 = 2504429) B2504429
theorem B1669649 : Blo 1112627 1669649 := bstep (se 2 (by rfl) ⟨626118, by rfl⟩ : syracuseStep 1669649 = 1252237) B1252237
theorem B1669667 : Blo 1112627 1669667 := bstep (se 1 (by rfl) ⟨1252250, by rfl⟩ : syracuseStep 1669667 = 2504501) B2504501
theorem B1112627 : Blo 1112627 1112627 := bstep (se 1 (by rfl) ⟨834470, by rfl⟩ : syracuseStep 1112627 = 1668941) B1668941
theorem B1669697 : Blo 1112627 1669697 := bstep (se 2 (by rfl) ⟨626136, by rfl⟩ : syracuseStep 1669697 = 1252273) B1252273
theorem B1112643 : Blo 1112627 1112643 := bstep (se 1 (by rfl) ⟨834482, by rfl⟩ : syracuseStep 1112643 = 1668965) B1668965
theorem B1112659 : Blo 1112627 1112659 := bstep (se 1 (by rfl) ⟨834494, by rfl⟩ : syracuseStep 1112659 = 1668989) B1668989
theorem B1669715 : Blo 1112627 1669715 := bstep (se 1 (by rfl) ⟨1252286, by rfl⟩ : syracuseStep 1669715 = 2504573) B2504573
theorem B1505875 : Blo 1112627 1505875 := bstep (se 1 (by rfl) ⟨1129406, by rfl⟩ : syracuseStep 1505875 = 2258813) B2258813
theorem B1112675 : Blo 1112627 1112675 := bstep (se 1 (by rfl) ⟨834506, by rfl⟩ : syracuseStep 1112675 = 1669013) B1669013
theorem B1505891 : Blo 1112627 1505891 := bstep (se 1 (by rfl) ⟨1129418, by rfl⟩ : syracuseStep 1505891 = 2258837) B2258837
theorem B1669745 : Blo 1112627 1669745 := bstep (se 2 (by rfl) ⟨626154, by rfl⟩ : syracuseStep 1669745 = 1252309) B1252309
theorem B3177073 : Blo 1112627 3177073 := bstep (se 2 (by rfl) ⟨1191402, by rfl⟩ : syracuseStep 3177073 = 2382805) B2382805
theorem B1112691 : Blo 1112627 1112691 := bstep (se 1 (by rfl) ⟨834518, by rfl⟩ : syracuseStep 1112691 = 1669037) B1669037
theorem B1112707 : Blo 1112627 1112707 := bstep (se 1 (by rfl) ⟨834530, by rfl⟩ : syracuseStep 1112707 = 1669061) B1669061
theorem B1669763 : Blo 1112627 1669763 := bstep (se 1 (by rfl) ⟨1252322, by rfl⟩ : syracuseStep 1669763 = 2504645) B2504645
theorem B1112723 : Blo 1112627 1112723 := bstep (se 1 (by rfl) ⟨834542, by rfl⟩ : syracuseStep 1112723 = 1669085) B1669085
theorem B1669793 : Blo 1112627 1669793 := bstep (se 2 (by rfl) ⟨626172, by rfl⟩ : syracuseStep 1669793 = 1252345) B1252345
theorem B1112739 : Blo 1112627 1112739 := bstep (se 1 (by rfl) ⟨834554, by rfl⟩ : syracuseStep 1112739 = 1669109) B1669109
theorem B1112755 : Blo 1112627 1112755 := bstep (se 1 (by rfl) ⟨834566, by rfl⟩ : syracuseStep 1112755 = 1669133) B1669133
theorem B1669811 : Blo 1112627 1669811 := bstep (se 1 (by rfl) ⟨1252358, by rfl⟩ : syracuseStep 1669811 = 2504717) B2504717
theorem B1112771 : Blo 1112627 1112771 := bstep (se 1 (by rfl) ⟨834578, by rfl⟩ : syracuseStep 1112771 = 1669157) B1669157
theorem B1669841 : Blo 1112627 1669841 := bstep (se 2 (by rfl) ⟨626190, by rfl⟩ : syracuseStep 1669841 = 1252381) B1252381
theorem B1112787 : Blo 1112627 1112787 := bstep (se 1 (by rfl) ⟨834590, by rfl⟩ : syracuseStep 1112787 = 1669181) B1669181
theorem B1112803 : Blo 1112627 1112803 := bstep (se 1 (by rfl) ⟨834602, by rfl⟩ : syracuseStep 1112803 = 1669205) B1669205
theorem B1669859 : Blo 1112627 1669859 := bstep (se 1 (by rfl) ⟨1252394, by rfl⟩ : syracuseStep 1669859 = 2504789) B2504789
theorem B1112819 : Blo 1112627 1112819 := bstep (se 1 (by rfl) ⟨834614, by rfl⟩ : syracuseStep 1112819 = 1669229) B1669229
theorem B1669889 : Blo 1112627 1669889 := bstep (se 2 (by rfl) ⟨626208, by rfl⟩ : syracuseStep 1669889 = 1252417) B1252417
theorem B1112835 : Blo 1112627 1112835 := bstep (se 1 (by rfl) ⟨834626, by rfl⟩ : syracuseStep 1112835 = 1669253) B1669253
theorem B1112851 : Blo 1112627 1112851 := bstep (se 1 (by rfl) ⟨834638, by rfl⟩ : syracuseStep 1112851 = 1669277) B1669277
theorem B1669907 : Blo 1112627 1669907 := bstep (se 1 (by rfl) ⟨1252430, by rfl⟩ : syracuseStep 1669907 = 2504861) B2504861
theorem B1112867 : Blo 1112627 1112867 := bstep (se 1 (by rfl) ⟨834650, by rfl⟩ : syracuseStep 1112867 = 1669301) B1669301
theorem B1669937 : Blo 1112627 1669937 := bstep (se 2 (by rfl) ⟨626226, by rfl⟩ : syracuseStep 1669937 = 1252453) B1252453
theorem B1112883 : Blo 1112627 1112883 := bstep (se 1 (by rfl) ⟨834662, by rfl⟩ : syracuseStep 1112883 = 1669325) B1669325
theorem B1112899 : Blo 1112627 1112899 := bstep (se 1 (by rfl) ⟨834674, by rfl⟩ : syracuseStep 1112899 = 1669349) B1669349
theorem B1669955 : Blo 1112627 1669955 := bstep (se 1 (by rfl) ⟨1252466, by rfl⟩ : syracuseStep 1669955 = 2504933) B2504933
theorem B1112915 : Blo 1112627 1112915 := bstep (se 1 (by rfl) ⟨834686, by rfl⟩ : syracuseStep 1112915 = 1669373) B1669373
theorem B1669985 : Blo 1112627 1669985 := bstep (se 2 (by rfl) ⟨626244, by rfl⟩ : syracuseStep 1669985 = 1252489) B1252489
theorem B1112931 : Blo 1112627 1112931 := bstep (se 1 (by rfl) ⟨834698, by rfl⟩ : syracuseStep 1112931 = 1669397) B1669397
theorem B4225891 : Blo 1112627 4225891 := bstep (se 1 (by rfl) ⟨3169418, by rfl⟩ : syracuseStep 4225891 = 6338837) B6338837
theorem B1112947 : Blo 1112627 1112947 := bstep (se 1 (by rfl) ⟨834710, by rfl⟩ : syracuseStep 1112947 = 1669421) B1669421
theorem B1670003 : Blo 1112627 1670003 := bstep (se 1 (by rfl) ⟨1252502, by rfl⟩ : syracuseStep 1670003 = 2505005) B2505005
theorem B1112963 : Blo 1112627 1112963 := bstep (se 1 (by rfl) ⟨834722, by rfl⟩ : syracuseStep 1112963 = 1669445) B1669445
theorem B1670033 : Blo 1112627 1670033 := bstep (se 2 (by rfl) ⟨626262, by rfl⟩ : syracuseStep 1670033 = 1252525) B1252525
theorem B1112979 : Blo 1112627 1112979 := bstep (se 1 (by rfl) ⟨834734, by rfl⟩ : syracuseStep 1112979 = 1669469) B1669469
theorem B1112995 : Blo 1112627 1112995 := bstep (se 1 (by rfl) ⟨834746, by rfl⟩ : syracuseStep 1112995 = 1669493) B1669493
theorem B1670051 : Blo 1112627 1670051 := bstep (se 1 (by rfl) ⟨1252538, by rfl⟩ : syracuseStep 1670051 = 2505077) B2505077
theorem B1113011 : Blo 1112627 1113011 := bstep (se 1 (by rfl) ⟨834758, by rfl⟩ : syracuseStep 1113011 = 1669517) B1669517
theorem B1670081 : Blo 1112627 1670081 := bstep (se 2 (by rfl) ⟨626280, by rfl⟩ : syracuseStep 1670081 = 1252561) B1252561
theorem B1113027 : Blo 1112627 1113027 := bstep (se 1 (by rfl) ⟨834770, by rfl⟩ : syracuseStep 1113027 = 1669541) B1669541
theorem B2816977 : Blo 1112627 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B1113043 : Blo 1112627 1113043 := bstep (se 1 (by rfl) ⟨834782, by rfl⟩ : syracuseStep 1113043 = 1669565) B1669565
theorem B1670099 : Blo 1112627 1670099 := bstep (se 1 (by rfl) ⟨1252574, by rfl⟩ : syracuseStep 1670099 = 2505149) B2505149
theorem B1113059 : Blo 1112627 1113059 := bstep (se 1 (by rfl) ⟨834794, by rfl⟩ : syracuseStep 1113059 = 1669589) B1669589
theorem B1670129 : Blo 1112627 1670129 := bstep (se 2 (by rfl) ⟨626298, by rfl⟩ : syracuseStep 1670129 = 1252597) B1252597
theorem B1113075 : Blo 1112627 1113075 := bstep (se 1 (by rfl) ⟨834806, by rfl⟩ : syracuseStep 1113075 = 1669613) B1669613
theorem B1113091 : Blo 1112627 1113091 := bstep (se 1 (by rfl) ⟨834818, by rfl⟩ : syracuseStep 1113091 = 1669637) B1669637
theorem B1670147 : Blo 1112627 1670147 := bstep (se 1 (by rfl) ⟨1252610, by rfl⟩ : syracuseStep 1670147 = 2505221) B2505221
theorem B3767309 : Blo 1112627 3767309 := bstep (se 3 (by rfl) ⟨706370, by rfl⟩ : syracuseStep 3767309 = 1412741) B1412741
theorem B1113107 : Blo 1112627 1113107 := bstep (se 1 (by rfl) ⟨834830, by rfl⟩ : syracuseStep 1113107 = 1669661) B1669661
theorem B1670177 : Blo 1112627 1670177 := bstep (se 2 (by rfl) ⟨626316, by rfl⟩ : syracuseStep 1670177 = 1252633) B1252633
theorem B1113123 : Blo 1112627 1113123 := bstep (se 1 (by rfl) ⟨834842, by rfl⟩ : syracuseStep 1113123 = 1669685) B1669685
theorem B1113139 : Blo 1112627 1113139 := bstep (se 1 (by rfl) ⟨834854, by rfl⟩ : syracuseStep 1113139 = 1669709) B1669709
theorem B1670195 : Blo 1112627 1670195 := bstep (se 1 (by rfl) ⟨1252646, by rfl⟩ : syracuseStep 1670195 = 2505293) B2505293
theorem B1113155 : Blo 1112627 1113155 := bstep (se 1 (by rfl) ⟨834866, by rfl⟩ : syracuseStep 1113155 = 1669733) B1669733
theorem B3767363 : Blo 1112627 3767363 := bstep (se 1 (by rfl) ⟨2825522, by rfl⟩ : syracuseStep 3767363 = 5651045) B5651045
theorem B1670225 : Blo 1112627 1670225 := bstep (se 2 (by rfl) ⟨626334, by rfl⟩ : syracuseStep 1670225 = 1252669) B1252669
theorem B1113171 : Blo 1112627 1113171 := bstep (se 1 (by rfl) ⟨834878, by rfl⟩ : syracuseStep 1113171 = 1669757) B1669757
theorem B1113187 : Blo 1112627 1113187 := bstep (se 1 (by rfl) ⟨834890, by rfl⟩ : syracuseStep 1113187 = 1669781) B1669781
theorem B1670243 : Blo 1112627 1670243 := bstep (se 1 (by rfl) ⟨1252682, by rfl⟩ : syracuseStep 1670243 = 2505365) B2505365
theorem B1113203 : Blo 1112627 1113203 := bstep (se 1 (by rfl) ⟨834902, by rfl⟩ : syracuseStep 1113203 = 1669805) B1669805
theorem B1670273 : Blo 1112627 1670273 := bstep (se 2 (by rfl) ⟨626352, by rfl⟩ : syracuseStep 1670273 = 1252705) B1252705
theorem B1113219 : Blo 1112627 1113219 := bstep (se 1 (by rfl) ⟨834914, by rfl⟩ : syracuseStep 1113219 = 1669829) B1669829
theorem B1113235 : Blo 1112627 1113235 := bstep (se 1 (by rfl) ⟨834926, by rfl⟩ : syracuseStep 1113235 = 1669853) B1669853
theorem B1670291 : Blo 1112627 1670291 := bstep (se 1 (by rfl) ⟨1252718, by rfl⟩ : syracuseStep 1670291 = 2505437) B2505437
theorem B1113251 : Blo 1112627 1113251 := bstep (se 1 (by rfl) ⟨834938, by rfl⟩ : syracuseStep 1113251 = 1669877) B1669877
theorem B6028451 : Blo 1112627 6028451 := bstep (se 1 (by rfl) ⟨4521338, by rfl⟩ : syracuseStep 6028451 = 9042677) B9042677
theorem B7634083 : Blo 1112627 7634083 := bstep (se 1 (by rfl) ⟨5725562, by rfl⟩ : syracuseStep 7634083 = 11451125) B11451125
theorem B1670321 : Blo 1112627 1670321 := bstep (se 2 (by rfl) ⟨626370, by rfl⟩ : syracuseStep 1670321 = 1252741) B1252741
theorem B1113267 : Blo 1112627 1113267 := bstep (se 1 (by rfl) ⟨834950, by rfl⟩ : syracuseStep 1113267 = 1669901) B1669901
theorem B1408195 : Blo 1112627 1408195 := bstep (se 1 (by rfl) ⟨1056146, by rfl⟩ : syracuseStep 1408195 = 2112293) B2112293
theorem B1113283 : Blo 1112627 1113283 := bstep (se 1 (by rfl) ⟨834962, by rfl⟩ : syracuseStep 1113283 = 1669925) B1669925
theorem B1670339 : Blo 1112627 1670339 := bstep (se 1 (by rfl) ⟨1252754, by rfl⟩ : syracuseStep 1670339 = 2505509) B2505509
theorem B1113299 : Blo 1112627 1113299 := bstep (se 1 (by rfl) ⟨834974, by rfl⟩ : syracuseStep 1113299 = 1669949) B1669949
theorem B1670369 : Blo 1112627 1670369 := bstep (se 2 (by rfl) ⟨626388, by rfl⟩ : syracuseStep 1670369 = 1252777) B1252777
theorem B2817251 : Blo 1112627 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B1113315 : Blo 1112627 1113315 := bstep (se 1 (by rfl) ⟨834986, by rfl⟩ : syracuseStep 1113315 = 1669973) B1669973
theorem B1113331 : Blo 1112627 1113331 := bstep (se 1 (by rfl) ⟨834998, by rfl⟩ : syracuseStep 1113331 = 1669997) B1669997
theorem B1670387 : Blo 1112627 1670387 := bstep (se 1 (by rfl) ⟨1252790, by rfl⟩ : syracuseStep 1670387 = 2505581) B2505581
theorem B1113347 : Blo 1112627 1113347 := bstep (se 1 (by rfl) ⟨835010, by rfl⟩ : syracuseStep 1113347 = 1670021) B1670021
theorem B1670417 : Blo 1112627 1670417 := bstep (se 2 (by rfl) ⟨626406, by rfl⟩ : syracuseStep 1670417 = 1252813) B1252813
theorem B1113363 : Blo 1112627 1113363 := bstep (se 1 (by rfl) ⟨835022, by rfl⟩ : syracuseStep 1113363 = 1670045) B1670045
theorem B1113379 : Blo 1112627 1113379 := bstep (se 1 (by rfl) ⟨835034, by rfl⟩ : syracuseStep 1113379 = 1670069) B1670069
theorem B1670435 : Blo 1112627 1670435 := bstep (se 1 (by rfl) ⟨1252826, by rfl⟩ : syracuseStep 1670435 = 2505653) B2505653
theorem B3570979 : Blo 1112627 3570979 := bstep (se 1 (by rfl) ⟨2678234, by rfl⟩ : syracuseStep 3570979 = 5356469) B5356469
theorem B1113395 : Blo 1112627 1113395 := bstep (se 1 (by rfl) ⟨835046, by rfl⟩ : syracuseStep 1113395 = 1670093) B1670093
theorem B1670465 : Blo 1112627 1670465 := bstep (se 2 (by rfl) ⟨626424, by rfl⟩ : syracuseStep 1670465 = 1252849) B1252849
theorem B1113411 : Blo 1112627 1113411 := bstep (se 1 (by rfl) ⟨835058, by rfl⟩ : syracuseStep 1113411 = 1670117) B1670117
theorem B3767633 : Blo 1112627 3767633 := bstep (se 2 (by rfl) ⟨1412862, by rfl⟩ : syracuseStep 3767633 = 2825725) B2825725
theorem B1113427 : Blo 1112627 1113427 := bstep (se 1 (by rfl) ⟨835070, by rfl⟩ : syracuseStep 1113427 = 1670141) B1670141
theorem B1670483 : Blo 1112627 1670483 := bstep (se 1 (by rfl) ⟨1252862, by rfl⟩ : syracuseStep 1670483 = 2505725) B2505725
theorem B1113443 : Blo 1112627 1113443 := bstep (se 1 (by rfl) ⟨835082, by rfl⟩ : syracuseStep 1113443 = 1670165) B1670165
theorem B1670513 : Blo 1112627 1670513 := bstep (se 2 (by rfl) ⟨626442, by rfl⟩ : syracuseStep 1670513 = 1252885) B1252885
theorem B1113459 : Blo 1112627 1113459 := bstep (se 1 (by rfl) ⟨835094, by rfl⟩ : syracuseStep 1113459 = 1670189) B1670189
theorem B1113475 : Blo 1112627 1113475 := bstep (se 1 (by rfl) ⟨835106, by rfl⟩ : syracuseStep 1113475 = 1670213) B1670213
theorem B1670531 : Blo 1112627 1670531 := bstep (se 1 (by rfl) ⟨1252898, by rfl⟩ : syracuseStep 1670531 = 2505797) B2505797
theorem B1113491 : Blo 1112627 1113491 := bstep (se 1 (by rfl) ⟨835118, by rfl⟩ : syracuseStep 1113491 = 1670237) B1670237
theorem B1670561 : Blo 1112627 1670561 := bstep (se 2 (by rfl) ⟨626460, by rfl⟩ : syracuseStep 1670561 = 1252921) B1252921
theorem B2817443 : Blo 1112627 2817443 := bstep (se 1 (by rfl) ⟨2113082, by rfl⟩ : syracuseStep 2817443 = 4226165) B4226165
theorem B1113507 : Blo 1112627 1113507 := bstep (se 1 (by rfl) ⟨835130, by rfl⟩ : syracuseStep 1113507 = 1670261) B1670261
theorem B3571121 : Blo 1112627 3571121 := bstep (se 2 (by rfl) ⟨1339170, by rfl⟩ : syracuseStep 3571121 = 2678341) B2678341
theorem B1113523 : Blo 1112627 1113523 := bstep (se 1 (by rfl) ⟨835142, by rfl⟩ : syracuseStep 1113523 = 1670285) B1670285
theorem B1670579 : Blo 1112627 1670579 := bstep (se 1 (by rfl) ⟨1252934, by rfl⟩ : syracuseStep 1670579 = 2505869) B2505869
theorem B1113539 : Blo 1112627 1113539 := bstep (se 1 (by rfl) ⟨835154, by rfl⟩ : syracuseStep 1113539 = 1670309) B1670309
theorem B1670609 : Blo 1112627 1670609 := bstep (se 2 (by rfl) ⟨626478, by rfl⟩ : syracuseStep 1670609 = 1252957) B1252957
theorem B1113555 : Blo 1112627 1113555 := bstep (se 1 (by rfl) ⟨835166, by rfl⟩ : syracuseStep 1113555 = 1670333) B1670333
theorem B1113571 : Blo 1112627 1113571 := bstep (se 1 (by rfl) ⟨835178, by rfl⟩ : syracuseStep 1113571 = 1670357) B1670357
theorem B1670627 : Blo 1112627 1670627 := bstep (se 1 (by rfl) ⟨1252970, by rfl⟩ : syracuseStep 1670627 = 2505941) B2505941
theorem B1113587 : Blo 1112627 1113587 := bstep (se 1 (by rfl) ⟨835190, by rfl⟩ : syracuseStep 1113587 = 1670381) B1670381
theorem B1670657 : Blo 1112627 1670657 := bstep (se 2 (by rfl) ⟨626496, by rfl⟩ : syracuseStep 1670657 = 1252993) B1252993
theorem B1113603 : Blo 1112627 1113603 := bstep (se 1 (by rfl) ⟨835202, by rfl⟩ : syracuseStep 1113603 = 1670405) B1670405
theorem B1113619 : Blo 1112627 1113619 := bstep (se 1 (by rfl) ⟨835214, by rfl⟩ : syracuseStep 1113619 = 1670429) B1670429
theorem B1670675 : Blo 1112627 1670675 := bstep (se 1 (by rfl) ⟨1253006, by rfl⟩ : syracuseStep 1670675 = 2506013) B2506013
theorem B1113635 : Blo 1112627 1113635 := bstep (se 1 (by rfl) ⟨835226, by rfl⟩ : syracuseStep 1113635 = 1670453) B1670453
theorem B6356515 : Blo 1112627 6356515 := bstep (se 1 (by rfl) ⟨4767386, by rfl⟩ : syracuseStep 6356515 = 9534773) B9534773
theorem B1670705 : Blo 1112627 1670705 := bstep (se 2 (by rfl) ⟨626514, by rfl⟩ : syracuseStep 1670705 = 1253029) B1253029
theorem B1113651 : Blo 1112627 1113651 := bstep (se 1 (by rfl) ⟨835238, by rfl⟩ : syracuseStep 1113651 = 1670477) B1670477
theorem B1113667 : Blo 1112627 1113667 := bstep (se 1 (by rfl) ⟨835250, by rfl⟩ : syracuseStep 1113667 = 1670501) B1670501
theorem B1670723 : Blo 1112627 1670723 := bstep (se 1 (by rfl) ⟨1253042, by rfl⟩ : syracuseStep 1670723 = 2506085) B2506085
theorem B1113683 : Blo 1112627 1113683 := bstep (se 1 (by rfl) ⟨835262, by rfl⟩ : syracuseStep 1113683 = 1670525) B1670525
theorem B1670753 : Blo 1112627 1670753 := bstep (se 2 (by rfl) ⟨626532, by rfl⟩ : syracuseStep 1670753 = 1253065) B1253065
theorem B1113699 : Blo 1112627 1113699 := bstep (se 1 (by rfl) ⟨835274, by rfl⟩ : syracuseStep 1113699 = 1670549) B1670549
theorem B1113715 : Blo 1112627 1113715 := bstep (se 1 (by rfl) ⟨835286, by rfl⟩ : syracuseStep 1113715 = 1670573) B1670573
theorem B1670771 : Blo 1112627 1670771 := bstep (se 1 (by rfl) ⟨1253078, by rfl⟩ : syracuseStep 1670771 = 2506157) B2506157
theorem B1113731 : Blo 1112627 1113731 := bstep (se 1 (by rfl) ⟨835298, by rfl⟩ : syracuseStep 1113731 = 1670597) B1670597
theorem B1670801 : Blo 1112627 1670801 := bstep (se 2 (by rfl) ⟨626550, by rfl⟩ : syracuseStep 1670801 = 1253101) B1253101
theorem B1506961 : Blo 1112627 1506961 := bstep (se 2 (by rfl) ⟨565110, by rfl⟩ : syracuseStep 1506961 = 1130221) B1130221
theorem B1113747 : Blo 1112627 1113747 := bstep (se 1 (by rfl) ⟨835310, by rfl⟩ : syracuseStep 1113747 = 1670621) B1670621
theorem B1113763 : Blo 1112627 1113763 := bstep (se 1 (by rfl) ⟨835322, by rfl⟩ : syracuseStep 1113763 = 1670645) B1670645
theorem B1670819 : Blo 1112627 1670819 := bstep (se 1 (by rfl) ⟨1253114, by rfl⟩ : syracuseStep 1670819 = 2506229) B2506229
theorem B1408691 : Blo 1112627 1408691 := bstep (se 1 (by rfl) ⟨1056518, by rfl⟩ : syracuseStep 1408691 = 2113037) B2113037
theorem B1113779 : Blo 1112627 1113779 := bstep (se 1 (by rfl) ⟨835334, by rfl⟩ : syracuseStep 1113779 = 1670669) B1670669
theorem B1670849 : Blo 1112627 1670849 := bstep (se 2 (by rfl) ⟨626568, by rfl⟩ : syracuseStep 1670849 = 1253137) B1253137
theorem B1113795 : Blo 1112627 1113795 := bstep (se 1 (by rfl) ⟨835346, by rfl⟩ : syracuseStep 1113795 = 1670693) B1670693
theorem B1113811 : Blo 1112627 1113811 := bstep (se 1 (by rfl) ⟨835358, by rfl⟩ : syracuseStep 1113811 = 1670717) B1670717
theorem B1670867 : Blo 1112627 1670867 := bstep (se 1 (by rfl) ⟨1253150, by rfl⟩ : syracuseStep 1670867 = 2506301) B2506301
theorem B1113827 : Blo 1112627 1113827 := bstep (se 1 (by rfl) ⟨835370, by rfl⟩ : syracuseStep 1113827 = 1670741) B1670741
theorem B1670897 : Blo 1112627 1670897 := bstep (se 2 (by rfl) ⟨626586, by rfl⟩ : syracuseStep 1670897 = 1253173) B1253173
theorem B14286577 : Blo 1112627 14286577 := bstep (se 2 (by rfl) ⟨5357466, by rfl⟩ : syracuseStep 14286577 = 10714933) B10714933
theorem B1113843 : Blo 1112627 1113843 := bstep (se 1 (by rfl) ⟨835382, by rfl⟩ : syracuseStep 1113843 = 1670765) B1670765
theorem B1113859 : Blo 1112627 1113859 := bstep (se 1 (by rfl) ⟨835394, by rfl⟩ : syracuseStep 1113859 = 1670789) B1670789
theorem B1670915 : Blo 1112627 1670915 := bstep (se 1 (by rfl) ⟨1253186, by rfl⟩ : syracuseStep 1670915 = 2506373) B2506373
theorem B1113875 : Blo 1112627 1113875 := bstep (se 1 (by rfl) ⟨835406, by rfl⟩ : syracuseStep 1113875 = 1670813) B1670813
theorem B1507091 : Blo 1112627 1507091 := bstep (se 1 (by rfl) ⟨1130318, by rfl⟩ : syracuseStep 1507091 = 2260637) B2260637
theorem B1670945 : Blo 1112627 1670945 := bstep (se 2 (by rfl) ⟨626604, by rfl⟩ : syracuseStep 1670945 = 1253209) B1253209
theorem B1113891 : Blo 1112627 1113891 := bstep (se 1 (by rfl) ⟨835418, by rfl⟩ : syracuseStep 1113891 = 1670837) B1670837
theorem B1113907 : Blo 1112627 1113907 := bstep (se 1 (by rfl) ⟨835430, by rfl⟩ : syracuseStep 1113907 = 1670861) B1670861
theorem B1670963 : Blo 1112627 1670963 := bstep (se 1 (by rfl) ⟨1253222, by rfl⟩ : syracuseStep 1670963 = 2506445) B2506445
theorem B1113923 : Blo 1112627 1113923 := bstep (se 1 (by rfl) ⟨835442, by rfl⟩ : syracuseStep 1113923 = 1670885) B1670885
theorem B1670993 : Blo 1112627 1670993 := bstep (se 2 (by rfl) ⟨626622, by rfl⟩ : syracuseStep 1670993 = 1253245) B1253245
theorem B1113939 : Blo 1112627 1113939 := bstep (se 1 (by rfl) ⟨835454, by rfl⟩ : syracuseStep 1113939 = 1670909) B1670909
theorem B1113955 : Blo 1112627 1113955 := bstep (se 1 (by rfl) ⟨835466, by rfl⟩ : syracuseStep 1113955 = 1670933) B1670933
theorem B1671011 : Blo 1112627 1671011 := bstep (se 1 (by rfl) ⟨1253258, by rfl⟩ : syracuseStep 1671011 = 2506517) B2506517
theorem B3178349 : Blo 1112627 3178349 := bstep (se 3 (by rfl) ⟨595940, by rfl⟩ : syracuseStep 3178349 = 1191881) B1191881
theorem B3768173 : Blo 1112627 3768173 := bstep (se 3 (by rfl) ⟨706532, by rfl⟩ : syracuseStep 3768173 = 1413065) B1413065
theorem B1113971 : Blo 1112627 1113971 := bstep (se 1 (by rfl) ⟨835478, by rfl⟩ : syracuseStep 1113971 = 1670957) B1670957
theorem B1671041 : Blo 1112627 1671041 := bstep (se 2 (by rfl) ⟨626640, by rfl⟩ : syracuseStep 1671041 = 1253281) B1253281
theorem B1113987 : Blo 1112627 1113987 := bstep (se 1 (by rfl) ⟨835490, by rfl⟩ : syracuseStep 1113987 = 1670981) B1670981
theorem B1114003 : Blo 1112627 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B1671059 : Blo 1112627 1671059 := bstep (se 1 (by rfl) ⟨1253294, by rfl⟩ : syracuseStep 1671059 = 2506589) B2506589
theorem B1114019 : Blo 1112627 1114019 := bstep (se 1 (by rfl) ⟨835514, by rfl⟩ : syracuseStep 1114019 = 1671029) B1671029
theorem B3768227 : Blo 1112627 3768227 := bstep (se 1 (by rfl) ⟨2826170, by rfl⟩ : syracuseStep 3768227 = 5652341) B5652341
theorem B1671089 : Blo 1112627 1671089 := bstep (se 2 (by rfl) ⟨626658, by rfl⟩ : syracuseStep 1671089 = 1253317) B1253317
theorem B1114035 : Blo 1112627 1114035 := bstep (se 1 (by rfl) ⟨835526, by rfl⟩ : syracuseStep 1114035 = 1671053) B1671053
theorem B1114051 : Blo 1112627 1114051 := bstep (se 1 (by rfl) ⟨835538, by rfl⟩ : syracuseStep 1114051 = 1671077) B1671077
theorem B1671107 : Blo 1112627 1671107 := bstep (se 1 (by rfl) ⟨1253330, by rfl⟩ : syracuseStep 1671107 = 2506661) B2506661
theorem B1114067 : Blo 1112627 1114067 := bstep (se 1 (by rfl) ⟨835550, by rfl⟩ : syracuseStep 1114067 = 1671101) B1671101
theorem B1671137 : Blo 1112627 1671137 := bstep (se 2 (by rfl) ⟨626676, by rfl⟩ : syracuseStep 1671137 = 1253353) B1253353
theorem B1114083 : Blo 1112627 1114083 := bstep (se 1 (by rfl) ⟨835562, by rfl⟩ : syracuseStep 1114083 = 1671125) B1671125
theorem B1114099 : Blo 1112627 1114099 := bstep (se 1 (by rfl) ⟨835574, by rfl⟩ : syracuseStep 1114099 = 1671149) B1671149
theorem B1671155 : Blo 1112627 1671155 := bstep (se 1 (by rfl) ⟨1253366, by rfl⟩ : syracuseStep 1671155 = 2506733) B2506733
theorem B1671179 : Blo 1112627 1671179 := bstep (se 1 (by rfl) ⟨1253384, by rfl⟩ : syracuseStep 1671179 = 2506769) B2506769
theorem B1114123 : Blo 1112627 1114123 := bstep (se 1 (by rfl) ⟨835592, by rfl⟩ : syracuseStep 1114123 = 1671185) B1671185
theorem B1671191 : Blo 1112627 1671191 := bstep (se 1 (by rfl) ⟨1253393, by rfl⟩ : syracuseStep 1671191 = 2506787) B2506787
theorem B1114135 : Blo 1112627 1114135 := bstep (se 1 (by rfl) ⟨835601, by rfl⟩ : syracuseStep 1114135 = 1671203) B1671203
theorem B1114155 : Blo 1112627 1114155 := bstep (se 1 (by rfl) ⟨835616, by rfl⟩ : syracuseStep 1114155 = 1671233) B1671233
theorem B5636141 : Blo 1112627 5636141 := bstep (se 3 (by rfl) ⟨1056776, by rfl⟩ : syracuseStep 5636141 = 2113553) B2113553
theorem B1114167 : Blo 1112627 1114167 := bstep (se 1 (by rfl) ⟨835625, by rfl⟩ : syracuseStep 1114167 = 1671251) B1671251
theorem B4227137 : Blo 1112627 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B1114187 : Blo 1112627 1114187 := bstep (se 1 (by rfl) ⟨835640, by rfl⟩ : syracuseStep 1114187 = 1671281) B1671281
theorem B1114199 : Blo 1112627 1114199 := bstep (se 1 (by rfl) ⟨835649, by rfl⟩ : syracuseStep 1114199 = 1671299) B1671299
theorem B1671257 : Blo 1112627 1671257 := bstep (se 2 (by rfl) ⟨626721, by rfl⟩ : syracuseStep 1671257 = 1253443) B1253443
theorem B5079133 : Blo 1112627 5079133 := bstep (se 3 (by rfl) ⟨952337, by rfl⟩ : syracuseStep 5079133 = 1904675) B1904675
theorem B14286941 : Blo 1112627 14286941 := bstep (se 3 (by rfl) ⟨2678801, by rfl⟩ : syracuseStep 14286941 = 5357603) B5357603
theorem B9175133 : Blo 1112627 9175133 := bstep (se 3 (by rfl) ⟨1720337, by rfl⟩ : syracuseStep 9175133 = 3440675) B3440675
theorem B1114219 : Blo 1112627 1114219 := bstep (se 1 (by rfl) ⟨835664, by rfl⟩ : syracuseStep 1114219 = 1671329) B1671329
theorem B1114231 : Blo 1112627 1114231 := bstep (se 1 (by rfl) ⟨835673, by rfl⟩ : syracuseStep 1114231 = 1671347) B1671347
theorem B1114251 : Blo 1112627 1114251 := bstep (se 1 (by rfl) ⟨835688, by rfl⟩ : syracuseStep 1114251 = 1671377) B1671377
theorem B1114263 : Blo 1112627 1114263 := bstep (se 1 (by rfl) ⟨835697, by rfl⟩ : syracuseStep 1114263 = 1671395) B1671395
theorem B1114283 : Blo 1112627 1114283 := bstep (se 1 (by rfl) ⟨835712, by rfl⟩ : syracuseStep 1114283 = 1671425) B1671425
theorem B1114295 : Blo 1112627 1114295 := bstep (se 1 (by rfl) ⟨835721, by rfl⟩ : syracuseStep 1114295 = 1671443) B1671443
theorem B1671371 : Blo 1112627 1671371 := bstep (se 1 (by rfl) ⟨1253528, by rfl⟩ : syracuseStep 1671371 = 2507057) B2507057
theorem B1114315 : Blo 1112627 1114315 := bstep (se 1 (by rfl) ⟨835736, by rfl⟩ : syracuseStep 1114315 = 1671473) B1671473
theorem B1671383 : Blo 1112627 1671383 := bstep (se 1 (by rfl) ⟨1253537, by rfl⟩ : syracuseStep 1671383 = 2507075) B2507075
theorem B1114327 : Blo 1112627 1114327 := bstep (se 1 (by rfl) ⟨835745, by rfl⟩ : syracuseStep 1114327 = 1671491) B1671491
theorem B1114347 : Blo 1112627 1114347 := bstep (se 1 (by rfl) ⟨835760, by rfl⟩ : syracuseStep 1114347 = 1671521) B1671521
theorem B1114359 : Blo 1112627 1114359 := bstep (se 1 (by rfl) ⟨835769, by rfl⟩ : syracuseStep 1114359 = 1671539) B1671539
theorem B1114379 : Blo 1112627 1114379 := bstep (se 1 (by rfl) ⟨835784, by rfl⟩ : syracuseStep 1114379 = 1671569) B1671569
theorem B1114391 : Blo 1112627 1114391 := bstep (se 1 (by rfl) ⟨835793, by rfl⟩ : syracuseStep 1114391 = 1671587) B1671587
theorem B1671449 : Blo 1112627 1671449 := bstep (se 2 (by rfl) ⟨626793, by rfl⟩ : syracuseStep 1671449 = 1253587) B1253587
theorem B1114411 : Blo 1112627 1114411 := bstep (se 1 (by rfl) ⟨835808, by rfl⟩ : syracuseStep 1114411 = 1671617) B1671617
theorem B1114423 : Blo 1112627 1114423 := bstep (se 1 (by rfl) ⟨835817, by rfl⟩ : syracuseStep 1114423 = 1671635) B1671635
theorem B1114443 : Blo 1112627 1114443 := bstep (se 1 (by rfl) ⟨835832, by rfl⟩ : syracuseStep 1114443 = 1671665) B1671665
theorem B1114455 : Blo 1112627 1114455 := bstep (se 1 (by rfl) ⟨835841, by rfl⟩ : syracuseStep 1114455 = 1671683) B1671683
theorem B1114475 : Blo 1112627 1114475 := bstep (se 1 (by rfl) ⟨835856, by rfl⟩ : syracuseStep 1114475 = 1671713) B1671713
theorem B1114487 : Blo 1112627 1114487 := bstep (se 1 (by rfl) ⟨835865, by rfl⟩ : syracuseStep 1114487 = 1671731) B1671731
theorem B1671563 : Blo 1112627 1671563 := bstep (se 1 (by rfl) ⟨1253672, by rfl⟩ : syracuseStep 1671563 = 2507345) B2507345
theorem B1114507 : Blo 1112627 1114507 := bstep (se 1 (by rfl) ⟨835880, by rfl⟩ : syracuseStep 1114507 = 1671761) B1671761
theorem B1671575 : Blo 1112627 1671575 := bstep (se 1 (by rfl) ⟨1253681, by rfl⟩ : syracuseStep 1671575 = 2507363) B2507363
theorem B1114519 : Blo 1112627 1114519 := bstep (se 1 (by rfl) ⟨835889, by rfl⟩ : syracuseStep 1114519 = 1671779) B1671779
theorem B1114539 : Blo 1112627 1114539 := bstep (se 1 (by rfl) ⟨835904, by rfl⟩ : syracuseStep 1114539 = 1671809) B1671809
theorem B1114551 : Blo 1112627 1114551 := bstep (se 1 (by rfl) ⟨835913, by rfl⟩ : syracuseStep 1114551 = 1671827) B1671827
theorem B1114571 : Blo 1112627 1114571 := bstep (se 1 (by rfl) ⟨835928, by rfl⟩ : syracuseStep 1114571 = 1671857) B1671857
theorem B1114583 : Blo 1112627 1114583 := bstep (se 1 (by rfl) ⟨835937, by rfl⟩ : syracuseStep 1114583 = 1671875) B1671875
theorem B1671641 : Blo 1112627 1671641 := bstep (se 2 (by rfl) ⟨626865, by rfl⟩ : syracuseStep 1671641 = 1253731) B1253731
theorem B1114603 : Blo 1112627 1114603 := bstep (se 1 (by rfl) ⟨835952, by rfl⟩ : syracuseStep 1114603 = 1671905) B1671905
theorem B1114615 : Blo 1112627 1114615 := bstep (se 1 (by rfl) ⟨835961, by rfl⟩ : syracuseStep 1114615 = 1671923) B1671923
theorem B1114635 : Blo 1112627 1114635 := bstep (se 1 (by rfl) ⟨835976, by rfl⟩ : syracuseStep 1114635 = 1671953) B1671953
theorem B1114647 : Blo 1112627 1114647 := bstep (se 1 (by rfl) ⟨835985, by rfl⟩ : syracuseStep 1114647 = 1671971) B1671971
theorem B1114667 : Blo 1112627 1114667 := bstep (se 1 (by rfl) ⟨836000, by rfl⟩ : syracuseStep 1114667 = 1672001) B1672001
theorem B1114679 : Blo 1112627 1114679 := bstep (se 1 (by rfl) ⟨836009, by rfl⟩ : syracuseStep 1114679 = 1672019) B1672019
theorem B1671755 : Blo 1112627 1671755 := bstep (se 1 (by rfl) ⟨1253816, by rfl⟩ : syracuseStep 1671755 = 2507633) B2507633
theorem B1114699 : Blo 1112627 1114699 := bstep (se 1 (by rfl) ⟨836024, by rfl⟩ : syracuseStep 1114699 = 1672049) B1672049
theorem B1671767 : Blo 1112627 1671767 := bstep (se 1 (by rfl) ⟨1253825, by rfl⟩ : syracuseStep 1671767 = 2507651) B2507651
theorem B1114711 : Blo 1112627 1114711 := bstep (se 1 (by rfl) ⟨836033, by rfl⟩ : syracuseStep 1114711 = 1672067) B1672067
theorem B3179101 : Blo 1112627 3179101 := bstep (se 3 (by rfl) ⟨596081, by rfl⟩ : syracuseStep 3179101 = 1192163) B1192163
theorem B1114731 : Blo 1112627 1114731 := bstep (se 1 (by rfl) ⟨836048, by rfl⟩ : syracuseStep 1114731 = 1672097) B1672097
theorem B1114743 : Blo 1112627 1114743 := bstep (se 1 (by rfl) ⟨836057, by rfl⟩ : syracuseStep 1114743 = 1672115) B1672115
theorem B1114763 : Blo 1112627 1114763 := bstep (se 1 (by rfl) ⟨836072, by rfl⟩ : syracuseStep 1114763 = 1672145) B1672145
theorem B1114775 : Blo 1112627 1114775 := bstep (se 1 (by rfl) ⟨836081, by rfl⟩ : syracuseStep 1114775 = 1672163) B1672163
theorem B3179159 : Blo 1112627 3179159 := bstep (se 1 (by rfl) ⟨2384369, by rfl⟩ : syracuseStep 3179159 = 4768739) B4768739
theorem B1671833 : Blo 1112627 1671833 := bstep (se 2 (by rfl) ⟨626937, by rfl⟩ : syracuseStep 1671833 = 1253875) B1253875
theorem B1114795 : Blo 1112627 1114795 := bstep (se 1 (by rfl) ⟨836096, by rfl⟩ : syracuseStep 1114795 = 1672193) B1672193
theorem B2818739 : Blo 1112627 2818739 := bstep (se 1 (by rfl) ⟨2114054, by rfl⟩ : syracuseStep 2818739 = 4228109) B4228109
theorem B1114807 : Blo 1112627 1114807 := bstep (se 1 (by rfl) ⟨836105, by rfl⟩ : syracuseStep 1114807 = 1672211) B1672211
theorem B1114827 : Blo 1112627 1114827 := bstep (se 1 (by rfl) ⟨836120, by rfl⟩ : syracuseStep 1114827 = 1672241) B1672241
theorem B1114839 : Blo 1112627 1114839 := bstep (se 1 (by rfl) ⟨836129, by rfl⟩ : syracuseStep 1114839 = 1672259) B1672259
theorem B1114859 : Blo 1112627 1114859 := bstep (se 1 (by rfl) ⟨836144, by rfl⟩ : syracuseStep 1114859 = 1672289) B1672289
theorem B1114871 : Blo 1112627 1114871 := bstep (se 1 (by rfl) ⟨836153, by rfl⟩ : syracuseStep 1114871 = 1672307) B1672307
theorem B1671947 : Blo 1112627 1671947 := bstep (se 1 (by rfl) ⟨1253960, by rfl⟩ : syracuseStep 1671947 = 2507921) B2507921
theorem B1114891 : Blo 1112627 1114891 := bstep (se 1 (by rfl) ⟨836168, by rfl⟩ : syracuseStep 1114891 = 1672337) B1672337
theorem B1409815 : Blo 1112627 1409815 := bstep (se 1 (by rfl) ⟨1057361, by rfl⟩ : syracuseStep 1409815 = 2114723) B2114723
theorem B1671959 : Blo 1112627 1671959 := bstep (se 1 (by rfl) ⟨1253969, by rfl⟩ : syracuseStep 1671959 = 2507939) B2507939
theorem B1114903 : Blo 1112627 1114903 := bstep (se 1 (by rfl) ⟨836177, by rfl⟩ : syracuseStep 1114903 = 1672355) B1672355
theorem B1114923 : Blo 1112627 1114923 := bstep (se 1 (by rfl) ⟨836192, by rfl⟩ : syracuseStep 1114923 = 1672385) B1672385
theorem B1114935 : Blo 1112627 1114935 := bstep (se 1 (by rfl) ⟨836201, by rfl⟩ : syracuseStep 1114935 = 1672403) B1672403
theorem B1114955 : Blo 1112627 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B1114967 : Blo 1112627 1114967 := bstep (se 1 (by rfl) ⟨836225, by rfl⟩ : syracuseStep 1114967 = 1672451) B1672451
theorem B1672025 : Blo 1112627 1672025 := bstep (se 2 (by rfl) ⟨627009, by rfl⟩ : syracuseStep 1672025 = 1254019) B1254019
theorem B1114987 : Blo 1112627 1114987 := bstep (se 1 (by rfl) ⟨836240, by rfl⟩ : syracuseStep 1114987 = 1672481) B1672481
theorem B1114999 : Blo 1112627 1114999 := bstep (se 1 (by rfl) ⟨836249, by rfl⟩ : syracuseStep 1114999 = 1672499) B1672499
theorem B1115019 : Blo 1112627 1115019 := bstep (se 1 (by rfl) ⟨836264, by rfl⟩ : syracuseStep 1115019 = 1672529) B1672529
theorem B1115031 : Blo 1112627 1115031 := bstep (se 1 (by rfl) ⟨836273, by rfl⟩ : syracuseStep 1115031 = 1672547) B1672547
theorem B1115051 : Blo 1112627 1115051 := bstep (se 1 (by rfl) ⟨836288, by rfl⟩ : syracuseStep 1115051 = 1672577) B1672577
theorem B1115063 : Blo 1112627 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B1672139 : Blo 1112627 1672139 := bstep (se 1 (by rfl) ⟨1254104, by rfl⟩ : syracuseStep 1672139 = 2508209) B2508209
theorem B1115083 : Blo 1112627 1115083 := bstep (se 1 (by rfl) ⟨836312, by rfl⟩ : syracuseStep 1115083 = 1672625) B1672625
theorem B1672151 : Blo 1112627 1672151 := bstep (se 1 (by rfl) ⟨1254113, by rfl⟩ : syracuseStep 1672151 = 2508227) B2508227
theorem B1115095 : Blo 1112627 1115095 := bstep (se 1 (by rfl) ⟨836321, by rfl⟩ : syracuseStep 1115095 = 1672643) B1672643
theorem B2819033 : Blo 1112627 2819033 := bstep (se 2 (by rfl) ⟨1057137, by rfl⟩ : syracuseStep 2819033 = 2114275) B2114275
theorem B1115115 : Blo 1112627 1115115 := bstep (se 1 (by rfl) ⟨836336, by rfl⟩ : syracuseStep 1115115 = 1672673) B1672673
theorem B1115127 : Blo 1112627 1115127 := bstep (se 1 (by rfl) ⟨836345, by rfl⟩ : syracuseStep 1115127 = 1672691) B1672691
theorem B1115147 : Blo 1112627 1115147 := bstep (se 1 (by rfl) ⟨836360, by rfl⟩ : syracuseStep 1115147 = 1672721) B1672721
theorem B1115159 : Blo 1112627 1115159 := bstep (se 1 (by rfl) ⟨836369, by rfl⟩ : syracuseStep 1115159 = 1672739) B1672739
theorem B1672217 : Blo 1112627 1672217 := bstep (se 2 (by rfl) ⟨627081, by rfl⟩ : syracuseStep 1672217 = 1254163) B1254163
theorem B10159139 : Blo 1112627 10159139 := bstep (se 1 (by rfl) ⟨7619354, by rfl⟩ : syracuseStep 10159139 = 15238709) B15238709
theorem B1115179 : Blo 1112627 1115179 := bstep (se 1 (by rfl) ⟨836384, by rfl⟩ : syracuseStep 1115179 = 1672769) B1672769
theorem B1115191 : Blo 1112627 1115191 := bstep (se 1 (by rfl) ⟨836393, by rfl⟩ : syracuseStep 1115191 = 1672787) B1672787
theorem B1115211 : Blo 1112627 1115211 := bstep (se 1 (by rfl) ⟨836408, by rfl⟩ : syracuseStep 1115211 = 1672817) B1672817
theorem B1115223 : Blo 1112627 1115223 := bstep (se 1 (by rfl) ⟨836417, by rfl⟩ : syracuseStep 1115223 = 1672835) B1672835
theorem B1115243 : Blo 1112627 1115243 := bstep (se 1 (by rfl) ⟨836432, by rfl⟩ : syracuseStep 1115243 = 1672865) B1672865
theorem B1115255 : Blo 1112627 1115255 := bstep (se 1 (by rfl) ⟨836441, by rfl⟩ : syracuseStep 1115255 = 1672883) B1672883
theorem B1672331 : Blo 1112627 1672331 := bstep (se 1 (by rfl) ⟨1254248, by rfl⟩ : syracuseStep 1672331 = 2508497) B2508497
theorem B1115275 : Blo 1112627 1115275 := bstep (se 1 (by rfl) ⟨836456, by rfl⟩ : syracuseStep 1115275 = 1672913) B1672913
theorem B1672343 : Blo 1112627 1672343 := bstep (se 1 (by rfl) ⟨1254257, by rfl⟩ : syracuseStep 1672343 = 2508515) B2508515
theorem B1115287 : Blo 1112627 1115287 := bstep (se 1 (by rfl) ⟨836465, by rfl⟩ : syracuseStep 1115287 = 1672931) B1672931
theorem B1115307 : Blo 1112627 1115307 := bstep (se 1 (by rfl) ⟨836480, by rfl⟩ : syracuseStep 1115307 = 1672961) B1672961
theorem B1115319 : Blo 1112627 1115319 := bstep (se 1 (by rfl) ⟨836489, by rfl⟩ : syracuseStep 1115319 = 1672979) B1672979
theorem B1115339 : Blo 1112627 1115339 := bstep (se 1 (by rfl) ⟨836504, by rfl⟩ : syracuseStep 1115339 = 1673009) B1673009
theorem B1115351 : Blo 1112627 1115351 := bstep (se 1 (by rfl) ⟨836513, by rfl⟩ : syracuseStep 1115351 = 1673027) B1673027
theorem B1672409 : Blo 1112627 1672409 := bstep (se 2 (by rfl) ⟨627153, by rfl⟩ : syracuseStep 1672409 = 1254307) B1254307
theorem B1115371 : Blo 1112627 1115371 := bstep (se 1 (by rfl) ⟨836528, by rfl⟩ : syracuseStep 1115371 = 1673057) B1673057
theorem B1115383 : Blo 1112627 1115383 := bstep (se 1 (by rfl) ⟨836537, by rfl⟩ : syracuseStep 1115383 = 1673075) B1673075
theorem B1115403 : Blo 1112627 1115403 := bstep (se 1 (by rfl) ⟨836552, by rfl⟩ : syracuseStep 1115403 = 1673105) B1673105
theorem B1115415 : Blo 1112627 1115415 := bstep (se 1 (by rfl) ⟨836561, by rfl⟩ : syracuseStep 1115415 = 1673123) B1673123
theorem B1115435 : Blo 1112627 1115435 := bstep (se 1 (by rfl) ⟨836576, by rfl⟩ : syracuseStep 1115435 = 1673153) B1673153
theorem B1115447 : Blo 1112627 1115447 := bstep (se 1 (by rfl) ⟨836585, by rfl⟩ : syracuseStep 1115447 = 1673171) B1673171
theorem B10159435 : Blo 1112627 10159435 := bstep (se 1 (by rfl) ⟨7619576, by rfl⟩ : syracuseStep 10159435 = 15239153) B15239153
theorem B1672523 : Blo 1112627 1672523 := bstep (se 1 (by rfl) ⟨1254392, by rfl⟩ : syracuseStep 1672523 = 2508785) B2508785
theorem B1115467 : Blo 1112627 1115467 := bstep (se 1 (by rfl) ⟨836600, by rfl⟩ : syracuseStep 1115467 = 1673201) B1673201
theorem B1672535 : Blo 1112627 1672535 := bstep (se 1 (by rfl) ⟨1254401, by rfl⟩ : syracuseStep 1672535 = 2508803) B2508803
theorem B1115479 : Blo 1112627 1115479 := bstep (se 1 (by rfl) ⟨836609, by rfl⟩ : syracuseStep 1115479 = 1673219) B1673219
theorem B1115499 : Blo 1112627 1115499 := bstep (se 1 (by rfl) ⟨836624, by rfl⟩ : syracuseStep 1115499 = 1673249) B1673249
theorem B1115511 : Blo 1112627 1115511 := bstep (se 1 (by rfl) ⟨836633, by rfl⟩ : syracuseStep 1115511 = 1673267) B1673267
theorem B1115531 : Blo 1112627 1115531 := bstep (se 1 (by rfl) ⟨836648, by rfl⟩ : syracuseStep 1115531 = 1673297) B1673297
theorem B1115543 : Blo 1112627 1115543 := bstep (se 1 (by rfl) ⟨836657, by rfl⟩ : syracuseStep 1115543 = 1673315) B1673315
theorem B1672601 : Blo 1112627 1672601 := bstep (se 2 (by rfl) ⟨627225, by rfl⟩ : syracuseStep 1672601 = 1254451) B1254451
theorem B1115563 : Blo 1112627 1115563 := bstep (se 1 (by rfl) ⟨836672, by rfl⟩ : syracuseStep 1115563 = 1673345) B1673345
theorem B1115575 : Blo 1112627 1115575 := bstep (se 1 (by rfl) ⟨836681, by rfl⟩ : syracuseStep 1115575 = 1673363) B1673363
theorem B1115595 : Blo 1112627 1115595 := bstep (se 1 (by rfl) ⟨836696, by rfl⟩ : syracuseStep 1115595 = 1673393) B1673393
theorem B1115607 : Blo 1112627 1115607 := bstep (se 1 (by rfl) ⟨836705, by rfl⟩ : syracuseStep 1115607 = 1673411) B1673411
theorem B3573209 : Blo 1112627 3573209 := bstep (se 2 (by rfl) ⟨1339953, by rfl⟩ : syracuseStep 3573209 = 2679907) B2679907
theorem B1115627 : Blo 1112627 1115627 := bstep (se 1 (by rfl) ⟨836720, by rfl⟩ : syracuseStep 1115627 = 1673441) B1673441
theorem B1115639 : Blo 1112627 1115639 := bstep (se 1 (by rfl) ⟨836729, by rfl⟩ : syracuseStep 1115639 = 1673459) B1673459
theorem B1672715 : Blo 1112627 1672715 := bstep (se 1 (by rfl) ⟨1254536, by rfl⟩ : syracuseStep 1672715 = 2509073) B2509073
theorem B1115659 : Blo 1112627 1115659 := bstep (se 1 (by rfl) ⟨836744, by rfl⟩ : syracuseStep 1115659 = 1673489) B1673489
theorem B4228625 : Blo 1112627 4228625 := bstep (se 2 (by rfl) ⟨1585734, by rfl⟩ : syracuseStep 4228625 = 3171469) B3171469
theorem B1672727 : Blo 1112627 1672727 := bstep (se 1 (by rfl) ⟨1254545, by rfl⟩ : syracuseStep 1672727 = 2509091) B2509091
theorem B1115671 : Blo 1112627 1115671 := bstep (se 1 (by rfl) ⟨836753, by rfl⟩ : syracuseStep 1115671 = 1673507) B1673507
theorem B1115691 : Blo 1112627 1115691 := bstep (se 1 (by rfl) ⟨836768, by rfl⟩ : syracuseStep 1115691 = 1673537) B1673537
theorem B1115703 : Blo 1112627 1115703 := bstep (se 1 (by rfl) ⟨836777, by rfl⟩ : syracuseStep 1115703 = 1673555) B1673555
theorem B1410635 : Blo 1112627 1410635 := bstep (se 1 (by rfl) ⟨1057976, by rfl⟩ : syracuseStep 1410635 = 2115953) B2115953
theorem B1115723 : Blo 1112627 1115723 := bstep (se 1 (by rfl) ⟨836792, by rfl⟩ : syracuseStep 1115723 = 1673585) B1673585
theorem B1115735 : Blo 1112627 1115735 := bstep (se 1 (by rfl) ⟨836801, by rfl⟩ : syracuseStep 1115735 = 1673603) B1673603
theorem B1672793 : Blo 1112627 1672793 := bstep (se 2 (by rfl) ⟨627297, by rfl⟩ : syracuseStep 1672793 = 1254595) B1254595
theorem B11437661 : Blo 1112627 11437661 := bstep (se 3 (by rfl) ⟨2144561, by rfl⟩ : syracuseStep 11437661 = 4289123) B4289123
theorem B1115755 : Blo 1112627 1115755 := bstep (se 1 (by rfl) ⟨836816, by rfl⟩ : syracuseStep 1115755 = 1673633) B1673633
theorem B1115767 : Blo 1112627 1115767 := bstep (se 1 (by rfl) ⟨836825, by rfl⟩ : syracuseStep 1115767 = 1673651) B1673651
theorem B1115787 : Blo 1112627 1115787 := bstep (se 1 (by rfl) ⟨836840, by rfl⟩ : syracuseStep 1115787 = 1673681) B1673681
theorem B7145111 : Blo 1112627 7145111 := bstep (se 1 (by rfl) ⟨5358833, by rfl⟩ : syracuseStep 7145111 = 10717667) B10717667
theorem B1115799 : Blo 1112627 1115799 := bstep (se 1 (by rfl) ⟨836849, by rfl⟩ : syracuseStep 1115799 = 1673699) B1673699
theorem B3016343 : Blo 1112627 3016343 := bstep (se 1 (by rfl) ⟨2262257, by rfl⟩ : syracuseStep 3016343 = 4524515) B4524515
theorem B1115819 : Blo 1112627 1115819 := bstep (se 1 (by rfl) ⟨836864, by rfl⟩ : syracuseStep 1115819 = 1673729) B1673729
theorem B1115831 : Blo 1112627 1115831 := bstep (se 1 (by rfl) ⟨836873, by rfl⟩ : syracuseStep 1115831 = 1673747) B1673747
theorem B1672907 : Blo 1112627 1672907 := bstep (se 1 (by rfl) ⟨1254680, by rfl⟩ : syracuseStep 1672907 = 2509361) B2509361
theorem B1115851 : Blo 1112627 1115851 := bstep (se 1 (by rfl) ⟨836888, by rfl⟩ : syracuseStep 1115851 = 1673777) B1673777
theorem B1672919 : Blo 1112627 1672919 := bstep (se 1 (by rfl) ⟨1254689, by rfl⟩ : syracuseStep 1672919 = 2509379) B2509379
theorem B1115863 : Blo 1112627 1115863 := bstep (se 1 (by rfl) ⟨836897, by rfl⟩ : syracuseStep 1115863 = 1673795) B1673795
theorem B1115883 : Blo 1112627 1115883 := bstep (se 1 (by rfl) ⟨836912, by rfl⟩ : syracuseStep 1115883 = 1673825) B1673825
theorem B1115895 : Blo 1112627 1115895 := bstep (se 1 (by rfl) ⟨836921, by rfl⟩ : syracuseStep 1115895 = 1673843) B1673843
theorem B1115915 : Blo 1112627 1115915 := bstep (se 1 (by rfl) ⟨836936, by rfl⟩ : syracuseStep 1115915 = 1673873) B1673873
theorem B1115927 : Blo 1112627 1115927 := bstep (se 1 (by rfl) ⟨836945, by rfl⟩ : syracuseStep 1115927 = 1673891) B1673891
theorem B1672985 : Blo 1112627 1672985 := bstep (se 2 (by rfl) ⟨627369, by rfl⟩ : syracuseStep 1672985 = 1254739) B1254739
theorem B1115947 : Blo 1112627 1115947 := bstep (se 1 (by rfl) ⟨836960, by rfl⟩ : syracuseStep 1115947 = 1673921) B1673921
theorem B1115959 : Blo 1112627 1115959 := bstep (se 1 (by rfl) ⟨836969, by rfl⟩ : syracuseStep 1115959 = 1673939) B1673939
theorem B1115979 : Blo 1112627 1115979 := bstep (se 1 (by rfl) ⟨836984, by rfl⟩ : syracuseStep 1115979 = 1673969) B1673969
theorem B1115991 : Blo 1112627 1115991 := bstep (se 1 (by rfl) ⟨836993, by rfl⟩ : syracuseStep 1115991 = 1673987) B1673987
theorem B4753241 : Blo 1112627 4753241 := bstep (se 2 (by rfl) ⟨1782465, by rfl⟩ : syracuseStep 4753241 = 3564931) B3564931
theorem B3016541 : Blo 1112627 3016541 := bstep (se 3 (by rfl) ⟨565601, by rfl⟩ : syracuseStep 3016541 = 1131203) B1131203
theorem B1116011 : Blo 1112627 1116011 := bstep (se 1 (by rfl) ⟨837008, by rfl⟩ : syracuseStep 1116011 = 1674017) B1674017
theorem B1116023 : Blo 1112627 1116023 := bstep (se 1 (by rfl) ⟨837017, by rfl⟩ : syracuseStep 1116023 = 1674035) B1674035
theorem B1673099 : Blo 1112627 1673099 := bstep (se 1 (by rfl) ⟨1254824, by rfl⟩ : syracuseStep 1673099 = 2509649) B2509649
theorem B1116043 : Blo 1112627 1116043 := bstep (se 1 (by rfl) ⟨837032, by rfl⟩ : syracuseStep 1116043 = 1674065) B1674065
theorem B1673111 : Blo 1112627 1673111 := bstep (se 1 (by rfl) ⟨1254833, by rfl⟩ : syracuseStep 1673111 = 2509667) B2509667
theorem B1116055 : Blo 1112627 1116055 := bstep (se 1 (by rfl) ⟨837041, by rfl⟩ : syracuseStep 1116055 = 1674083) B1674083
theorem B1116075 : Blo 1112627 1116075 := bstep (se 1 (by rfl) ⟨837056, by rfl⟩ : syracuseStep 1116075 = 1674113) B1674113
theorem B1116087 : Blo 1112627 1116087 := bstep (se 1 (by rfl) ⟨837065, by rfl⟩ : syracuseStep 1116087 = 1674131) B1674131
theorem B1116107 : Blo 1112627 1116107 := bstep (se 1 (by rfl) ⟨837080, by rfl⟩ : syracuseStep 1116107 = 1674161) B1674161
theorem B1116119 : Blo 1112627 1116119 := bstep (se 1 (by rfl) ⟨837089, by rfl⟩ : syracuseStep 1116119 = 1674179) B1674179
theorem B4229081 : Blo 1112627 4229081 := bstep (se 2 (by rfl) ⟨1585905, by rfl⟩ : syracuseStep 4229081 = 3171811) B3171811
theorem B1673177 : Blo 1112627 1673177 := bstep (se 2 (by rfl) ⟨627441, by rfl⟩ : syracuseStep 1673177 = 1254883) B1254883
theorem B1116139 : Blo 1112627 1116139 := bstep (se 1 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 1116139 = 1674209) B1674209
theorem B1116151 : Blo 1112627 1116151 := bstep (se 1 (by rfl) ⟨837113, by rfl⟩ : syracuseStep 1116151 = 1674227) B1674227
theorem B1116171 : Blo 1112627 1116171 := bstep (se 1 (by rfl) ⟨837128, by rfl⟩ : syracuseStep 1116171 = 1674257) B1674257
theorem B1116183 : Blo 1112627 1116183 := bstep (se 1 (by rfl) ⟨837137, by rfl⟩ : syracuseStep 1116183 = 1674275) B1674275
theorem B1116203 : Blo 1112627 1116203 := bstep (se 1 (by rfl) ⟨837152, by rfl⟩ : syracuseStep 1116203 = 1674305) B1674305
theorem B1116215 : Blo 1112627 1116215 := bstep (se 1 (by rfl) ⟨837161, by rfl⟩ : syracuseStep 1116215 = 1674323) B1674323
theorem B1673291 : Blo 1112627 1673291 := bstep (se 1 (by rfl) ⟨1254968, by rfl⟩ : syracuseStep 1673291 = 2509937) B2509937
theorem B1116235 : Blo 1112627 1116235 := bstep (se 1 (by rfl) ⟨837176, by rfl⟩ : syracuseStep 1116235 = 1674353) B1674353
theorem B1673303 : Blo 1112627 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B1116247 : Blo 1112627 1116247 := bstep (se 1 (by rfl) ⟨837185, by rfl⟩ : syracuseStep 1116247 = 1674371) B1674371
theorem B1116267 : Blo 1112627 1116267 := bstep (se 1 (by rfl) ⟨837200, by rfl⟩ : syracuseStep 1116267 = 1674401) B1674401
theorem B1116279 : Blo 1112627 1116279 := bstep (se 1 (by rfl) ⟨837209, by rfl⟩ : syracuseStep 1116279 = 1674419) B1674419
theorem B1116299 : Blo 1112627 1116299 := bstep (se 1 (by rfl) ⟨837224, by rfl⟩ : syracuseStep 1116299 = 1674449) B1674449
theorem B1116311 : Blo 1112627 1116311 := bstep (se 1 (by rfl) ⟨837233, by rfl⟩ : syracuseStep 1116311 = 1674467) B1674467
theorem B1673369 : Blo 1112627 1673369 := bstep (se 2 (by rfl) ⟨627513, by rfl⟩ : syracuseStep 1673369 = 1255027) B1255027
theorem B1116331 : Blo 1112627 1116331 := bstep (se 1 (by rfl) ⟨837248, by rfl⟩ : syracuseStep 1116331 = 1674497) B1674497
theorem B4229293 : Blo 1112627 4229293 := bstep (se 3 (by rfl) ⟨792992, by rfl⟩ : syracuseStep 4229293 = 1585985) B1585985
theorem B1116343 : Blo 1112627 1116343 := bstep (se 1 (by rfl) ⟨837257, by rfl⟩ : syracuseStep 1116343 = 1674515) B1674515
theorem B3573953 : Blo 1112627 3573953 := bstep (se 2 (by rfl) ⟨1340232, by rfl⟩ : syracuseStep 3573953 = 2680465) B2680465
theorem B1116363 : Blo 1112627 1116363 := bstep (se 1 (by rfl) ⟨837272, by rfl⟩ : syracuseStep 1116363 = 1674545) B1674545
theorem B1116375 : Blo 1112627 1116375 := bstep (se 1 (by rfl) ⟨837281, by rfl⟩ : syracuseStep 1116375 = 1674563) B1674563
theorem B1116395 : Blo 1112627 1116395 := bstep (se 1 (by rfl) ⟨837296, by rfl⟩ : syracuseStep 1116395 = 1674593) B1674593
theorem B1116407 : Blo 1112627 1116407 := bstep (se 1 (by rfl) ⟨837305, by rfl⟩ : syracuseStep 1116407 = 1674611) B1674611
theorem B1411339 : Blo 1112627 1411339 := bstep (se 1 (by rfl) ⟨1058504, by rfl⟩ : syracuseStep 1411339 = 2117009) B2117009
theorem B1673483 : Blo 1112627 1673483 := bstep (se 1 (by rfl) ⟨1255112, by rfl⟩ : syracuseStep 1673483 = 2510225) B2510225
theorem B1116427 : Blo 1112627 1116427 := bstep (se 1 (by rfl) ⟨837320, by rfl⟩ : syracuseStep 1116427 = 1674641) B1674641
theorem B1673495 : Blo 1112627 1673495 := bstep (se 1 (by rfl) ⟨1255121, by rfl⟩ : syracuseStep 1673495 = 2510243) B2510243
theorem B1116439 : Blo 1112627 1116439 := bstep (se 1 (by rfl) ⟨837329, by rfl⟩ : syracuseStep 1116439 = 1674659) B1674659
theorem B1116459 : Blo 1112627 1116459 := bstep (se 1 (by rfl) ⟨837344, by rfl⟩ : syracuseStep 1116459 = 1674689) B1674689
theorem B1116471 : Blo 1112627 1116471 := bstep (se 1 (by rfl) ⟨837353, by rfl⟩ : syracuseStep 1116471 = 1674707) B1674707
theorem B1116491 : Blo 1112627 1116491 := bstep (se 1 (by rfl) ⟨837368, by rfl⟩ : syracuseStep 1116491 = 1674737) B1674737
theorem B1116503 : Blo 1112627 1116503 := bstep (se 1 (by rfl) ⟨837377, by rfl⟩ : syracuseStep 1116503 = 1674755) B1674755
theorem B1673561 : Blo 1112627 1673561 := bstep (se 2 (by rfl) ⟨627585, by rfl⟩ : syracuseStep 1673561 = 1255171) B1255171
theorem B1116523 : Blo 1112627 1116523 := bstep (se 1 (by rfl) ⟨837392, by rfl⟩ : syracuseStep 1116523 = 1674785) B1674785
theorem B1116535 : Blo 1112627 1116535 := bstep (se 1 (by rfl) ⟨837401, by rfl⟩ : syracuseStep 1116535 = 1674803) B1674803
theorem B1116555 : Blo 1112627 1116555 := bstep (se 1 (by rfl) ⟨837416, by rfl⟩ : syracuseStep 1116555 = 1674833) B1674833
theorem B1116567 : Blo 1112627 1116567 := bstep (se 1 (by rfl) ⟨837425, by rfl⟩ : syracuseStep 1116567 = 1674851) B1674851
theorem B1116587 : Blo 1112627 1116587 := bstep (se 1 (by rfl) ⟨837440, by rfl⟩ : syracuseStep 1116587 = 1674881) B1674881
theorem B1116599 : Blo 1112627 1116599 := bstep (se 1 (by rfl) ⟨837449, by rfl⟩ : syracuseStep 1116599 = 1674899) B1674899
theorem B1673675 : Blo 1112627 1673675 := bstep (se 1 (by rfl) ⟨1255256, by rfl⟩ : syracuseStep 1673675 = 2510513) B2510513
theorem B1116619 : Blo 1112627 1116619 := bstep (se 1 (by rfl) ⟨837464, by rfl⟩ : syracuseStep 1116619 = 1674929) B1674929
theorem B1673687 : Blo 1112627 1673687 := bstep (se 1 (by rfl) ⟨1255265, by rfl⟩ : syracuseStep 1673687 = 2510531) B2510531
theorem B4229597 : Blo 1112627 4229597 := bstep (se 3 (by rfl) ⟨793049, by rfl⟩ : syracuseStep 4229597 = 1586099) B1586099
theorem B1411607 : Blo 1112627 1411607 := bstep (se 1 (by rfl) ⟨1058705, by rfl⟩ : syracuseStep 1411607 = 2117411) B2117411
theorem B1673753 : Blo 1112627 1673753 := bstep (se 2 (by rfl) ⟨627657, by rfl⟩ : syracuseStep 1673753 = 1255315) B1255315
theorem B2820683 : Blo 1112627 2820683 := bstep (se 1 (by rfl) ⟨2115512, by rfl⟩ : syracuseStep 2820683 = 4231025) B4231025
theorem B12716675 : Blo 1112627 12716675 := bstep (se 1 (by rfl) ⟨9537506, by rfl⟩ : syracuseStep 12716675 = 19075013) B19075013
theorem B1673867 : Blo 1112627 1673867 := bstep (se 1 (by rfl) ⟨1255400, by rfl⟩ : syracuseStep 1673867 = 2510801) B2510801
theorem B1673879 : Blo 1112627 1673879 := bstep (se 1 (by rfl) ⟨1255409, by rfl⟩ : syracuseStep 1673879 = 2510819) B2510819
theorem B8030897 : Blo 1112627 8030897 := bstep (se 2 (by rfl) ⟨3011586, by rfl⟩ : syracuseStep 8030897 = 6023173) B6023173
theorem B1673945 : Blo 1112627 1673945 := bstep (se 2 (by rfl) ⟨627729, by rfl⟩ : syracuseStep 1673945 = 1255459) B1255459
theorem B1674059 : Blo 1112627 1674059 := bstep (se 1 (by rfl) ⟨1255544, by rfl⟩ : syracuseStep 1674059 = 2511089) B2511089
theorem B1674071 : Blo 1112627 1674071 := bstep (se 1 (by rfl) ⟨1255553, by rfl⟩ : syracuseStep 1674071 = 2511107) B2511107
theorem B4524893 : Blo 1112627 4524893 := bstep (se 3 (by rfl) ⟨848417, by rfl⟩ : syracuseStep 4524893 = 1696835) B1696835
theorem B9538397 : Blo 1112627 9538397 := bstep (se 3 (by rfl) ⟨1788449, by rfl⟩ : syracuseStep 9538397 = 3576899) B3576899
theorem B1674137 : Blo 1112627 1674137 := bstep (se 2 (by rfl) ⟨627801, by rfl⟩ : syracuseStep 1674137 = 1255603) B1255603
theorem B13536179 : Blo 1112627 13536179 := bstep (se 1 (by rfl) ⟨10152134, by rfl⟩ : syracuseStep 13536179 = 20304269) B20304269
theorem B1674251 : Blo 1112627 1674251 := bstep (se 1 (by rfl) ⟨1255688, by rfl⟩ : syracuseStep 1674251 = 2511377) B2511377
theorem B1674263 : Blo 1112627 1674263 := bstep (se 1 (by rfl) ⟨1255697, by rfl⟩ : syracuseStep 1674263 = 2511395) B2511395
theorem B3574849 : Blo 1112627 3574849 := bstep (se 2 (by rfl) ⟨1340568, by rfl⟩ : syracuseStep 3574849 = 2681137) B2681137
theorem B1674329 : Blo 1112627 1674329 := bstep (se 2 (by rfl) ⟨627873, by rfl⟩ : syracuseStep 1674329 = 1255747) B1255747
theorem B1674443 : Blo 1112627 1674443 := bstep (se 1 (by rfl) ⟨1255832, by rfl⟩ : syracuseStep 1674443 = 2511665) B2511665
theorem B1412311 : Blo 1112627 1412311 := bstep (se 1 (by rfl) ⟨1059233, by rfl⟩ : syracuseStep 1412311 = 2118467) B2118467
theorem B1674455 : Blo 1112627 1674455 := bstep (se 1 (by rfl) ⟨1255841, by rfl⟩ : syracuseStep 1674455 = 2511683) B2511683
theorem B1674521 : Blo 1112627 1674521 := bstep (se 2 (by rfl) ⟨627945, by rfl⟩ : syracuseStep 1674521 = 1255891) B1255891
theorem B1674635 : Blo 1112627 1674635 := bstep (se 1 (by rfl) ⟨1255976, by rfl⟩ : syracuseStep 1674635 = 2511953) B2511953
theorem B1674647 : Blo 1112627 1674647 := bstep (se 1 (by rfl) ⟨1255985, by rfl⟩ : syracuseStep 1674647 = 2511971) B2511971
theorem B1674713 : Blo 1112627 1674713 := bstep (se 2 (by rfl) ⟨628017, by rfl⟩ : syracuseStep 1674713 = 1256035) B1256035
theorem B2821655 : Blo 1112627 2821655 := bstep (se 1 (by rfl) ⟨2116241, by rfl⟩ : syracuseStep 2821655 = 4232483) B4232483
theorem B1674827 : Blo 1112627 1674827 := bstep (se 1 (by rfl) ⟨1256120, by rfl⟩ : syracuseStep 1674827 = 2512241) B2512241
theorem B9539147 : Blo 1112627 9539147 := bstep (se 1 (by rfl) ⟨7154360, by rfl⟩ : syracuseStep 9539147 = 14308721) B14308721
theorem B1674839 : Blo 1112627 1674839 := bstep (se 1 (by rfl) ⟨1256129, by rfl⟩ : syracuseStep 1674839 = 2512259) B2512259
theorem B1674905 : Blo 1112627 1674905 := bstep (se 2 (by rfl) ⟨628089, by rfl⟩ : syracuseStep 1674905 = 1256179) B1256179
theorem B5640029 : Blo 1112627 5640029 := bstep (se 3 (by rfl) ⟨1057505, by rfl⟩ : syracuseStep 5640029 = 2115011) B2115011
theorem B7147595 : Blo 1112627 7147595 := bstep (se 1 (by rfl) ⟨5360696, by rfl⟩ : syracuseStep 7147595 = 10721393) B10721393
theorem B2822323 : Blo 1112627 2822323 := bstep (se 1 (by rfl) ⟨2116742, by rfl⟩ : syracuseStep 2822323 = 4233485) B4233485
theorem B2822465 : Blo 1112627 2822465 := bstep (se 2 (by rfl) ⟨1058424, by rfl⟩ : syracuseStep 2822465 = 2116849) B2116849
theorem B4755905 : Blo 1112627 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B3576413 : Blo 1112627 3576413 := bstep (se 3 (by rfl) ⟨670577, by rfl⟩ : syracuseStep 3576413 = 1341155) B1341155
theorem B5509849 : Blo 1112627 5509849 := bstep (se 2 (by rfl) ⟨2066193, by rfl⟩ : syracuseStep 5509849 = 4132387) B4132387
theorem B4232195 : Blo 1112627 4232195 := bstep (se 1 (by rfl) ⟨3174146, by rfl⟩ : syracuseStep 4232195 = 6348293) B6348293
theorem B4232209 : Blo 1112627 4232209 := bstep (se 2 (by rfl) ⟨1587078, by rfl⟩ : syracuseStep 4232209 = 3174157) B3174157
theorem B4232513 : Blo 1112627 4232513 := bstep (se 2 (by rfl) ⟨1587192, by rfl⟩ : syracuseStep 4232513 = 3174385) B3174385
theorem B6034763 : Blo 1112627 6034763 := bstep (se 1 (by rfl) ⟨4526072, by rfl⟩ : syracuseStep 6034763 = 9052145) B9052145
theorem B3806615 : Blo 1112627 3806615 := bstep (se 1 (by rfl) ⟨2854961, by rfl⟩ : syracuseStep 3806615 = 5709923) B5709923
theorem B2823731 : Blo 1112627 2823731 := bstep (se 1 (by rfl) ⟨2117798, by rfl⟩ : syracuseStep 2823731 = 4235597) B4235597
theorem B9508529 : Blo 1112627 9508529 := bstep (se 2 (by rfl) ⟨3565698, by rfl⟩ : syracuseStep 9508529 = 7131397) B7131397
theorem B7149235 : Blo 1112627 7149235 := bstep (se 1 (by rfl) ⟨5361926, by rfl⟩ : syracuseStep 7149235 = 10723853) B10723853
theorem B3806999 : Blo 1112627 3806999 := bstep (se 1 (by rfl) ⟨2855249, by rfl⟩ : syracuseStep 3806999 = 5710499) B5710499
theorem B5347147 : Blo 1112627 5347147 := bstep (se 1 (by rfl) ⟨4010360, by rfl⟩ : syracuseStep 5347147 = 8020721) B8020721
theorem B4757393 : Blo 1112627 4757393 := bstep (se 2 (by rfl) ⟨1784022, by rfl⟩ : syracuseStep 4757393 = 3568045) B3568045
theorem B5642135 : Blo 1112627 5642135 := bstep (se 1 (by rfl) ⟨4231601, by rfl⟩ : syracuseStep 5642135 = 8463203) B8463203
theorem B4233181 : Blo 1112627 4233181 := bstep (se 3 (by rfl) ⟨793721, by rfl⟩ : syracuseStep 4233181 = 1587443) B1587443
theorem B2824267 : Blo 1112627 2824267 := bstep (se 1 (by rfl) ⟨2118200, by rfl⟩ : syracuseStep 2824267 = 4236401) B4236401
theorem B2824409 : Blo 1112627 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B1251787 : Blo 1112627 1251787 := bstep (se 1 (by rfl) ⟨938840, by rfl⟩ : syracuseStep 1251787 = 1877681) B1877681
theorem B14260697 : Blo 1112627 14260697 := bstep (se 2 (by rfl) ⟨5347761, by rfl⟩ : syracuseStep 14260697 = 10695523) B10695523
theorem B1251895 : Blo 1112627 1251895 := bstep (se 1 (by rfl) ⟨938921, by rfl⟩ : syracuseStep 1251895 = 1877843) B1877843
theorem B1252075 : Blo 1112627 1252075 := bstep (se 1 (by rfl) ⟨939056, by rfl⟩ : syracuseStep 1252075 = 1878113) B1878113
theorem B2857793 : Blo 1112627 2857793 := bstep (se 2 (by rfl) ⟨1071672, by rfl⟩ : syracuseStep 2857793 = 2143345) B2143345
theorem B1252183 : Blo 1112627 1252183 := bstep (se 1 (by rfl) ⟨939137, by rfl⟩ : syracuseStep 1252183 = 1878275) B1878275
theorem B4758365 : Blo 1112627 4758365 := bstep (se 3 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 4758365 = 1784387) B1784387
theorem B1252363 : Blo 1112627 1252363 := bstep (se 1 (by rfl) ⟨939272, by rfl⟩ : syracuseStep 1252363 = 1878545) B1878545
theorem B2825239 : Blo 1112627 2825239 := bstep (se 1 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 2825239 = 4237859) B4237859
theorem B19307555 : Blo 1112627 19307555 := bstep (se 1 (by rfl) ⟨14480666, by rfl⟩ : syracuseStep 19307555 = 28961333) B28961333
theorem B1252471 : Blo 1112627 1252471 := bstep (se 1 (by rfl) ⟨939353, by rfl⟩ : syracuseStep 1252471 = 1878707) B1878707
theorem B4234457 : Blo 1112627 4234457 := bstep (se 2 (by rfl) ⟨1587921, by rfl⟩ : syracuseStep 4234457 = 3175843) B3175843
theorem B1252651 : Blo 1112627 1252651 := bstep (se 1 (by rfl) ⟨939488, by rfl⟩ : syracuseStep 1252651 = 1878977) B1878977
theorem B1252759 : Blo 1112627 1252759 := bstep (se 1 (by rfl) ⟨939569, by rfl⟩ : syracuseStep 1252759 = 1879139) B1879139
theorem B8461745 : Blo 1112627 8461745 := bstep (se 2 (by rfl) ⟨3173154, by rfl⟩ : syracuseStep 8461745 = 6346309) B6346309
theorem B2825675 : Blo 1112627 2825675 := bstep (se 1 (by rfl) ⟨2119256, by rfl⟩ : syracuseStep 2825675 = 4238513) B4238513
theorem B5086723 : Blo 1112627 5086723 := bstep (se 1 (by rfl) ⟨3815042, by rfl⟩ : syracuseStep 5086723 = 7630085) B7630085
theorem B1252939 : Blo 1112627 1252939 := bstep (se 1 (by rfl) ⟨939704, by rfl⟩ : syracuseStep 1252939 = 1879409) B1879409
theorem B1253047 : Blo 1112627 1253047 := bstep (se 1 (by rfl) ⟨939785, by rfl⟩ : syracuseStep 1253047 = 1879571) B1879571
theorem B2006795 : Blo 1112627 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B2826049 : Blo 1112627 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B1253227 : Blo 1112627 1253227 := bstep (se 1 (by rfl) ⟨939920, by rfl⟩ : syracuseStep 1253227 = 1879841) B1879841
theorem B8462231 : Blo 1112627 8462231 := bstep (se 1 (by rfl) ⟨6346673, by rfl⟩ : syracuseStep 8462231 = 12693347) B12693347
theorem B65118131 : Blo 1112627 65118131 := bstep (se 1 (by rfl) ⟨48838598, by rfl⟩ : syracuseStep 65118131 = 97677197) B97677197
theorem B1253335 : Blo 1112627 1253335 := bstep (se 1 (by rfl) ⟨940001, by rfl⟩ : syracuseStep 1253335 = 1880003) B1880003
theorem B1253515 : Blo 1112627 1253515 := bstep (se 1 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 1253515 = 1880273) B1880273
theorem B3809459 : Blo 1112627 3809459 := bstep (se 1 (by rfl) ⟨2857094, by rfl⟩ : syracuseStep 3809459 = 5714189) B5714189
theorem B1253623 : Blo 1112627 1253623 := bstep (se 1 (by rfl) ⟨940217, by rfl⟩ : syracuseStep 1253623 = 1880435) B1880435
theorem B1253803 : Blo 1112627 1253803 := bstep (se 1 (by rfl) ⟨940352, by rfl⟩ : syracuseStep 1253803 = 1880705) B1880705
theorem B1253911 : Blo 1112627 1253911 := bstep (se 1 (by rfl) ⟨940433, by rfl⟩ : syracuseStep 1253911 = 1880867) B1880867
theorem B1254091 : Blo 1112627 1254091 := bstep (se 1 (by rfl) ⟨940568, by rfl⟩ : syracuseStep 1254091 = 1881137) B1881137
theorem B1188631 : Blo 1112627 1188631 := bstep (se 1 (by rfl) ⟨891473, by rfl⟩ : syracuseStep 1188631 = 1782947) B1782947
theorem B2007833 : Blo 1112627 2007833 := bstep (se 2 (by rfl) ⟨752937, by rfl⟩ : syracuseStep 2007833 = 1505875) B1505875
theorem B4236083 : Blo 1112627 4236083 := bstep (se 1 (by rfl) ⟨3177062, by rfl⟩ : syracuseStep 4236083 = 6354125) B6354125
theorem B1254199 : Blo 1112627 1254199 := bstep (se 1 (by rfl) ⟨940649, by rfl⟩ : syracuseStep 1254199 = 1881299) B1881299
theorem B4236097 : Blo 1112627 4236097 := bstep (se 2 (by rfl) ⟨1588536, by rfl⟩ : syracuseStep 4236097 = 3177073) B3177073
theorem B1254379 : Blo 1112627 1254379 := bstep (se 1 (by rfl) ⟨940784, by rfl⟩ : syracuseStep 1254379 = 1881569) B1881569
theorem B12231755 : Blo 1112627 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B1254487 : Blo 1112627 1254487 := bstep (se 1 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 1254487 = 1881731) B1881731
theorem B2008243 : Blo 1112627 2008243 := bstep (se 1 (by rfl) ⟨1506182, by rfl⟩ : syracuseStep 2008243 = 3012365) B3012365
theorem B9512153 : Blo 1112627 9512153 := bstep (se 2 (by rfl) ⟨3567057, by rfl⟩ : syracuseStep 9512153 = 7134115) B7134115
theorem B1254667 : Blo 1112627 1254667 := bstep (se 1 (by rfl) ⟨941000, by rfl⟩ : syracuseStep 1254667 = 1882001) B1882001
theorem B1254775 : Blo 1112627 1254775 := bstep (se 1 (by rfl) ⟨941081, by rfl⟩ : syracuseStep 1254775 = 1882163) B1882163
theorem B4760963 : Blo 1112627 4760963 := bstep (se 1 (by rfl) ⟨3570722, by rfl⟩ : syracuseStep 4760963 = 7141445) B7141445
theorem B5645699 : Blo 1112627 5645699 := bstep (se 1 (by rfl) ⟨4234274, by rfl⟩ : syracuseStep 5645699 = 8468549) B8468549
theorem B1254955 : Blo 1112627 1254955 := bstep (se 1 (by rfl) ⟨941216, by rfl⟩ : syracuseStep 1254955 = 1882433) B1882433
theorem B1189451 : Blo 1112627 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B1877593 : Blo 1112627 1877593 := bstep (se 2 (by rfl) ⟨704097, by rfl⟩ : syracuseStep 1877593 = 1408195) B1408195
theorem B1255063 : Blo 1112627 1255063 := bstep (se 1 (by rfl) ⟨941297, by rfl⟩ : syracuseStep 1255063 = 1882595) B1882595
theorem B4761305 : Blo 1112627 4761305 := bstep (se 2 (by rfl) ⟨1785489, by rfl⟩ : syracuseStep 4761305 = 3570979) B3570979
theorem B1255243 : Blo 1112627 1255243 := bstep (se 1 (by rfl) ⟨941432, by rfl⟩ : syracuseStep 1255243 = 1882865) B1882865
theorem B3614557 : Blo 1112627 3614557 := bstep (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) B1355459
theorem B1255351 : Blo 1112627 1255351 := bstep (se 1 (by rfl) ⟨941513, by rfl⟩ : syracuseStep 1255351 = 1883027) B1883027
theorem B1255531 : Blo 1112627 1255531 := bstep (se 1 (by rfl) ⟨941648, by rfl⟩ : syracuseStep 1255531 = 1883297) B1883297
theorem B1878167 : Blo 1112627 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B2009281 : Blo 1112627 2009281 := bstep (se 2 (by rfl) ⟨753480, by rfl⟩ : syracuseStep 2009281 = 1506961) B1506961
theorem B1255639 : Blo 1112627 1255639 := bstep (se 1 (by rfl) ⟨941729, by rfl⟩ : syracuseStep 1255639 = 1883459) B1883459
theorem B1878295 : Blo 1112627 1878295 := bstep (se 1 (by rfl) ⟨1408721, by rfl⟩ : syracuseStep 1878295 = 2817443) B2817443
theorem B19048769 : Blo 1112627 19048769 := bstep (se 2 (by rfl) ⟨7143288, by rfl⟩ : syracuseStep 19048769 = 14286577) B14286577
theorem B1255819 : Blo 1112627 1255819 := bstep (se 1 (by rfl) ⟨941864, by rfl⟩ : syracuseStep 1255819 = 1883729) B1883729
theorem B12691889 : Blo 1112627 12691889 := bstep (se 2 (by rfl) ⟨4759458, by rfl⟩ : syracuseStep 12691889 = 9518917) B9518917
theorem B1255927 : Blo 1112627 1255927 := bstep (se 1 (by rfl) ⟨941945, by rfl⟩ : syracuseStep 1255927 = 1883891) B1883891
theorem B1256107 : Blo 1112627 1256107 := bstep (se 1 (by rfl) ⟨942080, by rfl⟩ : syracuseStep 1256107 = 1884161) B1884161
theorem B4238027 : Blo 1112627 4238027 := bstep (se 1 (by rfl) ⟨3178520, by rfl⟩ : syracuseStep 4238027 = 6357041) B6357041
theorem B4238041 : Blo 1112627 4238041 := bstep (se 2 (by rfl) ⟨1589265, by rfl⟩ : syracuseStep 4238041 = 3178531) B3178531
theorem B1190647 : Blo 1112627 1190647 := bstep (se 1 (by rfl) ⟨892985, by rfl⟩ : syracuseStep 1190647 = 1785971) B1785971
theorem B121940801 : Blo 1112627 121940801 := bstep (se 2 (by rfl) ⟨45727800, by rfl⟩ : syracuseStep 121940801 = 91455601) B91455601
theorem B1878923 : Blo 1112627 1878923 := bstep (se 1 (by rfl) ⟨1409192, by rfl⟩ : syracuseStep 1878923 = 2818385) B2818385
theorem B1879051 : Blo 1112627 1879051 := bstep (se 1 (by rfl) ⟨1409288, by rfl⟩ : syracuseStep 1879051 = 2818577) B2818577
theorem B1879193 : Blo 1112627 1879193 := bstep (se 2 (by rfl) ⟨704697, by rfl⟩ : syracuseStep 1879193 = 1409395) B1409395
theorem B1879321 : Blo 1112627 1879321 := bstep (se 2 (by rfl) ⟨704745, by rfl⟩ : syracuseStep 1879321 = 1409491) B1409491
theorem B14265665 : Blo 1112627 14265665 := bstep (se 2 (by rfl) ⟨5349624, by rfl⟩ : syracuseStep 14265665 = 10699249) B10699249
theorem B4075031 : Blo 1112627 4075031 := bstep (se 1 (by rfl) ⟨3056273, by rfl⟩ : syracuseStep 4075031 = 6112547) B6112547
theorem B1191467 : Blo 1112627 1191467 := bstep (se 1 (by rfl) ⟨893600, by rfl⟩ : syracuseStep 1191467 = 1787201) B1787201
theorem B4238999 : Blo 1112627 4238999 := bstep (se 1 (by rfl) ⟨3179249, by rfl⟩ : syracuseStep 4238999 = 6358499) B6358499
theorem B9514817 : Blo 1112627 9514817 := bstep (se 2 (by rfl) ⟨3568056, by rfl⟩ : syracuseStep 9514817 = 7136113) B7136113
theorem B1879895 : Blo 1112627 1879895 := bstep (se 1 (by rfl) ⟨1409921, by rfl⟩ : syracuseStep 1879895 = 2819843) B2819843
theorem B1880023 : Blo 1112627 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B12857305 : Blo 1112627 12857305 := bstep (se 2 (by rfl) ⟨4821489, by rfl⟩ : syracuseStep 12857305 = 9642979) B9642979
theorem B12038219 : Blo 1112627 12038219 := bstep (se 1 (by rfl) ⟨9028664, by rfl⟩ : syracuseStep 12038219 = 18057329) B18057329
theorem B1585433 : Blo 1112627 1585433 := bstep (se 2 (by rfl) ⟨594537, by rfl⟩ : syracuseStep 1585433 = 1189075) B1189075
theorem B1880651 : Blo 1112627 1880651 := bstep (se 1 (by rfl) ⟨1410488, by rfl⟩ : syracuseStep 1880651 = 2820977) B2820977
theorem B1880779 : Blo 1112627 1880779 := bstep (se 1 (by rfl) ⟨1410584, by rfl⟩ : syracuseStep 1880779 = 2821169) B2821169
theorem B2503475 : Blo 1112627 2503475 := bstep (se 1 (by rfl) ⟨1877606, by rfl⟩ : syracuseStep 2503475 = 3755213) B3755213
theorem B2503511 : Blo 1112627 2503511 := bstep (se 1 (by rfl) ⟨1877633, by rfl⟩ : syracuseStep 2503511 = 3755267) B3755267
theorem B1880921 : Blo 1112627 1880921 := bstep (se 2 (by rfl) ⟨705345, by rfl⟩ : syracuseStep 1880921 = 1410691) B1410691
theorem B1586071 : Blo 1112627 1586071 := bstep (se 1 (by rfl) ⟨1189553, by rfl⟩ : syracuseStep 1586071 = 2379107) B2379107
theorem B2864065 : Blo 1112627 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B2012107 : Blo 1112627 2012107 := bstep (se 1 (by rfl) ⟨1509080, by rfl⟩ : syracuseStep 2012107 = 3018161) B3018161
theorem B1881049 : Blo 1112627 1881049 := bstep (se 2 (by rfl) ⟨705393, by rfl⟩ : syracuseStep 1881049 = 1410787) B1410787
theorem B2503691 : Blo 1112627 2503691 := bstep (se 1 (by rfl) ⟨1877768, by rfl⟩ : syracuseStep 2503691 = 3755537) B3755537
theorem B4764689 : Blo 1112627 4764689 := bstep (se 2 (by rfl) ⟨1786758, by rfl⟩ : syracuseStep 4764689 = 3573517) B3573517
theorem B5649425 : Blo 1112627 5649425 := bstep (se 2 (by rfl) ⟨2118534, by rfl⟩ : syracuseStep 5649425 = 4237069) B4237069
theorem B2503745 : Blo 1112627 2503745 := bstep (se 2 (by rfl) ⟨938904, by rfl⟩ : syracuseStep 2503745 = 1877809) B1877809
theorem B5649587 : Blo 1112627 5649587 := bstep (se 1 (by rfl) ⟨4237190, by rfl⟩ : syracuseStep 5649587 = 8474381) B8474381
theorem B2503961 : Blo 1112627 2503961 := bstep (se 2 (by rfl) ⟨938985, by rfl⟩ : syracuseStep 2503961 = 1877971) B1877971
theorem B2504051 : Blo 1112627 2504051 := bstep (se 1 (by rfl) ⟨1878038, by rfl⟩ : syracuseStep 2504051 = 3756077) B3756077
theorem B2504087 : Blo 1112627 2504087 := bstep (se 1 (by rfl) ⟨1878065, by rfl⟩ : syracuseStep 2504087 = 3756131) B3756131
theorem B1881623 : Blo 1112627 1881623 := bstep (se 1 (by rfl) ⟨1411217, by rfl⟩ : syracuseStep 1881623 = 2822435) B2822435
theorem B2504267 : Blo 1112627 2504267 := bstep (se 1 (by rfl) ⟨1878200, by rfl⟩ : syracuseStep 2504267 = 3756401) B3756401
theorem B2504321 : Blo 1112627 2504321 := bstep (se 2 (by rfl) ⟨939120, by rfl⟩ : syracuseStep 2504321 = 1878241) B1878241
theorem B1881751 : Blo 1112627 1881751 := bstep (se 1 (by rfl) ⟨1411313, by rfl⟩ : syracuseStep 1881751 = 2822627) B2822627
theorem B1586891 : Blo 1112627 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B4765405 : Blo 1112627 4765405 := bstep (se 3 (by rfl) ⟨893513, by rfl⟩ : syracuseStep 4765405 = 1787027) B1787027
theorem B2504537 : Blo 1112627 2504537 := bstep (se 2 (by rfl) ⟨939201, by rfl⟩ : syracuseStep 2504537 = 1878403) B1878403
theorem B2504627 : Blo 1112627 2504627 := bstep (se 1 (by rfl) ⟨1878470, by rfl⟩ : syracuseStep 2504627 = 3756941) B3756941
theorem B2504663 : Blo 1112627 2504663 := bstep (se 1 (by rfl) ⟨1878497, by rfl⟩ : syracuseStep 2504663 = 3756995) B3756995
theorem B2504843 : Blo 1112627 2504843 := bstep (se 1 (by rfl) ⟨1878632, by rfl⟩ : syracuseStep 2504843 = 3757265) B3757265
theorem B1718425 : Blo 1112627 1718425 := bstep (se 2 (by rfl) ⟨644409, by rfl⟩ : syracuseStep 1718425 = 1288819) B1288819
theorem B2504897 : Blo 1112627 2504897 := bstep (se 2 (by rfl) ⟨939336, by rfl⟩ : syracuseStep 2504897 = 1878673) B1878673
theorem B7616729 : Blo 1112627 7616729 := bstep (se 2 (by rfl) ⟨2856273, by rfl⟩ : syracuseStep 7616729 = 5712547) B5712547
theorem B4012249 : Blo 1112627 4012249 := bstep (se 2 (by rfl) ⟨1504593, by rfl⟩ : syracuseStep 4012249 = 3009187) B3009187
theorem B1882379 : Blo 1112627 1882379 := bstep (se 1 (by rfl) ⟨1411784, by rfl⟩ : syracuseStep 1882379 = 2823569) B2823569
theorem B1882507 : Blo 1112627 1882507 := bstep (se 1 (by rfl) ⟨1411880, by rfl⟩ : syracuseStep 1882507 = 2823761) B2823761
theorem B2505113 : Blo 1112627 2505113 := bstep (se 2 (by rfl) ⟨939417, by rfl⟩ : syracuseStep 2505113 = 1878835) B1878835
theorem B2505203 : Blo 1112627 2505203 := bstep (se 1 (by rfl) ⟨1878902, by rfl⟩ : syracuseStep 2505203 = 3757805) B3757805
theorem B2505239 : Blo 1112627 2505239 := bstep (se 1 (by rfl) ⟨1878929, by rfl⟩ : syracuseStep 2505239 = 3757859) B3757859
theorem B1882649 : Blo 1112627 1882649 := bstep (se 2 (by rfl) ⟨705993, by rfl⟩ : syracuseStep 1882649 = 1411987) B1411987
theorem B1587865 : Blo 1112627 1587865 := bstep (se 2 (by rfl) ⟨595449, by rfl⟩ : syracuseStep 1587865 = 1190899) B1190899
theorem B1882777 : Blo 1112627 1882777 := bstep (se 2 (by rfl) ⟨706041, by rfl⟩ : syracuseStep 1882777 = 1412083) B1412083
theorem B2505419 : Blo 1112627 2505419 := bstep (se 1 (by rfl) ⟨1879064, by rfl⟩ : syracuseStep 2505419 = 3758129) B3758129
theorem B2505473 : Blo 1112627 2505473 := bstep (se 2 (by rfl) ⟨939552, by rfl⟩ : syracuseStep 2505473 = 1879105) B1879105
theorem B1784587 : Blo 1112627 1784587 := bstep (se 1 (by rfl) ⟨1338440, by rfl⟩ : syracuseStep 1784587 = 2676881) B2676881
theorem B2112331 : Blo 1112627 2112331 := bstep (se 1 (by rfl) ⟨1584248, by rfl⟩ : syracuseStep 2112331 = 3168497) B3168497
theorem B6339545 : Blo 1112627 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B2505689 : Blo 1112627 2505689 := bstep (se 2 (by rfl) ⟨939633, by rfl⟩ : syracuseStep 2505689 = 1879267) B1879267
theorem B1784843 : Blo 1112627 1784843 := bstep (se 1 (by rfl) ⟨1338632, by rfl⟩ : syracuseStep 1784843 = 2677265) B2677265
theorem B1129483 : Blo 1112627 1129483 := bstep (se 1 (by rfl) ⟨847112, by rfl⟩ : syracuseStep 1129483 = 1694225) B1694225
theorem B8469521 : Blo 1112627 8469521 := bstep (se 2 (by rfl) ⟨3176070, by rfl⟩ : syracuseStep 8469521 = 6352141) B6352141
theorem B2505779 : Blo 1112627 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B5651531 : Blo 1112627 5651531 := bstep (se 1 (by rfl) ⟨4238648, by rfl⟩ : syracuseStep 5651531 = 8477297) B8477297
theorem B2505815 : Blo 1112627 2505815 := bstep (se 1 (by rfl) ⟨1879361, by rfl⟩ : syracuseStep 2505815 = 3758723) B3758723
theorem B1883351 : Blo 1112627 1883351 := bstep (se 1 (by rfl) ⟨1412513, by rfl⟩ : syracuseStep 1883351 = 2825027) B2825027
theorem B2112779 : Blo 1112627 2112779 := bstep (se 1 (by rfl) ⟨1584584, by rfl⟩ : syracuseStep 2112779 = 3169169) B3169169
theorem B2505995 : Blo 1112627 2505995 := bstep (se 1 (by rfl) ⟨1879496, by rfl⟩ : syracuseStep 2505995 = 3758993) B3758993
theorem B2506049 : Blo 1112627 2506049 := bstep (se 2 (by rfl) ⟨939768, by rfl⟩ : syracuseStep 2506049 = 1879537) B1879537
theorem B1883479 : Blo 1112627 1883479 := bstep (se 1 (by rfl) ⟨1412609, by rfl⟩ : syracuseStep 1883479 = 2825219) B2825219
theorem B2112961 : Blo 1112627 2112961 := bstep (se 2 (by rfl) ⟨792360, by rfl⟩ : syracuseStep 2112961 = 1584721) B1584721
theorem B9649625 : Blo 1112627 9649625 := bstep (se 2 (by rfl) ⟨3618609, by rfl⟩ : syracuseStep 9649625 = 7237219) B7237219
theorem B2506265 : Blo 1112627 2506265 := bstep (se 2 (by rfl) ⟨939849, by rfl⟩ : syracuseStep 2506265 = 1879699) B1879699
theorem B3391051 : Blo 1112627 3391051 := bstep (se 1 (by rfl) ⟨2543288, by rfl⟩ : syracuseStep 3391051 = 5086577) B5086577
theorem B2506355 : Blo 1112627 2506355 := bstep (se 1 (by rfl) ⟨1879766, by rfl⟩ : syracuseStep 2506355 = 3759533) B3759533
theorem B2506391 : Blo 1112627 2506391 := bstep (se 1 (by rfl) ⟨1879793, by rfl⟩ : syracuseStep 2506391 = 3759587) B3759587
theorem B2113303 : Blo 1112627 2113303 := bstep (se 1 (by rfl) ⟨1584977, by rfl⟩ : syracuseStep 2113303 = 3169955) B3169955
theorem B1589015 : Blo 1112627 1589015 := bstep (se 1 (by rfl) ⟨1191761, by rfl⟩ : syracuseStep 1589015 = 2383523) B2383523
theorem B2506571 : Blo 1112627 2506571 := bstep (se 1 (by rfl) ⟨1879928, by rfl⟩ : syracuseStep 2506571 = 3759857) B3759857
theorem B1359703 : Blo 1112627 1359703 := bstep (se 1 (by rfl) ⟨1019777, by rfl⟩ : syracuseStep 1359703 = 2039555) B2039555
theorem B2506625 : Blo 1112627 2506625 := bstep (se 2 (by rfl) ⟨939984, by rfl⟩ : syracuseStep 2506625 = 1879969) B1879969
theorem B1884107 : Blo 1112627 1884107 := bstep (se 1 (by rfl) ⟨1413080, by rfl⟩ : syracuseStep 1884107 = 2826161) B2826161
theorem B10698713 : Blo 1112627 10698713 := bstep (se 2 (by rfl) ⟨4012017, by rfl⟩ : syracuseStep 10698713 = 8024035) B8024035
theorem B1785817 : Blo 1112627 1785817 := bstep (se 2 (by rfl) ⟨669681, by rfl⟩ : syracuseStep 1785817 = 1339363) B1339363
theorem B8044505 : Blo 1112627 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B2113523 : Blo 1112627 2113523 := bstep (se 1 (by rfl) ⟨1585142, by rfl⟩ : syracuseStep 2113523 = 3170285) B3170285
theorem B1589323 : Blo 1112627 1589323 := bstep (se 1 (by rfl) ⟨1191992, by rfl⟩ : syracuseStep 1589323 = 2383985) B2383985
theorem B1884235 : Blo 1112627 1884235 := bstep (se 1 (by rfl) ⟨1413176, by rfl⟩ : syracuseStep 1884235 = 2826353) B2826353
theorem B2506841 : Blo 1112627 2506841 := bstep (se 2 (by rfl) ⟨940065, by rfl⟩ : syracuseStep 2506841 = 1880131) B1880131
theorem B2506931 : Blo 1112627 2506931 := bstep (se 1 (by rfl) ⟨1880198, by rfl⟩ : syracuseStep 2506931 = 3760397) B3760397
theorem B2113751 : Blo 1112627 2113751 := bstep (se 1 (by rfl) ⟨1585313, by rfl⟩ : syracuseStep 2113751 = 3170627) B3170627
theorem B2506967 : Blo 1112627 2506967 := bstep (se 1 (by rfl) ⟨1880225, by rfl⟩ : syracuseStep 2506967 = 3760451) B3760451
theorem B4014353 : Blo 1112627 4014353 := bstep (se 2 (by rfl) ⟨1505382, by rfl⟩ : syracuseStep 4014353 = 3010765) B3010765
theorem B2507147 : Blo 1112627 2507147 := bstep (se 1 (by rfl) ⟨1880360, by rfl⟩ : syracuseStep 2507147 = 3760721) B3760721
theorem B2507201 : Blo 1112627 2507201 := bstep (se 2 (by rfl) ⟨940200, by rfl⟩ : syracuseStep 2507201 = 1880401) B1880401
theorem B2114009 : Blo 1112627 2114009 := bstep (se 2 (by rfl) ⟨792753, by rfl⟩ : syracuseStep 2114009 = 1585507) B1585507
theorem B1130999 : Blo 1112627 1130999 := bstep (se 1 (by rfl) ⟨848249, by rfl⟩ : syracuseStep 1130999 = 1696499) B1696499
theorem B2507417 : Blo 1112627 2507417 := bstep (se 2 (by rfl) ⟨940281, by rfl⟩ : syracuseStep 2507417 = 1880563) B1880563
theorem B2507507 : Blo 1112627 2507507 := bstep (se 1 (by rfl) ⟨1880630, by rfl⟩ : syracuseStep 2507507 = 3761261) B3761261
theorem B2507543 : Blo 1112627 2507543 := bstep (se 1 (by rfl) ⟨1880657, by rfl⟩ : syracuseStep 2507543 = 3761315) B3761315
theorem B2376535 : Blo 1112627 2376535 := bstep (se 1 (by rfl) ⟨1782401, by rfl⟩ : syracuseStep 2376535 = 3564803) B3564803
theorem B8045405 : Blo 1112627 8045405 := bstep (se 3 (by rfl) ⟨1508513, by rfl⟩ : syracuseStep 8045405 = 3017027) B3017027
theorem B2114419 : Blo 1112627 2114419 := bstep (se 1 (by rfl) ⟨1585814, by rfl⟩ : syracuseStep 2114419 = 3171629) B3171629
theorem B2507723 : Blo 1112627 2507723 := bstep (se 1 (by rfl) ⟨1880792, by rfl⟩ : syracuseStep 2507723 = 3761585) B3761585
theorem B2507777 : Blo 1112627 2507777 := bstep (se 2 (by rfl) ⟨940416, by rfl⟩ : syracuseStep 2507777 = 1880833) B1880833
theorem B2376715 : Blo 1112627 2376715 := bstep (se 1 (by rfl) ⟨1782536, by rfl⟩ : syracuseStep 2376715 = 3565073) B3565073
theorem B2376791 : Blo 1112627 2376791 := bstep (se 1 (by rfl) ⟨1782593, by rfl⟩ : syracuseStep 2376791 = 3565187) B3565187
theorem B4015277 : Blo 1112627 4015277 := bstep (se 3 (by rfl) ⟨752864, by rfl⟩ : syracuseStep 4015277 = 1505729) B1505729
theorem B2507993 : Blo 1112627 2507993 := bstep (se 2 (by rfl) ⟨940497, by rfl⟩ : syracuseStep 2507993 = 1880995) B1880995
theorem B4769027 : Blo 1112627 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B2508083 : Blo 1112627 2508083 := bstep (se 1 (by rfl) ⟨1881062, by rfl⟩ : syracuseStep 2508083 = 3762125) B3762125
theorem B4015435 : Blo 1112627 4015435 := bstep (se 1 (by rfl) ⟨3011576, by rfl⟩ : syracuseStep 4015435 = 6023153) B6023153
theorem B2508119 : Blo 1112627 2508119 := bstep (se 1 (by rfl) ⟨1881089, by rfl⟩ : syracuseStep 2508119 = 3762179) B3762179
theorem B2114905 : Blo 1112627 2114905 := bstep (se 2 (by rfl) ⟨793089, by rfl⟩ : syracuseStep 2114905 = 1586179) B1586179
theorem B2508299 : Blo 1112627 2508299 := bstep (se 1 (by rfl) ⟨1881224, by rfl⟩ : syracuseStep 2508299 = 3762449) B3762449
theorem B6342209 : Blo 1112627 6342209 := bstep (se 2 (by rfl) ⟨2378328, by rfl⟩ : syracuseStep 6342209 = 4756657) B4756657
theorem B2508353 : Blo 1112627 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B4015709 : Blo 1112627 4015709 := bstep (se 3 (by rfl) ⟨752945, by rfl⟩ : syracuseStep 4015709 = 1505891) B1505891
theorem B9520901 : Blo 1112627 9520901 := bstep (se 4 (by rfl) ⟨892584, by rfl⟩ : syracuseStep 9520901 = 1785169) B1785169
theorem B2508569 : Blo 1112627 2508569 := bstep (se 2 (by rfl) ⟨940713, by rfl⟩ : syracuseStep 2508569 = 1881427) B1881427
theorem B2508659 : Blo 1112627 2508659 := bstep (se 1 (by rfl) ⟨1881494, by rfl⟩ : syracuseStep 2508659 = 3762989) B3762989
theorem B2115467 : Blo 1112627 2115467 := bstep (se 1 (by rfl) ⟨1586600, by rfl⟩ : syracuseStep 2115467 = 3173201) B3173201
theorem B2508695 : Blo 1112627 2508695 := bstep (se 1 (by rfl) ⟨1881521, by rfl⟩ : syracuseStep 2508695 = 3763043) B3763043
theorem B2115649 : Blo 1112627 2115649 := bstep (se 2 (by rfl) ⟨793368, by rfl⟩ : syracuseStep 2115649 = 1586737) B1586737
theorem B2508875 : Blo 1112627 2508875 := bstep (se 1 (by rfl) ⟨1881656, by rfl⟩ : syracuseStep 2508875 = 3763313) B3763313
theorem B2508929 : Blo 1112627 2508929 := bstep (se 2 (by rfl) ⟨940848, by rfl⟩ : syracuseStep 2508929 = 1881697) B1881697
theorem B2509145 : Blo 1112627 2509145 := bstep (se 2 (by rfl) ⟨940929, by rfl⟩ : syracuseStep 2509145 = 1881859) B1881859
theorem B2509235 : Blo 1112627 2509235 := bstep (se 1 (by rfl) ⟨1881926, by rfl⟩ : syracuseStep 2509235 = 3763853) B3763853
theorem B2509271 : Blo 1112627 2509271 := bstep (se 1 (by rfl) ⟨1881953, by rfl⟩ : syracuseStep 2509271 = 3763907) B3763907
theorem B2509451 : Blo 1112627 2509451 := bstep (se 1 (by rfl) ⟨1882088, by rfl⟩ : syracuseStep 2509451 = 3764177) B3764177
theorem B2509505 : Blo 1112627 2509505 := bstep (se 2 (by rfl) ⟨941064, by rfl⟩ : syracuseStep 2509505 = 1882129) B1882129
theorem B2116363 : Blo 1112627 2116363 := bstep (se 1 (by rfl) ⟨1587272, by rfl⟩ : syracuseStep 2116363 = 3174545) B3174545
theorem B4016947 : Blo 1112627 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B8473409 : Blo 1112627 8473409 := bstep (se 2 (by rfl) ⟨3177528, by rfl⟩ : syracuseStep 8473409 = 6355057) B6355057
theorem B2116439 : Blo 1112627 2116439 := bstep (se 1 (by rfl) ⟨1587329, by rfl⟩ : syracuseStep 2116439 = 3174659) B3174659
theorem B2378585 : Blo 1112627 2378585 := bstep (se 2 (by rfl) ⟨891969, by rfl⟩ : syracuseStep 2378585 = 1783939) B1783939
theorem B2509721 : Blo 1112627 2509721 := bstep (se 2 (by rfl) ⟨941145, by rfl⟩ : syracuseStep 2509721 = 1882291) B1882291
theorem B3394507 : Blo 1112627 3394507 := bstep (se 1 (by rfl) ⟨2545880, by rfl⟩ : syracuseStep 3394507 = 5091761) B5091761
theorem B2509811 : Blo 1112627 2509811 := bstep (se 1 (by rfl) ⟨1882358, by rfl⟩ : syracuseStep 2509811 = 3764717) B3764717
theorem B2509847 : Blo 1112627 2509847 := bstep (se 1 (by rfl) ⟨1882385, by rfl⟩ : syracuseStep 2509847 = 3764771) B3764771
theorem B3755159 : Blo 1112627 3755159 := bstep (se 1 (by rfl) ⟨2816369, by rfl⟩ : syracuseStep 3755159 = 5632739) B5632739
theorem B8047795 : Blo 1112627 8047795 := bstep (se 1 (by rfl) ⟨6035846, by rfl⟩ : syracuseStep 8047795 = 12071693) B12071693
theorem B2510027 : Blo 1112627 2510027 := bstep (se 1 (by rfl) ⟨1882520, by rfl⟩ : syracuseStep 2510027 = 3765041) B3765041
theorem B2510081 : Blo 1112627 2510081 := bstep (se 2 (by rfl) ⟨941280, by rfl⟩ : syracuseStep 2510081 = 1882561) B1882561
theorem B2510297 : Blo 1112627 2510297 := bstep (se 2 (by rfl) ⟨941361, by rfl⟩ : syracuseStep 2510297 = 1882723) B1882723
theorem B2379251 : Blo 1112627 2379251 := bstep (se 1 (by rfl) ⟨1784438, by rfl⟩ : syracuseStep 2379251 = 3568877) B3568877
theorem B2117107 : Blo 1112627 2117107 := bstep (se 1 (by rfl) ⟨1587830, by rfl⟩ : syracuseStep 2117107 = 3175661) B3175661
theorem B2510387 : Blo 1112627 2510387 := bstep (se 1 (by rfl) ⟨1882790, by rfl⟩ : syracuseStep 2510387 = 3765581) B3765581
theorem B2510423 : Blo 1112627 2510423 := bstep (se 1 (by rfl) ⟨1882817, by rfl⟩ : syracuseStep 2510423 = 3765635) B3765635
theorem B6016643 : Blo 1112627 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B3755699 : Blo 1112627 3755699 := bstep (se 1 (by rfl) ⟨2816774, by rfl⟩ : syracuseStep 3755699 = 5633549) B5633549
theorem B2117335 : Blo 1112627 2117335 := bstep (se 1 (by rfl) ⟨1588001, by rfl⟩ : syracuseStep 2117335 = 3176003) B3176003
theorem B2510603 : Blo 1112627 2510603 := bstep (se 1 (by rfl) ⟨1882952, by rfl⟩ : syracuseStep 2510603 = 3765905) B3765905
theorem B2117441 : Blo 1112627 2117441 := bstep (se 2 (by rfl) ⟨794040, by rfl⟩ : syracuseStep 2117441 = 1588081) B1588081
theorem B2510657 : Blo 1112627 2510657 := bstep (se 2 (by rfl) ⟨941496, by rfl⟩ : syracuseStep 2510657 = 1882993) B1882993
theorem B2674583 : Blo 1112627 2674583 := bstep (se 1 (by rfl) ⟨2005937, by rfl⟩ : syracuseStep 2674583 = 4011875) B4011875
theorem B3755969 : Blo 1112627 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B2117593 : Blo 1112627 2117593 := bstep (se 2 (by rfl) ⟨794097, by rfl⟩ : syracuseStep 2117593 = 1588195) B1588195
theorem B20369369 : Blo 1112627 20369369 := bstep (se 2 (by rfl) ⟨7638513, by rfl⟩ : syracuseStep 20369369 = 15277027) B15277027
theorem B2510873 : Blo 1112627 2510873 := bstep (se 2 (by rfl) ⟨941577, by rfl⟩ : syracuseStep 2510873 = 1883155) B1883155
theorem B2510963 : Blo 1112627 2510963 := bstep (se 1 (by rfl) ⟨1883222, by rfl⟩ : syracuseStep 2510963 = 3766445) B3766445
theorem B2510999 : Blo 1112627 2510999 := bstep (se 1 (by rfl) ⟨1883249, by rfl⟩ : syracuseStep 2510999 = 3766499) B3766499
theorem B8704205 : Blo 1112627 8704205 := bstep (se 3 (by rfl) ⟨1632038, by rfl⟩ : syracuseStep 8704205 = 3264077) B3264077
theorem B10178777 : Blo 1112627 10178777 := bstep (se 2 (by rfl) ⟨3817041, by rfl⟩ : syracuseStep 10178777 = 7634083) B7634083
theorem B2511179 : Blo 1112627 2511179 := bstep (se 1 (by rfl) ⟨1883384, by rfl⟩ : syracuseStep 2511179 = 3766769) B3766769
theorem B2511233 : Blo 1112627 2511233 := bstep (se 2 (by rfl) ⟨941712, by rfl⟩ : syracuseStep 2511233 = 1883425) B1883425
theorem B3756509 : Blo 1112627 3756509 := bstep (se 3 (by rfl) ⟨704345, by rfl⟩ : syracuseStep 3756509 = 1408691) B1408691
theorem B2511449 : Blo 1112627 2511449 := bstep (se 2 (by rfl) ⟨941793, by rfl⟩ : syracuseStep 2511449 = 1883587) B1883587
theorem B2675351 : Blo 1112627 2675351 := bstep (se 1 (by rfl) ⟨2006513, by rfl⟩ : syracuseStep 2675351 = 4013027) B4013027
theorem B2511539 : Blo 1112627 2511539 := bstep (se 1 (by rfl) ⟨1883654, by rfl⟩ : syracuseStep 2511539 = 3767309) B3767309
theorem B2511575 : Blo 1112627 2511575 := bstep (se 1 (by rfl) ⟨1883681, by rfl⟩ : syracuseStep 2511575 = 3767363) B3767363
theorem B8475353 : Blo 1112627 8475353 := bstep (se 2 (by rfl) ⟨3178257, by rfl⟩ : syracuseStep 8475353 = 6356515) B6356515
theorem B4018909 : Blo 1112627 4018909 := bstep (se 3 (by rfl) ⟨753545, by rfl⟩ : syracuseStep 4018909 = 1507091) B1507091
theorem B2544385 : Blo 1112627 2544385 := bstep (se 2 (by rfl) ⟨954144, by rfl⟩ : syracuseStep 2544385 = 1908289) B1908289
theorem B4018967 : Blo 1112627 4018967 := bstep (se 1 (by rfl) ⟨3014225, by rfl⟩ : syracuseStep 4018967 = 6028451) B6028451
theorem B2511755 : Blo 1112627 2511755 := bstep (se 1 (by rfl) ⟨1883816, by rfl⟩ : syracuseStep 2511755 = 3767633) B3767633
theorem B2511809 : Blo 1112627 2511809 := bstep (se 2 (by rfl) ⟨941928, by rfl⟩ : syracuseStep 2511809 = 1883857) B1883857
theorem B2380747 : Blo 1112627 2380747 := bstep (se 1 (by rfl) ⟨1785560, by rfl⟩ : syracuseStep 2380747 = 3571121) B3571121
theorem B2512025 : Blo 1112627 2512025 := bstep (se 2 (by rfl) ⟨942009, by rfl⟩ : syracuseStep 2512025 = 1884019) B1884019
theorem B2118899 : Blo 1112627 2118899 := bstep (se 1 (by rfl) ⟨1589174, by rfl⟩ : syracuseStep 2118899 = 3178349) B3178349
theorem B2512115 : Blo 1112627 2512115 := bstep (se 1 (by rfl) ⟨1884086, by rfl⟩ : syracuseStep 2512115 = 3768173) B3768173
theorem B2512151 : Blo 1112627 2512151 := bstep (se 1 (by rfl) ⟨1884113, by rfl⟩ : syracuseStep 2512151 = 3768227) B3768227
theorem B2119051 : Blo 1112627 2119051 := bstep (se 1 (by rfl) ⟨1589288, by rfl⟩ : syracuseStep 2119051 = 3178577) B3178577
theorem B2512331 : Blo 1112627 2512331 := bstep (se 1 (by rfl) ⟨1884248, by rfl⟩ : syracuseStep 2512331 = 3768497) B3768497
theorem B2512385 : Blo 1112627 2512385 := bstep (se 2 (by rfl) ⟨942144, by rfl⟩ : syracuseStep 2512385 = 1884289) B1884289
theorem B5723713 : Blo 1112627 5723713 := bstep (se 2 (by rfl) ⟨2146392, by rfl⟩ : syracuseStep 5723713 = 4292785) B4292785
theorem B3757643 : Blo 1112627 3757643 := bstep (se 1 (by rfl) ⟨2818232, by rfl⟩ : syracuseStep 3757643 = 5636465) B5636465
theorem B2119385 : Blo 1112627 2119385 := bstep (se 2 (by rfl) ⟨794769, by rfl⟩ : syracuseStep 2119385 = 1589539) B1589539
theorem B1431319 : Blo 1112627 1431319 := bstep (se 1 (by rfl) ⟨1073489, by rfl⟩ : syracuseStep 1431319 = 2146979) B2146979
theorem B12703553 : Blo 1112627 12703553 := bstep (se 2 (by rfl) ⟨4763832, by rfl⟩ : syracuseStep 12703553 = 9527665) B9527665
theorem B3757913 : Blo 1112627 3757913 := bstep (se 2 (by rfl) ⟨1409217, by rfl⟩ : syracuseStep 3757913 = 2818435) B2818435
theorem B34363237 : Blo 1112627 34363237 := bstep (se 4 (by rfl) ⟨3221553, by rfl⟩ : syracuseStep 34363237 = 6443107) B6443107
theorem B1693579 : Blo 1112627 1693579 := bstep (se 1 (by rfl) ⟨1270184, by rfl⟩ : syracuseStep 1693579 = 2540369) B2540369
theorem B4577303 : Blo 1112627 4577303 := bstep (se 1 (by rfl) ⟨3432977, by rfl⟩ : syracuseStep 4577303 = 6865955) B6865955
theorem B2414657 : Blo 1112627 2414657 := bstep (se 2 (by rfl) ⟨905496, by rfl⟩ : syracuseStep 2414657 = 1810993) B1810993
theorem B2381977 : Blo 1112627 2381977 := bstep (se 2 (by rfl) ⟨893241, by rfl⟩ : syracuseStep 2381977 = 1786483) B1786483
theorem B2677043 : Blo 1112627 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B6773057 : Blo 1112627 6773057 := bstep (se 2 (by rfl) ⟨2539896, by rfl⟩ : syracuseStep 6773057 = 5079793) B5079793
theorem B2546009 : Blo 1112627 2546009 := bstep (se 2 (by rfl) ⟨954753, by rfl⟩ : syracuseStep 2546009 = 1909507) B1909507
theorem B5364119 : Blo 1112627 5364119 := bstep (se 1 (by rfl) ⟨4023089, by rfl⟩ : syracuseStep 5364119 = 8046179) B8046179
theorem B4282841 : Blo 1112627 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B3758615 : Blo 1112627 3758615 := bstep (se 1 (by rfl) ⟨2818961, by rfl⟩ : syracuseStep 3758615 = 5637923) B5637923
theorem B2677465 : Blo 1112627 2677465 := bstep (se 2 (by rfl) ⟨1004049, by rfl⟩ : syracuseStep 2677465 = 2008099) B2008099
theorem B6347585 : Blo 1112627 6347585 := bstep (se 2 (by rfl) ⟨2380344, by rfl⟩ : syracuseStep 6347585 = 4760689) B4760689
theorem B2710451 : Blo 1112627 2710451 := bstep (se 1 (by rfl) ⟨2032838, by rfl⟩ : syracuseStep 2710451 = 4065677) B4065677
theorem B3759155 : Blo 1112627 3759155 := bstep (se 1 (by rfl) ⟨2819366, by rfl⟩ : syracuseStep 3759155 = 5638733) B5638733
theorem B19061891 : Blo 1112627 19061891 := bstep (se 1 (by rfl) ⟨14296418, by rfl⟩ : syracuseStep 19061891 = 28592837) B28592837
theorem B3169601 : Blo 1112627 3169601 := bstep (se 2 (by rfl) ⟨1188600, by rfl⟩ : syracuseStep 3169601 = 2377201) B2377201
theorem B3759425 : Blo 1112627 3759425 := bstep (se 2 (by rfl) ⟨1409784, by rfl⟩ : syracuseStep 3759425 = 2819569) B2819569
theorem B6872471 : Blo 1112627 6872471 := bstep (se 1 (by rfl) ⟨5154353, by rfl⟩ : syracuseStep 6872471 = 10308707) B10308707
theorem B1269163 : Blo 1112627 1269163 := bstep (se 1 (by rfl) ⟨951872, by rfl⟩ : syracuseStep 1269163 = 1903745) B1903745
theorem B8248925 : Blo 1112627 8248925 := bstep (se 3 (by rfl) ⟨1546673, by rfl⟩ : syracuseStep 8248925 = 3093347) B3093347
theorem B4513553 : Blo 1112627 4513553 := bstep (se 2 (by rfl) ⟨1692582, by rfl⟩ : syracuseStep 4513553 = 3385165) B3385165
theorem B3170137 : Blo 1112627 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B3759965 : Blo 1112627 3759965 := bstep (se 3 (by rfl) ⟨704993, by rfl⟩ : syracuseStep 3759965 = 1409987) B1409987
theorem B10182493 : Blo 1112627 10182493 := bstep (se 3 (by rfl) ⟨1909217, by rfl⟩ : syracuseStep 10182493 = 3818435) B3818435
theorem B3923905 : Blo 1112627 3923905 := bstep (se 2 (by rfl) ⟨1471464, by rfl⟩ : syracuseStep 3923905 = 2942929) B2942929
theorem B8478755 : Blo 1112627 8478755 := bstep (se 1 (by rfl) ⟨6359066, by rfl⟩ : syracuseStep 8478755 = 12718133) B12718133
theorem B14278787 : Blo 1112627 14278787 := bstep (se 1 (by rfl) ⟨10709090, by rfl⟩ : syracuseStep 14278787 = 21418181) B21418181
theorem B4514071 : Blo 1112627 4514071 := bstep (se 1 (by rfl) ⟨3385553, by rfl⟩ : syracuseStep 4514071 = 6771107) B6771107
theorem B6283585 : Blo 1112627 6283585 := bstep (se 2 (by rfl) ⟨2356344, by rfl⟩ : syracuseStep 6283585 = 4712689) B4712689
theorem B4514123 : Blo 1112627 4514123 := bstep (se 1 (by rfl) ⟨3385592, by rfl⟩ : syracuseStep 4514123 = 6771185) B6771185
theorem B8020403 : Blo 1112627 8020403 := bstep (se 1 (by rfl) ⟨6015302, by rfl⟩ : syracuseStep 8020403 = 12030605) B12030605
theorem B4514251 : Blo 1112627 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B9527939 : Blo 1112627 9527939 := bstep (se 1 (by rfl) ⟨7145954, by rfl⟩ : syracuseStep 9527939 = 14291909) B14291909
theorem B10150757 : Blo 1112627 10150757 := bstep (se 4 (by rfl) ⟨951633, by rfl⟩ : syracuseStep 10150757 = 1903267) B1903267
theorem B3761099 : Blo 1112627 3761099 := bstep (se 1 (by rfl) ⟨2820824, by rfl⟩ : syracuseStep 3761099 = 5641649) B5641649
theorem B9036805 : Blo 1112627 9036805 := bstep (se 4 (by rfl) ⟨847200, by rfl⟩ : syracuseStep 9036805 = 1694401) B1694401
theorem B45737141 : Blo 1112627 45737141 := bstep (se 5 (by rfl) ⟨2143928, by rfl⟩ : syracuseStep 45737141 = 4287857) B4287857
theorem B3761369 : Blo 1112627 3761369 := bstep (se 2 (by rfl) ⟨1410513, by rfl⟩ : syracuseStep 3761369 = 2821027) B2821027
theorem B3433693 : Blo 1112627 3433693 := bstep (se 3 (by rfl) ⟨643817, by rfl⟩ : syracuseStep 3433693 = 1287635) B1287635
theorem B9168515 : Blo 1112627 9168515 := bstep (se 1 (by rfl) ⟨6876386, by rfl⟩ : syracuseStep 9168515 = 13752773) B13752773
theorem B10708631 : Blo 1112627 10708631 := bstep (se 1 (by rfl) ⟨8031473, by rfl⟩ : syracuseStep 10708631 = 16062947) B16062947
theorem B2680523 : Blo 1112627 2680523 := bstep (se 1 (by rfl) ⟨2010392, by rfl⟩ : syracuseStep 2680523 = 4020785) B4020785
theorem B3172061 : Blo 1112627 3172061 := bstep (se 3 (by rfl) ⟨594761, by rfl⟩ : syracuseStep 3172061 = 1189523) B1189523
theorem B3762071 : Blo 1112627 3762071 := bstep (se 1 (by rfl) ⟨2821553, by rfl⟩ : syracuseStep 3762071 = 5643107) B5643107
theorem B6023261 : Blo 1112627 6023261 := bstep (se 3 (by rfl) ⟨1129361, by rfl⟩ : syracuseStep 6023261 = 2258723) B2258723
theorem B3008819 : Blo 1112627 3008819 := bstep (se 1 (by rfl) ⟨2256614, by rfl⟩ : syracuseStep 3008819 = 4513229) B4513229
theorem B3762611 : Blo 1112627 3762611 := bstep (se 1 (by rfl) ⟨2821958, by rfl⟩ : syracuseStep 3762611 = 5643917) B5643917
theorem B1206775 : Blo 1112627 1206775 := bstep (se 1 (by rfl) ⟨905081, by rfl⟩ : syracuseStep 1206775 = 1810163) B1810163
theorem B1272407 : Blo 1112627 1272407 := bstep (se 1 (by rfl) ⟨954305, by rfl⟩ : syracuseStep 1272407 = 1908611) B1908611
theorem B3762881 : Blo 1112627 3762881 := bstep (se 2 (by rfl) ⟨1411080, by rfl⟩ : syracuseStep 3762881 = 2822161) B2822161
theorem B3763421 : Blo 1112627 3763421 := bstep (se 3 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 3763421 = 1411283) B1411283
theorem B2714969 : Blo 1112627 2714969 := bstep (se 2 (by rfl) ⟨1018113, by rfl⟩ : syracuseStep 2714969 = 2036227) B2036227
theorem B29355533 : Blo 1112627 29355533 := bstep (se 3 (by rfl) ⟨5504162, by rfl⟩ : syracuseStep 29355533 = 11008325) B11008325
theorem B1339031 : Blo 1112627 1339031 := bstep (se 1 (by rfl) ⟨1004273, by rfl⟩ : syracuseStep 1339031 = 2008547) B2008547
theorem B3764555 : Blo 1112627 3764555 := bstep (se 1 (by rfl) ⟨2823416, by rfl⟩ : syracuseStep 3764555 = 5646833) B5646833
theorem B3174977 : Blo 1112627 3174977 := bstep (se 2 (by rfl) ⟨1190616, by rfl⟩ : syracuseStep 3174977 = 2381233) B2381233
theorem B3175001 : Blo 1112627 3175001 := bstep (se 2 (by rfl) ⟨1190625, by rfl⟩ : syracuseStep 3175001 = 2381251) B2381251
theorem B3764825 : Blo 1112627 3764825 := bstep (se 2 (by rfl) ⟨1411809, by rfl⟩ : syracuseStep 3764825 = 2823619) B2823619
theorem B8024669 : Blo 1112627 8024669 := bstep (se 3 (by rfl) ⟨1504625, by rfl⟩ : syracuseStep 8024669 = 3009251) B3009251
theorem B9040535 : Blo 1112627 9040535 := bstep (se 1 (by rfl) ⟨6780401, by rfl⟩ : syracuseStep 9040535 = 13560803) B13560803
theorem B1340107 : Blo 1112627 1340107 := bstep (se 1 (by rfl) ⟨1005080, by rfl⟩ : syracuseStep 1340107 = 2010161) B2010161
theorem B5075777 : Blo 1112627 5075777 := bstep (se 2 (by rfl) ⟨1903416, by rfl⟩ : syracuseStep 5075777 = 3806833) B3806833
theorem B1504345 : Blo 1112627 1504345 := bstep (se 2 (by rfl) ⟨564129, by rfl⟩ : syracuseStep 1504345 = 1128259) B1128259
theorem B9172099 : Blo 1112627 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B3765527 : Blo 1112627 3765527 := bstep (se 1 (by rfl) ⟨2824145, by rfl⟩ : syracuseStep 3765527 = 5648291) B5648291
theorem B4519261 : Blo 1112627 4519261 := bstep (se 3 (by rfl) ⟨847361, by rfl⟩ : syracuseStep 4519261 = 1694723) B1694723
theorem B7239091 : Blo 1112627 7239091 := bstep (se 1 (by rfl) ⟨5429318, by rfl⟩ : syracuseStep 7239091 = 10858637) B10858637
theorem B73266893 : Blo 1112627 73266893 := bstep (se 3 (by rfl) ⟨13737542, by rfl⟩ : syracuseStep 73266893 = 27475085) B27475085
theorem B6616849 : Blo 1112627 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B3176243 : Blo 1112627 3176243 := bstep (se 1 (by rfl) ⟨2382182, by rfl⟩ : syracuseStep 3176243 = 4764365) B4764365
theorem B3766067 : Blo 1112627 3766067 := bstep (se 1 (by rfl) ⟨2824550, by rfl⟩ : syracuseStep 3766067 = 5649101) B5649101
theorem B1668953 : Blo 1112627 1668953 := bstep (se 2 (by rfl) ⟨625857, by rfl⟩ : syracuseStep 1668953 = 1251715) B1251715
theorem B4224919 : Blo 1112627 4224919 := bstep (se 1 (by rfl) ⟨3168689, by rfl⟩ : syracuseStep 4224919 = 6337379) B6337379
theorem B1669067 : Blo 1112627 1669067 := bstep (se 1 (by rfl) ⟨1251800, by rfl⟩ : syracuseStep 1669067 = 2503601) B2503601
theorem B1669079 : Blo 1112627 1669079 := bstep (se 1 (by rfl) ⟨1251809, by rfl⟩ : syracuseStep 1669079 = 2503619) B2503619
theorem B1341463 : Blo 1112627 1341463 := bstep (se 1 (by rfl) ⟨1006097, by rfl⟩ : syracuseStep 1341463 = 2012195) B2012195
theorem B1669145 : Blo 1112627 1669145 := bstep (se 2 (by rfl) ⟨625929, by rfl⟩ : syracuseStep 1669145 = 1251859) B1251859
theorem B3766337 : Blo 1112627 3766337 := bstep (se 2 (by rfl) ⟨1412376, by rfl⟩ : syracuseStep 3766337 = 2824753) B2824753
theorem B1669259 : Blo 1112627 1669259 := bstep (se 1 (by rfl) ⟨1251944, by rfl⟩ : syracuseStep 1669259 = 2503889) B2503889
theorem B1669271 : Blo 1112627 1669271 := bstep (se 1 (by rfl) ⟨1251953, by rfl⟩ : syracuseStep 1669271 = 2503907) B2503907
theorem B2259137 : Blo 1112627 2259137 := bstep (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) B1694353
theorem B1669337 : Blo 1112627 1669337 := bstep (se 2 (by rfl) ⟨626001, by rfl⟩ : syracuseStep 1669337 = 1252003) B1252003
theorem B1669451 : Blo 1112627 1669451 := bstep (se 1 (by rfl) ⟨1252088, by rfl⟩ : syracuseStep 1669451 = 2504177) B2504177
theorem B1669463 : Blo 1112627 1669463 := bstep (se 1 (by rfl) ⟨1252097, by rfl⟩ : syracuseStep 1669463 = 2504195) B2504195
theorem B6355331 : Blo 1112627 6355331 := bstep (se 1 (by rfl) ⟨4766498, by rfl⟩ : syracuseStep 6355331 = 9532997) B9532997
theorem B1669529 : Blo 1112627 1669529 := bstep (se 2 (by rfl) ⟨626073, by rfl⟩ : syracuseStep 1669529 = 1252147) B1252147
theorem B5634521 : Blo 1112627 5634521 := bstep (se 2 (by rfl) ⟨2112945, by rfl⟩ : syracuseStep 5634521 = 4225891) B4225891
theorem B1669643 : Blo 1112627 1669643 := bstep (se 1 (by rfl) ⟨1252232, by rfl⟩ : syracuseStep 1669643 = 2504465) B2504465
theorem B1669655 : Blo 1112627 1669655 := bstep (se 1 (by rfl) ⟨1252241, by rfl⟩ : syracuseStep 1669655 = 2504483) B2504483
theorem B1112631 : Blo 1112627 1112631 := bstep (se 1 (by rfl) ⟨834473, by rfl⟩ : syracuseStep 1112631 = 1668947) B1668947
theorem B1112651 : Blo 1112627 1112651 := bstep (se 1 (by rfl) ⟨834488, by rfl⟩ : syracuseStep 1112651 = 1668977) B1668977
theorem B1112663 : Blo 1112627 1112663 := bstep (se 1 (by rfl) ⟨834497, by rfl⟩ : syracuseStep 1112663 = 1668995) B1668995
theorem B1669721 : Blo 1112627 1669721 := bstep (se 2 (by rfl) ⟨626145, by rfl⟩ : syracuseStep 1669721 = 1252291) B1252291
theorem B3766877 : Blo 1112627 3766877 := bstep (se 3 (by rfl) ⟨706289, by rfl⟩ : syracuseStep 3766877 = 1412579) B1412579
theorem B1112683 : Blo 1112627 1112683 := bstep (se 1 (by rfl) ⟨834512, by rfl⟩ : syracuseStep 1112683 = 1669025) B1669025
theorem B1112695 : Blo 1112627 1112695 := bstep (se 1 (by rfl) ⟨834521, by rfl⟩ : syracuseStep 1112695 = 1669043) B1669043
theorem B1112715 : Blo 1112627 1112715 := bstep (se 1 (by rfl) ⟨834536, by rfl⟩ : syracuseStep 1112715 = 1669073) B1669073
theorem B1112727 : Blo 1112627 1112727 := bstep (se 1 (by rfl) ⟨834545, by rfl⟩ : syracuseStep 1112727 = 1669091) B1669091
theorem B1112747 : Blo 1112627 1112747 := bstep (se 1 (by rfl) ⟨834560, by rfl⟩ : syracuseStep 1112747 = 1669121) B1669121
theorem B4225709 : Blo 1112627 4225709 := bstep (se 3 (by rfl) ⟨792320, by rfl⟩ : syracuseStep 4225709 = 1584641) B1584641
theorem B1112759 : Blo 1112627 1112759 := bstep (se 1 (by rfl) ⟨834569, by rfl⟩ : syracuseStep 1112759 = 1669139) B1669139
theorem B1112779 : Blo 1112627 1112779 := bstep (se 1 (by rfl) ⟨834584, by rfl⟩ : syracuseStep 1112779 = 1669169) B1669169
theorem B1669835 : Blo 1112627 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B1112791 : Blo 1112627 1112791 := bstep (se 1 (by rfl) ⟨834593, by rfl⟩ : syracuseStep 1112791 = 1669187) B1669187
theorem B1669847 : Blo 1112627 1669847 := bstep (se 1 (by rfl) ⟨1252385, by rfl⟩ : syracuseStep 1669847 = 2504771) B2504771
theorem B1112811 : Blo 1112627 1112811 := bstep (se 1 (by rfl) ⟨834608, by rfl⟩ : syracuseStep 1112811 = 1669217) B1669217
theorem B1112823 : Blo 1112627 1112823 := bstep (se 1 (by rfl) ⟨834617, by rfl⟩ : syracuseStep 1112823 = 1669235) B1669235
theorem B10156805 : Blo 1112627 10156805 := bstep (se 4 (by rfl) ⟨952200, by rfl⟩ : syracuseStep 10156805 = 1904401) B1904401
theorem B1112843 : Blo 1112627 1112843 := bstep (se 1 (by rfl) ⟨834632, by rfl⟩ : syracuseStep 1112843 = 1669265) B1669265
theorem B1112855 : Blo 1112627 1112855 := bstep (se 1 (by rfl) ⟨834641, by rfl⟩ : syracuseStep 1112855 = 1669283) B1669283
theorem B1669913 : Blo 1112627 1669913 := bstep (se 2 (by rfl) ⟨626217, by rfl⟩ : syracuseStep 1669913 = 1252435) B1252435
theorem B1112875 : Blo 1112627 1112875 := bstep (se 1 (by rfl) ⟨834656, by rfl⟩ : syracuseStep 1112875 = 1669313) B1669313
theorem B1112887 : Blo 1112627 1112887 := bstep (se 1 (by rfl) ⟨834665, by rfl⟩ : syracuseStep 1112887 = 1669331) B1669331
theorem B1112907 : Blo 1112627 1112907 := bstep (se 1 (by rfl) ⟨834680, by rfl⟩ : syracuseStep 1112907 = 1669361) B1669361
theorem B1145675 : Blo 1112627 1145675 := bstep (se 1 (by rfl) ⟨859256, by rfl⟩ : syracuseStep 1145675 = 1718513) B1718513
theorem B1112919 : Blo 1112627 1112919 := bstep (se 1 (by rfl) ⟨834689, by rfl⟩ : syracuseStep 1112919 = 1669379) B1669379
theorem B1112939 : Blo 1112627 1112939 := bstep (se 1 (by rfl) ⟨834704, by rfl⟩ : syracuseStep 1112939 = 1669409) B1669409
theorem B1145707 : Blo 1112627 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B1112951 : Blo 1112627 1112951 := bstep (se 1 (by rfl) ⟨834713, by rfl⟩ : syracuseStep 1112951 = 1669427) B1669427
theorem B1112971 : Blo 1112627 1112971 := bstep (se 1 (by rfl) ⟨834728, by rfl⟩ : syracuseStep 1112971 = 1669457) B1669457
theorem B1670027 : Blo 1112627 1670027 := bstep (se 1 (by rfl) ⟨1252520, by rfl⟩ : syracuseStep 1670027 = 2505041) B2505041
theorem B1112983 : Blo 1112627 1112983 := bstep (se 1 (by rfl) ⟨834737, by rfl⟩ : syracuseStep 1112983 = 1669475) B1669475
theorem B1670039 : Blo 1112627 1670039 := bstep (se 1 (by rfl) ⟨1252529, by rfl⟩ : syracuseStep 1670039 = 2505059) B2505059
theorem B1113003 : Blo 1112627 1113003 := bstep (se 1 (by rfl) ⟨834752, by rfl⟩ : syracuseStep 1113003 = 1669505) B1669505
theorem B1113015 : Blo 1112627 1113015 := bstep (se 1 (by rfl) ⟨834761, by rfl⟩ : syracuseStep 1113015 = 1669523) B1669523
theorem B1113035 : Blo 1112627 1113035 := bstep (se 1 (by rfl) ⟨834776, by rfl⟩ : syracuseStep 1113035 = 1669553) B1669553
theorem B1113047 : Blo 1112627 1113047 := bstep (se 1 (by rfl) ⟨834785, by rfl⟩ : syracuseStep 1113047 = 1669571) B1669571
theorem B1670105 : Blo 1112627 1670105 := bstep (se 2 (by rfl) ⟨626289, by rfl⟩ : syracuseStep 1670105 = 1252579) B1252579
theorem B1113067 : Blo 1112627 1113067 := bstep (se 1 (by rfl) ⟨834800, by rfl⟩ : syracuseStep 1113067 = 1669601) B1669601
theorem B1113079 : Blo 1112627 1113079 := bstep (se 1 (by rfl) ⟨834809, by rfl⟩ : syracuseStep 1113079 = 1669619) B1669619
theorem B1113099 : Blo 1112627 1113099 := bstep (se 1 (by rfl) ⟨834824, by rfl⟩ : syracuseStep 1113099 = 1669649) B1669649
theorem B1113111 : Blo 1112627 1113111 := bstep (se 1 (by rfl) ⟨834833, by rfl⟩ : syracuseStep 1113111 = 1669667) B1669667
theorem B1113131 : Blo 1112627 1113131 := bstep (se 1 (by rfl) ⟨834848, by rfl⟩ : syracuseStep 1113131 = 1669697) B1669697
theorem B1113143 : Blo 1112627 1113143 := bstep (se 1 (by rfl) ⟨834857, by rfl⟩ : syracuseStep 1113143 = 1669715) B1669715
theorem B2817089 : Blo 1112627 2817089 := bstep (se 2 (by rfl) ⟨1056408, by rfl⟩ : syracuseStep 2817089 = 2112817) B2112817
theorem B1113163 : Blo 1112627 1113163 := bstep (se 1 (by rfl) ⟨834872, by rfl⟩ : syracuseStep 1113163 = 1669745) B1669745
theorem B1670219 : Blo 1112627 1670219 := bstep (se 1 (by rfl) ⟨1252664, by rfl⟩ : syracuseStep 1670219 = 2505329) B2505329
theorem B1113175 : Blo 1112627 1113175 := bstep (se 1 (by rfl) ⟨834881, by rfl⟩ : syracuseStep 1113175 = 1669763) B1669763
theorem B1670231 : Blo 1112627 1670231 := bstep (se 1 (by rfl) ⟨1252673, by rfl⟩ : syracuseStep 1670231 = 2505347) B2505347
theorem B1113195 : Blo 1112627 1113195 := bstep (se 1 (by rfl) ⟨834896, by rfl⟩ : syracuseStep 1113195 = 1669793) B1669793
theorem B1113207 : Blo 1112627 1113207 := bstep (se 1 (by rfl) ⟨834905, by rfl⟩ : syracuseStep 1113207 = 1669811) B1669811
theorem B1113227 : Blo 1112627 1113227 := bstep (se 1 (by rfl) ⟨834920, by rfl⟩ : syracuseStep 1113227 = 1669841) B1669841
theorem B1113239 : Blo 1112627 1113239 := bstep (se 1 (by rfl) ⟨834929, by rfl⟩ : syracuseStep 1113239 = 1669859) B1669859
theorem B1670297 : Blo 1112627 1670297 := bstep (se 2 (by rfl) ⟨626361, by rfl⟩ : syracuseStep 1670297 = 1252723) B1252723
theorem B1113259 : Blo 1112627 1113259 := bstep (se 1 (by rfl) ⟨834944, by rfl⟩ : syracuseStep 1113259 = 1669889) B1669889
theorem B1113271 : Blo 1112627 1113271 := bstep (se 1 (by rfl) ⟨834953, by rfl⟩ : syracuseStep 1113271 = 1669907) B1669907
theorem B1113291 : Blo 1112627 1113291 := bstep (se 1 (by rfl) ⟨834968, by rfl⟩ : syracuseStep 1113291 = 1669937) B1669937
theorem B1113303 : Blo 1112627 1113303 := bstep (se 1 (by rfl) ⟨834977, by rfl⟩ : syracuseStep 1113303 = 1669955) B1669955
theorem B1113323 : Blo 1112627 1113323 := bstep (se 1 (by rfl) ⟨834992, by rfl⟩ : syracuseStep 1113323 = 1669985) B1669985
theorem B1113335 : Blo 1112627 1113335 := bstep (se 1 (by rfl) ⟨835001, by rfl⟩ : syracuseStep 1113335 = 1670003) B1670003
theorem B1113355 : Blo 1112627 1113355 := bstep (se 1 (by rfl) ⟨835016, by rfl⟩ : syracuseStep 1113355 = 1670033) B1670033
theorem B1670411 : Blo 1112627 1670411 := bstep (se 1 (by rfl) ⟨1252808, by rfl⟩ : syracuseStep 1670411 = 2505617) B2505617
theorem B1113367 : Blo 1112627 1113367 := bstep (se 1 (by rfl) ⟨835025, by rfl⟩ : syracuseStep 1113367 = 1670051) B1670051
theorem B1670423 : Blo 1112627 1670423 := bstep (se 1 (by rfl) ⟨1252817, by rfl⟩ : syracuseStep 1670423 = 2505635) B2505635
theorem B1113387 : Blo 1112627 1113387 := bstep (se 1 (by rfl) ⟨835040, by rfl⟩ : syracuseStep 1113387 = 1670081) B1670081
theorem B1113399 : Blo 1112627 1113399 := bstep (se 1 (by rfl) ⟨835049, by rfl⟩ : syracuseStep 1113399 = 1670099) B1670099
theorem B1113419 : Blo 1112627 1113419 := bstep (se 1 (by rfl) ⟨835064, by rfl⟩ : syracuseStep 1113419 = 1670129) B1670129
theorem B1113431 : Blo 1112627 1113431 := bstep (se 1 (by rfl) ⟨835073, by rfl⟩ : syracuseStep 1113431 = 1670147) B1670147
theorem B1670489 : Blo 1112627 1670489 := bstep (se 2 (by rfl) ⟨626433, by rfl⟩ : syracuseStep 1670489 = 1252867) B1252867
theorem B1113451 : Blo 1112627 1113451 := bstep (se 1 (by rfl) ⟨835088, by rfl⟩ : syracuseStep 1113451 = 1670177) B1670177
theorem B1113463 : Blo 1112627 1113463 := bstep (se 1 (by rfl) ⟨835097, by rfl⟩ : syracuseStep 1113463 = 1670195) B1670195
theorem B1113483 : Blo 1112627 1113483 := bstep (se 1 (by rfl) ⟨835112, by rfl⟩ : syracuseStep 1113483 = 1670225) B1670225
theorem B1113495 : Blo 1112627 1113495 := bstep (se 1 (by rfl) ⟨835121, by rfl⟩ : syracuseStep 1113495 = 1670243) B1670243
theorem B1113515 : Blo 1112627 1113515 := bstep (se 1 (by rfl) ⟨835136, by rfl⟩ : syracuseStep 1113515 = 1670273) B1670273
theorem B1113527 : Blo 1112627 1113527 := bstep (se 1 (by rfl) ⟨835145, by rfl⟩ : syracuseStep 1113527 = 1670291) B1670291
theorem B1113547 : Blo 1112627 1113547 := bstep (se 1 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 1113547 = 1670321) B1670321
theorem B1670603 : Blo 1112627 1670603 := bstep (se 1 (by rfl) ⟨1252952, by rfl⟩ : syracuseStep 1670603 = 2505905) B2505905
theorem B1113559 : Blo 1112627 1113559 := bstep (se 1 (by rfl) ⟨835169, by rfl⟩ : syracuseStep 1113559 = 1670339) B1670339
theorem B1670615 : Blo 1112627 1670615 := bstep (se 1 (by rfl) ⟨1252961, by rfl⟩ : syracuseStep 1670615 = 2505923) B2505923
theorem B1113579 : Blo 1112627 1113579 := bstep (se 1 (by rfl) ⟨835184, by rfl⟩ : syracuseStep 1113579 = 1670369) B1670369
theorem B1113591 : Blo 1112627 1113591 := bstep (se 1 (by rfl) ⟨835193, by rfl⟩ : syracuseStep 1113591 = 1670387) B1670387
theorem B1113611 : Blo 1112627 1113611 := bstep (se 1 (by rfl) ⟨835208, by rfl⟩ : syracuseStep 1113611 = 1670417) B1670417
theorem B1113623 : Blo 1112627 1113623 := bstep (se 1 (by rfl) ⟨835217, by rfl⟩ : syracuseStep 1113623 = 1670435) B1670435
theorem B1670681 : Blo 1112627 1670681 := bstep (se 2 (by rfl) ⟨626505, by rfl⟩ : syracuseStep 1670681 = 1253011) B1253011
theorem B1113643 : Blo 1112627 1113643 := bstep (se 1 (by rfl) ⟨835232, by rfl⟩ : syracuseStep 1113643 = 1670465) B1670465
theorem B1113655 : Blo 1112627 1113655 := bstep (se 1 (by rfl) ⟨835241, by rfl⟩ : syracuseStep 1113655 = 1670483) B1670483
theorem B1113675 : Blo 1112627 1113675 := bstep (se 1 (by rfl) ⟨835256, by rfl⟩ : syracuseStep 1113675 = 1670513) B1670513
theorem B1113687 : Blo 1112627 1113687 := bstep (se 1 (by rfl) ⟨835265, by rfl⟩ : syracuseStep 1113687 = 1670531) B1670531
theorem B2817625 : Blo 1112627 2817625 := bstep (se 2 (by rfl) ⟨1056609, by rfl⟩ : syracuseStep 2817625 = 2113219) B2113219
theorem B1113707 : Blo 1112627 1113707 := bstep (se 1 (by rfl) ⟨835280, by rfl⟩ : syracuseStep 1113707 = 1670561) B1670561
theorem B1113719 : Blo 1112627 1113719 := bstep (se 1 (by rfl) ⟨835289, by rfl⟩ : syracuseStep 1113719 = 1670579) B1670579
theorem B1113739 : Blo 1112627 1113739 := bstep (se 1 (by rfl) ⟨835304, by rfl⟩ : syracuseStep 1113739 = 1670609) B1670609
theorem B1670795 : Blo 1112627 1670795 := bstep (se 1 (by rfl) ⟨1253096, by rfl⟩ : syracuseStep 1670795 = 2506193) B2506193
theorem B1113751 : Blo 1112627 1113751 := bstep (se 1 (by rfl) ⟨835313, by rfl⟩ : syracuseStep 1113751 = 1670627) B1670627
theorem B1670807 : Blo 1112627 1670807 := bstep (se 1 (by rfl) ⟨1253105, by rfl⟩ : syracuseStep 1670807 = 2506211) B2506211
theorem B1113771 : Blo 1112627 1113771 := bstep (se 1 (by rfl) ⟨835328, by rfl⟩ : syracuseStep 1113771 = 1670657) B1670657
theorem B1113783 : Blo 1112627 1113783 := bstep (se 1 (by rfl) ⟨835337, by rfl⟩ : syracuseStep 1113783 = 1670675) B1670675
theorem B1113803 : Blo 1112627 1113803 := bstep (se 1 (by rfl) ⟨835352, by rfl⟩ : syracuseStep 1113803 = 1670705) B1670705
theorem B3768011 : Blo 1112627 3768011 := bstep (se 1 (by rfl) ⟨2826008, by rfl⟩ : syracuseStep 3768011 = 5652017) B5652017
theorem B1113815 : Blo 1112627 1113815 := bstep (se 1 (by rfl) ⟨835361, by rfl⟩ : syracuseStep 1113815 = 1670723) B1670723
theorem B1670873 : Blo 1112627 1670873 := bstep (se 2 (by rfl) ⟨626577, by rfl⟩ : syracuseStep 1670873 = 1253155) B1253155
theorem B1113835 : Blo 1112627 1113835 := bstep (se 1 (by rfl) ⟨835376, by rfl⟩ : syracuseStep 1113835 = 1670753) B1670753
theorem B1113847 : Blo 1112627 1113847 := bstep (se 1 (by rfl) ⟨835385, by rfl⟩ : syracuseStep 1113847 = 1670771) B1670771
theorem B1113867 : Blo 1112627 1113867 := bstep (se 1 (by rfl) ⟨835400, by rfl⟩ : syracuseStep 1113867 = 1670801) B1670801
theorem B6782737 : Blo 1112627 6782737 := bstep (se 2 (by rfl) ⟨2543526, by rfl⟩ : syracuseStep 6782737 = 5087053) B5087053
theorem B1113879 : Blo 1112627 1113879 := bstep (se 1 (by rfl) ⟨835409, by rfl⟩ : syracuseStep 1113879 = 1670819) B1670819
theorem B1113899 : Blo 1112627 1113899 := bstep (se 1 (by rfl) ⟨835424, by rfl⟩ : syracuseStep 1113899 = 1670849) B1670849
theorem B1113911 : Blo 1112627 1113911 := bstep (se 1 (by rfl) ⟨835433, by rfl⟩ : syracuseStep 1113911 = 1670867) B1670867
theorem B1408843 : Blo 1112627 1408843 := bstep (se 1 (by rfl) ⟨1056632, by rfl⟩ : syracuseStep 1408843 = 2113265) B2113265
theorem B1113931 : Blo 1112627 1113931 := bstep (se 1 (by rfl) ⟨835448, by rfl⟩ : syracuseStep 1113931 = 1670897) B1670897
theorem B1670987 : Blo 1112627 1670987 := bstep (se 1 (by rfl) ⟨1253240, by rfl⟩ : syracuseStep 1670987 = 2506481) B2506481
theorem B1113943 : Blo 1112627 1113943 := bstep (se 1 (by rfl) ⟨835457, by rfl⟩ : syracuseStep 1113943 = 1670915) B1670915
theorem B1670999 : Blo 1112627 1670999 := bstep (se 1 (by rfl) ⟨1253249, by rfl⟩ : syracuseStep 1670999 = 2506499) B2506499
theorem B1113963 : Blo 1112627 1113963 := bstep (se 1 (by rfl) ⟨835472, by rfl⟩ : syracuseStep 1113963 = 1670945) B1670945
theorem B1113975 : Blo 1112627 1113975 := bstep (se 1 (by rfl) ⟨835481, by rfl⟩ : syracuseStep 1113975 = 1670963) B1670963
theorem B1113995 : Blo 1112627 1113995 := bstep (se 1 (by rfl) ⟨835496, by rfl⟩ : syracuseStep 1113995 = 1670993) B1670993
theorem B1114007 : Blo 1112627 1114007 := bstep (se 1 (by rfl) ⟨835505, by rfl⟩ : syracuseStep 1114007 = 1671011) B1671011
theorem B1671065 : Blo 1112627 1671065 := bstep (se 2 (by rfl) ⟨626649, by rfl⟩ : syracuseStep 1671065 = 1253299) B1253299
theorem B2260889 : Blo 1112627 2260889 := bstep (se 2 (by rfl) ⟨847833, by rfl⟩ : syracuseStep 2260889 = 1695667) B1695667
theorem B1114027 : Blo 1112627 1114027 := bstep (se 1 (by rfl) ⟨835520, by rfl⟩ : syracuseStep 1114027 = 1671041) B1671041
theorem B1114039 : Blo 1112627 1114039 := bstep (se 1 (by rfl) ⟨835529, by rfl⟩ : syracuseStep 1114039 = 1671059) B1671059
theorem B1114059 : Blo 1112627 1114059 := bstep (se 1 (by rfl) ⟨835544, by rfl⟩ : syracuseStep 1114059 = 1671089) B1671089
theorem B1114071 : Blo 1112627 1114071 := bstep (se 1 (by rfl) ⟨835553, by rfl⟩ : syracuseStep 1114071 = 1671107) B1671107
theorem B3768281 : Blo 1112627 3768281 := bstep (se 2 (by rfl) ⟨1413105, by rfl⟩ : syracuseStep 3768281 = 2826211) B2826211
theorem B1114091 : Blo 1112627 1114091 := bstep (se 1 (by rfl) ⟨835568, by rfl⟩ : syracuseStep 1114091 = 1671137) B1671137
theorem B1114103 : Blo 1112627 1114103 := bstep (se 1 (by rfl) ⟨835577, by rfl⟩ : syracuseStep 1114103 = 1671155) B1671155
theorem B1114119 : Blo 1112627 1114119 := bstep (se 1 (by rfl) ⟨835589, by rfl⟩ : syracuseStep 1114119 = 1671179) B1671179
theorem B1114127 : Blo 1112627 1114127 := bstep (se 1 (by rfl) ⟨835595, by rfl⟩ : syracuseStep 1114127 = 1671191) B1671191
theorem B2818091 : Blo 1112627 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B1671227 : Blo 1112627 1671227 := bstep (se 1 (by rfl) ⟨1253420, by rfl⟩ : syracuseStep 1671227 = 2506841) B2506841
theorem B1114171 : Blo 1112627 1114171 := bstep (se 1 (by rfl) ⟨835628, by rfl⟩ : syracuseStep 1114171 = 1671257) B1671257
theorem B1671287 : Blo 1112627 1671287 := bstep (se 1 (by rfl) ⟨1253465, by rfl⟩ : syracuseStep 1671287 = 2506931) B2506931
theorem B1114247 : Blo 1112627 1114247 := bstep (se 1 (by rfl) ⟨835685, by rfl⟩ : syracuseStep 1114247 = 1671371) B1671371
theorem B1409167 : Blo 1112627 1409167 := bstep (se 1 (by rfl) ⟨1056875, by rfl⟩ : syracuseStep 1409167 = 2113751) B2113751
theorem B1671311 : Blo 1112627 1671311 := bstep (se 1 (by rfl) ⟨1253483, by rfl⟩ : syracuseStep 1671311 = 2506967) B2506967
theorem B1114255 : Blo 1112627 1114255 := bstep (se 1 (by rfl) ⟨835691, by rfl⟩ : syracuseStep 1114255 = 1671383) B1671383
theorem B1671353 : Blo 1112627 1671353 := bstep (se 2 (by rfl) ⟨626757, by rfl⟩ : syracuseStep 1671353 = 1253515) B1253515
theorem B1114299 : Blo 1112627 1114299 := bstep (se 1 (by rfl) ⟨835724, by rfl⟩ : syracuseStep 1114299 = 1671449) B1671449
theorem B1671431 : Blo 1112627 1671431 := bstep (se 1 (by rfl) ⟨1253573, by rfl⟩ : syracuseStep 1671431 = 2507147) B2507147
theorem B1114375 : Blo 1112627 1114375 := bstep (se 1 (by rfl) ⟨835781, by rfl⟩ : syracuseStep 1114375 = 1671563) B1671563
theorem B1114383 : Blo 1112627 1114383 := bstep (se 1 (by rfl) ⟨835787, by rfl⟩ : syracuseStep 1114383 = 1671575) B1671575
theorem B1671467 : Blo 1112627 1671467 := bstep (se 1 (by rfl) ⟨1253600, by rfl⟩ : syracuseStep 1671467 = 2507201) B2507201
theorem B1409339 : Blo 1112627 1409339 := bstep (se 1 (by rfl) ⟨1057004, by rfl⟩ : syracuseStep 1409339 = 2114009) B2114009
theorem B1114427 : Blo 1112627 1114427 := bstep (se 1 (by rfl) ⟨835820, by rfl⟩ : syracuseStep 1114427 = 1671641) B1671641
theorem B1671497 : Blo 1112627 1671497 := bstep (se 2 (by rfl) ⟨626811, by rfl⟩ : syracuseStep 1671497 = 1253623) B1253623
theorem B1114503 : Blo 1112627 1114503 := bstep (se 1 (by rfl) ⟨835877, by rfl⟩ : syracuseStep 1114503 = 1671755) B1671755
theorem B1114511 : Blo 1112627 1114511 := bstep (se 1 (by rfl) ⟨835883, by rfl⟩ : syracuseStep 1114511 = 1671767) B1671767
theorem B1671611 : Blo 1112627 1671611 := bstep (se 1 (by rfl) ⟨1253708, by rfl⟩ : syracuseStep 1671611 = 2507417) B2507417
theorem B1114555 : Blo 1112627 1114555 := bstep (se 1 (by rfl) ⟨835916, by rfl⟩ : syracuseStep 1114555 = 1671833) B1671833
theorem B1671671 : Blo 1112627 1671671 := bstep (se 1 (by rfl) ⟨1253753, by rfl⟩ : syracuseStep 1671671 = 2507507) B2507507
theorem B1114631 : Blo 1112627 1114631 := bstep (se 1 (by rfl) ⟨835973, by rfl⟩ : syracuseStep 1114631 = 1671947) B1671947
theorem B1671695 : Blo 1112627 1671695 := bstep (se 1 (by rfl) ⟨1253771, by rfl⟩ : syracuseStep 1671695 = 2507543) B2507543
theorem B1114639 : Blo 1112627 1114639 := bstep (se 1 (by rfl) ⟨835979, by rfl⟩ : syracuseStep 1114639 = 1671959) B1671959
theorem B1671737 : Blo 1112627 1671737 := bstep (se 2 (by rfl) ⟨626901, by rfl⟩ : syracuseStep 1671737 = 1253803) B1253803
theorem B1114683 : Blo 1112627 1114683 := bstep (se 1 (by rfl) ⟨836012, by rfl⟩ : syracuseStep 1114683 = 1672025) B1672025
theorem B1671815 : Blo 1112627 1671815 := bstep (se 1 (by rfl) ⟨1253861, by rfl⟩ : syracuseStep 1671815 = 2507723) B2507723
theorem B1114759 : Blo 1112627 1114759 := bstep (se 1 (by rfl) ⟨836069, by rfl⟩ : syracuseStep 1114759 = 1672139) B1672139
theorem B1114767 : Blo 1112627 1114767 := bstep (se 1 (by rfl) ⟨836075, by rfl⟩ : syracuseStep 1114767 = 1672151) B1672151
theorem B1671851 : Blo 1112627 1671851 := bstep (se 1 (by rfl) ⟨1253888, by rfl⟩ : syracuseStep 1671851 = 2507777) B2507777
theorem B1114811 : Blo 1112627 1114811 := bstep (se 1 (by rfl) ⟨836108, by rfl⟩ : syracuseStep 1114811 = 1672217) B1672217
theorem B1671881 : Blo 1112627 1671881 := bstep (se 2 (by rfl) ⟨626955, by rfl⟩ : syracuseStep 1671881 = 1253911) B1253911
theorem B4227821 : Blo 1112627 4227821 := bstep (se 3 (by rfl) ⟨792716, by rfl⟩ : syracuseStep 4227821 = 1585433) B1585433
theorem B1114887 : Blo 1112627 1114887 := bstep (se 1 (by rfl) ⟨836165, by rfl⟩ : syracuseStep 1114887 = 1672331) B1672331
theorem B1114895 : Blo 1112627 1114895 := bstep (se 1 (by rfl) ⟨836171, by rfl⟩ : syracuseStep 1114895 = 1672343) B1672343
theorem B1671995 : Blo 1112627 1671995 := bstep (se 1 (by rfl) ⟨1253996, by rfl⟩ : syracuseStep 1671995 = 2507993) B2507993
theorem B1114939 : Blo 1112627 1114939 := bstep (se 1 (by rfl) ⟨836204, by rfl⟩ : syracuseStep 1114939 = 1672409) B1672409
theorem B3179351 : Blo 1112627 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B1672055 : Blo 1112627 1672055 := bstep (se 1 (by rfl) ⟨1254041, by rfl⟩ : syracuseStep 1672055 = 2508083) B2508083
theorem B1115015 : Blo 1112627 1115015 := bstep (se 1 (by rfl) ⟨836261, by rfl⟩ : syracuseStep 1115015 = 1672523) B1672523
theorem B1672079 : Blo 1112627 1672079 := bstep (se 1 (by rfl) ⟨1254059, by rfl⟩ : syracuseStep 1672079 = 2508119) B2508119
theorem B1115023 : Blo 1112627 1115023 := bstep (se 1 (by rfl) ⟨836267, by rfl⟩ : syracuseStep 1115023 = 1672535) B1672535
theorem B1672121 : Blo 1112627 1672121 := bstep (se 2 (by rfl) ⟨627045, by rfl⟩ : syracuseStep 1672121 = 1254091) B1254091
theorem B1115067 : Blo 1112627 1115067 := bstep (se 1 (by rfl) ⟨836300, by rfl⟩ : syracuseStep 1115067 = 1672601) B1672601
theorem B1672199 : Blo 1112627 1672199 := bstep (se 1 (by rfl) ⟨1254149, by rfl⟩ : syracuseStep 1672199 = 2508299) B2508299
theorem B1115143 : Blo 1112627 1115143 := bstep (se 1 (by rfl) ⟨836357, by rfl⟩ : syracuseStep 1115143 = 1672715) B1672715
theorem B2819083 : Blo 1112627 2819083 := bstep (se 1 (by rfl) ⟨2114312, by rfl⟩ : syracuseStep 2819083 = 4228625) B4228625
theorem B1115151 : Blo 1112627 1115151 := bstep (se 1 (by rfl) ⟨836363, by rfl⟩ : syracuseStep 1115151 = 1672727) B1672727
theorem B4228139 : Blo 1112627 4228139 := bstep (se 1 (by rfl) ⟨3171104, by rfl⟩ : syracuseStep 4228139 = 6342209) B6342209
theorem B1672235 : Blo 1112627 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B1115195 : Blo 1112627 1115195 := bstep (se 1 (by rfl) ⟨836396, by rfl⟩ : syracuseStep 1115195 = 1672793) B1672793
theorem B1672265 : Blo 1112627 1672265 := bstep (se 2 (by rfl) ⟨627099, by rfl⟩ : syracuseStep 1672265 = 1254199) B1254199
theorem B1115271 : Blo 1112627 1115271 := bstep (se 1 (by rfl) ⟨836453, by rfl⟩ : syracuseStep 1115271 = 1672907) B1672907
theorem B1115279 : Blo 1112627 1115279 := bstep (se 1 (by rfl) ⟨836459, by rfl⟩ : syracuseStep 1115279 = 1672919) B1672919
theorem B2819225 : Blo 1112627 2819225 := bstep (se 2 (by rfl) ⟨1057209, by rfl⟩ : syracuseStep 2819225 = 2114419) B2114419
theorem B1672379 : Blo 1112627 1672379 := bstep (se 1 (by rfl) ⟨1254284, by rfl⟩ : syracuseStep 1672379 = 2508569) B2508569
theorem B1115323 : Blo 1112627 1115323 := bstep (se 1 (by rfl) ⟨836492, by rfl⟩ : syracuseStep 1115323 = 1672985) B1672985
theorem B1672439 : Blo 1112627 1672439 := bstep (se 1 (by rfl) ⟨1254329, by rfl⟩ : syracuseStep 1672439 = 2508659) B2508659
theorem B1410311 : Blo 1112627 1410311 := bstep (se 1 (by rfl) ⟨1057733, by rfl⟩ : syracuseStep 1410311 = 2115467) B2115467
theorem B1115399 : Blo 1112627 1115399 := bstep (se 1 (by rfl) ⟨836549, by rfl⟩ : syracuseStep 1115399 = 1673099) B1673099
theorem B1672463 : Blo 1112627 1672463 := bstep (se 1 (by rfl) ⟨1254347, by rfl⟩ : syracuseStep 1672463 = 2508695) B2508695
theorem B1115407 : Blo 1112627 1115407 := bstep (se 1 (by rfl) ⟨836555, by rfl⟩ : syracuseStep 1115407 = 1673111) B1673111
theorem B1672505 : Blo 1112627 1672505 := bstep (se 2 (by rfl) ⟨627189, by rfl⟩ : syracuseStep 1672505 = 1254379) B1254379
theorem B2819387 : Blo 1112627 2819387 := bstep (se 1 (by rfl) ⟨2114540, by rfl⟩ : syracuseStep 2819387 = 4229081) B4229081
theorem B1115451 : Blo 1112627 1115451 := bstep (se 1 (by rfl) ⟨836588, by rfl⟩ : syracuseStep 1115451 = 1673177) B1673177
theorem B3015997 : Blo 1112627 3015997 := bstep (se 3 (by rfl) ⟨565499, by rfl⟩ : syracuseStep 3015997 = 1130999) B1130999
theorem B1672583 : Blo 1112627 1672583 := bstep (se 1 (by rfl) ⟨1254437, by rfl⟩ : syracuseStep 1672583 = 2508875) B2508875
theorem B1115527 : Blo 1112627 1115527 := bstep (se 1 (by rfl) ⟨836645, by rfl⟩ : syracuseStep 1115527 = 1673291) B1673291
theorem B1115535 : Blo 1112627 1115535 := bstep (se 1 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 1115535 = 1673303) B1673303
theorem B1672619 : Blo 1112627 1672619 := bstep (se 1 (by rfl) ⟨1254464, by rfl⟩ : syracuseStep 1672619 = 2508929) B2508929
theorem B1115579 : Blo 1112627 1115579 := bstep (se 1 (by rfl) ⟨836684, by rfl⟩ : syracuseStep 1115579 = 1673369) B1673369
theorem B1672649 : Blo 1112627 1672649 := bstep (se 2 (by rfl) ⟨627243, by rfl⟩ : syracuseStep 1672649 = 1254487) B1254487
theorem B1115655 : Blo 1112627 1115655 := bstep (se 1 (by rfl) ⟨836741, by rfl⟩ : syracuseStep 1115655 = 1673483) B1673483
theorem B1115663 : Blo 1112627 1115663 := bstep (se 1 (by rfl) ⟨836747, by rfl⟩ : syracuseStep 1115663 = 1673495) B1673495
theorem B1672763 : Blo 1112627 1672763 := bstep (se 1 (by rfl) ⟨1254572, by rfl⟩ : syracuseStep 1672763 = 2509145) B2509145
theorem B1115707 : Blo 1112627 1115707 := bstep (se 1 (by rfl) ⟨836780, by rfl⟩ : syracuseStep 1115707 = 1673561) B1673561
theorem B1672823 : Blo 1112627 1672823 := bstep (se 1 (by rfl) ⟨1254617, by rfl⟩ : syracuseStep 1672823 = 2509235) B2509235
theorem B1115783 : Blo 1112627 1115783 := bstep (se 1 (by rfl) ⟨836837, by rfl⟩ : syracuseStep 1115783 = 1673675) B1673675
theorem B1672847 : Blo 1112627 1672847 := bstep (se 1 (by rfl) ⟨1254635, by rfl⟩ : syracuseStep 1672847 = 2509271) B2509271
theorem B1115791 : Blo 1112627 1115791 := bstep (se 1 (by rfl) ⟨836843, by rfl⟩ : syracuseStep 1115791 = 1673687) B1673687
theorem B2819731 : Blo 1112627 2819731 := bstep (se 1 (by rfl) ⟨2114798, by rfl⟩ : syracuseStep 2819731 = 4229597) B4229597
theorem B1672889 : Blo 1112627 1672889 := bstep (se 2 (by rfl) ⟨627333, by rfl⟩ : syracuseStep 1672889 = 1254667) B1254667
theorem B1115835 : Blo 1112627 1115835 := bstep (se 1 (by rfl) ⟨836876, by rfl⟩ : syracuseStep 1115835 = 1673753) B1673753
theorem B1672967 : Blo 1112627 1672967 := bstep (se 1 (by rfl) ⟨1254725, by rfl⟩ : syracuseStep 1672967 = 2509451) B2509451
theorem B1115911 : Blo 1112627 1115911 := bstep (se 1 (by rfl) ⟨836933, by rfl⟩ : syracuseStep 1115911 = 1673867) B1673867
theorem B1115919 : Blo 1112627 1115919 := bstep (se 1 (by rfl) ⟨836939, by rfl⟩ : syracuseStep 1115919 = 1673879) B1673879
theorem B2819873 : Blo 1112627 2819873 := bstep (se 2 (by rfl) ⟨1057452, by rfl⟩ : syracuseStep 2819873 = 2114905) B2114905
theorem B1673003 : Blo 1112627 1673003 := bstep (se 1 (by rfl) ⟨1254752, by rfl⟩ : syracuseStep 1673003 = 2509505) B2509505
theorem B1115963 : Blo 1112627 1115963 := bstep (se 1 (by rfl) ⟨836972, by rfl⟩ : syracuseStep 1115963 = 1673945) B1673945
theorem B1673033 : Blo 1112627 1673033 := bstep (se 2 (by rfl) ⟨627387, by rfl⟩ : syracuseStep 1673033 = 1254775) B1254775
theorem B1116039 : Blo 1112627 1116039 := bstep (se 1 (by rfl) ⟨837029, by rfl⟩ : syracuseStep 1116039 = 1674059) B1674059
theorem B1410959 : Blo 1112627 1410959 := bstep (se 1 (by rfl) ⟨1058219, by rfl⟩ : syracuseStep 1410959 = 2116439) B2116439
theorem B1116047 : Blo 1112627 1116047 := bstep (se 1 (by rfl) ⟨837035, by rfl⟩ : syracuseStep 1116047 = 1674071) B1674071
theorem B3016595 : Blo 1112627 3016595 := bstep (se 1 (by rfl) ⟨2262446, by rfl⟩ : syracuseStep 3016595 = 4524893) B4524893
theorem B6358931 : Blo 1112627 6358931 := bstep (se 1 (by rfl) ⟨4769198, by rfl⟩ : syracuseStep 6358931 = 9538397) B9538397
theorem B1673147 : Blo 1112627 1673147 := bstep (se 1 (by rfl) ⟨1254860, by rfl⟩ : syracuseStep 1673147 = 2509721) B2509721
theorem B1116091 : Blo 1112627 1116091 := bstep (se 1 (by rfl) ⟨837068, by rfl⟩ : syracuseStep 1116091 = 1674137) B1674137
theorem B1673207 : Blo 1112627 1673207 := bstep (se 1 (by rfl) ⟨1254905, by rfl⟩ : syracuseStep 1673207 = 2509811) B2509811
theorem B1116167 : Blo 1112627 1116167 := bstep (se 1 (by rfl) ⟨837125, by rfl⟩ : syracuseStep 1116167 = 1674251) B1674251
theorem B1673231 : Blo 1112627 1673231 := bstep (se 1 (by rfl) ⟨1254923, by rfl⟩ : syracuseStep 1673231 = 2509847) B2509847
theorem B1116175 : Blo 1112627 1116175 := bstep (se 1 (by rfl) ⟨837131, by rfl⟩ : syracuseStep 1116175 = 1674263) B1674263
theorem B1673273 : Blo 1112627 1673273 := bstep (se 2 (by rfl) ⟨627477, by rfl⟩ : syracuseStep 1673273 = 1254955) B1254955
theorem B1116219 : Blo 1112627 1116219 := bstep (se 1 (by rfl) ⟨837164, by rfl⟩ : syracuseStep 1116219 = 1674329) B1674329
theorem B1673351 : Blo 1112627 1673351 := bstep (se 1 (by rfl) ⟨1255013, by rfl⟩ : syracuseStep 1673351 = 2510027) B2510027
theorem B1116295 : Blo 1112627 1116295 := bstep (se 1 (by rfl) ⟨837221, by rfl⟩ : syracuseStep 1116295 = 1674443) B1674443
theorem B1116303 : Blo 1112627 1116303 := bstep (se 1 (by rfl) ⟨837227, by rfl⟩ : syracuseStep 1116303 = 1674455) B1674455
theorem B1673387 : Blo 1112627 1673387 := bstep (se 1 (by rfl) ⟨1255040, by rfl⟩ : syracuseStep 1673387 = 2510081) B2510081
theorem B1116347 : Blo 1112627 1116347 := bstep (se 1 (by rfl) ⟨837260, by rfl⟩ : syracuseStep 1116347 = 1674521) B1674521
theorem B1673417 : Blo 1112627 1673417 := bstep (se 2 (by rfl) ⟨627531, by rfl⟩ : syracuseStep 1673417 = 1255063) B1255063
theorem B1116423 : Blo 1112627 1116423 := bstep (se 1 (by rfl) ⟨837317, by rfl⟩ : syracuseStep 1116423 = 1674635) B1674635
theorem B1116431 : Blo 1112627 1116431 := bstep (se 1 (by rfl) ⟨837323, by rfl⟩ : syracuseStep 1116431 = 1674647) B1674647
theorem B1673531 : Blo 1112627 1673531 := bstep (se 1 (by rfl) ⟨1255148, by rfl⟩ : syracuseStep 1673531 = 2510297) B2510297
theorem B1116475 : Blo 1112627 1116475 := bstep (se 1 (by rfl) ⟨837356, by rfl⟩ : syracuseStep 1116475 = 1674713) B1674713
theorem B1673591 : Blo 1112627 1673591 := bstep (se 1 (by rfl) ⟨1255193, by rfl⟩ : syracuseStep 1673591 = 2510387) B2510387
theorem B1116551 : Blo 1112627 1116551 := bstep (se 1 (by rfl) ⟨837413, by rfl⟩ : syracuseStep 1116551 = 1674827) B1674827
theorem B6359431 : Blo 1112627 6359431 := bstep (se 1 (by rfl) ⟨4769573, by rfl⟩ : syracuseStep 6359431 = 9539147) B9539147
theorem B1673615 : Blo 1112627 1673615 := bstep (se 1 (by rfl) ⟨1255211, by rfl⟩ : syracuseStep 1673615 = 2510423) B2510423
theorem B1116559 : Blo 1112627 1116559 := bstep (se 1 (by rfl) ⟨837419, by rfl⟩ : syracuseStep 1116559 = 1674839) B1674839
theorem B1673657 : Blo 1112627 1673657 := bstep (se 2 (by rfl) ⟨627621, by rfl⟩ : syracuseStep 1673657 = 1255243) B1255243
theorem B1116603 : Blo 1112627 1116603 := bstep (se 1 (by rfl) ⟨837452, by rfl⟩ : syracuseStep 1116603 = 1674905) B1674905
theorem B4819409 : Blo 1112627 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B1673735 : Blo 1112627 1673735 := bstep (se 1 (by rfl) ⟨1255301, by rfl⟩ : syracuseStep 1673735 = 2510603) B2510603
theorem B1673771 : Blo 1112627 1673771 := bstep (se 1 (by rfl) ⟨1255328, by rfl⟩ : syracuseStep 1673771 = 2510657) B2510657
theorem B1673801 : Blo 1112627 1673801 := bstep (se 2 (by rfl) ⟨627675, by rfl⟩ : syracuseStep 1673801 = 1255351) B1255351
theorem B1673915 : Blo 1112627 1673915 := bstep (se 1 (by rfl) ⟨1255436, by rfl⟩ : syracuseStep 1673915 = 2510873) B2510873
theorem B1673975 : Blo 1112627 1673975 := bstep (se 1 (by rfl) ⟨1255481, by rfl⟩ : syracuseStep 1673975 = 2510963) B2510963
theorem B2820865 : Blo 1112627 2820865 := bstep (se 2 (by rfl) ⟨1057824, by rfl⟩ : syracuseStep 2820865 = 2115649) B2115649
theorem B1673999 : Blo 1112627 1673999 := bstep (se 1 (by rfl) ⟨1255499, by rfl⟩ : syracuseStep 1673999 = 2510999) B2510999
theorem B5802803 : Blo 1112627 5802803 := bstep (se 1 (by rfl) ⟨4352102, by rfl⟩ : syracuseStep 5802803 = 8704205) B8704205
theorem B1674041 : Blo 1112627 1674041 := bstep (se 2 (by rfl) ⟨627765, by rfl⟩ : syracuseStep 1674041 = 1255531) B1255531
theorem B6785851 : Blo 1112627 6785851 := bstep (se 1 (by rfl) ⟨5089388, by rfl⟩ : syracuseStep 6785851 = 10178777) B10178777
theorem B1674119 : Blo 1112627 1674119 := bstep (se 1 (by rfl) ⟨1255589, by rfl⟩ : syracuseStep 1674119 = 2511179) B2511179
theorem B5639057 : Blo 1112627 5639057 := bstep (se 2 (by rfl) ⟨2114646, by rfl⟩ : syracuseStep 5639057 = 4229293) B4229293
theorem B1674155 : Blo 1112627 1674155 := bstep (se 1 (by rfl) ⟨1255616, by rfl⟩ : syracuseStep 1674155 = 2511233) B2511233
theorem B1674185 : Blo 1112627 1674185 := bstep (se 2 (by rfl) ⟨627819, by rfl⟩ : syracuseStep 1674185 = 1255639) B1255639
theorem B1674299 : Blo 1112627 1674299 := bstep (se 1 (by rfl) ⟨1255724, by rfl⟩ : syracuseStep 1674299 = 2511449) B2511449
theorem B1674359 : Blo 1112627 1674359 := bstep (se 1 (by rfl) ⟨1255769, by rfl⟩ : syracuseStep 1674359 = 2511539) B2511539
theorem B1674383 : Blo 1112627 1674383 := bstep (se 1 (by rfl) ⟨1255787, by rfl⟩ : syracuseStep 1674383 = 2511575) B2511575
theorem B1674425 : Blo 1112627 1674425 := bstep (se 2 (by rfl) ⟨627909, by rfl⟩ : syracuseStep 1674425 = 1255819) B1255819
theorem B1674503 : Blo 1112627 1674503 := bstep (se 1 (by rfl) ⟨1255877, by rfl⟩ : syracuseStep 1674503 = 2511755) B2511755
theorem B1674539 : Blo 1112627 1674539 := bstep (se 1 (by rfl) ⟨1255904, by rfl⟩ : syracuseStep 1674539 = 2511809) B2511809
theorem B1609033 : Blo 1112627 1609033 := bstep (se 2 (by rfl) ⟨603387, by rfl⟩ : syracuseStep 1609033 = 1206775) B1206775
theorem B1674569 : Blo 1112627 1674569 := bstep (se 2 (by rfl) ⟨627963, by rfl⟩ : syracuseStep 1674569 = 1255927) B1255927
theorem B2821463 : Blo 1112627 2821463 := bstep (se 1 (by rfl) ⟨2116097, by rfl⟩ : syracuseStep 2821463 = 4232195) B4232195
theorem B1674683 : Blo 1112627 1674683 := bstep (se 1 (by rfl) ⟨1256012, by rfl⟩ : syracuseStep 1674683 = 2512025) B2512025
theorem B1674743 : Blo 1112627 1674743 := bstep (se 1 (by rfl) ⟨1256057, by rfl⟩ : syracuseStep 1674743 = 2512115) B2512115
theorem B1674767 : Blo 1112627 1674767 := bstep (se 1 (by rfl) ⟨1256075, by rfl⟩ : syracuseStep 1674767 = 2512151) B2512151
theorem B2821675 : Blo 1112627 2821675 := bstep (se 1 (by rfl) ⟨2116256, by rfl⟩ : syracuseStep 2821675 = 4232513) B4232513
theorem B1674809 : Blo 1112627 1674809 := bstep (se 2 (by rfl) ⟨628053, by rfl⟩ : syracuseStep 1674809 = 1256107) B1256107
theorem B1674887 : Blo 1112627 1674887 := bstep (se 1 (by rfl) ⟨1256165, by rfl⟩ : syracuseStep 1674887 = 2512331) B2512331
theorem B1674923 : Blo 1112627 1674923 := bstep (se 1 (by rfl) ⟨1256192, by rfl⟩ : syracuseStep 1674923 = 2512385) B2512385
theorem B2821817 : Blo 1112627 2821817 := bstep (se 2 (by rfl) ⟨1058181, by rfl⟩ : syracuseStep 2821817 = 2116363) B2116363
theorem B7147237 : Blo 1112627 7147237 := bstep (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) B1340107
theorem B4526009 : Blo 1112627 4526009 := bstep (se 2 (by rfl) ⟨1697253, by rfl⟩ : syracuseStep 4526009 = 3394507) B3394507
theorem B3051535 : Blo 1112627 3051535 := bstep (se 1 (by rfl) ⟨2288651, by rfl⟩ : syracuseStep 3051535 = 4577303) B4577303
theorem B3576079 : Blo 1112627 3576079 := bstep (se 1 (by rfl) ⟨2682059, by rfl⟩ : syracuseStep 3576079 = 5364119) B5364119
theorem B2855227 : Blo 1112627 2855227 := bstep (se 1 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 2855227 = 4282841) B4282841
theorem B9507131 : Blo 1112627 9507131 := bstep (se 1 (by rfl) ⟨7130348, by rfl⟩ : syracuseStep 9507131 = 14260697) B14260697
theorem B4231709 : Blo 1112627 4231709 := bstep (se 3 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 4231709 = 1586891) B1586891
theorem B4231723 : Blo 1112627 4231723 := bstep (se 1 (by rfl) ⟨3173792, by rfl⟩ : syracuseStep 4231723 = 6347585) B6347585
theorem B8458829 : Blo 1112627 8458829 := bstep (se 3 (by rfl) ⟨1586030, by rfl⟩ : syracuseStep 8458829 = 3172061) B3172061
theorem B1806967 : Blo 1112627 1806967 := bstep (se 1 (by rfl) ⟨1355225, by rfl⟩ : syracuseStep 1806967 = 2710451) B2710451
theorem B2822809 : Blo 1112627 2822809 := bstep (se 2 (by rfl) ⟨1058553, by rfl⟩ : syracuseStep 2822809 = 2117107) B2117107
theorem B2822971 : Blo 1112627 2822971 := bstep (se 1 (by rfl) ⟨2117228, by rfl⟩ : syracuseStep 2822971 = 4234457) B4234457
theorem B2823113 : Blo 1112627 2823113 := bstep (se 2 (by rfl) ⟨1058667, by rfl⟩ : syracuseStep 2823113 = 2117335) B2117335
theorem B5641163 : Blo 1112627 5641163 := bstep (se 1 (by rfl) ⟨4230872, by rfl⟩ : syracuseStep 5641163 = 8461745) B8461745
theorem B5641487 : Blo 1112627 5641487 := bstep (se 1 (by rfl) ⟨4231115, by rfl⟩ : syracuseStep 5641487 = 8462231) B8462231
theorem B17143073 : Blo 1112627 17143073 := bstep (se 2 (by rfl) ⟨6428652, by rfl⟩ : syracuseStep 17143073 = 12857305) B12857305
theorem B2823457 : Blo 1112627 2823457 := bstep (se 2 (by rfl) ⟨1058796, by rfl⟩ : syracuseStep 2823457 = 2117593) B2117593
theorem B5346935 : Blo 1112627 5346935 := bstep (se 1 (by rfl) ⟨4010201, by rfl⟩ : syracuseStep 5346935 = 8020403) B8020403
theorem B2824055 : Blo 1112627 2824055 := bstep (se 1 (by rfl) ⟨2118041, by rfl⟩ : syracuseStep 2824055 = 4236083) B4236083
theorem B7346465 : Blo 1112627 7346465 := bstep (se 2 (by rfl) ⟨2754924, by rfl⟩ : syracuseStep 7346465 = 5509849) B5509849
theorem B5642945 : Blo 1112627 5642945 := bstep (se 2 (by rfl) ⟨2116104, by rfl⟩ : syracuseStep 5642945 = 4232209) B4232209
theorem B1252111 : Blo 1112627 1252111 := bstep (se 1 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 1252111 = 1878167) B1878167
theorem B2005793 : Blo 1112627 2005793 := bstep (se 2 (by rfl) ⟨752172, by rfl⟩ : syracuseStep 2005793 = 1504345) B1504345
theorem B12229465 : Blo 1112627 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B2005879 : Blo 1112627 2005879 := bstep (se 1 (by rfl) ⟨1504409, by rfl⟩ : syracuseStep 2005879 = 3008819) B3008819
theorem B8461259 : Blo 1112627 8461259 := bstep (se 1 (by rfl) ⟨6345944, by rfl⟩ : syracuseStep 8461259 = 12691889) B12691889
theorem B2825351 : Blo 1112627 2825351 := bstep (se 1 (by rfl) ⟨2119013, by rfl⟩ : syracuseStep 2825351 = 4238027) B4238027
theorem B2825401 : Blo 1112627 2825401 := bstep (se 2 (by rfl) ⟨1059525, by rfl⟩ : syracuseStep 2825401 = 2119051) B2119051
theorem B1252615 : Blo 1112627 1252615 := bstep (se 1 (by rfl) ⟨939461, by rfl⟩ : syracuseStep 1252615 = 1878923) B1878923
theorem B1252795 : Blo 1112627 1252795 := bstep (se 1 (by rfl) ⟨939596, by rfl⟩ : syracuseStep 1252795 = 1879193) B1879193
theorem B3055133 : Blo 1112627 3055133 := bstep (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) B1145675
theorem B9510443 : Blo 1112627 9510443 := bstep (se 1 (by rfl) ⟨7132832, by rfl⟩ : syracuseStep 9510443 = 14265665) B14265665
theorem B12688973 : Blo 1112627 12688973 := bstep (se 3 (by rfl) ⟨2379182, by rfl⟩ : syracuseStep 12688973 = 4758365) B4758365
theorem B19570355 : Blo 1112627 19570355 := bstep (se 1 (by rfl) ⟨14677766, by rfl⟩ : syracuseStep 19570355 = 29355533) B29355533
theorem B8822465 : Blo 1112627 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B1908425 : Blo 1112627 1908425 := bstep (se 2 (by rfl) ⟨715659, by rfl⟩ : syracuseStep 1908425 = 1431319) B1431319
theorem B2825999 : Blo 1112627 2825999 := bstep (se 1 (by rfl) ⟨2119499, by rfl⟩ : syracuseStep 2825999 = 4238999) B4238999
theorem B45817649 : Blo 1112627 45817649 := bstep (se 2 (by rfl) ⟨17181618, by rfl⟩ : syracuseStep 45817649 = 34363237) B34363237
theorem B1253263 : Blo 1112627 1253263 := bstep (se 1 (by rfl) ⟨939947, by rfl⟩ : syracuseStep 1253263 = 1879895) B1879895
theorem B5644241 : Blo 1112627 5644241 := bstep (se 2 (by rfl) ⟨2116590, by rfl⟩ : syracuseStep 5644241 = 4233181) B4233181
theorem B5349665 : Blo 1112627 5349665 := bstep (se 2 (by rfl) ⟨2006124, by rfl⟩ : syracuseStep 5349665 = 4012249) B4012249
theorem B1253767 : Blo 1112627 1253767 := bstep (se 1 (by rfl) ⟨940325, by rfl⟩ : syracuseStep 1253767 = 1880651) B1880651
theorem B5349779 : Blo 1112627 5349779 := bstep (se 1 (by rfl) ⟨4012334, by rfl⟩ : syracuseStep 5349779 = 8024669) B8024669
theorem B3383851 : Blo 1112627 3383851 := bstep (se 1 (by rfl) ⟨2537888, by rfl⟩ : syracuseStep 3383851 = 5075777) B5075777
theorem B1253947 : Blo 1112627 1253947 := bstep (se 1 (by rfl) ⟨940460, by rfl⟩ : syracuseStep 1253947 = 1880921) B1880921
theorem B30483125 : Blo 1112627 30483125 := bstep (se 5 (by rfl) ⟨1428896, by rfl⟩ : syracuseStep 30483125 = 2857793) B2857793
theorem B1254415 : Blo 1112627 1254415 := bstep (se 1 (by rfl) ⟨940811, by rfl⟩ : syracuseStep 1254415 = 1881623) B1881623
theorem B25732333 : Blo 1112627 25732333 := bstep (se 3 (by rfl) ⟨4824812, by rfl⟩ : syracuseStep 25732333 = 9649625) B9649625
theorem B1254919 : Blo 1112627 1254919 := bstep (se 1 (by rfl) ⟨941189, by rfl⟩ : syracuseStep 1254919 = 1882379) B1882379
theorem B4236887 : Blo 1112627 4236887 := bstep (se 1 (by rfl) ⟨3177665, by rfl⟩ : syracuseStep 4236887 = 6355331) B6355331
theorem B1255099 : Blo 1112627 1255099 := bstep (se 1 (by rfl) ⟨941324, by rfl⟩ : syracuseStep 1255099 = 1882649) B1882649
theorem B1189895 : Blo 1112627 1189895 := bstep (se 1 (by rfl) ⟨892421, by rfl⟩ : syracuseStep 1189895 = 1784843) B1784843
theorem B5646347 : Blo 1112627 5646347 := bstep (se 1 (by rfl) ⟨4234760, by rfl⟩ : syracuseStep 5646347 = 8469521) B8469521
theorem B5351453 : Blo 1112627 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B1878059 : Blo 1112627 1878059 := bstep (se 1 (by rfl) ⟨1408544, by rfl⟩ : syracuseStep 1878059 = 2817089) B2817089
theorem B4237373 : Blo 1112627 4237373 := bstep (se 3 (by rfl) ⟨794507, by rfl⟩ : syracuseStep 4237373 = 1589015) B1589015
theorem B1255567 : Blo 1112627 1255567 := bstep (se 1 (by rfl) ⟨941675, by rfl⟩ : syracuseStep 1255567 = 1883351) B1883351
theorem B5646509 : Blo 1112627 5646509 := bstep (se 3 (by rfl) ⟨1058720, by rfl⟩ : syracuseStep 5646509 = 2117441) B2117441
theorem B1878457 : Blo 1112627 1878457 := bstep (se 2 (by rfl) ⟨704421, by rfl⟩ : syracuseStep 1878457 = 1408843) B1408843
theorem B1812937 : Blo 1112627 1812937 := bstep (se 2 (by rfl) ⟨679851, by rfl⟩ : syracuseStep 1812937 = 1359703) B1359703
theorem B13576657 : Blo 1112627 13576657 := bstep (se 2 (by rfl) ⟨5091246, by rfl⟩ : syracuseStep 13576657 = 10182493) B10182493
theorem B1256071 : Blo 1112627 1256071 := bstep (se 1 (by rfl) ⟨942053, by rfl⟩ : syracuseStep 1256071 = 1884107) B1884107
theorem B1409015 : Blo 1112627 1409015 := bstep (se 1 (by rfl) ⟨1056761, by rfl⟩ : syracuseStep 1409015 = 2113523) B2113523
theorem B1879159 : Blo 1112627 1879159 := bstep (se 1 (by rfl) ⟨1409369, by rfl⟩ : syracuseStep 1879159 = 2818739) B2818739
theorem B1879355 : Blo 1112627 1879355 := bstep (se 1 (by rfl) ⟨1409516, by rfl⟩ : syracuseStep 1879355 = 2819033) B2819033
theorem B1584527 : Blo 1112627 1584527 := bstep (se 1 (by rfl) ⟨1188395, by rfl⟩ : syracuseStep 1584527 = 2376791) B2376791
theorem B4238801 : Blo 1112627 4238801 := bstep (se 2 (by rfl) ⟨1589550, by rfl⟩ : syracuseStep 4238801 = 3179101) B3179101
theorem B1584841 : Blo 1112627 1584841 := bstep (se 2 (by rfl) ⟨594315, by rfl⟩ : syracuseStep 1584841 = 1188631) B1188631
theorem B1879753 : Blo 1112627 1879753 := bstep (se 2 (by rfl) ⟨704907, by rfl⟩ : syracuseStep 1879753 = 1409815) B1409815
theorem B5648129 : Blo 1112627 5648129 := bstep (se 2 (by rfl) ⟨2118048, by rfl⟩ : syracuseStep 5648129 = 4236097) B4236097
theorem B4763407 : Blo 1112627 4763407 := bstep (se 1 (by rfl) ⟨3572555, by rfl⟩ : syracuseStep 4763407 = 7145111) B7145111
theorem B2011027 : Blo 1112627 2011027 := bstep (se 1 (by rfl) ⟨1508270, by rfl⟩ : syracuseStep 2011027 = 3016541) B3016541
theorem B8466605 : Blo 1112627 8466605 := bstep (se 3 (by rfl) ⟨1587488, by rfl⟩ : syracuseStep 8466605 = 3174977) B3174977
theorem B1880455 : Blo 1112627 1880455 := bstep (se 1 (by rfl) ⟨1410341, by rfl⟩ : syracuseStep 1880455 = 2820683) B2820683
theorem B13545913 : Blo 1112627 13545913 := bstep (se 2 (by rfl) ⟨5079717, by rfl⟩ : syracuseStep 13545913 = 10159435) B10159435
theorem B5353913 : Blo 1112627 5353913 := bstep (se 2 (by rfl) ⟨2007717, by rfl⟩ : syracuseStep 5353913 = 4015435) B4015435
theorem B5353931 : Blo 1112627 5353931 := bstep (se 1 (by rfl) ⟨4015448, by rfl⟩ : syracuseStep 5353931 = 8030897) B8030897
theorem B5648939 : Blo 1112627 5648939 := bstep (se 1 (by rfl) ⟨4236704, by rfl⟩ : syracuseStep 5648939 = 8473409) B8473409
theorem B487862837 : Blo 1112627 487862837 := bstep (se 5 (by rfl) ⟨22868570, by rfl⟩ : syracuseStep 487862837 = 45737141) B45737141
theorem B9024119 : Blo 1112627 9024119 := bstep (se 1 (by rfl) ⟨6768089, by rfl⟩ : syracuseStep 9024119 = 13536179) B13536179
theorem B5354221 : Blo 1112627 5354221 := bstep (se 3 (by rfl) ⟨1003916, by rfl⟩ : syracuseStep 5354221 = 2007833) B2007833
theorem B2503439 : Blo 1112627 2503439 := bstep (se 1 (by rfl) ⟨1877579, by rfl⟩ : syracuseStep 2503439 = 3755159) B3755159
theorem B2503457 : Blo 1112627 2503457 := bstep (se 2 (by rfl) ⟨938796, by rfl⟩ : syracuseStep 2503457 = 1877593) B1877593
theorem B1881103 : Blo 1112627 1881103 := bstep (se 1 (by rfl) ⟨1410827, by rfl⟩ : syracuseStep 1881103 = 2821655) B2821655
theorem B4011095 : Blo 1112627 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B2503799 : Blo 1112627 2503799 := bstep (se 1 (by rfl) ⟨1877849, by rfl⟩ : syracuseStep 2503799 = 3755699) B3755699
theorem B1783055 : Blo 1112627 1783055 := bstep (se 1 (by rfl) ⟨1337291, by rfl⟩ : syracuseStep 1783055 = 2674583) B2674583
theorem B2503979 : Blo 1112627 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B13579579 : Blo 1112627 13579579 := bstep (se 1 (by rfl) ⟨10184684, by rfl⟩ : syracuseStep 13579579 = 20369369) B20369369
theorem B4765063 : Blo 1112627 4765063 := bstep (se 1 (by rfl) ⟨3573797, by rfl⟩ : syracuseStep 4765063 = 7147595) B7147595
theorem B1881643 : Blo 1112627 1881643 := bstep (se 1 (by rfl) ⟨1411232, by rfl⟩ : syracuseStep 1881643 = 2822465) B2822465
theorem B2504339 : Blo 1112627 2504339 := bstep (se 1 (by rfl) ⟨1878254, by rfl⟩ : syracuseStep 2504339 = 3756509) B3756509
theorem B1881785 : Blo 1112627 1881785 := bstep (se 2 (by rfl) ⟨705669, by rfl⟩ : syracuseStep 1881785 = 1411339) B1411339
theorem B2504393 : Blo 1112627 2504393 := bstep (se 2 (by rfl) ⟨939147, by rfl⟩ : syracuseStep 2504393 = 1878295) B1878295
theorem B1783567 : Blo 1112627 1783567 := bstep (se 1 (by rfl) ⟨1337675, by rfl⟩ : syracuseStep 1783567 = 2675351) B2675351
theorem B5650235 : Blo 1112627 5650235 := bstep (se 1 (by rfl) ⟨4237676, by rfl⟩ : syracuseStep 5650235 = 8475353) B8475353
theorem B5650397 : Blo 1112627 5650397 := bstep (se 3 (by rfl) ⟨1059449, by rfl⟩ : syracuseStep 5650397 = 2118899) B2118899
theorem B2537743 : Blo 1112627 2537743 := bstep (se 1 (by rfl) ⟨1903307, by rfl⟩ : syracuseStep 2537743 = 3806615) B3806615
theorem B5650721 : Blo 1112627 5650721 := bstep (se 2 (by rfl) ⟨2119020, by rfl⟩ : syracuseStep 5650721 = 4238041) B4238041
theorem B1587529 : Blo 1112627 1587529 := bstep (se 2 (by rfl) ⟨595323, by rfl⟩ : syracuseStep 1587529 = 1190647) B1190647
theorem B1882487 : Blo 1112627 1882487 := bstep (se 1 (by rfl) ⟨1411865, by rfl⟩ : syracuseStep 1882487 = 2823731) B2823731
theorem B2505095 : Blo 1112627 2505095 := bstep (se 1 (by rfl) ⟨1878821, by rfl⟩ : syracuseStep 2505095 = 3757643) B3757643
theorem B5355929 : Blo 1112627 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B6339019 : Blo 1112627 6339019 := bstep (se 1 (by rfl) ⟨4754264, by rfl⟩ : syracuseStep 6339019 = 9508529) B9508529
theorem B2537999 : Blo 1112627 2537999 := bstep (se 1 (by rfl) ⟨1903499, by rfl⟩ : syracuseStep 2537999 = 3806999) B3806999
theorem B8469035 : Blo 1112627 8469035 := bstep (se 1 (by rfl) ⟨6351776, by rfl⟩ : syracuseStep 8469035 = 12703553) B12703553
theorem B2505275 : Blo 1112627 2505275 := bstep (se 1 (by rfl) ⟨1878956, by rfl⟩ : syracuseStep 2505275 = 3757913) B3757913
theorem B2505401 : Blo 1112627 2505401 := bstep (se 2 (by rfl) ⟨939525, by rfl⟩ : syracuseStep 2505401 = 1879051) B1879051
theorem B4766465 : Blo 1112627 4766465 := bstep (se 2 (by rfl) ⟨1787424, by rfl⟩ : syracuseStep 4766465 = 3574849) B3574849
theorem B1882939 : Blo 1112627 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B1784695 : Blo 1112627 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B10730393 : Blo 1112627 10730393 := bstep (se 2 (by rfl) ⟨4023897, by rfl⟩ : syracuseStep 10730393 = 8047795) B8047795
theorem B1883081 : Blo 1112627 1883081 := bstep (se 2 (by rfl) ⟨706155, by rfl⟩ : syracuseStep 1883081 = 1412311) B1412311
theorem B2505743 : Blo 1112627 2505743 := bstep (se 1 (by rfl) ⟨1879307, by rfl⟩ : syracuseStep 2505743 = 3758615) B3758615
theorem B2505761 : Blo 1112627 2505761 := bstep (se 2 (by rfl) ⟨939660, by rfl⟩ : syracuseStep 2505761 = 1879321) B1879321
theorem B8043581 : Blo 1112627 8043581 := bstep (se 3 (by rfl) ⟨1508171, by rfl⟩ : syracuseStep 8043581 = 3016343) B3016343
theorem B6110437 : Blo 1112627 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B5651693 : Blo 1112627 5651693 := bstep (se 3 (by rfl) ⟨1059692, by rfl⟩ : syracuseStep 5651693 = 2119385) B2119385
theorem B2506103 : Blo 1112627 2506103 := bstep (se 1 (by rfl) ⟨1879577, by rfl⟩ : syracuseStep 2506103 = 3759155) B3759155
theorem B2113067 : Blo 1112627 2113067 := bstep (se 1 (by rfl) ⟨1584800, by rfl⟩ : syracuseStep 2113067 = 3169601) B3169601
theorem B2506283 : Blo 1112627 2506283 := bstep (se 1 (by rfl) ⟨1879712, by rfl⟩ : syracuseStep 2506283 = 3759425) B3759425
theorem B1883783 : Blo 1112627 1883783 := bstep (se 1 (by rfl) ⟨1412837, by rfl⟩ : syracuseStep 1883783 = 2825675) B2825675
theorem B2506643 : Blo 1112627 2506643 := bstep (se 1 (by rfl) ⟨1879982, by rfl⟩ : syracuseStep 2506643 = 3759965) B3759965
theorem B2506697 : Blo 1112627 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B5652503 : Blo 1112627 5652503 := bstep (se 1 (by rfl) ⟨4239377, by rfl⟩ : syracuseStep 5652503 = 8478755) B8478755
theorem B9519191 : Blo 1112627 9519191 := bstep (se 1 (by rfl) ⟨7139393, by rfl⟩ : syracuseStep 9519191 = 14278787) B14278787
theorem B2539639 : Blo 1112627 2539639 := bstep (se 1 (by rfl) ⟨1904729, by rfl⟩ : syracuseStep 2539639 = 3809459) B3809459
theorem B6439085 : Blo 1112627 6439085 := bstep (se 3 (by rfl) ⟨1207328, by rfl⟩ : syracuseStep 6439085 = 2414657) B2414657
theorem B6767171 : Blo 1112627 6767171 := bstep (se 1 (by rfl) ⟨5075378, by rfl⟩ : syracuseStep 6767171 = 10150757) B10150757
theorem B2507399 : Blo 1112627 2507399 := bstep (se 1 (by rfl) ⟨1880549, by rfl⟩ : syracuseStep 2507399 = 3761099) B3761099
theorem B6341435 : Blo 1112627 6341435 := bstep (se 1 (by rfl) ⟨4756076, by rfl⟩ : syracuseStep 6341435 = 9512153) B9512153
theorem B2507579 : Blo 1112627 2507579 := bstep (se 1 (by rfl) ⟨1880684, by rfl⟩ : syracuseStep 2507579 = 3761369) B3761369
theorem B2507705 : Blo 1112627 2507705 := bstep (se 2 (by rfl) ⟨940389, by rfl⟩ : syracuseStep 2507705 = 1880779) B1880779
theorem B5358545 : Blo 1112627 5358545 := bstep (se 2 (by rfl) ⟨2009454, by rfl⟩ : syracuseStep 5358545 = 4018909) B4018909
theorem B3392513 : Blo 1112627 3392513 := bstep (se 2 (by rfl) ⟨1272192, by rfl⟩ : syracuseStep 3392513 = 2544385) B2544385
theorem B6112343 : Blo 1112627 6112343 := bstep (se 1 (by rfl) ⟨4584257, by rfl⟩ : syracuseStep 6112343 = 9168515) B9168515
theorem B1787015 : Blo 1112627 1787015 := bstep (se 1 (by rfl) ⟨1340261, by rfl⟩ : syracuseStep 1787015 = 2680523) B2680523
theorem B2114761 : Blo 1112627 2114761 := bstep (se 2 (by rfl) ⟨793035, by rfl⟩ : syracuseStep 2114761 = 1586071) B1586071
theorem B3818753 : Blo 1112627 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B2508047 : Blo 1112627 2508047 := bstep (se 1 (by rfl) ⟨1881035, by rfl⟩ : syracuseStep 2508047 = 3762071) B3762071
theorem B2508065 : Blo 1112627 2508065 := bstep (se 2 (by rfl) ⟨940524, by rfl⟩ : syracuseStep 2508065 = 1881049) B1881049
theorem B4015507 : Blo 1112627 4015507 := bstep (se 1 (by rfl) ⟨3011630, by rfl⟩ : syracuseStep 4015507 = 6023261) B6023261
theorem B12699179 : Blo 1112627 12699179 := bstep (se 1 (by rfl) ⟨9524384, by rfl⟩ : syracuseStep 12699179 = 19048769) B19048769
theorem B3393085 : Blo 1112627 3393085 := bstep (se 3 (by rfl) ⟨636203, by rfl⟩ : syracuseStep 3393085 = 1272407) B1272407
theorem B2508407 : Blo 1112627 2508407 := bstep (se 1 (by rfl) ⟨1881305, by rfl⟩ : syracuseStep 2508407 = 3762611) B3762611
theorem B2508587 : Blo 1112627 2508587 := bstep (se 1 (by rfl) ⟨1881440, by rfl⟩ : syracuseStep 2508587 = 3762881) B3762881
theorem B9652121 : Blo 1112627 9652121 := bstep (se 2 (by rfl) ⟨3619545, by rfl⟩ : syracuseStep 9652121 = 7239091) B7239091
theorem B2508947 : Blo 1112627 2508947 := bstep (se 1 (by rfl) ⟨1881710, by rfl⟩ : syracuseStep 2508947 = 3763421) B3763421
theorem B2509001 : Blo 1112627 2509001 := bstep (se 2 (by rfl) ⟨940875, by rfl⟩ : syracuseStep 2509001 = 1881751) B1881751
theorem B6342893 : Blo 1112627 6342893 := bstep (se 3 (by rfl) ⟨1189292, by rfl⟩ : syracuseStep 6342893 = 2378585) B2378585
theorem B7129529 : Blo 1112627 7129529 := bstep (se 2 (by rfl) ⟨2673573, by rfl⟩ : syracuseStep 7129529 = 5347147) B5347147
theorem B6343211 : Blo 1112627 6343211 := bstep (se 1 (by rfl) ⟨4757408, by rfl⟩ : syracuseStep 6343211 = 9514817) B9514817
theorem B1788617 : Blo 1112627 1788617 := bstep (se 2 (by rfl) ⟨670731, by rfl⟩ : syracuseStep 1788617 = 1341463) B1341463
theorem B2509703 : Blo 1112627 2509703 := bstep (se 1 (by rfl) ⟨1882277, by rfl⟩ : syracuseStep 2509703 = 3764555) B3764555
theorem B36129685 : Blo 1112627 36129685 := bstep (se 6 (by rfl) ⟨846789, by rfl⟩ : syracuseStep 36129685 = 1693579) B1693579
theorem B2116667 : Blo 1112627 2116667 := bstep (se 1 (by rfl) ⟨1587500, by rfl⟩ : syracuseStep 2116667 = 3175001) B3175001
theorem B2509883 : Blo 1112627 2509883 := bstep (se 1 (by rfl) ⟨1882412, by rfl⟩ : syracuseStep 2509883 = 3764825) B3764825
theorem B2510009 : Blo 1112627 2510009 := bstep (se 2 (by rfl) ⟨941253, by rfl⟩ : syracuseStep 2510009 = 1882507) B1882507
theorem B2510351 : Blo 1112627 2510351 := bstep (se 1 (by rfl) ⟨1882763, by rfl⟩ : syracuseStep 2510351 = 3765527) B3765527
theorem B2117153 : Blo 1112627 2117153 := bstep (se 2 (by rfl) ⟨793932, by rfl⟩ : syracuseStep 2117153 = 1587865) B1587865
theorem B2510369 : Blo 1112627 2510369 := bstep (se 2 (by rfl) ⟨941388, by rfl⟩ : syracuseStep 2510369 = 1882777) B1882777
theorem B2379449 : Blo 1112627 2379449 := bstep (se 2 (by rfl) ⟨892293, by rfl⟩ : syracuseStep 2379449 = 1784587) B1784587
theorem B48844595 : Blo 1112627 48844595 := bstep (se 1 (by rfl) ⟨36633446, by rfl⟩ : syracuseStep 48844595 = 73266893) B73266893
theorem B2117495 : Blo 1112627 2117495 := bstep (se 1 (by rfl) ⟨1588121, by rfl⟩ : syracuseStep 2117495 = 3176243) B3176243
theorem B2510711 : Blo 1112627 2510711 := bstep (se 1 (by rfl) ⟨1883033, by rfl⟩ : syracuseStep 2510711 = 3766067) B3766067
theorem B6344669 : Blo 1112627 6344669 := bstep (se 3 (by rfl) ⟨1189625, by rfl⟩ : syracuseStep 6344669 = 2379251) B2379251
theorem B2510891 : Blo 1112627 2510891 := bstep (se 1 (by rfl) ⟨1883168, by rfl⟩ : syracuseStep 2510891 = 3766337) B3766337
theorem B3756347 : Blo 1112627 3756347 := bstep (se 1 (by rfl) ⟨2817260, by rfl⟩ : syracuseStep 3756347 = 5634521) B5634521
theorem B2511251 : Blo 1112627 2511251 := bstep (se 1 (by rfl) ⟨1883438, by rfl⟩ : syracuseStep 2511251 = 3766877) B3766877
theorem B2511305 : Blo 1112627 2511305 := bstep (se 2 (by rfl) ⟨941739, by rfl⟩ : syracuseStep 2511305 = 1883479) B1883479
theorem B6771203 : Blo 1112627 6771203 := bstep (se 1 (by rfl) ⟨5078402, by rfl⟩ : syracuseStep 6771203 = 10156805) B10156805
theorem B1692217 : Blo 1112627 1692217 := bstep (se 2 (by rfl) ⟨634581, by rfl⟩ : syracuseStep 1692217 = 1269163) B1269163
theorem B3756833 : Blo 1112627 3756833 := bstep (se 2 (by rfl) ⟨1408812, by rfl⟩ : syracuseStep 3756833 = 2817625) B2817625
theorem B2512007 : Blo 1112627 2512007 := bstep (se 1 (by rfl) ⟨1884005, by rfl⟩ : syracuseStep 2512007 = 3768011) B3768011
theorem B5231873 : Blo 1112627 5231873 := bstep (se 2 (by rfl) ⟨1961952, by rfl⟩ : syracuseStep 5231873 = 3923905) B3923905
theorem B2381089 : Blo 1112627 2381089 := bstep (se 2 (by rfl) ⟨892908, by rfl⟩ : syracuseStep 2381089 = 1785817) B1785817
theorem B7132475 : Blo 1112627 7132475 := bstep (se 1 (by rfl) ⟨5349356, by rfl⟩ : syracuseStep 7132475 = 10698713) B10698713
theorem B5363003 : Blo 1112627 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B2512187 : Blo 1112627 2512187 := bstep (se 1 (by rfl) ⟨1884140, by rfl⟩ : syracuseStep 2512187 = 3768281) B3768281
theorem B3757427 : Blo 1112627 3757427 := bstep (se 1 (by rfl) ⟨2818070, by rfl⟩ : syracuseStep 3757427 = 5636141) B5636141
theorem B9524627 : Blo 1112627 9524627 := bstep (se 1 (by rfl) ⟨7143470, by rfl⟩ : syracuseStep 9524627 = 14286941) B14286941
theorem B6116755 : Blo 1112627 6116755 := bstep (se 1 (by rfl) ⟨4587566, by rfl⟩ : syracuseStep 6116755 = 9175133) B9175133
theorem B2119097 : Blo 1112627 2119097 := bstep (se 2 (by rfl) ⟨794661, by rfl⟩ : syracuseStep 2119097 = 1589323) B1589323
theorem B2512313 : Blo 1112627 2512313 := bstep (se 2 (by rfl) ⟨942117, by rfl⟩ : syracuseStep 2512313 = 1884235) B1884235
theorem B6772177 : Blo 1112627 6772177 := bstep (se 2 (by rfl) ⟨2539566, by rfl⟩ : syracuseStep 6772177 = 5079133) B5079133
theorem B2676235 : Blo 1112627 2676235 := bstep (se 1 (by rfl) ⟨2007176, by rfl⟩ : syracuseStep 2676235 = 4014353) B4014353
theorem B6018761 : Blo 1112627 6018761 := bstep (se 2 (by rfl) ⟨2257035, by rfl⟩ : syracuseStep 6018761 = 4514071) B4514071
theorem B8378113 : Blo 1112627 8378113 := bstep (se 2 (by rfl) ⟨3141792, by rfl⟩ : syracuseStep 8378113 = 6283585) B6283585
theorem B2119439 : Blo 1112627 2119439 := bstep (se 1 (by rfl) ⟨1589579, by rfl⟩ : syracuseStep 2119439 = 3179159) B3179159
theorem B5363603 : Blo 1112627 5363603 := bstep (se 1 (by rfl) ⟨4022702, by rfl⟩ : syracuseStep 5363603 = 8045405) B8045405
theorem B6019001 : Blo 1112627 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B2676851 : Blo 1112627 2676851 := bstep (se 1 (by rfl) ⟨2007638, by rfl⟩ : syracuseStep 2676851 = 4015277) B4015277
theorem B9164933 : Blo 1112627 9164933 := bstep (se 4 (by rfl) ⟨859212, by rfl⟩ : syracuseStep 9164933 = 1718425) B1718425
theorem B2382139 : Blo 1112627 2382139 := bstep (se 1 (by rfl) ⟨1786604, by rfl⟩ : syracuseStep 2382139 = 3573209) B3573209
theorem B2677139 : Blo 1112627 2677139 := bstep (se 1 (by rfl) ⟨2007854, by rfl⟩ : syracuseStep 2677139 = 4015709) B4015709
theorem B7625107 : Blo 1112627 7625107 := bstep (se 1 (by rfl) ⟨5718830, by rfl⟩ : syracuseStep 7625107 = 11437661) B11437661
theorem B3168713 : Blo 1112627 3168713 := bstep (se 2 (by rfl) ⟨1188267, by rfl⟩ : syracuseStep 3168713 = 2376535) B2376535
theorem B6347267 : Blo 1112627 6347267 := bstep (se 1 (by rfl) ⟨4760450, by rfl⟩ : syracuseStep 6347267 = 9520901) B9520901
theorem B3168827 : Blo 1112627 3168827 := bstep (se 1 (by rfl) ⟨2376620, by rfl⟩ : syracuseStep 3168827 = 4753241) B4753241
theorem B12049073 : Blo 1112627 12049073 := bstep (se 2 (by rfl) ⟨4518402, by rfl⟩ : syracuseStep 12049073 = 9036805) B9036805
theorem B3168953 : Blo 1112627 3168953 := bstep (se 2 (by rfl) ⟨1188357, by rfl⟩ : syracuseStep 3168953 = 2376715) B2376715
theorem B2382635 : Blo 1112627 2382635 := bstep (se 1 (by rfl) ⟨1786976, by rfl⟩ : syracuseStep 2382635 = 3573953) B3573953
theorem B4578257 : Blo 1112627 4578257 := bstep (se 2 (by rfl) ⟨1716846, by rfl⟩ : syracuseStep 4578257 = 3433693) B3433693
theorem B8477783 : Blo 1112627 8477783 := bstep (se 1 (by rfl) ⟨6358337, by rfl⟩ : syracuseStep 8477783 = 12716675) B12716675
theorem B3760019 : Blo 1112627 3760019 := bstep (se 1 (by rfl) ⟨2820014, by rfl⟩ : syracuseStep 3760019 = 5640029) B5640029
theorem B27091037 : Blo 1112627 27091037 := bstep (se 3 (by rfl) ⟨5079569, by rfl⟩ : syracuseStep 27091037 = 10159139) B10159139
theorem B2679041 : Blo 1112627 2679041 := bstep (se 2 (by rfl) ⟨1004640, by rfl⟩ : syracuseStep 2679041 = 2009281) B2009281
theorem B3170603 : Blo 1112627 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B2384275 : Blo 1112627 2384275 := bstep (se 1 (by rfl) ⟨1788206, by rfl⟩ : syracuseStep 2384275 = 3576413) B3576413
theorem B2679311 : Blo 1112627 2679311 := bstep (se 1 (by rfl) ⟨2009483, by rfl⟩ : syracuseStep 2679311 = 4018967) B4018967
theorem B4023175 : Blo 1112627 4023175 := bstep (se 1 (by rfl) ⟨3017381, by rfl⟩ : syracuseStep 4023175 = 6034763) B6034763
theorem B14279813 : Blo 1112627 14279813 := bstep (se 4 (by rfl) ⟨1338732, by rfl⟩ : syracuseStep 14279813 = 2677465) B2677465
theorem B3171595 : Blo 1112627 3171595 := bstep (se 1 (by rfl) ⟨2378696, by rfl⟩ : syracuseStep 3171595 = 4757393) B4757393
theorem B3761423 : Blo 1112627 3761423 := bstep (se 1 (by rfl) ⟨2821067, by rfl⟩ : syracuseStep 3761423 = 5642135) B5642135
theorem B3171869 : Blo 1112627 3171869 := bstep (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) B1189451
theorem B3761693 : Blo 1112627 3761693 := bstep (se 3 (by rfl) ⟨705317, by rfl⟩ : syracuseStep 3761693 = 1410635) B1410635
theorem B4515371 : Blo 1112627 4515371 := bstep (se 1 (by rfl) ⟨3386528, by rfl⟩ : syracuseStep 4515371 = 6773057) B6773057
theorem B1697339 : Blo 1112627 1697339 := bstep (se 1 (by rfl) ⟨1273004, by rfl⟩ : syracuseStep 1697339 = 2546009) B2546009
theorem B12871703 : Blo 1112627 12871703 := bstep (se 1 (by rfl) ⟨9653777, by rfl⟩ : syracuseStep 12871703 = 19307555) B19307555
theorem B12707927 : Blo 1112627 12707927 := bstep (se 1 (by rfl) ⟨9530945, by rfl⟩ : syracuseStep 12707927 = 19061891) B19061891
theorem B4581647 : Blo 1112627 4581647 := bstep (se 1 (by rfl) ⟨3436235, by rfl⟩ : syracuseStep 4581647 = 6872471) B6872471
theorem B5499283 : Blo 1112627 5499283 := bstep (se 1 (by rfl) ⟨4124462, by rfl⟩ : syracuseStep 5499283 = 8248925) B8248925
theorem B3009035 : Blo 1112627 3009035 := bstep (se 1 (by rfl) ⟨2256776, by rfl⟩ : syracuseStep 3009035 = 4513553) B4513553
theorem B43412087 : Blo 1112627 43412087 := bstep (se 1 (by rfl) ⟨32559065, by rfl⟩ : syracuseStep 43412087 = 65118131) B65118131
theorem B6023909 : Blo 1112627 6023909 := bstep (se 4 (by rfl) ⟨564741, by rfl⟩ : syracuseStep 6023909 = 1129483) B1129483
theorem B3009415 : Blo 1112627 3009415 := bstep (se 1 (by rfl) ⟨2257061, by rfl⟩ : syracuseStep 3009415 = 4514123) B4514123
theorem B3763097 : Blo 1112627 3763097 := bstep (se 2 (by rfl) ⟨1411161, by rfl⟩ : syracuseStep 3763097 = 2822323) B2822323
theorem B6351959 : Blo 1112627 6351959 := bstep (se 1 (by rfl) ⟨4763969, by rfl⟩ : syracuseStep 6351959 = 9527939) B9527939
theorem B6024365 : Blo 1112627 6024365 := bstep (se 3 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 6024365 = 2259137) B2259137
theorem B8154503 : Blo 1112627 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B3173975 : Blo 1112627 3173975 := bstep (se 1 (by rfl) ⟨2380481, by rfl⟩ : syracuseStep 3173975 = 4760963) B4760963
theorem B3763799 : Blo 1112627 3763799 := bstep (se 1 (by rfl) ⟨2822849, by rfl⟩ : syracuseStep 3763799 = 5645699) B5645699
theorem B10710629 : Blo 1112627 10710629 := bstep (se 4 (by rfl) ⟨1004121, by rfl⟩ : syracuseStep 10710629 = 2008243) B2008243
theorem B7139087 : Blo 1112627 7139087 := bstep (se 1 (by rfl) ⟨5354315, by rfl⟩ : syracuseStep 7139087 = 10708631) B10708631
theorem B3174203 : Blo 1112627 3174203 := bstep (se 1 (by rfl) ⟨2380652, by rfl⟩ : syracuseStep 3174203 = 4761305) B4761305
theorem B3174329 : Blo 1112627 3174329 := bstep (se 2 (by rfl) ⟨1190373, by rfl⟩ : syracuseStep 3174329 = 2380747) B2380747
theorem B2682809 : Blo 1112627 2682809 := bstep (se 2 (by rfl) ⟨1006053, by rfl⟩ : syracuseStep 2682809 = 2012107) B2012107
theorem B3764285 : Blo 1112627 3764285 := bstep (se 3 (by rfl) ⟨705803, by rfl⟩ : syracuseStep 3764285 = 1411607) B1411607
theorem B6025681 : Blo 1112627 6025681 := bstep (se 2 (by rfl) ⟨2259630, by rfl⟩ : syracuseStep 6025681 = 4519261) B4519261
theorem B81293867 : Blo 1112627 81293867 := bstep (se 1 (by rfl) ⟨60970400, by rfl⟩ : syracuseStep 81293867 = 121940801) B121940801
theorem B7631617 : Blo 1112627 7631617 := bstep (se 2 (by rfl) ⟨2861856, by rfl⟩ : syracuseStep 7631617 = 5723713) B5723713
theorem B9532313 : Blo 1112627 9532313 := bstep (se 2 (by rfl) ⟨3574617, by rfl⟩ : syracuseStep 9532313 = 7149235) B7149235
theorem B6353873 : Blo 1112627 6353873 := bstep (se 2 (by rfl) ⟨2382702, by rfl⟩ : syracuseStep 6353873 = 4765405) B4765405
theorem B2716687 : Blo 1112627 2716687 := bstep (se 1 (by rfl) ⟨2037515, by rfl⟩ : syracuseStep 2716687 = 4075031) B4075031
theorem B5633225 : Blo 1112627 5633225 := bstep (se 2 (by rfl) ⟨2112459, by rfl⟩ : syracuseStep 5633225 = 4224919) B4224919
theorem B8025479 : Blo 1112627 8025479 := bstep (se 1 (by rfl) ⟨6019109, by rfl⟩ : syracuseStep 8025479 = 12038219) B12038219
theorem B3765689 : Blo 1112627 3765689 := bstep (se 2 (by rfl) ⟨1412133, by rfl⟩ : syracuseStep 3765689 = 2824267) B2824267
theorem B3175969 : Blo 1112627 3175969 := bstep (se 2 (by rfl) ⟨1190988, by rfl⟩ : syracuseStep 3175969 = 2381977) B2381977
theorem B6027023 : Blo 1112627 6027023 := bstep (se 1 (by rfl) ⟨4520267, by rfl⟩ : syracuseStep 6027023 = 9040535) B9040535
theorem B1668983 : Blo 1112627 1668983 := bstep (se 1 (by rfl) ⟨1251737, by rfl⟩ : syracuseStep 1668983 = 2503475) B2503475
theorem B1669007 : Blo 1112627 1669007 := bstep (se 1 (by rfl) ⟨1251755, by rfl⟩ : syracuseStep 1669007 = 2503511) B2503511
theorem B1669049 : Blo 1112627 1669049 := bstep (se 2 (by rfl) ⟨625893, by rfl⟩ : syracuseStep 1669049 = 1251787) B1251787
theorem B1669127 : Blo 1112627 1669127 := bstep (se 1 (by rfl) ⟨1251845, by rfl⟩ : syracuseStep 1669127 = 2503691) B2503691
theorem B3176459 : Blo 1112627 3176459 := bstep (se 1 (by rfl) ⟨2382344, by rfl⟩ : syracuseStep 3176459 = 4764689) B4764689
theorem B3766283 : Blo 1112627 3766283 := bstep (se 1 (by rfl) ⟨2824712, by rfl⟩ : syracuseStep 3766283 = 5649425) B5649425
theorem B1669163 : Blo 1112627 1669163 := bstep (se 1 (by rfl) ⟨1251872, by rfl⟩ : syracuseStep 1669163 = 2503745) B2503745
theorem B1669193 : Blo 1112627 1669193 := bstep (se 2 (by rfl) ⟨625947, by rfl⟩ : syracuseStep 1669193 = 1251895) B1251895
theorem B3766391 : Blo 1112627 3766391 := bstep (se 1 (by rfl) ⟨2824793, by rfl⟩ : syracuseStep 3766391 = 5649587) B5649587
theorem B1669307 : Blo 1112627 1669307 := bstep (se 1 (by rfl) ⟨1251980, by rfl⟩ : syracuseStep 1669307 = 2503961) B2503961
theorem B7239917 : Blo 1112627 7239917 := bstep (se 3 (by rfl) ⟨1357484, by rfl⟩ : syracuseStep 7239917 = 2714969) B2714969
theorem B1669367 : Blo 1112627 1669367 := bstep (se 1 (by rfl) ⟨1252025, by rfl⟩ : syracuseStep 1669367 = 2504051) B2504051
theorem B1669391 : Blo 1112627 1669391 := bstep (se 1 (by rfl) ⟨1252043, by rfl⟩ : syracuseStep 1669391 = 2504087) B2504087
theorem B1669433 : Blo 1112627 1669433 := bstep (se 2 (by rfl) ⟨626037, by rfl⟩ : syracuseStep 1669433 = 1252075) B1252075
theorem B1669511 : Blo 1112627 1669511 := bstep (se 1 (by rfl) ⟨1252133, by rfl⟩ : syracuseStep 1669511 = 2504267) B2504267
theorem B1669547 : Blo 1112627 1669547 := bstep (se 1 (by rfl) ⟨1252160, by rfl⟩ : syracuseStep 1669547 = 2504321) B2504321
theorem B2816441 : Blo 1112627 2816441 := bstep (se 2 (by rfl) ⟨1056165, by rfl⟩ : syracuseStep 2816441 = 2112331) B2112331
theorem B1669577 : Blo 1112627 1669577 := bstep (se 2 (by rfl) ⟨626091, by rfl⟩ : syracuseStep 1669577 = 1252183) B1252183
theorem B1112635 : Blo 1112627 1112635 := bstep (se 1 (by rfl) ⟨834476, by rfl⟩ : syracuseStep 1112635 = 1668953) B1668953
theorem B1669691 : Blo 1112627 1669691 := bstep (se 1 (by rfl) ⟨1252268, by rfl⟩ : syracuseStep 1669691 = 2504537) B2504537
theorem B1669751 : Blo 1112627 1669751 := bstep (se 1 (by rfl) ⟨1252313, by rfl⟩ : syracuseStep 1669751 = 2504627) B2504627
theorem B1112711 : Blo 1112627 1112711 := bstep (se 1 (by rfl) ⟨834533, by rfl⟩ : syracuseStep 1112711 = 1669067) B1669067
theorem B1112719 : Blo 1112627 1112719 := bstep (se 1 (by rfl) ⟨834539, by rfl⟩ : syracuseStep 1112719 = 1669079) B1669079
theorem B1669775 : Blo 1112627 1669775 := bstep (se 1 (by rfl) ⟨1252331, by rfl⟩ : syracuseStep 1669775 = 2504663) B2504663
theorem B1669817 : Blo 1112627 1669817 := bstep (se 2 (by rfl) ⟨626181, by rfl⟩ : syracuseStep 1669817 = 1252363) B1252363
theorem B1112763 : Blo 1112627 1112763 := bstep (se 1 (by rfl) ⟨834572, by rfl⟩ : syracuseStep 1112763 = 1669145) B1669145
theorem B3766985 : Blo 1112627 3766985 := bstep (se 2 (by rfl) ⟨1412619, by rfl⟩ : syracuseStep 3766985 = 2825239) B2825239
theorem B1112839 : Blo 1112627 1112839 := bstep (se 1 (by rfl) ⟨834629, by rfl⟩ : syracuseStep 1112839 = 1669259) B1669259
theorem B1669895 : Blo 1112627 1669895 := bstep (se 1 (by rfl) ⟨1252421, by rfl⟩ : syracuseStep 1669895 = 2504843) B2504843
theorem B1112847 : Blo 1112627 1112847 := bstep (se 1 (by rfl) ⟨834635, by rfl⟩ : syracuseStep 1112847 = 1669271) B1669271
theorem B3177245 : Blo 1112627 3177245 := bstep (se 3 (by rfl) ⟨595733, by rfl⟩ : syracuseStep 3177245 = 1191467) B1191467
theorem B1669931 : Blo 1112627 1669931 := bstep (se 1 (by rfl) ⟨1252448, by rfl⟩ : syracuseStep 1669931 = 2504897) B2504897
theorem B1112891 : Blo 1112627 1112891 := bstep (se 1 (by rfl) ⟨834668, by rfl⟩ : syracuseStep 1112891 = 1669337) B1669337
theorem B5077819 : Blo 1112627 5077819 := bstep (se 1 (by rfl) ⟨3808364, by rfl⟩ : syracuseStep 5077819 = 7616729) B7616729
theorem B1669961 : Blo 1112627 1669961 := bstep (se 2 (by rfl) ⟨626235, by rfl⟩ : syracuseStep 1669961 = 1252471) B1252471
theorem B1112967 : Blo 1112627 1112967 := bstep (se 1 (by rfl) ⟨834725, by rfl⟩ : syracuseStep 1112967 = 1669451) B1669451
theorem B1112975 : Blo 1112627 1112975 := bstep (se 1 (by rfl) ⟨834731, by rfl⟩ : syracuseStep 1112975 = 1669463) B1669463
theorem B1113019 : Blo 1112627 1113019 := bstep (se 1 (by rfl) ⟨834764, by rfl⟩ : syracuseStep 1113019 = 1669529) B1669529
theorem B1670075 : Blo 1112627 1670075 := bstep (se 1 (by rfl) ⟨1252556, by rfl⟩ : syracuseStep 1670075 = 2505113) B2505113
theorem B1670135 : Blo 1112627 1670135 := bstep (se 1 (by rfl) ⟨1252601, by rfl⟩ : syracuseStep 1670135 = 2505203) B2505203
theorem B1113095 : Blo 1112627 1113095 := bstep (se 1 (by rfl) ⟨834821, by rfl⟩ : syracuseStep 1113095 = 1669643) B1669643
theorem B1113103 : Blo 1112627 1113103 := bstep (se 1 (by rfl) ⟨834827, by rfl⟩ : syracuseStep 1113103 = 1669655) B1669655
theorem B1670159 : Blo 1112627 1670159 := bstep (se 1 (by rfl) ⟨1252619, by rfl⟩ : syracuseStep 1670159 = 2505239) B2505239
theorem B1670201 : Blo 1112627 1670201 := bstep (se 2 (by rfl) ⟨626325, by rfl⟩ : syracuseStep 1670201 = 1252651) B1252651
theorem B1113147 : Blo 1112627 1113147 := bstep (se 1 (by rfl) ⟨834860, by rfl⟩ : syracuseStep 1113147 = 1669721) B1669721
theorem B3570749 : Blo 1112627 3570749 := bstep (se 3 (by rfl) ⟨669515, by rfl⟩ : syracuseStep 3570749 = 1339031) B1339031
theorem B2817139 : Blo 1112627 2817139 := bstep (se 1 (by rfl) ⟨2112854, by rfl⟩ : syracuseStep 2817139 = 4225709) B4225709
theorem B1113223 : Blo 1112627 1113223 := bstep (se 1 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 1113223 = 1669835) B1669835
theorem B1670279 : Blo 1112627 1670279 := bstep (se 1 (by rfl) ⟨1252709, by rfl⟩ : syracuseStep 1670279 = 2505419) B2505419
theorem B1113231 : Blo 1112627 1113231 := bstep (se 1 (by rfl) ⟨834923, by rfl⟩ : syracuseStep 1113231 = 1669847) B1669847
theorem B1670315 : Blo 1112627 1670315 := bstep (se 1 (by rfl) ⟨1252736, by rfl⟩ : syracuseStep 1670315 = 2505473) B2505473
theorem B1113275 : Blo 1112627 1113275 := bstep (se 1 (by rfl) ⟨834956, by rfl⟩ : syracuseStep 1113275 = 1669913) B1669913
theorem B1670345 : Blo 1112627 1670345 := bstep (se 2 (by rfl) ⟨626379, by rfl⟩ : syracuseStep 1670345 = 1252759) B1252759
theorem B2817281 : Blo 1112627 2817281 := bstep (se 2 (by rfl) ⟨1056480, by rfl⟩ : syracuseStep 2817281 = 2112961) B2112961
theorem B1113351 : Blo 1112627 1113351 := bstep (se 1 (by rfl) ⟨835013, by rfl⟩ : syracuseStep 1113351 = 1670027) B1670027
theorem B1113359 : Blo 1112627 1113359 := bstep (se 1 (by rfl) ⟨835019, by rfl⟩ : syracuseStep 1113359 = 1670039) B1670039
theorem B4226363 : Blo 1112627 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B1113403 : Blo 1112627 1113403 := bstep (se 1 (by rfl) ⟨835052, by rfl⟩ : syracuseStep 1113403 = 1670105) B1670105
theorem B1670459 : Blo 1112627 1670459 := bstep (se 1 (by rfl) ⟨1252844, by rfl⟩ : syracuseStep 1670459 = 2505689) B2505689
theorem B6782297 : Blo 1112627 6782297 := bstep (se 2 (by rfl) ⟨2543361, by rfl⟩ : syracuseStep 6782297 = 5086723) B5086723
theorem B1670519 : Blo 1112627 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B1113479 : Blo 1112627 1113479 := bstep (se 1 (by rfl) ⟨835109, by rfl⟩ : syracuseStep 1113479 = 1670219) B1670219
theorem B3767687 : Blo 1112627 3767687 := bstep (se 1 (by rfl) ⟨2825765, by rfl⟩ : syracuseStep 3767687 = 5651531) B5651531
theorem B1113487 : Blo 1112627 1113487 := bstep (se 1 (by rfl) ⟨835115, by rfl⟩ : syracuseStep 1113487 = 1670231) B1670231
theorem B1670543 : Blo 1112627 1670543 := bstep (se 1 (by rfl) ⟨1252907, by rfl⟩ : syracuseStep 1670543 = 2505815) B2505815
theorem B1670585 : Blo 1112627 1670585 := bstep (se 2 (by rfl) ⟨626469, by rfl⟩ : syracuseStep 1670585 = 1252939) B1252939
theorem B4521401 : Blo 1112627 4521401 := bstep (se 2 (by rfl) ⟨1695525, by rfl⟩ : syracuseStep 4521401 = 3391051) B3391051
theorem B1113531 : Blo 1112627 1113531 := bstep (se 1 (by rfl) ⟨835148, by rfl⟩ : syracuseStep 1113531 = 1670297) B1670297
theorem B1408519 : Blo 1112627 1408519 := bstep (se 1 (by rfl) ⟨1056389, by rfl⟩ : syracuseStep 1408519 = 2112779) B2112779
theorem B1113607 : Blo 1112627 1113607 := bstep (se 1 (by rfl) ⟨835205, by rfl⟩ : syracuseStep 1113607 = 1670411) B1670411
theorem B1670663 : Blo 1112627 1670663 := bstep (se 1 (by rfl) ⟨1252997, by rfl⟩ : syracuseStep 1670663 = 2505995) B2505995
theorem B1113615 : Blo 1112627 1113615 := bstep (se 1 (by rfl) ⟨835211, by rfl⟩ : syracuseStep 1113615 = 1670423) B1670423
theorem B1670699 : Blo 1112627 1670699 := bstep (se 1 (by rfl) ⟨1253024, by rfl⟩ : syracuseStep 1670699 = 2506049) B2506049
theorem B1113659 : Blo 1112627 1113659 := bstep (se 1 (by rfl) ⟨835244, by rfl⟩ : syracuseStep 1113659 = 1670489) B1670489
theorem B1670729 : Blo 1112627 1670729 := bstep (se 2 (by rfl) ⟨626523, by rfl⟩ : syracuseStep 1670729 = 1253047) B1253047
theorem B1113735 : Blo 1112627 1113735 := bstep (se 1 (by rfl) ⟨835301, by rfl⟩ : syracuseStep 1113735 = 1670603) B1670603
theorem B1113743 : Blo 1112627 1113743 := bstep (se 1 (by rfl) ⟨835307, by rfl⟩ : syracuseStep 1113743 = 1670615) B1670615
theorem B1113787 : Blo 1112627 1113787 := bstep (se 1 (by rfl) ⟨835340, by rfl⟩ : syracuseStep 1113787 = 1670681) B1670681
theorem B1670843 : Blo 1112627 1670843 := bstep (se 1 (by rfl) ⟨1253132, by rfl⟩ : syracuseStep 1670843 = 2506265) B2506265
theorem B9043649 : Blo 1112627 9043649 := bstep (se 2 (by rfl) ⟨3391368, by rfl⟩ : syracuseStep 9043649 = 6782737) B6782737
theorem B2817737 : Blo 1112627 2817737 := bstep (se 2 (by rfl) ⟨1056651, by rfl⟩ : syracuseStep 2817737 = 2113303) B2113303
theorem B1670903 : Blo 1112627 1670903 := bstep (se 1 (by rfl) ⟨1253177, by rfl⟩ : syracuseStep 1670903 = 2506355) B2506355
theorem B3768065 : Blo 1112627 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B1113863 : Blo 1112627 1113863 := bstep (se 1 (by rfl) ⟨835397, by rfl⟩ : syracuseStep 1113863 = 1670795) B1670795
theorem B1113871 : Blo 1112627 1113871 := bstep (se 1 (by rfl) ⟨835403, by rfl⟩ : syracuseStep 1113871 = 1670807) B1670807
theorem B1670927 : Blo 1112627 1670927 := bstep (se 1 (by rfl) ⟨1253195, by rfl⟩ : syracuseStep 1670927 = 2506391) B2506391
theorem B4226849 : Blo 1112627 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B1670969 : Blo 1112627 1670969 := bstep (se 2 (by rfl) ⟨626613, by rfl⟩ : syracuseStep 1670969 = 1253227) B1253227
theorem B1113915 : Blo 1112627 1113915 := bstep (se 1 (by rfl) ⟨835436, by rfl⟩ : syracuseStep 1113915 = 1670873) B1670873
theorem B1113991 : Blo 1112627 1113991 := bstep (se 1 (by rfl) ⟨835493, by rfl⟩ : syracuseStep 1113991 = 1670987) B1670987
theorem B1671047 : Blo 1112627 1671047 := bstep (se 1 (by rfl) ⟨1253285, by rfl⟩ : syracuseStep 1671047 = 2506571) B2506571
theorem B1113999 : Blo 1112627 1113999 := bstep (se 1 (by rfl) ⟨835499, by rfl⟩ : syracuseStep 1113999 = 1670999) B1670999
theorem B1671083 : Blo 1112627 1671083 := bstep (se 1 (by rfl) ⟨1253312, by rfl⟩ : syracuseStep 1671083 = 2506625) B2506625
theorem B1114043 : Blo 1112627 1114043 := bstep (se 1 (by rfl) ⟨835532, by rfl⟩ : syracuseStep 1114043 = 1671065) B1671065
theorem B1507259 : Blo 1112627 1507259 := bstep (se 1 (by rfl) ⟨1130444, by rfl⟩ : syracuseStep 1507259 = 2260889) B2260889
theorem B1671113 : Blo 1112627 1671113 := bstep (se 2 (by rfl) ⟨626667, by rfl⟩ : syracuseStep 1671113 = 1253335) B1253335
theorem B3768335 : Blo 1112627 3768335 := bstep (se 1 (by rfl) ⟨2826251, by rfl⟩ : syracuseStep 3768335 = 5652503) B5652503
theorem B1114151 : Blo 1112627 1114151 := bstep (se 1 (by rfl) ⟨835613, by rfl⟩ : syracuseStep 1114151 = 1671227) B1671227
theorem B1114191 : Blo 1112627 1114191 := bstep (se 1 (by rfl) ⟨835643, by rfl⟩ : syracuseStep 1114191 = 1671287) B1671287
theorem B1114207 : Blo 1112627 1114207 := bstep (se 1 (by rfl) ⟨835655, by rfl⟩ : syracuseStep 1114207 = 1671311) B1671311
theorem B4292723 : Blo 1112627 4292723 := bstep (se 1 (by rfl) ⟨3219542, by rfl⟩ : syracuseStep 4292723 = 6439085) B6439085
theorem B1114235 : Blo 1112627 1114235 := bstep (se 1 (by rfl) ⟨835676, by rfl⟩ : syracuseStep 1114235 = 1671353) B1671353
theorem B1114287 : Blo 1112627 1114287 := bstep (se 1 (by rfl) ⟨835715, by rfl⟩ : syracuseStep 1114287 = 1671431) B1671431
theorem B1114311 : Blo 1112627 1114311 := bstep (se 1 (by rfl) ⟨835733, by rfl⟩ : syracuseStep 1114311 = 1671467) B1671467
theorem B1114331 : Blo 1112627 1114331 := bstep (se 1 (by rfl) ⟨835748, by rfl⟩ : syracuseStep 1114331 = 1671497) B1671497
theorem B1114407 : Blo 1112627 1114407 := bstep (se 1 (by rfl) ⟨835805, by rfl⟩ : syracuseStep 1114407 = 1671611) B1671611
theorem B1114447 : Blo 1112627 1114447 := bstep (se 1 (by rfl) ⟨835835, by rfl⟩ : syracuseStep 1114447 = 1671671) B1671671
theorem B1114463 : Blo 1112627 1114463 := bstep (se 1 (by rfl) ⟨835847, by rfl⟩ : syracuseStep 1114463 = 1671695) B1671695
theorem B1114491 : Blo 1112627 1114491 := bstep (se 1 (by rfl) ⟨835868, by rfl⟩ : syracuseStep 1114491 = 1671737) B1671737
theorem B1671599 : Blo 1112627 1671599 := bstep (se 1 (by rfl) ⟨1253699, by rfl⟩ : syracuseStep 1671599 = 2507399) B2507399
theorem B1114543 : Blo 1112627 1114543 := bstep (se 1 (by rfl) ⟨835907, by rfl⟩ : syracuseStep 1114543 = 1671815) B1671815
theorem B1114567 : Blo 1112627 1114567 := bstep (se 1 (by rfl) ⟨835925, by rfl⟩ : syracuseStep 1114567 = 1671851) B1671851
theorem B1114587 : Blo 1112627 1114587 := bstep (se 1 (by rfl) ⟨835940, by rfl⟩ : syracuseStep 1114587 = 1671881) B1671881
theorem B2818547 : Blo 1112627 2818547 := bstep (se 1 (by rfl) ⟨2113910, by rfl⟩ : syracuseStep 2818547 = 4227821) B4227821
theorem B1671689 : Blo 1112627 1671689 := bstep (se 2 (by rfl) ⟨626883, by rfl⟩ : syracuseStep 1671689 = 1253767) B1253767
theorem B3179033 : Blo 1112627 3179033 := bstep (se 2 (by rfl) ⟨1192137, by rfl⟩ : syracuseStep 3179033 = 2384275) B2384275
theorem B4227623 : Blo 1112627 4227623 := bstep (se 1 (by rfl) ⟨3170717, by rfl⟩ : syracuseStep 4227623 = 6341435) B6341435
theorem B1671719 : Blo 1112627 1671719 := bstep (se 1 (by rfl) ⟨1253789, by rfl⟩ : syracuseStep 1671719 = 2507579) B2507579
theorem B1114663 : Blo 1112627 1114663 := bstep (se 1 (by rfl) ⟨835997, by rfl⟩ : syracuseStep 1114663 = 1671995) B1671995
theorem B1114703 : Blo 1112627 1114703 := bstep (se 1 (by rfl) ⟨836027, by rfl⟩ : syracuseStep 1114703 = 1672055) B1672055
theorem B1114719 : Blo 1112627 1114719 := bstep (se 1 (by rfl) ⟨836039, by rfl⟩ : syracuseStep 1114719 = 1672079) B1672079
theorem B1671803 : Blo 1112627 1671803 := bstep (se 1 (by rfl) ⟨1253852, by rfl⟩ : syracuseStep 1671803 = 2507705) B2507705
theorem B1114747 : Blo 1112627 1114747 := bstep (se 1 (by rfl) ⟨836060, by rfl⟩ : syracuseStep 1114747 = 1672121) B1672121
theorem B3572363 : Blo 1112627 3572363 := bstep (se 1 (by rfl) ⟨2679272, by rfl⟩ : syracuseStep 3572363 = 5358545) B5358545
theorem B7144109 : Blo 1112627 7144109 := bstep (se 3 (by rfl) ⟨1339520, by rfl⟩ : syracuseStep 7144109 = 2679041) B2679041
theorem B1114799 : Blo 1112627 1114799 := bstep (se 1 (by rfl) ⟨836099, by rfl⟩ : syracuseStep 1114799 = 1672199) B1672199
theorem B2261675 : Blo 1112627 2261675 := bstep (se 1 (by rfl) ⟨1696256, by rfl⟩ : syracuseStep 2261675 = 3392513) B3392513
theorem B2818759 : Blo 1112627 2818759 := bstep (se 1 (by rfl) ⟨2114069, by rfl⟩ : syracuseStep 2818759 = 4228139) B4228139
theorem B1114823 : Blo 1112627 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B1114843 : Blo 1112627 1114843 := bstep (se 1 (by rfl) ⟨836132, by rfl⟩ : syracuseStep 1114843 = 1672265) B1672265
theorem B1671929 : Blo 1112627 1671929 := bstep (se 2 (by rfl) ⟨626973, by rfl⟩ : syracuseStep 1671929 = 1253947) B1253947
theorem B8454941 : Blo 1112627 8454941 := bstep (se 3 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 8454941 = 3170603) B3170603
theorem B1114919 : Blo 1112627 1114919 := bstep (se 1 (by rfl) ⟨836189, by rfl⟩ : syracuseStep 1114919 = 1672379) B1672379
theorem B1114959 : Blo 1112627 1114959 := bstep (se 1 (by rfl) ⟨836219, by rfl⟩ : syracuseStep 1114959 = 1672439) B1672439
theorem B1672031 : Blo 1112627 1672031 := bstep (se 1 (by rfl) ⟨1254023, by rfl⟩ : syracuseStep 1672031 = 2508047) B2508047
theorem B1114975 : Blo 1112627 1114975 := bstep (se 1 (by rfl) ⟨836231, by rfl⟩ : syracuseStep 1114975 = 1672463) B1672463
theorem B1672043 : Blo 1112627 1672043 := bstep (se 1 (by rfl) ⟨1254032, by rfl⟩ : syracuseStep 1672043 = 2508065) B2508065
theorem B1115003 : Blo 1112627 1115003 := bstep (se 1 (by rfl) ⟨836252, by rfl⟩ : syracuseStep 1115003 = 1672505) B1672505
theorem B1115055 : Blo 1112627 1115055 := bstep (se 1 (by rfl) ⟨836291, by rfl⟩ : syracuseStep 1115055 = 1672583) B1672583
theorem B1115079 : Blo 1112627 1115079 := bstep (se 1 (by rfl) ⟨836309, by rfl⟩ : syracuseStep 1115079 = 1672619) B1672619
theorem B1115099 : Blo 1112627 1115099 := bstep (se 1 (by rfl) ⟨836324, by rfl⟩ : syracuseStep 1115099 = 1672649) B1672649
theorem B1115175 : Blo 1112627 1115175 := bstep (se 1 (by rfl) ⟨836381, by rfl⟩ : syracuseStep 1115175 = 1672763) B1672763
theorem B1672271 : Blo 1112627 1672271 := bstep (se 1 (by rfl) ⟨1254203, by rfl⟩ : syracuseStep 1672271 = 2508407) B2508407
theorem B1115215 : Blo 1112627 1115215 := bstep (se 1 (by rfl) ⟨836411, by rfl⟩ : syracuseStep 1115215 = 1672823) B1672823
theorem B1115231 : Blo 1112627 1115231 := bstep (se 1 (by rfl) ⟨836423, by rfl⟩ : syracuseStep 1115231 = 1672847) B1672847
theorem B1115259 : Blo 1112627 1115259 := bstep (se 1 (by rfl) ⟨836444, by rfl⟩ : syracuseStep 1115259 = 1672889) B1672889
theorem B1115311 : Blo 1112627 1115311 := bstep (se 1 (by rfl) ⟨836483, by rfl⟩ : syracuseStep 1115311 = 1672967) B1672967
theorem B1672391 : Blo 1112627 1672391 := bstep (se 1 (by rfl) ⟨1254293, by rfl⟩ : syracuseStep 1672391 = 2508587) B2508587
theorem B1115335 : Blo 1112627 1115335 := bstep (se 1 (by rfl) ⟨836501, by rfl⟩ : syracuseStep 1115335 = 1673003) B1673003
theorem B1115355 : Blo 1112627 1115355 := bstep (se 1 (by rfl) ⟨836516, by rfl⟩ : syracuseStep 1115355 = 1673033) B1673033
theorem B1115431 : Blo 1112627 1115431 := bstep (se 1 (by rfl) ⟨836573, by rfl⟩ : syracuseStep 1115431 = 1673147) B1673147
theorem B1115471 : Blo 1112627 1115471 := bstep (se 1 (by rfl) ⟨836603, by rfl⟩ : syracuseStep 1115471 = 1673207) B1673207
theorem B1115487 : Blo 1112627 1115487 := bstep (se 1 (by rfl) ⟨836615, by rfl⟩ : syracuseStep 1115487 = 1673231) B1673231
theorem B1672553 : Blo 1112627 1672553 := bstep (se 2 (by rfl) ⟨627207, by rfl⟩ : syracuseStep 1672553 = 1254415) B1254415
theorem B1115515 : Blo 1112627 1115515 := bstep (se 1 (by rfl) ⟨836636, by rfl⟩ : syracuseStep 1115515 = 1673273) B1673273
theorem B1115567 : Blo 1112627 1115567 := bstep (se 1 (by rfl) ⟨836675, by rfl⟩ : syracuseStep 1115567 = 1673351) B1673351
theorem B1672631 : Blo 1112627 1672631 := bstep (se 1 (by rfl) ⟨1254473, by rfl⟩ : syracuseStep 1672631 = 2508947) B2508947
theorem B1115591 : Blo 1112627 1115591 := bstep (se 1 (by rfl) ⟨836693, by rfl⟩ : syracuseStep 1115591 = 1673387) B1673387
theorem B1672667 : Blo 1112627 1672667 := bstep (se 1 (by rfl) ⟨1254500, by rfl⟩ : syracuseStep 1672667 = 2509001) B2509001
theorem B1115611 : Blo 1112627 1115611 := bstep (se 1 (by rfl) ⟨836708, by rfl⟩ : syracuseStep 1115611 = 1673417) B1673417
theorem B4228595 : Blo 1112627 4228595 := bstep (se 1 (by rfl) ⟨3171446, by rfl⟩ : syracuseStep 4228595 = 6342893) B6342893
theorem B1115687 : Blo 1112627 1115687 := bstep (se 1 (by rfl) ⟨836765, by rfl⟩ : syracuseStep 1115687 = 1673531) B1673531
theorem B1115727 : Blo 1112627 1115727 := bstep (se 1 (by rfl) ⟨836795, by rfl⟩ : syracuseStep 1115727 = 1673591) B1673591
theorem B1115743 : Blo 1112627 1115743 := bstep (se 1 (by rfl) ⟨836807, by rfl⟩ : syracuseStep 1115743 = 1673615) B1673615
theorem B2819681 : Blo 1112627 2819681 := bstep (se 2 (by rfl) ⟨1057380, by rfl⟩ : syracuseStep 2819681 = 2114761) B2114761
theorem B4753019 : Blo 1112627 4753019 := bstep (se 1 (by rfl) ⟨3564764, by rfl⟩ : syracuseStep 4753019 = 7129529) B7129529
theorem B1115771 : Blo 1112627 1115771 := bstep (se 1 (by rfl) ⟨836828, by rfl⟩ : syracuseStep 1115771 = 1673657) B1673657
theorem B3212939 : Blo 1112627 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B34309777 : Blo 1112627 34309777 := bstep (se 2 (by rfl) ⟨12866166, by rfl⟩ : syracuseStep 34309777 = 25732333) B25732333
theorem B1115823 : Blo 1112627 1115823 := bstep (se 1 (by rfl) ⟨836867, by rfl⟩ : syracuseStep 1115823 = 1673735) B1673735
theorem B4228793 : Blo 1112627 4228793 := bstep (se 2 (by rfl) ⟨1585797, by rfl⟩ : syracuseStep 4228793 = 3171595) B3171595
theorem B4228807 : Blo 1112627 4228807 := bstep (se 1 (by rfl) ⟨3171605, by rfl⟩ : syracuseStep 4228807 = 6343211) B6343211
theorem B1115847 : Blo 1112627 1115847 := bstep (se 1 (by rfl) ⟨836885, by rfl⟩ : syracuseStep 1115847 = 1673771) B1673771
theorem B1115867 : Blo 1112627 1115867 := bstep (se 1 (by rfl) ⟨836900, by rfl⟩ : syracuseStep 1115867 = 1673801) B1673801
theorem B1115943 : Blo 1112627 1115943 := bstep (se 1 (by rfl) ⟨836957, by rfl⟩ : syracuseStep 1115943 = 1673915) B1673915
theorem B1115983 : Blo 1112627 1115983 := bstep (se 1 (by rfl) ⟨836987, by rfl⟩ : syracuseStep 1115983 = 1673975) B1673975
theorem B1115999 : Blo 1112627 1115999 := bstep (se 1 (by rfl) ⟨836999, by rfl⟩ : syracuseStep 1115999 = 1673999) B1673999
theorem B3868535 : Blo 1112627 3868535 := bstep (se 1 (by rfl) ⟨2901401, by rfl⟩ : syracuseStep 3868535 = 5802803) B5802803
theorem B1116027 : Blo 1112627 1116027 := bstep (se 1 (by rfl) ⟨837020, by rfl⟩ : syracuseStep 1116027 = 1674041) B1674041
theorem B1673135 : Blo 1112627 1673135 := bstep (se 1 (by rfl) ⟨1254851, by rfl⟩ : syracuseStep 1673135 = 2509703) B2509703
theorem B1116079 : Blo 1112627 1116079 := bstep (se 1 (by rfl) ⟨837059, by rfl⟩ : syracuseStep 1116079 = 1674119) B1674119
theorem B1116103 : Blo 1112627 1116103 := bstep (se 1 (by rfl) ⟨837077, by rfl⟩ : syracuseStep 1116103 = 1674155) B1674155
theorem B1116123 : Blo 1112627 1116123 := bstep (se 1 (by rfl) ⟨837092, by rfl⟩ : syracuseStep 1116123 = 1674185) B1674185
theorem B1673225 : Blo 1112627 1673225 := bstep (se 2 (by rfl) ⟨627459, by rfl⟩ : syracuseStep 1673225 = 1254919) B1254919
theorem B1411111 : Blo 1112627 1411111 := bstep (se 1 (by rfl) ⟨1058333, by rfl⟩ : syracuseStep 1411111 = 2116667) B2116667
theorem B1673255 : Blo 1112627 1673255 := bstep (se 1 (by rfl) ⟨1254941, by rfl⟩ : syracuseStep 1673255 = 2509883) B2509883
theorem B1116199 : Blo 1112627 1116199 := bstep (se 1 (by rfl) ⟨837149, by rfl⟩ : syracuseStep 1116199 = 1674299) B1674299
theorem B1116239 : Blo 1112627 1116239 := bstep (se 1 (by rfl) ⟨837179, by rfl⟩ : syracuseStep 1116239 = 1674359) B1674359
theorem B4524113 : Blo 1112627 4524113 := bstep (se 2 (by rfl) ⟨1696542, by rfl⟩ : syracuseStep 4524113 = 3393085) B3393085
theorem B1116255 : Blo 1112627 1116255 := bstep (se 1 (by rfl) ⟨837191, by rfl⟩ : syracuseStep 1116255 = 1674383) B1674383
theorem B1673339 : Blo 1112627 1673339 := bstep (se 1 (by rfl) ⟨1255004, by rfl⟩ : syracuseStep 1673339 = 2510009) B2510009
theorem B1116283 : Blo 1112627 1116283 := bstep (se 1 (by rfl) ⟨837212, by rfl⟩ : syracuseStep 1116283 = 1674425) B1674425
theorem B1116335 : Blo 1112627 1116335 := bstep (se 1 (by rfl) ⟨837251, by rfl⟩ : syracuseStep 1116335 = 1674503) B1674503
theorem B1116359 : Blo 1112627 1116359 := bstep (se 1 (by rfl) ⟨837269, by rfl⟩ : syracuseStep 1116359 = 1674539) B1674539
theorem B1116379 : Blo 1112627 1116379 := bstep (se 1 (by rfl) ⟨837284, by rfl⟩ : syracuseStep 1116379 = 1674569) B1674569
theorem B1673465 : Blo 1112627 1673465 := bstep (se 2 (by rfl) ⟨627549, by rfl⟩ : syracuseStep 1673465 = 1255099) B1255099
theorem B1116455 : Blo 1112627 1116455 := bstep (se 1 (by rfl) ⟨837341, by rfl⟩ : syracuseStep 1116455 = 1674683) B1674683
theorem B1116495 : Blo 1112627 1116495 := bstep (se 1 (by rfl) ⟨837371, by rfl⟩ : syracuseStep 1116495 = 1674743) B1674743
theorem B1673567 : Blo 1112627 1673567 := bstep (se 1 (by rfl) ⟨1255175, by rfl⟩ : syracuseStep 1673567 = 2510351) B2510351
theorem B1116511 : Blo 1112627 1116511 := bstep (se 1 (by rfl) ⟨837383, by rfl⟩ : syracuseStep 1116511 = 1674767) B1674767
theorem B1411435 : Blo 1112627 1411435 := bstep (se 1 (by rfl) ⟨1058576, by rfl⟩ : syracuseStep 1411435 = 2117153) B2117153
theorem B1673579 : Blo 1112627 1673579 := bstep (se 1 (by rfl) ⟨1255184, by rfl⟩ : syracuseStep 1673579 = 2510369) B2510369
theorem B1116539 : Blo 1112627 1116539 := bstep (se 1 (by rfl) ⟨837404, by rfl⟩ : syracuseStep 1116539 = 1674809) B1674809
theorem B1116591 : Blo 1112627 1116591 := bstep (se 1 (by rfl) ⟨837443, by rfl⟩ : syracuseStep 1116591 = 1674887) B1674887
theorem B1116615 : Blo 1112627 1116615 := bstep (se 1 (by rfl) ⟨837461, by rfl⟩ : syracuseStep 1116615 = 1674923) B1674923
theorem B1411663 : Blo 1112627 1411663 := bstep (se 1 (by rfl) ⟨1058747, by rfl⟩ : syracuseStep 1411663 = 2117495) B2117495
theorem B1673807 : Blo 1112627 1673807 := bstep (se 1 (by rfl) ⟨1255355, by rfl⟩ : syracuseStep 1673807 = 2510711) B2510711
theorem B3017339 : Blo 1112627 3017339 := bstep (se 1 (by rfl) ⟨2263004, by rfl⟩ : syracuseStep 3017339 = 4526009) B4526009
theorem B4229779 : Blo 1112627 4229779 := bstep (se 1 (by rfl) ⟨3172334, by rfl⟩ : syracuseStep 4229779 = 6344669) B6344669
theorem B1673927 : Blo 1112627 1673927 := bstep (se 1 (by rfl) ⟨1255445, by rfl⟩ : syracuseStep 1673927 = 2510891) B2510891
theorem B1674089 : Blo 1112627 1674089 := bstep (se 2 (by rfl) ⟨627783, by rfl⟩ : syracuseStep 1674089 = 1255567) B1255567
theorem B1674167 : Blo 1112627 1674167 := bstep (se 1 (by rfl) ⟨1255625, by rfl⟩ : syracuseStep 1674167 = 2511251) B2511251
theorem B1674203 : Blo 1112627 1674203 := bstep (se 1 (by rfl) ⟨1255652, by rfl⟩ : syracuseStep 1674203 = 2511305) B2511305
theorem B2821139 : Blo 1112627 2821139 := bstep (se 1 (by rfl) ⟨2115854, by rfl⟩ : syracuseStep 2821139 = 4231709) B4231709
theorem B5639219 : Blo 1112627 5639219 := bstep (se 1 (by rfl) ⟨4229414, by rfl⟩ : syracuseStep 5639219 = 8458829) B8458829
theorem B9637157 : Blo 1112627 9637157 := bstep (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) B1806967
theorem B1674671 : Blo 1112627 1674671 := bstep (se 1 (by rfl) ⟨1256003, by rfl⟩ : syracuseStep 1674671 = 2512007) B2512007
theorem B1674761 : Blo 1112627 1674761 := bstep (se 2 (by rfl) ⟨628035, by rfl⟩ : syracuseStep 1674761 = 1256071) B1256071
theorem B4754983 : Blo 1112627 4754983 := bstep (se 1 (by rfl) ⟨3566237, by rfl⟩ : syracuseStep 4754983 = 7132475) B7132475
theorem B3575335 : Blo 1112627 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B1674791 : Blo 1112627 1674791 := bstep (se 1 (by rfl) ⟨1256093, by rfl⟩ : syracuseStep 1674791 = 2512187) B2512187
theorem B1412731 : Blo 1112627 1412731 := bstep (se 1 (by rfl) ⟨1059548, by rfl⟩ : syracuseStep 1412731 = 2119097) B2119097
theorem B1674875 : Blo 1112627 1674875 := bstep (se 1 (by rfl) ⟨1256156, by rfl⟩ : syracuseStep 1674875 = 2512313) B2512313
theorem B9047801 : Blo 1112627 9047801 := bstep (se 2 (by rfl) ⟨3392925, by rfl⟩ : syracuseStep 9047801 = 6785851) B6785851
theorem B1412959 : Blo 1112627 1412959 := bstep (se 1 (by rfl) ⟨1059719, by rfl⟩ : syracuseStep 1412959 = 2119439) B2119439
theorem B48172913 : Blo 1112627 48172913 := bstep (se 2 (by rfl) ⟨18064842, by rfl⟩ : syracuseStep 48172913 = 36129685) B36129685
theorem B3575735 : Blo 1112627 3575735 := bstep (se 1 (by rfl) ⟨2681801, by rfl⟩ : syracuseStep 3575735 = 5363603) B5363603
theorem B4231511 : Blo 1112627 4231511 := bstep (se 1 (by rfl) ⟨3173633, by rfl⟩ : syracuseStep 4231511 = 6347267) B6347267
theorem B8032715 : Blo 1112627 8032715 := bstep (se 1 (by rfl) ⟨6024536, by rfl⟩ : syracuseStep 8032715 = 12049073) B12049073
theorem B5640839 : Blo 1112627 5640839 := bstep (se 1 (by rfl) ⟨4230629, by rfl⟩ : syracuseStep 5640839 = 8461259) B8461259
theorem B3052171 : Blo 1112627 3052171 := bstep (se 1 (by rfl) ⟨2289128, by rfl⟩ : syracuseStep 3052171 = 4578257) B4578257
theorem B2036755 : Blo 1112627 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B8459315 : Blo 1112627 8459315 := bstep (se 1 (by rfl) ⟨6344486, by rfl⟩ : syracuseStep 8459315 = 12688973) B12688973
theorem B13046903 : Blo 1112627 13046903 := bstep (se 1 (by rfl) ⟨9785177, by rfl⟩ : syracuseStep 13046903 = 19570355) B19570355
theorem B30545099 : Blo 1112627 30545099 := bstep (se 1 (by rfl) ⟨22908824, by rfl⟩ : syracuseStep 30545099 = 45817649) B45817649
theorem B4068713 : Blo 1112627 4068713 := bstep (se 2 (by rfl) ⟨1525767, by rfl⟩ : syracuseStep 4068713 = 3051535) B3051535
theorem B18060691 : Blo 1112627 18060691 := bstep (se 1 (by rfl) ⟨13545518, by rfl⟩ : syracuseStep 18060691 = 27091037) B27091037
theorem B3806969 : Blo 1112627 3806969 := bstep (se 2 (by rfl) ⟨1427613, by rfl⟩ : syracuseStep 3806969 = 2855227) B2855227
theorem B20322083 : Blo 1112627 20322083 := bstep (se 1 (by rfl) ⟨15241562, by rfl⟩ : syracuseStep 20322083 = 30483125) B30483125
theorem B18061217 : Blo 1112627 18061217 := bstep (se 2 (by rfl) ⟨6772956, by rfl⟩ : syracuseStep 18061217 = 13545913) B13545913
theorem B8034241 : Blo 1112627 8034241 := bstep (se 2 (by rfl) ⟨3012840, by rfl⟩ : syracuseStep 8034241 = 6025681) B6025681
theorem B5642297 : Blo 1112627 5642297 := bstep (se 2 (by rfl) ⟨2115861, by rfl⟩ : syracuseStep 5642297 = 4231723) B4231723
theorem B2824591 : Blo 1112627 2824591 := bstep (se 1 (by rfl) ⟨2118443, by rfl⟩ : syracuseStep 2824591 = 4236887) B4236887
theorem B1252039 : Blo 1112627 1252039 := bstep (se 1 (by rfl) ⟨939029, by rfl⟩ : syracuseStep 1252039 = 1878059) B1878059
theorem B2824915 : Blo 1112627 2824915 := bstep (se 1 (by rfl) ⟨2118686, by rfl⟩ : syracuseStep 2824915 = 4237373) B4237373
theorem B3054431 : Blo 1112627 3054431 := bstep (se 1 (by rfl) ⟨2290823, by rfl⟩ : syracuseStep 3054431 = 4581647) B4581647
theorem B28941391 : Blo 1112627 28941391 := bstep (se 1 (by rfl) ⟨21706043, by rfl⟩ : syracuseStep 28941391 = 43412087) B43412087
theorem B16063757 : Blo 1112627 16063757 := bstep (se 3 (by rfl) ⟨3011954, by rfl⟩ : syracuseStep 16063757 = 6023909) B6023909
theorem B4234625 : Blo 1112627 4234625 := bstep (se 2 (by rfl) ⟨1587984, by rfl⟩ : syracuseStep 4234625 = 3175969) B3175969
theorem B4234639 : Blo 1112627 4234639 := bstep (se 1 (by rfl) ⟨3175979, by rfl⟩ : syracuseStep 4234639 = 6351959) B6351959
theorem B1252903 : Blo 1112627 1252903 := bstep (se 1 (by rfl) ⟨939677, by rfl⟩ : syracuseStep 1252903 = 1879355) B1879355
theorem B2825867 : Blo 1112627 2825867 := bstep (se 1 (by rfl) ⟨2119400, by rfl⟩ : syracuseStep 2825867 = 4238801) B4238801
theorem B4759391 : Blo 1112627 4759391 := bstep (se 1 (by rfl) ⟨3569543, by rfl⟩ : syracuseStep 4759391 = 7139087) B7139087
theorem B5644403 : Blo 1112627 5644403 := bstep (se 1 (by rfl) ⟨4233302, by rfl⟩ : syracuseStep 5644403 = 8466605) B8466605
theorem B3383657 : Blo 1112627 3383657 := bstep (se 2 (by rfl) ⟨1268871, by rfl⟩ : syracuseStep 3383657 = 2537743) B2537743
theorem B10166809 : Blo 1112627 10166809 := bstep (se 2 (by rfl) ⟨3812553, by rfl⟩ : syracuseStep 10166809 = 7625107) B7625107
theorem B4235915 : Blo 1112627 4235915 := bstep (se 1 (by rfl) ⟨3176936, by rfl⟩ : syracuseStep 4235915 = 6353873) B6353873
theorem B1188703 : Blo 1112627 1188703 := bstep (se 1 (by rfl) ⟨891527, by rfl⟩ : syracuseStep 1188703 = 1783055) B1783055
theorem B5350319 : Blo 1112627 5350319 := bstep (se 1 (by rfl) ⟨4012739, by rfl⟩ : syracuseStep 5350319 = 8025479) B8025479
theorem B1254523 : Blo 1112627 1254523 := bstep (se 1 (by rfl) ⟨940892, by rfl⟩ : syracuseStep 1254523 = 1881785) B1881785
theorem B4826611 : Blo 1112627 4826611 := bstep (se 1 (by rfl) ⟨3619958, by rfl⟩ : syracuseStep 4826611 = 7239917) B7239917
theorem B1254991 : Blo 1112627 1254991 := bstep (se 1 (by rfl) ⟨941243, by rfl⟩ : syracuseStep 1254991 = 1882487) B1882487
theorem B1877627 : Blo 1112627 1877627 := bstep (se 1 (by rfl) ⟨1408220, by rfl⟩ : syracuseStep 1877627 = 2816441) B2816441
theorem B5646023 : Blo 1112627 5646023 := bstep (se 1 (by rfl) ⟨4234517, by rfl⟩ : syracuseStep 5646023 = 8469035) B8469035
theorem B7153595 : Blo 1112627 7153595 := bstep (se 1 (by rfl) ⟨5365196, by rfl⟩ : syracuseStep 7153595 = 10730393) B10730393
theorem B1255387 : Blo 1112627 1255387 := bstep (se 1 (by rfl) ⟨941540, by rfl⟩ : syracuseStep 1255387 = 1883081) B1883081
theorem B1878025 : Blo 1112627 1878025 := bstep (se 2 (by rfl) ⟨704259, by rfl⟩ : syracuseStep 1878025 = 1408519) B1408519
theorem B1878187 : Blo 1112627 1878187 := bstep (se 1 (by rfl) ⟨1408640, by rfl⟩ : syracuseStep 1878187 = 2817281) B2817281
theorem B1255855 : Blo 1112627 1255855 := bstep (se 1 (by rfl) ⟨941891, by rfl⟩ : syracuseStep 1255855 = 1883783) B1883783
theorem B1878491 : Blo 1112627 1878491 := bstep (se 1 (by rfl) ⟨1408868, by rfl⟩ : syracuseStep 1878491 = 2817737) B2817737
theorem B1878727 : Blo 1112627 1878727 := bstep (se 1 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 1878727 = 2818091) B2818091
theorem B1878889 : Blo 1112627 1878889 := bstep (se 2 (by rfl) ⟨704583, by rfl⟩ : syracuseStep 1878889 = 1409167) B1409167
theorem B13544741 : Blo 1112627 13544741 := bstep (se 4 (by rfl) ⟨1269819, by rfl⟩ : syracuseStep 13544741 = 2539639) B2539639
theorem B4074895 : Blo 1112627 4074895 := bstep (se 1 (by rfl) ⟨3056171, by rfl⟩ : syracuseStep 4074895 = 6112343) B6112343
theorem B1191343 : Blo 1112627 1191343 := bstep (se 1 (by rfl) ⟨893507, by rfl⟩ : syracuseStep 1191343 = 1787015) B1787015
theorem B1879483 : Blo 1112627 1879483 := bstep (se 1 (by rfl) ⟨1409612, by rfl⟩ : syracuseStep 1879483 = 2819225) B2819225
theorem B1879591 : Blo 1112627 1879591 := bstep (se 1 (by rfl) ⟨1409693, by rfl⟩ : syracuseStep 1879591 = 2819387) B2819387
theorem B8466119 : Blo 1112627 8466119 := bstep (se 1 (by rfl) ⟨6349589, by rfl⟩ : syracuseStep 8466119 = 12699179) B12699179
theorem B1879915 : Blo 1112627 1879915 := bstep (se 1 (by rfl) ⟨1409936, by rfl⟩ : syracuseStep 1879915 = 2819873) B2819873
theorem B2011063 : Blo 1112627 2011063 := bstep (se 1 (by rfl) ⟨1508297, by rfl⟩ : syracuseStep 2011063 = 3016595) B3016595
theorem B4239287 : Blo 1112627 4239287 := bstep (se 1 (by rfl) ⟨3179465, by rfl⟩ : syracuseStep 4239287 = 6358931) B6358931
theorem B6434747 : Blo 1112627 6434747 := bstep (se 1 (by rfl) ⟨4826060, by rfl⟩ : syracuseStep 6434747 = 9652121) B9652121
theorem B1192411 : Blo 1112627 1192411 := bstep (se 1 (by rfl) ⟨894308, by rfl⟩ : syracuseStep 1192411 = 1788617) B1788617
theorem B5354009 : Blo 1112627 5354009 := bstep (se 2 (by rfl) ⟨2007753, by rfl⟩ : syracuseStep 5354009 = 4015507) B4015507
theorem B1880975 : Blo 1112627 1880975 := bstep (se 1 (by rfl) ⟨1410731, by rfl⟩ : syracuseStep 1880975 = 2821463) B2821463
theorem B1586299 : Blo 1112627 1586299 := bstep (se 1 (by rfl) ⟨1189724, by rfl⟩ : syracuseStep 1586299 = 2379449) B2379449
theorem B1881211 : Blo 1112627 1881211 := bstep (se 1 (by rfl) ⟨1410908, by rfl⟩ : syracuseStep 1881211 = 2821817) B2821817
theorem B6338087 : Blo 1112627 6338087 := bstep (se 1 (by rfl) ⟨4753565, by rfl⟩ : syracuseStep 6338087 = 9507131) B9507131
theorem B2504231 : Blo 1112627 2504231 := bstep (se 1 (by rfl) ⟨1878173, by rfl⟩ : syracuseStep 2504231 = 3756347) B3756347
theorem B9025157 : Blo 1112627 9025157 := bstep (se 4 (by rfl) ⟨846108, by rfl⟩ : syracuseStep 9025157 = 1692217) B1692217
theorem B2504555 : Blo 1112627 2504555 := bstep (se 1 (by rfl) ⟨1878416, by rfl⟩ : syracuseStep 2504555 = 3756833) B3756833
theorem B2504609 : Blo 1112627 2504609 := bstep (se 2 (by rfl) ⟨939228, by rfl⟩ : syracuseStep 2504609 = 1878457) B1878457
theorem B18102209 : Blo 1112627 18102209 := bstep (se 2 (by rfl) ⟨6788328, by rfl⟩ : syracuseStep 18102209 = 13576657) B13576657
theorem B1882075 : Blo 1112627 1882075 := bstep (se 1 (by rfl) ⟨1411556, by rfl⟩ : syracuseStep 1882075 = 2823113) B2823113
theorem B3487915 : Blo 1112627 3487915 := bstep (se 1 (by rfl) ⟨2615936, by rfl⟩ : syracuseStep 3487915 = 5231873) B5231873
theorem B2504951 : Blo 1112627 2504951 := bstep (se 1 (by rfl) ⟨1878713, by rfl⟩ : syracuseStep 2504951 = 3757427) B3757427
theorem B4012507 : Blo 1112627 4012507 := bstep (se 1 (by rfl) ⟨3009380, by rfl⟩ : syracuseStep 4012507 = 6018761) B6018761
theorem B4012553 : Blo 1112627 4012553 := bstep (se 2 (by rfl) ⟨1504707, by rfl⟩ : syracuseStep 4012553 = 3009415) B3009415
theorem B1882703 : Blo 1112627 1882703 := bstep (se 1 (by rfl) ⟨1412027, by rfl⟩ : syracuseStep 1882703 = 2824055) B2824055
theorem B4012667 : Blo 1112627 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B1784567 : Blo 1112627 1784567 := bstep (se 1 (by rfl) ⟨1338425, by rfl⟩ : syracuseStep 1784567 = 2676851) B2676851
theorem B6109955 : Blo 1112627 6109955 := bstep (se 1 (by rfl) ⟨4582466, by rfl⟩ : syracuseStep 6109955 = 9164933) B9164933
theorem B2505545 : Blo 1112627 2505545 := bstep (se 2 (by rfl) ⟨939579, by rfl⟩ : syracuseStep 2505545 = 1879159) B1879159
theorem B4897643 : Blo 1112627 4897643 := bstep (se 1 (by rfl) ⟨3673232, by rfl⟩ : syracuseStep 4897643 = 7346465) B7346465
theorem B1784759 : Blo 1112627 1784759 := bstep (se 1 (by rfl) ⟨1338569, by rfl⟩ : syracuseStep 1784759 = 2677139) B2677139
theorem B2112475 : Blo 1112627 2112475 := bstep (se 1 (by rfl) ⟨1584356, by rfl⟩ : syracuseStep 2112475 = 3168713) B3168713
theorem B2112551 : Blo 1112627 2112551 := bstep (se 1 (by rfl) ⟨1584413, by rfl⟩ : syracuseStep 2112551 = 3168827) B3168827
theorem B2145377 : Blo 1112627 2145377 := bstep (se 2 (by rfl) ⟨804516, by rfl⟩ : syracuseStep 2145377 = 1609033) B1609033
theorem B2112635 : Blo 1112627 2112635 := bstep (se 1 (by rfl) ⟨1584476, by rfl⟩ : syracuseStep 2112635 = 3168953) B3168953
theorem B1588423 : Blo 1112627 1588423 := bstep (se 1 (by rfl) ⟨1191317, by rfl⟩ : syracuseStep 1588423 = 2382635) B2382635
theorem B5651855 : Blo 1112627 5651855 := bstep (se 1 (by rfl) ⟨4238891, by rfl⟩ : syracuseStep 5651855 = 8477783) B8477783
theorem B1883567 : Blo 1112627 1883567 := bstep (se 1 (by rfl) ⟨1412675, by rfl⟩ : syracuseStep 1883567 = 2825351) B2825351
theorem B2113121 : Blo 1112627 2113121 := bstep (se 2 (by rfl) ⟨792420, by rfl⟩ : syracuseStep 2113121 = 1584841) B1584841
theorem B2506337 : Blo 1112627 2506337 := bstep (se 2 (by rfl) ⟨939876, by rfl⟩ : syracuseStep 2506337 = 1879753) B1879753
theorem B6340295 : Blo 1112627 6340295 := bstep (se 1 (by rfl) ⟨4755221, by rfl⟩ : syracuseStep 6340295 = 9510443) B9510443
theorem B5881643 : Blo 1112627 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B1883999 : Blo 1112627 1883999 := bstep (se 1 (by rfl) ⟨1412999, by rfl⟩ : syracuseStep 1883999 = 2825999) B2825999
theorem B2506679 : Blo 1112627 2506679 := bstep (se 1 (by rfl) ⟨1880009, by rfl⟩ : syracuseStep 2506679 = 3760019) B3760019
theorem B1786207 : Blo 1112627 1786207 := bstep (se 1 (by rfl) ⟨1339655, by rfl⟩ : syracuseStep 1786207 = 2679311) B2679311
theorem B4768105 : Blo 1112627 4768105 := bstep (se 2 (by rfl) ⟨1788039, by rfl⟩ : syracuseStep 4768105 = 3576079) B3576079
theorem B2507273 : Blo 1112627 2507273 := bstep (se 2 (by rfl) ⟨940227, by rfl⟩ : syracuseStep 2507273 = 1880455) B1880455
theorem B9519875 : Blo 1112627 9519875 := bstep (se 1 (by rfl) ⟨7139906, by rfl⟩ : syracuseStep 9519875 = 14279813) B14279813
theorem B2507615 : Blo 1112627 2507615 := bstep (se 1 (by rfl) ⟨1880711, by rfl⟩ : syracuseStep 2507615 = 3761423) B3761423
theorem B10175489 : Blo 1112627 10175489 := bstep (se 2 (by rfl) ⟨3815808, by rfl⟩ : syracuseStep 10175489 = 7631617) B7631617
theorem B2114579 : Blo 1112627 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B2507795 : Blo 1112627 2507795 := bstep (se 1 (by rfl) ⟨1880846, by rfl⟩ : syracuseStep 2507795 = 3761693) B3761693
theorem B1131559 : Blo 1112627 1131559 := bstep (se 1 (by rfl) ⟨848669, by rfl⟩ : syracuseStep 1131559 = 1697339) B1697339
theorem B2508137 : Blo 1112627 2508137 := bstep (se 2 (by rfl) ⟨940551, by rfl⟩ : syracuseStep 2508137 = 1881103) B1881103
theorem B3622249 : Blo 1112627 3622249 := bstep (se 2 (by rfl) ⟨1358343, by rfl⟩ : syracuseStep 3622249 = 2716687) B2716687
theorem B8471951 : Blo 1112627 8471951 := bstep (se 1 (by rfl) ⟨6353963, by rfl⟩ : syracuseStep 8471951 = 12707927) B12707927
theorem B18106105 : Blo 1112627 18106105 := bstep (se 2 (by rfl) ⟨6789789, by rfl⟩ : syracuseStep 18106105 = 13579579) B13579579
theorem B2508731 : Blo 1112627 2508731 := bstep (se 1 (by rfl) ⟨1881548, by rfl⟩ : syracuseStep 2508731 = 3763097) B3763097
theorem B9029569 : Blo 1112627 9029569 := bstep (se 2 (by rfl) ⟨3386088, by rfl⟩ : syracuseStep 9029569 = 6772177) B6772177
theorem B2508857 : Blo 1112627 2508857 := bstep (se 2 (by rfl) ⟨940821, by rfl⟩ : syracuseStep 2508857 = 1881643) B1881643
theorem B4016243 : Blo 1112627 4016243 := bstep (se 1 (by rfl) ⟨3012182, by rfl⟩ : syracuseStep 4016243 = 6024365) B6024365
theorem B2378089 : Blo 1112627 2378089 := bstep (se 2 (by rfl) ⟨891783, by rfl⟩ : syracuseStep 2378089 = 1783567) B1783567
theorem B2115983 : Blo 1112627 2115983 := bstep (se 1 (by rfl) ⟨1586987, by rfl⟩ : syracuseStep 2115983 = 3173975) B3173975
theorem B2509199 : Blo 1112627 2509199 := bstep (se 1 (by rfl) ⟨1881899, by rfl⟩ : syracuseStep 2509199 = 3763799) B3763799
theorem B2116135 : Blo 1112627 2116135 := bstep (se 1 (by rfl) ⟨1587101, by rfl⟩ : syracuseStep 2116135 = 3174203) B3174203
theorem B2116219 : Blo 1112627 2116219 := bstep (se 1 (by rfl) ⟨1587164, by rfl⟩ : syracuseStep 2116219 = 3174329) B3174329
theorem B1788539 : Blo 1112627 1788539 := bstep (se 1 (by rfl) ⟨1341404, by rfl⟩ : syracuseStep 1788539 = 2682809) B2682809
theorem B2509523 : Blo 1112627 2509523 := bstep (se 1 (by rfl) ⟨1882142, by rfl⟩ : syracuseStep 2509523 = 3764285) B3764285
theorem B21449549 : Blo 1112627 21449549 := bstep (se 3 (by rfl) ⟨4021790, by rfl⟩ : syracuseStep 21449549 = 8043581) B8043581
theorem B325241891 : Blo 1112627 325241891 := bstep (se 1 (by rfl) ⟨243931418, by rfl⟩ : syracuseStep 325241891 = 487862837) B487862837
theorem B6016079 : Blo 1112627 6016079 := bstep (se 1 (by rfl) ⟨4512059, by rfl⟩ : syracuseStep 6016079 = 9024119) B9024119
theorem B2116705 : Blo 1112627 2116705 := bstep (se 2 (by rfl) ⟨793764, by rfl⟩ : syracuseStep 2116705 = 1587529) B1587529
theorem B2674063 : Blo 1112627 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B3755483 : Blo 1112627 3755483 := bstep (se 1 (by rfl) ⟨2816612, by rfl⟩ : syracuseStep 3755483 = 5633225) B5633225
theorem B2510459 : Blo 1112627 2510459 := bstep (se 1 (by rfl) ⟨1882844, by rfl⟩ : syracuseStep 2510459 = 3765689) B3765689
theorem B6770425 : Blo 1112627 6770425 := bstep (se 2 (by rfl) ⟨2538909, by rfl⟩ : syracuseStep 6770425 = 5077819) B5077819
theorem B2510585 : Blo 1112627 2510585 := bstep (se 2 (by rfl) ⟨941469, by rfl⟩ : syracuseStep 2510585 = 1882939) B1882939
theorem B16305953 : Blo 1112627 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B2674505 : Blo 1112627 2674505 := bstep (se 2 (by rfl) ⟨1002939, by rfl⟩ : syracuseStep 2674505 = 2005879) B2005879
theorem B2379593 : Blo 1112627 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B4018015 : Blo 1112627 4018015 := bstep (se 1 (by rfl) ⟨3013511, by rfl⟩ : syracuseStep 4018015 = 6027023) B6027023
theorem B2117639 : Blo 1112627 2117639 := bstep (se 1 (by rfl) ⟨1588229, by rfl⟩ : syracuseStep 2117639 = 3176459) B3176459
theorem B2510855 : Blo 1112627 2510855 := bstep (se 1 (by rfl) ⟨1883141, by rfl⟩ : syracuseStep 2510855 = 3766283) B3766283
theorem B2510927 : Blo 1112627 2510927 := bstep (se 1 (by rfl) ⟨1883195, by rfl⟩ : syracuseStep 2510927 = 3766391) B3766391
theorem B3756185 : Blo 1112627 3756185 := bstep (se 2 (by rfl) ⟨1408569, by rfl⟩ : syracuseStep 3756185 = 2817139) B2817139
theorem B8147249 : Blo 1112627 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B1691999 : Blo 1112627 1691999 := bstep (se 1 (by rfl) ⟨1268999, by rfl⟩ : syracuseStep 1691999 = 2537999) B2537999
theorem B2511323 : Blo 1112627 2511323 := bstep (se 1 (by rfl) ⟨1883492, by rfl⟩ : syracuseStep 2511323 = 3766985) B3766985
theorem B2118163 : Blo 1112627 2118163 := bstep (se 1 (by rfl) ⟨1588622, by rfl⟩ : syracuseStep 2118163 = 3177245) B3177245
theorem B2380499 : Blo 1112627 2380499 := bstep (se 1 (by rfl) ⟨1785374, by rfl⟩ : syracuseStep 2380499 = 3570749) B3570749
theorem B2511791 : Blo 1112627 2511791 := bstep (se 1 (by rfl) ⟨1883843, by rfl⟩ : syracuseStep 2511791 = 3767687) B3767687
theorem B4019357 : Blo 1112627 4019357 := bstep (se 3 (by rfl) ⟨753629, by rfl⟩ : syracuseStep 4019357 = 1507259) B1507259
theorem B2512043 : Blo 1112627 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B3757373 : Blo 1112627 3757373 := bstep (se 3 (by rfl) ⟨704507, by rfl⟩ : syracuseStep 3757373 = 1409015) B1409015
theorem B6346127 : Blo 1112627 6346127 := bstep (se 1 (by rfl) ⟨4759595, by rfl⟩ : syracuseStep 6346127 = 9519191) B9519191
theorem B4511447 : Blo 1112627 4511447 := bstep (se 1 (by rfl) ⟨3383585, by rfl⟩ : syracuseStep 4511447 = 6767171) B6767171
theorem B4511801 : Blo 1112627 4511801 := bstep (se 2 (by rfl) ⟨1691925, by rfl⟩ : syracuseStep 4511801 = 3383851) B3383851
theorem B3758237 : Blo 1112627 3758237 := bstep (se 3 (by rfl) ⟨704669, by rfl⟩ : syracuseStep 3758237 = 1409339) B1409339
theorem B2545835 : Blo 1112627 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B5364233 : Blo 1112627 5364233 := bstep (se 2 (by rfl) ⟨2011587, by rfl⟩ : syracuseStep 5364233 = 4023175) B4023175
theorem B3758777 : Blo 1112627 3758777 := bstep (se 2 (by rfl) ⟨1409541, by rfl⟩ : syracuseStep 3758777 = 2819083) B2819083
theorem B3759371 : Blo 1112627 3759371 := bstep (se 1 (by rfl) ⟨2819528, by rfl⟩ : syracuseStep 3759371 = 5639057) B5639057
theorem B3759641 : Blo 1112627 3759641 := bstep (se 2 (by rfl) ⟨1409865, by rfl⟩ : syracuseStep 3759641 = 2819731) B2819731
theorem B8478269 : Blo 1112627 8478269 := bstep (se 3 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 8478269 = 3179351) B3179351
theorem B32563063 : Blo 1112627 32563063 := bstep (se 1 (by rfl) ⟨24422297, by rfl⟩ : syracuseStep 32563063 = 48844595) B48844595
theorem B4514135 : Blo 1112627 4514135 := bstep (se 1 (by rfl) ⟨3385601, by rfl⟩ : syracuseStep 4514135 = 6771203) B6771203
theorem B8479241 : Blo 1112627 8479241 := bstep (se 2 (by rfl) ⟨3179715, by rfl⟩ : syracuseStep 8479241 = 6359431) B6359431
theorem B7332377 : Blo 1112627 7332377 := bstep (se 2 (by rfl) ⟨2749641, by rfl⟩ : syracuseStep 7332377 = 5499283) B5499283
theorem B2417249 : Blo 1112627 2417249 := bstep (se 2 (by rfl) ⟨906468, by rfl⟩ : syracuseStep 2417249 = 1812937) B1812937
theorem B3760775 : Blo 1112627 3760775 := bstep (se 1 (by rfl) ⟨2820581, by rfl⟩ : syracuseStep 3760775 = 5641163) B5641163
theorem B3760829 : Blo 1112627 3760829 := bstep (se 3 (by rfl) ⟨705155, by rfl⟩ : syracuseStep 3760829 = 1410311) B1410311
theorem B3760991 : Blo 1112627 3760991 := bstep (se 1 (by rfl) ⟨2820743, by rfl⟩ : syracuseStep 3760991 = 5641487) B5641487
theorem B11428715 : Blo 1112627 11428715 := bstep (se 1 (by rfl) ⟨8571536, by rfl⟩ : syracuseStep 11428715 = 17143073) B17143073
theorem B6349751 : Blo 1112627 6349751 := bstep (se 1 (by rfl) ⟨4762313, by rfl⟩ : syracuseStep 6349751 = 9524627) B9524627
theorem B3761153 : Blo 1112627 3761153 := bstep (se 2 (by rfl) ⟨1410432, by rfl⟩ : syracuseStep 3761153 = 2820865) B2820865
theorem B3564623 : Blo 1112627 3564623 := bstep (se 1 (by rfl) ⟨2673467, by rfl⟩ : syracuseStep 3564623 = 5346935) B5346935
theorem B3761963 : Blo 1112627 3761963 := bstep (se 1 (by rfl) ⟨2821472, by rfl⟩ : syracuseStep 3761963 = 5642945) B5642945
theorem B1337195 : Blo 1112627 1337195 := bstep (se 1 (by rfl) ⟨1002896, by rfl⟩ : syracuseStep 1337195 = 2005793) B2005793
theorem B3762233 : Blo 1112627 3762233 := bstep (se 2 (by rfl) ⟨1410837, by rfl⟩ : syracuseStep 3762233 = 2821675) B2821675
theorem B9529649 : Blo 1112627 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B6351209 : Blo 1112627 6351209 := bstep (se 2 (by rfl) ⟨2381703, by rfl⟩ : syracuseStep 6351209 = 4763407) B4763407
theorem B3762557 : Blo 1112627 3762557 := bstep (se 3 (by rfl) ⟨705479, by rfl⟩ : syracuseStep 3762557 = 1410959) B1410959
theorem B1272283 : Blo 1112627 1272283 := bstep (se 1 (by rfl) ⟨954212, by rfl⟩ : syracuseStep 1272283 = 1908425) B1908425
theorem B2681369 : Blo 1112627 2681369 := bstep (se 2 (by rfl) ⟨1005513, by rfl⟩ : syracuseStep 2681369 = 2011027) B2011027
theorem B3762827 : Blo 1112627 3762827 := bstep (se 1 (by rfl) ⟨2822120, by rfl⟩ : syracuseStep 3762827 = 5644241) B5644241
theorem B3173053 : Blo 1112627 3173053 := bstep (se 3 (by rfl) ⟨594947, by rfl⟩ : syracuseStep 3173053 = 1189895) B1189895
theorem B3566443 : Blo 1112627 3566443 := bstep (se 1 (by rfl) ⟨2674832, by rfl⟩ : syracuseStep 3566443 = 5349665) B5349665
theorem B3566519 : Blo 1112627 3566519 := bstep (se 1 (by rfl) ⟨2674889, by rfl⟩ : syracuseStep 3566519 = 5349779) B5349779
theorem B3763745 : Blo 1112627 3763745 := bstep (se 2 (by rfl) ⟨1411404, by rfl⟩ : syracuseStep 3763745 = 2822809) B2822809
theorem B7138961 : Blo 1112627 7138961 := bstep (se 2 (by rfl) ⟨2677110, by rfl⟩ : syracuseStep 7138961 = 5354221) B5354221
theorem B3010247 : Blo 1112627 3010247 := bstep (se 1 (by rfl) ⟨2257685, by rfl⟩ : syracuseStep 3010247 = 4515371) B4515371
theorem B14282477 : Blo 1112627 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B3763961 : Blo 1112627 3763961 := bstep (se 2 (by rfl) ⟨1411485, by rfl⟩ : syracuseStep 3763961 = 2822971) B2822971
theorem B3764231 : Blo 1112627 3764231 := bstep (se 1 (by rfl) ⟨2823173, by rfl⟩ : syracuseStep 3764231 = 5646347) B5646347
theorem B8581135 : Blo 1112627 8581135 := bstep (se 1 (by rfl) ⟨6435851, by rfl⟩ : syracuseStep 8581135 = 12871703) B12871703
theorem B3567635 : Blo 1112627 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B8024093 : Blo 1112627 8024093 := bstep (se 3 (by rfl) ⟨1504517, by rfl⟩ : syracuseStep 8024093 = 3009035) B3009035
theorem B3764339 : Blo 1112627 3764339 := bstep (se 1 (by rfl) ⟨2823254, by rfl⟩ : syracuseStep 3764339 = 5646509) B5646509
theorem B16085317 : Blo 1112627 16085317 := bstep (se 4 (by rfl) ⟨1507998, by rfl⟩ : syracuseStep 16085317 = 3015997) B3015997
theorem B3174785 : Blo 1112627 3174785 := bstep (se 2 (by rfl) ⟨1190544, by rfl⟩ : syracuseStep 3174785 = 2381089) B2381089
theorem B3764609 : Blo 1112627 3764609 := bstep (se 2 (by rfl) ⟨1411728, by rfl⟩ : syracuseStep 3764609 = 2823457) B2823457
theorem B6353417 : Blo 1112627 6353417 := bstep (se 2 (by rfl) ⟨2382531, by rfl⟩ : syracuseStep 6353417 = 4765063) B4765063
theorem B8155673 : Blo 1112627 8155673 := bstep (se 2 (by rfl) ⟨3058377, by rfl⟩ : syracuseStep 8155673 = 6116755) B6116755
theorem B3568313 : Blo 1112627 3568313 := bstep (se 2 (by rfl) ⟨1338117, by rfl⟩ : syracuseStep 3568313 = 2676235) B2676235
theorem B5436335 : Blo 1112627 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B11170817 : Blo 1112627 11170817 := bstep (se 2 (by rfl) ⟨4189056, by rfl⟩ : syracuseStep 11170817 = 8378113) B8378113
theorem B7140419 : Blo 1112627 7140419 := bstep (se 1 (by rfl) ⟨5355314, by rfl⟩ : syracuseStep 7140419 = 10710629) B10710629
theorem B3765419 : Blo 1112627 3765419 := bstep (se 1 (by rfl) ⟨2824064, by rfl⟩ : syracuseStep 3765419 = 5648129) B5648129
theorem B3569275 : Blo 1112627 3569275 := bstep (se 1 (by rfl) ⟨2676956, by rfl⟩ : syracuseStep 3569275 = 5353913) B5353913
theorem B3569287 : Blo 1112627 3569287 := bstep (se 1 (by rfl) ⟨2676965, by rfl⟩ : syracuseStep 3569287 = 5353931) B5353931
theorem B54195911 : Blo 1112627 54195911 := bstep (se 1 (by rfl) ⟨40646933, by rfl⟩ : syracuseStep 54195911 = 81293867) B81293867
theorem B3765959 : Blo 1112627 3765959 := bstep (se 1 (by rfl) ⟨2824469, by rfl⟩ : syracuseStep 3765959 = 5648939) B5648939
theorem B3176185 : Blo 1112627 3176185 := bstep (se 2 (by rfl) ⟨1191069, by rfl⟩ : syracuseStep 3176185 = 2382139) B2382139
theorem B1668959 : Blo 1112627 1668959 := bstep (se 1 (by rfl) ⟨1251719, by rfl⟩ : syracuseStep 1668959 = 2503439) B2503439
theorem B1668971 : Blo 1112627 1668971 := bstep (se 1 (by rfl) ⟨1251728, by rfl⟩ : syracuseStep 1668971 = 2503457) B2503457
theorem B8452025 : Blo 1112627 8452025 := bstep (se 2 (by rfl) ⟨3169509, by rfl⟩ : syracuseStep 8452025 = 6339019) B6339019
theorem B6354875 : Blo 1112627 6354875 := bstep (se 1 (by rfl) ⟨4766156, by rfl⟩ : syracuseStep 6354875 = 9532313) B9532313
theorem B1669199 : Blo 1112627 1669199 := bstep (se 1 (by rfl) ⟨1251899, by rfl⟩ : syracuseStep 1669199 = 2503799) B2503799
theorem B1669319 : Blo 1112627 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B18086125 : Blo 1112627 18086125 := bstep (se 3 (by rfl) ⟨3391148, by rfl⟩ : syracuseStep 18086125 = 6782297) B6782297
theorem B1669481 : Blo 1112627 1669481 := bstep (se 2 (by rfl) ⟨626055, by rfl⟩ : syracuseStep 1669481 = 1252111) B1252111
theorem B4225405 : Blo 1112627 4225405 := bstep (se 3 (by rfl) ⟨792263, by rfl⟩ : syracuseStep 4225405 = 1584527) B1584527
theorem B1669559 : Blo 1112627 1669559 := bstep (se 1 (by rfl) ⟨1252169, by rfl⟩ : syracuseStep 1669559 = 2504339) B2504339
theorem B1669595 : Blo 1112627 1669595 := bstep (se 1 (by rfl) ⟨1252196, by rfl⟩ : syracuseStep 1669595 = 2504393) B2504393
theorem B3766823 : Blo 1112627 3766823 := bstep (se 1 (by rfl) ⟨2825117, by rfl⟩ : syracuseStep 3766823 = 5650235) B5650235
theorem B1112655 : Blo 1112627 1112655 := bstep (se 1 (by rfl) ⟨834491, by rfl⟩ : syracuseStep 1112655 = 1668983) B1668983
theorem B1112671 : Blo 1112627 1112671 := bstep (se 1 (by rfl) ⟨834503, by rfl⟩ : syracuseStep 1112671 = 1669007) B1669007
theorem B1112699 : Blo 1112627 1112699 := bstep (se 1 (by rfl) ⟨834524, by rfl⟩ : syracuseStep 1112699 = 1669049) B1669049
theorem B3766931 : Blo 1112627 3766931 := bstep (se 1 (by rfl) ⟨2825198, by rfl⟩ : syracuseStep 3766931 = 5650397) B5650397
theorem B1112751 : Blo 1112627 1112751 := bstep (se 1 (by rfl) ⟨834563, by rfl⟩ : syracuseStep 1112751 = 1669127) B1669127
theorem B1112775 : Blo 1112627 1112775 := bstep (se 1 (by rfl) ⟨834581, by rfl⟩ : syracuseStep 1112775 = 1669163) B1669163
theorem B1112795 : Blo 1112627 1112795 := bstep (se 1 (by rfl) ⟨834596, by rfl⟩ : syracuseStep 1112795 = 1669193) B1669193
theorem B5634845 : Blo 1112627 5634845 := bstep (se 3 (by rfl) ⟨1056533, by rfl⟩ : syracuseStep 5634845 = 2113067) B2113067
theorem B1112871 : Blo 1112627 1112871 := bstep (se 1 (by rfl) ⟨834653, by rfl⟩ : syracuseStep 1112871 = 1669307) B1669307
theorem B1112911 : Blo 1112627 1112911 := bstep (se 1 (by rfl) ⟨834683, by rfl⟩ : syracuseStep 1112911 = 1669367) B1669367
theorem B1112927 : Blo 1112627 1112927 := bstep (se 1 (by rfl) ⟨834695, by rfl⟩ : syracuseStep 1112927 = 1669391) B1669391
theorem B3767147 : Blo 1112627 3767147 := bstep (se 1 (by rfl) ⟨2825360, by rfl⟩ : syracuseStep 3767147 = 5650721) B5650721
theorem B1112955 : Blo 1112627 1112955 := bstep (se 1 (by rfl) ⟨834716, by rfl⟩ : syracuseStep 1112955 = 1669433) B1669433
theorem B3767201 : Blo 1112627 3767201 := bstep (se 2 (by rfl) ⟨1412700, by rfl⟩ : syracuseStep 3767201 = 2825401) B2825401
theorem B1113007 : Blo 1112627 1113007 := bstep (se 1 (by rfl) ⟨834755, by rfl⟩ : syracuseStep 1113007 = 1669511) B1669511
theorem B1670063 : Blo 1112627 1670063 := bstep (se 1 (by rfl) ⟨1252547, by rfl⟩ : syracuseStep 1670063 = 2505095) B2505095
theorem B1113031 : Blo 1112627 1113031 := bstep (se 1 (by rfl) ⟨834773, by rfl⟩ : syracuseStep 1113031 = 1669547) B1669547
theorem B1113051 : Blo 1112627 1113051 := bstep (se 1 (by rfl) ⟨834788, by rfl⟩ : syracuseStep 1113051 = 1669577) B1669577
theorem B1670153 : Blo 1112627 1670153 := bstep (se 2 (by rfl) ⟨626307, by rfl⟩ : syracuseStep 1670153 = 1252615) B1252615
theorem B1113127 : Blo 1112627 1113127 := bstep (se 1 (by rfl) ⟨834845, by rfl⟩ : syracuseStep 1113127 = 1669691) B1669691
theorem B1670183 : Blo 1112627 1670183 := bstep (se 1 (by rfl) ⟨1252637, by rfl⟩ : syracuseStep 1670183 = 2505275) B2505275
theorem B1113167 : Blo 1112627 1113167 := bstep (se 1 (by rfl) ⟨834875, by rfl⟩ : syracuseStep 1113167 = 1669751) B1669751
theorem B1113183 : Blo 1112627 1113183 := bstep (se 1 (by rfl) ⟨834887, by rfl⟩ : syracuseStep 1113183 = 1669775) B1669775
theorem B1113211 : Blo 1112627 1113211 := bstep (se 1 (by rfl) ⟨834908, by rfl⟩ : syracuseStep 1113211 = 1669817) B1669817
theorem B1670267 : Blo 1112627 1670267 := bstep (se 1 (by rfl) ⟨1252700, by rfl⟩ : syracuseStep 1670267 = 2505401) B2505401
theorem B3177643 : Blo 1112627 3177643 := bstep (se 1 (by rfl) ⟨2383232, by rfl⟩ : syracuseStep 3177643 = 4766465) B4766465
theorem B1113263 : Blo 1112627 1113263 := bstep (se 1 (by rfl) ⟨834947, by rfl⟩ : syracuseStep 1113263 = 1669895) B1669895
theorem B1113287 : Blo 1112627 1113287 := bstep (se 1 (by rfl) ⟨834965, by rfl⟩ : syracuseStep 1113287 = 1669931) B1669931
theorem B1113307 : Blo 1112627 1113307 := bstep (se 1 (by rfl) ⟨834980, by rfl⟩ : syracuseStep 1113307 = 1669961) B1669961
theorem B1670393 : Blo 1112627 1670393 := bstep (se 2 (by rfl) ⟨626397, by rfl⟩ : syracuseStep 1670393 = 1252795) B1252795
theorem B1113383 : Blo 1112627 1113383 := bstep (se 1 (by rfl) ⟨835037, by rfl⟩ : syracuseStep 1113383 = 1670075) B1670075
theorem B1113423 : Blo 1112627 1113423 := bstep (se 1 (by rfl) ⟨835067, by rfl⟩ : syracuseStep 1113423 = 1670135) B1670135
theorem B1113439 : Blo 1112627 1113439 := bstep (se 1 (by rfl) ⟨835079, by rfl⟩ : syracuseStep 1113439 = 1670159) B1670159
theorem B1670495 : Blo 1112627 1670495 := bstep (se 1 (by rfl) ⟨1252871, by rfl⟩ : syracuseStep 1670495 = 2505743) B2505743
theorem B1670507 : Blo 1112627 1670507 := bstep (se 1 (by rfl) ⟨1252880, by rfl⟩ : syracuseStep 1670507 = 2505761) B2505761
theorem B1113467 : Blo 1112627 1113467 := bstep (se 1 (by rfl) ⟨835100, by rfl⟩ : syracuseStep 1113467 = 1670201) B1670201
theorem B1113519 : Blo 1112627 1113519 := bstep (se 1 (by rfl) ⟨835139, by rfl⟩ : syracuseStep 1113519 = 1670279) B1670279
theorem B1113543 : Blo 1112627 1113543 := bstep (se 1 (by rfl) ⟨835157, by rfl⟩ : syracuseStep 1113543 = 1670315) B1670315
theorem B1113563 : Blo 1112627 1113563 := bstep (se 1 (by rfl) ⟨835172, by rfl⟩ : syracuseStep 1113563 = 1670345) B1670345
theorem B3767795 : Blo 1112627 3767795 := bstep (se 1 (by rfl) ⟨2825846, by rfl⟩ : syracuseStep 3767795 = 5651693) B5651693
theorem B2817575 : Blo 1112627 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B1113639 : Blo 1112627 1113639 := bstep (se 1 (by rfl) ⟨835229, by rfl⟩ : syracuseStep 1113639 = 1670459) B1670459
theorem B1113679 : Blo 1112627 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B1670735 : Blo 1112627 1670735 := bstep (se 1 (by rfl) ⟨1253051, by rfl⟩ : syracuseStep 1670735 = 2506103) B2506103
theorem B1113695 : Blo 1112627 1113695 := bstep (se 1 (by rfl) ⟨835271, by rfl⟩ : syracuseStep 1113695 = 1670543) B1670543
theorem B1113723 : Blo 1112627 1113723 := bstep (se 1 (by rfl) ⟨835292, by rfl⟩ : syracuseStep 1113723 = 1670585) B1670585
theorem B3014267 : Blo 1112627 3014267 := bstep (se 1 (by rfl) ⟨2260700, by rfl⟩ : syracuseStep 3014267 = 4521401) B4521401
theorem B1113775 : Blo 1112627 1113775 := bstep (se 1 (by rfl) ⟨835331, by rfl⟩ : syracuseStep 1113775 = 1670663) B1670663
theorem B1113799 : Blo 1112627 1113799 := bstep (se 1 (by rfl) ⟨835349, by rfl⟩ : syracuseStep 1113799 = 1670699) B1670699
theorem B1670855 : Blo 1112627 1670855 := bstep (se 1 (by rfl) ⟨1253141, by rfl⟩ : syracuseStep 1670855 = 2506283) B2506283
theorem B1113819 : Blo 1112627 1113819 := bstep (se 1 (by rfl) ⟨835364, by rfl⟩ : syracuseStep 1113819 = 1670729) B1670729
theorem B1113895 : Blo 1112627 1113895 := bstep (se 1 (by rfl) ⟨835421, by rfl⟩ : syracuseStep 1113895 = 1670843) B1670843
theorem B6029099 : Blo 1112627 6029099 := bstep (se 1 (by rfl) ⟨4521824, by rfl⟩ : syracuseStep 6029099 = 9043649) B9043649
theorem B1113935 : Blo 1112627 1113935 := bstep (se 1 (by rfl) ⟨835451, by rfl⟩ : syracuseStep 1113935 = 1670903) B1670903
theorem B1113951 : Blo 1112627 1113951 := bstep (se 1 (by rfl) ⟨835463, by rfl⟩ : syracuseStep 1113951 = 1670927) B1670927
theorem B1671017 : Blo 1112627 1671017 := bstep (se 2 (by rfl) ⟨626631, by rfl⟩ : syracuseStep 1671017 = 1253263) B1253263
theorem B2817899 : Blo 1112627 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B1113979 : Blo 1112627 1113979 := bstep (se 1 (by rfl) ⟨835484, by rfl⟩ : syracuseStep 1113979 = 1670969) B1670969
theorem B1114031 : Blo 1112627 1114031 := bstep (se 1 (by rfl) ⟨835523, by rfl⟩ : syracuseStep 1114031 = 1671047) B1671047
theorem B1671095 : Blo 1112627 1671095 := bstep (se 1 (by rfl) ⟨1253321, by rfl⟩ : syracuseStep 1671095 = 2506643) B2506643
theorem B1114055 : Blo 1112627 1114055 := bstep (se 1 (by rfl) ⟨835541, by rfl⟩ : syracuseStep 1114055 = 1671083) B1671083
theorem B1114075 : Blo 1112627 1114075 := bstep (se 1 (by rfl) ⟨835556, by rfl⟩ : syracuseStep 1114075 = 1671113) B1671113
theorem B1671131 : Blo 1112627 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B1114399 : Blo 1112627 1114399 := bstep (se 1 (by rfl) ⟨835799, by rfl⟩ : syracuseStep 1114399 = 1671599) B1671599
theorem B1671515 : Blo 1112627 1671515 := bstep (se 1 (by rfl) ⟨1253636, by rfl⟩ : syracuseStep 1671515 = 2507273) B2507273
theorem B1114459 : Blo 1112627 1114459 := bstep (se 1 (by rfl) ⟨835844, by rfl⟩ : syracuseStep 1114459 = 1671689) B1671689
theorem B2818415 : Blo 1112627 2818415 := bstep (se 1 (by rfl) ⟨2113811, by rfl⟩ : syracuseStep 2818415 = 4227623) B4227623
theorem B1114479 : Blo 1112627 1114479 := bstep (se 1 (by rfl) ⟨835859, by rfl⟩ : syracuseStep 1114479 = 1671719) B1671719
theorem B1114535 : Blo 1112627 1114535 := bstep (se 1 (by rfl) ⟨835901, by rfl⟩ : syracuseStep 1114535 = 1671803) B1671803
theorem B1507783 : Blo 1112627 1507783 := bstep (se 1 (by rfl) ⟨1130837, by rfl⟩ : syracuseStep 1507783 = 2261675) B2261675
theorem B6357473 : Blo 1112627 6357473 := bstep (se 2 (by rfl) ⟨2384052, by rfl⟩ : syracuseStep 6357473 = 4768105) B4768105
theorem B1114619 : Blo 1112627 1114619 := bstep (se 1 (by rfl) ⟨835964, by rfl⟩ : syracuseStep 1114619 = 1671929) B1671929
theorem B5636627 : Blo 1112627 5636627 := bstep (se 1 (by rfl) ⟨4227470, by rfl⟩ : syracuseStep 5636627 = 8454941) B8454941
theorem B1671743 : Blo 1112627 1671743 := bstep (se 1 (by rfl) ⟨1253807, by rfl⟩ : syracuseStep 1671743 = 2507615) B2507615
theorem B1114687 : Blo 1112627 1114687 := bstep (se 1 (by rfl) ⟨836015, by rfl⟩ : syracuseStep 1114687 = 1672031) B1672031
theorem B1114695 : Blo 1112627 1114695 := bstep (se 1 (by rfl) ⟨836021, by rfl⟩ : syracuseStep 1114695 = 1672043) B1672043
theorem B6783659 : Blo 1112627 6783659 := bstep (se 1 (by rfl) ⟨5087744, by rfl⟩ : syracuseStep 6783659 = 10175489) B10175489
theorem B1409719 : Blo 1112627 1409719 := bstep (se 1 (by rfl) ⟨1057289, by rfl⟩ : syracuseStep 1409719 = 2114579) B2114579
theorem B1671863 : Blo 1112627 1671863 := bstep (se 1 (by rfl) ⟨1253897, by rfl⟩ : syracuseStep 1671863 = 2507795) B2507795
theorem B1114847 : Blo 1112627 1114847 := bstep (se 1 (by rfl) ⟨836135, by rfl⟩ : syracuseStep 1114847 = 1672271) B1672271
theorem B1114927 : Blo 1112627 1114927 := bstep (se 1 (by rfl) ⟨836195, by rfl⟩ : syracuseStep 1114927 = 1672391) B1672391
theorem B1672091 : Blo 1112627 1672091 := bstep (se 1 (by rfl) ⟨1254068, by rfl⟩ : syracuseStep 1672091 = 2508137) B2508137
theorem B1115035 : Blo 1112627 1115035 := bstep (se 1 (by rfl) ⟨836276, by rfl⟩ : syracuseStep 1115035 = 1672553) B1672553
theorem B1115087 : Blo 1112627 1115087 := bstep (se 1 (by rfl) ⟨836315, by rfl⟩ : syracuseStep 1115087 = 1672631) B1672631
theorem B1115111 : Blo 1112627 1115111 := bstep (se 1 (by rfl) ⟨836333, by rfl⟩ : syracuseStep 1115111 = 1672667) B1672667
theorem B2819063 : Blo 1112627 2819063 := bstep (se 1 (by rfl) ⟨2114297, by rfl⟩ : syracuseStep 2819063 = 4228595) B4228595
theorem B2819195 : Blo 1112627 2819195 := bstep (se 1 (by rfl) ⟨2114396, by rfl⟩ : syracuseStep 2819195 = 4228793) B4228793
theorem B1115423 : Blo 1112627 1115423 := bstep (se 1 (by rfl) ⟨836567, by rfl⟩ : syracuseStep 1115423 = 1673135) B1673135
theorem B1672487 : Blo 1112627 1672487 := bstep (se 1 (by rfl) ⟨1254365, by rfl⟩ : syracuseStep 1672487 = 2508731) B2508731
theorem B1115483 : Blo 1112627 1115483 := bstep (se 1 (by rfl) ⟨836612, by rfl⟩ : syracuseStep 1115483 = 1673225) B1673225
theorem B1115503 : Blo 1112627 1115503 := bstep (se 1 (by rfl) ⟨836627, by rfl⟩ : syracuseStep 1115503 = 1673255) B1673255
theorem B1672571 : Blo 1112627 1672571 := bstep (se 1 (by rfl) ⟨1254428, by rfl⟩ : syracuseStep 1672571 = 2508857) B2508857
theorem B3016075 : Blo 1112627 3016075 := bstep (se 1 (by rfl) ⟨2262056, by rfl⟩ : syracuseStep 3016075 = 4524113) B4524113
theorem B1115559 : Blo 1112627 1115559 := bstep (se 1 (by rfl) ⟨836669, by rfl⟩ : syracuseStep 1115559 = 1673339) B1673339
theorem B1672697 : Blo 1112627 1672697 := bstep (se 2 (by rfl) ⟨627261, by rfl⟩ : syracuseStep 1672697 = 1254523) B1254523
theorem B1115643 : Blo 1112627 1115643 := bstep (se 1 (by rfl) ⟨836732, by rfl⟩ : syracuseStep 1115643 = 1673465) B1673465
theorem B1115711 : Blo 1112627 1115711 := bstep (se 1 (by rfl) ⟨836783, by rfl⟩ : syracuseStep 1115711 = 1673567) B1673567
theorem B1115719 : Blo 1112627 1115719 := bstep (se 1 (by rfl) ⟨836789, by rfl⟩ : syracuseStep 1115719 = 1673579) B1673579
theorem B1672799 : Blo 1112627 1672799 := bstep (se 1 (by rfl) ⟨1254599, by rfl⟩ : syracuseStep 1672799 = 2509199) B2509199
theorem B1115871 : Blo 1112627 1115871 := bstep (se 1 (by rfl) ⟨836903, by rfl⟩ : syracuseStep 1115871 = 1673807) B1673807
theorem B1115951 : Blo 1112627 1115951 := bstep (se 1 (by rfl) ⟨836963, by rfl⟩ : syracuseStep 1115951 = 1673927) B1673927
theorem B1673015 : Blo 1112627 1673015 := bstep (se 1 (by rfl) ⟨1254761, by rfl⟩ : syracuseStep 1673015 = 2509523) B2509523
theorem B12683141 : Blo 1112627 12683141 := bstep (se 4 (by rfl) ⟨1189044, by rfl⟩ : syracuseStep 12683141 = 2378089) B2378089
theorem B1116059 : Blo 1112627 1116059 := bstep (se 1 (by rfl) ⟨837044, by rfl⟩ : syracuseStep 1116059 = 1674089) B1674089
theorem B1116111 : Blo 1112627 1116111 := bstep (se 1 (by rfl) ⟨837083, by rfl⟩ : syracuseStep 1116111 = 1674167) B1674167
theorem B1116135 : Blo 1112627 1116135 := bstep (se 1 (by rfl) ⟨837101, by rfl⟩ : syracuseStep 1116135 = 1674203) B1674203
theorem B216827927 : Blo 1112627 216827927 := bstep (se 1 (by rfl) ⟨162620945, by rfl⟩ : syracuseStep 216827927 = 325241891) B325241891
theorem B1673321 : Blo 1112627 1673321 := bstep (se 2 (by rfl) ⟨627495, by rfl⟩ : syracuseStep 1673321 = 1254991) B1254991
theorem B45746369 : Blo 1112627 45746369 := bstep (se 2 (by rfl) ⟨17154888, by rfl⟩ : syracuseStep 45746369 = 34309777) B34309777
theorem B6424771 : Blo 1112627 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B5638409 : Blo 1112627 5638409 := bstep (se 2 (by rfl) ⟨2114403, by rfl⟩ : syracuseStep 5638409 = 4228807) B4228807
theorem B1116447 : Blo 1112627 1116447 := bstep (se 1 (by rfl) ⟨837335, by rfl⟩ : syracuseStep 1116447 = 1674671) B1674671
theorem B1116507 : Blo 1112627 1116507 := bstep (se 1 (by rfl) ⟨837380, by rfl⟩ : syracuseStep 1116507 = 1674761) B1674761
theorem B1116527 : Blo 1112627 1116527 := bstep (se 1 (by rfl) ⟨837395, by rfl⟩ : syracuseStep 1116527 = 1674791) B1674791
theorem B1673639 : Blo 1112627 1673639 := bstep (se 1 (by rfl) ⟨1255229, by rfl⟩ : syracuseStep 1673639 = 2510459) B2510459
theorem B1116583 : Blo 1112627 1116583 := bstep (se 1 (by rfl) ⟨837437, by rfl⟩ : syracuseStep 1116583 = 1674875) B1674875
theorem B21400037 : Blo 1112627 21400037 := bstep (se 4 (by rfl) ⟨2006253, by rfl⟩ : syracuseStep 21400037 = 4012507) B4012507
theorem B6031867 : Blo 1112627 6031867 := bstep (se 1 (by rfl) ⟨4523900, by rfl⟩ : syracuseStep 6031867 = 9047801) B9047801
theorem B1673723 : Blo 1112627 1673723 := bstep (se 1 (by rfl) ⟨1255292, by rfl⟩ : syracuseStep 1673723 = 2510585) B2510585
theorem B32115275 : Blo 1112627 32115275 := bstep (se 1 (by rfl) ⟨24086456, by rfl⟩ : syracuseStep 32115275 = 48172913) B48172913
theorem B1673849 : Blo 1112627 1673849 := bstep (se 2 (by rfl) ⟨627693, by rfl⟩ : syracuseStep 1673849 = 1255387) B1255387
theorem B1411759 : Blo 1112627 1411759 := bstep (se 1 (by rfl) ⟨1058819, by rfl⟩ : syracuseStep 1411759 = 2117639) B2117639
theorem B1673903 : Blo 1112627 1673903 := bstep (se 1 (by rfl) ⟨1255427, by rfl⟩ : syracuseStep 1673903 = 2510855) B2510855
theorem B1673951 : Blo 1112627 1673951 := bstep (se 1 (by rfl) ⟨1255463, by rfl⟩ : syracuseStep 1673951 = 2510927) B2510927
theorem B2821007 : Blo 1112627 2821007 := bstep (se 1 (by rfl) ⟨2115755, by rfl⟩ : syracuseStep 2821007 = 4231511) B4231511
theorem B1674215 : Blo 1112627 1674215 := bstep (se 1 (by rfl) ⟨1255661, by rfl⟩ : syracuseStep 1674215 = 2511323) B2511323
theorem B1674473 : Blo 1112627 1674473 := bstep (se 2 (by rfl) ⟨627927, by rfl⟩ : syracuseStep 1674473 = 1255855) B1255855
theorem B1674527 : Blo 1112627 1674527 := bstep (se 1 (by rfl) ⟨1255895, by rfl⟩ : syracuseStep 1674527 = 2511791) B2511791
theorem B5639543 : Blo 1112627 5639543 := bstep (se 1 (by rfl) ⟨4229657, by rfl⟩ : syracuseStep 5639543 = 8459315) B8459315
theorem B2821513 : Blo 1112627 2821513 := bstep (se 2 (by rfl) ⟨1058067, by rfl⟩ : syracuseStep 2821513 = 2116135) B2116135
theorem B1674695 : Blo 1112627 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B2821625 : Blo 1112627 2821625 := bstep (se 2 (by rfl) ⟨1058109, by rfl⟩ : syracuseStep 2821625 = 2116219) B2116219
theorem B5639705 : Blo 1112627 5639705 := bstep (se 2 (by rfl) ⟨2114889, by rfl⟩ : syracuseStep 5639705 = 4229779) B4229779
theorem B4230737 : Blo 1112627 4230737 := bstep (se 2 (by rfl) ⟨1586526, by rfl⟩ : syracuseStep 4230737 = 3173053) B3173053
theorem B4230751 : Blo 1112627 4230751 := bstep (se 1 (by rfl) ⟨3173063, by rfl⟩ : syracuseStep 4230751 = 6346127) B6346127
theorem B4755257 : Blo 1112627 4755257 := bstep (se 2 (by rfl) ⟨1783221, by rfl⟩ : syracuseStep 4755257 = 3566443) B3566443
theorem B2822273 : Blo 1112627 2822273 := bstep (se 2 (by rfl) ⟨1058352, by rfl⟩ : syracuseStep 2822273 = 2116705) B2116705
theorem B3576155 : Blo 1112627 3576155 := bstep (se 1 (by rfl) ⟨2682116, by rfl⟩ : syracuseStep 3576155 = 5364233) B5364233
theorem B2036287 : Blo 1112627 2036287 := bstep (se 1 (by rfl) ⟨1527215, by rfl⟩ : syracuseStep 2036287 = 3054431) B3054431
theorem B2823083 : Blo 1112627 2823083 := bstep (se 1 (by rfl) ⟨2117312, by rfl⟩ : syracuseStep 2823083 = 4234625) B4234625
theorem B48272557 : Blo 1112627 48272557 := bstep (se 3 (by rfl) ⟨9051104, by rfl⟩ : syracuseStep 48272557 = 18102209) B18102209
theorem B11441513 : Blo 1112627 11441513 := bstep (se 2 (by rfl) ⟨4290567, by rfl⟩ : syracuseStep 11441513 = 8581135) B8581135
theorem B6034981 : Blo 1112627 6034981 := bstep (se 4 (by rfl) ⟨565779, by rfl⟩ : syracuseStep 6034981 = 1131559) B1131559
theorem B1611499 : Blo 1112627 1611499 := bstep (se 1 (by rfl) ⟨1208624, by rfl⟩ : syracuseStep 1611499 = 2417249) B2417249
theorem B2823943 : Blo 1112627 2823943 := bstep (se 1 (by rfl) ⟨2117957, by rfl⟩ : syracuseStep 2823943 = 4235915) B4235915
theorem B6788893 : Blo 1112627 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B4233167 : Blo 1112627 4233167 := bstep (se 1 (by rfl) ⟨3174875, by rfl⟩ : syracuseStep 4233167 = 6349751) B6349751
theorem B2824217 : Blo 1112627 2824217 := bstep (se 2 (by rfl) ⟨1059081, by rfl⟩ : syracuseStep 2824217 = 2118163) B2118163
theorem B5642621 : Blo 1112627 5642621 := bstep (se 3 (by rfl) ⟨1057991, by rfl⟩ : syracuseStep 5642621 = 2115983) B2115983
theorem B1251751 : Blo 1112627 1251751 := bstep (se 1 (by rfl) ⟨938813, by rfl⟩ : syracuseStep 1251751 = 1877627) B1877627
theorem B4234139 : Blo 1112627 4234139 := bstep (se 1 (by rfl) ⟨3175604, by rfl⟩ : syracuseStep 4234139 = 6351209) B6351209
theorem B1252327 : Blo 1112627 1252327 := bstep (se 1 (by rfl) ⟨939245, by rfl⟩ : syracuseStep 1252327 = 1878491) B1878491
theorem B14261669 : Blo 1112627 14261669 := bstep (se 4 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 14261669 = 2674063) B2674063
theorem B4759033 : Blo 1112627 4759033 := bstep (se 2 (by rfl) ⟨1784637, by rfl⟩ : syracuseStep 4759033 = 3569275) B3569275
theorem B4759049 : Blo 1112627 4759049 := bstep (se 2 (by rfl) ⟨1784643, by rfl⟩ : syracuseStep 4759049 = 3569287) B3569287
theorem B4234913 : Blo 1112627 4234913 := bstep (se 2 (by rfl) ⟨1588092, by rfl⟩ : syracuseStep 4234913 = 3176185) B3176185
theorem B4759307 : Blo 1112627 4759307 := bstep (se 1 (by rfl) ⟨3569480, by rfl⟩ : syracuseStep 4759307 = 7138961) B7138961
theorem B2006831 : Blo 1112627 2006831 := bstep (se 1 (by rfl) ⟨1505123, by rfl⟩ : syracuseStep 2006831 = 3010247) B3010247
theorem B5644079 : Blo 1112627 5644079 := bstep (se 1 (by rfl) ⟨4233059, by rfl⟩ : syracuseStep 5644079 = 8466119) B8466119
theorem B4759357 : Blo 1112627 4759357 := bstep (se 3 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 4759357 = 1784759) B1784759
theorem B40607669 : Blo 1112627 40607669 := bstep (se 5 (by rfl) ⟨1903484, by rfl⟩ : syracuseStep 40607669 = 3806969) B3806969
theorem B2826191 : Blo 1112627 2826191 := bstep (se 1 (by rfl) ⟨2119643, by rfl⟩ : syracuseStep 2826191 = 4239287) B4239287
theorem B5349395 : Blo 1112627 5349395 := bstep (se 1 (by rfl) ⟨4012046, by rfl⟩ : syracuseStep 5349395 = 8024093) B8024093
theorem B4235611 : Blo 1112627 4235611 := bstep (se 1 (by rfl) ⟨3176708, by rfl⟩ : syracuseStep 4235611 = 6353417) B6353417
theorem B1253983 : Blo 1112627 1253983 := bstep (se 1 (by rfl) ⟨940487, by rfl⟩ : syracuseStep 1253983 = 1880975) B1880975
theorem B7447211 : Blo 1112627 7447211 := bstep (se 1 (by rfl) ⟨5585408, by rfl⟩ : syracuseStep 7447211 = 11170817) B11170817
theorem B4760279 : Blo 1112627 4760279 := bstep (se 1 (by rfl) ⟨3570209, by rfl⟩ : syracuseStep 4760279 = 7140419) B7140419
theorem B4236583 : Blo 1112627 4236583 := bstep (se 1 (by rfl) ⟨3177437, by rfl⟩ : syracuseStep 4236583 = 6354875) B6354875
theorem B4236857 : Blo 1112627 4236857 := bstep (se 2 (by rfl) ⟨1588821, by rfl⟩ : syracuseStep 4236857 = 3177643) B3177643
theorem B8038045 : Blo 1112627 8038045 := bstep (se 3 (by rfl) ⟨1507133, by rfl⟩ : syracuseStep 8038045 = 3014267) B3014267
theorem B1255135 : Blo 1112627 1255135 := bstep (se 1 (by rfl) ⟨941351, by rfl⟩ : syracuseStep 1255135 = 1882703) B1882703
theorem B1189711 : Blo 1112627 1189711 := bstep (se 1 (by rfl) ⟨892283, by rfl⟩ : syracuseStep 1189711 = 1784567) B1784567
theorem B4073303 : Blo 1112627 4073303 := bstep (se 1 (by rfl) ⟨3054977, by rfl⟩ : syracuseStep 4073303 = 6109955) B6109955
theorem B5646185 : Blo 1112627 5646185 := bstep (se 2 (by rfl) ⟨2117319, by rfl⟩ : syracuseStep 5646185 = 4234639) B4234639
theorem B27142037 : Blo 1112627 27142037 := bstep (se 6 (by rfl) ⟨636141, by rfl⟩ : syracuseStep 27142037 = 1272283) B1272283
theorem B1255711 : Blo 1112627 1255711 := bstep (se 1 (by rfl) ⟨941783, by rfl⟩ : syracuseStep 1255711 = 1883567) B1883567
theorem B1878383 : Blo 1112627 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B1255999 : Blo 1112627 1255999 := bstep (se 1 (by rfl) ⟨941999, by rfl⟩ : syracuseStep 1255999 = 1883999) B1883999
theorem B1878599 : Blo 1112627 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B11447261 : Blo 1112627 11447261 := bstep (se 3 (by rfl) ⟨2146361, by rfl⟩ : syracuseStep 11447261 = 4292723) B4292723
theorem B1879031 : Blo 1112627 1879031 := bstep (se 1 (by rfl) ⟨1409273, by rfl⟩ : syracuseStep 1879031 = 2818547) B2818547
theorem B4762739 : Blo 1112627 4762739 := bstep (se 1 (by rfl) ⟨3572054, by rfl⟩ : syracuseStep 4762739 = 7144109) B7144109
theorem B12037693 : Blo 1112627 12037693 := bstep (se 3 (by rfl) ⟨2257067, by rfl⟩ : syracuseStep 12037693 = 4514135) B4514135
theorem B5647967 : Blo 1112627 5647967 := bstep (se 1 (by rfl) ⟨4235975, by rfl⟩ : syracuseStep 5647967 = 8471951) B8471951
theorem B1879787 : Blo 1112627 1879787 := bstep (se 1 (by rfl) ⟨1409840, by rfl⟩ : syracuseStep 1879787 = 2819681) B2819681
theorem B2141959 : Blo 1112627 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B1584937 : Blo 1112627 1584937 := bstep (se 2 (by rfl) ⟨594351, by rfl⟩ : syracuseStep 1584937 = 1188703) B1188703
theorem B2011559 : Blo 1112627 2011559 := bstep (se 1 (by rfl) ⟨1508669, by rfl⟩ : syracuseStep 2011559 = 3017339) B3017339
theorem B9515501 : Blo 1112627 9515501 := bstep (se 3 (by rfl) ⟨1784156, by rfl⟩ : syracuseStep 9515501 = 3568313) B3568313
theorem B14299699 : Blo 1112627 14299699 := bstep (se 1 (by rfl) ⟨10724774, by rfl⟩ : syracuseStep 14299699 = 21449549) B21449549
theorem B1880759 : Blo 1112627 1880759 := bstep (se 1 (by rfl) ⟨1410569, by rfl⟩ : syracuseStep 1880759 = 2821139) B2821139
theorem B4010719 : Blo 1112627 4010719 := bstep (se 1 (by rfl) ⟨3008039, by rfl⟩ : syracuseStep 4010719 = 6016079) B6016079
theorem B2503655 : Blo 1112627 2503655 := bstep (se 1 (by rfl) ⟨1877741, by rfl⟩ : syracuseStep 2503655 = 3755483) B3755483
theorem B14496893 : Blo 1112627 14496893 := bstep (se 3 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 14496893 = 5436335) B5436335
theorem B1586395 : Blo 1112627 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B12039425 : Blo 1112627 12039425 := bstep (se 2 (by rfl) ⟨4514784, by rfl⟩ : syracuseStep 12039425 = 9029569) B9029569
theorem B2504033 : Blo 1112627 2504033 := bstep (se 2 (by rfl) ⟨939012, by rfl⟩ : syracuseStep 2504033 = 1878025) B1878025
theorem B1881481 : Blo 1112627 1881481 := bstep (se 2 (by rfl) ⟨705555, by rfl⟩ : syracuseStep 1881481 = 1411111) B1411111
theorem B2504123 : Blo 1112627 2504123 := bstep (se 1 (by rfl) ⟨1878092, by rfl⟩ : syracuseStep 2504123 = 3756185) B3756185
theorem B2504249 : Blo 1112627 2504249 := bstep (se 2 (by rfl) ⟨939093, by rfl⟩ : syracuseStep 2504249 = 1878187) B1878187
theorem B1127999 : Blo 1112627 1127999 := bstep (se 1 (by rfl) ⟨845999, by rfl⟩ : syracuseStep 1127999 = 1691999) B1691999
theorem B5355143 : Blo 1112627 5355143 := bstep (se 1 (by rfl) ⟨4016357, by rfl⟩ : syracuseStep 5355143 = 8032715) B8032715
theorem B1586999 : Blo 1112627 1586999 := bstep (se 1 (by rfl) ⟨1190249, by rfl⟩ : syracuseStep 1586999 = 2380499) B2380499
theorem B1881913 : Blo 1112627 1881913 := bstep (se 2 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 1881913 = 1411435) B1411435
theorem B8697935 : Blo 1112627 8697935 := bstep (se 1 (by rfl) ⟨6523451, by rfl⟩ : syracuseStep 8697935 = 13046903) B13046903
theorem B1882217 : Blo 1112627 1882217 := bstep (se 2 (by rfl) ⟨705831, by rfl⟩ : syracuseStep 1882217 = 1411663) B1411663
theorem B20363399 : Blo 1112627 20363399 := bstep (se 1 (by rfl) ⟨15272549, by rfl⟩ : syracuseStep 20363399 = 30545099) B30545099
theorem B2504915 : Blo 1112627 2504915 := bstep (se 1 (by rfl) ⟨1878686, by rfl⟩ : syracuseStep 2504915 = 3757373) B3757373
theorem B2504969 : Blo 1112627 2504969 := bstep (se 2 (by rfl) ⟨939363, by rfl⟩ : syracuseStep 2504969 = 1878727) B1878727
theorem B2505185 : Blo 1112627 2505185 := bstep (se 2 (by rfl) ⟨939444, by rfl⟩ : syracuseStep 2505185 = 1878889) B1878889
theorem B13548055 : Blo 1112627 13548055 := bstep (se 1 (by rfl) ⟨10161041, by rfl⟩ : syracuseStep 13548055 = 20322083) B20322083
theorem B12040811 : Blo 1112627 12040811 := bstep (se 1 (by rfl) ⟨9030608, by rfl⟩ : syracuseStep 12040811 = 18061217) B18061217
theorem B2505491 : Blo 1112627 2505491 := bstep (se 1 (by rfl) ⟨1879118, by rfl⟩ : syracuseStep 2505491 = 3758237) B3758237
theorem B2505851 : Blo 1112627 2505851 := bstep (se 1 (by rfl) ⟨1879388, by rfl⟩ : syracuseStep 2505851 = 3758777) B3758777
theorem B1588457 : Blo 1112627 1588457 := bstep (se 2 (by rfl) ⟨595671, by rfl⟩ : syracuseStep 1588457 = 1191343) B1191343
theorem B2505977 : Blo 1112627 2505977 := bstep (se 2 (by rfl) ⟨939741, by rfl⟩ : syracuseStep 2505977 = 1879483) B1879483
theorem B6339977 : Blo 1112627 6339977 := bstep (se 2 (by rfl) ⟨2377491, by rfl⟩ : syracuseStep 6339977 = 4754983) B4754983
theorem B2506121 : Blo 1112627 2506121 := bstep (se 2 (by rfl) ⟨939795, by rfl⟩ : syracuseStep 2506121 = 1879591) B1879591
theorem B4767113 : Blo 1112627 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B1883641 : Blo 1112627 1883641 := bstep (se 2 (by rfl) ⟨706365, by rfl⟩ : syracuseStep 1883641 = 1412731) B1412731
theorem B2506247 : Blo 1112627 2506247 := bstep (se 1 (by rfl) ⟨1879685, by rfl⟩ : syracuseStep 2506247 = 3759371) B3759371
theorem B9027233 : Blo 1112627 9027233 := bstep (se 2 (by rfl) ⟨3385212, by rfl⟩ : syracuseStep 9027233 = 6770425) B6770425
theorem B2506427 : Blo 1112627 2506427 := bstep (se 1 (by rfl) ⟨1879820, by rfl⟩ : syracuseStep 2506427 = 3759641) B3759641
theorem B5652179 : Blo 1112627 5652179 := bstep (se 1 (by rfl) ⟨4239134, by rfl⟩ : syracuseStep 5652179 = 8478269) B8478269
theorem B1883911 : Blo 1112627 1883911 := bstep (se 1 (by rfl) ⟨1412933, by rfl⟩ : syracuseStep 1883911 = 2825867) B2825867
theorem B5357353 : Blo 1112627 5357353 := bstep (se 2 (by rfl) ⟨2009007, by rfl⟩ : syracuseStep 5357353 = 4018015) B4018015
theorem B1883945 : Blo 1112627 1883945 := bstep (se 2 (by rfl) ⟨706479, by rfl⟩ : syracuseStep 1883945 = 1412959) B1412959
theorem B2506553 : Blo 1112627 2506553 := bstep (se 2 (by rfl) ⟨939957, by rfl⟩ : syracuseStep 2506553 = 1879915) B1879915
theorem B10862693 : Blo 1112627 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B5652827 : Blo 1112627 5652827 := bstep (se 1 (by rfl) ⟨4239620, by rfl⟩ : syracuseStep 5652827 = 8479241) B8479241
theorem B2507183 : Blo 1112627 2507183 := bstep (se 1 (by rfl) ⟨1880387, by rfl⟩ : syracuseStep 2507183 = 3760775) B3760775
theorem B21447089 : Blo 1112627 21447089 := bstep (se 2 (by rfl) ⟨8042658, by rfl⟩ : syracuseStep 21447089 = 16085317) B16085317
theorem B2507219 : Blo 1112627 2507219 := bstep (se 1 (by rfl) ⟨1880414, by rfl⟩ : syracuseStep 2507219 = 3760829) B3760829
theorem B2507327 : Blo 1112627 2507327 := bstep (se 1 (by rfl) ⟨1880495, by rfl⟩ : syracuseStep 2507327 = 3760991) B3760991
theorem B7619143 : Blo 1112627 7619143 := bstep (se 1 (by rfl) ⟨5714357, by rfl⟩ : syracuseStep 7619143 = 11428715) B11428715
theorem B1589881 : Blo 1112627 1589881 := bstep (se 2 (by rfl) ⟨596205, by rfl⟩ : syracuseStep 1589881 = 1192411) B1192411
theorem B2507435 : Blo 1112627 2507435 := bstep (se 1 (by rfl) ⟨1880576, by rfl⟩ : syracuseStep 2507435 = 3761153) B3761153
theorem B2376415 : Blo 1112627 2376415 := bstep (se 1 (by rfl) ⟨1782311, by rfl⟩ : syracuseStep 2376415 = 3564623) B3564623
theorem B2507975 : Blo 1112627 2507975 := bstep (se 1 (by rfl) ⟨1880981, by rfl⟩ : syracuseStep 2507975 = 3761963) B3761963
theorem B4769063 : Blo 1112627 4769063 := bstep (se 1 (by rfl) ⟨3576797, by rfl⟩ : syracuseStep 4769063 = 7153595) B7153595
theorem B2508155 : Blo 1112627 2508155 := bstep (se 1 (by rfl) ⟨1881116, by rfl⟩ : syracuseStep 2508155 = 3762233) B3762233
theorem B2115065 : Blo 1112627 2115065 := bstep (se 2 (by rfl) ⟨793149, by rfl⟩ : syracuseStep 2115065 = 1586299) B1586299
theorem B2508281 : Blo 1112627 2508281 := bstep (se 2 (by rfl) ⟨940605, by rfl⟩ : syracuseStep 2508281 = 1881211) B1881211
theorem B2508371 : Blo 1112627 2508371 := bstep (se 1 (by rfl) ⟨1881278, by rfl⟩ : syracuseStep 2508371 = 3762557) B3762557
theorem B4769437 : Blo 1112627 4769437 := bstep (se 3 (by rfl) ⟨894269, by rfl⟩ : syracuseStep 4769437 = 1788539) B1788539
theorem B1787579 : Blo 1112627 1787579 := bstep (se 1 (by rfl) ⟨1340684, by rfl⟩ : syracuseStep 1787579 = 2681369) B2681369
theorem B2508551 : Blo 1112627 2508551 := bstep (se 1 (by rfl) ⟨1881413, by rfl⟩ : syracuseStep 2508551 = 3762827) B3762827
theorem B19318661 : Blo 1112627 19318661 := bstep (se 4 (by rfl) ⟨1811124, by rfl⟩ : syracuseStep 19318661 = 3622249) B3622249
theorem B2377679 : Blo 1112627 2377679 := bstep (se 1 (by rfl) ⟨1783259, by rfl⟩ : syracuseStep 2377679 = 3566519) B3566519
theorem B9029827 : Blo 1112627 9029827 := bstep (se 1 (by rfl) ⟨6772370, by rfl⟩ : syracuseStep 9029827 = 13544741) B13544741
theorem B13060381 : Blo 1112627 13060381 := bstep (se 3 (by rfl) ⟨2448821, by rfl⟩ : syracuseStep 13060381 = 4897643) B4897643
theorem B2509163 : Blo 1112627 2509163 := bstep (se 1 (by rfl) ⟨1881872, by rfl⟩ : syracuseStep 2509163 = 3763745) B3763745
theorem B9521651 : Blo 1112627 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B2509307 : Blo 1112627 2509307 := bstep (se 1 (by rfl) ⟨1881980, by rfl⟩ : syracuseStep 2509307 = 3763961) B3763961
theorem B25741925 : Blo 1112627 25741925 := bstep (se 4 (by rfl) ⟨2413305, by rfl⟩ : syracuseStep 25741925 = 4826611) B4826611
theorem B2509433 : Blo 1112627 2509433 := bstep (se 2 (by rfl) ⟨941037, by rfl⟩ : syracuseStep 2509433 = 1882075) B1882075
theorem B2509487 : Blo 1112627 2509487 := bstep (se 1 (by rfl) ⟨1882115, by rfl⟩ : syracuseStep 2509487 = 3764231) B3764231
theorem B2378423 : Blo 1112627 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B2509559 : Blo 1112627 2509559 := bstep (se 1 (by rfl) ⟨1882169, by rfl⟩ : syracuseStep 2509559 = 3764339) B3764339
theorem B2116523 : Blo 1112627 2116523 := bstep (se 1 (by rfl) ⟨1587392, by rfl⟩ : syracuseStep 2116523 = 3174785) B3174785
theorem B2509739 : Blo 1112627 2509739 := bstep (se 1 (by rfl) ⟨1882304, by rfl⟩ : syracuseStep 2509739 = 3764609) B3764609
theorem B5721005 : Blo 1112627 5721005 := bstep (se 3 (by rfl) ⟨1072688, by rfl⟩ : syracuseStep 5721005 = 2145377) B2145377
theorem B2510279 : Blo 1112627 2510279 := bstep (se 1 (by rfl) ⟨1882709, by rfl⟩ : syracuseStep 2510279 = 3765419) B3765419
theorem B6016771 : Blo 1112627 6016771 := bstep (se 1 (by rfl) ⟨4512578, by rfl⟩ : syracuseStep 6016771 = 9025157) B9025157
theorem B36130607 : Blo 1112627 36130607 := bstep (se 1 (by rfl) ⟨27097955, by rfl⟩ : syracuseStep 36130607 = 54195911) B54195911
theorem B2510639 : Blo 1112627 2510639 := bstep (se 1 (by rfl) ⟨1882979, by rfl⟩ : syracuseStep 2510639 = 3765959) B3765959
theorem B38588521 : Blo 1112627 38588521 := bstep (se 2 (by rfl) ⟨14470695, by rfl⟩ : syracuseStep 38588521 = 28941391) B28941391
theorem B2117897 : Blo 1112627 2117897 := bstep (se 2 (by rfl) ⟨794211, by rfl⟩ : syracuseStep 2117897 = 1588423) B1588423
theorem B2675035 : Blo 1112627 2675035 := bstep (se 1 (by rfl) ⟨2006276, by rfl⟩ : syracuseStep 2675035 = 4012553) B4012553
theorem B2511215 : Blo 1112627 2511215 := bstep (se 1 (by rfl) ⟨1883411, by rfl⟩ : syracuseStep 2511215 = 3766823) B3766823
theorem B2675111 : Blo 1112627 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B2511287 : Blo 1112627 2511287 := bstep (se 1 (by rfl) ⟨1883465, by rfl⟩ : syracuseStep 2511287 = 3766931) B3766931
theorem B3756563 : Blo 1112627 3756563 := bstep (se 1 (by rfl) ⟨2817422, by rfl⟩ : syracuseStep 3756563 = 5634845) B5634845
theorem B2511431 : Blo 1112627 2511431 := bstep (se 1 (by rfl) ⟨1883573, by rfl⟩ : syracuseStep 2511431 = 3767147) B3767147
theorem B2511467 : Blo 1112627 2511467 := bstep (se 1 (by rfl) ⟨1883600, by rfl⟩ : syracuseStep 2511467 = 3767201) B3767201
theorem B7132013 : Blo 1112627 7132013 := bstep (se 3 (by rfl) ⟨1337252, by rfl⟩ : syracuseStep 7132013 = 2674505) B2674505
theorem B2511863 : Blo 1112627 2511863 := bstep (se 1 (by rfl) ⟨1883897, by rfl⟩ : syracuseStep 2511863 = 3767795) B3767795
theorem B4019399 : Blo 1112627 4019399 := bstep (se 1 (by rfl) ⟨3014549, by rfl⟩ : syracuseStep 4019399 = 6029099) B6029099
theorem B3921095 : Blo 1112627 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B2512223 : Blo 1112627 2512223 := bstep (se 1 (by rfl) ⟨1884167, by rfl⟩ : syracuseStep 2512223 = 3768335) B3768335
theorem B2119355 : Blo 1112627 2119355 := bstep (se 1 (by rfl) ⟨1589516, by rfl⟩ : syracuseStep 2119355 = 3179033) B3179033
theorem B2381575 : Blo 1112627 2381575 := bstep (se 1 (by rfl) ⟨1786181, by rfl⟩ : syracuseStep 2381575 = 3572363) B3572363
theorem B2381609 : Blo 1112627 2381609 := bstep (se 2 (by rfl) ⟨893103, by rfl⟩ : syracuseStep 2381609 = 1786207) B1786207
theorem B6346583 : Blo 1112627 6346583 := bstep (se 1 (by rfl) ⟨4759937, by rfl⟩ : syracuseStep 6346583 = 9519875) B9519875
theorem B13555745 : Blo 1112627 13555745 := bstep (se 2 (by rfl) ⟨5083404, by rfl⟩ : syracuseStep 13555745 = 10166809) B10166809
theorem B3758345 : Blo 1112627 3758345 := bstep (se 2 (by rfl) ⟨1409379, by rfl⟩ : syracuseStep 3758345 = 2818759) B2818759
theorem B3168679 : Blo 1112627 3168679 := bstep (se 1 (by rfl) ⟨2376509, by rfl⟩ : syracuseStep 3168679 = 4753019) B4753019
theorem B2579023 : Blo 1112627 2579023 := bstep (se 1 (by rfl) ⟨1934267, by rfl⟩ : syracuseStep 2579023 = 3868535) B3868535
theorem B19553005 : Blo 1112627 19553005 := bstep (se 3 (by rfl) ⟨3666188, by rfl⟩ : syracuseStep 19553005 = 7332377) B7332377
theorem B3759479 : Blo 1112627 3759479 := bstep (se 1 (by rfl) ⟨2819609, by rfl⟩ : syracuseStep 3759479 = 5639219) B5639219
theorem B24141473 : Blo 1112627 24141473 := bstep (se 2 (by rfl) ⟨9053052, by rfl⟩ : syracuseStep 24141473 = 18106105) B18106105
theorem B2383823 : Blo 1112627 2383823 := bstep (se 1 (by rfl) ⟨1787867, by rfl⟩ : syracuseStep 2383823 = 3575735) B3575735
theorem B5431499 : Blo 1112627 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B3760559 : Blo 1112627 3760559 := bstep (se 1 (by rfl) ⟨2820419, by rfl⟩ : syracuseStep 3760559 = 5640839) B5640839
theorem B16278245 : Blo 1112627 16278245 := bstep (se 4 (by rfl) ⟨1526085, by rfl⟩ : syracuseStep 16278245 = 3052171) B3052171
theorem B2679571 : Blo 1112627 2679571 := bstep (se 1 (by rfl) ⟨2009678, by rfl⟩ : syracuseStep 2679571 = 4019357) B4019357
theorem B2712475 : Blo 1112627 2712475 := bstep (se 1 (by rfl) ⟨2034356, by rfl⟩ : syracuseStep 2712475 = 4068713) B4068713
theorem B3007631 : Blo 1112627 3007631 := bstep (se 1 (by rfl) ⟨2255723, by rfl⟩ : syracuseStep 3007631 = 4511447) B4511447
theorem B3007867 : Blo 1112627 3007867 := bstep (se 1 (by rfl) ⟨2255900, by rfl⟩ : syracuseStep 3007867 = 4511801) B4511801
theorem B3761531 : Blo 1112627 3761531 := bstep (se 1 (by rfl) ⟨2821148, by rfl⟩ : syracuseStep 3761531 = 5642297) B5642297
theorem B5433193 : Blo 1112627 5433193 := bstep (se 2 (by rfl) ⟨2037447, by rfl⟩ : syracuseStep 5433193 = 4074895) B4074895
theorem B10709171 : Blo 1112627 10709171 := bstep (se 1 (by rfl) ⟨8031878, by rfl⟩ : syracuseStep 10709171 = 16063757) B16063757
theorem B3565853 : Blo 1112627 3565853 := bstep (se 3 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 3565853 = 1337195) B1337195
theorem B3172927 : Blo 1112627 3172927 := bstep (se 1 (by rfl) ⟨2379695, by rfl⟩ : syracuseStep 3172927 = 4759391) B4759391
theorem B2681417 : Blo 1112627 2681417 := bstep (se 2 (by rfl) ⟨1005531, by rfl⟩ : syracuseStep 2681417 = 2011063) B2011063
theorem B3762935 : Blo 1112627 3762935 := bstep (se 1 (by rfl) ⟨2822201, by rfl⟩ : syracuseStep 3762935 = 5644403) B5644403
theorem B2255771 : Blo 1112627 2255771 := bstep (se 1 (by rfl) ⟨1691828, by rfl⟩ : syracuseStep 2255771 = 3383657) B3383657
theorem B10709981 : Blo 1112627 10709981 := bstep (se 3 (by rfl) ⟨2008121, by rfl⟩ : syracuseStep 10709981 = 4016243) B4016243
theorem B3566879 : Blo 1112627 3566879 := bstep (se 1 (by rfl) ⟨2675159, by rfl⟩ : syracuseStep 3566879 = 5350319) B5350319
theorem B3764015 : Blo 1112627 3764015 := bstep (se 1 (by rfl) ⟨2823011, by rfl⟩ : syracuseStep 3764015 = 5646023) B5646023
theorem B6353099 : Blo 1112627 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B24080921 : Blo 1112627 24080921 := bstep (se 2 (by rfl) ⟨9030345, by rfl⟩ : syracuseStep 24080921 = 18060691) B18060691
theorem B10712321 : Blo 1112627 10712321 := bstep (se 2 (by rfl) ⟨4017120, by rfl⟩ : syracuseStep 10712321 = 8034241) B8034241
theorem B4289831 : Blo 1112627 4289831 := bstep (se 1 (by rfl) ⟨3217373, by rfl⟩ : syracuseStep 4289831 = 6434747) B6434747
theorem B4650553 : Blo 1112627 4650553 := bstep (se 2 (by rfl) ⟨1743957, by rfl⟩ : syracuseStep 4650553 = 3487915) B3487915
theorem B24114833 : Blo 1112627 24114833 := bstep (se 2 (by rfl) ⟨9043062, by rfl⟩ : syracuseStep 24114833 = 18086125) B18086125
theorem B173930165 : Blo 1112627 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B3569339 : Blo 1112627 3569339 := bstep (se 1 (by rfl) ⟨2677004, by rfl⟩ : syracuseStep 3569339 = 5354009) B5354009
theorem B5437115 : Blo 1112627 5437115 := bstep (se 1 (by rfl) ⟨4077836, by rfl⟩ : syracuseStep 5437115 = 8155673) B8155673
theorem B5633873 : Blo 1112627 5633873 := bstep (se 2 (by rfl) ⟨2112702, by rfl⟩ : syracuseStep 5633873 = 4225405) B4225405
theorem B3766121 : Blo 1112627 3766121 := bstep (se 2 (by rfl) ⟨1412295, by rfl⟩ : syracuseStep 3766121 = 2824591) B2824591
theorem B1669385 : Blo 1112627 1669385 := bstep (se 2 (by rfl) ⟨626019, by rfl⟩ : syracuseStep 1669385 = 1252039) B1252039
theorem B3766553 : Blo 1112627 3766553 := bstep (se 2 (by rfl) ⟨1412457, by rfl⟩ : syracuseStep 3766553 = 2824915) B2824915
theorem B4225391 : Blo 1112627 4225391 := bstep (se 1 (by rfl) ⟨3169043, by rfl⟩ : syracuseStep 4225391 = 6338087) B6338087
theorem B1669487 : Blo 1112627 1669487 := bstep (se 1 (by rfl) ⟨1252115, by rfl⟩ : syracuseStep 1669487 = 2504231) B2504231
theorem B1112639 : Blo 1112627 1112639 := bstep (se 1 (by rfl) ⟨834479, by rfl⟩ : syracuseStep 1112639 = 1668959) B1668959
theorem B1112647 : Blo 1112627 1112647 := bstep (se 1 (by rfl) ⟨834485, by rfl⟩ : syracuseStep 1112647 = 1668971) B1668971
theorem B1669703 : Blo 1112627 1669703 := bstep (se 1 (by rfl) ⟨1252277, by rfl⟩ : syracuseStep 1669703 = 2504555) B2504555
theorem B1669739 : Blo 1112627 1669739 := bstep (se 1 (by rfl) ⟨1252304, by rfl⟩ : syracuseStep 1669739 = 2504609) B2504609
theorem B2816633 : Blo 1112627 2816633 := bstep (se 2 (by rfl) ⟨1056237, by rfl⟩ : syracuseStep 2816633 = 2112475) B2112475
theorem B5634683 : Blo 1112627 5634683 := bstep (se 1 (by rfl) ⟨4226012, by rfl⟩ : syracuseStep 5634683 = 8452025) B8452025
theorem B1112799 : Blo 1112627 1112799 := bstep (se 1 (by rfl) ⟨834599, by rfl⟩ : syracuseStep 1112799 = 1669199) B1669199
theorem B1112879 : Blo 1112627 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B1669967 : Blo 1112627 1669967 := bstep (se 1 (by rfl) ⟨1252475, by rfl⟩ : syracuseStep 1669967 = 2504951) B2504951
theorem B1112987 : Blo 1112627 1112987 := bstep (se 1 (by rfl) ⟨834740, by rfl⟩ : syracuseStep 1112987 = 1669481) B1669481
theorem B1113039 : Blo 1112627 1113039 := bstep (se 1 (by rfl) ⟨834779, by rfl⟩ : syracuseStep 1113039 = 1669559) B1669559
theorem B1113063 : Blo 1112627 1113063 := bstep (se 1 (by rfl) ⟨834797, by rfl⟩ : syracuseStep 1113063 = 1669595) B1669595
theorem B1670363 : Blo 1112627 1670363 := bstep (se 1 (by rfl) ⟨1252772, by rfl⟩ : syracuseStep 1670363 = 2505545) B2505545
theorem B1113375 : Blo 1112627 1113375 := bstep (se 1 (by rfl) ⟨835031, by rfl⟩ : syracuseStep 1113375 = 1670063) B1670063
theorem B1113435 : Blo 1112627 1113435 := bstep (se 1 (by rfl) ⟨835076, by rfl⟩ : syracuseStep 1113435 = 1670153) B1670153
theorem B1408367 : Blo 1112627 1408367 := bstep (se 1 (by rfl) ⟨1056275, by rfl⟩ : syracuseStep 1408367 = 2112551) B2112551
theorem B1113455 : Blo 1112627 1113455 := bstep (se 1 (by rfl) ⟨835091, by rfl⟩ : syracuseStep 1113455 = 1670183) B1670183
theorem B1670537 : Blo 1112627 1670537 := bstep (se 2 (by rfl) ⟨626451, by rfl⟩ : syracuseStep 1670537 = 1252903) B1252903
theorem B1408423 : Blo 1112627 1408423 := bstep (se 1 (by rfl) ⟨1056317, by rfl⟩ : syracuseStep 1408423 = 2112635) B2112635
theorem B1113511 : Blo 1112627 1113511 := bstep (se 1 (by rfl) ⟨835133, by rfl⟩ : syracuseStep 1113511 = 1670267) B1670267
theorem B1113595 : Blo 1112627 1113595 := bstep (se 1 (by rfl) ⟨835196, by rfl⟩ : syracuseStep 1113595 = 1670393) B1670393
theorem B1113663 : Blo 1112627 1113663 := bstep (se 1 (by rfl) ⟨835247, by rfl⟩ : syracuseStep 1113663 = 1670495) B1670495
theorem B1113671 : Blo 1112627 1113671 := bstep (se 1 (by rfl) ⟨835253, by rfl⟩ : syracuseStep 1113671 = 1670507) B1670507
theorem B3767903 : Blo 1112627 3767903 := bstep (se 1 (by rfl) ⟨2825927, by rfl⟩ : syracuseStep 3767903 = 5651855) B5651855
theorem B1113823 : Blo 1112627 1113823 := bstep (se 1 (by rfl) ⟨835367, by rfl⟩ : syracuseStep 1113823 = 1670735) B1670735
theorem B1408747 : Blo 1112627 1408747 := bstep (se 1 (by rfl) ⟨1056560, by rfl⟩ : syracuseStep 1408747 = 2113121) B2113121
theorem B1670891 : Blo 1112627 1670891 := bstep (se 1 (by rfl) ⟨1253168, by rfl⟩ : syracuseStep 1670891 = 2506337) B2506337
theorem B4226863 : Blo 1112627 4226863 := bstep (se 1 (by rfl) ⟨3170147, by rfl⟩ : syracuseStep 4226863 = 6340295) B6340295
theorem B1113903 : Blo 1112627 1113903 := bstep (se 1 (by rfl) ⟨835427, by rfl⟩ : syracuseStep 1113903 = 1670855) B1670855
theorem B43417417 : Blo 1112627 43417417 := bstep (se 2 (by rfl) ⟨16281531, by rfl⟩ : syracuseStep 43417417 = 32563063) B32563063
theorem B1114011 : Blo 1112627 1114011 := bstep (se 1 (by rfl) ⟨835508, by rfl⟩ : syracuseStep 1114011 = 1671017) B1671017
theorem B1114063 : Blo 1112627 1114063 := bstep (se 1 (by rfl) ⟨835547, by rfl⟩ : syracuseStep 1114063 = 1671095) B1671095
theorem B1671119 : Blo 1112627 1671119 := bstep (se 1 (by rfl) ⟨1253339, by rfl⟩ : syracuseStep 1671119 = 2506679) B2506679
theorem B1114087 : Blo 1112627 1114087 := bstep (se 1 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 1114087 = 1671131) B1671131
theorem B7241795 : Blo 1112627 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B1114343 : Blo 1112627 1114343 := bstep (se 1 (by rfl) ⟨835757, by rfl⟩ : syracuseStep 1114343 = 1671515) B1671515
theorem B3768551 : Blo 1112627 3768551 := bstep (se 1 (by rfl) ⟨2826413, by rfl⟩ : syracuseStep 3768551 = 5652827) B5652827
theorem B1671455 : Blo 1112627 1671455 := bstep (se 1 (by rfl) ⟨1253591, by rfl⟩ : syracuseStep 1671455 = 2507183) B2507183
theorem B1671479 : Blo 1112627 1671479 := bstep (se 1 (by rfl) ⟨1253609, by rfl⟩ : syracuseStep 1671479 = 2507219) B2507219
theorem B1671551 : Blo 1112627 1671551 := bstep (se 1 (by rfl) ⟨1253663, by rfl⟩ : syracuseStep 1671551 = 2507327) B2507327
theorem B1114495 : Blo 1112627 1114495 := bstep (se 1 (by rfl) ⟨835871, by rfl⟩ : syracuseStep 1114495 = 1671743) B1671743
theorem B1671623 : Blo 1112627 1671623 := bstep (se 1 (by rfl) ⟨1253717, by rfl⟩ : syracuseStep 1671623 = 2507435) B2507435
theorem B4522439 : Blo 1112627 4522439 := bstep (se 1 (by rfl) ⟨3391829, by rfl⟩ : syracuseStep 4522439 = 6783659) B6783659
theorem B1114575 : Blo 1112627 1114575 := bstep (se 1 (by rfl) ⟨835931, by rfl⟩ : syracuseStep 1114575 = 1671863) B1671863
theorem B1114727 : Blo 1112627 1114727 := bstep (se 1 (by rfl) ⟨836045, by rfl⟩ : syracuseStep 1114727 = 1672091) B1672091
theorem B10158857 : Blo 1112627 10158857 := bstep (se 2 (by rfl) ⟨3809571, by rfl⟩ : syracuseStep 10158857 = 7619143) B7619143
theorem B1671977 : Blo 1112627 1671977 := bstep (se 2 (by rfl) ⟨626991, by rfl⟩ : syracuseStep 1671977 = 1253983) B1253983
theorem B1671983 : Blo 1112627 1671983 := bstep (se 1 (by rfl) ⟨1253987, by rfl⟩ : syracuseStep 1671983 = 2507975) B2507975
theorem B1114991 : Blo 1112627 1114991 := bstep (se 1 (by rfl) ⟨836243, by rfl⟩ : syracuseStep 1114991 = 1672487) B1672487
theorem B3179375 : Blo 1112627 3179375 := bstep (se 1 (by rfl) ⟨2384531, by rfl⟩ : syracuseStep 3179375 = 4769063) B4769063
theorem B9536413 : Blo 1112627 9536413 := bstep (se 3 (by rfl) ⟨1788077, by rfl⟩ : syracuseStep 9536413 = 3576155) B3576155
theorem B1672103 : Blo 1112627 1672103 := bstep (se 1 (by rfl) ⟨1254077, by rfl⟩ : syracuseStep 1672103 = 2508155) B2508155
theorem B1115047 : Blo 1112627 1115047 := bstep (se 1 (by rfl) ⟨836285, by rfl⟩ : syracuseStep 1115047 = 1672571) B1672571
theorem B1410043 : Blo 1112627 1410043 := bstep (se 1 (by rfl) ⟨1057532, by rfl⟩ : syracuseStep 1410043 = 2115065) B2115065
theorem B1672187 : Blo 1112627 1672187 := bstep (se 1 (by rfl) ⟨1254140, by rfl⟩ : syracuseStep 1672187 = 2508281) B2508281
theorem B1115131 : Blo 1112627 1115131 := bstep (se 1 (by rfl) ⟨836348, by rfl⟩ : syracuseStep 1115131 = 1672697) B1672697
theorem B3572761 : Blo 1112627 3572761 := bstep (se 2 (by rfl) ⟨1339785, by rfl⟩ : syracuseStep 3572761 = 2679571) B2679571
theorem B1672247 : Blo 1112627 1672247 := bstep (se 1 (by rfl) ⟨1254185, by rfl⟩ : syracuseStep 1672247 = 2508371) B2508371
theorem B1115199 : Blo 1112627 1115199 := bstep (se 1 (by rfl) ⟨836399, by rfl⟩ : syracuseStep 1115199 = 1672799) B1672799
theorem B1672367 : Blo 1112627 1672367 := bstep (se 1 (by rfl) ⟨1254275, by rfl⟩ : syracuseStep 1672367 = 2508551) B2508551
theorem B1115343 : Blo 1112627 1115343 := bstep (se 1 (by rfl) ⟨836507, by rfl⟩ : syracuseStep 1115343 = 1673015) B1673015
theorem B8455427 : Blo 1112627 8455427 := bstep (se 1 (by rfl) ⟨6341570, by rfl⟩ : syracuseStep 8455427 = 12683141) B12683141
theorem B12879107 : Blo 1112627 12879107 := bstep (se 1 (by rfl) ⟨9659330, by rfl⟩ : syracuseStep 12879107 = 19318661) B19318661
theorem B1115547 : Blo 1112627 1115547 := bstep (se 1 (by rfl) ⟨836660, by rfl⟩ : syracuseStep 1115547 = 1673321) B1673321
theorem B1672775 : Blo 1112627 1672775 := bstep (se 1 (by rfl) ⟨1254581, by rfl⟩ : syracuseStep 1672775 = 2509163) B2509163
theorem B1115759 : Blo 1112627 1115759 := bstep (se 1 (by rfl) ⟨836819, by rfl⟩ : syracuseStep 1115759 = 1673639) B1673639
theorem B1672871 : Blo 1112627 1672871 := bstep (se 1 (by rfl) ⟨1254653, by rfl⟩ : syracuseStep 1672871 = 2509307) B2509307
theorem B1115815 : Blo 1112627 1115815 := bstep (se 1 (by rfl) ⟨836861, by rfl⟩ : syracuseStep 1115815 = 1673723) B1673723
theorem B1672955 : Blo 1112627 1672955 := bstep (se 1 (by rfl) ⟨1254716, by rfl⟩ : syracuseStep 1672955 = 2509433) B2509433
theorem B1115899 : Blo 1112627 1115899 := bstep (se 1 (by rfl) ⟨836924, by rfl⟩ : syracuseStep 1115899 = 1673849) B1673849
theorem B1672991 : Blo 1112627 1672991 := bstep (se 1 (by rfl) ⟨1254743, by rfl⟩ : syracuseStep 1672991 = 2509487) B2509487
theorem B1115935 : Blo 1112627 1115935 := bstep (se 1 (by rfl) ⟨836951, by rfl⟩ : syracuseStep 1115935 = 1673903) B1673903
theorem B1115967 : Blo 1112627 1115967 := bstep (se 1 (by rfl) ⟨836975, by rfl⟩ : syracuseStep 1115967 = 1673951) B1673951
theorem B1673039 : Blo 1112627 1673039 := bstep (se 1 (by rfl) ⟨1254779, by rfl⟩ : syracuseStep 1673039 = 2509559) B2509559
theorem B1411015 : Blo 1112627 1411015 := bstep (se 1 (by rfl) ⟨1058261, by rfl⟩ : syracuseStep 1411015 = 2116523) B2116523
theorem B1673159 : Blo 1112627 1673159 := bstep (se 1 (by rfl) ⟨1254869, by rfl⟩ : syracuseStep 1673159 = 2509739) B2509739
theorem B1116143 : Blo 1112627 1116143 := bstep (se 1 (by rfl) ⟨837107, by rfl⟩ : syracuseStep 1116143 = 1674215) B1674215
theorem B1116315 : Blo 1112627 1116315 := bstep (se 1 (by rfl) ⟨837236, by rfl⟩ : syracuseStep 1116315 = 1674473) B1674473
theorem B1116351 : Blo 1112627 1116351 := bstep (se 1 (by rfl) ⟨837263, by rfl⟩ : syracuseStep 1116351 = 1674527) B1674527
theorem B6359249 : Blo 1112627 6359249 := bstep (se 2 (by rfl) ⟨2384718, by rfl⟩ : syracuseStep 6359249 = 4769437) B4769437
theorem B1673513 : Blo 1112627 1673513 := bstep (se 2 (by rfl) ⟨627567, by rfl⟩ : syracuseStep 1673513 = 1255135) B1255135
theorem B1673519 : Blo 1112627 1673519 := bstep (se 1 (by rfl) ⟨1255139, by rfl⟩ : syracuseStep 1673519 = 2510279) B2510279
theorem B1116463 : Blo 1112627 1116463 := bstep (se 1 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 1116463 = 1674695) B1674695
theorem B2820491 : Blo 1112627 2820491 := bstep (se 1 (by rfl) ⟨2115368, by rfl⟩ : syracuseStep 2820491 = 4230737) B4230737
theorem B24087071 : Blo 1112627 24087071 := bstep (se 1 (by rfl) ⟨18065303, by rfl⟩ : syracuseStep 24087071 = 36130607) B36130607
theorem B1673759 : Blo 1112627 1673759 := bstep (se 1 (by rfl) ⟨1255319, by rfl⟩ : syracuseStep 1673759 = 2510639) B2510639
theorem B1411931 : Blo 1112627 1411931 := bstep (se 1 (by rfl) ⟨1058948, by rfl⟩ : syracuseStep 1411931 = 2117897) B2117897
theorem B1674143 : Blo 1112627 1674143 := bstep (se 1 (by rfl) ⟨1255607, by rfl⟩ : syracuseStep 1674143 = 2511215) B2511215
theorem B1674191 : Blo 1112627 1674191 := bstep (se 1 (by rfl) ⟨1255643, by rfl⟩ : syracuseStep 1674191 = 2511287) B2511287
theorem B1674281 : Blo 1112627 1674281 := bstep (se 2 (by rfl) ⟨627855, by rfl⟩ : syracuseStep 1674281 = 1255711) B1255711
theorem B1674287 : Blo 1112627 1674287 := bstep (se 1 (by rfl) ⟨1255715, by rfl⟩ : syracuseStep 1674287 = 2511431) B2511431
theorem B1674311 : Blo 1112627 1674311 := bstep (se 1 (by rfl) ⟨1255733, by rfl⟩ : syracuseStep 1674311 = 2511467) B2511467
theorem B10456253 : Blo 1112627 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B4754675 : Blo 1112627 4754675 := bstep (se 1 (by rfl) ⟨3566006, by rfl⟩ : syracuseStep 4754675 = 7132013) B7132013
theorem B1674575 : Blo 1112627 1674575 := bstep (se 1 (by rfl) ⟨1255931, by rfl⟩ : syracuseStep 1674575 = 2511863) B2511863
theorem B4230569 : Blo 1112627 4230569 := bstep (se 2 (by rfl) ⟨1586463, by rfl⟩ : syracuseStep 4230569 = 3172927) B3172927
theorem B1674665 : Blo 1112627 1674665 := bstep (se 2 (by rfl) ⟨627999, by rfl⟩ : syracuseStep 1674665 = 1255999) B1255999
theorem B1674815 : Blo 1112627 1674815 := bstep (se 1 (by rfl) ⟨1256111, by rfl⟩ : syracuseStep 1674815 = 2512223) B2512223
theorem B30510701 : Blo 1112627 30510701 := bstep (se 3 (by rfl) ⟨5720756, by rfl⟩ : syracuseStep 30510701 = 11441513) B11441513
theorem B1412903 : Blo 1112627 1412903 := bstep (se 1 (by rfl) ⟨1059677, by rfl⟩ : syracuseStep 1412903 = 2119355) B2119355
theorem B4231055 : Blo 1112627 4231055 := bstep (se 1 (by rfl) ⟨3173291, by rfl⟩ : syracuseStep 4231055 = 6346583) B6346583
theorem B2822111 : Blo 1112627 2822111 := bstep (se 1 (by rfl) ⟨2116583, by rfl⟩ : syracuseStep 2822111 = 4233167) B4233167
theorem B2822759 : Blo 1112627 2822759 := bstep (se 1 (by rfl) ⟨2117069, by rfl⟩ : syracuseStep 2822759 = 4234139) B4234139
theorem B5641001 : Blo 1112627 5641001 := bstep (se 2 (by rfl) ⟨2115375, by rfl⟩ : syracuseStep 5641001 = 4230751) B4230751
theorem B4231997 : Blo 1112627 4231997 := bstep (se 3 (by rfl) ⟨793499, by rfl⟩ : syracuseStep 4231997 = 1586999) B1586999
theorem B9507779 : Blo 1112627 9507779 := bstep (se 1 (by rfl) ⟨7130834, by rfl⟩ : syracuseStep 9507779 = 14261669) B14261669
theorem B2855945 : Blo 1112627 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B2823275 : Blo 1112627 2823275 := bstep (se 1 (by rfl) ⟨2117456, by rfl⟩ : syracuseStep 2823275 = 4234913) B4234913
theorem B16094315 : Blo 1112627 16094315 := bstep (se 1 (by rfl) ⟨12070736, by rfl⟩ : syracuseStep 16094315 = 24141473) B24141473
theorem B27071779 : Blo 1112627 27071779 := bstep (se 1 (by rfl) ⟨20303834, by rfl⟩ : syracuseStep 27071779 = 40607669) B40607669
theorem B51451361 : Blo 1112627 51451361 := bstep (se 2 (by rfl) ⟨19294260, by rfl⟩ : syracuseStep 51451361 = 38588521) B38588521
theorem B10852163 : Blo 1112627 10852163 := bstep (se 1 (by rfl) ⟨8139122, by rfl⟩ : syracuseStep 10852163 = 16278245) B16278245
theorem B2005087 : Blo 1112627 2005087 := bstep (se 1 (by rfl) ⟨1503815, by rfl⟩ : syracuseStep 2005087 = 3007631) B3007631
theorem B5347625 : Blo 1112627 5347625 := bstep (se 2 (by rfl) ⟨2005359, by rfl⟩ : syracuseStep 5347625 = 4010719) B4010719
theorem B2824571 : Blo 1112627 2824571 := bstep (se 1 (by rfl) ⟨2118428, by rfl⟩ : syracuseStep 2824571 = 4236857) B4236857
theorem B8460773 : Blo 1112627 8460773 := bstep (se 4 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 8460773 = 1586395) B1586395
theorem B18094691 : Blo 1112627 18094691 := bstep (se 1 (by rfl) ⟨13571018, by rfl⟩ : syracuseStep 18094691 = 27142037) B27142037
theorem B64363409 : Blo 1112627 64363409 := bstep (se 2 (by rfl) ⟨24136278, by rfl⟩ : syracuseStep 64363409 = 48272557) B48272557
theorem B1252255 : Blo 1112627 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B1252399 : Blo 1112627 1252399 := bstep (se 1 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 1252399 = 1878599) B1878599
theorem B1252687 : Blo 1112627 1252687 := bstep (se 1 (by rfl) ⟨939515, by rfl⟩ : syracuseStep 1252687 = 1879031) B1879031
theorem B9051857 : Blo 1112627 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B1253191 : Blo 1112627 1253191 := bstep (se 1 (by rfl) ⟨939893, by rfl⟩ : syracuseStep 1253191 = 1879787) B1879787
theorem B4235399 : Blo 1112627 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B1253839 : Blo 1112627 1253839 := bstep (se 1 (by rfl) ⟨940379, by rfl⟩ : syracuseStep 1253839 = 1880759) B1880759
theorem B4235885 : Blo 1112627 4235885 := bstep (se 3 (by rfl) ⟨794228, by rfl⟩ : syracuseStep 4235885 = 1588457) B1588457
theorem B18064073 : Blo 1112627 18064073 := bstep (se 2 (by rfl) ⟨6774027, by rfl⟩ : syracuseStep 18064073 = 13548055) B13548055
theorem B42869573 : Blo 1112627 42869573 := bstep (se 4 (by rfl) ⟨4019022, by rfl⟩ : syracuseStep 42869573 = 8038045) B8038045
theorem B2859887 : Blo 1112627 2859887 := bstep (se 1 (by rfl) ⟨2144915, by rfl⟩ : syracuseStep 2859887 = 4289831) B4289831
theorem B1254811 : Blo 1112627 1254811 := bstep (se 1 (by rfl) ⟨941108, by rfl⟩ : syracuseStep 1254811 = 1882217) B1882217
theorem B13575599 : Blo 1112627 13575599 := bstep (se 1 (by rfl) ⟨10181699, by rfl⟩ : syracuseStep 13575599 = 20363399) B20363399
theorem B1877755 : Blo 1112627 1877755 := bstep (se 1 (by rfl) ⟨1408316, by rfl⟩ : syracuseStep 1877755 = 2816633) B2816633
theorem B28977029 : Blo 1112627 28977029 := bstep (se 4 (by rfl) ⟨2716596, by rfl⟩ : syracuseStep 28977029 = 5433193) B5433193
theorem B1877897 : Blo 1112627 1877897 := bstep (se 2 (by rfl) ⟨704211, by rfl⟩ : syracuseStep 1877897 = 1408423) B1408423
theorem B1878329 : Blo 1112627 1878329 := bstep (se 2 (by rfl) ⟨704373, by rfl⟩ : syracuseStep 1878329 = 1408747) B1408747
theorem B1255963 : Blo 1112627 1255963 := bstep (se 1 (by rfl) ⟨941972, by rfl⟩ : syracuseStep 1255963 = 1883945) B1883945
theorem B1878943 : Blo 1112627 1878943 := bstep (se 1 (by rfl) ⟨1409207, by rfl⟩ : syracuseStep 1878943 = 2818415) B2818415
theorem B14298059 : Blo 1112627 14298059 := bstep (se 1 (by rfl) ⟨10723544, by rfl⟩ : syracuseStep 14298059 = 21447089) B21447089
theorem B4238315 : Blo 1112627 4238315 := bstep (se 1 (by rfl) ⟨3178736, by rfl⟩ : syracuseStep 4238315 = 6357473) B6357473
theorem B5647481 : Blo 1112627 5647481 := bstep (se 2 (by rfl) ⟨2117805, by rfl⟩ : syracuseStep 5647481 = 4235611) B4235611
theorem B2010377 : Blo 1112627 2010377 := bstep (se 2 (by rfl) ⟨753891, by rfl⟩ : syracuseStep 2010377 = 1507783) B1507783
theorem B1879375 : Blo 1112627 1879375 := bstep (se 1 (by rfl) ⟨1409531, by rfl⟩ : syracuseStep 1879375 = 2819063) B2819063
theorem B1879463 : Blo 1112627 1879463 := bstep (se 1 (by rfl) ⟨1409597, by rfl⟩ : syracuseStep 1879463 = 2819195) B2819195
theorem B1879625 : Blo 1112627 1879625 := bstep (se 2 (by rfl) ⟨704859, by rfl⟩ : syracuseStep 1879625 = 1409719) B1409719
theorem B1191719 : Blo 1112627 1191719 := bstep (se 1 (by rfl) ⟨893789, by rfl⟩ : syracuseStep 1191719 = 1787579) B1787579
theorem B3616633 : Blo 1112627 3616633 := bstep (se 2 (by rfl) ⟨1356237, by rfl⟩ : syracuseStep 3616633 = 2712475) B2712475
theorem B144551951 : Blo 1112627 144551951 := bstep (se 1 (by rfl) ⟨108413963, by rfl⟩ : syracuseStep 144551951 = 216827927) B216827927
theorem B14266691 : Blo 1112627 14266691 := bstep (se 1 (by rfl) ⟨10700018, by rfl⟩ : syracuseStep 14266691 = 21400037) B21400037
theorem B21410183 : Blo 1112627 21410183 := bstep (se 1 (by rfl) ⟨16057637, by rfl⟩ : syracuseStep 21410183 = 32115275) B32115275
theorem B5648777 : Blo 1112627 5648777 := bstep (se 2 (by rfl) ⟨2118291, by rfl⟩ : syracuseStep 5648777 = 4236583) B4236583
theorem B4010489 : Blo 1112627 4010489 := bstep (se 2 (by rfl) ⟨1503933, by rfl⟩ : syracuseStep 4010489 = 3007867) B3007867
theorem B1880671 : Blo 1112627 1880671 := bstep (se 1 (by rfl) ⟨1410503, by rfl⟩ : syracuseStep 1880671 = 2821007) B2821007
theorem B3814003 : Blo 1112627 3814003 := bstep (se 1 (by rfl) ⟨2860502, by rfl⟩ : syracuseStep 3814003 = 5721005) B5721005
theorem B1881083 : Blo 1112627 1881083 := bstep (se 1 (by rfl) ⟨1410812, by rfl⟩ : syracuseStep 1881083 = 2821625) B2821625
theorem B1881515 : Blo 1112627 1881515 := bstep (se 1 (by rfl) ⟨1411136, by rfl⟩ : syracuseStep 1881515 = 2822273) B2822273
theorem B8566361 : Blo 1112627 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B12039769 : Blo 1112627 12039769 := bstep (se 2 (by rfl) ⟨4514913, by rfl⟩ : syracuseStep 12039769 = 9029827) B9029827
theorem B2504375 : Blo 1112627 2504375 := bstep (se 1 (by rfl) ⟨1878281, by rfl⟩ : syracuseStep 2504375 = 3756563) B3756563
theorem B17413841 : Blo 1112627 17413841 := bstep (se 2 (by rfl) ⟨6530190, by rfl⟩ : syracuseStep 17413841 = 13060381) B13060381
theorem B1882055 : Blo 1112627 1882055 := bstep (se 1 (by rfl) ⟨1411541, by rfl⟩ : syracuseStep 1882055 = 2823083) B2823083
theorem B8042489 : Blo 1112627 8042489 := bstep (se 2 (by rfl) ⟨3015933, by rfl⟩ : syracuseStep 8042489 = 6031867) B6031867
theorem B1882345 : Blo 1112627 1882345 := bstep (se 2 (by rfl) ⟨705879, by rfl⟩ : syracuseStep 1882345 = 1411759) B1411759
theorem B1882811 : Blo 1112627 1882811 := bstep (se 1 (by rfl) ⟨1412108, by rfl⟩ : syracuseStep 1882811 = 2824217) B2824217
theorem B2505563 : Blo 1112627 2505563 := bstep (se 1 (by rfl) ⟨1879172, by rfl⟩ : syracuseStep 2505563 = 3758345) B3758345
theorem B2506319 : Blo 1112627 2506319 := bstep (se 1 (by rfl) ⟨1879739, by rfl⟩ : syracuseStep 2506319 = 3759479) B3759479
theorem B6340477 : Blo 1112627 6340477 := bstep (se 3 (by rfl) ⟨1188839, by rfl⟩ : syracuseStep 6340477 = 2377679) B2377679
theorem B1589215 : Blo 1112627 1589215 := bstep (se 1 (by rfl) ⟨1191911, by rfl⟩ : syracuseStep 1589215 = 2383823) B2383823
theorem B1884127 : Blo 1112627 1884127 := bstep (se 1 (by rfl) ⟨1413095, by rfl⟩ : syracuseStep 1884127 = 2826191) B2826191
theorem B3620999 : Blo 1112627 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B2507039 : Blo 1112627 2507039 := bstep (se 1 (by rfl) ⟨1880279, by rfl⟩ : syracuseStep 2507039 = 3760559) B3760559
theorem B4964807 : Blo 1112627 4964807 := bstep (se 1 (by rfl) ⟨3723605, by rfl⟩ : syracuseStep 4964807 = 7447211) B7447211
theorem B2507687 : Blo 1112627 2507687 := bstep (se 1 (by rfl) ⟨1880765, by rfl⟩ : syracuseStep 2507687 = 3761531) B3761531
theorem B2377235 : Blo 1112627 2377235 := bstep (se 1 (by rfl) ⟨1782926, by rfl⟩ : syracuseStep 2377235 = 3565853) B3565853
theorem B1787611 : Blo 1112627 1787611 := bstep (se 1 (by rfl) ⟨1340708, by rfl⟩ : syracuseStep 1787611 = 2681417) B2681417
theorem B6342461 : Blo 1112627 6342461 := bstep (se 3 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 6342461 = 2378423) B2378423
theorem B2508623 : Blo 1112627 2508623 := bstep (se 1 (by rfl) ⟨1881467, by rfl⟩ : syracuseStep 2508623 = 3762935) B3762935
theorem B2508641 : Blo 1112627 2508641 := bstep (se 2 (by rfl) ⟨940740, by rfl⟩ : syracuseStep 2508641 = 1881481) B1881481
theorem B8046641 : Blo 1112627 8046641 := bstep (se 2 (by rfl) ⟨3017490, by rfl⟩ : syracuseStep 8046641 = 6034981) B6034981
theorem B2377919 : Blo 1112627 2377919 := bstep (se 1 (by rfl) ⟨1783439, by rfl⟩ : syracuseStep 2377919 = 3566879) B3566879
theorem B2148665 : Blo 1112627 2148665 := bstep (se 2 (by rfl) ⟨805749, by rfl⟩ : syracuseStep 2148665 = 1611499) B1611499
theorem B2509217 : Blo 1112627 2509217 := bstep (se 2 (by rfl) ⟨940956, by rfl⟩ : syracuseStep 2509217 = 1881913) B1881913
theorem B2509343 : Blo 1112627 2509343 := bstep (se 1 (by rfl) ⟨1882007, by rfl⟩ : syracuseStep 2509343 = 3764015) B3764015
theorem B12700637 : Blo 1112627 12700637 := bstep (se 3 (by rfl) ⟨2381369, by rfl⟩ : syracuseStep 12700637 = 4762739) B4762739
theorem B6343667 : Blo 1112627 6343667 := bstep (se 1 (by rfl) ⟨4757750, by rfl⟩ : syracuseStep 6343667 = 9515501) B9515501
theorem B3755645 : Blo 1112627 3755645 := bstep (se 3 (by rfl) ⟨704183, by rfl⟩ : syracuseStep 3755645 = 1408367) B1408367
theorem B26070673 : Blo 1112627 26070673 := bstep (se 2 (by rfl) ⟨9776502, by rfl⟩ : syracuseStep 26070673 = 19553005) B19553005
theorem B16076555 : Blo 1112627 16076555 := bstep (se 1 (by rfl) ⟨12057416, by rfl⟩ : syracuseStep 16076555 = 24114833) B24114833
theorem B115953443 : Blo 1112627 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B2379559 : Blo 1112627 2379559 := bstep (se 1 (by rfl) ⟨1784669, by rfl⟩ : syracuseStep 2379559 = 3569339) B3569339
theorem B3624743 : Blo 1112627 3624743 := bstep (se 1 (by rfl) ⟨2718557, by rfl⟩ : syracuseStep 3624743 = 5437115) B5437115
theorem B3755915 : Blo 1112627 3755915 := bstep (se 1 (by rfl) ⟨2816936, by rfl⟩ : syracuseStep 3755915 = 5633873) B5633873
theorem B2510747 : Blo 1112627 2510747 := bstep (se 1 (by rfl) ⟨1883060, by rfl⟩ : syracuseStep 2510747 = 3766121) B3766121
theorem B2511035 : Blo 1112627 2511035 := bstep (se 1 (by rfl) ⟨1883276, by rfl⟩ : syracuseStep 2511035 = 3766553) B3766553
theorem B6345125 : Blo 1112627 6345125 := bstep (se 4 (by rfl) ⟨594855, by rfl⟩ : syracuseStep 6345125 = 1189711) B1189711
theorem B3756455 : Blo 1112627 3756455 := bstep (se 1 (by rfl) ⟨2817341, by rfl⟩ : syracuseStep 3756455 = 5634683) B5634683
theorem B6345377 : Blo 1112627 6345377 := bstep (se 2 (by rfl) ⟨2379516, by rfl⟩ : syracuseStep 6345377 = 4759033) B4759033
theorem B2511521 : Blo 1112627 2511521 := bstep (se 2 (by rfl) ⟨941820, by rfl⟩ : syracuseStep 2511521 = 1883641) B1883641
theorem B2511881 : Blo 1112627 2511881 := bstep (se 2 (by rfl) ⟨941955, by rfl⟩ : syracuseStep 2511881 = 1883911) B1883911
theorem B2511935 : Blo 1112627 2511935 := bstep (se 1 (by rfl) ⟨1883951, by rfl⟩ : syracuseStep 2511935 = 3767903) B3767903
theorem B6345809 : Blo 1112627 6345809 := bstep (se 2 (by rfl) ⟨2379678, by rfl⟩ : syracuseStep 6345809 = 4759357) B4759357
theorem B57889889 : Blo 1112627 57889889 := bstep (se 2 (by rfl) ⟨21708708, by rfl⟩ : syracuseStep 57889889 = 43417417) B43417417
theorem B6018155 : Blo 1112627 6018155 := bstep (se 1 (by rfl) ⟨4513616, by rfl⟩ : syracuseStep 6018155 = 9027233) B9027233
theorem B3757751 : Blo 1112627 3757751 := bstep (se 1 (by rfl) ⟨2818313, by rfl⟩ : syracuseStep 3757751 = 5636627) B5636627
theorem B2119841 : Blo 1112627 2119841 := bstep (se 2 (by rfl) ⟨794940, by rfl⟩ : syracuseStep 2119841 = 1589881) B1589881
theorem B3168553 : Blo 1112627 3168553 := bstep (se 2 (by rfl) ⟨1188207, by rfl⟩ : syracuseStep 3168553 = 2376415) B2376415
theorem B7133629 : Blo 1112627 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B5364157 : Blo 1112627 5364157 := bstep (se 3 (by rfl) ⟨1005779, by rfl⟩ : syracuseStep 5364157 = 2011559) B2011559
theorem B30497579 : Blo 1112627 30497579 := bstep (se 1 (by rfl) ⟨22873184, by rfl⟩ : syracuseStep 30497579 = 45746369) B45746369
theorem B3758939 : Blo 1112627 3758939 := bstep (se 1 (by rfl) ⟨2819204, by rfl⟩ : syracuseStep 3758939 = 5638409) B5638409
theorem B6347767 : Blo 1112627 6347767 := bstep (se 1 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 6347767 = 9521651) B9521651
theorem B17161283 : Blo 1112627 17161283 := bstep (se 1 (by rfl) ⟨12870962, by rfl⟩ : syracuseStep 17161283 = 25741925) B25741925
theorem B4021433 : Blo 1112627 4021433 := bstep (se 2 (by rfl) ⟨1508037, by rfl⟩ : syracuseStep 4021433 = 3016075) B3016075
theorem B3759695 : Blo 1112627 3759695 := bstep (se 1 (by rfl) ⟨2819771, by rfl⟩ : syracuseStep 3759695 = 5639543) B5639543
theorem B3759803 : Blo 1112627 3759803 := bstep (se 1 (by rfl) ⟨2819852, by rfl⟩ : syracuseStep 3759803 = 5639705) B5639705
theorem B3170171 : Blo 1112627 3170171 := bstep (se 1 (by rfl) ⟨2377628, by rfl⟩ : syracuseStep 3170171 = 4755257) B4755257
theorem B2679599 : Blo 1112627 2679599 := bstep (se 1 (by rfl) ⟨2009699, by rfl⟩ : syracuseStep 2679599 = 4019399) B4019399
theorem B9037163 : Blo 1112627 9037163 := bstep (se 1 (by rfl) ⟨6777872, by rfl⟩ : syracuseStep 9037163 = 13555745) B13555745
theorem B3007997 : Blo 1112627 3007997 := bstep (se 3 (by rfl) ⟨563999, by rfl⟩ : syracuseStep 3007997 = 1127999) B1127999
theorem B3761747 : Blo 1112627 3761747 := bstep (se 1 (by rfl) ⟨2821310, by rfl⟩ : syracuseStep 3761747 = 5642621) B5642621
theorem B3762017 : Blo 1112627 3762017 := bstep (se 2 (by rfl) ⟨1410756, by rfl⟩ : syracuseStep 3762017 = 2821513) B2821513
theorem B16050257 : Blo 1112627 16050257 := bstep (se 2 (by rfl) ⟨6018846, by rfl⟩ : syracuseStep 16050257 = 12037693) B12037693
theorem B6350957 : Blo 1112627 6350957 := bstep (se 3 (by rfl) ⟨1190804, by rfl⟩ : syracuseStep 6350957 = 2381609) B2381609
theorem B8022361 : Blo 1112627 8022361 := bstep (se 2 (by rfl) ⟨3008385, by rfl⟩ : syracuseStep 8022361 = 6016771) B6016771
theorem B3172699 : Blo 1112627 3172699 := bstep (se 1 (by rfl) ⟨2379524, by rfl⟩ : syracuseStep 3172699 = 4759049) B4759049
theorem B3172871 : Blo 1112627 3172871 := bstep (se 1 (by rfl) ⟨2379653, by rfl⟩ : syracuseStep 3172871 = 4759307) B4759307
theorem B1337887 : Blo 1112627 1337887 := bstep (se 1 (by rfl) ⟨1003415, by rfl⟩ : syracuseStep 1337887 = 2006831) B2006831
theorem B3762719 : Blo 1112627 3762719 := bstep (se 1 (by rfl) ⟨2822039, by rfl⟩ : syracuseStep 3762719 = 5644079) B5644079
theorem B3566263 : Blo 1112627 3566263 := bstep (se 1 (by rfl) ⟨2674697, by rfl⟩ : syracuseStep 3566263 = 5349395) B5349395
theorem B3566713 : Blo 1112627 3566713 := bstep (se 2 (by rfl) ⟨1337517, by rfl⟩ : syracuseStep 3566713 = 2675035) B2675035
theorem B3173519 : Blo 1112627 3173519 := bstep (se 1 (by rfl) ⟨2380139, by rfl⟩ : syracuseStep 3173519 = 4760279) B4760279
theorem B19066265 : Blo 1112627 19066265 := bstep (se 2 (by rfl) ⟨7149849, by rfl⟩ : syracuseStep 19066265 = 14299699) B14299699
theorem B2715049 : Blo 1112627 2715049 := bstep (se 2 (by rfl) ⟨1018143, by rfl⟩ : syracuseStep 2715049 = 2036287) B2036287
theorem B2715535 : Blo 1112627 2715535 := bstep (se 1 (by rfl) ⟨2036651, by rfl⟩ : syracuseStep 2715535 = 4073303) B4073303
theorem B3764123 : Blo 1112627 3764123 := bstep (se 1 (by rfl) ⟨2823092, by rfl⟩ : syracuseStep 3764123 = 5646185) B5646185
theorem B7139447 : Blo 1112627 7139447 := bstep (se 1 (by rfl) ⟨5354585, by rfl⟩ : syracuseStep 7139447 = 10709171) B10709171
theorem B1503847 : Blo 1112627 1503847 := bstep (se 1 (by rfl) ⟨1127885, by rfl⟩ : syracuseStep 1503847 = 2255771) B2255771
theorem B7139987 : Blo 1112627 7139987 := bstep (se 1 (by rfl) ⟨5354990, by rfl⟩ : syracuseStep 7139987 = 10709981) B10709981
theorem B7631507 : Blo 1112627 7631507 := bstep (se 1 (by rfl) ⟨5723630, by rfl⟩ : syracuseStep 7631507 = 11447261) B11447261
theorem B3175433 : Blo 1112627 3175433 := bstep (se 2 (by rfl) ⟨1190787, by rfl⟩ : syracuseStep 3175433 = 2381575) B2381575
theorem B3765257 : Blo 1112627 3765257 := bstep (se 2 (by rfl) ⟨1411971, by rfl⟩ : syracuseStep 3765257 = 2823943) B2823943
theorem B3765311 : Blo 1112627 3765311 := bstep (se 1 (by rfl) ⟨2823983, by rfl⟩ : syracuseStep 3765311 = 5647967) B5647967
theorem B24802949 : Blo 1112627 24802949 := bstep (se 4 (by rfl) ⟨2325276, by rfl⟩ : syracuseStep 24802949 = 4650553) B4650553
theorem B16053947 : Blo 1112627 16053947 := bstep (se 1 (by rfl) ⟨12040460, by rfl⟩ : syracuseStep 16053947 = 24080921) B24080921
theorem B1669001 : Blo 1112627 1669001 := bstep (se 2 (by rfl) ⟨625875, by rfl⟩ : syracuseStep 1669001 = 1251751) B1251751
theorem B4224905 : Blo 1112627 4224905 := bstep (se 2 (by rfl) ⟨1584339, by rfl⟩ : syracuseStep 4224905 = 3168679) B3168679
theorem B1669103 : Blo 1112627 1669103 := bstep (se 1 (by rfl) ⟨1251827, by rfl⟩ : syracuseStep 1669103 = 2503655) B2503655
theorem B9664595 : Blo 1112627 9664595 := bstep (se 1 (by rfl) ⟨7248446, by rfl⟩ : syracuseStep 9664595 = 14496893) B14496893
theorem B3438697 : Blo 1112627 3438697 := bstep (se 2 (by rfl) ⟨1289511, by rfl⟩ : syracuseStep 3438697 = 2579023) B2579023
theorem B8026283 : Blo 1112627 8026283 := bstep (se 1 (by rfl) ⟨6019712, by rfl⟩ : syracuseStep 8026283 = 12039425) B12039425
theorem B7141547 : Blo 1112627 7141547 := bstep (se 1 (by rfl) ⟨5356160, by rfl⟩ : syracuseStep 7141547 = 10712321) B10712321
theorem B1669355 : Blo 1112627 1669355 := bstep (se 1 (by rfl) ⟨1252016, by rfl⟩ : syracuseStep 1669355 = 2504033) B2504033
theorem B1669415 : Blo 1112627 1669415 := bstep (se 1 (by rfl) ⟨1252061, by rfl⟩ : syracuseStep 1669415 = 2504123) B2504123
theorem B12712301 : Blo 1112627 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B1669499 : Blo 1112627 1669499 := bstep (se 1 (by rfl) ⟨1252124, by rfl⟩ : syracuseStep 1669499 = 2504249) B2504249
theorem B3570095 : Blo 1112627 3570095 := bstep (se 1 (by rfl) ⟨2677571, by rfl⟩ : syracuseStep 3570095 = 5355143) B5355143
theorem B1669769 : Blo 1112627 1669769 := bstep (se 2 (by rfl) ⟨626163, by rfl⟩ : syracuseStep 1669769 = 1252327) B1252327
theorem B5798623 : Blo 1112627 5798623 := bstep (se 1 (by rfl) ⟨4348967, by rfl⟩ : syracuseStep 5798623 = 8697935) B8697935
theorem B1669943 : Blo 1112627 1669943 := bstep (se 1 (by rfl) ⟨1252457, by rfl⟩ : syracuseStep 1669943 = 2504915) B2504915
theorem B1112923 : Blo 1112627 1112923 := bstep (se 1 (by rfl) ⟨834692, by rfl⟩ : syracuseStep 1112923 = 1669385) B1669385
theorem B1669979 : Blo 1112627 1669979 := bstep (se 1 (by rfl) ⟨1252484, by rfl⟩ : syracuseStep 1669979 = 2504969) B2504969
theorem B8452997 : Blo 1112627 8452997 := bstep (se 4 (by rfl) ⟨792468, by rfl⟩ : syracuseStep 8452997 = 1584937) B1584937
theorem B2816927 : Blo 1112627 2816927 := bstep (se 1 (by rfl) ⟨2112695, by rfl⟩ : syracuseStep 2816927 = 4225391) B4225391
theorem B1112991 : Blo 1112627 1112991 := bstep (se 1 (by rfl) ⟨834743, by rfl⟩ : syracuseStep 1112991 = 1669487) B1669487
theorem B1670123 : Blo 1112627 1670123 := bstep (se 1 (by rfl) ⟨1252592, by rfl⟩ : syracuseStep 1670123 = 2505185) B2505185
theorem B1113135 : Blo 1112627 1113135 := bstep (se 1 (by rfl) ⟨834851, by rfl⟩ : syracuseStep 1113135 = 1669703) B1669703
theorem B1113159 : Blo 1112627 1113159 := bstep (se 1 (by rfl) ⟨834869, by rfl⟩ : syracuseStep 1113159 = 1669739) B1669739
theorem B8027207 : Blo 1112627 8027207 := bstep (se 1 (by rfl) ⟨6020405, by rfl⟩ : syracuseStep 8027207 = 12040811) B12040811
theorem B1670327 : Blo 1112627 1670327 := bstep (se 1 (by rfl) ⟨1252745, by rfl⟩ : syracuseStep 1670327 = 2505491) B2505491
theorem B1113311 : Blo 1112627 1113311 := bstep (se 1 (by rfl) ⟨834983, by rfl⟩ : syracuseStep 1113311 = 1669967) B1669967
theorem B1670567 : Blo 1112627 1670567 := bstep (se 1 (by rfl) ⟨1252925, by rfl⟩ : syracuseStep 1670567 = 2505851) B2505851
theorem B1113575 : Blo 1112627 1113575 := bstep (se 1 (by rfl) ⟨835181, by rfl⟩ : syracuseStep 1113575 = 1670363) B1670363
theorem B1670651 : Blo 1112627 1670651 := bstep (se 1 (by rfl) ⟨1252988, by rfl⟩ : syracuseStep 1670651 = 2505977) B2505977
theorem B4226651 : Blo 1112627 4226651 := bstep (se 1 (by rfl) ⟨3169988, by rfl⟩ : syracuseStep 4226651 = 6339977) B6339977
theorem B1113691 : Blo 1112627 1113691 := bstep (se 1 (by rfl) ⟨835268, by rfl⟩ : syracuseStep 1113691 = 1670537) B1670537
theorem B1670747 : Blo 1112627 1670747 := bstep (se 1 (by rfl) ⟨1253060, by rfl⟩ : syracuseStep 1670747 = 2506121) B2506121
theorem B1670831 : Blo 1112627 1670831 := bstep (se 1 (by rfl) ⟨1253123, by rfl⟩ : syracuseStep 1670831 = 2506247) B2506247
theorem B7143137 : Blo 1112627 7143137 := bstep (se 2 (by rfl) ⟨2678676, by rfl⟩ : syracuseStep 7143137 = 5357353) B5357353
theorem B5635817 : Blo 1112627 5635817 := bstep (se 2 (by rfl) ⟨2113431, by rfl⟩ : syracuseStep 5635817 = 4226863) B4226863
theorem B1670951 : Blo 1112627 1670951 := bstep (se 1 (by rfl) ⟨1253213, by rfl⟩ : syracuseStep 1670951 = 2506427) B2506427
theorem B3768119 : Blo 1112627 3768119 := bstep (se 1 (by rfl) ⟨2826089, by rfl⟩ : syracuseStep 3768119 = 5652179) B5652179
theorem B1113927 : Blo 1112627 1113927 := bstep (se 1 (by rfl) ⟨835445, by rfl⟩ : syracuseStep 1113927 = 1670891) B1670891
theorem B1671035 : Blo 1112627 1671035 := bstep (se 1 (by rfl) ⟨1253276, by rfl⟩ : syracuseStep 1671035 = 2506553) B2506553
theorem B1114079 : Blo 1112627 1114079 := bstep (se 1 (by rfl) ⟨835559, by rfl⟩ : syracuseStep 1114079 = 1671119) B1671119
theorem B1671359 : Blo 1112627 1671359 := bstep (se 1 (by rfl) ⟨1253519, by rfl⟩ : syracuseStep 1671359 = 2507039) B2507039
theorem B1114303 : Blo 1112627 1114303 := bstep (se 1 (by rfl) ⟨835727, by rfl⟩ : syracuseStep 1114303 = 1671455) B1671455
theorem B1114319 : Blo 1112627 1114319 := bstep (se 1 (by rfl) ⟨835739, by rfl⟩ : syracuseStep 1114319 = 1671479) B1671479
theorem B1114367 : Blo 1112627 1114367 := bstep (se 1 (by rfl) ⟨835775, by rfl⟩ : syracuseStep 1114367 = 1671551) B1671551
theorem B1114415 : Blo 1112627 1114415 := bstep (se 1 (by rfl) ⟨835811, by rfl⟩ : syracuseStep 1114415 = 1671623) B1671623
theorem B3309871 : Blo 1112627 3309871 := bstep (se 1 (by rfl) ⟨2482403, by rfl⟩ : syracuseStep 3309871 = 4964807) B4964807
theorem B1114651 : Blo 1112627 1114651 := bstep (se 1 (by rfl) ⟨835988, by rfl⟩ : syracuseStep 1114651 = 1671977) B1671977
theorem B1114655 : Blo 1112627 1114655 := bstep (se 1 (by rfl) ⟨835991, by rfl⟩ : syracuseStep 1114655 = 1671983) B1671983
theorem B1671785 : Blo 1112627 1671785 := bstep (se 2 (by rfl) ⟨626919, by rfl⟩ : syracuseStep 1671785 = 1253839) B1253839
theorem B1671791 : Blo 1112627 1671791 := bstep (se 1 (by rfl) ⟨1253843, by rfl⟩ : syracuseStep 1671791 = 2507687) B2507687
theorem B1114735 : Blo 1112627 1114735 := bstep (se 1 (by rfl) ⟨836051, by rfl⟩ : syracuseStep 1114735 = 1672103) B1672103
theorem B1114791 : Blo 1112627 1114791 := bstep (se 1 (by rfl) ⟨836093, by rfl⟩ : syracuseStep 1114791 = 1672187) B1672187
theorem B1114831 : Blo 1112627 1114831 := bstep (se 1 (by rfl) ⟨836123, by rfl⟩ : syracuseStep 1114831 = 1672247) B1672247
theorem B1114911 : Blo 1112627 1114911 := bstep (se 1 (by rfl) ⟨836183, by rfl⟩ : syracuseStep 1114911 = 1672367) B1672367
theorem B5636951 : Blo 1112627 5636951 := bstep (se 1 (by rfl) ⟨4227713, by rfl⟩ : syracuseStep 5636951 = 8455427) B8455427
theorem B8586071 : Blo 1112627 8586071 := bstep (se 1 (by rfl) ⟨6439553, by rfl⟩ : syracuseStep 8586071 = 12879107) B12879107
theorem B1115183 : Blo 1112627 1115183 := bstep (se 1 (by rfl) ⟨836387, by rfl⟩ : syracuseStep 1115183 = 1672775) B1672775
theorem B1115247 : Blo 1112627 1115247 := bstep (se 1 (by rfl) ⟨836435, by rfl⟩ : syracuseStep 1115247 = 1672871) B1672871
theorem B1115303 : Blo 1112627 1115303 := bstep (se 1 (by rfl) ⟨836477, by rfl⟩ : syracuseStep 1115303 = 1672955) B1672955
theorem B12059837 : Blo 1112627 12059837 := bstep (se 3 (by rfl) ⟨2261219, by rfl⟩ : syracuseStep 12059837 = 4522439) B4522439
theorem B1115327 : Blo 1112627 1115327 := bstep (se 1 (by rfl) ⟨836495, by rfl⟩ : syracuseStep 1115327 = 1672991) B1672991
theorem B12715217 : Blo 1112627 12715217 := bstep (se 2 (by rfl) ⟨4768206, by rfl⟩ : syracuseStep 12715217 = 9536413) B9536413
theorem B4228307 : Blo 1112627 4228307 := bstep (se 1 (by rfl) ⟨3171230, by rfl⟩ : syracuseStep 4228307 = 6342461) B6342461
theorem B1672415 : Blo 1112627 1672415 := bstep (se 1 (by rfl) ⟨1254311, by rfl⟩ : syracuseStep 1672415 = 2508623) B2508623
theorem B1115359 : Blo 1112627 1115359 := bstep (se 1 (by rfl) ⟨836519, by rfl⟩ : syracuseStep 1115359 = 1673039) B1673039
theorem B1672427 : Blo 1112627 1672427 := bstep (se 1 (by rfl) ⟨1254320, by rfl⟩ : syracuseStep 1672427 = 2508641) B2508641
theorem B1115439 : Blo 1112627 1115439 := bstep (se 1 (by rfl) ⟨836579, by rfl⟩ : syracuseStep 1115439 = 1673159) B1673159
theorem B1115675 : Blo 1112627 1115675 := bstep (se 1 (by rfl) ⟨836756, by rfl⟩ : syracuseStep 1115675 = 1673513) B1673513
theorem B1115679 : Blo 1112627 1115679 := bstep (se 1 (by rfl) ⟨836759, by rfl⟩ : syracuseStep 1115679 = 1673519) B1673519
theorem B1672811 : Blo 1112627 1672811 := bstep (se 1 (by rfl) ⟨1254608, by rfl⟩ : syracuseStep 1672811 = 2509217) B2509217
theorem B16058047 : Blo 1112627 16058047 := bstep (se 1 (by rfl) ⟨12043535, by rfl⟩ : syracuseStep 16058047 = 24087071) B24087071
theorem B1672895 : Blo 1112627 1672895 := bstep (se 1 (by rfl) ⟨1254671, by rfl⟩ : syracuseStep 1672895 = 2509343) B2509343
theorem B1115839 : Blo 1112627 1115839 := bstep (se 1 (by rfl) ⟨836879, by rfl⟩ : syracuseStep 1115839 = 1673759) B1673759
theorem B20350685 : Blo 1112627 20350685 := bstep (se 3 (by rfl) ⟨3815753, by rfl⟩ : syracuseStep 20350685 = 7631507) B7631507
theorem B1673081 : Blo 1112627 1673081 := bstep (se 2 (by rfl) ⟨627405, by rfl⟩ : syracuseStep 1673081 = 1254811) B1254811
theorem B1116095 : Blo 1112627 1116095 := bstep (se 1 (by rfl) ⟨837071, by rfl⟩ : syracuseStep 1116095 = 1674143) B1674143
theorem B1116127 : Blo 1112627 1116127 := bstep (se 1 (by rfl) ⟨837095, by rfl⟩ : syracuseStep 1116127 = 1674191) B1674191
theorem B4229111 : Blo 1112627 4229111 := bstep (se 1 (by rfl) ⟨3171833, by rfl⟩ : syracuseStep 4229111 = 6343667) B6343667
theorem B1116187 : Blo 1112627 1116187 := bstep (se 1 (by rfl) ⟨837140, by rfl⟩ : syracuseStep 1116187 = 1674281) B1674281
theorem B1116191 : Blo 1112627 1116191 := bstep (se 1 (by rfl) ⟨837143, by rfl⟩ : syracuseStep 1116191 = 1674287) B1674287
theorem B1116207 : Blo 1112627 1116207 := bstep (se 1 (by rfl) ⟨837155, by rfl⟩ : syracuseStep 1116207 = 1674311) B1674311
theorem B7145597 : Blo 1112627 7145597 := bstep (se 3 (by rfl) ⟨1339799, by rfl⟩ : syracuseStep 7145597 = 2679599) B2679599
theorem B1116383 : Blo 1112627 1116383 := bstep (se 1 (by rfl) ⟨837287, by rfl⟩ : syracuseStep 1116383 = 1674575) B1674575
theorem B2820379 : Blo 1112627 2820379 := bstep (se 1 (by rfl) ⟨2115284, by rfl⟩ : syracuseStep 2820379 = 4230569) B4230569
theorem B1116443 : Blo 1112627 1116443 := bstep (se 1 (by rfl) ⟨837332, by rfl⟩ : syracuseStep 1116443 = 1674665) B1674665
theorem B1116543 : Blo 1112627 1116543 := bstep (se 1 (by rfl) ⟨837407, by rfl⟩ : syracuseStep 1116543 = 1674815) B1674815
theorem B10717703 : Blo 1112627 10717703 := bstep (se 1 (by rfl) ⟨8038277, by rfl⟩ : syracuseStep 10717703 = 16076555) B16076555
theorem B77302295 : Blo 1112627 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B2820703 : Blo 1112627 2820703 := bstep (se 1 (by rfl) ⟨2115527, by rfl⟩ : syracuseStep 2820703 = 4231055) B4231055
theorem B1673831 : Blo 1112627 1673831 := bstep (se 1 (by rfl) ⟨1255373, by rfl⟩ : syracuseStep 1673831 = 2510747) B2510747
theorem B1674023 : Blo 1112627 1674023 := bstep (se 1 (by rfl) ⟨1255517, by rfl⟩ : syracuseStep 1674023 = 2511035) B2511035
theorem B4230083 : Blo 1112627 4230083 := bstep (se 1 (by rfl) ⟨3172562, by rfl⟩ : syracuseStep 4230083 = 6345125) B6345125
theorem B4230251 : Blo 1112627 4230251 := bstep (se 1 (by rfl) ⟨3172688, by rfl⟩ : syracuseStep 4230251 = 6345377) B6345377
theorem B1674347 : Blo 1112627 1674347 := bstep (se 1 (by rfl) ⟨1255760, by rfl⟩ : syracuseStep 1674347 = 2511521) B2511521
theorem B4230265 : Blo 1112627 4230265 := bstep (se 2 (by rfl) ⟨1586349, by rfl⟩ : syracuseStep 4230265 = 3172699) B3172699
theorem B2821331 : Blo 1112627 2821331 := bstep (se 1 (by rfl) ⟨2115998, by rfl⟩ : syracuseStep 2821331 = 4231997) B4231997
theorem B1903963 : Blo 1112627 1903963 := bstep (se 1 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 1903963 = 2855945) B2855945
theorem B1674587 : Blo 1112627 1674587 := bstep (se 1 (by rfl) ⟨1255940, by rfl⟩ : syracuseStep 1674587 = 2511881) B2511881
theorem B1674617 : Blo 1112627 1674617 := bstep (se 2 (by rfl) ⟨627981, by rfl⟩ : syracuseStep 1674617 = 1255963) B1255963
theorem B1674623 : Blo 1112627 1674623 := bstep (se 1 (by rfl) ⟨1255967, by rfl⟩ : syracuseStep 1674623 = 2511935) B2511935
theorem B4230539 : Blo 1112627 4230539 := bstep (se 1 (by rfl) ⟨3172904, by rfl⟩ : syracuseStep 4230539 = 6345809) B6345809
theorem B4755017 : Blo 1112627 4755017 := bstep (se 2 (by rfl) ⟨1783131, by rfl⟩ : syracuseStep 4755017 = 3566263) B3566263
theorem B1413227 : Blo 1112627 1413227 := bstep (se 1 (by rfl) ⟨1059920, by rfl⟩ : syracuseStep 1413227 = 2119841) B2119841
theorem B4755617 : Blo 1112627 4755617 := bstep (se 2 (by rfl) ⟨1783356, by rfl⟩ : syracuseStep 4755617 = 3566713) B3566713
theorem B5640515 : Blo 1112627 5640515 := bstep (se 1 (by rfl) ⟨4230386, by rfl⟩ : syracuseStep 5640515 = 8460773) B8460773
theorem B12063127 : Blo 1112627 12063127 := bstep (se 1 (by rfl) ⟨9047345, by rfl⟩ : syracuseStep 12063127 = 18094691) B18094691
theorem B11440855 : Blo 1112627 11440855 := bstep (se 1 (by rfl) ⟨8580641, by rfl⟩ : syracuseStep 11440855 = 17161283) B17161283
theorem B6034571 : Blo 1112627 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B2823599 : Blo 1112627 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B2823923 : Blo 1112627 2823923 := bstep (se 1 (by rfl) ⟨2117942, by rfl⟩ : syracuseStep 2823923 = 4235885) B4235885
theorem B28579715 : Blo 1112627 28579715 := bstep (se 1 (by rfl) ⟨21434786, by rfl⟩ : syracuseStep 28579715 = 42869573) B42869573
theorem B1906591 : Blo 1112627 1906591 := bstep (se 1 (by rfl) ⟨1429943, by rfl⟩ : syracuseStep 1906591 = 2859887) B2859887
theorem B14260333 : Blo 1112627 14260333 := bstep (se 3 (by rfl) ⟨2673812, by rfl⟩ : syracuseStep 14260333 = 5347625) B5347625
theorem B2005129 : Blo 1112627 2005129 := bstep (se 2 (by rfl) ⟨751923, by rfl⟩ : syracuseStep 2005129 = 1503847) B1503847
theorem B5085337 : Blo 1112627 5085337 := bstep (se 2 (by rfl) ⟨1907001, by rfl⟩ : syracuseStep 5085337 = 3814003) B3814003
theorem B9050399 : Blo 1112627 9050399 := bstep (se 1 (by rfl) ⟨6787799, by rfl⟩ : syracuseStep 9050399 = 13575599) B13575599
theorem B2005331 : Blo 1112627 2005331 := bstep (se 1 (by rfl) ⟨1503998, by rfl⟩ : syracuseStep 2005331 = 3007997) B3007997
theorem B1251931 : Blo 1112627 1251931 := bstep (se 1 (by rfl) ⟨938948, by rfl⟩ : syracuseStep 1251931 = 1877897) B1877897
theorem B4233971 : Blo 1112627 4233971 := bstep (se 1 (by rfl) ⟨3175478, by rfl⟩ : syracuseStep 4233971 = 6350957) B6350957
theorem B1252219 : Blo 1112627 1252219 := bstep (se 1 (by rfl) ⟨939164, by rfl⟩ : syracuseStep 1252219 = 1878329) B1878329
theorem B2825543 : Blo 1112627 2825543 := bstep (se 1 (by rfl) ⟨2119157, by rfl⟩ : syracuseStep 2825543 = 4238315) B4238315
theorem B1252975 : Blo 1112627 1252975 := bstep (se 1 (by rfl) ⟨939731, by rfl⟩ : syracuseStep 1252975 = 1879463) B1879463
theorem B1253083 : Blo 1112627 1253083 := bstep (se 1 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 1253083 = 1879625) B1879625
theorem B4759631 : Blo 1112627 4759631 := bstep (se 1 (by rfl) ⟨3569723, by rfl⟩ : syracuseStep 4759631 = 7139447) B7139447
theorem B9511127 : Blo 1112627 9511127 := bstep (se 1 (by rfl) ⟨7133345, by rfl⟩ : syracuseStep 9511127 = 14266691) B14266691
theorem B8462717 : Blo 1112627 8462717 := bstep (se 3 (by rfl) ⟨1586759, by rfl⟩ : syracuseStep 8462717 = 3173519) B3173519
theorem B4759991 : Blo 1112627 4759991 := bstep (se 1 (by rfl) ⟨3569993, by rfl⟩ : syracuseStep 4759991 = 7139987) B7139987
theorem B9511505 : Blo 1112627 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B7152209 : Blo 1112627 7152209 := bstep (se 2 (by rfl) ⟨2682078, by rfl⟩ : syracuseStep 7152209 = 5364157) B5364157
theorem B1254055 : Blo 1112627 1254055 := bstep (se 1 (by rfl) ⟨940541, by rfl⟩ : syracuseStep 1254055 = 1881083) B1881083
theorem B1254343 : Blo 1112627 1254343 := bstep (se 1 (by rfl) ⟨940757, by rfl⟩ : syracuseStep 1254343 = 1881515) B1881515
theorem B5710907 : Blo 1112627 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B11609227 : Blo 1112627 11609227 := bstep (se 1 (by rfl) ⟨8706920, by rfl⟩ : syracuseStep 11609227 = 17413841) B17413841
theorem B1254703 : Blo 1112627 1254703 := bstep (se 1 (by rfl) ⟨941027, by rfl⟩ : syracuseStep 1254703 = 1882055) B1882055
theorem B8463689 : Blo 1112627 8463689 := bstep (se 2 (by rfl) ⟨3173883, by rfl⟩ : syracuseStep 8463689 = 6347767) B6347767
theorem B5350855 : Blo 1112627 5350855 := bstep (se 1 (by rfl) ⟨4013141, by rfl⟩ : syracuseStep 5350855 = 8026283) B8026283
theorem B4761031 : Blo 1112627 4761031 := bstep (se 1 (by rfl) ⟨3570773, by rfl⟩ : syracuseStep 4761031 = 7141547) B7141547
theorem B1255207 : Blo 1112627 1255207 := bstep (se 1 (by rfl) ⟨941405, by rfl⟩ : syracuseStep 1255207 = 1882811) B1882811
theorem B1877951 : Blo 1112627 1877951 := bstep (se 1 (by rfl) ⟨1408463, by rfl⟩ : syracuseStep 1877951 = 2816927) B2816927
theorem B5351471 : Blo 1112627 5351471 := bstep (se 1 (by rfl) ⟨4013603, by rfl⟩ : syracuseStep 5351471 = 8027207) B8027207
theorem B4762091 : Blo 1112627 4762091 := bstep (se 1 (by rfl) ⟨3571568, by rfl⟩ : syracuseStep 4762091 = 7143137) B7143137
theorem B4827863 : Blo 1112627 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B1880057 : Blo 1112627 1880057 := bstep (se 2 (by rfl) ⟨705021, by rfl⟩ : syracuseStep 1880057 = 1410043) B1410043
theorem B4763681 : Blo 1112627 4763681 := bstep (se 2 (by rfl) ⟨1786380, by rfl⟩ : syracuseStep 4763681 = 3572761) B3572761
theorem B1585279 : Blo 1112627 1585279 := bstep (se 1 (by rfl) ⟨1188959, by rfl⟩ : syracuseStep 1585279 = 2377919) B2377919
theorem B4239499 : Blo 1112627 4239499 := bstep (se 1 (by rfl) ⟨3179624, by rfl⟩ : syracuseStep 4239499 = 6359249) B6359249
theorem B1880327 : Blo 1112627 1880327 := bstep (se 1 (by rfl) ⟨1410245, by rfl⟩ : syracuseStep 1880327 = 2820491) B2820491
theorem B8467091 : Blo 1112627 8467091 := bstep (se 1 (by rfl) ⟨6350318, by rfl⟩ : syracuseStep 8467091 = 12700637) B12700637
theorem B2503673 : Blo 1112627 2503673 := bstep (se 2 (by rfl) ⟨938877, by rfl⟩ : syracuseStep 2503673 = 1877755) B1877755
theorem B2503763 : Blo 1112627 2503763 := bstep (se 1 (by rfl) ⟨1877822, by rfl⟩ : syracuseStep 2503763 = 3755645) B3755645
theorem B2503943 : Blo 1112627 2503943 := bstep (se 1 (by rfl) ⟨1877957, by rfl⟩ : syracuseStep 2503943 = 3755915) B3755915
theorem B1881353 : Blo 1112627 1881353 := bstep (se 2 (by rfl) ⟨705507, by rfl⟩ : syracuseStep 1881353 = 1411015) B1411015
theorem B1881407 : Blo 1112627 1881407 := bstep (se 1 (by rfl) ⟨1411055, by rfl⟩ : syracuseStep 1881407 = 2822111) B2822111
theorem B2504303 : Blo 1112627 2504303 := bstep (se 1 (by rfl) ⟨1878227, by rfl⟩ : syracuseStep 2504303 = 3756455) B3756455
theorem B1881839 : Blo 1112627 1881839 := bstep (se 1 (by rfl) ⟨1411379, by rfl⟩ : syracuseStep 1881839 = 2822759) B2822759
theorem B10696481 : Blo 1112627 10696481 := bstep (se 2 (by rfl) ⟨4011180, by rfl⟩ : syracuseStep 10696481 = 8022361) B8022361
theorem B6338519 : Blo 1112627 6338519 := bstep (se 1 (by rfl) ⟨4753889, by rfl⟩ : syracuseStep 6338519 = 9507779) B9507779
theorem B4012103 : Blo 1112627 4012103 := bstep (se 1 (by rfl) ⟨3009077, by rfl⟩ : syracuseStep 4012103 = 6018155) B6018155
theorem B1882183 : Blo 1112627 1882183 := bstep (se 1 (by rfl) ⟨1411637, by rfl⟩ : syracuseStep 1882183 = 2823275) B2823275
theorem B10729543 : Blo 1112627 10729543 := bstep (se 1 (by rfl) ⟨8047157, by rfl⟩ : syracuseStep 10729543 = 16094315) B16094315
theorem B2505167 : Blo 1112627 2505167 := bstep (se 1 (by rfl) ⟨1878875, by rfl⟩ : syracuseStep 2505167 = 3757751) B3757751
theorem B2505257 : Blo 1112627 2505257 := bstep (se 2 (by rfl) ⟨939471, by rfl⟩ : syracuseStep 2505257 = 1878943) B1878943
theorem B6339293 : Blo 1112627 6339293 := bstep (se 3 (by rfl) ⟨1188617, by rfl⟩ : syracuseStep 6339293 = 2377235) B2377235
theorem B1883047 : Blo 1112627 1883047 := bstep (se 1 (by rfl) ⟨1412285, by rfl⟩ : syracuseStep 1883047 = 2824571) B2824571
theorem B2505833 : Blo 1112627 2505833 := bstep (se 2 (by rfl) ⟨939687, by rfl⟩ : syracuseStep 2505833 = 1879375) B1879375
theorem B20331719 : Blo 1112627 20331719 := bstep (se 1 (by rfl) ⟨15248789, by rfl⟩ : syracuseStep 20331719 = 30497579) B30497579
theorem B3620065 : Blo 1112627 3620065 := bstep (se 2 (by rfl) ⟨1357524, by rfl⟩ : syracuseStep 3620065 = 2715049) B2715049
theorem B2505959 : Blo 1112627 2505959 := bstep (se 1 (by rfl) ⟨1879469, by rfl⟩ : syracuseStep 2505959 = 3758939) B3758939
theorem B42908939 : Blo 1112627 42908939 := bstep (se 1 (by rfl) ⟨32181704, by rfl⟩ : syracuseStep 42908939 = 64363409) B64363409
theorem B2506463 : Blo 1112627 2506463 := bstep (se 1 (by rfl) ⟨1879847, by rfl⟩ : syracuseStep 2506463 = 3759695) B3759695
theorem B2506535 : Blo 1112627 2506535 := bstep (se 1 (by rfl) ⟨1879901, by rfl⟩ : syracuseStep 2506535 = 3759803) B3759803
theorem B3620713 : Blo 1112627 3620713 := bstep (se 2 (by rfl) ⟨1357767, by rfl⟩ : syracuseStep 3620713 = 2715535) B2715535
theorem B2113447 : Blo 1112627 2113447 := bstep (se 1 (by rfl) ⟨1585085, by rfl⟩ : syracuseStep 2113447 = 3170171) B3170171
theorem B12042715 : Blo 1112627 12042715 := bstep (se 1 (by rfl) ⟨9032036, by rfl⟩ : syracuseStep 12042715 = 18064073) B18064073
theorem B2507561 : Blo 1112627 2507561 := bstep (se 2 (by rfl) ⟨940335, by rfl⟩ : syracuseStep 2507561 = 1880671) B1880671
theorem B2507831 : Blo 1112627 2507831 := bstep (se 1 (by rfl) ⟨1880873, by rfl⟩ : syracuseStep 2507831 = 3761747) B3761747
theorem B9520253 : Blo 1112627 9520253 := bstep (se 3 (by rfl) ⟨1785047, by rfl⟩ : syracuseStep 9520253 = 3570095) B3570095
theorem B2508011 : Blo 1112627 2508011 := bstep (se 1 (by rfl) ⟨1881008, by rfl⟩ : syracuseStep 2508011 = 3762017) B3762017
theorem B19318019 : Blo 1112627 19318019 := bstep (se 1 (by rfl) ⟨14488514, by rfl⟩ : syracuseStep 19318019 = 28977029) B28977029
theorem B10700171 : Blo 1112627 10700171 := bstep (se 1 (by rfl) ⟨8025128, by rfl⟩ : syracuseStep 10700171 = 16050257) B16050257
theorem B2115247 : Blo 1112627 2115247 := bstep (se 1 (by rfl) ⟨1586435, by rfl⟩ : syracuseStep 2115247 = 3172871) B3172871
theorem B2508479 : Blo 1112627 2508479 := bstep (se 1 (by rfl) ⟨1881359, by rfl⟩ : syracuseStep 2508479 = 3762719) B3762719
theorem B36095705 : Blo 1112627 36095705 := bstep (se 2 (by rfl) ⟨13535889, by rfl⟩ : syracuseStep 36095705 = 27071779) B27071779
theorem B2509415 : Blo 1112627 2509415 := bstep (se 1 (by rfl) ⟨1882061, by rfl⟩ : syracuseStep 2509415 = 3764123) B3764123
theorem B2673449 : Blo 1112627 2673449 := bstep (se 2 (by rfl) ⟨1002543, by rfl⟩ : syracuseStep 2673449 = 2005087) B2005087
theorem B14273455 : Blo 1112627 14273455 := bstep (se 1 (by rfl) ⟨10705091, by rfl⟩ : syracuseStep 14273455 = 21410183) B21410183
theorem B2509793 : Blo 1112627 2509793 := bstep (se 2 (by rfl) ⟨941172, by rfl⟩ : syracuseStep 2509793 = 1882345) B1882345
theorem B2673659 : Blo 1112627 2673659 := bstep (se 1 (by rfl) ⟨2005244, by rfl⟩ : syracuseStep 2673659 = 4010489) B4010489
theorem B2116955 : Blo 1112627 2116955 := bstep (se 1 (by rfl) ⟨1587716, by rfl⟩ : syracuseStep 2116955 = 3175433) B3175433
theorem B2510171 : Blo 1112627 2510171 := bstep (se 1 (by rfl) ⟨1882628, by rfl⟩ : syracuseStep 2510171 = 3765257) B3765257
theorem B5361005 : Blo 1112627 5361005 := bstep (se 3 (by rfl) ⟨1005188, by rfl⟩ : syracuseStep 5361005 = 2010377) B2010377
theorem B2510207 : Blo 1112627 2510207 := bstep (se 1 (by rfl) ⟨1882655, by rfl⟩ : syracuseStep 2510207 = 3765311) B3765311
theorem B16535299 : Blo 1112627 16535299 := bstep (se 1 (by rfl) ⟨12401474, by rfl⟩ : syracuseStep 16535299 = 24802949) B24802949
theorem B10702631 : Blo 1112627 10702631 := bstep (se 1 (by rfl) ⟨8026973, by rfl⟩ : syracuseStep 10702631 = 16053947) B16053947
theorem B5361659 : Blo 1112627 5361659 := bstep (se 1 (by rfl) ⟨4021244, by rfl⟩ : syracuseStep 5361659 = 8042489) B8042489
theorem B6443063 : Blo 1112627 6443063 := bstep (se 1 (by rfl) ⟨4832297, by rfl⟩ : syracuseStep 6443063 = 9664595) B9664595
theorem B8474867 : Blo 1112627 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B19288709 : Blo 1112627 19288709 := bstep (se 4 (by rfl) ⟨1808316, by rfl⟩ : syracuseStep 19288709 = 3616633) B3616633
theorem B3757211 : Blo 1112627 3757211 := bstep (se 1 (by rfl) ⟨2817908, by rfl⟩ : syracuseStep 3757211 = 5635817) B5635817
theorem B2512079 : Blo 1112627 2512079 := bstep (se 1 (by rfl) ⟨1884059, by rfl⟩ : syracuseStep 2512079 = 3768119) B3768119
theorem B2118953 : Blo 1112627 2118953 := bstep (se 2 (by rfl) ⟨794607, by rfl⟩ : syracuseStep 2118953 = 1589215) B1589215
theorem B2512169 : Blo 1112627 2512169 := bstep (se 2 (by rfl) ⟨942063, by rfl⟩ : syracuseStep 2512169 = 1884127) B1884127
theorem B2413999 : Blo 1112627 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B2512367 : Blo 1112627 2512367 := bstep (se 1 (by rfl) ⟨1884275, by rfl⟩ : syracuseStep 2512367 = 3768551) B3768551
theorem B6772571 : Blo 1112627 6772571 := bstep (se 1 (by rfl) ⟨5079428, by rfl⟩ : syracuseStep 6772571 = 10158857) B10158857
theorem B2119583 : Blo 1112627 2119583 := bstep (se 1 (by rfl) ⟨1589687, by rfl⟩ : syracuseStep 2119583 = 3179375) B3179375
theorem B5364427 : Blo 1112627 5364427 := bstep (se 1 (by rfl) ⟨4023320, by rfl⟩ : syracuseStep 5364427 = 8046641) B8046641
theorem B6970835 : Blo 1112627 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B3169783 : Blo 1112627 3169783 := bstep (se 1 (by rfl) ⟨2377337, by rfl⟩ : syracuseStep 3169783 = 4754675) B4754675
theorem B2383481 : Blo 1112627 2383481 := bstep (se 2 (by rfl) ⟨893805, by rfl⟩ : syracuseStep 2383481 = 1787611) B1787611
theorem B20340467 : Blo 1112627 20340467 := bstep (se 1 (by rfl) ⟨15255350, by rfl⟩ : syracuseStep 20340467 = 30510701) B30510701
theorem B2416495 : Blo 1112627 2416495 := bstep (se 1 (by rfl) ⟨1812371, by rfl⟩ : syracuseStep 2416495 = 3624743) B3624743
theorem B7135397 : Blo 1112627 7135397 := bstep (se 4 (by rfl) ⟨668943, by rfl⟩ : syracuseStep 7135397 = 1337887) B1337887
theorem B3760667 : Blo 1112627 3760667 := bstep (se 1 (by rfl) ⟨2820500, by rfl⟩ : syracuseStep 3760667 = 5641001) B5641001
theorem B38593259 : Blo 1112627 38593259 := bstep (se 1 (by rfl) ⟨28944944, by rfl⟩ : syracuseStep 38593259 = 57889889) B57889889
theorem B34300907 : Blo 1112627 34300907 := bstep (se 1 (by rfl) ⟨25725680, by rfl⟩ : syracuseStep 34300907 = 51451361) B51451361
theorem B7234775 : Blo 1112627 7234775 := bstep (se 1 (by rfl) ⟨5426081, by rfl⟩ : syracuseStep 7234775 = 10852163) B10852163
theorem B2680955 : Blo 1112627 2680955 := bstep (se 1 (by rfl) ⟨2010716, by rfl⟩ : syracuseStep 2680955 = 4021433) B4021433
theorem B34760897 : Blo 1112627 34760897 := bstep (se 2 (by rfl) ⟨13035336, by rfl⟩ : syracuseStep 34760897 = 26070673) B26070673
theorem B3172745 : Blo 1112627 3172745 := bstep (se 2 (by rfl) ⟨1189779, by rfl⟩ : syracuseStep 3172745 = 2379559) B2379559
theorem B5729773 : Blo 1112627 5729773 := bstep (se 3 (by rfl) ⟨1074332, by rfl⟩ : syracuseStep 5729773 = 2148665) B2148665
theorem B6024775 : Blo 1112627 6024775 := bstep (se 1 (by rfl) ⟨4518581, by rfl⟩ : syracuseStep 6024775 = 9037163) B9037163
theorem B9532039 : Blo 1112627 9532039 := bstep (se 1 (by rfl) ⟨7149029, by rfl⟩ : syracuseStep 9532039 = 14298059) B14298059
theorem B3764987 : Blo 1112627 3764987 := bstep (se 1 (by rfl) ⟨2823740, by rfl⟩ : syracuseStep 3764987 = 5647481) B5647481
theorem B16053025 : Blo 1112627 16053025 := bstep (se 2 (by rfl) ⟨6019884, by rfl⟩ : syracuseStep 16053025 = 12039769) B12039769
theorem B3765149 : Blo 1112627 3765149 := bstep (se 3 (by rfl) ⟨705965, by rfl⟩ : syracuseStep 3765149 = 1411931) B1411931
theorem B12710843 : Blo 1112627 12710843 := bstep (se 1 (by rfl) ⟨9533132, by rfl⟩ : syracuseStep 12710843 = 19066265) B19066265
theorem B96367967 : Blo 1112627 96367967 := bstep (se 1 (by rfl) ⟨72275975, by rfl⟩ : syracuseStep 96367967 = 144551951) B144551951
theorem B4584929 : Blo 1112627 4584929 := bstep (se 2 (by rfl) ⟨1719348, by rfl⟩ : syracuseStep 4584929 = 3438697) B3438697
theorem B3765851 : Blo 1112627 3765851 := bstep (se 1 (by rfl) ⟨2824388, by rfl⟩ : syracuseStep 3765851 = 5648777) B5648777
theorem B4224737 : Blo 1112627 4224737 := bstep (se 2 (by rfl) ⟨1584276, by rfl⟩ : syracuseStep 4224737 = 3168553) B3168553
theorem B7731497 : Blo 1112627 7731497 := bstep (se 2 (by rfl) ⟨2899311, by rfl⟩ : syracuseStep 7731497 = 5798623) B5798623
theorem B1669583 : Blo 1112627 1669583 := bstep (se 1 (by rfl) ⟨1252187, by rfl⟩ : syracuseStep 1669583 = 2504375) B2504375
theorem B1669673 : Blo 1112627 1669673 := bstep (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) B1252255
theorem B1112667 : Blo 1112627 1112667 := bstep (se 1 (by rfl) ⟨834500, by rfl⟩ : syracuseStep 1112667 = 1669001) B1669001
theorem B2816603 : Blo 1112627 2816603 := bstep (se 1 (by rfl) ⟨2112452, by rfl⟩ : syracuseStep 2816603 = 4224905) B4224905
theorem B1112735 : Blo 1112627 1112735 := bstep (se 1 (by rfl) ⟨834551, by rfl⟩ : syracuseStep 1112735 = 1669103) B1669103
theorem B1669865 : Blo 1112627 1669865 := bstep (se 2 (by rfl) ⟨626199, by rfl⟩ : syracuseStep 1669865 = 1252399) B1252399
theorem B1112903 : Blo 1112627 1112903 := bstep (se 1 (by rfl) ⟨834677, by rfl⟩ : syracuseStep 1112903 = 1669355) B1669355
theorem B1112943 : Blo 1112627 1112943 := bstep (se 1 (by rfl) ⟨834707, by rfl⟩ : syracuseStep 1112943 = 1669415) B1669415
theorem B1112999 : Blo 1112627 1112999 := bstep (se 1 (by rfl) ⟨834749, by rfl⟩ : syracuseStep 1112999 = 1669499) B1669499
theorem B1113179 : Blo 1112627 1113179 := bstep (se 1 (by rfl) ⟨834884, by rfl⟩ : syracuseStep 1113179 = 1669769) B1669769
theorem B1670249 : Blo 1112627 1670249 := bstep (se 2 (by rfl) ⟨626343, by rfl⟩ : syracuseStep 1670249 = 1252687) B1252687
theorem B1113295 : Blo 1112627 1113295 := bstep (se 1 (by rfl) ⟨834971, by rfl⟩ : syracuseStep 1113295 = 1669943) B1669943
theorem B1113319 : Blo 1112627 1113319 := bstep (se 1 (by rfl) ⟨834989, by rfl⟩ : syracuseStep 1113319 = 1669979) B1669979
theorem B1670375 : Blo 1112627 1670375 := bstep (se 1 (by rfl) ⟨1252781, by rfl⟩ : syracuseStep 1670375 = 2505563) B2505563
theorem B5635331 : Blo 1112627 5635331 := bstep (se 1 (by rfl) ⟨4226498, by rfl⟩ : syracuseStep 5635331 = 8452997) B8452997
theorem B1113415 : Blo 1112627 1113415 := bstep (se 1 (by rfl) ⟨835061, by rfl⟩ : syracuseStep 1113415 = 1670123) B1670123
theorem B3177917 : Blo 1112627 3177917 := bstep (se 3 (by rfl) ⟨595859, by rfl⟩ : syracuseStep 3177917 = 1191719) B1191719
theorem B3767741 : Blo 1112627 3767741 := bstep (se 3 (by rfl) ⟨706451, by rfl⟩ : syracuseStep 3767741 = 1412903) B1412903
theorem B1113551 : Blo 1112627 1113551 := bstep (se 1 (by rfl) ⟨835163, by rfl⟩ : syracuseStep 1113551 = 1670327) B1670327
theorem B1113711 : Blo 1112627 1113711 := bstep (se 1 (by rfl) ⟨835283, by rfl⟩ : syracuseStep 1113711 = 1670567) B1670567
theorem B1113767 : Blo 1112627 1113767 := bstep (se 1 (by rfl) ⟨835325, by rfl⟩ : syracuseStep 1113767 = 1670651) B1670651
theorem B1670879 : Blo 1112627 1670879 := bstep (se 1 (by rfl) ⟨1253159, by rfl⟩ : syracuseStep 1670879 = 2506319) B2506319
theorem B2817767 : Blo 1112627 2817767 := bstep (se 1 (by rfl) ⟨2113325, by rfl⟩ : syracuseStep 2817767 = 4226651) B4226651
theorem B1113831 : Blo 1112627 1113831 := bstep (se 1 (by rfl) ⟨835373, by rfl⟩ : syracuseStep 1113831 = 1670747) B1670747
theorem B1670921 : Blo 1112627 1670921 := bstep (se 2 (by rfl) ⟨626595, by rfl⟩ : syracuseStep 1670921 = 1253191) B1253191
theorem B1113887 : Blo 1112627 1113887 := bstep (se 1 (by rfl) ⟨835415, by rfl⟩ : syracuseStep 1113887 = 1670831) B1670831
theorem B8453969 : Blo 1112627 8453969 := bstep (se 2 (by rfl) ⟨3170238, by rfl⟩ : syracuseStep 8453969 = 6340477) B6340477
theorem B1113967 : Blo 1112627 1113967 := bstep (se 1 (by rfl) ⟨835475, by rfl⟩ : syracuseStep 1113967 = 1670951) B1670951
theorem B1114023 : Blo 1112627 1114023 := bstep (se 1 (by rfl) ⟨835517, by rfl⟩ : syracuseStep 1114023 = 1671035) B1671035
theorem B1114239 : Blo 1112627 1114239 := bstep (se 1 (by rfl) ⟨835679, by rfl⟩ : syracuseStep 1114239 = 1671359) B1671359
theorem B3768605 : Blo 1112627 3768605 := bstep (se 3 (by rfl) ⟨706613, by rfl⟩ : syracuseStep 3768605 = 1413227) B1413227
theorem B1114523 : Blo 1112627 1114523 := bstep (se 1 (by rfl) ⟨835892, by rfl⟩ : syracuseStep 1114523 = 1671785) B1671785
theorem B1114527 : Blo 1112627 1114527 := bstep (se 1 (by rfl) ⟨835895, by rfl⟩ : syracuseStep 1114527 = 1671791) B1671791
theorem B1671707 : Blo 1112627 1671707 := bstep (se 1 (by rfl) ⟨1253780, by rfl⟩ : syracuseStep 1671707 = 2507561) B2507561
theorem B16056953 : Blo 1112627 16056953 := bstep (se 2 (by rfl) ⟨6021357, by rfl⟩ : syracuseStep 16056953 = 12042715) B12042715
theorem B1671887 : Blo 1112627 1671887 := bstep (se 1 (by rfl) ⟨1253915, by rfl⟩ : syracuseStep 1671887 = 2507831) B2507831
theorem B2818871 : Blo 1112627 2818871 := bstep (se 1 (by rfl) ⟨2114153, by rfl⟩ : syracuseStep 2818871 = 4228307) B4228307
theorem B1114943 : Blo 1112627 1114943 := bstep (se 1 (by rfl) ⟨836207, by rfl⟩ : syracuseStep 1114943 = 1672415) B1672415
theorem B1672007 : Blo 1112627 1672007 := bstep (se 1 (by rfl) ⟨1254005, by rfl⟩ : syracuseStep 1672007 = 2508011) B2508011
theorem B1114951 : Blo 1112627 1114951 := bstep (se 1 (by rfl) ⟨836213, by rfl⟩ : syracuseStep 1114951 = 1672427) B1672427
theorem B1672073 : Blo 1112627 1672073 := bstep (se 2 (by rfl) ⟨627027, by rfl⟩ : syracuseStep 1672073 = 1254055) B1254055
theorem B1115207 : Blo 1112627 1115207 := bstep (se 1 (by rfl) ⟨836405, by rfl⟩ : syracuseStep 1115207 = 1672811) B1672811
theorem B1672319 : Blo 1112627 1672319 := bstep (se 1 (by rfl) ⟨1254239, by rfl⟩ : syracuseStep 1672319 = 2508479) B2508479
theorem B1115263 : Blo 1112627 1115263 := bstep (se 1 (by rfl) ⟨836447, by rfl⟩ : syracuseStep 1115263 = 1672895) B1672895
theorem B13567123 : Blo 1112627 13567123 := bstep (se 1 (by rfl) ⟨10175342, by rfl⟩ : syracuseStep 13567123 = 20350685) B20350685
theorem B1115387 : Blo 1112627 1115387 := bstep (se 1 (by rfl) ⟨836540, by rfl⟩ : syracuseStep 1115387 = 1673081) B1673081
theorem B1672457 : Blo 1112627 1672457 := bstep (se 2 (by rfl) ⟨627171, by rfl⟩ : syracuseStep 1672457 = 1254343) B1254343
theorem B2819407 : Blo 1112627 2819407 := bstep (se 1 (by rfl) ⟨2114555, by rfl⟩ : syracuseStep 2819407 = 4229111) B4229111
theorem B7145135 : Blo 1112627 7145135 := bstep (se 1 (by rfl) ⟨5358851, by rfl⟩ : syracuseStep 7145135 = 10717703) B10717703
theorem B1672937 : Blo 1112627 1672937 := bstep (se 2 (by rfl) ⟨627351, by rfl⟩ : syracuseStep 1672937 = 1254703) B1254703
theorem B1672943 : Blo 1112627 1672943 := bstep (se 1 (by rfl) ⟨1254707, by rfl⟩ : syracuseStep 1672943 = 2509415) B2509415
theorem B1115887 : Blo 1112627 1115887 := bstep (se 1 (by rfl) ⟨836915, by rfl⟩ : syracuseStep 1115887 = 1673831) B1673831
theorem B1116015 : Blo 1112627 1116015 := bstep (se 1 (by rfl) ⟨837011, by rfl⟩ : syracuseStep 1116015 = 1674023) B1674023
theorem B2820055 : Blo 1112627 2820055 := bstep (se 1 (by rfl) ⟨2115041, by rfl⟩ : syracuseStep 2820055 = 4230083) B4230083
theorem B1673195 : Blo 1112627 1673195 := bstep (se 1 (by rfl) ⟨1254896, by rfl⟩ : syracuseStep 1673195 = 2509793) B2509793
theorem B2820167 : Blo 1112627 2820167 := bstep (se 1 (by rfl) ⟨2115125, by rfl⟩ : syracuseStep 2820167 = 4230251) B4230251
theorem B1116231 : Blo 1112627 1116231 := bstep (se 1 (by rfl) ⟨837173, by rfl⟩ : syracuseStep 1116231 = 1674347) B1674347
theorem B1673447 : Blo 1112627 1673447 := bstep (se 1 (by rfl) ⟨1255085, by rfl⟩ : syracuseStep 1673447 = 2510171) B2510171
theorem B1116391 : Blo 1112627 1116391 := bstep (se 1 (by rfl) ⟨837293, by rfl⟩ : syracuseStep 1116391 = 1674587) B1674587
theorem B2820329 : Blo 1112627 2820329 := bstep (se 2 (by rfl) ⟨1057623, by rfl⟩ : syracuseStep 2820329 = 2115247) B2115247
theorem B3574003 : Blo 1112627 3574003 := bstep (se 1 (by rfl) ⟨2680502, by rfl⟩ : syracuseStep 3574003 = 5361005) B5361005
theorem B1116411 : Blo 1112627 1116411 := bstep (se 1 (by rfl) ⟨837308, by rfl⟩ : syracuseStep 1116411 = 1674617) B1674617
theorem B1673471 : Blo 1112627 1673471 := bstep (se 1 (by rfl) ⟨1255103, by rfl⟩ : syracuseStep 1673471 = 2510207) B2510207
theorem B1116415 : Blo 1112627 1116415 := bstep (se 1 (by rfl) ⟨837311, by rfl⟩ : syracuseStep 1116415 = 1674623) B1674623
theorem B2820359 : Blo 1112627 2820359 := bstep (se 1 (by rfl) ⟨2115269, by rfl⟩ : syracuseStep 2820359 = 4230539) B4230539
theorem B1673609 : Blo 1112627 1673609 := bstep (se 2 (by rfl) ⟨627603, by rfl⟩ : syracuseStep 1673609 = 1255207) B1255207
theorem B3574439 : Blo 1112627 3574439 := bstep (se 1 (by rfl) ⟨2680829, by rfl⟩ : syracuseStep 3574439 = 5361659) B5361659
theorem B4295375 : Blo 1112627 4295375 := bstep (se 1 (by rfl) ⟨3221531, by rfl⟩ : syracuseStep 4295375 = 6443063) B6443063
theorem B51514717 : Blo 1112627 51514717 := bstep (se 3 (by rfl) ⟨9659009, by rfl⟩ : syracuseStep 51514717 = 19318019) B19318019
theorem B1674719 : Blo 1112627 1674719 := bstep (se 1 (by rfl) ⟨1256039, by rfl⟩ : syracuseStep 1674719 = 2512079) B2512079
theorem B1412635 : Blo 1112627 1412635 := bstep (se 1 (by rfl) ⟨1059476, by rfl⟩ : syracuseStep 1412635 = 2118953) B2118953
theorem B1674779 : Blo 1112627 1674779 := bstep (se 1 (by rfl) ⟨1256084, by rfl⟩ : syracuseStep 1674779 = 2512169) B2512169
theorem B1674911 : Blo 1112627 1674911 := bstep (se 1 (by rfl) ⟨1256183, by rfl⟩ : syracuseStep 1674911 = 2512367) B2512367
theorem B61017893 : Blo 1112627 61017893 := bstep (se 4 (by rfl) ⟨5720427, by rfl⟩ : syracuseStep 61017893 = 11440855) B11440855
theorem B1413055 : Blo 1112627 1413055 := bstep (se 1 (by rfl) ⟨1059791, by rfl⟩ : syracuseStep 1413055 = 2119583) B2119583
theorem B5640353 : Blo 1112627 5640353 := bstep (se 2 (by rfl) ⟨2115132, by rfl⟩ : syracuseStep 5640353 = 4230265) B4230265
theorem B6033599 : Blo 1112627 6033599 := bstep (se 1 (by rfl) ⟨4525199, by rfl⟩ : syracuseStep 6033599 = 9050399) B9050399
theorem B2822647 : Blo 1112627 2822647 := bstep (se 1 (by rfl) ⟨2116985, by rfl⟩ : syracuseStep 2822647 = 4233971) B4233971
theorem B7639697 : Blo 1112627 7639697 := bstep (se 2 (by rfl) ⟨2864886, by rfl⟩ : syracuseStep 7639697 = 5729773) B5729773
theorem B8033033 : Blo 1112627 8033033 := bstep (se 2 (by rfl) ⟨3012387, by rfl⟩ : syracuseStep 8033033 = 6024775) B6024775
theorem B4756931 : Blo 1112627 4756931 := bstep (se 1 (by rfl) ⟨3567698, by rfl⟩ : syracuseStep 4756931 = 7135397) B7135397
theorem B5641811 : Blo 1112627 5641811 := bstep (se 1 (by rfl) ⟨4231358, by rfl⟩ : syracuseStep 5641811 = 8462717) B8462717
theorem B25728839 : Blo 1112627 25728839 := bstep (se 1 (by rfl) ⟨19296629, by rfl⟩ : syracuseStep 25728839 = 38593259) B38593259
theorem B3807271 : Blo 1112627 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B20617325 : Blo 1112627 20617325 := bstep (se 3 (by rfl) ⟨3865748, by rfl⟩ : syracuseStep 20617325 = 7731497) B7731497
theorem B4823183 : Blo 1112627 4823183 := bstep (se 1 (by rfl) ⟨3617387, by rfl⟩ : syracuseStep 4823183 = 7234775) B7234775
theorem B5642459 : Blo 1112627 5642459 := bstep (se 1 (by rfl) ⟨4231844, by rfl⟩ : syracuseStep 5642459 = 8463689) B8463689
theorem B5347549 : Blo 1112627 5347549 := bstep (se 3 (by rfl) ⟨1002665, by rfl⟩ : syracuseStep 5347549 = 2005331) B2005331
theorem B21404033 : Blo 1112627 21404033 := bstep (se 2 (by rfl) ⟨8026512, by rfl⟩ : syracuseStep 21404033 = 16053025) B16053025
theorem B1251967 : Blo 1112627 1251967 := bstep (se 1 (by rfl) ⟨938975, by rfl⟩ : syracuseStep 1251967 = 1877951) B1877951
theorem B23173931 : Blo 1112627 23173931 := bstep (se 1 (by rfl) ⟨17380448, by rfl⟩ : syracuseStep 23173931 = 34760897) B34760897
theorem B3218665 : Blo 1112627 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B1253371 : Blo 1112627 1253371 := bstep (se 1 (by rfl) ⟨940028, by rfl⟩ : syracuseStep 1253371 = 1880057) B1880057
theorem B19013777 : Blo 1112627 19013777 := bstep (se 2 (by rfl) ⟨7130166, by rfl⟩ : syracuseStep 19013777 = 14260333) B14260333
theorem B1253551 : Blo 1112627 1253551 := bstep (se 1 (by rfl) ⟨940163, by rfl⟩ : syracuseStep 1253551 = 1880327) B1880327
theorem B5644727 : Blo 1112627 5644727 := bstep (se 1 (by rfl) ⟨4233545, by rfl⟩ : syracuseStep 5644727 = 8467091) B8467091
theorem B1254235 : Blo 1112627 1254235 := bstep (se 1 (by rfl) ⟨940676, by rfl⟩ : syracuseStep 1254235 = 1881353) B1881353
theorem B1254271 : Blo 1112627 1254271 := bstep (se 1 (by rfl) ⟨940703, by rfl⟩ : syracuseStep 1254271 = 1881407) B1881407
theorem B5645213 : Blo 1112627 5645213 := bstep (se 3 (by rfl) ⟨1058477, by rfl⟩ : syracuseStep 5645213 = 2116955) B2116955
theorem B7152569 : Blo 1112627 7152569 := bstep (se 2 (by rfl) ⟨2682213, by rfl⟩ : syracuseStep 7152569 = 5364427) B5364427
theorem B1254559 : Blo 1112627 1254559 := bstep (se 1 (by rfl) ⟨940919, by rfl⟩ : syracuseStep 1254559 = 1881839) B1881839
theorem B4826753 : Blo 1112627 4826753 := bstep (se 2 (by rfl) ⟨1810032, by rfl⟩ : syracuseStep 4826753 = 3620065) B3620065
theorem B1877735 : Blo 1112627 1877735 := bstep (se 1 (by rfl) ⟨1408301, by rfl⟩ : syracuseStep 1877735 = 2816603) B2816603
theorem B4827617 : Blo 1112627 4827617 := bstep (se 2 (by rfl) ⟨1810356, by rfl⟩ : syracuseStep 4827617 = 3620713) B3620713
theorem B3221993 : Blo 1112627 3221993 := bstep (se 2 (by rfl) ⟨1208247, by rfl⟩ : syracuseStep 3221993 = 2416495) B2416495
theorem B1878511 : Blo 1112627 1878511 := bstep (se 1 (by rfl) ⟨1408883, by rfl⟩ : syracuseStep 1878511 = 2817767) B2817767
theorem B8039891 : Blo 1112627 8039891 := bstep (se 1 (by rfl) ⟨6029918, by rfl⟩ : syracuseStep 8039891 = 12059837) B12059837
theorem B24063803 : Blo 1112627 24063803 := bstep (se 1 (by rfl) ⟨18047852, by rfl⟩ : syracuseStep 24063803 = 36095705) B36095705
theorem B4763731 : Blo 1112627 4763731 := bstep (se 1 (by rfl) ⟨3572798, by rfl⟩ : syracuseStep 4763731 = 7145597) B7145597
theorem B1782299 : Blo 1112627 1782299 := bstep (se 1 (by rfl) ⟨1336724, by rfl⟩ : syracuseStep 1782299 = 2673449) B2673449
theorem B1880887 : Blo 1112627 1880887 := bstep (se 1 (by rfl) ⟨1410665, by rfl⟩ : syracuseStep 1880887 = 2821331) B2821331
theorem B21410729 : Blo 1112627 21410729 := bstep (se 2 (by rfl) ⟨8029023, by rfl⟩ : syracuseStep 21410729 = 16058047) B16058047
theorem B5649911 : Blo 1112627 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B12859139 : Blo 1112627 12859139 := bstep (se 1 (by rfl) ⟨9644354, by rfl⟩ : syracuseStep 12859139 = 19288709) B19288709
theorem B2504807 : Blo 1112627 2504807 := bstep (se 1 (by rfl) ⟨1878605, by rfl⟩ : syracuseStep 2504807 = 3757211) B3757211
theorem B1882399 : Blo 1112627 1882399 := bstep (se 1 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 1882399 = 2823599) B2823599
theorem B1882615 : Blo 1112627 1882615 := bstep (se 1 (by rfl) ⟨1411961, by rfl⟩ : syracuseStep 1882615 = 2823923) B2823923
theorem B19053143 : Blo 1112627 19053143 := bstep (se 1 (by rfl) ⟨14289857, by rfl⟩ : syracuseStep 19053143 = 28579715) B28579715
theorem B2538617 : Blo 1112627 2538617 := bstep (se 2 (by rfl) ⟨951981, by rfl⟩ : syracuseStep 2538617 = 1903963) B1903963
theorem B1883695 : Blo 1112627 1883695 := bstep (se 1 (by rfl) ⟨1412771, by rfl⟩ : syracuseStep 1883695 = 2825543) B2825543
theorem B48905909 : Blo 1112627 48905909 := bstep (se 5 (by rfl) ⟨2292464, by rfl⟩ : syracuseStep 48905909 = 4584929) B4584929
theorem B1588987 : Blo 1112627 1588987 := bstep (se 1 (by rfl) ⟨1191740, by rfl⟩ : syracuseStep 1588987 = 2383481) B2383481
theorem B6340751 : Blo 1112627 6340751 := bstep (se 1 (by rfl) ⟨4755563, by rfl⟩ : syracuseStep 6340751 = 9511127) B9511127
theorem B2113705 : Blo 1112627 2113705 := bstep (se 2 (by rfl) ⟨792639, by rfl⟩ : syracuseStep 2113705 = 1585279) B1585279
theorem B5652665 : Blo 1112627 5652665 := bstep (se 2 (by rfl) ⟨2119749, by rfl⟩ : syracuseStep 5652665 = 4239499) B4239499
theorem B10698941 : Blo 1112627 10698941 := bstep (se 3 (by rfl) ⟨2006051, by rfl⟩ : syracuseStep 10698941 = 4012103) B4012103
theorem B2507111 : Blo 1112627 2507111 := bstep (se 1 (by rfl) ⟨1880333, by rfl⟩ : syracuseStep 2507111 = 3760667) B3760667
theorem B6341003 : Blo 1112627 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B4768139 : Blo 1112627 4768139 := bstep (se 1 (by rfl) ⟨3576104, by rfl⟩ : syracuseStep 4768139 = 7152209) B7152209
theorem B61915877 : Blo 1112627 61915877 := bstep (se 4 (by rfl) ⟨5804613, by rfl⟩ : syracuseStep 61915877 = 11609227) B11609227
theorem B1787303 : Blo 1112627 1787303 := bstep (se 1 (by rfl) ⟨1340477, by rfl⟩ : syracuseStep 1787303 = 2680955) B2680955
theorem B2115163 : Blo 1112627 2115163 := bstep (se 1 (by rfl) ⟨1586372, by rfl⟩ : syracuseStep 2115163 = 3172745) B3172745
theorem B2542121 : Blo 1112627 2542121 := bstep (se 2 (by rfl) ⟨953295, by rfl⟩ : syracuseStep 2542121 = 1906591) B1906591
theorem B7129757 : Blo 1112627 7129757 := bstep (se 3 (by rfl) ⟨1336829, by rfl⟩ : syracuseStep 7129757 = 2673659) B2673659
theorem B2509577 : Blo 1112627 2509577 := bstep (se 2 (by rfl) ⟨941091, by rfl⟩ : syracuseStep 2509577 = 1882183) B1882183
theorem B14306057 : Blo 1112627 14306057 := bstep (se 2 (by rfl) ⟨5364771, by rfl⟩ : syracuseStep 14306057 = 10729543) B10729543
theorem B2673505 : Blo 1112627 2673505 := bstep (se 2 (by rfl) ⟨1002564, by rfl⟩ : syracuseStep 2673505 = 2005129) B2005129
theorem B2509991 : Blo 1112627 2509991 := bstep (se 1 (by rfl) ⟨1882493, by rfl⟩ : syracuseStep 2509991 = 3764987) B3764987
theorem B2510099 : Blo 1112627 2510099 := bstep (se 1 (by rfl) ⟨1882574, by rfl⟩ : syracuseStep 2510099 = 3765149) B3765149
theorem B8473895 : Blo 1112627 8473895 := bstep (se 1 (by rfl) ⟨6355421, by rfl⟩ : syracuseStep 8473895 = 12710843) B12710843
theorem B64245311 : Blo 1112627 64245311 := bstep (se 1 (by rfl) ⟨48183983, by rfl⟩ : syracuseStep 64245311 = 96367967) B96367967
theorem B2510567 : Blo 1112627 2510567 := bstep (se 1 (by rfl) ⟨1882925, by rfl⟩ : syracuseStep 2510567 = 3765851) B3765851
theorem B7130987 : Blo 1112627 7130987 := bstep (se 1 (by rfl) ⟨5348240, by rfl⟩ : syracuseStep 7130987 = 10696481) B10696481
theorem B2510729 : Blo 1112627 2510729 := bstep (se 2 (by rfl) ⟨941523, by rfl⟩ : syracuseStep 2510729 = 1883047) B1883047
theorem B13554479 : Blo 1112627 13554479 := bstep (se 1 (by rfl) ⟨10165859, by rfl⟩ : syracuseStep 13554479 = 20331719) B20331719
theorem B3756887 : Blo 1112627 3756887 := bstep (se 1 (by rfl) ⟨2817665, by rfl⟩ : syracuseStep 3756887 = 5635331) B5635331
theorem B2118611 : Blo 1112627 2118611 := bstep (se 1 (by rfl) ⟨1588958, by rfl⟩ : syracuseStep 2118611 = 3177917) B3177917
theorem B2511827 : Blo 1112627 2511827 := bstep (se 1 (by rfl) ⟨1883870, by rfl⟩ : syracuseStep 2511827 = 3767741) B3767741
theorem B4413161 : Blo 1112627 4413161 := bstep (se 2 (by rfl) ⟨1654935, by rfl⟩ : syracuseStep 4413161 = 3309871) B3309871
theorem B3757967 : Blo 1112627 3757967 := bstep (se 1 (by rfl) ⟨2818475, by rfl⟩ : syracuseStep 3757967 = 5636951) B5636951
theorem B5724047 : Blo 1112627 5724047 := bstep (se 1 (by rfl) ⟨4293035, by rfl⟩ : syracuseStep 5724047 = 8586071) B8586071
theorem B6346835 : Blo 1112627 6346835 := bstep (se 1 (by rfl) ⟨4760126, by rfl⟩ : syracuseStep 6346835 = 9520253) B9520253
theorem B8476811 : Blo 1112627 8476811 := bstep (se 1 (by rfl) ⟨6357608, by rfl⟩ : syracuseStep 8476811 = 12715217) B12715217
theorem B7133447 : Blo 1112627 7133447 := bstep (se 1 (by rfl) ⟨5350085, by rfl⟩ : syracuseStep 7133447 = 10700171) B10700171
theorem B51534863 : Blo 1112627 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B7134473 : Blo 1112627 7134473 := bstep (se 2 (by rfl) ⟨2675427, by rfl⟩ : syracuseStep 7134473 = 5350855) B5350855
theorem B6348041 : Blo 1112627 6348041 := bstep (se 2 (by rfl) ⟨2380515, by rfl⟩ : syracuseStep 6348041 = 4761031) B4761031
theorem B3170011 : Blo 1112627 3170011 := bstep (se 1 (by rfl) ⟨2377508, by rfl⟩ : syracuseStep 3170011 = 4755017) B4755017
theorem B3170411 : Blo 1112627 3170411 := bstep (se 1 (by rfl) ⟨2377808, by rfl⟩ : syracuseStep 3170411 = 4755617) B4755617
theorem B3760343 : Blo 1112627 3760343 := bstep (se 1 (by rfl) ⟨2820257, by rfl⟩ : syracuseStep 3760343 = 5640515) B5640515
theorem B3760505 : Blo 1112627 3760505 := bstep (se 2 (by rfl) ⟨1410189, by rfl⟩ : syracuseStep 3760505 = 2820379) B2820379
theorem B4023047 : Blo 1112627 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B3760937 : Blo 1112627 3760937 := bstep (se 2 (by rfl) ⟨1410351, by rfl⟩ : syracuseStep 3760937 = 2820703) B2820703
theorem B4515047 : Blo 1112627 4515047 := bstep (se 1 (by rfl) ⟨3386285, by rfl⟩ : syracuseStep 4515047 = 6772571) B6772571
theorem B19031273 : Blo 1112627 19031273 := bstep (se 2 (by rfl) ⟨7136727, by rfl⟩ : syracuseStep 19031273 = 14273455) B14273455
theorem B4647223 : Blo 1112627 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B22047065 : Blo 1112627 22047065 := bstep (se 2 (by rfl) ⟨8267649, by rfl⟩ : syracuseStep 22047065 = 16535299) B16535299
theorem B13560311 : Blo 1112627 13560311 := bstep (se 1 (by rfl) ⟨10170233, by rfl⟩ : syracuseStep 13560311 = 20340467) B20340467
theorem B3173087 : Blo 1112627 3173087 := bstep (se 1 (by rfl) ⟨2379815, by rfl⟩ : syracuseStep 3173087 = 4759631) B4759631
theorem B3173327 : Blo 1112627 3173327 := bstep (se 1 (by rfl) ⟨2379995, by rfl⟩ : syracuseStep 3173327 = 4759991) B4759991
theorem B16084169 : Blo 1112627 16084169 := bstep (se 2 (by rfl) ⟨6031563, by rfl⟩ : syracuseStep 16084169 = 12063127) B12063127
theorem B22867271 : Blo 1112627 22867271 := bstep (se 1 (by rfl) ⟨17150453, by rfl⟩ : syracuseStep 22867271 = 34300907) B34300907
theorem B12709385 : Blo 1112627 12709385 := bstep (se 2 (by rfl) ⟨4766019, by rfl⟩ : syracuseStep 12709385 = 9532039) B9532039
theorem B3567647 : Blo 1112627 3567647 := bstep (se 1 (by rfl) ⟨2675735, by rfl⟩ : syracuseStep 3567647 = 5351471) B5351471
theorem B3174727 : Blo 1112627 3174727 := bstep (se 1 (by rfl) ⟨2381045, by rfl⟩ : syracuseStep 3174727 = 4762091) B4762091
theorem B12874301 : Blo 1112627 12874301 := bstep (se 3 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 12874301 = 4827863) B4827863
theorem B3175787 : Blo 1112627 3175787 := bstep (se 1 (by rfl) ⟨2381840, by rfl⟩ : syracuseStep 3175787 = 4763681) B4763681
theorem B6780449 : Blo 1112627 6780449 := bstep (se 2 (by rfl) ⟨2542668, by rfl⟩ : syracuseStep 6780449 = 5085337) B5085337
theorem B1669115 : Blo 1112627 1669115 := bstep (se 1 (by rfl) ⟨1251836, by rfl⟩ : syracuseStep 1669115 = 2503673) B2503673
theorem B1669175 : Blo 1112627 1669175 := bstep (se 1 (by rfl) ⟨1251881, by rfl⟩ : syracuseStep 1669175 = 2503763) B2503763
theorem B1669241 : Blo 1112627 1669241 := bstep (se 2 (by rfl) ⟨625965, by rfl⟩ : syracuseStep 1669241 = 1251931) B1251931
theorem B1669295 : Blo 1112627 1669295 := bstep (se 1 (by rfl) ⟨1251971, by rfl⟩ : syracuseStep 1669295 = 2503943) B2503943
theorem B1669535 : Blo 1112627 1669535 := bstep (se 1 (by rfl) ⟨1252151, by rfl⟩ : syracuseStep 1669535 = 2504303) B2504303
theorem B2816491 : Blo 1112627 2816491 := bstep (se 1 (by rfl) ⟨2112368, by rfl⟩ : syracuseStep 2816491 = 4224737) B4224737
theorem B1669625 : Blo 1112627 1669625 := bstep (se 2 (by rfl) ⟨626109, by rfl⟩ : syracuseStep 1669625 = 1252219) B1252219
theorem B4225679 : Blo 1112627 4225679 := bstep (se 1 (by rfl) ⟨3169259, by rfl⟩ : syracuseStep 4225679 = 6338519) B6338519
theorem B1113055 : Blo 1112627 1113055 := bstep (se 1 (by rfl) ⟨834791, by rfl⟩ : syracuseStep 1113055 = 1669583) B1669583
theorem B1670111 : Blo 1112627 1670111 := bstep (se 1 (by rfl) ⟨1252583, by rfl⟩ : syracuseStep 1670111 = 2505167) B2505167
theorem B1113115 : Blo 1112627 1113115 := bstep (se 1 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 1113115 = 1669673) B1669673
theorem B1670171 : Blo 1112627 1670171 := bstep (se 1 (by rfl) ⟨1252628, by rfl⟩ : syracuseStep 1670171 = 2505257) B2505257
theorem B4226195 : Blo 1112627 4226195 := bstep (se 1 (by rfl) ⟨3169646, by rfl⟩ : syracuseStep 4226195 = 6339293) B6339293
theorem B1113243 : Blo 1112627 1113243 := bstep (se 1 (by rfl) ⟨834932, by rfl⟩ : syracuseStep 1113243 = 1669865) B1669865
theorem B4226377 : Blo 1112627 4226377 := bstep (se 2 (by rfl) ⟨1584891, by rfl⟩ : syracuseStep 4226377 = 3169783) B3169783
theorem B1113499 : Blo 1112627 1113499 := bstep (se 1 (by rfl) ⟨835124, by rfl⟩ : syracuseStep 1113499 = 1670249) B1670249
theorem B1670555 : Blo 1112627 1670555 := bstep (se 1 (by rfl) ⟨1252916, by rfl⟩ : syracuseStep 1670555 = 2505833) B2505833
theorem B28540349 : Blo 1112627 28540349 := bstep (se 3 (by rfl) ⟨5351315, by rfl⟩ : syracuseStep 28540349 = 10702631) B10702631
theorem B1670633 : Blo 1112627 1670633 := bstep (se 2 (by rfl) ⟨626487, by rfl⟩ : syracuseStep 1670633 = 1252975) B1252975
theorem B1113583 : Blo 1112627 1113583 := bstep (se 1 (by rfl) ⟨835187, by rfl⟩ : syracuseStep 1113583 = 1670375) B1670375
theorem B1670639 : Blo 1112627 1670639 := bstep (se 1 (by rfl) ⟨1252979, by rfl⟩ : syracuseStep 1670639 = 2505959) B2505959
theorem B28605959 : Blo 1112627 28605959 := bstep (se 1 (by rfl) ⟨21454469, by rfl⟩ : syracuseStep 28605959 = 42908939) B42908939
theorem B1670777 : Blo 1112627 1670777 := bstep (se 2 (by rfl) ⟨626541, by rfl⟩ : syracuseStep 1670777 = 1253083) B1253083
theorem B1113919 : Blo 1112627 1113919 := bstep (se 1 (by rfl) ⟨835439, by rfl⟩ : syracuseStep 1113919 = 1670879) B1670879
theorem B1670975 : Blo 1112627 1670975 := bstep (se 1 (by rfl) ⟨1253231, by rfl⟩ : syracuseStep 1670975 = 2506463) B2506463
theorem B1113947 : Blo 1112627 1113947 := bstep (se 1 (by rfl) ⟨835460, by rfl⟩ : syracuseStep 1113947 = 1670921) B1670921
theorem B1671023 : Blo 1112627 1671023 := bstep (se 1 (by rfl) ⟨1253267, by rfl⟩ : syracuseStep 1671023 = 2506535) B2506535
theorem B2817929 : Blo 1112627 2817929 := bstep (se 2 (by rfl) ⟨1056723, by rfl⟩ : syracuseStep 2817929 = 2113447) B2113447
theorem B5635979 : Blo 1112627 5635979 := bstep (se 1 (by rfl) ⟨4226984, by rfl⟩ : syracuseStep 5635979 = 8453969) B8453969
theorem B4227167 : Blo 1112627 4227167 := bstep (se 1 (by rfl) ⟨3170375, by rfl⟩ : syracuseStep 4227167 = 6340751) B6340751
theorem B3768443 : Blo 1112627 3768443 := bstep (se 1 (by rfl) ⟨2826332, by rfl⟩ : syracuseStep 3768443 = 5652665) B5652665
theorem B2818273 : Blo 1112627 2818273 := bstep (se 2 (by rfl) ⟨1056852, by rfl⟩ : syracuseStep 2818273 = 2113705) B2113705
theorem B1671401 : Blo 1112627 1671401 := bstep (se 2 (by rfl) ⟨626775, by rfl⟩ : syracuseStep 1671401 = 1253551) B1253551
theorem B1671407 : Blo 1112627 1671407 := bstep (se 1 (by rfl) ⟨1253555, by rfl⟩ : syracuseStep 1671407 = 2507111) B2507111
theorem B4227335 : Blo 1112627 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B3178759 : Blo 1112627 3178759 := bstep (se 1 (by rfl) ⟨2384069, by rfl⟩ : syracuseStep 3178759 = 4768139) B4768139
theorem B1114471 : Blo 1112627 1114471 := bstep (se 1 (by rfl) ⟨835853, by rfl⟩ : syracuseStep 1114471 = 1671707) B1671707
theorem B1114591 : Blo 1112627 1114591 := bstep (se 1 (by rfl) ⟨835943, by rfl⟩ : syracuseStep 1114591 = 1671887) B1671887
theorem B1114671 : Blo 1112627 1114671 := bstep (se 1 (by rfl) ⟨836003, by rfl⟩ : syracuseStep 1114671 = 1672007) B1672007
theorem B1114715 : Blo 1112627 1114715 := bstep (se 1 (by rfl) ⟨836036, by rfl⟩ : syracuseStep 1114715 = 1672073) B1672073
theorem B1114879 : Blo 1112627 1114879 := bstep (se 1 (by rfl) ⟨836159, by rfl⟩ : syracuseStep 1114879 = 1672319) B1672319
theorem B1114971 : Blo 1112627 1114971 := bstep (se 1 (by rfl) ⟨836228, by rfl⟩ : syracuseStep 1114971 = 1672457) B1672457
theorem B1672313 : Blo 1112627 1672313 := bstep (se 2 (by rfl) ⟨627117, by rfl⟩ : syracuseStep 1672313 = 1254235) B1254235
theorem B1115291 : Blo 1112627 1115291 := bstep (se 1 (by rfl) ⟨836468, by rfl⟩ : syracuseStep 1115291 = 1672937) B1672937
theorem B1115295 : Blo 1112627 1115295 := bstep (se 1 (by rfl) ⟨836471, by rfl⟩ : syracuseStep 1115295 = 1672943) B1672943
theorem B1672361 : Blo 1112627 1672361 := bstep (se 2 (by rfl) ⟨627135, by rfl⟩ : syracuseStep 1672361 = 1254271) B1254271
theorem B1115463 : Blo 1112627 1115463 := bstep (se 1 (by rfl) ⟨836597, by rfl⟩ : syracuseStep 1115463 = 1673195) B1673195
theorem B1115631 : Blo 1112627 1115631 := bstep (se 1 (by rfl) ⟨836723, by rfl⟩ : syracuseStep 1115631 = 1673447) B1673447
theorem B1115647 : Blo 1112627 1115647 := bstep (se 1 (by rfl) ⟨836735, by rfl⟩ : syracuseStep 1115647 = 1673471) B1673471
theorem B18089497 : Blo 1112627 18089497 := bstep (se 2 (by rfl) ⟨6783561, by rfl⟩ : syracuseStep 18089497 = 13567123) B13567123
theorem B1672745 : Blo 1112627 1672745 := bstep (se 2 (by rfl) ⟨627279, by rfl⟩ : syracuseStep 1672745 = 1254559) B1254559
theorem B1115739 : Blo 1112627 1115739 := bstep (se 1 (by rfl) ⟨836804, by rfl⟩ : syracuseStep 1115739 = 1673609) B1673609
theorem B4753171 : Blo 1112627 4753171 := bstep (se 1 (by rfl) ⟨3564878, by rfl⟩ : syracuseStep 4753171 = 7129757) B7129757
theorem B1673051 : Blo 1112627 1673051 := bstep (se 1 (by rfl) ⟨1254788, by rfl⟩ : syracuseStep 1673051 = 2509577) B2509577
theorem B9537371 : Blo 1112627 9537371 := bstep (se 1 (by rfl) ⟨7153028, by rfl⟩ : syracuseStep 9537371 = 14306057) B14306057
theorem B1673327 : Blo 1112627 1673327 := bstep (se 1 (by rfl) ⟨1254995, by rfl⟩ : syracuseStep 1673327 = 2509991) B2509991
theorem B2820217 : Blo 1112627 2820217 := bstep (se 2 (by rfl) ⟨1057581, by rfl⟩ : syracuseStep 2820217 = 2115163) B2115163
theorem B1673399 : Blo 1112627 1673399 := bstep (se 1 (by rfl) ⟨1255049, by rfl⟩ : syracuseStep 1673399 = 2510099) B2510099
theorem B1116479 : Blo 1112627 1116479 := bstep (se 1 (by rfl) ⟨837359, by rfl⟩ : syracuseStep 1116479 = 1674719) B1674719
theorem B1116519 : Blo 1112627 1116519 := bstep (se 1 (by rfl) ⟨837389, by rfl⟩ : syracuseStep 1116519 = 1674779) B1674779
theorem B42830207 : Blo 1112627 42830207 := bstep (se 1 (by rfl) ⟨32122655, by rfl⟩ : syracuseStep 42830207 = 64245311) B64245311
theorem B1116607 : Blo 1112627 1116607 := bstep (se 1 (by rfl) ⟨837455, by rfl⟩ : syracuseStep 1116607 = 1674911) B1674911
theorem B1673711 : Blo 1112627 1673711 := bstep (se 1 (by rfl) ⟨1255283, by rfl⟩ : syracuseStep 1673711 = 2510567) B2510567
theorem B4753991 : Blo 1112627 4753991 := bstep (se 1 (by rfl) ⟨3565493, by rfl⟩ : syracuseStep 4753991 = 7130987) B7130987
theorem B1673819 : Blo 1112627 1673819 := bstep (se 1 (by rfl) ⟨1255364, by rfl⟩ : syracuseStep 1673819 = 2510729) B2510729
theorem B1412407 : Blo 1112627 1412407 := bstep (se 1 (by rfl) ⟨1059305, by rfl⟩ : syracuseStep 1412407 = 2118611) B2118611
theorem B1674551 : Blo 1112627 1674551 := bstep (se 1 (by rfl) ⟨1255913, by rfl⟩ : syracuseStep 1674551 = 2511827) B2511827
theorem B4231223 : Blo 1112627 4231223 := bstep (se 1 (by rfl) ⟨3173417, by rfl⟩ : syracuseStep 4231223 = 6346835) B6346835
theorem B68686289 : Blo 1112627 68686289 := bstep (se 2 (by rfl) ⟨25757358, by rfl⟩ : syracuseStep 68686289 = 51514717) B51514717
theorem B14258693 : Blo 1112627 14258693 := bstep (se 4 (by rfl) ⟨1336752, by rfl⟩ : syracuseStep 14258693 = 2673505) B2673505
theorem B11768429 : Blo 1112627 11768429 := bstep (se 3 (by rfl) ⟨2206580, by rfl⟩ : syracuseStep 11768429 = 4413161) B4413161
theorem B4756315 : Blo 1112627 4756315 := bstep (se 1 (by rfl) ⟨3567236, by rfl⟩ : syracuseStep 4756315 = 7134473) B7134473
theorem B4232027 : Blo 1112627 4232027 := bstep (se 1 (by rfl) ⟨3174020, by rfl⟩ : syracuseStep 4232027 = 6348041) B6348041
theorem B4232969 : Blo 1112627 4232969 := bstep (se 2 (by rfl) ⟨1587363, by rfl⟩ : syracuseStep 4232969 = 3174727) B3174727
theorem B12687515 : Blo 1112627 12687515 := bstep (se 1 (by rfl) ⟨9515636, by rfl⟩ : syracuseStep 12687515 = 19031273) B19031273
theorem B3217835 : Blo 1112627 3217835 := bstep (se 1 (by rfl) ⟨2413376, by rfl⟩ : syracuseStep 3217835 = 4826753) B4826753
theorem B1251823 : Blo 1112627 1251823 := bstep (se 1 (by rfl) ⟨938867, by rfl⟩ : syracuseStep 1251823 = 1877735) B1877735
theorem B3218411 : Blo 1112627 3218411 := bstep (se 1 (by rfl) ⟨2413808, by rfl⟩ : syracuseStep 3218411 = 4827617) B4827617
theorem B10722779 : Blo 1112627 10722779 := bstep (se 1 (by rfl) ⟨8042084, by rfl⟩ : syracuseStep 10722779 = 16084169) B16084169
theorem B15244847 : Blo 1112627 15244847 := bstep (se 1 (by rfl) ⟨11433635, by rfl⟩ : syracuseStep 15244847 = 22867271) B22867271
theorem B1188199 : Blo 1112627 1188199 := bstep (se 1 (by rfl) ⟨891149, by rfl⟩ : syracuseStep 1188199 = 1782299) B1782299
theorem B1878619 : Blo 1112627 1878619 := bstep (se 1 (by rfl) ⟨1408964, by rfl⟩ : syracuseStep 1878619 = 2817929) B2817929
theorem B1879247 : Blo 1112627 1879247 := bstep (se 1 (by rfl) ⟨1409435, by rfl⟩ : syracuseStep 1879247 = 2818871) B2818871
theorem B4763423 : Blo 1112627 4763423 := bstep (se 1 (by rfl) ⟨3572567, by rfl⟩ : syracuseStep 4763423 = 7145135) B7145135
theorem B1880111 : Blo 1112627 1880111 := bstep (se 1 (by rfl) ⟨1410083, by rfl⟩ : syracuseStep 1880111 = 2820167) B2820167
theorem B1880219 : Blo 1112627 1880219 := bstep (se 1 (by rfl) ⟨1410164, by rfl⟩ : syracuseStep 1880219 = 2820329) B2820329
theorem B1880239 : Blo 1112627 1880239 := bstep (se 1 (by rfl) ⟨1410179, by rfl⟩ : syracuseStep 1880239 = 2820359) B2820359
theorem B24785189 : Blo 1112627 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B2863583 : Blo 1112627 2863583 := bstep (se 1 (by rfl) ⟨2147687, by rfl⟩ : syracuseStep 2863583 = 4295375) B4295375
theorem B10728125 : Blo 1112627 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B5649263 : Blo 1112627 5649263 := bstep (se 1 (by rfl) ⟨4236947, by rfl⟩ : syracuseStep 5649263 = 8473895) B8473895
theorem B40678595 : Blo 1112627 40678595 := bstep (se 1 (by rfl) ⟨30508946, by rfl⟩ : syracuseStep 40678595 = 61017893) B61017893
theorem B4765337 : Blo 1112627 4765337 := bstep (se 2 (by rfl) ⟨1787001, by rfl⟩ : syracuseStep 4765337 = 3574003) B3574003
theorem B5093131 : Blo 1112627 5093131 := bstep (se 1 (by rfl) ⟨3819848, by rfl⟩ : syracuseStep 5093131 = 7639697) B7639697
theorem B5355355 : Blo 1112627 5355355 := bstep (se 1 (by rfl) ⟨4016516, by rfl⟩ : syracuseStep 5355355 = 8033033) B8033033
theorem B2504591 : Blo 1112627 2504591 := bstep (se 1 (by rfl) ⟨1878443, by rfl⟩ : syracuseStep 2504591 = 3756887) B3756887
theorem B2504681 : Blo 1112627 2504681 := bstep (se 2 (by rfl) ⟨939255, by rfl⟩ : syracuseStep 2504681 = 1878511) B1878511
theorem B4766141 : Blo 1112627 4766141 := bstep (se 3 (by rfl) ⟨893651, by rfl⟩ : syracuseStep 4766141 = 1787303) B1787303
theorem B17152559 : Blo 1112627 17152559 := bstep (se 1 (by rfl) ⟨12864419, by rfl⟩ : syracuseStep 17152559 = 25728839) B25728839
theorem B2505311 : Blo 1112627 2505311 := bstep (se 1 (by rfl) ⟨1878983, by rfl⟩ : syracuseStep 2505311 = 3757967) B3757967
theorem B3816031 : Blo 1112627 3816031 := bstep (se 1 (by rfl) ⟨2862023, by rfl⟩ : syracuseStep 3816031 = 5724047) B5724047
theorem B13744883 : Blo 1112627 13744883 := bstep (se 1 (by rfl) ⟨10308662, by rfl⟩ : syracuseStep 13744883 = 20617325) B20617325
theorem B5651207 : Blo 1112627 5651207 := bstep (se 1 (by rfl) ⟨4238405, by rfl⟩ : syracuseStep 5651207 = 8476811) B8476811
theorem B14269355 : Blo 1112627 14269355 := bstep (se 1 (by rfl) ⟨10702016, by rfl⟩ : syracuseStep 14269355 = 21404033) B21404033
theorem B15449287 : Blo 1112627 15449287 := bstep (se 1 (by rfl) ⟨11586965, by rfl⟩ : syracuseStep 15449287 = 23173931) B23173931
theorem B34356575 : Blo 1112627 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B1883513 : Blo 1112627 1883513 := bstep (se 2 (by rfl) ⟨706317, by rfl⟩ : syracuseStep 1883513 = 1412635) B1412635
theorem B1884073 : Blo 1112627 1884073 := bstep (se 2 (by rfl) ⟨706527, by rfl⟩ : syracuseStep 1884073 = 1413055) B1413055
theorem B2113607 : Blo 1112627 2113607 := bstep (se 1 (by rfl) ⟨1585205, by rfl⟩ : syracuseStep 2113607 = 3170411) B3170411
theorem B2506895 : Blo 1112627 2506895 := bstep (se 1 (by rfl) ⟨1880171, by rfl⟩ : syracuseStep 2506895 = 3760343) B3760343
theorem B2507003 : Blo 1112627 2507003 := bstep (se 1 (by rfl) ⟨1880252, by rfl⟩ : syracuseStep 2507003 = 3760505) B3760505
theorem B12861821 : Blo 1112627 12861821 := bstep (se 3 (by rfl) ⟨2411591, by rfl⟩ : syracuseStep 12861821 = 4823183) B4823183
theorem B2507291 : Blo 1112627 2507291 := bstep (se 1 (by rfl) ⟨1880468, by rfl⟩ : syracuseStep 2507291 = 3760937) B3760937
theorem B4768379 : Blo 1112627 4768379 := bstep (se 1 (by rfl) ⟨3576284, by rfl⟩ : syracuseStep 4768379 = 7152569) B7152569
theorem B19022525 : Blo 1112627 19022525 := bstep (se 3 (by rfl) ⟨3566723, by rfl⟩ : syracuseStep 19022525 = 7133447) B7133447
theorem B2507849 : Blo 1112627 2507849 := bstep (se 2 (by rfl) ⟨940443, by rfl⟩ : syracuseStep 2507849 = 1880887) B1880887
theorem B36160829 : Blo 1112627 36160829 := bstep (se 3 (by rfl) ⟨6780155, by rfl⟩ : syracuseStep 36160829 = 13560311) B13560311
theorem B14698043 : Blo 1112627 14698043 := bstep (se 1 (by rfl) ⟨11023532, by rfl⟩ : syracuseStep 14698043 = 22047065) B22047065
theorem B2147995 : Blo 1112627 2147995 := bstep (se 1 (by rfl) ⟨1610996, by rfl⟩ : syracuseStep 2147995 = 3221993) B3221993
theorem B2115391 : Blo 1112627 2115391 := bstep (se 1 (by rfl) ⟨1586543, by rfl⟩ : syracuseStep 2115391 = 3173087) B3173087
theorem B2115551 : Blo 1112627 2115551 := bstep (se 1 (by rfl) ⟨1586663, by rfl⟩ : syracuseStep 2115551 = 3173327) B3173327
theorem B5359927 : Blo 1112627 5359927 := bstep (se 1 (by rfl) ⟨4019945, by rfl⟩ : syracuseStep 5359927 = 8039891) B8039891
theorem B8472923 : Blo 1112627 8472923 := bstep (se 1 (by rfl) ⟨6354692, by rfl⟩ : syracuseStep 8472923 = 12709385) B12709385
theorem B16042535 : Blo 1112627 16042535 := bstep (se 1 (by rfl) ⟨12031901, by rfl⟩ : syracuseStep 16042535 = 24063803) B24063803
theorem B2378431 : Blo 1112627 2378431 := bstep (se 1 (by rfl) ⟨1783823, by rfl⟩ : syracuseStep 2378431 = 3567647) B3567647
theorem B7130065 : Blo 1112627 7130065 := bstep (se 2 (by rfl) ⟨2673774, by rfl⟩ : syracuseStep 7130065 = 5347549) B5347549
theorem B6769645 : Blo 1112627 6769645 := bstep (se 3 (by rfl) ⟨1269308, by rfl⟩ : syracuseStep 6769645 = 2538617) B2538617
theorem B2509865 : Blo 1112627 2509865 := bstep (se 2 (by rfl) ⟨941199, by rfl⟩ : syracuseStep 2509865 = 1882399) B1882399
theorem B14273819 : Blo 1112627 14273819 := bstep (se 1 (by rfl) ⟨10705364, by rfl⟩ : syracuseStep 14273819 = 21410729) B21410729
theorem B3755321 : Blo 1112627 3755321 := bstep (se 2 (by rfl) ⟨1408245, by rfl⟩ : syracuseStep 3755321 = 2816491) B2816491
theorem B2510153 : Blo 1112627 2510153 := bstep (se 2 (by rfl) ⟨941307, by rfl⟩ : syracuseStep 2510153 = 1882615) B1882615
theorem B2117191 : Blo 1112627 2117191 := bstep (se 1 (by rfl) ⟨1587893, by rfl⟩ : syracuseStep 2117191 = 3175787) B3175787
theorem B8572759 : Blo 1112627 8572759 := bstep (se 1 (by rfl) ⟨6429569, by rfl⟩ : syracuseStep 8572759 = 12859139) B12859139
theorem B12702095 : Blo 1112627 12702095 := bstep (se 1 (by rfl) ⟨9526571, by rfl⟩ : syracuseStep 12702095 = 19053143) B19053143
theorem B2511593 : Blo 1112627 2511593 := bstep (se 2 (by rfl) ⟨941847, by rfl⟩ : syracuseStep 2511593 = 1883695) B1883695
theorem B19026899 : Blo 1112627 19026899 := bstep (se 1 (by rfl) ⟨14270174, by rfl⟩ : syracuseStep 19026899 = 28540349) B28540349
theorem B2118649 : Blo 1112627 2118649 := bstep (se 2 (by rfl) ⟨794493, by rfl⟩ : syracuseStep 2118649 = 1588987) B1588987
theorem B3757319 : Blo 1112627 3757319 := bstep (se 1 (by rfl) ⟨2817989, by rfl⟩ : syracuseStep 3757319 = 5635979) B5635979
theorem B7132627 : Blo 1112627 7132627 := bstep (se 1 (by rfl) ⟨5349470, by rfl⟩ : syracuseStep 7132627 = 10698941) B10698941
theorem B2512403 : Blo 1112627 2512403 := bstep (se 1 (by rfl) ⟨1884302, by rfl⟩ : syracuseStep 2512403 = 3768605) B3768605
theorem B10704635 : Blo 1112627 10704635 := bstep (se 1 (by rfl) ⟨8028476, by rfl⟩ : syracuseStep 10704635 = 16056953) B16056953
theorem B41277251 : Blo 1112627 41277251 := bstep (se 1 (by rfl) ⟨30957938, by rfl⟩ : syracuseStep 41277251 = 61915877) B61915877
theorem B1694747 : Blo 1112627 1694747 := bstep (se 1 (by rfl) ⟨1271060, by rfl⟩ : syracuseStep 1694747 = 2542121) B2542121
theorem B3759209 : Blo 1112627 3759209 := bstep (se 2 (by rfl) ⟨1409703, by rfl⟩ : syracuseStep 3759209 = 2819407) B2819407
theorem B2382959 : Blo 1112627 2382959 := bstep (se 1 (by rfl) ⟨1787219, by rfl⟩ : syracuseStep 2382959 = 3574439) B3574439
theorem B3760073 : Blo 1112627 3760073 := bstep (se 2 (by rfl) ⟨1410027, by rfl⟩ : syracuseStep 3760073 = 2820055) B2820055
theorem B3760235 : Blo 1112627 3760235 := bstep (se 1 (by rfl) ⟨2820176, by rfl⟩ : syracuseStep 3760235 = 5640353) B5640353
theorem B4022399 : Blo 1112627 4022399 := bstep (se 1 (by rfl) ⟨3016799, by rfl⟩ : syracuseStep 4022399 = 6033599) B6033599
theorem B9036319 : Blo 1112627 9036319 := bstep (se 1 (by rfl) ⟨6777239, by rfl⟩ : syracuseStep 9036319 = 13554479) B13554479
theorem B3171287 : Blo 1112627 3171287 := bstep (se 1 (by rfl) ⟨2378465, by rfl⟩ : syracuseStep 3171287 = 4756931) B4756931
theorem B3761207 : Blo 1112627 3761207 := bstep (se 1 (by rfl) ⟨2820905, by rfl⟩ : syracuseStep 3761207 = 5641811) B5641811
theorem B3761639 : Blo 1112627 3761639 := bstep (se 1 (by rfl) ⟨2821229, by rfl⟩ : syracuseStep 3761639 = 5642459) B5642459
theorem B12675851 : Blo 1112627 12675851 := bstep (se 1 (by rfl) ⟨9506888, by rfl⟩ : syracuseStep 12675851 = 19013777) B19013777
theorem B6351641 : Blo 1112627 6351641 := bstep (se 2 (by rfl) ⟨2381865, by rfl⟩ : syracuseStep 6351641 = 4763731) B4763731
theorem B3763151 : Blo 1112627 3763151 := bstep (se 1 (by rfl) ⟨2822363, by rfl⟩ : syracuseStep 3763151 = 5644727) B5644727
theorem B3763475 : Blo 1112627 3763475 := bstep (se 1 (by rfl) ⟨2822606, by rfl⟩ : syracuseStep 3763475 = 5645213) B5645213
theorem B3763529 : Blo 1112627 3763529 := bstep (se 2 (by rfl) ⟨1411323, by rfl⟩ : syracuseStep 3763529 = 2822647) B2822647
theorem B3010031 : Blo 1112627 3010031 := bstep (se 1 (by rfl) ⟨2257523, by rfl⟩ : syracuseStep 3010031 = 4515047) B4515047
theorem B5076361 : Blo 1112627 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B8582867 : Blo 1112627 8582867 := bstep (se 1 (by rfl) ⟨6437150, by rfl⟩ : syracuseStep 8582867 = 12874301) B12874301
theorem B1669289 : Blo 1112627 1669289 := bstep (se 2 (by rfl) ⟨625983, by rfl⟩ : syracuseStep 1669289 = 1251967) B1251967
theorem B3766607 : Blo 1112627 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B4520299 : Blo 1112627 4520299 := bstep (se 1 (by rfl) ⟨3390224, by rfl⟩ : syracuseStep 4520299 = 6780449) B6780449
theorem B1112743 : Blo 1112627 1112743 := bstep (se 1 (by rfl) ⟨834557, by rfl⟩ : syracuseStep 1112743 = 1669115) B1669115
theorem B1112783 : Blo 1112627 1112783 := bstep (se 1 (by rfl) ⟨834587, by rfl⟩ : syracuseStep 1112783 = 1669175) B1669175
theorem B1669871 : Blo 1112627 1669871 := bstep (se 1 (by rfl) ⟨1252403, by rfl⟩ : syracuseStep 1669871 = 2504807) B2504807
theorem B1112827 : Blo 1112627 1112827 := bstep (se 1 (by rfl) ⟨834620, by rfl⟩ : syracuseStep 1112827 = 1669241) B1669241
theorem B1112863 : Blo 1112627 1112863 := bstep (se 1 (by rfl) ⟨834647, by rfl⟩ : syracuseStep 1112863 = 1669295) B1669295
theorem B1113023 : Blo 1112627 1113023 := bstep (se 1 (by rfl) ⟨834767, by rfl⟩ : syracuseStep 1113023 = 1669535) B1669535
theorem B4291553 : Blo 1112627 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B1113083 : Blo 1112627 1113083 := bstep (se 1 (by rfl) ⟨834812, by rfl⟩ : syracuseStep 1113083 = 1669625) B1669625
theorem B2817119 : Blo 1112627 2817119 := bstep (se 1 (by rfl) ⟨2112839, by rfl⟩ : syracuseStep 2817119 = 4225679) B4225679
theorem B5635169 : Blo 1112627 5635169 := bstep (se 2 (by rfl) ⟨2113188, by rfl⟩ : syracuseStep 5635169 = 4226377) B4226377
theorem B1113407 : Blo 1112627 1113407 := bstep (se 1 (by rfl) ⟨835055, by rfl⟩ : syracuseStep 1113407 = 1670111) B1670111
theorem B1113447 : Blo 1112627 1113447 := bstep (se 1 (by rfl) ⟨835085, by rfl⟩ : syracuseStep 1113447 = 1670171) B1670171
theorem B2817463 : Blo 1112627 2817463 := bstep (se 1 (by rfl) ⟨2113097, by rfl⟩ : syracuseStep 2817463 = 4226195) B4226195
theorem B1113703 : Blo 1112627 1113703 := bstep (se 1 (by rfl) ⟨835277, by rfl⟩ : syracuseStep 1113703 = 1670555) B1670555
theorem B4226681 : Blo 1112627 4226681 := bstep (se 2 (by rfl) ⟨1585005, by rfl⟩ : syracuseStep 4226681 = 3170011) B3170011
theorem B1113755 : Blo 1112627 1113755 := bstep (se 1 (by rfl) ⟨835316, by rfl⟩ : syracuseStep 1113755 = 1670633) B1670633
theorem B1113759 : Blo 1112627 1113759 := bstep (se 1 (by rfl) ⟨835319, by rfl⟩ : syracuseStep 1113759 = 1670639) B1670639
theorem B19070639 : Blo 1112627 19070639 := bstep (se 1 (by rfl) ⟨14302979, by rfl⟩ : syracuseStep 19070639 = 28605959) B28605959
theorem B1113851 : Blo 1112627 1113851 := bstep (se 1 (by rfl) ⟨835388, by rfl⟩ : syracuseStep 1113851 = 1670777) B1670777
theorem B32603939 : Blo 1112627 32603939 := bstep (se 1 (by rfl) ⟨24452954, by rfl⟩ : syracuseStep 32603939 = 48905909) B48905909
theorem B1113983 : Blo 1112627 1113983 := bstep (se 1 (by rfl) ⟨835487, by rfl⟩ : syracuseStep 1113983 = 1670975) B1670975
theorem B1114015 : Blo 1112627 1114015 := bstep (se 1 (by rfl) ⟨835511, by rfl⟩ : syracuseStep 1114015 = 1671023) B1671023
theorem B1671161 : Blo 1112627 1671161 := bstep (se 2 (by rfl) ⟨626685, by rfl⟩ : syracuseStep 1671161 = 1253371) B1253371
theorem B1409071 : Blo 1112627 1409071 := bstep (se 1 (by rfl) ⟨1056803, by rfl⟩ : syracuseStep 1409071 = 2113607) B2113607
theorem B2818111 : Blo 1112627 2818111 := bstep (se 1 (by rfl) ⟨2113583, by rfl⟩ : syracuseStep 2818111 = 4227167) B4227167
theorem B1671263 : Blo 1112627 1671263 := bstep (se 1 (by rfl) ⟨1253447, by rfl⟩ : syracuseStep 1671263 = 2506895) B2506895
theorem B1114267 : Blo 1112627 1114267 := bstep (se 1 (by rfl) ⟨835700, by rfl⟩ : syracuseStep 1114267 = 1671401) B1671401
theorem B1114271 : Blo 1112627 1114271 := bstep (se 1 (by rfl) ⟨835703, by rfl⟩ : syracuseStep 1114271 = 1671407) B1671407
theorem B1671335 : Blo 1112627 1671335 := bstep (se 1 (by rfl) ⟨1253501, by rfl⟩ : syracuseStep 1671335 = 2507003) B2507003
theorem B2818223 : Blo 1112627 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B1671527 : Blo 1112627 1671527 := bstep (se 1 (by rfl) ⟨1253645, by rfl⟩ : syracuseStep 1671527 = 2507291) B2507291
theorem B3178919 : Blo 1112627 3178919 := bstep (se 1 (by rfl) ⟨2384189, by rfl⟩ : syracuseStep 3178919 = 4768379) B4768379
theorem B12681683 : Blo 1112627 12681683 := bstep (se 1 (by rfl) ⟨9511262, by rfl⟩ : syracuseStep 12681683 = 19022525) B19022525
theorem B1671899 : Blo 1112627 1671899 := bstep (se 1 (by rfl) ⟨1253924, by rfl⟩ : syracuseStep 1671899 = 2507849) B2507849
theorem B1114875 : Blo 1112627 1114875 := bstep (se 1 (by rfl) ⟨836156, by rfl⟩ : syracuseStep 1114875 = 1672313) B1672313
theorem B1114907 : Blo 1112627 1114907 := bstep (se 1 (by rfl) ⟨836180, by rfl⟩ : syracuseStep 1114907 = 1672361) B1672361
theorem B1115163 : Blo 1112627 1115163 := bstep (se 1 (by rfl) ⟨836372, by rfl⟩ : syracuseStep 1115163 = 1672745) B1672745
theorem B9798695 : Blo 1112627 9798695 := bstep (se 1 (by rfl) ⟨7349021, by rfl⟩ : syracuseStep 9798695 = 14698043) B14698043
theorem B1115367 : Blo 1112627 1115367 := bstep (se 1 (by rfl) ⟨836525, by rfl⟩ : syracuseStep 1115367 = 1673051) B1673051
theorem B6358247 : Blo 1112627 6358247 := bstep (se 1 (by rfl) ⟨4768685, by rfl⟩ : syracuseStep 6358247 = 9537371) B9537371
theorem B1410367 : Blo 1112627 1410367 := bstep (se 1 (by rfl) ⟨1057775, by rfl⟩ : syracuseStep 1410367 = 2115551) B2115551
theorem B1115551 : Blo 1112627 1115551 := bstep (se 1 (by rfl) ⟨836663, by rfl⟩ : syracuseStep 1115551 = 1673327) B1673327
theorem B1115599 : Blo 1112627 1115599 := bstep (se 1 (by rfl) ⟨836699, by rfl⟩ : syracuseStep 1115599 = 1673399) B1673399
theorem B1115807 : Blo 1112627 1115807 := bstep (se 1 (by rfl) ⟨836855, by rfl⟩ : syracuseStep 1115807 = 1673711) B1673711
theorem B1115879 : Blo 1112627 1115879 := bstep (se 1 (by rfl) ⟨836909, by rfl⟩ : syracuseStep 1115879 = 1673819) B1673819
theorem B1673243 : Blo 1112627 1673243 := bstep (se 1 (by rfl) ⟨1254932, by rfl⟩ : syracuseStep 1673243 = 2509865) B2509865
theorem B24119329 : Blo 1112627 24119329 := bstep (se 2 (by rfl) ⟨9044748, by rfl⟩ : syracuseStep 24119329 = 18089497) B18089497
theorem B1116367 : Blo 1112627 1116367 := bstep (se 1 (by rfl) ⟨837275, by rfl⟩ : syracuseStep 1116367 = 1674551) B1674551
theorem B1673435 : Blo 1112627 1673435 := bstep (se 1 (by rfl) ⟨1255076, by rfl⟩ : syracuseStep 1673435 = 2510153) B2510153
theorem B2820521 : Blo 1112627 2820521 := bstep (se 2 (by rfl) ⟨1057695, by rfl⟩ : syracuseStep 2820521 = 2115391) B2115391
theorem B2820815 : Blo 1112627 2820815 := bstep (se 1 (by rfl) ⟨2115611, by rfl⟩ : syracuseStep 2820815 = 4231223) B4231223
theorem B9505795 : Blo 1112627 9505795 := bstep (se 1 (by rfl) ⟨7129346, by rfl⟩ : syracuseStep 9505795 = 14258693) B14258693
theorem B7146569 : Blo 1112627 7146569 := bstep (se 2 (by rfl) ⟨2679963, by rfl⟩ : syracuseStep 7146569 = 5359927) B5359927
theorem B1674395 : Blo 1112627 1674395 := bstep (se 1 (by rfl) ⟨1255796, by rfl⟩ : syracuseStep 1674395 = 2511593) B2511593
theorem B2821351 : Blo 1112627 2821351 := bstep (se 1 (by rfl) ⟨2116013, by rfl⟩ : syracuseStep 2821351 = 4232027) B4232027
theorem B12684599 : Blo 1112627 12684599 := bstep (se 1 (by rfl) ⟨9513449, by rfl⟩ : syracuseStep 12684599 = 19026899) B19026899
theorem B1674935 : Blo 1112627 1674935 := bstep (se 1 (by rfl) ⟨1256201, by rfl⟩ : syracuseStep 1674935 = 2512403) B2512403
theorem B2821979 : Blo 1112627 2821979 := bstep (se 1 (by rfl) ⟨2116484, by rfl⟩ : syracuseStep 2821979 = 4232969) B4232969
theorem B9506753 : Blo 1112627 9506753 := bstep (se 2 (by rfl) ⟨3565032, by rfl⟩ : syracuseStep 9506753 = 7130065) B7130065
theorem B8458343 : Blo 1112627 8458343 := bstep (se 1 (by rfl) ⟨6343757, by rfl⟩ : syracuseStep 8458343 = 12687515) B12687515
theorem B2822921 : Blo 1112627 2822921 := bstep (se 2 (by rfl) ⟨1058595, by rfl⟩ : syracuseStep 2822921 = 2117191) B2117191
theorem B7148519 : Blo 1112627 7148519 := bstep (se 1 (by rfl) ⟨5361389, by rfl⟩ : syracuseStep 7148519 = 10722779) B10722779
theorem B10163231 : Blo 1112627 10163231 := bstep (se 1 (by rfl) ⟨7622423, by rfl⟩ : syracuseStep 10163231 = 15244847) B15244847
theorem B2824865 : Blo 1112627 2824865 := bstep (se 2 (by rfl) ⟨1059324, by rfl⟩ : syracuseStep 2824865 = 2118649) B2118649
theorem B4234427 : Blo 1112627 4234427 := bstep (se 1 (by rfl) ⟨3175820, by rfl⟩ : syracuseStep 4234427 = 6351641) B6351641
theorem B9510169 : Blo 1112627 9510169 := bstep (se 2 (by rfl) ⟨3566313, by rfl⟩ : syracuseStep 9510169 = 7132627) B7132627
theorem B1252831 : Blo 1112627 1252831 := bstep (se 1 (by rfl) ⟨939623, by rfl⟩ : syracuseStep 1252831 = 1879247) B1879247
theorem B2006687 : Blo 1112627 2006687 := bstep (se 1 (by rfl) ⟨1505015, by rfl⟩ : syracuseStep 2006687 = 3010031) B3010031
theorem B6790841 : Blo 1112627 6790841 := bstep (se 2 (by rfl) ⟨2546565, by rfl⟩ : syracuseStep 6790841 = 5093131) B5093131
theorem B11444141 : Blo 1112627 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B1253407 : Blo 1112627 1253407 := bstep (se 1 (by rfl) ⟨940055, by rfl⟩ : syracuseStep 1253407 = 1880111) B1880111
theorem B1253479 : Blo 1112627 1253479 := bstep (se 1 (by rfl) ⟨940109, by rfl⟩ : syracuseStep 1253479 = 1880219) B1880219
theorem B16523459 : Blo 1112627 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B1909055 : Blo 1112627 1909055 := bstep (se 1 (by rfl) ⟨1431791, by rfl⟩ : syracuseStep 1909055 = 2863583) B2863583
theorem B7152083 : Blo 1112627 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B5088041 : Blo 1112627 5088041 := bstep (se 2 (by rfl) ⟨1908015, by rfl⟩ : syracuseStep 5088041 = 3816031) B3816031
theorem B45721381 : Blo 1112627 45721381 := bstep (se 4 (by rfl) ⟨4286379, by rfl⟩ : syracuseStep 45721381 = 8572759) B8572759
theorem B9512903 : Blo 1112627 9512903 := bstep (se 1 (by rfl) ⟨7134677, by rfl⟩ : syracuseStep 9512903 = 14269355) B14269355
theorem B1878079 : Blo 1112627 1878079 := bstep (se 1 (by rfl) ⟨1408559, by rfl⟩ : syracuseStep 1878079 = 2817119) B2817119
theorem B1255675 : Blo 1112627 1255675 := bstep (se 1 (by rfl) ⟨941756, by rfl⟩ : syracuseStep 1255675 = 1883513) B1883513
theorem B21735959 : Blo 1112627 21735959 := bstep (se 1 (by rfl) ⟨16301969, by rfl⟩ : syracuseStep 21735959 = 32603939) B32603939
theorem B4238345 : Blo 1112627 4238345 := bstep (se 2 (by rfl) ⟨1589379, by rfl⟩ : syracuseStep 4238345 = 3178759) B3178759
theorem B5648615 : Blo 1112627 5648615 := bstep (se 1 (by rfl) ⟨4236461, by rfl⟩ : syracuseStep 5648615 = 8472923) B8472923
theorem B28553471 : Blo 1112627 28553471 := bstep (se 1 (by rfl) ⟨21415103, by rfl⟩ : syracuseStep 28553471 = 42830207) B42830207
theorem B10695023 : Blo 1112627 10695023 := bstep (se 1 (by rfl) ⟨8021267, by rfl⟩ : syracuseStep 10695023 = 16042535) B16042535
theorem B6337061 : Blo 1112627 6337061 := bstep (se 4 (by rfl) ⟨594099, by rfl⟩ : syracuseStep 6337061 = 1188199) B1188199
theorem B9515879 : Blo 1112627 9515879 := bstep (se 1 (by rfl) ⟨7136909, by rfl⟩ : syracuseStep 9515879 = 14273819) B14273819
theorem B2863993 : Blo 1112627 2863993 := bstep (se 2 (by rfl) ⟨1073997, by rfl⟩ : syracuseStep 2863993 = 2147995) B2147995
theorem B2503547 : Blo 1112627 2503547 := bstep (se 1 (by rfl) ⟨1877660, by rfl⟩ : syracuseStep 2503547 = 3755321) B3755321
theorem B6337561 : Blo 1112627 6337561 := bstep (se 2 (by rfl) ⟨2376585, by rfl⟩ : syracuseStep 6337561 = 4753171) B4753171
theorem B8468063 : Blo 1112627 8468063 := bstep (se 1 (by rfl) ⟨6351047, by rfl⟩ : syracuseStep 8468063 = 12702095) B12702095
theorem B45790859 : Blo 1112627 45790859 := bstep (se 1 (by rfl) ⟨34343144, by rfl⟩ : syracuseStep 45790859 = 68686289) B68686289
theorem B7845619 : Blo 1112627 7845619 := bstep (se 1 (by rfl) ⟨5884214, by rfl⟩ : syracuseStep 7845619 = 11768429) B11768429
theorem B2504825 : Blo 1112627 2504825 := bstep (se 2 (by rfl) ⟨939309, by rfl⟩ : syracuseStep 2504825 = 1878619) B1878619
theorem B2504879 : Blo 1112627 2504879 := bstep (se 1 (by rfl) ⟨1878659, by rfl⟩ : syracuseStep 2504879 = 3757319) B3757319
theorem B2145223 : Blo 1112627 2145223 := bstep (se 1 (by rfl) ⟨1608917, by rfl⟩ : syracuseStep 2145223 = 3217835) B3217835
theorem B1883209 : Blo 1112627 1883209 := bstep (se 2 (by rfl) ⟨706203, by rfl⟩ : syracuseStep 1883209 = 1412407) B1412407
theorem B2506139 : Blo 1112627 2506139 := bstep (se 1 (by rfl) ⟨1879604, by rfl⟩ : syracuseStep 2506139 = 3759209) B3759209
theorem B2506715 : Blo 1112627 2506715 := bstep (se 1 (by rfl) ⟨1880036, by rfl⟩ : syracuseStep 2506715 = 3760073) B3760073
theorem B2506823 : Blo 1112627 2506823 := bstep (se 1 (by rfl) ⟨1880117, by rfl⟩ : syracuseStep 2506823 = 3760235) B3760235
theorem B2506985 : Blo 1112627 2506985 := bstep (se 2 (by rfl) ⟨940119, by rfl⟩ : syracuseStep 2506985 = 1880239) B1880239
theorem B2114191 : Blo 1112627 2114191 := bstep (se 1 (by rfl) ⟨1585643, by rfl⟩ : syracuseStep 2114191 = 3171287) B3171287
theorem B2507471 : Blo 1112627 2507471 := bstep (se 1 (by rfl) ⟨1880603, by rfl⟩ : syracuseStep 2507471 = 3761207) B3761207
theorem B2507759 : Blo 1112627 2507759 := bstep (se 1 (by rfl) ⟨1880819, by rfl⟩ : syracuseStep 2507759 = 3761639) B3761639
theorem B6341753 : Blo 1112627 6341753 := bstep (se 2 (by rfl) ⟨2378157, by rfl⟩ : syracuseStep 6341753 = 4756315) B4756315
theorem B6768481 : Blo 1112627 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B2508767 : Blo 1112627 2508767 := bstep (se 1 (by rfl) ⟨1881575, by rfl⟩ : syracuseStep 2508767 = 3763151) B3763151
theorem B2508983 : Blo 1112627 2508983 := bstep (se 1 (by rfl) ⟨1881737, by rfl⟩ : syracuseStep 2508983 = 3763475) B3763475
theorem B2509019 : Blo 1112627 2509019 := bstep (se 1 (by rfl) ⟨1881764, by rfl⟩ : syracuseStep 2509019 = 3763529) B3763529
theorem B27119063 : Blo 1112627 27119063 := bstep (se 1 (by rfl) ⟨20339297, by rfl⟩ : syracuseStep 27119063 = 40678595) B40678595
theorem B5721911 : Blo 1112627 5721911 := bstep (se 1 (by rfl) ⟨4291433, by rfl⟩ : syracuseStep 5721911 = 8582867) B8582867
theorem B2511071 : Blo 1112627 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B20599049 : Blo 1112627 20599049 := bstep (se 2 (by rfl) ⟨7724643, by rfl⟩ : syracuseStep 20599049 = 15449287) B15449287
theorem B9163255 : Blo 1112627 9163255 := bstep (se 1 (by rfl) ⟨6872441, by rfl⟩ : syracuseStep 9163255 = 13744883) B13744883
theorem B3756617 : Blo 1112627 3756617 := bstep (se 2 (by rfl) ⟨1408731, by rfl⟩ : syracuseStep 3756617 = 2817463) B2817463
theorem B3756779 : Blo 1112627 3756779 := bstep (se 1 (by rfl) ⟨2817584, by rfl⟩ : syracuseStep 3756779 = 5635169) B5635169
theorem B2512097 : Blo 1112627 2512097 := bstep (se 2 (by rfl) ⟨942036, by rfl⟩ : syracuseStep 2512097 = 1884073) B1884073
theorem B2512295 : Blo 1112627 2512295 := bstep (se 1 (by rfl) ⟨1884221, by rfl⟩ : syracuseStep 2512295 = 3768443) B3768443
theorem B8574547 : Blo 1112627 8574547 := bstep (se 1 (by rfl) ⟨6430910, by rfl⟩ : syracuseStep 8574547 = 12861821) B12861821
theorem B3757697 : Blo 1112627 3757697 := bstep (se 2 (by rfl) ⟨1409136, by rfl⟩ : syracuseStep 3757697 = 2818273) B2818273
theorem B12048425 : Blo 1112627 12048425 := bstep (se 2 (by rfl) ⟨4518159, by rfl⟩ : syracuseStep 12048425 = 9036319) B9036319
theorem B24107219 : Blo 1112627 24107219 := bstep (se 1 (by rfl) ⟨18080414, by rfl⟩ : syracuseStep 24107219 = 36160829) B36160829
theorem B3760289 : Blo 1112627 3760289 := bstep (se 2 (by rfl) ⟨1410108, by rfl⟩ : syracuseStep 3760289 = 2820217) B2820217
theorem B3171241 : Blo 1112627 3171241 := bstep (se 2 (by rfl) ⟨1189215, by rfl⟩ : syracuseStep 3171241 = 2378431) B2378431
theorem B7136423 : Blo 1112627 7136423 := bstep (se 1 (by rfl) ⟨5352317, by rfl⟩ : syracuseStep 7136423 = 10704635) B10704635
theorem B27518167 : Blo 1112627 27518167 := bstep (se 1 (by rfl) ⟨20638625, by rfl⟩ : syracuseStep 27518167 = 41277251) B41277251
theorem B36104773 : Blo 1112627 36104773 := bstep (se 4 (by rfl) ⟨3384822, by rfl⟩ : syracuseStep 36104773 = 6769645) B6769645
theorem B2681599 : Blo 1112627 2681599 := bstep (se 1 (by rfl) ⟨2011199, by rfl⟩ : syracuseStep 2681599 = 4022399) B4022399
theorem B12677309 : Blo 1112627 12677309 := bstep (se 3 (by rfl) ⟨2376995, by rfl⟩ : syracuseStep 12677309 = 4753991) B4753991
theorem B8450567 : Blo 1112627 8450567 := bstep (se 1 (by rfl) ⟨6337925, by rfl⟩ : syracuseStep 8450567 = 12675851) B12675851
theorem B7140473 : Blo 1112627 7140473 := bstep (se 2 (by rfl) ⟨2677677, by rfl⟩ : syracuseStep 7140473 = 5355355) B5355355
theorem B3175615 : Blo 1112627 3175615 := bstep (se 1 (by rfl) ⟨2381711, by rfl⟩ : syracuseStep 3175615 = 4763423) B4763423
theorem B8582429 : Blo 1112627 8582429 := bstep (se 3 (by rfl) ⟨1609205, by rfl⟩ : syracuseStep 8582429 = 3218411) B3218411
theorem B4519325 : Blo 1112627 4519325 := bstep (se 3 (by rfl) ⟨847373, by rfl⟩ : syracuseStep 4519325 = 1694747) B1694747
theorem B6354557 : Blo 1112627 6354557 := bstep (se 3 (by rfl) ⟨1191479, by rfl⟩ : syracuseStep 6354557 = 2382959) B2382959
theorem B6027065 : Blo 1112627 6027065 := bstep (se 2 (by rfl) ⟨2260149, by rfl⟩ : syracuseStep 6027065 = 4520299) B4520299
theorem B3766175 : Blo 1112627 3766175 := bstep (se 1 (by rfl) ⟨2824631, by rfl⟩ : syracuseStep 3766175 = 5649263) B5649263
theorem B1669097 : Blo 1112627 1669097 := bstep (se 2 (by rfl) ⟨625911, by rfl⟩ : syracuseStep 1669097 = 1251823) B1251823
theorem B3176891 : Blo 1112627 3176891 := bstep (se 1 (by rfl) ⟨2382668, by rfl⟩ : syracuseStep 3176891 = 4765337) B4765337
theorem B1669727 : Blo 1112627 1669727 := bstep (se 1 (by rfl) ⟨1252295, by rfl⟩ : syracuseStep 1669727 = 2504591) B2504591
theorem B1669787 : Blo 1112627 1669787 := bstep (se 1 (by rfl) ⟨1252340, by rfl⟩ : syracuseStep 1669787 = 2504681) B2504681
theorem B1112859 : Blo 1112627 1112859 := bstep (se 1 (by rfl) ⟨834644, by rfl⟩ : syracuseStep 1112859 = 1669289) B1669289
theorem B3177427 : Blo 1112627 3177427 := bstep (se 1 (by rfl) ⟨2383070, by rfl⟩ : syracuseStep 3177427 = 4766141) B4766141
theorem B11435039 : Blo 1112627 11435039 := bstep (se 1 (by rfl) ⟨8576279, by rfl⟩ : syracuseStep 11435039 = 17152559) B17152559
theorem B1670207 : Blo 1112627 1670207 := bstep (se 1 (by rfl) ⟨1252655, by rfl⟩ : syracuseStep 1670207 = 2505311) B2505311
theorem B1113247 : Blo 1112627 1113247 := bstep (se 1 (by rfl) ⟨834935, by rfl⟩ : syracuseStep 1113247 = 1669871) B1669871
theorem B3767471 : Blo 1112627 3767471 := bstep (se 1 (by rfl) ⟨2825603, by rfl⟩ : syracuseStep 3767471 = 5651207) B5651207
theorem B22904383 : Blo 1112627 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B2817787 : Blo 1112627 2817787 := bstep (se 1 (by rfl) ⟨2113340, by rfl⟩ : syracuseStep 2817787 = 4226681) B4226681
theorem B12713759 : Blo 1112627 12713759 := bstep (se 1 (by rfl) ⟨9535319, by rfl⟩ : syracuseStep 12713759 = 19070639) B19070639
theorem B1114107 : Blo 1112627 1114107 := bstep (se 1 (by rfl) ⟨835580, by rfl⟩ : syracuseStep 1114107 = 1671161) B1671161
theorem B1671209 : Blo 1112627 1671209 := bstep (se 2 (by rfl) ⟨626703, by rfl⟩ : syracuseStep 1671209 = 1253407) B1253407
theorem B1671215 : Blo 1112627 1671215 := bstep (se 1 (by rfl) ⟨1253411, by rfl⟩ : syracuseStep 1671215 = 2506823) B2506823
theorem B1114175 : Blo 1112627 1114175 := bstep (se 1 (by rfl) ⟨835631, by rfl⟩ : syracuseStep 1114175 = 1671263) B1671263
theorem B1114223 : Blo 1112627 1114223 := bstep (se 1 (by rfl) ⟨835667, by rfl⟩ : syracuseStep 1114223 = 1671335) B1671335
theorem B1671305 : Blo 1112627 1671305 := bstep (se 2 (by rfl) ⟨626739, by rfl⟩ : syracuseStep 1671305 = 1253479) B1253479
theorem B1671323 : Blo 1112627 1671323 := bstep (se 1 (by rfl) ⟨1253492, by rfl⟩ : syracuseStep 1671323 = 2506985) B2506985
theorem B1114351 : Blo 1112627 1114351 := bstep (se 1 (by rfl) ⟨835763, by rfl⟩ : syracuseStep 1114351 = 1671527) B1671527
theorem B8454455 : Blo 1112627 8454455 := bstep (se 1 (by rfl) ⟨6340841, by rfl⟩ : syracuseStep 8454455 = 12681683) B12681683
theorem B1671647 : Blo 1112627 1671647 := bstep (se 1 (by rfl) ⟨1253735, by rfl⟩ : syracuseStep 1671647 = 2507471) B2507471
theorem B1114599 : Blo 1112627 1114599 := bstep (se 1 (by rfl) ⟨835949, by rfl⟩ : syracuseStep 1114599 = 1671899) B1671899
theorem B1671839 : Blo 1112627 1671839 := bstep (se 1 (by rfl) ⟨1253879, by rfl⟩ : syracuseStep 1671839 = 2507759) B2507759
theorem B4227835 : Blo 1112627 4227835 := bstep (se 1 (by rfl) ⟨3170876, by rfl⟩ : syracuseStep 4227835 = 6341753) B6341753
theorem B2818921 : Blo 1112627 2818921 := bstep (se 2 (by rfl) ⟨1057095, by rfl⟩ : syracuseStep 2818921 = 2114191) B2114191
theorem B4228321 : Blo 1112627 4228321 := bstep (se 2 (by rfl) ⟨1585620, by rfl⟩ : syracuseStep 4228321 = 3171241) B3171241
theorem B1672511 : Blo 1112627 1672511 := bstep (se 1 (by rfl) ⟨1254383, by rfl⟩ : syracuseStep 1672511 = 2508767) B2508767
theorem B1115495 : Blo 1112627 1115495 := bstep (se 1 (by rfl) ⟨836621, by rfl⟩ : syracuseStep 1115495 = 1673243) B1673243
theorem B1672655 : Blo 1112627 1672655 := bstep (se 1 (by rfl) ⟨1254491, by rfl⟩ : syracuseStep 1672655 = 2508983) B2508983
theorem B1672679 : Blo 1112627 1672679 := bstep (se 1 (by rfl) ⟨1254509, by rfl⟩ : syracuseStep 1672679 = 2509019) B2509019
theorem B1115623 : Blo 1112627 1115623 := bstep (se 1 (by rfl) ⟨836717, by rfl⟩ : syracuseStep 1115623 = 1673435) B1673435
theorem B1116263 : Blo 1112627 1116263 := bstep (se 1 (by rfl) ⟨837197, by rfl⟩ : syracuseStep 1116263 = 1674395) B1674395
theorem B8456399 : Blo 1112627 8456399 := bstep (se 1 (by rfl) ⟨6342299, by rfl⟩ : syracuseStep 8456399 = 12684599) B12684599
theorem B1116623 : Blo 1112627 1116623 := bstep (se 1 (by rfl) ⟨837467, by rfl⟩ : syracuseStep 1116623 = 1674935) B1674935
theorem B5638895 : Blo 1112627 5638895 := bstep (se 1 (by rfl) ⟨4229171, by rfl⟩ : syracuseStep 5638895 = 8458343) B8458343
theorem B1674047 : Blo 1112627 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B1674233 : Blo 1112627 1674233 := bstep (se 2 (by rfl) ⟨627837, by rfl⟩ : syracuseStep 1674233 = 1255675) B1255675
theorem B48139697 : Blo 1112627 48139697 := bstep (se 2 (by rfl) ⟨18052386, by rfl⟩ : syracuseStep 48139697 = 36104773) B36104773
theorem B1674731 : Blo 1112627 1674731 := bstep (se 1 (by rfl) ⟨1256048, by rfl⟩ : syracuseStep 1674731 = 2512097) B2512097
theorem B1674863 : Blo 1112627 1674863 := bstep (se 1 (by rfl) ⟨1256147, by rfl⟩ : syracuseStep 1674863 = 2512295) B2512295
theorem B3575465 : Blo 1112627 3575465 := bstep (se 2 (by rfl) ⟨1340799, by rfl⟩ : syracuseStep 3575465 = 2681599) B2681599
theorem B8032283 : Blo 1112627 8032283 := bstep (se 1 (by rfl) ⟨6024212, by rfl⟩ : syracuseStep 8032283 = 12048425) B12048425
theorem B2822951 : Blo 1112627 2822951 := bstep (se 1 (by rfl) ⟨2117213, by rfl⟩ : syracuseStep 2822951 = 4234427) B4234427
theorem B11441189 : Blo 1112627 11441189 := bstep (se 4 (by rfl) ⟨1072611, by rfl⟩ : syracuseStep 11441189 = 2145223) B2145223
theorem B4527227 : Blo 1112627 4527227 := bstep (se 1 (by rfl) ⟨3395420, by rfl⟩ : syracuseStep 4527227 = 6790841) B6790841
theorem B11015639 : Blo 1112627 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B4757615 : Blo 1112627 4757615 := bstep (se 1 (by rfl) ⟨3568211, by rfl⟩ : syracuseStep 4757615 = 7136423) B7136423
theorem B4234153 : Blo 1112627 4234153 := bstep (se 2 (by rfl) ⟨1587807, by rfl⟩ : syracuseStep 4234153 = 3175615) B3175615
theorem B2825563 : Blo 1112627 2825563 := bstep (se 1 (by rfl) ⟨2119172, by rfl⟩ : syracuseStep 2825563 = 4238345) B4238345
theorem B10460825 : Blo 1112627 10460825 := bstep (se 2 (by rfl) ⟨3922809, by rfl⟩ : syracuseStep 10460825 = 7845619) B7845619
theorem B4760315 : Blo 1112627 4760315 := bstep (se 1 (by rfl) ⟨3570236, by rfl⟩ : syracuseStep 4760315 = 7140473) B7140473
theorem B5645375 : Blo 1112627 5645375 := bstep (se 1 (by rfl) ⟨4234031, by rfl⟩ : syracuseStep 5645375 = 8468063) B8468063
theorem B4236371 : Blo 1112627 4236371 := bstep (se 1 (by rfl) ⟨3177278, by rfl⟩ : syracuseStep 4236371 = 6354557) B6354557
theorem B4236569 : Blo 1112627 4236569 := bstep (se 2 (by rfl) ⟨1588713, by rfl⟩ : syracuseStep 4236569 = 3177427) B3177427
theorem B1878761 : Blo 1112627 1878761 := bstep (se 2 (by rfl) ⟨704535, by rfl⟩ : syracuseStep 1878761 = 1409071) B1409071
theorem B1878815 : Blo 1112627 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B54930797 : Blo 1112627 54930797 := bstep (se 3 (by rfl) ⟨10299524, by rfl⟩ : syracuseStep 54930797 = 20599049) B20599049
theorem B6532463 : Blo 1112627 6532463 := bstep (se 1 (by rfl) ⟨4899347, by rfl⟩ : syracuseStep 6532463 = 9798695) B9798695
theorem B4238831 : Blo 1112627 4238831 := bstep (se 1 (by rfl) ⟨3179123, by rfl⟩ : syracuseStep 4238831 = 6358247) B6358247
theorem B5090813 : Blo 1112627 5090813 := bstep (se 3 (by rfl) ⟨954527, by rfl⟩ : syracuseStep 5090813 = 1909055) B1909055
theorem B1880347 : Blo 1112627 1880347 := bstep (se 1 (by rfl) ⟨1410260, by rfl⟩ : syracuseStep 1880347 = 2820521) B2820521
theorem B1880489 : Blo 1112627 1880489 := bstep (se 2 (by rfl) ⟨705183, by rfl⟩ : syracuseStep 1880489 = 1410367) B1410367
theorem B1880543 : Blo 1112627 1880543 := bstep (se 1 (by rfl) ⟨1410407, by rfl⟩ : syracuseStep 1880543 = 2820815) B2820815
theorem B60961841 : Blo 1112627 60961841 := bstep (se 2 (by rfl) ⟨22860690, by rfl⟩ : syracuseStep 60961841 = 45721381) B45721381
theorem B9024641 : Blo 1112627 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B3814607 : Blo 1112627 3814607 := bstep (se 1 (by rfl) ⟨2860955, by rfl⟩ : syracuseStep 3814607 = 5721911) B5721911
theorem B1881319 : Blo 1112627 1881319 := bstep (se 1 (by rfl) ⟨1410989, by rfl⟩ : syracuseStep 1881319 = 2821979) B2821979
theorem B6337835 : Blo 1112627 6337835 := bstep (se 1 (by rfl) ⟨4753376, by rfl⟩ : syracuseStep 6337835 = 9506753) B9506753
theorem B32159105 : Blo 1112627 32159105 := bstep (se 2 (by rfl) ⟨12059664, by rfl⟩ : syracuseStep 32159105 = 24119329) B24119329
theorem B2504105 : Blo 1112627 2504105 := bstep (se 2 (by rfl) ⟨939039, by rfl⟩ : syracuseStep 2504105 = 1878079) B1878079
theorem B2504411 : Blo 1112627 2504411 := bstep (se 1 (by rfl) ⟨1878308, by rfl⟩ : syracuseStep 2504411 = 3756617) B3756617
theorem B2504519 : Blo 1112627 2504519 := bstep (se 1 (by rfl) ⟨1878389, by rfl⟩ : syracuseStep 2504519 = 3756779) B3756779
theorem B1881947 : Blo 1112627 1881947 := bstep (se 1 (by rfl) ⟨1411460, by rfl⟩ : syracuseStep 1881947 = 2822921) B2822921
theorem B4765679 : Blo 1112627 4765679 := bstep (se 1 (by rfl) ⟨3574259, by rfl⟩ : syracuseStep 4765679 = 7148519) B7148519
theorem B22886477 : Blo 1112627 22886477 := bstep (se 3 (by rfl) ⟨4291214, by rfl⟩ : syracuseStep 22886477 = 8582429) B8582429
theorem B2505131 : Blo 1112627 2505131 := bstep (se 1 (by rfl) ⟨1878848, by rfl⟩ : syracuseStep 2505131 = 3757697) B3757697
theorem B16071479 : Blo 1112627 16071479 := bstep (se 1 (by rfl) ⟨12053609, by rfl⟩ : syracuseStep 16071479 = 24107219) B24107219
theorem B122108957 : Blo 1112627 122108957 := bstep (se 3 (by rfl) ⟨22895429, by rfl⟩ : syracuseStep 122108957 = 45790859) B45790859
theorem B1883243 : Blo 1112627 1883243 := bstep (se 1 (by rfl) ⟨1412432, by rfl⟩ : syracuseStep 1883243 = 2824865) B2824865
theorem B2506859 : Blo 1112627 2506859 := bstep (se 1 (by rfl) ⟨1880144, by rfl⟩ : syracuseStep 2506859 = 3760289) B3760289
theorem B4768055 : Blo 1112627 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B3392027 : Blo 1112627 3392027 := bstep (se 1 (by rfl) ⟨2544020, by rfl⟩ : syracuseStep 3392027 = 5088041) B5088041
theorem B3818657 : Blo 1112627 3818657 := bstep (se 2 (by rfl) ⟨1431996, by rfl⟩ : syracuseStep 3818657 = 2863993) B2863993
theorem B6341935 : Blo 1112627 6341935 := bstep (se 1 (by rfl) ⟨4756451, by rfl⟩ : syracuseStep 6341935 = 9512903) B9512903
theorem B19057517 : Blo 1112627 19057517 := bstep (se 3 (by rfl) ⟨3573284, by rfl⟩ : syracuseStep 19057517 = 7146569) B7146569
theorem B7130015 : Blo 1112627 7130015 := bstep (se 1 (by rfl) ⟨5347511, by rfl⟩ : syracuseStep 7130015 = 10695023) B10695023
theorem B6343919 : Blo 1112627 6343919 := bstep (se 1 (by rfl) ⟨4757939, by rfl⟩ : syracuseStep 6343919 = 9515879) B9515879
theorem B4018043 : Blo 1112627 4018043 := bstep (se 1 (by rfl) ⟨3013532, by rfl⟩ : syracuseStep 4018043 = 6027065) B6027065
theorem B2510783 : Blo 1112627 2510783 := bstep (se 1 (by rfl) ⟨1883087, by rfl⟩ : syracuseStep 2510783 = 3766175) B3766175
theorem B2510945 : Blo 1112627 2510945 := bstep (se 2 (by rfl) ⟨941604, by rfl⟩ : syracuseStep 2510945 = 1883209) B1883209
theorem B2117927 : Blo 1112627 2117927 := bstep (se 1 (by rfl) ⟨1588445, by rfl⟩ : syracuseStep 2117927 = 3176891) B3176891
theorem B7623359 : Blo 1112627 7623359 := bstep (se 1 (by rfl) ⟨5717519, by rfl⟩ : syracuseStep 7623359 = 11435039) B11435039
theorem B2511647 : Blo 1112627 2511647 := bstep (se 1 (by rfl) ⟨1883735, by rfl⟩ : syracuseStep 2511647 = 3767471) B3767471
theorem B3757049 : Blo 1112627 3757049 := bstep (se 2 (by rfl) ⟨1408893, by rfl⟩ : syracuseStep 3757049 = 2817787) B2817787
theorem B8475839 : Blo 1112627 8475839 := bstep (se 1 (by rfl) ⟨6356879, by rfl⟩ : syracuseStep 8475839 = 12713759) B12713759
theorem B3757481 : Blo 1112627 3757481 := bstep (se 2 (by rfl) ⟨1409055, by rfl⟩ : syracuseStep 3757481 = 2818111) B2818111
theorem B2119279 : Blo 1112627 2119279 := bstep (se 1 (by rfl) ⟨1589459, by rfl⟩ : syracuseStep 2119279 = 3178919) B3178919
theorem B36690889 : Blo 1112627 36690889 := bstep (se 2 (by rfl) ⟨13759083, by rfl⟩ : syracuseStep 36690889 = 27518167) B27518167
theorem B18079375 : Blo 1112627 18079375 := bstep (se 1 (by rfl) ⟨13559531, by rfl⟩ : syracuseStep 18079375 = 27119063) B27119063
theorem B6775487 : Blo 1112627 6775487 := bstep (se 1 (by rfl) ⟨5081615, by rfl⟩ : syracuseStep 6775487 = 10163231) B10163231
theorem B12674393 : Blo 1112627 12674393 := bstep (se 2 (by rfl) ⟨4752897, by rfl⟩ : syracuseStep 12674393 = 9505795) B9505795
theorem B3761801 : Blo 1112627 3761801 := bstep (se 2 (by rfl) ⟨1410675, by rfl⟩ : syracuseStep 3761801 = 2821351) B2821351
theorem B1337791 : Blo 1112627 1337791 := bstep (se 1 (by rfl) ⟨1003343, by rfl⟩ : syracuseStep 1337791 = 2006687) B2006687
theorem B7629427 : Blo 1112627 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B12217673 : Blo 1112627 12217673 := bstep (se 2 (by rfl) ⟨4581627, by rfl⟩ : syracuseStep 12217673 = 9163255) B9163255
theorem B8450081 : Blo 1112627 8450081 := bstep (se 2 (by rfl) ⟨3168780, by rfl⟩ : syracuseStep 8450081 = 6337561) B6337561
theorem B57962557 : Blo 1112627 57962557 := bstep (se 3 (by rfl) ⟨10867979, by rfl⟩ : syracuseStep 57962557 = 21735959) B21735959
theorem B11432729 : Blo 1112627 11432729 := bstep (se 2 (by rfl) ⟨4287273, by rfl⟩ : syracuseStep 11432729 = 8574547) B8574547
theorem B8451539 : Blo 1112627 8451539 := bstep (se 1 (by rfl) ⟨6338654, by rfl⟩ : syracuseStep 8451539 = 12677309) B12677309
theorem B3765743 : Blo 1112627 3765743 := bstep (se 1 (by rfl) ⟨2824307, by rfl⟩ : syracuseStep 3765743 = 5648615) B5648615
theorem B19035647 : Blo 1112627 19035647 := bstep (se 1 (by rfl) ⟨14276735, by rfl⟩ : syracuseStep 19035647 = 28553471) B28553471
theorem B5633711 : Blo 1112627 5633711 := bstep (se 1 (by rfl) ⟨4225283, by rfl⟩ : syracuseStep 5633711 = 8450567) B8450567
theorem B4224707 : Blo 1112627 4224707 := bstep (se 1 (by rfl) ⟨3168530, by rfl⟩ : syracuseStep 4224707 = 6337061) B6337061
theorem B1669031 : Blo 1112627 1669031 := bstep (se 1 (by rfl) ⟨1251773, by rfl⟩ : syracuseStep 1669031 = 2503547) B2503547
theorem B3012883 : Blo 1112627 3012883 := bstep (se 1 (by rfl) ⟨2259662, by rfl⟩ : syracuseStep 3012883 = 4519325) B4519325
theorem B1112731 : Blo 1112627 1112731 := bstep (se 1 (by rfl) ⟨834548, by rfl⟩ : syracuseStep 1112731 = 1669097) B1669097
theorem B1669883 : Blo 1112627 1669883 := bstep (se 1 (by rfl) ⟨1252412, by rfl⟩ : syracuseStep 1669883 = 2504825) B2504825
theorem B1669919 : Blo 1112627 1669919 := bstep (se 1 (by rfl) ⟨1252439, by rfl⟩ : syracuseStep 1669919 = 2504879) B2504879
theorem B12680225 : Blo 1112627 12680225 := bstep (se 2 (by rfl) ⟨4755084, by rfl⟩ : syracuseStep 12680225 = 9510169) B9510169
theorem B1113151 : Blo 1112627 1113151 := bstep (se 1 (by rfl) ⟨834863, by rfl⟩ : syracuseStep 1113151 = 1669727) B1669727
theorem B1113191 : Blo 1112627 1113191 := bstep (se 1 (by rfl) ⟨834893, by rfl⟩ : syracuseStep 1113191 = 1669787) B1669787
theorem B1670441 : Blo 1112627 1670441 := bstep (se 2 (by rfl) ⟨626415, by rfl⟩ : syracuseStep 1670441 = 1252831) B1252831
theorem B1113471 : Blo 1112627 1113471 := bstep (se 1 (by rfl) ⟨835103, by rfl⟩ : syracuseStep 1113471 = 1670207) B1670207
theorem B30539177 : Blo 1112627 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B1670759 : Blo 1112627 1670759 := bstep (se 1 (by rfl) ⟨1253069, by rfl⟩ : syracuseStep 1670759 = 2506139) B2506139
theorem B1671143 : Blo 1112627 1671143 := bstep (se 1 (by rfl) ⟨1253357, by rfl⟩ : syracuseStep 1671143 = 2506715) B2506715
theorem B1114139 : Blo 1112627 1114139 := bstep (se 1 (by rfl) ⟨835604, by rfl⟩ : syracuseStep 1114139 = 1671209) B1671209
theorem B1114143 : Blo 1112627 1114143 := bstep (se 1 (by rfl) ⟨835607, by rfl⟩ : syracuseStep 1114143 = 1671215) B1671215
theorem B1671239 : Blo 1112627 1671239 := bstep (se 1 (by rfl) ⟨1253429, by rfl⟩ : syracuseStep 1671239 = 2506859) B2506859
theorem B1114203 : Blo 1112627 1114203 := bstep (se 1 (by rfl) ⟨835652, by rfl⟩ : syracuseStep 1114203 = 1671305) B1671305
theorem B1114215 : Blo 1112627 1114215 := bstep (se 1 (by rfl) ⟨835661, by rfl⟩ : syracuseStep 1114215 = 1671323) B1671323
theorem B5636303 : Blo 1112627 5636303 := bstep (se 1 (by rfl) ⟨4227227, by rfl⟩ : syracuseStep 5636303 = 8454455) B8454455
theorem B3178703 : Blo 1112627 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B1114431 : Blo 1112627 1114431 := bstep (se 1 (by rfl) ⟨835823, by rfl⟩ : syracuseStep 1114431 = 1671647) B1671647
theorem B2261351 : Blo 1112627 2261351 := bstep (se 1 (by rfl) ⟨1696013, by rfl⟩ : syracuseStep 2261351 = 3392027) B3392027
theorem B1114559 : Blo 1112627 1114559 := bstep (se 1 (by rfl) ⟨835919, by rfl⟩ : syracuseStep 1114559 = 1671839) B1671839
theorem B1115007 : Blo 1112627 1115007 := bstep (se 1 (by rfl) ⟨836255, by rfl⟩ : syracuseStep 1115007 = 1672511) B1672511
theorem B1115103 : Blo 1112627 1115103 := bstep (se 1 (by rfl) ⟨836327, by rfl⟩ : syracuseStep 1115103 = 1672655) B1672655
theorem B1115119 : Blo 1112627 1115119 := bstep (se 1 (by rfl) ⟨836339, by rfl⟩ : syracuseStep 1115119 = 1672679) B1672679
theorem B5637113 : Blo 1112627 5637113 := bstep (se 2 (by rfl) ⟨2113917, by rfl⟩ : syracuseStep 5637113 = 4227835) B4227835
theorem B5637599 : Blo 1112627 5637599 := bstep (se 1 (by rfl) ⟨4228199, by rfl⟩ : syracuseStep 5637599 = 8456399) B8456399
theorem B5637761 : Blo 1112627 5637761 := bstep (se 2 (by rfl) ⟨2114160, by rfl⟩ : syracuseStep 5637761 = 4228321) B4228321
theorem B8455913 : Blo 1112627 8455913 := bstep (se 2 (by rfl) ⟨3170967, by rfl⟩ : syracuseStep 8455913 = 6341935) B6341935
theorem B1116031 : Blo 1112627 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B4753343 : Blo 1112627 4753343 := bstep (se 1 (by rfl) ⟨3565007, by rfl⟩ : syracuseStep 4753343 = 7130015) B7130015
theorem B1116155 : Blo 1112627 1116155 := bstep (se 1 (by rfl) ⟨837116, by rfl⟩ : syracuseStep 1116155 = 1674233) B1674233
theorem B4229279 : Blo 1112627 4229279 := bstep (se 1 (by rfl) ⟨3171959, by rfl⟩ : syracuseStep 4229279 = 6343919) B6343919
theorem B1116487 : Blo 1112627 1116487 := bstep (se 1 (by rfl) ⟨837365, by rfl⟩ : syracuseStep 1116487 = 1674731) B1674731
theorem B1116575 : Blo 1112627 1116575 := bstep (se 1 (by rfl) ⟨837431, by rfl⟩ : syracuseStep 1116575 = 1674863) B1674863
theorem B1673855 : Blo 1112627 1673855 := bstep (se 1 (by rfl) ⟨1255391, by rfl⟩ : syracuseStep 1673855 = 2510783) B2510783
theorem B1673963 : Blo 1112627 1673963 := bstep (se 1 (by rfl) ⟨1255472, by rfl⟩ : syracuseStep 1673963 = 2510945) B2510945
theorem B5082239 : Blo 1112627 5082239 := bstep (se 1 (by rfl) ⟨3811679, by rfl⟩ : syracuseStep 5082239 = 7623359) B7623359
theorem B1674431 : Blo 1112627 1674431 := bstep (se 1 (by rfl) ⟨1255823, by rfl⟩ : syracuseStep 1674431 = 2511647) B2511647
theorem B3018151 : Blo 1112627 3018151 := bstep (se 1 (by rfl) ⟨2263613, by rfl⟩ : syracuseStep 3018151 = 4527227) B4527227
theorem B7343759 : Blo 1112627 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B2824247 : Blo 1112627 2824247 := bstep (se 1 (by rfl) ⟨2118185, by rfl⟩ : syracuseStep 2824247 = 4236371) B4236371
theorem B2824379 : Blo 1112627 2824379 := bstep (se 1 (by rfl) ⟨2118284, by rfl⟩ : syracuseStep 2824379 = 4236569) B4236569
theorem B1252507 : Blo 1112627 1252507 := bstep (se 1 (by rfl) ⟨939380, by rfl⟩ : syracuseStep 1252507 = 1878761) B1878761
theorem B1252543 : Blo 1112627 1252543 := bstep (se 1 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 1252543 = 1878815) B1878815
theorem B2825705 : Blo 1112627 2825705 := bstep (se 2 (by rfl) ⟨1059639, by rfl⟩ : syracuseStep 2825705 = 2119279) B2119279
theorem B2825887 : Blo 1112627 2825887 := bstep (se 1 (by rfl) ⟨2119415, by rfl⟩ : syracuseStep 2825887 = 4238831) B4238831
theorem B1253659 : Blo 1112627 1253659 := bstep (se 1 (by rfl) ⟨940244, by rfl⟩ : syracuseStep 1253659 = 1880489) B1880489
theorem B1253695 : Blo 1112627 1253695 := bstep (se 1 (by rfl) ⟨940271, by rfl⟩ : syracuseStep 1253695 = 1880543) B1880543
theorem B40641227 : Blo 1112627 40641227 := bstep (se 1 (by rfl) ⟨30480920, by rfl⟩ : syracuseStep 40641227 = 60961841) B60961841
theorem B32580461 : Blo 1112627 32580461 := bstep (se 3 (by rfl) ⟨6108836, by rfl⟩ : syracuseStep 32580461 = 12217673) B12217673
theorem B21439403 : Blo 1112627 21439403 := bstep (se 1 (by rfl) ⟨16079552, by rfl⟩ : syracuseStep 21439403 = 32159105) B32159105
theorem B12690431 : Blo 1112627 12690431 := bstep (se 1 (by rfl) ⟨9517823, by rfl⟩ : syracuseStep 12690431 = 19035647) B19035647
theorem B5645537 : Blo 1112627 5645537 := bstep (se 2 (by rfl) ⟨2117076, by rfl⟩ : syracuseStep 5645537 = 4234153) B4234153
theorem B1254631 : Blo 1112627 1254631 := bstep (se 1 (by rfl) ⟨940973, by rfl⟩ : syracuseStep 1254631 = 1881947) B1881947
theorem B81405971 : Blo 1112627 81405971 := bstep (se 1 (by rfl) ⟨61054478, by rfl⟩ : syracuseStep 81405971 = 122108957) B122108957
theorem B1255495 : Blo 1112627 1255495 := bstep (se 1 (by rfl) ⟨941621, by rfl⟩ : syracuseStep 1255495 = 1883243) B1883243
theorem B20359451 : Blo 1112627 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B5647805 : Blo 1112627 5647805 := bstep (se 3 (by rfl) ⟨1058963, by rfl⟩ : syracuseStep 5647805 = 2117927) B2117927
theorem B16068709 : Blo 1112627 16068709 := bstep (se 4 (by rfl) ⟨1506441, by rfl⟩ : syracuseStep 16068709 = 3012883) B3012883
theorem B32093131 : Blo 1112627 32093131 := bstep (se 1 (by rfl) ⟨24069848, by rfl⟩ : syracuseStep 32093131 = 48139697) B48139697
theorem B5354855 : Blo 1112627 5354855 := bstep (se 1 (by rfl) ⟨4016141, by rfl⟩ : syracuseStep 5354855 = 8032283) B8032283
theorem B1881967 : Blo 1112627 1881967 := bstep (se 1 (by rfl) ⟨1411475, by rfl⟩ : syracuseStep 1881967 = 2822951) B2822951
theorem B1783721 : Blo 1112627 1783721 := bstep (se 2 (by rfl) ⟨668895, by rfl⟩ : syracuseStep 1783721 = 1337791) B1337791
theorem B2504699 : Blo 1112627 2504699 := bstep (se 1 (by rfl) ⟨1878524, by rfl⟩ : syracuseStep 2504699 = 3757049) B3757049
theorem B5650559 : Blo 1112627 5650559 := bstep (se 1 (by rfl) ⟨4237919, by rfl⟩ : syracuseStep 5650559 = 8475839) B8475839
theorem B10172569 : Blo 1112627 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B2504987 : Blo 1112627 2504987 := bstep (se 1 (by rfl) ⟨1878740, by rfl⟩ : syracuseStep 2504987 = 3757481) B3757481
theorem B77283409 : Blo 1112627 77283409 := bstep (se 2 (by rfl) ⟨28981278, by rfl⟩ : syracuseStep 77283409 = 57962557) B57962557
theorem B2507129 : Blo 1112627 2507129 := bstep (se 2 (by rfl) ⟨940173, by rfl⟩ : syracuseStep 2507129 = 1880347) B1880347
theorem B2507867 : Blo 1112627 2507867 := bstep (se 1 (by rfl) ⟨1880900, by rfl⟩ : syracuseStep 2507867 = 3761801) B3761801
theorem B2508425 : Blo 1112627 2508425 := bstep (se 2 (by rfl) ⟨940659, by rfl⟩ : syracuseStep 2508425 = 1881319) B1881319
theorem B36620531 : Blo 1112627 36620531 := bstep (se 1 (by rfl) ⟨27465398, by rfl⟩ : syracuseStep 36620531 = 54930797) B54930797
theorem B3393875 : Blo 1112627 3393875 := bstep (se 1 (by rfl) ⟨2545406, by rfl⟩ : syracuseStep 3393875 = 5090813) B5090813
theorem B7621819 : Blo 1112627 7621819 := bstep (se 1 (by rfl) ⟨5716364, by rfl⟩ : syracuseStep 7621819 = 11432729) B11432729
theorem B6016427 : Blo 1112627 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B2543071 : Blo 1112627 2543071 := bstep (se 1 (by rfl) ⟨1907303, by rfl⟩ : syracuseStep 2543071 = 3814607) B3814607
theorem B2510495 : Blo 1112627 2510495 := bstep (se 1 (by rfl) ⟨1882871, by rfl⟩ : syracuseStep 2510495 = 3765743) B3765743
theorem B3755807 : Blo 1112627 3755807 := bstep (se 1 (by rfl) ⟨2816855, by rfl⟩ : syracuseStep 3755807 = 5633711) B5633711
theorem B15257651 : Blo 1112627 15257651 := bstep (se 1 (by rfl) ⟨11443238, by rfl⟩ : syracuseStep 15257651 = 22886477) B22886477
theorem B24105833 : Blo 1112627 24105833 := bstep (se 2 (by rfl) ⟨9039687, by rfl⟩ : syracuseStep 24105833 = 18079375) B18079375
theorem B2545771 : Blo 1112627 2545771 := bstep (se 1 (by rfl) ⟨1909328, by rfl⟩ : syracuseStep 2545771 = 3818657) B3818657
theorem B3758561 : Blo 1112627 3758561 := bstep (se 2 (by rfl) ⟨1409460, by rfl⟩ : syracuseStep 3758561 = 2818921) B2818921
theorem B3759263 : Blo 1112627 3759263 := bstep (se 1 (by rfl) ⟨2819447, by rfl⟩ : syracuseStep 3759263 = 5638895) B5638895
theorem B12705011 : Blo 1112627 12705011 := bstep (se 1 (by rfl) ⟨9528758, by rfl⟩ : syracuseStep 12705011 = 19057517) B19057517
theorem B2383643 : Blo 1112627 2383643 := bstep (se 1 (by rfl) ⟨1787732, by rfl⟩ : syracuseStep 2383643 = 3575465) B3575465
theorem B7627459 : Blo 1112627 7627459 := bstep (se 1 (by rfl) ⟨5720594, by rfl⟩ : syracuseStep 7627459 = 11441189) B11441189
theorem B3171743 : Blo 1112627 3171743 := bstep (se 1 (by rfl) ⟨2378807, by rfl⟩ : syracuseStep 3171743 = 4757615) B4757615
theorem B6973883 : Blo 1112627 6973883 := bstep (se 1 (by rfl) ⟨5230412, by rfl⟩ : syracuseStep 6973883 = 10460825) B10460825
theorem B4516991 : Blo 1112627 4516991 := bstep (se 1 (by rfl) ⟨3387743, by rfl⟩ : syracuseStep 4516991 = 6775487) B6775487
theorem B3173543 : Blo 1112627 3173543 := bstep (se 1 (by rfl) ⟨2380157, by rfl⟩ : syracuseStep 3173543 = 4760315) B4760315
theorem B3763583 : Blo 1112627 3763583 := bstep (se 1 (by rfl) ⟨2822687, by rfl⟩ : syracuseStep 3763583 = 5645375) B5645375
theorem B8449595 : Blo 1112627 8449595 := bstep (se 1 (by rfl) ⟨6337196, by rfl⟩ : syracuseStep 8449595 = 12674393) B12674393
theorem B4354975 : Blo 1112627 4354975 := bstep (se 1 (by rfl) ⟨3266231, by rfl⟩ : syracuseStep 4354975 = 6532463) B6532463
theorem B5633387 : Blo 1112627 5633387 := bstep (se 1 (by rfl) ⟨4225040, by rfl⟩ : syracuseStep 5633387 = 8450081) B8450081
theorem B4225223 : Blo 1112627 4225223 := bstep (se 1 (by rfl) ⟨3168917, by rfl⟩ : syracuseStep 4225223 = 6337835) B6337835
theorem B1669403 : Blo 1112627 1669403 := bstep (se 1 (by rfl) ⟨1252052, by rfl⟩ : syracuseStep 1669403 = 2504105) B2504105
theorem B5634359 : Blo 1112627 5634359 := bstep (se 1 (by rfl) ⟨4225769, by rfl⟩ : syracuseStep 5634359 = 8451539) B8451539
theorem B2816471 : Blo 1112627 2816471 := bstep (se 1 (by rfl) ⟨2112353, by rfl⟩ : syracuseStep 2816471 = 4224707) B4224707
theorem B1669607 : Blo 1112627 1669607 := bstep (se 1 (by rfl) ⟨1252205, by rfl⟩ : syracuseStep 1669607 = 2504411) B2504411
theorem B1669679 : Blo 1112627 1669679 := bstep (se 1 (by rfl) ⟨1252259, by rfl⟩ : syracuseStep 1669679 = 2504519) B2504519
theorem B48921185 : Blo 1112627 48921185 := bstep (se 2 (by rfl) ⟨18345444, by rfl⟩ : syracuseStep 48921185 = 36690889) B36690889
theorem B1112687 : Blo 1112627 1112687 := bstep (se 1 (by rfl) ⟨834515, by rfl⟩ : syracuseStep 1112687 = 1669031) B1669031
theorem B3177119 : Blo 1112627 3177119 := bstep (se 1 (by rfl) ⟨2382839, by rfl⟩ : syracuseStep 3177119 = 4765679) B4765679
theorem B1670087 : Blo 1112627 1670087 := bstep (se 1 (by rfl) ⟨1252565, by rfl⟩ : syracuseStep 1670087 = 2505131) B2505131
theorem B3767417 : Blo 1112627 3767417 := bstep (se 2 (by rfl) ⟨1412781, by rfl⟩ : syracuseStep 3767417 = 2825563) B2825563
theorem B1113255 : Blo 1112627 1113255 := bstep (se 1 (by rfl) ⟨834941, by rfl⟩ : syracuseStep 1113255 = 1669883) B1669883
theorem B1113279 : Blo 1112627 1113279 := bstep (se 1 (by rfl) ⟨834959, by rfl⟩ : syracuseStep 1113279 = 1669919) B1669919
theorem B10714319 : Blo 1112627 10714319 := bstep (se 1 (by rfl) ⟨8035739, by rfl⟩ : syracuseStep 10714319 = 16071479) B16071479
theorem B8453483 : Blo 1112627 8453483 := bstep (se 1 (by rfl) ⟨6340112, by rfl⟩ : syracuseStep 8453483 = 12680225) B12680225
theorem B1113627 : Blo 1112627 1113627 := bstep (se 1 (by rfl) ⟨835220, by rfl⟩ : syracuseStep 1113627 = 1670441) B1670441
theorem B10714781 : Blo 1112627 10714781 := bstep (se 3 (by rfl) ⟨2009021, by rfl⟩ : syracuseStep 10714781 = 4018043) B4018043
theorem B1113839 : Blo 1112627 1113839 := bstep (se 1 (by rfl) ⟨835379, by rfl⟩ : syracuseStep 1113839 = 1670759) B1670759
theorem B1114095 : Blo 1112627 1114095 := bstep (se 1 (by rfl) ⟨835571, by rfl⟩ : syracuseStep 1114095 = 1671143) B1671143
theorem B1114159 : Blo 1112627 1114159 := bstep (se 1 (by rfl) ⟨835619, by rfl⟩ : syracuseStep 1114159 = 1671239) B1671239
theorem B1507567 : Blo 1112627 1507567 := bstep (se 1 (by rfl) ⟨1130675, by rfl⟩ : syracuseStep 1507567 = 2261351) B2261351
theorem B1671419 : Blo 1112627 1671419 := bstep (se 1 (by rfl) ⟨1253564, by rfl⟩ : syracuseStep 1671419 = 2507129) B2507129
theorem B1671545 : Blo 1112627 1671545 := bstep (se 2 (by rfl) ⟨626829, by rfl⟩ : syracuseStep 1671545 = 1253659) B1253659
theorem B1671593 : Blo 1112627 1671593 := bstep (se 2 (by rfl) ⟨626847, by rfl⟩ : syracuseStep 1671593 = 1253695) B1253695
theorem B1671911 : Blo 1112627 1671911 := bstep (se 1 (by rfl) ⟨1253933, by rfl⟩ : syracuseStep 1671911 = 2507867) B2507867
theorem B1672283 : Blo 1112627 1672283 := bstep (se 1 (by rfl) ⟨1254212, by rfl⟩ : syracuseStep 1672283 = 2508425) B2508425
theorem B5637275 : Blo 1112627 5637275 := bstep (se 1 (by rfl) ⟨4227956, by rfl⟩ : syracuseStep 5637275 = 8455913) B8455913
theorem B2819519 : Blo 1112627 2819519 := bstep (se 1 (by rfl) ⟨2114639, by rfl⟩ : syracuseStep 2819519 = 4229279) B4229279
theorem B24413687 : Blo 1112627 24413687 := bstep (se 1 (by rfl) ⟨18310265, by rfl⟩ : syracuseStep 24413687 = 36620531) B36620531
theorem B2262583 : Blo 1112627 2262583 := bstep (se 1 (by rfl) ⟨1696937, by rfl⟩ : syracuseStep 2262583 = 3393875) B3393875
theorem B1672841 : Blo 1112627 1672841 := bstep (se 2 (by rfl) ⟨627315, by rfl⟩ : syracuseStep 1672841 = 1254631) B1254631
theorem B1115903 : Blo 1112627 1115903 := bstep (se 1 (by rfl) ⟨836927, by rfl⟩ : syracuseStep 1115903 = 1673855) B1673855
theorem B1115975 : Blo 1112627 1115975 := bstep (se 1 (by rfl) ⟨836981, by rfl⟩ : syracuseStep 1115975 = 1673963) B1673963
theorem B1116287 : Blo 1112627 1116287 := bstep (se 1 (by rfl) ⟨837215, by rfl⟩ : syracuseStep 1116287 = 1674431) B1674431
theorem B1673663 : Blo 1112627 1673663 := bstep (se 1 (by rfl) ⟨1255247, by rfl⟩ : syracuseStep 1673663 = 2510495) B2510495
theorem B1673993 : Blo 1112627 1673993 := bstep (se 2 (by rfl) ⟨627747, by rfl⟩ : syracuseStep 1673993 = 1255495) B1255495
theorem B4756589 : Blo 1112627 4756589 := bstep (se 3 (by rfl) ⟨891860, by rfl⟩ : syracuseStep 4756589 = 1783721) B1783721
theorem B14292935 : Blo 1112627 14292935 := bstep (se 1 (by rfl) ⟨10719701, by rfl⟩ : syracuseStep 14292935 = 21439403) B21439403
theorem B8460287 : Blo 1112627 8460287 := bstep (se 1 (by rfl) ⟨6345215, by rfl⟩ : syracuseStep 8460287 = 12690431) B12690431
theorem B54270647 : Blo 1112627 54270647 := bstep (se 1 (by rfl) ⟨40702985, by rfl⟩ : syracuseStep 54270647 = 81405971) B81405971
theorem B13572967 : Blo 1112627 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B1877647 : Blo 1112627 1877647 := bstep (se 1 (by rfl) ⟨1408235, by rfl⟩ : syracuseStep 1877647 = 2816471) B2816471
theorem B32614123 : Blo 1112627 32614123 := bstep (se 1 (by rfl) ⟨24460592, by rfl⟩ : syracuseStep 32614123 = 48921185) B48921185
theorem B10169945 : Blo 1112627 10169945 := bstep (se 2 (by rfl) ⟨3813729, by rfl⟩ : syracuseStep 10169945 = 7627459) B7627459
theorem B3388159 : Blo 1112627 3388159 := bstep (se 1 (by rfl) ⟨2541119, by rfl⟩ : syracuseStep 3388159 = 5082239) B5082239
theorem B4010951 : Blo 1112627 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B4895839 : Blo 1112627 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B2503871 : Blo 1112627 2503871 := bstep (se 1 (by rfl) ⟨1877903, by rfl⟩ : syracuseStep 2503871 = 3755807) B3755807
theorem B16070555 : Blo 1112627 16070555 := bstep (se 1 (by rfl) ⟨12052916, by rfl⟩ : syracuseStep 16070555 = 24105833) B24105833
theorem B1882831 : Blo 1112627 1882831 := bstep (se 1 (by rfl) ⟨1412123, by rfl⟩ : syracuseStep 1882831 = 2824247) B2824247
theorem B1882919 : Blo 1112627 1882919 := bstep (se 1 (by rfl) ⟨1412189, by rfl⟩ : syracuseStep 1882919 = 2824379) B2824379
theorem B2505707 : Blo 1112627 2505707 := bstep (se 1 (by rfl) ⟨1879280, by rfl⟩ : syracuseStep 2505707 = 3758561) B3758561
theorem B3390761 : Blo 1112627 3390761 := bstep (se 2 (by rfl) ⟨1271535, by rfl⟩ : syracuseStep 3390761 = 2543071) B2543071
theorem B2506175 : Blo 1112627 2506175 := bstep (se 1 (by rfl) ⟨1879631, by rfl⟩ : syracuseStep 2506175 = 3759263) B3759263
theorem B8470007 : Blo 1112627 8470007 := bstep (se 1 (by rfl) ⟨6352505, by rfl⟩ : syracuseStep 8470007 = 12705011) B12705011
theorem B1883803 : Blo 1112627 1883803 := bstep (se 1 (by rfl) ⟨1412852, by rfl⟩ : syracuseStep 1883803 = 2825705) B2825705
theorem B1589095 : Blo 1112627 1589095 := bstep (se 1 (by rfl) ⟨1191821, by rfl⟩ : syracuseStep 1589095 = 2383643) B2383643
theorem B2114495 : Blo 1112627 2114495 := bstep (se 1 (by rfl) ⟨1585871, by rfl⟩ : syracuseStep 2114495 = 3171743) B3171743
theorem B40649701 : Blo 1112627 40649701 := bstep (se 4 (by rfl) ⟨3810909, by rfl⟩ : syracuseStep 40649701 = 7621819) B7621819
theorem B2115695 : Blo 1112627 2115695 := bstep (se 1 (by rfl) ⟨1586771, by rfl⟩ : syracuseStep 2115695 = 3173543) B3173543
theorem B2509055 : Blo 1112627 2509055 := bstep (se 1 (by rfl) ⟨1881791, by rfl⟩ : syracuseStep 2509055 = 3763583) B3763583
theorem B2509289 : Blo 1112627 2509289 := bstep (se 2 (by rfl) ⟨940983, by rfl⟩ : syracuseStep 2509289 = 1881967) B1881967
theorem B3394361 : Blo 1112627 3394361 := bstep (se 2 (by rfl) ⟨1272885, by rfl⟩ : syracuseStep 3394361 = 2545771) B2545771
theorem B3755591 : Blo 1112627 3755591 := bstep (se 1 (by rfl) ⟨2816693, by rfl⟩ : syracuseStep 3755591 = 5633387) B5633387
theorem B3756239 : Blo 1112627 3756239 := bstep (se 1 (by rfl) ⟨2817179, by rfl⟩ : syracuseStep 3756239 = 5634359) B5634359
theorem B2118079 : Blo 1112627 2118079 := bstep (se 1 (by rfl) ⟨1588559, by rfl⟩ : syracuseStep 2118079 = 3177119) B3177119
theorem B2511611 : Blo 1112627 2511611 := bstep (se 1 (by rfl) ⟨1883708, by rfl⟩ : syracuseStep 2511611 = 3767417) B3767417
theorem B103044545 : Blo 1112627 103044545 := bstep (se 2 (by rfl) ⟨38641704, by rfl⟩ : syracuseStep 103044545 = 77283409) B77283409
theorem B40687069 : Blo 1112627 40687069 := bstep (se 3 (by rfl) ⟨7628825, by rfl⟩ : syracuseStep 40687069 = 15257651) B15257651
theorem B3757535 : Blo 1112627 3757535 := bstep (se 1 (by rfl) ⟨2818151, by rfl⟩ : syracuseStep 3757535 = 5636303) B5636303
theorem B2119135 : Blo 1112627 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B3758075 : Blo 1112627 3758075 := bstep (se 1 (by rfl) ⟨2818556, by rfl⟩ : syracuseStep 3758075 = 5637113) B5637113
theorem B3758399 : Blo 1112627 3758399 := bstep (se 1 (by rfl) ⟨2818799, by rfl⟩ : syracuseStep 3758399 = 5637599) B5637599
theorem B3758507 : Blo 1112627 3758507 := bstep (se 1 (by rfl) ⟨2818880, by rfl⟩ : syracuseStep 3758507 = 5637761) B5637761
theorem B3168895 : Blo 1112627 3168895 := bstep (se 1 (by rfl) ⟨2376671, by rfl⟩ : syracuseStep 3168895 = 4753343) B4753343
theorem B4024201 : Blo 1112627 4024201 := bstep (se 2 (by rfl) ⟨1509075, by rfl⟩ : syracuseStep 4024201 = 3018151) B3018151
theorem B23226533 : Blo 1112627 23226533 := bstep (se 4 (by rfl) ⟨2177487, by rfl⟩ : syracuseStep 23226533 = 4354975) B4354975
theorem B21424945 : Blo 1112627 21424945 := bstep (se 2 (by rfl) ⟨8034354, by rfl⟩ : syracuseStep 21424945 = 16068709) B16068709
theorem B27094151 : Blo 1112627 27094151 := bstep (se 1 (by rfl) ⟨20320613, by rfl⟩ : syracuseStep 27094151 = 40641227) B40641227
theorem B21720307 : Blo 1112627 21720307 := bstep (se 1 (by rfl) ⟨16290230, by rfl⟩ : syracuseStep 21720307 = 32580461) B32580461
theorem B3763691 : Blo 1112627 3763691 := bstep (se 1 (by rfl) ⟨2822768, by rfl⟩ : syracuseStep 3763691 = 5645537) B5645537
theorem B42790841 : Blo 1112627 42790841 := bstep (se 2 (by rfl) ⟨16046565, by rfl⟩ : syracuseStep 42790841 = 32093131) B32093131
theorem B4649255 : Blo 1112627 4649255 := bstep (se 1 (by rfl) ⟨3486941, by rfl⟩ : syracuseStep 4649255 = 6973883) B6973883
theorem B3011327 : Blo 1112627 3011327 := bstep (se 1 (by rfl) ⟨2258495, by rfl⟩ : syracuseStep 3011327 = 4516991) B4516991
theorem B3765203 : Blo 1112627 3765203 := bstep (se 1 (by rfl) ⟨2823902, by rfl⟩ : syracuseStep 3765203 = 5647805) B5647805
theorem B5633063 : Blo 1112627 5633063 := bstep (se 1 (by rfl) ⟨4224797, by rfl⟩ : syracuseStep 5633063 = 8449595) B8449595
theorem B13563425 : Blo 1112627 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B3569903 : Blo 1112627 3569903 := bstep (se 1 (by rfl) ⟨2677427, by rfl⟩ : syracuseStep 3569903 = 5354855) B5354855
theorem B1669799 : Blo 1112627 1669799 := bstep (se 1 (by rfl) ⟨1252349, by rfl⟩ : syracuseStep 1669799 = 2504699) B2504699
theorem B3767039 : Blo 1112627 3767039 := bstep (se 1 (by rfl) ⟨2825279, by rfl⟩ : syracuseStep 3767039 = 5650559) B5650559
theorem B2816815 : Blo 1112627 2816815 := bstep (se 1 (by rfl) ⟨2112611, by rfl⟩ : syracuseStep 2816815 = 4225223) B4225223
theorem B1112935 : Blo 1112627 1112935 := bstep (se 1 (by rfl) ⟨834701, by rfl⟩ : syracuseStep 1112935 = 1669403) B1669403
theorem B1669991 : Blo 1112627 1669991 := bstep (se 1 (by rfl) ⟨1252493, by rfl⟩ : syracuseStep 1669991 = 2504987) B2504987
theorem B1670009 : Blo 1112627 1670009 := bstep (se 2 (by rfl) ⟨626253, by rfl⟩ : syracuseStep 1670009 = 1252507) B1252507
theorem B1670057 : Blo 1112627 1670057 := bstep (se 2 (by rfl) ⟨626271, by rfl⟩ : syracuseStep 1670057 = 1252543) B1252543
theorem B1113071 : Blo 1112627 1113071 := bstep (se 1 (by rfl) ⟨834803, by rfl⟩ : syracuseStep 1113071 = 1669607) B1669607
theorem B1113119 : Blo 1112627 1113119 := bstep (se 1 (by rfl) ⟨834839, by rfl⟩ : syracuseStep 1113119 = 1669679) B1669679
theorem B1113391 : Blo 1112627 1113391 := bstep (se 1 (by rfl) ⟨835043, by rfl⟩ : syracuseStep 1113391 = 1670087) B1670087
theorem B7142879 : Blo 1112627 7142879 := bstep (se 1 (by rfl) ⟨5357159, by rfl⟩ : syracuseStep 7142879 = 10714319) B10714319
theorem B3767849 : Blo 1112627 3767849 := bstep (se 2 (by rfl) ⟨1412943, by rfl⟩ : syracuseStep 3767849 = 2825887) B2825887
theorem B5635655 : Blo 1112627 5635655 := bstep (se 1 (by rfl) ⟨4226741, by rfl⟩ : syracuseStep 5635655 = 8453483) B8453483
theorem B7143187 : Blo 1112627 7143187 := bstep (se 1 (by rfl) ⟨5357390, by rfl⟩ : syracuseStep 7143187 = 10714781) B10714781
theorem B1114279 : Blo 1112627 1114279 := bstep (se 1 (by rfl) ⟨835709, by rfl⟩ : syracuseStep 1114279 = 1671419) B1671419
theorem B1114363 : Blo 1112627 1114363 := bstep (se 1 (by rfl) ⟨835772, by rfl⟩ : syracuseStep 1114363 = 1671545) B1671545
theorem B1114395 : Blo 1112627 1114395 := bstep (se 1 (by rfl) ⟨835796, by rfl⟩ : syracuseStep 1114395 = 1671593) B1671593
theorem B1114607 : Blo 1112627 1114607 := bstep (se 1 (by rfl) ⟨835955, by rfl⟩ : syracuseStep 1114607 = 1671911) B1671911
theorem B1409663 : Blo 1112627 1409663 := bstep (se 1 (by rfl) ⟨1057247, by rfl⟩ : syracuseStep 1409663 = 2114495) B2114495
theorem B1114855 : Blo 1112627 1114855 := bstep (se 1 (by rfl) ⟨836141, by rfl⟩ : syracuseStep 1114855 = 1672283) B1672283
theorem B1115227 : Blo 1112627 1115227 := bstep (se 1 (by rfl) ⟨836420, by rfl⟩ : syracuseStep 1115227 = 1672841) B1672841
theorem B54199601 : Blo 1112627 54199601 := bstep (se 2 (by rfl) ⟨20324850, by rfl⟩ : syracuseStep 54199601 = 40649701) B40649701
theorem B1410463 : Blo 1112627 1410463 := bstep (se 1 (by rfl) ⟨1057847, by rfl⟩ : syracuseStep 1410463 = 2115695) B2115695
theorem B1672703 : Blo 1112627 1672703 := bstep (se 1 (by rfl) ⟨1254527, by rfl⟩ : syracuseStep 1672703 = 2509055) B2509055
theorem B1115775 : Blo 1112627 1115775 := bstep (se 1 (by rfl) ⟨836831, by rfl⟩ : syracuseStep 1115775 = 1673663) B1673663
theorem B1672859 : Blo 1112627 1672859 := bstep (se 1 (by rfl) ⟨1254644, by rfl⟩ : syracuseStep 1672859 = 2509289) B2509289
theorem B1115995 : Blo 1112627 1115995 := bstep (se 1 (by rfl) ⟨836996, by rfl⟩ : syracuseStep 1115995 = 1673993) B1673993
theorem B2262907 : Blo 1112627 2262907 := bstep (se 1 (by rfl) ⟨1697180, by rfl⟩ : syracuseStep 2262907 = 3394361) B3394361
theorem B3016777 : Blo 1112627 3016777 := bstep (se 2 (by rfl) ⟨1131291, by rfl⟩ : syracuseStep 3016777 = 2262583) B2262583
theorem B43485497 : Blo 1112627 43485497 := bstep (se 2 (by rfl) ⟨16307061, by rfl⟩ : syracuseStep 43485497 = 32614123) B32614123
theorem B1674407 : Blo 1112627 1674407 := bstep (se 1 (by rfl) ⟨1255805, by rfl⟩ : syracuseStep 1674407 = 2511611) B2511611
theorem B5640191 : Blo 1112627 5640191 := bstep (se 1 (by rfl) ⟨4230143, by rfl⟩ : syracuseStep 5640191 = 8460287) B8460287
theorem B36180431 : Blo 1112627 36180431 := bstep (se 1 (by rfl) ⟨27135323, by rfl⟩ : syracuseStep 36180431 = 54270647) B54270647
theorem B2824105 : Blo 1112627 2824105 := bstep (se 2 (by rfl) ⟨1059039, by rfl⟩ : syracuseStep 2824105 = 2118079) B2118079
theorem B6527785 : Blo 1112627 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B2825513 : Blo 1112627 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B18062767 : Blo 1112627 18062767 := bstep (se 1 (by rfl) ⟨13547075, by rfl⟩ : syracuseStep 18062767 = 27094151) B27094151
theorem B2007551 : Blo 1112627 2007551 := bstep (se 1 (by rfl) ⟨1505663, by rfl⟩ : syracuseStep 2007551 = 3011327) B3011327
theorem B18097289 : Blo 1112627 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B1255279 : Blo 1112627 1255279 := bstep (se 1 (by rfl) ⟨941459, by rfl⟩ : syracuseStep 1255279 = 1882919) B1882919
theorem B4761919 : Blo 1112627 4761919 := bstep (se 1 (by rfl) ⟨3571439, by rfl⟩ : syracuseStep 4761919 = 7142879) B7142879
theorem B5646671 : Blo 1112627 5646671 := bstep (se 1 (by rfl) ⟨4235003, by rfl⟩ : syracuseStep 5646671 = 8470007) B8470007
theorem B2010089 : Blo 1112627 2010089 := bstep (se 2 (by rfl) ⟨753783, by rfl⟩ : syracuseStep 2010089 = 1507567) B1507567
theorem B1879679 : Blo 1112627 1879679 := bstep (se 1 (by rfl) ⟨1409759, by rfl⟩ : syracuseStep 1879679 = 2819519) B2819519
theorem B2503529 : Blo 1112627 2503529 := bstep (se 2 (by rfl) ⟨938823, by rfl⟩ : syracuseStep 2503529 = 1877647) B1877647
theorem B2503727 : Blo 1112627 2503727 := bstep (se 1 (by rfl) ⟨1877795, by rfl⟩ : syracuseStep 2503727 = 3755591) B3755591
theorem B2504159 : Blo 1112627 2504159 := bstep (se 1 (by rfl) ⟨1878119, by rfl⟩ : syracuseStep 2504159 = 3756239) B3756239
theorem B68696363 : Blo 1112627 68696363 := bstep (se 1 (by rfl) ⟨51522272, by rfl⟩ : syracuseStep 68696363 = 103044545) B103044545
theorem B2505023 : Blo 1112627 2505023 := bstep (se 1 (by rfl) ⟨1878767, by rfl⟩ : syracuseStep 2505023 = 3757535) B3757535
theorem B2505383 : Blo 1112627 2505383 := bstep (se 1 (by rfl) ⟨1879037, by rfl⟩ : syracuseStep 2505383 = 3758075) B3758075
theorem B2505599 : Blo 1112627 2505599 := bstep (se 1 (by rfl) ⟨1879199, by rfl⟩ : syracuseStep 2505599 = 3758399) B3758399
theorem B2505671 : Blo 1112627 2505671 := bstep (se 1 (by rfl) ⟨1879253, by rfl⟩ : syracuseStep 2505671 = 3758507) B3758507
theorem B15484355 : Blo 1112627 15484355 := bstep (se 1 (by rfl) ⟨11613266, by rfl⟩ : syracuseStep 15484355 = 23226533) B23226533
theorem B54249425 : Blo 1112627 54249425 := bstep (se 2 (by rfl) ⟨20343534, by rfl⟩ : syracuseStep 54249425 = 40687069) B40687069
theorem B2509127 : Blo 1112627 2509127 := bstep (se 1 (by rfl) ⟨1881845, by rfl⟩ : syracuseStep 2509127 = 3763691) B3763691
theorem B28527227 : Blo 1112627 28527227 := bstep (se 1 (by rfl) ⟨21395420, by rfl⟩ : syracuseStep 28527227 = 42790841) B42790841
theorem B3099503 : Blo 1112627 3099503 := bstep (se 1 (by rfl) ⟨2324627, by rfl⟩ : syracuseStep 3099503 = 4649255) B4649255
theorem B2673967 : Blo 1112627 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B2510135 : Blo 1112627 2510135 := bstep (se 1 (by rfl) ⟨1882601, by rfl⟩ : syracuseStep 2510135 = 3765203) B3765203
theorem B3755375 : Blo 1112627 3755375 := bstep (se 1 (by rfl) ⟨2816531, by rfl⟩ : syracuseStep 3755375 = 5633063) B5633063
theorem B2510441 : Blo 1112627 2510441 := bstep (se 2 (by rfl) ⟨941415, by rfl⟩ : syracuseStep 2510441 = 1882831) B1882831
theorem B3755753 : Blo 1112627 3755753 := bstep (se 2 (by rfl) ⟨1408407, by rfl⟩ : syracuseStep 3755753 = 2816815) B2816815
theorem B2379935 : Blo 1112627 2379935 := bstep (se 1 (by rfl) ⟨1784951, by rfl⟩ : syracuseStep 2379935 = 3569903) B3569903
theorem B2511359 : Blo 1112627 2511359 := bstep (se 1 (by rfl) ⟨1883519, by rfl⟩ : syracuseStep 2511359 = 3767039) B3767039
theorem B2511737 : Blo 1112627 2511737 := bstep (se 2 (by rfl) ⟨941901, by rfl⟩ : syracuseStep 2511737 = 1883803) B1883803
theorem B9524249 : Blo 1112627 9524249 := bstep (se 2 (by rfl) ⟨3571593, by rfl⟩ : syracuseStep 9524249 = 7143187) B7143187
theorem B2511899 : Blo 1112627 2511899 := bstep (se 1 (by rfl) ⟨1883924, by rfl⟩ : syracuseStep 2511899 = 3767849) B3767849
theorem B3757103 : Blo 1112627 3757103 := bstep (se 1 (by rfl) ⟨2817827, by rfl⟩ : syracuseStep 3757103 = 5635655) B5635655
theorem B2118793 : Blo 1112627 2118793 := bstep (se 2 (by rfl) ⟨794547, by rfl⟩ : syracuseStep 2118793 = 1589095) B1589095
theorem B3758183 : Blo 1112627 3758183 := bstep (se 1 (by rfl) ⟨2818637, by rfl⟩ : syracuseStep 3758183 = 5637275) B5637275
theorem B16275791 : Blo 1112627 16275791 := bstep (se 1 (by rfl) ⟨12206843, by rfl⟩ : syracuseStep 16275791 = 24413687) B24413687
theorem B5365601 : Blo 1112627 5365601 := bstep (se 2 (by rfl) ⟨2012100, by rfl⟩ : syracuseStep 5365601 = 4024201) B4024201
theorem B3171059 : Blo 1112627 3171059 := bstep (se 1 (by rfl) ⟨2378294, by rfl⟩ : syracuseStep 3171059 = 4756589) B4756589
theorem B28566593 : Blo 1112627 28566593 := bstep (se 2 (by rfl) ⟨10712472, by rfl⟩ : syracuseStep 28566593 = 21424945) B21424945
theorem B9528623 : Blo 1112627 9528623 := bstep (se 1 (by rfl) ⟨7146467, by rfl⟩ : syracuseStep 9528623 = 14292935) B14292935
theorem B28960409 : Blo 1112627 28960409 := bstep (se 2 (by rfl) ⟨10860153, by rfl⟩ : syracuseStep 28960409 = 21720307) B21720307
theorem B4517545 : Blo 1112627 4517545 := bstep (se 2 (by rfl) ⟨1694079, by rfl⟩ : syracuseStep 4517545 = 3388159) B3388159
theorem B6779963 : Blo 1112627 6779963 := bstep (se 1 (by rfl) ⟨5084972, by rfl⟩ : syracuseStep 6779963 = 10169945) B10169945
theorem B9042029 : Blo 1112627 9042029 := bstep (se 3 (by rfl) ⟨1695380, by rfl⟩ : syracuseStep 9042029 = 3390761) B3390761
theorem B1669247 : Blo 1112627 1669247 := bstep (se 1 (by rfl) ⟨1251935, by rfl⟩ : syracuseStep 1669247 = 2503871) B2503871
theorem B4225193 : Blo 1112627 4225193 := bstep (se 2 (by rfl) ⟨1584447, by rfl⟩ : syracuseStep 4225193 = 3168895) B3168895
theorem B9042283 : Blo 1112627 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B10713703 : Blo 1112627 10713703 := bstep (se 1 (by rfl) ⟨8035277, by rfl⟩ : syracuseStep 10713703 = 16070555) B16070555
theorem B1113199 : Blo 1112627 1113199 := bstep (se 1 (by rfl) ⟨834899, by rfl⟩ : syracuseStep 1113199 = 1669799) B1669799
theorem B1113327 : Blo 1112627 1113327 := bstep (se 1 (by rfl) ⟨834995, by rfl⟩ : syracuseStep 1113327 = 1669991) B1669991
theorem B1113339 : Blo 1112627 1113339 := bstep (se 1 (by rfl) ⟨835004, by rfl⟩ : syracuseStep 1113339 = 1670009) B1670009
theorem B1113371 : Blo 1112627 1113371 := bstep (se 1 (by rfl) ⟨835028, by rfl⟩ : syracuseStep 1113371 = 1670057) B1670057
theorem B1670471 : Blo 1112627 1670471 := bstep (se 1 (by rfl) ⟨1252853, by rfl⟩ : syracuseStep 1670471 = 2505707) B2505707
theorem B1670783 : Blo 1112627 1670783 := bstep (se 1 (by rfl) ⟨1253087, by rfl⟩ : syracuseStep 1670783 = 2506175) B2506175
theorem B10322903 : Blo 1112627 10322903 := bstep (se 1 (by rfl) ⟨7742177, by rfl⟩ : syracuseStep 10322903 = 15484355) B15484355
theorem B1115135 : Blo 1112627 1115135 := bstep (se 1 (by rfl) ⟨836351, by rfl⟩ : syracuseStep 1115135 = 1672703) B1672703
theorem B1115239 : Blo 1112627 1115239 := bstep (se 1 (by rfl) ⟨836429, by rfl⟩ : syracuseStep 1115239 = 1672859) B1672859
theorem B1672751 : Blo 1112627 1672751 := bstep (se 1 (by rfl) ⟨1254563, by rfl⟩ : syracuseStep 1672751 = 2509127) B2509127
theorem B1116271 : Blo 1112627 1116271 := bstep (se 1 (by rfl) ⟨837203, by rfl⟩ : syracuseStep 1116271 = 1674407) B1674407
theorem B1673423 : Blo 1112627 1673423 := bstep (se 1 (by rfl) ⟨1255067, by rfl⟩ : syracuseStep 1673423 = 2510135) B2510135
theorem B1673627 : Blo 1112627 1673627 := bstep (se 1 (by rfl) ⟨1255220, by rfl⟩ : syracuseStep 1673627 = 2510441) B2510441
theorem B1673705 : Blo 1112627 1673705 := bstep (se 2 (by rfl) ⟨627639, by rfl⟩ : syracuseStep 1673705 = 1255279) B1255279
theorem B24120287 : Blo 1112627 24120287 := bstep (se 1 (by rfl) ⟨18090215, by rfl⟩ : syracuseStep 24120287 = 36180431) B36180431
theorem B1674239 : Blo 1112627 1674239 := bstep (se 1 (by rfl) ⟨1255679, by rfl⟩ : syracuseStep 1674239 = 2511359) B2511359
theorem B1674491 : Blo 1112627 1674491 := bstep (se 1 (by rfl) ⟨1255868, by rfl⟩ : syracuseStep 1674491 = 2511737) B2511737
theorem B1674599 : Blo 1112627 1674599 := bstep (se 1 (by rfl) ⟨1255949, by rfl⟩ : syracuseStep 1674599 = 2511899) B2511899
theorem B10850527 : Blo 1112627 10850527 := bstep (se 1 (by rfl) ⟨8137895, by rfl⟩ : syracuseStep 10850527 = 16275791) B16275791
theorem B3577067 : Blo 1112627 3577067 := bstep (se 1 (by rfl) ⟨2682800, by rfl⟩ : syracuseStep 3577067 = 5365601) B5365601
theorem B19044395 : Blo 1112627 19044395 := bstep (se 1 (by rfl) ⟨14283296, by rfl⟩ : syracuseStep 19044395 = 28566593) B28566593
theorem B12064859 : Blo 1112627 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B19306939 : Blo 1112627 19306939 := bstep (se 1 (by rfl) ⟨14480204, by rfl⟩ : syracuseStep 19306939 = 28960409) B28960409
theorem B2825057 : Blo 1112627 2825057 := bstep (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) B2118793
theorem B8265341 : Blo 1112627 8265341 := bstep (se 3 (by rfl) ⟨1549751, by rfl⟩ : syracuseStep 8265341 = 3099503) B3099503
theorem B1253119 : Blo 1112627 1253119 := bstep (se 1 (by rfl) ⟨939839, by rfl⟩ : syracuseStep 1253119 = 1879679) B1879679
theorem B12068837 : Blo 1112627 12068837 := bstep (se 4 (by rfl) ⟨1131453, by rfl⟩ : syracuseStep 12068837 = 2262907) B2262907
theorem B5353469 : Blo 1112627 5353469 := bstep (se 3 (by rfl) ⟨1003775, by rfl⟩ : syracuseStep 5353469 = 2007551) B2007551
theorem B19018151 : Blo 1112627 19018151 := bstep (se 1 (by rfl) ⟨14263613, by rfl⟩ : syracuseStep 19018151 = 28527227) B28527227
theorem B1880617 : Blo 1112627 1880617 := bstep (se 2 (by rfl) ⟨705231, by rfl⟩ : syracuseStep 1880617 = 1410463) B1410463
theorem B2503583 : Blo 1112627 2503583 := bstep (se 1 (by rfl) ⟨1877687, by rfl⟩ : syracuseStep 2503583 = 3755375) B3755375
theorem B2503835 : Blo 1112627 2503835 := bstep (se 1 (by rfl) ⟨1877876, by rfl⟩ : syracuseStep 2503835 = 3755753) B3755753
theorem B1586623 : Blo 1112627 1586623 := bstep (se 1 (by rfl) ⟨1189967, by rfl⟩ : syracuseStep 1586623 = 2379935) B2379935
theorem B2504735 : Blo 1112627 2504735 := bstep (se 1 (by rfl) ⟨1878551, by rfl⟩ : syracuseStep 2504735 = 3757103) B3757103
theorem B2505455 : Blo 1112627 2505455 := bstep (se 1 (by rfl) ⟨1879091, by rfl⟩ : syracuseStep 2505455 = 3758183) B3758183
theorem B1883675 : Blo 1112627 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B2114039 : Blo 1112627 2114039 := bstep (se 1 (by rfl) ⟨1585529, by rfl⟩ : syracuseStep 2114039 = 3171059) B3171059
theorem B8703713 : Blo 1112627 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B45797575 : Blo 1112627 45797575 := bstep (se 1 (by rfl) ⟨34348181, by rfl⟩ : syracuseStep 45797575 = 68696363) B68696363
theorem B36133067 : Blo 1112627 36133067 := bstep (se 1 (by rfl) ⟨27099800, by rfl⟩ : syracuseStep 36133067 = 54199601) B54199601
theorem B36166283 : Blo 1112627 36166283 := bstep (se 1 (by rfl) ⟨27124712, by rfl⟩ : syracuseStep 36166283 = 54249425) B54249425
theorem B28990331 : Blo 1112627 28990331 := bstep (se 1 (by rfl) ⟨21742748, by rfl⟩ : syracuseStep 28990331 = 43485497) B43485497
theorem B3759101 : Blo 1112627 3759101 := bstep (se 3 (by rfl) ⟨704831, by rfl⟩ : syracuseStep 3759101 = 1409663) B1409663
theorem B3760127 : Blo 1112627 3760127 := bstep (se 1 (by rfl) ⟨2820095, by rfl⟩ : syracuseStep 3760127 = 5640191) B5640191
theorem B4022369 : Blo 1112627 4022369 := bstep (se 2 (by rfl) ⟨1508388, by rfl⟩ : syracuseStep 4022369 = 3016777) B3016777
theorem B6349225 : Blo 1112627 6349225 := bstep (se 2 (by rfl) ⟨2380959, by rfl⟩ : syracuseStep 6349225 = 4761919) B4761919
theorem B6349499 : Blo 1112627 6349499 := bstep (se 1 (by rfl) ⟨4762124, by rfl⟩ : syracuseStep 6349499 = 9524249) B9524249
theorem B3565289 : Blo 1112627 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B6023393 : Blo 1112627 6023393 := bstep (se 2 (by rfl) ⟨2258772, by rfl⟩ : syracuseStep 6023393 = 4517545) B4517545
theorem B6352415 : Blo 1112627 6352415 := bstep (se 1 (by rfl) ⟨4764311, by rfl⟩ : syracuseStep 6352415 = 9528623) B9528623
theorem B3764447 : Blo 1112627 3764447 := bstep (se 1 (by rfl) ⟨2823335, by rfl⟩ : syracuseStep 3764447 = 5646671) B5646671
theorem B1340059 : Blo 1112627 1340059 := bstep (se 1 (by rfl) ⟨1005044, by rfl⟩ : syracuseStep 1340059 = 2010089) B2010089
theorem B3765473 : Blo 1112627 3765473 := bstep (se 2 (by rfl) ⟨1412052, by rfl⟩ : syracuseStep 3765473 = 2824105) B2824105
theorem B12056377 : Blo 1112627 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B1669019 : Blo 1112627 1669019 := bstep (se 1 (by rfl) ⟨1251764, by rfl⟩ : syracuseStep 1669019 = 2503529) B2503529
theorem B1669151 : Blo 1112627 1669151 := bstep (se 1 (by rfl) ⟨1251863, by rfl⟩ : syracuseStep 1669151 = 2503727) B2503727
theorem B4519975 : Blo 1112627 4519975 := bstep (se 1 (by rfl) ⟨3389981, by rfl⟩ : syracuseStep 4519975 = 6779963) B6779963
theorem B14284937 : Blo 1112627 14284937 := bstep (se 2 (by rfl) ⟨5356851, by rfl⟩ : syracuseStep 14284937 = 10713703) B10713703
theorem B1669439 : Blo 1112627 1669439 := bstep (se 1 (by rfl) ⟨1252079, by rfl⟩ : syracuseStep 1669439 = 2504159) B2504159
theorem B6028019 : Blo 1112627 6028019 := bstep (se 1 (by rfl) ⟨4521014, by rfl⟩ : syracuseStep 6028019 = 9042029) B9042029
theorem B1112831 : Blo 1112627 1112831 := bstep (se 1 (by rfl) ⟨834623, by rfl⟩ : syracuseStep 1112831 = 1669247) B1669247
theorem B2816795 : Blo 1112627 2816795 := bstep (se 1 (by rfl) ⟨2112596, by rfl⟩ : syracuseStep 2816795 = 4225193) B4225193
theorem B1670015 : Blo 1112627 1670015 := bstep (se 1 (by rfl) ⟨1252511, by rfl⟩ : syracuseStep 1670015 = 2505023) B2505023
theorem B1670255 : Blo 1112627 1670255 := bstep (se 1 (by rfl) ⟨1252691, by rfl⟩ : syracuseStep 1670255 = 2505383) B2505383
theorem B24083689 : Blo 1112627 24083689 := bstep (se 2 (by rfl) ⟨9031383, by rfl⟩ : syracuseStep 24083689 = 18062767) B18062767
theorem B1670399 : Blo 1112627 1670399 := bstep (se 1 (by rfl) ⟨1252799, by rfl⟩ : syracuseStep 1670399 = 2505599) B2505599
theorem B1670447 : Blo 1112627 1670447 := bstep (se 1 (by rfl) ⟨1252835, by rfl⟩ : syracuseStep 1670447 = 2505671) B2505671
theorem B1113647 : Blo 1112627 1113647 := bstep (se 1 (by rfl) ⟨835235, by rfl⟩ : syracuseStep 1113647 = 1670471) B1670471
theorem B1113855 : Blo 1112627 1113855 := bstep (se 1 (by rfl) ⟨835391, by rfl⟩ : syracuseStep 1113855 = 1670783) B1670783
theorem B6881935 : Blo 1112627 6881935 := bstep (se 1 (by rfl) ⟨5161451, by rfl⟩ : syracuseStep 6881935 = 10322903) B10322903
theorem B1115167 : Blo 1112627 1115167 := bstep (se 1 (by rfl) ⟨836375, by rfl⟩ : syracuseStep 1115167 = 1672751) B1672751
theorem B5637437 : Blo 1112627 5637437 := bstep (se 3 (by rfl) ⟨1057019, by rfl⟩ : syracuseStep 5637437 = 2114039) B2114039
theorem B1115615 : Blo 1112627 1115615 := bstep (se 1 (by rfl) ⟨836711, by rfl⟩ : syracuseStep 1115615 = 1673423) B1673423
theorem B1115751 : Blo 1112627 1115751 := bstep (se 1 (by rfl) ⟨836813, by rfl⟩ : syracuseStep 1115751 = 1673627) B1673627
theorem B1115803 : Blo 1112627 1115803 := bstep (se 1 (by rfl) ⟨836852, by rfl⟩ : syracuseStep 1115803 = 1673705) B1673705
theorem B1116159 : Blo 1112627 1116159 := bstep (se 1 (by rfl) ⟨837119, by rfl⟩ : syracuseStep 1116159 = 1674239) B1674239
theorem B1116327 : Blo 1112627 1116327 := bstep (se 1 (by rfl) ⟨837245, by rfl⟩ : syracuseStep 1116327 = 1674491) B1674491
theorem B1116399 : Blo 1112627 1116399 := bstep (se 1 (by rfl) ⟨837299, by rfl⟩ : syracuseStep 1116399 = 1674599) B1674599
theorem B24088711 : Blo 1112627 24088711 := bstep (se 1 (by rfl) ⟨18066533, by rfl⟩ : syracuseStep 24088711 = 36133067) B36133067
theorem B5510227 : Blo 1112627 5510227 := bstep (se 1 (by rfl) ⟨4132670, by rfl⟩ : syracuseStep 5510227 = 8265341) B8265341
theorem B4232999 : Blo 1112627 4232999 := bstep (se 1 (by rfl) ⟨3174749, by rfl⟩ : syracuseStep 4232999 = 6349499) B6349499
theorem B4234943 : Blo 1112627 4234943 := bstep (se 1 (by rfl) ⟨3176207, by rfl⟩ : syracuseStep 4234943 = 6352415) B6352415
theorem B1877863 : Blo 1112627 1877863 := bstep (se 1 (by rfl) ⟨1408397, by rfl⟩ : syracuseStep 1877863 = 2816795) B2816795
theorem B23209901 : Blo 1112627 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B1255783 : Blo 1112627 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B8465633 : Blo 1112627 8465633 := bstep (se 2 (by rfl) ⟨3174612, by rfl⟩ : syracuseStep 8465633 = 6349225) B6349225
theorem B12696263 : Blo 1112627 12696263 := bstep (se 1 (by rfl) ⟨9522197, by rfl⟩ : syracuseStep 12696263 = 19044395) B19044395
theorem B8043239 : Blo 1112627 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B1883371 : Blo 1112627 1883371 := bstep (se 1 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 1883371 = 2825057) B2825057
theorem B2506067 : Blo 1112627 2506067 := bstep (se 1 (by rfl) ⟨1879550, by rfl⟩ : syracuseStep 2506067 = 3759101) B3759101
theorem B2506751 : Blo 1112627 2506751 := bstep (se 1 (by rfl) ⟨1880063, by rfl⟩ : syracuseStep 2506751 = 3760127) B3760127
theorem B61063433 : Blo 1112627 61063433 := bstep (se 2 (by rfl) ⟨22898787, by rfl⟩ : syracuseStep 61063433 = 45797575) B45797575
theorem B14467369 : Blo 1112627 14467369 := bstep (se 2 (by rfl) ⟨5425263, by rfl⟩ : syracuseStep 14467369 = 10850527) B10850527
theorem B2507489 : Blo 1112627 2507489 := bstep (se 2 (by rfl) ⟨940308, by rfl⟩ : syracuseStep 2507489 = 1880617) B1880617
theorem B1786745 : Blo 1112627 1786745 := bstep (se 2 (by rfl) ⟨670029, by rfl⟩ : syracuseStep 1786745 = 1340059) B1340059
theorem B2376859 : Blo 1112627 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B8045891 : Blo 1112627 8045891 := bstep (se 1 (by rfl) ⟨6034418, by rfl⟩ : syracuseStep 8045891 = 12068837) B12068837
theorem B4015595 : Blo 1112627 4015595 := bstep (se 1 (by rfl) ⟨3011696, by rfl⟩ : syracuseStep 4015595 = 6023393) B6023393
theorem B2115497 : Blo 1112627 2115497 := bstep (se 2 (by rfl) ⟨793311, by rfl⟩ : syracuseStep 2115497 = 1586623) B1586623
theorem B16075169 : Blo 1112627 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B2509631 : Blo 1112627 2509631 := bstep (se 1 (by rfl) ⟨1882223, by rfl⟩ : syracuseStep 2509631 = 3764447) B3764447
theorem B25742585 : Blo 1112627 25742585 := bstep (se 2 (by rfl) ⟨9653469, by rfl⟩ : syracuseStep 25742585 = 19306939) B19306939
theorem B2510315 : Blo 1112627 2510315 := bstep (se 1 (by rfl) ⟨1882736, by rfl⟩ : syracuseStep 2510315 = 3765473) B3765473
theorem B9523291 : Blo 1112627 9523291 := bstep (se 1 (by rfl) ⟨7142468, by rfl⟩ : syracuseStep 9523291 = 14284937) B14284937
theorem B4018679 : Blo 1112627 4018679 := bstep (se 1 (by rfl) ⟨3014009, by rfl⟩ : syracuseStep 4018679 = 6028019) B6028019
theorem B16080191 : Blo 1112627 16080191 := bstep (se 1 (by rfl) ⟨12060143, by rfl⟩ : syracuseStep 16080191 = 24120287) B24120287
theorem B2384711 : Blo 1112627 2384711 := bstep (se 1 (by rfl) ⟨1788533, by rfl⟩ : syracuseStep 2384711 = 3577067) B3577067
theorem B24110855 : Blo 1112627 24110855 := bstep (se 1 (by rfl) ⟨18083141, by rfl⟩ : syracuseStep 24110855 = 36166283) B36166283
theorem B19326887 : Blo 1112627 19326887 := bstep (se 1 (by rfl) ⟨14495165, by rfl⟩ : syracuseStep 19326887 = 28990331) B28990331
theorem B2681579 : Blo 1112627 2681579 := bstep (se 1 (by rfl) ⟨2011184, by rfl⟩ : syracuseStep 2681579 = 4022369) B4022369
theorem B3568979 : Blo 1112627 3568979 := bstep (se 1 (by rfl) ⟨2676734, by rfl⟩ : syracuseStep 3568979 = 5353469) B5353469
theorem B6026633 : Blo 1112627 6026633 := bstep (se 2 (by rfl) ⟨2259987, by rfl⟩ : syracuseStep 6026633 = 4519975) B4519975
theorem B12678767 : Blo 1112627 12678767 := bstep (se 1 (by rfl) ⟨9509075, by rfl⟩ : syracuseStep 12678767 = 19018151) B19018151
theorem B1669055 : Blo 1112627 1669055 := bstep (se 1 (by rfl) ⟨1251791, by rfl⟩ : syracuseStep 1669055 = 2503583) B2503583
theorem B1669223 : Blo 1112627 1669223 := bstep (se 1 (by rfl) ⟨1251917, by rfl⟩ : syracuseStep 1669223 = 2503835) B2503835
theorem B1112679 : Blo 1112627 1112679 := bstep (se 1 (by rfl) ⟨834509, by rfl⟩ : syracuseStep 1112679 = 1669019) B1669019
theorem B1112767 : Blo 1112627 1112767 := bstep (se 1 (by rfl) ⟨834575, by rfl⟩ : syracuseStep 1112767 = 1669151) B1669151
theorem B1669823 : Blo 1112627 1669823 := bstep (se 1 (by rfl) ⟨1252367, by rfl⟩ : syracuseStep 1669823 = 2504735) B2504735
theorem B1112959 : Blo 1112627 1112959 := bstep (se 1 (by rfl) ⟨834719, by rfl⟩ : syracuseStep 1112959 = 1669439) B1669439
theorem B32111585 : Blo 1112627 32111585 := bstep (se 2 (by rfl) ⟨12041844, by rfl⟩ : syracuseStep 32111585 = 24083689) B24083689
theorem B1670303 : Blo 1112627 1670303 := bstep (se 1 (by rfl) ⟨1252727, by rfl⟩ : syracuseStep 1670303 = 2505455) B2505455
theorem B1113343 : Blo 1112627 1113343 := bstep (se 1 (by rfl) ⟨835007, by rfl⟩ : syracuseStep 1113343 = 1670015) B1670015
theorem B1113503 : Blo 1112627 1113503 := bstep (se 1 (by rfl) ⟨835127, by rfl⟩ : syracuseStep 1113503 = 1670255) B1670255
theorem B1113599 : Blo 1112627 1113599 := bstep (se 1 (by rfl) ⟨835199, by rfl⟩ : syracuseStep 1113599 = 1670399) B1670399
theorem B1113631 : Blo 1112627 1113631 := bstep (se 1 (by rfl) ⟨835223, by rfl⟩ : syracuseStep 1113631 = 1670447) B1670447
theorem B1670825 : Blo 1112627 1670825 := bstep (se 2 (by rfl) ⟨626559, by rfl⟩ : syracuseStep 1670825 = 1253119) B1253119
theorem B1671659 : Blo 1112627 1671659 := bstep (se 1 (by rfl) ⟨1253744, by rfl⟩ : syracuseStep 1671659 = 2507489) B2507489
theorem B9175913 : Blo 1112627 9175913 := bstep (se 2 (by rfl) ⟨3440967, by rfl⟩ : syracuseStep 9175913 = 6881935) B6881935
theorem B10716779 : Blo 1112627 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B1673087 : Blo 1112627 1673087 := bstep (se 1 (by rfl) ⟨1254815, by rfl⟩ : syracuseStep 1673087 = 2509631) B2509631
theorem B1673543 : Blo 1112627 1673543 := bstep (se 1 (by rfl) ⟨1255157, by rfl⟩ : syracuseStep 1673543 = 2510315) B2510315
theorem B1674377 : Blo 1112627 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B2821999 : Blo 1112627 2821999 := bstep (se 1 (by rfl) ⟨2116499, by rfl⟩ : syracuseStep 2821999 = 4232999) B4232999
theorem B10720127 : Blo 1112627 10720127 := bstep (se 1 (by rfl) ⟨8040095, by rfl⟩ : syracuseStep 10720127 = 16080191) B16080191
theorem B5641325 : Blo 1112627 5641325 := bstep (se 3 (by rfl) ⟨1057748, by rfl⟩ : syracuseStep 5641325 = 2115497) B2115497
theorem B2823295 : Blo 1112627 2823295 := bstep (se 1 (by rfl) ⟨2117471, by rfl⟩ : syracuseStep 2823295 = 4234943) B4234943
theorem B32118281 : Blo 1112627 32118281 := bstep (se 2 (by rfl) ⟨12044355, by rfl⟩ : syracuseStep 32118281 = 24088711) B24088711
theorem B12884591 : Blo 1112627 12884591 := bstep (se 1 (by rfl) ⟨9663443, by rfl⟩ : syracuseStep 12884591 = 19326887) B19326887
theorem B15473267 : Blo 1112627 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B7346969 : Blo 1112627 7346969 := bstep (se 2 (by rfl) ⟨2755113, by rfl⟩ : syracuseStep 7346969 = 5510227) B5510227
theorem B5643755 : Blo 1112627 5643755 := bstep (se 1 (by rfl) ⟨4232816, by rfl⟩ : syracuseStep 5643755 = 8465633) B8465633
theorem B8464175 : Blo 1112627 8464175 := bstep (se 1 (by rfl) ⟨6348131, by rfl⟩ : syracuseStep 8464175 = 12696263) B12696263
theorem B21407723 : Blo 1112627 21407723 := bstep (se 1 (by rfl) ⟨16055792, by rfl⟩ : syracuseStep 21407723 = 32111585) B32111585
theorem B40708955 : Blo 1112627 40708955 := bstep (se 1 (by rfl) ⟨30531716, by rfl⟩ : syracuseStep 40708955 = 61063433) B61063433
theorem B4764653 : Blo 1112627 4764653 := bstep (se 3 (by rfl) ⟨893372, by rfl⟩ : syracuseStep 4764653 = 1786745) B1786745
theorem B2503817 : Blo 1112627 2503817 := bstep (se 2 (by rfl) ⟨938931, by rfl⟩ : syracuseStep 2503817 = 1877863) B1877863
theorem B9517277 : Blo 1112627 9517277 := bstep (se 3 (by rfl) ⟨1784489, by rfl⟩ : syracuseStep 9517277 = 3568979) B3568979
theorem B12697721 : Blo 1112627 12697721 := bstep (se 2 (by rfl) ⟨4761645, by rfl⟩ : syracuseStep 12697721 = 9523291) B9523291
theorem B1589807 : Blo 1112627 1589807 := bstep (se 1 (by rfl) ⟨1192355, by rfl⟩ : syracuseStep 1589807 = 2384711) B2384711
theorem B16073903 : Blo 1112627 16073903 := bstep (se 1 (by rfl) ⟨12055427, by rfl⟩ : syracuseStep 16073903 = 24110855) B24110855
theorem B1787719 : Blo 1112627 1787719 := bstep (se 1 (by rfl) ⟨1340789, by rfl⟩ : syracuseStep 1787719 = 2681579) B2681579
theorem B4017755 : Blo 1112627 4017755 := bstep (se 1 (by rfl) ⟨3013316, by rfl⟩ : syracuseStep 4017755 = 6026633) B6026633
theorem B2511161 : Blo 1112627 2511161 := bstep (se 2 (by rfl) ⟨941685, by rfl⟩ : syracuseStep 2511161 = 1883371) B1883371
theorem B5362159 : Blo 1112627 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B19289825 : Blo 1112627 19289825 := bstep (se 2 (by rfl) ⟨7233684, by rfl⟩ : syracuseStep 19289825 = 14467369) B14467369
theorem B3758291 : Blo 1112627 3758291 := bstep (se 1 (by rfl) ⟨2818718, by rfl⟩ : syracuseStep 3758291 = 5637437) B5637437
theorem B5363927 : Blo 1112627 5363927 := bstep (se 1 (by rfl) ⟨4022945, by rfl⟩ : syracuseStep 5363927 = 8045891) B8045891
theorem B2677063 : Blo 1112627 2677063 := bstep (se 1 (by rfl) ⟨2007797, by rfl⟩ : syracuseStep 2677063 = 4015595) B4015595
theorem B3169145 : Blo 1112627 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B17161723 : Blo 1112627 17161723 := bstep (se 1 (by rfl) ⟨12871292, by rfl⟩ : syracuseStep 17161723 = 25742585) B25742585
theorem B2679119 : Blo 1112627 2679119 := bstep (se 1 (by rfl) ⟨2009339, by rfl⟩ : syracuseStep 2679119 = 4018679) B4018679
theorem B8452511 : Blo 1112627 8452511 := bstep (se 1 (by rfl) ⟨6339383, by rfl⟩ : syracuseStep 8452511 = 12678767) B12678767
theorem B1112703 : Blo 1112627 1112703 := bstep (se 1 (by rfl) ⟨834527, by rfl⟩ : syracuseStep 1112703 = 1669055) B1669055
theorem B1112815 : Blo 1112627 1112815 := bstep (se 1 (by rfl) ⟨834611, by rfl⟩ : syracuseStep 1112815 = 1669223) B1669223
theorem B1113215 : Blo 1112627 1113215 := bstep (se 1 (by rfl) ⟨834911, by rfl⟩ : syracuseStep 1113215 = 1669823) B1669823
theorem B1113535 : Blo 1112627 1113535 := bstep (se 1 (by rfl) ⟨835151, by rfl⟩ : syracuseStep 1113535 = 1670303) B1670303
theorem B1670711 : Blo 1112627 1670711 := bstep (se 1 (by rfl) ⟨1253033, by rfl⟩ : syracuseStep 1670711 = 2506067) B2506067
theorem B1113883 : Blo 1112627 1113883 := bstep (se 1 (by rfl) ⟨835412, by rfl⟩ : syracuseStep 1113883 = 1670825) B1670825
theorem B1671167 : Blo 1112627 1671167 := bstep (se 1 (by rfl) ⟨1253375, by rfl⟩ : syracuseStep 1671167 = 2506751) B2506751
theorem B1114439 : Blo 1112627 1114439 := bstep (se 1 (by rfl) ⟨835829, by rfl⟩ : syracuseStep 1114439 = 1671659) B1671659
theorem B10715935 : Blo 1112627 10715935 := bstep (se 1 (by rfl) ⟨8036951, by rfl⟩ : syracuseStep 10715935 = 16073903) B16073903
theorem B7144519 : Blo 1112627 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B1115391 : Blo 1112627 1115391 := bstep (se 1 (by rfl) ⟨836543, by rfl⟩ : syracuseStep 1115391 = 1673087) B1673087
theorem B1115695 : Blo 1112627 1115695 := bstep (se 1 (by rfl) ⟨836771, by rfl⟩ : syracuseStep 1115695 = 1673543) B1673543
theorem B1114111 : Blo 1112627 1114111 := bstep (se 1 (by rfl) ⟨835583, by rfl⟩ : syracuseStep 1114111 = 1671167) B1671167
theorem B1116251 : Blo 1112627 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B1674107 : Blo 1112627 1674107 := bstep (se 1 (by rfl) ⟨1255580, by rfl⟩ : syracuseStep 1674107 = 2511161) B2511161
theorem B7146751 : Blo 1112627 7146751 := bstep (se 1 (by rfl) ⟨5360063, by rfl⟩ : syracuseStep 7146751 = 10720127) B10720127
theorem B3575951 : Blo 1112627 3575951 := bstep (se 1 (by rfl) ⟨2681963, by rfl⟩ : syracuseStep 3575951 = 5363927) B5363927
theorem B8589727 : Blo 1112627 8589727 := bstep (se 1 (by rfl) ⟨6442295, by rfl⟩ : syracuseStep 8589727 = 12884591) B12884591
theorem B7149545 : Blo 1112627 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B5642783 : Blo 1112627 5642783 := bstep (se 1 (by rfl) ⟨4232087, by rfl⟩ : syracuseStep 5642783 = 8464175) B8464175
theorem B27139303 : Blo 1112627 27139303 := bstep (se 1 (by rfl) ⟨20354477, by rfl⟩ : syracuseStep 27139303 = 40708955) B40708955
theorem B22882297 : Blo 1112627 22882297 := bstep (se 2 (by rfl) ⟨8580861, by rfl⟩ : syracuseStep 22882297 = 17161723) B17161723
theorem B8465147 : Blo 1112627 8465147 := bstep (se 1 (by rfl) ⟨6348860, by rfl⟩ : syracuseStep 8465147 = 12697721) B12697721
theorem B4239485 : Blo 1112627 4239485 := bstep (se 3 (by rfl) ⟨794903, by rfl⟩ : syracuseStep 4239485 = 1589807) B1589807
theorem B21412187 : Blo 1112627 21412187 := bstep (se 1 (by rfl) ⟨16059140, by rfl⟩ : syracuseStep 21412187 = 32118281) B32118281
theorem B12859883 : Blo 1112627 12859883 := bstep (se 1 (by rfl) ⟨9644912, by rfl⟩ : syracuseStep 12859883 = 19289825) B19289825
theorem B2505527 : Blo 1112627 2505527 := bstep (se 1 (by rfl) ⟨1879145, by rfl⟩ : syracuseStep 2505527 = 3758291) B3758291
theorem B4897979 : Blo 1112627 4897979 := bstep (se 1 (by rfl) ⟨3673484, by rfl⟩ : syracuseStep 4897979 = 7346969) B7346969
theorem B1786079 : Blo 1112627 1786079 := bstep (se 1 (by rfl) ⟨1339559, by rfl⟩ : syracuseStep 1786079 = 2679119) B2679119
theorem B14271815 : Blo 1112627 14271815 := bstep (se 1 (by rfl) ⟨10703861, by rfl⟩ : syracuseStep 14271815 = 21407723) B21407723
theorem B6344851 : Blo 1112627 6344851 := bstep (se 1 (by rfl) ⟨4758638, by rfl⟩ : syracuseStep 6344851 = 9517277) B9517277
theorem B6117275 : Blo 1112627 6117275 := bstep (se 1 (by rfl) ⟨4587956, by rfl⟩ : syracuseStep 6117275 = 9175913) B9175913
theorem B2678503 : Blo 1112627 2678503 := bstep (se 1 (by rfl) ⟨2008877, by rfl⟩ : syracuseStep 2678503 = 4017755) B4017755
theorem B2383625 : Blo 1112627 2383625 := bstep (se 2 (by rfl) ⟨893859, by rfl⟩ : syracuseStep 2383625 = 1787719) B1787719
theorem B3760883 : Blo 1112627 3760883 := bstep (se 1 (by rfl) ⟨2820662, by rfl⟩ : syracuseStep 3760883 = 5641325) B5641325
theorem B10315511 : Blo 1112627 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B3762503 : Blo 1112627 3762503 := bstep (se 1 (by rfl) ⟨2821877, by rfl⟩ : syracuseStep 3762503 = 5643755) B5643755
theorem B3762665 : Blo 1112627 3762665 := bstep (se 2 (by rfl) ⟨1410999, by rfl⟩ : syracuseStep 3762665 = 2821999) B2821999
theorem B3764393 : Blo 1112627 3764393 := bstep (se 2 (by rfl) ⟨1411647, by rfl⟩ : syracuseStep 3764393 = 2823295) B2823295
theorem B8451053 : Blo 1112627 8451053 := bstep (se 3 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 8451053 = 3169145) B3169145
theorem B3569417 : Blo 1112627 3569417 := bstep (se 2 (by rfl) ⟨1338531, by rfl⟩ : syracuseStep 3569417 = 2677063) B2677063
theorem B3176435 : Blo 1112627 3176435 := bstep (se 1 (by rfl) ⟨2382326, by rfl⟩ : syracuseStep 3176435 = 4764653) B4764653
theorem B1669211 : Blo 1112627 1669211 := bstep (se 1 (by rfl) ⟨1251908, by rfl⟩ : syracuseStep 1669211 = 2503817) B2503817
theorem B5635007 : Blo 1112627 5635007 := bstep (se 1 (by rfl) ⟨4226255, by rfl⟩ : syracuseStep 5635007 = 8452511) B8452511
theorem B1113807 : Blo 1112627 1113807 := bstep (se 1 (by rfl) ⟨835355, by rfl⟩ : syracuseStep 1113807 = 1670711) B1670711
theorem B14287913 : Blo 1112627 14287913 := bstep (se 2 (by rfl) ⟨5357967, by rfl⟩ : syracuseStep 14287913 = 10715935) B10715935
theorem B1116071 : Blo 1112627 1116071 := bstep (se 1 (by rfl) ⟨837053, by rfl⟩ : syracuseStep 1116071 = 1674107) B1674107
theorem B30509729 : Blo 1112627 30509729 := bstep (se 2 (by rfl) ⟨11441148, by rfl⟩ : syracuseStep 30509729 = 22882297) B22882297
theorem B8459801 : Blo 1112627 8459801 := bstep (se 2 (by rfl) ⟨3172425, by rfl⟩ : syracuseStep 8459801 = 6344851) B6344851
theorem B5643431 : Blo 1112627 5643431 := bstep (se 1 (by rfl) ⟨4232573, by rfl⟩ : syracuseStep 5643431 = 8465147) B8465147
theorem B2826323 : Blo 1112627 2826323 := bstep (se 1 (by rfl) ⟨2119742, by rfl⟩ : syracuseStep 2826323 = 4239485) B4239485
theorem B36185737 : Blo 1112627 36185737 := bstep (se 2 (by rfl) ⟨13569651, by rfl⟩ : syracuseStep 36185737 = 27139303) B27139303
theorem B1190719 : Blo 1112627 1190719 := bstep (se 1 (by rfl) ⟨893039, by rfl⟩ : syracuseStep 1190719 = 1786079) B1786079
theorem B9514543 : Blo 1112627 9514543 := bstep (se 1 (by rfl) ⟨7135907, by rfl⟩ : syracuseStep 9514543 = 14271815) B14271815
theorem B4078183 : Blo 1112627 4078183 := bstep (se 1 (by rfl) ⟨3058637, by rfl⟩ : syracuseStep 4078183 = 6117275) B6117275
theorem B4766363 : Blo 1112627 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B8470493 : Blo 1112627 8470493 := bstep (se 3 (by rfl) ⟨1588217, by rfl⟩ : syracuseStep 8470493 = 3176435) B3176435
theorem B2507255 : Blo 1112627 2507255 := bstep (se 1 (by rfl) ⟨1880441, by rfl⟩ : syracuseStep 2507255 = 3760883) B3760883
theorem B11452969 : Blo 1112627 11452969 := bstep (se 2 (by rfl) ⟨4294863, by rfl⟩ : syracuseStep 11452969 = 8589727) B8589727
theorem B2508335 : Blo 1112627 2508335 := bstep (se 1 (by rfl) ⟨1881251, by rfl⟩ : syracuseStep 2508335 = 3762503) B3762503
theorem B2508443 : Blo 1112627 2508443 := bstep (se 1 (by rfl) ⟨1881332, by rfl⟩ : syracuseStep 2508443 = 3762665) B3762665
theorem B2509595 : Blo 1112627 2509595 := bstep (se 1 (by rfl) ⟨1882196, by rfl⟩ : syracuseStep 2509595 = 3764393) B3764393
theorem B2379611 : Blo 1112627 2379611 := bstep (se 1 (by rfl) ⟨1784708, by rfl⟩ : syracuseStep 2379611 = 3569417) B3569417
theorem B14274791 : Blo 1112627 14274791 := bstep (se 1 (by rfl) ⟨10706093, by rfl⟩ : syracuseStep 14274791 = 21412187) B21412187
theorem B8573255 : Blo 1112627 8573255 := bstep (se 1 (by rfl) ⟨6429941, by rfl⟩ : syracuseStep 8573255 = 12859883) B12859883
theorem B3756671 : Blo 1112627 3756671 := bstep (se 1 (by rfl) ⟨2817503, by rfl⟩ : syracuseStep 3756671 = 5635007) B5635007
theorem B3265319 : Blo 1112627 3265319 := bstep (se 1 (by rfl) ⟨2448989, by rfl⟩ : syracuseStep 3265319 = 4897979) B4897979
theorem B9526025 : Blo 1112627 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B2383967 : Blo 1112627 2383967 := bstep (se 1 (by rfl) ⟨1787975, by rfl⟩ : syracuseStep 2383967 = 3575951) B3575951
theorem B9529001 : Blo 1112627 9529001 := bstep (se 2 (by rfl) ⟨3573375, by rfl⟩ : syracuseStep 9529001 = 7146751) B7146751
theorem B3761855 : Blo 1112627 3761855 := bstep (se 1 (by rfl) ⟨2821391, by rfl⟩ : syracuseStep 3761855 = 5642783) B5642783
theorem B6877007 : Blo 1112627 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B5634035 : Blo 1112627 5634035 := bstep (se 1 (by rfl) ⟨4225526, by rfl⟩ : syracuseStep 5634035 = 8451053) B8451053
theorem B1112807 : Blo 1112627 1112807 := bstep (se 1 (by rfl) ⟨834605, by rfl⟩ : syracuseStep 1112807 = 1669211) B1669211
theorem B1670351 : Blo 1112627 1670351 := bstep (se 1 (by rfl) ⟨1252763, by rfl⟩ : syracuseStep 1670351 = 2505527) B2505527
theorem B6356333 : Blo 1112627 6356333 := bstep (se 3 (by rfl) ⟨1191812, by rfl⟩ : syracuseStep 6356333 = 2383625) B2383625
theorem B3571337 : Blo 1112627 3571337 := bstep (se 2 (by rfl) ⟨1339251, by rfl⟩ : syracuseStep 3571337 = 2678503) B2678503
theorem B1671503 : Blo 1112627 1671503 := bstep (se 1 (by rfl) ⟨1253627, by rfl⟩ : syracuseStep 1671503 = 2507255) B2507255
theorem B15270625 : Blo 1112627 15270625 := bstep (se 2 (by rfl) ⟨5726484, by rfl⟩ : syracuseStep 15270625 = 11452969) B11452969
theorem B1672223 : Blo 1112627 1672223 := bstep (se 1 (by rfl) ⟨1254167, by rfl⟩ : syracuseStep 1672223 = 2508335) B2508335
theorem B1672295 : Blo 1112627 1672295 := bstep (se 1 (by rfl) ⟨1254221, by rfl⟩ : syracuseStep 1672295 = 2508443) B2508443
theorem B1673063 : Blo 1112627 1673063 := bstep (se 1 (by rfl) ⟨1254797, by rfl⟩ : syracuseStep 1673063 = 2509595) B2509595
theorem B5639867 : Blo 1112627 5639867 := bstep (se 1 (by rfl) ⟨4229900, by rfl⟩ : syracuseStep 5639867 = 8459801) B8459801
theorem B12686057 : Blo 1112627 12686057 := bstep (se 2 (by rfl) ⟨4757271, by rfl⟩ : syracuseStep 12686057 = 9514543) B9514543
theorem B4237555 : Blo 1112627 4237555 := bstep (se 1 (by rfl) ⟨3178166, by rfl⟩ : syracuseStep 4237555 = 6356333) B6356333
theorem B5646995 : Blo 1112627 5646995 := bstep (se 1 (by rfl) ⟨4235246, by rfl⟩ : syracuseStep 5646995 = 8470493) B8470493
theorem B48247649 : Blo 1112627 48247649 := bstep (se 2 (by rfl) ⟨18092868, by rfl⟩ : syracuseStep 48247649 = 36185737) B36185737
theorem B1586407 : Blo 1112627 1586407 := bstep (se 1 (by rfl) ⟨1189805, by rfl⟩ : syracuseStep 1586407 = 2379611) B2379611
theorem B9516527 : Blo 1112627 9516527 := bstep (se 1 (by rfl) ⟨7137395, by rfl⟩ : syracuseStep 9516527 = 14274791) B14274791
theorem B5715503 : Blo 1112627 5715503 := bstep (se 1 (by rfl) ⟨4286627, by rfl⟩ : syracuseStep 5715503 = 8573255) B8573255
theorem B2504447 : Blo 1112627 2504447 := bstep (se 1 (by rfl) ⟨1878335, by rfl⟩ : syracuseStep 2504447 = 3756671) B3756671
theorem B2176879 : Blo 1112627 2176879 := bstep (se 1 (by rfl) ⟨1632659, by rfl⟩ : syracuseStep 2176879 = 3265319) B3265319
theorem B1884215 : Blo 1112627 1884215 := bstep (se 1 (by rfl) ⟨1413161, by rfl⟩ : syracuseStep 1884215 = 2826323) B2826323
theorem B1589311 : Blo 1112627 1589311 := bstep (se 1 (by rfl) ⟨1191983, by rfl⟩ : syracuseStep 1589311 = 2383967) B2383967
theorem B2507903 : Blo 1112627 2507903 := bstep (se 1 (by rfl) ⟨1880927, by rfl⟩ : syracuseStep 2507903 = 3761855) B3761855
theorem B3756023 : Blo 1112627 3756023 := bstep (se 1 (by rfl) ⟨2817017, by rfl⟩ : syracuseStep 3756023 = 5634035) B5634035
theorem B9523565 : Blo 1112627 9523565 := bstep (se 3 (by rfl) ⟨1785668, by rfl⟩ : syracuseStep 9523565 = 3571337) B3571337
theorem B9525275 : Blo 1112627 9525275 := bstep (se 1 (by rfl) ⟨7143956, by rfl⟩ : syracuseStep 9525275 = 14287913) B14287913
theorem B20339819 : Blo 1112627 20339819 := bstep (se 1 (by rfl) ⟨15254864, by rfl⟩ : syracuseStep 20339819 = 30509729) B30509729
theorem B6350501 : Blo 1112627 6350501 := bstep (se 4 (by rfl) ⟨595359, by rfl⟩ : syracuseStep 6350501 = 1190719) B1190719
theorem B6350683 : Blo 1112627 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B3762287 : Blo 1112627 3762287 := bstep (se 1 (by rfl) ⟨2821715, by rfl⟩ : syracuseStep 3762287 = 5643431) B5643431
theorem B6352667 : Blo 1112627 6352667 := bstep (se 1 (by rfl) ⟨4764500, by rfl⟩ : syracuseStep 6352667 = 9529001) B9529001
theorem B4584671 : Blo 1112627 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B5437577 : Blo 1112627 5437577 := bstep (se 2 (by rfl) ⟨2039091, by rfl⟩ : syracuseStep 5437577 = 4078183) B4078183
theorem B3177575 : Blo 1112627 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B1113567 : Blo 1112627 1113567 := bstep (se 1 (by rfl) ⟨835175, by rfl⟩ : syracuseStep 1113567 = 1670351) B1670351
theorem B1114335 : Blo 1112627 1114335 := bstep (se 1 (by rfl) ⟨835751, by rfl⟩ : syracuseStep 1114335 = 1671503) B1671503
theorem B1114815 : Blo 1112627 1114815 := bstep (se 1 (by rfl) ⟨836111, by rfl⟩ : syracuseStep 1114815 = 1672223) B1672223
theorem B1114863 : Blo 1112627 1114863 := bstep (se 1 (by rfl) ⟨836147, by rfl⟩ : syracuseStep 1114863 = 1672295) B1672295
theorem B1671935 : Blo 1112627 1671935 := bstep (se 1 (by rfl) ⟨1253951, by rfl⟩ : syracuseStep 1671935 = 2507903) B2507903
theorem B1115375 : Blo 1112627 1115375 := bstep (se 1 (by rfl) ⟨836531, by rfl⟩ : syracuseStep 1115375 = 1673063) B1673063
theorem B8457371 : Blo 1112627 8457371 := bstep (se 1 (by rfl) ⟨6343028, by rfl⟩ : syracuseStep 8457371 = 12686057) B12686057
theorem B4233667 : Blo 1112627 4233667 := bstep (se 1 (by rfl) ⟨3175250, by rfl⟩ : syracuseStep 4233667 = 6350501) B6350501
theorem B4235111 : Blo 1112627 4235111 := bstep (se 1 (by rfl) ⟨3176333, by rfl⟩ : syracuseStep 4235111 = 6352667) B6352667
theorem B3056447 : Blo 1112627 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B3810335 : Blo 1112627 3810335 := bstep (se 1 (by rfl) ⟨2857751, by rfl⟩ : syracuseStep 3810335 = 5715503) B5715503
theorem B1256143 : Blo 1112627 1256143 := bstep (se 1 (by rfl) ⟨942107, by rfl⟩ : syracuseStep 1256143 = 1884215) B1884215
theorem B8467577 : Blo 1112627 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B2504015 : Blo 1112627 2504015 := bstep (se 1 (by rfl) ⟨1878011, by rfl⟩ : syracuseStep 2504015 = 3756023) B3756023
theorem B5650073 : Blo 1112627 5650073 := bstep (se 2 (by rfl) ⟨2118777, by rfl⟩ : syracuseStep 5650073 = 4237555) B4237555
theorem B81443333 : Blo 1112627 81443333 := bstep (se 4 (by rfl) ⟨7635312, by rfl⟩ : syracuseStep 81443333 = 15270625) B15270625
theorem B14500205 : Blo 1112627 14500205 := bstep (se 3 (by rfl) ⟨2718788, by rfl⟩ : syracuseStep 14500205 = 5437577) B5437577
theorem B2508191 : Blo 1112627 2508191 := bstep (se 1 (by rfl) ⟨1881143, by rfl⟩ : syracuseStep 2508191 = 3762287) B3762287
theorem B2115209 : Blo 1112627 2115209 := bstep (se 2 (by rfl) ⟨793203, by rfl⟩ : syracuseStep 2115209 = 1586407) B1586407
theorem B2902505 : Blo 1112627 2902505 := bstep (se 2 (by rfl) ⟨1088439, by rfl⟩ : syracuseStep 2902505 = 2176879) B2176879
theorem B32165099 : Blo 1112627 32165099 := bstep (se 1 (by rfl) ⟨24123824, by rfl⟩ : syracuseStep 32165099 = 48247649) B48247649
theorem B6344351 : Blo 1112627 6344351 := bstep (se 1 (by rfl) ⟨4758263, by rfl⟩ : syracuseStep 6344351 = 9516527) B9516527
theorem B2118383 : Blo 1112627 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B8476325 : Blo 1112627 8476325 := bstep (se 4 (by rfl) ⟨794655, by rfl⟩ : syracuseStep 8476325 = 1589311) B1589311
theorem B3759911 : Blo 1112627 3759911 := bstep (se 1 (by rfl) ⟨2819933, by rfl⟩ : syracuseStep 3759911 = 5639867) B5639867
theorem B6349043 : Blo 1112627 6349043 := bstep (se 1 (by rfl) ⟨4761782, by rfl⟩ : syracuseStep 6349043 = 9523565) B9523565
theorem B6350183 : Blo 1112627 6350183 := bstep (se 1 (by rfl) ⟨4762637, by rfl⟩ : syracuseStep 6350183 = 9525275) B9525275
theorem B13559879 : Blo 1112627 13559879 := bstep (se 1 (by rfl) ⟨10169909, by rfl⟩ : syracuseStep 13559879 = 20339819) B20339819
theorem B3764663 : Blo 1112627 3764663 := bstep (se 1 (by rfl) ⟨2823497, by rfl⟩ : syracuseStep 3764663 = 5646995) B5646995
theorem B1669631 : Blo 1112627 1669631 := bstep (se 1 (by rfl) ⟨1252223, by rfl⟩ : syracuseStep 1669631 = 2504447) B2504447
theorem B9666803 : Blo 1112627 9666803 := bstep (se 1 (by rfl) ⟨7250102, by rfl⟩ : syracuseStep 9666803 = 14500205) B14500205
theorem B1114623 : Blo 1112627 1114623 := bstep (se 1 (by rfl) ⟨835967, by rfl⟩ : syracuseStep 1114623 = 1671935) B1671935
theorem B1672127 : Blo 1112627 1672127 := bstep (se 1 (by rfl) ⟨1254095, by rfl⟩ : syracuseStep 1672127 = 2508191) B2508191
theorem B1410139 : Blo 1112627 1410139 := bstep (se 1 (by rfl) ⟨1057604, by rfl⟩ : syracuseStep 1410139 = 2115209) B2115209
theorem B5638247 : Blo 1112627 5638247 := bstep (se 1 (by rfl) ⟨4228685, by rfl⟩ : syracuseStep 5638247 = 8457371) B8457371
theorem B4229567 : Blo 1112627 4229567 := bstep (se 1 (by rfl) ⟨3172175, by rfl⟩ : syracuseStep 4229567 = 6344351) B6344351
theorem B10160893 : Blo 1112627 10160893 := bstep (se 3 (by rfl) ⟨1905167, by rfl⟩ : syracuseStep 10160893 = 3810335) B3810335
theorem B1412255 : Blo 1112627 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B1674857 : Blo 1112627 1674857 := bstep (se 2 (by rfl) ⟨628071, by rfl⟩ : syracuseStep 1674857 = 1256143) B1256143
theorem B2823407 : Blo 1112627 2823407 := bstep (se 1 (by rfl) ⟨2117555, by rfl⟩ : syracuseStep 2823407 = 4235111) B4235111
theorem B4232695 : Blo 1112627 4232695 := bstep (se 1 (by rfl) ⟨3174521, by rfl⟩ : syracuseStep 4232695 = 6349043) B6349043
theorem B2037631 : Blo 1112627 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B4233455 : Blo 1112627 4233455 := bstep (se 1 (by rfl) ⟨3175091, by rfl⟩ : syracuseStep 4233455 = 6350183) B6350183
theorem B5644889 : Blo 1112627 5644889 := bstep (se 2 (by rfl) ⟨2116833, by rfl⟩ : syracuseStep 5644889 = 4233667) B4233667
theorem B5645051 : Blo 1112627 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B21443399 : Blo 1112627 21443399 := bstep (se 1 (by rfl) ⟨16082549, by rfl⟩ : syracuseStep 21443399 = 32165099) B32165099
theorem B5650883 : Blo 1112627 5650883 := bstep (se 1 (by rfl) ⟨4238162, by rfl⟩ : syracuseStep 5650883 = 8476325) B8476325
theorem B2506607 : Blo 1112627 2506607 := bstep (se 1 (by rfl) ⟨1879955, by rfl⟩ : syracuseStep 2506607 = 3759911) B3759911
theorem B2509775 : Blo 1112627 2509775 := bstep (se 1 (by rfl) ⟨1882331, by rfl⟩ : syracuseStep 2509775 = 3764663) B3764663
theorem B30960053 : Blo 1112627 30960053 := bstep (se 5 (by rfl) ⟨1451252, by rfl⟩ : syracuseStep 30960053 = 2902505) B2902505
theorem B9039919 : Blo 1112627 9039919 := bstep (se 1 (by rfl) ⟨6779939, by rfl⟩ : syracuseStep 9039919 = 13559879) B13559879
theorem B1669343 : Blo 1112627 1669343 := bstep (se 1 (by rfl) ⟨1252007, by rfl⟩ : syracuseStep 1669343 = 2504015) B2504015
theorem B3766715 : Blo 1112627 3766715 := bstep (se 1 (by rfl) ⟨2825036, by rfl⟩ : syracuseStep 3766715 = 5650073) B5650073
theorem B1113087 : Blo 1112627 1113087 := bstep (se 1 (by rfl) ⟨834815, by rfl⟩ : syracuseStep 1113087 = 1669631) B1669631
theorem B54295555 : Blo 1112627 54295555 := bstep (se 1 (by rfl) ⟨40721666, by rfl⟩ : syracuseStep 54295555 = 81443333) B81443333
theorem B1114751 : Blo 1112627 1114751 := bstep (se 1 (by rfl) ⟨836063, by rfl⟩ : syracuseStep 1114751 = 1672127) B1672127
theorem B2819711 : Blo 1112627 2819711 := bstep (se 1 (by rfl) ⟨2114783, by rfl⟩ : syracuseStep 2819711 = 4229567) B4229567
theorem B1673183 : Blo 1112627 1673183 := bstep (se 1 (by rfl) ⟨1254887, by rfl⟩ : syracuseStep 1673183 = 2509775) B2509775
theorem B1116571 : Blo 1112627 1116571 := bstep (se 1 (by rfl) ⟨837428, by rfl⟩ : syracuseStep 1116571 = 1674857) B1674857
theorem B2822303 : Blo 1112627 2822303 := bstep (se 1 (by rfl) ⟨2116727, by rfl⟩ : syracuseStep 2822303 = 4233455) B4233455
theorem B5643593 : Blo 1112627 5643593 := bstep (se 2 (by rfl) ⟨2116347, by rfl⟩ : syracuseStep 5643593 = 4232695) B4232695
theorem B14295599 : Blo 1112627 14295599 := bstep (se 1 (by rfl) ⟨10721699, by rfl⟩ : syracuseStep 14295599 = 21443399) B21443399
theorem B72394073 : Blo 1112627 72394073 := bstep (se 2 (by rfl) ⟨27147777, by rfl⟩ : syracuseStep 72394073 = 54295555) B54295555
theorem B1880185 : Blo 1112627 1880185 := bstep (se 2 (by rfl) ⟨705069, by rfl⟩ : syracuseStep 1880185 = 1410139) B1410139
theorem B1882271 : Blo 1112627 1882271 := bstep (se 1 (by rfl) ⟨1411703, by rfl⟩ : syracuseStep 1882271 = 2823407) B2823407
theorem B13547857 : Blo 1112627 13547857 := bstep (se 2 (by rfl) ⟨5080446, by rfl⟩ : syracuseStep 13547857 = 10160893) B10160893
theorem B2511143 : Blo 1112627 2511143 := bstep (se 1 (by rfl) ⟨1883357, by rfl⟩ : syracuseStep 2511143 = 3766715) B3766715
theorem B6444535 : Blo 1112627 6444535 := bstep (se 1 (by rfl) ⟨4833401, by rfl⟩ : syracuseStep 6444535 = 9666803) B9666803
theorem B3758831 : Blo 1112627 3758831 := bstep (se 1 (by rfl) ⟨2819123, by rfl⟩ : syracuseStep 3758831 = 5638247) B5638247
theorem B12053225 : Blo 1112627 12053225 := bstep (se 2 (by rfl) ⟨4519959, by rfl⟩ : syracuseStep 12053225 = 9039919) B9039919
theorem B3763259 : Blo 1112627 3763259 := bstep (se 1 (by rfl) ⟨2822444, by rfl⟩ : syracuseStep 3763259 = 5644889) B5644889
theorem B3763367 : Blo 1112627 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B20640035 : Blo 1112627 20640035 := bstep (se 1 (by rfl) ⟨15480026, by rfl⟩ : syracuseStep 20640035 = 30960053) B30960053
theorem B2716841 : Blo 1112627 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B3766013 : Blo 1112627 3766013 := bstep (se 3 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 3766013 = 1412255) B1412255
theorem B1112895 : Blo 1112627 1112895 := bstep (se 1 (by rfl) ⟨834671, by rfl⟩ : syracuseStep 1112895 = 1669343) B1669343
theorem B3767255 : Blo 1112627 3767255 := bstep (se 1 (by rfl) ⟨2825441, by rfl⟩ : syracuseStep 3767255 = 5650883) B5650883
theorem B1671071 : Blo 1112627 1671071 := bstep (se 1 (by rfl) ⟨1253303, by rfl⟩ : syracuseStep 1671071 = 2506607) B2506607
theorem B1115455 : Blo 1112627 1115455 := bstep (se 1 (by rfl) ⟨836591, by rfl⟩ : syracuseStep 1115455 = 1673183) B1673183
theorem B1674095 : Blo 1112627 1674095 := bstep (se 1 (by rfl) ⟨1255571, by rfl⟩ : syracuseStep 1674095 = 2511143) B2511143
theorem B7244909 : Blo 1112627 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B8035483 : Blo 1112627 8035483 := bstep (se 1 (by rfl) ⟨6026612, by rfl⟩ : syracuseStep 8035483 = 12053225) B12053225
theorem B8592713 : Blo 1112627 8592713 := bstep (se 2 (by rfl) ⟨3222267, by rfl⟩ : syracuseStep 8592713 = 6444535) B6444535
theorem B18063809 : Blo 1112627 18063809 := bstep (se 2 (by rfl) ⟨6773928, by rfl⟩ : syracuseStep 18063809 = 13547857) B13547857
theorem B1254847 : Blo 1112627 1254847 := bstep (se 1 (by rfl) ⟨941135, by rfl⟩ : syracuseStep 1254847 = 1882271) B1882271
theorem B1879807 : Blo 1112627 1879807 := bstep (se 1 (by rfl) ⟨1409855, by rfl⟩ : syracuseStep 1879807 = 2819711) B2819711
theorem B1881535 : Blo 1112627 1881535 := bstep (se 1 (by rfl) ⟨1411151, by rfl⟩ : syracuseStep 1881535 = 2822303) B2822303
theorem B2505887 : Blo 1112627 2505887 := bstep (se 1 (by rfl) ⟨1879415, by rfl⟩ : syracuseStep 2505887 = 3758831) B3758831
theorem B2506913 : Blo 1112627 2506913 := bstep (se 2 (by rfl) ⟨940092, by rfl⟩ : syracuseStep 2506913 = 1880185) B1880185
theorem B2508839 : Blo 1112627 2508839 := bstep (se 1 (by rfl) ⟨1881629, by rfl⟩ : syracuseStep 2508839 = 3763259) B3763259
theorem B2508911 : Blo 1112627 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B2510675 : Blo 1112627 2510675 := bstep (se 1 (by rfl) ⟨1883006, by rfl⟩ : syracuseStep 2510675 = 3766013) B3766013
theorem B2511503 : Blo 1112627 2511503 := bstep (se 1 (by rfl) ⟨1883627, by rfl⟩ : syracuseStep 2511503 = 3767255) B3767255
theorem B55040093 : Blo 1112627 55040093 := bstep (se 3 (by rfl) ⟨10320017, by rfl⟩ : syracuseStep 55040093 = 20640035) B20640035
theorem B3762395 : Blo 1112627 3762395 := bstep (se 1 (by rfl) ⟨2821796, by rfl⟩ : syracuseStep 3762395 = 5643593) B5643593
theorem B9530399 : Blo 1112627 9530399 := bstep (se 1 (by rfl) ⟨7147799, by rfl⟩ : syracuseStep 9530399 = 14295599) B14295599
theorem B48262715 : Blo 1112627 48262715 := bstep (se 1 (by rfl) ⟨36197036, by rfl⟩ : syracuseStep 48262715 = 72394073) B72394073
theorem B1114047 : Blo 1112627 1114047 := bstep (se 1 (by rfl) ⟨835535, by rfl⟩ : syracuseStep 1114047 = 1671071) B1671071
theorem B1671275 : Blo 1112627 1671275 := bstep (se 1 (by rfl) ⟨1253456, by rfl⟩ : syracuseStep 1671275 = 2506913) B2506913
theorem B1672559 : Blo 1112627 1672559 := bstep (se 1 (by rfl) ⟨1254419, by rfl⟩ : syracuseStep 1672559 = 2508839) B2508839
theorem B1672607 : Blo 1112627 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B1116063 : Blo 1112627 1116063 := bstep (se 1 (by rfl) ⟨837047, by rfl⟩ : syracuseStep 1116063 = 1674095) B1674095
theorem B1673129 : Blo 1112627 1673129 := bstep (se 2 (by rfl) ⟨627423, by rfl⟩ : syracuseStep 1673129 = 1254847) B1254847
theorem B1673783 : Blo 1112627 1673783 := bstep (se 1 (by rfl) ⟨1255337, by rfl⟩ : syracuseStep 1673783 = 2510675) B2510675
theorem B1674335 : Blo 1112627 1674335 := bstep (se 1 (by rfl) ⟨1255751, by rfl⟩ : syracuseStep 1674335 = 2511503) B2511503
theorem B4829939 : Blo 1112627 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B2506409 : Blo 1112627 2506409 := bstep (se 2 (by rfl) ⟨939903, by rfl⟩ : syracuseStep 2506409 = 1879807) B1879807
theorem B12042539 : Blo 1112627 12042539 := bstep (se 1 (by rfl) ⟨9031904, by rfl⟩ : syracuseStep 12042539 = 18063809) B18063809
theorem B2508263 : Blo 1112627 2508263 := bstep (se 1 (by rfl) ⟨1881197, by rfl⟩ : syracuseStep 2508263 = 3762395) B3762395
theorem B2508713 : Blo 1112627 2508713 := bstep (se 2 (by rfl) ⟨940767, by rfl⟩ : syracuseStep 2508713 = 1881535) B1881535
theorem B36693395 : Blo 1112627 36693395 := bstep (se 1 (by rfl) ⟨27520046, by rfl⟩ : syracuseStep 36693395 = 55040093) B55040093
theorem B5728475 : Blo 1112627 5728475 := bstep (se 1 (by rfl) ⟨4296356, by rfl⟩ : syracuseStep 5728475 = 8592713) B8592713
theorem B6353599 : Blo 1112627 6353599 := bstep (se 1 (by rfl) ⟨4765199, by rfl⟩ : syracuseStep 6353599 = 9530399) B9530399
theorem B32175143 : Blo 1112627 32175143 := bstep (se 1 (by rfl) ⟨24131357, by rfl⟩ : syracuseStep 32175143 = 48262715) B48262715
theorem B10713977 : Blo 1112627 10713977 := bstep (se 2 (by rfl) ⟨4017741, by rfl⟩ : syracuseStep 10713977 = 8035483) B8035483
theorem B1670591 : Blo 1112627 1670591 := bstep (se 1 (by rfl) ⟨1252943, by rfl⟩ : syracuseStep 1670591 = 2505887) B2505887
theorem B1114183 : Blo 1112627 1114183 := bstep (se 1 (by rfl) ⟨835637, by rfl⟩ : syracuseStep 1114183 = 1671275) B1671275
theorem B8028359 : Blo 1112627 8028359 := bstep (se 1 (by rfl) ⟨6021269, by rfl⟩ : syracuseStep 8028359 = 12042539) B12042539
theorem B1115039 : Blo 1112627 1115039 := bstep (se 1 (by rfl) ⟨836279, by rfl⟩ : syracuseStep 1115039 = 1672559) B1672559
theorem B1115071 : Blo 1112627 1115071 := bstep (se 1 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 1115071 = 1672607) B1672607
theorem B1672175 : Blo 1112627 1672175 := bstep (se 1 (by rfl) ⟨1254131, by rfl⟩ : syracuseStep 1672175 = 2508263) B2508263
theorem B1672475 : Blo 1112627 1672475 := bstep (se 1 (by rfl) ⟨1254356, by rfl⟩ : syracuseStep 1672475 = 2508713) B2508713
theorem B1115419 : Blo 1112627 1115419 := bstep (se 1 (by rfl) ⟨836564, by rfl⟩ : syracuseStep 1115419 = 1673129) B1673129
theorem B1115855 : Blo 1112627 1115855 := bstep (se 1 (by rfl) ⟨836891, by rfl⟩ : syracuseStep 1115855 = 1673783) B1673783
theorem B1116223 : Blo 1112627 1116223 := bstep (se 1 (by rfl) ⟨837167, by rfl⟩ : syracuseStep 1116223 = 1674335) B1674335
theorem B3219959 : Blo 1112627 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B8471465 : Blo 1112627 8471465 := bstep (se 2 (by rfl) ⟨3176799, by rfl⟩ : syracuseStep 8471465 = 6353599) B6353599
theorem B24462263 : Blo 1112627 24462263 := bstep (se 1 (by rfl) ⟨18346697, by rfl⟩ : syracuseStep 24462263 = 36693395) B36693395
theorem B3818983 : Blo 1112627 3818983 := bstep (se 1 (by rfl) ⟨2864237, by rfl⟩ : syracuseStep 3818983 = 5728475) B5728475
theorem B21450095 : Blo 1112627 21450095 := bstep (se 1 (by rfl) ⟨16087571, by rfl⟩ : syracuseStep 21450095 = 32175143) B32175143
theorem B7142651 : Blo 1112627 7142651 := bstep (se 1 (by rfl) ⟨5356988, by rfl⟩ : syracuseStep 7142651 = 10713977) B10713977
theorem B1113727 : Blo 1112627 1113727 := bstep (se 1 (by rfl) ⟨835295, by rfl⟩ : syracuseStep 1113727 = 1670591) B1670591
theorem B1670939 : Blo 1112627 1670939 := bstep (se 1 (by rfl) ⟨1253204, by rfl⟩ : syracuseStep 1670939 = 2506409) B2506409
theorem B1114783 : Blo 1112627 1114783 := bstep (se 1 (by rfl) ⟨836087, by rfl⟩ : syracuseStep 1114783 = 1672175) B1672175
theorem B1114983 : Blo 1112627 1114983 := bstep (se 1 (by rfl) ⟨836237, by rfl⟩ : syracuseStep 1114983 = 1672475) B1672475
theorem B4761767 : Blo 1112627 4761767 := bstep (se 1 (by rfl) ⟨3571325, by rfl⟩ : syracuseStep 4761767 = 7142651) B7142651
theorem B5352239 : Blo 1112627 5352239 := bstep (se 1 (by rfl) ⟨4014179, by rfl⟩ : syracuseStep 5352239 = 8028359) B8028359
theorem B5647643 : Blo 1112627 5647643 := bstep (se 1 (by rfl) ⟨4235732, by rfl⟩ : syracuseStep 5647643 = 8471465) B8471465
theorem B5091977 : Blo 1112627 5091977 := bstep (se 2 (by rfl) ⟨1909491, by rfl⟩ : syracuseStep 5091977 = 3818983) B3818983
theorem B14300063 : Blo 1112627 14300063 := bstep (se 1 (by rfl) ⟨10725047, by rfl⟩ : syracuseStep 14300063 = 21450095) B21450095
theorem B2146639 : Blo 1112627 2146639 := bstep (se 1 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 2146639 = 3219959) B3219959
theorem B16308175 : Blo 1112627 16308175 := bstep (se 1 (by rfl) ⟨12231131, by rfl⟩ : syracuseStep 16308175 = 24462263) B24462263
theorem B1113959 : Blo 1112627 1113959 := bstep (se 1 (by rfl) ⟨835469, by rfl⟩ : syracuseStep 1113959 = 1670939) B1670939
theorem B2862185 : Blo 1112627 2862185 := bstep (se 2 (by rfl) ⟨1073319, by rfl⟩ : syracuseStep 2862185 = 2146639) B2146639
theorem B13578605 : Blo 1112627 13578605 := bstep (se 3 (by rfl) ⟨2545988, by rfl⟩ : syracuseStep 13578605 = 5091977) B5091977
theorem B21744233 : Blo 1112627 21744233 := bstep (se 2 (by rfl) ⟨8154087, by rfl⟩ : syracuseStep 21744233 = 16308175) B16308175
theorem B3174511 : Blo 1112627 3174511 := bstep (se 1 (by rfl) ⟨2380883, by rfl⟩ : syracuseStep 3174511 = 4761767) B4761767
theorem B3568159 : Blo 1112627 3568159 := bstep (se 1 (by rfl) ⟨2676119, by rfl⟩ : syracuseStep 3568159 = 5352239) B5352239
theorem B3765095 : Blo 1112627 3765095 := bstep (se 1 (by rfl) ⟨2823821, by rfl⟩ : syracuseStep 3765095 = 5647643) B5647643
theorem B9533375 : Blo 1112627 9533375 := bstep (se 1 (by rfl) ⟨7150031, by rfl⟩ : syracuseStep 9533375 = 14300063) B14300063
theorem B4232681 : Blo 1112627 4232681 := bstep (se 2 (by rfl) ⟨1587255, by rfl⟩ : syracuseStep 4232681 = 3174511) B3174511
theorem B4757545 : Blo 1112627 4757545 := bstep (se 2 (by rfl) ⟨1784079, by rfl⟩ : syracuseStep 4757545 = 3568159) B3568159
theorem B9052403 : Blo 1112627 9052403 := bstep (se 1 (by rfl) ⟨6789302, by rfl⟩ : syracuseStep 9052403 = 13578605) B13578605
theorem B14496155 : Blo 1112627 14496155 := bstep (se 1 (by rfl) ⟨10872116, by rfl⟩ : syracuseStep 14496155 = 21744233) B21744233
theorem B2510063 : Blo 1112627 2510063 := bstep (se 1 (by rfl) ⟨1882547, by rfl⟩ : syracuseStep 2510063 = 3765095) B3765095
theorem B30529973 : Blo 1112627 30529973 := bstep (se 5 (by rfl) ⟨1431092, by rfl⟩ : syracuseStep 30529973 = 2862185) B2862185
theorem B6355583 : Blo 1112627 6355583 := bstep (se 1 (by rfl) ⟨4766687, by rfl⟩ : syracuseStep 6355583 = 9533375) B9533375
theorem B1673375 : Blo 1112627 1673375 := bstep (se 1 (by rfl) ⟨1255031, by rfl⟩ : syracuseStep 1673375 = 2510063) B2510063
theorem B2821787 : Blo 1112627 2821787 := bstep (se 1 (by rfl) ⟨2116340, by rfl⟩ : syracuseStep 2821787 = 4232681) B4232681
theorem B20353315 : Blo 1112627 20353315 := bstep (se 1 (by rfl) ⟨15264986, by rfl⟩ : syracuseStep 20353315 = 30529973) B30529973
theorem B4237055 : Blo 1112627 4237055 := bstep (se 1 (by rfl) ⟨3177791, by rfl⟩ : syracuseStep 4237055 = 6355583) B6355583
theorem B6343393 : Blo 1112627 6343393 := bstep (se 2 (by rfl) ⟨2378772, by rfl⟩ : syracuseStep 6343393 = 4757545) B4757545
theorem B24139741 : Blo 1112627 24139741 := bstep (se 3 (by rfl) ⟨4526201, by rfl⟩ : syracuseStep 24139741 = 9052403) B9052403
theorem B9664103 : Blo 1112627 9664103 := bstep (se 1 (by rfl) ⟨7248077, by rfl⟩ : syracuseStep 9664103 = 14496155) B14496155
theorem B1115583 : Blo 1112627 1115583 := bstep (se 1 (by rfl) ⟨836687, by rfl⟩ : syracuseStep 1115583 = 1673375) B1673375
theorem B8457857 : Blo 1112627 8457857 := bstep (se 2 (by rfl) ⟨3171696, by rfl⟩ : syracuseStep 8457857 = 6343393) B6343393
theorem B27137753 : Blo 1112627 27137753 := bstep (se 2 (by rfl) ⟨10176657, by rfl⟩ : syracuseStep 27137753 = 20353315) B20353315
theorem B2824703 : Blo 1112627 2824703 := bstep (se 1 (by rfl) ⟨2118527, by rfl⟩ : syracuseStep 2824703 = 4237055) B4237055
theorem B32186321 : Blo 1112627 32186321 := bstep (se 2 (by rfl) ⟨12069870, by rfl⟩ : syracuseStep 32186321 = 24139741) B24139741
theorem B1881191 : Blo 1112627 1881191 := bstep (se 1 (by rfl) ⟨1410893, by rfl⟩ : syracuseStep 1881191 = 2821787) B2821787
theorem B6442735 : Blo 1112627 6442735 := bstep (se 1 (by rfl) ⟨4832051, by rfl⟩ : syracuseStep 6442735 = 9664103) B9664103
theorem B5638571 : Blo 1112627 5638571 := bstep (se 1 (by rfl) ⟨4228928, by rfl⟩ : syracuseStep 5638571 = 8457857) B8457857
theorem B18091835 : Blo 1112627 18091835 := bstep (se 1 (by rfl) ⟨13568876, by rfl⟩ : syracuseStep 18091835 = 27137753) B27137753
theorem B8590313 : Blo 1112627 8590313 := bstep (se 2 (by rfl) ⟨3221367, by rfl⟩ : syracuseStep 8590313 = 6442735) B6442735
theorem B1254127 : Blo 1112627 1254127 := bstep (se 1 (by rfl) ⟨940595, by rfl⟩ : syracuseStep 1254127 = 1881191) B1881191
theorem B1883135 : Blo 1112627 1883135 := bstep (se 1 (by rfl) ⟨1412351, by rfl⟩ : syracuseStep 1883135 = 2824703) B2824703
theorem B21457547 : Blo 1112627 21457547 := bstep (se 1 (by rfl) ⟨16093160, by rfl⟩ : syracuseStep 21457547 = 32186321) B32186321
theorem B1672169 : Blo 1112627 1672169 := bstep (se 2 (by rfl) ⟨627063, by rfl⟩ : syracuseStep 1672169 = 1254127) B1254127
theorem B12061223 : Blo 1112627 12061223 := bstep (se 1 (by rfl) ⟨9045917, by rfl⟩ : syracuseStep 12061223 = 18091835) B18091835
theorem B1255423 : Blo 1112627 1255423 := bstep (se 1 (by rfl) ⟨941567, by rfl⟩ : syracuseStep 1255423 = 1883135) B1883135
theorem B14305031 : Blo 1112627 14305031 := bstep (se 1 (by rfl) ⟨10728773, by rfl⟩ : syracuseStep 14305031 = 21457547) B21457547
theorem B3759047 : Blo 1112627 3759047 := bstep (se 1 (by rfl) ⟨2819285, by rfl⟩ : syracuseStep 3759047 = 5638571) B5638571
theorem B5726875 : Blo 1112627 5726875 := bstep (se 1 (by rfl) ⟨4295156, by rfl⟩ : syracuseStep 5726875 = 8590313) B8590313
theorem B1114779 : Blo 1112627 1114779 := bstep (se 1 (by rfl) ⟨836084, by rfl⟩ : syracuseStep 1114779 = 1672169) B1672169
theorem B7635833 : Blo 1112627 7635833 := bstep (se 2 (by rfl) ⟨2863437, by rfl⟩ : syracuseStep 7635833 = 5726875) B5726875
theorem B9536687 : Blo 1112627 9536687 := bstep (se 1 (by rfl) ⟨7152515, by rfl⟩ : syracuseStep 9536687 = 14305031) B14305031
theorem B1673897 : Blo 1112627 1673897 := bstep (se 2 (by rfl) ⟨627711, by rfl⟩ : syracuseStep 1673897 = 1255423) B1255423
theorem B8040815 : Blo 1112627 8040815 := bstep (se 1 (by rfl) ⟨6030611, by rfl⟩ : syracuseStep 8040815 = 12061223) B12061223
theorem B2506031 : Blo 1112627 2506031 := bstep (se 1 (by rfl) ⟨1879523, by rfl⟩ : syracuseStep 2506031 = 3759047) B3759047
theorem B6357791 : Blo 1112627 6357791 := bstep (se 1 (by rfl) ⟨4768343, by rfl⟩ : syracuseStep 6357791 = 9536687) B9536687
theorem B1115931 : Blo 1112627 1115931 := bstep (se 1 (by rfl) ⟨836948, by rfl⟩ : syracuseStep 1115931 = 1673897) B1673897
theorem B5090555 : Blo 1112627 5090555 := bstep (se 1 (by rfl) ⟨3817916, by rfl⟩ : syracuseStep 5090555 = 7635833) B7635833
theorem B5360543 : Blo 1112627 5360543 := bstep (se 1 (by rfl) ⟨4020407, by rfl⟩ : syracuseStep 5360543 = 8040815) B8040815
theorem B1670687 : Blo 1112627 1670687 := bstep (se 1 (by rfl) ⟨1253015, by rfl⟩ : syracuseStep 1670687 = 2506031) B2506031
theorem B3573695 : Blo 1112627 3573695 := bstep (se 1 (by rfl) ⟨2680271, by rfl⟩ : syracuseStep 3573695 = 5360543) B5360543
theorem B4238527 : Blo 1112627 4238527 := bstep (se 1 (by rfl) ⟨3178895, by rfl⟩ : syracuseStep 4238527 = 6357791) B6357791
theorem B3393703 : Blo 1112627 3393703 := bstep (se 1 (by rfl) ⟨2545277, by rfl⟩ : syracuseStep 3393703 = 5090555) B5090555
theorem B1113791 : Blo 1112627 1113791 := bstep (se 1 (by rfl) ⟨835343, by rfl⟩ : syracuseStep 1113791 = 1670687) B1670687
theorem B18099749 : Blo 1112627 18099749 := bstep (se 4 (by rfl) ⟨1696851, by rfl⟩ : syracuseStep 18099749 = 3393703) B3393703
theorem B5651369 : Blo 1112627 5651369 := bstep (se 2 (by rfl) ⟨2119263, by rfl⟩ : syracuseStep 5651369 = 4238527) B4238527
theorem B2382463 : Blo 1112627 2382463 := bstep (se 1 (by rfl) ⟨1786847, by rfl⟩ : syracuseStep 2382463 = 3573695) B3573695
theorem B12066499 : Blo 1112627 12066499 := bstep (se 1 (by rfl) ⟨9049874, by rfl⟩ : syracuseStep 12066499 = 18099749) B18099749
theorem B12706469 : Blo 1112627 12706469 := bstep (se 4 (by rfl) ⟨1191231, by rfl⟩ : syracuseStep 12706469 = 2382463) B2382463
theorem B3767579 : Blo 1112627 3767579 := bstep (se 1 (by rfl) ⟨2825684, by rfl⟩ : syracuseStep 3767579 = 5651369) B5651369
theorem B8470979 : Blo 1112627 8470979 := bstep (se 1 (by rfl) ⟨6353234, by rfl⟩ : syracuseStep 8470979 = 12706469) B12706469
theorem B2511719 : Blo 1112627 2511719 := bstep (se 1 (by rfl) ⟨1883789, by rfl⟩ : syracuseStep 2511719 = 3767579) B3767579
theorem B16088665 : Blo 1112627 16088665 := bstep (se 2 (by rfl) ⟨6033249, by rfl⟩ : syracuseStep 16088665 = 12066499) B12066499
theorem B1674479 : Blo 1112627 1674479 := bstep (se 1 (by rfl) ⟨1255859, by rfl⟩ : syracuseStep 1674479 = 2511719) B2511719
theorem B5647319 : Blo 1112627 5647319 := bstep (se 1 (by rfl) ⟨4235489, by rfl⟩ : syracuseStep 5647319 = 8470979) B8470979
theorem B21451553 : Blo 1112627 21451553 := bstep (se 2 (by rfl) ⟨8044332, by rfl⟩ : syracuseStep 21451553 = 16088665) B16088665
theorem B1116319 : Blo 1112627 1116319 := bstep (se 1 (by rfl) ⟨837239, by rfl⟩ : syracuseStep 1116319 = 1674479) B1674479
theorem B14301035 : Blo 1112627 14301035 := bstep (se 1 (by rfl) ⟨10725776, by rfl⟩ : syracuseStep 14301035 = 21451553) B21451553
theorem B3764879 : Blo 1112627 3764879 := bstep (se 1 (by rfl) ⟨2823659, by rfl⟩ : syracuseStep 3764879 = 5647319) B5647319
theorem B2509919 : Blo 1112627 2509919 := bstep (se 1 (by rfl) ⟨1882439, by rfl⟩ : syracuseStep 2509919 = 3764879) B3764879
theorem B9534023 : Blo 1112627 9534023 := bstep (se 1 (by rfl) ⟨7150517, by rfl⟩ : syracuseStep 9534023 = 14301035) B14301035
theorem B1673279 : Blo 1112627 1673279 := bstep (se 1 (by rfl) ⟨1254959, by rfl⟩ : syracuseStep 1673279 = 2509919) B2509919
theorem B6356015 : Blo 1112627 6356015 := bstep (se 1 (by rfl) ⟨4767011, by rfl⟩ : syracuseStep 6356015 = 9534023) B9534023
theorem B1115519 : Blo 1112627 1115519 := bstep (se 1 (by rfl) ⟨836639, by rfl⟩ : syracuseStep 1115519 = 1673279) B1673279
theorem B4237343 : Blo 1112627 4237343 := bstep (se 1 (by rfl) ⟨3178007, by rfl⟩ : syracuseStep 4237343 = 6356015) B6356015
theorem B2824895 : Blo 1112627 2824895 := bstep (se 1 (by rfl) ⟨2118671, by rfl⟩ : syracuseStep 2824895 = 4237343) B4237343
theorem B1883263 : Blo 1112627 1883263 := bstep (se 1 (by rfl) ⟨1412447, by rfl⟩ : syracuseStep 1883263 = 2824895) B2824895
theorem B2511017 : Blo 1112627 2511017 := bstep (se 2 (by rfl) ⟨941631, by rfl⟩ : syracuseStep 2511017 = 1883263) B1883263
theorem B1674011 : Blo 1112627 1674011 := bstep (se 1 (by rfl) ⟨1255508, by rfl⟩ : syracuseStep 1674011 = 2511017) B2511017
theorem B1116007 : Blo 1112627 1116007 := bstep (se 1 (by rfl) ⟨837005, by rfl⟩ : syracuseStep 1116007 = 1674011) B1674011

theorem C0 (j : ℕ) (h1 : 278156 ≤ j) (h2 : j ≤ 278855) : Blo 1112627 (4 * j + 3) := by
  interval_cases j
  · exact B1112627
  · exact B1112631
  · exact B1112635
  · exact B1112639
  · exact B1112643
  · exact B1112647
  · exact B1112651
  · exact B1112655
  · exact B1112659
  · exact B1112663
  · exact B1112667
  · exact B1112671
  · exact B1112675
  · exact B1112679
  · exact B1112683
  · exact B1112687
  · exact B1112691
  · exact B1112695
  · exact B1112699
  · exact B1112703
  · exact B1112707
  · exact B1112711
  · exact B1112715
  · exact B1112719
  · exact B1112723
  · exact B1112727
  · exact B1112731
  · exact B1112735
  · exact B1112739
  · exact B1112743
  · exact B1112747
  · exact B1112751
  · exact B1112755
  · exact B1112759
  · exact B1112763
  · exact B1112767
  · exact B1112771
  · exact B1112775
  · exact B1112779
  · exact B1112783
  · exact B1112787
  · exact B1112791
  · exact B1112795
  · exact B1112799
  · exact B1112803
  · exact B1112807
  · exact B1112811
  · exact B1112815
  · exact B1112819
  · exact B1112823
  · exact B1112827
  · exact B1112831
  · exact B1112835
  · exact B1112839
  · exact B1112843
  · exact B1112847
  · exact B1112851
  · exact B1112855
  · exact B1112859
  · exact B1112863
  · exact B1112867
  · exact B1112871
  · exact B1112875
  · exact B1112879
  · exact B1112883
  · exact B1112887
  · exact B1112891
  · exact B1112895
  · exact B1112899
  · exact B1112903
  · exact B1112907
  · exact B1112911
  · exact B1112915
  · exact B1112919
  · exact B1112923
  · exact B1112927
  · exact B1112931
  · exact B1112935
  · exact B1112939
  · exact B1112943
  · exact B1112947
  · exact B1112951
  · exact B1112955
  · exact B1112959
  · exact B1112963
  · exact B1112967
  · exact B1112971
  · exact B1112975
  · exact B1112979
  · exact B1112983
  · exact B1112987
  · exact B1112991
  · exact B1112995
  · exact B1112999
  · exact B1113003
  · exact B1113007
  · exact B1113011
  · exact B1113015
  · exact B1113019
  · exact B1113023
  · exact B1113027
  · exact B1113031
  · exact B1113035
  · exact B1113039
  · exact B1113043
  · exact B1113047
  · exact B1113051
  · exact B1113055
  · exact B1113059
  · exact B1113063
  · exact B1113067
  · exact B1113071
  · exact B1113075
  · exact B1113079
  · exact B1113083
  · exact B1113087
  · exact B1113091
  · exact B1113095
  · exact B1113099
  · exact B1113103
  · exact B1113107
  · exact B1113111
  · exact B1113115
  · exact B1113119
  · exact B1113123
  · exact B1113127
  · exact B1113131
  · exact B1113135
  · exact B1113139
  · exact B1113143
  · exact B1113147
  · exact B1113151
  · exact B1113155
  · exact B1113159
  · exact B1113163
  · exact B1113167
  · exact B1113171
  · exact B1113175
  · exact B1113179
  · exact B1113183
  · exact B1113187
  · exact B1113191
  · exact B1113195
  · exact B1113199
  · exact B1113203
  · exact B1113207
  · exact B1113211
  · exact B1113215
  · exact B1113219
  · exact B1113223
  · exact B1113227
  · exact B1113231
  · exact B1113235
  · exact B1113239
  · exact B1113243
  · exact B1113247
  · exact B1113251
  · exact B1113255
  · exact B1113259
  · exact B1113263
  · exact B1113267
  · exact B1113271
  · exact B1113275
  · exact B1113279
  · exact B1113283
  · exact B1113287
  · exact B1113291
  · exact B1113295
  · exact B1113299
  · exact B1113303
  · exact B1113307
  · exact B1113311
  · exact B1113315
  · exact B1113319
  · exact B1113323
  · exact B1113327
  · exact B1113331
  · exact B1113335
  · exact B1113339
  · exact B1113343
  · exact B1113347
  · exact B1113351
  · exact B1113355
  · exact B1113359
  · exact B1113363
  · exact B1113367
  · exact B1113371
  · exact B1113375
  · exact B1113379
  · exact B1113383
  · exact B1113387
  · exact B1113391
  · exact B1113395
  · exact B1113399
  · exact B1113403
  · exact B1113407
  · exact B1113411
  · exact B1113415
  · exact B1113419
  · exact B1113423
  · exact B1113427
  · exact B1113431
  · exact B1113435
  · exact B1113439
  · exact B1113443
  · exact B1113447
  · exact B1113451
  · exact B1113455
  · exact B1113459
  · exact B1113463
  · exact B1113467
  · exact B1113471
  · exact B1113475
  · exact B1113479
  · exact B1113483
  · exact B1113487
  · exact B1113491
  · exact B1113495
  · exact B1113499
  · exact B1113503
  · exact B1113507
  · exact B1113511
  · exact B1113515
  · exact B1113519
  · exact B1113523
  · exact B1113527
  · exact B1113531
  · exact B1113535
  · exact B1113539
  · exact B1113543
  · exact B1113547
  · exact B1113551
  · exact B1113555
  · exact B1113559
  · exact B1113563
  · exact B1113567
  · exact B1113571
  · exact B1113575
  · exact B1113579
  · exact B1113583
  · exact B1113587
  · exact B1113591
  · exact B1113595
  · exact B1113599
  · exact B1113603
  · exact B1113607
  · exact B1113611
  · exact B1113615
  · exact B1113619
  · exact B1113623
  · exact B1113627
  · exact B1113631
  · exact B1113635
  · exact B1113639
  · exact B1113643
  · exact B1113647
  · exact B1113651
  · exact B1113655
  · exact B1113659
  · exact B1113663
  · exact B1113667
  · exact B1113671
  · exact B1113675
  · exact B1113679
  · exact B1113683
  · exact B1113687
  · exact B1113691
  · exact B1113695
  · exact B1113699
  · exact B1113703
  · exact B1113707
  · exact B1113711
  · exact B1113715
  · exact B1113719
  · exact B1113723
  · exact B1113727
  · exact B1113731
  · exact B1113735
  · exact B1113739
  · exact B1113743
  · exact B1113747
  · exact B1113751
  · exact B1113755
  · exact B1113759
  · exact B1113763
  · exact B1113767
  · exact B1113771
  · exact B1113775
  · exact B1113779
  · exact B1113783
  · exact B1113787
  · exact B1113791
  · exact B1113795
  · exact B1113799
  · exact B1113803
  · exact B1113807
  · exact B1113811
  · exact B1113815
  · exact B1113819
  · exact B1113823
  · exact B1113827
  · exact B1113831
  · exact B1113835
  · exact B1113839
  · exact B1113843
  · exact B1113847
  · exact B1113851
  · exact B1113855
  · exact B1113859
  · exact B1113863
  · exact B1113867
  · exact B1113871
  · exact B1113875
  · exact B1113879
  · exact B1113883
  · exact B1113887
  · exact B1113891
  · exact B1113895
  · exact B1113899
  · exact B1113903
  · exact B1113907
  · exact B1113911
  · exact B1113915
  · exact B1113919
  · exact B1113923
  · exact B1113927
  · exact B1113931
  · exact B1113935
  · exact B1113939
  · exact B1113943
  · exact B1113947
  · exact B1113951
  · exact B1113955
  · exact B1113959
  · exact B1113963
  · exact B1113967
  · exact B1113971
  · exact B1113975
  · exact B1113979
  · exact B1113983
  · exact B1113987
  · exact B1113991
  · exact B1113995
  · exact B1113999
  · exact B1114003
  · exact B1114007
  · exact B1114011
  · exact B1114015
  · exact B1114019
  · exact B1114023
  · exact B1114027
  · exact B1114031
  · exact B1114035
  · exact B1114039
  · exact B1114043
  · exact B1114047
  · exact B1114051
  · exact B1114055
  · exact B1114059
  · exact B1114063
  · exact B1114067
  · exact B1114071
  · exact B1114075
  · exact B1114079
  · exact B1114083
  · exact B1114087
  · exact B1114091
  · exact B1114095
  · exact B1114099
  · exact B1114103
  · exact B1114107
  · exact B1114111
  · exact B1114115
  · exact B1114119
  · exact B1114123
  · exact B1114127
  · exact B1114131
  · exact B1114135
  · exact B1114139
  · exact B1114143
  · exact B1114147
  · exact B1114151
  · exact B1114155
  · exact B1114159
  · exact B1114163
  · exact B1114167
  · exact B1114171
  · exact B1114175
  · exact B1114179
  · exact B1114183
  · exact B1114187
  · exact B1114191
  · exact B1114195
  · exact B1114199
  · exact B1114203
  · exact B1114207
  · exact B1114211
  · exact B1114215
  · exact B1114219
  · exact B1114223
  · exact B1114227
  · exact B1114231
  · exact B1114235
  · exact B1114239
  · exact B1114243
  · exact B1114247
  · exact B1114251
  · exact B1114255
  · exact B1114259
  · exact B1114263
  · exact B1114267
  · exact B1114271
  · exact B1114275
  · exact B1114279
  · exact B1114283
  · exact B1114287
  · exact B1114291
  · exact B1114295
  · exact B1114299
  · exact B1114303
  · exact B1114307
  · exact B1114311
  · exact B1114315
  · exact B1114319
  · exact B1114323
  · exact B1114327
  · exact B1114331
  · exact B1114335
  · exact B1114339
  · exact B1114343
  · exact B1114347
  · exact B1114351
  · exact B1114355
  · exact B1114359
  · exact B1114363
  · exact B1114367
  · exact B1114371
  · exact B1114375
  · exact B1114379
  · exact B1114383
  · exact B1114387
  · exact B1114391
  · exact B1114395
  · exact B1114399
  · exact B1114403
  · exact B1114407
  · exact B1114411
  · exact B1114415
  · exact B1114419
  · exact B1114423
  · exact B1114427
  · exact B1114431
  · exact B1114435
  · exact B1114439
  · exact B1114443
  · exact B1114447
  · exact B1114451
  · exact B1114455
  · exact B1114459
  · exact B1114463
  · exact B1114467
  · exact B1114471
  · exact B1114475
  · exact B1114479
  · exact B1114483
  · exact B1114487
  · exact B1114491
  · exact B1114495
  · exact B1114499
  · exact B1114503
  · exact B1114507
  · exact B1114511
  · exact B1114515
  · exact B1114519
  · exact B1114523
  · exact B1114527
  · exact B1114531
  · exact B1114535
  · exact B1114539
  · exact B1114543
  · exact B1114547
  · exact B1114551
  · exact B1114555
  · exact B1114559
  · exact B1114563
  · exact B1114567
  · exact B1114571
  · exact B1114575
  · exact B1114579
  · exact B1114583
  · exact B1114587
  · exact B1114591
  · exact B1114595
  · exact B1114599
  · exact B1114603
  · exact B1114607
  · exact B1114611
  · exact B1114615
  · exact B1114619
  · exact B1114623
  · exact B1114627
  · exact B1114631
  · exact B1114635
  · exact B1114639
  · exact B1114643
  · exact B1114647
  · exact B1114651
  · exact B1114655
  · exact B1114659
  · exact B1114663
  · exact B1114667
  · exact B1114671
  · exact B1114675
  · exact B1114679
  · exact B1114683
  · exact B1114687
  · exact B1114691
  · exact B1114695
  · exact B1114699
  · exact B1114703
  · exact B1114707
  · exact B1114711
  · exact B1114715
  · exact B1114719
  · exact B1114723
  · exact B1114727
  · exact B1114731
  · exact B1114735
  · exact B1114739
  · exact B1114743
  · exact B1114747
  · exact B1114751
  · exact B1114755
  · exact B1114759
  · exact B1114763
  · exact B1114767
  · exact B1114771
  · exact B1114775
  · exact B1114779
  · exact B1114783
  · exact B1114787
  · exact B1114791
  · exact B1114795
  · exact B1114799
  · exact B1114803
  · exact B1114807
  · exact B1114811
  · exact B1114815
  · exact B1114819
  · exact B1114823
  · exact B1114827
  · exact B1114831
  · exact B1114835
  · exact B1114839
  · exact B1114843
  · exact B1114847
  · exact B1114851
  · exact B1114855
  · exact B1114859
  · exact B1114863
  · exact B1114867
  · exact B1114871
  · exact B1114875
  · exact B1114879
  · exact B1114883
  · exact B1114887
  · exact B1114891
  · exact B1114895
  · exact B1114899
  · exact B1114903
  · exact B1114907
  · exact B1114911
  · exact B1114915
  · exact B1114919
  · exact B1114923
  · exact B1114927
  · exact B1114931
  · exact B1114935
  · exact B1114939
  · exact B1114943
  · exact B1114947
  · exact B1114951
  · exact B1114955
  · exact B1114959
  · exact B1114963
  · exact B1114967
  · exact B1114971
  · exact B1114975
  · exact B1114979
  · exact B1114983
  · exact B1114987
  · exact B1114991
  · exact B1114995
  · exact B1114999
  · exact B1115003
  · exact B1115007
  · exact B1115011
  · exact B1115015
  · exact B1115019
  · exact B1115023
  · exact B1115027
  · exact B1115031
  · exact B1115035
  · exact B1115039
  · exact B1115043
  · exact B1115047
  · exact B1115051
  · exact B1115055
  · exact B1115059
  · exact B1115063
  · exact B1115067
  · exact B1115071
  · exact B1115075
  · exact B1115079
  · exact B1115083
  · exact B1115087
  · exact B1115091
  · exact B1115095
  · exact B1115099
  · exact B1115103
  · exact B1115107
  · exact B1115111
  · exact B1115115
  · exact B1115119
  · exact B1115123
  · exact B1115127
  · exact B1115131
  · exact B1115135
  · exact B1115139
  · exact B1115143
  · exact B1115147
  · exact B1115151
  · exact B1115155
  · exact B1115159
  · exact B1115163
  · exact B1115167
  · exact B1115171
  · exact B1115175
  · exact B1115179
  · exact B1115183
  · exact B1115187
  · exact B1115191
  · exact B1115195
  · exact B1115199
  · exact B1115203
  · exact B1115207
  · exact B1115211
  · exact B1115215
  · exact B1115219
  · exact B1115223
  · exact B1115227
  · exact B1115231
  · exact B1115235
  · exact B1115239
  · exact B1115243
  · exact B1115247
  · exact B1115251
  · exact B1115255
  · exact B1115259
  · exact B1115263
  · exact B1115267
  · exact B1115271
  · exact B1115275
  · exact B1115279
  · exact B1115283
  · exact B1115287
  · exact B1115291
  · exact B1115295
  · exact B1115299
  · exact B1115303
  · exact B1115307
  · exact B1115311
  · exact B1115315
  · exact B1115319
  · exact B1115323
  · exact B1115327
  · exact B1115331
  · exact B1115335
  · exact B1115339
  · exact B1115343
  · exact B1115347
  · exact B1115351
  · exact B1115355
  · exact B1115359
  · exact B1115363
  · exact B1115367
  · exact B1115371
  · exact B1115375
  · exact B1115379
  · exact B1115383
  · exact B1115387
  · exact B1115391
  · exact B1115395
  · exact B1115399
  · exact B1115403
  · exact B1115407
  · exact B1115411
  · exact B1115415
  · exact B1115419
  · exact B1115423

theorem C1 (j : ℕ) (h1 : 278856 ≤ j) (h2 : j ≤ 279156) : Blo 1112627 (4 * j + 3) := by
  interval_cases j
  · exact B1115427
  · exact B1115431
  · exact B1115435
  · exact B1115439
  · exact B1115443
  · exact B1115447
  · exact B1115451
  · exact B1115455
  · exact B1115459
  · exact B1115463
  · exact B1115467
  · exact B1115471
  · exact B1115475
  · exact B1115479
  · exact B1115483
  · exact B1115487
  · exact B1115491
  · exact B1115495
  · exact B1115499
  · exact B1115503
  · exact B1115507
  · exact B1115511
  · exact B1115515
  · exact B1115519
  · exact B1115523
  · exact B1115527
  · exact B1115531
  · exact B1115535
  · exact B1115539
  · exact B1115543
  · exact B1115547
  · exact B1115551
  · exact B1115555
  · exact B1115559
  · exact B1115563
  · exact B1115567
  · exact B1115571
  · exact B1115575
  · exact B1115579
  · exact B1115583
  · exact B1115587
  · exact B1115591
  · exact B1115595
  · exact B1115599
  · exact B1115603
  · exact B1115607
  · exact B1115611
  · exact B1115615
  · exact B1115619
  · exact B1115623
  · exact B1115627
  · exact B1115631
  · exact B1115635
  · exact B1115639
  · exact B1115643
  · exact B1115647
  · exact B1115651
  · exact B1115655
  · exact B1115659
  · exact B1115663
  · exact B1115667
  · exact B1115671
  · exact B1115675
  · exact B1115679
  · exact B1115683
  · exact B1115687
  · exact B1115691
  · exact B1115695
  · exact B1115699
  · exact B1115703
  · exact B1115707
  · exact B1115711
  · exact B1115715
  · exact B1115719
  · exact B1115723
  · exact B1115727
  · exact B1115731
  · exact B1115735
  · exact B1115739
  · exact B1115743
  · exact B1115747
  · exact B1115751
  · exact B1115755
  · exact B1115759
  · exact B1115763
  · exact B1115767
  · exact B1115771
  · exact B1115775
  · exact B1115779
  · exact B1115783
  · exact B1115787
  · exact B1115791
  · exact B1115795
  · exact B1115799
  · exact B1115803
  · exact B1115807
  · exact B1115811
  · exact B1115815
  · exact B1115819
  · exact B1115823
  · exact B1115827
  · exact B1115831
  · exact B1115835
  · exact B1115839
  · exact B1115843
  · exact B1115847
  · exact B1115851
  · exact B1115855
  · exact B1115859
  · exact B1115863
  · exact B1115867
  · exact B1115871
  · exact B1115875
  · exact B1115879
  · exact B1115883
  · exact B1115887
  · exact B1115891
  · exact B1115895
  · exact B1115899
  · exact B1115903
  · exact B1115907
  · exact B1115911
  · exact B1115915
  · exact B1115919
  · exact B1115923
  · exact B1115927
  · exact B1115931
  · exact B1115935
  · exact B1115939
  · exact B1115943
  · exact B1115947
  · exact B1115951
  · exact B1115955
  · exact B1115959
  · exact B1115963
  · exact B1115967
  · exact B1115971
  · exact B1115975
  · exact B1115979
  · exact B1115983
  · exact B1115987
  · exact B1115991
  · exact B1115995
  · exact B1115999
  · exact B1116003
  · exact B1116007
  · exact B1116011
  · exact B1116015
  · exact B1116019
  · exact B1116023
  · exact B1116027
  · exact B1116031
  · exact B1116035
  · exact B1116039
  · exact B1116043
  · exact B1116047
  · exact B1116051
  · exact B1116055
  · exact B1116059
  · exact B1116063
  · exact B1116067
  · exact B1116071
  · exact B1116075
  · exact B1116079
  · exact B1116083
  · exact B1116087
  · exact B1116091
  · exact B1116095
  · exact B1116099
  · exact B1116103
  · exact B1116107
  · exact B1116111
  · exact B1116115
  · exact B1116119
  · exact B1116123
  · exact B1116127
  · exact B1116131
  · exact B1116135
  · exact B1116139
  · exact B1116143
  · exact B1116147
  · exact B1116151
  · exact B1116155
  · exact B1116159
  · exact B1116163
  · exact B1116167
  · exact B1116171
  · exact B1116175
  · exact B1116179
  · exact B1116183
  · exact B1116187
  · exact B1116191
  · exact B1116195
  · exact B1116199
  · exact B1116203
  · exact B1116207
  · exact B1116211
  · exact B1116215
  · exact B1116219
  · exact B1116223
  · exact B1116227
  · exact B1116231
  · exact B1116235
  · exact B1116239
  · exact B1116243
  · exact B1116247
  · exact B1116251
  · exact B1116255
  · exact B1116259
  · exact B1116263
  · exact B1116267
  · exact B1116271
  · exact B1116275
  · exact B1116279
  · exact B1116283
  · exact B1116287
  · exact B1116291
  · exact B1116295
  · exact B1116299
  · exact B1116303
  · exact B1116307
  · exact B1116311
  · exact B1116315
  · exact B1116319
  · exact B1116323
  · exact B1116327
  · exact B1116331
  · exact B1116335
  · exact B1116339
  · exact B1116343
  · exact B1116347
  · exact B1116351
  · exact B1116355
  · exact B1116359
  · exact B1116363
  · exact B1116367
  · exact B1116371
  · exact B1116375
  · exact B1116379
  · exact B1116383
  · exact B1116387
  · exact B1116391
  · exact B1116395
  · exact B1116399
  · exact B1116403
  · exact B1116407
  · exact B1116411
  · exact B1116415
  · exact B1116419
  · exact B1116423
  · exact B1116427
  · exact B1116431
  · exact B1116435
  · exact B1116439
  · exact B1116443
  · exact B1116447
  · exact B1116451
  · exact B1116455
  · exact B1116459
  · exact B1116463
  · exact B1116467
  · exact B1116471
  · exact B1116475
  · exact B1116479
  · exact B1116483
  · exact B1116487
  · exact B1116491
  · exact B1116495
  · exact B1116499
  · exact B1116503
  · exact B1116507
  · exact B1116511
  · exact B1116515
  · exact B1116519
  · exact B1116523
  · exact B1116527
  · exact B1116531
  · exact B1116535
  · exact B1116539
  · exact B1116543
  · exact B1116547
  · exact B1116551
  · exact B1116555
  · exact B1116559
  · exact B1116563
  · exact B1116567
  · exact B1116571
  · exact B1116575
  · exact B1116579
  · exact B1116583
  · exact B1116587
  · exact B1116591
  · exact B1116595
  · exact B1116599
  · exact B1116603
  · exact B1116607
  · exact B1116611
  · exact B1116615
  · exact B1116619
  · exact B1116623
  · exact B1116627

theorem solution (m : ℕ) (hlo : 1112627 ≤ m) (hhi : m ≤ 1116627) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 278156 ≤ j := by omega
    have hj2 : j ≤ 279156 := by omega
    have hb : Blo 1112627 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 278856 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
