-- Prove2me | solution 1 for syracuse_descends_range_1835619_1837619
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:01:52.279268+00:00
-- url     : https://prove2.me/submissions/a97fb1cf-ddef-4f40-a925-82497595ca27

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


theorem B7954469 : Blo 1835619 7954469 := bbase (se 4 (by rfl) ⟨745731, by rfl⟩ : syracuseStep 7954469 = 1491463) (by norm_num)
theorem B9297989 : Blo 1835619 9297989 := bbase (se 4 (by rfl) ⟨871686, by rfl⟩ : syracuseStep 9297989 = 1743373) (by norm_num)
theorem B6201413 : Blo 1835619 6201413 := bbase (se 4 (by rfl) ⟨581382, by rfl⟩ : syracuseStep 6201413 = 1162765) (by norm_num)
theorem B11772053 : Blo 1835619 11772053 := bbase (se 6 (by rfl) ⟨275907, by rfl⟩ : syracuseStep 11772053 = 551815) (by norm_num)
theorem B2941085 : Blo 1835619 2941085 := bbase (se 3 (by rfl) ⟨551453, by rfl⟩ : syracuseStep 2941085 = 1102907) (by norm_num)
theorem B11166101 : Blo 1835619 11166101 := bbase (se 6 (by rfl) ⟨261705, by rfl⟩ : syracuseStep 11166101 = 523411) (by norm_num)
theorem B2941373 : Blo 1835619 2941373 := bbase (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) (by norm_num)
theorem B6619589 : Blo 1835619 6619589 := bbase (se 4 (by rfl) ⟨620586, by rfl⟩ : syracuseStep 6619589 = 1241173) (by norm_num)
theorem B15696341 : Blo 1835619 15696341 := bbase (se 7 (by rfl) ⟨183941, by rfl⟩ : syracuseStep 15696341 = 367883) (by norm_num)
theorem B6201845 : Blo 1835619 6201845 := bbase (se 5 (by rfl) ⟨290711, by rfl⟩ : syracuseStep 6201845 = 581423) (by norm_num)
theorem B7168517 : Blo 1835619 7168517 := bbase (se 4 (by rfl) ⟨672048, by rfl⟩ : syracuseStep 7168517 = 1344097) (by norm_num)
theorem B3310141 : Blo 1835619 3310141 := bbase (se 3 (by rfl) ⟨620651, by rfl⟩ : syracuseStep 3310141 = 1241303) (by norm_num)
theorem B2065081 : Blo 1835619 2065081 := bbase (se 2 (by rfl) ⟨774405, by rfl⟩ : syracuseStep 2065081 = 1548811) (by norm_num)
theorem B2065117 : Blo 1835619 2065117 := bbase (se 3 (by rfl) ⟨387209, by rfl⟩ : syracuseStep 2065117 = 774419) (by norm_num)
theorem B2613989 : Blo 1835619 2613989 := bbase (se 4 (by rfl) ⟨245061, by rfl⟩ : syracuseStep 2613989 = 490123) (by norm_num)
theorem B2065153 : Blo 1835619 2065153 := bbase (se 2 (by rfl) ⟨774432, by rfl⟩ : syracuseStep 2065153 = 1548865) (by norm_num)
theorem B27214613 : Blo 1835619 27214613 := bbase (se 6 (by rfl) ⟨637842, by rfl⟩ : syracuseStep 27214613 = 1275685) (by norm_num)
theorem B2065189 : Blo 1835619 2065189 := bbase (se 4 (by rfl) ⟨193611, by rfl⟩ : syracuseStep 2065189 = 387223) (by norm_num)
theorem B2614069 : Blo 1835619 2614069 := bbase (se 5 (by rfl) ⟨122534, by rfl⟩ : syracuseStep 2614069 = 245069) (by norm_num)
theorem B2065225 : Blo 1835619 2065225 := bbase (se 2 (by rfl) ⟨774459, by rfl⟩ : syracuseStep 2065225 = 1548919) (by norm_num)
theorem B2065261 : Blo 1835619 2065261 := bbase (se 3 (by rfl) ⟨387236, by rfl⟩ : syracuseStep 2065261 = 774473) (by norm_num)
theorem B6972277 : Blo 1835619 6972277 := bbase (se 5 (by rfl) ⟨326825, by rfl⟩ : syracuseStep 6972277 = 653651) (by norm_num)
theorem B2065297 : Blo 1835619 2065297 := bbase (se 2 (by rfl) ⟨774486, by rfl⟩ : syracuseStep 2065297 = 1548973) (by norm_num)
theorem B2753429 : Blo 1835619 2753429 := bbase (se 6 (by rfl) ⟨64533, by rfl⟩ : syracuseStep 2753429 = 129067) (by norm_num)
theorem B2753453 : Blo 1835619 2753453 := bbase (se 3 (by rfl) ⟨516272, by rfl⟩ : syracuseStep 2753453 = 1032545) (by norm_num)
theorem B2614189 : Blo 1835619 2614189 := bbase (se 3 (by rfl) ⟨490160, by rfl⟩ : syracuseStep 2614189 = 980321) (by norm_num)
theorem B2065333 : Blo 1835619 2065333 := bbase (se 5 (by rfl) ⟨96812, by rfl⟩ : syracuseStep 2065333 = 193625) (by norm_num)
theorem B2753477 : Blo 1835619 2753477 := bbase (se 4 (by rfl) ⟨258138, by rfl⟩ : syracuseStep 2753477 = 516277) (by norm_num)
theorem B11764693 : Blo 1835619 11764693 := bbase (se 7 (by rfl) ⟨137867, by rfl⟩ : syracuseStep 11764693 = 275735) (by norm_num)
theorem B2065369 : Blo 1835619 2065369 := bbase (se 2 (by rfl) ⟨774513, by rfl⟩ : syracuseStep 2065369 = 1549027) (by norm_num)
theorem B2753501 : Blo 1835619 2753501 := bbase (se 3 (by rfl) ⟨516281, by rfl⟩ : syracuseStep 2753501 = 1032563) (by norm_num)
theorem B2753525 : Blo 1835619 2753525 := bbase (se 5 (by rfl) ⟨129071, by rfl⟩ : syracuseStep 2753525 = 258143) (by norm_num)
theorem B2065405 : Blo 1835619 2065405 := bbase (se 3 (by rfl) ⟨387263, by rfl⟩ : syracuseStep 2065405 = 774527) (by norm_num)
theorem B2753549 : Blo 1835619 2753549 := bbase (se 3 (by rfl) ⟨516290, by rfl⟩ : syracuseStep 2753549 = 1032581) (by norm_num)
theorem B2614285 : Blo 1835619 2614285 := bbase (se 3 (by rfl) ⟨490178, by rfl⟩ : syracuseStep 2614285 = 980357) (by norm_num)
theorem B2065441 : Blo 1835619 2065441 := bbase (se 2 (by rfl) ⟨774540, by rfl⟩ : syracuseStep 2065441 = 1549081) (by norm_num)
theorem B2753573 : Blo 1835619 2753573 := bbase (se 4 (by rfl) ⟨258147, by rfl⟩ : syracuseStep 2753573 = 516295) (by norm_num)
theorem B3310637 : Blo 1835619 3310637 := bbase (se 3 (by rfl) ⟨620744, by rfl⟩ : syracuseStep 3310637 = 1241489) (by norm_num)
theorem B2753597 : Blo 1835619 2753597 := bbase (se 3 (by rfl) ⟨516299, by rfl⟩ : syracuseStep 2753597 = 1032599) (by norm_num)
theorem B3097669 : Blo 1835619 3097669 := bbase (se 4 (by rfl) ⟨290406, by rfl⟩ : syracuseStep 3097669 = 580813) (by norm_num)
theorem B2065477 : Blo 1835619 2065477 := bbase (se 4 (by rfl) ⟨193638, by rfl⟩ : syracuseStep 2065477 = 387277) (by norm_num)
theorem B6284357 : Blo 1835619 6284357 := bbase (se 4 (by rfl) ⟨589158, by rfl⟩ : syracuseStep 6284357 = 1178317) (by norm_num)
theorem B2753621 : Blo 1835619 2753621 := bbase (se 8 (by rfl) ⟨16134, by rfl⟩ : syracuseStep 2753621 = 32269) (by norm_num)
theorem B2065513 : Blo 1835619 2065513 := bbase (se 2 (by rfl) ⟨774567, by rfl⟩ : syracuseStep 2065513 = 1549135) (by norm_num)
theorem B2753645 : Blo 1835619 2753645 := bbase (se 3 (by rfl) ⟨516308, by rfl⟩ : syracuseStep 2753645 = 1032617) (by norm_num)
theorem B2753669 : Blo 1835619 2753669 := bbase (se 4 (by rfl) ⟨258156, by rfl⟩ : syracuseStep 2753669 = 516313) (by norm_num)
theorem B2065549 : Blo 1835619 2065549 := bbase (se 3 (by rfl) ⟨387290, by rfl⟩ : syracuseStep 2065549 = 774581) (by norm_num)
theorem B3097757 : Blo 1835619 3097757 := bbase (se 3 (by rfl) ⟨580829, by rfl⟩ : syracuseStep 3097757 = 1161659) (by norm_num)
theorem B2753693 : Blo 1835619 2753693 := bbase (se 3 (by rfl) ⟨516317, by rfl⟩ : syracuseStep 2753693 = 1032635) (by norm_num)
theorem B6972581 : Blo 1835619 6972581 := bbase (se 4 (by rfl) ⟨653679, by rfl⟩ : syracuseStep 6972581 = 1307359) (by norm_num)
theorem B7070885 : Blo 1835619 7070885 := bbase (se 4 (by rfl) ⟨662895, by rfl⟩ : syracuseStep 7070885 = 1325791) (by norm_num)
theorem B2065585 : Blo 1835619 2065585 := bbase (se 2 (by rfl) ⟨774594, by rfl⟩ : syracuseStep 2065585 = 1549189) (by norm_num)
theorem B2753717 : Blo 1835619 2753717 := bbase (se 5 (by rfl) ⟨129080, by rfl⟩ : syracuseStep 2753717 = 258161) (by norm_num)
theorem B2483389 : Blo 1835619 2483389 := bbase (se 3 (by rfl) ⟨465635, by rfl⟩ : syracuseStep 2483389 = 931271) (by norm_num)
theorem B2753741 : Blo 1835619 2753741 := bbase (se 3 (by rfl) ⟨516326, by rfl⟩ : syracuseStep 2753741 = 1032653) (by norm_num)
theorem B2065621 : Blo 1835619 2065621 := bbase (se 7 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 2065621 = 48413) (by norm_num)
theorem B2942173 : Blo 1835619 2942173 := bbase (se 3 (by rfl) ⟨551657, by rfl⟩ : syracuseStep 2942173 = 1103315) (by norm_num)
theorem B2753765 : Blo 1835619 2753765 := bbase (se 4 (by rfl) ⟨258165, by rfl⟩ : syracuseStep 2753765 = 516331) (by norm_num)
theorem B2065657 : Blo 1835619 2065657 := bbase (se 2 (by rfl) ⟨774621, by rfl⟩ : syracuseStep 2065657 = 1549243) (by norm_num)
theorem B2753789 : Blo 1835619 2753789 := bbase (se 3 (by rfl) ⟨516335, by rfl⟩ : syracuseStep 2753789 = 1032671) (by norm_num)
theorem B2753813 : Blo 1835619 2753813 := bbase (se 6 (by rfl) ⟨64542, by rfl⟩ : syracuseStep 2753813 = 129085) (by norm_num)
theorem B3097885 : Blo 1835619 3097885 := bbase (se 3 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 3097885 = 1161707) (by norm_num)
theorem B2065693 : Blo 1835619 2065693 := bbase (se 3 (by rfl) ⟨387317, by rfl⟩ : syracuseStep 2065693 = 774635) (by norm_num)
theorem B2753837 : Blo 1835619 2753837 := bbase (se 3 (by rfl) ⟨516344, by rfl⟩ : syracuseStep 2753837 = 1032689) (by norm_num)
theorem B10462517 : Blo 1835619 10462517 := bbase (se 5 (by rfl) ⟨490430, by rfl⟩ : syracuseStep 10462517 = 980861) (by norm_num)
theorem B2065729 : Blo 1835619 2065729 := bbase (se 2 (by rfl) ⟨774648, by rfl⟩ : syracuseStep 2065729 = 1549297) (by norm_num)
theorem B2753861 : Blo 1835619 2753861 := bbase (se 4 (by rfl) ⟨258174, by rfl⟩ : syracuseStep 2753861 = 516349) (by norm_num)
theorem B9299285 : Blo 1835619 9299285 := bbase (se 12 (by rfl) ⟨3405, by rfl⟩ : syracuseStep 9299285 = 6811) (by norm_num)
theorem B2753885 : Blo 1835619 2753885 := bbase (se 3 (by rfl) ⟨516353, by rfl⟩ : syracuseStep 2753885 = 1032707) (by norm_num)
theorem B2065765 : Blo 1835619 2065765 := bbase (se 4 (by rfl) ⟨193665, by rfl⟩ : syracuseStep 2065765 = 387331) (by norm_num)
theorem B3097973 : Blo 1835619 3097973 := bbase (se 5 (by rfl) ⟨145217, by rfl⟩ : syracuseStep 3097973 = 290435) (by norm_num)
theorem B2753909 : Blo 1835619 2753909 := bbase (se 5 (by rfl) ⟨129089, by rfl⟩ : syracuseStep 2753909 = 258179) (by norm_num)
theorem B1860985 : Blo 1835619 1860985 := bbase (se 2 (by rfl) ⟨697869, by rfl⟩ : syracuseStep 1860985 = 1395739) (by norm_num)
theorem B7849349 : Blo 1835619 7849349 := bbase (se 4 (by rfl) ⟨735876, by rfl⟩ : syracuseStep 7849349 = 1471753) (by norm_num)
theorem B2065801 : Blo 1835619 2065801 := bbase (se 2 (by rfl) ⟨774675, by rfl⟩ : syracuseStep 2065801 = 1549351) (by norm_num)
theorem B4130189 : Blo 1835619 4130189 := bbase (se 3 (by rfl) ⟨774410, by rfl⟩ : syracuseStep 4130189 = 1548821) (by norm_num)
theorem B2753933 : Blo 1835619 2753933 := bbase (se 3 (by rfl) ⟨516362, by rfl⟩ : syracuseStep 2753933 = 1032725) (by norm_num)
theorem B2753957 : Blo 1835619 2753957 := bbase (se 4 (by rfl) ⟨258183, by rfl⟩ : syracuseStep 2753957 = 516367) (by norm_num)
theorem B2065837 : Blo 1835619 2065837 := bbase (se 3 (by rfl) ⟨387344, by rfl⟩ : syracuseStep 2065837 = 774689) (by norm_num)
theorem B10454453 : Blo 1835619 10454453 := bbase (se 5 (by rfl) ⟨490052, by rfl⟩ : syracuseStep 10454453 = 980105) (by norm_num)
theorem B2753981 : Blo 1835619 2753981 := bbase (se 3 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 2753981 = 1032743) (by norm_num)
theorem B2065873 : Blo 1835619 2065873 := bbase (se 2 (by rfl) ⟨774702, by rfl⟩ : syracuseStep 2065873 = 1549405) (by norm_num)
theorem B4130261 : Blo 1835619 4130261 := bbase (se 7 (by rfl) ⟨48401, by rfl⟩ : syracuseStep 4130261 = 96803) (by norm_num)
theorem B2754005 : Blo 1835619 2754005 := bbase (se 7 (by rfl) ⟨32273, by rfl⟩ : syracuseStep 2754005 = 64547) (by norm_num)
theorem B2754029 : Blo 1835619 2754029 := bbase (se 3 (by rfl) ⟨516380, by rfl⟩ : syracuseStep 2754029 = 1032761) (by norm_num)
theorem B3098101 : Blo 1835619 3098101 := bbase (se 5 (by rfl) ⟨145223, by rfl⟩ : syracuseStep 3098101 = 290447) (by norm_num)
theorem B2065909 : Blo 1835619 2065909 := bbase (se 5 (by rfl) ⟨96839, by rfl⟩ : syracuseStep 2065909 = 193679) (by norm_num)
theorem B2614781 : Blo 1835619 2614781 := bbase (se 3 (by rfl) ⟨490271, by rfl⟩ : syracuseStep 2614781 = 980543) (by norm_num)
theorem B7841285 : Blo 1835619 7841285 := bbase (se 4 (by rfl) ⟨735120, by rfl⟩ : syracuseStep 7841285 = 1470241) (by norm_num)
theorem B2754053 : Blo 1835619 2754053 := bbase (se 4 (by rfl) ⟨258192, by rfl⟩ : syracuseStep 2754053 = 516385) (by norm_num)
theorem B2065945 : Blo 1835619 2065945 := bbase (se 2 (by rfl) ⟨774729, by rfl⟩ : syracuseStep 2065945 = 1549459) (by norm_num)
theorem B4130333 : Blo 1835619 4130333 := bbase (se 3 (by rfl) ⟨774437, by rfl⟩ : syracuseStep 4130333 = 1548875) (by norm_num)
theorem B2754077 : Blo 1835619 2754077 := bbase (se 3 (by rfl) ⟨516389, by rfl⟩ : syracuseStep 2754077 = 1032779) (by norm_num)
theorem B2754101 : Blo 1835619 2754101 := bbase (se 5 (by rfl) ⟨129098, by rfl⟩ : syracuseStep 2754101 = 258197) (by norm_num)
theorem B2065981 : Blo 1835619 2065981 := bbase (se 3 (by rfl) ⟨387371, by rfl⟩ : syracuseStep 2065981 = 774743) (by norm_num)
theorem B3098189 : Blo 1835619 3098189 := bbase (se 3 (by rfl) ⟨580910, by rfl⟩ : syracuseStep 3098189 = 1161821) (by norm_num)
theorem B2754125 : Blo 1835619 2754125 := bbase (se 3 (by rfl) ⟨516398, by rfl⟩ : syracuseStep 2754125 = 1032797) (by norm_num)
theorem B13239893 : Blo 1835619 13239893 := bbase (se 8 (by rfl) ⟨77577, by rfl⟩ : syracuseStep 13239893 = 155155) (by norm_num)
theorem B2066017 : Blo 1835619 2066017 := bbase (se 2 (by rfl) ⟨774756, by rfl⟩ : syracuseStep 2066017 = 1549513) (by norm_num)
theorem B4130405 : Blo 1835619 4130405 := bbase (se 4 (by rfl) ⟨387225, by rfl⟩ : syracuseStep 4130405 = 774451) (by norm_num)
theorem B2754149 : Blo 1835619 2754149 := bbase (se 4 (by rfl) ⟨258201, by rfl⟩ : syracuseStep 2754149 = 516403) (by norm_num)
theorem B2754173 : Blo 1835619 2754173 := bbase (se 3 (by rfl) ⟨516407, by rfl⟩ : syracuseStep 2754173 = 1032815) (by norm_num)
theorem B2066053 : Blo 1835619 2066053 := bbase (se 4 (by rfl) ⟨193692, by rfl⟩ : syracuseStep 2066053 = 387385) (by norm_num)
theorem B2754197 : Blo 1835619 2754197 := bbase (se 6 (by rfl) ⟨64551, by rfl⟩ : syracuseStep 2754197 = 129103) (by norm_num)
theorem B2066089 : Blo 1835619 2066089 := bbase (se 2 (by rfl) ⟨774783, by rfl⟩ : syracuseStep 2066089 = 1549567) (by norm_num)
theorem B4130477 : Blo 1835619 4130477 := bbase (se 3 (by rfl) ⟨774464, by rfl⟩ : syracuseStep 4130477 = 1548929) (by norm_num)
theorem B2754221 : Blo 1835619 2754221 := bbase (se 3 (by rfl) ⟨516416, by rfl⟩ : syracuseStep 2754221 = 1032833) (by norm_num)
theorem B2754245 : Blo 1835619 2754245 := bbase (se 4 (by rfl) ⟨258210, by rfl⟩ : syracuseStep 2754245 = 516421) (by norm_num)
theorem B4646605 : Blo 1835619 4646605 := bbase (se 3 (by rfl) ⟨871238, by rfl⟩ : syracuseStep 4646605 = 1742477) (by norm_num)
theorem B3098317 : Blo 1835619 3098317 := bbase (se 3 (by rfl) ⟨580934, by rfl⟩ : syracuseStep 3098317 = 1161869) (by norm_num)
theorem B2066125 : Blo 1835619 2066125 := bbase (se 3 (by rfl) ⟨387398, by rfl⟩ : syracuseStep 2066125 = 774797) (by norm_num)
theorem B2754269 : Blo 1835619 2754269 := bbase (se 3 (by rfl) ⟨516425, by rfl⟩ : syracuseStep 2754269 = 1032851) (by norm_num)
theorem B2066161 : Blo 1835619 2066161 := bbase (se 2 (by rfl) ⟨774810, by rfl⟩ : syracuseStep 2066161 = 1549621) (by norm_num)
theorem B4130549 : Blo 1835619 4130549 := bbase (se 5 (by rfl) ⟨193619, by rfl⟩ : syracuseStep 4130549 = 387239) (by norm_num)
theorem B2754293 : Blo 1835619 2754293 := bbase (se 5 (by rfl) ⟨129107, by rfl⟩ : syracuseStep 2754293 = 258215) (by norm_num)
theorem B2942725 : Blo 1835619 2942725 := bbase (se 4 (by rfl) ⟨275880, by rfl⟩ : syracuseStep 2942725 = 551761) (by norm_num)
theorem B2754317 : Blo 1835619 2754317 := bbase (se 3 (by rfl) ⟨516434, by rfl⟩ : syracuseStep 2754317 = 1032869) (by norm_num)
theorem B2066197 : Blo 1835619 2066197 := bbase (se 6 (by rfl) ⟨48426, by rfl⟩ : syracuseStep 2066197 = 96853) (by norm_num)
theorem B3098405 : Blo 1835619 3098405 := bbase (se 4 (by rfl) ⟨290475, by rfl⟩ : syracuseStep 3098405 = 580951) (by norm_num)
theorem B2754341 : Blo 1835619 2754341 := bbase (se 4 (by rfl) ⟨258219, by rfl⟩ : syracuseStep 2754341 = 516439) (by norm_num)
theorem B2066233 : Blo 1835619 2066233 := bbase (se 2 (by rfl) ⟨774837, by rfl⟩ : syracuseStep 2066233 = 1549675) (by norm_num)
theorem B4646717 : Blo 1835619 4646717 := bbase (se 3 (by rfl) ⟨871259, by rfl⟩ : syracuseStep 4646717 = 1742519) (by norm_num)
theorem B4130621 : Blo 1835619 4130621 := bbase (se 3 (by rfl) ⟨774491, by rfl⟩ : syracuseStep 4130621 = 1548983) (by norm_num)
theorem B2754365 : Blo 1835619 2754365 := bbase (se 3 (by rfl) ⟨516443, by rfl⟩ : syracuseStep 2754365 = 1032887) (by norm_num)
theorem B4187965 : Blo 1835619 4187965 := bbase (se 3 (by rfl) ⟨785243, by rfl⟩ : syracuseStep 4187965 = 1570487) (by norm_num)
theorem B2754389 : Blo 1835619 2754389 := bbase (se 9 (by rfl) ⟨8069, by rfl⟩ : syracuseStep 2754389 = 16139) (by norm_num)
theorem B2066269 : Blo 1835619 2066269 := bbase (se 3 (by rfl) ⟨387425, by rfl⟩ : syracuseStep 2066269 = 774851) (by norm_num)
theorem B2754413 : Blo 1835619 2754413 := bbase (se 3 (by rfl) ⟨516452, by rfl⟩ : syracuseStep 2754413 = 1032905) (by norm_num)
theorem B9930613 : Blo 1835619 9930613 := bbase (se 5 (by rfl) ⟨465497, by rfl⟩ : syracuseStep 9930613 = 930995) (by norm_num)
theorem B2066305 : Blo 1835619 2066305 := bbase (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) (by norm_num)
theorem B4130693 : Blo 1835619 4130693 := bbase (se 4 (by rfl) ⟨387252, by rfl⟩ : syracuseStep 4130693 = 774505) (by norm_num)
theorem B2754437 : Blo 1835619 2754437 := bbase (se 4 (by rfl) ⟨258228, by rfl⟩ : syracuseStep 2754437 = 516457) (by norm_num)
theorem B2754461 : Blo 1835619 2754461 := bbase (se 3 (by rfl) ⟨516461, by rfl⟩ : syracuseStep 2754461 = 1032923) (by norm_num)
theorem B3098533 : Blo 1835619 3098533 := bbase (se 4 (by rfl) ⟨290487, by rfl⟩ : syracuseStep 3098533 = 580975) (by norm_num)
theorem B2066341 : Blo 1835619 2066341 := bbase (se 4 (by rfl) ⟨193719, by rfl⟩ : syracuseStep 2066341 = 387439) (by norm_num)
theorem B1861553 : Blo 1835619 1861553 := bbase (se 2 (by rfl) ⟨698082, by rfl⟩ : syracuseStep 1861553 = 1396165) (by norm_num)
theorem B2754485 : Blo 1835619 2754485 := bbase (se 5 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 2754485 = 258233) (by norm_num)
theorem B2066377 : Blo 1835619 2066377 := bbase (se 2 (by rfl) ⟨774891, by rfl⟩ : syracuseStep 2066377 = 1549783) (by norm_num)
theorem B4130765 : Blo 1835619 4130765 := bbase (se 3 (by rfl) ⟨774518, by rfl⟩ : syracuseStep 4130765 = 1549037) (by norm_num)
theorem B2754509 : Blo 1835619 2754509 := bbase (se 3 (by rfl) ⟨516470, by rfl⟩ : syracuseStep 2754509 = 1032941) (by norm_num)
theorem B2754533 : Blo 1835619 2754533 := bbase (se 4 (by rfl) ⟨258237, by rfl⟩ : syracuseStep 2754533 = 516475) (by norm_num)
theorem B2066413 : Blo 1835619 2066413 := bbase (se 3 (by rfl) ⟨387452, by rfl⟩ : syracuseStep 2066413 = 774905) (by norm_num)
theorem B2754557 : Blo 1835619 2754557 := bbase (se 3 (by rfl) ⟨516479, by rfl⟩ : syracuseStep 2754557 = 1032959) (by norm_num)
theorem B3098621 : Blo 1835619 3098621 := bbase (se 3 (by rfl) ⟨580991, by rfl⟩ : syracuseStep 3098621 = 1161983) (by norm_num)
theorem B4646909 : Blo 1835619 4646909 := bbase (se 3 (by rfl) ⟨871295, by rfl⟩ : syracuseStep 4646909 = 1742591) (by norm_num)
theorem B2942981 : Blo 1835619 2942981 := bbase (se 4 (by rfl) ⟨275904, by rfl⟩ : syracuseStep 2942981 = 551809) (by norm_num)
theorem B2066449 : Blo 1835619 2066449 := bbase (se 2 (by rfl) ⟨774918, by rfl⟩ : syracuseStep 2066449 = 1549837) (by norm_num)
theorem B4130837 : Blo 1835619 4130837 := bbase (se 6 (by rfl) ⟨96816, by rfl⟩ : syracuseStep 4130837 = 193633) (by norm_num)
theorem B2754581 : Blo 1835619 2754581 := bbase (se 6 (by rfl) ⟨64560, by rfl⟩ : syracuseStep 2754581 = 129121) (by norm_num)
theorem B2615333 : Blo 1835619 2615333 := bbase (se 4 (by rfl) ⟨245187, by rfl⟩ : syracuseStep 2615333 = 490375) (by norm_num)
theorem B2754605 : Blo 1835619 2754605 := bbase (se 3 (by rfl) ⟨516488, by rfl⟩ : syracuseStep 2754605 = 1032977) (by norm_num)
theorem B2066485 : Blo 1835619 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B2754629 : Blo 1835619 2754629 := bbase (se 4 (by rfl) ⟨258246, by rfl⟩ : syracuseStep 2754629 = 516493) (by norm_num)
theorem B2066521 : Blo 1835619 2066521 := bbase (se 2 (by rfl) ⟨774945, by rfl⟩ : syracuseStep 2066521 = 1549891) (by norm_num)
theorem B4130909 : Blo 1835619 4130909 := bbase (se 3 (by rfl) ⟨774545, by rfl⟩ : syracuseStep 4130909 = 1549091) (by norm_num)
theorem B2754653 : Blo 1835619 2754653 := bbase (se 3 (by rfl) ⟨516497, by rfl⟩ : syracuseStep 2754653 = 1032995) (by norm_num)
theorem B2754677 : Blo 1835619 2754677 := bbase (se 5 (by rfl) ⟨129125, by rfl⟩ : syracuseStep 2754677 = 258251) (by norm_num)
theorem B3098749 : Blo 1835619 3098749 := bbase (se 3 (by rfl) ⟨581015, by rfl⟩ : syracuseStep 3098749 = 1162031) (by norm_num)
theorem B2066557 : Blo 1835619 2066557 := bbase (se 3 (by rfl) ⟨387479, by rfl⟩ : syracuseStep 2066557 = 774959) (by norm_num)
theorem B2754701 : Blo 1835619 2754701 := bbase (se 3 (by rfl) ⟨516506, by rfl⟩ : syracuseStep 2754701 = 1033013) (by norm_num)
theorem B2066593 : Blo 1835619 2066593 := bbase (se 2 (by rfl) ⟨774972, by rfl⟩ : syracuseStep 2066593 = 1549945) (by norm_num)
theorem B6195365 : Blo 1835619 6195365 := bbase (se 4 (by rfl) ⟨580815, by rfl⟩ : syracuseStep 6195365 = 1161631) (by norm_num)
theorem B4130981 : Blo 1835619 4130981 := bbase (se 4 (by rfl) ⟨387279, by rfl⟩ : syracuseStep 4130981 = 774559) (by norm_num)
theorem B2754725 : Blo 1835619 2754725 := bbase (se 4 (by rfl) ⟨258255, by rfl⟩ : syracuseStep 2754725 = 516511) (by norm_num)
theorem B10602677 : Blo 1835619 10602677 := bbase (se 5 (by rfl) ⟨497000, by rfl⟩ : syracuseStep 10602677 = 994001) (by norm_num)
theorem B2754749 : Blo 1835619 2754749 := bbase (se 3 (by rfl) ⟨516515, by rfl⟩ : syracuseStep 2754749 = 1033031) (by norm_num)
theorem B2066629 : Blo 1835619 2066629 := bbase (se 4 (by rfl) ⟨193746, by rfl⟩ : syracuseStep 2066629 = 387493) (by norm_num)
theorem B3098837 : Blo 1835619 3098837 := bbase (se 7 (by rfl) ⟨36314, by rfl⟩ : syracuseStep 3098837 = 72629) (by norm_num)
theorem B2754773 : Blo 1835619 2754773 := bbase (se 7 (by rfl) ⟨32282, by rfl⟩ : syracuseStep 2754773 = 64565) (by norm_num)
theorem B1886441 : Blo 1835619 1886441 := bbase (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) (by norm_num)
theorem B2066665 : Blo 1835619 2066665 := bbase (se 2 (by rfl) ⟨774999, by rfl⟩ : syracuseStep 2066665 = 1549999) (by norm_num)
theorem B4131053 : Blo 1835619 4131053 := bbase (se 3 (by rfl) ⟨774572, by rfl⟩ : syracuseStep 4131053 = 1549145) (by norm_num)
theorem B2754797 : Blo 1835619 2754797 := bbase (se 3 (by rfl) ⟨516524, by rfl⟩ : syracuseStep 2754797 = 1033049) (by norm_num)
theorem B2754821 : Blo 1835619 2754821 := bbase (se 4 (by rfl) ⟨258264, by rfl⟩ : syracuseStep 2754821 = 516529) (by norm_num)
theorem B2066701 : Blo 1835619 2066701 := bbase (se 3 (by rfl) ⟨387506, by rfl⟩ : syracuseStep 2066701 = 775013) (by norm_num)
theorem B2754845 : Blo 1835619 2754845 := bbase (se 3 (by rfl) ⟨516533, by rfl⟩ : syracuseStep 2754845 = 1033067) (by norm_num)
theorem B2066737 : Blo 1835619 2066737 := bbase (se 2 (by rfl) ⟨775026, by rfl⟩ : syracuseStep 2066737 = 1550053) (by norm_num)
theorem B4131125 : Blo 1835619 4131125 := bbase (se 5 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 4131125 = 387293) (by norm_num)
theorem B2754869 : Blo 1835619 2754869 := bbase (se 5 (by rfl) ⟨129134, by rfl⟩ : syracuseStep 2754869 = 258269) (by norm_num)
theorem B2754893 : Blo 1835619 2754893 := bbase (se 3 (by rfl) ⟨516542, by rfl⟩ : syracuseStep 2754893 = 1033085) (by norm_num)
theorem B4647253 : Blo 1835619 4647253 := bbase (se 10 (by rfl) ⟨6807, by rfl⟩ : syracuseStep 4647253 = 13615) (by norm_num)
theorem B3098965 : Blo 1835619 3098965 := bbase (se 10 (by rfl) ⟨4539, by rfl⟩ : syracuseStep 3098965 = 9079) (by norm_num)
theorem B2066773 : Blo 1835619 2066773 := bbase (se 10 (by rfl) ⟨3027, by rfl⟩ : syracuseStep 2066773 = 6055) (by norm_num)
theorem B7072085 : Blo 1835619 7072085 := bbase (se 10 (by rfl) ⟨10359, by rfl⟩ : syracuseStep 7072085 = 20719) (by norm_num)
theorem B2754917 : Blo 1835619 2754917 := bbase (se 4 (by rfl) ⟨258273, by rfl⟩ : syracuseStep 2754917 = 516547) (by norm_num)
theorem B2066809 : Blo 1835619 2066809 := bbase (se 2 (by rfl) ⟨775053, by rfl⟩ : syracuseStep 2066809 = 1550107) (by norm_num)
theorem B4131197 : Blo 1835619 4131197 := bbase (se 3 (by rfl) ⟨774599, by rfl⟩ : syracuseStep 4131197 = 1549199) (by norm_num)
theorem B2754941 : Blo 1835619 2754941 := bbase (se 3 (by rfl) ⟨516551, by rfl⟩ : syracuseStep 2754941 = 1033103) (by norm_num)
theorem B2754965 : Blo 1835619 2754965 := bbase (se 6 (by rfl) ⟨64569, by rfl⟩ : syracuseStep 2754965 = 129139) (by norm_num)
theorem B2066845 : Blo 1835619 2066845 := bbase (se 3 (by rfl) ⟨387533, by rfl⟩ : syracuseStep 2066845 = 775067) (by norm_num)
theorem B2206121 : Blo 1835619 2206121 := bbase (se 2 (by rfl) ⟨827295, by rfl⟩ : syracuseStep 2206121 = 1654591) (by norm_num)
theorem B3099053 : Blo 1835619 3099053 := bbase (se 3 (by rfl) ⟨581072, by rfl⟩ : syracuseStep 3099053 = 1162145) (by norm_num)
theorem B2754989 : Blo 1835619 2754989 := bbase (se 3 (by rfl) ⟨516560, by rfl⟩ : syracuseStep 2754989 = 1033121) (by norm_num)
theorem B5228981 : Blo 1835619 5228981 := bbase (se 5 (by rfl) ⟨245108, by rfl⟩ : syracuseStep 5228981 = 490217) (by norm_num)
theorem B2066881 : Blo 1835619 2066881 := bbase (se 2 (by rfl) ⟨775080, by rfl⟩ : syracuseStep 2066881 = 1550161) (by norm_num)
theorem B4647365 : Blo 1835619 4647365 := bbase (se 4 (by rfl) ⟨435690, by rfl⟩ : syracuseStep 4647365 = 871381) (by norm_num)
theorem B4131269 : Blo 1835619 4131269 := bbase (se 4 (by rfl) ⟨387306, by rfl⟩ : syracuseStep 4131269 = 774613) (by norm_num)
theorem B2755013 : Blo 1835619 2755013 := bbase (se 4 (by rfl) ⟨258282, by rfl⟩ : syracuseStep 2755013 = 516565) (by norm_num)
theorem B10463701 : Blo 1835619 10463701 := bbase (se 7 (by rfl) ⟨122621, by rfl⟩ : syracuseStep 10463701 = 245243) (by norm_num)
theorem B2755037 : Blo 1835619 2755037 := bbase (se 3 (by rfl) ⟨516569, by rfl⟩ : syracuseStep 2755037 = 1033139) (by norm_num)
theorem B2066917 : Blo 1835619 2066917 := bbase (se 4 (by rfl) ⟨193773, by rfl⟩ : syracuseStep 2066917 = 387547) (by norm_num)
theorem B2755061 : Blo 1835619 2755061 := bbase (se 5 (by rfl) ⟨129143, by rfl⟩ : syracuseStep 2755061 = 258287) (by norm_num)
theorem B2066953 : Blo 1835619 2066953 := bbase (se 2 (by rfl) ⟨775107, by rfl⟩ : syracuseStep 2066953 = 1550215) (by norm_num)
theorem B4131341 : Blo 1835619 4131341 := bbase (se 3 (by rfl) ⟨774626, by rfl⟩ : syracuseStep 4131341 = 1549253) (by norm_num)
theorem B2755085 : Blo 1835619 2755085 := bbase (se 3 (by rfl) ⟨516578, by rfl⟩ : syracuseStep 2755085 = 1033157) (by norm_num)
theorem B8825365 : Blo 1835619 8825365 := bbase (se 6 (by rfl) ⟨206844, by rfl⟩ : syracuseStep 8825365 = 413689) (by norm_num)
theorem B2755109 : Blo 1835619 2755109 := bbase (se 4 (by rfl) ⟨258291, by rfl⟩ : syracuseStep 2755109 = 516583) (by norm_num)
theorem B3099181 : Blo 1835619 3099181 := bbase (se 3 (by rfl) ⟨581096, by rfl⟩ : syracuseStep 3099181 = 1162193) (by norm_num)
theorem B2066989 : Blo 1835619 2066989 := bbase (se 3 (by rfl) ⟨387560, by rfl⟩ : syracuseStep 2066989 = 775121) (by norm_num)
theorem B2755133 : Blo 1835619 2755133 := bbase (se 3 (by rfl) ⟨516587, by rfl⟩ : syracuseStep 2755133 = 1033175) (by norm_num)
theorem B2067025 : Blo 1835619 2067025 := bbase (se 2 (by rfl) ⟨775134, by rfl⟩ : syracuseStep 2067025 = 1550269) (by norm_num)
theorem B6195797 : Blo 1835619 6195797 := bbase (se 8 (by rfl) ⟨36303, by rfl⟩ : syracuseStep 6195797 = 72607) (by norm_num)
theorem B4131413 : Blo 1835619 4131413 := bbase (se 8 (by rfl) ⟨24207, by rfl⟩ : syracuseStep 4131413 = 48415) (by norm_num)
theorem B2755157 : Blo 1835619 2755157 := bbase (se 8 (by rfl) ⟨16143, by rfl⟩ : syracuseStep 2755157 = 32287) (by norm_num)
theorem B9300581 : Blo 1835619 9300581 := bbase (se 4 (by rfl) ⟨871929, by rfl⟩ : syracuseStep 9300581 = 1743859) (by norm_num)
theorem B2755181 : Blo 1835619 2755181 := bbase (se 3 (by rfl) ⟨516596, by rfl⟩ : syracuseStep 2755181 = 1033193) (by norm_num)
theorem B2067061 : Blo 1835619 2067061 := bbase (se 5 (by rfl) ⟨96893, by rfl⟩ : syracuseStep 2067061 = 193787) (by norm_num)
theorem B4647557 : Blo 1835619 4647557 := bbase (se 4 (by rfl) ⟨435708, by rfl⟩ : syracuseStep 4647557 = 871417) (by norm_num)
theorem B3099269 : Blo 1835619 3099269 := bbase (se 4 (by rfl) ⟨290556, by rfl⟩ : syracuseStep 3099269 = 581113) (by norm_num)
theorem B2755205 : Blo 1835619 2755205 := bbase (se 4 (by rfl) ⟨258300, by rfl⟩ : syracuseStep 2755205 = 516601) (by norm_num)
theorem B2067097 : Blo 1835619 2067097 := bbase (se 2 (by rfl) ⟨775161, by rfl⟩ : syracuseStep 2067097 = 1550323) (by norm_num)
theorem B4131485 : Blo 1835619 4131485 := bbase (se 3 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 4131485 = 1549307) (by norm_num)
theorem B2755229 : Blo 1835619 2755229 := bbase (se 3 (by rfl) ⟨516605, by rfl⟩ : syracuseStep 2755229 = 1033211) (by norm_num)
theorem B2755253 : Blo 1835619 2755253 := bbase (se 5 (by rfl) ⟨129152, by rfl⟩ : syracuseStep 2755253 = 258305) (by norm_num)
theorem B2067133 : Blo 1835619 2067133 := bbase (se 3 (by rfl) ⟨387587, by rfl⟩ : syracuseStep 2067133 = 775175) (by norm_num)
theorem B2755277 : Blo 1835619 2755277 := bbase (se 3 (by rfl) ⟨516614, by rfl⟩ : syracuseStep 2755277 = 1033229) (by norm_num)
theorem B2067169 : Blo 1835619 2067169 := bbase (se 2 (by rfl) ⟨775188, by rfl⟩ : syracuseStep 2067169 = 1550377) (by norm_num)
theorem B4131557 : Blo 1835619 4131557 := bbase (se 4 (by rfl) ⟨387333, by rfl⟩ : syracuseStep 4131557 = 774667) (by norm_num)
theorem B2755301 : Blo 1835619 2755301 := bbase (se 4 (by rfl) ⟨258309, by rfl⟩ : syracuseStep 2755301 = 516619) (by norm_num)
theorem B2206453 : Blo 1835619 2206453 := bbase (se 5 (by rfl) ⟨103427, by rfl⟩ : syracuseStep 2206453 = 206855) (by norm_num)
theorem B5966581 : Blo 1835619 5966581 := bbase (se 5 (by rfl) ⟨279683, by rfl⟩ : syracuseStep 5966581 = 559367) (by norm_num)
theorem B1960697 : Blo 1835619 1960697 := bbase (se 2 (by rfl) ⟨735261, by rfl⟩ : syracuseStep 1960697 = 1470523) (by norm_num)
theorem B2755325 : Blo 1835619 2755325 := bbase (se 3 (by rfl) ⟨516623, by rfl⟩ : syracuseStep 2755325 = 1033247) (by norm_num)
theorem B3099397 : Blo 1835619 3099397 := bbase (se 4 (by rfl) ⟨290568, by rfl⟩ : syracuseStep 3099397 = 581137) (by norm_num)
theorem B2067205 : Blo 1835619 2067205 := bbase (se 4 (by rfl) ⟨193800, by rfl⟩ : syracuseStep 2067205 = 387601) (by norm_num)
theorem B2755349 : Blo 1835619 2755349 := bbase (se 6 (by rfl) ⟨64578, by rfl⟩ : syracuseStep 2755349 = 129157) (by norm_num)
theorem B2616085 : Blo 1835619 2616085 := bbase (se 6 (by rfl) ⟨61314, by rfl⟩ : syracuseStep 2616085 = 122629) (by norm_num)
theorem B2067241 : Blo 1835619 2067241 := bbase (se 2 (by rfl) ⟨775215, by rfl⟩ : syracuseStep 2067241 = 1550431) (by norm_num)
theorem B4131629 : Blo 1835619 4131629 := bbase (se 3 (by rfl) ⟨774680, by rfl⟩ : syracuseStep 4131629 = 1549361) (by norm_num)
theorem B2755373 : Blo 1835619 2755373 := bbase (se 3 (by rfl) ⟨516632, by rfl⟩ : syracuseStep 2755373 = 1033265) (by norm_num)
theorem B2755397 : Blo 1835619 2755397 := bbase (se 4 (by rfl) ⟨258318, by rfl⟩ : syracuseStep 2755397 = 516637) (by norm_num)
theorem B2067277 : Blo 1835619 2067277 := bbase (se 3 (by rfl) ⟨387614, by rfl⟩ : syracuseStep 2067277 = 775229) (by norm_num)
theorem B5884757 : Blo 1835619 5884757 := bbase (se 9 (by rfl) ⟨17240, by rfl⟩ : syracuseStep 5884757 = 34481) (by norm_num)
theorem B3099485 : Blo 1835619 3099485 := bbase (se 3 (by rfl) ⟨581153, by rfl⟩ : syracuseStep 3099485 = 1162307) (by norm_num)
theorem B2755421 : Blo 1835619 2755421 := bbase (se 3 (by rfl) ⟨516641, by rfl⟩ : syracuseStep 2755421 = 1033283) (by norm_num)
theorem B2067313 : Blo 1835619 2067313 := bbase (se 2 (by rfl) ⟨775242, by rfl⟩ : syracuseStep 2067313 = 1550485) (by norm_num)
theorem B4131701 : Blo 1835619 4131701 := bbase (se 5 (by rfl) ⟨193673, by rfl⟩ : syracuseStep 4131701 = 387347) (by norm_num)
theorem B2755445 : Blo 1835619 2755445 := bbase (se 5 (by rfl) ⟨129161, by rfl⟩ : syracuseStep 2755445 = 258323) (by norm_num)
theorem B2755469 : Blo 1835619 2755469 := bbase (se 3 (by rfl) ⟨516650, by rfl⟩ : syracuseStep 2755469 = 1033301) (by norm_num)
theorem B2755493 : Blo 1835619 2755493 := bbase (se 4 (by rfl) ⟨258327, by rfl⟩ : syracuseStep 2755493 = 516655) (by norm_num)
theorem B1960885 : Blo 1835619 1960885 := bbase (se 5 (by rfl) ⟨91916, by rfl⟩ : syracuseStep 1960885 = 183833) (by norm_num)
theorem B4131773 : Blo 1835619 4131773 := bbase (se 3 (by rfl) ⟨774707, by rfl⟩ : syracuseStep 4131773 = 1549415) (by norm_num)
theorem B2755517 : Blo 1835619 2755517 := bbase (se 3 (by rfl) ⟨516659, by rfl⟩ : syracuseStep 2755517 = 1033319) (by norm_num)
theorem B3533765 : Blo 1835619 3533765 := bbase (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) (by norm_num)
theorem B4189133 : Blo 1835619 4189133 := bbase (se 3 (by rfl) ⟨785462, by rfl⟩ : syracuseStep 4189133 = 1570925) (by norm_num)
theorem B68848597 : Blo 1835619 68848597 := bbase (se 7 (by rfl) ⟨806819, by rfl⟩ : syracuseStep 68848597 = 1613639) (by norm_num)
theorem B2755541 : Blo 1835619 2755541 := bbase (se 7 (by rfl) ⟨32291, by rfl⟩ : syracuseStep 2755541 = 64583) (by norm_num)
theorem B4647901 : Blo 1835619 4647901 := bbase (se 3 (by rfl) ⟨871481, by rfl⟩ : syracuseStep 4647901 = 1742963) (by norm_num)
theorem B3099613 : Blo 1835619 3099613 := bbase (se 3 (by rfl) ⟨581177, by rfl⟩ : syracuseStep 3099613 = 1162355) (by norm_num)
theorem B3722221 : Blo 1835619 3722221 := bbase (se 3 (by rfl) ⟨697916, by rfl⟩ : syracuseStep 3722221 = 1395833) (by norm_num)
theorem B2755565 : Blo 1835619 2755565 := bbase (se 3 (by rfl) ⟨516668, by rfl⟩ : syracuseStep 2755565 = 1033337) (by norm_num)
theorem B6196229 : Blo 1835619 6196229 := bbase (se 4 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 6196229 = 1161793) (by norm_num)
theorem B4131845 : Blo 1835619 4131845 := bbase (se 4 (by rfl) ⟨387360, by rfl⟩ : syracuseStep 4131845 = 774721) (by norm_num)
theorem B2755589 : Blo 1835619 2755589 := bbase (se 4 (by rfl) ⟨258336, by rfl⟩ : syracuseStep 2755589 = 516673) (by norm_num)
theorem B2755613 : Blo 1835619 2755613 := bbase (se 3 (by rfl) ⟨516677, by rfl⟩ : syracuseStep 2755613 = 1033355) (by norm_num)
theorem B3099701 : Blo 1835619 3099701 := bbase (se 5 (by rfl) ⟨145298, by rfl⟩ : syracuseStep 3099701 = 290597) (by norm_num)
theorem B2755637 : Blo 1835619 2755637 := bbase (se 5 (by rfl) ⟨129170, by rfl⟩ : syracuseStep 2755637 = 258341) (by norm_num)
theorem B4648013 : Blo 1835619 4648013 := bbase (se 3 (by rfl) ⟨871502, by rfl⟩ : syracuseStep 4648013 = 1743005) (by norm_num)
theorem B4131917 : Blo 1835619 4131917 := bbase (se 3 (by rfl) ⟨774734, by rfl⟩ : syracuseStep 4131917 = 1549469) (by norm_num)
theorem B2755661 : Blo 1835619 2755661 := bbase (se 3 (by rfl) ⟨516686, by rfl⟩ : syracuseStep 2755661 = 1033373) (by norm_num)
theorem B2755685 : Blo 1835619 2755685 := bbase (se 4 (by rfl) ⟨258345, by rfl⟩ : syracuseStep 2755685 = 516691) (by norm_num)
theorem B2755709 : Blo 1835619 2755709 := bbase (se 3 (by rfl) ⟨516695, by rfl⟩ : syracuseStep 2755709 = 1033391) (by norm_num)
theorem B4131989 : Blo 1835619 4131989 := bbase (se 6 (by rfl) ⟨96843, by rfl⟩ : syracuseStep 4131989 = 193687) (by norm_num)
theorem B2755733 : Blo 1835619 2755733 := bbase (se 6 (by rfl) ⟨64587, by rfl⟩ : syracuseStep 2755733 = 129175) (by norm_num)
theorem B6622357 : Blo 1835619 6622357 := bbase (se 6 (by rfl) ⟨155211, by rfl⟩ : syracuseStep 6622357 = 310423) (by norm_num)
theorem B2755757 : Blo 1835619 2755757 := bbase (se 3 (by rfl) ⟨516704, by rfl⟩ : syracuseStep 2755757 = 1033409) (by norm_num)
theorem B3099829 : Blo 1835619 3099829 := bbase (se 5 (by rfl) ⟨145304, by rfl⟩ : syracuseStep 3099829 = 290609) (by norm_num)
theorem B2755781 : Blo 1835619 2755781 := bbase (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) (by norm_num)
theorem B4132061 : Blo 1835619 4132061 := bbase (se 3 (by rfl) ⟨774761, by rfl⟩ : syracuseStep 4132061 = 1549523) (by norm_num)
theorem B2755805 : Blo 1835619 2755805 := bbase (se 3 (by rfl) ⟨516713, by rfl⟩ : syracuseStep 2755805 = 1033427) (by norm_num)
theorem B6974693 : Blo 1835619 6974693 := bbase (se 4 (by rfl) ⟨653877, by rfl⟩ : syracuseStep 6974693 = 1307755) (by norm_num)
theorem B7843061 : Blo 1835619 7843061 := bbase (se 5 (by rfl) ⟨367643, by rfl⟩ : syracuseStep 7843061 = 735287) (by norm_num)
theorem B2755829 : Blo 1835619 2755829 := bbase (se 5 (by rfl) ⟨129179, by rfl⟩ : syracuseStep 2755829 = 258359) (by norm_num)
theorem B4648205 : Blo 1835619 4648205 := bbase (se 3 (by rfl) ⟨871538, by rfl⟩ : syracuseStep 4648205 = 1743077) (by norm_num)
theorem B3099917 : Blo 1835619 3099917 := bbase (se 3 (by rfl) ⟨581234, by rfl⟩ : syracuseStep 3099917 = 1162469) (by norm_num)
theorem B2755853 : Blo 1835619 2755853 := bbase (se 3 (by rfl) ⟨516722, by rfl⟩ : syracuseStep 2755853 = 1033445) (by norm_num)
theorem B4132133 : Blo 1835619 4132133 := bbase (se 4 (by rfl) ⟨387387, by rfl⟩ : syracuseStep 4132133 = 774775) (by norm_num)
theorem B2755877 : Blo 1835619 2755877 := bbase (se 4 (by rfl) ⟨258363, by rfl⟩ : syracuseStep 2755877 = 516727) (by norm_num)
theorem B2755901 : Blo 1835619 2755901 := bbase (se 3 (by rfl) ⟨516731, by rfl⟩ : syracuseStep 2755901 = 1033463) (by norm_num)
theorem B2755925 : Blo 1835619 2755925 := bbase (se 11 (by rfl) ⟨2018, by rfl⟩ : syracuseStep 2755925 = 4037) (by norm_num)
theorem B4713821 : Blo 1835619 4713821 := bbase (se 3 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 4713821 = 1767683) (by norm_num)
theorem B4132205 : Blo 1835619 4132205 := bbase (se 3 (by rfl) ⟨774788, by rfl⟩ : syracuseStep 4132205 = 1549577) (by norm_num)
theorem B2755949 : Blo 1835619 2755949 := bbase (se 3 (by rfl) ⟨516740, by rfl⟩ : syracuseStep 2755949 = 1033481) (by norm_num)
theorem B3485045 : Blo 1835619 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B13241717 : Blo 1835619 13241717 := bbase (se 5 (by rfl) ⟨620705, by rfl⟩ : syracuseStep 13241717 = 1241411) (by norm_num)
theorem B2755973 : Blo 1835619 2755973 := bbase (se 4 (by rfl) ⟨258372, by rfl⟩ : syracuseStep 2755973 = 516745) (by norm_num)
theorem B3100045 : Blo 1835619 3100045 := bbase (se 3 (by rfl) ⟨581258, by rfl⟩ : syracuseStep 3100045 = 1162517) (by norm_num)
theorem B35794325 : Blo 1835619 35794325 := bbase (se 6 (by rfl) ⟨838929, by rfl⟩ : syracuseStep 35794325 = 1677859) (by norm_num)
theorem B2755997 : Blo 1835619 2755997 := bbase (se 3 (by rfl) ⟨516749, by rfl⟩ : syracuseStep 2755997 = 1033499) (by norm_num)
theorem B6196661 : Blo 1835619 6196661 := bbase (se 5 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 6196661 = 580937) (by norm_num)
theorem B4132277 : Blo 1835619 4132277 := bbase (se 5 (by rfl) ⟨193700, by rfl⟩ : syracuseStep 4132277 = 387401) (by norm_num)
theorem B2756021 : Blo 1835619 2756021 := bbase (se 5 (by rfl) ⟨129188, by rfl⟩ : syracuseStep 2756021 = 258377) (by norm_num)
theorem B2756045 : Blo 1835619 2756045 := bbase (se 3 (by rfl) ⟨516758, by rfl⟩ : syracuseStep 2756045 = 1033517) (by norm_num)
theorem B7843301 : Blo 1835619 7843301 := bbase (se 4 (by rfl) ⟨735309, by rfl⟩ : syracuseStep 7843301 = 1470619) (by norm_num)
theorem B3100133 : Blo 1835619 3100133 := bbase (se 4 (by rfl) ⟨290637, by rfl⟩ : syracuseStep 3100133 = 581275) (by norm_num)
theorem B2756069 : Blo 1835619 2756069 := bbase (se 4 (by rfl) ⟨258381, by rfl⟩ : syracuseStep 2756069 = 516763) (by norm_num)
theorem B4132349 : Blo 1835619 4132349 := bbase (se 3 (by rfl) ⟨774815, by rfl⟩ : syracuseStep 4132349 = 1549631) (by norm_num)
theorem B2756093 : Blo 1835619 2756093 := bbase (se 3 (by rfl) ⟨516767, by rfl⟩ : syracuseStep 2756093 = 1033535) (by norm_num)
theorem B6974981 : Blo 1835619 6974981 := bbase (se 4 (by rfl) ⟨653904, by rfl⟩ : syracuseStep 6974981 = 1307809) (by norm_num)
theorem B3485197 : Blo 1835619 3485197 := bbase (se 3 (by rfl) ⟨653474, by rfl⟩ : syracuseStep 3485197 = 1306949) (by norm_num)
theorem B2756117 : Blo 1835619 2756117 := bbase (se 6 (by rfl) ⟨64596, by rfl⟩ : syracuseStep 2756117 = 129193) (by norm_num)
theorem B2756141 : Blo 1835619 2756141 := bbase (se 3 (by rfl) ⟨516776, by rfl⟩ : syracuseStep 2756141 = 1033553) (by norm_num)
theorem B4132421 : Blo 1835619 4132421 := bbase (se 4 (by rfl) ⟨387414, by rfl⟩ : syracuseStep 4132421 = 774829) (by norm_num)
theorem B2756165 : Blo 1835619 2756165 := bbase (se 4 (by rfl) ⟨258390, by rfl⟩ : syracuseStep 2756165 = 516781) (by norm_num)
theorem B2649677 : Blo 1835619 2649677 := bbase (se 3 (by rfl) ⟨496814, by rfl⟩ : syracuseStep 2649677 = 993629) (by norm_num)
theorem B5230165 : Blo 1835619 5230165 := bbase (se 8 (by rfl) ⟨30645, by rfl⟩ : syracuseStep 5230165 = 61291) (by norm_num)
theorem B2756189 : Blo 1835619 2756189 := bbase (se 3 (by rfl) ⟨516785, by rfl⟩ : syracuseStep 2756189 = 1033571) (by norm_num)
theorem B4648549 : Blo 1835619 4648549 := bbase (se 4 (by rfl) ⟨435801, by rfl⟩ : syracuseStep 4648549 = 871603) (by norm_num)
theorem B3100261 : Blo 1835619 3100261 := bbase (se 4 (by rfl) ⟨290649, by rfl⟩ : syracuseStep 3100261 = 581299) (by norm_num)
theorem B2207341 : Blo 1835619 2207341 := bbase (se 3 (by rfl) ⟨413876, by rfl⟩ : syracuseStep 2207341 = 827753) (by norm_num)
theorem B2756213 : Blo 1835619 2756213 := bbase (se 5 (by rfl) ⟨129197, by rfl⟩ : syracuseStep 2756213 = 258395) (by norm_num)
theorem B4132493 : Blo 1835619 4132493 := bbase (se 3 (by rfl) ⟨774842, by rfl⟩ : syracuseStep 4132493 = 1549685) (by norm_num)
theorem B2756237 : Blo 1835619 2756237 := bbase (se 3 (by rfl) ⟨516794, by rfl⟩ : syracuseStep 2756237 = 1033589) (by norm_num)
theorem B2756261 : Blo 1835619 2756261 := bbase (se 4 (by rfl) ⟨258399, by rfl⟩ : syracuseStep 2756261 = 516799) (by norm_num)
theorem B4411061 : Blo 1835619 4411061 := bbase (se 5 (by rfl) ⟨206768, by rfl⟩ : syracuseStep 4411061 = 413537) (by norm_num)
theorem B8171189 : Blo 1835619 8171189 := bbase (se 5 (by rfl) ⟨383024, by rfl⟩ : syracuseStep 8171189 = 766049) (by norm_num)
theorem B3100349 : Blo 1835619 3100349 := bbase (se 3 (by rfl) ⟨581315, by rfl⟩ : syracuseStep 3100349 = 1162631) (by norm_num)
theorem B2756285 : Blo 1835619 2756285 := bbase (se 3 (by rfl) ⟨516803, by rfl⟩ : syracuseStep 2756285 = 1033607) (by norm_num)
theorem B7065301 : Blo 1835619 7065301 := bbase (se 7 (by rfl) ⟨82796, by rfl⟩ : syracuseStep 7065301 = 165593) (by norm_num)
theorem B4648661 : Blo 1835619 4648661 := bbase (se 7 (by rfl) ⟨54476, by rfl⟩ : syracuseStep 4648661 = 108953) (by norm_num)
theorem B4132565 : Blo 1835619 4132565 := bbase (se 7 (by rfl) ⟨48428, by rfl⟩ : syracuseStep 4132565 = 96857) (by norm_num)
theorem B2756309 : Blo 1835619 2756309 := bbase (se 7 (by rfl) ⟨32300, by rfl⟩ : syracuseStep 2756309 = 64601) (by norm_num)
theorem B1961705 : Blo 1835619 1961705 := bbase (se 2 (by rfl) ⟨735639, by rfl⟩ : syracuseStep 1961705 = 1471279) (by norm_num)
theorem B2756333 : Blo 1835619 2756333 := bbase (se 3 (by rfl) ⟨516812, by rfl⟩ : syracuseStep 2756333 = 1033625) (by norm_num)
theorem B5230325 : Blo 1835619 5230325 := bbase (se 5 (by rfl) ⟨245171, by rfl⟩ : syracuseStep 5230325 = 490343) (by norm_num)
theorem B2756357 : Blo 1835619 2756357 := bbase (se 4 (by rfl) ⟨258408, by rfl⟩ : syracuseStep 2756357 = 516817) (by norm_num)
theorem B4132637 : Blo 1835619 4132637 := bbase (se 3 (by rfl) ⟨774869, by rfl⟩ : syracuseStep 4132637 = 1549739) (by norm_num)
theorem B4189981 : Blo 1835619 4189981 := bbase (se 3 (by rfl) ⟨785621, by rfl⟩ : syracuseStep 4189981 = 1571243) (by norm_num)
theorem B2756381 : Blo 1835619 2756381 := bbase (se 3 (by rfl) ⟨516821, by rfl⟩ : syracuseStep 2756381 = 1033643) (by norm_num)
theorem B3141413 : Blo 1835619 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B2756405 : Blo 1835619 2756405 := bbase (se 5 (by rfl) ⟨129206, by rfl⟩ : syracuseStep 2756405 = 258413) (by norm_num)
theorem B3485501 : Blo 1835619 3485501 := bbase (se 3 (by rfl) ⟨653531, by rfl⟩ : syracuseStep 3485501 = 1307063) (by norm_num)
theorem B3100477 : Blo 1835619 3100477 := bbase (se 3 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 3100477 = 1162679) (by norm_num)
theorem B2756429 : Blo 1835619 2756429 := bbase (se 3 (by rfl) ⟨516830, by rfl⟩ : syracuseStep 2756429 = 1033661) (by norm_num)
theorem B107343701 : Blo 1835619 107343701 := bbase (se 9 (by rfl) ⟨314483, by rfl⟩ : syracuseStep 107343701 = 628967) (by norm_num)
theorem B6197093 : Blo 1835619 6197093 := bbase (se 4 (by rfl) ⟨580977, by rfl⟩ : syracuseStep 6197093 = 1161955) (by norm_num)
theorem B4132709 : Blo 1835619 4132709 := bbase (se 4 (by rfl) ⟨387441, by rfl⟩ : syracuseStep 4132709 = 774883) (by norm_num)
theorem B13946741 : Blo 1835619 13946741 := bbase (se 5 (by rfl) ⟨653753, by rfl⟩ : syracuseStep 13946741 = 1307507) (by norm_num)
theorem B9301877 : Blo 1835619 9301877 := bbase (se 5 (by rfl) ⟨436025, by rfl⟩ : syracuseStep 9301877 = 872051) (by norm_num)
theorem B4648853 : Blo 1835619 4648853 := bbase (se 6 (by rfl) ⟨108957, by rfl⟩ : syracuseStep 4648853 = 217915) (by norm_num)
theorem B3100565 : Blo 1835619 3100565 := bbase (se 6 (by rfl) ⟨72669, by rfl⟩ : syracuseStep 3100565 = 145339) (by norm_num)
theorem B4132781 : Blo 1835619 4132781 := bbase (se 3 (by rfl) ⟨774896, by rfl⟩ : syracuseStep 4132781 = 1549793) (by norm_num)
theorem B5230565 : Blo 1835619 5230565 := bbase (se 4 (by rfl) ⟨490365, by rfl⟩ : syracuseStep 5230565 = 980731) (by norm_num)
theorem B4132853 : Blo 1835619 4132853 := bbase (se 5 (by rfl) ⟨193727, by rfl⟩ : syracuseStep 4132853 = 387455) (by norm_num)
theorem B3100693 : Blo 1835619 3100693 := bbase (se 6 (by rfl) ⟨72672, by rfl⟩ : syracuseStep 3100693 = 145345) (by norm_num)
theorem B4132925 : Blo 1835619 4132925 := bbase (se 3 (by rfl) ⟨774923, by rfl⟩ : syracuseStep 4132925 = 1549847) (by norm_num)
theorem B5886037 : Blo 1835619 5886037 := bbase (se 8 (by rfl) ⟨34488, by rfl⟩ : syracuseStep 5886037 = 68977) (by norm_num)
theorem B3100781 : Blo 1835619 3100781 := bbase (se 3 (by rfl) ⟨581396, by rfl⟩ : syracuseStep 3100781 = 1162793) (by norm_num)
theorem B4132997 : Blo 1835619 4132997 := bbase (se 4 (by rfl) ⟨387468, by rfl⟩ : syracuseStep 4132997 = 774937) (by norm_num)
theorem B3723413 : Blo 1835619 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B5230757 : Blo 1835619 5230757 := bbase (se 4 (by rfl) ⟨490383, by rfl⟩ : syracuseStep 5230757 = 980767) (by norm_num)
theorem B1962149 : Blo 1835619 1962149 := bbase (se 4 (by rfl) ⟨183951, by rfl⟩ : syracuseStep 1962149 = 367903) (by norm_num)
theorem B13234357 : Blo 1835619 13234357 := bbase (se 5 (by rfl) ⟨620360, by rfl⟩ : syracuseStep 13234357 = 1240721) (by norm_num)
theorem B3723461 : Blo 1835619 3723461 := bbase (se 4 (by rfl) ⟨349074, by rfl⟩ : syracuseStep 3723461 = 698149) (by norm_num)
theorem B4133069 : Blo 1835619 4133069 := bbase (se 3 (by rfl) ⟨774950, by rfl⟩ : syracuseStep 4133069 = 1549901) (by norm_num)
theorem B4649197 : Blo 1835619 4649197 := bbase (se 3 (by rfl) ⟨871724, by rfl⟩ : syracuseStep 4649197 = 1743449) (by norm_num)
theorem B3100909 : Blo 1835619 3100909 := bbase (se 3 (by rfl) ⟨581420, by rfl⟩ : syracuseStep 3100909 = 1162841) (by norm_num)
theorem B2355473 : Blo 1835619 2355473 := bbase (se 2 (by rfl) ⟨883302, by rfl⟩ : syracuseStep 2355473 = 1766605) (by norm_num)
theorem B9294101 : Blo 1835619 9294101 := bbase (se 6 (by rfl) ⟨217830, by rfl⟩ : syracuseStep 9294101 = 435661) (by norm_num)
theorem B6197525 : Blo 1835619 6197525 := bbase (se 6 (by rfl) ⟨145254, by rfl⟩ : syracuseStep 6197525 = 290509) (by norm_num)
theorem B4133141 : Blo 1835619 4133141 := bbase (se 6 (by rfl) ⟨96870, by rfl⟩ : syracuseStep 4133141 = 193741) (by norm_num)
theorem B4649309 : Blo 1835619 4649309 := bbase (se 3 (by rfl) ⟨871745, by rfl⟩ : syracuseStep 4649309 = 1743491) (by norm_num)
theorem B4133213 : Blo 1835619 4133213 := bbase (se 3 (by rfl) ⟨774977, by rfl⟩ : syracuseStep 4133213 = 1549955) (by norm_num)
theorem B10465685 : Blo 1835619 10465685 := bbase (se 6 (by rfl) ⟨245289, by rfl⟩ : syracuseStep 10465685 = 490579) (by norm_num)
theorem B4133285 : Blo 1835619 4133285 := bbase (se 4 (by rfl) ⟨387495, by rfl⟩ : syracuseStep 4133285 = 774991) (by norm_num)
theorem B4411829 : Blo 1835619 4411829 := bbase (se 5 (by rfl) ⟨206804, by rfl⟩ : syracuseStep 4411829 = 413609) (by norm_num)
theorem B4411837 : Blo 1835619 4411837 := bbase (se 3 (by rfl) ⟨827219, by rfl⟩ : syracuseStep 4411837 = 1654439) (by norm_num)
theorem B7442885 : Blo 1835619 7442885 := bbase (se 4 (by rfl) ⟨697770, by rfl⟩ : syracuseStep 7442885 = 1395541) (by norm_num)
theorem B4133357 : Blo 1835619 4133357 := bbase (se 3 (by rfl) ⟨775004, by rfl⟩ : syracuseStep 4133357 = 1550009) (by norm_num)
theorem B4534805 : Blo 1835619 4534805 := bbase (se 6 (by rfl) ⟨106284, by rfl⟩ : syracuseStep 4534805 = 212569) (by norm_num)
theorem B3142165 : Blo 1835619 3142165 := bbase (se 6 (by rfl) ⟨73644, by rfl⟩ : syracuseStep 3142165 = 147289) (by norm_num)
theorem B4649501 : Blo 1835619 4649501 := bbase (se 3 (by rfl) ⟨871781, by rfl⟩ : syracuseStep 4649501 = 1743563) (by norm_num)
theorem B3486253 : Blo 1835619 3486253 := bbase (se 3 (by rfl) ⟨653672, by rfl⟩ : syracuseStep 3486253 = 1307345) (by norm_num)
theorem B3920437 : Blo 1835619 3920437 := bbase (se 5 (by rfl) ⟨183770, by rfl⟩ : syracuseStep 3920437 = 367541) (by norm_num)
theorem B4133429 : Blo 1835619 4133429 := bbase (se 5 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 4133429 = 387509) (by norm_num)
theorem B3723869 : Blo 1835619 3723869 := bbase (se 3 (by rfl) ⟨698225, by rfl⟩ : syracuseStep 3723869 = 1396451) (by norm_num)
theorem B4133501 : Blo 1835619 4133501 := bbase (se 3 (by rfl) ⟨775031, by rfl⟩ : syracuseStep 4133501 = 1550063) (by norm_num)
theorem B6976165 : Blo 1835619 6976165 := bbase (se 4 (by rfl) ⟨654015, by rfl⟩ : syracuseStep 6976165 = 1308031) (by norm_num)
theorem B3920557 : Blo 1835619 3920557 := bbase (se 3 (by rfl) ⟨735104, by rfl⟩ : syracuseStep 3920557 = 1470209) (by norm_num)
theorem B3486397 : Blo 1835619 3486397 := bbase (se 3 (by rfl) ⟨653699, by rfl⟩ : syracuseStep 3486397 = 1307399) (by norm_num)
theorem B6197957 : Blo 1835619 6197957 := bbase (se 4 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 6197957 = 1162117) (by norm_num)
theorem B4133573 : Blo 1835619 4133573 := bbase (se 4 (by rfl) ⟨387522, by rfl⟩ : syracuseStep 4133573 = 775045) (by norm_num)
theorem B2355925 : Blo 1835619 2355925 := bbase (se 7 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 2355925 = 55217) (by norm_num)
theorem B4133645 : Blo 1835619 4133645 := bbase (se 3 (by rfl) ⟨775058, by rfl⟩ : syracuseStep 4133645 = 1550117) (by norm_num)
theorem B2323237 : Blo 1835619 2323237 := bbase (se 4 (by rfl) ⟨217803, by rfl⟩ : syracuseStep 2323237 = 435607) (by norm_num)
theorem B4133717 : Blo 1835619 4133717 := bbase (se 9 (by rfl) ⟨12110, by rfl⟩ : syracuseStep 4133717 = 24221) (by norm_num)
theorem B3486557 : Blo 1835619 3486557 := bbase (se 3 (by rfl) ⟨653729, by rfl⟩ : syracuseStep 3486557 = 1307459) (by norm_num)
theorem B3978085 : Blo 1835619 3978085 := bbase (se 4 (by rfl) ⟨372945, by rfl⟩ : syracuseStep 3978085 = 745891) (by norm_num)
theorem B4649845 : Blo 1835619 4649845 := bbase (se 5 (by rfl) ⟨217961, by rfl⟩ : syracuseStep 4649845 = 435923) (by norm_num)
theorem B2323333 : Blo 1835619 2323333 := bbase (se 4 (by rfl) ⟨217812, by rfl⟩ : syracuseStep 2323333 = 435625) (by norm_num)
theorem B4133789 : Blo 1835619 4133789 := bbase (se 3 (by rfl) ⟨775085, by rfl⟩ : syracuseStep 4133789 = 1550171) (by norm_num)
theorem B3920813 : Blo 1835619 3920813 := bbase (se 3 (by rfl) ⟨735152, by rfl⟩ : syracuseStep 3920813 = 1470305) (by norm_num)
theorem B13595573 : Blo 1835619 13595573 := bbase (se 5 (by rfl) ⟨637292, by rfl⟩ : syracuseStep 13595573 = 1274585) (by norm_num)
theorem B6976469 : Blo 1835619 6976469 := bbase (se 7 (by rfl) ⟨81755, by rfl⟩ : syracuseStep 6976469 = 163511) (by norm_num)
theorem B4649957 : Blo 1835619 4649957 := bbase (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) (by norm_num)
theorem B4133861 : Blo 1835619 4133861 := bbase (se 4 (by rfl) ⟨387549, by rfl⟩ : syracuseStep 4133861 = 775099) (by norm_num)
theorem B3486701 : Blo 1835619 3486701 := bbase (se 3 (by rfl) ⟨653756, by rfl⟩ : syracuseStep 3486701 = 1307513) (by norm_num)
theorem B3142685 : Blo 1835619 3142685 := bbase (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) (by norm_num)
theorem B4133933 : Blo 1835619 4133933 := bbase (se 3 (by rfl) ⟨775112, by rfl⟩ : syracuseStep 4133933 = 1550225) (by norm_num)
theorem B2323505 : Blo 1835619 2323505 := bbase (se 2 (by rfl) ⟨871314, by rfl⟩ : syracuseStep 2323505 = 1742629) (by norm_num)
theorem B9925685 : Blo 1835619 9925685 := bbase (se 5 (by rfl) ⟨465266, by rfl⟩ : syracuseStep 9925685 = 930533) (by norm_num)
theorem B2323561 : Blo 1835619 2323561 := bbase (se 2 (by rfl) ⟨871335, by rfl⟩ : syracuseStep 2323561 = 1742671) (by norm_num)
theorem B6198389 : Blo 1835619 6198389 := bbase (se 5 (by rfl) ⟨290549, by rfl⟩ : syracuseStep 6198389 = 581099) (by norm_num)
theorem B4134005 : Blo 1835619 4134005 := bbase (se 5 (by rfl) ⟨193781, by rfl⟩ : syracuseStep 4134005 = 387563) (by norm_num)
theorem B5231749 : Blo 1835619 5231749 := bbase (se 4 (by rfl) ⟨490476, by rfl⟩ : syracuseStep 5231749 = 980953) (by norm_num)
theorem B4650149 : Blo 1835619 4650149 := bbase (se 4 (by rfl) ⟨435951, by rfl⟩ : syracuseStep 4650149 = 871903) (by norm_num)
theorem B2094265 : Blo 1835619 2094265 := bbase (se 2 (by rfl) ⟨785349, by rfl⟩ : syracuseStep 2094265 = 1570699) (by norm_num)
theorem B4134077 : Blo 1835619 4134077 := bbase (se 3 (by rfl) ⟨775139, by rfl⟩ : syracuseStep 4134077 = 1550279) (by norm_num)
theorem B2323657 : Blo 1835619 2323657 := bbase (se 2 (by rfl) ⟨871371, by rfl⟩ : syracuseStep 2323657 = 1742743) (by norm_num)
theorem B4412645 : Blo 1835619 4412645 := bbase (se 4 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 4412645 = 827371) (by norm_num)
theorem B4134149 : Blo 1835619 4134149 := bbase (se 4 (by rfl) ⟨387576, by rfl⟩ : syracuseStep 4134149 = 775153) (by norm_num)
theorem B3486989 : Blo 1835619 3486989 := bbase (se 3 (by rfl) ⟨653810, by rfl⟩ : syracuseStep 3486989 = 1307621) (by norm_num)
theorem B4134221 : Blo 1835619 4134221 := bbase (se 3 (by rfl) ⟨775166, by rfl⟩ : syracuseStep 4134221 = 1550333) (by norm_num)
theorem B2323829 : Blo 1835619 2323829 := bbase (se 5 (by rfl) ⟨108929, by rfl⟩ : syracuseStep 2323829 = 217859) (by norm_num)
theorem B4134293 : Blo 1835619 4134293 := bbase (se 6 (by rfl) ⟨96897, by rfl⟩ : syracuseStep 4134293 = 193795) (by norm_num)
theorem B3487141 : Blo 1835619 3487141 := bbase (se 4 (by rfl) ⟨326919, by rfl⟩ : syracuseStep 3487141 = 653839) (by norm_num)
theorem B2323885 : Blo 1835619 2323885 := bbase (se 3 (by rfl) ⟨435728, by rfl⟩ : syracuseStep 2323885 = 871457) (by norm_num)
theorem B4134365 : Blo 1835619 4134365 := bbase (se 3 (by rfl) ⟨775193, by rfl⟩ : syracuseStep 4134365 = 1550387) (by norm_num)
theorem B10597877 : Blo 1835619 10597877 := bbase (se 5 (by rfl) ⟨496775, by rfl⟩ : syracuseStep 10597877 = 993551) (by norm_num)
theorem B4650493 : Blo 1835619 4650493 := bbase (se 3 (by rfl) ⟨871967, by rfl⟩ : syracuseStep 4650493 = 1743935) (by norm_num)
theorem B2356745 : Blo 1835619 2356745 := bbase (se 2 (by rfl) ⟨883779, by rfl⟩ : syracuseStep 2356745 = 1767559) (by norm_num)
theorem B2323981 : Blo 1835619 2323981 := bbase (se 3 (by rfl) ⟨435746, by rfl⟩ : syracuseStep 2323981 = 871493) (by norm_num)
theorem B2389537 : Blo 1835619 2389537 := bbase (se 2 (by rfl) ⟨896076, by rfl⟩ : syracuseStep 2389537 = 1792153) (by norm_num)
theorem B9295397 : Blo 1835619 9295397 := bbase (se 4 (by rfl) ⟨871443, by rfl⟩ : syracuseStep 9295397 = 1742887) (by norm_num)
theorem B6198821 : Blo 1835619 6198821 := bbase (se 4 (by rfl) ⟨581139, by rfl⟩ : syracuseStep 6198821 = 1162279) (by norm_num)
theorem B4134437 : Blo 1835619 4134437 := bbase (se 4 (by rfl) ⟨387603, by rfl⟩ : syracuseStep 4134437 = 775207) (by norm_num)
theorem B15693365 : Blo 1835619 15693365 := bbase (se 5 (by rfl) ⟨735626, by rfl⟩ : syracuseStep 15693365 = 1471253) (by norm_num)
theorem B4650605 : Blo 1835619 4650605 := bbase (se 3 (by rfl) ⟨871988, by rfl⟩ : syracuseStep 4650605 = 1743977) (by norm_num)
theorem B4134509 : Blo 1835619 4134509 := bbase (se 3 (by rfl) ⟨775220, by rfl⟩ : syracuseStep 4134509 = 1550441) (by norm_num)
theorem B3446405 : Blo 1835619 3446405 := bbase (se 4 (by rfl) ⟨323100, by rfl⟩ : syracuseStep 3446405 = 646201) (by norm_num)
theorem B18855605 : Blo 1835619 18855605 := bbase (se 5 (by rfl) ⟨883856, by rfl⟩ : syracuseStep 18855605 = 1767713) (by norm_num)
theorem B4134581 : Blo 1835619 4134581 := bbase (se 5 (by rfl) ⟨193808, by rfl⟩ : syracuseStep 4134581 = 387617) (by norm_num)
theorem B2324153 : Blo 1835619 2324153 := bbase (se 2 (by rfl) ⟨871557, by rfl⟩ : syracuseStep 2324153 = 1743115) (by norm_num)
theorem B2832077 : Blo 1835619 2832077 := bbase (se 3 (by rfl) ⟨531014, by rfl⟩ : syracuseStep 2832077 = 1062029) (by norm_num)
theorem B7845589 : Blo 1835619 7845589 := bbase (se 7 (by rfl) ⟨91940, by rfl⟩ : syracuseStep 7845589 = 183881) (by norm_num)
theorem B3487445 : Blo 1835619 3487445 := bbase (se 7 (by rfl) ⟨40868, by rfl⟩ : syracuseStep 3487445 = 81737) (by norm_num)
theorem B2324209 : Blo 1835619 2324209 := bbase (se 2 (by rfl) ⟨871578, by rfl⟩ : syracuseStep 2324209 = 1743157) (by norm_num)
theorem B3921701 : Blo 1835619 3921701 := bbase (se 4 (by rfl) ⟨367659, by rfl⟩ : syracuseStep 3921701 = 735319) (by norm_num)
theorem B4650797 : Blo 1835619 4650797 := bbase (se 3 (by rfl) ⟨872024, by rfl⟩ : syracuseStep 4650797 = 1744049) (by norm_num)
theorem B2324305 : Blo 1835619 2324305 := bbase (se 2 (by rfl) ⟨871614, by rfl⟩ : syracuseStep 2324305 = 1743229) (by norm_num)
theorem B17643349 : Blo 1835619 17643349 := bbase (se 9 (by rfl) ⟨51689, by rfl⟩ : syracuseStep 17643349 = 103379) (by norm_num)
theorem B2791277 : Blo 1835619 2791277 := bbase (se 3 (by rfl) ⟨523364, by rfl⟩ : syracuseStep 2791277 = 1046729) (by norm_num)
theorem B6199253 : Blo 1835619 6199253 := bbase (se 7 (by rfl) ⟨72647, by rfl⟩ : syracuseStep 6199253 = 145295) (by norm_num)
theorem B2324477 : Blo 1835619 2324477 := bbase (se 3 (by rfl) ⟨435839, by rfl⟩ : syracuseStep 2324477 = 871679) (by norm_num)
theorem B3921941 : Blo 1835619 3921941 := bbase (se 6 (by rfl) ⟨91920, by rfl⟩ : syracuseStep 3921941 = 183841) (by norm_num)
theorem B2324533 : Blo 1835619 2324533 := bbase (se 5 (by rfl) ⟨108962, by rfl⟩ : syracuseStep 2324533 = 217925) (by norm_num)
theorem B17659957 : Blo 1835619 17659957 := bbase (se 5 (by rfl) ⟨827810, by rfl⟩ : syracuseStep 17659957 = 1655621) (by norm_num)
theorem B8943733 : Blo 1835619 8943733 := bbase (se 5 (by rfl) ⟨419237, by rfl⟩ : syracuseStep 8943733 = 838475) (by norm_num)
theorem B4651141 : Blo 1835619 4651141 := bbase (se 4 (by rfl) ⟨436044, by rfl⟩ : syracuseStep 4651141 = 872089) (by norm_num)
theorem B2324629 : Blo 1835619 2324629 := bbase (se 6 (by rfl) ⟨54483, by rfl⟩ : syracuseStep 2324629 = 108967) (by norm_num)
theorem B3184805 : Blo 1835619 3184805 := bbase (se 4 (by rfl) ⟨298575, by rfl⟩ : syracuseStep 3184805 = 597151) (by norm_num)
theorem B5232853 : Blo 1835619 5232853 := bbase (se 7 (by rfl) ⟨61322, by rfl⟩ : syracuseStep 5232853 = 122645) (by norm_num)
theorem B4651253 : Blo 1835619 4651253 := bbase (se 5 (by rfl) ⟨218027, by rfl⟩ : syracuseStep 4651253 = 436055) (by norm_num)
theorem B6281509 : Blo 1835619 6281509 := bbase (se 4 (by rfl) ⟨588891, by rfl⟩ : syracuseStep 6281509 = 1177783) (by norm_num)
theorem B2324801 : Blo 1835619 2324801 := bbase (se 2 (by rfl) ⟨871800, by rfl⟩ : syracuseStep 2324801 = 1743601) (by norm_num)
theorem B2324857 : Blo 1835619 2324857 := bbase (se 2 (by rfl) ⟨871821, by rfl⟩ : syracuseStep 2324857 = 1743643) (by norm_num)
theorem B6199685 : Blo 1835619 6199685 := bbase (se 4 (by rfl) ⟨581220, by rfl⟩ : syracuseStep 6199685 = 1162441) (by norm_num)
theorem B4651445 : Blo 1835619 4651445 := bbase (se 5 (by rfl) ⟨218036, by rfl⟩ : syracuseStep 4651445 = 436073) (by norm_num)
theorem B3488197 : Blo 1835619 3488197 := bbase (se 4 (by rfl) ⟨327018, by rfl⟩ : syracuseStep 3488197 = 654037) (by norm_num)
theorem B2324953 : Blo 1835619 2324953 := bbase (se 2 (by rfl) ⟨871857, by rfl⟩ : syracuseStep 2324953 = 1743715) (by norm_num)
theorem B3922445 : Blo 1835619 3922445 := bbase (se 3 (by rfl) ⟨735458, by rfl⟩ : syracuseStep 3922445 = 1470917) (by norm_num)
theorem B3922453 : Blo 1835619 3922453 := bbase (se 6 (by rfl) ⟨91932, by rfl⟩ : syracuseStep 3922453 = 183865) (by norm_num)
theorem B3488341 : Blo 1835619 3488341 := bbase (se 8 (by rfl) ⟨20439, by rfl⟩ : syracuseStep 3488341 = 40879) (by norm_num)
theorem B8829557 : Blo 1835619 8829557 := bbase (se 5 (by rfl) ⟨413885, by rfl⟩ : syracuseStep 8829557 = 827771) (by norm_num)
theorem B2325125 : Blo 1835619 2325125 := bbase (se 4 (by rfl) ⟨217980, by rfl⟩ : syracuseStep 2325125 = 435961) (by norm_num)
theorem B2325181 : Blo 1835619 2325181 := bbase (se 3 (by rfl) ⟨435971, by rfl⟩ : syracuseStep 2325181 = 871943) (by norm_num)
theorem B5167813 : Blo 1835619 5167813 := bbase (se 4 (by rfl) ⟨484482, by rfl⟩ : syracuseStep 5167813 = 968965) (by norm_num)
theorem B3488501 : Blo 1835619 3488501 := bbase (se 5 (by rfl) ⟨163523, by rfl⟩ : syracuseStep 3488501 = 327047) (by norm_num)
theorem B2325277 : Blo 1835619 2325277 := bbase (se 3 (by rfl) ⟨435989, by rfl⟩ : syracuseStep 2325277 = 871979) (by norm_num)
theorem B9296693 : Blo 1835619 9296693 := bbase (se 5 (by rfl) ⟨435782, by rfl⟩ : syracuseStep 9296693 = 871565) (by norm_num)
theorem B6200117 : Blo 1835619 6200117 := bbase (se 5 (by rfl) ⟨290630, by rfl⟩ : syracuseStep 6200117 = 581261) (by norm_num)
theorem B2325449 : Blo 1835619 2325449 := bbase (se 2 (by rfl) ⟨872043, by rfl⟩ : syracuseStep 2325449 = 1744087) (by norm_num)
theorem B2325505 : Blo 1835619 2325505 := bbase (se 2 (by rfl) ⟨872064, by rfl⟩ : syracuseStep 2325505 = 1744129) (by norm_num)
theorem B2325601 : Blo 1835619 2325601 := bbase (se 2 (by rfl) ⟨872100, by rfl⟩ : syracuseStep 2325601 = 1744201) (by norm_num)
theorem B2014345 : Blo 1835619 2014345 := bbase (se 2 (by rfl) ⟨755379, by rfl⟩ : syracuseStep 2014345 = 1510759) (by norm_num)
theorem B7847077 : Blo 1835619 7847077 := bbase (se 4 (by rfl) ⟨735663, by rfl⟩ : syracuseStep 7847077 = 1471327) (by norm_num)
theorem B7847093 : Blo 1835619 7847093 := bbase (se 5 (by rfl) ⟨367832, by rfl⟩ : syracuseStep 7847093 = 735665) (by norm_num)
theorem B2792645 : Blo 1835619 2792645 := bbase (se 4 (by rfl) ⟨261810, by rfl⟩ : syracuseStep 2792645 = 523621) (by norm_num)
theorem B6200549 : Blo 1835619 6200549 := bbase (se 4 (by rfl) ⟨581301, by rfl⟩ : syracuseStep 6200549 = 1162603) (by norm_num)
theorem B6970805 : Blo 1835619 6970805 := bbase (se 5 (by rfl) ⟨326756, by rfl⟩ : syracuseStep 6970805 = 653513) (by norm_num)
theorem B9420293 : Blo 1835619 9420293 := bbase (se 4 (by rfl) ⟨883152, by rfl⟩ : syracuseStep 9420293 = 1766305) (by norm_num)
theorem B5881349 : Blo 1835619 5881349 := bbase (se 4 (by rfl) ⟨551376, by rfl⟩ : syracuseStep 5881349 = 1102753) (by norm_num)
theorem B3923581 : Blo 1835619 3923581 := bbase (se 3 (by rfl) ⟨735671, by rfl⟩ : syracuseStep 3923581 = 1471343) (by norm_num)
theorem B2981509 : Blo 1835619 2981509 := bbase (se 4 (by rfl) ⟨279516, by rfl⟩ : syracuseStep 2981509 = 559033) (by norm_num)
theorem B6200981 : Blo 1835619 6200981 := bbase (se 6 (by rfl) ⟨145335, by rfl⟩ : syracuseStep 6200981 = 290671) (by norm_num)
theorem B6971093 : Blo 1835619 6971093 := bbase (se 7 (by rfl) ⟨81692, by rfl⟩ : syracuseStep 6971093 = 163385) (by norm_num)
theorem B2940661 : Blo 1835619 2940661 := bbase (se 5 (by rfl) ⟨137843, by rfl⟩ : syracuseStep 2940661 = 275687) (by norm_num)
theorem B2514773 : Blo 1835619 2514773 := bbase (se 9 (by rfl) ⟨7367, by rfl⟩ : syracuseStep 2514773 = 14735) (by norm_num)
theorem B2236261 : Blo 1835619 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B2981821 : Blo 1835619 2981821 := bbase (se 3 (by rfl) ⟨559091, by rfl⟩ : syracuseStep 2981821 = 1118183) (by norm_num)
theorem B3923957 : Blo 1835619 3923957 := bbase (se 5 (by rfl) ⟨183935, by rfl⟩ : syracuseStep 3923957 = 367871) (by norm_num)
theorem B13942853 : Blo 1835619 13942853 := bstep (se 4 (by rfl) ⟨1307142, by rfl⟩ : syracuseStep 13942853 = 2614285) B2614285
theorem B8380493 : Blo 1835619 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B7848035 : Blo 1835619 7848035 := bstep (se 1 (by rfl) ⟨5886026, by rfl⟩ : syracuseStep 7848035 = 11772053) B11772053
theorem B2482307 : Blo 1835619 2482307 := bstep (se 1 (by rfl) ⟨1861730, by rfl⟩ : syracuseStep 2482307 = 3723461) B3723461
theorem B6201521 : Blo 1835619 6201521 := bstep (se 2 (by rfl) ⟨2325570, by rfl⟩ : syracuseStep 6201521 = 4651141) B4651141
theorem B2941219 : Blo 1835619 2941219 := bstep (se 1 (by rfl) ⟨2205914, by rfl⟩ : syracuseStep 2941219 = 4411829) B4411829
theorem B9929101 : Blo 1835619 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B2482579 : Blo 1835619 2482579 := bstep (se 1 (by rfl) ⟨1861934, by rfl⟩ : syracuseStep 2482579 = 3723869) B3723869
theorem B31392197 : Blo 1835619 31392197 := bstep (se 4 (by rfl) ⟨2943018, by rfl⟩ : syracuseStep 31392197 = 5886037) B5886037
theorem B11772485 : Blo 1835619 11772485 := bstep (se 4 (by rfl) ⟨1103670, by rfl⟩ : syracuseStep 11772485 = 2207341) B2207341
theorem B1835619 : Blo 1835619 1835619 := bstep (se 1 (by rfl) ⟨1376714, by rfl⟩ : syracuseStep 1835619 = 2753429) B2753429
theorem B13951601 : Blo 1835619 13951601 := bstep (se 2 (by rfl) ⟨5231850, by rfl⟩ : syracuseStep 13951601 = 10463701) B10463701
theorem B1835635 : Blo 1835619 1835635 := bstep (se 1 (by rfl) ⟨1376726, by rfl⟩ : syracuseStep 1835635 = 2753453) B2753453
theorem B2613875 : Blo 1835619 2613875 := bstep (se 1 (by rfl) ⟨1960406, by rfl⟩ : syracuseStep 2613875 = 3920813) B3920813
theorem B1835651 : Blo 1835619 1835651 := bstep (se 1 (by rfl) ⟨1376738, by rfl⟩ : syracuseStep 1835651 = 2753477) B2753477
theorem B1835667 : Blo 1835619 1835667 := bstep (se 1 (by rfl) ⟨1376750, by rfl⟩ : syracuseStep 1835667 = 2753501) B2753501
theorem B1835683 : Blo 1835619 1835683 := bstep (se 1 (by rfl) ⟨1376762, by rfl⟩ : syracuseStep 1835683 = 2753525) B2753525
theorem B1835699 : Blo 1835619 1835699 := bstep (se 1 (by rfl) ⟨1376774, by rfl⟩ : syracuseStep 1835699 = 2753549) B2753549
theorem B1835715 : Blo 1835619 1835715 := bstep (se 1 (by rfl) ⟨1376786, by rfl⟩ : syracuseStep 1835715 = 2753573) B2753573
theorem B15901381 : Blo 1835619 15901381 := bstep (se 4 (by rfl) ⟨1490754, by rfl⟩ : syracuseStep 15901381 = 2981509) B2981509
theorem B9298637 : Blo 1835619 9298637 := bstep (se 3 (by rfl) ⟨1743494, by rfl⟩ : syracuseStep 9298637 = 3486989) B3486989
theorem B1835731 : Blo 1835619 1835731 := bstep (se 1 (by rfl) ⟨1376798, by rfl⟩ : syracuseStep 1835731 = 2753597) B2753597
theorem B1835747 : Blo 1835619 1835747 := bstep (se 1 (by rfl) ⟨1376810, by rfl⟩ : syracuseStep 1835747 = 2753621) B2753621
theorem B5227249 : Blo 1835619 5227249 := bstep (se 2 (by rfl) ⟨1960218, by rfl⟩ : syracuseStep 5227249 = 3920437) B3920437
theorem B1835763 : Blo 1835619 1835763 := bstep (se 1 (by rfl) ⟨1376822, by rfl⟩ : syracuseStep 1835763 = 2753645) B2753645
theorem B1835779 : Blo 1835619 1835779 := bstep (se 1 (by rfl) ⟨1376834, by rfl⟩ : syracuseStep 1835779 = 2753669) B2753669
theorem B2065171 : Blo 1835619 2065171 := bstep (se 1 (by rfl) ⟨1548878, by rfl⟩ : syracuseStep 2065171 = 3097757) B3097757
theorem B1835795 : Blo 1835619 1835795 := bstep (se 1 (by rfl) ⟨1376846, by rfl⟩ : syracuseStep 1835795 = 2753693) B2753693
theorem B1835811 : Blo 1835619 1835811 := bstep (se 1 (by rfl) ⟨1376858, by rfl⟩ : syracuseStep 1835811 = 2753717) B2753717
theorem B1835827 : Blo 1835619 1835827 := bstep (se 1 (by rfl) ⟨1376870, by rfl⟩ : syracuseStep 1835827 = 2753741) B2753741
theorem B1835843 : Blo 1835619 1835843 := bstep (se 1 (by rfl) ⟨1376882, by rfl⟩ : syracuseStep 1835843 = 2753765) B2753765
theorem B2941763 : Blo 1835619 2941763 := bstep (se 1 (by rfl) ⟨2206322, by rfl⟩ : syracuseStep 2941763 = 4412645) B4412645
theorem B1835859 : Blo 1835619 1835859 := bstep (se 1 (by rfl) ⟨1376894, by rfl⟩ : syracuseStep 1835859 = 2753789) B2753789
theorem B1835875 : Blo 1835619 1835875 := bstep (se 1 (by rfl) ⟨1376906, by rfl⟩ : syracuseStep 1835875 = 2753813) B2753813
theorem B1835891 : Blo 1835619 1835891 := bstep (se 1 (by rfl) ⟨1376918, by rfl⟩ : syracuseStep 1835891 = 2753837) B2753837
theorem B1835907 : Blo 1835619 1835907 := bstep (se 1 (by rfl) ⟨1376930, by rfl⟩ : syracuseStep 1835907 = 2753861) B2753861
theorem B5227409 : Blo 1835619 5227409 := bstep (se 2 (by rfl) ⟨1960278, by rfl⟩ : syracuseStep 5227409 = 3920557) B3920557
theorem B1835923 : Blo 1835619 1835923 := bstep (se 1 (by rfl) ⟨1376942, by rfl⟩ : syracuseStep 1835923 = 2753885) B2753885
theorem B2753441 : Blo 1835619 2753441 := bstep (se 2 (by rfl) ⟨1032540, by rfl⟩ : syracuseStep 2753441 = 2065081) B2065081
theorem B2065315 : Blo 1835619 2065315 := bstep (se 1 (by rfl) ⟨1548986, by rfl⟩ : syracuseStep 2065315 = 3097973) B3097973
theorem B1835939 : Blo 1835619 1835939 := bstep (se 1 (by rfl) ⟨1376954, by rfl⟩ : syracuseStep 1835939 = 2753909) B2753909
theorem B6890417 : Blo 1835619 6890417 := bstep (se 2 (by rfl) ⟨2583906, by rfl⟩ : syracuseStep 6890417 = 5167813) B5167813
theorem B2753459 : Blo 1835619 2753459 := bstep (se 1 (by rfl) ⟨2065094, by rfl⟩ : syracuseStep 2753459 = 4130189) B4130189
theorem B1835955 : Blo 1835619 1835955 := bstep (se 1 (by rfl) ⟨1376966, by rfl⟩ : syracuseStep 1835955 = 2753933) B2753933
theorem B1835971 : Blo 1835619 1835971 := bstep (se 1 (by rfl) ⟨1376978, by rfl⟩ : syracuseStep 1835971 = 2753957) B2753957
theorem B70583237 : Blo 1835619 70583237 := bstep (se 4 (by rfl) ⟨6617178, by rfl⟩ : syracuseStep 70583237 = 13234357) B13234357
theorem B2753489 : Blo 1835619 2753489 := bstep (se 2 (by rfl) ⟨1032558, by rfl⟩ : syracuseStep 2753489 = 2065117) B2065117
theorem B1835987 : Blo 1835619 1835987 := bstep (se 1 (by rfl) ⟨1376990, by rfl⟩ : syracuseStep 1835987 = 2753981) B2753981
theorem B2753507 : Blo 1835619 2753507 := bstep (se 1 (by rfl) ⟨2065130, by rfl⟩ : syracuseStep 2753507 = 4130261) B4130261
theorem B1836003 : Blo 1835619 1836003 := bstep (se 1 (by rfl) ⟨1377002, by rfl⟩ : syracuseStep 1836003 = 2754005) B2754005
theorem B2941937 : Blo 1835619 2941937 := bstep (se 2 (by rfl) ⟨1103226, by rfl⟩ : syracuseStep 2941937 = 2206453) B2206453
theorem B7955441 : Blo 1835619 7955441 := bstep (se 2 (by rfl) ⟨2983290, by rfl⟩ : syracuseStep 7955441 = 5966581) B5966581
theorem B1836019 : Blo 1835619 1836019 := bstep (se 1 (by rfl) ⟨1377014, by rfl⟩ : syracuseStep 1836019 = 2754029) B2754029
theorem B2753537 : Blo 1835619 2753537 := bstep (se 2 (by rfl) ⟨1032576, by rfl⟩ : syracuseStep 2753537 = 2065153) B2065153
theorem B5227523 : Blo 1835619 5227523 := bstep (se 1 (by rfl) ⟨3920642, by rfl⟩ : syracuseStep 5227523 = 7841285) B7841285
theorem B1836035 : Blo 1835619 1836035 := bstep (se 1 (by rfl) ⟨1377026, by rfl⟩ : syracuseStep 1836035 = 2754053) B2754053
theorem B2753555 : Blo 1835619 2753555 := bstep (se 1 (by rfl) ⟨2065166, by rfl⟩ : syracuseStep 2753555 = 4130333) B4130333
theorem B1836051 : Blo 1835619 1836051 := bstep (se 1 (by rfl) ⟨1377038, by rfl⟩ : syracuseStep 1836051 = 2754077) B2754077
theorem B1836067 : Blo 1835619 1836067 := bstep (se 1 (by rfl) ⟨1377050, by rfl⟩ : syracuseStep 1836067 = 2754101) B2754101
theorem B10462243 : Blo 1835619 10462243 := bstep (se 1 (by rfl) ⟨7846682, by rfl⟩ : syracuseStep 10462243 = 15693365) B15693365
theorem B3097649 : Blo 1835619 3097649 := bstep (se 2 (by rfl) ⟨1161618, by rfl⟩ : syracuseStep 3097649 = 2323237) B2323237
theorem B2753585 : Blo 1835619 2753585 := bstep (se 2 (by rfl) ⟨1032594, by rfl⟩ : syracuseStep 2753585 = 2065189) B2065189
theorem B2065459 : Blo 1835619 2065459 := bstep (se 1 (by rfl) ⟨1549094, by rfl⟩ : syracuseStep 2065459 = 3098189) B3098189
theorem B1836083 : Blo 1835619 1836083 := bstep (se 1 (by rfl) ⟨1377062, by rfl⟩ : syracuseStep 1836083 = 2754125) B2754125
theorem B2753603 : Blo 1835619 2753603 := bstep (se 1 (by rfl) ⟨2065202, by rfl⟩ : syracuseStep 2753603 = 4130405) B4130405
theorem B1836099 : Blo 1835619 1836099 := bstep (se 1 (by rfl) ⟨1377074, by rfl⟩ : syracuseStep 1836099 = 2754149) B2754149
theorem B1836115 : Blo 1835619 1836115 := bstep (se 1 (by rfl) ⟨1377086, by rfl⟩ : syracuseStep 1836115 = 2754173) B2754173
theorem B2753633 : Blo 1835619 2753633 := bstep (se 2 (by rfl) ⟨1032612, by rfl⟩ : syracuseStep 2753633 = 2065225) B2065225
theorem B1836131 : Blo 1835619 1836131 := bstep (se 1 (by rfl) ⟨1377098, by rfl⟩ : syracuseStep 1836131 = 2754197) B2754197
theorem B5882989 : Blo 1835619 5882989 := bstep (se 3 (by rfl) ⟨1103060, by rfl⟩ : syracuseStep 5882989 = 2206121) B2206121
theorem B2753651 : Blo 1835619 2753651 := bstep (se 1 (by rfl) ⟨2065238, by rfl⟩ : syracuseStep 2753651 = 4130477) B4130477
theorem B1836147 : Blo 1835619 1836147 := bstep (se 1 (by rfl) ⟨1377110, by rfl⟩ : syracuseStep 1836147 = 2754221) B2754221
theorem B1836163 : Blo 1835619 1836163 := bstep (se 1 (by rfl) ⟨1377122, by rfl⟩ : syracuseStep 1836163 = 2754245) B2754245
theorem B2753681 : Blo 1835619 2753681 := bstep (se 2 (by rfl) ⟨1032630, by rfl⟩ : syracuseStep 2753681 = 2065261) B2065261
theorem B1836179 : Blo 1835619 1836179 := bstep (se 1 (by rfl) ⟨1377134, by rfl⟩ : syracuseStep 1836179 = 2754269) B2754269
theorem B2753699 : Blo 1835619 2753699 := bstep (se 1 (by rfl) ⟨2065274, by rfl⟩ : syracuseStep 2753699 = 4130549) B4130549
theorem B1836195 : Blo 1835619 1836195 := bstep (se 1 (by rfl) ⟨1377146, by rfl⟩ : syracuseStep 1836195 = 2754293) B2754293
theorem B3097777 : Blo 1835619 3097777 := bstep (se 2 (by rfl) ⟨1161666, by rfl⟩ : syracuseStep 3097777 = 2323333) B2323333
theorem B1836211 : Blo 1835619 1836211 := bstep (se 1 (by rfl) ⟨1377158, by rfl⟩ : syracuseStep 1836211 = 2754317) B2754317
theorem B2753729 : Blo 1835619 2753729 := bstep (se 2 (by rfl) ⟨1032648, by rfl⟩ : syracuseStep 2753729 = 2065297) B2065297
theorem B2065603 : Blo 1835619 2065603 := bstep (se 1 (by rfl) ⟨1549202, by rfl⟩ : syracuseStep 2065603 = 3098405) B3098405
theorem B1836227 : Blo 1835619 1836227 := bstep (se 1 (by rfl) ⟨1377170, by rfl⟩ : syracuseStep 1836227 = 2754341) B2754341
theorem B3097811 : Blo 1835619 3097811 := bstep (se 1 (by rfl) ⟨2323358, by rfl⟩ : syracuseStep 3097811 = 4646717) B4646717
theorem B2753747 : Blo 1835619 2753747 := bstep (se 1 (by rfl) ⟨2065310, by rfl⟩ : syracuseStep 2753747 = 4130621) B4130621
theorem B1836243 : Blo 1835619 1836243 := bstep (se 1 (by rfl) ⟨1377182, by rfl⟩ : syracuseStep 1836243 = 2754365) B2754365
theorem B1836259 : Blo 1835619 1836259 := bstep (se 1 (by rfl) ⟨1377194, by rfl⟩ : syracuseStep 1836259 = 2754389) B2754389
theorem B2753777 : Blo 1835619 2753777 := bstep (se 2 (by rfl) ⟨1032666, by rfl⟩ : syracuseStep 2753777 = 2065333) B2065333
theorem B2614513 : Blo 1835619 2614513 := bstep (se 2 (by rfl) ⟨980442, by rfl⟩ : syracuseStep 2614513 = 1960885) B1960885
theorem B1860851 : Blo 1835619 1860851 := bstep (se 1 (by rfl) ⟨1395638, by rfl⟩ : syracuseStep 1860851 = 2791277) B2791277
theorem B1836275 : Blo 1835619 1836275 := bstep (se 1 (by rfl) ⟨1377206, by rfl⟩ : syracuseStep 1836275 = 2754413) B2754413
theorem B2753795 : Blo 1835619 2753795 := bstep (se 1 (by rfl) ⟨2065346, by rfl⟩ : syracuseStep 2753795 = 4130693) B4130693
theorem B1836291 : Blo 1835619 1836291 := bstep (se 1 (by rfl) ⟨1377218, by rfl⟩ : syracuseStep 1836291 = 2754437) B2754437
theorem B1836307 : Blo 1835619 1836307 := bstep (se 1 (by rfl) ⟨1377230, by rfl⟩ : syracuseStep 1836307 = 2754461) B2754461
theorem B2753825 : Blo 1835619 2753825 := bstep (se 2 (by rfl) ⟨1032684, by rfl⟩ : syracuseStep 2753825 = 2065369) B2065369
theorem B1836323 : Blo 1835619 1836323 := bstep (se 1 (by rfl) ⟨1377242, by rfl⟩ : syracuseStep 1836323 = 2754485) B2754485
theorem B2753843 : Blo 1835619 2753843 := bstep (se 1 (by rfl) ⟨2065382, by rfl⟩ : syracuseStep 2753843 = 4130765) B4130765
theorem B1836339 : Blo 1835619 1836339 := bstep (se 1 (by rfl) ⟨1377254, by rfl⟩ : syracuseStep 1836339 = 2754509) B2754509
theorem B1836355 : Blo 1835619 1836355 := bstep (se 1 (by rfl) ⟨1377266, by rfl⟩ : syracuseStep 1836355 = 2754533) B2754533
theorem B6972749 : Blo 1835619 6972749 := bstep (se 3 (by rfl) ⟨1307390, by rfl⟩ : syracuseStep 6972749 = 2614781) B2614781
theorem B2753873 : Blo 1835619 2753873 := bstep (se 2 (by rfl) ⟨1032702, by rfl⟩ : syracuseStep 2753873 = 2065405) B2065405
theorem B3097939 : Blo 1835619 3097939 := bstep (se 1 (by rfl) ⟨2323454, by rfl⟩ : syracuseStep 3097939 = 4646909) B4646909
theorem B2065747 : Blo 1835619 2065747 := bstep (se 1 (by rfl) ⟨1549310, by rfl⟩ : syracuseStep 2065747 = 3098621) B3098621
theorem B1836371 : Blo 1835619 1836371 := bstep (se 1 (by rfl) ⟨1377278, by rfl⟩ : syracuseStep 1836371 = 2754557) B2754557
theorem B2753891 : Blo 1835619 2753891 := bstep (se 1 (by rfl) ⟨2065418, by rfl⟩ : syracuseStep 2753891 = 4130837) B4130837
theorem B2614627 : Blo 1835619 2614627 := bstep (se 1 (by rfl) ⟨1960970, by rfl⟩ : syracuseStep 2614627 = 3921941) B3921941
theorem B1836387 : Blo 1835619 1836387 := bstep (se 1 (by rfl) ⟨1377290, by rfl⟩ : syracuseStep 1836387 = 2754581) B2754581
theorem B1836403 : Blo 1835619 1836403 := bstep (se 1 (by rfl) ⟨1377302, by rfl⟩ : syracuseStep 1836403 = 2754605) B2754605
theorem B2753921 : Blo 1835619 2753921 := bstep (se 2 (by rfl) ⟨1032720, by rfl⟩ : syracuseStep 2753921 = 2065441) B2065441
theorem B1836419 : Blo 1835619 1836419 := bstep (se 1 (by rfl) ⟨1377314, by rfl⟩ : syracuseStep 1836419 = 2754629) B2754629
theorem B12092813 : Blo 1835619 12092813 := bstep (se 3 (by rfl) ⟨2267402, by rfl⟩ : syracuseStep 12092813 = 4534805) B4534805
theorem B2753939 : Blo 1835619 2753939 := bstep (se 1 (by rfl) ⟨2065454, by rfl⟩ : syracuseStep 2753939 = 4130909) B4130909
theorem B1836435 : Blo 1835619 1836435 := bstep (se 1 (by rfl) ⟨1377326, by rfl⟩ : syracuseStep 1836435 = 2754653) B2754653
theorem B1836451 : Blo 1835619 1836451 := bstep (se 1 (by rfl) ⟨1377338, by rfl⟩ : syracuseStep 1836451 = 2754677) B2754677
theorem B4130225 : Blo 1835619 4130225 := bstep (se 2 (by rfl) ⟨1548834, by rfl⟩ : syracuseStep 4130225 = 3097669) B3097669
theorem B2753969 : Blo 1835619 2753969 := bstep (se 2 (by rfl) ⟨1032738, by rfl⟩ : syracuseStep 2753969 = 2065477) B2065477
theorem B1836467 : Blo 1835619 1836467 := bstep (se 1 (by rfl) ⟨1377350, by rfl⟩ : syracuseStep 1836467 = 2754701) B2754701
theorem B4130243 : Blo 1835619 4130243 := bstep (se 1 (by rfl) ⟨3097682, by rfl⟩ : syracuseStep 4130243 = 6195365) B6195365
theorem B2753987 : Blo 1835619 2753987 := bstep (se 1 (by rfl) ⟨2065490, by rfl⟩ : syracuseStep 2753987 = 4130981) B4130981
theorem B1836483 : Blo 1835619 1836483 := bstep (se 1 (by rfl) ⟨1377362, by rfl⟩ : syracuseStep 1836483 = 2754725) B2754725
theorem B1836499 : Blo 1835619 1836499 := bstep (se 1 (by rfl) ⟨1377374, by rfl⟩ : syracuseStep 1836499 = 2754749) B2754749
theorem B3098081 : Blo 1835619 3098081 := bstep (se 2 (by rfl) ⟨1161780, by rfl⟩ : syracuseStep 3098081 = 2323561) B2323561
theorem B2754017 : Blo 1835619 2754017 := bstep (se 2 (by rfl) ⟨1032756, by rfl⟩ : syracuseStep 2754017 = 2065513) B2065513
theorem B2065891 : Blo 1835619 2065891 := bstep (se 1 (by rfl) ⟨1549418, by rfl⟩ : syracuseStep 2065891 = 3098837) B3098837
theorem B1836515 : Blo 1835619 1836515 := bstep (se 1 (by rfl) ⟨1377386, by rfl⟩ : syracuseStep 1836515 = 2754773) B2754773
theorem B2754035 : Blo 1835619 2754035 := bstep (se 1 (by rfl) ⟨2065526, by rfl⟩ : syracuseStep 2754035 = 4131053) B4131053
theorem B1836531 : Blo 1835619 1836531 := bstep (se 1 (by rfl) ⟨1377398, by rfl⟩ : syracuseStep 1836531 = 2754797) B2754797
theorem B1836547 : Blo 1835619 1836547 := bstep (se 1 (by rfl) ⟨1377410, by rfl⟩ : syracuseStep 1836547 = 2754821) B2754821
theorem B2754065 : Blo 1835619 2754065 := bstep (se 2 (by rfl) ⟨1032774, by rfl⟩ : syracuseStep 2754065 = 2065549) B2065549
theorem B1836563 : Blo 1835619 1836563 := bstep (se 1 (by rfl) ⟨1377422, by rfl⟩ : syracuseStep 1836563 = 2754845) B2754845
theorem B2754083 : Blo 1835619 2754083 := bstep (se 1 (by rfl) ⟨2065562, by rfl⟩ : syracuseStep 2754083 = 4131125) B4131125
theorem B1836579 : Blo 1835619 1836579 := bstep (se 1 (by rfl) ⟨1377434, by rfl⟩ : syracuseStep 1836579 = 2754869) B2754869
theorem B1836595 : Blo 1835619 1836595 := bstep (se 1 (by rfl) ⟨1377446, by rfl⟩ : syracuseStep 1836595 = 2754893) B2754893
theorem B10462769 : Blo 1835619 10462769 := bstep (se 2 (by rfl) ⟨3923538, by rfl⟩ : syracuseStep 10462769 = 7847077) B7847077
theorem B2754113 : Blo 1835619 2754113 := bstep (se 2 (by rfl) ⟨1032792, by rfl⟩ : syracuseStep 2754113 = 2065585) B2065585
theorem B1836611 : Blo 1835619 1836611 := bstep (se 1 (by rfl) ⟨1377458, by rfl⟩ : syracuseStep 1836611 = 2754917) B2754917
theorem B3311185 : Blo 1835619 3311185 := bstep (se 2 (by rfl) ⟨1241694, by rfl⟩ : syracuseStep 3311185 = 2483389) B2483389
theorem B2754131 : Blo 1835619 2754131 := bstep (se 1 (by rfl) ⟨2065598, by rfl⟩ : syracuseStep 2754131 = 4131197) B4131197
theorem B1836627 : Blo 1835619 1836627 := bstep (se 1 (by rfl) ⟨1377470, by rfl⟩ : syracuseStep 1836627 = 2754941) B2754941
theorem B3098209 : Blo 1835619 3098209 := bstep (se 2 (by rfl) ⟨1161828, by rfl⟩ : syracuseStep 3098209 = 2323657) B2323657
theorem B1836643 : Blo 1835619 1836643 := bstep (se 1 (by rfl) ⟨1377482, by rfl⟩ : syracuseStep 1836643 = 2754965) B2754965
theorem B2754161 : Blo 1835619 2754161 := bstep (se 2 (by rfl) ⟨1032810, by rfl⟩ : syracuseStep 2754161 = 2065621) B2065621
theorem B2066035 : Blo 1835619 2066035 := bstep (se 1 (by rfl) ⟨1549526, by rfl⟩ : syracuseStep 2066035 = 3099053) B3099053
theorem B1836659 : Blo 1835619 1836659 := bstep (se 1 (by rfl) ⟨1377494, by rfl⟩ : syracuseStep 1836659 = 2754989) B2754989
theorem B3098243 : Blo 1835619 3098243 := bstep (se 1 (by rfl) ⟨2323682, by rfl⟩ : syracuseStep 3098243 = 4647365) B4647365
theorem B2754179 : Blo 1835619 2754179 := bstep (se 1 (by rfl) ⟨2065634, by rfl⟩ : syracuseStep 2754179 = 4131269) B4131269
theorem B1836675 : Blo 1835619 1836675 := bstep (se 1 (by rfl) ⟨1377506, by rfl⟩ : syracuseStep 1836675 = 2755013) B2755013
theorem B1836691 : Blo 1835619 1836691 := bstep (se 1 (by rfl) ⟨1377518, by rfl⟩ : syracuseStep 1836691 = 2755037) B2755037
theorem B2754209 : Blo 1835619 2754209 := bstep (se 2 (by rfl) ⟨1032828, by rfl⟩ : syracuseStep 2754209 = 2065657) B2065657
theorem B1836707 : Blo 1835619 1836707 := bstep (se 1 (by rfl) ⟨1377530, by rfl⟩ : syracuseStep 1836707 = 2755061) B2755061
theorem B2754227 : Blo 1835619 2754227 := bstep (se 1 (by rfl) ⟨2065670, by rfl⟩ : syracuseStep 2754227 = 4131341) B4131341
theorem B1836723 : Blo 1835619 1836723 := bstep (se 1 (by rfl) ⟨1377542, by rfl⟩ : syracuseStep 1836723 = 2755085) B2755085
theorem B1836739 : Blo 1835619 1836739 := bstep (se 1 (by rfl) ⟨1377554, by rfl⟩ : syracuseStep 1836739 = 2755109) B2755109
theorem B4130513 : Blo 1835619 4130513 := bstep (se 2 (by rfl) ⟨1548942, by rfl⟩ : syracuseStep 4130513 = 3097885) B3097885
theorem B2754257 : Blo 1835619 2754257 := bstep (se 2 (by rfl) ⟨1032846, by rfl⟩ : syracuseStep 2754257 = 2065693) B2065693
theorem B1836755 : Blo 1835619 1836755 := bstep (se 1 (by rfl) ⟨1377566, by rfl⟩ : syracuseStep 1836755 = 2755133) B2755133
theorem B4130531 : Blo 1835619 4130531 := bstep (se 1 (by rfl) ⟨3097898, by rfl⟩ : syracuseStep 4130531 = 6195797) B6195797
theorem B2754275 : Blo 1835619 2754275 := bstep (se 1 (by rfl) ⟨2065706, by rfl⟩ : syracuseStep 2754275 = 4131413) B4131413
theorem B1836771 : Blo 1835619 1836771 := bstep (se 1 (by rfl) ⟨1377578, by rfl⟩ : syracuseStep 1836771 = 2755157) B2755157
theorem B1836787 : Blo 1835619 1836787 := bstep (se 1 (by rfl) ⟨1377590, by rfl⟩ : syracuseStep 1836787 = 2755181) B2755181
theorem B2754305 : Blo 1835619 2754305 := bstep (se 2 (by rfl) ⟨1032864, by rfl⟩ : syracuseStep 2754305 = 2065729) B2065729
theorem B3098371 : Blo 1835619 3098371 := bstep (se 1 (by rfl) ⟨2323778, by rfl⟩ : syracuseStep 3098371 = 4647557) B4647557
theorem B2066179 : Blo 1835619 2066179 := bstep (se 1 (by rfl) ⟨1549634, by rfl⟩ : syracuseStep 2066179 = 3099269) B3099269
theorem B1836803 : Blo 1835619 1836803 := bstep (se 1 (by rfl) ⟨1377602, by rfl⟩ : syracuseStep 1836803 = 2755205) B2755205
theorem B2754323 : Blo 1835619 2754323 := bstep (se 1 (by rfl) ⟨2065742, by rfl⟩ : syracuseStep 2754323 = 4131485) B4131485
theorem B1836819 : Blo 1835619 1836819 := bstep (se 1 (by rfl) ⟨1377614, by rfl⟩ : syracuseStep 1836819 = 2755229) B2755229
theorem B1836835 : Blo 1835619 1836835 := bstep (se 1 (by rfl) ⟨1377626, by rfl⟩ : syracuseStep 1836835 = 2755253) B2755253
theorem B2754353 : Blo 1835619 2754353 := bstep (se 2 (by rfl) ⟨1032882, by rfl⟩ : syracuseStep 2754353 = 2065765) B2065765
theorem B1836851 : Blo 1835619 1836851 := bstep (se 1 (by rfl) ⟨1377638, by rfl⟩ : syracuseStep 1836851 = 2755277) B2755277
theorem B2754371 : Blo 1835619 2754371 := bstep (se 1 (by rfl) ⟨2065778, by rfl⟩ : syracuseStep 2754371 = 4131557) B4131557
theorem B1836867 : Blo 1835619 1836867 := bstep (se 1 (by rfl) ⟨1377650, by rfl⟩ : syracuseStep 1836867 = 2755301) B2755301
theorem B1836883 : Blo 1835619 1836883 := bstep (se 1 (by rfl) ⟨1377662, by rfl⟩ : syracuseStep 1836883 = 2755325) B2755325
theorem B2754401 : Blo 1835619 2754401 := bstep (se 2 (by rfl) ⟨1032900, by rfl⟩ : syracuseStep 2754401 = 2065801) B2065801
theorem B1836899 : Blo 1835619 1836899 := bstep (se 1 (by rfl) ⟨1377674, by rfl⟩ : syracuseStep 1836899 = 2755349) B2755349
theorem B2754419 : Blo 1835619 2754419 := bstep (se 1 (by rfl) ⟨2065814, by rfl⟩ : syracuseStep 2754419 = 4131629) B4131629
theorem B1836915 : Blo 1835619 1836915 := bstep (se 1 (by rfl) ⟨1377686, by rfl⟩ : syracuseStep 1836915 = 2755373) B2755373
theorem B1836931 : Blo 1835619 1836931 := bstep (se 1 (by rfl) ⟨1377698, by rfl⟩ : syracuseStep 1836931 = 2755397) B2755397
theorem B3098513 : Blo 1835619 3098513 := bstep (se 2 (by rfl) ⟨1161942, by rfl⟩ : syracuseStep 3098513 = 2323885) B2323885
theorem B2754449 : Blo 1835619 2754449 := bstep (se 2 (by rfl) ⟨1032918, by rfl⟩ : syracuseStep 2754449 = 2065837) B2065837
theorem B2066323 : Blo 1835619 2066323 := bstep (se 1 (by rfl) ⟨1549742, by rfl⟩ : syracuseStep 2066323 = 3099485) B3099485
theorem B1836947 : Blo 1835619 1836947 := bstep (se 1 (by rfl) ⟨1377710, by rfl⟩ : syracuseStep 1836947 = 2755421) B2755421
theorem B2754467 : Blo 1835619 2754467 := bstep (se 1 (by rfl) ⟨2065850, by rfl⟩ : syracuseStep 2754467 = 4131701) B4131701
theorem B1836963 : Blo 1835619 1836963 := bstep (se 1 (by rfl) ⟨1377722, by rfl⟩ : syracuseStep 1836963 = 2755445) B2755445
theorem B1836979 : Blo 1835619 1836979 := bstep (se 1 (by rfl) ⟨1377734, by rfl⟩ : syracuseStep 1836979 = 2755469) B2755469
theorem B2754497 : Blo 1835619 2754497 := bstep (se 2 (by rfl) ⟨1032936, by rfl⟩ : syracuseStep 2754497 = 2065873) B2065873
theorem B1836995 : Blo 1835619 1836995 := bstep (se 1 (by rfl) ⟨1377746, by rfl⟩ : syracuseStep 1836995 = 2755493) B2755493
theorem B2754515 : Blo 1835619 2754515 := bstep (se 1 (by rfl) ⟨2065886, by rfl⟩ : syracuseStep 2754515 = 4131773) B4131773
theorem B1837011 : Blo 1835619 1837011 := bstep (se 1 (by rfl) ⟨1377758, by rfl⟩ : syracuseStep 1837011 = 2755517) B2755517
theorem B1837027 : Blo 1835619 1837027 := bstep (se 1 (by rfl) ⟨1377770, by rfl⟩ : syracuseStep 1837027 = 2755541) B2755541
theorem B5228525 : Blo 1835619 5228525 := bstep (se 3 (by rfl) ⟨980348, by rfl⟩ : syracuseStep 5228525 = 1960697) B1960697
theorem B4130801 : Blo 1835619 4130801 := bstep (se 2 (by rfl) ⟨1549050, by rfl⟩ : syracuseStep 4130801 = 3098101) B3098101
theorem B2754545 : Blo 1835619 2754545 := bstep (se 2 (by rfl) ⟨1032954, by rfl⟩ : syracuseStep 2754545 = 2065909) B2065909
theorem B1837043 : Blo 1835619 1837043 := bstep (se 1 (by rfl) ⟨1377782, by rfl⟩ : syracuseStep 1837043 = 2755565) B2755565
theorem B4130819 : Blo 1835619 4130819 := bstep (se 1 (by rfl) ⟨3098114, by rfl⟩ : syracuseStep 4130819 = 6196229) B6196229
theorem B2754563 : Blo 1835619 2754563 := bstep (se 1 (by rfl) ⟨2065922, by rfl⟩ : syracuseStep 2754563 = 4131845) B4131845
theorem B1837059 : Blo 1835619 1837059 := bstep (se 1 (by rfl) ⟨1377794, by rfl⟩ : syracuseStep 1837059 = 2755589) B2755589
theorem B4646929 : Blo 1835619 4646929 := bstep (se 2 (by rfl) ⟨1742598, by rfl⟩ : syracuseStep 4646929 = 3485197) B3485197
theorem B3098641 : Blo 1835619 3098641 := bstep (se 2 (by rfl) ⟨1161990, by rfl⟩ : syracuseStep 3098641 = 2323981) B2323981
theorem B1837075 : Blo 1835619 1837075 := bstep (se 1 (by rfl) ⟨1377806, by rfl⟩ : syracuseStep 1837075 = 2755613) B2755613
theorem B2754593 : Blo 1835619 2754593 := bstep (se 2 (by rfl) ⟨1032972, by rfl⟩ : syracuseStep 2754593 = 2065945) B2065945
theorem B2066467 : Blo 1835619 2066467 := bstep (se 1 (by rfl) ⟨1549850, by rfl⟩ : syracuseStep 2066467 = 3099701) B3099701
theorem B1837091 : Blo 1835619 1837091 := bstep (se 1 (by rfl) ⟨1377818, by rfl⟩ : syracuseStep 1837091 = 2755637) B2755637
theorem B3098675 : Blo 1835619 3098675 := bstep (se 1 (by rfl) ⟨2324006, by rfl⟩ : syracuseStep 3098675 = 4648013) B4648013
theorem B2754611 : Blo 1835619 2754611 := bstep (se 1 (by rfl) ⟨2065958, by rfl⟩ : syracuseStep 2754611 = 4131917) B4131917
theorem B1837107 : Blo 1835619 1837107 := bstep (se 1 (by rfl) ⟨1377830, by rfl⟩ : syracuseStep 1837107 = 2755661) B2755661
theorem B1837123 : Blo 1835619 1837123 := bstep (se 1 (by rfl) ⟨1377842, by rfl⟩ : syracuseStep 1837123 = 2755685) B2755685
theorem B2754641 : Blo 1835619 2754641 := bstep (se 2 (by rfl) ⟨1032990, by rfl⟩ : syracuseStep 2754641 = 2065981) B2065981
theorem B1837139 : Blo 1835619 1837139 := bstep (se 1 (by rfl) ⟨1377854, by rfl⟩ : syracuseStep 1837139 = 2755709) B2755709
theorem B2754659 : Blo 1835619 2754659 := bstep (se 1 (by rfl) ⟨2065994, by rfl⟩ : syracuseStep 2754659 = 4131989) B4131989
theorem B1837155 : Blo 1835619 1837155 := bstep (se 1 (by rfl) ⟨1377866, by rfl⟩ : syracuseStep 1837155 = 2755733) B2755733
theorem B6973553 : Blo 1835619 6973553 := bstep (se 2 (by rfl) ⟨2615082, by rfl⟩ : syracuseStep 6973553 = 5230165) B5230165
theorem B1837171 : Blo 1835619 1837171 := bstep (se 1 (by rfl) ⟨1377878, by rfl⟩ : syracuseStep 1837171 = 2755757) B2755757
theorem B2754689 : Blo 1835619 2754689 := bstep (se 2 (by rfl) ⟨1033008, by rfl⟩ : syracuseStep 2754689 = 2066017) B2066017
theorem B1861763 : Blo 1835619 1861763 := bstep (se 1 (by rfl) ⟨1396322, by rfl⟩ : syracuseStep 1861763 = 2792645) B2792645
theorem B1837187 : Blo 1835619 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B2754707 : Blo 1835619 2754707 := bstep (se 1 (by rfl) ⟨2066030, by rfl⟩ : syracuseStep 2754707 = 4132061) B4132061
theorem B1837203 : Blo 1835619 1837203 := bstep (se 1 (by rfl) ⟨1377902, by rfl⟩ : syracuseStep 1837203 = 2755805) B2755805
theorem B5228707 : Blo 1835619 5228707 := bstep (se 1 (by rfl) ⟨3921530, by rfl⟩ : syracuseStep 5228707 = 7843061) B7843061
theorem B1837219 : Blo 1835619 1837219 := bstep (se 1 (by rfl) ⟨1377914, by rfl⟩ : syracuseStep 1837219 = 2755829) B2755829
theorem B2754737 : Blo 1835619 2754737 := bstep (se 2 (by rfl) ⟨1033026, by rfl⟩ : syracuseStep 2754737 = 2066053) B2066053
theorem B3098803 : Blo 1835619 3098803 := bstep (se 1 (by rfl) ⟨2324102, by rfl⟩ : syracuseStep 3098803 = 4648205) B4648205
theorem B2066611 : Blo 1835619 2066611 := bstep (se 1 (by rfl) ⟨1549958, by rfl⟩ : syracuseStep 2066611 = 3099917) B3099917
theorem B1837235 : Blo 1835619 1837235 := bstep (se 1 (by rfl) ⟨1377926, by rfl⟩ : syracuseStep 1837235 = 2755853) B2755853
theorem B2754755 : Blo 1835619 2754755 := bstep (se 1 (by rfl) ⟨2066066, by rfl⟩ : syracuseStep 2754755 = 4132133) B4132133
theorem B1837251 : Blo 1835619 1837251 := bstep (se 1 (by rfl) ⟨1377938, by rfl⟩ : syracuseStep 1837251 = 2755877) B2755877
theorem B1837267 : Blo 1835619 1837267 := bstep (se 1 (by rfl) ⟨1377950, by rfl⟩ : syracuseStep 1837267 = 2755901) B2755901
theorem B2754785 : Blo 1835619 2754785 := bstep (se 2 (by rfl) ⟨1033044, by rfl⟩ : syracuseStep 2754785 = 2066089) B2066089
theorem B1837283 : Blo 1835619 1837283 := bstep (se 1 (by rfl) ⟨1377962, by rfl⟩ : syracuseStep 1837283 = 2755925) B2755925
theorem B2754803 : Blo 1835619 2754803 := bstep (se 1 (by rfl) ⟨2066102, by rfl⟩ : syracuseStep 2754803 = 4132205) B4132205
theorem B1837299 : Blo 1835619 1837299 := bstep (se 1 (by rfl) ⟨1377974, by rfl⟩ : syracuseStep 1837299 = 2755949) B2755949
theorem B1837315 : Blo 1835619 1837315 := bstep (se 1 (by rfl) ⟨1377986, by rfl⟩ : syracuseStep 1837315 = 2755973) B2755973
theorem B6195473 : Blo 1835619 6195473 := bstep (se 2 (by rfl) ⟨2323302, by rfl⟩ : syracuseStep 6195473 = 4646605) B4646605
theorem B4131089 : Blo 1835619 4131089 := bstep (se 2 (by rfl) ⟨1549158, by rfl⟩ : syracuseStep 4131089 = 3098317) B3098317
theorem B2754833 : Blo 1835619 2754833 := bstep (se 2 (by rfl) ⟨1033062, by rfl⟩ : syracuseStep 2754833 = 2066125) B2066125
theorem B1837331 : Blo 1835619 1837331 := bstep (se 1 (by rfl) ⟨1377998, by rfl⟩ : syracuseStep 1837331 = 2755997) B2755997
theorem B4647203 : Blo 1835619 4647203 := bstep (se 1 (by rfl) ⟨3485402, by rfl⟩ : syracuseStep 4647203 = 6970805) B6970805
theorem B4131107 : Blo 1835619 4131107 := bstep (se 1 (by rfl) ⟨3098330, by rfl⟩ : syracuseStep 4131107 = 6196661) B6196661
theorem B2754851 : Blo 1835619 2754851 := bstep (se 1 (by rfl) ⟨2066138, by rfl⟩ : syracuseStep 2754851 = 4132277) B4132277
theorem B1837347 : Blo 1835619 1837347 := bstep (se 1 (by rfl) ⟨1378010, by rfl⟩ : syracuseStep 1837347 = 2756021) B2756021
theorem B1837363 : Blo 1835619 1837363 := bstep (se 1 (by rfl) ⟨1378022, by rfl⟩ : syracuseStep 1837363 = 2756045) B2756045
theorem B3098945 : Blo 1835619 3098945 := bstep (se 2 (by rfl) ⟨1162104, by rfl⟩ : syracuseStep 3098945 = 2324209) B2324209
theorem B5228867 : Blo 1835619 5228867 := bstep (se 1 (by rfl) ⟨3921650, by rfl⟩ : syracuseStep 5228867 = 7843301) B7843301
theorem B2754881 : Blo 1835619 2754881 := bstep (se 2 (by rfl) ⟨1033080, by rfl⟩ : syracuseStep 2754881 = 2066161) B2066161
theorem B23529797 : Blo 1835619 23529797 := bstep (se 4 (by rfl) ⟨2205918, by rfl⟩ : syracuseStep 23529797 = 4411837) B4411837
theorem B2066755 : Blo 1835619 2066755 := bstep (se 1 (by rfl) ⟨1550066, by rfl⟩ : syracuseStep 2066755 = 3100133) B3100133
theorem B1837379 : Blo 1835619 1837379 := bstep (se 1 (by rfl) ⟨1378034, by rfl⟩ : syracuseStep 1837379 = 2756069) B2756069
theorem B2754899 : Blo 1835619 2754899 := bstep (se 1 (by rfl) ⟨2066174, by rfl⟩ : syracuseStep 2754899 = 4132349) B4132349
theorem B1837395 : Blo 1835619 1837395 := bstep (se 1 (by rfl) ⟨1378046, by rfl⟩ : syracuseStep 1837395 = 2756093) B2756093
theorem B1837411 : Blo 1835619 1837411 := bstep (se 1 (by rfl) ⟨1378058, by rfl⟩ : syracuseStep 1837411 = 2756117) B2756117
theorem B2754929 : Blo 1835619 2754929 := bstep (se 2 (by rfl) ⟨1033098, by rfl⟩ : syracuseStep 2754929 = 2066197) B2066197
theorem B1837427 : Blo 1835619 1837427 := bstep (se 1 (by rfl) ⟨1378070, by rfl⟩ : syracuseStep 1837427 = 2756141) B2756141
theorem B2754947 : Blo 1835619 2754947 := bstep (se 1 (by rfl) ⟨2066210, by rfl⟩ : syracuseStep 2754947 = 4132421) B4132421
theorem B1837443 : Blo 1835619 1837443 := bstep (se 1 (by rfl) ⟨1378082, by rfl⟩ : syracuseStep 1837443 = 2756165) B2756165
theorem B1837459 : Blo 1835619 1837459 := bstep (se 1 (by rfl) ⟨1378094, by rfl⟩ : syracuseStep 1837459 = 2756189) B2756189
theorem B2754977 : Blo 1835619 2754977 := bstep (se 2 (by rfl) ⟨1033116, by rfl⟩ : syracuseStep 2754977 = 2066233) B2066233
theorem B1837475 : Blo 1835619 1837475 := bstep (se 1 (by rfl) ⟨1378106, by rfl⟩ : syracuseStep 1837475 = 2756213) B2756213
theorem B20122037 : Blo 1835619 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B2754995 : Blo 1835619 2754995 := bstep (se 1 (by rfl) ⟨2066246, by rfl⟩ : syracuseStep 2754995 = 4132493) B4132493
theorem B1837491 : Blo 1835619 1837491 := bstep (se 1 (by rfl) ⟨1378118, by rfl⟩ : syracuseStep 1837491 = 2756237) B2756237
theorem B3099073 : Blo 1835619 3099073 := bstep (se 2 (by rfl) ⟨1162152, by rfl⟩ : syracuseStep 3099073 = 2324305) B2324305
theorem B1837507 : Blo 1835619 1837507 := bstep (se 1 (by rfl) ⟨1378130, by rfl⟩ : syracuseStep 1837507 = 2756261) B2756261
theorem B2755025 : Blo 1835619 2755025 := bstep (se 2 (by rfl) ⟨1033134, by rfl⟩ : syracuseStep 2755025 = 2066269) B2066269
theorem B2066899 : Blo 1835619 2066899 := bstep (se 1 (by rfl) ⟨1550174, by rfl⟩ : syracuseStep 2066899 = 3100349) B3100349
theorem B1837523 : Blo 1835619 1837523 := bstep (se 1 (by rfl) ⟨1378142, by rfl⟩ : syracuseStep 1837523 = 2756285) B2756285
theorem B4647395 : Blo 1835619 4647395 := bstep (se 1 (by rfl) ⟨3485546, by rfl⟩ : syracuseStep 4647395 = 6971093) B6971093
theorem B3099107 : Blo 1835619 3099107 := bstep (se 1 (by rfl) ⟨2324330, by rfl⟩ : syracuseStep 3099107 = 4648661) B4648661
theorem B2755043 : Blo 1835619 2755043 := bstep (se 1 (by rfl) ⟨2066282, by rfl⟩ : syracuseStep 2755043 = 4132565) B4132565
theorem B1837539 : Blo 1835619 1837539 := bstep (se 1 (by rfl) ⟨1378154, by rfl⟩ : syracuseStep 1837539 = 2756309) B2756309
theorem B13240817 : Blo 1835619 13240817 := bstep (se 2 (by rfl) ⟨4965306, by rfl⟩ : syracuseStep 13240817 = 9930613) B9930613
theorem B1837555 : Blo 1835619 1837555 := bstep (se 1 (by rfl) ⟨1378166, by rfl⟩ : syracuseStep 1837555 = 2756333) B2756333
theorem B2755073 : Blo 1835619 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B1837571 : Blo 1835619 1837571 := bstep (se 1 (by rfl) ⟨1378178, by rfl⟩ : syracuseStep 1837571 = 2756357) B2756357
theorem B9423373 : Blo 1835619 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B2755091 : Blo 1835619 2755091 := bstep (se 1 (by rfl) ⟨2066318, by rfl⟩ : syracuseStep 2755091 = 4132637) B4132637
theorem B1837587 : Blo 1835619 1837587 := bstep (se 1 (by rfl) ⟨1378190, by rfl⟩ : syracuseStep 1837587 = 2756381) B2756381
theorem B1837603 : Blo 1835619 1837603 := bstep (se 1 (by rfl) ⟨1378202, by rfl⟩ : syracuseStep 1837603 = 2756405) B2756405
theorem B4131377 : Blo 1835619 4131377 := bstep (se 2 (by rfl) ⟨1549266, by rfl⟩ : syracuseStep 4131377 = 3098533) B3098533
theorem B2755121 : Blo 1835619 2755121 := bstep (se 2 (by rfl) ⟨1033170, by rfl⟩ : syracuseStep 2755121 = 2066341) B2066341
theorem B1837619 : Blo 1835619 1837619 := bstep (se 1 (by rfl) ⟨1378214, by rfl⟩ : syracuseStep 1837619 = 2756429) B2756429
theorem B4131395 : Blo 1835619 4131395 := bstep (se 1 (by rfl) ⟨3098546, by rfl⟩ : syracuseStep 4131395 = 6197093) B6197093
theorem B2755139 : Blo 1835619 2755139 := bstep (se 1 (by rfl) ⟨2066354, by rfl⟩ : syracuseStep 2755139 = 4132709) B4132709
theorem B3975761 : Blo 1835619 3975761 := bstep (se 2 (by rfl) ⟨1490910, by rfl⟩ : syracuseStep 3975761 = 2981821) B2981821
theorem B2755169 : Blo 1835619 2755169 := bstep (se 2 (by rfl) ⟨1033188, by rfl⟩ : syracuseStep 2755169 = 2066377) B2066377
theorem B3099235 : Blo 1835619 3099235 := bstep (se 1 (by rfl) ⟨2324426, by rfl⟩ : syracuseStep 3099235 = 4648853) B4648853
theorem B2067043 : Blo 1835619 2067043 := bstep (se 1 (by rfl) ⟨1550282, by rfl⟩ : syracuseStep 2067043 = 3100565) B3100565
theorem B2755187 : Blo 1835619 2755187 := bstep (se 1 (by rfl) ⟨2066390, by rfl⟩ : syracuseStep 2755187 = 4132781) B4132781
theorem B2755217 : Blo 1835619 2755217 := bstep (se 2 (by rfl) ⟨1033206, by rfl⟩ : syracuseStep 2755217 = 2066413) B2066413
theorem B2755235 : Blo 1835619 2755235 := bstep (se 1 (by rfl) ⟨2066426, by rfl⟩ : syracuseStep 2755235 = 4132853) B4132853
theorem B2615971 : Blo 1835619 2615971 := bstep (se 1 (by rfl) ⟨1961978, by rfl⟩ : syracuseStep 2615971 = 3923957) B3923957
theorem B2755265 : Blo 1835619 2755265 := bstep (se 2 (by rfl) ⟨1033224, by rfl⟩ : syracuseStep 2755265 = 2066449) B2066449
theorem B5302979 : Blo 1835619 5302979 := bstep (se 1 (by rfl) ⟨3977234, by rfl⟩ : syracuseStep 5302979 = 7954469) B7954469
theorem B2755283 : Blo 1835619 2755283 := bstep (se 1 (by rfl) ⟨2066462, by rfl⟩ : syracuseStep 2755283 = 4132925) B4132925
theorem B3099377 : Blo 1835619 3099377 := bstep (se 2 (by rfl) ⟨1162266, by rfl⟩ : syracuseStep 3099377 = 2324533) B2324533
theorem B2755313 : Blo 1835619 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B2067187 : Blo 1835619 2067187 := bstep (se 1 (by rfl) ⟨1550390, by rfl⟩ : syracuseStep 2067187 = 3100781) B3100781
theorem B2755331 : Blo 1835619 2755331 := bstep (se 1 (by rfl) ⟨2066498, by rfl⟩ : syracuseStep 2755331 = 4132997) B4132997
theorem B6974221 : Blo 1835619 6974221 := bstep (se 3 (by rfl) ⟨1307666, by rfl⟩ : syracuseStep 6974221 = 2615333) B2615333
theorem B1960723 : Blo 1835619 1960723 := bstep (se 1 (by rfl) ⟨1470542, by rfl⟩ : syracuseStep 1960723 = 2941085) B2941085
theorem B2755361 : Blo 1835619 2755361 := bstep (se 2 (by rfl) ⟨1033260, by rfl⟩ : syracuseStep 2755361 = 2066521) B2066521
theorem B6196013 : Blo 1835619 6196013 := bstep (se 3 (by rfl) ⟨1161752, by rfl⟩ : syracuseStep 6196013 = 2323505) B2323505
theorem B2755379 : Blo 1835619 2755379 := bstep (se 1 (by rfl) ⟨2066534, by rfl⟩ : syracuseStep 2755379 = 4133069) B4133069
theorem B4131665 : Blo 1835619 4131665 := bstep (se 2 (by rfl) ⟨1549374, by rfl⟩ : syracuseStep 4131665 = 3098749) B3098749
theorem B2755409 : Blo 1835619 2755409 := bstep (se 2 (by rfl) ⟨1033278, by rfl⟩ : syracuseStep 2755409 = 2066557) B2066557
theorem B6196067 : Blo 1835619 6196067 := bstep (se 1 (by rfl) ⟨4647050, by rfl⟩ : syracuseStep 6196067 = 9294101) B9294101
theorem B4131683 : Blo 1835619 4131683 := bstep (se 1 (by rfl) ⟨3098762, by rfl⟩ : syracuseStep 4131683 = 6197525) B6197525
theorem B2755427 : Blo 1835619 2755427 := bstep (se 1 (by rfl) ⟨2066570, by rfl⟩ : syracuseStep 2755427 = 4133141) B4133141
theorem B3099505 : Blo 1835619 3099505 := bstep (se 2 (by rfl) ⟨1162314, by rfl⟩ : syracuseStep 3099505 = 2324629) B2324629
theorem B2755457 : Blo 1835619 2755457 := bstep (se 2 (by rfl) ⟨1033296, by rfl⟩ : syracuseStep 2755457 = 2066593) B2066593
theorem B3099539 : Blo 1835619 3099539 := bstep (se 1 (by rfl) ⟨2324654, by rfl⟩ : syracuseStep 3099539 = 4649309) B4649309
theorem B2755475 : Blo 1835619 2755475 := bstep (se 1 (by rfl) ⟨2066606, by rfl⟩ : syracuseStep 2755475 = 4133213) B4133213
theorem B2755505 : Blo 1835619 2755505 := bstep (se 2 (by rfl) ⟨1033314, by rfl⟩ : syracuseStep 2755505 = 2066629) B2066629
theorem B2755523 : Blo 1835619 2755523 := bstep (se 1 (by rfl) ⟨2066642, by rfl⟩ : syracuseStep 2755523 = 4133285) B4133285
theorem B2755553 : Blo 1835619 2755553 := bstep (se 2 (by rfl) ⟨1033332, by rfl⟩ : syracuseStep 2755553 = 2066665) B2066665
theorem B10464227 : Blo 1835619 10464227 := bstep (se 1 (by rfl) ⟨7848170, by rfl⟩ : syracuseStep 10464227 = 15696341) B15696341
theorem B2755571 : Blo 1835619 2755571 := bstep (se 1 (by rfl) ⟨2066678, by rfl⟩ : syracuseStep 2755571 = 4133357) B4133357
theorem B4779011 : Blo 1835619 4779011 := bstep (se 1 (by rfl) ⟨3584258, by rfl⟩ : syracuseStep 4779011 = 7168517) B7168517
theorem B2755601 : Blo 1835619 2755601 := bstep (se 2 (by rfl) ⟨1033350, by rfl⟩ : syracuseStep 2755601 = 2066701) B2066701
theorem B3099667 : Blo 1835619 3099667 := bstep (se 1 (by rfl) ⟨2324750, by rfl⟩ : syracuseStep 3099667 = 4649501) B4649501
theorem B2755619 : Blo 1835619 2755619 := bstep (se 1 (by rfl) ⟨2066714, by rfl⟩ : syracuseStep 2755619 = 4133429) B4133429
theorem B8375345 : Blo 1835619 8375345 := bstep (se 2 (by rfl) ⟨3140754, by rfl⟩ : syracuseStep 8375345 = 6281509) B6281509
theorem B2755649 : Blo 1835619 2755649 := bstep (se 2 (by rfl) ⟨1033368, by rfl⟩ : syracuseStep 2755649 = 2066737) B2066737
theorem B2755667 : Blo 1835619 2755667 := bstep (se 1 (by rfl) ⟨2066750, by rfl⟩ : syracuseStep 2755667 = 4133501) B4133501
theorem B6196337 : Blo 1835619 6196337 := bstep (se 2 (by rfl) ⟨2323626, by rfl⟩ : syracuseStep 6196337 = 4647253) B4647253
theorem B4131953 : Blo 1835619 4131953 := bstep (se 2 (by rfl) ⟨1549482, by rfl⟩ : syracuseStep 4131953 = 3098965) B3098965
theorem B2755697 : Blo 1835619 2755697 := bstep (se 2 (by rfl) ⟨1033386, by rfl⟩ : syracuseStep 2755697 = 2066773) B2066773
theorem B4131971 : Blo 1835619 4131971 := bstep (se 1 (by rfl) ⟨3098978, by rfl⟩ : syracuseStep 4131971 = 6197957) B6197957
theorem B2755715 : Blo 1835619 2755715 := bstep (se 1 (by rfl) ⟨2066786, by rfl⟩ : syracuseStep 2755715 = 4133573) B4133573
theorem B28273805 : Blo 1835619 28273805 := bstep (se 3 (by rfl) ⟨5301338, by rfl⟩ : syracuseStep 28273805 = 10602677) B10602677
theorem B3099809 : Blo 1835619 3099809 := bstep (se 2 (by rfl) ⟨1162428, by rfl⟩ : syracuseStep 3099809 = 2324857) B2324857
theorem B2755745 : Blo 1835619 2755745 := bstep (se 2 (by rfl) ⟨1033404, by rfl⟩ : syracuseStep 2755745 = 2066809) B2066809
theorem B2755763 : Blo 1835619 2755763 := bstep (se 1 (by rfl) ⟨2066822, by rfl⟩ : syracuseStep 2755763 = 4133645) B4133645
theorem B2755793 : Blo 1835619 2755793 := bstep (se 2 (by rfl) ⟨1033422, by rfl⟩ : syracuseStep 2755793 = 2066845) B2066845
theorem B2755811 : Blo 1835619 2755811 := bstep (se 1 (by rfl) ⟨2066858, by rfl⟩ : syracuseStep 2755811 = 4133717) B4133717
theorem B2755841 : Blo 1835619 2755841 := bstep (se 2 (by rfl) ⟨1033440, by rfl⟩ : syracuseStep 2755841 = 2066881) B2066881
theorem B2755859 : Blo 1835619 2755859 := bstep (se 1 (by rfl) ⟨2066894, by rfl⟩ : syracuseStep 2755859 = 4133789) B4133789
theorem B3099937 : Blo 1835619 3099937 := bstep (se 2 (by rfl) ⟨1162476, by rfl⟩ : syracuseStep 3099937 = 2324953) B2324953
theorem B2755889 : Blo 1835619 2755889 := bstep (se 2 (by rfl) ⟨1033458, by rfl⟩ : syracuseStep 2755889 = 2066917) B2066917
theorem B3099971 : Blo 1835619 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B2755907 : Blo 1835619 2755907 := bstep (se 1 (by rfl) ⟨2066930, by rfl⟩ : syracuseStep 2755907 = 4133861) B4133861
theorem B2755937 : Blo 1835619 2755937 := bstep (se 2 (by rfl) ⟨1033476, by rfl⟩ : syracuseStep 2755937 = 2066953) B2066953
theorem B5229937 : Blo 1835619 5229937 := bstep (se 2 (by rfl) ⟨1961226, by rfl⟩ : syracuseStep 5229937 = 3922453) B3922453
theorem B4189553 : Blo 1835619 4189553 := bstep (se 2 (by rfl) ⟨1571082, by rfl⟩ : syracuseStep 4189553 = 3142165) B3142165
theorem B2755955 : Blo 1835619 2755955 := bstep (se 1 (by rfl) ⟨2066966, by rfl⟩ : syracuseStep 2755955 = 4133933) B4133933
theorem B4189571 : Blo 1835619 4189571 := bstep (se 1 (by rfl) ⟨3142178, by rfl⟩ : syracuseStep 4189571 = 6284357) B6284357
theorem B4648337 : Blo 1835619 4648337 := bstep (se 2 (by rfl) ⟨1743126, by rfl⟩ : syracuseStep 4648337 = 3486253) B3486253
theorem B4132241 : Blo 1835619 4132241 := bstep (se 2 (by rfl) ⟨1549590, by rfl⟩ : syracuseStep 4132241 = 3099181) B3099181
theorem B2755985 : Blo 1835619 2755985 := bstep (se 2 (by rfl) ⟨1033494, by rfl⟩ : syracuseStep 2755985 = 2066989) B2066989
theorem B4132259 : Blo 1835619 4132259 := bstep (se 1 (by rfl) ⟨3099194, by rfl⟩ : syracuseStep 4132259 = 6198389) B6198389
theorem B2756003 : Blo 1835619 2756003 := bstep (se 1 (by rfl) ⟨2067002, by rfl⟩ : syracuseStep 2756003 = 4134005) B4134005
theorem B2756033 : Blo 1835619 2756033 := bstep (se 2 (by rfl) ⟨1033512, by rfl⟩ : syracuseStep 2756033 = 2067025) B2067025
theorem B4648387 : Blo 1835619 4648387 := bstep (se 1 (by rfl) ⟨3486290, by rfl⟩ : syracuseStep 4648387 = 6972581) B6972581
theorem B3100099 : Blo 1835619 3100099 := bstep (se 1 (by rfl) ⟨2325074, by rfl⟩ : syracuseStep 3100099 = 4650149) B4650149
theorem B4713923 : Blo 1835619 4713923 := bstep (se 1 (by rfl) ⟨3535442, by rfl⟩ : syracuseStep 4713923 = 7070885) B7070885
theorem B2756051 : Blo 1835619 2756051 := bstep (se 1 (by rfl) ⟨2067038, by rfl⟩ : syracuseStep 2756051 = 4134077) B4134077
theorem B2756081 : Blo 1835619 2756081 := bstep (se 2 (by rfl) ⟨1033530, by rfl⟩ : syracuseStep 2756081 = 2067061) B2067061
theorem B2756099 : Blo 1835619 2756099 := bstep (se 1 (by rfl) ⟨2067074, by rfl⟩ : syracuseStep 2756099 = 4134149) B4134149
theorem B6975011 : Blo 1835619 6975011 := bstep (se 1 (by rfl) ⟨5231258, by rfl⟩ : syracuseStep 6975011 = 10462517) B10462517
theorem B2756129 : Blo 1835619 2756129 := bstep (se 2 (by rfl) ⟨1033548, by rfl⟩ : syracuseStep 2756129 = 2067097) B2067097
theorem B9301553 : Blo 1835619 9301553 := bstep (se 2 (by rfl) ⟨3488082, by rfl⟩ : syracuseStep 9301553 = 6976165) B6976165
theorem B2756147 : Blo 1835619 2756147 := bstep (se 1 (by rfl) ⟨2067110, by rfl⟩ : syracuseStep 2756147 = 4134221) B4134221
theorem B4648529 : Blo 1835619 4648529 := bstep (se 2 (by rfl) ⟨1743198, by rfl⟩ : syracuseStep 4648529 = 3486397) B3486397
theorem B3100241 : Blo 1835619 3100241 := bstep (se 2 (by rfl) ⟨1162590, by rfl⟩ : syracuseStep 3100241 = 2325181) B2325181
theorem B2756177 : Blo 1835619 2756177 := bstep (se 2 (by rfl) ⟨1033566, by rfl⟩ : syracuseStep 2756177 = 2067133) B2067133
theorem B2756195 : Blo 1835619 2756195 := bstep (se 1 (by rfl) ⟨2067146, by rfl⟩ : syracuseStep 2756195 = 4134293) B4134293
theorem B3141233 : Blo 1835619 3141233 := bstep (se 2 (by rfl) ⟨1177962, by rfl⟩ : syracuseStep 3141233 = 2355925) B2355925
theorem B2756225 : Blo 1835619 2756225 := bstep (se 2 (by rfl) ⟨1033584, by rfl⟩ : syracuseStep 2756225 = 2067169) B2067169
theorem B11169413 : Blo 1835619 11169413 := bstep (se 4 (by rfl) ⟨1047132, by rfl⟩ : syracuseStep 11169413 = 2094265) B2094265
theorem B9293453 : Blo 1835619 9293453 := bstep (se 3 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 9293453 = 3485045) B3485045
theorem B6196877 : Blo 1835619 6196877 := bstep (se 3 (by rfl) ⟨1161914, by rfl⟩ : syracuseStep 6196877 = 2323829) B2323829
theorem B2756243 : Blo 1835619 2756243 := bstep (se 1 (by rfl) ⟨2067182, by rfl⟩ : syracuseStep 2756243 = 4134365) B4134365
theorem B7065251 : Blo 1835619 7065251 := bstep (se 1 (by rfl) ⟨5298938, by rfl⟩ : syracuseStep 7065251 = 10597877) B10597877
theorem B4132529 : Blo 1835619 4132529 := bstep (se 2 (by rfl) ⟨1549698, by rfl⟩ : syracuseStep 4132529 = 3099397) B3099397
theorem B2756273 : Blo 1835619 2756273 := bstep (se 2 (by rfl) ⟨1033602, by rfl⟩ : syracuseStep 2756273 = 2067205) B2067205
theorem B6196931 : Blo 1835619 6196931 := bstep (se 1 (by rfl) ⟨4647698, by rfl⟩ : syracuseStep 6196931 = 9295397) B9295397
theorem B4132547 : Blo 1835619 4132547 := bstep (se 1 (by rfl) ⟨3099410, by rfl⟩ : syracuseStep 4132547 = 6198821) B6198821
theorem B2756291 : Blo 1835619 2756291 := bstep (se 1 (by rfl) ⟨2067218, by rfl⟩ : syracuseStep 2756291 = 4134437) B4134437
theorem B3100369 : Blo 1835619 3100369 := bstep (se 2 (by rfl) ⟨1162638, by rfl⟩ : syracuseStep 3100369 = 2325277) B2325277
theorem B2756321 : Blo 1835619 2756321 := bstep (se 2 (by rfl) ⟨1033620, by rfl⟩ : syracuseStep 2756321 = 2067241) B2067241
theorem B3485425 : Blo 1835619 3485425 := bstep (se 2 (by rfl) ⟨1307034, by rfl⟩ : syracuseStep 3485425 = 2614069) B2614069
theorem B3100403 : Blo 1835619 3100403 := bstep (se 1 (by rfl) ⟨2325302, by rfl⟩ : syracuseStep 3100403 = 4650605) B4650605
theorem B2756339 : Blo 1835619 2756339 := bstep (se 1 (by rfl) ⟨2067254, by rfl⟩ : syracuseStep 2756339 = 4134509) B4134509
theorem B2297603 : Blo 1835619 2297603 := bstep (se 1 (by rfl) ⟨1723202, by rfl⟩ : syracuseStep 2297603 = 3446405) B3446405
theorem B2756369 : Blo 1835619 2756369 := bstep (se 2 (by rfl) ⟨1033638, by rfl⟩ : syracuseStep 2756369 = 2067277) B2067277
theorem B12570403 : Blo 1835619 12570403 := bstep (se 1 (by rfl) ⟨9427802, by rfl⟩ : syracuseStep 12570403 = 18855605) B18855605
theorem B2756387 : Blo 1835619 2756387 := bstep (se 1 (by rfl) ⟨2067290, by rfl⟩ : syracuseStep 2756387 = 4134581) B4134581
theorem B5304113 : Blo 1835619 5304113 := bstep (se 2 (by rfl) ⟨1989042, by rfl⟩ : syracuseStep 5304113 = 3978085) B3978085
theorem B2756417 : Blo 1835619 2756417 := bstep (se 2 (by rfl) ⟨1033656, by rfl⟩ : syracuseStep 2756417 = 2067313) B2067313
theorem B15691589 : Blo 1835619 15691589 := bstep (se 4 (by rfl) ⟨1471086, by rfl⟩ : syracuseStep 15691589 = 2942173) B2942173
theorem B7843661 : Blo 1835619 7843661 := bstep (se 3 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 7843661 = 2941373) B2941373
theorem B3100531 : Blo 1835619 3100531 := bstep (se 1 (by rfl) ⟨2325398, by rfl⟩ : syracuseStep 3100531 = 4650797) B4650797
theorem B3485585 : Blo 1835619 3485585 := bstep (se 2 (by rfl) ⟨1307094, by rfl⟩ : syracuseStep 3485585 = 2614189) B2614189
theorem B6197201 : Blo 1835619 6197201 := bstep (se 2 (by rfl) ⟨2323950, by rfl⟩ : syracuseStep 6197201 = 4647901) B4647901
theorem B4132817 : Blo 1835619 4132817 := bstep (se 2 (by rfl) ⟨1549806, by rfl⟩ : syracuseStep 4132817 = 3099613) B3099613
theorem B4132835 : Blo 1835619 4132835 := bstep (se 1 (by rfl) ⟨3099626, by rfl⟩ : syracuseStep 4132835 = 6199253) B6199253
theorem B3100673 : Blo 1835619 3100673 := bstep (se 2 (by rfl) ⟨1162752, by rfl⟩ : syracuseStep 3100673 = 2325505) B2325505
theorem B1961987 : Blo 1835619 1961987 := bstep (se 1 (by rfl) ⟨1471490, by rfl⟩ : syracuseStep 1961987 = 2942981) B2942981
theorem B3100801 : Blo 1835619 3100801 := bstep (se 2 (by rfl) ⟨1162800, by rfl⟩ : syracuseStep 3100801 = 2325601) B2325601
theorem B3100835 : Blo 1835619 3100835 := bstep (se 1 (by rfl) ⟨2325626, by rfl⟩ : syracuseStep 3100835 = 4651253) B4651253
theorem B6975665 : Blo 1835619 6975665 := bstep (se 2 (by rfl) ⟨2615874, by rfl⟩ : syracuseStep 6975665 = 5231749) B5231749
theorem B7065805 : Blo 1835619 7065805 := bstep (se 3 (by rfl) ⟨1324838, by rfl⟩ : syracuseStep 7065805 = 2649677) B2649677
theorem B4714723 : Blo 1835619 4714723 := bstep (se 1 (by rfl) ⟨3536042, by rfl⟩ : syracuseStep 4714723 = 7072085) B7072085
theorem B4133105 : Blo 1835619 4133105 := bstep (se 2 (by rfl) ⟨1549914, by rfl⟩ : syracuseStep 4133105 = 3099829) B3099829
theorem B4133123 : Blo 1835619 4133123 := bstep (se 1 (by rfl) ⟨3099842, by rfl⟩ : syracuseStep 4133123 = 6199685) B6199685
theorem B23546609 : Blo 1835619 23546609 := bstep (se 2 (by rfl) ⟨8829978, by rfl⟩ : syracuseStep 23546609 = 17659957) B17659957
theorem B3485987 : Blo 1835619 3485987 := bstep (se 1 (by rfl) ⟨2614490, by rfl⟩ : syracuseStep 3485987 = 5228981) B5228981
theorem B3100963 : Blo 1835619 3100963 := bstep (se 1 (by rfl) ⟨2325722, by rfl⟩ : syracuseStep 3100963 = 4651445) B4651445
theorem B5886371 : Blo 1835619 5886371 := bstep (se 1 (by rfl) ⟨4414778, by rfl⟩ : syracuseStep 5886371 = 8829557) B8829557
theorem B6197741 : Blo 1835619 6197741 := bstep (se 3 (by rfl) ⟨1162076, by rfl⟩ : syracuseStep 6197741 = 2324153) B2324153
theorem B4133393 : Blo 1835619 4133393 := bstep (se 2 (by rfl) ⟨1550022, by rfl⟩ : syracuseStep 4133393 = 3100045) B3100045
theorem B6197795 : Blo 1835619 6197795 := bstep (se 1 (by rfl) ⟨4648346, by rfl⟩ : syracuseStep 6197795 = 9296693) B9296693
theorem B4133411 : Blo 1835619 4133411 := bstep (se 1 (by rfl) ⟨3100058, by rfl⟩ : syracuseStep 4133411 = 6200117) B6200117
theorem B4649521 : Blo 1835619 4649521 := bstep (se 2 (by rfl) ⟨1743570, by rfl⟩ : syracuseStep 4649521 = 3487141) B3487141
theorem B5231213 : Blo 1835619 5231213 := bstep (se 3 (by rfl) ⟨980852, by rfl⟩ : syracuseStep 5231213 = 1961705) B1961705
theorem B9925253 : Blo 1835619 9925253 := bstep (se 4 (by rfl) ⟨930492, by rfl⟩ : syracuseStep 9925253 = 1860985) B1860985
theorem B10457869 : Blo 1835619 10457869 := bstep (se 3 (by rfl) ⟨1960850, by rfl⟩ : syracuseStep 10457869 = 3921701) B3921701
theorem B5231395 : Blo 1835619 5231395 := bstep (se 1 (by rfl) ⟨3923546, by rfl⟩ : syracuseStep 5231395 = 7847093) B7847093
theorem B6198065 : Blo 1835619 6198065 := bstep (se 2 (by rfl) ⟨2324274, by rfl⟩ : syracuseStep 6198065 = 4648549) B4648549
theorem B4133681 : Blo 1835619 4133681 := bstep (se 2 (by rfl) ⟨1550130, by rfl⟩ : syracuseStep 4133681 = 3100261) B3100261
theorem B4649795 : Blo 1835619 4649795 := bstep (se 1 (by rfl) ⟨3487346, by rfl⟩ : syracuseStep 4649795 = 6974693) B6974693
theorem B4133699 : Blo 1835619 4133699 := bstep (se 1 (by rfl) ⟨3100274, by rfl⟩ : syracuseStep 4133699 = 6200549) B6200549
theorem B5231441 : Blo 1835619 5231441 := bstep (se 2 (by rfl) ⟨1961790, by rfl⟩ : syracuseStep 5231441 = 3923581) B3923581
theorem B6706061 : Blo 1835619 6706061 := bstep (se 3 (by rfl) ⟨1257386, by rfl⟩ : syracuseStep 6706061 = 2514773) B2514773
theorem B3142547 : Blo 1835619 3142547 := bstep (se 1 (by rfl) ⟨2356910, by rfl⟩ : syracuseStep 3142547 = 4713821) B4713821
theorem B8827811 : Blo 1835619 8827811 := bstep (se 1 (by rfl) ⟨6620858, by rfl⟩ : syracuseStep 8827811 = 13241717) B13241717
theorem B3920881 : Blo 1835619 3920881 := bstep (se 2 (by rfl) ⟨1470330, by rfl⟩ : syracuseStep 3920881 = 2940661) B2940661
theorem B6280195 : Blo 1835619 6280195 := bstep (se 1 (by rfl) ⟨4710146, by rfl⟩ : syracuseStep 6280195 = 9420293) B9420293
theorem B3920899 : Blo 1835619 3920899 := bstep (se 1 (by rfl) ⟨2940674, by rfl⟩ : syracuseStep 3920899 = 5881349) B5881349
theorem B4649987 : Blo 1835619 4649987 := bstep (se 1 (by rfl) ⟨3487490, by rfl⟩ : syracuseStep 4649987 = 6974981) B6974981
theorem B5583953 : Blo 1835619 5583953 := bstep (se 2 (by rfl) ⟨2093982, by rfl⟩ : syracuseStep 5583953 = 4187965) B4187965
theorem B4133969 : Blo 1835619 4133969 := bstep (se 2 (by rfl) ⟨1550238, by rfl⟩ : syracuseStep 4133969 = 3100477) B3100477
theorem B4133987 : Blo 1835619 4133987 := bstep (se 1 (by rfl) ⟨3100490, by rfl⟩ : syracuseStep 4133987 = 6200981) B6200981
theorem B23524465 : Blo 1835619 23524465 := bstep (se 2 (by rfl) ⟨8821674, by rfl⟩ : syracuseStep 23524465 = 17643349) B17643349
theorem B36254861 : Blo 1835619 36254861 := bstep (se 3 (by rfl) ⟨6797786, by rfl⟩ : syracuseStep 36254861 = 13595573) B13595573
theorem B3486883 : Blo 1835619 3486883 := bstep (se 1 (by rfl) ⟨2615162, by rfl⟩ : syracuseStep 3486883 = 5230325) B5230325
theorem B2094275 : Blo 1835619 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B2323667 : Blo 1835619 2323667 := bstep (se 1 (by rfl) ⟨1742750, by rfl⟩ : syracuseStep 2323667 = 3485501) B3485501
theorem B71562467 : Blo 1835619 71562467 := bstep (se 1 (by rfl) ⟨53671850, by rfl⟩ : syracuseStep 71562467 = 107343701) B107343701
theorem B3487043 : Blo 1835619 3487043 := bstep (se 1 (by rfl) ⟨2615282, by rfl⟩ : syracuseStep 3487043 = 5230565) B5230565
theorem B6198605 : Blo 1835619 6198605 := bstep (se 3 (by rfl) ⟨1162238, by rfl⟩ : syracuseStep 6198605 = 2324477) B2324477
theorem B4134257 : Blo 1835619 4134257 := bstep (se 2 (by rfl) ⟨1550346, by rfl⟩ : syracuseStep 4134257 = 3100693) B3100693
theorem B6198659 : Blo 1835619 6198659 := bstep (se 1 (by rfl) ⟨4648994, by rfl⟩ : syracuseStep 6198659 = 9297989) B9297989
theorem B4134275 : Blo 1835619 4134275 := bstep (se 1 (by rfl) ⟨3100706, by rfl⟩ : syracuseStep 4134275 = 6201413) B6201413
theorem B25138613 : Blo 1835619 25138613 := bstep (se 5 (by rfl) ⟨1178372, by rfl⟩ : syracuseStep 25138613 = 2356745) B2356745
theorem B47068613 : Blo 1835619 47068613 := bstep (se 4 (by rfl) ⟨4412682, by rfl⟩ : syracuseStep 47068613 = 8825365) B8825365
theorem B8828365 : Blo 1835619 8828365 := bstep (se 3 (by rfl) ⟨1655318, by rfl⟩ : syracuseStep 8828365 = 3310637) B3310637
theorem B11924977 : Blo 1835619 11924977 := bstep (se 2 (by rfl) ⟨4471866, by rfl⟩ : syracuseStep 11924977 = 8943733) B8943733
theorem B7444067 : Blo 1835619 7444067 := bstep (se 1 (by rfl) ⟨5583050, by rfl⟩ : syracuseStep 7444067 = 11166101) B11166101
theorem B6977123 : Blo 1835619 6977123 := bstep (se 1 (by rfl) ⟨5232842, by rfl⟩ : syracuseStep 6977123 = 10465685) B10465685
theorem B6977137 : Blo 1835619 6977137 := bstep (se 2 (by rfl) ⟨2616426, by rfl⟩ : syracuseStep 6977137 = 5232853) B5232853
theorem B4413059 : Blo 1835619 4413059 := bstep (se 1 (by rfl) ⟨3309794, by rfl⟩ : syracuseStep 4413059 = 6619589) B6619589
theorem B6198929 : Blo 1835619 6198929 := bstep (se 2 (by rfl) ⟨2324598, by rfl⟩ : syracuseStep 6198929 = 4649197) B4649197
theorem B4134545 : Blo 1835619 4134545 := bstep (se 2 (by rfl) ⟨1550454, by rfl⟩ : syracuseStep 4134545 = 3100909) B3100909
theorem B4134563 : Blo 1835619 4134563 := bstep (se 1 (by rfl) ⟨3100922, by rfl⟩ : syracuseStep 4134563 = 6201845) B6201845
theorem B8492813 : Blo 1835619 8492813 := bstep (se 3 (by rfl) ⟨1592402, by rfl⟩ : syracuseStep 8492813 = 3184805) B3184805
theorem B13948685 : Blo 1835619 13948685 := bstep (se 3 (by rfl) ⟨2615378, by rfl⟩ : syracuseStep 13948685 = 5230757) B5230757
theorem B18143075 : Blo 1835619 18143075 := bstep (se 1 (by rfl) ⟨13607306, by rfl⟩ : syracuseStep 18143075 = 27214613) B27214613
theorem B2324371 : Blo 1835619 2324371 := bstep (se 1 (by rfl) ⟨1743278, by rfl⟩ : syracuseStep 2324371 = 3486557) B3486557
theorem B4650929 : Blo 1835619 4650929 := bstep (se 2 (by rfl) ⟨1744098, by rfl⟩ : syracuseStep 4650929 = 3488197) B3488197
theorem B4650979 : Blo 1835619 4650979 := bstep (se 1 (by rfl) ⟨3488234, by rfl⟩ : syracuseStep 4650979 = 6976469) B6976469
theorem B2324467 : Blo 1835619 2324467 := bstep (se 1 (by rfl) ⟨1743350, by rfl⟩ : syracuseStep 2324467 = 3486701) B3486701
theorem B6617123 : Blo 1835619 6617123 := bstep (se 1 (by rfl) ⟨4962842, by rfl⟩ : syracuseStep 6617123 = 9925685) B9925685
theorem B6281261 : Blo 1835619 6281261 := bstep (se 3 (by rfl) ⟨1177736, by rfl⟩ : syracuseStep 6281261 = 2355473) B2355473
theorem B4413521 : Blo 1835619 4413521 := bstep (se 2 (by rfl) ⟨1655070, by rfl⟩ : syracuseStep 4413521 = 3310141) B3310141
theorem B4651121 : Blo 1835619 4651121 := bstep (se 2 (by rfl) ⟨1744170, by rfl⟩ : syracuseStep 4651121 = 3488341) B3488341
theorem B6199469 : Blo 1835619 6199469 := bstep (se 3 (by rfl) ⟨1162400, by rfl⟩ : syracuseStep 6199469 = 2324801) B2324801
theorem B6199523 : Blo 1835619 6199523 := bstep (se 1 (by rfl) ⟨4649642, by rfl⟩ : syracuseStep 6199523 = 9299285) B9299285
theorem B5232899 : Blo 1835619 5232899 := bstep (se 1 (by rfl) ⟨3924674, by rfl⟩ : syracuseStep 5232899 = 7849349) B7849349
theorem B6969635 : Blo 1835619 6969635 := bstep (se 1 (by rfl) ⟨5227226, by rfl⟩ : syracuseStep 6969635 = 10454453) B10454453
theorem B3488113 : Blo 1835619 3488113 := bstep (se 2 (by rfl) ⟨1308042, by rfl⟩ : syracuseStep 3488113 = 2616085) B2616085
theorem B95451533 : Blo 1835619 95451533 := bstep (se 3 (by rfl) ⟨17897162, by rfl⟩ : syracuseStep 95451533 = 35794325) B35794325
theorem B2324963 : Blo 1835619 2324963 := bstep (se 1 (by rfl) ⟨1743722, by rfl⟩ : syracuseStep 2324963 = 3487445) B3487445
theorem B9296369 : Blo 1835619 9296369 := bstep (se 2 (by rfl) ⟨3486138, by rfl⟩ : syracuseStep 9296369 = 6972277) B6972277
theorem B6199793 : Blo 1835619 6199793 := bstep (se 2 (by rfl) ⟨2324922, by rfl⟩ : syracuseStep 6199793 = 4649845) B4649845
theorem B19847693 : Blo 1835619 19847693 := bstep (se 3 (by rfl) ⟨3721442, by rfl⟩ : syracuseStep 19847693 = 7442885) B7442885
theorem B15686257 : Blo 1835619 15686257 := bstep (se 2 (by rfl) ⟨5882346, by rfl⟩ : syracuseStep 15686257 = 11764693) B11764693
theorem B91798129 : Blo 1835619 91798129 := bstep (se 2 (by rfl) ⟨34424298, by rfl⟩ : syracuseStep 91798129 = 68848597) B68848597
theorem B4962961 : Blo 1835619 4962961 := bstep (se 2 (by rfl) ⟨1861110, by rfl⟩ : syracuseStep 4962961 = 3722221) B3722221
theorem B10459853 : Blo 1835619 10459853 := bstep (se 3 (by rfl) ⟨1961222, by rfl⟩ : syracuseStep 10459853 = 3922445) B3922445
theorem B2685793 : Blo 1835619 2685793 := bstep (se 2 (by rfl) ⟨1007172, by rfl⟩ : syracuseStep 2685793 = 2014345) B2014345
theorem B8829809 : Blo 1835619 8829809 := bstep (se 2 (by rfl) ⟨3311178, by rfl⟩ : syracuseStep 8829809 = 6622357) B6622357
theorem B35306381 : Blo 1835619 35306381 := bstep (se 3 (by rfl) ⟨6619946, by rfl⟩ : syracuseStep 35306381 = 13239893) B13239893
theorem B6200333 : Blo 1835619 6200333 := bstep (se 3 (by rfl) ⟨1162562, by rfl⟩ : syracuseStep 6200333 = 2325125) B2325125
theorem B20929589 : Blo 1835619 20929589 := bstep (se 5 (by rfl) ⟨981074, by rfl⟩ : syracuseStep 20929589 = 1962149) B1962149
theorem B6200387 : Blo 1835619 6200387 := bstep (se 1 (by rfl) ⟨4650290, by rfl⟩ : syracuseStep 6200387 = 9300581) B9300581
theorem B2325667 : Blo 1835619 2325667 := bstep (se 1 (by rfl) ⟨1744250, by rfl⟩ : syracuseStep 2325667 = 3488501) B3488501
theorem B7552205 : Blo 1835619 7552205 := bstep (se 3 (by rfl) ⟨1416038, by rfl⟩ : syracuseStep 7552205 = 2832077) B2832077
theorem B3923171 : Blo 1835619 3923171 := bstep (se 1 (by rfl) ⟨2942378, by rfl⟩ : syracuseStep 3923171 = 5884757) B5884757
theorem B6970637 : Blo 1835619 6970637 := bstep (se 3 (by rfl) ⟨1306994, by rfl⟩ : syracuseStep 6970637 = 2613989) B2613989
theorem B2792755 : Blo 1835619 2792755 := bstep (se 1 (by rfl) ⟨2094566, by rfl⟩ : syracuseStep 2792755 = 4189133) B4189133
theorem B6200657 : Blo 1835619 6200657 := bstep (se 2 (by rfl) ⟨2325246, by rfl⟩ : syracuseStep 6200657 = 4650493) B4650493
theorem B3186049 : Blo 1835619 3186049 := bstep (se 2 (by rfl) ⟨1194768, by rfl⟩ : syracuseStep 3186049 = 2389537) B2389537
theorem B9420401 : Blo 1835619 9420401 := bstep (se 2 (by rfl) ⟨3532650, by rfl⟩ : syracuseStep 9420401 = 7065301) B7065301
theorem B10460785 : Blo 1835619 10460785 := bstep (se 2 (by rfl) ⟨3922794, by rfl⟩ : syracuseStep 10460785 = 7845589) B7845589
theorem B3923633 : Blo 1835619 3923633 := bstep (se 2 (by rfl) ⟨1471362, by rfl⟩ : syracuseStep 3923633 = 2942725) B2942725
theorem B5586641 : Blo 1835619 5586641 := bstep (se 2 (by rfl) ⟨2094990, by rfl⟩ : syracuseStep 5586641 = 4189981) B4189981
theorem B2940707 : Blo 1835619 2940707 := bstep (se 1 (by rfl) ⟨2205530, by rfl⟩ : syracuseStep 2940707 = 4411061) B4411061
theorem B5447459 : Blo 1835619 5447459 := bstep (se 1 (by rfl) ⟨4085594, by rfl⟩ : syracuseStep 5447459 = 8171189) B8171189
theorem B4964141 : Blo 1835619 4964141 := bstep (se 3 (by rfl) ⟨930776, by rfl⟩ : syracuseStep 4964141 = 1861553) B1861553
theorem B2981681 : Blo 1835619 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B6201197 : Blo 1835619 6201197 := bstep (se 3 (by rfl) ⟨1162724, by rfl⟩ : syracuseStep 6201197 = 2325449) B2325449
theorem B9297827 : Blo 1835619 9297827 := bstep (se 1 (by rfl) ⟨6973370, by rfl⟩ : syracuseStep 9297827 = 13946741) B13946741
theorem B6201251 : Blo 1835619 6201251 := bstep (se 1 (by rfl) ⟨4650938, by rfl⟩ : syracuseStep 6201251 = 9301877) B9301877
theorem B5586995 : Blo 1835619 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B6971609 : Blo 1835619 6971609 := bstep (se 2 (by rfl) ⟨2614353, by rfl⟩ : syracuseStep 6971609 = 5228707) B5228707
theorem B9421073 : Blo 1835619 9421073 := bstep (se 2 (by rfl) ⟨3532902, by rfl⟩ : syracuseStep 9421073 = 7065805) B7065805
theorem B4964701 : Blo 1835619 4964701 := bstep (se 3 (by rfl) ⟨930881, by rfl⟩ : syracuseStep 4964701 = 1861763) B1861763
theorem B7848323 : Blo 1835619 7848323 := bstep (se 1 (by rfl) ⟨5886242, by rfl⟩ : syracuseStep 7848323 = 11772485) B11772485
theorem B13238801 : Blo 1835619 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B3310105 : Blo 1835619 3310105 := bstep (se 2 (by rfl) ⟨1241289, by rfl⟩ : syracuseStep 3310105 = 2482579) B2482579
theorem B1835627 : Blo 1835619 1835627 := bstep (se 1 (by rfl) ⟨1376720, by rfl⟩ : syracuseStep 1835627 = 2753441) B2753441
theorem B1835639 : Blo 1835619 1835639 := bstep (se 1 (by rfl) ⟨1376729, by rfl⟩ : syracuseStep 1835639 = 2753459) B2753459
theorem B47055491 : Blo 1835619 47055491 := bstep (se 1 (by rfl) ⟨35291618, by rfl⟩ : syracuseStep 47055491 = 70583237) B70583237
theorem B1835659 : Blo 1835619 1835659 := bstep (se 1 (by rfl) ⟨1376744, by rfl⟩ : syracuseStep 1835659 = 2753489) B2753489
theorem B1835671 : Blo 1835619 1835671 := bstep (se 1 (by rfl) ⟨1376753, by rfl⟩ : syracuseStep 1835671 = 2753507) B2753507
theorem B1835691 : Blo 1835619 1835691 := bstep (se 1 (by rfl) ⟨1376768, by rfl⟩ : syracuseStep 1835691 = 2753537) B2753537
theorem B1835703 : Blo 1835619 1835703 := bstep (se 1 (by rfl) ⟨1376777, by rfl⟩ : syracuseStep 1835703 = 2753555) B2753555
theorem B2065099 : Blo 1835619 2065099 := bstep (se 1 (by rfl) ⟨1548824, by rfl⟩ : syracuseStep 2065099 = 3097649) B3097649
theorem B1835723 : Blo 1835619 1835723 := bstep (se 1 (by rfl) ⟨1376792, by rfl⟩ : syracuseStep 1835723 = 2753585) B2753585
theorem B1835735 : Blo 1835619 1835735 := bstep (se 1 (by rfl) ⟨1376801, by rfl⟩ : syracuseStep 1835735 = 2753603) B2753603
theorem B1835755 : Blo 1835619 1835755 := bstep (se 1 (by rfl) ⟨1376816, by rfl⟩ : syracuseStep 1835755 = 2753633) B2753633
theorem B1835767 : Blo 1835619 1835767 := bstep (se 1 (by rfl) ⟨1376825, by rfl⟩ : syracuseStep 1835767 = 2753651) B2753651
theorem B26469125 : Blo 1835619 26469125 := bstep (se 4 (by rfl) ⟨2481480, by rfl⟩ : syracuseStep 26469125 = 4962961) B4962961
theorem B1835787 : Blo 1835619 1835787 := bstep (se 1 (by rfl) ⟨1376840, by rfl⟩ : syracuseStep 1835787 = 2753681) B2753681
theorem B1835799 : Blo 1835619 1835799 := bstep (se 1 (by rfl) ⟨1376849, by rfl⟩ : syracuseStep 1835799 = 2753699) B2753699
theorem B1835819 : Blo 1835619 1835819 := bstep (se 1 (by rfl) ⟨1376864, by rfl⟩ : syracuseStep 1835819 = 2753729) B2753729
theorem B2065207 : Blo 1835619 2065207 := bstep (se 1 (by rfl) ⟨1548905, by rfl⟩ : syracuseStep 2065207 = 3097811) B3097811
theorem B1835831 : Blo 1835619 1835831 := bstep (se 1 (by rfl) ⟨1376873, by rfl⟩ : syracuseStep 1835831 = 2753747) B2753747
theorem B20915009 : Blo 1835619 20915009 := bstep (se 2 (by rfl) ⟨7843128, by rfl⟩ : syracuseStep 20915009 = 15686257) B15686257
theorem B1835851 : Blo 1835619 1835851 := bstep (se 1 (by rfl) ⟨1376888, by rfl⟩ : syracuseStep 1835851 = 2753777) B2753777
theorem B1835863 : Blo 1835619 1835863 := bstep (se 1 (by rfl) ⟨1376897, by rfl⟩ : syracuseStep 1835863 = 2753795) B2753795
theorem B1835883 : Blo 1835619 1835883 := bstep (se 1 (by rfl) ⟨1376912, by rfl⟩ : syracuseStep 1835883 = 2753825) B2753825
theorem B1835895 : Blo 1835619 1835895 := bstep (se 1 (by rfl) ⟨1376921, by rfl⟩ : syracuseStep 1835895 = 2753843) B2753843
theorem B1835915 : Blo 1835619 1835915 := bstep (se 1 (by rfl) ⟨1376936, by rfl⟩ : syracuseStep 1835915 = 2753873) B2753873
theorem B1835927 : Blo 1835619 1835927 := bstep (se 1 (by rfl) ⟨1376945, by rfl⟩ : syracuseStep 1835927 = 2753891) B2753891
theorem B1835947 : Blo 1835619 1835947 := bstep (se 1 (by rfl) ⟨1376960, by rfl⟩ : syracuseStep 1835947 = 2753921) B2753921
theorem B21201841 : Blo 1835619 21201841 := bstep (se 2 (by rfl) ⟨7950690, by rfl⟩ : syracuseStep 21201841 = 15901381) B15901381
theorem B8061875 : Blo 1835619 8061875 := bstep (se 1 (by rfl) ⟨6046406, by rfl⟩ : syracuseStep 8061875 = 12092813) B12092813
theorem B1835959 : Blo 1835619 1835959 := bstep (se 1 (by rfl) ⟨1376969, by rfl⟩ : syracuseStep 1835959 = 2753939) B2753939
theorem B2753483 : Blo 1835619 2753483 := bstep (se 1 (by rfl) ⟨2065112, by rfl⟩ : syracuseStep 2753483 = 4130225) B4130225
theorem B1835979 : Blo 1835619 1835979 := bstep (se 1 (by rfl) ⟨1376984, by rfl⟩ : syracuseStep 1835979 = 2753969) B2753969
theorem B2753495 : Blo 1835619 2753495 := bstep (se 1 (by rfl) ⟨2065121, by rfl⟩ : syracuseStep 2753495 = 4130243) B4130243
theorem B1835991 : Blo 1835619 1835991 := bstep (se 1 (by rfl) ⟨1376993, by rfl⟩ : syracuseStep 1835991 = 2753987) B2753987
theorem B2065387 : Blo 1835619 2065387 := bstep (se 1 (by rfl) ⟨1549040, by rfl⟩ : syracuseStep 2065387 = 3098081) B3098081
theorem B1836011 : Blo 1835619 1836011 := bstep (se 1 (by rfl) ⟨1377008, by rfl⟩ : syracuseStep 1836011 = 2754017) B2754017
theorem B1836023 : Blo 1835619 1836023 := bstep (se 1 (by rfl) ⟨1377017, by rfl⟩ : syracuseStep 1836023 = 2754035) B2754035
theorem B1836043 : Blo 1835619 1836043 := bstep (se 1 (by rfl) ⟨1377032, by rfl⟩ : syracuseStep 1836043 = 2754065) B2754065
theorem B13943825 : Blo 1835619 13943825 := bstep (se 2 (by rfl) ⟨5228934, by rfl⟩ : syracuseStep 13943825 = 10457869) B10457869
theorem B9298961 : Blo 1835619 9298961 := bstep (se 2 (by rfl) ⟨3487110, by rfl⟩ : syracuseStep 9298961 = 6974221) B6974221
theorem B1836055 : Blo 1835619 1836055 := bstep (se 1 (by rfl) ⟨1377041, by rfl⟩ : syracuseStep 1836055 = 2754083) B2754083
theorem B2753561 : Blo 1835619 2753561 := bstep (se 2 (by rfl) ⟨1032585, by rfl⟩ : syracuseStep 2753561 = 2065171) B2065171
theorem B2614297 : Blo 1835619 2614297 := bstep (se 2 (by rfl) ⟨980361, by rfl⟩ : syracuseStep 2614297 = 1960723) B1960723
theorem B1836075 : Blo 1835619 1836075 := bstep (se 1 (by rfl) ⟨1377056, by rfl⟩ : syracuseStep 1836075 = 2754113) B2754113
theorem B1836087 : Blo 1835619 1836087 := bstep (se 1 (by rfl) ⟨1377065, by rfl⟩ : syracuseStep 1836087 = 2754131) B2754131
theorem B1836107 : Blo 1835619 1836107 := bstep (se 1 (by rfl) ⟨1377080, by rfl⟩ : syracuseStep 1836107 = 2754161) B2754161
theorem B2065495 : Blo 1835619 2065495 := bstep (se 1 (by rfl) ⟨1549121, by rfl⟩ : syracuseStep 2065495 = 3098243) B3098243
theorem B1836119 : Blo 1835619 1836119 := bstep (se 1 (by rfl) ⟨1377089, by rfl⟩ : syracuseStep 1836119 = 2754179) B2754179
theorem B2942039 : Blo 1835619 2942039 := bstep (se 1 (by rfl) ⟨2206529, by rfl⟩ : syracuseStep 2942039 = 4413059) B4413059
theorem B15696989 : Blo 1835619 15696989 := bstep (se 3 (by rfl) ⟨2943185, by rfl⟩ : syracuseStep 15696989 = 5886371) B5886371
theorem B1836139 : Blo 1835619 1836139 := bstep (se 1 (by rfl) ⟨1377104, by rfl⟩ : syracuseStep 1836139 = 2754209) B2754209
theorem B1836151 : Blo 1835619 1836151 := bstep (se 1 (by rfl) ⟨1377113, by rfl⟩ : syracuseStep 1836151 = 2754227) B2754227
theorem B3581057 : Blo 1835619 3581057 := bstep (se 2 (by rfl) ⟨1342896, by rfl⟩ : syracuseStep 3581057 = 2685793) B2685793
theorem B2753675 : Blo 1835619 2753675 := bstep (se 1 (by rfl) ⟨2065256, by rfl⟩ : syracuseStep 2753675 = 4130513) B4130513
theorem B1836171 : Blo 1835619 1836171 := bstep (se 1 (by rfl) ⟨1377128, by rfl⟩ : syracuseStep 1836171 = 2754257) B2754257
theorem B67036301 : Blo 1835619 67036301 := bstep (se 3 (by rfl) ⟨12569306, by rfl⟩ : syracuseStep 67036301 = 25138613) B25138613
theorem B2753687 : Blo 1835619 2753687 := bstep (se 1 (by rfl) ⟨2065265, by rfl⟩ : syracuseStep 2753687 = 4130531) B4130531
theorem B1836183 : Blo 1835619 1836183 := bstep (se 1 (by rfl) ⟨1377137, by rfl⟩ : syracuseStep 1836183 = 2754275) B2754275
theorem B1836203 : Blo 1835619 1836203 := bstep (se 1 (by rfl) ⟨1377152, by rfl⟩ : syracuseStep 1836203 = 2754305) B2754305
theorem B5661875 : Blo 1835619 5661875 := bstep (se 1 (by rfl) ⟨4246406, by rfl⟩ : syracuseStep 5661875 = 8492813) B8492813
theorem B9299123 : Blo 1835619 9299123 := bstep (se 1 (by rfl) ⟨6974342, by rfl⟩ : syracuseStep 9299123 = 13948685) B13948685
theorem B1836215 : Blo 1835619 1836215 := bstep (se 1 (by rfl) ⟨1377161, by rfl⟩ : syracuseStep 1836215 = 2754323) B2754323
theorem B1836235 : Blo 1835619 1836235 := bstep (se 1 (by rfl) ⟨1377176, by rfl⟩ : syracuseStep 1836235 = 2754353) B2754353
theorem B1836247 : Blo 1835619 1836247 := bstep (se 1 (by rfl) ⟨1377185, by rfl⟩ : syracuseStep 1836247 = 2754371) B2754371
theorem B2753753 : Blo 1835619 2753753 := bstep (se 2 (by rfl) ⟨1032657, by rfl⟩ : syracuseStep 2753753 = 2065315) B2065315
theorem B1836267 : Blo 1835619 1836267 := bstep (se 1 (by rfl) ⟨1377200, by rfl⟩ : syracuseStep 1836267 = 2754401) B2754401
theorem B1836279 : Blo 1835619 1836279 := bstep (se 1 (by rfl) ⟨1377209, by rfl⟩ : syracuseStep 1836279 = 2754419) B2754419
theorem B2065675 : Blo 1835619 2065675 := bstep (se 1 (by rfl) ⟨1549256, by rfl⟩ : syracuseStep 2065675 = 3098513) B3098513
theorem B1836299 : Blo 1835619 1836299 := bstep (se 1 (by rfl) ⟨1377224, by rfl⟩ : syracuseStep 1836299 = 2754449) B2754449
theorem B1836311 : Blo 1835619 1836311 := bstep (se 1 (by rfl) ⟨1377233, by rfl⟩ : syracuseStep 1836311 = 2754467) B2754467
theorem B1836331 : Blo 1835619 1836331 := bstep (se 1 (by rfl) ⟨1377248, by rfl⟩ : syracuseStep 1836331 = 2754497) B2754497
theorem B1836343 : Blo 1835619 1836343 := bstep (se 1 (by rfl) ⟨1377257, by rfl⟩ : syracuseStep 1836343 = 2754515) B2754515
theorem B5227841 : Blo 1835619 5227841 := bstep (se 2 (by rfl) ⟨1960440, by rfl⟩ : syracuseStep 5227841 = 3920881) B3920881
theorem B2753867 : Blo 1835619 2753867 := bstep (se 1 (by rfl) ⟨2065400, by rfl⟩ : syracuseStep 2753867 = 4130801) B4130801
theorem B1836363 : Blo 1835619 1836363 := bstep (se 1 (by rfl) ⟨1377272, by rfl⟩ : syracuseStep 1836363 = 2754545) B2754545
theorem B2753879 : Blo 1835619 2753879 := bstep (se 1 (by rfl) ⟨2065409, by rfl⟩ : syracuseStep 2753879 = 4130819) B4130819
theorem B1836375 : Blo 1835619 1836375 := bstep (se 1 (by rfl) ⟨1377281, by rfl⟩ : syracuseStep 1836375 = 2754563) B2754563
theorem B8373593 : Blo 1835619 8373593 := bstep (se 2 (by rfl) ⟨3140097, by rfl⟩ : syracuseStep 8373593 = 6280195) B6280195
theorem B5227865 : Blo 1835619 5227865 := bstep (se 2 (by rfl) ⟨1960449, by rfl⟩ : syracuseStep 5227865 = 3920899) B3920899
theorem B1836395 : Blo 1835619 1836395 := bstep (se 1 (by rfl) ⟨1377296, by rfl⟩ : syracuseStep 1836395 = 2754593) B2754593
theorem B4187507 : Blo 1835619 4187507 := bstep (se 1 (by rfl) ⟨3140630, by rfl⟩ : syracuseStep 4187507 = 6281261) B6281261
theorem B2065783 : Blo 1835619 2065783 := bstep (se 1 (by rfl) ⟨1549337, by rfl⟩ : syracuseStep 2065783 = 3098675) B3098675
theorem B1836407 : Blo 1835619 1836407 := bstep (se 1 (by rfl) ⟨1377305, by rfl⟩ : syracuseStep 1836407 = 2754611) B2754611
theorem B26477941 : Blo 1835619 26477941 := bstep (se 5 (by rfl) ⟨1241153, by rfl⟩ : syracuseStep 26477941 = 2482307) B2482307
theorem B1836427 : Blo 1835619 1836427 := bstep (se 1 (by rfl) ⟨1377320, by rfl⟩ : syracuseStep 1836427 = 2754641) B2754641
theorem B2942347 : Blo 1835619 2942347 := bstep (se 1 (by rfl) ⟨2206760, by rfl⟩ : syracuseStep 2942347 = 4413521) B4413521
theorem B1836439 : Blo 1835619 1836439 := bstep (se 1 (by rfl) ⟨1377329, by rfl⟩ : syracuseStep 1836439 = 2754659) B2754659
theorem B2753945 : Blo 1835619 2753945 := bstep (se 2 (by rfl) ⟨1032729, by rfl⟩ : syracuseStep 2753945 = 2065459) B2065459
theorem B1836459 : Blo 1835619 1836459 := bstep (se 1 (by rfl) ⟨1377344, by rfl⟩ : syracuseStep 1836459 = 2754689) B2754689
theorem B1836471 : Blo 1835619 1836471 := bstep (se 1 (by rfl) ⟨1377353, by rfl⟩ : syracuseStep 1836471 = 2754707) B2754707
theorem B1836491 : Blo 1835619 1836491 := bstep (se 1 (by rfl) ⟨1377368, by rfl⟩ : syracuseStep 1836491 = 2754737) B2754737
theorem B1836503 : Blo 1835619 1836503 := bstep (se 1 (by rfl) ⟨1377377, by rfl⟩ : syracuseStep 1836503 = 2754755) B2754755
theorem B1836523 : Blo 1835619 1836523 := bstep (se 1 (by rfl) ⟨1377392, by rfl⟩ : syracuseStep 1836523 = 2754785) B2754785
theorem B1836535 : Blo 1835619 1836535 := bstep (se 1 (by rfl) ⟨1377401, by rfl⟩ : syracuseStep 1836535 = 2754803) B2754803
theorem B4130315 : Blo 1835619 4130315 := bstep (se 1 (by rfl) ⟨3097736, by rfl⟩ : syracuseStep 4130315 = 6195473) B6195473
theorem B2754059 : Blo 1835619 2754059 := bstep (se 1 (by rfl) ⟨2065544, by rfl⟩ : syracuseStep 2754059 = 4131089) B4131089
theorem B1836555 : Blo 1835619 1836555 := bstep (se 1 (by rfl) ⟨1377416, by rfl⟩ : syracuseStep 1836555 = 2754833) B2754833
theorem B4646423 : Blo 1835619 4646423 := bstep (se 1 (by rfl) ⟨3484817, by rfl⟩ : syracuseStep 4646423 = 6969635) B6969635
theorem B3098135 : Blo 1835619 3098135 := bstep (se 1 (by rfl) ⟨2323601, by rfl⟩ : syracuseStep 3098135 = 4647203) B4647203
theorem B2754071 : Blo 1835619 2754071 := bstep (se 1 (by rfl) ⟨2065553, by rfl⟩ : syracuseStep 2754071 = 4131107) B4131107
theorem B1836567 : Blo 1835619 1836567 := bstep (se 1 (by rfl) ⟨1377425, by rfl⟩ : syracuseStep 1836567 = 2754851) B2754851
theorem B2065963 : Blo 1835619 2065963 := bstep (se 1 (by rfl) ⟨1549472, by rfl⟩ : syracuseStep 2065963 = 3098945) B3098945
theorem B10602029 : Blo 1835619 10602029 := bstep (se 3 (by rfl) ⟨1987880, by rfl⟩ : syracuseStep 10602029 = 3975761) B3975761
theorem B1836587 : Blo 1835619 1836587 := bstep (se 1 (by rfl) ⟨1377440, by rfl⟩ : syracuseStep 1836587 = 2754881) B2754881
theorem B1836599 : Blo 1835619 1836599 := bstep (se 1 (by rfl) ⟨1377449, by rfl⟩ : syracuseStep 1836599 = 2754899) B2754899
theorem B4130369 : Blo 1835619 4130369 := bstep (se 2 (by rfl) ⟨1548888, by rfl⟩ : syracuseStep 4130369 = 3097777) B3097777
theorem B1836619 : Blo 1835619 1836619 := bstep (se 1 (by rfl) ⟨1377464, by rfl⟩ : syracuseStep 1836619 = 2754929) B2754929
theorem B1836631 : Blo 1835619 1836631 := bstep (se 1 (by rfl) ⟨1377473, by rfl⟩ : syracuseStep 1836631 = 2754947) B2754947
theorem B2754137 : Blo 1835619 2754137 := bstep (se 2 (by rfl) ⟨1032801, by rfl⟩ : syracuseStep 2754137 = 2065603) B2065603
theorem B19850845 : Blo 1835619 19850845 := bstep (se 3 (by rfl) ⟨3722033, by rfl⟩ : syracuseStep 19850845 = 7444067) B7444067
theorem B1836651 : Blo 1835619 1836651 := bstep (se 1 (by rfl) ⟨1377488, by rfl⟩ : syracuseStep 1836651 = 2754977) B2754977
theorem B1836663 : Blo 1835619 1836663 := bstep (se 1 (by rfl) ⟨1377497, by rfl⟩ : syracuseStep 1836663 = 2754995) B2754995
theorem B1836683 : Blo 1835619 1836683 := bstep (se 1 (by rfl) ⟨1377512, by rfl⟩ : syracuseStep 1836683 = 2755025) B2755025
theorem B3098263 : Blo 1835619 3098263 := bstep (se 1 (by rfl) ⟨2323697, by rfl⟩ : syracuseStep 3098263 = 4647395) B4647395
theorem B2066071 : Blo 1835619 2066071 := bstep (se 1 (by rfl) ⟨1549553, by rfl⟩ : syracuseStep 2066071 = 3099107) B3099107
theorem B1836695 : Blo 1835619 1836695 := bstep (se 1 (by rfl) ⟨1377521, by rfl⟩ : syracuseStep 1836695 = 2755043) B2755043
theorem B1836715 : Blo 1835619 1836715 := bstep (se 1 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 1836715 = 2755073) B2755073
theorem B13231795 : Blo 1835619 13231795 := bstep (se 1 (by rfl) ⟨9923846, by rfl⟩ : syracuseStep 13231795 = 19847693) B19847693
theorem B1836727 : Blo 1835619 1836727 := bstep (se 1 (by rfl) ⟨1377545, by rfl⟩ : syracuseStep 1836727 = 2755091) B2755091
theorem B2754251 : Blo 1835619 2754251 := bstep (se 1 (by rfl) ⟨2065688, by rfl⟩ : syracuseStep 2754251 = 4131377) B4131377
theorem B1836747 : Blo 1835619 1836747 := bstep (se 1 (by rfl) ⟨1377560, by rfl⟩ : syracuseStep 1836747 = 2755121) B2755121
theorem B2754263 : Blo 1835619 2754263 := bstep (se 1 (by rfl) ⟨2065697, by rfl⟩ : syracuseStep 2754263 = 4131395) B4131395
theorem B1836759 : Blo 1835619 1836759 := bstep (se 1 (by rfl) ⟨1377569, by rfl⟩ : syracuseStep 1836759 = 2755139) B2755139
theorem B1836779 : Blo 1835619 1836779 := bstep (se 1 (by rfl) ⟨1377584, by rfl⟩ : syracuseStep 1836779 = 2755169) B2755169
theorem B1836791 : Blo 1835619 1836791 := bstep (se 1 (by rfl) ⟨1377593, by rfl⟩ : syracuseStep 1836791 = 2755187) B2755187
theorem B1836811 : Blo 1835619 1836811 := bstep (se 1 (by rfl) ⟨1377608, by rfl⟩ : syracuseStep 1836811 = 2755217) B2755217
theorem B1836823 : Blo 1835619 1836823 := bstep (se 1 (by rfl) ⟨1377617, by rfl⟩ : syracuseStep 1836823 = 2755235) B2755235
theorem B4130585 : Blo 1835619 4130585 := bstep (se 2 (by rfl) ⟨1548969, by rfl⟩ : syracuseStep 4130585 = 3097939) B3097939
theorem B2754329 : Blo 1835619 2754329 := bstep (se 2 (by rfl) ⟨1032873, by rfl⟩ : syracuseStep 2754329 = 2065747) B2065747
theorem B1836843 : Blo 1835619 1836843 := bstep (se 1 (by rfl) ⟨1377632, by rfl⟩ : syracuseStep 1836843 = 2755265) B2755265
theorem B6973235 : Blo 1835619 6973235 := bstep (se 1 (by rfl) ⟨5229926, by rfl⟩ : syracuseStep 6973235 = 10459853) B10459853
theorem B1836855 : Blo 1835619 1836855 := bstep (se 1 (by rfl) ⟨1377641, by rfl⟩ : syracuseStep 1836855 = 2755283) B2755283
theorem B6973249 : Blo 1835619 6973249 := bstep (se 2 (by rfl) ⟨2614968, by rfl⟩ : syracuseStep 6973249 = 5229937) B5229937
theorem B2066251 : Blo 1835619 2066251 := bstep (se 1 (by rfl) ⟨1549688, by rfl⟩ : syracuseStep 2066251 = 3099377) B3099377
theorem B1836875 : Blo 1835619 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B15697739 : Blo 1835619 15697739 := bstep (se 1 (by rfl) ⟨11773304, by rfl⟩ : syracuseStep 15697739 = 23546609) B23546609
theorem B1836887 : Blo 1835619 1836887 := bstep (se 1 (by rfl) ⟨1377665, by rfl⟩ : syracuseStep 1836887 = 2755331) B2755331
theorem B1836907 : Blo 1835619 1836907 := bstep (se 1 (by rfl) ⟨1377680, by rfl⟩ : syracuseStep 1836907 = 2755361) B2755361
theorem B4130675 : Blo 1835619 4130675 := bstep (se 1 (by rfl) ⟨3098006, by rfl⟩ : syracuseStep 4130675 = 6196013) B6196013
theorem B1836919 : Blo 1835619 1836919 := bstep (se 1 (by rfl) ⟨1377689, by rfl⟩ : syracuseStep 1836919 = 2755379) B2755379
theorem B2754443 : Blo 1835619 2754443 := bstep (se 1 (by rfl) ⟨2065832, by rfl⟩ : syracuseStep 2754443 = 4131665) B4131665
theorem B1836939 : Blo 1835619 1836939 := bstep (se 1 (by rfl) ⟨1377704, by rfl⟩ : syracuseStep 1836939 = 2755409) B2755409
theorem B4130711 : Blo 1835619 4130711 := bstep (se 1 (by rfl) ⟨3098033, by rfl⟩ : syracuseStep 4130711 = 6196067) B6196067
theorem B2754455 : Blo 1835619 2754455 := bstep (se 1 (by rfl) ⟨2065841, by rfl⟩ : syracuseStep 2754455 = 4131683) B4131683
theorem B1836951 : Blo 1835619 1836951 := bstep (se 1 (by rfl) ⟨1377713, by rfl⟩ : syracuseStep 1836951 = 2755427) B2755427
theorem B1836971 : Blo 1835619 1836971 := bstep (se 1 (by rfl) ⟨1377728, by rfl⟩ : syracuseStep 1836971 = 2755457) B2755457
theorem B23537587 : Blo 1835619 23537587 := bstep (se 1 (by rfl) ⟨17653190, by rfl⟩ : syracuseStep 23537587 = 35306381) B35306381
theorem B2066359 : Blo 1835619 2066359 := bstep (se 1 (by rfl) ⟨1549769, by rfl⟩ : syracuseStep 2066359 = 3099539) B3099539
theorem B1836983 : Blo 1835619 1836983 := bstep (se 1 (by rfl) ⟨1377737, by rfl⟩ : syracuseStep 1836983 = 2755475) B2755475
theorem B1837003 : Blo 1835619 1837003 := bstep (se 1 (by rfl) ⟨1377752, by rfl⟩ : syracuseStep 1837003 = 2755505) B2755505
theorem B1837015 : Blo 1835619 1837015 := bstep (se 1 (by rfl) ⟨1377761, by rfl⟩ : syracuseStep 1837015 = 2755523) B2755523
theorem B2754521 : Blo 1835619 2754521 := bstep (se 2 (by rfl) ⟨1032945, by rfl⟩ : syracuseStep 2754521 = 2065891) B2065891
theorem B1837035 : Blo 1835619 1837035 := bstep (se 1 (by rfl) ⟨1377776, by rfl⟩ : syracuseStep 1837035 = 2755553) B2755553
theorem B1837047 : Blo 1835619 1837047 := bstep (se 1 (by rfl) ⟨1377785, by rfl⟩ : syracuseStep 1837047 = 2755571) B2755571
theorem B1837067 : Blo 1835619 1837067 := bstep (se 1 (by rfl) ⟨1377800, by rfl⟩ : syracuseStep 1837067 = 2755601) B2755601
theorem B1837079 : Blo 1835619 1837079 := bstep (se 1 (by rfl) ⟨1377809, by rfl⟩ : syracuseStep 1837079 = 2755619) B2755619
theorem B13953059 : Blo 1835619 13953059 := bstep (se 1 (by rfl) ⟨10464794, by rfl⟩ : syracuseStep 13953059 = 20929589) B20929589
theorem B1837099 : Blo 1835619 1837099 := bstep (se 1 (by rfl) ⟨1377824, by rfl⟩ : syracuseStep 1837099 = 2755649) B2755649
theorem B1837111 : Blo 1835619 1837111 := bstep (se 1 (by rfl) ⟨1377833, by rfl⟩ : syracuseStep 1837111 = 2755667) B2755667
theorem B4130891 : Blo 1835619 4130891 := bstep (se 1 (by rfl) ⟨3098168, by rfl⟩ : syracuseStep 4130891 = 6196337) B6196337
theorem B2754635 : Blo 1835619 2754635 := bstep (se 1 (by rfl) ⟨2065976, by rfl⟩ : syracuseStep 2754635 = 4131953) B4131953
theorem B1837131 : Blo 1835619 1837131 := bstep (se 1 (by rfl) ⟨1377848, by rfl⟩ : syracuseStep 1837131 = 2755697) B2755697
theorem B2754647 : Blo 1835619 2754647 := bstep (se 1 (by rfl) ⟨2065985, by rfl⟩ : syracuseStep 2754647 = 4131971) B4131971
theorem B1837143 : Blo 1835619 1837143 := bstep (se 1 (by rfl) ⟨1377857, by rfl⟩ : syracuseStep 1837143 = 2755715) B2755715
theorem B2066539 : Blo 1835619 2066539 := bstep (se 1 (by rfl) ⟨1549904, by rfl⟩ : syracuseStep 2066539 = 3099809) B3099809
theorem B1837163 : Blo 1835619 1837163 := bstep (se 1 (by rfl) ⟨1377872, by rfl⟩ : syracuseStep 1837163 = 2755745) B2755745
theorem B1837175 : Blo 1835619 1837175 := bstep (se 1 (by rfl) ⟨1377881, by rfl⟩ : syracuseStep 1837175 = 2755763) B2755763
theorem B4130945 : Blo 1835619 4130945 := bstep (se 2 (by rfl) ⟨1549104, by rfl⟩ : syracuseStep 4130945 = 3098209) B3098209
theorem B1837195 : Blo 1835619 1837195 := bstep (se 1 (by rfl) ⟨1377896, by rfl⟩ : syracuseStep 1837195 = 2755793) B2755793
theorem B2615447 : Blo 1835619 2615447 := bstep (se 1 (by rfl) ⟨1961585, by rfl⟩ : syracuseStep 2615447 = 3923171) B3923171
theorem B1837207 : Blo 1835619 1837207 := bstep (se 1 (by rfl) ⟨1377905, by rfl⟩ : syracuseStep 1837207 = 2755811) B2755811
theorem B2754713 : Blo 1835619 2754713 := bstep (se 2 (by rfl) ⟨1033017, by rfl⟩ : syracuseStep 2754713 = 2066035) B2066035
theorem B1837227 : Blo 1835619 1837227 := bstep (se 1 (by rfl) ⟨1377920, by rfl⟩ : syracuseStep 1837227 = 2755841) B2755841
theorem B4647091 : Blo 1835619 4647091 := bstep (se 1 (by rfl) ⟨3485318, by rfl⟩ : syracuseStep 4647091 = 6970637) B6970637
theorem B1837239 : Blo 1835619 1837239 := bstep (se 1 (by rfl) ⟨1377929, by rfl⟩ : syracuseStep 1837239 = 2755859) B2755859
theorem B1837259 : Blo 1835619 1837259 := bstep (se 1 (by rfl) ⟨1377944, by rfl⟩ : syracuseStep 1837259 = 2755889) B2755889
theorem B2066647 : Blo 1835619 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B1837271 : Blo 1835619 1837271 := bstep (se 1 (by rfl) ⟨1377953, by rfl⟩ : syracuseStep 1837271 = 2755907) B2755907
theorem B1837291 : Blo 1835619 1837291 := bstep (se 1 (by rfl) ⟨1377968, by rfl⟩ : syracuseStep 1837291 = 2755937) B2755937
theorem B1837303 : Blo 1835619 1837303 := bstep (se 1 (by rfl) ⟨1377977, by rfl⟩ : syracuseStep 1837303 = 2755955) B2755955
theorem B3098891 : Blo 1835619 3098891 := bstep (se 1 (by rfl) ⟨2324168, by rfl⟩ : syracuseStep 3098891 = 4648337) B4648337
theorem B2754827 : Blo 1835619 2754827 := bstep (se 1 (by rfl) ⟨2066120, by rfl⟩ : syracuseStep 2754827 = 4132241) B4132241
theorem B1837323 : Blo 1835619 1837323 := bstep (se 1 (by rfl) ⟨1377992, by rfl⟩ : syracuseStep 1837323 = 2755985) B2755985
theorem B2754839 : Blo 1835619 2754839 := bstep (se 1 (by rfl) ⟨2066129, by rfl⟩ : syracuseStep 2754839 = 4132259) B4132259
theorem B1837335 : Blo 1835619 1837335 := bstep (se 1 (by rfl) ⟨1378001, by rfl⟩ : syracuseStep 1837335 = 2756003) B2756003
theorem B1837355 : Blo 1835619 1837355 := bstep (se 1 (by rfl) ⟨1378016, by rfl⟩ : syracuseStep 1837355 = 2756033) B2756033
theorem B1837367 : Blo 1835619 1837367 := bstep (se 1 (by rfl) ⟨1378025, by rfl⟩ : syracuseStep 1837367 = 2756051) B2756051
theorem B4647233 : Blo 1835619 4647233 := bstep (se 2 (by rfl) ⟨1742712, by rfl⟩ : syracuseStep 4647233 = 3485425) B3485425
theorem B1837387 : Blo 1835619 1837387 := bstep (se 1 (by rfl) ⟨1378040, by rfl⟩ : syracuseStep 1837387 = 2756081) B2756081
theorem B1837399 : Blo 1835619 1837399 := bstep (se 1 (by rfl) ⟨1378049, by rfl⟩ : syracuseStep 1837399 = 2756099) B2756099
theorem B4131161 : Blo 1835619 4131161 := bstep (se 2 (by rfl) ⟨1549185, by rfl⟩ : syracuseStep 4131161 = 3098371) B3098371
theorem B2754905 : Blo 1835619 2754905 := bstep (se 2 (by rfl) ⟨1033089, by rfl⟩ : syracuseStep 2754905 = 2066179) B2066179
theorem B1837419 : Blo 1835619 1837419 := bstep (se 1 (by rfl) ⟨1378064, by rfl⟩ : syracuseStep 1837419 = 2756129) B2756129
theorem B1837431 : Blo 1835619 1837431 := bstep (se 1 (by rfl) ⟨1378073, by rfl⟩ : syracuseStep 1837431 = 2756147) B2756147
theorem B3099019 : Blo 1835619 3099019 := bstep (se 1 (by rfl) ⟨2324264, by rfl⟩ : syracuseStep 3099019 = 4648529) B4648529
theorem B2066827 : Blo 1835619 2066827 := bstep (se 1 (by rfl) ⟨1550120, by rfl⟩ : syracuseStep 2066827 = 3100241) B3100241
theorem B1837451 : Blo 1835619 1837451 := bstep (se 1 (by rfl) ⟨1378088, by rfl⟩ : syracuseStep 1837451 = 2756177) B2756177
theorem B1837463 : Blo 1835619 1837463 := bstep (se 1 (by rfl) ⟨1378097, by rfl⟩ : syracuseStep 1837463 = 2756195) B2756195
theorem B1837483 : Blo 1835619 1837483 := bstep (se 1 (by rfl) ⟨1378112, by rfl⟩ : syracuseStep 1837483 = 2756225) B2756225
theorem B6195635 : Blo 1835619 6195635 := bstep (se 1 (by rfl) ⟨4646726, by rfl⟩ : syracuseStep 6195635 = 9293453) B9293453
theorem B4131251 : Blo 1835619 4131251 := bstep (se 1 (by rfl) ⟨3098438, by rfl⟩ : syracuseStep 4131251 = 6196877) B6196877
theorem B1837495 : Blo 1835619 1837495 := bstep (se 1 (by rfl) ⟨1378121, by rfl⟩ : syracuseStep 1837495 = 2756243) B2756243
theorem B2755019 : Blo 1835619 2755019 := bstep (se 1 (by rfl) ⟨2066264, by rfl⟩ : syracuseStep 2755019 = 4132529) B4132529
theorem B2615755 : Blo 1835619 2615755 := bstep (se 1 (by rfl) ⟨1961816, by rfl⟩ : syracuseStep 2615755 = 3923633) B3923633
theorem B1837515 : Blo 1835619 1837515 := bstep (se 1 (by rfl) ⟨1378136, by rfl⟩ : syracuseStep 1837515 = 2756273) B2756273
theorem B4131287 : Blo 1835619 4131287 := bstep (se 1 (by rfl) ⟨3098465, by rfl⟩ : syracuseStep 4131287 = 6196931) B6196931
theorem B2755031 : Blo 1835619 2755031 := bstep (se 1 (by rfl) ⟨2066273, by rfl⟩ : syracuseStep 2755031 = 4132547) B4132547
theorem B1837527 : Blo 1835619 1837527 := bstep (se 1 (by rfl) ⟨1378145, by rfl⟩ : syracuseStep 1837527 = 2756291) B2756291
theorem B1837547 : Blo 1835619 1837547 := bstep (se 1 (by rfl) ⟨1378160, by rfl⟩ : syracuseStep 1837547 = 2756321) B2756321
theorem B2066935 : Blo 1835619 2066935 := bstep (se 1 (by rfl) ⟨1550201, by rfl⟩ : syracuseStep 2066935 = 3100403) B3100403
theorem B1837559 : Blo 1835619 1837559 := bstep (se 1 (by rfl) ⟨1378169, by rfl⟩ : syracuseStep 1837559 = 2756339) B2756339
theorem B1837579 : Blo 1835619 1837579 := bstep (se 1 (by rfl) ⟨1378184, by rfl⟩ : syracuseStep 1837579 = 2756369) B2756369
theorem B1960471 : Blo 1835619 1960471 := bstep (se 1 (by rfl) ⟨1470353, by rfl⟩ : syracuseStep 1960471 = 2940707) B2940707
theorem B3631639 : Blo 1835619 3631639 := bstep (se 1 (by rfl) ⟨2723729, by rfl⟩ : syracuseStep 3631639 = 5447459) B5447459
theorem B3099161 : Blo 1835619 3099161 := bstep (se 2 (by rfl) ⟨1162185, by rfl⟩ : syracuseStep 3099161 = 2324371) B2324371
theorem B2755097 : Blo 1835619 2755097 := bstep (se 2 (by rfl) ⟨1033161, by rfl⟩ : syracuseStep 2755097 = 2066323) B2066323
theorem B1837591 : Blo 1835619 1837591 := bstep (se 1 (by rfl) ⟨1378193, by rfl⟩ : syracuseStep 1837591 = 2756387) B2756387
theorem B1837611 : Blo 1835619 1837611 := bstep (se 1 (by rfl) ⟨1378208, by rfl⟩ : syracuseStep 1837611 = 2756417) B2756417
theorem B5229107 : Blo 1835619 5229107 := bstep (se 1 (by rfl) ⟨3921830, by rfl⟩ : syracuseStep 5229107 = 7843661) B7843661
theorem B4131467 : Blo 1835619 4131467 := bstep (se 1 (by rfl) ⟨3098600, by rfl⟩ : syracuseStep 4131467 = 6197201) B6197201
theorem B2755211 : Blo 1835619 2755211 := bstep (se 1 (by rfl) ⟨2066408, by rfl⟩ : syracuseStep 2755211 = 4132817) B4132817
theorem B2755223 : Blo 1835619 2755223 := bstep (se 1 (by rfl) ⟨2066417, by rfl⟩ : syracuseStep 2755223 = 4132835) B4132835
theorem B3099289 : Blo 1835619 3099289 := bstep (se 2 (by rfl) ⟨1162233, by rfl⟩ : syracuseStep 3099289 = 2324467) B2324467
theorem B2067115 : Blo 1835619 2067115 := bstep (se 1 (by rfl) ⟨1550336, by rfl⟩ : syracuseStep 2067115 = 3100673) B3100673
theorem B6195905 : Blo 1835619 6195905 := bstep (se 2 (by rfl) ⟨2323464, by rfl⟩ : syracuseStep 6195905 = 4646929) B4646929
theorem B4131521 : Blo 1835619 4131521 := bstep (se 2 (by rfl) ⟨1549320, by rfl⟩ : syracuseStep 4131521 = 3098641) B3098641
theorem B2755289 : Blo 1835619 2755289 := bstep (se 2 (by rfl) ⟨1033233, by rfl⟩ : syracuseStep 2755289 = 2066467) B2066467
theorem B2067223 : Blo 1835619 2067223 := bstep (se 1 (by rfl) ⟨1550417, by rfl⟩ : syracuseStep 2067223 = 3100835) B3100835
theorem B2755403 : Blo 1835619 2755403 := bstep (se 1 (by rfl) ⟨2066552, by rfl⟩ : syracuseStep 2755403 = 4133105) B4133105
theorem B2755415 : Blo 1835619 2755415 := bstep (se 1 (by rfl) ⟨2066561, by rfl⟩ : syracuseStep 2755415 = 4133123) B4133123
theorem B4131737 : Blo 1835619 4131737 := bstep (se 2 (by rfl) ⟨1549401, by rfl⟩ : syracuseStep 4131737 = 3098803) B3098803
theorem B2755481 : Blo 1835619 2755481 := bstep (se 2 (by rfl) ⟨1033305, by rfl⟩ : syracuseStep 2755481 = 2066611) B2066611
theorem B6286297 : Blo 1835619 6286297 := bstep (se 2 (by rfl) ⟨2357361, by rfl⟩ : syracuseStep 6286297 = 4714723) B4714723
theorem B4131827 : Blo 1835619 4131827 := bstep (se 1 (by rfl) ⟨3098870, by rfl⟩ : syracuseStep 4131827 = 6197741) B6197741
theorem B2755595 : Blo 1835619 2755595 := bstep (se 1 (by rfl) ⟨2066696, by rfl⟩ : syracuseStep 2755595 = 4133393) B4133393
theorem B4131863 : Blo 1835619 4131863 := bstep (se 1 (by rfl) ⟨3098897, by rfl⟩ : syracuseStep 4131863 = 6197795) B6197795
theorem B2755607 : Blo 1835619 2755607 := bstep (se 1 (by rfl) ⟨2066705, by rfl⟩ : syracuseStep 2755607 = 4133411) B4133411
theorem B9301067 : Blo 1835619 9301067 := bstep (se 1 (by rfl) ⟨6975800, by rfl⟩ : syracuseStep 9301067 = 13951601) B13951601
theorem B2755673 : Blo 1835619 2755673 := bstep (se 2 (by rfl) ⟨1033377, by rfl⟩ : syracuseStep 2755673 = 2066755) B2066755
theorem B4132043 : Blo 1835619 4132043 := bstep (se 1 (by rfl) ⟨3099032, by rfl⟩ : syracuseStep 4132043 = 6198065) B6198065
theorem B2755787 : Blo 1835619 2755787 := bstep (se 1 (by rfl) ⟨2066840, by rfl⟩ : syracuseStep 2755787 = 4133681) B4133681
theorem B3099863 : Blo 1835619 3099863 := bstep (se 1 (by rfl) ⟨2324897, by rfl⟩ : syracuseStep 3099863 = 4649795) B4649795
theorem B2755799 : Blo 1835619 2755799 := bstep (se 1 (by rfl) ⟨2066849, by rfl⟩ : syracuseStep 2755799 = 4133699) B4133699
theorem B6196445 : Blo 1835619 6196445 := bstep (se 3 (by rfl) ⟨1161833, by rfl⟩ : syracuseStep 6196445 = 2323667) B2323667
theorem B4132097 : Blo 1835619 4132097 := bstep (se 2 (by rfl) ⟨1549536, by rfl⟩ : syracuseStep 4132097 = 3099073) B3099073
theorem B489590021 : Blo 1835619 489590021 := bstep (se 4 (by rfl) ⟨45899064, by rfl⟩ : syracuseStep 489590021 = 91798129) B91798129
theorem B3484939 : Blo 1835619 3484939 := bstep (se 1 (by rfl) ⟨2613704, by rfl⟩ : syracuseStep 3484939 = 5227409) B5227409
theorem B5885207 : Blo 1835619 5885207 := bstep (se 1 (by rfl) ⟨4413905, by rfl⟩ : syracuseStep 5885207 = 8827811) B8827811
theorem B2755865 : Blo 1835619 2755865 := bstep (se 2 (by rfl) ⟨1033449, by rfl⟩ : syracuseStep 2755865 = 2066899) B2066899
theorem B1961291 : Blo 1835619 1961291 := bstep (se 1 (by rfl) ⟨1470968, by rfl⟩ : syracuseStep 1961291 = 2941937) B2941937
theorem B5303627 : Blo 1835619 5303627 := bstep (se 1 (by rfl) ⟨3977720, by rfl⟩ : syracuseStep 5303627 = 7955441) B7955441
theorem B3485015 : Blo 1835619 3485015 := bstep (se 1 (by rfl) ⟨2613761, by rfl⟩ : syracuseStep 3485015 = 5227523) B5227523
theorem B3099991 : Blo 1835619 3099991 := bstep (se 1 (by rfl) ⟨2324993, by rfl⟩ : syracuseStep 3099991 = 4649987) B4649987
theorem B3722635 : Blo 1835619 3722635 := bstep (se 1 (by rfl) ⟨2791976, by rfl⟩ : syracuseStep 3722635 = 5583953) B5583953
theorem B2755979 : Blo 1835619 2755979 := bstep (se 1 (by rfl) ⟨2066984, by rfl⟩ : syracuseStep 2755979 = 4133969) B4133969
theorem B2755991 : Blo 1835619 2755991 := bstep (se 1 (by rfl) ⟨2066993, by rfl⟩ : syracuseStep 2755991 = 4133987) B4133987
theorem B24169907 : Blo 1835619 24169907 := bstep (se 1 (by rfl) ⟨18127430, by rfl⟩ : syracuseStep 24169907 = 36254861) B36254861
theorem B4132313 : Blo 1835619 4132313 := bstep (se 2 (by rfl) ⟨1549617, by rfl⟩ : syracuseStep 4132313 = 3099235) B3099235
theorem B2756057 : Blo 1835619 2756057 := bstep (se 2 (by rfl) ⟨1033521, by rfl⟩ : syracuseStep 2756057 = 2067043) B2067043
theorem B4648499 : Blo 1835619 4648499 := bstep (se 1 (by rfl) ⟨3486374, by rfl⟩ : syracuseStep 4648499 = 6972749) B6972749
theorem B4132403 : Blo 1835619 4132403 := bstep (se 1 (by rfl) ⟨3099302, by rfl⟩ : syracuseStep 4132403 = 6198605) B6198605
theorem B2756171 : Blo 1835619 2756171 := bstep (se 1 (by rfl) ⟨2067128, by rfl⟩ : syracuseStep 2756171 = 4134257) B4134257
theorem B4132439 : Blo 1835619 4132439 := bstep (se 1 (by rfl) ⟨3099329, by rfl⟩ : syracuseStep 4132439 = 6198659) B6198659
theorem B2756183 : Blo 1835619 2756183 := bstep (se 1 (by rfl) ⟨2067137, by rfl⟩ : syracuseStep 2756183 = 4134275) B4134275
theorem B31379075 : Blo 1835619 31379075 := bstep (se 1 (by rfl) ⟨23534306, by rfl⟩ : syracuseStep 31379075 = 47068613) B47068613
theorem B2756249 : Blo 1835619 2756249 := bstep (se 2 (by rfl) ⟨1033593, by rfl⟩ : syracuseStep 2756249 = 2067187) B2067187
theorem B6975179 : Blo 1835619 6975179 := bstep (se 1 (by rfl) ⟨5231384, by rfl⟩ : syracuseStep 6975179 = 10462769) B10462769
theorem B6975193 : Blo 1835619 6975193 := bstep (se 2 (by rfl) ⟨2615697, by rfl⟩ : syracuseStep 6975193 = 5231395) B5231395
theorem B4132619 : Blo 1835619 4132619 := bstep (se 1 (by rfl) ⟨3099464, by rfl⟩ : syracuseStep 4132619 = 6198929) B6198929
theorem B2756363 : Blo 1835619 2756363 := bstep (se 1 (by rfl) ⟨2067272, by rfl⟩ : syracuseStep 2756363 = 4134545) B4134545
theorem B2756375 : Blo 1835619 2756375 := bstep (se 1 (by rfl) ⟨2067281, by rfl⟩ : syracuseStep 2756375 = 4134563) B4134563
theorem B4132673 : Blo 1835619 4132673 := bstep (se 2 (by rfl) ⟨1549752, by rfl⟩ : syracuseStep 4132673 = 3099505) B3099505
theorem B12570461 : Blo 1835619 12570461 := bstep (se 3 (by rfl) ⟨2356961, by rfl⟩ : syracuseStep 12570461 = 4713923) B4713923
theorem B3100619 : Blo 1835619 3100619 := bstep (se 1 (by rfl) ⟨2325464, by rfl⟩ : syracuseStep 3100619 = 4650929) B4650929
theorem B3485683 : Blo 1835619 3485683 := bstep (se 1 (by rfl) ⟨2614262, by rfl⟩ : syracuseStep 3485683 = 5228525) B5228525
theorem B4411415 : Blo 1835619 4411415 := bstep (se 1 (by rfl) ⟨3308561, by rfl⟩ : syracuseStep 4411415 = 6617123) B6617123
theorem B4132889 : Blo 1835619 4132889 := bstep (se 2 (by rfl) ⟨1549833, by rfl⟩ : syracuseStep 4132889 = 3099667) B3099667
theorem B4649035 : Blo 1835619 4649035 := bstep (se 1 (by rfl) ⟨3486776, by rfl⟩ : syracuseStep 4649035 = 6973553) B6973553
theorem B3100747 : Blo 1835619 3100747 := bstep (se 1 (by rfl) ⟨2325560, by rfl⟩ : syracuseStep 3100747 = 4651121) B4651121
theorem B4132979 : Blo 1835619 4132979 := bstep (se 1 (by rfl) ⟨3099734, by rfl⟩ : syracuseStep 4132979 = 6199469) B6199469
theorem B7843985 : Blo 1835619 7843985 := bstep (se 2 (by rfl) ⟨2941494, by rfl⟩ : syracuseStep 7843985 = 5882989) B5882989
theorem B4133015 : Blo 1835619 4133015 := bstep (se 1 (by rfl) ⟨3099761, by rfl⟩ : syracuseStep 4133015 = 6199523) B6199523
theorem B3485911 : Blo 1835619 3485911 := bstep (se 1 (by rfl) ⟨2614433, by rfl⟩ : syracuseStep 3485911 = 5228867) B5228867
theorem B4649177 : Blo 1835619 4649177 := bstep (se 2 (by rfl) ⟨1743441, by rfl⟩ : syracuseStep 4649177 = 3486883) B3486883
theorem B3100889 : Blo 1835619 3100889 := bstep (se 2 (by rfl) ⟨1162833, by rfl⟩ : syracuseStep 3100889 = 2325667) B2325667
theorem B13414691 : Blo 1835619 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B3486017 : Blo 1835619 3486017 := bstep (se 2 (by rfl) ⟨1307256, by rfl⟩ : syracuseStep 3486017 = 2614513) B2614513
theorem B6197579 : Blo 1835619 6197579 := bstep (se 1 (by rfl) ⟨4648184, by rfl⟩ : syracuseStep 6197579 = 9296369) B9296369
theorem B8827211 : Blo 1835619 8827211 := bstep (se 1 (by rfl) ⟨6620408, by rfl⟩ : syracuseStep 8827211 = 13240817) B13240817
theorem B4133195 : Blo 1835619 4133195 := bstep (se 1 (by rfl) ⟨3099896, by rfl⟩ : syracuseStep 4133195 = 6199793) B6199793
theorem B4133249 : Blo 1835619 4133249 := bstep (se 2 (by rfl) ⟨1549968, by rfl⟩ : syracuseStep 4133249 = 3099937) B3099937
theorem B3723673 : Blo 1835619 3723673 := bstep (se 2 (by rfl) ⟨1396377, by rfl⟩ : syracuseStep 3723673 = 2792755) B2792755
theorem B3535319 : Blo 1835619 3535319 := bstep (se 1 (by rfl) ⟨2651489, by rfl⟩ : syracuseStep 3535319 = 5302979) B5302979
theorem B3486169 : Blo 1835619 3486169 := bstep (se 2 (by rfl) ⟨1307313, by rfl⟩ : syracuseStep 3486169 = 2614627) B2614627
theorem B4248065 : Blo 1835619 4248065 := bstep (se 2 (by rfl) ⟨1593024, by rfl⟩ : syracuseStep 4248065 = 3186049) B3186049
theorem B5886539 : Blo 1835619 5886539 := bstep (se 1 (by rfl) ⟨4414904, by rfl⟩ : syracuseStep 5886539 = 8829809) B8829809
theorem B6197849 : Blo 1835619 6197849 := bstep (se 2 (by rfl) ⟨2324193, by rfl⟩ : syracuseStep 6197849 = 4648387) B4648387
theorem B4133465 : Blo 1835619 4133465 := bstep (se 2 (by rfl) ⟨1550049, by rfl⟩ : syracuseStep 4133465 = 3100099) B3100099
theorem B6976151 : Blo 1835619 6976151 := bstep (se 1 (by rfl) ⟨5232113, by rfl⟩ : syracuseStep 6976151 = 10464227) B10464227
theorem B4133555 : Blo 1835619 4133555 := bstep (se 1 (by rfl) ⟨3100166, by rfl⟩ : syracuseStep 4133555 = 6200333) B6200333
theorem B5583563 : Blo 1835619 5583563 := bstep (se 1 (by rfl) ⟨4187672, by rfl⟩ : syracuseStep 5583563 = 8375345) B8375345
theorem B4133591 : Blo 1835619 4133591 := bstep (se 1 (by rfl) ⟨3100193, by rfl⟩ : syracuseStep 4133591 = 6200387) B6200387
theorem B5034803 : Blo 1835619 5034803 := bstep (se 1 (by rfl) ⟨3776102, by rfl⟩ : syracuseStep 5034803 = 7552205) B7552205
theorem B13947713 : Blo 1835619 13947713 := bstep (se 2 (by rfl) ⟨5230392, by rfl⟩ : syracuseStep 13947713 = 10460785) B10460785
theorem B9302849 : Blo 1835619 9302849 := bstep (se 2 (by rfl) ⟨3488568, by rfl⟩ : syracuseStep 9302849 = 6977137) B6977137
theorem B7844701 : Blo 1835619 7844701 := bstep (se 3 (by rfl) ⟨1470881, by rfl⟩ : syracuseStep 7844701 = 2941763) B2941763
theorem B4133771 : Blo 1835619 4133771 := bstep (se 1 (by rfl) ⟨3100328, by rfl⟩ : syracuseStep 4133771 = 6200657) B6200657
theorem B4133825 : Blo 1835619 4133825 := bstep (se 2 (by rfl) ⟨1550184, by rfl⟩ : syracuseStep 4133825 = 3100369) B3100369
theorem B4650007 : Blo 1835619 4650007 := bstep (se 1 (by rfl) ⟨3487505, by rfl⟩ : syracuseStep 4650007 = 6975011) B6975011
theorem B6280267 : Blo 1835619 6280267 := bstep (se 1 (by rfl) ⟨4710200, by rfl⟩ : syracuseStep 6280267 = 9420401) B9420401
theorem B2094155 : Blo 1835619 2094155 := bstep (se 1 (by rfl) ⟨1570616, by rfl⟩ : syracuseStep 2094155 = 3141233) B3141233
theorem B3724427 : Blo 1835619 3724427 := bstep (se 1 (by rfl) ⟨2793320, by rfl⟩ : syracuseStep 3724427 = 5586641) B5586641
theorem B4134041 : Blo 1835619 4134041 := bstep (se 2 (by rfl) ⟨1550265, by rfl⟩ : syracuseStep 4134041 = 3100531) B3100531
theorem B1987787 : Blo 1835619 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B3536075 : Blo 1835619 3536075 := bstep (se 1 (by rfl) ⟨2652056, by rfl⟩ : syracuseStep 3536075 = 5304113) B5304113
theorem B4134131 : Blo 1835619 4134131 := bstep (se 1 (by rfl) ⟨3100598, by rfl⟩ : syracuseStep 4134131 = 6201197) B6201197
theorem B2323723 : Blo 1835619 2323723 := bstep (se 1 (by rfl) ⟨1742792, by rfl⟩ : syracuseStep 2323723 = 3485585) B3485585
theorem B6198551 : Blo 1835619 6198551 := bstep (se 1 (by rfl) ⟨4648913, by rfl⟩ : syracuseStep 6198551 = 9297827) B9297827
theorem B4134167 : Blo 1835619 4134167 := bstep (se 1 (by rfl) ⟨3100625, by rfl⟩ : syracuseStep 4134167 = 6201251) B6201251
theorem B5231965 : Blo 1835619 5231965 := bstep (se 3 (by rfl) ⟨980993, by rfl⟩ : syracuseStep 5231965 = 1961987) B1961987
theorem B12744029 : Blo 1835619 12744029 := bstep (se 3 (by rfl) ⟨2389505, by rfl⟩ : syracuseStep 12744029 = 4779011) B4779011
theorem B9295235 : Blo 1835619 9295235 := bstep (se 1 (by rfl) ⟨6971426, by rfl⟩ : syracuseStep 9295235 = 13942853) B13942853
theorem B5232023 : Blo 1835619 5232023 := bstep (se 1 (by rfl) ⟨3924017, by rfl⟩ : syracuseStep 5232023 = 7848035) B7848035
theorem B4650443 : Blo 1835619 4650443 := bstep (se 1 (by rfl) ⟨3487832, by rfl⟩ : syracuseStep 4650443 = 6975665) B6975665
theorem B4134347 : Blo 1835619 4134347 := bstep (se 1 (by rfl) ⟨3100760, by rfl⟩ : syracuseStep 4134347 = 6201521) B6201521
theorem B4134401 : Blo 1835619 4134401 := bstep (se 2 (by rfl) ⟨1550400, by rfl⟩ : syracuseStep 4134401 = 3100801) B3100801
theorem B2323991 : Blo 1835619 2323991 := bstep (se 1 (by rfl) ⟨1742993, by rfl⟩ : syracuseStep 2323991 = 3485987) B3485987
theorem B20928131 : Blo 1835619 20928131 := bstep (se 1 (by rfl) ⟨15696098, by rfl⟩ : syracuseStep 20928131 = 31392197) B31392197
theorem B3921625 : Blo 1835619 3921625 := bstep (se 2 (by rfl) ⟨1470609, by rfl⟩ : syracuseStep 3921625 = 2941219) B2941219
theorem B4134617 : Blo 1835619 4134617 := bstep (se 2 (by rfl) ⟨1550481, by rfl⟩ : syracuseStep 4134617 = 3100963) B3100963
theorem B3487475 : Blo 1835619 3487475 := bstep (se 1 (by rfl) ⟨2615606, by rfl⟩ : syracuseStep 3487475 = 5231213) B5231213
theorem B6616835 : Blo 1835619 6616835 := bstep (se 1 (by rfl) ⟨4962626, by rfl⟩ : syracuseStep 6616835 = 9925253) B9925253
theorem B6199091 : Blo 1835619 6199091 := bstep (se 1 (by rfl) ⟨4649318, by rfl⟩ : syracuseStep 6199091 = 9298637) B9298637
theorem B4650817 : Blo 1835619 4650817 := bstep (se 2 (by rfl) ⟨1744056, by rfl⟩ : syracuseStep 4650817 = 3488113) B3488113
theorem B5584733 : Blo 1835619 5584733 := bstep (se 3 (by rfl) ⟨1047137, by rfl⟩ : syracuseStep 5584733 = 2094275) B2094275
theorem B3487627 : Blo 1835619 3487627 := bstep (se 1 (by rfl) ⟨2615720, by rfl⟩ : syracuseStep 3487627 = 5231441) B5231441
theorem B4470707 : Blo 1835619 4470707 := bstep (se 1 (by rfl) ⟨3353030, by rfl⟩ : syracuseStep 4470707 = 6706061) B6706061
theorem B2095031 : Blo 1835619 2095031 := bstep (se 1 (by rfl) ⟨1571273, by rfl⟩ : syracuseStep 2095031 = 3142547) B3142547
theorem B4593611 : Blo 1835619 4593611 := bstep (se 1 (by rfl) ⟨3445208, by rfl⟩ : syracuseStep 4593611 = 6890417) B6890417
theorem B4962269 : Blo 1835619 4962269 := bstep (se 3 (by rfl) ⟨930425, by rfl⟩ : syracuseStep 4962269 = 1860851) B1860851
theorem B12564497 : Blo 1835619 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B6199361 : Blo 1835619 6199361 := bstep (se 2 (by rfl) ⟨2324760, by rfl⟩ : syracuseStep 6199361 = 4649521) B4649521
theorem B47708311 : Blo 1835619 47708311 := bstep (se 1 (by rfl) ⟨35781233, by rfl⟩ : syracuseStep 47708311 = 71562467) B71562467
theorem B2324695 : Blo 1835619 2324695 := bstep (se 1 (by rfl) ⟨1743521, by rfl⟩ : syracuseStep 2324695 = 3487043) B3487043
theorem B3487961 : Blo 1835619 3487961 := bstep (se 2 (by rfl) ⟨1307985, by rfl⟩ : syracuseStep 3487961 = 2615971) B2615971
theorem B6969665 : Blo 1835619 6969665 := bstep (se 2 (by rfl) ⟨2613624, by rfl⟩ : syracuseStep 6969665 = 5227249) B5227249
theorem B4651415 : Blo 1835619 4651415 := bstep (se 1 (by rfl) ⟨3488561, by rfl⟩ : syracuseStep 4651415 = 6977123) B6977123
theorem B6199901 : Blo 1835619 6199901 := bstep (se 3 (by rfl) ⟨1162481, by rfl⟩ : syracuseStep 6199901 = 2324963) B2324963
theorem B13949657 : Blo 1835619 13949657 := bstep (se 2 (by rfl) ⟨5231121, by rfl⟩ : syracuseStep 13949657 = 10462243) B10462243
theorem B31365953 : Blo 1835619 31365953 := bstep (se 2 (by rfl) ⟨11762232, by rfl⟩ : syracuseStep 31365953 = 23524465) B23524465
theorem B3488599 : Blo 1835619 3488599 := bstep (se 1 (by rfl) ⟨2616449, by rfl⟩ : syracuseStep 3488599 = 5232899) B5232899
theorem B15686531 : Blo 1835619 15686531 := bstep (se 1 (by rfl) ⟨11764898, by rfl⟩ : syracuseStep 15686531 = 23529797) B23529797
theorem B63634355 : Blo 1835619 63634355 := bstep (se 1 (by rfl) ⟨47725766, by rfl⟩ : syracuseStep 63634355 = 95451533) B95451533
theorem B6970333 : Blo 1835619 6970333 := bstep (se 3 (by rfl) ⟨1306937, by rfl⟩ : syracuseStep 6970333 = 2613875) B2613875
theorem B11771153 : Blo 1835619 11771153 := bstep (se 2 (by rfl) ⟨4414182, by rfl⟩ : syracuseStep 11771153 = 8828365) B8828365
theorem B15899969 : Blo 1835619 15899969 := bstep (se 2 (by rfl) ⟨5962488, by rfl⟩ : syracuseStep 15899969 = 11924977) B11924977
theorem B6126941 : Blo 1835619 6126941 := bstep (se 3 (by rfl) ⟨1148801, by rfl⟩ : syracuseStep 6126941 = 2297603) B2297603
theorem B18849203 : Blo 1835619 18849203 := bstep (se 1 (by rfl) ⟨14136902, by rfl⟩ : syracuseStep 18849203 = 28273805) B28273805
theorem B4414913 : Blo 1835619 4414913 := bstep (se 2 (by rfl) ⟨1655592, by rfl⟩ : syracuseStep 4414913 = 3311185) B3311185
theorem B2793035 : Blo 1835619 2793035 := bstep (se 1 (by rfl) ⟨2094776, by rfl⟩ : syracuseStep 2793035 = 4189553) B4189553
theorem B2793047 : Blo 1835619 2793047 := bstep (se 1 (by rfl) ⟨2094785, by rfl⟩ : syracuseStep 2793047 = 4189571) B4189571
theorem B48381533 : Blo 1835619 48381533 := bstep (se 3 (by rfl) ⟨9071537, by rfl⟩ : syracuseStep 48381533 = 18143075) B18143075
theorem B6201035 : Blo 1835619 6201035 := bstep (se 1 (by rfl) ⟨4650776, by rfl⟩ : syracuseStep 6201035 = 9301553) B9301553
theorem B16760537 : Blo 1835619 16760537 := bstep (se 2 (by rfl) ⟨6285201, by rfl⟩ : syracuseStep 16760537 = 12570403) B12570403
theorem B7446275 : Blo 1835619 7446275 := bstep (se 1 (by rfl) ⟨5584706, by rfl⟩ : syracuseStep 7446275 = 11169413) B11169413
theorem B4710167 : Blo 1835619 4710167 := bstep (se 1 (by rfl) ⟨3532625, by rfl⟩ : syracuseStep 4710167 = 7065251) B7065251
theorem B3309427 : Blo 1835619 3309427 := bstep (se 1 (by rfl) ⟨2482070, by rfl⟩ : syracuseStep 3309427 = 4964141) B4964141
theorem B10461059 : Blo 1835619 10461059 := bstep (se 1 (by rfl) ⟨7845794, by rfl⟩ : syracuseStep 10461059 = 15691589) B15691589
theorem B6201305 : Blo 1835619 6201305 := bstep (se 2 (by rfl) ⟨2325489, by rfl⟩ : syracuseStep 6201305 = 4650979) B4650979
theorem B2940943 : Blo 1835619 2940943 := bstep (se 1 (by rfl) ⟨2205707, by rfl⟩ : syracuseStep 2940943 = 4411415) B4411415
theorem B63611081 : Blo 1835619 63611081 := bstep (se 2 (by rfl) ⟨23854155, by rfl⟩ : syracuseStep 63611081 = 47708311) B47708311
theorem B3924359 : Blo 1835619 3924359 := bstep (se 1 (by rfl) ⟨2943269, by rfl⟩ : syracuseStep 3924359 = 5886539) B5886539
theorem B6619601 : Blo 1835619 6619601 := bstep (se 2 (by rfl) ⟨2482350, by rfl⟩ : syracuseStep 6619601 = 4964701) B4964701
theorem B17646083 : Blo 1835619 17646083 := bstep (se 1 (by rfl) ⟨13234562, by rfl⟩ : syracuseStep 17646083 = 26469125) B26469125
theorem B5300765 : Blo 1835619 5300765 := bstep (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) B1987787
theorem B9429533 : Blo 1835619 9429533 := bstep (se 3 (by rfl) ⟨1768037, by rfl⟩ : syracuseStep 9429533 = 3536075) B3536075
theorem B4964897 : Blo 1835619 4964897 := bstep (se 2 (by rfl) ⟨1861836, by rfl⟩ : syracuseStep 4964897 = 3723673) B3723673
theorem B13943339 : Blo 1835619 13943339 := bstep (se 1 (by rfl) ⟨10457504, by rfl⟩ : syracuseStep 13943339 = 20915009) B20915009
theorem B9298475 : Blo 1835619 9298475 := bstep (se 1 (by rfl) ⟨6973856, by rfl⟩ : syracuseStep 9298475 = 13947713) B13947713
theorem B6201899 : Blo 1835619 6201899 := bstep (se 1 (by rfl) ⟨4651424, by rfl⟩ : syracuseStep 6201899 = 9302849) B9302849
theorem B5374583 : Blo 1835619 5374583 := bstep (se 1 (by rfl) ⟨4030937, by rfl⟩ : syracuseStep 5374583 = 8061875) B8061875
theorem B1835655 : Blo 1835619 1835655 := bstep (se 1 (by rfl) ⟨1376741, by rfl⟩ : syracuseStep 1835655 = 2753483) B2753483
theorem B1835663 : Blo 1835619 1835663 := bstep (se 1 (by rfl) ⟨1376747, by rfl⟩ : syracuseStep 1835663 = 2753495) B2753495
theorem B1835707 : Blo 1835619 1835707 := bstep (se 1 (by rfl) ⟨1376780, by rfl⟩ : syracuseStep 1835707 = 2753561) B2753561
theorem B2613961 : Blo 1835619 2613961 := bstep (se 2 (by rfl) ⟨980235, by rfl⟩ : syracuseStep 2613961 = 1960471) B1960471
theorem B4842185 : Blo 1835619 4842185 := bstep (se 2 (by rfl) ⟨1815819, by rfl⟩ : syracuseStep 4842185 = 3631639) B3631639
theorem B1835783 : Blo 1835619 1835783 := bstep (se 1 (by rfl) ⟨1376837, by rfl⟩ : syracuseStep 1835783 = 2753675) B2753675
theorem B1835791 : Blo 1835619 1835791 := bstep (se 1 (by rfl) ⟨1376843, by rfl⟩ : syracuseStep 1835791 = 2753687) B2753687
theorem B1835835 : Blo 1835619 1835835 := bstep (se 1 (by rfl) ⟨1376876, by rfl⟩ : syracuseStep 1835835 = 2753753) B2753753
theorem B1835911 : Blo 1835619 1835911 := bstep (se 1 (by rfl) ⟨1376933, by rfl⟩ : syracuseStep 1835911 = 2753867) B2753867
theorem B1835919 : Blo 1835619 1835919 := bstep (se 1 (by rfl) ⟨1376939, by rfl⟩ : syracuseStep 1835919 = 2753879) B2753879
theorem B8496019 : Blo 1835619 8496019 := bstep (se 1 (by rfl) ⟨6372014, by rfl⟩ : syracuseStep 8496019 = 12744029) B12744029
theorem B2753465 : Blo 1835619 2753465 := bstep (se 2 (by rfl) ⟨1032549, by rfl⟩ : syracuseStep 2753465 = 2065099) B2065099
theorem B1835963 : Blo 1835619 1835963 := bstep (se 1 (by rfl) ⟨1376972, by rfl⟩ : syracuseStep 1835963 = 2753945) B2753945
theorem B2753543 : Blo 1835619 2753543 := bstep (se 1 (by rfl) ⟨2065157, by rfl⟩ : syracuseStep 2753543 = 4130315) B4130315
theorem B1836039 : Blo 1835619 1836039 := bstep (se 1 (by rfl) ⟨1377029, by rfl⟩ : syracuseStep 1836039 = 2754059) B2754059
theorem B3097615 : Blo 1835619 3097615 := bstep (se 1 (by rfl) ⟨2323211, by rfl⟩ : syracuseStep 3097615 = 4646423) B4646423
theorem B2065423 : Blo 1835619 2065423 := bstep (se 1 (by rfl) ⟨1549067, by rfl⟩ : syracuseStep 2065423 = 3098135) B3098135
theorem B1836047 : Blo 1835619 1836047 := bstep (se 1 (by rfl) ⟨1377035, by rfl⟩ : syracuseStep 1836047 = 2754071) B2754071
theorem B2753579 : Blo 1835619 2753579 := bstep (se 1 (by rfl) ⟨2065184, by rfl⟩ : syracuseStep 2753579 = 4130369) B4130369
theorem B1836091 : Blo 1835619 1836091 := bstep (se 1 (by rfl) ⟨1377068, by rfl⟩ : syracuseStep 1836091 = 2754137) B2754137
theorem B2753609 : Blo 1835619 2753609 := bstep (se 2 (by rfl) ⟨1032603, by rfl⟩ : syracuseStep 2753609 = 2065207) B2065207
theorem B13952087 : Blo 1835619 13952087 := bstep (se 1 (by rfl) ⟨10464065, by rfl⟩ : syracuseStep 13952087 = 20928131) B20928131
theorem B1836167 : Blo 1835619 1836167 := bstep (se 1 (by rfl) ⟨1377125, by rfl⟩ : syracuseStep 1836167 = 2754251) B2754251
theorem B1836175 : Blo 1835619 1836175 := bstep (se 1 (by rfl) ⟨1377131, by rfl⟩ : syracuseStep 1836175 = 2754263) B2754263
theorem B2753723 : Blo 1835619 2753723 := bstep (se 1 (by rfl) ⟨2065292, by rfl⟩ : syracuseStep 2753723 = 4130585) B4130585
theorem B1836219 : Blo 1835619 1836219 := bstep (se 1 (by rfl) ⟨1377164, by rfl⟩ : syracuseStep 1836219 = 2754329) B2754329
theorem B2753783 : Blo 1835619 2753783 := bstep (se 1 (by rfl) ⟨2065337, by rfl⟩ : syracuseStep 2753783 = 4130675) B4130675
theorem B1836295 : Blo 1835619 1836295 := bstep (se 1 (by rfl) ⟨1377221, by rfl⟩ : syracuseStep 1836295 = 2754443) B2754443
theorem B2753807 : Blo 1835619 2753807 := bstep (se 1 (by rfl) ⟨2065355, by rfl⟩ : syracuseStep 2753807 = 4130711) B4130711
theorem B1836303 : Blo 1835619 1836303 := bstep (se 1 (by rfl) ⟨1377227, by rfl⟩ : syracuseStep 1836303 = 2754455) B2754455
theorem B8381729 : Blo 1835619 8381729 := bstep (se 2 (by rfl) ⟨3143148, by rfl⟩ : syracuseStep 8381729 = 6286297) B6286297
theorem B2753849 : Blo 1835619 2753849 := bstep (se 2 (by rfl) ⟨1032693, by rfl⟩ : syracuseStep 2753849 = 2065387) B2065387
theorem B1836347 : Blo 1835619 1836347 := bstep (se 1 (by rfl) ⟨1377260, by rfl⟩ : syracuseStep 1836347 = 2754521) B2754521
theorem B2753927 : Blo 1835619 2753927 := bstep (se 1 (by rfl) ⟨2065445, by rfl⟩ : syracuseStep 2753927 = 4130891) B4130891
theorem B1836423 : Blo 1835619 1836423 := bstep (se 1 (by rfl) ⟨1377317, by rfl⟩ : syracuseStep 1836423 = 2754635) B2754635
theorem B1836431 : Blo 1835619 1836431 := bstep (se 1 (by rfl) ⟨1377323, by rfl⟩ : syracuseStep 1836431 = 2754647) B2754647
theorem B2753963 : Blo 1835619 2753963 := bstep (se 1 (by rfl) ⟨2065472, by rfl⟩ : syracuseStep 2753963 = 4130945) B4130945
theorem B8373689 : Blo 1835619 8373689 := bstep (se 2 (by rfl) ⟨3140133, by rfl⟩ : syracuseStep 8373689 = 6280267) B6280267
theorem B1836475 : Blo 1835619 1836475 := bstep (se 1 (by rfl) ⟨1377356, by rfl⟩ : syracuseStep 1836475 = 2754713) B2754713
theorem B2753993 : Blo 1835619 2753993 := bstep (se 2 (by rfl) ⟨1032747, by rfl⟩ : syracuseStep 2753993 = 2065495) B2065495
theorem B28272077 : Blo 1835619 28272077 := bstep (se 3 (by rfl) ⟨5301014, by rfl⟩ : syracuseStep 28272077 = 10602029) B10602029
theorem B2065927 : Blo 1835619 2065927 := bstep (se 1 (by rfl) ⟨1549445, by rfl⟩ : syracuseStep 2065927 = 3098891) B3098891
theorem B1836551 : Blo 1835619 1836551 := bstep (se 1 (by rfl) ⟨1377413, by rfl⟩ : syracuseStep 1836551 = 2754827) B2754827
theorem B1836559 : Blo 1835619 1836559 := bstep (se 1 (by rfl) ⟨1377419, by rfl⟩ : syracuseStep 1836559 = 2754839) B2754839
theorem B4646443 : Blo 1835619 4646443 := bstep (se 1 (by rfl) ⟨3484832, by rfl⟩ : syracuseStep 4646443 = 6969665) B6969665
theorem B3098155 : Blo 1835619 3098155 := bstep (se 1 (by rfl) ⟨2323616, by rfl⟩ : syracuseStep 3098155 = 4647233) B4647233
theorem B2754107 : Blo 1835619 2754107 := bstep (se 1 (by rfl) ⟨2065580, by rfl⟩ : syracuseStep 2754107 = 4131161) B4131161
theorem B1836603 : Blo 1835619 1836603 := bstep (se 1 (by rfl) ⟨1377452, by rfl⟩ : syracuseStep 1836603 = 2754905) B2754905
theorem B7448125 : Blo 1835619 7448125 := bstep (se 3 (by rfl) ⟨1396523, by rfl⟩ : syracuseStep 7448125 = 2793047) B2793047
theorem B4130423 : Blo 1835619 4130423 := bstep (se 1 (by rfl) ⟨3097817, by rfl⟩ : syracuseStep 4130423 = 6195635) B6195635
theorem B2754167 : Blo 1835619 2754167 := bstep (se 1 (by rfl) ⟨2065625, by rfl⟩ : syracuseStep 2754167 = 4131251) B4131251
theorem B1836679 : Blo 1835619 1836679 := bstep (se 1 (by rfl) ⟨1377509, by rfl⟩ : syracuseStep 1836679 = 2755019) B2755019
theorem B2754191 : Blo 1835619 2754191 := bstep (se 1 (by rfl) ⟨2065643, by rfl⟩ : syracuseStep 2754191 = 4131287) B4131287
theorem B1836687 : Blo 1835619 1836687 := bstep (se 1 (by rfl) ⟨1377515, by rfl⟩ : syracuseStep 1836687 = 2755031) B2755031
theorem B4646585 : Blo 1835619 4646585 := bstep (se 2 (by rfl) ⟨1742469, by rfl⟩ : syracuseStep 4646585 = 3484939) B3484939
theorem B3098297 : Blo 1835619 3098297 := bstep (se 2 (by rfl) ⟨1161861, by rfl⟩ : syracuseStep 3098297 = 2323723) B2323723
theorem B2754233 : Blo 1835619 2754233 := bstep (se 2 (by rfl) ⟨1032837, by rfl⟩ : syracuseStep 2754233 = 2065675) B2065675
theorem B2066107 : Blo 1835619 2066107 := bstep (se 1 (by rfl) ⟨1549580, by rfl⟩ : syracuseStep 2066107 = 3099161) B3099161
theorem B1836731 : Blo 1835619 1836731 := bstep (se 1 (by rfl) ⟨1377548, by rfl⟩ : syracuseStep 1836731 = 2755097) B2755097
theorem B2754311 : Blo 1835619 2754311 := bstep (se 1 (by rfl) ⟨2065733, by rfl⟩ : syracuseStep 2754311 = 4131467) B4131467
theorem B1836807 : Blo 1835619 1836807 := bstep (se 1 (by rfl) ⟨1377605, by rfl⟩ : syracuseStep 1836807 = 2755211) B2755211
theorem B1836815 : Blo 1835619 1836815 := bstep (se 1 (by rfl) ⟨1377611, by rfl⟩ : syracuseStep 1836815 = 2755223) B2755223
theorem B4130603 : Blo 1835619 4130603 := bstep (se 1 (by rfl) ⟨3097952, by rfl⟩ : syracuseStep 4130603 = 6195905) B6195905
theorem B2754347 : Blo 1835619 2754347 := bstep (se 1 (by rfl) ⟨2065760, by rfl⟩ : syracuseStep 2754347 = 4131521) B4131521
theorem B1836859 : Blo 1835619 1836859 := bstep (se 1 (by rfl) ⟨1377644, by rfl⟩ : syracuseStep 1836859 = 2755289) B2755289
theorem B9299771 : Blo 1835619 9299771 := bstep (se 1 (by rfl) ⟨6974828, by rfl⟩ : syracuseStep 9299771 = 13949657) B13949657
theorem B2754377 : Blo 1835619 2754377 := bstep (se 2 (by rfl) ⟨1032891, by rfl⟩ : syracuseStep 2754377 = 2065783) B2065783
theorem B1836935 : Blo 1835619 1836935 := bstep (se 1 (by rfl) ⟨1377701, by rfl⟩ : syracuseStep 1836935 = 2755403) B2755403
theorem B1836943 : Blo 1835619 1836943 := bstep (se 1 (by rfl) ⟨1377707, by rfl⟩ : syracuseStep 1836943 = 2755415) B2755415
theorem B2754491 : Blo 1835619 2754491 := bstep (se 1 (by rfl) ⟨2065868, by rfl⟩ : syracuseStep 2754491 = 4131737) B4131737
theorem B1836987 : Blo 1835619 1836987 := bstep (se 1 (by rfl) ⟨1377740, by rfl⟩ : syracuseStep 1836987 = 2755481) B2755481
theorem B9299933 : Blo 1835619 9299933 := bstep (se 3 (by rfl) ⟨1743737, by rfl⟩ : syracuseStep 9299933 = 3487475) B3487475
theorem B2754551 : Blo 1835619 2754551 := bstep (se 1 (by rfl) ⟨2065913, by rfl⟩ : syracuseStep 2754551 = 4131827) B4131827
theorem B1837063 : Blo 1835619 1837063 := bstep (se 1 (by rfl) ⟨1377797, by rfl⟩ : syracuseStep 1837063 = 2755595) B2755595
theorem B2754575 : Blo 1835619 2754575 := bstep (se 1 (by rfl) ⟨2065931, by rfl⟩ : syracuseStep 2754575 = 4131863) B4131863
theorem B1837071 : Blo 1835619 1837071 := bstep (se 1 (by rfl) ⟨1377803, by rfl⟩ : syracuseStep 1837071 = 2755607) B2755607
theorem B2754617 : Blo 1835619 2754617 := bstep (se 2 (by rfl) ⟨1032981, by rfl⟩ : syracuseStep 2754617 = 2065963) B2065963
theorem B1837115 : Blo 1835619 1837115 := bstep (se 1 (by rfl) ⟨1377836, by rfl⟩ : syracuseStep 1837115 = 2755673) B2755673
theorem B2754695 : Blo 1835619 2754695 := bstep (se 1 (by rfl) ⟨2066021, by rfl⟩ : syracuseStep 2754695 = 4132043) B4132043
theorem B1837191 : Blo 1835619 1837191 := bstep (se 1 (by rfl) ⟨1377893, by rfl⟩ : syracuseStep 1837191 = 2755787) B2755787
theorem B2066575 : Blo 1835619 2066575 := bstep (se 1 (by rfl) ⟨1549931, by rfl⟩ : syracuseStep 2066575 = 3099863) B3099863
theorem B1837199 : Blo 1835619 1837199 := bstep (se 1 (by rfl) ⟨1377899, by rfl⟩ : syracuseStep 1837199 = 2755799) B2755799
theorem B4130963 : Blo 1835619 4130963 := bstep (se 1 (by rfl) ⟨3098222, by rfl⟩ : syracuseStep 4130963 = 6196445) B6196445
theorem B2754731 : Blo 1835619 2754731 := bstep (se 1 (by rfl) ⟨2066048, by rfl⟩ : syracuseStep 2754731 = 4132097) B4132097
theorem B1837243 : Blo 1835619 1837243 := bstep (se 1 (by rfl) ⟨1377932, by rfl⟩ : syracuseStep 1837243 = 2755865) B2755865
theorem B4131017 : Blo 1835619 4131017 := bstep (se 2 (by rfl) ⟨1549131, by rfl⟩ : syracuseStep 4131017 = 3098263) B3098263
theorem B2754761 : Blo 1835619 2754761 := bstep (se 2 (by rfl) ⟨1033035, by rfl⟩ : syracuseStep 2754761 = 2066071) B2066071
theorem B1837319 : Blo 1835619 1837319 := bstep (se 1 (by rfl) ⟨1377989, by rfl⟩ : syracuseStep 1837319 = 2755979) B2755979
theorem B1837327 : Blo 1835619 1837327 := bstep (se 1 (by rfl) ⟨1377995, by rfl⟩ : syracuseStep 1837327 = 2755991) B2755991
theorem B5228833 : Blo 1835619 5228833 := bstep (se 2 (by rfl) ⟨1960812, by rfl⟩ : syracuseStep 5228833 = 3921625) B3921625
theorem B9300257 : Blo 1835619 9300257 := bstep (se 2 (by rfl) ⟨3487596, by rfl⟩ : syracuseStep 9300257 = 6975193) B6975193
theorem B2943275 : Blo 1835619 2943275 := bstep (se 1 (by rfl) ⟨2207456, by rfl⟩ : syracuseStep 2943275 = 4414913) B4414913
theorem B2754875 : Blo 1835619 2754875 := bstep (se 1 (by rfl) ⟨2066156, by rfl⟩ : syracuseStep 2754875 = 4132313) B4132313
theorem B1837371 : Blo 1835619 1837371 := bstep (se 1 (by rfl) ⟨1378028, by rfl⟩ : syracuseStep 1837371 = 2756057) B2756057
theorem B3098999 : Blo 1835619 3098999 := bstep (se 1 (by rfl) ⟨2324249, by rfl⟩ : syracuseStep 3098999 = 4648499) B4648499
theorem B2754935 : Blo 1835619 2754935 := bstep (se 1 (by rfl) ⟨2066201, by rfl⟩ : syracuseStep 2754935 = 4132403) B4132403
theorem B1862023 : Blo 1835619 1862023 := bstep (se 1 (by rfl) ⟨1396517, by rfl⟩ : syracuseStep 1862023 = 2793035) B2793035
theorem B1837447 : Blo 1835619 1837447 := bstep (se 1 (by rfl) ⟨1378085, by rfl⟩ : syracuseStep 1837447 = 2756171) B2756171
theorem B2754959 : Blo 1835619 2754959 := bstep (se 1 (by rfl) ⟨2066219, by rfl⟩ : syracuseStep 2754959 = 4132439) B4132439
theorem B1837455 : Blo 1835619 1837455 := bstep (se 1 (by rfl) ⟨1378091, by rfl⟩ : syracuseStep 1837455 = 2756183) B2756183
theorem B32254355 : Blo 1835619 32254355 := bstep (se 1 (by rfl) ⟨24190766, by rfl⟩ : syracuseStep 32254355 = 48381533) B48381533
theorem B2755001 : Blo 1835619 2755001 := bstep (se 2 (by rfl) ⟨1033125, by rfl⟩ : syracuseStep 2755001 = 2066251) B2066251
theorem B1837499 : Blo 1835619 1837499 := bstep (se 1 (by rfl) ⟨1378124, by rfl⟩ : syracuseStep 1837499 = 2756249) B2756249
theorem B2755079 : Blo 1835619 2755079 := bstep (se 1 (by rfl) ⟨2066309, by rfl⟩ : syracuseStep 2755079 = 4132619) B4132619
theorem B1837575 : Blo 1835619 1837575 := bstep (se 1 (by rfl) ⟨1378181, by rfl⟩ : syracuseStep 1837575 = 2756363) B2756363
theorem B3140111 : Blo 1835619 3140111 := bstep (se 1 (by rfl) ⟨2355083, by rfl⟩ : syracuseStep 3140111 = 4710167) B4710167
theorem B1837583 : Blo 1835619 1837583 := bstep (se 1 (by rfl) ⟨1378187, by rfl⟩ : syracuseStep 1837583 = 2756375) B2756375
theorem B12249629 : Blo 1835619 12249629 := bstep (se 3 (by rfl) ⟨2296805, by rfl⟩ : syracuseStep 12249629 = 4593611) B4593611
theorem B2755115 : Blo 1835619 2755115 := bstep (se 1 (by rfl) ⟨2066336, by rfl⟩ : syracuseStep 2755115 = 4132673) B4132673
theorem B2755145 : Blo 1835619 2755145 := bstep (se 2 (by rfl) ⟨1033179, by rfl⟩ : syracuseStep 2755145 = 2066359) B2066359
theorem B13232717 : Blo 1835619 13232717 := bstep (se 3 (by rfl) ⟨2481134, by rfl⟩ : syracuseStep 13232717 = 4962269) B4962269
theorem B6974039 : Blo 1835619 6974039 := bstep (se 1 (by rfl) ⟨5230529, by rfl⟩ : syracuseStep 6974039 = 10461059) B10461059
theorem B2067079 : Blo 1835619 2067079 := bstep (se 1 (by rfl) ⟨1550309, by rfl⟩ : syracuseStep 2067079 = 3100619) B3100619
theorem B4647577 : Blo 1835619 4647577 := bstep (se 2 (by rfl) ⟨1742841, by rfl⟩ : syracuseStep 4647577 = 3485683) B3485683
theorem B2755259 : Blo 1835619 2755259 := bstep (se 1 (by rfl) ⟨2066444, by rfl⟩ : syracuseStep 2755259 = 4132889) B4132889
theorem B2755319 : Blo 1835619 2755319 := bstep (se 1 (by rfl) ⟨2066489, by rfl⟩ : syracuseStep 2755319 = 4132979) B4132979
theorem B5229323 : Blo 1835619 5229323 := bstep (se 1 (by rfl) ⟨3921992, by rfl⟩ : syracuseStep 5229323 = 7843985) B7843985
theorem B2755343 : Blo 1835619 2755343 := bstep (se 1 (by rfl) ⟨2066507, by rfl⟩ : syracuseStep 2755343 = 4133015) B4133015
theorem B2755385 : Blo 1835619 2755385 := bstep (se 2 (by rfl) ⟨1033269, by rfl⟩ : syracuseStep 2755385 = 2066539) B2066539
theorem B4647739 : Blo 1835619 4647739 := bstep (se 1 (by rfl) ⟨3485804, by rfl⟩ : syracuseStep 4647739 = 6971609) B6971609
theorem B3099451 : Blo 1835619 3099451 := bstep (se 1 (by rfl) ⟨2324588, by rfl⟩ : syracuseStep 3099451 = 4649177) B4649177
theorem B2067259 : Blo 1835619 2067259 := bstep (se 1 (by rfl) ⟨1550444, by rfl⟩ : syracuseStep 2067259 = 3100889) B3100889
theorem B4131719 : Blo 1835619 4131719 := bstep (se 1 (by rfl) ⟨3098789, by rfl⟩ : syracuseStep 4131719 = 6197579) B6197579
theorem B5884807 : Blo 1835619 5884807 := bstep (se 1 (by rfl) ⟨4413605, by rfl⟩ : syracuseStep 5884807 = 8827211) B8827211
theorem B2755463 : Blo 1835619 2755463 := bstep (se 1 (by rfl) ⟨2066597, by rfl⟩ : syracuseStep 2755463 = 4133195) B4133195
theorem B6196121 : Blo 1835619 6196121 := bstep (se 2 (by rfl) ⟨2323545, by rfl⟩ : syracuseStep 6196121 = 4647091) B4647091
theorem B2755499 : Blo 1835619 2755499 := bstep (se 1 (by rfl) ⟨2066624, by rfl⟩ : syracuseStep 2755499 = 4133249) B4133249
theorem B4647881 : Blo 1835619 4647881 := bstep (se 2 (by rfl) ⟨1742955, by rfl⟩ : syracuseStep 4647881 = 3485911) B3485911
theorem B3099593 : Blo 1835619 3099593 := bstep (se 2 (by rfl) ⟨1162347, by rfl⟩ : syracuseStep 3099593 = 2324695) B2324695
theorem B2755529 : Blo 1835619 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B8825867 : Blo 1835619 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B9931805 : Blo 1835619 9931805 := bstep (se 3 (by rfl) ⟨1862213, by rfl⟩ : syracuseStep 9931805 = 3724427) B3724427
theorem B4131899 : Blo 1835619 4131899 := bstep (se 1 (by rfl) ⟨3098924, by rfl⟩ : syracuseStep 4131899 = 6197849) B6197849
theorem B6974525 : Blo 1835619 6974525 := bstep (se 3 (by rfl) ⟨1307723, by rfl⟩ : syracuseStep 6974525 = 2615447) B2615447
theorem B2755643 : Blo 1835619 2755643 := bstep (se 1 (by rfl) ⟨2066732, by rfl⟩ : syracuseStep 2755643 = 4133465) B4133465
theorem B31370327 : Blo 1835619 31370327 := bstep (se 1 (by rfl) ⟨23527745, by rfl⟩ : syracuseStep 31370327 = 47055491) B47055491
theorem B2755703 : Blo 1835619 2755703 := bstep (se 1 (by rfl) ⟨2066777, by rfl⟩ : syracuseStep 2755703 = 4133555) B4133555
theorem B3722375 : Blo 1835619 3722375 := bstep (se 1 (by rfl) ⟨2791781, by rfl⟩ : syracuseStep 3722375 = 5583563) B5583563
theorem B2755727 : Blo 1835619 2755727 := bstep (se 1 (by rfl) ⟨2066795, by rfl⟩ : syracuseStep 2755727 = 4133591) B4133591
theorem B4132025 : Blo 1835619 4132025 := bstep (se 2 (by rfl) ⟨1549509, by rfl⟩ : syracuseStep 4132025 = 3099019) B3099019
theorem B2755769 : Blo 1835619 2755769 := bstep (se 2 (by rfl) ⟨1033413, by rfl⟩ : syracuseStep 2755769 = 2066827) B2066827
theorem B9301229 : Blo 1835619 9301229 := bstep (se 3 (by rfl) ⟨1743980, by rfl⟩ : syracuseStep 9301229 = 3487961) B3487961
theorem B2755847 : Blo 1835619 2755847 := bstep (se 1 (by rfl) ⟨2066885, by rfl⟩ : syracuseStep 2755847 = 4133771) B4133771
theorem B4648225 : Blo 1835619 4648225 := bstep (se 2 (by rfl) ⟨1743084, by rfl⟩ : syracuseStep 4648225 = 3486169) B3486169
theorem B2755883 : Blo 1835619 2755883 := bstep (se 1 (by rfl) ⟨2066912, by rfl⟩ : syracuseStep 2755883 = 4133825) B4133825
theorem B2755913 : Blo 1835619 2755913 := bstep (se 2 (by rfl) ⟨1033467, by rfl⟩ : syracuseStep 2755913 = 2066935) B2066935
theorem B10464659 : Blo 1835619 10464659 := bstep (se 1 (by rfl) ⟨7848494, by rfl⟩ : syracuseStep 10464659 = 15696989) B15696989
theorem B44690867 : Blo 1835619 44690867 := bstep (se 1 (by rfl) ⟨33518150, by rfl⟩ : syracuseStep 44690867 = 67036301) B67036301
theorem B2756027 : Blo 1835619 2756027 := bstep (se 1 (by rfl) ⟨2067020, by rfl⟩ : syracuseStep 2756027 = 4134041) B4134041
theorem B2756087 : Blo 1835619 2756087 := bstep (se 1 (by rfl) ⟨2067065, by rfl⟩ : syracuseStep 2756087 = 4134131) B4134131
theorem B4132367 : Blo 1835619 4132367 := bstep (se 1 (by rfl) ⟨3099275, by rfl⟩ : syracuseStep 4132367 = 6198551) B6198551
theorem B2756111 : Blo 1835619 2756111 := bstep (se 1 (by rfl) ⟨2067083, by rfl⟩ : syracuseStep 2756111 = 4134167) B4134167
theorem B5230109 : Blo 1835619 5230109 := bstep (se 3 (by rfl) ⟨980645, by rfl⟩ : syracuseStep 5230109 = 1961291) B1961291
theorem B4132385 : Blo 1835619 4132385 := bstep (se 2 (by rfl) ⟨1549644, by rfl⟩ : syracuseStep 4132385 = 3099289) B3099289
theorem B2756153 : Blo 1835619 2756153 := bstep (se 2 (by rfl) ⟨1033557, by rfl⟩ : syracuseStep 2756153 = 2067115) B2067115
theorem B5582395 : Blo 1835619 5582395 := bstep (se 1 (by rfl) ⟨4186796, by rfl⟩ : syracuseStep 5582395 = 8373593) B8373593
theorem B3485243 : Blo 1835619 3485243 := bstep (se 1 (by rfl) ⟨2613932, by rfl⟩ : syracuseStep 3485243 = 5227865) B5227865
theorem B16338509 : Blo 1835619 16338509 := bstep (se 3 (by rfl) ⟨3063470, by rfl⟩ : syracuseStep 16338509 = 6126941) B6126941
theorem B6196823 : Blo 1835619 6196823 := bstep (se 1 (by rfl) ⟨4647617, by rfl⟩ : syracuseStep 6196823 = 9295235) B9295235
theorem B3100295 : Blo 1835619 3100295 := bstep (se 1 (by rfl) ⟨2325221, by rfl⟩ : syracuseStep 3100295 = 4650443) B4650443
theorem B2756231 : Blo 1835619 2756231 := bstep (se 1 (by rfl) ⟨2067173, by rfl⟩ : syracuseStep 2756231 = 4134347) B4134347
theorem B2756267 : Blo 1835619 2756267 := bstep (se 1 (by rfl) ⟨2067200, by rfl⟩ : syracuseStep 2756267 = 4134401) B4134401
theorem B2756297 : Blo 1835619 2756297 := bstep (se 2 (by rfl) ⟨1033611, by rfl⟩ : syracuseStep 2756297 = 2067223) B2067223
theorem B2756411 : Blo 1835619 2756411 := bstep (se 1 (by rfl) ⟨2067308, by rfl⟩ : syracuseStep 2756411 = 4134617) B4134617
theorem B4411223 : Blo 1835619 4411223 := bstep (se 1 (by rfl) ⟨3308417, by rfl⟩ : syracuseStep 4411223 = 6616835) B6616835
theorem B44666741 : Blo 1835619 44666741 := bstep (se 5 (by rfl) ⟨2093753, by rfl⟩ : syracuseStep 44666741 = 4187507) B4187507
theorem B4648823 : Blo 1835619 4648823 := bstep (se 1 (by rfl) ⟨3486617, by rfl⟩ : syracuseStep 4648823 = 6973235) B6973235
theorem B4132727 : Blo 1835619 4132727 := bstep (se 1 (by rfl) ⟨3099545, by rfl⟩ : syracuseStep 4132727 = 6199091) B6199091
theorem B10465159 : Blo 1835619 10465159 := bstep (se 1 (by rfl) ⟨7848869, by rfl⟩ : syracuseStep 10465159 = 15697739) B15697739
theorem B3723155 : Blo 1835619 3723155 := bstep (se 1 (by rfl) ⟨2792366, by rfl⟩ : syracuseStep 3723155 = 5584733) B5584733
theorem B9293777 : Blo 1835619 9293777 := bstep (se 2 (by rfl) ⟨3485166, by rfl⟩ : syracuseStep 9293777 = 6970333) B6970333
theorem B8376331 : Blo 1835619 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B9302039 : Blo 1835619 9302039 := bstep (se 1 (by rfl) ⟨6976529, by rfl⟩ : syracuseStep 9302039 = 13953059) B13953059
theorem B3485729 : Blo 1835619 3485729 := bstep (se 2 (by rfl) ⟨1307148, by rfl⟩ : syracuseStep 3485729 = 2614297) B2614297
theorem B4132907 : Blo 1835619 4132907 := bstep (se 1 (by rfl) ⟨3099680, by rfl⟩ : syracuseStep 4132907 = 6199361) B6199361
theorem B6197309 : Blo 1835619 6197309 := bstep (se 3 (by rfl) ⟨1161995, by rfl⟩ : syracuseStep 6197309 = 2323991) B2323991
theorem B3100943 : Blo 1835619 3100943 := bstep (se 1 (by rfl) ⟨2325707, by rfl⟩ : syracuseStep 3100943 = 4651415) B4651415
theorem B3486071 : Blo 1835619 3486071 := bstep (se 1 (by rfl) ⟨2614553, by rfl⟩ : syracuseStep 3486071 = 5229107) B5229107
theorem B4133267 : Blo 1835619 4133267 := bstep (se 1 (by rfl) ⟨3099950, by rfl⟩ : syracuseStep 4133267 = 6199901) B6199901
theorem B4133321 : Blo 1835619 4133321 := bstep (se 2 (by rfl) ⟨1549995, by rfl⟩ : syracuseStep 4133321 = 3099991) B3099991
theorem B6975953 : Blo 1835619 6975953 := bstep (se 2 (by rfl) ⟨2615982, by rfl⟩ : syracuseStep 6975953 = 5231965) B5231965
theorem B35303921 : Blo 1835619 35303921 := bstep (se 2 (by rfl) ⟨13238970, by rfl⟩ : syracuseStep 35303921 = 26477941) B26477941
theorem B20910635 : Blo 1835619 20910635 := bstep (se 1 (by rfl) ⟨15682976, by rfl⟩ : syracuseStep 20910635 = 31365953) B31365953
theorem B10457687 : Blo 1835619 10457687 := bstep (se 1 (by rfl) ⟨7843265, by rfl⟩ : syracuseStep 10457687 = 15686531) B15686531
theorem B42422903 : Blo 1835619 42422903 := bstep (se 1 (by rfl) ⟨31817177, by rfl⟩ : syracuseStep 42422903 = 63634355) B63634355
theorem B3535751 : Blo 1835619 3535751 := bstep (se 1 (by rfl) ⟨2651813, by rfl⟩ : syracuseStep 3535751 = 5303627) B5303627
theorem B2323343 : Blo 1835619 2323343 := bstep (se 1 (by rfl) ⟨1742507, by rfl⟩ : syracuseStep 2323343 = 3485015) B3485015
theorem B17642393 : Blo 1835619 17642393 := bstep (se 2 (by rfl) ⟨6615897, by rfl⟩ : syracuseStep 17642393 = 13231795) B13231795
theorem B20919383 : Blo 1835619 20919383 := bstep (se 1 (by rfl) ⟨15689537, by rfl⟩ : syracuseStep 20919383 = 31379075) B31379075
theorem B4650119 : Blo 1835619 4650119 := bstep (se 1 (by rfl) ⟨3487589, by rfl⟩ : syracuseStep 4650119 = 6975179) B6975179
theorem B4134023 : Blo 1835619 4134023 := bstep (se 1 (by rfl) ⟨3100517, by rfl⟩ : syracuseStep 4134023 = 6201035) B6201035
theorem B4412569 : Blo 1835619 4412569 := bstep (se 2 (by rfl) ⟨1654713, by rfl⟩ : syracuseStep 4412569 = 3309427) B3309427
theorem B4650169 : Blo 1835619 4650169 := bstep (se 2 (by rfl) ⟨1743813, by rfl⟩ : syracuseStep 4650169 = 3487627) B3487627
theorem B4134203 : Blo 1835619 4134203 := bstep (se 1 (by rfl) ⟨3100652, by rfl⟩ : syracuseStep 4134203 = 6201305) B6201305
theorem B3724663 : Blo 1835619 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B6198713 : Blo 1835619 6198713 := bstep (se 2 (by rfl) ⟨2324517, by rfl⟩ : syracuseStep 6198713 = 4649035) B4649035
theorem B4134329 : Blo 1835619 4134329 := bstep (se 2 (by rfl) ⟨1550373, by rfl⟩ : syracuseStep 4134329 = 3100747) B3100747
theorem B6280715 : Blo 1835619 6280715 := bstep (se 1 (by rfl) ⟨4710536, by rfl⟩ : syracuseStep 6280715 = 9421073) B9421073
theorem B7845437 : Blo 1835619 7845437 := bstep (se 3 (by rfl) ⟨1471019, by rfl⟩ : syracuseStep 7845437 = 2942039) B2942039
theorem B5232215 : Blo 1835619 5232215 := bstep (se 1 (by rfl) ⟨3924161, by rfl⟩ : syracuseStep 5232215 = 7848323) B7848323
theorem B9549485 : Blo 1835619 9549485 := bstep (se 3 (by rfl) ⟨1790528, by rfl⟩ : syracuseStep 9549485 = 3581057) B3581057
theorem B4650767 : Blo 1835619 4650767 := bstep (se 1 (by rfl) ⟨3488075, by rfl⟩ : syracuseStep 4650767 = 6976151) B6976151
theorem B3487673 : Blo 1835619 3487673 := bstep (se 2 (by rfl) ⟨1307877, by rfl⟩ : syracuseStep 3487673 = 2615755) B2615755
theorem B9295883 : Blo 1835619 9295883 := bstep (se 1 (by rfl) ⟨6971912, by rfl⟩ : syracuseStep 9295883 = 13943825) B13943825
theorem B6199307 : Blo 1835619 6199307 := bstep (se 1 (by rfl) ⟨4649480, by rfl⟩ : syracuseStep 6199307 = 9298961) B9298961
theorem B4413473 : Blo 1835619 4413473 := bstep (se 2 (by rfl) ⟨1655052, by rfl⟩ : syracuseStep 4413473 = 3310105) B3310105
theorem B35772509 : Blo 1835619 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B22337653 : Blo 1835619 22337653 := bstep (se 5 (by rfl) ⟨1047077, by rfl⟩ : syracuseStep 22337653 = 2094155) B2094155
theorem B3774583 : Blo 1835619 3774583 := bstep (se 1 (by rfl) ⟨2830937, by rfl⟩ : syracuseStep 3774583 = 5661875) B5661875
theorem B6199415 : Blo 1835619 6199415 := bstep (se 1 (by rfl) ⟨4649561, by rfl⟩ : syracuseStep 6199415 = 9299123) B9299123
theorem B13940909 : Blo 1835619 13940909 := bstep (se 3 (by rfl) ⟨2613920, by rfl⟩ : syracuseStep 13940909 = 5227841) B5227841
theorem B9296045 : Blo 1835619 9296045 := bstep (se 3 (by rfl) ⟨1743008, by rfl⟩ : syracuseStep 9296045 = 3486017) B3486017
theorem B3488015 : Blo 1835619 3488015 := bstep (se 1 (by rfl) ⟨2616011, by rfl⟩ : syracuseStep 3488015 = 5232023) B5232023
theorem B4651465 : Blo 1835619 4651465 := bstep (se 2 (by rfl) ⟨1744299, by rfl⟩ : syracuseStep 4651465 = 3488599) B3488599
theorem B10459601 : Blo 1835619 10459601 := bstep (se 2 (by rfl) ⟨3922350, by rfl⟩ : syracuseStep 10459601 = 7844701) B7844701
theorem B9427517 : Blo 1835619 9427517 := bstep (se 3 (by rfl) ⟨1767659, by rfl⟩ : syracuseStep 9427517 = 3535319) B3535319
theorem B28269121 : Blo 1835619 28269121 := bstep (se 2 (by rfl) ⟨10600920, by rfl⟩ : syracuseStep 28269121 = 21201841) B21201841
theorem B2980471 : Blo 1835619 2980471 := bstep (se 1 (by rfl) ⟨2235353, by rfl⟩ : syracuseStep 2980471 = 4470707) B4470707
theorem B11328173 : Blo 1835619 11328173 := bstep (se 3 (by rfl) ⟨2124032, by rfl⟩ : syracuseStep 11328173 = 4248065) B4248065
theorem B6200009 : Blo 1835619 6200009 := bstep (se 2 (by rfl) ⟨2325003, by rfl⟩ : syracuseStep 6200009 = 4650007) B4650007
theorem B4963513 : Blo 1835619 4963513 := bstep (se 2 (by rfl) ⟨1861317, by rfl⟩ : syracuseStep 4963513 = 3722635) B3722635
theorem B3923129 : Blo 1835619 3923129 := bstep (se 2 (by rfl) ⟨1471173, by rfl⟩ : syracuseStep 3923129 = 2942347) B2942347
theorem B6200711 : Blo 1835619 6200711 := bstep (se 1 (by rfl) ⟨4650533, by rfl⟩ : syracuseStep 6200711 = 9301067) B9301067
theorem B26467793 : Blo 1835619 26467793 := bstep (se 2 (by rfl) ⟨9925422, by rfl⟩ : syracuseStep 26467793 = 19850845) B19850845
theorem B13426141 : Blo 1835619 13426141 := bstep (se 3 (by rfl) ⟨2517401, by rfl⟩ : syracuseStep 13426141 = 5034803) B5034803
theorem B326393347 : Blo 1835619 326393347 := bstep (se 1 (by rfl) ⟨244795010, by rfl⟩ : syracuseStep 326393347 = 489590021) B489590021
theorem B7847435 : Blo 1835619 7847435 := bstep (se 1 (by rfl) ⟨5885576, by rfl⟩ : syracuseStep 7847435 = 11771153) B11771153
theorem B3923471 : Blo 1835619 3923471 := bstep (se 1 (by rfl) ⟨2942603, by rfl⟩ : syracuseStep 3923471 = 5885207) B5885207
theorem B10599979 : Blo 1835619 10599979 := bstep (se 1 (by rfl) ⟨7949984, by rfl⟩ : syracuseStep 10599979 = 15899969) B15899969
theorem B16113271 : Blo 1835619 16113271 := bstep (se 1 (by rfl) ⟨12084953, by rfl⟩ : syracuseStep 16113271 = 24169907) B24169907
theorem B12566135 : Blo 1835619 12566135 := bstep (se 1 (by rfl) ⟨9424601, by rfl⟩ : syracuseStep 12566135 = 18849203) B18849203
theorem B9297665 : Blo 1835619 9297665 := bstep (se 2 (by rfl) ⟨3486624, by rfl⟩ : syracuseStep 9297665 = 6973249) B6973249
theorem B6201089 : Blo 1835619 6201089 := bstep (se 2 (by rfl) ⟨2325408, by rfl⟩ : syracuseStep 6201089 = 4650817) B4650817
theorem B11173691 : Blo 1835619 11173691 := bstep (se 1 (by rfl) ⟨8380268, by rfl⟩ : syracuseStep 11173691 = 16760537) B16760537
theorem B5586749 : Blo 1835619 5586749 := bstep (se 3 (by rfl) ⟨1047515, by rfl⟩ : syracuseStep 5586749 = 2095031) B2095031
theorem B4964183 : Blo 1835619 4964183 := bstep (se 1 (by rfl) ⟨3723137, by rfl⟩ : syracuseStep 4964183 = 7446275) B7446275
theorem B8380307 : Blo 1835619 8380307 := bstep (se 1 (by rfl) ⟨6285230, by rfl⟩ : syracuseStep 8380307 = 12570461) B12570461
theorem B31383449 : Blo 1835619 31383449 := bstep (se 2 (by rfl) ⟨11768793, by rfl⟩ : syracuseStep 31383449 = 23537587) B23537587
theorem B6201359 : Blo 1835619 6201359 := bstep (se 1 (by rfl) ⟨4651019, by rfl⟩ : syracuseStep 6201359 = 9302039) B9302039
theorem B23535947 : Blo 1835619 23535947 := bstep (se 1 (by rfl) ⟨17651960, by rfl⟩ : syracuseStep 23535947 = 35303921) B35303921
theorem B11764055 : Blo 1835619 11764055 := bstep (se 1 (by rfl) ⟨8823041, by rfl⟩ : syracuseStep 11764055 = 17646083) B17646083
theorem B3309931 : Blo 1835619 3309931 := bstep (se 1 (by rfl) ⟨2482448, by rfl⟩ : syracuseStep 3309931 = 4964897) B4964897
theorem B6971777 : Blo 1835619 6971777 := bstep (se 2 (by rfl) ⟨2614416, by rfl⟩ : syracuseStep 6971777 = 5228833) B5228833
theorem B6971791 : Blo 1835619 6971791 := bstep (se 1 (by rfl) ⟨5228843, by rfl⟩ : syracuseStep 6971791 = 10457687) B10457687
theorem B2482697 : Blo 1835619 2482697 := bstep (se 2 (by rfl) ⟨931011, by rfl⟩ : syracuseStep 2482697 = 1862023) B1862023
theorem B6201953 : Blo 1835619 6201953 := bstep (se 2 (by rfl) ⟨2325732, by rfl⟩ : syracuseStep 6201953 = 4651465) B4651465
theorem B1835643 : Blo 1835619 1835643 := bstep (se 1 (by rfl) ⟨1376732, by rfl⟩ : syracuseStep 1835643 = 2753465) B2753465
theorem B1835695 : Blo 1835619 1835695 := bstep (se 1 (by rfl) ⟨1376771, by rfl⟩ : syracuseStep 1835695 = 2753543) B2753543
theorem B1835719 : Blo 1835619 1835719 := bstep (se 1 (by rfl) ⟨1376789, by rfl⟩ : syracuseStep 1835719 = 2753579) B2753579
theorem B1835739 : Blo 1835619 1835739 := bstep (se 1 (by rfl) ⟨1376804, by rfl⟩ : syracuseStep 1835739 = 2753609) B2753609
theorem B37692161 : Blo 1835619 37692161 := bstep (se 2 (by rfl) ⟨14134560, by rfl⟩ : syracuseStep 37692161 = 28269121) B28269121
theorem B7848733 : Blo 1835619 7848733 := bstep (se 3 (by rfl) ⟨1471637, by rfl⟩ : syracuseStep 7848733 = 2943275) B2943275
theorem B1835815 : Blo 1835619 1835815 := bstep (se 1 (by rfl) ⟨1376861, by rfl⟩ : syracuseStep 1835815 = 2753723) B2753723
theorem B3973961 : Blo 1835619 3973961 := bstep (se 2 (by rfl) ⟨1490235, by rfl⟩ : syracuseStep 3973961 = 2980471) B2980471
theorem B1835855 : Blo 1835619 1835855 := bstep (se 1 (by rfl) ⟨1376891, by rfl⟩ : syracuseStep 1835855 = 2753783) B2753783
theorem B1835871 : Blo 1835619 1835871 := bstep (se 1 (by rfl) ⟨1376903, by rfl⟩ : syracuseStep 1835871 = 2753807) B2753807
theorem B1835899 : Blo 1835619 1835899 := bstep (se 1 (by rfl) ⟨1376924, by rfl⟩ : syracuseStep 1835899 = 2753849) B2753849
theorem B1835951 : Blo 1835619 1835951 := bstep (se 1 (by rfl) ⟨1376963, by rfl⟩ : syracuseStep 1835951 = 2753927) B2753927
theorem B1835975 : Blo 1835619 1835975 := bstep (se 1 (by rfl) ⟨1376981, by rfl⟩ : syracuseStep 1835975 = 2753963) B2753963
theorem B1835995 : Blo 1835619 1835995 := bstep (se 1 (by rfl) ⟨1376996, by rfl⟩ : syracuseStep 1835995 = 2753993) B2753993
theorem B4187143 : Blo 1835619 4187143 := bstep (se 1 (by rfl) ⟨3140357, by rfl⟩ : syracuseStep 4187143 = 6280715) B6280715
theorem B1836071 : Blo 1835619 1836071 := bstep (se 1 (by rfl) ⟨1377053, by rfl⟩ : syracuseStep 1836071 = 2754107) B2754107
theorem B2753615 : Blo 1835619 2753615 := bstep (se 1 (by rfl) ⟨2065211, by rfl⟩ : syracuseStep 2753615 = 4130423) B4130423
theorem B1836111 : Blo 1835619 1836111 := bstep (se 1 (by rfl) ⟨1377083, by rfl⟩ : syracuseStep 1836111 = 2754167) B2754167
theorem B1836127 : Blo 1835619 1836127 := bstep (se 1 (by rfl) ⟨1377095, by rfl⟩ : syracuseStep 1836127 = 2754191) B2754191
theorem B6366323 : Blo 1835619 6366323 := bstep (se 1 (by rfl) ⟨4774742, by rfl⟩ : syracuseStep 6366323 = 9549485) B9549485
theorem B3097723 : Blo 1835619 3097723 := bstep (se 1 (by rfl) ⟨2323292, by rfl⟩ : syracuseStep 3097723 = 4646585) B4646585
theorem B2065531 : Blo 1835619 2065531 := bstep (se 1 (by rfl) ⟨1549148, by rfl⟩ : syracuseStep 2065531 = 3098297) B3098297
theorem B1836155 : Blo 1835619 1836155 := bstep (se 1 (by rfl) ⟨1377116, by rfl⟩ : syracuseStep 1836155 = 2754233) B2754233
theorem B1836207 : Blo 1835619 1836207 := bstep (se 1 (by rfl) ⟨1377155, by rfl⟩ : syracuseStep 1836207 = 2754311) B2754311
theorem B2753735 : Blo 1835619 2753735 := bstep (se 1 (by rfl) ⟨2065301, by rfl⟩ : syracuseStep 2753735 = 4130603) B4130603
theorem B1836231 : Blo 1835619 1836231 := bstep (se 1 (by rfl) ⟨1377173, by rfl⟩ : syracuseStep 1836231 = 2754347) B2754347
theorem B1836251 : Blo 1835619 1836251 := bstep (se 1 (by rfl) ⟨1377188, by rfl⟩ : syracuseStep 1836251 = 2754377) B2754377
theorem B1836327 : Blo 1835619 1836327 := bstep (se 1 (by rfl) ⟨1377245, by rfl⟩ : syracuseStep 1836327 = 2754491) B2754491
theorem B1836367 : Blo 1835619 1836367 := bstep (se 1 (by rfl) ⟨1377275, by rfl⟩ : syracuseStep 1836367 = 2754551) B2754551
theorem B1836383 : Blo 1835619 1836383 := bstep (se 1 (by rfl) ⟨1377287, by rfl⟩ : syracuseStep 1836383 = 2754575) B2754575
theorem B4130153 : Blo 1835619 4130153 := bstep (se 2 (by rfl) ⟨1548807, by rfl⟩ : syracuseStep 4130153 = 3097615) B3097615
theorem B2753897 : Blo 1835619 2753897 := bstep (se 2 (by rfl) ⟨1032711, by rfl⟩ : syracuseStep 2753897 = 2065423) B2065423
theorem B2942315 : Blo 1835619 2942315 := bstep (se 1 (by rfl) ⟨2206736, by rfl⟩ : syracuseStep 2942315 = 4413473) B4413473
theorem B1836411 : Blo 1835619 1836411 := bstep (se 1 (by rfl) ⟨1377308, by rfl⟩ : syracuseStep 1836411 = 2754617) B2754617
theorem B23848339 : Blo 1835619 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B1836463 : Blo 1835619 1836463 := bstep (se 1 (by rfl) ⟨1377347, by rfl⟩ : syracuseStep 1836463 = 2754695) B2754695
theorem B2753975 : Blo 1835619 2753975 := bstep (se 1 (by rfl) ⟨2065481, by rfl⟩ : syracuseStep 2753975 = 4130963) B4130963
theorem B1836487 : Blo 1835619 1836487 := bstep (se 1 (by rfl) ⟨1377365, by rfl⟩ : syracuseStep 1836487 = 2754731) B2754731
theorem B2754011 : Blo 1835619 2754011 := bstep (se 1 (by rfl) ⟨2065508, by rfl⟩ : syracuseStep 2754011 = 4131017) B4131017
theorem B1836507 : Blo 1835619 1836507 := bstep (se 1 (by rfl) ⟨1377380, by rfl⟩ : syracuseStep 1836507 = 2754761) B2754761
theorem B5883425 : Blo 1835619 5883425 := bstep (se 2 (by rfl) ⟨2206284, by rfl⟩ : syracuseStep 5883425 = 4412569) B4412569
theorem B1836583 : Blo 1835619 1836583 := bstep (se 1 (by rfl) ⟨1377437, by rfl⟩ : syracuseStep 1836583 = 2754875) B2754875
theorem B13952573 : Blo 1835619 13952573 := bstep (se 3 (by rfl) ⟨2616107, by rfl⟩ : syracuseStep 13952573 = 5232215) B5232215
theorem B2065999 : Blo 1835619 2065999 := bstep (se 1 (by rfl) ⟨1549499, by rfl⟩ : syracuseStep 2065999 = 3098999) B3098999
theorem B1836623 : Blo 1835619 1836623 := bstep (se 1 (by rfl) ⟨1377467, by rfl⟩ : syracuseStep 1836623 = 2754935) B2754935
theorem B1836639 : Blo 1835619 1836639 := bstep (se 1 (by rfl) ⟨1377479, by rfl⟩ : syracuseStep 1836639 = 2754959) B2754959
theorem B1836667 : Blo 1835619 1836667 := bstep (se 1 (by rfl) ⟨1377500, by rfl⟩ : syracuseStep 1836667 = 2755001) B2755001
theorem B6973067 : Blo 1835619 6973067 := bstep (se 1 (by rfl) ⟨5229800, by rfl⟩ : syracuseStep 6973067 = 10459601) B10459601
theorem B1836719 : Blo 1835619 1836719 := bstep (se 1 (by rfl) ⟨1377539, by rfl⟩ : syracuseStep 1836719 = 2755079) B2755079
theorem B1836743 : Blo 1835619 1836743 := bstep (se 1 (by rfl) ⟨1377557, by rfl⟩ : syracuseStep 1836743 = 2755115) B2755115
theorem B6285011 : Blo 1835619 6285011 := bstep (se 1 (by rfl) ⟨4713758, by rfl⟩ : syracuseStep 6285011 = 9427517) B9427517
theorem B1836763 : Blo 1835619 1836763 := bstep (se 1 (by rfl) ⟨1377572, by rfl⟩ : syracuseStep 1836763 = 2755145) B2755145
theorem B1836839 : Blo 1835619 1836839 := bstep (se 1 (by rfl) ⟨1377629, by rfl⟩ : syracuseStep 1836839 = 2755259) B2755259
theorem B4966217 : Blo 1835619 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B1836879 : Blo 1835619 1836879 := bstep (se 1 (by rfl) ⟨1377659, by rfl⟩ : syracuseStep 1836879 = 2755319) B2755319
theorem B1836895 : Blo 1835619 1836895 := bstep (se 1 (by rfl) ⟨1377671, by rfl⟩ : syracuseStep 1836895 = 2755343) B2755343
theorem B12912493 : Blo 1835619 12912493 := bstep (se 3 (by rfl) ⟨2421092, by rfl⟩ : syracuseStep 12912493 = 4842185) B4842185
theorem B1836923 : Blo 1835619 1836923 := bstep (se 1 (by rfl) ⟨1377692, by rfl⟩ : syracuseStep 1836923 = 2755385) B2755385
theorem B2754479 : Blo 1835619 2754479 := bstep (se 1 (by rfl) ⟨2065859, by rfl⟩ : syracuseStep 2754479 = 4131719) B4131719
theorem B1836975 : Blo 1835619 1836975 := bstep (se 1 (by rfl) ⟨1377731, by rfl⟩ : syracuseStep 1836975 = 2755463) B2755463
theorem B4130747 : Blo 1835619 4130747 := bstep (se 1 (by rfl) ⟨3098060, by rfl⟩ : syracuseStep 4130747 = 6196121) B6196121
theorem B1836999 : Blo 1835619 1836999 := bstep (se 1 (by rfl) ⟨1377749, by rfl⟩ : syracuseStep 1836999 = 2755499) B2755499
theorem B17901521 : Blo 1835619 17901521 := bstep (se 2 (by rfl) ⟨6713070, by rfl⟩ : syracuseStep 17901521 = 13426141) B13426141
theorem B3098587 : Blo 1835619 3098587 := bstep (se 1 (by rfl) ⟨2323940, by rfl⟩ : syracuseStep 3098587 = 4647881) B4647881
theorem B2066395 : Blo 1835619 2066395 := bstep (se 1 (by rfl) ⟨1549796, by rfl⟩ : syracuseStep 2066395 = 3099593) B3099593
theorem B1837019 : Blo 1835619 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B5883911 : Blo 1835619 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B2754569 : Blo 1835619 2754569 := bstep (se 2 (by rfl) ⟨1032963, by rfl⟩ : syracuseStep 2754569 = 2065927) B2065927
theorem B6621203 : Blo 1835619 6621203 := bstep (se 1 (by rfl) ⟨4965902, by rfl⟩ : syracuseStep 6621203 = 9931805) B9931805
theorem B2754599 : Blo 1835619 2754599 := bstep (se 1 (by rfl) ⟨2065949, by rfl⟩ : syracuseStep 2754599 = 4131899) B4131899
theorem B1837095 : Blo 1835619 1837095 := bstep (se 1 (by rfl) ⟨1377821, by rfl⟩ : syracuseStep 1837095 = 2755643) B2755643
theorem B6195257 : Blo 1835619 6195257 := bstep (se 2 (by rfl) ⟨2323221, by rfl⟩ : syracuseStep 6195257 = 4646443) B4646443
theorem B4130873 : Blo 1835619 4130873 := bstep (se 2 (by rfl) ⟨1549077, by rfl⟩ : syracuseStep 4130873 = 3098155) B3098155
theorem B14133305 : Blo 1835619 14133305 := bstep (se 2 (by rfl) ⟨5299989, by rfl⟩ : syracuseStep 14133305 = 10599979) B10599979
theorem B1837135 : Blo 1835619 1837135 := bstep (se 1 (by rfl) ⟨1377851, by rfl⟩ : syracuseStep 1837135 = 2755703) B2755703
theorem B9930833 : Blo 1835619 9930833 := bstep (se 2 (by rfl) ⟨3724062, by rfl⟩ : syracuseStep 9930833 = 7448125) B7448125
theorem B1837151 : Blo 1835619 1837151 := bstep (se 1 (by rfl) ⟨1377863, by rfl⟩ : syracuseStep 1837151 = 2755727) B2755727
theorem B2754683 : Blo 1835619 2754683 := bstep (se 1 (by rfl) ⟨2066012, by rfl⟩ : syracuseStep 2754683 = 4132025) B4132025
theorem B2615419 : Blo 1835619 2615419 := bstep (se 1 (by rfl) ⟨1961564, by rfl⟩ : syracuseStep 2615419 = 3923129) B3923129
theorem B1837179 : Blo 1835619 1837179 := bstep (se 1 (by rfl) ⟨1377884, by rfl⟩ : syracuseStep 1837179 = 2755769) B2755769
theorem B1837231 : Blo 1835619 1837231 := bstep (se 1 (by rfl) ⟨1377923, by rfl⟩ : syracuseStep 1837231 = 2755847) B2755847
theorem B1837255 : Blo 1835619 1837255 := bstep (se 1 (by rfl) ⟨1377941, by rfl⟩ : syracuseStep 1837255 = 2755883) B2755883
theorem B1837275 : Blo 1835619 1837275 := bstep (se 1 (by rfl) ⟨1377956, by rfl⟩ : syracuseStep 1837275 = 2755913) B2755913
theorem B2754809 : Blo 1835619 2754809 := bstep (se 2 (by rfl) ⟨1033053, by rfl⟩ : syracuseStep 2754809 = 2066107) B2066107
theorem B1837351 : Blo 1835619 1837351 := bstep (se 1 (by rfl) ⟨1378013, by rfl⟩ : syracuseStep 1837351 = 2756027) B2756027
theorem B1837391 : Blo 1835619 1837391 := bstep (se 1 (by rfl) ⟨1378043, by rfl⟩ : syracuseStep 1837391 = 2756087) B2756087
theorem B2754911 : Blo 1835619 2754911 := bstep (se 1 (by rfl) ⟨2066183, by rfl⟩ : syracuseStep 2754911 = 4132367) B4132367
theorem B2615647 : Blo 1835619 2615647 := bstep (se 1 (by rfl) ⟨1961735, by rfl⟩ : syracuseStep 2615647 = 3923471) B3923471
theorem B1837407 : Blo 1835619 1837407 := bstep (se 1 (by rfl) ⟨1378055, by rfl⟩ : syracuseStep 1837407 = 2756111) B2756111
theorem B2754923 : Blo 1835619 2754923 := bstep (se 1 (by rfl) ⟨2066192, by rfl⟩ : syracuseStep 2754923 = 4132385) B4132385
theorem B1837435 : Blo 1835619 1837435 := bstep (se 1 (by rfl) ⟨1378076, by rfl⟩ : syracuseStep 1837435 = 2756153) B2756153
theorem B6195581 : Blo 1835619 6195581 := bstep (se 3 (by rfl) ⟨1161671, by rfl⟩ : syracuseStep 6195581 = 2323343) B2323343
theorem B4131215 : Blo 1835619 4131215 := bstep (se 1 (by rfl) ⟨3098411, by rfl⟩ : syracuseStep 4131215 = 6196823) B6196823
theorem B2066863 : Blo 1835619 2066863 := bstep (se 1 (by rfl) ⟨1550147, by rfl⟩ : syracuseStep 2066863 = 3100295) B3100295
theorem B1837487 : Blo 1835619 1837487 := bstep (se 1 (by rfl) ⟨1378115, by rfl⟩ : syracuseStep 1837487 = 2756231) B2756231
theorem B1837511 : Blo 1835619 1837511 := bstep (se 1 (by rfl) ⟨1378133, by rfl⟩ : syracuseStep 1837511 = 2756267) B2756267
theorem B1837531 : Blo 1835619 1837531 := bstep (se 1 (by rfl) ⟨1378148, by rfl⟩ : syracuseStep 1837531 = 2756297) B2756297
theorem B13953545 : Blo 1835619 13953545 := bstep (se 2 (by rfl) ⟨5232579, by rfl⟩ : syracuseStep 13953545 = 10465159) B10465159
theorem B7449127 : Blo 1835619 7449127 := bstep (se 1 (by rfl) ⟨5586845, by rfl⟩ : syracuseStep 7449127 = 11173691) B11173691
theorem B1837607 : Blo 1835619 1837607 := bstep (se 1 (by rfl) ⟨1378205, by rfl⟩ : syracuseStep 1837607 = 2756411) B2756411
theorem B3099215 : Blo 1835619 3099215 := bstep (se 1 (by rfl) ⟨2324411, by rfl⟩ : syracuseStep 3099215 = 4648823) B4648823
theorem B2755151 : Blo 1835619 2755151 := bstep (se 1 (by rfl) ⟨2066363, by rfl⟩ : syracuseStep 2755151 = 4132727) B4132727
theorem B6195851 : Blo 1835619 6195851 := bstep (se 1 (by rfl) ⟨4646888, by rfl⟩ : syracuseStep 6195851 = 9293777) B9293777
theorem B11168441 : Blo 1835619 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B2755271 : Blo 1835619 2755271 := bstep (se 1 (by rfl) ⟨2066453, by rfl⟩ : syracuseStep 2755271 = 4132907) B4132907
theorem B4131539 : Blo 1835619 4131539 := bstep (se 1 (by rfl) ⟨3098654, by rfl⟩ : syracuseStep 4131539 = 6197309) B6197309
theorem B5032777 : Blo 1835619 5032777 := bstep (se 2 (by rfl) ⟨1887291, by rfl⟩ : syracuseStep 5032777 = 3774583) B3774583
theorem B2067295 : Blo 1835619 2067295 := bstep (se 1 (by rfl) ⟨1550471, by rfl⟩ : syracuseStep 2067295 = 3100943) B3100943
theorem B2755433 : Blo 1835619 2755433 := bstep (se 2 (by rfl) ⟨1033287, by rfl⟩ : syracuseStep 2755433 = 2066575) B2066575
theorem B2616239 : Blo 1835619 2616239 := bstep (se 1 (by rfl) ⟨1962179, by rfl⟩ : syracuseStep 2616239 = 3924359) B3924359
theorem B2755511 : Blo 1835619 2755511 := bstep (se 1 (by rfl) ⟨2066633, by rfl⟩ : syracuseStep 2755511 = 4133267) B4133267
theorem B2755547 : Blo 1835619 2755547 := bstep (se 1 (by rfl) ⟨2066660, by rfl⟩ : syracuseStep 2755547 = 4133321) B4133321
theorem B3533843 : Blo 1835619 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B6286355 : Blo 1835619 6286355 := bstep (se 1 (by rfl) ⟨4714766, by rfl⟩ : syracuseStep 6286355 = 9429533) B9429533
theorem B3583055 : Blo 1835619 3583055 := bstep (se 1 (by rfl) ⟨2687291, by rfl⟩ : syracuseStep 3583055 = 5374583) B5374583
theorem B28281935 : Blo 1835619 28281935 := bstep (se 1 (by rfl) ⟨21211451, by rfl⟩ : syracuseStep 28281935 = 42422903) B42422903
theorem B13946255 : Blo 1835619 13946255 := bstep (se 1 (by rfl) ⟨10459691, by rfl⟩ : syracuseStep 13946255 = 20919383) B20919383
theorem B9301391 : Blo 1835619 9301391 := bstep (se 1 (by rfl) ⟨6976043, by rfl⟩ : syracuseStep 9301391 = 13952087) B13952087
theorem B22351277 : Blo 1835619 22351277 := bstep (se 3 (by rfl) ⟨4190864, by rfl⟩ : syracuseStep 22351277 = 8381729) B8381729
theorem B3100079 : Blo 1835619 3100079 := bstep (se 1 (by rfl) ⟨2325059, by rfl⟩ : syracuseStep 3100079 = 4650119) B4650119
theorem B2756015 : Blo 1835619 2756015 := bstep (se 1 (by rfl) ⟨2067011, by rfl⟩ : syracuseStep 2756015 = 4134023) B4134023
theorem B2756105 : Blo 1835619 2756105 := bstep (se 2 (by rfl) ⟨1033539, by rfl⟩ : syracuseStep 2756105 = 2067079) B2067079
theorem B6196769 : Blo 1835619 6196769 := bstep (se 2 (by rfl) ⟨2323788, by rfl⟩ : syracuseStep 6196769 = 4647577) B4647577
theorem B2756135 : Blo 1835619 2756135 := bstep (se 1 (by rfl) ⟨2067101, by rfl⟩ : syracuseStep 2756135 = 4134203) B4134203
theorem B3485281 : Blo 1835619 3485281 := bstep (se 2 (by rfl) ⟨1306980, by rfl⟩ : syracuseStep 3485281 = 2613961) B2613961
theorem B5582459 : Blo 1835619 5582459 := bstep (se 1 (by rfl) ⟨4186844, by rfl⟩ : syracuseStep 5582459 = 8373689) B8373689
theorem B4132475 : Blo 1835619 4132475 := bstep (se 1 (by rfl) ⟨3099356, by rfl⟩ : syracuseStep 4132475 = 6198713) B6198713
theorem B2756219 : Blo 1835619 2756219 := bstep (se 1 (by rfl) ⟨2067164, by rfl⟩ : syracuseStep 2756219 = 4134329) B4134329
theorem B5230291 : Blo 1835619 5230291 := bstep (se 1 (by rfl) ⟨3922718, by rfl⟩ : syracuseStep 5230291 = 7845437) B7845437
theorem B6196985 : Blo 1835619 6196985 := bstep (se 2 (by rfl) ⟨2323869, by rfl⟩ : syracuseStep 6196985 = 4647739) B4647739
theorem B4132601 : Blo 1835619 4132601 := bstep (se 2 (by rfl) ⟨1549725, by rfl⟩ : syracuseStep 4132601 = 3099451) B3099451
theorem B2756345 : Blo 1835619 2756345 := bstep (se 2 (by rfl) ⟨1033629, by rfl⟩ : syracuseStep 2756345 = 2067259) B2067259
theorem B3100511 : Blo 1835619 3100511 := bstep (se 1 (by rfl) ⟨2325383, by rfl⟩ : syracuseStep 3100511 = 4650767) B4650767
theorem B6197255 : Blo 1835619 6197255 := bstep (se 1 (by rfl) ⟨4647941, by rfl⟩ : syracuseStep 6197255 = 9295883) B9295883
theorem B4132871 : Blo 1835619 4132871 := bstep (se 1 (by rfl) ⟨3099653, by rfl⟩ : syracuseStep 4132871 = 6199307) B6199307
theorem B4132943 : Blo 1835619 4132943 := bstep (se 1 (by rfl) ⟨3099707, by rfl⟩ : syracuseStep 4132943 = 6199415) B6199415
theorem B9293939 : Blo 1835619 9293939 := bstep (se 1 (by rfl) ⟨6970454, by rfl⟩ : syracuseStep 9293939 = 13940909) B13940909
theorem B6197363 : Blo 1835619 6197363 := bstep (se 1 (by rfl) ⟨4648022, by rfl⟩ : syracuseStep 6197363 = 9296045) B9296045
theorem B33509693 : Blo 1835619 33509693 := bstep (se 3 (by rfl) ⟨6283067, by rfl⟩ : syracuseStep 33509693 = 12566135) B12566135
theorem B2093407 : Blo 1835619 2093407 := bstep (se 1 (by rfl) ⟨1570055, by rfl⟩ : syracuseStep 2093407 = 3140111) B3140111
theorem B6197633 : Blo 1835619 6197633 := bstep (se 2 (by rfl) ⟨2324112, by rfl⟩ : syracuseStep 6197633 = 4648225) B4648225
theorem B4649359 : Blo 1835619 4649359 := bstep (se 1 (by rfl) ⟨3487019, by rfl⟩ : syracuseStep 4649359 = 6974039) B6974039
theorem B4133339 : Blo 1835619 4133339 := bstep (se 1 (by rfl) ⟨3100004, by rfl⟩ : syracuseStep 4133339 = 6200009) B6200009
theorem B3486215 : Blo 1835619 3486215 := bstep (se 1 (by rfl) ⟨2614661, by rfl⟩ : syracuseStep 3486215 = 5229323) B5229323
theorem B4649683 : Blo 1835619 4649683 := bstep (se 1 (by rfl) ⟨3487262, by rfl⟩ : syracuseStep 4649683 = 6974525) B6974525
theorem B7443193 : Blo 1835619 7443193 := bstep (se 2 (by rfl) ⟨2791197, by rfl⟩ : syracuseStep 7443193 = 5582395) B5582395
theorem B21484361 : Blo 1835619 21484361 := bstep (se 2 (by rfl) ⟨8056635, by rfl⟩ : syracuseStep 21484361 = 16113271) B16113271
theorem B4133807 : Blo 1835619 4133807 := bstep (se 1 (by rfl) ⟨3100355, by rfl⟩ : syracuseStep 4133807 = 6200711) B6200711
theorem B6976439 : Blo 1835619 6976439 := bstep (se 1 (by rfl) ⟨5232329, by rfl⟩ : syracuseStep 6976439 = 10464659) B10464659
theorem B5231623 : Blo 1835619 5231623 := bstep (se 1 (by rfl) ⟨3923717, by rfl⟩ : syracuseStep 5231623 = 7847435) B7847435
theorem B3486739 : Blo 1835619 3486739 := bstep (se 1 (by rfl) ⟨2615054, by rfl⟩ : syracuseStep 3486739 = 5230109) B5230109
theorem B2323495 : Blo 1835619 2323495 := bstep (se 1 (by rfl) ⟨1742621, by rfl⟩ : syracuseStep 2323495 = 3485243) B3485243
theorem B10892339 : Blo 1835619 10892339 := bstep (se 1 (by rfl) ⟨8169254, by rfl⟩ : syracuseStep 10892339 = 16338509) B16338509
theorem B6198443 : Blo 1835619 6198443 := bstep (se 1 (by rfl) ⟨4648832, by rfl⟩ : syracuseStep 6198443 = 9297665) B9297665
theorem B4134059 : Blo 1835619 4134059 := bstep (se 1 (by rfl) ⟨3100544, by rfl⟩ : syracuseStep 4134059 = 6201089) B6201089
theorem B3724499 : Blo 1835619 3724499 := bstep (se 1 (by rfl) ⟨2793374, by rfl⟩ : syracuseStep 3724499 = 5586749) B5586749
theorem B3921257 : Blo 1835619 3921257 := bstep (se 2 (by rfl) ⟨1470471, by rfl⟩ : syracuseStep 3921257 = 2940943) B2940943
theorem B2323819 : Blo 1835619 2323819 := bstep (se 1 (by rfl) ⟨1742864, by rfl⟩ : syracuseStep 2323819 = 3485729) B3485729
theorem B42407387 : Blo 1835619 42407387 := bstep (se 1 (by rfl) ⟨31805540, by rfl⟩ : syracuseStep 42407387 = 63611081) B63611081
theorem B29783537 : Blo 1835619 29783537 := bstep (se 2 (by rfl) ⟨11168826, by rfl⟩ : syracuseStep 29783537 = 22337653) B22337653
theorem B2324047 : Blo 1835619 2324047 := bstep (se 1 (by rfl) ⟨1743035, by rfl⟩ : syracuseStep 2324047 = 3486071) B3486071
theorem B4650635 : Blo 1835619 4650635 := bstep (se 1 (by rfl) ⟨3487976, by rfl⟩ : syracuseStep 4650635 = 6975953) B6975953
theorem B9926333 : Blo 1835619 9926333 := bstep (se 3 (by rfl) ⟨1861187, by rfl⟩ : syracuseStep 9926333 = 3722375) B3722375
theorem B13940423 : Blo 1835619 13940423 := bstep (se 1 (by rfl) ⟨10455317, by rfl⟩ : syracuseStep 13940423 = 20910635) B20910635
theorem B9295559 : Blo 1835619 9295559 := bstep (se 1 (by rfl) ⟨6971669, by rfl⟩ : syracuseStep 9295559 = 13943339) B13943339
theorem B6198983 : Blo 1835619 6198983 := bstep (se 1 (by rfl) ⟨4649237, by rfl⟩ : syracuseStep 6198983 = 9298475) B9298475
theorem B4134599 : Blo 1835619 4134599 := bstep (se 1 (by rfl) ⟨3100949, by rfl⟩ : syracuseStep 4134599 = 6201899) B6201899
theorem B11761595 : Blo 1835619 11761595 := bstep (se 1 (by rfl) ⟨8821196, by rfl⟩ : syracuseStep 11761595 = 17642393) B17642393
theorem B18848051 : Blo 1835619 18848051 := bstep (se 1 (by rfl) ⟨14136038, by rfl⟩ : syracuseStep 18848051 = 28272077) B28272077
theorem B7846409 : Blo 1835619 7846409 := bstep (se 2 (by rfl) ⟨2942403, by rfl⟩ : syracuseStep 7846409 = 5884807) B5884807
theorem B11328025 : Blo 1835619 11328025 := bstep (se 2 (by rfl) ⟨4248009, by rfl⟩ : syracuseStep 11328025 = 8496019) B8496019
theorem B6199847 : Blo 1835619 6199847 := bstep (se 1 (by rfl) ⟨4649885, by rfl⟩ : syracuseStep 6199847 = 9299771) B9299771
theorem B17652269 : Blo 1835619 17652269 := bstep (se 3 (by rfl) ⟨3309800, by rfl⟩ : syracuseStep 17652269 = 6619601) B6619601
theorem B2325115 : Blo 1835619 2325115 := bstep (se 1 (by rfl) ⟨1743836, by rfl⟩ : syracuseStep 2325115 = 3487673) B3487673
theorem B6199955 : Blo 1835619 6199955 := bstep (se 1 (by rfl) ⟨4649966, by rfl⟩ : syracuseStep 6199955 = 9299933) B9299933
theorem B2325343 : Blo 1835619 2325343 := bstep (se 1 (by rfl) ⟨1744007, by rfl⟩ : syracuseStep 2325343 = 3488015) B3488015
theorem B6200171 : Blo 1835619 6200171 := bstep (se 1 (by rfl) ⟨4650128, by rfl⟩ : syracuseStep 6200171 = 9300257) B9300257
theorem B6618017 : Blo 1835619 6618017 := bstep (se 2 (by rfl) ⟨2481756, by rfl⟩ : syracuseStep 6618017 = 4963513) B4963513
theorem B6200225 : Blo 1835619 6200225 := bstep (se 2 (by rfl) ⟨2325084, by rfl⟩ : syracuseStep 6200225 = 4650169) B4650169
theorem B21502903 : Blo 1835619 21502903 := bstep (se 1 (by rfl) ⟨16127177, by rfl⟩ : syracuseStep 21502903 = 32254355) B32254355
theorem B8166419 : Blo 1835619 8166419 := bstep (se 1 (by rfl) ⟨6124814, by rfl⟩ : syracuseStep 8166419 = 12249629) B12249629
theorem B8821811 : Blo 1835619 8821811 := bstep (se 1 (by rfl) ⟨6616358, by rfl⟩ : syracuseStep 8821811 = 13232717) B13232717
theorem B7552115 : Blo 1835619 7552115 := bstep (se 1 (by rfl) ⟨5664086, by rfl⟩ : syracuseStep 7552115 = 11328173) B11328173
theorem B435191129 : Blo 1835619 435191129 := bstep (se 2 (by rfl) ⟨163196673, by rfl⟩ : syracuseStep 435191129 = 326393347) B326393347
theorem B20913551 : Blo 1835619 20913551 := bstep (se 1 (by rfl) ⟨15685163, by rfl⟩ : syracuseStep 20913551 = 31370327) B31370327
theorem B6200819 : Blo 1835619 6200819 := bstep (se 1 (by rfl) ⟨4650614, by rfl⟩ : syracuseStep 6200819 = 9301229) B9301229
theorem B29793911 : Blo 1835619 29793911 := bstep (se 1 (by rfl) ⟨22345433, by rfl⟩ : syracuseStep 29793911 = 44690867) B44690867
theorem B17645195 : Blo 1835619 17645195 := bstep (se 1 (by rfl) ⟨13233896, by rfl⟩ : syracuseStep 17645195 = 26467793) B26467793
theorem B9428669 : Blo 1835619 9428669 := bstep (se 3 (by rfl) ⟨1767875, by rfl⟩ : syracuseStep 9428669 = 3535751) B3535751
theorem B22347485 : Blo 1835619 22347485 := bstep (se 3 (by rfl) ⟨4190153, by rfl⟩ : syracuseStep 22347485 = 8380307) B8380307
theorem B2940815 : Blo 1835619 2940815 := bstep (se 1 (by rfl) ⟨2205611, by rfl⟩ : syracuseStep 2940815 = 4411223) B4411223
theorem B3309455 : Blo 1835619 3309455 := bstep (se 1 (by rfl) ⟨2482091, by rfl⟩ : syracuseStep 3309455 = 4964183) B4964183
theorem B29777827 : Blo 1835619 29777827 := bstep (se 1 (by rfl) ⟨22333370, by rfl⟩ : syracuseStep 29777827 = 44666741) B44666741
theorem B2482103 : Blo 1835619 2482103 := bstep (se 1 (by rfl) ⟨1861577, by rfl⟩ : syracuseStep 2482103 = 3723155) B3723155
theorem B20922299 : Blo 1835619 20922299 := bstep (se 1 (by rfl) ⟨15691724, by rfl⟩ : syracuseStep 20922299 = 31383449) B31383449
theorem B22339795 : Blo 1835619 22339795 := bstep (se 1 (by rfl) ⟨16754846, by rfl⟩ : syracuseStep 22339795 = 33509693) B33509693
theorem B1835743 : Blo 1835619 1835743 := bstep (se 1 (by rfl) ⟨1376807, by rfl⟩ : syracuseStep 1835743 = 2753615) B2753615
theorem B1835823 : Blo 1835619 1835823 := bstep (se 1 (by rfl) ⟨1376867, by rfl⟩ : syracuseStep 1835823 = 2753735) B2753735
theorem B2753435 : Blo 1835619 2753435 := bstep (se 1 (by rfl) ⟨2065076, by rfl⟩ : syracuseStep 2753435 = 4130153) B4130153
theorem B1835931 : Blo 1835619 1835931 := bstep (se 1 (by rfl) ⟨1376948, by rfl⟩ : syracuseStep 1835931 = 2753897) B2753897
theorem B1835983 : Blo 1835619 1835983 := bstep (se 1 (by rfl) ⟨1376987, by rfl⟩ : syracuseStep 1835983 = 2753975) B2753975
theorem B1836007 : Blo 1835619 1836007 := bstep (se 1 (by rfl) ⟨1377005, by rfl⟩ : syracuseStep 1836007 = 2754011) B2754011
theorem B28271591 : Blo 1835619 28271591 := bstep (se 1 (by rfl) ⟨21203693, by rfl⟩ : syracuseStep 28271591 = 42407387) B42407387
theorem B6710369 : Blo 1835619 6710369 := bstep (se 2 (by rfl) ⟨2516388, by rfl⟩ : syracuseStep 6710369 = 5032777) B5032777
theorem B3310811 : Blo 1835619 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B1836319 : Blo 1835619 1836319 := bstep (se 1 (by rfl) ⟨1377239, by rfl⟩ : syracuseStep 1836319 = 2754479) B2754479
theorem B7841063 : Blo 1835619 7841063 := bstep (se 1 (by rfl) ⟨5880797, by rfl⟩ : syracuseStep 7841063 = 11761595) B11761595
theorem B2753831 : Blo 1835619 2753831 := bstep (se 1 (by rfl) ⟨2065373, by rfl⟩ : syracuseStep 2753831 = 4130747) B4130747
theorem B1836379 : Blo 1835619 1836379 := bstep (se 1 (by rfl) ⟨1377284, by rfl⟩ : syracuseStep 1836379 = 2754569) B2754569
theorem B20923757 : Blo 1835619 20923757 := bstep (se 3 (by rfl) ⟨3923204, by rfl⟩ : syracuseStep 20923757 = 7846409) B7846409
theorem B6620525 : Blo 1835619 6620525 := bstep (se 3 (by rfl) ⟨1241348, by rfl⟩ : syracuseStep 6620525 = 2482697) B2482697
theorem B1836399 : Blo 1835619 1836399 := bstep (se 1 (by rfl) ⟨1377299, by rfl⟩ : syracuseStep 1836399 = 2754599) B2754599
theorem B4130171 : Blo 1835619 4130171 := bstep (se 1 (by rfl) ⟨3097628, by rfl⟩ : syracuseStep 4130171 = 6195257) B6195257
theorem B2753915 : Blo 1835619 2753915 := bstep (se 1 (by rfl) ⟨2065436, by rfl⟩ : syracuseStep 2753915 = 4130873) B4130873
theorem B3097993 : Blo 1835619 3097993 := bstep (se 2 (by rfl) ⟨1161747, by rfl⟩ : syracuseStep 3097993 = 2323495) B2323495
theorem B6620555 : Blo 1835619 6620555 := bstep (se 1 (by rfl) ⟨4965416, by rfl⟩ : syracuseStep 6620555 = 9930833) B9930833
theorem B1836455 : Blo 1835619 1836455 := bstep (se 1 (by rfl) ⟨1377341, by rfl⟩ : syracuseStep 1836455 = 2754683) B2754683
theorem B4130297 : Blo 1835619 4130297 := bstep (se 2 (by rfl) ⟨1548861, by rfl⟩ : syracuseStep 4130297 = 3097723) B3097723
theorem B2754041 : Blo 1835619 2754041 := bstep (se 2 (by rfl) ⟨1032765, by rfl⟩ : syracuseStep 2754041 = 2065531) B2065531
theorem B1836539 : Blo 1835619 1836539 := bstep (se 1 (by rfl) ⟨1377404, by rfl⟩ : syracuseStep 1836539 = 2754809) B2754809
theorem B1836607 : Blo 1835619 1836607 := bstep (se 1 (by rfl) ⟨1377455, by rfl⟩ : syracuseStep 1836607 = 2754911) B2754911
theorem B1836615 : Blo 1835619 1836615 := bstep (se 1 (by rfl) ⟨1377461, by rfl⟩ : syracuseStep 1836615 = 2754923) B2754923
theorem B4130387 : Blo 1835619 4130387 := bstep (se 1 (by rfl) ⟨3097790, by rfl⟩ : syracuseStep 4130387 = 6195581) B6195581
theorem B2754143 : Blo 1835619 2754143 := bstep (se 1 (by rfl) ⟨2065607, by rfl⟩ : syracuseStep 2754143 = 4131215) B4131215
theorem B2066143 : Blo 1835619 2066143 := bstep (se 1 (by rfl) ⟨1549607, by rfl⟩ : syracuseStep 2066143 = 3099215) B3099215
theorem B1836767 : Blo 1835619 1836767 := bstep (se 1 (by rfl) ⟨1377575, by rfl⟩ : syracuseStep 1836767 = 2755151) B2755151
theorem B4130567 : Blo 1835619 4130567 := bstep (se 1 (by rfl) ⟨3097925, by rfl⟩ : syracuseStep 4130567 = 6195851) B6195851
theorem B1836847 : Blo 1835619 1836847 := bstep (se 1 (by rfl) ⟨1377635, by rfl⟩ : syracuseStep 1836847 = 2755271) B2755271
theorem B2754359 : Blo 1835619 2754359 := bstep (se 1 (by rfl) ⟨2065769, by rfl⟩ : syracuseStep 2754359 = 4131539) B4131539
theorem B3098425 : Blo 1835619 3098425 := bstep (se 2 (by rfl) ⟨1161909, by rfl⟩ : syracuseStep 3098425 = 2323819) B2323819
theorem B1836955 : Blo 1835619 1836955 := bstep (se 1 (by rfl) ⟨1377716, by rfl⟩ : syracuseStep 1836955 = 2755433) B2755433
theorem B1837007 : Blo 1835619 1837007 := bstep (se 1 (by rfl) ⟨1377755, by rfl⟩ : syracuseStep 1837007 = 2755511) B2755511
theorem B1837031 : Blo 1835619 1837031 := bstep (se 1 (by rfl) ⟨1377773, by rfl⟩ : syracuseStep 1837031 = 2755547) B2755547
theorem B3098729 : Blo 1835619 3098729 := bstep (se 2 (by rfl) ⟨1162023, by rfl⟩ : syracuseStep 3098729 = 2324047) B2324047
theorem B2754665 : Blo 1835619 2754665 := bstep (se 2 (by rfl) ⟨1032999, by rfl⟩ : syracuseStep 2754665 = 2065999) B2065999
theorem B4647041 : Blo 1835619 4647041 := bstep (se 2 (by rfl) ⟨1742640, by rfl⟩ : syracuseStep 4647041 = 3485281) B3485281
theorem B6973721 : Blo 1835619 6973721 := bstep (se 2 (by rfl) ⟨2615145, by rfl⟩ : syracuseStep 6973721 = 5230291) B5230291
theorem B2066719 : Blo 1835619 2066719 := bstep (se 1 (by rfl) ⟨1550039, by rfl⟩ : syracuseStep 2066719 = 3100079) B3100079
theorem B1837403 : Blo 1835619 1837403 := bstep (se 1 (by rfl) ⟨1378052, by rfl⟩ : syracuseStep 1837403 = 2756105) B2756105
theorem B4131179 : Blo 1835619 4131179 := bstep (se 1 (by rfl) ⟨3098384, by rfl⟩ : syracuseStep 4131179 = 6196769) B6196769
theorem B1837423 : Blo 1835619 1837423 := bstep (se 1 (by rfl) ⟨1378067, by rfl⟩ : syracuseStep 1837423 = 2756135) B2756135
theorem B8825213 : Blo 1835619 8825213 := bstep (se 3 (by rfl) ⟨1654727, by rfl⟩ : syracuseStep 8825213 = 3309455) B3309455
theorem B3721639 : Blo 1835619 3721639 := bstep (se 1 (by rfl) ⟨2791229, by rfl⟩ : syracuseStep 3721639 = 5582459) B5582459
theorem B2754983 : Blo 1835619 2754983 := bstep (se 1 (by rfl) ⟨2066237, by rfl⟩ : syracuseStep 2754983 = 4132475) B4132475
theorem B1837479 : Blo 1835619 1837479 := bstep (se 1 (by rfl) ⟨1378109, by rfl⟩ : syracuseStep 1837479 = 2756219) B2756219
theorem B6285779 : Blo 1835619 6285779 := bstep (se 1 (by rfl) ⟨4714334, by rfl⟩ : syracuseStep 6285779 = 9428669) B9428669
theorem B4131323 : Blo 1835619 4131323 := bstep (se 1 (by rfl) ⟨3098492, by rfl⟩ : syracuseStep 4131323 = 6196985) B6196985
theorem B2755067 : Blo 1835619 2755067 := bstep (se 1 (by rfl) ⟨2066300, by rfl⟩ : syracuseStep 2755067 = 4132601) B4132601
theorem B1837563 : Blo 1835619 1837563 := bstep (se 1 (by rfl) ⟨1378172, by rfl⟩ : syracuseStep 1837563 = 2756345) B2756345
theorem B2067007 : Blo 1835619 2067007 := bstep (se 1 (by rfl) ⟨1550255, by rfl⟩ : syracuseStep 2067007 = 3100511) B3100511
theorem B1960543 : Blo 1835619 1960543 := bstep (se 1 (by rfl) ⟨1470407, by rfl⟩ : syracuseStep 1960543 = 2940815) B2940815
theorem B4131449 : Blo 1835619 4131449 := bstep (se 2 (by rfl) ⟨1549293, by rfl⟩ : syracuseStep 4131449 = 3098587) B3098587
theorem B2755193 : Blo 1835619 2755193 := bstep (se 2 (by rfl) ⟨1033197, by rfl⟩ : syracuseStep 2755193 = 2066395) B2066395
theorem B4131503 : Blo 1835619 4131503 := bstep (se 1 (by rfl) ⟨3098627, by rfl⟩ : syracuseStep 4131503 = 6197255) B6197255
theorem B2755247 : Blo 1835619 2755247 := bstep (se 1 (by rfl) ⟨2066435, by rfl⟩ : syracuseStep 2755247 = 4132871) B4132871
theorem B17656541 : Blo 1835619 17656541 := bstep (se 3 (by rfl) ⟨3310601, by rfl⟩ : syracuseStep 17656541 = 6621203) B6621203
theorem B2755295 : Blo 1835619 2755295 := bstep (se 1 (by rfl) ⟨2066471, by rfl⟩ : syracuseStep 2755295 = 4132943) B4132943
theorem B6195959 : Blo 1835619 6195959 := bstep (se 1 (by rfl) ⟨4646969, by rfl⟩ : syracuseStep 6195959 = 9293939) B9293939
theorem B4131575 : Blo 1835619 4131575 := bstep (se 1 (by rfl) ⟨3098681, by rfl⟩ : syracuseStep 4131575 = 6197363) B6197363
theorem B15690631 : Blo 1835619 15690631 := bstep (se 1 (by rfl) ⟨11767973, by rfl⟩ : syracuseStep 15690631 = 23535947) B23535947
theorem B7842703 : Blo 1835619 7842703 := bstep (se 1 (by rfl) ⟨5882027, by rfl⟩ : syracuseStep 7842703 = 11764055) B11764055
theorem B4131755 : Blo 1835619 4131755 := bstep (se 1 (by rfl) ⟨3098816, by rfl⟩ : syracuseStep 4131755 = 6197633) B6197633
theorem B4647851 : Blo 1835619 4647851 := bstep (se 1 (by rfl) ⟨3485888, by rfl⟩ : syracuseStep 4647851 = 6971777) B6971777
theorem B16976861 : Blo 1835619 16976861 := bstep (se 3 (by rfl) ⟨3183161, by rfl⟩ : syracuseStep 16976861 = 6366323) B6366323
theorem B2755559 : Blo 1835619 2755559 := bstep (se 1 (by rfl) ⟨2066669, by rfl⟩ : syracuseStep 2755559 = 4133339) B4133339
theorem B25128107 : Blo 1835619 25128107 := bstep (se 1 (by rfl) ⟨18846080, by rfl⟩ : syracuseStep 25128107 = 37692161) B37692161
theorem B9931997 : Blo 1835619 9931997 := bstep (se 3 (by rfl) ⟨1862249, by rfl⟩ : syracuseStep 9931997 = 3724499) B3724499
theorem B2755817 : Blo 1835619 2755817 := bstep (se 2 (by rfl) ⟨1033431, by rfl⟩ : syracuseStep 2755817 = 2066863) B2066863
theorem B2755871 : Blo 1835619 2755871 := bstep (se 1 (by rfl) ⟨2066903, by rfl⟩ : syracuseStep 2755871 = 4133807) B4133807
theorem B7261559 : Blo 1835619 7261559 := bstep (se 1 (by rfl) ⟨5446169, by rfl⟩ : syracuseStep 7261559 = 10892339) B10892339
theorem B4132295 : Blo 1835619 4132295 := bstep (se 1 (by rfl) ⟨3099221, by rfl⟩ : syracuseStep 4132295 = 6198443) B6198443
theorem B2756039 : Blo 1835619 2756039 := bstep (se 1 (by rfl) ⟨2067029, by rfl⟩ : syracuseStep 2756039 = 4134059) B4134059
theorem B1837343 : Blo 1835619 1837343 := bstep (se 1 (by rfl) ⟨1378007, by rfl⟩ : syracuseStep 1837343 = 2756015) B2756015
theorem B3100153 : Blo 1835619 3100153 := bstep (se 2 (by rfl) ⟨1162557, by rfl⟩ : syracuseStep 3100153 = 2325115) B2325115
theorem B1961543 : Blo 1835619 1961543 := bstep (se 1 (by rfl) ⟨1471157, by rfl⟩ : syracuseStep 1961543 = 2942315) B2942315
theorem B10456685 : Blo 1835619 10456685 := bstep (se 3 (by rfl) ⟨1960628, by rfl⟩ : syracuseStep 10456685 = 3921257) B3921257
theorem B9924257 : Blo 1835619 9924257 := bstep (se 2 (by rfl) ⟨3721596, by rfl⟩ : syracuseStep 9924257 = 7443193) B7443193
theorem B10464977 : Blo 1835619 10464977 := bstep (se 2 (by rfl) ⟨3924366, by rfl⟩ : syracuseStep 10464977 = 7848733) B7848733
theorem B9301715 : Blo 1835619 9301715 := bstep (se 1 (by rfl) ⟨6976286, by rfl⟩ : syracuseStep 9301715 = 13952573) B13952573
theorem B4648711 : Blo 1835619 4648711 := bstep (se 1 (by rfl) ⟨3486533, by rfl⟩ : syracuseStep 4648711 = 6973067) B6973067
theorem B3100423 : Blo 1835619 3100423 := bstep (se 1 (by rfl) ⟨2325317, by rfl⟩ : syracuseStep 3100423 = 4650635) B4650635
theorem B3100457 : Blo 1835619 3100457 := bstep (se 2 (by rfl) ⟨1162671, by rfl⟩ : syracuseStep 3100457 = 2325343) B2325343
theorem B2756393 : Blo 1835619 2756393 := bstep (se 2 (by rfl) ⟨1033647, by rfl⟩ : syracuseStep 2756393 = 2067295) B2067295
theorem B9293615 : Blo 1835619 9293615 := bstep (se 1 (by rfl) ⟨6970211, by rfl⟩ : syracuseStep 9293615 = 13940423) B13940423
theorem B6197039 : Blo 1835619 6197039 := bstep (se 1 (by rfl) ⟨4647779, by rfl⟩ : syracuseStep 6197039 = 9295559) B9295559
theorem B4132655 : Blo 1835619 4132655 := bstep (se 1 (by rfl) ⟨3099491, by rfl⟩ : syracuseStep 4132655 = 6198983) B6198983
theorem B2756399 : Blo 1835619 2756399 := bstep (se 1 (by rfl) ⟨2067299, by rfl⟩ : syracuseStep 2756399 = 4134599) B4134599
theorem B5582857 : Blo 1835619 5582857 := bstep (se 2 (by rfl) ⟨2093571, by rfl⟩ : syracuseStep 5582857 = 4187143) B4187143
theorem B6975497 : Blo 1835619 6975497 := bstep (se 2 (by rfl) ⟨2615811, by rfl⟩ : syracuseStep 6975497 = 5231623) B5231623
theorem B4648985 : Blo 1835619 4648985 := bstep (se 2 (by rfl) ⟨1743369, by rfl⟩ : syracuseStep 4648985 = 3486739) B3486739
theorem B79450429 : Blo 1835619 79450429 := bstep (se 3 (by rfl) ⟨14896955, by rfl⟩ : syracuseStep 79450429 = 29793911) B29793911
theorem B9302363 : Blo 1835619 9302363 := bstep (se 1 (by rfl) ⟨6976772, by rfl⟩ : syracuseStep 9302363 = 13953545) B13953545
theorem B4133231 : Blo 1835619 4133231 := bstep (se 1 (by rfl) ⟨3099923, by rfl⟩ : syracuseStep 4133231 = 6199847) B6199847
theorem B11768179 : Blo 1835619 11768179 := bstep (se 1 (by rfl) ⟨8826134, by rfl⟩ : syracuseStep 11768179 = 17652269) B17652269
theorem B4133303 : Blo 1835619 4133303 := bstep (se 1 (by rfl) ⟨3099977, by rfl⟩ : syracuseStep 4133303 = 6199955) B6199955
theorem B31797785 : Blo 1835619 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B4133447 : Blo 1835619 4133447 := bstep (se 1 (by rfl) ⟨3100085, by rfl⟩ : syracuseStep 4133447 = 6200171) B6200171
theorem B4412011 : Blo 1835619 4412011 := bstep (se 1 (by rfl) ⟨3309008, by rfl⟩ : syracuseStep 4412011 = 6618017) B6618017
theorem B4133483 : Blo 1835619 4133483 := bstep (se 1 (by rfl) ⟨3100112, by rfl⟩ : syracuseStep 4133483 = 6200225) B6200225
theorem B5444279 : Blo 1835619 5444279 := bstep (se 1 (by rfl) ⟨4083209, by rfl⟩ : syracuseStep 5444279 = 8166419) B8166419
theorem B2355895 : Blo 1835619 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B4190903 : Blo 1835619 4190903 := bstep (se 1 (by rfl) ⟨3143177, by rfl⟩ : syracuseStep 4190903 = 6286355) B6286355
theorem B2388703 : Blo 1835619 2388703 := bstep (se 1 (by rfl) ⟨1791527, by rfl⟩ : syracuseStep 2388703 = 3583055) B3583055
theorem B18854623 : Blo 1835619 18854623 := bstep (se 1 (by rfl) ⟨14140967, by rfl⟩ : syracuseStep 18854623 = 28281935) B28281935
theorem B5034743 : Blo 1835619 5034743 := bstep (se 1 (by rfl) ⟨3776057, by rfl⟩ : syracuseStep 5034743 = 7552115) B7552115
theorem B10597229 : Blo 1835619 10597229 := bstep (se 3 (by rfl) ⟨1986980, by rfl⟩ : syracuseStep 10597229 = 3973961) B3973961
theorem B57291629 : Blo 1835619 57291629 := bstep (se 3 (by rfl) ⟨10742180, by rfl⟩ : syracuseStep 57291629 = 21484361) B21484361
theorem B4133879 : Blo 1835619 4133879 := bstep (se 1 (by rfl) ⟨3100409, by rfl⟩ : syracuseStep 4133879 = 6200819) B6200819
theorem B6976637 : Blo 1835619 6976637 := bstep (se 3 (by rfl) ⟨1308119, by rfl⟩ : syracuseStep 6976637 = 2616239) B2616239
theorem B17216657 : Blo 1835619 17216657 := bstep (se 2 (by rfl) ⟨6456246, by rfl⟩ : syracuseStep 17216657 = 12912493) B12912493
theorem B14898323 : Blo 1835619 14898323 := bstep (se 1 (by rfl) ⟨11173742, by rfl⟩ : syracuseStep 14898323 = 22347485) B22347485
theorem B39703769 : Blo 1835619 39703769 := bstep (se 2 (by rfl) ⟨14888913, by rfl⟩ : syracuseStep 39703769 = 29777827) B29777827
theorem B13948199 : Blo 1835619 13948199 := bstep (se 1 (by rfl) ⟨10461149, by rfl⟩ : syracuseStep 13948199 = 20922299) B20922299
theorem B4134239 : Blo 1835619 4134239 := bstep (se 1 (by rfl) ⟨3100679, by rfl⟩ : syracuseStep 4134239 = 6201359) B6201359
theorem B23524829 : Blo 1835619 23524829 := bstep (se 3 (by rfl) ⟨4410905, by rfl⟩ : syracuseStep 23524829 = 8821811) B8821811
theorem B37688813 : Blo 1835619 37688813 := bstep (se 3 (by rfl) ⟨7066652, by rfl⟩ : syracuseStep 37688813 = 14133305) B14133305
theorem B3487225 : Blo 1835619 3487225 := bstep (se 2 (by rfl) ⟨1307709, by rfl⟩ : syracuseStep 3487225 = 2615419) B2615419
theorem B39728677 : Blo 1835619 39728677 := bstep (se 4 (by rfl) ⟨3724563, by rfl⟩ : syracuseStep 39728677 = 7449127) B7449127
theorem B2324143 : Blo 1835619 2324143 := bstep (se 1 (by rfl) ⟨1743107, by rfl⟩ : syracuseStep 2324143 = 3486215) B3486215
theorem B4134635 : Blo 1835619 4134635 := bstep (se 1 (by rfl) ⟨3100976, by rfl⟩ : syracuseStep 4134635 = 6201953) B6201953
theorem B3487529 : Blo 1835619 3487529 := bstep (se 2 (by rfl) ⟨1307823, by rfl⟩ : syracuseStep 3487529 = 2615647) B2615647
theorem B4413241 : Blo 1835619 4413241 := bstep (se 2 (by rfl) ⟨1654965, by rfl⟩ : syracuseStep 4413241 = 3309931) B3309931
theorem B9295721 : Blo 1835619 9295721 := bstep (se 2 (by rfl) ⟨3485895, by rfl⟩ : syracuseStep 9295721 = 6971791) B6971791
theorem B6199145 : Blo 1835619 6199145 := bstep (se 2 (by rfl) ⟨2324679, by rfl⟩ : syracuseStep 6199145 = 4649359) B4649359
theorem B4650959 : Blo 1835619 4650959 := bstep (se 1 (by rfl) ⟨3488219, by rfl⟩ : syracuseStep 4650959 = 6976439) B6976439
theorem B15104033 : Blo 1835619 15104033 := bstep (se 2 (by rfl) ⟨5664012, by rfl⟩ : syracuseStep 15104033 = 11328025) B11328025
theorem B6199577 : Blo 1835619 6199577 := bstep (se 2 (by rfl) ⟨2324841, by rfl⟩ : syracuseStep 6199577 = 4649683) B4649683
theorem B19855691 : Blo 1835619 19855691 := bstep (se 1 (by rfl) ⟨14891768, by rfl⟩ : syracuseStep 19855691 = 29783537) B29783537
theorem B3922283 : Blo 1835619 3922283 := bstep (se 1 (by rfl) ⟨2941712, by rfl⟩ : syracuseStep 3922283 = 5883425) B5883425
theorem B6617555 : Blo 1835619 6617555 := bstep (se 1 (by rfl) ⟨4963166, by rfl⟩ : syracuseStep 6617555 = 9926333) B9926333
theorem B28670537 : Blo 1835619 28670537 := bstep (se 2 (by rfl) ⟨10751451, by rfl⟩ : syracuseStep 28670537 = 21502903) B21502903
theorem B11934347 : Blo 1835619 11934347 := bstep (se 1 (by rfl) ⟨8950760, by rfl⟩ : syracuseStep 11934347 = 17901521) B17901521
theorem B3922607 : Blo 1835619 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B12565367 : Blo 1835619 12565367 := bstep (se 1 (by rfl) ⟨9424025, by rfl⟩ : syracuseStep 12565367 = 18848051) B18848051
theorem B7445627 : Blo 1835619 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B11164837 : Blo 1835619 11164837 := bstep (se 4 (by rfl) ⟨1046703, by rfl⟩ : syracuseStep 11164837 = 2093407) B2093407
theorem B16760029 : Blo 1835619 16760029 := bstep (se 3 (by rfl) ⟨3142505, by rfl⟩ : syracuseStep 16760029 = 6285011) B6285011
theorem B290127419 : Blo 1835619 290127419 := bstep (se 1 (by rfl) ⟨217595564, by rfl⟩ : syracuseStep 290127419 = 435191129) B435191129
theorem B13942367 : Blo 1835619 13942367 := bstep (se 1 (by rfl) ⟨10456775, by rfl⟩ : syracuseStep 13942367 = 20913551) B20913551
theorem B9297503 : Blo 1835619 9297503 := bstep (se 1 (by rfl) ⟨6973127, by rfl⟩ : syracuseStep 9297503 = 13946255) B13946255
theorem B6200927 : Blo 1835619 6200927 := bstep (se 1 (by rfl) ⟨4650695, by rfl⟩ : syracuseStep 6200927 = 9301391) B9301391
theorem B14900851 : Blo 1835619 14900851 := bstep (se 1 (by rfl) ⟨11175638, by rfl⟩ : syracuseStep 14900851 = 22351277) B22351277
theorem B11763463 : Blo 1835619 11763463 := bstep (se 1 (by rfl) ⟨8822597, by rfl⟩ : syracuseStep 11763463 = 17645195) B17645195
theorem B6618941 : Blo 1835619 6618941 := bstep (se 3 (by rfl) ⟨1241051, by rfl⟩ : syracuseStep 6618941 = 2482103) B2482103
theorem B6201575 : Blo 1835619 6201575 := bstep (se 1 (by rfl) ⟨4651181, by rfl⟩ : syracuseStep 6201575 = 9302363) B9302363
theorem B29786393 : Blo 1835619 29786393 := bstep (se 2 (by rfl) ⟨11169897, by rfl⟩ : syracuseStep 29786393 = 22339795) B22339795
theorem B3629519 : Blo 1835619 3629519 := bstep (se 1 (by rfl) ⟨2722139, by rfl⟩ : syracuseStep 3629519 = 5444279) B5444279
theorem B2793935 : Blo 1835619 2793935 := bstep (se 1 (by rfl) ⟨2095451, by rfl⟩ : syracuseStep 2793935 = 4190903) B4190903
theorem B1835623 : Blo 1835619 1835623 := bstep (se 1 (by rfl) ⟨1376717, by rfl⟩ : syracuseStep 1835623 = 2753435) B2753435
theorem B11477771 : Blo 1835619 11477771 := bstep (se 1 (by rfl) ⟨8608328, by rfl⟩ : syracuseStep 11477771 = 17216657) B17216657
theorem B5882681 : Blo 1835619 5882681 := bstep (se 2 (by rfl) ⟨2206005, by rfl⟩ : syracuseStep 5882681 = 4412011) B4412011
theorem B26469179 : Blo 1835619 26469179 := bstep (se 1 (by rfl) ⟨19851884, by rfl⟩ : syracuseStep 26469179 = 39703769) B39703769
theorem B5227375 : Blo 1835619 5227375 := bstep (se 1 (by rfl) ⟨3920531, by rfl⟩ : syracuseStep 5227375 = 7841063) B7841063
theorem B1835887 : Blo 1835619 1835887 := bstep (se 1 (by rfl) ⟨1376915, by rfl⟩ : syracuseStep 1835887 = 2753831) B2753831
theorem B9298799 : Blo 1835619 9298799 := bstep (se 1 (by rfl) ⟨6974099, by rfl⟩ : syracuseStep 9298799 = 13948199) B13948199
theorem B2753447 : Blo 1835619 2753447 := bstep (se 1 (by rfl) ⟨2065085, by rfl⟩ : syracuseStep 2753447 = 4130171) B4130171
theorem B1835943 : Blo 1835619 1835943 := bstep (se 1 (by rfl) ⟨1376957, by rfl⟩ : syracuseStep 1835943 = 2753915) B2753915
theorem B25125875 : Blo 1835619 25125875 := bstep (se 1 (by rfl) ⟨18844406, by rfl⟩ : syracuseStep 25125875 = 37688813) B37688813
theorem B2753531 : Blo 1835619 2753531 := bstep (se 1 (by rfl) ⟨2065148, by rfl⟩ : syracuseStep 2753531 = 4130297) B4130297
theorem B1836027 : Blo 1835619 1836027 := bstep (se 1 (by rfl) ⟨1377020, by rfl⟩ : syracuseStep 1836027 = 2754041) B2754041
theorem B2753591 : Blo 1835619 2753591 := bstep (se 1 (by rfl) ⟨2065193, by rfl⟩ : syracuseStep 2753591 = 4130387) B4130387
theorem B1836095 : Blo 1835619 1836095 := bstep (se 1 (by rfl) ⟨1377071, by rfl⟩ : syracuseStep 1836095 = 2754143) B2754143
theorem B2753711 : Blo 1835619 2753711 := bstep (se 1 (by rfl) ⟨2065283, by rfl⟩ : syracuseStep 2753711 = 4130567) B4130567
theorem B1836239 : Blo 1835619 1836239 := bstep (se 1 (by rfl) ⟨1377179, by rfl⟩ : syracuseStep 1836239 = 2754359) B2754359
theorem B10069355 : Blo 1835619 10069355 := bstep (se 1 (by rfl) ⟨7552016, by rfl⟩ : syracuseStep 10069355 = 15104033) B15104033
theorem B2065819 : Blo 1835619 2065819 := bstep (se 1 (by rfl) ⟨1549364, by rfl⟩ : syracuseStep 2065819 = 3098729) B3098729
theorem B1836443 : Blo 1835619 1836443 := bstep (se 1 (by rfl) ⟨1377332, by rfl⟩ : syracuseStep 1836443 = 2754665) B2754665
theorem B3098027 : Blo 1835619 3098027 := bstep (se 1 (by rfl) ⟨2323520, by rfl⟩ : syracuseStep 3098027 = 4647041) B4647041
theorem B14886449 : Blo 1835619 14886449 := bstep (se 2 (by rfl) ⟨5582418, by rfl⟩ : syracuseStep 14886449 = 11164837) B11164837
theorem B2754119 : Blo 1835619 2754119 := bstep (se 1 (by rfl) ⟨2065589, by rfl⟩ : syracuseStep 2754119 = 4131179) B4131179
theorem B2614855 : Blo 1835619 2614855 := bstep (se 1 (by rfl) ⟨1961141, by rfl⟩ : syracuseStep 2614855 = 3922283) B3922283
theorem B5883475 : Blo 1835619 5883475 := bstep (se 1 (by rfl) ⟨4412606, by rfl⟩ : syracuseStep 5883475 = 8825213) B8825213
theorem B1836655 : Blo 1835619 1836655 := bstep (se 1 (by rfl) ⟨1377491, by rfl⟩ : syracuseStep 1836655 = 2754983) B2754983
theorem B2754215 : Blo 1835619 2754215 := bstep (se 1 (by rfl) ⟨2065661, by rfl⟩ : syracuseStep 2754215 = 4131323) B4131323
theorem B1836711 : Blo 1835619 1836711 := bstep (se 1 (by rfl) ⟨1377533, by rfl⟩ : syracuseStep 1836711 = 2755067) B2755067
theorem B2754299 : Blo 1835619 2754299 := bstep (se 1 (by rfl) ⟨2065724, by rfl⟩ : syracuseStep 2754299 = 4131449) B4131449
theorem B1836795 : Blo 1835619 1836795 := bstep (se 1 (by rfl) ⟨1377596, by rfl⟩ : syracuseStep 1836795 = 2755193) B2755193
theorem B2754335 : Blo 1835619 2754335 := bstep (se 1 (by rfl) ⟨2065751, by rfl⟩ : syracuseStep 2754335 = 4131503) B4131503
theorem B1836831 : Blo 1835619 1836831 := bstep (se 1 (by rfl) ⟨1377623, by rfl⟩ : syracuseStep 1836831 = 2755247) B2755247
theorem B1836863 : Blo 1835619 1836863 := bstep (se 1 (by rfl) ⟨1377647, by rfl⟩ : syracuseStep 1836863 = 2755295) B2755295
theorem B4130639 : Blo 1835619 4130639 := bstep (se 1 (by rfl) ⟨3097979, by rfl⟩ : syracuseStep 4130639 = 6195959) B6195959
theorem B2754383 : Blo 1835619 2754383 := bstep (se 1 (by rfl) ⟨2065787, by rfl⟩ : syracuseStep 2754383 = 4131575) B4131575
theorem B4130657 : Blo 1835619 4130657 := bstep (se 2 (by rfl) ⟨1548996, by rfl⟩ : syracuseStep 4130657 = 3097993) B3097993
theorem B3098567 : Blo 1835619 3098567 := bstep (se 1 (by rfl) ⟨2323925, by rfl⟩ : syracuseStep 3098567 = 4647851) B4647851
theorem B2754503 : Blo 1835619 2754503 := bstep (se 1 (by rfl) ⟨2065877, by rfl⟩ : syracuseStep 2754503 = 4131755) B4131755
theorem B1837039 : Blo 1835619 1837039 := bstep (se 1 (by rfl) ⟨1377779, by rfl⟩ : syracuseStep 1837039 = 2755559) B2755559
theorem B52971569 : Blo 1835619 52971569 := bstep (se 2 (by rfl) ⟨19864338, by rfl⟩ : syracuseStep 52971569 = 39728677) B39728677
theorem B6621331 : Blo 1835619 6621331 := bstep (se 1 (by rfl) ⟨4965998, by rfl⟩ : syracuseStep 6621331 = 9931997) B9931997
theorem B19867801 : Blo 1835619 19867801 := bstep (se 2 (by rfl) ⟨7450425, by rfl⟩ : syracuseStep 19867801 = 14900851) B14900851
theorem B1837211 : Blo 1835619 1837211 := bstep (se 1 (by rfl) ⟨1377908, by rfl⟩ : syracuseStep 1837211 = 2755817) B2755817
theorem B1837247 : Blo 1835619 1837247 := bstep (se 1 (by rfl) ⟨1377935, by rfl⟩ : syracuseStep 1837247 = 2755871) B2755871
theorem B3098857 : Blo 1835619 3098857 := bstep (se 2 (by rfl) ⟨1162071, by rfl⟩ : syracuseStep 3098857 = 2324143) B2324143
theorem B2754857 : Blo 1835619 2754857 := bstep (se 2 (by rfl) ⟨1033071, by rfl⟩ : syracuseStep 2754857 = 2066143) B2066143
theorem B2754863 : Blo 1835619 2754863 := bstep (se 1 (by rfl) ⟨2066147, by rfl⟩ : syracuseStep 2754863 = 4132295) B4132295
theorem B1837359 : Blo 1835619 1837359 := bstep (se 1 (by rfl) ⟨1378019, by rfl⟩ : syracuseStep 1837359 = 2756039) B2756039
theorem B4131233 : Blo 1835619 4131233 := bstep (se 2 (by rfl) ⟨1549212, by rfl⟩ : syracuseStep 4131233 = 3098425) B3098425
theorem B5884321 : Blo 1835619 5884321 := bstep (se 2 (by rfl) ⟨2206620, by rfl⟩ : syracuseStep 5884321 = 4413241) B4413241
theorem B2066971 : Blo 1835619 2066971 := bstep (se 1 (by rfl) ⟨1550228, by rfl⟩ : syracuseStep 2066971 = 3100457) B3100457
theorem B1837595 : Blo 1835619 1837595 := bstep (se 1 (by rfl) ⟨1378196, by rfl⟩ : syracuseStep 1837595 = 2756393) B2756393
theorem B6195743 : Blo 1835619 6195743 := bstep (se 1 (by rfl) ⟨4646807, by rfl⟩ : syracuseStep 6195743 = 9293615) B9293615
theorem B4131359 : Blo 1835619 4131359 := bstep (se 1 (by rfl) ⟨3098519, by rfl⟩ : syracuseStep 4131359 = 6197039) B6197039
theorem B2755103 : Blo 1835619 2755103 := bstep (se 1 (by rfl) ⟨2066327, by rfl⟩ : syracuseStep 2755103 = 4132655) B4132655
theorem B1837599 : Blo 1835619 1837599 := bstep (se 1 (by rfl) ⟨1378199, by rfl⟩ : syracuseStep 1837599 = 2756399) B2756399
theorem B3099323 : Blo 1835619 3099323 := bstep (se 1 (by rfl) ⟨2324492, by rfl⟩ : syracuseStep 3099323 = 4648985) B4648985
theorem B2755487 : Blo 1835619 2755487 := bstep (se 1 (by rfl) ⟨2066615, by rfl⟩ : syracuseStep 2755487 = 4133231) B4133231
theorem B17894317 : Blo 1835619 17894317 := bstep (se 3 (by rfl) ⟨3355184, by rfl⟩ : syracuseStep 17894317 = 6710369) B6710369
theorem B2755535 : Blo 1835619 2755535 := bstep (se 1 (by rfl) ⟨2066651, by rfl⟩ : syracuseStep 2755535 = 4133303) B4133303
theorem B2755625 : Blo 1835619 2755625 := bstep (se 2 (by rfl) ⟨1033359, by rfl⟩ : syracuseStep 2755625 = 2066719) B2066719
theorem B2755631 : Blo 1835619 2755631 := bstep (se 1 (by rfl) ⟨2066723, by rfl⟩ : syracuseStep 2755631 = 4133447) B4133447
theorem B2755655 : Blo 1835619 2755655 := bstep (se 1 (by rfl) ⟨2066741, by rfl⟩ : syracuseStep 2755655 = 4133483) B4133483
theorem B105933905 : Blo 1835619 105933905 := bstep (se 2 (by rfl) ⟨39725214, by rfl⟩ : syracuseStep 105933905 = 79450429) B79450429
theorem B15690905 : Blo 1835619 15690905 := bstep (se 2 (by rfl) ⟨5884089, by rfl⟩ : syracuseStep 15690905 = 11768179) B11768179
theorem B10456229 : Blo 1835619 10456229 := bstep (se 4 (by rfl) ⟨980271, by rfl⟩ : syracuseStep 10456229 = 1960543) B1960543
theorem B7064819 : Blo 1835619 7064819 := bstep (se 1 (by rfl) ⟨5298614, by rfl⟩ : syracuseStep 7064819 = 10597229) B10597229
theorem B2755919 : Blo 1835619 2755919 := bstep (se 1 (by rfl) ⟨2066939, by rfl⟩ : syracuseStep 2755919 = 4133879) B4133879
theorem B2756009 : Blo 1835619 2756009 := bstep (se 2 (by rfl) ⟨1033503, by rfl⟩ : syracuseStep 2756009 = 2067007) B2067007
theorem B9932215 : Blo 1835619 9932215 := bstep (se 1 (by rfl) ⟨7449161, by rfl⟩ : syracuseStep 9932215 = 14898323) B14898323
theorem B2207207 : Blo 1835619 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B2756159 : Blo 1835619 2756159 := bstep (se 1 (by rfl) ⟨2067119, by rfl⟩ : syracuseStep 2756159 = 4134239) B4134239
theorem B3141193 : Blo 1835619 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B15683219 : Blo 1835619 15683219 := bstep (se 1 (by rfl) ⟨11762414, by rfl⟩ : syracuseStep 15683219 = 23524829) B23524829
theorem B2756423 : Blo 1835619 2756423 := bstep (se 1 (by rfl) ⟨2067317, by rfl⟩ : syracuseStep 2756423 = 4134635) B4134635
theorem B10456937 : Blo 1835619 10456937 := bstep (se 2 (by rfl) ⟨3921351, by rfl⟩ : syracuseStep 10456937 = 7842703) B7842703
theorem B6197147 : Blo 1835619 6197147 := bstep (se 1 (by rfl) ⟨4647860, by rfl⟩ : syracuseStep 6197147 = 9295721) B9295721
theorem B4132763 : Blo 1835619 4132763 := bstep (se 1 (by rfl) ⟨3099572, by rfl⟩ : syracuseStep 4132763 = 6199145) B6199145
theorem B3100639 : Blo 1835619 3100639 := bstep (se 1 (by rfl) ⟨2325479, by rfl⟩ : syracuseStep 3100639 = 4650959) B4650959
theorem B127299701 : Blo 1835619 127299701 := bstep (se 5 (by rfl) ⟨5967173, by rfl⟩ : syracuseStep 127299701 = 11934347) B11934347
theorem B4649147 : Blo 1835619 4649147 := bstep (se 1 (by rfl) ⟨3486860, by rfl⟩ : syracuseStep 4649147 = 6973721) B6973721
theorem B4133051 : Blo 1835619 4133051 := bstep (se 1 (by rfl) ⟨3099788, by rfl⟩ : syracuseStep 4133051 = 6199577) B6199577
theorem B5230781 : Blo 1835619 5230781 := bstep (se 3 (by rfl) ⟨980771, by rfl⟩ : syracuseStep 5230781 = 1961543) B1961543
theorem B4411703 : Blo 1835619 4411703 := bstep (se 1 (by rfl) ⟨3308777, by rfl⟩ : syracuseStep 4411703 = 6617555) B6617555
theorem B4190519 : Blo 1835619 4190519 := bstep (se 1 (by rfl) ⟨3142889, by rfl⟩ : syracuseStep 4190519 = 6285779) B6285779
theorem B8376911 : Blo 1835619 8376911 := bstep (se 1 (by rfl) ⟨6282683, by rfl⟩ : syracuseStep 8376911 = 12565367) B12565367
theorem B11317907 : Blo 1835619 11317907 := bstep (se 1 (by rfl) ⟨8488430, by rfl⟩ : syracuseStep 11317907 = 16976861) B16976861
theorem B4649633 : Blo 1835619 4649633 := bstep (se 2 (by rfl) ⟨1743612, by rfl⟩ : syracuseStep 4649633 = 3487225) B3487225
theorem B4133537 : Blo 1835619 4133537 := bstep (se 2 (by rfl) ⟨1550076, by rfl⟩ : syracuseStep 4133537 = 3100153) B3100153
theorem B152777677 : Blo 1835619 152777677 := bstep (se 3 (by rfl) ⟨28645814, by rfl⟩ : syracuseStep 152777677 = 57291629) B57291629
theorem B15684617 : Blo 1835619 15684617 := bstep (se 2 (by rfl) ⟨5881731, by rfl⟩ : syracuseStep 15684617 = 11763463) B11763463
theorem B6198281 : Blo 1835619 6198281 := bstep (se 2 (by rfl) ⟨2324355, by rfl⟩ : syracuseStep 6198281 = 4648711) B4648711
theorem B4133897 : Blo 1835619 4133897 := bstep (se 2 (by rfl) ⟨1550211, by rfl⟩ : syracuseStep 4133897 = 3100423) B3100423
theorem B193418279 : Blo 1835619 193418279 := bstep (se 1 (by rfl) ⟨145063709, by rfl⟩ : syracuseStep 193418279 = 290127419) B290127419
theorem B9294911 : Blo 1835619 9294911 := bstep (se 1 (by rfl) ⟨6971183, by rfl⟩ : syracuseStep 9294911 = 13942367) B13942367
theorem B6198335 : Blo 1835619 6198335 := bstep (se 1 (by rfl) ⟨4648751, by rfl⟩ : syracuseStep 6198335 = 9297503) B9297503
theorem B4133951 : Blo 1835619 4133951 := bstep (se 1 (by rfl) ⟨3100463, by rfl⟩ : syracuseStep 4133951 = 6200927) B6200927
theorem B6616171 : Blo 1835619 6616171 := bstep (se 1 (by rfl) ⟨4962128, by rfl⟩ : syracuseStep 6616171 = 9924257) B9924257
theorem B6976651 : Blo 1835619 6976651 := bstep (se 1 (by rfl) ⟨5232488, by rfl⟩ : syracuseStep 6976651 = 10464977) B10464977
theorem B4412627 : Blo 1835619 4412627 := bstep (se 1 (by rfl) ⟨3309470, by rfl⟩ : syracuseStep 4412627 = 6618941) B6618941
theorem B4650331 : Blo 1835619 4650331 := bstep (se 1 (by rfl) ⟨3487748, by rfl⟩ : syracuseStep 4650331 = 6975497) B6975497
theorem B7443809 : Blo 1835619 7443809 := bstep (se 2 (by rfl) ⟨2791428, by rfl⟩ : syracuseStep 7443809 = 5582857) B5582857
theorem B21198523 : Blo 1835619 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B3356495 : Blo 1835619 3356495 := bstep (se 1 (by rfl) ⟨2517371, by rfl⟩ : syracuseStep 3356495 = 5034743) B5034743
theorem B4962185 : Blo 1835619 4962185 := bstep (se 2 (by rfl) ⟨1860819, by rfl⟩ : syracuseStep 4962185 = 3721639) B3721639
theorem B18847727 : Blo 1835619 18847727 := bstep (se 1 (by rfl) ⟨14135795, by rfl⟩ : syracuseStep 18847727 = 28271591) B28271591
theorem B4651091 : Blo 1835619 4651091 := bstep (se 1 (by rfl) ⟨3488318, by rfl⟩ : syracuseStep 4651091 = 6976637) B6976637
theorem B13949171 : Blo 1835619 13949171 := bstep (se 1 (by rfl) ⟨10461878, by rfl⟩ : syracuseStep 13949171 = 20923757) B20923757
theorem B4413683 : Blo 1835619 4413683 := bstep (se 1 (by rfl) ⟨3310262, by rfl⟩ : syracuseStep 4413683 = 6620525) B6620525
theorem B4413703 : Blo 1835619 4413703 := bstep (se 1 (by rfl) ⟨3310277, by rfl⟩ : syracuseStep 4413703 = 6620555) B6620555
theorem B3184937 : Blo 1835619 3184937 := bstep (se 2 (by rfl) ⟨1194351, by rfl⟩ : syracuseStep 3184937 = 2388703) B2388703
theorem B25139497 : Blo 1835619 25139497 := bstep (se 2 (by rfl) ⟨9427311, by rfl⟩ : syracuseStep 25139497 = 18854623) B18854623
theorem B20920841 : Blo 1835619 20920841 := bstep (se 2 (by rfl) ⟨7845315, by rfl⟩ : syracuseStep 20920841 = 15690631) B15690631
theorem B2325019 : Blo 1835619 2325019 := bstep (se 1 (by rfl) ⟨1743764, by rfl⟩ : syracuseStep 2325019 = 3487529) B3487529
theorem B76454765 : Blo 1835619 76454765 := bstep (se 3 (by rfl) ⟨14335268, by rfl⟩ : syracuseStep 76454765 = 28670537) B28670537
theorem B13237127 : Blo 1835619 13237127 := bstep (se 1 (by rfl) ⟨9927845, by rfl⟩ : syracuseStep 13237127 = 19855691) B19855691
theorem B22346705 : Blo 1835619 22346705 := bstep (se 2 (by rfl) ⟨8380014, by rfl⟩ : syracuseStep 22346705 = 16760029) B16760029
theorem B10460285 : Blo 1835619 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B11771027 : Blo 1835619 11771027 := bstep (se 1 (by rfl) ⟨8828270, by rfl⟩ : syracuseStep 11771027 = 17656541) B17656541
theorem B4963751 : Blo 1835619 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B16752071 : Blo 1835619 16752071 := bstep (se 1 (by rfl) ⟨12564053, by rfl⟩ : syracuseStep 16752071 = 25128107) B25128107
theorem B4841039 : Blo 1835619 4841039 := bstep (se 1 (by rfl) ⟨3630779, by rfl⟩ : syracuseStep 4841039 = 7261559) B7261559
theorem B6971123 : Blo 1835619 6971123 := bstep (se 1 (by rfl) ⟨5228342, by rfl⟩ : syracuseStep 6971123 = 10456685) B10456685
theorem B6201143 : Blo 1835619 6201143 := bstep (se 1 (by rfl) ⟨4650857, by rfl⟩ : syracuseStep 6201143 = 9301715) B9301715
theorem B19857595 : Blo 1835619 19857595 := bstep (se 1 (by rfl) ⟨14893196, by rfl⟩ : syracuseStep 19857595 = 29786393) B29786393
theorem B2793679 : Blo 1835619 2793679 := bstep (se 1 (by rfl) ⟨2095259, by rfl⟩ : syracuseStep 2793679 = 4190519) B4190519
theorem B7545271 : Blo 1835619 7545271 := bstep (se 1 (by rfl) ⟨5658953, by rfl⟩ : syracuseStep 7545271 = 11317907) B11317907
theorem B7651847 : Blo 1835619 7651847 := bstep (se 1 (by rfl) ⟨5738885, by rfl⟩ : syracuseStep 7651847 = 11477771) B11477771
theorem B17646119 : Blo 1835619 17646119 := bstep (se 1 (by rfl) ⟨13234589, by rfl⟩ : syracuseStep 17646119 = 26469179) B26469179
theorem B1835631 : Blo 1835619 1835631 := bstep (se 1 (by rfl) ⟨1376723, by rfl⟩ : syracuseStep 1835631 = 2753447) B2753447
theorem B1835687 : Blo 1835619 1835687 := bstep (se 1 (by rfl) ⟨1376765, by rfl⟩ : syracuseStep 1835687 = 2753531) B2753531
theorem B1835727 : Blo 1835619 1835727 := bstep (se 1 (by rfl) ⟨1376795, by rfl⟩ : syracuseStep 1835727 = 2753591) B2753591
theorem B1835807 : Blo 1835619 1835807 := bstep (se 1 (by rfl) ⟨1376855, by rfl⟩ : syracuseStep 1835807 = 2753711) B2753711
theorem B11764541 : Blo 1835619 11764541 := bstep (se 3 (by rfl) ⟨2205851, by rfl⟩ : syracuseStep 11764541 = 4411703) B4411703
theorem B2941751 : Blo 1835619 2941751 := bstep (se 1 (by rfl) ⟨2206313, by rfl⟩ : syracuseStep 2941751 = 4412627) B4412627
theorem B2065351 : Blo 1835619 2065351 := bstep (se 1 (by rfl) ⟨1549013, by rfl⟩ : syracuseStep 2065351 = 3098027) B3098027
theorem B1836079 : Blo 1835619 1836079 := bstep (se 1 (by rfl) ⟨1377059, by rfl⟩ : syracuseStep 1836079 = 2754119) B2754119
theorem B1836143 : Blo 1835619 1836143 := bstep (se 1 (by rfl) ⟨1377107, by rfl⟩ : syracuseStep 1836143 = 2754215) B2754215
theorem B1836199 : Blo 1835619 1836199 := bstep (se 1 (by rfl) ⟨1377149, by rfl⟩ : syracuseStep 1836199 = 2754299) B2754299
theorem B1836223 : Blo 1835619 1836223 := bstep (se 1 (by rfl) ⟨1377167, by rfl⟩ : syracuseStep 1836223 = 2754335) B2754335
theorem B2753759 : Blo 1835619 2753759 := bstep (se 1 (by rfl) ⟨2065319, by rfl⟩ : syracuseStep 2753759 = 4130639) B4130639
theorem B1836255 : Blo 1835619 1836255 := bstep (se 1 (by rfl) ⟨1377191, by rfl⟩ : syracuseStep 1836255 = 2754383) B2754383
theorem B2237663 : Blo 1835619 2237663 := bstep (se 1 (by rfl) ⟨1678247, by rfl⟩ : syracuseStep 2237663 = 3356495) B3356495
theorem B2753771 : Blo 1835619 2753771 := bstep (se 1 (by rfl) ⟨2065328, by rfl⟩ : syracuseStep 2753771 = 4130657) B4130657
theorem B2942455 : Blo 1835619 2942455 := bstep (se 1 (by rfl) ⟨2206841, by rfl⟩ : syracuseStep 2942455 = 4413683) B4413683
theorem B203703569 : Blo 1835619 203703569 := bstep (se 2 (by rfl) ⟨76388838, by rfl⟩ : syracuseStep 203703569 = 152777677) B152777677
theorem B2065711 : Blo 1835619 2065711 := bstep (se 1 (by rfl) ⟨1549283, by rfl⟩ : syracuseStep 2065711 = 3098567) B3098567
theorem B1836335 : Blo 1835619 1836335 := bstep (se 1 (by rfl) ⟨1377251, by rfl⟩ : syracuseStep 1836335 = 2754503) B2754503
theorem B9299447 : Blo 1835619 9299447 := bstep (se 1 (by rfl) ⟨6974585, by rfl⟩ : syracuseStep 9299447 = 13949171) B13949171
theorem B1836571 : Blo 1835619 1836571 := bstep (se 1 (by rfl) ⟨1377428, by rfl⟩ : syracuseStep 1836571 = 2754857) B2754857
theorem B1836575 : Blo 1835619 1836575 := bstep (se 1 (by rfl) ⟨1377431, by rfl⟩ : syracuseStep 1836575 = 2754863) B2754863
theorem B2123291 : Blo 1835619 2123291 := bstep (se 1 (by rfl) ⟨1592468, by rfl⟩ : syracuseStep 2123291 = 3184937) B3184937
theorem B2754155 : Blo 1835619 2754155 := bstep (se 1 (by rfl) ⟨2065616, by rfl⟩ : syracuseStep 2754155 = 4131233) B4131233
theorem B4130495 : Blo 1835619 4130495 := bstep (se 1 (by rfl) ⟨3097871, by rfl⟩ : syracuseStep 4130495 = 6195743) B6195743
theorem B2754239 : Blo 1835619 2754239 := bstep (se 1 (by rfl) ⟨2065679, by rfl⟩ : syracuseStep 2754239 = 4131359) B4131359
theorem B1836735 : Blo 1835619 1836735 := bstep (se 1 (by rfl) ⟨1377551, by rfl⟩ : syracuseStep 1836735 = 2755103) B2755103
theorem B2066215 : Blo 1835619 2066215 := bstep (se 1 (by rfl) ⟨1549661, by rfl⟩ : syracuseStep 2066215 = 3099323) B3099323
theorem B2754425 : Blo 1835619 2754425 := bstep (se 2 (by rfl) ⟨1032909, by rfl⟩ : syracuseStep 2754425 = 2065819) B2065819
theorem B8824751 : Blo 1835619 8824751 := bstep (se 1 (by rfl) ⟨6618563, by rfl⟩ : syracuseStep 8824751 = 13237127) B13237127
theorem B1836991 : Blo 1835619 1836991 := bstep (se 1 (by rfl) ⟨1377743, by rfl⟩ : syracuseStep 1836991 = 2755487) B2755487
theorem B1837023 : Blo 1835619 1837023 := bstep (se 1 (by rfl) ⟨1377767, by rfl⟩ : syracuseStep 1837023 = 2755535) B2755535
theorem B1837083 : Blo 1835619 1837083 := bstep (se 1 (by rfl) ⟨1377812, by rfl⟩ : syracuseStep 1837083 = 2755625) B2755625
theorem B1837087 : Blo 1835619 1837087 := bstep (se 1 (by rfl) ⟨1377815, by rfl⟩ : syracuseStep 1837087 = 2755631) B2755631
theorem B1837103 : Blo 1835619 1837103 := bstep (se 1 (by rfl) ⟨1377827, by rfl⟩ : syracuseStep 1837103 = 2755655) B2755655
theorem B6973523 : Blo 1835619 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B4188257 : Blo 1835619 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B1837279 : Blo 1835619 1837279 := bstep (se 1 (by rfl) ⟨1377959, by rfl⟩ : syracuseStep 1837279 = 2755919) B2755919
theorem B28264697 : Blo 1835619 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B1837339 : Blo 1835619 1837339 := bstep (se 1 (by rfl) ⟨1378004, by rfl⟩ : syracuseStep 1837339 = 2756009) B2756009
theorem B11168047 : Blo 1835619 11168047 := bstep (se 1 (by rfl) ⟨8376035, by rfl⟩ : syracuseStep 11168047 = 16752071) B16752071
theorem B1837439 : Blo 1835619 1837439 := bstep (se 1 (by rfl) ⟨1378079, by rfl⟩ : syracuseStep 1837439 = 2756159) B2756159
theorem B10455479 : Blo 1835619 10455479 := bstep (se 1 (by rfl) ⟨7841609, by rfl⟩ : syracuseStep 10455479 = 15683219) B15683219
theorem B4647415 : Blo 1835619 4647415 := bstep (se 1 (by rfl) ⟨3485561, by rfl⟩ : syracuseStep 4647415 = 6971123) B6971123
theorem B1837615 : Blo 1835619 1837615 := bstep (se 1 (by rfl) ⟨1378211, by rfl⟩ : syracuseStep 1837615 = 2756423) B2756423
theorem B4131431 : Blo 1835619 4131431 := bstep (se 1 (by rfl) ⟨3098573, by rfl⟩ : syracuseStep 4131431 = 6197147) B6197147
theorem B2755175 : Blo 1835619 2755175 := bstep (se 1 (by rfl) ⟨2066381, by rfl⟩ : syracuseStep 2755175 = 4132763) B4132763
theorem B3099431 : Blo 1835619 3099431 := bstep (se 1 (by rfl) ⟨2324573, by rfl⟩ : syracuseStep 3099431 = 4649147) B4649147
theorem B2755367 : Blo 1835619 2755367 := bstep (se 1 (by rfl) ⟨2066525, by rfl⟩ : syracuseStep 2755367 = 4133051) B4133051
theorem B2419679 : Blo 1835619 2419679 := bstep (se 1 (by rfl) ⟨1814759, by rfl⟩ : syracuseStep 2419679 = 3629519) B3629519
theorem B4131809 : Blo 1835619 4131809 := bstep (se 2 (by rfl) ⟨1549428, by rfl⟩ : syracuseStep 4131809 = 3098857) B3098857
theorem B1862623 : Blo 1835619 1862623 := bstep (se 1 (by rfl) ⟨1396967, by rfl⟩ : syracuseStep 1862623 = 2793935) B2793935
theorem B5884937 : Blo 1835619 5884937 := bstep (se 2 (by rfl) ⟨2206851, by rfl⟩ : syracuseStep 5884937 = 4413703) B4413703
theorem B3099755 : Blo 1835619 3099755 := bstep (se 1 (by rfl) ⟨2324816, by rfl⟩ : syracuseStep 3099755 = 4649633) B4649633
theorem B2755691 : Blo 1835619 2755691 := bstep (se 1 (by rfl) ⟨2066768, by rfl⟩ : syracuseStep 2755691 = 4133537) B4133537
theorem B10456411 : Blo 1835619 10456411 := bstep (se 1 (by rfl) ⟨7842308, by rfl⟩ : syracuseStep 10456411 = 15684617) B15684617
theorem B4132187 : Blo 1835619 4132187 := bstep (se 1 (by rfl) ⟨3099140, by rfl⟩ : syracuseStep 4132187 = 6198281) B6198281
theorem B2755931 : Blo 1835619 2755931 := bstep (se 1 (by rfl) ⟨2066948, by rfl⟩ : syracuseStep 2755931 = 4133897) B4133897
theorem B128945519 : Blo 1835619 128945519 := bstep (se 1 (by rfl) ⟨96709139, by rfl⟩ : syracuseStep 128945519 = 193418279) B193418279
theorem B3100025 : Blo 1835619 3100025 := bstep (se 2 (by rfl) ⟨1162509, by rfl⟩ : syracuseStep 3100025 = 2325019) B2325019
theorem B2755961 : Blo 1835619 2755961 := bstep (se 2 (by rfl) ⟨1033485, by rfl⟩ : syracuseStep 2755961 = 2066971) B2066971
theorem B6196607 : Blo 1835619 6196607 := bstep (se 1 (by rfl) ⟨4647455, by rfl⟩ : syracuseStep 6196607 = 9294911) B9294911
theorem B4132223 : Blo 1835619 4132223 := bstep (se 1 (by rfl) ⟨3099167, by rfl⟩ : syracuseStep 4132223 = 6198335) B6198335
theorem B2755967 : Blo 1835619 2755967 := bstep (se 1 (by rfl) ⟨2066975, by rfl⟩ : syracuseStep 2755967 = 4133951) B4133951
theorem B6712903 : Blo 1835619 6712903 := bstep (se 1 (by rfl) ⟨5034677, by rfl⟩ : syracuseStep 6712903 = 10069355) B10069355
theorem B9924299 : Blo 1835619 9924299 := bstep (se 1 (by rfl) ⟨7443224, by rfl⟩ : syracuseStep 9924299 = 14886449) B14886449
theorem B23859089 : Blo 1835619 23859089 := bstep (se 2 (by rfl) ⟨8947158, by rfl⟩ : syracuseStep 23859089 = 17894317) B17894317
theorem B5885885 : Blo 1835619 5885885 := bstep (se 3 (by rfl) ⟨1103603, by rfl⟩ : syracuseStep 5885885 = 2207207) B2207207
theorem B3100727 : Blo 1835619 3100727 := bstep (se 1 (by rfl) ⟨2325545, by rfl⟩ : syracuseStep 3100727 = 4651091) B4651091
theorem B9302201 : Blo 1835619 9302201 := bstep (se 2 (by rfl) ⟨3488325, by rfl⟩ : syracuseStep 9302201 = 6976651) B6976651
theorem B13947227 : Blo 1835619 13947227 := bstep (se 1 (by rfl) ⟨10460420, by rfl⟩ : syracuseStep 13947227 = 20920841) B20920841
theorem B13242953 : Blo 1835619 13242953 := bstep (se 2 (by rfl) ⟨4966107, by rfl⟩ : syracuseStep 13242953 = 9932215) B9932215
theorem B14897803 : Blo 1835619 14897803 := bstep (se 1 (by rfl) ⟨11173352, by rfl⟩ : syracuseStep 14897803 = 22346705) B22346705
theorem B3486473 : Blo 1835619 3486473 := bstep (se 2 (by rfl) ⟨1307427, by rfl⟩ : syracuseStep 3486473 = 2614855) B2614855
theorem B7844633 : Blo 1835619 7844633 := bstep (se 2 (by rfl) ⟨2941737, by rfl⟩ : syracuseStep 7844633 = 5883475) B5883475
theorem B4134095 : Blo 1835619 4134095 := bstep (se 1 (by rfl) ⟨3100571, by rfl⟩ : syracuseStep 4134095 = 6201143) B6201143
theorem B4134185 : Blo 1835619 4134185 := bstep (se 2 (by rfl) ⟨1550319, by rfl⟩ : syracuseStep 4134185 = 3100639) B3100639
theorem B84866467 : Blo 1835619 84866467 := bstep (se 1 (by rfl) ⟨63649850, by rfl⟩ : syracuseStep 84866467 = 127299701) B127299701
theorem B3487187 : Blo 1835619 3487187 := bstep (se 1 (by rfl) ⟨2615390, by rfl⟩ : syracuseStep 3487187 = 5230781) B5230781
theorem B4134383 : Blo 1835619 4134383 := bstep (se 1 (by rfl) ⟨3100787, by rfl⟩ : syracuseStep 4134383 = 6201575) B6201575
theorem B8828441 : Blo 1835619 8828441 := bstep (se 2 (by rfl) ⟨3310665, by rfl⟩ : syracuseStep 8828441 = 6621331) B6621331
theorem B26490401 : Blo 1835619 26490401 := bstep (se 2 (by rfl) ⟨9933900, by rfl⟩ : syracuseStep 26490401 = 19867801) B19867801
theorem B5584607 : Blo 1835619 5584607 := bstep (se 1 (by rfl) ⟨4188455, by rfl⟩ : syracuseStep 5584607 = 8376911) B8376911
theorem B33519329 : Blo 1835619 33519329 := bstep (se 2 (by rfl) ⟨12569748, by rfl⟩ : syracuseStep 33519329 = 25139497) B25139497
theorem B3921787 : Blo 1835619 3921787 := bstep (se 1 (by rfl) ⟨2941340, by rfl⟩ : syracuseStep 3921787 = 5882681) B5882681
theorem B7845761 : Blo 1835619 7845761 := bstep (se 2 (by rfl) ⟨2942160, by rfl⟩ : syracuseStep 7845761 = 5884321) B5884321
theorem B6199199 : Blo 1835619 6199199 := bstep (se 1 (by rfl) ⟨4649399, by rfl⟩ : syracuseStep 6199199 = 9298799) B9298799
theorem B16750583 : Blo 1835619 16750583 := bstep (se 1 (by rfl) ⟨12562937, by rfl⟩ : syracuseStep 16750583 = 25125875) B25125875
theorem B4962539 : Blo 1835619 4962539 := bstep (se 1 (by rfl) ⟨3721904, by rfl⟩ : syracuseStep 4962539 = 7443809) B7443809
theorem B6969833 : Blo 1835619 6969833 := bstep (se 2 (by rfl) ⟨2613687, by rfl⟩ : syracuseStep 6969833 = 5227375) B5227375
theorem B3308123 : Blo 1835619 3308123 := bstep (se 1 (by rfl) ⟨2481092, by rfl⟩ : syracuseStep 3308123 = 4962185) B4962185
theorem B12565151 : Blo 1835619 12565151 := bstep (se 1 (by rfl) ⟨9423863, by rfl⟩ : syracuseStep 12565151 = 18847727) B18847727
theorem B35314379 : Blo 1835619 35314379 := bstep (se 1 (by rfl) ⟨26485784, by rfl⟩ : syracuseStep 35314379 = 52971569) B52971569
theorem B8821561 : Blo 1835619 8821561 := bstep (se 2 (by rfl) ⟨3308085, by rfl⟩ : syracuseStep 8821561 = 6616171) B6616171
theorem B6200441 : Blo 1835619 6200441 := bstep (se 2 (by rfl) ⟨2325165, by rfl⟩ : syracuseStep 6200441 = 4650331) B4650331
theorem B50969843 : Blo 1835619 50969843 := bstep (se 1 (by rfl) ⟨38227382, by rfl⟩ : syracuseStep 50969843 = 76454765) B76454765
theorem B70622603 : Blo 1835619 70622603 := bstep (se 1 (by rfl) ⟨52966952, by rfl⟩ : syracuseStep 70622603 = 105933905) B105933905
theorem B7847351 : Blo 1835619 7847351 := bstep (se 1 (by rfl) ⟨5885513, by rfl⟩ : syracuseStep 7847351 = 11771027) B11771027
theorem B10460603 : Blo 1835619 10460603 := bstep (se 1 (by rfl) ⟨7845452, by rfl⟩ : syracuseStep 10460603 = 15690905) B15690905
theorem B6970819 : Blo 1835619 6970819 := bstep (se 1 (by rfl) ⟨5228114, by rfl⟩ : syracuseStep 6970819 = 10456229) B10456229
theorem B4709879 : Blo 1835619 4709879 := bstep (se 1 (by rfl) ⟨3532409, by rfl⟩ : syracuseStep 4709879 = 7064819) B7064819
theorem B3309167 : Blo 1835619 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B3227359 : Blo 1835619 3227359 := bstep (se 1 (by rfl) ⟨2420519, by rfl⟩ : syracuseStep 3227359 = 4841039) B4841039
theorem B6971291 : Blo 1835619 6971291 := bstep (se 1 (by rfl) ⟨5228468, by rfl⟩ : syracuseStep 6971291 = 10456937) B10456937
theorem B6201467 : Blo 1835619 6201467 := bstep (se 1 (by rfl) ⟨4651100, by rfl⟩ : syracuseStep 6201467 = 9302201) B9302201
theorem B9298151 : Blo 1835619 9298151 := bstep (se 1 (by rfl) ⟨6973613, by rfl⟩ : syracuseStep 9298151 = 13947227) B13947227
theorem B26476793 : Blo 1835619 26476793 := bstep (se 2 (by rfl) ⟨9928797, by rfl⟩ : syracuseStep 26476793 = 19857595) B19857595
theorem B11764079 : Blo 1835619 11764079 := bstep (se 1 (by rfl) ⟨8823059, by rfl⟩ : syracuseStep 11764079 = 17646119) B17646119
theorem B10060361 : Blo 1835619 10060361 := bstep (se 2 (by rfl) ⟨3772635, by rfl⟩ : syracuseStep 10060361 = 7545271) B7545271
theorem B1835839 : Blo 1835619 1835839 := bstep (se 1 (by rfl) ⟨1376879, by rfl⟩ : syracuseStep 1835839 = 2753759) B2753759
theorem B1835847 : Blo 1835619 1835847 := bstep (se 1 (by rfl) ⟨1376885, by rfl⟩ : syracuseStep 1835847 = 2753771) B2753771
theorem B1836103 : Blo 1835619 1836103 := bstep (se 1 (by rfl) ⟨1377077, by rfl⟩ : syracuseStep 1836103 = 2754155) B2754155
theorem B2753663 : Blo 1835619 2753663 := bstep (se 1 (by rfl) ⟨2065247, by rfl⟩ : syracuseStep 2753663 = 4130495) B4130495
theorem B1836159 : Blo 1835619 1836159 := bstep (se 1 (by rfl) ⟨1377119, by rfl⟩ : syracuseStep 1836159 = 2754239) B2754239
theorem B1836283 : Blo 1835619 1836283 := bstep (se 1 (by rfl) ⟨1377212, by rfl⟩ : syracuseStep 1836283 = 2754425) B2754425
theorem B2753801 : Blo 1835619 2753801 := bstep (se 2 (by rfl) ⟨1032675, by rfl⟩ : syracuseStep 2753801 = 2065351) B2065351
theorem B5883167 : Blo 1835619 5883167 := bstep (se 1 (by rfl) ⟨4412375, by rfl⟩ : syracuseStep 5883167 = 8824751) B8824751
theorem B2483497 : Blo 1835619 2483497 := bstep (se 2 (by rfl) ⟨931311, by rfl⟩ : syracuseStep 2483497 = 1862623) B1862623
theorem B11167055 : Blo 1835619 11167055 := bstep (se 1 (by rfl) ⟨8375291, by rfl⟩ : syracuseStep 11167055 = 16750583) B16750583
theorem B5662109 : Blo 1835619 5662109 := bstep (se 3 (by rfl) ⟨1061645, by rfl⟩ : syracuseStep 5662109 = 2123291) B2123291
theorem B18843131 : Blo 1835619 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B4646555 : Blo 1835619 4646555 := bstep (se 1 (by rfl) ⟨3484916, by rfl⟩ : syracuseStep 4646555 = 6969833) B6969833
theorem B2205415 : Blo 1835619 2205415 := bstep (se 1 (by rfl) ⟨1654061, by rfl⟩ : syracuseStep 2205415 = 3308123) B3308123
theorem B2754281 : Blo 1835619 2754281 := bstep (se 2 (by rfl) ⟨1032855, by rfl⟩ : syracuseStep 2754281 = 2065711) B2065711
theorem B2754287 : Blo 1835619 2754287 := bstep (se 1 (by rfl) ⟨2065715, by rfl⟩ : syracuseStep 2754287 = 4131431) B4131431
theorem B1836783 : Blo 1835619 1836783 := bstep (se 1 (by rfl) ⟨1377587, by rfl⟩ : syracuseStep 1836783 = 2755175) B2755175
theorem B2066287 : Blo 1835619 2066287 := bstep (se 1 (by rfl) ⟨1549715, by rfl⟩ : syracuseStep 2066287 = 3099431) B3099431
theorem B1836911 : Blo 1835619 1836911 := bstep (se 1 (by rfl) ⟨1377683, by rfl⟩ : syracuseStep 1836911 = 2755367) B2755367
theorem B2754539 : Blo 1835619 2754539 := bstep (se 1 (by rfl) ⟨2065904, by rfl⟩ : syracuseStep 2754539 = 4131809) B4131809
theorem B2066503 : Blo 1835619 2066503 := bstep (se 1 (by rfl) ⟨1549877, by rfl⟩ : syracuseStep 2066503 = 3099755) B3099755
theorem B1837127 : Blo 1835619 1837127 := bstep (se 1 (by rfl) ⟨1377845, by rfl⟩ : syracuseStep 1837127 = 2755691) B2755691
theorem B2754791 : Blo 1835619 2754791 := bstep (se 1 (by rfl) ⟨2066093, by rfl⟩ : syracuseStep 2754791 = 4132187) B4132187
theorem B1837287 : Blo 1835619 1837287 := bstep (se 1 (by rfl) ⟨1377965, by rfl⟩ : syracuseStep 1837287 = 2755931) B2755931
theorem B2066683 : Blo 1835619 2066683 := bstep (se 1 (by rfl) ⟨1550012, by rfl⟩ : syracuseStep 2066683 = 3100025) B3100025
theorem B1837307 : Blo 1835619 1837307 := bstep (se 1 (by rfl) ⟨1377980, by rfl⟩ : syracuseStep 1837307 = 2755961) B2755961
theorem B4131071 : Blo 1835619 4131071 := bstep (se 1 (by rfl) ⟨3098303, by rfl⟩ : syracuseStep 4131071 = 6196607) B6196607
theorem B2754815 : Blo 1835619 2754815 := bstep (se 1 (by rfl) ⟨2066111, by rfl⟩ : syracuseStep 2754815 = 4132223) B4132223
theorem B1837311 : Blo 1835619 1837311 := bstep (se 1 (by rfl) ⟨1377983, by rfl⟩ : syracuseStep 1837311 = 2755967) B2755967
theorem B47081735 : Blo 1835619 47081735 := bstep (se 1 (by rfl) ⟨35311301, by rfl⟩ : syracuseStep 47081735 = 70622603) B70622603
theorem B6973735 : Blo 1835619 6973735 := bstep (se 1 (by rfl) ⟨5230301, by rfl⟩ : syracuseStep 6973735 = 10460603) B10460603
theorem B4303145 : Blo 1835619 4303145 := bstep (se 2 (by rfl) ⟨1613679, by rfl⟩ : syracuseStep 4303145 = 3227359) B3227359
theorem B3139919 : Blo 1835619 3139919 := bstep (se 1 (by rfl) ⟨2354939, by rfl⟩ : syracuseStep 3139919 = 4709879) B4709879
theorem B2754953 : Blo 1835619 2754953 := bstep (se 2 (by rfl) ⟨1033107, by rfl⟩ : syracuseStep 2754953 = 2066215) B2066215
theorem B2206111 : Blo 1835619 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B5229049 : Blo 1835619 5229049 := bstep (se 2 (by rfl) ⟨1960893, by rfl⟩ : syracuseStep 5229049 = 3921787) B3921787
theorem B4647527 : Blo 1835619 4647527 := bstep (se 1 (by rfl) ⟨3485645, by rfl⟩ : syracuseStep 4647527 = 6971291) B6971291
theorem B2067151 : Blo 1835619 2067151 := bstep (se 1 (by rfl) ⟨1550363, by rfl⟩ : syracuseStep 2067151 = 3100727) B3100727
theorem B5229755 : Blo 1835619 5229755 := bstep (se 1 (by rfl) ⟨3922316, by rfl⟩ : syracuseStep 5229755 = 7844633) B7844633
theorem B1961167 : Blo 1835619 1961167 := bstep (se 1 (by rfl) ⟨1470875, by rfl⟩ : syracuseStep 1961167 = 2941751) B2941751
theorem B7843027 : Blo 1835619 7843027 := bstep (se 1 (by rfl) ⟨5882270, by rfl⟩ : syracuseStep 7843027 = 11764541) B11764541
theorem B5967101 : Blo 1835619 5967101 := bstep (se 3 (by rfl) ⟨1118831, by rfl⟩ : syracuseStep 5967101 = 2237663) B2237663
theorem B6196553 : Blo 1835619 6196553 := bstep (se 2 (by rfl) ⟨2323707, by rfl⟩ : syracuseStep 6196553 = 4647415) B4647415
theorem B2756063 : Blo 1835619 2756063 := bstep (se 1 (by rfl) ⟨2067047, by rfl⟩ : syracuseStep 2756063 = 4134095) B4134095
theorem B135802379 : Blo 1835619 135802379 := bstep (se 1 (by rfl) ⟨101851784, by rfl⟩ : syracuseStep 135802379 = 203703569) B203703569
theorem B2756123 : Blo 1835619 2756123 := bstep (se 1 (by rfl) ⟨2067092, by rfl⟩ : syracuseStep 2756123 = 4134185) B4134185
theorem B2756255 : Blo 1835619 2756255 := bstep (se 1 (by rfl) ⟨2067191, by rfl⟩ : syracuseStep 2756255 = 4134383) B4134383
theorem B5885627 : Blo 1835619 5885627 := bstep (se 1 (by rfl) ⟨4414220, by rfl⟩ : syracuseStep 5885627 = 8828441) B8828441
theorem B5230507 : Blo 1835619 5230507 := bstep (se 1 (by rfl) ⟨3922880, by rfl⟩ : syracuseStep 5230507 = 7845761) B7845761
theorem B4132799 : Blo 1835619 4132799 := bstep (se 1 (by rfl) ⟨3099599, by rfl⟩ : syracuseStep 4132799 = 6199199) B6199199
theorem B4649015 : Blo 1835619 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B8376767 : Blo 1835619 8376767 := bstep (se 1 (by rfl) ⟨6282575, by rfl⟩ : syracuseStep 8376767 = 12565151) B12565151
theorem B9294425 : Blo 1835619 9294425 := bstep (se 2 (by rfl) ⟨3485409, by rfl⟩ : syracuseStep 9294425 = 6970819) B6970819
theorem B4133627 : Blo 1835619 4133627 := bstep (se 1 (by rfl) ⟨3100220, by rfl⟩ : syracuseStep 4133627 = 6200441) B6200441
theorem B8950537 : Blo 1835619 8950537 := bstep (se 2 (by rfl) ⟨3356451, by rfl⟩ : syracuseStep 8950537 = 6712903) B6712903
theorem B85963679 : Blo 1835619 85963679 := bstep (se 1 (by rfl) ⟨64472759, by rfl⟩ : syracuseStep 85963679 = 128945519) B128945519
theorem B5231567 : Blo 1835619 5231567 := bstep (se 1 (by rfl) ⟨3923675, by rfl⟩ : syracuseStep 5231567 = 7847351) B7847351
theorem B59569141 : Blo 1835619 59569141 := bstep (se 5 (by rfl) ⟨2792303, by rfl⟩ : syracuseStep 59569141 = 5584607) B5584607
theorem B6616199 : Blo 1835619 6616199 := bstep (se 1 (by rfl) ⟨4962149, by rfl⟩ : syracuseStep 6616199 = 9924299) B9924299
theorem B6452477 : Blo 1835619 6452477 := bstep (se 3 (by rfl) ⟨1209839, by rfl⟩ : syracuseStep 6452477 = 2419679) B2419679
theorem B15906059 : Blo 1835619 15906059 := bstep (se 1 (by rfl) ⟨11929544, by rfl⟩ : syracuseStep 15906059 = 23859089) B23859089
theorem B5101231 : Blo 1835619 5101231 := bstep (se 1 (by rfl) ⟨3825923, by rfl⟩ : syracuseStep 5101231 = 7651847) B7651847
theorem B8828635 : Blo 1835619 8828635 := bstep (se 1 (by rfl) ⟨6621476, by rfl⟩ : syracuseStep 8828635 = 13242953) B13242953
theorem B14890729 : Blo 1835619 14890729 := bstep (se 2 (by rfl) ⟨5584023, by rfl⟩ : syracuseStep 14890729 = 11168047) B11168047
theorem B2324315 : Blo 1835619 2324315 := bstep (se 1 (by rfl) ⟨1743236, by rfl⟩ : syracuseStep 2324315 = 3486473) B3486473
theorem B19863737 : Blo 1835619 19863737 := bstep (se 2 (by rfl) ⟨7448901, by rfl⟩ : syracuseStep 19863737 = 14897803) B14897803
theorem B2324791 : Blo 1835619 2324791 := bstep (se 1 (by rfl) ⟨1743593, by rfl⟩ : syracuseStep 2324791 = 3487187) B3487187
theorem B6199631 : Blo 1835619 6199631 := bstep (se 1 (by rfl) ⟨4649723, by rfl⟩ : syracuseStep 6199631 = 9299447) B9299447
theorem B17660267 : Blo 1835619 17660267 := bstep (se 1 (by rfl) ⟨13245200, by rfl⟩ : syracuseStep 17660267 = 26490401) B26490401
theorem B11762081 : Blo 1835619 11762081 := bstep (se 2 (by rfl) ⟨4410780, by rfl⟩ : syracuseStep 11762081 = 8821561) B8821561
theorem B14899621 : Blo 1835619 14899621 := bstep (se 4 (by rfl) ⟨1396839, by rfl⟩ : syracuseStep 14899621 = 2793679) B2793679
theorem B22346219 : Blo 1835619 22346219 := bstep (se 1 (by rfl) ⟨16759664, by rfl⟩ : syracuseStep 22346219 = 33519329) B33519329
theorem B2792171 : Blo 1835619 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B3308359 : Blo 1835619 3308359 := bstep (se 1 (by rfl) ⟨2481269, by rfl⟩ : syracuseStep 3308359 = 4962539) B4962539
theorem B6970319 : Blo 1835619 6970319 := bstep (se 1 (by rfl) ⟨5227739, by rfl⟩ : syracuseStep 6970319 = 10455479) B10455479
theorem B13941881 : Blo 1835619 13941881 := bstep (se 2 (by rfl) ⟨5228205, by rfl⟩ : syracuseStep 13941881 = 10456411) B10456411
theorem B23542919 : Blo 1835619 23542919 := bstep (se 1 (by rfl) ⟨17657189, by rfl⟩ : syracuseStep 23542919 = 35314379) B35314379
theorem B113155289 : Blo 1835619 113155289 := bstep (se 2 (by rfl) ⟨42433233, by rfl⟩ : syracuseStep 113155289 = 84866467) B84866467
theorem B3923273 : Blo 1835619 3923273 := bstep (se 2 (by rfl) ⟨1471227, by rfl⟩ : syracuseStep 3923273 = 2942455) B2942455
theorem B3923291 : Blo 1835619 3923291 := bstep (se 1 (by rfl) ⟨2942468, by rfl⟩ : syracuseStep 3923291 = 5884937) B5884937
theorem B33979895 : Blo 1835619 33979895 := bstep (se 1 (by rfl) ⟨25484921, by rfl⟩ : syracuseStep 33979895 = 50969843) B50969843
theorem B3923923 : Blo 1835619 3923923 := bstep (se 1 (by rfl) ⟨2942942, by rfl⟩ : syracuseStep 3923923 = 5885885) B5885885
theorem B9298313 : Blo 1835619 9298313 := bstep (se 2 (by rfl) ⟨3486867, by rfl⟩ : syracuseStep 9298313 = 6973735) B6973735
theorem B2941481 : Blo 1835619 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B19866161 : Blo 1835619 19866161 := bstep (se 2 (by rfl) ⟨7449810, by rfl⟩ : syracuseStep 19866161 = 14899621) B14899621
theorem B6972065 : Blo 1835619 6972065 := bstep (se 2 (by rfl) ⟨2614524, by rfl⟩ : syracuseStep 6972065 = 5229049) B5229049
theorem B1835775 : Blo 1835619 1835775 := bstep (se 1 (by rfl) ⟨1376831, by rfl⟩ : syracuseStep 1835775 = 2753663) B2753663
theorem B4301651 : Blo 1835619 4301651 := bstep (se 1 (by rfl) ⟨3226238, by rfl⟩ : syracuseStep 4301651 = 6452477) B6452477
theorem B1835867 : Blo 1835619 1835867 := bstep (se 1 (by rfl) ⟨1376900, by rfl⟩ : syracuseStep 1835867 = 2753801) B2753801
theorem B10462061 : Blo 1835619 10462061 := bstep (se 3 (by rfl) ⟨1961636, by rfl⟩ : syracuseStep 10462061 = 3923273) B3923273
theorem B15098957 : Blo 1835619 15098957 := bstep (se 3 (by rfl) ⟨2831054, by rfl⟩ : syracuseStep 15098957 = 5662109) B5662109
theorem B3097703 : Blo 1835619 3097703 := bstep (se 1 (by rfl) ⟨2323277, by rfl⟩ : syracuseStep 3097703 = 4646555) B4646555
theorem B1836187 : Blo 1835619 1836187 := bstep (se 1 (by rfl) ⟨1377140, by rfl⟩ : syracuseStep 1836187 = 2754281) B2754281
theorem B1836191 : Blo 1835619 1836191 := bstep (se 1 (by rfl) ⟨1377143, by rfl⟩ : syracuseStep 1836191 = 2754287) B2754287
theorem B1836359 : Blo 1835619 1836359 := bstep (se 1 (by rfl) ⟨1377269, by rfl⟩ : syracuseStep 1836359 = 2754539) B2754539
theorem B1836527 : Blo 1835619 1836527 := bstep (se 1 (by rfl) ⟨1377395, by rfl⟩ : syracuseStep 1836527 = 2754791) B2754791
theorem B2754047 : Blo 1835619 2754047 := bstep (se 1 (by rfl) ⟨2065535, by rfl⟩ : syracuseStep 2754047 = 4131071) B4131071
theorem B1836543 : Blo 1835619 1836543 := bstep (se 1 (by rfl) ⟨1377407, by rfl⟩ : syracuseStep 1836543 = 2754815) B2754815
theorem B11773511 : Blo 1835619 11773511 := bstep (se 1 (by rfl) ⟨8830133, by rfl⟩ : syracuseStep 11773511 = 17660267) B17660267
theorem B1836635 : Blo 1835619 1836635 := bstep (se 1 (by rfl) ⟨1377476, by rfl⟩ : syracuseStep 1836635 = 2754953) B2754953
theorem B2614889 : Blo 1835619 2614889 := bstep (se 2 (by rfl) ⟨980583, by rfl⟩ : syracuseStep 2614889 = 1961167) B1961167
theorem B7841387 : Blo 1835619 7841387 := bstep (se 1 (by rfl) ⟨5881040, by rfl⟩ : syracuseStep 7841387 = 11762081) B11762081
theorem B3311329 : Blo 1835619 3311329 := bstep (se 2 (by rfl) ⟨1241748, by rfl⟩ : syracuseStep 3311329 = 2483497) B2483497
theorem B3098351 : Blo 1835619 3098351 := bstep (se 1 (by rfl) ⟨2323763, by rfl⟩ : syracuseStep 3098351 = 4647527) B4647527
theorem B4646879 : Blo 1835619 4646879 := bstep (se 1 (by rfl) ⟨3485159, by rfl⟩ : syracuseStep 4646879 = 6970319) B6970319
theorem B4131035 : Blo 1835619 4131035 := bstep (se 1 (by rfl) ⟨3098276, by rfl⟩ : syracuseStep 4131035 = 6196553) B6196553
theorem B2615527 : Blo 1835619 2615527 := bstep (se 1 (by rfl) ⟨1961645, by rfl⟩ : syracuseStep 2615527 = 3923291) B3923291
theorem B6801641 : Blo 1835619 6801641 := bstep (se 2 (by rfl) ⟨2550615, by rfl⟩ : syracuseStep 6801641 = 5101231) B5101231
theorem B1837375 : Blo 1835619 1837375 := bstep (se 1 (by rfl) ⟨1378031, by rfl⟩ : syracuseStep 1837375 = 2756063) B2756063
theorem B22653263 : Blo 1835619 22653263 := bstep (se 1 (by rfl) ⟨16989947, by rfl⟩ : syracuseStep 22653263 = 33979895) B33979895
theorem B1837415 : Blo 1835619 1837415 := bstep (se 1 (by rfl) ⟨1378061, by rfl⟩ : syracuseStep 1837415 = 2756123) B2756123
theorem B1837503 : Blo 1835619 1837503 := bstep (se 1 (by rfl) ⟨1378127, by rfl⟩ : syracuseStep 1837503 = 2756255) B2756255
theorem B2755049 : Blo 1835619 2755049 := bstep (se 2 (by rfl) ⟨1033143, by rfl⟩ : syracuseStep 2755049 = 2066287) B2066287
theorem B6974009 : Blo 1835619 6974009 := bstep (se 2 (by rfl) ⟨2615253, by rfl⟩ : syracuseStep 6974009 = 5230507) B5230507
theorem B2755199 : Blo 1835619 2755199 := bstep (se 1 (by rfl) ⟨2066399, by rfl⟩ : syracuseStep 2755199 = 4132799) B4132799
theorem B3099343 : Blo 1835619 3099343 := bstep (se 1 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 3099343 = 4649015) B4649015
theorem B2755337 : Blo 1835619 2755337 := bstep (se 2 (by rfl) ⟨1033251, by rfl⟩ : syracuseStep 2755337 = 2066503) B2066503
theorem B7842719 : Blo 1835619 7842719 := bstep (se 1 (by rfl) ⟨5882039, by rfl⟩ : syracuseStep 7842719 = 11764079) B11764079
theorem B2755577 : Blo 1835619 2755577 := bstep (se 2 (by rfl) ⟨1033341, by rfl⟩ : syracuseStep 2755577 = 2066683) B2066683
theorem B6196283 : Blo 1835619 6196283 := bstep (se 1 (by rfl) ⟨4647212, by rfl⟩ : syracuseStep 6196283 = 9294425) B9294425
theorem B3099721 : Blo 1835619 3099721 := bstep (se 2 (by rfl) ⟨1162395, by rfl⟩ : syracuseStep 3099721 = 2324791) B2324791
theorem B2755751 : Blo 1835619 2755751 := bstep (se 1 (by rfl) ⟨2066813, by rfl⟩ : syracuseStep 2755751 = 4133627) B4133627
theorem B10604039 : Blo 1835619 10604039 := bstep (se 1 (by rfl) ⟨7953029, by rfl⟩ : syracuseStep 10604039 = 15906059) B15906059
theorem B2756201 : Blo 1835619 2756201 := bstep (se 2 (by rfl) ⟨1033575, by rfl⟩ : syracuseStep 2756201 = 2067151) B2067151
theorem B12562087 : Blo 1835619 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B4411145 : Blo 1835619 4411145 := bstep (se 2 (by rfl) ⟨1654179, by rfl⟩ : syracuseStep 4411145 = 3308359) B3308359
theorem B79425521 : Blo 1835619 79425521 := bstep (se 2 (by rfl) ⟨29784570, by rfl⟩ : syracuseStep 79425521 = 59569141) B59569141
theorem B13242491 : Blo 1835619 13242491 := bstep (se 1 (by rfl) ⟨9931868, by rfl⟩ : syracuseStep 13242491 = 19863737) B19863737
theorem B31387823 : Blo 1835619 31387823 := bstep (se 1 (by rfl) ⟨23540867, by rfl⟩ : syracuseStep 31387823 = 47081735) B47081735
theorem B2093279 : Blo 1835619 2093279 := bstep (se 1 (by rfl) ⟨1569959, by rfl⟩ : syracuseStep 2093279 = 3139919) B3139919
theorem B4133087 : Blo 1835619 4133087 := bstep (se 1 (by rfl) ⟨3099815, by rfl⟩ : syracuseStep 4133087 = 6199631) B6199631
theorem B10457369 : Blo 1835619 10457369 := bstep (se 2 (by rfl) ⟨3921513, by rfl⟩ : syracuseStep 10457369 = 7843027) B7843027
theorem B14897479 : Blo 1835619 14897479 := bstep (se 1 (by rfl) ⟨11173109, by rfl⟩ : syracuseStep 14897479 = 22346219) B22346219
theorem B9294587 : Blo 1835619 9294587 := bstep (se 1 (by rfl) ⟨6970940, by rfl⟩ : syracuseStep 9294587 = 13941881) B13941881
theorem B3486503 : Blo 1835619 3486503 := bstep (se 1 (by rfl) ⟨2614877, by rfl⟩ : syracuseStep 3486503 = 5229755) B5229755
theorem B75436859 : Blo 1835619 75436859 := bstep (se 1 (by rfl) ⟨56577644, by rfl⟩ : syracuseStep 75436859 = 113155289) B113155289
theorem B3978067 : Blo 1835619 3978067 := bstep (se 1 (by rfl) ⟨2983550, by rfl⟩ : syracuseStep 3978067 = 5967101) B5967101
theorem B6198173 : Blo 1835619 6198173 := bstep (se 3 (by rfl) ⟨1162157, by rfl⟩ : syracuseStep 6198173 = 2324315) B2324315
theorem B19854305 : Blo 1835619 19854305 := bstep (se 2 (by rfl) ⟨7445364, by rfl⟩ : syracuseStep 19854305 = 14890729) B14890729
theorem B90534919 : Blo 1835619 90534919 := bstep (se 1 (by rfl) ⟨67901189, by rfl⟩ : syracuseStep 90534919 = 135802379) B135802379
theorem B5231897 : Blo 1835619 5231897 := bstep (se 2 (by rfl) ⟨1961961, by rfl⟩ : syracuseStep 5231897 = 3923923) B3923923
theorem B4134311 : Blo 1835619 4134311 := bstep (se 1 (by rfl) ⟨3100733, by rfl⟩ : syracuseStep 4134311 = 6201467) B6201467
theorem B6198767 : Blo 1835619 6198767 := bstep (se 1 (by rfl) ⟨4649075, by rfl⟩ : syracuseStep 6198767 = 9298151) B9298151
theorem B17651195 : Blo 1835619 17651195 := bstep (se 1 (by rfl) ⟨13238396, by rfl⟩ : syracuseStep 17651195 = 26476793) B26476793
theorem B5584511 : Blo 1835619 5584511 := bstep (se 1 (by rfl) ⟨4188383, by rfl⟩ : syracuseStep 5584511 = 8376767) B8376767
theorem B17643197 : Blo 1835619 17643197 := bstep (se 3 (by rfl) ⟨3308099, by rfl⟩ : syracuseStep 17643197 = 6616199) B6616199
theorem B6706907 : Blo 1835619 6706907 := bstep (se 1 (by rfl) ⟨5030180, by rfl⟩ : syracuseStep 6706907 = 10060361) B10060361
theorem B57309119 : Blo 1835619 57309119 := bstep (se 1 (by rfl) ⟨42981839, by rfl⟩ : syracuseStep 57309119 = 85963679) B85963679
theorem B3487711 : Blo 1835619 3487711 := bstep (se 1 (by rfl) ⟨2615783, by rfl⟩ : syracuseStep 3487711 = 5231567) B5231567
theorem B11475053 : Blo 1835619 11475053 := bstep (se 3 (by rfl) ⟨2151572, by rfl⟩ : syracuseStep 11475053 = 4303145) B4303145
theorem B3922111 : Blo 1835619 3922111 := bstep (se 1 (by rfl) ⟨2941583, by rfl⟩ : syracuseStep 3922111 = 5883167) B5883167
theorem B7444703 : Blo 1835619 7444703 := bstep (se 1 (by rfl) ⟨5583527, by rfl⟩ : syracuseStep 7444703 = 11167055) B11167055
theorem B11934049 : Blo 1835619 11934049 := bstep (se 2 (by rfl) ⟨4475268, by rfl⟩ : syracuseStep 11934049 = 8950537) B8950537
theorem B15695005 : Blo 1835619 15695005 := bstep (se 3 (by rfl) ⟨2942813, by rfl⟩ : syracuseStep 15695005 = 5885627) B5885627
theorem B7445789 : Blo 1835619 7445789 := bstep (se 3 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 7445789 = 2792171) B2792171
theorem B15695279 : Blo 1835619 15695279 := bstep (se 1 (by rfl) ⟨11771459, by rfl⟩ : syracuseStep 15695279 = 23542919) B23542919
theorem B11771513 : Blo 1835619 11771513 := bstep (se 2 (by rfl) ⟨4414317, by rfl⟩ : syracuseStep 11771513 = 8828635) B8828635
theorem B2940553 : Blo 1835619 2940553 := bstep (se 2 (by rfl) ⟨1102707, by rfl⟩ : syracuseStep 2940553 = 2205415) B2205415
theorem B6971579 : Blo 1835619 6971579 := bstep (se 1 (by rfl) ⟨5228684, by rfl⟩ : syracuseStep 6971579 = 10457369) B10457369
theorem B50291239 : Blo 1835619 50291239 := bstep (se 1 (by rfl) ⟨37718429, by rfl⟩ : syracuseStep 50291239 = 75436859) B75436859
theorem B2065135 : Blo 1835619 2065135 := bstep (se 1 (by rfl) ⟨1548851, by rfl⟩ : syracuseStep 2065135 = 3097703) B3097703
theorem B1836031 : Blo 1835619 1836031 := bstep (se 1 (by rfl) ⟨1377023, by rfl⟩ : syracuseStep 1836031 = 2754047) B2754047
theorem B7849007 : Blo 1835619 7849007 := bstep (se 1 (by rfl) ⟨5886755, by rfl⟩ : syracuseStep 7849007 = 11773511) B11773511
theorem B5227591 : Blo 1835619 5227591 := bstep (se 1 (by rfl) ⟨3920693, by rfl⟩ : syracuseStep 5227591 = 7841387) B7841387
theorem B2065567 : Blo 1835619 2065567 := bstep (se 1 (by rfl) ⟨1549175, by rfl⟩ : syracuseStep 2065567 = 3098351) B3098351
theorem B3097919 : Blo 1835619 3097919 := bstep (se 1 (by rfl) ⟨2323439, by rfl⟩ : syracuseStep 3097919 = 4646879) B4646879
theorem B2754023 : Blo 1835619 2754023 := bstep (se 1 (by rfl) ⟨2065517, by rfl⟩ : syracuseStep 2754023 = 4131035) B4131035
theorem B6973037 : Blo 1835619 6973037 := bstep (se 3 (by rfl) ⟨1307444, by rfl⟩ : syracuseStep 6973037 = 2614889) B2614889
theorem B1836699 : Blo 1835619 1836699 := bstep (se 1 (by rfl) ⟨1377524, by rfl⟩ : syracuseStep 1836699 = 2755049) B2755049
theorem B1836799 : Blo 1835619 1836799 := bstep (se 1 (by rfl) ⟨1377599, by rfl⟩ : syracuseStep 1836799 = 2755199) B2755199
theorem B1836891 : Blo 1835619 1836891 := bstep (se 1 (by rfl) ⟨1377668, by rfl⟩ : syracuseStep 1836891 = 2755337) B2755337
theorem B5228479 : Blo 1835619 5228479 := bstep (se 1 (by rfl) ⟨3921359, by rfl⟩ : syracuseStep 5228479 = 7842719) B7842719
theorem B1837051 : Blo 1835619 1837051 := bstep (se 1 (by rfl) ⟨1377788, by rfl⟩ : syracuseStep 1837051 = 2755577) B2755577
theorem B4130855 : Blo 1835619 4130855 := bstep (se 1 (by rfl) ⟨3098141, by rfl⟩ : syracuseStep 4130855 = 6196283) B6196283
theorem B1837167 : Blo 1835619 1837167 := bstep (se 1 (by rfl) ⟨1377875, by rfl⟩ : syracuseStep 1837167 = 2755751) B2755751
theorem B11471069 : Blo 1835619 11471069 := bstep (se 3 (by rfl) ⟨2150825, by rfl⟩ : syracuseStep 11471069 = 4301651) B4301651
theorem B10463519 : Blo 1835619 10463519 := bstep (se 1 (by rfl) ⟨7847639, by rfl⟩ : syracuseStep 10463519 = 15695279) B15695279
theorem B1837467 : Blo 1835619 1837467 := bstep (se 1 (by rfl) ⟨1378100, by rfl⟩ : syracuseStep 1837467 = 2756201) B2756201
theorem B20925215 : Blo 1835619 20925215 := bstep (se 1 (by rfl) ⟨15693911, by rfl⟩ : syracuseStep 20925215 = 31387823) B31387823
theorem B2755391 : Blo 1835619 2755391 := bstep (se 1 (by rfl) ⟨2066543, by rfl⟩ : syracuseStep 2755391 = 4133087) B4133087
theorem B4648043 : Blo 1835619 4648043 := bstep (se 1 (by rfl) ⟨3486032, by rfl⟩ : syracuseStep 4648043 = 6972065) B6972065
theorem B15912065 : Blo 1835619 15912065 := bstep (se 2 (by rfl) ⟨5967024, by rfl⟩ : syracuseStep 15912065 = 11934049) B11934049
theorem B6196391 : Blo 1835619 6196391 := bstep (se 1 (by rfl) ⟨4647293, by rfl⟩ : syracuseStep 6196391 = 9294587) B9294587
theorem B6974707 : Blo 1835619 6974707 := bstep (se 1 (by rfl) ⟨5231030, by rfl⟩ : syracuseStep 6974707 = 10462061) B10462061
theorem B5582077 : Blo 1835619 5582077 := bstep (se 3 (by rfl) ⟨1046639, by rfl⟩ : syracuseStep 5582077 = 2093279) B2093279
theorem B4132115 : Blo 1835619 4132115 := bstep (se 1 (by rfl) ⟨3099086, by rfl⟩ : syracuseStep 4132115 = 6198173) B6198173
theorem B4132457 : Blo 1835619 4132457 := bstep (se 2 (by rfl) ⟨1549671, by rfl⟩ : syracuseStep 4132457 = 3099343) B3099343
theorem B2756207 : Blo 1835619 2756207 := bstep (se 1 (by rfl) ⟨2067155, by rfl⟩ : syracuseStep 2756207 = 4134311) B4134311
theorem B4132511 : Blo 1835619 4132511 := bstep (se 1 (by rfl) ⟨3099383, by rfl⟩ : syracuseStep 4132511 = 6198767) B6198767
theorem B20917925 : Blo 1835619 20917925 := bstep (se 4 (by rfl) ⟨1961055, by rfl⟩ : syracuseStep 20917925 = 3922111) B3922111
theorem B11767463 : Blo 1835619 11767463 := bstep (se 1 (by rfl) ⟨8825597, by rfl⟩ : syracuseStep 11767463 = 17651195) B17651195
theorem B3723007 : Blo 1835619 3723007 := bstep (se 1 (by rfl) ⟨2792255, by rfl⟩ : syracuseStep 3723007 = 5584511) B5584511
theorem B5304089 : Blo 1835619 5304089 := bstep (se 2 (by rfl) ⟨1989033, by rfl⟩ : syracuseStep 5304089 = 3978067) B3978067
theorem B120713225 : Blo 1835619 120713225 := bstep (se 2 (by rfl) ⟨45267459, by rfl⟩ : syracuseStep 120713225 = 90534919) B90534919
theorem B4132961 : Blo 1835619 4132961 := bstep (se 2 (by rfl) ⟨1549860, by rfl⟩ : syracuseStep 4132961 = 3099721) B3099721
theorem B7843949 : Blo 1835619 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B4534427 : Blo 1835619 4534427 := bstep (se 1 (by rfl) ⟨3400820, by rfl⟩ : syracuseStep 4534427 = 6801641) B6801641
theorem B20926673 : Blo 1835619 20926673 := bstep (se 2 (by rfl) ⟨7847502, by rfl⟩ : syracuseStep 20926673 = 15695005) B15695005
theorem B15102175 : Blo 1835619 15102175 := bstep (se 1 (by rfl) ⟨11326631, by rfl⟩ : syracuseStep 15102175 = 22653263) B22653263
theorem B4649339 : Blo 1835619 4649339 := bstep (se 1 (by rfl) ⟨3487004, by rfl⟩ : syracuseStep 4649339 = 6974009) B6974009
theorem B3920737 : Blo 1835619 3920737 := bstep (se 2 (by rfl) ⟨1470276, by rfl⟩ : syracuseStep 3920737 = 2940553) B2940553
theorem B16749449 : Blo 1835619 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B4650281 : Blo 1835619 4650281 := bstep (se 2 (by rfl) ⟨1743855, by rfl⟩ : syracuseStep 4650281 = 3487711) B3487711
theorem B52950347 : Blo 1835619 52950347 := bstep (se 1 (by rfl) ⟨39712760, by rfl⟩ : syracuseStep 52950347 = 79425521) B79425521
theorem B8828327 : Blo 1835619 8828327 := bstep (se 1 (by rfl) ⟨6621245, by rfl⟩ : syracuseStep 8828327 = 13242491) B13242491
theorem B6198875 : Blo 1835619 6198875 := bstep (se 1 (by rfl) ⟨4649156, by rfl⟩ : syracuseStep 6198875 = 9298313) B9298313
theorem B3487369 : Blo 1835619 3487369 := bstep (se 2 (by rfl) ⟨1307763, by rfl⟩ : syracuseStep 3487369 = 2615527) B2615527
theorem B13244107 : Blo 1835619 13244107 := bstep (se 1 (by rfl) ⟨9933080, by rfl⟩ : syracuseStep 13244107 = 19866161) B19866161
theorem B19863305 : Blo 1835619 19863305 := bstep (se 2 (by rfl) ⟨7448739, by rfl⟩ : syracuseStep 19863305 = 14897479) B14897479
theorem B13236203 : Blo 1835619 13236203 := bstep (se 1 (by rfl) ⟨9927152, by rfl⟩ : syracuseStep 13236203 = 19854305) B19854305
theorem B10065971 : Blo 1835619 10065971 := bstep (se 1 (by rfl) ⟨7549478, by rfl⟩ : syracuseStep 10065971 = 15098957) B15098957
theorem B3487931 : Blo 1835619 3487931 := bstep (se 1 (by rfl) ⟨2615948, by rfl⟩ : syracuseStep 3487931 = 5231897) B5231897
theorem B11762131 : Blo 1835619 11762131 := bstep (se 1 (by rfl) ⟨8821598, by rfl⟩ : syracuseStep 11762131 = 17643197) B17643197
theorem B4471271 : Blo 1835619 4471271 := bstep (se 1 (by rfl) ⟨3353453, by rfl⟩ : syracuseStep 4471271 = 6706907) B6706907
theorem B38206079 : Blo 1835619 38206079 := bstep (se 1 (by rfl) ⟨28654559, by rfl⟩ : syracuseStep 38206079 = 57309119) B57309119
theorem B28277437 : Blo 1835619 28277437 := bstep (se 3 (by rfl) ⟨5302019, by rfl⟩ : syracuseStep 28277437 = 10604039) B10604039
theorem B7650035 : Blo 1835619 7650035 := bstep (se 1 (by rfl) ⟨5737526, by rfl⟩ : syracuseStep 7650035 = 11475053) B11475053
theorem B4963135 : Blo 1835619 4963135 := bstep (se 1 (by rfl) ⟨3722351, by rfl⟩ : syracuseStep 4963135 = 7444703) B7444703
theorem B11763053 : Blo 1835619 11763053 := bstep (se 3 (by rfl) ⟨2205572, by rfl⟩ : syracuseStep 11763053 = 4411145) B4411145
theorem B9297341 : Blo 1835619 9297341 := bstep (se 3 (by rfl) ⟨1743251, by rfl⟩ : syracuseStep 9297341 = 3486503) B3486503
theorem B4963859 : Blo 1835619 4963859 := bstep (se 1 (by rfl) ⟨3722894, by rfl⟩ : syracuseStep 4963859 = 7445789) B7445789
theorem B4415105 : Blo 1835619 4415105 := bstep (se 2 (by rfl) ⟨1655664, by rfl⟩ : syracuseStep 4415105 = 3311329) B3311329
theorem B7847675 : Blo 1835619 7847675 := bstep (se 1 (by rfl) ⟨5885756, by rfl⟩ : syracuseStep 7847675 = 11771513) B11771513
theorem B3022951 : Blo 1835619 3022951 := bstep (se 1 (by rfl) ⟨2267213, by rfl⟩ : syracuseStep 3022951 = 4534427) B4534427
theorem B13951115 : Blo 1835619 13951115 := bstep (se 1 (by rfl) ⟨10463336, by rfl⟩ : syracuseStep 13951115 = 20926673) B20926673
theorem B20136233 : Blo 1835619 20136233 := bstep (se 2 (by rfl) ⟨7551087, by rfl⟩ : syracuseStep 20136233 = 15102175) B15102175
theorem B11166299 : Blo 1835619 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B2065279 : Blo 1835619 2065279 := bstep (se 1 (by rfl) ⟨1548959, by rfl⟩ : syracuseStep 2065279 = 3097919) B3097919
theorem B35300231 : Blo 1835619 35300231 := bstep (se 1 (by rfl) ⟨26475173, by rfl⟩ : syracuseStep 35300231 = 52950347) B52950347
theorem B2753513 : Blo 1835619 2753513 := bstep (se 2 (by rfl) ⟨1032567, by rfl⟩ : syracuseStep 2753513 = 2065135) B2065135
theorem B1836015 : Blo 1835619 1836015 := bstep (se 1 (by rfl) ⟨1377011, by rfl⟩ : syracuseStep 1836015 = 2754023) B2754023
theorem B5227649 : Blo 1835619 5227649 := bstep (se 2 (by rfl) ⟨1960368, by rfl⟩ : syracuseStep 5227649 = 3920737) B3920737
theorem B29771077 : Blo 1835619 29771077 := bstep (se 4 (by rfl) ⟨2791038, by rfl⟩ : syracuseStep 29771077 = 5582077) B5582077
theorem B8824135 : Blo 1835619 8824135 := bstep (se 1 (by rfl) ⟨6618101, by rfl⟩ : syracuseStep 8824135 = 13236203) B13236203
theorem B2753903 : Blo 1835619 2753903 := bstep (se 1 (by rfl) ⟨2065427, by rfl⟩ : syracuseStep 2753903 = 4130855) B4130855
theorem B6710647 : Blo 1835619 6710647 := bstep (se 1 (by rfl) ⟨5032985, by rfl⟩ : syracuseStep 6710647 = 10065971) B10065971
theorem B2754089 : Blo 1835619 2754089 := bstep (se 2 (by rfl) ⟨1032783, by rfl⟩ : syracuseStep 2754089 = 2065567) B2065567
theorem B9299609 : Blo 1835619 9299609 := bstep (se 2 (by rfl) ⟨3487353, by rfl⟩ : syracuseStep 9299609 = 6974707) B6974707
theorem B11773613 : Blo 1835619 11773613 := bstep (se 3 (by rfl) ⟨2207552, by rfl⟩ : syracuseStep 11773613 = 4415105) B4415105
theorem B25470719 : Blo 1835619 25470719 := bstep (se 1 (by rfl) ⟨19103039, by rfl⟩ : syracuseStep 25470719 = 38206079) B38206079
theorem B1836927 : Blo 1835619 1836927 := bstep (se 1 (by rfl) ⟨1377695, by rfl⟩ : syracuseStep 1836927 = 2755391) B2755391
theorem B3098695 : Blo 1835619 3098695 := bstep (se 1 (by rfl) ⟨2324021, by rfl⟩ : syracuseStep 3098695 = 4648043) B4648043
theorem B4130927 : Blo 1835619 4130927 := bstep (se 1 (by rfl) ⟨3098195, by rfl⟩ : syracuseStep 4130927 = 6196391) B6196391
theorem B2754743 : Blo 1835619 2754743 := bstep (se 1 (by rfl) ⟨2066057, by rfl⟩ : syracuseStep 2754743 = 4132115) B4132115
theorem B7842035 : Blo 1835619 7842035 := bstep (se 1 (by rfl) ⟨5881526, by rfl⟩ : syracuseStep 7842035 = 11763053) B11763053
theorem B2754971 : Blo 1835619 2754971 := bstep (se 1 (by rfl) ⟨2066228, by rfl⟩ : syracuseStep 2754971 = 4132457) B4132457
theorem B1837471 : Blo 1835619 1837471 := bstep (se 1 (by rfl) ⟨1378103, by rfl⟩ : syracuseStep 1837471 = 2756207) B2756207
theorem B2755007 : Blo 1835619 2755007 := bstep (se 1 (by rfl) ⟨2066255, by rfl⟩ : syracuseStep 2755007 = 4132511) B4132511
theorem B13945283 : Blo 1835619 13945283 := bstep (se 1 (by rfl) ⟨10458962, by rfl⟩ : syracuseStep 13945283 = 20917925) B20917925
theorem B2755307 : Blo 1835619 2755307 := bstep (se 1 (by rfl) ⟨2066480, by rfl⟩ : syracuseStep 2755307 = 4132961) B4132961
theorem B5229299 : Blo 1835619 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B4647719 : Blo 1835619 4647719 := bstep (se 1 (by rfl) ⟨3485789, by rfl⟩ : syracuseStep 4647719 = 6971579) B6971579
theorem B3099559 : Blo 1835619 3099559 := bstep (se 1 (by rfl) ⟨2324669, by rfl⟩ : syracuseStep 3099559 = 4649339) B4649339
theorem B15682841 : Blo 1835619 15682841 := bstep (se 2 (by rfl) ⟨5881065, by rfl⟩ : syracuseStep 15682841 = 11762131) B11762131
theorem B67054985 : Blo 1835619 67054985 := bstep (se 2 (by rfl) ⟨25145619, by rfl⟩ : syracuseStep 67054985 = 50291239) B50291239
theorem B3100187 : Blo 1835619 3100187 := bstep (se 1 (by rfl) ⟨2325140, by rfl⟩ : syracuseStep 3100187 = 4650281) B4650281
theorem B37703249 : Blo 1835619 37703249 := bstep (se 2 (by rfl) ⟨14138718, by rfl⟩ : syracuseStep 37703249 = 28277437) B28277437
theorem B5885551 : Blo 1835619 5885551 := bstep (se 1 (by rfl) ⟨4414163, by rfl⟩ : syracuseStep 5885551 = 8828327) B8828327
theorem B4132583 : Blo 1835619 4132583 := bstep (se 1 (by rfl) ⟨3099437, by rfl⟩ : syracuseStep 4132583 = 6198875) B6198875
theorem B4648691 : Blo 1835619 4648691 := bstep (se 1 (by rfl) ⟨3486518, by rfl⟩ : syracuseStep 4648691 = 6973037) B6973037
theorem B13242203 : Blo 1835619 13242203 := bstep (se 1 (by rfl) ⟨9931652, by rfl⟩ : syracuseStep 13242203 = 19863305) B19863305
theorem B7647379 : Blo 1835619 7647379 := bstep (se 1 (by rfl) ⟨5735534, by rfl⟩ : syracuseStep 7647379 = 11471069) B11471069
theorem B6975679 : Blo 1835619 6975679 := bstep (se 1 (by rfl) ⟨5231759, by rfl⟩ : syracuseStep 6975679 = 10463519) B10463519
theorem B5100023 : Blo 1835619 5100023 := bstep (se 1 (by rfl) ⟨3825017, by rfl⟩ : syracuseStep 5100023 = 7650035) B7650035
theorem B4649825 : Blo 1835619 4649825 := bstep (se 2 (by rfl) ⟨1743684, by rfl⟩ : syracuseStep 4649825 = 3487369) B3487369
theorem B17658809 : Blo 1835619 17658809 := bstep (se 2 (by rfl) ⟨6622053, by rfl⟩ : syracuseStep 17658809 = 13244107) B13244107
theorem B6198227 : Blo 1835619 6198227 := bstep (se 1 (by rfl) ⟨4648670, by rfl⟩ : syracuseStep 6198227 = 9297341) B9297341
theorem B7844975 : Blo 1835619 7844975 := bstep (se 1 (by rfl) ⟨5883731, by rfl⟩ : syracuseStep 7844975 = 11767463) B11767463
theorem B5231783 : Blo 1835619 5231783 := bstep (se 1 (by rfl) ⟨3923837, by rfl⟩ : syracuseStep 5231783 = 7847675) B7847675
theorem B3536059 : Blo 1835619 3536059 := bstep (se 1 (by rfl) ⟨2652044, by rfl⟩ : syracuseStep 3536059 = 5304089) B5304089
theorem B321901933 : Blo 1835619 321901933 := bstep (se 3 (by rfl) ⟨60356612, by rfl⟩ : syracuseStep 321901933 = 120713225) B120713225
theorem B42432173 : Blo 1835619 42432173 := bstep (se 3 (by rfl) ⟨7956032, by rfl⟩ : syracuseStep 42432173 = 15912065) B15912065
theorem B5232671 : Blo 1835619 5232671 := bstep (se 1 (by rfl) ⟨3924503, by rfl⟩ : syracuseStep 5232671 = 7849007) B7849007
theorem B6617513 : Blo 1835619 6617513 := bstep (se 2 (by rfl) ⟨2481567, by rfl⟩ : syracuseStep 6617513 = 4963135) B4963135
theorem B6970121 : Blo 1835619 6970121 := bstep (se 2 (by rfl) ⟨2613795, by rfl⟩ : syracuseStep 6970121 = 5227591) B5227591
theorem B2325287 : Blo 1835619 2325287 := bstep (se 1 (by rfl) ⟨1743965, by rfl⟩ : syracuseStep 2325287 = 3487931) B3487931
theorem B2980847 : Blo 1835619 2980847 := bstep (se 1 (by rfl) ⟨2235635, by rfl⟩ : syracuseStep 2980847 = 4471271) B4471271
theorem B13950143 : Blo 1835619 13950143 := bstep (se 1 (by rfl) ⟨10462607, by rfl⟩ : syracuseStep 13950143 = 20925215) B20925215
theorem B4964009 : Blo 1835619 4964009 := bstep (se 2 (by rfl) ⟨1861503, by rfl⟩ : syracuseStep 4964009 = 3723007) B3723007
theorem B3309239 : Blo 1835619 3309239 := bstep (se 1 (by rfl) ⟨2481929, by rfl⟩ : syracuseStep 3309239 = 4963859) B4963859
theorem B6971305 : Blo 1835619 6971305 := bstep (se 2 (by rfl) ⟨2614239, by rfl⟩ : syracuseStep 6971305 = 5228479) B5228479
theorem B4030601 : Blo 1835619 4030601 := bstep (se 2 (by rfl) ⟨1511475, by rfl⟩ : syracuseStep 4030601 = 3022951) B3022951
theorem B3400015 : Blo 1835619 3400015 := bstep (se 1 (by rfl) ⟨2550011, by rfl⟩ : syracuseStep 3400015 = 5100023) B5100023
theorem B11772539 : Blo 1835619 11772539 := bstep (se 1 (by rfl) ⟨8829404, by rfl⟩ : syracuseStep 11772539 = 17658809) B17658809
theorem B1835675 : Blo 1835619 1835675 := bstep (se 1 (by rfl) ⟨1376756, by rfl⟩ : syracuseStep 1835675 = 2753513) B2753513
theorem B1835935 : Blo 1835619 1835935 := bstep (se 1 (by rfl) ⟨1376951, by rfl⟩ : syracuseStep 1835935 = 2753903) B2753903
theorem B1836059 : Blo 1835619 1836059 := bstep (se 1 (by rfl) ⟨1377044, by rfl⟩ : syracuseStep 1836059 = 2754089) B2754089
theorem B28288115 : Blo 1835619 28288115 := bstep (se 1 (by rfl) ⟨21216086, by rfl⟩ : syracuseStep 28288115 = 42432173) B42432173
theorem B7849075 : Blo 1835619 7849075 := bstep (se 1 (by rfl) ⟨5886806, by rfl⟩ : syracuseStep 7849075 = 11773613) B11773613
theorem B2753705 : Blo 1835619 2753705 := bstep (se 2 (by rfl) ⟨1032639, by rfl⟩ : syracuseStep 2753705 = 2065279) B2065279
theorem B2753951 : Blo 1835619 2753951 := bstep (se 1 (by rfl) ⟨2065463, by rfl⟩ : syracuseStep 2753951 = 4130927) B4130927
theorem B1836495 : Blo 1835619 1836495 := bstep (se 1 (by rfl) ⟨1377371, by rfl⟩ : syracuseStep 1836495 = 2754743) B2754743
theorem B1836647 : Blo 1835619 1836647 := bstep (se 1 (by rfl) ⟨1377485, by rfl⟩ : syracuseStep 1836647 = 2754971) B2754971
theorem B1836671 : Blo 1835619 1836671 := bstep (se 1 (by rfl) ⟨1377503, by rfl⟩ : syracuseStep 1836671 = 2755007) B2755007
theorem B11765513 : Blo 1835619 11765513 := bstep (se 2 (by rfl) ⟨4412067, by rfl⟩ : syracuseStep 11765513 = 8824135) B8824135
theorem B1836871 : Blo 1835619 1836871 := bstep (se 1 (by rfl) ⟨1377653, by rfl⟩ : syracuseStep 1836871 = 2755307) B2755307
theorem B8947529 : Blo 1835619 8947529 := bstep (se 2 (by rfl) ⟨3355323, by rfl⟩ : syracuseStep 8947529 = 6710647) B6710647
theorem B4646747 : Blo 1835619 4646747 := bstep (se 1 (by rfl) ⟨3485060, by rfl⟩ : syracuseStep 4646747 = 6970121) B6970121
theorem B3098479 : Blo 1835619 3098479 := bstep (se 1 (by rfl) ⟨2323859, by rfl⟩ : syracuseStep 3098479 = 4647719) B4647719
theorem B13944797 : Blo 1835619 13944797 := bstep (se 3 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 13944797 = 5229299) B5229299
theorem B9300095 : Blo 1835619 9300095 := bstep (se 1 (by rfl) ⟨6975071, by rfl⟩ : syracuseStep 9300095 = 13950143) B13950143
theorem B10455227 : Blo 1835619 10455227 := bstep (se 1 (by rfl) ⟨7841420, by rfl⟩ : syracuseStep 10455227 = 15682841) B15682841
theorem B2066791 : Blo 1835619 2066791 := bstep (se 1 (by rfl) ⟨1550093, by rfl⟩ : syracuseStep 2066791 = 3100187) B3100187
theorem B25135499 : Blo 1835619 25135499 := bstep (se 1 (by rfl) ⟨18851624, by rfl⟩ : syracuseStep 25135499 = 37703249) B37703249
theorem B2206159 : Blo 1835619 2206159 := bstep (se 1 (by rfl) ⟨1654619, by rfl⟩ : syracuseStep 2206159 = 3309239) B3309239
theorem B2755055 : Blo 1835619 2755055 := bstep (se 1 (by rfl) ⟨2066291, by rfl⟩ : syracuseStep 2755055 = 4132583) B4132583
theorem B3099127 : Blo 1835619 3099127 := bstep (se 1 (by rfl) ⟨2324345, by rfl⟩ : syracuseStep 3099127 = 4648691) B4648691
theorem B9300743 : Blo 1835619 9300743 := bstep (se 1 (by rfl) ⟨6975557, by rfl⟩ : syracuseStep 9300743 = 13951115) B13951115
theorem B4131593 : Blo 1835619 4131593 := bstep (se 2 (by rfl) ⟨1549347, by rfl⟩ : syracuseStep 4131593 = 3098695) B3098695
theorem B9300905 : Blo 1835619 9300905 := bstep (se 2 (by rfl) ⟨3487839, by rfl⟩ : syracuseStep 9300905 = 6975679) B6975679
theorem B3099883 : Blo 1835619 3099883 := bstep (se 1 (by rfl) ⟨2324912, by rfl⟩ : syracuseStep 3099883 = 4649825) B4649825
theorem B4132151 : Blo 1835619 4132151 := bstep (se 1 (by rfl) ⟨3099113, by rfl⟩ : syracuseStep 4132151 = 6198227) B6198227
theorem B5229983 : Blo 1835619 5229983 := bstep (se 1 (by rfl) ⟨3922487, by rfl⟩ : syracuseStep 5229983 = 7844975) B7844975
theorem B3485099 : Blo 1835619 3485099 := bstep (se 1 (by rfl) ⟨2613824, by rfl⟩ : syracuseStep 3485099 = 5227649) B5227649
theorem B4132745 : Blo 1835619 4132745 := bstep (se 2 (by rfl) ⟨1549779, by rfl⟩ : syracuseStep 4132745 = 3099559) B3099559
theorem B4714745 : Blo 1835619 4714745 := bstep (se 2 (by rfl) ⟨1768029, by rfl⟩ : syracuseStep 4714745 = 3536059) B3536059
theorem B4411675 : Blo 1835619 4411675 := bstep (se 1 (by rfl) ⟨3308756, by rfl⟩ : syracuseStep 4411675 = 6617513) B6617513
theorem B39694769 : Blo 1835619 39694769 := bstep (se 2 (by rfl) ⟨14885538, by rfl⟩ : syracuseStep 39694769 = 29771077) B29771077
theorem B1987231 : Blo 1835619 1987231 := bstep (se 1 (by rfl) ⟨1490423, by rfl⟩ : syracuseStep 1987231 = 2980847) B2980847
theorem B9295073 : Blo 1835619 9295073 := bstep (se 2 (by rfl) ⟨3485652, by rfl⟩ : syracuseStep 9295073 = 6971305) B6971305
theorem B8828135 : Blo 1835619 8828135 := bstep (se 1 (by rfl) ⟨6621101, by rfl⟩ : syracuseStep 8828135 = 13242203) B13242203
theorem B7444199 : Blo 1835619 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B23533487 : Blo 1835619 23533487 := bstep (se 1 (by rfl) ⟨17650115, by rfl⟩ : syracuseStep 23533487 = 35300231) B35300231
theorem B20912093 : Blo 1835619 20912093 := bstep (se 3 (by rfl) ⟨3921017, by rfl⟩ : syracuseStep 20912093 = 7842035) B7842035
theorem B40786021 : Blo 1835619 40786021 := bstep (se 4 (by rfl) ⟨3823689, by rfl⟩ : syracuseStep 40786021 = 7647379) B7647379
theorem B53696621 : Blo 1835619 53696621 := bstep (se 3 (by rfl) ⟨10068116, by rfl⟩ : syracuseStep 53696621 = 20136233) B20136233
theorem B3487855 : Blo 1835619 3487855 := bstep (se 1 (by rfl) ⟨2615891, by rfl⟩ : syracuseStep 3487855 = 5231783) B5231783
theorem B6199739 : Blo 1835619 6199739 := bstep (se 1 (by rfl) ⟨4649804, by rfl⟩ : syracuseStep 6199739 = 9299609) B9299609
theorem B16980479 : Blo 1835619 16980479 := bstep (se 1 (by rfl) ⟨12735359, by rfl⟩ : syracuseStep 16980479 = 25470719) B25470719
theorem B3488447 : Blo 1835619 3488447 := bstep (se 1 (by rfl) ⟨2616335, by rfl⟩ : syracuseStep 3488447 = 5232671) B5232671
theorem B9296855 : Blo 1835619 9296855 := bstep (se 1 (by rfl) ⟨6972641, by rfl⟩ : syracuseStep 9296855 = 13945283) B13945283
theorem B13237357 : Blo 1835619 13237357 := bstep (se 3 (by rfl) ⟨2482004, by rfl⟩ : syracuseStep 13237357 = 4964009) B4964009
theorem B429202577 : Blo 1835619 429202577 := bstep (se 2 (by rfl) ⟨160950966, by rfl⟩ : syracuseStep 429202577 = 321901933) B321901933
theorem B6200765 : Blo 1835619 6200765 := bstep (se 3 (by rfl) ⟨1162643, by rfl⟩ : syracuseStep 6200765 = 2325287) B2325287
theorem B7847401 : Blo 1835619 7847401 := bstep (se 2 (by rfl) ⟨2942775, by rfl⟩ : syracuseStep 7847401 = 5885551) B5885551
theorem B44703323 : Blo 1835619 44703323 := bstep (se 1 (by rfl) ⟨33527492, by rfl⟩ : syracuseStep 44703323 = 67054985) B67054985
theorem B5882233 : Blo 1835619 5882233 := bstep (se 2 (by rfl) ⟨2205837, by rfl⟩ : syracuseStep 5882233 = 4411675) B4411675
theorem B7848359 : Blo 1835619 7848359 := bstep (se 1 (by rfl) ⟨5886269, by rfl⟩ : syracuseStep 7848359 = 11772539) B11772539
theorem B42394261 : Blo 1835619 42394261 := bstep (se 6 (by rfl) ⟨993615, by rfl⟩ : syracuseStep 42394261 = 1987231) B1987231
theorem B18858743 : Blo 1835619 18858743 := bstep (se 1 (by rfl) ⟨14144057, by rfl⟩ : syracuseStep 18858743 = 28288115) B28288115
theorem B1835803 : Blo 1835619 1835803 := bstep (se 1 (by rfl) ⟨1376852, by rfl⟩ : syracuseStep 1835803 = 2753705) B2753705
theorem B1835967 : Blo 1835619 1835967 := bstep (se 1 (by rfl) ⟨1376975, by rfl⟩ : syracuseStep 1835967 = 2753951) B2753951
theorem B5965019 : Blo 1835619 5965019 := bstep (se 1 (by rfl) ⟨4473764, by rfl⟩ : syracuseStep 5965019 = 8947529) B8947529
theorem B3097831 : Blo 1835619 3097831 := bstep (se 1 (by rfl) ⟨2323373, by rfl⟩ : syracuseStep 3097831 = 4646747) B4646747
theorem B15688991 : Blo 1835619 15688991 := bstep (se 1 (by rfl) ⟨11766743, by rfl⟩ : syracuseStep 15688991 = 23533487) B23533487
theorem B42993077 : Blo 1835619 42993077 := bstep (se 5 (by rfl) ⟨2015300, by rfl⟩ : syracuseStep 42993077 = 4030601) B4030601
theorem B1836703 : Blo 1835619 1836703 := bstep (se 1 (by rfl) ⟨1377527, by rfl⟩ : syracuseStep 1836703 = 2755055) B2755055
theorem B2754395 : Blo 1835619 2754395 := bstep (se 1 (by rfl) ⟨2065796, by rfl⟩ : syracuseStep 2754395 = 4131593) B4131593
theorem B10463201 : Blo 1835619 10463201 := bstep (se 2 (by rfl) ⟨3923700, by rfl⟩ : syracuseStep 10463201 = 7847401) B7847401
theorem B2754767 : Blo 1835619 2754767 := bstep (se 1 (by rfl) ⟨2066075, by rfl⟩ : syracuseStep 2754767 = 4132151) B4132151
theorem B11766181 : Blo 1835619 11766181 := bstep (se 4 (by rfl) ⟨1103079, by rfl⟩ : syracuseStep 11766181 = 2206159) B2206159
theorem B4131305 : Blo 1835619 4131305 := bstep (se 2 (by rfl) ⟨1549239, by rfl⟩ : syracuseStep 4131305 = 3098479) B3098479
theorem B2755163 : Blo 1835619 2755163 := bstep (se 1 (by rfl) ⟨2066372, by rfl⟩ : syracuseStep 2755163 = 4132745) B4132745
theorem B26463179 : Blo 1835619 26463179 := bstep (se 1 (by rfl) ⟨19847384, by rfl⟩ : syracuseStep 26463179 = 39694769) B39694769
theorem B1144540205 : Blo 1835619 1144540205 := bstep (se 3 (by rfl) ⟨214601288, by rfl⟩ : syracuseStep 1144540205 = 429202577) B429202577
theorem B4533353 : Blo 1835619 4533353 := bstep (se 2 (by rfl) ⟨1700007, by rfl⟩ : syracuseStep 4533353 = 3400015) B3400015
theorem B2755721 : Blo 1835619 2755721 := bstep (se 2 (by rfl) ⟨1033395, by rfl⟩ : syracuseStep 2755721 = 2066791) B2066791
theorem B217525445 : Blo 1835619 217525445 := bstep (se 4 (by rfl) ⟨20393010, by rfl⟩ : syracuseStep 217525445 = 40786021) B40786021
theorem B4132169 : Blo 1835619 4132169 := bstep (se 2 (by rfl) ⟨1549563, by rfl⟩ : syracuseStep 4132169 = 3099127) B3099127
theorem B6196715 : Blo 1835619 6196715 := bstep (se 1 (by rfl) ⟨4647536, by rfl⟩ : syracuseStep 6196715 = 9295073) B9295073
theorem B5885423 : Blo 1835619 5885423 := bstep (se 1 (by rfl) ⟨4414067, by rfl⟩ : syracuseStep 5885423 = 8828135) B8828135
theorem B17649809 : Blo 1835619 17649809 := bstep (se 2 (by rfl) ⟨6618678, by rfl⟩ : syracuseStep 17649809 = 13237357) B13237357
theorem B10465433 : Blo 1835619 10465433 := bstep (se 2 (by rfl) ⟨3924537, by rfl⟩ : syracuseStep 10465433 = 7849075) B7849075
theorem B16756999 : Blo 1835619 16756999 := bstep (se 1 (by rfl) ⟨12567749, by rfl⟩ : syracuseStep 16756999 = 25135499) B25135499
theorem B4133159 : Blo 1835619 4133159 := bstep (se 1 (by rfl) ⟨3099869, by rfl⟩ : syracuseStep 4133159 = 6199739) B6199739
theorem B4133177 : Blo 1835619 4133177 := bstep (se 2 (by rfl) ⟨1549941, by rfl⟩ : syracuseStep 4133177 = 3099883) B3099883
theorem B9302525 : Blo 1835619 9302525 := bstep (se 3 (by rfl) ⟨1744223, by rfl⟩ : syracuseStep 9302525 = 3488447) B3488447
theorem B6197903 : Blo 1835619 6197903 := bstep (se 1 (by rfl) ⟨4648427, by rfl⟩ : syracuseStep 6197903 = 9296855) B9296855
theorem B3486655 : Blo 1835619 3486655 := bstep (se 1 (by rfl) ⟨2614991, by rfl⟩ : syracuseStep 3486655 = 5229983) B5229983
theorem B2323399 : Blo 1835619 2323399 := bstep (se 1 (by rfl) ⟨1742549, by rfl⟩ : syracuseStep 2323399 = 3485099) B3485099
theorem B4133843 : Blo 1835619 4133843 := bstep (se 1 (by rfl) ⟨3100382, by rfl⟩ : syracuseStep 4133843 = 6200765) B6200765
theorem B4650473 : Blo 1835619 4650473 := bstep (se 2 (by rfl) ⟨1743927, by rfl⟩ : syracuseStep 4650473 = 3487855) B3487855
theorem B12572653 : Blo 1835619 12572653 := bstep (se 3 (by rfl) ⟨2357372, by rfl⟩ : syracuseStep 12572653 = 4714745) B4714745
theorem B4962799 : Blo 1835619 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B13941395 : Blo 1835619 13941395 := bstep (se 1 (by rfl) ⟨10456046, by rfl⟩ : syracuseStep 13941395 = 20912093) B20912093
theorem B9296531 : Blo 1835619 9296531 := bstep (se 1 (by rfl) ⟨6972398, by rfl⟩ : syracuseStep 9296531 = 13944797) B13944797
theorem B35797747 : Blo 1835619 35797747 := bstep (se 1 (by rfl) ⟨26848310, by rfl⟩ : syracuseStep 35797747 = 53696621) B53696621
theorem B6200063 : Blo 1835619 6200063 := bstep (se 1 (by rfl) ⟨4650047, by rfl⟩ : syracuseStep 6200063 = 9300095) B9300095
theorem B6970151 : Blo 1835619 6970151 := bstep (se 1 (by rfl) ⟨5227613, by rfl⟩ : syracuseStep 6970151 = 10455227) B10455227
theorem B11320319 : Blo 1835619 11320319 := bstep (se 1 (by rfl) ⟨8490239, by rfl⟩ : syracuseStep 11320319 = 16980479) B16980479
theorem B6200495 : Blo 1835619 6200495 := bstep (se 1 (by rfl) ⟨4650371, by rfl⟩ : syracuseStep 6200495 = 9300743) B9300743
theorem B6200603 : Blo 1835619 6200603 := bstep (se 1 (by rfl) ⟨4650452, by rfl⟩ : syracuseStep 6200603 = 9300905) B9300905
theorem B31374701 : Blo 1835619 31374701 := bstep (se 3 (by rfl) ⟨5882756, by rfl⟩ : syracuseStep 31374701 = 11765513) B11765513
theorem B29802215 : Blo 1835619 29802215 := bstep (se 1 (by rfl) ⟨22351661, by rfl⟩ : syracuseStep 29802215 = 44703323) B44703323
theorem B6201683 : Blo 1835619 6201683 := bstep (se 1 (by rfl) ⟨4651262, by rfl⟩ : syracuseStep 6201683 = 9302525) B9302525
theorem B15688241 : Blo 1835619 15688241 := bstep (se 2 (by rfl) ⟨5883090, by rfl⟩ : syracuseStep 15688241 = 11766181) B11766181
theorem B56525681 : Blo 1835619 56525681 := bstep (se 2 (by rfl) ⟨21197130, by rfl⟩ : syracuseStep 56525681 = 42394261) B42394261
theorem B114648205 : Blo 1835619 114648205 := bstep (se 3 (by rfl) ⟨21496538, by rfl⟩ : syracuseStep 114648205 = 42993077) B42993077
theorem B1836263 : Blo 1835619 1836263 := bstep (se 1 (by rfl) ⟨1377197, by rfl⟩ : syracuseStep 1836263 = 2754395) B2754395
theorem B3097865 : Blo 1835619 3097865 := bstep (se 2 (by rfl) ⟨1161699, by rfl⟩ : syracuseStep 3097865 = 2323399) B2323399
theorem B1836511 : Blo 1835619 1836511 := bstep (se 1 (by rfl) ⟨1377383, by rfl⟩ : syracuseStep 1836511 = 2754767) B2754767
theorem B4130441 : Blo 1835619 4130441 := bstep (se 2 (by rfl) ⟨1548915, by rfl⟩ : syracuseStep 4130441 = 3097831) B3097831
theorem B2754203 : Blo 1835619 2754203 := bstep (se 1 (by rfl) ⟨2065652, by rfl⟩ : syracuseStep 2754203 = 4131305) B4131305
theorem B1836775 : Blo 1835619 1836775 := bstep (se 1 (by rfl) ⟨1377581, by rfl⟩ : syracuseStep 1836775 = 2755163) B2755163
theorem B4646767 : Blo 1835619 4646767 := bstep (se 1 (by rfl) ⟨3485075, by rfl⟩ : syracuseStep 4646767 = 6970151) B6970151
theorem B79472573 : Blo 1835619 79472573 := bstep (se 3 (by rfl) ⟨14901107, by rfl⟩ : syracuseStep 79472573 = 29802215) B29802215
theorem B7546879 : Blo 1835619 7546879 := bstep (se 1 (by rfl) ⟨5660159, by rfl⟩ : syracuseStep 7546879 = 11320319) B11320319
theorem B1837147 : Blo 1835619 1837147 := bstep (se 1 (by rfl) ⟨1377860, by rfl⟩ : syracuseStep 1837147 = 2755721) B2755721
theorem B145016963 : Blo 1835619 145016963 := bstep (se 1 (by rfl) ⟨108762722, by rfl⟩ : syracuseStep 145016963 = 217525445) B217525445
theorem B2754779 : Blo 1835619 2754779 := bstep (se 1 (by rfl) ⟨2066084, by rfl⟩ : syracuseStep 2754779 = 4132169) B4132169
theorem B20916467 : Blo 1835619 20916467 := bstep (se 1 (by rfl) ⟨15687350, by rfl⟩ : syracuseStep 20916467 = 31374701) B31374701
theorem B4131143 : Blo 1835619 4131143 := bstep (se 1 (by rfl) ⟨3098357, by rfl⟩ : syracuseStep 4131143 = 6196715) B6196715
theorem B16763537 : Blo 1835619 16763537 := bstep (se 2 (by rfl) ⟨6286326, by rfl⟩ : syracuseStep 16763537 = 12572653) B12572653
theorem B11766539 : Blo 1835619 11766539 := bstep (se 1 (by rfl) ⟨8824904, by rfl⟩ : syracuseStep 11766539 = 17649809) B17649809
theorem B2755439 : Blo 1835619 2755439 := bstep (se 1 (by rfl) ⟨2066579, by rfl⟩ : syracuseStep 2755439 = 4133159) B4133159
theorem B2755451 : Blo 1835619 2755451 := bstep (se 1 (by rfl) ⟨2066588, by rfl⟩ : syracuseStep 2755451 = 4133177) B4133177
theorem B4131935 : Blo 1835619 4131935 := bstep (se 1 (by rfl) ⟨3098951, by rfl⟩ : syracuseStep 4131935 = 6197903) B6197903
theorem B7842977 : Blo 1835619 7842977 := bstep (se 2 (by rfl) ⟨2941116, by rfl⟩ : syracuseStep 7842977 = 5882233) B5882233
theorem B2755895 : Blo 1835619 2755895 := bstep (se 1 (by rfl) ⟨2066921, by rfl⟩ : syracuseStep 2755895 = 4133843) B4133843
theorem B3976679 : Blo 1835619 3976679 := bstep (se 1 (by rfl) ⟨2982509, by rfl⟩ : syracuseStep 3976679 = 5965019) B5965019
theorem B47730329 : Blo 1835619 47730329 := bstep (se 2 (by rfl) ⟨17898873, by rfl⟩ : syracuseStep 47730329 = 35797747) B35797747
theorem B3100315 : Blo 1835619 3100315 := bstep (se 1 (by rfl) ⟨2325236, by rfl⟩ : syracuseStep 3100315 = 4650473) B4650473
theorem B4648873 : Blo 1835619 4648873 := bstep (se 2 (by rfl) ⟨1743327, by rfl⟩ : syracuseStep 4648873 = 3486655) B3486655
theorem B6975467 : Blo 1835619 6975467 := bstep (se 1 (by rfl) ⟨5231600, by rfl⟩ : syracuseStep 6975467 = 10463201) B10463201
theorem B89370661 : Blo 1835619 89370661 := bstep (se 4 (by rfl) ⟨8378499, by rfl⟩ : syracuseStep 89370661 = 16756999) B16756999
theorem B9294263 : Blo 1835619 9294263 := bstep (se 1 (by rfl) ⟨6970697, by rfl⟩ : syracuseStep 9294263 = 13941395) B13941395
theorem B6197687 : Blo 1835619 6197687 := bstep (se 1 (by rfl) ⟨4648265, by rfl⟩ : syracuseStep 6197687 = 9296531) B9296531
theorem B4133375 : Blo 1835619 4133375 := bstep (se 1 (by rfl) ⟨3100031, by rfl⟩ : syracuseStep 4133375 = 6200063) B6200063
theorem B17642119 : Blo 1835619 17642119 := bstep (se 1 (by rfl) ⟨13231589, by rfl⟩ : syracuseStep 17642119 = 26463179) B26463179
theorem B4133663 : Blo 1835619 4133663 := bstep (se 1 (by rfl) ⟨3100247, by rfl⟩ : syracuseStep 4133663 = 6200495) B6200495
theorem B4133735 : Blo 1835619 4133735 := bstep (se 1 (by rfl) ⟨3100301, by rfl⟩ : syracuseStep 4133735 = 6200603) B6200603
theorem B6976955 : Blo 1835619 6976955 := bstep (se 1 (by rfl) ⟨5232716, by rfl⟩ : syracuseStep 6976955 = 10465433) B10465433
theorem B5232239 : Blo 1835619 5232239 := bstep (se 1 (by rfl) ⟨3924179, by rfl⟩ : syracuseStep 5232239 = 7848359) B7848359
theorem B12572495 : Blo 1835619 12572495 := bstep (se 1 (by rfl) ⟨9429371, by rfl⟩ : syracuseStep 12572495 = 18858743) B18858743
theorem B6617065 : Blo 1835619 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B10459327 : Blo 1835619 10459327 := bstep (se 1 (by rfl) ⟨7844495, by rfl⟩ : syracuseStep 10459327 = 15688991) B15688991
theorem B763026803 : Blo 1835619 763026803 := bstep (se 1 (by rfl) ⟨572270102, by rfl⟩ : syracuseStep 763026803 = 1144540205) B1144540205
theorem B3022235 : Blo 1835619 3022235 := bstep (se 1 (by rfl) ⟨2266676, by rfl⟩ : syracuseStep 3022235 = 4533353) B4533353
theorem B3923615 : Blo 1835619 3923615 := bstep (se 1 (by rfl) ⟨2942711, by rfl⟩ : syracuseStep 3923615 = 5885423) B5885423
theorem B119160881 : Blo 1835619 119160881 := bstep (se 2 (by rfl) ⟨44685330, by rfl⟩ : syracuseStep 119160881 = 89370661) B89370661
theorem B37683787 : Blo 1835619 37683787 := bstep (se 1 (by rfl) ⟨28262840, by rfl⟩ : syracuseStep 37683787 = 56525681) B56525681
theorem B2065243 : Blo 1835619 2065243 := bstep (se 1 (by rfl) ⟨1548932, by rfl⟩ : syracuseStep 2065243 = 3097865) B3097865
theorem B2753627 : Blo 1835619 2753627 := bstep (se 1 (by rfl) ⟨2065220, by rfl⟩ : syracuseStep 2753627 = 4130441) B4130441
theorem B1836135 : Blo 1835619 1836135 := bstep (se 1 (by rfl) ⟨1377101, by rfl⟩ : syracuseStep 1836135 = 2754203) B2754203
theorem B8381663 : Blo 1835619 8381663 := bstep (se 1 (by rfl) ⟨6286247, by rfl⟩ : syracuseStep 8381663 = 12572495) B12572495
theorem B1836519 : Blo 1835619 1836519 := bstep (se 1 (by rfl) ⟨1377389, by rfl⟩ : syracuseStep 1836519 = 2754779) B2754779
theorem B13944311 : Blo 1835619 13944311 := bstep (se 1 (by rfl) ⟨10458233, by rfl⟩ : syracuseStep 13944311 = 20916467) B20916467
theorem B152864273 : Blo 1835619 152864273 := bstep (se 2 (by rfl) ⟨57324102, by rfl⟩ : syracuseStep 152864273 = 114648205) B114648205
theorem B2754095 : Blo 1835619 2754095 := bstep (se 1 (by rfl) ⟨2065571, by rfl⟩ : syracuseStep 2754095 = 4131143) B4131143
theorem B11175691 : Blo 1835619 11175691 := bstep (se 1 (by rfl) ⟨8381768, by rfl⟩ : syracuseStep 11175691 = 16763537) B16763537
theorem B1836959 : Blo 1835619 1836959 := bstep (se 1 (by rfl) ⟨1377719, by rfl⟩ : syracuseStep 1836959 = 2755439) B2755439
theorem B1836967 : Blo 1835619 1836967 := bstep (se 1 (by rfl) ⟨1377725, by rfl⟩ : syracuseStep 1836967 = 2755451) B2755451
theorem B2754623 : Blo 1835619 2754623 := bstep (se 1 (by rfl) ⟨2065967, by rfl⟩ : syracuseStep 2754623 = 4131935) B4131935
theorem B5228651 : Blo 1835619 5228651 := bstep (se 1 (by rfl) ⟨3921488, by rfl⟩ : syracuseStep 5228651 = 7842977) B7842977
theorem B1837263 : Blo 1835619 1837263 := bstep (se 1 (by rfl) ⟨1377947, by rfl⟩ : syracuseStep 1837263 = 2755895) B2755895
theorem B508684535 : Blo 1835619 508684535 := bstep (se 1 (by rfl) ⟨381513401, by rfl⟩ : syracuseStep 508684535 = 763026803) B763026803
theorem B31820219 : Blo 1835619 31820219 := bstep (se 1 (by rfl) ⟨23865164, by rfl⟩ : syracuseStep 31820219 = 47730329) B47730329
theorem B2615743 : Blo 1835619 2615743 := bstep (se 1 (by rfl) ⟨1961807, by rfl⟩ : syracuseStep 2615743 = 3923615) B3923615
theorem B6195689 : Blo 1835619 6195689 := bstep (se 2 (by rfl) ⟨2323383, by rfl⟩ : syracuseStep 6195689 = 4646767) B4646767
theorem B10062505 : Blo 1835619 10062505 := bstep (se 2 (by rfl) ⟨3773439, by rfl⟩ : syracuseStep 10062505 = 7546879) B7546879
theorem B13945769 : Blo 1835619 13945769 := bstep (se 2 (by rfl) ⟨5229663, by rfl⟩ : syracuseStep 13945769 = 10459327) B10459327
theorem B6196175 : Blo 1835619 6196175 := bstep (se 1 (by rfl) ⟨4647131, by rfl⟩ : syracuseStep 6196175 = 9294263) B9294263
theorem B4131791 : Blo 1835619 4131791 := bstep (se 1 (by rfl) ⟨3098843, by rfl⟩ : syracuseStep 4131791 = 6197687) B6197687
theorem B2755583 : Blo 1835619 2755583 := bstep (se 1 (by rfl) ⟨2066687, by rfl⟩ : syracuseStep 2755583 = 4133375) B4133375
theorem B2755775 : Blo 1835619 2755775 := bstep (se 1 (by rfl) ⟨2066831, by rfl⟩ : syracuseStep 2755775 = 4133663) B4133663
theorem B2755823 : Blo 1835619 2755823 := bstep (se 1 (by rfl) ⟨2066867, by rfl⟩ : syracuseStep 2755823 = 4133735) B4133735
theorem B23522825 : Blo 1835619 23522825 := bstep (se 2 (by rfl) ⟨8821059, by rfl⟩ : syracuseStep 23522825 = 17642119) B17642119
theorem B10604477 : Blo 1835619 10604477 := bstep (se 3 (by rfl) ⟨1988339, by rfl⟩ : syracuseStep 10604477 = 3976679) B3976679
theorem B52981715 : Blo 1835619 52981715 := bstep (se 1 (by rfl) ⟨39736286, by rfl⟩ : syracuseStep 52981715 = 79472573) B79472573
theorem B96677975 : Blo 1835619 96677975 := bstep (se 1 (by rfl) ⟨72508481, by rfl⟩ : syracuseStep 96677975 = 145016963) B145016963
theorem B7844359 : Blo 1835619 7844359 := bstep (se 1 (by rfl) ⟨5883269, by rfl⟩ : syracuseStep 7844359 = 11766539) B11766539
theorem B4133753 : Blo 1835619 4133753 := bstep (se 2 (by rfl) ⟨1550157, by rfl⟩ : syracuseStep 4133753 = 3100315) B3100315
theorem B6198497 : Blo 1835619 6198497 := bstep (se 2 (by rfl) ⟨2324436, by rfl⟩ : syracuseStep 6198497 = 4648873) B4648873
theorem B4650311 : Blo 1835619 4650311 := bstep (se 1 (by rfl) ⟨3487733, by rfl⟩ : syracuseStep 4650311 = 6975467) B6975467
theorem B4134455 : Blo 1835619 4134455 := bstep (se 1 (by rfl) ⟨3100841, by rfl⟩ : syracuseStep 4134455 = 6201683) B6201683
theorem B10458827 : Blo 1835619 10458827 := bstep (se 1 (by rfl) ⟨7844120, by rfl⟩ : syracuseStep 10458827 = 15688241) B15688241
theorem B4651303 : Blo 1835619 4651303 := bstep (se 1 (by rfl) ⟨3488477, by rfl⟩ : syracuseStep 4651303 = 6976955) B6976955
theorem B3488159 : Blo 1835619 3488159 := bstep (se 1 (by rfl) ⟨2616119, by rfl⟩ : syracuseStep 3488159 = 5232239) B5232239
theorem B2014823 : Blo 1835619 2014823 := bstep (se 1 (by rfl) ⟨1511117, by rfl⟩ : syracuseStep 2014823 = 3022235) B3022235
theorem B8822753 : Blo 1835619 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B6201737 : Blo 1835619 6201737 := bstep (se 2 (by rfl) ⟨2325651, by rfl⟩ : syracuseStep 6201737 = 4651303) B4651303
theorem B1835751 : Blo 1835619 1835751 := bstep (se 1 (by rfl) ⟨1376813, by rfl⟩ : syracuseStep 1835751 = 2753627) B2753627
theorem B5587775 : Blo 1835619 5587775 := bstep (se 1 (by rfl) ⟨4190831, by rfl⟩ : syracuseStep 5587775 = 8381663) B8381663
theorem B101909515 : Blo 1835619 101909515 := bstep (se 1 (by rfl) ⟨76432136, by rfl⟩ : syracuseStep 101909515 = 152864273) B152864273
theorem B1836063 : Blo 1835619 1836063 := bstep (se 1 (by rfl) ⟨1377047, by rfl⟩ : syracuseStep 1836063 = 2754095) B2754095
theorem B2753657 : Blo 1835619 2753657 := bstep (se 2 (by rfl) ⟨1032621, by rfl⟩ : syracuseStep 2753657 = 2065243) B2065243
theorem B6972551 : Blo 1835619 6972551 := bstep (se 1 (by rfl) ⟨5229413, by rfl⟩ : syracuseStep 6972551 = 10458827) B10458827
theorem B1836415 : Blo 1835619 1836415 := bstep (se 1 (by rfl) ⟨1377311, by rfl⟩ : syracuseStep 1836415 = 2754623) B2754623
theorem B4130459 : Blo 1835619 4130459 := bstep (se 1 (by rfl) ⟨3097844, by rfl⟩ : syracuseStep 4130459 = 6195689) B6195689
theorem B4130783 : Blo 1835619 4130783 := bstep (se 1 (by rfl) ⟨3098087, by rfl⟩ : syracuseStep 4130783 = 6196175) B6196175
theorem B2754527 : Blo 1835619 2754527 := bstep (se 1 (by rfl) ⟨2065895, by rfl⟩ : syracuseStep 2754527 = 4131791) B4131791
theorem B1837055 : Blo 1835619 1837055 := bstep (se 1 (by rfl) ⟨1377791, by rfl⟩ : syracuseStep 1837055 = 2755583) B2755583
theorem B1837183 : Blo 1835619 1837183 := bstep (se 1 (by rfl) ⟨1377887, by rfl⟩ : syracuseStep 1837183 = 2755775) B2755775
theorem B1837215 : Blo 1835619 1837215 := bstep (se 1 (by rfl) ⟨1377911, by rfl⟩ : syracuseStep 1837215 = 2755823) B2755823
theorem B15681883 : Blo 1835619 15681883 := bstep (se 1 (by rfl) ⟨11761412, by rfl⟩ : syracuseStep 15681883 = 23522825) B23522825
theorem B79440587 : Blo 1835619 79440587 := bstep (se 1 (by rfl) ⟨59580440, by rfl⟩ : syracuseStep 79440587 = 119160881) B119160881
theorem B2755835 : Blo 1835619 2755835 := bstep (se 1 (by rfl) ⟨2066876, by rfl⟩ : syracuseStep 2755835 = 4133753) B4133753
theorem B50245049 : Blo 1835619 50245049 := bstep (se 2 (by rfl) ⟨18841893, by rfl⟩ : syracuseStep 50245049 = 37683787) B37683787
theorem B4132331 : Blo 1835619 4132331 := bstep (se 1 (by rfl) ⟨3099248, by rfl⟩ : syracuseStep 4132331 = 6198497) B6198497
theorem B3100207 : Blo 1835619 3100207 := bstep (se 1 (by rfl) ⟨2325155, by rfl⟩ : syracuseStep 3100207 = 4650311) B4650311
theorem B2756303 : Blo 1835619 2756303 := bstep (se 1 (by rfl) ⟨2067227, by rfl⟩ : syracuseStep 2756303 = 4134455) B4134455
theorem B3485767 : Blo 1835619 3485767 := bstep (se 1 (by rfl) ⟨2614325, by rfl⟩ : syracuseStep 3485767 = 5228651) B5228651
theorem B21213479 : Blo 1835619 21213479 := bstep (se 1 (by rfl) ⟨15910109, by rfl⟩ : syracuseStep 21213479 = 31820219) B31820219
theorem B35321143 : Blo 1835619 35321143 := bstep (se 1 (by rfl) ⟨26490857, by rfl⟩ : syracuseStep 35321143 = 52981715) B52981715
theorem B257807933 : Blo 1835619 257807933 := bstep (se 3 (by rfl) ⟨48338987, by rfl⟩ : syracuseStep 257807933 = 96677975) B96677975
theorem B10459145 : Blo 1835619 10459145 := bstep (se 2 (by rfl) ⟨3922179, by rfl⟩ : syracuseStep 10459145 = 7844359) B7844359
theorem B13416673 : Blo 1835619 13416673 := bstep (se 2 (by rfl) ⟨5031252, by rfl⟩ : syracuseStep 13416673 = 10062505) B10062505
theorem B9296207 : Blo 1835619 9296207 := bstep (se 1 (by rfl) ⟨6972155, by rfl⟩ : syracuseStep 9296207 = 13944311) B13944311
theorem B339123023 : Blo 1835619 339123023 := bstep (se 1 (by rfl) ⟨254342267, by rfl⟩ : syracuseStep 339123023 = 508684535) B508684535
theorem B5372861 : Blo 1835619 5372861 := bstep (se 3 (by rfl) ⟨1007411, by rfl⟩ : syracuseStep 5372861 = 2014823) B2014823
theorem B2325439 : Blo 1835619 2325439 := bstep (se 1 (by rfl) ⟨1744079, by rfl⟩ : syracuseStep 2325439 = 3488159) B3488159
theorem B9297179 : Blo 1835619 9297179 := bstep (se 1 (by rfl) ⟨6972884, by rfl⟩ : syracuseStep 9297179 = 13945769) B13945769
theorem B13950629 : Blo 1835619 13950629 := bstep (se 4 (by rfl) ⟨1307871, by rfl⟩ : syracuseStep 13950629 = 2615743) B2615743
theorem B14900921 : Blo 1835619 14900921 := bstep (se 2 (by rfl) ⟨5587845, by rfl⟩ : syracuseStep 14900921 = 11175691) B11175691
theorem B28278605 : Blo 1835619 28278605 := bstep (se 3 (by rfl) ⟨5302238, by rfl⟩ : syracuseStep 28278605 = 10604477) B10604477
theorem B5881835 : Blo 1835619 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B1835771 : Blo 1835619 1835771 := bstep (se 1 (by rfl) ⟨1376828, by rfl⟩ : syracuseStep 1835771 = 2753657) B2753657
theorem B2753639 : Blo 1835619 2753639 := bstep (se 1 (by rfl) ⟨2065229, by rfl⟩ : syracuseStep 2753639 = 4130459) B4130459
theorem B2753855 : Blo 1835619 2753855 := bstep (se 1 (by rfl) ⟨2065391, by rfl⟩ : syracuseStep 2753855 = 4130783) B4130783
theorem B1836351 : Blo 1835619 1836351 := bstep (se 1 (by rfl) ⟨1377263, by rfl⟩ : syracuseStep 1836351 = 2754527) B2754527
theorem B6972763 : Blo 1835619 6972763 := bstep (se 1 (by rfl) ⟨5229572, by rfl⟩ : syracuseStep 6972763 = 10459145) B10459145
theorem B1837223 : Blo 1835619 1837223 := bstep (se 1 (by rfl) ⟨1377917, by rfl⟩ : syracuseStep 1837223 = 2755835) B2755835
theorem B75409613 : Blo 1835619 75409613 := bstep (se 3 (by rfl) ⟨14139302, by rfl⟩ : syracuseStep 75409613 = 28278605) B28278605
theorem B2754887 : Blo 1835619 2754887 := bstep (se 1 (by rfl) ⟨2066165, by rfl⟩ : syracuseStep 2754887 = 4132331) B4132331
theorem B9300419 : Blo 1835619 9300419 := bstep (se 1 (by rfl) ⟨6975314, by rfl⟩ : syracuseStep 9300419 = 13950629) B13950629
theorem B1837535 : Blo 1835619 1837535 := bstep (se 1 (by rfl) ⟨1378151, by rfl⟩ : syracuseStep 1837535 = 2756303) B2756303
theorem B4647689 : Blo 1835619 4647689 := bstep (se 2 (by rfl) ⟨1742883, by rfl⟩ : syracuseStep 4647689 = 3485767) B3485767
theorem B14142319 : Blo 1835619 14142319 := bstep (se 1 (by rfl) ⟨10606739, by rfl⟩ : syracuseStep 14142319 = 21213479) B21213479
theorem B20909177 : Blo 1835619 20909177 := bstep (se 2 (by rfl) ⟨7840941, by rfl⟩ : syracuseStep 20909177 = 15681883) B15681883
theorem B4648367 : Blo 1835619 4648367 := bstep (se 1 (by rfl) ⟨3486275, by rfl⟩ : syracuseStep 4648367 = 6972551) B6972551
theorem B171871955 : Blo 1835619 171871955 := bstep (se 1 (by rfl) ⟨128903966, by rfl⟩ : syracuseStep 171871955 = 257807933) B257807933
theorem B3100585 : Blo 1835619 3100585 := bstep (se 2 (by rfl) ⟨1162719, by rfl⟩ : syracuseStep 3100585 = 2325439) B2325439
theorem B6197471 : Blo 1835619 6197471 := bstep (se 1 (by rfl) ⟨4648103, by rfl⟩ : syracuseStep 6197471 = 9296207) B9296207
theorem B4133609 : Blo 1835619 4133609 := bstep (se 2 (by rfl) ⟨1550103, by rfl⟩ : syracuseStep 4133609 = 3100207) B3100207
theorem B6198119 : Blo 1835619 6198119 := bstep (se 1 (by rfl) ⟨4648589, by rfl⟩ : syracuseStep 6198119 = 9297179) B9297179
theorem B9933947 : Blo 1835619 9933947 := bstep (se 1 (by rfl) ⟨7450460, by rfl⟩ : syracuseStep 9933947 = 14900921) B14900921
theorem B3921223 : Blo 1835619 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B4134491 : Blo 1835619 4134491 := bstep (se 1 (by rfl) ⟨3100868, by rfl⟩ : syracuseStep 4134491 = 6201737) B6201737
theorem B17888897 : Blo 1835619 17888897 := bstep (se 2 (by rfl) ⟨6708336, by rfl⟩ : syracuseStep 17888897 = 13416673) B13416673
theorem B3725183 : Blo 1835619 3725183 := bstep (se 1 (by rfl) ⟨2793887, by rfl⟩ : syracuseStep 3725183 = 5587775) B5587775
theorem B133986797 : Blo 1835619 133986797 := bstep (se 3 (by rfl) ⟨25122524, by rfl⟩ : syracuseStep 133986797 = 50245049) B50245049
theorem B135879353 : Blo 1835619 135879353 := bstep (se 2 (by rfl) ⟨50954757, by rfl⟩ : syracuseStep 135879353 = 101909515) B101909515
theorem B47094857 : Blo 1835619 47094857 := bstep (se 2 (by rfl) ⟨17660571, by rfl⟩ : syracuseStep 47094857 = 35321143) B35321143
theorem B52960391 : Blo 1835619 52960391 := bstep (se 1 (by rfl) ⟨39720293, by rfl⟩ : syracuseStep 52960391 = 79440587) B79440587
theorem B226082015 : Blo 1835619 226082015 := bstep (se 1 (by rfl) ⟨169561511, by rfl⟩ : syracuseStep 226082015 = 339123023) B339123023
theorem B57310517 : Blo 1835619 57310517 := bstep (se 5 (by rfl) ⟨2686430, by rfl⟩ : syracuseStep 57310517 = 5372861) B5372861
theorem B1835759 : Blo 1835619 1835759 := bstep (se 1 (by rfl) ⟨1376819, by rfl⟩ : syracuseStep 1835759 = 2753639) B2753639
theorem B1835903 : Blo 1835619 1835903 := bstep (se 1 (by rfl) ⟨1376927, by rfl⟩ : syracuseStep 1835903 = 2753855) B2753855
theorem B2483455 : Blo 1835619 2483455 := bstep (se 1 (by rfl) ⟨1862591, by rfl⟩ : syracuseStep 2483455 = 3725183) B3725183
theorem B1836591 : Blo 1835619 1836591 := bstep (se 1 (by rfl) ⟨1377443, by rfl⟩ : syracuseStep 1836591 = 2754887) B2754887
theorem B47703725 : Blo 1835619 47703725 := bstep (se 3 (by rfl) ⟨8944448, by rfl⟩ : syracuseStep 47703725 = 17888897) B17888897
theorem B5228297 : Blo 1835619 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B3098459 : Blo 1835619 3098459 := bstep (se 1 (by rfl) ⟨2323844, by rfl⟩ : syracuseStep 3098459 = 4647689) B4647689
theorem B75425701 : Blo 1835619 75425701 := bstep (se 4 (by rfl) ⟨7071159, by rfl⟩ : syracuseStep 75425701 = 14142319) B14142319
theorem B3098911 : Blo 1835619 3098911 := bstep (se 1 (by rfl) ⟨2324183, by rfl⟩ : syracuseStep 3098911 = 4648367) B4648367
theorem B4131647 : Blo 1835619 4131647 := bstep (se 1 (by rfl) ⟨3098735, by rfl⟩ : syracuseStep 4131647 = 6197471) B6197471
theorem B2755739 : Blo 1835619 2755739 := bstep (se 1 (by rfl) ⟨2066804, by rfl⟩ : syracuseStep 2755739 = 4133609) B4133609
theorem B4132079 : Blo 1835619 4132079 := bstep (se 1 (by rfl) ⟨3099059, by rfl⟩ : syracuseStep 4132079 = 6198119) B6198119
theorem B6622631 : Blo 1835619 6622631 := bstep (se 1 (by rfl) ⟨4966973, by rfl⟩ : syracuseStep 6622631 = 9933947) B9933947
theorem B2756327 : Blo 1835619 2756327 := bstep (se 1 (by rfl) ⟨2067245, by rfl⟩ : syracuseStep 2756327 = 4134491) B4134491
theorem B31396571 : Blo 1835619 31396571 := bstep (se 1 (by rfl) ⟨23547428, by rfl⟩ : syracuseStep 31396571 = 47094857) B47094857
theorem B13939451 : Blo 1835619 13939451 := bstep (se 1 (by rfl) ⟨10454588, by rfl⟩ : syracuseStep 13939451 = 20909177) B20909177
theorem B150721343 : Blo 1835619 150721343 := bstep (se 1 (by rfl) ⟨113041007, by rfl⟩ : syracuseStep 150721343 = 226082015) B226082015
theorem B4134113 : Blo 1835619 4134113 := bstep (se 2 (by rfl) ⟨1550292, by rfl⟩ : syracuseStep 4134113 = 3100585) B3100585
theorem B50273075 : Blo 1835619 50273075 := bstep (se 1 (by rfl) ⟨37704806, by rfl⟩ : syracuseStep 50273075 = 75409613) B75409613
theorem B6200279 : Blo 1835619 6200279 := bstep (se 1 (by rfl) ⟨4650209, by rfl⟩ : syracuseStep 6200279 = 9300419) B9300419
theorem B89324531 : Blo 1835619 89324531 := bstep (se 1 (by rfl) ⟨66993398, by rfl⟩ : syracuseStep 89324531 = 133986797) B133986797
theorem B9297017 : Blo 1835619 9297017 := bstep (se 2 (by rfl) ⟨3486381, by rfl⟩ : syracuseStep 9297017 = 6972763) B6972763
theorem B90586235 : Blo 1835619 90586235 := bstep (se 1 (by rfl) ⟨67939676, by rfl⟩ : syracuseStep 90586235 = 135879353) B135879353
theorem B35306927 : Blo 1835619 35306927 := bstep (se 1 (by rfl) ⟨26480195, by rfl⟩ : syracuseStep 35306927 = 52960391) B52960391
theorem B38207011 : Blo 1835619 38207011 := bstep (se 1 (by rfl) ⟨28655258, by rfl⟩ : syracuseStep 38207011 = 57310517) B57310517
theorem B114581303 : Blo 1835619 114581303 := bstep (se 1 (by rfl) ⟨85935977, by rfl⟩ : syracuseStep 114581303 = 171871955) B171871955
theorem B20931047 : Blo 1835619 20931047 := bstep (se 1 (by rfl) ⟨15698285, by rfl⟩ : syracuseStep 20931047 = 31396571) B31396571
theorem B31802483 : Blo 1835619 31802483 := bstep (se 1 (by rfl) ⟨23851862, by rfl⟩ : syracuseStep 31802483 = 47703725) B47703725
theorem B2065639 : Blo 1835619 2065639 := bstep (se 1 (by rfl) ⟨1549229, by rfl⟩ : syracuseStep 2065639 = 3098459) B3098459
theorem B3311273 : Blo 1835619 3311273 := bstep (se 2 (by rfl) ⟨1241727, by rfl⟩ : syracuseStep 3311273 = 2483455) B2483455
theorem B33515383 : Blo 1835619 33515383 := bstep (se 1 (by rfl) ⟨25136537, by rfl⟩ : syracuseStep 33515383 = 50273075) B50273075
theorem B2754431 : Blo 1835619 2754431 := bstep (se 1 (by rfl) ⟨2065823, by rfl⟩ : syracuseStep 2754431 = 4131647) B4131647
theorem B59549687 : Blo 1835619 59549687 := bstep (se 1 (by rfl) ⟨44662265, by rfl⟩ : syracuseStep 59549687 = 89324531) B89324531
theorem B1837159 : Blo 1835619 1837159 := bstep (se 1 (by rfl) ⟨1377869, by rfl⟩ : syracuseStep 1837159 = 2755739) B2755739
theorem B2754719 : Blo 1835619 2754719 := bstep (se 1 (by rfl) ⟨2066039, by rfl⟩ : syracuseStep 2754719 = 4132079) B4132079
theorem B23537951 : Blo 1835619 23537951 := bstep (se 1 (by rfl) ⟨17653463, by rfl⟩ : syracuseStep 23537951 = 35306927) B35306927
theorem B1837551 : Blo 1835619 1837551 := bstep (se 1 (by rfl) ⟨1378163, by rfl⟩ : syracuseStep 1837551 = 2756327) B2756327
theorem B100567601 : Blo 1835619 100567601 := bstep (se 2 (by rfl) ⟨37712850, by rfl⟩ : syracuseStep 100567601 = 75425701) B75425701
theorem B4131881 : Blo 1835619 4131881 := bstep (se 2 (by rfl) ⟨1549455, by rfl⟩ : syracuseStep 4131881 = 3098911) B3098911
theorem B9292967 : Blo 1835619 9292967 := bstep (se 1 (by rfl) ⟨6969725, by rfl⟩ : syracuseStep 9292967 = 13939451) B13939451
theorem B2756075 : Blo 1835619 2756075 := bstep (se 1 (by rfl) ⟨2067056, by rfl⟩ : syracuseStep 2756075 = 4134113) B4134113
theorem B3485531 : Blo 1835619 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B4133519 : Blo 1835619 4133519 := bstep (se 1 (by rfl) ⟨3100139, by rfl⟩ : syracuseStep 4133519 = 6200279) B6200279
theorem B50942681 : Blo 1835619 50942681 := bstep (se 2 (by rfl) ⟨19103505, by rfl⟩ : syracuseStep 50942681 = 38207011) B38207011
theorem B6198011 : Blo 1835619 6198011 := bstep (se 1 (by rfl) ⟨4648508, by rfl⟩ : syracuseStep 6198011 = 9297017) B9297017
theorem B76387535 : Blo 1835619 76387535 := bstep (se 1 (by rfl) ⟨57290651, by rfl⟩ : syracuseStep 76387535 = 114581303) B114581303
theorem B241563293 : Blo 1835619 241563293 := bstep (se 3 (by rfl) ⟨45293117, by rfl⟩ : syracuseStep 241563293 = 90586235) B90586235
theorem B100480895 : Blo 1835619 100480895 := bstep (se 1 (by rfl) ⟨75360671, by rfl⟩ : syracuseStep 100480895 = 150721343) B150721343
theorem B4415087 : Blo 1835619 4415087 := bstep (se 1 (by rfl) ⟨3311315, by rfl⟩ : syracuseStep 4415087 = 6622631) B6622631
theorem B66987263 : Blo 1835619 66987263 := bstep (se 1 (by rfl) ⟨50240447, by rfl⟩ : syracuseStep 66987263 = 100480895) B100480895
theorem B1836287 : Blo 1835619 1836287 := bstep (se 1 (by rfl) ⟨1377215, by rfl⟩ : syracuseStep 1836287 = 2754431) B2754431
theorem B39699791 : Blo 1835619 39699791 := bstep (se 1 (by rfl) ⟨29774843, by rfl⟩ : syracuseStep 39699791 = 59549687) B59549687
theorem B1836479 : Blo 1835619 1836479 := bstep (se 1 (by rfl) ⟨1377359, by rfl⟩ : syracuseStep 1836479 = 2754719) B2754719
theorem B2754185 : Blo 1835619 2754185 := bstep (se 2 (by rfl) ⟨1032819, by rfl⟩ : syracuseStep 2754185 = 2065639) B2065639
theorem B2754587 : Blo 1835619 2754587 := bstep (se 1 (by rfl) ⟨2065940, by rfl⟩ : syracuseStep 2754587 = 4131881) B4131881
theorem B6195311 : Blo 1835619 6195311 := bstep (se 1 (by rfl) ⟨4646483, by rfl⟩ : syracuseStep 6195311 = 9292967) B9292967
theorem B1837383 : Blo 1835619 1837383 := bstep (se 1 (by rfl) ⟨1378037, by rfl⟩ : syracuseStep 1837383 = 2756075) B2756075
theorem B2943391 : Blo 1835619 2943391 := bstep (se 1 (by rfl) ⟨2207543, by rfl⟩ : syracuseStep 2943391 = 4415087) B4415087
theorem B84806621 : Blo 1835619 84806621 := bstep (se 3 (by rfl) ⟨15901241, by rfl⟩ : syracuseStep 84806621 = 31802483) B31802483
theorem B13954031 : Blo 1835619 13954031 := bstep (se 1 (by rfl) ⟨10465523, by rfl⟩ : syracuseStep 13954031 = 20931047) B20931047
theorem B2755679 : Blo 1835619 2755679 := bstep (se 1 (by rfl) ⟨2066759, by rfl⟩ : syracuseStep 2755679 = 4133519) B4133519
theorem B4132007 : Blo 1835619 4132007 := bstep (se 1 (by rfl) ⟨3099005, by rfl⟩ : syracuseStep 4132007 = 6198011) B6198011
theorem B50925023 : Blo 1835619 50925023 := bstep (se 1 (by rfl) ⟨38193767, by rfl⟩ : syracuseStep 50925023 = 76387535) B76387535
theorem B161042195 : Blo 1835619 161042195 := bstep (se 1 (by rfl) ⟨120781646, by rfl⟩ : syracuseStep 161042195 = 241563293) B241563293
theorem B2207515 : Blo 1835619 2207515 := bstep (se 1 (by rfl) ⟨1655636, by rfl⟩ : syracuseStep 2207515 = 3311273) B3311273
theorem B15691967 : Blo 1835619 15691967 := bstep (se 1 (by rfl) ⟨11768975, by rfl⟩ : syracuseStep 15691967 = 23537951) B23537951
theorem B9294749 : Blo 1835619 9294749 := bstep (se 3 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 9294749 = 3485531) B3485531
theorem B33961787 : Blo 1835619 33961787 := bstep (se 1 (by rfl) ⟨25471340, by rfl⟩ : syracuseStep 33961787 = 50942681) B50942681
theorem B67045067 : Blo 1835619 67045067 := bstep (se 1 (by rfl) ⟨50283800, by rfl⟩ : syracuseStep 67045067 = 100567601) B100567601
theorem B44687177 : Blo 1835619 44687177 := bstep (se 2 (by rfl) ⟨16757691, by rfl⟩ : syracuseStep 44687177 = 33515383) B33515383
theorem B10461311 : Blo 1835619 10461311 := bstep (se 1 (by rfl) ⟨7845983, by rfl⟩ : syracuseStep 10461311 = 15691967) B15691967
theorem B3924521 : Blo 1835619 3924521 := bstep (se 2 (by rfl) ⟨1471695, by rfl⟩ : syracuseStep 3924521 = 2943391) B2943391
theorem B1836123 : Blo 1835619 1836123 := bstep (se 1 (by rfl) ⟨1377092, by rfl⟩ : syracuseStep 1836123 = 2754185) B2754185
theorem B44696711 : Blo 1835619 44696711 := bstep (se 1 (by rfl) ⟨33522533, by rfl⟩ : syracuseStep 44696711 = 67045067) B67045067
theorem B1836391 : Blo 1835619 1836391 := bstep (se 1 (by rfl) ⟨1377293, by rfl⟩ : syracuseStep 1836391 = 2754587) B2754587
theorem B4130207 : Blo 1835619 4130207 := bstep (se 1 (by rfl) ⟨3097655, by rfl⟩ : syracuseStep 4130207 = 6195311) B6195311
theorem B1837119 : Blo 1835619 1837119 := bstep (se 1 (by rfl) ⟨1377839, by rfl⟩ : syracuseStep 1837119 = 2755679) B2755679
theorem B2754671 : Blo 1835619 2754671 := bstep (se 1 (by rfl) ⟨2066003, by rfl⟩ : syracuseStep 2754671 = 4132007) B4132007
theorem B33950015 : Blo 1835619 33950015 := bstep (se 1 (by rfl) ⟨25462511, by rfl⟩ : syracuseStep 33950015 = 50925023) B50925023
theorem B2943353 : Blo 1835619 2943353 := bstep (se 2 (by rfl) ⟨1103757, by rfl⟩ : syracuseStep 2943353 = 2207515) B2207515
theorem B6196499 : Blo 1835619 6196499 := bstep (se 1 (by rfl) ⟨4647374, by rfl⟩ : syracuseStep 6196499 = 9294749) B9294749
theorem B44658175 : Blo 1835619 44658175 := bstep (se 1 (by rfl) ⟨33493631, by rfl⟩ : syracuseStep 44658175 = 66987263) B66987263
theorem B56537747 : Blo 1835619 56537747 := bstep (se 1 (by rfl) ⟨42403310, by rfl⟩ : syracuseStep 56537747 = 84806621) B84806621
theorem B9302687 : Blo 1835619 9302687 := bstep (se 1 (by rfl) ⟨6977015, by rfl⟩ : syracuseStep 9302687 = 13954031) B13954031
theorem B107361463 : Blo 1835619 107361463 := bstep (se 1 (by rfl) ⟨80521097, by rfl⟩ : syracuseStep 107361463 = 161042195) B161042195
theorem B29791451 : Blo 1835619 29791451 := bstep (se 1 (by rfl) ⟨22343588, by rfl⟩ : syracuseStep 29791451 = 44687177) B44687177
theorem B26466527 : Blo 1835619 26466527 := bstep (se 1 (by rfl) ⟨19849895, by rfl⟩ : syracuseStep 26466527 = 39699791) B39699791
theorem B22641191 : Blo 1835619 22641191 := bstep (se 1 (by rfl) ⟨16980893, by rfl⟩ : syracuseStep 22641191 = 33961787) B33961787
theorem B37691831 : Blo 1835619 37691831 := bstep (se 1 (by rfl) ⟨28268873, by rfl⟩ : syracuseStep 37691831 = 56537747) B56537747
theorem B6201791 : Blo 1835619 6201791 := bstep (se 1 (by rfl) ⟨4651343, by rfl⟩ : syracuseStep 6201791 = 9302687) B9302687
theorem B2753471 : Blo 1835619 2753471 := bstep (se 1 (by rfl) ⟨2065103, by rfl⟩ : syracuseStep 2753471 = 4130207) B4130207
theorem B1836447 : Blo 1835619 1836447 := bstep (se 1 (by rfl) ⟨1377335, by rfl⟩ : syracuseStep 1836447 = 2754671) B2754671
theorem B143148617 : Blo 1835619 143148617 := bstep (se 2 (by rfl) ⟨53680731, by rfl⟩ : syracuseStep 143148617 = 107361463) B107361463
theorem B4130999 : Blo 1835619 4130999 := bstep (se 1 (by rfl) ⟨3098249, by rfl⟩ : syracuseStep 4130999 = 6196499) B6196499
theorem B6974207 : Blo 1835619 6974207 := bstep (se 1 (by rfl) ⟨5230655, by rfl⟩ : syracuseStep 6974207 = 10461311) B10461311
theorem B2616347 : Blo 1835619 2616347 := bstep (se 1 (by rfl) ⟨1962260, by rfl⟩ : syracuseStep 2616347 = 3924521) B3924521
theorem B29797807 : Blo 1835619 29797807 := bstep (se 1 (by rfl) ⟨22348355, by rfl⟩ : syracuseStep 29797807 = 44696711) B44696711
theorem B19860967 : Blo 1835619 19860967 := bstep (se 1 (by rfl) ⟨14895725, by rfl⟩ : syracuseStep 19860967 = 29791451) B29791451
theorem B1962235 : Blo 1835619 1962235 := bstep (se 1 (by rfl) ⟨1471676, by rfl⟩ : syracuseStep 1962235 = 2943353) B2943353
theorem B15094127 : Blo 1835619 15094127 := bstep (se 1 (by rfl) ⟨11320595, by rfl⟩ : syracuseStep 15094127 = 22641191) B22641191
theorem B59544233 : Blo 1835619 59544233 := bstep (se 2 (by rfl) ⟨22329087, by rfl⟩ : syracuseStep 59544233 = 44658175) B44658175
theorem B17644351 : Blo 1835619 17644351 := bstep (se 1 (by rfl) ⟨13233263, by rfl⟩ : syracuseStep 17644351 = 26466527) B26466527
theorem B22633343 : Blo 1835619 22633343 := bstep (se 1 (by rfl) ⟨16975007, by rfl⟩ : syracuseStep 22633343 = 33950015) B33950015
theorem B1835647 : Blo 1835619 1835647 := bstep (se 1 (by rfl) ⟨1376735, by rfl⟩ : syracuseStep 1835647 = 2753471) B2753471
theorem B2753999 : Blo 1835619 2753999 := bstep (se 1 (by rfl) ⟨2065499, by rfl⟩ : syracuseStep 2753999 = 4130999) B4130999
theorem B10062751 : Blo 1835619 10062751 := bstep (se 1 (by rfl) ⟨7547063, by rfl⟩ : syracuseStep 10062751 = 15094127) B15094127
theorem B2616313 : Blo 1835619 2616313 := bstep (se 2 (by rfl) ⟨981117, by rfl⟩ : syracuseStep 2616313 = 1962235) B1962235
theorem B95432411 : Blo 1835619 95432411 := bstep (se 1 (by rfl) ⟨71574308, by rfl⟩ : syracuseStep 95432411 = 143148617) B143148617
theorem B100511549 : Blo 1835619 100511549 := bstep (se 3 (by rfl) ⟨18845915, by rfl⟩ : syracuseStep 100511549 = 37691831) B37691831
theorem B4649471 : Blo 1835619 4649471 := bstep (se 1 (by rfl) ⟨3487103, by rfl⟩ : syracuseStep 4649471 = 6974207) B6974207
theorem B26481289 : Blo 1835619 26481289 := bstep (se 2 (by rfl) ⟨9930483, by rfl⟩ : syracuseStep 26481289 = 19860967) B19860967
theorem B6976925 : Blo 1835619 6976925 := bstep (se 3 (by rfl) ⟨1308173, by rfl⟩ : syracuseStep 6976925 = 2616347) B2616347
theorem B4134527 : Blo 1835619 4134527 := bstep (se 1 (by rfl) ⟨3100895, by rfl⟩ : syracuseStep 4134527 = 6201791) B6201791
theorem B39696155 : Blo 1835619 39696155 := bstep (se 1 (by rfl) ⟨29772116, by rfl⟩ : syracuseStep 39696155 = 59544233) B59544233
theorem B23525801 : Blo 1835619 23525801 := bstep (se 2 (by rfl) ⟨8822175, by rfl⟩ : syracuseStep 23525801 = 17644351) B17644351
theorem B39730409 : Blo 1835619 39730409 := bstep (se 2 (by rfl) ⟨14898903, by rfl⟩ : syracuseStep 39730409 = 29797807) B29797807
theorem B15088895 : Blo 1835619 15088895 := bstep (se 1 (by rfl) ⟨11316671, by rfl⟩ : syracuseStep 15088895 = 22633343) B22633343
theorem B35308385 : Blo 1835619 35308385 := bstep (se 2 (by rfl) ⟨13240644, by rfl⟩ : syracuseStep 35308385 = 26481289) B26481289
theorem B1835999 : Blo 1835619 1835999 := bstep (se 1 (by rfl) ⟨1376999, by rfl⟩ : syracuseStep 1835999 = 2753999) B2753999
theorem B26486939 : Blo 1835619 26486939 := bstep (se 1 (by rfl) ⟨19865204, by rfl⟩ : syracuseStep 26486939 = 39730409) B39730409
theorem B63621607 : Blo 1835619 63621607 := bstep (se 1 (by rfl) ⟨47716205, by rfl⟩ : syracuseStep 63621607 = 95432411) B95432411
theorem B3099647 : Blo 1835619 3099647 := bstep (se 1 (by rfl) ⟨2324735, by rfl⟩ : syracuseStep 3099647 = 4649471) B4649471
theorem B2756351 : Blo 1835619 2756351 := bstep (se 1 (by rfl) ⟨2067263, by rfl⟩ : syracuseStep 2756351 = 4134527) B4134527
theorem B26464103 : Blo 1835619 26464103 := bstep (se 1 (by rfl) ⟨19848077, by rfl⟩ : syracuseStep 26464103 = 39696155) B39696155
theorem B15683867 : Blo 1835619 15683867 := bstep (se 1 (by rfl) ⟨11762900, by rfl⟩ : syracuseStep 15683867 = 23525801) B23525801
theorem B67007699 : Blo 1835619 67007699 := bstep (se 1 (by rfl) ⟨50255774, by rfl⟩ : syracuseStep 67007699 = 100511549) B100511549
theorem B4651283 : Blo 1835619 4651283 := bstep (se 1 (by rfl) ⟨3488462, by rfl⟩ : syracuseStep 4651283 = 6976925) B6976925
theorem B13417001 : Blo 1835619 13417001 := bstep (se 2 (by rfl) ⟨5031375, by rfl⟩ : syracuseStep 13417001 = 10062751) B10062751
theorem B3488417 : Blo 1835619 3488417 := bstep (se 2 (by rfl) ⟨1308156, by rfl⟩ : syracuseStep 3488417 = 2616313) B2616313
theorem B10059263 : Blo 1835619 10059263 := bstep (se 1 (by rfl) ⟨7544447, by rfl⟩ : syracuseStep 10059263 = 15088895) B15088895
theorem B84828809 : Blo 1835619 84828809 := bstep (se 2 (by rfl) ⟨31810803, by rfl⟩ : syracuseStep 84828809 = 63621607) B63621607
theorem B44671799 : Blo 1835619 44671799 := bstep (se 1 (by rfl) ⟨33503849, by rfl⟩ : syracuseStep 44671799 = 67007699) B67007699
theorem B2066431 : Blo 1835619 2066431 := bstep (se 1 (by rfl) ⟨1549823, by rfl⟩ : syracuseStep 2066431 = 3099647) B3099647
theorem B1837567 : Blo 1835619 1837567 := bstep (se 1 (by rfl) ⟨1378175, by rfl⟩ : syracuseStep 1837567 = 2756351) B2756351
theorem B10455911 : Blo 1835619 10455911 := bstep (se 1 (by rfl) ⟨7841933, by rfl⟩ : syracuseStep 10455911 = 15683867) B15683867
theorem B23538923 : Blo 1835619 23538923 := bstep (se 1 (by rfl) ⟨17654192, by rfl⟩ : syracuseStep 23538923 = 35308385) B35308385
theorem B17657959 : Blo 1835619 17657959 := bstep (se 1 (by rfl) ⟨13243469, by rfl⟩ : syracuseStep 17657959 = 26486939) B26486939
theorem B3100855 : Blo 1835619 3100855 := bstep (se 1 (by rfl) ⟨2325641, by rfl⟩ : syracuseStep 3100855 = 4651283) B4651283
theorem B6706175 : Blo 1835619 6706175 := bstep (se 1 (by rfl) ⟨5029631, by rfl⟩ : syracuseStep 6706175 = 10059263) B10059263
theorem B17642735 : Blo 1835619 17642735 := bstep (se 1 (by rfl) ⟨13232051, by rfl⟩ : syracuseStep 17642735 = 26464103) B26464103
theorem B8944667 : Blo 1835619 8944667 := bstep (se 1 (by rfl) ⟨6708500, by rfl⟩ : syracuseStep 8944667 = 13417001) B13417001
theorem B2325611 : Blo 1835619 2325611 := bstep (se 1 (by rfl) ⟨1744208, by rfl⟩ : syracuseStep 2325611 = 3488417) B3488417
theorem B23543945 : Blo 1835619 23543945 := bstep (se 2 (by rfl) ⟨8828979, by rfl⟩ : syracuseStep 23543945 = 17657959) B17657959
theorem B6201629 : Blo 1835619 6201629 := bstep (se 3 (by rfl) ⟨1162805, by rfl⟩ : syracuseStep 6201629 = 2325611) B2325611
theorem B2755241 : Blo 1835619 2755241 := bstep (se 2 (by rfl) ⟨1033215, by rfl⟩ : syracuseStep 2755241 = 2066431) B2066431
theorem B29781199 : Blo 1835619 29781199 := bstep (se 1 (by rfl) ⟨22335899, by rfl⟩ : syracuseStep 29781199 = 44671799) B44671799
theorem B226210157 : Blo 1835619 226210157 := bstep (se 3 (by rfl) ⟨42414404, by rfl⟩ : syracuseStep 226210157 = 84828809) B84828809
theorem B15692615 : Blo 1835619 15692615 := bstep (se 1 (by rfl) ⟨11769461, by rfl⟩ : syracuseStep 15692615 = 23538923) B23538923
theorem B4134473 : Blo 1835619 4134473 := bstep (se 2 (by rfl) ⟨1550427, by rfl⟩ : syracuseStep 4134473 = 3100855) B3100855
theorem B11761823 : Blo 1835619 11761823 := bstep (se 1 (by rfl) ⟨8821367, by rfl⟩ : syracuseStep 11761823 = 17642735) B17642735
theorem B6970607 : Blo 1835619 6970607 := bstep (se 1 (by rfl) ⟨5227955, by rfl⟩ : syracuseStep 6970607 = 10455911) B10455911
theorem B5963111 : Blo 1835619 5963111 := bstep (se 1 (by rfl) ⟨4472333, by rfl⟩ : syracuseStep 5963111 = 8944667) B8944667
theorem B71532533 : Blo 1835619 71532533 := bstep (se 5 (by rfl) ⟨3353087, by rfl⟩ : syracuseStep 71532533 = 6706175) B6706175
theorem B15695963 : Blo 1835619 15695963 := bstep (se 1 (by rfl) ⟨11771972, by rfl⟩ : syracuseStep 15695963 = 23543945) B23543945
theorem B150806771 : Blo 1835619 150806771 := bstep (se 1 (by rfl) ⟨113105078, by rfl⟩ : syracuseStep 150806771 = 226210157) B226210157
theorem B10461743 : Blo 1835619 10461743 := bstep (se 1 (by rfl) ⟨7846307, by rfl⟩ : syracuseStep 10461743 = 15692615) B15692615
theorem B7841215 : Blo 1835619 7841215 := bstep (se 1 (by rfl) ⟨5880911, by rfl⟩ : syracuseStep 7841215 = 11761823) B11761823
theorem B39708265 : Blo 1835619 39708265 := bstep (se 2 (by rfl) ⟨14890599, by rfl⟩ : syracuseStep 39708265 = 29781199) B29781199
theorem B1836827 : Blo 1835619 1836827 := bstep (se 1 (by rfl) ⟨1377620, by rfl⟩ : syracuseStep 1836827 = 2755241) B2755241
theorem B4647071 : Blo 1835619 4647071 := bstep (se 1 (by rfl) ⟨3485303, by rfl⟩ : syracuseStep 4647071 = 6970607) B6970607
theorem B3975407 : Blo 1835619 3975407 := bstep (se 1 (by rfl) ⟨2981555, by rfl⟩ : syracuseStep 3975407 = 5963111) B5963111
theorem B47688355 : Blo 1835619 47688355 := bstep (se 1 (by rfl) ⟨35766266, by rfl⟩ : syracuseStep 47688355 = 71532533) B71532533
theorem B2756315 : Blo 1835619 2756315 := bstep (se 1 (by rfl) ⟨2067236, by rfl⟩ : syracuseStep 2756315 = 4134473) B4134473
theorem B4134419 : Blo 1835619 4134419 := bstep (se 1 (by rfl) ⟨3100814, by rfl⟩ : syracuseStep 4134419 = 6201629) B6201629
theorem B3098047 : Blo 1835619 3098047 := bstep (se 1 (by rfl) ⟨2323535, by rfl⟩ : syracuseStep 3098047 = 4647071) B4647071
theorem B10454953 : Blo 1835619 10454953 := bstep (se 2 (by rfl) ⟨3920607, by rfl⟩ : syracuseStep 10454953 = 7841215) B7841215
theorem B1837543 : Blo 1835619 1837543 := bstep (se 1 (by rfl) ⟨1378157, by rfl⟩ : syracuseStep 1837543 = 2756315) B2756315
theorem B10463975 : Blo 1835619 10463975 := bstep (se 1 (by rfl) ⟨7847981, by rfl⟩ : syracuseStep 10463975 = 15695963) B15695963
theorem B6974495 : Blo 1835619 6974495 := bstep (se 1 (by rfl) ⟨5230871, by rfl⟩ : syracuseStep 6974495 = 10461743) B10461743
theorem B2756279 : Blo 1835619 2756279 := bstep (se 1 (by rfl) ⟨2067209, by rfl⟩ : syracuseStep 2756279 = 4134419) B4134419
theorem B2650271 : Blo 1835619 2650271 := bstep (se 1 (by rfl) ⟨1987703, by rfl⟩ : syracuseStep 2650271 = 3975407) B3975407
theorem B100537847 : Blo 1835619 100537847 := bstep (se 1 (by rfl) ⟨75403385, by rfl⟩ : syracuseStep 100537847 = 150806771) B150806771
theorem B63584473 : Blo 1835619 63584473 := bstep (se 2 (by rfl) ⟨23844177, by rfl⟩ : syracuseStep 63584473 = 47688355) B47688355
theorem B52944353 : Blo 1835619 52944353 := bstep (se 2 (by rfl) ⟨19854132, by rfl⟩ : syracuseStep 52944353 = 39708265) B39708265
theorem B84779297 : Blo 1835619 84779297 := bstep (se 2 (by rfl) ⟨31792236, by rfl⟩ : syracuseStep 84779297 = 63584473) B63584473
theorem B4130729 : Blo 1835619 4130729 := bstep (se 2 (by rfl) ⟨1549023, by rfl⟩ : syracuseStep 4130729 = 3098047) B3098047
theorem B1837519 : Blo 1835619 1837519 := bstep (se 1 (by rfl) ⟨1378139, by rfl⟩ : syracuseStep 1837519 = 2756279) B2756279
theorem B6975983 : Blo 1835619 6975983 := bstep (se 1 (by rfl) ⟨5231987, by rfl⟩ : syracuseStep 6975983 = 10463975) B10463975
theorem B4649663 : Blo 1835619 4649663 := bstep (se 1 (by rfl) ⟨3487247, by rfl⟩ : syracuseStep 4649663 = 6974495) B6974495
theorem B35296235 : Blo 1835619 35296235 := bstep (se 1 (by rfl) ⟨26472176, by rfl⟩ : syracuseStep 35296235 = 52944353) B52944353
theorem B13939937 : Blo 1835619 13939937 := bstep (se 2 (by rfl) ⟨5227476, by rfl⟩ : syracuseStep 13939937 = 10454953) B10454953
theorem B7067389 : Blo 1835619 7067389 := bstep (se 3 (by rfl) ⟨1325135, by rfl⟩ : syracuseStep 7067389 = 2650271) B2650271
theorem B67025231 : Blo 1835619 67025231 := bstep (se 1 (by rfl) ⟨50268923, by rfl⟩ : syracuseStep 67025231 = 100537847) B100537847
theorem B2753819 : Blo 1835619 2753819 := bstep (se 1 (by rfl) ⟨2065364, by rfl⟩ : syracuseStep 2753819 = 4130729) B4130729
theorem B9423185 : Blo 1835619 9423185 := bstep (se 2 (by rfl) ⟨3533694, by rfl⟩ : syracuseStep 9423185 = 7067389) B7067389
theorem B56519531 : Blo 1835619 56519531 := bstep (se 1 (by rfl) ⟨42389648, by rfl⟩ : syracuseStep 56519531 = 84779297) B84779297
theorem B3099775 : Blo 1835619 3099775 := bstep (se 1 (by rfl) ⟨2324831, by rfl⟩ : syracuseStep 3099775 = 4649663) B4649663
theorem B23530823 : Blo 1835619 23530823 := bstep (se 1 (by rfl) ⟨17648117, by rfl⟩ : syracuseStep 23530823 = 35296235) B35296235
theorem B9293291 : Blo 1835619 9293291 := bstep (se 1 (by rfl) ⟨6969968, by rfl⟩ : syracuseStep 9293291 = 13939937) B13939937
theorem B44683487 : Blo 1835619 44683487 := bstep (se 1 (by rfl) ⟨33512615, by rfl⟩ : syracuseStep 44683487 = 67025231) B67025231
theorem B4650655 : Blo 1835619 4650655 := bstep (se 1 (by rfl) ⟨3487991, by rfl⟩ : syracuseStep 4650655 = 6975983) B6975983
theorem B1835879 : Blo 1835619 1835879 := bstep (se 1 (by rfl) ⟨1376909, by rfl⟩ : syracuseStep 1835879 = 2753819) B2753819
theorem B6195527 : Blo 1835619 6195527 := bstep (se 1 (by rfl) ⟨4646645, by rfl⟩ : syracuseStep 6195527 = 9293291) B9293291
theorem B29788991 : Blo 1835619 29788991 := bstep (se 1 (by rfl) ⟨22341743, by rfl⟩ : syracuseStep 29788991 = 44683487) B44683487
theorem B4133033 : Blo 1835619 4133033 := bstep (se 2 (by rfl) ⟨1549887, by rfl⟩ : syracuseStep 4133033 = 3099775) B3099775
theorem B37679687 : Blo 1835619 37679687 := bstep (se 1 (by rfl) ⟨28259765, by rfl⟩ : syracuseStep 37679687 = 56519531) B56519531
theorem B100513973 : Blo 1835619 100513973 := bstep (se 5 (by rfl) ⟨4711592, by rfl⟩ : syracuseStep 100513973 = 9423185) B9423185
theorem B6200873 : Blo 1835619 6200873 := bstep (se 2 (by rfl) ⟨2325327, by rfl⟩ : syracuseStep 6200873 = 4650655) B4650655
theorem B15687215 : Blo 1835619 15687215 := bstep (se 1 (by rfl) ⟨11765411, by rfl⟩ : syracuseStep 15687215 = 23530823) B23530823
theorem B4130351 : Blo 1835619 4130351 := bstep (se 1 (by rfl) ⟨3097763, by rfl⟩ : syracuseStep 4130351 = 6195527) B6195527
theorem B19859327 : Blo 1835619 19859327 := bstep (se 1 (by rfl) ⟨14894495, by rfl⟩ : syracuseStep 19859327 = 29788991) B29788991
theorem B2755355 : Blo 1835619 2755355 := bstep (se 1 (by rfl) ⟨2066516, by rfl⟩ : syracuseStep 2755355 = 4133033) B4133033
theorem B25119791 : Blo 1835619 25119791 := bstep (se 1 (by rfl) ⟨18839843, by rfl⟩ : syracuseStep 25119791 = 37679687) B37679687
theorem B4133915 : Blo 1835619 4133915 := bstep (se 1 (by rfl) ⟨3100436, by rfl⟩ : syracuseStep 4133915 = 6200873) B6200873
theorem B10458143 : Blo 1835619 10458143 := bstep (se 1 (by rfl) ⟨7843607, by rfl⟩ : syracuseStep 10458143 = 15687215) B15687215
theorem B67009315 : Blo 1835619 67009315 := bstep (se 1 (by rfl) ⟨50256986, by rfl⟩ : syracuseStep 67009315 = 100513973) B100513973
theorem B6972095 : Blo 1835619 6972095 := bstep (se 1 (by rfl) ⟨5229071, by rfl⟩ : syracuseStep 6972095 = 10458143) B10458143
theorem B2753567 : Blo 1835619 2753567 := bstep (se 1 (by rfl) ⟨2065175, by rfl⟩ : syracuseStep 2753567 = 4130351) B4130351
theorem B13239551 : Blo 1835619 13239551 := bstep (se 1 (by rfl) ⟨9929663, by rfl⟩ : syracuseStep 13239551 = 19859327) B19859327
theorem B1836903 : Blo 1835619 1836903 := bstep (se 1 (by rfl) ⟨1377677, by rfl⟩ : syracuseStep 1836903 = 2755355) B2755355
theorem B16746527 : Blo 1835619 16746527 := bstep (se 1 (by rfl) ⟨12559895, by rfl⟩ : syracuseStep 16746527 = 25119791) B25119791
theorem B2755943 : Blo 1835619 2755943 := bstep (se 1 (by rfl) ⟨2066957, by rfl⟩ : syracuseStep 2755943 = 4133915) B4133915
theorem B89345753 : Blo 1835619 89345753 := bstep (se 2 (by rfl) ⟨33504657, by rfl⟩ : syracuseStep 89345753 = 67009315) B67009315
theorem B1835711 : Blo 1835619 1835711 := bstep (se 1 (by rfl) ⟨1376783, by rfl⟩ : syracuseStep 1835711 = 2753567) B2753567
theorem B1837295 : Blo 1835619 1837295 := bstep (se 1 (by rfl) ⟨1377971, by rfl⟩ : syracuseStep 1837295 = 2755943) B2755943
theorem B4648063 : Blo 1835619 4648063 := bstep (se 1 (by rfl) ⟨3486047, by rfl⟩ : syracuseStep 4648063 = 6972095) B6972095
theorem B8826367 : Blo 1835619 8826367 := bstep (se 1 (by rfl) ⟨6619775, by rfl⟩ : syracuseStep 8826367 = 13239551) B13239551
theorem B11164351 : Blo 1835619 11164351 := bstep (se 1 (by rfl) ⟨8373263, by rfl⟩ : syracuseStep 11164351 = 16746527) B16746527
theorem B59563835 : Blo 1835619 59563835 := bstep (se 1 (by rfl) ⟨44672876, by rfl⟩ : syracuseStep 59563835 = 89345753) B89345753
theorem B14885801 : Blo 1835619 14885801 := bstep (se 2 (by rfl) ⟨5582175, by rfl⟩ : syracuseStep 14885801 = 11164351) B11164351
theorem B39709223 : Blo 1835619 39709223 := bstep (se 1 (by rfl) ⟨29781917, by rfl⟩ : syracuseStep 39709223 = 59563835) B59563835
theorem B6197417 : Blo 1835619 6197417 := bstep (se 2 (by rfl) ⟨2324031, by rfl⟩ : syracuseStep 6197417 = 4648063) B4648063
theorem B11768489 : Blo 1835619 11768489 := bstep (se 2 (by rfl) ⟨4413183, by rfl⟩ : syracuseStep 11768489 = 8826367) B8826367
theorem B4131611 : Blo 1835619 4131611 := bstep (se 1 (by rfl) ⟨3098708, by rfl⟩ : syracuseStep 4131611 = 6197417) B6197417
theorem B9923867 : Blo 1835619 9923867 := bstep (se 1 (by rfl) ⟨7442900, by rfl⟩ : syracuseStep 9923867 = 14885801) B14885801
theorem B26472815 : Blo 1835619 26472815 := bstep (se 1 (by rfl) ⟨19854611, by rfl⟩ : syracuseStep 26472815 = 39709223) B39709223
theorem B7845659 : Blo 1835619 7845659 := bstep (se 1 (by rfl) ⟨5884244, by rfl⟩ : syracuseStep 7845659 = 11768489) B11768489
theorem B2754407 : Blo 1835619 2754407 := bstep (se 1 (by rfl) ⟨2065805, by rfl⟩ : syracuseStep 2754407 = 4131611) B4131611
theorem B17648543 : Blo 1835619 17648543 := bstep (se 1 (by rfl) ⟨13236407, by rfl⟩ : syracuseStep 17648543 = 26472815) B26472815
theorem B5230439 : Blo 1835619 5230439 := bstep (se 1 (by rfl) ⟨3922829, by rfl⟩ : syracuseStep 5230439 = 7845659) B7845659
theorem B6615911 : Blo 1835619 6615911 := bstep (se 1 (by rfl) ⟨4961933, by rfl⟩ : syracuseStep 6615911 = 9923867) B9923867
theorem B1836271 : Blo 1835619 1836271 := bstep (se 1 (by rfl) ⟨1377203, by rfl⟩ : syracuseStep 1836271 = 2754407) B2754407
theorem B11765695 : Blo 1835619 11765695 := bstep (se 1 (by rfl) ⟨8824271, by rfl⟩ : syracuseStep 11765695 = 17648543) B17648543
theorem B4410607 : Blo 1835619 4410607 := bstep (se 1 (by rfl) ⟨3307955, by rfl⟩ : syracuseStep 4410607 = 6615911) B6615911
theorem B3486959 : Blo 1835619 3486959 := bstep (se 1 (by rfl) ⟨2615219, by rfl⟩ : syracuseStep 3486959 = 5230439) B5230439
theorem B2324639 : Blo 1835619 2324639 := bstep (se 1 (by rfl) ⟨1743479, by rfl⟩ : syracuseStep 2324639 = 3486959) B3486959
theorem B5880809 : Blo 1835619 5880809 := bstep (se 2 (by rfl) ⟨2205303, by rfl⟩ : syracuseStep 5880809 = 4410607) B4410607
theorem B15687593 : Blo 1835619 15687593 := bstep (se 2 (by rfl) ⟨5882847, by rfl⟩ : syracuseStep 15687593 = 11765695) B11765695
theorem B15682157 : Blo 1835619 15682157 := bstep (se 3 (by rfl) ⟨2940404, by rfl⟩ : syracuseStep 15682157 = 5880809) B5880809
theorem B10458395 : Blo 1835619 10458395 := bstep (se 1 (by rfl) ⟨7843796, by rfl⟩ : syracuseStep 10458395 = 15687593) B15687593
theorem B6199037 : Blo 1835619 6199037 := bstep (se 3 (by rfl) ⟨1162319, by rfl⟩ : syracuseStep 6199037 = 2324639) B2324639
theorem B6972263 : Blo 1835619 6972263 := bstep (se 1 (by rfl) ⟨5229197, by rfl⟩ : syracuseStep 6972263 = 10458395) B10458395
theorem B10454771 : Blo 1835619 10454771 := bstep (se 1 (by rfl) ⟨7841078, by rfl⟩ : syracuseStep 10454771 = 15682157) B15682157
theorem B4132691 : Blo 1835619 4132691 := bstep (se 1 (by rfl) ⟨3099518, by rfl⟩ : syracuseStep 4132691 = 6199037) B6199037
theorem B2755127 : Blo 1835619 2755127 := bstep (se 1 (by rfl) ⟨2066345, by rfl⟩ : syracuseStep 2755127 = 4132691) B4132691
theorem B4648175 : Blo 1835619 4648175 := bstep (se 1 (by rfl) ⟨3486131, by rfl⟩ : syracuseStep 4648175 = 6972263) B6972263
theorem B6969847 : Blo 1835619 6969847 := bstep (se 1 (by rfl) ⟨5227385, by rfl⟩ : syracuseStep 6969847 = 10454771) B10454771
theorem B1836751 : Blo 1835619 1836751 := bstep (se 1 (by rfl) ⟨1377563, by rfl⟩ : syracuseStep 1836751 = 2755127) B2755127
theorem B3098783 : Blo 1835619 3098783 := bstep (se 1 (by rfl) ⟨2324087, by rfl⟩ : syracuseStep 3098783 = 4648175) B4648175
theorem B9293129 : Blo 1835619 9293129 := bstep (se 2 (by rfl) ⟨3484923, by rfl⟩ : syracuseStep 9293129 = 6969847) B6969847
theorem B2065855 : Blo 1835619 2065855 := bstep (se 1 (by rfl) ⟨1549391, by rfl⟩ : syracuseStep 2065855 = 3098783) B3098783
theorem B6195419 : Blo 1835619 6195419 := bstep (se 1 (by rfl) ⟨4646564, by rfl⟩ : syracuseStep 6195419 = 9293129) B9293129
theorem B4130279 : Blo 1835619 4130279 := bstep (se 1 (by rfl) ⟨3097709, by rfl⟩ : syracuseStep 4130279 = 6195419) B6195419
theorem B2754473 : Blo 1835619 2754473 := bstep (se 2 (by rfl) ⟨1032927, by rfl⟩ : syracuseStep 2754473 = 2065855) B2065855
theorem B2753519 : Blo 1835619 2753519 := bstep (se 1 (by rfl) ⟨2065139, by rfl⟩ : syracuseStep 2753519 = 4130279) B4130279
theorem B1836315 : Blo 1835619 1836315 := bstep (se 1 (by rfl) ⟨1377236, by rfl⟩ : syracuseStep 1836315 = 2754473) B2754473
theorem B1835679 : Blo 1835619 1835679 := bstep (se 1 (by rfl) ⟨1376759, by rfl⟩ : syracuseStep 1835679 = 2753519) B2753519

theorem C0 (j : ℕ) (h1 : 458904 ≤ j) (h2 : j ≤ 459404) : Blo 1835619 (4 * j + 3) := by
  interval_cases j
  · exact B1835619
  · exact B1835623
  · exact B1835627
  · exact B1835631
  · exact B1835635
  · exact B1835639
  · exact B1835643
  · exact B1835647
  · exact B1835651
  · exact B1835655
  · exact B1835659
  · exact B1835663
  · exact B1835667
  · exact B1835671
  · exact B1835675
  · exact B1835679
  · exact B1835683
  · exact B1835687
  · exact B1835691
  · exact B1835695
  · exact B1835699
  · exact B1835703
  · exact B1835707
  · exact B1835711
  · exact B1835715
  · exact B1835719
  · exact B1835723
  · exact B1835727
  · exact B1835731
  · exact B1835735
  · exact B1835739
  · exact B1835743
  · exact B1835747
  · exact B1835751
  · exact B1835755
  · exact B1835759
  · exact B1835763
  · exact B1835767
  · exact B1835771
  · exact B1835775
  · exact B1835779
  · exact B1835783
  · exact B1835787
  · exact B1835791
  · exact B1835795
  · exact B1835799
  · exact B1835803
  · exact B1835807
  · exact B1835811
  · exact B1835815
  · exact B1835819
  · exact B1835823
  · exact B1835827
  · exact B1835831
  · exact B1835835
  · exact B1835839
  · exact B1835843
  · exact B1835847
  · exact B1835851
  · exact B1835855
  · exact B1835859
  · exact B1835863
  · exact B1835867
  · exact B1835871
  · exact B1835875
  · exact B1835879
  · exact B1835883
  · exact B1835887
  · exact B1835891
  · exact B1835895
  · exact B1835899
  · exact B1835903
  · exact B1835907
  · exact B1835911
  · exact B1835915
  · exact B1835919
  · exact B1835923
  · exact B1835927
  · exact B1835931
  · exact B1835935
  · exact B1835939
  · exact B1835943
  · exact B1835947
  · exact B1835951
  · exact B1835955
  · exact B1835959
  · exact B1835963
  · exact B1835967
  · exact B1835971
  · exact B1835975
  · exact B1835979
  · exact B1835983
  · exact B1835987
  · exact B1835991
  · exact B1835995
  · exact B1835999
  · exact B1836003
  · exact B1836007
  · exact B1836011
  · exact B1836015
  · exact B1836019
  · exact B1836023
  · exact B1836027
  · exact B1836031
  · exact B1836035
  · exact B1836039
  · exact B1836043
  · exact B1836047
  · exact B1836051
  · exact B1836055
  · exact B1836059
  · exact B1836063
  · exact B1836067
  · exact B1836071
  · exact B1836075
  · exact B1836079
  · exact B1836083
  · exact B1836087
  · exact B1836091
  · exact B1836095
  · exact B1836099
  · exact B1836103
  · exact B1836107
  · exact B1836111
  · exact B1836115
  · exact B1836119
  · exact B1836123
  · exact B1836127
  · exact B1836131
  · exact B1836135
  · exact B1836139
  · exact B1836143
  · exact B1836147
  · exact B1836151
  · exact B1836155
  · exact B1836159
  · exact B1836163
  · exact B1836167
  · exact B1836171
  · exact B1836175
  · exact B1836179
  · exact B1836183
  · exact B1836187
  · exact B1836191
  · exact B1836195
  · exact B1836199
  · exact B1836203
  · exact B1836207
  · exact B1836211
  · exact B1836215
  · exact B1836219
  · exact B1836223
  · exact B1836227
  · exact B1836231
  · exact B1836235
  · exact B1836239
  · exact B1836243
  · exact B1836247
  · exact B1836251
  · exact B1836255
  · exact B1836259
  · exact B1836263
  · exact B1836267
  · exact B1836271
  · exact B1836275
  · exact B1836279
  · exact B1836283
  · exact B1836287
  · exact B1836291
  · exact B1836295
  · exact B1836299
  · exact B1836303
  · exact B1836307
  · exact B1836311
  · exact B1836315
  · exact B1836319
  · exact B1836323
  · exact B1836327
  · exact B1836331
  · exact B1836335
  · exact B1836339
  · exact B1836343
  · exact B1836347
  · exact B1836351
  · exact B1836355
  · exact B1836359
  · exact B1836363
  · exact B1836367
  · exact B1836371
  · exact B1836375
  · exact B1836379
  · exact B1836383
  · exact B1836387
  · exact B1836391
  · exact B1836395
  · exact B1836399
  · exact B1836403
  · exact B1836407
  · exact B1836411
  · exact B1836415
  · exact B1836419
  · exact B1836423
  · exact B1836427
  · exact B1836431
  · exact B1836435
  · exact B1836439
  · exact B1836443
  · exact B1836447
  · exact B1836451
  · exact B1836455
  · exact B1836459
  · exact B1836463
  · exact B1836467
  · exact B1836471
  · exact B1836475
  · exact B1836479
  · exact B1836483
  · exact B1836487
  · exact B1836491
  · exact B1836495
  · exact B1836499
  · exact B1836503
  · exact B1836507
  · exact B1836511
  · exact B1836515
  · exact B1836519
  · exact B1836523
  · exact B1836527
  · exact B1836531
  · exact B1836535
  · exact B1836539
  · exact B1836543
  · exact B1836547
  · exact B1836551
  · exact B1836555
  · exact B1836559
  · exact B1836563
  · exact B1836567
  · exact B1836571
  · exact B1836575
  · exact B1836579
  · exact B1836583
  · exact B1836587
  · exact B1836591
  · exact B1836595
  · exact B1836599
  · exact B1836603
  · exact B1836607
  · exact B1836611
  · exact B1836615
  · exact B1836619
  · exact B1836623
  · exact B1836627
  · exact B1836631
  · exact B1836635
  · exact B1836639
  · exact B1836643
  · exact B1836647
  · exact B1836651
  · exact B1836655
  · exact B1836659
  · exact B1836663
  · exact B1836667
  · exact B1836671
  · exact B1836675
  · exact B1836679
  · exact B1836683
  · exact B1836687
  · exact B1836691
  · exact B1836695
  · exact B1836699
  · exact B1836703
  · exact B1836707
  · exact B1836711
  · exact B1836715
  · exact B1836719
  · exact B1836723
  · exact B1836727
  · exact B1836731
  · exact B1836735
  · exact B1836739
  · exact B1836743
  · exact B1836747
  · exact B1836751
  · exact B1836755
  · exact B1836759
  · exact B1836763
  · exact B1836767
  · exact B1836771
  · exact B1836775
  · exact B1836779
  · exact B1836783
  · exact B1836787
  · exact B1836791
  · exact B1836795
  · exact B1836799
  · exact B1836803
  · exact B1836807
  · exact B1836811
  · exact B1836815
  · exact B1836819
  · exact B1836823
  · exact B1836827
  · exact B1836831
  · exact B1836835
  · exact B1836839
  · exact B1836843
  · exact B1836847
  · exact B1836851
  · exact B1836855
  · exact B1836859
  · exact B1836863
  · exact B1836867
  · exact B1836871
  · exact B1836875
  · exact B1836879
  · exact B1836883
  · exact B1836887
  · exact B1836891
  · exact B1836895
  · exact B1836899
  · exact B1836903
  · exact B1836907
  · exact B1836911
  · exact B1836915
  · exact B1836919
  · exact B1836923
  · exact B1836927
  · exact B1836931
  · exact B1836935
  · exact B1836939
  · exact B1836943
  · exact B1836947
  · exact B1836951
  · exact B1836955
  · exact B1836959
  · exact B1836963
  · exact B1836967
  · exact B1836971
  · exact B1836975
  · exact B1836979
  · exact B1836983
  · exact B1836987
  · exact B1836991
  · exact B1836995
  · exact B1836999
  · exact B1837003
  · exact B1837007
  · exact B1837011
  · exact B1837015
  · exact B1837019
  · exact B1837023
  · exact B1837027
  · exact B1837031
  · exact B1837035
  · exact B1837039
  · exact B1837043
  · exact B1837047
  · exact B1837051
  · exact B1837055
  · exact B1837059
  · exact B1837063
  · exact B1837067
  · exact B1837071
  · exact B1837075
  · exact B1837079
  · exact B1837083
  · exact B1837087
  · exact B1837091
  · exact B1837095
  · exact B1837099
  · exact B1837103
  · exact B1837107
  · exact B1837111
  · exact B1837115
  · exact B1837119
  · exact B1837123
  · exact B1837127
  · exact B1837131
  · exact B1837135
  · exact B1837139
  · exact B1837143
  · exact B1837147
  · exact B1837151
  · exact B1837155
  · exact B1837159
  · exact B1837163
  · exact B1837167
  · exact B1837171
  · exact B1837175
  · exact B1837179
  · exact B1837183
  · exact B1837187
  · exact B1837191
  · exact B1837195
  · exact B1837199
  · exact B1837203
  · exact B1837207
  · exact B1837211
  · exact B1837215
  · exact B1837219
  · exact B1837223
  · exact B1837227
  · exact B1837231
  · exact B1837235
  · exact B1837239
  · exact B1837243
  · exact B1837247
  · exact B1837251
  · exact B1837255
  · exact B1837259
  · exact B1837263
  · exact B1837267
  · exact B1837271
  · exact B1837275
  · exact B1837279
  · exact B1837283
  · exact B1837287
  · exact B1837291
  · exact B1837295
  · exact B1837299
  · exact B1837303
  · exact B1837307
  · exact B1837311
  · exact B1837315
  · exact B1837319
  · exact B1837323
  · exact B1837327
  · exact B1837331
  · exact B1837335
  · exact B1837339
  · exact B1837343
  · exact B1837347
  · exact B1837351
  · exact B1837355
  · exact B1837359
  · exact B1837363
  · exact B1837367
  · exact B1837371
  · exact B1837375
  · exact B1837379
  · exact B1837383
  · exact B1837387
  · exact B1837391
  · exact B1837395
  · exact B1837399
  · exact B1837403
  · exact B1837407
  · exact B1837411
  · exact B1837415
  · exact B1837419
  · exact B1837423
  · exact B1837427
  · exact B1837431
  · exact B1837435
  · exact B1837439
  · exact B1837443
  · exact B1837447
  · exact B1837451
  · exact B1837455
  · exact B1837459
  · exact B1837463
  · exact B1837467
  · exact B1837471
  · exact B1837475
  · exact B1837479
  · exact B1837483
  · exact B1837487
  · exact B1837491
  · exact B1837495
  · exact B1837499
  · exact B1837503
  · exact B1837507
  · exact B1837511
  · exact B1837515
  · exact B1837519
  · exact B1837523
  · exact B1837527
  · exact B1837531
  · exact B1837535
  · exact B1837539
  · exact B1837543
  · exact B1837547
  · exact B1837551
  · exact B1837555
  · exact B1837559
  · exact B1837563
  · exact B1837567
  · exact B1837571
  · exact B1837575
  · exact B1837579
  · exact B1837583
  · exact B1837587
  · exact B1837591
  · exact B1837595
  · exact B1837599
  · exact B1837603
  · exact B1837607
  · exact B1837611
  · exact B1837615
  · exact B1837619

theorem solution (m : ℕ) (hlo : 1835619 ≤ m) (hhi : m ≤ 1837619) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 458904 ≤ j := by omega
    have hj2 : j ≤ 459404 := by omega
    have hb : Blo 1835619 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
