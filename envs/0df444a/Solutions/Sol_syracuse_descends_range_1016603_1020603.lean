-- Prove2me | solution 1 for syracuse_descends_range_1016603_1020603
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:19.196962+00:00
-- url     : https://prove2.me/submissions/63b6b13e-f725-49b2-b784-874ed29ad9b7

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


theorem B1769485 : Blo 1016603 1769485 := bbase (se 3 (by rfl) ⟨331778, by rfl⟩ : syracuseStep 1769485 = 663557) (by norm_num)
theorem B1146901 : Blo 1016603 1146901 := bbase (se 6 (by rfl) ⟨26880, by rfl⟩ : syracuseStep 1146901 = 53761) (by norm_num)
theorem B1146937 : Blo 1016603 1146937 := bbase (se 2 (by rfl) ⟨430101, by rfl⟩ : syracuseStep 1146937 = 860203) (by norm_num)
theorem B2293829 : Blo 1016603 2293829 := bbase (se 4 (by rfl) ⟨215046, by rfl⟩ : syracuseStep 2293829 = 430093) (by norm_num)
theorem B1146973 : Blo 1016603 1146973 := bbase (se 3 (by rfl) ⟨215057, by rfl⟩ : syracuseStep 1146973 = 430115) (by norm_num)
theorem B1147009 : Blo 1016603 1147009 := bbase (se 2 (by rfl) ⟨430128, by rfl⟩ : syracuseStep 1147009 = 860257) (by norm_num)
theorem B1933445 : Blo 1016603 1933445 := bbase (se 4 (by rfl) ⟨181260, by rfl⟩ : syracuseStep 1933445 = 362521) (by norm_num)
theorem B2293901 : Blo 1016603 2293901 := bbase (se 3 (by rfl) ⟨430106, by rfl⟩ : syracuseStep 2293901 = 860213) (by norm_num)
theorem B5800085 : Blo 1016603 5800085 := bbase (se 6 (by rfl) ⟨135939, by rfl⟩ : syracuseStep 5800085 = 271879) (by norm_num)
theorem B3670181 : Blo 1016603 3670181 := bbase (se 4 (by rfl) ⟨344079, by rfl⟩ : syracuseStep 3670181 = 688159) (by norm_num)
theorem B1147045 : Blo 1016603 1147045 := bbase (se 4 (by rfl) ⟨107535, by rfl⟩ : syracuseStep 1147045 = 215071) (by norm_num)
theorem B1147081 : Blo 1016603 1147081 := bbase (se 2 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 1147081 = 860311) (by norm_num)
theorem B2293973 : Blo 1016603 2293973 := bbase (se 7 (by rfl) ⟨26882, by rfl⟩ : syracuseStep 2293973 = 53765) (by norm_num)
theorem B1147117 : Blo 1016603 1147117 := bbase (se 3 (by rfl) ⟨215084, by rfl⟩ : syracuseStep 1147117 = 430169) (by norm_num)
theorem B1147153 : Blo 1016603 1147153 := bbase (se 2 (by rfl) ⟨430182, by rfl⟩ : syracuseStep 1147153 = 860365) (by norm_num)
theorem B2294045 : Blo 1016603 2294045 := bbase (se 3 (by rfl) ⟨430133, by rfl⟩ : syracuseStep 2294045 = 860267) (by norm_num)
theorem B3440933 : Blo 1016603 3440933 := bbase (se 4 (by rfl) ⟨322587, by rfl⟩ : syracuseStep 3440933 = 645175) (by norm_num)
theorem B1147189 : Blo 1016603 1147189 := bbase (se 5 (by rfl) ⟨53774, by rfl⟩ : syracuseStep 1147189 = 107549) (by norm_num)
theorem B1147225 : Blo 1016603 1147225 := bbase (se 2 (by rfl) ⟨430209, by rfl⟩ : syracuseStep 1147225 = 860419) (by norm_num)
theorem B2294117 : Blo 1016603 2294117 := bbase (se 4 (by rfl) ⟨215073, by rfl⟩ : syracuseStep 2294117 = 430147) (by norm_num)
theorem B1147261 : Blo 1016603 1147261 := bbase (se 3 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 1147261 = 430223) (by norm_num)
theorem B1147297 : Blo 1016603 1147297 := bbase (se 2 (by rfl) ⟨430236, by rfl⟩ : syracuseStep 1147297 = 860473) (by norm_num)
theorem B1933733 : Blo 1016603 1933733 := bbase (se 4 (by rfl) ⟨181287, by rfl⟩ : syracuseStep 1933733 = 362575) (by norm_num)
theorem B2294189 : Blo 1016603 2294189 := bbase (se 3 (by rfl) ⟨430160, by rfl⟩ : syracuseStep 2294189 = 860321) (by norm_num)
theorem B1147333 : Blo 1016603 1147333 := bbase (se 4 (by rfl) ⟨107562, by rfl⟩ : syracuseStep 1147333 = 215125) (by norm_num)
theorem B7733717 : Blo 1016603 7733717 := bbase (se 7 (by rfl) ⟨90629, by rfl⟩ : syracuseStep 7733717 = 181259) (by norm_num)
theorem B1147369 : Blo 1016603 1147369 := bbase (se 2 (by rfl) ⟨430263, by rfl⟩ : syracuseStep 1147369 = 860527) (by norm_num)
theorem B2294261 : Blo 1016603 2294261 := bbase (se 5 (by rfl) ⟨107543, by rfl⟩ : syracuseStep 2294261 = 215087) (by norm_num)
theorem B1147405 : Blo 1016603 1147405 := bbase (se 3 (by rfl) ⟨215138, by rfl⟩ : syracuseStep 1147405 = 430277) (by norm_num)
theorem B2753045 : Blo 1016603 2753045 := bbase (se 6 (by rfl) ⟨64524, by rfl⟩ : syracuseStep 2753045 = 129049) (by norm_num)
theorem B1147441 : Blo 1016603 1147441 := bbase (se 2 (by rfl) ⟨430290, by rfl⟩ : syracuseStep 1147441 = 860581) (by norm_num)
theorem B9306677 : Blo 1016603 9306677 := bbase (se 5 (by rfl) ⟨436250, by rfl⟩ : syracuseStep 9306677 = 872501) (by norm_num)
theorem B1933885 : Blo 1016603 1933885 := bbase (se 3 (by rfl) ⟨362603, by rfl⟩ : syracuseStep 1933885 = 725207) (by norm_num)
theorem B2294333 : Blo 1016603 2294333 := bbase (se 3 (by rfl) ⟨430187, by rfl⟩ : syracuseStep 2294333 = 860375) (by norm_num)
theorem B1147477 : Blo 1016603 1147477 := bbase (se 8 (by rfl) ⟨6723, by rfl⟩ : syracuseStep 1147477 = 13447) (by norm_num)
theorem B1147513 : Blo 1016603 1147513 := bbase (se 2 (by rfl) ⟨430317, by rfl⟩ : syracuseStep 1147513 = 860635) (by norm_num)
theorem B2294405 : Blo 1016603 2294405 := bbase (se 4 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 2294405 = 430201) (by norm_num)
theorem B1147549 : Blo 1016603 1147549 := bbase (se 3 (by rfl) ⟨215165, by rfl⟩ : syracuseStep 1147549 = 430331) (by norm_num)
theorem B1147585 : Blo 1016603 1147585 := bbase (se 2 (by rfl) ⟨430344, by rfl⟩ : syracuseStep 1147585 = 860689) (by norm_num)
theorem B1835725 : Blo 1016603 1835725 := bbase (se 3 (by rfl) ⟨344198, by rfl⟩ : syracuseStep 1835725 = 688397) (by norm_num)
theorem B2294477 : Blo 1016603 2294477 := bbase (se 3 (by rfl) ⟨430214, by rfl⟩ : syracuseStep 2294477 = 860429) (by norm_num)
theorem B3441365 : Blo 1016603 3441365 := bbase (se 7 (by rfl) ⟨40328, by rfl⟩ : syracuseStep 3441365 = 80657) (by norm_num)
theorem B1147621 : Blo 1016603 1147621 := bbase (se 4 (by rfl) ⟨107589, by rfl⟩ : syracuseStep 1147621 = 215179) (by norm_num)
theorem B1147657 : Blo 1016603 1147657 := bbase (se 2 (by rfl) ⟨430371, by rfl⟩ : syracuseStep 1147657 = 860743) (by norm_num)
theorem B1835797 : Blo 1016603 1835797 := bbase (se 6 (by rfl) ⟨43026, by rfl⟩ : syracuseStep 1835797 = 86053) (by norm_num)
theorem B2294549 : Blo 1016603 2294549 := bbase (se 6 (by rfl) ⟨53778, by rfl⟩ : syracuseStep 2294549 = 107557) (by norm_num)
theorem B1147693 : Blo 1016603 1147693 := bbase (se 3 (by rfl) ⟨215192, by rfl⟩ : syracuseStep 1147693 = 430385) (by norm_num)
theorem B1377085 : Blo 1016603 1377085 := bbase (se 3 (by rfl) ⟨258203, by rfl⟩ : syracuseStep 1377085 = 516407) (by norm_num)
theorem B1147729 : Blo 1016603 1147729 := bbase (se 2 (by rfl) ⟨430398, by rfl⟩ : syracuseStep 1147729 = 860797) (by norm_num)
theorem B2294621 : Blo 1016603 2294621 := bbase (se 3 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 2294621 = 860483) (by norm_num)
theorem B1934189 : Blo 1016603 1934189 := bbase (se 3 (by rfl) ⟨362660, by rfl⟩ : syracuseStep 1934189 = 725321) (by norm_num)
theorem B1147765 : Blo 1016603 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B1147801 : Blo 1016603 1147801 := bbase (se 2 (by rfl) ⟨430425, by rfl⟩ : syracuseStep 1147801 = 860851) (by norm_num)
theorem B2294693 : Blo 1016603 2294693 := bbase (se 4 (by rfl) ⟨215127, by rfl⟩ : syracuseStep 2294693 = 430255) (by norm_num)
theorem B1147837 : Blo 1016603 1147837 := bbase (se 3 (by rfl) ⟨215219, by rfl⟩ : syracuseStep 1147837 = 430439) (by norm_num)
theorem B1147873 : Blo 1016603 1147873 := bbase (se 2 (by rfl) ⟨430452, by rfl⟩ : syracuseStep 1147873 = 860905) (by norm_num)
theorem B1377253 : Blo 1016603 1377253 := bbase (se 4 (by rfl) ⟨129117, by rfl⟩ : syracuseStep 1377253 = 258235) (by norm_num)
theorem B2294765 : Blo 1016603 2294765 := bbase (se 3 (by rfl) ⟨430268, by rfl⟩ : syracuseStep 2294765 = 860537) (by norm_num)
theorem B1147909 : Blo 1016603 1147909 := bbase (se 4 (by rfl) ⟨107616, by rfl⟩ : syracuseStep 1147909 = 215233) (by norm_num)
theorem B1147945 : Blo 1016603 1147945 := bbase (se 2 (by rfl) ⟨430479, by rfl⟩ : syracuseStep 1147945 = 860959) (by norm_num)
theorem B2294837 : Blo 1016603 2294837 := bbase (se 5 (by rfl) ⟨107570, by rfl⟩ : syracuseStep 2294837 = 215141) (by norm_num)
theorem B1147981 : Blo 1016603 1147981 := bbase (se 3 (by rfl) ⟨215246, by rfl⟩ : syracuseStep 1147981 = 430493) (by norm_num)
theorem B1148017 : Blo 1016603 1148017 := bbase (se 2 (by rfl) ⟨430506, by rfl⟩ : syracuseStep 1148017 = 861013) (by norm_num)
theorem B2294909 : Blo 1016603 2294909 := bbase (se 3 (by rfl) ⟨430295, by rfl⟩ : syracuseStep 2294909 = 860591) (by norm_num)
theorem B3441797 : Blo 1016603 3441797 := bbase (se 4 (by rfl) ⟨322668, by rfl⟩ : syracuseStep 3441797 = 645337) (by norm_num)
theorem B1148053 : Blo 1016603 1148053 := bbase (se 6 (by rfl) ⟨26907, by rfl⟩ : syracuseStep 1148053 = 53815) (by norm_num)
theorem B1148089 : Blo 1016603 1148089 := bbase (se 2 (by rfl) ⟨430533, by rfl⟩ : syracuseStep 1148089 = 861067) (by norm_num)
theorem B2294981 : Blo 1016603 2294981 := bbase (se 4 (by rfl) ⟨215154, by rfl⟩ : syracuseStep 2294981 = 430309) (by norm_num)
theorem B1148125 : Blo 1016603 1148125 := bbase (se 3 (by rfl) ⟨215273, by rfl⟩ : syracuseStep 1148125 = 430547) (by norm_num)
theorem B1148161 : Blo 1016603 1148161 := bbase (se 2 (by rfl) ⟨430560, by rfl⟩ : syracuseStep 1148161 = 861121) (by norm_num)
theorem B2295053 : Blo 1016603 2295053 := bbase (se 3 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 2295053 = 860645) (by norm_num)
theorem B2295125 : Blo 1016603 2295125 := bbase (se 12 (by rfl) ⟨840, by rfl⟩ : syracuseStep 2295125 = 1681) (by norm_num)
theorem B2295197 : Blo 1016603 2295197 := bbase (se 3 (by rfl) ⟨430349, by rfl⟩ : syracuseStep 2295197 = 860699) (by norm_num)
theorem B2295269 : Blo 1016603 2295269 := bbase (se 4 (by rfl) ⟨215181, by rfl⟩ : syracuseStep 2295269 = 430363) (by norm_num)
theorem B3868181 : Blo 1016603 3868181 := bbase (se 6 (by rfl) ⟨90660, by rfl⟩ : syracuseStep 3868181 = 181321) (by norm_num)
theorem B2295341 : Blo 1016603 2295341 := bbase (se 3 (by rfl) ⟨430376, by rfl⟩ : syracuseStep 2295341 = 860753) (by norm_num)
theorem B3442229 : Blo 1016603 3442229 := bbase (se 5 (by rfl) ⟨161354, by rfl⟩ : syracuseStep 3442229 = 322709) (by norm_num)
theorem B1934941 : Blo 1016603 1934941 := bbase (se 3 (by rfl) ⟨362801, by rfl⟩ : syracuseStep 1934941 = 725603) (by norm_num)
theorem B2295413 : Blo 1016603 2295413 := bbase (se 5 (by rfl) ⟨107597, by rfl⟩ : syracuseStep 2295413 = 215195) (by norm_num)
theorem B2295485 : Blo 1016603 2295485 := bbase (se 3 (by rfl) ⟨430403, by rfl⟩ : syracuseStep 2295485 = 860807) (by norm_num)
theorem B1935085 : Blo 1016603 1935085 := bbase (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) (by norm_num)
theorem B1836805 : Blo 1016603 1836805 := bbase (se 4 (by rfl) ⟨172200, by rfl⟩ : syracuseStep 1836805 = 344401) (by norm_num)
theorem B2295557 : Blo 1016603 2295557 := bbase (se 4 (by rfl) ⟨215208, by rfl⟩ : syracuseStep 2295557 = 430417) (by norm_num)
theorem B3868469 : Blo 1016603 3868469 := bbase (se 5 (by rfl) ⟨181334, by rfl⟩ : syracuseStep 3868469 = 362669) (by norm_num)
theorem B2295629 : Blo 1016603 2295629 := bbase (se 3 (by rfl) ⟨430430, by rfl⟩ : syracuseStep 2295629 = 860861) (by norm_num)
theorem B1836893 : Blo 1016603 1836893 := bbase (se 3 (by rfl) ⟨344417, by rfl⟩ : syracuseStep 1836893 = 688835) (by norm_num)
theorem B1935245 : Blo 1016603 1935245 := bbase (se 3 (by rfl) ⟨362858, by rfl⟩ : syracuseStep 1935245 = 725717) (by norm_num)
theorem B2295701 : Blo 1016603 2295701 := bbase (se 6 (by rfl) ⟨53805, by rfl⟩ : syracuseStep 2295701 = 107611) (by norm_num)
theorem B2295773 : Blo 1016603 2295773 := bbase (se 3 (by rfl) ⟨430457, by rfl⟩ : syracuseStep 2295773 = 860915) (by norm_num)
theorem B3442661 : Blo 1016603 3442661 := bbase (se 4 (by rfl) ⟨322749, by rfl⟩ : syracuseStep 3442661 = 645499) (by norm_num)
theorem B1935389 : Blo 1016603 1935389 := bbase (se 3 (by rfl) ⟨362885, by rfl⟩ : syracuseStep 1935389 = 725771) (by norm_num)
theorem B2295845 : Blo 1016603 2295845 := bbase (se 4 (by rfl) ⟨215235, by rfl⟩ : syracuseStep 2295845 = 430471) (by norm_num)
theorem B2295917 : Blo 1016603 2295917 := bbase (se 3 (by rfl) ⟨430484, by rfl⟩ : syracuseStep 2295917 = 860969) (by norm_num)
theorem B1837181 : Blo 1016603 1837181 := bbase (se 3 (by rfl) ⟨344471, by rfl⟩ : syracuseStep 1837181 = 688943) (by norm_num)
theorem B1378469 : Blo 1016603 1378469 := bbase (se 4 (by rfl) ⟨129231, by rfl⟩ : syracuseStep 1378469 = 258463) (by norm_num)
theorem B2295989 : Blo 1016603 2295989 := bbase (se 5 (by rfl) ⟨107624, by rfl⟩ : syracuseStep 2295989 = 215249) (by norm_num)
theorem B2296061 : Blo 1016603 2296061 := bbase (se 3 (by rfl) ⟨430511, by rfl⟩ : syracuseStep 2296061 = 861023) (by norm_num)
theorem B5146901 : Blo 1016603 5146901 := bbase (se 6 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 5146901 = 241261) (by norm_num)
theorem B5802293 : Blo 1016603 5802293 := bbase (se 5 (by rfl) ⟨271982, by rfl⟩ : syracuseStep 5802293 = 543965) (by norm_num)
theorem B1935677 : Blo 1016603 1935677 := bbase (se 3 (by rfl) ⟨362939, by rfl⟩ : syracuseStep 1935677 = 725879) (by norm_num)
theorem B2296133 : Blo 1016603 2296133 := bbase (se 4 (by rfl) ⟨215262, by rfl⟩ : syracuseStep 2296133 = 430525) (by norm_num)
theorem B1837397 : Blo 1016603 1837397 := bbase (se 10 (by rfl) ⟨2691, by rfl⟩ : syracuseStep 1837397 = 5383) (by norm_num)
theorem B6523253 : Blo 1016603 6523253 := bbase (se 5 (by rfl) ⟨305777, by rfl⟩ : syracuseStep 6523253 = 611555) (by norm_num)
theorem B2296205 : Blo 1016603 2296205 := bbase (se 3 (by rfl) ⟨430538, by rfl⟩ : syracuseStep 2296205 = 861077) (by norm_num)
theorem B3443093 : Blo 1016603 3443093 := bbase (se 6 (by rfl) ⟨80697, by rfl⟩ : syracuseStep 3443093 = 161395) (by norm_num)
theorem B1935829 : Blo 1016603 1935829 := bbase (se 7 (by rfl) ⟨22685, by rfl⟩ : syracuseStep 1935829 = 45371) (by norm_num)
theorem B2296277 : Blo 1016603 2296277 := bbase (se 7 (by rfl) ⟨26909, by rfl⟩ : syracuseStep 2296277 = 53819) (by norm_num)
theorem B2296349 : Blo 1016603 2296349 := bbase (se 3 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 2296349 = 861131) (by norm_num)
theorem B1936133 : Blo 1016603 1936133 := bbase (se 4 (by rfl) ⟨181512, by rfl⟩ : syracuseStep 1936133 = 363025) (by norm_num)
theorem B3443525 : Blo 1016603 3443525 := bbase (se 4 (by rfl) ⟨322830, by rfl⟩ : syracuseStep 3443525 = 645661) (by norm_num)
theorem B3869653 : Blo 1016603 3869653 := bbase (se 7 (by rfl) ⟨45347, by rfl⟩ : syracuseStep 3869653 = 90695) (by norm_num)
theorem B3443957 : Blo 1016603 3443957 := bbase (se 5 (by rfl) ⟨161435, by rfl⟩ : syracuseStep 3443957 = 322871) (by norm_num)
theorem B1838333 : Blo 1016603 1838333 := bbase (se 3 (by rfl) ⟨344687, by rfl⟩ : syracuseStep 1838333 = 689375) (by norm_num)
theorem B3869957 : Blo 1016603 3869957 := bbase (se 4 (by rfl) ⟨362808, by rfl⟩ : syracuseStep 3869957 = 725617) (by norm_num)
theorem B1838413 : Blo 1016603 1838413 := bbase (se 3 (by rfl) ⟨344702, by rfl⟩ : syracuseStep 1838413 = 689405) (by norm_num)
theorem B1936885 : Blo 1016603 1936885 := bbase (se 5 (by rfl) ⟨90791, by rfl⟩ : syracuseStep 1936885 = 181583) (by norm_num)
theorem B5148197 : Blo 1016603 5148197 := bbase (se 4 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 5148197 = 965287) (by norm_num)
theorem B1937029 : Blo 1016603 1937029 := bbase (se 4 (by rfl) ⟨181596, by rfl⟩ : syracuseStep 1937029 = 363193) (by norm_num)
theorem B3444389 : Blo 1016603 3444389 := bbase (se 4 (by rfl) ⟨322911, by rfl⟩ : syracuseStep 3444389 = 645823) (by norm_num)
theorem B1937189 : Blo 1016603 1937189 := bbase (se 4 (by rfl) ⟨181611, by rfl⟩ : syracuseStep 1937189 = 363223) (by norm_num)
theorem B1740629 : Blo 1016603 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1740677 : Blo 1016603 1740677 := bbase (se 4 (by rfl) ⟨163188, by rfl⟩ : syracuseStep 1740677 = 326377) (by norm_num)
theorem B1937333 : Blo 1016603 1937333 := bbase (se 5 (by rfl) ⟨90812, by rfl⟩ : syracuseStep 1937333 = 181625) (by norm_num)
theorem B5509205 : Blo 1016603 5509205 := bbase (se 8 (by rfl) ⟨32280, by rfl⟩ : syracuseStep 5509205 = 64561) (by norm_num)
theorem B4526293 : Blo 1016603 4526293 := bbase (se 7 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 4526293 = 106085) (by norm_num)
theorem B1085897 : Blo 1016603 1085897 := bbase (se 2 (by rfl) ⟨407211, by rfl⟩ : syracuseStep 1085897 = 814423) (by norm_num)
theorem B19599893 : Blo 1016603 19599893 := bbase (se 6 (by rfl) ⟨459372, by rfl⟩ : syracuseStep 19599893 = 918745) (by norm_num)
theorem B1086085 : Blo 1016603 1086085 := bbase (se 4 (by rfl) ⟨101820, by rfl⟩ : syracuseStep 1086085 = 203641) (by norm_num)
theorem B3674821 : Blo 1016603 3674821 := bbase (se 4 (by rfl) ⟨344514, by rfl⟩ : syracuseStep 3674821 = 689029) (by norm_num)
theorem B5149493 : Blo 1016603 5149493 := bbase (se 5 (by rfl) ⟨241382, by rfl⟩ : syracuseStep 5149493 = 482765) (by norm_num)
theorem B3872069 : Blo 1016603 3872069 := bbase (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) (by norm_num)
theorem B1086905 : Blo 1016603 1086905 := bbase (se 2 (by rfl) ⟨407589, by rfl⟩ : syracuseStep 1086905 = 815179) (by norm_num)
theorem B6526453 : Blo 1016603 6526453 := bbase (se 5 (by rfl) ⟨305927, by rfl⟩ : syracuseStep 6526453 = 611855) (by norm_num)
theorem B1742429 : Blo 1016603 1742429 := bbase (se 3 (by rfl) ⟨326705, by rfl⟩ : syracuseStep 1742429 = 653411) (by norm_num)
theorem B3872357 : Blo 1016603 3872357 := bbase (se 4 (by rfl) ⟨363033, by rfl⟩ : syracuseStep 3872357 = 726067) (by norm_num)
theorem B1447589 : Blo 1016603 1447589 := bbase (se 4 (by rfl) ⟨135711, by rfl⟩ : syracuseStep 1447589 = 271423) (by norm_num)
theorem B1447669 : Blo 1016603 1447669 := bbase (se 5 (by rfl) ⟨67859, by rfl⟩ : syracuseStep 1447669 = 135719) (by norm_num)
theorem B5510933 : Blo 1016603 5510933 := bbase (se 6 (by rfl) ⟨129162, by rfl⟩ : syracuseStep 5510933 = 258325) (by norm_num)
theorem B1447789 : Blo 1016603 1447789 := bbase (se 3 (by rfl) ⟨271460, by rfl⟩ : syracuseStep 1447789 = 542921) (by norm_num)
theorem B1087349 : Blo 1016603 1087349 := bbase (se 5 (by rfl) ⟨50969, by rfl⟩ : syracuseStep 1087349 = 101939) (by norm_num)
theorem B1447885 : Blo 1016603 1447885 := bbase (se 3 (by rfl) ⟨271478, by rfl⟩ : syracuseStep 1447885 = 542957) (by norm_num)
theorem B4888613 : Blo 1016603 4888613 := bbase (se 4 (by rfl) ⟨458307, by rfl⟩ : syracuseStep 4888613 = 916615) (by norm_num)
theorem B5150789 : Blo 1016603 5150789 := bbase (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) (by norm_num)
theorem B1087597 : Blo 1016603 1087597 := bbase (se 3 (by rfl) ⟨203924, by rfl⟩ : syracuseStep 1087597 = 407849) (by norm_num)
theorem B1743229 : Blo 1016603 1743229 := bbase (se 3 (by rfl) ⟨326855, by rfl⟩ : syracuseStep 1743229 = 653711) (by norm_num)
theorem B1448381 : Blo 1016603 1448381 := bbase (se 3 (by rfl) ⟨271571, by rfl⟩ : syracuseStep 1448381 = 543143) (by norm_num)
theorem B1088029 : Blo 1016603 1088029 := bbase (se 3 (by rfl) ⟨204005, by rfl⟩ : syracuseStep 1088029 = 408011) (by norm_num)
theorem B1546813 : Blo 1016603 1546813 := bbase (se 3 (by rfl) ⟨290027, by rfl⟩ : syracuseStep 1546813 = 580055) (by norm_num)
theorem B1088101 : Blo 1016603 1088101 := bbase (se 4 (by rfl) ⟨102009, by rfl⟩ : syracuseStep 1088101 = 204019) (by norm_num)
theorem B10459829 : Blo 1016603 10459829 := bbase (se 5 (by rfl) ⟨490304, by rfl⟩ : syracuseStep 10459829 = 980609) (by norm_num)
theorem B11901653 : Blo 1016603 11901653 := bbase (se 7 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 11901653 = 278945) (by norm_num)
theorem B3873541 : Blo 1016603 3873541 := bbase (se 4 (by rfl) ⟨363144, by rfl⟩ : syracuseStep 3873541 = 726289) (by norm_num)
theorem B1088473 : Blo 1016603 1088473 := bbase (se 2 (by rfl) ⟨408177, by rfl⟩ : syracuseStep 1088473 = 816355) (by norm_num)
theorem B1448933 : Blo 1016603 1448933 := bbase (se 4 (by rfl) ⟨135837, by rfl⟩ : syracuseStep 1448933 = 271675) (by norm_num)
theorem B4135925 : Blo 1016603 4135925 := bbase (se 5 (by rfl) ⟨193871, by rfl⟩ : syracuseStep 4135925 = 387743) (by norm_num)
theorem B3873845 : Blo 1016603 3873845 := bbase (se 5 (by rfl) ⟨181586, by rfl⟩ : syracuseStep 3873845 = 363173) (by norm_num)
theorem B1088849 : Blo 1016603 1088849 := bbase (se 2 (by rfl) ⟨408318, by rfl⟩ : syracuseStep 1088849 = 816637) (by norm_num)
theorem B5152085 : Blo 1016603 5152085 := bbase (se 11 (by rfl) ⟨3773, by rfl⟩ : syracuseStep 5152085 = 7547) (by norm_num)
theorem B1088921 : Blo 1016603 1088921 := bbase (se 2 (by rfl) ⟨408345, by rfl⟩ : syracuseStep 1088921 = 816691) (by norm_num)
theorem B7347797 : Blo 1016603 7347797 := bbase (se 8 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 7347797 = 86107) (by norm_num)
theorem B1089109 : Blo 1016603 1089109 := bbase (se 8 (by rfl) ⟨6381, by rfl⟩ : syracuseStep 1089109 = 12763) (by norm_num)
theorem B1449685 : Blo 1016603 1449685 := bbase (se 7 (by rfl) ⟨16988, by rfl⟩ : syracuseStep 1449685 = 33977) (by norm_num)
theorem B1089293 : Blo 1016603 1089293 := bbase (se 3 (by rfl) ⟨204242, by rfl⟩ : syracuseStep 1089293 = 408485) (by norm_num)
theorem B7741493 : Blo 1016603 7741493 := bbase (se 5 (by rfl) ⟨362882, by rfl⟩ : syracuseStep 7741493 = 725765) (by norm_num)
theorem B2171213 : Blo 1016603 2171213 := bbase (se 3 (by rfl) ⟨407102, by rfl⟩ : syracuseStep 2171213 = 814205) (by norm_num)
theorem B1450477 : Blo 1016603 1450477 := bbase (se 3 (by rfl) ⟨271964, by rfl⟩ : syracuseStep 1450477 = 543929) (by norm_num)
theorem B1286705 : Blo 1016603 1286705 := bbase (se 2 (by rfl) ⟨482514, by rfl⟩ : syracuseStep 1286705 = 965029) (by norm_num)
theorem B27927125 : Blo 1016603 27927125 := bbase (se 8 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 27927125 = 327271) (by norm_num)
theorem B5153381 : Blo 1016603 5153381 := bbase (se 4 (by rfl) ⟨483129, by rfl⟩ : syracuseStep 5153381 = 966259) (by norm_num)
theorem B1286761 : Blo 1016603 1286761 := bbase (se 2 (by rfl) ⟨482535, by rfl⟩ : syracuseStep 1286761 = 965071) (by norm_num)
theorem B1548941 : Blo 1016603 1548941 := bbase (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) (by norm_num)
theorem B1286857 : Blo 1016603 1286857 := bbase (se 2 (by rfl) ⟨482571, by rfl⟩ : syracuseStep 1286857 = 965143) (by norm_num)
theorem B1450813 : Blo 1016603 1450813 := bbase (se 3 (by rfl) ⟨272027, by rfl⟩ : syracuseStep 1450813 = 544055) (by norm_num)
theorem B1287029 : Blo 1016603 1287029 := bbase (se 5 (by rfl) ⟨60329, by rfl⟩ : syracuseStep 1287029 = 120659) (by norm_num)
theorem B1287085 : Blo 1016603 1287085 := bbase (se 3 (by rfl) ⟨241328, by rfl⟩ : syracuseStep 1287085 = 482657) (by norm_num)
theorem B1287181 : Blo 1016603 1287181 := bbase (se 3 (by rfl) ⟨241346, by rfl⟩ : syracuseStep 1287181 = 482693) (by norm_num)
theorem B1451029 : Blo 1016603 1451029 := bbase (se 6 (by rfl) ⟨34008, by rfl⟩ : syracuseStep 1451029 = 68017) (by norm_num)
theorem B4138037 : Blo 1016603 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B4891765 : Blo 1016603 4891765 := bbase (se 5 (by rfl) ⟨229301, by rfl⟩ : syracuseStep 4891765 = 458603) (by norm_num)
theorem B1287353 : Blo 1016603 1287353 := bbase (se 2 (by rfl) ⟨482757, by rfl⟩ : syracuseStep 1287353 = 965515) (by norm_num)
theorem B2172101 : Blo 1016603 2172101 := bbase (se 4 (by rfl) ⟨203634, by rfl⟩ : syracuseStep 2172101 = 407269) (by norm_num)
theorem B1287409 : Blo 1016603 1287409 := bbase (se 2 (by rfl) ⟨482778, by rfl⟩ : syracuseStep 1287409 = 965557) (by norm_num)
theorem B1221961 : Blo 1016603 1221961 := bbase (se 2 (by rfl) ⟨458235, by rfl⟩ : syracuseStep 1221961 = 916471) (by norm_num)
theorem B1287505 : Blo 1016603 1287505 := bbase (se 2 (by rfl) ⟨482814, by rfl⟩ : syracuseStep 1287505 = 965629) (by norm_num)
theorem B1222009 : Blo 1016603 1222009 := bbase (se 2 (by rfl) ⟨458253, by rfl⟩ : syracuseStep 1222009 = 916507) (by norm_num)
theorem B1451405 : Blo 1016603 1451405 := bbase (se 3 (by rfl) ⟨272138, by rfl⟩ : syracuseStep 1451405 = 544277) (by norm_num)
theorem B2172341 : Blo 1016603 2172341 := bbase (se 5 (by rfl) ⟨101828, by rfl⟩ : syracuseStep 2172341 = 203657) (by norm_num)
theorem B1287677 : Blo 1016603 1287677 := bbase (se 3 (by rfl) ⟨241439, by rfl⟩ : syracuseStep 1287677 = 482879) (by norm_num)
theorem B1287733 : Blo 1016603 1287733 := bbase (se 5 (by rfl) ⟨60362, by rfl⟩ : syracuseStep 1287733 = 120725) (by norm_num)
theorem B1287829 : Blo 1016603 1287829 := bbase (se 6 (by rfl) ⟨30183, by rfl⟩ : syracuseStep 1287829 = 60367) (by norm_num)
theorem B1288001 : Blo 1016603 1288001 := bbase (se 2 (by rfl) ⟨483000, by rfl⟩ : syracuseStep 1288001 = 966001) (by norm_num)
theorem B5154677 : Blo 1016603 5154677 := bbase (se 5 (by rfl) ⟨241625, by rfl⟩ : syracuseStep 5154677 = 483251) (by norm_num)
theorem B1288057 : Blo 1016603 1288057 := bbase (se 2 (by rfl) ⟨483021, by rfl⟩ : syracuseStep 1288057 = 966043) (by norm_num)
theorem B2172845 : Blo 1016603 2172845 := bbase (se 3 (by rfl) ⟨407408, by rfl⟩ : syracuseStep 2172845 = 814817) (by norm_num)
theorem B2172853 : Blo 1016603 2172853 := bbase (se 5 (by rfl) ⟨101852, by rfl⟩ : syracuseStep 2172853 = 203705) (by norm_num)
theorem B1288153 : Blo 1016603 1288153 := bbase (se 2 (by rfl) ⟨483057, by rfl⟩ : syracuseStep 1288153 = 966115) (by norm_num)
theorem B1288325 : Blo 1016603 1288325 := bbase (se 4 (by rfl) ⟨120780, by rfl⟩ : syracuseStep 1288325 = 241561) (by norm_num)
theorem B3582133 : Blo 1016603 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B1288381 : Blo 1016603 1288381 := bbase (se 3 (by rfl) ⟨241571, by rfl⟩ : syracuseStep 1288381 = 483143) (by norm_num)
theorem B1288477 : Blo 1016603 1288477 := bbase (se 3 (by rfl) ⟨241589, by rfl⟩ : syracuseStep 1288477 = 483179) (by norm_num)
theorem B1223057 : Blo 1016603 1223057 := bbase (se 2 (by rfl) ⟨458646, by rfl⟩ : syracuseStep 1223057 = 917293) (by norm_num)
theorem B1288649 : Blo 1016603 1288649 := bbase (se 2 (by rfl) ⟨483243, by rfl⟩ : syracuseStep 1288649 = 966487) (by norm_num)
theorem B1288705 : Blo 1016603 1288705 := bbase (se 2 (by rfl) ⟨483264, by rfl⟩ : syracuseStep 1288705 = 966529) (by norm_num)
theorem B1288801 : Blo 1016603 1288801 := bbase (se 2 (by rfl) ⟨483300, by rfl⟩ : syracuseStep 1288801 = 966601) (by norm_num)
theorem B1223365 : Blo 1016603 1223365 := bbase (se 4 (by rfl) ⟨114690, by rfl⟩ : syracuseStep 1223365 = 229381) (by norm_num)
theorem B1288973 : Blo 1016603 1288973 := bbase (se 3 (by rfl) ⟨241682, by rfl⟩ : syracuseStep 1288973 = 483365) (by norm_num)
theorem B1452829 : Blo 1016603 1452829 := bbase (se 3 (by rfl) ⟨272405, by rfl⟩ : syracuseStep 1452829 = 544811) (by norm_num)
theorem B1289029 : Blo 1016603 1289029 := bbase (se 4 (by rfl) ⟨120846, by rfl⟩ : syracuseStep 1289029 = 241693) (by norm_num)
theorem B1223533 : Blo 1016603 1223533 := bbase (se 3 (by rfl) ⟨229412, by rfl⟩ : syracuseStep 1223533 = 458825) (by norm_num)
theorem B1289125 : Blo 1016603 1289125 := bbase (se 4 (by rfl) ⟨120855, by rfl⟩ : syracuseStep 1289125 = 241711) (by norm_num)
theorem B2173981 : Blo 1016603 2173981 := bbase (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) (by norm_num)
theorem B1223729 : Blo 1016603 1223729 := bbase (se 2 (by rfl) ⟨458898, by rfl⟩ : syracuseStep 1223729 = 917797) (by norm_num)
theorem B1289297 : Blo 1016603 1289297 := bbase (se 2 (by rfl) ⟨483486, by rfl⟩ : syracuseStep 1289297 = 966973) (by norm_num)
theorem B7842901 : Blo 1016603 7842901 := bbase (se 8 (by rfl) ⟨45954, by rfl⟩ : syracuseStep 7842901 = 91909) (by norm_num)
theorem B5155973 : Blo 1016603 5155973 := bbase (se 4 (by rfl) ⟨483372, by rfl⟩ : syracuseStep 5155973 = 966745) (by norm_num)
theorem B1289353 : Blo 1016603 1289353 := bbase (se 2 (by rfl) ⟨483507, by rfl⟩ : syracuseStep 1289353 = 967015) (by norm_num)
theorem B3091621 : Blo 1016603 3091621 := bbase (se 4 (by rfl) ⟨289839, by rfl⟩ : syracuseStep 3091621 = 579679) (by norm_num)
theorem B8694965 : Blo 1016603 8694965 := bbase (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) (by norm_num)
theorem B1289449 : Blo 1016603 1289449 := bbase (se 2 (by rfl) ⟨483543, by rfl⟩ : syracuseStep 1289449 = 967087) (by norm_num)
theorem B3484981 : Blo 1016603 3484981 := bbase (se 5 (by rfl) ⟨163358, by rfl⟩ : syracuseStep 3484981 = 326717) (by norm_num)
theorem B1715573 : Blo 1016603 1715573 := bbase (se 5 (by rfl) ⟨80417, by rfl⟩ : syracuseStep 1715573 = 160835) (by norm_num)
theorem B2174357 : Blo 1016603 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B1289621 : Blo 1016603 1289621 := bbase (se 6 (by rfl) ⟨30225, by rfl⟩ : syracuseStep 1289621 = 60451) (by norm_num)
theorem B6532501 : Blo 1016603 6532501 := bbase (se 6 (by rfl) ⟨153105, by rfl⟩ : syracuseStep 6532501 = 306211) (by norm_num)
theorem B1289677 : Blo 1016603 1289677 := bbase (se 3 (by rfl) ⟨241814, by rfl⟩ : syracuseStep 1289677 = 483629) (by norm_num)
theorem B1715701 : Blo 1016603 1715701 := bbase (se 5 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 1715701 = 160847) (by norm_num)
theorem B1289773 : Blo 1016603 1289773 := bbase (se 3 (by rfl) ⟨241832, by rfl⟩ : syracuseStep 1289773 = 483665) (by norm_num)
theorem B1715789 : Blo 1016603 1715789 := bbase (se 3 (by rfl) ⟨321710, by rfl⟩ : syracuseStep 1715789 = 643421) (by norm_num)
theorem B3092069 : Blo 1016603 3092069 := bbase (se 4 (by rfl) ⟨289881, by rfl⟩ : syracuseStep 3092069 = 579763) (by norm_num)
theorem B1715917 : Blo 1016603 1715917 := bbase (se 3 (by rfl) ⟨321734, by rfl⟩ : syracuseStep 1715917 = 643469) (by norm_num)
theorem B1289945 : Blo 1016603 1289945 := bbase (se 2 (by rfl) ⟨483729, by rfl⟩ : syracuseStep 1289945 = 967459) (by norm_num)
theorem B3092213 : Blo 1016603 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B1289981 : Blo 1016603 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B1290001 : Blo 1016603 1290001 := bbase (se 2 (by rfl) ⟨483750, by rfl⟩ : syracuseStep 1290001 = 967501) (by norm_num)
theorem B1716005 : Blo 1016603 1716005 := bbase (se 4 (by rfl) ⟨160875, by rfl⟩ : syracuseStep 1716005 = 321751) (by norm_num)
theorem B1290097 : Blo 1016603 1290097 := bbase (se 2 (by rfl) ⟨483786, by rfl⟩ : syracuseStep 1290097 = 967573) (by norm_num)
theorem B1716133 : Blo 1016603 1716133 := bbase (se 4 (by rfl) ⟨160887, by rfl⟩ : syracuseStep 1716133 = 321775) (by norm_num)
theorem B5812181 : Blo 1016603 5812181 := bbase (se 7 (by rfl) ⟨68111, by rfl⟩ : syracuseStep 5812181 = 136223) (by norm_num)
theorem B1716221 : Blo 1016603 1716221 := bbase (se 3 (by rfl) ⟨321791, by rfl⟩ : syracuseStep 1716221 = 643583) (by norm_num)
theorem B1290269 : Blo 1016603 1290269 := bbase (se 3 (by rfl) ⟨241925, by rfl⟩ : syracuseStep 1290269 = 483851) (by norm_num)
theorem B1290325 : Blo 1016603 1290325 := bbase (se 8 (by rfl) ⟨7560, by rfl⟩ : syracuseStep 1290325 = 15121) (by norm_num)
theorem B1716349 : Blo 1016603 1716349 := bbase (se 3 (by rfl) ⟨321815, by rfl⟩ : syracuseStep 1716349 = 643631) (by norm_num)
theorem B4894901 : Blo 1016603 4894901 := bbase (se 5 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 4894901 = 458897) (by norm_num)
theorem B1290421 : Blo 1016603 1290421 := bbase (se 5 (by rfl) ⟨60488, by rfl⟩ : syracuseStep 1290421 = 120977) (by norm_num)
theorem B1716437 : Blo 1016603 1716437 := bbase (se 7 (by rfl) ⟨20114, by rfl⟩ : syracuseStep 1716437 = 40229) (by norm_num)
theorem B1323221 : Blo 1016603 1323221 := bbase (se 7 (by rfl) ⟨15506, by rfl⟩ : syracuseStep 1323221 = 31013) (by norm_num)
theorem B2896181 : Blo 1016603 2896181 := bbase (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) (by norm_num)
theorem B1716565 : Blo 1016603 1716565 := bbase (se 10 (by rfl) ⟨2514, by rfl⟩ : syracuseStep 1716565 = 5029) (by norm_num)
theorem B1290593 : Blo 1016603 1290593 := bbase (se 2 (by rfl) ⟨483972, by rfl⟩ : syracuseStep 1290593 = 967945) (by norm_num)
theorem B5157269 : Blo 1016603 5157269 := bbase (se 6 (by rfl) ⟨120873, by rfl⟩ : syracuseStep 5157269 = 241747) (by norm_num)
theorem B1290649 : Blo 1016603 1290649 := bbase (se 2 (by rfl) ⟨483993, by rfl⟩ : syracuseStep 1290649 = 967987) (by norm_num)
theorem B1716653 : Blo 1016603 1716653 := bbase (se 3 (by rfl) ⟨321872, by rfl⟩ : syracuseStep 1716653 = 643745) (by norm_num)
theorem B1290745 : Blo 1016603 1290745 := bbase (se 2 (by rfl) ⟨484029, by rfl⟩ : syracuseStep 1290745 = 968059) (by norm_num)
theorem B1716781 : Blo 1016603 1716781 := bbase (se 3 (by rfl) ⟨321896, by rfl⟩ : syracuseStep 1716781 = 643793) (by norm_num)
theorem B1225301 : Blo 1016603 1225301 := bbase (se 8 (by rfl) ⟨7179, by rfl⟩ : syracuseStep 1225301 = 14359) (by norm_num)
theorem B1225325 : Blo 1016603 1225325 := bbase (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) (by norm_num)
theorem B3256949 : Blo 1016603 3256949 := bbase (se 5 (by rfl) ⟨152669, by rfl⟩ : syracuseStep 3256949 = 305339) (by norm_num)
theorem B1716869 : Blo 1016603 1716869 := bbase (se 4 (by rfl) ⟨160956, by rfl⟩ : syracuseStep 1716869 = 321913) (by norm_num)
theorem B1159817 : Blo 1016603 1159817 := bbase (se 2 (by rfl) ⟨434931, by rfl⟩ : syracuseStep 1159817 = 869863) (by norm_num)
theorem B1290917 : Blo 1016603 1290917 := bbase (se 4 (by rfl) ⟨121023, by rfl⟩ : syracuseStep 1290917 = 242047) (by norm_num)
theorem B1290973 : Blo 1016603 1290973 := bbase (se 3 (by rfl) ⟨242057, by rfl⟩ : syracuseStep 1290973 = 484115) (by norm_num)
theorem B1716997 : Blo 1016603 1716997 := bbase (se 4 (by rfl) ⟨160968, by rfl⟩ : syracuseStep 1716997 = 321937) (by norm_num)
theorem B1291069 : Blo 1016603 1291069 := bbase (se 3 (by rfl) ⟨242075, by rfl⟩ : syracuseStep 1291069 = 484151) (by norm_num)
theorem B1717085 : Blo 1016603 1717085 := bbase (se 3 (by rfl) ⟨321953, by rfl⟩ : syracuseStep 1717085 = 643907) (by norm_num)
theorem B1225633 : Blo 1016603 1225633 := bbase (se 2 (by rfl) ⟨459612, by rfl⟩ : syracuseStep 1225633 = 919225) (by norm_num)
theorem B1160101 : Blo 1016603 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B1717213 : Blo 1016603 1717213 := bbase (se 3 (by rfl) ⟨321977, by rfl⟩ : syracuseStep 1717213 = 643955) (by norm_num)
theorem B1291241 : Blo 1016603 1291241 := bbase (se 2 (by rfl) ⟨484215, by rfl⟩ : syracuseStep 1291241 = 968431) (by norm_num)
theorem B2175997 : Blo 1016603 2175997 := bbase (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) (by norm_num)
theorem B1291297 : Blo 1016603 1291297 := bbase (se 2 (by rfl) ⟨484236, by rfl⟩ : syracuseStep 1291297 = 968473) (by norm_num)
theorem B1717301 : Blo 1016603 1717301 := bbase (se 5 (by rfl) ⟨80498, by rfl⟩ : syracuseStep 1717301 = 160997) (by norm_num)
theorem B1225805 : Blo 1016603 1225805 := bbase (se 3 (by rfl) ⟨229838, by rfl⟩ : syracuseStep 1225805 = 459677) (by norm_num)
theorem B1291393 : Blo 1016603 1291393 := bbase (se 2 (by rfl) ⟨484272, by rfl⟩ : syracuseStep 1291393 = 968545) (by norm_num)
theorem B3486869 : Blo 1016603 3486869 := bbase (se 6 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 3486869 = 163447) (by norm_num)
theorem B1717429 : Blo 1016603 1717429 := bbase (se 5 (by rfl) ⟨80504, by rfl⟩ : syracuseStep 1717429 = 161009) (by norm_num)
theorem B1225921 : Blo 1016603 1225921 := bbase (se 2 (by rfl) ⟨459720, by rfl⟩ : syracuseStep 1225921 = 919441) (by norm_num)
theorem B1717517 : Blo 1016603 1717517 := bbase (se 3 (by rfl) ⟨322034, by rfl⟩ : syracuseStep 1717517 = 644069) (by norm_num)
theorem B1226017 : Blo 1016603 1226017 := bbase (se 2 (by rfl) ⟨459756, by rfl⟩ : syracuseStep 1226017 = 919513) (by norm_num)
theorem B1291565 : Blo 1016603 1291565 := bbase (se 3 (by rfl) ⟨242168, by rfl⟩ : syracuseStep 1291565 = 484337) (by norm_num)
theorem B1291621 : Blo 1016603 1291621 := bbase (se 4 (by rfl) ⟨121089, by rfl⟩ : syracuseStep 1291621 = 242179) (by norm_num)
theorem B1717645 : Blo 1016603 1717645 := bbase (se 3 (by rfl) ⟨322058, by rfl⟩ : syracuseStep 1717645 = 644117) (by norm_num)
theorem B2897365 : Blo 1016603 2897365 := bbase (se 7 (by rfl) ⟨33953, by rfl⟩ : syracuseStep 2897365 = 67907) (by norm_num)
theorem B1717733 : Blo 1016603 1717733 := bbase (se 4 (by rfl) ⟨161037, by rfl⟩ : syracuseStep 1717733 = 322075) (by norm_num)
theorem B1717861 : Blo 1016603 1717861 := bbase (se 4 (by rfl) ⟨161049, by rfl⟩ : syracuseStep 1717861 = 322099) (by norm_num)
theorem B2897525 : Blo 1016603 2897525 := bbase (se 5 (by rfl) ⟨135821, by rfl⟩ : syracuseStep 2897525 = 271643) (by norm_num)
theorem B5158565 : Blo 1016603 5158565 := bbase (se 4 (by rfl) ⟨483615, by rfl⟩ : syracuseStep 5158565 = 967231) (by norm_num)
theorem B1717949 : Blo 1016603 1717949 := bbase (se 3 (by rfl) ⟨322115, by rfl⟩ : syracuseStep 1717949 = 644231) (by norm_num)
theorem B1718077 : Blo 1016603 1718077 := bbase (se 3 (by rfl) ⟨322139, by rfl⟩ : syracuseStep 1718077 = 644279) (by norm_num)
theorem B2897765 : Blo 1016603 2897765 := bbase (se 4 (by rfl) ⟨271665, by rfl⟩ : syracuseStep 2897765 = 543331) (by norm_num)
theorem B2176885 : Blo 1016603 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B1718165 : Blo 1016603 1718165 := bbase (se 6 (by rfl) ⟨40269, by rfl⟩ : syracuseStep 1718165 = 80539) (by norm_num)
theorem B1718293 : Blo 1016603 1718293 := bbase (se 6 (by rfl) ⟨40272, by rfl⟩ : syracuseStep 1718293 = 80545) (by norm_num)
theorem B2897957 : Blo 1016603 2897957 := bbase (se 4 (by rfl) ⟨271683, by rfl⟩ : syracuseStep 2897957 = 543367) (by norm_num)
theorem B8697941 : Blo 1016603 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B1718381 : Blo 1016603 1718381 := bbase (se 3 (by rfl) ⟨322196, by rfl⟩ : syracuseStep 1718381 = 644393) (by norm_num)
theorem B6535349 : Blo 1016603 6535349 := bbase (se 5 (by rfl) ⟨306344, by rfl⟩ : syracuseStep 6535349 = 612689) (by norm_num)
theorem B1718509 : Blo 1016603 1718509 := bbase (se 3 (by rfl) ⟨322220, by rfl⟩ : syracuseStep 1718509 = 644441) (by norm_num)
theorem B1718597 : Blo 1016603 1718597 := bbase (se 4 (by rfl) ⟨161118, by rfl⟩ : syracuseStep 1718597 = 322237) (by norm_num)
theorem B2177381 : Blo 1016603 2177381 := bbase (se 4 (by rfl) ⟨204129, by rfl⟩ : syracuseStep 2177381 = 408259) (by norm_num)
theorem B1718725 : Blo 1016603 1718725 := bbase (se 4 (by rfl) ⟨161130, by rfl⟩ : syracuseStep 1718725 = 322261) (by norm_num)
theorem B1161733 : Blo 1016603 1161733 := bbase (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) (by norm_num)
theorem B1718813 : Blo 1016603 1718813 := bbase (se 3 (by rfl) ⟨322277, by rfl⟩ : syracuseStep 1718813 = 644555) (by norm_num)
theorem B1030705 : Blo 1016603 1030705 := bbase (se 2 (by rfl) ⟨386514, by rfl⟩ : syracuseStep 1030705 = 773029) (by norm_num)
theorem B1718941 : Blo 1016603 1718941 := bbase (se 3 (by rfl) ⟨322301, by rfl⟩ : syracuseStep 1718941 = 644603) (by norm_num)
theorem B1719029 : Blo 1016603 1719029 := bbase (se 5 (by rfl) ⟨80579, by rfl⟩ : syracuseStep 1719029 = 161159) (by norm_num)
theorem B1719157 : Blo 1016603 1719157 := bbase (se 5 (by rfl) ⟨80585, by rfl⟩ : syracuseStep 1719157 = 161171) (by norm_num)
theorem B4897685 : Blo 1016603 4897685 := bbase (se 6 (by rfl) ⟨114789, by rfl⟩ : syracuseStep 4897685 = 229579) (by norm_num)
theorem B7650229 : Blo 1016603 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B5159861 : Blo 1016603 5159861 := bbase (se 5 (by rfl) ⟨241868, by rfl⟩ : syracuseStep 5159861 = 483737) (by norm_num)
theorem B1719245 : Blo 1016603 1719245 := bbase (se 3 (by rfl) ⟨322358, by rfl⟩ : syracuseStep 1719245 = 644717) (by norm_num)
theorem B2898949 : Blo 1016603 2898949 := bbase (se 4 (by rfl) ⟨271776, by rfl⟩ : syracuseStep 2898949 = 543553) (by norm_num)
theorem B1719373 : Blo 1016603 1719373 := bbase (se 3 (by rfl) ⟨322382, by rfl⟩ : syracuseStep 1719373 = 644765) (by norm_num)
theorem B1031273 : Blo 1016603 1031273 := bbase (se 2 (by rfl) ⟨386727, by rfl⟩ : syracuseStep 1031273 = 773455) (by norm_num)
theorem B1719461 : Blo 1016603 1719461 := bbase (se 4 (by rfl) ⟨161199, by rfl⟩ : syracuseStep 1719461 = 322399) (by norm_num)
theorem B2178245 : Blo 1016603 2178245 := bbase (se 4 (by rfl) ⟨204210, by rfl⟩ : syracuseStep 2178245 = 408421) (by norm_num)
theorem B1719589 : Blo 1016603 1719589 := bbase (se 4 (by rfl) ⟨161211, by rfl⟩ : syracuseStep 1719589 = 322423) (by norm_num)
theorem B2178389 : Blo 1016603 2178389 := bbase (se 11 (by rfl) ⟨1595, by rfl⟩ : syracuseStep 2178389 = 3191) (by norm_num)
theorem B1719677 : Blo 1016603 1719677 := bbase (se 3 (by rfl) ⟨322439, by rfl⟩ : syracuseStep 1719677 = 644879) (by norm_num)
theorem B3980773 : Blo 1016603 3980773 := bbase (se 4 (by rfl) ⟨373197, by rfl⟩ : syracuseStep 3980773 = 746395) (by norm_num)
theorem B1719805 : Blo 1016603 1719805 := bbase (se 3 (by rfl) ⟨322463, by rfl⟩ : syracuseStep 1719805 = 644927) (by norm_num)
theorem B49495637 : Blo 1016603 49495637 := bbase (se 8 (by rfl) ⟨290013, by rfl⟩ : syracuseStep 49495637 = 580027) (by norm_num)
theorem B1719893 : Blo 1016603 1719893 := bbase (se 8 (by rfl) ⟨10077, by rfl⟩ : syracuseStep 1719893 = 20155) (by norm_num)
theorem B7749269 : Blo 1016603 7749269 := bbase (se 6 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 7749269 = 363247) (by norm_num)
theorem B1031837 : Blo 1016603 1031837 := bbase (se 3 (by rfl) ⟨193469, by rfl⟩ : syracuseStep 1031837 = 386939) (by norm_num)
theorem B1031873 : Blo 1016603 1031873 := bbase (se 2 (by rfl) ⟨386952, by rfl⟩ : syracuseStep 1031873 = 773905) (by norm_num)
theorem B1720021 : Blo 1016603 1720021 := bbase (se 7 (by rfl) ⟨20156, by rfl⟩ : syracuseStep 1720021 = 40313) (by norm_num)
theorem B6602485 : Blo 1016603 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B1720109 : Blo 1016603 1720109 := bbase (se 3 (by rfl) ⟨322520, by rfl⟩ : syracuseStep 1720109 = 645041) (by norm_num)
theorem B3096485 : Blo 1016603 3096485 := bbase (se 4 (by rfl) ⟨290295, by rfl⟩ : syracuseStep 3096485 = 580591) (by norm_num)
theorem B1720237 : Blo 1016603 1720237 := bbase (se 3 (by rfl) ⟨322544, by rfl⟩ : syracuseStep 1720237 = 645089) (by norm_num)
theorem B3260357 : Blo 1016603 3260357 := bbase (se 4 (by rfl) ⟨305658, by rfl⟩ : syracuseStep 3260357 = 611317) (by norm_num)
theorem B1720325 : Blo 1016603 1720325 := bbase (se 4 (by rfl) ⟨161280, by rfl⟩ : syracuseStep 1720325 = 322561) (by norm_num)
theorem B2179133 : Blo 1016603 2179133 := bbase (se 3 (by rfl) ⟨408587, by rfl⟩ : syracuseStep 2179133 = 817175) (by norm_num)
theorem B2900053 : Blo 1016603 2900053 := bbase (se 8 (by rfl) ⟨16992, by rfl⟩ : syracuseStep 2900053 = 33985) (by norm_num)
theorem B1720453 : Blo 1016603 1720453 := bbase (se 4 (by rfl) ⟨161292, by rfl⟩ : syracuseStep 1720453 = 322585) (by norm_num)
theorem B5161157 : Blo 1016603 5161157 := bbase (se 4 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 5161157 = 967717) (by norm_num)
theorem B1720541 : Blo 1016603 1720541 := bbase (se 3 (by rfl) ⟨322601, by rfl⟩ : syracuseStep 1720541 = 645203) (by norm_num)
theorem B1032421 : Blo 1016603 1032421 := bbase (se 4 (by rfl) ⟨96789, by rfl⟩ : syracuseStep 1032421 = 193579) (by norm_num)
theorem B1032457 : Blo 1016603 1032457 := bbase (se 2 (by rfl) ⟨387171, by rfl⟩ : syracuseStep 1032457 = 774343) (by norm_num)
theorem B4538693 : Blo 1016603 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B9290069 : Blo 1016603 9290069 := bbase (se 10 (by rfl) ⟨13608, by rfl⟩ : syracuseStep 9290069 = 27217) (by norm_num)
theorem B1720669 : Blo 1016603 1720669 := bbase (se 3 (by rfl) ⟨322625, by rfl⟩ : syracuseStep 1720669 = 645251) (by norm_num)
theorem B1720757 : Blo 1016603 1720757 := bbase (se 5 (by rfl) ⟨80660, by rfl⟩ : syracuseStep 1720757 = 161321) (by norm_num)
theorem B1163813 : Blo 1016603 1163813 := bbase (se 4 (by rfl) ⟨109107, by rfl⟩ : syracuseStep 1163813 = 218215) (by norm_num)
theorem B1720885 : Blo 1016603 1720885 := bbase (se 5 (by rfl) ⟨80666, by rfl⟩ : syracuseStep 1720885 = 161333) (by norm_num)
theorem B1720973 : Blo 1016603 1720973 := bbase (se 3 (by rfl) ⟨322682, by rfl⟩ : syracuseStep 1720973 = 645365) (by norm_num)
theorem B1721101 : Blo 1016603 1721101 := bbase (se 3 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 1721101 = 645413) (by norm_num)
theorem B1721189 : Blo 1016603 1721189 := bbase (se 4 (by rfl) ⟨161361, by rfl⟩ : syracuseStep 1721189 = 322723) (by norm_num)
theorem B1721317 : Blo 1016603 1721317 := bbase (se 4 (by rfl) ⟨161373, by rfl⟩ : syracuseStep 1721317 = 322747) (by norm_num)
theorem B2573309 : Blo 1016603 2573309 := bbase (se 3 (by rfl) ⟨482495, by rfl⟩ : syracuseStep 2573309 = 964991) (by norm_num)
theorem B1721405 : Blo 1016603 1721405 := bbase (se 3 (by rfl) ⟨322763, by rfl⟩ : syracuseStep 1721405 = 645527) (by norm_num)
theorem B1033349 : Blo 1016603 1033349 := bbase (se 4 (by rfl) ⟨96876, by rfl⟩ : syracuseStep 1033349 = 193753) (by norm_num)
theorem B1524917 : Blo 1016603 1524917 := bbase (se 5 (by rfl) ⟨71480, by rfl⟩ : syracuseStep 1524917 = 142961) (by norm_num)
theorem B1721533 : Blo 1016603 1721533 := bbase (se 3 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 1721533 = 645575) (by norm_num)
theorem B3261637 : Blo 1016603 3261637 := bbase (se 4 (by rfl) ⟨305778, by rfl⟩ : syracuseStep 3261637 = 611557) (by norm_num)
theorem B1524941 : Blo 1016603 1524941 := bbase (se 3 (by rfl) ⟨285926, by rfl⟩ : syracuseStep 1524941 = 571853) (by norm_num)
theorem B1524965 : Blo 1016603 1524965 := bbase (se 4 (by rfl) ⟨142965, by rfl⟩ : syracuseStep 1524965 = 285931) (by norm_num)
theorem B1524989 : Blo 1016603 1524989 := bbase (se 3 (by rfl) ⟨285935, by rfl⟩ : syracuseStep 1524989 = 571871) (by norm_num)
theorem B1525013 : Blo 1016603 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B1721621 : Blo 1016603 1721621 := bbase (se 6 (by rfl) ⟨40350, by rfl⟩ : syracuseStep 1721621 = 80701) (by norm_num)
theorem B1525037 : Blo 1016603 1525037 := bbase (se 3 (by rfl) ⟨285944, by rfl⟩ : syracuseStep 1525037 = 571889) (by norm_num)
theorem B1525061 : Blo 1016603 1525061 := bbase (se 4 (by rfl) ⟨142974, by rfl⟩ : syracuseStep 1525061 = 285949) (by norm_num)
theorem B2573653 : Blo 1016603 2573653 := bbase (se 12 (by rfl) ⟨942, by rfl⟩ : syracuseStep 2573653 = 1885) (by norm_num)
theorem B1525085 : Blo 1016603 1525085 := bbase (se 3 (by rfl) ⟨285953, by rfl⟩ : syracuseStep 1525085 = 571907) (by norm_num)
theorem B1525109 : Blo 1016603 1525109 := bbase (se 5 (by rfl) ⟨71489, by rfl⟩ : syracuseStep 1525109 = 142979) (by norm_num)
theorem B1525133 : Blo 1016603 1525133 := bbase (se 3 (by rfl) ⟨285962, by rfl⟩ : syracuseStep 1525133 = 571925) (by norm_num)
theorem B1721749 : Blo 1016603 1721749 := bbase (se 6 (by rfl) ⟨40353, by rfl⟩ : syracuseStep 1721749 = 80707) (by norm_num)
theorem B1525157 : Blo 1016603 1525157 := bbase (se 4 (by rfl) ⟨142983, by rfl⟩ : syracuseStep 1525157 = 285967) (by norm_num)
theorem B1525181 : Blo 1016603 1525181 := bbase (se 3 (by rfl) ⟨285971, by rfl⟩ : syracuseStep 1525181 = 571943) (by norm_num)
theorem B2573765 : Blo 1016603 2573765 := bbase (se 4 (by rfl) ⟨241290, by rfl⟩ : syracuseStep 2573765 = 482581) (by norm_num)
theorem B1525205 : Blo 1016603 1525205 := bbase (se 7 (by rfl) ⟨17873, by rfl⟩ : syracuseStep 1525205 = 35747) (by norm_num)
theorem B5162453 : Blo 1016603 5162453 := bbase (se 7 (by rfl) ⟨60497, by rfl⟩ : syracuseStep 5162453 = 120995) (by norm_num)
theorem B1525229 : Blo 1016603 1525229 := bbase (se 3 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 1525229 = 571961) (by norm_num)
theorem B1721837 : Blo 1016603 1721837 := bbase (se 3 (by rfl) ⟨322844, by rfl⟩ : syracuseStep 1721837 = 645689) (by norm_num)
theorem B1525253 : Blo 1016603 1525253 := bbase (se 4 (by rfl) ⟨142992, by rfl⟩ : syracuseStep 1525253 = 285985) (by norm_num)
theorem B1525277 : Blo 1016603 1525277 := bbase (se 3 (by rfl) ⟨285989, by rfl⟩ : syracuseStep 1525277 = 571979) (by norm_num)
theorem B1525301 : Blo 1016603 1525301 := bbase (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) (by norm_num)
theorem B2901557 : Blo 1016603 2901557 := bbase (se 5 (by rfl) ⟨136010, by rfl⟩ : syracuseStep 2901557 = 272021) (by norm_num)
theorem B1525325 : Blo 1016603 1525325 := bbase (se 3 (by rfl) ⟨285998, by rfl⟩ : syracuseStep 1525325 = 571997) (by norm_num)
theorem B2442845 : Blo 1016603 2442845 := bbase (se 3 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 2442845 = 916067) (by norm_num)
theorem B1525349 : Blo 1016603 1525349 := bbase (se 4 (by rfl) ⟨143001, by rfl⟩ : syracuseStep 1525349 = 286003) (by norm_num)
theorem B1721965 : Blo 1016603 1721965 := bbase (se 3 (by rfl) ⟨322868, by rfl⟩ : syracuseStep 1721965 = 645737) (by norm_num)
theorem B1525373 : Blo 1016603 1525373 := bbase (se 3 (by rfl) ⟨286007, by rfl⟩ : syracuseStep 1525373 = 572015) (by norm_num)
theorem B2573957 : Blo 1016603 2573957 := bbase (se 4 (by rfl) ⟨241308, by rfl⟩ : syracuseStep 2573957 = 482617) (by norm_num)
theorem B1525397 : Blo 1016603 1525397 := bbase (se 6 (by rfl) ⟨35751, by rfl⟩ : syracuseStep 1525397 = 71503) (by norm_num)
theorem B1525421 : Blo 1016603 1525421 := bbase (se 3 (by rfl) ⟨286016, by rfl⟩ : syracuseStep 1525421 = 572033) (by norm_num)
theorem B4966069 : Blo 1016603 4966069 := bbase (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) (by norm_num)
theorem B1525445 : Blo 1016603 1525445 := bbase (se 4 (by rfl) ⟨143010, by rfl⟩ : syracuseStep 1525445 = 286021) (by norm_num)
theorem B1722053 : Blo 1016603 1722053 := bbase (se 4 (by rfl) ⟨161442, by rfl⟩ : syracuseStep 1722053 = 322885) (by norm_num)
theorem B1033933 : Blo 1016603 1033933 := bbase (se 3 (by rfl) ⟨193862, by rfl⟩ : syracuseStep 1033933 = 387725) (by norm_num)
theorem B1525469 : Blo 1016603 1525469 := bbase (se 3 (by rfl) ⟨286025, by rfl⟩ : syracuseStep 1525469 = 572051) (by norm_num)
theorem B1525493 : Blo 1016603 1525493 := bbase (se 5 (by rfl) ⟨71507, by rfl⟩ : syracuseStep 1525493 = 143015) (by norm_num)
theorem B1525517 : Blo 1016603 1525517 := bbase (se 3 (by rfl) ⟨286034, by rfl⟩ : syracuseStep 1525517 = 572069) (by norm_num)
theorem B1525541 : Blo 1016603 1525541 := bbase (se 4 (by rfl) ⟨143019, by rfl⟩ : syracuseStep 1525541 = 286039) (by norm_num)
theorem B1525565 : Blo 1016603 1525565 := bbase (se 3 (by rfl) ⟨286043, by rfl⟩ : syracuseStep 1525565 = 572087) (by norm_num)
theorem B1722181 : Blo 1016603 1722181 := bbase (se 4 (by rfl) ⟨161454, by rfl⟩ : syracuseStep 1722181 = 322909) (by norm_num)
theorem B1525589 : Blo 1016603 1525589 := bbase (se 9 (by rfl) ⟨4469, by rfl⟩ : syracuseStep 1525589 = 8939) (by norm_num)
theorem B1525613 : Blo 1016603 1525613 := bbase (se 3 (by rfl) ⟨286052, by rfl⟩ : syracuseStep 1525613 = 572105) (by norm_num)
theorem B10438517 : Blo 1016603 10438517 := bbase (se 5 (by rfl) ⟨489305, by rfl⟩ : syracuseStep 10438517 = 978611) (by norm_num)
theorem B1525637 : Blo 1016603 1525637 := bbase (se 4 (by rfl) ⟨143028, by rfl⟩ : syracuseStep 1525637 = 286057) (by norm_num)
theorem B1525661 : Blo 1016603 1525661 := bbase (se 3 (by rfl) ⟨286061, by rfl⟩ : syracuseStep 1525661 = 572123) (by norm_num)
theorem B1722269 : Blo 1016603 1722269 := bbase (se 3 (by rfl) ⟨322925, by rfl⟩ : syracuseStep 1722269 = 645851) (by norm_num)
theorem B1525685 : Blo 1016603 1525685 := bbase (se 5 (by rfl) ⟨71516, by rfl⟩ : syracuseStep 1525685 = 143033) (by norm_num)
theorem B1525709 : Blo 1016603 1525709 := bbase (se 3 (by rfl) ⟨286070, by rfl⟩ : syracuseStep 1525709 = 572141) (by norm_num)
theorem B2574301 : Blo 1016603 2574301 := bbase (se 3 (by rfl) ⟨482681, by rfl⟩ : syracuseStep 2574301 = 965363) (by norm_num)
theorem B1525733 : Blo 1016603 1525733 := bbase (se 4 (by rfl) ⟨143037, by rfl⟩ : syracuseStep 1525733 = 286075) (by norm_num)
theorem B1525757 : Blo 1016603 1525757 := bbase (se 3 (by rfl) ⟨286079, by rfl⟩ : syracuseStep 1525757 = 572159) (by norm_num)
theorem B1525781 : Blo 1016603 1525781 := bbase (se 6 (by rfl) ⟨35760, by rfl⟩ : syracuseStep 1525781 = 71521) (by norm_num)
theorem B1525805 : Blo 1016603 1525805 := bbase (se 3 (by rfl) ⟨286088, by rfl⟩ : syracuseStep 1525805 = 572177) (by norm_num)
theorem B4343861 : Blo 1016603 4343861 := bbase (se 5 (by rfl) ⟨203618, by rfl⟩ : syracuseStep 4343861 = 407237) (by norm_num)
theorem B1525829 : Blo 1016603 1525829 := bbase (se 4 (by rfl) ⟨143046, by rfl⟩ : syracuseStep 1525829 = 286093) (by norm_num)
theorem B2574413 : Blo 1016603 2574413 := bbase (se 3 (by rfl) ⟨482702, by rfl⟩ : syracuseStep 2574413 = 965405) (by norm_num)
theorem B2476117 : Blo 1016603 2476117 := bbase (se 8 (by rfl) ⟨14508, by rfl⟩ : syracuseStep 2476117 = 29017) (by norm_num)
theorem B1525853 : Blo 1016603 1525853 := bbase (se 3 (by rfl) ⟨286097, by rfl⟩ : syracuseStep 1525853 = 572195) (by norm_num)
theorem B1525877 : Blo 1016603 1525877 := bbase (se 5 (by rfl) ⟨71525, by rfl⟩ : syracuseStep 1525877 = 143051) (by norm_num)
theorem B1525901 : Blo 1016603 1525901 := bbase (se 3 (by rfl) ⟨286106, by rfl⟩ : syracuseStep 1525901 = 572213) (by norm_num)
theorem B1525925 : Blo 1016603 1525925 := bbase (se 4 (by rfl) ⟨143055, by rfl⟩ : syracuseStep 1525925 = 286111) (by norm_num)
theorem B1525949 : Blo 1016603 1525949 := bbase (se 3 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 1525949 = 572231) (by norm_num)
theorem B1525973 : Blo 1016603 1525973 := bbase (se 7 (by rfl) ⟨17882, by rfl⟩ : syracuseStep 1525973 = 35765) (by norm_num)
theorem B1525997 : Blo 1016603 1525997 := bbase (se 3 (by rfl) ⟨286124, by rfl⟩ : syracuseStep 1525997 = 572249) (by norm_num)
theorem B1526021 : Blo 1016603 1526021 := bbase (se 4 (by rfl) ⟨143064, by rfl⟩ : syracuseStep 1526021 = 286129) (by norm_num)
theorem B2574605 : Blo 1016603 2574605 := bbase (se 3 (by rfl) ⟨482738, by rfl⟩ : syracuseStep 2574605 = 965477) (by norm_num)
theorem B1526045 : Blo 1016603 1526045 := bbase (se 3 (by rfl) ⟨286133, by rfl⟩ : syracuseStep 1526045 = 572267) (by norm_num)
theorem B4344101 : Blo 1016603 4344101 := bbase (se 4 (by rfl) ⟨407259, by rfl⟩ : syracuseStep 4344101 = 814519) (by norm_num)
theorem B1526069 : Blo 1016603 1526069 := bbase (se 5 (by rfl) ⟨71534, by rfl⟩ : syracuseStep 1526069 = 143069) (by norm_num)
theorem B1526093 : Blo 1016603 1526093 := bbase (se 3 (by rfl) ⟨286142, by rfl⟩ : syracuseStep 1526093 = 572285) (by norm_num)
theorem B1526117 : Blo 1016603 1526117 := bbase (se 4 (by rfl) ⟨143073, by rfl⟩ : syracuseStep 1526117 = 286147) (by norm_num)
theorem B1526141 : Blo 1016603 1526141 := bbase (se 3 (by rfl) ⟨286151, by rfl⟩ : syracuseStep 1526141 = 572303) (by norm_num)
theorem B1526165 : Blo 1016603 1526165 := bbase (se 6 (by rfl) ⟨35769, by rfl⟩ : syracuseStep 1526165 = 71539) (by norm_num)
theorem B1526189 : Blo 1016603 1526189 := bbase (se 3 (by rfl) ⟨286160, by rfl⟩ : syracuseStep 1526189 = 572321) (by norm_num)
theorem B1526213 : Blo 1016603 1526213 := bbase (se 4 (by rfl) ⟨143082, by rfl⟩ : syracuseStep 1526213 = 286165) (by norm_num)
theorem B1526237 : Blo 1016603 1526237 := bbase (se 3 (by rfl) ⟨286169, by rfl⟩ : syracuseStep 1526237 = 572339) (by norm_num)
theorem B1526261 : Blo 1016603 1526261 := bbase (se 5 (by rfl) ⟨71543, by rfl⟩ : syracuseStep 1526261 = 143087) (by norm_num)
theorem B1526285 : Blo 1016603 1526285 := bbase (se 3 (by rfl) ⟨286178, by rfl⟩ : syracuseStep 1526285 = 572357) (by norm_num)
theorem B3262997 : Blo 1016603 3262997 := bbase (se 6 (by rfl) ⟨76476, by rfl⟩ : syracuseStep 3262997 = 152953) (by norm_num)
theorem B1526309 : Blo 1016603 1526309 := bbase (se 4 (by rfl) ⟨143091, by rfl⟩ : syracuseStep 1526309 = 286183) (by norm_num)
theorem B1526333 : Blo 1016603 1526333 := bbase (se 3 (by rfl) ⟨286187, by rfl⟩ : syracuseStep 1526333 = 572375) (by norm_num)
theorem B1526357 : Blo 1016603 1526357 := bbase (se 8 (by rfl) ⟨8943, by rfl⟩ : syracuseStep 1526357 = 17887) (by norm_num)
theorem B2574949 : Blo 1016603 2574949 := bbase (se 4 (by rfl) ⟨241401, by rfl⟩ : syracuseStep 2574949 = 482803) (by norm_num)
theorem B1526381 : Blo 1016603 1526381 := bbase (se 3 (by rfl) ⟨286196, by rfl⟩ : syracuseStep 1526381 = 572393) (by norm_num)
theorem B1526405 : Blo 1016603 1526405 := bbase (se 4 (by rfl) ⟨143100, by rfl⟩ : syracuseStep 1526405 = 286201) (by norm_num)
theorem B6965909 : Blo 1016603 6965909 := bbase (se 6 (by rfl) ⟨163263, by rfl⟩ : syracuseStep 6965909 = 326527) (by norm_num)
theorem B3263125 : Blo 1016603 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B1526429 : Blo 1016603 1526429 := bbase (se 3 (by rfl) ⟨286205, by rfl⟩ : syracuseStep 1526429 = 572411) (by norm_num)
theorem B1526453 : Blo 1016603 1526453 := bbase (se 5 (by rfl) ⟨71552, by rfl⟩ : syracuseStep 1526453 = 143105) (by norm_num)
theorem B1526477 : Blo 1016603 1526477 := bbase (se 3 (by rfl) ⟨286214, by rfl⟩ : syracuseStep 1526477 = 572429) (by norm_num)
theorem B2575061 : Blo 1016603 2575061 := bbase (se 7 (by rfl) ⟨30176, by rfl⟩ : syracuseStep 2575061 = 60353) (by norm_num)
theorem B1526501 : Blo 1016603 1526501 := bbase (se 4 (by rfl) ⟨143109, by rfl⟩ : syracuseStep 1526501 = 286219) (by norm_num)
theorem B5163749 : Blo 1016603 5163749 := bbase (se 4 (by rfl) ⟨484101, by rfl⟩ : syracuseStep 5163749 = 968203) (by norm_num)
theorem B1526525 : Blo 1016603 1526525 := bbase (se 3 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 1526525 = 572447) (by norm_num)
theorem B1526549 : Blo 1016603 1526549 := bbase (se 6 (by rfl) ⟨35778, by rfl⟩ : syracuseStep 1526549 = 71557) (by norm_num)
theorem B1526573 : Blo 1016603 1526573 := bbase (se 3 (by rfl) ⟨286232, by rfl⟩ : syracuseStep 1526573 = 572465) (by norm_num)
theorem B1526597 : Blo 1016603 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B1526621 : Blo 1016603 1526621 := bbase (se 3 (by rfl) ⟨286241, by rfl⟩ : syracuseStep 1526621 = 572483) (by norm_num)
theorem B1526645 : Blo 1016603 1526645 := bbase (se 5 (by rfl) ⟨71561, by rfl⟩ : syracuseStep 1526645 = 143123) (by norm_num)
theorem B1526669 : Blo 1016603 1526669 := bbase (se 3 (by rfl) ⟨286250, by rfl⟩ : syracuseStep 1526669 = 572501) (by norm_num)
theorem B2575253 : Blo 1016603 2575253 := bbase (se 6 (by rfl) ⟨60357, by rfl⟩ : syracuseStep 2575253 = 120715) (by norm_num)
theorem B3263381 : Blo 1016603 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B1526693 : Blo 1016603 1526693 := bbase (se 4 (by rfl) ⟨143127, by rfl⟩ : syracuseStep 1526693 = 286255) (by norm_num)
theorem B1526717 : Blo 1016603 1526717 := bbase (se 3 (by rfl) ⟨286259, by rfl⟩ : syracuseStep 1526717 = 572519) (by norm_num)
theorem B1526741 : Blo 1016603 1526741 := bbase (se 7 (by rfl) ⟨17891, by rfl⟩ : syracuseStep 1526741 = 35783) (by norm_num)
theorem B2444269 : Blo 1016603 2444269 := bbase (se 3 (by rfl) ⟨458300, by rfl⟩ : syracuseStep 2444269 = 916601) (by norm_num)
theorem B1526765 : Blo 1016603 1526765 := bbase (se 3 (by rfl) ⟨286268, by rfl⟩ : syracuseStep 1526765 = 572537) (by norm_num)
theorem B1526789 : Blo 1016603 1526789 := bbase (se 4 (by rfl) ⟨143136, by rfl⟩ : syracuseStep 1526789 = 286273) (by norm_num)
theorem B1526813 : Blo 1016603 1526813 := bbase (se 3 (by rfl) ⟨286277, by rfl⟩ : syracuseStep 1526813 = 572555) (by norm_num)
theorem B1526837 : Blo 1016603 1526837 := bbase (se 5 (by rfl) ⟨71570, by rfl⟩ : syracuseStep 1526837 = 143141) (by norm_num)
theorem B1526861 : Blo 1016603 1526861 := bbase (se 3 (by rfl) ⟨286286, by rfl⟩ : syracuseStep 1526861 = 572573) (by norm_num)
theorem B1526885 : Blo 1016603 1526885 := bbase (se 4 (by rfl) ⟨143145, by rfl⟩ : syracuseStep 1526885 = 286291) (by norm_num)
theorem B2903141 : Blo 1016603 2903141 := bbase (se 4 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 2903141 = 544339) (by norm_num)
theorem B7851125 : Blo 1016603 7851125 := bbase (se 5 (by rfl) ⟨368021, by rfl⟩ : syracuseStep 7851125 = 736043) (by norm_num)
theorem B1526909 : Blo 1016603 1526909 := bbase (se 3 (by rfl) ⟨286295, by rfl⟩ : syracuseStep 1526909 = 572591) (by norm_num)
theorem B1526933 : Blo 1016603 1526933 := bbase (se 6 (by rfl) ⟨35787, by rfl⟩ : syracuseStep 1526933 = 71575) (by norm_num)
theorem B1526957 : Blo 1016603 1526957 := bbase (se 3 (by rfl) ⟨286304, by rfl⟩ : syracuseStep 1526957 = 572609) (by norm_num)
theorem B1526981 : Blo 1016603 1526981 := bbase (se 4 (by rfl) ⟨143154, by rfl⟩ : syracuseStep 1526981 = 286309) (by norm_num)
theorem B1527005 : Blo 1016603 1527005 := bbase (se 3 (by rfl) ⟨286313, by rfl⟩ : syracuseStep 1527005 = 572627) (by norm_num)
theorem B2575597 : Blo 1016603 2575597 := bbase (se 3 (by rfl) ⟨482924, by rfl⟩ : syracuseStep 2575597 = 965849) (by norm_num)
theorem B1527029 : Blo 1016603 1527029 := bbase (se 5 (by rfl) ⟨71579, by rfl⟩ : syracuseStep 1527029 = 143159) (by norm_num)
theorem B1527053 : Blo 1016603 1527053 := bbase (se 3 (by rfl) ⟨286322, by rfl⟩ : syracuseStep 1527053 = 572645) (by norm_num)
theorem B1527077 : Blo 1016603 1527077 := bbase (se 4 (by rfl) ⟨143163, by rfl⟩ : syracuseStep 1527077 = 286327) (by norm_num)
theorem B1527101 : Blo 1016603 1527101 := bbase (se 3 (by rfl) ⟨286331, by rfl⟩ : syracuseStep 1527101 = 572663) (by norm_num)
theorem B1527125 : Blo 1016603 1527125 := bbase (se 11 (by rfl) ⟨1118, by rfl⟩ : syracuseStep 1527125 = 2237) (by norm_num)
theorem B2575709 : Blo 1016603 2575709 := bbase (se 3 (by rfl) ⟨482945, by rfl⟩ : syracuseStep 2575709 = 965891) (by norm_num)
theorem B1527149 : Blo 1016603 1527149 := bbase (se 3 (by rfl) ⟨286340, by rfl⟩ : syracuseStep 1527149 = 572681) (by norm_num)
theorem B1527173 : Blo 1016603 1527173 := bbase (se 4 (by rfl) ⟨143172, by rfl⟩ : syracuseStep 1527173 = 286345) (by norm_num)
theorem B1527197 : Blo 1016603 1527197 := bbase (se 3 (by rfl) ⟨286349, by rfl⟩ : syracuseStep 1527197 = 572699) (by norm_num)
theorem B1527221 : Blo 1016603 1527221 := bbase (se 5 (by rfl) ⟨71588, by rfl⟩ : syracuseStep 1527221 = 143177) (by norm_num)
theorem B1527245 : Blo 1016603 1527245 := bbase (se 3 (by rfl) ⟨286358, by rfl⟩ : syracuseStep 1527245 = 572717) (by norm_num)
theorem B1527269 : Blo 1016603 1527269 := bbase (se 4 (by rfl) ⟨143181, by rfl⟩ : syracuseStep 1527269 = 286363) (by norm_num)
theorem B1527293 : Blo 1016603 1527293 := bbase (se 3 (by rfl) ⟨286367, by rfl⟩ : syracuseStep 1527293 = 572735) (by norm_num)
theorem B1527317 : Blo 1016603 1527317 := bbase (se 6 (by rfl) ⟨35796, by rfl⟩ : syracuseStep 1527317 = 71593) (by norm_num)
theorem B2575901 : Blo 1016603 2575901 := bbase (se 3 (by rfl) ⟨482981, by rfl⟩ : syracuseStep 2575901 = 965963) (by norm_num)
theorem B1527341 : Blo 1016603 1527341 := bbase (se 3 (by rfl) ⟨286376, by rfl⟩ : syracuseStep 1527341 = 572753) (by norm_num)
theorem B1527365 : Blo 1016603 1527365 := bbase (se 4 (by rfl) ⟨143190, by rfl⟩ : syracuseStep 1527365 = 286381) (by norm_num)
theorem B1527389 : Blo 1016603 1527389 := bbase (se 3 (by rfl) ⟨286385, by rfl⟩ : syracuseStep 1527389 = 572771) (by norm_num)
theorem B1527413 : Blo 1016603 1527413 := bbase (se 5 (by rfl) ⟨71597, by rfl⟩ : syracuseStep 1527413 = 143195) (by norm_num)
theorem B2444941 : Blo 1016603 2444941 := bbase (se 3 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 2444941 = 916853) (by norm_num)
theorem B1527437 : Blo 1016603 1527437 := bbase (se 3 (by rfl) ⟨286394, by rfl⟩ : syracuseStep 1527437 = 572789) (by norm_num)
theorem B1527461 : Blo 1016603 1527461 := bbase (se 4 (by rfl) ⟨143199, by rfl⟩ : syracuseStep 1527461 = 286399) (by norm_num)
theorem B1527485 : Blo 1016603 1527485 := bbase (se 3 (by rfl) ⟨286403, by rfl⟩ : syracuseStep 1527485 = 572807) (by norm_num)
theorem B4181701 : Blo 1016603 4181701 := bbase (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) (by norm_num)
theorem B1527509 : Blo 1016603 1527509 := bbase (se 7 (by rfl) ⟨17900, by rfl⟩ : syracuseStep 1527509 = 35801) (by norm_num)
theorem B1527533 : Blo 1016603 1527533 := bbase (se 3 (by rfl) ⟨286412, by rfl⟩ : syracuseStep 1527533 = 572825) (by norm_num)
theorem B1527557 : Blo 1016603 1527557 := bbase (se 4 (by rfl) ⟨143208, by rfl⟩ : syracuseStep 1527557 = 286417) (by norm_num)
theorem B2903813 : Blo 1016603 2903813 := bbase (se 4 (by rfl) ⟨272232, by rfl⟩ : syracuseStep 2903813 = 544465) (by norm_num)
theorem B1527581 : Blo 1016603 1527581 := bbase (se 3 (by rfl) ⟨286421, by rfl⟩ : syracuseStep 1527581 = 572843) (by norm_num)
theorem B1527605 : Blo 1016603 1527605 := bbase (se 5 (by rfl) ⟨71606, by rfl⟩ : syracuseStep 1527605 = 143213) (by norm_num)
theorem B1527629 : Blo 1016603 1527629 := bbase (se 3 (by rfl) ⟨286430, by rfl⟩ : syracuseStep 1527629 = 572861) (by norm_num)
theorem B1527653 : Blo 1016603 1527653 := bbase (se 4 (by rfl) ⟨143217, by rfl⟩ : syracuseStep 1527653 = 286435) (by norm_num)
theorem B2445173 : Blo 1016603 2445173 := bbase (se 5 (by rfl) ⟨114617, by rfl⟩ : syracuseStep 2445173 = 229235) (by norm_num)
theorem B2576245 : Blo 1016603 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B1527677 : Blo 1016603 1527677 := bbase (se 3 (by rfl) ⟨286439, by rfl⟩ : syracuseStep 1527677 = 572879) (by norm_num)
theorem B1527701 : Blo 1016603 1527701 := bbase (se 6 (by rfl) ⟨35805, by rfl⟩ : syracuseStep 1527701 = 71611) (by norm_num)
theorem B2445221 : Blo 1016603 2445221 := bbase (se 4 (by rfl) ⟨229239, by rfl⟩ : syracuseStep 2445221 = 458479) (by norm_num)
theorem B1527725 : Blo 1016603 1527725 := bbase (se 3 (by rfl) ⟨286448, by rfl⟩ : syracuseStep 1527725 = 572897) (by norm_num)
theorem B1527749 : Blo 1016603 1527749 := bbase (se 4 (by rfl) ⟨143226, by rfl⟩ : syracuseStep 1527749 = 286453) (by norm_num)
theorem B1527773 : Blo 1016603 1527773 := bbase (se 3 (by rfl) ⟨286457, by rfl⟩ : syracuseStep 1527773 = 572915) (by norm_num)
theorem B2576357 : Blo 1016603 2576357 := bbase (se 4 (by rfl) ⟨241533, by rfl⟩ : syracuseStep 2576357 = 483067) (by norm_num)
theorem B1527797 : Blo 1016603 1527797 := bbase (se 5 (by rfl) ⟨71615, by rfl⟩ : syracuseStep 1527797 = 143231) (by norm_num)
theorem B5165045 : Blo 1016603 5165045 := bbase (se 5 (by rfl) ⟨242111, by rfl⟩ : syracuseStep 5165045 = 484223) (by norm_num)
theorem B1527821 : Blo 1016603 1527821 := bbase (se 3 (by rfl) ⟨286466, by rfl⟩ : syracuseStep 1527821 = 572933) (by norm_num)
theorem B1527845 : Blo 1016603 1527845 := bbase (se 4 (by rfl) ⟨143235, by rfl⟩ : syracuseStep 1527845 = 286471) (by norm_num)
theorem B1527869 : Blo 1016603 1527869 := bbase (se 3 (by rfl) ⟨286475, by rfl⟩ : syracuseStep 1527869 = 572951) (by norm_num)
theorem B1527893 : Blo 1016603 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B1527917 : Blo 1016603 1527917 := bbase (se 3 (by rfl) ⟨286484, by rfl⟩ : syracuseStep 1527917 = 572969) (by norm_num)
theorem B1527941 : Blo 1016603 1527941 := bbase (se 4 (by rfl) ⟨143244, by rfl⟩ : syracuseStep 1527941 = 286489) (by norm_num)
theorem B3723413 : Blo 1016603 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B1527965 : Blo 1016603 1527965 := bbase (se 3 (by rfl) ⟨286493, by rfl⟩ : syracuseStep 1527965 = 572987) (by norm_num)
theorem B2576549 : Blo 1016603 2576549 := bbase (se 4 (by rfl) ⟨241551, by rfl⟩ : syracuseStep 2576549 = 483103) (by norm_num)
theorem B1527989 : Blo 1016603 1527989 := bbase (se 5 (by rfl) ⟨71624, by rfl⟩ : syracuseStep 1527989 = 143249) (by norm_num)
theorem B2904245 : Blo 1016603 2904245 := bbase (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) (by norm_num)
theorem B1528013 : Blo 1016603 1528013 := bbase (se 3 (by rfl) ⟨286502, by rfl⟩ : syracuseStep 1528013 = 573005) (by norm_num)
theorem B1528037 : Blo 1016603 1528037 := bbase (se 4 (by rfl) ⟨143253, by rfl⟩ : syracuseStep 1528037 = 286507) (by norm_num)
theorem B1528061 : Blo 1016603 1528061 := bbase (se 3 (by rfl) ⟨286511, by rfl⟩ : syracuseStep 1528061 = 573023) (by norm_num)
theorem B1528085 : Blo 1016603 1528085 := bbase (se 6 (by rfl) ⟨35814, by rfl⟩ : syracuseStep 1528085 = 71629) (by norm_num)
theorem B1528109 : Blo 1016603 1528109 := bbase (se 3 (by rfl) ⟨286520, by rfl⟩ : syracuseStep 1528109 = 573041) (by norm_num)
theorem B1528133 : Blo 1016603 1528133 := bbase (se 4 (by rfl) ⟨143262, by rfl⟩ : syracuseStep 1528133 = 286525) (by norm_num)
theorem B1528157 : Blo 1016603 1528157 := bbase (se 3 (by rfl) ⟨286529, by rfl⟩ : syracuseStep 1528157 = 573059) (by norm_num)
theorem B1528181 : Blo 1016603 1528181 := bbase (se 5 (by rfl) ⟨71633, by rfl⟩ : syracuseStep 1528181 = 143267) (by norm_num)
theorem B1528205 : Blo 1016603 1528205 := bbase (se 3 (by rfl) ⟨286538, by rfl⟩ : syracuseStep 1528205 = 573077) (by norm_num)
theorem B1528229 : Blo 1016603 1528229 := bbase (se 4 (by rfl) ⟨143271, by rfl⟩ : syracuseStep 1528229 = 286543) (by norm_num)
theorem B1528253 : Blo 1016603 1528253 := bbase (se 3 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 1528253 = 573095) (by norm_num)
theorem B1528277 : Blo 1016603 1528277 := bbase (se 7 (by rfl) ⟨17909, by rfl⟩ : syracuseStep 1528277 = 35819) (by norm_num)
theorem B1528301 : Blo 1016603 1528301 := bbase (se 3 (by rfl) ⟨286556, by rfl⟩ : syracuseStep 1528301 = 573113) (by norm_num)
theorem B2576893 : Blo 1016603 2576893 := bbase (se 3 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 2576893 = 966335) (by norm_num)
theorem B1528325 : Blo 1016603 1528325 := bbase (se 4 (by rfl) ⟨143280, by rfl⟩ : syracuseStep 1528325 = 286561) (by norm_num)
theorem B4346389 : Blo 1016603 4346389 := bbase (se 6 (by rfl) ⟨101868, by rfl⟩ : syracuseStep 4346389 = 203737) (by norm_num)
theorem B1528349 : Blo 1016603 1528349 := bbase (se 3 (by rfl) ⟨286565, by rfl⟩ : syracuseStep 1528349 = 573131) (by norm_num)
theorem B1528373 : Blo 1016603 1528373 := bbase (se 5 (by rfl) ⟨71642, by rfl⟩ : syracuseStep 1528373 = 143285) (by norm_num)
theorem B1528397 : Blo 1016603 1528397 := bbase (se 3 (by rfl) ⟨286574, by rfl⟩ : syracuseStep 1528397 = 573149) (by norm_num)
theorem B1528421 : Blo 1016603 1528421 := bbase (se 4 (by rfl) ⟨143289, by rfl⟩ : syracuseStep 1528421 = 286579) (by norm_num)
theorem B2577005 : Blo 1016603 2577005 := bbase (se 3 (by rfl) ⟨483188, by rfl⟩ : syracuseStep 2577005 = 966377) (by norm_num)
theorem B1528445 : Blo 1016603 1528445 := bbase (se 3 (by rfl) ⟨286583, by rfl⟩ : syracuseStep 1528445 = 573167) (by norm_num)
theorem B11162261 : Blo 1016603 11162261 := bbase (se 6 (by rfl) ⟨261615, by rfl⟩ : syracuseStep 11162261 = 523231) (by norm_num)
theorem B1528469 : Blo 1016603 1528469 := bbase (se 6 (by rfl) ⟨35823, by rfl⟩ : syracuseStep 1528469 = 71647) (by norm_num)
theorem B1528493 : Blo 1016603 1528493 := bbase (se 3 (by rfl) ⟨286592, by rfl⟩ : syracuseStep 1528493 = 573185) (by norm_num)
theorem B1528517 : Blo 1016603 1528517 := bbase (se 4 (by rfl) ⟨143298, by rfl⟩ : syracuseStep 1528517 = 286597) (by norm_num)
theorem B1528541 : Blo 1016603 1528541 := bbase (se 3 (by rfl) ⟨286601, by rfl⟩ : syracuseStep 1528541 = 573203) (by norm_num)
theorem B1528565 : Blo 1016603 1528565 := bbase (se 5 (by rfl) ⟨71651, by rfl⟩ : syracuseStep 1528565 = 143303) (by norm_num)
theorem B1528589 : Blo 1016603 1528589 := bbase (se 3 (by rfl) ⟨286610, by rfl⟩ : syracuseStep 1528589 = 573221) (by norm_num)
theorem B1528613 : Blo 1016603 1528613 := bbase (se 4 (by rfl) ⟨143307, by rfl⟩ : syracuseStep 1528613 = 286615) (by norm_num)
theorem B2577197 : Blo 1016603 2577197 := bbase (se 3 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 2577197 = 966449) (by norm_num)
theorem B1528637 : Blo 1016603 1528637 := bbase (se 3 (by rfl) ⟨286619, by rfl⟩ : syracuseStep 1528637 = 573239) (by norm_num)
theorem B1528661 : Blo 1016603 1528661 := bbase (se 9 (by rfl) ⟨4478, by rfl⟩ : syracuseStep 1528661 = 8957) (by norm_num)
theorem B1528685 : Blo 1016603 1528685 := bbase (se 3 (by rfl) ⟨286628, by rfl⟩ : syracuseStep 1528685 = 573257) (by norm_num)
theorem B1528709 : Blo 1016603 1528709 := bbase (se 4 (by rfl) ⟨143316, by rfl⟩ : syracuseStep 1528709 = 286633) (by norm_num)
theorem B1528733 : Blo 1016603 1528733 := bbase (se 3 (by rfl) ⟨286637, by rfl⟩ : syracuseStep 1528733 = 573275) (by norm_num)
theorem B2904997 : Blo 1016603 2904997 := bbase (se 4 (by rfl) ⟨272343, by rfl⟩ : syracuseStep 2904997 = 544687) (by norm_num)
theorem B1528757 : Blo 1016603 1528757 := bbase (se 5 (by rfl) ⟨71660, by rfl⟩ : syracuseStep 1528757 = 143321) (by norm_num)
theorem B1528781 : Blo 1016603 1528781 := bbase (se 3 (by rfl) ⟨286646, by rfl⟩ : syracuseStep 1528781 = 573293) (by norm_num)
theorem B5297125 : Blo 1016603 5297125 := bbase (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) (by norm_num)
theorem B1528805 : Blo 1016603 1528805 := bbase (se 4 (by rfl) ⟨143325, by rfl⟩ : syracuseStep 1528805 = 286651) (by norm_num)
theorem B1528829 : Blo 1016603 1528829 := bbase (se 3 (by rfl) ⟨286655, by rfl⟩ : syracuseStep 1528829 = 573311) (by norm_num)
theorem B1528853 : Blo 1016603 1528853 := bbase (se 6 (by rfl) ⟨35832, by rfl⟩ : syracuseStep 1528853 = 71665) (by norm_num)
theorem B1102877 : Blo 1016603 1102877 := bbase (se 3 (by rfl) ⟨206789, by rfl⟩ : syracuseStep 1102877 = 413579) (by norm_num)
theorem B4903973 : Blo 1016603 4903973 := bbase (se 4 (by rfl) ⟨459747, by rfl⟩ : syracuseStep 4903973 = 919495) (by norm_num)
theorem B1528877 : Blo 1016603 1528877 := bbase (se 3 (by rfl) ⟨286664, by rfl⟩ : syracuseStep 1528877 = 573329) (by norm_num)
theorem B1528901 : Blo 1016603 1528901 := bbase (se 4 (by rfl) ⟨143334, by rfl⟩ : syracuseStep 1528901 = 286669) (by norm_num)
theorem B1528925 : Blo 1016603 1528925 := bbase (se 3 (by rfl) ⟨286673, by rfl⟩ : syracuseStep 1528925 = 573347) (by norm_num)
theorem B1528949 : Blo 1016603 1528949 := bbase (se 5 (by rfl) ⟨71669, by rfl⟩ : syracuseStep 1528949 = 143339) (by norm_num)
theorem B2577541 : Blo 1016603 2577541 := bbase (se 4 (by rfl) ⟨241644, by rfl⟩ : syracuseStep 2577541 = 483289) (by norm_num)
theorem B1528973 : Blo 1016603 1528973 := bbase (se 3 (by rfl) ⟨286682, by rfl⟩ : syracuseStep 1528973 = 573365) (by norm_num)
theorem B3134629 : Blo 1016603 3134629 := bbase (se 4 (by rfl) ⟨293871, by rfl⟩ : syracuseStep 3134629 = 587743) (by norm_num)
theorem B1528997 : Blo 1016603 1528997 := bbase (se 4 (by rfl) ⟨143343, by rfl⟩ : syracuseStep 1528997 = 286687) (by norm_num)
theorem B1529021 : Blo 1016603 1529021 := bbase (se 3 (by rfl) ⟨286691, by rfl⟩ : syracuseStep 1529021 = 573383) (by norm_num)
theorem B1529045 : Blo 1016603 1529045 := bbase (se 7 (by rfl) ⟨17918, by rfl⟩ : syracuseStep 1529045 = 35837) (by norm_num)
theorem B1529069 : Blo 1016603 1529069 := bbase (se 3 (by rfl) ⟨286700, by rfl⟩ : syracuseStep 1529069 = 573401) (by norm_num)
theorem B2577653 : Blo 1016603 2577653 := bbase (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) (by norm_num)
theorem B1529093 : Blo 1016603 1529093 := bbase (se 4 (by rfl) ⟨143352, by rfl⟩ : syracuseStep 1529093 = 286705) (by norm_num)
theorem B5166341 : Blo 1016603 5166341 := bbase (se 4 (by rfl) ⟨484344, by rfl⟩ : syracuseStep 5166341 = 968689) (by norm_num)
theorem B2446613 : Blo 1016603 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B1529117 : Blo 1016603 1529117 := bbase (se 3 (by rfl) ⟨286709, by rfl⟩ : syracuseStep 1529117 = 573419) (by norm_num)
theorem B3265829 : Blo 1016603 3265829 := bbase (se 4 (by rfl) ⟨306171, by rfl⟩ : syracuseStep 3265829 = 612343) (by norm_num)
theorem B1529141 : Blo 1016603 1529141 := bbase (se 5 (by rfl) ⟨71678, by rfl⟩ : syracuseStep 1529141 = 143357) (by norm_num)
theorem B1529165 : Blo 1016603 1529165 := bbase (se 3 (by rfl) ⟨286718, by rfl⟩ : syracuseStep 1529165 = 573437) (by norm_num)
theorem B11621717 : Blo 1016603 11621717 := bbase (se 18 (by rfl) ⟨66, by rfl⟩ : syracuseStep 11621717 = 133) (by norm_num)
theorem B1529189 : Blo 1016603 1529189 := bbase (se 4 (by rfl) ⟨143361, by rfl⟩ : syracuseStep 1529189 = 286723) (by norm_num)
theorem B1529213 : Blo 1016603 1529213 := bbase (se 3 (by rfl) ⟨286727, by rfl⟩ : syracuseStep 1529213 = 573455) (by norm_num)
theorem B1529237 : Blo 1016603 1529237 := bbase (se 6 (by rfl) ⟨35841, by rfl⟩ : syracuseStep 1529237 = 71683) (by norm_num)
theorem B1529261 : Blo 1016603 1529261 := bbase (se 3 (by rfl) ⟨286736, by rfl⟩ : syracuseStep 1529261 = 573473) (by norm_num)
theorem B2577845 : Blo 1016603 2577845 := bbase (se 5 (by rfl) ⟨120836, by rfl⟩ : syracuseStep 2577845 = 241673) (by norm_num)
theorem B1529285 : Blo 1016603 1529285 := bbase (se 4 (by rfl) ⟨143370, by rfl⟩ : syracuseStep 1529285 = 286741) (by norm_num)
theorem B2446805 : Blo 1016603 2446805 := bbase (se 7 (by rfl) ⟨28673, by rfl⟩ : syracuseStep 2446805 = 57347) (by norm_num)
theorem B1529309 : Blo 1016603 1529309 := bbase (se 3 (by rfl) ⟨286745, by rfl⟩ : syracuseStep 1529309 = 573491) (by norm_num)
theorem B1529333 : Blo 1016603 1529333 := bbase (se 5 (by rfl) ⟨71687, by rfl⟩ : syracuseStep 1529333 = 143375) (by norm_num)
theorem B1529357 : Blo 1016603 1529357 := bbase (se 3 (by rfl) ⟨286754, by rfl⟩ : syracuseStep 1529357 = 573509) (by norm_num)
theorem B1529381 : Blo 1016603 1529381 := bbase (se 4 (by rfl) ⟨143379, by rfl⟩ : syracuseStep 1529381 = 286759) (by norm_num)
theorem B1529405 : Blo 1016603 1529405 := bbase (se 3 (by rfl) ⟨286763, by rfl⟩ : syracuseStep 1529405 = 573527) (by norm_num)
theorem B1529429 : Blo 1016603 1529429 := bbase (se 8 (by rfl) ⟨8961, by rfl⟩ : syracuseStep 1529429 = 17923) (by norm_num)
theorem B1529453 : Blo 1016603 1529453 := bbase (se 3 (by rfl) ⟨286772, by rfl⟩ : syracuseStep 1529453 = 573545) (by norm_num)
theorem B1529477 : Blo 1016603 1529477 := bbase (se 4 (by rfl) ⟨143388, by rfl⟩ : syracuseStep 1529477 = 286777) (by norm_num)
theorem B1529501 : Blo 1016603 1529501 := bbase (se 3 (by rfl) ⟨286781, by rfl⟩ : syracuseStep 1529501 = 573563) (by norm_num)
theorem B2479781 : Blo 1016603 2479781 := bbase (se 4 (by rfl) ⟨232479, by rfl⟩ : syracuseStep 2479781 = 464959) (by norm_num)
theorem B1529525 : Blo 1016603 1529525 := bbase (se 5 (by rfl) ⟨71696, by rfl⟩ : syracuseStep 1529525 = 143393) (by norm_num)
theorem B1529549 : Blo 1016603 1529549 := bbase (se 3 (by rfl) ⟨286790, by rfl⟩ : syracuseStep 1529549 = 573581) (by norm_num)
theorem B33052373 : Blo 1016603 33052373 := bbase (se 7 (by rfl) ⟨387332, by rfl⟩ : syracuseStep 33052373 = 774665) (by norm_num)
theorem B1529573 : Blo 1016603 1529573 := bbase (se 4 (by rfl) ⟨143397, by rfl⟩ : syracuseStep 1529573 = 286795) (by norm_num)
theorem B1529597 : Blo 1016603 1529597 := bbase (se 3 (by rfl) ⟨286799, by rfl⟩ : syracuseStep 1529597 = 573599) (by norm_num)
theorem B2578189 : Blo 1016603 2578189 := bbase (se 3 (by rfl) ⟨483410, by rfl⟩ : syracuseStep 2578189 = 966821) (by norm_num)
theorem B1529621 : Blo 1016603 1529621 := bbase (se 6 (by rfl) ⟨35850, by rfl⟩ : syracuseStep 1529621 = 71701) (by norm_num)
theorem B1529645 : Blo 1016603 1529645 := bbase (se 3 (by rfl) ⟨286808, by rfl⟩ : syracuseStep 1529645 = 573617) (by norm_num)
theorem B1529669 : Blo 1016603 1529669 := bbase (se 4 (by rfl) ⟨143406, by rfl⟩ : syracuseStep 1529669 = 286813) (by norm_num)
theorem B1529693 : Blo 1016603 1529693 := bbase (se 3 (by rfl) ⟨286817, by rfl⟩ : syracuseStep 1529693 = 573635) (by norm_num)
theorem B1529717 : Blo 1016603 1529717 := bbase (se 5 (by rfl) ⟨71705, by rfl⟩ : syracuseStep 1529717 = 143411) (by norm_num)
theorem B2578301 : Blo 1016603 2578301 := bbase (se 3 (by rfl) ⟨483431, by rfl⟩ : syracuseStep 2578301 = 966863) (by norm_num)
theorem B1529741 : Blo 1016603 1529741 := bbase (se 3 (by rfl) ⟨286826, by rfl⟩ : syracuseStep 1529741 = 573653) (by norm_num)
theorem B1529765 : Blo 1016603 1529765 := bbase (se 4 (by rfl) ⟨143415, by rfl⟩ : syracuseStep 1529765 = 286831) (by norm_num)
theorem B1529789 : Blo 1016603 1529789 := bbase (se 3 (by rfl) ⟨286835, by rfl⟩ : syracuseStep 1529789 = 573671) (by norm_num)
theorem B1529813 : Blo 1016603 1529813 := bbase (se 7 (by rfl) ⟨17927, by rfl⟩ : syracuseStep 1529813 = 35855) (by norm_num)
theorem B4347877 : Blo 1016603 4347877 := bbase (se 4 (by rfl) ⟨407613, by rfl⟩ : syracuseStep 4347877 = 815227) (by norm_num)
theorem B1529837 : Blo 1016603 1529837 := bbase (se 3 (by rfl) ⟨286844, by rfl⟩ : syracuseStep 1529837 = 573689) (by norm_num)
theorem B4347893 : Blo 1016603 4347893 := bbase (se 5 (by rfl) ⟨203807, by rfl⟩ : syracuseStep 4347893 = 407615) (by norm_num)
theorem B1529861 : Blo 1016603 1529861 := bbase (se 4 (by rfl) ⟨143424, by rfl⟩ : syracuseStep 1529861 = 286849) (by norm_num)
theorem B1529885 : Blo 1016603 1529885 := bbase (se 3 (by rfl) ⟨286853, by rfl⟩ : syracuseStep 1529885 = 573707) (by norm_num)
theorem B1529909 : Blo 1016603 1529909 := bbase (se 5 (by rfl) ⟨71714, by rfl⟩ : syracuseStep 1529909 = 143429) (by norm_num)
theorem B2578493 : Blo 1016603 2578493 := bbase (se 3 (by rfl) ⟨483467, by rfl⟩ : syracuseStep 2578493 = 966935) (by norm_num)
theorem B1529933 : Blo 1016603 1529933 := bbase (se 3 (by rfl) ⟨286862, by rfl⟩ : syracuseStep 1529933 = 573725) (by norm_num)
theorem B1529957 : Blo 1016603 1529957 := bbase (se 4 (by rfl) ⟨143433, by rfl⟩ : syracuseStep 1529957 = 286867) (by norm_num)
theorem B1529981 : Blo 1016603 1529981 := bbase (se 3 (by rfl) ⟨286871, by rfl⟩ : syracuseStep 1529981 = 573743) (by norm_num)
theorem B1530005 : Blo 1016603 1530005 := bbase (se 6 (by rfl) ⟨35859, by rfl⟩ : syracuseStep 1530005 = 71719) (by norm_num)
theorem B1530029 : Blo 1016603 1530029 := bbase (se 3 (by rfl) ⟨286880, by rfl⟩ : syracuseStep 1530029 = 573761) (by norm_num)
theorem B2119861 : Blo 1016603 2119861 := bbase (se 5 (by rfl) ⟨99368, by rfl⟩ : syracuseStep 2119861 = 198737) (by norm_num)
theorem B1530053 : Blo 1016603 1530053 := bbase (se 4 (by rfl) ⟨143442, by rfl⟩ : syracuseStep 1530053 = 286885) (by norm_num)
theorem B1530077 : Blo 1016603 1530077 := bbase (se 3 (by rfl) ⟨286889, by rfl⟩ : syracuseStep 1530077 = 573779) (by norm_num)
theorem B1530101 : Blo 1016603 1530101 := bbase (se 5 (by rfl) ⟨71723, by rfl⟩ : syracuseStep 1530101 = 143447) (by norm_num)
theorem B1530125 : Blo 1016603 1530125 := bbase (se 3 (by rfl) ⟨286898, by rfl⟩ : syracuseStep 1530125 = 573797) (by norm_num)
theorem B1530149 : Blo 1016603 1530149 := bbase (se 4 (by rfl) ⟨143451, by rfl⟩ : syracuseStep 1530149 = 286903) (by norm_num)
theorem B1628461 : Blo 1016603 1628461 := bbase (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) (by norm_num)
theorem B1530173 : Blo 1016603 1530173 := bbase (se 3 (by rfl) ⟨286907, by rfl⟩ : syracuseStep 1530173 = 573815) (by norm_num)
theorem B1530197 : Blo 1016603 1530197 := bbase (se 10 (by rfl) ⟨2241, by rfl⟩ : syracuseStep 1530197 = 4483) (by norm_num)
theorem B1530221 : Blo 1016603 1530221 := bbase (se 3 (by rfl) ⟨286916, by rfl⟩ : syracuseStep 1530221 = 573833) (by norm_num)
theorem B1530245 : Blo 1016603 1530245 := bbase (se 4 (by rfl) ⟨143460, by rfl⟩ : syracuseStep 1530245 = 286921) (by norm_num)
theorem B2578837 : Blo 1016603 2578837 := bbase (se 6 (by rfl) ⟨60441, by rfl⟩ : syracuseStep 2578837 = 120883) (by norm_num)
theorem B1530269 : Blo 1016603 1530269 := bbase (se 3 (by rfl) ⟨286925, by rfl⟩ : syracuseStep 1530269 = 573851) (by norm_num)
theorem B1530293 : Blo 1016603 1530293 := bbase (se 5 (by rfl) ⟨71732, by rfl⟩ : syracuseStep 1530293 = 143465) (by norm_num)
theorem B1530317 : Blo 1016603 1530317 := bbase (se 3 (by rfl) ⟨286934, by rfl⟩ : syracuseStep 1530317 = 573869) (by norm_num)
theorem B1530341 : Blo 1016603 1530341 := bbase (se 4 (by rfl) ⟨143469, by rfl⟩ : syracuseStep 1530341 = 286939) (by norm_num)
theorem B1530365 : Blo 1016603 1530365 := bbase (se 3 (by rfl) ⟨286943, by rfl⟩ : syracuseStep 1530365 = 573887) (by norm_num)
theorem B2578949 : Blo 1016603 2578949 := bbase (se 4 (by rfl) ⟨241776, by rfl⟩ : syracuseStep 2578949 = 483553) (by norm_num)
theorem B1530389 : Blo 1016603 1530389 := bbase (se 6 (by rfl) ⟨35868, by rfl⟩ : syracuseStep 1530389 = 71737) (by norm_num)
theorem B1530413 : Blo 1016603 1530413 := bbase (se 3 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 1530413 = 573905) (by norm_num)
theorem B1530437 : Blo 1016603 1530437 := bbase (se 4 (by rfl) ⟨143478, by rfl⟩ : syracuseStep 1530437 = 286957) (by norm_num)
theorem B1530461 : Blo 1016603 1530461 := bbase (se 3 (by rfl) ⟨286961, by rfl⟩ : syracuseStep 1530461 = 573923) (by norm_num)
theorem B3267173 : Blo 1016603 3267173 := bbase (se 4 (by rfl) ⟨306297, by rfl⟩ : syracuseStep 3267173 = 612595) (by norm_num)
theorem B1530485 : Blo 1016603 1530485 := bbase (se 5 (by rfl) ⟨71741, by rfl⟩ : syracuseStep 1530485 = 143483) (by norm_num)
theorem B1530509 : Blo 1016603 1530509 := bbase (se 3 (by rfl) ⟨286970, by rfl⟩ : syracuseStep 1530509 = 573941) (by norm_num)
theorem B1530533 : Blo 1016603 1530533 := bbase (se 4 (by rfl) ⟨143487, by rfl⟩ : syracuseStep 1530533 = 286975) (by norm_num)
theorem B1530557 : Blo 1016603 1530557 := bbase (se 3 (by rfl) ⟨286979, by rfl⟩ : syracuseStep 1530557 = 573959) (by norm_num)
theorem B2579141 : Blo 1016603 2579141 := bbase (se 4 (by rfl) ⟨241794, by rfl⟩ : syracuseStep 2579141 = 483589) (by norm_num)
theorem B1628885 : Blo 1016603 1628885 := bbase (se 7 (by rfl) ⟨19088, by rfl⟩ : syracuseStep 1628885 = 38177) (by norm_num)
theorem B1530581 : Blo 1016603 1530581 := bbase (se 7 (by rfl) ⟨17936, by rfl⟩ : syracuseStep 1530581 = 35873) (by norm_num)
theorem B2579165 : Blo 1016603 2579165 := bbase (se 3 (by rfl) ⟨483593, by rfl⟩ : syracuseStep 2579165 = 967187) (by norm_num)
theorem B1530605 : Blo 1016603 1530605 := bbase (se 3 (by rfl) ⟨286988, by rfl⟩ : syracuseStep 1530605 = 573977) (by norm_num)
theorem B1530629 : Blo 1016603 1530629 := bbase (se 4 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 1530629 = 286993) (by norm_num)
theorem B1530653 : Blo 1016603 1530653 := bbase (se 3 (by rfl) ⟨286997, by rfl⟩ : syracuseStep 1530653 = 573995) (by norm_num)
theorem B1530677 : Blo 1016603 1530677 := bbase (se 5 (by rfl) ⟨71750, by rfl⟩ : syracuseStep 1530677 = 143501) (by norm_num)
theorem B1530701 : Blo 1016603 1530701 := bbase (se 3 (by rfl) ⟨287006, by rfl⟩ : syracuseStep 1530701 = 574013) (by norm_num)
theorem B1530725 : Blo 1016603 1530725 := bbase (se 4 (by rfl) ⟨143505, by rfl⟩ : syracuseStep 1530725 = 287011) (by norm_num)
theorem B1530749 : Blo 1016603 1530749 := bbase (se 3 (by rfl) ⟨287015, by rfl⟩ : syracuseStep 1530749 = 574031) (by norm_num)
theorem B1530773 : Blo 1016603 1530773 := bbase (se 6 (by rfl) ⟨35877, by rfl⟩ : syracuseStep 1530773 = 71755) (by norm_num)
theorem B1530797 : Blo 1016603 1530797 := bbase (se 3 (by rfl) ⟨287024, by rfl⟩ : syracuseStep 1530797 = 574049) (by norm_num)
theorem B1530821 : Blo 1016603 1530821 := bbase (se 4 (by rfl) ⟨143514, by rfl⟩ : syracuseStep 1530821 = 287029) (by norm_num)
theorem B1530845 : Blo 1016603 1530845 := bbase (se 3 (by rfl) ⟨287033, by rfl⟩ : syracuseStep 1530845 = 574067) (by norm_num)
theorem B1629173 : Blo 1016603 1629173 := bbase (se 5 (by rfl) ⟨76367, by rfl⟩ : syracuseStep 1629173 = 152735) (by norm_num)
theorem B1530869 : Blo 1016603 1530869 := bbase (se 5 (by rfl) ⟨71759, by rfl⟩ : syracuseStep 1530869 = 143519) (by norm_num)
theorem B3431429 : Blo 1016603 3431429 := bbase (se 4 (by rfl) ⟨321696, by rfl⟩ : syracuseStep 3431429 = 643393) (by norm_num)
theorem B1530893 : Blo 1016603 1530893 := bbase (se 3 (by rfl) ⟨287042, by rfl⟩ : syracuseStep 1530893 = 574085) (by norm_num)
theorem B2579485 : Blo 1016603 2579485 := bbase (se 3 (by rfl) ⟨483653, by rfl⟩ : syracuseStep 2579485 = 967307) (by norm_num)
theorem B2579597 : Blo 1016603 2579597 := bbase (se 3 (by rfl) ⟨483674, by rfl⟩ : syracuseStep 2579597 = 967349) (by norm_num)
theorem B2579789 : Blo 1016603 2579789 := bbase (se 3 (by rfl) ⟨483710, by rfl⟩ : syracuseStep 2579789 = 967421) (by norm_num)
theorem B2448805 : Blo 1016603 2448805 := bbase (se 4 (by rfl) ⟨229575, by rfl⟩ : syracuseStep 2448805 = 459151) (by norm_num)
theorem B3431861 : Blo 1016603 3431861 := bbase (se 5 (by rfl) ⟨160868, by rfl⟩ : syracuseStep 3431861 = 321737) (by norm_num)
theorem B2580133 : Blo 1016603 2580133 := bbase (se 4 (by rfl) ⟨241887, by rfl⟩ : syracuseStep 2580133 = 483775) (by norm_num)
theorem B1629973 : Blo 1016603 1629973 := bbase (se 6 (by rfl) ⟨38202, by rfl⟩ : syracuseStep 1629973 = 76405) (by norm_num)
theorem B2580245 : Blo 1016603 2580245 := bbase (se 6 (by rfl) ⟨60474, by rfl⟩ : syracuseStep 2580245 = 120949) (by norm_num)
theorem B4415285 : Blo 1016603 4415285 := bbase (se 5 (by rfl) ⟨206966, by rfl⟩ : syracuseStep 4415285 = 413933) (by norm_num)
theorem B3432293 : Blo 1016603 3432293 := bbase (se 4 (by rfl) ⟨321777, by rfl⟩ : syracuseStep 3432293 = 643555) (by norm_num)
theorem B2580437 : Blo 1016603 2580437 := bbase (se 7 (by rfl) ⟨30239, by rfl⟩ : syracuseStep 2580437 = 60479) (by norm_num)
theorem B2449381 : Blo 1016603 2449381 := bbase (se 4 (by rfl) ⟨229629, by rfl⟩ : syracuseStep 2449381 = 459259) (by norm_num)
theorem B2384005 : Blo 1016603 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B4350149 : Blo 1016603 4350149 := bbase (se 4 (by rfl) ⟨407826, by rfl⟩ : syracuseStep 4350149 = 815653) (by norm_num)
theorem B3432725 : Blo 1016603 3432725 := bbase (se 6 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 3432725 = 160909) (by norm_num)
theorem B2449709 : Blo 1016603 2449709 := bbase (se 3 (by rfl) ⟨459320, by rfl⟩ : syracuseStep 2449709 = 918641) (by norm_num)
theorem B2580781 : Blo 1016603 2580781 := bbase (se 3 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 2580781 = 967793) (by norm_num)
theorem B1630525 : Blo 1016603 1630525 := bbase (se 3 (by rfl) ⟨305723, by rfl⟩ : syracuseStep 1630525 = 611447) (by norm_num)
theorem B2449765 : Blo 1016603 2449765 := bbase (se 4 (by rfl) ⟨229665, by rfl⟩ : syracuseStep 2449765 = 459331) (by norm_num)
theorem B2580893 : Blo 1016603 2580893 := bbase (se 3 (by rfl) ⟨483917, by rfl⟩ : syracuseStep 2580893 = 967835) (by norm_num)
theorem B2089405 : Blo 1016603 2089405 := bbase (se 3 (by rfl) ⟨391763, by rfl⟩ : syracuseStep 2089405 = 783527) (by norm_num)
theorem B5366245 : Blo 1016603 5366245 := bbase (se 4 (by rfl) ⟨503085, by rfl⟩ : syracuseStep 5366245 = 1006171) (by norm_num)
theorem B3269173 : Blo 1016603 3269173 := bbase (se 5 (by rfl) ⟨153242, by rfl⟩ : syracuseStep 3269173 = 306485) (by norm_num)
theorem B1630781 : Blo 1016603 1630781 := bbase (se 3 (by rfl) ⟨305771, by rfl⟩ : syracuseStep 1630781 = 611543) (by norm_num)
theorem B2449997 : Blo 1016603 2449997 := bbase (se 3 (by rfl) ⟨459374, by rfl⟩ : syracuseStep 2449997 = 918749) (by norm_num)
theorem B2581085 : Blo 1016603 2581085 := bbase (se 3 (by rfl) ⟨483953, by rfl⟩ : syracuseStep 2581085 = 967907) (by norm_num)
theorem B3433157 : Blo 1016603 3433157 := bbase (se 4 (by rfl) ⟨321858, by rfl⟩ : syracuseStep 3433157 = 643717) (by norm_num)
theorem B6972149 : Blo 1016603 6972149 := bbase (se 5 (by rfl) ⟨326819, by rfl⟩ : syracuseStep 6972149 = 653639) (by norm_num)
theorem B2450189 : Blo 1016603 2450189 := bbase (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) (by norm_num)
theorem B7725941 : Blo 1016603 7725941 := bbase (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) (by norm_num)
theorem B2581429 : Blo 1016603 2581429 := bbase (se 5 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 2581429 = 242009) (by norm_num)
theorem B2581541 : Blo 1016603 2581541 := bbase (se 4 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 2581541 = 484039) (by norm_num)
theorem B2319445 : Blo 1016603 2319445 := bbase (se 8 (by rfl) ⟨13590, by rfl⟩ : syracuseStep 2319445 = 27181) (by norm_num)
theorem B3433589 : Blo 1016603 3433589 := bbase (se 5 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 3433589 = 321899) (by norm_num)
theorem B5235845 : Blo 1016603 5235845 := bbase (se 4 (by rfl) ⟨490860, by rfl⟩ : syracuseStep 5235845 = 981721) (by norm_num)
theorem B2581733 : Blo 1016603 2581733 := bbase (se 4 (by rfl) ⟨242037, by rfl⟩ : syracuseStep 2581733 = 484075) (by norm_num)
theorem B1631485 : Blo 1016603 1631485 := bbase (se 3 (by rfl) ⟨305903, by rfl⟩ : syracuseStep 1631485 = 611807) (by norm_num)
theorem B1860989 : Blo 1016603 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B3434021 : Blo 1016603 3434021 := bbase (se 4 (by rfl) ⟨321939, by rfl⟩ : syracuseStep 3434021 = 643879) (by norm_num)
theorem B2582077 : Blo 1016603 2582077 := bbase (se 3 (by rfl) ⟨484139, by rfl⟩ : syracuseStep 2582077 = 968279) (by norm_num)
theorem B1631909 : Blo 1016603 1631909 := bbase (se 4 (by rfl) ⟨152991, by rfl⟩ : syracuseStep 1631909 = 305983) (by norm_num)
theorem B2582189 : Blo 1016603 2582189 := bbase (se 3 (by rfl) ⟨484160, by rfl⟩ : syracuseStep 2582189 = 968321) (by norm_num)
theorem B2451149 : Blo 1016603 2451149 := bbase (se 3 (by rfl) ⟨459590, by rfl⟩ : syracuseStep 2451149 = 919181) (by norm_num)
theorem B1304365 : Blo 1016603 1304365 := bbase (se 3 (by rfl) ⟨244568, by rfl⟩ : syracuseStep 1304365 = 489137) (by norm_num)
theorem B2287421 : Blo 1016603 2287421 := bbase (se 3 (by rfl) ⟨428891, by rfl⟩ : syracuseStep 2287421 = 857783) (by norm_num)
theorem B2582381 : Blo 1016603 2582381 := bbase (se 3 (by rfl) ⟨484196, by rfl⟩ : syracuseStep 2582381 = 968393) (by norm_num)
theorem B2287493 : Blo 1016603 2287493 := bbase (se 4 (by rfl) ⟨214452, by rfl⟩ : syracuseStep 2287493 = 428905) (by norm_num)
theorem B3860405 : Blo 1016603 3860405 := bbase (se 5 (by rfl) ⟨180956, by rfl⟩ : syracuseStep 3860405 = 361913) (by norm_num)
theorem B1632197 : Blo 1016603 1632197 := bbase (se 4 (by rfl) ⟨153018, by rfl⟩ : syracuseStep 1632197 = 306037) (by norm_num)
theorem B2287565 : Blo 1016603 2287565 := bbase (se 3 (by rfl) ⟨428918, by rfl⟩ : syracuseStep 2287565 = 857837) (by norm_num)
theorem B3434453 : Blo 1016603 3434453 := bbase (se 7 (by rfl) ⟨40247, by rfl⟩ : syracuseStep 3434453 = 80495) (by norm_num)
theorem B2287637 : Blo 1016603 2287637 := bbase (se 6 (by rfl) ⟨53616, by rfl⟩ : syracuseStep 2287637 = 107233) (by norm_num)
theorem B2287709 : Blo 1016603 2287709 := bbase (se 3 (by rfl) ⟨428945, by rfl⟩ : syracuseStep 2287709 = 857891) (by norm_num)
theorem B2287781 : Blo 1016603 2287781 := bbase (se 4 (by rfl) ⟨214479, by rfl⟩ : syracuseStep 2287781 = 428959) (by norm_num)
theorem B1632421 : Blo 1016603 1632421 := bbase (se 4 (by rfl) ⟨153039, by rfl⟩ : syracuseStep 1632421 = 306079) (by norm_num)
theorem B1960133 : Blo 1016603 1960133 := bbase (se 4 (by rfl) ⟨183762, by rfl⟩ : syracuseStep 1960133 = 367525) (by norm_num)
theorem B2582725 : Blo 1016603 2582725 := bbase (se 4 (by rfl) ⟨242130, by rfl⟩ : syracuseStep 2582725 = 484261) (by norm_num)
theorem B3860693 : Blo 1016603 3860693 := bbase (se 7 (by rfl) ⟨45242, by rfl⟩ : syracuseStep 3860693 = 90485) (by norm_num)
theorem B2320613 : Blo 1016603 2320613 := bbase (se 4 (by rfl) ⟨217557, by rfl⟩ : syracuseStep 2320613 = 435115) (by norm_num)
theorem B2287853 : Blo 1016603 2287853 := bbase (se 3 (by rfl) ⟨428972, by rfl⟩ : syracuseStep 2287853 = 857945) (by norm_num)
theorem B2287925 : Blo 1016603 2287925 := bbase (se 5 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 2287925 = 214493) (by norm_num)
theorem B2582837 : Blo 1016603 2582837 := bbase (se 5 (by rfl) ⟨121070, by rfl⟩ : syracuseStep 2582837 = 242141) (by norm_num)
theorem B2287997 : Blo 1016603 2287997 := bbase (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) (by norm_num)
theorem B3434885 : Blo 1016603 3434885 := bbase (se 4 (by rfl) ⟨322020, by rfl⟩ : syracuseStep 3434885 = 644041) (by norm_num)
theorem B2288069 : Blo 1016603 2288069 := bbase (se 4 (by rfl) ⟨214506, by rfl⟩ : syracuseStep 2288069 = 429013) (by norm_num)
theorem B2583029 : Blo 1016603 2583029 := bbase (se 5 (by rfl) ⟨121079, by rfl⟩ : syracuseStep 2583029 = 242159) (by norm_num)
theorem B2288141 : Blo 1016603 2288141 := bbase (se 3 (by rfl) ⟨429026, by rfl⟩ : syracuseStep 2288141 = 858053) (by norm_num)
theorem B3926549 : Blo 1016603 3926549 := bbase (se 6 (by rfl) ⟨92028, by rfl⟩ : syracuseStep 3926549 = 184057) (by norm_num)
theorem B2288213 : Blo 1016603 2288213 := bbase (se 8 (by rfl) ⟨13407, by rfl⟩ : syracuseStep 2288213 = 26815) (by norm_num)
theorem B2288285 : Blo 1016603 2288285 := bbase (se 3 (by rfl) ⟨429053, by rfl⟩ : syracuseStep 2288285 = 858107) (by norm_num)
theorem B2288357 : Blo 1016603 2288357 := bbase (se 4 (by rfl) ⟨214533, by rfl⟩ : syracuseStep 2288357 = 429067) (by norm_num)
theorem B3304165 : Blo 1016603 3304165 := bbase (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) (by norm_num)
theorem B2616077 : Blo 1016603 2616077 := bbase (se 3 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 2616077 = 981029) (by norm_num)
theorem B2288429 : Blo 1016603 2288429 := bbase (se 3 (by rfl) ⟨429080, by rfl⟩ : syracuseStep 2288429 = 858161) (by norm_num)
theorem B3435317 : Blo 1016603 3435317 := bbase (se 5 (by rfl) ⟨161030, by rfl⟩ : syracuseStep 3435317 = 322061) (by norm_num)
theorem B2583373 : Blo 1016603 2583373 := bbase (se 3 (by rfl) ⟨484382, by rfl⟩ : syracuseStep 2583373 = 968765) (by norm_num)
theorem B1862509 : Blo 1016603 1862509 := bbase (se 3 (by rfl) ⟨349220, by rfl⟩ : syracuseStep 1862509 = 698441) (by norm_num)
theorem B2288501 : Blo 1016603 2288501 := bbase (se 5 (by rfl) ⟨107273, by rfl⟩ : syracuseStep 2288501 = 214547) (by norm_num)
theorem B2288573 : Blo 1016603 2288573 := bbase (se 3 (by rfl) ⟨429107, by rfl⟩ : syracuseStep 2288573 = 858215) (by norm_num)
theorem B4025285 : Blo 1016603 4025285 := bbase (se 4 (by rfl) ⟨377370, by rfl⟩ : syracuseStep 4025285 = 754741) (by norm_num)
theorem B2288645 : Blo 1016603 2288645 := bbase (se 4 (by rfl) ⟨214560, by rfl⟩ : syracuseStep 2288645 = 429121) (by norm_num)
theorem B2288717 : Blo 1016603 2288717 := bbase (se 3 (by rfl) ⟨429134, by rfl⟩ : syracuseStep 2288717 = 858269) (by norm_num)
theorem B2616437 : Blo 1016603 2616437 := bbase (se 5 (by rfl) ⟨122645, by rfl⟩ : syracuseStep 2616437 = 245291) (by norm_num)
theorem B2288789 : Blo 1016603 2288789 := bbase (se 6 (by rfl) ⟨53643, by rfl⟩ : syracuseStep 2288789 = 107287) (by norm_num)
theorem B6515893 : Blo 1016603 6515893 := bbase (se 5 (by rfl) ⟨305432, by rfl⟩ : syracuseStep 6515893 = 610865) (by norm_num)
theorem B1961165 : Blo 1016603 1961165 := bbase (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) (by norm_num)
theorem B2288861 : Blo 1016603 2288861 := bbase (se 3 (by rfl) ⟨429161, by rfl⟩ : syracuseStep 2288861 = 858323) (by norm_num)
theorem B3435749 : Blo 1016603 3435749 := bbase (se 4 (by rfl) ⟨322101, by rfl⟩ : syracuseStep 3435749 = 644203) (by norm_num)
theorem B1633549 : Blo 1016603 1633549 := bbase (se 3 (by rfl) ⟨306290, by rfl⟩ : syracuseStep 1633549 = 612581) (by norm_num)
theorem B2288933 : Blo 1016603 2288933 := bbase (se 4 (by rfl) ⟨214587, by rfl⟩ : syracuseStep 2288933 = 429175) (by norm_num)
theorem B3140965 : Blo 1016603 3140965 := bbase (se 4 (by rfl) ⟨294465, by rfl⟩ : syracuseStep 3140965 = 588931) (by norm_num)
theorem B2289005 : Blo 1016603 2289005 := bbase (se 3 (by rfl) ⟨429188, by rfl⟩ : syracuseStep 2289005 = 858377) (by norm_num)
theorem B3861877 : Blo 1016603 3861877 := bbase (se 5 (by rfl) ⟨181025, by rfl⟩ : syracuseStep 3861877 = 362051) (by norm_num)
theorem B2289077 : Blo 1016603 2289077 := bbase (se 5 (by rfl) ⟨107300, by rfl⟩ : syracuseStep 2289077 = 214601) (by norm_num)
theorem B1764821 : Blo 1016603 1764821 := bbase (se 7 (by rfl) ⟨20681, by rfl⟩ : syracuseStep 1764821 = 41363) (by norm_num)
theorem B3141109 : Blo 1016603 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B2289149 : Blo 1016603 2289149 := bbase (se 3 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 2289149 = 858431) (by norm_num)
theorem B1961533 : Blo 1016603 1961533 := bbase (se 3 (by rfl) ⟨367787, by rfl⟩ : syracuseStep 1961533 = 735575) (by norm_num)
theorem B2289221 : Blo 1016603 2289221 := bbase (se 4 (by rfl) ⟨214614, by rfl⟩ : syracuseStep 2289221 = 429229) (by norm_num)
theorem B2944613 : Blo 1016603 2944613 := bbase (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) (by norm_num)
theorem B2289293 : Blo 1016603 2289293 := bbase (se 3 (by rfl) ⟨429242, by rfl⟩ : syracuseStep 2289293 = 858485) (by norm_num)
theorem B3436181 : Blo 1016603 3436181 := bbase (se 6 (by rfl) ⟨80535, by rfl⟩ : syracuseStep 3436181 = 161071) (by norm_num)
theorem B3862181 : Blo 1016603 3862181 := bbase (se 4 (by rfl) ⟨362079, by rfl⟩ : syracuseStep 3862181 = 724159) (by norm_num)
theorem B1633997 : Blo 1016603 1633997 := bbase (se 3 (by rfl) ⟨306374, by rfl⟩ : syracuseStep 1633997 = 612749) (by norm_num)
theorem B2289365 : Blo 1016603 2289365 := bbase (se 7 (by rfl) ⟨26828, by rfl⟩ : syracuseStep 2289365 = 53657) (by norm_num)
theorem B2289437 : Blo 1016603 2289437 := bbase (se 3 (by rfl) ⟨429269, by rfl⟩ : syracuseStep 2289437 = 858539) (by norm_num)
theorem B2322245 : Blo 1016603 2322245 := bbase (se 4 (by rfl) ⟨217710, by rfl⟩ : syracuseStep 2322245 = 435421) (by norm_num)
theorem B2289509 : Blo 1016603 2289509 := bbase (se 4 (by rfl) ⟨214641, by rfl⟩ : syracuseStep 2289509 = 429283) (by norm_num)
theorem B2289581 : Blo 1016603 2289581 := bbase (se 3 (by rfl) ⟨429296, by rfl⟩ : syracuseStep 2289581 = 858593) (by norm_num)
theorem B1961957 : Blo 1016603 1961957 := bbase (se 4 (by rfl) ⟨183933, by rfl⟩ : syracuseStep 1961957 = 367867) (by norm_num)
theorem B2289653 : Blo 1016603 2289653 := bbase (se 5 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 2289653 = 214655) (by norm_num)
theorem B2322445 : Blo 1016603 2322445 := bbase (se 3 (by rfl) ⟨435458, by rfl⟩ : syracuseStep 2322445 = 870917) (by norm_num)
theorem B2289725 : Blo 1016603 2289725 := bbase (se 3 (by rfl) ⟨429323, by rfl⟩ : syracuseStep 2289725 = 858647) (by norm_num)
theorem B3436613 : Blo 1016603 3436613 := bbase (se 4 (by rfl) ⟨322182, by rfl⟩ : syracuseStep 3436613 = 644365) (by norm_num)
theorem B2289797 : Blo 1016603 2289797 := bbase (se 4 (by rfl) ⟨214668, by rfl⟩ : syracuseStep 2289797 = 429337) (by norm_num)
theorem B4354181 : Blo 1016603 4354181 := bbase (se 4 (by rfl) ⟨408204, by rfl⟩ : syracuseStep 4354181 = 816409) (by norm_num)
theorem B1863869 : Blo 1016603 1863869 := bbase (se 3 (by rfl) ⟨349475, by rfl⟩ : syracuseStep 1863869 = 698951) (by norm_num)
theorem B2289869 : Blo 1016603 2289869 := bbase (se 3 (by rfl) ⟨429350, by rfl⟩ : syracuseStep 2289869 = 858701) (by norm_num)
theorem B2289941 : Blo 1016603 2289941 := bbase (se 6 (by rfl) ⟨53670, by rfl⟩ : syracuseStep 2289941 = 107341) (by norm_num)
theorem B1863965 : Blo 1016603 1863965 := bbase (se 3 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 1863965 = 698987) (by norm_num)
theorem B1175845 : Blo 1016603 1175845 := bbase (se 4 (by rfl) ⟨110235, by rfl⟩ : syracuseStep 1175845 = 220471) (by norm_num)
theorem B1044797 : Blo 1016603 1044797 := bbase (se 3 (by rfl) ⟨195899, by rfl⟩ : syracuseStep 1044797 = 391799) (by norm_num)
theorem B2290013 : Blo 1016603 2290013 := bbase (se 3 (by rfl) ⟨429377, by rfl⟩ : syracuseStep 2290013 = 858755) (by norm_num)
theorem B2290085 : Blo 1016603 2290085 := bbase (se 4 (by rfl) ⟨214695, by rfl⟩ : syracuseStep 2290085 = 429391) (by norm_num)
theorem B2290157 : Blo 1016603 2290157 := bbase (se 3 (by rfl) ⟨429404, by rfl⟩ : syracuseStep 2290157 = 858809) (by norm_num)
theorem B3437045 : Blo 1016603 3437045 := bbase (se 5 (by rfl) ⟨161111, by rfl⟩ : syracuseStep 3437045 = 322223) (by norm_num)
theorem B2290229 : Blo 1016603 2290229 := bbase (se 5 (by rfl) ⟨107354, by rfl⟩ : syracuseStep 2290229 = 214709) (by norm_num)
theorem B2290301 : Blo 1016603 2290301 := bbase (se 3 (by rfl) ⟨429431, by rfl⟩ : syracuseStep 2290301 = 858863) (by norm_num)
theorem B2290373 : Blo 1016603 2290373 := bbase (se 4 (by rfl) ⟨214722, by rfl⟩ : syracuseStep 2290373 = 429445) (by norm_num)
theorem B1929997 : Blo 1016603 1929997 := bbase (se 3 (by rfl) ⟨361874, by rfl⟩ : syracuseStep 1929997 = 723749) (by norm_num)
theorem B2290445 : Blo 1016603 2290445 := bbase (se 3 (by rfl) ⟨429458, by rfl⟩ : syracuseStep 2290445 = 858917) (by norm_num)
theorem B1176401 : Blo 1016603 1176401 := bbase (se 2 (by rfl) ⟨441150, by rfl⟩ : syracuseStep 1176401 = 882301) (by norm_num)
theorem B2290517 : Blo 1016603 2290517 := bbase (se 9 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 2290517 = 13421) (by norm_num)
theorem B1143697 : Blo 1016603 1143697 := bbase (se 2 (by rfl) ⟨428886, by rfl⟩ : syracuseStep 1143697 = 857773) (by norm_num)
theorem B2290589 : Blo 1016603 2290589 := bbase (se 3 (by rfl) ⟨429485, by rfl⟩ : syracuseStep 2290589 = 858971) (by norm_num)
theorem B3437477 : Blo 1016603 3437477 := bbase (se 4 (by rfl) ⟨322263, by rfl⟩ : syracuseStep 3437477 = 644527) (by norm_num)
theorem B1143733 : Blo 1016603 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B1143769 : Blo 1016603 1143769 := bbase (se 2 (by rfl) ⟨428913, by rfl⟩ : syracuseStep 1143769 = 857827) (by norm_num)
theorem B2290661 : Blo 1016603 2290661 := bbase (se 4 (by rfl) ⟨214749, by rfl⟩ : syracuseStep 2290661 = 429499) (by norm_num)
theorem B1143805 : Blo 1016603 1143805 := bbase (se 3 (by rfl) ⟨214463, by rfl⟩ : syracuseStep 1143805 = 428927) (by norm_num)
theorem B1143841 : Blo 1016603 1143841 := bbase (se 2 (by rfl) ⟨428940, by rfl⟩ : syracuseStep 1143841 = 857881) (by norm_num)
theorem B2290733 : Blo 1016603 2290733 := bbase (se 3 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 2290733 = 859025) (by norm_num)
theorem B5796917 : Blo 1016603 5796917 := bbase (se 5 (by rfl) ⟨271730, by rfl⟩ : syracuseStep 5796917 = 543461) (by norm_num)
theorem B1930301 : Blo 1016603 1930301 := bbase (se 3 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 1930301 = 723863) (by norm_num)
theorem B1143877 : Blo 1016603 1143877 := bbase (se 4 (by rfl) ⟨107238, by rfl⟩ : syracuseStep 1143877 = 214477) (by norm_num)
theorem B1143913 : Blo 1016603 1143913 := bbase (se 2 (by rfl) ⟨428967, by rfl⟩ : syracuseStep 1143913 = 857935) (by norm_num)
theorem B2290805 : Blo 1016603 2290805 := bbase (se 5 (by rfl) ⟨107381, by rfl⟩ : syracuseStep 2290805 = 214763) (by norm_num)
theorem B1143949 : Blo 1016603 1143949 := bbase (se 3 (by rfl) ⟨214490, by rfl⟩ : syracuseStep 1143949 = 428981) (by norm_num)
theorem B1143985 : Blo 1016603 1143985 := bbase (se 2 (by rfl) ⟨428994, by rfl⟩ : syracuseStep 1143985 = 857989) (by norm_num)
theorem B2290877 : Blo 1016603 2290877 := bbase (se 3 (by rfl) ⟨429539, by rfl⟩ : syracuseStep 2290877 = 859079) (by norm_num)
theorem B1144021 : Blo 1016603 1144021 := bbase (se 7 (by rfl) ⟨13406, by rfl⟩ : syracuseStep 1144021 = 26813) (by norm_num)
theorem B1144057 : Blo 1016603 1144057 := bbase (se 2 (by rfl) ⟨429021, by rfl⟩ : syracuseStep 1144057 = 858043) (by norm_num)
theorem B2290949 : Blo 1016603 2290949 := bbase (se 4 (by rfl) ⟨214776, by rfl⟩ : syracuseStep 2290949 = 429553) (by norm_num)
theorem B1144093 : Blo 1016603 1144093 := bbase (se 3 (by rfl) ⟨214517, by rfl⟩ : syracuseStep 1144093 = 429035) (by norm_num)
theorem B1144129 : Blo 1016603 1144129 := bbase (se 2 (by rfl) ⟨429048, by rfl⟩ : syracuseStep 1144129 = 858097) (by norm_num)
theorem B2291021 : Blo 1016603 2291021 := bbase (se 3 (by rfl) ⟨429566, by rfl⟩ : syracuseStep 2291021 = 859133) (by norm_num)
theorem B89257301 : Blo 1016603 89257301 := bbase (se 13 (by rfl) ⟨16343, by rfl⟩ : syracuseStep 89257301 = 32687) (by norm_num)
theorem B3437909 : Blo 1016603 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B1144165 : Blo 1016603 1144165 := bbase (se 4 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 1144165 = 214531) (by norm_num)
theorem B1144201 : Blo 1016603 1144201 := bbase (se 2 (by rfl) ⟨429075, by rfl⟩ : syracuseStep 1144201 = 858151) (by norm_num)
theorem B2291093 : Blo 1016603 2291093 := bbase (se 6 (by rfl) ⟨53697, by rfl⟩ : syracuseStep 2291093 = 107395) (by norm_num)
theorem B1144237 : Blo 1016603 1144237 := bbase (se 3 (by rfl) ⟨214544, by rfl⟩ : syracuseStep 1144237 = 429089) (by norm_num)
theorem B1144273 : Blo 1016603 1144273 := bbase (se 2 (by rfl) ⟨429102, by rfl⟩ : syracuseStep 1144273 = 858205) (by norm_num)
theorem B2291165 : Blo 1016603 2291165 := bbase (se 3 (by rfl) ⟨429593, by rfl⟩ : syracuseStep 2291165 = 859187) (by norm_num)
theorem B1471981 : Blo 1016603 1471981 := bbase (se 3 (by rfl) ⟨275996, by rfl⟩ : syracuseStep 1471981 = 551993) (by norm_num)
theorem B1144309 : Blo 1016603 1144309 := bbase (se 5 (by rfl) ⟨53639, by rfl⟩ : syracuseStep 1144309 = 107279) (by norm_num)
theorem B1144345 : Blo 1016603 1144345 := bbase (se 2 (by rfl) ⟨429129, by rfl⟩ : syracuseStep 1144345 = 858259) (by norm_num)
theorem B2291237 : Blo 1016603 2291237 := bbase (se 4 (by rfl) ⟨214803, by rfl⟩ : syracuseStep 2291237 = 429607) (by norm_num)
theorem B1144381 : Blo 1016603 1144381 := bbase (se 3 (by rfl) ⟨214571, by rfl⟩ : syracuseStep 1144381 = 429143) (by norm_num)
theorem B1144417 : Blo 1016603 1144417 := bbase (se 2 (by rfl) ⟨429156, by rfl⟩ : syracuseStep 1144417 = 858313) (by norm_num)
theorem B2291309 : Blo 1016603 2291309 := bbase (se 3 (by rfl) ⟨429620, by rfl⟩ : syracuseStep 2291309 = 859241) (by norm_num)
theorem B1767037 : Blo 1016603 1767037 := bbase (se 3 (by rfl) ⟨331319, by rfl⟩ : syracuseStep 1767037 = 662639) (by norm_num)
theorem B1144453 : Blo 1016603 1144453 := bbase (se 4 (by rfl) ⟨107292, by rfl⟩ : syracuseStep 1144453 = 214585) (by norm_num)
theorem B5502613 : Blo 1016603 5502613 := bbase (se 6 (by rfl) ⟨128967, by rfl⟩ : syracuseStep 5502613 = 257935) (by norm_num)
theorem B1144489 : Blo 1016603 1144489 := bbase (se 2 (by rfl) ⟨429183, by rfl⟩ : syracuseStep 1144489 = 858367) (by norm_num)
theorem B2291381 : Blo 1016603 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B1832653 : Blo 1016603 1832653 := bbase (se 3 (by rfl) ⟨343622, by rfl⟩ : syracuseStep 1832653 = 687245) (by norm_num)
theorem B1144525 : Blo 1016603 1144525 := bbase (se 3 (by rfl) ⟨214598, by rfl⟩ : syracuseStep 1144525 = 429197) (by norm_num)
theorem B3864293 : Blo 1016603 3864293 := bbase (se 4 (by rfl) ⟨362277, by rfl⟩ : syracuseStep 3864293 = 724555) (by norm_num)
theorem B1144561 : Blo 1016603 1144561 := bbase (se 2 (by rfl) ⟨429210, by rfl⟩ : syracuseStep 1144561 = 858421) (by norm_num)
theorem B2291453 : Blo 1016603 2291453 := bbase (se 3 (by rfl) ⟨429647, by rfl⟩ : syracuseStep 2291453 = 859295) (by norm_num)
theorem B2750213 : Blo 1016603 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B3438341 : Blo 1016603 3438341 := bbase (se 4 (by rfl) ⟨322344, by rfl⟩ : syracuseStep 3438341 = 644689) (by norm_num)
theorem B1144597 : Blo 1016603 1144597 := bbase (se 6 (by rfl) ⟨26826, by rfl⟩ : syracuseStep 1144597 = 53653) (by norm_num)
theorem B1931053 : Blo 1016603 1931053 := bbase (se 3 (by rfl) ⟨362072, by rfl⟩ : syracuseStep 1931053 = 724145) (by norm_num)
theorem B3143477 : Blo 1016603 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B1144633 : Blo 1016603 1144633 := bbase (se 2 (by rfl) ⟨429237, by rfl⟩ : syracuseStep 1144633 = 858475) (by norm_num)
theorem B2291525 : Blo 1016603 2291525 := bbase (se 4 (by rfl) ⟨214830, by rfl⟩ : syracuseStep 2291525 = 429661) (by norm_num)
theorem B1144669 : Blo 1016603 1144669 := bbase (se 3 (by rfl) ⟨214625, by rfl⟩ : syracuseStep 1144669 = 429251) (by norm_num)
theorem B2062189 : Blo 1016603 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B4355957 : Blo 1016603 4355957 := bbase (se 5 (by rfl) ⟨204185, by rfl⟩ : syracuseStep 4355957 = 408371) (by norm_num)
theorem B8714101 : Blo 1016603 8714101 := bbase (se 5 (by rfl) ⟨408473, by rfl⟩ : syracuseStep 8714101 = 816947) (by norm_num)
theorem B1144705 : Blo 1016603 1144705 := bbase (se 2 (by rfl) ⟨429264, by rfl⟩ : syracuseStep 1144705 = 858529) (by norm_num)
theorem B2291597 : Blo 1016603 2291597 := bbase (se 3 (by rfl) ⟨429674, by rfl⟩ : syracuseStep 2291597 = 859349) (by norm_num)
theorem B1144741 : Blo 1016603 1144741 := bbase (se 4 (by rfl) ⟨107319, by rfl⟩ : syracuseStep 1144741 = 214639) (by norm_num)
theorem B1931197 : Blo 1016603 1931197 := bbase (se 3 (by rfl) ⟨362099, by rfl⟩ : syracuseStep 1931197 = 724199) (by norm_num)
theorem B1144777 : Blo 1016603 1144777 := bbase (se 2 (by rfl) ⟨429291, by rfl⟩ : syracuseStep 1144777 = 858583) (by norm_num)
theorem B7436245 : Blo 1016603 7436245 := bbase (se 7 (by rfl) ⟨87143, by rfl⟩ : syracuseStep 7436245 = 174287) (by norm_num)
theorem B2291669 : Blo 1016603 2291669 := bbase (se 7 (by rfl) ⟨26855, by rfl⟩ : syracuseStep 2291669 = 53711) (by norm_num)
theorem B1144813 : Blo 1016603 1144813 := bbase (se 3 (by rfl) ⟨214652, by rfl⟩ : syracuseStep 1144813 = 429305) (by norm_num)
theorem B6191093 : Blo 1016603 6191093 := bbase (se 5 (by rfl) ⟨290207, by rfl⟩ : syracuseStep 6191093 = 580415) (by norm_num)
theorem B1832957 : Blo 1016603 1832957 := bbase (se 3 (by rfl) ⟨343679, by rfl⟩ : syracuseStep 1832957 = 687359) (by norm_num)
theorem B3766277 : Blo 1016603 3766277 := bbase (se 4 (by rfl) ⟨353088, by rfl⟩ : syracuseStep 3766277 = 706177) (by norm_num)
theorem B3864581 : Blo 1016603 3864581 := bbase (se 4 (by rfl) ⟨362304, by rfl⟩ : syracuseStep 3864581 = 724609) (by norm_num)
theorem B1144849 : Blo 1016603 1144849 := bbase (se 2 (by rfl) ⟨429318, by rfl⟩ : syracuseStep 1144849 = 858637) (by norm_num)
theorem B2291741 : Blo 1016603 2291741 := bbase (se 3 (by rfl) ⟨429701, by rfl⟩ : syracuseStep 2291741 = 859403) (by norm_num)
theorem B1144885 : Blo 1016603 1144885 := bbase (se 5 (by rfl) ⟨53666, by rfl⟩ : syracuseStep 1144885 = 107333) (by norm_num)
theorem B1144921 : Blo 1016603 1144921 := bbase (se 2 (by rfl) ⟨429345, by rfl⟩ : syracuseStep 1144921 = 858691) (by norm_num)
theorem B1931357 : Blo 1016603 1931357 := bbase (se 3 (by rfl) ⟨362129, by rfl⟩ : syracuseStep 1931357 = 724259) (by norm_num)
theorem B2291813 : Blo 1016603 2291813 := bbase (se 4 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 2291813 = 429715) (by norm_num)
theorem B1144957 : Blo 1016603 1144957 := bbase (se 3 (by rfl) ⟨214679, by rfl⟩ : syracuseStep 1144957 = 429359) (by norm_num)
theorem B1144993 : Blo 1016603 1144993 := bbase (se 2 (by rfl) ⟨429372, by rfl⟩ : syracuseStep 1144993 = 858745) (by norm_num)
theorem B2291885 : Blo 1016603 2291885 := bbase (se 3 (by rfl) ⟨429728, by rfl⟩ : syracuseStep 2291885 = 859457) (by norm_num)
theorem B3438773 : Blo 1016603 3438773 := bbase (se 5 (by rfl) ⟨161192, by rfl⟩ : syracuseStep 3438773 = 322385) (by norm_num)
theorem B1145029 : Blo 1016603 1145029 := bbase (se 4 (by rfl) ⟨107346, by rfl⟩ : syracuseStep 1145029 = 214693) (by norm_num)
theorem B5798101 : Blo 1016603 5798101 := bbase (se 7 (by rfl) ⟨67946, by rfl⟩ : syracuseStep 5798101 = 135893) (by norm_num)
theorem B1145065 : Blo 1016603 1145065 := bbase (se 2 (by rfl) ⟨429399, by rfl⟩ : syracuseStep 1145065 = 858799) (by norm_num)
theorem B1931501 : Blo 1016603 1931501 := bbase (se 3 (by rfl) ⟨362156, by rfl⟩ : syracuseStep 1931501 = 724313) (by norm_num)
theorem B2291957 : Blo 1016603 2291957 := bbase (se 5 (by rfl) ⟨107435, by rfl⟩ : syracuseStep 2291957 = 214871) (by norm_num)
theorem B1145101 : Blo 1016603 1145101 := bbase (se 3 (by rfl) ⟨214706, by rfl⟩ : syracuseStep 1145101 = 429413) (by norm_num)
theorem B6715669 : Blo 1016603 6715669 := bbase (se 6 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 6715669 = 314797) (by norm_num)
theorem B1145137 : Blo 1016603 1145137 := bbase (se 2 (by rfl) ⟨429426, by rfl⟩ : syracuseStep 1145137 = 858853) (by norm_num)
theorem B2292029 : Blo 1016603 2292029 := bbase (se 3 (by rfl) ⟨429755, by rfl⟩ : syracuseStep 2292029 = 859511) (by norm_num)
theorem B1145173 : Blo 1016603 1145173 := bbase (se 10 (by rfl) ⟨1677, by rfl⟩ : syracuseStep 1145173 = 3355) (by norm_num)
theorem B1145209 : Blo 1016603 1145209 := bbase (se 2 (by rfl) ⟨429453, by rfl⟩ : syracuseStep 1145209 = 858907) (by norm_num)
theorem B2292101 : Blo 1016603 2292101 := bbase (se 4 (by rfl) ⟨214884, by rfl⟩ : syracuseStep 2292101 = 429769) (by norm_num)
theorem B1145245 : Blo 1016603 1145245 := bbase (se 3 (by rfl) ⟨214733, by rfl⟩ : syracuseStep 1145245 = 429467) (by norm_num)
theorem B1145281 : Blo 1016603 1145281 := bbase (se 2 (by rfl) ⟨429480, by rfl⟩ : syracuseStep 1145281 = 858961) (by norm_num)
theorem B2292173 : Blo 1016603 2292173 := bbase (se 3 (by rfl) ⟨429782, by rfl⟩ : syracuseStep 2292173 = 859565) (by norm_num)
theorem B1145317 : Blo 1016603 1145317 := bbase (se 4 (by rfl) ⟨107373, by rfl⟩ : syracuseStep 1145317 = 214747) (by norm_num)
theorem B1145353 : Blo 1016603 1145353 := bbase (se 2 (by rfl) ⟨429507, by rfl⟩ : syracuseStep 1145353 = 859015) (by norm_num)
theorem B1931789 : Blo 1016603 1931789 := bbase (se 3 (by rfl) ⟨362210, by rfl⟩ : syracuseStep 1931789 = 724421) (by norm_num)
theorem B2292245 : Blo 1016603 2292245 := bbase (se 6 (by rfl) ⟨53724, by rfl⟩ : syracuseStep 2292245 = 107449) (by norm_num)
theorem B1145389 : Blo 1016603 1145389 := bbase (se 3 (by rfl) ⟨214760, by rfl⟩ : syracuseStep 1145389 = 429521) (by norm_num)
theorem B1145425 : Blo 1016603 1145425 := bbase (se 2 (by rfl) ⟨429534, by rfl⟩ : syracuseStep 1145425 = 859069) (by norm_num)
theorem B2292317 : Blo 1016603 2292317 := bbase (se 3 (by rfl) ⟨429809, by rfl⟩ : syracuseStep 2292317 = 859619) (by norm_num)
theorem B3439205 : Blo 1016603 3439205 := bbase (se 4 (by rfl) ⟨322425, by rfl⟩ : syracuseStep 3439205 = 644851) (by norm_num)
theorem B1309285 : Blo 1016603 1309285 := bbase (se 4 (by rfl) ⟨122745, by rfl⟩ : syracuseStep 1309285 = 245491) (by norm_num)
theorem B1145461 : Blo 1016603 1145461 := bbase (se 5 (by rfl) ⟨53693, by rfl⟩ : syracuseStep 1145461 = 107387) (by norm_num)
theorem B1145497 : Blo 1016603 1145497 := bbase (se 2 (by rfl) ⟨429561, by rfl⟩ : syracuseStep 1145497 = 859123) (by norm_num)
theorem B1931941 : Blo 1016603 1931941 := bbase (se 4 (by rfl) ⟨181119, by rfl⟩ : syracuseStep 1931941 = 362239) (by norm_num)
theorem B2292389 : Blo 1016603 2292389 := bbase (se 4 (by rfl) ⟨214911, by rfl⟩ : syracuseStep 2292389 = 429823) (by norm_num)
theorem B1145533 : Blo 1016603 1145533 := bbase (se 3 (by rfl) ⟨214787, by rfl⟩ : syracuseStep 1145533 = 429575) (by norm_num)
theorem B1145569 : Blo 1016603 1145569 := bbase (se 2 (by rfl) ⟨429588, by rfl⟩ : syracuseStep 1145569 = 859177) (by norm_num)
theorem B2292461 : Blo 1016603 2292461 := bbase (se 3 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 2292461 = 859673) (by norm_num)
theorem B1145605 : Blo 1016603 1145605 := bbase (se 4 (by rfl) ⟨107400, by rfl⟩ : syracuseStep 1145605 = 214801) (by norm_num)
theorem B1145641 : Blo 1016603 1145641 := bbase (se 2 (by rfl) ⟨429615, by rfl⟩ : syracuseStep 1145641 = 859231) (by norm_num)
theorem B2292533 : Blo 1016603 2292533 := bbase (se 5 (by rfl) ⟨107462, by rfl⟩ : syracuseStep 2292533 = 214925) (by norm_num)
theorem B1145677 : Blo 1016603 1145677 := bbase (se 3 (by rfl) ⟨214814, by rfl⟩ : syracuseStep 1145677 = 429629) (by norm_num)
theorem B4356949 : Blo 1016603 4356949 := bbase (se 9 (by rfl) ⟨12764, by rfl⟩ : syracuseStep 4356949 = 25529) (by norm_num)
theorem B1145713 : Blo 1016603 1145713 := bbase (se 2 (by rfl) ⟨429642, by rfl⟩ : syracuseStep 1145713 = 859285) (by norm_num)
theorem B2292605 : Blo 1016603 2292605 := bbase (se 3 (by rfl) ⟨429863, by rfl⟩ : syracuseStep 2292605 = 859727) (by norm_num)
theorem B1145749 : Blo 1016603 1145749 := bbase (se 6 (by rfl) ⟨26853, by rfl⟩ : syracuseStep 1145749 = 53707) (by norm_num)
theorem B1145785 : Blo 1016603 1145785 := bbase (se 2 (by rfl) ⟨429669, by rfl⟩ : syracuseStep 1145785 = 859339) (by norm_num)
theorem B2292677 : Blo 1016603 2292677 := bbase (se 4 (by rfl) ⟨214938, by rfl⟩ : syracuseStep 2292677 = 429877) (by norm_num)
theorem B1932245 : Blo 1016603 1932245 := bbase (se 7 (by rfl) ⟨22643, by rfl⟩ : syracuseStep 1932245 = 45287) (by norm_num)
theorem B7076821 : Blo 1016603 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B1145821 : Blo 1016603 1145821 := bbase (se 3 (by rfl) ⟨214841, by rfl⟩ : syracuseStep 1145821 = 429683) (by norm_num)
theorem B1145857 : Blo 1016603 1145857 := bbase (se 2 (by rfl) ⟨429696, by rfl⟩ : syracuseStep 1145857 = 859393) (by norm_num)
theorem B2292749 : Blo 1016603 2292749 := bbase (se 3 (by rfl) ⟨429890, by rfl⟩ : syracuseStep 2292749 = 859781) (by norm_num)
theorem B3439637 : Blo 1016603 3439637 := bbase (se 6 (by rfl) ⟨80616, by rfl⟩ : syracuseStep 3439637 = 161233) (by norm_num)
theorem B1145893 : Blo 1016603 1145893 := bbase (se 4 (by rfl) ⟨107427, by rfl⟩ : syracuseStep 1145893 = 214855) (by norm_num)
theorem B3308581 : Blo 1016603 3308581 := bbase (se 4 (by rfl) ⟨310179, by rfl⟩ : syracuseStep 3308581 = 620359) (by norm_num)
theorem B1145929 : Blo 1016603 1145929 := bbase (se 2 (by rfl) ⟨429723, by rfl⟩ : syracuseStep 1145929 = 859447) (by norm_num)
theorem B2292821 : Blo 1016603 2292821 := bbase (se 8 (by rfl) ⟨13434, by rfl⟩ : syracuseStep 2292821 = 26869) (by norm_num)
theorem B1145965 : Blo 1016603 1145965 := bbase (se 3 (by rfl) ⟨214868, by rfl⟩ : syracuseStep 1145965 = 429737) (by norm_num)
theorem B1146001 : Blo 1016603 1146001 := bbase (se 2 (by rfl) ⟨429750, by rfl⟩ : syracuseStep 1146001 = 859501) (by norm_num)
theorem B2292893 : Blo 1016603 2292893 := bbase (se 3 (by rfl) ⟨429917, by rfl⟩ : syracuseStep 2292893 = 859835) (by norm_num)
theorem B3865765 : Blo 1016603 3865765 := bbase (se 4 (by rfl) ⟨362415, by rfl⟩ : syracuseStep 3865765 = 724831) (by norm_num)
theorem B1146037 : Blo 1016603 1146037 := bbase (se 5 (by rfl) ⟨53720, by rfl⟩ : syracuseStep 1146037 = 107441) (by norm_num)
theorem B1146073 : Blo 1016603 1146073 := bbase (se 2 (by rfl) ⟨429777, by rfl⟩ : syracuseStep 1146073 = 859555) (by norm_num)
theorem B2292965 : Blo 1016603 2292965 := bbase (se 4 (by rfl) ⟨214965, by rfl⟩ : syracuseStep 2292965 = 429931) (by norm_num)
theorem B1146109 : Blo 1016603 1146109 := bbase (se 3 (by rfl) ⟨214895, by rfl⟩ : syracuseStep 1146109 = 429791) (by norm_num)
theorem B1146145 : Blo 1016603 1146145 := bbase (se 2 (by rfl) ⟨429804, by rfl⟩ : syracuseStep 1146145 = 859609) (by norm_num)
theorem B2293037 : Blo 1016603 2293037 := bbase (se 3 (by rfl) ⟨429944, by rfl⟩ : syracuseStep 2293037 = 859889) (by norm_num)
theorem B1146181 : Blo 1016603 1146181 := bbase (se 4 (by rfl) ⟨107454, by rfl⟩ : syracuseStep 1146181 = 214909) (by norm_num)
theorem B1146217 : Blo 1016603 1146217 := bbase (se 2 (by rfl) ⟨429831, by rfl⟩ : syracuseStep 1146217 = 859663) (by norm_num)
theorem B2293109 : Blo 1016603 2293109 := bbase (se 5 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 2293109 = 214979) (by norm_num)
theorem B1146253 : Blo 1016603 1146253 := bbase (se 3 (by rfl) ⟨214922, by rfl⟩ : syracuseStep 1146253 = 429845) (by norm_num)
theorem B1146289 : Blo 1016603 1146289 := bbase (se 2 (by rfl) ⟨429858, by rfl⟩ : syracuseStep 1146289 = 859717) (by norm_num)
theorem B2293181 : Blo 1016603 2293181 := bbase (se 3 (by rfl) ⟨429971, by rfl⟩ : syracuseStep 2293181 = 859943) (by norm_num)
theorem B3440069 : Blo 1016603 3440069 := bbase (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) (by norm_num)
theorem B3866069 : Blo 1016603 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B1146325 : Blo 1016603 1146325 := bbase (se 7 (by rfl) ⟨13433, by rfl⟩ : syracuseStep 1146325 = 26867) (by norm_num)
theorem B1179109 : Blo 1016603 1179109 := bbase (se 4 (by rfl) ⟨110541, by rfl⟩ : syracuseStep 1179109 = 221083) (by norm_num)
theorem B1146361 : Blo 1016603 1146361 := bbase (se 2 (by rfl) ⟨429885, by rfl⟩ : syracuseStep 1146361 = 859771) (by norm_num)
theorem B2293253 : Blo 1016603 2293253 := bbase (se 4 (by rfl) ⟨214992, by rfl⟩ : syracuseStep 2293253 = 429985) (by norm_num)
theorem B1146397 : Blo 1016603 1146397 := bbase (se 3 (by rfl) ⟨214949, by rfl⟩ : syracuseStep 1146397 = 429899) (by norm_num)
theorem B1146433 : Blo 1016603 1146433 := bbase (se 2 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 1146433 = 859825) (by norm_num)
theorem B2293325 : Blo 1016603 2293325 := bbase (se 3 (by rfl) ⟨429998, by rfl⟩ : syracuseStep 2293325 = 859997) (by norm_num)
theorem B1146469 : Blo 1016603 1146469 := bbase (se 4 (by rfl) ⟨107481, by rfl⟩ : syracuseStep 1146469 = 214963) (by norm_num)
theorem B1146505 : Blo 1016603 1146505 := bbase (se 2 (by rfl) ⟨429939, by rfl⟩ : syracuseStep 1146505 = 859879) (by norm_num)
theorem B1375885 : Blo 1016603 1375885 := bbase (se 3 (by rfl) ⟨257978, by rfl⟩ : syracuseStep 1375885 = 515957) (by norm_num)
theorem B2293397 : Blo 1016603 2293397 := bbase (se 6 (by rfl) ⟨53751, by rfl⟩ : syracuseStep 2293397 = 107503) (by norm_num)
theorem B1146541 : Blo 1016603 1146541 := bbase (se 3 (by rfl) ⟨214976, by rfl⟩ : syracuseStep 1146541 = 429953) (by norm_num)
theorem B2752181 : Blo 1016603 2752181 := bbase (se 5 (by rfl) ⟨129008, by rfl⟩ : syracuseStep 2752181 = 258017) (by norm_num)
theorem B1932997 : Blo 1016603 1932997 := bbase (se 4 (by rfl) ⟨181218, by rfl⟩ : syracuseStep 1932997 = 362437) (by norm_num)
theorem B1146577 : Blo 1016603 1146577 := bbase (se 2 (by rfl) ⟨429966, by rfl⟩ : syracuseStep 1146577 = 859933) (by norm_num)
theorem B2293469 : Blo 1016603 2293469 := bbase (se 3 (by rfl) ⟨430025, by rfl⟩ : syracuseStep 2293469 = 860051) (by norm_num)
theorem B1146613 : Blo 1016603 1146613 := bbase (se 5 (by rfl) ⟨53747, by rfl⟩ : syracuseStep 1146613 = 107495) (by norm_num)
theorem B1146649 : Blo 1016603 1146649 := bbase (se 2 (by rfl) ⟨429993, by rfl⟩ : syracuseStep 1146649 = 859987) (by norm_num)
theorem B2293541 : Blo 1016603 2293541 := bbase (se 4 (by rfl) ⟨215019, by rfl⟩ : syracuseStep 2293541 = 430039) (by norm_num)
theorem B8716085 : Blo 1016603 8716085 := bbase (se 5 (by rfl) ⟨408566, by rfl⟩ : syracuseStep 8716085 = 817133) (by norm_num)
theorem B1146685 : Blo 1016603 1146685 := bbase (se 3 (by rfl) ⟨215003, by rfl⟩ : syracuseStep 1146685 = 430007) (by norm_num)
theorem B1933141 : Blo 1016603 1933141 := bbase (se 9 (by rfl) ⟨5663, by rfl⟩ : syracuseStep 1933141 = 11327) (by norm_num)
theorem B1146721 : Blo 1016603 1146721 := bbase (se 2 (by rfl) ⟨430020, by rfl⟩ : syracuseStep 1146721 = 860041) (by norm_num)
theorem B2293613 : Blo 1016603 2293613 := bbase (se 3 (by rfl) ⟨430052, by rfl⟩ : syracuseStep 2293613 = 860105) (by norm_num)
theorem B3440501 : Blo 1016603 3440501 := bbase (se 5 (by rfl) ⟨161273, by rfl⟩ : syracuseStep 3440501 = 322547) (by norm_num)
theorem B1146757 : Blo 1016603 1146757 := bbase (se 4 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 1146757 = 215017) (by norm_num)
theorem B1146793 : Blo 1016603 1146793 := bbase (se 2 (by rfl) ⟨430047, by rfl⟩ : syracuseStep 1146793 = 860095) (by norm_num)
theorem B2293685 : Blo 1016603 2293685 := bbase (se 5 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 2293685 = 215033) (by norm_num)
theorem B1146829 : Blo 1016603 1146829 := bbase (se 3 (by rfl) ⟨215030, by rfl⟩ : syracuseStep 1146829 = 430061) (by norm_num)
theorem B1146865 : Blo 1016603 1146865 := bbase (se 2 (by rfl) ⟨430074, by rfl⟩ : syracuseStep 1146865 = 860149) (by norm_num)
theorem B1933301 : Blo 1016603 1933301 := bbase (se 5 (by rfl) ⟨90623, by rfl⟩ : syracuseStep 1933301 = 181247) (by norm_num)
theorem B2293757 : Blo 1016603 2293757 := bbase (se 3 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 2293757 = 860159) (by norm_num)
theorem B1146883 : Blo 1016603 1146883 := bstep (se 1 (by rfl) ⟨860162, by rfl⟩ : syracuseStep 1146883 = 1720325) B1720325
theorem B2359313 : Blo 1016603 2359313 := bstep (se 2 (by rfl) ⟨884742, by rfl⟩ : syracuseStep 2359313 = 1769485) B1769485
theorem B3440717 : Blo 1016603 3440717 := bstep (se 3 (by rfl) ⟨645134, by rfl⟩ : syracuseStep 3440717 = 1290269) B1290269
theorem B3866723 : Blo 1016603 3866723 := bstep (se 1 (by rfl) ⟨2900042, by rfl⟩ : syracuseStep 3866723 = 5800085) B5800085
theorem B3866737 : Blo 1016603 3866737 := bstep (se 2 (by rfl) ⟨1450026, by rfl⟩ : syracuseStep 3866737 = 2900053) B2900053
theorem B3440771 : Blo 1016603 3440771 := bstep (se 1 (by rfl) ⟨2580578, by rfl⟩ : syracuseStep 3440771 = 5161157) B5161157
theorem B1147027 : Blo 1016603 1147027 := bstep (se 1 (by rfl) ⟨860270, by rfl⟩ : syracuseStep 1147027 = 1720541) B1720541
theorem B3178673 : Blo 1016603 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B2293937 : Blo 1016603 2293937 := bstep (se 2 (by rfl) ⟨860226, by rfl⟩ : syracuseStep 2293937 = 1720453) B1720453
theorem B2293955 : Blo 1016603 2293955 := bstep (se 1 (by rfl) ⟨1720466, by rfl⟩ : syracuseStep 2293955 = 3440933) B3440933
theorem B6193379 : Blo 1016603 6193379 := bstep (se 1 (by rfl) ⟨4645034, by rfl⟩ : syracuseStep 6193379 = 9290069) B9290069
theorem B1147171 : Blo 1016603 1147171 := bstep (se 1 (by rfl) ⟨860378, by rfl⟩ : syracuseStep 1147171 = 1720757) B1720757
theorem B1376561 : Blo 1016603 1376561 := bstep (se 2 (by rfl) ⟨516210, by rfl⟩ : syracuseStep 1376561 = 1032421) B1032421
theorem B1376609 : Blo 1016603 1376609 := bstep (se 2 (by rfl) ⟨516228, by rfl⟩ : syracuseStep 1376609 = 1032457) B1032457
theorem B1835363 : Blo 1016603 1835363 := bstep (se 1 (by rfl) ⟨1376522, by rfl⟩ : syracuseStep 1835363 = 2753045) B2753045
theorem B9929101 : Blo 1016603 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B3441041 : Blo 1016603 3441041 := bstep (se 2 (by rfl) ⟨1290390, by rfl⟩ : syracuseStep 3441041 = 2580781) B2580781
theorem B1147315 : Blo 1016603 1147315 := bstep (se 1 (by rfl) ⟨860486, by rfl⟩ : syracuseStep 1147315 = 1720973) B1720973
theorem B2294225 : Blo 1016603 2294225 := bstep (se 2 (by rfl) ⟨860334, by rfl⟩ : syracuseStep 2294225 = 1720669) B1720669
theorem B2294243 : Blo 1016603 2294243 := bstep (se 1 (by rfl) ⟨1720682, by rfl⟩ : syracuseStep 2294243 = 3441365) B3441365
theorem B1147459 : Blo 1016603 1147459 := bstep (se 1 (by rfl) ⟨860594, by rfl⟩ : syracuseStep 1147459 = 1721189) B1721189
theorem B5800517 : Blo 1016603 5800517 := bstep (se 4 (by rfl) ⟨543798, by rfl⟩ : syracuseStep 5800517 = 1087597) B1087597
theorem B1933969 : Blo 1016603 1933969 := bstep (se 2 (by rfl) ⟨725238, by rfl⟩ : syracuseStep 1933969 = 1450477) B1450477
theorem B1147603 : Blo 1016603 1147603 := bstep (se 1 (by rfl) ⟨860702, by rfl⟩ : syracuseStep 1147603 = 1721405) B1721405
theorem B2294513 : Blo 1016603 2294513 := bstep (se 2 (by rfl) ⟨860442, by rfl⟩ : syracuseStep 2294513 = 1720885) B1720885
theorem B4358897 : Blo 1016603 4358897 := bstep (se 2 (by rfl) ⟨1634586, by rfl⟩ : syracuseStep 4358897 = 3269173) B3269173
theorem B2294531 : Blo 1016603 2294531 := bstep (se 1 (by rfl) ⟨1720898, by rfl⟩ : syracuseStep 2294531 = 3441797) B3441797
theorem B1016611 : Blo 1016603 1016611 := bstep (se 1 (by rfl) ⟨762458, by rfl⟩ : syracuseStep 1016611 = 1524917) B1524917
theorem B1016627 : Blo 1016603 1016627 := bstep (se 1 (by rfl) ⟨762470, by rfl⟩ : syracuseStep 1016627 = 1524941) B1524941
theorem B13075253 : Blo 1016603 13075253 := bstep (se 5 (by rfl) ⟨612902, by rfl⟩ : syracuseStep 13075253 = 1225805) B1225805
theorem B1016643 : Blo 1016603 1016643 := bstep (se 1 (by rfl) ⟨762482, by rfl⟩ : syracuseStep 1016643 = 1524965) B1524965
theorem B2786125 : Blo 1016603 2786125 := bstep (se 3 (by rfl) ⟨522398, by rfl⟩ : syracuseStep 2786125 = 1044797) B1044797
theorem B1016659 : Blo 1016603 1016659 := bstep (se 1 (by rfl) ⟨762494, by rfl⟩ : syracuseStep 1016659 = 1524989) B1524989
theorem B1016675 : Blo 1016603 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B1147747 : Blo 1016603 1147747 := bstep (se 1 (by rfl) ⟨860810, by rfl⟩ : syracuseStep 1147747 = 1721621) B1721621
theorem B1016691 : Blo 1016603 1016691 := bstep (se 1 (by rfl) ⟨762518, by rfl⟩ : syracuseStep 1016691 = 1525037) B1525037
theorem B1016707 : Blo 1016603 1016707 := bstep (se 1 (by rfl) ⟨762530, by rfl⟩ : syracuseStep 1016707 = 1525061) B1525061
theorem B1016723 : Blo 1016603 1016723 := bstep (se 1 (by rfl) ⟨762542, by rfl⟩ : syracuseStep 1016723 = 1525085) B1525085
theorem B1016739 : Blo 1016603 1016739 := bstep (se 1 (by rfl) ⟨762554, by rfl⟩ : syracuseStep 1016739 = 1525109) B1525109
theorem B3441581 : Blo 1016603 3441581 := bstep (se 3 (by rfl) ⟨645296, by rfl⟩ : syracuseStep 3441581 = 1290593) B1290593
theorem B1016755 : Blo 1016603 1016755 := bstep (se 1 (by rfl) ⟨762566, by rfl⟩ : syracuseStep 1016755 = 1525133) B1525133
theorem B1016771 : Blo 1016603 1016771 := bstep (se 1 (by rfl) ⟨762578, by rfl⟩ : syracuseStep 1016771 = 1525157) B1525157
theorem B11305925 : Blo 1016603 11305925 := bstep (se 4 (by rfl) ⟨1059930, by rfl⟩ : syracuseStep 11305925 = 2119861) B2119861
theorem B19104709 : Blo 1016603 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B1016787 : Blo 1016603 1016787 := bstep (se 1 (by rfl) ⟨762590, by rfl⟩ : syracuseStep 1016787 = 1525181) B1525181
theorem B1016803 : Blo 1016603 1016803 := bstep (se 1 (by rfl) ⟨762602, by rfl⟩ : syracuseStep 1016803 = 1525205) B1525205
theorem B3441635 : Blo 1016603 3441635 := bstep (se 1 (by rfl) ⟨2581226, by rfl⟩ : syracuseStep 3441635 = 5162453) B5162453
theorem B1016819 : Blo 1016603 1016819 := bstep (se 1 (by rfl) ⟨762614, by rfl⟩ : syracuseStep 1016819 = 1525229) B1525229
theorem B1147891 : Blo 1016603 1147891 := bstep (se 1 (by rfl) ⟨860918, by rfl⟩ : syracuseStep 1147891 = 1721837) B1721837
theorem B1016835 : Blo 1016603 1016835 := bstep (se 1 (by rfl) ⟨762626, by rfl⟩ : syracuseStep 1016835 = 1525253) B1525253
theorem B2294801 : Blo 1016603 2294801 := bstep (se 2 (by rfl) ⟨860550, by rfl⟩ : syracuseStep 2294801 = 1721101) B1721101
theorem B1016851 : Blo 1016603 1016851 := bstep (se 1 (by rfl) ⟨762638, by rfl⟩ : syracuseStep 1016851 = 1525277) B1525277
theorem B1016867 : Blo 1016603 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B1934371 : Blo 1016603 1934371 := bstep (se 1 (by rfl) ⟨1450778, by rfl⟩ : syracuseStep 1934371 = 2901557) B2901557
theorem B2294819 : Blo 1016603 2294819 := bstep (se 1 (by rfl) ⟨1721114, by rfl⟩ : syracuseStep 2294819 = 3442229) B3442229
theorem B1016883 : Blo 1016603 1016883 := bstep (se 1 (by rfl) ⟨762662, by rfl⟩ : syracuseStep 1016883 = 1525325) B1525325
theorem B1016899 : Blo 1016603 1016899 := bstep (se 1 (by rfl) ⟨762674, by rfl⟩ : syracuseStep 1016899 = 1525349) B1525349
theorem B1836113 : Blo 1016603 1836113 := bstep (se 2 (by rfl) ⟨688542, by rfl⟩ : syracuseStep 1836113 = 1377085) B1377085
theorem B1934417 : Blo 1016603 1934417 := bstep (se 2 (by rfl) ⟨725406, by rfl⟩ : syracuseStep 1934417 = 1450813) B1450813
theorem B1016915 : Blo 1016603 1016915 := bstep (se 1 (by rfl) ⟨762686, by rfl⟩ : syracuseStep 1016915 = 1525373) B1525373
theorem B1016931 : Blo 1016603 1016931 := bstep (se 1 (by rfl) ⟨762698, by rfl⟩ : syracuseStep 1016931 = 1525397) B1525397
theorem B1016947 : Blo 1016603 1016947 := bstep (se 1 (by rfl) ⟨762710, by rfl⟩ : syracuseStep 1016947 = 1525421) B1525421
theorem B1016963 : Blo 1016603 1016963 := bstep (se 1 (by rfl) ⟨762722, by rfl⟩ : syracuseStep 1016963 = 1525445) B1525445
theorem B1148035 : Blo 1016603 1148035 := bstep (se 1 (by rfl) ⟨861026, by rfl⟩ : syracuseStep 1148035 = 1722053) B1722053
theorem B1016979 : Blo 1016603 1016979 := bstep (se 1 (by rfl) ⟨762734, by rfl⟩ : syracuseStep 1016979 = 1525469) B1525469
theorem B1016995 : Blo 1016603 1016995 := bstep (se 1 (by rfl) ⟨762746, by rfl⟩ : syracuseStep 1016995 = 1525493) B1525493
theorem B1017011 : Blo 1016603 1017011 := bstep (se 1 (by rfl) ⟨762758, by rfl⟩ : syracuseStep 1017011 = 1525517) B1525517
theorem B1017027 : Blo 1016603 1017027 := bstep (se 1 (by rfl) ⟨762770, by rfl⟩ : syracuseStep 1017027 = 1525541) B1525541
theorem B1017043 : Blo 1016603 1017043 := bstep (se 1 (by rfl) ⟨762782, by rfl⟩ : syracuseStep 1017043 = 1525565) B1525565
theorem B47056085 : Blo 1016603 47056085 := bstep (se 7 (by rfl) ⟨551438, by rfl⟩ : syracuseStep 47056085 = 1102877) B1102877
theorem B1017059 : Blo 1016603 1017059 := bstep (se 1 (by rfl) ⟨762794, by rfl⟩ : syracuseStep 1017059 = 1525589) B1525589
theorem B3441905 : Blo 1016603 3441905 := bstep (se 2 (by rfl) ⟨1290714, by rfl⟩ : syracuseStep 3441905 = 2581429) B2581429
theorem B1017075 : Blo 1016603 1017075 := bstep (se 1 (by rfl) ⟨762806, by rfl⟩ : syracuseStep 1017075 = 1525613) B1525613
theorem B1017091 : Blo 1016603 1017091 := bstep (se 1 (by rfl) ⟨762818, by rfl⟩ : syracuseStep 1017091 = 1525637) B1525637
theorem B1017107 : Blo 1016603 1017107 := bstep (se 1 (by rfl) ⟨762830, by rfl⟩ : syracuseStep 1017107 = 1525661) B1525661
theorem B1148179 : Blo 1016603 1148179 := bstep (se 1 (by rfl) ⟨861134, by rfl⟩ : syracuseStep 1148179 = 1722269) B1722269
theorem B1017123 : Blo 1016603 1017123 := bstep (se 1 (by rfl) ⟨762842, by rfl⟩ : syracuseStep 1017123 = 1525685) B1525685
theorem B2295089 : Blo 1016603 2295089 := bstep (se 2 (by rfl) ⟨860658, by rfl⟩ : syracuseStep 2295089 = 1721317) B1721317
theorem B1017139 : Blo 1016603 1017139 := bstep (se 1 (by rfl) ⟨762854, by rfl⟩ : syracuseStep 1017139 = 1525709) B1525709
theorem B1017155 : Blo 1016603 1017155 := bstep (se 1 (by rfl) ⟨762866, by rfl⟩ : syracuseStep 1017155 = 1525733) B1525733
theorem B2295107 : Blo 1016603 2295107 := bstep (se 1 (by rfl) ⟨1721330, by rfl⟩ : syracuseStep 2295107 = 3442661) B3442661
theorem B1017171 : Blo 1016603 1017171 := bstep (se 1 (by rfl) ⟨762878, by rfl⟩ : syracuseStep 1017171 = 1525757) B1525757
theorem B1017187 : Blo 1016603 1017187 := bstep (se 1 (by rfl) ⟨762890, by rfl⟩ : syracuseStep 1017187 = 1525781) B1525781
theorem B1934705 : Blo 1016603 1934705 := bstep (se 2 (by rfl) ⟨725514, by rfl⟩ : syracuseStep 1934705 = 1451029) B1451029
theorem B1017203 : Blo 1016603 1017203 := bstep (se 1 (by rfl) ⟨762902, by rfl⟩ : syracuseStep 1017203 = 1525805) B1525805
theorem B1017219 : Blo 1016603 1017219 := bstep (se 1 (by rfl) ⟨762914, by rfl⟩ : syracuseStep 1017219 = 1525829) B1525829
theorem B1017235 : Blo 1016603 1017235 := bstep (se 1 (by rfl) ⟨762926, by rfl⟩ : syracuseStep 1017235 = 1525853) B1525853
theorem B1017251 : Blo 1016603 1017251 := bstep (se 1 (by rfl) ⟨762938, by rfl⟩ : syracuseStep 1017251 = 1525877) B1525877
theorem B1017267 : Blo 1016603 1017267 := bstep (se 1 (by rfl) ⟨762950, by rfl⟩ : syracuseStep 1017267 = 1525901) B1525901
theorem B1017283 : Blo 1016603 1017283 := bstep (se 1 (by rfl) ⟨762962, by rfl⟩ : syracuseStep 1017283 = 1525925) B1525925
theorem B1017299 : Blo 1016603 1017299 := bstep (se 1 (by rfl) ⟨762974, by rfl⟩ : syracuseStep 1017299 = 1525949) B1525949
theorem B1017315 : Blo 1016603 1017315 := bstep (se 1 (by rfl) ⟨762986, by rfl⟩ : syracuseStep 1017315 = 1525973) B1525973
theorem B6522353 : Blo 1016603 6522353 := bstep (se 2 (by rfl) ⟨2445882, by rfl⟩ : syracuseStep 6522353 = 4891765) B4891765
theorem B1017331 : Blo 1016603 1017331 := bstep (se 1 (by rfl) ⟨762998, by rfl⟩ : syracuseStep 1017331 = 1525997) B1525997
theorem B1017347 : Blo 1016603 1017347 := bstep (se 1 (by rfl) ⟨763010, by rfl⟩ : syracuseStep 1017347 = 1526021) B1526021
theorem B1017363 : Blo 1016603 1017363 := bstep (se 1 (by rfl) ⟨763022, by rfl⟩ : syracuseStep 1017363 = 1526045) B1526045
theorem B1017379 : Blo 1016603 1017379 := bstep (se 1 (by rfl) ⟨763034, by rfl⟩ : syracuseStep 1017379 = 1526069) B1526069
theorem B3868195 : Blo 1016603 3868195 := bstep (se 1 (by rfl) ⟨2901146, by rfl⟩ : syracuseStep 3868195 = 5802293) B5802293
theorem B1017395 : Blo 1016603 1017395 := bstep (se 1 (by rfl) ⟨763046, by rfl⟩ : syracuseStep 1017395 = 1526093) B1526093
theorem B1017411 : Blo 1016603 1017411 := bstep (se 1 (by rfl) ⟨763058, by rfl⟩ : syracuseStep 1017411 = 1526117) B1526117
theorem B2295377 : Blo 1016603 2295377 := bstep (se 2 (by rfl) ⟨860766, by rfl⟩ : syracuseStep 2295377 = 1721533) B1721533
theorem B1017427 : Blo 1016603 1017427 := bstep (se 1 (by rfl) ⟨763070, by rfl⟩ : syracuseStep 1017427 = 1526141) B1526141
theorem B1017443 : Blo 1016603 1017443 := bstep (se 1 (by rfl) ⟨763082, by rfl⟩ : syracuseStep 1017443 = 1526165) B1526165
theorem B2295395 : Blo 1016603 2295395 := bstep (se 1 (by rfl) ⟨1721546, by rfl⟩ : syracuseStep 2295395 = 3443093) B3443093
theorem B1017459 : Blo 1016603 1017459 := bstep (se 1 (by rfl) ⟨763094, by rfl⟩ : syracuseStep 1017459 = 1526189) B1526189
theorem B1017475 : Blo 1016603 1017475 := bstep (se 1 (by rfl) ⟨763106, by rfl⟩ : syracuseStep 1017475 = 1526213) B1526213
theorem B1017491 : Blo 1016603 1017491 := bstep (se 1 (by rfl) ⟨763118, by rfl⟩ : syracuseStep 1017491 = 1526237) B1526237
theorem B1017507 : Blo 1016603 1017507 := bstep (se 1 (by rfl) ⟨763130, by rfl⟩ : syracuseStep 1017507 = 1526261) B1526261
theorem B1017523 : Blo 1016603 1017523 := bstep (se 1 (by rfl) ⟨763142, by rfl⟩ : syracuseStep 1017523 = 1526285) B1526285
theorem B1017539 : Blo 1016603 1017539 := bstep (se 1 (by rfl) ⟨763154, by rfl⟩ : syracuseStep 1017539 = 1526309) B1526309
theorem B4130509 : Blo 1016603 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B1017555 : Blo 1016603 1017555 := bstep (se 1 (by rfl) ⟨763166, by rfl⟩ : syracuseStep 1017555 = 1526333) B1526333
theorem B1017571 : Blo 1016603 1017571 := bstep (se 1 (by rfl) ⟨763178, by rfl⟩ : syracuseStep 1017571 = 1526357) B1526357
theorem B1017587 : Blo 1016603 1017587 := bstep (se 1 (by rfl) ⟨763190, by rfl⟩ : syracuseStep 1017587 = 1526381) B1526381
theorem B1017603 : Blo 1016603 1017603 := bstep (se 1 (by rfl) ⟨763202, by rfl⟩ : syracuseStep 1017603 = 1526405) B1526405
theorem B3442445 : Blo 1016603 3442445 := bstep (se 3 (by rfl) ⟨645458, by rfl⟩ : syracuseStep 3442445 = 1290917) B1290917
theorem B1017619 : Blo 1016603 1017619 := bstep (se 1 (by rfl) ⟨763214, by rfl⟩ : syracuseStep 1017619 = 1526429) B1526429
theorem B1017635 : Blo 1016603 1017635 := bstep (se 1 (by rfl) ⟨763226, by rfl⟩ : syracuseStep 1017635 = 1526453) B1526453
theorem B1017651 : Blo 1016603 1017651 := bstep (se 1 (by rfl) ⟨763238, by rfl⟩ : syracuseStep 1017651 = 1526477) B1526477
theorem B1017667 : Blo 1016603 1017667 := bstep (se 1 (by rfl) ⟨763250, by rfl⟩ : syracuseStep 1017667 = 1526501) B1526501
theorem B3442499 : Blo 1016603 3442499 := bstep (se 1 (by rfl) ⟨2581874, by rfl⟩ : syracuseStep 3442499 = 5163749) B5163749
theorem B1017683 : Blo 1016603 1017683 := bstep (se 1 (by rfl) ⟨763262, by rfl⟩ : syracuseStep 1017683 = 1526525) B1526525
theorem B1017699 : Blo 1016603 1017699 := bstep (se 1 (by rfl) ⟨763274, by rfl⟩ : syracuseStep 1017699 = 1526549) B1526549
theorem B2295665 : Blo 1016603 2295665 := bstep (se 2 (by rfl) ⟨860874, by rfl⟩ : syracuseStep 2295665 = 1721749) B1721749
theorem B1017715 : Blo 1016603 1017715 := bstep (se 1 (by rfl) ⟨763286, by rfl⟩ : syracuseStep 1017715 = 1526573) B1526573
theorem B1017731 : Blo 1016603 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B2295683 : Blo 1016603 2295683 := bstep (se 1 (by rfl) ⟨1721762, by rfl⟩ : syracuseStep 2295683 = 3443525) B3443525
theorem B1017747 : Blo 1016603 1017747 := bstep (se 1 (by rfl) ⟨763310, by rfl⟩ : syracuseStep 1017747 = 1526621) B1526621
theorem B1017763 : Blo 1016603 1017763 := bstep (se 1 (by rfl) ⟨763322, by rfl⟩ : syracuseStep 1017763 = 1526645) B1526645
theorem B1017779 : Blo 1016603 1017779 := bstep (se 1 (by rfl) ⟨763334, by rfl⟩ : syracuseStep 1017779 = 1526669) B1526669
theorem B1017795 : Blo 1016603 1017795 := bstep (se 1 (by rfl) ⟨763346, by rfl⟩ : syracuseStep 1017795 = 1526693) B1526693
theorem B1017811 : Blo 1016603 1017811 := bstep (se 1 (by rfl) ⟨763358, by rfl⟩ : syracuseStep 1017811 = 1526717) B1526717
theorem B1017827 : Blo 1016603 1017827 := bstep (se 1 (by rfl) ⟨763370, by rfl⟩ : syracuseStep 1017827 = 1526741) B1526741
theorem B1017843 : Blo 1016603 1017843 := bstep (se 1 (by rfl) ⟨763382, by rfl⟩ : syracuseStep 1017843 = 1526765) B1526765
theorem B1017859 : Blo 1016603 1017859 := bstep (se 1 (by rfl) ⟨763394, by rfl⟩ : syracuseStep 1017859 = 1526789) B1526789
theorem B1017875 : Blo 1016603 1017875 := bstep (se 1 (by rfl) ⟨763406, by rfl⟩ : syracuseStep 1017875 = 1526813) B1526813
theorem B1017891 : Blo 1016603 1017891 := bstep (se 1 (by rfl) ⟨763418, by rfl⟩ : syracuseStep 1017891 = 1526837) B1526837
theorem B1017907 : Blo 1016603 1017907 := bstep (se 1 (by rfl) ⟨763430, by rfl⟩ : syracuseStep 1017907 = 1526861) B1526861
theorem B1017923 : Blo 1016603 1017923 := bstep (se 1 (by rfl) ⟨763442, by rfl⟩ : syracuseStep 1017923 = 1526885) B1526885
theorem B1935427 : Blo 1016603 1935427 := bstep (se 1 (by rfl) ⟨1451570, by rfl⟩ : syracuseStep 1935427 = 2903141) B2903141
theorem B3442769 : Blo 1016603 3442769 := bstep (se 2 (by rfl) ⟨1291038, by rfl⟩ : syracuseStep 3442769 = 2582077) B2582077
theorem B1017939 : Blo 1016603 1017939 := bstep (se 1 (by rfl) ⟨763454, by rfl⟩ : syracuseStep 1017939 = 1526909) B1526909
theorem B1017955 : Blo 1016603 1017955 := bstep (se 1 (by rfl) ⟨763466, by rfl⟩ : syracuseStep 1017955 = 1526933) B1526933
theorem B1017971 : Blo 1016603 1017971 := bstep (se 1 (by rfl) ⟨763478, by rfl⟩ : syracuseStep 1017971 = 1526957) B1526957
theorem B1017987 : Blo 1016603 1017987 := bstep (se 1 (by rfl) ⟨763490, by rfl⟩ : syracuseStep 1017987 = 1526981) B1526981
theorem B2295953 : Blo 1016603 2295953 := bstep (se 2 (by rfl) ⟨860982, by rfl⟩ : syracuseStep 2295953 = 1721965) B1721965
theorem B1018003 : Blo 1016603 1018003 := bstep (se 1 (by rfl) ⟨763502, by rfl⟩ : syracuseStep 1018003 = 1527005) B1527005
theorem B1018019 : Blo 1016603 1018019 := bstep (se 1 (by rfl) ⟨763514, by rfl⟩ : syracuseStep 1018019 = 1527029) B1527029
theorem B2295971 : Blo 1016603 2295971 := bstep (se 1 (by rfl) ⟨1721978, by rfl⟩ : syracuseStep 2295971 = 3443957) B3443957
theorem B1018035 : Blo 1016603 1018035 := bstep (se 1 (by rfl) ⟨763526, by rfl⟩ : syracuseStep 1018035 = 1527053) B1527053
theorem B1018051 : Blo 1016603 1018051 := bstep (se 1 (by rfl) ⟨763538, by rfl⟩ : syracuseStep 1018051 = 1527077) B1527077
theorem B1018067 : Blo 1016603 1018067 := bstep (se 1 (by rfl) ⟨763550, by rfl⟩ : syracuseStep 1018067 = 1527101) B1527101
theorem B1018083 : Blo 1016603 1018083 := bstep (se 1 (by rfl) ⟨763562, by rfl⟩ : syracuseStep 1018083 = 1527125) B1527125
theorem B6621425 : Blo 1016603 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B1018099 : Blo 1016603 1018099 := bstep (se 1 (by rfl) ⟨763574, by rfl⟩ : syracuseStep 1018099 = 1527149) B1527149
theorem B1018115 : Blo 1016603 1018115 := bstep (se 1 (by rfl) ⟨763586, by rfl⟩ : syracuseStep 1018115 = 1527173) B1527173
theorem B1378577 : Blo 1016603 1378577 := bstep (se 2 (by rfl) ⟨516966, by rfl⟩ : syracuseStep 1378577 = 1033933) B1033933
theorem B1018131 : Blo 1016603 1018131 := bstep (se 1 (by rfl) ⟨763598, by rfl⟩ : syracuseStep 1018131 = 1527197) B1527197
theorem B1018147 : Blo 1016603 1018147 := bstep (se 1 (by rfl) ⟨763610, by rfl⟩ : syracuseStep 1018147 = 1527221) B1527221
theorem B1018163 : Blo 1016603 1018163 := bstep (se 1 (by rfl) ⟨763622, by rfl⟩ : syracuseStep 1018163 = 1527245) B1527245
theorem B1018179 : Blo 1016603 1018179 := bstep (se 1 (by rfl) ⟨763634, by rfl⟩ : syracuseStep 1018179 = 1527269) B1527269
theorem B11143493 : Blo 1016603 11143493 := bstep (se 4 (by rfl) ⟨1044702, by rfl⟩ : syracuseStep 11143493 = 2089405) B2089405
theorem B1018195 : Blo 1016603 1018195 := bstep (se 1 (by rfl) ⟨763646, by rfl⟩ : syracuseStep 1018195 = 1527293) B1527293
theorem B1018211 : Blo 1016603 1018211 := bstep (se 1 (by rfl) ⟨763658, by rfl⟩ : syracuseStep 1018211 = 1527317) B1527317
theorem B1018227 : Blo 1016603 1018227 := bstep (se 1 (by rfl) ⟨763670, by rfl⟩ : syracuseStep 1018227 = 1527341) B1527341
theorem B1018243 : Blo 1016603 1018243 := bstep (se 1 (by rfl) ⟨763682, by rfl⟩ : syracuseStep 1018243 = 1527365) B1527365
theorem B1739153 : Blo 1016603 1739153 := bstep (se 2 (by rfl) ⟨652182, by rfl⟩ : syracuseStep 1739153 = 1304365) B1304365
theorem B1018259 : Blo 1016603 1018259 := bstep (se 1 (by rfl) ⟨763694, by rfl⟩ : syracuseStep 1018259 = 1527389) B1527389
theorem B1018275 : Blo 1016603 1018275 := bstep (se 1 (by rfl) ⟨763706, by rfl⟩ : syracuseStep 1018275 = 1527413) B1527413
theorem B2296241 : Blo 1016603 2296241 := bstep (se 2 (by rfl) ⟨861090, by rfl⟩ : syracuseStep 2296241 = 1722181) B1722181
theorem B1018291 : Blo 1016603 1018291 := bstep (se 1 (by rfl) ⟨763718, by rfl⟩ : syracuseStep 1018291 = 1527437) B1527437
theorem B1018307 : Blo 1016603 1018307 := bstep (se 1 (by rfl) ⟨763730, by rfl⟩ : syracuseStep 1018307 = 1527461) B1527461
theorem B2296259 : Blo 1016603 2296259 := bstep (se 1 (by rfl) ⟨1722194, by rfl⟩ : syracuseStep 2296259 = 3444389) B3444389
theorem B1018323 : Blo 1016603 1018323 := bstep (se 1 (by rfl) ⟨763742, by rfl⟩ : syracuseStep 1018323 = 1527485) B1527485
theorem B1018339 : Blo 1016603 1018339 := bstep (se 1 (by rfl) ⟨763754, by rfl⟩ : syracuseStep 1018339 = 1527509) B1527509
theorem B1018355 : Blo 1016603 1018355 := bstep (se 1 (by rfl) ⟨763766, by rfl⟩ : syracuseStep 1018355 = 1527533) B1527533
theorem B1018371 : Blo 1016603 1018371 := bstep (se 1 (by rfl) ⟨763778, by rfl⟩ : syracuseStep 1018371 = 1527557) B1527557
theorem B1935875 : Blo 1016603 1935875 := bstep (se 1 (by rfl) ⟨1451906, by rfl⟩ : syracuseStep 1935875 = 2903813) B2903813
theorem B1018387 : Blo 1016603 1018387 := bstep (se 1 (by rfl) ⟨763790, by rfl⟩ : syracuseStep 1018387 = 1527581) B1527581
theorem B1018403 : Blo 1016603 1018403 := bstep (se 1 (by rfl) ⟨763802, by rfl⟩ : syracuseStep 1018403 = 1527605) B1527605
theorem B1018419 : Blo 1016603 1018419 := bstep (se 1 (by rfl) ⟨763814, by rfl⟩ : syracuseStep 1018419 = 1527629) B1527629
theorem B1018435 : Blo 1016603 1018435 := bstep (se 1 (by rfl) ⟨763826, by rfl⟩ : syracuseStep 1018435 = 1527653) B1527653
theorem B1018451 : Blo 1016603 1018451 := bstep (se 1 (by rfl) ⟨763838, by rfl⟩ : syracuseStep 1018451 = 1527677) B1527677
theorem B1018467 : Blo 1016603 1018467 := bstep (se 1 (by rfl) ⟨763850, by rfl⟩ : syracuseStep 1018467 = 1527701) B1527701
theorem B3443309 : Blo 1016603 3443309 := bstep (se 3 (by rfl) ⟨645620, by rfl⟩ : syracuseStep 3443309 = 1291241) B1291241
theorem B1018483 : Blo 1016603 1018483 := bstep (se 1 (by rfl) ⟨763862, by rfl⟩ : syracuseStep 1018483 = 1527725) B1527725
theorem B1018499 : Blo 1016603 1018499 := bstep (se 1 (by rfl) ⟨763874, by rfl⟩ : syracuseStep 1018499 = 1527749) B1527749
theorem B1018515 : Blo 1016603 1018515 := bstep (se 1 (by rfl) ⟨763886, by rfl⟩ : syracuseStep 1018515 = 1527773) B1527773
theorem B1018531 : Blo 1016603 1018531 := bstep (se 1 (by rfl) ⟨763898, by rfl⟩ : syracuseStep 1018531 = 1527797) B1527797
theorem B3443363 : Blo 1016603 3443363 := bstep (se 1 (by rfl) ⟨2582522, by rfl⟩ : syracuseStep 3443363 = 5165045) B5165045
theorem B1018547 : Blo 1016603 1018547 := bstep (se 1 (by rfl) ⟨763910, by rfl⟩ : syracuseStep 1018547 = 1527821) B1527821
theorem B1018563 : Blo 1016603 1018563 := bstep (se 1 (by rfl) ⟨763922, by rfl⟩ : syracuseStep 1018563 = 1527845) B1527845
theorem B1018579 : Blo 1016603 1018579 := bstep (se 1 (by rfl) ⟨763934, by rfl⟩ : syracuseStep 1018579 = 1527869) B1527869
theorem B1018595 : Blo 1016603 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B3672803 : Blo 1016603 3672803 := bstep (se 1 (by rfl) ⟨2754602, by rfl⟩ : syracuseStep 3672803 = 5509205) B5509205
theorem B1018611 : Blo 1016603 1018611 := bstep (se 1 (by rfl) ⟨763958, by rfl⟩ : syracuseStep 1018611 = 1527917) B1527917
theorem B1018627 : Blo 1016603 1018627 := bstep (se 1 (by rfl) ⟨763970, by rfl⟩ : syracuseStep 1018627 = 1527941) B1527941
theorem B1018643 : Blo 1016603 1018643 := bstep (se 1 (by rfl) ⟨763982, by rfl⟩ : syracuseStep 1018643 = 1527965) B1527965
theorem B1018659 : Blo 1016603 1018659 := bstep (se 1 (by rfl) ⟨763994, by rfl⟩ : syracuseStep 1018659 = 1527989) B1527989
theorem B1936163 : Blo 1016603 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B1018675 : Blo 1016603 1018675 := bstep (se 1 (by rfl) ⟨764006, by rfl⟩ : syracuseStep 1018675 = 1528013) B1528013
theorem B1018691 : Blo 1016603 1018691 := bstep (se 1 (by rfl) ⟨764018, by rfl⟩ : syracuseStep 1018691 = 1528037) B1528037
theorem B1018707 : Blo 1016603 1018707 := bstep (se 1 (by rfl) ⟨764030, by rfl⟩ : syracuseStep 1018707 = 1528061) B1528061
theorem B1018723 : Blo 1016603 1018723 := bstep (se 1 (by rfl) ⟨764042, by rfl⟩ : syracuseStep 1018723 = 1528085) B1528085
theorem B1018739 : Blo 1016603 1018739 := bstep (se 1 (by rfl) ⟨764054, by rfl⟩ : syracuseStep 1018739 = 1528109) B1528109
theorem B1018755 : Blo 1016603 1018755 := bstep (se 1 (by rfl) ⟨764066, by rfl⟩ : syracuseStep 1018755 = 1528133) B1528133
theorem B1018771 : Blo 1016603 1018771 := bstep (se 1 (by rfl) ⟨764078, by rfl⟩ : syracuseStep 1018771 = 1528157) B1528157
theorem B1018787 : Blo 1016603 1018787 := bstep (se 1 (by rfl) ⟨764090, by rfl⟩ : syracuseStep 1018787 = 1528181) B1528181
theorem B3443633 : Blo 1016603 3443633 := bstep (se 2 (by rfl) ⟨1291362, by rfl⟩ : syracuseStep 3443633 = 2582725) B2582725
theorem B1018803 : Blo 1016603 1018803 := bstep (se 1 (by rfl) ⟨764102, by rfl⟩ : syracuseStep 1018803 = 1528205) B1528205
theorem B1018819 : Blo 1016603 1018819 := bstep (se 1 (by rfl) ⟨764114, by rfl⟩ : syracuseStep 1018819 = 1528229) B1528229
theorem B1018835 : Blo 1016603 1018835 := bstep (se 1 (by rfl) ⟨764126, by rfl⟩ : syracuseStep 1018835 = 1528253) B1528253
theorem B1018851 : Blo 1016603 1018851 := bstep (se 1 (by rfl) ⟨764138, by rfl⟩ : syracuseStep 1018851 = 1528277) B1528277
theorem B1018867 : Blo 1016603 1018867 := bstep (se 1 (by rfl) ⟨764150, by rfl⟩ : syracuseStep 1018867 = 1528301) B1528301
theorem B1018883 : Blo 1016603 1018883 := bstep (se 1 (by rfl) ⟨764162, by rfl⟩ : syracuseStep 1018883 = 1528325) B1528325
theorem B13962253 : Blo 1016603 13962253 := bstep (se 3 (by rfl) ⟨2617922, by rfl⟩ : syracuseStep 13962253 = 5235845) B5235845
theorem B1018899 : Blo 1016603 1018899 := bstep (se 1 (by rfl) ⟨764174, by rfl⟩ : syracuseStep 1018899 = 1528349) B1528349
theorem B1018915 : Blo 1016603 1018915 := bstep (se 1 (by rfl) ⟨764186, by rfl⟩ : syracuseStep 1018915 = 1528373) B1528373
theorem B1018931 : Blo 1016603 1018931 := bstep (se 1 (by rfl) ⟨764198, by rfl⟩ : syracuseStep 1018931 = 1528397) B1528397
theorem B1018947 : Blo 1016603 1018947 := bstep (se 1 (by rfl) ⟨764210, by rfl⟩ : syracuseStep 1018947 = 1528421) B1528421
theorem B1018963 : Blo 1016603 1018963 := bstep (se 1 (by rfl) ⟨764222, by rfl⟩ : syracuseStep 1018963 = 1528445) B1528445
theorem B7441507 : Blo 1016603 7441507 := bstep (se 1 (by rfl) ⟨5581130, by rfl⟩ : syracuseStep 7441507 = 11162261) B11162261
theorem B1018979 : Blo 1016603 1018979 := bstep (se 1 (by rfl) ⟨764234, by rfl⟩ : syracuseStep 1018979 = 1528469) B1528469
theorem B1018995 : Blo 1016603 1018995 := bstep (se 1 (by rfl) ⟨764246, by rfl⟩ : syracuseStep 1018995 = 1528493) B1528493
theorem B1019011 : Blo 1016603 1019011 := bstep (se 1 (by rfl) ⟨764258, by rfl⟩ : syracuseStep 1019011 = 1528517) B1528517
theorem B1019027 : Blo 1016603 1019027 := bstep (se 1 (by rfl) ⟨764270, by rfl⟩ : syracuseStep 1019027 = 1528541) B1528541
theorem B1019043 : Blo 1016603 1019043 := bstep (se 1 (by rfl) ⟨764282, by rfl⟩ : syracuseStep 1019043 = 1528565) B1528565
theorem B1019059 : Blo 1016603 1019059 := bstep (se 1 (by rfl) ⟨764294, by rfl⟩ : syracuseStep 1019059 = 1528589) B1528589
theorem B1019075 : Blo 1016603 1019075 := bstep (se 1 (by rfl) ⟨764306, by rfl⟩ : syracuseStep 1019075 = 1528613) B1528613
theorem B1019091 : Blo 1016603 1019091 := bstep (se 1 (by rfl) ⟨764318, by rfl⟩ : syracuseStep 1019091 = 1528637) B1528637
theorem B1019107 : Blo 1016603 1019107 := bstep (se 1 (by rfl) ⟨764330, by rfl⟩ : syracuseStep 1019107 = 1528661) B1528661
theorem B1019123 : Blo 1016603 1019123 := bstep (se 1 (by rfl) ⟨764342, by rfl⟩ : syracuseStep 1019123 = 1528685) B1528685
theorem B1019139 : Blo 1016603 1019139 := bstep (se 1 (by rfl) ⟨764354, by rfl⟩ : syracuseStep 1019139 = 1528709) B1528709
theorem B1019155 : Blo 1016603 1019155 := bstep (se 1 (by rfl) ⟨764366, by rfl⟩ : syracuseStep 1019155 = 1528733) B1528733
theorem B1019171 : Blo 1016603 1019171 := bstep (se 1 (by rfl) ⟨764378, by rfl⟩ : syracuseStep 1019171 = 1528757) B1528757
theorem B1019187 : Blo 1016603 1019187 := bstep (se 1 (by rfl) ⟨764390, by rfl⟩ : syracuseStep 1019187 = 1528781) B1528781
theorem B1019203 : Blo 1016603 1019203 := bstep (se 1 (by rfl) ⟨764402, by rfl⟩ : syracuseStep 1019203 = 1528805) B1528805
theorem B1019219 : Blo 1016603 1019219 := bstep (se 1 (by rfl) ⟨764414, by rfl⟩ : syracuseStep 1019219 = 1528829) B1528829
theorem B1019235 : Blo 1016603 1019235 := bstep (se 1 (by rfl) ⟨764426, by rfl⟩ : syracuseStep 1019235 = 1528853) B1528853
theorem B1019251 : Blo 1016603 1019251 := bstep (se 1 (by rfl) ⟨764438, by rfl⟩ : syracuseStep 1019251 = 1528877) B1528877
theorem B1019267 : Blo 1016603 1019267 := bstep (se 1 (by rfl) ⟨764450, by rfl⟩ : syracuseStep 1019267 = 1528901) B1528901
theorem B1019283 : Blo 1016603 1019283 := bstep (se 1 (by rfl) ⟨764462, by rfl⟩ : syracuseStep 1019283 = 1528925) B1528925
theorem B1019299 : Blo 1016603 1019299 := bstep (se 1 (by rfl) ⟨764474, by rfl⟩ : syracuseStep 1019299 = 1528949) B1528949
theorem B1019315 : Blo 1016603 1019315 := bstep (se 1 (by rfl) ⟨764486, by rfl⟩ : syracuseStep 1019315 = 1528973) B1528973
theorem B1019331 : Blo 1016603 1019331 := bstep (se 1 (by rfl) ⟨764498, by rfl⟩ : syracuseStep 1019331 = 1528997) B1528997
theorem B3444173 : Blo 1016603 3444173 := bstep (se 3 (by rfl) ⟨645782, by rfl⟩ : syracuseStep 3444173 = 1291565) B1291565
theorem B1019347 : Blo 1016603 1019347 := bstep (se 1 (by rfl) ⟨764510, by rfl⟩ : syracuseStep 1019347 = 1529021) B1529021
theorem B1019363 : Blo 1016603 1019363 := bstep (se 1 (by rfl) ⟨764522, by rfl⟩ : syracuseStep 1019363 = 1529045) B1529045
theorem B1019379 : Blo 1016603 1019379 := bstep (se 1 (by rfl) ⟨764534, by rfl⟩ : syracuseStep 1019379 = 1529069) B1529069
theorem B1019395 : Blo 1016603 1019395 := bstep (se 1 (by rfl) ⟨764546, by rfl⟩ : syracuseStep 1019395 = 1529093) B1529093
theorem B3444227 : Blo 1016603 3444227 := bstep (se 1 (by rfl) ⟨2583170, by rfl⟩ : syracuseStep 3444227 = 5166341) B5166341
theorem B1019411 : Blo 1016603 1019411 := bstep (se 1 (by rfl) ⟨764558, by rfl⟩ : syracuseStep 1019411 = 1529117) B1529117
theorem B1019427 : Blo 1016603 1019427 := bstep (se 1 (by rfl) ⟨764570, by rfl⟩ : syracuseStep 1019427 = 1529141) B1529141
theorem B1019443 : Blo 1016603 1019443 := bstep (se 1 (by rfl) ⟨764582, by rfl⟩ : syracuseStep 1019443 = 1529165) B1529165
theorem B1019459 : Blo 1016603 1019459 := bstep (se 1 (by rfl) ⟨764594, by rfl⟩ : syracuseStep 1019459 = 1529189) B1529189
theorem B1019475 : Blo 1016603 1019475 := bstep (se 1 (by rfl) ⟨764606, by rfl⟩ : syracuseStep 1019475 = 1529213) B1529213
theorem B1019491 : Blo 1016603 1019491 := bstep (se 1 (by rfl) ⟨764618, by rfl⟩ : syracuseStep 1019491 = 1529237) B1529237
theorem B1019507 : Blo 1016603 1019507 := bstep (se 1 (by rfl) ⟨764630, by rfl⟩ : syracuseStep 1019507 = 1529261) B1529261
theorem B1019523 : Blo 1016603 1019523 := bstep (se 1 (by rfl) ⟨764642, by rfl⟩ : syracuseStep 1019523 = 1529285) B1529285
theorem B1019539 : Blo 1016603 1019539 := bstep (se 1 (by rfl) ⟨764654, by rfl⟩ : syracuseStep 1019539 = 1529309) B1529309
theorem B1019555 : Blo 1016603 1019555 := bstep (se 1 (by rfl) ⟨764666, by rfl⟩ : syracuseStep 1019555 = 1529333) B1529333
theorem B1019571 : Blo 1016603 1019571 := bstep (se 1 (by rfl) ⟨764678, by rfl⟩ : syracuseStep 1019571 = 1529357) B1529357
theorem B1019587 : Blo 1016603 1019587 := bstep (se 1 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 1019587 = 1529381) B1529381
theorem B3870413 : Blo 1016603 3870413 := bstep (se 3 (by rfl) ⟨725702, by rfl⟩ : syracuseStep 3870413 = 1451405) B1451405
theorem B1937105 : Blo 1016603 1937105 := bstep (se 2 (by rfl) ⟨726414, by rfl⟩ : syracuseStep 1937105 = 1452829) B1452829
theorem B1019603 : Blo 1016603 1019603 := bstep (se 1 (by rfl) ⟨764702, by rfl⟩ : syracuseStep 1019603 = 1529405) B1529405
theorem B1019619 : Blo 1016603 1019619 := bstep (se 1 (by rfl) ⟨764714, by rfl⟩ : syracuseStep 1019619 = 1529429) B1529429
theorem B1019635 : Blo 1016603 1019635 := bstep (se 1 (by rfl) ⟨764726, by rfl⟩ : syracuseStep 1019635 = 1529453) B1529453
theorem B1019651 : Blo 1016603 1019651 := bstep (se 1 (by rfl) ⟨764738, by rfl⟩ : syracuseStep 1019651 = 1529477) B1529477
theorem B3444497 : Blo 1016603 3444497 := bstep (se 2 (by rfl) ⟨1291686, by rfl⟩ : syracuseStep 3444497 = 2583373) B2583373
theorem B1019667 : Blo 1016603 1019667 := bstep (se 1 (by rfl) ⟨764750, by rfl⟩ : syracuseStep 1019667 = 1529501) B1529501
theorem B1019683 : Blo 1016603 1019683 := bstep (se 1 (by rfl) ⟨764762, by rfl⟩ : syracuseStep 1019683 = 1529525) B1529525
theorem B1019699 : Blo 1016603 1019699 := bstep (se 1 (by rfl) ⟨764774, by rfl⟩ : syracuseStep 1019699 = 1529549) B1529549
theorem B1019715 : Blo 1016603 1019715 := bstep (se 1 (by rfl) ⟨764786, by rfl⟩ : syracuseStep 1019715 = 1529573) B1529573
theorem B1019731 : Blo 1016603 1019731 := bstep (se 1 (by rfl) ⟨764798, by rfl⟩ : syracuseStep 1019731 = 1529597) B1529597
theorem B3673955 : Blo 1016603 3673955 := bstep (se 1 (by rfl) ⟨2755466, by rfl⟩ : syracuseStep 3673955 = 5510933) B5510933
theorem B1019747 : Blo 1016603 1019747 := bstep (se 1 (by rfl) ⟨764810, by rfl⟩ : syracuseStep 1019747 = 1529621) B1529621
theorem B1019763 : Blo 1016603 1019763 := bstep (se 1 (by rfl) ⟨764822, by rfl⟩ : syracuseStep 1019763 = 1529645) B1529645
theorem B1019779 : Blo 1016603 1019779 := bstep (se 1 (by rfl) ⟨764834, by rfl⟩ : syracuseStep 1019779 = 1529669) B1529669
theorem B6524813 : Blo 1016603 6524813 := bstep (se 3 (by rfl) ⟨1223402, by rfl⟩ : syracuseStep 6524813 = 2446805) B2446805
theorem B1019795 : Blo 1016603 1019795 := bstep (se 1 (by rfl) ⟨764846, by rfl⟩ : syracuseStep 1019795 = 1529693) B1529693
theorem B1019811 : Blo 1016603 1019811 := bstep (se 1 (by rfl) ⟨764858, by rfl⟩ : syracuseStep 1019811 = 1529717) B1529717
theorem B1019827 : Blo 1016603 1019827 := bstep (se 1 (by rfl) ⟨764870, by rfl⟩ : syracuseStep 1019827 = 1529741) B1529741
theorem B1019843 : Blo 1016603 1019843 := bstep (se 1 (by rfl) ⟨764882, by rfl⟩ : syracuseStep 1019843 = 1529765) B1529765
theorem B1019859 : Blo 1016603 1019859 := bstep (se 1 (by rfl) ⟨764894, by rfl⟩ : syracuseStep 1019859 = 1529789) B1529789
theorem B1019875 : Blo 1016603 1019875 := bstep (se 1 (by rfl) ⟨764906, by rfl⟩ : syracuseStep 1019875 = 1529813) B1529813
theorem B1019891 : Blo 1016603 1019891 := bstep (se 1 (by rfl) ⟨764918, by rfl⟩ : syracuseStep 1019891 = 1529837) B1529837
theorem B1019907 : Blo 1016603 1019907 := bstep (se 1 (by rfl) ⟨764930, by rfl⟩ : syracuseStep 1019907 = 1529861) B1529861
theorem B1019923 : Blo 1016603 1019923 := bstep (se 1 (by rfl) ⟨764942, by rfl⟩ : syracuseStep 1019923 = 1529885) B1529885
theorem B1019939 : Blo 1016603 1019939 := bstep (se 1 (by rfl) ⟨764954, by rfl⟩ : syracuseStep 1019939 = 1529909) B1529909
theorem B1019955 : Blo 1016603 1019955 := bstep (se 1 (by rfl) ⟨764966, by rfl⟩ : syracuseStep 1019955 = 1529933) B1529933
theorem B1019971 : Blo 1016603 1019971 := bstep (se 1 (by rfl) ⟨764978, by rfl⟩ : syracuseStep 1019971 = 1529957) B1529957
theorem B1019987 : Blo 1016603 1019987 := bstep (se 1 (by rfl) ⟨764990, by rfl⟩ : syracuseStep 1019987 = 1529981) B1529981
theorem B1020003 : Blo 1016603 1020003 := bstep (se 1 (by rfl) ⟨765002, by rfl⟩ : syracuseStep 1020003 = 1530005) B1530005
theorem B10457201 : Blo 1016603 10457201 := bstep (se 2 (by rfl) ⟨3921450, by rfl⟩ : syracuseStep 10457201 = 7842901) B7842901
theorem B1020019 : Blo 1016603 1020019 := bstep (se 1 (by rfl) ⟨765014, by rfl⟩ : syracuseStep 1020019 = 1530029) B1530029
theorem B1020035 : Blo 1016603 1020035 := bstep (se 1 (by rfl) ⟨765026, by rfl⟩ : syracuseStep 1020035 = 1530053) B1530053
theorem B1020051 : Blo 1016603 1020051 := bstep (se 1 (by rfl) ⟨765038, by rfl⟩ : syracuseStep 1020051 = 1530077) B1530077
theorem B1020067 : Blo 1016603 1020067 := bstep (se 1 (by rfl) ⟨765050, by rfl⟩ : syracuseStep 1020067 = 1530101) B1530101
theorem B1020083 : Blo 1016603 1020083 := bstep (se 1 (by rfl) ⟨765062, by rfl⟩ : syracuseStep 1020083 = 1530125) B1530125
theorem B1020099 : Blo 1016603 1020099 := bstep (se 1 (by rfl) ⟨765074, by rfl⟩ : syracuseStep 1020099 = 1530149) B1530149
theorem B1020115 : Blo 1016603 1020115 := bstep (se 1 (by rfl) ⟨765086, by rfl⟩ : syracuseStep 1020115 = 1530173) B1530173
theorem B1020131 : Blo 1016603 1020131 := bstep (se 1 (by rfl) ⟨765098, by rfl⟩ : syracuseStep 1020131 = 1530197) B1530197
theorem B8687857 : Blo 1016603 8687857 := bstep (se 2 (by rfl) ⟨3257946, by rfl⟩ : syracuseStep 8687857 = 6515893) B6515893
theorem B1020147 : Blo 1016603 1020147 := bstep (se 1 (by rfl) ⟨765110, by rfl⟩ : syracuseStep 1020147 = 1530221) B1530221
theorem B1020163 : Blo 1016603 1020163 := bstep (se 1 (by rfl) ⟨765122, by rfl⟩ : syracuseStep 1020163 = 1530245) B1530245
theorem B1020179 : Blo 1016603 1020179 := bstep (se 1 (by rfl) ⟨765134, by rfl⟩ : syracuseStep 1020179 = 1530269) B1530269
theorem B1020195 : Blo 1016603 1020195 := bstep (se 1 (by rfl) ⟨765146, by rfl⟩ : syracuseStep 1020195 = 1530293) B1530293
theorem B1020211 : Blo 1016603 1020211 := bstep (se 1 (by rfl) ⟨765158, by rfl⟩ : syracuseStep 1020211 = 1530317) B1530317
theorem B1020227 : Blo 1016603 1020227 := bstep (se 1 (by rfl) ⟨765170, by rfl⟩ : syracuseStep 1020227 = 1530341) B1530341
theorem B1020243 : Blo 1016603 1020243 := bstep (se 1 (by rfl) ⟨765182, by rfl⟩ : syracuseStep 1020243 = 1530365) B1530365
theorem B1020259 : Blo 1016603 1020259 := bstep (se 1 (by rfl) ⟨765194, by rfl⟩ : syracuseStep 1020259 = 1530389) B1530389
theorem B1020275 : Blo 1016603 1020275 := bstep (se 1 (by rfl) ⟨765206, by rfl⟩ : syracuseStep 1020275 = 1530413) B1530413
theorem B1020291 : Blo 1016603 1020291 := bstep (se 1 (by rfl) ⟨765218, by rfl⟩ : syracuseStep 1020291 = 1530437) B1530437
theorem B1020307 : Blo 1016603 1020307 := bstep (se 1 (by rfl) ⟨765230, by rfl⟩ : syracuseStep 1020307 = 1530461) B1530461
theorem B1020323 : Blo 1016603 1020323 := bstep (se 1 (by rfl) ⟨765242, by rfl⟩ : syracuseStep 1020323 = 1530485) B1530485
theorem B1020339 : Blo 1016603 1020339 := bstep (se 1 (by rfl) ⟨765254, by rfl⟩ : syracuseStep 1020339 = 1530509) B1530509
theorem B1020355 : Blo 1016603 1020355 := bstep (se 1 (by rfl) ⟨765266, by rfl⟩ : syracuseStep 1020355 = 1530533) B1530533
theorem B1020371 : Blo 1016603 1020371 := bstep (se 1 (by rfl) ⟨765278, by rfl⟩ : syracuseStep 1020371 = 1530557) B1530557
theorem B1085923 : Blo 1016603 1085923 := bstep (se 1 (by rfl) ⟨814442, by rfl⟩ : syracuseStep 1085923 = 1628885) B1628885
theorem B7934435 : Blo 1016603 7934435 := bstep (se 1 (by rfl) ⟨5950826, by rfl⟩ : syracuseStep 7934435 = 11901653) B11901653
theorem B1020387 : Blo 1016603 1020387 := bstep (se 1 (by rfl) ⟨765290, by rfl⟩ : syracuseStep 1020387 = 1530581) B1530581
theorem B5149169 : Blo 1016603 5149169 := bstep (se 2 (by rfl) ⟨1930938, by rfl⟩ : syracuseStep 5149169 = 3861877) B3861877
theorem B1020403 : Blo 1016603 1020403 := bstep (se 1 (by rfl) ⟨765302, by rfl⟩ : syracuseStep 1020403 = 1530605) B1530605
theorem B1020419 : Blo 1016603 1020419 := bstep (se 1 (by rfl) ⟨765314, by rfl⟩ : syracuseStep 1020419 = 1530629) B1530629
theorem B1020435 : Blo 1016603 1020435 := bstep (se 1 (by rfl) ⟨765326, by rfl⟩ : syracuseStep 1020435 = 1530653) B1530653
theorem B1020451 : Blo 1016603 1020451 := bstep (se 1 (by rfl) ⟨765338, by rfl⟩ : syracuseStep 1020451 = 1530677) B1530677
theorem B1020467 : Blo 1016603 1020467 := bstep (se 1 (by rfl) ⟨765350, by rfl⟩ : syracuseStep 1020467 = 1530701) B1530701
theorem B1020483 : Blo 1016603 1020483 := bstep (se 1 (by rfl) ⟨765362, by rfl⟩ : syracuseStep 1020483 = 1530725) B1530725
theorem B1020499 : Blo 1016603 1020499 := bstep (se 1 (by rfl) ⟨765374, by rfl⟩ : syracuseStep 1020499 = 1530749) B1530749
theorem B1020515 : Blo 1016603 1020515 := bstep (se 1 (by rfl) ⟨765386, by rfl⟩ : syracuseStep 1020515 = 1530773) B1530773
theorem B1020531 : Blo 1016603 1020531 := bstep (se 1 (by rfl) ⟨765398, by rfl⟩ : syracuseStep 1020531 = 1530797) B1530797
theorem B1020547 : Blo 1016603 1020547 := bstep (se 1 (by rfl) ⟨765410, by rfl⟩ : syracuseStep 1020547 = 1530821) B1530821
theorem B1020563 : Blo 1016603 1020563 := bstep (se 1 (by rfl) ⟨765422, by rfl⟩ : syracuseStep 1020563 = 1530845) B1530845
theorem B2757283 : Blo 1016603 2757283 := bstep (se 1 (by rfl) ⟨2067962, by rfl⟩ : syracuseStep 2757283 = 4135925) B4135925
theorem B1020579 : Blo 1016603 1020579 := bstep (se 1 (by rfl) ⟨765434, by rfl⟩ : syracuseStep 1020579 = 1530869) B1530869
theorem B1020595 : Blo 1016603 1020595 := bstep (se 1 (by rfl) ⟨765446, by rfl⟩ : syracuseStep 1020595 = 1530893) B1530893
theorem B5575601 : Blo 1016603 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B7345349 : Blo 1016603 7345349 := bstep (se 4 (by rfl) ⟨688626, by rfl⟩ : syracuseStep 7345349 = 1377253) B1377253
theorem B1447475 : Blo 1016603 1447475 := bstep (se 1 (by rfl) ⟨1085606, by rfl⟩ : syracuseStep 1447475 = 2171213) B2171213
theorem B6035057 : Blo 1016603 6035057 := bstep (se 2 (by rfl) ⟨2263146, by rfl⟩ : syracuseStep 6035057 = 4526293) B4526293
theorem B1087187 : Blo 1016603 1087187 := bstep (se 1 (by rfl) ⟨815390, by rfl⟩ : syracuseStep 1087187 = 1630781) B1630781
theorem B18618083 : Blo 1016603 18618083 := bstep (se 1 (by rfl) ⟨13963562, by rfl⟩ : syracuseStep 18618083 = 27927125) B27927125
theorem B3675917 : Blo 1016603 3675917 := bstep (se 3 (by rfl) ⟨689234, by rfl⟩ : syracuseStep 3675917 = 1378469) B1378469
theorem B5150627 : Blo 1016603 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B2758691 : Blo 1016603 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B1448113 : Blo 1016603 1448113 := bstep (se 2 (by rfl) ⟨543042, by rfl⟩ : syracuseStep 1448113 = 1086085) B1086085
theorem B16718021 : Blo 1016603 16718021 := bstep (se 4 (by rfl) ⟨1567314, by rfl⟩ : syracuseStep 16718021 = 3134629) B3134629
theorem B5806349 : Blo 1016603 5806349 := bstep (se 3 (by rfl) ⟨1088690, by rfl⟩ : syracuseStep 5806349 = 2177381) B2177381
theorem B1448227 : Blo 1016603 1448227 := bstep (se 1 (by rfl) ⟨1086170, by rfl⟩ : syracuseStep 1448227 = 2172341) B2172341
theorem B1087939 : Blo 1016603 1087939 := bstep (se 1 (by rfl) ⟨815954, by rfl⟩ : syracuseStep 1087939 = 1631909) B1631909
theorem B3873329 : Blo 1016603 3873329 := bstep (se 2 (by rfl) ⟨1452498, by rfl⟩ : syracuseStep 3873329 = 2904997) B2904997
theorem B5151437 : Blo 1016603 5151437 := bstep (se 3 (by rfl) ⟨965894, by rfl⟩ : syracuseStep 5151437 = 1931789) B1931789
theorem B1547075 : Blo 1016603 1547075 := bstep (se 1 (by rfl) ⟨1160306, by rfl⟩ : syracuseStep 1547075 = 2320613) B2320613
theorem B1744291 : Blo 1016603 1744291 := bstep (se 1 (by rfl) ⟨1308218, by rfl⟩ : syracuseStep 1744291 = 2616437) B2616437
theorem B1449571 : Blo 1016603 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B1089331 : Blo 1016603 1089331 := bstep (se 1 (by rfl) ⟨816998, by rfl⟩ : syracuseStep 1089331 = 1633997) B1633997
theorem B1548163 : Blo 1016603 1548163 := bstep (se 1 (by rfl) ⟨1161122, by rfl⟩ : syracuseStep 1548163 = 2322245) B2322245
theorem B16752581 : Blo 1016603 16752581 := bstep (se 4 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 16752581 = 3141109) B3141109
theorem B3874787 : Blo 1016603 3874787 := bstep (se 1 (by rfl) ⟨2906090, by rfl⟩ : syracuseStep 3874787 = 5812181) B5812181
theorem B8954225 : Blo 1016603 8954225 := bstep (se 2 (by rfl) ⟨3357834, by rfl⟩ : syracuseStep 8954225 = 6715669) B6715669
theorem B2171281 : Blo 1016603 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B2171299 : Blo 1016603 2171299 := bstep (se 1 (by rfl) ⟨1628474, by rfl⟩ : syracuseStep 2171299 = 3256949) B3256949
theorem B5808581 : Blo 1016603 5808581 := bstep (se 4 (by rfl) ⟨544554, by rfl⟩ : syracuseStep 5808581 = 1089109) B1089109
theorem B1548977 : Blo 1016603 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B1450705 : Blo 1016603 1450705 := bstep (se 2 (by rfl) ⟨544014, by rfl⟩ : syracuseStep 1450705 = 1088029) B1088029
theorem B1286867 : Blo 1016603 1286867 := bstep (se 1 (by rfl) ⟨965150, by rfl⟩ : syracuseStep 1286867 = 1930301) B1930301
theorem B1450801 : Blo 1016603 1450801 := bstep (se 2 (by rfl) ⟨544050, by rfl⟩ : syracuseStep 1450801 = 1088101) B1088101
theorem B1745713 : Blo 1016603 1745713 := bstep (se 2 (by rfl) ⟨654642, by rfl⟩ : syracuseStep 1745713 = 1309285) B1309285
theorem B5809265 : Blo 1016603 5809265 := bstep (se 2 (by rfl) ⟨2178474, by rfl⟩ : syracuseStep 5809265 = 4356949) B4356949
theorem B10200305 : Blo 1016603 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B1451297 : Blo 1016603 1451297 := bstep (se 2 (by rfl) ⟨544236, by rfl⟩ : syracuseStep 1451297 = 1088473) B1088473
theorem B1221971 : Blo 1016603 1221971 := bstep (se 1 (by rfl) ⟨916478, by rfl⟩ : syracuseStep 1221971 = 1832957) B1832957
theorem B1287571 : Blo 1016603 1287571 := bstep (se 1 (by rfl) ⟨965678, by rfl⟩ : syracuseStep 1287571 = 1931357) B1931357
theorem B8693189 : Blo 1016603 8693189 := bstep (se 4 (by rfl) ⟨814986, by rfl⟩ : syracuseStep 8693189 = 1629973) B1629973
theorem B1287667 : Blo 1016603 1287667 := bstep (se 1 (by rfl) ⟨965750, by rfl⟩ : syracuseStep 1287667 = 1931501) B1931501
theorem B5154353 : Blo 1016603 5154353 := bstep (se 2 (by rfl) ⟨1932882, by rfl⟩ : syracuseStep 5154353 = 3865765) B3865765
theorem B11610053 : Blo 1016603 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B1288163 : Blo 1016603 1288163 := bstep (se 1 (by rfl) ⟨966122, by rfl⟩ : syracuseStep 1288163 = 1932245) B1932245
theorem B1452163 : Blo 1016603 1452163 := bstep (se 1 (by rfl) ⟨1089122, by rfl⟩ : syracuseStep 1452163 = 2178245) B2178245
theorem B1452259 : Blo 1016603 1452259 := bstep (se 1 (by rfl) ⟨1089194, by rfl⟩ : syracuseStep 1452259 = 2178389) B2178389
theorem B5810723 : Blo 1016603 5810723 := bstep (se 1 (by rfl) ⟨4358042, by rfl⟩ : syracuseStep 5810723 = 8716085) B8716085
theorem B2173571 : Blo 1016603 2173571 := bstep (se 1 (by rfl) ⟨1630178, by rfl⟩ : syracuseStep 2173571 = 3260357) B3260357
theorem B1288867 : Blo 1016603 1288867 := bstep (se 1 (by rfl) ⟨966650, by rfl⟩ : syracuseStep 1288867 = 1933301) B1933301
theorem B1452755 : Blo 1016603 1452755 := bstep (se 1 (by rfl) ⟨1089566, by rfl⟩ : syracuseStep 1452755 = 2179133) B2179133
theorem B1288963 : Blo 1016603 1288963 := bstep (se 1 (by rfl) ⟨966722, by rfl⟩ : syracuseStep 1288963 = 1933445) B1933445
theorem B3025795 : Blo 1016603 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B5155811 : Blo 1016603 5155811 := bstep (se 1 (by rfl) ⟨3866858, by rfl⟩ : syracuseStep 5155811 = 7733717) B7733717
theorem B6204451 : Blo 1016603 6204451 := bstep (se 1 (by rfl) ⟨4653338, by rfl⟩ : syracuseStep 6204451 = 9306677) B9306677
theorem B2174033 : Blo 1016603 2174033 := bstep (se 2 (by rfl) ⟨815262, by rfl⟩ : syracuseStep 2174033 = 1630525) B1630525
theorem B13053109 : Blo 1016603 13053109 := bstep (se 5 (by rfl) ⟨611864, by rfl⟩ : syracuseStep 13053109 = 1223729) B1223729
theorem B1289459 : Blo 1016603 1289459 := bstep (se 1 (by rfl) ⟨967094, by rfl⟩ : syracuseStep 1289459 = 1934189) B1934189
theorem B7154993 : Blo 1016603 7154993 := bstep (se 2 (by rfl) ⟨2683122, by rfl⟩ : syracuseStep 7154993 = 5366245) B5366245
theorem B1715539 : Blo 1016603 1715539 := bstep (se 1 (by rfl) ⟨1286654, by rfl⟩ : syracuseStep 1715539 = 2573309) B2573309
theorem B1715681 : Blo 1016603 1715681 := bstep (se 2 (by rfl) ⟨643380, by rfl⟩ : syracuseStep 1715681 = 1286761) B1286761
theorem B1715809 : Blo 1016603 1715809 := bstep (se 2 (by rfl) ⟨643428, by rfl⟩ : syracuseStep 1715809 = 1286857) B1286857
theorem B1715843 : Blo 1016603 1715843 := bstep (se 1 (by rfl) ⟨1286882, by rfl⟩ : syracuseStep 1715843 = 2573765) B2573765
theorem B1715971 : Blo 1016603 1715971 := bstep (se 1 (by rfl) ⟨1286978, by rfl⟩ : syracuseStep 1715971 = 2573957) B2573957
theorem B5156621 : Blo 1016603 5156621 := bstep (se 3 (by rfl) ⟨966866, by rfl⟩ : syracuseStep 5156621 = 1933733) B1933733
theorem B2895725 : Blo 1016603 2895725 := bstep (se 3 (by rfl) ⟨542948, by rfl⟩ : syracuseStep 2895725 = 1085897) B1085897
theorem B1716113 : Blo 1016603 1716113 := bstep (se 2 (by rfl) ⟨643542, by rfl⟩ : syracuseStep 1716113 = 1287085) B1287085
theorem B1224595 : Blo 1016603 1224595 := bstep (se 1 (by rfl) ⟨918446, by rfl⟩ : syracuseStep 1224595 = 1836893) B1836893
theorem B1290163 : Blo 1016603 1290163 := bstep (se 1 (by rfl) ⟨967622, by rfl⟩ : syracuseStep 1290163 = 1935245) B1935245
theorem B1716241 : Blo 1016603 1716241 := bstep (se 2 (by rfl) ⟨643590, by rfl⟩ : syracuseStep 1716241 = 1287181) B1287181
theorem B1290259 : Blo 1016603 1290259 := bstep (se 1 (by rfl) ⟨967694, by rfl⟩ : syracuseStep 1290259 = 1935389) B1935389
theorem B2895907 : Blo 1016603 2895907 := bstep (se 1 (by rfl) ⟨2171930, by rfl⟩ : syracuseStep 2895907 = 4343861) B4343861
theorem B1716275 : Blo 1016603 1716275 := bstep (se 1 (by rfl) ⟨1287206, by rfl⟩ : syracuseStep 1716275 = 2574413) B2574413
theorem B11022389 : Blo 1016603 11022389 := bstep (se 5 (by rfl) ⟨516674, by rfl⟩ : syracuseStep 11022389 = 1033349) B1033349
theorem B1224787 : Blo 1016603 1224787 := bstep (se 1 (by rfl) ⟨918590, by rfl⟩ : syracuseStep 1224787 = 1837181) B1837181
theorem B3092593 : Blo 1016603 3092593 := bstep (se 2 (by rfl) ⟨1159722, by rfl⟩ : syracuseStep 3092593 = 2319445) B2319445
theorem B1716403 : Blo 1016603 1716403 := bstep (se 1 (by rfl) ⟨1287302, by rfl⟩ : syracuseStep 1716403 = 2574605) B2574605
theorem B2896067 : Blo 1016603 2896067 := bstep (se 1 (by rfl) ⟨2172050, by rfl⟩ : syracuseStep 2896067 = 4344101) B4344101
theorem B1224931 : Blo 1016603 1224931 := bstep (se 1 (by rfl) ⟨918698, by rfl⟩ : syracuseStep 1224931 = 1837397) B1837397
theorem B1716545 : Blo 1016603 1716545 := bstep (se 2 (by rfl) ⟨643704, by rfl⟩ : syracuseStep 1716545 = 1287409) B1287409
theorem B2175331 : Blo 1016603 2175331 := bstep (se 1 (by rfl) ⟨1631498, by rfl⟩ : syracuseStep 2175331 = 3262997) B3262997
theorem B1716673 : Blo 1016603 1716673 := bstep (se 2 (by rfl) ⟨643752, by rfl⟩ : syracuseStep 1716673 = 1287505) B1287505
theorem B1716707 : Blo 1016603 1716707 := bstep (se 1 (by rfl) ⟨1287530, by rfl⟩ : syracuseStep 1716707 = 2575061) B2575061
theorem B1290755 : Blo 1016603 1290755 := bstep (se 1 (by rfl) ⟨968066, by rfl⟩ : syracuseStep 1290755 = 1936133) B1936133
theorem B1716835 : Blo 1016603 1716835 := bstep (se 1 (by rfl) ⟨1287626, by rfl⟩ : syracuseStep 1716835 = 2575253) B2575253
theorem B2175587 : Blo 1016603 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B1716977 : Blo 1016603 1716977 := bstep (se 2 (by rfl) ⟨643866, by rfl⟩ : syracuseStep 1716977 = 1287733) B1287733
theorem B1717105 : Blo 1016603 1717105 := bstep (se 2 (by rfl) ⟨643914, by rfl⟩ : syracuseStep 1717105 = 1287829) B1287829
theorem B1717139 : Blo 1016603 1717139 := bstep (se 1 (by rfl) ⟨1287854, by rfl⟩ : syracuseStep 1717139 = 2575709) B2575709
theorem B1717267 : Blo 1016603 1717267 := bstep (se 1 (by rfl) ⟨1287950, by rfl⟩ : syracuseStep 1717267 = 2575901) B2575901
theorem B1717409 : Blo 1016603 1717409 := bstep (se 2 (by rfl) ⟨644028, by rfl⟩ : syracuseStep 1717409 = 1288057) B1288057
theorem B1291459 : Blo 1016603 1291459 := bstep (se 1 (by rfl) ⟨968594, by rfl⟩ : syracuseStep 1291459 = 1937189) B1937189
theorem B2897137 : Blo 1016603 2897137 := bstep (se 2 (by rfl) ⟨1086426, by rfl⟩ : syracuseStep 2897137 = 2172853) B2172853
theorem B1717537 : Blo 1016603 1717537 := bstep (se 2 (by rfl) ⟨644076, by rfl⟩ : syracuseStep 1717537 = 1288153) B1288153
theorem B1291555 : Blo 1016603 1291555 := bstep (se 1 (by rfl) ⟨968666, by rfl⟩ : syracuseStep 1291555 = 1937333) B1937333
theorem B1717571 : Blo 1016603 1717571 := bstep (se 1 (by rfl) ⟨1288178, by rfl⟩ : syracuseStep 1717571 = 2576357) B2576357
theorem B1717699 : Blo 1016603 1717699 := bstep (se 1 (by rfl) ⟨1288274, by rfl⟩ : syracuseStep 1717699 = 2576549) B2576549
theorem B2176561 : Blo 1016603 2176561 := bstep (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) B1632421
theorem B1717841 : Blo 1016603 1717841 := bstep (se 2 (by rfl) ⟨644190, by rfl⟩ : syracuseStep 1717841 = 1288381) B1288381
theorem B1717969 : Blo 1016603 1717969 := bstep (se 2 (by rfl) ⟨644238, by rfl⟩ : syracuseStep 1717969 = 1288477) B1288477
theorem B1718003 : Blo 1016603 1718003 := bstep (se 1 (by rfl) ⟨1288502, by rfl⟩ : syracuseStep 1718003 = 2577005) B2577005
theorem B1718131 : Blo 1016603 1718131 := bstep (se 1 (by rfl) ⟨1288598, by rfl⟩ : syracuseStep 1718131 = 2577197) B2577197
theorem B1718273 : Blo 1016603 1718273 := bstep (se 2 (by rfl) ⟨644352, by rfl⟩ : syracuseStep 1718273 = 1288705) B1288705
theorem B1718401 : Blo 1016603 1718401 := bstep (se 2 (by rfl) ⟨644400, by rfl⟩ : syracuseStep 1718401 = 1288801) B1288801
theorem B1718435 : Blo 1016603 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B2177219 : Blo 1016603 2177219 := bstep (se 1 (by rfl) ⟨1632914, by rfl⟩ : syracuseStep 2177219 = 3265829) B3265829
theorem B7747811 : Blo 1016603 7747811 := bstep (se 1 (by rfl) ⟨5810858, by rfl⟩ : syracuseStep 7747811 = 11621717) B11621717
theorem B1718563 : Blo 1016603 1718563 := bstep (se 1 (by rfl) ⟨1288922, by rfl⟩ : syracuseStep 1718563 = 2577845) B2577845
theorem B4405553 : Blo 1016603 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B4962637 : Blo 1016603 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B1718705 : Blo 1016603 1718705 := bstep (se 2 (by rfl) ⟨644514, by rfl⟩ : syracuseStep 1718705 = 1289029) B1289029
theorem B22034915 : Blo 1016603 22034915 := bstep (se 1 (by rfl) ⟨16526186, by rfl⟩ : syracuseStep 22034915 = 33052373) B33052373
theorem B2898413 : Blo 1016603 2898413 := bstep (se 3 (by rfl) ⟨543452, by rfl⟩ : syracuseStep 2898413 = 1086905) B1086905
theorem B1718833 : Blo 1016603 1718833 := bstep (se 2 (by rfl) ⟨644562, by rfl⟩ : syracuseStep 1718833 = 1289125) B1289125
theorem B1718867 : Blo 1016603 1718867 := bstep (se 1 (by rfl) ⟨1289150, by rfl⟩ : syracuseStep 1718867 = 2578301) B2578301
theorem B5159537 : Blo 1016603 5159537 := bstep (se 2 (by rfl) ⟨1934826, by rfl⟩ : syracuseStep 5159537 = 3869653) B3869653
theorem B3259025 : Blo 1016603 3259025 := bstep (se 2 (by rfl) ⟨1222134, by rfl⟩ : syracuseStep 3259025 = 2444269) B2444269
theorem B2898595 : Blo 1016603 2898595 := bstep (se 1 (by rfl) ⟨2173946, by rfl⟩ : syracuseStep 2898595 = 4347893) B4347893
theorem B3259075 : Blo 1016603 3259075 := bstep (se 1 (by rfl) ⟨2444306, by rfl⟩ : syracuseStep 3259075 = 4888613) B4888613
theorem B2898641 : Blo 1016603 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B1718995 : Blo 1016603 1718995 := bstep (se 1 (by rfl) ⟨1289246, by rfl⟩ : syracuseStep 1718995 = 2578493) B2578493
theorem B1719137 : Blo 1016603 1719137 := bstep (se 2 (by rfl) ⟨644676, by rfl⟩ : syracuseStep 1719137 = 1289353) B1289353
theorem B1719265 : Blo 1016603 1719265 := bstep (se 2 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 1719265 = 1289449) B1289449
theorem B1719299 : Blo 1016603 1719299 := bstep (se 1 (by rfl) ⟨1289474, by rfl⟩ : syracuseStep 1719299 = 2578949) B2578949
theorem B2178065 : Blo 1016603 2178065 := bstep (se 2 (by rfl) ⟨816774, by rfl⟩ : syracuseStep 2178065 = 1633549) B1633549
theorem B1719427 : Blo 1016603 1719427 := bstep (se 1 (by rfl) ⟨1289570, by rfl⟩ : syracuseStep 1719427 = 2579141) B2579141
theorem B1719443 : Blo 1016603 1719443 := bstep (se 1 (by rfl) ⟨1289582, by rfl⟩ : syracuseStep 1719443 = 2579165) B2579165
theorem B1719569 : Blo 1016603 1719569 := bstep (se 2 (by rfl) ⟨644838, by rfl⟩ : syracuseStep 1719569 = 1289677) B1289677
theorem B1719697 : Blo 1016603 1719697 := bstep (se 2 (by rfl) ⟨644886, by rfl⟩ : syracuseStep 1719697 = 1289773) B1289773
theorem B1719731 : Blo 1016603 1719731 := bstep (se 1 (by rfl) ⟨1289798, by rfl⟩ : syracuseStep 1719731 = 2579597) B2579597
theorem B3259921 : Blo 1016603 3259921 := bstep (se 2 (by rfl) ⟨1222470, by rfl⟩ : syracuseStep 3259921 = 2444941) B2444941
theorem B1719859 : Blo 1016603 1719859 := bstep (se 1 (by rfl) ⟨1289894, by rfl⟩ : syracuseStep 1719859 = 2579789) B2579789
theorem B27836045 : Blo 1016603 27836045 := bstep (se 3 (by rfl) ⟨5219258, by rfl⟩ : syracuseStep 27836045 = 10438517) B10438517
theorem B11615885 : Blo 1016603 11615885 := bstep (se 3 (by rfl) ⟨2177978, by rfl⟩ : syracuseStep 11615885 = 4355957) B4355957
theorem B1720001 : Blo 1016603 1720001 := bstep (se 2 (by rfl) ⟨645000, by rfl⟩ : syracuseStep 1720001 = 1290001) B1290001
theorem B4898531 : Blo 1016603 4898531 := bstep (se 1 (by rfl) ⟨3673898, by rfl⟩ : syracuseStep 4898531 = 7347797) B7347797
theorem B1720129 : Blo 1016603 1720129 := bstep (se 2 (by rfl) ⟨645048, by rfl⟩ : syracuseStep 1720129 = 1290097) B1290097
theorem B1720163 : Blo 1016603 1720163 := bstep (se 1 (by rfl) ⟨1290122, by rfl⟩ : syracuseStep 1720163 = 2580245) B2580245
theorem B1720291 : Blo 1016603 1720291 := bstep (se 1 (by rfl) ⟨1290218, by rfl⟩ : syracuseStep 1720291 = 2580437) B2580437
theorem B3096593 : Blo 1016603 3096593 := bstep (se 2 (by rfl) ⟨1161222, by rfl⟩ : syracuseStep 3096593 = 2322445) B2322445
theorem B5160995 : Blo 1016603 5160995 := bstep (se 1 (by rfl) ⟨3870746, by rfl⟩ : syracuseStep 5160995 = 7741493) B7741493
theorem B1720433 : Blo 1016603 1720433 := bstep (se 2 (by rfl) ⟨645162, by rfl⟩ : syracuseStep 1720433 = 1290325) B1290325
theorem B2900099 : Blo 1016603 2900099 := bstep (se 1 (by rfl) ⟨2175074, by rfl⟩ : syracuseStep 2900099 = 4350149) B4350149
theorem B1720561 : Blo 1016603 1720561 := bstep (se 2 (by rfl) ⟨645210, by rfl⟩ : syracuseStep 1720561 = 1290421) B1290421
theorem B1720595 : Blo 1016603 1720595 := bstep (se 1 (by rfl) ⟨1290446, by rfl⟩ : syracuseStep 1720595 = 2580893) B2580893
theorem B1720723 : Blo 1016603 1720723 := bstep (se 1 (by rfl) ⟨1290542, by rfl⟩ : syracuseStep 1720723 = 2581085) B2581085
theorem B5227021 : Blo 1016603 5227021 := bstep (se 3 (by rfl) ⟨980066, by rfl⟩ : syracuseStep 5227021 = 1960133) B1960133
theorem B1720865 : Blo 1016603 1720865 := bstep (se 2 (by rfl) ⟨645324, by rfl⟩ : syracuseStep 1720865 = 1290649) B1290649
theorem B1720993 : Blo 1016603 1720993 := bstep (se 2 (by rfl) ⟨645372, by rfl⟩ : syracuseStep 1720993 = 1290745) B1290745
theorem B1721027 : Blo 1016603 1721027 := bstep (se 1 (by rfl) ⟨1290770, by rfl⟩ : syracuseStep 1721027 = 2581541) B2581541
theorem B1721155 : Blo 1016603 1721155 := bstep (se 1 (by rfl) ⟨1290866, by rfl⟩ : syracuseStep 1721155 = 2581733) B2581733
theorem B5161805 : Blo 1016603 5161805 := bstep (se 3 (by rfl) ⟨967838, by rfl⟩ : syracuseStep 5161805 = 1935677) B1935677
theorem B4899761 : Blo 1016603 4899761 := bstep (se 2 (by rfl) ⟨1837410, by rfl⟩ : syracuseStep 4899761 = 3674821) B3674821
theorem B1721297 : Blo 1016603 1721297 := bstep (se 2 (by rfl) ⟨645486, by rfl⟩ : syracuseStep 1721297 = 1290973) B1290973
theorem B2573329 : Blo 1016603 2573329 := bstep (se 2 (by rfl) ⟨964998, by rfl⟩ : syracuseStep 2573329 = 1929997) B1929997
theorem B3261485 : Blo 1016603 3261485 := bstep (se 3 (by rfl) ⟨611528, by rfl⟩ : syracuseStep 3261485 = 1223057) B1223057
theorem B1721425 : Blo 1016603 1721425 := bstep (se 2 (by rfl) ⟨645534, by rfl⟩ : syracuseStep 1721425 = 1291069) B1291069
theorem B1721459 : Blo 1016603 1721459 := bstep (se 1 (by rfl) ⟨1291094, by rfl⟩ : syracuseStep 1721459 = 2582189) B2582189
theorem B1524929 : Blo 1016603 1524929 := bstep (se 2 (by rfl) ⟨571848, by rfl⟩ : syracuseStep 1524929 = 1143697) B1143697
theorem B1524947 : Blo 1016603 1524947 := bstep (se 1 (by rfl) ⟨1143710, by rfl⟩ : syracuseStep 1524947 = 2287421) B2287421
theorem B1524977 : Blo 1016603 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B1721587 : Blo 1016603 1721587 := bstep (se 1 (by rfl) ⟨1291190, by rfl⟩ : syracuseStep 1721587 = 2582381) B2582381
theorem B1524995 : Blo 1016603 1524995 := bstep (se 1 (by rfl) ⟨1143746, by rfl⟩ : syracuseStep 1524995 = 2287493) B2287493
theorem B1525025 : Blo 1016603 1525025 := bstep (se 2 (by rfl) ⟨571884, by rfl⟩ : syracuseStep 1525025 = 1143769) B1143769
theorem B2573603 : Blo 1016603 2573603 := bstep (se 1 (by rfl) ⟨1930202, by rfl⟩ : syracuseStep 2573603 = 3860405) B3860405
theorem B7062833 : Blo 1016603 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B1525043 : Blo 1016603 1525043 := bstep (se 1 (by rfl) ⟨1143782, by rfl⟩ : syracuseStep 1525043 = 2287565) B2287565
theorem B8701253 : Blo 1016603 8701253 := bstep (se 4 (by rfl) ⟨815742, by rfl⟩ : syracuseStep 8701253 = 1631485) B1631485
theorem B1525073 : Blo 1016603 1525073 := bstep (se 2 (by rfl) ⟨571902, by rfl⟩ : syracuseStep 1525073 = 1143805) B1143805
theorem B2901329 : Blo 1016603 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B1525091 : Blo 1016603 1525091 := bstep (se 1 (by rfl) ⟨1143818, by rfl⟩ : syracuseStep 1525091 = 2287637) B2287637
theorem B1525121 : Blo 1016603 1525121 := bstep (se 2 (by rfl) ⟨571920, by rfl⟩ : syracuseStep 1525121 = 1143841) B1143841
theorem B1721729 : Blo 1016603 1721729 := bstep (se 2 (by rfl) ⟨645648, by rfl⟩ : syracuseStep 1721729 = 1291297) B1291297
theorem B1525139 : Blo 1016603 1525139 := bstep (se 1 (by rfl) ⟨1143854, by rfl⟩ : syracuseStep 1525139 = 2287709) B2287709
theorem B1525169 : Blo 1016603 1525169 := bstep (se 2 (by rfl) ⟨571938, by rfl⟩ : syracuseStep 1525169 = 1143877) B1143877
theorem B12371381 : Blo 1016603 12371381 := bstep (se 5 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 12371381 = 1159817) B1159817
theorem B1525187 : Blo 1016603 1525187 := bstep (se 1 (by rfl) ⟨1143890, by rfl⟩ : syracuseStep 1525187 = 2287781) B2287781
theorem B1525217 : Blo 1016603 1525217 := bstep (se 2 (by rfl) ⟨571956, by rfl⟩ : syracuseStep 1525217 = 1143913) B1143913
theorem B2573795 : Blo 1016603 2573795 := bstep (se 1 (by rfl) ⟨1930346, by rfl⟩ : syracuseStep 2573795 = 3860693) B3860693
theorem B1525235 : Blo 1016603 1525235 := bstep (se 1 (by rfl) ⟨1143926, by rfl⟩ : syracuseStep 1525235 = 2287853) B2287853
theorem B1721857 : Blo 1016603 1721857 := bstep (se 2 (by rfl) ⟨645696, by rfl⟩ : syracuseStep 1721857 = 1291393) B1291393
theorem B1525265 : Blo 1016603 1525265 := bstep (se 2 (by rfl) ⟨571974, by rfl⟩ : syracuseStep 1525265 = 1143949) B1143949
theorem B1525283 : Blo 1016603 1525283 := bstep (se 1 (by rfl) ⟨1143962, by rfl⟩ : syracuseStep 1525283 = 2287925) B2287925
theorem B1721891 : Blo 1016603 1721891 := bstep (se 1 (by rfl) ⟨1291418, by rfl⟩ : syracuseStep 1721891 = 2582837) B2582837
theorem B1525313 : Blo 1016603 1525313 := bstep (se 2 (by rfl) ⟨571992, by rfl⟩ : syracuseStep 1525313 = 1143985) B1143985
theorem B1525331 : Blo 1016603 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B1525361 : Blo 1016603 1525361 := bstep (se 2 (by rfl) ⟨572010, by rfl⟩ : syracuseStep 1525361 = 1144021) B1144021
theorem B1525379 : Blo 1016603 1525379 := bstep (se 1 (by rfl) ⟨1144034, by rfl⟩ : syracuseStep 1525379 = 2288069) B2288069
theorem B1525409 : Blo 1016603 1525409 := bstep (se 2 (by rfl) ⟨572028, by rfl⟩ : syracuseStep 1525409 = 1144057) B1144057
theorem B1722019 : Blo 1016603 1722019 := bstep (se 1 (by rfl) ⟨1291514, by rfl⟩ : syracuseStep 1722019 = 2583029) B2583029
theorem B1525427 : Blo 1016603 1525427 := bstep (se 1 (by rfl) ⟨1144070, by rfl⟩ : syracuseStep 1525427 = 2288141) B2288141
theorem B1525457 : Blo 1016603 1525457 := bstep (se 2 (by rfl) ⟨572046, by rfl⟩ : syracuseStep 1525457 = 1144093) B1144093
theorem B1525475 : Blo 1016603 1525475 := bstep (se 1 (by rfl) ⟨1144106, by rfl⟩ : syracuseStep 1525475 = 2288213) B2288213
theorem B1525505 : Blo 1016603 1525505 := bstep (se 2 (by rfl) ⟨572064, by rfl⟩ : syracuseStep 1525505 = 1144129) B1144129
theorem B1525523 : Blo 1016603 1525523 := bstep (se 1 (by rfl) ⟨1144142, by rfl⟩ : syracuseStep 1525523 = 2288285) B2288285
theorem B1525553 : Blo 1016603 1525553 := bstep (se 2 (by rfl) ⟨572082, by rfl⟩ : syracuseStep 1525553 = 1144165) B1144165
theorem B1722161 : Blo 1016603 1722161 := bstep (se 2 (by rfl) ⟨645810, by rfl⟩ : syracuseStep 1722161 = 1291621) B1291621
theorem B1525571 : Blo 1016603 1525571 := bstep (se 1 (by rfl) ⟨1144178, by rfl⟩ : syracuseStep 1525571 = 2288357) B2288357
theorem B1525601 : Blo 1016603 1525601 := bstep (se 2 (by rfl) ⟨572100, by rfl⟩ : syracuseStep 1525601 = 1144201) B1144201
theorem B1525619 : Blo 1016603 1525619 := bstep (se 1 (by rfl) ⟨1144214, by rfl⟩ : syracuseStep 1525619 = 2288429) B2288429
theorem B1525649 : Blo 1016603 1525649 := bstep (se 2 (by rfl) ⟨572118, by rfl⟩ : syracuseStep 1525649 = 1144237) B1144237
theorem B1525667 : Blo 1016603 1525667 := bstep (se 1 (by rfl) ⟨1144250, by rfl⟩ : syracuseStep 1525667 = 2288501) B2288501
theorem B1525697 : Blo 1016603 1525697 := bstep (se 2 (by rfl) ⟨572136, by rfl⟩ : syracuseStep 1525697 = 1144273) B1144273
theorem B1525715 : Blo 1016603 1525715 := bstep (se 1 (by rfl) ⟨1144286, by rfl⟩ : syracuseStep 1525715 = 2288573) B2288573
theorem B1525745 : Blo 1016603 1525745 := bstep (se 2 (by rfl) ⟨572154, by rfl⟩ : syracuseStep 1525745 = 1144309) B1144309
theorem B8701937 : Blo 1016603 8701937 := bstep (se 2 (by rfl) ⟨3263226, by rfl⟩ : syracuseStep 8701937 = 6526453) B6526453
theorem B1525763 : Blo 1016603 1525763 := bstep (se 1 (by rfl) ⟨1144322, by rfl⟩ : syracuseStep 1525763 = 2288645) B2288645
theorem B1525793 : Blo 1016603 1525793 := bstep (se 2 (by rfl) ⟨572172, by rfl⟩ : syracuseStep 1525793 = 1144345) B1144345
theorem B1525811 : Blo 1016603 1525811 := bstep (se 1 (by rfl) ⟨1144358, by rfl⟩ : syracuseStep 1525811 = 2288717) B2288717
theorem B1525841 : Blo 1016603 1525841 := bstep (se 2 (by rfl) ⟨572190, by rfl⟩ : syracuseStep 1525841 = 1144381) B1144381
theorem B1525859 : Blo 1016603 1525859 := bstep (se 1 (by rfl) ⟨1144394, by rfl⟩ : syracuseStep 1525859 = 2288789) B2288789
theorem B1525889 : Blo 1016603 1525889 := bstep (se 2 (by rfl) ⟨572208, by rfl⟩ : syracuseStep 1525889 = 1144417) B1144417
theorem B1525907 : Blo 1016603 1525907 := bstep (se 1 (by rfl) ⟨1144430, by rfl⟩ : syracuseStep 1525907 = 2288861) B2288861
theorem B1525937 : Blo 1016603 1525937 := bstep (se 2 (by rfl) ⟨572226, by rfl⟩ : syracuseStep 1525937 = 1144453) B1144453
theorem B1525955 : Blo 1016603 1525955 := bstep (se 1 (by rfl) ⟨1144466, by rfl⟩ : syracuseStep 1525955 = 2288933) B2288933
theorem B1525985 : Blo 1016603 1525985 := bstep (se 2 (by rfl) ⟨572244, by rfl⟩ : syracuseStep 1525985 = 1144489) B1144489
theorem B1526003 : Blo 1016603 1526003 := bstep (se 1 (by rfl) ⟨1144502, by rfl⟩ : syracuseStep 1526003 = 2289005) B2289005
theorem B2443537 : Blo 1016603 2443537 := bstep (se 2 (by rfl) ⟨916326, by rfl⟩ : syracuseStep 2443537 = 1832653) B1832653
theorem B1526033 : Blo 1016603 1526033 := bstep (se 2 (by rfl) ⟨572262, by rfl⟩ : syracuseStep 1526033 = 1144525) B1144525
theorem B1526051 : Blo 1016603 1526051 := bstep (se 1 (by rfl) ⟨1144538, by rfl⟩ : syracuseStep 1526051 = 2289077) B2289077
theorem B1526081 : Blo 1016603 1526081 := bstep (se 2 (by rfl) ⟨572280, by rfl⟩ : syracuseStep 1526081 = 1144561) B1144561
theorem B1526099 : Blo 1016603 1526099 := bstep (se 1 (by rfl) ⟨1144574, by rfl⟩ : syracuseStep 1526099 = 2289149) B2289149
theorem B1526129 : Blo 1016603 1526129 := bstep (se 2 (by rfl) ⟨572298, by rfl⟩ : syracuseStep 1526129 = 1144597) B1144597
theorem B1526147 : Blo 1016603 1526147 := bstep (se 1 (by rfl) ⟨1144610, by rfl⟩ : syracuseStep 1526147 = 2289221) B2289221
theorem B2574737 : Blo 1016603 2574737 := bstep (se 2 (by rfl) ⟨965526, by rfl⟩ : syracuseStep 2574737 = 1931053) B1931053
theorem B1526177 : Blo 1016603 1526177 := bstep (se 2 (by rfl) ⟨572316, by rfl⟩ : syracuseStep 1526177 = 1144633) B1144633
theorem B1526195 : Blo 1016603 1526195 := bstep (se 1 (by rfl) ⟨1144646, by rfl⟩ : syracuseStep 1526195 = 2289293) B2289293
theorem B2574787 : Blo 1016603 2574787 := bstep (se 1 (by rfl) ⟨1931090, by rfl⟩ : syracuseStep 2574787 = 3862181) B3862181
theorem B1526225 : Blo 1016603 1526225 := bstep (se 2 (by rfl) ⟨572334, by rfl⟩ : syracuseStep 1526225 = 1144669) B1144669
theorem B1526243 : Blo 1016603 1526243 := bstep (se 1 (by rfl) ⟨1144682, by rfl⟩ : syracuseStep 1526243 = 2289365) B2289365
theorem B11618801 : Blo 1016603 11618801 := bstep (se 2 (by rfl) ⟨4357050, by rfl⟩ : syracuseStep 11618801 = 8714101) B8714101
theorem B1526273 : Blo 1016603 1526273 := bstep (se 2 (by rfl) ⟨572352, by rfl⟩ : syracuseStep 1526273 = 1144705) B1144705
theorem B1526291 : Blo 1016603 1526291 := bstep (se 1 (by rfl) ⟨1144718, by rfl⟩ : syracuseStep 1526291 = 2289437) B2289437
theorem B1526321 : Blo 1016603 1526321 := bstep (se 2 (by rfl) ⟨572370, by rfl⟩ : syracuseStep 1526321 = 1144741) B1144741
theorem B1526339 : Blo 1016603 1526339 := bstep (se 1 (by rfl) ⟨1144754, by rfl⟩ : syracuseStep 1526339 = 2289509) B2289509
theorem B2574929 : Blo 1016603 2574929 := bstep (se 2 (by rfl) ⟨965598, by rfl⟩ : syracuseStep 2574929 = 1931197) B1931197
theorem B1526369 : Blo 1016603 1526369 := bstep (se 2 (by rfl) ⟨572388, by rfl⟩ : syracuseStep 1526369 = 1144777) B1144777
theorem B9914993 : Blo 1016603 9914993 := bstep (se 2 (by rfl) ⟨3718122, by rfl⟩ : syracuseStep 9914993 = 7436245) B7436245
theorem B1526387 : Blo 1016603 1526387 := bstep (se 1 (by rfl) ⟨1144790, by rfl⟩ : syracuseStep 1526387 = 2289581) B2289581
theorem B4344461 : Blo 1016603 4344461 := bstep (se 3 (by rfl) ⟨814586, by rfl⟩ : syracuseStep 4344461 = 1629173) B1629173
theorem B1526417 : Blo 1016603 1526417 := bstep (se 2 (by rfl) ⟨572406, by rfl⟩ : syracuseStep 1526417 = 1144813) B1144813
theorem B1526435 : Blo 1016603 1526435 := bstep (se 1 (by rfl) ⟨1144826, by rfl⟩ : syracuseStep 1526435 = 2289653) B2289653
theorem B1526465 : Blo 1016603 1526465 := bstep (se 2 (by rfl) ⟨572424, by rfl⟩ : syracuseStep 1526465 = 1144849) B1144849
theorem B1526483 : Blo 1016603 1526483 := bstep (se 1 (by rfl) ⟨1144862, by rfl⟩ : syracuseStep 1526483 = 2289725) B2289725
theorem B1526513 : Blo 1016603 1526513 := bstep (se 2 (by rfl) ⟨572442, by rfl⟩ : syracuseStep 1526513 = 1144885) B1144885
theorem B1526531 : Blo 1016603 1526531 := bstep (se 1 (by rfl) ⟨1144898, by rfl⟩ : syracuseStep 1526531 = 2289797) B2289797
theorem B2902787 : Blo 1016603 2902787 := bstep (se 1 (by rfl) ⟨2177090, by rfl⟩ : syracuseStep 2902787 = 4354181) B4354181
theorem B1526561 : Blo 1016603 1526561 := bstep (se 2 (by rfl) ⟨572460, by rfl⟩ : syracuseStep 1526561 = 1144921) B1144921
theorem B3263267 : Blo 1016603 3263267 := bstep (se 1 (by rfl) ⟨2447450, by rfl⟩ : syracuseStep 3263267 = 4894901) B4894901
theorem B1526579 : Blo 1016603 1526579 := bstep (se 1 (by rfl) ⟨1144934, by rfl⟩ : syracuseStep 1526579 = 2289869) B2289869
theorem B1526609 : Blo 1016603 1526609 := bstep (se 2 (by rfl) ⟨572478, by rfl⟩ : syracuseStep 1526609 = 1144957) B1144957
theorem B1526627 : Blo 1016603 1526627 := bstep (se 1 (by rfl) ⟨1144970, by rfl⟩ : syracuseStep 1526627 = 2289941) B2289941
theorem B1526657 : Blo 1016603 1526657 := bstep (se 2 (by rfl) ⟨572496, by rfl⟩ : syracuseStep 1526657 = 1144993) B1144993
theorem B1526675 : Blo 1016603 1526675 := bstep (se 1 (by rfl) ⟨1145006, by rfl⟩ : syracuseStep 1526675 = 2290013) B2290013
theorem B1526705 : Blo 1016603 1526705 := bstep (se 2 (by rfl) ⟨572514, by rfl⟩ : syracuseStep 1526705 = 1145029) B1145029
theorem B1526723 : Blo 1016603 1526723 := bstep (se 1 (by rfl) ⟨1145042, by rfl⟩ : syracuseStep 1526723 = 2290085) B2290085
theorem B1526753 : Blo 1016603 1526753 := bstep (se 2 (by rfl) ⟨572532, by rfl⟩ : syracuseStep 1526753 = 1145065) B1145065
theorem B1526771 : Blo 1016603 1526771 := bstep (se 1 (by rfl) ⟨1145078, by rfl⟩ : syracuseStep 1526771 = 2290157) B2290157
theorem B1526801 : Blo 1016603 1526801 := bstep (se 2 (by rfl) ⟨572550, by rfl⟩ : syracuseStep 1526801 = 1145101) B1145101
theorem B1526819 : Blo 1016603 1526819 := bstep (se 1 (by rfl) ⟨1145114, by rfl⟩ : syracuseStep 1526819 = 2290229) B2290229
theorem B1526849 : Blo 1016603 1526849 := bstep (se 2 (by rfl) ⟨572568, by rfl⟩ : syracuseStep 1526849 = 1145137) B1145137
theorem B1526867 : Blo 1016603 1526867 := bstep (se 1 (by rfl) ⟨1145150, by rfl⟩ : syracuseStep 1526867 = 2290301) B2290301
theorem B1526897 : Blo 1016603 1526897 := bstep (se 2 (by rfl) ⟨572586, by rfl⟩ : syracuseStep 1526897 = 1145173) B1145173
theorem B1526915 : Blo 1016603 1526915 := bstep (se 1 (by rfl) ⟨1145186, by rfl⟩ : syracuseStep 1526915 = 2290373) B2290373
theorem B1526945 : Blo 1016603 1526945 := bstep (se 2 (by rfl) ⟨572604, by rfl⟩ : syracuseStep 1526945 = 1145209) B1145209
theorem B1526963 : Blo 1016603 1526963 := bstep (se 1 (by rfl) ⟨1145222, by rfl⟩ : syracuseStep 1526963 = 2290445) B2290445
theorem B1526993 : Blo 1016603 1526993 := bstep (se 2 (by rfl) ⟨572622, by rfl⟩ : syracuseStep 1526993 = 1145245) B1145245
theorem B1527011 : Blo 1016603 1527011 := bstep (se 1 (by rfl) ⟨1145258, by rfl⟩ : syracuseStep 1527011 = 2290517) B2290517
theorem B1527041 : Blo 1016603 1527041 := bstep (se 2 (by rfl) ⟨572640, by rfl⟩ : syracuseStep 1527041 = 1145281) B1145281
theorem B1527059 : Blo 1016603 1527059 := bstep (se 1 (by rfl) ⟨1145294, by rfl⟩ : syracuseStep 1527059 = 2290589) B2290589
theorem B1527089 : Blo 1016603 1527089 := bstep (se 2 (by rfl) ⟨572658, by rfl⟩ : syracuseStep 1527089 = 1145317) B1145317
theorem B1527107 : Blo 1016603 1527107 := bstep (se 1 (by rfl) ⟨1145330, by rfl⟩ : syracuseStep 1527107 = 2290661) B2290661
theorem B4902221 : Blo 1016603 4902221 := bstep (se 3 (by rfl) ⟨919166, by rfl⟩ : syracuseStep 4902221 = 1838333) B1838333
theorem B1527137 : Blo 1016603 1527137 := bstep (se 2 (by rfl) ⟨572676, by rfl⟩ : syracuseStep 1527137 = 1145353) B1145353
theorem B1527155 : Blo 1016603 1527155 := bstep (se 1 (by rfl) ⟨1145366, by rfl⟩ : syracuseStep 1527155 = 2290733) B2290733
theorem B1527185 : Blo 1016603 1527185 := bstep (se 2 (by rfl) ⟨572694, by rfl⟩ : syracuseStep 1527185 = 1145389) B1145389
theorem B1527203 : Blo 1016603 1527203 := bstep (se 1 (by rfl) ⟨1145402, by rfl⟩ : syracuseStep 1527203 = 2290805) B2290805
theorem B1527233 : Blo 1016603 1527233 := bstep (se 2 (by rfl) ⟨572712, by rfl⟩ : syracuseStep 1527233 = 1145425) B1145425
theorem B1527251 : Blo 1016603 1527251 := bstep (se 1 (by rfl) ⟨1145438, by rfl⟩ : syracuseStep 1527251 = 2290877) B2290877
theorem B1527281 : Blo 1016603 1527281 := bstep (se 2 (by rfl) ⟨572730, by rfl⟩ : syracuseStep 1527281 = 1145461) B1145461
theorem B1527299 : Blo 1016603 1527299 := bstep (se 1 (by rfl) ⟨1145474, by rfl⟩ : syracuseStep 1527299 = 2290949) B2290949
theorem B1527329 : Blo 1016603 1527329 := bstep (se 2 (by rfl) ⟨572748, by rfl⟩ : syracuseStep 1527329 = 1145497) B1145497
theorem B2903597 : Blo 1016603 2903597 := bstep (se 3 (by rfl) ⟨544424, by rfl⟩ : syracuseStep 2903597 = 1088849) B1088849
theorem B2575921 : Blo 1016603 2575921 := bstep (se 2 (by rfl) ⟨965970, by rfl⟩ : syracuseStep 2575921 = 1931941) B1931941
theorem B1527347 : Blo 1016603 1527347 := bstep (se 1 (by rfl) ⟨1145510, by rfl⟩ : syracuseStep 1527347 = 2291021) B2291021
theorem B1527377 : Blo 1016603 1527377 := bstep (se 2 (by rfl) ⟨572766, by rfl⟩ : syracuseStep 1527377 = 1145533) B1145533
theorem B1527395 : Blo 1016603 1527395 := bstep (se 1 (by rfl) ⟨1145546, by rfl⟩ : syracuseStep 1527395 = 2291093) B2291093
theorem B1527425 : Blo 1016603 1527425 := bstep (se 2 (by rfl) ⟨572784, by rfl⟩ : syracuseStep 1527425 = 1145569) B1145569
theorem B1527443 : Blo 1016603 1527443 := bstep (se 1 (by rfl) ⟨1145582, by rfl⟩ : syracuseStep 1527443 = 2291165) B2291165
theorem B1527473 : Blo 1016603 1527473 := bstep (se 2 (by rfl) ⟨572802, by rfl⟩ : syracuseStep 1527473 = 1145605) B1145605
theorem B5164721 : Blo 1016603 5164721 := bstep (se 2 (by rfl) ⟨1936770, by rfl⟩ : syracuseStep 5164721 = 3873541) B3873541
theorem B1527491 : Blo 1016603 1527491 := bstep (se 1 (by rfl) ⟨1145618, by rfl⟩ : syracuseStep 1527491 = 2291237) B2291237
theorem B1527521 : Blo 1016603 1527521 := bstep (se 2 (by rfl) ⟨572820, by rfl⟩ : syracuseStep 1527521 = 1145641) B1145641
theorem B2903789 : Blo 1016603 2903789 := bstep (se 3 (by rfl) ⟨544460, by rfl⟩ : syracuseStep 2903789 = 1088921) B1088921
theorem B1527539 : Blo 1016603 1527539 := bstep (se 1 (by rfl) ⟨1145654, by rfl⟩ : syracuseStep 1527539 = 2291309) B2291309
theorem B1527569 : Blo 1016603 1527569 := bstep (se 2 (by rfl) ⟨572838, by rfl⟩ : syracuseStep 1527569 = 1145677) B1145677
theorem B1527587 : Blo 1016603 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B1527617 : Blo 1016603 1527617 := bstep (se 2 (by rfl) ⟨572856, by rfl⟩ : syracuseStep 1527617 = 1145713) B1145713
theorem B2576195 : Blo 1016603 2576195 := bstep (se 1 (by rfl) ⟨1932146, by rfl⟩ : syracuseStep 2576195 = 3864293) B3864293
theorem B1527635 : Blo 1016603 1527635 := bstep (se 1 (by rfl) ⟨1145726, by rfl⟩ : syracuseStep 1527635 = 2291453) B2291453
theorem B1527665 : Blo 1016603 1527665 := bstep (se 2 (by rfl) ⟨572874, by rfl⟩ : syracuseStep 1527665 = 1145749) B1145749
theorem B1527683 : Blo 1016603 1527683 := bstep (se 1 (by rfl) ⟨1145762, by rfl⟩ : syracuseStep 1527683 = 2291525) B2291525
theorem B4706189 : Blo 1016603 4706189 := bstep (se 3 (by rfl) ⟨882410, by rfl⟩ : syracuseStep 4706189 = 1764821) B1764821
theorem B1527713 : Blo 1016603 1527713 := bstep (se 2 (by rfl) ⟨572892, by rfl⟩ : syracuseStep 1527713 = 1145785) B1145785
theorem B1527731 : Blo 1016603 1527731 := bstep (se 1 (by rfl) ⟨1145798, by rfl⟩ : syracuseStep 1527731 = 2291597) B2291597
theorem B1527761 : Blo 1016603 1527761 := bstep (se 2 (by rfl) ⟨572910, by rfl⟩ : syracuseStep 1527761 = 1145821) B1145821
theorem B1527779 : Blo 1016603 1527779 := bstep (se 1 (by rfl) ⟨1145834, by rfl⟩ : syracuseStep 1527779 = 2291669) B2291669
theorem B1527809 : Blo 1016603 1527809 := bstep (se 2 (by rfl) ⟨572928, by rfl⟩ : syracuseStep 1527809 = 1145857) B1145857
theorem B2510851 : Blo 1016603 2510851 := bstep (se 1 (by rfl) ⟨1883138, by rfl⟩ : syracuseStep 2510851 = 3766277) B3766277
theorem B2576387 : Blo 1016603 2576387 := bstep (se 1 (by rfl) ⟨1932290, by rfl⟩ : syracuseStep 2576387 = 3864581) B3864581
theorem B1527827 : Blo 1016603 1527827 := bstep (se 1 (by rfl) ⟨1145870, by rfl⟩ : syracuseStep 1527827 = 2291741) B2291741
theorem B1527857 : Blo 1016603 1527857 := bstep (se 2 (by rfl) ⟨572946, by rfl⟩ : syracuseStep 1527857 = 1145893) B1145893
theorem B4411441 : Blo 1016603 4411441 := bstep (se 2 (by rfl) ⟨1654290, by rfl⟩ : syracuseStep 4411441 = 3308581) B3308581
theorem B1527875 : Blo 1016603 1527875 := bstep (se 1 (by rfl) ⟨1145906, by rfl⟩ : syracuseStep 1527875 = 2291813) B2291813
theorem B1527905 : Blo 1016603 1527905 := bstep (se 2 (by rfl) ⟨572964, by rfl⟩ : syracuseStep 1527905 = 1145929) B1145929
theorem B1527923 : Blo 1016603 1527923 := bstep (se 1 (by rfl) ⟨1145942, by rfl⟩ : syracuseStep 1527923 = 2291885) B2291885
theorem B1527953 : Blo 1016603 1527953 := bstep (se 2 (by rfl) ⟨572982, by rfl⟩ : syracuseStep 1527953 = 1145965) B1145965
theorem B1527971 : Blo 1016603 1527971 := bstep (se 1 (by rfl) ⟨1145978, by rfl⟩ : syracuseStep 1527971 = 2291957) B2291957
theorem B1528001 : Blo 1016603 1528001 := bstep (se 2 (by rfl) ⟨573000, by rfl⟩ : syracuseStep 1528001 = 1146001) B1146001
theorem B1528019 : Blo 1016603 1528019 := bstep (se 1 (by rfl) ⟨1146014, by rfl⟩ : syracuseStep 1528019 = 2292029) B2292029
theorem B1528049 : Blo 1016603 1528049 := bstep (se 2 (by rfl) ⟨573018, by rfl⟩ : syracuseStep 1528049 = 1146037) B1146037
theorem B1528067 : Blo 1016603 1528067 := bstep (se 1 (by rfl) ⟨1146050, by rfl⟩ : syracuseStep 1528067 = 2292101) B2292101
theorem B7852301 : Blo 1016603 7852301 := bstep (se 3 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 7852301 = 2944613) B2944613
theorem B1528097 : Blo 1016603 1528097 := bstep (se 2 (by rfl) ⟨573036, by rfl⟩ : syracuseStep 1528097 = 1146073) B1146073
theorem B1528115 : Blo 1016603 1528115 := bstep (se 1 (by rfl) ⟨1146086, by rfl⟩ : syracuseStep 1528115 = 2292173) B2292173
theorem B1528145 : Blo 1016603 1528145 := bstep (se 2 (by rfl) ⟨573054, by rfl⟩ : syracuseStep 1528145 = 1146109) B1146109
theorem B1528163 : Blo 1016603 1528163 := bstep (se 1 (by rfl) ⟨1146122, by rfl⟩ : syracuseStep 1528163 = 2292245) B2292245
theorem B1528193 : Blo 1016603 1528193 := bstep (se 2 (by rfl) ⟨573072, by rfl⟩ : syracuseStep 1528193 = 1146145) B1146145
theorem B1528211 : Blo 1016603 1528211 := bstep (se 1 (by rfl) ⟨1146158, by rfl⟩ : syracuseStep 1528211 = 2292317) B2292317
theorem B1528241 : Blo 1016603 1528241 := bstep (se 2 (by rfl) ⟨573090, by rfl⟩ : syracuseStep 1528241 = 1146181) B1146181
theorem B1528259 : Blo 1016603 1528259 := bstep (se 1 (by rfl) ⟨1146194, by rfl⟩ : syracuseStep 1528259 = 2292389) B2292389
theorem B1528289 : Blo 1016603 1528289 := bstep (se 2 (by rfl) ⟨573108, by rfl⟩ : syracuseStep 1528289 = 1146217) B1146217
theorem B1528307 : Blo 1016603 1528307 := bstep (se 1 (by rfl) ⟨1146230, by rfl⟩ : syracuseStep 1528307 = 2292461) B2292461
theorem B1528337 : Blo 1016603 1528337 := bstep (se 2 (by rfl) ⟨573126, by rfl⟩ : syracuseStep 1528337 = 1146253) B1146253
theorem B1528355 : Blo 1016603 1528355 := bstep (se 1 (by rfl) ⟨1146266, by rfl⟩ : syracuseStep 1528355 = 2292533) B2292533
theorem B3265073 : Blo 1016603 3265073 := bstep (se 2 (by rfl) ⟨1224402, by rfl⟩ : syracuseStep 3265073 = 2448805) B2448805
theorem B1528385 : Blo 1016603 1528385 := bstep (se 2 (by rfl) ⟨573144, by rfl⟩ : syracuseStep 1528385 = 1146289) B1146289
theorem B10998341 : Blo 1016603 10998341 := bstep (se 4 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 10998341 = 2062189) B2062189
theorem B1528403 : Blo 1016603 1528403 := bstep (se 1 (by rfl) ⟨1146302, by rfl⟩ : syracuseStep 1528403 = 2292605) B2292605
theorem B3265123 : Blo 1016603 3265123 := bstep (se 1 (by rfl) ⟨2448842, by rfl⟩ : syracuseStep 3265123 = 4897685) B4897685
theorem B1528433 : Blo 1016603 1528433 := bstep (se 2 (by rfl) ⟨573162, by rfl⟩ : syracuseStep 1528433 = 1146325) B1146325
theorem B1528451 : Blo 1016603 1528451 := bstep (se 1 (by rfl) ⟨1146338, by rfl⟩ : syracuseStep 1528451 = 2292677) B2292677
theorem B8245901 : Blo 1016603 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B1528481 : Blo 1016603 1528481 := bstep (se 2 (by rfl) ⟨573180, by rfl⟩ : syracuseStep 1528481 = 1146361) B1146361
theorem B1528499 : Blo 1016603 1528499 := bstep (se 1 (by rfl) ⟨1146374, by rfl⟩ : syracuseStep 1528499 = 2292749) B2292749
theorem B2904781 : Blo 1016603 2904781 := bstep (se 3 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 2904781 = 1089293) B1089293
theorem B1528529 : Blo 1016603 1528529 := bstep (se 2 (by rfl) ⟨573198, by rfl⟩ : syracuseStep 1528529 = 1146397) B1146397
theorem B1528547 : Blo 1016603 1528547 := bstep (se 1 (by rfl) ⟨1146410, by rfl⟩ : syracuseStep 1528547 = 2292821) B2292821
theorem B1528577 : Blo 1016603 1528577 := bstep (se 2 (by rfl) ⟨573216, by rfl⟩ : syracuseStep 1528577 = 1146433) B1146433
theorem B1528595 : Blo 1016603 1528595 := bstep (se 1 (by rfl) ⟨1146446, by rfl⟩ : syracuseStep 1528595 = 2292893) B2292893
theorem B1528625 : Blo 1016603 1528625 := bstep (se 2 (by rfl) ⟨573234, by rfl⟩ : syracuseStep 1528625 = 1146469) B1146469
theorem B1528643 : Blo 1016603 1528643 := bstep (se 1 (by rfl) ⟨1146482, by rfl⟩ : syracuseStep 1528643 = 2292965) B2292965
theorem B1528673 : Blo 1016603 1528673 := bstep (se 2 (by rfl) ⟨573252, by rfl⟩ : syracuseStep 1528673 = 1146505) B1146505
theorem B1528691 : Blo 1016603 1528691 := bstep (se 1 (by rfl) ⟨1146518, by rfl⟩ : syracuseStep 1528691 = 2293037) B2293037
theorem B4641677 : Blo 1016603 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B1528721 : Blo 1016603 1528721 := bstep (se 2 (by rfl) ⟨573270, by rfl⟩ : syracuseStep 1528721 = 1146541) B1146541
theorem B1528739 : Blo 1016603 1528739 := bstep (se 1 (by rfl) ⟨1146554, by rfl⟩ : syracuseStep 1528739 = 2293109) B2293109
theorem B2577329 : Blo 1016603 2577329 := bstep (se 2 (by rfl) ⟨966498, by rfl⟩ : syracuseStep 2577329 = 1932997) B1932997
theorem B1528769 : Blo 1016603 1528769 := bstep (se 2 (by rfl) ⟨573288, by rfl⟩ : syracuseStep 1528769 = 1146577) B1146577
theorem B1528787 : Blo 1016603 1528787 := bstep (se 1 (by rfl) ⟨1146590, by rfl⟩ : syracuseStep 1528787 = 2293181) B2293181
theorem B2577379 : Blo 1016603 2577379 := bstep (se 1 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 2577379 = 3866069) B3866069
theorem B8803313 : Blo 1016603 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B1528817 : Blo 1016603 1528817 := bstep (se 2 (by rfl) ⟨573306, by rfl⟩ : syracuseStep 1528817 = 1146613) B1146613
theorem B1528835 : Blo 1016603 1528835 := bstep (se 1 (by rfl) ⟨1146626, by rfl⟩ : syracuseStep 1528835 = 2293253) B2293253
theorem B4641805 : Blo 1016603 4641805 := bstep (se 3 (by rfl) ⟨870338, by rfl⟩ : syracuseStep 4641805 = 1740677) B1740677
theorem B1528865 : Blo 1016603 1528865 := bstep (se 2 (by rfl) ⟨573324, by rfl⟩ : syracuseStep 1528865 = 1146649) B1146649
theorem B1528883 : Blo 1016603 1528883 := bstep (se 1 (by rfl) ⟨1146662, by rfl⟩ : syracuseStep 1528883 = 2293325) B2293325
theorem B7722053 : Blo 1016603 7722053 := bstep (se 4 (by rfl) ⟨723942, by rfl⟩ : syracuseStep 7722053 = 1447885) B1447885
theorem B1528913 : Blo 1016603 1528913 := bstep (se 2 (by rfl) ⟨573342, by rfl⟩ : syracuseStep 1528913 = 1146685) B1146685
theorem B1528931 : Blo 1016603 1528931 := bstep (se 1 (by rfl) ⟨1146698, by rfl⟩ : syracuseStep 1528931 = 2293397) B2293397
theorem B5166179 : Blo 1016603 5166179 := bstep (se 1 (by rfl) ⟨3874634, by rfl⟩ : syracuseStep 5166179 = 7749269) B7749269
theorem B2577521 : Blo 1016603 2577521 := bstep (se 2 (by rfl) ⟨966570, by rfl⟩ : syracuseStep 2577521 = 1933141) B1933141
theorem B1528961 : Blo 1016603 1528961 := bstep (se 2 (by rfl) ⟨573360, by rfl⟩ : syracuseStep 1528961 = 1146721) B1146721
theorem B1528979 : Blo 1016603 1528979 := bstep (se 1 (by rfl) ⟨1146734, by rfl⟩ : syracuseStep 1528979 = 2293469) B2293469
theorem B1529009 : Blo 1016603 1529009 := bstep (se 2 (by rfl) ⟨573378, by rfl⟩ : syracuseStep 1529009 = 1146757) B1146757
theorem B1529027 : Blo 1016603 1529027 := bstep (se 1 (by rfl) ⟨1146770, by rfl⟩ : syracuseStep 1529027 = 2293541) B2293541
theorem B1529057 : Blo 1016603 1529057 := bstep (se 2 (by rfl) ⟨573396, by rfl⟩ : syracuseStep 1529057 = 1146793) B1146793
theorem B1529075 : Blo 1016603 1529075 := bstep (se 1 (by rfl) ⟨1146806, by rfl⟩ : syracuseStep 1529075 = 2293613) B2293613
theorem B5231885 : Blo 1016603 5231885 := bstep (se 3 (by rfl) ⟨980978, by rfl⟩ : syracuseStep 5231885 = 1961957) B1961957
theorem B1529105 : Blo 1016603 1529105 := bstep (se 2 (by rfl) ⟨573414, by rfl⟩ : syracuseStep 1529105 = 1146829) B1146829
theorem B1529123 : Blo 1016603 1529123 := bstep (se 1 (by rfl) ⟨1146842, by rfl⟩ : syracuseStep 1529123 = 2293685) B2293685
theorem B3265841 : Blo 1016603 3265841 := bstep (se 2 (by rfl) ⟨1224690, by rfl⟩ : syracuseStep 3265841 = 2449381) B2449381
theorem B1529153 : Blo 1016603 1529153 := bstep (se 2 (by rfl) ⟨573432, by rfl⟩ : syracuseStep 1529153 = 1146865) B1146865
theorem B1529171 : Blo 1016603 1529171 := bstep (se 1 (by rfl) ⟨1146878, by rfl⟩ : syracuseStep 1529171 = 2293757) B2293757
theorem B1529201 : Blo 1016603 1529201 := bstep (se 2 (by rfl) ⟨573450, by rfl⟩ : syracuseStep 1529201 = 1146901) B1146901
theorem B1529219 : Blo 1016603 1529219 := bstep (se 1 (by rfl) ⟨1146914, by rfl⟩ : syracuseStep 1529219 = 2293829) B2293829
theorem B1529249 : Blo 1016603 1529249 := bstep (se 2 (by rfl) ⟨573468, by rfl⟩ : syracuseStep 1529249 = 1146937) B1146937
theorem B1529267 : Blo 1016603 1529267 := bstep (se 1 (by rfl) ⟨1146950, by rfl⟩ : syracuseStep 1529267 = 2293901) B2293901
theorem B2446787 : Blo 1016603 2446787 := bstep (se 1 (by rfl) ⟨1835090, by rfl⟩ : syracuseStep 2446787 = 3670181) B3670181
theorem B1529297 : Blo 1016603 1529297 := bstep (se 2 (by rfl) ⟨573486, by rfl⟩ : syracuseStep 1529297 = 1146973) B1146973
theorem B1529315 : Blo 1016603 1529315 := bstep (se 1 (by rfl) ⟨1146986, by rfl⟩ : syracuseStep 1529315 = 2293973) B2293973
theorem B1529345 : Blo 1016603 1529345 := bstep (se 2 (by rfl) ⟨573504, by rfl⟩ : syracuseStep 1529345 = 1147009) B1147009
theorem B1529363 : Blo 1016603 1529363 := bstep (se 1 (by rfl) ⟨1147022, by rfl⟩ : syracuseStep 1529363 = 2294045) B2294045
theorem B1529393 : Blo 1016603 1529393 := bstep (se 2 (by rfl) ⟨573522, by rfl⟩ : syracuseStep 1529393 = 1147045) B1147045
theorem B1529411 : Blo 1016603 1529411 := bstep (se 1 (by rfl) ⟨1147058, by rfl⟩ : syracuseStep 1529411 = 2294117) B2294117
theorem B1529441 : Blo 1016603 1529441 := bstep (se 2 (by rfl) ⟨573540, by rfl⟩ : syracuseStep 1529441 = 1147081) B1147081
theorem B1529459 : Blo 1016603 1529459 := bstep (se 1 (by rfl) ⟨1147094, by rfl⟩ : syracuseStep 1529459 = 2294189) B2294189
theorem B1529489 : Blo 1016603 1529489 := bstep (se 2 (by rfl) ⟨573558, by rfl⟩ : syracuseStep 1529489 = 1147117) B1147117
theorem B1529507 : Blo 1016603 1529507 := bstep (se 1 (by rfl) ⟨1147130, by rfl⟩ : syracuseStep 1529507 = 2294261) B2294261
theorem B1529537 : Blo 1016603 1529537 := bstep (se 2 (by rfl) ⟨573576, by rfl⟩ : syracuseStep 1529537 = 1147153) B1147153
theorem B1529555 : Blo 1016603 1529555 := bstep (se 1 (by rfl) ⟨1147166, by rfl⟩ : syracuseStep 1529555 = 2294333) B2294333
theorem B1529585 : Blo 1016603 1529585 := bstep (se 2 (by rfl) ⟨573594, by rfl⟩ : syracuseStep 1529585 = 1147189) B1147189
theorem B1529603 : Blo 1016603 1529603 := bstep (se 1 (by rfl) ⟨1147202, by rfl⟩ : syracuseStep 1529603 = 2294405) B2294405
theorem B1529633 : Blo 1016603 1529633 := bstep (se 2 (by rfl) ⟨573612, by rfl⟩ : syracuseStep 1529633 = 1147225) B1147225
theorem B3266353 : Blo 1016603 3266353 := bstep (se 2 (by rfl) ⟨1224882, by rfl⟩ : syracuseStep 3266353 = 2449765) B2449765
theorem B1529651 : Blo 1016603 1529651 := bstep (se 1 (by rfl) ⟨1147238, by rfl⟩ : syracuseStep 1529651 = 2294477) B2294477
theorem B4970317 : Blo 1016603 4970317 := bstep (se 3 (by rfl) ⟨931934, by rfl⟩ : syracuseStep 4970317 = 1863869) B1863869
theorem B1529681 : Blo 1016603 1529681 := bstep (se 2 (by rfl) ⟨573630, by rfl⟩ : syracuseStep 1529681 = 1147261) B1147261
theorem B1529699 : Blo 1016603 1529699 := bstep (se 1 (by rfl) ⟨1147274, by rfl⟩ : syracuseStep 1529699 = 2294549) B2294549
theorem B1529729 : Blo 1016603 1529729 := bstep (se 2 (by rfl) ⟨573648, by rfl⟩ : syracuseStep 1529729 = 1147297) B1147297
theorem B1529747 : Blo 1016603 1529747 := bstep (se 1 (by rfl) ⟨1147310, by rfl⟩ : syracuseStep 1529747 = 2294621) B2294621
theorem B1529777 : Blo 1016603 1529777 := bstep (se 2 (by rfl) ⟨573666, by rfl⟩ : syracuseStep 1529777 = 1147333) B1147333
theorem B1529795 : Blo 1016603 1529795 := bstep (se 1 (by rfl) ⟨1147346, by rfl⟩ : syracuseStep 1529795 = 2294693) B2294693
theorem B1529825 : Blo 1016603 1529825 := bstep (se 2 (by rfl) ⟨573684, by rfl⟩ : syracuseStep 1529825 = 1147369) B1147369
theorem B1529843 : Blo 1016603 1529843 := bstep (se 1 (by rfl) ⟨1147382, by rfl⟩ : syracuseStep 1529843 = 2294765) B2294765
theorem B1529873 : Blo 1016603 1529873 := bstep (se 2 (by rfl) ⟨573702, by rfl⟩ : syracuseStep 1529873 = 1147405) B1147405
theorem B1529891 : Blo 1016603 1529891 := bstep (se 1 (by rfl) ⟨1147418, by rfl⟩ : syracuseStep 1529891 = 2294837) B2294837
theorem B1529921 : Blo 1016603 1529921 := bstep (se 2 (by rfl) ⟨573720, by rfl⟩ : syracuseStep 1529921 = 1147441) B1147441
theorem B4970573 : Blo 1016603 4970573 := bstep (se 3 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 4970573 = 1863965) B1863965
theorem B2578513 : Blo 1016603 2578513 := bstep (se 2 (by rfl) ⟨966942, by rfl⟩ : syracuseStep 2578513 = 1933885) B1933885
theorem B1529939 : Blo 1016603 1529939 := bstep (se 1 (by rfl) ⟨1147454, by rfl⟩ : syracuseStep 1529939 = 2294909) B2294909
theorem B1529969 : Blo 1016603 1529969 := bstep (se 2 (by rfl) ⟨573738, by rfl⟩ : syracuseStep 1529969 = 1147477) B1147477
theorem B1529987 : Blo 1016603 1529987 := bstep (se 1 (by rfl) ⟨1147490, by rfl⟩ : syracuseStep 1529987 = 2294981) B2294981
theorem B1530017 : Blo 1016603 1530017 := bstep (se 2 (by rfl) ⟨573756, by rfl⟩ : syracuseStep 1530017 = 1147513) B1147513
theorem B1530035 : Blo 1016603 1530035 := bstep (se 1 (by rfl) ⟨1147526, by rfl⟩ : syracuseStep 1530035 = 2295053) B2295053
theorem B1530065 : Blo 1016603 1530065 := bstep (se 2 (by rfl) ⟨573774, by rfl⟩ : syracuseStep 1530065 = 1147549) B1147549
theorem B1530083 : Blo 1016603 1530083 := bstep (se 1 (by rfl) ⟨1147562, by rfl⟩ : syracuseStep 1530083 = 2295125) B2295125
theorem B1530113 : Blo 1016603 1530113 := bstep (se 2 (by rfl) ⟨573792, by rfl⟩ : syracuseStep 1530113 = 1147585) B1147585
theorem B2447633 : Blo 1016603 2447633 := bstep (se 2 (by rfl) ⟨917862, by rfl⟩ : syracuseStep 2447633 = 1835725) B1835725
theorem B1530131 : Blo 1016603 1530131 := bstep (se 1 (by rfl) ⟨1147598, by rfl⟩ : syracuseStep 1530131 = 2295197) B2295197
theorem B1530161 : Blo 1016603 1530161 := bstep (se 2 (by rfl) ⟨573810, by rfl⟩ : syracuseStep 1530161 = 1147621) B1147621
theorem B1530179 : Blo 1016603 1530179 := bstep (se 1 (by rfl) ⟨1147634, by rfl⟩ : syracuseStep 1530179 = 2295269) B2295269
theorem B1530209 : Blo 1016603 1530209 := bstep (se 2 (by rfl) ⟨573828, by rfl⟩ : syracuseStep 1530209 = 1147657) B1147657
theorem B2578787 : Blo 1016603 2578787 := bstep (se 1 (by rfl) ⟨1934090, by rfl⟩ : syracuseStep 2578787 = 3868181) B3868181
theorem B2447729 : Blo 1016603 2447729 := bstep (se 2 (by rfl) ⟨917898, by rfl⟩ : syracuseStep 2447729 = 1835797) B1835797
theorem B1530227 : Blo 1016603 1530227 := bstep (se 1 (by rfl) ⟨1147670, by rfl⟩ : syracuseStep 1530227 = 2295341) B2295341
theorem B1530257 : Blo 1016603 1530257 := bstep (se 2 (by rfl) ⟨573846, by rfl⟩ : syracuseStep 1530257 = 1147693) B1147693
theorem B1530275 : Blo 1016603 1530275 := bstep (se 1 (by rfl) ⟨1147706, by rfl⟩ : syracuseStep 1530275 = 2295413) B2295413
theorem B11000245 : Blo 1016603 11000245 := bstep (se 5 (by rfl) ⟨515636, by rfl⟩ : syracuseStep 11000245 = 1031273) B1031273
theorem B1530305 : Blo 1016603 1530305 := bstep (se 2 (by rfl) ⟨573864, by rfl⟩ : syracuseStep 1530305 = 1147729) B1147729
theorem B1530323 : Blo 1016603 1530323 := bstep (se 1 (by rfl) ⟨1147742, by rfl⟩ : syracuseStep 1530323 = 2295485) B2295485
theorem B1530353 : Blo 1016603 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B1530371 : Blo 1016603 1530371 := bstep (se 1 (by rfl) ⟨1147778, by rfl⟩ : syracuseStep 1530371 = 2295557) B2295557
theorem B1530401 : Blo 1016603 1530401 := bstep (se 2 (by rfl) ⟨573900, by rfl⟩ : syracuseStep 1530401 = 1147801) B1147801
theorem B2578979 : Blo 1016603 2578979 := bstep (se 1 (by rfl) ⟨1934234, by rfl⟩ : syracuseStep 2578979 = 3868469) B3868469
theorem B1530419 : Blo 1016603 1530419 := bstep (se 1 (by rfl) ⟨1147814, by rfl⟩ : syracuseStep 1530419 = 2295629) B2295629
theorem B1530449 : Blo 1016603 1530449 := bstep (se 2 (by rfl) ⟨573918, by rfl⟩ : syracuseStep 1530449 = 1147837) B1147837
theorem B1530467 : Blo 1016603 1530467 := bstep (se 1 (by rfl) ⟨1147850, by rfl⟩ : syracuseStep 1530467 = 2295701) B2295701
theorem B1530497 : Blo 1016603 1530497 := bstep (se 2 (by rfl) ⟨573936, by rfl⟩ : syracuseStep 1530497 = 1147873) B1147873
theorem B1530515 : Blo 1016603 1530515 := bstep (se 1 (by rfl) ⟨1147886, by rfl⟩ : syracuseStep 1530515 = 2295773) B2295773
theorem B1530545 : Blo 1016603 1530545 := bstep (se 2 (by rfl) ⟨573954, by rfl⟩ : syracuseStep 1530545 = 1147909) B1147909
theorem B1530563 : Blo 1016603 1530563 := bstep (se 1 (by rfl) ⟨1147922, by rfl⟩ : syracuseStep 1530563 = 2295845) B2295845
theorem B1530593 : Blo 1016603 1530593 := bstep (se 2 (by rfl) ⟨573972, by rfl⟩ : syracuseStep 1530593 = 1147945) B1147945
theorem B1530611 : Blo 1016603 1530611 := bstep (se 1 (by rfl) ⟨1147958, by rfl⟩ : syracuseStep 1530611 = 2295917) B2295917
theorem B1530641 : Blo 1016603 1530641 := bstep (se 2 (by rfl) ⟨573990, by rfl⟩ : syracuseStep 1530641 = 1147981) B1147981
theorem B1530659 : Blo 1016603 1530659 := bstep (se 1 (by rfl) ⟨1147994, by rfl⟩ : syracuseStep 1530659 = 2295989) B2295989
theorem B3431213 : Blo 1016603 3431213 := bstep (se 3 (by rfl) ⟨643352, by rfl⟩ : syracuseStep 3431213 = 1286705) B1286705
theorem B1530689 : Blo 1016603 1530689 := bstep (se 2 (by rfl) ⟨574008, by rfl⟩ : syracuseStep 1530689 = 1148017) B1148017
theorem B1530707 : Blo 1016603 1530707 := bstep (se 1 (by rfl) ⟨1148030, by rfl⟩ : syracuseStep 1530707 = 2296061) B2296061
theorem B3431267 : Blo 1016603 3431267 := bstep (se 1 (by rfl) ⟨2573450, by rfl⟩ : syracuseStep 3431267 = 5146901) B5146901
theorem B1530737 : Blo 1016603 1530737 := bstep (se 2 (by rfl) ⟨574026, by rfl⟩ : syracuseStep 1530737 = 1148053) B1148053
theorem B1530755 : Blo 1016603 1530755 := bstep (se 1 (by rfl) ⟨1148066, by rfl⟩ : syracuseStep 1530755 = 2296133) B2296133
theorem B3267469 : Blo 1016603 3267469 := bstep (se 3 (by rfl) ⟨612650, by rfl⟩ : syracuseStep 3267469 = 1225301) B1225301
theorem B1530785 : Blo 1016603 1530785 := bstep (se 2 (by rfl) ⟨574044, by rfl⟩ : syracuseStep 1530785 = 1148089) B1148089
theorem B4348835 : Blo 1016603 4348835 := bstep (se 1 (by rfl) ⟨3261626, by rfl⟩ : syracuseStep 4348835 = 6523253) B6523253
theorem B1530803 : Blo 1016603 1530803 := bstep (se 1 (by rfl) ⟨1148102, by rfl⟩ : syracuseStep 1530803 = 2296205) B2296205
theorem B3267533 : Blo 1016603 3267533 := bstep (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) B1225325
theorem B1530833 : Blo 1016603 1530833 := bstep (se 2 (by rfl) ⟨574062, by rfl⟩ : syracuseStep 1530833 = 1148125) B1148125
theorem B1530851 : Blo 1016603 1530851 := bstep (se 1 (by rfl) ⟨1148138, by rfl⟩ : syracuseStep 1530851 = 2296277) B2296277
theorem B1530881 : Blo 1016603 1530881 := bstep (se 2 (by rfl) ⟨574080, by rfl⟩ : syracuseStep 1530881 = 1148161) B1148161
theorem B1530899 : Blo 1016603 1530899 := bstep (se 1 (by rfl) ⟨1148174, by rfl⟩ : syracuseStep 1530899 = 2296349) B2296349
theorem B1629281 : Blo 1016603 1629281 := bstep (se 2 (by rfl) ⟨610980, by rfl⟩ : syracuseStep 1629281 = 1221961) B1221961
theorem B4643939 : Blo 1016603 4643939 := bstep (se 1 (by rfl) ⟨3482954, by rfl⟩ : syracuseStep 4643939 = 6965909) B6965909
theorem B3431537 : Blo 1016603 3431537 := bstep (se 2 (by rfl) ⟨1286826, by rfl⟩ : syracuseStep 3431537 = 2573653) B2573653
theorem B2579921 : Blo 1016603 2579921 := bstep (se 2 (by rfl) ⟨967470, by rfl⟩ : syracuseStep 2579921 = 1934941) B1934941
theorem B2579971 : Blo 1016603 2579971 := bstep (se 1 (by rfl) ⟨1934978, by rfl⟩ : syracuseStep 2579971 = 3869957) B3869957
theorem B3137069 : Blo 1016603 3137069 := bstep (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) B1176401
theorem B14114357 : Blo 1016603 14114357 := bstep (se 5 (by rfl) ⟨661610, by rfl⟩ : syracuseStep 14114357 = 1323221) B1323221
theorem B3432077 : Blo 1016603 3432077 := bstep (se 3 (by rfl) ⟨643514, by rfl⟩ : syracuseStep 3432077 = 1287029) B1287029
theorem B2580113 : Blo 1016603 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B2449073 : Blo 1016603 2449073 := bstep (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) B1836805
theorem B3432131 : Blo 1016603 3432131 := bstep (se 1 (by rfl) ⟨2574098, by rfl⟩ : syracuseStep 3432131 = 5148197) B5148197
theorem B1630115 : Blo 1016603 1630115 := bstep (se 1 (by rfl) ⟨1222586, by rfl⟩ : syracuseStep 1630115 = 2445173) B2445173
theorem B1630147 : Blo 1016603 1630147 := bstep (se 1 (by rfl) ⟨1222610, by rfl⟩ : syracuseStep 1630147 = 2445221) B2445221
theorem B3432401 : Blo 1016603 3432401 := bstep (se 2 (by rfl) ⟨1287150, by rfl⟩ : syracuseStep 3432401 = 2574301) B2574301
theorem B3301489 : Blo 1016603 3301489 := bstep (se 2 (by rfl) ⟨1238058, by rfl⟩ : syracuseStep 3301489 = 2476117) B2476117
theorem B5497093 : Blo 1016603 5497093 := bstep (se 4 (by rfl) ⟨515352, by rfl⟩ : syracuseStep 5497093 = 1030705) B1030705
theorem B13066595 : Blo 1016603 13066595 := bstep (se 1 (by rfl) ⟨9799946, by rfl⟩ : syracuseStep 13066595 = 19599893) B19599893
theorem B3432941 : Blo 1016603 3432941 := bstep (se 3 (by rfl) ⟨643676, by rfl⟩ : syracuseStep 3432941 = 1287353) B1287353
theorem B5792269 : Blo 1016603 5792269 := bstep (se 3 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 5792269 = 2172101) B2172101
theorem B3432995 : Blo 1016603 3432995 := bstep (se 1 (by rfl) ⟨2574746, by rfl⟩ : syracuseStep 3432995 = 5149493) B5149493
theorem B2581105 : Blo 1016603 2581105 := bstep (se 2 (by rfl) ⟨967914, by rfl⟩ : syracuseStep 2581105 = 1935829) B1935829
theorem B3269315 : Blo 1016603 3269315 := bstep (se 1 (by rfl) ⟨2451986, by rfl⟩ : syracuseStep 3269315 = 4903973) B4903973
theorem B3433265 : Blo 1016603 3433265 := bstep (se 2 (by rfl) ⟨1287474, by rfl⟩ : syracuseStep 3433265 = 2574949) B2574949
theorem B1631075 : Blo 1016603 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B4350833 : Blo 1016603 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B2581379 : Blo 1016603 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B1631153 : Blo 1016603 1631153 := bstep (se 2 (by rfl) ⟨611682, by rfl⟩ : syracuseStep 1631153 = 1223365) B1223365
theorem B2581571 : Blo 1016603 2581571 := bstep (se 1 (by rfl) ⟨1936178, by rfl⟩ : syracuseStep 2581571 = 3872357) B3872357
theorem B1631377 : Blo 1016603 1631377 := bstep (se 2 (by rfl) ⟨611766, by rfl⟩ : syracuseStep 1631377 = 1223533) B1223533
theorem B2483345 : Blo 1016603 2483345 := bstep (se 2 (by rfl) ⟨931254, by rfl⟩ : syracuseStep 2483345 = 1862509) B1862509
theorem B3433805 : Blo 1016603 3433805 := bstep (se 3 (by rfl) ⟨643838, by rfl⟩ : syracuseStep 3433805 = 1287677) B1287677
theorem B3433859 : Blo 1016603 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B4122161 : Blo 1016603 4122161 := bstep (se 2 (by rfl) ⟨1545810, by rfl⟩ : syracuseStep 4122161 = 3091621) B3091621
theorem B6514253 : Blo 1016603 6514253 := bstep (se 3 (by rfl) ⟨1221422, by rfl⟩ : syracuseStep 6514253 = 2442845) B2442845
theorem B4646477 : Blo 1016603 4646477 := bstep (se 3 (by rfl) ⟨871214, by rfl⟩ : syracuseStep 4646477 = 1742429) B1742429
theorem B3434129 : Blo 1016603 3434129 := bstep (se 2 (by rfl) ⟨1287798, by rfl⟩ : syracuseStep 3434129 = 2575597) B2575597
theorem B4646641 : Blo 1016603 4646641 := bstep (se 2 (by rfl) ⟨1742490, by rfl⟩ : syracuseStep 4646641 = 3484981) B3484981
theorem B3860237 : Blo 1016603 3860237 := bstep (se 3 (by rfl) ⟨723794, by rfl⟩ : syracuseStep 3860237 = 1447589) B1447589
theorem B6612749 : Blo 1016603 6612749 := bstep (se 3 (by rfl) ⟨1239890, by rfl⟩ : syracuseStep 6612749 = 2479781) B2479781
theorem B2451217 : Blo 1016603 2451217 := bstep (se 2 (by rfl) ⟨919206, by rfl⟩ : syracuseStep 2451217 = 1838413) B1838413
theorem B6973219 : Blo 1016603 6973219 := bstep (se 1 (by rfl) ⟨5229914, by rfl⟩ : syracuseStep 6973219 = 10459829) B10459829
theorem B4187953 : Blo 1016603 4187953 := bstep (se 2 (by rfl) ⟨1570482, by rfl⟩ : syracuseStep 4187953 = 3140965) B3140965
theorem B8710001 : Blo 1016603 8710001 := bstep (se 2 (by rfl) ⟨3266250, by rfl⟩ : syracuseStep 8710001 = 6532501) B6532501
theorem B2287601 : Blo 1016603 2287601 := bstep (se 2 (by rfl) ⟨857850, by rfl⟩ : syracuseStep 2287601 = 1715701) B1715701
theorem B2582513 : Blo 1016603 2582513 := bstep (se 2 (by rfl) ⟨968442, by rfl⟩ : syracuseStep 2582513 = 1936885) B1936885
theorem B2287619 : Blo 1016603 2287619 := bstep (se 1 (by rfl) ⟨1715714, by rfl⟩ : syracuseStep 2287619 = 3431429) B3431429
theorem B7333901 : Blo 1016603 7333901 := bstep (se 3 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 7333901 = 2750213) B2750213
theorem B2582563 : Blo 1016603 2582563 := bstep (se 1 (by rfl) ⟨1936922, by rfl⟩ : syracuseStep 2582563 = 3873845) B3873845
theorem B2615377 : Blo 1016603 2615377 := bstep (se 2 (by rfl) ⟨980766, by rfl⟩ : syracuseStep 2615377 = 1961533) B1961533
theorem B3434669 : Blo 1016603 3434669 := bstep (se 3 (by rfl) ⟨644000, by rfl⟩ : syracuseStep 3434669 = 1288001) B1288001
theorem B2582705 : Blo 1016603 2582705 := bstep (se 2 (by rfl) ⟨968514, by rfl⟩ : syracuseStep 2582705 = 1937029) B1937029
theorem B6187205 : Blo 1016603 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B3434723 : Blo 1016603 3434723 := bstep (se 1 (by rfl) ⟨2576042, by rfl⟩ : syracuseStep 3434723 = 5152085) B5152085
theorem B2287889 : Blo 1016603 2287889 := bstep (se 2 (by rfl) ⟨857958, by rfl⟩ : syracuseStep 2287889 = 1715917) B1715917
theorem B2287907 : Blo 1016603 2287907 := bstep (se 1 (by rfl) ⟨1715930, by rfl⟩ : syracuseStep 2287907 = 3431861) B3431861
theorem B5794253 : Blo 1016603 5794253 := bstep (se 3 (by rfl) ⟨1086422, by rfl⟩ : syracuseStep 5794253 = 2172845) B2172845
theorem B3434993 : Blo 1016603 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B4352525 : Blo 1016603 4352525 := bstep (se 3 (by rfl) ⟨816098, by rfl⟩ : syracuseStep 4352525 = 1632197) B1632197
theorem B2943523 : Blo 1016603 2943523 := bstep (se 1 (by rfl) ⟨2207642, by rfl⟩ : syracuseStep 2943523 = 4415285) B4415285
theorem B2288177 : Blo 1016603 2288177 := bstep (se 2 (by rfl) ⟨858066, by rfl⟩ : syracuseStep 2288177 = 1716133) B1716133
theorem B2288195 : Blo 1016603 2288195 := bstep (se 1 (by rfl) ⟨1716146, by rfl⟩ : syracuseStep 2288195 = 3432293) B3432293
theorem B16509581 : Blo 1016603 16509581 := bstep (se 3 (by rfl) ⟨3095546, by rfl⟩ : syracuseStep 16509581 = 6191093) B6191093
theorem B7727885 : Blo 1016603 7727885 := bstep (se 3 (by rfl) ⟨1448978, by rfl⟩ : syracuseStep 7727885 = 2897957) B2897957
theorem B2288465 : Blo 1016603 2288465 := bstep (se 2 (by rfl) ⟨858174, by rfl⟩ : syracuseStep 2288465 = 1716349) B1716349
theorem B2288483 : Blo 1016603 2288483 := bstep (se 1 (by rfl) ⟨1716362, by rfl⟩ : syracuseStep 2288483 = 3432725) B3432725
theorem B1633139 : Blo 1016603 1633139 := bstep (se 1 (by rfl) ⟨1224854, by rfl⟩ : syracuseStep 1633139 = 2449709) B2449709
theorem B3435533 : Blo 1016603 3435533 := bstep (se 3 (by rfl) ⟨644162, by rfl⟩ : syracuseStep 3435533 = 1288325) B1288325
theorem B1567793 : Blo 1016603 1567793 := bstep (se 2 (by rfl) ⟨587922, by rfl⟩ : syracuseStep 1567793 = 1175845) B1175845
theorem B1633331 : Blo 1016603 1633331 := bstep (se 1 (by rfl) ⟨1224998, by rfl⟩ : syracuseStep 1633331 = 2449997) B2449997
theorem B12414005 : Blo 1016603 12414005 := bstep (se 5 (by rfl) ⟨581906, by rfl⟩ : syracuseStep 12414005 = 1163813) B1163813
theorem B3435587 : Blo 1016603 3435587 := bstep (se 1 (by rfl) ⟨2576690, by rfl⟩ : syracuseStep 3435587 = 5153381) B5153381
theorem B2288753 : Blo 1016603 2288753 := bstep (se 2 (by rfl) ⟨858282, by rfl⟩ : syracuseStep 2288753 = 1716565) B1716565
theorem B2288771 : Blo 1016603 2288771 := bstep (se 1 (by rfl) ⟨1716578, by rfl⟩ : syracuseStep 2288771 = 3433157) B3433157
theorem B4648099 : Blo 1016603 4648099 := bstep (se 1 (by rfl) ⟨3486074, by rfl⟩ : syracuseStep 4648099 = 6972149) B6972149
theorem B1633459 : Blo 1016603 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B3435857 : Blo 1016603 3435857 := bstep (se 2 (by rfl) ⟨1288446, by rfl⟩ : syracuseStep 3435857 = 2576893) B2576893
theorem B5795185 : Blo 1016603 5795185 := bstep (se 2 (by rfl) ⟨2173194, by rfl⟩ : syracuseStep 5795185 = 4346389) B4346389
theorem B2289041 : Blo 1016603 2289041 := bstep (se 2 (by rfl) ⟨858390, by rfl⟩ : syracuseStep 2289041 = 1716781) B1716781
theorem B2289059 : Blo 1016603 2289059 := bstep (se 1 (by rfl) ⟨1716794, by rfl⟩ : syracuseStep 2289059 = 3433589) B3433589
theorem B2289329 : Blo 1016603 2289329 := bstep (se 2 (by rfl) ⟨858498, by rfl⟩ : syracuseStep 2289329 = 1716997) B1716997
theorem B2289347 : Blo 1016603 2289347 := bstep (se 1 (by rfl) ⟨1717010, by rfl⟩ : syracuseStep 2289347 = 3434021) B3434021
theorem B17395397 : Blo 1016603 17395397 := bstep (se 4 (by rfl) ⟨1630818, by rfl⟩ : syracuseStep 17395397 = 3261637) B3261637
theorem B1634099 : Blo 1016603 1634099 := bstep (se 1 (by rfl) ⟨1225574, by rfl⟩ : syracuseStep 1634099 = 2451149) B2451149
theorem B3862349 : Blo 1016603 3862349 := bstep (se 3 (by rfl) ⟨724190, by rfl⟩ : syracuseStep 3862349 = 1448381) B1448381
theorem B3436397 : Blo 1016603 3436397 := bstep (se 3 (by rfl) ⟨644324, by rfl⟩ : syracuseStep 3436397 = 1288649) B1288649
theorem B1634177 : Blo 1016603 1634177 := bstep (se 2 (by rfl) ⟨612816, by rfl⟩ : syracuseStep 1634177 = 1225633) B1225633
theorem B3436451 : Blo 1016603 3436451 := bstep (se 1 (by rfl) ⟨2577338, by rfl⟩ : syracuseStep 3436451 = 5154677) B5154677
theorem B2289617 : Blo 1016603 2289617 := bstep (se 2 (by rfl) ⟨858606, by rfl⟩ : syracuseStep 2289617 = 1717213) B1717213
theorem B2289635 : Blo 1016603 2289635 := bstep (se 1 (by rfl) ⟨1717226, by rfl⟩ : syracuseStep 2289635 = 3434453) B3434453
theorem B3436721 : Blo 1016603 3436721 := bstep (se 2 (by rfl) ⟨1288770, by rfl⟩ : syracuseStep 3436721 = 2577541) B2577541
theorem B2289905 : Blo 1016603 2289905 := bstep (se 2 (by rfl) ⟨858714, by rfl⟩ : syracuseStep 2289905 = 1717429) B1717429
theorem B1634561 : Blo 1016603 1634561 := bstep (se 2 (by rfl) ⟨612960, by rfl⟩ : syracuseStep 1634561 = 1225921) B1225921
theorem B2289923 : Blo 1016603 2289923 := bstep (se 1 (by rfl) ⟨1717442, by rfl⟩ : syracuseStep 2289923 = 3434885) B3434885
theorem B8712461 : Blo 1016603 8712461 := bstep (se 3 (by rfl) ⟨1633586, by rfl⟩ : syracuseStep 8712461 = 3267173) B3267173
theorem B2617699 : Blo 1016603 2617699 := bstep (se 1 (by rfl) ⟨1963274, by rfl⟩ : syracuseStep 2617699 = 3926549) B3926549
theorem B1634689 : Blo 1016603 1634689 := bstep (se 2 (by rfl) ⟨613008, by rfl⟩ : syracuseStep 1634689 = 1226017) B1226017
theorem B2290193 : Blo 1016603 2290193 := bstep (se 2 (by rfl) ⟨858822, by rfl⟩ : syracuseStep 2290193 = 1717645) B1717645
theorem B2290211 : Blo 1016603 2290211 := bstep (se 1 (by rfl) ⟨1717658, by rfl⟩ : syracuseStep 2290211 = 3435317) B3435317
theorem B3863153 : Blo 1016603 3863153 := bstep (se 2 (by rfl) ⟨1448682, by rfl⟩ : syracuseStep 3863153 = 2897365) B2897365
theorem B2683523 : Blo 1016603 2683523 := bstep (se 1 (by rfl) ⟨2012642, by rfl⟩ : syracuseStep 2683523 = 4025285) B4025285
theorem B6517381 : Blo 1016603 6517381 := bstep (se 4 (by rfl) ⟨611004, by rfl⟩ : syracuseStep 6517381 = 1222009) B1222009
theorem B1962641 : Blo 1016603 1962641 := bstep (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) B1471981
theorem B3437261 : Blo 1016603 3437261 := bstep (se 3 (by rfl) ⟨644486, by rfl⟩ : syracuseStep 3437261 = 1288973) B1288973
theorem B6976205 : Blo 1016603 6976205 := bstep (se 3 (by rfl) ⟨1308038, by rfl⟩ : syracuseStep 6976205 = 2616077) B2616077
theorem B3437315 : Blo 1016603 3437315 := bstep (se 1 (by rfl) ⟨2577986, by rfl⟩ : syracuseStep 3437315 = 5155973) B5155973
theorem B5796643 : Blo 1016603 5796643 := bstep (se 1 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 5796643 = 8694965) B8694965
theorem B2290481 : Blo 1016603 2290481 := bstep (se 2 (by rfl) ⟨858930, by rfl⟩ : syracuseStep 2290481 = 1717861) B1717861
theorem B1307443 : Blo 1016603 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B2290499 : Blo 1016603 2290499 := bstep (se 1 (by rfl) ⟨1717874, by rfl⟩ : syracuseStep 2290499 = 3435749) B3435749
theorem B2356049 : Blo 1016603 2356049 := bstep (se 2 (by rfl) ⟨883518, by rfl⟩ : syracuseStep 2356049 = 1767037) B1767037
theorem B7336817 : Blo 1016603 7336817 := bstep (se 2 (by rfl) ⟨2751306, by rfl⟩ : syracuseStep 7336817 = 5502613) B5502613
theorem B1143715 : Blo 1016603 1143715 := bstep (se 1 (by rfl) ⟨857786, by rfl⟩ : syracuseStep 1143715 = 1715573) B1715573
theorem B1930225 : Blo 1016603 1930225 := bstep (se 2 (by rfl) ⟨723834, by rfl⟩ : syracuseStep 1930225 = 1447669) B1447669
theorem B3437585 : Blo 1016603 3437585 := bstep (se 2 (by rfl) ⟨1289094, by rfl⟩ : syracuseStep 3437585 = 2578189) B2578189
theorem B1143859 : Blo 1016603 1143859 := bstep (se 1 (by rfl) ⟨857894, by rfl⟩ : syracuseStep 1143859 = 1715789) B1715789
theorem B2061379 : Blo 1016603 2061379 := bstep (se 1 (by rfl) ⟨1546034, by rfl⟩ : syracuseStep 2061379 = 3092069) B3092069
theorem B2290769 : Blo 1016603 2290769 := bstep (se 2 (by rfl) ⟨859038, by rfl⟩ : syracuseStep 2290769 = 1718077) B1718077
theorem B2290787 : Blo 1016603 2290787 := bstep (se 1 (by rfl) ⟨1718090, by rfl⟩ : syracuseStep 2290787 = 3436181) B3436181
theorem B1930385 : Blo 1016603 1930385 := bstep (se 2 (by rfl) ⟨723894, by rfl⟩ : syracuseStep 1930385 = 1447789) B1447789
theorem B1144003 : Blo 1016603 1144003 := bstep (se 1 (by rfl) ⟨858002, by rfl⟩ : syracuseStep 1144003 = 1716005) B1716005
theorem B6288581 : Blo 1016603 6288581 := bstep (se 4 (by rfl) ⟨589554, by rfl⟩ : syracuseStep 6288581 = 1179109) B1179109
theorem B3863821 : Blo 1016603 3863821 := bstep (se 3 (by rfl) ⟨724466, by rfl⟩ : syracuseStep 3863821 = 1448933) B1448933
theorem B5797169 : Blo 1016603 5797169 := bstep (se 2 (by rfl) ⟨2173938, by rfl⟩ : syracuseStep 5797169 = 4347877) B4347877
theorem B1144147 : Blo 1016603 1144147 := bstep (se 1 (by rfl) ⟨858110, by rfl⟩ : syracuseStep 1144147 = 1716221) B1716221
theorem B2291057 : Blo 1016603 2291057 := bstep (se 2 (by rfl) ⟨859146, by rfl⟩ : syracuseStep 2291057 = 1718293) B1718293
theorem B2291075 : Blo 1016603 2291075 := bstep (se 1 (by rfl) ⟨1718306, by rfl⟩ : syracuseStep 2291075 = 3436613) B3436613
theorem B1144291 : Blo 1016603 1144291 := bstep (se 1 (by rfl) ⟨858218, by rfl⟩ : syracuseStep 1144291 = 1716437) B1716437
theorem B1930787 : Blo 1016603 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B3438125 : Blo 1016603 3438125 := bstep (se 3 (by rfl) ⟨644648, by rfl⟩ : syracuseStep 3438125 = 1289297) B1289297
theorem B3438179 : Blo 1016603 3438179 := bstep (se 1 (by rfl) ⟨2578634, by rfl⟩ : syracuseStep 3438179 = 5157269) B5157269
theorem B7730801 : Blo 1016603 7730801 := bstep (se 2 (by rfl) ⟨2899050, by rfl⟩ : syracuseStep 7730801 = 5798101) B5798101
theorem B1144435 : Blo 1016603 1144435 := bstep (se 1 (by rfl) ⟨858326, by rfl⟩ : syracuseStep 1144435 = 1716653) B1716653
theorem B20936333 : Blo 1016603 20936333 := bstep (se 3 (by rfl) ⟨3925562, by rfl⟩ : syracuseStep 20936333 = 7851125) B7851125
theorem B2291345 : Blo 1016603 2291345 := bstep (se 2 (by rfl) ⟨859254, by rfl⟩ : syracuseStep 2291345 = 1718509) B1718509
theorem B2291363 : Blo 1016603 2291363 := bstep (se 1 (by rfl) ⟨1718522, by rfl⟩ : syracuseStep 2291363 = 3437045) B3437045
theorem B1144579 : Blo 1016603 1144579 := bstep (se 1 (by rfl) ⟨858434, by rfl⟩ : syracuseStep 1144579 = 1716869) B1716869
theorem B2324305 : Blo 1016603 2324305 := bstep (se 2 (by rfl) ⟨871614, by rfl⟩ : syracuseStep 2324305 = 1743229) B1743229
theorem B3438449 : Blo 1016603 3438449 := bstep (se 2 (by rfl) ⟨1289418, by rfl⟩ : syracuseStep 3438449 = 2578837) B2578837
theorem B1144723 : Blo 1016603 1144723 := bstep (se 1 (by rfl) ⟨858542, by rfl⟩ : syracuseStep 1144723 = 1717085) B1717085
theorem B2291633 : Blo 1016603 2291633 := bstep (se 2 (by rfl) ⟨859362, by rfl⟩ : syracuseStep 2291633 = 1718725) B1718725
theorem B2291651 : Blo 1016603 2291651 := bstep (se 1 (by rfl) ⟨1718738, by rfl⟩ : syracuseStep 2291651 = 3437477) B3437477
theorem B1144867 : Blo 1016603 1144867 := bstep (se 1 (by rfl) ⟨858650, by rfl⟩ : syracuseStep 1144867 = 1717301) B1717301
theorem B3864611 : Blo 1016603 3864611 := bstep (se 1 (by rfl) ⟨2898458, by rfl⟩ : syracuseStep 3864611 = 5796917) B5796917
theorem B7338053 : Blo 1016603 7338053 := bstep (se 4 (by rfl) ⟨687942, by rfl⟩ : syracuseStep 7338053 = 1375885) B1375885
theorem B2062417 : Blo 1016603 2062417 := bstep (se 2 (by rfl) ⟨773406, by rfl⟩ : syracuseStep 2062417 = 1546813) B1546813
theorem B2324579 : Blo 1016603 2324579 := bstep (se 1 (by rfl) ⟨1743434, by rfl⟩ : syracuseStep 2324579 = 3486869) B3486869
theorem B1145011 : Blo 1016603 1145011 := bstep (se 1 (by rfl) ⟨858758, by rfl⟩ : syracuseStep 1145011 = 1717517) B1717517
theorem B2291921 : Blo 1016603 2291921 := bstep (se 2 (by rfl) ⟨859470, by rfl⟩ : syracuseStep 2291921 = 1718941) B1718941
theorem B59504867 : Blo 1016603 59504867 := bstep (se 1 (by rfl) ⟨44628650, by rfl⟩ : syracuseStep 59504867 = 89257301) B89257301
theorem B2291939 : Blo 1016603 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B1145155 : Blo 1016603 1145155 := bstep (se 1 (by rfl) ⟨858866, by rfl⟩ : syracuseStep 1145155 = 1717733) B1717733
theorem B3438989 : Blo 1016603 3438989 := bstep (se 3 (by rfl) ⟨644810, by rfl⟩ : syracuseStep 3438989 = 1289621) B1289621
theorem B1931683 : Blo 1016603 1931683 := bstep (se 1 (by rfl) ⟨1448762, by rfl⟩ : syracuseStep 1931683 = 2897525) B2897525
theorem B3439043 : Blo 1016603 3439043 := bstep (se 1 (by rfl) ⟨2579282, by rfl⟩ : syracuseStep 3439043 = 5158565) B5158565
theorem B1145299 : Blo 1016603 1145299 := bstep (se 1 (by rfl) ⟨858974, by rfl⟩ : syracuseStep 1145299 = 1717949) B1717949
theorem B2292209 : Blo 1016603 2292209 := bstep (se 2 (by rfl) ⟨859578, by rfl⟩ : syracuseStep 2292209 = 1719157) B1719157
theorem B2292227 : Blo 1016603 2292227 := bstep (se 1 (by rfl) ⟨1719170, by rfl⟩ : syracuseStep 2292227 = 3438341) B3438341
theorem B2095651 : Blo 1016603 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B11598389 : Blo 1016603 11598389 := bstep (se 5 (by rfl) ⟨543674, by rfl⟩ : syracuseStep 11598389 = 1087349) B1087349
theorem B1931843 : Blo 1016603 1931843 := bstep (se 1 (by rfl) ⟨1448882, by rfl⟩ : syracuseStep 1931843 = 2897765) B2897765
theorem B1145443 : Blo 1016603 1145443 := bstep (se 1 (by rfl) ⟨859082, by rfl⟩ : syracuseStep 1145443 = 1718165) B1718165
theorem B9435761 : Blo 1016603 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B3865265 : Blo 1016603 3865265 := bstep (se 2 (by rfl) ⟨1449474, by rfl⟩ : syracuseStep 3865265 = 2898949) B2898949
theorem B3439313 : Blo 1016603 3439313 := bstep (se 2 (by rfl) ⟨1289742, by rfl⟩ : syracuseStep 3439313 = 2579485) B2579485
theorem B5798627 : Blo 1016603 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B1145587 : Blo 1016603 1145587 := bstep (se 1 (by rfl) ⟨859190, by rfl⟩ : syracuseStep 1145587 = 1718381) B1718381
theorem B2292497 : Blo 1016603 2292497 := bstep (se 2 (by rfl) ⟨859686, by rfl⟩ : syracuseStep 2292497 = 1719373) B1719373
theorem B2292515 : Blo 1016603 2292515 := bstep (se 1 (by rfl) ⟨1719386, by rfl⟩ : syracuseStep 2292515 = 3438773) B3438773
theorem B4356899 : Blo 1016603 4356899 := bstep (se 1 (by rfl) ⟨3267674, by rfl⟩ : syracuseStep 4356899 = 6535349) B6535349
theorem B1145731 : Blo 1016603 1145731 := bstep (se 1 (by rfl) ⟨859298, by rfl⟩ : syracuseStep 1145731 = 1718597) B1718597
theorem B1145875 : Blo 1016603 1145875 := bstep (se 1 (by rfl) ⟨859406, by rfl⟩ : syracuseStep 1145875 = 1718813) B1718813
theorem B2292785 : Blo 1016603 2292785 := bstep (se 2 (by rfl) ⟨859794, by rfl⟩ : syracuseStep 2292785 = 1719589) B1719589
theorem B2292803 : Blo 1016603 2292803 := bstep (se 1 (by rfl) ⟨1719602, by rfl⟩ : syracuseStep 2292803 = 3439205) B3439205
theorem B2751565 : Blo 1016603 2751565 := bstep (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) B1031837
theorem B1146019 : Blo 1016603 1146019 := bstep (se 1 (by rfl) ⟨859514, by rfl⟩ : syracuseStep 1146019 = 1719029) B1719029
theorem B2751661 : Blo 1016603 2751661 := bstep (se 3 (by rfl) ⟨515936, by rfl⟩ : syracuseStep 2751661 = 1031873) B1031873
theorem B3439853 : Blo 1016603 3439853 := bstep (se 3 (by rfl) ⟨644972, by rfl⟩ : syracuseStep 3439853 = 1289945) B1289945
theorem B3439907 : Blo 1016603 3439907 := bstep (se 1 (by rfl) ⟨2579930, by rfl⟩ : syracuseStep 3439907 = 5159861) B5159861
theorem B5307697 : Blo 1016603 5307697 := bstep (se 2 (by rfl) ⟨1990386, by rfl⟩ : syracuseStep 5307697 = 3980773) B3980773
theorem B1146163 : Blo 1016603 1146163 := bstep (se 1 (by rfl) ⟨859622, by rfl⟩ : syracuseStep 1146163 = 1719245) B1719245
theorem B3439949 : Blo 1016603 3439949 := bstep (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) B1289981
theorem B2293073 : Blo 1016603 2293073 := bstep (se 2 (by rfl) ⟨859902, by rfl⟩ : syracuseStep 2293073 = 1719805) B1719805
theorem B2293091 : Blo 1016603 2293091 := bstep (se 1 (by rfl) ⟨1719818, by rfl⟩ : syracuseStep 2293091 = 3439637) B3439637
theorem B1146307 : Blo 1016603 1146307 := bstep (se 1 (by rfl) ⟨859730, by rfl⟩ : syracuseStep 1146307 = 1719461) B1719461
theorem B3440177 : Blo 1016603 3440177 := bstep (se 2 (by rfl) ⟨1290066, by rfl⟩ : syracuseStep 3440177 = 2580133) B2580133
theorem B1146451 : Blo 1016603 1146451 := bstep (se 1 (by rfl) ⟨859838, by rfl⟩ : syracuseStep 1146451 = 1719677) B1719677
theorem B1932913 : Blo 1016603 1932913 := bstep (se 2 (by rfl) ⟨724842, by rfl⟩ : syracuseStep 1932913 = 1449685) B1449685
theorem B2293361 : Blo 1016603 2293361 := bstep (se 2 (by rfl) ⟨860010, by rfl⟩ : syracuseStep 2293361 = 1720021) B1720021
theorem B2293379 : Blo 1016603 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B32997091 : Blo 1016603 32997091 := bstep (se 1 (by rfl) ⟨24747818, by rfl⟩ : syracuseStep 32997091 = 49495637) B49495637
theorem B1146595 : Blo 1016603 1146595 := bstep (se 1 (by rfl) ⟨859946, by rfl⟩ : syracuseStep 1146595 = 1719893) B1719893
theorem B1834787 : Blo 1016603 1834787 := bstep (se 1 (by rfl) ⟨1376090, by rfl⟩ : syracuseStep 1834787 = 2752181) B2752181
theorem B1146739 : Blo 1016603 1146739 := bstep (se 1 (by rfl) ⟨860054, by rfl⟩ : syracuseStep 1146739 = 1720109) B1720109
theorem B2293649 : Blo 1016603 2293649 := bstep (se 2 (by rfl) ⟨860118, by rfl⟩ : syracuseStep 2293649 = 1720237) B1720237
theorem B2293667 : Blo 1016603 2293667 := bstep (se 1 (by rfl) ⟨1720250, by rfl⟩ : syracuseStep 2293667 = 3440501) B3440501
theorem B2064323 : Blo 1016603 2064323 := bstep (se 1 (by rfl) ⟨1548242, by rfl⟩ : syracuseStep 2064323 = 3096485) B3096485
theorem B2064395 : Blo 1016603 2064395 := bstep (se 1 (by rfl) ⟨1548296, by rfl⟩ : syracuseStep 2064395 = 3096593) B3096593
theorem B1572875 : Blo 1016603 1572875 := bstep (se 1 (by rfl) ⟨1179656, by rfl⟩ : syracuseStep 1572875 = 2359313) B2359313
theorem B3440663 : Blo 1016603 3440663 := bstep (se 1 (by rfl) ⟨2580497, by rfl⟩ : syracuseStep 3440663 = 5160995) B5160995
theorem B2293811 : Blo 1016603 2293811 := bstep (se 1 (by rfl) ⟨1720358, by rfl⟩ : syracuseStep 2293811 = 3440717) B3440717
theorem B1146955 : Blo 1016603 1146955 := bstep (se 1 (by rfl) ⟨860216, by rfl⟩ : syracuseStep 1146955 = 1720433) B1720433
theorem B1933399 : Blo 1016603 1933399 := bstep (se 1 (by rfl) ⟨1450049, by rfl⟩ : syracuseStep 1933399 = 2900099) B2900099
theorem B2293847 : Blo 1016603 2293847 := bstep (se 1 (by rfl) ⟨1720385, by rfl⟩ : syracuseStep 2293847 = 3440771) B3440771
theorem B1147063 : Blo 1016603 1147063 := bstep (se 1 (by rfl) ⟨860297, by rfl⟩ : syracuseStep 1147063 = 1720595) B1720595
theorem B23527685 : Blo 1016603 23527685 := bstep (se 4 (by rfl) ⟨2205720, by rfl⟩ : syracuseStep 23527685 = 4411441) B4411441
theorem B2294027 : Blo 1016603 2294027 := bstep (se 1 (by rfl) ⟨1720520, by rfl⟩ : syracuseStep 2294027 = 3441041) B3441041
theorem B27885869 : Blo 1016603 27885869 := bstep (se 3 (by rfl) ⟨5228600, by rfl⟩ : syracuseStep 27885869 = 10457201) B10457201
theorem B2294081 : Blo 1016603 2294081 := bstep (se 2 (by rfl) ⟨860280, by rfl⟩ : syracuseStep 2294081 = 1720561) B1720561
theorem B1147243 : Blo 1016603 1147243 := bstep (se 1 (by rfl) ⟨860432, by rfl⟩ : syracuseStep 1147243 = 1720865) B1720865
theorem B3867011 : Blo 1016603 3867011 := bstep (se 1 (by rfl) ⟨2900258, by rfl⟩ : syracuseStep 3867011 = 5800517) B5800517
theorem B1147351 : Blo 1016603 1147351 := bstep (se 1 (by rfl) ⟨860513, by rfl⟩ : syracuseStep 1147351 = 1721027) B1721027
theorem B13238801 : Blo 1016603 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B2294297 : Blo 1016603 2294297 := bstep (se 2 (by rfl) ⟨860361, by rfl⟩ : syracuseStep 2294297 = 1720723) B1720723
theorem B8716835 : Blo 1016603 8716835 := bstep (se 1 (by rfl) ⟨6537626, by rfl⟩ : syracuseStep 8716835 = 13075253) B13075253
theorem B3441203 : Blo 1016603 3441203 := bstep (se 1 (by rfl) ⟨2580902, by rfl⟩ : syracuseStep 3441203 = 5161805) B5161805
theorem B16515677 : Blo 1016603 16515677 := bstep (se 3 (by rfl) ⟨3096689, by rfl⟩ : syracuseStep 16515677 = 6193379) B6193379
theorem B2294387 : Blo 1016603 2294387 := bstep (se 1 (by rfl) ⟨1720790, by rfl⟩ : syracuseStep 2294387 = 3441581) B3441581
theorem B7537283 : Blo 1016603 7537283 := bstep (se 1 (by rfl) ⟨5652962, by rfl⟩ : syracuseStep 7537283 = 11305925) B11305925
theorem B1147531 : Blo 1016603 1147531 := bstep (se 1 (by rfl) ⟨860648, by rfl⟩ : syracuseStep 1147531 = 1721297) B1721297
theorem B2294423 : Blo 1016603 2294423 := bstep (se 1 (by rfl) ⟨1720817, by rfl⟩ : syracuseStep 2294423 = 3441635) B3441635
theorem B1147639 : Blo 1016603 1147639 := bstep (se 1 (by rfl) ⟨860729, by rfl⟩ : syracuseStep 1147639 = 1721459) B1721459
theorem B1016619 : Blo 1016603 1016619 := bstep (se 1 (by rfl) ⟨762464, by rfl⟩ : syracuseStep 1016619 = 1524929) B1524929
theorem B3670829 : Blo 1016603 3670829 := bstep (se 3 (by rfl) ⟨688280, by rfl⟩ : syracuseStep 3670829 = 1376561) B1376561
theorem B1016631 : Blo 1016603 1016631 := bstep (se 1 (by rfl) ⟨762473, by rfl⟩ : syracuseStep 1016631 = 1524947) B1524947
theorem B3441473 : Blo 1016603 3441473 := bstep (se 2 (by rfl) ⟨1290552, by rfl⟩ : syracuseStep 3441473 = 2581105) B2581105
theorem B1016651 : Blo 1016603 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B2294603 : Blo 1016603 2294603 := bstep (se 1 (by rfl) ⟨1720952, by rfl⟩ : syracuseStep 2294603 = 3441905) B3441905
theorem B1016663 : Blo 1016603 1016663 := bstep (se 1 (by rfl) ⟨762497, by rfl⟩ : syracuseStep 1016663 = 1524995) B1524995
theorem B1016683 : Blo 1016603 1016683 := bstep (se 1 (by rfl) ⟨762512, by rfl⟩ : syracuseStep 1016683 = 1525025) B1525025
theorem B1016695 : Blo 1016603 1016695 := bstep (se 1 (by rfl) ⟨762521, by rfl⟩ : syracuseStep 1016695 = 1525043) B1525043
theorem B2294657 : Blo 1016603 2294657 := bstep (se 2 (by rfl) ⟨860496, by rfl⟩ : syracuseStep 2294657 = 1720993) B1720993
theorem B5800835 : Blo 1016603 5800835 := bstep (se 1 (by rfl) ⟨4350626, by rfl⟩ : syracuseStep 5800835 = 8701253) B8701253
theorem B1016715 : Blo 1016603 1016715 := bstep (se 1 (by rfl) ⟨762536, by rfl⟩ : syracuseStep 1016715 = 1525073) B1525073
theorem B1934219 : Blo 1016603 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B1016727 : Blo 1016603 1016727 := bstep (se 1 (by rfl) ⟨762545, by rfl⟩ : syracuseStep 1016727 = 1525091) B1525091
theorem B1016747 : Blo 1016603 1016747 := bstep (se 1 (by rfl) ⟨762560, by rfl⟩ : syracuseStep 1016747 = 1525121) B1525121
theorem B1147819 : Blo 1016603 1147819 := bstep (se 1 (by rfl) ⟨860864, by rfl⟩ : syracuseStep 1147819 = 1721729) B1721729
theorem B3670957 : Blo 1016603 3670957 := bstep (se 3 (by rfl) ⟨688304, by rfl⟩ : syracuseStep 3670957 = 1376609) B1376609
theorem B1016759 : Blo 1016603 1016759 := bstep (se 1 (by rfl) ⟨762569, by rfl⟩ : syracuseStep 1016759 = 1525139) B1525139
theorem B1934273 : Blo 1016603 1934273 := bstep (se 2 (by rfl) ⟨725352, by rfl⟩ : syracuseStep 1934273 = 1450705) B1450705
theorem B1016779 : Blo 1016603 1016779 := bstep (se 1 (by rfl) ⟨762584, by rfl⟩ : syracuseStep 1016779 = 1525169) B1525169
theorem B1016791 : Blo 1016603 1016791 := bstep (se 1 (by rfl) ⟨762593, by rfl⟩ : syracuseStep 1016791 = 1525187) B1525187
theorem B1016811 : Blo 1016603 1016811 := bstep (se 1 (by rfl) ⟨762608, by rfl⟩ : syracuseStep 1016811 = 1525217) B1525217
theorem B1016823 : Blo 1016603 1016823 := bstep (se 1 (by rfl) ⟨762617, by rfl⟩ : syracuseStep 1016823 = 1525235) B1525235
theorem B1016843 : Blo 1016603 1016843 := bstep (se 1 (by rfl) ⟨762632, by rfl⟩ : syracuseStep 1016843 = 1525265) B1525265
theorem B1016855 : Blo 1016603 1016855 := bstep (se 1 (by rfl) ⟨762641, by rfl⟩ : syracuseStep 1016855 = 1525283) B1525283
theorem B1147927 : Blo 1016603 1147927 := bstep (se 1 (by rfl) ⟨860945, by rfl⟩ : syracuseStep 1147927 = 1721891) B1721891
theorem B1016875 : Blo 1016603 1016875 := bstep (se 1 (by rfl) ⟨762656, by rfl⟩ : syracuseStep 1016875 = 1525313) B1525313
theorem B1016887 : Blo 1016603 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B1016907 : Blo 1016603 1016907 := bstep (se 1 (by rfl) ⟨762680, by rfl⟩ : syracuseStep 1016907 = 1525361) B1525361
theorem B1016919 : Blo 1016603 1016919 := bstep (se 1 (by rfl) ⟨762689, by rfl⟩ : syracuseStep 1016919 = 1525379) B1525379
theorem B2294873 : Blo 1016603 2294873 := bstep (se 2 (by rfl) ⟨860577, by rfl⟩ : syracuseStep 2294873 = 1721155) B1721155
theorem B1016939 : Blo 1016603 1016939 := bstep (se 1 (by rfl) ⟨762704, by rfl⟩ : syracuseStep 1016939 = 1525409) B1525409
theorem B1016951 : Blo 1016603 1016951 := bstep (se 1 (by rfl) ⟨762713, by rfl⟩ : syracuseStep 1016951 = 1525427) B1525427
theorem B1016971 : Blo 1016603 1016971 := bstep (se 1 (by rfl) ⟨762728, by rfl⟩ : syracuseStep 1016971 = 1525457) B1525457
theorem B1016983 : Blo 1016603 1016983 := bstep (se 1 (by rfl) ⟨762737, by rfl⟩ : syracuseStep 1016983 = 1525475) B1525475
theorem B1017003 : Blo 1016603 1017003 := bstep (se 1 (by rfl) ⟨762752, by rfl⟩ : syracuseStep 1017003 = 1525505) B1525505
theorem B2294963 : Blo 1016603 2294963 := bstep (se 1 (by rfl) ⟨1721222, by rfl⟩ : syracuseStep 2294963 = 3442445) B3442445
theorem B1017015 : Blo 1016603 1017015 := bstep (se 1 (by rfl) ⟨762761, by rfl⟩ : syracuseStep 1017015 = 1525523) B1525523
theorem B1017035 : Blo 1016603 1017035 := bstep (se 1 (by rfl) ⟨762776, by rfl⟩ : syracuseStep 1017035 = 1525553) B1525553
theorem B1148107 : Blo 1016603 1148107 := bstep (se 1 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 1148107 = 1722161) B1722161
theorem B1017047 : Blo 1016603 1017047 := bstep (se 1 (by rfl) ⟨762785, by rfl⟩ : syracuseStep 1017047 = 1525571) B1525571
theorem B2294999 : Blo 1016603 2294999 := bstep (se 1 (by rfl) ⟨1721249, by rfl⟩ : syracuseStep 2294999 = 3442499) B3442499
theorem B1017067 : Blo 1016603 1017067 := bstep (se 1 (by rfl) ⟨762800, by rfl⟩ : syracuseStep 1017067 = 1525601) B1525601
theorem B1017079 : Blo 1016603 1017079 := bstep (se 1 (by rfl) ⟨762809, by rfl⟩ : syracuseStep 1017079 = 1525619) B1525619
theorem B1017099 : Blo 1016603 1017099 := bstep (se 1 (by rfl) ⟨762824, by rfl⟩ : syracuseStep 1017099 = 1525649) B1525649
theorem B1017111 : Blo 1016603 1017111 := bstep (se 1 (by rfl) ⟨762833, by rfl⟩ : syracuseStep 1017111 = 1525667) B1525667
theorem B1017131 : Blo 1016603 1017131 := bstep (se 1 (by rfl) ⟨762848, by rfl⟩ : syracuseStep 1017131 = 1525697) B1525697
theorem B1017143 : Blo 1016603 1017143 := bstep (se 1 (by rfl) ⟨762857, by rfl⟩ : syracuseStep 1017143 = 1525715) B1525715
theorem B1017163 : Blo 1016603 1017163 := bstep (se 1 (by rfl) ⟨762872, by rfl⟩ : syracuseStep 1017163 = 1525745) B1525745
theorem B5801291 : Blo 1016603 5801291 := bstep (se 1 (by rfl) ⟨4350968, by rfl⟩ : syracuseStep 5801291 = 8701937) B8701937
theorem B1017175 : Blo 1016603 1017175 := bstep (se 1 (by rfl) ⟨762881, by rfl⟩ : syracuseStep 1017175 = 1525763) B1525763
theorem B3442013 : Blo 1016603 3442013 := bstep (se 3 (by rfl) ⟨645377, by rfl⟩ : syracuseStep 3442013 = 1290755) B1290755
theorem B1017195 : Blo 1016603 1017195 := bstep (se 1 (by rfl) ⟨762896, by rfl⟩ : syracuseStep 1017195 = 1525793) B1525793
theorem B1017207 : Blo 1016603 1017207 := bstep (se 1 (by rfl) ⟨762905, by rfl⟩ : syracuseStep 1017207 = 1525811) B1525811
theorem B1017227 : Blo 1016603 1017227 := bstep (se 1 (by rfl) ⟨762920, by rfl⟩ : syracuseStep 1017227 = 1525841) B1525841
theorem B2295179 : Blo 1016603 2295179 := bstep (se 1 (by rfl) ⟨1721384, by rfl⟩ : syracuseStep 2295179 = 3442769) B3442769
theorem B1017239 : Blo 1016603 1017239 := bstep (se 1 (by rfl) ⟨762929, by rfl⟩ : syracuseStep 1017239 = 1525859) B1525859
theorem B1017259 : Blo 1016603 1017259 := bstep (se 1 (by rfl) ⟨762944, by rfl⟩ : syracuseStep 1017259 = 1525889) B1525889
theorem B1017271 : Blo 1016603 1017271 := bstep (se 1 (by rfl) ⟨762953, by rfl⟩ : syracuseStep 1017271 = 1525907) B1525907
theorem B2295233 : Blo 1016603 2295233 := bstep (se 2 (by rfl) ⟨860712, by rfl⟩ : syracuseStep 2295233 = 1721425) B1721425
theorem B1017291 : Blo 1016603 1017291 := bstep (se 1 (by rfl) ⟨762968, by rfl⟩ : syracuseStep 1017291 = 1525937) B1525937
theorem B1017303 : Blo 1016603 1017303 := bstep (se 1 (by rfl) ⟨762977, by rfl⟩ : syracuseStep 1017303 = 1525955) B1525955
theorem B1017323 : Blo 1016603 1017323 := bstep (se 1 (by rfl) ⟨762992, by rfl⟩ : syracuseStep 1017323 = 1525985) B1525985
theorem B1017335 : Blo 1016603 1017335 := bstep (se 1 (by rfl) ⟨763001, by rfl⟩ : syracuseStep 1017335 = 1526003) B1526003
theorem B1017355 : Blo 1016603 1017355 := bstep (se 1 (by rfl) ⟨763016, by rfl⟩ : syracuseStep 1017355 = 1526033) B1526033
theorem B1017367 : Blo 1016603 1017367 := bstep (se 1 (by rfl) ⟨763025, by rfl⟩ : syracuseStep 1017367 = 1526051) B1526051
theorem B1017387 : Blo 1016603 1017387 := bstep (se 1 (by rfl) ⟨763040, by rfl⟩ : syracuseStep 1017387 = 1526081) B1526081
theorem B1017399 : Blo 1016603 1017399 := bstep (se 1 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 1017399 = 1526099) B1526099
theorem B1017419 : Blo 1016603 1017419 := bstep (se 1 (by rfl) ⟨763064, by rfl⟩ : syracuseStep 1017419 = 1526129) B1526129
theorem B1017431 : Blo 1016603 1017431 := bstep (se 1 (by rfl) ⟨763073, by rfl⟩ : syracuseStep 1017431 = 1526147) B1526147
theorem B1017451 : Blo 1016603 1017451 := bstep (se 1 (by rfl) ⟨763088, by rfl⟩ : syracuseStep 1017451 = 1526177) B1526177
theorem B1017463 : Blo 1016603 1017463 := bstep (se 1 (by rfl) ⟨763097, by rfl⟩ : syracuseStep 1017463 = 1526195) B1526195
theorem B1017483 : Blo 1016603 1017483 := bstep (se 1 (by rfl) ⟨763112, by rfl⟩ : syracuseStep 1017483 = 1526225) B1526225
theorem B1017495 : Blo 1016603 1017495 := bstep (se 1 (by rfl) ⟨763121, by rfl⟩ : syracuseStep 1017495 = 1526243) B1526243
theorem B2295449 : Blo 1016603 2295449 := bstep (se 2 (by rfl) ⟨860793, by rfl⟩ : syracuseStep 2295449 = 1721587) B1721587
theorem B1017515 : Blo 1016603 1017515 := bstep (se 1 (by rfl) ⟨763136, by rfl⟩ : syracuseStep 1017515 = 1526273) B1526273
theorem B1017527 : Blo 1016603 1017527 := bstep (se 1 (by rfl) ⟨763145, by rfl⟩ : syracuseStep 1017527 = 1526291) B1526291
theorem B1017547 : Blo 1016603 1017547 := bstep (se 1 (by rfl) ⟨763160, by rfl⟩ : syracuseStep 1017547 = 1526321) B1526321
theorem B21989069 : Blo 1016603 21989069 := bstep (se 3 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 21989069 = 8245901) B8245901
theorem B1017559 : Blo 1016603 1017559 := bstep (se 1 (by rfl) ⟨763169, by rfl⟩ : syracuseStep 1017559 = 1526339) B1526339
theorem B1017579 : Blo 1016603 1017579 := bstep (se 1 (by rfl) ⟨763184, by rfl⟩ : syracuseStep 1017579 = 1526369) B1526369
theorem B2295539 : Blo 1016603 2295539 := bstep (se 1 (by rfl) ⟨1721654, by rfl⟩ : syracuseStep 2295539 = 3443309) B3443309
theorem B1017591 : Blo 1016603 1017591 := bstep (se 1 (by rfl) ⟨763193, by rfl⟩ : syracuseStep 1017591 = 1526387) B1526387
theorem B1017611 : Blo 1016603 1017611 := bstep (se 1 (by rfl) ⟨763208, by rfl⟩ : syracuseStep 1017611 = 1526417) B1526417
theorem B1017623 : Blo 1016603 1017623 := bstep (se 1 (by rfl) ⟨763217, by rfl⟩ : syracuseStep 1017623 = 1526435) B1526435
theorem B2295575 : Blo 1016603 2295575 := bstep (se 1 (by rfl) ⟨1721681, by rfl⟩ : syracuseStep 2295575 = 3443363) B3443363
theorem B1017643 : Blo 1016603 1017643 := bstep (se 1 (by rfl) ⟨763232, by rfl⟩ : syracuseStep 1017643 = 1526465) B1526465
theorem B4130605 : Blo 1016603 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B1017655 : Blo 1016603 1017655 := bstep (se 1 (by rfl) ⟨763241, by rfl⟩ : syracuseStep 1017655 = 1526483) B1526483
theorem B1017675 : Blo 1016603 1017675 := bstep (se 1 (by rfl) ⟨763256, by rfl⟩ : syracuseStep 1017675 = 1526513) B1526513
theorem B1017687 : Blo 1016603 1017687 := bstep (se 1 (by rfl) ⟨763265, by rfl⟩ : syracuseStep 1017687 = 1526531) B1526531
theorem B1935191 : Blo 1016603 1935191 := bstep (se 1 (by rfl) ⟨1451393, by rfl⟩ : syracuseStep 1935191 = 2902787) B2902787
theorem B1017707 : Blo 1016603 1017707 := bstep (se 1 (by rfl) ⟨763280, by rfl⟩ : syracuseStep 1017707 = 1526561) B1526561
theorem B1017719 : Blo 1016603 1017719 := bstep (se 1 (by rfl) ⟨763289, by rfl⟩ : syracuseStep 1017719 = 1526579) B1526579
theorem B1017739 : Blo 1016603 1017739 := bstep (se 1 (by rfl) ⟨763304, by rfl⟩ : syracuseStep 1017739 = 1526609) B1526609
theorem B1017751 : Blo 1016603 1017751 := bstep (se 1 (by rfl) ⟨763313, by rfl⟩ : syracuseStep 1017751 = 1526627) B1526627
theorem B1017771 : Blo 1016603 1017771 := bstep (se 1 (by rfl) ⟨763328, by rfl⟩ : syracuseStep 1017771 = 1526657) B1526657
theorem B1017783 : Blo 1016603 1017783 := bstep (se 1 (by rfl) ⟨763337, by rfl⟩ : syracuseStep 1017783 = 1526675) B1526675
theorem B1017803 : Blo 1016603 1017803 := bstep (se 1 (by rfl) ⟨763352, by rfl⟩ : syracuseStep 1017803 = 1526705) B1526705
theorem B2295755 : Blo 1016603 2295755 := bstep (se 1 (by rfl) ⟨1721816, by rfl⟩ : syracuseStep 2295755 = 3443633) B3443633
theorem B1017815 : Blo 1016603 1017815 := bstep (se 1 (by rfl) ⟨763361, by rfl⟩ : syracuseStep 1017815 = 1526723) B1526723
theorem B1017835 : Blo 1016603 1017835 := bstep (se 1 (by rfl) ⟨763376, by rfl⟩ : syracuseStep 1017835 = 1526753) B1526753
theorem B1017847 : Blo 1016603 1017847 := bstep (se 1 (by rfl) ⟨763385, by rfl⟩ : syracuseStep 1017847 = 1526771) B1526771
theorem B2295809 : Blo 1016603 2295809 := bstep (se 2 (by rfl) ⟨860928, by rfl⟩ : syracuseStep 2295809 = 1721857) B1721857
theorem B1017867 : Blo 1016603 1017867 := bstep (se 1 (by rfl) ⟨763400, by rfl⟩ : syracuseStep 1017867 = 1526801) B1526801
theorem B1017879 : Blo 1016603 1017879 := bstep (se 1 (by rfl) ⟨763409, by rfl⟩ : syracuseStep 1017879 = 1526819) B1526819
theorem B1017899 : Blo 1016603 1017899 := bstep (se 1 (by rfl) ⟨763424, by rfl⟩ : syracuseStep 1017899 = 1526849) B1526849
theorem B1017911 : Blo 1016603 1017911 := bstep (se 1 (by rfl) ⟨763433, by rfl⟩ : syracuseStep 1017911 = 1526867) B1526867
theorem B1017931 : Blo 1016603 1017931 := bstep (se 1 (by rfl) ⟨763448, by rfl⟩ : syracuseStep 1017931 = 1526897) B1526897
theorem B1017943 : Blo 1016603 1017943 := bstep (se 1 (by rfl) ⟨763457, by rfl⟩ : syracuseStep 1017943 = 1526915) B1526915
theorem B1017963 : Blo 1016603 1017963 := bstep (se 1 (by rfl) ⟨763472, by rfl⟩ : syracuseStep 1017963 = 1526945) B1526945
theorem B1017975 : Blo 1016603 1017975 := bstep (se 1 (by rfl) ⟨763481, by rfl⟩ : syracuseStep 1017975 = 1526963) B1526963
theorem B1017995 : Blo 1016603 1017995 := bstep (se 1 (by rfl) ⟨763496, by rfl⟩ : syracuseStep 1017995 = 1526993) B1526993
theorem B1018007 : Blo 1016603 1018007 := bstep (se 1 (by rfl) ⟨763505, by rfl⟩ : syracuseStep 1018007 = 1527011) B1527011
theorem B1018027 : Blo 1016603 1018027 := bstep (se 1 (by rfl) ⟨763520, by rfl⟩ : syracuseStep 1018027 = 1527041) B1527041
theorem B1018039 : Blo 1016603 1018039 := bstep (se 1 (by rfl) ⟨763529, by rfl⟩ : syracuseStep 1018039 = 1527059) B1527059
theorem B1018059 : Blo 1016603 1018059 := bstep (se 1 (by rfl) ⟨763544, by rfl⟩ : syracuseStep 1018059 = 1527089) B1527089
theorem B1018071 : Blo 1016603 1018071 := bstep (se 1 (by rfl) ⟨763553, by rfl⟩ : syracuseStep 1018071 = 1527107) B1527107
theorem B2296025 : Blo 1016603 2296025 := bstep (se 2 (by rfl) ⟨861009, by rfl⟩ : syracuseStep 2296025 = 1722019) B1722019
theorem B1018091 : Blo 1016603 1018091 := bstep (se 1 (by rfl) ⟨763568, by rfl⟩ : syracuseStep 1018091 = 1527137) B1527137
theorem B1018103 : Blo 1016603 1018103 := bstep (se 1 (by rfl) ⟨763577, by rfl⟩ : syracuseStep 1018103 = 1527155) B1527155
theorem B1018123 : Blo 1016603 1018123 := bstep (se 1 (by rfl) ⟨763592, by rfl⟩ : syracuseStep 1018123 = 1527185) B1527185
theorem B5507345 : Blo 1016603 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B1018135 : Blo 1016603 1018135 := bstep (se 1 (by rfl) ⟨763601, by rfl⟩ : syracuseStep 1018135 = 1527203) B1527203
theorem B1018155 : Blo 1016603 1018155 := bstep (se 1 (by rfl) ⟨763616, by rfl⟩ : syracuseStep 1018155 = 1527233) B1527233
theorem B2296115 : Blo 1016603 2296115 := bstep (se 1 (by rfl) ⟨1722086, by rfl⟩ : syracuseStep 2296115 = 3444173) B3444173
theorem B1018167 : Blo 1016603 1018167 := bstep (se 1 (by rfl) ⟨763625, by rfl⟩ : syracuseStep 1018167 = 1527251) B1527251
theorem B6195521 : Blo 1016603 6195521 := bstep (se 2 (by rfl) ⟨2323320, by rfl⟩ : syracuseStep 6195521 = 4646641) B4646641
theorem B1018187 : Blo 1016603 1018187 := bstep (se 1 (by rfl) ⟨763640, by rfl⟩ : syracuseStep 1018187 = 1527281) B1527281
theorem B1018199 : Blo 1016603 1018199 := bstep (se 1 (by rfl) ⟨763649, by rfl⟩ : syracuseStep 1018199 = 1527299) B1527299
theorem B2296151 : Blo 1016603 2296151 := bstep (se 1 (by rfl) ⟨1722113, by rfl⟩ : syracuseStep 2296151 = 3444227) B3444227
theorem B1018219 : Blo 1016603 1018219 := bstep (se 1 (by rfl) ⟨763664, by rfl⟩ : syracuseStep 1018219 = 1527329) B1527329
theorem B1935731 : Blo 1016603 1935731 := bstep (se 1 (by rfl) ⟨1451798, by rfl⟩ : syracuseStep 1935731 = 2903597) B2903597
theorem B1018231 : Blo 1016603 1018231 := bstep (se 1 (by rfl) ⟨763673, by rfl⟩ : syracuseStep 1018231 = 1527347) B1527347
theorem B1018251 : Blo 1016603 1018251 := bstep (se 1 (by rfl) ⟨763688, by rfl⟩ : syracuseStep 1018251 = 1527377) B1527377
theorem B1018263 : Blo 1016603 1018263 := bstep (se 1 (by rfl) ⟨763697, by rfl⟩ : syracuseStep 1018263 = 1527395) B1527395
theorem B1018283 : Blo 1016603 1018283 := bstep (se 1 (by rfl) ⟨763712, by rfl⟩ : syracuseStep 1018283 = 1527425) B1527425
theorem B1018295 : Blo 1016603 1018295 := bstep (se 1 (by rfl) ⟨763721, by rfl⟩ : syracuseStep 1018295 = 1527443) B1527443
theorem B1018315 : Blo 1016603 1018315 := bstep (se 1 (by rfl) ⟨763736, by rfl⟩ : syracuseStep 1018315 = 1527473) B1527473
theorem B3443147 : Blo 1016603 3443147 := bstep (se 1 (by rfl) ⟨2582360, by rfl⟩ : syracuseStep 3443147 = 5164721) B5164721
theorem B1018327 : Blo 1016603 1018327 := bstep (se 1 (by rfl) ⟨763745, by rfl⟩ : syracuseStep 1018327 = 1527491) B1527491
theorem B1018347 : Blo 1016603 1018347 := bstep (se 1 (by rfl) ⟨763760, by rfl⟩ : syracuseStep 1018347 = 1527521) B1527521
theorem B1018359 : Blo 1016603 1018359 := bstep (se 1 (by rfl) ⟨763769, by rfl⟩ : syracuseStep 1018359 = 1527539) B1527539
theorem B1018379 : Blo 1016603 1018379 := bstep (se 1 (by rfl) ⟨763784, by rfl⟩ : syracuseStep 1018379 = 1527569) B1527569
theorem B2296331 : Blo 1016603 2296331 := bstep (se 1 (by rfl) ⟨1722248, by rfl⟩ : syracuseStep 2296331 = 3444497) B3444497
theorem B1018391 : Blo 1016603 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B1018411 : Blo 1016603 1018411 := bstep (se 1 (by rfl) ⟨763808, by rfl⟩ : syracuseStep 1018411 = 1527617) B1527617
theorem B1018423 : Blo 1016603 1018423 := bstep (se 1 (by rfl) ⟨763817, by rfl⟩ : syracuseStep 1018423 = 1527635) B1527635
theorem B1018443 : Blo 1016603 1018443 := bstep (se 1 (by rfl) ⟨763832, by rfl⟩ : syracuseStep 1018443 = 1527665) B1527665
theorem B1018455 : Blo 1016603 1018455 := bstep (se 1 (by rfl) ⟨763841, by rfl⟩ : syracuseStep 1018455 = 1527683) B1527683
theorem B1018475 : Blo 1016603 1018475 := bstep (se 1 (by rfl) ⟨763856, by rfl⟩ : syracuseStep 1018475 = 1527713) B1527713
theorem B1018487 : Blo 1016603 1018487 := bstep (se 1 (by rfl) ⟨763865, by rfl⟩ : syracuseStep 1018487 = 1527731) B1527731
theorem B1018507 : Blo 1016603 1018507 := bstep (se 1 (by rfl) ⟨763880, by rfl⟩ : syracuseStep 1018507 = 1527761) B1527761
theorem B1018519 : Blo 1016603 1018519 := bstep (se 1 (by rfl) ⟨763889, by rfl⟩ : syracuseStep 1018519 = 1527779) B1527779
theorem B1018539 : Blo 1016603 1018539 := bstep (se 1 (by rfl) ⟨763904, by rfl⟩ : syracuseStep 1018539 = 1527809) B1527809
theorem B1018551 : Blo 1016603 1018551 := bstep (se 1 (by rfl) ⟨763913, by rfl⟩ : syracuseStep 1018551 = 1527827) B1527827
theorem B1018571 : Blo 1016603 1018571 := bstep (se 1 (by rfl) ⟨763928, by rfl⟩ : syracuseStep 1018571 = 1527857) B1527857
theorem B1018583 : Blo 1016603 1018583 := bstep (se 1 (by rfl) ⟨763937, by rfl⟩ : syracuseStep 1018583 = 1527875) B1527875
theorem B3443417 : Blo 1016603 3443417 := bstep (se 2 (by rfl) ⟨1291281, by rfl⟩ : syracuseStep 3443417 = 2582563) B2582563
theorem B1018603 : Blo 1016603 1018603 := bstep (se 1 (by rfl) ⟨763952, by rfl⟩ : syracuseStep 1018603 = 1527905) B1527905
theorem B1018615 : Blo 1016603 1018615 := bstep (se 1 (by rfl) ⟨763961, by rfl⟩ : syracuseStep 1018615 = 1527923) B1527923
theorem B1018635 : Blo 1016603 1018635 := bstep (se 1 (by rfl) ⟨763976, by rfl⟩ : syracuseStep 1018635 = 1527953) B1527953
theorem B1018647 : Blo 1016603 1018647 := bstep (se 1 (by rfl) ⟨763985, by rfl⟩ : syracuseStep 1018647 = 1527971) B1527971
theorem B1018667 : Blo 1016603 1018667 := bstep (se 1 (by rfl) ⟨764000, by rfl⟩ : syracuseStep 1018667 = 1528001) B1528001
theorem B1018679 : Blo 1016603 1018679 := bstep (se 1 (by rfl) ⟨764009, by rfl⟩ : syracuseStep 1018679 = 1528019) B1528019
theorem B1018699 : Blo 1016603 1018699 := bstep (se 1 (by rfl) ⟨764024, by rfl⟩ : syracuseStep 1018699 = 1528049) B1528049
theorem B1018711 : Blo 1016603 1018711 := bstep (se 1 (by rfl) ⟨764033, by rfl⟩ : syracuseStep 1018711 = 1528067) B1528067
theorem B1936217 : Blo 1016603 1936217 := bstep (se 2 (by rfl) ⟨726081, by rfl⟩ : syracuseStep 1936217 = 1452163) B1452163
theorem B15698789 : Blo 1016603 15698789 := bstep (se 4 (by rfl) ⟨1471761, by rfl⟩ : syracuseStep 15698789 = 2943523) B2943523
theorem B1018731 : Blo 1016603 1018731 := bstep (se 1 (by rfl) ⟨764048, by rfl⟩ : syracuseStep 1018731 = 1528097) B1528097
theorem B1018743 : Blo 1016603 1018743 := bstep (se 1 (by rfl) ⟨764057, by rfl⟩ : syracuseStep 1018743 = 1528115) B1528115
theorem B1018763 : Blo 1016603 1018763 := bstep (se 1 (by rfl) ⟨764072, by rfl⟩ : syracuseStep 1018763 = 1528145) B1528145
theorem B1018775 : Blo 1016603 1018775 := bstep (se 1 (by rfl) ⟨764081, by rfl⟩ : syracuseStep 1018775 = 1528163) B1528163
theorem B1018795 : Blo 1016603 1018795 := bstep (se 1 (by rfl) ⟨764096, by rfl⟩ : syracuseStep 1018795 = 1528193) B1528193
theorem B1018807 : Blo 1016603 1018807 := bstep (se 1 (by rfl) ⟨764105, by rfl⟩ : syracuseStep 1018807 = 1528211) B1528211
theorem B1018827 : Blo 1016603 1018827 := bstep (se 1 (by rfl) ⟨764120, by rfl⟩ : syracuseStep 1018827 = 1528241) B1528241
theorem B1018839 : Blo 1016603 1018839 := bstep (se 1 (by rfl) ⟨764129, by rfl⟩ : syracuseStep 1018839 = 1528259) B1528259
theorem B1018859 : Blo 1016603 1018859 := bstep (se 1 (by rfl) ⟨764144, by rfl⟩ : syracuseStep 1018859 = 1528289) B1528289
theorem B1018871 : Blo 1016603 1018871 := bstep (se 1 (by rfl) ⟨764153, by rfl⟩ : syracuseStep 1018871 = 1528307) B1528307
theorem B1018891 : Blo 1016603 1018891 := bstep (se 1 (by rfl) ⟨764168, by rfl⟩ : syracuseStep 1018891 = 1528337) B1528337
theorem B1018903 : Blo 1016603 1018903 := bstep (se 1 (by rfl) ⟨764177, by rfl⟩ : syracuseStep 1018903 = 1528355) B1528355
theorem B1018923 : Blo 1016603 1018923 := bstep (se 1 (by rfl) ⟨764192, by rfl⟩ : syracuseStep 1018923 = 1528385) B1528385
theorem B1018935 : Blo 1016603 1018935 := bstep (se 1 (by rfl) ⟨764201, by rfl⟩ : syracuseStep 1018935 = 1528403) B1528403
theorem B1018955 : Blo 1016603 1018955 := bstep (se 1 (by rfl) ⟨764216, by rfl⟩ : syracuseStep 1018955 = 1528433) B1528433
theorem B1018967 : Blo 1016603 1018967 := bstep (se 1 (by rfl) ⟨764225, by rfl⟩ : syracuseStep 1018967 = 1528451) B1528451
theorem B1018987 : Blo 1016603 1018987 := bstep (se 1 (by rfl) ⟨764240, by rfl⟩ : syracuseStep 1018987 = 1528481) B1528481
theorem B1018999 : Blo 1016603 1018999 := bstep (se 1 (by rfl) ⟨764249, by rfl⟩ : syracuseStep 1018999 = 1528499) B1528499
theorem B1019019 : Blo 1016603 1019019 := bstep (se 1 (by rfl) ⟨764264, by rfl⟩ : syracuseStep 1019019 = 1528529) B1528529
theorem B1019031 : Blo 1016603 1019031 := bstep (se 1 (by rfl) ⟨764273, by rfl⟩ : syracuseStep 1019031 = 1528547) B1528547
theorem B1019051 : Blo 1016603 1019051 := bstep (se 1 (by rfl) ⟨764288, by rfl⟩ : syracuseStep 1019051 = 1528577) B1528577
theorem B1019063 : Blo 1016603 1019063 := bstep (se 1 (by rfl) ⟨764297, by rfl⟩ : syracuseStep 1019063 = 1528595) B1528595
theorem B1019083 : Blo 1016603 1019083 := bstep (se 1 (by rfl) ⟨764312, by rfl⟩ : syracuseStep 1019083 = 1528625) B1528625
theorem B1019095 : Blo 1016603 1019095 := bstep (se 1 (by rfl) ⟨764321, by rfl⟩ : syracuseStep 1019095 = 1528643) B1528643
theorem B1019115 : Blo 1016603 1019115 := bstep (se 1 (by rfl) ⟨764336, by rfl⟩ : syracuseStep 1019115 = 1528673) B1528673
theorem B1019127 : Blo 1016603 1019127 := bstep (se 1 (by rfl) ⟨764345, by rfl⟩ : syracuseStep 1019127 = 1528691) B1528691
theorem B1019147 : Blo 1016603 1019147 := bstep (se 1 (by rfl) ⟨764360, by rfl⟩ : syracuseStep 1019147 = 1528721) B1528721
theorem B1019159 : Blo 1016603 1019159 := bstep (se 1 (by rfl) ⟨764369, by rfl⟩ : syracuseStep 1019159 = 1528739) B1528739
theorem B1019179 : Blo 1016603 1019179 := bstep (se 1 (by rfl) ⟨764384, by rfl⟩ : syracuseStep 1019179 = 1528769) B1528769
theorem B1019191 : Blo 1016603 1019191 := bstep (se 1 (by rfl) ⟨764393, by rfl⟩ : syracuseStep 1019191 = 1528787) B1528787
theorem B5868875 : Blo 1016603 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B1019211 : Blo 1016603 1019211 := bstep (se 1 (by rfl) ⟨764408, by rfl⟩ : syracuseStep 1019211 = 1528817) B1528817
theorem B1019223 : Blo 1016603 1019223 := bstep (se 1 (by rfl) ⟨764417, by rfl⟩ : syracuseStep 1019223 = 1528835) B1528835
theorem B1019243 : Blo 1016603 1019243 := bstep (se 1 (by rfl) ⟨764432, by rfl⟩ : syracuseStep 1019243 = 1528865) B1528865
theorem B1019255 : Blo 1016603 1019255 := bstep (se 1 (by rfl) ⟨764441, by rfl⟩ : syracuseStep 1019255 = 1528883) B1528883
theorem B5148035 : Blo 1016603 5148035 := bstep (se 1 (by rfl) ⟨3861026, by rfl⟩ : syracuseStep 5148035 = 7722053) B7722053
theorem B1019275 : Blo 1016603 1019275 := bstep (se 1 (by rfl) ⟨764456, by rfl⟩ : syracuseStep 1019275 = 1528913) B1528913
theorem B1019287 : Blo 1016603 1019287 := bstep (se 1 (by rfl) ⟨764465, by rfl⟩ : syracuseStep 1019287 = 1528931) B1528931
theorem B3444119 : Blo 1016603 3444119 := bstep (se 1 (by rfl) ⟨2583089, by rfl⟩ : syracuseStep 3444119 = 5166179) B5166179
theorem B1019307 : Blo 1016603 1019307 := bstep (se 1 (by rfl) ⟨764480, by rfl⟩ : syracuseStep 1019307 = 1528961) B1528961
theorem B3870125 : Blo 1016603 3870125 := bstep (se 3 (by rfl) ⟨725648, by rfl⟩ : syracuseStep 3870125 = 1451297) B1451297
theorem B1019319 : Blo 1016603 1019319 := bstep (se 1 (by rfl) ⟨764489, by rfl⟩ : syracuseStep 1019319 = 1528979) B1528979
theorem B1019339 : Blo 1016603 1019339 := bstep (se 1 (by rfl) ⟨764504, by rfl⟩ : syracuseStep 1019339 = 1529009) B1529009
theorem B1019351 : Blo 1016603 1019351 := bstep (se 1 (by rfl) ⟨764513, by rfl⟩ : syracuseStep 1019351 = 1529027) B1529027
theorem B1019371 : Blo 1016603 1019371 := bstep (se 1 (by rfl) ⟨764528, by rfl⟩ : syracuseStep 1019371 = 1529057) B1529057
theorem B1019383 : Blo 1016603 1019383 := bstep (se 1 (by rfl) ⟨764537, by rfl⟩ : syracuseStep 1019383 = 1529075) B1529075
theorem B1019403 : Blo 1016603 1019403 := bstep (se 1 (by rfl) ⟨764552, by rfl⟩ : syracuseStep 1019403 = 1529105) B1529105
theorem B1019415 : Blo 1016603 1019415 := bstep (se 1 (by rfl) ⟨764561, by rfl⟩ : syracuseStep 1019415 = 1529123) B1529123
theorem B1019435 : Blo 1016603 1019435 := bstep (se 1 (by rfl) ⟨764576, by rfl⟩ : syracuseStep 1019435 = 1529153) B1529153
theorem B1019447 : Blo 1016603 1019447 := bstep (se 1 (by rfl) ⟨764585, by rfl⟩ : syracuseStep 1019447 = 1529171) B1529171
theorem B1019467 : Blo 1016603 1019467 := bstep (se 1 (by rfl) ⟨764600, by rfl⟩ : syracuseStep 1019467 = 1529201) B1529201
theorem B1019479 : Blo 1016603 1019479 := bstep (se 1 (by rfl) ⟨764609, by rfl⟩ : syracuseStep 1019479 = 1529219) B1529219
theorem B1019499 : Blo 1016603 1019499 := bstep (se 1 (by rfl) ⟨764624, by rfl⟩ : syracuseStep 1019499 = 1529249) B1529249
theorem B1019511 : Blo 1016603 1019511 := bstep (se 1 (by rfl) ⟨764633, by rfl⟩ : syracuseStep 1019511 = 1529267) B1529267
theorem B1019531 : Blo 1016603 1019531 := bstep (se 1 (by rfl) ⟨764648, by rfl⟩ : syracuseStep 1019531 = 1529297) B1529297
theorem B1019543 : Blo 1016603 1019543 := bstep (se 1 (by rfl) ⟨764657, by rfl⟩ : syracuseStep 1019543 = 1529315) B1529315
theorem B1019563 : Blo 1016603 1019563 := bstep (se 1 (by rfl) ⟨764672, by rfl⟩ : syracuseStep 1019563 = 1529345) B1529345
theorem B1019575 : Blo 1016603 1019575 := bstep (se 1 (by rfl) ⟨764681, by rfl⟩ : syracuseStep 1019575 = 1529363) B1529363
theorem B1019595 : Blo 1016603 1019595 := bstep (se 1 (by rfl) ⟨764696, by rfl⟩ : syracuseStep 1019595 = 1529393) B1529393
theorem B1019607 : Blo 1016603 1019607 := bstep (se 1 (by rfl) ⟨764705, by rfl⟩ : syracuseStep 1019607 = 1529411) B1529411
theorem B1019627 : Blo 1016603 1019627 := bstep (se 1 (by rfl) ⟨764720, by rfl⟩ : syracuseStep 1019627 = 1529441) B1529441
theorem B1019639 : Blo 1016603 1019639 := bstep (se 1 (by rfl) ⟨764729, by rfl⟩ : syracuseStep 1019639 = 1529459) B1529459
theorem B1019659 : Blo 1016603 1019659 := bstep (se 1 (by rfl) ⟨764744, by rfl⟩ : syracuseStep 1019659 = 1529489) B1529489
theorem B1019671 : Blo 1016603 1019671 := bstep (se 1 (by rfl) ⟨764753, by rfl⟩ : syracuseStep 1019671 = 1529507) B1529507
theorem B1019691 : Blo 1016603 1019691 := bstep (se 1 (by rfl) ⟨764768, by rfl⟩ : syracuseStep 1019691 = 1529537) B1529537
theorem B1019703 : Blo 1016603 1019703 := bstep (se 1 (by rfl) ⟨764777, by rfl⟩ : syracuseStep 1019703 = 1529555) B1529555
theorem B1019723 : Blo 1016603 1019723 := bstep (se 1 (by rfl) ⟨764792, by rfl⟩ : syracuseStep 1019723 = 1529585) B1529585
theorem B1019735 : Blo 1016603 1019735 := bstep (se 1 (by rfl) ⟨764801, by rfl⟩ : syracuseStep 1019735 = 1529603) B1529603
theorem B4034393 : Blo 1016603 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B1019755 : Blo 1016603 1019755 := bstep (se 1 (by rfl) ⟨764816, by rfl⟩ : syracuseStep 1019755 = 1529633) B1529633
theorem B1019767 : Blo 1016603 1019767 := bstep (se 1 (by rfl) ⟨764825, by rfl⟩ : syracuseStep 1019767 = 1529651) B1529651
theorem B1019787 : Blo 1016603 1019787 := bstep (se 1 (by rfl) ⟨764840, by rfl⟩ : syracuseStep 1019787 = 1529681) B1529681
theorem B1019799 : Blo 1016603 1019799 := bstep (se 1 (by rfl) ⟨764849, by rfl⟩ : syracuseStep 1019799 = 1529699) B1529699
theorem B1019819 : Blo 1016603 1019819 := bstep (se 1 (by rfl) ⟨764864, by rfl⟩ : syracuseStep 1019819 = 1529729) B1529729
theorem B1019831 : Blo 1016603 1019831 := bstep (se 1 (by rfl) ⟨764873, by rfl⟩ : syracuseStep 1019831 = 1529747) B1529747
theorem B1019851 : Blo 1016603 1019851 := bstep (se 1 (by rfl) ⟨764888, by rfl⟩ : syracuseStep 1019851 = 1529777) B1529777
theorem B1019863 : Blo 1016603 1019863 := bstep (se 1 (by rfl) ⟨764897, by rfl⟩ : syracuseStep 1019863 = 1529795) B1529795
theorem B1019883 : Blo 1016603 1019883 := bstep (se 1 (by rfl) ⟨764912, by rfl⟩ : syracuseStep 1019883 = 1529825) B1529825
theorem B1019895 : Blo 1016603 1019895 := bstep (se 1 (by rfl) ⟨764921, by rfl⟩ : syracuseStep 1019895 = 1529843) B1529843
theorem B1019915 : Blo 1016603 1019915 := bstep (se 1 (by rfl) ⟨764936, by rfl⟩ : syracuseStep 1019915 = 1529873) B1529873
theorem B18616337 : Blo 1016603 18616337 := bstep (se 2 (by rfl) ⟨6981126, by rfl⟩ : syracuseStep 18616337 = 13962253) B13962253
theorem B1019927 : Blo 1016603 1019927 := bstep (se 1 (by rfl) ⟨764945, by rfl⟩ : syracuseStep 1019927 = 1529891) B1529891
theorem B1839127 : Blo 1016603 1839127 := bstep (se 1 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 1839127 = 2758691) B2758691
theorem B1019947 : Blo 1016603 1019947 := bstep (se 1 (by rfl) ⟨764960, by rfl⟩ : syracuseStep 1019947 = 1529921) B1529921
theorem B3313715 : Blo 1016603 3313715 := bstep (se 1 (by rfl) ⟨2485286, by rfl⟩ : syracuseStep 3313715 = 4970573) B4970573
theorem B1019959 : Blo 1016603 1019959 := bstep (se 1 (by rfl) ⟨764969, by rfl⟩ : syracuseStep 1019959 = 1529939) B1529939
theorem B1019979 : Blo 1016603 1019979 := bstep (se 1 (by rfl) ⟨764984, by rfl⟩ : syracuseStep 1019979 = 1529969) B1529969
theorem B1019991 : Blo 1016603 1019991 := bstep (se 1 (by rfl) ⟨764993, by rfl⟩ : syracuseStep 1019991 = 1529987) B1529987
theorem B1020011 : Blo 1016603 1020011 := bstep (se 1 (by rfl) ⟨765008, by rfl⟩ : syracuseStep 1020011 = 1530017) B1530017
theorem B1020023 : Blo 1016603 1020023 := bstep (se 1 (by rfl) ⟨765017, by rfl⟩ : syracuseStep 1020023 = 1530035) B1530035
theorem B11145347 : Blo 1016603 11145347 := bstep (se 1 (by rfl) ⟨8359010, by rfl⟩ : syracuseStep 11145347 = 16718021) B16718021
theorem B1020043 : Blo 1016603 1020043 := bstep (se 1 (by rfl) ⟨765032, by rfl⟩ : syracuseStep 1020043 = 1530065) B1530065
theorem B1020055 : Blo 1016603 1020055 := bstep (se 1 (by rfl) ⟨765041, by rfl⟩ : syracuseStep 1020055 = 1530083) B1530083
theorem B1020075 : Blo 1016603 1020075 := bstep (se 1 (by rfl) ⟨765056, by rfl⟩ : syracuseStep 1020075 = 1530113) B1530113
theorem B3870899 : Blo 1016603 3870899 := bstep (se 1 (by rfl) ⟨2903174, by rfl⟩ : syracuseStep 3870899 = 5806349) B5806349
theorem B1020087 : Blo 1016603 1020087 := bstep (se 1 (by rfl) ⟨765065, by rfl⟩ : syracuseStep 1020087 = 1530131) B1530131
theorem B1020107 : Blo 1016603 1020107 := bstep (se 1 (by rfl) ⟨765080, by rfl⟩ : syracuseStep 1020107 = 1530161) B1530161
theorem B1020119 : Blo 1016603 1020119 := bstep (se 1 (by rfl) ⟨765089, by rfl⟩ : syracuseStep 1020119 = 1530179) B1530179
theorem B6197465 : Blo 1016603 6197465 := bstep (se 2 (by rfl) ⟨2324049, by rfl⟩ : syracuseStep 6197465 = 4648099) B4648099
theorem B1020139 : Blo 1016603 1020139 := bstep (se 1 (by rfl) ⟨765104, by rfl⟩ : syracuseStep 1020139 = 1530209) B1530209
theorem B17404145 : Blo 1016603 17404145 := bstep (se 2 (by rfl) ⟨6526554, by rfl⟩ : syracuseStep 17404145 = 13053109) B13053109
theorem B1020151 : Blo 1016603 1020151 := bstep (se 1 (by rfl) ⟨765113, by rfl⟩ : syracuseStep 1020151 = 1530227) B1530227
theorem B7737605 : Blo 1016603 7737605 := bstep (se 4 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 7737605 = 1450801) B1450801
theorem B9310469 : Blo 1016603 9310469 := bstep (se 4 (by rfl) ⟨872856, by rfl⟩ : syracuseStep 9310469 = 1745713) B1745713
theorem B1020171 : Blo 1016603 1020171 := bstep (se 1 (by rfl) ⟨765128, by rfl⟩ : syracuseStep 1020171 = 1530257) B1530257
theorem B1020183 : Blo 1016603 1020183 := bstep (se 1 (by rfl) ⟨765137, by rfl⟩ : syracuseStep 1020183 = 1530275) B1530275
theorem B1020203 : Blo 1016603 1020203 := bstep (se 1 (by rfl) ⟨765152, by rfl⟩ : syracuseStep 1020203 = 1530305) B1530305
theorem B1020215 : Blo 1016603 1020215 := bstep (se 1 (by rfl) ⟨765161, by rfl⟩ : syracuseStep 1020215 = 1530323) B1530323
theorem B1020235 : Blo 1016603 1020235 := bstep (se 1 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 1020235 = 1530353) B1530353
theorem B1020247 : Blo 1016603 1020247 := bstep (se 1 (by rfl) ⟨765185, by rfl⟩ : syracuseStep 1020247 = 1530371) B1530371
theorem B1020267 : Blo 1016603 1020267 := bstep (se 1 (by rfl) ⟨765200, by rfl⟩ : syracuseStep 1020267 = 1530401) B1530401
theorem B1020279 : Blo 1016603 1020279 := bstep (se 1 (by rfl) ⟨765209, by rfl⟩ : syracuseStep 1020279 = 1530419) B1530419
theorem B1020299 : Blo 1016603 1020299 := bstep (se 1 (by rfl) ⟨765224, by rfl⟩ : syracuseStep 1020299 = 1530449) B1530449
theorem B1020311 : Blo 1016603 1020311 := bstep (se 1 (by rfl) ⟨765233, by rfl⟩ : syracuseStep 1020311 = 1530467) B1530467
theorem B1020331 : Blo 1016603 1020331 := bstep (se 1 (by rfl) ⟨765248, by rfl⟩ : syracuseStep 1020331 = 1530497) B1530497
theorem B1020343 : Blo 1016603 1020343 := bstep (se 1 (by rfl) ⟨765257, by rfl⟩ : syracuseStep 1020343 = 1530515) B1530515
theorem B1020363 : Blo 1016603 1020363 := bstep (se 1 (by rfl) ⟨765272, by rfl⟩ : syracuseStep 1020363 = 1530545) B1530545
theorem B1020375 : Blo 1016603 1020375 := bstep (se 1 (by rfl) ⟨765281, by rfl⟩ : syracuseStep 1020375 = 1530563) B1530563
theorem B1020395 : Blo 1016603 1020395 := bstep (se 1 (by rfl) ⟨765296, by rfl⟩ : syracuseStep 1020395 = 1530593) B1530593
theorem B1020407 : Blo 1016603 1020407 := bstep (se 1 (by rfl) ⟨765305, by rfl⟩ : syracuseStep 1020407 = 1530611) B1530611
theorem B1020427 : Blo 1016603 1020427 := bstep (se 1 (by rfl) ⟨765320, by rfl⟩ : syracuseStep 1020427 = 1530641) B1530641
theorem B1020439 : Blo 1016603 1020439 := bstep (se 1 (by rfl) ⟨765329, by rfl⟩ : syracuseStep 1020439 = 1530659) B1530659
theorem B1020459 : Blo 1016603 1020459 := bstep (se 1 (by rfl) ⟨765344, by rfl⟩ : syracuseStep 1020459 = 1530689) B1530689
theorem B1020471 : Blo 1016603 1020471 := bstep (se 1 (by rfl) ⟨765353, by rfl⟩ : syracuseStep 1020471 = 1530707) B1530707
theorem B1020491 : Blo 1016603 1020491 := bstep (se 1 (by rfl) ⟨765368, by rfl⟩ : syracuseStep 1020491 = 1530737) B1530737
theorem B1020503 : Blo 1016603 1020503 := bstep (se 1 (by rfl) ⟨765377, by rfl⟩ : syracuseStep 1020503 = 1530755) B1530755
theorem B1020523 : Blo 1016603 1020523 := bstep (se 1 (by rfl) ⟨765392, by rfl⟩ : syracuseStep 1020523 = 1530785) B1530785
theorem B1020535 : Blo 1016603 1020535 := bstep (se 1 (by rfl) ⟨765401, by rfl⟩ : syracuseStep 1020535 = 1530803) B1530803
theorem B1020555 : Blo 1016603 1020555 := bstep (se 1 (by rfl) ⟨765416, by rfl⟩ : syracuseStep 1020555 = 1530833) B1530833
theorem B1020567 : Blo 1016603 1020567 := bstep (se 1 (by rfl) ⟨765425, by rfl⟩ : syracuseStep 1020567 = 1530851) B1530851
theorem B1020587 : Blo 1016603 1020587 := bstep (se 1 (by rfl) ⟨765440, by rfl⟩ : syracuseStep 1020587 = 1530881) B1530881
theorem B1020599 : Blo 1016603 1020599 := bstep (se 1 (by rfl) ⟨765449, by rfl⟩ : syracuseStep 1020599 = 1530899) B1530899
theorem B9409571 : Blo 1016603 9409571 := bstep (se 1 (by rfl) ⟨7057178, by rfl⟩ : syracuseStep 9409571 = 14114357) B14114357
theorem B1086743 : Blo 1016603 1086743 := bstep (se 1 (by rfl) ⟨815057, by rfl⟩ : syracuseStep 1086743 = 1630115) B1630115
theorem B3347801 : Blo 1016603 3347801 := bstep (se 2 (by rfl) ⟨1255425, by rfl⟩ : syracuseStep 3347801 = 2510851) B2510851
theorem B5969483 : Blo 1016603 5969483 := bstep (se 1 (by rfl) ⟨4477112, by rfl⟩ : syracuseStep 5969483 = 8954225) B8954225
theorem B6198877 : Blo 1016603 6198877 := bstep (se 3 (by rfl) ⟨1162289, by rfl⟩ : syracuseStep 6198877 = 2324579) B2324579
theorem B3872387 : Blo 1016603 3872387 := bstep (se 1 (by rfl) ⟨2904290, by rfl⟩ : syracuseStep 3872387 = 5808581) B5808581
theorem B5805917 : Blo 1016603 5805917 := bstep (se 3 (by rfl) ⟨1088609, by rfl⟩ : syracuseStep 5805917 = 2177219) B2177219
theorem B1087435 : Blo 1016603 1087435 := bstep (se 1 (by rfl) ⟨815576, by rfl⟩ : syracuseStep 1087435 = 1631153) B1631153
theorem B1447897 : Blo 1016603 1447897 := bstep (se 2 (by rfl) ⟨542961, by rfl⟩ : syracuseStep 1447897 = 1085923) B1085923
theorem B3676205 : Blo 1016603 3676205 := bstep (se 3 (by rfl) ⟨689288, by rfl⟩ : syracuseStep 3676205 = 1378577) B1378577
theorem B3872843 : Blo 1016603 3872843 := bstep (se 1 (by rfl) ⟨2904632, by rfl⟩ : syracuseStep 3872843 = 5809265) B5809265
theorem B8689841 : Blo 1016603 8689841 := bstep (se 2 (by rfl) ⟨3258690, by rfl⟩ : syracuseStep 8689841 = 6517381) B6517381
theorem B3873041 : Blo 1016603 3873041 := bstep (se 2 (by rfl) ⟨1452390, by rfl⟩ : syracuseStep 3873041 = 2904781) B2904781
theorem B1743257 : Blo 1016603 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B5806667 : Blo 1016603 5806667 := bstep (se 1 (by rfl) ⟨4355000, by rfl⟩ : syracuseStep 5806667 = 8710001) B8710001
theorem B7740035 : Blo 1016603 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B4889267 : Blo 1016603 4889267 := bstep (se 1 (by rfl) ⟨3666950, by rfl⟩ : syracuseStep 4889267 = 7333901) B7333901
theorem B5151761 : Blo 1016603 5151761 := bstep (se 2 (by rfl) ⟨1931910, by rfl⟩ : syracuseStep 5151761 = 3863821) B3863821
theorem B3873815 : Blo 1016603 3873815 := bstep (se 1 (by rfl) ⟨2905361, by rfl⟩ : syracuseStep 3873815 = 5810723) B5810723
theorem B1449047 : Blo 1016603 1449047 := bstep (se 1 (by rfl) ⟨1086785, by rfl⟩ : syracuseStep 1449047 = 2173571) B2173571
theorem B5151923 : Blo 1016603 5151923 := bstep (se 1 (by rfl) ⟨3863942, by rfl⟩ : syracuseStep 5151923 = 7727885) B7727885
theorem B3874013 : Blo 1016603 3874013 := bstep (se 3 (by rfl) ⟨726377, by rfl⟩ : syracuseStep 3874013 = 1452755) B1452755
theorem B1088759 : Blo 1016603 1088759 := bstep (se 1 (by rfl) ⟨816569, by rfl⟩ : syracuseStep 1088759 = 1633139) B1633139
theorem B1088887 : Blo 1016603 1088887 := bstep (se 1 (by rfl) ⟨816665, by rfl⟩ : syracuseStep 1088887 = 1633331) B1633331
theorem B1449355 : Blo 1016603 1449355 := bstep (se 1 (by rfl) ⟨1087016, by rfl⟩ : syracuseStep 1449355 = 2174033) B2174033
theorem B6627089 : Blo 1016603 6627089 := bstep (se 2 (by rfl) ⟨2485158, by rfl⟩ : syracuseStep 6627089 = 4970317) B4970317
theorem B1089451 : Blo 1016603 1089451 := bstep (se 1 (by rfl) ⟨817088, by rfl⟩ : syracuseStep 1089451 = 1634177) B1634177
theorem B7348259 : Blo 1016603 7348259 := bstep (se 1 (by rfl) ⟨5511194, by rfl⟩ : syracuseStep 7348259 = 11022389) B11022389
theorem B1089707 : Blo 1016603 1089707 := bstep (se 1 (by rfl) ⟨817280, by rfl⟩ : syracuseStep 1089707 = 1634561) B1634561
theorem B5808307 : Blo 1016603 5808307 := bstep (se 1 (by rfl) ⟨4356230, by rfl⟩ : syracuseStep 5808307 = 8712461) B8712461
theorem B1450391 : Blo 1016603 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B4891211 : Blo 1016603 4891211 := bstep (se 1 (by rfl) ⟨3668408, by rfl⟩ : syracuseStep 4891211 = 7336817) B7336817
theorem B1450585 : Blo 1016603 1450585 := bstep (se 2 (by rfl) ⟨543969, by rfl⟩ : syracuseStep 1450585 = 1087939) B1087939
theorem B2794201 : Blo 1016603 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B1286923 : Blo 1016603 1286923 := bstep (se 1 (by rfl) ⟨965192, by rfl⟩ : syracuseStep 1286923 = 1930385) B1930385
theorem B19079981 : Blo 1016603 19079981 := bstep (se 3 (by rfl) ⟨3577496, by rfl⟩ : syracuseStep 19079981 = 7154993) B7154993
theorem B1287191 : Blo 1016603 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B5153867 : Blo 1016603 5153867 := bstep (se 1 (by rfl) ⟨3865400, by rfl⟩ : syracuseStep 5153867 = 7730801) B7730801
theorem B4892035 : Blo 1016603 4892035 := bstep (se 1 (by rfl) ⟨3669026, by rfl⟩ : syracuseStep 4892035 = 7338053) B7338053
theorem B8365517 : Blo 1016603 8365517 := bstep (se 3 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 8365517 = 3137069) B3137069
theorem B5809765 : Blo 1016603 5809765 := bstep (se 4 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 5809765 = 1089331) B1089331
theorem B14689943 : Blo 1016603 14689943 := bstep (se 1 (by rfl) ⟨11017457, by rfl⟩ : syracuseStep 14689943 = 22034915) B22034915
theorem B1287895 : Blo 1016603 1287895 := bstep (se 1 (by rfl) ⟨965921, by rfl⟩ : syracuseStep 1287895 = 1931843) B1931843
theorem B12396293 : Blo 1016603 12396293 := bstep (se 4 (by rfl) ⟨1162152, by rfl⟩ : syracuseStep 12396293 = 2324305) B2324305
theorem B2172683 : Blo 1016603 2172683 := bstep (se 1 (by rfl) ⟨1629512, by rfl⟩ : syracuseStep 2172683 = 3259025) B3259025
theorem B6530861 : Blo 1016603 6530861 := bstep (se 3 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 6530861 = 2449073) B2449073
theorem B7743437 : Blo 1016603 7743437 := bstep (se 3 (by rfl) ⟨1451894, by rfl⟩ : syracuseStep 7743437 = 2903789) B2903789
theorem B1452043 : Blo 1016603 1452043 := bstep (se 1 (by rfl) ⟨1089032, by rfl⟩ : syracuseStep 1452043 = 2178065) B2178065
theorem B7743923 : Blo 1016603 7743923 := bstep (se 1 (by rfl) ⟨5807942, by rfl⟩ : syracuseStep 7743923 = 11615885) B11615885
theorem B18557363 : Blo 1016603 18557363 := bstep (se 1 (by rfl) ⟨13918022, by rfl⟩ : syracuseStep 18557363 = 27836045) B27836045
theorem B1223191 : Blo 1016603 1223191 := bstep (se 1 (by rfl) ⟨917393, by rfl⟩ : syracuseStep 1223191 = 1834787) B1834787
theorem B2173529 : Blo 1016603 2173529 := bstep (se 2 (by rfl) ⟨815073, by rfl⟩ : syracuseStep 2173529 = 1630147) B1630147
theorem B4401985 : Blo 1016603 4401985 := bstep (se 2 (by rfl) ⟨1650744, by rfl⟩ : syracuseStep 4401985 = 3301489) B3301489
theorem B5155649 : Blo 1016603 5155649 := bstep (se 2 (by rfl) ⟨1933368, by rfl⟩ : syracuseStep 5155649 = 3866737) B3866737
theorem B2895041 : Blo 1016603 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B2895065 : Blo 1016603 2895065 := bstep (se 2 (by rfl) ⟨1085649, by rfl⟩ : syracuseStep 2895065 = 2171299) B2171299
theorem B2174323 : Blo 1016603 2174323 := bstep (se 1 (by rfl) ⟨1630742, by rfl⟩ : syracuseStep 2174323 = 3261485) B3261485
theorem B1289611 : Blo 1016603 1289611 := bstep (se 1 (by rfl) ⟨967208, by rfl⟩ : syracuseStep 1289611 = 1934417) B1934417
theorem B31370723 : Blo 1016603 31370723 := bstep (se 1 (by rfl) ⟨23528042, by rfl⟩ : syracuseStep 31370723 = 47056085) B47056085
theorem B1715735 : Blo 1016603 1715735 := bstep (se 1 (by rfl) ⟨1286801, by rfl⟩ : syracuseStep 1715735 = 2573603) B2573603
theorem B4894301 : Blo 1016603 4894301 := bstep (se 3 (by rfl) ⟨917681, by rfl⟩ : syracuseStep 4894301 = 1835363) B1835363
theorem B1715863 : Blo 1016603 1715863 := bstep (se 1 (by rfl) ⟨1286897, by rfl⟩ : syracuseStep 1715863 = 2573795) B2573795
theorem B3714833 : Blo 1016603 3714833 := bstep (se 2 (by rfl) ⟨1393062, by rfl⟩ : syracuseStep 3714833 = 2786125) B2786125
theorem B7745381 : Blo 1016603 7745381 := bstep (se 4 (by rfl) ⟨726129, by rfl⟩ : syracuseStep 7745381 = 1452259) B1452259
theorem B25472945 : Blo 1016603 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B2175169 : Blo 1016603 2175169 := bstep (se 2 (by rfl) ⟨815688, by rfl⟩ : syracuseStep 2175169 = 1631377) B1631377
theorem B1159435 : Blo 1016603 1159435 := bstep (se 1 (by rfl) ⟨869576, by rfl⟩ : syracuseStep 1159435 = 1739153) B1739153
theorem B1716491 : Blo 1016603 1716491 := bstep (se 1 (by rfl) ⟨1287368, by rfl⟩ : syracuseStep 1716491 = 2574737) B2574737
theorem B7745867 : Blo 1016603 7745867 := bstep (se 1 (by rfl) ⟨5809400, by rfl⟩ : syracuseStep 7745867 = 11618801) B11618801
theorem B1290583 : Blo 1016603 1290583 := bstep (se 1 (by rfl) ⟨967937, by rfl⟩ : syracuseStep 1290583 = 1935875) B1935875
theorem B1716619 : Blo 1016603 1716619 := bstep (se 1 (by rfl) ⟨1287464, by rfl⟩ : syracuseStep 1716619 = 2574929) B2574929
theorem B2896307 : Blo 1016603 2896307 := bstep (se 1 (by rfl) ⟨2172230, by rfl⟩ : syracuseStep 2896307 = 4344461) B4344461
theorem B2175511 : Blo 1016603 2175511 := bstep (se 1 (by rfl) ⟨1631633, by rfl⟩ : syracuseStep 2175511 = 3263267) B3263267
theorem B1716761 : Blo 1016603 1716761 := bstep (se 2 (by rfl) ⟨643785, by rfl⟩ : syracuseStep 1716761 = 1287571) B1287571
theorem B1716889 : Blo 1016603 1716889 := bstep (se 2 (by rfl) ⟨643833, by rfl⟩ : syracuseStep 1716889 = 1287667) B1287667
theorem B5157593 : Blo 1016603 5157593 := bstep (se 2 (by rfl) ⟨1934097, by rfl⟩ : syracuseStep 5157593 = 3868195) B3868195
theorem B1291403 : Blo 1016603 1291403 := bstep (se 1 (by rfl) ⟨968552, by rfl⟩ : syracuseStep 1291403 = 1937105) B1937105
theorem B1717463 : Blo 1016603 1717463 := bstep (se 1 (by rfl) ⟨1288097, by rfl⟩ : syracuseStep 1717463 = 2576195) B2576195
theorem B1717591 : Blo 1016603 1717591 := bstep (se 1 (by rfl) ⟨1288193, by rfl⟩ : syracuseStep 1717591 = 2576387) B2576387
theorem B3487169 : Blo 1016603 3487169 := bstep (se 2 (by rfl) ⟨1307688, by rfl⟩ : syracuseStep 3487169 = 2615377) B2615377
theorem B4896301 : Blo 1016603 4896301 := bstep (se 3 (by rfl) ⟨918056, by rfl⟩ : syracuseStep 4896301 = 1836113) B1836113
theorem B5289623 : Blo 1016603 5289623 := bstep (se 1 (by rfl) ⟨3967217, by rfl⟩ : syracuseStep 5289623 = 7934435) B7934435
theorem B2176715 : Blo 1016603 2176715 := bstep (se 1 (by rfl) ⟨1632536, by rfl⟩ : syracuseStep 2176715 = 3265073) B3265073
theorem B3094451 : Blo 1016603 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B1718219 : Blo 1016603 1718219 := bstep (se 1 (by rfl) ⟨1288664, by rfl⟩ : syracuseStep 1718219 = 2577329) B2577329
theorem B1718347 : Blo 1016603 1718347 := bstep (se 1 (by rfl) ⟨1288760, by rfl⟩ : syracuseStep 1718347 = 2577521) B2577521
theorem B4896899 : Blo 1016603 4896899 := bstep (se 1 (by rfl) ⟨3672674, by rfl⟩ : syracuseStep 4896899 = 7345349) B7345349
theorem B2177227 : Blo 1016603 2177227 := bstep (se 1 (by rfl) ⟨1632920, by rfl⟩ : syracuseStep 2177227 = 3265841) B3265841
theorem B1718489 : Blo 1016603 1718489 := bstep (se 2 (by rfl) ⟨644433, by rfl⟩ : syracuseStep 1718489 = 1288867) B1288867
theorem B3258589 : Blo 1016603 3258589 := bstep (se 3 (by rfl) ⟨610985, by rfl⟩ : syracuseStep 3258589 = 1221971) B1221971
theorem B5159213 : Blo 1016603 5159213 := bstep (se 3 (by rfl) ⟨967352, by rfl⟩ : syracuseStep 5159213 = 1934705) B1934705
theorem B1718617 : Blo 1016603 1718617 := bstep (se 2 (by rfl) ⟨644481, by rfl⟩ : syracuseStep 1718617 = 1288963) B1288963
theorem B8272601 : Blo 1016603 8272601 := bstep (se 2 (by rfl) ⟨3102225, by rfl⟩ : syracuseStep 8272601 = 6204451) B6204451
theorem B1719191 : Blo 1016603 1719191 := bstep (se 1 (by rfl) ⟨1289393, by rfl⟩ : syracuseStep 1719191 = 2578787) B2578787
theorem B2177945 : Blo 1016603 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B1719319 : Blo 1016603 1719319 := bstep (se 1 (by rfl) ⟨1289489, by rfl⟩ : syracuseStep 1719319 = 2578979) B2578979
theorem B1031383 : Blo 1016603 1031383 := bstep (se 1 (by rfl) ⟨773537, by rfl⟩ : syracuseStep 1031383 = 1547075) B1547075
theorem B2899165 : Blo 1016603 2899165 := bstep (se 3 (by rfl) ⟨543593, by rfl⟩ : syracuseStep 2899165 = 1087187) B1087187
theorem B2899223 : Blo 1016603 2899223 := bstep (se 1 (by rfl) ⟨2174417, by rfl⟩ : syracuseStep 2899223 = 4348835) B4348835
theorem B2178355 : Blo 1016603 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B1719947 : Blo 1016603 1719947 := bstep (se 1 (by rfl) ⟨1289960, by rfl⟩ : syracuseStep 1719947 = 2579921) B2579921
theorem B1720075 : Blo 1016603 1720075 := bstep (se 1 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 1720075 = 2580113) B2580113
theorem B1720217 : Blo 1016603 1720217 := bstep (se 2 (by rfl) ⟨645081, by rfl⟩ : syracuseStep 1720217 = 1290163) B1290163
theorem B1720345 : Blo 1016603 1720345 := bstep (se 2 (by rfl) ⟨645129, by rfl⟩ : syracuseStep 1720345 = 1290259) B1290259
theorem B24756293 : Blo 1016603 24756293 := bstep (se 4 (by rfl) ⟨2320902, by rfl⟩ : syracuseStep 24756293 = 4641805) B4641805
theorem B11583809 : Blo 1016603 11583809 := bstep (se 2 (by rfl) ⟨4343928, by rfl⟩ : syracuseStep 11583809 = 8687857) B8687857
theorem B2179543 : Blo 1016603 2179543 := bstep (se 1 (by rfl) ⟨1634657, by rfl⟩ : syracuseStep 2179543 = 3269315) B3269315
theorem B2900441 : Blo 1016603 2900441 := bstep (se 2 (by rfl) ⟨1087665, by rfl⟩ : syracuseStep 2900441 = 2175331) B2175331
theorem B3490265 : Blo 1016603 3490265 := bstep (se 2 (by rfl) ⟨1308849, by rfl⟩ : syracuseStep 3490265 = 2617699) B2617699
theorem B2179585 : Blo 1016603 2179585 := bstep (se 2 (by rfl) ⟨817344, by rfl⟩ : syracuseStep 2179585 = 1634689) B1634689
theorem B2900555 : Blo 1016603 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B1720919 : Blo 1016603 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B1721047 : Blo 1016603 1721047 := bstep (se 1 (by rfl) ⟨1290785, by rfl⟩ : syracuseStep 1721047 = 2581571) B2581571
theorem B1655563 : Blo 1016603 1655563 := bstep (se 1 (by rfl) ⟨1241672, by rfl⟩ : syracuseStep 1655563 = 2483345) B2483345
theorem B6800203 : Blo 1016603 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B4342835 : Blo 1016603 4342835 := bstep (se 1 (by rfl) ⟨3257126, by rfl⟩ : syracuseStep 4342835 = 6514253) B6514253
theorem B3097651 : Blo 1016603 3097651 := bstep (se 1 (by rfl) ⟨2323238, by rfl⟩ : syracuseStep 3097651 = 4646477) B4646477
theorem B2573491 : Blo 1016603 2573491 := bstep (se 1 (by rfl) ⟨1930118, by rfl⟩ : syracuseStep 2573491 = 3860237) B3860237
theorem B4408499 : Blo 1016603 4408499 := bstep (se 1 (by rfl) ⟨3306374, by rfl⟩ : syracuseStep 4408499 = 6612749) B6612749
theorem B1524953 : Blo 1016603 1524953 := bstep (se 2 (by rfl) ⟨571857, by rfl⟩ : syracuseStep 1524953 = 1143715) B1143715
theorem B2573633 : Blo 1016603 2573633 := bstep (se 2 (by rfl) ⟨965112, by rfl⟩ : syracuseStep 2573633 = 1930225) B1930225
theorem B1525067 : Blo 1016603 1525067 := bstep (se 1 (by rfl) ⟨1143800, by rfl⟩ : syracuseStep 1525067 = 2287601) B2287601
theorem B1721675 : Blo 1016603 1721675 := bstep (se 1 (by rfl) ⟨1291256, by rfl⟩ : syracuseStep 1721675 = 2582513) B2582513
theorem B1525079 : Blo 1016603 1525079 := bstep (se 1 (by rfl) ⟨1143809, by rfl⟩ : syracuseStep 1525079 = 2287619) B2287619
theorem B1525145 : Blo 1016603 1525145 := bstep (se 2 (by rfl) ⟨571929, by rfl⟩ : syracuseStep 1525145 = 1143859) B1143859
theorem B1721803 : Blo 1016603 1721803 := bstep (se 1 (by rfl) ⟨1291352, by rfl⟩ : syracuseStep 1721803 = 2582705) B2582705
theorem B1525259 : Blo 1016603 1525259 := bstep (se 1 (by rfl) ⟨1143944, by rfl⟩ : syracuseStep 1525259 = 2287889) B2287889
theorem B1525271 : Blo 1016603 1525271 := bstep (se 1 (by rfl) ⟨1143953, by rfl⟩ : syracuseStep 1525271 = 2287907) B2287907
theorem B1525337 : Blo 1016603 1525337 := bstep (se 2 (by rfl) ⟨572001, by rfl⟩ : syracuseStep 1525337 = 1144003) B1144003
theorem B1721945 : Blo 1016603 1721945 := bstep (se 2 (by rfl) ⟨645729, by rfl⟩ : syracuseStep 1721945 = 1291459) B1291459
theorem B2901683 : Blo 1016603 2901683 := bstep (se 1 (by rfl) ⟨2176262, by rfl⟩ : syracuseStep 2901683 = 4352525) B4352525
theorem B1525451 : Blo 1016603 1525451 := bstep (se 1 (by rfl) ⟨1144088, by rfl⟩ : syracuseStep 1525451 = 2288177) B2288177
theorem B1525463 : Blo 1016603 1525463 := bstep (se 1 (by rfl) ⟨1144097, by rfl⟩ : syracuseStep 1525463 = 2288195) B2288195
theorem B1722073 : Blo 1016603 1722073 := bstep (se 2 (by rfl) ⟨645777, by rfl⟩ : syracuseStep 1722073 = 1291555) B1291555
theorem B1525529 : Blo 1016603 1525529 := bstep (se 2 (by rfl) ⟨572073, by rfl⟩ : syracuseStep 1525529 = 1144147) B1144147
theorem B1525643 : Blo 1016603 1525643 := bstep (se 1 (by rfl) ⟨1144232, by rfl⟩ : syracuseStep 1525643 = 2288465) B2288465
theorem B1525655 : Blo 1016603 1525655 := bstep (se 1 (by rfl) ⟨1144241, by rfl⟩ : syracuseStep 1525655 = 2288483) B2288483
theorem B1525721 : Blo 1016603 1525721 := bstep (se 2 (by rfl) ⟨572145, by rfl⟩ : syracuseStep 1525721 = 1144291) B1144291
theorem B8276003 : Blo 1016603 8276003 := bstep (se 1 (by rfl) ⟨6207002, by rfl⟩ : syracuseStep 8276003 = 12414005) B12414005
theorem B2902081 : Blo 1016603 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B1525835 : Blo 1016603 1525835 := bstep (se 1 (by rfl) ⟨1144376, by rfl⟩ : syracuseStep 1525835 = 2288753) B2288753
theorem B1525847 : Blo 1016603 1525847 := bstep (se 1 (by rfl) ⟨1144385, by rfl⟩ : syracuseStep 1525847 = 2288771) B2288771
theorem B5163101 : Blo 1016603 5163101 := bstep (se 3 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 5163101 = 1936163) B1936163
theorem B1525913 : Blo 1016603 1525913 := bstep (se 2 (by rfl) ⟨572217, by rfl⟩ : syracuseStep 1525913 = 1144435) B1144435
theorem B1526027 : Blo 1016603 1526027 := bstep (se 1 (by rfl) ⟨1144520, by rfl⟩ : syracuseStep 1526027 = 2289041) B2289041
theorem B1526039 : Blo 1016603 1526039 := bstep (se 1 (by rfl) ⟨1144529, by rfl⟩ : syracuseStep 1526039 = 2289059) B2289059
theorem B1526105 : Blo 1016603 1526105 := bstep (se 2 (by rfl) ⟨572289, by rfl⟩ : syracuseStep 1526105 = 1144579) B1144579
theorem B1526219 : Blo 1016603 1526219 := bstep (se 1 (by rfl) ⟨1144664, by rfl⟩ : syracuseStep 1526219 = 2289329) B2289329
theorem B1526231 : Blo 1016603 1526231 := bstep (se 1 (by rfl) ⟨1144673, by rfl⟩ : syracuseStep 1526231 = 2289347) B2289347
theorem B1526297 : Blo 1016603 1526297 := bstep (se 2 (by rfl) ⟨572361, by rfl⟩ : syracuseStep 1526297 = 1144723) B1144723
theorem B2574899 : Blo 1016603 2574899 := bstep (se 1 (by rfl) ⟨1931174, by rfl⟩ : syracuseStep 2574899 = 3862349) B3862349
theorem B1526411 : Blo 1016603 1526411 := bstep (se 1 (by rfl) ⟨1144808, by rfl⟩ : syracuseStep 1526411 = 2289617) B2289617
theorem B1526423 : Blo 1016603 1526423 := bstep (se 1 (by rfl) ⟨1144817, by rfl⟩ : syracuseStep 1526423 = 2289635) B2289635
theorem B1526489 : Blo 1016603 1526489 := bstep (se 2 (by rfl) ⟨572433, by rfl⟩ : syracuseStep 1526489 = 1144867) B1144867
theorem B4180781 : Blo 1016603 4180781 := bstep (se 3 (by rfl) ⟨783896, by rfl⟩ : syracuseStep 4180781 = 1567793) B1567793
theorem B1526603 : Blo 1016603 1526603 := bstep (se 1 (by rfl) ⟨1144952, by rfl⟩ : syracuseStep 1526603 = 2289905) B2289905
theorem B1526615 : Blo 1016603 1526615 := bstep (se 1 (by rfl) ⟨1144961, by rfl⟩ : syracuseStep 1526615 = 2289923) B2289923
theorem B1526681 : Blo 1016603 1526681 := bstep (se 2 (by rfl) ⟨572505, by rfl⟩ : syracuseStep 1526681 = 1145011) B1145011
theorem B4344749 : Blo 1016603 4344749 := bstep (se 3 (by rfl) ⟨814640, by rfl⟩ : syracuseStep 4344749 = 1629281) B1629281
theorem B1526795 : Blo 1016603 1526795 := bstep (se 1 (by rfl) ⟨1145096, by rfl⟩ : syracuseStep 1526795 = 2290193) B2290193
theorem B1526807 : Blo 1016603 1526807 := bstep (se 1 (by rfl) ⟨1145105, by rfl⟩ : syracuseStep 1526807 = 2290211) B2290211
theorem B2575435 : Blo 1016603 2575435 := bstep (se 1 (by rfl) ⟨1931576, by rfl⟩ : syracuseStep 2575435 = 3863153) B3863153
theorem B1789015 : Blo 1016603 1789015 := bstep (se 1 (by rfl) ⟨1341761, by rfl⟩ : syracuseStep 1789015 = 2683523) B2683523
theorem B1526873 : Blo 1016603 1526873 := bstep (se 2 (by rfl) ⟨572577, by rfl⟩ : syracuseStep 1526873 = 1145155) B1145155
theorem B1526987 : Blo 1016603 1526987 := bstep (se 1 (by rfl) ⟨1145240, by rfl⟩ : syracuseStep 1526987 = 2290481) B2290481
theorem B1526999 : Blo 1016603 1526999 := bstep (se 1 (by rfl) ⟨1145249, by rfl⟩ : syracuseStep 1526999 = 2290499) B2290499
theorem B2575577 : Blo 1016603 2575577 := bstep (se 2 (by rfl) ⟨965841, by rfl⟩ : syracuseStep 2575577 = 1931683) B1931683
theorem B14666993 : Blo 1016603 14666993 := bstep (se 2 (by rfl) ⟨5500122, by rfl⟩ : syracuseStep 14666993 = 11000245) B11000245
theorem B1527065 : Blo 1016603 1527065 := bstep (se 2 (by rfl) ⟨572649, by rfl⟩ : syracuseStep 1527065 = 1145299) B1145299
theorem B1527179 : Blo 1016603 1527179 := bstep (se 1 (by rfl) ⟨1145384, by rfl⟩ : syracuseStep 1527179 = 2290769) B2290769
theorem B1527191 : Blo 1016603 1527191 := bstep (se 1 (by rfl) ⟨1145393, by rfl⟩ : syracuseStep 1527191 = 2290787) B2290787
theorem B1527257 : Blo 1016603 1527257 := bstep (se 2 (by rfl) ⟨572721, by rfl⟩ : syracuseStep 1527257 = 1145443) B1145443
theorem B1527371 : Blo 1016603 1527371 := bstep (se 1 (by rfl) ⟨1145528, by rfl⟩ : syracuseStep 1527371 = 2291057) B2291057
theorem B1527383 : Blo 1016603 1527383 := bstep (se 1 (by rfl) ⟨1145537, by rfl⟩ : syracuseStep 1527383 = 2291075) B2291075
theorem B4345433 : Blo 1016603 4345433 := bstep (se 2 (by rfl) ⟨1629537, by rfl⟩ : syracuseStep 4345433 = 3259075) B3259075
theorem B1527449 : Blo 1016603 1527449 := bstep (se 2 (by rfl) ⟨572793, by rfl⟩ : syracuseStep 1527449 = 1145587) B1145587
theorem B1527563 : Blo 1016603 1527563 := bstep (se 1 (by rfl) ⟨1145672, by rfl⟩ : syracuseStep 1527563 = 2291345) B2291345
theorem B1527575 : Blo 1016603 1527575 := bstep (se 1 (by rfl) ⟨1145681, by rfl⟩ : syracuseStep 1527575 = 2291363) B2291363
theorem B1527641 : Blo 1016603 1527641 := bstep (se 2 (by rfl) ⟨572865, by rfl⟩ : syracuseStep 1527641 = 1145731) B1145731
theorem B1527755 : Blo 1016603 1527755 := bstep (se 1 (by rfl) ⟨1145816, by rfl⟩ : syracuseStep 1527755 = 2291633) B2291633
theorem B1527767 : Blo 1016603 1527767 := bstep (se 1 (by rfl) ⟨1145825, by rfl⟩ : syracuseStep 1527767 = 2291651) B2291651
theorem B2576407 : Blo 1016603 2576407 := bstep (se 1 (by rfl) ⟨1932305, by rfl⟩ : syracuseStep 2576407 = 3864611) B3864611
theorem B1527833 : Blo 1016603 1527833 := bstep (se 2 (by rfl) ⟨572937, by rfl⟩ : syracuseStep 1527833 = 1145875) B1145875
theorem B1527947 : Blo 1016603 1527947 := bstep (se 1 (by rfl) ⟨1145960, by rfl⟩ : syracuseStep 1527947 = 2291921) B2291921
theorem B39669911 : Blo 1016603 39669911 := bstep (se 1 (by rfl) ⟨29752433, by rfl⟩ : syracuseStep 39669911 = 59504867) B59504867
theorem B1527959 : Blo 1016603 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B5165207 : Blo 1016603 5165207 := bstep (se 1 (by rfl) ⟨3873905, by rfl⟩ : syracuseStep 5165207 = 7747811) B7747811
theorem B2937035 : Blo 1016603 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B1528025 : Blo 1016603 1528025 := bstep (se 2 (by rfl) ⟨573009, by rfl⟩ : syracuseStep 1528025 = 1146019) B1146019
theorem B22335749 : Blo 1016603 22335749 := bstep (se 4 (by rfl) ⟨2093976, by rfl⟩ : syracuseStep 22335749 = 4187953) B4187953
theorem B1528139 : Blo 1016603 1528139 := bstep (se 1 (by rfl) ⟨1146104, by rfl⟩ : syracuseStep 1528139 = 2292209) B2292209
theorem B1528151 : Blo 1016603 1528151 := bstep (se 1 (by rfl) ⟨1146113, by rfl⟩ : syracuseStep 1528151 = 2292227) B2292227
theorem B1528217 : Blo 1016603 1528217 := bstep (se 2 (by rfl) ⟨573081, by rfl⟩ : syracuseStep 1528217 = 1146163) B1146163
theorem B2576843 : Blo 1016603 2576843 := bstep (se 1 (by rfl) ⟨1932632, by rfl⟩ : syracuseStep 2576843 = 3865265) B3865265
theorem B1528331 : Blo 1016603 1528331 := bstep (se 1 (by rfl) ⟨1146248, by rfl⟩ : syracuseStep 1528331 = 2292497) B2292497
theorem B1528343 : Blo 1016603 1528343 := bstep (se 1 (by rfl) ⟨1146257, by rfl⟩ : syracuseStep 1528343 = 2292515) B2292515
theorem B2904599 : Blo 1016603 2904599 := bstep (se 1 (by rfl) ⟨2178449, by rfl⟩ : syracuseStep 2904599 = 4356899) B4356899
theorem B1528409 : Blo 1016603 1528409 := bstep (se 2 (by rfl) ⟨573153, by rfl⟩ : syracuseStep 1528409 = 1146307) B1146307
theorem B4346561 : Blo 1016603 4346561 := bstep (se 2 (by rfl) ⟨1629960, by rfl⟩ : syracuseStep 4346561 = 3259921) B3259921
theorem B1528523 : Blo 1016603 1528523 := bstep (se 1 (by rfl) ⟨1146392, by rfl⟩ : syracuseStep 1528523 = 2292785) B2292785
theorem B1528535 : Blo 1016603 1528535 := bstep (se 1 (by rfl) ⟨1146401, by rfl⟩ : syracuseStep 1528535 = 2292803) B2292803
theorem B1528601 : Blo 1016603 1528601 := bstep (se 2 (by rfl) ⟨573225, by rfl⟩ : syracuseStep 1528601 = 1146451) B1146451
theorem B2577217 : Blo 1016603 2577217 := bstep (se 2 (by rfl) ⟨966456, by rfl⟩ : syracuseStep 2577217 = 1932913) B1932913
theorem B1528715 : Blo 1016603 1528715 := bstep (se 1 (by rfl) ⟨1146536, by rfl⟩ : syracuseStep 1528715 = 2293073) B2293073
theorem B1528727 : Blo 1016603 1528727 := bstep (se 1 (by rfl) ⟨1146545, by rfl⟩ : syracuseStep 1528727 = 2293091) B2293091
theorem B43996121 : Blo 1016603 43996121 := bstep (se 2 (by rfl) ⟨16498545, by rfl⟩ : syracuseStep 43996121 = 32997091) B32997091
theorem B1528793 : Blo 1016603 1528793 := bstep (se 2 (by rfl) ⟨573297, by rfl⟩ : syracuseStep 1528793 = 1146595) B1146595
theorem B1528907 : Blo 1016603 1528907 := bstep (se 1 (by rfl) ⟨1146680, by rfl⟩ : syracuseStep 1528907 = 2293361) B2293361
theorem B1528919 : Blo 1016603 1528919 := bstep (se 1 (by rfl) ⟨1146689, by rfl⟩ : syracuseStep 1528919 = 2293379) B2293379
theorem B3265687 : Blo 1016603 3265687 := bstep (se 1 (by rfl) ⟨2449265, by rfl⟩ : syracuseStep 3265687 = 4898531) B4898531
theorem B1528985 : Blo 1016603 1528985 := bstep (se 2 (by rfl) ⟨573369, by rfl⟩ : syracuseStep 1528985 = 1146739) B1146739
theorem B1529099 : Blo 1016603 1529099 := bstep (se 1 (by rfl) ⟨1146824, by rfl⟩ : syracuseStep 1529099 = 2293649) B2293649
theorem B1529111 : Blo 1016603 1529111 := bstep (se 1 (by rfl) ⟨1146833, by rfl⟩ : syracuseStep 1529111 = 2293667) B2293667
theorem B1529177 : Blo 1016603 1529177 := bstep (se 2 (by rfl) ⟨573441, by rfl⟩ : syracuseStep 1529177 = 1146883) B1146883
theorem B2577815 : Blo 1016603 2577815 := bstep (se 1 (by rfl) ⟨1933361, by rfl⟩ : syracuseStep 2577815 = 3866723) B3866723
theorem B2119115 : Blo 1016603 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B1529291 : Blo 1016603 1529291 := bstep (se 1 (by rfl) ⟨1146968, by rfl⟩ : syracuseStep 1529291 = 2293937) B2293937
theorem B1529303 : Blo 1016603 1529303 := bstep (se 1 (by rfl) ⟨1146977, by rfl⟩ : syracuseStep 1529303 = 2293955) B2293955
theorem B1529369 : Blo 1016603 1529369 := bstep (se 2 (by rfl) ⟨573513, by rfl⟩ : syracuseStep 1529369 = 1147027) B1147027
theorem B1529483 : Blo 1016603 1529483 := bstep (se 1 (by rfl) ⟨1147112, by rfl⟩ : syracuseStep 1529483 = 2294225) B2294225
theorem B1529495 : Blo 1016603 1529495 := bstep (se 1 (by rfl) ⟨1147121, by rfl⟩ : syracuseStep 1529495 = 2294243) B2294243
theorem B7329457 : Blo 1016603 7329457 := bstep (se 2 (by rfl) ⟨2748546, by rfl⟩ : syracuseStep 7329457 = 5497093) B5497093
theorem B1529561 : Blo 1016603 1529561 := bstep (se 2 (by rfl) ⟨573585, by rfl⟩ : syracuseStep 1529561 = 1147171) B1147171
theorem B1529675 : Blo 1016603 1529675 := bstep (se 1 (by rfl) ⟨1147256, by rfl⟩ : syracuseStep 1529675 = 2294513) B2294513
theorem B2905931 : Blo 1016603 2905931 := bstep (se 1 (by rfl) ⟨2179448, by rfl⟩ : syracuseStep 2905931 = 4358897) B4358897
theorem B1529687 : Blo 1016603 1529687 := bstep (se 1 (by rfl) ⟨1147265, by rfl⟩ : syracuseStep 1529687 = 2294531) B2294531
theorem B1529753 : Blo 1016603 1529753 := bstep (se 2 (by rfl) ⟨573657, by rfl⟩ : syracuseStep 1529753 = 1147315) B1147315
theorem B3266507 : Blo 1016603 3266507 := bstep (se 1 (by rfl) ⟨2449880, by rfl⟩ : syracuseStep 3266507 = 4899761) B4899761
theorem B1529867 : Blo 1016603 1529867 := bstep (se 1 (by rfl) ⟨1147400, by rfl⟩ : syracuseStep 1529867 = 2294801) B2294801
theorem B7723025 : Blo 1016603 7723025 := bstep (se 2 (by rfl) ⟨2896134, by rfl⟩ : syracuseStep 7723025 = 5792269) B5792269
theorem B6969361 : Blo 1016603 6969361 := bstep (se 2 (by rfl) ⟨2613510, by rfl⟩ : syracuseStep 6969361 = 5227021) B5227021
theorem B1529879 : Blo 1016603 1529879 := bstep (se 1 (by rfl) ⟨1147409, by rfl⟩ : syracuseStep 1529879 = 2294819) B2294819
theorem B1529945 : Blo 1016603 1529945 := bstep (se 2 (by rfl) ⟨573729, by rfl⟩ : syracuseStep 1529945 = 1147459) B1147459
theorem B2578625 : Blo 1016603 2578625 := bstep (se 2 (by rfl) ⟨966984, by rfl⟩ : syracuseStep 2578625 = 1933969) B1933969
theorem B1530059 : Blo 1016603 1530059 := bstep (se 1 (by rfl) ⟨1147544, by rfl⟩ : syracuseStep 1530059 = 2295089) B2295089
theorem B1530071 : Blo 1016603 1530071 := bstep (se 1 (by rfl) ⟨1147553, by rfl⟩ : syracuseStep 1530071 = 2295107) B2295107
theorem B1530137 : Blo 1016603 1530137 := bstep (se 2 (by rfl) ⟨573801, by rfl⟩ : syracuseStep 1530137 = 1147603) B1147603
theorem B8247587 : Blo 1016603 8247587 := bstep (se 1 (by rfl) ⟨6185690, by rfl⟩ : syracuseStep 8247587 = 12371381) B12371381
theorem B4348235 : Blo 1016603 4348235 := bstep (se 1 (by rfl) ⟨3261176, by rfl⟩ : syracuseStep 4348235 = 6522353) B6522353
theorem B1530251 : Blo 1016603 1530251 := bstep (se 1 (by rfl) ⟨1147688, by rfl⟩ : syracuseStep 1530251 = 2295377) B2295377
theorem B1530263 : Blo 1016603 1530263 := bstep (se 1 (by rfl) ⟨1147697, by rfl⟩ : syracuseStep 1530263 = 2295395) B2295395
theorem B1530329 : Blo 1016603 1530329 := bstep (se 2 (by rfl) ⟨573873, by rfl⟩ : syracuseStep 1530329 = 1147747) B1147747
theorem B1530443 : Blo 1016603 1530443 := bstep (se 1 (by rfl) ⟨1147832, by rfl⟩ : syracuseStep 1530443 = 2295665) B2295665
theorem B1530455 : Blo 1016603 1530455 := bstep (se 1 (by rfl) ⟨1147841, by rfl⟩ : syracuseStep 1530455 = 2295683) B2295683
theorem B1530521 : Blo 1016603 1530521 := bstep (se 2 (by rfl) ⟨573945, by rfl⟩ : syracuseStep 1530521 = 1147891) B1147891
theorem B3431105 : Blo 1016603 3431105 := bstep (se 2 (by rfl) ⟨1286664, by rfl⟩ : syracuseStep 3431105 = 2573329) B2573329
theorem B2579161 : Blo 1016603 2579161 := bstep (se 2 (by rfl) ⟨967185, by rfl⟩ : syracuseStep 2579161 = 1934371) B1934371
theorem B13032197 : Blo 1016603 13032197 := bstep (se 4 (by rfl) ⟨1221768, by rfl⟩ : syracuseStep 13032197 = 2443537) B2443537
theorem B1530635 : Blo 1016603 1530635 := bstep (se 1 (by rfl) ⟨1147976, by rfl⟩ : syracuseStep 1530635 = 2295953) B2295953
theorem B1530647 : Blo 1016603 1530647 := bstep (se 1 (by rfl) ⟨1147985, by rfl⟩ : syracuseStep 1530647 = 2295971) B2295971
theorem B4414283 : Blo 1016603 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B1530713 : Blo 1016603 1530713 := bstep (se 2 (by rfl) ⟨574017, by rfl⟩ : syracuseStep 1530713 = 1148035) B1148035
theorem B7428995 : Blo 1016603 7428995 := bstep (se 1 (by rfl) ⟨5571746, by rfl⟩ : syracuseStep 7428995 = 11143493) B11143493
theorem B1530827 : Blo 1016603 1530827 := bstep (se 1 (by rfl) ⟨1148120, by rfl⟩ : syracuseStep 1530827 = 2296241) B2296241
theorem B1530839 : Blo 1016603 1530839 := bstep (se 1 (by rfl) ⟨1148129, by rfl⟩ : syracuseStep 1530839 = 2296259) B2296259
theorem B1530905 : Blo 1016603 1530905 := bstep (se 2 (by rfl) ⟨574089, by rfl⟩ : syracuseStep 1530905 = 1148179) B1148179
theorem B5233709 : Blo 1016603 5233709 := bstep (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) B1962641
theorem B6609995 : Blo 1016603 6609995 := bstep (se 1 (by rfl) ⟨4957496, by rfl⟩ : syracuseStep 6609995 = 9914993) B9914993
theorem B2448535 : Blo 1016603 2448535 := bstep (se 1 (by rfl) ⟨1836401, by rfl⟩ : syracuseStep 2448535 = 3672803) B3672803
theorem B3431645 : Blo 1016603 3431645 := bstep (se 3 (by rfl) ⟨643433, by rfl⟩ : syracuseStep 3431645 = 1286867) B1286867
theorem B4349533 : Blo 1016603 4349533 := bstep (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) B1631075
theorem B3268289 : Blo 1016603 3268289 := bstep (se 2 (by rfl) ⟨1225608, by rfl⟩ : syracuseStep 3268289 = 2451217) B2451217
theorem B9297625 : Blo 1016603 9297625 := bstep (se 2 (by rfl) ⟨3486609, by rfl⟩ : syracuseStep 9297625 = 6973219) B6973219
theorem B14868269 : Blo 1016603 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B2580275 : Blo 1016603 2580275 := bstep (se 1 (by rfl) ⟨1935206, by rfl⟩ : syracuseStep 2580275 = 3870413) B3870413
theorem B3137459 : Blo 1016603 3137459 := bstep (se 1 (by rfl) ⟨2353094, by rfl⟩ : syracuseStep 3137459 = 4706189) B4706189
theorem B4349875 : Blo 1016603 4349875 := bstep (se 1 (by rfl) ⟨3262406, by rfl⟩ : syracuseStep 4349875 = 6524813) B6524813
theorem B2580569 : Blo 1016603 2580569 := bstep (se 2 (by rfl) ⟨967713, by rfl⟩ : syracuseStep 2580569 = 1935427) B1935427
theorem B5234867 : Blo 1016603 5234867 := bstep (se 1 (by rfl) ⟨3926150, by rfl⟩ : syracuseStep 5234867 = 7852301) B7852301
theorem B3432779 : Blo 1016603 3432779 := bstep (se 1 (by rfl) ⟨2574584, by rfl⟩ : syracuseStep 3432779 = 5149169) B5149169
theorem B7332227 : Blo 1016603 7332227 := bstep (se 1 (by rfl) ⟨5499170, by rfl⟩ : syracuseStep 7332227 = 10998341) B10998341
theorem B16769549 : Blo 1016603 16769549 := bstep (se 3 (by rfl) ⟨3144290, by rfl⟩ : syracuseStep 16769549 = 6288581) B6288581
theorem B3433049 : Blo 1016603 3433049 := bstep (se 2 (by rfl) ⟨1287393, by rfl⟩ : syracuseStep 3433049 = 2574787) B2574787
theorem B13951693 : Blo 1016603 13951693 := bstep (se 3 (by rfl) ⟨2615942, by rfl⟩ : syracuseStep 13951693 = 5231885) B5231885
theorem B18834221 : Blo 1016603 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B14705509 : Blo 1016603 14705509 := bstep (se 4 (by rfl) ⟨1378641, by rfl⟩ : syracuseStep 14705509 = 2757283) B2757283
theorem B1631191 : Blo 1016603 1631191 := bstep (se 1 (by rfl) ⟨1223393, by rfl⟩ : syracuseStep 1631191 = 2446787) B2446787
theorem B4023371 : Blo 1016603 4023371 := bstep (se 1 (by rfl) ⟨3017528, by rfl⟩ : syracuseStep 4023371 = 6035057) B6035057
theorem B12412055 : Blo 1016603 12412055 := bstep (se 1 (by rfl) ⟨9309041, by rfl⟩ : syracuseStep 12412055 = 18618083) B18618083
theorem B2450611 : Blo 1016603 2450611 := bstep (se 1 (by rfl) ⟨1837958, by rfl⟩ : syracuseStep 2450611 = 3675917) B3675917
theorem B3433751 : Blo 1016603 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B9922009 : Blo 1016603 9922009 := bstep (se 2 (by rfl) ⟨3720753, by rfl⟩ : syracuseStep 9922009 = 7441507) B7441507
theorem B3859933 : Blo 1016603 3859933 := bstep (se 3 (by rfl) ⟨723737, by rfl⟩ : syracuseStep 3859933 = 1447475) B1447475
theorem B1631755 : Blo 1016603 1631755 := bstep (se 1 (by rfl) ⟨1223816, by rfl⟩ : syracuseStep 1631755 = 2447633) B2447633
theorem B1631819 : Blo 1016603 1631819 := bstep (se 1 (by rfl) ⟨1223864, by rfl⟩ : syracuseStep 1631819 = 2447729) B2447729
theorem B2582219 : Blo 1016603 2582219 := bstep (se 1 (by rfl) ⟨1936664, by rfl⟩ : syracuseStep 2582219 = 3873329) B3873329
theorem B2287385 : Blo 1016603 2287385 := bstep (se 2 (by rfl) ⟨857769, by rfl⟩ : syracuseStep 2287385 = 1715539) B1715539
theorem B3434291 : Blo 1016603 3434291 := bstep (se 1 (by rfl) ⟨2575718, by rfl⟩ : syracuseStep 3434291 = 5151437) B5151437
theorem B7726913 : Blo 1016603 7726913 := bstep (se 2 (by rfl) ⟨2897592, by rfl⟩ : syracuseStep 7726913 = 5795185) B5795185
theorem B2287475 : Blo 1016603 2287475 := bstep (se 1 (by rfl) ⟨1715606, by rfl⟩ : syracuseStep 2287475 = 3431213) B3431213
theorem B2287511 : Blo 1016603 2287511 := bstep (se 1 (by rfl) ⟨1715633, by rfl⟩ : syracuseStep 2287511 = 3431267) B3431267
theorem B3434561 : Blo 1016603 3434561 := bstep (se 2 (by rfl) ⟨1287960, by rfl⟩ : syracuseStep 3434561 = 2575921) B2575921
theorem B2287691 : Blo 1016603 2287691 := bstep (se 1 (by rfl) ⟨1715768, by rfl⟩ : syracuseStep 2287691 = 3431537) B3431537
theorem B2287745 : Blo 1016603 2287745 := bstep (se 2 (by rfl) ⟨857904, by rfl⟩ : syracuseStep 2287745 = 1715809) B1715809
theorem B2287961 : Blo 1016603 2287961 := bstep (se 2 (by rfl) ⟨857985, by rfl⟩ : syracuseStep 2287961 = 1715971) B1715971
theorem B2288051 : Blo 1016603 2288051 := bstep (se 1 (by rfl) ⟨1716038, by rfl⟩ : syracuseStep 2288051 = 3432077) B3432077
theorem B2288087 : Blo 1016603 2288087 := bstep (se 1 (by rfl) ⟨1716065, by rfl⟩ : syracuseStep 2288087 = 3432131) B3432131
theorem B1632793 : Blo 1016603 1632793 := bstep (se 2 (by rfl) ⟨612297, by rfl⟩ : syracuseStep 1632793 = 1224595) B1224595
theorem B3435101 : Blo 1016603 3435101 := bstep (se 3 (by rfl) ⟨644081, by rfl⟩ : syracuseStep 3435101 = 1288163) B1288163
theorem B11168387 : Blo 1016603 11168387 := bstep (se 1 (by rfl) ⟨8376290, by rfl⟩ : syracuseStep 11168387 = 16752581) B16752581
theorem B2288267 : Blo 1016603 2288267 := bstep (se 1 (by rfl) ⟨1716200, by rfl⟩ : syracuseStep 2288267 = 3432401) B3432401
theorem B2583191 : Blo 1016603 2583191 := bstep (se 1 (by rfl) ⟨1937393, by rfl⟩ : syracuseStep 2583191 = 3874787) B3874787
theorem B2288321 : Blo 1016603 2288321 := bstep (se 2 (by rfl) ⟨858120, by rfl⟩ : syracuseStep 2288321 = 1716241) B1716241
theorem B3861209 : Blo 1016603 3861209 := bstep (se 2 (by rfl) ⟨1447953, by rfl⟩ : syracuseStep 3861209 = 2895907) B2895907
theorem B1633049 : Blo 1016603 1633049 := bstep (se 2 (by rfl) ⟨612393, by rfl⟩ : syracuseStep 1633049 = 1224787) B1224787
theorem B4123457 : Blo 1016603 4123457 := bstep (se 2 (by rfl) ⟨1546296, by rfl⟩ : syracuseStep 4123457 = 3092593) B3092593
theorem B8711063 : Blo 1016603 8711063 := bstep (se 1 (by rfl) ⟨6533297, by rfl⟩ : syracuseStep 8711063 = 13066595) B13066595
theorem B2288537 : Blo 1016603 2288537 := bstep (se 2 (by rfl) ⟨858201, by rfl⟩ : syracuseStep 2288537 = 1716403) B1716403
theorem B1633241 : Blo 1016603 1633241 := bstep (se 2 (by rfl) ⟨612465, by rfl⟩ : syracuseStep 1633241 = 1224931) B1224931
theorem B2288627 : Blo 1016603 2288627 := bstep (se 1 (by rfl) ⟨1716470, by rfl⟩ : syracuseStep 2288627 = 3432941) B3432941
theorem B2288663 : Blo 1016603 2288663 := bstep (se 1 (by rfl) ⟨1716497, by rfl⟩ : syracuseStep 2288663 = 3432995) B3432995
theorem B2288843 : Blo 1016603 2288843 := bstep (se 1 (by rfl) ⟨1716632, by rfl⟩ : syracuseStep 2288843 = 3433265) B3433265
theorem B2288897 : Blo 1016603 2288897 := bstep (se 2 (by rfl) ⟨858336, by rfl⟩ : syracuseStep 2288897 = 1716673) B1716673
theorem B2289113 : Blo 1016603 2289113 := bstep (se 2 (by rfl) ⟨858417, by rfl⟩ : syracuseStep 2289113 = 1716835) B1716835
theorem B4353497 : Blo 1016603 4353497 := bstep (se 2 (by rfl) ⟨1632561, by rfl⟩ : syracuseStep 4353497 = 3265123) B3265123
theorem B2289203 : Blo 1016603 2289203 := bstep (se 1 (by rfl) ⟨1716902, by rfl⟩ : syracuseStep 2289203 = 3433805) B3433805
theorem B2289239 : Blo 1016603 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B5795459 : Blo 1016603 5795459 := bstep (se 1 (by rfl) ⟨4346594, by rfl⟩ : syracuseStep 5795459 = 8693189) B8693189
theorem B2748107 : Blo 1016603 2748107 := bstep (se 1 (by rfl) ⟨2061080, by rfl⟩ : syracuseStep 2748107 = 4122161) B4122161
theorem B3436235 : Blo 1016603 3436235 := bstep (se 1 (by rfl) ⟨2577176, by rfl⟩ : syracuseStep 3436235 = 5154353) B5154353
theorem B7728857 : Blo 1016603 7728857 := bstep (se 2 (by rfl) ⟨2898321, by rfl⟩ : syracuseStep 7728857 = 5796643) B5796643
theorem B2289419 : Blo 1016603 2289419 := bstep (se 1 (by rfl) ⟨1717064, by rfl⟩ : syracuseStep 2289419 = 3434129) B3434129
theorem B2289473 : Blo 1016603 2289473 := bstep (se 2 (by rfl) ⟨858552, by rfl⟩ : syracuseStep 2289473 = 1717105) B1717105
theorem B3436505 : Blo 1016603 3436505 := bstep (se 2 (by rfl) ⟨1288689, by rfl⟩ : syracuseStep 3436505 = 2577379) B2577379
theorem B2289689 : Blo 1016603 2289689 := bstep (se 2 (by rfl) ⟨858633, by rfl⟩ : syracuseStep 2289689 = 1717267) B1717267
theorem B2748505 : Blo 1016603 2748505 := bstep (se 2 (by rfl) ⟨1030689, by rfl⟩ : syracuseStep 2748505 = 2061379) B2061379
theorem B2289779 : Blo 1016603 2289779 := bstep (se 1 (by rfl) ⟨1717334, by rfl⟩ : syracuseStep 2289779 = 3434669) B3434669
theorem B4124803 : Blo 1016603 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B2289815 : Blo 1016603 2289815 := bstep (se 1 (by rfl) ⟨1717361, by rfl⟩ : syracuseStep 2289815 = 3434723) B3434723
theorem B3862835 : Blo 1016603 3862835 := bstep (se 1 (by rfl) ⟨2897126, by rfl⟩ : syracuseStep 3862835 = 5794253) B5794253
theorem B3862849 : Blo 1016603 3862849 := bstep (se 2 (by rfl) ⟨1448568, by rfl⟩ : syracuseStep 3862849 = 2897137) B2897137
theorem B2289995 : Blo 1016603 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B2290049 : Blo 1016603 2290049 := bstep (se 2 (by rfl) ⟨858768, by rfl⟩ : syracuseStep 2290049 = 1717537) B1717537
theorem B11006387 : Blo 1016603 11006387 := bstep (se 1 (by rfl) ⟨8254790, by rfl⟩ : syracuseStep 11006387 = 16509581) B16509581
theorem B2290265 : Blo 1016603 2290265 := bstep (se 2 (by rfl) ⟨858849, by rfl⟩ : syracuseStep 2290265 = 1717699) B1717699
theorem B3437207 : Blo 1016603 3437207 := bstep (se 1 (by rfl) ⟨2577905, by rfl⟩ : syracuseStep 3437207 = 5155811) B5155811
theorem B2290355 : Blo 1016603 2290355 := bstep (se 1 (by rfl) ⟨1717766, by rfl⟩ : syracuseStep 2290355 = 3435533) B3435533
theorem B2290391 : Blo 1016603 2290391 := bstep (se 1 (by rfl) ⟨1717793, by rfl⟩ : syracuseStep 2290391 = 3435587) B3435587
theorem B2290571 : Blo 1016603 2290571 := bstep (se 1 (by rfl) ⟨1717928, by rfl⟩ : syracuseStep 2290571 = 3435857) B3435857
theorem B2290625 : Blo 1016603 2290625 := bstep (se 2 (by rfl) ⟨858984, by rfl⟩ : syracuseStep 2290625 = 1717969) B1717969
theorem B1143787 : Blo 1016603 1143787 := bstep (se 1 (by rfl) ⟨857840, by rfl⟩ : syracuseStep 1143787 = 1715681) B1715681
theorem B4355137 : Blo 1016603 4355137 := bstep (se 2 (by rfl) ⟨1633176, by rfl⟩ : syracuseStep 4355137 = 3266353) B3266353
theorem B1143895 : Blo 1016603 1143895 := bstep (se 1 (by rfl) ⟨857921, by rfl⟩ : syracuseStep 1143895 = 1715843) B1715843
theorem B11596931 : Blo 1016603 11596931 := bstep (se 1 (by rfl) ⟨8697698, by rfl⟩ : syracuseStep 11596931 = 17395397) B17395397
theorem B2290841 : Blo 1016603 2290841 := bstep (se 2 (by rfl) ⟨859065, by rfl⟩ : syracuseStep 2290841 = 1718131) B1718131
theorem B3437747 : Blo 1016603 3437747 := bstep (se 1 (by rfl) ⟨2578310, by rfl⟩ : syracuseStep 3437747 = 5156621) B5156621
theorem B1930483 : Blo 1016603 1930483 := bstep (se 1 (by rfl) ⟨1447862, by rfl⟩ : syracuseStep 1930483 = 2895725) B2895725
theorem B2290931 : Blo 1016603 2290931 := bstep (se 1 (by rfl) ⟨1718198, by rfl⟩ : syracuseStep 2290931 = 3436397) B3436397
theorem B1144075 : Blo 1016603 1144075 := bstep (se 1 (by rfl) ⟨858056, by rfl⟩ : syracuseStep 1144075 = 1716113) B1716113
theorem B2290967 : Blo 1016603 2290967 := bstep (se 1 (by rfl) ⟨1718225, by rfl⟩ : syracuseStep 2290967 = 3436451) B3436451
theorem B1144183 : Blo 1016603 1144183 := bstep (se 1 (by rfl) ⟨858137, by rfl⟩ : syracuseStep 1144183 = 1716275) B1716275
theorem B2749889 : Blo 1016603 2749889 := bstep (se 2 (by rfl) ⟨1031208, by rfl⟩ : syracuseStep 2749889 = 2062417) B2062417
theorem B3438017 : Blo 1016603 3438017 := bstep (se 2 (by rfl) ⟨1289256, by rfl⟩ : syracuseStep 3438017 = 2578513) B2578513
theorem B2291147 : Blo 1016603 2291147 := bstep (se 1 (by rfl) ⟨1718360, by rfl⟩ : syracuseStep 2291147 = 3436721) B3436721
theorem B1930711 : Blo 1016603 1930711 := bstep (se 1 (by rfl) ⟨1448033, by rfl⟩ : syracuseStep 1930711 = 2896067) B2896067
theorem B2291201 : Blo 1016603 2291201 := bstep (se 2 (by rfl) ⟨859200, by rfl⟩ : syracuseStep 2291201 = 1718401) B1718401
theorem B1144363 : Blo 1016603 1144363 := bstep (se 1 (by rfl) ⟨858272, by rfl⟩ : syracuseStep 1144363 = 1716545) B1716545
theorem B1930817 : Blo 1016603 1930817 := bstep (se 2 (by rfl) ⟨724056, by rfl⟩ : syracuseStep 1930817 = 1448113) B1448113
theorem B12383837 : Blo 1016603 12383837 := bstep (se 3 (by rfl) ⟨2321969, by rfl⟩ : syracuseStep 12383837 = 4643939) B4643939
theorem B1144471 : Blo 1016603 1144471 := bstep (se 1 (by rfl) ⟨858353, by rfl⟩ : syracuseStep 1144471 = 1716707) B1716707
theorem B1930969 : Blo 1016603 1930969 := bstep (se 2 (by rfl) ⟨724113, by rfl⟩ : syracuseStep 1930969 = 1448227) B1448227
theorem B2291417 : Blo 1016603 2291417 := bstep (se 2 (by rfl) ⟨859281, by rfl⟩ : syracuseStep 2291417 = 1718563) B1718563
theorem B6616849 : Blo 1016603 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B2291507 : Blo 1016603 2291507 := bstep (se 1 (by rfl) ⟨1718630, by rfl⟩ : syracuseStep 2291507 = 3437261) B3437261
theorem B4650803 : Blo 1016603 4650803 := bstep (se 1 (by rfl) ⟨3488102, by rfl⟩ : syracuseStep 4650803 = 6976205) B6976205
theorem B1144651 : Blo 1016603 1144651 := bstep (se 1 (by rfl) ⟨858488, by rfl⟩ : syracuseStep 1144651 = 1716977) B1716977
theorem B2291543 : Blo 1016603 2291543 := bstep (se 1 (by rfl) ⟨1718657, by rfl⟩ : syracuseStep 2291543 = 3437315) B3437315
theorem B17430389 : Blo 1016603 17430389 := bstep (se 5 (by rfl) ⟨817049, by rfl⟩ : syracuseStep 17430389 = 1634099) B1634099
theorem B1570699 : Blo 1016603 1570699 := bstep (se 1 (by rfl) ⟨1178024, by rfl⟩ : syracuseStep 1570699 = 2356049) B2356049
theorem B1144759 : Blo 1016603 1144759 := bstep (se 1 (by rfl) ⟨858569, by rfl⟩ : syracuseStep 1144759 = 1717139) B1717139
theorem B3438557 : Blo 1016603 3438557 := bstep (se 3 (by rfl) ⟨644729, by rfl⟩ : syracuseStep 3438557 = 1289459) B1289459
theorem B2291723 : Blo 1016603 2291723 := bstep (se 1 (by rfl) ⟨1718792, by rfl⟩ : syracuseStep 2291723 = 3437585) B3437585
theorem B2291777 : Blo 1016603 2291777 := bstep (se 2 (by rfl) ⟨859416, by rfl⟩ : syracuseStep 2291777 = 1718833) B1718833
theorem B1144939 : Blo 1016603 1144939 := bstep (se 1 (by rfl) ⟨858704, by rfl⟩ : syracuseStep 1144939 = 1717409) B1717409
theorem B3864779 : Blo 1016603 3864779 := bstep (se 1 (by rfl) ⟨2898584, by rfl⟩ : syracuseStep 3864779 = 5797169) B5797169
theorem B9173197 : Blo 1016603 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B13072589 : Blo 1016603 13072589 := bstep (se 3 (by rfl) ⟨2451110, by rfl⟩ : syracuseStep 13072589 = 4902221) B4902221
theorem B1145047 : Blo 1016603 1145047 := bstep (se 1 (by rfl) ⟨858785, by rfl⟩ : syracuseStep 1145047 = 1717571) B1717571
theorem B3864793 : Blo 1016603 3864793 := bstep (se 2 (by rfl) ⟨1449297, by rfl⟩ : syracuseStep 3864793 = 2898595) B2898595
theorem B2291993 : Blo 1016603 2291993 := bstep (se 2 (by rfl) ⟨859497, by rfl⟩ : syracuseStep 2291993 = 1718995) B1718995
theorem B2292083 : Blo 1016603 2292083 := bstep (se 1 (by rfl) ⟨1719062, by rfl⟩ : syracuseStep 2292083 = 3438125) B3438125
theorem B1145227 : Blo 1016603 1145227 := bstep (se 1 (by rfl) ⟨858920, by rfl⟩ : syracuseStep 1145227 = 1717841) B1717841
theorem B2292119 : Blo 1016603 2292119 := bstep (se 1 (by rfl) ⟨1719089, by rfl⟩ : syracuseStep 2292119 = 3438179) B3438179
theorem B13957555 : Blo 1016603 13957555 := bstep (se 1 (by rfl) ⟨10468166, by rfl⟩ : syracuseStep 13957555 = 20936333) B20936333
theorem B1145335 : Blo 1016603 1145335 := bstep (se 1 (by rfl) ⟨859001, by rfl⟩ : syracuseStep 1145335 = 1718003) B1718003
theorem B4356625 : Blo 1016603 4356625 := bstep (se 2 (by rfl) ⟨1633734, by rfl⟩ : syracuseStep 4356625 = 3267469) B3267469
theorem B2292299 : Blo 1016603 2292299 := bstep (se 1 (by rfl) ⟨1719224, by rfl⟩ : syracuseStep 2292299 = 3438449) B3438449
theorem B2292353 : Blo 1016603 2292353 := bstep (se 2 (by rfl) ⟨859632, by rfl⟩ : syracuseStep 2292353 = 1719265) B1719265
theorem B1145515 : Blo 1016603 1145515 := bstep (se 1 (by rfl) ⟨859136, by rfl⟩ : syracuseStep 1145515 = 1718273) B1718273
theorem B3668753 : Blo 1016603 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B1145623 : Blo 1016603 1145623 := bstep (se 1 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 1145623 = 1718435) B1718435
theorem B2292569 : Blo 1016603 2292569 := bstep (se 2 (by rfl) ⟨859713, by rfl⟩ : syracuseStep 2292569 = 1719427) B1719427
theorem B3668881 : Blo 1016603 3668881 := bstep (se 2 (by rfl) ⟨1375830, by rfl⟩ : syracuseStep 3668881 = 2751661) B2751661
theorem B2292659 : Blo 1016603 2292659 := bstep (se 1 (by rfl) ⟨1719494, by rfl⟩ : syracuseStep 2292659 = 3438989) B3438989
theorem B1145803 : Blo 1016603 1145803 := bstep (se 1 (by rfl) ⟨859352, by rfl⟩ : syracuseStep 1145803 = 1718705) B1718705
theorem B2292695 : Blo 1016603 2292695 := bstep (se 1 (by rfl) ⟨1719521, by rfl⟩ : syracuseStep 2292695 = 3439043) B3439043
theorem B1932275 : Blo 1016603 1932275 := bstep (se 1 (by rfl) ⟨1449206, by rfl⟩ : syracuseStep 1932275 = 2898413) B2898413
theorem B7732259 : Blo 1016603 7732259 := bstep (se 1 (by rfl) ⟨5799194, by rfl⟩ : syracuseStep 7732259 = 11598389) B11598389
theorem B1145911 : Blo 1016603 1145911 := bstep (se 1 (by rfl) ⟨859433, by rfl⟩ : syracuseStep 1145911 = 1718867) B1718867
theorem B7076929 : Blo 1016603 7076929 := bstep (se 2 (by rfl) ⟨2653848, by rfl⟩ : syracuseStep 7076929 = 5307697) B5307697
theorem B3439691 : Blo 1016603 3439691 := bstep (se 1 (by rfl) ⟨2579768, by rfl⟩ : syracuseStep 3439691 = 5159537) B5159537
theorem B6290507 : Blo 1016603 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B1932427 : Blo 1016603 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B2292875 : Blo 1016603 2292875 := bstep (se 1 (by rfl) ⟨1719656, by rfl⟩ : syracuseStep 2292875 = 3439313) B3439313
theorem B3865751 : Blo 1016603 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B2292929 : Blo 1016603 2292929 := bstep (se 2 (by rfl) ⟨859848, by rfl⟩ : syracuseStep 2292929 = 1719697) B1719697
theorem B2325721 : Blo 1016603 2325721 := bstep (se 2 (by rfl) ⟨872145, by rfl⟩ : syracuseStep 2325721 = 1744291) B1744291
theorem B1146091 : Blo 1016603 1146091 := bstep (se 1 (by rfl) ⟨859568, by rfl⟩ : syracuseStep 1146091 = 1719137) B1719137
theorem B1146199 : Blo 1016603 1146199 := bstep (se 1 (by rfl) ⟨859649, by rfl⟩ : syracuseStep 1146199 = 1719299) B1719299
theorem B3439961 : Blo 1016603 3439961 := bstep (se 2 (by rfl) ⟨1289985, by rfl⟩ : syracuseStep 3439961 = 2579971) B2579971
theorem B2293145 : Blo 1016603 2293145 := bstep (se 2 (by rfl) ⟨859929, by rfl⟩ : syracuseStep 2293145 = 1719859) B1719859
theorem B1146295 : Blo 1016603 1146295 := bstep (se 1 (by rfl) ⟨859721, by rfl⟩ : syracuseStep 1146295 = 1719443) B1719443
theorem B1932761 : Blo 1016603 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B2293235 : Blo 1016603 2293235 := bstep (se 1 (by rfl) ⟨1719926, by rfl⟩ : syracuseStep 2293235 = 3439853) B3439853
theorem B1146379 : Blo 1016603 1146379 := bstep (se 1 (by rfl) ⟨859784, by rfl⟩ : syracuseStep 1146379 = 1719569) B1719569
theorem B2293271 : Blo 1016603 2293271 := bstep (se 1 (by rfl) ⟨1719953, by rfl⟩ : syracuseStep 2293271 = 3439907) B3439907
theorem B9797213 : Blo 1016603 9797213 := bstep (se 3 (by rfl) ⟨1836977, by rfl⟩ : syracuseStep 9797213 = 3673955) B3673955
theorem B1146487 : Blo 1016603 1146487 := bstep (se 1 (by rfl) ⟨859865, by rfl⟩ : syracuseStep 1146487 = 1719731) B1719731
theorem B2293451 : Blo 1016603 2293451 := bstep (se 1 (by rfl) ⟨1720088, by rfl⟩ : syracuseStep 2293451 = 3440177) B3440177
theorem B2293505 : Blo 1016603 2293505 := bstep (se 2 (by rfl) ⟨860064, by rfl⟩ : syracuseStep 2293505 = 1720129) B1720129
theorem B1146667 : Blo 1016603 1146667 := bstep (se 1 (by rfl) ⟨860000, by rfl⟩ : syracuseStep 1146667 = 1720001) B1720001
theorem B2064217 : Blo 1016603 2064217 := bstep (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) B1548163
theorem B5504861 : Blo 1016603 5504861 := bstep (se 3 (by rfl) ⟨1032161, by rfl⟩ : syracuseStep 5504861 = 2064323) B2064323
theorem B1146775 : Blo 1016603 1146775 := bstep (se 1 (by rfl) ⟨860081, by rfl⟩ : syracuseStep 1146775 = 1720163) B1720163
theorem B2293721 : Blo 1016603 2293721 := bstep (se 2 (by rfl) ⟨860145, by rfl⟩ : syracuseStep 2293721 = 1720291) B1720291
theorem B1376263 : Blo 1016603 1376263 := bstep (se 1 (by rfl) ⟨1032197, by rfl⟩ : syracuseStep 1376263 = 2064395) B2064395
theorem B1048583 : Blo 1016603 1048583 := bstep (se 1 (by rfl) ⟨786437, by rfl⟩ : syracuseStep 1048583 = 1572875) B1572875
theorem B2293775 : Blo 1016603 2293775 := bstep (se 1 (by rfl) ⟨1720331, by rfl⟩ : syracuseStep 2293775 = 3440663) B3440663
theorem B2293793 : Blo 1016603 2293793 := bstep (se 2 (by rfl) ⟨860172, by rfl⟩ : syracuseStep 2293793 = 1720345) B1720345
theorem B1933627 : Blo 1016603 1933627 := bstep (se 1 (by rfl) ⟨1450220, by rfl⟩ : syracuseStep 1933627 = 2900441) B2900441
theorem B2326843 : Blo 1016603 2326843 := bstep (se 1 (by rfl) ⟨1745132, by rfl⟩ : syracuseStep 2326843 = 3490265) B3490265
theorem B2294135 : Blo 1016603 2294135 := bstep (se 1 (by rfl) ⟨1720601, by rfl⟩ : syracuseStep 2294135 = 3441203) B3441203
theorem B1933703 : Blo 1016603 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B1147279 : Blo 1016603 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B11010451 : Blo 1016603 11010451 := bstep (se 1 (by rfl) ⟨8257838, by rfl⟩ : syracuseStep 11010451 = 16515677) B16515677
theorem B2294315 : Blo 1016603 2294315 := bstep (se 1 (by rfl) ⟨1720736, by rfl⟩ : syracuseStep 2294315 = 3441473) B3441473
theorem B3867223 : Blo 1016603 3867223 := bstep (se 1 (by rfl) ⟨2900417, by rfl⟩ : syracuseStep 3867223 = 5800835) B5800835
theorem B1934113 : Blo 1016603 1934113 := bstep (se 2 (by rfl) ⟨725292, by rfl⟩ : syracuseStep 1934113 = 1450585) B1450585
theorem B1016635 : Blo 1016603 1016635 := bstep (se 1 (by rfl) ⟨762476, by rfl⟩ : syracuseStep 1016635 = 1524953) B1524953
theorem B1016711 : Blo 1016603 1016711 := bstep (se 1 (by rfl) ⟨762533, by rfl⟩ : syracuseStep 1016711 = 1525067) B1525067
theorem B3867527 : Blo 1016603 3867527 := bstep (se 1 (by rfl) ⟨2900645, by rfl⟩ : syracuseStep 3867527 = 5801291) B5801291
theorem B1147783 : Blo 1016603 1147783 := bstep (se 1 (by rfl) ⟨860837, by rfl⟩ : syracuseStep 1147783 = 1721675) B1721675
theorem B1016719 : Blo 1016603 1016719 := bstep (se 1 (by rfl) ⟨762539, by rfl⟩ : syracuseStep 1016719 = 1525079) B1525079
theorem B2294675 : Blo 1016603 2294675 := bstep (se 1 (by rfl) ⟨1721006, by rfl⟩ : syracuseStep 2294675 = 3442013) B3442013
theorem B1016763 : Blo 1016603 1016763 := bstep (se 1 (by rfl) ⟨762572, by rfl⟩ : syracuseStep 1016763 = 1525145) B1525145
theorem B2294729 : Blo 1016603 2294729 := bstep (se 2 (by rfl) ⟨860523, by rfl⟩ : syracuseStep 2294729 = 1721047) B1721047
theorem B1016839 : Blo 1016603 1016839 := bstep (se 1 (by rfl) ⟨762629, by rfl⟩ : syracuseStep 1016839 = 1525259) B1525259
theorem B1016847 : Blo 1016603 1016847 := bstep (se 1 (by rfl) ⟨762635, by rfl⟩ : syracuseStep 1016847 = 1525271) B1525271
theorem B1016891 : Blo 1016603 1016891 := bstep (se 1 (by rfl) ⟨762668, by rfl⟩ : syracuseStep 1016891 = 1525337) B1525337
theorem B1147963 : Blo 1016603 1147963 := bstep (se 1 (by rfl) ⟨860972, by rfl⟩ : syracuseStep 1147963 = 1721945) B1721945
theorem B3867709 : Blo 1016603 3867709 := bstep (se 3 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 3867709 = 1450391) B1450391
theorem B1934455 : Blo 1016603 1934455 := bstep (se 1 (by rfl) ⟨1450841, by rfl⟩ : syracuseStep 1934455 = 2901683) B2901683
theorem B1016967 : Blo 1016603 1016967 := bstep (se 1 (by rfl) ⟨762725, by rfl⟩ : syracuseStep 1016967 = 1525451) B1525451
theorem B1016975 : Blo 1016603 1016975 := bstep (se 1 (by rfl) ⟨762731, by rfl⟩ : syracuseStep 1016975 = 1525463) B1525463
theorem B1017019 : Blo 1016603 1017019 := bstep (se 1 (by rfl) ⟨762764, by rfl⟩ : syracuseStep 1017019 = 1525529) B1525529
theorem B1017095 : Blo 1016603 1017095 := bstep (se 1 (by rfl) ⟨762821, by rfl⟩ : syracuseStep 1017095 = 1525643) B1525643
theorem B1017103 : Blo 1016603 1017103 := bstep (se 1 (by rfl) ⟨762827, by rfl⟩ : syracuseStep 1017103 = 1525655) B1525655
theorem B1017147 : Blo 1016603 1017147 := bstep (se 1 (by rfl) ⟨762860, by rfl⟩ : syracuseStep 1017147 = 1525721) B1525721
theorem B1017223 : Blo 1016603 1017223 := bstep (se 1 (by rfl) ⟨762917, by rfl⟩ : syracuseStep 1017223 = 1525835) B1525835
theorem B1017231 : Blo 1016603 1017231 := bstep (se 1 (by rfl) ⟨762923, by rfl⟩ : syracuseStep 1017231 = 1525847) B1525847
theorem B3442067 : Blo 1016603 3442067 := bstep (se 1 (by rfl) ⟨2581550, by rfl⟩ : syracuseStep 3442067 = 5163101) B5163101
theorem B4130201 : Blo 1016603 4130201 := bstep (se 2 (by rfl) ⟨1548825, by rfl⟩ : syracuseStep 4130201 = 3097651) B3097651
theorem B1017275 : Blo 1016603 1017275 := bstep (se 1 (by rfl) ⟨762956, by rfl⟩ : syracuseStep 1017275 = 1525913) B1525913
theorem B1017351 : Blo 1016603 1017351 := bstep (se 1 (by rfl) ⟨763013, by rfl⟩ : syracuseStep 1017351 = 1526027) B1526027
theorem B3671563 : Blo 1016603 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B1017359 : Blo 1016603 1017359 := bstep (se 1 (by rfl) ⟨763019, by rfl⟩ : syracuseStep 1017359 = 1526039) B1526039
theorem B4130347 : Blo 1016603 4130347 := bstep (se 1 (by rfl) ⟨3097760, by rfl⟩ : syracuseStep 4130347 = 6195521) B6195521
theorem B1017403 : Blo 1016603 1017403 := bstep (se 1 (by rfl) ⟨763052, by rfl⟩ : syracuseStep 1017403 = 1526105) B1526105
theorem B1017479 : Blo 1016603 1017479 := bstep (se 1 (by rfl) ⟨763109, by rfl⟩ : syracuseStep 1017479 = 1526219) B1526219
theorem B2295431 : Blo 1016603 2295431 := bstep (se 1 (by rfl) ⟨1721573, by rfl⟩ : syracuseStep 2295431 = 3443147) B3443147
theorem B1017487 : Blo 1016603 1017487 := bstep (se 1 (by rfl) ⟨763115, by rfl⟩ : syracuseStep 1017487 = 1526231) B1526231
theorem B1017531 : Blo 1016603 1017531 := bstep (se 1 (by rfl) ⟨763148, by rfl⟩ : syracuseStep 1017531 = 1526297) B1526297
theorem B1017607 : Blo 1016603 1017607 := bstep (se 1 (by rfl) ⟨763205, by rfl⟩ : syracuseStep 1017607 = 1526411) B1526411
theorem B1017615 : Blo 1016603 1017615 := bstep (se 1 (by rfl) ⟨763211, by rfl⟩ : syracuseStep 1017615 = 1526423) B1526423
theorem B1017659 : Blo 1016603 1017659 := bstep (se 1 (by rfl) ⟨763244, by rfl⟩ : syracuseStep 1017659 = 1526489) B1526489
theorem B2295611 : Blo 1016603 2295611 := bstep (se 1 (by rfl) ⟨1721708, by rfl⟩ : syracuseStep 2295611 = 3443417) B3443417
theorem B6522713 : Blo 1016603 6522713 := bstep (se 2 (by rfl) ⟨2446017, by rfl⟩ : syracuseStep 6522713 = 4892035) B4892035
theorem B1017735 : Blo 1016603 1017735 := bstep (se 1 (by rfl) ⟨763301, by rfl⟩ : syracuseStep 1017735 = 1526603) B1526603
theorem B1017743 : Blo 1016603 1017743 := bstep (se 1 (by rfl) ⟨763307, by rfl⟩ : syracuseStep 1017743 = 1526615) B1526615
theorem B2295737 : Blo 1016603 2295737 := bstep (se 2 (by rfl) ⟨860901, by rfl⟩ : syracuseStep 2295737 = 1721803) B1721803
theorem B1017787 : Blo 1016603 1017787 := bstep (se 1 (by rfl) ⟨763340, by rfl⟩ : syracuseStep 1017787 = 1526681) B1526681
theorem B5146577 : Blo 1016603 5146577 := bstep (se 2 (by rfl) ⟨1929966, by rfl⟩ : syracuseStep 5146577 = 3859933) B3859933
theorem B1017863 : Blo 1016603 1017863 := bstep (se 1 (by rfl) ⟨763397, by rfl⟩ : syracuseStep 1017863 = 1526795) B1526795
theorem B1017871 : Blo 1016603 1017871 := bstep (se 1 (by rfl) ⟨763403, by rfl⟩ : syracuseStep 1017871 = 1526807) B1526807
theorem B1017915 : Blo 1016603 1017915 := bstep (se 1 (by rfl) ⟨763436, by rfl⟩ : syracuseStep 1017915 = 1526873) B1526873
theorem B1017991 : Blo 1016603 1017991 := bstep (se 1 (by rfl) ⟨763493, by rfl⟩ : syracuseStep 1017991 = 1526987) B1526987
theorem B1017999 : Blo 1016603 1017999 := bstep (se 1 (by rfl) ⟨763499, by rfl⟩ : syracuseStep 1017999 = 1526999) B1526999
theorem B1018043 : Blo 1016603 1018043 := bstep (se 1 (by rfl) ⟨763532, by rfl⟩ : syracuseStep 1018043 = 1527065) B1527065
theorem B1018119 : Blo 1016603 1018119 := bstep (se 1 (by rfl) ⟨763589, by rfl⟩ : syracuseStep 1018119 = 1527179) B1527179
theorem B1018127 : Blo 1016603 1018127 := bstep (se 1 (by rfl) ⟨763595, by rfl⟩ : syracuseStep 1018127 = 1527191) B1527191
theorem B2296079 : Blo 1016603 2296079 := bstep (se 1 (by rfl) ⟨1722059, by rfl⟩ : syracuseStep 2296079 = 3444119) B3444119
theorem B2296097 : Blo 1016603 2296097 := bstep (se 2 (by rfl) ⟨861036, by rfl⟩ : syracuseStep 2296097 = 1722073) B1722073
theorem B1018171 : Blo 1016603 1018171 := bstep (se 1 (by rfl) ⟨763628, by rfl⟩ : syracuseStep 1018171 = 1527257) B1527257
theorem B1018247 : Blo 1016603 1018247 := bstep (se 1 (by rfl) ⟨763685, by rfl⟩ : syracuseStep 1018247 = 1527371) B1527371
theorem B1018255 : Blo 1016603 1018255 := bstep (se 1 (by rfl) ⟨763691, by rfl⟩ : syracuseStep 1018255 = 1527383) B1527383
theorem B1018299 : Blo 1016603 1018299 := bstep (se 1 (by rfl) ⟨763724, by rfl⟩ : syracuseStep 1018299 = 1527449) B1527449
theorem B1018375 : Blo 1016603 1018375 := bstep (se 1 (by rfl) ⟨763781, by rfl⟩ : syracuseStep 1018375 = 1527563) B1527563
theorem B1018383 : Blo 1016603 1018383 := bstep (se 1 (by rfl) ⟨763787, by rfl⟩ : syracuseStep 1018383 = 1527575) B1527575
theorem B1018427 : Blo 1016603 1018427 := bstep (se 1 (by rfl) ⟨763820, by rfl⟩ : syracuseStep 1018427 = 1527641) B1527641
theorem B2689595 : Blo 1016603 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B1018503 : Blo 1016603 1018503 := bstep (se 1 (by rfl) ⟨763877, by rfl⟩ : syracuseStep 1018503 = 1527755) B1527755
theorem B1018511 : Blo 1016603 1018511 := bstep (se 1 (by rfl) ⟨763883, by rfl⟩ : syracuseStep 1018511 = 1527767) B1527767
theorem B1936057 : Blo 1016603 1936057 := bstep (se 2 (by rfl) ⟨726021, by rfl⟩ : syracuseStep 1936057 = 1452043) B1452043
theorem B1018555 : Blo 1016603 1018555 := bstep (se 1 (by rfl) ⟨763916, by rfl⟩ : syracuseStep 1018555 = 1527833) B1527833
theorem B3869441 : Blo 1016603 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B1018631 : Blo 1016603 1018631 := bstep (se 1 (by rfl) ⟨763973, by rfl⟩ : syracuseStep 1018631 = 1527947) B1527947
theorem B26446607 : Blo 1016603 26446607 := bstep (se 1 (by rfl) ⟨19834955, by rfl⟩ : syracuseStep 26446607 = 39669911) B39669911
theorem B1018639 : Blo 1016603 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B3443471 : Blo 1016603 3443471 := bstep (se 1 (by rfl) ⟨2582603, by rfl⟩ : syracuseStep 3443471 = 5165207) B5165207
theorem B6523685 : Blo 1016603 6523685 := bstep (se 4 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 6523685 = 1223191) B1223191
theorem B1018683 : Blo 1016603 1018683 := bstep (se 1 (by rfl) ⟨764012, by rfl⟩ : syracuseStep 1018683 = 1528025) B1528025
theorem B4131643 : Blo 1016603 4131643 := bstep (se 1 (by rfl) ⟨3098732, by rfl⟩ : syracuseStep 4131643 = 6197465) B6197465
theorem B11602763 : Blo 1016603 11602763 := bstep (se 1 (by rfl) ⟨8702072, by rfl⟩ : syracuseStep 11602763 = 17404145) B17404145
theorem B1018759 : Blo 1016603 1018759 := bstep (se 1 (by rfl) ⟨764069, by rfl⟩ : syracuseStep 1018759 = 1528139) B1528139
theorem B1018767 : Blo 1016603 1018767 := bstep (se 1 (by rfl) ⟨764075, by rfl⟩ : syracuseStep 1018767 = 1528151) B1528151
theorem B1018811 : Blo 1016603 1018811 := bstep (se 1 (by rfl) ⟨764108, by rfl⟩ : syracuseStep 1018811 = 1528217) B1528217
theorem B1018887 : Blo 1016603 1018887 := bstep (se 1 (by rfl) ⟨764165, by rfl⟩ : syracuseStep 1018887 = 1528331) B1528331
theorem B1018895 : Blo 1016603 1018895 := bstep (se 1 (by rfl) ⟨764171, by rfl⟩ : syracuseStep 1018895 = 1528343) B1528343
theorem B1936399 : Blo 1016603 1936399 := bstep (se 1 (by rfl) ⟨1452299, by rfl⟩ : syracuseStep 1936399 = 2904599) B2904599
theorem B3443741 : Blo 1016603 3443741 := bstep (se 3 (by rfl) ⟨645701, by rfl⟩ : syracuseStep 3443741 = 1291403) B1291403
theorem B1018939 : Blo 1016603 1018939 := bstep (se 1 (by rfl) ⟨764204, by rfl⟩ : syracuseStep 1018939 = 1528409) B1528409
theorem B1019015 : Blo 1016603 1019015 := bstep (se 1 (by rfl) ⟨764261, by rfl⟩ : syracuseStep 1019015 = 1528523) B1528523
theorem B1019023 : Blo 1016603 1019023 := bstep (se 1 (by rfl) ⟨764267, by rfl⟩ : syracuseStep 1019023 = 1528535) B1528535
theorem B1019067 : Blo 1016603 1019067 := bstep (se 1 (by rfl) ⟨764300, by rfl⟩ : syracuseStep 1019067 = 1528601) B1528601
theorem B1019143 : Blo 1016603 1019143 := bstep (se 1 (by rfl) ⟨764357, by rfl⟩ : syracuseStep 1019143 = 1528715) B1528715
theorem B1019151 : Blo 1016603 1019151 := bstep (se 1 (by rfl) ⟨764363, by rfl⟩ : syracuseStep 1019151 = 1528727) B1528727
theorem B29330747 : Blo 1016603 29330747 := bstep (se 1 (by rfl) ⟨21998060, by rfl⟩ : syracuseStep 29330747 = 43996121) B43996121
theorem B1019195 : Blo 1016603 1019195 := bstep (se 1 (by rfl) ⟨764396, by rfl⟩ : syracuseStep 1019195 = 1528793) B1528793
theorem B1019271 : Blo 1016603 1019271 := bstep (se 1 (by rfl) ⟨764453, by rfl⟩ : syracuseStep 1019271 = 1528907) B1528907
theorem B1019279 : Blo 1016603 1019279 := bstep (se 1 (by rfl) ⟨764459, by rfl⟩ : syracuseStep 1019279 = 1528919) B1528919
theorem B1019323 : Blo 1016603 1019323 := bstep (se 1 (by rfl) ⟨764492, by rfl⟩ : syracuseStep 1019323 = 1528985) B1528985
theorem B1019399 : Blo 1016603 1019399 := bstep (se 1 (by rfl) ⟨764549, by rfl⟩ : syracuseStep 1019399 = 1529099) B1529099
theorem B1019407 : Blo 1016603 1019407 := bstep (se 1 (by rfl) ⟨764555, by rfl⟩ : syracuseStep 1019407 = 1529111) B1529111
theorem B2231867 : Blo 1016603 2231867 := bstep (se 1 (by rfl) ⟨1673900, by rfl⟩ : syracuseStep 2231867 = 3347801) B3347801
theorem B1019451 : Blo 1016603 1019451 := bstep (se 1 (by rfl) ⟨764588, by rfl⟩ : syracuseStep 1019451 = 1529177) B1529177
theorem B1019527 : Blo 1016603 1019527 := bstep (se 1 (by rfl) ⟨764645, by rfl⟩ : syracuseStep 1019527 = 1529291) B1529291
theorem B1412743 : Blo 1016603 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B1019535 : Blo 1016603 1019535 := bstep (se 1 (by rfl) ⟨764651, by rfl⟩ : syracuseStep 1019535 = 1529303) B1529303
theorem B1019579 : Blo 1016603 1019579 := bstep (se 1 (by rfl) ⟨764684, by rfl⟩ : syracuseStep 1019579 = 1529369) B1529369
theorem B5869313 : Blo 1016603 5869313 := bstep (se 2 (by rfl) ⟨2200992, by rfl⟩ : syracuseStep 5869313 = 4401985) B4401985
theorem B1019655 : Blo 1016603 1019655 := bstep (se 1 (by rfl) ⟨764741, by rfl⟩ : syracuseStep 1019655 = 1529483) B1529483
theorem B1019663 : Blo 1016603 1019663 := bstep (se 1 (by rfl) ⟨764747, by rfl⟩ : syracuseStep 1019663 = 1529495) B1529495
theorem B1019707 : Blo 1016603 1019707 := bstep (se 1 (by rfl) ⟨764780, by rfl⟩ : syracuseStep 1019707 = 1529561) B1529561
theorem B1019783 : Blo 1016603 1019783 := bstep (se 1 (by rfl) ⟨764837, by rfl⟩ : syracuseStep 1019783 = 1529675) B1529675
theorem B1937287 : Blo 1016603 1937287 := bstep (se 1 (by rfl) ⟨1452965, by rfl⟩ : syracuseStep 1937287 = 2905931) B2905931
theorem B1019791 : Blo 1016603 1019791 := bstep (se 1 (by rfl) ⟨764843, by rfl⟩ : syracuseStep 1019791 = 1529687) B1529687
theorem B3870611 : Blo 1016603 3870611 := bstep (se 1 (by rfl) ⟨2902958, by rfl⟩ : syracuseStep 3870611 = 5805917) B5805917
theorem B1019835 : Blo 1016603 1019835 := bstep (se 1 (by rfl) ⟨764876, by rfl⟩ : syracuseStep 1019835 = 1529753) B1529753
theorem B1019911 : Blo 1016603 1019911 := bstep (se 1 (by rfl) ⟨764933, by rfl⟩ : syracuseStep 1019911 = 1529867) B1529867
theorem B5148683 : Blo 1016603 5148683 := bstep (se 1 (by rfl) ⟨3861512, by rfl⟩ : syracuseStep 5148683 = 7723025) B7723025
theorem B1019919 : Blo 1016603 1019919 := bstep (se 1 (by rfl) ⟨764939, by rfl⟩ : syracuseStep 1019919 = 1529879) B1529879
theorem B1019963 : Blo 1016603 1019963 := bstep (se 1 (by rfl) ⟨764972, by rfl⟩ : syracuseStep 1019963 = 1529945) B1529945
theorem B1020039 : Blo 1016603 1020039 := bstep (se 1 (by rfl) ⟨765029, by rfl⟩ : syracuseStep 1020039 = 1530059) B1530059
theorem B1020047 : Blo 1016603 1020047 := bstep (se 1 (by rfl) ⟨765035, by rfl⟩ : syracuseStep 1020047 = 1530071) B1530071
theorem B5148845 : Blo 1016603 5148845 := bstep (se 3 (by rfl) ⟨965408, by rfl⟩ : syracuseStep 5148845 = 1930817) B1930817
theorem B1020091 : Blo 1016603 1020091 := bstep (se 1 (by rfl) ⟨765068, by rfl⟩ : syracuseStep 1020091 = 1530137) B1530137
theorem B1020167 : Blo 1016603 1020167 := bstep (se 1 (by rfl) ⟨765125, by rfl⟩ : syracuseStep 1020167 = 1530251) B1530251
theorem B1020175 : Blo 1016603 1020175 := bstep (se 1 (by rfl) ⟨765131, by rfl⟩ : syracuseStep 1020175 = 1530263) B1530263
theorem B1020219 : Blo 1016603 1020219 := bstep (se 1 (by rfl) ⟨765164, by rfl⟩ : syracuseStep 1020219 = 1530329) B1530329
theorem B3871111 : Blo 1016603 3871111 := bstep (se 1 (by rfl) ⟨2903333, by rfl⟩ : syracuseStep 3871111 = 5806667) B5806667
theorem B1020295 : Blo 1016603 1020295 := bstep (se 1 (by rfl) ⟨765221, by rfl⟩ : syracuseStep 1020295 = 1530443) B1530443
theorem B1020303 : Blo 1016603 1020303 := bstep (se 1 (by rfl) ⟨765227, by rfl⟩ : syracuseStep 1020303 = 1530455) B1530455
theorem B1020347 : Blo 1016603 1020347 := bstep (se 1 (by rfl) ⟨765260, by rfl⟩ : syracuseStep 1020347 = 1530521) B1530521
theorem B8688131 : Blo 1016603 8688131 := bstep (se 1 (by rfl) ⟨6516098, by rfl⟩ : syracuseStep 8688131 = 13032197) B13032197
theorem B1020423 : Blo 1016603 1020423 := bstep (se 1 (by rfl) ⟨765317, by rfl⟩ : syracuseStep 1020423 = 1530635) B1530635
theorem B1020431 : Blo 1016603 1020431 := bstep (se 1 (by rfl) ⟨765323, by rfl⟩ : syracuseStep 1020431 = 1530647) B1530647
theorem B59609621 : Blo 1016603 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B1020475 : Blo 1016603 1020475 := bstep (se 1 (by rfl) ⟨765356, by rfl⟩ : syracuseStep 1020475 = 1530713) B1530713
theorem B4952663 : Blo 1016603 4952663 := bstep (se 1 (by rfl) ⟨3714497, by rfl⟩ : syracuseStep 4952663 = 7428995) B7428995
theorem B1020551 : Blo 1016603 1020551 := bstep (se 1 (by rfl) ⟨765413, by rfl⟩ : syracuseStep 1020551 = 1530827) B1530827
theorem B1020559 : Blo 1016603 1020559 := bstep (se 1 (by rfl) ⟨765419, by rfl⟩ : syracuseStep 1020559 = 1530839) B1530839
theorem B1020603 : Blo 1016603 1020603 := bstep (se 1 (by rfl) ⟨765452, by rfl⟩ : syracuseStep 1020603 = 1530905) B1530905
theorem B9803213 : Blo 1016603 9803213 := bstep (se 3 (by rfl) ⟨1838102, by rfl⟩ : syracuseStep 9803213 = 3676205) B3676205
theorem B4888151 : Blo 1016603 4888151 := bstep (se 1 (by rfl) ⟨3666113, by rfl⟩ : syracuseStep 4888151 = 7332227) B7332227
theorem B1545913 : Blo 1016603 1545913 := bstep (se 2 (by rfl) ⟨579717, by rfl⟩ : syracuseStep 1545913 = 1159435) B1159435
theorem B5150465 : Blo 1016603 5150465 := bstep (se 2 (by rfl) ⟨1931424, by rfl⟩ : syracuseStep 5150465 = 3862849) B3862849
theorem B12719987 : Blo 1016603 12719987 := bstep (se 1 (by rfl) ⟨9539990, by rfl⟩ : syracuseStep 12719987 = 19079981) B19079981
theorem B12556147 : Blo 1016603 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B21993565 : Blo 1016603 21993565 := bstep (se 3 (by rfl) ⟨4123793, by rfl⟩ : syracuseStep 21993565 = 8247587) B8247587
theorem B5577011 : Blo 1016603 5577011 := bstep (se 1 (by rfl) ⟨4182758, by rfl⟩ : syracuseStep 5577011 = 8365517) B8365517
theorem B1087879 : Blo 1016603 1087879 := bstep (se 1 (by rfl) ⟨815909, by rfl⟩ : syracuseStep 1087879 = 1631819) B1631819
theorem B8264195 : Blo 1016603 8264195 := bstep (se 1 (by rfl) ⟨6198146, by rfl⟩ : syracuseStep 8264195 = 12396293) B12396293
theorem B1448455 : Blo 1016603 1448455 := bstep (se 1 (by rfl) ⟨1086341, by rfl⟩ : syracuseStep 1448455 = 2172683) B2172683
theorem B5151275 : Blo 1016603 5151275 := bstep (se 1 (by rfl) ⟨3863456, by rfl⟩ : syracuseStep 5151275 = 7726913) B7726913
theorem B5806849 : Blo 1016603 5806849 := bstep (se 2 (by rfl) ⟨2177568, by rfl⟩ : syracuseStep 5806849 = 4355137) B4355137
theorem B1449019 : Blo 1016603 1449019 := bstep (se 1 (by rfl) ⟨1086764, by rfl⟩ : syracuseStep 1449019 = 2173529) B2173529
theorem B7445591 : Blo 1016603 7445591 := bstep (se 1 (by rfl) ⟨5584193, by rfl⟩ : syracuseStep 7445591 = 11168387) B11168387
theorem B1088699 : Blo 1016603 1088699 := bstep (se 1 (by rfl) ⟨816524, by rfl⟩ : syracuseStep 1088699 = 1633049) B1633049
theorem B5807375 : Blo 1016603 5807375 := bstep (se 1 (by rfl) ⟨4355531, by rfl⟩ : syracuseStep 5807375 = 8711063) B8711063
theorem B6528401 : Blo 1016603 6528401 := bstep (se 2 (by rfl) ⟨2448150, by rfl⟩ : syracuseStep 6528401 = 4896301) B4896301
theorem B11148749 : Blo 1016603 11148749 := bstep (se 3 (by rfl) ⟨2090390, by rfl⟩ : syracuseStep 11148749 = 4180781) B4180781
theorem B8265169 : Blo 1016603 8265169 := bstep (se 2 (by rfl) ⟨3099438, by rfl⟩ : syracuseStep 8265169 = 6198877) B6198877
theorem B20913815 : Blo 1016603 20913815 := bstep (se 1 (by rfl) ⟨15685361, by rfl⟩ : syracuseStep 20913815 = 31370723) B31370723
theorem B8822465 : Blo 1016603 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B5152571 : Blo 1016603 5152571 := bstep (se 1 (by rfl) ⟨3864428, by rfl⟩ : syracuseStep 5152571 = 7728857) B7728857
theorem B1449913 : Blo 1016603 1449913 := bstep (se 2 (by rfl) ⟨543717, by rfl⟩ : syracuseStep 1449913 = 1087435) B1087435
theorem B5152733 : Blo 1016603 5152733 := bstep (se 3 (by rfl) ⟨966137, by rfl⟩ : syracuseStep 5152733 = 1932275) B1932275
theorem B12230929 : Blo 1016603 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B5153057 : Blo 1016603 5153057 := bstep (se 2 (by rfl) ⟨1932396, by rfl⟩ : syracuseStep 5153057 = 3864793) B3864793
theorem B5808833 : Blo 1016603 5808833 := bstep (se 2 (by rfl) ⟨2178312, by rfl⟩ : syracuseStep 5808833 = 4356625) B4356625
theorem B1451143 : Blo 1016603 1451143 := bstep (se 1 (by rfl) ⟨1088357, by rfl⟩ : syracuseStep 1451143 = 2176715) B2176715
theorem B4891841 : Blo 1016603 4891841 := bstep (se 2 (by rfl) ⟨1834440, by rfl⟩ : syracuseStep 4891841 = 3668881) B3668881
theorem B5154029 : Blo 1016603 5154029 := bstep (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) B1932761
theorem B22029893 : Blo 1016603 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B13051469 : Blo 1016603 13051469 := bstep (se 3 (by rfl) ⟨2447150, by rfl⟩ : syracuseStep 13051469 = 4894301) B4894301
theorem B26125901 : Blo 1016603 26125901 := bstep (se 3 (by rfl) ⟨4898606, by rfl⟩ : syracuseStep 26125901 = 9797213) B9797213
theorem B5515067 : Blo 1016603 5515067 := bstep (se 1 (by rfl) ⟨4136300, by rfl⟩ : syracuseStep 5515067 = 8272601) B8272601
theorem B1451849 : Blo 1016603 1451849 := bstep (se 2 (by rfl) ⟨544443, by rfl⟩ : syracuseStep 1451849 = 1088887) B1088887
theorem B1451963 : Blo 1016603 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B5154839 : Blo 1016603 5154839 := bstep (se 1 (by rfl) ⟨3866129, by rfl⟩ : syracuseStep 5154839 = 7732259) B7732259
theorem B12396833 : Blo 1016603 12396833 := bstep (se 2 (by rfl) ⟨4648812, by rfl⟩ : syracuseStep 12396833 = 9297625) B9297625
theorem B8366557 : Blo 1016603 8366557 := bstep (se 3 (by rfl) ⟨1568729, by rfl⟩ : syracuseStep 8366557 = 3137459) B3137459
theorem B1452601 : Blo 1016603 1452601 := bstep (se 2 (by rfl) ⟨544725, by rfl⟩ : syracuseStep 1452601 = 1089451) B1089451
theorem B18590579 : Blo 1016603 18590579 := bstep (se 1 (by rfl) ⟨13942934, by rfl⟩ : syracuseStep 18590579 = 27885869) B27885869
theorem B7744409 : Blo 1016603 7744409 := bstep (se 2 (by rfl) ⟨2904153, by rfl⟩ : syracuseStep 7744409 = 5808307) B5808307
theorem B8825867 : Blo 1016603 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B5811223 : Blo 1016603 5811223 := bstep (se 1 (by rfl) ⟨4358417, by rfl⟩ : syracuseStep 5811223 = 8716835) B8716835
theorem B5024855 : Blo 1016603 5024855 := bstep (se 1 (by rfl) ⟨3768641, by rfl⟩ : syracuseStep 5024855 = 7537283) B7537283
theorem B1289515 : Blo 1016603 1289515 := bstep (se 1 (by rfl) ⟨967136, by rfl⟩ : syracuseStep 1289515 = 1934273) B1934273
theorem B1715755 : Blo 1016603 1715755 := bstep (se 1 (by rfl) ⟨1286816, by rfl⟩ : syracuseStep 1715755 = 2573633) B2573633
theorem B1715897 : Blo 1016603 1715897 := bstep (se 2 (by rfl) ⟨643461, by rfl⟩ : syracuseStep 1715897 = 1286923) B1286923
theorem B2207417 : Blo 1016603 2207417 := bstep (se 2 (by rfl) ⟨827781, by rfl⟩ : syracuseStep 2207417 = 1655563) B1655563
theorem B19607345 : Blo 1016603 19607345 := bstep (se 2 (by rfl) ⟨7352754, by rfl⟩ : syracuseStep 19607345 = 14705509) B14705509
theorem B14659379 : Blo 1016603 14659379 := bstep (se 1 (by rfl) ⟨10994534, by rfl⟩ : syracuseStep 14659379 = 21989069) B21989069
theorem B4894609 : Blo 1016603 4894609 := bstep (se 2 (by rfl) ⟨1835478, by rfl⟩ : syracuseStep 4894609 = 3670957) B3670957
theorem B2174921 : Blo 1016603 2174921 := bstep (se 2 (by rfl) ⟨815595, by rfl⟩ : syracuseStep 2174921 = 1631191) B1631191
theorem B5517335 : Blo 1016603 5517335 := bstep (se 1 (by rfl) ⟨4138001, by rfl⟩ : syracuseStep 5517335 = 8276003) B8276003
theorem B1290487 : Blo 1016603 1290487 := bstep (se 1 (by rfl) ⟨967865, by rfl⟩ : syracuseStep 1290487 = 1935731) B1935731
theorem B1716599 : Blo 1016603 1716599 := bstep (se 1 (by rfl) ⟨1287449, by rfl⟩ : syracuseStep 1716599 = 2574899) B2574899
theorem B1290811 : Blo 1016603 1290811 := bstep (se 1 (by rfl) ⟨968108, by rfl⟩ : syracuseStep 1290811 = 1936217) B1936217
theorem B10465859 : Blo 1016603 10465859 := bstep (se 1 (by rfl) ⟨7849394, by rfl⟩ : syracuseStep 10465859 = 15698789) B15698789
theorem B2896499 : Blo 1016603 2896499 := bstep (se 1 (by rfl) ⟨2172374, by rfl⟩ : syracuseStep 2896499 = 4344749) B4344749
theorem B2175673 : Blo 1016603 2175673 := bstep (se 2 (by rfl) ⟨815877, by rfl⟩ : syracuseStep 2175673 = 1631755) B1631755
theorem B7746353 : Blo 1016603 7746353 := bstep (se 2 (by rfl) ⟨2904882, by rfl⟩ : syracuseStep 7746353 = 5809765) B5809765
theorem B1717051 : Blo 1016603 1717051 := bstep (se 1 (by rfl) ⟨1287788, by rfl⟩ : syracuseStep 1717051 = 2575577) B2575577
theorem B9777995 : Blo 1016603 9777995 := bstep (se 1 (by rfl) ⟨7333496, by rfl⟩ : syracuseStep 9777995 = 14666993) B14666993
theorem B1717193 : Blo 1016603 1717193 := bstep (se 2 (by rfl) ⟨643947, by rfl⟩ : syracuseStep 1717193 = 1287895) B1287895
theorem B5157917 : Blo 1016603 5157917 := bstep (se 3 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 5157917 = 1934219) B1934219
theorem B2896955 : Blo 1016603 2896955 := bstep (se 1 (by rfl) ⟨2172716, by rfl⟩ : syracuseStep 2896955 = 4345433) B4345433
theorem B11580893 : Blo 1016603 11580893 := bstep (se 3 (by rfl) ⟨2171417, by rfl⟩ : syracuseStep 11580893 = 4342835) B4342835
theorem B5158403 : Blo 1016603 5158403 := bstep (se 1 (by rfl) ⟨3868802, by rfl⟩ : syracuseStep 5158403 = 7737605) B7737605
theorem B14890499 : Blo 1016603 14890499 := bstep (se 1 (by rfl) ⟨11167874, by rfl⟩ : syracuseStep 14890499 = 22335749) B22335749
theorem B1717895 : Blo 1016603 1717895 := bstep (se 1 (by rfl) ⟨1288421, by rfl⟩ : syracuseStep 1717895 = 2576843) B2576843
theorem B2897707 : Blo 1016603 2897707 := bstep (se 1 (by rfl) ⟨2173280, by rfl⟩ : syracuseStep 2897707 = 4346561) B4346561
theorem B6273047 : Blo 1016603 6273047 := bstep (se 1 (by rfl) ⟨4704785, by rfl⟩ : syracuseStep 6273047 = 9409571) B9409571
theorem B2177057 : Blo 1016603 2177057 := bstep (se 2 (by rfl) ⟨816396, by rfl⟩ : syracuseStep 2177057 = 1632793) B1632793
theorem B2897981 : Blo 1016603 2897981 := bstep (se 3 (by rfl) ⟨543371, by rfl⟩ : syracuseStep 2897981 = 1086743) B1086743
theorem B1718543 : Blo 1016603 1718543 := bstep (se 1 (by rfl) ⟨1288907, by rfl⟩ : syracuseStep 1718543 = 2577815) B2577815
theorem B3979655 : Blo 1016603 3979655 := bstep (se 1 (by rfl) ⟨2984741, by rfl⟩ : syracuseStep 3979655 = 5969483) B5969483
theorem B1719083 : Blo 1016603 1719083 := bstep (se 1 (by rfl) ⟨1289312, by rfl⟩ : syracuseStep 1719083 = 2578625) B2578625
theorem B2898823 : Blo 1016603 2898823 := bstep (se 1 (by rfl) ⟨2174117, by rfl⟩ : syracuseStep 2898823 = 4348235) B4348235
theorem B1162171 : Blo 1016603 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B5160023 : Blo 1016603 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B3259511 : Blo 1016603 3259511 := bstep (se 1 (by rfl) ⟨2444633, by rfl⟩ : syracuseStep 3259511 = 4889267) B4889267
theorem B2899097 : Blo 1016603 2899097 := bstep (se 2 (by rfl) ⟨1087161, by rfl⟩ : syracuseStep 2899097 = 2174323) B2174323
theorem B1719481 : Blo 1016603 1719481 := bstep (se 2 (by rfl) ⟨644805, by rfl⟩ : syracuseStep 1719481 = 1289611) B1289611
theorem B3489139 : Blo 1016603 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B4406663 : Blo 1016603 4406663 := bstep (se 1 (by rfl) ⟨3304997, by rfl⟩ : syracuseStep 4406663 = 6609995) B6609995
theorem B5160509 : Blo 1016603 5160509 := bstep (se 3 (by rfl) ⟨967595, by rfl⟩ : syracuseStep 5160509 = 1935191) B1935191
theorem B9912179 : Blo 1016603 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B1720183 : Blo 1016603 1720183 := bstep (se 1 (by rfl) ⟨1290137, by rfl⟩ : syracuseStep 1720183 = 2580275) B2580275
theorem B4898839 : Blo 1016603 4898839 := bstep (se 1 (by rfl) ⟨3674129, by rfl⟩ : syracuseStep 4898839 = 7348259) B7348259
theorem B1720379 : Blo 1016603 1720379 := bstep (se 1 (by rfl) ⟨1290284, by rfl⟩ : syracuseStep 1720379 = 2580569) B2580569
theorem B3489911 : Blo 1016603 3489911 := bstep (se 1 (by rfl) ⟨2617433, by rfl⟩ : syracuseStep 3489911 = 5234867) B5234867
theorem B2900225 : Blo 1016603 2900225 := bstep (se 2 (by rfl) ⟨1087584, by rfl⟩ : syracuseStep 2900225 = 2175169) B2175169
theorem B3260807 : Blo 1016603 3260807 := bstep (se 1 (by rfl) ⟨2445605, by rfl⟩ : syracuseStep 3260807 = 4891211) B4891211
theorem B1720777 : Blo 1016603 1720777 := bstep (se 2 (by rfl) ⟨645291, by rfl⟩ : syracuseStep 1720777 = 1290583) B1290583
theorem B2900681 : Blo 1016603 2900681 := bstep (se 2 (by rfl) ⟨1087755, by rfl⟩ : syracuseStep 2900681 = 2175511) B2175511
theorem B8274703 : Blo 1016603 8274703 := bstep (se 1 (by rfl) ⟨6206027, by rfl⟩ : syracuseStep 8274703 = 12412055) B12412055
theorem B1721479 : Blo 1016603 1721479 := bstep (se 1 (by rfl) ⟨1291109, by rfl⟩ : syracuseStep 1721479 = 2582219) B2582219
theorem B1524923 : Blo 1016603 1524923 := bstep (se 1 (by rfl) ⟨1143692, by rfl⟩ : syracuseStep 1524923 = 2287385) B2287385
theorem B1524983 : Blo 1016603 1524983 := bstep (se 1 (by rfl) ⟨1143737, by rfl⟩ : syracuseStep 1524983 = 2287475) B2287475
theorem B1525007 : Blo 1016603 1525007 := bstep (se 1 (by rfl) ⟨1143755, by rfl⟩ : syracuseStep 1525007 = 2287511) B2287511
theorem B5162291 : Blo 1016603 5162291 := bstep (se 1 (by rfl) ⟨3871718, by rfl⟩ : syracuseStep 5162291 = 7743437) B7743437
theorem B1525049 : Blo 1016603 1525049 := bstep (se 2 (by rfl) ⟨571893, by rfl⟩ : syracuseStep 1525049 = 1143787) B1143787
theorem B1525127 : Blo 1016603 1525127 := bstep (se 1 (by rfl) ⟨1143845, by rfl⟩ : syracuseStep 1525127 = 2287691) B2287691
theorem B1525163 : Blo 1016603 1525163 := bstep (se 1 (by rfl) ⟨1143872, by rfl⟩ : syracuseStep 1525163 = 2287745) B2287745
theorem B1525193 : Blo 1016603 1525193 := bstep (se 2 (by rfl) ⟨571947, by rfl⟩ : syracuseStep 1525193 = 1143895) B1143895
theorem B1525307 : Blo 1016603 1525307 := bstep (se 1 (by rfl) ⟨1143980, by rfl⟩ : syracuseStep 1525307 = 2287961) B2287961
theorem B1525367 : Blo 1016603 1525367 := bstep (se 1 (by rfl) ⟨1144025, by rfl⟩ : syracuseStep 1525367 = 2288051) B2288051
theorem B12371575 : Blo 1016603 12371575 := bstep (se 1 (by rfl) ⟨9278681, by rfl⟩ : syracuseStep 12371575 = 18557363) B18557363
theorem B5162615 : Blo 1016603 5162615 := bstep (se 1 (by rfl) ⟨3871961, by rfl⟩ : syracuseStep 5162615 = 7743923) B7743923
theorem B1525391 : Blo 1016603 1525391 := bstep (se 1 (by rfl) ⟨1144043, by rfl⟩ : syracuseStep 1525391 = 2288087) B2288087
theorem B2573977 : Blo 1016603 2573977 := bstep (se 2 (by rfl) ⟨965241, by rfl⟩ : syracuseStep 2573977 = 1930483) B1930483
theorem B1525433 : Blo 1016603 1525433 := bstep (se 2 (by rfl) ⟨572037, by rfl⟩ : syracuseStep 1525433 = 1144075) B1144075
theorem B1525511 : Blo 1016603 1525511 := bstep (se 1 (by rfl) ⟨1144133, by rfl⟩ : syracuseStep 1525511 = 2288267) B2288267
theorem B1722127 : Blo 1016603 1722127 := bstep (se 1 (by rfl) ⟨1291595, by rfl⟩ : syracuseStep 1722127 = 2583191) B2583191
theorem B1525547 : Blo 1016603 1525547 := bstep (se 1 (by rfl) ⟨1144160, by rfl⟩ : syracuseStep 1525547 = 2288321) B2288321
theorem B2574139 : Blo 1016603 2574139 := bstep (se 1 (by rfl) ⟨1930604, by rfl⟩ : syracuseStep 2574139 = 3861209) B3861209
theorem B1525577 : Blo 1016603 1525577 := bstep (se 2 (by rfl) ⟨572091, by rfl⟩ : syracuseStep 1525577 = 1144183) B1144183
theorem B1525691 : Blo 1016603 1525691 := bstep (se 1 (by rfl) ⟨1144268, by rfl⟩ : syracuseStep 1525691 = 2288537) B2288537
theorem B2574281 : Blo 1016603 2574281 := bstep (se 2 (by rfl) ⟨965355, by rfl⟩ : syracuseStep 2574281 = 1930711) B1930711
theorem B1525751 : Blo 1016603 1525751 := bstep (se 1 (by rfl) ⟨1144313, by rfl⟩ : syracuseStep 1525751 = 2288627) B2288627
theorem B1525775 : Blo 1016603 1525775 := bstep (se 1 (by rfl) ⟨1144331, by rfl⟩ : syracuseStep 1525775 = 2288663) B2288663
theorem B9783341 : Blo 1016603 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B1525817 : Blo 1016603 1525817 := bstep (se 2 (by rfl) ⟨572181, by rfl⟩ : syracuseStep 1525817 = 1144363) B1144363
theorem B1525895 : Blo 1016603 1525895 := bstep (se 1 (by rfl) ⟨1144421, by rfl⟩ : syracuseStep 1525895 = 2288843) B2288843
theorem B1525931 : Blo 1016603 1525931 := bstep (se 1 (by rfl) ⟨1144448, by rfl⟩ : syracuseStep 1525931 = 2288897) B2288897
theorem B1525961 : Blo 1016603 1525961 := bstep (se 2 (by rfl) ⟨572235, by rfl⟩ : syracuseStep 1525961 = 1144471) B1144471
theorem B2574625 : Blo 1016603 2574625 := bstep (se 2 (by rfl) ⟨965484, by rfl⟩ : syracuseStep 2574625 = 1930969) B1930969
theorem B1526075 : Blo 1016603 1526075 := bstep (se 1 (by rfl) ⟨1144556, by rfl⟩ : syracuseStep 1526075 = 2289113) B2289113
theorem B2902331 : Blo 1016603 2902331 := bstep (se 1 (by rfl) ⟨2176748, by rfl⟩ : syracuseStep 2902331 = 4353497) B4353497
theorem B1526135 : Blo 1016603 1526135 := bstep (se 1 (by rfl) ⟨1144601, by rfl⟩ : syracuseStep 1526135 = 2289203) B2289203
theorem B1526159 : Blo 1016603 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B1526201 : Blo 1016603 1526201 := bstep (se 2 (by rfl) ⟨572325, by rfl⟩ : syracuseStep 1526201 = 1144651) B1144651
theorem B1526279 : Blo 1016603 1526279 := bstep (se 1 (by rfl) ⟨1144709, by rfl⟩ : syracuseStep 1526279 = 2289419) B2289419
theorem B2476555 : Blo 1016603 2476555 := bstep (se 1 (by rfl) ⟨1857416, by rfl⟩ : syracuseStep 2476555 = 3714833) B3714833
theorem B1526315 : Blo 1016603 1526315 := bstep (se 1 (by rfl) ⟨1144736, by rfl⟩ : syracuseStep 1526315 = 2289473) B2289473
theorem B5163587 : Blo 1016603 5163587 := bstep (se 1 (by rfl) ⟨3872690, by rfl⟩ : syracuseStep 5163587 = 7745381) B7745381
theorem B1526345 : Blo 1016603 1526345 := bstep (se 2 (by rfl) ⟨572379, by rfl⟩ : syracuseStep 1526345 = 1144759) B1144759
theorem B1526459 : Blo 1016603 1526459 := bstep (se 1 (by rfl) ⟨1144844, by rfl⟩ : syracuseStep 1526459 = 2289689) B2289689
theorem B9292481 : Blo 1016603 9292481 := bstep (se 2 (by rfl) ⟨3484680, by rfl⟩ : syracuseStep 9292481 = 6969361) B6969361
theorem B1526519 : Blo 1016603 1526519 := bstep (se 1 (by rfl) ⟨1144889, by rfl⟩ : syracuseStep 1526519 = 2289779) B2289779
theorem B1526543 : Blo 1016603 1526543 := bstep (se 1 (by rfl) ⟨1144907, by rfl⟩ : syracuseStep 1526543 = 2289815) B2289815
theorem B1526585 : Blo 1016603 1526585 := bstep (se 2 (by rfl) ⟨572469, by rfl⟩ : syracuseStep 1526585 = 1144939) B1144939
theorem B2575223 : Blo 1016603 2575223 := bstep (se 1 (by rfl) ⟨1931417, by rfl⟩ : syracuseStep 2575223 = 3862835) B3862835
theorem B1526663 : Blo 1016603 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B5163911 : Blo 1016603 5163911 := bstep (se 1 (by rfl) ⟨3872933, by rfl⟩ : syracuseStep 5163911 = 7745867) B7745867
theorem B1526699 : Blo 1016603 1526699 := bstep (se 1 (by rfl) ⟨1145024, by rfl⟩ : syracuseStep 1526699 = 2290049) B2290049
theorem B2902969 : Blo 1016603 2902969 := bstep (se 2 (by rfl) ⟨1088613, by rfl⟩ : syracuseStep 2902969 = 2177227) B2177227
theorem B1526729 : Blo 1016603 1526729 := bstep (se 2 (by rfl) ⟨572523, by rfl⟩ : syracuseStep 1526729 = 1145047) B1145047
theorem B4344785 : Blo 1016603 4344785 := bstep (se 2 (by rfl) ⟨1629294, by rfl⟩ : syracuseStep 4344785 = 3258589) B3258589
theorem B1526843 : Blo 1016603 1526843 := bstep (se 1 (by rfl) ⟨1145132, by rfl⟩ : syracuseStep 1526843 = 2290265) B2290265
theorem B1526903 : Blo 1016603 1526903 := bstep (se 1 (by rfl) ⟨1145177, by rfl⟩ : syracuseStep 1526903 = 2290355) B2290355
theorem B1526927 : Blo 1016603 1526927 := bstep (se 1 (by rfl) ⟨1145195, by rfl⟩ : syracuseStep 1526927 = 2290391) B2290391
theorem B7720109 : Blo 1016603 7720109 := bstep (se 3 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 7720109 = 2895041) B2895041
theorem B1526969 : Blo 1016603 1526969 := bstep (se 2 (by rfl) ⟨572613, by rfl⟩ : syracuseStep 1526969 = 1145227) B1145227
theorem B1527047 : Blo 1016603 1527047 := bstep (se 1 (by rfl) ⟨1145285, by rfl⟩ : syracuseStep 1527047 = 2290571) B2290571
theorem B1527083 : Blo 1016603 1527083 := bstep (se 1 (by rfl) ⟨1145312, by rfl⟩ : syracuseStep 1527083 = 2290625) B2290625
theorem B2903357 : Blo 1016603 2903357 := bstep (se 3 (by rfl) ⟨544379, by rfl⟩ : syracuseStep 2903357 = 1088759) B1088759
theorem B1527113 : Blo 1016603 1527113 := bstep (se 2 (by rfl) ⟨572667, by rfl⟩ : syracuseStep 1527113 = 1145335) B1145335
theorem B1527227 : Blo 1016603 1527227 := bstep (se 1 (by rfl) ⟨1145420, by rfl⟩ : syracuseStep 1527227 = 2290841) B2290841
theorem B1527287 : Blo 1016603 1527287 := bstep (se 1 (by rfl) ⟨1145465, by rfl⟩ : syracuseStep 1527287 = 2290931) B2290931
theorem B1527311 : Blo 1016603 1527311 := bstep (se 1 (by rfl) ⟨1145483, by rfl⟩ : syracuseStep 1527311 = 2290967) B2290967
theorem B15650333 : Blo 1016603 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B1527353 : Blo 1016603 1527353 := bstep (se 2 (by rfl) ⟨572757, by rfl⟩ : syracuseStep 1527353 = 1145515) B1145515
theorem B1527431 : Blo 1016603 1527431 := bstep (se 1 (by rfl) ⟨1145573, by rfl⟩ : syracuseStep 1527431 = 2291147) B2291147
theorem B1527467 : Blo 1016603 1527467 := bstep (se 1 (by rfl) ⟨1145600, by rfl⟩ : syracuseStep 1527467 = 2291201) B2291201
theorem B1527497 : Blo 1016603 1527497 := bstep (se 2 (by rfl) ⟨572811, by rfl⟩ : syracuseStep 1527497 = 1145623) B1145623
theorem B3526415 : Blo 1016603 3526415 := bstep (se 1 (by rfl) ⟨2644811, by rfl⟩ : syracuseStep 3526415 = 5289623) B5289623
theorem B1527611 : Blo 1016603 1527611 := bstep (se 1 (by rfl) ⟨1145708, by rfl⟩ : syracuseStep 1527611 = 2291417) B2291417
theorem B1527671 : Blo 1016603 1527671 := bstep (se 1 (by rfl) ⟨1145753, by rfl⟩ : syracuseStep 1527671 = 2291507) B2291507
theorem B3100535 : Blo 1016603 3100535 := bstep (se 1 (by rfl) ⟨2325401, by rfl⟩ : syracuseStep 3100535 = 4650803) B4650803
theorem B1527695 : Blo 1016603 1527695 := bstep (se 1 (by rfl) ⟨1145771, by rfl⟩ : syracuseStep 1527695 = 2291543) B2291543
theorem B11620259 : Blo 1016603 11620259 := bstep (se 1 (by rfl) ⟨8715194, by rfl⟩ : syracuseStep 11620259 = 17430389) B17430389
theorem B1527737 : Blo 1016603 1527737 := bstep (se 2 (by rfl) ⟨572901, by rfl⟩ : syracuseStep 1527737 = 1145803) B1145803
theorem B1527815 : Blo 1016603 1527815 := bstep (se 1 (by rfl) ⟨1145861, by rfl⟩ : syracuseStep 1527815 = 2291723) B2291723
theorem B1527851 : Blo 1016603 1527851 := bstep (se 1 (by rfl) ⟨1145888, by rfl⟩ : syracuseStep 1527851 = 2291777) B2291777
theorem B1527881 : Blo 1016603 1527881 := bstep (se 2 (by rfl) ⟨572955, by rfl⟩ : syracuseStep 1527881 = 1145911) B1145911
theorem B3264599 : Blo 1016603 3264599 := bstep (se 1 (by rfl) ⟨2448449, by rfl⟩ : syracuseStep 3264599 = 4896899) B4896899
theorem B2576519 : Blo 1016603 2576519 := bstep (se 1 (by rfl) ⟨1932389, by rfl⟩ : syracuseStep 2576519 = 3864779) B3864779
theorem B2576569 : Blo 1016603 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B1527995 : Blo 1016603 1527995 := bstep (se 1 (by rfl) ⟨1145996, by rfl⟩ : syracuseStep 1527995 = 2291993) B2291993
theorem B3264713 : Blo 1016603 3264713 := bstep (se 2 (by rfl) ⟨1224267, by rfl⟩ : syracuseStep 3264713 = 2448535) B2448535
theorem B1528055 : Blo 1016603 1528055 := bstep (se 1 (by rfl) ⟨1146041, by rfl⟩ : syracuseStep 1528055 = 2292083) B2292083
theorem B1528079 : Blo 1016603 1528079 := bstep (se 1 (by rfl) ⟨1146059, by rfl⟩ : syracuseStep 1528079 = 2292119) B2292119
theorem B3100961 : Blo 1016603 3100961 := bstep (se 2 (by rfl) ⟨1162860, by rfl⟩ : syracuseStep 3100961 = 2325721) B2325721
theorem B1528121 : Blo 1016603 1528121 := bstep (se 2 (by rfl) ⟨573045, by rfl⟩ : syracuseStep 1528121 = 1146091) B1146091
theorem B1528199 : Blo 1016603 1528199 := bstep (se 1 (by rfl) ⟨1146149, by rfl⟩ : syracuseStep 1528199 = 2292299) B2292299
theorem B2904473 : Blo 1016603 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B1528235 : Blo 1016603 1528235 := bstep (se 1 (by rfl) ⟨1146176, by rfl⟩ : syracuseStep 1528235 = 2292353) B2292353
theorem B1528265 : Blo 1016603 1528265 := bstep (se 2 (by rfl) ⟨573099, by rfl⟩ : syracuseStep 1528265 = 1146199) B1146199
theorem B1528379 : Blo 1016603 1528379 := bstep (se 1 (by rfl) ⟨1146284, by rfl⟩ : syracuseStep 1528379 = 2292569) B2292569
theorem B1528393 : Blo 1016603 1528393 := bstep (se 2 (by rfl) ⟨573147, by rfl⟩ : syracuseStep 1528393 = 1146295) B1146295
theorem B1528439 : Blo 1016603 1528439 := bstep (se 1 (by rfl) ⟨1146329, by rfl⟩ : syracuseStep 1528439 = 2292659) B2292659
theorem B1528463 : Blo 1016603 1528463 := bstep (se 1 (by rfl) ⟨1146347, by rfl⟩ : syracuseStep 1528463 = 2292695) B2292695
theorem B1528505 : Blo 1016603 1528505 := bstep (se 2 (by rfl) ⟨573189, by rfl⟩ : syracuseStep 1528505 = 1146379) B1146379
theorem B1528583 : Blo 1016603 1528583 := bstep (se 1 (by rfl) ⟨1146437, by rfl⟩ : syracuseStep 1528583 = 2292875) B2292875
theorem B2577167 : Blo 1016603 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B1528619 : Blo 1016603 1528619 := bstep (se 1 (by rfl) ⟨1146464, by rfl⟩ : syracuseStep 1528619 = 2292929) B2292929
theorem B1528649 : Blo 1016603 1528649 := bstep (se 2 (by rfl) ⟨573243, by rfl⟩ : syracuseStep 1528649 = 1146487) B1146487
theorem B1528763 : Blo 1016603 1528763 := bstep (se 1 (by rfl) ⟨1146572, by rfl⟩ : syracuseStep 1528763 = 2293145) B2293145
theorem B1528823 : Blo 1016603 1528823 := bstep (se 1 (by rfl) ⟨1146617, by rfl⟩ : syracuseStep 1528823 = 2293235) B2293235
theorem B1528847 : Blo 1016603 1528847 := bstep (se 1 (by rfl) ⟨1146635, by rfl⟩ : syracuseStep 1528847 = 2293271) B2293271
theorem B1528889 : Blo 1016603 1528889 := bstep (se 2 (by rfl) ⟨573333, by rfl⟩ : syracuseStep 1528889 = 1146667) B1146667
theorem B1528967 : Blo 1016603 1528967 := bstep (se 1 (by rfl) ⟨1146725, by rfl⟩ : syracuseStep 1528967 = 2293451) B2293451
theorem B1529003 : Blo 1016603 1529003 := bstep (se 1 (by rfl) ⟨1146752, by rfl⟩ : syracuseStep 1529003 = 2293505) B2293505
theorem B1529033 : Blo 1016603 1529033 := bstep (se 2 (by rfl) ⟨573387, by rfl⟩ : syracuseStep 1529033 = 1146775) B1146775
theorem B1529147 : Blo 1016603 1529147 := bstep (se 1 (by rfl) ⟨1146860, by rfl⟩ : syracuseStep 1529147 = 2293721) B2293721
theorem B1529207 : Blo 1016603 1529207 := bstep (se 1 (by rfl) ⟨1146905, by rfl⟩ : syracuseStep 1529207 = 2293811) B2293811
theorem B1529231 : Blo 1016603 1529231 := bstep (se 1 (by rfl) ⟨1146923, by rfl⟩ : syracuseStep 1529231 = 2293847) B2293847
theorem B1529273 : Blo 1016603 1529273 := bstep (se 2 (by rfl) ⟨573477, by rfl⟩ : syracuseStep 1529273 = 1146955) B1146955
theorem B2577865 : Blo 1016603 2577865 := bstep (se 2 (by rfl) ⟨966699, by rfl⟩ : syracuseStep 2577865 = 1933399) B1933399
theorem B15685123 : Blo 1016603 15685123 := bstep (se 1 (by rfl) ⟨11763842, by rfl⟩ : syracuseStep 15685123 = 23527685) B23527685
theorem B1529351 : Blo 1016603 1529351 := bstep (se 1 (by rfl) ⟨1147013, by rfl⟩ : syracuseStep 1529351 = 2294027) B2294027
theorem B66016781 : Blo 1016603 66016781 := bstep (se 3 (by rfl) ⟨12378146, by rfl⟩ : syracuseStep 66016781 = 24756293) B24756293
theorem B7722539 : Blo 1016603 7722539 := bstep (se 1 (by rfl) ⟨5791904, by rfl⟩ : syracuseStep 7722539 = 11583809) B11583809
theorem B1529387 : Blo 1016603 1529387 := bstep (se 1 (by rfl) ⟨1147040, by rfl⟩ : syracuseStep 1529387 = 2294081) B2294081
theorem B1529417 : Blo 1016603 1529417 := bstep (se 2 (by rfl) ⟨573531, by rfl⟩ : syracuseStep 1529417 = 1147063) B1147063
theorem B2578007 : Blo 1016603 2578007 := bstep (se 1 (by rfl) ⟨1933505, by rfl⟩ : syracuseStep 2578007 = 3867011) B3867011
theorem B1529531 : Blo 1016603 1529531 := bstep (se 1 (by rfl) ⟨1147148, by rfl⟩ : syracuseStep 1529531 = 2294297) B2294297
theorem B1529591 : Blo 1016603 1529591 := bstep (se 1 (by rfl) ⟨1147193, by rfl⟩ : syracuseStep 1529591 = 2294387) B2294387
theorem B1529615 : Blo 1016603 1529615 := bstep (se 1 (by rfl) ⟨1147211, by rfl⟩ : syracuseStep 1529615 = 2294423) B2294423
theorem B2905885 : Blo 1016603 2905885 := bstep (se 3 (by rfl) ⟨544853, by rfl⟩ : syracuseStep 2905885 = 1089707) B1089707
theorem B1529657 : Blo 1016603 1529657 := bstep (se 2 (by rfl) ⟨573621, by rfl⟩ : syracuseStep 1529657 = 1147243) B1147243
theorem B2447219 : Blo 1016603 2447219 := bstep (se 1 (by rfl) ⟨1835414, by rfl⟩ : syracuseStep 2447219 = 3670829) B3670829
theorem B35346293 : Blo 1016603 35346293 := bstep (se 5 (by rfl) ⟨1656857, by rfl⟩ : syracuseStep 35346293 = 3313715) B3313715
theorem B1529735 : Blo 1016603 1529735 := bstep (se 1 (by rfl) ⟨1147301, by rfl⟩ : syracuseStep 1529735 = 2294603) B2294603
theorem B1529771 : Blo 1016603 1529771 := bstep (se 1 (by rfl) ⟨1147328, by rfl⟩ : syracuseStep 1529771 = 2294657) B2294657
theorem B1529801 : Blo 1016603 1529801 := bstep (se 2 (by rfl) ⟨573675, by rfl⟩ : syracuseStep 1529801 = 1147351) B1147351
theorem B2906057 : Blo 1016603 2906057 := bstep (se 2 (by rfl) ⟨1089771, by rfl⟩ : syracuseStep 2906057 = 2179543) B2179543
theorem B2906113 : Blo 1016603 2906113 := bstep (se 2 (by rfl) ⟨1089792, by rfl⟩ : syracuseStep 2906113 = 2179585) B2179585
theorem B24827917 : Blo 1016603 24827917 := bstep (se 3 (by rfl) ⟨4655234, by rfl⟩ : syracuseStep 24827917 = 9310469) B9310469
theorem B1529915 : Blo 1016603 1529915 := bstep (se 1 (by rfl) ⟨1147436, by rfl⟩ : syracuseStep 1529915 = 2294873) B2294873
theorem B2938999 : Blo 1016603 2938999 := bstep (se 1 (by rfl) ⟨2204249, by rfl⟩ : syracuseStep 2938999 = 4408499) B4408499
theorem B1529975 : Blo 1016603 1529975 := bstep (se 1 (by rfl) ⟨1147481, by rfl⟩ : syracuseStep 1529975 = 2294963) B2294963
theorem B1529999 : Blo 1016603 1529999 := bstep (se 1 (by rfl) ⟨1147499, by rfl⟩ : syracuseStep 1529999 = 2294999) B2294999
theorem B1530041 : Blo 1016603 1530041 := bstep (se 2 (by rfl) ⟨573765, by rfl⟩ : syracuseStep 1530041 = 1147531) B1147531
theorem B1530119 : Blo 1016603 1530119 := bstep (se 1 (by rfl) ⟨1147589, by rfl⟩ : syracuseStep 1530119 = 2295179) B2295179
theorem B18602257 : Blo 1016603 18602257 := bstep (se 2 (by rfl) ⟨6975846, by rfl⟩ : syracuseStep 18602257 = 13951693) B13951693
theorem B1530155 : Blo 1016603 1530155 := bstep (se 1 (by rfl) ⟨1147616, by rfl⟩ : syracuseStep 1530155 = 2295233) B2295233
theorem B1530185 : Blo 1016603 1530185 := bstep (se 2 (by rfl) ⟨573819, by rfl⟩ : syracuseStep 1530185 = 1147639) B1147639
theorem B9066937 : Blo 1016603 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B1530299 : Blo 1016603 1530299 := bstep (se 1 (by rfl) ⟨1147724, by rfl⟩ : syracuseStep 1530299 = 2295449) B2295449
theorem B1530359 : Blo 1016603 1530359 := bstep (se 1 (by rfl) ⟨1147769, by rfl⟩ : syracuseStep 1530359 = 2295539) B2295539
theorem B1530383 : Blo 1016603 1530383 := bstep (se 1 (by rfl) ⟨1147787, by rfl⟩ : syracuseStep 1530383 = 2295575) B2295575
theorem B1530425 : Blo 1016603 1530425 := bstep (se 2 (by rfl) ⟨573909, by rfl⟩ : syracuseStep 1530425 = 1147819) B1147819
theorem B1530503 : Blo 1016603 1530503 := bstep (se 1 (by rfl) ⟨1147877, by rfl⟩ : syracuseStep 1530503 = 2295755) B2295755
theorem B1530539 : Blo 1016603 1530539 := bstep (se 1 (by rfl) ⟨1147904, by rfl⟩ : syracuseStep 1530539 = 2295809) B2295809
theorem B1530569 : Blo 1016603 1530569 := bstep (se 2 (by rfl) ⟨573963, by rfl⟩ : syracuseStep 1530569 = 1147927) B1147927
theorem B44718797 : Blo 1016603 44718797 := bstep (se 3 (by rfl) ⟨8384774, by rfl⟩ : syracuseStep 44718797 = 16769549) B16769549
theorem B1530683 : Blo 1016603 1530683 := bstep (se 1 (by rfl) ⟨1148012, by rfl⟩ : syracuseStep 1530683 = 2296025) B2296025
theorem B1530743 : Blo 1016603 1530743 := bstep (se 1 (by rfl) ⟨1148057, by rfl⟩ : syracuseStep 1530743 = 2296115) B2296115
theorem B1530767 : Blo 1016603 1530767 := bstep (se 1 (by rfl) ⟨1148075, by rfl⟩ : syracuseStep 1530767 = 2296151) B2296151
theorem B3431321 : Blo 1016603 3431321 := bstep (se 2 (by rfl) ⟨1286745, by rfl⟩ : syracuseStep 3431321 = 2573491) B2573491
theorem B3267481 : Blo 1016603 3267481 := bstep (se 2 (by rfl) ⟨1225305, by rfl⟩ : syracuseStep 3267481 = 2450611) B2450611
theorem B1530809 : Blo 1016603 1530809 := bstep (se 2 (by rfl) ⟨574053, by rfl⟩ : syracuseStep 1530809 = 1148107) B1148107
theorem B1530887 : Blo 1016603 1530887 := bstep (se 1 (by rfl) ⟨1148165, by rfl⟩ : syracuseStep 1530887 = 2296331) B2296331
theorem B13229345 : Blo 1016603 13229345 := bstep (se 2 (by rfl) ⟨4961004, by rfl⟩ : syracuseStep 13229345 = 9922009) B9922009
theorem B3432023 : Blo 1016603 3432023 := bstep (se 1 (by rfl) ⟨2574017, by rfl⟩ : syracuseStep 3432023 = 5148035) B5148035
theorem B2580083 : Blo 1016603 2580083 := bstep (se 1 (by rfl) ⟨1935062, by rfl⟩ : syracuseStep 2580083 = 3870125) B3870125
theorem B12410891 : Blo 1016603 12410891 := bstep (se 1 (by rfl) ⟨9308168, by rfl⟩ : syracuseStep 12410891 = 18616337) B18616337
theorem B3432509 : Blo 1016603 3432509 := bstep (se 3 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 3432509 = 1287191) B1287191
theorem B7430231 : Blo 1016603 7430231 := bstep (se 1 (by rfl) ⟨5572673, by rfl⟩ : syracuseStep 7430231 = 11145347) B11145347
theorem B2580599 : Blo 1016603 2580599 := bstep (se 1 (by rfl) ⟨1935449, by rfl⟩ : syracuseStep 2580599 = 3870899) B3870899
theorem B1958023 : Blo 1016603 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B2581591 : Blo 1016603 2581591 := bstep (se 1 (by rfl) ⟨1936193, by rfl⟩ : syracuseStep 2581591 = 3872387) B3872387
theorem B9299117 : Blo 1016603 9299117 := bstep (se 3 (by rfl) ⟨1743584, by rfl⟩ : syracuseStep 9299117 = 3487169) B3487169
theorem B2581895 : Blo 1016603 2581895 := bstep (se 1 (by rfl) ⟨1936421, by rfl⟩ : syracuseStep 2581895 = 3872843) B3872843
theorem B3433913 : Blo 1016603 3433913 := bstep (se 2 (by rfl) ⟨1287717, by rfl⟩ : syracuseStep 3433913 = 2575435) B2575435
theorem B2385353 : Blo 1016603 2385353 := bstep (se 2 (by rfl) ⟨894507, by rfl⟩ : syracuseStep 2385353 = 1789015) B1789015
theorem B5793227 : Blo 1016603 5793227 := bstep (se 1 (by rfl) ⟨4344920, by rfl⟩ : syracuseStep 5793227 = 8689841) B8689841
theorem B2582027 : Blo 1016603 2582027 := bstep (se 1 (by rfl) ⟨1936520, by rfl⟩ : syracuseStep 2582027 = 3873041) B3873041
theorem B2287403 : Blo 1016603 2287403 := bstep (se 1 (by rfl) ⟨1715552, by rfl⟩ : syracuseStep 2287403 = 3431105) B3431105
theorem B2942855 : Blo 1016603 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B3434507 : Blo 1016603 3434507 := bstep (se 1 (by rfl) ⟨2575880, by rfl⟩ : syracuseStep 3434507 = 5151761) B5151761
theorem B2582543 : Blo 1016603 2582543 := bstep (se 1 (by rfl) ⟨1936907, by rfl⟩ : syracuseStep 2582543 = 3873815) B3873815
theorem B3434615 : Blo 1016603 3434615 := bstep (se 1 (by rfl) ⟨2575961, by rfl⟩ : syracuseStep 3434615 = 5151923) B5151923
theorem B2287763 : Blo 1016603 2287763 := bstep (se 1 (by rfl) ⟨1715822, by rfl⟩ : syracuseStep 2287763 = 3431645) B3431645
theorem B2582675 : Blo 1016603 2582675 := bstep (se 1 (by rfl) ⟨1937006, by rfl⟩ : syracuseStep 2582675 = 3874013) B3874013
theorem B2287817 : Blo 1016603 2287817 := bstep (se 2 (by rfl) ⟨857931, by rfl⟩ : syracuseStep 2287817 = 1715863) B1715863
theorem B4418059 : Blo 1016603 4418059 := bstep (se 1 (by rfl) ⟨3313544, by rfl⟩ : syracuseStep 4418059 = 6627089) B6627089
theorem B8710685 : Blo 1016603 8710685 := bstep (se 3 (by rfl) ⟨1633253, by rfl⟩ : syracuseStep 8710685 = 3266507) B3266507
theorem B3435209 : Blo 1016603 3435209 := bstep (se 2 (by rfl) ⟨1288203, by rfl⟩ : syracuseStep 3435209 = 2576407) B2576407
theorem B2452169 : Blo 1016603 2452169 := bstep (se 2 (by rfl) ⟨919563, by rfl⟩ : syracuseStep 2452169 = 1839127) B1839127
theorem B3664673 : Blo 1016603 3664673 := bstep (se 2 (by rfl) ⟨1374252, by rfl⟩ : syracuseStep 3664673 = 2748505) B2748505
theorem B5499737 : Blo 1016603 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B2288519 : Blo 1016603 2288519 := bstep (se 1 (by rfl) ⟨1716389, by rfl⟩ : syracuseStep 2288519 = 3432779) B3432779
theorem B2288699 : Blo 1016603 2288699 := bstep (se 1 (by rfl) ⟨1716524, by rfl⟩ : syracuseStep 2288699 = 3433049) B3433049
theorem B2288825 : Blo 1016603 2288825 := bstep (se 2 (by rfl) ⟨858309, by rfl⟩ : syracuseStep 2288825 = 1716619) B1716619
theorem B2682247 : Blo 1016603 2682247 := bstep (se 1 (by rfl) ⟨2011685, by rfl⟩ : syracuseStep 2682247 = 4023371) B4023371
theorem B3435911 : Blo 1016603 3435911 := bstep (se 1 (by rfl) ⟨2576933, by rfl⟩ : syracuseStep 3435911 = 5153867) B5153867
theorem B2289167 : Blo 1016603 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B2289185 : Blo 1016603 2289185 := bstep (se 2 (by rfl) ⟨858444, by rfl⟩ : syracuseStep 2289185 = 1716889) B1716889
theorem B3436289 : Blo 1016603 3436289 := bstep (se 2 (by rfl) ⟨1288608, by rfl⟩ : syracuseStep 3436289 = 2577217) B2577217
theorem B9793295 : Blo 1016603 9793295 := bstep (se 1 (by rfl) ⟨7344971, by rfl⟩ : syracuseStep 9793295 = 14689943) B14689943
theorem B5500709 : Blo 1016603 5500709 := bstep (se 4 (by rfl) ⟨515691, by rfl⟩ : syracuseStep 5500709 = 1031383) B1031383
theorem B4353907 : Blo 1016603 4353907 := bstep (se 1 (by rfl) ⟨3265430, by rfl⟩ : syracuseStep 4353907 = 6530861) B6530861
theorem B2289527 : Blo 1016603 2289527 := bstep (se 1 (by rfl) ⟨1717145, by rfl⟩ : syracuseStep 2289527 = 3434291) B3434291
theorem B2289707 : Blo 1016603 2289707 := bstep (se 1 (by rfl) ⟨1717280, by rfl⟩ : syracuseStep 2289707 = 3434561) B3434561
theorem B4354249 : Blo 1016603 4354249 := bstep (se 2 (by rfl) ⟨1632843, by rfl⟩ : syracuseStep 4354249 = 3265687) B3265687
theorem B2290067 : Blo 1016603 2290067 := bstep (se 1 (by rfl) ⟨1717550, by rfl⟩ : syracuseStep 2290067 = 3435101) B3435101
theorem B2290121 : Blo 1016603 2290121 := bstep (se 2 (by rfl) ⟨858795, by rfl⟩ : syracuseStep 2290121 = 1717591) B1717591
theorem B2748971 : Blo 1016603 2748971 := bstep (se 1 (by rfl) ⟨2061728, by rfl⟩ : syracuseStep 2748971 = 4123457) B4123457
theorem B3437099 : Blo 1016603 3437099 := bstep (se 1 (by rfl) ⟨2577824, by rfl⟩ : syracuseStep 3437099 = 5155649) B5155649
theorem B1930043 : Blo 1016603 1930043 := bstep (se 1 (by rfl) ⟨1447532, by rfl⟩ : syracuseStep 1930043 = 2895065) B2895065
theorem B1143823 : Blo 1016603 1143823 := bstep (se 1 (by rfl) ⟨857867, by rfl⟩ : syracuseStep 1143823 = 1715735) B1715735
theorem B3863639 : Blo 1016603 3863639 := bstep (se 1 (by rfl) ⟨2897729, by rfl⟩ : syracuseStep 3863639 = 5795459) B5795459
theorem B1832071 : Blo 1016603 1832071 := bstep (se 1 (by rfl) ⟨1374053, by rfl⟩ : syracuseStep 1832071 = 2748107) B2748107
theorem B2290823 : Blo 1016603 2290823 := bstep (se 1 (by rfl) ⟨1718117, by rfl⟩ : syracuseStep 2290823 = 3436235) B3436235
theorem B2094265 : Blo 1016603 2094265 := bstep (se 2 (by rfl) ⟨785349, by rfl⟩ : syracuseStep 2094265 = 1570699) B1570699
theorem B4355309 : Blo 1016603 4355309 := bstep (se 3 (by rfl) ⟨816620, by rfl⟩ : syracuseStep 4355309 = 1633241) B1633241
theorem B1930529 : Blo 1016603 1930529 := bstep (se 2 (by rfl) ⟨723948, by rfl⟩ : syracuseStep 1930529 = 1447897) B1447897
theorem B2291003 : Blo 1016603 2291003 := bstep (se 1 (by rfl) ⟨1718252, by rfl⟩ : syracuseStep 2291003 = 3436505) B3436505
theorem B2291129 : Blo 1016603 2291129 := bstep (se 2 (by rfl) ⟨859173, by rfl⟩ : syracuseStep 2291129 = 1718347) B1718347
theorem B1144327 : Blo 1016603 1144327 := bstep (se 1 (by rfl) ⟨858245, by rfl⟩ : syracuseStep 1144327 = 1716491) B1716491
theorem B16774685 : Blo 1016603 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B3864125 : Blo 1016603 3864125 := bstep (se 3 (by rfl) ⟨724523, by rfl⟩ : syracuseStep 3864125 = 1449047) B1449047
theorem B1930871 : Blo 1016603 1930871 := bstep (se 1 (by rfl) ⟨1448153, by rfl⟩ : syracuseStep 1930871 = 2896307) B2896307
theorem B7337591 : Blo 1016603 7337591 := bstep (se 1 (by rfl) ⟨5503193, by rfl⟩ : syracuseStep 7337591 = 11006387) B11006387
theorem B1144507 : Blo 1016603 1144507 := bstep (se 1 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 1144507 = 1716761) B1716761
theorem B2291471 : Blo 1016603 2291471 := bstep (se 1 (by rfl) ⟨1718603, by rfl⟩ : syracuseStep 2291471 = 3437207) B3437207
theorem B2291489 : Blo 1016603 2291489 := bstep (se 2 (by rfl) ⟨859308, by rfl⟩ : syracuseStep 2291489 = 1718617) B1718617
theorem B3438395 : Blo 1016603 3438395 := bstep (se 1 (by rfl) ⟨2578796, by rfl⟩ : syracuseStep 3438395 = 5157593) B5157593
theorem B18610073 : Blo 1016603 18610073 := bstep (se 2 (by rfl) ⟨6978777, by rfl⟩ : syracuseStep 18610073 = 13957555) B13957555
theorem B7731287 : Blo 1016603 7731287 := bstep (se 1 (by rfl) ⟨5798465, by rfl⟩ : syracuseStep 7731287 = 11596931) B11596931
theorem B2291831 : Blo 1016603 2291831 := bstep (se 1 (by rfl) ⟨1718873, by rfl⟩ : syracuseStep 2291831 = 3437747) B3437747
theorem B1144975 : Blo 1016603 1144975 := bstep (se 1 (by rfl) ⟨858731, by rfl⟩ : syracuseStep 1144975 = 1717463) B1717463
theorem B39090437 : Blo 1016603 39090437 := bstep (se 4 (by rfl) ⟨3664728, by rfl⟩ : syracuseStep 39090437 = 7329457) B7329457
theorem B3438881 : Blo 1016603 3438881 := bstep (se 2 (by rfl) ⟨1289580, by rfl⟩ : syracuseStep 3438881 = 2579161) B2579161
theorem B1833259 : Blo 1016603 1833259 := bstep (se 1 (by rfl) ⟨1374944, by rfl⟩ : syracuseStep 1833259 = 2749889) B2749889
theorem B2292011 : Blo 1016603 2292011 := bstep (se 1 (by rfl) ⟨1719008, by rfl⟩ : syracuseStep 2292011 = 3438017) B3438017
theorem B8255891 : Blo 1016603 8255891 := bstep (se 1 (by rfl) ⟨6191918, by rfl⟩ : syracuseStep 8255891 = 12383837) B12383837
theorem B2062967 : Blo 1016603 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B1145479 : Blo 1016603 1145479 := bstep (se 1 (by rfl) ⟨859109, by rfl⟩ : syracuseStep 1145479 = 1718219) B1718219
theorem B2292371 : Blo 1016603 2292371 := bstep (se 1 (by rfl) ⟨1719278, by rfl⟩ : syracuseStep 2292371 = 3438557) B3438557
theorem B2292425 : Blo 1016603 2292425 := bstep (se 2 (by rfl) ⟨859659, by rfl⟩ : syracuseStep 2292425 = 1719319) B1719319
theorem B9435905 : Blo 1016603 9435905 := bstep (se 2 (by rfl) ⟨3538464, by rfl⟩ : syracuseStep 9435905 = 7076929) B7076929
theorem B8715059 : Blo 1016603 8715059 := bstep (se 1 (by rfl) ⟨6536294, by rfl⟩ : syracuseStep 8715059 = 13072589) B13072589
theorem B1145659 : Blo 1016603 1145659 := bstep (se 1 (by rfl) ⟨859244, by rfl⟩ : syracuseStep 1145659 = 1718489) B1718489
theorem B3439475 : Blo 1016603 3439475 := bstep (se 1 (by rfl) ⟨2579606, by rfl⟩ : syracuseStep 3439475 = 5159213) B5159213
theorem B3865553 : Blo 1016603 3865553 := bstep (se 2 (by rfl) ⟨1449582, by rfl⟩ : syracuseStep 3865553 = 2899165) B2899165
theorem B8715437 : Blo 1016603 8715437 := bstep (se 3 (by rfl) ⟨1634144, by rfl⟩ : syracuseStep 8715437 = 3268289) B3268289
theorem B1932473 : Blo 1016603 1932473 := bstep (se 2 (by rfl) ⟨724677, by rfl⟩ : syracuseStep 1932473 = 1449355) B1449355
theorem B1146127 : Blo 1016603 1146127 := bstep (se 1 (by rfl) ⟨859595, by rfl⟩ : syracuseStep 1146127 = 1719191) B1719191
theorem B2293127 : Blo 1016603 2293127 := bstep (se 1 (by rfl) ⟨1719845, by rfl⟩ : syracuseStep 2293127 = 3439691) B3439691
theorem B5799377 : Blo 1016603 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B1932815 : Blo 1016603 1932815 := bstep (se 1 (by rfl) ⟨1449611, by rfl⟩ : syracuseStep 1932815 = 2899223) B2899223
theorem B2293307 : Blo 1016603 2293307 := bstep (se 1 (by rfl) ⟨1719980, by rfl⟩ : syracuseStep 2293307 = 3439961) B3439961
theorem B2293433 : Blo 1016603 2293433 := bstep (se 2 (by rfl) ⟨860037, by rfl⟩ : syracuseStep 2293433 = 1720075) B1720075
theorem B1146631 : Blo 1016603 1146631 := bstep (se 1 (by rfl) ⟨859973, by rfl⟩ : syracuseStep 1146631 = 1719947) B1719947
theorem B2752289 : Blo 1016603 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B67927853 : Blo 1016603 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B3669907 : Blo 1016603 3669907 := bstep (se 1 (by rfl) ⟨2752430, by rfl⟩ : syracuseStep 3669907 = 5504861) B5504861
theorem B5799833 : Blo 1016603 5799833 := bstep (se 2 (by rfl) ⟨2174937, by rfl⟩ : syracuseStep 5799833 = 4349875) B4349875
theorem B1146811 : Blo 1016603 1146811 := bstep (se 1 (by rfl) ⟨860108, by rfl⟩ : syracuseStep 1146811 = 1720217) B1720217
theorem B1835017 : Blo 1016603 1835017 := bstep (se 2 (by rfl) ⟨688131, by rfl⟩ : syracuseStep 1835017 = 1376263) B1376263
theorem B1146919 : Blo 1016603 1146919 := bstep (se 1 (by rfl) ⟨860189, by rfl⟩ : syracuseStep 1146919 = 1720379) B1720379
theorem B2326607 : Blo 1016603 2326607 := bstep (se 1 (by rfl) ⟨1744955, by rfl⟩ : syracuseStep 2326607 = 3489911) B3489911
theorem B1933483 : Blo 1016603 1933483 := bstep (se 1 (by rfl) ⟨1450112, by rfl⟩ : syracuseStep 1933483 = 2900225) B2900225
theorem B1933787 : Blo 1016603 1933787 := bstep (se 1 (by rfl) ⟨1450340, by rfl⟩ : syracuseStep 1933787 = 2900681) B2900681
theorem B14680601 : Blo 1016603 14680601 := bstep (se 2 (by rfl) ⟨5505225, by rfl⟩ : syracuseStep 14680601 = 11010451) B11010451
theorem B2294369 : Blo 1016603 2294369 := bstep (se 2 (by rfl) ⟨860388, by rfl⟩ : syracuseStep 2294369 = 1720777) B1720777
theorem B1016615 : Blo 1016603 1016615 := bstep (se 1 (by rfl) ⟨762461, by rfl⟩ : syracuseStep 1016615 = 1524923) B1524923
theorem B1016655 : Blo 1016603 1016655 := bstep (se 1 (by rfl) ⟨762491, by rfl⟩ : syracuseStep 1016655 = 1524983) B1524983
theorem B1016671 : Blo 1016603 1016671 := bstep (se 1 (by rfl) ⟨762503, by rfl⟩ : syracuseStep 1016671 = 1525007) B1525007
theorem B3441527 : Blo 1016603 3441527 := bstep (se 1 (by rfl) ⟨2581145, by rfl⟩ : syracuseStep 3441527 = 5162291) B5162291
theorem B1016699 : Blo 1016603 1016699 := bstep (se 1 (by rfl) ⟨762524, by rfl⟩ : syracuseStep 1016699 = 1525049) B1525049
theorem B1016751 : Blo 1016603 1016751 := bstep (se 1 (by rfl) ⟨762563, by rfl⟩ : syracuseStep 1016751 = 1525127) B1525127
theorem B2294711 : Blo 1016603 2294711 := bstep (se 1 (by rfl) ⟨1721033, by rfl⟩ : syracuseStep 2294711 = 3442067) B3442067
theorem B1016775 : Blo 1016603 1016775 := bstep (se 1 (by rfl) ⟨762581, by rfl⟩ : syracuseStep 1016775 = 1525163) B1525163
theorem B1016795 : Blo 1016603 1016795 := bstep (se 1 (by rfl) ⟨762596, by rfl⟩ : syracuseStep 1016795 = 1525193) B1525193
theorem B1016871 : Blo 1016603 1016871 := bstep (se 1 (by rfl) ⟨762653, by rfl⟩ : syracuseStep 1016871 = 1525307) B1525307
theorem B1016911 : Blo 1016603 1016911 := bstep (se 1 (by rfl) ⟨762683, by rfl⟩ : syracuseStep 1016911 = 1525367) B1525367
theorem B3441743 : Blo 1016603 3441743 := bstep (se 1 (by rfl) ⟨2581307, by rfl⟩ : syracuseStep 3441743 = 5162615) B5162615
theorem B1016927 : Blo 1016603 1016927 := bstep (se 1 (by rfl) ⟨762695, by rfl⟩ : syracuseStep 1016927 = 1525391) B1525391
theorem B1016955 : Blo 1016603 1016955 := bstep (se 1 (by rfl) ⟨762716, by rfl⟩ : syracuseStep 1016955 = 1525433) B1525433
theorem B1017007 : Blo 1016603 1017007 := bstep (se 1 (by rfl) ⟨762755, by rfl⟩ : syracuseStep 1017007 = 1525511) B1525511
theorem B1017031 : Blo 1016603 1017031 := bstep (se 1 (by rfl) ⟨762773, by rfl⟩ : syracuseStep 1017031 = 1525547) B1525547
theorem B1017051 : Blo 1016603 1017051 := bstep (se 1 (by rfl) ⟨762788, by rfl⟩ : syracuseStep 1017051 = 1525577) B1525577
theorem B1017127 : Blo 1016603 1017127 := bstep (se 1 (by rfl) ⟨762845, by rfl⟩ : syracuseStep 1017127 = 1525691) B1525691
theorem B1017167 : Blo 1016603 1017167 := bstep (se 1 (by rfl) ⟨762875, by rfl⟩ : syracuseStep 1017167 = 1525751) B1525751
theorem B1017183 : Blo 1016603 1017183 := bstep (se 1 (by rfl) ⟨762887, by rfl⟩ : syracuseStep 1017183 = 1525775) B1525775
theorem B6522227 : Blo 1016603 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B1017211 : Blo 1016603 1017211 := bstep (se 1 (by rfl) ⟨762908, by rfl⟩ : syracuseStep 1017211 = 1525817) B1525817
theorem B1017263 : Blo 1016603 1017263 := bstep (se 1 (by rfl) ⟨762947, by rfl⟩ : syracuseStep 1017263 = 1525895) B1525895
theorem B1017287 : Blo 1016603 1017287 := bstep (se 1 (by rfl) ⟨762965, by rfl⟩ : syracuseStep 1017287 = 1525931) B1525931
theorem B3442121 : Blo 1016603 3442121 := bstep (se 2 (by rfl) ⟨1290795, by rfl⟩ : syracuseStep 3442121 = 2581591) B2581591
theorem B1017307 : Blo 1016603 1017307 := bstep (se 1 (by rfl) ⟨762980, by rfl⟩ : syracuseStep 1017307 = 1525961) B1525961
theorem B1934857 : Blo 1016603 1934857 := bstep (se 2 (by rfl) ⟨725571, by rfl⟩ : syracuseStep 1934857 = 1451143) B1451143
theorem B2295305 : Blo 1016603 2295305 := bstep (se 2 (by rfl) ⟨860739, by rfl⟩ : syracuseStep 2295305 = 1721479) B1721479
theorem B1017383 : Blo 1016603 1017383 := bstep (se 1 (by rfl) ⟨763037, by rfl⟩ : syracuseStep 1017383 = 1526075) B1526075
theorem B1017423 : Blo 1016603 1017423 := bstep (se 1 (by rfl) ⟨763067, by rfl⟩ : syracuseStep 1017423 = 1526135) B1526135
theorem B1017439 : Blo 1016603 1017439 := bstep (se 1 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 1017439 = 1526159) B1526159
theorem B1017467 : Blo 1016603 1017467 := bstep (se 1 (by rfl) ⟨763100, by rfl⟩ : syracuseStep 1017467 = 1526201) B1526201
theorem B1017519 : Blo 1016603 1017519 := bstep (se 1 (by rfl) ⟨763139, by rfl⟩ : syracuseStep 1017519 = 1526279) B1526279
theorem B1017543 : Blo 1016603 1017543 := bstep (se 1 (by rfl) ⟨763157, by rfl⟩ : syracuseStep 1017543 = 1526315) B1526315
theorem B3442391 : Blo 1016603 3442391 := bstep (se 1 (by rfl) ⟨2581793, by rfl⟩ : syracuseStep 3442391 = 5163587) B5163587
theorem B1017563 : Blo 1016603 1017563 := bstep (se 1 (by rfl) ⟨763172, by rfl⟩ : syracuseStep 1017563 = 1526345) B1526345
theorem B1017639 : Blo 1016603 1017639 := bstep (se 1 (by rfl) ⟨763229, by rfl⟩ : syracuseStep 1017639 = 1526459) B1526459
theorem B6194987 : Blo 1016603 6194987 := bstep (se 1 (by rfl) ⟨4646240, by rfl⟩ : syracuseStep 6194987 = 9292481) B9292481
theorem B1017679 : Blo 1016603 1017679 := bstep (se 1 (by rfl) ⟨763259, by rfl⟩ : syracuseStep 1017679 = 1526519) B1526519
theorem B1017695 : Blo 1016603 1017695 := bstep (se 1 (by rfl) ⟨763271, by rfl⟩ : syracuseStep 1017695 = 1526543) B1526543
theorem B17631071 : Blo 1016603 17631071 := bstep (se 1 (by rfl) ⟨13223303, by rfl⟩ : syracuseStep 17631071 = 26446607) B26446607
theorem B2295647 : Blo 1016603 2295647 := bstep (se 1 (by rfl) ⟨1721735, by rfl⟩ : syracuseStep 2295647 = 3443471) B3443471
theorem B1017723 : Blo 1016603 1017723 := bstep (se 1 (by rfl) ⟨763292, by rfl⟩ : syracuseStep 1017723 = 1526585) B1526585
theorem B7735175 : Blo 1016603 7735175 := bstep (se 1 (by rfl) ⟨5801381, by rfl⟩ : syracuseStep 7735175 = 11602763) B11602763
theorem B1017775 : Blo 1016603 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B3442607 : Blo 1016603 3442607 := bstep (se 1 (by rfl) ⟨2581955, by rfl⟩ : syracuseStep 3442607 = 5163911) B5163911
theorem B1017799 : Blo 1016603 1017799 := bstep (se 1 (by rfl) ⟨763349, by rfl⟩ : syracuseStep 1017799 = 1526699) B1526699
theorem B1017819 : Blo 1016603 1017819 := bstep (se 1 (by rfl) ⟨763364, by rfl⟩ : syracuseStep 1017819 = 1526729) B1526729
theorem B2295827 : Blo 1016603 2295827 := bstep (se 1 (by rfl) ⟨1721870, by rfl⟩ : syracuseStep 2295827 = 3443741) B3443741
theorem B1017895 : Blo 1016603 1017895 := bstep (se 1 (by rfl) ⟨763421, by rfl⟩ : syracuseStep 1017895 = 1526843) B1526843
theorem B5507129 : Blo 1016603 5507129 := bstep (se 2 (by rfl) ⟨2065173, by rfl⟩ : syracuseStep 5507129 = 4130347) B4130347
theorem B1017935 : Blo 1016603 1017935 := bstep (se 1 (by rfl) ⟨763451, by rfl⟩ : syracuseStep 1017935 = 1526903) B1526903
theorem B1017951 : Blo 1016603 1017951 := bstep (se 1 (by rfl) ⟨763463, by rfl⟩ : syracuseStep 1017951 = 1526927) B1526927
theorem B5146739 : Blo 1016603 5146739 := bstep (se 1 (by rfl) ⟨3860054, by rfl⟩ : syracuseStep 5146739 = 7720109) B7720109
theorem B1017979 : Blo 1016603 1017979 := bstep (se 1 (by rfl) ⟨763484, by rfl⟩ : syracuseStep 1017979 = 1526969) B1526969
theorem B1018031 : Blo 1016603 1018031 := bstep (se 1 (by rfl) ⟨763523, by rfl⟩ : syracuseStep 1018031 = 1527047) B1527047
theorem B1018055 : Blo 1016603 1018055 := bstep (se 1 (by rfl) ⟨763541, by rfl⟩ : syracuseStep 1018055 = 1527083) B1527083
theorem B1935571 : Blo 1016603 1935571 := bstep (se 1 (by rfl) ⟨1451678, by rfl⟩ : syracuseStep 1935571 = 2903357) B2903357
theorem B1018075 : Blo 1016603 1018075 := bstep (se 1 (by rfl) ⟨763556, by rfl⟩ : syracuseStep 1018075 = 1527113) B1527113
theorem B1018151 : Blo 1016603 1018151 := bstep (se 1 (by rfl) ⟨763613, by rfl⟩ : syracuseStep 1018151 = 1527227) B1527227
theorem B1018191 : Blo 1016603 1018191 := bstep (se 1 (by rfl) ⟨763643, by rfl⟩ : syracuseStep 1018191 = 1527287) B1527287
theorem B1018207 : Blo 1016603 1018207 := bstep (se 1 (by rfl) ⟨763655, by rfl⟩ : syracuseStep 1018207 = 1527311) B1527311
theorem B2296169 : Blo 1016603 2296169 := bstep (se 2 (by rfl) ⟨861063, by rfl⟩ : syracuseStep 2296169 = 1722127) B1722127
theorem B1018235 : Blo 1016603 1018235 := bstep (se 1 (by rfl) ⟨763676, by rfl⟩ : syracuseStep 1018235 = 1527353) B1527353
theorem B1018287 : Blo 1016603 1018287 := bstep (se 1 (by rfl) ⟨763715, by rfl⟩ : syracuseStep 1018287 = 1527431) B1527431
theorem B1018311 : Blo 1016603 1018311 := bstep (se 1 (by rfl) ⟨763733, by rfl⟩ : syracuseStep 1018311 = 1527467) B1527467
theorem B1018331 : Blo 1016603 1018331 := bstep (se 1 (by rfl) ⟨763748, by rfl⟩ : syracuseStep 1018331 = 1527497) B1527497
theorem B1018407 : Blo 1016603 1018407 := bstep (se 1 (by rfl) ⟨763805, by rfl⟩ : syracuseStep 1018407 = 1527611) B1527611
theorem B1018447 : Blo 1016603 1018447 := bstep (se 1 (by rfl) ⟨763835, by rfl⟩ : syracuseStep 1018447 = 1527671) B1527671
theorem B2067023 : Blo 1016603 2067023 := bstep (se 1 (by rfl) ⟨1550267, by rfl⟩ : syracuseStep 2067023 = 3100535) B3100535
theorem B1018463 : Blo 1016603 1018463 := bstep (se 1 (by rfl) ⟨763847, by rfl⟩ : syracuseStep 1018463 = 1527695) B1527695
theorem B1018491 : Blo 1016603 1018491 := bstep (se 1 (by rfl) ⟨763868, by rfl⟩ : syracuseStep 1018491 = 1527737) B1527737
theorem B1018543 : Blo 1016603 1018543 := bstep (se 1 (by rfl) ⟨763907, by rfl⟩ : syracuseStep 1018543 = 1527815) B1527815
theorem B1018567 : Blo 1016603 1018567 := bstep (se 1 (by rfl) ⟨763925, by rfl⟩ : syracuseStep 1018567 = 1527851) B1527851
theorem B1018587 : Blo 1016603 1018587 := bstep (se 1 (by rfl) ⟨763940, by rfl⟩ : syracuseStep 1018587 = 1527881) B1527881
theorem B13208293 : Blo 1016603 13208293 := bstep (se 4 (by rfl) ⟨1238277, by rfl⟩ : syracuseStep 13208293 = 2476555) B2476555
theorem B1018663 : Blo 1016603 1018663 := bstep (se 1 (by rfl) ⟨763997, by rfl⟩ : syracuseStep 1018663 = 1527995) B1527995
theorem B1018703 : Blo 1016603 1018703 := bstep (se 1 (by rfl) ⟨764027, by rfl⟩ : syracuseStep 1018703 = 1528055) B1528055
theorem B1018719 : Blo 1016603 1018719 := bstep (se 1 (by rfl) ⟨764039, by rfl⟩ : syracuseStep 1018719 = 1528079) B1528079
theorem B1018747 : Blo 1016603 1018747 := bstep (se 1 (by rfl) ⟨764060, by rfl⟩ : syracuseStep 1018747 = 1528121) B1528121
theorem B1018799 : Blo 1016603 1018799 := bstep (se 1 (by rfl) ⟨764099, by rfl⟩ : syracuseStep 1018799 = 1528199) B1528199
theorem B1936315 : Blo 1016603 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B1018823 : Blo 1016603 1018823 := bstep (se 1 (by rfl) ⟨764117, by rfl⟩ : syracuseStep 1018823 = 1528235) B1528235
theorem B1018843 : Blo 1016603 1018843 := bstep (se 1 (by rfl) ⟨764132, by rfl⟩ : syracuseStep 1018843 = 1528265) B1528265
theorem B1018919 : Blo 1016603 1018919 := bstep (se 1 (by rfl) ⟨764189, by rfl⟩ : syracuseStep 1018919 = 1528379) B1528379
theorem B1018959 : Blo 1016603 1018959 := bstep (se 1 (by rfl) ⟨764219, by rfl⟩ : syracuseStep 1018959 = 1528439) B1528439
theorem B1018975 : Blo 1016603 1018975 := bstep (se 1 (by rfl) ⟨764231, by rfl⟩ : syracuseStep 1018975 = 1528463) B1528463
theorem B1019003 : Blo 1016603 1019003 := bstep (se 1 (by rfl) ⟨764252, by rfl⟩ : syracuseStep 1019003 = 1528505) B1528505
theorem B1019055 : Blo 1016603 1019055 := bstep (se 1 (by rfl) ⟨764291, by rfl⟩ : syracuseStep 1019055 = 1528583) B1528583
theorem B1019079 : Blo 1016603 1019079 := bstep (se 1 (by rfl) ⟨764309, by rfl⟩ : syracuseStep 1019079 = 1528619) B1528619
theorem B1019099 : Blo 1016603 1019099 := bstep (se 1 (by rfl) ⟨764324, by rfl⟩ : syracuseStep 1019099 = 1528649) B1528649
theorem B1019175 : Blo 1016603 1019175 := bstep (se 1 (by rfl) ⟨764381, by rfl⟩ : syracuseStep 1019175 = 1528763) B1528763
theorem B1019215 : Blo 1016603 1019215 := bstep (se 1 (by rfl) ⟨764411, by rfl⟩ : syracuseStep 1019215 = 1528823) B1528823
theorem B1019231 : Blo 1016603 1019231 := bstep (se 1 (by rfl) ⟨764423, by rfl⟩ : syracuseStep 1019231 = 1528847) B1528847
theorem B1019259 : Blo 1016603 1019259 := bstep (se 1 (by rfl) ⟨764444, by rfl⟩ : syracuseStep 1019259 = 1528889) B1528889
theorem B1936801 : Blo 1016603 1936801 := bstep (se 2 (by rfl) ⟨726300, by rfl⟩ : syracuseStep 1936801 = 1452601) B1452601
theorem B1019311 : Blo 1016603 1019311 := bstep (se 1 (by rfl) ⟨764483, by rfl⟩ : syracuseStep 1019311 = 1528967) B1528967
theorem B1019335 : Blo 1016603 1019335 := bstep (se 1 (by rfl) ⟨764501, by rfl⟩ : syracuseStep 1019335 = 1529003) B1529003
theorem B1019355 : Blo 1016603 1019355 := bstep (se 1 (by rfl) ⟨764516, by rfl⟩ : syracuseStep 1019355 = 1529033) B1529033
theorem B1019431 : Blo 1016603 1019431 := bstep (se 1 (by rfl) ⟨764573, by rfl⟩ : syracuseStep 1019431 = 1529147) B1529147
theorem B1019471 : Blo 1016603 1019471 := bstep (se 1 (by rfl) ⟨764603, by rfl⟩ : syracuseStep 1019471 = 1529207) B1529207
theorem B1019487 : Blo 1016603 1019487 := bstep (se 1 (by rfl) ⟨764615, by rfl⟩ : syracuseStep 1019487 = 1529231) B1529231
theorem B1019515 : Blo 1016603 1019515 := bstep (se 1 (by rfl) ⟨764636, by rfl⟩ : syracuseStep 1019515 = 1529273) B1529273
theorem B1019567 : Blo 1016603 1019567 := bstep (se 1 (by rfl) ⟨764675, by rfl⟩ : syracuseStep 1019567 = 1529351) B1529351
theorem B44011187 : Blo 1016603 44011187 := bstep (se 1 (by rfl) ⟨33008390, by rfl⟩ : syracuseStep 44011187 = 66016781) B66016781
theorem B1019591 : Blo 1016603 1019591 := bstep (se 1 (by rfl) ⟨764693, by rfl⟩ : syracuseStep 1019591 = 1529387) B1529387
theorem B5148359 : Blo 1016603 5148359 := bstep (se 1 (by rfl) ⟨3861269, by rfl⟩ : syracuseStep 5148359 = 7722539) B7722539
theorem B1019611 : Blo 1016603 1019611 := bstep (se 1 (by rfl) ⟨764708, by rfl⟩ : syracuseStep 1019611 = 1529417) B1529417
theorem B11013869 : Blo 1016603 11013869 := bstep (se 3 (by rfl) ⟨2065100, by rfl⟩ : syracuseStep 11013869 = 4130201) B4130201
theorem B5508857 : Blo 1016603 5508857 := bstep (se 2 (by rfl) ⟨2065821, by rfl⟩ : syracuseStep 5508857 = 4131643) B4131643
theorem B1019687 : Blo 1016603 1019687 := bstep (se 1 (by rfl) ⟨764765, by rfl⟩ : syracuseStep 1019687 = 1529531) B1529531
theorem B1019727 : Blo 1016603 1019727 := bstep (se 1 (by rfl) ⟨764795, by rfl⟩ : syracuseStep 1019727 = 1529591) B1529591
theorem B1019743 : Blo 1016603 1019743 := bstep (se 1 (by rfl) ⟨764807, by rfl⟩ : syracuseStep 1019743 = 1529615) B1529615
theorem B6360941 : Blo 1016603 6360941 := bstep (se 3 (by rfl) ⟨1192676, by rfl⟩ : syracuseStep 6360941 = 2385353) B2385353
theorem B1019771 : Blo 1016603 1019771 := bstep (se 1 (by rfl) ⟨764828, by rfl⟩ : syracuseStep 1019771 = 1529657) B1529657
theorem B3870625 : Blo 1016603 3870625 := bstep (se 2 (by rfl) ⟨1451484, by rfl⟩ : syracuseStep 3870625 = 2902969) B2902969
theorem B23564195 : Blo 1016603 23564195 := bstep (se 1 (by rfl) ⟨17673146, by rfl⟩ : syracuseStep 23564195 = 35346293) B35346293
theorem B1019823 : Blo 1016603 1019823 := bstep (se 1 (by rfl) ⟨764867, by rfl⟩ : syracuseStep 1019823 = 1529735) B1529735
theorem B1019847 : Blo 1016603 1019847 := bstep (se 1 (by rfl) ⟨764885, by rfl⟩ : syracuseStep 1019847 = 1529771) B1529771
theorem B1019867 : Blo 1016603 1019867 := bstep (se 1 (by rfl) ⟨764900, by rfl⟩ : syracuseStep 1019867 = 1529801) B1529801
theorem B1937371 : Blo 1016603 1937371 := bstep (se 1 (by rfl) ⟨1453028, by rfl⟩ : syracuseStep 1937371 = 2906057) B2906057
theorem B1019943 : Blo 1016603 1019943 := bstep (se 1 (by rfl) ⟨764957, by rfl⟩ : syracuseStep 1019943 = 1529915) B1529915
theorem B1019983 : Blo 1016603 1019983 := bstep (se 1 (by rfl) ⟨764987, by rfl⟩ : syracuseStep 1019983 = 1529975) B1529975
theorem B1019999 : Blo 1016603 1019999 := bstep (se 1 (by rfl) ⟨764999, by rfl⟩ : syracuseStep 1019999 = 1529999) B1529999
theorem B1020027 : Blo 1016603 1020027 := bstep (se 1 (by rfl) ⟨765020, by rfl⟩ : syracuseStep 1020027 = 1530041) B1530041
theorem B1020079 : Blo 1016603 1020079 := bstep (se 1 (by rfl) ⟨765059, by rfl⟩ : syracuseStep 1020079 = 1530119) B1530119
theorem B1020103 : Blo 1016603 1020103 := bstep (se 1 (by rfl) ⟨765077, by rfl⟩ : syracuseStep 1020103 = 1530155) B1530155
theorem B1020123 : Blo 1016603 1020123 := bstep (se 1 (by rfl) ⟨765092, by rfl⟩ : syracuseStep 1020123 = 1530185) B1530185
theorem B1020199 : Blo 1016603 1020199 := bstep (se 1 (by rfl) ⟨765149, by rfl⟩ : syracuseStep 1020199 = 1530299) B1530299
theorem B1020239 : Blo 1016603 1020239 := bstep (se 1 (by rfl) ⟨765179, by rfl⟩ : syracuseStep 1020239 = 1530359) B1530359
theorem B5509463 : Blo 1016603 5509463 := bstep (se 1 (by rfl) ⟨4132097, by rfl⟩ : syracuseStep 5509463 = 8264195) B8264195
theorem B1020255 : Blo 1016603 1020255 := bstep (se 1 (by rfl) ⟨765191, by rfl⟩ : syracuseStep 1020255 = 1530383) B1530383
theorem B1020283 : Blo 1016603 1020283 := bstep (se 1 (by rfl) ⟨765212, by rfl⟩ : syracuseStep 1020283 = 1530425) B1530425
theorem B1020335 : Blo 1016603 1020335 := bstep (se 1 (by rfl) ⟨765251, by rfl⟩ : syracuseStep 1020335 = 1530503) B1530503
theorem B1020359 : Blo 1016603 1020359 := bstep (se 1 (by rfl) ⟨765269, by rfl⟩ : syracuseStep 1020359 = 1530539) B1530539
theorem B1020379 : Blo 1016603 1020379 := bstep (se 1 (by rfl) ⟨765284, by rfl⟩ : syracuseStep 1020379 = 1530569) B1530569
theorem B3576329 : Blo 1016603 3576329 := bstep (se 2 (by rfl) ⟨1341123, by rfl⟩ : syracuseStep 3576329 = 2682247) B2682247
theorem B1020455 : Blo 1016603 1020455 := bstep (se 1 (by rfl) ⟨765341, by rfl⟩ : syracuseStep 1020455 = 1530683) B1530683
theorem B1020495 : Blo 1016603 1020495 := bstep (se 1 (by rfl) ⟨765371, by rfl⟩ : syracuseStep 1020495 = 1530743) B1530743
theorem B1020511 : Blo 1016603 1020511 := bstep (se 1 (by rfl) ⟨765383, by rfl⟩ : syracuseStep 1020511 = 1530767) B1530767
theorem B1020539 : Blo 1016603 1020539 := bstep (se 1 (by rfl) ⟨765404, by rfl⟩ : syracuseStep 1020539 = 1530809) B1530809
theorem B1020591 : Blo 1016603 1020591 := bstep (se 1 (by rfl) ⟨765443, by rfl⟩ : syracuseStep 1020591 = 1530887) B1530887
theorem B3871583 : Blo 1016603 3871583 := bstep (se 1 (by rfl) ⟨2903687, by rfl⟩ : syracuseStep 3871583 = 5807375) B5807375
theorem B8819563 : Blo 1016603 8819563 := bstep (se 1 (by rfl) ⟨6614672, by rfl⟩ : syracuseStep 8819563 = 13229345) B13229345
theorem B3871597 : Blo 1016603 3871597 := bstep (se 3 (by rfl) ⟨725924, by rfl⟩ : syracuseStep 3871597 = 1451849) B1451849
theorem B6525917 : Blo 1016603 6525917 := bstep (se 3 (by rfl) ⟨1223609, by rfl⟩ : syracuseStep 6525917 = 2447219) B2447219
theorem B5805209 : Blo 1016603 5805209 := bstep (se 2 (by rfl) ⟨2176953, by rfl⟩ : syracuseStep 5805209 = 4353907) B4353907
theorem B3871901 : Blo 1016603 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B6526145 : Blo 1016603 6526145 := bstep (se 2 (by rfl) ⟨2447304, by rfl⟩ : syracuseStep 6526145 = 4894609) B4894609
theorem B4953487 : Blo 1016603 4953487 := bstep (se 1 (by rfl) ⟨3715115, by rfl⟩ : syracuseStep 4953487 = 7430231) B7430231
theorem B5805665 : Blo 1016603 5805665 := bstep (se 2 (by rfl) ⟨2177124, by rfl⟩ : syracuseStep 5805665 = 4354249) B4354249
theorem B3872555 : Blo 1016603 3872555 := bstep (se 1 (by rfl) ⟨2904416, by rfl⟩ : syracuseStep 3872555 = 5808833) B5808833
theorem B2037857 : Blo 1016603 2037857 := bstep (se 2 (by rfl) ⟨764196, by rfl⟩ : syracuseStep 2037857 = 1528393) B1528393
theorem B6199411 : Blo 1016603 6199411 := bstep (se 1 (by rfl) ⟨4649558, by rfl⟩ : syracuseStep 6199411 = 9299117) B9299117
theorem B7739549 : Blo 1016603 7739549 := bstep (se 3 (by rfl) ⟨1451165, by rfl⟩ : syracuseStep 7739549 = 2902331) B2902331
theorem B14686595 : Blo 1016603 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B8264555 : Blo 1016603 8264555 := bstep (se 1 (by rfl) ⟨6198416, by rfl⟩ : syracuseStep 8264555 = 12396833) B12396833
theorem B5807123 : Blo 1016603 5807123 := bstep (se 1 (by rfl) ⟨4355342, by rfl⟩ : syracuseStep 5807123 = 8710685) B8710685
theorem B12393719 : Blo 1016603 12393719 := bstep (se 1 (by rfl) ⟨9295289, by rfl⟩ : syracuseStep 12393719 = 18590579) B18590579
theorem B20913497 : Blo 1016603 20913497 := bstep (se 2 (by rfl) ⟨7842561, by rfl⟩ : syracuseStep 20913497 = 15685123) B15685123
theorem B3874513 : Blo 1016603 3874513 := bstep (se 2 (by rfl) ⟨1452942, by rfl⟩ : syracuseStep 3874513 = 2905885) B2905885
theorem B6528863 : Blo 1016603 6528863 := bstep (se 1 (by rfl) ⟨4896647, by rfl⟩ : syracuseStep 6528863 = 9793295) B9793295
theorem B9772919 : Blo 1016603 9772919 := bstep (se 1 (by rfl) ⟨7329689, by rfl⟩ : syracuseStep 9772919 = 14659379) B14659379
theorem B1449947 : Blo 1016603 1449947 := bstep (se 1 (by rfl) ⟨1087460, by rfl⟩ : syracuseStep 1449947 = 2174921) B2174921
theorem B3874817 : Blo 1016603 3874817 := bstep (se 2 (by rfl) ⟨1453056, by rfl⟩ : syracuseStep 3874817 = 2906113) B2906113
theorem B3678223 : Blo 1016603 3678223 := bstep (se 1 (by rfl) ⟨2758667, by rfl⟩ : syracuseStep 3678223 = 5517335) B5517335
theorem B33103889 : Blo 1016603 33103889 := bstep (se 2 (by rfl) ⟨12413958, by rfl⟩ : syracuseStep 33103889 = 24827917) B24827917
theorem B1450505 : Blo 1016603 1450505 := bstep (se 2 (by rfl) ⟨543939, by rfl⟩ : syracuseStep 1450505 = 1087879) B1087879
theorem B1286695 : Blo 1016603 1286695 := bstep (se 1 (by rfl) ⟨965021, by rfl⟩ : syracuseStep 1286695 = 1930043) B1930043
theorem B1287019 : Blo 1016603 1287019 := bstep (se 1 (by rfl) ⟨965264, by rfl⟩ : syracuseStep 1287019 = 1930529) B1930529
theorem B7742465 : Blo 1016603 7742465 := bstep (se 2 (by rfl) ⟨2903424, by rfl⟩ : syracuseStep 7742465 = 5806849) B5806849
theorem B11183123 : Blo 1016603 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B1287247 : Blo 1016603 1287247 := bstep (se 1 (by rfl) ⟨965435, by rfl⟩ : syracuseStep 1287247 = 1930871) B1930871
theorem B4891727 : Blo 1016603 4891727 := bstep (se 1 (by rfl) ⟨3668795, by rfl⟩ : syracuseStep 4891727 = 7337591) B7337591
theorem B1549561 : Blo 1016603 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B1451371 : Blo 1016603 1451371 := bstep (se 1 (by rfl) ⟨1088528, by rfl⟩ : syracuseStep 1451371 = 2177057) B2177057
theorem B5154191 : Blo 1016603 5154191 := bstep (se 1 (by rfl) ⟨3865643, by rfl⟩ : syracuseStep 5154191 = 7731287) B7731287
theorem B26060291 : Blo 1016603 26060291 := bstep (se 1 (by rfl) ⟨19545218, by rfl⟩ : syracuseStep 26060291 = 39090437) B39090437
theorem B5810039 : Blo 1016603 5810039 := bstep (se 1 (by rfl) ⟨4357529, by rfl⟩ : syracuseStep 5810039 = 8715059) B8715059
theorem B11020225 : Blo 1016603 11020225 := bstep (se 2 (by rfl) ⟨4132584, by rfl⟩ : syracuseStep 11020225 = 8265169) B8265169
theorem B2173007 : Blo 1016603 2173007 := bstep (se 1 (by rfl) ⟨1629755, by rfl⟩ : syracuseStep 2173007 = 3259511) B3259511
theorem B5810291 : Blo 1016603 5810291 := bstep (se 1 (by rfl) ⟨4357718, by rfl⟩ : syracuseStep 5810291 = 8715437) B8715437
theorem B1288315 : Blo 1016603 1288315 := bstep (se 1 (by rfl) ⟨966236, by rfl⟩ : syracuseStep 1288315 = 1932473) B1932473
theorem B1288543 : Blo 1016603 1288543 := bstep (se 1 (by rfl) ⟨966407, by rfl⟩ : syracuseStep 1288543 = 1932815) B1932815
theorem B4893209 : Blo 1016603 4893209 := bstep (se 2 (by rfl) ⟨1834953, by rfl⟩ : syracuseStep 4893209 = 3669907) B3669907
theorem B2796221 : Blo 1016603 2796221 := bstep (se 3 (by rfl) ⟨524291, by rfl⟩ : syracuseStep 2796221 = 1048583) B1048583
theorem B6531785 : Blo 1016603 6531785 := bstep (se 2 (by rfl) ⟨2449419, by rfl⟩ : syracuseStep 6531785 = 4898839) B4898839
theorem B2173871 : Blo 1016603 2173871 := bstep (se 1 (by rfl) ⟨1630403, by rfl⟩ : syracuseStep 2173871 = 3260807) B3260807
theorem B1289135 : Blo 1016603 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B8269229 : Blo 1016603 8269229 := bstep (se 3 (by rfl) ⟨1550480, by rfl⟩ : syracuseStep 8269229 = 3100961) B3100961
theorem B5156297 : Blo 1016603 5156297 := bstep (se 2 (by rfl) ⟨1933611, by rfl⟩ : syracuseStep 5156297 = 3867223) B3867223
theorem B1716187 : Blo 1016603 1716187 := bstep (se 1 (by rfl) ⟨1287140, by rfl⟩ : syracuseStep 1716187 = 2574281) B2574281
theorem B5156945 : Blo 1016603 5156945 := bstep (se 2 (by rfl) ⟨1933854, by rfl⟩ : syracuseStep 5156945 = 3867709) B3867709
theorem B1716815 : Blo 1016603 1716815 := bstep (se 1 (by rfl) ⟨1287611, by rfl⟩ : syracuseStep 1716815 = 2575223) B2575223
theorem B2896523 : Blo 1016603 2896523 := bstep (se 1 (by rfl) ⟨2172392, by rfl⟩ : syracuseStep 2896523 = 4344785) B4344785
theorem B4895417 : Blo 1016603 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B16495433 : Blo 1016603 16495433 := bstep (se 2 (by rfl) ⟨6185787, by rfl⟩ : syracuseStep 16495433 = 12371575) B12371575
theorem B10433555 : Blo 1016603 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B1487911 : Blo 1016603 1487911 := bstep (se 1 (by rfl) ⟨1115933, by rfl⟩ : syracuseStep 1487911 = 2231867) B2231867
theorem B3912875 : Blo 1016603 3912875 := bstep (se 1 (by rfl) ⟨2934656, by rfl⟩ : syracuseStep 3912875 = 5869313) B5869313
theorem B7746839 : Blo 1016603 7746839 := bstep (se 1 (by rfl) ⟨5810129, by rfl⟩ : syracuseStep 7746839 = 11620259) B11620259
theorem B2176399 : Blo 1016603 2176399 := bstep (se 1 (by rfl) ⟨1632299, by rfl⟩ : syracuseStep 2176399 = 3264599) B3264599
theorem B1717679 : Blo 1016603 1717679 := bstep (se 1 (by rfl) ⟨1288259, by rfl⟩ : syracuseStep 1717679 = 2576519) B2576519
theorem B2176475 : Blo 1016603 2176475 := bstep (se 1 (by rfl) ⟨1632356, by rfl⟩ : syracuseStep 2176475 = 3264713) B3264713
theorem B1718111 : Blo 1016603 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B11155409 : Blo 1016603 11155409 := bstep (se 2 (by rfl) ⟨4183278, by rfl⟩ : syracuseStep 11155409 = 8366557) B8366557
theorem B6535475 : Blo 1016603 6535475 := bstep (se 1 (by rfl) ⟨4901606, by rfl⟩ : syracuseStep 6535475 = 9803213) B9803213
theorem B3258767 : Blo 1016603 3258767 := bstep (se 1 (by rfl) ⟨2444075, by rfl⟩ : syracuseStep 3258767 = 4888151) B4888151
theorem B1718671 : Blo 1016603 1718671 := bstep (se 1 (by rfl) ⟨1289003, by rfl⟩ : syracuseStep 1718671 = 2578007) B2578007
theorem B7748297 : Blo 1016603 7748297 := bstep (se 2 (by rfl) ⟨2905611, by rfl⟩ : syracuseStep 7748297 = 5811223) B5811223
theorem B3718007 : Blo 1016603 3718007 := bstep (se 1 (by rfl) ⟨2788505, by rfl⟩ : syracuseStep 3718007 = 5577011) B5577011
theorem B1719353 : Blo 1016603 1719353 := bstep (se 2 (by rfl) ⟨644757, by rfl⟩ : syracuseStep 1719353 = 1289515) B1289515
theorem B4963727 : Blo 1016603 4963727 := bstep (se 1 (by rfl) ⟨3722795, by rfl⟩ : syracuseStep 4963727 = 7445591) B7445591
theorem B1883657 : Blo 1016603 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B1720055 : Blo 1016603 1720055 := bstep (se 1 (by rfl) ⟨1290041, by rfl⟩ : syracuseStep 1720055 = 2580083) B2580083
theorem B13942543 : Blo 1016603 13942543 := bstep (se 1 (by rfl) ⟨10456907, by rfl⟩ : syracuseStep 13942543 = 20913815) B20913815
theorem B5881643 : Blo 1016603 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B8273927 : Blo 1016603 8273927 := bstep (se 1 (by rfl) ⟨6205445, by rfl⟩ : syracuseStep 8273927 = 12410891) B12410891
theorem B1720399 : Blo 1016603 1720399 := bstep (se 1 (by rfl) ⟨1290299, by rfl⟩ : syracuseStep 1720399 = 2580599) B2580599
theorem B1720649 : Blo 1016603 1720649 := bstep (se 2 (by rfl) ⟨645243, by rfl⟩ : syracuseStep 1720649 = 1290487) B1290487
theorem B5161481 : Blo 1016603 5161481 := bstep (se 2 (by rfl) ⟨1935555, by rfl⟩ : syracuseStep 5161481 = 3871111) B3871111
theorem B1721081 : Blo 1016603 1721081 := bstep (se 2 (by rfl) ⟨645405, by rfl⟩ : syracuseStep 1721081 = 1290811) B1290811
theorem B3261227 : Blo 1016603 3261227 := bstep (se 1 (by rfl) ⟨2445920, by rfl⟩ : syracuseStep 3261227 = 4891841) B4891841
theorem B2900897 : Blo 1016603 2900897 := bstep (se 2 (by rfl) ⟨1087836, by rfl⟩ : syracuseStep 2900897 = 2175673) B2175673
theorem B1721263 : Blo 1016603 1721263 := bstep (se 1 (by rfl) ⟨1290947, by rfl⟩ : syracuseStep 1721263 = 2581895) B2581895
theorem B1721351 : Blo 1016603 1721351 := bstep (se 1 (by rfl) ⟨1291013, by rfl⟩ : syracuseStep 1721351 = 2582027) B2582027
theorem B8700979 : Blo 1016603 8700979 := bstep (se 1 (by rfl) ⟨6525734, by rfl⟩ : syracuseStep 8700979 = 13051469) B13051469
theorem B17417267 : Blo 1016603 17417267 := bstep (se 1 (by rfl) ⟨13062950, by rfl⟩ : syracuseStep 17417267 = 26125901) B26125901
theorem B1524935 : Blo 1016603 1524935 := bstep (se 1 (by rfl) ⟨1143701, by rfl⟩ : syracuseStep 1524935 = 2287403) B2287403
theorem B1721695 : Blo 1016603 1721695 := bstep (se 1 (by rfl) ⟨1291271, by rfl⟩ : syracuseStep 1721695 = 2582543) B2582543
theorem B1525097 : Blo 1016603 1525097 := bstep (se 2 (by rfl) ⟨571911, by rfl⟩ : syracuseStep 1525097 = 1143823) B1143823
theorem B1525175 : Blo 1016603 1525175 := bstep (se 1 (by rfl) ⟨1143881, by rfl⟩ : syracuseStep 1525175 = 2287763) B2287763
theorem B1721783 : Blo 1016603 1721783 := bstep (se 1 (by rfl) ⟨1291337, by rfl⟩ : syracuseStep 1721783 = 2582675) B2582675
theorem B1525211 : Blo 1016603 1525211 := bstep (se 1 (by rfl) ⟨1143908, by rfl⟩ : syracuseStep 1525211 = 2287817) B2287817
theorem B2442761 : Blo 1016603 2442761 := bstep (se 2 (by rfl) ⟨916035, by rfl⟩ : syracuseStep 2442761 = 1832071) B1832071
theorem B2443115 : Blo 1016603 2443115 := bstep (se 1 (by rfl) ⟨1832336, by rfl⟩ : syracuseStep 2443115 = 3664673) B3664673
theorem B1525679 : Blo 1016603 1525679 := bstep (se 1 (by rfl) ⟨1144259, by rfl⟩ : syracuseStep 1525679 = 2288519) B2288519
theorem B5162939 : Blo 1016603 5162939 := bstep (se 1 (by rfl) ⟨3872204, by rfl⟩ : syracuseStep 5162939 = 7744409) B7744409
theorem B5883911 : Blo 1016603 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B1525769 : Blo 1016603 1525769 := bstep (se 2 (by rfl) ⟨572163, by rfl⟩ : syracuseStep 1525769 = 1144327) B1144327
theorem B1525799 : Blo 1016603 1525799 := bstep (se 1 (by rfl) ⟨1144349, by rfl⟩ : syracuseStep 1525799 = 2288699) B2288699
theorem B1525883 : Blo 1016603 1525883 := bstep (se 1 (by rfl) ⟨1144412, by rfl⟩ : syracuseStep 1525883 = 2288825) B2288825
theorem B1526009 : Blo 1016603 1526009 := bstep (se 2 (by rfl) ⟨572253, by rfl⟩ : syracuseStep 1526009 = 1144507) B1144507
theorem B1526111 : Blo 1016603 1526111 := bstep (se 1 (by rfl) ⟨1144583, by rfl⟩ : syracuseStep 1526111 = 2289167) B2289167
theorem B1526123 : Blo 1016603 1526123 := bstep (se 1 (by rfl) ⟨1144592, by rfl⟩ : syracuseStep 1526123 = 2289185) B2289185
theorem B1526351 : Blo 1016603 1526351 := bstep (se 1 (by rfl) ⟨1144763, by rfl⟩ : syracuseStep 1526351 = 2289527) B2289527
theorem B1526471 : Blo 1016603 1526471 := bstep (se 1 (by rfl) ⟨1144853, by rfl⟩ : syracuseStep 1526471 = 2289707) B2289707
theorem B3918665 : Blo 1016603 3918665 := bstep (se 2 (by rfl) ⟨1469499, by rfl⟩ : syracuseStep 3918665 = 2938999) B2938999
theorem B1526633 : Blo 1016603 1526633 := bstep (se 2 (by rfl) ⟨572487, by rfl⟩ : syracuseStep 1526633 = 1144975) B1144975
theorem B1526711 : Blo 1016603 1526711 := bstep (se 1 (by rfl) ⟨1145033, by rfl⟩ : syracuseStep 1526711 = 2290067) B2290067
theorem B1526747 : Blo 1016603 1526747 := bstep (se 1 (by rfl) ⟨1145060, by rfl⟩ : syracuseStep 1526747 = 2290121) B2290121
theorem B2444345 : Blo 1016603 2444345 := bstep (se 2 (by rfl) ⟨916629, by rfl⟩ : syracuseStep 2444345 = 1833259) B1833259
theorem B2903197 : Blo 1016603 2903197 := bstep (se 3 (by rfl) ⟨544349, by rfl⟩ : syracuseStep 2903197 = 1088699) B1088699
theorem B5164235 : Blo 1016603 5164235 := bstep (se 1 (by rfl) ⟨3873176, by rfl⟩ : syracuseStep 5164235 = 7746353) B7746353
theorem B2575759 : Blo 1016603 2575759 := bstep (se 1 (by rfl) ⟨1931819, by rfl⟩ : syracuseStep 2575759 = 3863639) B3863639
theorem B1527215 : Blo 1016603 1527215 := bstep (se 1 (by rfl) ⟨1145411, by rfl⟩ : syracuseStep 1527215 = 2290823) B2290823
theorem B2903539 : Blo 1016603 2903539 := bstep (se 1 (by rfl) ⟨2177654, by rfl⟩ : syracuseStep 2903539 = 4355309) B4355309
theorem B1527305 : Blo 1016603 1527305 := bstep (se 2 (by rfl) ⟨572739, by rfl⟩ : syracuseStep 1527305 = 1145479) B1145479
theorem B1527335 : Blo 1016603 1527335 := bstep (se 1 (by rfl) ⟨1145501, by rfl⟩ : syracuseStep 1527335 = 2291003) B2291003
theorem B1527419 : Blo 1016603 1527419 := bstep (se 1 (by rfl) ⟨1145564, by rfl⟩ : syracuseStep 1527419 = 2291129) B2291129
theorem B7720595 : Blo 1016603 7720595 := bstep (se 1 (by rfl) ⟨5790446, by rfl⟩ : syracuseStep 7720595 = 11580893) B11580893
theorem B11751101 : Blo 1016603 11751101 := bstep (se 3 (by rfl) ⟨2203331, by rfl⟩ : syracuseStep 11751101 = 4406663) B4406663
theorem B2576083 : Blo 1016603 2576083 := bstep (se 1 (by rfl) ⟨1932062, by rfl⟩ : syracuseStep 2576083 = 3864125) B3864125
theorem B1527545 : Blo 1016603 1527545 := bstep (se 2 (by rfl) ⟨572829, by rfl⟩ : syracuseStep 1527545 = 1145659) B1145659
theorem B1527647 : Blo 1016603 1527647 := bstep (se 1 (by rfl) ⟨1145735, by rfl⟩ : syracuseStep 1527647 = 2291471) B2291471
theorem B1527659 : Blo 1016603 1527659 := bstep (se 1 (by rfl) ⟨1145744, by rfl⟩ : syracuseStep 1527659 = 2291489) B2291489
theorem B12406715 : Blo 1016603 12406715 := bstep (se 1 (by rfl) ⟨9305036, by rfl⟩ : syracuseStep 12406715 = 18610073) B18610073
theorem B4182031 : Blo 1016603 4182031 := bstep (se 1 (by rfl) ⟨3136523, by rfl⟩ : syracuseStep 4182031 = 6273047) B6273047
theorem B1527887 : Blo 1016603 1527887 := bstep (se 1 (by rfl) ⟨1145915, by rfl⟩ : syracuseStep 1527887 = 2291831) B2291831
theorem B1528007 : Blo 1016603 1528007 := bstep (se 1 (by rfl) ⟨1146005, by rfl⟩ : syracuseStep 1528007 = 2292011) B2292011
theorem B1528169 : Blo 1016603 1528169 := bstep (se 2 (by rfl) ⟨573063, by rfl⟩ : syracuseStep 1528169 = 1146127) B1146127
theorem B1528247 : Blo 1016603 1528247 := bstep (se 1 (by rfl) ⟨1146185, by rfl⟩ : syracuseStep 1528247 = 2292371) B2292371
theorem B1528283 : Blo 1016603 1528283 := bstep (se 1 (by rfl) ⟨1146212, by rfl⟩ : syracuseStep 1528283 = 2292425) B2292425
theorem B5886445 : Blo 1016603 5886445 := bstep (se 3 (by rfl) ⟨1103708, by rfl⟩ : syracuseStep 5886445 = 2207417) B2207417
theorem B2577035 : Blo 1016603 2577035 := bstep (se 1 (by rfl) ⟨1932776, by rfl⟩ : syracuseStep 2577035 = 3865553) B3865553
theorem B1528751 : Blo 1016603 1528751 := bstep (se 1 (by rfl) ⟨1146563, by rfl⟩ : syracuseStep 1528751 = 2293127) B2293127
theorem B26432477 : Blo 1016603 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B1528841 : Blo 1016603 1528841 := bstep (se 2 (by rfl) ⟨573315, by rfl⟩ : syracuseStep 1528841 = 1146631) B1146631
theorem B1528871 : Blo 1016603 1528871 := bstep (se 1 (by rfl) ⟨1146653, by rfl⟩ : syracuseStep 1528871 = 2293307) B2293307
theorem B1528955 : Blo 1016603 1528955 := bstep (se 1 (by rfl) ⟨1146716, by rfl⟩ : syracuseStep 1528955 = 2293433) B2293433
theorem B1529081 : Blo 1016603 1529081 := bstep (se 2 (by rfl) ⟨573405, by rfl⟩ : syracuseStep 1529081 = 1146811) B1146811
theorem B1529183 : Blo 1016603 1529183 := bstep (se 1 (by rfl) ⟨1146887, by rfl⟩ : syracuseStep 1529183 = 2293775) B2293775
theorem B1529195 : Blo 1016603 1529195 := bstep (se 1 (by rfl) ⟨1146896, by rfl⟩ : syracuseStep 1529195 = 2293793) B2293793
theorem B1529423 : Blo 1016603 1529423 := bstep (se 1 (by rfl) ⟨1147067, by rfl⟩ : syracuseStep 1529423 = 2294135) B2294135
theorem B16307905 : Blo 1016603 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B1529543 : Blo 1016603 1529543 := bstep (se 1 (by rfl) ⟨1147157, by rfl⟩ : syracuseStep 1529543 = 2294315) B2294315
theorem B2578169 : Blo 1016603 2578169 := bstep (se 2 (by rfl) ⟨966813, by rfl⟩ : syracuseStep 2578169 = 1933627) B1933627
theorem B3102457 : Blo 1016603 3102457 := bstep (se 2 (by rfl) ⟨1163421, by rfl⟩ : syracuseStep 3102457 = 2326843) B2326843
theorem B1529705 : Blo 1016603 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B2578351 : Blo 1016603 2578351 := bstep (se 1 (by rfl) ⟨1933763, by rfl⟩ : syracuseStep 2578351 = 3867527) B3867527
theorem B1529783 : Blo 1016603 1529783 := bstep (se 1 (by rfl) ⟨1147337, by rfl⟩ : syracuseStep 1529783 = 2294675) B2294675
theorem B1529819 : Blo 1016603 1529819 := bstep (se 1 (by rfl) ⟨1147364, by rfl⟩ : syracuseStep 1529819 = 2294729) B2294729
theorem B10442789 : Blo 1016603 10442789 := bstep (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) B1958023
theorem B11032937 : Blo 1016603 11032937 := bstep (se 2 (by rfl) ⟨4137351, by rfl⟩ : syracuseStep 11032937 = 8274703) B8274703
theorem B2578817 : Blo 1016603 2578817 := bstep (se 2 (by rfl) ⟨967056, by rfl⟩ : syracuseStep 2578817 = 1934113) B1934113
theorem B1530287 : Blo 1016603 1530287 := bstep (se 1 (by rfl) ⟨1147715, by rfl⟩ : syracuseStep 1530287 = 2295431) B2295431
theorem B1530377 : Blo 1016603 1530377 := bstep (se 2 (by rfl) ⟨573891, by rfl⟩ : syracuseStep 1530377 = 1147783) B1147783
theorem B1530407 : Blo 1016603 1530407 := bstep (se 1 (by rfl) ⟨1147805, by rfl⟩ : syracuseStep 1530407 = 2295611) B2295611
theorem B4348475 : Blo 1016603 4348475 := bstep (se 1 (by rfl) ⟨3261356, by rfl⟩ : syracuseStep 4348475 = 6522713) B6522713
theorem B1530491 : Blo 1016603 1530491 := bstep (se 1 (by rfl) ⟨1147868, by rfl⟩ : syracuseStep 1530491 = 2295737) B2295737
theorem B3431051 : Blo 1016603 3431051 := bstep (se 1 (by rfl) ⟨2573288, by rfl⟩ : syracuseStep 3431051 = 5146577) B5146577
theorem B1530617 : Blo 1016603 1530617 := bstep (se 2 (by rfl) ⟨573981, by rfl⟩ : syracuseStep 1530617 = 1147963) B1147963
theorem B2579273 : Blo 1016603 2579273 := bstep (se 2 (by rfl) ⟨967227, by rfl⟩ : syracuseStep 2579273 = 1934455) B1934455
theorem B27908957 : Blo 1016603 27908957 := bstep (se 3 (by rfl) ⟨5232929, by rfl⟩ : syracuseStep 27908957 = 10465859) B10465859
theorem B1530719 : Blo 1016603 1530719 := bstep (se 1 (by rfl) ⟨1148039, by rfl⟩ : syracuseStep 1530719 = 2296079) B2296079
theorem B1530731 : Blo 1016603 1530731 := bstep (se 1 (by rfl) ⟨1148048, by rfl⟩ : syracuseStep 1530731 = 2296097) B2296097
theorem B7723997 : Blo 1016603 7723997 := bstep (se 3 (by rfl) ⟨1448249, by rfl⟩ : syracuseStep 7723997 = 2896499) B2896499
theorem B1793063 : Blo 1016603 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B2579627 : Blo 1016603 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B4349123 : Blo 1016603 4349123 := bstep (se 1 (by rfl) ⟨3261842, by rfl⟩ : syracuseStep 4349123 = 6523685) B6523685
theorem B3431969 : Blo 1016603 3431969 := bstep (se 2 (by rfl) ⟨1286988, by rfl⟩ : syracuseStep 3431969 = 2573977) B2573977
theorem B19553831 : Blo 1016603 19553831 := bstep (se 1 (by rfl) ⟨14665373, by rfl⟩ : syracuseStep 19553831 = 29330747) B29330747
theorem B3432185 : Blo 1016603 3432185 := bstep (se 2 (by rfl) ⟨1287069, by rfl⟩ : syracuseStep 3432185 = 2574139) B2574139
theorem B2350943 : Blo 1016603 2350943 := bstep (se 1 (by rfl) ⟨1763207, by rfl⟩ : syracuseStep 2350943 = 3526415) B3526415
theorem B2580407 : Blo 1016603 2580407 := bstep (se 1 (by rfl) ⟨1935305, by rfl⟩ : syracuseStep 2580407 = 3870611) B3870611
theorem B3432455 : Blo 1016603 3432455 := bstep (se 1 (by rfl) ⟨2574341, by rfl⟩ : syracuseStep 3432455 = 5148683) B5148683
theorem B3432563 : Blo 1016603 3432563 := bstep (se 1 (by rfl) ⟨2574422, by rfl⟩ : syracuseStep 3432563 = 5148845) B5148845
theorem B5792087 : Blo 1016603 5792087 := bstep (se 1 (by rfl) ⟨4344065, by rfl⟩ : syracuseStep 5792087 = 8688131) B8688131
theorem B39739747 : Blo 1016603 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B3432833 : Blo 1016603 3432833 := bstep (se 2 (by rfl) ⟨1287312, by rfl⟩ : syracuseStep 3432833 = 2574625) B2574625
theorem B3301775 : Blo 1016603 3301775 := bstep (se 1 (by rfl) ⟨2476331, by rfl⟩ : syracuseStep 3301775 = 4952663) B4952663
theorem B5890745 : Blo 1016603 5890745 := bstep (se 2 (by rfl) ⟨2209029, by rfl⟩ : syracuseStep 5890745 = 4418059) B4418059
theorem B2581409 : Blo 1016603 2581409 := bstep (se 2 (by rfl) ⟨968028, by rfl⟩ : syracuseStep 2581409 = 1936057) B1936057
theorem B3433643 : Blo 1016603 3433643 := bstep (se 1 (by rfl) ⟨2575232, by rfl⟩ : syracuseStep 3433643 = 5150465) B5150465
theorem B8479991 : Blo 1016603 8479991 := bstep (se 1 (by rfl) ⟨6359993, by rfl⟩ : syracuseStep 8479991 = 12719987) B12719987
theorem B2581865 : Blo 1016603 2581865 := bstep (se 2 (by rfl) ⟨968199, by rfl⟩ : syracuseStep 2581865 = 1936399) B1936399
theorem B3434183 : Blo 1016603 3434183 := bstep (se 1 (by rfl) ⟨2575637, by rfl⟩ : syracuseStep 3434183 = 5151275) B5151275
theorem B29812531 : Blo 1016603 29812531 := bstep (se 1 (by rfl) ⟨22359398, by rfl⟩ : syracuseStep 29812531 = 44718797) B44718797
theorem B2287547 : Blo 1016603 2287547 := bstep (se 1 (by rfl) ⟨1715660, by rfl⟩ : syracuseStep 2287547 = 3431321) B3431321
theorem B2287673 : Blo 1016603 2287673 := bstep (se 2 (by rfl) ⟨857877, by rfl⟩ : syracuseStep 2287673 = 1715755) B1715755
theorem B14706845 : Blo 1016603 14706845 := bstep (se 3 (by rfl) ⟨2757533, by rfl⟩ : syracuseStep 14706845 = 5515067) B5515067
theorem B4352267 : Blo 1016603 4352267 := bstep (se 1 (by rfl) ⟨3264200, by rfl⟩ : syracuseStep 4352267 = 6528401) B6528401
theorem B7432499 : Blo 1016603 7432499 := bstep (se 1 (by rfl) ⟨5574374, by rfl⟩ : syracuseStep 7432499 = 11148749) B11148749
theorem B2288015 : Blo 1016603 2288015 := bstep (se 1 (by rfl) ⟨1716011, by rfl⟩ : syracuseStep 2288015 = 3432023) B3432023
theorem B2583049 : Blo 1016603 2583049 := bstep (se 2 (by rfl) ⟨968643, by rfl⟩ : syracuseStep 2583049 = 1937287) B1937287
theorem B3435047 : Blo 1016603 3435047 := bstep (se 1 (by rfl) ⟨2576285, by rfl⟩ : syracuseStep 3435047 = 5152571) B5152571
theorem B3435155 : Blo 1016603 3435155 := bstep (se 1 (by rfl) ⟨2576366, by rfl⟩ : syracuseStep 3435155 = 5152733) B5152733
theorem B2288339 : Blo 1016603 2288339 := bstep (se 1 (by rfl) ⟨1716254, by rfl⟩ : syracuseStep 2288339 = 3432509) B3432509
theorem B3435371 : Blo 1016603 3435371 := bstep (se 1 (by rfl) ⟨2576528, by rfl⟩ : syracuseStep 3435371 = 5153057) B5153057
theorem B3435425 : Blo 1016603 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B3436019 : Blo 1016603 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B2289275 : Blo 1016603 2289275 := bstep (se 1 (by rfl) ⟨1716956, by rfl⟩ : syracuseStep 2289275 = 3433913) B3433913
theorem B11169413 : Blo 1016603 11169413 := bstep (se 4 (by rfl) ⟨1047132, by rfl⟩ : syracuseStep 11169413 = 2094265) B2094265
theorem B3862151 : Blo 1016603 3862151 := bstep (se 1 (by rfl) ⟨2896613, by rfl⟩ : syracuseStep 3862151 = 5793227) B5793227
theorem B22015709 : Blo 1016603 22015709 := bstep (se 3 (by rfl) ⟨4127945, by rfl⟩ : syracuseStep 22015709 = 8255891) B8255891
theorem B2289401 : Blo 1016603 2289401 := bstep (se 2 (by rfl) ⟨858525, by rfl⟩ : syracuseStep 2289401 = 1717051) B1717051
theorem B1961903 : Blo 1016603 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B2289671 : Blo 1016603 2289671 := bstep (se 1 (by rfl) ⟨1717253, by rfl⟩ : syracuseStep 2289671 = 3434507) B3434507
theorem B3436559 : Blo 1016603 3436559 := bstep (se 1 (by rfl) ⟨2577419, by rfl⟩ : syracuseStep 3436559 = 5154839) B5154839
theorem B2289743 : Blo 1016603 2289743 := bstep (se 1 (by rfl) ⟨1717307, by rfl⟩ : syracuseStep 2289743 = 3434615) B3434615
theorem B5501245 : Blo 1016603 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B2290139 : Blo 1016603 2290139 := bstep (se 1 (by rfl) ⟨1717604, by rfl⟩ : syracuseStep 2290139 = 3435209) B3435209
theorem B1634779 : Blo 1016603 1634779 := bstep (se 1 (by rfl) ⟨1226084, by rfl⟩ : syracuseStep 1634779 = 2452169) B2452169
theorem B3666491 : Blo 1016603 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B3437153 : Blo 1016603 3437153 := bstep (se 2 (by rfl) ⟨1288932, by rfl⟩ : syracuseStep 3437153 = 2577865) B2577865
theorem B2061217 : Blo 1016603 2061217 := bstep (se 2 (by rfl) ⟨772956, by rfl⟩ : syracuseStep 2061217 = 1545913) B1545913
theorem B2290607 : Blo 1016603 2290607 := bstep (se 1 (by rfl) ⟨1717955, by rfl⟩ : syracuseStep 2290607 = 3435911) B3435911
theorem B3863609 : Blo 1016603 3863609 := bstep (se 2 (by rfl) ⟨1448853, by rfl⟩ : syracuseStep 3863609 = 2897707) B2897707
theorem B1143931 : Blo 1016603 1143931 := bstep (se 1 (by rfl) ⟨857948, by rfl⟩ : syracuseStep 1143931 = 1715897) B1715897
theorem B16741529 : Blo 1016603 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B2290859 : Blo 1016603 2290859 := bstep (se 1 (by rfl) ⟨1718144, by rfl⟩ : syracuseStep 2290859 = 3436289) B3436289
theorem B3667139 : Blo 1016603 3667139 := bstep (se 1 (by rfl) ⟨2750354, by rfl⟩ : syracuseStep 3667139 = 5500709) B5500709
theorem B13071563 : Blo 1016603 13071563 := bstep (se 1 (by rfl) ⟨9803672, by rfl⟩ : syracuseStep 13071563 = 19607345) B19607345
theorem B29324753 : Blo 1016603 29324753 := bstep (se 2 (by rfl) ⟨10996782, by rfl⟩ : syracuseStep 29324753 = 21993565) B21993565
theorem B13399613 : Blo 1016603 13399613 := bstep (se 3 (by rfl) ⟨2512427, by rfl⟩ : syracuseStep 13399613 = 5024855) B5024855
theorem B1144399 : Blo 1016603 1144399 := bstep (se 1 (by rfl) ⟨858299, by rfl⟩ : syracuseStep 1144399 = 1716599) B1716599
theorem B24803009 : Blo 1016603 24803009 := bstep (se 2 (by rfl) ⟨9301128, by rfl⟩ : syracuseStep 24803009 = 18602257) B18602257
theorem B1832647 : Blo 1016603 1832647 := bstep (se 1 (by rfl) ⟨1374485, by rfl⟩ : syracuseStep 1832647 = 2748971) B2748971
theorem B2291399 : Blo 1016603 2291399 := bstep (se 1 (by rfl) ⟨1718549, by rfl⟩ : syracuseStep 2291399 = 3437099) B3437099
theorem B6518663 : Blo 1016603 6518663 := bstep (se 1 (by rfl) ⟨4888997, by rfl⟩ : syracuseStep 6518663 = 9777995) B9777995
theorem B12089249 : Blo 1016603 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B1144795 : Blo 1016603 1144795 := bstep (se 1 (by rfl) ⟨858596, by rfl⟩ : syracuseStep 1144795 = 1717193) B1717193
theorem B1931273 : Blo 1016603 1931273 := bstep (se 2 (by rfl) ⟨724227, by rfl⟩ : syracuseStep 1931273 = 1448455) B1448455
theorem B3438611 : Blo 1016603 3438611 := bstep (se 1 (by rfl) ⟨2578958, by rfl⟩ : syracuseStep 3438611 = 5157917) B5157917
theorem B1931303 : Blo 1016603 1931303 := bstep (se 1 (by rfl) ⟨1448477, by rfl⟩ : syracuseStep 1931303 = 2896955) B2896955
theorem B3438935 : Blo 1016603 3438935 := bstep (se 1 (by rfl) ⟨2579201, by rfl⟩ : syracuseStep 3438935 = 5158403) B5158403
theorem B9926999 : Blo 1016603 9926999 := bstep (se 1 (by rfl) ⟨7445249, by rfl⟩ : syracuseStep 9926999 = 14890499) B14890499
theorem B1145263 : Blo 1016603 1145263 := bstep (se 1 (by rfl) ⟨858947, by rfl⟩ : syracuseStep 1145263 = 1717895) B1717895
theorem B3865097 : Blo 1016603 3865097 := bstep (se 2 (by rfl) ⟨1449411, by rfl⟩ : syracuseStep 3865097 = 2898823) B2898823
theorem B4356641 : Blo 1016603 4356641 := bstep (se 2 (by rfl) ⟨1633740, by rfl⟩ : syracuseStep 4356641 = 3267481) B3267481
theorem B2292263 : Blo 1016603 2292263 := bstep (se 1 (by rfl) ⟨1719197, by rfl⟩ : syracuseStep 2292263 = 3438395) B3438395
theorem B1931987 : Blo 1016603 1931987 := bstep (se 1 (by rfl) ⟨1448990, by rfl⟩ : syracuseStep 1931987 = 2897981) B2897981
theorem B1932025 : Blo 1016603 1932025 := bstep (se 2 (by rfl) ⟨724509, by rfl⟩ : syracuseStep 1932025 = 1449019) B1449019
theorem B1145695 : Blo 1016603 1145695 := bstep (se 1 (by rfl) ⟨859271, by rfl⟩ : syracuseStep 1145695 = 1718543) B1718543
theorem B2292587 : Blo 1016603 2292587 := bstep (se 1 (by rfl) ⟨1719440, by rfl⟩ : syracuseStep 2292587 = 3438881) B3438881
theorem B2292641 : Blo 1016603 2292641 := bstep (se 2 (by rfl) ⟨859740, by rfl⟩ : syracuseStep 2292641 = 1719481) B1719481
theorem B2653103 : Blo 1016603 2653103 := bstep (se 1 (by rfl) ⟨1989827, by rfl⟩ : syracuseStep 2653103 = 3979655) B3979655
theorem B4652185 : Blo 1016603 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B6290603 : Blo 1016603 6290603 := bstep (se 1 (by rfl) ⟨4717952, by rfl⟩ : syracuseStep 6290603 = 9435905) B9435905
theorem B1146055 : Blo 1016603 1146055 := bstep (se 1 (by rfl) ⟨859541, by rfl⟩ : syracuseStep 1146055 = 1719083) B1719083
theorem B2292983 : Blo 1016603 2292983 := bstep (se 1 (by rfl) ⟨1719737, by rfl⟩ : syracuseStep 2292983 = 3439475) B3439475
theorem B3440015 : Blo 1016603 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B1932731 : Blo 1016603 1932731 := bstep (se 1 (by rfl) ⟨1449548, by rfl⟩ : syracuseStep 1932731 = 2899097) B2899097
theorem B181140941 : Blo 1016603 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B3866251 : Blo 1016603 3866251 := bstep (se 1 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 3866251 = 5799377) B5799377
theorem B3440339 : Blo 1016603 3440339 := bstep (se 1 (by rfl) ⟨2580254, by rfl⟩ : syracuseStep 3440339 = 5160509) B5160509
theorem B2293577 : Blo 1016603 2293577 := bstep (se 2 (by rfl) ⟨860091, by rfl⟩ : syracuseStep 2293577 = 1720183) B1720183
theorem B1834859 : Blo 1016603 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B1933217 : Blo 1016603 1933217 := bstep (se 2 (by rfl) ⟨724956, by rfl⟩ : syracuseStep 1933217 = 1449913) B1449913
theorem B3866555 : Blo 1016603 3866555 := bstep (se 1 (by rfl) ⟨2899916, by rfl⟩ : syracuseStep 3866555 = 5799833) B5799833
theorem B2293865 : Blo 1016603 2293865 := bstep (se 2 (by rfl) ⟨860199, by rfl⟩ : syracuseStep 2293865 = 1720399) B1720399
theorem B1147099 : Blo 1016603 1147099 := bstep (se 1 (by rfl) ⟨860324, by rfl⟩ : syracuseStep 1147099 = 1720649) B1720649
theorem B3440987 : Blo 1016603 3440987 := bstep (se 1 (by rfl) ⟨2580740, by rfl⟩ : syracuseStep 3440987 = 5161481) B5161481
theorem B52986329 : Blo 1016603 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B1147387 : Blo 1016603 1147387 := bstep (se 1 (by rfl) ⟨860540, by rfl⟩ : syracuseStep 1147387 = 1721081) B1721081
theorem B2294351 : Blo 1016603 2294351 := bstep (se 1 (by rfl) ⟨1720763, by rfl⟩ : syracuseStep 2294351 = 3441527) B3441527
theorem B1933931 : Blo 1016603 1933931 := bstep (se 1 (by rfl) ⟨1450448, by rfl⟩ : syracuseStep 1933931 = 2900897) B2900897
theorem B1147567 : Blo 1016603 1147567 := bstep (se 1 (by rfl) ⟨860675, by rfl⟩ : syracuseStep 1147567 = 1721351) B1721351
theorem B2294495 : Blo 1016603 2294495 := bstep (se 1 (by rfl) ⟨1720871, by rfl⟩ : syracuseStep 2294495 = 3441743) B3441743
theorem B1016623 : Blo 1016603 1016623 := bstep (se 1 (by rfl) ⟨762467, by rfl⟩ : syracuseStep 1016623 = 1524935) B1524935
theorem B1016731 : Blo 1016603 1016731 := bstep (se 1 (by rfl) ⟨762548, by rfl⟩ : syracuseStep 1016731 = 1525097) B1525097
theorem B1016783 : Blo 1016603 1016783 := bstep (se 1 (by rfl) ⟨762587, by rfl⟩ : syracuseStep 1016783 = 1525175) B1525175
theorem B1147855 : Blo 1016603 1147855 := bstep (se 1 (by rfl) ⟨860891, by rfl⟩ : syracuseStep 1147855 = 1721783) B1721783
theorem B2294747 : Blo 1016603 2294747 := bstep (se 1 (by rfl) ⟨1721060, by rfl⟩ : syracuseStep 2294747 = 3442121) B3442121
theorem B1016807 : Blo 1016603 1016807 := bstep (se 1 (by rfl) ⟨762605, by rfl⟩ : syracuseStep 1016807 = 1525211) B1525211
theorem B2294927 : Blo 1016603 2294927 := bstep (se 1 (by rfl) ⟨1721195, by rfl⟩ : syracuseStep 2294927 = 3442391) B3442391
theorem B4129991 : Blo 1016603 4129991 := bstep (se 1 (by rfl) ⟨3097493, by rfl⟩ : syracuseStep 4129991 = 6194987) B6194987
theorem B2295017 : Blo 1016603 2295017 := bstep (se 2 (by rfl) ⟨860631, by rfl⟩ : syracuseStep 2295017 = 1721263) B1721263
theorem B1017119 : Blo 1016603 1017119 := bstep (se 1 (by rfl) ⟨762839, by rfl⟩ : syracuseStep 1017119 = 1525679) B1525679
theorem B2295071 : Blo 1016603 2295071 := bstep (se 1 (by rfl) ⟨1721303, by rfl⟩ : syracuseStep 2295071 = 3442607) B3442607
theorem B3441959 : Blo 1016603 3441959 := bstep (se 1 (by rfl) ⟨2581469, by rfl⟩ : syracuseStep 3441959 = 5162939) B5162939
theorem B1017179 : Blo 1016603 1017179 := bstep (se 1 (by rfl) ⟨762884, by rfl⟩ : syracuseStep 1017179 = 1525769) B1525769
theorem B3868013 : Blo 1016603 3868013 := bstep (se 3 (by rfl) ⟨725252, by rfl⟩ : syracuseStep 3868013 = 1450505) B1450505
theorem B1017199 : Blo 1016603 1017199 := bstep (se 1 (by rfl) ⟨762899, by rfl⟩ : syracuseStep 1017199 = 1525799) B1525799
theorem B3671419 : Blo 1016603 3671419 := bstep (se 1 (by rfl) ⟨2753564, by rfl⟩ : syracuseStep 3671419 = 5507129) B5507129
theorem B11601305 : Blo 1016603 11601305 := bstep (se 2 (by rfl) ⟨4350489, by rfl⟩ : syracuseStep 11601305 = 8700979) B8700979
theorem B1017255 : Blo 1016603 1017255 := bstep (se 1 (by rfl) ⟨762941, by rfl⟩ : syracuseStep 1017255 = 1525883) B1525883
theorem B1017339 : Blo 1016603 1017339 := bstep (se 1 (by rfl) ⟨763004, by rfl⟩ : syracuseStep 1017339 = 1526009) B1526009
theorem B1017407 : Blo 1016603 1017407 := bstep (se 1 (by rfl) ⟨763055, by rfl⟩ : syracuseStep 1017407 = 1526111) B1526111
theorem B1017415 : Blo 1016603 1017415 := bstep (se 1 (by rfl) ⟨763061, by rfl⟩ : syracuseStep 1017415 = 1526123) B1526123
theorem B2066081 : Blo 1016603 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B1017567 : Blo 1016603 1017567 := bstep (se 1 (by rfl) ⟨763175, by rfl⟩ : syracuseStep 1017567 = 1526351) B1526351
theorem B1378015 : Blo 1016603 1378015 := bstep (se 1 (by rfl) ⟨1033511, by rfl⟩ : syracuseStep 1378015 = 2067023) B2067023
theorem B2295593 : Blo 1016603 2295593 := bstep (se 2 (by rfl) ⟨860847, by rfl⟩ : syracuseStep 2295593 = 1721695) B1721695
theorem B1017647 : Blo 1016603 1017647 := bstep (se 1 (by rfl) ⟨763235, by rfl⟩ : syracuseStep 1017647 = 1526471) B1526471
theorem B1935161 : Blo 1016603 1935161 := bstep (se 2 (by rfl) ⟨725685, by rfl⟩ : syracuseStep 1935161 = 1451371) B1451371
theorem B1017755 : Blo 1016603 1017755 := bstep (se 1 (by rfl) ⟨763316, by rfl⟩ : syracuseStep 1017755 = 1526633) B1526633
theorem B1017807 : Blo 1016603 1017807 := bstep (se 1 (by rfl) ⟨763355, by rfl⟩ : syracuseStep 1017807 = 1526711) B1526711
theorem B1017831 : Blo 1016603 1017831 := bstep (se 1 (by rfl) ⟨763373, by rfl⟩ : syracuseStep 1017831 = 1526747) B1526747
theorem B3442823 : Blo 1016603 3442823 := bstep (se 1 (by rfl) ⟨2582117, by rfl⟩ : syracuseStep 3442823 = 5164235) B5164235
theorem B1018143 : Blo 1016603 1018143 := bstep (se 1 (by rfl) ⟨763607, by rfl⟩ : syracuseStep 1018143 = 1527215) B1527215
theorem B1018203 : Blo 1016603 1018203 := bstep (se 1 (by rfl) ⟨763652, by rfl⟩ : syracuseStep 1018203 = 1527305) B1527305
theorem B1018223 : Blo 1016603 1018223 := bstep (se 1 (by rfl) ⟨763667, by rfl⟩ : syracuseStep 1018223 = 1527335) B1527335
theorem B39750041 : Blo 1016603 39750041 := bstep (se 2 (by rfl) ⟨14906265, by rfl⟩ : syracuseStep 39750041 = 29812531) B29812531
theorem B1018279 : Blo 1016603 1018279 := bstep (se 1 (by rfl) ⟨763709, by rfl⟩ : syracuseStep 1018279 = 1527419) B1527419
theorem B5147063 : Blo 1016603 5147063 := bstep (se 1 (by rfl) ⟨3860297, by rfl⟩ : syracuseStep 5147063 = 7720595) B7720595
theorem B7834067 : Blo 1016603 7834067 := bstep (se 1 (by rfl) ⟨5875550, by rfl⟩ : syracuseStep 7834067 = 11751101) B11751101
theorem B7342579 : Blo 1016603 7342579 := bstep (se 1 (by rfl) ⟨5506934, by rfl⟩ : syracuseStep 7342579 = 11013869) B11013869
theorem B1018363 : Blo 1016603 1018363 := bstep (se 1 (by rfl) ⟨763772, by rfl⟩ : syracuseStep 1018363 = 1527545) B1527545
theorem B1018431 : Blo 1016603 1018431 := bstep (se 1 (by rfl) ⟨763823, by rfl⟩ : syracuseStep 1018431 = 1527647) B1527647
theorem B1018439 : Blo 1016603 1018439 := bstep (se 1 (by rfl) ⟨763829, by rfl⟩ : syracuseStep 1018439 = 1527659) B1527659
theorem B1018591 : Blo 1016603 1018591 := bstep (se 1 (by rfl) ⟨763943, by rfl⟩ : syracuseStep 1018591 = 1527887) B1527887
theorem B1018671 : Blo 1016603 1018671 := bstep (se 1 (by rfl) ⟨764003, by rfl⟩ : syracuseStep 1018671 = 1528007) B1528007
theorem B1018779 : Blo 1016603 1018779 := bstep (se 1 (by rfl) ⟨764084, by rfl⟩ : syracuseStep 1018779 = 1528169) B1528169
theorem B1018831 : Blo 1016603 1018831 := bstep (se 1 (by rfl) ⟨764123, by rfl⟩ : syracuseStep 1018831 = 1528247) B1528247
theorem B1018855 : Blo 1016603 1018855 := bstep (se 1 (by rfl) ⟨764141, by rfl⟩ : syracuseStep 1018855 = 1528283) B1528283
theorem B1019167 : Blo 1016603 1019167 := bstep (se 1 (by rfl) ⟨764375, by rfl⟩ : syracuseStep 1019167 = 1528751) B1528751
theorem B1019227 : Blo 1016603 1019227 := bstep (se 1 (by rfl) ⟨764420, by rfl⟩ : syracuseStep 1019227 = 1528841) B1528841
theorem B3444065 : Blo 1016603 3444065 := bstep (se 2 (by rfl) ⟨1291524, by rfl⟩ : syracuseStep 3444065 = 2583049) B2583049
theorem B1019247 : Blo 1016603 1019247 := bstep (se 1 (by rfl) ⟨764435, by rfl⟩ : syracuseStep 1019247 = 1528871) B1528871
theorem B1019303 : Blo 1016603 1019303 := bstep (se 1 (by rfl) ⟨764477, by rfl⟩ : syracuseStep 1019303 = 1528955) B1528955
theorem B3870139 : Blo 1016603 3870139 := bstep (se 1 (by rfl) ⟨2902604, by rfl⟩ : syracuseStep 3870139 = 5805209) B5805209
theorem B1019387 : Blo 1016603 1019387 := bstep (se 1 (by rfl) ⟨764540, by rfl⟩ : syracuseStep 1019387 = 1529081) B1529081
theorem B1019455 : Blo 1016603 1019455 := bstep (se 1 (by rfl) ⟨764591, by rfl⟩ : syracuseStep 1019455 = 1529183) B1529183
theorem B1019463 : Blo 1016603 1019463 := bstep (se 1 (by rfl) ⟨764597, by rfl⟩ : syracuseStep 1019463 = 1529195) B1529195
theorem B1019615 : Blo 1016603 1019615 := bstep (se 1 (by rfl) ⟨764711, by rfl⟩ : syracuseStep 1019615 = 1529423) B1529423
theorem B3870443 : Blo 1016603 3870443 := bstep (se 1 (by rfl) ⟨2902832, by rfl⟩ : syracuseStep 3870443 = 5805665) B5805665
theorem B1019695 : Blo 1016603 1019695 := bstep (se 1 (by rfl) ⟨764771, by rfl⟩ : syracuseStep 1019695 = 1529543) B1529543
theorem B1019803 : Blo 1016603 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B5803933 : Blo 1016603 5803933 := bstep (se 3 (by rfl) ⟨1088237, by rfl⟩ : syracuseStep 5803933 = 2176475) B2176475
theorem B1019855 : Blo 1016603 1019855 := bstep (se 1 (by rfl) ⟨764891, by rfl⟩ : syracuseStep 1019855 = 1529783) B1529783
theorem B1019879 : Blo 1016603 1019879 := bstep (se 1 (by rfl) ⟨764909, by rfl⟩ : syracuseStep 1019879 = 1529819) B1529819
theorem B3870929 : Blo 1016603 3870929 := bstep (se 2 (by rfl) ⟨1451598, by rfl⟩ : syracuseStep 3870929 = 2903197) B2903197
theorem B1020191 : Blo 1016603 1020191 := bstep (se 1 (by rfl) ⟨765143, by rfl⟩ : syracuseStep 1020191 = 1530287) B1530287
theorem B1020251 : Blo 1016603 1020251 := bstep (se 1 (by rfl) ⟨765188, by rfl⟩ : syracuseStep 1020251 = 1530377) B1530377
theorem B1020271 : Blo 1016603 1020271 := bstep (se 1 (by rfl) ⟨765203, by rfl⟩ : syracuseStep 1020271 = 1530407) B1530407
theorem B1020327 : Blo 1016603 1020327 := bstep (se 1 (by rfl) ⟨765245, by rfl⟩ : syracuseStep 1020327 = 1530491) B1530491
theorem B1020411 : Blo 1016603 1020411 := bstep (se 1 (by rfl) ⟨765308, by rfl⟩ : syracuseStep 1020411 = 1530617) B1530617
theorem B1020479 : Blo 1016603 1020479 := bstep (se 1 (by rfl) ⟨765359, by rfl⟩ : syracuseStep 1020479 = 1530719) B1530719
theorem B5509703 : Blo 1016603 5509703 := bstep (se 1 (by rfl) ⟨4132277, by rfl⟩ : syracuseStep 5509703 = 8264555) B8264555
theorem B1020487 : Blo 1016603 1020487 := bstep (se 1 (by rfl) ⟨765365, by rfl⟩ : syracuseStep 1020487 = 1530731) B1530731
theorem B5149331 : Blo 1016603 5149331 := bstep (se 1 (by rfl) ⟨3861998, by rfl⟩ : syracuseStep 5149331 = 7723997) B7723997
theorem B3871385 : Blo 1016603 3871385 := bstep (se 2 (by rfl) ⟨1451769, by rfl⟩ : syracuseStep 3871385 = 2903539) B2903539
theorem B3871415 : Blo 1016603 3871415 := bstep (se 1 (by rfl) ⟨2903561, by rfl⟩ : syracuseStep 3871415 = 5807123) B5807123
theorem B8262479 : Blo 1016603 8262479 := bstep (se 1 (by rfl) ⟨6196859, by rfl⟩ : syracuseStep 8262479 = 12393719) B12393719
theorem B5150141 : Blo 1016603 5150141 := bstep (se 3 (by rfl) ⟨965651, by rfl⟩ : syracuseStep 5150141 = 1931303) B1931303
theorem B2201183 : Blo 1016603 2201183 := bstep (se 1 (by rfl) ⟨1650887, by rfl⟩ : syracuseStep 2201183 = 3301775) B3301775
theorem B17373527 : Blo 1016603 17373527 := bstep (se 1 (by rfl) ⟨13030145, by rfl⟩ : syracuseStep 17373527 = 26060291) B26060291
theorem B3873359 : Blo 1016603 3873359 := bstep (se 1 (by rfl) ⟨2905019, by rfl⟩ : syracuseStep 3873359 = 5810039) B5810039
theorem B3873527 : Blo 1016603 3873527 := bstep (se 1 (by rfl) ⟨2905145, by rfl⟩ : syracuseStep 3873527 = 5810291) B5810291
theorem B9804563 : Blo 1016603 9804563 := bstep (se 1 (by rfl) ⟨7353422, by rfl⟩ : syracuseStep 9804563 = 14706845) B14706845
theorem B1449247 : Blo 1016603 1449247 := bstep (se 1 (by rfl) ⟨1086935, by rfl⟩ : syracuseStep 1449247 = 2173871) B2173871
theorem B5512819 : Blo 1016603 5512819 := bstep (se 1 (by rfl) ⟨4134614, by rfl⟩ : syracuseStep 5512819 = 8269229) B8269229
theorem B4136609 : Blo 1016603 4136609 := bstep (se 2 (by rfl) ⟨1551228, by rfl⟩ : syracuseStep 4136609 = 3102457) B3102457
theorem B7446275 : Blo 1016603 7446275 := bstep (se 1 (by rfl) ⟨5584706, by rfl⟩ : syracuseStep 7446275 = 11169413) B11169413
theorem B8265881 : Blo 1016603 8265881 := bstep (se 2 (by rfl) ⟨3099705, by rfl⟩ : syracuseStep 8265881 = 6199411) B6199411
theorem B6955703 : Blo 1016603 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B1287515 : Blo 1016603 1287515 := bstep (se 1 (by rfl) ⟨965636, by rfl⟩ : syracuseStep 1287515 = 1931273) B1931273
theorem B6202913 : Blo 1016603 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B2172511 : Blo 1016603 2172511 := bstep (se 1 (by rfl) ⟨1629383, by rfl⟩ : syracuseStep 2172511 = 3258767) B3258767
theorem B1287991 : Blo 1016603 1287991 := bstep (se 1 (by rfl) ⟨965993, by rfl⟩ : syracuseStep 1287991 = 1931987) B1931987
theorem B14690285 : Blo 1016603 14690285 := bstep (se 3 (by rfl) ⟨2754428, by rfl⟩ : syracuseStep 14690285 = 5508857) B5508857
theorem B5155001 : Blo 1016603 5155001 := bstep (se 2 (by rfl) ⟨1933125, by rfl⟩ : syracuseStep 5155001 = 3866251) B3866251
theorem B4892957 : Blo 1016603 4892957 := bstep (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) B1834859
theorem B1288487 : Blo 1016603 1288487 := bstep (se 1 (by rfl) ⟨966365, by rfl⟩ : syracuseStep 1288487 = 1932731) B1932731
theorem B120760627 : Blo 1016603 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B1255771 : Blo 1016603 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B18590057 : Blo 1016603 18590057 := bstep (se 2 (by rfl) ⟨6971271, by rfl⟩ : syracuseStep 18590057 = 13942543) B13942543
theorem B1288811 : Blo 1016603 1288811 := bstep (se 1 (by rfl) ⟨966608, by rfl⟩ : syracuseStep 1288811 = 1933217) B1933217
theorem B5515951 : Blo 1016603 5515951 := bstep (se 1 (by rfl) ⟨4136963, by rfl⟩ : syracuseStep 5515951 = 8273927) B8273927
theorem B1551071 : Blo 1016603 1551071 := bstep (se 1 (by rfl) ⟨1163303, by rfl⟩ : syracuseStep 1551071 = 2326607) B2326607
theorem B1289191 : Blo 1016603 1289191 := bstep (se 1 (by rfl) ⟨966893, by rfl⟩ : syracuseStep 1289191 = 1933787) B1933787
theorem B11611511 : Blo 1016603 11611511 := bstep (se 1 (by rfl) ⟨8708633, by rfl⟩ : syracuseStep 11611511 = 17417267) B17417267
theorem B1715593 : Blo 1016603 1715593 := bstep (se 2 (by rfl) ⟨643347, by rfl⟩ : syracuseStep 1715593 = 1286695) B1286695
theorem B14691901 : Blo 1016603 14691901 := bstep (se 3 (by rfl) ⟨2754731, by rfl⟩ : syracuseStep 14691901 = 5509463) B5509463
theorem B1716025 : Blo 1016603 1716025 := bstep (se 2 (by rfl) ⟨643509, by rfl⟩ : syracuseStep 1716025 = 1287019) B1287019
theorem B5156783 : Blo 1016603 5156783 := bstep (se 1 (by rfl) ⟨3867587, by rfl⟩ : syracuseStep 5156783 = 7735175) B7735175
theorem B1716329 : Blo 1016603 1716329 := bstep (se 2 (by rfl) ⟨643623, by rfl⟩ : syracuseStep 1716329 = 1287247) B1287247
theorem B13054445 : Blo 1016603 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B15708653 : Blo 1016603 15708653 := bstep (se 3 (by rfl) ⟨2945372, by rfl⟩ : syracuseStep 15708653 = 5890745) B5890745
theorem B8696605 : Blo 1016603 8696605 := bstep (se 3 (by rfl) ⟨1630613, by rfl⟩ : syracuseStep 8696605 = 3261227) B3261227
theorem B29340791 : Blo 1016603 29340791 := bstep (se 1 (by rfl) ⟨22005593, by rfl⟩ : syracuseStep 29340791 = 44011187) B44011187
theorem B14693633 : Blo 1016603 14693633 := bstep (se 2 (by rfl) ⟨5510112, by rfl⟩ : syracuseStep 14693633 = 11020225) B11020225
theorem B15709463 : Blo 1016603 15709463 := bstep (se 1 (by rfl) ⟨11782097, by rfl⟩ : syracuseStep 15709463 = 23564195) B23564195
theorem B8271143 : Blo 1016603 8271143 := bstep (se 1 (by rfl) ⟨6203357, by rfl⟩ : syracuseStep 8271143 = 12406715) B12406715
theorem B1717753 : Blo 1016603 1717753 := bstep (se 2 (by rfl) ⟨644157, by rfl⟩ : syracuseStep 1717753 = 1288315) B1288315
theorem B1718023 : Blo 1016603 1718023 := bstep (se 1 (by rfl) ⟨1288517, by rfl⟩ : syracuseStep 1718023 = 2577035) B2577035
theorem B1718057 : Blo 1016603 1718057 := bstep (se 2 (by rfl) ⟨644271, by rfl⟩ : syracuseStep 1718057 = 1288543) B1288543
theorem B17611057 : Blo 1016603 17611057 := bstep (se 2 (by rfl) ⟨6604146, by rfl⟩ : syracuseStep 17611057 = 13208293) B13208293
theorem B1718779 : Blo 1016603 1718779 := bstep (se 1 (by rfl) ⟨1289084, by rfl⟩ : syracuseStep 1718779 = 2578169) B2578169
theorem B6961859 : Blo 1016603 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B5159699 : Blo 1016603 5159699 := bstep (se 1 (by rfl) ⟨3869774, by rfl⟩ : syracuseStep 5159699 = 7739549) B7739549
theorem B7355291 : Blo 1016603 7355291 := bstep (se 1 (by rfl) ⟨5516468, by rfl⟩ : syracuseStep 7355291 = 11032937) B11032937
theorem B1719211 : Blo 1016603 1719211 := bstep (se 1 (by rfl) ⟨1289408, by rfl⟩ : syracuseStep 1719211 = 2578817) B2578817
theorem B2898983 : Blo 1016603 2898983 := bstep (se 1 (by rfl) ⟨2174237, by rfl⟩ : syracuseStep 2898983 = 4348475) B4348475
theorem B1719515 : Blo 1016603 1719515 := bstep (se 1 (by rfl) ⟨1289636, by rfl⟩ : syracuseStep 1719515 = 2579273) B2579273
theorem B1719751 : Blo 1016603 1719751 := bstep (se 1 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 1719751 = 2579627) B2579627
theorem B2899415 : Blo 1016603 2899415 := bstep (se 1 (by rfl) ⟨2174561, by rfl⟩ : syracuseStep 2899415 = 4349123) B4349123
theorem B13942331 : Blo 1016603 13942331 := bstep (se 1 (by rfl) ⟨10456748, by rfl⟩ : syracuseStep 13942331 = 20913497) B20913497
theorem B5160833 : Blo 1016603 5160833 := bstep (se 2 (by rfl) ⟨1935312, by rfl⟩ : syracuseStep 5160833 = 3870625) B3870625
theorem B1720271 : Blo 1016603 1720271 := bstep (se 1 (by rfl) ⟨1290203, by rfl⟩ : syracuseStep 1720271 = 2580407) B2580407
theorem B22069259 : Blo 1016603 22069259 := bstep (se 1 (by rfl) ⟨16551944, by rfl⟩ : syracuseStep 22069259 = 33103889) B33103889
theorem B1720939 : Blo 1016603 1720939 := bstep (se 1 (by rfl) ⟨1290704, by rfl⟩ : syracuseStep 1720939 = 2581409) B2581409
theorem B2179705 : Blo 1016603 2179705 := bstep (se 2 (by rfl) ⟨817389, by rfl⟩ : syracuseStep 2179705 = 1634779) B1634779
theorem B7848593 : Blo 1016603 7848593 := bstep (se 2 (by rfl) ⟨2943222, by rfl⟩ : syracuseStep 7848593 = 5886445) B5886445
theorem B5161643 : Blo 1016603 5161643 := bstep (se 1 (by rfl) ⟨3871232, by rfl⟩ : syracuseStep 5161643 = 7742465) B7742465
theorem B7455415 : Blo 1016603 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B3261151 : Blo 1016603 3261151 := bstep (se 1 (by rfl) ⟨2445863, by rfl⟩ : syracuseStep 3261151 = 4891727) B4891727
theorem B5653327 : Blo 1016603 5653327 := bstep (se 1 (by rfl) ⟨4239995, by rfl⟩ : syracuseStep 5653327 = 8479991) B8479991
theorem B1721243 : Blo 1016603 1721243 := bstep (se 1 (by rfl) ⟨1290932, by rfl⟩ : syracuseStep 1721243 = 2581865) B2581865
theorem B5162129 : Blo 1016603 5162129 := bstep (se 2 (by rfl) ⟨1935798, by rfl⟩ : syracuseStep 5162129 = 3871597) B3871597
theorem B1525031 : Blo 1016603 1525031 := bstep (se 1 (by rfl) ⟨1143773, by rfl⟩ : syracuseStep 1525031 = 2287547) B2287547
theorem B1525115 : Blo 1016603 1525115 := bstep (se 1 (by rfl) ⟨1143836, by rfl⟩ : syracuseStep 1525115 = 2287673) B2287673
theorem B1983881 : Blo 1016603 1983881 := bstep (se 2 (by rfl) ⟨743955, by rfl⟩ : syracuseStep 1983881 = 1487911) B1487911
theorem B1525241 : Blo 1016603 1525241 := bstep (se 2 (by rfl) ⟨571965, by rfl⟩ : syracuseStep 1525241 = 1143931) B1143931
theorem B2901511 : Blo 1016603 2901511 := bstep (se 1 (by rfl) ⟨2176133, by rfl⟩ : syracuseStep 2901511 = 4352267) B4352267
theorem B1525343 : Blo 1016603 1525343 := bstep (se 1 (by rfl) ⟨1144007, by rfl⟩ : syracuseStep 1525343 = 2288015) B2288015
theorem B3262139 : Blo 1016603 3262139 := bstep (se 1 (by rfl) ⟨2446604, by rfl⟩ : syracuseStep 3262139 = 4893209) B4893209
theorem B1525559 : Blo 1016603 1525559 := bstep (se 1 (by rfl) ⟨1144169, by rfl⟩ : syracuseStep 1525559 = 2288339) B2288339
theorem B6604649 : Blo 1016603 6604649 := bstep (se 2 (by rfl) ⟨2476743, by rfl⟩ : syracuseStep 6604649 = 4953487) B4953487
theorem B2901865 : Blo 1016603 2901865 := bstep (se 2 (by rfl) ⟨1088199, by rfl⟩ : syracuseStep 2901865 = 2176399) B2176399
theorem B1525865 : Blo 1016603 1525865 := bstep (se 2 (by rfl) ⟨572199, by rfl⟩ : syracuseStep 1525865 = 1144399) B1144399
theorem B21743873 : Blo 1016603 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B2443529 : Blo 1016603 2443529 := bstep (se 2 (by rfl) ⟨916323, by rfl⟩ : syracuseStep 2443529 = 1832647) B1832647
theorem B1526183 : Blo 1016603 1526183 := bstep (se 1 (by rfl) ⟨1144637, by rfl⟩ : syracuseStep 1526183 = 2289275) B2289275
theorem B2574767 : Blo 1016603 2574767 := bstep (se 1 (by rfl) ⟨1931075, by rfl⟩ : syracuseStep 2574767 = 3862151) B3862151
theorem B1526267 : Blo 1016603 1526267 := bstep (se 1 (by rfl) ⟨1144700, by rfl⟩ : syracuseStep 1526267 = 2289401) B2289401
theorem B1526393 : Blo 1016603 1526393 := bstep (se 2 (by rfl) ⟨572397, by rfl⟩ : syracuseStep 1526393 = 1144795) B1144795
theorem B1526447 : Blo 1016603 1526447 := bstep (se 1 (by rfl) ⟨1144835, by rfl⟩ : syracuseStep 1526447 = 2289671) B2289671
theorem B1526495 : Blo 1016603 1526495 := bstep (se 1 (by rfl) ⟨1144871, by rfl⟩ : syracuseStep 1526495 = 2289743) B2289743
theorem B1526759 : Blo 1016603 1526759 := bstep (se 1 (by rfl) ⟨1145069, by rfl⟩ : syracuseStep 1526759 = 2290139) B2290139
theorem B2444327 : Blo 1016603 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B10996955 : Blo 1016603 10996955 := bstep (se 1 (by rfl) ⟨8247716, by rfl⟩ : syracuseStep 10996955 = 16495433) B16495433
theorem B1527017 : Blo 1016603 1527017 := bstep (se 2 (by rfl) ⟨572631, by rfl⟩ : syracuseStep 1527017 = 1145263) B1145263
theorem B1527071 : Blo 1016603 1527071 := bstep (se 1 (by rfl) ⟨1145303, by rfl⟩ : syracuseStep 1527071 = 2290607) B2290607
theorem B2575739 : Blo 1016603 2575739 := bstep (se 1 (by rfl) ⟨1931804, by rfl⟩ : syracuseStep 2575739 = 3863609) B3863609
theorem B11161019 : Blo 1016603 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B2608583 : Blo 1016603 2608583 := bstep (se 1 (by rfl) ⟨1956437, by rfl⟩ : syracuseStep 2608583 = 3912875) B3912875
theorem B1527239 : Blo 1016603 1527239 := bstep (se 1 (by rfl) ⟨1145429, by rfl⟩ : syracuseStep 1527239 = 2290859) B2290859
theorem B2444759 : Blo 1016603 2444759 := bstep (se 1 (by rfl) ⟨1833569, by rfl⟩ : syracuseStep 2444759 = 3667139) B3667139
theorem B5164559 : Blo 1016603 5164559 := bstep (se 1 (by rfl) ⟨3873419, by rfl⟩ : syracuseStep 5164559 = 7746839) B7746839
theorem B19549835 : Blo 1016603 19549835 := bstep (se 1 (by rfl) ⟨14662376, by rfl⟩ : syracuseStep 19549835 = 29324753) B29324753
theorem B2576033 : Blo 1016603 2576033 := bstep (se 2 (by rfl) ⟨966012, by rfl⟩ : syracuseStep 2576033 = 1932025) B1932025
theorem B8933075 : Blo 1016603 8933075 := bstep (se 1 (by rfl) ⟨6699806, by rfl⟩ : syracuseStep 8933075 = 13399613) B13399613
theorem B1527593 : Blo 1016603 1527593 := bstep (se 2 (by rfl) ⟨572847, by rfl⟩ : syracuseStep 1527593 = 1145695) B1145695
theorem B16535339 : Blo 1016603 16535339 := bstep (se 1 (by rfl) ⟨12401504, by rfl⟩ : syracuseStep 16535339 = 24803009) B24803009
theorem B1527599 : Blo 1016603 1527599 := bstep (se 1 (by rfl) ⟨1145699, by rfl⟩ : syracuseStep 1527599 = 2291399) B2291399
theorem B4345775 : Blo 1016603 4345775 := bstep (se 1 (by rfl) ⟨3259331, by rfl⟩ : syracuseStep 4345775 = 6518663) B6518663
theorem B1528073 : Blo 1016603 1528073 := bstep (se 2 (by rfl) ⟨573027, by rfl⟩ : syracuseStep 1528073 = 1146055) B1146055
theorem B2576731 : Blo 1016603 2576731 := bstep (se 1 (by rfl) ⟨1932548, by rfl⟩ : syracuseStep 2576731 = 3865097) B3865097
theorem B2904427 : Blo 1016603 2904427 := bstep (se 1 (by rfl) ⟨2178320, by rfl⟩ : syracuseStep 2904427 = 4356641) B4356641
theorem B1528175 : Blo 1016603 1528175 := bstep (se 1 (by rfl) ⟨1146131, by rfl⟩ : syracuseStep 1528175 = 2292263) B2292263
theorem B5165531 : Blo 1016603 5165531 := bstep (se 1 (by rfl) ⟨3874148, by rfl⟩ : syracuseStep 5165531 = 7748297) B7748297
theorem B1528391 : Blo 1016603 1528391 := bstep (se 1 (by rfl) ⟨1146293, by rfl⟩ : syracuseStep 1528391 = 2292587) B2292587
theorem B2478671 : Blo 1016603 2478671 := bstep (se 1 (by rfl) ⟨1859003, by rfl⟩ : syracuseStep 2478671 = 3718007) B3718007
theorem B1528427 : Blo 1016603 1528427 := bstep (se 1 (by rfl) ⟨1146320, by rfl⟩ : syracuseStep 1528427 = 2292641) B2292641
theorem B1528655 : Blo 1016603 1528655 := bstep (se 1 (by rfl) ⟨1146491, by rfl⟩ : syracuseStep 1528655 = 2292983) B2292983
theorem B5166017 : Blo 1016603 5166017 := bstep (se 2 (by rfl) ⟨1937256, by rfl⟩ : syracuseStep 5166017 = 3874513) B3874513
theorem B16962509 : Blo 1016603 16962509 := bstep (se 3 (by rfl) ⟨3180470, by rfl⟩ : syracuseStep 16962509 = 6360941) B6360941
theorem B3921095 : Blo 1016603 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B1529051 : Blo 1016603 1529051 := bstep (se 1 (by rfl) ⟨1146788, by rfl⟩ : syracuseStep 1529051 = 2293577) B2293577
theorem B2577703 : Blo 1016603 2577703 := bstep (se 1 (by rfl) ⟨1933277, by rfl⟩ : syracuseStep 2577703 = 3866555) B3866555
theorem B4904297 : Blo 1016603 4904297 := bstep (se 2 (by rfl) ⟨1839111, by rfl⟩ : syracuseStep 4904297 = 3678223) B3678223
theorem B9786757 : Blo 1016603 9786757 := bstep (se 4 (by rfl) ⟨917508, by rfl⟩ : syracuseStep 9786757 = 1835017) B1835017
theorem B1529225 : Blo 1016603 1529225 := bstep (se 2 (by rfl) ⟨573459, by rfl⟩ : syracuseStep 1529225 = 1146919) B1146919
theorem B22304165 : Blo 1016603 22304165 := bstep (se 4 (by rfl) ⟨2091015, by rfl⟩ : syracuseStep 22304165 = 4182031) B4182031
theorem B2577977 : Blo 1016603 2577977 := bstep (se 2 (by rfl) ⟨966741, by rfl⟩ : syracuseStep 2577977 = 1933483) B1933483
theorem B9787067 : Blo 1016603 9787067 := bstep (se 1 (by rfl) ⟨7340300, by rfl⟩ : syracuseStep 9787067 = 14680601) B14680601
theorem B1529579 : Blo 1016603 1529579 := bstep (se 1 (by rfl) ⟨1147184, by rfl⟩ : syracuseStep 1529579 = 2294369) B2294369
theorem B1529807 : Blo 1016603 1529807 := bstep (se 1 (by rfl) ⟨1147355, by rfl⟩ : syracuseStep 1529807 = 2294711) B2294711
theorem B4348151 : Blo 1016603 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B1628507 : Blo 1016603 1628507 := bstep (se 1 (by rfl) ⟨1221380, by rfl⟩ : syracuseStep 1628507 = 2442761) B2442761
theorem B1530203 : Blo 1016603 1530203 := bstep (se 1 (by rfl) ⟨1147652, by rfl⟩ : syracuseStep 1530203 = 2295305) B2295305
theorem B11754047 : Blo 1016603 11754047 := bstep (se 1 (by rfl) ⟨8815535, by rfl⟩ : syracuseStep 11754047 = 17631071) B17631071
theorem B1530431 : Blo 1016603 1530431 := bstep (se 1 (by rfl) ⟨1147823, by rfl⟩ : syracuseStep 1530431 = 2295647) B2295647
theorem B1628743 : Blo 1016603 1628743 := bstep (se 1 (by rfl) ⟨1221557, by rfl⟩ : syracuseStep 1628743 = 2443115) B2443115
theorem B3922607 : Blo 1016603 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B1530551 : Blo 1016603 1530551 := bstep (se 1 (by rfl) ⟨1147913, by rfl⟩ : syracuseStep 1530551 = 2295827) B2295827
theorem B3431159 : Blo 1016603 3431159 := bstep (se 1 (by rfl) ⟨2573369, by rfl⟩ : syracuseStep 3431159 = 5146739) B5146739
theorem B1530779 : Blo 1016603 1530779 := bstep (se 1 (by rfl) ⟨1148084, by rfl⟩ : syracuseStep 1530779 = 2296169) B2296169
theorem B2612443 : Blo 1016603 2612443 := bstep (se 1 (by rfl) ⟨1959332, by rfl⟩ : syracuseStep 2612443 = 3918665) B3918665
theorem B2579809 : Blo 1016603 2579809 := bstep (se 2 (by rfl) ⟨967428, by rfl⟩ : syracuseStep 2579809 = 1934857) B1934857
theorem B1629563 : Blo 1016603 1629563 := bstep (se 1 (by rfl) ⟨1222172, by rfl⟩ : syracuseStep 1629563 = 2444345) B2444345
theorem B3432239 : Blo 1016603 3432239 := bstep (se 1 (by rfl) ⟨2574179, by rfl⟩ : syracuseStep 3432239 = 5148359) B5148359
theorem B2580761 : Blo 1016603 2580761 := bstep (se 2 (by rfl) ⟨967785, by rfl⟩ : syracuseStep 2580761 = 1935571) B1935571
theorem B2384219 : Blo 1016603 2384219 := bstep (se 1 (by rfl) ⟨1788164, by rfl⟩ : syracuseStep 2384219 = 3576329) B3576329
theorem B2581055 : Blo 1016603 2581055 := bstep (se 1 (by rfl) ⟨1935791, by rfl⟩ : syracuseStep 2581055 = 3871583) B3871583
theorem B17621651 : Blo 1016603 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B4350611 : Blo 1016603 4350611 := bstep (se 1 (by rfl) ⟨3262958, by rfl⟩ : syracuseStep 4350611 = 6525917) B6525917
theorem B2581267 : Blo 1016603 2581267 := bstep (se 1 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 2581267 = 3871901) B3871901
theorem B4350763 : Blo 1016603 4350763 := bstep (se 1 (by rfl) ⟨3263072, by rfl⟩ : syracuseStep 4350763 = 6526145) B6526145
theorem B2581703 : Blo 1016603 2581703 := bstep (se 1 (by rfl) ⟨1936277, by rfl⟩ : syracuseStep 2581703 = 3872555) B3872555
theorem B2581753 : Blo 1016603 2581753 := bstep (se 2 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 2581753 = 1936315) B1936315
theorem B9791063 : Blo 1016603 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B2287367 : Blo 1016603 2287367 := bstep (se 1 (by rfl) ⟨1715525, by rfl⟩ : syracuseStep 2287367 = 3431051) B3431051
theorem B3434345 : Blo 1016603 3434345 := bstep (se 2 (by rfl) ⟨1287879, by rfl⟩ : syracuseStep 3434345 = 2575759) B2575759
theorem B2582401 : Blo 1016603 2582401 := bstep (se 2 (by rfl) ⟨968400, by rfl⟩ : syracuseStep 2582401 = 1936801) B1936801
theorem B18605971 : Blo 1016603 18605971 := bstep (se 1 (by rfl) ⟨13954478, by rfl⟩ : syracuseStep 18605971 = 27908957) B27908957
theorem B3434777 : Blo 1016603 3434777 := bstep (se 2 (by rfl) ⟨1288041, by rfl⟩ : syracuseStep 3434777 = 2576083) B2576083
theorem B2287979 : Blo 1016603 2287979 := bstep (se 1 (by rfl) ⟨1715984, by rfl⟩ : syracuseStep 2287979 = 3431969) B3431969
theorem B13035887 : Blo 1016603 13035887 := bstep (se 1 (by rfl) ⟨9776915, by rfl⟩ : syracuseStep 13035887 = 19553831) B19553831
theorem B2288123 : Blo 1016603 2288123 := bstep (se 1 (by rfl) ⟨1716092, by rfl⟩ : syracuseStep 2288123 = 3432185) B3432185
theorem B1567295 : Blo 1016603 1567295 := bstep (se 1 (by rfl) ⟨1175471, by rfl⟩ : syracuseStep 1567295 = 2350943) B2350943
theorem B4352575 : Blo 1016603 4352575 := bstep (se 1 (by rfl) ⟨3264431, by rfl⟩ : syracuseStep 4352575 = 6528863) B6528863
theorem B6515279 : Blo 1016603 6515279 := bstep (se 1 (by rfl) ⟨4886459, by rfl⟩ : syracuseStep 6515279 = 9772919) B9772919
theorem B2288249 : Blo 1016603 2288249 := bstep (se 2 (by rfl) ⟨858093, by rfl⟩ : syracuseStep 2288249 = 1716187) B1716187
theorem B2583161 : Blo 1016603 2583161 := bstep (se 2 (by rfl) ⟨968685, by rfl⟩ : syracuseStep 2583161 = 1937371) B1937371
theorem B2583211 : Blo 1016603 2583211 := bstep (se 1 (by rfl) ⟨1937408, by rfl⟩ : syracuseStep 2583211 = 3874817) B3874817
theorem B2288303 : Blo 1016603 2288303 := bstep (se 1 (by rfl) ⟨1716227, by rfl⟩ : syracuseStep 2288303 = 3432455) B3432455
theorem B2288375 : Blo 1016603 2288375 := bstep (se 1 (by rfl) ⟨1716281, by rfl⟩ : syracuseStep 2288375 = 3432563) B3432563
theorem B5794685 : Blo 1016603 5794685 := bstep (se 3 (by rfl) ⟨1086503, by rfl⟩ : syracuseStep 5794685 = 2173007) B2173007
theorem B3861391 : Blo 1016603 3861391 := bstep (se 1 (by rfl) ⟨2896043, by rfl⟩ : syracuseStep 3861391 = 5792087) B5792087
theorem B2288555 : Blo 1016603 2288555 := bstep (se 1 (by rfl) ⟨1716416, by rfl⟩ : syracuseStep 2288555 = 3432833) B3432833
theorem B5434285 : Blo 1016603 5434285 := bstep (se 3 (by rfl) ⟨1018928, by rfl⟩ : syracuseStep 5434285 = 2037857) B2037857
theorem B7334993 : Blo 1016603 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B2289095 : Blo 1016603 2289095 := bstep (se 1 (by rfl) ⟨1716821, by rfl⟩ : syracuseStep 2289095 = 3433643) B3433643
theorem B19819997 : Blo 1016603 19819997 := bstep (se 3 (by rfl) ⟨3716249, by rfl⟩ : syracuseStep 19819997 = 7432499) B7432499
theorem B3436127 : Blo 1016603 3436127 := bstep (se 1 (by rfl) ⟨2577095, by rfl⟩ : syracuseStep 3436127 = 5154191) B5154191
theorem B2289455 : Blo 1016603 2289455 := bstep (se 1 (by rfl) ⟨1717091, by rfl⟩ : syracuseStep 2289455 = 3434183) B3434183
theorem B11759417 : Blo 1016603 11759417 := bstep (se 2 (by rfl) ⟨4409781, by rfl⟩ : syracuseStep 11759417 = 8819563) B8819563
theorem B2748289 : Blo 1016603 2748289 := bstep (se 2 (by rfl) ⟨1030608, by rfl⟩ : syracuseStep 2748289 = 2061217) B2061217
theorem B2290031 : Blo 1016603 2290031 := bstep (se 1 (by rfl) ⟨1717523, by rfl⟩ : syracuseStep 2290031 = 3435047) B3435047
theorem B2290103 : Blo 1016603 2290103 := bstep (se 1 (by rfl) ⟨1717577, by rfl⟩ : syracuseStep 2290103 = 3435155) B3435155
theorem B1864147 : Blo 1016603 1864147 := bstep (se 1 (by rfl) ⟨1398110, by rfl⟩ : syracuseStep 1864147 = 2796221) B2796221
theorem B4354523 : Blo 1016603 4354523 := bstep (se 1 (by rfl) ⟨3265892, by rfl⟩ : syracuseStep 4354523 = 6531785) B6531785
theorem B2290247 : Blo 1016603 2290247 := bstep (se 1 (by rfl) ⟨1717685, by rfl⟩ : syracuseStep 2290247 = 3435371) B3435371
theorem B2290283 : Blo 1016603 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B3437531 : Blo 1016603 3437531 := bstep (se 1 (by rfl) ⟨2578148, by rfl⟩ : syracuseStep 3437531 = 5156297) B5156297
theorem B2290679 : Blo 1016603 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B3437693 : Blo 1016603 3437693 := bstep (se 3 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 3437693 = 1289135) B1289135
theorem B14677139 : Blo 1016603 14677139 := bstep (se 1 (by rfl) ⟨11007854, by rfl⟩ : syracuseStep 14677139 = 22015709) B22015709
theorem B3437801 : Blo 1016603 3437801 := bstep (se 2 (by rfl) ⟨1289175, by rfl⟩ : syracuseStep 3437801 = 2578351) B2578351
theorem B1307935 : Blo 1016603 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B2291039 : Blo 1016603 2291039 := bstep (se 1 (by rfl) ⟨1718279, by rfl⟩ : syracuseStep 2291039 = 3436559) B3436559
theorem B3437963 : Blo 1016603 3437963 := bstep (se 1 (by rfl) ⟨2578472, by rfl⟩ : syracuseStep 3437963 = 5156945) B5156945
theorem B4781501 : Blo 1016603 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B1144543 : Blo 1016603 1144543 := bstep (se 1 (by rfl) ⟨858407, by rfl⟩ : syracuseStep 1144543 = 1716815) B1716815
theorem B2291435 : Blo 1016603 2291435 := bstep (se 1 (by rfl) ⟨1718576, by rfl⟩ : syracuseStep 2291435 = 3437153) B3437153
theorem B1931015 : Blo 1016603 1931015 := bstep (se 1 (by rfl) ⟨1448261, by rfl⟩ : syracuseStep 1931015 = 2896523) B2896523
theorem B2291561 : Blo 1016603 2291561 := bstep (se 2 (by rfl) ⟨859335, by rfl⟩ : syracuseStep 2291561 = 1718671) B1718671
theorem B8714375 : Blo 1016603 8714375 := bstep (se 1 (by rfl) ⟨6535781, by rfl⟩ : syracuseStep 8714375 = 13071563) B13071563
theorem B1145119 : Blo 1016603 1145119 := bstep (se 1 (by rfl) ⟨858839, by rfl⟩ : syracuseStep 1145119 = 1717679) B1717679
theorem B13236605 : Blo 1016603 13236605 := bstep (se 3 (by rfl) ⟨2481863, by rfl⟩ : syracuseStep 13236605 = 4963727) B4963727
theorem B1145407 : Blo 1016603 1145407 := bstep (se 1 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 1145407 = 1718111) B1718111
theorem B8059499 : Blo 1016603 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B7436939 : Blo 1016603 7436939 := bstep (se 1 (by rfl) ⟨5577704, by rfl⟩ : syracuseStep 7436939 = 11155409) B11155409
theorem B2292407 : Blo 1016603 2292407 := bstep (se 1 (by rfl) ⟨1719305, by rfl⟩ : syracuseStep 2292407 = 3438611) B3438611
theorem B4356983 : Blo 1016603 4356983 := bstep (se 1 (by rfl) ⟨3267737, by rfl⟩ : syracuseStep 4356983 = 6535475) B6535475
theorem B2292623 : Blo 1016603 2292623 := bstep (se 1 (by rfl) ⟨1719467, by rfl⟩ : syracuseStep 2292623 = 3438935) B3438935
theorem B6617999 : Blo 1016603 6617999 := bstep (se 1 (by rfl) ⟨4963499, by rfl⟩ : syracuseStep 6617999 = 9926999) B9926999
theorem B1768735 : Blo 1016603 1768735 := bstep (se 1 (by rfl) ⟨1326551, by rfl⟩ : syracuseStep 1768735 = 2653103) B2653103
theorem B1146235 : Blo 1016603 1146235 := bstep (se 1 (by rfl) ⟨859676, by rfl⟩ : syracuseStep 1146235 = 1719353) B1719353
theorem B4193735 : Blo 1016603 4193735 := bstep (se 1 (by rfl) ⟨3145301, by rfl⟩ : syracuseStep 4193735 = 6290603) B6290603
theorem B2293343 : Blo 1016603 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B2293559 : Blo 1016603 2293559 := bstep (se 1 (by rfl) ⟨1720169, by rfl⟩ : syracuseStep 2293559 = 3440339) B3440339
theorem B1146703 : Blo 1016603 1146703 := bstep (se 1 (by rfl) ⟨860027, by rfl⟩ : syracuseStep 1146703 = 1720055) B1720055
theorem B3866525 : Blo 1016603 3866525 := bstep (se 3 (by rfl) ⟨724973, by rfl⟩ : syracuseStep 3866525 = 1449947) B1449947
theorem B14712839 : Blo 1016603 14712839 := bstep (se 1 (by rfl) ⟨11034629, by rfl⟩ : syracuseStep 14712839 = 22069259) B22069259
theorem B2293991 : Blo 1016603 2293991 := bstep (se 1 (by rfl) ⟨1720493, by rfl⟩ : syracuseStep 2293991 = 3440987) B3440987
theorem B35324219 : Blo 1016603 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B3441095 : Blo 1016603 3441095 := bstep (se 1 (by rfl) ⟨2580821, by rfl⟩ : syracuseStep 3441095 = 5161643) B5161643
theorem B1147495 : Blo 1016603 1147495 := bstep (se 1 (by rfl) ⟨860621, by rfl⟩ : syracuseStep 1147495 = 1721243) B1721243
theorem B3441419 : Blo 1016603 3441419 := bstep (se 1 (by rfl) ⟨2581064, by rfl⟩ : syracuseStep 3441419 = 5162129) B5162129
theorem B2753327 : Blo 1016603 2753327 := bstep (se 1 (by rfl) ⟨2064995, by rfl⟩ : syracuseStep 2753327 = 4129991) B4129991
theorem B2294585 : Blo 1016603 2294585 := bstep (se 2 (by rfl) ⟨860469, by rfl⟩ : syracuseStep 2294585 = 1720939) B1720939
theorem B1016687 : Blo 1016603 1016687 := bstep (se 1 (by rfl) ⟨762515, by rfl⟩ : syracuseStep 1016687 = 1525031) B1525031
theorem B2294639 : Blo 1016603 2294639 := bstep (se 1 (by rfl) ⟨1720979, by rfl⟩ : syracuseStep 2294639 = 3441959) B3441959
theorem B6357917 : Blo 1016603 6357917 := bstep (se 3 (by rfl) ⟨1192109, by rfl⟩ : syracuseStep 6357917 = 2384219) B2384219
theorem B1016743 : Blo 1016603 1016743 := bstep (se 1 (by rfl) ⟨762557, by rfl⟩ : syracuseStep 1016743 = 1525115) B1525115
theorem B7734203 : Blo 1016603 7734203 := bstep (se 1 (by rfl) ⟨5800652, by rfl⟩ : syracuseStep 7734203 = 11601305) B11601305
theorem B1016827 : Blo 1016603 1016827 := bstep (se 1 (by rfl) ⟨762620, by rfl⟩ : syracuseStep 1016827 = 1525241) B1525241
theorem B3441689 : Blo 1016603 3441689 := bstep (se 2 (by rfl) ⟨1290633, by rfl⟩ : syracuseStep 3441689 = 2581267) B2581267
theorem B5801017 : Blo 1016603 5801017 := bstep (se 2 (by rfl) ⟨2175381, by rfl⟩ : syracuseStep 5801017 = 4350763) B4350763
theorem B1016895 : Blo 1016603 1016895 := bstep (se 1 (by rfl) ⟨762671, by rfl⟩ : syracuseStep 1016895 = 1525343) B1525343
theorem B7537769 : Blo 1016603 7537769 := bstep (se 2 (by rfl) ⟨2826663, by rfl⟩ : syracuseStep 7537769 = 5653327) B5653327
theorem B1017039 : Blo 1016603 1017039 := bstep (se 1 (by rfl) ⟨762779, by rfl⟩ : syracuseStep 1017039 = 1525559) B1525559
theorem B1017243 : Blo 1016603 1017243 := bstep (se 1 (by rfl) ⟨762932, by rfl⟩ : syracuseStep 1017243 = 1525865) B1525865
theorem B2295215 : Blo 1016603 2295215 := bstep (se 1 (by rfl) ⟨1721411, by rfl⟩ : syracuseStep 2295215 = 3442823) B3442823
theorem B1017455 : Blo 1016603 1017455 := bstep (se 1 (by rfl) ⟨763091, by rfl⟩ : syracuseStep 1017455 = 1526183) B1526183
theorem B3442337 : Blo 1016603 3442337 := bstep (se 2 (by rfl) ⟨1290876, by rfl⟩ : syracuseStep 3442337 = 2581753) B2581753
theorem B1017511 : Blo 1016603 1017511 := bstep (se 1 (by rfl) ⟨763133, by rfl⟩ : syracuseStep 1017511 = 1526267) B1526267
theorem B1017595 : Blo 1016603 1017595 := bstep (se 1 (by rfl) ⟨763196, by rfl⟩ : syracuseStep 1017595 = 1526393) B1526393
theorem B1017631 : Blo 1016603 1017631 := bstep (se 1 (by rfl) ⟨763223, by rfl⟩ : syracuseStep 1017631 = 1526447) B1526447
theorem B1017663 : Blo 1016603 1017663 := bstep (se 1 (by rfl) ⟨763247, by rfl⟩ : syracuseStep 1017663 = 1526495) B1526495
theorem B1017839 : Blo 1016603 1017839 := bstep (se 1 (by rfl) ⟨763379, by rfl⟩ : syracuseStep 1017839 = 1526759) B1526759
theorem B3868681 : Blo 1016603 3868681 := bstep (se 2 (by rfl) ⟨1450755, by rfl⟩ : syracuseStep 3868681 = 2901511) B2901511
theorem B1018011 : Blo 1016603 1018011 := bstep (se 1 (by rfl) ⟨763508, by rfl⟩ : syracuseStep 1018011 = 1527017) B1527017
theorem B1018047 : Blo 1016603 1018047 := bstep (se 1 (by rfl) ⟨763535, by rfl⟩ : syracuseStep 1018047 = 1527071) B1527071
theorem B2296043 : Blo 1016603 2296043 := bstep (se 1 (by rfl) ⟨1722032, by rfl⟩ : syracuseStep 2296043 = 3444065) B3444065
theorem B7440679 : Blo 1016603 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B1018159 : Blo 1016603 1018159 := bstep (se 1 (by rfl) ⟨763619, by rfl⟩ : syracuseStep 1018159 = 1527239) B1527239
theorem B3443039 : Blo 1016603 3443039 := bstep (se 1 (by rfl) ⟨2582279, by rfl⟩ : syracuseStep 3443039 = 5164559) B5164559
theorem B3869153 : Blo 1016603 3869153 := bstep (se 2 (by rfl) ⟨1450932, by rfl⟩ : syracuseStep 3869153 = 2901865) B2901865
theorem B3443201 : Blo 1016603 3443201 := bstep (se 2 (by rfl) ⟨1291200, by rfl⟩ : syracuseStep 3443201 = 2582401) B2582401
theorem B24807961 : Blo 1016603 24807961 := bstep (se 2 (by rfl) ⟨9302985, by rfl⟩ : syracuseStep 24807961 = 18605971) B18605971
theorem B1018395 : Blo 1016603 1018395 := bstep (se 1 (by rfl) ⟨763796, by rfl⟩ : syracuseStep 1018395 = 1527593) B1527593
theorem B1018399 : Blo 1016603 1018399 := bstep (se 1 (by rfl) ⟨763799, by rfl⟩ : syracuseStep 1018399 = 1527599) B1527599
theorem B1018715 : Blo 1016603 1018715 := bstep (se 1 (by rfl) ⟨764036, by rfl⟩ : syracuseStep 1018715 = 1528073) B1528073
theorem B1018783 : Blo 1016603 1018783 := bstep (se 1 (by rfl) ⟨764087, by rfl⟩ : syracuseStep 1018783 = 1528175) B1528175
theorem B3443687 : Blo 1016603 3443687 := bstep (se 1 (by rfl) ⟨2582765, by rfl⟩ : syracuseStep 3443687 = 5165531) B5165531
theorem B1018927 : Blo 1016603 1018927 := bstep (se 1 (by rfl) ⟨764195, by rfl⟩ : syracuseStep 1018927 = 1528391) B1528391
theorem B3673135 : Blo 1016603 3673135 := bstep (se 1 (by rfl) ⟨2754851, by rfl⟩ : syracuseStep 3673135 = 5509703) B5509703
theorem B1018951 : Blo 1016603 1018951 := bstep (se 1 (by rfl) ⟨764213, by rfl⟩ : syracuseStep 1018951 = 1528427) B1528427
theorem B1674361 : Blo 1016603 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B10456253 : Blo 1016603 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B5508319 : Blo 1016603 5508319 := bstep (se 1 (by rfl) ⟨4131239, by rfl⟩ : syracuseStep 5508319 = 8262479) B8262479
theorem B1019103 : Blo 1016603 1019103 := bstep (se 1 (by rfl) ⟨764327, by rfl⟩ : syracuseStep 1019103 = 1528655) B1528655
theorem B3444011 : Blo 1016603 3444011 := bstep (se 1 (by rfl) ⟨2583008, by rfl⟩ : syracuseStep 3444011 = 5166017) B5166017
theorem B11308339 : Blo 1016603 11308339 := bstep (se 1 (by rfl) ⟨8481254, by rfl⟩ : syracuseStep 11308339 = 16962509) B16962509
theorem B5803433 : Blo 1016603 5803433 := bstep (se 2 (by rfl) ⟨2176287, by rfl⟩ : syracuseStep 5803433 = 4352575) B4352575
theorem B1019367 : Blo 1016603 1019367 := bstep (se 1 (by rfl) ⟨764525, by rfl⟩ : syracuseStep 1019367 = 1529051) B1529051
theorem B3444281 : Blo 1016603 3444281 := bstep (se 2 (by rfl) ⟨1291605, by rfl⟩ : syracuseStep 3444281 = 2583211) B2583211
theorem B1019483 : Blo 1016603 1019483 := bstep (se 1 (by rfl) ⟨764612, by rfl⟩ : syracuseStep 1019483 = 1529225) B1529225
theorem B59477773 : Blo 1016603 59477773 := bstep (se 3 (by rfl) ⟨11152082, by rfl⟩ : syracuseStep 59477773 = 22304165) B22304165
theorem B6524711 : Blo 1016603 6524711 := bstep (se 1 (by rfl) ⟨4893533, by rfl⟩ : syracuseStep 6524711 = 9787067) B9787067
theorem B1019719 : Blo 1016603 1019719 := bstep (se 1 (by rfl) ⟨764789, by rfl⟩ : syracuseStep 1019719 = 1529579) B1529579
theorem B5148521 : Blo 1016603 5148521 := bstep (se 2 (by rfl) ⟨1930695, by rfl⟩ : syracuseStep 5148521 = 3861391) B3861391
theorem B7245713 : Blo 1016603 7245713 := bstep (se 2 (by rfl) ⟨2717142, by rfl⟩ : syracuseStep 7245713 = 5434285) B5434285
theorem B1019871 : Blo 1016603 1019871 := bstep (se 1 (by rfl) ⟨764903, by rfl⟩ : syracuseStep 1019871 = 1529807) B1529807
theorem B1085671 : Blo 1016603 1085671 := bstep (se 1 (by rfl) ⟨814253, by rfl⟩ : syracuseStep 1085671 = 1628507) B1628507
theorem B1020135 : Blo 1016603 1020135 := bstep (se 1 (by rfl) ⟨765101, by rfl⟩ : syracuseStep 1020135 = 1530203) B1530203
theorem B7836031 : Blo 1016603 7836031 := bstep (se 1 (by rfl) ⟨5877023, by rfl⟩ : syracuseStep 7836031 = 11754047) B11754047
theorem B1020287 : Blo 1016603 1020287 := bstep (se 1 (by rfl) ⟨765215, by rfl⟩ : syracuseStep 1020287 = 1530431) B1530431
theorem B5509549 : Blo 1016603 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B1020367 : Blo 1016603 1020367 := bstep (se 1 (by rfl) ⟨765275, by rfl⟩ : syracuseStep 1020367 = 1530551) B1530551
theorem B1020519 : Blo 1016603 1020519 := bstep (se 1 (by rfl) ⟨765389, by rfl⟩ : syracuseStep 1020519 = 1530779) B1530779
theorem B2757739 : Blo 1016603 2757739 := bstep (se 1 (by rfl) ⟨2068304, by rfl⟩ : syracuseStep 2757739 = 4136609) B4136609
theorem B7738577 : Blo 1016603 7738577 := bstep (se 2 (by rfl) ⟨2901966, by rfl⟩ : syracuseStep 7738577 = 5803933) B5803933
theorem B5510587 : Blo 1016603 5510587 := bstep (se 1 (by rfl) ⟨4132940, by rfl⟩ : syracuseStep 5510587 = 8265881) B8265881
theorem B3872569 : Blo 1016603 3872569 := bstep (se 2 (by rfl) ⟨1452213, by rfl⟩ : syracuseStep 3872569 = 2904427) B2904427
theorem B6527375 : Blo 1016603 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B12393371 : Blo 1016603 12393371 := bstep (se 1 (by rfl) ⟨9295028, by rfl⟩ : syracuseStep 12393371 = 18590057) B18590057
theorem B8690591 : Blo 1016603 8690591 := bstep (se 1 (by rfl) ⟨6517943, by rfl⟩ : syracuseStep 8690591 = 13035887) B13035887
theorem B19831837 : Blo 1016603 19831837 := bstep (se 3 (by rfl) ⟨3718469, by rfl⟩ : syracuseStep 19831837 = 7436939) B7436939
theorem B1743913 : Blo 1016603 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B10460285 : Blo 1016603 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B13049009 : Blo 1016603 13049009 := bstep (se 2 (by rfl) ⟨4893378, by rfl⟩ : syracuseStep 13049009 = 9786757) B9786757
theorem B7741007 : Blo 1016603 7741007 := bstep (se 1 (by rfl) ⟨5805755, by rfl⟩ : syracuseStep 7741007 = 11611511) B11611511
theorem B13213331 : Blo 1016603 13213331 := bstep (se 1 (by rfl) ⟨9909998, by rfl⟩ : syracuseStep 13213331 = 19819997) B19819997
theorem B7839611 : Blo 1016603 7839611 := bstep (se 1 (by rfl) ⟨5879708, by rfl⟩ : syracuseStep 7839611 = 11759417) B11759417
theorem B2171657 : Blo 1016603 2171657 := bstep (se 2 (by rfl) ⟨814371, by rfl⟩ : syracuseStep 2171657 = 1628743) B1628743
theorem B5514095 : Blo 1016603 5514095 := bstep (se 1 (by rfl) ⟨4135571, by rfl⟩ : syracuseStep 5514095 = 8271143) B8271143
theorem B3187667 : Blo 1016603 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B7349413 : Blo 1016603 7349413 := bstep (se 4 (by rfl) ⟨689007, by rfl⟩ : syracuseStep 7349413 = 1378015) B1378015
theorem B1287343 : Blo 1016603 1287343 := bstep (se 1 (by rfl) ⟨965507, by rfl⟩ : syracuseStep 1287343 = 1931015) B1931015
theorem B6956221 : Blo 1016603 6956221 := bstep (se 3 (by rfl) ⟨1304291, by rfl⟩ : syracuseStep 6956221 = 2608583) B2608583
theorem B11183293 : Blo 1016603 11183293 := bstep (se 3 (by rfl) ⟨2096867, by rfl⟩ : syracuseStep 11183293 = 4193735) B4193735
theorem B5809583 : Blo 1016603 5809583 := bstep (se 1 (by rfl) ⟨4357187, by rfl⟩ : syracuseStep 5809583 = 8714375) B8714375
theorem B8824403 : Blo 1016603 8824403 := bstep (se 1 (by rfl) ⟨6618302, by rfl⟩ : syracuseStep 8824403 = 13236605) B13236605
theorem B3483257 : Blo 1016603 3483257 := bstep (se 2 (by rfl) ⟨1306221, by rfl⟩ : syracuseStep 3483257 = 2612443) B2612443
theorem B7350425 : Blo 1016603 7350425 := bstep (se 2 (by rfl) ⟨2756409, by rfl⟩ : syracuseStep 7350425 = 5512819) B5512819
theorem B1289287 : Blo 1016603 1289287 := bstep (se 1 (by rfl) ⟨966965, by rfl⟩ : syracuseStep 1289287 = 1933931) B1933931
theorem B9940553 : Blo 1016603 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B1322587 : Blo 1016603 1322587 := bstep (se 1 (by rfl) ⟨991940, by rfl⟩ : syracuseStep 1322587 = 1983881) B1983881
theorem B2174759 : Blo 1016603 2174759 := bstep (se 1 (by rfl) ⟨1631069, by rfl⟩ : syracuseStep 2174759 = 3262139) B3262139
theorem B1290107 : Blo 1016603 1290107 := bstep (se 1 (by rfl) ⟨967580, by rfl⟩ : syracuseStep 1290107 = 1935161) B1935161
theorem B4403099 : Blo 1016603 4403099 := bstep (se 1 (by rfl) ⟨3302324, by rfl⟩ : syracuseStep 4403099 = 6604649) B6604649
theorem B14495915 : Blo 1016603 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B1716511 : Blo 1016603 1716511 := bstep (se 1 (by rfl) ⟨1287383, by rfl⟩ : syracuseStep 1716511 = 2574767) B2574767
theorem B5222711 : Blo 1016603 5222711 := bstep (se 1 (by rfl) ⟨3917033, by rfl⟩ : syracuseStep 5222711 = 7834067) B7834067
theorem B4895225 : Blo 1016603 4895225 := bstep (se 2 (by rfl) ⟨1835709, by rfl⟩ : syracuseStep 4895225 = 3671419) B3671419
theorem B1717159 : Blo 1016603 1717159 := bstep (se 1 (by rfl) ⟨1287869, by rfl⟩ : syracuseStep 1717159 = 2575739) B2575739
theorem B1717321 : Blo 1016603 1717321 := bstep (se 2 (by rfl) ⟨643995, by rfl⟩ : syracuseStep 1717321 = 1287991) B1287991
theorem B1717355 : Blo 1016603 1717355 := bstep (se 1 (by rfl) ⟨1288016, by rfl⟩ : syracuseStep 1717355 = 2576033) B2576033
theorem B11023559 : Blo 1016603 11023559 := bstep (se 1 (by rfl) ⟨8267669, by rfl⟩ : syracuseStep 11023559 = 16535339) B16535339
theorem B2897183 : Blo 1016603 2897183 := bstep (se 1 (by rfl) ⟨2172887, by rfl⟩ : syracuseStep 2897183 = 4345775) B4345775
theorem B1652447 : Blo 1016603 1652447 := bstep (se 1 (by rfl) ⟨1239335, by rfl⟩ : syracuseStep 1652447 = 2478671) B2478671
theorem B7354601 : Blo 1016603 7354601 := bstep (se 2 (by rfl) ⟨2757975, by rfl⟩ : syracuseStep 7354601 = 5515951) B5515951
theorem B1718651 : Blo 1016603 1718651 := bstep (se 1 (by rfl) ⟨1288988, by rfl⟩ : syracuseStep 1718651 = 2577977) B2577977
theorem B1718921 : Blo 1016603 1718921 := bstep (se 2 (by rfl) ⟨644595, by rfl⟩ : syracuseStep 1718921 = 1289191) B1289191
theorem B2898767 : Blo 1016603 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B11582351 : Blo 1016603 11582351 := bstep (se 1 (by rfl) ⟨8686763, by rfl⟩ : syracuseStep 11582351 = 17373527) B17373527
theorem B6536375 : Blo 1016603 6536375 := bstep (se 1 (by rfl) ⟨4902281, by rfl⟩ : syracuseStep 6536375 = 9804563) B9804563
theorem B5160185 : Blo 1016603 5160185 := bstep (se 2 (by rfl) ⟨1935069, by rfl⟩ : syracuseStep 5160185 = 3870139) B3870139
theorem B4964183 : Blo 1016603 4964183 := bstep (se 1 (by rfl) ⟨3723137, by rfl⟩ : syracuseStep 4964183 = 7446275) B7446275
theorem B1720507 : Blo 1016603 1720507 := bstep (se 1 (by rfl) ⟨1290380, by rfl⟩ : syracuseStep 1720507 = 2580761) B2580761
theorem B1720703 : Blo 1016603 1720703 := bstep (se 1 (by rfl) ⟨1290527, by rfl⟩ : syracuseStep 1720703 = 2581055) B2581055
theorem B11747767 : Blo 1016603 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B2900407 : Blo 1016603 2900407 := bstep (se 1 (by rfl) ⟨2175305, by rfl⟩ : syracuseStep 2900407 = 4350611) B4350611
theorem B4637135 : Blo 1016603 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B1721135 : Blo 1016603 1721135 := bstep (se 1 (by rfl) ⟨1290851, by rfl⟩ : syracuseStep 1721135 = 2581703) B2581703
theorem B1524911 : Blo 1016603 1524911 := bstep (se 1 (by rfl) ⟨1143683, by rfl⟩ : syracuseStep 1524911 = 2287367) B2287367
theorem B3261971 : Blo 1016603 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B1525319 : Blo 1016603 1525319 := bstep (se 1 (by rfl) ⟨1143989, by rfl⟩ : syracuseStep 1525319 = 2287979) B2287979
theorem B1525415 : Blo 1016603 1525415 := bstep (se 1 (by rfl) ⟨1144061, by rfl⟩ : syracuseStep 1525415 = 2288123) B2288123
theorem B4343519 : Blo 1016603 4343519 := bstep (se 1 (by rfl) ⟨3257639, by rfl⟩ : syracuseStep 4343519 = 6515279) B6515279
theorem B1525499 : Blo 1016603 1525499 := bstep (se 1 (by rfl) ⟨1144124, by rfl⟩ : syracuseStep 1525499 = 2288249) B2288249
theorem B1722107 : Blo 1016603 1722107 := bstep (se 1 (by rfl) ⟨1291580, by rfl⟩ : syracuseStep 1722107 = 2583161) B2583161
theorem B1525535 : Blo 1016603 1525535 := bstep (se 1 (by rfl) ⟨1144151, by rfl⟩ : syracuseStep 1525535 = 2288303) B2288303
theorem B1034047 : Blo 1016603 1034047 := bstep (se 1 (by rfl) ⟨775535, by rfl⟩ : syracuseStep 1034047 = 1551071) B1551071
theorem B1525583 : Blo 1016603 1525583 := bstep (se 1 (by rfl) ⟨1144187, by rfl⟩ : syracuseStep 1525583 = 2288375) B2288375
theorem B1525703 : Blo 1016603 1525703 := bstep (se 1 (by rfl) ⟨1144277, by rfl⟩ : syracuseStep 1525703 = 2288555) B2288555
theorem B1526057 : Blo 1016603 1526057 := bstep (se 2 (by rfl) ⟨572271, by rfl⟩ : syracuseStep 1526057 = 1144543) B1144543
theorem B1526063 : Blo 1016603 1526063 := bstep (se 1 (by rfl) ⟨1144547, by rfl⟩ : syracuseStep 1526063 = 2289095) B2289095
theorem B19614109 : Blo 1016603 19614109 := bstep (se 3 (by rfl) ⟨3677645, by rfl⟩ : syracuseStep 19614109 = 7355291) B7355291
theorem B1526303 : Blo 1016603 1526303 := bstep (se 1 (by rfl) ⟨1144727, by rfl⟩ : syracuseStep 1526303 = 2289455) B2289455
theorem B1526687 : Blo 1016603 1526687 := bstep (se 1 (by rfl) ⟨1145015, by rfl⟩ : syracuseStep 1526687 = 2290031) B2290031
theorem B1526735 : Blo 1016603 1526735 := bstep (se 1 (by rfl) ⟨1145051, by rfl⟩ : syracuseStep 1526735 = 2290103) B2290103
theorem B2903015 : Blo 1016603 2903015 := bstep (se 1 (by rfl) ⟨2177261, by rfl⟩ : syracuseStep 2903015 = 4354523) B4354523
theorem B8702963 : Blo 1016603 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B10472435 : Blo 1016603 10472435 := bstep (se 1 (by rfl) ⟨7854326, by rfl⟩ : syracuseStep 10472435 = 15708653) B15708653
theorem B1526825 : Blo 1016603 1526825 := bstep (se 2 (by rfl) ⟨572559, by rfl⟩ : syracuseStep 1526825 = 1145119) B1145119
theorem B1526831 : Blo 1016603 1526831 := bstep (se 1 (by rfl) ⟨1145123, by rfl⟩ : syracuseStep 1526831 = 2290247) B2290247
theorem B23481409 : Blo 1016603 23481409 := bstep (se 2 (by rfl) ⟨8805528, by rfl⟩ : syracuseStep 23481409 = 17611057) B17611057
theorem B1526855 : Blo 1016603 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B11586725 : Blo 1016603 11586725 := bstep (se 4 (by rfl) ⟨1086255, by rfl⟩ : syracuseStep 11586725 = 2172511) B2172511
theorem B1527119 : Blo 1016603 1527119 := bstep (se 1 (by rfl) ⟨1145339, by rfl⟩ : syracuseStep 1527119 = 2290679) B2290679
theorem B1527209 : Blo 1016603 1527209 := bstep (se 2 (by rfl) ⟨572703, by rfl⟩ : syracuseStep 1527209 = 1145407) B1145407
theorem B9784759 : Blo 1016603 9784759 := bstep (se 1 (by rfl) ⟨7338569, by rfl⟩ : syracuseStep 9784759 = 14677139) B14677139
theorem B10472975 : Blo 1016603 10472975 := bstep (se 1 (by rfl) ⟨7854731, by rfl⟩ : syracuseStep 10472975 = 15709463) B15709463
theorem B1527359 : Blo 1016603 1527359 := bstep (se 1 (by rfl) ⟨1145519, by rfl⟩ : syracuseStep 1527359 = 2291039) B2291039
theorem B4345501 : Blo 1016603 4345501 := bstep (se 3 (by rfl) ⟨814781, by rfl⟩ : syracuseStep 4345501 = 1629563) B1629563
theorem B1527623 : Blo 1016603 1527623 := bstep (se 1 (by rfl) ⟨1145717, by rfl⟩ : syracuseStep 1527623 = 2291435) B2291435
theorem B1527707 : Blo 1016603 1527707 := bstep (se 1 (by rfl) ⟨1145780, by rfl⟩ : syracuseStep 1527707 = 2291561) B2291561
theorem B1528271 : Blo 1016603 1528271 := bstep (se 1 (by rfl) ⟨1146203, by rfl⟩ : syracuseStep 1528271 = 2292407) B2292407
theorem B4641239 : Blo 1016603 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B1528313 : Blo 1016603 1528313 := bstep (se 2 (by rfl) ⟨573117, by rfl⟩ : syracuseStep 1528313 = 1146235) B1146235
theorem B2904655 : Blo 1016603 2904655 := bstep (se 1 (by rfl) ⟨2178491, by rfl⟩ : syracuseStep 2904655 = 4356983) B4356983
theorem B1528415 : Blo 1016603 1528415 := bstep (se 1 (by rfl) ⟨1146311, by rfl⟩ : syracuseStep 1528415 = 2292623) B2292623
theorem B4411999 : Blo 1016603 4411999 := bstep (se 1 (by rfl) ⟨3308999, by rfl⟩ : syracuseStep 4411999 = 6617999) B6617999
theorem B9294887 : Blo 1016603 9294887 := bstep (se 1 (by rfl) ⟨6971165, by rfl⟩ : syracuseStep 9294887 = 13942331) B13942331
theorem B1528895 : Blo 1016603 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B1528937 : Blo 1016603 1528937 := bstep (se 2 (by rfl) ⟨573351, by rfl⟩ : syracuseStep 1528937 = 1146703) B1146703
theorem B1529039 : Blo 1016603 1529039 := bstep (se 1 (by rfl) ⟨1146779, by rfl⟩ : syracuseStep 1529039 = 2293559) B2293559
theorem B2577683 : Blo 1016603 2577683 := bstep (se 1 (by rfl) ⟨1933262, by rfl⟩ : syracuseStep 2577683 = 3866525) B3866525
theorem B1529243 : Blo 1016603 1529243 := bstep (se 1 (by rfl) ⟨1146932, by rfl⟩ : syracuseStep 1529243 = 2293865) B2293865
theorem B1529465 : Blo 1016603 1529465 := bstep (se 2 (by rfl) ⟨573549, by rfl⟩ : syracuseStep 1529465 = 1147099) B1147099
theorem B1529567 : Blo 1016603 1529567 := bstep (se 1 (by rfl) ⟨1147175, by rfl⟩ : syracuseStep 1529567 = 2294351) B2294351
theorem B5232395 : Blo 1016603 5232395 := bstep (se 1 (by rfl) ⟨3924296, by rfl⟩ : syracuseStep 5232395 = 7848593) B7848593
theorem B1529663 : Blo 1016603 1529663 := bstep (se 1 (by rfl) ⟨1147247, by rfl⟩ : syracuseStep 1529663 = 2294495) B2294495
theorem B1529831 : Blo 1016603 1529831 := bstep (se 1 (by rfl) ⟨1147373, by rfl⟩ : syracuseStep 1529831 = 2294747) B2294747
theorem B1529849 : Blo 1016603 1529849 := bstep (se 2 (by rfl) ⟨573693, by rfl⟩ : syracuseStep 1529849 = 1147387) B1147387
theorem B1529951 : Blo 1016603 1529951 := bstep (se 1 (by rfl) ⟨1147463, by rfl⟩ : syracuseStep 1529951 = 2294927) B2294927
theorem B1530011 : Blo 1016603 1530011 := bstep (se 1 (by rfl) ⟨1147508, by rfl⟩ : syracuseStep 1530011 = 2295017) B2295017
theorem B2906273 : Blo 1016603 2906273 := bstep (se 2 (by rfl) ⟨1089852, by rfl⟩ : syracuseStep 2906273 = 2179705) B2179705
theorem B1530047 : Blo 1016603 1530047 := bstep (se 1 (by rfl) ⟨1147535, by rfl⟩ : syracuseStep 1530047 = 2295071) B2295071
theorem B1530089 : Blo 1016603 1530089 := bstep (se 2 (by rfl) ⟨573783, by rfl⟩ : syracuseStep 1530089 = 1147567) B1147567
theorem B2578675 : Blo 1016603 2578675 := bstep (se 1 (by rfl) ⟨1934006, by rfl⟩ : syracuseStep 2578675 = 3868013) B3868013
theorem B4348201 : Blo 1016603 4348201 := bstep (se 2 (by rfl) ⟨1630575, by rfl⟩ : syracuseStep 4348201 = 3261151) B3261151
theorem B1530395 : Blo 1016603 1530395 := bstep (se 1 (by rfl) ⟨1147796, by rfl⟩ : syracuseStep 1530395 = 2295593) B2295593
theorem B1530473 : Blo 1016603 1530473 := bstep (se 2 (by rfl) ⟨573927, by rfl⟩ : syracuseStep 1530473 = 1147855) B1147855
theorem B1629019 : Blo 1016603 1629019 := bstep (se 1 (by rfl) ⟨1221764, by rfl⟩ : syracuseStep 1629019 = 2443529) B2443529
theorem B3431375 : Blo 1016603 3431375 := bstep (se 1 (by rfl) ⟨2573531, by rfl⟩ : syracuseStep 3431375 = 5147063) B5147063
theorem B1629551 : Blo 1016603 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B7331303 : Blo 1016603 7331303 := bstep (se 1 (by rfl) ⟨5498477, by rfl⟩ : syracuseStep 7331303 = 10996955) B10996955
theorem B1629839 : Blo 1016603 1629839 := bstep (se 1 (by rfl) ⟨1222379, by rfl⟩ : syracuseStep 1629839 = 2444759) B2444759
theorem B13033223 : Blo 1016603 13033223 := bstep (se 1 (by rfl) ⟨9774917, by rfl⟩ : syracuseStep 13033223 = 19549835) B19549835
theorem B5955383 : Blo 1016603 5955383 := bstep (se 1 (by rfl) ⟨4466537, by rfl⟩ : syracuseStep 5955383 = 8933075) B8933075
theorem B2580295 : Blo 1016603 2580295 := bstep (se 1 (by rfl) ⟨1935221, by rfl⟩ : syracuseStep 2580295 = 3870443) B3870443
theorem B2580619 : Blo 1016603 2580619 := bstep (se 1 (by rfl) ⟨1935464, by rfl⟩ : syracuseStep 2580619 = 3870929) B3870929
theorem B161014169 : Blo 1016603 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B3432887 : Blo 1016603 3432887 := bstep (se 1 (by rfl) ⟨2574665, by rfl⟩ : syracuseStep 3432887 = 5149331) B5149331
theorem B2580923 : Blo 1016603 2580923 := bstep (se 1 (by rfl) ⟨1935692, by rfl⟩ : syracuseStep 2580923 = 3871385) B3871385
theorem B2580943 : Blo 1016603 2580943 := bstep (se 1 (by rfl) ⟨1935707, by rfl⟩ : syracuseStep 2580943 = 3871415) B3871415
theorem B9790105 : Blo 1016603 9790105 := bstep (se 2 (by rfl) ⟨3671289, by rfl⟩ : syracuseStep 9790105 = 7342579) B7342579
theorem B3269531 : Blo 1016603 3269531 := bstep (se 1 (by rfl) ⟨2452148, by rfl⟩ : syracuseStep 3269531 = 4904297) B4904297
theorem B3433373 : Blo 1016603 3433373 := bstep (se 3 (by rfl) ⟨643757, by rfl⟩ : syracuseStep 3433373 = 1287515) B1287515
theorem B3433427 : Blo 1016603 3433427 := bstep (se 1 (by rfl) ⟨2575070, by rfl⟩ : syracuseStep 3433427 = 5150141) B5150141
theorem B1467455 : Blo 1016603 1467455 := bstep (se 1 (by rfl) ⟨1100591, by rfl⟩ : syracuseStep 1467455 = 2201183) B2201183
theorem B16541101 : Blo 1016603 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B2582239 : Blo 1016603 2582239 := bstep (se 1 (by rfl) ⟨1936679, by rfl⟩ : syracuseStep 2582239 = 3873359) B3873359
theorem B2287439 : Blo 1016603 2287439 := bstep (se 1 (by rfl) ⟨1715579, by rfl⟩ : syracuseStep 2287439 = 3431159) B3431159
theorem B2582351 : Blo 1016603 2582351 := bstep (se 1 (by rfl) ⟨1936763, by rfl⟩ : syracuseStep 2582351 = 3873527) B3873527
theorem B2287457 : Blo 1016603 2287457 := bstep (se 2 (by rfl) ⟨857796, by rfl⟩ : syracuseStep 2287457 = 1715593) B1715593
theorem B19589201 : Blo 1016603 19589201 := bstep (se 2 (by rfl) ⟨7345950, by rfl⟩ : syracuseStep 19589201 = 14691901) B14691901
theorem B2288033 : Blo 1016603 2288033 := bstep (se 2 (by rfl) ⟨858012, by rfl⟩ : syracuseStep 2288033 = 1716025) B1716025
theorem B3664385 : Blo 1016603 3664385 := bstep (se 2 (by rfl) ⟨1374144, by rfl⟩ : syracuseStep 3664385 = 2748289) B2748289
theorem B2288159 : Blo 1016603 2288159 := bstep (se 1 (by rfl) ⟨1716119, by rfl⟩ : syracuseStep 2288159 = 3432239) B3432239
theorem B3435641 : Blo 1016603 3435641 := bstep (se 2 (by rfl) ⟨1288365, by rfl⟩ : syracuseStep 3435641 = 2576731) B2576731
theorem B2485529 : Blo 1016603 2485529 := bstep (se 2 (by rfl) ⟨932073, by rfl⟩ : syracuseStep 2485529 = 1864147) B1864147
theorem B3435965 : Blo 1016603 3435965 := bstep (se 3 (by rfl) ⟨644243, by rfl⟩ : syracuseStep 3435965 = 1288487) B1288487
theorem B11595473 : Blo 1016603 11595473 := bstep (se 2 (by rfl) ⟨4348302, by rfl⟩ : syracuseStep 11595473 = 8696605) B8696605
theorem B106000109 : Blo 1016603 106000109 := bstep (se 3 (by rfl) ⟨19875020, by rfl⟩ : syracuseStep 106000109 = 39750041) B39750041
theorem B2289563 : Blo 1016603 2289563 := bstep (se 1 (by rfl) ⟨1717172, by rfl⟩ : syracuseStep 2289563 = 3434345) B3434345
theorem B9793523 : Blo 1016603 9793523 := bstep (se 1 (by rfl) ⟨7345142, by rfl⟩ : syracuseStep 9793523 = 14690285) B14690285
theorem B3436667 : Blo 1016603 3436667 := bstep (se 1 (by rfl) ⟨2577500, by rfl⟩ : syracuseStep 3436667 = 5155001) B5155001
theorem B9433253 : Blo 1016603 9433253 := bstep (se 4 (by rfl) ⟨884367, by rfl⟩ : syracuseStep 9433253 = 1768735) B1768735
theorem B2289851 : Blo 1016603 2289851 := bstep (se 1 (by rfl) ⟨1717388, by rfl⟩ : syracuseStep 2289851 = 3434777) B3434777
theorem B3436829 : Blo 1016603 3436829 := bstep (se 3 (by rfl) ⟨644405, by rfl⟩ : syracuseStep 3436829 = 1288811) B1288811
theorem B1044863 : Blo 1016603 1044863 := bstep (se 1 (by rfl) ⟨783647, by rfl⟩ : syracuseStep 1044863 = 1567295) B1567295
theorem B3436937 : Blo 1016603 3436937 := bstep (se 2 (by rfl) ⟨1288851, by rfl⟩ : syracuseStep 3436937 = 2577703) B2577703
theorem B3863123 : Blo 1016603 3863123 := bstep (se 1 (by rfl) ⟨2897342, by rfl⟩ : syracuseStep 3863123 = 5794685) B5794685
theorem B2290337 : Blo 1016603 2290337 := bstep (se 2 (by rfl) ⟨858876, by rfl⟩ : syracuseStep 2290337 = 1717753) B1717753
theorem B2290697 : Blo 1016603 2290697 := bstep (se 2 (by rfl) ⟨859011, by rfl⟩ : syracuseStep 2290697 = 1718023) B1718023
theorem B2290751 : Blo 1016603 2290751 := bstep (se 1 (by rfl) ⟨1718063, by rfl⟩ : syracuseStep 2290751 = 3436127) B3436127
theorem B3437855 : Blo 1016603 3437855 := bstep (se 1 (by rfl) ⟨2578391, by rfl⟩ : syracuseStep 3437855 = 5156783) B5156783
theorem B1144219 : Blo 1016603 1144219 := bstep (se 1 (by rfl) ⟨858164, by rfl⟩ : syracuseStep 1144219 = 1716329) B1716329
theorem B19559981 : Blo 1016603 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B2291687 : Blo 1016603 2291687 := bstep (se 1 (by rfl) ⟨1718765, by rfl⟩ : syracuseStep 2291687 = 3437531) B3437531
theorem B2291705 : Blo 1016603 2291705 := bstep (se 2 (by rfl) ⟨859389, by rfl⟩ : syracuseStep 2291705 = 1718779) B1718779
theorem B19560527 : Blo 1016603 19560527 := bstep (se 1 (by rfl) ⟨14670395, by rfl⟩ : syracuseStep 19560527 = 29340791) B29340791
theorem B2291795 : Blo 1016603 2291795 := bstep (se 1 (by rfl) ⟨1718846, by rfl⟩ : syracuseStep 2291795 = 3437693) B3437693
theorem B2291867 : Blo 1016603 2291867 := bstep (se 1 (by rfl) ⟨1718900, by rfl⟩ : syracuseStep 2291867 = 3437801) B3437801
theorem B9795755 : Blo 1016603 9795755 := bstep (se 1 (by rfl) ⟨7346816, by rfl⟩ : syracuseStep 9795755 = 14693633) B14693633
theorem B2291975 : Blo 1016603 2291975 := bstep (se 1 (by rfl) ⟨1718981, by rfl⟩ : syracuseStep 2291975 = 3437963) B3437963
theorem B1145371 : Blo 1016603 1145371 := bstep (se 1 (by rfl) ⟨859028, by rfl⟩ : syracuseStep 1145371 = 1718057) B1718057
theorem B2292281 : Blo 1016603 2292281 := bstep (se 2 (by rfl) ⟨859605, by rfl⟩ : syracuseStep 2292281 = 1719211) B1719211
theorem B7731773 : Blo 1016603 7731773 := bstep (se 3 (by rfl) ⟨1449707, by rfl⟩ : syracuseStep 7731773 = 2899415) B2899415
theorem B1932329 : Blo 1016603 1932329 := bstep (se 2 (by rfl) ⟨724623, by rfl⟩ : syracuseStep 1932329 = 1449247) B1449247
theorem B5372999 : Blo 1016603 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B3439745 : Blo 1016603 3439745 := bstep (se 2 (by rfl) ⟨1289904, by rfl⟩ : syracuseStep 3439745 = 2579809) B2579809
theorem B3439799 : Blo 1016603 3439799 := bstep (se 1 (by rfl) ⟨2579849, by rfl⟩ : syracuseStep 3439799 = 5159699) B5159699
theorem B2293001 : Blo 1016603 2293001 := bstep (se 2 (by rfl) ⟨859875, by rfl⟩ : syracuseStep 2293001 = 1719751) B1719751
theorem B1932655 : Blo 1016603 1932655 := bstep (se 1 (by rfl) ⟨1449491, by rfl⟩ : syracuseStep 1932655 = 2898983) B2898983
theorem B1146343 : Blo 1016603 1146343 := bstep (se 1 (by rfl) ⟨859757, by rfl⟩ : syracuseStep 1146343 = 1719515) B1719515
theorem B3440555 : Blo 1016603 3440555 := bstep (se 1 (by rfl) ⟨2580416, by rfl⟩ : syracuseStep 3440555 = 5160833) B5160833
theorem B1146847 : Blo 1016603 1146847 := bstep (se 1 (by rfl) ⟨860135, by rfl⟩ : syracuseStep 1146847 = 1720271) B1720271
theorem B3440825 : Blo 1016603 3440825 := bstep (se 2 (by rfl) ⟨1290309, by rfl⟩ : syracuseStep 3440825 = 2580619) B2580619
theorem B2294009 : Blo 1016603 2294009 := bstep (se 2 (by rfl) ⟨860253, by rfl⟩ : syracuseStep 2294009 = 1720507) B1720507
theorem B1147135 : Blo 1016603 1147135 := bstep (se 1 (by rfl) ⟨860351, by rfl⟩ : syracuseStep 1147135 = 1720703) B1720703
theorem B2294063 : Blo 1016603 2294063 := bstep (se 1 (by rfl) ⟨1720547, by rfl⟩ : syracuseStep 2294063 = 3441095) B3441095
theorem B2294279 : Blo 1016603 2294279 := bstep (se 1 (by rfl) ⟨1720709, by rfl⟩ : syracuseStep 2294279 = 3441419) B3441419
theorem B1835551 : Blo 1016603 1835551 := bstep (se 1 (by rfl) ⟨1376663, by rfl⟩ : syracuseStep 1835551 = 2753327) B2753327
theorem B1147423 : Blo 1016603 1147423 := bstep (se 1 (by rfl) ⟨860567, by rfl⟩ : syracuseStep 1147423 = 1721135) B1721135
theorem B15663689 : Blo 1016603 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B3867209 : Blo 1016603 3867209 := bstep (se 2 (by rfl) ⟨1450203, by rfl⟩ : syracuseStep 3867209 = 2900407) B2900407
theorem B3441257 : Blo 1016603 3441257 := bstep (se 2 (by rfl) ⟨1290471, by rfl⟩ : syracuseStep 3441257 = 2580943) B2580943
theorem B2294459 : Blo 1016603 2294459 := bstep (se 1 (by rfl) ⟨1720844, by rfl⟩ : syracuseStep 2294459 = 3441689) B3441689
theorem B1016607 : Blo 1016603 1016607 := bstep (se 1 (by rfl) ⟨762455, by rfl⟩ : syracuseStep 1016607 = 1524911) B1524911
theorem B1016879 : Blo 1016603 1016879 := bstep (se 1 (by rfl) ⟨762659, by rfl⟩ : syracuseStep 1016879 = 1525319) B1525319
theorem B2294891 : Blo 1016603 2294891 := bstep (se 1 (by rfl) ⟨1721168, by rfl⟩ : syracuseStep 2294891 = 3442337) B3442337
theorem B1016943 : Blo 1016603 1016943 := bstep (se 1 (by rfl) ⟨762707, by rfl⟩ : syracuseStep 1016943 = 1525415) B1525415
theorem B1016999 : Blo 1016603 1016999 := bstep (se 1 (by rfl) ⟨762749, by rfl⟩ : syracuseStep 1016999 = 1525499) B1525499
theorem B1148071 : Blo 1016603 1148071 := bstep (se 1 (by rfl) ⟨861053, by rfl⟩ : syracuseStep 1148071 = 1722107) B1722107
theorem B1017023 : Blo 1016603 1017023 := bstep (se 1 (by rfl) ⟨762767, by rfl⟩ : syracuseStep 1017023 = 1525535) B1525535
theorem B1017055 : Blo 1016603 1017055 := bstep (se 1 (by rfl) ⟨762791, by rfl⟩ : syracuseStep 1017055 = 1525583) B1525583
theorem B1017135 : Blo 1016603 1017135 := bstep (se 1 (by rfl) ⟨762851, by rfl⟩ : syracuseStep 1017135 = 1525703) B1525703
theorem B7734689 : Blo 1016603 7734689 := bstep (se 2 (by rfl) ⟨2900508, by rfl⟩ : syracuseStep 7734689 = 5801017) B5801017
theorem B1017371 : Blo 1016603 1017371 := bstep (se 1 (by rfl) ⟨763028, by rfl⟩ : syracuseStep 1017371 = 1526057) B1526057
theorem B1017375 : Blo 1016603 1017375 := bstep (se 1 (by rfl) ⟨763031, by rfl⟩ : syracuseStep 1017375 = 1526063) B1526063
theorem B39683621 : Blo 1016603 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B9799217 : Blo 1016603 9799217 := bstep (se 2 (by rfl) ⟨3674706, by rfl⟩ : syracuseStep 9799217 = 7349413) B7349413
theorem B2295359 : Blo 1016603 2295359 := bstep (se 1 (by rfl) ⟨1721519, by rfl⟩ : syracuseStep 2295359 = 3443039) B3443039
theorem B9274961 : Blo 1016603 9274961 := bstep (se 2 (by rfl) ⟨3478110, by rfl⟩ : syracuseStep 9274961 = 6956221) B6956221
theorem B14911057 : Blo 1016603 14911057 := bstep (se 2 (by rfl) ⟨5591646, by rfl⟩ : syracuseStep 14911057 = 11183293) B11183293
theorem B2295467 : Blo 1016603 2295467 := bstep (se 1 (by rfl) ⟨1721600, by rfl⟩ : syracuseStep 2295467 = 3443201) B3443201
theorem B1017535 : Blo 1016603 1017535 := bstep (se 1 (by rfl) ⟨763151, by rfl⟩ : syracuseStep 1017535 = 1526303) B1526303
theorem B1017791 : Blo 1016603 1017791 := bstep (se 1 (by rfl) ⟨763343, by rfl⟩ : syracuseStep 1017791 = 1526687) B1526687
theorem B1017823 : Blo 1016603 1017823 := bstep (se 1 (by rfl) ⟨763367, by rfl⟩ : syracuseStep 1017823 = 1526735) B1526735
theorem B1935343 : Blo 1016603 1935343 := bstep (se 1 (by rfl) ⟨1451507, by rfl⟩ : syracuseStep 1935343 = 2903015) B2903015
theorem B2295791 : Blo 1016603 2295791 := bstep (se 1 (by rfl) ⟨1721843, by rfl⟩ : syracuseStep 2295791 = 3443687) B3443687
theorem B5801975 : Blo 1016603 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B6981623 : Blo 1016603 6981623 := bstep (se 1 (by rfl) ⟨5236217, by rfl⟩ : syracuseStep 6981623 = 10472435) B10472435
theorem B1017883 : Blo 1016603 1017883 := bstep (se 1 (by rfl) ⟨763412, by rfl⟩ : syracuseStep 1017883 = 1526825) B1526825
theorem B1017887 : Blo 1016603 1017887 := bstep (se 1 (by rfl) ⟨763415, by rfl⟩ : syracuseStep 1017887 = 1526831) B1526831
theorem B1017903 : Blo 1016603 1017903 := bstep (se 1 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 1017903 = 1526855) B1526855
theorem B2296007 : Blo 1016603 2296007 := bstep (se 1 (by rfl) ⟨1722005, by rfl⟩ : syracuseStep 2296007 = 3444011) B3444011
theorem B1018079 : Blo 1016603 1018079 := bstep (se 1 (by rfl) ⟨763559, by rfl⟩ : syracuseStep 1018079 = 1527119) B1527119
theorem B1018139 : Blo 1016603 1018139 := bstep (se 1 (by rfl) ⟨763604, by rfl⟩ : syracuseStep 1018139 = 1527209) B1527209
theorem B3868955 : Blo 1016603 3868955 := bstep (se 1 (by rfl) ⟨2901716, by rfl⟩ : syracuseStep 3868955 = 5803433) B5803433
theorem B3442985 : Blo 1016603 3442985 := bstep (se 2 (by rfl) ⟨1291119, by rfl⟩ : syracuseStep 3442985 = 2582239) B2582239
theorem B6981983 : Blo 1016603 6981983 := bstep (se 1 (by rfl) ⟨5236487, by rfl⟩ : syracuseStep 6981983 = 10472975) B10472975
theorem B2296187 : Blo 1016603 2296187 := bstep (se 1 (by rfl) ⟨1722140, by rfl⟩ : syracuseStep 2296187 = 3444281) B3444281
theorem B1018239 : Blo 1016603 1018239 := bstep (se 1 (by rfl) ⟨763679, by rfl⟩ : syracuseStep 1018239 = 1527359) B1527359
theorem B8718749 : Blo 1016603 8718749 := bstep (se 3 (by rfl) ⟨1634765, by rfl⟩ : syracuseStep 8718749 = 3269531) B3269531
theorem B1378729 : Blo 1016603 1378729 := bstep (se 2 (by rfl) ⟨517023, by rfl⟩ : syracuseStep 1378729 = 1034047) B1034047
theorem B1018415 : Blo 1016603 1018415 := bstep (se 1 (by rfl) ⟨763811, by rfl⟩ : syracuseStep 1018415 = 1527623) B1527623
theorem B1018471 : Blo 1016603 1018471 := bstep (se 1 (by rfl) ⟨763853, by rfl⟩ : syracuseStep 1018471 = 1527707) B1527707
theorem B1018847 : Blo 1016603 1018847 := bstep (se 1 (by rfl) ⟨764135, by rfl⟩ : syracuseStep 1018847 = 1528271) B1528271
theorem B1018875 : Blo 1016603 1018875 := bstep (se 1 (by rfl) ⟨764156, by rfl⟩ : syracuseStep 1018875 = 1528313) B1528313
theorem B1018943 : Blo 1016603 1018943 := bstep (se 1 (by rfl) ⟨764207, by rfl⟩ : syracuseStep 1018943 = 1528415) B1528415
theorem B26152145 : Blo 1016603 26152145 := bstep (se 2 (by rfl) ⟨9807054, by rfl⟩ : syracuseStep 26152145 = 19614109) B19614109
theorem B6196591 : Blo 1016603 6196591 := bstep (se 1 (by rfl) ⟨4647443, by rfl⟩ : syracuseStep 6196591 = 9294887) B9294887
theorem B1019263 : Blo 1016603 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B1019291 : Blo 1016603 1019291 := bstep (se 1 (by rfl) ⟨764468, by rfl⟩ : syracuseStep 1019291 = 1528937) B1528937
theorem B1019359 : Blo 1016603 1019359 := bstep (se 1 (by rfl) ⟨764519, by rfl⟩ : syracuseStep 1019359 = 1529039) B1529039
theorem B1019495 : Blo 1016603 1019495 := bstep (se 1 (by rfl) ⟨764621, by rfl⟩ : syracuseStep 1019495 = 1529243) B1529243
theorem B1019643 : Blo 1016603 1019643 := bstep (se 1 (by rfl) ⟨764732, by rfl⟩ : syracuseStep 1019643 = 1529465) B1529465
theorem B1019711 : Blo 1016603 1019711 := bstep (se 1 (by rfl) ⟨764783, by rfl⟩ : syracuseStep 1019711 = 1529567) B1529567
theorem B1019775 : Blo 1016603 1019775 := bstep (se 1 (by rfl) ⟨764831, by rfl⟩ : syracuseStep 1019775 = 1529663) B1529663
theorem B1019887 : Blo 1016603 1019887 := bstep (se 1 (by rfl) ⟨764915, by rfl⟩ : syracuseStep 1019887 = 1529831) B1529831
theorem B11145205 : Blo 1016603 11145205 := bstep (se 5 (by rfl) ⟨522431, by rfl⟩ : syracuseStep 11145205 = 1044863) B1044863
theorem B1019899 : Blo 1016603 1019899 := bstep (se 1 (by rfl) ⟨764924, by rfl⟩ : syracuseStep 1019899 = 1529849) B1529849
theorem B1019967 : Blo 1016603 1019967 := bstep (se 1 (by rfl) ⟨764975, by rfl⟩ : syracuseStep 1019967 = 1529951) B1529951
theorem B1020007 : Blo 1016603 1020007 := bstep (se 1 (by rfl) ⟨765005, by rfl⟩ : syracuseStep 1020007 = 1530011) B1530011
theorem B1937515 : Blo 1016603 1937515 := bstep (se 1 (by rfl) ⟨1453136, by rfl⟩ : syracuseStep 1937515 = 2906273) B2906273
theorem B1020031 : Blo 1016603 1020031 := bstep (se 1 (by rfl) ⟨765023, by rfl⟩ : syracuseStep 1020031 = 1530047) B1530047
theorem B1020059 : Blo 1016603 1020059 := bstep (se 1 (by rfl) ⟨765044, by rfl⟩ : syracuseStep 1020059 = 1530089) B1530089
theorem B2232481 : Blo 1016603 2232481 := bstep (se 2 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 2232481 = 1674361) B1674361
theorem B23531741 : Blo 1016603 23531741 := bstep (se 3 (by rfl) ⟨4412201, by rfl⟩ : syracuseStep 23531741 = 8824403) B8824403
theorem B7344425 : Blo 1016603 7344425 := bstep (se 2 (by rfl) ⟨2754159, by rfl⟩ : syracuseStep 7344425 = 5508319) B5508319
theorem B1020263 : Blo 1016603 1020263 := bstep (se 1 (by rfl) ⟨765197, by rfl⟩ : syracuseStep 1020263 = 1530395) B1530395
theorem B1020315 : Blo 1016603 1020315 := bstep (se 1 (by rfl) ⟨765236, by rfl⟩ : syracuseStep 1020315 = 1530473) B1530473
theorem B13046345 : Blo 1016603 13046345 := bstep (se 2 (by rfl) ⟨4892379, by rfl⟩ : syracuseStep 13046345 = 9784759) B9784759
theorem B8262247 : Blo 1016603 8262247 := bstep (se 1 (by rfl) ⟨6196685, by rfl⟩ : syracuseStep 8262247 = 12393371) B12393371
theorem B1086367 : Blo 1016603 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B4887535 : Blo 1016603 4887535 := bstep (se 1 (by rfl) ⟨3665651, by rfl⟩ : syracuseStep 4887535 = 7331303) B7331303
theorem B79303697 : Blo 1016603 79303697 := bstep (se 2 (by rfl) ⟨29738886, by rfl⟩ : syracuseStep 79303697 = 59477773) B59477773
theorem B8688815 : Blo 1016603 8688815 := bstep (se 1 (by rfl) ⟨6516611, by rfl⟩ : syracuseStep 8688815 = 13033223) B13033223
theorem B1447561 : Blo 1016603 1447561 := bstep (se 2 (by rfl) ⟨542835, by rfl⟩ : syracuseStep 1447561 = 1085671) B1085671
theorem B7346065 : Blo 1016603 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B3676063 : Blo 1016603 3676063 := bstep (se 1 (by rfl) ⟨2757047, by rfl⟩ : syracuseStep 3676063 = 5514095) B5514095
theorem B3872873 : Blo 1016603 3872873 := bstep (se 2 (by rfl) ⟨1452327, by rfl⟩ : syracuseStep 3872873 = 2904655) B2904655
theorem B3873055 : Blo 1016603 3873055 := bstep (se 1 (by rfl) ⟨2904791, by rfl⟩ : syracuseStep 3873055 = 5809583) B5809583
theorem B3676985 : Blo 1016603 3676985 := bstep (se 2 (by rfl) ⟨1378869, by rfl⟩ : syracuseStep 3676985 = 2757739) B2757739
theorem B7347449 : Blo 1016603 7347449 := bstep (se 2 (by rfl) ⟨2755293, by rfl⟩ : syracuseStep 7347449 = 5510587) B5510587
theorem B88219205 : Blo 1016603 88219205 := bstep (se 4 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 88219205 = 16541101) B16541101
theorem B6627035 : Blo 1016603 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B1449839 : Blo 1016603 1449839 := bstep (se 1 (by rfl) ⟨1087379, by rfl⟩ : syracuseStep 1449839 = 2174759) B2174759
theorem B6529015 : Blo 1016603 6529015 := bstep (se 1 (by rfl) ⟨4896761, by rfl⟩ : syracuseStep 6529015 = 9793523) B9793523
theorem B3481807 : Blo 1016603 3481807 := bstep (se 1 (by rfl) ⟨2611355, by rfl⟩ : syracuseStep 3481807 = 5222711) B5222711
theorem B7053797 : Blo 1016603 7053797 := bstep (se 4 (by rfl) ⟨661293, by rfl⟩ : syracuseStep 7053797 = 1322587) B1322587
theorem B7349039 : Blo 1016603 7349039 := bstep (se 1 (by rfl) ⟨5511779, by rfl⟩ : syracuseStep 7349039 = 11023559) B11023559
theorem B2172025 : Blo 1016603 2172025 := bstep (se 2 (by rfl) ⟨814509, by rfl⟩ : syracuseStep 2172025 = 1629019) B1629019
theorem B6530503 : Blo 1016603 6530503 := bstep (se 1 (by rfl) ⟨4897877, by rfl⟩ : syracuseStep 6530503 = 9795755) B9795755
theorem B5154515 : Blo 1016603 5154515 := bstep (se 1 (by rfl) ⟨3865886, by rfl⟩ : syracuseStep 5154515 = 7731773) B7731773
theorem B1288219 : Blo 1016603 1288219 := bstep (se 1 (by rfl) ⟨966164, by rfl⟩ : syracuseStep 1288219 = 1932329) B1932329
theorem B3581999 : Blo 1016603 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B9808559 : Blo 1016603 9808559 := bstep (se 1 (by rfl) ⟨7356419, by rfl⟩ : syracuseStep 9808559 = 14712839) B14712839
theorem B4238611 : Blo 1016603 4238611 := bstep (se 1 (by rfl) ⟨3178958, by rfl⟩ : syracuseStep 4238611 = 6357917) B6357917
theorem B5156135 : Blo 1016603 5156135 := bstep (se 1 (by rfl) ⟨3867101, by rfl⟩ : syracuseStep 5156135 = 7734203) B7734203
theorem B5025179 : Blo 1016603 5025179 := bstep (se 1 (by rfl) ⟨3768884, by rfl⟩ : syracuseStep 5025179 = 7537769) B7537769
theorem B13053473 : Blo 1016603 13053473 := bstep (se 2 (by rfl) ⟨4895052, by rfl⟩ : syracuseStep 13053473 = 9790105) B9790105
theorem B2895679 : Blo 1016603 2895679 := bstep (se 1 (by rfl) ⟨2171759, by rfl⟩ : syracuseStep 2895679 = 4343519) B4343519
theorem B12365693 : Blo 1016603 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B1716457 : Blo 1016603 1716457 := bstep (se 2 (by rfl) ⟨643671, by rfl⟩ : syracuseStep 1716457 = 1287343) B1287343
theorem B4830475 : Blo 1016603 4830475 := bstep (se 1 (by rfl) ⟨3622856, by rfl⟩ : syracuseStep 4830475 = 7245713) B7245713
theorem B5158241 : Blo 1016603 5158241 := bstep (se 2 (by rfl) ⟨1934340, by rfl⟩ : syracuseStep 5158241 = 3868681) B3868681
theorem B3913213 : Blo 1016603 3913213 := bstep (se 3 (by rfl) ⟨733727, by rfl⟩ : syracuseStep 3913213 = 1467455) B1467455
theorem B33077281 : Blo 1016603 33077281 := bstep (se 2 (by rfl) ⟨12403980, by rfl⟩ : syracuseStep 33077281 = 24807961) B24807961
theorem B5159051 : Blo 1016603 5159051 := bstep (se 1 (by rfl) ⟨3869288, by rfl⟩ : syracuseStep 5159051 = 7738577) B7738577
theorem B1718455 : Blo 1016603 1718455 := bstep (se 1 (by rfl) ⟨1288841, by rfl⟩ : syracuseStep 1718455 = 2577683) B2577683
theorem B8698589 : Blo 1016603 8698589 := bstep (se 3 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 8698589 = 3261971) B3261971
theorem B4897513 : Blo 1016603 4897513 := bstep (se 2 (by rfl) ⟨1836567, by rfl⟩ : syracuseStep 4897513 = 3673135) B3673135
theorem B31308545 : Blo 1016603 31308545 := bstep (se 2 (by rfl) ⟨11740704, by rfl⟩ : syracuseStep 31308545 = 23481409) B23481409
theorem B1719049 : Blo 1016603 1719049 := bstep (se 2 (by rfl) ⟨644643, by rfl⟩ : syracuseStep 1719049 = 1289287) B1289287
theorem B9288685 : Blo 1016603 9288685 := bstep (se 3 (by rfl) ⟨1741628, by rfl⟩ : syracuseStep 9288685 = 3483257) B3483257
theorem B4406525 : Blo 1016603 4406525 := bstep (se 3 (by rfl) ⟨826223, by rfl⟩ : syracuseStep 4406525 = 1652447) B1652447
theorem B8699339 : Blo 1016603 8699339 := bstep (se 1 (by rfl) ⟨6524504, by rfl⟩ : syracuseStep 8699339 = 13049009) B13049009
theorem B5160671 : Blo 1016603 5160671 := bstep (se 1 (by rfl) ⟨3870503, by rfl⟩ : syracuseStep 5160671 = 7741007) B7741007
theorem B5226407 : Blo 1016603 5226407 := bstep (se 1 (by rfl) ⟨3919805, by rfl⟩ : syracuseStep 5226407 = 7839611) B7839611
theorem B1720615 : Blo 1016603 1720615 := bstep (se 1 (by rfl) ⟨1290461, by rfl⟩ : syracuseStep 1720615 = 2580923) B2580923
theorem B5882665 : Blo 1016603 5882665 := bstep (se 2 (by rfl) ⟨2205999, by rfl⟩ : syracuseStep 5882665 = 4411999) B4411999
theorem B1524959 : Blo 1016603 1524959 := bstep (se 1 (by rfl) ⟨1143719, by rfl⟩ : syracuseStep 1524959 = 2287439) B2287439
theorem B1721567 : Blo 1016603 1721567 := bstep (se 1 (by rfl) ⟨1291175, by rfl⟩ : syracuseStep 1721567 = 2582351) B2582351
theorem B1524971 : Blo 1016603 1524971 := bstep (se 1 (by rfl) ⟨1143728, by rfl⟩ : syracuseStep 1524971 = 2287457) B2287457
theorem B13059467 : Blo 1016603 13059467 := bstep (se 1 (by rfl) ⟨9794600, by rfl⟩ : syracuseStep 13059467 = 19589201) B19589201
theorem B4900283 : Blo 1016603 4900283 := bstep (se 1 (by rfl) ⟨3675212, by rfl⟩ : syracuseStep 4900283 = 7350425) B7350425
theorem B60311141 : Blo 1016603 60311141 := bstep (se 4 (by rfl) ⟨5654169, by rfl⟩ : syracuseStep 60311141 = 11308339) B11308339
theorem B1525355 : Blo 1016603 1525355 := bstep (se 1 (by rfl) ⟨1144016, by rfl⟩ : syracuseStep 1525355 = 2288033) B2288033
theorem B2442923 : Blo 1016603 2442923 := bstep (se 1 (by rfl) ⟨1832192, by rfl⟩ : syracuseStep 2442923 = 3664385) B3664385
theorem B1525439 : Blo 1016603 1525439 := bstep (se 1 (by rfl) ⟨1144079, by rfl⟩ : syracuseStep 1525439 = 2288159) B2288159
theorem B1525625 : Blo 1016603 1525625 := bstep (se 2 (by rfl) ⟨572109, by rfl⟩ : syracuseStep 1525625 = 1144219) B1144219
theorem B1657019 : Blo 1016603 1657019 := bstep (se 1 (by rfl) ⟨1242764, by rfl⟩ : syracuseStep 1657019 = 2485529) B2485529
theorem B5163425 : Blo 1016603 5163425 := bstep (se 2 (by rfl) ⟨1936284, by rfl⟩ : syracuseStep 5163425 = 3872569) B3872569
theorem B70666739 : Blo 1016603 70666739 := bstep (se 1 (by rfl) ⟨53000054, by rfl⟩ : syracuseStep 70666739 = 106000109) B106000109
theorem B2935399 : Blo 1016603 2935399 := bstep (se 1 (by rfl) ⟨2201549, by rfl⟩ : syracuseStep 2935399 = 4403099) B4403099
theorem B1526375 : Blo 1016603 1526375 := bstep (se 1 (by rfl) ⟨1144781, by rfl⟩ : syracuseStep 1526375 = 2289563) B2289563
theorem B1526567 : Blo 1016603 1526567 := bstep (se 1 (by rfl) ⟨1144925, by rfl⟩ : syracuseStep 1526567 = 2289851) B2289851
theorem B3263483 : Blo 1016603 3263483 := bstep (se 1 (by rfl) ⟨2447612, by rfl⟩ : syracuseStep 3263483 = 4895225) B4895225
theorem B2575415 : Blo 1016603 2575415 := bstep (se 1 (by rfl) ⟨1931561, by rfl⟩ : syracuseStep 2575415 = 3863123) B3863123
theorem B1526891 : Blo 1016603 1526891 := bstep (se 1 (by rfl) ⟨1145168, by rfl⟩ : syracuseStep 1526891 = 2290337) B2290337
theorem B1527131 : Blo 1016603 1527131 := bstep (se 1 (by rfl) ⟨1145348, by rfl⟩ : syracuseStep 1527131 = 2290697) B2290697
theorem B1527161 : Blo 1016603 1527161 := bstep (se 2 (by rfl) ⟨572685, by rfl⟩ : syracuseStep 1527161 = 1145371) B1145371
theorem B1527167 : Blo 1016603 1527167 := bstep (se 1 (by rfl) ⟨1145375, by rfl⟩ : syracuseStep 1527167 = 2290751) B2290751
theorem B1527791 : Blo 1016603 1527791 := bstep (se 1 (by rfl) ⟨1145843, by rfl⟩ : syracuseStep 1527791 = 2291687) B2291687
theorem B1527803 : Blo 1016603 1527803 := bstep (se 1 (by rfl) ⟨1145852, by rfl⟩ : syracuseStep 1527803 = 2291705) B2291705
theorem B1527863 : Blo 1016603 1527863 := bstep (se 1 (by rfl) ⟨1145897, by rfl⟩ : syracuseStep 1527863 = 2291795) B2291795
theorem B1527911 : Blo 1016603 1527911 := bstep (se 1 (by rfl) ⟨1145933, by rfl⟩ : syracuseStep 1527911 = 2291867) B2291867
theorem B4903067 : Blo 1016603 4903067 := bstep (se 1 (by rfl) ⟨3677300, by rfl⟩ : syracuseStep 4903067 = 7354601) B7354601
theorem B1527983 : Blo 1016603 1527983 := bstep (se 1 (by rfl) ⟨1145987, by rfl⟩ : syracuseStep 1527983 = 2291975) B2291975
theorem B1528187 : Blo 1016603 1528187 := bstep (se 1 (by rfl) ⟨1146140, by rfl⟩ : syracuseStep 1528187 = 2292281) B2292281
theorem B4346237 : Blo 1016603 4346237 := bstep (se 3 (by rfl) ⟨814919, by rfl⟩ : syracuseStep 4346237 = 1629839) B1629839
theorem B2576873 : Blo 1016603 2576873 := bstep (se 2 (by rfl) ⟨966327, by rfl⟩ : syracuseStep 2576873 = 1932655) B1932655
theorem B7721567 : Blo 1016603 7721567 := bstep (se 1 (by rfl) ⟨5791175, by rfl⟩ : syracuseStep 7721567 = 11582351) B11582351
theorem B1528457 : Blo 1016603 1528457 := bstep (se 2 (by rfl) ⟨573171, by rfl⟩ : syracuseStep 1528457 = 1146343) B1146343
theorem B15881021 : Blo 1016603 15881021 := bstep (se 3 (by rfl) ⟨2977691, by rfl⟩ : syracuseStep 15881021 = 5955383) B5955383
theorem B1528667 : Blo 1016603 1528667 := bstep (se 1 (by rfl) ⟨1146500, by rfl⟩ : syracuseStep 1528667 = 2293001) B2293001
theorem B1529129 : Blo 1016603 1529129 := bstep (se 2 (by rfl) ⟨573423, by rfl⟩ : syracuseStep 1529129 = 1146847) B1146847
theorem B1529327 : Blo 1016603 1529327 := bstep (se 1 (by rfl) ⟨1146995, by rfl⟩ : syracuseStep 1529327 = 2293991) B2293991
theorem B1529723 : Blo 1016603 1529723 := bstep (se 1 (by rfl) ⟨1147292, by rfl⟩ : syracuseStep 1529723 = 2294585) B2294585
theorem B1529759 : Blo 1016603 1529759 := bstep (se 1 (by rfl) ⟨1147319, by rfl⟩ : syracuseStep 1529759 = 2294639) B2294639
theorem B1529993 : Blo 1016603 1529993 := bstep (se 2 (by rfl) ⟨573747, by rfl⟩ : syracuseStep 1529993 = 1147495) B1147495
theorem B94197917 : Blo 1016603 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B1530143 : Blo 1016603 1530143 := bstep (se 1 (by rfl) ⟨1147607, by rfl⟩ : syracuseStep 1530143 = 2295215) B2295215
theorem B12376637 : Blo 1016603 12376637 := bstep (se 3 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 12376637 = 4641239) B4641239
theorem B1530695 : Blo 1016603 1530695 := bstep (se 1 (by rfl) ⟨1148021, by rfl⟩ : syracuseStep 1530695 = 2296043) B2296043
theorem B2579435 : Blo 1016603 2579435 := bstep (se 1 (by rfl) ⟨1934576, by rfl⟩ : syracuseStep 2579435 = 3869153) B3869153
theorem B5791085 : Blo 1016603 5791085 := bstep (se 3 (by rfl) ⟨1085828, by rfl⟩ : syracuseStep 5791085 = 2171657) B2171657
theorem B7724483 : Blo 1016603 7724483 := bstep (se 1 (by rfl) ⟨5793362, by rfl⟩ : syracuseStep 7724483 = 11586725) B11586725
theorem B6970835 : Blo 1016603 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B4349807 : Blo 1016603 4349807 := bstep (se 1 (by rfl) ⟨3262355, by rfl⟩ : syracuseStep 4349807 = 6524711) B6524711
theorem B3432347 : Blo 1016603 3432347 := bstep (se 1 (by rfl) ⟨2574260, by rfl⟩ : syracuseStep 3432347 = 5148521) B5148521
theorem B4351583 : Blo 1016603 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B5793727 : Blo 1016603 5793727 := bstep (se 1 (by rfl) ⟨4345295, by rfl⟩ : syracuseStep 5793727 = 8690591) B8690591
theorem B2287583 : Blo 1016603 2287583 := bstep (se 1 (by rfl) ⟨1715687, by rfl⟩ : syracuseStep 2287583 = 3431375) B3431375
theorem B13953053 : Blo 1016603 13953053 := bstep (se 3 (by rfl) ⟨2616197, by rfl⟩ : syracuseStep 13953053 = 5232395) B5232395
theorem B6973523 : Blo 1016603 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B5794001 : Blo 1016603 5794001 := bstep (se 2 (by rfl) ⟨2172750, by rfl⟩ : syracuseStep 5794001 = 4345501) B4345501
theorem B8808887 : Blo 1016603 8808887 := bstep (se 1 (by rfl) ⟨6606665, by rfl⟩ : syracuseStep 8808887 = 13213331) B13213331
theorem B107342779 : Blo 1016603 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B2288591 : Blo 1016603 2288591 := bstep (se 1 (by rfl) ⟨1716443, by rfl⟩ : syracuseStep 2288591 = 3432887) B3432887
theorem B2288681 : Blo 1016603 2288681 := bstep (se 2 (by rfl) ⟨858255, by rfl⟩ : syracuseStep 2288681 = 1716511) B1716511
theorem B10448041 : Blo 1016603 10448041 := bstep (se 2 (by rfl) ⟨3918015, by rfl⟩ : syracuseStep 10448041 = 7836031) B7836031
theorem B2288915 : Blo 1016603 2288915 := bstep (se 1 (by rfl) ⟨1716686, by rfl⟩ : syracuseStep 2288915 = 3433373) B3433373
theorem B2288951 : Blo 1016603 2288951 := bstep (se 1 (by rfl) ⟨1716713, by rfl⟩ : syracuseStep 2288951 = 3433427) B3433427
theorem B2125111 : Blo 1016603 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B2289545 : Blo 1016603 2289545 := bstep (se 2 (by rfl) ⟨858579, by rfl⟩ : syracuseStep 2289545 = 1717159) B1717159
theorem B2289761 : Blo 1016603 2289761 := bstep (se 2 (by rfl) ⟨858660, by rfl⟩ : syracuseStep 2289761 = 1717321) B1717321
theorem B2290427 : Blo 1016603 2290427 := bstep (se 1 (by rfl) ⟨1717820, by rfl⟩ : syracuseStep 2290427 = 3435641) B3435641
theorem B2290643 : Blo 1016603 2290643 := bstep (se 1 (by rfl) ⟨1717982, by rfl⟩ : syracuseStep 2290643 = 3435965) B3435965
theorem B7730315 : Blo 1016603 7730315 := bstep (se 1 (by rfl) ⟨5797736, by rfl⟩ : syracuseStep 7730315 = 11595473) B11595473
theorem B2291111 : Blo 1016603 2291111 := bstep (se 1 (by rfl) ⟨1718333, by rfl⟩ : syracuseStep 2291111 = 3436667) B3436667
theorem B6288835 : Blo 1016603 6288835 := bstep (se 1 (by rfl) ⟨4716626, by rfl⟩ : syracuseStep 6288835 = 9433253) B9433253
theorem B9663943 : Blo 1016603 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B2291219 : Blo 1016603 2291219 := bstep (se 1 (by rfl) ⟨1718414, by rfl⟩ : syracuseStep 2291219 = 3436829) B3436829
theorem B2291291 : Blo 1016603 2291291 := bstep (se 1 (by rfl) ⟨1718468, by rfl⟩ : syracuseStep 2291291 = 3436937) B3436937
theorem B3438233 : Blo 1016603 3438233 := bstep (se 2 (by rfl) ⟨1289337, by rfl⟩ : syracuseStep 3438233 = 2578675) B2578675
theorem B5797601 : Blo 1016603 5797601 := bstep (se 2 (by rfl) ⟨2174100, by rfl⟩ : syracuseStep 5797601 = 4348201) B4348201
theorem B1144903 : Blo 1016603 1144903 := bstep (se 1 (by rfl) ⟨858677, by rfl⟩ : syracuseStep 1144903 = 1717355) B1717355
theorem B1931455 : Blo 1016603 1931455 := bstep (se 1 (by rfl) ⟨1448591, by rfl⟩ : syracuseStep 1931455 = 2897183) B2897183
theorem B2291903 : Blo 1016603 2291903 := bstep (se 1 (by rfl) ⟨1718927, by rfl⟩ : syracuseStep 2291903 = 3437855) B3437855
theorem B13039987 : Blo 1016603 13039987 := bstep (se 1 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 13039987 = 19559981) B19559981
theorem B26442449 : Blo 1016603 26442449 := bstep (se 2 (by rfl) ⟨9915918, by rfl⟩ : syracuseStep 26442449 = 19831837) B19831837
theorem B13040351 : Blo 1016603 13040351 := bstep (se 1 (by rfl) ⟨9780263, by rfl⟩ : syracuseStep 13040351 = 19560527) B19560527
theorem B2325217 : Blo 1016603 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B1145767 : Blo 1016603 1145767 := bstep (se 1 (by rfl) ⟨859325, by rfl⟩ : syracuseStep 1145767 = 1718651) B1718651
theorem B1145947 : Blo 1016603 1145947 := bstep (se 1 (by rfl) ⟨859460, by rfl⟩ : syracuseStep 1145947 = 1718921) B1718921
theorem B1932511 : Blo 1016603 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B2293163 : Blo 1016603 2293163 := bstep (se 1 (by rfl) ⟨1719872, by rfl⟩ : syracuseStep 2293163 = 3439745) B3439745
theorem B2293199 : Blo 1016603 2293199 := bstep (se 1 (by rfl) ⟨1719899, by rfl⟩ : syracuseStep 2293199 = 3439799) B3439799
theorem B4357583 : Blo 1016603 4357583 := bstep (se 1 (by rfl) ⟨3268187, by rfl⟩ : syracuseStep 4357583 = 6536375) B6536375
theorem B3440123 : Blo 1016603 3440123 := bstep (se 1 (by rfl) ⟨2580092, by rfl⟩ : syracuseStep 3440123 = 5160185) B5160185
theorem B3440285 : Blo 1016603 3440285 := bstep (se 3 (by rfl) ⟨645053, by rfl⟩ : syracuseStep 3440285 = 1290107) B1290107
theorem B3440393 : Blo 1016603 3440393 := bstep (se 2 (by rfl) ⟨1290147, by rfl⟩ : syracuseStep 3440393 = 2580295) B2580295
theorem B3309455 : Blo 1016603 3309455 := bstep (se 1 (by rfl) ⟨2482091, by rfl⟩ : syracuseStep 3309455 = 4964183) B4964183
theorem B2293703 : Blo 1016603 2293703 := bstep (se 1 (by rfl) ⟨1720277, by rfl⟩ : syracuseStep 2293703 = 3440555) B3440555
theorem B2293883 : Blo 1016603 2293883 := bstep (se 1 (by rfl) ⟨1720412, by rfl⟩ : syracuseStep 2293883 = 3440825) B3440825
theorem B2294153 : Blo 1016603 2294153 := bstep (se 2 (by rfl) ⟨860307, by rfl⟩ : syracuseStep 2294153 = 1720615) B1720615
theorem B2294171 : Blo 1016603 2294171 := bstep (se 1 (by rfl) ⟨1720628, by rfl⟩ : syracuseStep 2294171 = 3441257) B3441257
theorem B1016639 : Blo 1016603 1016639 := bstep (se 1 (by rfl) ⟨762479, by rfl⟩ : syracuseStep 1016639 = 1524959) B1524959
theorem B1147711 : Blo 1016603 1147711 := bstep (se 1 (by rfl) ⟨860783, by rfl⟩ : syracuseStep 1147711 = 1721567) B1721567
theorem B1016647 : Blo 1016603 1016647 := bstep (se 1 (by rfl) ⟨762485, by rfl⟩ : syracuseStep 1016647 = 1524971) B1524971
theorem B40207427 : Blo 1016603 40207427 := bstep (se 1 (by rfl) ⟨30155570, by rfl⟩ : syracuseStep 40207427 = 60311141) B60311141
theorem B1016903 : Blo 1016603 1016903 := bstep (se 1 (by rfl) ⟨762677, by rfl⟩ : syracuseStep 1016903 = 1525355) B1525355
theorem B1016959 : Blo 1016603 1016959 := bstep (se 1 (by rfl) ⟨762719, by rfl⟩ : syracuseStep 1016959 = 1525439) B1525439
theorem B1017083 : Blo 1016603 1017083 := bstep (se 1 (by rfl) ⟨762812, by rfl⟩ : syracuseStep 1017083 = 1525625) B1525625
theorem B3867983 : Blo 1016603 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B4654415 : Blo 1016603 4654415 := bstep (se 1 (by rfl) ⟨3490811, by rfl⟩ : syracuseStep 4654415 = 6981623) B6981623
theorem B2295323 : Blo 1016603 2295323 := bstep (se 1 (by rfl) ⟨1721492, by rfl⟩ : syracuseStep 2295323 = 3442985) B3442985
theorem B4654655 : Blo 1016603 4654655 := bstep (se 1 (by rfl) ⟨3490991, by rfl⟩ : syracuseStep 4654655 = 6981983) B6981983
theorem B3442283 : Blo 1016603 3442283 := bstep (se 1 (by rfl) ⟨2581712, by rfl⟩ : syracuseStep 3442283 = 5163425) B5163425
theorem B1017583 : Blo 1016603 1017583 := bstep (se 1 (by rfl) ⟨763187, by rfl⟩ : syracuseStep 1017583 = 1526375) B1526375
theorem B1017711 : Blo 1016603 1017711 := bstep (se 1 (by rfl) ⟨763283, by rfl⟩ : syracuseStep 1017711 = 1526567) B1526567
theorem B1017927 : Blo 1016603 1017927 := bstep (se 1 (by rfl) ⟨763445, by rfl⟩ : syracuseStep 1017927 = 1526891) B1526891
theorem B17434763 : Blo 1016603 17434763 := bstep (se 1 (by rfl) ⟨13076072, by rfl⟩ : syracuseStep 17434763 = 26152145) B26152145
theorem B1018087 : Blo 1016603 1018087 := bstep (se 1 (by rfl) ⟨763565, by rfl⟩ : syracuseStep 1018087 = 1527131) B1527131
theorem B1018107 : Blo 1016603 1018107 := bstep (se 1 (by rfl) ⟨763580, by rfl⟩ : syracuseStep 1018107 = 1527161) B1527161
theorem B1018111 : Blo 1016603 1018111 := bstep (se 1 (by rfl) ⟨763583, by rfl⟩ : syracuseStep 1018111 = 1527167) B1527167
theorem B1018527 : Blo 1016603 1018527 := bstep (se 1 (by rfl) ⟨763895, by rfl⟩ : syracuseStep 1018527 = 1527791) B1527791
theorem B1018535 : Blo 1016603 1018535 := bstep (se 1 (by rfl) ⟨763901, by rfl⟩ : syracuseStep 1018535 = 1527803) B1527803
theorem B1018575 : Blo 1016603 1018575 := bstep (se 1 (by rfl) ⟨763931, by rfl⟩ : syracuseStep 1018575 = 1527863) B1527863
theorem B1018607 : Blo 1016603 1018607 := bstep (se 1 (by rfl) ⟨763955, by rfl⟩ : syracuseStep 1018607 = 1527911) B1527911
theorem B1018655 : Blo 1016603 1018655 := bstep (se 1 (by rfl) ⟨763991, by rfl⟩ : syracuseStep 1018655 = 1527983) B1527983
theorem B1018791 : Blo 1016603 1018791 := bstep (se 1 (by rfl) ⟨764093, by rfl⟩ : syracuseStep 1018791 = 1528187) B1528187
theorem B5147711 : Blo 1016603 5147711 := bstep (se 1 (by rfl) ⟨3860783, by rfl⟩ : syracuseStep 5147711 = 7721567) B7721567
theorem B1018971 : Blo 1016603 1018971 := bstep (se 1 (by rfl) ⟨764228, by rfl⟩ : syracuseStep 1018971 = 1528457) B1528457
theorem B10587347 : Blo 1016603 10587347 := bstep (se 1 (by rfl) ⟨7940510, by rfl⟩ : syracuseStep 10587347 = 15881021) B15881021
theorem B1838305 : Blo 1016603 1838305 := bstep (se 2 (by rfl) ⟨689364, by rfl⟩ : syracuseStep 1838305 = 1378729) B1378729
theorem B1019111 : Blo 1016603 1019111 := bstep (se 1 (by rfl) ⟨764333, by rfl⟩ : syracuseStep 1019111 = 1528667) B1528667
theorem B1019419 : Blo 1016603 1019419 := bstep (se 1 (by rfl) ⟨764564, by rfl⟩ : syracuseStep 1019419 = 1529129) B1529129
theorem B1019551 : Blo 1016603 1019551 := bstep (se 1 (by rfl) ⟨764663, by rfl⟩ : syracuseStep 1019551 = 1529327) B1529327
theorem B1019815 : Blo 1016603 1019815 := bstep (se 1 (by rfl) ⟨764861, by rfl⟩ : syracuseStep 1019815 = 1529723) B1529723
theorem B1019839 : Blo 1016603 1019839 := bstep (se 1 (by rfl) ⟨764879, by rfl⟩ : syracuseStep 1019839 = 1529759) B1529759
theorem B1019995 : Blo 1016603 1019995 := bstep (se 1 (by rfl) ⟨764996, by rfl⟩ : syracuseStep 1019995 = 1529993) B1529993
theorem B1020095 : Blo 1016603 1020095 := bstep (se 1 (by rfl) ⟨765071, by rfl⟩ : syracuseStep 1020095 = 1530143) B1530143
theorem B13930721 : Blo 1016603 13930721 := bstep (se 2 (by rfl) ⟨5224020, by rfl⟩ : syracuseStep 13930721 = 10448041) B10448041
theorem B11604221 : Blo 1016603 11604221 := bstep (se 3 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 11604221 = 4351583) B4351583
theorem B8262121 : Blo 1016603 8262121 := bstep (se 2 (by rfl) ⟨3098295, by rfl⟩ : syracuseStep 8262121 = 6196591) B6196591
theorem B1020463 : Blo 1016603 1020463 := bstep (se 1 (by rfl) ⟨765347, by rfl⟩ : syracuseStep 1020463 = 1530695) B1530695
theorem B5149655 : Blo 1016603 5149655 := bstep (se 1 (by rfl) ⟨3862241, by rfl⟩ : syracuseStep 5149655 = 7724483) B7724483
theorem B11016329 : Blo 1016603 11016329 := bstep (se 2 (by rfl) ⟨4131123, by rfl⟩ : syracuseStep 11016329 = 8262247) B8262247
theorem B1448489 : Blo 1016603 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B5872591 : Blo 1016603 5872591 := bstep (se 1 (by rfl) ⟨4404443, by rfl⟩ : syracuseStep 5872591 = 8808887) B8808887
theorem B12885257 : Blo 1016603 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B5217617 : Blo 1016603 5217617 := bstep (se 2 (by rfl) ⟨1956606, by rfl⟩ : syracuseStep 5217617 = 3913213) B3913213
theorem B5153543 : Blo 1016603 5153543 := bstep (se 1 (by rfl) ⟨3865157, by rfl⟩ : syracuseStep 5153543 = 7730315) B7730315
theorem B6530017 : Blo 1016603 6530017 := bstep (se 2 (by rfl) ⟨2448756, by rfl⟩ : syracuseStep 6530017 = 4897513) B4897513
theorem B8693567 : Blo 1016603 8693567 := bstep (se 1 (by rfl) ⟨6520175, by rfl⟩ : syracuseStep 8693567 = 13040351) B13040351
theorem B8825213 : Blo 1016603 8825213 := bstep (se 3 (by rfl) ⟨1654727, by rfl⟩ : syracuseStep 8825213 = 3309455) B3309455
theorem B3484271 : Blo 1016603 3484271 := bstep (se 1 (by rfl) ⟨2613203, by rfl⟩ : syracuseStep 3484271 = 5226407) B5226407
theorem B5156459 : Blo 1016603 5156459 := bstep (se 1 (by rfl) ⟨3867344, by rfl⟩ : syracuseStep 5156459 = 7734689) B7734689
theorem B26455747 : Blo 1016603 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B6532811 : Blo 1016603 6532811 := bstep (se 1 (by rfl) ⟨4899608, by rfl⟩ : syracuseStep 6532811 = 9799217) B9799217
theorem B7843553 : Blo 1016603 7843553 := bstep (se 2 (by rfl) ⟨2941332, by rfl⟩ : syracuseStep 7843553 = 5882665) B5882665
theorem B2896033 : Blo 1016603 2896033 := bstep (se 2 (by rfl) ⟨1086012, by rfl⟩ : syracuseStep 2896033 = 2172025) B2172025
theorem B5812499 : Blo 1016603 5812499 := bstep (se 1 (by rfl) ⟨4359374, by rfl⟩ : syracuseStep 5812499 = 8718749) B8718749
theorem B2175655 : Blo 1016603 2175655 := bstep (se 1 (by rfl) ⟨1631741, by rfl⟩ : syracuseStep 2175655 = 3263483) B3263483
theorem B1716943 : Blo 1016603 1716943 := bstep (se 1 (by rfl) ⟨1287707, by rfl⟩ : syracuseStep 1716943 = 2575415) B2575415
theorem B1717625 : Blo 1016603 1717625 := bstep (se 2 (by rfl) ⟨644109, by rfl⟩ : syracuseStep 1717625 = 1288219) B1288219
theorem B4896283 : Blo 1016603 4896283 := bstep (se 1 (by rfl) ⟨3672212, by rfl⟩ : syracuseStep 4896283 = 7344425) B7344425
theorem B2897491 : Blo 1016603 2897491 := bstep (se 1 (by rfl) ⟨2173118, by rfl⟩ : syracuseStep 2897491 = 4346237) B4346237
theorem B1717915 : Blo 1016603 1717915 := bstep (se 1 (by rfl) ⟨1288436, by rfl⟩ : syracuseStep 1717915 = 2576873) B2576873
theorem B8697563 : Blo 1016603 8697563 := bstep (se 1 (by rfl) ⟨6523172, by rfl⟩ : syracuseStep 8697563 = 13046345) B13046345
theorem B52869131 : Blo 1016603 52869131 := bstep (se 1 (by rfl) ⟨39651848, by rfl⟩ : syracuseStep 52869131 = 79303697) B79303697
theorem B3913865 : Blo 1016603 3913865 := bstep (se 2 (by rfl) ⟨1467699, by rfl⟩ : syracuseStep 3913865 = 2935399) B2935399
theorem B62798611 : Blo 1016603 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B2833481 : Blo 1016603 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B1719623 : Blo 1016603 1719623 := bstep (se 1 (by rfl) ⟨1289717, by rfl⟩ : syracuseStep 1719623 = 2579435) B2579435
theorem B2899871 : Blo 1016603 2899871 := bstep (se 1 (by rfl) ⟨2174903, by rfl⟩ : syracuseStep 2899871 = 4349807) B4349807
theorem B14860273 : Blo 1016603 14860273 := bstep (se 2 (by rfl) ⟨5572602, by rfl⟩ : syracuseStep 14860273 = 11145205) B11145205
theorem B4702531 : Blo 1016603 4702531 := bstep (se 1 (by rfl) ⟨3526898, by rfl⟩ : syracuseStep 4702531 = 7053797) B7053797
theorem B4899359 : Blo 1016603 4899359 := bstep (se 1 (by rfl) ⟨3674519, by rfl⟩ : syracuseStep 4899359 = 7349039) B7349039
theorem B1525055 : Blo 1016603 1525055 := bstep (se 1 (by rfl) ⟨1143791, by rfl⟩ : syracuseStep 1525055 = 2287583) B2287583
theorem B6440633 : Blo 1016603 6440633 := bstep (se 2 (by rfl) ⟨2415237, by rfl⟩ : syracuseStep 6440633 = 4830475) B4830475
theorem B6539039 : Blo 1016603 6539039 := bstep (se 1 (by rfl) ⟨4904279, by rfl⟩ : syracuseStep 6539039 = 9808559) B9808559
theorem B1525727 : Blo 1016603 1525727 := bstep (se 1 (by rfl) ⟨1144295, by rfl⟩ : syracuseStep 1525727 = 2288591) B2288591
theorem B1525787 : Blo 1016603 1525787 := bstep (se 1 (by rfl) ⟨1144340, by rfl⟩ : syracuseStep 1525787 = 2288681) B2288681
theorem B1525943 : Blo 1016603 1525943 := bstep (se 1 (by rfl) ⟨1144457, by rfl⟩ : syracuseStep 1525943 = 2288915) B2288915
theorem B1525967 : Blo 1016603 1525967 := bstep (se 1 (by rfl) ⟨1144475, by rfl⟩ : syracuseStep 1525967 = 2288951) B2288951
theorem B8702315 : Blo 1016603 8702315 := bstep (se 1 (by rfl) ⟨6526736, by rfl⟩ : syracuseStep 8702315 = 13053473) B13053473
theorem B4901417 : Blo 1016603 4901417 := bstep (se 2 (by rfl) ⟨1838031, by rfl⟩ : syracuseStep 4901417 = 3676063) B3676063
theorem B8243795 : Blo 1016603 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B1526363 : Blo 1016603 1526363 := bstep (se 1 (by rfl) ⟨1144772, by rfl⟩ : syracuseStep 1526363 = 2289545) B2289545
theorem B1526507 : Blo 1016603 1526507 := bstep (se 1 (by rfl) ⟨1144880, by rfl⟩ : syracuseStep 1526507 = 2289761) B2289761
theorem B1526537 : Blo 1016603 1526537 := bstep (se 2 (by rfl) ⟨572451, by rfl⟩ : syracuseStep 1526537 = 1144903) B1144903
theorem B2575273 : Blo 1016603 2575273 := bstep (se 2 (by rfl) ⟨965727, by rfl⟩ : syracuseStep 2575273 = 1931455) B1931455
theorem B5164073 : Blo 1016603 5164073 := bstep (se 2 (by rfl) ⟨1936527, by rfl⟩ : syracuseStep 5164073 = 3873055) B3873055
theorem B17386649 : Blo 1016603 17386649 := bstep (se 2 (by rfl) ⟨6519993, by rfl⟩ : syracuseStep 17386649 = 13039987) B13039987
theorem B1526951 : Blo 1016603 1526951 := bstep (se 1 (by rfl) ⟨1145213, by rfl⟩ : syracuseStep 1526951 = 2290427) B2290427
theorem B1527095 : Blo 1016603 1527095 := bstep (se 1 (by rfl) ⟨1145321, by rfl⟩ : syracuseStep 1527095 = 2290643) B2290643
theorem B1527407 : Blo 1016603 1527407 := bstep (se 1 (by rfl) ⟨1145555, by rfl⟩ : syracuseStep 1527407 = 2291111) B2291111
theorem B3100289 : Blo 1016603 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B1527479 : Blo 1016603 1527479 := bstep (se 1 (by rfl) ⟨1145609, by rfl⟩ : syracuseStep 1527479 = 2291219) B2291219
theorem B1527527 : Blo 1016603 1527527 := bstep (se 1 (by rfl) ⟨1145645, by rfl⟩ : syracuseStep 1527527 = 2291291) B2291291
theorem B1527689 : Blo 1016603 1527689 := bstep (se 2 (by rfl) ⟨572883, by rfl⟩ : syracuseStep 1527689 = 1145767) B1145767
theorem B1527929 : Blo 1016603 1527929 := bstep (se 2 (by rfl) ⟨572973, by rfl⟩ : syracuseStep 1527929 = 1145947) B1145947
theorem B1527935 : Blo 1016603 1527935 := bstep (se 1 (by rfl) ⟨1145951, by rfl⟩ : syracuseStep 1527935 = 2291903) B2291903
theorem B2576681 : Blo 1016603 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B2937683 : Blo 1016603 2937683 := bstep (se 1 (by rfl) ⟨2203262, by rfl⟩ : syracuseStep 2937683 = 4406525) B4406525
theorem B1528775 : Blo 1016603 1528775 := bstep (se 1 (by rfl) ⟨1146581, by rfl⟩ : syracuseStep 1528775 = 2293163) B2293163
theorem B1528799 : Blo 1016603 1528799 := bstep (se 1 (by rfl) ⟨1146599, by rfl⟩ : syracuseStep 1528799 = 2293199) B2293199
theorem B2905055 : Blo 1016603 2905055 := bstep (se 1 (by rfl) ⟨2178791, by rfl⟩ : syracuseStep 2905055 = 4357583) B4357583
theorem B1529135 : Blo 1016603 1529135 := bstep (se 1 (by rfl) ⟨1146851, by rfl⟩ : syracuseStep 1529135 = 2293703) B2293703
theorem B8705353 : Blo 1016603 8705353 := bstep (se 2 (by rfl) ⟨3264507, by rfl⟩ : syracuseStep 8705353 = 6529015) B6529015
theorem B1529339 : Blo 1016603 1529339 := bstep (se 1 (by rfl) ⟨1147004, by rfl⟩ : syracuseStep 1529339 = 2294009) B2294009
theorem B1529375 : Blo 1016603 1529375 := bstep (se 1 (by rfl) ⟨1147031, by rfl⟩ : syracuseStep 1529375 = 2294063) B2294063
theorem B4642409 : Blo 1016603 4642409 := bstep (se 2 (by rfl) ⟨1740903, by rfl⟩ : syracuseStep 4642409 = 3481807) B3481807
theorem B1529513 : Blo 1016603 1529513 := bstep (se 2 (by rfl) ⟨573567, by rfl⟩ : syracuseStep 1529513 = 1147135) B1147135
theorem B1529519 : Blo 1016603 1529519 := bstep (se 1 (by rfl) ⟨1147139, by rfl⟩ : syracuseStep 1529519 = 2294279) B2294279
theorem B10442459 : Blo 1016603 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B2578139 : Blo 1016603 2578139 := bstep (se 1 (by rfl) ⟨1933604, by rfl⟩ : syracuseStep 2578139 = 3867209) B3867209
theorem B1529639 : Blo 1016603 1529639 := bstep (se 1 (by rfl) ⟨1147229, by rfl⟩ : syracuseStep 1529639 = 2294459) B2294459
theorem B1529897 : Blo 1016603 1529897 := bstep (se 2 (by rfl) ⟨573711, by rfl⟩ : syracuseStep 1529897 = 1147423) B1147423
theorem B1529927 : Blo 1016603 1529927 := bstep (se 1 (by rfl) ⟨1147445, by rfl⟩ : syracuseStep 1529927 = 2294891) B2294891
theorem B8706311 : Blo 1016603 8706311 := bstep (se 1 (by rfl) ⟨6529733, by rfl⟩ : syracuseStep 8706311 = 13059467) B13059467
theorem B3266855 : Blo 1016603 3266855 := bstep (se 1 (by rfl) ⟨2450141, by rfl⟩ : syracuseStep 3266855 = 4900283) B4900283
theorem B1530239 : Blo 1016603 1530239 := bstep (se 1 (by rfl) ⟨1147679, by rfl⟩ : syracuseStep 1530239 = 2295359) B2295359
theorem B6183307 : Blo 1016603 6183307 := bstep (se 1 (by rfl) ⟨4637480, by rfl⟩ : syracuseStep 6183307 = 9274961) B9274961
theorem B1628615 : Blo 1016603 1628615 := bstep (se 1 (by rfl) ⟨1221461, by rfl⟩ : syracuseStep 1628615 = 2442923) B2442923
theorem B1530311 : Blo 1016603 1530311 := bstep (se 1 (by rfl) ⟨1147733, by rfl⟩ : syracuseStep 1530311 = 2295467) B2295467
theorem B1530527 : Blo 1016603 1530527 := bstep (se 1 (by rfl) ⟨1147895, by rfl⟩ : syracuseStep 1530527 = 2295791) B2295791
theorem B1104679 : Blo 1016603 1104679 := bstep (se 1 (by rfl) ⟨828509, by rfl⟩ : syracuseStep 1104679 = 1657019) B1657019
theorem B1530671 : Blo 1016603 1530671 := bstep (se 1 (by rfl) ⟨1148003, by rfl⟩ : syracuseStep 1530671 = 2296007) B2296007
theorem B2579303 : Blo 1016603 2579303 := bstep (se 1 (by rfl) ⟨1934477, by rfl⟩ : syracuseStep 2579303 = 3868955) B3868955
theorem B1530761 : Blo 1016603 1530761 := bstep (se 2 (by rfl) ⟨574035, by rfl⟩ : syracuseStep 1530761 = 1148071) B1148071
theorem B1530791 : Blo 1016603 1530791 := bstep (se 1 (by rfl) ⟨1148093, by rfl⟩ : syracuseStep 1530791 = 2296187) B2296187
theorem B47111159 : Blo 1016603 47111159 := bstep (se 1 (by rfl) ⟨35333369, by rfl⟩ : syracuseStep 47111159 = 70666739) B70666739
theorem B8707337 : Blo 1016603 8707337 := bstep (se 2 (by rfl) ⟨3265251, by rfl⟩ : syracuseStep 8707337 = 6530503) B6530503
theorem B19881409 : Blo 1016603 19881409 := bstep (se 2 (by rfl) ⟨7455528, by rfl⟩ : syracuseStep 19881409 = 14911057) B14911057
theorem B7724969 : Blo 1016603 7724969 := bstep (se 2 (by rfl) ⟨2896863, by rfl⟩ : syracuseStep 7724969 = 5793727) B5793727
theorem B2580457 : Blo 1016603 2580457 := bstep (se 2 (by rfl) ⟨967671, by rfl⟩ : syracuseStep 2580457 = 1935343) B1935343
theorem B3268711 : Blo 1016603 3268711 := bstep (se 1 (by rfl) ⟨2451533, by rfl⟩ : syracuseStep 3268711 = 4903067) B4903067
theorem B15687827 : Blo 1016603 15687827 := bstep (se 1 (by rfl) ⟨11765870, by rfl⟩ : syracuseStep 15687827 = 23531741) B23531741
theorem B9789605 : Blo 1016603 9789605 := bstep (se 4 (by rfl) ⟨917775, by rfl⟩ : syracuseStep 9789605 = 1835551) B1835551
theorem B5792543 : Blo 1016603 5792543 := bstep (se 1 (by rfl) ⟨4344407, by rfl⟩ : syracuseStep 5792543 = 8688815) B8688815
theorem B143123705 : Blo 1016603 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B2581915 : Blo 1016603 2581915 := bstep (se 1 (by rfl) ⟨1936436, by rfl⟩ : syracuseStep 2581915 = 3872873) B3872873
theorem B8251091 : Blo 1016603 8251091 := bstep (se 1 (by rfl) ⟨6188318, by rfl⟩ : syracuseStep 8251091 = 12376637) B12376637
theorem B2451323 : Blo 1016603 2451323 := bstep (se 1 (by rfl) ⟨1838492, by rfl⟩ : syracuseStep 2451323 = 3676985) B3676985
theorem B3860723 : Blo 1016603 3860723 := bstep (se 1 (by rfl) ⟨2895542, by rfl⟩ : syracuseStep 3860723 = 5791085) B5791085
theorem B4647223 : Blo 1016603 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B58812803 : Blo 1016603 58812803 := bstep (se 1 (by rfl) ⟨44109602, by rfl⟩ : syracuseStep 58812803 = 88219205) B88219205
theorem B3860905 : Blo 1016603 3860905 := bstep (se 2 (by rfl) ⟨1447839, by rfl⟩ : syracuseStep 3860905 = 2895679) B2895679
theorem B4418023 : Blo 1016603 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B2288231 : Blo 1016603 2288231 := bstep (se 1 (by rfl) ⟨1716173, by rfl⟩ : syracuseStep 2288231 = 3432347) B3432347
theorem B2583353 : Blo 1016603 2583353 := bstep (se 2 (by rfl) ⟨968757, by rfl⟩ : syracuseStep 2583353 = 1937515) B1937515
theorem B2976641 : Blo 1016603 2976641 := bstep (se 2 (by rfl) ⟨1116240, by rfl⟩ : syracuseStep 2976641 = 2232481) B2232481
theorem B2288609 : Blo 1016603 2288609 := bstep (se 2 (by rfl) ⟨858228, by rfl⟩ : syracuseStep 2288609 = 1716457) B1716457
theorem B3436343 : Blo 1016603 3436343 := bstep (se 1 (by rfl) ⟨2577257, by rfl⟩ : syracuseStep 3436343 = 5154515) B5154515
theorem B6516713 : Blo 1016603 6516713 := bstep (se 2 (by rfl) ⟨2443767, by rfl⟩ : syracuseStep 6516713 = 4887535) B4887535
theorem B9302035 : Blo 1016603 9302035 := bstep (se 1 (by rfl) ⟨6976526, by rfl⟩ : syracuseStep 9302035 = 13953053) B13953053
theorem B2387999 : Blo 1016603 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B4649015 : Blo 1016603 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B22605925 : Blo 1016603 22605925 := bstep (se 4 (by rfl) ⟨2119305, by rfl⟩ : syracuseStep 22605925 = 4238611) B4238611
theorem B3862667 : Blo 1016603 3862667 := bstep (se 1 (by rfl) ⟨2897000, by rfl⟩ : syracuseStep 3862667 = 5794001) B5794001
theorem B8385113 : Blo 1016603 8385113 := bstep (se 2 (by rfl) ⟨3144417, by rfl⟩ : syracuseStep 8385113 = 6288835) B6288835
theorem B1930081 : Blo 1016603 1930081 := bstep (se 2 (by rfl) ⟨723780, by rfl⟩ : syracuseStep 1930081 = 1447561) B1447561
theorem B3437423 : Blo 1016603 3437423 := bstep (se 1 (by rfl) ⟨2578067, by rfl⟩ : syracuseStep 3437423 = 5156135) B5156135
theorem B9794753 : Blo 1016603 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B44103041 : Blo 1016603 44103041 := bstep (se 2 (by rfl) ⟨16538640, by rfl⟩ : syracuseStep 44103041 = 33077281) B33077281
theorem B2291273 : Blo 1016603 2291273 := bstep (se 2 (by rfl) ⟨859227, by rfl⟩ : syracuseStep 2291273 = 1718455) B1718455
theorem B19593197 : Blo 1016603 19593197 := bstep (se 3 (by rfl) ⟨3673724, by rfl⟩ : syracuseStep 19593197 = 7347449) B7347449
theorem B3438827 : Blo 1016603 3438827 := bstep (se 1 (by rfl) ⟨2579120, by rfl⟩ : syracuseStep 3438827 = 5158241) B5158241
theorem B2292065 : Blo 1016603 2292065 := bstep (se 2 (by rfl) ⟨859524, by rfl⟩ : syracuseStep 2292065 = 1719049) B1719049
theorem B13400477 : Blo 1016603 13400477 := bstep (se 3 (by rfl) ⟨2512589, by rfl⟩ : syracuseStep 13400477 = 5025179) B5025179
theorem B2292155 : Blo 1016603 2292155 := bstep (se 1 (by rfl) ⟨1719116, by rfl⟩ : syracuseStep 2292155 = 3438233) B3438233
theorem B3865067 : Blo 1016603 3865067 := bstep (se 1 (by rfl) ⟨2898800, by rfl⟩ : syracuseStep 3865067 = 5797601) B5797601
theorem B12384913 : Blo 1016603 12384913 := bstep (se 2 (by rfl) ⟨4644342, by rfl⟩ : syracuseStep 12384913 = 9288685) B9288685
theorem B3439367 : Blo 1016603 3439367 := bstep (se 1 (by rfl) ⟨2579525, by rfl⟩ : syracuseStep 3439367 = 5159051) B5159051
theorem B17628299 : Blo 1016603 17628299 := bstep (se 1 (by rfl) ⟨13221224, by rfl⟩ : syracuseStep 17628299 = 26442449) B26442449
theorem B5799059 : Blo 1016603 5799059 := bstep (se 1 (by rfl) ⟨4349294, by rfl⟩ : syracuseStep 5799059 = 8698589) B8698589
theorem B20872363 : Blo 1016603 20872363 := bstep (se 1 (by rfl) ⟨15654272, by rfl⟩ : syracuseStep 20872363 = 31308545) B31308545
theorem B3866237 : Blo 1016603 3866237 := bstep (se 3 (by rfl) ⟨724919, by rfl⟩ : syracuseStep 3866237 = 1449839) B1449839
theorem B5799559 : Blo 1016603 5799559 := bstep (se 1 (by rfl) ⟨4349669, by rfl⟩ : syracuseStep 5799559 = 8699339) B8699339
theorem B2293415 : Blo 1016603 2293415 := bstep (se 1 (by rfl) ⟨1720061, by rfl⟩ : syracuseStep 2293415 = 3440123) B3440123
theorem B2293523 : Blo 1016603 2293523 := bstep (se 1 (by rfl) ⟨1720142, by rfl⟩ : syracuseStep 2293523 = 3440285) B3440285
theorem B3440447 : Blo 1016603 3440447 := bstep (se 1 (by rfl) ⟨2580335, by rfl⟩ : syracuseStep 3440447 = 5160671) B5160671
theorem B2293595 : Blo 1016603 2293595 := bstep (se 1 (by rfl) ⟨1720196, by rfl⟩ : syracuseStep 2293595 = 3440393) B3440393
theorem B4358281 : Blo 1016603 4358281 := bstep (se 2 (by rfl) ⟨1634355, by rfl⟩ : syracuseStep 4358281 = 3268711) B3268711
theorem B26804951 : Blo 1016603 26804951 := bstep (se 1 (by rfl) ⟨20103713, by rfl⟩ : syracuseStep 26804951 = 40207427) B40207427
theorem B1016703 : Blo 1016603 1016703 := bstep (se 1 (by rfl) ⟨762527, by rfl⟩ : syracuseStep 1016703 = 1525055) B1525055
theorem B2294855 : Blo 1016603 2294855 := bstep (se 1 (by rfl) ⟨1721141, by rfl⟩ : syracuseStep 2294855 = 3442283) B3442283
theorem B4293755 : Blo 1016603 4293755 := bstep (se 1 (by rfl) ⟨3220316, by rfl⟩ : syracuseStep 4293755 = 6440633) B6440633
theorem B4359359 : Blo 1016603 4359359 := bstep (se 1 (by rfl) ⟨3269519, by rfl⟩ : syracuseStep 4359359 = 6539039) B6539039
theorem B1017151 : Blo 1016603 1017151 := bstep (se 1 (by rfl) ⟨762863, by rfl⟩ : syracuseStep 1017151 = 1525727) B1525727
theorem B1017191 : Blo 1016603 1017191 := bstep (se 1 (by rfl) ⟨762893, by rfl⟩ : syracuseStep 1017191 = 1525787) B1525787
theorem B1017295 : Blo 1016603 1017295 := bstep (se 1 (by rfl) ⟨762971, by rfl⟩ : syracuseStep 1017295 = 1525943) B1525943
theorem B1017311 : Blo 1016603 1017311 := bstep (se 1 (by rfl) ⟨762983, by rfl⟩ : syracuseStep 1017311 = 1525967) B1525967
theorem B5801543 : Blo 1016603 5801543 := bstep (se 1 (by rfl) ⟨4351157, by rfl⟩ : syracuseStep 5801543 = 8702315) B8702315
theorem B1017575 : Blo 1016603 1017575 := bstep (se 1 (by rfl) ⟨763181, by rfl⟩ : syracuseStep 1017575 = 1526363) B1526363
theorem B1017671 : Blo 1016603 1017671 := bstep (se 1 (by rfl) ⟨763253, by rfl⟩ : syracuseStep 1017671 = 1526507) B1526507
theorem B1017691 : Blo 1016603 1017691 := bstep (se 1 (by rfl) ⟨763268, by rfl⟩ : syracuseStep 1017691 = 1526537) B1526537
theorem B3442553 : Blo 1016603 3442553 := bstep (se 2 (by rfl) ⟨1290957, by rfl⟩ : syracuseStep 3442553 = 2581915) B2581915
theorem B3442715 : Blo 1016603 3442715 := bstep (se 1 (by rfl) ⟨2582036, by rfl⟩ : syracuseStep 3442715 = 5164073) B5164073
theorem B1017967 : Blo 1016603 1017967 := bstep (se 1 (by rfl) ⟨763475, by rfl⟩ : syracuseStep 1017967 = 1526951) B1526951
theorem B1018063 : Blo 1016603 1018063 := bstep (se 1 (by rfl) ⟨763547, by rfl⟩ : syracuseStep 1018063 = 1527095) B1527095
theorem B1018271 : Blo 1016603 1018271 := bstep (se 1 (by rfl) ⟨763703, by rfl⟩ : syracuseStep 1018271 = 1527407) B1527407
theorem B1018319 : Blo 1016603 1018319 := bstep (se 1 (by rfl) ⟨763739, by rfl⟩ : syracuseStep 1018319 = 1527479) B1527479
theorem B1018351 : Blo 1016603 1018351 := bstep (se 1 (by rfl) ⟨763763, by rfl⟩ : syracuseStep 1018351 = 1527527) B1527527
theorem B1018459 : Blo 1016603 1018459 := bstep (se 1 (by rfl) ⟨763844, by rfl⟩ : syracuseStep 1018459 = 1527689) B1527689
theorem B1018619 : Blo 1016603 1018619 := bstep (se 1 (by rfl) ⟨763964, by rfl⟩ : syracuseStep 1018619 = 1527929) B1527929
theorem B1018623 : Blo 1016603 1018623 := bstep (se 1 (by rfl) ⟨763967, by rfl⟩ : syracuseStep 1018623 = 1527935) B1527935
theorem B7736147 : Blo 1016603 7736147 := bstep (se 1 (by rfl) ⟨5802110, by rfl⟩ : syracuseStep 7736147 = 11604221) B11604221
theorem B5147873 : Blo 1016603 5147873 := bstep (se 2 (by rfl) ⟨1930452, by rfl⟩ : syracuseStep 5147873 = 3860905) B3860905
theorem B1019183 : Blo 1016603 1019183 := bstep (se 1 (by rfl) ⟨764387, by rfl⟩ : syracuseStep 1019183 = 1528775) B1528775
theorem B1019199 : Blo 1016603 1019199 := bstep (se 1 (by rfl) ⟨764399, by rfl⟩ : syracuseStep 1019199 = 1528799) B1528799
theorem B1936703 : Blo 1016603 1936703 := bstep (se 1 (by rfl) ⟨1452527, by rfl⟩ : syracuseStep 1936703 = 2905055) B2905055
theorem B1019423 : Blo 1016603 1019423 := bstep (se 1 (by rfl) ⟨764567, by rfl⟩ : syracuseStep 1019423 = 1529135) B1529135
theorem B1019559 : Blo 1016603 1019559 := bstep (se 1 (by rfl) ⟨764669, by rfl⟩ : syracuseStep 1019559 = 1529339) B1529339
theorem B1019583 : Blo 1016603 1019583 := bstep (se 1 (by rfl) ⟨764687, by rfl⟩ : syracuseStep 1019583 = 1529375) B1529375
theorem B1019675 : Blo 1016603 1019675 := bstep (se 1 (by rfl) ⟨764756, by rfl⟩ : syracuseStep 1019675 = 1529513) B1529513
theorem B1019679 : Blo 1016603 1019679 := bstep (se 1 (by rfl) ⟨764759, by rfl⟩ : syracuseStep 1019679 = 1529519) B1529519
theorem B1019759 : Blo 1016603 1019759 := bstep (se 1 (by rfl) ⟨764819, by rfl⟩ : syracuseStep 1019759 = 1529639) B1529639
theorem B1019931 : Blo 1016603 1019931 := bstep (se 1 (by rfl) ⟨764948, by rfl⟩ : syracuseStep 1019931 = 1529897) B1529897
theorem B1019951 : Blo 1016603 1019951 := bstep (se 1 (by rfl) ⟨764963, by rfl⟩ : syracuseStep 1019951 = 1529927) B1529927
theorem B5804207 : Blo 1016603 5804207 := bstep (se 1 (by rfl) ⟨4353155, by rfl⟩ : syracuseStep 5804207 = 8706311) B8706311
theorem B1020159 : Blo 1016603 1020159 := bstep (se 1 (by rfl) ⟨765119, by rfl⟩ : syracuseStep 1020159 = 1530239) B1530239
theorem B1085743 : Blo 1016603 1085743 := bstep (se 1 (by rfl) ⟨814307, by rfl⟩ : syracuseStep 1085743 = 1628615) B1628615
theorem B1020207 : Blo 1016603 1020207 := bstep (se 1 (by rfl) ⟨765155, by rfl⟩ : syracuseStep 1020207 = 1530311) B1530311
theorem B1020351 : Blo 1016603 1020351 := bstep (se 1 (by rfl) ⟨765263, by rfl⟩ : syracuseStep 1020351 = 1530527) B1530527
theorem B1020447 : Blo 1016603 1020447 := bstep (se 1 (by rfl) ⟨765335, by rfl⟩ : syracuseStep 1020447 = 1530671) B1530671
theorem B1020507 : Blo 1016603 1020507 := bstep (se 1 (by rfl) ⟨765380, by rfl⟩ : syracuseStep 1020507 = 1530761) B1530761
theorem B1020527 : Blo 1016603 1020527 := bstep (se 1 (by rfl) ⟨765395, by rfl⟩ : syracuseStep 1020527 = 1530791) B1530791
theorem B8590171 : Blo 1016603 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B5804891 : Blo 1016603 5804891 := bstep (se 1 (by rfl) ⟨4353668, by rfl⟩ : syracuseStep 5804891 = 8707337) B8707337
theorem B3478411 : Blo 1016603 3478411 := bstep (se 1 (by rfl) ⟨2608808, by rfl⟩ : syracuseStep 3478411 = 5217617) B5217617
theorem B5149979 : Blo 1016603 5149979 := bstep (se 1 (by rfl) ⟨3862484, by rfl⟩ : syracuseStep 5149979 = 7724969) B7724969
theorem B10458551 : Blo 1016603 10458551 := bstep (se 1 (by rfl) ⟨7843913, by rfl⟩ : syracuseStep 10458551 = 15687827) B15687827
theorem B6526403 : Blo 1016603 6526403 := bstep (se 1 (by rfl) ⟨4894802, by rfl⟩ : syracuseStep 6526403 = 9789605) B9789605
theorem B11016161 : Blo 1016603 11016161 := bstep (se 2 (by rfl) ⟨4131060, by rfl⟩ : syracuseStep 11016161 = 8262121) B8262121
theorem B11607137 : Blo 1016603 11607137 := bstep (se 2 (by rfl) ⟨4352676, by rfl⟩ : syracuseStep 11607137 = 8705353) B8705353
theorem B6528377 : Blo 1016603 6528377 := bstep (se 2 (by rfl) ⟨2448141, by rfl⟩ : syracuseStep 6528377 = 4896283) B4896283
theorem B3874999 : Blo 1016603 3874999 := bstep (se 1 (by rfl) ⟨2906249, by rfl⟩ : syracuseStep 3874999 = 5812499) B5812499
theorem B6529835 : Blo 1016603 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B29402027 : Blo 1016603 29402027 := bstep (se 1 (by rfl) ⟨22051520, by rfl⟩ : syracuseStep 29402027 = 44103041) B44103041
theorem B83731481 : Blo 1016603 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B27829817 : Blo 1016603 27829817 := bstep (se 2 (by rfl) ⟨10436181, by rfl⟩ : syracuseStep 27829817 = 20872363) B20872363
theorem B8267437 : Blo 1016603 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B17377901 : Blo 1016603 17377901 := bstep (se 3 (by rfl) ⟨3258356, by rfl⟩ : syracuseStep 17377901 = 6516713) B6516713
theorem B6367997 : Blo 1016603 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B12397373 : Blo 1016603 12397373 := bstep (se 3 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 12397373 = 4649015) B4649015
theorem B6270041 : Blo 1016603 6270041 := bstep (se 2 (by rfl) ⟨2351265, by rfl⟩ : syracuseStep 6270041 = 4702531) B4702531
theorem B24785189 : Blo 1016603 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B32977637 : Blo 1016603 32977637 := bstep (se 4 (by rfl) ⟨3091653, by rfl⟩ : syracuseStep 32977637 = 6183307) B6183307
theorem B7058231 : Blo 1016603 7058231 := bstep (se 1 (by rfl) ⟨5293673, by rfl⟩ : syracuseStep 7058231 = 10587347) B10587347
theorem B9287147 : Blo 1016603 9287147 := bstep (se 1 (by rfl) ⟨6965360, by rfl⟩ : syracuseStep 9287147 = 13930721) B13930721
theorem B1717787 : Blo 1016603 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B3094939 : Blo 1016603 3094939 := bstep (se 1 (by rfl) ⟨2321204, by rfl⟩ : syracuseStep 3094939 = 4642409) B4642409
theorem B6961639 : Blo 1016603 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B1718759 : Blo 1016603 1718759 := bstep (se 1 (by rfl) ⟨1289069, by rfl⟩ : syracuseStep 1718759 = 2578139) B2578139
theorem B2177903 : Blo 1016603 2177903 := bstep (se 1 (by rfl) ⟨1633427, by rfl⟩ : syracuseStep 2177903 = 3266855) B3266855
theorem B1719535 : Blo 1016603 1719535 := bstep (se 1 (by rfl) ⟨1289651, by rfl⟩ : syracuseStep 1719535 = 2579303) B2579303
theorem B31407439 : Blo 1016603 31407439 := bstep (se 1 (by rfl) ⟨23555579, by rfl⟩ : syracuseStep 31407439 = 47111159) B47111159
theorem B35274329 : Blo 1016603 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B6536861 : Blo 1016603 6536861 := bstep (se 3 (by rfl) ⟨1225661, by rfl⟩ : syracuseStep 6536861 = 2451323) B2451323
theorem B12402713 : Blo 1016603 12402713 := bstep (se 2 (by rfl) ⟨4651017, by rfl⟩ : syracuseStep 12402713 = 9302035) B9302035
theorem B29376877 : Blo 1016603 29376877 := bstep (se 3 (by rfl) ⟨5508164, by rfl⟩ : syracuseStep 29376877 = 11016329) B11016329
theorem B2900873 : Blo 1016603 2900873 := bstep (se 2 (by rfl) ⟨1087827, by rfl⟩ : syracuseStep 2900873 = 2175655) B2175655
theorem B2573441 : Blo 1016603 2573441 := bstep (se 2 (by rfl) ⟨965040, by rfl⟩ : syracuseStep 2573441 = 1930081) B1930081
theorem B2573815 : Blo 1016603 2573815 := bstep (se 1 (by rfl) ⟨1930361, by rfl⟩ : syracuseStep 2573815 = 3860723) B3860723
theorem B5883475 : Blo 1016603 5883475 := bstep (se 1 (by rfl) ⟨4412606, by rfl⟩ : syracuseStep 5883475 = 8825213) B8825213
theorem B39208535 : Blo 1016603 39208535 := bstep (se 1 (by rfl) ⟨29406401, by rfl⟩ : syracuseStep 39208535 = 58812803) B58812803
theorem B1525487 : Blo 1016603 1525487 := bstep (se 1 (by rfl) ⟨1144115, by rfl⟩ : syracuseStep 1525487 = 2288231) B2288231
theorem B1722235 : Blo 1016603 1722235 := bstep (se 1 (by rfl) ⟨1291676, by rfl⟩ : syracuseStep 1722235 = 2583353) B2583353
theorem B1984427 : Blo 1016603 1984427 := bstep (se 1 (by rfl) ⟨1488320, by rfl⟩ : syracuseStep 1984427 = 2976641) B2976641
theorem B1525739 : Blo 1016603 1525739 := bstep (se 1 (by rfl) ⟨1144304, by rfl⟩ : syracuseStep 1525739 = 2288609) B2288609
theorem B5229035 : Blo 1016603 5229035 := bstep (se 1 (by rfl) ⟨3921776, by rfl⟩ : syracuseStep 5229035 = 7843553) B7843553
theorem B2575111 : Blo 1016603 2575111 := bstep (se 1 (by rfl) ⟨1931333, by rfl⟩ : syracuseStep 2575111 = 3862667) B3862667
theorem B7555949 : Blo 1016603 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B5590075 : Blo 1016603 5590075 := bstep (se 1 (by rfl) ⟨4192556, by rfl⟩ : syracuseStep 5590075 = 8385113) B8385113
theorem B1527515 : Blo 1016603 1527515 := bstep (se 1 (by rfl) ⟨1145636, by rfl⟩ : syracuseStep 1527515 = 2291273) B2291273
theorem B13062131 : Blo 1016603 13062131 := bstep (se 1 (by rfl) ⟨9796598, by rfl⟩ : syracuseStep 13062131 = 19593197) B19593197
theorem B35246087 : Blo 1016603 35246087 := bstep (se 1 (by rfl) ⟨26434565, by rfl⟩ : syracuseStep 35246087 = 52869131) B52869131
theorem B2609243 : Blo 1016603 2609243 := bstep (se 1 (by rfl) ⟨1956932, by rfl⟩ : syracuseStep 2609243 = 3913865) B3913865
theorem B1528043 : Blo 1016603 1528043 := bstep (se 1 (by rfl) ⟨1146032, by rfl⟩ : syracuseStep 1528043 = 2292065) B2292065
theorem B8933651 : Blo 1016603 8933651 := bstep (se 1 (by rfl) ⟨6700238, by rfl⟩ : syracuseStep 8933651 = 13400477) B13400477
theorem B1528103 : Blo 1016603 1528103 := bstep (se 1 (by rfl) ⟨1146077, by rfl⟩ : syracuseStep 1528103 = 2292155) B2292155
theorem B2576711 : Blo 1016603 2576711 := bstep (se 1 (by rfl) ⟨1932533, by rfl⟩ : syracuseStep 2576711 = 3865067) B3865067
theorem B11752199 : Blo 1016603 11752199 := bstep (se 1 (by rfl) ⟨8814149, by rfl⟩ : syracuseStep 11752199 = 17628299) B17628299
theorem B2577491 : Blo 1016603 2577491 := bstep (se 1 (by rfl) ⟨1933118, by rfl⟩ : syracuseStep 2577491 = 3866237) B3866237
theorem B1528943 : Blo 1016603 1528943 := bstep (se 1 (by rfl) ⟨1146707, by rfl⟩ : syracuseStep 1528943 = 2293415) B2293415
theorem B1529015 : Blo 1016603 1529015 := bstep (se 1 (by rfl) ⟨1146761, by rfl⟩ : syracuseStep 1529015 = 2293523) B2293523
theorem B1529063 : Blo 1016603 1529063 := bstep (se 1 (by rfl) ⟨1146797, by rfl⟩ : syracuseStep 1529063 = 2293595) B2293595
theorem B19813697 : Blo 1016603 19813697 := bstep (se 2 (by rfl) ⟨7430136, by rfl⟩ : syracuseStep 19813697 = 14860273) B14860273
theorem B1529255 : Blo 1016603 1529255 := bstep (se 1 (by rfl) ⟨1146941, by rfl⟩ : syracuseStep 1529255 = 2293883) B2293883
theorem B1529435 : Blo 1016603 1529435 := bstep (se 1 (by rfl) ⟨1147076, by rfl⟩ : syracuseStep 1529435 = 2294153) B2294153
theorem B1529447 : Blo 1016603 1529447 := bstep (se 1 (by rfl) ⟨1147085, by rfl⟩ : syracuseStep 1529447 = 2294171) B2294171
theorem B3266239 : Blo 1016603 3266239 := bstep (se 1 (by rfl) ⟨2449679, by rfl⟩ : syracuseStep 3266239 = 4899359) B4899359
theorem B2578655 : Blo 1016603 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B3102943 : Blo 1016603 3102943 := bstep (se 1 (by rfl) ⟨2327207, by rfl⟩ : syracuseStep 3102943 = 4654415) B4654415
theorem B1530215 : Blo 1016603 1530215 := bstep (se 1 (by rfl) ⟨1147661, by rfl⟩ : syracuseStep 1530215 = 2295323) B2295323
theorem B3103103 : Blo 1016603 3103103 := bstep (se 1 (by rfl) ⟨2327327, by rfl⟩ : syracuseStep 3103103 = 4654655) B4654655
theorem B1530281 : Blo 1016603 1530281 := bstep (se 2 (by rfl) ⟨573855, by rfl⟩ : syracuseStep 1530281 = 1147711) B1147711
theorem B8706689 : Blo 1016603 8706689 := bstep (se 2 (by rfl) ⟨3265008, by rfl⟩ : syracuseStep 8706689 = 6530017) B6530017
theorem B11623175 : Blo 1016603 11623175 := bstep (se 1 (by rfl) ⟨8717381, by rfl⟩ : syracuseStep 11623175 = 17434763) B17434763
theorem B3267611 : Blo 1016603 3267611 := bstep (se 1 (by rfl) ⟨2450708, by rfl⟩ : syracuseStep 3267611 = 4901417) B4901417
theorem B5495863 : Blo 1016603 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B3431807 : Blo 1016603 3431807 := bstep (se 1 (by rfl) ⟨2573855, by rfl⟩ : syracuseStep 3431807 = 5147711) B5147711
theorem B11591099 : Blo 1016603 11591099 := bstep (se 1 (by rfl) ⟨8693324, by rfl⟩ : syracuseStep 11591099 = 17386649) B17386649
theorem B1958455 : Blo 1016603 1958455 := bstep (se 1 (by rfl) ⟨1468841, by rfl⟩ : syracuseStep 1958455 = 2937683) B2937683
theorem B5890697 : Blo 1016603 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B3433103 : Blo 1016603 3433103 := bstep (se 1 (by rfl) ⟨2574827, by rfl⟩ : syracuseStep 3433103 = 5149655) B5149655
theorem B3433697 : Blo 1016603 3433697 := bstep (se 2 (by rfl) ⟨1287636, by rfl⟩ : syracuseStep 3433697 = 2575273) B2575273
theorem B2451073 : Blo 1016603 2451073 := bstep (se 2 (by rfl) ⟨919152, by rfl⟩ : syracuseStep 2451073 = 1838305) B1838305
theorem B30141233 : Blo 1016603 30141233 := bstep (se 2 (by rfl) ⟨11302962, by rfl⟩ : syracuseStep 30141233 = 22605925) B22605925
theorem B3861377 : Blo 1016603 3861377 := bstep (se 2 (by rfl) ⟨1448016, by rfl⟩ : syracuseStep 3861377 = 2896033) B2896033
theorem B3435695 : Blo 1016603 3435695 := bstep (se 1 (by rfl) ⟨2576771, by rfl⟩ : syracuseStep 3435695 = 5153543) B5153543
theorem B3861695 : Blo 1016603 3861695 := bstep (se 1 (by rfl) ⟨2896271, by rfl⟩ : syracuseStep 3861695 = 5792543) B5792543
theorem B95415803 : Blo 1016603 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B2289257 : Blo 1016603 2289257 := bstep (se 2 (by rfl) ⟨858471, by rfl⟩ : syracuseStep 2289257 = 1716943) B1716943
theorem B5500727 : Blo 1016603 5500727 := bstep (se 1 (by rfl) ⟨4125545, by rfl⟩ : syracuseStep 5500727 = 8251091) B8251091
theorem B5795711 : Blo 1016603 5795711 := bstep (se 1 (by rfl) ⟨4346783, by rfl⟩ : syracuseStep 5795711 = 8693567) B8693567
theorem B3862637 : Blo 1016603 3862637 := bstep (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) B1448489
theorem B2322847 : Blo 1016603 2322847 := bstep (se 1 (by rfl) ⟨1742135, by rfl⟩ : syracuseStep 2322847 = 3484271) B3484271
theorem B3863321 : Blo 1016603 3863321 := bstep (se 2 (by rfl) ⟨1448745, by rfl⟩ : syracuseStep 3863321 = 2897491) B2897491
theorem B2290553 : Blo 1016603 2290553 := bstep (se 2 (by rfl) ⟨858957, by rfl⟩ : syracuseStep 2290553 = 1717915) B1717915
theorem B3437639 : Blo 1016603 3437639 := bstep (se 1 (by rfl) ⟨2578229, by rfl⟩ : syracuseStep 3437639 = 5156459) B5156459
theorem B4355207 : Blo 1016603 4355207 := bstep (se 1 (by rfl) ⟨3266405, by rfl⟩ : syracuseStep 4355207 = 6532811) B6532811
theorem B2290895 : Blo 1016603 2290895 := bstep (se 1 (by rfl) ⟨1718171, by rfl⟩ : syracuseStep 2290895 = 3436343) B3436343
theorem B2291615 : Blo 1016603 2291615 := bstep (se 1 (by rfl) ⟨1718711, by rfl⟩ : syracuseStep 2291615 = 3437423) B3437423
theorem B16513217 : Blo 1016603 16513217 := bstep (se 2 (by rfl) ⟨6192456, by rfl⟩ : syracuseStep 16513217 = 12384913) B12384913
theorem B1145083 : Blo 1016603 1145083 := bstep (se 1 (by rfl) ⟨858812, by rfl⟩ : syracuseStep 1145083 = 1717625) B1717625
theorem B1472905 : Blo 1016603 1472905 := bstep (se 2 (by rfl) ⟨552339, by rfl⟩ : syracuseStep 1472905 = 1104679) B1104679
theorem B5798375 : Blo 1016603 5798375 := bstep (se 1 (by rfl) ⟨4348781, by rfl⟩ : syracuseStep 5798375 = 8697563) B8697563
theorem B7830121 : Blo 1016603 7830121 := bstep (se 2 (by rfl) ⟨2936295, by rfl⟩ : syracuseStep 7830121 = 5872591) B5872591
theorem B2292551 : Blo 1016603 2292551 := bstep (se 1 (by rfl) ⟨1719413, by rfl⟩ : syracuseStep 2292551 = 3438827) B3438827
theorem B2292911 : Blo 1016603 2292911 := bstep (se 1 (by rfl) ⟨1719683, by rfl⟩ : syracuseStep 2292911 = 3439367) B3439367
theorem B26508545 : Blo 1016603 26508545 := bstep (se 2 (by rfl) ⟨9940704, by rfl⟩ : syracuseStep 26508545 = 19881409) B19881409
theorem B3866039 : Blo 1016603 3866039 := bstep (se 1 (by rfl) ⟨2899529, by rfl⟩ : syracuseStep 3866039 = 5799059) B5799059
theorem B7732745 : Blo 1016603 7732745 := bstep (se 2 (by rfl) ⟨2899779, by rfl⟩ : syracuseStep 7732745 = 5799559) B5799559
theorem B1146415 : Blo 1016603 1146415 := bstep (se 1 (by rfl) ⟨859811, by rfl⟩ : syracuseStep 1146415 = 1719623) B1719623
theorem B2293631 : Blo 1016603 2293631 := bstep (se 1 (by rfl) ⟨1720223, by rfl⟩ : syracuseStep 2293631 = 3440447) B3440447
theorem B1933247 : Blo 1016603 1933247 := bstep (se 1 (by rfl) ⟨1449935, by rfl⟩ : syracuseStep 1933247 = 2899871) B2899871
theorem B3440609 : Blo 1016603 3440609 := bstep (se 2 (by rfl) ⟨1290228, by rfl⟩ : syracuseStep 3440609 = 2580457) B2580457
theorem B3867695 : Blo 1016603 3867695 := bstep (se 1 (by rfl) ⟨2900771, by rfl⟩ : syracuseStep 3867695 = 5801543) B5801543
theorem B1016991 : Blo 1016603 1016991 := bstep (se 1 (by rfl) ⟨762743, by rfl⟩ : syracuseStep 1016991 = 1525487) B1525487
theorem B2295035 : Blo 1016603 2295035 := bstep (se 1 (by rfl) ⟨1721276, by rfl⟩ : syracuseStep 2295035 = 3442553) B3442553
theorem B1017159 : Blo 1016603 1017159 := bstep (se 1 (by rfl) ⟨762869, by rfl⟩ : syracuseStep 1017159 = 1525739) B1525739
theorem B2295143 : Blo 1016603 2295143 := bstep (se 1 (by rfl) ⟨1721357, by rfl⟩ : syracuseStep 2295143 = 3442715) B3442715
theorem B7735661 : Blo 1016603 7735661 := bstep (se 3 (by rfl) ⟨1450436, by rfl⟩ : syracuseStep 7735661 = 2900873) B2900873
theorem B1018343 : Blo 1016603 1018343 := bstep (se 1 (by rfl) ⟨763757, by rfl⟩ : syracuseStep 1018343 = 1527515) B1527515
theorem B2296313 : Blo 1016603 2296313 := bstep (se 2 (by rfl) ⟨861117, by rfl⟩ : syracuseStep 2296313 = 1722235) B1722235
theorem B23497391 : Blo 1016603 23497391 := bstep (se 1 (by rfl) ⟨17623043, by rfl⟩ : syracuseStep 23497391 = 35246087) B35246087
theorem B1739495 : Blo 1016603 1739495 := bstep (se 1 (by rfl) ⟨1304621, by rfl⟩ : syracuseStep 1739495 = 2609243) B2609243
theorem B3869471 : Blo 1016603 3869471 := bstep (se 1 (by rfl) ⟨2902103, by rfl⟩ : syracuseStep 3869471 = 5804207) B5804207
theorem B1018695 : Blo 1016603 1018695 := bstep (se 1 (by rfl) ⟨764021, by rfl⟩ : syracuseStep 1018695 = 1528043) B1528043
theorem B1018735 : Blo 1016603 1018735 := bstep (se 1 (by rfl) ⟨764051, by rfl⟩ : syracuseStep 1018735 = 1528103) B1528103
theorem B7834799 : Blo 1016603 7834799 := bstep (se 1 (by rfl) ⟨5876099, by rfl⟩ : syracuseStep 7834799 = 11752199) B11752199
theorem B3869927 : Blo 1016603 3869927 := bstep (se 1 (by rfl) ⟨2902445, by rfl⟩ : syracuseStep 3869927 = 5804891) B5804891
theorem B1019295 : Blo 1016603 1019295 := bstep (se 1 (by rfl) ⟨764471, by rfl⟩ : syracuseStep 1019295 = 1528943) B1528943
theorem B1019343 : Blo 1016603 1019343 := bstep (se 1 (by rfl) ⟨764507, by rfl⟩ : syracuseStep 1019343 = 1529015) B1529015
theorem B1019375 : Blo 1016603 1019375 := bstep (se 1 (by rfl) ⟨764531, by rfl⟩ : syracuseStep 1019375 = 1529063) B1529063
theorem B13209131 : Blo 1016603 13209131 := bstep (se 1 (by rfl) ⟨9906848, by rfl⟩ : syracuseStep 13209131 = 19813697) B19813697
theorem B1019503 : Blo 1016603 1019503 := bstep (se 1 (by rfl) ⟨764627, by rfl⟩ : syracuseStep 1019503 = 1529255) B1529255
theorem B1019623 : Blo 1016603 1019623 := bstep (se 1 (by rfl) ⟨764717, by rfl⟩ : syracuseStep 1019623 = 1529435) B1529435
theorem B1019631 : Blo 1016603 1019631 := bstep (se 1 (by rfl) ⟨764723, by rfl⟩ : syracuseStep 1019631 = 1529447) B1529447
theorem B7344107 : Blo 1016603 7344107 := bstep (se 1 (by rfl) ⟨5508080, by rfl⟩ : syracuseStep 7344107 = 11016161) B11016161
theorem B1020143 : Blo 1016603 1020143 := bstep (se 1 (by rfl) ⟨765107, by rfl⟩ : syracuseStep 1020143 = 1530215) B1530215
theorem B2068735 : Blo 1016603 2068735 := bstep (se 1 (by rfl) ⟨1551551, by rfl⟩ : syracuseStep 2068735 = 3103103) B3103103
theorem B1020187 : Blo 1016603 1020187 := bstep (se 1 (by rfl) ⟨765140, by rfl⟩ : syracuseStep 1020187 = 1530281) B1530281
theorem B5804459 : Blo 1016603 5804459 := bstep (se 1 (by rfl) ⟨4353344, by rfl⟩ : syracuseStep 5804459 = 8706689) B8706689
theorem B7738091 : Blo 1016603 7738091 := bstep (se 1 (by rfl) ⟨5803568, by rfl⟩ : syracuseStep 7738091 = 11607137) B11607137
theorem B19601351 : Blo 1016603 19601351 := bstep (se 1 (by rfl) ⟨14701013, by rfl⟩ : syracuseStep 19601351 = 29402027) B29402027
theorem B18553211 : Blo 1016603 18553211 := bstep (se 1 (by rfl) ⟨13914908, by rfl⟩ : syracuseStep 18553211 = 27829817) B27829817
theorem B20094155 : Blo 1016603 20094155 := bstep (se 1 (by rfl) ⟨15070616, by rfl⟩ : syracuseStep 20094155 = 30141233) B30141233
theorem B8264915 : Blo 1016603 8264915 := bstep (se 1 (by rfl) ⟨6198686, by rfl⟩ : syracuseStep 8264915 = 12397373) B12397373
theorem B16981325 : Blo 1016603 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B63610535 : Blo 1016603 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B16523459 : Blo 1016603 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B4137257 : Blo 1016603 4137257 := bstep (se 2 (by rfl) ⟨1551471, by rfl⟩ : syracuseStep 4137257 = 3102943) B3102943
theorem B9282185 : Blo 1016603 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B1451935 : Blo 1016603 1451935 := bstep (se 1 (by rfl) ⟨1088951, by rfl⟩ : syracuseStep 1451935 = 2177903) B2177903
theorem B17672363 : Blo 1016603 17672363 := bstep (se 1 (by rfl) ⟨13254272, by rfl⟩ : syracuseStep 17672363 = 26508545) B26508545
theorem B5155163 : Blo 1016603 5155163 := bstep (se 1 (by rfl) ⟨3866372, by rfl⟩ : syracuseStep 5155163 = 7732745) B7732745
theorem B5155325 : Blo 1016603 5155325 := bstep (se 3 (by rfl) ⟨966623, by rfl⟩ : syracuseStep 5155325 = 1933247) B1933247
theorem B8268475 : Blo 1016603 8268475 := bstep (se 1 (by rfl) ⟨6201356, by rfl⟩ : syracuseStep 8268475 = 12402713) B12402713
theorem B5811041 : Blo 1016603 5811041 := bstep (se 2 (by rfl) ⟨2179140, by rfl⟩ : syracuseStep 5811041 = 4358281) B4358281
theorem B17869967 : Blo 1016603 17869967 := bstep (se 1 (by rfl) ⟨13402475, by rfl⟩ : syracuseStep 17869967 = 26804951) B26804951
theorem B39169169 : Blo 1016603 39169169 := bstep (se 2 (by rfl) ⟨14688438, by rfl⟩ : syracuseStep 39169169 = 29376877) B29376877
theorem B2862503 : Blo 1016603 2862503 := bstep (se 1 (by rfl) ⟨2146877, by rfl⟩ : syracuseStep 2862503 = 4293755) B4293755
theorem B1715627 : Blo 1016603 1715627 := bstep (se 1 (by rfl) ⟨1286720, by rfl⟩ : syracuseStep 1715627 = 2573441) B2573441
theorem B1322951 : Blo 1016603 1322951 := bstep (se 1 (by rfl) ⟨992213, by rfl⟩ : syracuseStep 1322951 = 1984427) B1984427
theorem B3486023 : Blo 1016603 3486023 := bstep (se 1 (by rfl) ⟨2614517, by rfl⟩ : syracuseStep 3486023 = 5229035) B5229035
theorem B5157431 : Blo 1016603 5157431 := bstep (se 1 (by rfl) ⟨3868073, by rfl⟩ : syracuseStep 5157431 = 7736147) B7736147
theorem B7844633 : Blo 1016603 7844633 := bstep (se 2 (by rfl) ⟨2941737, by rfl⟩ : syracuseStep 7844633 = 5883475) B5883475
theorem B17412893 : Blo 1016603 17412893 := bstep (se 3 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 17412893 = 6529835) B6529835
theorem B1291135 : Blo 1016603 1291135 := bstep (se 1 (by rfl) ⟨968351, by rfl⟩ : syracuseStep 1291135 = 1936703) B1936703
theorem B1717807 : Blo 1016603 1717807 := bstep (se 1 (by rfl) ⟨1288355, by rfl⟩ : syracuseStep 1717807 = 2576711) B2576711
theorem B1718327 : Blo 1016603 1718327 := bstep (se 1 (by rfl) ⟨1288745, by rfl⟩ : syracuseStep 1718327 = 2577491) B2577491
theorem B7453433 : Blo 1016603 7453433 := bstep (se 2 (by rfl) ⟨2795037, by rfl⟩ : syracuseStep 7453433 = 5590075) B5590075
theorem B1719103 : Blo 1016603 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B7748783 : Blo 1016603 7748783 := bstep (se 1 (by rfl) ⟨5811587, by rfl⟩ : syracuseStep 7748783 = 11623175) B11623175
theorem B2178407 : Blo 1016603 2178407 := bstep (se 1 (by rfl) ⟨1633805, by rfl⟩ : syracuseStep 2178407 = 3267611) B3267611
theorem B3097129 : Blo 1016603 3097129 := bstep (se 2 (by rfl) ⟨1161423, by rfl⟩ : syracuseStep 3097129 = 2322847) B2322847
theorem B55820987 : Blo 1016603 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B11453561 : Blo 1016603 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B4637881 : Blo 1016603 4637881 := bstep (se 2 (by rfl) ⟨1739205, by rfl⟩ : syracuseStep 4637881 = 3478411) B3478411
theorem B11585267 : Blo 1016603 11585267 := bstep (se 1 (by rfl) ⟨8688950, by rfl⟩ : syracuseStep 11585267 = 17377901) B17377901
theorem B2574251 : Blo 1016603 2574251 := bstep (se 1 (by rfl) ⟨1930688, by rfl⟩ : syracuseStep 2574251 = 3861377) B3861377
theorem B4180027 : Blo 1016603 4180027 := bstep (se 1 (by rfl) ⟨3135020, by rfl⟩ : syracuseStep 4180027 = 6270041) B6270041
theorem B2574463 : Blo 1016603 2574463 := bstep (se 1 (by rfl) ⟨1930847, by rfl⟩ : syracuseStep 2574463 = 3861695) B3861695
theorem B1526171 : Blo 1016603 1526171 := bstep (se 1 (by rfl) ⟨1144628, by rfl⟩ : syracuseStep 1526171 = 2289257) B2289257
theorem B2575091 : Blo 1016603 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B1526777 : Blo 1016603 1526777 := bstep (se 2 (by rfl) ⟨572541, by rfl⟩ : syracuseStep 1526777 = 1145083) B1145083
theorem B2575547 : Blo 1016603 2575547 := bstep (se 1 (by rfl) ⟨1931660, by rfl⟩ : syracuseStep 2575547 = 3863321) B3863321
theorem B4705487 : Blo 1016603 4705487 := bstep (se 1 (by rfl) ⟨3529115, by rfl⟩ : syracuseStep 4705487 = 7058231) B7058231
theorem B1527035 : Blo 1016603 1527035 := bstep (se 1 (by rfl) ⟨1145276, by rfl⟩ : syracuseStep 1527035 = 2290553) B2290553
theorem B2903471 : Blo 1016603 2903471 := bstep (se 1 (by rfl) ⟨2177603, by rfl⟩ : syracuseStep 2903471 = 4355207) B4355207
theorem B1527263 : Blo 1016603 1527263 := bstep (se 1 (by rfl) ⟨1145447, by rfl⟩ : syracuseStep 1527263 = 2290895) B2290895
theorem B10440161 : Blo 1016603 10440161 := bstep (se 2 (by rfl) ⟨3915060, by rfl⟩ : syracuseStep 10440161 = 7830121) B7830121
theorem B44092997 : Blo 1016603 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B1527743 : Blo 1016603 1527743 := bstep (se 1 (by rfl) ⟨1145807, by rfl⟩ : syracuseStep 1527743 = 2291615) B2291615
theorem B7327817 : Blo 1016603 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B1528367 : Blo 1016603 1528367 := bstep (se 1 (by rfl) ⟨1146275, by rfl⟩ : syracuseStep 1528367 = 2292551) B2292551
theorem B1528553 : Blo 1016603 1528553 := bstep (se 2 (by rfl) ⟨573207, by rfl⟩ : syracuseStep 1528553 = 1146415) B1146415
theorem B1528607 : Blo 1016603 1528607 := bstep (se 1 (by rfl) ⟨1146455, by rfl⟩ : syracuseStep 1528607 = 2292911) B2292911
theorem B2577359 : Blo 1016603 2577359 := bstep (se 1 (by rfl) ⟨1933019, by rfl⟩ : syracuseStep 2577359 = 3866039) B3866039
theorem B23516219 : Blo 1016603 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B1529087 : Blo 1016603 1529087 := bstep (se 1 (by rfl) ⟨1146815, by rfl⟩ : syracuseStep 1529087 = 2293631) B2293631
theorem B5166665 : Blo 1016603 5166665 := bstep (se 2 (by rfl) ⟨1937499, by rfl⟩ : syracuseStep 5166665 = 3874999) B3874999
theorem B1529903 : Blo 1016603 1529903 := bstep (se 1 (by rfl) ⟨1147427, by rfl⟩ : syracuseStep 1529903 = 2294855) B2294855
theorem B2611273 : Blo 1016603 2611273 := bstep (se 2 (by rfl) ⟨979227, by rfl⟩ : syracuseStep 2611273 = 1958455) B1958455
theorem B2906239 : Blo 1016603 2906239 := bstep (se 1 (by rfl) ⟨2179679, by rfl⟩ : syracuseStep 2906239 = 4359359) B4359359
theorem B26139023 : Blo 1016603 26139023 := bstep (se 1 (by rfl) ⟨19604267, by rfl⟩ : syracuseStep 26139023 = 39208535) B39208535
theorem B5790629 : Blo 1016603 5790629 := bstep (se 4 (by rfl) ⟨542871, by rfl⟩ : syracuseStep 5790629 = 1085743) B1085743
theorem B5037299 : Blo 1016603 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B3431753 : Blo 1016603 3431753 := bstep (se 2 (by rfl) ⟨1286907, by rfl⟩ : syracuseStep 3431753 = 2573815) B2573815
theorem B3431915 : Blo 1016603 3431915 := bstep (se 1 (by rfl) ⟨2573936, by rfl⟩ : syracuseStep 3431915 = 5147873) B5147873
theorem B3268097 : Blo 1016603 3268097 := bstep (se 2 (by rfl) ⟨1225536, by rfl⟩ : syracuseStep 3268097 = 2451073) B2451073
theorem B8708087 : Blo 1016603 8708087 := bstep (se 1 (by rfl) ⟨6531065, by rfl⟩ : syracuseStep 8708087 = 13062131) B13062131
theorem B5955767 : Blo 1016603 5955767 := bstep (se 1 (by rfl) ⟨4466825, by rfl⟩ : syracuseStep 5955767 = 8933651) B8933651
theorem B3433319 : Blo 1016603 3433319 := bstep (se 1 (by rfl) ⟨2574989, by rfl⟩ : syracuseStep 3433319 = 5149979) B5149979
theorem B6972367 : Blo 1016603 6972367 := bstep (se 1 (by rfl) ⟨5229275, by rfl⟩ : syracuseStep 6972367 = 10458551) B10458551
theorem B4350935 : Blo 1016603 4350935 := bstep (se 1 (by rfl) ⟨3263201, by rfl⟩ : syracuseStep 4350935 = 6526403) B6526403
theorem B3433481 : Blo 1016603 3433481 := bstep (se 2 (by rfl) ⟨1287555, by rfl⟩ : syracuseStep 3433481 = 2575111) B2575111
theorem B24765725 : Blo 1016603 24765725 := bstep (se 3 (by rfl) ⟨4643573, by rfl⟩ : syracuseStep 24765725 = 9287147) B9287147
theorem B4352251 : Blo 1016603 4352251 := bstep (se 1 (by rfl) ⟨3264188, by rfl⟩ : syracuseStep 4352251 = 6528377) B6528377
theorem B2287871 : Blo 1016603 2287871 := bstep (se 1 (by rfl) ⟨1715903, by rfl⟩ : syracuseStep 2287871 = 3431807) B3431807
theorem B7727399 : Blo 1016603 7727399 := bstep (se 1 (by rfl) ⟨5795549, by rfl⟩ : syracuseStep 7727399 = 11591099) B11591099
theorem B3927131 : Blo 1016603 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B2288735 : Blo 1016603 2288735 := bstep (se 1 (by rfl) ⟨1716551, by rfl⟩ : syracuseStep 2288735 = 3433103) B3433103
theorem B2289131 : Blo 1016603 2289131 := bstep (se 1 (by rfl) ⟨1716848, by rfl⟩ : syracuseStep 2289131 = 3433697) B3433697
theorem B2290463 : Blo 1016603 2290463 := bstep (se 1 (by rfl) ⟨1717847, by rfl⟩ : syracuseStep 2290463 = 3435695) B3435695
theorem B4354985 : Blo 1016603 4354985 := bstep (se 2 (by rfl) ⟨1633119, by rfl⟩ : syracuseStep 4354985 = 3266239) B3266239
theorem B3667151 : Blo 1016603 3667151 := bstep (se 1 (by rfl) ⟨2750363, by rfl⟩ : syracuseStep 3667151 = 5500727) B5500727
theorem B3863807 : Blo 1016603 3863807 := bstep (se 1 (by rfl) ⟨2897855, by rfl⟩ : syracuseStep 3863807 = 5795711) B5795711
theorem B21985091 : Blo 1016603 21985091 := bstep (se 1 (by rfl) ⟨16488818, by rfl⟩ : syracuseStep 21985091 = 32977637) B32977637
theorem B1963873 : Blo 1016603 1963873 := bstep (se 2 (by rfl) ⟨736452, by rfl⟩ : syracuseStep 1963873 = 1472905) B1472905
theorem B4126585 : Blo 1016603 4126585 := bstep (se 2 (by rfl) ⟨1547469, by rfl⟩ : syracuseStep 4126585 = 3094939) B3094939
theorem B2291759 : Blo 1016603 2291759 := bstep (se 1 (by rfl) ⟨1718819, by rfl⟩ : syracuseStep 2291759 = 3437639) B3437639
theorem B1145191 : Blo 1016603 1145191 := bstep (se 1 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 1145191 = 1717787) B1717787
theorem B11008811 : Blo 1016603 11008811 := bstep (se 1 (by rfl) ⟨8256608, by rfl⟩ : syracuseStep 11008811 = 16513217) B16513217
theorem B2292713 : Blo 1016603 2292713 := bstep (se 2 (by rfl) ⟨859767, by rfl⟩ : syracuseStep 2292713 = 1719535) B1719535
theorem B3865583 : Blo 1016603 3865583 := bstep (se 1 (by rfl) ⟨2899187, by rfl⟩ : syracuseStep 3865583 = 5798375) B5798375
theorem B1145839 : Blo 1016603 1145839 := bstep (se 1 (by rfl) ⟨859379, by rfl⟩ : syracuseStep 1145839 = 1718759) B1718759
theorem B41876585 : Blo 1016603 41876585 := bstep (se 2 (by rfl) ⟨15703719, by rfl⟩ : syracuseStep 41876585 = 31407439) B31407439
theorem B4357907 : Blo 1016603 4357907 := bstep (se 1 (by rfl) ⟨3268430, by rfl⟩ : syracuseStep 4357907 = 6536861) B6536861
theorem B2293739 : Blo 1016603 2293739 := bstep (se 1 (by rfl) ⟨1720304, by rfl⟩ : syracuseStep 2293739 = 3440609) B3440609
theorem B4129505 : Blo 1016603 4129505 := bstep (se 2 (by rfl) ⟨1548564, by rfl⟩ : syracuseStep 4129505 = 3097129) B3097129
theorem B7635707 : Blo 1016603 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B1017447 : Blo 1016603 1017447 := bstep (se 1 (by rfl) ⟨763085, by rfl⟩ : syracuseStep 1017447 = 1526171) B1526171
theorem B15664927 : Blo 1016603 15664927 := bstep (se 1 (by rfl) ⟨11748695, by rfl⟩ : syracuseStep 15664927 = 23497391) B23497391
theorem B1017851 : Blo 1016603 1017851 := bstep (se 1 (by rfl) ⟨763388, by rfl⟩ : syracuseStep 1017851 = 1526777) B1526777
theorem B1018023 : Blo 1016603 1018023 := bstep (se 1 (by rfl) ⟨763517, by rfl⟩ : syracuseStep 1018023 = 1527035) B1527035
theorem B1935647 : Blo 1016603 1935647 := bstep (se 1 (by rfl) ⟨1451735, by rfl⟩ : syracuseStep 1935647 = 2903471) B2903471
theorem B1018175 : Blo 1016603 1018175 := bstep (se 1 (by rfl) ⟨763631, by rfl⟩ : syracuseStep 1018175 = 1527263) B1527263
theorem B29395331 : Blo 1016603 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B1935913 : Blo 1016603 1935913 := bstep (se 2 (by rfl) ⟨725967, by rfl⟩ : syracuseStep 1935913 = 1451935) B1451935
theorem B1018495 : Blo 1016603 1018495 := bstep (se 1 (by rfl) ⟨763871, by rfl⟩ : syracuseStep 1018495 = 1527743) B1527743
theorem B4885211 : Blo 1016603 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B5573369 : Blo 1016603 5573369 := bstep (se 2 (by rfl) ⟨2090013, by rfl⟩ : syracuseStep 5573369 = 4180027) B4180027
theorem B3869639 : Blo 1016603 3869639 := bstep (se 1 (by rfl) ⟨2902229, by rfl⟩ : syracuseStep 3869639 = 5804459) B5804459
theorem B5803001 : Blo 1016603 5803001 := bstep (se 2 (by rfl) ⟨2176125, by rfl⟩ : syracuseStep 5803001 = 4352251) B4352251
theorem B1018911 : Blo 1016603 1018911 := bstep (se 1 (by rfl) ⟨764183, by rfl⟩ : syracuseStep 1018911 = 1528367) B1528367
theorem B1019035 : Blo 1016603 1019035 := bstep (se 1 (by rfl) ⟨764276, by rfl⟩ : syracuseStep 1019035 = 1528553) B1528553
theorem B1019071 : Blo 1016603 1019071 := bstep (se 1 (by rfl) ⟨764303, by rfl⟩ : syracuseStep 1019071 = 1528607) B1528607
theorem B1019391 : Blo 1016603 1019391 := bstep (se 1 (by rfl) ⟨764543, by rfl⟩ : syracuseStep 1019391 = 1529087) B1529087
theorem B3444443 : Blo 1016603 3444443 := bstep (se 1 (by rfl) ⟨2583332, by rfl⟩ : syracuseStep 3444443 = 5166665) B5166665
theorem B1019935 : Blo 1016603 1019935 := bstep (se 1 (by rfl) ⟨764951, by rfl⟩ : syracuseStep 1019935 = 1529903) B1529903
theorem B5509943 : Blo 1016603 5509943 := bstep (se 1 (by rfl) ⟨4132457, by rfl⟩ : syracuseStep 5509943 = 8264915) B8264915
theorem B42407023 : Blo 1016603 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B5805391 : Blo 1016603 5805391 := bstep (se 1 (by rfl) ⟨4354043, by rfl⟩ : syracuseStep 5805391 = 8708087) B8708087
theorem B3970511 : Blo 1016603 3970511 := bstep (se 1 (by rfl) ⟨2977883, by rfl⟩ : syracuseStep 3970511 = 5955767) B5955767
theorem B11015639 : Blo 1016603 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B2758313 : Blo 1016603 2758313 := bstep (se 2 (by rfl) ⟨1034367, by rfl⟩ : syracuseStep 2758313 = 2068735) B2068735
theorem B5151599 : Blo 1016603 5151599 := bstep (se 1 (by rfl) ⟨3863699, by rfl⟩ : syracuseStep 5151599 = 7727399) B7727399
theorem B3874027 : Blo 1016603 3874027 := bstep (se 1 (by rfl) ⟨2905520, by rfl⟩ : syracuseStep 3874027 = 5811041) B5811041
theorem B1908335 : Blo 1016603 1908335 := bstep (se 1 (by rfl) ⟨1431251, by rfl⟩ : syracuseStep 1908335 = 2862503) B2862503
theorem B3481697 : Blo 1016603 3481697 := bstep (se 2 (by rfl) ⟨1305636, by rfl⟩ : syracuseStep 3481697 = 2611273) B2611273
theorem B3874985 : Blo 1016603 3874985 := bstep (se 2 (by rfl) ⟨1453119, by rfl⟩ : syracuseStep 3874985 = 2906239) B2906239
theorem B11608595 : Blo 1016603 11608595 := bstep (se 1 (by rfl) ⟨8706446, by rfl⟩ : syracuseStep 11608595 = 17412893) B17412893
theorem B14656727 : Blo 1016603 14656727 := bstep (se 1 (by rfl) ⟨10992545, by rfl⟩ : syracuseStep 14656727 = 21985091) B21985091
theorem B1452271 : Blo 1016603 1452271 := bstep (se 1 (by rfl) ⟨1089203, by rfl⟩ : syracuseStep 1452271 = 2178407) B2178407
theorem B1716167 : Blo 1016603 1716167 := bstep (se 1 (by rfl) ⟨1287125, by rfl⟩ : syracuseStep 1716167 = 2574251) B2574251
theorem B5157107 : Blo 1016603 5157107 := bstep (se 1 (by rfl) ⟨3867830, by rfl⟩ : syracuseStep 5157107 = 7735661) B7735661
theorem B1159663 : Blo 1016603 1159663 := bstep (se 1 (by rfl) ⟨869747, by rfl⟩ : syracuseStep 1159663 = 1739495) B1739495
theorem B1716727 : Blo 1016603 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B5223199 : Blo 1016603 5223199 := bstep (se 1 (by rfl) ⟨3917399, by rfl⟩ : syracuseStep 5223199 = 7834799) B7834799
theorem B1717031 : Blo 1016603 1717031 := bstep (se 1 (by rfl) ⟨1287773, by rfl⟩ : syracuseStep 1717031 = 2575547) B2575547
theorem B6960107 : Blo 1016603 6960107 := bstep (se 1 (by rfl) ⟨5220080, by rfl⟩ : syracuseStep 6960107 = 10440161) B10440161
theorem B4896071 : Blo 1016603 4896071 := bstep (se 1 (by rfl) ⟨3672053, by rfl⟩ : syracuseStep 4896071 = 7344107) B7344107
theorem B5158727 : Blo 1016603 5158727 := bstep (se 1 (by rfl) ⟨3869045, by rfl⟩ : syracuseStep 5158727 = 7738091) B7738091
theorem B9779069 : Blo 1016603 9779069 := bstep (se 3 (by rfl) ⟨1833575, by rfl⟩ : syracuseStep 9779069 = 3667151) B3667151
theorem B1718239 : Blo 1016603 1718239 := bstep (se 1 (by rfl) ⟨1288679, by rfl⟩ : syracuseStep 1718239 = 2577359) B2577359
theorem B15677479 : Blo 1016603 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B11024633 : Blo 1016603 11024633 := bstep (se 2 (by rfl) ⟨4134237, by rfl⟩ : syracuseStep 11024633 = 8268475) B8268475
theorem B12368807 : Blo 1016603 12368807 := bstep (se 1 (by rfl) ⟨9276605, by rfl⟩ : syracuseStep 12368807 = 18553211) B18553211
theorem B3358199 : Blo 1016603 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B11320883 : Blo 1016603 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B2178731 : Blo 1016603 2178731 := bstep (se 1 (by rfl) ⟨1634048, by rfl⟩ : syracuseStep 2178731 = 3268097) B3268097
theorem B2900623 : Blo 1016603 2900623 := bstep (se 1 (by rfl) ⟨2175467, by rfl⟩ : syracuseStep 2900623 = 4350935) B4350935
theorem B1721513 : Blo 1016603 1721513 := bstep (se 2 (by rfl) ⟨645567, by rfl⟩ : syracuseStep 1721513 = 1291135) B1291135
theorem B11781575 : Blo 1016603 11781575 := bstep (se 1 (by rfl) ⟨8836181, by rfl⟩ : syracuseStep 11781575 = 17672363) B17672363
theorem B1525247 : Blo 1016603 1525247 := bstep (se 1 (by rfl) ⟨1143935, by rfl⟩ : syracuseStep 1525247 = 2287871) B2287871
theorem B1525823 : Blo 1016603 1525823 := bstep (se 1 (by rfl) ⟨1144367, by rfl⟩ : syracuseStep 1525823 = 2288735) B2288735
theorem B11913311 : Blo 1016603 11913311 := bstep (se 1 (by rfl) ⟨8934983, by rfl⟩ : syracuseStep 11913311 = 17869967) B17869967
theorem B1526087 : Blo 1016603 1526087 := bstep (se 1 (by rfl) ⟨1144565, by rfl⟩ : syracuseStep 1526087 = 2289131) B2289131
theorem B1526921 : Blo 1016603 1526921 := bstep (se 2 (by rfl) ⟨572595, by rfl⟩ : syracuseStep 1526921 = 1145191) B1145191
theorem B5229755 : Blo 1016603 5229755 := bstep (se 1 (by rfl) ⟨3922316, by rfl⟩ : syracuseStep 5229755 = 7844633) B7844633
theorem B1526975 : Blo 1016603 1526975 := bstep (se 1 (by rfl) ⟨1145231, by rfl⟩ : syracuseStep 1526975 = 2290463) B2290463
theorem B2903323 : Blo 1016603 2903323 := bstep (se 1 (by rfl) ⟨2177492, by rfl⟩ : syracuseStep 2903323 = 4354985) B4354985
theorem B2575871 : Blo 1016603 2575871 := bstep (se 1 (by rfl) ⟨1931903, by rfl⟩ : syracuseStep 2575871 = 3863807) B3863807
theorem B1527785 : Blo 1016603 1527785 := bstep (se 2 (by rfl) ⟨572919, by rfl⟩ : syracuseStep 1527785 = 1145839) B1145839
theorem B1527839 : Blo 1016603 1527839 := bstep (se 1 (by rfl) ⟨1145879, by rfl⟩ : syracuseStep 1527839 = 2291759) B2291759
theorem B4968955 : Blo 1016603 4968955 := bstep (se 1 (by rfl) ⟨3726716, by rfl⟩ : syracuseStep 4968955 = 7453433) B7453433
theorem B1528475 : Blo 1016603 1528475 := bstep (se 1 (by rfl) ⟨1146356, by rfl⟩ : syracuseStep 1528475 = 2292713) B2292713
theorem B2577055 : Blo 1016603 2577055 := bstep (se 1 (by rfl) ⟨1932791, by rfl⟩ : syracuseStep 2577055 = 3865583) B3865583
theorem B5165855 : Blo 1016603 5165855 := bstep (se 1 (by rfl) ⟨3874391, by rfl⟩ : syracuseStep 5165855 = 7748783) B7748783
theorem B2905271 : Blo 1016603 2905271 := bstep (se 1 (by rfl) ⟨2178953, by rfl⟩ : syracuseStep 2905271 = 4357907) B4357907
theorem B3527869 : Blo 1016603 3527869 := bstep (se 3 (by rfl) ⟨661475, by rfl⟩ : syracuseStep 3527869 = 1322951) B1322951
theorem B1529159 : Blo 1016603 1529159 := bstep (se 1 (by rfl) ⟨1146869, by rfl⟩ : syracuseStep 1529159 = 2293739) B2293739
theorem B37213991 : Blo 1016603 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B2578463 : Blo 1016603 2578463 := bstep (se 1 (by rfl) ⟨1933847, by rfl⟩ : syracuseStep 2578463 = 3867695) B3867695
theorem B11032685 : Blo 1016603 11032685 := bstep (se 3 (by rfl) ⟨2068628, by rfl⟩ : syracuseStep 11032685 = 4137257) B4137257
theorem B1530023 : Blo 1016603 1530023 := bstep (se 1 (by rfl) ⟨1147517, by rfl⟩ : syracuseStep 1530023 = 2295035) B2295035
theorem B1530095 : Blo 1016603 1530095 := bstep (se 1 (by rfl) ⟨1147571, by rfl⟩ : syracuseStep 1530095 = 2295143) B2295143
theorem B7723511 : Blo 1016603 7723511 := bstep (se 1 (by rfl) ⟨5792633, by rfl⟩ : syracuseStep 7723511 = 11585267) B11585267
theorem B9296489 : Blo 1016603 9296489 := bstep (se 2 (by rfl) ⟨3486183, by rfl⟩ : syracuseStep 9296489 = 6972367) B6972367
theorem B1530875 : Blo 1016603 1530875 := bstep (se 1 (by rfl) ⟨1148156, by rfl⟩ : syracuseStep 1530875 = 2296313) B2296313
theorem B2579647 : Blo 1016603 2579647 := bstep (se 1 (by rfl) ⟨1934735, by rfl⟩ : syracuseStep 2579647 = 3869471) B3869471
theorem B3136991 : Blo 1016603 3136991 := bstep (se 1 (by rfl) ⟨2352743, by rfl⟩ : syracuseStep 3136991 = 4705487) B4705487
theorem B2579951 : Blo 1016603 2579951 := bstep (se 1 (by rfl) ⟨1934963, by rfl⟩ : syracuseStep 2579951 = 3869927) B3869927
theorem B8806087 : Blo 1016603 8806087 := bstep (se 1 (by rfl) ⟨6604565, by rfl⟩ : syracuseStep 8806087 = 13209131) B13209131
theorem B3432617 : Blo 1016603 3432617 := bstep (se 2 (by rfl) ⟨1287231, by rfl⟩ : syracuseStep 3432617 = 2574463) B2574463
theorem B13067567 : Blo 1016603 13067567 := bstep (se 1 (by rfl) ⟨9800675, by rfl⟩ : syracuseStep 13067567 = 19601351) B19601351
theorem B17426015 : Blo 1016603 17426015 := bstep (se 1 (by rfl) ⟨13069511, by rfl⟩ : syracuseStep 17426015 = 26139023) B26139023
theorem B3860419 : Blo 1016603 3860419 := bstep (se 1 (by rfl) ⟨2895314, by rfl⟩ : syracuseStep 3860419 = 5790629) B5790629
theorem B13396103 : Blo 1016603 13396103 := bstep (se 1 (by rfl) ⟨10047077, by rfl⟩ : syracuseStep 13396103 = 20094155) B20094155
theorem B2287835 : Blo 1016603 2287835 := bstep (se 1 (by rfl) ⟨1715876, by rfl⟩ : syracuseStep 2287835 = 3431753) B3431753
theorem B2287943 : Blo 1016603 2287943 := bstep (se 1 (by rfl) ⟨1715957, by rfl⟩ : syracuseStep 2287943 = 3431915) B3431915
theorem B6188123 : Blo 1016603 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B2288879 : Blo 1016603 2288879 := bstep (se 1 (by rfl) ⟨1716659, by rfl⟩ : syracuseStep 2288879 = 3433319) B3433319
theorem B2288987 : Blo 1016603 2288987 := bstep (se 1 (by rfl) ⟨1716740, by rfl⟩ : syracuseStep 2288987 = 3433481) B3433481
theorem B16510483 : Blo 1016603 16510483 := bstep (se 1 (by rfl) ⟨12382862, by rfl⟩ : syracuseStep 16510483 = 24765725) B24765725
theorem B24735365 : Blo 1016603 24735365 := bstep (se 4 (by rfl) ⟨2318940, by rfl⟩ : syracuseStep 24735365 = 4637881) B4637881
theorem B3436775 : Blo 1016603 3436775 := bstep (se 1 (by rfl) ⟨2577581, by rfl⟩ : syracuseStep 3436775 = 5155163) B5155163
theorem B3436883 : Blo 1016603 3436883 := bstep (se 1 (by rfl) ⟨2577662, by rfl⟩ : syracuseStep 3436883 = 5155325) B5155325
theorem B2618087 : Blo 1016603 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B2290409 : Blo 1016603 2290409 := bstep (se 2 (by rfl) ⟨858903, by rfl⟩ : syracuseStep 2290409 = 1717807) B1717807
theorem B26112779 : Blo 1016603 26112779 := bstep (se 1 (by rfl) ⟨19584584, by rfl⟩ : syracuseStep 26112779 = 39169169) B39169169
theorem B1143751 : Blo 1016603 1143751 := bstep (se 1 (by rfl) ⟨857813, by rfl⟩ : syracuseStep 1143751 = 1715627) B1715627
theorem B2618497 : Blo 1016603 2618497 := bstep (se 2 (by rfl) ⟨981936, by rfl⟩ : syracuseStep 2618497 = 1963873) B1963873
theorem B5502113 : Blo 1016603 5502113 := bstep (se 2 (by rfl) ⟨2063292, by rfl⟩ : syracuseStep 5502113 = 4126585) B4126585
theorem B2324015 : Blo 1016603 2324015 := bstep (se 1 (by rfl) ⟨1743011, by rfl⟩ : syracuseStep 2324015 = 3486023) B3486023
theorem B3438287 : Blo 1016603 3438287 := bstep (se 1 (by rfl) ⟨2578715, by rfl⟩ : syracuseStep 3438287 = 5157431) B5157431
theorem B2292137 : Blo 1016603 2292137 := bstep (se 2 (by rfl) ⟨859551, by rfl⟩ : syracuseStep 2292137 = 1719103) B1719103
theorem B1145551 : Blo 1016603 1145551 := bstep (se 1 (by rfl) ⟨859163, by rfl⟩ : syracuseStep 1145551 = 1718327) B1718327
theorem B7339207 : Blo 1016603 7339207 := bstep (se 1 (by rfl) ⟨5504405, by rfl⟩ : syracuseStep 7339207 = 11008811) B11008811
theorem B27917723 : Blo 1016603 27917723 := bstep (se 1 (by rfl) ⟨20938292, by rfl⟩ : syracuseStep 27917723 = 41876585) B41876585
theorem B2753003 : Blo 1016603 2753003 := bstep (se 1 (by rfl) ⟨2064752, by rfl⟩ : syracuseStep 2753003 = 4129505) B4129505
theorem B1147675 : Blo 1016603 1147675 := bstep (se 1 (by rfl) ⟨860756, by rfl⟩ : syracuseStep 1147675 = 1721513) B1721513
theorem B3867497 : Blo 1016603 3867497 := bstep (se 2 (by rfl) ⟨1450311, by rfl⟩ : syracuseStep 3867497 = 2900623) B2900623
theorem B1016831 : Blo 1016603 1016831 := bstep (se 1 (by rfl) ⟨762623, by rfl⟩ : syracuseStep 1016831 = 1525247) B1525247
theorem B1017215 : Blo 1016603 1017215 := bstep (se 1 (by rfl) ⟨762911, by rfl⟩ : syracuseStep 1017215 = 1525823) B1525823
theorem B1017391 : Blo 1016603 1017391 := bstep (se 1 (by rfl) ⟨763043, by rfl⟩ : syracuseStep 1017391 = 1526087) B1526087
theorem B19596887 : Blo 1016603 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B6981565 : Blo 1016603 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B3868667 : Blo 1016603 3868667 := bstep (se 1 (by rfl) ⟨2901500, by rfl⟩ : syracuseStep 3868667 = 5803001) B5803001
theorem B1017947 : Blo 1016603 1017947 := bstep (se 1 (by rfl) ⟨763460, by rfl⟩ : syracuseStep 1017947 = 1526921) B1526921
theorem B1017983 : Blo 1016603 1017983 := bstep (se 1 (by rfl) ⟨763487, by rfl⟩ : syracuseStep 1017983 = 1526975) B1526975
theorem B2296295 : Blo 1016603 2296295 := bstep (se 1 (by rfl) ⟨1722221, by rfl⟩ : syracuseStep 2296295 = 3444443) B3444443
theorem B5147225 : Blo 1016603 5147225 := bstep (se 2 (by rfl) ⟨1930209, by rfl⟩ : syracuseStep 5147225 = 3860419) B3860419
theorem B1018523 : Blo 1016603 1018523 := bstep (se 1 (by rfl) ⟨763892, by rfl⟩ : syracuseStep 1018523 = 1527785) B1527785
theorem B1018559 : Blo 1016603 1018559 := bstep (se 1 (by rfl) ⟨763919, by rfl⟩ : syracuseStep 1018559 = 1527839) B1527839
theorem B1936361 : Blo 1016603 1936361 := bstep (se 2 (by rfl) ⟨726135, by rfl⟩ : syracuseStep 1936361 = 1452271) B1452271
theorem B1018983 : Blo 1016603 1018983 := bstep (se 1 (by rfl) ⟨764237, by rfl⟩ : syracuseStep 1018983 = 1528475) B1528475
theorem B3443903 : Blo 1016603 3443903 := bstep (se 1 (by rfl) ⟨2582927, by rfl⟩ : syracuseStep 3443903 = 5165855) B5165855
theorem B3673295 : Blo 1016603 3673295 := bstep (se 1 (by rfl) ⟨2754971, by rfl⟩ : syracuseStep 3673295 = 5509943) B5509943
theorem B1936847 : Blo 1016603 1936847 := bstep (se 1 (by rfl) ⟨1452635, by rfl⟩ : syracuseStep 1936847 = 2905271) B2905271
theorem B1019439 : Blo 1016603 1019439 := bstep (se 1 (by rfl) ⟨764579, by rfl⟩ : syracuseStep 1019439 = 1529159) B1529159
theorem B7343759 : Blo 1016603 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B1838875 : Blo 1016603 1838875 := bstep (se 1 (by rfl) ⟨1379156, by rfl⟩ : syracuseStep 1838875 = 2758313) B2758313
theorem B24809327 : Blo 1016603 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B1020015 : Blo 1016603 1020015 := bstep (se 1 (by rfl) ⟨765011, by rfl⟩ : syracuseStep 1020015 = 1530023) B1530023
theorem B1020063 : Blo 1016603 1020063 := bstep (se 1 (by rfl) ⟨765047, by rfl⟩ : syracuseStep 1020063 = 1530095) B1530095
theorem B5149007 : Blo 1016603 5149007 := bstep (se 1 (by rfl) ⟨3861755, by rfl⟩ : syracuseStep 5149007 = 7723511) B7723511
theorem B3871097 : Blo 1016603 3871097 := bstep (se 2 (by rfl) ⟨1451661, by rfl⟩ : syracuseStep 3871097 = 2903323) B2903323
theorem B1020583 : Blo 1016603 1020583 := bstep (se 1 (by rfl) ⟨765437, by rfl⟩ : syracuseStep 1020583 = 1530875) B1530875
theorem B33461237 : Blo 1016603 33461237 := bstep (se 5 (by rfl) ⟨1568495, by rfl⟩ : syracuseStep 33461237 = 3136991) B3136991
theorem B7739063 : Blo 1016603 7739063 := bstep (se 1 (by rfl) ⟨5804297, by rfl⟩ : syracuseStep 7739063 = 11608595) B11608595
theorem B1546217 : Blo 1016603 1546217 := bstep (se 2 (by rfl) ⟨579831, by rfl⟩ : syracuseStep 1546217 = 1159663) B1159663
theorem B29399021 : Blo 1016603 29399021 := bstep (se 3 (by rfl) ⟨5512316, by rfl⟩ : syracuseStep 29399021 = 11024633) B11024633
theorem B6625273 : Blo 1016603 6625273 := bstep (se 2 (by rfl) ⟨2484477, by rfl⟩ : syracuseStep 6625273 = 4968955) B4968955
theorem B13965317 : Blo 1016603 13965317 := bstep (se 4 (by rfl) ⟨1309248, by rfl⟩ : syracuseStep 13965317 = 2618497) B2618497
theorem B9771151 : Blo 1016603 9771151 := bstep (se 1 (by rfl) ⟨7328363, by rfl⟩ : syracuseStep 9771151 = 14656727) B14656727
theorem B7740521 : Blo 1016603 7740521 := bstep (se 2 (by rfl) ⟨2902695, by rfl⟩ : syracuseStep 7740521 = 5805391) B5805391
theorem B16490243 : Blo 1016603 16490243 := bstep (se 1 (by rfl) ⟨12367682, by rfl⟩ : syracuseStep 16490243 = 24735365) B24735365
theorem B17408519 : Blo 1016603 17408519 := bstep (se 1 (by rfl) ⟨13056389, by rfl⟩ : syracuseStep 17408519 = 26112779) B26112779
theorem B1549343 : Blo 1016603 1549343 := bstep (se 1 (by rfl) ⟨1162007, by rfl⟩ : syracuseStep 1549343 = 2324015) B2324015
theorem B8955197 : Blo 1016603 8955197 := bstep (se 3 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 8955197 = 3358199) B3358199
theorem B11741449 : Blo 1016603 11741449 := bstep (se 2 (by rfl) ⟨4403043, by rfl⟩ : syracuseStep 11741449 = 8806087) B8806087
theorem B7547255 : Blo 1016603 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B1452487 : Blo 1016603 1452487 := bstep (se 1 (by rfl) ⟨1089365, by rfl⟩ : syracuseStep 1452487 = 2178731) B2178731
theorem B5090471 : Blo 1016603 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B7942207 : Blo 1016603 7942207 := bstep (se 1 (by rfl) ⟨5956655, by rfl⟩ : syracuseStep 7942207 = 11913311) B11913311
theorem B1290431 : Blo 1016603 1290431 := bstep (se 1 (by rfl) ⟨967823, by rfl⟩ : syracuseStep 1290431 = 1935647) B1935647
theorem B3715579 : Blo 1016603 3715579 := bstep (se 1 (by rfl) ⟨2786684, by rfl⟩ : syracuseStep 3715579 = 5573369) B5573369
theorem B3486503 : Blo 1016603 3486503 := bstep (se 1 (by rfl) ⟨2614877, by rfl⟩ : syracuseStep 3486503 = 5229755) B5229755
theorem B1717247 : Blo 1016603 1717247 := bstep (se 1 (by rfl) ⟨1287935, by rfl⟩ : syracuseStep 1717247 = 2575871) B2575871
theorem B20886569 : Blo 1016603 20886569 := bstep (se 2 (by rfl) ⟨7832463, by rfl⟩ : syracuseStep 20886569 = 15664927) B15664927
theorem B18560285 : Blo 1016603 18560285 := bstep (se 3 (by rfl) ⟨3480053, by rfl⟩ : syracuseStep 18560285 = 6960107) B6960107
theorem B1718975 : Blo 1016603 1718975 := bstep (se 1 (by rfl) ⟨1289231, by rfl⟩ : syracuseStep 1718975 = 2578463) B2578463
theorem B7355123 : Blo 1016603 7355123 := bstep (se 1 (by rfl) ⟨5516342, by rfl⟩ : syracuseStep 7355123 = 11032685) B11032685
theorem B1719967 : Blo 1016603 1719967 := bstep (se 1 (by rfl) ⟨1289975, by rfl⟩ : syracuseStep 1719967 = 2579951) B2579951
theorem B6964265 : Blo 1016603 6964265 := bstep (se 2 (by rfl) ⟨2611599, by rfl⟩ : syracuseStep 6964265 = 5223199) B5223199
theorem B11617343 : Blo 1016603 11617343 := bstep (se 1 (by rfl) ⟨8713007, by rfl⟩ : syracuseStep 11617343 = 17426015) B17426015
theorem B1525001 : Blo 1016603 1525001 := bstep (se 2 (by rfl) ⟨571875, by rfl⟩ : syracuseStep 1525001 = 1143751) B1143751
theorem B8930735 : Blo 1016603 8930735 := bstep (se 1 (by rfl) ⟨6698051, by rfl⟩ : syracuseStep 8930735 = 13396103) B13396103
theorem B1525223 : Blo 1016603 1525223 := bstep (se 1 (by rfl) ⟨1143917, by rfl⟩ : syracuseStep 1525223 = 2287835) B2287835
theorem B56542697 : Blo 1016603 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B1525295 : Blo 1016603 1525295 := bstep (se 1 (by rfl) ⟨1143971, by rfl⟩ : syracuseStep 1525295 = 2287943) B2287943
theorem B4703825 : Blo 1016603 4703825 := bstep (se 2 (by rfl) ⟨1763934, by rfl⟩ : syracuseStep 4703825 = 3527869) B3527869
theorem B24790637 : Blo 1016603 24790637 := bstep (se 3 (by rfl) ⟨4648244, by rfl⟩ : syracuseStep 24790637 = 9296489) B9296489
theorem B13027229 : Blo 1016603 13027229 := bstep (se 3 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 13027229 = 4885211) B4885211
theorem B1525919 : Blo 1016603 1525919 := bstep (se 1 (by rfl) ⟨1144439, by rfl⟩ : syracuseStep 1525919 = 2288879) B2288879
theorem B1525991 : Blo 1016603 1525991 := bstep (se 1 (by rfl) ⟨1144493, by rfl⟩ : syracuseStep 1525991 = 2288987) B2288987
theorem B1526939 : Blo 1016603 1526939 := bstep (se 1 (by rfl) ⟨1145204, by rfl⟩ : syracuseStep 1526939 = 2290409) B2290409
theorem B3264047 : Blo 1016603 3264047 := bstep (se 1 (by rfl) ⟨2448035, by rfl⟩ : syracuseStep 3264047 = 4896071) B4896071
theorem B1527401 : Blo 1016603 1527401 := bstep (se 2 (by rfl) ⟨572775, by rfl⟩ : syracuseStep 1527401 = 1145551) B1145551
theorem B9785609 : Blo 1016603 9785609 := bstep (se 2 (by rfl) ⟨3669603, by rfl⟩ : syracuseStep 9785609 = 7339207) B7339207
theorem B1528091 : Blo 1016603 1528091 := bstep (se 1 (by rfl) ⟨1146068, by rfl⟩ : syracuseStep 1528091 = 2292137) B2292137
theorem B5165369 : Blo 1016603 5165369 := bstep (se 2 (by rfl) ⟨1937013, by rfl⟩ : syracuseStep 5165369 = 3874027) B3874027
theorem B8245871 : Blo 1016603 8245871 := bstep (se 1 (by rfl) ⟨6184403, by rfl⟩ : syracuseStep 8245871 = 12368807) B12368807
theorem B7854383 : Blo 1016603 7854383 := bstep (se 1 (by rfl) ⟨5890787, by rfl⟩ : syracuseStep 7854383 = 11781575) B11781575
theorem B2579759 : Blo 1016603 2579759 := bstep (se 1 (by rfl) ⟨1934819, by rfl⟩ : syracuseStep 2579759 = 3869639) B3869639
theorem B2581217 : Blo 1016603 2581217 := bstep (se 2 (by rfl) ⟨967956, by rfl⟩ : syracuseStep 2581217 = 1935913) B1935913
theorem B2647007 : Blo 1016603 2647007 := bstep (se 1 (by rfl) ⟨1985255, by rfl⟩ : syracuseStep 2647007 = 3970511) B3970511
theorem B3434399 : Blo 1016603 3434399 := bstep (se 1 (by rfl) ⟨2575799, by rfl⟩ : syracuseStep 3434399 = 5151599) B5151599
theorem B22013977 : Blo 1016603 22013977 := bstep (se 2 (by rfl) ⟨8255241, by rfl⟩ : syracuseStep 22013977 = 16510483) B16510483
theorem B1272223 : Blo 1016603 1272223 := bstep (se 1 (by rfl) ⟨954167, by rfl⟩ : syracuseStep 1272223 = 1908335) B1908335
theorem B2321131 : Blo 1016603 2321131 := bstep (se 1 (by rfl) ⟨1740848, by rfl⟩ : syracuseStep 2321131 = 3481697) B3481697
theorem B2288411 : Blo 1016603 2288411 := bstep (se 1 (by rfl) ⟨1716308, by rfl⟩ : syracuseStep 2288411 = 3432617) B3432617
theorem B2583323 : Blo 1016603 2583323 := bstep (se 1 (by rfl) ⟨1937492, by rfl⟩ : syracuseStep 2583323 = 3874985) B3874985
theorem B2288969 : Blo 1016603 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B8711711 : Blo 1016603 8711711 := bstep (se 1 (by rfl) ⟨6533783, by rfl⟩ : syracuseStep 8711711 = 13067567) B13067567
theorem B3436073 : Blo 1016603 3436073 := bstep (se 2 (by rfl) ⟨1288527, by rfl⟩ : syracuseStep 3436073 = 2577055) B2577055
theorem B4125415 : Blo 1016603 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B2290985 : Blo 1016603 2290985 := bstep (se 2 (by rfl) ⟨859119, by rfl⟩ : syracuseStep 2290985 = 1718239) B1718239
theorem B1144111 : Blo 1016603 1144111 := bstep (se 1 (by rfl) ⟨858083, by rfl⟩ : syracuseStep 1144111 = 1716167) B1716167
theorem B20903305 : Blo 1016603 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B2291183 : Blo 1016603 2291183 := bstep (se 1 (by rfl) ⟨1718387, by rfl⟩ : syracuseStep 2291183 = 3436775) B3436775
theorem B3438071 : Blo 1016603 3438071 := bstep (se 1 (by rfl) ⟨2578553, by rfl⟩ : syracuseStep 3438071 = 5157107) B5157107
theorem B2291255 : Blo 1016603 2291255 := bstep (se 1 (by rfl) ⟨1718441, by rfl⟩ : syracuseStep 2291255 = 3436883) B3436883
theorem B1144687 : Blo 1016603 1144687 := bstep (se 1 (by rfl) ⟨858515, by rfl⟩ : syracuseStep 1144687 = 1717031) B1717031
theorem B3668075 : Blo 1016603 3668075 := bstep (se 1 (by rfl) ⟨2751056, by rfl⟩ : syracuseStep 3668075 = 5502113) B5502113
theorem B2292191 : Blo 1016603 2292191 := bstep (se 1 (by rfl) ⟨1719143, by rfl⟩ : syracuseStep 2292191 = 3438287) B3438287
theorem B3439151 : Blo 1016603 3439151 := bstep (se 1 (by rfl) ⟨2579363, by rfl⟩ : syracuseStep 3439151 = 5158727) B5158727
theorem B6519379 : Blo 1016603 6519379 := bstep (se 1 (by rfl) ⟨4889534, by rfl⟩ : syracuseStep 6519379 = 9779069) B9779069
theorem B3439529 : Blo 1016603 3439529 := bstep (se 2 (by rfl) ⟨1289823, by rfl⟩ : syracuseStep 3439529 = 2579647) B2579647
theorem B18611815 : Blo 1016603 18611815 := bstep (se 1 (by rfl) ⟨13958861, by rfl⟩ : syracuseStep 18611815 = 27917723) B27917723
theorem B1835335 : Blo 1016603 1835335 := bstep (se 1 (by rfl) ⟨1376501, by rfl⟩ : syracuseStep 1835335 = 2753003) B2753003
theorem B3441149 : Blo 1016603 3441149 := bstep (se 3 (by rfl) ⟨645215, by rfl⟩ : syracuseStep 3441149 = 1290431) B1290431
theorem B1016667 : Blo 1016603 1016667 := bstep (se 1 (by rfl) ⟨762500, by rfl⟩ : syracuseStep 1016667 = 1525001) B1525001
theorem B1016815 : Blo 1016603 1016815 := bstep (se 1 (by rfl) ⟨762611, by rfl⟩ : syracuseStep 1016815 = 1525223) B1525223
theorem B1016863 : Blo 1016603 1016863 := bstep (se 1 (by rfl) ⟨762647, by rfl⟩ : syracuseStep 1016863 = 1525295) B1525295
theorem B8684819 : Blo 1016603 8684819 := bstep (se 1 (by rfl) ⟨6513614, by rfl⟩ : syracuseStep 8684819 = 13027229) B13027229
theorem B1017279 : Blo 1016603 1017279 := bstep (se 1 (by rfl) ⟨762959, by rfl⟩ : syracuseStep 1017279 = 1525919) B1525919
theorem B1017327 : Blo 1016603 1017327 := bstep (se 1 (by rfl) ⟨762995, by rfl⟩ : syracuseStep 1017327 = 1525991) B1525991
theorem B1017959 : Blo 1016603 1017959 := bstep (se 1 (by rfl) ⟨763469, by rfl⟩ : syracuseStep 1017959 = 1526939) B1526939
theorem B2295935 : Blo 1016603 2295935 := bstep (se 1 (by rfl) ⟨1721951, by rfl⟩ : syracuseStep 2295935 = 3443903) B3443903
theorem B1018267 : Blo 1016603 1018267 := bstep (se 1 (by rfl) ⟨763700, by rfl⟩ : syracuseStep 1018267 = 1527401) B1527401
theorem B9308753 : Blo 1016603 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B6523739 : Blo 1016603 6523739 := bstep (se 1 (by rfl) ⟨4892804, by rfl⟩ : syracuseStep 6523739 = 9785609) B9785609
theorem B1018727 : Blo 1016603 1018727 := bstep (se 1 (by rfl) ⟨764045, by rfl⟩ : syracuseStep 1018727 = 1528091) B1528091
theorem B3443579 : Blo 1016603 3443579 := bstep (se 1 (by rfl) ⟨2582684, by rfl⟩ : syracuseStep 3443579 = 5165369) B5165369
theorem B1936649 : Blo 1016603 1936649 := bstep (se 2 (by rfl) ⟨726243, by rfl⟩ : syracuseStep 1936649 = 1452487) B1452487
theorem B19599347 : Blo 1016603 19599347 := bstep (se 1 (by rfl) ⟨14699510, by rfl⟩ : syracuseStep 19599347 = 29399021) B29399021
theorem B9310211 : Blo 1016603 9310211 := bstep (se 1 (by rfl) ⟨6982658, by rfl⟩ : syracuseStep 9310211 = 13965317) B13965317
theorem B10589609 : Blo 1016603 10589609 := bstep (se 2 (by rfl) ⟨3971103, by rfl⟩ : syracuseStep 10589609 = 7942207) B7942207
theorem B11605679 : Blo 1016603 11605679 := bstep (se 1 (by rfl) ⟨8704259, by rfl⟩ : syracuseStep 11605679 = 17408519) B17408519
theorem B4954105 : Blo 1016603 4954105 := bstep (se 2 (by rfl) ⟨1857789, by rfl⟩ : syracuseStep 4954105 = 3715579) B3715579
theorem B5970131 : Blo 1016603 5970131 := bstep (se 1 (by rfl) ⟨4477598, by rfl⟩ : syracuseStep 5970131 = 8955197) B8955197
theorem B5807807 : Blo 1016603 5807807 := bstep (se 1 (by rfl) ⟨4355855, by rfl⟩ : syracuseStep 5807807 = 8711711) B8711711
theorem B8692505 : Blo 1016603 8692505 := bstep (se 2 (by rfl) ⟨3259689, by rfl⟩ : syracuseStep 8692505 = 6519379) B6519379
theorem B24815753 : Blo 1016603 24815753 := bstep (se 2 (by rfl) ⟨9305907, by rfl⟩ : syracuseStep 24815753 = 18611815) B18611815
theorem B7744895 : Blo 1016603 7744895 := bstep (se 1 (by rfl) ⟨5808671, by rfl⟩ : syracuseStep 7744895 = 11617343) B11617343
theorem B37695131 : Blo 1016603 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B16527091 : Blo 1016603 16527091 := bstep (se 1 (by rfl) ⟨12395318, by rfl⟩ : syracuseStep 16527091 = 24790637) B24790637
theorem B1290907 : Blo 1016603 1290907 := bstep (se 1 (by rfl) ⟨968180, by rfl⟩ : syracuseStep 1290907 = 1936361) B1936361
theorem B1291231 : Blo 1016603 1291231 := bstep (se 1 (by rfl) ⟨968423, by rfl⟩ : syracuseStep 1291231 = 1936847) B1936847
theorem B2176031 : Blo 1016603 2176031 := bstep (se 1 (by rfl) ⟨1632023, by rfl⟩ : syracuseStep 2176031 = 3264047) B3264047
theorem B4895839 : Blo 1016603 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B3094841 : Blo 1016603 3094841 := bstep (se 2 (by rfl) ⟨1160565, by rfl⟩ : syracuseStep 3094841 = 2321131) B2321131
theorem B5159375 : Blo 1016603 5159375 := bstep (se 1 (by rfl) ⟨3869531, by rfl⟩ : syracuseStep 5159375 = 7739063) B7739063
theorem B1030811 : Blo 1016603 1030811 := bstep (se 1 (by rfl) ⟨773108, by rfl⟩ : syracuseStep 1030811 = 1546217) B1546217
theorem B5160347 : Blo 1016603 5160347 := bstep (se 1 (by rfl) ⟨3870260, by rfl⟩ : syracuseStep 5160347 = 7740521) B7740521
theorem B1719839 : Blo 1016603 1719839 := bstep (se 1 (by rfl) ⟨1289879, by rfl⟩ : syracuseStep 1719839 = 2579759) B2579759
theorem B10993495 : Blo 1016603 10993495 := bstep (se 1 (by rfl) ⟨8245121, by rfl⟩ : syracuseStep 10993495 = 16490243) B16490243
theorem B1720811 : Blo 1016603 1720811 := bstep (se 1 (by rfl) ⟨1290608, by rfl⟩ : syracuseStep 1720811 = 2581217) B2581217
theorem B1032895 : Blo 1016603 1032895 := bstep (se 1 (by rfl) ⟨774671, by rfl⟩ : syracuseStep 1032895 = 1549343) B1549343
theorem B5031503 : Blo 1016603 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B1525481 : Blo 1016603 1525481 := bstep (se 2 (by rfl) ⟨572055, by rfl⟩ : syracuseStep 1525481 = 1144111) B1144111
theorem B27871073 : Blo 1016603 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B1525607 : Blo 1016603 1525607 := bstep (se 1 (by rfl) ⟨1144205, by rfl⟩ : syracuseStep 1525607 = 2288411) B2288411
theorem B1722215 : Blo 1016603 1722215 := bstep (se 1 (by rfl) ⟨1291661, by rfl⟩ : syracuseStep 1722215 = 2583323) B2583323
theorem B3393647 : Blo 1016603 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B1525979 : Blo 1016603 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B1526249 : Blo 1016603 1526249 := bstep (se 2 (by rfl) ⟨572343, by rfl⟩ : syracuseStep 1526249 = 1144687) B1144687
theorem B8833697 : Blo 1016603 8833697 := bstep (se 2 (by rfl) ⟨3312636, by rfl⟩ : syracuseStep 8833697 = 6625273) B6625273
theorem B13028201 : Blo 1016603 13028201 := bstep (se 2 (by rfl) ⟨4885575, by rfl⟩ : syracuseStep 13028201 = 9771151) B9771151
theorem B12373523 : Blo 1016603 12373523 := bstep (se 1 (by rfl) ⟨9280142, by rfl⟩ : syracuseStep 12373523 = 18560285) B18560285
theorem B1527323 : Blo 1016603 1527323 := bstep (se 1 (by rfl) ⟨1145492, by rfl⟩ : syracuseStep 1527323 = 2290985) B2290985
theorem B1527455 : Blo 1016603 1527455 := bstep (se 1 (by rfl) ⟨1145591, by rfl⟩ : syracuseStep 1527455 = 2291183) B2291183
theorem B1527503 : Blo 1016603 1527503 := bstep (se 1 (by rfl) ⟨1145627, by rfl⟩ : syracuseStep 1527503 = 2291255) B2291255
theorem B2445383 : Blo 1016603 2445383 := bstep (se 1 (by rfl) ⟨1834037, by rfl⟩ : syracuseStep 2445383 = 3668075) B3668075
theorem B1528127 : Blo 1016603 1528127 := bstep (se 1 (by rfl) ⟨1146095, by rfl⟩ : syracuseStep 1528127 = 2292191) B2292191
theorem B4903415 : Blo 1016603 4903415 := bstep (se 1 (by rfl) ⟨3677561, by rfl⟩ : syracuseStep 4903415 = 7355123) B7355123
theorem B2578331 : Blo 1016603 2578331 := bstep (se 1 (by rfl) ⟨1933748, by rfl⟩ : syracuseStep 2578331 = 3867497) B3867497
theorem B5953823 : Blo 1016603 5953823 := bstep (se 1 (by rfl) ⟨4465367, by rfl⟩ : syracuseStep 5953823 = 8930735) B8930735
theorem B1530233 : Blo 1016603 1530233 := bstep (se 2 (by rfl) ⟨573837, by rfl⟩ : syracuseStep 1530233 = 1147675) B1147675
theorem B3135883 : Blo 1016603 3135883 := bstep (se 1 (by rfl) ⟨2351912, by rfl⟩ : syracuseStep 3135883 = 4703825) B4703825
theorem B13064591 : Blo 1016603 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B2579111 : Blo 1016603 2579111 := bstep (se 1 (by rfl) ⟨1934333, by rfl⟩ : syracuseStep 2579111 = 3868667) B3868667
theorem B1530863 : Blo 1016603 1530863 := bstep (se 1 (by rfl) ⟨1148147, by rfl⟩ : syracuseStep 1530863 = 2296295) B2296295
theorem B3431483 : Blo 1016603 3431483 := bstep (se 1 (by rfl) ⟨2573612, by rfl⟩ : syracuseStep 3431483 = 5147225) B5147225
theorem B2448863 : Blo 1016603 2448863 := bstep (se 1 (by rfl) ⟨1836647, by rfl⟩ : syracuseStep 2448863 = 3673295) B3673295
theorem B16539551 : Blo 1016603 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B29351969 : Blo 1016603 29351969 := bstep (se 2 (by rfl) ⟨11006988, by rfl⟩ : syracuseStep 29351969 = 22013977) B22013977
theorem B18571373 : Blo 1016603 18571373 := bstep (se 3 (by rfl) ⟨3482132, by rfl⟩ : syracuseStep 18571373 = 6964265) B6964265
theorem B3432671 : Blo 1016603 3432671 := bstep (se 1 (by rfl) ⟨2574503, by rfl⟩ : syracuseStep 3432671 = 5149007) B5149007
theorem B2580731 : Blo 1016603 2580731 := bstep (se 1 (by rfl) ⟨1935548, by rfl⟩ : syracuseStep 2580731 = 3871097) B3871097
theorem B15655265 : Blo 1016603 15655265 := bstep (se 2 (by rfl) ⟨5870724, by rfl⟩ : syracuseStep 15655265 = 11741449) B11741449
theorem B5497247 : Blo 1016603 5497247 := bstep (se 1 (by rfl) ⟨4122935, by rfl⟩ : syracuseStep 5497247 = 8245871) B8245871
theorem B1696297 : Blo 1016603 1696297 := bstep (se 2 (by rfl) ⟨636111, by rfl⟩ : syracuseStep 1696297 = 1272223) B1272223
theorem B22307491 : Blo 1016603 22307491 := bstep (se 1 (by rfl) ⟨16730618, by rfl⟩ : syracuseStep 22307491 = 33461237) B33461237
theorem B5236255 : Blo 1016603 5236255 := bstep (se 1 (by rfl) ⟨3927191, by rfl⟩ : syracuseStep 5236255 = 7854383) B7854383
theorem B2451833 : Blo 1016603 2451833 := bstep (se 2 (by rfl) ⟨919437, by rfl⟩ : syracuseStep 2451833 = 1838875) B1838875
theorem B1764671 : Blo 1016603 1764671 := bstep (se 1 (by rfl) ⟨1323503, by rfl⟩ : syracuseStep 1764671 = 2647007) B2647007
theorem B5500553 : Blo 1016603 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B2289599 : Blo 1016603 2289599 := bstep (se 1 (by rfl) ⟨1717199, by rfl⟩ : syracuseStep 2289599 = 3434399) B3434399
theorem B2290715 : Blo 1016603 2290715 := bstep (se 1 (by rfl) ⟨1718036, by rfl⟩ : syracuseStep 2290715 = 3436073) B3436073
theorem B2324335 : Blo 1016603 2324335 := bstep (se 1 (by rfl) ⟨1743251, by rfl⟩ : syracuseStep 2324335 = 3486503) B3486503
theorem B1144831 : Blo 1016603 1144831 := bstep (se 1 (by rfl) ⟨858623, by rfl⟩ : syracuseStep 1144831 = 1717247) B1717247
theorem B13924379 : Blo 1016603 13924379 := bstep (se 1 (by rfl) ⟨10443284, by rfl⟩ : syracuseStep 13924379 = 20886569) B20886569
theorem B2292047 : Blo 1016603 2292047 := bstep (se 1 (by rfl) ⟨1719035, by rfl⟩ : syracuseStep 2292047 = 3438071) B3438071
theorem B2292767 : Blo 1016603 2292767 := bstep (se 1 (by rfl) ⟨1719575, by rfl⟩ : syracuseStep 2292767 = 3439151) B3439151
theorem B1145983 : Blo 1016603 1145983 := bstep (se 1 (by rfl) ⟨859487, by rfl⟩ : syracuseStep 1145983 = 1718975) B1718975
theorem B2293019 : Blo 1016603 2293019 := bstep (se 1 (by rfl) ⟨1719764, by rfl⟩ : syracuseStep 2293019 = 3439529) B3439529
theorem B2293289 : Blo 1016603 2293289 := bstep (se 2 (by rfl) ⟨859983, by rfl⟩ : syracuseStep 2293289 = 1719967) B1719967
theorem B1147207 : Blo 1016603 1147207 := bstep (se 1 (by rfl) ⟨860405, by rfl⟩ : syracuseStep 1147207 = 1720811) B1720811
theorem B2294099 : Blo 1016603 2294099 := bstep (se 1 (by rfl) ⟨1720574, by rfl⟩ : syracuseStep 2294099 = 3441149) B3441149
theorem B2261729 : Blo 1016603 2261729 := bstep (se 2 (by rfl) ⟨848148, by rfl⟩ : syracuseStep 2261729 = 1696297) B1696297
theorem B1016987 : Blo 1016603 1016987 := bstep (se 1 (by rfl) ⟨762740, by rfl⟩ : syracuseStep 1016987 = 1525481) B1525481
theorem B18580715 : Blo 1016603 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B1017071 : Blo 1016603 1017071 := bstep (se 1 (by rfl) ⟨762803, by rfl⟩ : syracuseStep 1017071 = 1525607) B1525607
theorem B1148143 : Blo 1016603 1148143 := bstep (se 1 (by rfl) ⟨861107, by rfl⟩ : syracuseStep 1148143 = 1722215) B1722215
theorem B2262431 : Blo 1016603 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B1017319 : Blo 1016603 1017319 := bstep (se 1 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 1017319 = 1525979) B1525979
theorem B1017499 : Blo 1016603 1017499 := bstep (se 1 (by rfl) ⟨763124, by rfl⟩ : syracuseStep 1017499 = 1526249) B1526249
theorem B8685467 : Blo 1016603 8685467 := bstep (se 1 (by rfl) ⟨6514100, by rfl⟩ : syracuseStep 8685467 = 13028201) B13028201
theorem B2295719 : Blo 1016603 2295719 := bstep (se 1 (by rfl) ⟨1721789, by rfl⟩ : syracuseStep 2295719 = 3443579) B3443579
theorem B1018215 : Blo 1016603 1018215 := bstep (se 1 (by rfl) ⟨763661, by rfl⟩ : syracuseStep 1018215 = 1527323) B1527323
theorem B1018303 : Blo 1016603 1018303 := bstep (se 1 (by rfl) ⟨763727, by rfl⟩ : syracuseStep 1018303 = 1527455) B1527455
theorem B1018335 : Blo 1016603 1018335 := bstep (se 1 (by rfl) ⟨763751, by rfl⟩ : syracuseStep 1018335 = 1527503) B1527503
theorem B5802749 : Blo 1016603 5802749 := bstep (se 3 (by rfl) ⟨1088015, by rfl⟩ : syracuseStep 5802749 = 2176031) B2176031
theorem B1018751 : Blo 1016603 1018751 := bstep (se 1 (by rfl) ⟨764063, by rfl⟩ : syracuseStep 1018751 = 1528127) B1528127
theorem B5508773 : Blo 1016603 5508773 := bstep (se 4 (by rfl) ⟨516447, by rfl⟩ : syracuseStep 5508773 = 1032895) B1032895
theorem B7737119 : Blo 1016603 7737119 := bstep (se 1 (by rfl) ⟨5802839, by rfl⟩ : syracuseStep 7737119 = 11605679) B11605679
theorem B3969215 : Blo 1016603 3969215 := bstep (se 1 (by rfl) ⟨2976911, by rfl⟩ : syracuseStep 3969215 = 5953823) B5953823
theorem B1020155 : Blo 1016603 1020155 := bstep (se 1 (by rfl) ⟨765116, by rfl⟩ : syracuseStep 1020155 = 1530233) B1530233
theorem B1020575 : Blo 1016603 1020575 := bstep (se 1 (by rfl) ⟨765431, by rfl⟩ : syracuseStep 1020575 = 1530863) B1530863
theorem B3871871 : Blo 1016603 3871871 := bstep (se 1 (by rfl) ⟨2903903, by rfl⟩ : syracuseStep 3871871 = 5807807) B5807807
theorem B19567979 : Blo 1016603 19567979 := bstep (se 1 (by rfl) ⟨14675984, by rfl⟩ : syracuseStep 19567979 = 29351969) B29351969
theorem B6527785 : Blo 1016603 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B27926693 : Blo 1016603 27926693 := bstep (se 4 (by rfl) ⟨2618127, by rfl⟩ : syracuseStep 27926693 = 5236255) B5236255
theorem B9282919 : Blo 1016603 9282919 := bstep (se 1 (by rfl) ⟨6962189, by rfl⟩ : syracuseStep 9282919 = 13924379) B13924379
theorem B14657993 : Blo 1016603 14657993 := bstep (se 2 (by rfl) ⟨5496747, by rfl⟩ : syracuseStep 14657993 = 10993495) B10993495
theorem B3354335 : Blo 1016603 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B14659325 : Blo 1016603 14659325 := bstep (se 3 (by rfl) ⟨2748623, by rfl⟩ : syracuseStep 14659325 = 5497247) B5497247
theorem B6205835 : Blo 1016603 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B6206807 : Blo 1016603 6206807 := bstep (se 1 (by rfl) ⟨4655105, by rfl⟩ : syracuseStep 6206807 = 9310211) B9310211
theorem B7059739 : Blo 1016603 7059739 := bstep (se 1 (by rfl) ⟨5294804, by rfl⟩ : syracuseStep 7059739 = 10589609) B10589609
theorem B1718887 : Blo 1016603 1718887 := bstep (se 1 (by rfl) ⟨1289165, by rfl⟩ : syracuseStep 1718887 = 2578331) B2578331
theorem B3980087 : Blo 1016603 3980087 := bstep (se 1 (by rfl) ⟨2985065, by rfl⟩ : syracuseStep 3980087 = 5970131) B5970131
theorem B1719407 : Blo 1016603 1719407 := bstep (se 1 (by rfl) ⟨1289555, by rfl⟩ : syracuseStep 1719407 = 2579111) B2579111
theorem B22036121 : Blo 1016603 22036121 := bstep (se 2 (by rfl) ⟨8263545, by rfl⟩ : syracuseStep 22036121 = 16527091) B16527091
theorem B11026367 : Blo 1016603 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B1720487 : Blo 1016603 1720487 := bstep (se 1 (by rfl) ⟨1290365, by rfl⟩ : syracuseStep 1720487 = 2580731) B2580731
theorem B10436843 : Blo 1016603 10436843 := bstep (se 1 (by rfl) ⟨7827632, by rfl⟩ : syracuseStep 10436843 = 15655265) B15655265
theorem B1721209 : Blo 1016603 1721209 := bstep (se 2 (by rfl) ⟨645453, by rfl⟩ : syracuseStep 1721209 = 1290907) B1290907
theorem B1721641 : Blo 1016603 1721641 := bstep (se 2 (by rfl) ⟨645615, by rfl⟩ : syracuseStep 1721641 = 1291231) B1291231
theorem B5163263 : Blo 1016603 5163263 := bstep (se 1 (by rfl) ⟨3872447, by rfl⟩ : syracuseStep 5163263 = 7744895) B7744895
theorem B3099113 : Blo 1016603 3099113 := bstep (se 2 (by rfl) ⟨1162167, by rfl⟩ : syracuseStep 3099113 = 2324335) B2324335
theorem B1526399 : Blo 1016603 1526399 := bstep (se 1 (by rfl) ⟨1144799, by rfl⟩ : syracuseStep 1526399 = 2289599) B2289599
theorem B6605473 : Blo 1016603 6605473 := bstep (se 2 (by rfl) ⟨2477052, by rfl⟩ : syracuseStep 6605473 = 4954105) B4954105
theorem B1526441 : Blo 1016603 1526441 := bstep (se 2 (by rfl) ⟨572415, by rfl⟩ : syracuseStep 1526441 = 1144831) B1144831
theorem B4181177 : Blo 1016603 4181177 := bstep (se 2 (by rfl) ⟨1567941, by rfl⟩ : syracuseStep 4181177 = 3135883) B3135883
theorem B1527143 : Blo 1016603 1527143 := bstep (se 1 (by rfl) ⟨1145357, by rfl⟩ : syracuseStep 1527143 = 2290715) B2290715
theorem B5164397 : Blo 1016603 5164397 := bstep (se 3 (by rfl) ⟨968324, by rfl⟩ : syracuseStep 5164397 = 1936649) B1936649
theorem B4705789 : Blo 1016603 4705789 := bstep (se 3 (by rfl) ⟨882335, by rfl⟩ : syracuseStep 4705789 = 1764671) B1764671
theorem B1527977 : Blo 1016603 1527977 := bstep (se 2 (by rfl) ⟨572991, by rfl⟩ : syracuseStep 1527977 = 1145983) B1145983
theorem B1528031 : Blo 1016603 1528031 := bstep (se 1 (by rfl) ⟨1146023, by rfl⟩ : syracuseStep 1528031 = 2292047) B2292047
theorem B14668141 : Blo 1016603 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B1528511 : Blo 1016603 1528511 := bstep (se 1 (by rfl) ⟨1146383, by rfl⟩ : syracuseStep 1528511 = 2292767) B2292767
theorem B1528679 : Blo 1016603 1528679 := bstep (se 1 (by rfl) ⟨1146509, by rfl⟩ : syracuseStep 1528679 = 2293019) B2293019
theorem B1528859 : Blo 1016603 1528859 := bstep (se 1 (by rfl) ⟨1146644, by rfl⟩ : syracuseStep 1528859 = 2293289) B2293289
theorem B2447113 : Blo 1016603 2447113 := bstep (se 2 (by rfl) ⟨917667, by rfl⟩ : syracuseStep 2447113 = 1835335) B1835335
theorem B5789879 : Blo 1016603 5789879 := bstep (se 1 (by rfl) ⟨4342409, by rfl⟩ : syracuseStep 5789879 = 8684819) B8684819
theorem B29743321 : Blo 1016603 29743321 := bstep (se 2 (by rfl) ⟨11153745, by rfl⟩ : syracuseStep 29743321 = 22307491) B22307491
theorem B1530623 : Blo 1016603 1530623 := bstep (se 1 (by rfl) ⟨1147967, by rfl⟩ : syracuseStep 1530623 = 2295935) B2295935
theorem B5889131 : Blo 1016603 5889131 := bstep (se 1 (by rfl) ⟨4416848, by rfl⟩ : syracuseStep 5889131 = 8833697) B8833697
theorem B4349159 : Blo 1016603 4349159 := bstep (se 1 (by rfl) ⟨3261869, by rfl⟩ : syracuseStep 4349159 = 6523739) B6523739
theorem B8249015 : Blo 1016603 8249015 := bstep (se 1 (by rfl) ⟨6186761, by rfl⟩ : syracuseStep 8249015 = 12373523) B12373523
theorem B13066231 : Blo 1016603 13066231 := bstep (se 1 (by rfl) ⟨9799673, by rfl⟩ : syracuseStep 13066231 = 19599347) B19599347
theorem B1630255 : Blo 1016603 1630255 := bstep (se 1 (by rfl) ⟨1222691, by rfl⟩ : syracuseStep 1630255 = 2445383) B2445383
theorem B3268943 : Blo 1016603 3268943 := bstep (se 1 (by rfl) ⟨2451707, by rfl⟩ : syracuseStep 3268943 = 4903415) B4903415
theorem B8709727 : Blo 1016603 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B2287655 : Blo 1016603 2287655 := bstep (se 1 (by rfl) ⟨1715741, by rfl⟩ : syracuseStep 2287655 = 3431483) B3431483
theorem B1632575 : Blo 1016603 1632575 := bstep (se 1 (by rfl) ⟨1224431, by rfl⟩ : syracuseStep 1632575 = 2448863) B2448863
theorem B12380915 : Blo 1016603 12380915 := bstep (se 1 (by rfl) ⟨9285686, by rfl⟩ : syracuseStep 12380915 = 18571373) B18571373
theorem B2288447 : Blo 1016603 2288447 := bstep (se 1 (by rfl) ⟨1716335, by rfl⟩ : syracuseStep 2288447 = 3432671) B3432671
theorem B5795003 : Blo 1016603 5795003 := bstep (se 1 (by rfl) ⟨4346252, by rfl⟩ : syracuseStep 5795003 = 8692505) B8692505
theorem B16543835 : Blo 1016603 16543835 := bstep (se 1 (by rfl) ⟨12407876, by rfl⟩ : syracuseStep 16543835 = 24815753) B24815753
theorem B1634555 : Blo 1016603 1634555 := bstep (se 1 (by rfl) ⟨1225916, by rfl⟩ : syracuseStep 1634555 = 2451833) B2451833
theorem B2748829 : Blo 1016603 2748829 := bstep (se 3 (by rfl) ⟨515405, by rfl⟩ : syracuseStep 2748829 = 1030811) B1030811
theorem B25130087 : Blo 1016603 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B2063227 : Blo 1016603 2063227 := bstep (se 1 (by rfl) ⟨1547420, by rfl⟩ : syracuseStep 2063227 = 3094841) B3094841
theorem B3439583 : Blo 1016603 3439583 := bstep (se 1 (by rfl) ⟨2579687, by rfl⟩ : syracuseStep 3439583 = 5159375) B5159375
theorem B3440231 : Blo 1016603 3440231 := bstep (se 1 (by rfl) ⟨2580173, by rfl⟩ : syracuseStep 3440231 = 5160347) B5160347
theorem B1146559 : Blo 1016603 1146559 := bstep (se 1 (by rfl) ⟨859919, by rfl⟩ : syracuseStep 1146559 = 1719839) B1719839
theorem B1146991 : Blo 1016603 1146991 := bstep (se 1 (by rfl) ⟨860243, by rfl⟩ : syracuseStep 1146991 = 1720487) B1720487
theorem B12387143 : Blo 1016603 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B1508287 : Blo 1016603 1508287 := bstep (se 1 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 1508287 = 2262431) B2262431
theorem B16548893 : Blo 1016603 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B2294945 : Blo 1016603 2294945 := bstep (se 2 (by rfl) ⟨860604, by rfl⟩ : syracuseStep 2294945 = 1721209) B1721209
theorem B3442175 : Blo 1016603 3442175 := bstep (se 1 (by rfl) ⟨2581631, by rfl⟩ : syracuseStep 3442175 = 5163263) B5163263
theorem B2066075 : Blo 1016603 2066075 := bstep (se 1 (by rfl) ⟨1549556, by rfl⟩ : syracuseStep 2066075 = 3099113) B3099113
theorem B2295521 : Blo 1016603 2295521 := bstep (se 2 (by rfl) ⟨860820, by rfl⟩ : syracuseStep 2295521 = 1721641) B1721641
theorem B1017599 : Blo 1016603 1017599 := bstep (se 1 (by rfl) ⟨763199, by rfl⟩ : syracuseStep 1017599 = 1526399) B1526399
theorem B1017627 : Blo 1016603 1017627 := bstep (se 1 (by rfl) ⟨763220, by rfl⟩ : syracuseStep 1017627 = 1526441) B1526441
theorem B3868499 : Blo 1016603 3868499 := bstep (se 1 (by rfl) ⟨2901374, by rfl⟩ : syracuseStep 3868499 = 5802749) B5802749
theorem B6031277 : Blo 1016603 6031277 := bstep (se 3 (by rfl) ⟨1130864, by rfl⟩ : syracuseStep 6031277 = 2261729) B2261729
theorem B1018095 : Blo 1016603 1018095 := bstep (se 1 (by rfl) ⟨763571, by rfl⟩ : syracuseStep 1018095 = 1527143) B1527143
theorem B3442931 : Blo 1016603 3442931 := bstep (se 1 (by rfl) ⟨2582198, by rfl⟩ : syracuseStep 3442931 = 5164397) B5164397
theorem B3672515 : Blo 1016603 3672515 := bstep (se 1 (by rfl) ⟨2754386, by rfl⟩ : syracuseStep 3672515 = 5508773) B5508773
theorem B1018651 : Blo 1016603 1018651 := bstep (se 1 (by rfl) ⟨763988, by rfl⟩ : syracuseStep 1018651 = 1527977) B1527977
theorem B1018687 : Blo 1016603 1018687 := bstep (se 1 (by rfl) ⟨764015, by rfl⟩ : syracuseStep 1018687 = 1528031) B1528031
theorem B1019007 : Blo 1016603 1019007 := bstep (se 1 (by rfl) ⟨764255, by rfl⟩ : syracuseStep 1019007 = 1528511) B1528511
theorem B1019119 : Blo 1016603 1019119 := bstep (se 1 (by rfl) ⟨764339, by rfl⟩ : syracuseStep 1019119 = 1528679) B1528679
theorem B1019239 : Blo 1016603 1019239 := bstep (se 1 (by rfl) ⟨764429, by rfl⟩ : syracuseStep 1019239 = 1528859) B1528859
theorem B13045319 : Blo 1016603 13045319 := bstep (se 1 (by rfl) ⟨9783989, by rfl⟩ : syracuseStep 13045319 = 19567979) B19567979
theorem B1020415 : Blo 1016603 1020415 := bstep (se 1 (by rfl) ⟨765311, by rfl⟩ : syracuseStep 1020415 = 1530623) B1530623
theorem B18617795 : Blo 1016603 18617795 := bstep (se 1 (by rfl) ⟨13963346, by rfl⟩ : syracuseStep 18617795 = 27926693) B27926693
theorem B9771995 : Blo 1016603 9771995 := bstep (se 1 (by rfl) ⟨7328996, by rfl⟩ : syracuseStep 9771995 = 14657993) B14657993
theorem B2236223 : Blo 1016603 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B9772883 : Blo 1016603 9772883 := bstep (se 1 (by rfl) ⟨7329662, by rfl⟩ : syracuseStep 9772883 = 14659325) B14659325
theorem B1089703 : Blo 1016603 1089703 := bstep (se 1 (by rfl) ⟨817277, by rfl⟩ : syracuseStep 1089703 = 1634555) B1634555
theorem B39657761 : Blo 1016603 39657761 := bstep (se 2 (by rfl) ⟨14871660, by rfl⟩ : syracuseStep 39657761 = 29743321) B29743321
theorem B9412985 : Blo 1016603 9412985 := bstep (se 2 (by rfl) ⟨3529869, by rfl⟩ : syracuseStep 9412985 = 7059739) B7059739
theorem B11149805 : Blo 1016603 11149805 := bstep (se 3 (by rfl) ⟨2090588, by rfl⟩ : syracuseStep 11149805 = 4181177) B4181177
theorem B16753391 : Blo 1016603 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B4137871 : Blo 1016603 4137871 := bstep (se 1 (by rfl) ⟨3103403, by rfl⟩ : syracuseStep 4137871 = 6206807) B6206807
theorem B14690747 : Blo 1016603 14690747 := bstep (se 1 (by rfl) ⟨11018060, by rfl⟩ : syracuseStep 14690747 = 22036121) B22036121
theorem B7350911 : Blo 1016603 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B2173673 : Blo 1016603 2173673 := bstep (se 2 (by rfl) ⟨815127, by rfl⟩ : syracuseStep 2173673 = 1630255) B1630255
theorem B6957895 : Blo 1016603 6957895 := bstep (se 1 (by rfl) ⟨5218421, by rfl⟩ : syracuseStep 6957895 = 10436843) B10436843
theorem B11612969 : Blo 1016603 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B5158079 : Blo 1016603 5158079 := bstep (se 1 (by rfl) ⟨3868559, by rfl⟩ : syracuseStep 5158079 = 7737119) B7737119
theorem B6274385 : Blo 1016603 6274385 := bstep (se 2 (by rfl) ⟨2352894, by rfl⟩ : syracuseStep 6274385 = 4705789) B4705789
theorem B2899439 : Blo 1016603 2899439 := bstep (se 1 (by rfl) ⟨2174579, by rfl⟩ : syracuseStep 2899439 = 4349159) B4349159
theorem B2179295 : Blo 1016603 2179295 := bstep (se 1 (by rfl) ⟨1634471, by rfl⟩ : syracuseStep 2179295 = 3268943) B3268943
theorem B1525103 : Blo 1016603 1525103 := bstep (se 1 (by rfl) ⟨1143827, by rfl⟩ : syracuseStep 1525103 = 2287655) B2287655
theorem B1525631 : Blo 1016603 1525631 := bstep (se 1 (by rfl) ⟨1144223, by rfl⟩ : syracuseStep 1525631 = 2288447) B2288447
theorem B3262817 : Blo 1016603 3262817 := bstep (se 2 (by rfl) ⟨1223556, by rfl⟩ : syracuseStep 3262817 = 2447113) B2447113
theorem B11029223 : Blo 1016603 11029223 := bstep (se 1 (by rfl) ⟨8271917, by rfl⟩ : syracuseStep 11029223 = 16543835) B16543835
theorem B8703713 : Blo 1016603 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B1528745 : Blo 1016603 1528745 := bstep (se 2 (by rfl) ⟨573279, by rfl⟩ : syracuseStep 1528745 = 1146559) B1146559
theorem B17421641 : Blo 1016603 17421641 := bstep (se 2 (by rfl) ⟨6533115, by rfl⟩ : syracuseStep 17421641 = 13066231) B13066231
theorem B1529399 : Blo 1016603 1529399 := bstep (se 1 (by rfl) ⟨1147049, by rfl⟩ : syracuseStep 1529399 = 2294099) B2294099
theorem B1529609 : Blo 1016603 1529609 := bstep (se 2 (by rfl) ⟨573603, by rfl⟩ : syracuseStep 1529609 = 1147207) B1147207
theorem B5790311 : Blo 1016603 5790311 := bstep (se 1 (by rfl) ⟨4342733, by rfl⟩ : syracuseStep 5790311 = 8685467) B8685467
theorem B1530479 : Blo 1016603 1530479 := bstep (se 1 (by rfl) ⟨1147859, by rfl⟩ : syracuseStep 1530479 = 2295719) B2295719
theorem B1530857 : Blo 1016603 1530857 := bstep (se 2 (by rfl) ⟨574071, by rfl⟩ : syracuseStep 1530857 = 1148143) B1148143
theorem B12377225 : Blo 1016603 12377225 := bstep (se 2 (by rfl) ⟨4641459, by rfl⟩ : syracuseStep 12377225 = 9282919) B9282919
theorem B2646143 : Blo 1016603 2646143 := bstep (se 1 (by rfl) ⟨1984607, by rfl⟩ : syracuseStep 2646143 = 3969215) B3969215
theorem B2581247 : Blo 1016603 2581247 := bstep (se 1 (by rfl) ⟨1935935, by rfl⟩ : syracuseStep 2581247 = 3871871) B3871871
theorem B8807297 : Blo 1016603 8807297 := bstep (se 2 (by rfl) ⟨3302736, by rfl⟩ : syracuseStep 8807297 = 6605473) B6605473
theorem B3859919 : Blo 1016603 3859919 := bstep (se 1 (by rfl) ⟨2894939, by rfl⟩ : syracuseStep 3859919 = 5789879) B5789879
theorem B3926087 : Blo 1016603 3926087 := bstep (se 1 (by rfl) ⟨2944565, by rfl⟩ : syracuseStep 3926087 = 5889131) B5889131
theorem B5499343 : Blo 1016603 5499343 := bstep (se 1 (by rfl) ⟨4124507, by rfl⟩ : syracuseStep 5499343 = 8249015) B8249015
theorem B19557521 : Blo 1016603 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B3665105 : Blo 1016603 3665105 := bstep (se 2 (by rfl) ⟨1374414, by rfl⟩ : syracuseStep 3665105 = 2748829) B2748829
theorem B4353533 : Blo 1016603 4353533 := bstep (se 3 (by rfl) ⟨816287, by rfl⟩ : syracuseStep 4353533 = 1632575) B1632575
theorem B8253943 : Blo 1016603 8253943 := bstep (se 1 (by rfl) ⟨6190457, by rfl⟩ : syracuseStep 8253943 = 12380915) B12380915
theorem B3863335 : Blo 1016603 3863335 := bstep (se 1 (by rfl) ⟨2897501, by rfl⟩ : syracuseStep 3863335 = 5795003) B5795003
theorem B2291849 : Blo 1016603 2291849 := bstep (se 2 (by rfl) ⟨859443, by rfl⟩ : syracuseStep 2291849 = 1718887) B1718887
theorem B2750969 : Blo 1016603 2750969 := bstep (se 2 (by rfl) ⟨1031613, by rfl⟩ : syracuseStep 2750969 = 2063227) B2063227
theorem B2653391 : Blo 1016603 2653391 := bstep (se 1 (by rfl) ⟨1990043, by rfl⟩ : syracuseStep 2653391 = 3980087) B3980087
theorem B2293055 : Blo 1016603 2293055 := bstep (se 1 (by rfl) ⟨1719791, by rfl⟩ : syracuseStep 2293055 = 3439583) B3439583
theorem B1146271 : Blo 1016603 1146271 := bstep (se 1 (by rfl) ⟨859703, by rfl⟩ : syracuseStep 1146271 = 1719407) B1719407
theorem B2293487 : Blo 1016603 2293487 := bstep (se 1 (by rfl) ⟨1720115, by rfl⟩ : syracuseStep 2293487 = 3440231) B3440231
theorem B8258095 : Blo 1016603 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B1016735 : Blo 1016603 1016735 := bstep (se 1 (by rfl) ⟨762551, by rfl⟩ : syracuseStep 1016735 = 1525103) B1525103
theorem B2294783 : Blo 1016603 2294783 := bstep (se 1 (by rfl) ⟨1721087, by rfl⟩ : syracuseStep 2294783 = 3442175) B3442175
theorem B1377383 : Blo 1016603 1377383 := bstep (se 1 (by rfl) ⟨1033037, by rfl⟩ : syracuseStep 1377383 = 2066075) B2066075
theorem B1017087 : Blo 1016603 1017087 := bstep (se 1 (by rfl) ⟨762815, by rfl⟩ : syracuseStep 1017087 = 1525631) B1525631
theorem B2295287 : Blo 1016603 2295287 := bstep (se 1 (by rfl) ⟨1721465, by rfl⟩ : syracuseStep 2295287 = 3442931) B3442931
theorem B5802475 : Blo 1016603 5802475 := bstep (se 1 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 5802475 = 8703713) B8703713
theorem B1019163 : Blo 1016603 1019163 := bstep (se 1 (by rfl) ⟨764372, by rfl⟩ : syracuseStep 1019163 = 1528745) B1528745
theorem B1019599 : Blo 1016603 1019599 := bstep (se 1 (by rfl) ⟨764699, by rfl⟩ : syracuseStep 1019599 = 1529399) B1529399
theorem B9277193 : Blo 1016603 9277193 := bstep (se 2 (by rfl) ⟨3478947, by rfl⟩ : syracuseStep 9277193 = 6957895) B6957895
theorem B1019739 : Blo 1016603 1019739 := bstep (se 1 (by rfl) ⟨764804, by rfl⟩ : syracuseStep 1019739 = 1529609) B1529609
theorem B1020319 : Blo 1016603 1020319 := bstep (se 1 (by rfl) ⟨765239, by rfl⟩ : syracuseStep 1020319 = 1530479) B1530479
theorem B1020571 : Blo 1016603 1020571 := bstep (se 1 (by rfl) ⟨765428, by rfl⟩ : syracuseStep 1020571 = 1530857) B1530857
theorem B5151113 : Blo 1016603 5151113 := bstep (se 2 (by rfl) ⟨1931667, by rfl⟩ : syracuseStep 5151113 = 3863335) B3863335
theorem B7741979 : Blo 1016603 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B1452863 : Blo 1016603 1452863 := bstep (se 1 (by rfl) ⟨1089647, by rfl⟩ : syracuseStep 1452863 = 2179295) B2179295
theorem B5811749 : Blo 1016603 5811749 := bstep (se 4 (by rfl) ⟨544851, by rfl⟩ : syracuseStep 5811749 = 1089703) B1089703
theorem B5517161 : Blo 1016603 5517161 := bstep (se 2 (by rfl) ⟨2068935, by rfl⟩ : syracuseStep 5517161 = 4137871) B4137871
theorem B2011049 : Blo 1016603 2011049 := bstep (se 2 (by rfl) ⟨754143, by rfl⟩ : syracuseStep 2011049 = 1508287) B1508287
theorem B28225525 : Blo 1016603 28225525 := bstep (se 5 (by rfl) ⟨1323071, by rfl⟩ : syracuseStep 28225525 = 2646143) B2646143
theorem B2175211 : Blo 1016603 2175211 := bstep (se 1 (by rfl) ⟨1631408, by rfl⟩ : syracuseStep 2175211 = 3262817) B3262817
theorem B7352815 : Blo 1016603 7352815 := bstep (se 1 (by rfl) ⟨5514611, by rfl⟩ : syracuseStep 7352815 = 11029223) B11029223
theorem B8696879 : Blo 1016603 8696879 := bstep (se 1 (by rfl) ⟨6522659, by rfl⟩ : syracuseStep 8696879 = 13045319) B13045319
theorem B44021029 : Blo 1016603 44021029 := bstep (se 4 (by rfl) ⟨4126971, by rfl⟩ : syracuseStep 44021029 = 8253943) B8253943
theorem B11614427 : Blo 1016603 11614427 := bstep (se 1 (by rfl) ⟨8710820, by rfl⟩ : syracuseStep 11614427 = 17421641) B17421641
theorem B1490815 : Blo 1016603 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B6275323 : Blo 1016603 6275323 := bstep (se 1 (by rfl) ⟨4706492, by rfl⟩ : syracuseStep 6275323 = 9412985) B9412985
theorem B1720831 : Blo 1016603 1720831 := bstep (se 1 (by rfl) ⟨1290623, by rfl⟩ : syracuseStep 1720831 = 2581247) B2581247
theorem B2573279 : Blo 1016603 2573279 := bstep (se 1 (by rfl) ⟨1929959, by rfl⟩ : syracuseStep 2573279 = 3859919) B3859919
theorem B4900607 : Blo 1016603 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B2443403 : Blo 1016603 2443403 := bstep (se 1 (by rfl) ⟨1832552, by rfl⟩ : syracuseStep 2443403 = 3665105) B3665105
theorem B2902355 : Blo 1016603 2902355 := bstep (se 1 (by rfl) ⟨2176766, by rfl⟩ : syracuseStep 2902355 = 4353533) B4353533
theorem B1527899 : Blo 1016603 1527899 := bstep (se 1 (by rfl) ⟨1145924, by rfl⟩ : syracuseStep 1527899 = 2291849) B2291849
theorem B1528361 : Blo 1016603 1528361 := bstep (se 2 (by rfl) ⟨573135, by rfl⟩ : syracuseStep 1528361 = 1146271) B1146271
theorem B1528703 : Blo 1016603 1528703 := bstep (se 1 (by rfl) ⟨1146527, by rfl⟩ : syracuseStep 1528703 = 2293055) B2293055
theorem B4182923 : Blo 1016603 4182923 := bstep (se 1 (by rfl) ⟨3137192, by rfl⟩ : syracuseStep 4182923 = 6274385) B6274385
theorem B1528991 : Blo 1016603 1528991 := bstep (se 1 (by rfl) ⟨1146743, by rfl⟩ : syracuseStep 1528991 = 2293487) B2293487
theorem B1529321 : Blo 1016603 1529321 := bstep (se 2 (by rfl) ⟨573495, by rfl⟩ : syracuseStep 1529321 = 1146991) B1146991
theorem B11032595 : Blo 1016603 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B1529963 : Blo 1016603 1529963 := bstep (se 1 (by rfl) ⟨1147472, by rfl⟩ : syracuseStep 1529963 = 2294945) B2294945
theorem B1530347 : Blo 1016603 1530347 := bstep (se 1 (by rfl) ⟨1147760, by rfl⟩ : syracuseStep 1530347 = 2295521) B2295521
theorem B2578999 : Blo 1016603 2578999 := bstep (se 1 (by rfl) ⟨1934249, by rfl⟩ : syracuseStep 2578999 = 3868499) B3868499
theorem B4020851 : Blo 1016603 4020851 := bstep (se 1 (by rfl) ⟨3015638, by rfl⟩ : syracuseStep 4020851 = 6031277) B6031277
theorem B2448343 : Blo 1016603 2448343 := bstep (se 1 (by rfl) ⟨1836257, by rfl⟩ : syracuseStep 2448343 = 3672515) B3672515
theorem B23486125 : Blo 1016603 23486125 := bstep (se 3 (by rfl) ⟨4403648, by rfl⟩ : syracuseStep 23486125 = 8807297) B8807297
theorem B7332457 : Blo 1016603 7332457 := bstep (se 2 (by rfl) ⟨2749671, by rfl⟩ : syracuseStep 7332457 = 5499343) B5499343
theorem B12411863 : Blo 1016603 12411863 := bstep (se 1 (by rfl) ⟨9308897, by rfl⟩ : syracuseStep 12411863 = 18617795) B18617795
theorem B3860207 : Blo 1016603 3860207 := bstep (se 1 (by rfl) ⟨2895155, by rfl⟩ : syracuseStep 3860207 = 5790311) B5790311
theorem B6514663 : Blo 1016603 6514663 := bstep (se 1 (by rfl) ⟨4885997, by rfl⟩ : syracuseStep 6514663 = 9771995) B9771995
theorem B8251483 : Blo 1016603 8251483 := bstep (se 1 (by rfl) ⟨6188612, by rfl⟩ : syracuseStep 8251483 = 12377225) B12377225
theorem B6515255 : Blo 1016603 6515255 := bstep (se 1 (by rfl) ⟨4886441, by rfl⟩ : syracuseStep 6515255 = 9772883) B9772883
theorem B26438507 : Blo 1016603 26438507 := bstep (se 1 (by rfl) ⟨19828880, by rfl⟩ : syracuseStep 26438507 = 39657761) B39657761
theorem B7433203 : Blo 1016603 7433203 := bstep (se 1 (by rfl) ⟨5574902, by rfl⟩ : syracuseStep 7433203 = 11149805) B11149805
theorem B11168927 : Blo 1016603 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B7335917 : Blo 1016603 7335917 := bstep (se 3 (by rfl) ⟨1375484, by rfl⟩ : syracuseStep 7335917 = 2750969) B2750969
theorem B2617391 : Blo 1016603 2617391 := bstep (se 1 (by rfl) ⟨1963043, by rfl⟩ : syracuseStep 2617391 = 3926087) B3926087
theorem B9793831 : Blo 1016603 9793831 := bstep (se 1 (by rfl) ⟨7345373, by rfl⟩ : syracuseStep 9793831 = 14690747) B14690747
theorem B5796461 : Blo 1016603 5796461 := bstep (se 3 (by rfl) ⟨1086836, by rfl⟩ : syracuseStep 5796461 = 2173673) B2173673
theorem B13038347 : Blo 1016603 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B3438719 : Blo 1016603 3438719 := bstep (se 1 (by rfl) ⟨2579039, by rfl⟩ : syracuseStep 3438719 = 5158079) B5158079
theorem B1768927 : Blo 1016603 1768927 := bstep (se 1 (by rfl) ⟨1326695, by rfl⟩ : syracuseStep 1768927 = 2653391) B2653391
theorem B1932959 : Blo 1016603 1932959 := bstep (se 1 (by rfl) ⟨1449719, by rfl⟩ : syracuseStep 1932959 = 2899439) B2899439
theorem B6979709 : Blo 1016603 6979709 := bstep (se 3 (by rfl) ⟨1308695, by rfl⟩ : syracuseStep 6979709 = 2617391) B2617391
theorem B2294441 : Blo 1016603 2294441 := bstep (se 2 (by rfl) ⟨860415, by rfl⟩ : syracuseStep 2294441 = 1720831) B1720831
theorem B1934903 : Blo 1016603 1934903 := bstep (se 1 (by rfl) ⟨1451177, by rfl⟩ : syracuseStep 1934903 = 2902355) B2902355
theorem B8686217 : Blo 1016603 8686217 := bstep (se 2 (by rfl) ⟨3257331, by rfl⟩ : syracuseStep 8686217 = 6514663) B6514663
theorem B1018599 : Blo 1016603 1018599 := bstep (se 1 (by rfl) ⟨763949, by rfl⟩ : syracuseStep 1018599 = 1527899) B1527899
theorem B44043173 : Blo 1016603 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B3673021 : Blo 1016603 3673021 := bstep (se 3 (by rfl) ⟨688691, by rfl⟩ : syracuseStep 3673021 = 1377383) B1377383
theorem B1018907 : Blo 1016603 1018907 := bstep (se 1 (by rfl) ⟨764180, by rfl⟩ : syracuseStep 1018907 = 1528361) B1528361
theorem B1019135 : Blo 1016603 1019135 := bstep (se 1 (by rfl) ⟨764351, by rfl⟩ : syracuseStep 1019135 = 1528703) B1528703
theorem B2788615 : Blo 1016603 2788615 := bstep (se 1 (by rfl) ⟨2091461, by rfl⟩ : syracuseStep 2788615 = 4182923) B4182923
theorem B7736633 : Blo 1016603 7736633 := bstep (se 2 (by rfl) ⟨2901237, by rfl⟩ : syracuseStep 7736633 = 5802475) B5802475
theorem B1019327 : Blo 1016603 1019327 := bstep (se 1 (by rfl) ⟨764495, by rfl⟩ : syracuseStep 1019327 = 1528991) B1528991
theorem B1019547 : Blo 1016603 1019547 := bstep (se 1 (by rfl) ⟨764660, by rfl⟩ : syracuseStep 1019547 = 1529321) B1529321
theorem B1019975 : Blo 1016603 1019975 := bstep (se 1 (by rfl) ⟨764981, by rfl⟩ : syracuseStep 1019975 = 1529963) B1529963
theorem B1020231 : Blo 1016603 1020231 := bstep (se 1 (by rfl) ⟨765173, by rfl⟩ : syracuseStep 1020231 = 1530347) B1530347
theorem B9803753 : Blo 1016603 9803753 := bstep (se 2 (by rfl) ⟨3676407, by rfl⟩ : syracuseStep 9803753 = 7352815) B7352815
theorem B10722269 : Blo 1016603 10722269 := bstep (se 3 (by rfl) ⟨2010425, by rfl⟩ : syracuseStep 10722269 = 4020851) B4020851
theorem B58694705 : Blo 1016603 58694705 := bstep (se 2 (by rfl) ⟨22010514, by rfl⟩ : syracuseStep 58694705 = 44021029) B44021029
theorem B7445951 : Blo 1016603 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B3874301 : Blo 1016603 3874301 := bstep (se 3 (by rfl) ⟨726431, by rfl⟩ : syracuseStep 3874301 = 1452863) B1452863
theorem B3874499 : Blo 1016603 3874499 := bstep (se 1 (by rfl) ⟨2905874, by rfl⟩ : syracuseStep 3874499 = 5811749) B5811749
theorem B3678107 : Blo 1016603 3678107 := bstep (se 1 (by rfl) ⟨2758580, by rfl⟩ : syracuseStep 3678107 = 5517161) B5517161
theorem B4890611 : Blo 1016603 4890611 := bstep (se 1 (by rfl) ⟨3667958, by rfl⟩ : syracuseStep 4890611 = 7335917) B7335917
theorem B8692231 : Blo 1016603 8692231 := bstep (se 1 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 8692231 = 13038347) B13038347
theorem B7742951 : Blo 1016603 7742951 := bstep (se 1 (by rfl) ⟨5807213, by rfl⟩ : syracuseStep 7742951 = 11614427) B11614427
theorem B1288639 : Blo 1016603 1288639 := bstep (se 1 (by rfl) ⟨966479, by rfl⟩ : syracuseStep 1288639 = 1932959) B1932959
theorem B8367097 : Blo 1016603 8367097 := bstep (se 2 (by rfl) ⟨3137661, by rfl⟩ : syracuseStep 8367097 = 6275323) B6275323
theorem B1715519 : Blo 1016603 1715519 := bstep (se 1 (by rfl) ⟨1286639, by rfl⟩ : syracuseStep 1715519 = 2573279) B2573279
theorem B9776609 : Blo 1016603 9776609 := bstep (se 2 (by rfl) ⟨3666228, by rfl⟩ : syracuseStep 9776609 = 7332457) B7332457
theorem B9910937 : Blo 1016603 9910937 := bstep (se 2 (by rfl) ⟨3716601, by rfl⟩ : syracuseStep 9910937 = 7433203) B7433203
theorem B7355063 : Blo 1016603 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B37634033 : Blo 1016603 37634033 := bstep (se 2 (by rfl) ⟨14112762, by rfl⟩ : syracuseStep 37634033 = 28225525) B28225525
theorem B2900281 : Blo 1016603 2900281 := bstep (se 2 (by rfl) ⟨1087605, by rfl⟩ : syracuseStep 2900281 = 2175211) B2175211
theorem B5161319 : Blo 1016603 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B13058441 : Blo 1016603 13058441 := bstep (se 2 (by rfl) ⟨4896915, by rfl⟩ : syracuseStep 13058441 = 9793831) B9793831
theorem B8274575 : Blo 1016603 8274575 := bstep (se 1 (by rfl) ⟨6205931, by rfl⟩ : syracuseStep 8274575 = 12411863) B12411863
theorem B2573471 : Blo 1016603 2573471 := bstep (se 1 (by rfl) ⟨1930103, by rfl⟩ : syracuseStep 2573471 = 3860207) B3860207
theorem B4343503 : Blo 1016603 4343503 := bstep (se 1 (by rfl) ⟨3257627, by rfl⟩ : syracuseStep 4343503 = 6515255) B6515255
theorem B3264457 : Blo 1016603 3264457 := bstep (se 2 (by rfl) ⟨1224171, by rfl⟩ : syracuseStep 3264457 = 2448343) B2448343
theorem B21451189 : Blo 1016603 21451189 := bstep (se 5 (by rfl) ⟨1005524, by rfl⟩ : syracuseStep 21451189 = 2011049) B2011049
theorem B31314833 : Blo 1016603 31314833 := bstep (se 2 (by rfl) ⟨11743062, by rfl⟩ : syracuseStep 31314833 = 23486125) B23486125
theorem B1987753 : Blo 1016603 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B1529855 : Blo 1016603 1529855 := bstep (se 1 (by rfl) ⟨1147391, by rfl⟩ : syracuseStep 1529855 = 2294783) B2294783
theorem B1530191 : Blo 1016603 1530191 := bstep (se 1 (by rfl) ⟨1147643, by rfl⟩ : syracuseStep 1530191 = 2295287) B2295287
theorem B3267071 : Blo 1016603 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B6184795 : Blo 1016603 6184795 := bstep (se 1 (by rfl) ⟨4638596, by rfl⟩ : syracuseStep 6184795 = 9277193) B9277193
theorem B11001977 : Blo 1016603 11001977 := bstep (se 2 (by rfl) ⟨4125741, by rfl⟩ : syracuseStep 11001977 = 8251483) B8251483
theorem B3434075 : Blo 1016603 3434075 := bstep (se 1 (by rfl) ⟨2575556, by rfl⟩ : syracuseStep 3434075 = 5151113) B5151113
theorem B6515741 : Blo 1016603 6515741 := bstep (se 3 (by rfl) ⟨1221701, by rfl⟩ : syracuseStep 6515741 = 2443403) B2443403
theorem B17625671 : Blo 1016603 17625671 := bstep (se 1 (by rfl) ⟨13219253, by rfl⟩ : syracuseStep 17625671 = 26438507) B26438507
theorem B3864307 : Blo 1016603 3864307 := bstep (se 1 (by rfl) ⟨2898230, by rfl⟩ : syracuseStep 3864307 = 5796461) B5796461
theorem B5797919 : Blo 1016603 5797919 := bstep (se 1 (by rfl) ⟨4348439, by rfl⟩ : syracuseStep 5797919 = 8696879) B8696879
theorem B3438665 : Blo 1016603 3438665 := bstep (se 2 (by rfl) ⟨1289499, by rfl⟩ : syracuseStep 3438665 = 2578999) B2578999
theorem B2292479 : Blo 1016603 2292479 := bstep (se 1 (by rfl) ⟨1719359, by rfl⟩ : syracuseStep 2292479 = 3438719) B3438719
theorem B2358569 : Blo 1016603 2358569 := bstep (se 2 (by rfl) ⟨884463, by rfl⟩ : syracuseStep 2358569 = 1768927) B1768927
theorem B4653139 : Blo 1016603 4653139 := bstep (se 1 (by rfl) ⟨3489854, by rfl⟩ : syracuseStep 4653139 = 6979709) B6979709
theorem B3440879 : Blo 1016603 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B3867041 : Blo 1016603 3867041 := bstep (se 2 (by rfl) ⟨1450140, by rfl⟩ : syracuseStep 3867041 = 2900281) B2900281
theorem B29362115 : Blo 1016603 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B20876555 : Blo 1016603 20876555 := bstep (se 1 (by rfl) ⟨15657416, by rfl⟩ : syracuseStep 20876555 = 31314833) B31314833
theorem B1019903 : Blo 1016603 1019903 := bstep (se 1 (by rfl) ⟨764927, by rfl⟩ : syracuseStep 1019903 = 1529855) B1529855
theorem B1020127 : Blo 1016603 1020127 := bstep (se 1 (by rfl) ⟨765095, by rfl⟩ : syracuseStep 1020127 = 1530191) B1530191
theorem B7148179 : Blo 1016603 7148179 := bstep (se 1 (by rfl) ⟨5361134, by rfl⟩ : syracuseStep 7148179 = 10722269) B10722269
theorem B39129803 : Blo 1016603 39129803 := bstep (se 1 (by rfl) ⟨29347352, by rfl⟩ : syracuseStep 39129803 = 58694705) B58694705
theorem B5152409 : Blo 1016603 5152409 := bstep (se 2 (by rfl) ⟨1932153, by rfl⟩ : syracuseStep 5152409 = 3864307) B3864307
theorem B9808285 : Blo 1016603 9808285 := bstep (se 3 (by rfl) ⟨1839053, by rfl⟩ : syracuseStep 9808285 = 3678107) B3678107
theorem B1715647 : Blo 1016603 1715647 := bstep (se 1 (by rfl) ⟨1286735, by rfl⟩ : syracuseStep 1715647 = 2573471) B2573471
theorem B1289935 : Blo 1016603 1289935 := bstep (se 1 (by rfl) ⟨967451, by rfl⟩ : syracuseStep 1289935 = 1934903) B1934903
theorem B22065533 : Blo 1016603 22065533 := bstep (se 3 (by rfl) ⟨4137287, by rfl⟩ : syracuseStep 22065533 = 8274575) B8274575
theorem B5157755 : Blo 1016603 5157755 := bstep (se 1 (by rfl) ⟨3868316, by rfl⟩ : syracuseStep 5157755 = 7736633) B7736633
theorem B1718185 : Blo 1016603 1718185 := bstep (se 2 (by rfl) ⟨644319, by rfl⟩ : syracuseStep 1718185 = 1288639) B1288639
theorem B4897361 : Blo 1016603 4897361 := bstep (se 2 (by rfl) ⟨1836510, by rfl⟩ : syracuseStep 4897361 = 3673021) B3673021
theorem B6535835 : Blo 1016603 6535835 := bstep (se 1 (by rfl) ⟨4901876, by rfl⟩ : syracuseStep 6535835 = 9803753) B9803753
theorem B11156129 : Blo 1016603 11156129 := bstep (se 2 (by rfl) ⟨4183548, by rfl⟩ : syracuseStep 11156129 = 8367097) B8367097
theorem B2178047 : Blo 1016603 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B3718153 : Blo 1016603 3718153 := bstep (se 2 (by rfl) ⟨1394307, by rfl⟩ : syracuseStep 3718153 = 2788615) B2788615
theorem B4963967 : Blo 1016603 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B3260407 : Blo 1016603 3260407 := bstep (se 1 (by rfl) ⟨2445305, by rfl⟩ : syracuseStep 3260407 = 4890611) B4890611
theorem B5161967 : Blo 1016603 5161967 := bstep (se 1 (by rfl) ⟨3871475, by rfl⟩ : syracuseStep 5161967 = 7742951) B7742951
theorem B26429165 : Blo 1016603 26429165 := bstep (se 3 (by rfl) ⟨4955468, by rfl⟩ : syracuseStep 26429165 = 9910937) B9910937
theorem B4343827 : Blo 1016603 4343827 := bstep (se 1 (by rfl) ⟨3257870, by rfl⟩ : syracuseStep 4343827 = 6515741) B6515741
theorem B11750447 : Blo 1016603 11750447 := bstep (se 1 (by rfl) ⟨8812835, by rfl⟩ : syracuseStep 11750447 = 17625671) B17625671
theorem B4903375 : Blo 1016603 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B1528319 : Blo 1016603 1528319 := bstep (se 1 (by rfl) ⟨1146239, by rfl⟩ : syracuseStep 1528319 = 2292479) B2292479
theorem B8246393 : Blo 1016603 8246393 := bstep (se 2 (by rfl) ⟨3092397, by rfl⟩ : syracuseStep 8246393 = 6184795) B6184795
theorem B25089355 : Blo 1016603 25089355 := bstep (se 1 (by rfl) ⟨18817016, by rfl⟩ : syracuseStep 25089355 = 37634033) B37634033
theorem B8705627 : Blo 1016603 8705627 := bstep (se 1 (by rfl) ⟨6529220, by rfl⟩ : syracuseStep 8705627 = 13058441) B13058441
theorem B1529627 : Blo 1016603 1529627 := bstep (se 1 (by rfl) ⟨1147220, by rfl⟩ : syracuseStep 1529627 = 2294441) B2294441
theorem B11589641 : Blo 1016603 11589641 := bstep (se 2 (by rfl) ⟨4346115, by rfl⟩ : syracuseStep 11589641 = 8692231) B8692231
theorem B5790811 : Blo 1016603 5790811 := bstep (se 1 (by rfl) ⟨4343108, by rfl⟩ : syracuseStep 5790811 = 8686217) B8686217
theorem B5791337 : Blo 1016603 5791337 := bstep (se 2 (by rfl) ⟨2171751, by rfl⟩ : syracuseStep 5791337 = 4343503) B4343503
theorem B2582867 : Blo 1016603 2582867 := bstep (se 1 (by rfl) ⟨1937150, by rfl⟩ : syracuseStep 2582867 = 3874301) B3874301
theorem B2582999 : Blo 1016603 2582999 := bstep (se 1 (by rfl) ⟨1937249, by rfl⟩ : syracuseStep 2582999 = 3874499) B3874499
theorem B4352609 : Blo 1016603 4352609 := bstep (se 2 (by rfl) ⟨1632228, by rfl⟩ : syracuseStep 4352609 = 3264457) B3264457
theorem B7334651 : Blo 1016603 7334651 := bstep (se 1 (by rfl) ⟨5500988, by rfl⟩ : syracuseStep 7334651 = 11001977) B11001977
theorem B28601585 : Blo 1016603 28601585 := bstep (se 2 (by rfl) ⟨10725594, by rfl⟩ : syracuseStep 28601585 = 21451189) B21451189
theorem B2289383 : Blo 1016603 2289383 := bstep (se 1 (by rfl) ⟨1717037, by rfl⟩ : syracuseStep 2289383 = 3434075) B3434075
theorem B2650337 : Blo 1016603 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B1143679 : Blo 1016603 1143679 := bstep (se 1 (by rfl) ⟨857759, by rfl⟩ : syracuseStep 1143679 = 1715519) B1715519
theorem B6517739 : Blo 1016603 6517739 := bstep (se 1 (by rfl) ⟨4888304, by rfl⟩ : syracuseStep 6517739 = 9776609) B9776609
theorem B6289517 : Blo 1016603 6289517 := bstep (se 3 (by rfl) ⟨1179284, by rfl⟩ : syracuseStep 6289517 = 2358569) B2358569
theorem B3865279 : Blo 1016603 3865279 := bstep (se 1 (by rfl) ⟨2898959, by rfl⟩ : syracuseStep 3865279 = 5797919) B5797919
theorem B2292443 : Blo 1016603 2292443 := bstep (se 1 (by rfl) ⟨1719332, by rfl⟩ : syracuseStep 2292443 = 3438665) B3438665
theorem B2293919 : Blo 1016603 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B3441311 : Blo 1016603 3441311 := bstep (se 1 (by rfl) ⟨2580983, by rfl⟩ : syracuseStep 3441311 = 5161967) B5161967
theorem B1018879 : Blo 1016603 1018879 := bstep (se 1 (by rfl) ⟨764159, by rfl⟩ : syracuseStep 1018879 = 1528319) B1528319
theorem B26086535 : Blo 1016603 26086535 := bstep (se 1 (by rfl) ⟨19564901, by rfl⟩ : syracuseStep 26086535 = 39129803) B39129803
theorem B13077713 : Blo 1016603 13077713 := bstep (se 2 (by rfl) ⟨4904142, by rfl⟩ : syracuseStep 13077713 = 9808285) B9808285
theorem B5803751 : Blo 1016603 5803751 := bstep (se 1 (by rfl) ⟨4352813, by rfl⟩ : syracuseStep 5803751 = 8705627) B8705627
theorem B1019751 : Blo 1016603 1019751 := bstep (se 1 (by rfl) ⟨764813, by rfl⟩ : syracuseStep 1019751 = 1529627) B1529627
theorem B4889767 : Blo 1016603 4889767 := bstep (se 1 (by rfl) ⟨3667325, by rfl⟩ : syracuseStep 4889767 = 7334651) B7334651
theorem B5808125 : Blo 1016603 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B31334525 : Blo 1016603 31334525 := bstep (se 3 (by rfl) ⟨5875223, by rfl⟩ : syracuseStep 31334525 = 11750447) B11750447
theorem B5153705 : Blo 1016603 5153705 := bstep (se 2 (by rfl) ⟨1932639, by rfl⟩ : syracuseStep 5153705 = 3865279) B3865279
theorem B4957537 : Blo 1016603 4957537 := bstep (se 2 (by rfl) ⟨1859076, by rfl⟩ : syracuseStep 4957537 = 3718153) B3718153
theorem B6204185 : Blo 1016603 6204185 := bstep (se 2 (by rfl) ⟨2326569, by rfl⟩ : syracuseStep 6204185 = 4653139) B4653139
theorem B19574743 : Blo 1016603 19574743 := bstep (se 1 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 19574743 = 29362115) B29362115
theorem B1719913 : Blo 1016603 1719913 := bstep (se 2 (by rfl) ⟨644967, by rfl⟩ : syracuseStep 1719913 = 1289935) B1289935
theorem B6537833 : Blo 1016603 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B1524905 : Blo 1016603 1524905 := bstep (se 2 (by rfl) ⟨571839, by rfl⟩ : syracuseStep 1524905 = 1143679) B1143679
theorem B1721911 : Blo 1016603 1721911 := bstep (se 1 (by rfl) ⟨1291433, by rfl⟩ : syracuseStep 1721911 = 2582867) B2582867
theorem B1721999 : Blo 1016603 1721999 := bstep (se 1 (by rfl) ⟨1291499, by rfl⟩ : syracuseStep 1721999 = 2582999) B2582999
theorem B2901739 : Blo 1016603 2901739 := bstep (se 1 (by rfl) ⟨2176304, by rfl⟩ : syracuseStep 2901739 = 4352609) B4352609
theorem B1526255 : Blo 1016603 1526255 := bstep (se 1 (by rfl) ⟨1144691, by rfl⟩ : syracuseStep 1526255 = 2289383) B2289383
theorem B4345159 : Blo 1016603 4345159 := bstep (se 1 (by rfl) ⟨3258869, by rfl⟩ : syracuseStep 4345159 = 6517739) B6517739
theorem B7721081 : Blo 1016603 7721081 := bstep (se 2 (by rfl) ⟨2895405, by rfl⟩ : syracuseStep 7721081 = 5790811) B5790811
theorem B3264907 : Blo 1016603 3264907 := bstep (se 1 (by rfl) ⟨2448680, by rfl⟩ : syracuseStep 3264907 = 4897361) B4897361
theorem B1528295 : Blo 1016603 1528295 := bstep (se 1 (by rfl) ⟨1146221, by rfl⟩ : syracuseStep 1528295 = 2292443) B2292443
theorem B4347209 : Blo 1016603 4347209 := bstep (se 2 (by rfl) ⟨1630203, by rfl⟩ : syracuseStep 4347209 = 3260407) B3260407
theorem B2578027 : Blo 1016603 2578027 := bstep (se 1 (by rfl) ⟨1933520, by rfl⟩ : syracuseStep 2578027 = 3867041) B3867041
theorem B17619443 : Blo 1016603 17619443 := bstep (se 1 (by rfl) ⟨13214582, by rfl⟩ : syracuseStep 17619443 = 26429165) B26429165
theorem B13917703 : Blo 1016603 13917703 := bstep (se 1 (by rfl) ⟨10438277, by rfl⟩ : syracuseStep 13917703 = 20876555) B20876555
theorem B5791769 : Blo 1016603 5791769 := bstep (se 2 (by rfl) ⟨2171913, by rfl⟩ : syracuseStep 5791769 = 4343827) B4343827
theorem B5497595 : Blo 1016603 5497595 := bstep (se 1 (by rfl) ⟨4123196, by rfl⟩ : syracuseStep 5497595 = 8246393) B8246393
theorem B7726427 : Blo 1016603 7726427 := bstep (se 1 (by rfl) ⟨5794820, by rfl⟩ : syracuseStep 7726427 = 11589641) B11589641
theorem B2287529 : Blo 1016603 2287529 := bstep (se 2 (by rfl) ⟨857823, by rfl⟩ : syracuseStep 2287529 = 1715647) B1715647
theorem B3860891 : Blo 1016603 3860891 := bstep (se 1 (by rfl) ⟨2895668, by rfl⟩ : syracuseStep 3860891 = 5791337) B5791337
theorem B3434939 : Blo 1016603 3434939 := bstep (se 1 (by rfl) ⟨2576204, by rfl⟩ : syracuseStep 3434939 = 5152409) B5152409
theorem B9530905 : Blo 1016603 9530905 := bstep (se 2 (by rfl) ⟨3574089, by rfl⟩ : syracuseStep 9530905 = 7148179) B7148179
theorem B33452473 : Blo 1016603 33452473 := bstep (se 2 (by rfl) ⟨12544677, by rfl⟩ : syracuseStep 33452473 = 25089355) B25089355
theorem B19067723 : Blo 1016603 19067723 := bstep (se 1 (by rfl) ⟨14300792, by rfl⟩ : syracuseStep 19067723 = 28601585) B28601585
theorem B2290913 : Blo 1016603 2290913 := bstep (se 2 (by rfl) ⟨859092, by rfl⟩ : syracuseStep 2290913 = 1718185) B1718185
theorem B1766891 : Blo 1016603 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B14710355 : Blo 1016603 14710355 := bstep (se 1 (by rfl) ⟨11032766, by rfl⟩ : syracuseStep 14710355 = 22065533) B22065533
theorem B3438503 : Blo 1016603 3438503 := bstep (se 1 (by rfl) ⟨2578877, by rfl⟩ : syracuseStep 3438503 = 5157755) B5157755
theorem B4193011 : Blo 1016603 4193011 := bstep (se 1 (by rfl) ⟨3144758, by rfl⟩ : syracuseStep 4193011 = 6289517) B6289517
theorem B4357223 : Blo 1016603 4357223 := bstep (se 1 (by rfl) ⟨3267917, by rfl⟩ : syracuseStep 4357223 = 6535835) B6535835
theorem B7437419 : Blo 1016603 7437419 := bstep (se 1 (by rfl) ⟨5578064, by rfl⟩ : syracuseStep 7437419 = 11156129) B11156129
theorem B3309311 : Blo 1016603 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B4358555 : Blo 1016603 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B2294207 : Blo 1016603 2294207 := bstep (se 1 (by rfl) ⟨1720655, by rfl⟩ : syracuseStep 2294207 = 3441311) B3441311
theorem B1016603 : Blo 1016603 1016603 := bstep (se 1 (by rfl) ⟨762452, by rfl⟩ : syracuseStep 1016603 = 1524905) B1524905
theorem B1147999 : Blo 1016603 1147999 := bstep (se 1 (by rfl) ⟨860999, by rfl⟩ : syracuseStep 1147999 = 1721999) B1721999
theorem B1017503 : Blo 1016603 1017503 := bstep (se 1 (by rfl) ⟨763127, by rfl⟩ : syracuseStep 1017503 = 1526255) B1526255
theorem B2295881 : Blo 1016603 2295881 := bstep (se 2 (by rfl) ⟨860955, by rfl⟩ : syracuseStep 2295881 = 1721911) B1721911
theorem B8718475 : Blo 1016603 8718475 := bstep (se 1 (by rfl) ⟨6538856, by rfl⟩ : syracuseStep 8718475 = 13077713) B13077713
theorem B3868985 : Blo 1016603 3868985 := bstep (se 2 (by rfl) ⟨1450869, by rfl⟩ : syracuseStep 3868985 = 2901739) B2901739
theorem B3869167 : Blo 1016603 3869167 := bstep (se 1 (by rfl) ⟨2901875, by rfl⟩ : syracuseStep 3869167 = 5803751) B5803751
theorem B5147387 : Blo 1016603 5147387 := bstep (se 1 (by rfl) ⟨3860540, by rfl⟩ : syracuseStep 5147387 = 7721081) B7721081
theorem B1018863 : Blo 1016603 1018863 := bstep (se 1 (by rfl) ⟨764147, by rfl⟩ : syracuseStep 1018863 = 1528295) B1528295
theorem B3872083 : Blo 1016603 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B44603297 : Blo 1016603 44603297 := bstep (se 2 (by rfl) ⟨16726236, by rfl⟩ : syracuseStep 44603297 = 33452473) B33452473
theorem B5150951 : Blo 1016603 5150951 := bstep (se 1 (by rfl) ⟨3863213, by rfl⟩ : syracuseStep 5150951 = 7726427) B7726427
theorem B4136123 : Blo 1016603 4136123 := bstep (se 1 (by rfl) ⟨3102092, by rfl⟩ : syracuseStep 4136123 = 6204185) B6204185
theorem B9806903 : Blo 1016603 9806903 := bstep (se 1 (by rfl) ⟨7355177, by rfl⟩ : syracuseStep 9806903 = 14710355) B14710355
theorem B18556937 : Blo 1016603 18556937 := bstep (se 2 (by rfl) ⟨6958851, by rfl⟩ : syracuseStep 18556937 = 13917703) B13917703
theorem B4958279 : Blo 1016603 4958279 := bstep (se 1 (by rfl) ⟨3718709, by rfl⟩ : syracuseStep 4958279 = 7437419) B7437419
theorem B2206207 : Blo 1016603 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B22362725 : Blo 1016603 22362725 := bstep (se 4 (by rfl) ⟨2096505, by rfl⟩ : syracuseStep 22362725 = 4193011) B4193011
theorem B11746295 : Blo 1016603 11746295 := bstep (se 1 (by rfl) ⟨8809721, by rfl⟩ : syracuseStep 11746295 = 17619443) B17619443
theorem B26099657 : Blo 1016603 26099657 := bstep (se 2 (by rfl) ⟨9787371, by rfl⟩ : syracuseStep 26099657 = 19574743) B19574743
theorem B20889683 : Blo 1016603 20889683 := bstep (se 1 (by rfl) ⟨15667262, by rfl⟩ : syracuseStep 20889683 = 31334525) B31334525
theorem B1525019 : Blo 1016603 1525019 := bstep (se 1 (by rfl) ⟨1143764, by rfl⟩ : syracuseStep 1525019 = 2287529) B2287529
theorem B2573927 : Blo 1016603 2573927 := bstep (se 1 (by rfl) ⟨1930445, by rfl⟩ : syracuseStep 2573927 = 3860891) B3860891
theorem B1527275 : Blo 1016603 1527275 := bstep (se 1 (by rfl) ⟨1145456, by rfl⟩ : syracuseStep 1527275 = 2290913) B2290913
theorem B2904815 : Blo 1016603 2904815 := bstep (se 1 (by rfl) ⟨2178611, by rfl⟩ : syracuseStep 2904815 = 4357223) B4357223
theorem B1529279 : Blo 1016603 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B6610049 : Blo 1016603 6610049 := bstep (se 2 (by rfl) ⟨2478768, by rfl⟩ : syracuseStep 6610049 = 4957537) B4957537
theorem B17391023 : Blo 1016603 17391023 := bstep (se 1 (by rfl) ⟨13043267, by rfl⟩ : syracuseStep 17391023 = 26086535) B26086535
theorem B11592557 : Blo 1016603 11592557 := bstep (se 3 (by rfl) ⟨2173604, by rfl⟩ : syracuseStep 11592557 = 4347209) B4347209
theorem B4711709 : Blo 1016603 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B5793545 : Blo 1016603 5793545 := bstep (se 2 (by rfl) ⟨2172579, by rfl⟩ : syracuseStep 5793545 = 4345159) B4345159
theorem B12707873 : Blo 1016603 12707873 := bstep (se 2 (by rfl) ⟨4765452, by rfl⟩ : syracuseStep 12707873 = 9530905) B9530905
theorem B3861179 : Blo 1016603 3861179 := bstep (se 1 (by rfl) ⟨2895884, by rfl⟩ : syracuseStep 3861179 = 5791769) B5791769
theorem B3665063 : Blo 1016603 3665063 := bstep (se 1 (by rfl) ⟨2748797, by rfl⟩ : syracuseStep 3665063 = 5497595) B5497595
theorem B4353209 : Blo 1016603 4353209 := bstep (se 2 (by rfl) ⟨1632453, by rfl⟩ : syracuseStep 4353209 = 3264907) B3264907
theorem B3435803 : Blo 1016603 3435803 := bstep (se 1 (by rfl) ⟨2576852, by rfl⟩ : syracuseStep 3435803 = 5153705) B5153705
theorem B2289959 : Blo 1016603 2289959 := bstep (se 1 (by rfl) ⟨1717469, by rfl⟩ : syracuseStep 2289959 = 3434939) B3434939
theorem B3437369 : Blo 1016603 3437369 := bstep (se 2 (by rfl) ⟨1289013, by rfl⟩ : syracuseStep 3437369 = 2578027) B2578027
theorem B12711815 : Blo 1016603 12711815 := bstep (se 1 (by rfl) ⟨9533861, by rfl⟩ : syracuseStep 12711815 = 19067723) B19067723
theorem B2292335 : Blo 1016603 2292335 := bstep (se 1 (by rfl) ⟨1719251, by rfl⟩ : syracuseStep 2292335 = 3438503) B3438503
theorem B6519689 : Blo 1016603 6519689 := bstep (se 2 (by rfl) ⟨2444883, by rfl⟩ : syracuseStep 6519689 = 4889767) B4889767
theorem B2293217 : Blo 1016603 2293217 := bstep (se 2 (by rfl) ⟨859956, by rfl⟩ : syracuseStep 2293217 = 1719913) B1719913
theorem B13926455 : Blo 1016603 13926455 := bstep (se 1 (by rfl) ⟨10444841, by rfl⟩ : syracuseStep 13926455 = 20889683) B20889683
theorem B1016679 : Blo 1016603 1016679 := bstep (se 1 (by rfl) ⟨762509, by rfl⟩ : syracuseStep 1016679 = 1525019) B1525019
theorem B1018183 : Blo 1016603 1018183 := bstep (se 1 (by rfl) ⟨763637, by rfl⟩ : syracuseStep 1018183 = 1527275) B1527275
theorem B11766437 : Blo 1016603 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B1936543 : Blo 1016603 1936543 := bstep (se 1 (by rfl) ⟨1452407, by rfl⟩ : syracuseStep 1936543 = 2904815) B2904815
theorem B1019519 : Blo 1016603 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B2757415 : Blo 1016603 2757415 := bstep (se 1 (by rfl) ⟨2068061, by rfl⟩ : syracuseStep 2757415 = 4136123) B4136123
theorem B1715951 : Blo 1016603 1715951 := bstep (se 1 (by rfl) ⟨1286963, by rfl⟩ : syracuseStep 1715951 = 2573927) B2573927
theorem B5158889 : Blo 1016603 5158889 := bstep (se 2 (by rfl) ⟨1934583, by rfl⟩ : syracuseStep 5158889 = 3869167) B3869167
theorem B12564557 : Blo 1016603 12564557 := bstep (se 3 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 12564557 = 4711709) B4711709
theorem B29735531 : Blo 1016603 29735531 := bstep (se 1 (by rfl) ⟨22301648, by rfl⟩ : syracuseStep 29735531 = 44603297) B44603297
theorem B4406699 : Blo 1016603 4406699 := bstep (se 1 (by rfl) ⟨3305024, by rfl⟩ : syracuseStep 4406699 = 6610049) B6610049
theorem B6537935 : Blo 1016603 6537935 := bstep (se 1 (by rfl) ⟨4903451, by rfl⟩ : syracuseStep 6537935 = 9806903) B9806903
theorem B12371291 : Blo 1016603 12371291 := bstep (se 1 (by rfl) ⟨9278468, by rfl⟩ : syracuseStep 12371291 = 18556937) B18556937
theorem B8471915 : Blo 1016603 8471915 := bstep (se 1 (by rfl) ⟨6353936, by rfl⟩ : syracuseStep 8471915 = 12707873) B12707873
theorem B5162777 : Blo 1016603 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B2574119 : Blo 1016603 2574119 := bstep (se 1 (by rfl) ⟨1930589, by rfl⟩ : syracuseStep 2574119 = 3861179) B3861179
theorem B2443375 : Blo 1016603 2443375 := bstep (se 1 (by rfl) ⟨1832531, by rfl⟩ : syracuseStep 2443375 = 3665063) B3665063
theorem B2902139 : Blo 1016603 2902139 := bstep (se 1 (by rfl) ⟨2176604, by rfl⟩ : syracuseStep 2902139 = 4353209) B4353209
theorem B1526639 : Blo 1016603 1526639 := bstep (se 1 (by rfl) ⟨1144979, by rfl⟩ : syracuseStep 1526639 = 2289959) B2289959
theorem B8474543 : Blo 1016603 8474543 := bstep (se 1 (by rfl) ⟨6355907, by rfl⟩ : syracuseStep 8474543 = 12711815) B12711815
theorem B1528223 : Blo 1016603 1528223 := bstep (se 1 (by rfl) ⟨1146167, by rfl⟩ : syracuseStep 1528223 = 2292335) B2292335
theorem B4346459 : Blo 1016603 4346459 := bstep (se 1 (by rfl) ⟨3259844, by rfl⟩ : syracuseStep 4346459 = 6519689) B6519689
theorem B1528811 : Blo 1016603 1528811 := bstep (se 1 (by rfl) ⟨1146608, by rfl⟩ : syracuseStep 1528811 = 2293217) B2293217
theorem B2905703 : Blo 1016603 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B1529471 : Blo 1016603 1529471 := bstep (se 1 (by rfl) ⟨1147103, by rfl⟩ : syracuseStep 1529471 = 2294207) B2294207
theorem B1530587 : Blo 1016603 1530587 := bstep (se 1 (by rfl) ⟨1147940, by rfl⟩ : syracuseStep 1530587 = 2295881) B2295881
theorem B1530665 : Blo 1016603 1530665 := bstep (se 2 (by rfl) ⟨573999, by rfl⟩ : syracuseStep 1530665 = 1147999) B1147999
theorem B2579323 : Blo 1016603 2579323 := bstep (se 1 (by rfl) ⟨1934492, by rfl⟩ : syracuseStep 2579323 = 3868985) B3868985
theorem B3431591 : Blo 1016603 3431591 := bstep (se 1 (by rfl) ⟨2573693, by rfl⟩ : syracuseStep 3431591 = 5147387) B5147387
theorem B11624633 : Blo 1016603 11624633 := bstep (se 2 (by rfl) ⟨4359237, by rfl⟩ : syracuseStep 11624633 = 8718475) B8718475
theorem B3433967 : Blo 1016603 3433967 := bstep (se 1 (by rfl) ⟨2575475, by rfl⟩ : syracuseStep 3433967 = 5150951) B5150951
theorem B11594015 : Blo 1016603 11594015 := bstep (se 1 (by rfl) ⟨8695511, by rfl⟩ : syracuseStep 11594015 = 17391023) B17391023
theorem B7728371 : Blo 1016603 7728371 := bstep (se 1 (by rfl) ⟨5796278, by rfl⟩ : syracuseStep 7728371 = 11592557) B11592557
theorem B3862363 : Blo 1016603 3862363 := bstep (se 1 (by rfl) ⟨2896772, by rfl⟩ : syracuseStep 3862363 = 5793545) B5793545
theorem B3305519 : Blo 1016603 3305519 := bstep (se 1 (by rfl) ⟨2479139, by rfl⟩ : syracuseStep 3305519 = 4958279) B4958279
theorem B2290535 : Blo 1016603 2290535 := bstep (se 1 (by rfl) ⟨1717901, by rfl⟩ : syracuseStep 2290535 = 3435803) B3435803
theorem B2291579 : Blo 1016603 2291579 := bstep (se 1 (by rfl) ⟨1718684, by rfl⟩ : syracuseStep 2291579 = 3437369) B3437369
theorem B14908483 : Blo 1016603 14908483 := bstep (se 1 (by rfl) ⟨11181362, by rfl⟩ : syracuseStep 14908483 = 22362725) B22362725
theorem B7830863 : Blo 1016603 7830863 := bstep (se 1 (by rfl) ⟨5873147, by rfl⟩ : syracuseStep 7830863 = 11746295) B11746295
theorem B17399771 : Blo 1016603 17399771 := bstep (se 1 (by rfl) ⟨13049828, by rfl⟩ : syracuseStep 17399771 = 26099657) B26099657
theorem B4358623 : Blo 1016603 4358623 := bstep (se 1 (by rfl) ⟨3268967, by rfl⟩ : syracuseStep 4358623 = 6537935) B6537935
theorem B3441851 : Blo 1016603 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B1934759 : Blo 1016603 1934759 := bstep (se 1 (by rfl) ⟨1451069, by rfl⟩ : syracuseStep 1934759 = 2902139) B2902139
theorem B1017759 : Blo 1016603 1017759 := bstep (se 1 (by rfl) ⟨763319, by rfl⟩ : syracuseStep 1017759 = 1526639) B1526639
theorem B1018815 : Blo 1016603 1018815 := bstep (se 1 (by rfl) ⟨764111, by rfl⟩ : syracuseStep 1018815 = 1528223) B1528223
theorem B1019207 : Blo 1016603 1019207 := bstep (se 1 (by rfl) ⟨764405, by rfl⟩ : syracuseStep 1019207 = 1528811) B1528811
theorem B1937135 : Blo 1016603 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B1019647 : Blo 1016603 1019647 := bstep (se 1 (by rfl) ⟨764735, by rfl⟩ : syracuseStep 1019647 = 1529471) B1529471
theorem B1020391 : Blo 1016603 1020391 := bstep (se 1 (by rfl) ⟨765293, by rfl⟩ : syracuseStep 1020391 = 1530587) B1530587
theorem B1020443 : Blo 1016603 1020443 := bstep (se 1 (by rfl) ⟨765332, by rfl⟩ : syracuseStep 1020443 = 1530665) B1530665
theorem B5149817 : Blo 1016603 5149817 := bstep (se 2 (by rfl) ⟨1931181, by rfl⟩ : syracuseStep 5149817 = 3862363) B3862363
theorem B3676553 : Blo 1016603 3676553 := bstep (se 2 (by rfl) ⟨1378707, by rfl⟩ : syracuseStep 3676553 = 2757415) B2757415
theorem B5152247 : Blo 1016603 5152247 := bstep (se 1 (by rfl) ⟨3864185, by rfl⟩ : syracuseStep 5152247 = 7728371) B7728371
theorem B2203679 : Blo 1016603 2203679 := bstep (se 1 (by rfl) ⟨1652759, by rfl⟩ : syracuseStep 2203679 = 3305519) B3305519
theorem B5220575 : Blo 1016603 5220575 := bstep (se 1 (by rfl) ⟨3915431, by rfl⟩ : syracuseStep 5220575 = 7830863) B7830863
theorem B9284303 : Blo 1016603 9284303 := bstep (se 1 (by rfl) ⟨6963227, by rfl⟩ : syracuseStep 9284303 = 13926455) B13926455
theorem B5647943 : Blo 1016603 5647943 := bstep (se 1 (by rfl) ⟨4235957, by rfl⟩ : syracuseStep 5647943 = 8471915) B8471915
theorem B1716079 : Blo 1016603 1716079 := bstep (se 1 (by rfl) ⟨1287059, by rfl⟩ : syracuseStep 1716079 = 2574119) B2574119
theorem B7844291 : Blo 1016603 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B5649695 : Blo 1016603 5649695 := bstep (se 1 (by rfl) ⟨4237271, by rfl⟩ : syracuseStep 5649695 = 8474543) B8474543
theorem B3257833 : Blo 1016603 3257833 := bstep (se 2 (by rfl) ⟨1221687, by rfl⟩ : syracuseStep 3257833 = 2443375) B2443375
theorem B2897639 : Blo 1016603 2897639 := bstep (se 1 (by rfl) ⟨2173229, by rfl⟩ : syracuseStep 2897639 = 4346459) B4346459
theorem B7749755 : Blo 1016603 7749755 := bstep (se 1 (by rfl) ⟨5812316, by rfl⟩ : syracuseStep 7749755 = 11624633) B11624633
theorem B1527023 : Blo 1016603 1527023 := bstep (se 1 (by rfl) ⟨1145267, by rfl⟩ : syracuseStep 1527023 = 2290535) B2290535
theorem B1527719 : Blo 1016603 1527719 := bstep (se 1 (by rfl) ⟨1145789, by rfl⟩ : syracuseStep 1527719 = 2291579) B2291579
theorem B8376371 : Blo 1016603 8376371 := bstep (se 1 (by rfl) ⟨6282278, by rfl⟩ : syracuseStep 8376371 = 12564557) B12564557
theorem B19877977 : Blo 1016603 19877977 := bstep (se 2 (by rfl) ⟨7454241, by rfl⟩ : syracuseStep 19877977 = 14908483) B14908483
theorem B2937799 : Blo 1016603 2937799 := bstep (se 1 (by rfl) ⟨2203349, by rfl⟩ : syracuseStep 2937799 = 4406699) B4406699
theorem B8247527 : Blo 1016603 8247527 := bstep (se 1 (by rfl) ⟨6185645, by rfl⟩ : syracuseStep 8247527 = 12371291) B12371291
theorem B2582057 : Blo 1016603 2582057 := bstep (se 2 (by rfl) ⟨968271, by rfl⟩ : syracuseStep 2582057 = 1936543) B1936543
theorem B2287727 : Blo 1016603 2287727 := bstep (se 1 (by rfl) ⟨1715795, by rfl⟩ : syracuseStep 2287727 = 3431591) B3431591
theorem B2289311 : Blo 1016603 2289311 := bstep (se 1 (by rfl) ⟨1716983, by rfl⟩ : syracuseStep 2289311 = 3433967) B3433967
theorem B7729343 : Blo 1016603 7729343 := bstep (se 1 (by rfl) ⟨5797007, by rfl⟩ : syracuseStep 7729343 = 11594015) B11594015
theorem B1143967 : Blo 1016603 1143967 := bstep (se 1 (by rfl) ⟨857975, by rfl⟩ : syracuseStep 1143967 = 1715951) B1715951
theorem B3439097 : Blo 1016603 3439097 := bstep (se 2 (by rfl) ⟨1289661, by rfl⟩ : syracuseStep 3439097 = 2579323) B2579323
theorem B3439259 : Blo 1016603 3439259 := bstep (se 1 (by rfl) ⟨2579444, by rfl⟩ : syracuseStep 3439259 = 5158889) B5158889
theorem B19823687 : Blo 1016603 19823687 := bstep (se 1 (by rfl) ⟨14867765, by rfl⟩ : syracuseStep 19823687 = 29735531) B29735531
theorem B11599847 : Blo 1016603 11599847 := bstep (se 1 (by rfl) ⟨8699885, by rfl⟩ : syracuseStep 11599847 = 17399771) B17399771
theorem B2294567 : Blo 1016603 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B1018015 : Blo 1016603 1018015 := bstep (se 1 (by rfl) ⟨763511, by rfl⟩ : syracuseStep 1018015 = 1527023) B1527023
theorem B1018479 : Blo 1016603 1018479 := bstep (se 1 (by rfl) ⟨763859, by rfl⟩ : syracuseStep 1018479 = 1527719) B1527719
theorem B15668261 : Blo 1016603 15668261 := bstep (se 4 (by rfl) ⟨1468899, by rfl⟩ : syracuseStep 15668261 = 2937799) B2937799
theorem B3480383 : Blo 1016603 3480383 := bstep (se 1 (by rfl) ⟨2610287, by rfl⟩ : syracuseStep 3480383 = 5220575) B5220575
theorem B5152895 : Blo 1016603 5152895 := bstep (se 1 (by rfl) ⟨3864671, by rfl⟩ : syracuseStep 5152895 = 7729343) B7729343
theorem B13215791 : Blo 1016603 13215791 := bstep (se 1 (by rfl) ⟨9911843, by rfl⟩ : syracuseStep 13215791 = 19823687) B19823687
theorem B5811497 : Blo 1016603 5811497 := bstep (se 2 (by rfl) ⟨2179311, by rfl⟩ : syracuseStep 5811497 = 4358623) B4358623
theorem B1289839 : Blo 1016603 1289839 := bstep (se 1 (by rfl) ⟨967379, by rfl⟩ : syracuseStep 1289839 = 1934759) B1934759
theorem B5584247 : Blo 1016603 5584247 := bstep (se 1 (by rfl) ⟨4188185, by rfl⟩ : syracuseStep 5584247 = 8376371) B8376371
theorem B1721371 : Blo 1016603 1721371 := bstep (se 1 (by rfl) ⟨1291028, by rfl⟩ : syracuseStep 1721371 = 2582057) B2582057
theorem B1525151 : Blo 1016603 1525151 := bstep (se 1 (by rfl) ⟨1143863, by rfl⟩ : syracuseStep 1525151 = 2287727) B2287727
theorem B1525289 : Blo 1016603 1525289 := bstep (se 2 (by rfl) ⟨571983, by rfl⟩ : syracuseStep 1525289 = 1143967) B1143967
theorem B4343777 : Blo 1016603 4343777 := bstep (se 2 (by rfl) ⟨1628916, by rfl⟩ : syracuseStep 4343777 = 3257833) B3257833
theorem B1526207 : Blo 1016603 1526207 := bstep (se 1 (by rfl) ⟨1144655, by rfl⟩ : syracuseStep 1526207 = 2289311) B2289311
theorem B5229527 : Blo 1016603 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B5165693 : Blo 1016603 5165693 := bstep (se 3 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 5165693 = 1937135) B1937135
theorem B5166503 : Blo 1016603 5166503 := bstep (se 1 (by rfl) ⟨3874877, by rfl⟩ : syracuseStep 5166503 = 7749755) B7749755
theorem B3433211 : Blo 1016603 3433211 := bstep (se 1 (by rfl) ⟨2574908, by rfl⟩ : syracuseStep 3433211 = 5149817) B5149817
theorem B5498351 : Blo 1016603 5498351 := bstep (se 1 (by rfl) ⟨4123763, by rfl⟩ : syracuseStep 5498351 = 8247527) B8247527
theorem B2451035 : Blo 1016603 2451035 := bstep (se 1 (by rfl) ⟨1838276, by rfl⟩ : syracuseStep 2451035 = 3676553) B3676553
theorem B3434831 : Blo 1016603 3434831 := bstep (se 1 (by rfl) ⟨2576123, by rfl⟩ : syracuseStep 3434831 = 5152247) B5152247
theorem B2288105 : Blo 1016603 2288105 := bstep (se 2 (by rfl) ⟨858039, by rfl⟩ : syracuseStep 2288105 = 1716079) B1716079
theorem B1469119 : Blo 1016603 1469119 := bstep (se 1 (by rfl) ⟨1101839, by rfl⟩ : syracuseStep 1469119 = 2203679) B2203679
theorem B26503969 : Blo 1016603 26503969 := bstep (se 2 (by rfl) ⟨9938988, by rfl⟩ : syracuseStep 26503969 = 19877977) B19877977
theorem B6189535 : Blo 1016603 6189535 := bstep (se 1 (by rfl) ⟨4642151, by rfl⟩ : syracuseStep 6189535 = 9284303) B9284303
theorem B3765295 : Blo 1016603 3765295 := bstep (se 1 (by rfl) ⟨2823971, by rfl⟩ : syracuseStep 3765295 = 5647943) B5647943
theorem B3766463 : Blo 1016603 3766463 := bstep (se 1 (by rfl) ⟨2824847, by rfl⟩ : syracuseStep 3766463 = 5649695) B5649695
theorem B1931759 : Blo 1016603 1931759 := bstep (se 1 (by rfl) ⟨1448819, by rfl⟩ : syracuseStep 1931759 = 2897639) B2897639
theorem B2292731 : Blo 1016603 2292731 := bstep (se 1 (by rfl) ⟨1719548, by rfl⟩ : syracuseStep 2292731 = 3439097) B3439097
theorem B2292839 : Blo 1016603 2292839 := bstep (se 1 (by rfl) ⟨1719629, by rfl⟩ : syracuseStep 2292839 = 3439259) B3439259
theorem B7733231 : Blo 1016603 7733231 := bstep (se 1 (by rfl) ⟨5799923, by rfl⟩ : syracuseStep 7733231 = 11599847) B11599847
theorem B1016767 : Blo 1016603 1016767 := bstep (se 1 (by rfl) ⟨762575, by rfl⟩ : syracuseStep 1016767 = 1525151) B1525151
theorem B1016859 : Blo 1016603 1016859 := bstep (se 1 (by rfl) ⟨762644, by rfl⟩ : syracuseStep 1016859 = 1525289) B1525289
theorem B2295161 : Blo 1016603 2295161 := bstep (se 2 (by rfl) ⟨860685, by rfl⟩ : syracuseStep 2295161 = 1721371) B1721371
theorem B1017471 : Blo 1016603 1017471 := bstep (se 1 (by rfl) ⟨763103, by rfl⟩ : syracuseStep 1017471 = 1526207) B1526207
theorem B3443795 : Blo 1016603 3443795 := bstep (se 1 (by rfl) ⟨2582846, by rfl⟩ : syracuseStep 3443795 = 5165693) B5165693
theorem B3444335 : Blo 1016603 3444335 := bstep (se 1 (by rfl) ⟨2583251, by rfl⟩ : syracuseStep 3444335 = 5166503) B5166503
theorem B5020393 : Blo 1016603 5020393 := bstep (se 2 (by rfl) ⟨1882647, by rfl⟩ : syracuseStep 5020393 = 3765295) B3765295
theorem B3874331 : Blo 1016603 3874331 := bstep (se 1 (by rfl) ⟨2905748, by rfl⟩ : syracuseStep 3874331 = 5811497) B5811497
theorem B1287839 : Blo 1016603 1287839 := bstep (se 1 (by rfl) ⟨965879, by rfl⟩ : syracuseStep 1287839 = 1931759) B1931759
theorem B5155487 : Blo 1016603 5155487 := bstep (se 1 (by rfl) ⟨3866615, by rfl⟩ : syracuseStep 5155487 = 7733231) B7733231
theorem B2895851 : Blo 1016603 2895851 := bstep (se 1 (by rfl) ⟨2171888, by rfl⟩ : syracuseStep 2895851 = 4343777) B4343777
theorem B35338625 : Blo 1016603 35338625 := bstep (se 2 (by rfl) ⟨13251984, by rfl⟩ : syracuseStep 35338625 = 26503969) B26503969
theorem B1719785 : Blo 1016603 1719785 := bstep (se 2 (by rfl) ⟨644919, by rfl⟩ : syracuseStep 1719785 = 1289839) B1289839
theorem B1525403 : Blo 1016603 1525403 := bstep (se 1 (by rfl) ⟨1144052, by rfl⟩ : syracuseStep 1525403 = 2288105) B2288105
theorem B13945405 : Blo 1016603 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B3722831 : Blo 1016603 3722831 := bstep (se 1 (by rfl) ⟨2792123, by rfl⟩ : syracuseStep 3722831 = 5584247) B5584247
theorem B2510975 : Blo 1016603 2510975 := bstep (se 1 (by rfl) ⟨1883231, by rfl⟩ : syracuseStep 2510975 = 3766463) B3766463
theorem B1528487 : Blo 1016603 1528487 := bstep (se 1 (by rfl) ⟨1146365, by rfl⟩ : syracuseStep 1528487 = 2292731) B2292731
theorem B1528559 : Blo 1016603 1528559 := bstep (se 1 (by rfl) ⟨1146419, by rfl⟩ : syracuseStep 1528559 = 2292839) B2292839
theorem B1529711 : Blo 1016603 1529711 := bstep (se 1 (by rfl) ⟨1147283, by rfl⟩ : syracuseStep 1529711 = 2294567) B2294567
theorem B10445507 : Blo 1016603 10445507 := bstep (se 1 (by rfl) ⟨7834130, by rfl⟩ : syracuseStep 10445507 = 15668261) B15668261
theorem B1958825 : Blo 1016603 1958825 := bstep (se 2 (by rfl) ⟨734559, by rfl⟩ : syracuseStep 1958825 = 1469119) B1469119
theorem B2320255 : Blo 1016603 2320255 := bstep (se 1 (by rfl) ⟨1740191, by rfl⟩ : syracuseStep 2320255 = 3480383) B3480383
theorem B3435263 : Blo 1016603 3435263 := bstep (se 1 (by rfl) ⟨2576447, by rfl⟩ : syracuseStep 3435263 = 5152895) B5152895
theorem B2288807 : Blo 1016603 2288807 := bstep (se 1 (by rfl) ⟨1716605, by rfl⟩ : syracuseStep 2288807 = 3433211) B3433211
theorem B8252713 : Blo 1016603 8252713 := bstep (se 2 (by rfl) ⟨3094767, by rfl⟩ : syracuseStep 8252713 = 6189535) B6189535
theorem B3665567 : Blo 1016603 3665567 := bstep (se 1 (by rfl) ⟨2749175, by rfl⟩ : syracuseStep 3665567 = 5498351) B5498351
theorem B1634023 : Blo 1016603 1634023 := bstep (se 1 (by rfl) ⟨1225517, by rfl⟩ : syracuseStep 1634023 = 2451035) B2451035
theorem B8810527 : Blo 1016603 8810527 := bstep (se 1 (by rfl) ⟨6607895, by rfl⟩ : syracuseStep 8810527 = 13215791) B13215791
theorem B2289887 : Blo 1016603 2289887 := bstep (se 1 (by rfl) ⟨1717415, by rfl⟩ : syracuseStep 2289887 = 3434831) B3434831
theorem B1016935 : Blo 1016603 1016935 := bstep (se 1 (by rfl) ⟨762701, by rfl⟩ : syracuseStep 1016935 = 1525403) B1525403
theorem B2295863 : Blo 1016603 2295863 := bstep (se 1 (by rfl) ⟨1721897, by rfl⟩ : syracuseStep 2295863 = 3443795) B3443795
theorem B2296223 : Blo 1016603 2296223 := bstep (se 1 (by rfl) ⟨1722167, by rfl⟩ : syracuseStep 2296223 = 3444335) B3444335
theorem B1018991 : Blo 1016603 1018991 := bstep (se 1 (by rfl) ⟨764243, by rfl⟩ : syracuseStep 1018991 = 1528487) B1528487
theorem B1019039 : Blo 1016603 1019039 := bstep (se 1 (by rfl) ⟨764279, by rfl⟩ : syracuseStep 1019039 = 1528559) B1528559
theorem B1019807 : Blo 1016603 1019807 := bstep (se 1 (by rfl) ⟨764855, by rfl⟩ : syracuseStep 1019807 = 1529711) B1529711
theorem B6693857 : Blo 1016603 6693857 := bstep (se 2 (by rfl) ⟨2510196, by rfl⟩ : syracuseStep 6693857 = 5020393) B5020393
theorem B6695933 : Blo 1016603 6695933 := bstep (se 3 (by rfl) ⟨1255487, by rfl⟩ : syracuseStep 6695933 = 2510975) B2510975
theorem B3093673 : Blo 1016603 3093673 := bstep (se 2 (by rfl) ⟨1160127, by rfl⟩ : syracuseStep 3093673 = 2320255) B2320255
theorem B18593873 : Blo 1016603 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B2178697 : Blo 1016603 2178697 := bstep (se 2 (by rfl) ⟨817011, by rfl⟩ : syracuseStep 2178697 = 1634023) B1634023
theorem B11747369 : Blo 1016603 11747369 := bstep (se 2 (by rfl) ⟨4405263, by rfl⟩ : syracuseStep 11747369 = 8810527) B8810527
theorem B6963671 : Blo 1016603 6963671 := bstep (se 1 (by rfl) ⟨5222753, by rfl⟩ : syracuseStep 6963671 = 10445507) B10445507
theorem B1525871 : Blo 1016603 1525871 := bstep (se 1 (by rfl) ⟨1144403, by rfl⟩ : syracuseStep 1525871 = 2288807) B2288807
theorem B2443711 : Blo 1016603 2443711 := bstep (se 1 (by rfl) ⟨1832783, by rfl⟩ : syracuseStep 2443711 = 3665567) B3665567
theorem B1526591 : Blo 1016603 1526591 := bstep (se 1 (by rfl) ⟨1144943, by rfl⟩ : syracuseStep 1526591 = 2289887) B2289887
theorem B1530107 : Blo 1016603 1530107 := bstep (se 1 (by rfl) ⟨1147580, by rfl⟩ : syracuseStep 1530107 = 2295161) B2295161
theorem B2481887 : Blo 1016603 2481887 := bstep (se 1 (by rfl) ⟨1861415, by rfl⟩ : syracuseStep 2481887 = 3722831) B3722831
theorem B11003617 : Blo 1016603 11003617 := bstep (se 2 (by rfl) ⟨4126356, by rfl⟩ : syracuseStep 11003617 = 8252713) B8252713
theorem B3434237 : Blo 1016603 3434237 := bstep (se 3 (by rfl) ⟨643919, by rfl⟩ : syracuseStep 3434237 = 1287839) B1287839
theorem B2582887 : Blo 1016603 2582887 := bstep (se 1 (by rfl) ⟨1937165, by rfl⟩ : syracuseStep 2582887 = 3874331) B3874331
theorem B1305883 : Blo 1016603 1305883 := bstep (se 1 (by rfl) ⟨979412, by rfl⟩ : syracuseStep 1305883 = 1958825) B1958825
theorem B3436991 : Blo 1016603 3436991 := bstep (se 1 (by rfl) ⟨2577743, by rfl⟩ : syracuseStep 3436991 = 5155487) B5155487
theorem B2290175 : Blo 1016603 2290175 := bstep (se 1 (by rfl) ⟨1717631, by rfl⟩ : syracuseStep 2290175 = 3435263) B3435263
theorem B1930567 : Blo 1016603 1930567 := bstep (se 1 (by rfl) ⟨1447925, by rfl⟩ : syracuseStep 1930567 = 2895851) B2895851
theorem B23559083 : Blo 1016603 23559083 := bstep (se 1 (by rfl) ⟨17669312, by rfl⟩ : syracuseStep 23559083 = 35338625) B35338625
theorem B1146523 : Blo 1016603 1146523 := bstep (se 1 (by rfl) ⟨859892, by rfl⟩ : syracuseStep 1146523 = 1719785) B1719785
theorem B7831579 : Blo 1016603 7831579 := bstep (se 1 (by rfl) ⟨5873684, by rfl⟩ : syracuseStep 7831579 = 11747369) B11747369
theorem B1017247 : Blo 1016603 1017247 := bstep (se 1 (by rfl) ⟨762935, by rfl⟩ : syracuseStep 1017247 = 1525871) B1525871
theorem B1017727 : Blo 1016603 1017727 := bstep (se 1 (by rfl) ⟨763295, by rfl⟩ : syracuseStep 1017727 = 1526591) B1526591
theorem B3443849 : Blo 1016603 3443849 := bstep (se 2 (by rfl) ⟨1291443, by rfl⟩ : syracuseStep 3443849 = 2582887) B2582887
theorem B1020071 : Blo 1016603 1020071 := bstep (se 1 (by rfl) ⟨765053, by rfl⟩ : syracuseStep 1020071 = 1530107) B1530107
theorem B1741177 : Blo 1016603 1741177 := bstep (se 2 (by rfl) ⟨652941, by rfl⟩ : syracuseStep 1741177 = 1305883) B1305883
theorem B4462571 : Blo 1016603 4462571 := bstep (se 1 (by rfl) ⟨3346928, by rfl⟩ : syracuseStep 4462571 = 6693857) B6693857
theorem B12395915 : Blo 1016603 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B15706055 : Blo 1016603 15706055 := bstep (se 1 (by rfl) ⟨11779541, by rfl⟩ : syracuseStep 15706055 = 23559083) B23559083
theorem B3258281 : Blo 1016603 3258281 := bstep (se 2 (by rfl) ⟨1221855, by rfl⟩ : syracuseStep 3258281 = 2443711) B2443711
theorem B1654591 : Blo 1016603 1654591 := bstep (se 1 (by rfl) ⟨1240943, by rfl⟩ : syracuseStep 1654591 = 2481887) B2481887
theorem B2574089 : Blo 1016603 2574089 := bstep (se 2 (by rfl) ⟨965283, by rfl⟩ : syracuseStep 2574089 = 1930567) B1930567
theorem B1526783 : Blo 1016603 1526783 := bstep (se 1 (by rfl) ⟨1145087, by rfl⟩ : syracuseStep 1526783 = 2290175) B2290175
theorem B2904929 : Blo 1016603 2904929 := bstep (se 2 (by rfl) ⟨1089348, by rfl⟩ : syracuseStep 2904929 = 2178697) B2178697
theorem B1528697 : Blo 1016603 1528697 := bstep (se 2 (by rfl) ⟨573261, by rfl⟩ : syracuseStep 1528697 = 1146523) B1146523
theorem B4642447 : Blo 1016603 4642447 := bstep (se 1 (by rfl) ⟨3481835, by rfl⟩ : syracuseStep 4642447 = 6963671) B6963671
theorem B1530575 : Blo 1016603 1530575 := bstep (se 1 (by rfl) ⟨1147931, by rfl⟩ : syracuseStep 1530575 = 2295863) B2295863
theorem B1530815 : Blo 1016603 1530815 := bstep (se 1 (by rfl) ⟨1148111, by rfl⟩ : syracuseStep 1530815 = 2296223) B2296223
theorem B14671489 : Blo 1016603 14671489 := bstep (se 2 (by rfl) ⟨5501808, by rfl⟩ : syracuseStep 14671489 = 11003617) B11003617
theorem B2289491 : Blo 1016603 2289491 := bstep (se 1 (by rfl) ⟨1717118, by rfl⟩ : syracuseStep 2289491 = 3434237) B3434237
theorem B4124897 : Blo 1016603 4124897 := bstep (se 2 (by rfl) ⟨1546836, by rfl⟩ : syracuseStep 4124897 = 3093673) B3093673
theorem B17855821 : Blo 1016603 17855821 := bstep (se 3 (by rfl) ⟨3347966, by rfl⟩ : syracuseStep 17855821 = 6695933) B6695933
theorem B2291327 : Blo 1016603 2291327 := bstep (se 1 (by rfl) ⟨1718495, by rfl⟩ : syracuseStep 2291327 = 3436991) B3436991
theorem B1017855 : Blo 1016603 1017855 := bstep (se 1 (by rfl) ⟨763391, by rfl⟩ : syracuseStep 1017855 = 1526783) B1526783
theorem B2295899 : Blo 1016603 2295899 := bstep (se 1 (by rfl) ⟨1721924, by rfl⟩ : syracuseStep 2295899 = 3443849) B3443849
theorem B1936619 : Blo 1016603 1936619 := bstep (se 1 (by rfl) ⟨1452464, by rfl⟩ : syracuseStep 1936619 = 2904929) B2904929
theorem B1019131 : Blo 1016603 1019131 := bstep (se 1 (by rfl) ⟨764348, by rfl⟩ : syracuseStep 1019131 = 1528697) B1528697
theorem B1020383 : Blo 1016603 1020383 := bstep (se 1 (by rfl) ⟨765287, by rfl⟩ : syracuseStep 1020383 = 1530575) B1530575
theorem B1020543 : Blo 1016603 1020543 := bstep (se 1 (by rfl) ⟨765407, by rfl⟩ : syracuseStep 1020543 = 1530815) B1530815
theorem B11900189 : Blo 1016603 11900189 := bstep (se 3 (by rfl) ⟨2231285, by rfl⟩ : syracuseStep 11900189 = 4462571) B4462571
theorem B8263943 : Blo 1016603 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B95231045 : Blo 1016603 95231045 := bstep (se 4 (by rfl) ⟨8927910, by rfl⟩ : syracuseStep 95231045 = 17855821) B17855821
theorem B2172187 : Blo 1016603 2172187 := bstep (se 1 (by rfl) ⟨1629140, by rfl⟩ : syracuseStep 2172187 = 3258281) B3258281
theorem B2206121 : Blo 1016603 2206121 := bstep (se 2 (by rfl) ⟨827295, by rfl⟩ : syracuseStep 2206121 = 1654591) B1654591
theorem B1716059 : Blo 1016603 1716059 := bstep (se 1 (by rfl) ⟨1287044, by rfl⟩ : syracuseStep 1716059 = 2574089) B2574089
theorem B10470703 : Blo 1016603 10470703 := bstep (se 1 (by rfl) ⟨7853027, by rfl⟩ : syracuseStep 10470703 = 15706055) B15706055
theorem B1526327 : Blo 1016603 1526327 := bstep (se 1 (by rfl) ⟨1144745, by rfl⟩ : syracuseStep 1526327 = 2289491) B2289491
theorem B1527551 : Blo 1016603 1527551 := bstep (se 1 (by rfl) ⟨1145663, by rfl⟩ : syracuseStep 1527551 = 2291327) B2291327
theorem B10442105 : Blo 1016603 10442105 := bstep (se 2 (by rfl) ⟨3915789, by rfl⟩ : syracuseStep 10442105 = 7831579) B7831579
theorem B2321569 : Blo 1016603 2321569 := bstep (se 2 (by rfl) ⟨870588, by rfl⟩ : syracuseStep 2321569 = 1741177) B1741177
theorem B6189929 : Blo 1016603 6189929 := bstep (se 2 (by rfl) ⟨2321223, by rfl⟩ : syracuseStep 6189929 = 4642447) B4642447
theorem B2749931 : Blo 1016603 2749931 := bstep (se 1 (by rfl) ⟨2062448, by rfl⟩ : syracuseStep 2749931 = 4124897) B4124897
theorem B19561985 : Blo 1016603 19561985 := bstep (se 2 (by rfl) ⟨7335744, by rfl⟩ : syracuseStep 19561985 = 14671489) B14671489
theorem B1017551 : Blo 1016603 1017551 := bstep (se 1 (by rfl) ⟨763163, by rfl⟩ : syracuseStep 1017551 = 1526327) B1526327
theorem B13960937 : Blo 1016603 13960937 := bstep (se 2 (by rfl) ⟨5235351, by rfl⟩ : syracuseStep 13960937 = 10470703) B10470703
theorem B1018367 : Blo 1016603 1018367 := bstep (se 1 (by rfl) ⟨763775, by rfl⟩ : syracuseStep 1018367 = 1527551) B1527551
theorem B7933459 : Blo 1016603 7933459 := bstep (se 1 (by rfl) ⟨5950094, by rfl⟩ : syracuseStep 7933459 = 11900189) B11900189
theorem B5509295 : Blo 1016603 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B2896249 : Blo 1016603 2896249 := bstep (se 2 (by rfl) ⟨1086093, by rfl⟩ : syracuseStep 2896249 = 2172187) B2172187
theorem B1291079 : Blo 1016603 1291079 := bstep (se 1 (by rfl) ⟨968309, by rfl⟩ : syracuseStep 1291079 = 1936619) B1936619
theorem B6961403 : Blo 1016603 6961403 := bstep (se 1 (by rfl) ⟨5221052, by rfl⟩ : syracuseStep 6961403 = 10442105) B10442105
theorem B3095425 : Blo 1016603 3095425 := bstep (se 2 (by rfl) ⟨1160784, by rfl⟩ : syracuseStep 3095425 = 2321569) B2321569
theorem B63487363 : Blo 1016603 63487363 := bstep (se 1 (by rfl) ⟨47615522, by rfl⟩ : syracuseStep 63487363 = 95231045) B95231045
theorem B5882989 : Blo 1016603 5882989 := bstep (se 3 (by rfl) ⟨1103060, by rfl⟩ : syracuseStep 5882989 = 2206121) B2206121
theorem B1530599 : Blo 1016603 1530599 := bstep (se 1 (by rfl) ⟨1147949, by rfl⟩ : syracuseStep 1530599 = 2295899) B2295899
theorem B1144039 : Blo 1016603 1144039 := bstep (se 1 (by rfl) ⟨858029, by rfl⟩ : syracuseStep 1144039 = 1716059) B1716059
theorem B4126619 : Blo 1016603 4126619 := bstep (se 1 (by rfl) ⟨3094964, by rfl⟩ : syracuseStep 4126619 = 6189929) B6189929
theorem B1833287 : Blo 1016603 1833287 := bstep (se 1 (by rfl) ⟨1374965, by rfl⟩ : syracuseStep 1833287 = 2749931) B2749931
theorem B13041323 : Blo 1016603 13041323 := bstep (se 1 (by rfl) ⟨9780992, by rfl⟩ : syracuseStep 13041323 = 19561985) B19561985
theorem B3442877 : Blo 1016603 3442877 := bstep (se 3 (by rfl) ⟨645539, by rfl⟩ : syracuseStep 3442877 = 1291079) B1291079
theorem B3672863 : Blo 1016603 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B1020399 : Blo 1016603 1020399 := bstep (se 1 (by rfl) ⟨765299, by rfl⟩ : syracuseStep 1020399 = 1530599) B1530599
theorem B37229165 : Blo 1016603 37229165 := bstep (se 3 (by rfl) ⟨6980468, by rfl⟩ : syracuseStep 37229165 = 13960937) B13960937
theorem B4888765 : Blo 1016603 4888765 := bstep (se 3 (by rfl) ⟨916643, by rfl⟩ : syracuseStep 4888765 = 1833287) B1833287
theorem B84649817 : Blo 1016603 84649817 := bstep (se 2 (by rfl) ⟨31743681, by rfl⟩ : syracuseStep 84649817 = 63487363) B63487363
theorem B8694215 : Blo 1016603 8694215 := bstep (se 1 (by rfl) ⟨6520661, by rfl⟩ : syracuseStep 8694215 = 13041323) B13041323
theorem B7843985 : Blo 1016603 7843985 := bstep (se 2 (by rfl) ⟨2941494, by rfl⟩ : syracuseStep 7843985 = 5882989) B5882989
theorem B1525385 : Blo 1016603 1525385 := bstep (se 2 (by rfl) ⟨572019, by rfl⟩ : syracuseStep 1525385 = 1144039) B1144039
theorem B4640935 : Blo 1016603 4640935 := bstep (se 1 (by rfl) ⟨3480701, by rfl⟩ : syracuseStep 4640935 = 6961403) B6961403
theorem B16508933 : Blo 1016603 16508933 := bstep (se 4 (by rfl) ⟨1547712, by rfl⟩ : syracuseStep 16508933 = 3095425) B3095425
theorem B10577945 : Blo 1016603 10577945 := bstep (se 2 (by rfl) ⟨3966729, by rfl⟩ : syracuseStep 10577945 = 7933459) B7933459
theorem B3861665 : Blo 1016603 3861665 := bstep (se 2 (by rfl) ⟨1448124, by rfl⟩ : syracuseStep 3861665 = 2896249) B2896249
theorem B2751079 : Blo 1016603 2751079 := bstep (se 1 (by rfl) ⟨2063309, by rfl⟩ : syracuseStep 2751079 = 4126619) B4126619
theorem B1016923 : Blo 1016603 1016923 := bstep (se 1 (by rfl) ⟨762692, by rfl⟩ : syracuseStep 1016923 = 1525385) B1525385
theorem B2295251 : Blo 1016603 2295251 := bstep (se 1 (by rfl) ⟨1721438, by rfl⟩ : syracuseStep 2295251 = 3442877) B3442877
theorem B7051963 : Blo 1016603 7051963 := bstep (se 1 (by rfl) ⟨5288972, by rfl⟩ : syracuseStep 7051963 = 10577945) B10577945
theorem B24819443 : Blo 1016603 24819443 := bstep (se 1 (by rfl) ⟨18614582, by rfl⟩ : syracuseStep 24819443 = 37229165) B37229165
theorem B2574443 : Blo 1016603 2574443 := bstep (se 1 (by rfl) ⟨1930832, by rfl⟩ : syracuseStep 2574443 = 3861665) B3861665
theorem B5229323 : Blo 1016603 5229323 := bstep (se 1 (by rfl) ⟨3921992, by rfl⟩ : syracuseStep 5229323 = 7843985) B7843985
theorem B26073413 : Blo 1016603 26073413 := bstep (se 4 (by rfl) ⟨2444382, by rfl⟩ : syracuseStep 26073413 = 4888765) B4888765
theorem B2448575 : Blo 1016603 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B225732845 : Blo 1016603 225732845 := bstep (se 3 (by rfl) ⟨42324908, by rfl⟩ : syracuseStep 225732845 = 84649817) B84649817
theorem B6187913 : Blo 1016603 6187913 := bstep (se 2 (by rfl) ⟨2320467, by rfl⟩ : syracuseStep 6187913 = 4640935) B4640935
theorem B11005955 : Blo 1016603 11005955 := bstep (se 1 (by rfl) ⟨8254466, by rfl⟩ : syracuseStep 11005955 = 16508933) B16508933
theorem B5796143 : Blo 1016603 5796143 := bstep (se 1 (by rfl) ⟨4347107, by rfl⟩ : syracuseStep 5796143 = 8694215) B8694215
theorem B3668105 : Blo 1016603 3668105 := bstep (se 2 (by rfl) ⟨1375539, by rfl⟩ : syracuseStep 3668105 = 2751079) B2751079
theorem B601954253 : Blo 1016603 601954253 := bstep (se 3 (by rfl) ⟨112866422, by rfl⟩ : syracuseStep 601954253 = 225732845) B225732845
theorem B1716295 : Blo 1016603 1716295 := bstep (se 1 (by rfl) ⟨1287221, by rfl⟩ : syracuseStep 1716295 = 2574443) B2574443
theorem B3486215 : Blo 1016603 3486215 := bstep (se 1 (by rfl) ⟨2614661, by rfl⟩ : syracuseStep 3486215 = 5229323) B5229323
theorem B17382275 : Blo 1016603 17382275 := bstep (se 1 (by rfl) ⟨13036706, by rfl⟩ : syracuseStep 17382275 = 26073413) B26073413
theorem B2445403 : Blo 1016603 2445403 := bstep (se 1 (by rfl) ⟨1834052, by rfl⟩ : syracuseStep 2445403 = 3668105) B3668105
theorem B1530167 : Blo 1016603 1530167 := bstep (se 1 (by rfl) ⟨1147625, by rfl⟩ : syracuseStep 1530167 = 2295251) B2295251
theorem B1632383 : Blo 1016603 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B4125275 : Blo 1016603 4125275 := bstep (se 1 (by rfl) ⟨3093956, by rfl⟩ : syracuseStep 4125275 = 6187913) B6187913
theorem B7337303 : Blo 1016603 7337303 := bstep (se 1 (by rfl) ⟨5502977, by rfl⟩ : syracuseStep 7337303 = 11005955) B11005955
theorem B3864095 : Blo 1016603 3864095 := bstep (se 1 (by rfl) ⟨2898071, by rfl⟩ : syracuseStep 3864095 = 5796143) B5796143
theorem B9402617 : Blo 1016603 9402617 := bstep (se 2 (by rfl) ⟨3525981, by rfl⟩ : syracuseStep 9402617 = 7051963) B7051963
theorem B16546295 : Blo 1016603 16546295 := bstep (se 1 (by rfl) ⟨12409721, by rfl⟩ : syracuseStep 16546295 = 24819443) B24819443
theorem B1020111 : Blo 1016603 1020111 := bstep (se 1 (by rfl) ⟨765083, by rfl⟩ : syracuseStep 1020111 = 1530167) B1530167
theorem B1088255 : Blo 1016603 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B4891535 : Blo 1016603 4891535 := bstep (se 1 (by rfl) ⟨3668651, by rfl⟩ : syracuseStep 4891535 = 7337303) B7337303
theorem B6268411 : Blo 1016603 6268411 := bstep (se 1 (by rfl) ⟨4701308, by rfl⟩ : syracuseStep 6268411 = 9402617) B9402617
theorem B3260537 : Blo 1016603 3260537 := bstep (se 2 (by rfl) ⟨1222701, by rfl⟩ : syracuseStep 3260537 = 2445403) B2445403
theorem B2576063 : Blo 1016603 2576063 := bstep (se 1 (by rfl) ⟨1932047, by rfl⟩ : syracuseStep 2576063 = 3864095) B3864095
theorem B11030863 : Blo 1016603 11030863 := bstep (se 1 (by rfl) ⟨8273147, by rfl⟩ : syracuseStep 11030863 = 16546295) B16546295
theorem B11588183 : Blo 1016603 11588183 := bstep (se 1 (by rfl) ⟨8691137, by rfl⟩ : syracuseStep 11588183 = 17382275) B17382275
theorem B401302835 : Blo 1016603 401302835 := bstep (se 1 (by rfl) ⟨300977126, by rfl⟩ : syracuseStep 401302835 = 601954253) B601954253
theorem B2288393 : Blo 1016603 2288393 := bstep (se 2 (by rfl) ⟨858147, by rfl⟩ : syracuseStep 2288393 = 1716295) B1716295
theorem B2324143 : Blo 1016603 2324143 := bstep (se 1 (by rfl) ⟨1743107, by rfl⟩ : syracuseStep 2324143 = 3486215) B3486215
theorem B2750183 : Blo 1016603 2750183 := bstep (se 1 (by rfl) ⟨2062637, by rfl⟩ : syracuseStep 2750183 = 4125275) B4125275
theorem B33431525 : Blo 1016603 33431525 := bstep (se 4 (by rfl) ⟨3134205, by rfl⟩ : syracuseStep 33431525 = 6268411) B6268411
theorem B2173691 : Blo 1016603 2173691 := bstep (se 1 (by rfl) ⟨1630268, by rfl⟩ : syracuseStep 2173691 = 3260537) B3260537
theorem B1717375 : Blo 1016603 1717375 := bstep (se 1 (by rfl) ⟨1288031, by rfl⟩ : syracuseStep 1717375 = 2576063) B2576063
theorem B3261023 : Blo 1016603 3261023 := bstep (se 1 (by rfl) ⟨2445767, by rfl⟩ : syracuseStep 3261023 = 4891535) B4891535
theorem B267535223 : Blo 1016603 267535223 := bstep (se 1 (by rfl) ⟨200651417, by rfl⟩ : syracuseStep 267535223 = 401302835) B401302835
theorem B1525595 : Blo 1016603 1525595 := bstep (se 1 (by rfl) ⟨1144196, by rfl⟩ : syracuseStep 1525595 = 2288393) B2288393
theorem B2902013 : Blo 1016603 2902013 := bstep (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) B1088255
theorem B3098857 : Blo 1016603 3098857 := bstep (se 2 (by rfl) ⟨1162071, by rfl⟩ : syracuseStep 3098857 = 2324143) B2324143
theorem B7725455 : Blo 1016603 7725455 := bstep (se 1 (by rfl) ⟨5794091, by rfl⟩ : syracuseStep 7725455 = 11588183) B11588183
theorem B14707817 : Blo 1016603 14707817 := bstep (se 2 (by rfl) ⟨5515431, by rfl⟩ : syracuseStep 14707817 = 11030863) B11030863
theorem B1833455 : Blo 1016603 1833455 := bstep (se 1 (by rfl) ⟨1375091, by rfl⟩ : syracuseStep 1833455 = 2750183) B2750183
theorem B178356815 : Blo 1016603 178356815 := bstep (se 1 (by rfl) ⟨133767611, by rfl⟩ : syracuseStep 178356815 = 267535223) B267535223
theorem B1017063 : Blo 1016603 1017063 := bstep (se 1 (by rfl) ⟨762797, by rfl⟩ : syracuseStep 1017063 = 1525595) B1525595
theorem B1934675 : Blo 1016603 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B4131809 : Blo 1016603 4131809 := bstep (se 2 (by rfl) ⟨1549428, by rfl⟩ : syracuseStep 4131809 = 3098857) B3098857
theorem B22287683 : Blo 1016603 22287683 := bstep (se 1 (by rfl) ⟨16715762, by rfl⟩ : syracuseStep 22287683 = 33431525) B33431525
theorem B5150303 : Blo 1016603 5150303 := bstep (se 1 (by rfl) ⟨3862727, by rfl⟩ : syracuseStep 5150303 = 7725455) B7725455
theorem B1449127 : Blo 1016603 1449127 := bstep (se 1 (by rfl) ⟨1086845, by rfl⟩ : syracuseStep 1449127 = 2173691) B2173691
theorem B9805211 : Blo 1016603 9805211 := bstep (se 1 (by rfl) ⟨7353908, by rfl⟩ : syracuseStep 9805211 = 14707817) B14707817
theorem B1222303 : Blo 1016603 1222303 := bstep (se 1 (by rfl) ⟨916727, by rfl⟩ : syracuseStep 1222303 = 1833455) B1833455
theorem B2174015 : Blo 1016603 2174015 := bstep (se 1 (by rfl) ⟨1630511, by rfl⟩ : syracuseStep 2174015 = 3261023) B3261023
theorem B2289833 : Blo 1016603 2289833 := bstep (se 2 (by rfl) ⟨858687, by rfl⟩ : syracuseStep 2289833 = 1717375) B1717375
theorem B2754539 : Blo 1016603 2754539 := bstep (se 1 (by rfl) ⟨2065904, by rfl⟩ : syracuseStep 2754539 = 4131809) B4131809
theorem B1449343 : Blo 1016603 1449343 := bstep (se 1 (by rfl) ⟨1087007, by rfl⟩ : syracuseStep 1449343 = 2174015) B2174015
theorem B1289783 : Blo 1016603 1289783 := bstep (se 1 (by rfl) ⟨967337, by rfl⟩ : syracuseStep 1289783 = 1934675) B1934675
theorem B6536807 : Blo 1016603 6536807 := bstep (se 1 (by rfl) ⟨4902605, by rfl⟩ : syracuseStep 6536807 = 9805211) B9805211
theorem B1526555 : Blo 1016603 1526555 := bstep (se 1 (by rfl) ⟨1144916, by rfl⟩ : syracuseStep 1526555 = 2289833) B2289833
theorem B118904543 : Blo 1016603 118904543 := bstep (se 1 (by rfl) ⟨89178407, by rfl⟩ : syracuseStep 118904543 = 178356815) B178356815
theorem B1629737 : Blo 1016603 1629737 := bstep (se 2 (by rfl) ⟨611151, by rfl⟩ : syracuseStep 1629737 = 1222303) B1222303
theorem B59433821 : Blo 1016603 59433821 := bstep (se 3 (by rfl) ⟨11143841, by rfl⟩ : syracuseStep 59433821 = 22287683) B22287683
theorem B3433535 : Blo 1016603 3433535 := bstep (se 1 (by rfl) ⟨2575151, by rfl⟩ : syracuseStep 3433535 = 5150303) B5150303
theorem B1932169 : Blo 1016603 1932169 := bstep (se 2 (by rfl) ⟨724563, by rfl⟩ : syracuseStep 1932169 = 1449127) B1449127
theorem B1836359 : Blo 1016603 1836359 := bstep (se 1 (by rfl) ⟨1377269, by rfl⟩ : syracuseStep 1836359 = 2754539) B2754539
theorem B1017703 : Blo 1016603 1017703 := bstep (se 1 (by rfl) ⟨763277, by rfl⟩ : syracuseStep 1017703 = 1526555) B1526555
theorem B79269695 : Blo 1016603 79269695 := bstep (se 1 (by rfl) ⟨59452271, by rfl⟩ : syracuseStep 79269695 = 118904543) B118904543
theorem B1086491 : Blo 1016603 1086491 := bstep (se 1 (by rfl) ⟨814868, by rfl⟩ : syracuseStep 1086491 = 1629737) B1629737
theorem B39622547 : Blo 1016603 39622547 := bstep (se 1 (by rfl) ⟨29716910, by rfl⟩ : syracuseStep 39622547 = 59433821) B59433821
theorem B2576225 : Blo 1016603 2576225 := bstep (se 2 (by rfl) ⟨966084, by rfl⟩ : syracuseStep 2576225 = 1932169) B1932169
theorem B2289023 : Blo 1016603 2289023 := bstep (se 1 (by rfl) ⟨1716767, by rfl⟩ : syracuseStep 2289023 = 3433535) B3433535
theorem B7729829 : Blo 1016603 7729829 := bstep (se 4 (by rfl) ⟨724671, by rfl⟩ : syracuseStep 7729829 = 1449343) B1449343
theorem B3439421 : Blo 1016603 3439421 := bstep (se 3 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 3439421 = 1289783) B1289783
theorem B4357871 : Blo 1016603 4357871 := bstep (se 1 (by rfl) ⟨3268403, by rfl⟩ : syracuseStep 4357871 = 6536807) B6536807
theorem B26415031 : Blo 1016603 26415031 := bstep (se 1 (by rfl) ⟨19811273, by rfl⟩ : syracuseStep 26415031 = 39622547) B39622547
theorem B5153219 : Blo 1016603 5153219 := bstep (se 1 (by rfl) ⟨3864914, by rfl⟩ : syracuseStep 5153219 = 7729829) B7729829
theorem B1224239 : Blo 1016603 1224239 := bstep (se 1 (by rfl) ⟨918179, by rfl⟩ : syracuseStep 1224239 = 1836359) B1836359
theorem B1717483 : Blo 1016603 1717483 := bstep (se 1 (by rfl) ⟨1288112, by rfl⟩ : syracuseStep 1717483 = 2576225) B2576225
theorem B2897309 : Blo 1016603 2897309 := bstep (se 3 (by rfl) ⟨543245, by rfl⟩ : syracuseStep 2897309 = 1086491) B1086491
theorem B1526015 : Blo 1016603 1526015 := bstep (se 1 (by rfl) ⟨1144511, by rfl⟩ : syracuseStep 1526015 = 2289023) B2289023
theorem B2905247 : Blo 1016603 2905247 := bstep (se 1 (by rfl) ⟨2178935, by rfl⟩ : syracuseStep 2905247 = 4357871) B4357871
theorem B52846463 : Blo 1016603 52846463 := bstep (se 1 (by rfl) ⟨39634847, by rfl⟩ : syracuseStep 52846463 = 79269695) B79269695
theorem B2292947 : Blo 1016603 2292947 := bstep (se 1 (by rfl) ⟨1719710, by rfl⟩ : syracuseStep 2292947 = 3439421) B3439421
theorem B1017343 : Blo 1016603 1017343 := bstep (se 1 (by rfl) ⟨763007, by rfl⟩ : syracuseStep 1017343 = 1526015) B1526015
theorem B7747325 : Blo 1016603 7747325 := bstep (se 3 (by rfl) ⟨1452623, by rfl⟩ : syracuseStep 7747325 = 2905247) B2905247
theorem B3264637 : Blo 1016603 3264637 := bstep (se 3 (by rfl) ⟨612119, by rfl⟩ : syracuseStep 3264637 = 1224239) B1224239
theorem B1528631 : Blo 1016603 1528631 := bstep (se 1 (by rfl) ⟨1146473, by rfl⟩ : syracuseStep 1528631 = 2292947) B2292947
theorem B140923901 : Blo 1016603 140923901 := bstep (se 3 (by rfl) ⟨26423231, by rfl⟩ : syracuseStep 140923901 = 52846463) B52846463
theorem B35220041 : Blo 1016603 35220041 := bstep (se 2 (by rfl) ⟨13207515, by rfl⟩ : syracuseStep 35220041 = 26415031) B26415031
theorem B3435479 : Blo 1016603 3435479 := bstep (se 1 (by rfl) ⟨2576609, by rfl⟩ : syracuseStep 3435479 = 5153219) B5153219
theorem B2289977 : Blo 1016603 2289977 := bstep (se 2 (by rfl) ⟨858741, by rfl⟩ : syracuseStep 2289977 = 1717483) B1717483
theorem B1931539 : Blo 1016603 1931539 := bstep (se 1 (by rfl) ⟨1448654, by rfl⟩ : syracuseStep 1931539 = 2897309) B2897309
theorem B1019087 : Blo 1016603 1019087 := bstep (se 1 (by rfl) ⟨764315, by rfl⟩ : syracuseStep 1019087 = 1528631) B1528631
theorem B93949267 : Blo 1016603 93949267 := bstep (se 1 (by rfl) ⟨70461950, by rfl⟩ : syracuseStep 93949267 = 140923901) B140923901
theorem B23480027 : Blo 1016603 23480027 := bstep (se 1 (by rfl) ⟨17610020, by rfl⟩ : syracuseStep 23480027 = 35220041) B35220041
theorem B1526651 : Blo 1016603 1526651 := bstep (se 1 (by rfl) ⟨1144988, by rfl⟩ : syracuseStep 1526651 = 2289977) B2289977
theorem B2575385 : Blo 1016603 2575385 := bstep (se 2 (by rfl) ⟨965769, by rfl⟩ : syracuseStep 2575385 = 1931539) B1931539
theorem B5164883 : Blo 1016603 5164883 := bstep (se 1 (by rfl) ⟨3873662, by rfl⟩ : syracuseStep 5164883 = 7747325) B7747325
theorem B4352849 : Blo 1016603 4352849 := bstep (se 2 (by rfl) ⟨1632318, by rfl⟩ : syracuseStep 4352849 = 3264637) B3264637
theorem B2290319 : Blo 1016603 2290319 := bstep (se 1 (by rfl) ⟨1717739, by rfl⟩ : syracuseStep 2290319 = 3435479) B3435479
theorem B1017767 : Blo 1016603 1017767 := bstep (se 1 (by rfl) ⟨763325, by rfl⟩ : syracuseStep 1017767 = 1526651) B1526651
theorem B3443255 : Blo 1016603 3443255 := bstep (se 1 (by rfl) ⟨2582441, by rfl⟩ : syracuseStep 3443255 = 5164883) B5164883
theorem B1716923 : Blo 1016603 1716923 := bstep (se 1 (by rfl) ⟨1287692, by rfl⟩ : syracuseStep 1716923 = 2575385) B2575385
theorem B2901899 : Blo 1016603 2901899 := bstep (se 1 (by rfl) ⟨2176424, by rfl⟩ : syracuseStep 2901899 = 4352849) B4352849
theorem B1526879 : Blo 1016603 1526879 := bstep (se 1 (by rfl) ⟨1145159, by rfl⟩ : syracuseStep 1526879 = 2290319) B2290319
theorem B15653351 : Blo 1016603 15653351 := bstep (se 1 (by rfl) ⟨11740013, by rfl⟩ : syracuseStep 15653351 = 23480027) B23480027
theorem B125265689 : Blo 1016603 125265689 := bstep (se 2 (by rfl) ⟨46974633, by rfl⟩ : syracuseStep 125265689 = 93949267) B93949267
theorem B1934599 : Blo 1016603 1934599 := bstep (se 1 (by rfl) ⟨1450949, by rfl⟩ : syracuseStep 1934599 = 2901899) B2901899
theorem B2295503 : Blo 1016603 2295503 := bstep (se 1 (by rfl) ⟨1721627, by rfl⟩ : syracuseStep 2295503 = 3443255) B3443255
theorem B1017919 : Blo 1016603 1017919 := bstep (se 1 (by rfl) ⟨763439, by rfl⟩ : syracuseStep 1017919 = 1526879) B1526879
theorem B10435567 : Blo 1016603 10435567 := bstep (se 1 (by rfl) ⟨7826675, by rfl⟩ : syracuseStep 10435567 = 15653351) B15653351
theorem B83510459 : Blo 1016603 83510459 := bstep (se 1 (by rfl) ⟨62632844, by rfl⟩ : syracuseStep 83510459 = 125265689) B125265689
theorem B1144615 : Blo 1016603 1144615 := bstep (se 1 (by rfl) ⟨858461, by rfl⟩ : syracuseStep 1144615 = 1716923) B1716923
theorem B55673639 : Blo 1016603 55673639 := bstep (se 1 (by rfl) ⟨41755229, by rfl⟩ : syracuseStep 55673639 = 83510459) B83510459
theorem B1526153 : Blo 1016603 1526153 := bstep (se 2 (by rfl) ⟨572307, by rfl⟩ : syracuseStep 1526153 = 1144615) B1144615
theorem B13914089 : Blo 1016603 13914089 := bstep (se 2 (by rfl) ⟨5217783, by rfl⟩ : syracuseStep 13914089 = 10435567) B10435567
theorem B1530335 : Blo 1016603 1530335 := bstep (se 1 (by rfl) ⟨1147751, by rfl⟩ : syracuseStep 1530335 = 2295503) B2295503
theorem B2579465 : Blo 1016603 2579465 := bstep (se 2 (by rfl) ⟨967299, by rfl⟩ : syracuseStep 2579465 = 1934599) B1934599
theorem B1017435 : Blo 1016603 1017435 := bstep (se 1 (by rfl) ⟨763076, by rfl⟩ : syracuseStep 1017435 = 1526153) B1526153
theorem B9276059 : Blo 1016603 9276059 := bstep (se 1 (by rfl) ⟨6957044, by rfl⟩ : syracuseStep 9276059 = 13914089) B13914089
theorem B1020223 : Blo 1016603 1020223 := bstep (se 1 (by rfl) ⟨765167, by rfl⟩ : syracuseStep 1020223 = 1530335) B1530335
theorem B1719643 : Blo 1016603 1719643 := bstep (se 1 (by rfl) ⟨1289732, by rfl⟩ : syracuseStep 1719643 = 2579465) B2579465
theorem B37115759 : Blo 1016603 37115759 := bstep (se 1 (by rfl) ⟨27836819, by rfl⟩ : syracuseStep 37115759 = 55673639) B55673639
theorem B24743839 : Blo 1016603 24743839 := bstep (se 1 (by rfl) ⟨18557879, by rfl⟩ : syracuseStep 24743839 = 37115759) B37115759
theorem B6184039 : Blo 1016603 6184039 := bstep (se 1 (by rfl) ⟨4638029, by rfl⟩ : syracuseStep 6184039 = 9276059) B9276059
theorem B2292857 : Blo 1016603 2292857 := bstep (se 2 (by rfl) ⟨859821, by rfl⟩ : syracuseStep 2292857 = 1719643) B1719643
theorem B8245385 : Blo 1016603 8245385 := bstep (se 2 (by rfl) ⟨3092019, by rfl⟩ : syracuseStep 8245385 = 6184039) B6184039
theorem B1528571 : Blo 1016603 1528571 := bstep (se 1 (by rfl) ⟨1146428, by rfl⟩ : syracuseStep 1528571 = 2292857) B2292857
theorem B32991785 : Blo 1016603 32991785 := bstep (se 2 (by rfl) ⟨12371919, by rfl⟩ : syracuseStep 32991785 = 24743839) B24743839
theorem B1019047 : Blo 1016603 1019047 := bstep (se 1 (by rfl) ⟨764285, by rfl⟩ : syracuseStep 1019047 = 1528571) B1528571
theorem B21994523 : Blo 1016603 21994523 := bstep (se 1 (by rfl) ⟨16495892, by rfl⟩ : syracuseStep 21994523 = 32991785) B32991785
theorem B5496923 : Blo 1016603 5496923 := bstep (se 1 (by rfl) ⟨4122692, by rfl⟩ : syracuseStep 5496923 = 8245385) B8245385
theorem B14663015 : Blo 1016603 14663015 := bstep (se 1 (by rfl) ⟨10997261, by rfl⟩ : syracuseStep 14663015 = 21994523) B21994523
theorem B3664615 : Blo 1016603 3664615 := bstep (se 1 (by rfl) ⟨2748461, by rfl⟩ : syracuseStep 3664615 = 5496923) B5496923
theorem B4886153 : Blo 1016603 4886153 := bstep (se 2 (by rfl) ⟨1832307, by rfl⟩ : syracuseStep 4886153 = 3664615) B3664615
theorem B9775343 : Blo 1016603 9775343 := bstep (se 1 (by rfl) ⟨7331507, by rfl⟩ : syracuseStep 9775343 = 14663015) B14663015
theorem B3257435 : Blo 1016603 3257435 := bstep (se 1 (by rfl) ⟨2443076, by rfl⟩ : syracuseStep 3257435 = 4886153) B4886153
theorem B6516895 : Blo 1016603 6516895 := bstep (se 1 (by rfl) ⟨4887671, by rfl⟩ : syracuseStep 6516895 = 9775343) B9775343
theorem B8689193 : Blo 1016603 8689193 := bstep (se 2 (by rfl) ⟨3258447, by rfl⟩ : syracuseStep 8689193 = 6516895) B6516895
theorem B2171623 : Blo 1016603 2171623 := bstep (se 1 (by rfl) ⟨1628717, by rfl⟩ : syracuseStep 2171623 = 3257435) B3257435
theorem B2895497 : Blo 1016603 2895497 := bstep (se 2 (by rfl) ⟨1085811, by rfl⟩ : syracuseStep 2895497 = 2171623) B2171623
theorem B5792795 : Blo 1016603 5792795 := bstep (se 1 (by rfl) ⟨4344596, by rfl⟩ : syracuseStep 5792795 = 8689193) B8689193
theorem B3861863 : Blo 1016603 3861863 := bstep (se 1 (by rfl) ⟨2896397, by rfl⟩ : syracuseStep 3861863 = 5792795) B5792795
theorem B1930331 : Blo 1016603 1930331 := bstep (se 1 (by rfl) ⟨1447748, by rfl⟩ : syracuseStep 1930331 = 2895497) B2895497
theorem B5147549 : Blo 1016603 5147549 := bstep (se 3 (by rfl) ⟨965165, by rfl⟩ : syracuseStep 5147549 = 1930331) B1930331
theorem B2574575 : Blo 1016603 2574575 := bstep (se 1 (by rfl) ⟨1930931, by rfl⟩ : syracuseStep 2574575 = 3861863) B3861863
theorem B1716383 : Blo 1016603 1716383 := bstep (se 1 (by rfl) ⟨1287287, by rfl⟩ : syracuseStep 1716383 = 2574575) B2574575
theorem B3431699 : Blo 1016603 3431699 := bstep (se 1 (by rfl) ⟨2573774, by rfl⟩ : syracuseStep 3431699 = 5147549) B5147549
theorem B2287799 : Blo 1016603 2287799 := bstep (se 1 (by rfl) ⟨1715849, by rfl⟩ : syracuseStep 2287799 = 3431699) B3431699
theorem B1144255 : Blo 1016603 1144255 := bstep (se 1 (by rfl) ⟨858191, by rfl⟩ : syracuseStep 1144255 = 1716383) B1716383
theorem B1525199 : Blo 1016603 1525199 := bstep (se 1 (by rfl) ⟨1143899, by rfl⟩ : syracuseStep 1525199 = 2287799) B2287799
theorem B1525673 : Blo 1016603 1525673 := bstep (se 2 (by rfl) ⟨572127, by rfl⟩ : syracuseStep 1525673 = 1144255) B1144255
theorem B1016799 : Blo 1016603 1016799 := bstep (se 1 (by rfl) ⟨762599, by rfl⟩ : syracuseStep 1016799 = 1525199) B1525199
theorem B1017115 : Blo 1016603 1017115 := bstep (se 1 (by rfl) ⟨762836, by rfl⟩ : syracuseStep 1017115 = 1525673) B1525673

theorem C0 (j : ℕ) (h1 : 254150 ≤ j) (h2 : j ≤ 254849) : Blo 1016603 (4 * j + 3) := by
  interval_cases j
  · exact B1016603
  · exact B1016607
  · exact B1016611
  · exact B1016615
  · exact B1016619
  · exact B1016623
  · exact B1016627
  · exact B1016631
  · exact B1016635
  · exact B1016639
  · exact B1016643
  · exact B1016647
  · exact B1016651
  · exact B1016655
  · exact B1016659
  · exact B1016663
  · exact B1016667
  · exact B1016671
  · exact B1016675
  · exact B1016679
  · exact B1016683
  · exact B1016687
  · exact B1016691
  · exact B1016695
  · exact B1016699
  · exact B1016703
  · exact B1016707
  · exact B1016711
  · exact B1016715
  · exact B1016719
  · exact B1016723
  · exact B1016727
  · exact B1016731
  · exact B1016735
  · exact B1016739
  · exact B1016743
  · exact B1016747
  · exact B1016751
  · exact B1016755
  · exact B1016759
  · exact B1016763
  · exact B1016767
  · exact B1016771
  · exact B1016775
  · exact B1016779
  · exact B1016783
  · exact B1016787
  · exact B1016791
  · exact B1016795
  · exact B1016799
  · exact B1016803
  · exact B1016807
  · exact B1016811
  · exact B1016815
  · exact B1016819
  · exact B1016823
  · exact B1016827
  · exact B1016831
  · exact B1016835
  · exact B1016839
  · exact B1016843
  · exact B1016847
  · exact B1016851
  · exact B1016855
  · exact B1016859
  · exact B1016863
  · exact B1016867
  · exact B1016871
  · exact B1016875
  · exact B1016879
  · exact B1016883
  · exact B1016887
  · exact B1016891
  · exact B1016895
  · exact B1016899
  · exact B1016903
  · exact B1016907
  · exact B1016911
  · exact B1016915
  · exact B1016919
  · exact B1016923
  · exact B1016927
  · exact B1016931
  · exact B1016935
  · exact B1016939
  · exact B1016943
  · exact B1016947
  · exact B1016951
  · exact B1016955
  · exact B1016959
  · exact B1016963
  · exact B1016967
  · exact B1016971
  · exact B1016975
  · exact B1016979
  · exact B1016983
  · exact B1016987
  · exact B1016991
  · exact B1016995
  · exact B1016999
  · exact B1017003
  · exact B1017007
  · exact B1017011
  · exact B1017015
  · exact B1017019
  · exact B1017023
  · exact B1017027
  · exact B1017031
  · exact B1017035
  · exact B1017039
  · exact B1017043
  · exact B1017047
  · exact B1017051
  · exact B1017055
  · exact B1017059
  · exact B1017063
  · exact B1017067
  · exact B1017071
  · exact B1017075
  · exact B1017079
  · exact B1017083
  · exact B1017087
  · exact B1017091
  · exact B1017095
  · exact B1017099
  · exact B1017103
  · exact B1017107
  · exact B1017111
  · exact B1017115
  · exact B1017119
  · exact B1017123
  · exact B1017127
  · exact B1017131
  · exact B1017135
  · exact B1017139
  · exact B1017143
  · exact B1017147
  · exact B1017151
  · exact B1017155
  · exact B1017159
  · exact B1017163
  · exact B1017167
  · exact B1017171
  · exact B1017175
  · exact B1017179
  · exact B1017183
  · exact B1017187
  · exact B1017191
  · exact B1017195
  · exact B1017199
  · exact B1017203
  · exact B1017207
  · exact B1017211
  · exact B1017215
  · exact B1017219
  · exact B1017223
  · exact B1017227
  · exact B1017231
  · exact B1017235
  · exact B1017239
  · exact B1017243
  · exact B1017247
  · exact B1017251
  · exact B1017255
  · exact B1017259
  · exact B1017263
  · exact B1017267
  · exact B1017271
  · exact B1017275
  · exact B1017279
  · exact B1017283
  · exact B1017287
  · exact B1017291
  · exact B1017295
  · exact B1017299
  · exact B1017303
  · exact B1017307
  · exact B1017311
  · exact B1017315
  · exact B1017319
  · exact B1017323
  · exact B1017327
  · exact B1017331
  · exact B1017335
  · exact B1017339
  · exact B1017343
  · exact B1017347
  · exact B1017351
  · exact B1017355
  · exact B1017359
  · exact B1017363
  · exact B1017367
  · exact B1017371
  · exact B1017375
  · exact B1017379
  · exact B1017383
  · exact B1017387
  · exact B1017391
  · exact B1017395
  · exact B1017399
  · exact B1017403
  · exact B1017407
  · exact B1017411
  · exact B1017415
  · exact B1017419
  · exact B1017423
  · exact B1017427
  · exact B1017431
  · exact B1017435
  · exact B1017439
  · exact B1017443
  · exact B1017447
  · exact B1017451
  · exact B1017455
  · exact B1017459
  · exact B1017463
  · exact B1017467
  · exact B1017471
  · exact B1017475
  · exact B1017479
  · exact B1017483
  · exact B1017487
  · exact B1017491
  · exact B1017495
  · exact B1017499
  · exact B1017503
  · exact B1017507
  · exact B1017511
  · exact B1017515
  · exact B1017519
  · exact B1017523
  · exact B1017527
  · exact B1017531
  · exact B1017535
  · exact B1017539
  · exact B1017543
  · exact B1017547
  · exact B1017551
  · exact B1017555
  · exact B1017559
  · exact B1017563
  · exact B1017567
  · exact B1017571
  · exact B1017575
  · exact B1017579
  · exact B1017583
  · exact B1017587
  · exact B1017591
  · exact B1017595
  · exact B1017599
  · exact B1017603
  · exact B1017607
  · exact B1017611
  · exact B1017615
  · exact B1017619
  · exact B1017623
  · exact B1017627
  · exact B1017631
  · exact B1017635
  · exact B1017639
  · exact B1017643
  · exact B1017647
  · exact B1017651
  · exact B1017655
  · exact B1017659
  · exact B1017663
  · exact B1017667
  · exact B1017671
  · exact B1017675
  · exact B1017679
  · exact B1017683
  · exact B1017687
  · exact B1017691
  · exact B1017695
  · exact B1017699
  · exact B1017703
  · exact B1017707
  · exact B1017711
  · exact B1017715
  · exact B1017719
  · exact B1017723
  · exact B1017727
  · exact B1017731
  · exact B1017735
  · exact B1017739
  · exact B1017743
  · exact B1017747
  · exact B1017751
  · exact B1017755
  · exact B1017759
  · exact B1017763
  · exact B1017767
  · exact B1017771
  · exact B1017775
  · exact B1017779
  · exact B1017783
  · exact B1017787
  · exact B1017791
  · exact B1017795
  · exact B1017799
  · exact B1017803
  · exact B1017807
  · exact B1017811
  · exact B1017815
  · exact B1017819
  · exact B1017823
  · exact B1017827
  · exact B1017831
  · exact B1017835
  · exact B1017839
  · exact B1017843
  · exact B1017847
  · exact B1017851
  · exact B1017855
  · exact B1017859
  · exact B1017863
  · exact B1017867
  · exact B1017871
  · exact B1017875
  · exact B1017879
  · exact B1017883
  · exact B1017887
  · exact B1017891
  · exact B1017895
  · exact B1017899
  · exact B1017903
  · exact B1017907
  · exact B1017911
  · exact B1017915
  · exact B1017919
  · exact B1017923
  · exact B1017927
  · exact B1017931
  · exact B1017935
  · exact B1017939
  · exact B1017943
  · exact B1017947
  · exact B1017951
  · exact B1017955
  · exact B1017959
  · exact B1017963
  · exact B1017967
  · exact B1017971
  · exact B1017975
  · exact B1017979
  · exact B1017983
  · exact B1017987
  · exact B1017991
  · exact B1017995
  · exact B1017999
  · exact B1018003
  · exact B1018007
  · exact B1018011
  · exact B1018015
  · exact B1018019
  · exact B1018023
  · exact B1018027
  · exact B1018031
  · exact B1018035
  · exact B1018039
  · exact B1018043
  · exact B1018047
  · exact B1018051
  · exact B1018055
  · exact B1018059
  · exact B1018063
  · exact B1018067
  · exact B1018071
  · exact B1018075
  · exact B1018079
  · exact B1018083
  · exact B1018087
  · exact B1018091
  · exact B1018095
  · exact B1018099
  · exact B1018103
  · exact B1018107
  · exact B1018111
  · exact B1018115
  · exact B1018119
  · exact B1018123
  · exact B1018127
  · exact B1018131
  · exact B1018135
  · exact B1018139
  · exact B1018143
  · exact B1018147
  · exact B1018151
  · exact B1018155
  · exact B1018159
  · exact B1018163
  · exact B1018167
  · exact B1018171
  · exact B1018175
  · exact B1018179
  · exact B1018183
  · exact B1018187
  · exact B1018191
  · exact B1018195
  · exact B1018199
  · exact B1018203
  · exact B1018207
  · exact B1018211
  · exact B1018215
  · exact B1018219
  · exact B1018223
  · exact B1018227
  · exact B1018231
  · exact B1018235
  · exact B1018239
  · exact B1018243
  · exact B1018247
  · exact B1018251
  · exact B1018255
  · exact B1018259
  · exact B1018263
  · exact B1018267
  · exact B1018271
  · exact B1018275
  · exact B1018279
  · exact B1018283
  · exact B1018287
  · exact B1018291
  · exact B1018295
  · exact B1018299
  · exact B1018303
  · exact B1018307
  · exact B1018311
  · exact B1018315
  · exact B1018319
  · exact B1018323
  · exact B1018327
  · exact B1018331
  · exact B1018335
  · exact B1018339
  · exact B1018343
  · exact B1018347
  · exact B1018351
  · exact B1018355
  · exact B1018359
  · exact B1018363
  · exact B1018367
  · exact B1018371
  · exact B1018375
  · exact B1018379
  · exact B1018383
  · exact B1018387
  · exact B1018391
  · exact B1018395
  · exact B1018399
  · exact B1018403
  · exact B1018407
  · exact B1018411
  · exact B1018415
  · exact B1018419
  · exact B1018423
  · exact B1018427
  · exact B1018431
  · exact B1018435
  · exact B1018439
  · exact B1018443
  · exact B1018447
  · exact B1018451
  · exact B1018455
  · exact B1018459
  · exact B1018463
  · exact B1018467
  · exact B1018471
  · exact B1018475
  · exact B1018479
  · exact B1018483
  · exact B1018487
  · exact B1018491
  · exact B1018495
  · exact B1018499
  · exact B1018503
  · exact B1018507
  · exact B1018511
  · exact B1018515
  · exact B1018519
  · exact B1018523
  · exact B1018527
  · exact B1018531
  · exact B1018535
  · exact B1018539
  · exact B1018543
  · exact B1018547
  · exact B1018551
  · exact B1018555
  · exact B1018559
  · exact B1018563
  · exact B1018567
  · exact B1018571
  · exact B1018575
  · exact B1018579
  · exact B1018583
  · exact B1018587
  · exact B1018591
  · exact B1018595
  · exact B1018599
  · exact B1018603
  · exact B1018607
  · exact B1018611
  · exact B1018615
  · exact B1018619
  · exact B1018623
  · exact B1018627
  · exact B1018631
  · exact B1018635
  · exact B1018639
  · exact B1018643
  · exact B1018647
  · exact B1018651
  · exact B1018655
  · exact B1018659
  · exact B1018663
  · exact B1018667
  · exact B1018671
  · exact B1018675
  · exact B1018679
  · exact B1018683
  · exact B1018687
  · exact B1018691
  · exact B1018695
  · exact B1018699
  · exact B1018703
  · exact B1018707
  · exact B1018711
  · exact B1018715
  · exact B1018719
  · exact B1018723
  · exact B1018727
  · exact B1018731
  · exact B1018735
  · exact B1018739
  · exact B1018743
  · exact B1018747
  · exact B1018751
  · exact B1018755
  · exact B1018759
  · exact B1018763
  · exact B1018767
  · exact B1018771
  · exact B1018775
  · exact B1018779
  · exact B1018783
  · exact B1018787
  · exact B1018791
  · exact B1018795
  · exact B1018799
  · exact B1018803
  · exact B1018807
  · exact B1018811
  · exact B1018815
  · exact B1018819
  · exact B1018823
  · exact B1018827
  · exact B1018831
  · exact B1018835
  · exact B1018839
  · exact B1018843
  · exact B1018847
  · exact B1018851
  · exact B1018855
  · exact B1018859
  · exact B1018863
  · exact B1018867
  · exact B1018871
  · exact B1018875
  · exact B1018879
  · exact B1018883
  · exact B1018887
  · exact B1018891
  · exact B1018895
  · exact B1018899
  · exact B1018903
  · exact B1018907
  · exact B1018911
  · exact B1018915
  · exact B1018919
  · exact B1018923
  · exact B1018927
  · exact B1018931
  · exact B1018935
  · exact B1018939
  · exact B1018943
  · exact B1018947
  · exact B1018951
  · exact B1018955
  · exact B1018959
  · exact B1018963
  · exact B1018967
  · exact B1018971
  · exact B1018975
  · exact B1018979
  · exact B1018983
  · exact B1018987
  · exact B1018991
  · exact B1018995
  · exact B1018999
  · exact B1019003
  · exact B1019007
  · exact B1019011
  · exact B1019015
  · exact B1019019
  · exact B1019023
  · exact B1019027
  · exact B1019031
  · exact B1019035
  · exact B1019039
  · exact B1019043
  · exact B1019047
  · exact B1019051
  · exact B1019055
  · exact B1019059
  · exact B1019063
  · exact B1019067
  · exact B1019071
  · exact B1019075
  · exact B1019079
  · exact B1019083
  · exact B1019087
  · exact B1019091
  · exact B1019095
  · exact B1019099
  · exact B1019103
  · exact B1019107
  · exact B1019111
  · exact B1019115
  · exact B1019119
  · exact B1019123
  · exact B1019127
  · exact B1019131
  · exact B1019135
  · exact B1019139
  · exact B1019143
  · exact B1019147
  · exact B1019151
  · exact B1019155
  · exact B1019159
  · exact B1019163
  · exact B1019167
  · exact B1019171
  · exact B1019175
  · exact B1019179
  · exact B1019183
  · exact B1019187
  · exact B1019191
  · exact B1019195
  · exact B1019199
  · exact B1019203
  · exact B1019207
  · exact B1019211
  · exact B1019215
  · exact B1019219
  · exact B1019223
  · exact B1019227
  · exact B1019231
  · exact B1019235
  · exact B1019239
  · exact B1019243
  · exact B1019247
  · exact B1019251
  · exact B1019255
  · exact B1019259
  · exact B1019263
  · exact B1019267
  · exact B1019271
  · exact B1019275
  · exact B1019279
  · exact B1019283
  · exact B1019287
  · exact B1019291
  · exact B1019295
  · exact B1019299
  · exact B1019303
  · exact B1019307
  · exact B1019311
  · exact B1019315
  · exact B1019319
  · exact B1019323
  · exact B1019327
  · exact B1019331
  · exact B1019335
  · exact B1019339
  · exact B1019343
  · exact B1019347
  · exact B1019351
  · exact B1019355
  · exact B1019359
  · exact B1019363
  · exact B1019367
  · exact B1019371
  · exact B1019375
  · exact B1019379
  · exact B1019383
  · exact B1019387
  · exact B1019391
  · exact B1019395
  · exact B1019399

theorem C1 (j : ℕ) (h1 : 254850 ≤ j) (h2 : j ≤ 255150) : Blo 1016603 (4 * j + 3) := by
  interval_cases j
  · exact B1019403
  · exact B1019407
  · exact B1019411
  · exact B1019415
  · exact B1019419
  · exact B1019423
  · exact B1019427
  · exact B1019431
  · exact B1019435
  · exact B1019439
  · exact B1019443
  · exact B1019447
  · exact B1019451
  · exact B1019455
  · exact B1019459
  · exact B1019463
  · exact B1019467
  · exact B1019471
  · exact B1019475
  · exact B1019479
  · exact B1019483
  · exact B1019487
  · exact B1019491
  · exact B1019495
  · exact B1019499
  · exact B1019503
  · exact B1019507
  · exact B1019511
  · exact B1019515
  · exact B1019519
  · exact B1019523
  · exact B1019527
  · exact B1019531
  · exact B1019535
  · exact B1019539
  · exact B1019543
  · exact B1019547
  · exact B1019551
  · exact B1019555
  · exact B1019559
  · exact B1019563
  · exact B1019567
  · exact B1019571
  · exact B1019575
  · exact B1019579
  · exact B1019583
  · exact B1019587
  · exact B1019591
  · exact B1019595
  · exact B1019599
  · exact B1019603
  · exact B1019607
  · exact B1019611
  · exact B1019615
  · exact B1019619
  · exact B1019623
  · exact B1019627
  · exact B1019631
  · exact B1019635
  · exact B1019639
  · exact B1019643
  · exact B1019647
  · exact B1019651
  · exact B1019655
  · exact B1019659
  · exact B1019663
  · exact B1019667
  · exact B1019671
  · exact B1019675
  · exact B1019679
  · exact B1019683
  · exact B1019687
  · exact B1019691
  · exact B1019695
  · exact B1019699
  · exact B1019703
  · exact B1019707
  · exact B1019711
  · exact B1019715
  · exact B1019719
  · exact B1019723
  · exact B1019727
  · exact B1019731
  · exact B1019735
  · exact B1019739
  · exact B1019743
  · exact B1019747
  · exact B1019751
  · exact B1019755
  · exact B1019759
  · exact B1019763
  · exact B1019767
  · exact B1019771
  · exact B1019775
  · exact B1019779
  · exact B1019783
  · exact B1019787
  · exact B1019791
  · exact B1019795
  · exact B1019799
  · exact B1019803
  · exact B1019807
  · exact B1019811
  · exact B1019815
  · exact B1019819
  · exact B1019823
  · exact B1019827
  · exact B1019831
  · exact B1019835
  · exact B1019839
  · exact B1019843
  · exact B1019847
  · exact B1019851
  · exact B1019855
  · exact B1019859
  · exact B1019863
  · exact B1019867
  · exact B1019871
  · exact B1019875
  · exact B1019879
  · exact B1019883
  · exact B1019887
  · exact B1019891
  · exact B1019895
  · exact B1019899
  · exact B1019903
  · exact B1019907
  · exact B1019911
  · exact B1019915
  · exact B1019919
  · exact B1019923
  · exact B1019927
  · exact B1019931
  · exact B1019935
  · exact B1019939
  · exact B1019943
  · exact B1019947
  · exact B1019951
  · exact B1019955
  · exact B1019959
  · exact B1019963
  · exact B1019967
  · exact B1019971
  · exact B1019975
  · exact B1019979
  · exact B1019983
  · exact B1019987
  · exact B1019991
  · exact B1019995
  · exact B1019999
  · exact B1020003
  · exact B1020007
  · exact B1020011
  · exact B1020015
  · exact B1020019
  · exact B1020023
  · exact B1020027
  · exact B1020031
  · exact B1020035
  · exact B1020039
  · exact B1020043
  · exact B1020047
  · exact B1020051
  · exact B1020055
  · exact B1020059
  · exact B1020063
  · exact B1020067
  · exact B1020071
  · exact B1020075
  · exact B1020079
  · exact B1020083
  · exact B1020087
  · exact B1020091
  · exact B1020095
  · exact B1020099
  · exact B1020103
  · exact B1020107
  · exact B1020111
  · exact B1020115
  · exact B1020119
  · exact B1020123
  · exact B1020127
  · exact B1020131
  · exact B1020135
  · exact B1020139
  · exact B1020143
  · exact B1020147
  · exact B1020151
  · exact B1020155
  · exact B1020159
  · exact B1020163
  · exact B1020167
  · exact B1020171
  · exact B1020175
  · exact B1020179
  · exact B1020183
  · exact B1020187
  · exact B1020191
  · exact B1020195
  · exact B1020199
  · exact B1020203
  · exact B1020207
  · exact B1020211
  · exact B1020215
  · exact B1020219
  · exact B1020223
  · exact B1020227
  · exact B1020231
  · exact B1020235
  · exact B1020239
  · exact B1020243
  · exact B1020247
  · exact B1020251
  · exact B1020255
  · exact B1020259
  · exact B1020263
  · exact B1020267
  · exact B1020271
  · exact B1020275
  · exact B1020279
  · exact B1020283
  · exact B1020287
  · exact B1020291
  · exact B1020295
  · exact B1020299
  · exact B1020303
  · exact B1020307
  · exact B1020311
  · exact B1020315
  · exact B1020319
  · exact B1020323
  · exact B1020327
  · exact B1020331
  · exact B1020335
  · exact B1020339
  · exact B1020343
  · exact B1020347
  · exact B1020351
  · exact B1020355
  · exact B1020359
  · exact B1020363
  · exact B1020367
  · exact B1020371
  · exact B1020375
  · exact B1020379
  · exact B1020383
  · exact B1020387
  · exact B1020391
  · exact B1020395
  · exact B1020399
  · exact B1020403
  · exact B1020407
  · exact B1020411
  · exact B1020415
  · exact B1020419
  · exact B1020423
  · exact B1020427
  · exact B1020431
  · exact B1020435
  · exact B1020439
  · exact B1020443
  · exact B1020447
  · exact B1020451
  · exact B1020455
  · exact B1020459
  · exact B1020463
  · exact B1020467
  · exact B1020471
  · exact B1020475
  · exact B1020479
  · exact B1020483
  · exact B1020487
  · exact B1020491
  · exact B1020495
  · exact B1020499
  · exact B1020503
  · exact B1020507
  · exact B1020511
  · exact B1020515
  · exact B1020519
  · exact B1020523
  · exact B1020527
  · exact B1020531
  · exact B1020535
  · exact B1020539
  · exact B1020543
  · exact B1020547
  · exact B1020551
  · exact B1020555
  · exact B1020559
  · exact B1020563
  · exact B1020567
  · exact B1020571
  · exact B1020575
  · exact B1020579
  · exact B1020583
  · exact B1020587
  · exact B1020591
  · exact B1020595
  · exact B1020599
  · exact B1020603

theorem solution (m : ℕ) (hlo : 1016603 ≤ m) (hhi : m ≤ 1020603) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 254150 ≤ j := by omega
    have hj2 : j ≤ 255150 := by omega
    have hb : Blo 1016603 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 254850 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
