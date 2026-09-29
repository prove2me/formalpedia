-- Prove2me | solution 1 for syracuse_descends_range_1387513_1389513
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:30.260586+00:00
-- url     : https://prove2.me/submissions/33060f20-699f-4427-8534-d5b342f182c3

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


theorem B1482769 : Blo 1387513 1482769 := bbase (se 2 (by rfl) ⟨556038, by rfl⟩ : syracuseStep 1482769 = 1112077) (by norm_num)
theorem B2342965 : Blo 1387513 2342965 := bbase (se 5 (by rfl) ⟨109826, by rfl⟩ : syracuseStep 2342965 = 219653) (by norm_num)
theorem B2965565 : Blo 1387513 2965565 := bbase (se 3 (by rfl) ⟨556043, by rfl⟩ : syracuseStep 2965565 = 1112087) (by norm_num)
theorem B3334213 : Blo 1387513 3334213 := bbase (se 4 (by rfl) ⟨312582, by rfl⟩ : syracuseStep 3334213 = 625165) (by norm_num)
theorem B2252909 : Blo 1387513 2252909 := bbase (se 3 (by rfl) ⟨422420, by rfl⟩ : syracuseStep 2252909 = 844841) (by norm_num)
theorem B4685957 : Blo 1387513 4685957 := bbase (se 4 (by rfl) ⟨439308, by rfl⟩ : syracuseStep 4685957 = 878617) (by norm_num)
theorem B2343053 : Blo 1387513 2343053 := bbase (se 3 (by rfl) ⟨439322, by rfl⟩ : syracuseStep 2343053 = 878645) (by norm_num)
theorem B3514549 : Blo 1387513 3514549 := bbase (se 5 (by rfl) ⟨164744, by rfl⟩ : syracuseStep 3514549 = 329489) (by norm_num)
theorem B1482953 : Blo 1387513 1482953 := bbase (se 2 (by rfl) ⟨556107, by rfl⟩ : syracuseStep 1482953 = 1112215) (by norm_num)
theorem B2965709 : Blo 1387513 2965709 := bbase (se 3 (by rfl) ⟨556070, by rfl⟩ : syracuseStep 2965709 = 1112141) (by norm_num)
theorem B2343181 : Blo 1387513 2343181 := bbase (se 3 (by rfl) ⟨439346, by rfl⟩ : syracuseStep 2343181 = 878693) (by norm_num)
theorem B3514661 : Blo 1387513 3514661 := bbase (se 4 (by rfl) ⟨329499, by rfl⟩ : syracuseStep 3514661 = 658999) (by norm_num)
theorem B2343269 : Blo 1387513 2343269 := bbase (se 4 (by rfl) ⟨219681, by rfl⟩ : syracuseStep 2343269 = 439363) (by norm_num)
theorem B3514853 : Blo 1387513 3514853 := bbase (se 4 (by rfl) ⟨329517, by rfl⟩ : syracuseStep 3514853 = 659035) (by norm_num)
theorem B2343397 : Blo 1387513 2343397 := bbase (se 4 (by rfl) ⟨219693, by rfl⟩ : syracuseStep 2343397 = 439387) (by norm_num)
theorem B2081285 : Blo 1387513 2081285 := bbase (se 4 (by rfl) ⟨195120, by rfl⟩ : syracuseStep 2081285 = 390241) (by norm_num)
theorem B7225877 : Blo 1387513 7225877 := bbase (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) (by norm_num)
theorem B2081309 : Blo 1387513 2081309 := bbase (se 3 (by rfl) ⟨390245, by rfl⟩ : syracuseStep 2081309 = 780491) (by norm_num)
theorem B2081333 : Blo 1387513 2081333 := bbase (se 5 (by rfl) ⟨97562, by rfl⟩ : syracuseStep 2081333 = 195125) (by norm_num)
theorem B4686389 : Blo 1387513 4686389 := bbase (se 5 (by rfl) ⟨219674, by rfl⟩ : syracuseStep 4686389 = 439349) (by norm_num)
theorem B2343485 : Blo 1387513 2343485 := bbase (se 3 (by rfl) ⟨439403, by rfl⟩ : syracuseStep 2343485 = 878807) (by norm_num)
theorem B5931589 : Blo 1387513 5931589 := bbase (se 4 (by rfl) ⟨556086, by rfl⟩ : syracuseStep 5931589 = 1112173) (by norm_num)
theorem B2081357 : Blo 1387513 2081357 := bbase (se 3 (by rfl) ⟨390254, by rfl⟩ : syracuseStep 2081357 = 780509) (by norm_num)
theorem B1876565 : Blo 1387513 1876565 := bbase (se 8 (by rfl) ⟨10995, by rfl⟩ : syracuseStep 1876565 = 21991) (by norm_num)
theorem B2081381 : Blo 1387513 2081381 := bbase (se 4 (by rfl) ⟨195129, by rfl⟩ : syracuseStep 2081381 = 390259) (by norm_num)
theorem B2081405 : Blo 1387513 2081405 := bbase (se 3 (by rfl) ⟨390263, by rfl⟩ : syracuseStep 2081405 = 780527) (by norm_num)
theorem B2081429 : Blo 1387513 2081429 := bbase (se 6 (by rfl) ⟨48783, by rfl⟩ : syracuseStep 2081429 = 97567) (by norm_num)
theorem B2851493 : Blo 1387513 2851493 := bbase (se 4 (by rfl) ⟨267327, by rfl⟩ : syracuseStep 2851493 = 534655) (by norm_num)
theorem B2081453 : Blo 1387513 2081453 := bbase (se 3 (by rfl) ⟨390272, by rfl⟩ : syracuseStep 2081453 = 780545) (by norm_num)
theorem B2343613 : Blo 1387513 2343613 := bbase (se 3 (by rfl) ⟨439427, by rfl⟩ : syracuseStep 2343613 = 878855) (by norm_num)
theorem B2081477 : Blo 1387513 2081477 := bbase (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) (by norm_num)
theorem B2081501 : Blo 1387513 2081501 := bbase (se 3 (by rfl) ⟨390281, by rfl⟩ : syracuseStep 2081501 = 780563) (by norm_num)
theorem B1876717 : Blo 1387513 1876717 := bbase (se 3 (by rfl) ⟨351884, by rfl⟩ : syracuseStep 1876717 = 703769) (by norm_num)
theorem B2081525 : Blo 1387513 2081525 := bbase (se 5 (by rfl) ⟨97571, by rfl⟩ : syracuseStep 2081525 = 195143) (by norm_num)
theorem B2081549 : Blo 1387513 2081549 := bbase (se 3 (by rfl) ⟨390290, by rfl⟩ : syracuseStep 2081549 = 780581) (by norm_num)
theorem B3334925 : Blo 1387513 3334925 := bbase (se 3 (by rfl) ⟨625298, by rfl⟩ : syracuseStep 3334925 = 1250597) (by norm_num)
theorem B2343701 : Blo 1387513 2343701 := bbase (se 6 (by rfl) ⟨54930, by rfl⟩ : syracuseStep 2343701 = 109861) (by norm_num)
theorem B2081573 : Blo 1387513 2081573 := bbase (se 4 (by rfl) ⟨195147, by rfl⟩ : syracuseStep 2081573 = 390295) (by norm_num)
theorem B3121973 : Blo 1387513 3121973 := bbase (se 5 (by rfl) ⟨146342, by rfl⟩ : syracuseStep 3121973 = 292685) (by norm_num)
theorem B4449077 : Blo 1387513 4449077 := bbase (se 5 (by rfl) ⟨208550, by rfl⟩ : syracuseStep 4449077 = 417101) (by norm_num)
theorem B2081597 : Blo 1387513 2081597 := bbase (se 3 (by rfl) ⟨390299, by rfl⟩ : syracuseStep 2081597 = 780599) (by norm_num)
theorem B3515197 : Blo 1387513 3515197 := bbase (se 3 (by rfl) ⟨659099, by rfl⟩ : syracuseStep 3515197 = 1318199) (by norm_num)
theorem B2081621 : Blo 1387513 2081621 := bbase (se 9 (by rfl) ⟨6098, by rfl⟩ : syracuseStep 2081621 = 12197) (by norm_num)
theorem B2081645 : Blo 1387513 2081645 := bbase (se 3 (by rfl) ⟨390308, by rfl⟩ : syracuseStep 2081645 = 780617) (by norm_num)
theorem B3122045 : Blo 1387513 3122045 := bbase (se 3 (by rfl) ⟨585383, by rfl⟩ : syracuseStep 3122045 = 1170767) (by norm_num)
theorem B2081669 : Blo 1387513 2081669 := bbase (se 4 (by rfl) ⟨195156, by rfl⟩ : syracuseStep 2081669 = 390313) (by norm_num)
theorem B2343829 : Blo 1387513 2343829 := bbase (se 6 (by rfl) ⟨54933, by rfl⟩ : syracuseStep 2343829 = 109867) (by norm_num)
theorem B7127957 : Blo 1387513 7127957 := bbase (se 6 (by rfl) ⟨167061, by rfl⟩ : syracuseStep 7127957 = 334123) (by norm_num)
theorem B2081693 : Blo 1387513 2081693 := bbase (se 3 (by rfl) ⟨390317, by rfl⟩ : syracuseStep 2081693 = 780635) (by norm_num)
theorem B3515309 : Blo 1387513 3515309 := bbase (se 3 (by rfl) ⟨659120, by rfl⟩ : syracuseStep 3515309 = 1318241) (by norm_num)
theorem B4219829 : Blo 1387513 4219829 := bbase (se 5 (by rfl) ⟨197804, by rfl⟩ : syracuseStep 4219829 = 395609) (by norm_num)
theorem B2081717 : Blo 1387513 2081717 := bbase (se 5 (by rfl) ⟨97580, by rfl⟩ : syracuseStep 2081717 = 195161) (by norm_num)
theorem B2966453 : Blo 1387513 2966453 := bbase (se 5 (by rfl) ⟨139052, by rfl⟩ : syracuseStep 2966453 = 278105) (by norm_num)
theorem B1483705 : Blo 1387513 1483705 := bbase (se 2 (by rfl) ⟨556389, by rfl⟩ : syracuseStep 1483705 = 1112779) (by norm_num)
theorem B3122117 : Blo 1387513 3122117 := bbase (se 4 (by rfl) ⟨292698, by rfl⟩ : syracuseStep 3122117 = 585397) (by norm_num)
theorem B2081741 : Blo 1387513 2081741 := bbase (se 3 (by rfl) ⟨390326, by rfl⟩ : syracuseStep 2081741 = 780653) (by norm_num)
theorem B2081765 : Blo 1387513 2081765 := bbase (se 4 (by rfl) ⟨195165, by rfl⟩ : syracuseStep 2081765 = 390331) (by norm_num)
theorem B4686821 : Blo 1387513 4686821 := bbase (se 4 (by rfl) ⟨439389, by rfl⟩ : syracuseStep 4686821 = 878779) (by norm_num)
theorem B2343917 : Blo 1387513 2343917 := bbase (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) (by norm_num)
theorem B4449269 : Blo 1387513 4449269 := bbase (se 5 (by rfl) ⟨208559, by rfl⟩ : syracuseStep 4449269 = 417119) (by norm_num)
theorem B1713145 : Blo 1387513 1713145 := bbase (se 2 (by rfl) ⟨642429, by rfl⟩ : syracuseStep 1713145 = 1284859) (by norm_num)
theorem B2081789 : Blo 1387513 2081789 := bbase (se 3 (by rfl) ⟨390335, by rfl⟩ : syracuseStep 2081789 = 780671) (by norm_num)
theorem B1483777 : Blo 1387513 1483777 := bbase (se 2 (by rfl) ⟨556416, by rfl⟩ : syracuseStep 1483777 = 1112833) (by norm_num)
theorem B3122189 : Blo 1387513 3122189 := bbase (se 3 (by rfl) ⟨585410, by rfl⟩ : syracuseStep 3122189 = 1170821) (by norm_num)
theorem B2081813 : Blo 1387513 2081813 := bbase (se 6 (by rfl) ⟨48792, by rfl⟩ : syracuseStep 2081813 = 97585) (by norm_num)
theorem B2081837 : Blo 1387513 2081837 := bbase (se 3 (by rfl) ⟨390344, by rfl⟩ : syracuseStep 2081837 = 780689) (by norm_num)
theorem B12665909 : Blo 1387513 12665909 := bbase (se 5 (by rfl) ⟨593714, by rfl⟩ : syracuseStep 12665909 = 1187429) (by norm_num)
theorem B2081861 : Blo 1387513 2081861 := bbase (se 4 (by rfl) ⟨195174, by rfl⟩ : syracuseStep 2081861 = 390349) (by norm_num)
theorem B3122261 : Blo 1387513 3122261 := bbase (se 8 (by rfl) ⟨18294, by rfl⟩ : syracuseStep 3122261 = 36589) (by norm_num)
theorem B2081885 : Blo 1387513 2081885 := bbase (se 3 (by rfl) ⟨390353, by rfl⟩ : syracuseStep 2081885 = 780707) (by norm_num)
theorem B3515501 : Blo 1387513 3515501 := bbase (se 3 (by rfl) ⟨659156, by rfl⟩ : syracuseStep 3515501 = 1318313) (by norm_num)
theorem B2344045 : Blo 1387513 2344045 := bbase (se 3 (by rfl) ⟨439508, by rfl⟩ : syracuseStep 2344045 = 879017) (by norm_num)
theorem B2081909 : Blo 1387513 2081909 := bbase (se 5 (by rfl) ⟨97589, by rfl⟩ : syracuseStep 2081909 = 195179) (by norm_num)
theorem B2081933 : Blo 1387513 2081933 := bbase (se 3 (by rfl) ⟨390362, by rfl⟩ : syracuseStep 2081933 = 780725) (by norm_num)
theorem B3335309 : Blo 1387513 3335309 := bbase (se 3 (by rfl) ⟨625370, by rfl⟩ : syracuseStep 3335309 = 1250741) (by norm_num)
theorem B3122333 : Blo 1387513 3122333 := bbase (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) (by norm_num)
theorem B2081957 : Blo 1387513 2081957 := bbase (se 4 (by rfl) ⟨195183, by rfl⟩ : syracuseStep 2081957 = 390367) (by norm_num)
theorem B2081981 : Blo 1387513 2081981 := bbase (se 3 (by rfl) ⟨390371, by rfl⟩ : syracuseStep 2081981 = 780743) (by norm_num)
theorem B2344133 : Blo 1387513 2344133 := bbase (se 4 (by rfl) ⟨219762, by rfl⟩ : syracuseStep 2344133 = 439525) (by norm_num)
theorem B2082005 : Blo 1387513 2082005 := bbase (se 7 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 2082005 = 48797) (by norm_num)
theorem B3122405 : Blo 1387513 3122405 := bbase (se 4 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 3122405 = 585451) (by norm_num)
theorem B7029989 : Blo 1387513 7029989 := bbase (se 4 (by rfl) ⟨659061, by rfl⟩ : syracuseStep 7029989 = 1318123) (by norm_num)
theorem B2082029 : Blo 1387513 2082029 := bbase (se 3 (by rfl) ⟨390380, by rfl⟩ : syracuseStep 2082029 = 780761) (by norm_num)
theorem B2082053 : Blo 1387513 2082053 := bbase (se 4 (by rfl) ⟨195192, by rfl⟩ : syracuseStep 2082053 = 390385) (by norm_num)
theorem B10003733 : Blo 1387513 10003733 := bbase (se 6 (by rfl) ⟨234462, by rfl⟩ : syracuseStep 10003733 = 468925) (by norm_num)
theorem B2082077 : Blo 1387513 2082077 := bbase (se 3 (by rfl) ⟨390389, by rfl⟩ : syracuseStep 2082077 = 780779) (by norm_num)
theorem B3122477 : Blo 1387513 3122477 := bbase (se 3 (by rfl) ⟨585464, by rfl⟩ : syracuseStep 3122477 = 1170929) (by norm_num)
theorem B2082101 : Blo 1387513 2082101 := bbase (se 5 (by rfl) ⟨97598, by rfl⟩ : syracuseStep 2082101 = 195197) (by norm_num)
theorem B2344261 : Blo 1387513 2344261 := bbase (se 4 (by rfl) ⟨219774, by rfl⟩ : syracuseStep 2344261 = 439549) (by norm_num)
theorem B2082125 : Blo 1387513 2082125 := bbase (se 3 (by rfl) ⟨390398, by rfl⟩ : syracuseStep 2082125 = 780797) (by norm_num)
theorem B11863381 : Blo 1387513 11863381 := bbase (se 12 (by rfl) ⟨4344, by rfl⟩ : syracuseStep 11863381 = 8689) (by norm_num)
theorem B2082149 : Blo 1387513 2082149 := bbase (se 4 (by rfl) ⟨195201, by rfl⟩ : syracuseStep 2082149 = 390403) (by norm_num)
theorem B3122549 : Blo 1387513 3122549 := bbase (se 5 (by rfl) ⟨146369, by rfl⟩ : syracuseStep 3122549 = 292739) (by norm_num)
theorem B8562037 : Blo 1387513 8562037 := bbase (se 5 (by rfl) ⟨401345, by rfl⟩ : syracuseStep 8562037 = 802691) (by norm_num)
theorem B2082173 : Blo 1387513 2082173 := bbase (se 3 (by rfl) ⟨390407, by rfl⟩ : syracuseStep 2082173 = 780815) (by norm_num)
theorem B1975693 : Blo 1387513 1975693 := bbase (se 3 (by rfl) ⟨370442, by rfl⟩ : syracuseStep 1975693 = 740885) (by norm_num)
theorem B2082197 : Blo 1387513 2082197 := bbase (se 6 (by rfl) ⟨48801, by rfl⟩ : syracuseStep 2082197 = 97603) (by norm_num)
theorem B4687253 : Blo 1387513 4687253 := bbase (se 6 (by rfl) ⟨109857, by rfl⟩ : syracuseStep 4687253 = 219715) (by norm_num)
theorem B2672029 : Blo 1387513 2672029 := bbase (se 3 (by rfl) ⟨501005, by rfl⟩ : syracuseStep 2672029 = 1002011) (by norm_num)
theorem B2344349 : Blo 1387513 2344349 := bbase (se 3 (by rfl) ⟨439565, by rfl⟩ : syracuseStep 2344349 = 879131) (by norm_num)
theorem B2082221 : Blo 1387513 2082221 := bbase (se 3 (by rfl) ⟨390416, by rfl⟩ : syracuseStep 2082221 = 780833) (by norm_num)
theorem B3335597 : Blo 1387513 3335597 := bbase (se 3 (by rfl) ⟨625424, by rfl⟩ : syracuseStep 3335597 = 1250849) (by norm_num)
theorem B3122621 : Blo 1387513 3122621 := bbase (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) (by norm_num)
theorem B2082245 : Blo 1387513 2082245 := bbase (se 4 (by rfl) ⟨195210, by rfl⟩ : syracuseStep 2082245 = 390421) (by norm_num)
theorem B3515845 : Blo 1387513 3515845 := bbase (se 4 (by rfl) ⟨329610, by rfl⟩ : syracuseStep 3515845 = 659221) (by norm_num)
theorem B2082269 : Blo 1387513 2082269 := bbase (se 3 (by rfl) ⟨390425, by rfl⟩ : syracuseStep 2082269 = 780851) (by norm_num)
theorem B2082293 : Blo 1387513 2082293 := bbase (se 5 (by rfl) ⟨97607, by rfl⟩ : syracuseStep 2082293 = 195215) (by norm_num)
theorem B3122693 : Blo 1387513 3122693 := bbase (se 4 (by rfl) ⟨292752, by rfl⟩ : syracuseStep 3122693 = 585505) (by norm_num)
theorem B4752901 : Blo 1387513 4752901 := bbase (se 4 (by rfl) ⟨445584, by rfl⟩ : syracuseStep 4752901 = 891169) (by norm_num)
theorem B2082317 : Blo 1387513 2082317 := bbase (se 3 (by rfl) ⟨390434, by rfl⟩ : syracuseStep 2082317 = 780869) (by norm_num)
theorem B2344477 : Blo 1387513 2344477 := bbase (se 3 (by rfl) ⟨439589, by rfl⟩ : syracuseStep 2344477 = 879179) (by norm_num)
theorem B2082341 : Blo 1387513 2082341 := bbase (se 4 (by rfl) ⟨195219, by rfl⟩ : syracuseStep 2082341 = 390439) (by norm_num)
theorem B3515957 : Blo 1387513 3515957 := bbase (se 5 (by rfl) ⟨164810, by rfl⟩ : syracuseStep 3515957 = 329621) (by norm_num)
theorem B2082365 : Blo 1387513 2082365 := bbase (se 3 (by rfl) ⟨390443, by rfl⟩ : syracuseStep 2082365 = 780887) (by norm_num)
theorem B3122765 : Blo 1387513 3122765 := bbase (se 3 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 3122765 = 1171037) (by norm_num)
theorem B2082389 : Blo 1387513 2082389 := bbase (se 8 (by rfl) ⟨12201, by rfl⟩ : syracuseStep 2082389 = 24403) (by norm_num)
theorem B1975909 : Blo 1387513 1975909 := bbase (se 4 (by rfl) ⟨185241, by rfl⟩ : syracuseStep 1975909 = 370483) (by norm_num)
theorem B2082413 : Blo 1387513 2082413 := bbase (se 3 (by rfl) ⟨390452, by rfl⟩ : syracuseStep 2082413 = 780905) (by norm_num)
theorem B2344565 : Blo 1387513 2344565 := bbase (se 5 (by rfl) ⟨109901, by rfl⟩ : syracuseStep 2344565 = 219803) (by norm_num)
theorem B2082437 : Blo 1387513 2082437 := bbase (se 4 (by rfl) ⟨195228, by rfl⟩ : syracuseStep 2082437 = 390457) (by norm_num)
theorem B3122837 : Blo 1387513 3122837 := bbase (se 6 (by rfl) ⟨73191, by rfl⟩ : syracuseStep 3122837 = 146383) (by norm_num)
theorem B2082461 : Blo 1387513 2082461 := bbase (se 3 (by rfl) ⟨390461, by rfl⟩ : syracuseStep 2082461 = 780923) (by norm_num)
theorem B2967205 : Blo 1387513 2967205 := bbase (se 4 (by rfl) ⟨278175, by rfl⟩ : syracuseStep 2967205 = 556351) (by norm_num)
theorem B2082485 : Blo 1387513 2082485 := bbase (se 5 (by rfl) ⟨97616, by rfl⟩ : syracuseStep 2082485 = 195233) (by norm_num)
theorem B2082509 : Blo 1387513 2082509 := bbase (se 3 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 2082509 = 780941) (by norm_num)
theorem B3122909 : Blo 1387513 3122909 := bbase (se 3 (by rfl) ⟨585545, by rfl⟩ : syracuseStep 3122909 = 1171091) (by norm_num)
theorem B2082533 : Blo 1387513 2082533 := bbase (se 4 (by rfl) ⟨195237, by rfl⟩ : syracuseStep 2082533 = 390475) (by norm_num)
theorem B3516149 : Blo 1387513 3516149 := bbase (se 5 (by rfl) ⟨164819, by rfl⟩ : syracuseStep 3516149 = 329639) (by norm_num)
theorem B2344693 : Blo 1387513 2344693 := bbase (se 5 (by rfl) ⟨109907, by rfl⟩ : syracuseStep 2344693 = 219815) (by norm_num)
theorem B2082557 : Blo 1387513 2082557 := bbase (se 3 (by rfl) ⟨390479, by rfl⟩ : syracuseStep 2082557 = 780959) (by norm_num)
theorem B2082581 : Blo 1387513 2082581 := bbase (se 6 (by rfl) ⟨48810, by rfl⟩ : syracuseStep 2082581 = 97621) (by norm_num)
theorem B3122981 : Blo 1387513 3122981 := bbase (se 4 (by rfl) ⟨292779, by rfl⟩ : syracuseStep 3122981 = 585559) (by norm_num)
theorem B2082605 : Blo 1387513 2082605 := bbase (se 3 (by rfl) ⟨390488, by rfl⟩ : syracuseStep 2082605 = 780977) (by norm_num)
theorem B2967349 : Blo 1387513 2967349 := bbase (se 5 (by rfl) ⟨139094, by rfl⟩ : syracuseStep 2967349 = 278189) (by norm_num)
theorem B2082629 : Blo 1387513 2082629 := bbase (se 4 (by rfl) ⟨195246, by rfl⟩ : syracuseStep 2082629 = 390493) (by norm_num)
theorem B4687685 : Blo 1387513 4687685 := bbase (se 4 (by rfl) ⟨439470, by rfl⟩ : syracuseStep 4687685 = 878941) (by norm_num)
theorem B2344781 : Blo 1387513 2344781 := bbase (se 3 (by rfl) ⟨439646, by rfl⟩ : syracuseStep 2344781 = 879293) (by norm_num)
theorem B5269333 : Blo 1387513 5269333 := bbase (se 9 (by rfl) ⟨15437, by rfl⟩ : syracuseStep 5269333 = 30875) (by norm_num)
theorem B15222613 : Blo 1387513 15222613 := bbase (se 9 (by rfl) ⟨44597, by rfl⟩ : syracuseStep 15222613 = 89195) (by norm_num)
theorem B2082653 : Blo 1387513 2082653 := bbase (se 3 (by rfl) ⟨390497, by rfl⟩ : syracuseStep 2082653 = 780995) (by norm_num)
theorem B3123053 : Blo 1387513 3123053 := bbase (se 3 (by rfl) ⟨585572, by rfl⟩ : syracuseStep 3123053 = 1171145) (by norm_num)
theorem B2082677 : Blo 1387513 2082677 := bbase (se 5 (by rfl) ⟨97625, by rfl⟩ : syracuseStep 2082677 = 195251) (by norm_num)
theorem B6014837 : Blo 1387513 6014837 := bbase (se 5 (by rfl) ⟨281945, by rfl⟩ : syracuseStep 6014837 = 563891) (by norm_num)
theorem B2082701 : Blo 1387513 2082701 := bbase (se 3 (by rfl) ⟨390506, by rfl⟩ : syracuseStep 2082701 = 781013) (by norm_num)
theorem B7604117 : Blo 1387513 7604117 := bbase (se 6 (by rfl) ⟨178221, by rfl⟩ : syracuseStep 7604117 = 356443) (by norm_num)
theorem B2082725 : Blo 1387513 2082725 := bbase (se 4 (by rfl) ⟨195255, by rfl⟩ : syracuseStep 2082725 = 390511) (by norm_num)
theorem B3123125 : Blo 1387513 3123125 := bbase (se 5 (by rfl) ⟨146396, by rfl⟩ : syracuseStep 3123125 = 292793) (by norm_num)
theorem B2082749 : Blo 1387513 2082749 := bbase (se 3 (by rfl) ⟨390515, by rfl⟩ : syracuseStep 2082749 = 781031) (by norm_num)
theorem B30418901 : Blo 1387513 30418901 := bbase (se 7 (by rfl) ⟨356471, by rfl⟩ : syracuseStep 30418901 = 712943) (by norm_num)
theorem B2082773 : Blo 1387513 2082773 := bbase (se 7 (by rfl) ⟨24407, by rfl⟩ : syracuseStep 2082773 = 48815) (by norm_num)
theorem B15820757 : Blo 1387513 15820757 := bbase (se 7 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 15820757 = 370799) (by norm_num)
theorem B1976285 : Blo 1387513 1976285 := bbase (se 3 (by rfl) ⟨370553, by rfl⟩ : syracuseStep 1976285 = 741107) (by norm_num)
theorem B6670309 : Blo 1387513 6670309 := bbase (se 4 (by rfl) ⟨625341, by rfl⟩ : syracuseStep 6670309 = 1250683) (by norm_num)
theorem B2082797 : Blo 1387513 2082797 := bbase (se 3 (by rfl) ⟨390524, by rfl⟩ : syracuseStep 2082797 = 781049) (by norm_num)
theorem B3123197 : Blo 1387513 3123197 := bbase (se 3 (by rfl) ⟨585599, by rfl⟩ : syracuseStep 3123197 = 1171199) (by norm_num)
theorem B2082821 : Blo 1387513 2082821 := bbase (se 4 (by rfl) ⟨195264, by rfl⟩ : syracuseStep 2082821 = 390529) (by norm_num)
theorem B6334469 : Blo 1387513 6334469 := bbase (se 4 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 6334469 = 1187713) (by norm_num)
theorem B2672645 : Blo 1387513 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B2082845 : Blo 1387513 2082845 := bbase (se 3 (by rfl) ⟨390533, by rfl⟩ : syracuseStep 2082845 = 781067) (by norm_num)
theorem B2082869 : Blo 1387513 2082869 := bbase (se 5 (by rfl) ⟨97634, by rfl⟩ : syracuseStep 2082869 = 195269) (by norm_num)
theorem B3123269 : Blo 1387513 3123269 := bbase (se 4 (by rfl) ⟨292806, by rfl⟩ : syracuseStep 3123269 = 585613) (by norm_num)
theorem B2082893 : Blo 1387513 2082893 := bbase (se 3 (by rfl) ⟨390542, by rfl⟩ : syracuseStep 2082893 = 781085) (by norm_num)
theorem B3516493 : Blo 1387513 3516493 := bbase (se 3 (by rfl) ⟨659342, by rfl⟩ : syracuseStep 3516493 = 1318685) (by norm_num)
theorem B2082917 : Blo 1387513 2082917 := bbase (se 4 (by rfl) ⟨195273, by rfl⟩ : syracuseStep 2082917 = 390547) (by norm_num)
theorem B2500733 : Blo 1387513 2500733 := bbase (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) (by norm_num)
theorem B2082941 : Blo 1387513 2082941 := bbase (se 3 (by rfl) ⟨390551, by rfl⟩ : syracuseStep 2082941 = 781103) (by norm_num)
theorem B5269637 : Blo 1387513 5269637 := bbase (se 4 (by rfl) ⟨494028, by rfl⟩ : syracuseStep 5269637 = 988057) (by norm_num)
theorem B3123341 : Blo 1387513 3123341 := bbase (se 3 (by rfl) ⟨585626, by rfl⟩ : syracuseStep 3123341 = 1171253) (by norm_num)
theorem B2082965 : Blo 1387513 2082965 := bbase (se 6 (by rfl) ⟨48819, by rfl⟩ : syracuseStep 2082965 = 97639) (by norm_num)
theorem B2082989 : Blo 1387513 2082989 := bbase (se 3 (by rfl) ⟨390560, by rfl⟩ : syracuseStep 2082989 = 781121) (by norm_num)
theorem B3516605 : Blo 1387513 3516605 := bbase (se 3 (by rfl) ⟨659363, by rfl⟩ : syracuseStep 3516605 = 1318727) (by norm_num)
theorem B2083013 : Blo 1387513 2083013 := bbase (se 4 (by rfl) ⟨195282, by rfl⟩ : syracuseStep 2083013 = 390565) (by norm_num)
theorem B3123413 : Blo 1387513 3123413 := bbase (se 7 (by rfl) ⟨36602, by rfl⟩ : syracuseStep 3123413 = 73205) (by norm_num)
theorem B26699989 : Blo 1387513 26699989 := bbase (se 7 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 26699989 = 625781) (by norm_num)
theorem B2083037 : Blo 1387513 2083037 := bbase (se 3 (by rfl) ⟨390569, by rfl⟩ : syracuseStep 2083037 = 781139) (by norm_num)
theorem B2083061 : Blo 1387513 2083061 := bbase (se 5 (by rfl) ⟨97643, by rfl⟩ : syracuseStep 2083061 = 195287) (by norm_num)
theorem B4688117 : Blo 1387513 4688117 := bbase (se 5 (by rfl) ⟨219755, by rfl⟩ : syracuseStep 4688117 = 439511) (by norm_num)
theorem B8448245 : Blo 1387513 8448245 := bbase (se 5 (by rfl) ⟨396011, by rfl⟩ : syracuseStep 8448245 = 792023) (by norm_num)
theorem B2083085 : Blo 1387513 2083085 := bbase (se 3 (by rfl) ⟨390578, by rfl⟩ : syracuseStep 2083085 = 781157) (by norm_num)
theorem B3123485 : Blo 1387513 3123485 := bbase (se 3 (by rfl) ⟨585653, by rfl⟩ : syracuseStep 3123485 = 1171307) (by norm_num)
theorem B2083109 : Blo 1387513 2083109 := bbase (se 4 (by rfl) ⟨195291, by rfl⟩ : syracuseStep 2083109 = 390583) (by norm_num)
theorem B1648945 : Blo 1387513 1648945 := bbase (se 2 (by rfl) ⟨618354, by rfl⟩ : syracuseStep 1648945 = 1236709) (by norm_num)
theorem B2083133 : Blo 1387513 2083133 := bbase (se 3 (by rfl) ⟨390587, by rfl⟩ : syracuseStep 2083133 = 781175) (by norm_num)
theorem B12831061 : Blo 1387513 12831061 := bbase (se 10 (by rfl) ⟨18795, by rfl⟩ : syracuseStep 12831061 = 37591) (by norm_num)
theorem B2500949 : Blo 1387513 2500949 := bbase (se 10 (by rfl) ⟨3663, by rfl⟩ : syracuseStep 2500949 = 7327) (by norm_num)
theorem B2083157 : Blo 1387513 2083157 := bbase (se 10 (by rfl) ⟨3051, by rfl⟩ : syracuseStep 2083157 = 6103) (by norm_num)
theorem B3123557 : Blo 1387513 3123557 := bbase (se 4 (by rfl) ⟨292833, by rfl⟩ : syracuseStep 3123557 = 585667) (by norm_num)
theorem B2083181 : Blo 1387513 2083181 := bbase (se 3 (by rfl) ⟨390596, by rfl⟩ : syracuseStep 2083181 = 781193) (by norm_num)
theorem B3516797 : Blo 1387513 3516797 := bbase (se 3 (by rfl) ⟨659399, by rfl⟩ : syracuseStep 3516797 = 1318799) (by norm_num)
theorem B2083205 : Blo 1387513 2083205 := bbase (se 4 (by rfl) ⟨195300, by rfl⟩ : syracuseStep 2083205 = 390601) (by norm_num)
theorem B2083229 : Blo 1387513 2083229 := bbase (se 3 (by rfl) ⟨390605, by rfl⟩ : syracuseStep 2083229 = 781211) (by norm_num)
theorem B3123629 : Blo 1387513 3123629 := bbase (se 3 (by rfl) ⟨585680, by rfl⟩ : syracuseStep 3123629 = 1171361) (by norm_num)
theorem B2083253 : Blo 1387513 2083253 := bbase (se 5 (by rfl) ⟨97652, by rfl⟩ : syracuseStep 2083253 = 195305) (by norm_num)
theorem B2083277 : Blo 1387513 2083277 := bbase (se 3 (by rfl) ⟨390614, by rfl⟩ : syracuseStep 2083277 = 781229) (by norm_num)
theorem B2083301 : Blo 1387513 2083301 := bbase (se 4 (by rfl) ⟨195309, by rfl⟩ : syracuseStep 2083301 = 390619) (by norm_num)
theorem B3123701 : Blo 1387513 3123701 := bbase (se 5 (by rfl) ⟨146423, by rfl⟩ : syracuseStep 3123701 = 292847) (by norm_num)
theorem B7031285 : Blo 1387513 7031285 := bbase (se 5 (by rfl) ⟨329591, by rfl⟩ : syracuseStep 7031285 = 659183) (by norm_num)
theorem B2083325 : Blo 1387513 2083325 := bbase (se 3 (by rfl) ⟨390623, by rfl⟩ : syracuseStep 2083325 = 781247) (by norm_num)
theorem B2083349 : Blo 1387513 2083349 := bbase (se 6 (by rfl) ⟨48828, by rfl⟩ : syracuseStep 2083349 = 97657) (by norm_num)
theorem B2083373 : Blo 1387513 2083373 := bbase (se 3 (by rfl) ⟨390632, by rfl⟩ : syracuseStep 2083373 = 781265) (by norm_num)
theorem B3123773 : Blo 1387513 3123773 := bbase (se 3 (by rfl) ⟨585707, by rfl⟩ : syracuseStep 3123773 = 1171415) (by norm_num)
theorem B2083397 : Blo 1387513 2083397 := bbase (se 4 (by rfl) ⟨195318, by rfl⟩ : syracuseStep 2083397 = 390637) (by norm_num)
theorem B2083421 : Blo 1387513 2083421 := bbase (se 3 (by rfl) ⟨390641, by rfl⟩ : syracuseStep 2083421 = 781283) (by norm_num)
theorem B2083445 : Blo 1387513 2083445 := bbase (se 5 (by rfl) ⟨97661, by rfl⟩ : syracuseStep 2083445 = 195323) (by norm_num)
theorem B3123845 : Blo 1387513 3123845 := bbase (se 4 (by rfl) ⟨292860, by rfl⟩ : syracuseStep 3123845 = 585721) (by norm_num)
theorem B2083469 : Blo 1387513 2083469 := bbase (se 3 (by rfl) ⟨390650, by rfl⟩ : syracuseStep 2083469 = 781301) (by norm_num)
theorem B2083493 : Blo 1387513 2083493 := bbase (se 4 (by rfl) ⟨195327, by rfl⟩ : syracuseStep 2083493 = 390655) (by norm_num)
theorem B4688549 : Blo 1387513 4688549 := bbase (se 4 (by rfl) ⟨439551, by rfl⟩ : syracuseStep 4688549 = 879103) (by norm_num)
theorem B2083517 : Blo 1387513 2083517 := bbase (se 3 (by rfl) ⟨390659, by rfl⟩ : syracuseStep 2083517 = 781319) (by norm_num)
theorem B3123917 : Blo 1387513 3123917 := bbase (se 3 (by rfl) ⟨585734, by rfl⟩ : syracuseStep 3123917 = 1171469) (by norm_num)
theorem B3951317 : Blo 1387513 3951317 := bbase (se 7 (by rfl) ⟨46304, by rfl⟩ : syracuseStep 3951317 = 92609) (by norm_num)
theorem B2083541 : Blo 1387513 2083541 := bbase (se 7 (by rfl) ⟨24416, by rfl⟩ : syracuseStep 2083541 = 48833) (by norm_num)
theorem B3517141 : Blo 1387513 3517141 := bbase (se 7 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 3517141 = 82433) (by norm_num)
theorem B2083565 : Blo 1387513 2083565 := bbase (se 3 (by rfl) ⟨390668, by rfl⟩ : syracuseStep 2083565 = 781337) (by norm_num)
theorem B2083589 : Blo 1387513 2083589 := bbase (se 4 (by rfl) ⟨195336, by rfl⟩ : syracuseStep 2083589 = 390673) (by norm_num)
theorem B3123989 : Blo 1387513 3123989 := bbase (se 6 (by rfl) ⟨73218, by rfl⟩ : syracuseStep 3123989 = 146437) (by norm_num)
theorem B2083613 : Blo 1387513 2083613 := bbase (se 3 (by rfl) ⟨390677, by rfl⟩ : syracuseStep 2083613 = 781355) (by norm_num)
theorem B2083637 : Blo 1387513 2083637 := bbase (se 5 (by rfl) ⟨97670, by rfl⟩ : syracuseStep 2083637 = 195341) (by norm_num)
theorem B2255669 : Blo 1387513 2255669 := bbase (se 5 (by rfl) ⟨105734, by rfl⟩ : syracuseStep 2255669 = 211469) (by norm_num)
theorem B2083661 : Blo 1387513 2083661 := bbase (se 3 (by rfl) ⟨390686, by rfl⟩ : syracuseStep 2083661 = 781373) (by norm_num)
theorem B3124061 : Blo 1387513 3124061 := bbase (se 3 (by rfl) ⟨585761, by rfl⟩ : syracuseStep 3124061 = 1171523) (by norm_num)
theorem B2083685 : Blo 1387513 2083685 := bbase (se 4 (by rfl) ⟨195345, by rfl⟩ : syracuseStep 2083685 = 390691) (by norm_num)
theorem B2083709 : Blo 1387513 2083709 := bbase (se 3 (by rfl) ⟨390695, by rfl⟩ : syracuseStep 2083709 = 781391) (by norm_num)
theorem B2083733 : Blo 1387513 2083733 := bbase (se 6 (by rfl) ⟨48837, by rfl⟩ : syracuseStep 2083733 = 97675) (by norm_num)
theorem B3124133 : Blo 1387513 3124133 := bbase (se 4 (by rfl) ⟨292887, by rfl⟩ : syracuseStep 3124133 = 585775) (by norm_num)
theorem B2083757 : Blo 1387513 2083757 := bbase (se 3 (by rfl) ⟨390704, by rfl⟩ : syracuseStep 2083757 = 781409) (by norm_num)
theorem B2083781 : Blo 1387513 2083781 := bbase (se 4 (by rfl) ⟨195354, by rfl⟩ : syracuseStep 2083781 = 390709) (by norm_num)
theorem B2083805 : Blo 1387513 2083805 := bbase (se 3 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 2083805 = 781427) (by norm_num)
theorem B3124205 : Blo 1387513 3124205 := bbase (se 3 (by rfl) ⟨585788, by rfl⟩ : syracuseStep 3124205 = 1171577) (by norm_num)
theorem B2083829 : Blo 1387513 2083829 := bbase (se 5 (by rfl) ⟨97679, by rfl⟩ : syracuseStep 2083829 = 195359) (by norm_num)
theorem B2083853 : Blo 1387513 2083853 := bbase (se 3 (by rfl) ⟨390722, by rfl⟩ : syracuseStep 2083853 = 781445) (by norm_num)
theorem B2141197 : Blo 1387513 2141197 := bbase (se 3 (by rfl) ⟨401474, by rfl⟩ : syracuseStep 2141197 = 802949) (by norm_num)
theorem B1756181 : Blo 1387513 1756181 := bbase (se 6 (by rfl) ⟨41160, by rfl⟩ : syracuseStep 1756181 = 82321) (by norm_num)
theorem B2083877 : Blo 1387513 2083877 := bbase (se 4 (by rfl) ⟨195363, by rfl⟩ : syracuseStep 2083877 = 390727) (by norm_num)
theorem B3124277 : Blo 1387513 3124277 := bbase (se 5 (by rfl) ⟨146450, by rfl⟩ : syracuseStep 3124277 = 292901) (by norm_num)
theorem B2083901 : Blo 1387513 2083901 := bbase (se 3 (by rfl) ⟨390731, by rfl⟩ : syracuseStep 2083901 = 781463) (by norm_num)
theorem B1756237 : Blo 1387513 1756237 := bbase (se 3 (by rfl) ⟨329294, by rfl⟩ : syracuseStep 1756237 = 658589) (by norm_num)
theorem B2083925 : Blo 1387513 2083925 := bbase (se 8 (by rfl) ⟨12210, by rfl⟩ : syracuseStep 2083925 = 24421) (by norm_num)
theorem B4688981 : Blo 1387513 4688981 := bbase (se 8 (by rfl) ⟨27474, by rfl⟩ : syracuseStep 4688981 = 54949) (by norm_num)
theorem B2083949 : Blo 1387513 2083949 := bbase (se 3 (by rfl) ⟨390740, by rfl⟩ : syracuseStep 2083949 = 781481) (by norm_num)
theorem B3124349 : Blo 1387513 3124349 := bbase (se 3 (by rfl) ⟨585815, by rfl⟩ : syracuseStep 3124349 = 1171631) (by norm_num)
theorem B2083973 : Blo 1387513 2083973 := bbase (se 4 (by rfl) ⟨195372, by rfl⟩ : syracuseStep 2083973 = 390745) (by norm_num)
theorem B2083997 : Blo 1387513 2083997 := bbase (se 3 (by rfl) ⟨390749, by rfl⟩ : syracuseStep 2083997 = 781499) (by norm_num)
theorem B1690789 : Blo 1387513 1690789 := bbase (se 4 (by rfl) ⟨158511, by rfl⟩ : syracuseStep 1690789 = 317023) (by norm_num)
theorem B1756333 : Blo 1387513 1756333 := bbase (se 3 (by rfl) ⟨329312, by rfl⟩ : syracuseStep 1756333 = 658625) (by norm_num)
theorem B2084021 : Blo 1387513 2084021 := bbase (se 5 (by rfl) ⟨97688, by rfl⟩ : syracuseStep 2084021 = 195377) (by norm_num)
theorem B3124421 : Blo 1387513 3124421 := bbase (se 4 (by rfl) ⟨292914, by rfl⟩ : syracuseStep 3124421 = 585829) (by norm_num)
theorem B2084045 : Blo 1387513 2084045 := bbase (se 3 (by rfl) ⟨390758, by rfl⟩ : syracuseStep 2084045 = 781517) (by norm_num)
theorem B58576085 : Blo 1387513 58576085 := bbase (se 7 (by rfl) ⟨686438, by rfl⟩ : syracuseStep 58576085 = 1372877) (by norm_num)
theorem B2084069 : Blo 1387513 2084069 := bbase (se 4 (by rfl) ⟨195381, by rfl⟩ : syracuseStep 2084069 = 390763) (by norm_num)
theorem B2084093 : Blo 1387513 2084093 := bbase (se 3 (by rfl) ⟨390767, by rfl⟩ : syracuseStep 2084093 = 781535) (by norm_num)
theorem B3124493 : Blo 1387513 3124493 := bbase (se 3 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 3124493 = 1171685) (by norm_num)
theorem B11865365 : Blo 1387513 11865365 := bbase (se 6 (by rfl) ⟨278094, by rfl⟩ : syracuseStep 11865365 = 556189) (by norm_num)
theorem B2084117 : Blo 1387513 2084117 := bbase (se 6 (by rfl) ⟨48846, by rfl⟩ : syracuseStep 2084117 = 97693) (by norm_num)
theorem B2084141 : Blo 1387513 2084141 := bbase (se 3 (by rfl) ⟨390776, by rfl⟩ : syracuseStep 2084141 = 781553) (by norm_num)
theorem B2084165 : Blo 1387513 2084165 := bbase (se 4 (by rfl) ⟨195390, by rfl⟩ : syracuseStep 2084165 = 390781) (by norm_num)
theorem B3124565 : Blo 1387513 3124565 := bbase (se 11 (by rfl) ⟨2288, by rfl⟩ : syracuseStep 3124565 = 4577) (by norm_num)
theorem B1756505 : Blo 1387513 1756505 := bbase (se 2 (by rfl) ⟨658689, by rfl⟩ : syracuseStep 1756505 = 1317379) (by norm_num)
theorem B2084189 : Blo 1387513 2084189 := bbase (se 3 (by rfl) ⟨390785, by rfl⟩ : syracuseStep 2084189 = 781571) (by norm_num)
theorem B1977709 : Blo 1387513 1977709 := bbase (se 3 (by rfl) ⟨370820, by rfl⟩ : syracuseStep 1977709 = 741641) (by norm_num)
theorem B2084213 : Blo 1387513 2084213 := bbase (se 5 (by rfl) ⟨97697, by rfl⟩ : syracuseStep 2084213 = 195395) (by norm_num)
theorem B6761861 : Blo 1387513 6761861 := bbase (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) (by norm_num)
theorem B2502029 : Blo 1387513 2502029 := bbase (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) (by norm_num)
theorem B2084237 : Blo 1387513 2084237 := bbase (se 3 (by rfl) ⟨390794, by rfl⟩ : syracuseStep 2084237 = 781589) (by norm_num)
theorem B1756561 : Blo 1387513 1756561 := bbase (se 2 (by rfl) ⟨658710, by rfl⟩ : syracuseStep 1756561 = 1317421) (by norm_num)
theorem B3124637 : Blo 1387513 3124637 := bbase (se 3 (by rfl) ⟨585869, by rfl⟩ : syracuseStep 3124637 = 1171739) (by norm_num)
theorem B2084261 : Blo 1387513 2084261 := bbase (se 4 (by rfl) ⟨195399, by rfl⟩ : syracuseStep 2084261 = 390799) (by norm_num)
theorem B1445333 : Blo 1387513 1445333 := bbase (se 7 (by rfl) ⟨16937, by rfl⟩ : syracuseStep 1445333 = 33875) (by norm_num)
theorem B3124709 : Blo 1387513 3124709 := bbase (se 4 (by rfl) ⟨292941, by rfl⟩ : syracuseStep 3124709 = 585883) (by norm_num)
theorem B1756657 : Blo 1387513 1756657 := bbase (se 2 (by rfl) ⟨658746, by rfl⟩ : syracuseStep 1756657 = 1317493) (by norm_num)
theorem B4689413 : Blo 1387513 4689413 := bbase (se 4 (by rfl) ⟨439632, by rfl⟩ : syracuseStep 4689413 = 879265) (by norm_num)
theorem B2223629 : Blo 1387513 2223629 := bbase (se 3 (by rfl) ⟨416930, by rfl⟩ : syracuseStep 2223629 = 833861) (by norm_num)
theorem B3124781 : Blo 1387513 3124781 := bbase (se 3 (by rfl) ⟨585896, by rfl⟩ : syracuseStep 3124781 = 1171793) (by norm_num)
theorem B2502253 : Blo 1387513 2502253 := bbase (se 3 (by rfl) ⟨469172, by rfl⟩ : syracuseStep 2502253 = 938345) (by norm_num)
theorem B3124853 : Blo 1387513 3124853 := bbase (se 5 (by rfl) ⟨146477, by rfl⟩ : syracuseStep 3124853 = 292955) (by norm_num)
theorem B1756829 : Blo 1387513 1756829 := bbase (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) (by norm_num)
theorem B3124925 : Blo 1387513 3124925 := bbase (se 3 (by rfl) ⟨585923, by rfl⟩ : syracuseStep 3124925 = 1171847) (by norm_num)
theorem B2223821 : Blo 1387513 2223821 := bbase (se 3 (by rfl) ⟨416966, by rfl⟩ : syracuseStep 2223821 = 833933) (by norm_num)
theorem B1756885 : Blo 1387513 1756885 := bbase (se 7 (by rfl) ⟨20588, by rfl⟩ : syracuseStep 1756885 = 41177) (by norm_num)
theorem B1781497 : Blo 1387513 1781497 := bbase (se 2 (by rfl) ⟨668061, by rfl⟩ : syracuseStep 1781497 = 1336123) (by norm_num)
theorem B3124997 : Blo 1387513 3124997 := bbase (se 4 (by rfl) ⟨292968, by rfl⟩ : syracuseStep 3124997 = 585937) (by norm_num)
theorem B7032581 : Blo 1387513 7032581 := bbase (se 4 (by rfl) ⟨659304, by rfl⟩ : syracuseStep 7032581 = 1318609) (by norm_num)
theorem B3165973 : Blo 1387513 3165973 := bbase (se 6 (by rfl) ⟨74202, by rfl⟩ : syracuseStep 3165973 = 148405) (by norm_num)
theorem B1756981 : Blo 1387513 1756981 := bbase (se 5 (by rfl) ⟨82358, by rfl⟩ : syracuseStep 1756981 = 164717) (by norm_num)
theorem B2223949 : Blo 1387513 2223949 := bbase (se 3 (by rfl) ⟨416990, by rfl⟩ : syracuseStep 2223949 = 833981) (by norm_num)
theorem B3125069 : Blo 1387513 3125069 := bbase (se 3 (by rfl) ⟨585950, by rfl⟩ : syracuseStep 3125069 = 1171901) (by norm_num)
theorem B2854765 : Blo 1387513 2854765 := bbase (se 3 (by rfl) ⟨535268, by rfl⟩ : syracuseStep 2854765 = 1070537) (by norm_num)
theorem B4747157 : Blo 1387513 4747157 := bbase (se 6 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 4747157 = 222523) (by norm_num)
theorem B3125141 : Blo 1387513 3125141 := bbase (se 6 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 3125141 = 146491) (by norm_num)
theorem B1781677 : Blo 1387513 1781677 := bbase (se 3 (by rfl) ⟨334064, by rfl⟩ : syracuseStep 1781677 = 668129) (by norm_num)
theorem B1978301 : Blo 1387513 1978301 := bbase (se 3 (by rfl) ⟨370931, by rfl⟩ : syracuseStep 1978301 = 741863) (by norm_num)
theorem B4337621 : Blo 1387513 4337621 := bbase (se 7 (by rfl) ⟨50831, by rfl⟩ : syracuseStep 4337621 = 101663) (by norm_num)
theorem B2002909 : Blo 1387513 2002909 := bbase (se 3 (by rfl) ⟨375545, by rfl⟩ : syracuseStep 2002909 = 751091) (by norm_num)
theorem B3125213 : Blo 1387513 3125213 := bbase (se 3 (by rfl) ⟨585977, by rfl⟩ : syracuseStep 3125213 = 1171955) (by norm_num)
theorem B1757153 : Blo 1387513 1757153 := bbase (se 2 (by rfl) ⟨658932, by rfl⟩ : syracuseStep 1757153 = 1317865) (by norm_num)
theorem B1978381 : Blo 1387513 1978381 := bbase (se 3 (by rfl) ⟨370946, by rfl⟩ : syracuseStep 1978381 = 741893) (by norm_num)
theorem B1757209 : Blo 1387513 1757209 := bbase (se 2 (by rfl) ⟨658953, by rfl⟩ : syracuseStep 1757209 = 1317907) (by norm_num)
theorem B3125285 : Blo 1387513 3125285 := bbase (se 4 (by rfl) ⟨292995, by rfl⟩ : syracuseStep 3125285 = 585991) (by norm_num)
theorem B3608653 : Blo 1387513 3608653 := bbase (se 3 (by rfl) ⟨676622, by rfl⟩ : syracuseStep 3608653 = 1353245) (by norm_num)
theorem B3125357 : Blo 1387513 3125357 := bbase (se 3 (by rfl) ⟨586004, by rfl⟩ : syracuseStep 3125357 = 1172009) (by norm_num)
theorem B1757305 : Blo 1387513 1757305 := bbase (se 2 (by rfl) ⟨658989, by rfl⟩ : syracuseStep 1757305 = 1317979) (by norm_num)
theorem B4509829 : Blo 1387513 4509829 := bbase (se 4 (by rfl) ⟨422796, by rfl⟩ : syracuseStep 4509829 = 845593) (by norm_num)
theorem B7024805 : Blo 1387513 7024805 := bbase (se 4 (by rfl) ⟨658575, by rfl⟩ : syracuseStep 7024805 = 1317151) (by norm_num)
theorem B1781929 : Blo 1387513 1781929 := bbase (se 2 (by rfl) ⟨668223, by rfl⟩ : syracuseStep 1781929 = 1336447) (by norm_num)
theorem B3125429 : Blo 1387513 3125429 := bbase (se 5 (by rfl) ⟨146504, by rfl⟩ : syracuseStep 3125429 = 293009) (by norm_num)
theorem B5271749 : Blo 1387513 5271749 := bbase (se 4 (by rfl) ⟨494226, by rfl⟩ : syracuseStep 5271749 = 988453) (by norm_num)
theorem B3125501 : Blo 1387513 3125501 := bbase (se 3 (by rfl) ⟨586031, by rfl⟩ : syracuseStep 3125501 = 1172063) (by norm_num)
theorem B3952901 : Blo 1387513 3952901 := bbase (se 4 (by rfl) ⟨370584, by rfl⟩ : syracuseStep 3952901 = 741169) (by norm_num)
theorem B1757477 : Blo 1387513 1757477 := bbase (se 4 (by rfl) ⟨164763, by rfl⟩ : syracuseStep 1757477 = 329527) (by norm_num)
theorem B3125573 : Blo 1387513 3125573 := bbase (se 4 (by rfl) ⟨293022, by rfl⟩ : syracuseStep 3125573 = 586045) (by norm_num)
theorem B1757533 : Blo 1387513 1757533 := bbase (se 3 (by rfl) ⟨329537, by rfl⟩ : syracuseStep 1757533 = 659075) (by norm_num)
theorem B10015093 : Blo 1387513 10015093 := bbase (se 5 (by rfl) ⟨469457, by rfl⟩ : syracuseStep 10015093 = 938915) (by norm_num)
theorem B1560973 : Blo 1387513 1560973 := bbase (se 3 (by rfl) ⟨292682, by rfl⟩ : syracuseStep 1560973 = 585365) (by norm_num)
theorem B3125645 : Blo 1387513 3125645 := bbase (se 3 (by rfl) ⟨586058, by rfl⟩ : syracuseStep 3125645 = 1172117) (by norm_num)
theorem B3658133 : Blo 1387513 3658133 := bbase (se 6 (by rfl) ⟨85737, by rfl⟩ : syracuseStep 3658133 = 171475) (by norm_num)
theorem B8892821 : Blo 1387513 8892821 := bbase (se 6 (by rfl) ⟨208425, by rfl⟩ : syracuseStep 8892821 = 416851) (by norm_num)
theorem B15020437 : Blo 1387513 15020437 := bbase (se 6 (by rfl) ⟨352041, by rfl⟩ : syracuseStep 15020437 = 704083) (by norm_num)
theorem B1561009 : Blo 1387513 1561009 := bbase (se 2 (by rfl) ⟨585378, by rfl⟩ : syracuseStep 1561009 = 1170757) (by norm_num)
theorem B1757629 : Blo 1387513 1757629 := bbase (se 3 (by rfl) ⟨329555, by rfl⟩ : syracuseStep 1757629 = 659111) (by norm_num)
theorem B2224589 : Blo 1387513 2224589 := bbase (se 3 (by rfl) ⟨417110, by rfl⟩ : syracuseStep 2224589 = 834221) (by norm_num)
theorem B1561045 : Blo 1387513 1561045 := bbase (se 7 (by rfl) ⟨18293, by rfl⟩ : syracuseStep 1561045 = 36587) (by norm_num)
theorem B3125717 : Blo 1387513 3125717 := bbase (se 7 (by rfl) ⟨36629, by rfl⟩ : syracuseStep 3125717 = 73259) (by norm_num)
theorem B5272037 : Blo 1387513 5272037 := bbase (se 4 (by rfl) ⟨494253, by rfl⟩ : syracuseStep 5272037 = 988507) (by norm_num)
theorem B2535925 : Blo 1387513 2535925 := bbase (se 5 (by rfl) ⟨118871, by rfl⟩ : syracuseStep 2535925 = 237743) (by norm_num)
theorem B1561081 : Blo 1387513 1561081 := bbase (se 2 (by rfl) ⟨585405, by rfl⟩ : syracuseStep 1561081 = 1170811) (by norm_num)
theorem B1561117 : Blo 1387513 1561117 := bbase (se 3 (by rfl) ⟨292709, by rfl⟩ : syracuseStep 1561117 = 585419) (by norm_num)
theorem B3125789 : Blo 1387513 3125789 := bbase (se 3 (by rfl) ⟨586085, by rfl⟩ : syracuseStep 3125789 = 1172171) (by norm_num)
theorem B1561153 : Blo 1387513 1561153 := bbase (se 2 (by rfl) ⟨585432, by rfl⟩ : syracuseStep 1561153 = 1170865) (by norm_num)
theorem B1561189 : Blo 1387513 1561189 := bbase (se 4 (by rfl) ⟨146361, by rfl⟩ : syracuseStep 1561189 = 292723) (by norm_num)
theorem B3125861 : Blo 1387513 3125861 := bbase (se 4 (by rfl) ⟨293049, by rfl⟩ : syracuseStep 3125861 = 586099) (by norm_num)
theorem B1757801 : Blo 1387513 1757801 := bbase (se 2 (by rfl) ⟨659175, by rfl⟩ : syracuseStep 1757801 = 1318351) (by norm_num)
theorem B5345909 : Blo 1387513 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B1561225 : Blo 1387513 1561225 := bbase (se 2 (by rfl) ⟨585459, by rfl⟩ : syracuseStep 1561225 = 1170919) (by norm_num)
theorem B1757857 : Blo 1387513 1757857 := bbase (se 2 (by rfl) ⟨659196, by rfl⟩ : syracuseStep 1757857 = 1318393) (by norm_num)
theorem B1561261 : Blo 1387513 1561261 := bbase (se 3 (by rfl) ⟨292736, by rfl⟩ : syracuseStep 1561261 = 585473) (by norm_num)
theorem B3125933 : Blo 1387513 3125933 := bbase (se 3 (by rfl) ⟨586112, by rfl⟩ : syracuseStep 3125933 = 1172225) (by norm_num)
theorem B2003653 : Blo 1387513 2003653 := bbase (se 4 (by rfl) ⟨187842, by rfl⟩ : syracuseStep 2003653 = 375685) (by norm_num)
theorem B1561297 : Blo 1387513 1561297 := bbase (se 2 (by rfl) ⟨585486, by rfl⟩ : syracuseStep 1561297 = 1170973) (by norm_num)
theorem B1561333 : Blo 1387513 1561333 := bbase (se 5 (by rfl) ⟨73187, by rfl⟩ : syracuseStep 1561333 = 146375) (by norm_num)
theorem B3126005 : Blo 1387513 3126005 := bbase (se 5 (by rfl) ⟨146531, by rfl⟩ : syracuseStep 3126005 = 293063) (by norm_num)
theorem B1757953 : Blo 1387513 1757953 := bbase (se 2 (by rfl) ⟨659232, by rfl⟩ : syracuseStep 1757953 = 1318465) (by norm_num)
theorem B1561369 : Blo 1387513 1561369 := bbase (se 2 (by rfl) ⟨585513, by rfl⟩ : syracuseStep 1561369 = 1171027) (by norm_num)
theorem B1561405 : Blo 1387513 1561405 := bbase (se 3 (by rfl) ⟨292763, by rfl⟩ : syracuseStep 1561405 = 585527) (by norm_num)
theorem B3126077 : Blo 1387513 3126077 := bbase (se 3 (by rfl) ⟨586139, by rfl⟩ : syracuseStep 3126077 = 1172279) (by norm_num)
theorem B10695509 : Blo 1387513 10695509 := bbase (se 9 (by rfl) ⟨31334, by rfl⟩ : syracuseStep 10695509 = 62669) (by norm_num)
theorem B1561441 : Blo 1387513 1561441 := bbase (se 2 (by rfl) ⟨585540, by rfl⟩ : syracuseStep 1561441 = 1171081) (by norm_num)
theorem B3208061 : Blo 1387513 3208061 := bbase (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) (by norm_num)
theorem B1561477 : Blo 1387513 1561477 := bbase (se 4 (by rfl) ⟨146388, by rfl⟩ : syracuseStep 1561477 = 292777) (by norm_num)
theorem B3126149 : Blo 1387513 3126149 := bbase (se 4 (by rfl) ⟨293076, by rfl⟩ : syracuseStep 3126149 = 586153) (by norm_num)
theorem B2110357 : Blo 1387513 2110357 := bbase (se 6 (by rfl) ⟨49461, by rfl⟩ : syracuseStep 2110357 = 98923) (by norm_num)
theorem B2225045 : Blo 1387513 2225045 := bbase (se 6 (by rfl) ⟨52149, by rfl⟩ : syracuseStep 2225045 = 104299) (by norm_num)
theorem B3953573 : Blo 1387513 3953573 := bbase (se 4 (by rfl) ⟨370647, by rfl⟩ : syracuseStep 3953573 = 741295) (by norm_num)
theorem B1561513 : Blo 1387513 1561513 := bbase (se 2 (by rfl) ⟨585567, by rfl⟩ : syracuseStep 1561513 = 1171135) (by norm_num)
theorem B1758125 : Blo 1387513 1758125 := bbase (se 3 (by rfl) ⟨329648, by rfl⟩ : syracuseStep 1758125 = 659297) (by norm_num)
theorem B1561549 : Blo 1387513 1561549 := bbase (se 3 (by rfl) ⟨292790, by rfl⟩ : syracuseStep 1561549 = 585581) (by norm_num)
theorem B3126221 : Blo 1387513 3126221 := bbase (se 3 (by rfl) ⟨586166, by rfl⟩ : syracuseStep 3126221 = 1172333) (by norm_num)
theorem B9630677 : Blo 1387513 9630677 := bbase (se 7 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 9630677 = 225719) (by norm_num)
theorem B2503637 : Blo 1387513 2503637 := bbase (se 7 (by rfl) ⟨29339, by rfl⟩ : syracuseStep 2503637 = 58679) (by norm_num)
theorem B1758181 : Blo 1387513 1758181 := bbase (se 4 (by rfl) ⟨164829, by rfl⟩ : syracuseStep 1758181 = 329659) (by norm_num)
theorem B1561585 : Blo 1387513 1561585 := bbase (se 2 (by rfl) ⟨585594, by rfl⟩ : syracuseStep 1561585 = 1171189) (by norm_num)
theorem B1561621 : Blo 1387513 1561621 := bbase (se 6 (by rfl) ⟨36600, by rfl⟩ : syracuseStep 1561621 = 73201) (by norm_num)
theorem B7033877 : Blo 1387513 7033877 := bbase (se 6 (by rfl) ⟨164856, by rfl⟩ : syracuseStep 7033877 = 329713) (by norm_num)
theorem B3126293 : Blo 1387513 3126293 := bbase (se 6 (by rfl) ⟨73272, by rfl⟩ : syracuseStep 3126293 = 146545) (by norm_num)
theorem B2634781 : Blo 1387513 2634781 := bbase (se 3 (by rfl) ⟨494021, by rfl⟩ : syracuseStep 2634781 = 988043) (by norm_num)
theorem B1561657 : Blo 1387513 1561657 := bbase (se 2 (by rfl) ⟨585621, by rfl⟩ : syracuseStep 1561657 = 1171243) (by norm_num)
theorem B1758277 : Blo 1387513 1758277 := bbase (se 4 (by rfl) ⟨164838, by rfl⟩ : syracuseStep 1758277 = 329677) (by norm_num)
theorem B1668173 : Blo 1387513 1668173 := bbase (se 3 (by rfl) ⟨312782, by rfl⟩ : syracuseStep 1668173 = 625565) (by norm_num)
theorem B1561693 : Blo 1387513 1561693 := bbase (se 3 (by rfl) ⟨292817, by rfl⟩ : syracuseStep 1561693 = 585635) (by norm_num)
theorem B3126365 : Blo 1387513 3126365 := bbase (se 3 (by rfl) ⟨586193, by rfl⟩ : syracuseStep 3126365 = 1172387) (by norm_num)
theorem B2225269 : Blo 1387513 2225269 := bbase (se 5 (by rfl) ⟨104309, by rfl⟩ : syracuseStep 2225269 = 208619) (by norm_num)
theorem B1447033 : Blo 1387513 1447033 := bbase (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) (by norm_num)
theorem B3560573 : Blo 1387513 3560573 := bbase (se 3 (by rfl) ⟨667607, by rfl⟩ : syracuseStep 3560573 = 1335215) (by norm_num)
theorem B1561729 : Blo 1387513 1561729 := bbase (se 2 (by rfl) ⟨585648, by rfl⟩ : syracuseStep 1561729 = 1171297) (by norm_num)
theorem B1561765 : Blo 1387513 1561765 := bbase (se 4 (by rfl) ⟨146415, by rfl⟩ : syracuseStep 1561765 = 292831) (by norm_num)
theorem B2634925 : Blo 1387513 2634925 := bbase (se 3 (by rfl) ⟨494048, by rfl⟩ : syracuseStep 2634925 = 988097) (by norm_num)
theorem B4682933 : Blo 1387513 4682933 := bbase (se 5 (by rfl) ⟨219512, by rfl⟩ : syracuseStep 4682933 = 439025) (by norm_num)
theorem B2225333 : Blo 1387513 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B2815165 : Blo 1387513 2815165 := bbase (se 3 (by rfl) ⟨527843, by rfl⟩ : syracuseStep 2815165 = 1055687) (by norm_num)
theorem B1561801 : Blo 1387513 1561801 := bbase (se 2 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 1561801 = 1171351) (by norm_num)
theorem B2110693 : Blo 1387513 2110693 := bbase (se 4 (by rfl) ⟨197877, by rfl⟩ : syracuseStep 2110693 = 395755) (by norm_num)
theorem B1561837 : Blo 1387513 1561837 := bbase (se 3 (by rfl) ⟨292844, by rfl⟩ : syracuseStep 1561837 = 585689) (by norm_num)
theorem B1758449 : Blo 1387513 1758449 := bbase (se 2 (by rfl) ⟨659418, by rfl⟩ : syracuseStep 1758449 = 1318837) (by norm_num)
theorem B5002501 : Blo 1387513 5002501 := bbase (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) (by norm_num)
theorem B1561873 : Blo 1387513 1561873 := bbase (se 2 (by rfl) ⟨585702, by rfl⟩ : syracuseStep 1561873 = 1171405) (by norm_num)
theorem B1668385 : Blo 1387513 1668385 := bbase (se 2 (by rfl) ⟨625644, by rfl⟩ : syracuseStep 1668385 = 1251289) (by norm_num)
theorem B1758505 : Blo 1387513 1758505 := bbase (se 2 (by rfl) ⟨659439, by rfl⟩ : syracuseStep 1758505 = 1318879) (by norm_num)
theorem B1561909 : Blo 1387513 1561909 := bbase (se 5 (by rfl) ⟨73214, by rfl⟩ : syracuseStep 1561909 = 146429) (by norm_num)
theorem B2225461 : Blo 1387513 2225461 := bbase (se 5 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 2225461 = 208637) (by norm_num)
theorem B2635085 : Blo 1387513 2635085 := bbase (se 3 (by rfl) ⟨494078, by rfl⟩ : syracuseStep 2635085 = 988157) (by norm_num)
theorem B3954005 : Blo 1387513 3954005 := bbase (se 16 (by rfl) ⟨90, by rfl⟩ : syracuseStep 3954005 = 181) (by norm_num)
theorem B1561945 : Blo 1387513 1561945 := bbase (se 2 (by rfl) ⟨585729, by rfl⟩ : syracuseStep 1561945 = 1171459) (by norm_num)
theorem B1561981 : Blo 1387513 1561981 := bbase (se 3 (by rfl) ⟨292871, by rfl⟩ : syracuseStep 1561981 = 585743) (by norm_num)
theorem B1758601 : Blo 1387513 1758601 := bbase (se 2 (by rfl) ⟨659475, by rfl⟩ : syracuseStep 1758601 = 1318951) (by norm_num)
theorem B10548629 : Blo 1387513 10548629 := bbase (se 6 (by rfl) ⟨247233, by rfl⟩ : syracuseStep 10548629 = 494467) (by norm_num)
theorem B1562017 : Blo 1387513 1562017 := bbase (se 2 (by rfl) ⟨585756, by rfl⟩ : syracuseStep 1562017 = 1171513) (by norm_num)
theorem B5002661 : Blo 1387513 5002661 := bbase (se 4 (by rfl) ⟨468999, by rfl⟩ : syracuseStep 5002661 = 937999) (by norm_num)
theorem B7026101 : Blo 1387513 7026101 := bbase (se 5 (by rfl) ⟨329348, by rfl⟩ : syracuseStep 7026101 = 658697) (by norm_num)
theorem B1668529 : Blo 1387513 1668529 := bbase (se 2 (by rfl) ⟨625698, by rfl⟩ : syracuseStep 1668529 = 1251397) (by norm_num)
theorem B1562053 : Blo 1387513 1562053 := bbase (se 4 (by rfl) ⟨146442, by rfl⟩ : syracuseStep 1562053 = 292885) (by norm_num)
theorem B2635229 : Blo 1387513 2635229 := bbase (se 3 (by rfl) ⟨494105, by rfl⟩ : syracuseStep 2635229 = 988211) (by norm_num)
theorem B1562089 : Blo 1387513 1562089 := bbase (se 2 (by rfl) ⟨585783, by rfl⟩ : syracuseStep 1562089 = 1171567) (by norm_num)
theorem B1562125 : Blo 1387513 1562125 := bbase (se 3 (by rfl) ⟨292898, by rfl⟩ : syracuseStep 1562125 = 585797) (by norm_num)
theorem B1562161 : Blo 1387513 1562161 := bbase (se 2 (by rfl) ⟨585810, by rfl⟩ : syracuseStep 1562161 = 1171621) (by norm_num)
theorem B1562197 : Blo 1387513 1562197 := bbase (se 8 (by rfl) ⟨9153, by rfl⟩ : syracuseStep 1562197 = 18307) (by norm_num)
theorem B4683365 : Blo 1387513 4683365 := bbase (se 4 (by rfl) ⟨439065, by rfl⟩ : syracuseStep 4683365 = 878131) (by norm_num)
theorem B1562233 : Blo 1387513 1562233 := bbase (se 2 (by rfl) ⟨585837, by rfl⟩ : syracuseStep 1562233 = 1171675) (by norm_num)
theorem B5273221 : Blo 1387513 5273221 := bbase (se 4 (by rfl) ⟨494364, by rfl⟩ : syracuseStep 5273221 = 988729) (by norm_num)
theorem B1562269 : Blo 1387513 1562269 := bbase (se 3 (by rfl) ⟨292925, by rfl⟩ : syracuseStep 1562269 = 585851) (by norm_num)
theorem B1562305 : Blo 1387513 1562305 := bbase (se 2 (by rfl) ⟨585864, by rfl⟩ : syracuseStep 1562305 = 1171729) (by norm_num)
theorem B1562341 : Blo 1387513 1562341 := bbase (se 4 (by rfl) ⟨146469, by rfl⟩ : syracuseStep 1562341 = 292939) (by norm_num)
theorem B2635517 : Blo 1387513 2635517 := bbase (se 3 (by rfl) ⟨494159, by rfl⟩ : syracuseStep 2635517 = 988319) (by norm_num)
theorem B1562377 : Blo 1387513 1562377 := bbase (se 2 (by rfl) ⟨585891, by rfl⟩ : syracuseStep 1562377 = 1171783) (by norm_num)
theorem B1562413 : Blo 1387513 1562413 := bbase (se 3 (by rfl) ⟨292952, by rfl⟩ : syracuseStep 1562413 = 585905) (by norm_num)
theorem B10540853 : Blo 1387513 10540853 := bbase (se 5 (by rfl) ⟨494102, by rfl⟩ : syracuseStep 10540853 = 988205) (by norm_num)
theorem B1562449 : Blo 1387513 1562449 := bbase (se 2 (by rfl) ⟨585918, by rfl⟩ : syracuseStep 1562449 = 1171837) (by norm_num)
theorem B4446053 : Blo 1387513 4446053 := bbase (se 4 (by rfl) ⟨416817, by rfl⟩ : syracuseStep 4446053 = 833635) (by norm_num)
theorem B5928821 : Blo 1387513 5928821 := bbase (se 5 (by rfl) ⟨277913, by rfl⟩ : syracuseStep 5928821 = 555827) (by norm_num)
theorem B1562485 : Blo 1387513 1562485 := bbase (se 5 (by rfl) ⟨73241, by rfl⟩ : syracuseStep 1562485 = 146483) (by norm_num)
theorem B2635669 : Blo 1387513 2635669 := bbase (se 6 (by rfl) ⟨61773, by rfl⟩ : syracuseStep 2635669 = 123547) (by norm_num)
theorem B1562521 : Blo 1387513 1562521 := bbase (se 2 (by rfl) ⟨585945, by rfl⟩ : syracuseStep 1562521 = 1171891) (by norm_num)
theorem B5273525 : Blo 1387513 5273525 := bbase (se 5 (by rfl) ⟨247196, by rfl⟩ : syracuseStep 5273525 = 494393) (by norm_num)
theorem B1562557 : Blo 1387513 1562557 := bbase (se 3 (by rfl) ⟨292979, by rfl⟩ : syracuseStep 1562557 = 585959) (by norm_num)
theorem B3512261 : Blo 1387513 3512261 := bbase (se 4 (by rfl) ⟨329274, by rfl⟩ : syracuseStep 3512261 = 658549) (by norm_num)
theorem B6330325 : Blo 1387513 6330325 := bbase (se 7 (by rfl) ⟨74183, by rfl⟩ : syracuseStep 6330325 = 148367) (by norm_num)
theorem B1562593 : Blo 1387513 1562593 := bbase (se 2 (by rfl) ⟨585972, by rfl⟩ : syracuseStep 1562593 = 1171945) (by norm_num)
theorem B3168229 : Blo 1387513 3168229 := bbase (se 4 (by rfl) ⟨297021, by rfl⟩ : syracuseStep 3168229 = 594043) (by norm_num)
theorem B1562629 : Blo 1387513 1562629 := bbase (se 4 (by rfl) ⟨146496, by rfl⟩ : syracuseStep 1562629 = 292993) (by norm_num)
theorem B4683797 : Blo 1387513 4683797 := bbase (se 6 (by rfl) ⟨109776, by rfl⟩ : syracuseStep 4683797 = 219553) (by norm_num)
theorem B1562665 : Blo 1387513 1562665 := bbase (se 2 (by rfl) ⟨585999, by rfl⟩ : syracuseStep 1562665 = 1171999) (by norm_num)
theorem B3954757 : Blo 1387513 3954757 := bbase (se 4 (by rfl) ⟨370758, by rfl⟩ : syracuseStep 3954757 = 741517) (by norm_num)
theorem B1562701 : Blo 1387513 1562701 := bbase (se 3 (by rfl) ⟨293006, by rfl⟩ : syracuseStep 1562701 = 586013) (by norm_num)
theorem B1562737 : Blo 1387513 1562737 := bbase (se 2 (by rfl) ⟨586026, by rfl⟩ : syracuseStep 1562737 = 1172053) (by norm_num)
theorem B1562773 : Blo 1387513 1562773 := bbase (se 6 (by rfl) ⟨36627, by rfl⟩ : syracuseStep 1562773 = 73255) (by norm_num)
theorem B1562809 : Blo 1387513 1562809 := bbase (se 2 (by rfl) ⟨586053, by rfl⟩ : syracuseStep 1562809 = 1172107) (by norm_num)
theorem B2635973 : Blo 1387513 2635973 := bbase (se 4 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 2635973 = 494245) (by norm_num)
theorem B1407181 : Blo 1387513 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B1562845 : Blo 1387513 1562845 := bbase (se 3 (by rfl) ⟨293033, by rfl⟩ : syracuseStep 1562845 = 586067) (by norm_num)
theorem B1562881 : Blo 1387513 1562881 := bbase (se 2 (by rfl) ⟨586080, by rfl⟩ : syracuseStep 1562881 = 1172161) (by norm_num)
theorem B7911701 : Blo 1387513 7911701 := bbase (se 6 (by rfl) ⟨185430, by rfl⟩ : syracuseStep 7911701 = 370861) (by norm_num)
theorem B3512605 : Blo 1387513 3512605 := bbase (se 3 (by rfl) ⟨658613, by rfl⟩ : syracuseStep 3512605 = 1317227) (by norm_num)
theorem B1562917 : Blo 1387513 1562917 := bbase (se 4 (by rfl) ⟨146523, by rfl⟩ : syracuseStep 1562917 = 293047) (by norm_num)
theorem B1562953 : Blo 1387513 1562953 := bbase (se 2 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 1562953 = 1172215) (by norm_num)
theorem B19003733 : Blo 1387513 19003733 := bbase (se 10 (by rfl) ⟨27837, by rfl⟩ : syracuseStep 19003733 = 55675) (by norm_num)
theorem B1562989 : Blo 1387513 1562989 := bbase (se 3 (by rfl) ⟨293060, by rfl⟩ : syracuseStep 1562989 = 586121) (by norm_num)
theorem B3512717 : Blo 1387513 3512717 := bbase (se 3 (by rfl) ⟨658634, by rfl⟩ : syracuseStep 3512717 = 1317269) (by norm_num)
theorem B1563025 : Blo 1387513 1563025 := bbase (se 2 (by rfl) ⟨586134, by rfl⟩ : syracuseStep 1563025 = 1172269) (by norm_num)
theorem B1563061 : Blo 1387513 1563061 := bbase (se 5 (by rfl) ⟨73268, by rfl⟩ : syracuseStep 1563061 = 146537) (by norm_num)
theorem B4684229 : Blo 1387513 4684229 := bbase (se 4 (by rfl) ⟨439146, by rfl⟩ : syracuseStep 4684229 = 878293) (by norm_num)
theorem B6674885 : Blo 1387513 6674885 := bbase (se 4 (by rfl) ⟨625770, by rfl⟩ : syracuseStep 6674885 = 1251541) (by norm_num)
theorem B1563097 : Blo 1387513 1563097 := bbase (se 2 (by rfl) ⟨586161, by rfl⟩ : syracuseStep 1563097 = 1172323) (by norm_num)
theorem B1563133 : Blo 1387513 1563133 := bbase (se 3 (by rfl) ⟨293087, by rfl⟩ : syracuseStep 1563133 = 586175) (by norm_num)
theorem B1563169 : Blo 1387513 1563169 := bbase (se 2 (by rfl) ⟨586188, by rfl⟩ : syracuseStep 1563169 = 1172377) (by norm_num)
theorem B2341453 : Blo 1387513 2341453 := bbase (se 3 (by rfl) ⟨439022, by rfl⟩ : syracuseStep 2341453 = 878045) (by norm_num)
theorem B3512909 : Blo 1387513 3512909 := bbase (se 3 (by rfl) ⟨658670, by rfl⟩ : syracuseStep 3512909 = 1317341) (by norm_num)
theorem B2112085 : Blo 1387513 2112085 := bbase (se 8 (by rfl) ⟨12375, by rfl⟩ : syracuseStep 2112085 = 24751) (by norm_num)
theorem B4446821 : Blo 1387513 4446821 := bbase (se 4 (by rfl) ⟨416889, by rfl⟩ : syracuseStep 4446821 = 833779) (by norm_num)
theorem B7502453 : Blo 1387513 7502453 := bbase (se 5 (by rfl) ⟨351677, by rfl⟩ : syracuseStep 7502453 = 703355) (by norm_num)
theorem B2374261 : Blo 1387513 2374261 := bbase (se 5 (by rfl) ⟨111293, by rfl⟩ : syracuseStep 2374261 = 222587) (by norm_num)
theorem B3168893 : Blo 1387513 3168893 := bbase (se 3 (by rfl) ⟨594167, by rfl⟩ : syracuseStep 3168893 = 1188335) (by norm_num)
theorem B2341541 : Blo 1387513 2341541 := bbase (se 4 (by rfl) ⟨219519, by rfl⟩ : syracuseStep 2341541 = 439039) (by norm_num)
theorem B7027397 : Blo 1387513 7027397 := bbase (se 4 (by rfl) ⟨658818, by rfl⟩ : syracuseStep 7027397 = 1317637) (by norm_num)
theorem B2964205 : Blo 1387513 2964205 := bbase (se 3 (by rfl) ⟨555788, by rfl⟩ : syracuseStep 2964205 = 1111577) (by norm_num)
theorem B2341669 : Blo 1387513 2341669 := bbase (se 4 (by rfl) ⟨219531, by rfl⟩ : syracuseStep 2341669 = 439063) (by norm_num)
theorem B2112365 : Blo 1387513 2112365 := bbase (se 3 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 2112365 = 792137) (by norm_num)
theorem B4684661 : Blo 1387513 4684661 := bbase (se 5 (by rfl) ⟨219593, by rfl⟩ : syracuseStep 4684661 = 439187) (by norm_num)
theorem B2341757 : Blo 1387513 2341757 := bbase (se 3 (by rfl) ⟨439079, by rfl⟩ : syracuseStep 2341757 = 878159) (by norm_num)
theorem B3513253 : Blo 1387513 3513253 := bbase (se 4 (by rfl) ⟨329367, by rfl⟩ : syracuseStep 3513253 = 658735) (by norm_num)
theorem B2636725 : Blo 1387513 2636725 := bbase (se 5 (by rfl) ⟨123596, by rfl⟩ : syracuseStep 2636725 = 247193) (by norm_num)
theorem B1481689 : Blo 1387513 1481689 := bbase (se 2 (by rfl) ⟨555633, by rfl⟩ : syracuseStep 1481689 = 1111267) (by norm_num)
theorem B2341885 : Blo 1387513 2341885 := bbase (se 3 (by rfl) ⟨439103, by rfl⟩ : syracuseStep 2341885 = 878207) (by norm_num)
theorem B3513365 : Blo 1387513 3513365 := bbase (se 6 (by rfl) ⟨82344, by rfl⟩ : syracuseStep 3513365 = 164689) (by norm_num)
theorem B1481761 : Blo 1387513 1481761 := bbase (se 2 (by rfl) ⟨555660, by rfl⟩ : syracuseStep 1481761 = 1111321) (by norm_num)
theorem B2636869 : Blo 1387513 2636869 := bbase (se 4 (by rfl) ⟨247206, by rfl⟩ : syracuseStep 2636869 = 494413) (by norm_num)
theorem B2341973 : Blo 1387513 2341973 := bbase (se 8 (by rfl) ⟨13722, by rfl⟩ : syracuseStep 2341973 = 27445) (by norm_num)
theorem B4447333 : Blo 1387513 4447333 := bbase (se 4 (by rfl) ⟨416937, by rfl⟩ : syracuseStep 4447333 = 833875) (by norm_num)
theorem B2342101 : Blo 1387513 2342101 := bbase (se 7 (by rfl) ⟨27446, by rfl⟩ : syracuseStep 2342101 = 54893) (by norm_num)
theorem B3513557 : Blo 1387513 3513557 := bbase (se 7 (by rfl) ⟨41174, by rfl⟩ : syracuseStep 3513557 = 82349) (by norm_num)
theorem B2964701 : Blo 1387513 2964701 := bbase (se 3 (by rfl) ⟨555881, by rfl⟩ : syracuseStep 2964701 = 1111763) (by norm_num)
theorem B2637029 : Blo 1387513 2637029 := bbase (se 4 (by rfl) ⟨247221, by rfl⟩ : syracuseStep 2637029 = 494443) (by norm_num)
theorem B4685093 : Blo 1387513 4685093 := bbase (se 4 (by rfl) ⟨439227, by rfl⟩ : syracuseStep 4685093 = 878455) (by norm_num)
theorem B2342189 : Blo 1387513 2342189 := bbase (se 3 (by rfl) ⟨439160, by rfl⟩ : syracuseStep 2342189 = 878321) (by norm_num)
theorem B2637173 : Blo 1387513 2637173 := bbase (se 5 (by rfl) ⟨123617, by rfl⟩ : syracuseStep 2637173 = 247235) (by norm_num)
theorem B1482133 : Blo 1387513 1482133 := bbase (se 6 (by rfl) ⟨34737, by rfl⟩ : syracuseStep 1482133 = 69475) (by norm_num)
theorem B2342317 : Blo 1387513 2342317 := bbase (se 3 (by rfl) ⟨439184, by rfl⟩ : syracuseStep 2342317 = 878369) (by norm_num)
theorem B2342405 : Blo 1387513 2342405 := bbase (se 4 (by rfl) ⟨219600, by rfl⟩ : syracuseStep 2342405 = 439201) (by norm_num)
theorem B3513901 : Blo 1387513 3513901 := bbase (se 3 (by rfl) ⟨658856, by rfl⟩ : syracuseStep 3513901 = 1317713) (by norm_num)
theorem B5930597 : Blo 1387513 5930597 := bbase (se 4 (by rfl) ⟨555993, by rfl⟩ : syracuseStep 5930597 = 1111987) (by norm_num)
theorem B2342533 : Blo 1387513 2342533 := bbase (se 4 (by rfl) ⟨219612, by rfl⟩ : syracuseStep 2342533 = 439225) (by norm_num)
theorem B2637461 : Blo 1387513 2637461 := bbase (se 6 (by rfl) ⟨61815, by rfl⟩ : syracuseStep 2637461 = 123631) (by norm_num)
theorem B3514013 : Blo 1387513 3514013 := bbase (se 3 (by rfl) ⟨658877, by rfl⟩ : syracuseStep 3514013 = 1317755) (by norm_num)
theorem B4685525 : Blo 1387513 4685525 := bbase (se 7 (by rfl) ⟨54908, by rfl⟩ : syracuseStep 4685525 = 109817) (by norm_num)
theorem B2342621 : Blo 1387513 2342621 := bbase (se 3 (by rfl) ⟨439241, by rfl⟩ : syracuseStep 2342621 = 878483) (by norm_num)
theorem B1482509 : Blo 1387513 1482509 := bbase (se 3 (by rfl) ⟨277970, by rfl⟩ : syracuseStep 1482509 = 555941) (by norm_num)
theorem B2637613 : Blo 1387513 2637613 := bbase (se 3 (by rfl) ⟨494552, by rfl⟩ : syracuseStep 2637613 = 989105) (by norm_num)
theorem B1482581 : Blo 1387513 1482581 := bbase (se 9 (by rfl) ⟨4343, by rfl⟩ : syracuseStep 1482581 = 8687) (by norm_num)
theorem B2342749 : Blo 1387513 2342749 := bbase (se 3 (by rfl) ⟨439265, by rfl⟩ : syracuseStep 2342749 = 878531) (by norm_num)
theorem B3514205 : Blo 1387513 3514205 := bbase (se 3 (by rfl) ⟨658913, by rfl⟩ : syracuseStep 3514205 = 1317827) (by norm_num)
theorem B2342837 : Blo 1387513 2342837 := bbase (se 5 (by rfl) ⟨109820, by rfl⟩ : syracuseStep 2342837 = 219641) (by norm_num)
theorem B7028693 : Blo 1387513 7028693 := bbase (se 7 (by rfl) ⟨82367, by rfl⟩ : syracuseStep 7028693 = 164735) (by norm_num)
theorem B5275637 : Blo 1387513 5275637 := bbase (se 5 (by rfl) ⟨247295, by rfl⟩ : syracuseStep 5275637 = 494591) (by norm_num)
theorem B7913477 : Blo 1387513 7913477 := bstep (se 4 (by rfl) ⟨741888, by rfl⟩ : syracuseStep 7913477 = 1483777) B1483777
theorem B2637841 : Blo 1387513 2637841 := bstep (se 2 (by rfl) ⟨989190, by rfl⟩ : syracuseStep 2637841 = 1978381) B1978381
theorem B2342945 : Blo 1387513 2342945 := bstep (se 2 (by rfl) ⟨878604, by rfl⟩ : syracuseStep 2342945 = 1757209) B1757209
theorem B28508213 : Blo 1387513 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B11419717 : Blo 1387513 11419717 := bstep (se 4 (by rfl) ⟨1070598, by rfl⟩ : syracuseStep 11419717 = 2141197) B2141197
theorem B3514499 : Blo 1387513 3514499 := bstep (se 1 (by rfl) ⟨2635874, by rfl⟩ : syracuseStep 3514499 = 5271749) B5271749
theorem B2343073 : Blo 1387513 2343073 := bstep (se 2 (by rfl) ⟨878652, by rfl⟩ : syracuseStep 2343073 = 1757305) B1757305
theorem B2343107 : Blo 1387513 2343107 := bstep (se 1 (by rfl) ⟨1757330, by rfl⟩ : syracuseStep 2343107 = 3514661) B3514661
theorem B4448461 : Blo 1387513 4448461 := bstep (se 3 (by rfl) ⟨834086, by rfl⟩ : syracuseStep 4448461 = 1668173) B1668173
theorem B2375905 : Blo 1387513 2375905 := bstep (se 2 (by rfl) ⟨890964, by rfl⟩ : syracuseStep 2375905 = 1781929) B1781929
theorem B4686065 : Blo 1387513 4686065 := bstep (se 2 (by rfl) ⟨1757274, by rfl⟩ : syracuseStep 4686065 = 3514549) B3514549
theorem B1876241 : Blo 1387513 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B3514691 : Blo 1387513 3514691 := bstep (se 1 (by rfl) ⟨2636018, by rfl⟩ : syracuseStep 3514691 = 5272037) B5272037
theorem B2343235 : Blo 1387513 2343235 := bstep (se 1 (by rfl) ⟨1757426, by rfl⟩ : syracuseStep 2343235 = 3514853) B3514853
theorem B4817251 : Blo 1387513 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B3563939 : Blo 1387513 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B11264453 : Blo 1387513 11264453 := bstep (se 4 (by rfl) ⟨1056042, by rfl⟩ : syracuseStep 11264453 = 2112085) B2112085
theorem B2343377 : Blo 1387513 2343377 := bstep (se 2 (by rfl) ⟨878766, by rfl⟩ : syracuseStep 2343377 = 1757533) B1757533
theorem B13353457 : Blo 1387513 13353457 := bstep (se 2 (by rfl) ⟨5007546, by rfl⟩ : syracuseStep 13353457 = 10015093) B10015093
theorem B2081297 : Blo 1387513 2081297 := bstep (se 2 (by rfl) ⟨780486, by rfl⟩ : syracuseStep 2081297 = 1560973) B1560973
theorem B2081315 : Blo 1387513 2081315 := bstep (se 1 (by rfl) ⟨1560986, by rfl⟩ : syracuseStep 2081315 = 3121973) B3121973
theorem B2966051 : Blo 1387513 2966051 := bstep (se 1 (by rfl) ⟨2224538, by rfl⟩ : syracuseStep 2966051 = 4449077) B4449077
theorem B2081345 : Blo 1387513 2081345 := bstep (se 2 (by rfl) ⟨780504, by rfl⟩ : syracuseStep 2081345 = 1561009) B1561009
theorem B7905869 : Blo 1387513 7905869 := bstep (se 3 (by rfl) ⟨1482350, by rfl⟩ : syracuseStep 7905869 = 2964701) B2964701
theorem B2343505 : Blo 1387513 2343505 := bstep (se 2 (by rfl) ⟨878814, by rfl⟩ : syracuseStep 2343505 = 1757629) B1757629
theorem B2081363 : Blo 1387513 2081363 := bstep (se 1 (by rfl) ⟨1561022, by rfl⟩ : syracuseStep 2081363 = 3122045) B3122045
theorem B2138707 : Blo 1387513 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B1483363 : Blo 1387513 1483363 := bstep (se 1 (by rfl) ⟨1112522, by rfl⟩ : syracuseStep 1483363 = 2225045) B2225045
theorem B2081393 : Blo 1387513 2081393 := bstep (se 2 (by rfl) ⟨780522, by rfl⟩ : syracuseStep 2081393 = 1561045) B1561045
theorem B2343539 : Blo 1387513 2343539 := bstep (se 1 (by rfl) ⟨1757654, by rfl⟩ : syracuseStep 2343539 = 3515309) B3515309
theorem B2081411 : Blo 1387513 2081411 := bstep (se 1 (by rfl) ⟨1561058, by rfl⟩ : syracuseStep 2081411 = 3122117) B3122117
theorem B2081441 : Blo 1387513 2081441 := bstep (se 2 (by rfl) ⟨780540, by rfl⟩ : syracuseStep 2081441 = 1561081) B1561081
theorem B2081459 : Blo 1387513 2081459 := bstep (se 1 (by rfl) ⟨1561094, by rfl⟩ : syracuseStep 2081459 = 3122189) B3122189
theorem B24052421 : Blo 1387513 24052421 := bstep (se 4 (by rfl) ⟨2254914, by rfl⟩ : syracuseStep 24052421 = 4509829) B4509829
theorem B2081489 : Blo 1387513 2081489 := bstep (se 2 (by rfl) ⟨780558, by rfl⟩ : syracuseStep 2081489 = 1561117) B1561117
theorem B2081507 : Blo 1387513 2081507 := bstep (se 1 (by rfl) ⟨1561130, by rfl⟩ : syracuseStep 2081507 = 3122261) B3122261
theorem B2343667 : Blo 1387513 2343667 := bstep (se 1 (by rfl) ⟨1757750, by rfl⟩ : syracuseStep 2343667 = 3515501) B3515501
theorem B2081537 : Blo 1387513 2081537 := bstep (se 2 (by rfl) ⟨780576, by rfl⟩ : syracuseStep 2081537 = 1561153) B1561153
theorem B4686605 : Blo 1387513 4686605 := bstep (se 3 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 4686605 = 1757477) B1757477
theorem B3121937 : Blo 1387513 3121937 := bstep (se 2 (by rfl) ⟨1170726, by rfl⟩ : syracuseStep 3121937 = 2341453) B2341453
theorem B2081555 : Blo 1387513 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B3121955 : Blo 1387513 3121955 := bstep (se 1 (by rfl) ⟨2341466, by rfl⟩ : syracuseStep 3121955 = 4682933) B4682933
theorem B2081585 : Blo 1387513 2081585 := bstep (se 2 (by rfl) ⟨780594, by rfl⟩ : syracuseStep 2081585 = 1561189) B1561189
theorem B2081603 : Blo 1387513 2081603 := bstep (se 1 (by rfl) ⟨1561202, by rfl⟩ : syracuseStep 2081603 = 3122405) B3122405
theorem B4686659 : Blo 1387513 4686659 := bstep (se 1 (by rfl) ⟨3514994, by rfl⟩ : syracuseStep 4686659 = 7029989) B7029989
theorem B2081633 : Blo 1387513 2081633 := bstep (se 2 (by rfl) ⟨780612, by rfl⟩ : syracuseStep 2081633 = 1561225) B1561225
theorem B6669155 : Blo 1387513 6669155 := bstep (se 1 (by rfl) ⟨5001866, by rfl⟩ : syracuseStep 6669155 = 10003733) B10003733
theorem B2081651 : Blo 1387513 2081651 := bstep (se 1 (by rfl) ⟨1561238, by rfl⟩ : syracuseStep 2081651 = 3122477) B3122477
theorem B2343809 : Blo 1387513 2343809 := bstep (se 2 (by rfl) ⟨878928, by rfl⟩ : syracuseStep 2343809 = 1757857) B1757857
theorem B2081681 : Blo 1387513 2081681 := bstep (se 2 (by rfl) ⟨780630, by rfl⟩ : syracuseStep 2081681 = 1561261) B1561261
theorem B2081699 : Blo 1387513 2081699 := bstep (se 1 (by rfl) ⟨1561274, by rfl⟩ : syracuseStep 2081699 = 3122549) B3122549
theorem B2671537 : Blo 1387513 2671537 := bstep (se 2 (by rfl) ⟨1001826, by rfl⟩ : syracuseStep 2671537 = 2003653) B2003653
theorem B2081729 : Blo 1387513 2081729 := bstep (se 2 (by rfl) ⟨780648, by rfl⟩ : syracuseStep 2081729 = 1561297) B1561297
theorem B3335107 : Blo 1387513 3335107 := bstep (se 1 (by rfl) ⟨2501330, by rfl⟩ : syracuseStep 3335107 = 5002661) B5002661
theorem B2081747 : Blo 1387513 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B2081777 : Blo 1387513 2081777 := bstep (se 2 (by rfl) ⟨780666, by rfl⟩ : syracuseStep 2081777 = 1561333) B1561333
theorem B2343937 : Blo 1387513 2343937 := bstep (se 2 (by rfl) ⟨878976, by rfl⟩ : syracuseStep 2343937 = 1757953) B1757953
theorem B2081795 : Blo 1387513 2081795 := bstep (se 1 (by rfl) ⟨1561346, by rfl⟩ : syracuseStep 2081795 = 3122693) B3122693
theorem B2081825 : Blo 1387513 2081825 := bstep (se 2 (by rfl) ⟨780684, by rfl⟩ : syracuseStep 2081825 = 1561369) B1561369
theorem B2343971 : Blo 1387513 2343971 := bstep (se 1 (by rfl) ⟨1757978, by rfl⟩ : syracuseStep 2343971 = 3515957) B3515957
theorem B3122225 : Blo 1387513 3122225 := bstep (se 2 (by rfl) ⟨1170834, by rfl⟩ : syracuseStep 3122225 = 2341669) B2341669
theorem B2081843 : Blo 1387513 2081843 := bstep (se 1 (by rfl) ⟨1561382, by rfl⟩ : syracuseStep 2081843 = 3122765) B3122765
theorem B3122243 : Blo 1387513 3122243 := bstep (se 1 (by rfl) ⟨2341682, by rfl⟩ : syracuseStep 3122243 = 4683365) B4683365
theorem B2081873 : Blo 1387513 2081873 := bstep (se 2 (by rfl) ⟨780702, by rfl⟩ : syracuseStep 2081873 = 1561405) B1561405
theorem B4686929 : Blo 1387513 4686929 := bstep (se 2 (by rfl) ⟨1757598, by rfl⟩ : syracuseStep 4686929 = 3515197) B3515197
theorem B2081891 : Blo 1387513 2081891 := bstep (se 1 (by rfl) ⟨1561418, by rfl⟩ : syracuseStep 2081891 = 3122837) B3122837
theorem B2081921 : Blo 1387513 2081921 := bstep (se 2 (by rfl) ⟨780720, by rfl⟩ : syracuseStep 2081921 = 1561441) B1561441
theorem B2081939 : Blo 1387513 2081939 := bstep (se 1 (by rfl) ⟨1561454, by rfl⟩ : syracuseStep 2081939 = 3122909) B3122909
theorem B2344099 : Blo 1387513 2344099 := bstep (se 1 (by rfl) ⟨1758074, by rfl⟩ : syracuseStep 2344099 = 3516149) B3516149
theorem B2081969 : Blo 1387513 2081969 := bstep (se 2 (by rfl) ⟨780738, by rfl⟩ : syracuseStep 2081969 = 1561477) B1561477
theorem B2081987 : Blo 1387513 2081987 := bstep (se 1 (by rfl) ⟨1561490, by rfl⟩ : syracuseStep 2081987 = 3122981) B3122981
theorem B2082017 : Blo 1387513 2082017 := bstep (se 2 (by rfl) ⟨780756, by rfl⟩ : syracuseStep 2082017 = 1561513) B1561513
theorem B3515633 : Blo 1387513 3515633 := bstep (se 2 (by rfl) ⟨1318362, by rfl⟩ : syracuseStep 3515633 = 2636725) B2636725
theorem B2082035 : Blo 1387513 2082035 := bstep (se 1 (by rfl) ⟨1561526, by rfl⟩ : syracuseStep 2082035 = 3123053) B3123053
theorem B2082065 : Blo 1387513 2082065 := bstep (se 2 (by rfl) ⟨780774, by rfl⟩ : syracuseStep 2082065 = 1561549) B1561549
theorem B1975585 : Blo 1387513 1975585 := bstep (se 2 (by rfl) ⟨740844, by rfl⟩ : syracuseStep 1975585 = 1481689) B1481689
theorem B2082083 : Blo 1387513 2082083 := bstep (se 1 (by rfl) ⟨1561562, by rfl⟩ : syracuseStep 2082083 = 3123125) B3123125
theorem B3515683 : Blo 1387513 3515683 := bstep (se 1 (by rfl) ⟨2636762, by rfl⟩ : syracuseStep 3515683 = 5273525) B5273525
theorem B2344241 : Blo 1387513 2344241 := bstep (se 2 (by rfl) ⟨879090, by rfl⟩ : syracuseStep 2344241 = 1758181) B1758181
theorem B2082113 : Blo 1387513 2082113 := bstep (se 2 (by rfl) ⟨780792, by rfl⟩ : syracuseStep 2082113 = 1561585) B1561585
theorem B3122513 : Blo 1387513 3122513 := bstep (se 2 (by rfl) ⟨1170942, by rfl⟩ : syracuseStep 3122513 = 2341885) B2341885
theorem B2082131 : Blo 1387513 2082131 := bstep (se 1 (by rfl) ⟨1561598, by rfl⟩ : syracuseStep 2082131 = 3123197) B3123197
theorem B3122531 : Blo 1387513 3122531 := bstep (se 1 (by rfl) ⟨2341898, by rfl⟩ : syracuseStep 3122531 = 4683797) B4683797
theorem B2082161 : Blo 1387513 2082161 := bstep (se 2 (by rfl) ⟨780810, by rfl⟩ : syracuseStep 2082161 = 1561621) B1561621
theorem B1975681 : Blo 1387513 1975681 := bstep (se 2 (by rfl) ⟨740880, by rfl⟩ : syracuseStep 1975681 = 1481761) B1481761
theorem B2082179 : Blo 1387513 2082179 := bstep (se 1 (by rfl) ⟨1561634, by rfl⟩ : syracuseStep 2082179 = 3123269) B3123269
theorem B2082209 : Blo 1387513 2082209 := bstep (se 2 (by rfl) ⟨780828, by rfl⟩ : syracuseStep 2082209 = 1561657) B1561657
theorem B3515825 : Blo 1387513 3515825 := bstep (se 2 (by rfl) ⟨1318434, by rfl⟩ : syracuseStep 3515825 = 2636869) B2636869
theorem B2344369 : Blo 1387513 2344369 := bstep (se 2 (by rfl) ⟨879138, by rfl⟩ : syracuseStep 2344369 = 1758277) B1758277
theorem B2082227 : Blo 1387513 2082227 := bstep (se 1 (by rfl) ⟨1561670, by rfl⟩ : syracuseStep 2082227 = 3123341) B3123341
theorem B16885189 : Blo 1387513 16885189 := bstep (se 4 (by rfl) ⟨1582986, by rfl⟩ : syracuseStep 16885189 = 3165973) B3165973
theorem B2082257 : Blo 1387513 2082257 := bstep (se 2 (by rfl) ⟨780846, by rfl⟩ : syracuseStep 2082257 = 1561693) B1561693
theorem B2344403 : Blo 1387513 2344403 := bstep (se 1 (by rfl) ⟨1758302, by rfl⟩ : syracuseStep 2344403 = 3516605) B3516605
theorem B2082275 : Blo 1387513 2082275 := bstep (se 1 (by rfl) ⟨1561706, by rfl⟩ : syracuseStep 2082275 = 3123413) B3123413
theorem B2967025 : Blo 1387513 2967025 := bstep (se 2 (by rfl) ⟨1112634, by rfl⟩ : syracuseStep 2967025 = 2225269) B2225269
theorem B2082305 : Blo 1387513 2082305 := bstep (se 2 (by rfl) ⟨780864, by rfl⟩ : syracuseStep 2082305 = 1561729) B1561729
theorem B2082323 : Blo 1387513 2082323 := bstep (se 1 (by rfl) ⟨1561742, by rfl⟩ : syracuseStep 2082323 = 3123485) B3123485
theorem B2082353 : Blo 1387513 2082353 := bstep (se 2 (by rfl) ⟨780882, by rfl⟩ : syracuseStep 2082353 = 1561765) B1561765
theorem B2254385 : Blo 1387513 2254385 := bstep (se 2 (by rfl) ⟨845394, by rfl⟩ : syracuseStep 2254385 = 1690789) B1690789
theorem B2082371 : Blo 1387513 2082371 := bstep (se 1 (by rfl) ⟨1561778, by rfl⟩ : syracuseStep 2082371 = 3123557) B3123557
theorem B3753553 : Blo 1387513 3753553 := bstep (se 2 (by rfl) ⟨1407582, by rfl⟩ : syracuseStep 3753553 = 2815165) B2815165
theorem B2344531 : Blo 1387513 2344531 := bstep (se 1 (by rfl) ⟨1758398, by rfl⟩ : syracuseStep 2344531 = 3516797) B3516797
theorem B2082401 : Blo 1387513 2082401 := bstep (se 2 (by rfl) ⟨780900, by rfl⟩ : syracuseStep 2082401 = 1561801) B1561801
theorem B4687469 : Blo 1387513 4687469 := bstep (se 3 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 4687469 = 1757801) B1757801
theorem B3122801 : Blo 1387513 3122801 := bstep (se 2 (by rfl) ⟨1171050, by rfl⟩ : syracuseStep 3122801 = 2342101) B2342101
theorem B2082419 : Blo 1387513 2082419 := bstep (se 1 (by rfl) ⟨1561814, by rfl⟩ : syracuseStep 2082419 = 3123629) B3123629
theorem B3122819 : Blo 1387513 3122819 := bstep (se 1 (by rfl) ⟨2342114, by rfl⟩ : syracuseStep 3122819 = 4684229) B4684229
theorem B4449923 : Blo 1387513 4449923 := bstep (se 1 (by rfl) ⟨3337442, by rfl⟩ : syracuseStep 4449923 = 6674885) B6674885
theorem B2082449 : Blo 1387513 2082449 := bstep (se 2 (by rfl) ⟨780918, by rfl⟩ : syracuseStep 2082449 = 1561837) B1561837
theorem B2082467 : Blo 1387513 2082467 := bstep (se 1 (by rfl) ⟨1561850, by rfl⟩ : syracuseStep 2082467 = 3123701) B3123701
theorem B4687523 : Blo 1387513 4687523 := bstep (se 1 (by rfl) ⟨3515642, by rfl⟩ : syracuseStep 4687523 = 7031285) B7031285
theorem B6670001 : Blo 1387513 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B2082497 : Blo 1387513 2082497 := bstep (se 2 (by rfl) ⟨780936, by rfl⟩ : syracuseStep 2082497 = 1561873) B1561873
theorem B2082515 : Blo 1387513 2082515 := bstep (se 1 (by rfl) ⟨1561886, by rfl⟩ : syracuseStep 2082515 = 3123773) B3123773
theorem B2344673 : Blo 1387513 2344673 := bstep (se 2 (by rfl) ⟨879252, by rfl⟩ : syracuseStep 2344673 = 1758505) B1758505
theorem B2082545 : Blo 1387513 2082545 := bstep (se 2 (by rfl) ⟨780954, by rfl⟩ : syracuseStep 2082545 = 1561909) B1561909
theorem B2967281 : Blo 1387513 2967281 := bstep (se 2 (by rfl) ⟨1112730, by rfl⟩ : syracuseStep 2967281 = 2225461) B2225461
theorem B2082563 : Blo 1387513 2082563 := bstep (se 1 (by rfl) ⟨1561922, by rfl⟩ : syracuseStep 2082563 = 3123845) B3123845
theorem B2082593 : Blo 1387513 2082593 := bstep (se 2 (by rfl) ⟨780972, by rfl⟩ : syracuseStep 2082593 = 1561945) B1561945
theorem B2082611 : Blo 1387513 2082611 := bstep (se 1 (by rfl) ⟨1561958, by rfl⟩ : syracuseStep 2082611 = 3123917) B3123917
theorem B2082641 : Blo 1387513 2082641 := bstep (se 2 (by rfl) ⟨780990, by rfl⟩ : syracuseStep 2082641 = 1561981) B1561981
theorem B2344801 : Blo 1387513 2344801 := bstep (se 2 (by rfl) ⟨879300, by rfl⟩ : syracuseStep 2344801 = 1758601) B1758601
theorem B2082659 : Blo 1387513 2082659 := bstep (se 1 (by rfl) ⟨1561994, by rfl⟩ : syracuseStep 2082659 = 3123989) B3123989
theorem B1976177 : Blo 1387513 1976177 := bstep (se 2 (by rfl) ⟨741066, by rfl⟩ : syracuseStep 1976177 = 1482133) B1482133
theorem B2082689 : Blo 1387513 2082689 := bstep (se 2 (by rfl) ⟨781008, by rfl⟩ : syracuseStep 2082689 = 1562017) B1562017
theorem B3123089 : Blo 1387513 3123089 := bstep (se 2 (by rfl) ⟨1171158, by rfl⟩ : syracuseStep 3123089 = 2342317) B2342317
theorem B2082707 : Blo 1387513 2082707 := bstep (se 1 (by rfl) ⟨1562030, by rfl⟩ : syracuseStep 2082707 = 3124061) B3124061
theorem B3123107 : Blo 1387513 3123107 := bstep (se 1 (by rfl) ⟨2342330, by rfl⟩ : syracuseStep 3123107 = 4684661) B4684661
theorem B2082737 : Blo 1387513 2082737 := bstep (se 2 (by rfl) ⟨781026, by rfl⟩ : syracuseStep 2082737 = 1562053) B1562053
theorem B4687793 : Blo 1387513 4687793 := bstep (se 2 (by rfl) ⟨1757922, by rfl⟩ : syracuseStep 4687793 = 3515845) B3515845
theorem B2082755 : Blo 1387513 2082755 := bstep (se 1 (by rfl) ⟨1562066, by rfl⟩ : syracuseStep 2082755 = 3124133) B3124133
theorem B2082785 : Blo 1387513 2082785 := bstep (se 2 (by rfl) ⟨781044, by rfl⟩ : syracuseStep 2082785 = 1562089) B1562089
theorem B2082803 : Blo 1387513 2082803 := bstep (se 1 (by rfl) ⟨1562102, by rfl⟩ : syracuseStep 2082803 = 3124205) B3124205
theorem B2082833 : Blo 1387513 2082833 := bstep (se 2 (by rfl) ⟨781062, by rfl⟩ : syracuseStep 2082833 = 1562125) B1562125
theorem B2082851 : Blo 1387513 2082851 := bstep (se 1 (by rfl) ⟨1562138, by rfl⟩ : syracuseStep 2082851 = 3124277) B3124277
theorem B2082881 : Blo 1387513 2082881 := bstep (se 2 (by rfl) ⟨781080, by rfl⟩ : syracuseStep 2082881 = 1562161) B1562161
theorem B2082899 : Blo 1387513 2082899 := bstep (se 1 (by rfl) ⟨1562174, by rfl⟩ : syracuseStep 2082899 = 3124349) B3124349
theorem B2082929 : Blo 1387513 2082929 := bstep (se 2 (by rfl) ⟨781098, by rfl⟩ : syracuseStep 2082929 = 1562197) B1562197
theorem B2082947 : Blo 1387513 2082947 := bstep (se 1 (by rfl) ⟨1562210, by rfl⟩ : syracuseStep 2082947 = 3124421) B3124421
theorem B3336337 : Blo 1387513 3336337 := bstep (se 2 (by rfl) ⟨1251126, by rfl⟩ : syracuseStep 3336337 = 2502253) B2502253
theorem B2082977 : Blo 1387513 2082977 := bstep (se 2 (by rfl) ⟨781116, by rfl⟩ : syracuseStep 2082977 = 1562233) B1562233
theorem B3123377 : Blo 1387513 3123377 := bstep (se 2 (by rfl) ⟨1171266, by rfl⟩ : syracuseStep 3123377 = 2342533) B2342533
theorem B7030961 : Blo 1387513 7030961 := bstep (se 2 (by rfl) ⟨2636610, by rfl⟩ : syracuseStep 7030961 = 5273221) B5273221
theorem B2082995 : Blo 1387513 2082995 := bstep (se 1 (by rfl) ⟨1562246, by rfl⟩ : syracuseStep 2082995 = 3124493) B3124493
theorem B3123395 : Blo 1387513 3123395 := bstep (se 1 (by rfl) ⟨2342546, by rfl⟩ : syracuseStep 3123395 = 4685093) B4685093
theorem B2083025 : Blo 1387513 2083025 := bstep (se 2 (by rfl) ⟨781134, by rfl⟩ : syracuseStep 2083025 = 1562269) B1562269
theorem B2083043 : Blo 1387513 2083043 := bstep (se 1 (by rfl) ⟨1562282, by rfl⟩ : syracuseStep 2083043 = 3124565) B3124565
theorem B2083073 : Blo 1387513 2083073 := bstep (se 2 (by rfl) ⟨781152, by rfl⟩ : syracuseStep 2083073 = 1562305) B1562305
theorem B4507907 : Blo 1387513 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B8898821 : Blo 1387513 8898821 := bstep (se 4 (by rfl) ⟨834264, by rfl⟩ : syracuseStep 8898821 = 1668529) B1668529
theorem B2083091 : Blo 1387513 2083091 := bstep (se 1 (by rfl) ⟨1562318, by rfl⟩ : syracuseStep 2083091 = 3124637) B3124637
theorem B2083121 : Blo 1387513 2083121 := bstep (se 2 (by rfl) ⟨781170, by rfl⟩ : syracuseStep 2083121 = 1562341) B1562341
theorem B2083139 : Blo 1387513 2083139 := bstep (se 1 (by rfl) ⟨1562354, by rfl⟩ : syracuseStep 2083139 = 3124709) B3124709
theorem B2083169 : Blo 1387513 2083169 := bstep (se 2 (by rfl) ⟨781188, by rfl⟩ : syracuseStep 2083169 = 1562377) B1562377
theorem B2083187 : Blo 1387513 2083187 := bstep (se 1 (by rfl) ⟨1562390, by rfl⟩ : syracuseStep 2083187 = 3124781) B3124781
theorem B19007885 : Blo 1387513 19007885 := bstep (se 3 (by rfl) ⟨3563978, by rfl⟩ : syracuseStep 19007885 = 7127957) B7127957
theorem B2083217 : Blo 1387513 2083217 := bstep (se 2 (by rfl) ⟨781206, by rfl⟩ : syracuseStep 2083217 = 1562413) B1562413
theorem B3516817 : Blo 1387513 3516817 := bstep (se 2 (by rfl) ⟨1318806, by rfl⟩ : syracuseStep 3516817 = 2637613) B2637613
theorem B2083235 : Blo 1387513 2083235 := bstep (se 1 (by rfl) ⟨1562426, by rfl⟩ : syracuseStep 2083235 = 3124853) B3124853
theorem B2083265 : Blo 1387513 2083265 := bstep (se 2 (by rfl) ⟨781224, by rfl⟩ : syracuseStep 2083265 = 1562449) B1562449
theorem B4688333 : Blo 1387513 4688333 := bstep (se 3 (by rfl) ⟨879062, by rfl⟩ : syracuseStep 4688333 = 1758125) B1758125
theorem B3123665 : Blo 1387513 3123665 := bstep (se 2 (by rfl) ⟨1171374, by rfl⟩ : syracuseStep 3123665 = 2342749) B2342749
theorem B2083283 : Blo 1387513 2083283 := bstep (se 1 (by rfl) ⟨1562462, by rfl⟩ : syracuseStep 2083283 = 3124925) B3124925
theorem B3123683 : Blo 1387513 3123683 := bstep (se 1 (by rfl) ⟨2342762, by rfl⟩ : syracuseStep 3123683 = 4685525) B4685525
theorem B2083313 : Blo 1387513 2083313 := bstep (se 2 (by rfl) ⟨781242, by rfl⟩ : syracuseStep 2083313 = 1562485) B1562485
theorem B2083331 : Blo 1387513 2083331 := bstep (se 1 (by rfl) ⟨1562498, by rfl⟩ : syracuseStep 2083331 = 3124997) B3124997
theorem B4688387 : Blo 1387513 4688387 := bstep (se 1 (by rfl) ⟨3516290, by rfl⟩ : syracuseStep 4688387 = 7032581) B7032581
theorem B2083361 : Blo 1387513 2083361 := bstep (se 2 (by rfl) ⟨781260, by rfl⟩ : syracuseStep 2083361 = 1562521) B1562521
theorem B2083379 : Blo 1387513 2083379 := bstep (se 1 (by rfl) ⟨1562534, by rfl⟩ : syracuseStep 2083379 = 3125069) B3125069
theorem B5270093 : Blo 1387513 5270093 := bstep (se 3 (by rfl) ⟨988142, by rfl⟩ : syracuseStep 5270093 = 1976285) B1976285
theorem B2083409 : Blo 1387513 2083409 := bstep (se 2 (by rfl) ⟨781278, by rfl⟩ : syracuseStep 2083409 = 1562557) B1562557
theorem B3164771 : Blo 1387513 3164771 := bstep (se 1 (by rfl) ⟨2373578, by rfl⟩ : syracuseStep 3164771 = 4747157) B4747157
theorem B2083427 : Blo 1387513 2083427 := bstep (se 1 (by rfl) ⟨1562570, by rfl⟩ : syracuseStep 2083427 = 3125141) B3125141
theorem B8440433 : Blo 1387513 8440433 := bstep (se 2 (by rfl) ⟨3165162, by rfl⟩ : syracuseStep 8440433 = 6330325) B6330325
theorem B2083457 : Blo 1387513 2083457 := bstep (se 2 (by rfl) ⟨781296, by rfl⟩ : syracuseStep 2083457 = 1562593) B1562593
theorem B11864717 : Blo 1387513 11864717 := bstep (se 3 (by rfl) ⟨2224634, by rfl⟩ : syracuseStep 11864717 = 4449269) B4449269
theorem B2083475 : Blo 1387513 2083475 := bstep (se 1 (by rfl) ⟨1562606, by rfl⟩ : syracuseStep 2083475 = 3125213) B3125213
theorem B3517091 : Blo 1387513 3517091 := bstep (se 1 (by rfl) ⟨2637818, by rfl⟩ : syracuseStep 3517091 = 5275637) B5275637
theorem B2083505 : Blo 1387513 2083505 := bstep (se 2 (by rfl) ⟨781314, by rfl⟩ : syracuseStep 2083505 = 1562629) B1562629
theorem B2083523 : Blo 1387513 2083523 := bstep (se 1 (by rfl) ⟨1562642, by rfl⟩ : syracuseStep 2083523 = 3125285) B3125285
theorem B1977043 : Blo 1387513 1977043 := bstep (se 1 (by rfl) ⟨1482782, by rfl⟩ : syracuseStep 1977043 = 2965565) B2965565
theorem B2083553 : Blo 1387513 2083553 := bstep (se 2 (by rfl) ⟨781332, by rfl⟩ : syracuseStep 2083553 = 1562665) B1562665
theorem B3123953 : Blo 1387513 3123953 := bstep (se 2 (by rfl) ⟨1171482, by rfl⟩ : syracuseStep 3123953 = 2342965) B2342965
theorem B1501939 : Blo 1387513 1501939 := bstep (se 1 (by rfl) ⟨1126454, by rfl⟩ : syracuseStep 1501939 = 2252909) B2252909
theorem B2083571 : Blo 1387513 2083571 := bstep (se 1 (by rfl) ⟨1562678, by rfl⟩ : syracuseStep 2083571 = 3125357) B3125357
theorem B3123971 : Blo 1387513 3123971 := bstep (se 1 (by rfl) ⟨2342978, by rfl⟩ : syracuseStep 3123971 = 4685957) B4685957
theorem B7908101 : Blo 1387513 7908101 := bstep (se 4 (by rfl) ⟨741384, by rfl⟩ : syracuseStep 7908101 = 1482769) B1482769
theorem B4811537 : Blo 1387513 4811537 := bstep (se 2 (by rfl) ⟨1804326, by rfl⟩ : syracuseStep 4811537 = 3608653) B3608653
theorem B2083601 : Blo 1387513 2083601 := bstep (se 2 (by rfl) ⟨781350, by rfl⟩ : syracuseStep 2083601 = 1562701) B1562701
theorem B4688657 : Blo 1387513 4688657 := bstep (se 2 (by rfl) ⟨1758246, by rfl⟩ : syracuseStep 4688657 = 3516493) B3516493
theorem B2083619 : Blo 1387513 2083619 := bstep (se 1 (by rfl) ⟨1562714, by rfl⟩ : syracuseStep 2083619 = 3125429) B3125429
theorem B1977139 : Blo 1387513 1977139 := bstep (se 1 (by rfl) ⟨1482854, by rfl⟩ : syracuseStep 1977139 = 2965709) B2965709
theorem B2083649 : Blo 1387513 2083649 := bstep (se 2 (by rfl) ⟨781368, by rfl⟩ : syracuseStep 2083649 = 1562737) B1562737
theorem B2083667 : Blo 1387513 2083667 := bstep (se 1 (by rfl) ⟨1562750, by rfl⟩ : syracuseStep 2083667 = 3125501) B3125501
theorem B2083697 : Blo 1387513 2083697 := bstep (se 2 (by rfl) ⟨781386, by rfl⟩ : syracuseStep 2083697 = 1562773) B1562773
theorem B2083715 : Blo 1387513 2083715 := bstep (se 1 (by rfl) ⟨1562786, by rfl⟩ : syracuseStep 2083715 = 3125573) B3125573
theorem B2083745 : Blo 1387513 2083745 := bstep (se 2 (by rfl) ⟨781404, by rfl⟩ : syracuseStep 2083745 = 1562809) B1562809
theorem B2083763 : Blo 1387513 2083763 := bstep (se 1 (by rfl) ⟨1562822, by rfl⟩ : syracuseStep 2083763 = 3125645) B3125645
theorem B2083793 : Blo 1387513 2083793 := bstep (se 2 (by rfl) ⟨781422, by rfl⟩ : syracuseStep 2083793 = 1562845) B1562845
theorem B2083811 : Blo 1387513 2083811 := bstep (se 1 (by rfl) ⟨1562858, by rfl⟩ : syracuseStep 2083811 = 3125717) B3125717
theorem B1387523 : Blo 1387513 1387523 := bstep (se 1 (by rfl) ⟨1040642, by rfl⟩ : syracuseStep 1387523 = 2081285) B2081285
theorem B2083841 : Blo 1387513 2083841 := bstep (se 2 (by rfl) ⟨781440, by rfl⟩ : syracuseStep 2083841 = 1562881) B1562881
theorem B3124241 : Blo 1387513 3124241 := bstep (se 2 (by rfl) ⟨1171590, by rfl⟩ : syracuseStep 3124241 = 2343181) B2343181
theorem B1387539 : Blo 1387513 1387539 := bstep (se 1 (by rfl) ⟨1040654, by rfl⟩ : syracuseStep 1387539 = 2081309) B2081309
theorem B2083859 : Blo 1387513 2083859 := bstep (se 1 (by rfl) ⟨1562894, by rfl⟩ : syracuseStep 2083859 = 3125789) B3125789
theorem B1387555 : Blo 1387513 1387555 := bstep (se 1 (by rfl) ⟨1040666, by rfl⟩ : syracuseStep 1387555 = 2081333) B2081333
theorem B3124259 : Blo 1387513 3124259 := bstep (se 1 (by rfl) ⟨2343194, by rfl⟩ : syracuseStep 3124259 = 4686389) B4686389
theorem B2083889 : Blo 1387513 2083889 := bstep (se 2 (by rfl) ⟨781458, by rfl⟩ : syracuseStep 2083889 = 1562917) B1562917
theorem B1387571 : Blo 1387513 1387571 := bstep (se 1 (by rfl) ⟨1040678, by rfl⟩ : syracuseStep 1387571 = 2081357) B2081357
theorem B2198593 : Blo 1387513 2198593 := bstep (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) B1648945
theorem B1387587 : Blo 1387513 1387587 := bstep (se 1 (by rfl) ⟨1040690, by rfl⟩ : syracuseStep 1387587 = 2081381) B2081381
theorem B2083907 : Blo 1387513 2083907 := bstep (se 1 (by rfl) ⟨1562930, by rfl⟩ : syracuseStep 2083907 = 3125861) B3125861
theorem B1387603 : Blo 1387513 1387603 := bstep (se 1 (by rfl) ⟨1040702, by rfl⟩ : syracuseStep 1387603 = 2081405) B2081405
theorem B2083937 : Blo 1387513 2083937 := bstep (se 2 (by rfl) ⟨781476, by rfl⟩ : syracuseStep 2083937 = 1562953) B1562953
theorem B1387619 : Blo 1387513 1387619 := bstep (se 1 (by rfl) ⟨1040714, by rfl⟩ : syracuseStep 1387619 = 2081429) B2081429
theorem B17108081 : Blo 1387513 17108081 := bstep (se 2 (by rfl) ⟨6415530, by rfl⟩ : syracuseStep 17108081 = 12831061) B12831061
theorem B1387635 : Blo 1387513 1387635 := bstep (se 1 (by rfl) ⟨1040726, by rfl⟩ : syracuseStep 1387635 = 2081453) B2081453
theorem B2083955 : Blo 1387513 2083955 := bstep (se 1 (by rfl) ⟨1562966, by rfl⟩ : syracuseStep 2083955 = 3125933) B3125933
theorem B1387651 : Blo 1387513 1387651 := bstep (se 1 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 1387651 = 2081477) B2081477
theorem B5934221 : Blo 1387513 5934221 := bstep (se 3 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 5934221 = 2225333) B2225333
theorem B2083985 : Blo 1387513 2083985 := bstep (se 2 (by rfl) ⟨781494, by rfl⟩ : syracuseStep 2083985 = 1562989) B1562989
theorem B1387667 : Blo 1387513 1387667 := bstep (se 1 (by rfl) ⟨1040750, by rfl⟩ : syracuseStep 1387667 = 2081501) B2081501
theorem B1387683 : Blo 1387513 1387683 := bstep (se 1 (by rfl) ⟨1040762, by rfl⟩ : syracuseStep 1387683 = 2081525) B2081525
theorem B2084003 : Blo 1387513 2084003 := bstep (se 1 (by rfl) ⟨1563002, by rfl⟩ : syracuseStep 2084003 = 3126005) B3126005
theorem B1387699 : Blo 1387513 1387699 := bstep (se 1 (by rfl) ⟨1040774, by rfl⟩ : syracuseStep 1387699 = 2081549) B2081549
theorem B2223283 : Blo 1387513 2223283 := bstep (se 1 (by rfl) ⟨1667462, by rfl⟩ : syracuseStep 2223283 = 3334925) B3334925
theorem B2084033 : Blo 1387513 2084033 := bstep (se 2 (by rfl) ⟨781512, by rfl⟩ : syracuseStep 2084033 = 1563025) B1563025
theorem B1387715 : Blo 1387513 1387715 := bstep (se 1 (by rfl) ⟨1040786, by rfl⟩ : syracuseStep 1387715 = 2081573) B2081573
theorem B1387731 : Blo 1387513 1387731 := bstep (se 1 (by rfl) ⟨1040798, by rfl⟩ : syracuseStep 1387731 = 2081597) B2081597
theorem B2084051 : Blo 1387513 2084051 := bstep (se 1 (by rfl) ⟨1563038, by rfl⟩ : syracuseStep 2084051 = 3126077) B3126077
theorem B1387747 : Blo 1387513 1387747 := bstep (se 1 (by rfl) ⟨1040810, by rfl⟩ : syracuseStep 1387747 = 2081621) B2081621
theorem B7130339 : Blo 1387513 7130339 := bstep (se 1 (by rfl) ⟨5347754, by rfl⟩ : syracuseStep 7130339 = 10695509) B10695509
theorem B2084081 : Blo 1387513 2084081 := bstep (se 2 (by rfl) ⟨781530, by rfl⟩ : syracuseStep 2084081 = 1563061) B1563061
theorem B1387763 : Blo 1387513 1387763 := bstep (se 1 (by rfl) ⟨1040822, by rfl⟩ : syracuseStep 1387763 = 2081645) B2081645
theorem B1387779 : Blo 1387513 1387779 := bstep (se 1 (by rfl) ⟨1040834, by rfl⟩ : syracuseStep 1387779 = 2081669) B2081669
theorem B2084099 : Blo 1387513 2084099 := bstep (se 1 (by rfl) ⟨1563074, by rfl⟩ : syracuseStep 2084099 = 3126149) B3126149
theorem B1387795 : Blo 1387513 1387795 := bstep (se 1 (by rfl) ⟨1040846, by rfl⟩ : syracuseStep 1387795 = 2081693) B2081693
theorem B2813219 : Blo 1387513 2813219 := bstep (se 1 (by rfl) ⟨2109914, by rfl⟩ : syracuseStep 2813219 = 4219829) B4219829
theorem B1387811 : Blo 1387513 1387811 := bstep (se 1 (by rfl) ⟨1040858, by rfl⟩ : syracuseStep 1387811 = 2081717) B2081717
theorem B1977635 : Blo 1387513 1977635 := bstep (se 1 (by rfl) ⟨1483226, by rfl⟩ : syracuseStep 1977635 = 2966453) B2966453
theorem B2084129 : Blo 1387513 2084129 := bstep (se 2 (by rfl) ⟨781548, by rfl⟩ : syracuseStep 2084129 = 1563097) B1563097
theorem B4689197 : Blo 1387513 4689197 := bstep (se 3 (by rfl) ⟨879224, by rfl⟩ : syracuseStep 4689197 = 1758449) B1758449
theorem B3124529 : Blo 1387513 3124529 := bstep (se 2 (by rfl) ⟨1171698, by rfl⟩ : syracuseStep 3124529 = 2343397) B2343397
theorem B1387827 : Blo 1387513 1387827 := bstep (se 1 (by rfl) ⟨1040870, by rfl⟩ : syracuseStep 1387827 = 2081741) B2081741
theorem B2084147 : Blo 1387513 2084147 := bstep (se 1 (by rfl) ⟨1563110, by rfl⟩ : syracuseStep 2084147 = 3126221) B3126221
theorem B1387843 : Blo 1387513 1387843 := bstep (se 1 (by rfl) ⟨1040882, by rfl⟩ : syracuseStep 1387843 = 2081765) B2081765
theorem B3124547 : Blo 1387513 3124547 := bstep (se 1 (by rfl) ⟨2343410, by rfl⟩ : syracuseStep 3124547 = 4686821) B4686821
theorem B2084177 : Blo 1387513 2084177 := bstep (se 2 (by rfl) ⟨781566, by rfl⟩ : syracuseStep 2084177 = 1563133) B1563133
theorem B1387859 : Blo 1387513 1387859 := bstep (se 1 (by rfl) ⟨1040894, by rfl⟩ : syracuseStep 1387859 = 2081789) B2081789
theorem B1387875 : Blo 1387513 1387875 := bstep (se 1 (by rfl) ⟨1040906, by rfl⟩ : syracuseStep 1387875 = 2081813) B2081813
theorem B4689251 : Blo 1387513 4689251 := bstep (se 1 (by rfl) ⟨3516938, by rfl⟩ : syracuseStep 4689251 = 7033877) B7033877
theorem B2084195 : Blo 1387513 2084195 := bstep (se 1 (by rfl) ⟨1563146, by rfl⟩ : syracuseStep 2084195 = 3126293) B3126293
theorem B1387891 : Blo 1387513 1387891 := bstep (se 1 (by rfl) ⟨1040918, by rfl⟩ : syracuseStep 1387891 = 2081837) B2081837
theorem B2084225 : Blo 1387513 2084225 := bstep (se 2 (by rfl) ⟨781584, by rfl⟩ : syracuseStep 2084225 = 1563169) B1563169
theorem B1387907 : Blo 1387513 1387907 := bstep (se 1 (by rfl) ⟨1040930, by rfl⟩ : syracuseStep 1387907 = 2081861) B2081861
theorem B1387923 : Blo 1387513 1387923 := bstep (se 1 (by rfl) ⟨1040942, by rfl⟩ : syracuseStep 1387923 = 2081885) B2081885
theorem B2084243 : Blo 1387513 2084243 := bstep (se 1 (by rfl) ⟨1563182, by rfl⟩ : syracuseStep 2084243 = 3126365) B3126365
theorem B1387939 : Blo 1387513 1387939 := bstep (se 1 (by rfl) ⟨1040954, by rfl⟩ : syracuseStep 1387939 = 2081909) B2081909
theorem B7908785 : Blo 1387513 7908785 := bstep (se 2 (by rfl) ⟨2965794, by rfl⟩ : syracuseStep 7908785 = 5931589) B5931589
theorem B1387955 : Blo 1387513 1387955 := bstep (se 1 (by rfl) ⟨1040966, by rfl⟩ : syracuseStep 1387955 = 2081933) B2081933
theorem B2223539 : Blo 1387513 2223539 := bstep (se 1 (by rfl) ⟨1667654, by rfl⟩ : syracuseStep 2223539 = 3335309) B3335309
theorem B1387971 : Blo 1387513 1387971 := bstep (se 1 (by rfl) ⟨1040978, by rfl⟩ : syracuseStep 1387971 = 2081957) B2081957
theorem B1387987 : Blo 1387513 1387987 := bstep (se 1 (by rfl) ⟨1040990, by rfl⟩ : syracuseStep 1387987 = 2081981) B2081981
theorem B1388003 : Blo 1387513 1388003 := bstep (se 1 (by rfl) ⟨1041002, by rfl⟩ : syracuseStep 1388003 = 2082005) B2082005
theorem B1388019 : Blo 1387513 1388019 := bstep (se 1 (by rfl) ⟨1041014, by rfl⟩ : syracuseStep 1388019 = 2082029) B2082029
theorem B1388035 : Blo 1387513 1388035 := bstep (se 1 (by rfl) ⟨1041026, by rfl⟩ : syracuseStep 1388035 = 2082053) B2082053
theorem B1388051 : Blo 1387513 1388051 := bstep (se 1 (by rfl) ⟨1041038, by rfl⟩ : syracuseStep 1388051 = 2082077) B2082077
theorem B1388067 : Blo 1387513 1388067 := bstep (se 1 (by rfl) ⟨1041050, by rfl⟩ : syracuseStep 1388067 = 2082101) B2082101
theorem B1756723 : Blo 1387513 1756723 := bstep (se 1 (by rfl) ⟨1317542, by rfl⟩ : syracuseStep 1756723 = 2635085) B2635085
theorem B1388083 : Blo 1387513 1388083 := bstep (se 1 (by rfl) ⟨1041062, by rfl⟩ : syracuseStep 1388083 = 2082125) B2082125
theorem B1388099 : Blo 1387513 1388099 := bstep (se 1 (by rfl) ⟨1041074, by rfl⟩ : syracuseStep 1388099 = 2082149) B2082149
theorem B3124817 : Blo 1387513 3124817 := bstep (se 2 (by rfl) ⟨1171806, by rfl⟩ : syracuseStep 3124817 = 2343613) B2343613
theorem B1388115 : Blo 1387513 1388115 := bstep (se 1 (by rfl) ⟨1041086, by rfl⟩ : syracuseStep 1388115 = 2082173) B2082173
theorem B1388131 : Blo 1387513 1388131 := bstep (se 1 (by rfl) ⟨1041098, by rfl⟩ : syracuseStep 1388131 = 2082197) B2082197
theorem B3124835 : Blo 1387513 3124835 := bstep (se 1 (by rfl) ⟨2343626, by rfl⟩ : syracuseStep 3124835 = 4687253) B4687253
theorem B7032419 : Blo 1387513 7032419 := bstep (se 1 (by rfl) ⟨5274314, by rfl⟩ : syracuseStep 7032419 = 10548629) B10548629
theorem B4689521 : Blo 1387513 4689521 := bstep (se 2 (by rfl) ⟨1758570, by rfl⟩ : syracuseStep 4689521 = 3517141) B3517141
theorem B1388147 : Blo 1387513 1388147 := bstep (se 1 (by rfl) ⟨1041110, by rfl⟩ : syracuseStep 1388147 = 2082221) B2082221
theorem B2223731 : Blo 1387513 2223731 := bstep (se 1 (by rfl) ⟨1667798, by rfl⟩ : syracuseStep 2223731 = 3335597) B3335597
theorem B1388163 : Blo 1387513 1388163 := bstep (se 1 (by rfl) ⟨1041122, by rfl⟩ : syracuseStep 1388163 = 2082245) B2082245
theorem B2502289 : Blo 1387513 2502289 := bstep (se 2 (by rfl) ⟨938358, by rfl⟩ : syracuseStep 2502289 = 1876717) B1876717
theorem B1756819 : Blo 1387513 1756819 := bstep (se 1 (by rfl) ⟨1317614, by rfl⟩ : syracuseStep 1756819 = 2635229) B2635229
theorem B1388179 : Blo 1387513 1388179 := bstep (se 1 (by rfl) ⟨1041134, by rfl⟩ : syracuseStep 1388179 = 2082269) B2082269
theorem B1388195 : Blo 1387513 1388195 := bstep (se 1 (by rfl) ⟨1041146, by rfl⟩ : syracuseStep 1388195 = 2082293) B2082293
theorem B1388211 : Blo 1387513 1388211 := bstep (se 1 (by rfl) ⟨1041158, by rfl⟩ : syracuseStep 1388211 = 2082317) B2082317
theorem B1388227 : Blo 1387513 1388227 := bstep (se 1 (by rfl) ⟨1041170, by rfl⟩ : syracuseStep 1388227 = 2082341) B2082341
theorem B6672077 : Blo 1387513 6672077 := bstep (se 3 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 6672077 = 2502029) B2502029
theorem B1388243 : Blo 1387513 1388243 := bstep (se 1 (by rfl) ⟨1041182, by rfl⟩ : syracuseStep 1388243 = 2082365) B2082365
theorem B1388259 : Blo 1387513 1388259 := bstep (se 1 (by rfl) ⟨1041194, by rfl⟩ : syracuseStep 1388259 = 2082389) B2082389
theorem B1388275 : Blo 1387513 1388275 := bstep (se 1 (by rfl) ⟨1041206, by rfl⟩ : syracuseStep 1388275 = 2082413) B2082413
theorem B1388291 : Blo 1387513 1388291 := bstep (se 1 (by rfl) ⟨1041218, by rfl⟩ : syracuseStep 1388291 = 2082437) B2082437
theorem B1388307 : Blo 1387513 1388307 := bstep (se 1 (by rfl) ⟨1041230, by rfl⟩ : syracuseStep 1388307 = 2082461) B2082461
theorem B1388323 : Blo 1387513 1388323 := bstep (se 1 (by rfl) ⟨1041242, by rfl⟩ : syracuseStep 1388323 = 2082485) B2082485
theorem B1388339 : Blo 1387513 1388339 := bstep (se 1 (by rfl) ⟨1041254, by rfl⟩ : syracuseStep 1388339 = 2082509) B2082509
theorem B1388355 : Blo 1387513 1388355 := bstep (se 1 (by rfl) ⟨1041266, by rfl⟩ : syracuseStep 1388355 = 2082533) B2082533
theorem B1388371 : Blo 1387513 1388371 := bstep (se 1 (by rfl) ⟨1041278, by rfl⟩ : syracuseStep 1388371 = 2082557) B2082557
theorem B1388387 : Blo 1387513 1388387 := bstep (se 1 (by rfl) ⟨1041290, by rfl⟩ : syracuseStep 1388387 = 2082581) B2082581
theorem B3125105 : Blo 1387513 3125105 := bstep (se 2 (by rfl) ⟨1171914, by rfl⟩ : syracuseStep 3125105 = 2343829) B2343829
theorem B1388403 : Blo 1387513 1388403 := bstep (se 1 (by rfl) ⟨1041302, by rfl⟩ : syracuseStep 1388403 = 2082605) B2082605
theorem B1388419 : Blo 1387513 1388419 := bstep (se 1 (by rfl) ⟨1041314, by rfl⟩ : syracuseStep 1388419 = 2082629) B2082629
theorem B3125123 : Blo 1387513 3125123 := bstep (se 1 (by rfl) ⟨2343842, by rfl⟩ : syracuseStep 3125123 = 4687685) B4687685
theorem B1388435 : Blo 1387513 1388435 := bstep (se 1 (by rfl) ⟨1041326, by rfl⟩ : syracuseStep 1388435 = 2082653) B2082653
theorem B1978273 : Blo 1387513 1978273 := bstep (se 2 (by rfl) ⟨741852, by rfl⟩ : syracuseStep 1978273 = 1483705) B1483705
theorem B3952547 : Blo 1387513 3952547 := bstep (se 1 (by rfl) ⟨2964410, by rfl⟩ : syracuseStep 3952547 = 5928821) B5928821
theorem B1388451 : Blo 1387513 1388451 := bstep (se 1 (by rfl) ⟨1041338, by rfl⟩ : syracuseStep 1388451 = 2082677) B2082677
theorem B1388467 : Blo 1387513 1388467 := bstep (se 1 (by rfl) ⟨1041350, by rfl⟩ : syracuseStep 1388467 = 2082701) B2082701
theorem B1388483 : Blo 1387513 1388483 := bstep (se 1 (by rfl) ⟨1041362, by rfl⟩ : syracuseStep 1388483 = 2082725) B2082725
theorem B1388499 : Blo 1387513 1388499 := bstep (se 1 (by rfl) ⟨1041374, by rfl⟩ : syracuseStep 1388499 = 2082749) B2082749
theorem B20279267 : Blo 1387513 20279267 := bstep (se 1 (by rfl) ⟨15209450, by rfl⟩ : syracuseStep 20279267 = 30418901) B30418901
theorem B1388515 : Blo 1387513 1388515 := bstep (se 1 (by rfl) ⟨1041386, by rfl⟩ : syracuseStep 1388515 = 2082773) B2082773
theorem B10547171 : Blo 1387513 10547171 := bstep (se 1 (by rfl) ⟨7910378, by rfl⟩ : syracuseStep 10547171 = 15820757) B15820757
theorem B1388531 : Blo 1387513 1388531 := bstep (se 1 (by rfl) ⟨1041398, by rfl⟩ : syracuseStep 1388531 = 2082797) B2082797
theorem B1388547 : Blo 1387513 1388547 := bstep (se 1 (by rfl) ⟨1041410, by rfl⟩ : syracuseStep 1388547 = 2082821) B2082821
theorem B4222979 : Blo 1387513 4222979 := bstep (se 1 (by rfl) ⟨3167234, by rfl⟩ : syracuseStep 4222979 = 6334469) B6334469
theorem B1388563 : Blo 1387513 1388563 := bstep (se 1 (by rfl) ⟨1041422, by rfl⟩ : syracuseStep 1388563 = 2082845) B2082845
theorem B1388579 : Blo 1387513 1388579 := bstep (se 1 (by rfl) ⟨1041434, by rfl⟩ : syracuseStep 1388579 = 2082869) B2082869
theorem B1388595 : Blo 1387513 1388595 := bstep (se 1 (by rfl) ⟨1041446, by rfl⟩ : syracuseStep 1388595 = 2082893) B2082893
theorem B1388611 : Blo 1387513 1388611 := bstep (se 1 (by rfl) ⟨1041458, by rfl⟩ : syracuseStep 1388611 = 2082917) B2082917
theorem B1667155 : Blo 1387513 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B1388627 : Blo 1387513 1388627 := bstep (se 1 (by rfl) ⟨1041470, by rfl⟩ : syracuseStep 1388627 = 2082941) B2082941
theorem B1388643 : Blo 1387513 1388643 := bstep (se 1 (by rfl) ⟨1041482, by rfl⟩ : syracuseStep 1388643 = 2082965) B2082965
theorem B1388659 : Blo 1387513 1388659 := bstep (se 1 (by rfl) ⟨1041494, by rfl⟩ : syracuseStep 1388659 = 2082989) B2082989
theorem B1757315 : Blo 1387513 1757315 := bstep (se 1 (by rfl) ⟨1317986, by rfl⟩ : syracuseStep 1757315 = 2635973) B2635973
theorem B1388675 : Blo 1387513 1388675 := bstep (se 1 (by rfl) ⟨1041506, by rfl⟩ : syracuseStep 1388675 = 2083013) B2083013
theorem B3125393 : Blo 1387513 3125393 := bstep (se 2 (by rfl) ⟨1172022, by rfl⟩ : syracuseStep 3125393 = 2344045) B2344045
theorem B1388691 : Blo 1387513 1388691 := bstep (se 1 (by rfl) ⟨1041518, by rfl⟩ : syracuseStep 1388691 = 2083037) B2083037
theorem B1929377 : Blo 1387513 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B1388707 : Blo 1387513 1388707 := bstep (se 1 (by rfl) ⟨1041530, by rfl⟩ : syracuseStep 1388707 = 2083061) B2083061
theorem B3125411 : Blo 1387513 3125411 := bstep (se 1 (by rfl) ⟨2344058, by rfl⟩ : syracuseStep 3125411 = 4688117) B4688117
theorem B5632163 : Blo 1387513 5632163 := bstep (se 1 (by rfl) ⟨4224122, by rfl⟩ : syracuseStep 5632163 = 8448245) B8448245
theorem B1388723 : Blo 1387513 1388723 := bstep (se 1 (by rfl) ⟨1041542, by rfl⟩ : syracuseStep 1388723 = 2083085) B2083085
theorem B1388739 : Blo 1387513 1388739 := bstep (se 1 (by rfl) ⟨1041554, by rfl⟩ : syracuseStep 1388739 = 2083109) B2083109
theorem B1388755 : Blo 1387513 1388755 := bstep (se 1 (by rfl) ⟨1041566, by rfl⟩ : syracuseStep 1388755 = 2083133) B2083133
theorem B1667299 : Blo 1387513 1667299 := bstep (se 1 (by rfl) ⟨1250474, by rfl⟩ : syracuseStep 1667299 = 2500949) B2500949
theorem B12669155 : Blo 1387513 12669155 := bstep (se 1 (by rfl) ⟨9501866, by rfl⟩ : syracuseStep 12669155 = 19003733) B19003733
theorem B1388771 : Blo 1387513 1388771 := bstep (se 1 (by rfl) ⟨1041578, by rfl⟩ : syracuseStep 1388771 = 2083157) B2083157
theorem B1388787 : Blo 1387513 1388787 := bstep (se 1 (by rfl) ⟨1041590, by rfl⟩ : syracuseStep 1388787 = 2083181) B2083181
theorem B1388803 : Blo 1387513 1388803 := bstep (se 1 (by rfl) ⟨1041602, by rfl⟩ : syracuseStep 1388803 = 2083205) B2083205
theorem B15814925 : Blo 1387513 15814925 := bstep (se 3 (by rfl) ⟨2965298, by rfl⟩ : syracuseStep 15814925 = 5930597) B5930597
theorem B1388819 : Blo 1387513 1388819 := bstep (se 1 (by rfl) ⟨1041614, by rfl⟩ : syracuseStep 1388819 = 2083229) B2083229
theorem B1388835 : Blo 1387513 1388835 := bstep (se 1 (by rfl) ⟨1041626, by rfl⟩ : syracuseStep 1388835 = 2083253) B2083253
theorem B2814257 : Blo 1387513 2814257 := bstep (se 2 (by rfl) ⟨1055346, by rfl⟩ : syracuseStep 2814257 = 2110693) B2110693
theorem B1388851 : Blo 1387513 1388851 := bstep (se 1 (by rfl) ⟨1041638, by rfl⟩ : syracuseStep 1388851 = 2083277) B2083277
theorem B1388867 : Blo 1387513 1388867 := bstep (se 1 (by rfl) ⟨1041650, by rfl⟩ : syracuseStep 1388867 = 2083301) B2083301
theorem B1388883 : Blo 1387513 1388883 := bstep (se 1 (by rfl) ⟨1041662, by rfl⟩ : syracuseStep 1388883 = 2083325) B2083325
theorem B8450381 : Blo 1387513 8450381 := bstep (se 3 (by rfl) ⟨1584446, by rfl⟩ : syracuseStep 8450381 = 3168893) B3168893
theorem B1388899 : Blo 1387513 1388899 := bstep (se 1 (by rfl) ⟨1041674, by rfl⟩ : syracuseStep 1388899 = 2083349) B2083349
theorem B1388915 : Blo 1387513 1388915 := bstep (se 1 (by rfl) ⟨1041686, by rfl⟩ : syracuseStep 1388915 = 2083373) B2083373
theorem B2224513 : Blo 1387513 2224513 := bstep (se 2 (by rfl) ⟨834192, by rfl⟩ : syracuseStep 2224513 = 1668385) B1668385
theorem B1388931 : Blo 1387513 1388931 := bstep (se 1 (by rfl) ⟨1041698, by rfl⟩ : syracuseStep 1388931 = 2083397) B2083397
theorem B7033229 : Blo 1387513 7033229 := bstep (se 3 (by rfl) ⟨1318730, by rfl⟩ : syracuseStep 7033229 = 2637461) B2637461
theorem B1388947 : Blo 1387513 1388947 := bstep (se 1 (by rfl) ⟨1041710, by rfl⟩ : syracuseStep 1388947 = 2083421) B2083421
theorem B5001635 : Blo 1387513 5001635 := bstep (se 1 (by rfl) ⟨3751226, by rfl⟩ : syracuseStep 5001635 = 7502453) B7502453
theorem B1388963 : Blo 1387513 1388963 := bstep (se 1 (by rfl) ⟨1041722, by rfl⟩ : syracuseStep 1388963 = 2083445) B2083445
theorem B3125681 : Blo 1387513 3125681 := bstep (se 2 (by rfl) ⟨1172130, by rfl⟩ : syracuseStep 3125681 = 2344261) B2344261
theorem B1388979 : Blo 1387513 1388979 := bstep (se 1 (by rfl) ⟨1041734, by rfl⟩ : syracuseStep 1388979 = 2083469) B2083469
theorem B1561027 : Blo 1387513 1561027 := bstep (se 1 (by rfl) ⟨1170770, by rfl⟩ : syracuseStep 1561027 = 2341541) B2341541
theorem B1388995 : Blo 1387513 1388995 := bstep (se 1 (by rfl) ⟨1041746, by rfl⟩ : syracuseStep 1388995 = 2083493) B2083493
theorem B3125699 : Blo 1387513 3125699 := bstep (se 1 (by rfl) ⟨2344274, by rfl⟩ : syracuseStep 3125699 = 4688549) B4688549
theorem B1389011 : Blo 1387513 1389011 := bstep (se 1 (by rfl) ⟨1041758, by rfl⟩ : syracuseStep 1389011 = 2083517) B2083517
theorem B2634211 : Blo 1387513 2634211 := bstep (se 1 (by rfl) ⟨1975658, by rfl⟩ : syracuseStep 2634211 = 3951317) B3951317
theorem B1389027 : Blo 1387513 1389027 := bstep (se 1 (by rfl) ⟨1041770, by rfl⟩ : syracuseStep 1389027 = 2083541) B2083541
theorem B11416049 : Blo 1387513 11416049 := bstep (se 2 (by rfl) ⟨4281018, by rfl⟩ : syracuseStep 11416049 = 8562037) B8562037
theorem B1389043 : Blo 1387513 1389043 := bstep (se 1 (by rfl) ⟨1041782, by rfl⟩ : syracuseStep 1389043 = 2083565) B2083565
theorem B1389059 : Blo 1387513 1389059 := bstep (se 1 (by rfl) ⟨1041794, by rfl⟩ : syracuseStep 1389059 = 2083589) B2083589
theorem B2634257 : Blo 1387513 2634257 := bstep (se 2 (by rfl) ⟨987846, by rfl⟩ : syracuseStep 2634257 = 1975693) B1975693
theorem B1389075 : Blo 1387513 1389075 := bstep (se 1 (by rfl) ⟨1041806, by rfl⟩ : syracuseStep 1389075 = 2083613) B2083613
theorem B1389091 : Blo 1387513 1389091 := bstep (se 1 (by rfl) ⟨1041818, by rfl⟩ : syracuseStep 1389091 = 2083637) B2083637
theorem B1503779 : Blo 1387513 1503779 := bstep (se 1 (by rfl) ⟨1127834, by rfl⟩ : syracuseStep 1503779 = 2255669) B2255669
theorem B1389107 : Blo 1387513 1389107 := bstep (se 1 (by rfl) ⟨1041830, by rfl⟩ : syracuseStep 1389107 = 2083661) B2083661
theorem B1389123 : Blo 1387513 1389123 := bstep (se 1 (by rfl) ⟨1041842, by rfl⟩ : syracuseStep 1389123 = 2083685) B2083685
theorem B1561171 : Blo 1387513 1561171 := bstep (se 1 (by rfl) ⟨1170878, by rfl⟩ : syracuseStep 1561171 = 2341757) B2341757
theorem B1389139 : Blo 1387513 1389139 := bstep (se 1 (by rfl) ⟨1041854, by rfl⟩ : syracuseStep 1389139 = 2083709) B2083709
theorem B1389155 : Blo 1387513 1389155 := bstep (se 1 (by rfl) ⟨1041866, by rfl⟩ : syracuseStep 1389155 = 2083733) B2083733
theorem B1389171 : Blo 1387513 1389171 := bstep (se 1 (by rfl) ⟨1041878, by rfl⟩ : syracuseStep 1389171 = 2083757) B2083757
theorem B1389187 : Blo 1387513 1389187 := bstep (se 1 (by rfl) ⟨1041890, by rfl⟩ : syracuseStep 1389187 = 2083781) B2083781
theorem B1389203 : Blo 1387513 1389203 := bstep (se 1 (by rfl) ⟨1041902, by rfl⟩ : syracuseStep 1389203 = 2083805) B2083805
theorem B1389219 : Blo 1387513 1389219 := bstep (se 1 (by rfl) ⟨1041914, by rfl⟩ : syracuseStep 1389219 = 2083829) B2083829
theorem B6337201 : Blo 1387513 6337201 := bstep (se 2 (by rfl) ⟨2376450, by rfl⟩ : syracuseStep 6337201 = 4752901) B4752901
theorem B1389235 : Blo 1387513 1389235 := bstep (se 1 (by rfl) ⟨1041926, by rfl⟩ : syracuseStep 1389235 = 2083853) B2083853
theorem B1389251 : Blo 1387513 1389251 := bstep (se 1 (by rfl) ⟨1041938, by rfl⟩ : syracuseStep 1389251 = 2083877) B2083877
theorem B3953357 : Blo 1387513 3953357 := bstep (se 3 (by rfl) ⟨741254, by rfl⟩ : syracuseStep 3953357 = 1482509) B1482509
theorem B3125969 : Blo 1387513 3125969 := bstep (se 2 (by rfl) ⟨1172238, by rfl⟩ : syracuseStep 3125969 = 2344477) B2344477
theorem B1389267 : Blo 1387513 1389267 := bstep (se 1 (by rfl) ⟨1041950, by rfl⟩ : syracuseStep 1389267 = 2083901) B2083901
theorem B1561315 : Blo 1387513 1561315 := bstep (se 1 (by rfl) ⟨1170986, by rfl⟩ : syracuseStep 1561315 = 2341973) B2341973
theorem B1389283 : Blo 1387513 1389283 := bstep (se 1 (by rfl) ⟨1041962, by rfl⟩ : syracuseStep 1389283 = 2083925) B2083925
theorem B3125987 : Blo 1387513 3125987 := bstep (se 1 (by rfl) ⟨2344490, by rfl⟩ : syracuseStep 3125987 = 4688981) B4688981
theorem B1389299 : Blo 1387513 1389299 := bstep (se 1 (by rfl) ⟨1041974, by rfl⟩ : syracuseStep 1389299 = 2083949) B2083949
theorem B1389315 : Blo 1387513 1389315 := bstep (se 1 (by rfl) ⟨1041986, by rfl⟩ : syracuseStep 1389315 = 2083973) B2083973
theorem B1389331 : Blo 1387513 1389331 := bstep (se 1 (by rfl) ⟨1041998, by rfl⟩ : syracuseStep 1389331 = 2083997) B2083997
theorem B1389347 : Blo 1387513 1389347 := bstep (se 1 (by rfl) ⟨1042010, by rfl⟩ : syracuseStep 1389347 = 2084021) B2084021
theorem B2634545 : Blo 1387513 2634545 := bstep (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) B1975909
theorem B1389363 : Blo 1387513 1389363 := bstep (se 1 (by rfl) ⟨1042022, by rfl⟩ : syracuseStep 1389363 = 2084045) B2084045
theorem B23728949 : Blo 1387513 23728949 := bstep (se 5 (by rfl) ⟨1112294, by rfl⟩ : syracuseStep 23728949 = 2224589) B2224589
theorem B1758019 : Blo 1387513 1758019 := bstep (se 1 (by rfl) ⟨1318514, by rfl⟩ : syracuseStep 1758019 = 2637029) B2637029
theorem B1389379 : Blo 1387513 1389379 := bstep (se 1 (by rfl) ⟨1042034, by rfl⟩ : syracuseStep 1389379 = 2084069) B2084069
theorem B1389395 : Blo 1387513 1389395 := bstep (se 1 (by rfl) ⟨1042046, by rfl⟩ : syracuseStep 1389395 = 2084093) B2084093
theorem B7910243 : Blo 1387513 7910243 := bstep (se 1 (by rfl) ⟨5932682, by rfl⟩ : syracuseStep 7910243 = 11865365) B11865365
theorem B1389411 : Blo 1387513 1389411 := bstep (se 1 (by rfl) ⟨1042058, by rfl⟩ : syracuseStep 1389411 = 2084117) B2084117
theorem B1561459 : Blo 1387513 1561459 := bstep (se 1 (by rfl) ⟨1171094, by rfl⟩ : syracuseStep 1561459 = 2342189) B2342189
theorem B1389427 : Blo 1387513 1389427 := bstep (se 1 (by rfl) ⟨1042070, by rfl⟩ : syracuseStep 1389427 = 2084141) B2084141
theorem B1389443 : Blo 1387513 1389443 := bstep (se 1 (by rfl) ⟨1042082, by rfl⟩ : syracuseStep 1389443 = 2084165) B2084165
theorem B3953549 : Blo 1387513 3953549 := bstep (se 3 (by rfl) ⟨741290, by rfl⟩ : syracuseStep 3953549 = 1482581) B1482581
theorem B1389459 : Blo 1387513 1389459 := bstep (se 1 (by rfl) ⟨1042094, by rfl⟩ : syracuseStep 1389459 = 2084189) B2084189
theorem B1758115 : Blo 1387513 1758115 := bstep (se 1 (by rfl) ⟨1318586, by rfl⟩ : syracuseStep 1758115 = 2637173) B2637173
theorem B1389475 : Blo 1387513 1389475 := bstep (se 1 (by rfl) ⟨1042106, by rfl⟩ : syracuseStep 1389475 = 2084213) B2084213
theorem B1389491 : Blo 1387513 1389491 := bstep (se 1 (by rfl) ⟨1042118, by rfl⟩ : syracuseStep 1389491 = 2084237) B2084237
theorem B1389507 : Blo 1387513 1389507 := bstep (se 1 (by rfl) ⟨1042130, by rfl⟩ : syracuseStep 1389507 = 2084261) B2084261
theorem B5632973 : Blo 1387513 5632973 := bstep (se 3 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 5632973 = 2112365) B2112365
theorem B3126257 : Blo 1387513 3126257 := bstep (se 2 (by rfl) ⟨1172346, by rfl⟩ : syracuseStep 3126257 = 2344693) B2344693
theorem B1561603 : Blo 1387513 1561603 := bstep (se 1 (by rfl) ⟨1171202, by rfl⟩ : syracuseStep 1561603 = 2342405) B2342405
theorem B3126275 : Blo 1387513 3126275 := bstep (se 1 (by rfl) ⟨2344706, by rfl⟩ : syracuseStep 3126275 = 4689413) B4689413
theorem B7025777 : Blo 1387513 7025777 := bstep (se 2 (by rfl) ⟨2634666, by rfl⟩ : syracuseStep 7025777 = 5269333) B5269333
theorem B20296817 : Blo 1387513 20296817 := bstep (se 2 (by rfl) ⟨7611306, by rfl⟩ : syracuseStep 20296817 = 15222613) B15222613
theorem B3806353 : Blo 1387513 3806353 := bstep (se 2 (by rfl) ⟨1427382, by rfl⟩ : syracuseStep 3806353 = 2854765) B2854765
theorem B1561747 : Blo 1387513 1561747 := bstep (se 1 (by rfl) ⟨1171310, by rfl⟩ : syracuseStep 1561747 = 2342621) B2342621
theorem B1561891 : Blo 1387513 1561891 := bstep (se 1 (by rfl) ⟨1171418, by rfl⟩ : syracuseStep 1561891 = 2342837) B2342837
theorem B8893745 : Blo 1387513 8893745 := bstep (se 2 (by rfl) ⟨3335154, by rfl⟩ : syracuseStep 8893745 = 6670309) B6670309
theorem B4224305 : Blo 1387513 4224305 := bstep (se 2 (by rfl) ⟨1584114, by rfl⟩ : syracuseStep 4224305 = 3168229) B3168229
theorem B4683149 : Blo 1387513 4683149 := bstep (se 3 (by rfl) ⟨878090, by rfl⟩ : syracuseStep 4683149 = 1756181) B1756181
theorem B4445617 : Blo 1387513 4445617 := bstep (se 2 (by rfl) ⟨1667106, by rfl⟩ : syracuseStep 4445617 = 3334213) B3334213
theorem B5273009 : Blo 1387513 5273009 := bstep (se 2 (by rfl) ⟨1977378, by rfl⟩ : syracuseStep 5273009 = 3954757) B3954757
theorem B1562035 : Blo 1387513 1562035 := bstep (se 1 (by rfl) ⟨1171526, by rfl⟩ : syracuseStep 1562035 = 2343053) B2343053
theorem B4683203 : Blo 1387513 4683203 := bstep (se 1 (by rfl) ⟨3512402, by rfl⟩ : syracuseStep 4683203 = 7024805) B7024805
theorem B2635267 : Blo 1387513 2635267 := bstep (se 1 (by rfl) ⟨1976450, by rfl⟩ : syracuseStep 2635267 = 3952901) B3952901
theorem B1562179 : Blo 1387513 1562179 := bstep (se 1 (by rfl) ⟨1171634, by rfl⟩ : syracuseStep 1562179 = 2343269) B2343269
theorem B2438755 : Blo 1387513 2438755 := bstep (se 1 (by rfl) ⟨1829066, by rfl⟩ : syracuseStep 2438755 = 3658133) B3658133
theorem B5928547 : Blo 1387513 5928547 := bstep (se 1 (by rfl) ⟨4446410, by rfl⟩ : syracuseStep 5928547 = 8892821) B8892821
theorem B35599985 : Blo 1387513 35599985 := bstep (se 2 (by rfl) ⟨13349994, by rfl⟩ : syracuseStep 35599985 = 26699989) B26699989
theorem B4683473 : Blo 1387513 4683473 := bstep (se 2 (by rfl) ⟨1756302, by rfl⟩ : syracuseStep 4683473 = 3512605) B3512605
theorem B1562323 : Blo 1387513 1562323 := bstep (se 1 (by rfl) ⟨1171742, by rfl⟩ : syracuseStep 1562323 = 2343485) B2343485
theorem B1562467 : Blo 1387513 1562467 := bstep (se 1 (by rfl) ⟨1171850, by rfl⟩ : syracuseStep 1562467 = 2343701) B2343701
theorem B3954541 : Blo 1387513 3954541 := bstep (se 3 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 3954541 = 1482953) B1482953
theorem B20027249 : Blo 1387513 20027249 := bstep (se 2 (by rfl) ⟨7510218, by rfl⟩ : syracuseStep 20027249 = 15020437) B15020437
theorem B2635715 : Blo 1387513 2635715 := bstep (se 1 (by rfl) ⟨1976786, by rfl⟩ : syracuseStep 2635715 = 3953573) B3953573
theorem B12662725 : Blo 1387513 12662725 := bstep (se 4 (by rfl) ⟨1187130, by rfl⟩ : syracuseStep 12662725 = 2374261) B2374261
theorem B1669091 : Blo 1387513 1669091 := bstep (se 1 (by rfl) ⟨1251818, by rfl⟩ : syracuseStep 1669091 = 2503637) B2503637
theorem B3381233 : Blo 1387513 3381233 := bstep (se 2 (by rfl) ⟨1267962, by rfl⟩ : syracuseStep 3381233 = 2535925) B2535925
theorem B1562611 : Blo 1387513 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B8443939 : Blo 1387513 8443939 := bstep (se 1 (by rfl) ⟨6332954, by rfl⟩ : syracuseStep 8443939 = 12665909) B12665909
theorem B2373715 : Blo 1387513 2373715 := bstep (se 1 (by rfl) ⟨1780286, by rfl⟩ : syracuseStep 2373715 = 3560573) B3560573
theorem B1562755 : Blo 1387513 1562755 := bstep (se 1 (by rfl) ⟨1172066, by rfl⟩ : syracuseStep 1562755 = 2344133) B2344133
theorem B2636003 : Blo 1387513 2636003 := bstep (se 1 (by rfl) ⟨1977002, by rfl⟩ : syracuseStep 2636003 = 3954005) B3954005
theorem B4684013 : Blo 1387513 4684013 := bstep (se 3 (by rfl) ⟨878252, by rfl⟩ : syracuseStep 4684013 = 1756505) B1756505
theorem B1562899 : Blo 1387513 1562899 := bstep (se 1 (by rfl) ⟨1172174, by rfl⟩ : syracuseStep 1562899 = 2344349) B2344349
theorem B4684067 : Blo 1387513 4684067 := bstep (se 1 (by rfl) ⟨3513050, by rfl⟩ : syracuseStep 4684067 = 7026101) B7026101
theorem B1563043 : Blo 1387513 1563043 := bstep (se 1 (by rfl) ⟨1172282, by rfl⟩ : syracuseStep 1563043 = 2344565) B2344565
theorem B7027235 : Blo 1387513 7027235 := bstep (se 1 (by rfl) ⟨5270426, by rfl⟩ : syracuseStep 7027235 = 10540853) B10540853
theorem B4684337 : Blo 1387513 4684337 := bstep (se 2 (by rfl) ⟨1756626, by rfl⟩ : syracuseStep 4684337 = 3513253) B3513253
theorem B1563187 : Blo 1387513 1563187 := bstep (se 1 (by rfl) ⟨1172390, by rfl⟩ : syracuseStep 1563187 = 2344781) B2344781
theorem B2964035 : Blo 1387513 2964035 := bstep (se 1 (by rfl) ⟨2223026, by rfl⟩ : syracuseStep 2964035 = 4446053) B4446053
theorem B15809093 : Blo 1387513 15809093 := bstep (se 4 (by rfl) ⟨1482102, by rfl⟩ : syracuseStep 15809093 = 2964205) B2964205
theorem B5069411 : Blo 1387513 5069411 := bstep (se 1 (by rfl) ⟨3802058, by rfl⟩ : syracuseStep 5069411 = 7604117) B7604117
theorem B2341507 : Blo 1387513 2341507 := bstep (se 1 (by rfl) ⟨1756130, by rfl⟩ : syracuseStep 2341507 = 3512261) B3512261
theorem B2284193 : Blo 1387513 2284193 := bstep (se 2 (by rfl) ⟨856572, by rfl⟩ : syracuseStep 2284193 = 1713145) B1713145
theorem B3513041 : Blo 1387513 3513041 := bstep (se 2 (by rfl) ⟨1317390, by rfl⟩ : syracuseStep 3513041 = 2634781) B2634781
theorem B3513091 : Blo 1387513 3513091 := bstep (se 1 (by rfl) ⟨2634818, by rfl⟩ : syracuseStep 3513091 = 5269637) B5269637
theorem B2341649 : Blo 1387513 2341649 := bstep (se 2 (by rfl) ⟨878118, by rfl⟩ : syracuseStep 2341649 = 1756237) B1756237
theorem B5929777 : Blo 1387513 5929777 := bstep (se 2 (by rfl) ⟨2223666, by rfl⟩ : syracuseStep 5929777 = 4447333) B4447333
theorem B5274467 : Blo 1387513 5274467 := bstep (se 1 (by rfl) ⟨3955850, by rfl⟩ : syracuseStep 5274467 = 7911701) B7911701
theorem B5004173 : Blo 1387513 5004173 := bstep (se 3 (by rfl) ⟨938282, by rfl⟩ : syracuseStep 5004173 = 1876565) B1876565
theorem B2341777 : Blo 1387513 2341777 := bstep (se 2 (by rfl) ⟨878166, by rfl⟩ : syracuseStep 2341777 = 1756333) B1756333
theorem B3513233 : Blo 1387513 3513233 := bstep (se 2 (by rfl) ⟨1317462, by rfl⟩ : syracuseStep 3513233 = 2634925) B2634925
theorem B2341811 : Blo 1387513 2341811 := bstep (se 1 (by rfl) ⟨1756358, by rfl⟩ : syracuseStep 2341811 = 3512717) B3512717
theorem B2341939 : Blo 1387513 2341939 := bstep (se 1 (by rfl) ⟨1756454, by rfl⟩ : syracuseStep 2341939 = 3512909) B3512909
theorem B30415925 : Blo 1387513 30415925 := bstep (se 5 (by rfl) ⟨1425746, by rfl⟩ : syracuseStep 30415925 = 2851493) B2851493
theorem B2964547 : Blo 1387513 2964547 := bstep (se 1 (by rfl) ⟨2223410, by rfl⟩ : syracuseStep 2964547 = 4446821) B4446821
theorem B4684877 : Blo 1387513 4684877 := bstep (se 3 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 4684877 = 1756829) B1756829
theorem B15817841 : Blo 1387513 15817841 := bstep (se 2 (by rfl) ⟨5931690, by rfl⟩ : syracuseStep 15817841 = 11863381) B11863381
theorem B4684931 : Blo 1387513 4684931 := bstep (se 1 (by rfl) ⟨3513698, by rfl⟩ : syracuseStep 4684931 = 7027397) B7027397
theorem B2636945 : Blo 1387513 2636945 := bstep (se 2 (by rfl) ⟨988854, by rfl⟩ : syracuseStep 2636945 = 1977709) B1977709
theorem B2342081 : Blo 1387513 2342081 := bstep (se 2 (by rfl) ⟨878280, by rfl⟩ : syracuseStep 2342081 = 1756561) B1756561
theorem B3562705 : Blo 1387513 3562705 := bstep (se 2 (by rfl) ⟨1336014, by rfl⟩ : syracuseStep 3562705 = 2672029) B2672029
theorem B2342209 : Blo 1387513 2342209 := bstep (se 2 (by rfl) ⟨878328, by rfl⟩ : syracuseStep 2342209 = 1756657) B1756657
theorem B7028045 : Blo 1387513 7028045 := bstep (se 3 (by rfl) ⟨1317758, by rfl⟩ : syracuseStep 7028045 = 2635517) B2635517
theorem B2342243 : Blo 1387513 2342243 := bstep (se 1 (by rfl) ⟨1756682, by rfl⟩ : syracuseStep 2342243 = 3513365) B3513365
theorem B4685201 : Blo 1387513 4685201 := bstep (se 2 (by rfl) ⟨1756950, by rfl⟩ : syracuseStep 4685201 = 3513901) B3513901
theorem B11255237 : Blo 1387513 11255237 := bstep (se 4 (by rfl) ⟨1055178, by rfl⟩ : syracuseStep 11255237 = 2110357) B2110357
theorem B2342371 : Blo 1387513 2342371 := bstep (se 1 (by rfl) ⟨1756778, by rfl⟩ : syracuseStep 2342371 = 3513557) B3513557
theorem B39050723 : Blo 1387513 39050723 := bstep (se 1 (by rfl) ⟨29288042, by rfl⟩ : syracuseStep 39050723 = 58576085) B58576085
theorem B3956273 : Blo 1387513 3956273 := bstep (se 2 (by rfl) ⟨1483602, by rfl⟩ : syracuseStep 3956273 = 2967205) B2967205
theorem B15416885 : Blo 1387513 15416885 := bstep (se 5 (by rfl) ⟨722666, by rfl⟩ : syracuseStep 15416885 = 1445333) B1445333
theorem B2342513 : Blo 1387513 2342513 := bstep (se 2 (by rfl) ⟨878442, by rfl⟩ : syracuseStep 2342513 = 1756885) B1756885
theorem B16039565 : Blo 1387513 16039565 := bstep (se 3 (by rfl) ⟨3007418, by rfl⟩ : syracuseStep 16039565 = 6014837) B6014837
theorem B2375329 : Blo 1387513 2375329 := bstep (se 2 (by rfl) ⟨890748, by rfl⟩ : syracuseStep 2375329 = 1781497) B1781497
theorem B1482419 : Blo 1387513 1482419 := bstep (se 1 (by rfl) ⟨1111814, by rfl⟩ : syracuseStep 1482419 = 2223629) B2223629
theorem B2342641 : Blo 1387513 2342641 := bstep (se 2 (by rfl) ⟨878490, by rfl⟩ : syracuseStep 2342641 = 1756981) B1756981
theorem B3956465 : Blo 1387513 3956465 := bstep (se 2 (by rfl) ⟨1483674, by rfl⟩ : syracuseStep 3956465 = 2967349) B2967349
theorem B2965265 : Blo 1387513 2965265 := bstep (se 2 (by rfl) ⟨1111974, by rfl⟩ : syracuseStep 2965265 = 2223949) B2223949
theorem B2342675 : Blo 1387513 2342675 := bstep (se 1 (by rfl) ⟨1757006, by rfl⟩ : syracuseStep 2342675 = 3514013) B3514013
theorem B1482547 : Blo 1387513 1482547 := bstep (se 1 (by rfl) ⟨1111910, by rfl⟩ : syracuseStep 1482547 = 2223821) B2223821
theorem B5275469 : Blo 1387513 5275469 := bstep (se 3 (by rfl) ⟨989150, by rfl⟩ : syracuseStep 5275469 = 1978301) B1978301
theorem B3514225 : Blo 1387513 3514225 := bstep (se 2 (by rfl) ⟨1317834, by rfl⟩ : syracuseStep 3514225 = 2635669) B2635669
theorem B25681805 : Blo 1387513 25681805 := bstep (se 3 (by rfl) ⟨4815338, by rfl⟩ : syracuseStep 25681805 = 9630677) B9630677
theorem B2375569 : Blo 1387513 2375569 := bstep (se 2 (by rfl) ⟨890838, by rfl⟩ : syracuseStep 2375569 = 1781677) B1781677
theorem B2342803 : Blo 1387513 2342803 := bstep (se 1 (by rfl) ⟨1757102, by rfl⟩ : syracuseStep 2342803 = 3514205) B3514205
theorem B4685741 : Blo 1387513 4685741 := bstep (se 3 (by rfl) ⟨878576, by rfl⟩ : syracuseStep 4685741 = 1757153) B1757153
theorem B2670545 : Blo 1387513 2670545 := bstep (se 2 (by rfl) ⟨1001454, by rfl⟩ : syracuseStep 2670545 = 2002909) B2002909
theorem B2891747 : Blo 1387513 2891747 := bstep (se 1 (by rfl) ⟨2168810, by rfl⟩ : syracuseStep 2891747 = 4337621) B4337621
theorem B4685795 : Blo 1387513 4685795 := bstep (se 1 (by rfl) ⟨3514346, by rfl⟩ : syracuseStep 4685795 = 7028693) B7028693
theorem B5275651 : Blo 1387513 5275651 := bstep (se 1 (by rfl) ⟨3956738, by rfl⟩ : syracuseStep 5275651 = 7913477) B7913477
theorem B19005475 : Blo 1387513 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B2342999 : Blo 1387513 2342999 := bstep (se 1 (by rfl) ⟨1757249, by rfl⟩ : syracuseStep 2342999 = 3514499) B3514499
theorem B81109133 : Blo 1387513 81109133 := bstep (se 3 (by rfl) ⟨15207962, by rfl⟩ : syracuseStep 81109133 = 30415925) B30415925
theorem B8446103 : Blo 1387513 8446103 := bstep (se 1 (by rfl) ⟨6334577, by rfl⟩ : syracuseStep 8446103 = 12669155) B12669155
theorem B10543283 : Blo 1387513 10543283 := bstep (se 1 (by rfl) ⟨7907462, by rfl⟩ : syracuseStep 10543283 = 15814925) B15814925
theorem B4448449 : Blo 1387513 4448449 := bstep (se 2 (by rfl) ⟨1668168, by rfl⟩ : syracuseStep 4448449 = 3336337) B3336337
theorem B1876171 : Blo 1387513 1876171 := bstep (se 1 (by rfl) ⟨1407128, by rfl⟩ : syracuseStep 1876171 = 2814257) B2814257
theorem B2343127 : Blo 1387513 2343127 := bstep (se 1 (by rfl) ⟨1757345, by rfl⟩ : syracuseStep 2343127 = 3514691) B3514691
theorem B5931281 : Blo 1387513 5931281 := bstep (se 2 (by rfl) ⟨2224230, by rfl⟩ : syracuseStep 5931281 = 4448461) B4448461
theorem B7610699 : Blo 1387513 7610699 := bstep (se 1 (by rfl) ⟨5708024, by rfl⟩ : syracuseStep 7610699 = 11416049) B11416049
theorem B4686173 : Blo 1387513 4686173 := bstep (se 3 (by rfl) ⟨878657, by rfl⟩ : syracuseStep 4686173 = 1757315) B1757315
theorem B5145005 : Blo 1387513 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B2966017 : Blo 1387513 2966017 := bstep (se 2 (by rfl) ⟨1112256, by rfl⟩ : syracuseStep 2966017 = 2224513) B2224513
theorem B2081291 : Blo 1387513 2081291 := bstep (se 1 (by rfl) ⟨1560968, by rfl⟩ : syracuseStep 2081291 = 3121937) B3121937
theorem B2081303 : Blo 1387513 2081303 := bstep (se 1 (by rfl) ⟨1560977, by rfl⟩ : syracuseStep 2081303 = 3121955) B3121955
theorem B15819299 : Blo 1387513 15819299 := bstep (se 1 (by rfl) ⟨11864474, by rfl⟩ : syracuseStep 15819299 = 23728949) B23728949
theorem B2081369 : Blo 1387513 2081369 := bstep (se 2 (by rfl) ⟨780513, by rfl⟩ : syracuseStep 2081369 = 1561027) B1561027
theorem B7029341 : Blo 1387513 7029341 := bstep (se 3 (by rfl) ⟨1318001, by rfl⟩ : syracuseStep 7029341 = 2636003) B2636003
theorem B2081483 : Blo 1387513 2081483 := bstep (se 1 (by rfl) ⟨1561112, by rfl⟩ : syracuseStep 2081483 = 3122225) B3122225
theorem B2081495 : Blo 1387513 2081495 := bstep (se 1 (by rfl) ⟨1561121, by rfl⟩ : syracuseStep 2081495 = 3122243) B3122243
theorem B2851609 : Blo 1387513 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B2081561 : Blo 1387513 2081561 := bstep (se 2 (by rfl) ⟨780585, by rfl⟩ : syracuseStep 2081561 = 1561171) B1561171
theorem B2343755 : Blo 1387513 2343755 := bstep (se 1 (by rfl) ⟨1757816, by rfl⟩ : syracuseStep 2343755 = 3515633) B3515633
theorem B3122009 : Blo 1387513 3122009 := bstep (se 2 (by rfl) ⟨1170753, by rfl⟩ : syracuseStep 3122009 = 2341507) B2341507
theorem B2081675 : Blo 1387513 2081675 := bstep (se 1 (by rfl) ⟨1561256, by rfl⟩ : syracuseStep 2081675 = 3122513) B3122513
theorem B2081687 : Blo 1387513 2081687 := bstep (se 1 (by rfl) ⟨1561265, by rfl⟩ : syracuseStep 2081687 = 3122531) B3122531
theorem B3122099 : Blo 1387513 3122099 := bstep (se 1 (by rfl) ⟨2341574, by rfl⟩ : syracuseStep 3122099 = 4683149) B4683149
theorem B3515339 : Blo 1387513 3515339 := bstep (se 1 (by rfl) ⟨2636504, by rfl⟩ : syracuseStep 3515339 = 5273009) B5273009
theorem B2343883 : Blo 1387513 2343883 := bstep (se 1 (by rfl) ⟨1757912, by rfl⟩ : syracuseStep 2343883 = 3515825) B3515825
theorem B3122135 : Blo 1387513 3122135 := bstep (se 1 (by rfl) ⟨2341601, by rfl⟩ : syracuseStep 3122135 = 4683203) B4683203
theorem B2081753 : Blo 1387513 2081753 := bstep (se 2 (by rfl) ⟨780657, by rfl⟩ : syracuseStep 2081753 = 1561315) B1561315
theorem B7906369 : Blo 1387513 7906369 := bstep (se 2 (by rfl) ⟨2964888, by rfl⟩ : syracuseStep 7906369 = 5929777) B5929777
theorem B2081867 : Blo 1387513 2081867 := bstep (se 1 (by rfl) ⟨1561400, by rfl⟩ : syracuseStep 2081867 = 3122801) B3122801
theorem B23733323 : Blo 1387513 23733323 := bstep (se 1 (by rfl) ⟨17799992, by rfl⟩ : syracuseStep 23733323 = 35599985) B35599985
theorem B2081879 : Blo 1387513 2081879 := bstep (se 1 (by rfl) ⟨1561409, by rfl⟩ : syracuseStep 2081879 = 3122819) B3122819
theorem B2966615 : Blo 1387513 2966615 := bstep (se 1 (by rfl) ⟨2224961, by rfl⟩ : syracuseStep 2966615 = 4449923) B4449923
theorem B2344025 : Blo 1387513 2344025 := bstep (se 2 (by rfl) ⟨879009, by rfl⟩ : syracuseStep 2344025 = 1758019) B1758019
theorem B13337693 : Blo 1387513 13337693 := bstep (se 3 (by rfl) ⟨2500817, by rfl⟩ : syracuseStep 13337693 = 5001635) B5001635
theorem B9503837 : Blo 1387513 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B3122315 : Blo 1387513 3122315 := bstep (se 1 (by rfl) ⟨2341736, by rfl⟩ : syracuseStep 3122315 = 4683473) B4683473
theorem B2081945 : Blo 1387513 2081945 := bstep (se 2 (by rfl) ⟨780729, by rfl⟩ : syracuseStep 2081945 = 1561459) B1561459
theorem B3122369 : Blo 1387513 3122369 := bstep (se 2 (by rfl) ⟨1170888, by rfl⟩ : syracuseStep 3122369 = 2341777) B2341777
theorem B2344153 : Blo 1387513 2344153 := bstep (se 2 (by rfl) ⟨879057, by rfl⟩ : syracuseStep 2344153 = 1758115) B1758115
theorem B2082059 : Blo 1387513 2082059 := bstep (se 1 (by rfl) ⟨1561544, by rfl⟩ : syracuseStep 2082059 = 3123089) B3123089
theorem B2082071 : Blo 1387513 2082071 := bstep (se 1 (by rfl) ⟨1561553, by rfl⟩ : syracuseStep 2082071 = 3123107) B3123107
theorem B2082137 : Blo 1387513 2082137 := bstep (se 2 (by rfl) ⟨780801, by rfl⟩ : syracuseStep 2082137 = 1561603) B1561603
theorem B3122585 : Blo 1387513 3122585 := bstep (se 2 (by rfl) ⟨1170969, by rfl⟩ : syracuseStep 3122585 = 2341939) B2341939
theorem B2082251 : Blo 1387513 2082251 := bstep (se 1 (by rfl) ⟨1561688, by rfl⟩ : syracuseStep 2082251 = 3123377) B3123377
theorem B4687307 : Blo 1387513 4687307 := bstep (se 1 (by rfl) ⟨3515480, by rfl⟩ : syracuseStep 4687307 = 7030961) B7030961
theorem B2082263 : Blo 1387513 2082263 := bstep (se 1 (by rfl) ⟨1561697, by rfl⟩ : syracuseStep 2082263 = 3123395) B3123395
theorem B3122675 : Blo 1387513 3122675 := bstep (se 1 (by rfl) ⟨2342006, by rfl⟩ : syracuseStep 3122675 = 4684013) B4684013
theorem B5932547 : Blo 1387513 5932547 := bstep (se 1 (by rfl) ⟨4449410, by rfl⟩ : syracuseStep 5932547 = 8898821) B8898821
theorem B3122711 : Blo 1387513 3122711 := bstep (se 1 (by rfl) ⟨2342033, by rfl⟩ : syracuseStep 3122711 = 4684067) B4684067
theorem B2082329 : Blo 1387513 2082329 := bstep (se 2 (by rfl) ⟨780873, by rfl⟩ : syracuseStep 2082329 = 1561747) B1561747
theorem B8439389 : Blo 1387513 8439389 := bstep (se 3 (by rfl) ⟨1582385, by rfl⟩ : syracuseStep 8439389 = 3164771) B3164771
theorem B10544741 : Blo 1387513 10544741 := bstep (se 4 (by rfl) ⟨988569, by rfl⟩ : syracuseStep 10544741 = 1977139) B1977139
theorem B2082443 : Blo 1387513 2082443 := bstep (se 1 (by rfl) ⟨1561832, by rfl⟩ : syracuseStep 2082443 = 3123665) B3123665
theorem B2082455 : Blo 1387513 2082455 := bstep (se 1 (by rfl) ⟨1561841, by rfl⟩ : syracuseStep 2082455 = 3123683) B3123683
theorem B3122891 : Blo 1387513 3122891 := bstep (se 1 (by rfl) ⟨2342168, by rfl⟩ : syracuseStep 3122891 = 4684337) B4684337
theorem B1976023 : Blo 1387513 1976023 := bstep (se 1 (by rfl) ⟨1482017, by rfl⟩ : syracuseStep 1976023 = 2964035) B2964035
theorem B2082521 : Blo 1387513 2082521 := bstep (se 2 (by rfl) ⟨780945, by rfl⟩ : syracuseStep 2082521 = 1561891) B1561891
theorem B4687577 : Blo 1387513 4687577 := bstep (se 2 (by rfl) ⟨1757841, by rfl⟩ : syracuseStep 4687577 = 3515683) B3515683
theorem B3122945 : Blo 1387513 3122945 := bstep (se 2 (by rfl) ⟨1171104, by rfl⟩ : syracuseStep 3122945 = 2342209) B2342209
theorem B2344727 : Blo 1387513 2344727 := bstep (se 1 (by rfl) ⟨1758545, by rfl⟩ : syracuseStep 2344727 = 3517091) B3517091
theorem B2082635 : Blo 1387513 2082635 := bstep (se 1 (by rfl) ⟨1561976, by rfl⟩ : syracuseStep 2082635 = 3123953) B3123953
theorem B2082647 : Blo 1387513 2082647 := bstep (se 1 (by rfl) ⟨1561985, by rfl⟩ : syracuseStep 2082647 = 3123971) B3123971
theorem B25692005 : Blo 1387513 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B3516311 : Blo 1387513 3516311 := bstep (se 1 (by rfl) ⟨2637233, by rfl⟩ : syracuseStep 3516311 = 5274467) B5274467
theorem B2082713 : Blo 1387513 2082713 := bstep (se 2 (by rfl) ⟨781017, by rfl⟩ : syracuseStep 2082713 = 1562035) B1562035
theorem B3336115 : Blo 1387513 3336115 := bstep (se 1 (by rfl) ⟨2502086, by rfl⟩ : syracuseStep 3336115 = 5004173) B5004173
theorem B3123161 : Blo 1387513 3123161 := bstep (se 2 (by rfl) ⟨1171185, by rfl⟩ : syracuseStep 3123161 = 2342371) B2342371
theorem B10536965 : Blo 1387513 10536965 := bstep (se 4 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 10536965 = 1975681) B1975681
theorem B2082827 : Blo 1387513 2082827 := bstep (se 1 (by rfl) ⟨1562120, by rfl⟩ : syracuseStep 2082827 = 3124241) B3124241
theorem B2082839 : Blo 1387513 2082839 := bstep (se 1 (by rfl) ⟨1562129, by rfl⟩ : syracuseStep 2082839 = 3124259) B3124259
theorem B3123251 : Blo 1387513 3123251 := bstep (se 1 (by rfl) ⟨2342438, by rfl⟩ : syracuseStep 3123251 = 4684877) B4684877
theorem B11405387 : Blo 1387513 11405387 := bstep (se 1 (by rfl) ⟨8554040, by rfl⟩ : syracuseStep 11405387 = 17108081) B17108081
theorem B10545227 : Blo 1387513 10545227 := bstep (se 1 (by rfl) ⟨7908920, by rfl⟩ : syracuseStep 10545227 = 15817841) B15817841
theorem B3123287 : Blo 1387513 3123287 := bstep (se 1 (by rfl) ⟨2342465, by rfl⟩ : syracuseStep 3123287 = 4684931) B4684931
theorem B2082905 : Blo 1387513 2082905 := bstep (se 2 (by rfl) ⟨781089, by rfl⟩ : syracuseStep 2082905 = 1562179) B1562179
theorem B4753559 : Blo 1387513 4753559 := bstep (se 1 (by rfl) ⟨3565169, by rfl⟩ : syracuseStep 4753559 = 7130339) B7130339
theorem B3336385 : Blo 1387513 3336385 := bstep (se 2 (by rfl) ⟨1251144, by rfl⟩ : syracuseStep 3336385 = 2502289) B2502289
theorem B2083019 : Blo 1387513 2083019 := bstep (se 1 (by rfl) ⟨1562264, by rfl⟩ : syracuseStep 2083019 = 3124529) B3124529
theorem B2083031 : Blo 1387513 2083031 := bstep (se 1 (by rfl) ⟨1562273, by rfl⟩ : syracuseStep 2083031 = 3124547) B3124547
theorem B3123467 : Blo 1387513 3123467 := bstep (se 1 (by rfl) ⟨2342600, by rfl⟩ : syracuseStep 3123467 = 4685201) B4685201
theorem B2083097 : Blo 1387513 2083097 := bstep (se 2 (by rfl) ⟨781161, by rfl⟩ : syracuseStep 2083097 = 1562323) B1562323
theorem B5269805 : Blo 1387513 5269805 := bstep (se 3 (by rfl) ⟨988088, by rfl⟩ : syracuseStep 5269805 = 1976177) B1976177
theorem B3123521 : Blo 1387513 3123521 := bstep (se 2 (by rfl) ⟨1171320, by rfl⟩ : syracuseStep 3123521 = 2342641) B2342641
theorem B17803637 : Blo 1387513 17803637 := bstep (se 5 (by rfl) ⟨834545, by rfl⟩ : syracuseStep 17803637 = 1669091) B1669091
theorem B2083211 : Blo 1387513 2083211 := bstep (se 1 (by rfl) ⟨1562408, by rfl⟩ : syracuseStep 2083211 = 3124817) B3124817
theorem B2083223 : Blo 1387513 2083223 := bstep (se 1 (by rfl) ⟨1562417, by rfl⟩ : syracuseStep 2083223 = 3124835) B3124835
theorem B4688279 : Blo 1387513 4688279 := bstep (se 1 (by rfl) ⟨3516209, by rfl⟩ : syracuseStep 4688279 = 7032419) B7032419
theorem B1976729 : Blo 1387513 1976729 := bstep (se 2 (by rfl) ⟨741273, by rfl⟩ : syracuseStep 1976729 = 1482547) B1482547
theorem B10693043 : Blo 1387513 10693043 := bstep (se 1 (by rfl) ⟨8019782, by rfl⟩ : syracuseStep 10693043 = 16039565) B16039565
theorem B2083289 : Blo 1387513 2083289 := bstep (se 2 (by rfl) ⟨781233, by rfl⟩ : syracuseStep 2083289 = 1562467) B1562467
theorem B1976843 : Blo 1387513 1976843 := bstep (se 1 (by rfl) ⟨1482632, by rfl⟩ : syracuseStep 1976843 = 2965265) B2965265
theorem B3123737 : Blo 1387513 3123737 := bstep (se 2 (by rfl) ⟨1171401, by rfl⟩ : syracuseStep 3123737 = 2342803) B2342803
theorem B7121453 : Blo 1387513 7121453 := bstep (se 3 (by rfl) ⟨1335272, by rfl⟩ : syracuseStep 7121453 = 2670545) B2670545
theorem B3516979 : Blo 1387513 3516979 := bstep (se 1 (by rfl) ⟨2637734, by rfl⟩ : syracuseStep 3516979 = 5275469) B5275469
theorem B2083403 : Blo 1387513 2083403 := bstep (se 1 (by rfl) ⟨1562552, by rfl⟩ : syracuseStep 2083403 = 3125105) B3125105
theorem B2083415 : Blo 1387513 2083415 := bstep (se 1 (by rfl) ⟨1562561, by rfl⟩ : syracuseStep 2083415 = 3125123) B3125123
theorem B7711325 : Blo 1387513 7711325 := bstep (se 3 (by rfl) ⟨1445873, by rfl⟩ : syracuseStep 7711325 = 2891747) B2891747
theorem B3123827 : Blo 1387513 3123827 := bstep (se 1 (by rfl) ⟨2342870, by rfl⟩ : syracuseStep 3123827 = 4685741) B4685741
theorem B13519511 : Blo 1387513 13519511 := bstep (se 1 (by rfl) ⟨10139633, by rfl⟩ : syracuseStep 13519511 = 20279267) B20279267
theorem B3123863 : Blo 1387513 3123863 := bstep (se 1 (by rfl) ⟨2342897, by rfl⟩ : syracuseStep 3123863 = 4685795) B4685795
theorem B7031447 : Blo 1387513 7031447 := bstep (se 1 (by rfl) ⟨5273585, by rfl⟩ : syracuseStep 7031447 = 10547171) B10547171
theorem B2083481 : Blo 1387513 2083481 := bstep (se 2 (by rfl) ⟨781305, by rfl⟩ : syracuseStep 2083481 = 1562611) B1562611
theorem B3517121 : Blo 1387513 3517121 := bstep (se 2 (by rfl) ⟨1318920, by rfl⟩ : syracuseStep 3517121 = 2637841) B2637841
theorem B11258585 : Blo 1387513 11258585 := bstep (se 2 (by rfl) ⟨4221969, by rfl⟩ : syracuseStep 11258585 = 8443939) B8443939
theorem B2083595 : Blo 1387513 2083595 := bstep (se 1 (by rfl) ⟨1562696, by rfl⟩ : syracuseStep 2083595 = 3125393) B3125393
theorem B2083607 : Blo 1387513 2083607 := bstep (se 1 (by rfl) ⟨1562705, by rfl⟩ : syracuseStep 2083607 = 3125411) B3125411
theorem B3754775 : Blo 1387513 3754775 := bstep (se 1 (by rfl) ⟨2816081, by rfl⟩ : syracuseStep 3754775 = 5632163) B5632163
theorem B2222873 : Blo 1387513 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B3124043 : Blo 1387513 3124043 := bstep (se 1 (by rfl) ⟨2343032, by rfl⟩ : syracuseStep 3124043 = 4686065) B4686065
theorem B2083673 : Blo 1387513 2083673 := bstep (se 2 (by rfl) ⟨781377, by rfl⟩ : syracuseStep 2083673 = 1562755) B1562755
theorem B3124097 : Blo 1387513 3124097 := bstep (se 2 (by rfl) ⟨1171536, by rfl⟩ : syracuseStep 3124097 = 2343073) B2343073
theorem B4688819 : Blo 1387513 4688819 := bstep (se 1 (by rfl) ⟨3516614, by rfl⟩ : syracuseStep 4688819 = 7033229) B7033229
theorem B2083787 : Blo 1387513 2083787 := bstep (se 1 (by rfl) ⟨1562840, by rfl⟩ : syracuseStep 2083787 = 3125681) B3125681
theorem B2083799 : Blo 1387513 2083799 := bstep (se 1 (by rfl) ⟨1562849, by rfl⟩ : syracuseStep 2083799 = 3125699) B3125699
theorem B2223065 : Blo 1387513 2223065 := bstep (se 2 (by rfl) ⟨833649, by rfl⟩ : syracuseStep 2223065 = 1667299) B1667299
theorem B11725829 : Blo 1387513 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B1387531 : Blo 1387513 1387531 := bstep (se 1 (by rfl) ⟨1040648, by rfl⟩ : syracuseStep 1387531 = 2081297) B2081297
theorem B1756171 : Blo 1387513 1756171 := bstep (se 1 (by rfl) ⟨1317128, by rfl⟩ : syracuseStep 1756171 = 2634257) B2634257
theorem B1387543 : Blo 1387513 1387543 := bstep (se 1 (by rfl) ⟨1040657, by rfl⟩ : syracuseStep 1387543 = 2081315) B2081315
theorem B1977367 : Blo 1387513 1977367 := bstep (se 1 (by rfl) ⟨1483025, by rfl⟩ : syracuseStep 1977367 = 2966051) B2966051
theorem B2083865 : Blo 1387513 2083865 := bstep (se 2 (by rfl) ⟨781449, by rfl⟩ : syracuseStep 2083865 = 1562899) B1562899
theorem B1387563 : Blo 1387513 1387563 := bstep (se 1 (by rfl) ⟨1040672, by rfl⟩ : syracuseStep 1387563 = 2081345) B2081345
theorem B5270579 : Blo 1387513 5270579 := bstep (se 1 (by rfl) ⟨3952934, by rfl⟩ : syracuseStep 5270579 = 7905869) B7905869
theorem B1387575 : Blo 1387513 1387575 := bstep (se 1 (by rfl) ⟨1040681, by rfl⟩ : syracuseStep 1387575 = 2081363) B2081363
theorem B1387595 : Blo 1387513 1387595 := bstep (se 1 (by rfl) ⟨1040696, by rfl⟩ : syracuseStep 1387595 = 2081393) B2081393
theorem B1387607 : Blo 1387513 1387607 := bstep (se 1 (by rfl) ⟨1040705, by rfl⟩ : syracuseStep 1387607 = 2081411) B2081411
theorem B3124313 : Blo 1387513 3124313 := bstep (se 2 (by rfl) ⟨1171617, by rfl⟩ : syracuseStep 3124313 = 2343235) B2343235
theorem B12659813 : Blo 1387513 12659813 := bstep (se 4 (by rfl) ⟨1186857, by rfl⟩ : syracuseStep 12659813 = 2373715) B2373715
theorem B1387627 : Blo 1387513 1387627 := bstep (se 1 (by rfl) ⟨1040720, by rfl⟩ : syracuseStep 1387627 = 2081441) B2081441
theorem B1387639 : Blo 1387513 1387639 := bstep (se 1 (by rfl) ⟨1040729, by rfl⟩ : syracuseStep 1387639 = 2081459) B2081459
theorem B1387659 : Blo 1387513 1387659 := bstep (se 1 (by rfl) ⟨1040744, by rfl⟩ : syracuseStep 1387659 = 2081489) B2081489
theorem B2083979 : Blo 1387513 2083979 := bstep (se 1 (by rfl) ⟨1562984, by rfl⟩ : syracuseStep 2083979 = 3125969) B3125969
theorem B1387671 : Blo 1387513 1387671 := bstep (se 1 (by rfl) ⟨1040753, by rfl⟩ : syracuseStep 1387671 = 2081507) B2081507
theorem B2083991 : Blo 1387513 2083991 := bstep (se 1 (by rfl) ⟨1562993, by rfl⟩ : syracuseStep 2083991 = 3125987) B3125987
theorem B1387691 : Blo 1387513 1387691 := bstep (se 1 (by rfl) ⟨1040768, by rfl⟩ : syracuseStep 1387691 = 2081537) B2081537
theorem B3124403 : Blo 1387513 3124403 := bstep (se 1 (by rfl) ⟨2343302, by rfl⟩ : syracuseStep 3124403 = 4686605) B4686605
theorem B1387703 : Blo 1387513 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B4689089 : Blo 1387513 4689089 := bstep (se 2 (by rfl) ⟨1758408, by rfl⟩ : syracuseStep 4689089 = 3516817) B3516817
theorem B1387723 : Blo 1387513 1387723 := bstep (se 1 (by rfl) ⟨1040792, by rfl⟩ : syracuseStep 1387723 = 2081585) B2081585
theorem B1387735 : Blo 1387513 1387735 := bstep (se 1 (by rfl) ⟨1040801, by rfl⟩ : syracuseStep 1387735 = 2081603) B2081603
theorem B3124439 : Blo 1387513 3124439 := bstep (se 1 (by rfl) ⟨2343329, by rfl⟩ : syracuseStep 3124439 = 4686659) B4686659
theorem B2084057 : Blo 1387513 2084057 := bstep (se 2 (by rfl) ⟨781521, by rfl⟩ : syracuseStep 2084057 = 1563043) B1563043
theorem B1387755 : Blo 1387513 1387755 := bstep (se 1 (by rfl) ⟨1040816, by rfl⟩ : syracuseStep 1387755 = 2081633) B2081633
theorem B1387767 : Blo 1387513 1387767 := bstep (se 1 (by rfl) ⟨1040825, by rfl⟩ : syracuseStep 1387767 = 2081651) B2081651
theorem B1387787 : Blo 1387513 1387787 := bstep (se 1 (by rfl) ⟨1040840, by rfl⟩ : syracuseStep 1387787 = 2081681) B2081681
theorem B1387799 : Blo 1387513 1387799 := bstep (se 1 (by rfl) ⟨1040849, by rfl⟩ : syracuseStep 1387799 = 2081699) B2081699
theorem B1387819 : Blo 1387513 1387819 := bstep (se 1 (by rfl) ⟨1040864, by rfl⟩ : syracuseStep 1387819 = 2081729) B2081729
theorem B3755315 : Blo 1387513 3755315 := bstep (se 1 (by rfl) ⟨2816486, by rfl⟩ : syracuseStep 3755315 = 5632973) B5632973
theorem B1387831 : Blo 1387513 1387831 := bstep (se 1 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 1387831 = 2081747) B2081747
theorem B17804609 : Blo 1387513 17804609 := bstep (se 2 (by rfl) ⟨6676728, by rfl⟩ : syracuseStep 17804609 = 13353457) B13353457
theorem B1387851 : Blo 1387513 1387851 := bstep (se 1 (by rfl) ⟨1040888, by rfl⟩ : syracuseStep 1387851 = 2081777) B2081777
theorem B2084171 : Blo 1387513 2084171 := bstep (se 1 (by rfl) ⟨1563128, by rfl⟩ : syracuseStep 2084171 = 3126257) B3126257
theorem B1387863 : Blo 1387513 1387863 := bstep (se 1 (by rfl) ⟨1040897, by rfl⟩ : syracuseStep 1387863 = 2081795) B2081795
theorem B2084183 : Blo 1387513 2084183 := bstep (se 1 (by rfl) ⟨1563137, by rfl⟩ : syracuseStep 2084183 = 3126275) B3126275
theorem B12021085 : Blo 1387513 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B1387883 : Blo 1387513 1387883 := bstep (se 1 (by rfl) ⟨1040912, by rfl⟩ : syracuseStep 1387883 = 2081825) B2081825
theorem B1387895 : Blo 1387513 1387895 := bstep (se 1 (by rfl) ⟨1040921, by rfl⟩ : syracuseStep 1387895 = 2081843) B2081843
theorem B1387915 : Blo 1387513 1387915 := bstep (se 1 (by rfl) ⟨1040936, by rfl⟩ : syracuseStep 1387915 = 2081873) B2081873
theorem B3124619 : Blo 1387513 3124619 := bstep (se 1 (by rfl) ⟨2343464, by rfl⟩ : syracuseStep 3124619 = 4686929) B4686929
theorem B1387927 : Blo 1387513 1387927 := bstep (se 1 (by rfl) ⟨1040945, by rfl⟩ : syracuseStep 1387927 = 2081891) B2081891
theorem B2084249 : Blo 1387513 2084249 := bstep (se 2 (by rfl) ⟨781593, by rfl⟩ : syracuseStep 2084249 = 1563187) B1563187
theorem B1387947 : Blo 1387513 1387947 := bstep (se 1 (by rfl) ⟨1040960, by rfl⟩ : syracuseStep 1387947 = 2081921) B2081921
theorem B1387959 : Blo 1387513 1387959 := bstep (se 1 (by rfl) ⟨1040969, by rfl⟩ : syracuseStep 1387959 = 2081939) B2081939
theorem B3124673 : Blo 1387513 3124673 := bstep (se 2 (by rfl) ⟨1171752, by rfl⟩ : syracuseStep 3124673 = 2343505) B2343505
theorem B1387979 : Blo 1387513 1387979 := bstep (se 1 (by rfl) ⟨1040984, by rfl⟩ : syracuseStep 1387979 = 2081969) B2081969
theorem B1387991 : Blo 1387513 1387991 := bstep (se 1 (by rfl) ⟨1040993, by rfl⟩ : syracuseStep 1387991 = 2081987) B2081987
theorem B1388011 : Blo 1387513 1388011 := bstep (se 1 (by rfl) ⟨1041008, by rfl⟩ : syracuseStep 1388011 = 2082017) B2082017
theorem B1388023 : Blo 1387513 1388023 := bstep (se 1 (by rfl) ⟨1041017, by rfl⟩ : syracuseStep 1388023 = 2082035) B2082035
theorem B1388043 : Blo 1387513 1388043 := bstep (se 1 (by rfl) ⟨1041032, by rfl⟩ : syracuseStep 1388043 = 2082065) B2082065
theorem B1388055 : Blo 1387513 1388055 := bstep (se 1 (by rfl) ⟨1041041, by rfl⟩ : syracuseStep 1388055 = 2082083) B2082083
theorem B1388075 : Blo 1387513 1388075 := bstep (se 1 (by rfl) ⟨1041056, by rfl⟩ : syracuseStep 1388075 = 2082113) B2082113
theorem B1388087 : Blo 1387513 1388087 := bstep (se 1 (by rfl) ⟨1041065, by rfl⟩ : syracuseStep 1388087 = 2082131) B2082131
theorem B8449601 : Blo 1387513 8449601 := bstep (se 2 (by rfl) ⟨3168600, by rfl⟩ : syracuseStep 8449601 = 6337201) B6337201
theorem B1388107 : Blo 1387513 1388107 := bstep (se 1 (by rfl) ⟨1041080, by rfl⟩ : syracuseStep 1388107 = 2082161) B2082161
theorem B1388119 : Blo 1387513 1388119 := bstep (se 1 (by rfl) ⟨1041089, by rfl⟩ : syracuseStep 1388119 = 2082179) B2082179
theorem B1388139 : Blo 1387513 1388139 := bstep (se 1 (by rfl) ⟨1041104, by rfl⟩ : syracuseStep 1388139 = 2082209) B2082209
theorem B1388151 : Blo 1387513 1388151 := bstep (se 1 (by rfl) ⟨1041113, by rfl⟩ : syracuseStep 1388151 = 2082227) B2082227
theorem B1388171 : Blo 1387513 1388171 := bstep (se 1 (by rfl) ⟨1041128, by rfl⟩ : syracuseStep 1388171 = 2082257) B2082257
theorem B1388183 : Blo 1387513 1388183 := bstep (se 1 (by rfl) ⟨1041137, by rfl⟩ : syracuseStep 1388183 = 2082275) B2082275
theorem B3124889 : Blo 1387513 3124889 := bstep (se 2 (by rfl) ⟨1171833, by rfl⟩ : syracuseStep 3124889 = 2343667) B2343667
theorem B1388203 : Blo 1387513 1388203 := bstep (se 1 (by rfl) ⟨1041152, by rfl⟩ : syracuseStep 1388203 = 2082305) B2082305
theorem B1388215 : Blo 1387513 1388215 := bstep (se 1 (by rfl) ⟨1041161, by rfl⟩ : syracuseStep 1388215 = 2082323) B2082323
theorem B1388235 : Blo 1387513 1388235 := bstep (se 1 (by rfl) ⟨1041176, by rfl⟩ : syracuseStep 1388235 = 2082353) B2082353
theorem B1502923 : Blo 1387513 1502923 := bstep (se 1 (by rfl) ⟨1127192, by rfl⟩ : syracuseStep 1502923 = 2254385) B2254385
theorem B1388247 : Blo 1387513 1388247 := bstep (se 1 (by rfl) ⟨1041185, by rfl⟩ : syracuseStep 1388247 = 2082371) B2082371
theorem B1388267 : Blo 1387513 1388267 := bstep (se 1 (by rfl) ⟨1041200, by rfl⟩ : syracuseStep 1388267 = 2082401) B2082401
theorem B3124979 : Blo 1387513 3124979 := bstep (se 1 (by rfl) ⟨2343734, by rfl⟩ : syracuseStep 3124979 = 4687469) B4687469
theorem B1388279 : Blo 1387513 1388279 := bstep (se 1 (by rfl) ⟨1041209, by rfl⟩ : syracuseStep 1388279 = 2082419) B2082419
theorem B1388299 : Blo 1387513 1388299 := bstep (se 1 (by rfl) ⟨1041224, by rfl⟩ : syracuseStep 1388299 = 2082449) B2082449
theorem B1388311 : Blo 1387513 1388311 := bstep (se 1 (by rfl) ⟨1041233, by rfl⟩ : syracuseStep 1388311 = 2082467) B2082467
theorem B3125015 : Blo 1387513 3125015 := bstep (se 1 (by rfl) ⟨2343761, by rfl⟩ : syracuseStep 3125015 = 4687523) B4687523
theorem B1388331 : Blo 1387513 1388331 := bstep (se 1 (by rfl) ⟨1041248, by rfl⟩ : syracuseStep 1388331 = 2082497) B2082497
theorem B1388343 : Blo 1387513 1388343 := bstep (se 1 (by rfl) ⟨1041257, by rfl⟩ : syracuseStep 1388343 = 2082515) B2082515
theorem B1388363 : Blo 1387513 1388363 := bstep (se 1 (by rfl) ⟨1041272, by rfl⟩ : syracuseStep 1388363 = 2082545) B2082545
theorem B1978187 : Blo 1387513 1978187 := bstep (se 1 (by rfl) ⟨1483640, by rfl⟩ : syracuseStep 1978187 = 2967281) B2967281
theorem B1388375 : Blo 1387513 1388375 := bstep (se 1 (by rfl) ⟨1041281, by rfl⟩ : syracuseStep 1388375 = 2082563) B2082563
theorem B1388395 : Blo 1387513 1388395 := bstep (se 1 (by rfl) ⟨1041296, by rfl⟩ : syracuseStep 1388395 = 2082593) B2082593
theorem B1388407 : Blo 1387513 1388407 := bstep (se 1 (by rfl) ⟨1041305, by rfl⟩ : syracuseStep 1388407 = 2082611) B2082611
theorem B1388427 : Blo 1387513 1388427 := bstep (se 1 (by rfl) ⟨1041320, by rfl⟩ : syracuseStep 1388427 = 2082641) B2082641
theorem B1388439 : Blo 1387513 1388439 := bstep (se 1 (by rfl) ⟨1041329, by rfl⟩ : syracuseStep 1388439 = 2082659) B2082659
theorem B1388459 : Blo 1387513 1388459 := bstep (se 1 (by rfl) ⟨1041344, by rfl⟩ : syracuseStep 1388459 = 2082689) B2082689
theorem B1388471 : Blo 1387513 1388471 := bstep (se 1 (by rfl) ⟨1041353, by rfl⟩ : syracuseStep 1388471 = 2082707) B2082707
theorem B1388491 : Blo 1387513 1388491 := bstep (se 1 (by rfl) ⟨1041368, by rfl⟩ : syracuseStep 1388491 = 2082737) B2082737
theorem B3125195 : Blo 1387513 3125195 := bstep (se 1 (by rfl) ⟨2343896, by rfl⟩ : syracuseStep 3125195 = 4687793) B4687793
theorem B1757143 : Blo 1387513 1757143 := bstep (se 1 (by rfl) ⟨1317857, by rfl⟩ : syracuseStep 1757143 = 2635715) B2635715
theorem B1388503 : Blo 1387513 1388503 := bstep (se 1 (by rfl) ⟨1041377, by rfl⟩ : syracuseStep 1388503 = 2082755) B2082755
theorem B1388523 : Blo 1387513 1388523 := bstep (se 1 (by rfl) ⟨1041392, by rfl⟩ : syracuseStep 1388523 = 2082785) B2082785
theorem B1388535 : Blo 1387513 1388535 := bstep (se 1 (by rfl) ⟨1041401, by rfl⟩ : syracuseStep 1388535 = 2082803) B2082803
theorem B3125249 : Blo 1387513 3125249 := bstep (se 2 (by rfl) ⟨1171968, by rfl⟩ : syracuseStep 3125249 = 2343937) B2343937
theorem B1388555 : Blo 1387513 1388555 := bstep (se 1 (by rfl) ⟨1041416, by rfl⟩ : syracuseStep 1388555 = 2082833) B2082833
theorem B1388567 : Blo 1387513 1388567 := bstep (se 1 (by rfl) ⟨1041425, by rfl⟩ : syracuseStep 1388567 = 2082851) B2082851
theorem B1388587 : Blo 1387513 1388587 := bstep (se 1 (by rfl) ⟨1041440, by rfl⟩ : syracuseStep 1388587 = 2082881) B2082881
theorem B1388599 : Blo 1387513 1388599 := bstep (se 1 (by rfl) ⟨1041449, by rfl⟩ : syracuseStep 1388599 = 2082899) B2082899
theorem B1388619 : Blo 1387513 1388619 := bstep (se 1 (by rfl) ⟨1041464, by rfl⟩ : syracuseStep 1388619 = 2082929) B2082929
theorem B1388631 : Blo 1387513 1388631 := bstep (se 1 (by rfl) ⟨1041473, by rfl⟩ : syracuseStep 1388631 = 2082947) B2082947
theorem B3952729 : Blo 1387513 3952729 := bstep (se 2 (by rfl) ⟨1482273, by rfl⟩ : syracuseStep 3952729 = 2964547) B2964547
theorem B4010077 : Blo 1387513 4010077 := bstep (se 3 (by rfl) ⟨751889, by rfl⟩ : syracuseStep 4010077 = 1503779) B1503779
theorem B1388651 : Blo 1387513 1388651 := bstep (se 1 (by rfl) ⟨1041488, by rfl⟩ : syracuseStep 1388651 = 2082977) B2082977
theorem B1388663 : Blo 1387513 1388663 := bstep (se 1 (by rfl) ⟨1041497, by rfl⟩ : syracuseStep 1388663 = 2082995) B2082995
theorem B1388683 : Blo 1387513 1388683 := bstep (se 1 (by rfl) ⟨1041512, by rfl⟩ : syracuseStep 1388683 = 2083025) B2083025
theorem B1388695 : Blo 1387513 1388695 := bstep (se 1 (by rfl) ⟨1041521, by rfl⟩ : syracuseStep 1388695 = 2083043) B2083043
theorem B1388715 : Blo 1387513 1388715 := bstep (se 1 (by rfl) ⟨1041536, by rfl⟩ : syracuseStep 1388715 = 2083073) B2083073
theorem B1388727 : Blo 1387513 1388727 := bstep (se 1 (by rfl) ⟨1041545, by rfl⟩ : syracuseStep 1388727 = 2083091) B2083091
theorem B5075137 : Blo 1387513 5075137 := bstep (se 2 (by rfl) ⟨1903176, by rfl⟩ : syracuseStep 5075137 = 3806353) B3806353
theorem B1388747 : Blo 1387513 1388747 := bstep (se 1 (by rfl) ⟨1041560, by rfl⟩ : syracuseStep 1388747 = 2083121) B2083121
theorem B1388759 : Blo 1387513 1388759 := bstep (se 1 (by rfl) ⟨1041569, by rfl⟩ : syracuseStep 1388759 = 2083139) B2083139
theorem B3125465 : Blo 1387513 3125465 := bstep (se 2 (by rfl) ⟨1172049, by rfl⟩ : syracuseStep 3125465 = 2344099) B2344099
theorem B1388779 : Blo 1387513 1388779 := bstep (se 1 (by rfl) ⟨1041584, by rfl⟩ : syracuseStep 1388779 = 2083169) B2083169
theorem B1388791 : Blo 1387513 1388791 := bstep (se 1 (by rfl) ⟨1041593, by rfl⟩ : syracuseStep 1388791 = 2083187) B2083187
theorem B1388811 : Blo 1387513 1388811 := bstep (se 1 (by rfl) ⟨1041608, by rfl⟩ : syracuseStep 1388811 = 2083217) B2083217
theorem B1388823 : Blo 1387513 1388823 := bstep (se 1 (by rfl) ⟨1041617, by rfl⟩ : syracuseStep 1388823 = 2083235) B2083235
theorem B1388843 : Blo 1387513 1388843 := bstep (se 1 (by rfl) ⟨1041632, by rfl⟩ : syracuseStep 1388843 = 2083265) B2083265
theorem B3125555 : Blo 1387513 3125555 := bstep (se 1 (by rfl) ⟨2344166, by rfl⟩ : syracuseStep 3125555 = 4688333) B4688333
theorem B1388855 : Blo 1387513 1388855 := bstep (se 1 (by rfl) ⟨1041641, by rfl⟩ : syracuseStep 1388855 = 2083283) B2083283
theorem B1388875 : Blo 1387513 1388875 := bstep (se 1 (by rfl) ⟨1041656, by rfl⟩ : syracuseStep 1388875 = 2083313) B2083313
theorem B1388887 : Blo 1387513 1388887 := bstep (se 1 (by rfl) ⟨1041665, by rfl⟩ : syracuseStep 1388887 = 2083331) B2083331
theorem B3125591 : Blo 1387513 3125591 := bstep (se 1 (by rfl) ⟨2344193, by rfl⟩ : syracuseStep 3125591 = 4688387) B4688387
theorem B1388907 : Blo 1387513 1388907 := bstep (se 1 (by rfl) ⟨1041680, by rfl⟩ : syracuseStep 1388907 = 2083361) B2083361
theorem B1388919 : Blo 1387513 1388919 := bstep (se 1 (by rfl) ⟨1041689, by rfl⟩ : syracuseStep 1388919 = 2083379) B2083379
theorem B2634113 : Blo 1387513 2634113 := bstep (se 2 (by rfl) ⟨987792, by rfl⟩ : syracuseStep 2634113 = 1975585) B1975585
theorem B10539395 : Blo 1387513 10539395 := bstep (se 1 (by rfl) ⟨7904546, by rfl⟩ : syracuseStep 10539395 = 15809093) B15809093
theorem B1388939 : Blo 1387513 1388939 := bstep (se 1 (by rfl) ⟨1041704, by rfl⟩ : syracuseStep 1388939 = 2083409) B2083409
theorem B3379607 : Blo 1387513 3379607 := bstep (se 1 (by rfl) ⟨2534705, by rfl⟩ : syracuseStep 3379607 = 5069411) B5069411
theorem B1388951 : Blo 1387513 1388951 := bstep (se 1 (by rfl) ⟨1041713, by rfl⟩ : syracuseStep 1388951 = 2083427) B2083427
theorem B1388971 : Blo 1387513 1388971 := bstep (se 1 (by rfl) ⟨1041728, by rfl⟩ : syracuseStep 1388971 = 2083457) B2083457
theorem B7909811 : Blo 1387513 7909811 := bstep (se 1 (by rfl) ⟨5932358, by rfl⟩ : syracuseStep 7909811 = 11864717) B11864717
theorem B1388983 : Blo 1387513 1388983 := bstep (se 1 (by rfl) ⟨1041737, by rfl⟩ : syracuseStep 1388983 = 2083475) B2083475
theorem B1389003 : Blo 1387513 1389003 := bstep (se 1 (by rfl) ⟨1041752, by rfl⟩ : syracuseStep 1389003 = 2083505) B2083505
theorem B1389015 : Blo 1387513 1389015 := bstep (se 1 (by rfl) ⟨1041761, by rfl⟩ : syracuseStep 1389015 = 2083523) B2083523
theorem B3953117 : Blo 1387513 3953117 := bstep (se 3 (by rfl) ⟨741209, by rfl⟩ : syracuseStep 3953117 = 1482419) B1482419
theorem B1389035 : Blo 1387513 1389035 := bstep (se 1 (by rfl) ⟨1041776, by rfl⟩ : syracuseStep 1389035 = 2083553) B2083553
theorem B1389047 : Blo 1387513 1389047 := bstep (se 1 (by rfl) ⟨1041785, by rfl⟩ : syracuseStep 1389047 = 2083571) B2083571
theorem B5272067 : Blo 1387513 5272067 := bstep (se 1 (by rfl) ⟨3954050, by rfl⟩ : syracuseStep 5272067 = 7908101) B7908101
theorem B3207691 : Blo 1387513 3207691 := bstep (se 1 (by rfl) ⟨2405768, by rfl⟩ : syracuseStep 3207691 = 4811537) B4811537
theorem B1561099 : Blo 1387513 1561099 := bstep (se 1 (by rfl) ⟨1170824, by rfl⟩ : syracuseStep 1561099 = 2341649) B2341649
theorem B64139789 : Blo 1387513 64139789 := bstep (se 3 (by rfl) ⟨12026210, by rfl⟩ : syracuseStep 64139789 = 24052421) B24052421
theorem B1389067 : Blo 1387513 1389067 := bstep (se 1 (by rfl) ⟨1041800, by rfl⟩ : syracuseStep 1389067 = 2083601) B2083601
theorem B3125771 : Blo 1387513 3125771 := bstep (se 1 (by rfl) ⟨2344328, by rfl⟩ : syracuseStep 3125771 = 4688657) B4688657
theorem B1389079 : Blo 1387513 1389079 := bstep (se 1 (by rfl) ⟨1041809, by rfl⟩ : syracuseStep 1389079 = 2083619) B2083619
theorem B1389099 : Blo 1387513 1389099 := bstep (se 1 (by rfl) ⟨1041824, by rfl⟩ : syracuseStep 1389099 = 2083649) B2083649
theorem B1389111 : Blo 1387513 1389111 := bstep (se 1 (by rfl) ⟨1041833, by rfl⟩ : syracuseStep 1389111 = 2083667) B2083667
theorem B5927489 : Blo 1387513 5927489 := bstep (se 2 (by rfl) ⟨2222808, by rfl⟩ : syracuseStep 5927489 = 4445617) B4445617
theorem B3125825 : Blo 1387513 3125825 := bstep (se 2 (by rfl) ⟨1172184, by rfl⟩ : syracuseStep 3125825 = 2344369) B2344369
theorem B1389131 : Blo 1387513 1389131 := bstep (se 1 (by rfl) ⟨1041848, by rfl⟩ : syracuseStep 1389131 = 2083697) B2083697
theorem B1389143 : Blo 1387513 1389143 := bstep (se 1 (by rfl) ⟨1041857, by rfl⟩ : syracuseStep 1389143 = 2083715) B2083715
theorem B1389163 : Blo 1387513 1389163 := bstep (se 1 (by rfl) ⟨1041872, by rfl⟩ : syracuseStep 1389163 = 2083745) B2083745
theorem B1561207 : Blo 1387513 1561207 := bstep (se 1 (by rfl) ⟨1170905, by rfl⟩ : syracuseStep 1561207 = 2341811) B2341811
theorem B1389175 : Blo 1387513 1389175 := bstep (se 1 (by rfl) ⟨1041881, by rfl⟩ : syracuseStep 1389175 = 2083763) B2083763
theorem B1389195 : Blo 1387513 1389195 := bstep (se 1 (by rfl) ⟨1041896, by rfl⟩ : syracuseStep 1389195 = 2083793) B2083793
theorem B1389207 : Blo 1387513 1389207 := bstep (se 1 (by rfl) ⟨1041905, by rfl⟩ : syracuseStep 1389207 = 2083811) B2083811
theorem B1389227 : Blo 1387513 1389227 := bstep (se 1 (by rfl) ⟨1041920, by rfl⟩ : syracuseStep 1389227 = 2083841) B2083841
theorem B1389239 : Blo 1387513 1389239 := bstep (se 1 (by rfl) ⟨1041929, by rfl⟩ : syracuseStep 1389239 = 2083859) B2083859
theorem B1389259 : Blo 1387513 1389259 := bstep (se 1 (by rfl) ⟨1041944, by rfl⟩ : syracuseStep 1389259 = 2083889) B2083889
theorem B1389271 : Blo 1387513 1389271 := bstep (se 1 (by rfl) ⟨1041953, by rfl⟩ : syracuseStep 1389271 = 2083907) B2083907
theorem B1389291 : Blo 1387513 1389291 := bstep (se 1 (by rfl) ⟨1041968, by rfl⟩ : syracuseStep 1389291 = 2083937) B2083937
theorem B1389303 : Blo 1387513 1389303 := bstep (se 1 (by rfl) ⟨1041977, by rfl⟩ : syracuseStep 1389303 = 2083955) B2083955
theorem B12669701 : Blo 1387513 12669701 := bstep (se 4 (by rfl) ⟨1187784, by rfl⟩ : syracuseStep 12669701 = 2375569) B2375569
theorem B1757963 : Blo 1387513 1757963 := bstep (se 1 (by rfl) ⟨1318472, by rfl⟩ : syracuseStep 1757963 = 2636945) B2636945
theorem B1389323 : Blo 1387513 1389323 := bstep (se 1 (by rfl) ⟨1041992, by rfl⟩ : syracuseStep 1389323 = 2083985) B2083985
theorem B1389335 : Blo 1387513 1389335 := bstep (se 1 (by rfl) ⟨1042001, by rfl⟩ : syracuseStep 1389335 = 2084003) B2084003
theorem B3126041 : Blo 1387513 3126041 := bstep (se 2 (by rfl) ⟨1172265, by rfl⟩ : syracuseStep 3126041 = 2344531) B2344531
theorem B1561387 : Blo 1387513 1561387 := bstep (se 1 (by rfl) ⟨1171040, by rfl⟩ : syracuseStep 1561387 = 2342081) B2342081
theorem B1389355 : Blo 1387513 1389355 := bstep (se 1 (by rfl) ⟨1042016, by rfl⟩ : syracuseStep 1389355 = 2084033) B2084033
theorem B7025453 : Blo 1387513 7025453 := bstep (se 3 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 7025453 = 2634545) B2634545
theorem B1389367 : Blo 1387513 1389367 := bstep (se 1 (by rfl) ⟨1042025, by rfl⟩ : syracuseStep 1389367 = 2084051) B2084051
theorem B1389387 : Blo 1387513 1389387 := bstep (se 1 (by rfl) ⟨1042040, by rfl⟩ : syracuseStep 1389387 = 2084081) B2084081
theorem B1389399 : Blo 1387513 1389399 := bstep (se 1 (by rfl) ⟨1042049, by rfl⟩ : syracuseStep 1389399 = 2084099) B2084099
theorem B1389419 : Blo 1387513 1389419 := bstep (se 1 (by rfl) ⟨1042064, by rfl⟩ : syracuseStep 1389419 = 2084129) B2084129
theorem B3126131 : Blo 1387513 3126131 := bstep (se 1 (by rfl) ⟨2344598, by rfl⟩ : syracuseStep 3126131 = 4689197) B4689197
theorem B1389431 : Blo 1387513 1389431 := bstep (se 1 (by rfl) ⟨1042073, by rfl⟩ : syracuseStep 1389431 = 2084147) B2084147
theorem B3167105 : Blo 1387513 3167105 := bstep (se 2 (by rfl) ⟨1187664, by rfl⟩ : syracuseStep 3167105 = 2375329) B2375329
theorem B1389451 : Blo 1387513 1389451 := bstep (se 1 (by rfl) ⟨1042088, by rfl⟩ : syracuseStep 1389451 = 2084177) B2084177
theorem B1561495 : Blo 1387513 1561495 := bstep (se 1 (by rfl) ⟨1171121, by rfl⟩ : syracuseStep 1561495 = 2342243) B2342243
theorem B3126167 : Blo 1387513 3126167 := bstep (se 1 (by rfl) ⟨2344625, by rfl⟩ : syracuseStep 3126167 = 4689251) B4689251
theorem B1389463 : Blo 1387513 1389463 := bstep (se 1 (by rfl) ⟨1042097, by rfl⟩ : syracuseStep 1389463 = 2084195) B2084195
theorem B1389483 : Blo 1387513 1389483 := bstep (se 1 (by rfl) ⟨1042112, by rfl⟩ : syracuseStep 1389483 = 2084225) B2084225
theorem B1389495 : Blo 1387513 1389495 := bstep (se 1 (by rfl) ⟨1042121, by rfl⟩ : syracuseStep 1389495 = 2084243) B2084243
theorem B5272523 : Blo 1387513 5272523 := bstep (se 1 (by rfl) ⟨3954392, by rfl⟩ : syracuseStep 5272523 = 7908785) B7908785
theorem B10277923 : Blo 1387513 10277923 := bstep (se 1 (by rfl) ⟨7708442, by rfl⟩ : syracuseStep 10277923 = 15416885) B15416885
theorem B1561675 : Blo 1387513 1561675 := bstep (se 1 (by rfl) ⟨1171256, by rfl⟩ : syracuseStep 1561675 = 2342513) B2342513
theorem B3126347 : Blo 1387513 3126347 := bstep (se 1 (by rfl) ⟨2344760, by rfl⟩ : syracuseStep 3126347 = 4689521) B4689521
theorem B3126401 : Blo 1387513 3126401 := bstep (se 2 (by rfl) ⟨1172400, by rfl⟩ : syracuseStep 3126401 = 2344801) B2344801
theorem B5272721 : Blo 1387513 5272721 := bstep (se 2 (by rfl) ⟨1977270, by rfl⟩ : syracuseStep 5272721 = 3954541) B3954541
theorem B36066485 : Blo 1387513 36066485 := bstep (se 5 (by rfl) ⟨1690616, by rfl⟩ : syracuseStep 36066485 = 3381233) B3381233
theorem B1561783 : Blo 1387513 1561783 := bstep (se 1 (by rfl) ⟨1171337, by rfl⟩ : syracuseStep 1561783 = 2342675) B2342675
theorem B2635031 : Blo 1387513 2635031 := bstep (se 1 (by rfl) ⟨1976273, by rfl⟩ : syracuseStep 2635031 = 3952547) B3952547
theorem B2815319 : Blo 1387513 2815319 := bstep (se 1 (by rfl) ⟨2111489, by rfl⟩ : syracuseStep 2815319 = 4222979) B4222979
theorem B1561963 : Blo 1387513 1561963 := bstep (se 1 (by rfl) ⟨1171472, by rfl⟩ : syracuseStep 1561963 = 2342945) B2342945
theorem B15226289 : Blo 1387513 15226289 := bstep (se 2 (by rfl) ⟨5709858, by rfl⟩ : syracuseStep 15226289 = 11419717) B11419717
theorem B1562071 : Blo 1387513 1562071 := bstep (se 1 (by rfl) ⟨1171553, by rfl⟩ : syracuseStep 1562071 = 2343107) B2343107
theorem B5633587 : Blo 1387513 5633587 := bstep (se 1 (by rfl) ⟨4225190, by rfl⟩ : syracuseStep 5633587 = 8450381) B8450381
theorem B3167873 : Blo 1387513 3167873 := bstep (se 2 (by rfl) ⟨1187952, by rfl⟩ : syracuseStep 3167873 = 2375905) B2375905
theorem B7509635 : Blo 1387513 7509635 := bstep (se 1 (by rfl) ⟨5632226, by rfl⟩ : syracuseStep 7509635 = 11264453) B11264453
theorem B1562251 : Blo 1387513 1562251 := bstep (se 1 (by rfl) ⟨1171688, by rfl⟩ : syracuseStep 1562251 = 2343377) B2343377
theorem B1562359 : Blo 1387513 1562359 := bstep (se 1 (by rfl) ⟨1171769, by rfl⟩ : syracuseStep 1562359 = 2343539) B2343539
theorem B2635571 : Blo 1387513 2635571 := bstep (se 1 (by rfl) ⟨1976678, by rfl⟩ : syracuseStep 2635571 = 3953357) B3953357
theorem B13006693 : Blo 1387513 13006693 := bstep (se 4 (by rfl) ⟨1219377, by rfl⟩ : syracuseStep 13006693 = 2438755) B2438755
theorem B7911269 : Blo 1387513 7911269 := bstep (se 4 (by rfl) ⟨741681, by rfl⟩ : syracuseStep 7911269 = 1483363) B1483363
theorem B4446103 : Blo 1387513 4446103 := bstep (se 1 (by rfl) ⟨3334577, by rfl⟩ : syracuseStep 4446103 = 6669155) B6669155
theorem B5273495 : Blo 1387513 5273495 := bstep (se 1 (by rfl) ⟨3955121, by rfl⟩ : syracuseStep 5273495 = 7910243) B7910243
theorem B1562539 : Blo 1387513 1562539 := bstep (se 1 (by rfl) ⟨1171904, by rfl⟩ : syracuseStep 1562539 = 2343809) B2343809
theorem B3512281 : Blo 1387513 3512281 := bstep (se 2 (by rfl) ⟨1317105, by rfl⟩ : syracuseStep 3512281 = 2634211) B2634211
theorem B1562647 : Blo 1387513 1562647 := bstep (se 1 (by rfl) ⟨1171985, by rfl⟩ : syracuseStep 1562647 = 2343971) B2343971
theorem B5003309 : Blo 1387513 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B4683851 : Blo 1387513 4683851 := bstep (se 1 (by rfl) ⟨3512888, by rfl⟩ : syracuseStep 4683851 = 7025777) B7025777
theorem B13531211 : Blo 1387513 13531211 := bstep (se 1 (by rfl) ⟨10148408, by rfl⟩ : syracuseStep 13531211 = 20296817) B20296817
theorem B5273693 : Blo 1387513 5273693 := bstep (se 3 (by rfl) ⟨988817, by rfl⟩ : syracuseStep 5273693 = 1977635) B1977635
theorem B5929163 : Blo 1387513 5929163 := bstep (se 1 (by rfl) ⟨4446872, by rfl⟩ : syracuseStep 5929163 = 8893745) B8893745
theorem B2816203 : Blo 1387513 2816203 := bstep (se 1 (by rfl) ⟨2112152, by rfl⟩ : syracuseStep 2816203 = 4224305) B4224305
theorem B1562827 : Blo 1387513 1562827 := bstep (se 1 (by rfl) ⟨1172120, by rfl⟩ : syracuseStep 1562827 = 2344241) B2344241
theorem B2636057 : Blo 1387513 2636057 := bstep (se 2 (by rfl) ⟨988521, by rfl⟩ : syracuseStep 2636057 = 1977043) B1977043
theorem B1562935 : Blo 1387513 1562935 := bstep (se 1 (by rfl) ⟨1172201, by rfl⟩ : syracuseStep 1562935 = 2344403) B2344403
theorem B4684121 : Blo 1387513 4684121 := bstep (se 2 (by rfl) ⟨1756545, by rfl⟩ : syracuseStep 4684121 = 3513091) B3513091
theorem B4446667 : Blo 1387513 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B1563115 : Blo 1387513 1563115 := bstep (se 1 (by rfl) ⟨1172336, by rfl⟩ : syracuseStep 1563115 = 2344673) B2344673
theorem B3562049 : Blo 1387513 3562049 := bstep (se 2 (by rfl) ⟨1335768, by rfl⟩ : syracuseStep 3562049 = 2671537) B2671537
theorem B13351499 : Blo 1387513 13351499 := bstep (se 1 (by rfl) ⟨10013624, by rfl⟩ : syracuseStep 13351499 = 20027249) B20027249
theorem B4446809 : Blo 1387513 4446809 := bstep (se 2 (by rfl) ⟨1667553, by rfl⟩ : syracuseStep 4446809 = 3335107) B3335107
theorem B8010341 : Blo 1387513 8010341 := bstep (se 4 (by rfl) ⟨750969, by rfl⟩ : syracuseStep 8010341 = 1501939) B1501939
theorem B2964377 : Blo 1387513 2964377 := bstep (se 2 (by rfl) ⟨1111641, by rfl⟩ : syracuseStep 2964377 = 2223283) B2223283
theorem B12671923 : Blo 1387513 12671923 := bstep (se 1 (by rfl) ⟨9503942, by rfl⟩ : syracuseStep 12671923 = 19007885) B19007885
theorem B4750273 : Blo 1387513 4750273 := bstep (se 2 (by rfl) ⟨1781352, by rfl⟩ : syracuseStep 4750273 = 3562705) B3562705
theorem B5929949 : Blo 1387513 5929949 := bstep (se 3 (by rfl) ⟨1111865, by rfl⟩ : syracuseStep 5929949 = 2223731) B2223731
theorem B4684823 : Blo 1387513 4684823 := bstep (se 1 (by rfl) ⟨3513617, by rfl⟩ : syracuseStep 4684823 = 7027235) B7027235
theorem B3513395 : Blo 1387513 3513395 := bstep (se 1 (by rfl) ⟨2635046, by rfl⟩ : syracuseStep 3513395 = 5270093) B5270093
theorem B5626955 : Blo 1387513 5626955 := bstep (se 1 (by rfl) ⟨4220216, by rfl⟩ : syracuseStep 5626955 = 8440433) B8440433
theorem B1522795 : Blo 1387513 1522795 := bstep (se 1 (by rfl) ⟨1142096, by rfl⟩ : syracuseStep 1522795 = 2284193) B2284193
theorem B2342027 : Blo 1387513 2342027 := bstep (se 1 (by rfl) ⟨1756520, by rfl⟩ : syracuseStep 2342027 = 3513041) B3513041
theorem B2342155 : Blo 1387513 2342155 := bstep (se 1 (by rfl) ⟨1756616, by rfl⟩ : syracuseStep 2342155 = 3513233) B3513233
theorem B10550573 : Blo 1387513 10550573 := bstep (se 3 (by rfl) ⟨1978232, by rfl⟩ : syracuseStep 10550573 = 3956465) B3956465
theorem B3956033 : Blo 1387513 3956033 := bstep (se 2 (by rfl) ⟨1483512, by rfl⟩ : syracuseStep 3956033 = 2967025) B2967025
theorem B3513689 : Blo 1387513 3513689 := bstep (se 2 (by rfl) ⟨1317633, by rfl⟩ : syracuseStep 3513689 = 2635267) B2635267
theorem B2342297 : Blo 1387513 2342297 := bstep (se 2 (by rfl) ⟨878361, by rfl⟩ : syracuseStep 2342297 = 1756723) B1756723
theorem B3956147 : Blo 1387513 3956147 := bstep (se 1 (by rfl) ⟨2967110, by rfl⟩ : syracuseStep 3956147 = 5934221) B5934221
theorem B5004737 : Blo 1387513 5004737 := bstep (se 2 (by rfl) ⟨1876776, by rfl⟩ : syracuseStep 5004737 = 3753553) B3753553
theorem B7904729 : Blo 1387513 7904729 := bstep (se 2 (by rfl) ⟨2964273, by rfl⟩ : syracuseStep 7904729 = 5928547) B5928547
theorem B1875479 : Blo 1387513 1875479 := bstep (se 1 (by rfl) ⟨1406609, by rfl⟩ : syracuseStep 1875479 = 2813219) B2813219
theorem B2342425 : Blo 1387513 2342425 := bstep (se 2 (by rfl) ⟨878409, by rfl⟩ : syracuseStep 2342425 = 1756819) B1756819
theorem B4685363 : Blo 1387513 4685363 := bstep (se 1 (by rfl) ⟨3514022, by rfl⟩ : syracuseStep 4685363 = 7028045) B7028045
theorem B1482359 : Blo 1387513 1482359 := bstep (se 1 (by rfl) ⟨1111769, by rfl⟩ : syracuseStep 1482359 = 2223539) B2223539
theorem B7503491 : Blo 1387513 7503491 := bstep (se 1 (by rfl) ⟨5627618, by rfl⟩ : syracuseStep 7503491 = 11255237) B11255237
theorem B26033815 : Blo 1387513 26033815 := bstep (se 1 (by rfl) ⟨19525361, by rfl⟩ : syracuseStep 26033815 = 39050723) B39050723
theorem B90054341 : Blo 1387513 90054341 := bstep (se 4 (by rfl) ⟨8442594, by rfl⟩ : syracuseStep 90054341 = 16885189) B16885189
theorem B2637515 : Blo 1387513 2637515 := bstep (se 1 (by rfl) ⟨1978136, by rfl⟩ : syracuseStep 2637515 = 3956273) B3956273
theorem B10542797 : Blo 1387513 10542797 := bstep (se 3 (by rfl) ⟨1976774, by rfl⟩ : syracuseStep 10542797 = 3953549) B3953549
theorem B4448051 : Blo 1387513 4448051 := bstep (se 1 (by rfl) ⟨3336038, by rfl⟩ : syracuseStep 4448051 = 6672077) B6672077
theorem B4685633 : Blo 1387513 4685633 := bstep (se 2 (by rfl) ⟨1757112, by rfl⟩ : syracuseStep 4685633 = 3514225) B3514225
theorem B2637697 : Blo 1387513 2637697 := bstep (se 2 (by rfl) ⟨989136, by rfl⟩ : syracuseStep 2637697 = 1978273) B1978273
theorem B16883633 : Blo 1387513 16883633 := bstep (se 2 (by rfl) ⟨6331362, by rfl⟩ : syracuseStep 16883633 = 12662725) B12662725
theorem B17121203 : Blo 1387513 17121203 := bstep (se 1 (by rfl) ⟨12840902, by rfl⟩ : syracuseStep 17121203 = 25681805) B25681805
theorem B7028855 : Blo 1387513 7028855 := bstep (se 1 (by rfl) ⟨5271641, by rfl⟩ : syracuseStep 7028855 = 10543283) B10543283
theorem B5931265 : Blo 1387513 5931265 := bstep (se 2 (by rfl) ⟨2224224, by rfl⟩ : syracuseStep 5931265 = 4448449) B4448449
theorem B4448513 : Blo 1387513 4448513 := bstep (se 2 (by rfl) ⟨1668192, by rfl⟩ : syracuseStep 4448513 = 3336385) B3336385
theorem B6766849 : Blo 1387513 6766849 := bstep (se 2 (by rfl) ⟨2537568, by rfl⟩ : syracuseStep 6766849 = 5075137) B5075137
theorem B2253071 : Blo 1387513 2253071 := bstep (se 1 (by rfl) ⟨1689803, by rfl⟩ : syracuseStep 2253071 = 3379607) B3379607
theorem B3514711 : Blo 1387513 3514711 := bstep (se 1 (by rfl) ⟨2636033, by rfl⟩ : syracuseStep 3514711 = 5272067) B5272067
theorem B4686227 : Blo 1387513 4686227 := bstep (se 1 (by rfl) ⟨3514670, by rfl⟩ : syracuseStep 4686227 = 7029341) B7029341
theorem B2081339 : Blo 1387513 2081339 := bstep (se 1 (by rfl) ⟨1561004, by rfl⟩ : syracuseStep 2081339 = 3122009) B3122009
theorem B2081399 : Blo 1387513 2081399 := bstep (se 1 (by rfl) ⟨1561049, by rfl⟩ : syracuseStep 2081399 = 3122099) B3122099
theorem B3515015 : Blo 1387513 3515015 := bstep (se 1 (by rfl) ⟨2636261, by rfl⟩ : syracuseStep 3515015 = 5272523) B5272523
theorem B2343559 : Blo 1387513 2343559 := bstep (se 1 (by rfl) ⟨1757669, by rfl⟩ : syracuseStep 2343559 = 3515339) B3515339
theorem B2081423 : Blo 1387513 2081423 := bstep (se 1 (by rfl) ⟨1561067, by rfl⟩ : syracuseStep 2081423 = 3122135) B3122135
theorem B2081465 : Blo 1387513 2081465 := bstep (se 2 (by rfl) ⟨780549, by rfl⟩ : syracuseStep 2081465 = 1561099) B1561099
theorem B2081543 : Blo 1387513 2081543 := bstep (se 1 (by rfl) ⟨1561157, by rfl⟩ : syracuseStep 2081543 = 3122315) B3122315
theorem B3515147 : Blo 1387513 3515147 := bstep (se 1 (by rfl) ⟨2636360, by rfl⟩ : syracuseStep 3515147 = 5272721) B5272721
theorem B24044323 : Blo 1387513 24044323 := bstep (se 1 (by rfl) ⟨18033242, by rfl⟩ : syracuseStep 24044323 = 36066485) B36066485
theorem B2081579 : Blo 1387513 2081579 := bstep (se 1 (by rfl) ⟨1561184, by rfl⟩ : syracuseStep 2081579 = 3122369) B3122369
theorem B2081609 : Blo 1387513 2081609 := bstep (se 2 (by rfl) ⟨780603, by rfl⟩ : syracuseStep 2081609 = 1561207) B1561207
theorem B1876879 : Blo 1387513 1876879 := bstep (se 1 (by rfl) ⟨1407659, by rfl⟩ : syracuseStep 1876879 = 2815319) B2815319
theorem B2081723 : Blo 1387513 2081723 := bstep (se 1 (by rfl) ⟨1561292, by rfl⟩ : syracuseStep 2081723 = 3122585) B3122585
theorem B10150859 : Blo 1387513 10150859 := bstep (se 1 (by rfl) ⟨7613144, by rfl⟩ : syracuseStep 10150859 = 15226289) B15226289
theorem B2081783 : Blo 1387513 2081783 := bstep (se 1 (by rfl) ⟨1561337, by rfl⟩ : syracuseStep 2081783 = 3122675) B3122675
theorem B2081807 : Blo 1387513 2081807 := bstep (se 1 (by rfl) ⟨1561355, by rfl⟩ : syracuseStep 2081807 = 3122711) B3122711
theorem B3802145 : Blo 1387513 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B2081849 : Blo 1387513 2081849 := bstep (se 2 (by rfl) ⟨780693, by rfl⟩ : syracuseStep 2081849 = 1561387) B1561387
theorem B7029827 : Blo 1387513 7029827 := bstep (se 1 (by rfl) ⟨5272370, by rfl⟩ : syracuseStep 7029827 = 10544741) B10544741
theorem B5006423 : Blo 1387513 5006423 := bstep (se 1 (by rfl) ⟨3754817, by rfl⟩ : syracuseStep 5006423 = 7509635) B7509635
theorem B2081927 : Blo 1387513 2081927 := bstep (se 1 (by rfl) ⟨1561445, by rfl⟩ : syracuseStep 2081927 = 3122891) B3122891
theorem B2081963 : Blo 1387513 2081963 := bstep (se 1 (by rfl) ⟨1561472, by rfl⟩ : syracuseStep 2081963 = 3122945) B3122945
theorem B2081993 : Blo 1387513 2081993 := bstep (se 2 (by rfl) ⟨780747, by rfl⟩ : syracuseStep 2081993 = 1561495) B1561495
theorem B3515663 : Blo 1387513 3515663 := bstep (se 1 (by rfl) ⟨2636747, by rfl⟩ : syracuseStep 3515663 = 5273495) B5273495
theorem B2344207 : Blo 1387513 2344207 := bstep (se 1 (by rfl) ⟨1758155, by rfl⟩ : syracuseStep 2344207 = 3516311) B3516311
theorem B2082107 : Blo 1387513 2082107 := bstep (se 1 (by rfl) ⟨1561580, by rfl⟩ : syracuseStep 2082107 = 3123161) B3123161
theorem B2082167 : Blo 1387513 2082167 := bstep (se 1 (by rfl) ⟨1561625, by rfl⟩ : syracuseStep 2082167 = 3123251) B3123251
theorem B7603591 : Blo 1387513 7603591 := bstep (se 1 (by rfl) ⟨5702693, by rfl⟩ : syracuseStep 7603591 = 11405387) B11405387
theorem B3122567 : Blo 1387513 3122567 := bstep (se 1 (by rfl) ⟨2341925, by rfl⟩ : syracuseStep 3122567 = 4683851) B4683851
theorem B7030151 : Blo 1387513 7030151 := bstep (se 1 (by rfl) ⟨5272613, by rfl⟩ : syracuseStep 7030151 = 10545227) B10545227
theorem B9020807 : Blo 1387513 9020807 := bstep (se 1 (by rfl) ⟨6765605, by rfl⟩ : syracuseStep 9020807 = 13531211) B13531211
theorem B2082191 : Blo 1387513 2082191 := bstep (se 1 (by rfl) ⟨1561643, by rfl⟩ : syracuseStep 2082191 = 3123287) B3123287
theorem B3515795 : Blo 1387513 3515795 := bstep (se 1 (by rfl) ⟨2636846, by rfl⟩ : syracuseStep 3515795 = 5273693) B5273693
theorem B2082233 : Blo 1387513 2082233 := bstep (se 2 (by rfl) ⟨780837, by rfl⟩ : syracuseStep 2082233 = 1561675) B1561675
theorem B18990541 : Blo 1387513 18990541 := bstep (se 3 (by rfl) ⟨3560726, by rfl⟩ : syracuseStep 18990541 = 7121453) B7121453
theorem B2082311 : Blo 1387513 2082311 := bstep (se 1 (by rfl) ⟨1561733, by rfl⟩ : syracuseStep 2082311 = 3123467) B3123467
theorem B2082347 : Blo 1387513 2082347 := bstep (se 1 (by rfl) ⟨1561760, by rfl⟩ : syracuseStep 2082347 = 3123521) B3123521
theorem B3122747 : Blo 1387513 3122747 := bstep (se 1 (by rfl) ⟨2342060, by rfl⟩ : syracuseStep 3122747 = 4684121) B4684121
theorem B2082377 : Blo 1387513 2082377 := bstep (se 2 (by rfl) ⟨780891, by rfl⟩ : syracuseStep 2082377 = 1561783) B1561783
theorem B7128695 : Blo 1387513 7128695 := bstep (se 1 (by rfl) ⟨5346521, by rfl⟩ : syracuseStep 7128695 = 10693043) B10693043
theorem B3122873 : Blo 1387513 3122873 := bstep (se 2 (by rfl) ⟨1171077, by rfl⟩ : syracuseStep 3122873 = 2342155) B2342155
theorem B2082491 : Blo 1387513 2082491 := bstep (se 1 (by rfl) ⟨1561868, by rfl⟩ : syracuseStep 2082491 = 3123737) B3123737
theorem B2082551 : Blo 1387513 2082551 := bstep (se 1 (by rfl) ⟨1561913, by rfl⟩ : syracuseStep 2082551 = 3123827) B3123827
theorem B9013007 : Blo 1387513 9013007 := bstep (se 1 (by rfl) ⟨6759755, by rfl⟩ : syracuseStep 9013007 = 13519511) B13519511
theorem B2082575 : Blo 1387513 2082575 := bstep (se 1 (by rfl) ⟨1561931, by rfl⟩ : syracuseStep 2082575 = 3123863) B3123863
theorem B4687631 : Blo 1387513 4687631 := bstep (se 1 (by rfl) ⟨3515723, by rfl⟩ : syracuseStep 4687631 = 7031447) B7031447
theorem B2344747 : Blo 1387513 2344747 := bstep (se 1 (by rfl) ⟨1758560, by rfl⟩ : syracuseStep 2344747 = 3517121) B3517121
theorem B2082617 : Blo 1387513 2082617 := bstep (se 2 (by rfl) ⟨780981, by rfl⟩ : syracuseStep 2082617 = 1561963) B1561963
theorem B7505723 : Blo 1387513 7505723 := bstep (se 1 (by rfl) ⟨5629292, by rfl⟩ : syracuseStep 7505723 = 11258585) B11258585
theorem B2082695 : Blo 1387513 2082695 := bstep (se 1 (by rfl) ⟨1562021, by rfl⟩ : syracuseStep 2082695 = 3124043) B3124043
theorem B2082731 : Blo 1387513 2082731 := bstep (se 1 (by rfl) ⟨1562048, by rfl⟩ : syracuseStep 2082731 = 3124097) B3124097
theorem B1976251 : Blo 1387513 1976251 := bstep (se 1 (by rfl) ⟨1482188, by rfl⟩ : syracuseStep 1976251 = 2964377) B2964377
theorem B2082761 : Blo 1387513 2082761 := bstep (se 2 (by rfl) ⟨781035, by rfl⟩ : syracuseStep 2082761 = 1562071) B1562071
theorem B7817219 : Blo 1387513 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B33785869 : Blo 1387513 33785869 := bstep (se 3 (by rfl) ⟨6334850, by rfl⟩ : syracuseStep 33785869 = 12669701) B12669701
theorem B3123215 : Blo 1387513 3123215 := bstep (se 1 (by rfl) ⟨2342411, by rfl⟩ : syracuseStep 3123215 = 4684823) B4684823
theorem B4687901 : Blo 1387513 4687901 := bstep (se 3 (by rfl) ⟨878981, by rfl⟩ : syracuseStep 4687901 = 1757963) B1757963
theorem B3123233 : Blo 1387513 3123233 := bstep (se 2 (by rfl) ⟨1171212, by rfl⟩ : syracuseStep 3123233 = 2342425) B2342425
theorem B2082875 : Blo 1387513 2082875 := bstep (se 1 (by rfl) ⟨1562156, by rfl⟩ : syracuseStep 2082875 = 3124313) B3124313
theorem B8439875 : Blo 1387513 8439875 := bstep (se 1 (by rfl) ⟨6329906, by rfl⟩ : syracuseStep 8439875 = 12659813) B12659813
theorem B2082935 : Blo 1387513 2082935 := bstep (se 1 (by rfl) ⟨1562201, by rfl⟩ : syracuseStep 2082935 = 3124403) B3124403
theorem B2082959 : Blo 1387513 2082959 := bstep (se 1 (by rfl) ⟨1562219, by rfl⟩ : syracuseStep 2082959 = 3124439) B3124439
theorem B2083001 : Blo 1387513 2083001 := bstep (se 2 (by rfl) ⟨781125, by rfl⟩ : syracuseStep 2083001 = 1562251) B1562251
theorem B34711753 : Blo 1387513 34711753 := bstep (se 2 (by rfl) ⟨13016907, by rfl⟩ : syracuseStep 34711753 = 26033815) B26033815
theorem B2083079 : Blo 1387513 2083079 := bstep (se 1 (by rfl) ⟨1562309, by rfl⟩ : syracuseStep 2083079 = 3124619) B3124619
theorem B68512013 : Blo 1387513 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B3336491 : Blo 1387513 3336491 := bstep (se 1 (by rfl) ⟨2502368, by rfl⟩ : syracuseStep 3336491 = 5004737) B5004737
theorem B2083115 : Blo 1387513 2083115 := bstep (se 1 (by rfl) ⟨1562336, by rfl⟩ : syracuseStep 2083115 = 3124673) B3124673
theorem B5269819 : Blo 1387513 5269819 := bstep (se 1 (by rfl) ⟨3952364, by rfl⟩ : syracuseStep 5269819 = 7904729) B7904729
theorem B2083145 : Blo 1387513 2083145 := bstep (se 2 (by rfl) ⟨781179, by rfl⟩ : syracuseStep 2083145 = 1562359) B1562359
theorem B3123575 : Blo 1387513 3123575 := bstep (se 1 (by rfl) ⟨2342681, by rfl⟩ : syracuseStep 3123575 = 4685363) B4685363
theorem B2083259 : Blo 1387513 2083259 := bstep (se 1 (by rfl) ⟨1562444, by rfl⟩ : syracuseStep 2083259 = 3124889) B3124889
theorem B2083319 : Blo 1387513 2083319 := bstep (se 1 (by rfl) ⟨1562489, by rfl⟩ : syracuseStep 2083319 = 3124979) B3124979
theorem B3516929 : Blo 1387513 3516929 := bstep (se 2 (by rfl) ⟨1318848, by rfl⟩ : syracuseStep 3516929 = 2637697) B2637697
theorem B2083343 : Blo 1387513 2083343 := bstep (se 1 (by rfl) ⟨1562507, by rfl⟩ : syracuseStep 2083343 = 3125015) B3125015
theorem B3123755 : Blo 1387513 3123755 := bstep (se 1 (by rfl) ⟨2342816, by rfl⟩ : syracuseStep 3123755 = 4685633) B4685633
theorem B2083385 : Blo 1387513 2083385 := bstep (se 2 (by rfl) ⟨781269, by rfl⟩ : syracuseStep 2083385 = 1562539) B1562539
theorem B11414135 : Blo 1387513 11414135 := bstep (se 1 (by rfl) ⟨8560601, by rfl⟩ : syracuseStep 11414135 = 17121203) B17121203
theorem B2083463 : Blo 1387513 2083463 := bstep (se 1 (by rfl) ⟨1562597, by rfl⟩ : syracuseStep 2083463 = 3125195) B3125195
theorem B2083499 : Blo 1387513 2083499 := bstep (se 1 (by rfl) ⟨1562624, by rfl⟩ : syracuseStep 2083499 = 3125249) B3125249
theorem B2083529 : Blo 1387513 2083529 := bstep (se 2 (by rfl) ⟨781323, by rfl⟩ : syracuseStep 2083529 = 1562647) B1562647
theorem B25340633 : Blo 1387513 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B17107685 : Blo 1387513 17107685 := bstep (se 4 (by rfl) ⟨1603845, by rfl⟩ : syracuseStep 17107685 = 3207691) B3207691
theorem B5630735 : Blo 1387513 5630735 := bstep (se 1 (by rfl) ⟨4223051, by rfl⟩ : syracuseStep 5630735 = 8446103) B8446103
theorem B5270305 : Blo 1387513 5270305 := bstep (se 2 (by rfl) ⟨1976364, by rfl⟩ : syracuseStep 5270305 = 3952729) B3952729
theorem B2083643 : Blo 1387513 2083643 := bstep (se 1 (by rfl) ⟨1562732, by rfl⟩ : syracuseStep 2083643 = 3125465) B3125465
theorem B2083703 : Blo 1387513 2083703 := bstep (se 1 (by rfl) ⟨1562777, by rfl⟩ : syracuseStep 2083703 = 3125555) B3125555
theorem B5073799 : Blo 1387513 5073799 := bstep (se 1 (by rfl) ⟨3805349, by rfl⟩ : syracuseStep 5073799 = 7610699) B7610699
theorem B2083727 : Blo 1387513 2083727 := bstep (se 1 (by rfl) ⟨1562795, by rfl⟩ : syracuseStep 2083727 = 3125591) B3125591
theorem B3124115 : Blo 1387513 3124115 := bstep (se 1 (by rfl) ⟨2343086, by rfl⟩ : syracuseStep 3124115 = 4686173) B4686173
theorem B1756075 : Blo 1387513 1756075 := bstep (se 1 (by rfl) ⟨1317056, by rfl⟩ : syracuseStep 1756075 = 2634113) B2634113
theorem B2501561 : Blo 1387513 2501561 := bstep (se 2 (by rfl) ⟨938085, by rfl⟩ : syracuseStep 2501561 = 1876171) B1876171
theorem B3754937 : Blo 1387513 3754937 := bstep (se 2 (by rfl) ⟨1408101, by rfl⟩ : syracuseStep 3754937 = 2816203) B2816203
theorem B2083769 : Blo 1387513 2083769 := bstep (se 2 (by rfl) ⟨781413, by rfl⟩ : syracuseStep 2083769 = 1562827) B1562827
theorem B3124169 : Blo 1387513 3124169 := bstep (se 2 (by rfl) ⟨1171563, by rfl⟩ : syracuseStep 3124169 = 2343127) B2343127
theorem B1387527 : Blo 1387513 1387527 := bstep (se 1 (by rfl) ⟨1040645, by rfl⟩ : syracuseStep 1387527 = 2081291) B2081291
theorem B2083847 : Blo 1387513 2083847 := bstep (se 1 (by rfl) ⟨1562885, by rfl⟩ : syracuseStep 2083847 = 3125771) B3125771
theorem B1387535 : Blo 1387513 1387535 := bstep (se 1 (by rfl) ⟨1040651, by rfl⟩ : syracuseStep 1387535 = 2081303) B2081303
theorem B10546199 : Blo 1387513 10546199 := bstep (se 1 (by rfl) ⟨7909649, by rfl⟩ : syracuseStep 10546199 = 15819299) B15819299
theorem B3951659 : Blo 1387513 3951659 := bstep (se 1 (by rfl) ⟨2963744, by rfl⟩ : syracuseStep 3951659 = 5927489) B5927489
theorem B2083883 : Blo 1387513 2083883 := bstep (se 1 (by rfl) ⟨1562912, by rfl⟩ : syracuseStep 2083883 = 3125825) B3125825
theorem B1387579 : Blo 1387513 1387579 := bstep (se 1 (by rfl) ⟨1040684, by rfl⟩ : syracuseStep 1387579 = 2081369) B2081369
theorem B2083913 : Blo 1387513 2083913 := bstep (se 2 (by rfl) ⟨781467, by rfl⟩ : syracuseStep 2083913 = 1562935) B1562935
theorem B1387655 : Blo 1387513 1387655 := bstep (se 1 (by rfl) ⟨1040741, by rfl⟩ : syracuseStep 1387655 = 2081483) B2081483
theorem B1387663 : Blo 1387513 1387663 := bstep (se 1 (by rfl) ⟨1040747, by rfl⟩ : syracuseStep 1387663 = 2081495) B2081495
theorem B1387707 : Blo 1387513 1387707 := bstep (se 1 (by rfl) ⟨1040780, by rfl⟩ : syracuseStep 1387707 = 2081561) B2081561
theorem B2084027 : Blo 1387513 2084027 := bstep (se 1 (by rfl) ⟨1563020, by rfl⟩ : syracuseStep 2084027 = 3126041) B3126041
theorem B2084087 : Blo 1387513 2084087 := bstep (se 1 (by rfl) ⟨1563065, by rfl⟩ : syracuseStep 2084087 = 3126131) B3126131
theorem B1387783 : Blo 1387513 1387783 := bstep (se 1 (by rfl) ⟨1040837, by rfl⟩ : syracuseStep 1387783 = 2081675) B2081675
theorem B1387791 : Blo 1387513 1387791 := bstep (se 1 (by rfl) ⟨1040843, by rfl⟩ : syracuseStep 1387791 = 2081687) B2081687
theorem B2084111 : Blo 1387513 2084111 := bstep (se 1 (by rfl) ⟨1563083, by rfl⟩ : syracuseStep 2084111 = 3126167) B3126167
theorem B1387835 : Blo 1387513 1387835 := bstep (se 1 (by rfl) ⟨1040876, by rfl⟩ : syracuseStep 1387835 = 2081753) B2081753
theorem B2084153 : Blo 1387513 2084153 := bstep (se 2 (by rfl) ⟨781557, by rfl⟩ : syracuseStep 2084153 = 1563115) B1563115
theorem B1387911 : Blo 1387513 1387911 := bstep (se 1 (by rfl) ⟨1040933, by rfl⟩ : syracuseStep 1387911 = 2081867) B2081867
theorem B15822215 : Blo 1387513 15822215 := bstep (se 1 (by rfl) ⟨11866661, by rfl⟩ : syracuseStep 15822215 = 23733323) B23733323
theorem B2084231 : Blo 1387513 2084231 := bstep (se 1 (by rfl) ⟨1563173, by rfl⟩ : syracuseStep 2084231 = 3126347) B3126347
theorem B1387919 : Blo 1387513 1387919 := bstep (se 1 (by rfl) ⟨1040939, by rfl⟩ : syracuseStep 1387919 = 2081879) B2081879
theorem B1977743 : Blo 1387513 1977743 := bstep (se 1 (by rfl) ⟨1483307, by rfl⟩ : syracuseStep 1977743 = 2966615) B2966615
theorem B8891795 : Blo 1387513 8891795 := bstep (se 1 (by rfl) ⟨6668846, by rfl⟩ : syracuseStep 8891795 = 13337693) B13337693
theorem B6335891 : Blo 1387513 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B4689305 : Blo 1387513 4689305 := bstep (se 2 (by rfl) ⟨1758489, by rfl⟩ : syracuseStep 4689305 = 3516979) B3516979
theorem B2084267 : Blo 1387513 2084267 := bstep (se 1 (by rfl) ⟨1563200, by rfl⟩ : syracuseStep 2084267 = 3126401) B3126401
theorem B1387963 : Blo 1387513 1387963 := bstep (se 1 (by rfl) ⟨1040972, by rfl⟩ : syracuseStep 1387963 = 2081945) B2081945
theorem B1388039 : Blo 1387513 1388039 := bstep (se 1 (by rfl) ⟨1041029, by rfl⟩ : syracuseStep 1388039 = 2082059) B2082059
theorem B1388047 : Blo 1387513 1388047 := bstep (se 1 (by rfl) ⟨1041035, by rfl⟩ : syracuseStep 1388047 = 2082071) B2082071
theorem B1388091 : Blo 1387513 1388091 := bstep (se 1 (by rfl) ⟨1041068, by rfl⟩ : syracuseStep 1388091 = 2082137) B2082137
theorem B1388167 : Blo 1387513 1388167 := bstep (se 1 (by rfl) ⟨1041125, by rfl⟩ : syracuseStep 1388167 = 2082251) B2082251
theorem B3124871 : Blo 1387513 3124871 := bstep (se 1 (by rfl) ⟨2343653, by rfl⟩ : syracuseStep 3124871 = 4687307) B4687307
theorem B1388175 : Blo 1387513 1388175 := bstep (se 1 (by rfl) ⟨1041131, by rfl⟩ : syracuseStep 1388175 = 2082263) B2082263
theorem B1388219 : Blo 1387513 1388219 := bstep (se 1 (by rfl) ⟨1041164, by rfl⟩ : syracuseStep 1388219 = 2082329) B2082329
theorem B5271277 : Blo 1387513 5271277 := bstep (se 3 (by rfl) ⟨988364, by rfl⟩ : syracuseStep 5271277 = 1976729) B1976729
theorem B1388295 : Blo 1387513 1388295 := bstep (se 1 (by rfl) ⟨1041221, by rfl⟩ : syracuseStep 1388295 = 2082443) B2082443
theorem B1388303 : Blo 1387513 1388303 := bstep (se 1 (by rfl) ⟨1041227, by rfl⟩ : syracuseStep 1388303 = 2082455) B2082455
theorem B1388347 : Blo 1387513 1388347 := bstep (se 1 (by rfl) ⟨1041260, by rfl⟩ : syracuseStep 1388347 = 2082521) B2082521
theorem B3125051 : Blo 1387513 3125051 := bstep (se 1 (by rfl) ⟨2343788, by rfl⟩ : syracuseStep 3125051 = 4687577) B4687577
theorem B1757047 : Blo 1387513 1757047 := bstep (se 1 (by rfl) ⟨1317785, by rfl⟩ : syracuseStep 1757047 = 2635571) B2635571
theorem B1388423 : Blo 1387513 1388423 := bstep (se 1 (by rfl) ⟨1041317, by rfl⟩ : syracuseStep 1388423 = 2082635) B2082635
theorem B1388431 : Blo 1387513 1388431 := bstep (se 1 (by rfl) ⟨1041323, by rfl⟩ : syracuseStep 1388431 = 2082647) B2082647
theorem B16895897 : Blo 1387513 16895897 := bstep (se 2 (by rfl) ⟨6335961, by rfl⟩ : syracuseStep 16895897 = 12671923) B12671923
theorem B3125177 : Blo 1387513 3125177 := bstep (se 2 (by rfl) ⟨1171941, by rfl⟩ : syracuseStep 3125177 = 2343883) B2343883
theorem B1388475 : Blo 1387513 1388475 := bstep (se 1 (by rfl) ⟨1041356, by rfl⟩ : syracuseStep 1388475 = 2082713) B2082713
theorem B7024643 : Blo 1387513 7024643 := bstep (se 1 (by rfl) ⟨5268482, by rfl⟩ : syracuseStep 7024643 = 10536965) B10536965
theorem B1388551 : Blo 1387513 1388551 := bstep (se 1 (by rfl) ⟨1041413, by rfl⟩ : syracuseStep 1388551 = 2082827) B2082827
theorem B1388559 : Blo 1387513 1388559 := bstep (se 1 (by rfl) ⟨1041419, by rfl⟩ : syracuseStep 1388559 = 2082839) B2082839
theorem B5271581 : Blo 1387513 5271581 := bstep (se 3 (by rfl) ⟨988421, by rfl⟩ : syracuseStep 5271581 = 1976843) B1976843
theorem B1388603 : Blo 1387513 1388603 := bstep (se 1 (by rfl) ⟨1041452, by rfl⟩ : syracuseStep 1388603 = 2082905) B2082905
theorem B5001277 : Blo 1387513 5001277 := bstep (se 3 (by rfl) ⟨937739, by rfl⟩ : syracuseStep 5001277 = 1875479) B1875479
theorem B3952775 : Blo 1387513 3952775 := bstep (se 1 (by rfl) ⟨2964581, by rfl⟩ : syracuseStep 3952775 = 5929163) B5929163
theorem B1388679 : Blo 1387513 1388679 := bstep (se 1 (by rfl) ⟨1041509, by rfl⟩ : syracuseStep 1388679 = 2083019) B2083019
theorem B1388687 : Blo 1387513 1388687 := bstep (se 1 (by rfl) ⟨1041515, by rfl⟩ : syracuseStep 1388687 = 2083031) B2083031
theorem B22532269 : Blo 1387513 22532269 := bstep (se 3 (by rfl) ⟨4224800, by rfl⟩ : syracuseStep 22532269 = 8449601) B8449601
theorem B1757371 : Blo 1387513 1757371 := bstep (se 1 (by rfl) ⟨1318028, by rfl⟩ : syracuseStep 1757371 = 2636057) B2636057
theorem B1388731 : Blo 1387513 1388731 := bstep (se 1 (by rfl) ⟨1041548, by rfl⟩ : syracuseStep 1388731 = 2083097) B2083097
theorem B1388807 : Blo 1387513 1388807 := bstep (se 1 (by rfl) ⟨1041605, by rfl⟩ : syracuseStep 1388807 = 2083211) B2083211
theorem B1388815 : Blo 1387513 1388815 := bstep (se 1 (by rfl) ⟨1041611, by rfl⟩ : syracuseStep 1388815 = 2083223) B2083223
theorem B3125519 : Blo 1387513 3125519 := bstep (se 1 (by rfl) ⟨2344139, by rfl⟩ : syracuseStep 3125519 = 4688279) B4688279
theorem B3125537 : Blo 1387513 3125537 := bstep (se 2 (by rfl) ⟨1172076, by rfl⟩ : syracuseStep 3125537 = 2344153) B2344153
theorem B1388859 : Blo 1387513 1388859 := bstep (se 1 (by rfl) ⟨1041644, by rfl⟩ : syracuseStep 1388859 = 2083289) B2083289
theorem B3952957 : Blo 1387513 3952957 := bstep (se 3 (by rfl) ⟨741179, by rfl⟩ : syracuseStep 3952957 = 1482359) B1482359
theorem B1388935 : Blo 1387513 1388935 := bstep (se 1 (by rfl) ⟨1041701, by rfl⟩ : syracuseStep 1388935 = 2083403) B2083403
theorem B8900999 : Blo 1387513 8900999 := bstep (se 1 (by rfl) ⟨6675749, by rfl⟩ : syracuseStep 8900999 = 13351499) B13351499
theorem B1388943 : Blo 1387513 1388943 := bstep (se 1 (by rfl) ⟨1041707, by rfl⟩ : syracuseStep 1388943 = 2083415) B2083415
theorem B5140883 : Blo 1387513 5140883 := bstep (se 1 (by rfl) ⟨3855662, by rfl⟩ : syracuseStep 5140883 = 7711325) B7711325
theorem B1388987 : Blo 1387513 1388987 := bstep (se 1 (by rfl) ⟨1041740, by rfl⟩ : syracuseStep 1388987 = 2083481) B2083481
theorem B16028113 : Blo 1387513 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B1389063 : Blo 1387513 1389063 := bstep (se 1 (by rfl) ⟨1041797, by rfl⟩ : syracuseStep 1389063 = 2083595) B2083595
theorem B1389071 : Blo 1387513 1389071 := bstep (se 1 (by rfl) ⟨1041803, by rfl⟩ : syracuseStep 1389071 = 2083607) B2083607
theorem B2503183 : Blo 1387513 2503183 := bstep (se 1 (by rfl) ⟨1877387, by rfl⟩ : syracuseStep 2503183 = 3754775) B3754775
theorem B1389115 : Blo 1387513 1389115 := bstep (se 1 (by rfl) ⟨1041836, by rfl⟩ : syracuseStep 1389115 = 2083673) B2083673
theorem B3125879 : Blo 1387513 3125879 := bstep (se 1 (by rfl) ⟨2344409, by rfl⟩ : syracuseStep 3125879 = 4688819) B4688819
theorem B1389191 : Blo 1387513 1389191 := bstep (se 1 (by rfl) ⟨1041893, by rfl⟩ : syracuseStep 1389191 = 2083787) B2083787
theorem B1389199 : Blo 1387513 1389199 := bstep (se 1 (by rfl) ⟨1041899, by rfl⟩ : syracuseStep 1389199 = 2083799) B2083799
theorem B3953299 : Blo 1387513 3953299 := bstep (se 1 (by rfl) ⟨2964974, by rfl⟩ : syracuseStep 3953299 = 5929949) B5929949
theorem B1389243 : Blo 1387513 1389243 := bstep (se 1 (by rfl) ⟨1041932, by rfl⟩ : syracuseStep 1389243 = 2083865) B2083865
theorem B1561351 : Blo 1387513 1561351 := bstep (se 1 (by rfl) ⟨1171013, by rfl⟩ : syracuseStep 1561351 = 2342027) B2342027
theorem B1389319 : Blo 1387513 1389319 := bstep (se 1 (by rfl) ⟨1041989, by rfl⟩ : syracuseStep 1389319 = 2083979) B2083979
theorem B1389327 : Blo 1387513 1389327 := bstep (se 1 (by rfl) ⟨1041995, by rfl⟩ : syracuseStep 1389327 = 2083991) B2083991
theorem B3126059 : Blo 1387513 3126059 := bstep (se 1 (by rfl) ⟨2344544, by rfl⟩ : syracuseStep 3126059 = 4689089) B4689089
theorem B1389371 : Blo 1387513 1389371 := bstep (se 1 (by rfl) ⟨1042028, by rfl⟩ : syracuseStep 1389371 = 2084057) B2084057
theorem B7033715 : Blo 1387513 7033715 := bstep (se 1 (by rfl) ⟨5275286, by rfl⟩ : syracuseStep 7033715 = 10550573) B10550573
theorem B2503543 : Blo 1387513 2503543 := bstep (se 1 (by rfl) ⟨1877657, by rfl⟩ : syracuseStep 2503543 = 3755315) B3755315
theorem B1389447 : Blo 1387513 1389447 := bstep (se 1 (by rfl) ⟨1042085, by rfl⟩ : syracuseStep 1389447 = 2084171) B2084171
theorem B1389455 : Blo 1387513 1389455 := bstep (se 1 (by rfl) ⟨1042091, by rfl⟩ : syracuseStep 1389455 = 2084183) B2084183
theorem B2003897 : Blo 1387513 2003897 := bstep (se 2 (by rfl) ⟨751461, by rfl⟩ : syracuseStep 2003897 = 1502923) B1502923
theorem B1561531 : Blo 1387513 1561531 := bstep (se 1 (by rfl) ⟨1171148, by rfl⟩ : syracuseStep 1561531 = 2342297) B2342297
theorem B1389499 : Blo 1387513 1389499 := bstep (se 1 (by rfl) ⟨1042124, by rfl⟩ : syracuseStep 1389499 = 2084249) B2084249
theorem B2634697 : Blo 1387513 2634697 := bstep (se 2 (by rfl) ⟨988011, by rfl⟩ : syracuseStep 2634697 = 1976023) B1976023
theorem B25334789 : Blo 1387513 25334789 := bstep (se 4 (by rfl) ⟨2375136, by rfl⟩ : syracuseStep 25334789 = 4750273) B4750273
theorem B5002327 : Blo 1387513 5002327 := bstep (se 1 (by rfl) ⟨3751745, by rfl⟩ : syracuseStep 5002327 = 7503491) B7503491
theorem B60036227 : Blo 1387513 60036227 := bstep (se 1 (by rfl) ⟨45027170, by rfl⟩ : syracuseStep 60036227 = 90054341) B90054341
theorem B1758343 : Blo 1387513 1758343 := bstep (se 1 (by rfl) ⟨1318757, by rfl⟩ : syracuseStep 1758343 = 2637515) B2637515
theorem B5928137 : Blo 1387513 5928137 := bstep (se 2 (by rfl) ⟨2223051, by rfl⟩ : syracuseStep 5928137 = 4446103) B4446103
theorem B5928173 : Blo 1387513 5928173 := bstep (se 3 (by rfl) ⟨1111532, by rfl⟩ : syracuseStep 5928173 = 2223065) B2223065
theorem B4683041 : Blo 1387513 4683041 := bstep (se 2 (by rfl) ⟨1756140, by rfl⟩ : syracuseStep 4683041 = 3512281) B3512281
theorem B7034201 : Blo 1387513 7034201 := bstep (se 2 (by rfl) ⟨2637825, by rfl⟩ : syracuseStep 7034201 = 5275651) B5275651
theorem B1561999 : Blo 1387513 1561999 := bstep (se 1 (by rfl) ⟨1171499, by rfl⟩ : syracuseStep 1561999 = 2342999) B2342999
theorem B54072755 : Blo 1387513 54072755 := bstep (se 1 (by rfl) ⟨40554566, by rfl⟩ : syracuseStep 54072755 = 81109133) B81109133
theorem B13342157 : Blo 1387513 13342157 := bstep (se 3 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 13342157 = 5003309) B5003309
theorem B5346769 : Blo 1387513 5346769 := bstep (se 2 (by rfl) ⟨2005038, by rfl⟩ : syracuseStep 5346769 = 4010077) B4010077
theorem B3954187 : Blo 1387513 3954187 := bstep (se 1 (by rfl) ⟨2965640, by rfl⟩ : syracuseStep 3954187 = 5931281) B5931281
theorem B15005213 : Blo 1387513 15005213 := bstep (se 3 (by rfl) ⟨2813477, by rfl⟩ : syracuseStep 15005213 = 5626955) B5626955
theorem B7026263 : Blo 1387513 7026263 := bstep (se 1 (by rfl) ⟨5269697, by rfl⟩ : syracuseStep 7026263 = 10539395) B10539395
theorem B5273207 : Blo 1387513 5273207 := bstep (se 1 (by rfl) ⟨3954905, by rfl⟩ : syracuseStep 5273207 = 7909811) B7909811
theorem B2635411 : Blo 1387513 2635411 := bstep (se 1 (by rfl) ⟨1976558, by rfl⟩ : syracuseStep 2635411 = 3953117) B3953117
theorem B42759859 : Blo 1387513 42759859 := bstep (se 1 (by rfl) ⟨32069894, by rfl⟩ : syracuseStep 42759859 = 64139789) B64139789
theorem B4683635 : Blo 1387513 4683635 := bstep (se 1 (by rfl) ⟨3512726, by rfl⟩ : syracuseStep 4683635 = 7025453) B7025453
theorem B1562503 : Blo 1387513 1562503 := bstep (se 1 (by rfl) ⟨1171877, by rfl⟩ : syracuseStep 1562503 = 2343755) B2343755
theorem B5928889 : Blo 1387513 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B3954689 : Blo 1387513 3954689 := bstep (se 2 (by rfl) ⟨1483008, by rfl⟩ : syracuseStep 3954689 = 2966017) B2966017
theorem B1562683 : Blo 1387513 1562683 := bstep (se 1 (by rfl) ⟨1172012, by rfl⟩ : syracuseStep 1562683 = 2344025) B2344025
theorem B7026749 : Blo 1387513 7026749 := bstep (se 3 (by rfl) ⟨1317515, by rfl⟩ : syracuseStep 7026749 = 2635031) B2635031
theorem B3955031 : Blo 1387513 3955031 := bstep (se 1 (by rfl) ⟨2966273, by rfl⟩ : syracuseStep 3955031 = 5932547) B5932547
theorem B5626259 : Blo 1387513 5626259 := bstep (se 1 (by rfl) ⟨4219694, by rfl⟩ : syracuseStep 5626259 = 8439389) B8439389
theorem B2111915 : Blo 1387513 2111915 := bstep (se 1 (by rfl) ⟨1583936, by rfl⟩ : syracuseStep 2111915 = 3167873) B3167873
theorem B13720013 : Blo 1387513 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B1563151 : Blo 1387513 1563151 := bstep (se 1 (by rfl) ⟨1172363, by rfl⟩ : syracuseStep 1563151 = 2344727) B2344727
theorem B5274179 : Blo 1387513 5274179 := bstep (se 1 (by rfl) ⟨3955634, by rfl⟩ : syracuseStep 5274179 = 7911269) B7911269
theorem B33782453 : Blo 1387513 33782453 := bstep (se 5 (by rfl) ⟨1583552, by rfl⟩ : syracuseStep 33782453 = 3167105) B3167105
theorem B2341561 : Blo 1387513 2341561 := bstep (se 2 (by rfl) ⟨878085, by rfl⟩ : syracuseStep 2341561 = 1756171) B1756171
theorem B2636489 : Blo 1387513 2636489 := bstep (se 2 (by rfl) ⟨988683, by rfl⟩ : syracuseStep 2636489 = 1977367) B1977367
theorem B13703897 : Blo 1387513 13703897 := bstep (se 2 (by rfl) ⟨5138961, by rfl⟩ : syracuseStep 13703897 = 10277923) B10277923
theorem B10541825 : Blo 1387513 10541825 := bstep (se 2 (by rfl) ⟨3953184, by rfl⟩ : syracuseStep 10541825 = 7906369) B7906369
theorem B3169039 : Blo 1387513 3169039 := bstep (se 1 (by rfl) ⟨2376779, by rfl⟩ : syracuseStep 3169039 = 4753559) B4753559
theorem B2030393 : Blo 1387513 2030393 := bstep (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) B1522795
theorem B3513203 : Blo 1387513 3513203 := bstep (se 1 (by rfl) ⟨2634902, by rfl⟩ : syracuseStep 3513203 = 5269805) B5269805
theorem B11869091 : Blo 1387513 11869091 := bstep (se 1 (by rfl) ⟨8901818, by rfl⟩ : syracuseStep 11869091 = 17803637) B17803637
theorem B2374699 : Blo 1387513 2374699 := bstep (se 1 (by rfl) ⟨1781024, by rfl⟩ : syracuseStep 2374699 = 3562049) B3562049
theorem B2964539 : Blo 1387513 2964539 := bstep (se 1 (by rfl) ⟨2223404, by rfl⟩ : syracuseStep 2964539 = 4446809) B4446809
theorem B5340227 : Blo 1387513 5340227 := bstep (se 1 (by rfl) ⟨4005170, by rfl⟩ : syracuseStep 5340227 = 8010341) B8010341
theorem B1481915 : Blo 1387513 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B2342263 : Blo 1387513 2342263 := bstep (se 1 (by rfl) ⟨1756697, by rfl⟩ : syracuseStep 2342263 = 3513395) B3513395
theorem B3513719 : Blo 1387513 3513719 := bstep (se 1 (by rfl) ⟨2635289, by rfl⟩ : syracuseStep 3513719 = 5270579) B5270579
theorem B7511449 : Blo 1387513 7511449 := bstep (se 2 (by rfl) ⟨2816793, by rfl⟩ : syracuseStep 7511449 = 5633587) B5633587
theorem B5275165 : Blo 1387513 5275165 := bstep (se 3 (by rfl) ⟨989093, by rfl⟩ : syracuseStep 5275165 = 1978187) B1978187
theorem B2637355 : Blo 1387513 2637355 := bstep (se 1 (by rfl) ⟨1978016, by rfl⟩ : syracuseStep 2637355 = 3956033) B3956033
theorem B11869739 : Blo 1387513 11869739 := bstep (se 1 (by rfl) ⟨8902304, by rfl⟩ : syracuseStep 11869739 = 17804609) B17804609
theorem B2342459 : Blo 1387513 2342459 := bstep (se 1 (by rfl) ⟨1756844, by rfl⟩ : syracuseStep 2342459 = 3513689) B3513689
theorem B2637431 : Blo 1387513 2637431 := bstep (se 1 (by rfl) ⟨1978073, by rfl⟩ : syracuseStep 2637431 = 3956147) B3956147
theorem B17342257 : Blo 1387513 17342257 := bstep (se 2 (by rfl) ⟨6503346, by rfl⟩ : syracuseStep 17342257 = 13006693) B13006693
theorem B7028531 : Blo 1387513 7028531 := bstep (se 1 (by rfl) ⟨5271398, by rfl⟩ : syracuseStep 7028531 = 10542797) B10542797
theorem B2965367 : Blo 1387513 2965367 := bstep (se 1 (by rfl) ⟨2224025, by rfl⟩ : syracuseStep 2965367 = 4448051) B4448051
theorem B4448153 : Blo 1387513 4448153 := bstep (se 2 (by rfl) ⟨1668057, by rfl⟩ : syracuseStep 4448153 = 3336115) B3336115
theorem B2342857 : Blo 1387513 2342857 := bstep (se 2 (by rfl) ⟨878571, by rfl⟩ : syracuseStep 2342857 = 1757143) B1757143
theorem B11255755 : Blo 1387513 11255755 := bstep (se 1 (by rfl) ⟨8441816, by rfl⟩ : syracuseStep 11255755 = 16883633) B16883633
theorem B67559437 : Blo 1387513 67559437 := bstep (se 3 (by rfl) ⟨12667394, by rfl⟩ : syracuseStep 67559437 = 25334789) B25334789
theorem B3514387 : Blo 1387513 3514387 := bstep (se 1 (by rfl) ⟨2635790, by rfl⟩ : syracuseStep 3514387 = 5271581) B5271581
theorem B45047825 : Blo 1387513 45047825 := bstep (se 2 (by rfl) ⟨16892934, by rfl⟩ : syracuseStep 45047825 = 33785869) B33785869
theorem B4685903 : Blo 1387513 4685903 := bstep (se 1 (by rfl) ⟨3514427, by rfl⟩ : syracuseStep 4685903 = 7028855) B7028855
theorem B6668369 : Blo 1387513 6668369 := bstep (se 2 (by rfl) ⟨2500638, by rfl⟩ : syracuseStep 6668369 = 5001277) B5001277
theorem B7905437 : Blo 1387513 7905437 := bstep (se 3 (by rfl) ⟨1482269, by rfl⟩ : syracuseStep 7905437 = 2964539) B2964539
theorem B2965675 : Blo 1387513 2965675 := bstep (se 1 (by rfl) ⟨2224256, by rfl⟩ : syracuseStep 2965675 = 4448513) B4448513
theorem B2343161 : Blo 1387513 2343161 := bstep (se 2 (by rfl) ⟨878685, by rfl⟩ : syracuseStep 2343161 = 1757371) B1757371
theorem B2343343 : Blo 1387513 2343343 := bstep (se 1 (by rfl) ⟨1757507, by rfl⟩ : syracuseStep 2343343 = 3515015) B3515015
theorem B4686281 : Blo 1387513 4686281 := bstep (se 2 (by rfl) ⟨1757355, by rfl⟩ : syracuseStep 4686281 = 3514711) B3514711
theorem B2343431 : Blo 1387513 2343431 := bstep (se 1 (by rfl) ⟨1757573, by rfl⟩ : syracuseStep 2343431 = 3515147) B3515147
theorem B6767239 : Blo 1387513 6767239 := bstep (se 1 (by rfl) ⟨5075429, by rfl⟩ : syracuseStep 6767239 = 10150859) B10150859
theorem B4686551 : Blo 1387513 4686551 := bstep (se 1 (by rfl) ⟨3514913, by rfl⟩ : syracuseStep 4686551 = 7029827) B7029827
theorem B8897309 : Blo 1387513 8897309 := bstep (se 3 (by rfl) ⟨1668245, by rfl⟩ : syracuseStep 8897309 = 3336491) B3336491
theorem B2343775 : Blo 1387513 2343775 := bstep (se 1 (by rfl) ⟨1757831, by rfl⟩ : syracuseStep 2343775 = 3515663) B3515663
theorem B3122027 : Blo 1387513 3122027 := bstep (se 1 (by rfl) ⟨2341520, by rfl⟩ : syracuseStep 3122027 = 4683041) B4683041
theorem B3122081 : Blo 1387513 3122081 := bstep (se 2 (by rfl) ⟨1170780, by rfl⟩ : syracuseStep 3122081 = 2341561) B2341561
theorem B2081711 : Blo 1387513 2081711 := bstep (se 1 (by rfl) ⟨1561283, by rfl⟩ : syracuseStep 2081711 = 3122567) B3122567
theorem B4686767 : Blo 1387513 4686767 := bstep (se 1 (by rfl) ⟨3515075, by rfl⟩ : syracuseStep 4686767 = 7030151) B7030151
theorem B6013871 : Blo 1387513 6013871 := bstep (se 1 (by rfl) ⟨4510403, by rfl⟩ : syracuseStep 6013871 = 9020807) B9020807
theorem B2343863 : Blo 1387513 2343863 := bstep (se 1 (by rfl) ⟨1757897, by rfl⟩ : syracuseStep 2343863 = 3515795) B3515795
theorem B2081801 : Blo 1387513 2081801 := bstep (se 2 (by rfl) ⟨780675, by rfl⟩ : syracuseStep 2081801 = 1561351) B1561351
theorem B10003475 : Blo 1387513 10003475 := bstep (se 1 (by rfl) ⟨7502606, by rfl⟩ : syracuseStep 10003475 = 15005213) B15005213
theorem B2081831 : Blo 1387513 2081831 := bstep (se 1 (by rfl) ⟨1561373, by rfl⟩ : syracuseStep 2081831 = 3122747) B3122747
theorem B3515471 : Blo 1387513 3515471 := bstep (se 1 (by rfl) ⟨2636603, by rfl⟩ : syracuseStep 3515471 = 5273207) B5273207
theorem B2081915 : Blo 1387513 2081915 := bstep (se 1 (by rfl) ⟨1561436, by rfl⟩ : syracuseStep 2081915 = 3122873) B3122873
theorem B3122423 : Blo 1387513 3122423 := bstep (se 1 (by rfl) ⟨2341817, by rfl⟩ : syracuseStep 3122423 = 4683635) B4683635
theorem B2082041 : Blo 1387513 2082041 := bstep (se 2 (by rfl) ⟨780765, by rfl⟩ : syracuseStep 2082041 = 1561531) B1561531
theorem B5211479 : Blo 1387513 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B2082143 : Blo 1387513 2082143 := bstep (se 1 (by rfl) ⟨1561607, by rfl⟩ : syracuseStep 2082143 = 3123215) B3123215
theorem B2082155 : Blo 1387513 2082155 := bstep (se 1 (by rfl) ⟨1561616, by rfl⟩ : syracuseStep 2082155 = 3123233) B3123233
theorem B2344457 : Blo 1387513 2344457 := bstep (se 2 (by rfl) ⟨879171, by rfl⟩ : syracuseStep 2344457 = 1758343) B1758343
theorem B2082383 : Blo 1387513 2082383 := bstep (se 1 (by rfl) ⟨1561787, by rfl⟩ : syracuseStep 2082383 = 3123575) B3123575
theorem B2344619 : Blo 1387513 2344619 := bstep (se 1 (by rfl) ⟨1758464, by rfl⟩ : syracuseStep 2344619 = 3516929) B3516929
theorem B2082503 : Blo 1387513 2082503 := bstep (se 1 (by rfl) ⟨1561877, by rfl⟩ : syracuseStep 2082503 = 3123755) B3123755
theorem B3516119 : Blo 1387513 3516119 := bstep (se 1 (by rfl) ⟨2637089, by rfl⟩ : syracuseStep 3516119 = 5274179) B5274179
theorem B22521635 : Blo 1387513 22521635 := bstep (se 1 (by rfl) ⟨16891226, by rfl⟩ : syracuseStep 22521635 = 33782453) B33782453
theorem B9135931 : Blo 1387513 9135931 := bstep (se 1 (by rfl) ⟨6851948, by rfl⟩ : syracuseStep 9135931 = 13703897) B13703897
theorem B16893755 : Blo 1387513 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B11405123 : Blo 1387513 11405123 := bstep (se 1 (by rfl) ⟨8553842, by rfl⟩ : syracuseStep 11405123 = 17107685) B17107685
theorem B3123017 : Blo 1387513 3123017 := bstep (se 2 (by rfl) ⟨1171131, by rfl⟩ : syracuseStep 3123017 = 2342263) B2342263
theorem B3753823 : Blo 1387513 3753823 := bstep (se 1 (by rfl) ⟨2815367, by rfl⟩ : syracuseStep 3753823 = 5630735) B5630735
theorem B2082665 : Blo 1387513 2082665 := bstep (se 2 (by rfl) ⟨780999, by rfl⟩ : syracuseStep 2082665 = 1561999) B1561999
theorem B7030637 : Blo 1387513 7030637 := bstep (se 3 (by rfl) ⟨1318244, by rfl⟩ : syracuseStep 7030637 = 2636489) B2636489
theorem B2082743 : Blo 1387513 2082743 := bstep (se 1 (by rfl) ⟨1562057, by rfl⟩ : syracuseStep 2082743 = 3124115) B3124115
theorem B7129025 : Blo 1387513 7129025 := bstep (se 2 (by rfl) ⟨2673384, by rfl⟩ : syracuseStep 7129025 = 5346769) B5346769
theorem B2082779 : Blo 1387513 2082779 := bstep (se 1 (by rfl) ⟨1562084, by rfl⟩ : syracuseStep 2082779 = 3124169) B3124169
theorem B7030799 : Blo 1387513 7030799 := bstep (se 1 (by rfl) ⟨5273099, by rfl⟩ : syracuseStep 7030799 = 10546199) B10546199
theorem B3516473 : Blo 1387513 3516473 := bstep (se 2 (by rfl) ⟨1318677, by rfl⟩ : syracuseStep 3516473 = 2637355) B2637355
theorem B7907645 : Blo 1387513 7907645 := bstep (se 3 (by rfl) ⟨1482683, by rfl⟩ : syracuseStep 7907645 = 2965367) B2965367
theorem B2083247 : Blo 1387513 2083247 := bstep (se 1 (by rfl) ⟨1562435, by rfl⟩ : syracuseStep 2083247 = 3124871) B3124871
theorem B6670829 : Blo 1387513 6670829 := bstep (se 3 (by rfl) ⟨1250780, by rfl⟩ : syracuseStep 6670829 = 2501561) B2501561
theorem B5343725 : Blo 1387513 5343725 := bstep (se 3 (by rfl) ⟨1001948, by rfl⟩ : syracuseStep 5343725 = 2003897) B2003897
theorem B10013165 : Blo 1387513 10013165 := bstep (se 3 (by rfl) ⟨1877468, by rfl⟩ : syracuseStep 10013165 = 3754937) B3754937
theorem B2083337 : Blo 1387513 2083337 := bstep (se 2 (by rfl) ⟨781251, by rfl⟩ : syracuseStep 2083337 = 1562503) B1562503
theorem B2083367 : Blo 1387513 2083367 := bstep (se 1 (by rfl) ⟨1562525, by rfl⟩ : syracuseStep 2083367 = 3125051) B3125051
theorem B3123809 : Blo 1387513 3123809 := bstep (se 2 (by rfl) ⟨1171428, by rfl⟩ : syracuseStep 3123809 = 2342857) B2342857
theorem B2083451 : Blo 1387513 2083451 := bstep (se 1 (by rfl) ⟨1562588, by rfl⟩ : syracuseStep 2083451 = 3125177) B3125177
theorem B2083577 : Blo 1387513 2083577 := bstep (se 2 (by rfl) ⟨781341, by rfl⟩ : syracuseStep 2083577 = 1562683) B1562683
theorem B14240605 : Blo 1387513 14240605 := bstep (se 3 (by rfl) ⟨2670113, by rfl⟩ : syracuseStep 14240605 = 5340227) B5340227
theorem B1502047 : Blo 1387513 1502047 := bstep (se 1 (by rfl) ⟨1126535, by rfl⟩ : syracuseStep 1502047 = 2253071) B2253071
theorem B2083679 : Blo 1387513 2083679 := bstep (se 1 (by rfl) ⟨1562759, by rfl⟩ : syracuseStep 2083679 = 3125519) B3125519
theorem B2083691 : Blo 1387513 2083691 := bstep (se 1 (by rfl) ⟨1562768, by rfl⟩ : syracuseStep 2083691 = 3125537) B3125537
theorem B30043025 : Blo 1387513 30043025 := bstep (se 2 (by rfl) ⟨11266134, by rfl⟩ : syracuseStep 30043025 = 22532269) B22532269
theorem B5933999 : Blo 1387513 5933999 := bstep (se 1 (by rfl) ⟨4450499, by rfl⟩ : syracuseStep 5933999 = 8900999) B8900999
theorem B3427255 : Blo 1387513 3427255 := bstep (se 1 (by rfl) ⟨2570441, by rfl⟩ : syracuseStep 3427255 = 5140883) B5140883
theorem B3124151 : Blo 1387513 3124151 := bstep (se 1 (by rfl) ⟨2343113, by rfl⟩ : syracuseStep 3124151 = 4686227) B4686227
theorem B7908353 : Blo 1387513 7908353 := bstep (se 2 (by rfl) ⟨2965632, by rfl⟩ : syracuseStep 7908353 = 5931265) B5931265
theorem B9022465 : Blo 1387513 9022465 := bstep (se 2 (by rfl) ⟨3383424, by rfl⟩ : syracuseStep 9022465 = 6766849) B6766849
theorem B1387559 : Blo 1387513 1387559 := bstep (se 1 (by rfl) ⟨1040669, by rfl⟩ : syracuseStep 1387559 = 2081339) B2081339
theorem B1387599 : Blo 1387513 1387599 := bstep (se 1 (by rfl) ⟨1040699, by rfl⟩ : syracuseStep 1387599 = 2081399) B2081399
theorem B2083919 : Blo 1387513 2083919 := bstep (se 1 (by rfl) ⟨1562939, by rfl⟩ : syracuseStep 2083919 = 3125879) B3125879
theorem B5270609 : Blo 1387513 5270609 := bstep (se 2 (by rfl) ⟨1976478, by rfl⟩ : syracuseStep 5270609 = 3952957) B3952957
theorem B1387615 : Blo 1387513 1387615 := bstep (se 1 (by rfl) ⟨1040711, by rfl⟩ : syracuseStep 1387615 = 2081423) B2081423
theorem B1387643 : Blo 1387513 1387643 := bstep (se 1 (by rfl) ⟨1040732, by rfl⟩ : syracuseStep 1387643 = 2081465) B2081465
theorem B3951773 : Blo 1387513 3951773 := bstep (se 3 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 3951773 = 1481915) B1481915
theorem B1387695 : Blo 1387513 1387695 := bstep (se 1 (by rfl) ⟨1040771, by rfl⟩ : syracuseStep 1387695 = 2081543) B2081543
theorem B1387719 : Blo 1387513 1387719 := bstep (se 1 (by rfl) ⟨1040789, by rfl⟩ : syracuseStep 1387719 = 2081579) B2081579
theorem B2084039 : Blo 1387513 2084039 := bstep (se 1 (by rfl) ⟨1563029, by rfl⟩ : syracuseStep 2084039 = 3126059) B3126059
theorem B1387739 : Blo 1387513 1387739 := bstep (se 1 (by rfl) ⟨1040804, by rfl⟩ : syracuseStep 1387739 = 2081609) B2081609
theorem B4689143 : Blo 1387513 4689143 := bstep (se 1 (by rfl) ⟨3516857, by rfl⟩ : syracuseStep 4689143 = 7033715) B7033715
theorem B1387815 : Blo 1387513 1387815 := bstep (se 1 (by rfl) ⟨1040861, by rfl⟩ : syracuseStep 1387815 = 2081723) B2081723
theorem B1387855 : Blo 1387513 1387855 := bstep (se 1 (by rfl) ⟨1040891, by rfl⟩ : syracuseStep 1387855 = 2081783) B2081783
theorem B1387871 : Blo 1387513 1387871 := bstep (se 1 (by rfl) ⟨1040903, by rfl⟩ : syracuseStep 1387871 = 2081807) B2081807
theorem B3337577 : Blo 1387513 3337577 := bstep (se 2 (by rfl) ⟨1251591, by rfl⟩ : syracuseStep 3337577 = 2503183) B2503183
theorem B2084201 : Blo 1387513 2084201 := bstep (se 2 (by rfl) ⟨781575, by rfl⟩ : syracuseStep 2084201 = 1563151) B1563151
theorem B1387899 : Blo 1387513 1387899 := bstep (se 1 (by rfl) ⟨1040924, by rfl⟩ : syracuseStep 1387899 = 2081849) B2081849
theorem B3337615 : Blo 1387513 3337615 := bstep (se 1 (by rfl) ⟨2503211, by rfl⟩ : syracuseStep 3337615 = 5006423) B5006423
theorem B1387951 : Blo 1387513 1387951 := bstep (se 1 (by rfl) ⟨1040963, by rfl⟩ : syracuseStep 1387951 = 2081927) B2081927
theorem B1387975 : Blo 1387513 1387975 := bstep (se 1 (by rfl) ⟨1040981, by rfl⟩ : syracuseStep 1387975 = 2081963) B2081963
theorem B3952091 : Blo 1387513 3952091 := bstep (se 1 (by rfl) ⟨2964068, by rfl⟩ : syracuseStep 3952091 = 5928137) B5928137
theorem B1387995 : Blo 1387513 1387995 := bstep (se 1 (by rfl) ⟨1040996, by rfl⟩ : syracuseStep 1387995 = 2081993) B2081993
theorem B3952115 : Blo 1387513 3952115 := bstep (se 1 (by rfl) ⟨2964086, by rfl⟩ : syracuseStep 3952115 = 5928173) B5928173
theorem B3124745 : Blo 1387513 3124745 := bstep (se 2 (by rfl) ⟨1171779, by rfl⟩ : syracuseStep 3124745 = 2343559) B2343559
theorem B5271065 : Blo 1387513 5271065 := bstep (se 2 (by rfl) ⟨1976649, by rfl⟩ : syracuseStep 5271065 = 3953299) B3953299
theorem B1388071 : Blo 1387513 1388071 := bstep (se 1 (by rfl) ⟨1041053, by rfl⟩ : syracuseStep 1388071 = 2082107) B2082107
theorem B4689467 : Blo 1387513 4689467 := bstep (se 1 (by rfl) ⟨3517100, by rfl⟩ : syracuseStep 4689467 = 7034201) B7034201
theorem B1388111 : Blo 1387513 1388111 := bstep (se 1 (by rfl) ⟨1041083, by rfl⟩ : syracuseStep 1388111 = 2082167) B2082167
theorem B1388127 : Blo 1387513 1388127 := bstep (se 1 (by rfl) ⟨1041095, by rfl⟩ : syracuseStep 1388127 = 2082191) B2082191
theorem B36048503 : Blo 1387513 36048503 := bstep (se 1 (by rfl) ⟨27036377, by rfl⟩ : syracuseStep 36048503 = 54072755) B54072755
theorem B1388155 : Blo 1387513 1388155 := bstep (se 1 (by rfl) ⟨1041116, by rfl⟩ : syracuseStep 1388155 = 2082233) B2082233
theorem B1388207 : Blo 1387513 1388207 := bstep (se 1 (by rfl) ⟨1041155, by rfl⟩ : syracuseStep 1388207 = 2082311) B2082311
theorem B1388231 : Blo 1387513 1388231 := bstep (se 1 (by rfl) ⟨1041173, by rfl⟩ : syracuseStep 1388231 = 2082347) B2082347
theorem B32059097 : Blo 1387513 32059097 := bstep (se 2 (by rfl) ⟨12022161, by rfl⟩ : syracuseStep 32059097 = 24044323) B24044323
theorem B1388251 : Blo 1387513 1388251 := bstep (se 1 (by rfl) ⟨1041188, by rfl⟩ : syracuseStep 1388251 = 2082377) B2082377
theorem B23711453 : Blo 1387513 23711453 := bstep (se 3 (by rfl) ⟨4445897, by rfl⟩ : syracuseStep 23711453 = 8891795) B8891795
theorem B1388327 : Blo 1387513 1388327 := bstep (se 1 (by rfl) ⟨1041245, by rfl⟩ : syracuseStep 1388327 = 2082491) B2082491
theorem B3338057 : Blo 1387513 3338057 := bstep (se 2 (by rfl) ⟨1251771, by rfl⟩ : syracuseStep 3338057 = 2503543) B2503543
theorem B1388367 : Blo 1387513 1388367 := bstep (se 1 (by rfl) ⟨1041275, by rfl⟩ : syracuseStep 1388367 = 2082551) B2082551
theorem B6008671 : Blo 1387513 6008671 := bstep (se 1 (by rfl) ⟨4506503, by rfl⟩ : syracuseStep 6008671 = 9013007) B9013007
theorem B1388383 : Blo 1387513 1388383 := bstep (se 1 (by rfl) ⟨1041287, by rfl⟩ : syracuseStep 1388383 = 2082575) B2082575
theorem B3125087 : Blo 1387513 3125087 := bstep (se 1 (by rfl) ⟨2343815, by rfl⟩ : syracuseStep 3125087 = 4687631) B4687631
theorem B2502505 : Blo 1387513 2502505 := bstep (se 2 (by rfl) ⟨938439, by rfl⟩ : syracuseStep 2502505 = 1876879) B1876879
theorem B1388411 : Blo 1387513 1388411 := bstep (se 1 (by rfl) ⟨1041308, by rfl⟩ : syracuseStep 1388411 = 2082617) B2082617
theorem B1388463 : Blo 1387513 1388463 := bstep (se 1 (by rfl) ⟨1041347, by rfl⟩ : syracuseStep 1388463 = 2082695) B2082695
theorem B1388487 : Blo 1387513 1388487 := bstep (se 1 (by rfl) ⟨1041365, by rfl⟩ : syracuseStep 1388487 = 2082731) B2082731
theorem B1388507 : Blo 1387513 1388507 := bstep (se 1 (by rfl) ⟨1041380, by rfl⟩ : syracuseStep 1388507 = 2082761) B2082761
theorem B3125267 : Blo 1387513 3125267 := bstep (se 1 (by rfl) ⟨2343950, by rfl⟩ : syracuseStep 3125267 = 4687901) B4687901
theorem B1388583 : Blo 1387513 1388583 := bstep (se 1 (by rfl) ⟨1041437, by rfl⟩ : syracuseStep 1388583 = 2082875) B2082875
theorem B3166265 : Blo 1387513 3166265 := bstep (se 2 (by rfl) ⟨1187349, by rfl⟩ : syracuseStep 3166265 = 2374699) B2374699
theorem B1388623 : Blo 1387513 1388623 := bstep (se 1 (by rfl) ⟨1041467, by rfl⟩ : syracuseStep 1388623 = 2082935) B2082935
theorem B1388639 : Blo 1387513 1388639 := bstep (se 1 (by rfl) ⟨1041479, by rfl⟩ : syracuseStep 1388639 = 2082959) B2082959
theorem B1388667 : Blo 1387513 1388667 := bstep (se 1 (by rfl) ⟨1041500, by rfl⟩ : syracuseStep 1388667 = 2083001) B2083001
theorem B1388719 : Blo 1387513 1388719 := bstep (se 1 (by rfl) ⟨1041539, by rfl⟩ : syracuseStep 1388719 = 2083079) B2083079
theorem B45674675 : Blo 1387513 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B1388743 : Blo 1387513 1388743 := bstep (se 1 (by rfl) ⟨1041557, by rfl⟩ : syracuseStep 1388743 = 2083115) B2083115
theorem B1388763 : Blo 1387513 1388763 := bstep (se 1 (by rfl) ⟨1041572, by rfl⟩ : syracuseStep 1388763 = 2083145) B2083145
theorem B1388839 : Blo 1387513 1388839 := bstep (se 1 (by rfl) ⟨1041629, by rfl⟩ : syracuseStep 1388839 = 2083259) B2083259
theorem B9146675 : Blo 1387513 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B19009853 : Blo 1387513 19009853 := bstep (se 3 (by rfl) ⟨3564347, by rfl⟩ : syracuseStep 19009853 = 7128695) B7128695
theorem B1388879 : Blo 1387513 1388879 := bstep (se 1 (by rfl) ⟨1041659, by rfl⟩ : syracuseStep 1388879 = 2083319) B2083319
theorem B1388895 : Blo 1387513 1388895 := bstep (se 1 (by rfl) ⟨1041671, by rfl⟩ : syracuseStep 1388895 = 2083343) B2083343
theorem B3125609 : Blo 1387513 3125609 := bstep (se 2 (by rfl) ⟨1172103, by rfl⟩ : syracuseStep 3125609 = 2344207) B2344207
theorem B1388923 : Blo 1387513 1388923 := bstep (se 1 (by rfl) ⟨1041692, by rfl⟩ : syracuseStep 1388923 = 2083385) B2083385
theorem B1388975 : Blo 1387513 1388975 := bstep (se 1 (by rfl) ⟨1041731, by rfl⟩ : syracuseStep 1388975 = 2083463) B2083463
theorem B1388999 : Blo 1387513 1388999 := bstep (se 1 (by rfl) ⟨1041749, by rfl⟩ : syracuseStep 1388999 = 2083499) B2083499
theorem B1389019 : Blo 1387513 1389019 := bstep (se 1 (by rfl) ⟨1041764, by rfl⟩ : syracuseStep 1389019 = 2083529) B2083529
theorem B10138121 : Blo 1387513 10138121 := bstep (se 2 (by rfl) ⟨3801795, by rfl⟩ : syracuseStep 10138121 = 7603591) B7603591
theorem B10015265 : Blo 1387513 10015265 := bstep (se 2 (by rfl) ⟨3755724, by rfl⟩ : syracuseStep 10015265 = 7511449) B7511449
theorem B1389095 : Blo 1387513 1389095 := bstep (se 1 (by rfl) ⟨1041821, by rfl⟩ : syracuseStep 1389095 = 2083643) B2083643
theorem B1389135 : Blo 1387513 1389135 := bstep (se 1 (by rfl) ⟨1041851, by rfl⟩ : syracuseStep 1389135 = 2083703) B2083703
theorem B1389151 : Blo 1387513 1389151 := bstep (se 1 (by rfl) ⟨1041863, by rfl⟩ : syracuseStep 1389151 = 2083727) B2083727
theorem B1389179 : Blo 1387513 1389179 := bstep (se 1 (by rfl) ⟨1041884, by rfl⟩ : syracuseStep 1389179 = 2083769) B2083769
theorem B1389231 : Blo 1387513 1389231 := bstep (se 1 (by rfl) ⟨1041923, by rfl⟩ : syracuseStep 1389231 = 2083847) B2083847
theorem B5272249 : Blo 1387513 5272249 := bstep (se 2 (by rfl) ⟨1977093, by rfl⟩ : syracuseStep 5272249 = 3954187) B3954187
theorem B2634439 : Blo 1387513 2634439 := bstep (se 1 (by rfl) ⟨1975829, by rfl⟩ : syracuseStep 2634439 = 3951659) B3951659
theorem B1389255 : Blo 1387513 1389255 := bstep (se 1 (by rfl) ⟨1041941, by rfl⟩ : syracuseStep 1389255 = 2083883) B2083883
theorem B7033553 : Blo 1387513 7033553 := bstep (se 2 (by rfl) ⟨2637582, by rfl⟩ : syracuseStep 7033553 = 5275165) B5275165
theorem B1389275 : Blo 1387513 1389275 := bstep (se 1 (by rfl) ⟨1041956, by rfl⟩ : syracuseStep 1389275 = 2083913) B2083913
theorem B1389351 : Blo 1387513 1389351 := bstep (se 1 (by rfl) ⟨1042013, by rfl⟩ : syracuseStep 1389351 = 2084027) B2084027
theorem B1389391 : Blo 1387513 1389391 := bstep (se 1 (by rfl) ⟨1042043, by rfl⟩ : syracuseStep 1389391 = 2084087) B2084087
theorem B1389407 : Blo 1387513 1389407 := bstep (se 1 (by rfl) ⟨1042055, by rfl⟩ : syracuseStep 1389407 = 2084111) B2084111
theorem B1389435 : Blo 1387513 1389435 := bstep (se 1 (by rfl) ⟨1042076, by rfl⟩ : syracuseStep 1389435 = 2084153) B2084153
theorem B57013145 : Blo 1387513 57013145 := bstep (se 2 (by rfl) ⟨21379929, by rfl⟩ : syracuseStep 57013145 = 42759859) B42759859
theorem B10548143 : Blo 1387513 10548143 := bstep (se 1 (by rfl) ⟨7911107, by rfl⟩ : syracuseStep 10548143 = 15822215) B15822215
theorem B1389487 : Blo 1387513 1389487 := bstep (se 1 (by rfl) ⟨1042115, by rfl⟩ : syracuseStep 1389487 = 2084231) B2084231
theorem B4223927 : Blo 1387513 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B3126203 : Blo 1387513 3126203 := bstep (se 1 (by rfl) ⟨2344652, by rfl⟩ : syracuseStep 3126203 = 4689305) B4689305
theorem B1389511 : Blo 1387513 1389511 := bstep (se 1 (by rfl) ⟨1042133, by rfl⟩ : syracuseStep 1389511 = 2084267) B2084267
theorem B1561639 : Blo 1387513 1561639 := bstep (se 1 (by rfl) ⟨1171229, by rfl⟩ : syracuseStep 1561639 = 2342459) B2342459
theorem B3126329 : Blo 1387513 3126329 := bstep (se 2 (by rfl) ⟨1172373, by rfl⟩ : syracuseStep 3126329 = 2344747) B2344747
theorem B23123009 : Blo 1387513 23123009 := bstep (se 2 (by rfl) ⟨8671128, by rfl⟩ : syracuseStep 23123009 = 17342257) B17342257
theorem B1758287 : Blo 1387513 1758287 := bstep (se 1 (by rfl) ⟨1318715, by rfl⟩ : syracuseStep 1758287 = 2637431) B2637431
theorem B2635001 : Blo 1387513 2635001 := bstep (se 2 (by rfl) ⟨988125, by rfl⟩ : syracuseStep 2635001 = 1976251) B1976251
theorem B4683095 : Blo 1387513 4683095 := bstep (se 1 (by rfl) ⟨3512321, by rfl⟩ : syracuseStep 4683095 = 7024643) B7024643
theorem B10139053 : Blo 1387513 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B2635183 : Blo 1387513 2635183 := bstep (se 1 (by rfl) ⟨1976387, by rfl⟩ : syracuseStep 2635183 = 3952775) B3952775
theorem B46282337 : Blo 1387513 46282337 := bstep (se 2 (by rfl) ⟨17355876, by rfl⟩ : syracuseStep 46282337 = 34711753) B34711753
theorem B7026425 : Blo 1387513 7026425 := bstep (se 2 (by rfl) ⟨2634909, by rfl⟩ : syracuseStep 7026425 = 5269819) B5269819
theorem B26679077 : Blo 1387513 26679077 := bstep (se 4 (by rfl) ⟨2501163, by rfl⟩ : syracuseStep 26679077 = 5002327) B5002327
theorem B21370817 : Blo 1387513 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B40024151 : Blo 1387513 40024151 := bstep (se 1 (by rfl) ⟨30018113, by rfl⟩ : syracuseStep 40024151 = 60036227) B60036227
theorem B8894771 : Blo 1387513 8894771 := bstep (se 1 (by rfl) ⟨6671078, by rfl⟩ : syracuseStep 8894771 = 13342157) B13342157
theorem B4225385 : Blo 1387513 4225385 := bstep (se 2 (by rfl) ⟨1584519, by rfl⟩ : syracuseStep 4225385 = 3169039) B3169039
theorem B5273981 : Blo 1387513 5273981 := bstep (se 3 (by rfl) ⟨988871, by rfl⟩ : syracuseStep 5273981 = 1977743) B1977743
theorem B7027073 : Blo 1387513 7027073 := bstep (se 2 (by rfl) ⟨2635152, by rfl⟩ : syracuseStep 7027073 = 5270305) B5270305
theorem B4684175 : Blo 1387513 4684175 := bstep (se 1 (by rfl) ⟨3513131, by rfl⟩ : syracuseStep 4684175 = 7026263) B7026263
theorem B6765065 : Blo 1387513 6765065 := bstep (se 2 (by rfl) ⟨2536899, by rfl⟩ : syracuseStep 6765065 = 5073799) B5073799
theorem B5003815 : Blo 1387513 5003815 := bstep (se 1 (by rfl) ⟨3752861, by rfl⟩ : syracuseStep 5003815 = 7505723) B7505723
theorem B2341433 : Blo 1387513 2341433 := bstep (se 2 (by rfl) ⟨878037, by rfl⟩ : syracuseStep 2341433 = 1756075) B1756075
theorem B3512929 : Blo 1387513 3512929 := bstep (se 2 (by rfl) ⟨1317348, by rfl⟩ : syracuseStep 3512929 = 2634697) B2634697
theorem B2636459 : Blo 1387513 2636459 := bstep (se 1 (by rfl) ⟨1977344, by rfl⟩ : syracuseStep 2636459 = 3954689) B3954689
theorem B4684499 : Blo 1387513 4684499 := bstep (se 1 (by rfl) ⟨3513374, by rfl⟩ : syracuseStep 4684499 = 7026749) B7026749
theorem B5626583 : Blo 1387513 5626583 := bstep (se 1 (by rfl) ⟨4219937, by rfl⟩ : syracuseStep 5626583 = 8439875) B8439875
theorem B2636687 : Blo 1387513 2636687 := bstep (se 1 (by rfl) ⟨1977515, by rfl⟩ : syracuseStep 2636687 = 3955031) B3955031
theorem B3750839 : Blo 1387513 3750839 := bstep (se 1 (by rfl) ⟨2813129, by rfl⟩ : syracuseStep 3750839 = 5626259) B5626259
theorem B1407943 : Blo 1387513 1407943 := bstep (se 1 (by rfl) ⟨1055957, by rfl⟩ : syracuseStep 1407943 = 2111915) B2111915
theorem B7609423 : Blo 1387513 7609423 := bstep (se 1 (by rfl) ⟨5707067, by rfl⟩ : syracuseStep 7609423 = 11414135) B11414135
theorem B7027883 : Blo 1387513 7027883 := bstep (se 1 (by rfl) ⟨5270912, by rfl⟩ : syracuseStep 7027883 = 10541825) B10541825
theorem B2342135 : Blo 1387513 2342135 := bstep (se 1 (by rfl) ⟨1756601, by rfl⟩ : syracuseStep 2342135 = 3513203) B3513203
theorem B25320721 : Blo 1387513 25320721 := bstep (se 2 (by rfl) ⟨9495270, by rfl⟩ : syracuseStep 25320721 = 18990541) B18990541
theorem B7912727 : Blo 1387513 7912727 := bstep (se 1 (by rfl) ⟨5934545, by rfl⟩ : syracuseStep 7912727 = 11869091) B11869091
theorem B5414381 : Blo 1387513 5414381 := bstep (se 3 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 5414381 = 2030393) B2030393
theorem B3513881 : Blo 1387513 3513881 := bstep (se 2 (by rfl) ⟨1317705, by rfl⟩ : syracuseStep 3513881 = 2635411) B2635411
theorem B2342479 : Blo 1387513 2342479 := bstep (se 1 (by rfl) ⟨1756859, by rfl⟩ : syracuseStep 2342479 = 3513719) B3513719
theorem B7028369 : Blo 1387513 7028369 := bstep (se 2 (by rfl) ⟨2635638, by rfl⟩ : syracuseStep 7028369 = 5271277) B5271277
theorem B7913159 : Blo 1387513 7913159 := bstep (se 1 (by rfl) ⟨5934869, by rfl⟩ : syracuseStep 7913159 = 11869739) B11869739
theorem B11861741 : Blo 1387513 11861741 := bstep (se 3 (by rfl) ⟨2224076, by rfl⟩ : syracuseStep 11861741 = 4448153) B4448153
theorem B2342729 : Blo 1387513 2342729 := bstep (se 2 (by rfl) ⟨878523, by rfl⟩ : syracuseStep 2342729 = 1757047) B1757047
theorem B4685687 : Blo 1387513 4685687 := bstep (se 1 (by rfl) ⟨3514265, by rfl⟩ : syracuseStep 4685687 = 7028531) B7028531
theorem B7905185 : Blo 1387513 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B15007673 : Blo 1387513 15007673 := bstep (se 2 (by rfl) ⟨5627877, by rfl⟩ : syracuseStep 15007673 = 11255755) B11255755
theorem B11263931 : Blo 1387513 11263931 := bstep (se 1 (by rfl) ⟨8447948, by rfl⟩ : syracuseStep 11263931 = 16895897) B16895897
theorem B30031883 : Blo 1387513 30031883 := bstep (se 1 (by rfl) ⟨22523912, by rfl⟩ : syracuseStep 30031883 = 45047825) B45047825
theorem B90079249 : Blo 1387513 90079249 := bstep (se 2 (by rfl) ⟨33779718, by rfl⟩ : syracuseStep 90079249 = 67559437) B67559437
theorem B4685849 : Blo 1387513 4685849 := bstep (se 2 (by rfl) ⟨1757193, by rfl⟩ : syracuseStep 4685849 = 3514387) B3514387
theorem B30449783 : Blo 1387513 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B61661357 : Blo 1387513 61661357 := bstep (se 3 (by rfl) ⟨11561504, by rfl⟩ : syracuseStep 61661357 = 23123009) B23123009
theorem B12673235 : Blo 1387513 12673235 := bstep (se 1 (by rfl) ⟨9504926, by rfl⟩ : syracuseStep 12673235 = 19009853) B19009853
theorem B6758747 : Blo 1387513 6758747 := bstep (se 1 (by rfl) ⟨5069060, by rfl⟩ : syracuseStep 6758747 = 10138121) B10138121
theorem B6676843 : Blo 1387513 6676843 := bstep (se 1 (by rfl) ⟨5007632, by rfl⟩ : syracuseStep 6676843 = 10015265) B10015265
theorem B5931539 : Blo 1387513 5931539 := bstep (se 1 (by rfl) ⟨4448654, by rfl⟩ : syracuseStep 5931539 = 8897309) B8897309
theorem B2081351 : Blo 1387513 2081351 := bstep (se 1 (by rfl) ⟨1561013, by rfl⟩ : syracuseStep 2081351 = 3122027) B3122027
theorem B2081387 : Blo 1387513 2081387 := bstep (se 1 (by rfl) ⟨1561040, by rfl⟩ : syracuseStep 2081387 = 3122081) B3122081
theorem B6668983 : Blo 1387513 6668983 := bstep (se 1 (by rfl) ⟨5001737, by rfl⟩ : syracuseStep 6668983 = 10003475) B10003475
theorem B2343647 : Blo 1387513 2343647 := bstep (se 1 (by rfl) ⟨1757735, by rfl⟩ : syracuseStep 2343647 = 3515471) B3515471
theorem B2081615 : Blo 1387513 2081615 := bstep (se 1 (by rfl) ⟨1561211, by rfl⟩ : syracuseStep 2081615 = 3122423) B3122423
theorem B3122063 : Blo 1387513 3122063 := bstep (se 1 (by rfl) ⟨2341547, by rfl⟩ : syracuseStep 3122063 = 4683095) B4683095
theorem B7029665 : Blo 1387513 7029665 := bstep (se 2 (by rfl) ⟨2636124, by rfl⟩ : syracuseStep 7029665 = 5272249) B5272249
theorem B2344079 : Blo 1387513 2344079 := bstep (se 1 (by rfl) ⟨1758059, by rfl⟩ : syracuseStep 2344079 = 3516119) B3516119
theorem B17786051 : Blo 1387513 17786051 := bstep (se 1 (by rfl) ⟨13339538, by rfl⟩ : syracuseStep 17786051 = 26679077) B26679077
theorem B7603415 : Blo 1387513 7603415 := bstep (se 1 (by rfl) ⟨5702561, by rfl⟩ : syracuseStep 7603415 = 11405123) B11405123
theorem B2082011 : Blo 1387513 2082011 := bstep (se 1 (by rfl) ⟨1561508, by rfl⟩ : syracuseStep 2082011 = 3123017) B3123017
theorem B4687091 : Blo 1387513 4687091 := bstep (se 1 (by rfl) ⟨3515318, by rfl⟩ : syracuseStep 4687091 = 7030637) B7030637
theorem B1877257 : Blo 1387513 1877257 := bstep (se 2 (by rfl) ⟨703971, by rfl⟩ : syracuseStep 1877257 = 1407943) B1407943
theorem B4752683 : Blo 1387513 4752683 := bstep (se 1 (by rfl) ⟨3564512, by rfl⟩ : syracuseStep 4752683 = 7129025) B7129025
theorem B4687199 : Blo 1387513 4687199 := bstep (se 1 (by rfl) ⟨3515399, by rfl⟩ : syracuseStep 4687199 = 7030799) B7030799
theorem B2344315 : Blo 1387513 2344315 := bstep (se 1 (by rfl) ⟨1758236, by rfl⟩ : syracuseStep 2344315 = 3516473) B3516473
theorem B2082185 : Blo 1387513 2082185 := bstep (se 2 (by rfl) ⟨780819, by rfl⟩ : syracuseStep 2082185 = 1561639) B1561639
theorem B26682767 : Blo 1387513 26682767 := bstep (se 1 (by rfl) ⟨20012075, by rfl⟩ : syracuseStep 26682767 = 40024151) B40024151
theorem B3515987 : Blo 1387513 3515987 := bstep (se 1 (by rfl) ⟨2636990, by rfl⟩ : syracuseStep 3515987 = 5273981) B5273981
theorem B3122783 : Blo 1387513 3122783 := bstep (se 1 (by rfl) ⟨2342087, by rfl⟩ : syracuseStep 3122783 = 4684175) B4684175
theorem B33760961 : Blo 1387513 33760961 := bstep (se 2 (by rfl) ⟨12660360, by rfl⟩ : syracuseStep 33760961 = 25320721) B25320721
theorem B2082539 : Blo 1387513 2082539 := bstep (se 1 (by rfl) ⟨1561904, by rfl⟩ : syracuseStep 2082539 = 3123809) B3123809
theorem B3122999 : Blo 1387513 3122999 := bstep (se 1 (by rfl) ⟨2342249, by rfl⟩ : syracuseStep 3122999 = 4684499) B4684499
theorem B4450153 : Blo 1387513 4450153 := bstep (se 2 (by rfl) ⟨1668807, by rfl⟩ : syracuseStep 4450153 = 3337615) B3337615
theorem B13346693 : Blo 1387513 13346693 := bstep (se 4 (by rfl) ⟨1251252, by rfl⟩ : syracuseStep 13346693 = 2502505) B2502505
theorem B13518737 : Blo 1387513 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B2500559 : Blo 1387513 2500559 := bstep (se 1 (by rfl) ⟨1875419, by rfl⟩ : syracuseStep 2500559 = 3750839) B3750839
theorem B2082767 : Blo 1387513 2082767 := bstep (se 1 (by rfl) ⟨1562075, by rfl⟩ : syracuseStep 2082767 = 3124151) B3124151
theorem B3123305 : Blo 1387513 3123305 := bstep (se 2 (by rfl) ⟨1171239, by rfl⟩ : syracuseStep 3123305 = 2342479) B2342479
theorem B18278693 : Blo 1387513 18278693 := bstep (se 4 (by rfl) ⟨1713627, by rfl⟩ : syracuseStep 18278693 = 3427255) B3427255
theorem B2083163 : Blo 1387513 2083163 := bstep (se 1 (by rfl) ⟨1562372, by rfl⟩ : syracuseStep 2083163 = 3124745) B3124745
theorem B7907827 : Blo 1387513 7907827 := bstep (se 1 (by rfl) ⟨5930870, by rfl⟩ : syracuseStep 7907827 = 11861741) B11861741
theorem B2083391 : Blo 1387513 2083391 := bstep (se 1 (by rfl) ⟨1562543, by rfl⟩ : syracuseStep 2083391 = 3125087) B3125087
theorem B3123791 : Blo 1387513 3123791 := bstep (se 1 (by rfl) ⟨2342843, by rfl⟩ : syracuseStep 3123791 = 4685687) B4685687
theorem B5270123 : Blo 1387513 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B10005115 : Blo 1387513 10005115 := bstep (se 1 (by rfl) ⟨7503836, by rfl⟩ : syracuseStep 10005115 = 15007673) B15007673
theorem B2083511 : Blo 1387513 2083511 := bstep (se 1 (by rfl) ⟨1562633, by rfl⟩ : syracuseStep 2083511 = 3125267) B3125267
theorem B3123935 : Blo 1387513 3123935 := bstep (se 1 (by rfl) ⟨2342951, by rfl⟩ : syracuseStep 3123935 = 4685903) B4685903
theorem B5270291 : Blo 1387513 5270291 := bstep (se 1 (by rfl) ⟨3952718, by rfl⟩ : syracuseStep 5270291 = 7905437) B7905437
theorem B6097783 : Blo 1387513 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B4688765 : Blo 1387513 4688765 := bstep (se 3 (by rfl) ⟨879143, by rfl⟩ : syracuseStep 4688765 = 1758287) B1758287
theorem B2083739 : Blo 1387513 2083739 := bstep (se 1 (by rfl) ⟨1562804, by rfl⟩ : syracuseStep 2083739 = 3125609) B3125609
theorem B3124187 : Blo 1387513 3124187 := bstep (se 1 (by rfl) ⟨2343140, by rfl⟩ : syracuseStep 3124187 = 4686281) B4686281
theorem B4689035 : Blo 1387513 4689035 := bstep (se 1 (by rfl) ⟨3516776, by rfl⟩ : syracuseStep 4689035 = 7033553) B7033553
theorem B3124367 : Blo 1387513 3124367 := bstep (se 1 (by rfl) ⟨2343275, by rfl⟩ : syracuseStep 3124367 = 4686551) B4686551
theorem B3124457 : Blo 1387513 3124457 := bstep (se 2 (by rfl) ⟨1171671, by rfl⟩ : syracuseStep 3124457 = 2343343) B2343343
theorem B1387807 : Blo 1387513 1387807 := bstep (se 1 (by rfl) ⟨1040855, by rfl⟩ : syracuseStep 1387807 = 2081711) B2081711
theorem B3124511 : Blo 1387513 3124511 := bstep (se 1 (by rfl) ⟨2343383, by rfl⟩ : syracuseStep 3124511 = 4686767) B4686767
theorem B4009247 : Blo 1387513 4009247 := bstep (se 1 (by rfl) ⟨3006935, by rfl⟩ : syracuseStep 4009247 = 6013871) B6013871
theorem B7032095 : Blo 1387513 7032095 := bstep (se 1 (by rfl) ⟨5274071, by rfl⟩ : syracuseStep 7032095 = 10548143) B10548143
theorem B2084135 : Blo 1387513 2084135 := bstep (se 1 (by rfl) ⟨1563101, by rfl⟩ : syracuseStep 2084135 = 3126203) B3126203
theorem B1387867 : Blo 1387513 1387867 := bstep (se 1 (by rfl) ⟨1040900, by rfl⟩ : syracuseStep 1387867 = 2081801) B2081801
theorem B1387887 : Blo 1387513 1387887 := bstep (se 1 (by rfl) ⟨1040915, by rfl⟩ : syracuseStep 1387887 = 2081831) B2081831
theorem B2084219 : Blo 1387513 2084219 := bstep (se 1 (by rfl) ⟨1563164, by rfl⟩ : syracuseStep 2084219 = 3126329) B3126329
theorem B6671753 : Blo 1387513 6671753 := bstep (se 2 (by rfl) ⟨2501907, by rfl⟩ : syracuseStep 6671753 = 5003815) B5003815
theorem B1387943 : Blo 1387513 1387943 := bstep (se 1 (by rfl) ⟨1040957, by rfl⟩ : syracuseStep 1387943 = 2081915) B2081915
theorem B1756667 : Blo 1387513 1756667 := bstep (se 1 (by rfl) ⟨1317500, by rfl⟩ : syracuseStep 1756667 = 2635001) B2635001
theorem B1388027 : Blo 1387513 1388027 := bstep (se 1 (by rfl) ⟨1041020, by rfl⟩ : syracuseStep 1388027 = 2082041) B2082041
theorem B9022985 : Blo 1387513 9022985 := bstep (se 2 (by rfl) ⟨3383619, by rfl⟩ : syracuseStep 9022985 = 6767239) B6767239
theorem B13897277 : Blo 1387513 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B1388095 : Blo 1387513 1388095 := bstep (se 1 (by rfl) ⟨1041071, by rfl⟩ : syracuseStep 1388095 = 2082143) B2082143
theorem B1388103 : Blo 1387513 1388103 := bstep (se 1 (by rfl) ⟨1041077, by rfl⟩ : syracuseStep 1388103 = 2082155) B2082155
theorem B11267693 : Blo 1387513 11267693 := bstep (se 3 (by rfl) ⟨2112692, by rfl⟩ : syracuseStep 11267693 = 4225385) B4225385
theorem B1388255 : Blo 1387513 1388255 := bstep (se 1 (by rfl) ⟨1041191, by rfl⟩ : syracuseStep 1388255 = 2082383) B2082383
theorem B30854891 : Blo 1387513 30854891 := bstep (se 1 (by rfl) ⟨23141168, by rfl⟩ : syracuseStep 30854891 = 46282337) B46282337
theorem B2002729 : Blo 1387513 2002729 := bstep (se 2 (by rfl) ⟨751023, by rfl⟩ : syracuseStep 2002729 = 1502047) B1502047
theorem B3125033 : Blo 1387513 3125033 := bstep (se 2 (by rfl) ⟨1171887, by rfl⟩ : syracuseStep 3125033 = 2343775) B2343775
theorem B1388335 : Blo 1387513 1388335 := bstep (se 1 (by rfl) ⟨1041251, by rfl⟩ : syracuseStep 1388335 = 2082503) B2082503
theorem B1388443 : Blo 1387513 1388443 := bstep (se 1 (by rfl) ⟨1041332, by rfl⟩ : syracuseStep 1388443 = 2082665) B2082665
theorem B10538909 : Blo 1387513 10538909 := bstep (se 3 (by rfl) ⟨1976045, by rfl⟩ : syracuseStep 10538909 = 3952091) B3952091
theorem B1388495 : Blo 1387513 1388495 := bstep (se 1 (by rfl) ⟨1041371, by rfl⟩ : syracuseStep 1388495 = 2082743) B2082743
theorem B1388519 : Blo 1387513 1388519 := bstep (se 1 (by rfl) ⟨1041389, by rfl⟩ : syracuseStep 1388519 = 2082779) B2082779
theorem B12029953 : Blo 1387513 12029953 := bstep (se 2 (by rfl) ⟨4511232, by rfl⟩ : syracuseStep 12029953 = 9022465) B9022465
theorem B10145897 : Blo 1387513 10145897 := bstep (se 2 (by rfl) ⟨3804711, by rfl⟩ : syracuseStep 10145897 = 7609423) B7609423
theorem B5271763 : Blo 1387513 5271763 := bstep (se 1 (by rfl) ⟨3953822, by rfl⟩ : syracuseStep 5271763 = 7907645) B7907645
theorem B1388831 : Blo 1387513 1388831 := bstep (se 1 (by rfl) ⟨1041623, by rfl⟩ : syracuseStep 1388831 = 2083247) B2083247
theorem B4510043 : Blo 1387513 4510043 := bstep (se 1 (by rfl) ⟨3382532, by rfl⟩ : syracuseStep 4510043 = 6765065) B6765065
theorem B1388891 : Blo 1387513 1388891 := bstep (se 1 (by rfl) ⟨1041668, by rfl⟩ : syracuseStep 1388891 = 2083337) B2083337
theorem B1388911 : Blo 1387513 1388911 := bstep (se 1 (by rfl) ⟨1041683, by rfl⟩ : syracuseStep 1388911 = 2083367) B2083367
theorem B1560955 : Blo 1387513 1560955 := bstep (se 1 (by rfl) ⟨1170716, by rfl⟩ : syracuseStep 1560955 = 2341433) B2341433
theorem B1388967 : Blo 1387513 1388967 := bstep (se 1 (by rfl) ⟨1041725, by rfl⟩ : syracuseStep 1388967 = 2083451) B2083451
theorem B1757639 : Blo 1387513 1757639 := bstep (se 1 (by rfl) ⟨1318229, by rfl⟩ : syracuseStep 1757639 = 2636459) B2636459
theorem B1389051 : Blo 1387513 1389051 := bstep (se 1 (by rfl) ⟨1041788, by rfl⟩ : syracuseStep 1389051 = 2083577) B2083577
theorem B1389119 : Blo 1387513 1389119 := bstep (se 1 (by rfl) ⟨1041839, by rfl⟩ : syracuseStep 1389119 = 2083679) B2083679
theorem B1389127 : Blo 1387513 1389127 := bstep (se 1 (by rfl) ⟨1041845, by rfl⟩ : syracuseStep 1389127 = 2083691) B2083691
theorem B1757791 : Blo 1387513 1757791 := bstep (se 1 (by rfl) ⟨1318343, by rfl⟩ : syracuseStep 1757791 = 2636687) B2636687
theorem B5272235 : Blo 1387513 5272235 := bstep (se 1 (by rfl) ⟨3954176, by rfl⟩ : syracuseStep 5272235 = 7908353) B7908353
theorem B1389279 : Blo 1387513 1389279 := bstep (se 1 (by rfl) ⟨1041959, by rfl⟩ : syracuseStep 1389279 = 2083919) B2083919
theorem B2634515 : Blo 1387513 2634515 := bstep (se 1 (by rfl) ⟨1975886, by rfl⟩ : syracuseStep 2634515 = 3951773) B3951773
theorem B1389359 : Blo 1387513 1389359 := bstep (se 1 (by rfl) ⟨1042019, by rfl⟩ : syracuseStep 1389359 = 2084039) B2084039
theorem B1561423 : Blo 1387513 1561423 := bstep (se 1 (by rfl) ⟨1171067, by rfl⟩ : syracuseStep 1561423 = 2342135) B2342135
theorem B3126095 : Blo 1387513 3126095 := bstep (se 1 (by rfl) ⟨2344571, by rfl⟩ : syracuseStep 3126095 = 4689143) B4689143
theorem B8901485 : Blo 1387513 8901485 := bstep (se 3 (by rfl) ⟨1669028, by rfl⟩ : syracuseStep 8901485 = 3338057) B3338057
theorem B2225051 : Blo 1387513 2225051 := bstep (se 1 (by rfl) ⟨1668788, by rfl⟩ : syracuseStep 2225051 = 3337577) B3337577
theorem B1389467 : Blo 1387513 1389467 := bstep (se 1 (by rfl) ⟨1042100, by rfl⟩ : syracuseStep 1389467 = 2084201) B2084201
theorem B3609587 : Blo 1387513 3609587 := bstep (se 1 (by rfl) ⟨2707190, by rfl⟩ : syracuseStep 3609587 = 5414381) B5414381
theorem B2634743 : Blo 1387513 2634743 := bstep (se 1 (by rfl) ⟨1976057, by rfl⟩ : syracuseStep 2634743 = 3952115) B3952115
theorem B3126311 : Blo 1387513 3126311 := bstep (se 1 (by rfl) ⟨2344733, by rfl⟩ : syracuseStep 3126311 = 4689467) B4689467
theorem B24032335 : Blo 1387513 24032335 := bstep (se 1 (by rfl) ⟨18024251, by rfl⟩ : syracuseStep 24032335 = 36048503) B36048503
theorem B15807635 : Blo 1387513 15807635 := bstep (se 1 (by rfl) ⟨11855726, by rfl⟩ : syracuseStep 15807635 = 23711453) B23711453
theorem B56988845 : Blo 1387513 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B1561819 : Blo 1387513 1561819 := bstep (se 1 (by rfl) ⟨1171364, by rfl⟩ : syracuseStep 1561819 = 2342729) B2342729
theorem B7509287 : Blo 1387513 7509287 := bstep (se 1 (by rfl) ⟨5631965, by rfl⟩ : syracuseStep 7509287 = 11263931) B11263931
theorem B4445579 : Blo 1387513 4445579 := bstep (se 1 (by rfl) ⟨3334184, by rfl⟩ : syracuseStep 4445579 = 6668369) B6668369
theorem B8443373 : Blo 1387513 8443373 := bstep (se 3 (by rfl) ⟨1583132, by rfl⟩ : syracuseStep 8443373 = 3166265) B3166265
theorem B1562107 : Blo 1387513 1562107 := bstep (se 1 (by rfl) ⟨1171580, by rfl⟩ : syracuseStep 1562107 = 2343161) B2343161
theorem B3954233 : Blo 1387513 3954233 := bstep (se 2 (by rfl) ⟨1482837, by rfl⟩ : syracuseStep 3954233 = 2965675) B2965675
theorem B1562287 : Blo 1387513 1562287 := bstep (se 1 (by rfl) ⟨1171715, by rfl⟩ : syracuseStep 1562287 = 2343431) B2343431
theorem B38008763 : Blo 1387513 38008763 := bstep (se 1 (by rfl) ⟨28506572, by rfl⟩ : syracuseStep 38008763 = 57013145) B57013145
theorem B1562575 : Blo 1387513 1562575 := bstep (se 1 (by rfl) ⟨1171931, by rfl⟩ : syracuseStep 1562575 = 2343863) B2343863
theorem B2815951 : Blo 1387513 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B4683905 : Blo 1387513 4683905 := bstep (se 2 (by rfl) ⟨1756464, by rfl⟩ : syracuseStep 4683905 = 3512929) B3512929
theorem B3512585 : Blo 1387513 3512585 := bstep (se 2 (by rfl) ⟨1317219, by rfl⟩ : syracuseStep 3512585 = 2634439) B2634439
theorem B1562971 : Blo 1387513 1562971 := bstep (se 1 (by rfl) ⟨1172228, by rfl⟩ : syracuseStep 1562971 = 2344457) B2344457
theorem B1563079 : Blo 1387513 1563079 := bstep (se 1 (by rfl) ⟨1172309, by rfl⟩ : syracuseStep 1563079 = 2344619) B2344619
theorem B18987473 : Blo 1387513 18987473 := bstep (se 2 (by rfl) ⟨7120302, by rfl⟩ : syracuseStep 18987473 = 14240605) B14240605
theorem B4684283 : Blo 1387513 4684283 := bstep (se 1 (by rfl) ⟨3513212, by rfl⟩ : syracuseStep 4684283 = 7026425) B7026425
theorem B15014423 : Blo 1387513 15014423 := bstep (se 1 (by rfl) ⟨11260817, by rfl⟩ : syracuseStep 15014423 = 22521635) B22521635
theorem B11262503 : Blo 1387513 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B5929847 : Blo 1387513 5929847 := bstep (se 1 (by rfl) ⟨4447385, by rfl⟩ : syracuseStep 5929847 = 8894771) B8894771
theorem B4684715 : Blo 1387513 4684715 := bstep (se 1 (by rfl) ⟨3513536, by rfl⟩ : syracuseStep 4684715 = 7027073) B7027073
theorem B4447219 : Blo 1387513 4447219 := bstep (se 1 (by rfl) ⟨3335414, by rfl⟩ : syracuseStep 4447219 = 6670829) B6670829
theorem B3562483 : Blo 1387513 3562483 := bstep (se 1 (by rfl) ⟨2671862, by rfl⟩ : syracuseStep 3562483 = 5343725) B5343725
theorem B6675443 : Blo 1387513 6675443 := bstep (se 1 (by rfl) ⟨5006582, by rfl⟩ : syracuseStep 6675443 = 10013165) B10013165
theorem B3751055 : Blo 1387513 3751055 := bstep (se 1 (by rfl) ⟨2813291, by rfl⟩ : syracuseStep 3751055 = 5626583) B5626583
theorem B32046245 : Blo 1387513 32046245 := bstep (se 4 (by rfl) ⟨3004335, by rfl⟩ : syracuseStep 32046245 = 6008671) B6008671
theorem B3513577 : Blo 1387513 3513577 := bstep (se 2 (by rfl) ⟨1317591, by rfl⟩ : syracuseStep 3513577 = 2635183) B2635183
theorem B20028683 : Blo 1387513 20028683 := bstep (se 1 (by rfl) ⟨15021512, by rfl⟩ : syracuseStep 20028683 = 30043025) B30043025
theorem B3955999 : Blo 1387513 3955999 := bstep (se 1 (by rfl) ⟨2966999, by rfl⟩ : syracuseStep 3955999 = 5933999) B5933999
theorem B3513739 : Blo 1387513 3513739 := bstep (se 1 (by rfl) ⟨2635304, by rfl⟩ : syracuseStep 3513739 = 5270609) B5270609
theorem B4685255 : Blo 1387513 4685255 := bstep (se 1 (by rfl) ⟨3513941, by rfl⟩ : syracuseStep 4685255 = 7027883) B7027883
theorem B5275151 : Blo 1387513 5275151 := bstep (se 1 (by rfl) ⟨3956363, by rfl⟩ : syracuseStep 5275151 = 7912727) B7912727
theorem B2342587 : Blo 1387513 2342587 := bstep (se 1 (by rfl) ⟨1756940, by rfl⟩ : syracuseStep 2342587 = 3513881) B3513881
theorem B3514043 : Blo 1387513 3514043 := bstep (se 1 (by rfl) ⟨2635532, by rfl⟩ : syracuseStep 3514043 = 5271065) B5271065
theorem B12181241 : Blo 1387513 12181241 := bstep (se 2 (by rfl) ⟨4567965, by rfl⟩ : syracuseStep 12181241 = 9135931) B9135931
theorem B4685579 : Blo 1387513 4685579 := bstep (se 1 (by rfl) ⟨3514184, by rfl⟩ : syracuseStep 4685579 = 7028369) B7028369
theorem B5005097 : Blo 1387513 5005097 := bstep (se 2 (by rfl) ⟨1876911, by rfl⟩ : syracuseStep 5005097 = 3753823) B3753823
theorem B5275439 : Blo 1387513 5275439 := bstep (se 1 (by rfl) ⟨3956579, by rfl⟩ : syracuseStep 5275439 = 7913159) B7913159
theorem B21372731 : Blo 1387513 21372731 := bstep (se 1 (by rfl) ⟨16029548, by rfl⟩ : syracuseStep 21372731 = 32059097) B32059097
theorem B16039937 : Blo 1387513 16039937 := bstep (se 2 (by rfl) ⟨6014976, by rfl⟩ : syracuseStep 16039937 = 12029953) B12029953
theorem B20021255 : Blo 1387513 20021255 := bstep (se 1 (by rfl) ⟨15015941, by rfl⟩ : syracuseStep 20021255 = 30031883) B30031883
theorem B20299855 : Blo 1387513 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B41107571 : Blo 1387513 41107571 := bstep (se 1 (by rfl) ⟨30830678, by rfl⟩ : syracuseStep 41107571 = 61661357) B61661357
theorem B4505831 : Blo 1387513 4505831 := bstep (se 1 (by rfl) ⟨3379373, by rfl⟩ : syracuseStep 4505831 = 6758747) B6758747
theorem B3006695 : Blo 1387513 3006695 := bstep (se 1 (by rfl) ⟨2255021, by rfl⟩ : syracuseStep 3006695 = 4510043) B4510043
theorem B7029017 : Blo 1387513 7029017 := bstep (se 2 (by rfl) ⟨2635881, by rfl⟩ : syracuseStep 7029017 = 5271763) B5271763
theorem B3514823 : Blo 1387513 3514823 := bstep (se 1 (by rfl) ⟨2636117, by rfl⟩ : syracuseStep 3514823 = 5272235) B5272235
theorem B2081273 : Blo 1387513 2081273 := bstep (se 2 (by rfl) ⟨780477, by rfl⟩ : syracuseStep 2081273 = 1560955) B1560955
theorem B2081375 : Blo 1387513 2081375 := bstep (se 1 (by rfl) ⟨1561031, by rfl⟩ : syracuseStep 2081375 = 3122063) B3122063
theorem B1483367 : Blo 1387513 1483367 := bstep (se 1 (by rfl) ⟨1112525, by rfl⟩ : syracuseStep 1483367 = 2225051) B2225051
theorem B4686443 : Blo 1387513 4686443 := bstep (se 1 (by rfl) ⟨3514832, by rfl⟩ : syracuseStep 4686443 = 7029665) B7029665
theorem B10543769 : Blo 1387513 10543769 := bstep (se 2 (by rfl) ⟨3953913, by rfl⟩ : syracuseStep 10543769 = 7907827) B7907827
theorem B2343721 : Blo 1387513 2343721 := bstep (se 2 (by rfl) ⟨878895, by rfl⟩ : syracuseStep 2343721 = 1757791) B1757791
theorem B2343991 : Blo 1387513 2343991 := bstep (se 1 (by rfl) ⟨1757993, by rfl⟩ : syracuseStep 2343991 = 3515987) B3515987
theorem B2081855 : Blo 1387513 2081855 := bstep (se 1 (by rfl) ⟨1561391, by rfl⟩ : syracuseStep 2081855 = 3122783) B3122783
theorem B2081897 : Blo 1387513 2081897 := bstep (se 2 (by rfl) ⟨780711, by rfl⟩ : syracuseStep 2081897 = 1561423) B1561423
theorem B4687037 : Blo 1387513 4687037 := bstep (se 3 (by rfl) ⟨878819, by rfl⟩ : syracuseStep 4687037 = 1757639) B1757639
theorem B2081999 : Blo 1387513 2081999 := bstep (se 1 (by rfl) ⟨1561499, by rfl⟩ : syracuseStep 2081999 = 3122999) B3122999
theorem B8897795 : Blo 1387513 8897795 := bstep (se 1 (by rfl) ⟨6673346, by rfl⟩ : syracuseStep 8897795 = 13346693) B13346693
theorem B9012491 : Blo 1387513 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B25339175 : Blo 1387513 25339175 := bstep (se 1 (by rfl) ⟨19004381, by rfl⟩ : syracuseStep 25339175 = 38008763) B38008763
theorem B2082203 : Blo 1387513 2082203 := bstep (se 1 (by rfl) ⟨1561652, by rfl⟩ : syracuseStep 2082203 = 3123305) B3123305
theorem B3122603 : Blo 1387513 3122603 := bstep (se 1 (by rfl) ⟨2341952, by rfl⟩ : syracuseStep 3122603 = 4683905) B4683905
theorem B30033341 : Blo 1387513 30033341 := bstep (se 3 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 30033341 = 11262503) B11262503
theorem B2082425 : Blo 1387513 2082425 := bstep (se 2 (by rfl) ⟨780909, by rfl⟩ : syracuseStep 2082425 = 1561819) B1561819
theorem B12658315 : Blo 1387513 12658315 := bstep (se 1 (by rfl) ⟨9493736, by rfl⟩ : syracuseStep 12658315 = 18987473) B18987473
theorem B3122855 : Blo 1387513 3122855 := bstep (se 1 (by rfl) ⟨2342141, by rfl⟩ : syracuseStep 3122855 = 4684283) B4684283
theorem B2082527 : Blo 1387513 2082527 := bstep (se 1 (by rfl) ⟨1561895, by rfl⟩ : syracuseStep 2082527 = 3123791) B3123791
theorem B2082623 : Blo 1387513 2082623 := bstep (se 1 (by rfl) ⟨1561967, by rfl⟩ : syracuseStep 2082623 = 3123935) B3123935
theorem B3123143 : Blo 1387513 3123143 := bstep (se 1 (by rfl) ⟨2342357, by rfl⟩ : syracuseStep 3123143 = 4684715) B4684715
theorem B2082791 : Blo 1387513 2082791 := bstep (se 1 (by rfl) ⟨1562093, by rfl⟩ : syracuseStep 2082791 = 3124187) B3124187
theorem B4450295 : Blo 1387513 4450295 := bstep (se 1 (by rfl) ⟨3337721, by rfl⟩ : syracuseStep 4450295 = 6675443) B6675443
theorem B2082809 : Blo 1387513 2082809 := bstep (se 2 (by rfl) ⟨781053, by rfl⟩ : syracuseStep 2082809 = 1562107) B1562107
theorem B2500703 : Blo 1387513 2500703 := bstep (se 1 (by rfl) ⟨1875527, by rfl⟩ : syracuseStep 2500703 = 3751055) B3751055
theorem B2082911 : Blo 1387513 2082911 := bstep (se 1 (by rfl) ⟨1562183, by rfl⟩ : syracuseStep 2082911 = 3124367) B3124367
theorem B2082971 : Blo 1387513 2082971 := bstep (se 1 (by rfl) ⟨1562228, by rfl⟩ : syracuseStep 2082971 = 3124457) B3124457
theorem B2083007 : Blo 1387513 2083007 := bstep (se 1 (by rfl) ⟨1562255, by rfl⟩ : syracuseStep 2083007 = 3124511) B3124511
theorem B2672831 : Blo 1387513 2672831 := bstep (se 1 (by rfl) ⟨2004623, by rfl⟩ : syracuseStep 2672831 = 4009247) B4009247
theorem B4688063 : Blo 1387513 4688063 := bstep (se 1 (by rfl) ⟨3516047, by rfl⟩ : syracuseStep 4688063 = 7032095) B7032095
theorem B2083049 : Blo 1387513 2083049 := bstep (se 2 (by rfl) ⟨781143, by rfl⟩ : syracuseStep 2083049 = 1562287) B1562287
theorem B3123449 : Blo 1387513 3123449 := bstep (se 2 (by rfl) ⟨1171293, by rfl⟩ : syracuseStep 3123449 = 2342587) B2342587
theorem B3123503 : Blo 1387513 3123503 := bstep (se 1 (by rfl) ⟨2342627, by rfl⟩ : syracuseStep 3123503 = 4685255) B4685255
theorem B6015323 : Blo 1387513 6015323 := bstep (se 1 (by rfl) ⟨4511492, by rfl⟩ : syracuseStep 6015323 = 9022985) B9022985
theorem B3516767 : Blo 1387513 3516767 := bstep (se 1 (by rfl) ⟨2637575, by rfl⟩ : syracuseStep 3516767 = 5275151) B5275151
theorem B5933537 : Blo 1387513 5933537 := bstep (se 2 (by rfl) ⟨2225076, by rfl⟩ : syracuseStep 5933537 = 4450153) B4450153
theorem B8120827 : Blo 1387513 8120827 := bstep (se 1 (by rfl) ⟨6090620, by rfl⟩ : syracuseStep 8120827 = 12181241) B12181241
theorem B3123719 : Blo 1387513 3123719 := bstep (se 1 (by rfl) ⟨2342789, by rfl⟩ : syracuseStep 3123719 = 4685579) B4685579
theorem B3336731 : Blo 1387513 3336731 := bstep (se 1 (by rfl) ⟨2502548, by rfl⟩ : syracuseStep 3336731 = 5005097) B5005097
theorem B2083355 : Blo 1387513 2083355 := bstep (se 1 (by rfl) ⟨1562516, by rfl⟩ : syracuseStep 2083355 = 3125033) B3125033
theorem B3516959 : Blo 1387513 3516959 := bstep (se 1 (by rfl) ⟨2637719, by rfl⟩ : syracuseStep 3516959 = 5275439) B5275439
theorem B14248487 : Blo 1387513 14248487 := bstep (se 1 (by rfl) ⟨10686365, by rfl⟩ : syracuseStep 14248487 = 21372731) B21372731
theorem B2083433 : Blo 1387513 2083433 := bstep (se 2 (by rfl) ⟨781287, by rfl⟩ : syracuseStep 2083433 = 1562575) B1562575
theorem B3754601 : Blo 1387513 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B3123899 : Blo 1387513 3123899 := bstep (se 1 (by rfl) ⟨2342924, by rfl⟩ : syracuseStep 3123899 = 4685849) B4685849
theorem B120105665 : Blo 1387513 120105665 := bstep (se 2 (by rfl) ⟨45039624, by rfl⟩ : syracuseStep 120105665 = 90079249) B90079249
theorem B8448823 : Blo 1387513 8448823 := bstep (se 1 (by rfl) ⟨6336617, by rfl⟩ : syracuseStep 8448823 = 12673235) B12673235
theorem B1387567 : Blo 1387513 1387567 := bstep (se 1 (by rfl) ⟨1040675, by rfl⟩ : syracuseStep 1387567 = 2081351) B2081351
theorem B1387591 : Blo 1387513 1387591 := bstep (se 1 (by rfl) ⟨1040693, by rfl⟩ : syracuseStep 1387591 = 2081387) B2081387
theorem B2083961 : Blo 1387513 2083961 := bstep (se 2 (by rfl) ⟨781485, by rfl⟩ : syracuseStep 2083961 = 1562971) B1562971
theorem B1756343 : Blo 1387513 1756343 := bstep (se 1 (by rfl) ⟨1317257, by rfl⟩ : syracuseStep 1756343 = 2634515) B2634515
theorem B1387743 : Blo 1387513 1387743 := bstep (se 1 (by rfl) ⟨1040807, by rfl⟩ : syracuseStep 1387743 = 2081615) B2081615
theorem B2084063 : Blo 1387513 2084063 := bstep (se 1 (by rfl) ⟨1563047, by rfl⟩ : syracuseStep 2084063 = 3126095) B3126095
theorem B5934323 : Blo 1387513 5934323 := bstep (se 1 (by rfl) ⟨4450742, by rfl⟩ : syracuseStep 5934323 = 8901485) B8901485
theorem B2084105 : Blo 1387513 2084105 := bstep (se 2 (by rfl) ⟨781539, by rfl⟩ : syracuseStep 2084105 = 1563079) B1563079
theorem B1756495 : Blo 1387513 1756495 := bstep (se 1 (by rfl) ⟨1317371, by rfl⟩ : syracuseStep 1756495 = 2634743) B2634743
theorem B2084207 : Blo 1387513 2084207 := bstep (se 1 (by rfl) ⟨1563155, by rfl⟩ : syracuseStep 2084207 = 3126311) B3126311
theorem B10538423 : Blo 1387513 10538423 := bstep (se 1 (by rfl) ⟨7903817, by rfl⟩ : syracuseStep 10538423 = 15807635) B15807635
theorem B20024765 : Blo 1387513 20024765 := bstep (se 3 (by rfl) ⟨3754643, by rfl⟩ : syracuseStep 20024765 = 7509287) B7509287
theorem B11857367 : Blo 1387513 11857367 := bstep (se 1 (by rfl) ⟨8893025, by rfl⟩ : syracuseStep 11857367 = 17786051) B17786051
theorem B1388007 : Blo 1387513 1388007 := bstep (se 1 (by rfl) ⟨1041005, by rfl⟩ : syracuseStep 1388007 = 2082011) B2082011
theorem B3124727 : Blo 1387513 3124727 := bstep (se 1 (by rfl) ⟨2343545, by rfl⟩ : syracuseStep 3124727 = 4687091) B4687091
theorem B13340153 : Blo 1387513 13340153 := bstep (se 2 (by rfl) ⟨5002557, by rfl⟩ : syracuseStep 13340153 = 10005115) B10005115
theorem B3124799 : Blo 1387513 3124799 := bstep (se 1 (by rfl) ⟨2343599, by rfl⟩ : syracuseStep 3124799 = 4687199) B4687199
theorem B8891977 : Blo 1387513 8891977 := bstep (se 2 (by rfl) ⟨3334491, by rfl⟩ : syracuseStep 8891977 = 6668983) B6668983
theorem B1388123 : Blo 1387513 1388123 := bstep (se 1 (by rfl) ⟨1041092, by rfl⟩ : syracuseStep 1388123 = 2082185) B2082185
theorem B17788511 : Blo 1387513 17788511 := bstep (se 1 (by rfl) ⟨13341383, by rfl⟩ : syracuseStep 17788511 = 26682767) B26682767
theorem B22507307 : Blo 1387513 22507307 := bstep (se 1 (by rfl) ⟨16880480, by rfl⟩ : syracuseStep 22507307 = 33760961) B33760961
theorem B1388359 : Blo 1387513 1388359 := bstep (se 1 (by rfl) ⟨1041269, by rfl⟩ : syracuseStep 1388359 = 2082539) B2082539
theorem B8130377 : Blo 1387513 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B22515661 : Blo 1387513 22515661 := bstep (se 3 (by rfl) ⟨4221686, by rfl⟩ : syracuseStep 22515661 = 8443373) B8443373
theorem B1667039 : Blo 1387513 1667039 := bstep (se 1 (by rfl) ⟨1250279, by rfl⟩ : syracuseStep 1667039 = 2500559) B2500559
theorem B1388511 : Blo 1387513 1388511 := bstep (se 1 (by rfl) ⟨1041383, by rfl⟩ : syracuseStep 1388511 = 2082767) B2082767
theorem B32043113 : Blo 1387513 32043113 := bstep (se 2 (by rfl) ⟨12016167, by rfl⟩ : syracuseStep 32043113 = 24032335) B24032335
theorem B12185795 : Blo 1387513 12185795 := bstep (se 1 (by rfl) ⟨9139346, by rfl⟩ : syracuseStep 12185795 = 18278693) B18278693
theorem B1388775 : Blo 1387513 1388775 := bstep (se 1 (by rfl) ⟨1041581, by rfl⟩ : syracuseStep 1388775 = 2083163) B2083163
theorem B2503009 : Blo 1387513 2503009 := bstep (se 2 (by rfl) ⟨938628, by rfl⟩ : syracuseStep 2503009 = 1877257) B1877257
theorem B1388927 : Blo 1387513 1388927 := bstep (se 1 (by rfl) ⟨1041695, by rfl⟩ : syracuseStep 1388927 = 2083391) B2083391
theorem B1389007 : Blo 1387513 1389007 := bstep (se 1 (by rfl) ⟨1041755, by rfl⟩ : syracuseStep 1389007 = 2083511) B2083511
theorem B3125753 : Blo 1387513 3125753 := bstep (se 2 (by rfl) ⟨1172157, by rfl⟩ : syracuseStep 3125753 = 2344315) B2344315
theorem B3953231 : Blo 1387513 3953231 := bstep (se 1 (by rfl) ⟨2964923, by rfl⟩ : syracuseStep 3953231 = 5929847) B5929847
theorem B3125843 : Blo 1387513 3125843 := bstep (se 1 (by rfl) ⟨2344382, by rfl⟩ : syracuseStep 3125843 = 4688765) B4688765
theorem B1389159 : Blo 1387513 1389159 := bstep (se 1 (by rfl) ⟨1041869, by rfl⟩ : syracuseStep 1389159 = 2083739) B2083739
theorem B3126023 : Blo 1387513 3126023 := bstep (se 1 (by rfl) ⟨2344517, by rfl⟩ : syracuseStep 3126023 = 4689035) B4689035
theorem B1389423 : Blo 1387513 1389423 := bstep (se 1 (by rfl) ⟨1042067, by rfl⟩ : syracuseStep 1389423 = 2084135) B2084135
theorem B1389479 : Blo 1387513 1389479 := bstep (se 1 (by rfl) ⟨1042109, by rfl⟩ : syracuseStep 1389479 = 2084219) B2084219
theorem B7025939 : Blo 1387513 7025939 := bstep (se 1 (by rfl) ⟨5269454, by rfl⟩ : syracuseStep 7025939 = 10538909) B10538909
theorem B6763931 : Blo 1387513 6763931 := bstep (se 1 (by rfl) ⟨5072948, by rfl⟩ : syracuseStep 6763931 = 10145897) B10145897
theorem B3954359 : Blo 1387513 3954359 := bstep (se 1 (by rfl) ⟨2965769, by rfl⟩ : syracuseStep 3954359 = 5931539) B5931539
theorem B8902457 : Blo 1387513 8902457 := bstep (se 2 (by rfl) ⟨3338421, by rfl⟩ : syracuseStep 8902457 = 6676843) B6676843
theorem B1562431 : Blo 1387513 1562431 := bstep (se 1 (by rfl) ⟨1171823, by rfl⟩ : syracuseStep 1562431 = 2343647) B2343647
theorem B2406391 : Blo 1387513 2406391 := bstep (se 1 (by rfl) ⟨1804793, by rfl⟩ : syracuseStep 2406391 = 3609587) B3609587
theorem B1562719 : Blo 1387513 1562719 := bstep (se 1 (by rfl) ⟨1172039, by rfl⟩ : syracuseStep 1562719 = 2344079) B2344079
theorem B37992563 : Blo 1387513 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B5068943 : Blo 1387513 5068943 := bstep (se 1 (by rfl) ⟨3801707, by rfl⟩ : syracuseStep 5068943 = 7603415) B7603415
theorem B3168455 : Blo 1387513 3168455 := bstep (se 1 (by rfl) ⟨2376341, by rfl⟩ : syracuseStep 3168455 = 4752683) B4752683
theorem B2963719 : Blo 1387513 2963719 := bstep (se 1 (by rfl) ⟨2222789, by rfl⟩ : syracuseStep 2963719 = 4445579) B4445579
theorem B2636155 : Blo 1387513 2636155 := bstep (se 1 (by rfl) ⟨1977116, by rfl⟩ : syracuseStep 2636155 = 3954233) B3954233
theorem B5929625 : Blo 1387513 5929625 := bstep (se 2 (by rfl) ⟨2223609, by rfl⟩ : syracuseStep 5929625 = 4447219) B4447219
theorem B4749977 : Blo 1387513 4749977 := bstep (se 2 (by rfl) ⟨1781241, by rfl⟩ : syracuseStep 4749977 = 3562483) B3562483
theorem B4684445 : Blo 1387513 4684445 := bstep (se 3 (by rfl) ⟨878333, by rfl⟩ : syracuseStep 4684445 = 1756667) B1756667
theorem B2341723 : Blo 1387513 2341723 := bstep (se 1 (by rfl) ⟨1756292, by rfl⟩ : syracuseStep 2341723 = 3512585) B3512585
theorem B4684769 : Blo 1387513 4684769 := bstep (se 2 (by rfl) ⟨1756788, by rfl⟩ : syracuseStep 4684769 = 3513577) B3513577
theorem B10009615 : Blo 1387513 10009615 := bstep (se 1 (by rfl) ⟨7507211, by rfl⟩ : syracuseStep 10009615 = 15014423) B15014423
theorem B5274665 : Blo 1387513 5274665 := bstep (se 2 (by rfl) ⟨1977999, by rfl⟩ : syracuseStep 5274665 = 3955999) B3955999
theorem B3513415 : Blo 1387513 3513415 := bstep (se 1 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 3513415 = 5270123) B5270123
theorem B3513527 : Blo 1387513 3513527 := bstep (se 1 (by rfl) ⟨2635145, by rfl⟩ : syracuseStep 3513527 = 5270291) B5270291
theorem B4684985 : Blo 1387513 4684985 := bstep (se 2 (by rfl) ⟨1756869, by rfl⟩ : syracuseStep 4684985 = 3513739) B3513739
theorem B82279709 : Blo 1387513 82279709 := bstep (se 3 (by rfl) ⟨15427445, by rfl⟩ : syracuseStep 82279709 = 30854891) B30854891
theorem B21364163 : Blo 1387513 21364163 := bstep (se 1 (by rfl) ⟨16023122, by rfl⟩ : syracuseStep 21364163 = 32046245) B32046245
theorem B13352455 : Blo 1387513 13352455 := bstep (se 1 (by rfl) ⟨10014341, by rfl⟩ : syracuseStep 13352455 = 20028683) B20028683
theorem B4447835 : Blo 1387513 4447835 := bstep (se 1 (by rfl) ⟨3335876, by rfl⟩ : syracuseStep 4447835 = 6671753) B6671753
theorem B9264851 : Blo 1387513 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B2670305 : Blo 1387513 2670305 := bstep (se 2 (by rfl) ⟨1001364, by rfl⟩ : syracuseStep 2670305 = 2002729) B2002729
theorem B7511795 : Blo 1387513 7511795 := bstep (se 1 (by rfl) ⟨5633846, by rfl⟩ : syracuseStep 7511795 = 11267693) B11267693
theorem B2342695 : Blo 1387513 2342695 := bstep (se 1 (by rfl) ⟨1757021, by rfl⟩ : syracuseStep 2342695 = 3514043) B3514043
theorem B27066473 : Blo 1387513 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B4686011 : Blo 1387513 4686011 := bstep (se 1 (by rfl) ⟨3514508, by rfl⟩ : syracuseStep 4686011 = 7029017) B7029017
theorem B2343215 : Blo 1387513 2343215 := bstep (se 1 (by rfl) ⟨1757411, by rfl⟩ : syracuseStep 2343215 = 3514823) B3514823
theorem B7029179 : Blo 1387513 7029179 := bstep (se 1 (by rfl) ⟨5271884, by rfl⟩ : syracuseStep 7029179 = 10543769) B10543769
theorem B3514873 : Blo 1387513 3514873 := bstep (se 2 (by rfl) ⟨1318077, by rfl⟩ : syracuseStep 3514873 = 2636155) B2636155
theorem B5931863 : Blo 1387513 5931863 := bstep (se 1 (by rfl) ⟨4448897, by rfl⟩ : syracuseStep 5931863 = 8897795) B8897795
theorem B16892783 : Blo 1387513 16892783 := bstep (se 1 (by rfl) ⟨12669587, by rfl⟩ : syracuseStep 16892783 = 25339175) B25339175
theorem B2081735 : Blo 1387513 2081735 := bstep (se 1 (by rfl) ⟨1561301, by rfl⟩ : syracuseStep 2081735 = 3122603) B3122603
theorem B20022227 : Blo 1387513 20022227 := bstep (se 1 (by rfl) ⟨15016670, by rfl⟩ : syracuseStep 20022227 = 30033341) B30033341
theorem B11265097 : Blo 1387513 11265097 := bstep (se 2 (by rfl) ⟨4224411, by rfl⟩ : syracuseStep 11265097 = 8448823) B8448823
theorem B2081903 : Blo 1387513 2081903 := bstep (se 1 (by rfl) ⟨1561427, by rfl⟩ : syracuseStep 2081903 = 3122855) B3122855
theorem B3122297 : Blo 1387513 3122297 := bstep (se 2 (by rfl) ⟨1170861, by rfl⟩ : syracuseStep 3122297 = 2341723) B2341723
theorem B2082095 : Blo 1387513 2082095 := bstep (se 1 (by rfl) ⟨1561571, by rfl⟩ : syracuseStep 2082095 = 3123143) B3123143
theorem B2966863 : Blo 1387513 2966863 := bstep (se 1 (by rfl) ⟨2225147, by rfl⟩ : syracuseStep 2966863 = 4450295) B4450295
theorem B13346153 : Blo 1387513 13346153 := bstep (se 2 (by rfl) ⟨5004807, by rfl⟩ : syracuseStep 13346153 = 10009615) B10009615
theorem B2082299 : Blo 1387513 2082299 := bstep (se 1 (by rfl) ⟨1561724, by rfl⟩ : syracuseStep 2082299 = 3123449) B3123449
theorem B2082335 : Blo 1387513 2082335 := bstep (se 1 (by rfl) ⟨1561751, by rfl⟩ : syracuseStep 2082335 = 3123503) B3123503
theorem B2344511 : Blo 1387513 2344511 := bstep (se 1 (by rfl) ⟨1758383, by rfl⟩ : syracuseStep 2344511 = 3516767) B3516767
theorem B2082479 : Blo 1387513 2082479 := bstep (se 1 (by rfl) ⟨1561859, by rfl⟩ : syracuseStep 2082479 = 3123719) B3123719
theorem B2344639 : Blo 1387513 2344639 := bstep (se 1 (by rfl) ⟨1758479, by rfl⟩ : syracuseStep 2344639 = 3516959) B3516959
theorem B3122963 : Blo 1387513 3122963 := bstep (se 1 (by rfl) ⟨2342222, by rfl⟩ : syracuseStep 3122963 = 4684445) B4684445
theorem B2082599 : Blo 1387513 2082599 := bstep (se 1 (by rfl) ⟨1561949, by rfl⟩ : syracuseStep 2082599 = 3123899) B3123899
theorem B80070443 : Blo 1387513 80070443 := bstep (se 1 (by rfl) ⟨60052832, by rfl⟩ : syracuseStep 80070443 = 120105665) B120105665
theorem B7120813 : Blo 1387513 7120813 := bstep (se 3 (by rfl) ⟨1335152, by rfl⟩ : syracuseStep 7120813 = 2670305) B2670305
theorem B3123179 : Blo 1387513 3123179 := bstep (se 1 (by rfl) ⟨2342384, by rfl⟩ : syracuseStep 3123179 = 4684769) B4684769
theorem B17803273 : Blo 1387513 17803273 := bstep (se 2 (by rfl) ⟨6676227, by rfl⟩ : syracuseStep 17803273 = 13352455) B13352455
theorem B3516443 : Blo 1387513 3516443 := bstep (se 1 (by rfl) ⟨2637332, by rfl⟩ : syracuseStep 3516443 = 5274665) B5274665
theorem B11855969 : Blo 1387513 11855969 := bstep (se 2 (by rfl) ⟨4445988, by rfl⟩ : syracuseStep 11855969 = 8891977) B8891977
theorem B3123323 : Blo 1387513 3123323 := bstep (se 1 (by rfl) ⟨2342492, by rfl⟩ : syracuseStep 3123323 = 4684985) B4684985
theorem B16877753 : Blo 1387513 16877753 := bstep (se 2 (by rfl) ⟨6329157, by rfl⟩ : syracuseStep 16877753 = 12658315) B12658315
theorem B2083151 : Blo 1387513 2083151 := bstep (se 1 (by rfl) ⟨1562363, by rfl⟩ : syracuseStep 2083151 = 3124727) B3124727
theorem B2083199 : Blo 1387513 2083199 := bstep (se 1 (by rfl) ⟨1562399, by rfl⟩ : syracuseStep 2083199 = 3124799) B3124799
theorem B3123593 : Blo 1387513 3123593 := bstep (se 2 (by rfl) ⟨1171347, by rfl⟩ : syracuseStep 3123593 = 2342695) B2342695
theorem B2083241 : Blo 1387513 2083241 := bstep (se 2 (by rfl) ⟨781215, by rfl⟩ : syracuseStep 2083241 = 1562431) B1562431
theorem B5007863 : Blo 1387513 5007863 := bstep (se 1 (by rfl) ⟨3755897, by rfl⟩ : syracuseStep 5007863 = 7511795) B7511795
theorem B10693291 : Blo 1387513 10693291 := bstep (se 1 (by rfl) ⟨8019968, by rfl⟩ : syracuseStep 10693291 = 16039937) B16039937
theorem B13347503 : Blo 1387513 13347503 := bstep (se 1 (by rfl) ⟨10010627, by rfl⟩ : syracuseStep 13347503 = 20021255) B20021255
theorem B27405047 : Blo 1387513 27405047 := bstep (se 1 (by rfl) ⟨20553785, by rfl⟩ : syracuseStep 27405047 = 41107571) B41107571
theorem B2083625 : Blo 1387513 2083625 := bstep (se 2 (by rfl) ⟨781359, by rfl⟩ : syracuseStep 2083625 = 1562719) B1562719
theorem B1387515 : Blo 1387513 1387515 := bstep (se 1 (by rfl) ⟨1040636, by rfl⟩ : syracuseStep 1387515 = 2081273) B2081273
theorem B2083835 : Blo 1387513 2083835 := bstep (se 1 (by rfl) ⟨1562876, by rfl⟩ : syracuseStep 2083835 = 3125753) B3125753
theorem B3951625 : Blo 1387513 3951625 := bstep (se 2 (by rfl) ⟨1481859, by rfl⟩ : syracuseStep 3951625 = 2963719) B2963719
theorem B2083895 : Blo 1387513 2083895 := bstep (se 1 (by rfl) ⟨1562921, by rfl⟩ : syracuseStep 2083895 = 3125843) B3125843
theorem B1387583 : Blo 1387513 1387583 := bstep (se 1 (by rfl) ⟨1040687, by rfl⟩ : syracuseStep 1387583 = 2081375) B2081375
theorem B3124295 : Blo 1387513 3124295 := bstep (se 1 (by rfl) ⟨2343221, by rfl⟩ : syracuseStep 3124295 = 4686443) B4686443
theorem B3337345 : Blo 1387513 3337345 := bstep (se 2 (by rfl) ⟨1251504, by rfl⟩ : syracuseStep 3337345 = 2503009) B2503009
theorem B2084015 : Blo 1387513 2084015 := bstep (se 1 (by rfl) ⟨1563011, by rfl⟩ : syracuseStep 2084015 = 3126023) B3126023
theorem B8449213 : Blo 1387513 8449213 := bstep (se 3 (by rfl) ⟨1584227, by rfl⟩ : syracuseStep 8449213 = 3168455) B3168455
theorem B1387903 : Blo 1387513 1387903 := bstep (se 1 (by rfl) ⟨1040927, by rfl⟩ : syracuseStep 1387903 = 2081855) B2081855
theorem B1387931 : Blo 1387513 1387931 := bstep (se 1 (by rfl) ⟨1040948, by rfl⟩ : syracuseStep 1387931 = 2081897) B2081897
theorem B3124691 : Blo 1387513 3124691 := bstep (se 1 (by rfl) ⟨2343518, by rfl⟩ : syracuseStep 3124691 = 4687037) B4687037
theorem B1387999 : Blo 1387513 1387999 := bstep (se 1 (by rfl) ⟨1040999, by rfl⟩ : syracuseStep 1387999 = 2081999) B2081999
theorem B6008327 : Blo 1387513 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B1388135 : Blo 1387513 1388135 := bstep (se 1 (by rfl) ⟨1041101, by rfl⟩ : syracuseStep 1388135 = 2082203) B2082203
theorem B4509287 : Blo 1387513 4509287 := bstep (se 1 (by rfl) ⟨3381965, by rfl⟩ : syracuseStep 4509287 = 6763931) B6763931
theorem B3124961 : Blo 1387513 3124961 := bstep (se 2 (by rfl) ⟨1171860, by rfl⟩ : syracuseStep 3124961 = 2343721) B2343721
theorem B1388283 : Blo 1387513 1388283 := bstep (se 1 (by rfl) ⟨1041212, by rfl⟩ : syracuseStep 1388283 = 2082425) B2082425
theorem B1388351 : Blo 1387513 1388351 := bstep (se 1 (by rfl) ⟨1041263, by rfl⟩ : syracuseStep 1388351 = 2082527) B2082527
theorem B5934971 : Blo 1387513 5934971 := bstep (se 1 (by rfl) ⟨4451228, by rfl⟩ : syracuseStep 5934971 = 8902457) B8902457
theorem B1388415 : Blo 1387513 1388415 := bstep (se 1 (by rfl) ⟨1041311, by rfl⟩ : syracuseStep 1388415 = 2082623) B2082623
theorem B35573741 : Blo 1387513 35573741 := bstep (se 3 (by rfl) ⟨6670076, by rfl⟩ : syracuseStep 35573741 = 13340153) B13340153
theorem B1388527 : Blo 1387513 1388527 := bstep (se 1 (by rfl) ⟨1041395, by rfl⟩ : syracuseStep 1388527 = 2082791) B2082791
theorem B1388539 : Blo 1387513 1388539 := bstep (se 1 (by rfl) ⟨1041404, by rfl⟩ : syracuseStep 1388539 = 2082809) B2082809
theorem B1667135 : Blo 1387513 1667135 := bstep (se 1 (by rfl) ⟨1250351, by rfl⟩ : syracuseStep 1667135 = 2500703) B2500703
theorem B1388607 : Blo 1387513 1388607 := bstep (se 1 (by rfl) ⟨1041455, by rfl⟩ : syracuseStep 1388607 = 2082911) B2082911
theorem B3125321 : Blo 1387513 3125321 := bstep (se 2 (by rfl) ⟨1171995, by rfl⟩ : syracuseStep 3125321 = 2343991) B2343991
theorem B3379295 : Blo 1387513 3379295 := bstep (se 1 (by rfl) ⟨2534471, by rfl⟩ : syracuseStep 3379295 = 5068943) B5068943
theorem B1388647 : Blo 1387513 1388647 := bstep (se 1 (by rfl) ⟨1041485, by rfl⟩ : syracuseStep 1388647 = 2082971) B2082971
theorem B1388671 : Blo 1387513 1388671 := bstep (se 1 (by rfl) ⟨1041503, by rfl⟩ : syracuseStep 1388671 = 2083007) B2083007
theorem B1781887 : Blo 1387513 1781887 := bstep (se 1 (by rfl) ⟨1336415, by rfl⟩ : syracuseStep 1781887 = 2672831) B2672831
theorem B3125375 : Blo 1387513 3125375 := bstep (se 1 (by rfl) ⟨2344031, by rfl⟩ : syracuseStep 3125375 = 4688063) B4688063
theorem B1388699 : Blo 1387513 1388699 := bstep (se 1 (by rfl) ⟨1041524, by rfl⟩ : syracuseStep 1388699 = 2083049) B2083049
theorem B4010215 : Blo 1387513 4010215 := bstep (se 1 (by rfl) ⟨3007661, by rfl⟩ : syracuseStep 4010215 = 6015323) B6015323
theorem B2224487 : Blo 1387513 2224487 := bstep (se 1 (by rfl) ⟨1668365, by rfl⟩ : syracuseStep 2224487 = 3336731) B3336731
theorem B1388903 : Blo 1387513 1388903 := bstep (se 1 (by rfl) ⟨1041677, by rfl⟩ : syracuseStep 1388903 = 2083355) B2083355
theorem B9498991 : Blo 1387513 9498991 := bstep (se 1 (by rfl) ⟨7124243, by rfl⟩ : syracuseStep 9498991 = 14248487) B14248487
theorem B1388955 : Blo 1387513 1388955 := bstep (se 1 (by rfl) ⟨1041716, by rfl⟩ : syracuseStep 1388955 = 2083433) B2083433
theorem B2503067 : Blo 1387513 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B3953083 : Blo 1387513 3953083 := bstep (se 1 (by rfl) ⟨2964812, by rfl⟩ : syracuseStep 3953083 = 5929625) B5929625
theorem B3166651 : Blo 1387513 3166651 := bstep (se 1 (by rfl) ⟨2374988, by rfl⟩ : syracuseStep 3166651 = 4749977) B4749977
theorem B1389307 : Blo 1387513 1389307 := bstep (se 1 (by rfl) ⟨1041980, by rfl⟩ : syracuseStep 1389307 = 2083961) B2083961
theorem B1389375 : Blo 1387513 1389375 := bstep (se 1 (by rfl) ⟨1042031, by rfl⟩ : syracuseStep 1389375 = 2084063) B2084063
theorem B1389403 : Blo 1387513 1389403 := bstep (se 1 (by rfl) ⟨1042052, by rfl⟩ : syracuseStep 1389403 = 2084105) B2084105
theorem B1389471 : Blo 1387513 1389471 := bstep (se 1 (by rfl) ⟨1042103, by rfl⟩ : syracuseStep 1389471 = 2084207) B2084207
theorem B7025615 : Blo 1387513 7025615 := bstep (se 1 (by rfl) ⟨5269211, by rfl⟩ : syracuseStep 7025615 = 10538423) B10538423
theorem B13349843 : Blo 1387513 13349843 := bstep (se 1 (by rfl) ⟨10012382, by rfl⟩ : syracuseStep 13349843 = 20024765) B20024765
theorem B14242775 : Blo 1387513 14242775 := bstep (se 1 (by rfl) ⟨10682081, by rfl⟩ : syracuseStep 14242775 = 21364163) B21364163
theorem B11859007 : Blo 1387513 11859007 := bstep (se 1 (by rfl) ⟨8894255, by rfl⟩ : syracuseStep 11859007 = 17788511) B17788511
theorem B51336341 : Blo 1387513 51336341 := bstep (se 6 (by rfl) ⟨1203195, by rfl⟩ : syracuseStep 51336341 = 2406391) B2406391
theorem B15004871 : Blo 1387513 15004871 := bstep (se 1 (by rfl) ⟨11253653, by rfl⟩ : syracuseStep 15004871 = 22507307) B22507307
theorem B5420251 : Blo 1387513 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B4445437 : Blo 1387513 4445437 := bstep (se 3 (by rfl) ⟨833519, by rfl⟩ : syracuseStep 4445437 = 1667039) B1667039
theorem B30020881 : Blo 1387513 30020881 := bstep (se 2 (by rfl) ⟨11257830, by rfl⟩ : syracuseStep 30020881 = 22515661) B22515661
theorem B21362075 : Blo 1387513 21362075 := bstep (se 1 (by rfl) ⟨16021556, by rfl⟩ : syracuseStep 21362075 = 32043113) B32043113
theorem B8123863 : Blo 1387513 8123863 := bstep (se 1 (by rfl) ⟨6092897, by rfl⟩ : syracuseStep 8123863 = 12185795) B12185795
theorem B3003887 : Blo 1387513 3003887 := bstep (se 1 (by rfl) ⟨2252915, by rfl⟩ : syracuseStep 3003887 = 4505831) B4505831
theorem B2004463 : Blo 1387513 2004463 := bstep (se 1 (by rfl) ⟨1503347, by rfl⟩ : syracuseStep 2004463 = 3006695) B3006695
theorem B2635487 : Blo 1387513 2635487 := bstep (se 1 (by rfl) ⟨1976615, by rfl⟩ : syracuseStep 2635487 = 3953231) B3953231
theorem B4683581 : Blo 1387513 4683581 := bstep (se 3 (by rfl) ⟨878171, by rfl⟩ : syracuseStep 4683581 = 1756343) B1756343
theorem B10827769 : Blo 1387513 10827769 := bstep (se 2 (by rfl) ⟨4060413, by rfl⟩ : syracuseStep 10827769 = 8120827) B8120827
theorem B4683959 : Blo 1387513 4683959 := bstep (se 1 (by rfl) ⟨3512969, by rfl⟩ : syracuseStep 4683959 = 7025939) B7025939
theorem B2636239 : Blo 1387513 2636239 := bstep (se 1 (by rfl) ⟨1977179, by rfl⟩ : syracuseStep 2636239 = 3954359) B3954359
theorem B25328375 : Blo 1387513 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B4684553 : Blo 1387513 4684553 := bstep (se 2 (by rfl) ⟨1756707, by rfl⟩ : syracuseStep 4684553 = 3513415) B3513415
theorem B3955645 : Blo 1387513 3955645 := bstep (se 3 (by rfl) ⟨741683, by rfl⟩ : syracuseStep 3955645 = 1483367) B1483367
theorem B3955691 : Blo 1387513 3955691 := bstep (se 1 (by rfl) ⟨2966768, by rfl⟩ : syracuseStep 3955691 = 5933537) B5933537
theorem B2341993 : Blo 1387513 2341993 := bstep (se 2 (by rfl) ⟨878247, by rfl⟩ : syracuseStep 2341993 = 1756495) B1756495
theorem B2342351 : Blo 1387513 2342351 := bstep (se 1 (by rfl) ⟨1756763, by rfl⟩ : syracuseStep 2342351 = 3513527) B3513527
theorem B3956215 : Blo 1387513 3956215 := bstep (se 1 (by rfl) ⟨2967161, by rfl⟩ : syracuseStep 3956215 = 5934323) B5934323
theorem B54853139 : Blo 1387513 54853139 := bstep (se 1 (by rfl) ⟨41139854, by rfl⟩ : syracuseStep 54853139 = 82279709) B82279709
theorem B7904911 : Blo 1387513 7904911 := bstep (se 1 (by rfl) ⟨5928683, by rfl⟩ : syracuseStep 7904911 = 11857367) B11857367
theorem B2965223 : Blo 1387513 2965223 := bstep (se 1 (by rfl) ⟨2223917, by rfl⟩ : syracuseStep 2965223 = 4447835) B4447835
theorem B6176567 : Blo 1387513 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B2252863 : Blo 1387513 2252863 := bstep (se 1 (by rfl) ⟨1689647, by rfl⟩ : syracuseStep 2252863 = 3379295) B3379295
theorem B2375849 : Blo 1387513 2375849 := bstep (se 2 (by rfl) ⟨890943, by rfl⟩ : syracuseStep 2375849 = 1781887) B1781887
theorem B1482991 : Blo 1387513 1482991 := bstep (se 1 (by rfl) ⟨1112243, by rfl⟩ : syracuseStep 1482991 = 2224487) B2224487
theorem B4686119 : Blo 1387513 4686119 := bstep (se 1 (by rfl) ⟨3514589, by rfl⟩ : syracuseStep 4686119 = 7029179) B7029179
theorem B12665321 : Blo 1387513 12665321 := bstep (se 2 (by rfl) ⟨4749495, by rfl⟩ : syracuseStep 12665321 = 9498991) B9498991
theorem B3514985 : Blo 1387513 3514985 := bstep (se 2 (by rfl) ⟨1318119, by rfl⟩ : syracuseStep 3514985 = 2636239) B2636239
theorem B4686497 : Blo 1387513 4686497 := bstep (se 2 (by rfl) ⟨1757436, by rfl⟩ : syracuseStep 4686497 = 3514873) B3514873
theorem B2081531 : Blo 1387513 2081531 := bstep (se 1 (by rfl) ⟨1561148, by rfl⟩ : syracuseStep 2081531 = 3122297) B3122297
theorem B10003247 : Blo 1387513 10003247 := bstep (se 1 (by rfl) ⟨7502435, by rfl⟩ : syracuseStep 10003247 = 15004871) B15004871
theorem B8897435 : Blo 1387513 8897435 := bstep (se 1 (by rfl) ⟨6673076, by rfl⟩ : syracuseStep 8897435 = 13346153) B13346153
theorem B2081975 : Blo 1387513 2081975 := bstep (se 1 (by rfl) ⟨1561481, by rfl⟩ : syracuseStep 2081975 = 3122963) B3122963
theorem B53380295 : Blo 1387513 53380295 := bstep (se 1 (by rfl) ⟨40035221, by rfl⟩ : syracuseStep 53380295 = 80070443) B80070443
theorem B3122387 : Blo 1387513 3122387 := bstep (se 1 (by rfl) ⟨2341790, by rfl⟩ : syracuseStep 3122387 = 4683581) B4683581
theorem B13354301 : Blo 1387513 13354301 := bstep (se 3 (by rfl) ⟨2503931, by rfl⟩ : syracuseStep 13354301 = 5007863) B5007863
theorem B2082119 : Blo 1387513 2082119 := bstep (se 1 (by rfl) ⟨1561589, by rfl⟩ : syracuseStep 2082119 = 3123179) B3123179
theorem B5268833 : Blo 1387513 5268833 := bstep (se 2 (by rfl) ⟨1975812, by rfl⟩ : syracuseStep 5268833 = 3951625) B3951625
theorem B2344295 : Blo 1387513 2344295 := bstep (se 1 (by rfl) ⟨1758221, by rfl⟩ : syracuseStep 2344295 = 3516443) B3516443
theorem B2082215 : Blo 1387513 2082215 := bstep (se 1 (by rfl) ⟨1561661, by rfl⟩ : syracuseStep 2082215 = 3123323) B3123323
theorem B15812009 : Blo 1387513 15812009 := bstep (se 2 (by rfl) ⟨5929503, by rfl⟩ : syracuseStep 15812009 = 11859007) B11859007
theorem B3122639 : Blo 1387513 3122639 := bstep (se 1 (by rfl) ⟨2341979, by rfl⟩ : syracuseStep 3122639 = 4683959) B4683959
theorem B3122657 : Blo 1387513 3122657 := bstep (se 2 (by rfl) ⟨1170996, by rfl⟩ : syracuseStep 3122657 = 2341993) B2341993
theorem B11265617 : Blo 1387513 11265617 := bstep (se 2 (by rfl) ⟨4224606, by rfl⟩ : syracuseStep 11265617 = 8449213) B8449213
theorem B2082395 : Blo 1387513 2082395 := bstep (se 1 (by rfl) ⟨1561796, by rfl⟩ : syracuseStep 2082395 = 3123593) B3123593
theorem B7227001 : Blo 1387513 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B40027841 : Blo 1387513 40027841 := bstep (se 2 (by rfl) ⟨15010440, by rfl⟩ : syracuseStep 40027841 = 30020881) B30020881
theorem B8898335 : Blo 1387513 8898335 := bstep (se 1 (by rfl) ⟨6673751, by rfl⟩ : syracuseStep 8898335 = 13347503) B13347503
theorem B18270031 : Blo 1387513 18270031 := bstep (se 1 (by rfl) ⟨13702523, by rfl⟩ : syracuseStep 18270031 = 27405047) B27405047
theorem B16885583 : Blo 1387513 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B3123035 : Blo 1387513 3123035 := bstep (se 1 (by rfl) ⟨2342276, by rfl⟩ : syracuseStep 3123035 = 4684553) B4684553
theorem B10831817 : Blo 1387513 10831817 := bstep (se 2 (by rfl) ⟨4061931, by rfl⟩ : syracuseStep 10831817 = 8123863) B8123863
theorem B2672617 : Blo 1387513 2672617 := bstep (se 2 (by rfl) ⟨1002231, by rfl⟩ : syracuseStep 2672617 = 2004463) B2004463
theorem B2082863 : Blo 1387513 2082863 := bstep (se 1 (by rfl) ⟨1562147, by rfl⟩ : syracuseStep 2082863 = 3124295) B3124295
theorem B2083127 : Blo 1387513 2083127 := bstep (se 1 (by rfl) ⟨1562345, by rfl⟩ : syracuseStep 2083127 = 3124691) B3124691
theorem B2083307 : Blo 1387513 2083307 := bstep (se 1 (by rfl) ⟨1562480, by rfl⟩ : syracuseStep 2083307 = 3124961) B3124961
theorem B1976815 : Blo 1387513 1976815 := bstep (se 1 (by rfl) ⟨1482611, by rfl⟩ : syracuseStep 1976815 = 2965223) B2965223
theorem B37980733 : Blo 1387513 37980733 := bstep (se 3 (by rfl) ⟨7121387, by rfl⟩ : syracuseStep 37980733 = 14242775) B14242775
theorem B14437025 : Blo 1387513 14437025 := bstep (se 2 (by rfl) ⟨5413884, by rfl⟩ : syracuseStep 14437025 = 10827769) B10827769
theorem B2083547 : Blo 1387513 2083547 := bstep (se 1 (by rfl) ⟨1562660, by rfl⟩ : syracuseStep 2083547 = 3125321) B3125321
theorem B2083583 : Blo 1387513 2083583 := bstep (se 1 (by rfl) ⟨1562687, by rfl⟩ : syracuseStep 2083583 = 3125375) B3125375
theorem B3124007 : Blo 1387513 3124007 := bstep (se 1 (by rfl) ⟨2343005, by rfl⟩ : syracuseStep 3124007 = 4686011) B4686011
theorem B5270777 : Blo 1387513 5270777 := bstep (se 2 (by rfl) ⟨1976541, by rfl⟩ : syracuseStep 5270777 = 3953083) B3953083
theorem B4222201 : Blo 1387513 4222201 := bstep (se 2 (by rfl) ⟨1583325, by rfl⟩ : syracuseStep 4222201 = 3166651) B3166651
theorem B1387823 : Blo 1387513 1387823 := bstep (se 1 (by rfl) ⟨1040867, by rfl⟩ : syracuseStep 1387823 = 2081735) B2081735
theorem B13348151 : Blo 1387513 13348151 := bstep (se 1 (by rfl) ⟨10011113, by rfl⟩ : syracuseStep 13348151 = 20022227) B20022227
theorem B8899895 : Blo 1387513 8899895 := bstep (se 1 (by rfl) ⟨6674921, by rfl⟩ : syracuseStep 8899895 = 13349843) B13349843
theorem B1387935 : Blo 1387513 1387935 := bstep (se 1 (by rfl) ⟨1040951, by rfl⟩ : syracuseStep 1387935 = 2081903) B2081903
theorem B1388063 : Blo 1387513 1388063 := bstep (se 1 (by rfl) ⟨1041047, by rfl⟩ : syracuseStep 1388063 = 2082095) B2082095
theorem B14257721 : Blo 1387513 14257721 := bstep (se 2 (by rfl) ⟨5346645, by rfl⟩ : syracuseStep 14257721 = 10693291) B10693291
theorem B14241383 : Blo 1387513 14241383 := bstep (se 1 (by rfl) ⟨10681037, by rfl⟩ : syracuseStep 14241383 = 21362075) B21362075
theorem B2002591 : Blo 1387513 2002591 := bstep (se 1 (by rfl) ⟨1501943, by rfl⟩ : syracuseStep 2002591 = 3003887) B3003887
theorem B1388199 : Blo 1387513 1388199 := bstep (se 1 (by rfl) ⟨1041149, by rfl⟩ : syracuseStep 1388199 = 2082299) B2082299
theorem B1388223 : Blo 1387513 1388223 := bstep (se 1 (by rfl) ⟨1041167, by rfl⟩ : syracuseStep 1388223 = 2082335) B2082335
theorem B1388319 : Blo 1387513 1388319 := bstep (se 1 (by rfl) ⟨1041239, by rfl⟩ : syracuseStep 1388319 = 2082479) B2082479
theorem B1756991 : Blo 1387513 1756991 := bstep (se 1 (by rfl) ⟨1317743, by rfl⟩ : syracuseStep 1756991 = 2635487) B2635487
theorem B1388399 : Blo 1387513 1388399 := bstep (se 1 (by rfl) ⟨1041299, by rfl⟩ : syracuseStep 1388399 = 2082599) B2082599
theorem B15020129 : Blo 1387513 15020129 := bstep (se 2 (by rfl) ⟨5632548, by rfl⟩ : syracuseStep 15020129 = 11265097) B11265097
theorem B11251835 : Blo 1387513 11251835 := bstep (se 1 (by rfl) ⟨8438876, by rfl⟩ : syracuseStep 11251835 = 16877753) B16877753
theorem B1388767 : Blo 1387513 1388767 := bstep (se 1 (by rfl) ⟨1041575, by rfl⟩ : syracuseStep 1388767 = 2083151) B2083151
theorem B1388799 : Blo 1387513 1388799 := bstep (se 1 (by rfl) ⟨1041599, by rfl⟩ : syracuseStep 1388799 = 2083199) B2083199
theorem B1388827 : Blo 1387513 1388827 := bstep (se 1 (by rfl) ⟨1041620, by rfl⟩ : syracuseStep 1388827 = 2083241) B2083241
theorem B5927249 : Blo 1387513 5927249 := bstep (se 2 (by rfl) ⟨2222718, by rfl⟩ : syracuseStep 5927249 = 4445437) B4445437
theorem B1389083 : Blo 1387513 1389083 := bstep (se 1 (by rfl) ⟨1041812, by rfl⟩ : syracuseStep 1389083 = 2083625) B2083625
theorem B1389223 : Blo 1387513 1389223 := bstep (se 1 (by rfl) ⟨1041917, by rfl⟩ : syracuseStep 1389223 = 2083835) B2083835
theorem B1389263 : Blo 1387513 1389263 := bstep (se 1 (by rfl) ⟨1041947, by rfl⟩ : syracuseStep 1389263 = 2083895) B2083895
theorem B1389343 : Blo 1387513 1389343 := bstep (se 1 (by rfl) ⟨1042007, by rfl⟩ : syracuseStep 1389343 = 2084015) B2084015
theorem B10539881 : Blo 1387513 10539881 := bstep (se 2 (by rfl) ⟨3952455, by rfl⟩ : syracuseStep 10539881 = 7904911) B7904911
theorem B3126185 : Blo 1387513 3126185 := bstep (se 2 (by rfl) ⟨1172319, by rfl⟩ : syracuseStep 3126185 = 2344639) B2344639
theorem B1561567 : Blo 1387513 1561567 := bstep (se 1 (by rfl) ⟨1171175, by rfl⟩ : syracuseStep 1561567 = 2342351) B2342351
theorem B4117711 : Blo 1387513 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B23737697 : Blo 1387513 23737697 := bstep (se 2 (by rfl) ⟨8901636, by rfl⟩ : syracuseStep 23737697 = 17803273) B17803273
theorem B18044315 : Blo 1387513 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B4445693 : Blo 1387513 4445693 := bstep (se 3 (by rfl) ⟨833567, by rfl⟩ : syracuseStep 4445693 = 1667135) B1667135
theorem B1562143 : Blo 1387513 1562143 := bstep (se 1 (by rfl) ⟨1171607, by rfl⟩ : syracuseStep 1562143 = 2343215) B2343215
theorem B5346953 : Blo 1387513 5346953 := bstep (se 2 (by rfl) ⟨2005107, by rfl⟩ : syracuseStep 5346953 = 4010215) B4010215
theorem B3954575 : Blo 1387513 3954575 := bstep (se 1 (by rfl) ⟨2965931, by rfl⟩ : syracuseStep 3954575 = 5931863) B5931863
theorem B11261855 : Blo 1387513 11261855 := bstep (se 1 (by rfl) ⟨8446391, by rfl⟩ : syracuseStep 11261855 = 16892783) B16892783
theorem B4683743 : Blo 1387513 4683743 := bstep (se 1 (by rfl) ⟨3512807, by rfl⟩ : syracuseStep 4683743 = 7025615) B7025615
theorem B17799173 : Blo 1387513 17799173 := bstep (se 4 (by rfl) ⟨1668672, by rfl⟩ : syracuseStep 17799173 = 3337345) B3337345
theorem B34224227 : Blo 1387513 34224227 := bstep (se 1 (by rfl) ⟨25668170, by rfl⟩ : syracuseStep 34224227 = 51336341) B51336341
theorem B1563007 : Blo 1387513 1563007 := bstep (se 1 (by rfl) ⟨1172255, by rfl⟩ : syracuseStep 1563007 = 2344511) B2344511
theorem B6674845 : Blo 1387513 6674845 := bstep (se 3 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 6674845 = 2503067) B2503067
theorem B5274193 : Blo 1387513 5274193 := bstep (se 2 (by rfl) ⟨1977822, by rfl⟩ : syracuseStep 5274193 = 3955645) B3955645
theorem B7903979 : Blo 1387513 7903979 := bstep (se 1 (by rfl) ⟨5927984, by rfl⟩ : syracuseStep 7903979 = 11855969) B11855969
theorem B3955817 : Blo 1387513 3955817 := bstep (se 2 (by rfl) ⟨1483431, by rfl⟩ : syracuseStep 3955817 = 2966863) B2966863
theorem B2637127 : Blo 1387513 2637127 := bstep (se 1 (by rfl) ⟨1977845, by rfl⟩ : syracuseStep 2637127 = 3955691) B3955691
theorem B5274953 : Blo 1387513 5274953 := bstep (se 2 (by rfl) ⟨1978107, by rfl⟩ : syracuseStep 5274953 = 3956215) B3956215
theorem B15826589 : Blo 1387513 15826589 := bstep (se 3 (by rfl) ⟨2967485, by rfl⟩ : syracuseStep 15826589 = 5934971) B5934971
theorem B4005551 : Blo 1387513 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B36568759 : Blo 1387513 36568759 := bstep (se 1 (by rfl) ⟨27426569, by rfl⟩ : syracuseStep 36568759 = 54853139) B54853139
theorem B3006191 : Blo 1387513 3006191 := bstep (se 1 (by rfl) ⟨2254643, by rfl⟩ : syracuseStep 3006191 = 4509287) B4509287
theorem B9494417 : Blo 1387513 9494417 := bstep (se 2 (by rfl) ⟨3560406, by rfl⟩ : syracuseStep 9494417 = 7120813) B7120813
theorem B23715827 : Blo 1387513 23715827 := bstep (se 1 (by rfl) ⟨17786870, by rfl⟩ : syracuseStep 23715827 = 35573741) B35573741
theorem B2343323 : Blo 1387513 2343323 := bstep (se 1 (by rfl) ⟨1757492, by rfl⟩ : syracuseStep 2343323 = 3514985) B3514985
theorem B6668831 : Blo 1387513 6668831 := bstep (se 1 (by rfl) ⟨5001623, by rfl⟩ : syracuseStep 6668831 = 10003247) B10003247
theorem B5931623 : Blo 1387513 5931623 := bstep (se 1 (by rfl) ⟨4448717, by rfl⟩ : syracuseStep 5931623 = 8897435) B8897435
theorem B38544005 : Blo 1387513 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B35586863 : Blo 1387513 35586863 := bstep (se 1 (by rfl) ⟨26690147, by rfl⟩ : syracuseStep 35586863 = 53380295) B53380295
theorem B2081591 : Blo 1387513 2081591 := bstep (se 1 (by rfl) ⟨1561193, by rfl⟩ : syracuseStep 2081591 = 3122387) B3122387
theorem B2081759 : Blo 1387513 2081759 := bstep (se 1 (by rfl) ⟨1561319, by rfl⟩ : syracuseStep 2081759 = 3122639) B3122639
theorem B2081771 : Blo 1387513 2081771 := bstep (se 1 (by rfl) ⟨1561328, by rfl⟩ : syracuseStep 2081771 = 3122657) B3122657
theorem B3564635 : Blo 1387513 3564635 := bstep (se 1 (by rfl) ⟨2673476, by rfl⟩ : syracuseStep 3564635 = 5346953) B5346953
theorem B5932223 : Blo 1387513 5932223 := bstep (se 1 (by rfl) ⟨4449167, by rfl⟩ : syracuseStep 5932223 = 8898335) B8898335
theorem B11257055 : Blo 1387513 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B2082023 : Blo 1387513 2082023 := bstep (se 1 (by rfl) ⟨1561517, by rfl⟩ : syracuseStep 2082023 = 3123035) B3123035
theorem B2082089 : Blo 1387513 2082089 := bstep (se 2 (by rfl) ⟨780783, by rfl⟩ : syracuseStep 2082089 = 1561567) B1561567
theorem B3122495 : Blo 1387513 3122495 := bstep (se 1 (by rfl) ⟨2341871, by rfl⟩ : syracuseStep 3122495 = 4683743) B4683743
theorem B22816151 : Blo 1387513 22816151 := bstep (se 1 (by rfl) ⟨17112113, by rfl⟩ : syracuseStep 22816151 = 34224227) B34224227
theorem B5490281 : Blo 1387513 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B5629601 : Blo 1387513 5629601 := bstep (se 2 (by rfl) ⟨2111100, by rfl⟩ : syracuseStep 5629601 = 4222201) B4222201
theorem B3516169 : Blo 1387513 3516169 := bstep (se 2 (by rfl) ⟨1318563, by rfl⟩ : syracuseStep 3516169 = 2637127) B2637127
theorem B5269319 : Blo 1387513 5269319 := bstep (se 1 (by rfl) ⟨3951989, by rfl⟩ : syracuseStep 5269319 = 7903979) B7903979
theorem B2082671 : Blo 1387513 2082671 := bstep (se 1 (by rfl) ⟨1562003, by rfl⟩ : syracuseStep 2082671 = 3124007) B3124007
theorem B2082857 : Blo 1387513 2082857 := bstep (se 2 (by rfl) ⟨781071, by rfl⟩ : syracuseStep 2082857 = 1562143) B1562143
theorem B8898767 : Blo 1387513 8898767 := bstep (se 1 (by rfl) ⟨6674075, by rfl⟩ : syracuseStep 8898767 = 13348151) B13348151
theorem B5933263 : Blo 1387513 5933263 := bstep (se 1 (by rfl) ⟨4449947, by rfl⟩ : syracuseStep 5933263 = 8899895) B8899895
theorem B3516635 : Blo 1387513 3516635 := bstep (se 1 (by rfl) ⟨2637476, by rfl⟩ : syracuseStep 3516635 = 5274953) B5274953
theorem B9505147 : Blo 1387513 9505147 := bstep (se 1 (by rfl) ⟨7128860, by rfl⟩ : syracuseStep 9505147 = 14257721) B14257721
theorem B10013419 : Blo 1387513 10013419 := bstep (se 1 (by rfl) ⟨7510064, by rfl⟩ : syracuseStep 10013419 = 15020129) B15020129
theorem B3124079 : Blo 1387513 3124079 := bstep (se 1 (by rfl) ⟨2343059, by rfl⟩ : syracuseStep 3124079 = 4686119) B4686119
theorem B3951499 : Blo 1387513 3951499 := bstep (se 1 (by rfl) ⟨2963624, by rfl⟩ : syracuseStep 3951499 = 5927249) B5927249
theorem B3124331 : Blo 1387513 3124331 := bstep (se 1 (by rfl) ⟨2343248, by rfl⟩ : syracuseStep 3124331 = 4686497) B4686497
theorem B6335597 : Blo 1387513 6335597 := bstep (se 3 (by rfl) ⟨1187924, by rfl⟩ : syracuseStep 6335597 = 2375849) B2375849
theorem B1387687 : Blo 1387513 1387687 := bstep (se 1 (by rfl) ⟨1040765, by rfl⟩ : syracuseStep 1387687 = 2081531) B2081531
theorem B2084009 : Blo 1387513 2084009 := bstep (se 2 (by rfl) ⟨781503, by rfl⟩ : syracuseStep 2084009 = 1563007) B1563007
theorem B8899793 : Blo 1387513 8899793 := bstep (se 2 (by rfl) ⟨3337422, by rfl⟩ : syracuseStep 8899793 = 6674845) B6674845
theorem B2084123 : Blo 1387513 2084123 := bstep (se 1 (by rfl) ⟨1563092, by rfl⟩ : syracuseStep 2084123 = 3126185) B3126185
theorem B7032257 : Blo 1387513 7032257 := bstep (se 2 (by rfl) ⟨2637096, by rfl⟩ : syracuseStep 7032257 = 5274193) B5274193
theorem B1387983 : Blo 1387513 1387983 := bstep (se 1 (by rfl) ⟨1040987, by rfl⟩ : syracuseStep 1387983 = 2081975) B2081975
theorem B1388079 : Blo 1387513 1388079 := bstep (se 1 (by rfl) ⟨1041059, by rfl⟩ : syracuseStep 1388079 = 2082119) B2082119
theorem B12029543 : Blo 1387513 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B1388143 : Blo 1387513 1388143 := bstep (se 1 (by rfl) ⟨1041107, by rfl⟩ : syracuseStep 1388143 = 2082215) B2082215
theorem B1388263 : Blo 1387513 1388263 := bstep (se 1 (by rfl) ⟨1041197, by rfl⟩ : syracuseStep 1388263 = 2082395) B2082395
theorem B26685227 : Blo 1387513 26685227 := bstep (se 1 (by rfl) ⟨20013920, by rfl⟩ : syracuseStep 26685227 = 40027841) B40027841
theorem B7909285 : Blo 1387513 7909285 := bstep (se 4 (by rfl) ⟨741495, by rfl⟩ : syracuseStep 7909285 = 1482991) B1482991
theorem B7507903 : Blo 1387513 7507903 := bstep (se 1 (by rfl) ⟨5630927, by rfl⟩ : syracuseStep 7507903 = 11261855) B11261855
theorem B11866115 : Blo 1387513 11866115 := bstep (se 1 (by rfl) ⟨8899586, by rfl⟩ : syracuseStep 11866115 = 17799173) B17799173
theorem B1388575 : Blo 1387513 1388575 := bstep (se 1 (by rfl) ⟨1041431, by rfl⟩ : syracuseStep 1388575 = 2082863) B2082863
theorem B1388751 : Blo 1387513 1388751 := bstep (se 1 (by rfl) ⟨1041563, by rfl⟩ : syracuseStep 1388751 = 2083127) B2083127
theorem B1388871 : Blo 1387513 1388871 := bstep (se 1 (by rfl) ⟨1041653, by rfl⟩ : syracuseStep 1388871 = 2083307) B2083307
theorem B1389031 : Blo 1387513 1389031 := bstep (se 1 (by rfl) ⟨1041773, by rfl⟩ : syracuseStep 1389031 = 2083547) B2083547
theorem B1389055 : Blo 1387513 1389055 := bstep (se 1 (by rfl) ⟨1041791, by rfl⟩ : syracuseStep 1389055 = 2083583) B2083583
theorem B8016509 : Blo 1387513 8016509 := bstep (se 3 (by rfl) ⟨1503095, by rfl⟩ : syracuseStep 8016509 = 3006191) B3006191
theorem B24360041 : Blo 1387513 24360041 := bstep (se 2 (by rfl) ⟨9135015, by rfl⟩ : syracuseStep 24360041 = 18270031) B18270031
theorem B6329611 : Blo 1387513 6329611 := bstep (se 1 (by rfl) ⟨4747208, by rfl⟩ : syracuseStep 6329611 = 9494417) B9494417
theorem B7501223 : Blo 1387513 7501223 := bstep (se 1 (by rfl) ⟨5625917, by rfl⟩ : syracuseStep 7501223 = 11251835) B11251835
theorem B3003817 : Blo 1387513 3003817 := bstep (se 2 (by rfl) ⟨1126431, by rfl⟩ : syracuseStep 3003817 = 2252863) B2252863
theorem B8443547 : Blo 1387513 8443547 := bstep (se 1 (by rfl) ⟨6332660, by rfl⟩ : syracuseStep 8443547 = 12665321) B12665321
theorem B7026587 : Blo 1387513 7026587 := bstep (se 1 (by rfl) ⟨5269940, by rfl⟩ : syracuseStep 7026587 = 10539881) B10539881
theorem B2635753 : Blo 1387513 2635753 := bstep (se 2 (by rfl) ⟨988407, by rfl⟩ : syracuseStep 2635753 = 1976815) B1976815
theorem B50640977 : Blo 1387513 50640977 := bstep (se 2 (by rfl) ⟨18990366, by rfl⟩ : syracuseStep 50640977 = 37980733) B37980733
theorem B8902867 : Blo 1387513 8902867 := bstep (se 1 (by rfl) ⟨6677150, by rfl⟩ : syracuseStep 8902867 = 13354301) B13354301
theorem B3512555 : Blo 1387513 3512555 := bstep (se 1 (by rfl) ⟨2634416, by rfl⟩ : syracuseStep 3512555 = 5268833) B5268833
theorem B15825131 : Blo 1387513 15825131 := bstep (se 1 (by rfl) ⟨11868848, by rfl⟩ : syracuseStep 15825131 = 23737697) B23737697
theorem B1562863 : Blo 1387513 1562863 := bstep (se 1 (by rfl) ⟨1172147, by rfl⟩ : syracuseStep 1562863 = 2344295) B2344295
theorem B10541339 : Blo 1387513 10541339 := bstep (se 1 (by rfl) ⟨7906004, by rfl⟩ : syracuseStep 10541339 = 15812009) B15812009
theorem B2963795 : Blo 1387513 2963795 := bstep (se 1 (by rfl) ⟨2222846, by rfl⟩ : syracuseStep 2963795 = 4445693) B4445693
theorem B7510411 : Blo 1387513 7510411 := bstep (se 1 (by rfl) ⟨5632808, by rfl⟩ : syracuseStep 7510411 = 11265617) B11265617
theorem B2636383 : Blo 1387513 2636383 := bstep (se 1 (by rfl) ⟨1977287, by rfl⟩ : syracuseStep 2636383 = 3954575) B3954575
theorem B9624683 : Blo 1387513 9624683 := bstep (se 1 (by rfl) ⟨7218512, by rfl⟩ : syracuseStep 9624683 = 14437025) B14437025
theorem B10681469 : Blo 1387513 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B2637211 : Blo 1387513 2637211 := bstep (se 1 (by rfl) ⟨1977908, by rfl⟩ : syracuseStep 2637211 = 3955817) B3955817
theorem B3513851 : Blo 1387513 3513851 := bstep (se 1 (by rfl) ⟨2635388, by rfl⟩ : syracuseStep 3513851 = 5270777) B5270777
theorem B4685309 : Blo 1387513 4685309 := bstep (se 3 (by rfl) ⟨878495, by rfl⟩ : syracuseStep 4685309 = 1756991) B1756991
theorem B2670121 : Blo 1387513 2670121 := bstep (se 2 (by rfl) ⟨1001295, by rfl⟩ : syracuseStep 2670121 = 2002591) B2002591
theorem B48758345 : Blo 1387513 48758345 := bstep (se 2 (by rfl) ⟨18284379, by rfl⟩ : syracuseStep 48758345 = 36568759) B36568759
theorem B9494255 : Blo 1387513 9494255 := bstep (se 1 (by rfl) ⟨7120691, by rfl⟩ : syracuseStep 9494255 = 14241383) B14241383
theorem B10551059 : Blo 1387513 10551059 := bstep (se 1 (by rfl) ⟨7913294, by rfl⟩ : syracuseStep 10551059 = 15826589) B15826589
theorem B28884845 : Blo 1387513 28884845 := bstep (se 3 (by rfl) ⟨5415908, by rfl⟩ : syracuseStep 28884845 = 10831817) B10831817
theorem B3563489 : Blo 1387513 3563489 := bstep (se 2 (by rfl) ⟨1336308, by rfl⟩ : syracuseStep 3563489 = 2672617) B2672617
theorem B15810551 : Blo 1387513 15810551 := bstep (se 1 (by rfl) ⟨11857913, by rfl⟩ : syracuseStep 15810551 = 23715827) B23715827
theorem B11870489 : Blo 1387513 11870489 := bstep (se 2 (by rfl) ⟨4451433, by rfl⟩ : syracuseStep 11870489 = 8902867) B8902867
theorem B25665821 : Blo 1387513 25665821 := bstep (se 3 (by rfl) ⟨4812341, by rfl⟩ : syracuseStep 25665821 = 9624683) B9624683
theorem B12673529 : Blo 1387513 12673529 := bstep (se 2 (by rfl) ⟨4752573, by rfl⟩ : syracuseStep 12673529 = 9505147) B9505147
theorem B23724575 : Blo 1387513 23724575 := bstep (se 1 (by rfl) ⟨17793431, by rfl⟩ : syracuseStep 23724575 = 35586863) B35586863
theorem B3515177 : Blo 1387513 3515177 := bstep (se 2 (by rfl) ⟨1318191, by rfl⟩ : syracuseStep 3515177 = 2636383) B2636383
theorem B7504703 : Blo 1387513 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B2081663 : Blo 1387513 2081663 := bstep (se 1 (by rfl) ⟨1561247, by rfl⟩ : syracuseStep 2081663 = 3122495) B3122495
theorem B5629031 : Blo 1387513 5629031 := bstep (se 1 (by rfl) ⟨4221773, by rfl⟩ : syracuseStep 5629031 = 8443547) B8443547
theorem B3753067 : Blo 1387513 3753067 := bstep (se 1 (by rfl) ⟨2814800, by rfl⟩ : syracuseStep 3753067 = 5629601) B5629601
theorem B5268665 : Blo 1387513 5268665 := bstep (se 2 (by rfl) ⟨1975749, by rfl⟩ : syracuseStep 5268665 = 3951499) B3951499
theorem B33760651 : Blo 1387513 33760651 := bstep (se 1 (by rfl) ⟨25320488, by rfl⟩ : syracuseStep 33760651 = 50640977) B50640977
theorem B5932511 : Blo 1387513 5932511 := bstep (se 1 (by rfl) ⟨4449383, by rfl⟩ : syracuseStep 5932511 = 8898767) B8898767
theorem B2344423 : Blo 1387513 2344423 := bstep (se 1 (by rfl) ⟨1758317, by rfl⟩ : syracuseStep 2344423 = 3516635) B3516635
theorem B14640749 : Blo 1387513 14640749 := bstep (se 3 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 14640749 = 5490281) B5490281
theorem B8439481 : Blo 1387513 8439481 := bstep (se 2 (by rfl) ⟨3164805, by rfl⟩ : syracuseStep 8439481 = 6329611) B6329611
theorem B3516281 : Blo 1387513 3516281 := bstep (se 2 (by rfl) ⟨1318605, by rfl⟩ : syracuseStep 3516281 = 2637211) B2637211
theorem B2082719 : Blo 1387513 2082719 := bstep (se 1 (by rfl) ⟨1562039, by rfl⟩ : syracuseStep 2082719 = 3124079) B3124079
theorem B2082887 : Blo 1387513 2082887 := bstep (se 1 (by rfl) ⟨1562165, by rfl⟩ : syracuseStep 2082887 = 3124331) B3124331
theorem B7120979 : Blo 1387513 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B5933195 : Blo 1387513 5933195 := bstep (se 1 (by rfl) ⟨4449896, by rfl⟩ : syracuseStep 5933195 = 8899793) B8899793
theorem B4688171 : Blo 1387513 4688171 := bstep (se 1 (by rfl) ⟨3516128, by rfl⟩ : syracuseStep 4688171 = 7032257) B7032257
theorem B3123539 : Blo 1387513 3123539 := bstep (se 1 (by rfl) ⟨2342654, by rfl⟩ : syracuseStep 3123539 = 4685309) B4685309
theorem B4688225 : Blo 1387513 4688225 := bstep (se 2 (by rfl) ⟨1758084, by rfl⟩ : syracuseStep 4688225 = 3516169) B3516169
theorem B10545713 : Blo 1387513 10545713 := bstep (se 2 (by rfl) ⟨3954642, by rfl⟩ : syracuseStep 10545713 = 7909285) B7909285
theorem B9505693 : Blo 1387513 9505693 := bstep (se 3 (by rfl) ⟨1782317, by rfl⟩ : syracuseStep 9505693 = 3564635) B3564635
theorem B16894925 : Blo 1387513 16894925 := bstep (se 3 (by rfl) ⟨3167798, by rfl⟩ : syracuseStep 16894925 = 6335597) B6335597
theorem B2083817 : Blo 1387513 2083817 := bstep (se 2 (by rfl) ⟨781431, by rfl⟩ : syracuseStep 2083817 = 1562863) B1562863
theorem B10013881 : Blo 1387513 10013881 := bstep (se 2 (by rfl) ⟨3755205, by rfl⟩ : syracuseStep 10013881 = 7510411) B7510411
theorem B1387727 : Blo 1387513 1387727 := bstep (se 1 (by rfl) ⟨1040795, by rfl⟩ : syracuseStep 1387727 = 2081591) B2081591
theorem B1387839 : Blo 1387513 1387839 := bstep (se 1 (by rfl) ⟨1040879, by rfl⟩ : syracuseStep 1387839 = 2081759) B2081759
theorem B1387847 : Blo 1387513 1387847 := bstep (se 1 (by rfl) ⟨1040885, by rfl⟩ : syracuseStep 1387847 = 2081771) B2081771
theorem B16240027 : Blo 1387513 16240027 := bstep (se 1 (by rfl) ⟨12180020, by rfl⟩ : syracuseStep 16240027 = 24360041) B24360041
theorem B1388015 : Blo 1387513 1388015 := bstep (se 1 (by rfl) ⟨1041011, by rfl⟩ : syracuseStep 1388015 = 2082023) B2082023
theorem B1388059 : Blo 1387513 1388059 := bstep (se 1 (by rfl) ⟨1041044, by rfl⟩ : syracuseStep 1388059 = 2082089) B2082089
theorem B5000815 : Blo 1387513 5000815 := bstep (se 1 (by rfl) ⟨3750611, by rfl⟩ : syracuseStep 5000815 = 7501223) B7501223
theorem B1388447 : Blo 1387513 1388447 := bstep (se 1 (by rfl) ⟨1041335, by rfl⟩ : syracuseStep 1388447 = 2082671) B2082671
theorem B1388571 : Blo 1387513 1388571 := bstep (se 1 (by rfl) ⟨1041428, by rfl⟩ : syracuseStep 1388571 = 2082857) B2082857
theorem B21377357 : Blo 1387513 21377357 := bstep (se 3 (by rfl) ⟨4008254, by rfl⟩ : syracuseStep 21377357 = 8016509) B8016509
theorem B3560161 : Blo 1387513 3560161 := bstep (se 2 (by rfl) ⟨1335060, by rfl⟩ : syracuseStep 3560161 = 2670121) B2670121
theorem B1389339 : Blo 1387513 1389339 := bstep (se 1 (by rfl) ⟨1042004, by rfl⟩ : syracuseStep 1389339 = 2084009) B2084009
theorem B1389415 : Blo 1387513 1389415 := bstep (se 1 (by rfl) ⟨1042061, by rfl⟩ : syracuseStep 1389415 = 2084123) B2084123
theorem B6329503 : Blo 1387513 6329503 := bstep (se 1 (by rfl) ⟨4747127, by rfl⟩ : syracuseStep 6329503 = 9494255) B9494255
theorem B7034039 : Blo 1387513 7034039 := bstep (se 1 (by rfl) ⟨5275529, by rfl⟩ : syracuseStep 7034039 = 10551059) B10551059
theorem B17790151 : Blo 1387513 17790151 := bstep (se 1 (by rfl) ⟨13342613, by rfl⟩ : syracuseStep 17790151 = 26685227) B26685227
theorem B19256563 : Blo 1387513 19256563 := bstep (se 1 (by rfl) ⟨14442422, by rfl⟩ : syracuseStep 19256563 = 28884845) B28884845
theorem B10540367 : Blo 1387513 10540367 := bstep (se 1 (by rfl) ⟨7905275, by rfl⟩ : syracuseStep 10540367 = 15810551) B15810551
theorem B7910743 : Blo 1387513 7910743 := bstep (se 1 (by rfl) ⟨5933057, by rfl⟩ : syracuseStep 7910743 = 11866115) B11866115
theorem B1562215 : Blo 1387513 1562215 := bstep (se 1 (by rfl) ⟨1171661, by rfl⟩ : syracuseStep 1562215 = 2343323) B2343323
theorem B7911017 : Blo 1387513 7911017 := bstep (se 2 (by rfl) ⟨2966631, by rfl⟩ : syracuseStep 7911017 = 5933263) B5933263
theorem B4445887 : Blo 1387513 4445887 := bstep (se 1 (by rfl) ⟨3334415, by rfl⟩ : syracuseStep 4445887 = 6668831) B6668831
theorem B3954415 : Blo 1387513 3954415 := bstep (se 1 (by rfl) ⟨2965811, by rfl⟩ : syracuseStep 3954415 = 5931623) B5931623
theorem B25696003 : Blo 1387513 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B3954815 : Blo 1387513 3954815 := bstep (se 1 (by rfl) ⟨2966111, by rfl⟩ : syracuseStep 3954815 = 5932223) B5932223
theorem B7903453 : Blo 1387513 7903453 := bstep (se 3 (by rfl) ⟨1481897, by rfl⟩ : syracuseStep 7903453 = 2963795) B2963795
theorem B15210767 : Blo 1387513 15210767 := bstep (se 1 (by rfl) ⟨11408075, by rfl⟩ : syracuseStep 15210767 = 22816151) B22816151
theorem B13351225 : Blo 1387513 13351225 := bstep (se 2 (by rfl) ⟨5006709, by rfl⟩ : syracuseStep 13351225 = 10013419) B10013419
theorem B3512879 : Blo 1387513 3512879 := bstep (se 1 (by rfl) ⟨2634659, by rfl⟩ : syracuseStep 3512879 = 5269319) B5269319
theorem B4684391 : Blo 1387513 4684391 := bstep (se 1 (by rfl) ⟨3513293, by rfl⟩ : syracuseStep 4684391 = 7026587) B7026587
theorem B2341703 : Blo 1387513 2341703 := bstep (se 1 (by rfl) ⟨1756277, by rfl⟩ : syracuseStep 2341703 = 3512555) B3512555
theorem B10550087 : Blo 1387513 10550087 := bstep (se 1 (by rfl) ⟨7912565, by rfl⟩ : syracuseStep 10550087 = 15825131) B15825131
theorem B7027559 : Blo 1387513 7027559 := bstep (se 1 (by rfl) ⟨5270669, by rfl⟩ : syracuseStep 7027559 = 10541339) B10541339
theorem B4005089 : Blo 1387513 4005089 := bstep (se 2 (by rfl) ⟨1501908, by rfl⟩ : syracuseStep 4005089 = 3003817) B3003817
theorem B2342567 : Blo 1387513 2342567 := bstep (se 1 (by rfl) ⟨1756925, by rfl⟩ : syracuseStep 2342567 = 3513851) B3513851
theorem B32505563 : Blo 1387513 32505563 := bstep (se 1 (by rfl) ⟨24379172, by rfl⟩ : syracuseStep 32505563 = 48758345) B48758345
theorem B8019695 : Blo 1387513 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B10010537 : Blo 1387513 10010537 := bstep (se 2 (by rfl) ⟨3753951, by rfl⟩ : syracuseStep 10010537 = 7507903) B7507903
theorem B3514337 : Blo 1387513 3514337 := bstep (se 2 (by rfl) ⟨1317876, by rfl⟩ : syracuseStep 3514337 = 2635753) B2635753
theorem B2375659 : Blo 1387513 2375659 := bstep (se 1 (by rfl) ⟨1781744, by rfl⟩ : syracuseStep 2375659 = 3563489) B3563489
theorem B7913659 : Blo 1387513 7913659 := bstep (se 1 (by rfl) ⟨5935244, by rfl⟩ : syracuseStep 7913659 = 11870489) B11870489
theorem B17801633 : Blo 1387513 17801633 := bstep (se 2 (by rfl) ⟨6675612, by rfl⟩ : syracuseStep 17801633 = 13351225) B13351225
theorem B2343451 : Blo 1387513 2343451 := bstep (se 1 (by rfl) ⟨1757588, by rfl⟩ : syracuseStep 2343451 = 3515177) B3515177
theorem B3752687 : Blo 1387513 3752687 := bstep (se 1 (by rfl) ⟨2814515, by rfl⟩ : syracuseStep 3752687 = 5629031) B5629031
theorem B2344187 : Blo 1387513 2344187 := bstep (se 1 (by rfl) ⟨1758140, by rfl⟩ : syracuseStep 2344187 = 3516281) B3516281
theorem B8439337 : Blo 1387513 8439337 := bstep (se 2 (by rfl) ⟨3164751, by rfl⟩ : syracuseStep 8439337 = 6329503) B6329503
theorem B2082359 : Blo 1387513 2082359 := bstep (se 1 (by rfl) ⟨1561769, by rfl⟩ : syracuseStep 2082359 = 3123539) B3123539
theorem B25675417 : Blo 1387513 25675417 := bstep (se 2 (by rfl) ⟨9628281, by rfl⟩ : syracuseStep 25675417 = 19256563) B19256563
theorem B7030475 : Blo 1387513 7030475 := bstep (se 1 (by rfl) ⟨5272856, by rfl⟩ : syracuseStep 7030475 = 10545713) B10545713
theorem B3122927 : Blo 1387513 3122927 := bstep (se 1 (by rfl) ⟨2342195, by rfl⟩ : syracuseStep 3122927 = 4684391) B4684391
theorem B21653369 : Blo 1387513 21653369 := bstep (se 2 (by rfl) ⟨8120013, by rfl⟩ : syracuseStep 21653369 = 16240027) B16240027
theorem B2082953 : Blo 1387513 2082953 := bstep (se 2 (by rfl) ⟨781107, by rfl⟩ : syracuseStep 2082953 = 1562215) B1562215
theorem B34261337 : Blo 1387513 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B21670375 : Blo 1387513 21670375 := bstep (se 1 (by rfl) ⟨16252781, by rfl⟩ : syracuseStep 21670375 = 32505563) B32505563
theorem B10537937 : Blo 1387513 10537937 := bstep (se 2 (by rfl) ⟨3951726, by rfl⟩ : syracuseStep 10537937 = 7903453) B7903453
theorem B8449019 : Blo 1387513 8449019 := bstep (se 1 (by rfl) ⟨6336764, by rfl⟩ : syracuseStep 8449019 = 12673529) B12673529
theorem B1387775 : Blo 1387513 1387775 := bstep (se 1 (by rfl) ⟨1040831, by rfl⟩ : syracuseStep 1387775 = 2081663) B2081663
theorem B40562045 : Blo 1387513 40562045 := bstep (se 3 (by rfl) ⟨7605383, by rfl⟩ : syracuseStep 40562045 = 15210767) B15210767
theorem B4689359 : Blo 1387513 4689359 := bstep (se 1 (by rfl) ⟨3517019, by rfl⟩ : syracuseStep 4689359 = 7034039) B7034039
theorem B4746881 : Blo 1387513 4746881 := bstep (se 2 (by rfl) ⟨1780080, by rfl⟩ : syracuseStep 4746881 = 3560161) B3560161
theorem B45010565 : Blo 1387513 45010565 := bstep (se 4 (by rfl) ⟨4219740, by rfl⟩ : syracuseStep 45010565 = 8439481) B8439481
theorem B9760499 : Blo 1387513 9760499 := bstep (se 1 (by rfl) ⟨7320374, by rfl⟩ : syracuseStep 9760499 = 14640749) B14640749
theorem B1388479 : Blo 1387513 1388479 := bstep (se 1 (by rfl) ⟨1041359, by rfl⟩ : syracuseStep 1388479 = 2082719) B2082719
theorem B1388591 : Blo 1387513 1388591 := bstep (se 1 (by rfl) ⟨1041443, by rfl⟩ : syracuseStep 1388591 = 2082887) B2082887
theorem B4747319 : Blo 1387513 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B3125447 : Blo 1387513 3125447 := bstep (se 1 (by rfl) ⟨2344085, by rfl⟩ : syracuseStep 3125447 = 4688171) B4688171
theorem B3125483 : Blo 1387513 3125483 := bstep (se 1 (by rfl) ⟨2344112, by rfl⟩ : syracuseStep 3125483 = 4688225) B4688225
theorem B23720201 : Blo 1387513 23720201 := bstep (se 2 (by rfl) ⟨8895075, by rfl⟩ : syracuseStep 23720201 = 17790151) B17790151
theorem B10547657 : Blo 1387513 10547657 := bstep (se 2 (by rfl) ⟨3955371, by rfl⟩ : syracuseStep 10547657 = 7910743) B7910743
theorem B1561135 : Blo 1387513 1561135 := bstep (se 1 (by rfl) ⟨1170851, by rfl⟩ : syracuseStep 1561135 = 2341703) B2341703
theorem B7033391 : Blo 1387513 7033391 := bstep (se 1 (by rfl) ⟨5275043, by rfl⟩ : syracuseStep 7033391 = 10550087) B10550087
theorem B21385853 : Blo 1387513 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B3125897 : Blo 1387513 3125897 := bstep (se 2 (by rfl) ⟨1172211, by rfl⟩ : syracuseStep 3125897 = 2344423) B2344423
theorem B1389211 : Blo 1387513 1389211 := bstep (se 1 (by rfl) ⟨1041908, by rfl⟩ : syracuseStep 1389211 = 2083817) B2083817
theorem B50697029 : Blo 1387513 50697029 := bstep (se 4 (by rfl) ⟨4752846, by rfl⟩ : syracuseStep 50697029 = 9505693) B9505693
theorem B5927849 : Blo 1387513 5927849 := bstep (se 2 (by rfl) ⟨2222943, by rfl⟩ : syracuseStep 5927849 = 4445887) B4445887
theorem B5272553 : Blo 1387513 5272553 := bstep (se 2 (by rfl) ⟨1977207, by rfl⟩ : syracuseStep 5272553 = 3954415) B3954415
theorem B1561711 : Blo 1387513 1561711 := bstep (se 1 (by rfl) ⟨1171283, by rfl⟩ : syracuseStep 1561711 = 2342567) B2342567
theorem B12670181 : Blo 1387513 12670181 := bstep (se 4 (by rfl) ⟨1187829, by rfl⟩ : syracuseStep 12670181 = 2375659) B2375659
theorem B6673691 : Blo 1387513 6673691 := bstep (se 1 (by rfl) ⟨5005268, by rfl⟩ : syracuseStep 6673691 = 10010537) B10010537
theorem B17110547 : Blo 1387513 17110547 := bstep (se 1 (by rfl) ⟨12832910, by rfl⟩ : syracuseStep 17110547 = 25665821) B25665821
theorem B14251571 : Blo 1387513 14251571 := bstep (se 1 (by rfl) ⟨10688678, by rfl⟩ : syracuseStep 14251571 = 21377357) B21377357
theorem B15816383 : Blo 1387513 15816383 := bstep (se 1 (by rfl) ⟨11862287, by rfl⟩ : syracuseStep 15816383 = 23724575) B23724575
theorem B5003135 : Blo 1387513 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B3512443 : Blo 1387513 3512443 := bstep (se 1 (by rfl) ⟨2634332, by rfl⟩ : syracuseStep 3512443 = 5268665) B5268665
theorem B7026911 : Blo 1387513 7026911 := bstep (se 1 (by rfl) ⟨5270183, by rfl⟩ : syracuseStep 7026911 = 10540367) B10540367
theorem B3955007 : Blo 1387513 3955007 := bstep (se 1 (by rfl) ⟨2966255, by rfl⟩ : syracuseStep 3955007 = 5932511) B5932511
theorem B5274011 : Blo 1387513 5274011 := bstep (se 1 (by rfl) ⟨3955508, by rfl⟩ : syracuseStep 5274011 = 7911017) B7911017
theorem B2636543 : Blo 1387513 2636543 := bstep (se 1 (by rfl) ⟨1977407, by rfl⟩ : syracuseStep 2636543 = 3954815) B3954815
theorem B3955463 : Blo 1387513 3955463 := bstep (se 1 (by rfl) ⟨2966597, by rfl⟩ : syracuseStep 3955463 = 5933195) B5933195
theorem B5004089 : Blo 1387513 5004089 := bstep (se 2 (by rfl) ⟨1876533, by rfl⟩ : syracuseStep 5004089 = 3753067) B3753067
theorem B13351841 : Blo 1387513 13351841 := bstep (se 2 (by rfl) ⟨5006940, by rfl⟩ : syracuseStep 13351841 = 10013881) B10013881
theorem B2341919 : Blo 1387513 2341919 := bstep (se 1 (by rfl) ⟨1756439, by rfl⟩ : syracuseStep 2341919 = 3512879) B3512879
theorem B45014201 : Blo 1387513 45014201 := bstep (se 2 (by rfl) ⟨16880325, by rfl⟩ : syracuseStep 45014201 = 33760651) B33760651
theorem B4685039 : Blo 1387513 4685039 := bstep (se 1 (by rfl) ⟨3513779, by rfl⟩ : syracuseStep 4685039 = 7027559) B7027559
theorem B11263283 : Blo 1387513 11263283 := bstep (se 1 (by rfl) ⟨8447462, by rfl⟩ : syracuseStep 11263283 = 16894925) B16894925
theorem B6667753 : Blo 1387513 6667753 := bstep (se 2 (by rfl) ⟨2500407, by rfl⟩ : syracuseStep 6667753 = 5000815) B5000815
theorem B2670059 : Blo 1387513 2670059 := bstep (se 1 (by rfl) ⟨2002544, by rfl⟩ : syracuseStep 2670059 = 4005089) B4005089
theorem B2342891 : Blo 1387513 2342891 := bstep (se 1 (by rfl) ⟨1757168, by rfl⟩ : syracuseStep 2342891 = 3514337) B3514337
theorem B10551545 : Blo 1387513 10551545 := bstep (se 2 (by rfl) ⟨3956829, by rfl⟩ : syracuseStep 10551545 = 7913659) B7913659
theorem B28893833 : Blo 1387513 28893833 := bstep (se 2 (by rfl) ⟨10835187, by rfl⟩ : syracuseStep 28893833 = 21670375) B21670375
theorem B3515035 : Blo 1387513 3515035 := bstep (se 1 (by rfl) ⟨2636276, by rfl⟩ : syracuseStep 3515035 = 5272553) B5272553
theorem B2081513 : Blo 1387513 2081513 := bstep (se 2 (by rfl) ⟨780567, by rfl⟩ : syracuseStep 2081513 = 1561135) B1561135
theorem B8446787 : Blo 1387513 8446787 := bstep (se 1 (by rfl) ⟨6335090, by rfl⟩ : syracuseStep 8446787 = 12670181) B12670181
theorem B10544255 : Blo 1387513 10544255 := bstep (se 1 (by rfl) ⟨7908191, by rfl⟩ : syracuseStep 10544255 = 15816383) B15816383
theorem B4686983 : Blo 1387513 4686983 := bstep (se 1 (by rfl) ⟨3515237, by rfl⟩ : syracuseStep 4686983 = 7030475) B7030475
theorem B2081951 : Blo 1387513 2081951 := bstep (se 1 (by rfl) ⟨1561463, by rfl⟩ : syracuseStep 2081951 = 3122927) B3122927
theorem B14435579 : Blo 1387513 14435579 := bstep (se 1 (by rfl) ⟨10826684, by rfl⟩ : syracuseStep 14435579 = 21653369) B21653369
theorem B3335423 : Blo 1387513 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B2082281 : Blo 1387513 2082281 := bstep (se 2 (by rfl) ⟨780855, by rfl⟩ : syracuseStep 2082281 = 1561711) B1561711
theorem B3516007 : Blo 1387513 3516007 := bstep (se 1 (by rfl) ⟨2637005, by rfl⟩ : syracuseStep 3516007 = 5274011) B5274011
theorem B12658349 : Blo 1387513 12658349 := bstep (se 3 (by rfl) ⟨2373440, by rfl⟩ : syracuseStep 12658349 = 4746881) B4746881
theorem B3336059 : Blo 1387513 3336059 := bstep (se 1 (by rfl) ⟨2502044, by rfl⟩ : syracuseStep 3336059 = 5004089) B5004089
theorem B8890337 : Blo 1387513 8890337 := bstep (se 2 (by rfl) ⟨3333876, by rfl⟩ : syracuseStep 8890337 = 6667753) B6667753
theorem B30009467 : Blo 1387513 30009467 := bstep (se 1 (by rfl) ⟨22507100, by rfl⟩ : syracuseStep 30009467 = 45014201) B45014201
theorem B3123359 : Blo 1387513 3123359 := bstep (se 1 (by rfl) ⟨2342519, by rfl⟩ : syracuseStep 3123359 = 4685039) B4685039
theorem B1780039 : Blo 1387513 1780039 := bstep (se 1 (by rfl) ⟨1335029, by rfl⟩ : syracuseStep 1780039 = 2670059) B2670059
theorem B6506999 : Blo 1387513 6506999 := bstep (se 1 (by rfl) ⟨4880249, by rfl⟩ : syracuseStep 6506999 = 9760499) B9760499
theorem B3164879 : Blo 1387513 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B2083631 : Blo 1387513 2083631 := bstep (se 1 (by rfl) ⟨1562723, by rfl⟩ : syracuseStep 2083631 = 3125447) B3125447
theorem B2083655 : Blo 1387513 2083655 := bstep (se 1 (by rfl) ⟨1562741, by rfl⟩ : syracuseStep 2083655 = 3125483) B3125483
theorem B15813467 : Blo 1387513 15813467 := bstep (se 1 (by rfl) ⟨11860100, by rfl⟩ : syracuseStep 15813467 = 23720201) B23720201
theorem B7031771 : Blo 1387513 7031771 := bstep (se 1 (by rfl) ⟨5273828, by rfl⟩ : syracuseStep 7031771 = 10547657) B10547657
theorem B4688927 : Blo 1387513 4688927 := bstep (se 1 (by rfl) ⟨3516695, by rfl⟩ : syracuseStep 4688927 = 7033391) B7033391
theorem B14257235 : Blo 1387513 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B2083931 : Blo 1387513 2083931 := bstep (se 1 (by rfl) ⟨1562948, by rfl⟩ : syracuseStep 2083931 = 3125897) B3125897
theorem B3951899 : Blo 1387513 3951899 := bstep (se 1 (by rfl) ⟨2963924, by rfl⟩ : syracuseStep 3951899 = 5927849) B5927849
theorem B3124601 : Blo 1387513 3124601 := bstep (se 2 (by rfl) ⟨1171725, by rfl⟩ : syracuseStep 3124601 = 2343451) B2343451
theorem B17796509 : Blo 1387513 17796509 := bstep (se 3 (by rfl) ⟨3336845, by rfl⟩ : syracuseStep 17796509 = 6673691) B6673691
theorem B10546685 : Blo 1387513 10546685 := bstep (se 3 (by rfl) ⟨1977503, by rfl⟩ : syracuseStep 10546685 = 3955007) B3955007
theorem B11407031 : Blo 1387513 11407031 := bstep (se 1 (by rfl) ⟨8555273, by rfl⟩ : syracuseStep 11407031 = 17110547) B17110547
theorem B1388239 : Blo 1387513 1388239 := bstep (se 1 (by rfl) ⟨1041179, by rfl⟩ : syracuseStep 1388239 = 2082359) B2082359
theorem B1388635 : Blo 1387513 1388635 := bstep (se 1 (by rfl) ⟨1041476, by rfl⟩ : syracuseStep 1388635 = 2082953) B2082953
theorem B1757695 : Blo 1387513 1757695 := bstep (se 1 (by rfl) ⟨1318271, by rfl⟩ : syracuseStep 1757695 = 2636543) B2636543
theorem B8901227 : Blo 1387513 8901227 := bstep (se 1 (by rfl) ⟨6675920, by rfl⟩ : syracuseStep 8901227 = 13351841) B13351841
theorem B10007165 : Blo 1387513 10007165 := bstep (se 3 (by rfl) ⟨1876343, by rfl⟩ : syracuseStep 10007165 = 3752687) B3752687
theorem B7025291 : Blo 1387513 7025291 := bstep (se 1 (by rfl) ⟨5268968, by rfl⟩ : syracuseStep 7025291 = 10537937) B10537937
theorem B5632679 : Blo 1387513 5632679 := bstep (se 1 (by rfl) ⟨4224509, by rfl⟩ : syracuseStep 5632679 = 8449019) B8449019
theorem B1561279 : Blo 1387513 1561279 := bstep (se 1 (by rfl) ⟨1170959, by rfl⟩ : syracuseStep 1561279 = 2341919) B2341919
theorem B11252449 : Blo 1387513 11252449 := bstep (se 2 (by rfl) ⟨4219668, by rfl⟩ : syracuseStep 11252449 = 8439337) B8439337
theorem B7508855 : Blo 1387513 7508855 := bstep (se 1 (by rfl) ⟨5631641, by rfl⟩ : syracuseStep 7508855 = 11263283) B11263283
theorem B3126239 : Blo 1387513 3126239 := bstep (se 1 (by rfl) ⟨2344679, by rfl⟩ : syracuseStep 3126239 = 4689359) B4689359
theorem B1561927 : Blo 1387513 1561927 := bstep (se 1 (by rfl) ⟨1171445, by rfl⟩ : syracuseStep 1561927 = 2342891) B2342891
theorem B4683257 : Blo 1387513 4683257 := bstep (se 2 (by rfl) ⟨1756221, by rfl⟩ : syracuseStep 4683257 = 3512443) B3512443
theorem B11867755 : Blo 1387513 11867755 := bstep (se 1 (by rfl) ⟨8900816, by rfl⟩ : syracuseStep 11867755 = 17801633) B17801633
theorem B33798019 : Blo 1387513 33798019 := bstep (se 1 (by rfl) ⟨25348514, by rfl⟩ : syracuseStep 33798019 = 50697029) B50697029
theorem B1562791 : Blo 1387513 1562791 := bstep (se 1 (by rfl) ⟨1172093, by rfl⟩ : syracuseStep 1562791 = 2344187) B2344187
theorem B91363565 : Blo 1387513 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B9501047 : Blo 1387513 9501047 := bstep (se 1 (by rfl) ⟨7125785, by rfl⟩ : syracuseStep 9501047 = 14251571) B14251571
theorem B4684607 : Blo 1387513 4684607 := bstep (se 1 (by rfl) ⟨3513455, by rfl⟩ : syracuseStep 4684607 = 7026911) B7026911
theorem B2636975 : Blo 1387513 2636975 := bstep (se 1 (by rfl) ⟨1977731, by rfl⟩ : syracuseStep 2636975 = 3955463) B3955463
theorem B34233889 : Blo 1387513 34233889 := bstep (se 2 (by rfl) ⟨12837708, by rfl⟩ : syracuseStep 34233889 = 25675417) B25675417
theorem B27041363 : Blo 1387513 27041363 := bstep (se 1 (by rfl) ⟨20281022, by rfl⟩ : syracuseStep 27041363 = 40562045) B40562045
theorem B30007043 : Blo 1387513 30007043 := bstep (se 1 (by rfl) ⟨22505282, by rfl⟩ : syracuseStep 30007043 = 45010565) B45010565
theorem B5005903 : Blo 1387513 5005903 := bstep (se 1 (by rfl) ⟨3754427, by rfl⟩ : syracuseStep 5005903 = 7508855) B7508855
theorem B2343593 : Blo 1387513 2343593 := bstep (se 2 (by rfl) ⟨878847, by rfl⟩ : syracuseStep 2343593 = 1757695) B1757695
theorem B7029503 : Blo 1387513 7029503 := bstep (se 1 (by rfl) ⟨5272127, by rfl⟩ : syracuseStep 7029503 = 10544255) B10544255
theorem B4686713 : Blo 1387513 4686713 := bstep (se 2 (by rfl) ⟨1757517, by rfl⟩ : syracuseStep 4686713 = 3515035) B3515035
theorem B2081705 : Blo 1387513 2081705 := bstep (se 2 (by rfl) ⟨780639, by rfl⟩ : syracuseStep 2081705 = 1561279) B1561279
theorem B3122171 : Blo 1387513 3122171 := bstep (se 1 (by rfl) ⟨2341628, by rfl⟩ : syracuseStep 3122171 = 4683257) B4683257
theorem B8438899 : Blo 1387513 8438899 := bstep (se 1 (by rfl) ⟨6329174, by rfl⟩ : syracuseStep 8438899 = 12658349) B12658349
theorem B20006311 : Blo 1387513 20006311 := bstep (se 1 (by rfl) ⟨15004733, by rfl⟩ : syracuseStep 20006311 = 30009467) B30009467
theorem B2082239 : Blo 1387513 2082239 := bstep (se 1 (by rfl) ⟨1561679, by rfl⟩ : syracuseStep 2082239 = 3123359) B3123359
theorem B60909043 : Blo 1387513 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B6334031 : Blo 1387513 6334031 := bstep (se 1 (by rfl) ⟨4750523, by rfl⟩ : syracuseStep 6334031 = 9501047) B9501047
theorem B2082569 : Blo 1387513 2082569 := bstep (se 2 (by rfl) ⟨780963, by rfl⟩ : syracuseStep 2082569 = 1561927) B1561927
theorem B8439677 : Blo 1387513 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B3123071 : Blo 1387513 3123071 := bstep (se 1 (by rfl) ⟨2342303, by rfl⟩ : syracuseStep 3123071 = 4684607) B4684607
theorem B4687847 : Blo 1387513 4687847 := bstep (se 1 (by rfl) ⟨3515885, by rfl⟩ : syracuseStep 4687847 = 7031771) B7031771
theorem B9504823 : Blo 1387513 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B4688009 : Blo 1387513 4688009 := bstep (se 2 (by rfl) ⟨1758003, by rfl⟩ : syracuseStep 4688009 = 3516007) B3516007
theorem B2083067 : Blo 1387513 2083067 := bstep (se 1 (by rfl) ⟨1562300, by rfl⟩ : syracuseStep 2083067 = 3124601) B3124601
theorem B11864339 : Blo 1387513 11864339 := bstep (se 1 (by rfl) ⟨8898254, by rfl⟩ : syracuseStep 11864339 = 17796509) B17796509
theorem B7031123 : Blo 1387513 7031123 := bstep (se 1 (by rfl) ⟨5273342, by rfl⟩ : syracuseStep 7031123 = 10546685) B10546685
theorem B7604687 : Blo 1387513 7604687 := bstep (se 1 (by rfl) ⟨5703515, by rfl⟩ : syracuseStep 7604687 = 11407031) B11407031
theorem B2083721 : Blo 1387513 2083721 := bstep (se 2 (by rfl) ⟨781395, by rfl⟩ : syracuseStep 2083721 = 1562791) B1562791
theorem B5934151 : Blo 1387513 5934151 := bstep (se 1 (by rfl) ⟨4450613, by rfl⟩ : syracuseStep 5934151 = 8901227) B8901227
theorem B19262555 : Blo 1387513 19262555 := bstep (se 1 (by rfl) ⟨14446916, by rfl⟩ : syracuseStep 19262555 = 28893833) B28893833
theorem B7031933 : Blo 1387513 7031933 := bstep (se 3 (by rfl) ⟨1318487, by rfl⟩ : syracuseStep 7031933 = 2636975) B2636975
theorem B1387675 : Blo 1387513 1387675 := bstep (se 1 (by rfl) ⟨1040756, by rfl⟩ : syracuseStep 1387675 = 2081513) B2081513
theorem B5631191 : Blo 1387513 5631191 := bstep (se 1 (by rfl) ⟨4223393, by rfl⟩ : syracuseStep 5631191 = 8446787) B8446787
theorem B2084159 : Blo 1387513 2084159 := bstep (se 1 (by rfl) ⟨1563119, by rfl⟩ : syracuseStep 2084159 = 3126239) B3126239
theorem B3124655 : Blo 1387513 3124655 := bstep (se 1 (by rfl) ⟨2343491, by rfl⟩ : syracuseStep 3124655 = 4686983) B4686983
theorem B1387967 : Blo 1387513 1387967 := bstep (se 1 (by rfl) ⟨1040975, by rfl⟩ : syracuseStep 1387967 = 2081951) B2081951
theorem B15003265 : Blo 1387513 15003265 := bstep (se 2 (by rfl) ⟨5626224, by rfl⟩ : syracuseStep 15003265 = 11252449) B11252449
theorem B1388187 : Blo 1387513 1388187 := bstep (se 1 (by rfl) ⟨1041140, by rfl⟩ : syracuseStep 1388187 = 2082281) B2082281
theorem B2224039 : Blo 1387513 2224039 := bstep (se 1 (by rfl) ⟨1668029, by rfl⟩ : syracuseStep 2224039 = 3336059) B3336059
theorem B5926891 : Blo 1387513 5926891 := bstep (se 1 (by rfl) ⟨4445168, by rfl⟩ : syracuseStep 5926891 = 8890337) B8890337
theorem B26685773 : Blo 1387513 26685773 := bstep (se 3 (by rfl) ⟨5003582, by rfl⟩ : syracuseStep 26685773 = 10007165) B10007165
theorem B4337999 : Blo 1387513 4337999 := bstep (se 1 (by rfl) ⟨3253499, by rfl⟩ : syracuseStep 4337999 = 6506999) B6506999
theorem B15020477 : Blo 1387513 15020477 := bstep (se 3 (by rfl) ⟨2816339, by rfl⟩ : syracuseStep 15020477 = 5632679) B5632679
theorem B1389087 : Blo 1387513 1389087 := bstep (se 1 (by rfl) ⟨1041815, by rfl⟩ : syracuseStep 1389087 = 2083631) B2083631
theorem B1389103 : Blo 1387513 1389103 := bstep (se 1 (by rfl) ⟨1041827, by rfl⟩ : syracuseStep 1389103 = 2083655) B2083655
theorem B3125951 : Blo 1387513 3125951 := bstep (se 1 (by rfl) ⟨2344463, by rfl⟩ : syracuseStep 3125951 = 4688927) B4688927
theorem B1389287 : Blo 1387513 1389287 := bstep (se 1 (by rfl) ⟨1041965, by rfl⟩ : syracuseStep 1389287 = 2083931) B2083931
theorem B15823673 : Blo 1387513 15823673 := bstep (se 2 (by rfl) ⟨5933877, by rfl⟩ : syracuseStep 15823673 = 11867755) B11867755
theorem B2634599 : Blo 1387513 2634599 := bstep (se 1 (by rfl) ⟨1975949, by rfl⟩ : syracuseStep 2634599 = 3951899) B3951899
theorem B18027575 : Blo 1387513 18027575 := bstep (se 1 (by rfl) ⟨13520681, by rfl⟩ : syracuseStep 18027575 = 27041363) B27041363
theorem B7034363 : Blo 1387513 7034363 := bstep (se 1 (by rfl) ⟨5275772, by rfl⟩ : syracuseStep 7034363 = 10551545) B10551545
theorem B4683527 : Blo 1387513 4683527 := bstep (se 1 (by rfl) ⟨3512645, by rfl⟩ : syracuseStep 4683527 = 7025291) B7025291
theorem B8894461 : Blo 1387513 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B9623719 : Blo 1387513 9623719 := bstep (se 1 (by rfl) ⟨7217789, by rfl⟩ : syracuseStep 9623719 = 14435579) B14435579
theorem B9493541 : Blo 1387513 9493541 := bstep (se 4 (by rfl) ⟨890019, by rfl⟩ : syracuseStep 9493541 = 1780039) B1780039
theorem B10542311 : Blo 1387513 10542311 := bstep (se 1 (by rfl) ⟨7906733, by rfl⟩ : syracuseStep 10542311 = 15813467) B15813467
theorem B45645185 : Blo 1387513 45645185 := bstep (se 2 (by rfl) ⟨17116944, by rfl⟩ : syracuseStep 45645185 = 34233889) B34233889
theorem B20004695 : Blo 1387513 20004695 := bstep (se 1 (by rfl) ⟨15003521, by rfl⟩ : syracuseStep 20004695 = 30007043) B30007043
theorem B45064025 : Blo 1387513 45064025 := bstep (se 2 (by rfl) ⟨16899009, by rfl⟩ : syracuseStep 45064025 = 33798019) B33798019
theorem B12673097 : Blo 1387513 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B2891999 : Blo 1387513 2891999 := bstep (se 1 (by rfl) ⟨2168999, by rfl⟩ : syracuseStep 2891999 = 4337999) B4337999
theorem B4686335 : Blo 1387513 4686335 := bstep (se 1 (by rfl) ⟨3514751, by rfl⟩ : syracuseStep 4686335 = 7029503) B7029503
theorem B2081447 : Blo 1387513 2081447 := bstep (se 1 (by rfl) ⟨1561085, by rfl⟩ : syracuseStep 2081447 = 3122171) B3122171
theorem B12018383 : Blo 1387513 12018383 := bstep (se 1 (by rfl) ⟨9013787, by rfl⟩ : syracuseStep 12018383 = 18027575) B18027575
theorem B3122351 : Blo 1387513 3122351 := bstep (se 1 (by rfl) ⟨2341763, by rfl⟩ : syracuseStep 3122351 = 4683527) B4683527
theorem B2082047 : Blo 1387513 2082047 := bstep (se 1 (by rfl) ⟨1561535, by rfl⟩ : syracuseStep 2082047 = 3123071) B3123071
theorem B4687415 : Blo 1387513 4687415 := bstep (se 1 (by rfl) ⟨3515561, by rfl⟩ : syracuseStep 4687415 = 7031123) B7031123
theorem B26675081 : Blo 1387513 26675081 := bstep (se 2 (by rfl) ⟨10003155, by rfl⟩ : syracuseStep 26675081 = 20006311) B20006311
theorem B4687955 : Blo 1387513 4687955 := bstep (se 1 (by rfl) ⟨3515966, by rfl⟩ : syracuseStep 4687955 = 7031933) B7031933
theorem B3754127 : Blo 1387513 3754127 := bstep (se 1 (by rfl) ⟨2815595, by rfl⟩ : syracuseStep 3754127 = 5631191) B5631191
theorem B2083103 : Blo 1387513 2083103 := bstep (se 1 (by rfl) ⟨1562327, by rfl⟩ : syracuseStep 2083103 = 3124655) B3124655
theorem B30042683 : Blo 1387513 30042683 := bstep (se 1 (by rfl) ⟨22532012, by rfl⟩ : syracuseStep 30042683 = 45064025) B45064025
theorem B12831625 : Blo 1387513 12831625 := bstep (se 2 (by rfl) ⟨4811859, by rfl⟩ : syracuseStep 12831625 = 9623719) B9623719
theorem B10013651 : Blo 1387513 10013651 := bstep (se 1 (by rfl) ⟨7510238, by rfl⟩ : syracuseStep 10013651 = 15020477) B15020477
theorem B2083967 : Blo 1387513 2083967 := bstep (se 1 (by rfl) ⟨1562975, by rfl⟩ : syracuseStep 2083967 = 3125951) B3125951
theorem B1756399 : Blo 1387513 1756399 := bstep (se 1 (by rfl) ⟨1317299, by rfl⟩ : syracuseStep 1756399 = 2634599) B2634599
theorem B3124475 : Blo 1387513 3124475 := bstep (se 1 (by rfl) ⟨2343356, by rfl⟩ : syracuseStep 3124475 = 4686713) B4686713
theorem B1387803 : Blo 1387513 1387803 := bstep (se 1 (by rfl) ⟨1040852, by rfl⟩ : syracuseStep 1387803 = 2081705) B2081705
theorem B1388159 : Blo 1387513 1388159 := bstep (se 1 (by rfl) ⟨1041119, by rfl⟩ : syracuseStep 1388159 = 2082239) B2082239
theorem B4689575 : Blo 1387513 4689575 := bstep (se 1 (by rfl) ⟨3517181, by rfl⟩ : syracuseStep 4689575 = 7034363) B7034363
theorem B4222687 : Blo 1387513 4222687 := bstep (se 1 (by rfl) ⟨3167015, by rfl⟩ : syracuseStep 4222687 = 6334031) B6334031
theorem B1388379 : Blo 1387513 1388379 := bstep (se 1 (by rfl) ⟨1041284, by rfl⟩ : syracuseStep 1388379 = 2082569) B2082569
theorem B3125231 : Blo 1387513 3125231 := bstep (se 1 (by rfl) ⟨2343923, by rfl⟩ : syracuseStep 3125231 = 4687847) B4687847
theorem B3125339 : Blo 1387513 3125339 := bstep (se 1 (by rfl) ⟨2344004, by rfl⟩ : syracuseStep 3125339 = 4688009) B4688009
theorem B11251865 : Blo 1387513 11251865 := bstep (se 2 (by rfl) ⟨4219449, by rfl⟩ : syracuseStep 11251865 = 8438899) B8438899
theorem B1388711 : Blo 1387513 1388711 := bstep (se 1 (by rfl) ⟨1041533, by rfl⟩ : syracuseStep 1388711 = 2083067) B2083067
theorem B7909559 : Blo 1387513 7909559 := bstep (se 1 (by rfl) ⟨5932169, by rfl⟩ : syracuseStep 7909559 = 11864339) B11864339
theorem B1389147 : Blo 1387513 1389147 := bstep (se 1 (by rfl) ⟨1041860, by rfl⟩ : syracuseStep 1389147 = 2083721) B2083721
theorem B81212057 : Blo 1387513 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B6329027 : Blo 1387513 6329027 := bstep (se 1 (by rfl) ⟨4746770, by rfl⟩ : syracuseStep 6329027 = 9493541) B9493541
theorem B12841703 : Blo 1387513 12841703 := bstep (se 1 (by rfl) ⟨9631277, by rfl⟩ : syracuseStep 12841703 = 19262555) B19262555
theorem B1389439 : Blo 1387513 1389439 := bstep (se 1 (by rfl) ⟨1042079, by rfl⟩ : syracuseStep 1389439 = 2084159) B2084159
theorem B30430123 : Blo 1387513 30430123 := bstep (se 1 (by rfl) ⟨22822592, by rfl⟩ : syracuseStep 30430123 = 45645185) B45645185
theorem B7902521 : Blo 1387513 7902521 := bstep (se 2 (by rfl) ⟨2963445, by rfl⟩ : syracuseStep 7902521 = 5926891) B5926891
theorem B11859281 : Blo 1387513 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B17790515 : Blo 1387513 17790515 := bstep (se 1 (by rfl) ⟨13342886, by rfl⟩ : syracuseStep 17790515 = 26685773) B26685773
theorem B1562395 : Blo 1387513 1562395 := bstep (se 1 (by rfl) ⟨1171796, by rfl⟩ : syracuseStep 1562395 = 2343593) B2343593
theorem B10549115 : Blo 1387513 10549115 := bstep (se 1 (by rfl) ⟨7911836, by rfl⟩ : syracuseStep 10549115 = 15823673) B15823673
theorem B6674537 : Blo 1387513 6674537 := bstep (se 2 (by rfl) ⟨2502951, by rfl⟩ : syracuseStep 6674537 = 5005903) B5005903
theorem B5626451 : Blo 1387513 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B7912201 : Blo 1387513 7912201 := bstep (se 2 (by rfl) ⟨2967075, by rfl⟩ : syracuseStep 7912201 = 5934151) B5934151
theorem B5069791 : Blo 1387513 5069791 := bstep (se 1 (by rfl) ⟨3802343, by rfl⟩ : syracuseStep 5069791 = 7604687) B7604687
theorem B7028207 : Blo 1387513 7028207 := bstep (se 1 (by rfl) ⟨5271155, by rfl⟩ : syracuseStep 7028207 = 10542311) B10542311
theorem B20004353 : Blo 1387513 20004353 := bstep (se 2 (by rfl) ⟨7501632, by rfl⟩ : syracuseStep 20004353 = 15003265) B15003265
theorem B2965385 : Blo 1387513 2965385 := bstep (se 2 (by rfl) ⟨1112019, by rfl⟩ : syracuseStep 2965385 = 2224039) B2224039
theorem B13336463 : Blo 1387513 13336463 := bstep (se 1 (by rfl) ⟨10002347, by rfl⟩ : syracuseStep 13336463 = 20004695) B20004695
theorem B54141371 : Blo 1387513 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B4219351 : Blo 1387513 4219351 := bstep (se 1 (by rfl) ⟨3164513, by rfl⟩ : syracuseStep 4219351 = 6329027) B6329027
theorem B8012255 : Blo 1387513 8012255 := bstep (se 1 (by rfl) ⟨6009191, by rfl⟩ : syracuseStep 8012255 = 12018383) B12018383
theorem B8561135 : Blo 1387513 8561135 := bstep (se 1 (by rfl) ⟨6420851, by rfl⟩ : syracuseStep 8561135 = 12841703) B12841703
theorem B2081567 : Blo 1387513 2081567 := bstep (se 1 (by rfl) ⟨1561175, by rfl⟩ : syracuseStep 2081567 = 3122351) B3122351
theorem B5268347 : Blo 1387513 5268347 := bstep (se 1 (by rfl) ⟨3951260, by rfl⟩ : syracuseStep 5268347 = 7902521) B7902521
theorem B7906187 : Blo 1387513 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B6759721 : Blo 1387513 6759721 := bstep (se 2 (by rfl) ⟨2534895, by rfl⟩ : syracuseStep 6759721 = 5069791) B5069791
theorem B4449691 : Blo 1387513 4449691 := bstep (se 1 (by rfl) ⟨3337268, by rfl⟩ : syracuseStep 4449691 = 6674537) B6674537
theorem B2082983 : Blo 1387513 2082983 := bstep (se 1 (by rfl) ⟨1562237, by rfl⟩ : syracuseStep 2082983 = 3124475) B3124475
theorem B162293989 : Blo 1387513 162293989 := bstep (se 4 (by rfl) ⟨15215061, by rfl⟩ : syracuseStep 162293989 = 30430123) B30430123
theorem B5630249 : Blo 1387513 5630249 := bstep (se 2 (by rfl) ⟨2111343, by rfl⟩ : syracuseStep 5630249 = 4222687) B4222687
theorem B2083193 : Blo 1387513 2083193 := bstep (se 2 (by rfl) ⟨781197, by rfl⟩ : syracuseStep 2083193 = 1562395) B1562395
theorem B1976923 : Blo 1387513 1976923 := bstep (se 1 (by rfl) ⟨1482692, by rfl⟩ : syracuseStep 1976923 = 2965385) B2965385
theorem B8890975 : Blo 1387513 8890975 := bstep (se 1 (by rfl) ⟨6668231, by rfl⟩ : syracuseStep 8890975 = 13336463) B13336463
theorem B2083487 : Blo 1387513 2083487 := bstep (se 1 (by rfl) ⟨1562615, by rfl⟩ : syracuseStep 2083487 = 3125231) B3125231
theorem B8448731 : Blo 1387513 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B2083559 : Blo 1387513 2083559 := bstep (se 1 (by rfl) ⟨1562669, by rfl⟩ : syracuseStep 2083559 = 3125339) B3125339
theorem B1927999 : Blo 1387513 1927999 := bstep (se 1 (by rfl) ⟨1445999, by rfl⟩ : syracuseStep 1927999 = 2891999) B2891999
theorem B3124223 : Blo 1387513 3124223 := bstep (se 1 (by rfl) ⟨2343167, by rfl⟩ : syracuseStep 3124223 = 4686335) B4686335
theorem B1387631 : Blo 1387513 1387631 := bstep (se 1 (by rfl) ⟨1040723, by rfl⟩ : syracuseStep 1387631 = 2081447) B2081447
theorem B1388031 : Blo 1387513 1388031 := bstep (se 1 (by rfl) ⟨1041023, by rfl⟩ : syracuseStep 1388031 = 2082047) B2082047
theorem B3124943 : Blo 1387513 3124943 := bstep (se 1 (by rfl) ⟨2343707, by rfl⟩ : syracuseStep 3124943 = 4687415) B4687415
theorem B17108833 : Blo 1387513 17108833 := bstep (se 2 (by rfl) ⟨6415812, by rfl⟩ : syracuseStep 17108833 = 12831625) B12831625
theorem B7032743 : Blo 1387513 7032743 := bstep (se 1 (by rfl) ⟨5274557, by rfl⟩ : syracuseStep 7032743 = 10549115) B10549115
theorem B3125303 : Blo 1387513 3125303 := bstep (se 1 (by rfl) ⟨2343977, by rfl⟩ : syracuseStep 3125303 = 4687955) B4687955
theorem B2502751 : Blo 1387513 2502751 := bstep (se 1 (by rfl) ⟨1877063, by rfl⟩ : syracuseStep 2502751 = 3754127) B3754127
theorem B1388735 : Blo 1387513 1388735 := bstep (se 1 (by rfl) ⟨1041551, by rfl⟩ : syracuseStep 1388735 = 2083103) B2083103
theorem B1389311 : Blo 1387513 1389311 := bstep (se 1 (by rfl) ⟨1041983, by rfl⟩ : syracuseStep 1389311 = 2083967) B2083967
theorem B3126383 : Blo 1387513 3126383 := bstep (se 1 (by rfl) ⟨2344787, by rfl⟩ : syracuseStep 3126383 = 4689575) B4689575
theorem B7501243 : Blo 1387513 7501243 := bstep (se 1 (by rfl) ⟨5625932, by rfl⟩ : syracuseStep 7501243 = 11251865) B11251865
theorem B5273039 : Blo 1387513 5273039 := bstep (se 1 (by rfl) ⟨3954779, by rfl⟩ : syracuseStep 5273039 = 7909559) B7909559
theorem B10549601 : Blo 1387513 10549601 := bstep (se 2 (by rfl) ⟨3956100, by rfl⟩ : syracuseStep 10549601 = 7912201) B7912201
theorem B11860343 : Blo 1387513 11860343 := bstep (se 1 (by rfl) ⟨8895257, by rfl⟩ : syracuseStep 11860343 = 17790515) B17790515
theorem B17783387 : Blo 1387513 17783387 := bstep (se 1 (by rfl) ⟨13337540, by rfl⟩ : syracuseStep 17783387 = 26675081) B26675081
theorem B2341865 : Blo 1387513 2341865 := bstep (se 2 (by rfl) ⟨878199, by rfl⟩ : syracuseStep 2341865 = 1756399) B1756399
theorem B20028455 : Blo 1387513 20028455 := bstep (se 1 (by rfl) ⟨15021341, by rfl⟩ : syracuseStep 20028455 = 30042683) B30042683
theorem B3750967 : Blo 1387513 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B6675767 : Blo 1387513 6675767 := bstep (se 1 (by rfl) ⟨5006825, by rfl⟩ : syracuseStep 6675767 = 10013651) B10013651
theorem B4685471 : Blo 1387513 4685471 := bstep (se 1 (by rfl) ⟨3514103, by rfl⟩ : syracuseStep 4685471 = 7028207) B7028207
theorem B13336235 : Blo 1387513 13336235 := bstep (se 1 (by rfl) ⟨10002176, by rfl⟩ : syracuseStep 13336235 = 20004353) B20004353
theorem B20005157 : Blo 1387513 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B36094247 : Blo 1387513 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B216391985 : Blo 1387513 216391985 := bstep (se 2 (by rfl) ⟨81146994, by rfl⟩ : syracuseStep 216391985 = 162293989) B162293989
theorem B11854633 : Blo 1387513 11854633 := bstep (se 2 (by rfl) ⟨4445487, by rfl⟩ : syracuseStep 11854633 = 8890975) B8890975
theorem B3515359 : Blo 1387513 3515359 := bstep (se 1 (by rfl) ⟨2636519, by rfl⟩ : syracuseStep 3515359 = 5273039) B5273039
theorem B21366013 : Blo 1387513 21366013 := bstep (se 3 (by rfl) ⟨4006127, by rfl⟩ : syracuseStep 21366013 = 8012255) B8012255
theorem B7906895 : Blo 1387513 7906895 := bstep (se 1 (by rfl) ⟨5930171, by rfl⟩ : syracuseStep 7906895 = 11860343) B11860343
theorem B9012961 : Blo 1387513 9012961 := bstep (se 2 (by rfl) ⟨3379860, by rfl⟩ : syracuseStep 9012961 = 6759721) B6759721
theorem B11855591 : Blo 1387513 11855591 := bstep (se 1 (by rfl) ⟨8891693, by rfl⟩ : syracuseStep 11855591 = 17783387) B17783387
theorem B5932921 : Blo 1387513 5932921 := bstep (se 2 (by rfl) ⟨2224845, by rfl⟩ : syracuseStep 5932921 = 4449691) B4449691
theorem B2082815 : Blo 1387513 2082815 := bstep (se 1 (by rfl) ⟨1562111, by rfl⟩ : syracuseStep 2082815 = 3124223) B3124223
theorem B4450511 : Blo 1387513 4450511 := bstep (se 1 (by rfl) ⟨3337883, by rfl⟩ : syracuseStep 4450511 = 6675767) B6675767
theorem B3123647 : Blo 1387513 3123647 := bstep (se 1 (by rfl) ⟨2342735, by rfl⟩ : syracuseStep 3123647 = 4685471) B4685471
theorem B8890823 : Blo 1387513 8890823 := bstep (se 1 (by rfl) ⟨6668117, by rfl⟩ : syracuseStep 8890823 = 13336235) B13336235
theorem B2083295 : Blo 1387513 2083295 := bstep (se 1 (by rfl) ⟨1562471, by rfl⟩ : syracuseStep 2083295 = 3124943) B3124943
theorem B4688495 : Blo 1387513 4688495 := bstep (se 1 (by rfl) ⟨3516371, by rfl⟩ : syracuseStep 4688495 = 7032743) B7032743
theorem B2083535 : Blo 1387513 2083535 := bstep (se 1 (by rfl) ⟨1562651, by rfl⟩ : syracuseStep 2083535 = 3125303) B3125303
theorem B3337001 : Blo 1387513 3337001 := bstep (se 2 (by rfl) ⟨1251375, by rfl⟩ : syracuseStep 3337001 = 2502751) B2502751
theorem B1387711 : Blo 1387513 1387711 := bstep (se 1 (by rfl) ⟨1040783, by rfl⟩ : syracuseStep 1387711 = 2081567) B2081567
theorem B5270791 : Blo 1387513 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B2084255 : Blo 1387513 2084255 := bstep (se 1 (by rfl) ⟨1563191, by rfl⟩ : syracuseStep 2084255 = 3126383) B3126383
theorem B1388655 : Blo 1387513 1388655 := bstep (se 1 (by rfl) ⟨1041491, by rfl⟩ : syracuseStep 1388655 = 2082983) B2082983
theorem B7033067 : Blo 1387513 7033067 := bstep (se 1 (by rfl) ⟨5274800, by rfl⟩ : syracuseStep 7033067 = 10549601) B10549601
theorem B1388795 : Blo 1387513 1388795 := bstep (se 1 (by rfl) ⟨1041596, by rfl⟩ : syracuseStep 1388795 = 2083193) B2083193
theorem B1388991 : Blo 1387513 1388991 := bstep (se 1 (by rfl) ⟨1041743, by rfl⟩ : syracuseStep 1388991 = 2083487) B2083487
theorem B5632487 : Blo 1387513 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B1389039 : Blo 1387513 1389039 := bstep (se 1 (by rfl) ⟨1041779, by rfl⟩ : syracuseStep 1389039 = 2083559) B2083559
theorem B1561243 : Blo 1387513 1561243 := bstep (se 1 (by rfl) ⟨1170932, by rfl⟩ : syracuseStep 1561243 = 2341865) B2341865
theorem B22811777 : Blo 1387513 22811777 := bstep (se 2 (by rfl) ⟨8554416, by rfl⟩ : syracuseStep 22811777 = 17108833) B17108833
theorem B5707423 : Blo 1387513 5707423 := bstep (se 1 (by rfl) ⟨4280567, by rfl⟩ : syracuseStep 5707423 = 8561135) B8561135
theorem B3512231 : Blo 1387513 3512231 := bstep (se 1 (by rfl) ⟨2634173, by rfl⟩ : syracuseStep 3512231 = 5268347) B5268347
theorem B15013997 : Blo 1387513 15013997 := bstep (se 3 (by rfl) ⟨2815124, by rfl⟩ : syracuseStep 15013997 = 5630249) B5630249
theorem B2635897 : Blo 1387513 2635897 := bstep (se 2 (by rfl) ⟨988461, by rfl⟩ : syracuseStep 2635897 = 1976923) B1976923
theorem B2570665 : Blo 1387513 2570665 := bstep (se 2 (by rfl) ⟨963999, by rfl⟩ : syracuseStep 2570665 = 1927999) B1927999
theorem B10001657 : Blo 1387513 10001657 := bstep (se 2 (by rfl) ⟨3750621, by rfl⟩ : syracuseStep 10001657 = 7501243) B7501243
theorem B13352303 : Blo 1387513 13352303 := bstep (se 1 (by rfl) ⟨10014227, by rfl⟩ : syracuseStep 13352303 = 20028455) B20028455
theorem B22503205 : Blo 1387513 22503205 := bstep (se 4 (by rfl) ⟨2109675, by rfl⟩ : syracuseStep 22503205 = 4219351) B4219351
theorem B3514529 : Blo 1387513 3514529 := bstep (se 2 (by rfl) ⟨1317948, by rfl⟩ : syracuseStep 3514529 = 2635897) B2635897
theorem B13336771 : Blo 1387513 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B144261323 : Blo 1387513 144261323 := bstep (se 1 (by rfl) ⟨108195992, by rfl⟩ : syracuseStep 144261323 = 216391985) B216391985
theorem B2081657 : Blo 1387513 2081657 := bstep (se 2 (by rfl) ⟨780621, by rfl⟩ : syracuseStep 2081657 = 1561243) B1561243
theorem B4687145 : Blo 1387513 4687145 := bstep (se 2 (by rfl) ⟨1757679, by rfl⟩ : syracuseStep 4687145 = 3515359) B3515359
theorem B2082431 : Blo 1387513 2082431 := bstep (se 1 (by rfl) ⟨1561823, by rfl⟩ : syracuseStep 2082431 = 3123647) B3123647
theorem B4688711 : Blo 1387513 4688711 := bstep (se 1 (by rfl) ⟨3516533, by rfl⟩ : syracuseStep 4688711 = 7033067) B7033067
theorem B24062831 : Blo 1387513 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B3754991 : Blo 1387513 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B3427553 : Blo 1387513 3427553 := bstep (se 2 (by rfl) ⟨1285332, by rfl⟩ : syracuseStep 3427553 = 2570665) B2570665
theorem B15207851 : Blo 1387513 15207851 := bstep (se 1 (by rfl) ⟨11405888, by rfl⟩ : syracuseStep 15207851 = 22811777) B22811777
theorem B5271263 : Blo 1387513 5271263 := bstep (se 1 (by rfl) ⟨3953447, by rfl⟩ : syracuseStep 5271263 = 7906895) B7906895
theorem B15806177 : Blo 1387513 15806177 := bstep (se 2 (by rfl) ⟨5927316, by rfl⟩ : syracuseStep 15806177 = 11854633) B11854633
theorem B1388543 : Blo 1387513 1388543 := bstep (se 1 (by rfl) ⟨1041407, by rfl⟩ : syracuseStep 1388543 = 2082815) B2082815
theorem B5927215 : Blo 1387513 5927215 := bstep (se 1 (by rfl) ⟨4445411, by rfl⟩ : syracuseStep 5927215 = 8890823) B8890823
theorem B1388863 : Blo 1387513 1388863 := bstep (se 1 (by rfl) ⟨1041647, by rfl⟩ : syracuseStep 1388863 = 2083295) B2083295
theorem B28488017 : Blo 1387513 28488017 := bstep (se 2 (by rfl) ⟨10683006, by rfl⟩ : syracuseStep 28488017 = 21366013) B21366013
theorem B3125663 : Blo 1387513 3125663 := bstep (se 1 (by rfl) ⟨2344247, by rfl⟩ : syracuseStep 3125663 = 4688495) B4688495
theorem B1389023 : Blo 1387513 1389023 := bstep (se 1 (by rfl) ⟨1041767, by rfl⟩ : syracuseStep 1389023 = 2083535) B2083535
theorem B2224667 : Blo 1387513 2224667 := bstep (se 1 (by rfl) ⟨1668500, by rfl⟩ : syracuseStep 2224667 = 3337001) B3337001
theorem B8901535 : Blo 1387513 8901535 := bstep (se 1 (by rfl) ⟨6676151, by rfl⟩ : syracuseStep 8901535 = 13352303) B13352303
theorem B1389503 : Blo 1387513 1389503 := bstep (se 1 (by rfl) ⟨1042127, by rfl⟩ : syracuseStep 1389503 = 2084255) B2084255
theorem B30004273 : Blo 1387513 30004273 := bstep (se 2 (by rfl) ⟨11251602, by rfl⟩ : syracuseStep 30004273 = 22503205) B22503205
theorem B7910561 : Blo 1387513 7910561 := bstep (se 2 (by rfl) ⟨2966460, by rfl⟩ : syracuseStep 7910561 = 5932921) B5932921
theorem B11868029 : Blo 1387513 11868029 := bstep (se 3 (by rfl) ⟨2225255, by rfl⟩ : syracuseStep 11868029 = 4450511) B4450511
theorem B7903727 : Blo 1387513 7903727 := bstep (se 1 (by rfl) ⟨5927795, by rfl⟩ : syracuseStep 7903727 = 11855591) B11855591
theorem B2341487 : Blo 1387513 2341487 := bstep (se 1 (by rfl) ⟨1756115, by rfl⟩ : syracuseStep 2341487 = 3512231) B3512231
theorem B10009331 : Blo 1387513 10009331 := bstep (se 1 (by rfl) ⟨7506998, by rfl⟩ : syracuseStep 10009331 = 15013997) B15013997
theorem B7027721 : Blo 1387513 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B6667771 : Blo 1387513 6667771 := bstep (se 1 (by rfl) ⟨5000828, by rfl⟩ : syracuseStep 6667771 = 10001657) B10001657
theorem B7609897 : Blo 1387513 7609897 := bstep (se 2 (by rfl) ⟨2853711, by rfl⟩ : syracuseStep 7609897 = 5707423) B5707423
theorem B12017281 : Blo 1387513 12017281 := bstep (se 2 (by rfl) ⟨4506480, by rfl⟩ : syracuseStep 12017281 = 9012961) B9012961
theorem B2343019 : Blo 1387513 2343019 := bstep (se 1 (by rfl) ⟨1757264, by rfl⟩ : syracuseStep 2343019 = 3514529) B3514529
theorem B96174215 : Blo 1387513 96174215 := bstep (se 1 (by rfl) ⟨72130661, by rfl⟩ : syracuseStep 96174215 = 144261323) B144261323
theorem B1483111 : Blo 1387513 1483111 := bstep (se 1 (by rfl) ⟨1112333, by rfl⟩ : syracuseStep 1483111 = 2224667) B2224667
theorem B5269151 : Blo 1387513 5269151 := bstep (se 1 (by rfl) ⟨3951863, by rfl⟩ : syracuseStep 5269151 = 7903727) B7903727
theorem B16041887 : Blo 1387513 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B8890361 : Blo 1387513 8890361 := bstep (se 2 (by rfl) ⟨3333885, by rfl⟩ : syracuseStep 8890361 = 6667771) B6667771
theorem B10537451 : Blo 1387513 10537451 := bstep (se 1 (by rfl) ⟨7903088, by rfl⟩ : syracuseStep 10537451 = 15806177) B15806177
theorem B18992011 : Blo 1387513 18992011 := bstep (se 1 (by rfl) ⟨14244008, by rfl⟩ : syracuseStep 18992011 = 28488017) B28488017
theorem B2083775 : Blo 1387513 2083775 := bstep (se 1 (by rfl) ⟨1562831, by rfl⟩ : syracuseStep 2083775 = 3125663) B3125663
theorem B1387771 : Blo 1387513 1387771 := bstep (se 1 (by rfl) ⟨1040828, by rfl⟩ : syracuseStep 1387771 = 2081657) B2081657
theorem B3124763 : Blo 1387513 3124763 := bstep (se 1 (by rfl) ⟨2343572, by rfl⟩ : syracuseStep 3124763 = 4687145) B4687145
theorem B1388287 : Blo 1387513 1388287 := bstep (se 1 (by rfl) ⟨1041215, by rfl⟩ : syracuseStep 1388287 = 2082431) B2082431
theorem B40005697 : Blo 1387513 40005697 := bstep (se 2 (by rfl) ⟨15002136, by rfl⟩ : syracuseStep 40005697 = 30004273) B30004273
theorem B1560991 : Blo 1387513 1560991 := bstep (se 1 (by rfl) ⟨1170743, by rfl⟩ : syracuseStep 1560991 = 2341487) B2341487
theorem B6672887 : Blo 1387513 6672887 := bstep (se 1 (by rfl) ⟨5004665, by rfl⟩ : syracuseStep 6672887 = 10009331) B10009331
theorem B3125807 : Blo 1387513 3125807 := bstep (se 1 (by rfl) ⟨2344355, by rfl⟩ : syracuseStep 3125807 = 4688711) B4688711
theorem B2503327 : Blo 1387513 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B10146529 : Blo 1387513 10146529 := bstep (se 2 (by rfl) ⟨3804948, by rfl⟩ : syracuseStep 10146529 = 7609897) B7609897
theorem B10138567 : Blo 1387513 10138567 := bstep (se 1 (by rfl) ⟨7603925, by rfl⟩ : syracuseStep 10138567 = 15207851) B15207851
theorem B17782361 : Blo 1387513 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B7902953 : Blo 1387513 7902953 := bstep (se 2 (by rfl) ⟨2963607, by rfl⟩ : syracuseStep 7902953 = 5927215) B5927215
theorem B9140141 : Blo 1387513 9140141 := bstep (se 3 (by rfl) ⟨1713776, by rfl⟩ : syracuseStep 9140141 = 3427553) B3427553
theorem B5273707 : Blo 1387513 5273707 := bstep (se 1 (by rfl) ⟨3955280, by rfl⟩ : syracuseStep 5273707 = 7910561) B7910561
theorem B11868713 : Blo 1387513 11868713 := bstep (se 2 (by rfl) ⟨4450767, by rfl⟩ : syracuseStep 11868713 = 8901535) B8901535
theorem B7912019 : Blo 1387513 7912019 := bstep (se 1 (by rfl) ⟨5934014, by rfl⟩ : syracuseStep 7912019 = 11868029) B11868029
theorem B4685147 : Blo 1387513 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B16023041 : Blo 1387513 16023041 := bstep (se 2 (by rfl) ⟨6008640, by rfl⟩ : syracuseStep 16023041 = 12017281) B12017281
theorem B3514175 : Blo 1387513 3514175 := bstep (se 1 (by rfl) ⟨2635631, by rfl⟩ : syracuseStep 3514175 = 5271263) B5271263
theorem B4448591 : Blo 1387513 4448591 := bstep (se 1 (by rfl) ⟨3336443, by rfl⟩ : syracuseStep 4448591 = 6672887) B6672887
theorem B2081321 : Blo 1387513 2081321 := bstep (se 2 (by rfl) ⟨780495, by rfl⟩ : syracuseStep 2081321 = 1560991) B1560991
theorem B11854907 : Blo 1387513 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B5268635 : Blo 1387513 5268635 := bstep (se 1 (by rfl) ⟨3951476, by rfl⟩ : syracuseStep 5268635 = 7902953) B7902953
theorem B25322681 : Blo 1387513 25322681 := bstep (se 2 (by rfl) ⟨9496005, by rfl⟩ : syracuseStep 25322681 = 18992011) B18992011
theorem B13518089 : Blo 1387513 13518089 := bstep (se 2 (by rfl) ⟨5069283, by rfl⟩ : syracuseStep 13518089 = 10138567) B10138567
theorem B3123431 : Blo 1387513 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B2083175 : Blo 1387513 2083175 := bstep (se 1 (by rfl) ⟨1562381, by rfl⟩ : syracuseStep 2083175 = 3124763) B3124763
theorem B53340929 : Blo 1387513 53340929 := bstep (se 2 (by rfl) ⟨20002848, by rfl⟩ : syracuseStep 53340929 = 40005697) B40005697
theorem B3124025 : Blo 1387513 3124025 := bstep (se 2 (by rfl) ⟨1171509, by rfl⟩ : syracuseStep 3124025 = 2343019) B2343019
theorem B7031609 : Blo 1387513 7031609 := bstep (se 2 (by rfl) ⟨2636853, by rfl⟩ : syracuseStep 7031609 = 5273707) B5273707
theorem B2083871 : Blo 1387513 2083871 := bstep (se 1 (by rfl) ⟨1562903, by rfl⟩ : syracuseStep 2083871 = 3125807) B3125807
theorem B1977481 : Blo 1387513 1977481 := bstep (se 2 (by rfl) ⟨741555, by rfl⟩ : syracuseStep 1977481 = 1483111) B1483111
theorem B3337769 : Blo 1387513 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B10694591 : Blo 1387513 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B5926907 : Blo 1387513 5926907 := bstep (se 1 (by rfl) ⟨4445180, by rfl⟩ : syracuseStep 5926907 = 8890361) B8890361
theorem B7024967 : Blo 1387513 7024967 := bstep (se 1 (by rfl) ⟨5268725, by rfl⟩ : syracuseStep 7024967 = 10537451) B10537451
theorem B1389183 : Blo 1387513 1389183 := bstep (se 1 (by rfl) ⟨1041887, by rfl⟩ : syracuseStep 1389183 = 2083775) B2083775
theorem B64116143 : Blo 1387513 64116143 := bstep (se 1 (by rfl) ⟨48087107, by rfl⟩ : syracuseStep 64116143 = 96174215) B96174215
theorem B3512767 : Blo 1387513 3512767 := bstep (se 1 (by rfl) ⟨2634575, by rfl⟩ : syracuseStep 3512767 = 5269151) B5269151
theorem B54114821 : Blo 1387513 54114821 := bstep (se 4 (by rfl) ⟨5073264, by rfl⟩ : syracuseStep 54114821 = 10146529) B10146529
theorem B6093427 : Blo 1387513 6093427 := bstep (se 1 (by rfl) ⟨4570070, by rfl⟩ : syracuseStep 6093427 = 9140141) B9140141
theorem B7912475 : Blo 1387513 7912475 := bstep (se 1 (by rfl) ⟨5934356, by rfl⟩ : syracuseStep 7912475 = 11868713) B11868713
theorem B5274679 : Blo 1387513 5274679 := bstep (se 1 (by rfl) ⟨3956009, by rfl⟩ : syracuseStep 5274679 = 7912019) B7912019
theorem B10682027 : Blo 1387513 10682027 := bstep (se 1 (by rfl) ⟨8011520, by rfl⟩ : syracuseStep 10682027 = 16023041) B16023041
theorem B2342783 : Blo 1387513 2342783 := bstep (se 1 (by rfl) ⟨1757087, by rfl⟩ : syracuseStep 2342783 = 3514175) B3514175
theorem B2965727 : Blo 1387513 2965727 := bstep (se 1 (by rfl) ⟨2224295, by rfl⟩ : syracuseStep 2965727 = 4448591) B4448591
theorem B9012059 : Blo 1387513 9012059 := bstep (se 1 (by rfl) ⟨6759044, by rfl⟩ : syracuseStep 9012059 = 13518089) B13518089
theorem B2082287 : Blo 1387513 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B2082683 : Blo 1387513 2082683 := bstep (se 1 (by rfl) ⟨1562012, by rfl⟩ : syracuseStep 2082683 = 3124025) B3124025
theorem B4687739 : Blo 1387513 4687739 := bstep (se 1 (by rfl) ⟨3515804, by rfl⟩ : syracuseStep 4687739 = 7031609) B7031609
theorem B7121351 : Blo 1387513 7121351 := bstep (se 1 (by rfl) ⟨5341013, by rfl⟩ : syracuseStep 7121351 = 10682027) B10682027
theorem B7129727 : Blo 1387513 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B3951271 : Blo 1387513 3951271 := bstep (se 1 (by rfl) ⟨2963453, by rfl⟩ : syracuseStep 3951271 = 5926907) B5926907
theorem B1387547 : Blo 1387513 1387547 := bstep (se 1 (by rfl) ⟨1040660, by rfl⟩ : syracuseStep 1387547 = 2081321) B2081321
theorem B7032905 : Blo 1387513 7032905 := bstep (se 2 (by rfl) ⟨2637339, by rfl⟩ : syracuseStep 7032905 = 5274679) B5274679
theorem B1388783 : Blo 1387513 1388783 := bstep (se 1 (by rfl) ⟨1041587, by rfl⟩ : syracuseStep 1388783 = 2083175) B2083175
theorem B1389247 : Blo 1387513 1389247 := bstep (se 1 (by rfl) ⟨1041935, by rfl⟩ : syracuseStep 1389247 = 2083871) B2083871
theorem B2225179 : Blo 1387513 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B1561855 : Blo 1387513 1561855 := bstep (se 1 (by rfl) ⟨1171391, by rfl⟩ : syracuseStep 1561855 = 2342783) B2342783
theorem B4683311 : Blo 1387513 4683311 := bstep (se 1 (by rfl) ⟨3512483, by rfl⟩ : syracuseStep 4683311 = 7024967) B7024967
theorem B4683689 : Blo 1387513 4683689 := bstep (se 2 (by rfl) ⟨1756383, by rfl⟩ : syracuseStep 4683689 = 3512767) B3512767
theorem B7903271 : Blo 1387513 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B3512423 : Blo 1387513 3512423 := bstep (se 1 (by rfl) ⟨2634317, by rfl⟩ : syracuseStep 3512423 = 5268635) B5268635
theorem B16881787 : Blo 1387513 16881787 := bstep (se 1 (by rfl) ⟨12661340, by rfl⟩ : syracuseStep 16881787 = 25322681) B25322681
theorem B8124569 : Blo 1387513 8124569 := bstep (se 2 (by rfl) ⟨3046713, by rfl⟩ : syracuseStep 8124569 = 6093427) B6093427
theorem B42744095 : Blo 1387513 42744095 := bstep (se 1 (by rfl) ⟨32058071, by rfl⟩ : syracuseStep 42744095 = 64116143) B64116143
theorem B2636641 : Blo 1387513 2636641 := bstep (se 2 (by rfl) ⟨988740, by rfl⟩ : syracuseStep 2636641 = 1977481) B1977481
theorem B36076547 : Blo 1387513 36076547 := bstep (se 1 (by rfl) ⟨27057410, by rfl⟩ : syracuseStep 36076547 = 54114821) B54114821
theorem B35560619 : Blo 1387513 35560619 := bstep (se 1 (by rfl) ⟨26670464, by rfl⟩ : syracuseStep 35560619 = 53340929) B53340929
theorem B5274983 : Blo 1387513 5274983 := bstep (se 1 (by rfl) ⟨3956237, by rfl⟩ : syracuseStep 5274983 = 7912475) B7912475
theorem B5268361 : Blo 1387513 5268361 := bstep (se 2 (by rfl) ⟨1975635, by rfl⟩ : syracuseStep 5268361 = 3951271) B3951271
theorem B3122207 : Blo 1387513 3122207 := bstep (se 1 (by rfl) ⟨2341655, by rfl⟩ : syracuseStep 3122207 = 4683311) B4683311
theorem B3515521 : Blo 1387513 3515521 := bstep (se 2 (by rfl) ⟨1318320, by rfl⟩ : syracuseStep 3515521 = 2636641) B2636641
theorem B3122459 : Blo 1387513 3122459 := bstep (se 1 (by rfl) ⟨2341844, by rfl⟩ : syracuseStep 3122459 = 4683689) B4683689
theorem B5268847 : Blo 1387513 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B2966905 : Blo 1387513 2966905 := bstep (se 2 (by rfl) ⟨1112589, by rfl⟩ : syracuseStep 2966905 = 2225179) B2225179
theorem B5416379 : Blo 1387513 5416379 := bstep (se 1 (by rfl) ⟨4062284, by rfl⟩ : syracuseStep 5416379 = 8124569) B8124569
theorem B2082473 : Blo 1387513 2082473 := bstep (se 2 (by rfl) ⟨780927, by rfl⟩ : syracuseStep 2082473 = 1561855) B1561855
theorem B4753151 : Blo 1387513 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B3516655 : Blo 1387513 3516655 := bstep (se 1 (by rfl) ⟨2637491, by rfl⟩ : syracuseStep 3516655 = 5274983) B5274983
theorem B4688603 : Blo 1387513 4688603 := bstep (se 1 (by rfl) ⟨3516452, by rfl⟩ : syracuseStep 4688603 = 7032905) B7032905
theorem B1977151 : Blo 1387513 1977151 := bstep (se 1 (by rfl) ⟨1482863, by rfl⟩ : syracuseStep 1977151 = 2965727) B2965727
theorem B6008039 : Blo 1387513 6008039 := bstep (se 1 (by rfl) ⟨4506029, by rfl⟩ : syracuseStep 6008039 = 9012059) B9012059
theorem B1388191 : Blo 1387513 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B1388455 : Blo 1387513 1388455 := bstep (se 1 (by rfl) ⟨1041341, by rfl⟩ : syracuseStep 1388455 = 2082683) B2082683
theorem B3125159 : Blo 1387513 3125159 := bstep (se 1 (by rfl) ⟨2343869, by rfl⟩ : syracuseStep 3125159 = 4687739) B4687739
theorem B28496063 : Blo 1387513 28496063 := bstep (se 1 (by rfl) ⟨21372047, by rfl⟩ : syracuseStep 28496063 = 42744095) B42744095
theorem B4747567 : Blo 1387513 4747567 := bstep (se 1 (by rfl) ⟨3560675, by rfl⟩ : syracuseStep 4747567 = 7121351) B7121351
theorem B96204125 : Blo 1387513 96204125 := bstep (se 3 (by rfl) ⟨18038273, by rfl⟩ : syracuseStep 96204125 = 36076547) B36076547
theorem B22509049 : Blo 1387513 22509049 := bstep (se 2 (by rfl) ⟨8440893, by rfl⟩ : syracuseStep 22509049 = 16881787) B16881787
theorem B2341615 : Blo 1387513 2341615 := bstep (se 1 (by rfl) ⟨1756211, by rfl⟩ : syracuseStep 2341615 = 3512423) B3512423
theorem B23707079 : Blo 1387513 23707079 := bstep (se 1 (by rfl) ⟨17780309, by rfl⟩ : syracuseStep 23707079 = 35560619) B35560619
theorem B75989501 : Blo 1387513 75989501 := bstep (se 3 (by rfl) ⟨14248031, by rfl⟩ : syracuseStep 75989501 = 28496063) B28496063
theorem B2081471 : Blo 1387513 2081471 := bstep (se 1 (by rfl) ⟨1561103, by rfl⟩ : syracuseStep 2081471 = 3122207) B3122207
theorem B2081639 : Blo 1387513 2081639 := bstep (se 1 (by rfl) ⟨1561229, by rfl⟩ : syracuseStep 2081639 = 3122459) B3122459
theorem B64136083 : Blo 1387513 64136083 := bstep (se 1 (by rfl) ⟨48102062, by rfl⟩ : syracuseStep 64136083 = 96204125) B96204125
theorem B3122153 : Blo 1387513 3122153 := bstep (se 2 (by rfl) ⟨1170807, by rfl⟩ : syracuseStep 3122153 = 2341615) B2341615
theorem B4687361 : Blo 1387513 4687361 := bstep (se 2 (by rfl) ⟨1757760, by rfl⟩ : syracuseStep 4687361 = 3515521) B3515521
theorem B15804719 : Blo 1387513 15804719 := bstep (se 1 (by rfl) ⟨11853539, by rfl⟩ : syracuseStep 15804719 = 23707079) B23707079
theorem B2083439 : Blo 1387513 2083439 := bstep (se 1 (by rfl) ⟨1562579, by rfl⟩ : syracuseStep 2083439 = 3125159) B3125159
theorem B4688873 : Blo 1387513 4688873 := bstep (se 2 (by rfl) ⟨1758327, by rfl⟩ : syracuseStep 4688873 = 3516655) B3516655
theorem B1388315 : Blo 1387513 1388315 := bstep (se 1 (by rfl) ⟨1041236, by rfl⟩ : syracuseStep 1388315 = 2082473) B2082473
theorem B7024481 : Blo 1387513 7024481 := bstep (se 2 (by rfl) ⟨2634180, by rfl⟩ : syracuseStep 7024481 = 5268361) B5268361
theorem B7025129 : Blo 1387513 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B3125735 : Blo 1387513 3125735 := bstep (se 1 (by rfl) ⟨2344301, by rfl⟩ : syracuseStep 3125735 = 4688603) B4688603
theorem B30012065 : Blo 1387513 30012065 := bstep (se 2 (by rfl) ⟨11254524, by rfl⟩ : syracuseStep 30012065 = 22509049) B22509049
theorem B6330089 : Blo 1387513 6330089 := bstep (se 2 (by rfl) ⟨2373783, by rfl⟩ : syracuseStep 6330089 = 4747567) B4747567
theorem B3610919 : Blo 1387513 3610919 := bstep (se 1 (by rfl) ⟨2708189, by rfl⟩ : syracuseStep 3610919 = 5416379) B5416379
theorem B2636201 : Blo 1387513 2636201 := bstep (se 2 (by rfl) ⟨988575, by rfl⟩ : syracuseStep 2636201 = 1977151) B1977151
theorem B3168767 : Blo 1387513 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B3955873 : Blo 1387513 3955873 := bstep (se 2 (by rfl) ⟨1483452, by rfl⟩ : syracuseStep 3955873 = 2966905) B2966905
theorem B4005359 : Blo 1387513 4005359 := bstep (se 1 (by rfl) ⟨3004019, by rfl⟩ : syracuseStep 4005359 = 6008039) B6008039
theorem B50659667 : Blo 1387513 50659667 := bstep (se 1 (by rfl) ⟨37994750, by rfl⟩ : syracuseStep 50659667 = 75989501) B75989501
theorem B2081435 : Blo 1387513 2081435 := bstep (se 1 (by rfl) ⟨1561076, by rfl⟩ : syracuseStep 2081435 = 3122153) B3122153
theorem B10536479 : Blo 1387513 10536479 := bstep (se 1 (by rfl) ⟨7902359, by rfl⟩ : syracuseStep 10536479 = 15804719) B15804719
theorem B2083823 : Blo 1387513 2083823 := bstep (se 1 (by rfl) ⟨1562867, by rfl⟩ : syracuseStep 2083823 = 3125735) B3125735
theorem B20008043 : Blo 1387513 20008043 := bstep (se 1 (by rfl) ⟨15006032, by rfl⟩ : syracuseStep 20008043 = 30012065) B30012065
theorem B1387647 : Blo 1387513 1387647 := bstep (se 1 (by rfl) ⟨1040735, by rfl⟩ : syracuseStep 1387647 = 2081471) B2081471
theorem B1387759 : Blo 1387513 1387759 := bstep (se 1 (by rfl) ⟨1040819, by rfl⟩ : syracuseStep 1387759 = 2081639) B2081639
theorem B9629117 : Blo 1387513 9629117 := bstep (se 3 (by rfl) ⟨1805459, by rfl⟩ : syracuseStep 9629117 = 3610919) B3610919
theorem B3124907 : Blo 1387513 3124907 := bstep (se 1 (by rfl) ⟨2343680, by rfl⟩ : syracuseStep 3124907 = 4687361) B4687361
theorem B8450045 : Blo 1387513 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B1757467 : Blo 1387513 1757467 := bstep (se 1 (by rfl) ⟨1318100, by rfl⟩ : syracuseStep 1757467 = 2636201) B2636201
theorem B1388959 : Blo 1387513 1388959 := bstep (se 1 (by rfl) ⟨1041719, by rfl⟩ : syracuseStep 1388959 = 2083439) B2083439
theorem B16880237 : Blo 1387513 16880237 := bstep (se 3 (by rfl) ⟨3165044, by rfl⟩ : syracuseStep 16880237 = 6330089) B6330089
theorem B3125915 : Blo 1387513 3125915 := bstep (se 1 (by rfl) ⟨2344436, by rfl⟩ : syracuseStep 3125915 = 4688873) B4688873
theorem B4682987 : Blo 1387513 4682987 := bstep (se 1 (by rfl) ⟨3512240, by rfl⟩ : syracuseStep 4682987 = 7024481) B7024481
theorem B4683419 : Blo 1387513 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B85514777 : Blo 1387513 85514777 := bstep (se 2 (by rfl) ⟨32068041, by rfl⟩ : syracuseStep 85514777 = 64136083) B64136083
theorem B5274497 : Blo 1387513 5274497 := bstep (se 2 (by rfl) ⟨1977936, by rfl⟩ : syracuseStep 5274497 = 3955873) B3955873
theorem B2670239 : Blo 1387513 2670239 := bstep (se 1 (by rfl) ⟨2002679, by rfl⟩ : syracuseStep 2670239 = 4005359) B4005359
theorem B2343289 : Blo 1387513 2343289 := bstep (se 2 (by rfl) ⟨878733, by rfl⟩ : syracuseStep 2343289 = 1757467) B1757467
theorem B3121991 : Blo 1387513 3121991 := bstep (se 1 (by rfl) ⟨2341493, by rfl⟩ : syracuseStep 3121991 = 4682987) B4682987
theorem B3122279 : Blo 1387513 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B57009851 : Blo 1387513 57009851 := bstep (se 1 (by rfl) ⟨42757388, by rfl⟩ : syracuseStep 57009851 = 85514777) B85514777
theorem B3516331 : Blo 1387513 3516331 := bstep (se 1 (by rfl) ⟨2637248, by rfl⟩ : syracuseStep 3516331 = 5274497) B5274497
theorem B13338695 : Blo 1387513 13338695 := bstep (se 1 (by rfl) ⟨10004021, by rfl⟩ : syracuseStep 13338695 = 20008043) B20008043
theorem B1780159 : Blo 1387513 1780159 := bstep (se 1 (by rfl) ⟨1335119, by rfl⟩ : syracuseStep 1780159 = 2670239) B2670239
theorem B2083271 : Blo 1387513 2083271 := bstep (se 1 (by rfl) ⟨1562453, by rfl⟩ : syracuseStep 2083271 = 3124907) B3124907
theorem B1387623 : Blo 1387513 1387623 := bstep (se 1 (by rfl) ⟨1040717, by rfl⟩ : syracuseStep 1387623 = 2081435) B2081435
theorem B2083943 : Blo 1387513 2083943 := bstep (se 1 (by rfl) ⟨1562957, by rfl⟩ : syracuseStep 2083943 = 3125915) B3125915
theorem B7024319 : Blo 1387513 7024319 := bstep (se 1 (by rfl) ⟨5268239, by rfl⟩ : syracuseStep 7024319 = 10536479) B10536479
theorem B1389215 : Blo 1387513 1389215 := bstep (se 1 (by rfl) ⟨1041911, by rfl⟩ : syracuseStep 1389215 = 2083823) B2083823
theorem B6419411 : Blo 1387513 6419411 := bstep (se 1 (by rfl) ⟨4814558, by rfl⟩ : syracuseStep 6419411 = 9629117) B9629117
theorem B5633363 : Blo 1387513 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B33773111 : Blo 1387513 33773111 := bstep (se 1 (by rfl) ⟨25329833, by rfl⟩ : syracuseStep 33773111 = 50659667) B50659667
theorem B11253491 : Blo 1387513 11253491 := bstep (se 1 (by rfl) ⟨8440118, by rfl⟩ : syracuseStep 11253491 = 16880237) B16880237
theorem B2081327 : Blo 1387513 2081327 := bstep (se 1 (by rfl) ⟨1560995, by rfl⟩ : syracuseStep 2081327 = 3121991) B3121991
theorem B2081519 : Blo 1387513 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B4688441 : Blo 1387513 4688441 := bstep (se 2 (by rfl) ⟨1758165, by rfl⟩ : syracuseStep 4688441 = 3516331) B3516331
theorem B3124385 : Blo 1387513 3124385 := bstep (se 2 (by rfl) ⟨1171644, by rfl⟩ : syracuseStep 3124385 = 2343289) B2343289
theorem B4279607 : Blo 1387513 4279607 := bstep (se 1 (by rfl) ⟨3209705, by rfl⟩ : syracuseStep 4279607 = 6419411) B6419411
theorem B3755575 : Blo 1387513 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B22515407 : Blo 1387513 22515407 := bstep (se 1 (by rfl) ⟨16886555, by rfl⟩ : syracuseStep 22515407 = 33773111) B33773111
theorem B38006567 : Blo 1387513 38006567 := bstep (se 1 (by rfl) ⟨28504925, by rfl⟩ : syracuseStep 38006567 = 57009851) B57009851
theorem B8892463 : Blo 1387513 8892463 := bstep (se 1 (by rfl) ⟨6669347, by rfl⟩ : syracuseStep 8892463 = 13338695) B13338695
theorem B1388847 : Blo 1387513 1388847 := bstep (se 1 (by rfl) ⟨1041635, by rfl⟩ : syracuseStep 1388847 = 2083271) B2083271
theorem B1389295 : Blo 1387513 1389295 := bstep (se 1 (by rfl) ⟨1041971, by rfl⟩ : syracuseStep 1389295 = 2083943) B2083943
theorem B4682879 : Blo 1387513 4682879 := bstep (se 1 (by rfl) ⟨3512159, by rfl⟩ : syracuseStep 4682879 = 7024319) B7024319
theorem B2373545 : Blo 1387513 2373545 := bstep (se 2 (by rfl) ⟨890079, by rfl⟩ : syracuseStep 2373545 = 1780159) B1780159
theorem B7502327 : Blo 1387513 7502327 := bstep (se 1 (by rfl) ⟨5626745, by rfl⟩ : syracuseStep 7502327 = 11253491) B11253491
theorem B3121919 : Blo 1387513 3121919 := bstep (se 1 (by rfl) ⟨2341439, by rfl⟩ : syracuseStep 3121919 = 4682879) B4682879
theorem B1582363 : Blo 1387513 1582363 := bstep (se 1 (by rfl) ⟨1186772, by rfl⟩ : syracuseStep 1582363 = 2373545) B2373545
theorem B5007433 : Blo 1387513 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B2082923 : Blo 1387513 2082923 := bstep (se 1 (by rfl) ⟨1562192, by rfl⟩ : syracuseStep 2082923 = 3124385) B3124385
theorem B2853071 : Blo 1387513 2853071 := bstep (se 1 (by rfl) ⟨2139803, by rfl⟩ : syracuseStep 2853071 = 4279607) B4279607
theorem B15010271 : Blo 1387513 15010271 := bstep (se 1 (by rfl) ⟨11257703, by rfl⟩ : syracuseStep 15010271 = 22515407) B22515407
theorem B11856617 : Blo 1387513 11856617 := bstep (se 2 (by rfl) ⟨4446231, by rfl⟩ : syracuseStep 11856617 = 8892463) B8892463
theorem B1387551 : Blo 1387513 1387551 := bstep (se 1 (by rfl) ⟨1040663, by rfl⟩ : syracuseStep 1387551 = 2081327) B2081327
theorem B1387679 : Blo 1387513 1387679 := bstep (se 1 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 1387679 = 2081519) B2081519
theorem B5001551 : Blo 1387513 5001551 := bstep (se 1 (by rfl) ⟨3751163, by rfl⟩ : syracuseStep 5001551 = 7502327) B7502327
theorem B3125627 : Blo 1387513 3125627 := bstep (se 1 (by rfl) ⟨2344220, by rfl⟩ : syracuseStep 3125627 = 4688441) B4688441
theorem B25337711 : Blo 1387513 25337711 := bstep (se 1 (by rfl) ⟨19003283, by rfl⟩ : syracuseStep 25337711 = 38006567) B38006567
theorem B6676577 : Blo 1387513 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B3334367 : Blo 1387513 3334367 := bstep (se 1 (by rfl) ⟨2500775, by rfl⟩ : syracuseStep 3334367 = 5001551) B5001551
theorem B2081279 : Blo 1387513 2081279 := bstep (se 1 (by rfl) ⟨1560959, by rfl⟩ : syracuseStep 2081279 = 3121919) B3121919
theorem B1902047 : Blo 1387513 1902047 := bstep (se 1 (by rfl) ⟨1426535, by rfl⟩ : syracuseStep 1902047 = 2853071) B2853071
theorem B2083751 : Blo 1387513 2083751 := bstep (se 1 (by rfl) ⟨1562813, by rfl⟩ : syracuseStep 2083751 = 3125627) B3125627
theorem B1388615 : Blo 1387513 1388615 := bstep (se 1 (by rfl) ⟨1041461, by rfl⟩ : syracuseStep 1388615 = 2082923) B2082923
theorem B10006847 : Blo 1387513 10006847 := bstep (se 1 (by rfl) ⟨7505135, by rfl⟩ : syracuseStep 10006847 = 15010271) B15010271
theorem B2109817 : Blo 1387513 2109817 := bstep (se 2 (by rfl) ⟨791181, by rfl⟩ : syracuseStep 2109817 = 1582363) B1582363
theorem B7904411 : Blo 1387513 7904411 := bstep (se 1 (by rfl) ⟨5928308, by rfl⟩ : syracuseStep 7904411 = 11856617) B11856617
theorem B67567229 : Blo 1387513 67567229 := bstep (se 3 (by rfl) ⟨12668855, by rfl⟩ : syracuseStep 67567229 = 25337711) B25337711
theorem B5269607 : Blo 1387513 5269607 := bstep (se 1 (by rfl) ⟨3952205, by rfl⟩ : syracuseStep 5269607 = 7904411) B7904411
theorem B4451051 : Blo 1387513 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B2222911 : Blo 1387513 2222911 := bstep (se 1 (by rfl) ⟨1667183, by rfl⟩ : syracuseStep 2222911 = 3334367) B3334367
theorem B6671231 : Blo 1387513 6671231 := bstep (se 1 (by rfl) ⟨5003423, by rfl⟩ : syracuseStep 6671231 = 10006847) B10006847
theorem B1387519 : Blo 1387513 1387519 := bstep (se 1 (by rfl) ⟨1040639, by rfl⟩ : syracuseStep 1387519 = 2081279) B2081279
theorem B1389167 : Blo 1387513 1389167 := bstep (se 1 (by rfl) ⟨1041875, by rfl⟩ : syracuseStep 1389167 = 2083751) B2083751
theorem B11252357 : Blo 1387513 11252357 := bstep (se 4 (by rfl) ⟨1054908, by rfl⟩ : syracuseStep 11252357 = 2109817) B2109817
theorem B20288501 : Blo 1387513 20288501 := bstep (se 5 (by rfl) ⟨951023, by rfl⟩ : syracuseStep 20288501 = 1902047) B1902047
theorem B45044819 : Blo 1387513 45044819 := bstep (se 1 (by rfl) ⟨33783614, by rfl⟩ : syracuseStep 45044819 = 67567229) B67567229
theorem B13525667 : Blo 1387513 13525667 := bstep (se 1 (by rfl) ⟨10144250, by rfl⟩ : syracuseStep 13525667 = 20288501) B20288501
theorem B2967367 : Blo 1387513 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B7501571 : Blo 1387513 7501571 := bstep (se 1 (by rfl) ⟨5626178, by rfl⟩ : syracuseStep 7501571 = 11252357) B11252357
theorem B30029879 : Blo 1387513 30029879 := bstep (se 1 (by rfl) ⟨22522409, by rfl⟩ : syracuseStep 30029879 = 45044819) B45044819
theorem B2963881 : Blo 1387513 2963881 := bstep (se 2 (by rfl) ⟨1111455, by rfl⟩ : syracuseStep 2963881 = 2222911) B2222911
theorem B3513071 : Blo 1387513 3513071 := bstep (se 1 (by rfl) ⟨2634803, by rfl⟩ : syracuseStep 3513071 = 5269607) B5269607
theorem B4447487 : Blo 1387513 4447487 := bstep (se 1 (by rfl) ⟨3335615, by rfl⟩ : syracuseStep 4447487 = 6671231) B6671231
theorem B3951841 : Blo 1387513 3951841 := bstep (se 2 (by rfl) ⟨1481940, by rfl⟩ : syracuseStep 3951841 = 2963881) B2963881
theorem B5001047 : Blo 1387513 5001047 := bstep (se 1 (by rfl) ⟨3750785, by rfl⟩ : syracuseStep 5001047 = 7501571) B7501571
theorem B9017111 : Blo 1387513 9017111 := bstep (se 1 (by rfl) ⟨6762833, by rfl⟩ : syracuseStep 9017111 = 13525667) B13525667
theorem B11859965 : Blo 1387513 11859965 := bstep (se 3 (by rfl) ⟨2223743, by rfl⟩ : syracuseStep 11859965 = 4447487) B4447487
theorem B20019919 : Blo 1387513 20019919 := bstep (se 1 (by rfl) ⟨15014939, by rfl⟩ : syracuseStep 20019919 = 30029879) B30029879
theorem B2342047 : Blo 1387513 2342047 := bstep (se 1 (by rfl) ⟨1756535, by rfl⟩ : syracuseStep 2342047 = 3513071) B3513071
theorem B3956489 : Blo 1387513 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B384730069 : Blo 1387513 384730069 := bstep (se 7 (by rfl) ⟨4508555, by rfl⟩ : syracuseStep 384730069 = 9017111) B9017111
theorem B7906643 : Blo 1387513 7906643 := bstep (se 1 (by rfl) ⟨5929982, by rfl⟩ : syracuseStep 7906643 = 11859965) B11859965
theorem B3122729 : Blo 1387513 3122729 := bstep (se 2 (by rfl) ⟨1171023, by rfl⟩ : syracuseStep 3122729 = 2342047) B2342047
theorem B5269121 : Blo 1387513 5269121 := bstep (se 2 (by rfl) ⟨1975920, by rfl⟩ : syracuseStep 5269121 = 3951841) B3951841
theorem B26693225 : Blo 1387513 26693225 := bstep (se 2 (by rfl) ⟨10009959, by rfl⟩ : syracuseStep 26693225 = 20019919) B20019919
theorem B2637659 : Blo 1387513 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B3334031 : Blo 1387513 3334031 := bstep (se 1 (by rfl) ⟨2500523, by rfl⟩ : syracuseStep 3334031 = 5001047) B5001047
theorem B2081819 : Blo 1387513 2081819 := bstep (se 1 (by rfl) ⟨1561364, by rfl⟩ : syracuseStep 2081819 = 3122729) B3122729
theorem B17795483 : Blo 1387513 17795483 := bstep (se 1 (by rfl) ⟨13346612, by rfl⟩ : syracuseStep 17795483 = 26693225) B26693225
theorem B2222687 : Blo 1387513 2222687 := bstep (se 1 (by rfl) ⟨1667015, by rfl⟩ : syracuseStep 2222687 = 3334031) B3334031
theorem B5271095 : Blo 1387513 5271095 := bstep (se 1 (by rfl) ⟨3953321, by rfl⟩ : syracuseStep 5271095 = 7906643) B7906643
theorem B1758439 : Blo 1387513 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B3512747 : Blo 1387513 3512747 := bstep (se 1 (by rfl) ⟨2634560, by rfl⟩ : syracuseStep 3512747 = 5269121) B5269121
theorem B512973425 : Blo 1387513 512973425 := bstep (se 2 (by rfl) ⟨192365034, by rfl⟩ : syracuseStep 512973425 = 384730069) B384730069
theorem B11863655 : Blo 1387513 11863655 := bstep (se 1 (by rfl) ⟨8897741, by rfl⟩ : syracuseStep 11863655 = 17795483) B17795483
theorem B2344585 : Blo 1387513 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B1387879 : Blo 1387513 1387879 := bstep (se 1 (by rfl) ⟨1040909, by rfl⟩ : syracuseStep 1387879 = 2081819) B2081819
theorem B5927165 : Blo 1387513 5927165 := bstep (se 3 (by rfl) ⟨1111343, by rfl⟩ : syracuseStep 5927165 = 2222687) B2222687
theorem B2341831 : Blo 1387513 2341831 := bstep (se 1 (by rfl) ⟨1756373, by rfl⟩ : syracuseStep 2341831 = 3512747) B3512747
theorem B341982283 : Blo 1387513 341982283 := bstep (se 1 (by rfl) ⟨256486712, by rfl⟩ : syracuseStep 341982283 = 512973425) B512973425
theorem B3514063 : Blo 1387513 3514063 := bstep (se 1 (by rfl) ⟨2635547, by rfl⟩ : syracuseStep 3514063 = 5271095) B5271095
theorem B3122441 : Blo 1387513 3122441 := bstep (se 2 (by rfl) ⟨1170915, by rfl⟩ : syracuseStep 3122441 = 2341831) B2341831
theorem B455976377 : Blo 1387513 455976377 := bstep (se 2 (by rfl) ⟨170991141, by rfl⟩ : syracuseStep 455976377 = 341982283) B341982283
theorem B3951443 : Blo 1387513 3951443 := bstep (se 1 (by rfl) ⟨2963582, by rfl⟩ : syracuseStep 3951443 = 5927165) B5927165
theorem B7909103 : Blo 1387513 7909103 := bstep (se 1 (by rfl) ⟨5931827, by rfl⟩ : syracuseStep 7909103 = 11863655) B11863655
theorem B3126113 : Blo 1387513 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B4685417 : Blo 1387513 4685417 := bstep (se 2 (by rfl) ⟨1757031, by rfl⟩ : syracuseStep 4685417 = 3514063) B3514063
theorem B2081627 : Blo 1387513 2081627 := bstep (se 1 (by rfl) ⟨1561220, by rfl⟩ : syracuseStep 2081627 = 3122441) B3122441
theorem B3123611 : Blo 1387513 3123611 := bstep (se 1 (by rfl) ⟨2342708, by rfl⟩ : syracuseStep 3123611 = 4685417) B4685417
theorem B2084075 : Blo 1387513 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B303984251 : Blo 1387513 303984251 := bstep (se 1 (by rfl) ⟨227988188, by rfl⟩ : syracuseStep 303984251 = 455976377) B455976377
theorem B2634295 : Blo 1387513 2634295 := bstep (se 1 (by rfl) ⟨1975721, by rfl⟩ : syracuseStep 2634295 = 3951443) B3951443
theorem B5272735 : Blo 1387513 5272735 := bstep (se 1 (by rfl) ⟨3954551, by rfl⟩ : syracuseStep 5272735 = 7909103) B7909103
theorem B7030313 : Blo 1387513 7030313 := bstep (se 2 (by rfl) ⟨2636367, by rfl⟩ : syracuseStep 7030313 = 5272735) B5272735
theorem B2082407 : Blo 1387513 2082407 := bstep (se 1 (by rfl) ⟨1561805, by rfl⟩ : syracuseStep 2082407 = 3123611) B3123611
theorem B202656167 : Blo 1387513 202656167 := bstep (se 1 (by rfl) ⟨151992125, by rfl⟩ : syracuseStep 202656167 = 303984251) B303984251
theorem B1387751 : Blo 1387513 1387751 := bstep (se 1 (by rfl) ⟨1040813, by rfl⟩ : syracuseStep 1387751 = 2081627) B2081627
theorem B1389383 : Blo 1387513 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B3512393 : Blo 1387513 3512393 := bstep (se 2 (by rfl) ⟨1317147, by rfl⟩ : syracuseStep 3512393 = 2634295) B2634295
theorem B4686875 : Blo 1387513 4686875 := bstep (se 1 (by rfl) ⟨3515156, by rfl⟩ : syracuseStep 4686875 = 7030313) B7030313
theorem B135104111 : Blo 1387513 135104111 := bstep (se 1 (by rfl) ⟨101328083, by rfl⟩ : syracuseStep 135104111 = 202656167) B202656167
theorem B1388271 : Blo 1387513 1388271 := bstep (se 1 (by rfl) ⟨1041203, by rfl⟩ : syracuseStep 1388271 = 2082407) B2082407
theorem B2341595 : Blo 1387513 2341595 := bstep (se 1 (by rfl) ⟨1756196, by rfl⟩ : syracuseStep 2341595 = 3512393) B3512393
theorem B3124583 : Blo 1387513 3124583 := bstep (se 1 (by rfl) ⟨2343437, by rfl⟩ : syracuseStep 3124583 = 4686875) B4686875
theorem B1561063 : Blo 1387513 1561063 := bstep (se 1 (by rfl) ⟨1170797, by rfl⟩ : syracuseStep 1561063 = 2341595) B2341595
theorem B90069407 : Blo 1387513 90069407 := bstep (se 1 (by rfl) ⟨67552055, by rfl⟩ : syracuseStep 90069407 = 135104111) B135104111
theorem B2081417 : Blo 1387513 2081417 := bstep (se 2 (by rfl) ⟨780531, by rfl⟩ : syracuseStep 2081417 = 1561063) B1561063
theorem B2083055 : Blo 1387513 2083055 := bstep (se 1 (by rfl) ⟨1562291, by rfl⟩ : syracuseStep 2083055 = 3124583) B3124583
theorem B60046271 : Blo 1387513 60046271 := bstep (se 1 (by rfl) ⟨45034703, by rfl⟩ : syracuseStep 60046271 = 90069407) B90069407
theorem B1387611 : Blo 1387513 1387611 := bstep (se 1 (by rfl) ⟨1040708, by rfl⟩ : syracuseStep 1387611 = 2081417) B2081417
theorem B1388703 : Blo 1387513 1388703 := bstep (se 1 (by rfl) ⟨1041527, by rfl⟩ : syracuseStep 1388703 = 2083055) B2083055
theorem B40030847 : Blo 1387513 40030847 := bstep (se 1 (by rfl) ⟨30023135, by rfl⟩ : syracuseStep 40030847 = 60046271) B60046271
theorem B26687231 : Blo 1387513 26687231 := bstep (se 1 (by rfl) ⟨20015423, by rfl⟩ : syracuseStep 26687231 = 40030847) B40030847
theorem B17791487 : Blo 1387513 17791487 := bstep (se 1 (by rfl) ⟨13343615, by rfl⟩ : syracuseStep 17791487 = 26687231) B26687231
theorem B11860991 : Blo 1387513 11860991 := bstep (se 1 (by rfl) ⟨8895743, by rfl⟩ : syracuseStep 11860991 = 17791487) B17791487
theorem B7907327 : Blo 1387513 7907327 := bstep (se 1 (by rfl) ⟨5930495, by rfl⟩ : syracuseStep 7907327 = 11860991) B11860991
theorem B5271551 : Blo 1387513 5271551 := bstep (se 1 (by rfl) ⟨3953663, by rfl⟩ : syracuseStep 5271551 = 7907327) B7907327
theorem B3514367 : Blo 1387513 3514367 := bstep (se 1 (by rfl) ⟨2635775, by rfl⟩ : syracuseStep 3514367 = 5271551) B5271551
theorem B2342911 : Blo 1387513 2342911 := bstep (se 1 (by rfl) ⟨1757183, by rfl⟩ : syracuseStep 2342911 = 3514367) B3514367
theorem B3123881 : Blo 1387513 3123881 := bstep (se 2 (by rfl) ⟨1171455, by rfl⟩ : syracuseStep 3123881 = 2342911) B2342911
theorem B2082587 : Blo 1387513 2082587 := bstep (se 1 (by rfl) ⟨1561940, by rfl⟩ : syracuseStep 2082587 = 3123881) B3123881
theorem B1388391 : Blo 1387513 1388391 := bstep (se 1 (by rfl) ⟨1041293, by rfl⟩ : syracuseStep 1388391 = 2082587) B2082587

theorem C0 (j : ℕ) (h1 : 346878 ≤ j) (h2 : j ≤ 347377) : Blo 1387513 (4 * j + 3) := by
  interval_cases j
  · exact B1387515
  · exact B1387519
  · exact B1387523
  · exact B1387527
  · exact B1387531
  · exact B1387535
  · exact B1387539
  · exact B1387543
  · exact B1387547
  · exact B1387551
  · exact B1387555
  · exact B1387559
  · exact B1387563
  · exact B1387567
  · exact B1387571
  · exact B1387575
  · exact B1387579
  · exact B1387583
  · exact B1387587
  · exact B1387591
  · exact B1387595
  · exact B1387599
  · exact B1387603
  · exact B1387607
  · exact B1387611
  · exact B1387615
  · exact B1387619
  · exact B1387623
  · exact B1387627
  · exact B1387631
  · exact B1387635
  · exact B1387639
  · exact B1387643
  · exact B1387647
  · exact B1387651
  · exact B1387655
  · exact B1387659
  · exact B1387663
  · exact B1387667
  · exact B1387671
  · exact B1387675
  · exact B1387679
  · exact B1387683
  · exact B1387687
  · exact B1387691
  · exact B1387695
  · exact B1387699
  · exact B1387703
  · exact B1387707
  · exact B1387711
  · exact B1387715
  · exact B1387719
  · exact B1387723
  · exact B1387727
  · exact B1387731
  · exact B1387735
  · exact B1387739
  · exact B1387743
  · exact B1387747
  · exact B1387751
  · exact B1387755
  · exact B1387759
  · exact B1387763
  · exact B1387767
  · exact B1387771
  · exact B1387775
  · exact B1387779
  · exact B1387783
  · exact B1387787
  · exact B1387791
  · exact B1387795
  · exact B1387799
  · exact B1387803
  · exact B1387807
  · exact B1387811
  · exact B1387815
  · exact B1387819
  · exact B1387823
  · exact B1387827
  · exact B1387831
  · exact B1387835
  · exact B1387839
  · exact B1387843
  · exact B1387847
  · exact B1387851
  · exact B1387855
  · exact B1387859
  · exact B1387863
  · exact B1387867
  · exact B1387871
  · exact B1387875
  · exact B1387879
  · exact B1387883
  · exact B1387887
  · exact B1387891
  · exact B1387895
  · exact B1387899
  · exact B1387903
  · exact B1387907
  · exact B1387911
  · exact B1387915
  · exact B1387919
  · exact B1387923
  · exact B1387927
  · exact B1387931
  · exact B1387935
  · exact B1387939
  · exact B1387943
  · exact B1387947
  · exact B1387951
  · exact B1387955
  · exact B1387959
  · exact B1387963
  · exact B1387967
  · exact B1387971
  · exact B1387975
  · exact B1387979
  · exact B1387983
  · exact B1387987
  · exact B1387991
  · exact B1387995
  · exact B1387999
  · exact B1388003
  · exact B1388007
  · exact B1388011
  · exact B1388015
  · exact B1388019
  · exact B1388023
  · exact B1388027
  · exact B1388031
  · exact B1388035
  · exact B1388039
  · exact B1388043
  · exact B1388047
  · exact B1388051
  · exact B1388055
  · exact B1388059
  · exact B1388063
  · exact B1388067
  · exact B1388071
  · exact B1388075
  · exact B1388079
  · exact B1388083
  · exact B1388087
  · exact B1388091
  · exact B1388095
  · exact B1388099
  · exact B1388103
  · exact B1388107
  · exact B1388111
  · exact B1388115
  · exact B1388119
  · exact B1388123
  · exact B1388127
  · exact B1388131
  · exact B1388135
  · exact B1388139
  · exact B1388143
  · exact B1388147
  · exact B1388151
  · exact B1388155
  · exact B1388159
  · exact B1388163
  · exact B1388167
  · exact B1388171
  · exact B1388175
  · exact B1388179
  · exact B1388183
  · exact B1388187
  · exact B1388191
  · exact B1388195
  · exact B1388199
  · exact B1388203
  · exact B1388207
  · exact B1388211
  · exact B1388215
  · exact B1388219
  · exact B1388223
  · exact B1388227
  · exact B1388231
  · exact B1388235
  · exact B1388239
  · exact B1388243
  · exact B1388247
  · exact B1388251
  · exact B1388255
  · exact B1388259
  · exact B1388263
  · exact B1388267
  · exact B1388271
  · exact B1388275
  · exact B1388279
  · exact B1388283
  · exact B1388287
  · exact B1388291
  · exact B1388295
  · exact B1388299
  · exact B1388303
  · exact B1388307
  · exact B1388311
  · exact B1388315
  · exact B1388319
  · exact B1388323
  · exact B1388327
  · exact B1388331
  · exact B1388335
  · exact B1388339
  · exact B1388343
  · exact B1388347
  · exact B1388351
  · exact B1388355
  · exact B1388359
  · exact B1388363
  · exact B1388367
  · exact B1388371
  · exact B1388375
  · exact B1388379
  · exact B1388383
  · exact B1388387
  · exact B1388391
  · exact B1388395
  · exact B1388399
  · exact B1388403
  · exact B1388407
  · exact B1388411
  · exact B1388415
  · exact B1388419
  · exact B1388423
  · exact B1388427
  · exact B1388431
  · exact B1388435
  · exact B1388439
  · exact B1388443
  · exact B1388447
  · exact B1388451
  · exact B1388455
  · exact B1388459
  · exact B1388463
  · exact B1388467
  · exact B1388471
  · exact B1388475
  · exact B1388479
  · exact B1388483
  · exact B1388487
  · exact B1388491
  · exact B1388495
  · exact B1388499
  · exact B1388503
  · exact B1388507
  · exact B1388511
  · exact B1388515
  · exact B1388519
  · exact B1388523
  · exact B1388527
  · exact B1388531
  · exact B1388535
  · exact B1388539
  · exact B1388543
  · exact B1388547
  · exact B1388551
  · exact B1388555
  · exact B1388559
  · exact B1388563
  · exact B1388567
  · exact B1388571
  · exact B1388575
  · exact B1388579
  · exact B1388583
  · exact B1388587
  · exact B1388591
  · exact B1388595
  · exact B1388599
  · exact B1388603
  · exact B1388607
  · exact B1388611
  · exact B1388615
  · exact B1388619
  · exact B1388623
  · exact B1388627
  · exact B1388631
  · exact B1388635
  · exact B1388639
  · exact B1388643
  · exact B1388647
  · exact B1388651
  · exact B1388655
  · exact B1388659
  · exact B1388663
  · exact B1388667
  · exact B1388671
  · exact B1388675
  · exact B1388679
  · exact B1388683
  · exact B1388687
  · exact B1388691
  · exact B1388695
  · exact B1388699
  · exact B1388703
  · exact B1388707
  · exact B1388711
  · exact B1388715
  · exact B1388719
  · exact B1388723
  · exact B1388727
  · exact B1388731
  · exact B1388735
  · exact B1388739
  · exact B1388743
  · exact B1388747
  · exact B1388751
  · exact B1388755
  · exact B1388759
  · exact B1388763
  · exact B1388767
  · exact B1388771
  · exact B1388775
  · exact B1388779
  · exact B1388783
  · exact B1388787
  · exact B1388791
  · exact B1388795
  · exact B1388799
  · exact B1388803
  · exact B1388807
  · exact B1388811
  · exact B1388815
  · exact B1388819
  · exact B1388823
  · exact B1388827
  · exact B1388831
  · exact B1388835
  · exact B1388839
  · exact B1388843
  · exact B1388847
  · exact B1388851
  · exact B1388855
  · exact B1388859
  · exact B1388863
  · exact B1388867
  · exact B1388871
  · exact B1388875
  · exact B1388879
  · exact B1388883
  · exact B1388887
  · exact B1388891
  · exact B1388895
  · exact B1388899
  · exact B1388903
  · exact B1388907
  · exact B1388911
  · exact B1388915
  · exact B1388919
  · exact B1388923
  · exact B1388927
  · exact B1388931
  · exact B1388935
  · exact B1388939
  · exact B1388943
  · exact B1388947
  · exact B1388951
  · exact B1388955
  · exact B1388959
  · exact B1388963
  · exact B1388967
  · exact B1388971
  · exact B1388975
  · exact B1388979
  · exact B1388983
  · exact B1388987
  · exact B1388991
  · exact B1388995
  · exact B1388999
  · exact B1389003
  · exact B1389007
  · exact B1389011
  · exact B1389015
  · exact B1389019
  · exact B1389023
  · exact B1389027
  · exact B1389031
  · exact B1389035
  · exact B1389039
  · exact B1389043
  · exact B1389047
  · exact B1389051
  · exact B1389055
  · exact B1389059
  · exact B1389063
  · exact B1389067
  · exact B1389071
  · exact B1389075
  · exact B1389079
  · exact B1389083
  · exact B1389087
  · exact B1389091
  · exact B1389095
  · exact B1389099
  · exact B1389103
  · exact B1389107
  · exact B1389111
  · exact B1389115
  · exact B1389119
  · exact B1389123
  · exact B1389127
  · exact B1389131
  · exact B1389135
  · exact B1389139
  · exact B1389143
  · exact B1389147
  · exact B1389151
  · exact B1389155
  · exact B1389159
  · exact B1389163
  · exact B1389167
  · exact B1389171
  · exact B1389175
  · exact B1389179
  · exact B1389183
  · exact B1389187
  · exact B1389191
  · exact B1389195
  · exact B1389199
  · exact B1389203
  · exact B1389207
  · exact B1389211
  · exact B1389215
  · exact B1389219
  · exact B1389223
  · exact B1389227
  · exact B1389231
  · exact B1389235
  · exact B1389239
  · exact B1389243
  · exact B1389247
  · exact B1389251
  · exact B1389255
  · exact B1389259
  · exact B1389263
  · exact B1389267
  · exact B1389271
  · exact B1389275
  · exact B1389279
  · exact B1389283
  · exact B1389287
  · exact B1389291
  · exact B1389295
  · exact B1389299
  · exact B1389303
  · exact B1389307
  · exact B1389311
  · exact B1389315
  · exact B1389319
  · exact B1389323
  · exact B1389327
  · exact B1389331
  · exact B1389335
  · exact B1389339
  · exact B1389343
  · exact B1389347
  · exact B1389351
  · exact B1389355
  · exact B1389359
  · exact B1389363
  · exact B1389367
  · exact B1389371
  · exact B1389375
  · exact B1389379
  · exact B1389383
  · exact B1389387
  · exact B1389391
  · exact B1389395
  · exact B1389399
  · exact B1389403
  · exact B1389407
  · exact B1389411
  · exact B1389415
  · exact B1389419
  · exact B1389423
  · exact B1389427
  · exact B1389431
  · exact B1389435
  · exact B1389439
  · exact B1389443
  · exact B1389447
  · exact B1389451
  · exact B1389455
  · exact B1389459
  · exact B1389463
  · exact B1389467
  · exact B1389471
  · exact B1389475
  · exact B1389479
  · exact B1389483
  · exact B1389487
  · exact B1389491
  · exact B1389495
  · exact B1389499
  · exact B1389503
  · exact B1389507
  · exact B1389511

theorem solution (m : ℕ) (hlo : 1387513 ≤ m) (hhi : m ≤ 1389513) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 346878 ≤ j := by omega
    have hj2 : j ≤ 347377 := by omega
    have hb : Blo 1387513 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
