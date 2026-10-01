-- Prove2me | solution 1 for syracuse_descends_range_1995435_1997435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:28.485034+00:00
-- url     : https://prove2.me/submissions/5968d0bd-0c98-4df8-a494-d4a3b5f43a5d

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

theorem B2244865 : Blo 1995435 2244865 := bbase (se 2 (by rfl) ⟨841824, by rfl⟩ : syracuseStep 2244865 = 1683649) (by norm_num)
theorem B2993153 : Blo 1995435 2993153 := bstep (se 2 (by rfl) ⟨1122432, by rfl⟩ : syracuseStep 2993153 = 2244865) B2244865
theorem B1995435 : Blo 1995435 1995435 := bstep (se 1 (by rfl) ⟨1496576, by rfl⟩ : syracuseStep 1995435 = 2993153) B2993153
theorem B5050957 : Blo 1995435 5050957 := bbase (se 3 (by rfl) ⟨947054, by rfl⟩ : syracuseStep 5050957 = 1894109) (by norm_num)
theorem B6734609 : Blo 1995435 6734609 := bstep (se 2 (by rfl) ⟨2525478, by rfl⟩ : syracuseStep 6734609 = 5050957) B5050957
theorem B4489739 : Blo 1995435 4489739 := bstep (se 1 (by rfl) ⟨3367304, by rfl⟩ : syracuseStep 4489739 = 6734609) B6734609
theorem B2993159 : Blo 1995435 2993159 := bstep (se 1 (by rfl) ⟨2244869, by rfl⟩ : syracuseStep 2993159 = 4489739) B4489739
theorem B1995439 : Blo 1995435 1995439 := bstep (se 1 (by rfl) ⟨1496579, by rfl⟩ : syracuseStep 1995439 = 2993159) B2993159
theorem B2993165 : Blo 1995435 2993165 := bbase (se 3 (by rfl) ⟨561218, by rfl⟩ : syracuseStep 2993165 = 1122437) (by norm_num)
theorem B1995443 : Blo 1995435 1995443 := bstep (se 1 (by rfl) ⟨1496582, by rfl⟩ : syracuseStep 1995443 = 2993165) B2993165
theorem B4489757 : Blo 1995435 4489757 := bbase (se 3 (by rfl) ⟨841829, by rfl⟩ : syracuseStep 4489757 = 1683659) (by norm_num)
theorem B2993171 : Blo 1995435 2993171 := bstep (se 1 (by rfl) ⟨2244878, by rfl⟩ : syracuseStep 2993171 = 4489757) B4489757
theorem B1995447 : Blo 1995435 1995447 := bstep (se 1 (by rfl) ⟨1496585, by rfl⟩ : syracuseStep 1995447 = 2993171) B2993171
theorem B3367325 : Blo 1995435 3367325 := bbase (se 3 (by rfl) ⟨631373, by rfl⟩ : syracuseStep 3367325 = 1262747) (by norm_num)
theorem B2244883 : Blo 1995435 2244883 := bstep (se 1 (by rfl) ⟨1683662, by rfl⟩ : syracuseStep 2244883 = 3367325) B3367325
theorem B2993177 : Blo 1995435 2993177 := bstep (se 2 (by rfl) ⟨1122441, by rfl⟩ : syracuseStep 2993177 = 2244883) B2244883
theorem B1995451 : Blo 1995435 1995451 := bstep (se 1 (by rfl) ⟨1496588, by rfl⟩ : syracuseStep 1995451 = 2993177) B2993177
theorem B12136085 : Blo 1995435 12136085 := bbase (se 6 (by rfl) ⟨284439, by rfl⟩ : syracuseStep 12136085 = 568879) (by norm_num)
theorem B8090723 : Blo 1995435 8090723 := bstep (se 1 (by rfl) ⟨6068042, by rfl⟩ : syracuseStep 8090723 = 12136085) B12136085
theorem B21575261 : Blo 1995435 21575261 := bstep (se 3 (by rfl) ⟨4045361, by rfl⟩ : syracuseStep 21575261 = 8090723) B8090723
theorem B14383507 : Blo 1995435 14383507 := bstep (se 1 (by rfl) ⟨10787630, by rfl⟩ : syracuseStep 14383507 = 21575261) B21575261
theorem B19178009 : Blo 1995435 19178009 := bstep (se 2 (by rfl) ⟨7191753, by rfl⟩ : syracuseStep 19178009 = 14383507) B14383507
theorem B12785339 : Blo 1995435 12785339 := bstep (se 1 (by rfl) ⟨9589004, by rfl⟩ : syracuseStep 12785339 = 19178009) B19178009
theorem B8523559 : Blo 1995435 8523559 := bstep (se 1 (by rfl) ⟨6392669, by rfl⟩ : syracuseStep 8523559 = 12785339) B12785339
theorem B11364745 : Blo 1995435 11364745 := bstep (se 2 (by rfl) ⟨4261779, by rfl⟩ : syracuseStep 11364745 = 8523559) B8523559
theorem B15152993 : Blo 1995435 15152993 := bstep (se 2 (by rfl) ⟨5682372, by rfl⟩ : syracuseStep 15152993 = 11364745) B11364745
theorem B10101995 : Blo 1995435 10101995 := bstep (se 1 (by rfl) ⟨7576496, by rfl⟩ : syracuseStep 10101995 = 15152993) B15152993
theorem B6734663 : Blo 1995435 6734663 := bstep (se 1 (by rfl) ⟨5050997, by rfl⟩ : syracuseStep 6734663 = 10101995) B10101995
theorem B4489775 : Blo 1995435 4489775 := bstep (se 1 (by rfl) ⟨3367331, by rfl⟩ : syracuseStep 4489775 = 6734663) B6734663
theorem B2993183 : Blo 1995435 2993183 := bstep (se 1 (by rfl) ⟨2244887, by rfl⟩ : syracuseStep 2993183 = 4489775) B4489775
theorem B1995455 : Blo 1995435 1995455 := bstep (se 1 (by rfl) ⟨1496591, by rfl⟩ : syracuseStep 1995455 = 2993183) B2993183
theorem B2993189 : Blo 1995435 2993189 := bbase (se 4 (by rfl) ⟨280611, by rfl⟩ : syracuseStep 2993189 = 561223) (by norm_num)
theorem B1995459 : Blo 1995435 1995459 := bstep (se 1 (by rfl) ⟨1496594, by rfl⟩ : syracuseStep 1995459 = 2993189) B2993189
theorem B2525509 : Blo 1995435 2525509 := bbase (se 4 (by rfl) ⟨236766, by rfl⟩ : syracuseStep 2525509 = 473533) (by norm_num)
theorem B3367345 : Blo 1995435 3367345 := bstep (se 2 (by rfl) ⟨1262754, by rfl⟩ : syracuseStep 3367345 = 2525509) B2525509
theorem B4489793 : Blo 1995435 4489793 := bstep (se 2 (by rfl) ⟨1683672, by rfl⟩ : syracuseStep 4489793 = 3367345) B3367345
theorem B2993195 : Blo 1995435 2993195 := bstep (se 1 (by rfl) ⟨2244896, by rfl⟩ : syracuseStep 2993195 = 4489793) B4489793
theorem B1995463 : Blo 1995435 1995463 := bstep (se 1 (by rfl) ⟨1496597, by rfl⟩ : syracuseStep 1995463 = 2993195) B2993195
theorem B2244901 : Blo 1995435 2244901 := bbase (se 4 (by rfl) ⟨210459, by rfl⟩ : syracuseStep 2244901 = 420919) (by norm_num)
theorem B2993201 : Blo 1995435 2993201 := bstep (se 2 (by rfl) ⟨1122450, by rfl⟩ : syracuseStep 2993201 = 2244901) B2244901
theorem B1995467 : Blo 1995435 1995467 := bstep (se 1 (by rfl) ⟨1496600, by rfl⟩ : syracuseStep 1995467 = 2993201) B2993201
theorem B5393861 : Blo 1995435 5393861 := bbase (se 4 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 5393861 = 1011349) (by norm_num)
theorem B3595907 : Blo 1995435 3595907 := bstep (se 1 (by rfl) ⟨2696930, by rfl⟩ : syracuseStep 3595907 = 5393861) B5393861
theorem B2397271 : Blo 1995435 2397271 := bstep (se 1 (by rfl) ⟨1797953, by rfl⟩ : syracuseStep 2397271 = 3595907) B3595907
theorem B3196361 : Blo 1995435 3196361 := bstep (se 2 (by rfl) ⟨1198635, by rfl⟩ : syracuseStep 3196361 = 2397271) B2397271
theorem B8523629 : Blo 1995435 8523629 := bstep (se 3 (by rfl) ⟨1598180, by rfl⟩ : syracuseStep 8523629 = 3196361) B3196361
theorem B5682419 : Blo 1995435 5682419 := bstep (se 1 (by rfl) ⟨4261814, by rfl⟩ : syracuseStep 5682419 = 8523629) B8523629
theorem B3788279 : Blo 1995435 3788279 := bstep (se 1 (by rfl) ⟨2841209, by rfl⟩ : syracuseStep 3788279 = 5682419) B5682419
theorem B2525519 : Blo 1995435 2525519 := bstep (se 1 (by rfl) ⟨1894139, by rfl⟩ : syracuseStep 2525519 = 3788279) B3788279
theorem B6734717 : Blo 1995435 6734717 := bstep (se 3 (by rfl) ⟨1262759, by rfl⟩ : syracuseStep 6734717 = 2525519) B2525519
theorem B4489811 : Blo 1995435 4489811 := bstep (se 1 (by rfl) ⟨3367358, by rfl⟩ : syracuseStep 4489811 = 6734717) B6734717
theorem B2993207 : Blo 1995435 2993207 := bstep (se 1 (by rfl) ⟨2244905, by rfl⟩ : syracuseStep 2993207 = 4489811) B4489811
theorem B1995471 : Blo 1995435 1995471 := bstep (se 1 (by rfl) ⟨1496603, by rfl⟩ : syracuseStep 1995471 = 2993207) B2993207
theorem B2993213 : Blo 1995435 2993213 := bbase (se 3 (by rfl) ⟨561227, by rfl⟩ : syracuseStep 2993213 = 1122455) (by norm_num)
theorem B1995475 : Blo 1995435 1995475 := bstep (se 1 (by rfl) ⟨1496606, by rfl⟩ : syracuseStep 1995475 = 2993213) B2993213
theorem B4489829 : Blo 1995435 4489829 := bbase (se 4 (by rfl) ⟨420921, by rfl⟩ : syracuseStep 4489829 = 841843) (by norm_num)
theorem B2993219 : Blo 1995435 2993219 := bstep (se 1 (by rfl) ⟨2244914, by rfl⟩ : syracuseStep 2993219 = 4489829) B4489829
theorem B1995479 : Blo 1995435 1995479 := bstep (se 1 (by rfl) ⟨1496609, by rfl⟩ : syracuseStep 1995479 = 2993219) B2993219
theorem B5051069 : Blo 1995435 5051069 := bbase (se 3 (by rfl) ⟨947075, by rfl⟩ : syracuseStep 5051069 = 1894151) (by norm_num)
theorem B3367379 : Blo 1995435 3367379 := bstep (se 1 (by rfl) ⟨2525534, by rfl⟩ : syracuseStep 3367379 = 5051069) B5051069
theorem B2244919 : Blo 1995435 2244919 := bstep (se 1 (by rfl) ⟨1683689, by rfl⟩ : syracuseStep 2244919 = 3367379) B3367379
theorem B2993225 : Blo 1995435 2993225 := bstep (se 2 (by rfl) ⟨1122459, by rfl⟩ : syracuseStep 2993225 = 2244919) B2244919
theorem B1995483 : Blo 1995435 1995483 := bstep (se 1 (by rfl) ⟨1496612, by rfl⟩ : syracuseStep 1995483 = 2993225) B2993225
theorem B3788309 : Blo 1995435 3788309 := bbase (se 6 (by rfl) ⟨88788, by rfl⟩ : syracuseStep 3788309 = 177577) (by norm_num)
theorem B10102157 : Blo 1995435 10102157 := bstep (se 3 (by rfl) ⟨1894154, by rfl⟩ : syracuseStep 10102157 = 3788309) B3788309
theorem B6734771 : Blo 1995435 6734771 := bstep (se 1 (by rfl) ⟨5051078, by rfl⟩ : syracuseStep 6734771 = 10102157) B10102157
theorem B4489847 : Blo 1995435 4489847 := bstep (se 1 (by rfl) ⟨3367385, by rfl⟩ : syracuseStep 4489847 = 6734771) B6734771
theorem B2993231 : Blo 1995435 2993231 := bstep (se 1 (by rfl) ⟨2244923, by rfl⟩ : syracuseStep 2993231 = 4489847) B4489847
theorem B1995487 : Blo 1995435 1995487 := bstep (se 1 (by rfl) ⟨1496615, by rfl⟩ : syracuseStep 1995487 = 2993231) B2993231
theorem B2993237 : Blo 1995435 2993237 := bbase (se 8 (by rfl) ⟨17538, by rfl⟩ : syracuseStep 2993237 = 35077) (by norm_num)
theorem B1995491 : Blo 1995435 1995491 := bstep (se 1 (by rfl) ⟨1496618, by rfl⟩ : syracuseStep 1995491 = 2993237) B2993237
theorem B17280053 : Blo 1995435 17280053 := bbase (se 5 (by rfl) ⟨810002, by rfl⟩ : syracuseStep 17280053 = 1620005) (by norm_num)
theorem B11520035 : Blo 1995435 11520035 := bstep (se 1 (by rfl) ⟨8640026, by rfl⟩ : syracuseStep 11520035 = 17280053) B17280053
theorem B7680023 : Blo 1995435 7680023 := bstep (se 1 (by rfl) ⟨5760017, by rfl⟩ : syracuseStep 7680023 = 11520035) B11520035
theorem B5120015 : Blo 1995435 5120015 := bstep (se 1 (by rfl) ⟨3840011, by rfl⟩ : syracuseStep 5120015 = 7680023) B7680023
theorem B13653373 : Blo 1995435 13653373 := bstep (se 3 (by rfl) ⟨2560007, by rfl⟩ : syracuseStep 13653373 = 5120015) B5120015
theorem B18204497 : Blo 1995435 18204497 := bstep (se 2 (by rfl) ⟨6826686, by rfl⟩ : syracuseStep 18204497 = 13653373) B13653373
theorem B12136331 : Blo 1995435 12136331 := bstep (se 1 (by rfl) ⟨9102248, by rfl⟩ : syracuseStep 12136331 = 18204497) B18204497
theorem B8090887 : Blo 1995435 8090887 := bstep (se 1 (by rfl) ⟨6068165, by rfl⟩ : syracuseStep 8090887 = 12136331) B12136331
theorem B10787849 : Blo 1995435 10787849 := bstep (se 2 (by rfl) ⟨4045443, by rfl⟩ : syracuseStep 10787849 = 8090887) B8090887
theorem B7191899 : Blo 1995435 7191899 := bstep (se 1 (by rfl) ⟨5393924, by rfl⟩ : syracuseStep 7191899 = 10787849) B10787849
theorem B4794599 : Blo 1995435 4794599 := bstep (se 1 (by rfl) ⟨3595949, by rfl⟩ : syracuseStep 4794599 = 7191899) B7191899
theorem B12785597 : Blo 1995435 12785597 := bstep (se 3 (by rfl) ⟨2397299, by rfl⟩ : syracuseStep 12785597 = 4794599) B4794599
theorem B8523731 : Blo 1995435 8523731 := bstep (se 1 (by rfl) ⟨6392798, by rfl⟩ : syracuseStep 8523731 = 12785597) B12785597
theorem B5682487 : Blo 1995435 5682487 := bstep (se 1 (by rfl) ⟨4261865, by rfl⟩ : syracuseStep 5682487 = 8523731) B8523731
theorem B7576649 : Blo 1995435 7576649 := bstep (se 2 (by rfl) ⟨2841243, by rfl⟩ : syracuseStep 7576649 = 5682487) B5682487
theorem B5051099 : Blo 1995435 5051099 := bstep (se 1 (by rfl) ⟨3788324, by rfl⟩ : syracuseStep 5051099 = 7576649) B7576649
theorem B3367399 : Blo 1995435 3367399 := bstep (se 1 (by rfl) ⟨2525549, by rfl⟩ : syracuseStep 3367399 = 5051099) B5051099
theorem B4489865 : Blo 1995435 4489865 := bstep (se 2 (by rfl) ⟨1683699, by rfl⟩ : syracuseStep 4489865 = 3367399) B3367399
theorem B2993243 : Blo 1995435 2993243 := bstep (se 1 (by rfl) ⟨2244932, by rfl⟩ : syracuseStep 2993243 = 4489865) B4489865
theorem B1995495 : Blo 1995435 1995495 := bstep (se 1 (by rfl) ⟨1496621, by rfl⟩ : syracuseStep 1995495 = 2993243) B2993243
theorem B2244937 : Blo 1995435 2244937 := bbase (se 2 (by rfl) ⟨841851, by rfl⟩ : syracuseStep 2244937 = 1683703) (by norm_num)
theorem B2993249 : Blo 1995435 2993249 := bstep (se 2 (by rfl) ⟨1122468, by rfl⟩ : syracuseStep 2993249 = 2244937) B2244937
theorem B1995499 : Blo 1995435 1995499 := bstep (se 1 (by rfl) ⟨1496624, by rfl⟩ : syracuseStep 1995499 = 2993249) B2993249
theorem B72818261 : Blo 1995435 72818261 := bbase (se 8 (by rfl) ⟨426669, by rfl⟩ : syracuseStep 72818261 = 853339) (by norm_num)
theorem B48545507 : Blo 1995435 48545507 := bstep (se 1 (by rfl) ⟨36409130, by rfl⟩ : syracuseStep 48545507 = 72818261) B72818261
theorem B32363671 : Blo 1995435 32363671 := bstep (se 1 (by rfl) ⟨24272753, by rfl⟩ : syracuseStep 32363671 = 48545507) B48545507
theorem B43151561 : Blo 1995435 43151561 := bstep (se 2 (by rfl) ⟨16181835, by rfl⟩ : syracuseStep 43151561 = 32363671) B32363671
theorem B28767707 : Blo 1995435 28767707 := bstep (se 1 (by rfl) ⟨21575780, by rfl⟩ : syracuseStep 28767707 = 43151561) B43151561
theorem B19178471 : Blo 1995435 19178471 := bstep (se 1 (by rfl) ⟨14383853, by rfl⟩ : syracuseStep 19178471 = 28767707) B28767707
theorem B12785647 : Blo 1995435 12785647 := bstep (se 1 (by rfl) ⟨9589235, by rfl⟩ : syracuseStep 12785647 = 19178471) B19178471
theorem B17047529 : Blo 1995435 17047529 := bstep (se 2 (by rfl) ⟨6392823, by rfl⟩ : syracuseStep 17047529 = 12785647) B12785647
theorem B11365019 : Blo 1995435 11365019 := bstep (se 1 (by rfl) ⟨8523764, by rfl⟩ : syracuseStep 11365019 = 17047529) B17047529
theorem B7576679 : Blo 1995435 7576679 := bstep (se 1 (by rfl) ⟨5682509, by rfl⟩ : syracuseStep 7576679 = 11365019) B11365019
theorem B5051119 : Blo 1995435 5051119 := bstep (se 1 (by rfl) ⟨3788339, by rfl⟩ : syracuseStep 5051119 = 7576679) B7576679
theorem B6734825 : Blo 1995435 6734825 := bstep (se 2 (by rfl) ⟨2525559, by rfl⟩ : syracuseStep 6734825 = 5051119) B5051119
theorem B4489883 : Blo 1995435 4489883 := bstep (se 1 (by rfl) ⟨3367412, by rfl⟩ : syracuseStep 4489883 = 6734825) B6734825
theorem B2993255 : Blo 1995435 2993255 := bstep (se 1 (by rfl) ⟨2244941, by rfl⟩ : syracuseStep 2993255 = 4489883) B4489883
theorem B1995503 : Blo 1995435 1995503 := bstep (se 1 (by rfl) ⟨1496627, by rfl⟩ : syracuseStep 1995503 = 2993255) B2993255
theorem B2993261 : Blo 1995435 2993261 := bbase (se 3 (by rfl) ⟨561236, by rfl⟩ : syracuseStep 2993261 = 1122473) (by norm_num)
theorem B1995507 : Blo 1995435 1995507 := bstep (se 1 (by rfl) ⟨1496630, by rfl⟩ : syracuseStep 1995507 = 2993261) B2993261
theorem B4489901 : Blo 1995435 4489901 := bbase (se 3 (by rfl) ⟨841856, by rfl⟩ : syracuseStep 4489901 = 1683713) (by norm_num)
theorem B2993267 : Blo 1995435 2993267 := bstep (se 1 (by rfl) ⟨2244950, by rfl⟩ : syracuseStep 2993267 = 4489901) B4489901
theorem B1995511 : Blo 1995435 1995511 := bstep (se 1 (by rfl) ⟨1496633, by rfl⟩ : syracuseStep 1995511 = 2993267) B2993267
theorem B4261909 : Blo 1995435 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B5682545 : Blo 1995435 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B3788363 : Blo 1995435 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B2525575 : Blo 1995435 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B3367433 : Blo 1995435 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B2244955 : Blo 1995435 2244955 := bstep (se 1 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 2244955 = 3367433) B3367433
theorem B2993273 : Blo 1995435 2993273 := bstep (se 2 (by rfl) ⟨1122477, by rfl⟩ : syracuseStep 2993273 = 2244955) B2244955
theorem B1995515 : Blo 1995435 1995515 := bstep (se 1 (by rfl) ⟨1496636, by rfl⟩ : syracuseStep 1995515 = 2993273) B2993273
theorem B4676213 : Blo 1995435 4676213 := bbase (se 5 (by rfl) ⟨219197, by rfl⟩ : syracuseStep 4676213 = 438395) (by norm_num)
theorem B3117475 : Blo 1995435 3117475 := bstep (se 1 (by rfl) ⟨2338106, by rfl⟩ : syracuseStep 3117475 = 4676213) B4676213
theorem B4156633 : Blo 1995435 4156633 := bstep (se 2 (by rfl) ⟨1558737, by rfl⟩ : syracuseStep 4156633 = 3117475) B3117475
theorem B5542177 : Blo 1995435 5542177 := bstep (se 2 (by rfl) ⟨2078316, by rfl⟩ : syracuseStep 5542177 = 4156633) B4156633
theorem B7389569 : Blo 1995435 7389569 := bstep (se 2 (by rfl) ⟨2771088, by rfl⟩ : syracuseStep 7389569 = 5542177) B5542177
theorem B19705517 : Blo 1995435 19705517 := bstep (se 3 (by rfl) ⟨3694784, by rfl⟩ : syracuseStep 19705517 = 7389569) B7389569
theorem B13137011 : Blo 1995435 13137011 := bstep (se 1 (by rfl) ⟨9852758, by rfl⟩ : syracuseStep 13137011 = 19705517) B19705517
theorem B8758007 : Blo 1995435 8758007 := bstep (se 1 (by rfl) ⟨6568505, by rfl⟩ : syracuseStep 8758007 = 13137011) B13137011
theorem B5838671 : Blo 1995435 5838671 := bstep (se 1 (by rfl) ⟨4379003, by rfl⟩ : syracuseStep 5838671 = 8758007) B8758007
theorem B3892447 : Blo 1995435 3892447 := bstep (se 1 (by rfl) ⟨2919335, by rfl⟩ : syracuseStep 3892447 = 5838671) B5838671
theorem B20759717 : Blo 1995435 20759717 := bstep (se 4 (by rfl) ⟨1946223, by rfl⟩ : syracuseStep 20759717 = 3892447) B3892447
theorem B55359245 : Blo 1995435 55359245 := bstep (se 3 (by rfl) ⟨10379858, by rfl⟩ : syracuseStep 55359245 = 20759717) B20759717
theorem B147624653 : Blo 1995435 147624653 := bstep (se 3 (by rfl) ⟨27679622, by rfl⟩ : syracuseStep 147624653 = 55359245) B55359245
theorem B393665741 : Blo 1995435 393665741 := bstep (se 3 (by rfl) ⟨73812326, by rfl⟩ : syracuseStep 393665741 = 147624653) B147624653
theorem B262443827 : Blo 1995435 262443827 := bstep (se 1 (by rfl) ⟨196832870, by rfl⟩ : syracuseStep 262443827 = 393665741) B393665741
theorem B174962551 : Blo 1995435 174962551 := bstep (se 1 (by rfl) ⟨131221913, by rfl⟩ : syracuseStep 174962551 = 262443827) B262443827
theorem B233283401 : Blo 1995435 233283401 := bstep (se 2 (by rfl) ⟨87481275, by rfl⟩ : syracuseStep 233283401 = 174962551) B174962551
theorem B155522267 : Blo 1995435 155522267 := bstep (se 1 (by rfl) ⟨116641700, by rfl⟩ : syracuseStep 155522267 = 233283401) B233283401
theorem B103681511 : Blo 1995435 103681511 := bstep (se 1 (by rfl) ⟨77761133, by rfl⟩ : syracuseStep 103681511 = 155522267) B155522267
theorem B69121007 : Blo 1995435 69121007 := bstep (se 1 (by rfl) ⟨51840755, by rfl⟩ : syracuseStep 69121007 = 103681511) B103681511
theorem B46080671 : Blo 1995435 46080671 := bstep (se 1 (by rfl) ⟨34560503, by rfl⟩ : syracuseStep 46080671 = 69121007) B69121007
theorem B122881789 : Blo 1995435 122881789 := bstep (se 3 (by rfl) ⟨23040335, by rfl⟩ : syracuseStep 122881789 = 46080671) B46080671
theorem B163842385 : Blo 1995435 163842385 := bstep (se 2 (by rfl) ⟨61440894, by rfl⟩ : syracuseStep 163842385 = 122881789) B122881789
theorem B218456513 : Blo 1995435 218456513 := bstep (se 2 (by rfl) ⟨81921192, by rfl⟩ : syracuseStep 218456513 = 163842385) B163842385
theorem B145637675 : Blo 1995435 145637675 := bstep (se 1 (by rfl) ⟨109228256, by rfl⟩ : syracuseStep 145637675 = 218456513) B218456513
theorem B97091783 : Blo 1995435 97091783 := bstep (se 1 (by rfl) ⟨72818837, by rfl⟩ : syracuseStep 97091783 = 145637675) B145637675
theorem B64727855 : Blo 1995435 64727855 := bstep (se 1 (by rfl) ⟨48545891, by rfl⟩ : syracuseStep 64727855 = 97091783) B97091783
theorem B43151903 : Blo 1995435 43151903 := bstep (se 1 (by rfl) ⟨32363927, by rfl⟩ : syracuseStep 43151903 = 64727855) B64727855
theorem B28767935 : Blo 1995435 28767935 := bstep (se 1 (by rfl) ⟨21575951, by rfl⟩ : syracuseStep 28767935 = 43151903) B43151903
theorem B19178623 : Blo 1995435 19178623 := bstep (se 1 (by rfl) ⟨14383967, by rfl⟩ : syracuseStep 19178623 = 28767935) B28767935
theorem B25571497 : Blo 1995435 25571497 := bstep (se 2 (by rfl) ⟨9589311, by rfl⟩ : syracuseStep 25571497 = 19178623) B19178623
theorem B34095329 : Blo 1995435 34095329 := bstep (se 2 (by rfl) ⟨12785748, by rfl⟩ : syracuseStep 34095329 = 25571497) B25571497
theorem B22730219 : Blo 1995435 22730219 := bstep (se 1 (by rfl) ⟨17047664, by rfl⟩ : syracuseStep 22730219 = 34095329) B34095329
theorem B15153479 : Blo 1995435 15153479 := bstep (se 1 (by rfl) ⟨11365109, by rfl⟩ : syracuseStep 15153479 = 22730219) B22730219
theorem B10102319 : Blo 1995435 10102319 := bstep (se 1 (by rfl) ⟨7576739, by rfl⟩ : syracuseStep 10102319 = 15153479) B15153479
theorem B6734879 : Blo 1995435 6734879 := bstep (se 1 (by rfl) ⟨5051159, by rfl⟩ : syracuseStep 6734879 = 10102319) B10102319
theorem B4489919 : Blo 1995435 4489919 := bstep (se 1 (by rfl) ⟨3367439, by rfl⟩ : syracuseStep 4489919 = 6734879) B6734879
theorem B2993279 : Blo 1995435 2993279 := bstep (se 1 (by rfl) ⟨2244959, by rfl⟩ : syracuseStep 2993279 = 4489919) B4489919
theorem B1995519 : Blo 1995435 1995519 := bstep (se 1 (by rfl) ⟨1496639, by rfl⟩ : syracuseStep 1995519 = 2993279) B2993279
theorem B2993285 : Blo 1995435 2993285 := bbase (se 4 (by rfl) ⟨280620, by rfl⟩ : syracuseStep 2993285 = 561241) (by norm_num)
theorem B1995523 : Blo 1995435 1995523 := bstep (se 1 (by rfl) ⟨1496642, by rfl⟩ : syracuseStep 1995523 = 2993285) B2993285
theorem B3367453 : Blo 1995435 3367453 := bbase (se 3 (by rfl) ⟨631397, by rfl⟩ : syracuseStep 3367453 = 1262795) (by norm_num)
theorem B4489937 : Blo 1995435 4489937 := bstep (se 2 (by rfl) ⟨1683726, by rfl⟩ : syracuseStep 4489937 = 3367453) B3367453
theorem B2993291 : Blo 1995435 2993291 := bstep (se 1 (by rfl) ⟨2244968, by rfl⟩ : syracuseStep 2993291 = 4489937) B4489937
theorem B1995527 : Blo 1995435 1995527 := bstep (se 1 (by rfl) ⟨1496645, by rfl⟩ : syracuseStep 1995527 = 2993291) B2993291
theorem B2244973 : Blo 1995435 2244973 := bbase (se 3 (by rfl) ⟨420932, by rfl⟩ : syracuseStep 2244973 = 841865) (by norm_num)
theorem B2993297 : Blo 1995435 2993297 := bstep (se 2 (by rfl) ⟨1122486, by rfl⟩ : syracuseStep 2993297 = 2244973) B2244973
theorem B1995531 : Blo 1995435 1995531 := bstep (se 1 (by rfl) ⟨1496648, by rfl⟩ : syracuseStep 1995531 = 2993297) B2993297
theorem B6734933 : Blo 1995435 6734933 := bbase (se 8 (by rfl) ⟨39462, by rfl⟩ : syracuseStep 6734933 = 78925) (by norm_num)
theorem B4489955 : Blo 1995435 4489955 := bstep (se 1 (by rfl) ⟨3367466, by rfl⟩ : syracuseStep 4489955 = 6734933) B6734933
theorem B2993303 : Blo 1995435 2993303 := bstep (se 1 (by rfl) ⟨2244977, by rfl⟩ : syracuseStep 2993303 = 4489955) B4489955
theorem B1995535 : Blo 1995435 1995535 := bstep (se 1 (by rfl) ⟨1496651, by rfl⟩ : syracuseStep 1995535 = 2993303) B2993303
theorem B2993309 : Blo 1995435 2993309 := bbase (se 3 (by rfl) ⟨561245, by rfl⟩ : syracuseStep 2993309 = 1122491) (by norm_num)
theorem B1995539 : Blo 1995435 1995539 := bstep (se 1 (by rfl) ⟨1496654, by rfl⟩ : syracuseStep 1995539 = 2993309) B2993309
theorem B4489973 : Blo 1995435 4489973 := bbase (se 5 (by rfl) ⟨210467, by rfl⟩ : syracuseStep 4489973 = 420935) (by norm_num)
theorem B2993315 : Blo 1995435 2993315 := bstep (se 1 (by rfl) ⟨2244986, by rfl⟩ : syracuseStep 2993315 = 4489973) B4489973
theorem B1995543 : Blo 1995435 1995543 := bstep (se 1 (by rfl) ⟨1496657, by rfl⟩ : syracuseStep 1995543 = 2993315) B2993315
theorem B25571861 : Blo 1995435 25571861 := bbase (se 6 (by rfl) ⟨599340, by rfl⟩ : syracuseStep 25571861 = 1198681) (by norm_num)
theorem B17047907 : Blo 1995435 17047907 := bstep (se 1 (by rfl) ⟨12785930, by rfl⟩ : syracuseStep 17047907 = 25571861) B25571861
theorem B11365271 : Blo 1995435 11365271 := bstep (se 1 (by rfl) ⟨8523953, by rfl⟩ : syracuseStep 11365271 = 17047907) B17047907
theorem B7576847 : Blo 1995435 7576847 := bstep (se 1 (by rfl) ⟨5682635, by rfl⟩ : syracuseStep 7576847 = 11365271) B11365271
theorem B5051231 : Blo 1995435 5051231 := bstep (se 1 (by rfl) ⟨3788423, by rfl⟩ : syracuseStep 5051231 = 7576847) B7576847
theorem B3367487 : Blo 1995435 3367487 := bstep (se 1 (by rfl) ⟨2525615, by rfl⟩ : syracuseStep 3367487 = 5051231) B5051231
theorem B2244991 : Blo 1995435 2244991 := bstep (se 1 (by rfl) ⟨1683743, by rfl⟩ : syracuseStep 2244991 = 3367487) B3367487
theorem B2993321 : Blo 1995435 2993321 := bstep (se 2 (by rfl) ⟨1122495, by rfl⟩ : syracuseStep 2993321 = 2244991) B2244991
theorem B1995547 : Blo 1995435 1995547 := bstep (se 1 (by rfl) ⟨1496660, by rfl⟩ : syracuseStep 1995547 = 2993321) B2993321
theorem B2560081 : Blo 1995435 2560081 := bbase (se 2 (by rfl) ⟨960030, by rfl⟩ : syracuseStep 2560081 = 1920061) (by norm_num)
theorem B3413441 : Blo 1995435 3413441 := bstep (se 2 (by rfl) ⟨1280040, by rfl⟩ : syracuseStep 3413441 = 2560081) B2560081
theorem B2275627 : Blo 1995435 2275627 := bstep (se 1 (by rfl) ⟨1706720, by rfl⟩ : syracuseStep 2275627 = 3413441) B3413441
theorem B3034169 : Blo 1995435 3034169 := bstep (se 2 (by rfl) ⟨1137813, by rfl⟩ : syracuseStep 3034169 = 2275627) B2275627
theorem B2022779 : Blo 1995435 2022779 := bstep (se 1 (by rfl) ⟨1517084, by rfl⟩ : syracuseStep 2022779 = 3034169) B3034169
theorem B5394077 : Blo 1995435 5394077 := bstep (se 3 (by rfl) ⟨1011389, by rfl⟩ : syracuseStep 5394077 = 2022779) B2022779
theorem B3596051 : Blo 1995435 3596051 := bstep (se 1 (by rfl) ⟨2697038, by rfl⟩ : syracuseStep 3596051 = 5394077) B5394077
theorem B2397367 : Blo 1995435 2397367 := bstep (se 1 (by rfl) ⟨1798025, by rfl⟩ : syracuseStep 2397367 = 3596051) B3596051
theorem B3196489 : Blo 1995435 3196489 := bstep (se 2 (by rfl) ⟨1198683, by rfl⟩ : syracuseStep 3196489 = 2397367) B2397367
theorem B4261985 : Blo 1995435 4261985 := bstep (se 2 (by rfl) ⟨1598244, by rfl⟩ : syracuseStep 4261985 = 3196489) B3196489
theorem B2841323 : Blo 1995435 2841323 := bstep (se 1 (by rfl) ⟨2130992, by rfl⟩ : syracuseStep 2841323 = 4261985) B4261985
theorem B7576861 : Blo 1995435 7576861 := bstep (se 3 (by rfl) ⟨1420661, by rfl⟩ : syracuseStep 7576861 = 2841323) B2841323
theorem B10102481 : Blo 1995435 10102481 := bstep (se 2 (by rfl) ⟨3788430, by rfl⟩ : syracuseStep 10102481 = 7576861) B7576861
theorem B6734987 : Blo 1995435 6734987 := bstep (se 1 (by rfl) ⟨5051240, by rfl⟩ : syracuseStep 6734987 = 10102481) B10102481
theorem B4489991 : Blo 1995435 4489991 := bstep (se 1 (by rfl) ⟨3367493, by rfl⟩ : syracuseStep 4489991 = 6734987) B6734987
theorem B2993327 : Blo 1995435 2993327 := bstep (se 1 (by rfl) ⟨2244995, by rfl⟩ : syracuseStep 2993327 = 4489991) B4489991
theorem B1995551 : Blo 1995435 1995551 := bstep (se 1 (by rfl) ⟨1496663, by rfl⟩ : syracuseStep 1995551 = 2993327) B2993327
theorem B2993333 : Blo 1995435 2993333 := bbase (se 5 (by rfl) ⟨140312, by rfl⟩ : syracuseStep 2993333 = 280625) (by norm_num)
theorem B1995555 : Blo 1995435 1995555 := bstep (se 1 (by rfl) ⟨1496666, by rfl⟩ : syracuseStep 1995555 = 2993333) B2993333
theorem B5051261 : Blo 1995435 5051261 := bbase (se 3 (by rfl) ⟨947111, by rfl⟩ : syracuseStep 5051261 = 1894223) (by norm_num)
theorem B3367507 : Blo 1995435 3367507 := bstep (se 1 (by rfl) ⟨2525630, by rfl⟩ : syracuseStep 3367507 = 5051261) B5051261
theorem B4490009 : Blo 1995435 4490009 := bstep (se 2 (by rfl) ⟨1683753, by rfl⟩ : syracuseStep 4490009 = 3367507) B3367507
theorem B2993339 : Blo 1995435 2993339 := bstep (se 1 (by rfl) ⟨2245004, by rfl⟩ : syracuseStep 2993339 = 4490009) B4490009
theorem B1995559 : Blo 1995435 1995559 := bstep (se 1 (by rfl) ⟨1496669, by rfl⟩ : syracuseStep 1995559 = 2993339) B2993339
theorem B2245009 : Blo 1995435 2245009 := bbase (se 2 (by rfl) ⟨841878, by rfl⟩ : syracuseStep 2245009 = 1683757) (by norm_num)
theorem B2993345 : Blo 1995435 2993345 := bstep (se 2 (by rfl) ⟨1122504, by rfl⟩ : syracuseStep 2993345 = 2245009) B2245009
theorem B1995563 : Blo 1995435 1995563 := bstep (se 1 (by rfl) ⟨1496672, by rfl⟩ : syracuseStep 1995563 = 2993345) B2993345
theorem B3788461 : Blo 1995435 3788461 := bbase (se 3 (by rfl) ⟨710336, by rfl⟩ : syracuseStep 3788461 = 1420673) (by norm_num)
theorem B5051281 : Blo 1995435 5051281 := bstep (se 2 (by rfl) ⟨1894230, by rfl⟩ : syracuseStep 5051281 = 3788461) B3788461
theorem B6735041 : Blo 1995435 6735041 := bstep (se 2 (by rfl) ⟨2525640, by rfl⟩ : syracuseStep 6735041 = 5051281) B5051281
theorem B4490027 : Blo 1995435 4490027 := bstep (se 1 (by rfl) ⟨3367520, by rfl⟩ : syracuseStep 4490027 = 6735041) B6735041
theorem B2993351 : Blo 1995435 2993351 := bstep (se 1 (by rfl) ⟨2245013, by rfl⟩ : syracuseStep 2993351 = 4490027) B4490027
theorem B1995567 : Blo 1995435 1995567 := bstep (se 1 (by rfl) ⟨1496675, by rfl⟩ : syracuseStep 1995567 = 2993351) B2993351
theorem B2993357 : Blo 1995435 2993357 := bbase (se 3 (by rfl) ⟨561254, by rfl⟩ : syracuseStep 2993357 = 1122509) (by norm_num)
theorem B1995571 : Blo 1995435 1995571 := bstep (se 1 (by rfl) ⟨1496678, by rfl⟩ : syracuseStep 1995571 = 2993357) B2993357
theorem B4490045 : Blo 1995435 4490045 := bbase (se 3 (by rfl) ⟨841883, by rfl⟩ : syracuseStep 4490045 = 1683767) (by norm_num)
theorem B2993363 : Blo 1995435 2993363 := bstep (se 1 (by rfl) ⟨2245022, by rfl⟩ : syracuseStep 2993363 = 4490045) B4490045
theorem B1995575 : Blo 1995435 1995575 := bstep (se 1 (by rfl) ⟨1496681, by rfl⟩ : syracuseStep 1995575 = 2993363) B2993363
theorem B3367541 : Blo 1995435 3367541 := bbase (se 5 (by rfl) ⟨157853, by rfl⟩ : syracuseStep 3367541 = 315707) (by norm_num)
theorem B2245027 : Blo 1995435 2245027 := bstep (se 1 (by rfl) ⟨1683770, by rfl⟩ : syracuseStep 2245027 = 3367541) B3367541
theorem B2993369 : Blo 1995435 2993369 := bstep (se 2 (by rfl) ⟨1122513, by rfl⟩ : syracuseStep 2993369 = 2245027) B2245027
theorem B1995579 : Blo 1995435 1995579 := bstep (se 1 (by rfl) ⟨1496684, by rfl⟩ : syracuseStep 1995579 = 2993369) B2993369
theorem B4262053 : Blo 1995435 4262053 := bbase (se 4 (by rfl) ⟨399567, by rfl⟩ : syracuseStep 4262053 = 799135) (by norm_num)
theorem B5682737 : Blo 1995435 5682737 := bstep (se 2 (by rfl) ⟨2131026, by rfl⟩ : syracuseStep 5682737 = 4262053) B4262053
theorem B15153965 : Blo 1995435 15153965 := bstep (se 3 (by rfl) ⟨2841368, by rfl⟩ : syracuseStep 15153965 = 5682737) B5682737
theorem B10102643 : Blo 1995435 10102643 := bstep (se 1 (by rfl) ⟨7576982, by rfl⟩ : syracuseStep 10102643 = 15153965) B15153965
theorem B6735095 : Blo 1995435 6735095 := bstep (se 1 (by rfl) ⟨5051321, by rfl⟩ : syracuseStep 6735095 = 10102643) B10102643
theorem B4490063 : Blo 1995435 4490063 := bstep (se 1 (by rfl) ⟨3367547, by rfl⟩ : syracuseStep 4490063 = 6735095) B6735095
theorem B2993375 : Blo 1995435 2993375 := bstep (se 1 (by rfl) ⟨2245031, by rfl⟩ : syracuseStep 2993375 = 4490063) B4490063
theorem B1995583 : Blo 1995435 1995583 := bstep (se 1 (by rfl) ⟨1496687, by rfl⟩ : syracuseStep 1995583 = 2993375) B2993375
theorem B2993381 : Blo 1995435 2993381 := bbase (se 4 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 2993381 = 561259) (by norm_num)
theorem B1995587 : Blo 1995435 1995587 := bstep (se 1 (by rfl) ⟨1496690, by rfl⟩ : syracuseStep 1995587 = 2993381) B2993381
theorem B9226885 : Blo 1995435 9226885 := bbase (se 4 (by rfl) ⟨865020, by rfl⟩ : syracuseStep 9226885 = 1730041) (by norm_num)
theorem B12302513 : Blo 1995435 12302513 := bstep (se 2 (by rfl) ⟨4613442, by rfl⟩ : syracuseStep 12302513 = 9226885) B9226885
theorem B8201675 : Blo 1995435 8201675 := bstep (se 1 (by rfl) ⟨6151256, by rfl⟩ : syracuseStep 8201675 = 12302513) B12302513
theorem B5467783 : Blo 1995435 5467783 := bstep (se 1 (by rfl) ⟨4100837, by rfl⟩ : syracuseStep 5467783 = 8201675) B8201675
theorem B7290377 : Blo 1995435 7290377 := bstep (se 2 (by rfl) ⟨2733891, by rfl⟩ : syracuseStep 7290377 = 5467783) B5467783
theorem B4860251 : Blo 1995435 4860251 := bstep (se 1 (by rfl) ⟨3645188, by rfl⟩ : syracuseStep 4860251 = 7290377) B7290377
theorem B3240167 : Blo 1995435 3240167 := bstep (se 1 (by rfl) ⟨2430125, by rfl⟩ : syracuseStep 3240167 = 4860251) B4860251
theorem B8640445 : Blo 1995435 8640445 := bstep (se 3 (by rfl) ⟨1620083, by rfl⟩ : syracuseStep 8640445 = 3240167) B3240167
theorem B11520593 : Blo 1995435 11520593 := bstep (se 2 (by rfl) ⟨4320222, by rfl⟩ : syracuseStep 11520593 = 8640445) B8640445
theorem B7680395 : Blo 1995435 7680395 := bstep (se 1 (by rfl) ⟨5760296, by rfl⟩ : syracuseStep 7680395 = 11520593) B11520593
theorem B5120263 : Blo 1995435 5120263 := bstep (se 1 (by rfl) ⟨3840197, by rfl⟩ : syracuseStep 5120263 = 7680395) B7680395
theorem B6827017 : Blo 1995435 6827017 := bstep (se 2 (by rfl) ⟨2560131, by rfl⟩ : syracuseStep 6827017 = 5120263) B5120263
theorem B9102689 : Blo 1995435 9102689 := bstep (se 2 (by rfl) ⟨3413508, by rfl⟩ : syracuseStep 9102689 = 6827017) B6827017
theorem B6068459 : Blo 1995435 6068459 := bstep (se 1 (by rfl) ⟨4551344, by rfl⟩ : syracuseStep 6068459 = 9102689) B9102689
theorem B4045639 : Blo 1995435 4045639 := bstep (se 1 (by rfl) ⟨3034229, by rfl⟩ : syracuseStep 4045639 = 6068459) B6068459
theorem B5394185 : Blo 1995435 5394185 := bstep (se 2 (by rfl) ⟨2022819, by rfl⟩ : syracuseStep 5394185 = 4045639) B4045639
theorem B3596123 : Blo 1995435 3596123 := bstep (se 1 (by rfl) ⟨2697092, by rfl⟩ : syracuseStep 3596123 = 5394185) B5394185
theorem B9589661 : Blo 1995435 9589661 := bstep (se 3 (by rfl) ⟨1798061, by rfl⟩ : syracuseStep 9589661 = 3596123) B3596123
theorem B6393107 : Blo 1995435 6393107 := bstep (se 1 (by rfl) ⟨4794830, by rfl⟩ : syracuseStep 6393107 = 9589661) B9589661
theorem B4262071 : Blo 1995435 4262071 := bstep (se 1 (by rfl) ⟨3196553, by rfl⟩ : syracuseStep 4262071 = 6393107) B6393107
theorem B5682761 : Blo 1995435 5682761 := bstep (se 2 (by rfl) ⟨2131035, by rfl⟩ : syracuseStep 5682761 = 4262071) B4262071
theorem B3788507 : Blo 1995435 3788507 := bstep (se 1 (by rfl) ⟨2841380, by rfl⟩ : syracuseStep 3788507 = 5682761) B5682761
theorem B2525671 : Blo 1995435 2525671 := bstep (se 1 (by rfl) ⟨1894253, by rfl⟩ : syracuseStep 2525671 = 3788507) B3788507
theorem B3367561 : Blo 1995435 3367561 := bstep (se 2 (by rfl) ⟨1262835, by rfl⟩ : syracuseStep 3367561 = 2525671) B2525671
theorem B4490081 : Blo 1995435 4490081 := bstep (se 2 (by rfl) ⟨1683780, by rfl⟩ : syracuseStep 4490081 = 3367561) B3367561
theorem B2993387 : Blo 1995435 2993387 := bstep (se 1 (by rfl) ⟨2245040, by rfl⟩ : syracuseStep 2993387 = 4490081) B4490081
theorem B1995591 : Blo 1995435 1995591 := bstep (se 1 (by rfl) ⟨1496693, by rfl⟩ : syracuseStep 1995591 = 2993387) B2993387
theorem B2245045 : Blo 1995435 2245045 := bbase (se 5 (by rfl) ⟨105236, by rfl⟩ : syracuseStep 2245045 = 210473) (by norm_num)
theorem B2993393 : Blo 1995435 2993393 := bstep (se 2 (by rfl) ⟨1122522, by rfl⟩ : syracuseStep 2993393 = 2245045) B2245045
theorem B1995595 : Blo 1995435 1995595 := bstep (se 1 (by rfl) ⟨1496696, by rfl⟩ : syracuseStep 1995595 = 2993393) B2993393
theorem B2525681 : Blo 1995435 2525681 := bbase (se 2 (by rfl) ⟨947130, by rfl⟩ : syracuseStep 2525681 = 1894261) (by norm_num)
theorem B6735149 : Blo 1995435 6735149 := bstep (se 3 (by rfl) ⟨1262840, by rfl⟩ : syracuseStep 6735149 = 2525681) B2525681
theorem B4490099 : Blo 1995435 4490099 := bstep (se 1 (by rfl) ⟨3367574, by rfl⟩ : syracuseStep 4490099 = 6735149) B6735149
theorem B2993399 : Blo 1995435 2993399 := bstep (se 1 (by rfl) ⟨2245049, by rfl⟩ : syracuseStep 2993399 = 4490099) B4490099
theorem B1995599 : Blo 1995435 1995599 := bstep (se 1 (by rfl) ⟨1496699, by rfl⟩ : syracuseStep 1995599 = 2993399) B2993399
theorem B2993405 : Blo 1995435 2993405 := bbase (se 3 (by rfl) ⟨561263, by rfl⟩ : syracuseStep 2993405 = 1122527) (by norm_num)
theorem B1995603 : Blo 1995435 1995603 := bstep (se 1 (by rfl) ⟨1496702, by rfl⟩ : syracuseStep 1995603 = 2993405) B2993405
theorem B4490117 : Blo 1995435 4490117 := bbase (se 4 (by rfl) ⟨420948, by rfl⟩ : syracuseStep 4490117 = 841897) (by norm_num)
theorem B2993411 : Blo 1995435 2993411 := bstep (se 1 (by rfl) ⟨2245058, by rfl⟩ : syracuseStep 2993411 = 4490117) B4490117
theorem B1995607 : Blo 1995435 1995607 := bstep (se 1 (by rfl) ⟨1496705, by rfl⟩ : syracuseStep 1995607 = 2993411) B2993411
theorem B2131057 : Blo 1995435 2131057 := bbase (se 2 (by rfl) ⟨799146, by rfl⟩ : syracuseStep 2131057 = 1598293) (by norm_num)
theorem B2841409 : Blo 1995435 2841409 := bstep (se 2 (by rfl) ⟨1065528, by rfl⟩ : syracuseStep 2841409 = 2131057) B2131057
theorem B3788545 : Blo 1995435 3788545 := bstep (se 2 (by rfl) ⟨1420704, by rfl⟩ : syracuseStep 3788545 = 2841409) B2841409
theorem B5051393 : Blo 1995435 5051393 := bstep (se 2 (by rfl) ⟨1894272, by rfl⟩ : syracuseStep 5051393 = 3788545) B3788545
theorem B3367595 : Blo 1995435 3367595 := bstep (se 1 (by rfl) ⟨2525696, by rfl⟩ : syracuseStep 3367595 = 5051393) B5051393
theorem B2245063 : Blo 1995435 2245063 := bstep (se 1 (by rfl) ⟨1683797, by rfl⟩ : syracuseStep 2245063 = 3367595) B3367595
theorem B2993417 : Blo 1995435 2993417 := bstep (se 2 (by rfl) ⟨1122531, by rfl⟩ : syracuseStep 2993417 = 2245063) B2245063
theorem B1995611 : Blo 1995435 1995611 := bstep (se 1 (by rfl) ⟨1496708, by rfl⟩ : syracuseStep 1995611 = 2993417) B2993417
theorem B10102805 : Blo 1995435 10102805 := bbase (se 6 (by rfl) ⟨236784, by rfl⟩ : syracuseStep 10102805 = 473569) (by norm_num)
theorem B6735203 : Blo 1995435 6735203 := bstep (se 1 (by rfl) ⟨5051402, by rfl⟩ : syracuseStep 6735203 = 10102805) B10102805
theorem B4490135 : Blo 1995435 4490135 := bstep (se 1 (by rfl) ⟨3367601, by rfl⟩ : syracuseStep 4490135 = 6735203) B6735203
theorem B2993423 : Blo 1995435 2993423 := bstep (se 1 (by rfl) ⟨2245067, by rfl⟩ : syracuseStep 2993423 = 4490135) B4490135
theorem B1995615 : Blo 1995435 1995615 := bstep (se 1 (by rfl) ⟨1496711, by rfl⟩ : syracuseStep 1995615 = 2993423) B2993423
theorem B2993429 : Blo 1995435 2993429 := bbase (se 6 (by rfl) ⟨70158, by rfl⟩ : syracuseStep 2993429 = 140317) (by norm_num)
theorem B1995619 : Blo 1995435 1995619 := bstep (se 1 (by rfl) ⟨1496714, by rfl⟩ : syracuseStep 1995619 = 2993429) B2993429
theorem B2160145 : Blo 1995435 2160145 := bbase (se 2 (by rfl) ⟨810054, by rfl⟩ : syracuseStep 2160145 = 1620109) (by norm_num)
theorem B2880193 : Blo 1995435 2880193 := bstep (se 2 (by rfl) ⟨1080072, by rfl⟩ : syracuseStep 2880193 = 2160145) B2160145
theorem B3840257 : Blo 1995435 3840257 := bstep (se 2 (by rfl) ⟨1440096, by rfl⟩ : syracuseStep 3840257 = 2880193) B2880193
theorem B10240685 : Blo 1995435 10240685 := bstep (se 3 (by rfl) ⟨1920128, by rfl⟩ : syracuseStep 10240685 = 3840257) B3840257
theorem B6827123 : Blo 1995435 6827123 := bstep (se 1 (by rfl) ⟨5120342, by rfl⟩ : syracuseStep 6827123 = 10240685) B10240685
theorem B18205661 : Blo 1995435 18205661 := bstep (se 3 (by rfl) ⟨3413561, by rfl⟩ : syracuseStep 18205661 = 6827123) B6827123
theorem B48548429 : Blo 1995435 48548429 := bstep (se 3 (by rfl) ⟨9102830, by rfl⟩ : syracuseStep 48548429 = 18205661) B18205661
theorem B32365619 : Blo 1995435 32365619 := bstep (se 1 (by rfl) ⟨24274214, by rfl⟩ : syracuseStep 32365619 = 48548429) B48548429
theorem B21577079 : Blo 1995435 21577079 := bstep (se 1 (by rfl) ⟨16182809, by rfl⟩ : syracuseStep 21577079 = 32365619) B32365619
theorem B14384719 : Blo 1995435 14384719 := bstep (se 1 (by rfl) ⟨10788539, by rfl⟩ : syracuseStep 14384719 = 21577079) B21577079
theorem B19179625 : Blo 1995435 19179625 := bstep (se 2 (by rfl) ⟨7192359, by rfl⟩ : syracuseStep 19179625 = 14384719) B14384719
theorem B25572833 : Blo 1995435 25572833 := bstep (se 2 (by rfl) ⟨9589812, by rfl⟩ : syracuseStep 25572833 = 19179625) B19179625
theorem B17048555 : Blo 1995435 17048555 := bstep (se 1 (by rfl) ⟨12786416, by rfl⟩ : syracuseStep 17048555 = 25572833) B25572833
theorem B11365703 : Blo 1995435 11365703 := bstep (se 1 (by rfl) ⟨8524277, by rfl⟩ : syracuseStep 11365703 = 17048555) B17048555
theorem B7577135 : Blo 1995435 7577135 := bstep (se 1 (by rfl) ⟨5682851, by rfl⟩ : syracuseStep 7577135 = 11365703) B11365703
theorem B5051423 : Blo 1995435 5051423 := bstep (se 1 (by rfl) ⟨3788567, by rfl⟩ : syracuseStep 5051423 = 7577135) B7577135
theorem B3367615 : Blo 1995435 3367615 := bstep (se 1 (by rfl) ⟨2525711, by rfl⟩ : syracuseStep 3367615 = 5051423) B5051423
theorem B4490153 : Blo 1995435 4490153 := bstep (se 2 (by rfl) ⟨1683807, by rfl⟩ : syracuseStep 4490153 = 3367615) B3367615
theorem B2993435 : Blo 1995435 2993435 := bstep (se 1 (by rfl) ⟨2245076, by rfl⟩ : syracuseStep 2993435 = 4490153) B4490153
theorem B1995623 : Blo 1995435 1995623 := bstep (se 1 (by rfl) ⟨1496717, by rfl⟩ : syracuseStep 1995623 = 2993435) B2993435
theorem B2245081 : Blo 1995435 2245081 := bbase (se 2 (by rfl) ⟨841905, by rfl⟩ : syracuseStep 2245081 = 1683811) (by norm_num)
theorem B2993441 : Blo 1995435 2993441 := bstep (se 2 (by rfl) ⟨1122540, by rfl⟩ : syracuseStep 2993441 = 2245081) B2245081
theorem B1995627 : Blo 1995435 1995627 := bstep (se 1 (by rfl) ⟨1496720, by rfl⟩ : syracuseStep 1995627 = 2993441) B2993441
theorem B2841437 : Blo 1995435 2841437 := bbase (se 3 (by rfl) ⟨532769, by rfl⟩ : syracuseStep 2841437 = 1065539) (by norm_num)
theorem B7577165 : Blo 1995435 7577165 := bstep (se 3 (by rfl) ⟨1420718, by rfl⟩ : syracuseStep 7577165 = 2841437) B2841437
theorem B5051443 : Blo 1995435 5051443 := bstep (se 1 (by rfl) ⟨3788582, by rfl⟩ : syracuseStep 5051443 = 7577165) B7577165
theorem B6735257 : Blo 1995435 6735257 := bstep (se 2 (by rfl) ⟨2525721, by rfl⟩ : syracuseStep 6735257 = 5051443) B5051443
theorem B4490171 : Blo 1995435 4490171 := bstep (se 1 (by rfl) ⟨3367628, by rfl⟩ : syracuseStep 4490171 = 6735257) B6735257
theorem B2993447 : Blo 1995435 2993447 := bstep (se 1 (by rfl) ⟨2245085, by rfl⟩ : syracuseStep 2993447 = 4490171) B4490171
theorem B1995631 : Blo 1995435 1995631 := bstep (se 1 (by rfl) ⟨1496723, by rfl⟩ : syracuseStep 1995631 = 2993447) B2993447
theorem B2993453 : Blo 1995435 2993453 := bbase (se 3 (by rfl) ⟨561272, by rfl⟩ : syracuseStep 2993453 = 1122545) (by norm_num)
theorem B1995635 : Blo 1995435 1995635 := bstep (se 1 (by rfl) ⟨1496726, by rfl⟩ : syracuseStep 1995635 = 2993453) B2993453
theorem B4490189 : Blo 1995435 4490189 := bbase (se 3 (by rfl) ⟨841910, by rfl⟩ : syracuseStep 4490189 = 1683821) (by norm_num)
theorem B2993459 : Blo 1995435 2993459 := bstep (se 1 (by rfl) ⟨2245094, by rfl⟩ : syracuseStep 2993459 = 4490189) B4490189
theorem B1995639 : Blo 1995435 1995639 := bstep (se 1 (by rfl) ⟨1496729, by rfl⟩ : syracuseStep 1995639 = 2993459) B2993459
theorem B2525737 : Blo 1995435 2525737 := bbase (se 2 (by rfl) ⟨947151, by rfl⟩ : syracuseStep 2525737 = 1894303) (by norm_num)
theorem B3367649 : Blo 1995435 3367649 := bstep (se 2 (by rfl) ⟨1262868, by rfl⟩ : syracuseStep 3367649 = 2525737) B2525737
theorem B2245099 : Blo 1995435 2245099 := bstep (se 1 (by rfl) ⟨1683824, by rfl⟩ : syracuseStep 2245099 = 3367649) B3367649
theorem B2993465 : Blo 1995435 2993465 := bstep (se 2 (by rfl) ⟨1122549, by rfl⟩ : syracuseStep 2993465 = 2245099) B2245099
theorem B1995643 : Blo 1995435 1995643 := bstep (se 1 (by rfl) ⟨1496732, by rfl⟩ : syracuseStep 1995643 = 2993465) B2993465
theorem B8219045 : Blo 1995435 8219045 := bbase (se 4 (by rfl) ⟨770535, by rfl⟩ : syracuseStep 8219045 = 1541071) (by norm_num)
theorem B5479363 : Blo 1995435 5479363 := bstep (se 1 (by rfl) ⟨4109522, by rfl⟩ : syracuseStep 5479363 = 8219045) B8219045
theorem B7305817 : Blo 1995435 7305817 := bstep (se 2 (by rfl) ⟨2739681, by rfl⟩ : syracuseStep 7305817 = 5479363) B5479363
theorem B9741089 : Blo 1995435 9741089 := bstep (se 2 (by rfl) ⟨3652908, by rfl⟩ : syracuseStep 9741089 = 7305817) B7305817
theorem B6494059 : Blo 1995435 6494059 := bstep (se 1 (by rfl) ⟨4870544, by rfl⟩ : syracuseStep 6494059 = 9741089) B9741089
theorem B34634981 : Blo 1995435 34634981 := bstep (se 4 (by rfl) ⟨3247029, by rfl⟩ : syracuseStep 34634981 = 6494059) B6494059
theorem B23089987 : Blo 1995435 23089987 := bstep (se 1 (by rfl) ⟨17317490, by rfl⟩ : syracuseStep 23089987 = 34634981) B34634981
theorem B30786649 : Blo 1995435 30786649 := bstep (se 2 (by rfl) ⟨11544993, by rfl⟩ : syracuseStep 30786649 = 23089987) B23089987
theorem B164195461 : Blo 1995435 164195461 := bstep (se 4 (by rfl) ⟨15393324, by rfl⟩ : syracuseStep 164195461 = 30786649) B30786649
theorem B218927281 : Blo 1995435 218927281 := bstep (se 2 (by rfl) ⟨82097730, by rfl⟩ : syracuseStep 218927281 = 164195461) B164195461
theorem B291903041 : Blo 1995435 291903041 := bstep (se 2 (by rfl) ⟨109463640, by rfl⟩ : syracuseStep 291903041 = 218927281) B218927281
theorem B194602027 : Blo 1995435 194602027 := bstep (se 1 (by rfl) ⟨145951520, by rfl⟩ : syracuseStep 194602027 = 291903041) B291903041
theorem B259469369 : Blo 1995435 259469369 := bstep (se 2 (by rfl) ⟨97301013, by rfl⟩ : syracuseStep 259469369 = 194602027) B194602027
theorem B172979579 : Blo 1995435 172979579 := bstep (se 1 (by rfl) ⟨129734684, by rfl⟩ : syracuseStep 172979579 = 259469369) B259469369
theorem B115319719 : Blo 1995435 115319719 := bstep (se 1 (by rfl) ⟨86489789, by rfl⟩ : syracuseStep 115319719 = 172979579) B172979579
theorem B153759625 : Blo 1995435 153759625 := bstep (se 2 (by rfl) ⟨57659859, by rfl⟩ : syracuseStep 153759625 = 115319719) B115319719
theorem B820051333 : Blo 1995435 820051333 := bstep (se 4 (by rfl) ⟨76879812, by rfl⟩ : syracuseStep 820051333 = 153759625) B153759625
theorem B17494428437 : Blo 1995435 17494428437 := bstep (se 6 (by rfl) ⟨410025666, by rfl⟩ : syracuseStep 17494428437 = 820051333) B820051333
theorem B11662952291 : Blo 1995435 11662952291 := bstep (se 1 (by rfl) ⟨8747214218, by rfl⟩ : syracuseStep 11662952291 = 17494428437) B17494428437
theorem B7775301527 : Blo 1995435 7775301527 := bstep (se 1 (by rfl) ⟨5831476145, by rfl⟩ : syracuseStep 7775301527 = 11662952291) B11662952291
theorem B5183534351 : Blo 1995435 5183534351 := bstep (se 1 (by rfl) ⟨3887650763, by rfl⟩ : syracuseStep 5183534351 = 7775301527) B7775301527
theorem B3455689567 : Blo 1995435 3455689567 := bstep (se 1 (by rfl) ⟨2591767175, by rfl⟩ : syracuseStep 3455689567 = 5183534351) B5183534351
theorem B4607586089 : Blo 1995435 4607586089 := bstep (se 2 (by rfl) ⟨1727844783, by rfl⟩ : syracuseStep 4607586089 = 3455689567) B3455689567
theorem B3071724059 : Blo 1995435 3071724059 := bstep (se 1 (by rfl) ⟨2303793044, by rfl⟩ : syracuseStep 3071724059 = 4607586089) B4607586089
theorem B2047816039 : Blo 1995435 2047816039 := bstep (se 1 (by rfl) ⟨1535862029, by rfl⟩ : syracuseStep 2047816039 = 3071724059) B3071724059
theorem B2730421385 : Blo 1995435 2730421385 := bstep (se 2 (by rfl) ⟨1023908019, by rfl⟩ : syracuseStep 2730421385 = 2047816039) B2047816039
theorem B1820280923 : Blo 1995435 1820280923 := bstep (se 1 (by rfl) ⟨1365210692, by rfl⟩ : syracuseStep 1820280923 = 2730421385) B2730421385
theorem B1213520615 : Blo 1995435 1213520615 := bstep (se 1 (by rfl) ⟨910140461, by rfl⟩ : syracuseStep 1213520615 = 1820280923) B1820280923
theorem B809013743 : Blo 1995435 809013743 := bstep (se 1 (by rfl) ⟨606760307, by rfl⟩ : syracuseStep 809013743 = 1213520615) B1213520615
theorem B539342495 : Blo 1995435 539342495 := bstep (se 1 (by rfl) ⟨404506871, by rfl⟩ : syracuseStep 539342495 = 809013743) B809013743
theorem B359561663 : Blo 1995435 359561663 := bstep (se 1 (by rfl) ⟨269671247, by rfl⟩ : syracuseStep 359561663 = 539342495) B539342495
theorem B239707775 : Blo 1995435 239707775 := bstep (se 1 (by rfl) ⟨179780831, by rfl⟩ : syracuseStep 239707775 = 359561663) B359561663
theorem B639220733 : Blo 1995435 639220733 := bstep (se 3 (by rfl) ⟨119853887, by rfl⟩ : syracuseStep 639220733 = 239707775) B239707775
theorem B426147155 : Blo 1995435 426147155 := bstep (se 1 (by rfl) ⟨319610366, by rfl⟩ : syracuseStep 426147155 = 639220733) B639220733
theorem B284098103 : Blo 1995435 284098103 := bstep (se 1 (by rfl) ⟨213073577, by rfl⟩ : syracuseStep 284098103 = 426147155) B426147155
theorem B189398735 : Blo 1995435 189398735 := bstep (se 1 (by rfl) ⟨142049051, by rfl⟩ : syracuseStep 189398735 = 284098103) B284098103
theorem B126265823 : Blo 1995435 126265823 := bstep (se 1 (by rfl) ⟨94699367, by rfl⟩ : syracuseStep 126265823 = 189398735) B189398735
theorem B84177215 : Blo 1995435 84177215 := bstep (se 1 (by rfl) ⟨63132911, by rfl⟩ : syracuseStep 84177215 = 126265823) B126265823
theorem B56118143 : Blo 1995435 56118143 := bstep (se 1 (by rfl) ⟨42088607, by rfl⟩ : syracuseStep 56118143 = 84177215) B84177215
theorem B149648381 : Blo 1995435 149648381 := bstep (se 3 (by rfl) ⟨28059071, by rfl⟩ : syracuseStep 149648381 = 56118143) B56118143
theorem B99765587 : Blo 1995435 99765587 := bstep (se 1 (by rfl) ⟨74824190, by rfl⟩ : syracuseStep 99765587 = 149648381) B149648381
theorem B66510391 : Blo 1995435 66510391 := bstep (se 1 (by rfl) ⟨49882793, by rfl⟩ : syracuseStep 66510391 = 99765587) B99765587
theorem B88680521 : Blo 1995435 88680521 := bstep (se 2 (by rfl) ⟨33255195, by rfl⟩ : syracuseStep 88680521 = 66510391) B66510391
theorem B236481389 : Blo 1995435 236481389 := bstep (se 3 (by rfl) ⟨44340260, by rfl⟩ : syracuseStep 236481389 = 88680521) B88680521
theorem B157654259 : Blo 1995435 157654259 := bstep (se 1 (by rfl) ⟨118240694, by rfl⟩ : syracuseStep 157654259 = 236481389) B236481389
theorem B105102839 : Blo 1995435 105102839 := bstep (se 1 (by rfl) ⟨78827129, by rfl⟩ : syracuseStep 105102839 = 157654259) B157654259
theorem B70068559 : Blo 1995435 70068559 := bstep (se 1 (by rfl) ⟨52551419, by rfl⟩ : syracuseStep 70068559 = 105102839) B105102839
theorem B93424745 : Blo 1995435 93424745 := bstep (se 2 (by rfl) ⟨35034279, by rfl⟩ : syracuseStep 93424745 = 70068559) B70068559
theorem B62283163 : Blo 1995435 62283163 := bstep (se 1 (by rfl) ⟨46712372, by rfl⟩ : syracuseStep 62283163 = 93424745) B93424745
theorem B83044217 : Blo 1995435 83044217 := bstep (se 2 (by rfl) ⟨31141581, by rfl⟩ : syracuseStep 83044217 = 62283163) B62283163
theorem B55362811 : Blo 1995435 55362811 := bstep (se 1 (by rfl) ⟨41522108, by rfl⟩ : syracuseStep 55362811 = 83044217) B83044217
theorem B73817081 : Blo 1995435 73817081 := bstep (se 2 (by rfl) ⟨27681405, by rfl⟩ : syracuseStep 73817081 = 55362811) B55362811
theorem B49211387 : Blo 1995435 49211387 := bstep (se 1 (by rfl) ⟨36908540, by rfl⟩ : syracuseStep 49211387 = 73817081) B73817081
theorem B32807591 : Blo 1995435 32807591 := bstep (se 1 (by rfl) ⟨24605693, by rfl⟩ : syracuseStep 32807591 = 49211387) B49211387
theorem B21871727 : Blo 1995435 21871727 := bstep (se 1 (by rfl) ⟨16403795, by rfl⟩ : syracuseStep 21871727 = 32807591) B32807591
theorem B14581151 : Blo 1995435 14581151 := bstep (se 1 (by rfl) ⟨10935863, by rfl⟩ : syracuseStep 14581151 = 21871727) B21871727
theorem B9720767 : Blo 1995435 9720767 := bstep (se 1 (by rfl) ⟨7290575, by rfl⟩ : syracuseStep 9720767 = 14581151) B14581151
theorem B25922045 : Blo 1995435 25922045 := bstep (se 3 (by rfl) ⟨4860383, by rfl⟩ : syracuseStep 25922045 = 9720767) B9720767
theorem B17281363 : Blo 1995435 17281363 := bstep (se 1 (by rfl) ⟨12961022, by rfl⟩ : syracuseStep 17281363 = 25922045) B25922045
theorem B23041817 : Blo 1995435 23041817 := bstep (se 2 (by rfl) ⟨8640681, by rfl⟩ : syracuseStep 23041817 = 17281363) B17281363
theorem B15361211 : Blo 1995435 15361211 := bstep (se 1 (by rfl) ⟨11520908, by rfl⟩ : syracuseStep 15361211 = 23041817) B23041817
theorem B40963229 : Blo 1995435 40963229 := bstep (se 3 (by rfl) ⟨7680605, by rfl⟩ : syracuseStep 40963229 = 15361211) B15361211
theorem B27308819 : Blo 1995435 27308819 := bstep (se 1 (by rfl) ⟨20481614, by rfl⟩ : syracuseStep 27308819 = 40963229) B40963229
theorem B18205879 : Blo 1995435 18205879 := bstep (se 1 (by rfl) ⟨13654409, by rfl⟩ : syracuseStep 18205879 = 27308819) B27308819
theorem B24274505 : Blo 1995435 24274505 := bstep (se 2 (by rfl) ⟨9102939, by rfl⟩ : syracuseStep 24274505 = 18205879) B18205879
theorem B16183003 : Blo 1995435 16183003 := bstep (se 1 (by rfl) ⟨12137252, by rfl⟩ : syracuseStep 16183003 = 24274505) B24274505
theorem B21577337 : Blo 1995435 21577337 := bstep (se 2 (by rfl) ⟨8091501, by rfl⟩ : syracuseStep 21577337 = 16183003) B16183003
theorem B14384891 : Blo 1995435 14384891 := bstep (se 1 (by rfl) ⟨10788668, by rfl⟩ : syracuseStep 14384891 = 21577337) B21577337
theorem B9589927 : Blo 1995435 9589927 := bstep (se 1 (by rfl) ⟨7192445, by rfl⟩ : syracuseStep 9589927 = 14384891) B14384891
theorem B12786569 : Blo 1995435 12786569 := bstep (se 2 (by rfl) ⟨4794963, by rfl⟩ : syracuseStep 12786569 = 9589927) B9589927
theorem B8524379 : Blo 1995435 8524379 := bstep (se 1 (by rfl) ⟨6393284, by rfl⟩ : syracuseStep 8524379 = 12786569) B12786569
theorem B22731677 : Blo 1995435 22731677 := bstep (se 3 (by rfl) ⟨4262189, by rfl⟩ : syracuseStep 22731677 = 8524379) B8524379
theorem B15154451 : Blo 1995435 15154451 := bstep (se 1 (by rfl) ⟨11365838, by rfl⟩ : syracuseStep 15154451 = 22731677) B22731677
theorem B10102967 : Blo 1995435 10102967 := bstep (se 1 (by rfl) ⟨7577225, by rfl⟩ : syracuseStep 10102967 = 15154451) B15154451
theorem B6735311 : Blo 1995435 6735311 := bstep (se 1 (by rfl) ⟨5051483, by rfl⟩ : syracuseStep 6735311 = 10102967) B10102967
theorem B4490207 : Blo 1995435 4490207 := bstep (se 1 (by rfl) ⟨3367655, by rfl⟩ : syracuseStep 4490207 = 6735311) B6735311
theorem B2993471 : Blo 1995435 2993471 := bstep (se 1 (by rfl) ⟨2245103, by rfl⟩ : syracuseStep 2993471 = 4490207) B4490207
theorem B1995647 : Blo 1995435 1995647 := bstep (se 1 (by rfl) ⟨1496735, by rfl⟩ : syracuseStep 1995647 = 2993471) B2993471
theorem B2993477 : Blo 1995435 2993477 := bbase (se 4 (by rfl) ⟨280638, by rfl⟩ : syracuseStep 2993477 = 561277) (by norm_num)
theorem B1995651 : Blo 1995435 1995651 := bstep (se 1 (by rfl) ⟨1496738, by rfl⟩ : syracuseStep 1995651 = 2993477) B2993477
theorem B3367669 : Blo 1995435 3367669 := bbase (se 5 (by rfl) ⟨157859, by rfl⟩ : syracuseStep 3367669 = 315719) (by norm_num)
theorem B4490225 : Blo 1995435 4490225 := bstep (se 2 (by rfl) ⟨1683834, by rfl⟩ : syracuseStep 4490225 = 3367669) B3367669
theorem B2993483 : Blo 1995435 2993483 := bstep (se 1 (by rfl) ⟨2245112, by rfl⟩ : syracuseStep 2993483 = 4490225) B4490225
theorem B1995655 : Blo 1995435 1995655 := bstep (se 1 (by rfl) ⟨1496741, by rfl⟩ : syracuseStep 1995655 = 2993483) B2993483
theorem B2245117 : Blo 1995435 2245117 := bbase (se 3 (by rfl) ⟨420959, by rfl⟩ : syracuseStep 2245117 = 841919) (by norm_num)
theorem B2993489 : Blo 1995435 2993489 := bstep (se 2 (by rfl) ⟨1122558, by rfl⟩ : syracuseStep 2993489 = 2245117) B2245117
theorem B1995659 : Blo 1995435 1995659 := bstep (se 1 (by rfl) ⟨1496744, by rfl⟩ : syracuseStep 1995659 = 2993489) B2993489
theorem B6735365 : Blo 1995435 6735365 := bbase (se 4 (by rfl) ⟨631440, by rfl⟩ : syracuseStep 6735365 = 1262881) (by norm_num)
theorem B4490243 : Blo 1995435 4490243 := bstep (se 1 (by rfl) ⟨3367682, by rfl⟩ : syracuseStep 4490243 = 6735365) B6735365
theorem B2993495 : Blo 1995435 2993495 := bstep (se 1 (by rfl) ⟨2245121, by rfl⟩ : syracuseStep 2993495 = 4490243) B4490243
theorem B1995663 : Blo 1995435 1995663 := bstep (se 1 (by rfl) ⟨1496747, by rfl⟩ : syracuseStep 1995663 = 2993495) B2993495
theorem B2993501 : Blo 1995435 2993501 := bbase (se 3 (by rfl) ⟨561281, by rfl⟩ : syracuseStep 2993501 = 1122563) (by norm_num)
theorem B1995667 : Blo 1995435 1995667 := bstep (se 1 (by rfl) ⟨1496750, by rfl⟩ : syracuseStep 1995667 = 2993501) B2993501
theorem B4490261 : Blo 1995435 4490261 := bbase (se 6 (by rfl) ⟨105240, by rfl⟩ : syracuseStep 4490261 = 210481) (by norm_num)
theorem B2993507 : Blo 1995435 2993507 := bstep (se 1 (by rfl) ⟨2245130, by rfl⟩ : syracuseStep 2993507 = 4490261) B4490261
theorem B1995671 : Blo 1995435 1995671 := bstep (se 1 (by rfl) ⟨1496753, by rfl⟩ : syracuseStep 1995671 = 2993507) B2993507
theorem B7577333 : Blo 1995435 7577333 := bbase (se 5 (by rfl) ⟨355187, by rfl⟩ : syracuseStep 7577333 = 710375) (by norm_num)
theorem B5051555 : Blo 1995435 5051555 := bstep (se 1 (by rfl) ⟨3788666, by rfl⟩ : syracuseStep 5051555 = 7577333) B7577333
theorem B3367703 : Blo 1995435 3367703 := bstep (se 1 (by rfl) ⟨2525777, by rfl⟩ : syracuseStep 3367703 = 5051555) B5051555
theorem B2245135 : Blo 1995435 2245135 := bstep (se 1 (by rfl) ⟨1683851, by rfl⟩ : syracuseStep 2245135 = 3367703) B3367703
theorem B2993513 : Blo 1995435 2993513 := bstep (se 2 (by rfl) ⟨1122567, by rfl⟩ : syracuseStep 2993513 = 2245135) B2245135
theorem B1995675 : Blo 1995435 1995675 := bstep (se 1 (by rfl) ⟨1496756, by rfl⟩ : syracuseStep 1995675 = 2993513) B2993513
theorem B2131129 : Blo 1995435 2131129 := bbase (se 2 (by rfl) ⟨799173, by rfl⟩ : syracuseStep 2131129 = 1598347) (by norm_num)
theorem B11366021 : Blo 1995435 11366021 := bstep (se 4 (by rfl) ⟨1065564, by rfl⟩ : syracuseStep 11366021 = 2131129) B2131129
theorem B7577347 : Blo 1995435 7577347 := bstep (se 1 (by rfl) ⟨5683010, by rfl⟩ : syracuseStep 7577347 = 11366021) B11366021
theorem B10103129 : Blo 1995435 10103129 := bstep (se 2 (by rfl) ⟨3788673, by rfl⟩ : syracuseStep 10103129 = 7577347) B7577347
theorem B6735419 : Blo 1995435 6735419 := bstep (se 1 (by rfl) ⟨5051564, by rfl⟩ : syracuseStep 6735419 = 10103129) B10103129
theorem B4490279 : Blo 1995435 4490279 := bstep (se 1 (by rfl) ⟨3367709, by rfl⟩ : syracuseStep 4490279 = 6735419) B6735419
theorem B2993519 : Blo 1995435 2993519 := bstep (se 1 (by rfl) ⟨2245139, by rfl⟩ : syracuseStep 2993519 = 4490279) B4490279
theorem B1995679 : Blo 1995435 1995679 := bstep (se 1 (by rfl) ⟨1496759, by rfl⟩ : syracuseStep 1995679 = 2993519) B2993519
theorem B2993525 : Blo 1995435 2993525 := bbase (se 5 (by rfl) ⟨140321, by rfl⟩ : syracuseStep 2993525 = 280643) (by norm_num)
theorem B1995683 : Blo 1995435 1995683 := bstep (se 1 (by rfl) ⟨1496762, by rfl⟩ : syracuseStep 1995683 = 2993525) B2993525
theorem B2841517 : Blo 1995435 2841517 := bbase (se 3 (by rfl) ⟨532784, by rfl⟩ : syracuseStep 2841517 = 1065569) (by norm_num)
theorem B3788689 : Blo 1995435 3788689 := bstep (se 2 (by rfl) ⟨1420758, by rfl⟩ : syracuseStep 3788689 = 2841517) B2841517
theorem B5051585 : Blo 1995435 5051585 := bstep (se 2 (by rfl) ⟨1894344, by rfl⟩ : syracuseStep 5051585 = 3788689) B3788689
theorem B3367723 : Blo 1995435 3367723 := bstep (se 1 (by rfl) ⟨2525792, by rfl⟩ : syracuseStep 3367723 = 5051585) B5051585
theorem B4490297 : Blo 1995435 4490297 := bstep (se 2 (by rfl) ⟨1683861, by rfl⟩ : syracuseStep 4490297 = 3367723) B3367723
theorem B2993531 : Blo 1995435 2993531 := bstep (se 1 (by rfl) ⟨2245148, by rfl⟩ : syracuseStep 2993531 = 4490297) B4490297
theorem B1995687 : Blo 1995435 1995687 := bstep (se 1 (by rfl) ⟨1496765, by rfl⟩ : syracuseStep 1995687 = 2993531) B2993531
theorem B2245153 : Blo 1995435 2245153 := bbase (se 2 (by rfl) ⟨841932, by rfl⟩ : syracuseStep 2245153 = 1683865) (by norm_num)
theorem B2993537 : Blo 1995435 2993537 := bstep (se 2 (by rfl) ⟨1122576, by rfl⟩ : syracuseStep 2993537 = 2245153) B2245153
theorem B1995691 : Blo 1995435 1995691 := bstep (se 1 (by rfl) ⟨1496768, by rfl⟩ : syracuseStep 1995691 = 2993537) B2993537
theorem B5051605 : Blo 1995435 5051605 := bbase (se 7 (by rfl) ⟨59198, by rfl⟩ : syracuseStep 5051605 = 118397) (by norm_num)
theorem B6735473 : Blo 1995435 6735473 := bstep (se 2 (by rfl) ⟨2525802, by rfl⟩ : syracuseStep 6735473 = 5051605) B5051605
theorem B4490315 : Blo 1995435 4490315 := bstep (se 1 (by rfl) ⟨3367736, by rfl⟩ : syracuseStep 4490315 = 6735473) B6735473
theorem B2993543 : Blo 1995435 2993543 := bstep (se 1 (by rfl) ⟨2245157, by rfl⟩ : syracuseStep 2993543 = 4490315) B4490315
theorem B1995695 : Blo 1995435 1995695 := bstep (se 1 (by rfl) ⟨1496771, by rfl⟩ : syracuseStep 1995695 = 2993543) B2993543
theorem B2993549 : Blo 1995435 2993549 := bbase (se 3 (by rfl) ⟨561290, by rfl⟩ : syracuseStep 2993549 = 1122581) (by norm_num)
theorem B1995699 : Blo 1995435 1995699 := bstep (se 1 (by rfl) ⟨1496774, by rfl⟩ : syracuseStep 1995699 = 2993549) B2993549
theorem B4490333 : Blo 1995435 4490333 := bbase (se 3 (by rfl) ⟨841937, by rfl⟩ : syracuseStep 4490333 = 1683875) (by norm_num)
theorem B2993555 : Blo 1995435 2993555 := bstep (se 1 (by rfl) ⟨2245166, by rfl⟩ : syracuseStep 2993555 = 4490333) B4490333
theorem B1995703 : Blo 1995435 1995703 := bstep (se 1 (by rfl) ⟨1496777, by rfl⟩ : syracuseStep 1995703 = 2993555) B2993555
theorem B3367757 : Blo 1995435 3367757 := bbase (se 3 (by rfl) ⟨631454, by rfl⟩ : syracuseStep 3367757 = 1262909) (by norm_num)
theorem B2245171 : Blo 1995435 2245171 := bstep (se 1 (by rfl) ⟨1683878, by rfl⟩ : syracuseStep 2245171 = 3367757) B3367757
theorem B2993561 : Blo 1995435 2993561 := bstep (se 2 (by rfl) ⟨1122585, by rfl⟩ : syracuseStep 2993561 = 2245171) B2245171
theorem B1995707 : Blo 1995435 1995707 := bstep (se 1 (by rfl) ⟨1496780, by rfl⟩ : syracuseStep 1995707 = 2993561) B2993561
theorem B19180469 : Blo 1995435 19180469 := bbase (se 5 (by rfl) ⟨899084, by rfl⟩ : syracuseStep 19180469 = 1798169) (by norm_num)
theorem B12786979 : Blo 1995435 12786979 := bstep (se 1 (by rfl) ⟨9590234, by rfl⟩ : syracuseStep 12786979 = 19180469) B19180469
theorem B17049305 : Blo 1995435 17049305 := bstep (se 2 (by rfl) ⟨6393489, by rfl⟩ : syracuseStep 17049305 = 12786979) B12786979
theorem B11366203 : Blo 1995435 11366203 := bstep (se 1 (by rfl) ⟨8524652, by rfl⟩ : syracuseStep 11366203 = 17049305) B17049305
theorem B15154937 : Blo 1995435 15154937 := bstep (se 2 (by rfl) ⟨5683101, by rfl⟩ : syracuseStep 15154937 = 11366203) B11366203
theorem B10103291 : Blo 1995435 10103291 := bstep (se 1 (by rfl) ⟨7577468, by rfl⟩ : syracuseStep 10103291 = 15154937) B15154937
theorem B6735527 : Blo 1995435 6735527 := bstep (se 1 (by rfl) ⟨5051645, by rfl⟩ : syracuseStep 6735527 = 10103291) B10103291
theorem B4490351 : Blo 1995435 4490351 := bstep (se 1 (by rfl) ⟨3367763, by rfl⟩ : syracuseStep 4490351 = 6735527) B6735527
theorem B2993567 : Blo 1995435 2993567 := bstep (se 1 (by rfl) ⟨2245175, by rfl⟩ : syracuseStep 2993567 = 4490351) B4490351
theorem B1995711 : Blo 1995435 1995711 := bstep (se 1 (by rfl) ⟨1496783, by rfl⟩ : syracuseStep 1995711 = 2993567) B2993567
theorem B2993573 : Blo 1995435 2993573 := bbase (se 4 (by rfl) ⟨280647, by rfl⟩ : syracuseStep 2993573 = 561295) (by norm_num)
theorem B1995715 : Blo 1995435 1995715 := bstep (se 1 (by rfl) ⟨1496786, by rfl⟩ : syracuseStep 1995715 = 2993573) B2993573
theorem B2525833 : Blo 1995435 2525833 := bbase (se 2 (by rfl) ⟨947187, by rfl⟩ : syracuseStep 2525833 = 1894375) (by norm_num)
theorem B3367777 : Blo 1995435 3367777 := bstep (se 2 (by rfl) ⟨1262916, by rfl⟩ : syracuseStep 3367777 = 2525833) B2525833
theorem B4490369 : Blo 1995435 4490369 := bstep (se 2 (by rfl) ⟨1683888, by rfl⟩ : syracuseStep 4490369 = 3367777) B3367777
theorem B2993579 : Blo 1995435 2993579 := bstep (se 1 (by rfl) ⟨2245184, by rfl⟩ : syracuseStep 2993579 = 4490369) B4490369
theorem B1995719 : Blo 1995435 1995719 := bstep (se 1 (by rfl) ⟨1496789, by rfl⟩ : syracuseStep 1995719 = 2993579) B2993579
theorem B2245189 : Blo 1995435 2245189 := bbase (se 4 (by rfl) ⟨210486, by rfl⟩ : syracuseStep 2245189 = 420973) (by norm_num)
theorem B2993585 : Blo 1995435 2993585 := bstep (se 2 (by rfl) ⟨1122594, by rfl⟩ : syracuseStep 2993585 = 2245189) B2245189
theorem B1995723 : Blo 1995435 1995723 := bstep (se 1 (by rfl) ⟨1496792, by rfl⟩ : syracuseStep 1995723 = 2993585) B2993585
theorem B3788765 : Blo 1995435 3788765 := bbase (se 3 (by rfl) ⟨710393, by rfl⟩ : syracuseStep 3788765 = 1420787) (by norm_num)
theorem B2525843 : Blo 1995435 2525843 := bstep (se 1 (by rfl) ⟨1894382, by rfl⟩ : syracuseStep 2525843 = 3788765) B3788765
theorem B6735581 : Blo 1995435 6735581 := bstep (se 3 (by rfl) ⟨1262921, by rfl⟩ : syracuseStep 6735581 = 2525843) B2525843
theorem B4490387 : Blo 1995435 4490387 := bstep (se 1 (by rfl) ⟨3367790, by rfl⟩ : syracuseStep 4490387 = 6735581) B6735581
theorem B2993591 : Blo 1995435 2993591 := bstep (se 1 (by rfl) ⟨2245193, by rfl⟩ : syracuseStep 2993591 = 4490387) B4490387
theorem B1995727 : Blo 1995435 1995727 := bstep (se 1 (by rfl) ⟨1496795, by rfl⟩ : syracuseStep 1995727 = 2993591) B2993591
theorem B2993597 : Blo 1995435 2993597 := bbase (se 3 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 2993597 = 1122599) (by norm_num)
theorem B1995731 : Blo 1995435 1995731 := bstep (se 1 (by rfl) ⟨1496798, by rfl⟩ : syracuseStep 1995731 = 2993597) B2993597
theorem B4490405 : Blo 1995435 4490405 := bbase (se 4 (by rfl) ⟨420975, by rfl⟩ : syracuseStep 4490405 = 841951) (by norm_num)
theorem B2993603 : Blo 1995435 2993603 := bstep (se 1 (by rfl) ⟨2245202, by rfl⟩ : syracuseStep 2993603 = 4490405) B4490405
theorem B1995735 : Blo 1995435 1995735 := bstep (se 1 (by rfl) ⟨1496801, by rfl⟩ : syracuseStep 1995735 = 2993603) B2993603
theorem B5051717 : Blo 1995435 5051717 := bbase (se 4 (by rfl) ⟨473598, by rfl⟩ : syracuseStep 5051717 = 947197) (by norm_num)
theorem B3367811 : Blo 1995435 3367811 := bstep (se 1 (by rfl) ⟨2525858, by rfl⟩ : syracuseStep 3367811 = 5051717) B5051717
theorem B2245207 : Blo 1995435 2245207 := bstep (se 1 (by rfl) ⟨1683905, by rfl⟩ : syracuseStep 2245207 = 3367811) B3367811
theorem B2993609 : Blo 1995435 2993609 := bstep (se 2 (by rfl) ⟨1122603, by rfl⟩ : syracuseStep 2993609 = 2245207) B2245207
theorem B1995739 : Blo 1995435 1995739 := bstep (se 1 (by rfl) ⟨1496804, by rfl⟩ : syracuseStep 1995739 = 2993609) B2993609
theorem B8091893 : Blo 1995435 8091893 := bbase (se 5 (by rfl) ⟨379307, by rfl⟩ : syracuseStep 8091893 = 758615) (by norm_num)
theorem B5394595 : Blo 1995435 5394595 := bstep (se 1 (by rfl) ⟨4045946, by rfl⟩ : syracuseStep 5394595 = 8091893) B8091893
theorem B7192793 : Blo 1995435 7192793 := bstep (se 2 (by rfl) ⟨2697297, by rfl⟩ : syracuseStep 7192793 = 5394595) B5394595
theorem B4795195 : Blo 1995435 4795195 := bstep (se 1 (by rfl) ⟨3596396, by rfl⟩ : syracuseStep 4795195 = 7192793) B7192793
theorem B6393593 : Blo 1995435 6393593 := bstep (se 2 (by rfl) ⟨2397597, by rfl⟩ : syracuseStep 6393593 = 4795195) B4795195
theorem B4262395 : Blo 1995435 4262395 := bstep (se 1 (by rfl) ⟨3196796, by rfl⟩ : syracuseStep 4262395 = 6393593) B6393593
theorem B5683193 : Blo 1995435 5683193 := bstep (se 2 (by rfl) ⟨2131197, by rfl⟩ : syracuseStep 5683193 = 4262395) B4262395
theorem B3788795 : Blo 1995435 3788795 := bstep (se 1 (by rfl) ⟨2841596, by rfl⟩ : syracuseStep 3788795 = 5683193) B5683193
theorem B10103453 : Blo 1995435 10103453 := bstep (se 3 (by rfl) ⟨1894397, by rfl⟩ : syracuseStep 10103453 = 3788795) B3788795
theorem B6735635 : Blo 1995435 6735635 := bstep (se 1 (by rfl) ⟨5051726, by rfl⟩ : syracuseStep 6735635 = 10103453) B10103453
theorem B4490423 : Blo 1995435 4490423 := bstep (se 1 (by rfl) ⟨3367817, by rfl⟩ : syracuseStep 4490423 = 6735635) B6735635
theorem B2993615 : Blo 1995435 2993615 := bstep (se 1 (by rfl) ⟨2245211, by rfl⟩ : syracuseStep 2993615 = 4490423) B4490423
theorem B1995743 : Blo 1995435 1995743 := bstep (se 1 (by rfl) ⟨1496807, by rfl⟩ : syracuseStep 1995743 = 2993615) B2993615
theorem B2993621 : Blo 1995435 2993621 := bbase (se 7 (by rfl) ⟨35081, by rfl⟩ : syracuseStep 2993621 = 70163) (by norm_num)
theorem B1995747 : Blo 1995435 1995747 := bstep (se 1 (by rfl) ⟨1496810, by rfl⟩ : syracuseStep 1995747 = 2993621) B2993621
theorem B7577621 : Blo 1995435 7577621 := bbase (se 6 (by rfl) ⟨177600, by rfl⟩ : syracuseStep 7577621 = 355201) (by norm_num)
theorem B5051747 : Blo 1995435 5051747 := bstep (se 1 (by rfl) ⟨3788810, by rfl⟩ : syracuseStep 5051747 = 7577621) B7577621
theorem B3367831 : Blo 1995435 3367831 := bstep (se 1 (by rfl) ⟨2525873, by rfl⟩ : syracuseStep 3367831 = 5051747) B5051747
theorem B4490441 : Blo 1995435 4490441 := bstep (se 2 (by rfl) ⟨1683915, by rfl⟩ : syracuseStep 4490441 = 3367831) B3367831
theorem B2993627 : Blo 1995435 2993627 := bstep (se 1 (by rfl) ⟨2245220, by rfl⟩ : syracuseStep 2993627 = 4490441) B4490441
theorem B1995751 : Blo 1995435 1995751 := bstep (se 1 (by rfl) ⟨1496813, by rfl⟩ : syracuseStep 1995751 = 2993627) B2993627
theorem B2245225 : Blo 1995435 2245225 := bbase (se 2 (by rfl) ⟨841959, by rfl⟩ : syracuseStep 2245225 = 1683919) (by norm_num)
theorem B2993633 : Blo 1995435 2993633 := bstep (se 2 (by rfl) ⟨1122612, by rfl⟩ : syracuseStep 2993633 = 2245225) B2245225
theorem B1995755 : Blo 1995435 1995755 := bstep (se 1 (by rfl) ⟨1496816, by rfl⟩ : syracuseStep 1995755 = 2993633) B2993633
theorem B4262429 : Blo 1995435 4262429 := bbase (se 3 (by rfl) ⟨799205, by rfl⟩ : syracuseStep 4262429 = 1598411) (by norm_num)
theorem B11366477 : Blo 1995435 11366477 := bstep (se 3 (by rfl) ⟨2131214, by rfl⟩ : syracuseStep 11366477 = 4262429) B4262429
theorem B7577651 : Blo 1995435 7577651 := bstep (se 1 (by rfl) ⟨5683238, by rfl⟩ : syracuseStep 7577651 = 11366477) B11366477
theorem B5051767 : Blo 1995435 5051767 := bstep (se 1 (by rfl) ⟨3788825, by rfl⟩ : syracuseStep 5051767 = 7577651) B7577651
theorem B6735689 : Blo 1995435 6735689 := bstep (se 2 (by rfl) ⟨2525883, by rfl⟩ : syracuseStep 6735689 = 5051767) B5051767
theorem B4490459 : Blo 1995435 4490459 := bstep (se 1 (by rfl) ⟨3367844, by rfl⟩ : syracuseStep 4490459 = 6735689) B6735689
theorem B2993639 : Blo 1995435 2993639 := bstep (se 1 (by rfl) ⟨2245229, by rfl⟩ : syracuseStep 2993639 = 4490459) B4490459
theorem B1995759 : Blo 1995435 1995759 := bstep (se 1 (by rfl) ⟨1496819, by rfl⟩ : syracuseStep 1995759 = 2993639) B2993639
theorem B2993645 : Blo 1995435 2993645 := bbase (se 3 (by rfl) ⟨561308, by rfl⟩ : syracuseStep 2993645 = 1122617) (by norm_num)
theorem B1995763 : Blo 1995435 1995763 := bstep (se 1 (by rfl) ⟨1496822, by rfl⟩ : syracuseStep 1995763 = 2993645) B2993645
theorem B4490477 : Blo 1995435 4490477 := bbase (se 3 (by rfl) ⟨841964, by rfl⟩ : syracuseStep 4490477 = 1683929) (by norm_num)
theorem B2993651 : Blo 1995435 2993651 := bstep (se 1 (by rfl) ⟨2245238, by rfl⟩ : syracuseStep 2993651 = 4490477) B4490477
theorem B1995767 : Blo 1995435 1995767 := bstep (se 1 (by rfl) ⟨1496825, by rfl⟩ : syracuseStep 1995767 = 2993651) B2993651
theorem B2841637 : Blo 1995435 2841637 := bbase (se 4 (by rfl) ⟨266403, by rfl⟩ : syracuseStep 2841637 = 532807) (by norm_num)
theorem B3788849 : Blo 1995435 3788849 := bstep (se 2 (by rfl) ⟨1420818, by rfl⟩ : syracuseStep 3788849 = 2841637) B2841637
theorem B2525899 : Blo 1995435 2525899 := bstep (se 1 (by rfl) ⟨1894424, by rfl⟩ : syracuseStep 2525899 = 3788849) B3788849
theorem B3367865 : Blo 1995435 3367865 := bstep (se 2 (by rfl) ⟨1262949, by rfl⟩ : syracuseStep 3367865 = 2525899) B2525899
theorem B2245243 : Blo 1995435 2245243 := bstep (se 1 (by rfl) ⟨1683932, by rfl⟩ : syracuseStep 2245243 = 3367865) B3367865
theorem B2993657 : Blo 1995435 2993657 := bstep (se 2 (by rfl) ⟨1122621, by rfl⟩ : syracuseStep 2993657 = 2245243) B2245243
theorem B1995771 : Blo 1995435 1995771 := bstep (se 1 (by rfl) ⟨1496828, by rfl⟩ : syracuseStep 1995771 = 2993657) B2993657
theorem B12814133 : Blo 1995435 12814133 := bbase (se 5 (by rfl) ⟨600662, by rfl⟩ : syracuseStep 12814133 = 1201325) (by norm_num)
theorem B34171021 : Blo 1995435 34171021 := bstep (se 3 (by rfl) ⟨6407066, by rfl⟩ : syracuseStep 34171021 = 12814133) B12814133
theorem B45561361 : Blo 1995435 45561361 := bstep (se 2 (by rfl) ⟨17085510, by rfl⟩ : syracuseStep 45561361 = 34171021) B34171021
theorem B60748481 : Blo 1995435 60748481 := bstep (se 2 (by rfl) ⟨22780680, by rfl⟩ : syracuseStep 60748481 = 45561361) B45561361
theorem B40498987 : Blo 1995435 40498987 := bstep (se 1 (by rfl) ⟨30374240, by rfl⟩ : syracuseStep 40498987 = 60748481) B60748481
theorem B53998649 : Blo 1995435 53998649 := bstep (se 2 (by rfl) ⟨20249493, by rfl⟩ : syracuseStep 53998649 = 40498987) B40498987
theorem B35999099 : Blo 1995435 35999099 := bstep (se 1 (by rfl) ⟨26999324, by rfl⟩ : syracuseStep 35999099 = 53998649) B53998649
theorem B23999399 : Blo 1995435 23999399 := bstep (se 1 (by rfl) ⟨17999549, by rfl⟩ : syracuseStep 23999399 = 35999099) B35999099
theorem B15999599 : Blo 1995435 15999599 := bstep (se 1 (by rfl) ⟨11999699, by rfl⟩ : syracuseStep 15999599 = 23999399) B23999399
theorem B10666399 : Blo 1995435 10666399 := bstep (se 1 (by rfl) ⟨7999799, by rfl⟩ : syracuseStep 10666399 = 15999599) B15999599
theorem B14221865 : Blo 1995435 14221865 := bstep (se 2 (by rfl) ⟨5333199, by rfl⟩ : syracuseStep 14221865 = 10666399) B10666399
theorem B37924973 : Blo 1995435 37924973 := bstep (se 3 (by rfl) ⟨7110932, by rfl⟩ : syracuseStep 37924973 = 14221865) B14221865
theorem B25283315 : Blo 1995435 25283315 := bstep (se 1 (by rfl) ⟨18962486, by rfl⟩ : syracuseStep 25283315 = 37924973) B37924973
theorem B16855543 : Blo 1995435 16855543 := bstep (se 1 (by rfl) ⟨12641657, by rfl⟩ : syracuseStep 16855543 = 25283315) B25283315
theorem B22474057 : Blo 1995435 22474057 := bstep (se 2 (by rfl) ⟨8427771, by rfl⟩ : syracuseStep 22474057 = 16855543) B16855543
theorem B29965409 : Blo 1995435 29965409 := bstep (se 2 (by rfl) ⟨11237028, by rfl⟩ : syracuseStep 29965409 = 22474057) B22474057
theorem B19976939 : Blo 1995435 19976939 := bstep (se 1 (by rfl) ⟨14982704, by rfl⟩ : syracuseStep 19976939 = 29965409) B29965409
theorem B13317959 : Blo 1995435 13317959 := bstep (se 1 (by rfl) ⟨9988469, by rfl⟩ : syracuseStep 13317959 = 19976939) B19976939
theorem B35514557 : Blo 1995435 35514557 := bstep (se 3 (by rfl) ⟨6658979, by rfl⟩ : syracuseStep 35514557 = 13317959) B13317959
theorem B23676371 : Blo 1995435 23676371 := bstep (se 1 (by rfl) ⟨17757278, by rfl⟩ : syracuseStep 23676371 = 35514557) B35514557
theorem B15784247 : Blo 1995435 15784247 := bstep (se 1 (by rfl) ⟨11838185, by rfl⟩ : syracuseStep 15784247 = 23676371) B23676371
theorem B10522831 : Blo 1995435 10522831 := bstep (se 1 (by rfl) ⟨7892123, by rfl⟩ : syracuseStep 10522831 = 15784247) B15784247
theorem B14030441 : Blo 1995435 14030441 := bstep (se 2 (by rfl) ⟨5261415, by rfl⟩ : syracuseStep 14030441 = 10522831) B10522831
theorem B9353627 : Blo 1995435 9353627 := bstep (se 1 (by rfl) ⟨7015220, by rfl⟩ : syracuseStep 9353627 = 14030441) B14030441
theorem B6235751 : Blo 1995435 6235751 := bstep (se 1 (by rfl) ⟨4676813, by rfl⟩ : syracuseStep 6235751 = 9353627) B9353627
theorem B4157167 : Blo 1995435 4157167 := bstep (se 1 (by rfl) ⟨3117875, by rfl⟩ : syracuseStep 4157167 = 6235751) B6235751
theorem B5542889 : Blo 1995435 5542889 := bstep (se 2 (by rfl) ⟨2078583, by rfl⟩ : syracuseStep 5542889 = 4157167) B4157167
theorem B14781037 : Blo 1995435 14781037 := bstep (se 3 (by rfl) ⟨2771444, by rfl⟩ : syracuseStep 14781037 = 5542889) B5542889
theorem B19708049 : Blo 1995435 19708049 := bstep (se 2 (by rfl) ⟨7390518, by rfl⟩ : syracuseStep 19708049 = 14781037) B14781037
theorem B13138699 : Blo 1995435 13138699 := bstep (se 1 (by rfl) ⟨9854024, by rfl⟩ : syracuseStep 13138699 = 19708049) B19708049
theorem B17518265 : Blo 1995435 17518265 := bstep (se 2 (by rfl) ⟨6569349, by rfl⟩ : syracuseStep 17518265 = 13138699) B13138699
theorem B11678843 : Blo 1995435 11678843 := bstep (se 1 (by rfl) ⟨8759132, by rfl⟩ : syracuseStep 11678843 = 17518265) B17518265
theorem B7785895 : Blo 1995435 7785895 := bstep (se 1 (by rfl) ⟨5839421, by rfl⟩ : syracuseStep 7785895 = 11678843) B11678843
theorem B10381193 : Blo 1995435 10381193 := bstep (se 2 (by rfl) ⟨3892947, by rfl⟩ : syracuseStep 10381193 = 7785895) B7785895
theorem B6920795 : Blo 1995435 6920795 := bstep (se 1 (by rfl) ⟨5190596, by rfl⟩ : syracuseStep 6920795 = 10381193) B10381193
theorem B4613863 : Blo 1995435 4613863 := bstep (se 1 (by rfl) ⟨3460397, by rfl⟩ : syracuseStep 4613863 = 6920795) B6920795
theorem B6151817 : Blo 1995435 6151817 := bstep (se 2 (by rfl) ⟨2306931, by rfl⟩ : syracuseStep 6151817 = 4613863) B4613863
theorem B4101211 : Blo 1995435 4101211 := bstep (se 1 (by rfl) ⟨3075908, by rfl⟩ : syracuseStep 4101211 = 6151817) B6151817
theorem B21873125 : Blo 1995435 21873125 := bstep (se 4 (by rfl) ⟨2050605, by rfl⟩ : syracuseStep 21873125 = 4101211) B4101211
theorem B58328333 : Blo 1995435 58328333 := bstep (se 3 (by rfl) ⟨10936562, by rfl⟩ : syracuseStep 58328333 = 21873125) B21873125
theorem B38885555 : Blo 1995435 38885555 := bstep (se 1 (by rfl) ⟨29164166, by rfl⟩ : syracuseStep 38885555 = 58328333) B58328333
theorem B103694813 : Blo 1995435 103694813 := bstep (se 3 (by rfl) ⟨19442777, by rfl⟩ : syracuseStep 103694813 = 38885555) B38885555
theorem B69129875 : Blo 1995435 69129875 := bstep (se 1 (by rfl) ⟨51847406, by rfl⟩ : syracuseStep 69129875 = 103694813) B103694813
theorem B46086583 : Blo 1995435 46086583 := bstep (se 1 (by rfl) ⟨34564937, by rfl⟩ : syracuseStep 46086583 = 69129875) B69129875
theorem B61448777 : Blo 1995435 61448777 := bstep (se 2 (by rfl) ⟨23043291, by rfl⟩ : syracuseStep 61448777 = 46086583) B46086583
theorem B40965851 : Blo 1995435 40965851 := bstep (se 1 (by rfl) ⟨30724388, by rfl⟩ : syracuseStep 40965851 = 61448777) B61448777
theorem B109242269 : Blo 1995435 109242269 := bstep (se 3 (by rfl) ⟨20482925, by rfl⟩ : syracuseStep 109242269 = 40965851) B40965851
theorem B72828179 : Blo 1995435 72828179 := bstep (se 1 (by rfl) ⟨54621134, by rfl⟩ : syracuseStep 72828179 = 109242269) B109242269
theorem B48552119 : Blo 1995435 48552119 := bstep (se 1 (by rfl) ⟨36414089, by rfl⟩ : syracuseStep 48552119 = 72828179) B72828179
theorem B32368079 : Blo 1995435 32368079 := bstep (se 1 (by rfl) ⟨24276059, by rfl⟩ : syracuseStep 32368079 = 48552119) B48552119
theorem B21578719 : Blo 1995435 21578719 := bstep (se 1 (by rfl) ⟨16184039, by rfl⟩ : syracuseStep 21578719 = 32368079) B32368079
theorem B28771625 : Blo 1995435 28771625 := bstep (se 2 (by rfl) ⟨10789359, by rfl⟩ : syracuseStep 28771625 = 21578719) B21578719
theorem B76724333 : Blo 1995435 76724333 := bstep (se 3 (by rfl) ⟨14385812, by rfl⟩ : syracuseStep 76724333 = 28771625) B28771625
theorem B51149555 : Blo 1995435 51149555 := bstep (se 1 (by rfl) ⟨38362166, by rfl⟩ : syracuseStep 51149555 = 76724333) B76724333
theorem B34099703 : Blo 1995435 34099703 := bstep (se 1 (by rfl) ⟨25574777, by rfl⟩ : syracuseStep 34099703 = 51149555) B51149555
theorem B22733135 : Blo 1995435 22733135 := bstep (se 1 (by rfl) ⟨17049851, by rfl⟩ : syracuseStep 22733135 = 34099703) B34099703
theorem B15155423 : Blo 1995435 15155423 := bstep (se 1 (by rfl) ⟨11366567, by rfl⟩ : syracuseStep 15155423 = 22733135) B22733135
theorem B10103615 : Blo 1995435 10103615 := bstep (se 1 (by rfl) ⟨7577711, by rfl⟩ : syracuseStep 10103615 = 15155423) B15155423
theorem B6735743 : Blo 1995435 6735743 := bstep (se 1 (by rfl) ⟨5051807, by rfl⟩ : syracuseStep 6735743 = 10103615) B10103615
theorem B4490495 : Blo 1995435 4490495 := bstep (se 1 (by rfl) ⟨3367871, by rfl⟩ : syracuseStep 4490495 = 6735743) B6735743
theorem B2993663 : Blo 1995435 2993663 := bstep (se 1 (by rfl) ⟨2245247, by rfl⟩ : syracuseStep 2993663 = 4490495) B4490495
theorem B1995775 : Blo 1995435 1995775 := bstep (se 1 (by rfl) ⟨1496831, by rfl⟩ : syracuseStep 1995775 = 2993663) B2993663
theorem B2993669 : Blo 1995435 2993669 := bbase (se 4 (by rfl) ⟨280656, by rfl⟩ : syracuseStep 2993669 = 561313) (by norm_num)
theorem B1995779 : Blo 1995435 1995779 := bstep (se 1 (by rfl) ⟨1496834, by rfl⟩ : syracuseStep 1995779 = 2993669) B2993669
theorem B3367885 : Blo 1995435 3367885 := bbase (se 3 (by rfl) ⟨631478, by rfl⟩ : syracuseStep 3367885 = 1262957) (by norm_num)
theorem B4490513 : Blo 1995435 4490513 := bstep (se 2 (by rfl) ⟨1683942, by rfl⟩ : syracuseStep 4490513 = 3367885) B3367885
theorem B2993675 : Blo 1995435 2993675 := bstep (se 1 (by rfl) ⟨2245256, by rfl⟩ : syracuseStep 2993675 = 4490513) B4490513
theorem B1995783 : Blo 1995435 1995783 := bstep (se 1 (by rfl) ⟨1496837, by rfl⟩ : syracuseStep 1995783 = 2993675) B2993675
theorem B2245261 : Blo 1995435 2245261 := bbase (se 3 (by rfl) ⟨420986, by rfl⟩ : syracuseStep 2245261 = 841973) (by norm_num)
theorem B2993681 : Blo 1995435 2993681 := bstep (se 2 (by rfl) ⟨1122630, by rfl⟩ : syracuseStep 2993681 = 2245261) B2245261
theorem B1995787 : Blo 1995435 1995787 := bstep (se 1 (by rfl) ⟨1496840, by rfl⟩ : syracuseStep 1995787 = 2993681) B2993681
theorem B6735797 : Blo 1995435 6735797 := bbase (se 5 (by rfl) ⟨315740, by rfl⟩ : syracuseStep 6735797 = 631481) (by norm_num)
theorem B4490531 : Blo 1995435 4490531 := bstep (se 1 (by rfl) ⟨3367898, by rfl⟩ : syracuseStep 4490531 = 6735797) B6735797
theorem B2993687 : Blo 1995435 2993687 := bstep (se 1 (by rfl) ⟨2245265, by rfl⟩ : syracuseStep 2993687 = 4490531) B4490531
theorem B1995791 : Blo 1995435 1995791 := bstep (se 1 (by rfl) ⟨1496843, by rfl⟩ : syracuseStep 1995791 = 2993687) B2993687
theorem B2993693 : Blo 1995435 2993693 := bbase (se 3 (by rfl) ⟨561317, by rfl⟩ : syracuseStep 2993693 = 1122635) (by norm_num)
theorem B1995795 : Blo 1995435 1995795 := bstep (se 1 (by rfl) ⟨1496846, by rfl⟩ : syracuseStep 1995795 = 2993693) B2993693
theorem B4490549 : Blo 1995435 4490549 := bbase (se 5 (by rfl) ⟨210494, by rfl⟩ : syracuseStep 4490549 = 420989) (by norm_num)
theorem B2993699 : Blo 1995435 2993699 := bstep (se 1 (by rfl) ⟨2245274, by rfl⟩ : syracuseStep 2993699 = 4490549) B4490549
theorem B1995799 : Blo 1995435 1995799 := bstep (se 1 (by rfl) ⟨1496849, by rfl⟩ : syracuseStep 1995799 = 2993699) B2993699
theorem B5394757 : Blo 1995435 5394757 := bbase (se 4 (by rfl) ⟨505758, by rfl⟩ : syracuseStep 5394757 = 1011517) (by norm_num)
theorem B7193009 : Blo 1995435 7193009 := bstep (se 2 (by rfl) ⟨2697378, by rfl⟩ : syracuseStep 7193009 = 5394757) B5394757
theorem B19181357 : Blo 1995435 19181357 := bstep (se 3 (by rfl) ⟨3596504, by rfl⟩ : syracuseStep 19181357 = 7193009) B7193009
theorem B12787571 : Blo 1995435 12787571 := bstep (se 1 (by rfl) ⟨9590678, by rfl⟩ : syracuseStep 12787571 = 19181357) B19181357
theorem B8525047 : Blo 1995435 8525047 := bstep (se 1 (by rfl) ⟨6393785, by rfl⟩ : syracuseStep 8525047 = 12787571) B12787571
theorem B11366729 : Blo 1995435 11366729 := bstep (se 2 (by rfl) ⟨4262523, by rfl⟩ : syracuseStep 11366729 = 8525047) B8525047
theorem B7577819 : Blo 1995435 7577819 := bstep (se 1 (by rfl) ⟨5683364, by rfl⟩ : syracuseStep 7577819 = 11366729) B11366729
theorem B5051879 : Blo 1995435 5051879 := bstep (se 1 (by rfl) ⟨3788909, by rfl⟩ : syracuseStep 5051879 = 7577819) B7577819
theorem B3367919 : Blo 1995435 3367919 := bstep (se 1 (by rfl) ⟨2525939, by rfl⟩ : syracuseStep 3367919 = 5051879) B5051879
theorem B2245279 : Blo 1995435 2245279 := bstep (se 1 (by rfl) ⟨1683959, by rfl⟩ : syracuseStep 2245279 = 3367919) B3367919
theorem B2993705 : Blo 1995435 2993705 := bstep (se 2 (by rfl) ⟨1122639, by rfl⟩ : syracuseStep 2993705 = 2245279) B2245279
theorem B1995803 : Blo 1995435 1995803 := bstep (se 1 (by rfl) ⟨1496852, by rfl⟩ : syracuseStep 1995803 = 2993705) B2993705
theorem B3645581 : Blo 1995435 3645581 := bbase (se 3 (by rfl) ⟨683546, by rfl⟩ : syracuseStep 3645581 = 1367093) (by norm_num)
theorem B9721549 : Blo 1995435 9721549 := bstep (se 3 (by rfl) ⟨1822790, by rfl⟩ : syracuseStep 9721549 = 3645581) B3645581
theorem B12962065 : Blo 1995435 12962065 := bstep (se 2 (by rfl) ⟨4860774, by rfl⟩ : syracuseStep 12962065 = 9721549) B9721549
theorem B17282753 : Blo 1995435 17282753 := bstep (se 2 (by rfl) ⟨6481032, by rfl⟩ : syracuseStep 17282753 = 12962065) B12962065
theorem B11521835 : Blo 1995435 11521835 := bstep (se 1 (by rfl) ⟨8641376, by rfl⟩ : syracuseStep 11521835 = 17282753) B17282753
theorem B7681223 : Blo 1995435 7681223 := bstep (se 1 (by rfl) ⟨5760917, by rfl⟩ : syracuseStep 7681223 = 11521835) B11521835
theorem B5120815 : Blo 1995435 5120815 := bstep (se 1 (by rfl) ⟨3840611, by rfl⟩ : syracuseStep 5120815 = 7681223) B7681223
theorem B6827753 : Blo 1995435 6827753 := bstep (se 2 (by rfl) ⟨2560407, by rfl⟩ : syracuseStep 6827753 = 5120815) B5120815
theorem B18207341 : Blo 1995435 18207341 := bstep (se 3 (by rfl) ⟨3413876, by rfl⟩ : syracuseStep 18207341 = 6827753) B6827753
theorem B12138227 : Blo 1995435 12138227 := bstep (se 1 (by rfl) ⟨9103670, by rfl⟩ : syracuseStep 12138227 = 18207341) B18207341
theorem B8092151 : Blo 1995435 8092151 := bstep (se 1 (by rfl) ⟨6069113, by rfl⟩ : syracuseStep 8092151 = 12138227) B12138227
theorem B5394767 : Blo 1995435 5394767 := bstep (se 1 (by rfl) ⟨4046075, by rfl⟩ : syracuseStep 5394767 = 8092151) B8092151
theorem B14386045 : Blo 1995435 14386045 := bstep (se 3 (by rfl) ⟨2697383, by rfl⟩ : syracuseStep 14386045 = 5394767) B5394767
theorem B19181393 : Blo 1995435 19181393 := bstep (se 2 (by rfl) ⟨7193022, by rfl⟩ : syracuseStep 19181393 = 14386045) B14386045
theorem B12787595 : Blo 1995435 12787595 := bstep (se 1 (by rfl) ⟨9590696, by rfl⟩ : syracuseStep 12787595 = 19181393) B19181393
theorem B8525063 : Blo 1995435 8525063 := bstep (se 1 (by rfl) ⟨6393797, by rfl⟩ : syracuseStep 8525063 = 12787595) B12787595
theorem B5683375 : Blo 1995435 5683375 := bstep (se 1 (by rfl) ⟨4262531, by rfl⟩ : syracuseStep 5683375 = 8525063) B8525063
theorem B7577833 : Blo 1995435 7577833 := bstep (se 2 (by rfl) ⟨2841687, by rfl⟩ : syracuseStep 7577833 = 5683375) B5683375
theorem B10103777 : Blo 1995435 10103777 := bstep (se 2 (by rfl) ⟨3788916, by rfl⟩ : syracuseStep 10103777 = 7577833) B7577833
theorem B6735851 : Blo 1995435 6735851 := bstep (se 1 (by rfl) ⟨5051888, by rfl⟩ : syracuseStep 6735851 = 10103777) B10103777
theorem B4490567 : Blo 1995435 4490567 := bstep (se 1 (by rfl) ⟨3367925, by rfl⟩ : syracuseStep 4490567 = 6735851) B6735851
theorem B2993711 : Blo 1995435 2993711 := bstep (se 1 (by rfl) ⟨2245283, by rfl⟩ : syracuseStep 2993711 = 4490567) B4490567
theorem B1995807 : Blo 1995435 1995807 := bstep (se 1 (by rfl) ⟨1496855, by rfl⟩ : syracuseStep 1995807 = 2993711) B2993711
theorem B2993717 : Blo 1995435 2993717 := bbase (se 5 (by rfl) ⟨140330, by rfl⟩ : syracuseStep 2993717 = 280661) (by norm_num)
theorem B1995811 : Blo 1995435 1995811 := bstep (se 1 (by rfl) ⟨1496858, by rfl⟩ : syracuseStep 1995811 = 2993717) B2993717
theorem B5051909 : Blo 1995435 5051909 := bbase (se 4 (by rfl) ⟨473616, by rfl⟩ : syracuseStep 5051909 = 947233) (by norm_num)
theorem B3367939 : Blo 1995435 3367939 := bstep (se 1 (by rfl) ⟨2525954, by rfl⟩ : syracuseStep 3367939 = 5051909) B5051909
theorem B4490585 : Blo 1995435 4490585 := bstep (se 2 (by rfl) ⟨1683969, by rfl⟩ : syracuseStep 4490585 = 3367939) B3367939
theorem B2993723 : Blo 1995435 2993723 := bstep (se 1 (by rfl) ⟨2245292, by rfl⟩ : syracuseStep 2993723 = 4490585) B4490585
theorem B1995815 : Blo 1995435 1995815 := bstep (se 1 (by rfl) ⟨1496861, by rfl⟩ : syracuseStep 1995815 = 2993723) B2993723
theorem B2245297 : Blo 1995435 2245297 := bbase (se 2 (by rfl) ⟨841986, by rfl⟩ : syracuseStep 2245297 = 1683973) (by norm_num)
theorem B2993729 : Blo 1995435 2993729 := bstep (se 2 (by rfl) ⟨1122648, by rfl⟩ : syracuseStep 2993729 = 2245297) B2245297
theorem B1995819 : Blo 1995435 1995819 := bstep (se 1 (by rfl) ⟨1496864, by rfl⟩ : syracuseStep 1995819 = 2993729) B2993729
theorem B3196925 : Blo 1995435 3196925 := bbase (se 3 (by rfl) ⟨599423, by rfl⟩ : syracuseStep 3196925 = 1198847) (by norm_num)
theorem B2131283 : Blo 1995435 2131283 := bstep (se 1 (by rfl) ⟨1598462, by rfl⟩ : syracuseStep 2131283 = 3196925) B3196925
theorem B5683421 : Blo 1995435 5683421 := bstep (se 3 (by rfl) ⟨1065641, by rfl⟩ : syracuseStep 5683421 = 2131283) B2131283
theorem B3788947 : Blo 1995435 3788947 := bstep (se 1 (by rfl) ⟨2841710, by rfl⟩ : syracuseStep 3788947 = 5683421) B5683421
theorem B5051929 : Blo 1995435 5051929 := bstep (se 2 (by rfl) ⟨1894473, by rfl⟩ : syracuseStep 5051929 = 3788947) B3788947
theorem B6735905 : Blo 1995435 6735905 := bstep (se 2 (by rfl) ⟨2525964, by rfl⟩ : syracuseStep 6735905 = 5051929) B5051929
theorem B4490603 : Blo 1995435 4490603 := bstep (se 1 (by rfl) ⟨3367952, by rfl⟩ : syracuseStep 4490603 = 6735905) B6735905
theorem B2993735 : Blo 1995435 2993735 := bstep (se 1 (by rfl) ⟨2245301, by rfl⟩ : syracuseStep 2993735 = 4490603) B4490603
theorem B1995823 : Blo 1995435 1995823 := bstep (se 1 (by rfl) ⟨1496867, by rfl⟩ : syracuseStep 1995823 = 2993735) B2993735
theorem B2993741 : Blo 1995435 2993741 := bbase (se 3 (by rfl) ⟨561326, by rfl⟩ : syracuseStep 2993741 = 1122653) (by norm_num)
theorem B1995827 : Blo 1995435 1995827 := bstep (se 1 (by rfl) ⟨1496870, by rfl⟩ : syracuseStep 1995827 = 2993741) B2993741
theorem B4490621 : Blo 1995435 4490621 := bbase (se 3 (by rfl) ⟨841991, by rfl⟩ : syracuseStep 4490621 = 1683983) (by norm_num)
theorem B2993747 : Blo 1995435 2993747 := bstep (se 1 (by rfl) ⟨2245310, by rfl⟩ : syracuseStep 2993747 = 4490621) B4490621
theorem B1995831 : Blo 1995435 1995831 := bstep (se 1 (by rfl) ⟨1496873, by rfl⟩ : syracuseStep 1995831 = 2993747) B2993747
theorem B3367973 : Blo 1995435 3367973 := bbase (se 4 (by rfl) ⟨315747, by rfl⟩ : syracuseStep 3367973 = 631495) (by norm_num)
theorem B2245315 : Blo 1995435 2245315 := bstep (se 1 (by rfl) ⟨1683986, by rfl⟩ : syracuseStep 2245315 = 3367973) B3367973
theorem B2993753 : Blo 1995435 2993753 := bstep (se 2 (by rfl) ⟨1122657, by rfl⟩ : syracuseStep 2993753 = 2245315) B2245315
theorem B1995835 : Blo 1995435 1995835 := bstep (se 1 (by rfl) ⟨1496876, by rfl⟩ : syracuseStep 1995835 = 2993753) B2993753
theorem B2841733 : Blo 1995435 2841733 := bbase (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) (by norm_num)
theorem B15155909 : Blo 1995435 15155909 := bstep (se 4 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 15155909 = 2841733) B2841733
theorem B10103939 : Blo 1995435 10103939 := bstep (se 1 (by rfl) ⟨7577954, by rfl⟩ : syracuseStep 10103939 = 15155909) B15155909
theorem B6735959 : Blo 1995435 6735959 := bstep (se 1 (by rfl) ⟨5051969, by rfl⟩ : syracuseStep 6735959 = 10103939) B10103939
theorem B4490639 : Blo 1995435 4490639 := bstep (se 1 (by rfl) ⟨3367979, by rfl⟩ : syracuseStep 4490639 = 6735959) B6735959
theorem B2993759 : Blo 1995435 2993759 := bstep (se 1 (by rfl) ⟨2245319, by rfl⟩ : syracuseStep 2993759 = 4490639) B4490639
theorem B1995839 : Blo 1995435 1995839 := bstep (se 1 (by rfl) ⟨1496879, by rfl⟩ : syracuseStep 1995839 = 2993759) B2993759
theorem B2993765 : Blo 1995435 2993765 := bbase (se 4 (by rfl) ⟨280665, by rfl⟩ : syracuseStep 2993765 = 561331) (by norm_num)
theorem B1995843 : Blo 1995435 1995843 := bstep (se 1 (by rfl) ⟨1496882, by rfl⟩ : syracuseStep 1995843 = 2993765) B2993765
theorem B2131309 : Blo 1995435 2131309 := bbase (se 3 (by rfl) ⟨399620, by rfl⟩ : syracuseStep 2131309 = 799241) (by norm_num)
theorem B2841745 : Blo 1995435 2841745 := bstep (se 2 (by rfl) ⟨1065654, by rfl⟩ : syracuseStep 2841745 = 2131309) B2131309
theorem B3788993 : Blo 1995435 3788993 := bstep (se 2 (by rfl) ⟨1420872, by rfl⟩ : syracuseStep 3788993 = 2841745) B2841745
theorem B2525995 : Blo 1995435 2525995 := bstep (se 1 (by rfl) ⟨1894496, by rfl⟩ : syracuseStep 2525995 = 3788993) B3788993
theorem B3367993 : Blo 1995435 3367993 := bstep (se 2 (by rfl) ⟨1262997, by rfl⟩ : syracuseStep 3367993 = 2525995) B2525995
theorem B4490657 : Blo 1995435 4490657 := bstep (se 2 (by rfl) ⟨1683996, by rfl⟩ : syracuseStep 4490657 = 3367993) B3367993
theorem B2993771 : Blo 1995435 2993771 := bstep (se 1 (by rfl) ⟨2245328, by rfl⟩ : syracuseStep 2993771 = 4490657) B4490657
theorem B1995847 : Blo 1995435 1995847 := bstep (se 1 (by rfl) ⟨1496885, by rfl⟩ : syracuseStep 1995847 = 2993771) B2993771
theorem B2245333 : Blo 1995435 2245333 := bbase (se 7 (by rfl) ⟨26312, by rfl⟩ : syracuseStep 2245333 = 52625) (by norm_num)
theorem B2993777 : Blo 1995435 2993777 := bstep (se 2 (by rfl) ⟨1122666, by rfl⟩ : syracuseStep 2993777 = 2245333) B2245333
theorem B1995851 : Blo 1995435 1995851 := bstep (se 1 (by rfl) ⟨1496888, by rfl⟩ : syracuseStep 1995851 = 2993777) B2993777
theorem B2526005 : Blo 1995435 2526005 := bbase (se 5 (by rfl) ⟨118406, by rfl⟩ : syracuseStep 2526005 = 236813) (by norm_num)
theorem B6736013 : Blo 1995435 6736013 := bstep (se 3 (by rfl) ⟨1263002, by rfl⟩ : syracuseStep 6736013 = 2526005) B2526005
theorem B4490675 : Blo 1995435 4490675 := bstep (se 1 (by rfl) ⟨3368006, by rfl⟩ : syracuseStep 4490675 = 6736013) B6736013
theorem B2993783 : Blo 1995435 2993783 := bstep (se 1 (by rfl) ⟨2245337, by rfl⟩ : syracuseStep 2993783 = 4490675) B4490675
theorem B1995855 : Blo 1995435 1995855 := bstep (se 1 (by rfl) ⟨1496891, by rfl⟩ : syracuseStep 1995855 = 2993783) B2993783
theorem B2993789 : Blo 1995435 2993789 := bbase (se 3 (by rfl) ⟨561335, by rfl⟩ : syracuseStep 2993789 = 1122671) (by norm_num)
theorem B1995859 : Blo 1995435 1995859 := bstep (se 1 (by rfl) ⟨1496894, by rfl⟩ : syracuseStep 1995859 = 2993789) B2993789
theorem B4490693 : Blo 1995435 4490693 := bbase (se 4 (by rfl) ⟨421002, by rfl⟩ : syracuseStep 4490693 = 842005) (by norm_num)
theorem B2993795 : Blo 1995435 2993795 := bstep (se 1 (by rfl) ⟨2245346, by rfl⟩ : syracuseStep 2993795 = 4490693) B4490693
theorem B1995863 : Blo 1995435 1995863 := bstep (se 1 (by rfl) ⟨1496897, by rfl⟩ : syracuseStep 1995863 = 2993795) B2993795
theorem B3413981 : Blo 1995435 3413981 := bbase (se 3 (by rfl) ⟨640121, by rfl⟩ : syracuseStep 3413981 = 1280243) (by norm_num)
theorem B2275987 : Blo 1995435 2275987 := bstep (se 1 (by rfl) ⟨1706990, by rfl⟩ : syracuseStep 2275987 = 3413981) B3413981
theorem B3034649 : Blo 1995435 3034649 := bstep (se 2 (by rfl) ⟨1137993, by rfl⟩ : syracuseStep 3034649 = 2275987) B2275987
theorem B2023099 : Blo 1995435 2023099 := bstep (se 1 (by rfl) ⟨1517324, by rfl⟩ : syracuseStep 2023099 = 3034649) B3034649
theorem B10789861 : Blo 1995435 10789861 := bstep (se 4 (by rfl) ⟨1011549, by rfl⟩ : syracuseStep 10789861 = 2023099) B2023099
theorem B14386481 : Blo 1995435 14386481 := bstep (se 2 (by rfl) ⟨5394930, by rfl⟩ : syracuseStep 14386481 = 10789861) B10789861
theorem B9590987 : Blo 1995435 9590987 := bstep (se 1 (by rfl) ⟨7193240, by rfl⟩ : syracuseStep 9590987 = 14386481) B14386481
theorem B6393991 : Blo 1995435 6393991 := bstep (se 1 (by rfl) ⟨4795493, by rfl⟩ : syracuseStep 6393991 = 9590987) B9590987
theorem B8525321 : Blo 1995435 8525321 := bstep (se 2 (by rfl) ⟨3196995, by rfl⟩ : syracuseStep 8525321 = 6393991) B6393991
theorem B5683547 : Blo 1995435 5683547 := bstep (se 1 (by rfl) ⟨4262660, by rfl⟩ : syracuseStep 5683547 = 8525321) B8525321
theorem B3789031 : Blo 1995435 3789031 := bstep (se 1 (by rfl) ⟨2841773, by rfl⟩ : syracuseStep 3789031 = 5683547) B5683547
theorem B5052041 : Blo 1995435 5052041 := bstep (se 2 (by rfl) ⟨1894515, by rfl⟩ : syracuseStep 5052041 = 3789031) B3789031
theorem B3368027 : Blo 1995435 3368027 := bstep (se 1 (by rfl) ⟨2526020, by rfl⟩ : syracuseStep 3368027 = 5052041) B5052041
theorem B2245351 : Blo 1995435 2245351 := bstep (se 1 (by rfl) ⟨1684013, by rfl⟩ : syracuseStep 2245351 = 3368027) B3368027
theorem B2993801 : Blo 1995435 2993801 := bstep (se 2 (by rfl) ⟨1122675, by rfl⟩ : syracuseStep 2993801 = 2245351) B2245351
theorem B1995867 : Blo 1995435 1995867 := bstep (se 1 (by rfl) ⟨1496900, by rfl⟩ : syracuseStep 1995867 = 2993801) B2993801
theorem B10104101 : Blo 1995435 10104101 := bbase (se 4 (by rfl) ⟨947259, by rfl⟩ : syracuseStep 10104101 = 1894519) (by norm_num)
theorem B6736067 : Blo 1995435 6736067 := bstep (se 1 (by rfl) ⟨5052050, by rfl⟩ : syracuseStep 6736067 = 10104101) B10104101
theorem B4490711 : Blo 1995435 4490711 := bstep (se 1 (by rfl) ⟨3368033, by rfl⟩ : syracuseStep 4490711 = 6736067) B6736067
theorem B2993807 : Blo 1995435 2993807 := bstep (se 1 (by rfl) ⟨2245355, by rfl⟩ : syracuseStep 2993807 = 4490711) B4490711
theorem B1995871 : Blo 1995435 1995871 := bstep (se 1 (by rfl) ⟨1496903, by rfl⟩ : syracuseStep 1995871 = 2993807) B2993807
theorem B2993813 : Blo 1995435 2993813 := bbase (se 6 (by rfl) ⟨70167, by rfl⟩ : syracuseStep 2993813 = 140335) (by norm_num)
theorem B1995875 : Blo 1995435 1995875 := bstep (se 1 (by rfl) ⟨1496906, by rfl⟩ : syracuseStep 1995875 = 2993813) B2993813
theorem B2560501 : Blo 1995435 2560501 := bbase (se 5 (by rfl) ⟨120023, by rfl⟩ : syracuseStep 2560501 = 240047) (by norm_num)
theorem B3414001 : Blo 1995435 3414001 := bstep (se 2 (by rfl) ⟨1280250, by rfl⟩ : syracuseStep 3414001 = 2560501) B2560501
theorem B4552001 : Blo 1995435 4552001 := bstep (se 2 (by rfl) ⟨1707000, by rfl⟩ : syracuseStep 4552001 = 3414001) B3414001
theorem B3034667 : Blo 1995435 3034667 := bstep (se 1 (by rfl) ⟨2276000, by rfl⟩ : syracuseStep 3034667 = 4552001) B4552001
theorem B2023111 : Blo 1995435 2023111 := bstep (se 1 (by rfl) ⟨1517333, by rfl⟩ : syracuseStep 2023111 = 3034667) B3034667
theorem B2697481 : Blo 1995435 2697481 := bstep (se 2 (by rfl) ⟨1011555, by rfl⟩ : syracuseStep 2697481 = 2023111) B2023111
theorem B14386565 : Blo 1995435 14386565 := bstep (se 4 (by rfl) ⟨1348740, by rfl⟩ : syracuseStep 14386565 = 2697481) B2697481
theorem B9591043 : Blo 1995435 9591043 := bstep (se 1 (by rfl) ⟨7193282, by rfl⟩ : syracuseStep 9591043 = 14386565) B14386565
theorem B12788057 : Blo 1995435 12788057 := bstep (se 2 (by rfl) ⟨4795521, by rfl⟩ : syracuseStep 12788057 = 9591043) B9591043
theorem B8525371 : Blo 1995435 8525371 := bstep (se 1 (by rfl) ⟨6394028, by rfl⟩ : syracuseStep 8525371 = 12788057) B12788057
theorem B11367161 : Blo 1995435 11367161 := bstep (se 2 (by rfl) ⟨4262685, by rfl⟩ : syracuseStep 11367161 = 8525371) B8525371
theorem B7578107 : Blo 1995435 7578107 := bstep (se 1 (by rfl) ⟨5683580, by rfl⟩ : syracuseStep 7578107 = 11367161) B11367161
theorem B5052071 : Blo 1995435 5052071 := bstep (se 1 (by rfl) ⟨3789053, by rfl⟩ : syracuseStep 5052071 = 7578107) B7578107
theorem B3368047 : Blo 1995435 3368047 := bstep (se 1 (by rfl) ⟨2526035, by rfl⟩ : syracuseStep 3368047 = 5052071) B5052071
theorem B4490729 : Blo 1995435 4490729 := bstep (se 2 (by rfl) ⟨1684023, by rfl⟩ : syracuseStep 4490729 = 3368047) B3368047
theorem B2993819 : Blo 1995435 2993819 := bstep (se 1 (by rfl) ⟨2245364, by rfl⟩ : syracuseStep 2993819 = 4490729) B4490729
theorem B1995879 : Blo 1995435 1995879 := bstep (se 1 (by rfl) ⟨1496909, by rfl⟩ : syracuseStep 1995879 = 2993819) B2993819
theorem B2245369 : Blo 1995435 2245369 := bbase (se 2 (by rfl) ⟨842013, by rfl⟩ : syracuseStep 2245369 = 1684027) (by norm_num)
theorem B2993825 : Blo 1995435 2993825 := bstep (se 2 (by rfl) ⟨1122684, by rfl⟩ : syracuseStep 2993825 = 2245369) B2245369
theorem B1995883 : Blo 1995435 1995883 := bstep (se 1 (by rfl) ⟨1496912, by rfl⟩ : syracuseStep 1995883 = 2993825) B2993825
theorem B4795541 : Blo 1995435 4795541 := bbase (se 6 (by rfl) ⟨112395, by rfl⟩ : syracuseStep 4795541 = 224791) (by norm_num)
theorem B3197027 : Blo 1995435 3197027 := bstep (se 1 (by rfl) ⟨2397770, by rfl⟩ : syracuseStep 3197027 = 4795541) B4795541
theorem B8525405 : Blo 1995435 8525405 := bstep (se 3 (by rfl) ⟨1598513, by rfl⟩ : syracuseStep 8525405 = 3197027) B3197027
theorem B5683603 : Blo 1995435 5683603 := bstep (se 1 (by rfl) ⟨4262702, by rfl⟩ : syracuseStep 5683603 = 8525405) B8525405
theorem B7578137 : Blo 1995435 7578137 := bstep (se 2 (by rfl) ⟨2841801, by rfl⟩ : syracuseStep 7578137 = 5683603) B5683603
theorem B5052091 : Blo 1995435 5052091 := bstep (se 1 (by rfl) ⟨3789068, by rfl⟩ : syracuseStep 5052091 = 7578137) B7578137
theorem B6736121 : Blo 1995435 6736121 := bstep (se 2 (by rfl) ⟨2526045, by rfl⟩ : syracuseStep 6736121 = 5052091) B5052091
theorem B4490747 : Blo 1995435 4490747 := bstep (se 1 (by rfl) ⟨3368060, by rfl⟩ : syracuseStep 4490747 = 6736121) B6736121
theorem B2993831 : Blo 1995435 2993831 := bstep (se 1 (by rfl) ⟨2245373, by rfl⟩ : syracuseStep 2993831 = 4490747) B4490747
theorem B1995887 : Blo 1995435 1995887 := bstep (se 1 (by rfl) ⟨1496915, by rfl⟩ : syracuseStep 1995887 = 2993831) B2993831
theorem B2993837 : Blo 1995435 2993837 := bbase (se 3 (by rfl) ⟨561344, by rfl⟩ : syracuseStep 2993837 = 1122689) (by norm_num)
theorem B1995891 : Blo 1995435 1995891 := bstep (se 1 (by rfl) ⟨1496918, by rfl⟩ : syracuseStep 1995891 = 2993837) B2993837
theorem B4490765 : Blo 1995435 4490765 := bbase (se 3 (by rfl) ⟨842018, by rfl⟩ : syracuseStep 4490765 = 1684037) (by norm_num)
theorem B2993843 : Blo 1995435 2993843 := bstep (se 1 (by rfl) ⟨2245382, by rfl⟩ : syracuseStep 2993843 = 4490765) B4490765
theorem B1995895 : Blo 1995435 1995895 := bstep (se 1 (by rfl) ⟨1496921, by rfl⟩ : syracuseStep 1995895 = 2993843) B2993843
theorem B2526061 : Blo 1995435 2526061 := bbase (se 3 (by rfl) ⟨473636, by rfl⟩ : syracuseStep 2526061 = 947273) (by norm_num)
theorem B3368081 : Blo 1995435 3368081 := bstep (se 2 (by rfl) ⟨1263030, by rfl⟩ : syracuseStep 3368081 = 2526061) B2526061
theorem B2245387 : Blo 1995435 2245387 := bstep (se 1 (by rfl) ⟨1684040, by rfl⟩ : syracuseStep 2245387 = 3368081) B3368081
theorem B2993849 : Blo 1995435 2993849 := bstep (se 2 (by rfl) ⟨1122693, by rfl⟩ : syracuseStep 2993849 = 2245387) B2245387
theorem B1995899 : Blo 1995435 1995899 := bstep (se 1 (by rfl) ⟨1496924, by rfl⟩ : syracuseStep 1995899 = 2993849) B2993849
theorem B9591157 : Blo 1995435 9591157 := bbase (se 5 (by rfl) ⟨449585, by rfl⟩ : syracuseStep 9591157 = 899171) (by norm_num)
theorem B12788209 : Blo 1995435 12788209 := bstep (se 2 (by rfl) ⟨4795578, by rfl⟩ : syracuseStep 12788209 = 9591157) B9591157
theorem B17050945 : Blo 1995435 17050945 := bstep (se 2 (by rfl) ⟨6394104, by rfl⟩ : syracuseStep 17050945 = 12788209) B12788209
theorem B22734593 : Blo 1995435 22734593 := bstep (se 2 (by rfl) ⟨8525472, by rfl⟩ : syracuseStep 22734593 = 17050945) B17050945
theorem B15156395 : Blo 1995435 15156395 := bstep (se 1 (by rfl) ⟨11367296, by rfl⟩ : syracuseStep 15156395 = 22734593) B22734593
theorem B10104263 : Blo 1995435 10104263 := bstep (se 1 (by rfl) ⟨7578197, by rfl⟩ : syracuseStep 10104263 = 15156395) B15156395
theorem B6736175 : Blo 1995435 6736175 := bstep (se 1 (by rfl) ⟨5052131, by rfl⟩ : syracuseStep 6736175 = 10104263) B10104263
theorem B4490783 : Blo 1995435 4490783 := bstep (se 1 (by rfl) ⟨3368087, by rfl⟩ : syracuseStep 4490783 = 6736175) B6736175
theorem B2993855 : Blo 1995435 2993855 := bstep (se 1 (by rfl) ⟨2245391, by rfl⟩ : syracuseStep 2993855 = 4490783) B4490783
theorem B1995903 : Blo 1995435 1995903 := bstep (se 1 (by rfl) ⟨1496927, by rfl⟩ : syracuseStep 1995903 = 2993855) B2993855
theorem B2993861 : Blo 1995435 2993861 := bbase (se 4 (by rfl) ⟨280674, by rfl⟩ : syracuseStep 2993861 = 561349) (by norm_num)
theorem B1995907 : Blo 1995435 1995907 := bstep (se 1 (by rfl) ⟨1496930, by rfl⟩ : syracuseStep 1995907 = 2993861) B2993861
theorem B3368101 : Blo 1995435 3368101 := bbase (se 4 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 3368101 = 631519) (by norm_num)
theorem B4490801 : Blo 1995435 4490801 := bstep (se 2 (by rfl) ⟨1684050, by rfl⟩ : syracuseStep 4490801 = 3368101) B3368101
theorem B2993867 : Blo 1995435 2993867 := bstep (se 1 (by rfl) ⟨2245400, by rfl⟩ : syracuseStep 2993867 = 4490801) B4490801
theorem B1995911 : Blo 1995435 1995911 := bstep (se 1 (by rfl) ⟨1496933, by rfl⟩ : syracuseStep 1995911 = 2993867) B2993867
theorem B2245405 : Blo 1995435 2245405 := bbase (se 3 (by rfl) ⟨421013, by rfl⟩ : syracuseStep 2245405 = 842027) (by norm_num)
theorem B2993873 : Blo 1995435 2993873 := bstep (se 2 (by rfl) ⟨1122702, by rfl⟩ : syracuseStep 2993873 = 2245405) B2245405
theorem B1995915 : Blo 1995435 1995915 := bstep (se 1 (by rfl) ⟨1496936, by rfl⟩ : syracuseStep 1995915 = 2993873) B2993873
theorem B6736229 : Blo 1995435 6736229 := bbase (se 4 (by rfl) ⟨631521, by rfl⟩ : syracuseStep 6736229 = 1263043) (by norm_num)
theorem B4490819 : Blo 1995435 4490819 := bstep (se 1 (by rfl) ⟨3368114, by rfl⟩ : syracuseStep 4490819 = 6736229) B6736229
theorem B2993879 : Blo 1995435 2993879 := bstep (se 1 (by rfl) ⟨2245409, by rfl⟩ : syracuseStep 2993879 = 4490819) B4490819
theorem B1995919 : Blo 1995435 1995919 := bstep (se 1 (by rfl) ⟨1496939, by rfl⟩ : syracuseStep 1995919 = 2993879) B2993879
theorem B2993885 : Blo 1995435 2993885 := bbase (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) (by norm_num)
theorem B1995923 : Blo 1995435 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B4490837 : Blo 1995435 4490837 := bbase (se 8 (by rfl) ⟨26313, by rfl⟩ : syracuseStep 4490837 = 52627) (by norm_num)
theorem B2993891 : Blo 1995435 2993891 := bstep (se 1 (by rfl) ⟨2245418, by rfl⟩ : syracuseStep 2993891 = 4490837) B4490837
theorem B1995927 : Blo 1995435 1995927 := bstep (se 1 (by rfl) ⟨1496945, by rfl⟩ : syracuseStep 1995927 = 2993891) B2993891
theorem B4262797 : Blo 1995435 4262797 := bbase (se 3 (by rfl) ⟨799274, by rfl⟩ : syracuseStep 4262797 = 1598549) (by norm_num)
theorem B5683729 : Blo 1995435 5683729 := bstep (se 2 (by rfl) ⟨2131398, by rfl⟩ : syracuseStep 5683729 = 4262797) B4262797
theorem B7578305 : Blo 1995435 7578305 := bstep (se 2 (by rfl) ⟨2841864, by rfl⟩ : syracuseStep 7578305 = 5683729) B5683729
theorem B5052203 : Blo 1995435 5052203 := bstep (se 1 (by rfl) ⟨3789152, by rfl⟩ : syracuseStep 5052203 = 7578305) B7578305
theorem B3368135 : Blo 1995435 3368135 := bstep (se 1 (by rfl) ⟨2526101, by rfl⟩ : syracuseStep 3368135 = 5052203) B5052203
theorem B2245423 : Blo 1995435 2245423 := bstep (se 1 (by rfl) ⟨1684067, by rfl⟩ : syracuseStep 2245423 = 3368135) B3368135
theorem B2993897 : Blo 1995435 2993897 := bstep (se 2 (by rfl) ⟨1122711, by rfl⟩ : syracuseStep 2993897 = 2245423) B2245423
theorem B1995931 : Blo 1995435 1995931 := bstep (se 1 (by rfl) ⟨1496948, by rfl⟩ : syracuseStep 1995931 = 2993897) B2993897
theorem B7594165 : Blo 1995435 7594165 := bbase (se 5 (by rfl) ⟨355976, by rfl⟩ : syracuseStep 7594165 = 711953) (by norm_num)
theorem B10125553 : Blo 1995435 10125553 := bstep (se 2 (by rfl) ⟨3797082, by rfl⟩ : syracuseStep 10125553 = 7594165) B7594165
theorem B13500737 : Blo 1995435 13500737 := bstep (se 2 (by rfl) ⟨5062776, by rfl⟩ : syracuseStep 13500737 = 10125553) B10125553
theorem B9000491 : Blo 1995435 9000491 := bstep (se 1 (by rfl) ⟨6750368, by rfl⟩ : syracuseStep 9000491 = 13500737) B13500737
theorem B6144335189 : Blo 1995435 6144335189 := bstep (se 11 (by rfl) ⟨4500245, by rfl⟩ : syracuseStep 6144335189 = 9000491) B9000491
theorem B4096223459 : Blo 1995435 4096223459 := bstep (se 1 (by rfl) ⟨3072167594, by rfl⟩ : syracuseStep 4096223459 = 6144335189) B6144335189
theorem B2730815639 : Blo 1995435 2730815639 := bstep (se 1 (by rfl) ⟨2048111729, by rfl⟩ : syracuseStep 2730815639 = 4096223459) B4096223459
theorem B1820543759 : Blo 1995435 1820543759 := bstep (se 1 (by rfl) ⟨1365407819, by rfl⟩ : syracuseStep 1820543759 = 2730815639) B2730815639
theorem B1213695839 : Blo 1995435 1213695839 := bstep (se 1 (by rfl) ⟨910271879, by rfl⟩ : syracuseStep 1213695839 = 1820543759) B1820543759
theorem B809130559 : Blo 1995435 809130559 := bstep (se 1 (by rfl) ⟨606847919, by rfl⟩ : syracuseStep 809130559 = 1213695839) B1213695839
theorem B1078840745 : Blo 1995435 1078840745 := bstep (se 2 (by rfl) ⟨404565279, by rfl⟩ : syracuseStep 1078840745 = 809130559) B809130559
theorem B719227163 : Blo 1995435 719227163 := bstep (se 1 (by rfl) ⟨539420372, by rfl⟩ : syracuseStep 719227163 = 1078840745) B1078840745
theorem B479484775 : Blo 1995435 479484775 := bstep (se 1 (by rfl) ⟨359613581, by rfl⟩ : syracuseStep 479484775 = 719227163) B719227163
theorem B639313033 : Blo 1995435 639313033 := bstep (se 2 (by rfl) ⟨239742387, by rfl⟩ : syracuseStep 639313033 = 479484775) B479484775
theorem B852417377 : Blo 1995435 852417377 := bstep (se 2 (by rfl) ⟨319656516, by rfl⟩ : syracuseStep 852417377 = 639313033) B639313033
theorem B568278251 : Blo 1995435 568278251 := bstep (se 1 (by rfl) ⟨426208688, by rfl⟩ : syracuseStep 568278251 = 852417377) B852417377
theorem B378852167 : Blo 1995435 378852167 := bstep (se 1 (by rfl) ⟨284139125, by rfl⟩ : syracuseStep 378852167 = 568278251) B568278251
theorem B1010272445 : Blo 1995435 1010272445 := bstep (se 3 (by rfl) ⟨189426083, by rfl⟩ : syracuseStep 1010272445 = 378852167) B378852167
theorem B673514963 : Blo 1995435 673514963 := bstep (se 1 (by rfl) ⟨505136222, by rfl⟩ : syracuseStep 673514963 = 1010272445) B1010272445
theorem B449009975 : Blo 1995435 449009975 := bstep (se 1 (by rfl) ⟨336757481, by rfl⟩ : syracuseStep 449009975 = 673514963) B673514963
theorem B299339983 : Blo 1995435 299339983 := bstep (se 1 (by rfl) ⟨224504987, by rfl⟩ : syracuseStep 299339983 = 449009975) B449009975
theorem B399119977 : Blo 1995435 399119977 := bstep (se 2 (by rfl) ⟨149669991, by rfl⟩ : syracuseStep 399119977 = 299339983) B299339983
theorem B532159969 : Blo 1995435 532159969 := bstep (se 2 (by rfl) ⟨199559988, by rfl⟩ : syracuseStep 532159969 = 399119977) B399119977
theorem B709546625 : Blo 1995435 709546625 := bstep (se 2 (by rfl) ⟨266079984, by rfl⟩ : syracuseStep 709546625 = 532159969) B532159969
theorem B473031083 : Blo 1995435 473031083 := bstep (se 1 (by rfl) ⟨354773312, by rfl⟩ : syracuseStep 473031083 = 709546625) B709546625
theorem B315354055 : Blo 1995435 315354055 := bstep (se 1 (by rfl) ⟨236515541, by rfl⟩ : syracuseStep 315354055 = 473031083) B473031083
theorem B420472073 : Blo 1995435 420472073 := bstep (se 2 (by rfl) ⟨157677027, by rfl⟩ : syracuseStep 420472073 = 315354055) B315354055
theorem B1121258861 : Blo 1995435 1121258861 := bstep (se 3 (by rfl) ⟨210236036, by rfl⟩ : syracuseStep 1121258861 = 420472073) B420472073
theorem B747505907 : Blo 1995435 747505907 := bstep (se 1 (by rfl) ⟨560629430, by rfl⟩ : syracuseStep 747505907 = 1121258861) B1121258861
theorem B498337271 : Blo 1995435 498337271 := bstep (se 1 (by rfl) ⟨373752953, by rfl⟩ : syracuseStep 498337271 = 747505907) B747505907
theorem B332224847 : Blo 1995435 332224847 := bstep (se 1 (by rfl) ⟨249168635, by rfl⟩ : syracuseStep 332224847 = 498337271) B498337271
theorem B221483231 : Blo 1995435 221483231 := bstep (se 1 (by rfl) ⟨166112423, by rfl⟩ : syracuseStep 221483231 = 332224847) B332224847
theorem B147655487 : Blo 1995435 147655487 := bstep (se 1 (by rfl) ⟨110741615, by rfl⟩ : syracuseStep 147655487 = 221483231) B221483231
theorem B98436991 : Blo 1995435 98436991 := bstep (se 1 (by rfl) ⟨73827743, by rfl⟩ : syracuseStep 98436991 = 147655487) B147655487
theorem B131249321 : Blo 1995435 131249321 := bstep (se 2 (by rfl) ⟨49218495, by rfl⟩ : syracuseStep 131249321 = 98436991) B98436991
theorem B87499547 : Blo 1995435 87499547 := bstep (se 1 (by rfl) ⟨65624660, by rfl⟩ : syracuseStep 87499547 = 131249321) B131249321
theorem B58333031 : Blo 1995435 58333031 := bstep (se 1 (by rfl) ⟨43749773, by rfl⟩ : syracuseStep 58333031 = 87499547) B87499547
theorem B38888687 : Blo 1995435 38888687 := bstep (se 1 (by rfl) ⟨29166515, by rfl⟩ : syracuseStep 38888687 = 58333031) B58333031
theorem B25925791 : Blo 1995435 25925791 := bstep (se 1 (by rfl) ⟨19444343, by rfl⟩ : syracuseStep 25925791 = 38888687) B38888687
theorem B34567721 : Blo 1995435 34567721 := bstep (se 2 (by rfl) ⟨12962895, by rfl⟩ : syracuseStep 34567721 = 25925791) B25925791
theorem B23045147 : Blo 1995435 23045147 := bstep (se 1 (by rfl) ⟨17283860, by rfl⟩ : syracuseStep 23045147 = 34567721) B34567721
theorem B15363431 : Blo 1995435 15363431 := bstep (se 1 (by rfl) ⟨11522573, by rfl⟩ : syracuseStep 15363431 = 23045147) B23045147
theorem B10242287 : Blo 1995435 10242287 := bstep (se 1 (by rfl) ⟨7681715, by rfl⟩ : syracuseStep 10242287 = 15363431) B15363431
theorem B6828191 : Blo 1995435 6828191 := bstep (se 1 (by rfl) ⟨5121143, by rfl⟩ : syracuseStep 6828191 = 10242287) B10242287
theorem B4552127 : Blo 1995435 4552127 := bstep (se 1 (by rfl) ⟨3414095, by rfl⟩ : syracuseStep 4552127 = 6828191) B6828191
theorem B3034751 : Blo 1995435 3034751 := bstep (se 1 (by rfl) ⟨2276063, by rfl⟩ : syracuseStep 3034751 = 4552127) B4552127
theorem B32370677 : Blo 1995435 32370677 := bstep (se 5 (by rfl) ⟨1517375, by rfl⟩ : syracuseStep 32370677 = 3034751) B3034751
theorem B21580451 : Blo 1995435 21580451 := bstep (se 1 (by rfl) ⟨16185338, by rfl⟩ : syracuseStep 21580451 = 32370677) B32370677
theorem B14386967 : Blo 1995435 14386967 := bstep (se 1 (by rfl) ⟨10790225, by rfl⟩ : syracuseStep 14386967 = 21580451) B21580451
theorem B9591311 : Blo 1995435 9591311 := bstep (se 1 (by rfl) ⟨7193483, by rfl⟩ : syracuseStep 9591311 = 14386967) B14386967
theorem B25576829 : Blo 1995435 25576829 := bstep (se 3 (by rfl) ⟨4795655, by rfl⟩ : syracuseStep 25576829 = 9591311) B9591311
theorem B17051219 : Blo 1995435 17051219 := bstep (se 1 (by rfl) ⟨12788414, by rfl⟩ : syracuseStep 17051219 = 25576829) B25576829
theorem B11367479 : Blo 1995435 11367479 := bstep (se 1 (by rfl) ⟨8525609, by rfl⟩ : syracuseStep 11367479 = 17051219) B17051219
theorem B7578319 : Blo 1995435 7578319 := bstep (se 1 (by rfl) ⟨5683739, by rfl⟩ : syracuseStep 7578319 = 11367479) B11367479
theorem B10104425 : Blo 1995435 10104425 := bstep (se 2 (by rfl) ⟨3789159, by rfl⟩ : syracuseStep 10104425 = 7578319) B7578319
theorem B6736283 : Blo 1995435 6736283 := bstep (se 1 (by rfl) ⟨5052212, by rfl⟩ : syracuseStep 6736283 = 10104425) B10104425
theorem B4490855 : Blo 1995435 4490855 := bstep (se 1 (by rfl) ⟨3368141, by rfl⟩ : syracuseStep 4490855 = 6736283) B6736283
theorem B2993903 : Blo 1995435 2993903 := bstep (se 1 (by rfl) ⟨2245427, by rfl⟩ : syracuseStep 2993903 = 4490855) B4490855
theorem B1995935 : Blo 1995435 1995935 := bstep (se 1 (by rfl) ⟨1496951, by rfl⟩ : syracuseStep 1995935 = 2993903) B2993903
theorem B2993909 : Blo 1995435 2993909 := bbase (se 5 (by rfl) ⟨140339, by rfl⟩ : syracuseStep 2993909 = 280679) (by norm_num)
theorem B1995939 : Blo 1995435 1995939 := bstep (se 1 (by rfl) ⟨1496954, by rfl⟩ : syracuseStep 1995939 = 2993909) B2993909
theorem B3197117 : Blo 1995435 3197117 := bbase (se 3 (by rfl) ⟨599459, by rfl⟩ : syracuseStep 3197117 = 1198919) (by norm_num)
theorem B8525645 : Blo 1995435 8525645 := bstep (se 3 (by rfl) ⟨1598558, by rfl⟩ : syracuseStep 8525645 = 3197117) B3197117
theorem B5683763 : Blo 1995435 5683763 := bstep (se 1 (by rfl) ⟨4262822, by rfl⟩ : syracuseStep 5683763 = 8525645) B8525645
theorem B3789175 : Blo 1995435 3789175 := bstep (se 1 (by rfl) ⟨2841881, by rfl⟩ : syracuseStep 3789175 = 5683763) B5683763
theorem B5052233 : Blo 1995435 5052233 := bstep (se 2 (by rfl) ⟨1894587, by rfl⟩ : syracuseStep 5052233 = 3789175) B3789175
theorem B3368155 : Blo 1995435 3368155 := bstep (se 1 (by rfl) ⟨2526116, by rfl⟩ : syracuseStep 3368155 = 5052233) B5052233
theorem B4490873 : Blo 1995435 4490873 := bstep (se 2 (by rfl) ⟨1684077, by rfl⟩ : syracuseStep 4490873 = 3368155) B3368155
theorem B2993915 : Blo 1995435 2993915 := bstep (se 1 (by rfl) ⟨2245436, by rfl⟩ : syracuseStep 2993915 = 4490873) B4490873
theorem B1995943 : Blo 1995435 1995943 := bstep (se 1 (by rfl) ⟨1496957, by rfl⟩ : syracuseStep 1995943 = 2993915) B2993915
theorem B2245441 : Blo 1995435 2245441 := bbase (se 2 (by rfl) ⟨842040, by rfl⟩ : syracuseStep 2245441 = 1684081) (by norm_num)
theorem B2993921 : Blo 1995435 2993921 := bstep (se 2 (by rfl) ⟨1122720, by rfl⟩ : syracuseStep 2993921 = 2245441) B2245441
theorem B1995947 : Blo 1995435 1995947 := bstep (se 1 (by rfl) ⟨1496960, by rfl⟩ : syracuseStep 1995947 = 2993921) B2993921
theorem B5052253 : Blo 1995435 5052253 := bbase (se 3 (by rfl) ⟨947297, by rfl⟩ : syracuseStep 5052253 = 1894595) (by norm_num)
theorem B6736337 : Blo 1995435 6736337 := bstep (se 2 (by rfl) ⟨2526126, by rfl⟩ : syracuseStep 6736337 = 5052253) B5052253
theorem B4490891 : Blo 1995435 4490891 := bstep (se 1 (by rfl) ⟨3368168, by rfl⟩ : syracuseStep 4490891 = 6736337) B6736337
theorem B2993927 : Blo 1995435 2993927 := bstep (se 1 (by rfl) ⟨2245445, by rfl⟩ : syracuseStep 2993927 = 4490891) B4490891
theorem B1995951 : Blo 1995435 1995951 := bstep (se 1 (by rfl) ⟨1496963, by rfl⟩ : syracuseStep 1995951 = 2993927) B2993927
theorem B2993933 : Blo 1995435 2993933 := bbase (se 3 (by rfl) ⟨561362, by rfl⟩ : syracuseStep 2993933 = 1122725) (by norm_num)
theorem B1995955 : Blo 1995435 1995955 := bstep (se 1 (by rfl) ⟨1496966, by rfl⟩ : syracuseStep 1995955 = 2993933) B2993933
theorem B4490909 : Blo 1995435 4490909 := bbase (se 3 (by rfl) ⟨842045, by rfl⟩ : syracuseStep 4490909 = 1684091) (by norm_num)
theorem B2993939 : Blo 1995435 2993939 := bstep (se 1 (by rfl) ⟨2245454, by rfl⟩ : syracuseStep 2993939 = 4490909) B4490909
theorem B1995959 : Blo 1995435 1995959 := bstep (se 1 (by rfl) ⟨1496969, by rfl⟩ : syracuseStep 1995959 = 2993939) B2993939
theorem B3368189 : Blo 1995435 3368189 := bbase (se 3 (by rfl) ⟨631535, by rfl⟩ : syracuseStep 3368189 = 1263071) (by norm_num)
theorem B2245459 : Blo 1995435 2245459 := bstep (se 1 (by rfl) ⟨1684094, by rfl⟩ : syracuseStep 2245459 = 3368189) B3368189
theorem B2993945 : Blo 1995435 2993945 := bstep (se 2 (by rfl) ⟨1122729, by rfl⟩ : syracuseStep 2993945 = 2245459) B2245459
theorem B1995963 : Blo 1995435 1995963 := bstep (se 1 (by rfl) ⟨1496972, by rfl⟩ : syracuseStep 1995963 = 2993945) B2993945
theorem B4795733 : Blo 1995435 4795733 := bbase (se 11 (by rfl) ⟨3512, by rfl⟩ : syracuseStep 4795733 = 7025) (by norm_num)
theorem B3197155 : Blo 1995435 3197155 := bstep (se 1 (by rfl) ⟨2397866, by rfl⟩ : syracuseStep 3197155 = 4795733) B4795733
theorem B4262873 : Blo 1995435 4262873 := bstep (se 2 (by rfl) ⟨1598577, by rfl⟩ : syracuseStep 4262873 = 3197155) B3197155
theorem B11367661 : Blo 1995435 11367661 := bstep (se 3 (by rfl) ⟨2131436, by rfl⟩ : syracuseStep 11367661 = 4262873) B4262873
theorem B15156881 : Blo 1995435 15156881 := bstep (se 2 (by rfl) ⟨5683830, by rfl⟩ : syracuseStep 15156881 = 11367661) B11367661
theorem B10104587 : Blo 1995435 10104587 := bstep (se 1 (by rfl) ⟨7578440, by rfl⟩ : syracuseStep 10104587 = 15156881) B15156881
theorem B6736391 : Blo 1995435 6736391 := bstep (se 1 (by rfl) ⟨5052293, by rfl⟩ : syracuseStep 6736391 = 10104587) B10104587
theorem B4490927 : Blo 1995435 4490927 := bstep (se 1 (by rfl) ⟨3368195, by rfl⟩ : syracuseStep 4490927 = 6736391) B6736391
theorem B2993951 : Blo 1995435 2993951 := bstep (se 1 (by rfl) ⟨2245463, by rfl⟩ : syracuseStep 2993951 = 4490927) B4490927
theorem B1995967 : Blo 1995435 1995967 := bstep (se 1 (by rfl) ⟨1496975, by rfl⟩ : syracuseStep 1995967 = 2993951) B2993951
theorem B2993957 : Blo 1995435 2993957 := bbase (se 4 (by rfl) ⟨280683, by rfl⟩ : syracuseStep 2993957 = 561367) (by norm_num)
theorem B1995971 : Blo 1995435 1995971 := bstep (se 1 (by rfl) ⟨1496978, by rfl⟩ : syracuseStep 1995971 = 2993957) B2993957
theorem B2526157 : Blo 1995435 2526157 := bbase (se 3 (by rfl) ⟨473654, by rfl⟩ : syracuseStep 2526157 = 947309) (by norm_num)
theorem B3368209 : Blo 1995435 3368209 := bstep (se 2 (by rfl) ⟨1263078, by rfl⟩ : syracuseStep 3368209 = 2526157) B2526157
theorem B4490945 : Blo 1995435 4490945 := bstep (se 2 (by rfl) ⟨1684104, by rfl⟩ : syracuseStep 4490945 = 3368209) B3368209
theorem B2993963 : Blo 1995435 2993963 := bstep (se 1 (by rfl) ⟨2245472, by rfl⟩ : syracuseStep 2993963 = 4490945) B4490945
theorem B1995975 : Blo 1995435 1995975 := bstep (se 1 (by rfl) ⟨1496981, by rfl⟩ : syracuseStep 1995975 = 2993963) B2993963
theorem B2245477 : Blo 1995435 2245477 := bbase (se 4 (by rfl) ⟨210513, by rfl⟩ : syracuseStep 2245477 = 421027) (by norm_num)
theorem B2993969 : Blo 1995435 2993969 := bstep (se 2 (by rfl) ⟨1122738, by rfl⟩ : syracuseStep 2993969 = 2245477) B2245477
theorem B1995979 : Blo 1995435 1995979 := bstep (se 1 (by rfl) ⟨1496984, by rfl⟩ : syracuseStep 1995979 = 2993969) B2993969
theorem B5683877 : Blo 1995435 5683877 := bbase (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) (by norm_num)
theorem B3789251 : Blo 1995435 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B2526167 : Blo 1995435 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B6736445 : Blo 1995435 6736445 := bstep (se 3 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 6736445 = 2526167) B2526167
theorem B4490963 : Blo 1995435 4490963 := bstep (se 1 (by rfl) ⟨3368222, by rfl⟩ : syracuseStep 4490963 = 6736445) B6736445
theorem B2993975 : Blo 1995435 2993975 := bstep (se 1 (by rfl) ⟨2245481, by rfl⟩ : syracuseStep 2993975 = 4490963) B4490963
theorem B1995983 : Blo 1995435 1995983 := bstep (se 1 (by rfl) ⟨1496987, by rfl⟩ : syracuseStep 1995983 = 2993975) B2993975
theorem B2993981 : Blo 1995435 2993981 := bbase (se 3 (by rfl) ⟨561371, by rfl⟩ : syracuseStep 2993981 = 1122743) (by norm_num)
theorem B1995987 : Blo 1995435 1995987 := bstep (se 1 (by rfl) ⟨1496990, by rfl⟩ : syracuseStep 1995987 = 2993981) B2993981
theorem B4490981 : Blo 1995435 4490981 := bbase (se 4 (by rfl) ⟨421029, by rfl⟩ : syracuseStep 4490981 = 842059) (by norm_num)
theorem B2993987 : Blo 1995435 2993987 := bstep (se 1 (by rfl) ⟨2245490, by rfl⟩ : syracuseStep 2993987 = 4490981) B4490981
theorem B1995991 : Blo 1995435 1995991 := bstep (se 1 (by rfl) ⟨1496993, by rfl⟩ : syracuseStep 1995991 = 2993987) B2993987
theorem B5052365 : Blo 1995435 5052365 := bbase (se 3 (by rfl) ⟨947318, by rfl⟩ : syracuseStep 5052365 = 1894637) (by norm_num)
theorem B3368243 : Blo 1995435 3368243 := bstep (se 1 (by rfl) ⟨2526182, by rfl⟩ : syracuseStep 3368243 = 5052365) B5052365
theorem B2245495 : Blo 1995435 2245495 := bstep (se 1 (by rfl) ⟨1684121, by rfl⟩ : syracuseStep 2245495 = 3368243) B3368243
theorem B2993993 : Blo 1995435 2993993 := bstep (se 2 (by rfl) ⟨1122747, by rfl⟩ : syracuseStep 2993993 = 2245495) B2245495
theorem B1995995 : Blo 1995435 1995995 := bstep (se 1 (by rfl) ⟨1496996, by rfl⟩ : syracuseStep 1995995 = 2993993) B2993993
theorem B7193717 : Blo 1995435 7193717 := bbase (se 5 (by rfl) ⟨337205, by rfl⟩ : syracuseStep 7193717 = 674411) (by norm_num)
theorem B4795811 : Blo 1995435 4795811 := bstep (se 1 (by rfl) ⟨3596858, by rfl⟩ : syracuseStep 4795811 = 7193717) B7193717
theorem B3197207 : Blo 1995435 3197207 := bstep (se 1 (by rfl) ⟨2397905, by rfl⟩ : syracuseStep 3197207 = 4795811) B4795811
theorem B2131471 : Blo 1995435 2131471 := bstep (se 1 (by rfl) ⟨1598603, by rfl⟩ : syracuseStep 2131471 = 3197207) B3197207
theorem B2841961 : Blo 1995435 2841961 := bstep (se 2 (by rfl) ⟨1065735, by rfl⟩ : syracuseStep 2841961 = 2131471) B2131471
theorem B3789281 : Blo 1995435 3789281 := bstep (se 2 (by rfl) ⟨1420980, by rfl⟩ : syracuseStep 3789281 = 2841961) B2841961
theorem B10104749 : Blo 1995435 10104749 := bstep (se 3 (by rfl) ⟨1894640, by rfl⟩ : syracuseStep 10104749 = 3789281) B3789281
theorem B6736499 : Blo 1995435 6736499 := bstep (se 1 (by rfl) ⟨5052374, by rfl⟩ : syracuseStep 6736499 = 10104749) B10104749
theorem B4490999 : Blo 1995435 4490999 := bstep (se 1 (by rfl) ⟨3368249, by rfl⟩ : syracuseStep 4490999 = 6736499) B6736499
theorem B2993999 : Blo 1995435 2993999 := bstep (se 1 (by rfl) ⟨2245499, by rfl⟩ : syracuseStep 2993999 = 4490999) B4490999
theorem B1995999 : Blo 1995435 1995999 := bstep (se 1 (by rfl) ⟨1496999, by rfl⟩ : syracuseStep 1995999 = 2993999) B2993999
theorem B2994005 : Blo 1995435 2994005 := bbase (se 9 (by rfl) ⟨8771, by rfl⟩ : syracuseStep 2994005 = 17543) (by norm_num)
theorem B1996003 : Blo 1995435 1996003 := bstep (se 1 (by rfl) ⟨1497002, by rfl⟩ : syracuseStep 1996003 = 2994005) B2994005
theorem B12139445 : Blo 1995435 12139445 := bbase (se 5 (by rfl) ⟨569036, by rfl⟩ : syracuseStep 12139445 = 1138073) (by norm_num)
theorem B8092963 : Blo 1995435 8092963 := bstep (se 1 (by rfl) ⟨6069722, by rfl⟩ : syracuseStep 8092963 = 12139445) B12139445
theorem B10790617 : Blo 1995435 10790617 := bstep (se 2 (by rfl) ⟨4046481, by rfl⟩ : syracuseStep 10790617 = 8092963) B8092963
theorem B14387489 : Blo 1995435 14387489 := bstep (se 2 (by rfl) ⟨5395308, by rfl⟩ : syracuseStep 14387489 = 10790617) B10790617
theorem B9591659 : Blo 1995435 9591659 := bstep (se 1 (by rfl) ⟨7193744, by rfl⟩ : syracuseStep 9591659 = 14387489) B14387489
theorem B6394439 : Blo 1995435 6394439 := bstep (se 1 (by rfl) ⟨4795829, by rfl⟩ : syracuseStep 6394439 = 9591659) B9591659
theorem B4262959 : Blo 1995435 4262959 := bstep (se 1 (by rfl) ⟨3197219, by rfl⟩ : syracuseStep 4262959 = 6394439) B6394439
theorem B5683945 : Blo 1995435 5683945 := bstep (se 2 (by rfl) ⟨2131479, by rfl⟩ : syracuseStep 5683945 = 4262959) B4262959
theorem B7578593 : Blo 1995435 7578593 := bstep (se 2 (by rfl) ⟨2841972, by rfl⟩ : syracuseStep 7578593 = 5683945) B5683945
theorem B5052395 : Blo 1995435 5052395 := bstep (se 1 (by rfl) ⟨3789296, by rfl⟩ : syracuseStep 5052395 = 7578593) B7578593
theorem B3368263 : Blo 1995435 3368263 := bstep (se 1 (by rfl) ⟨2526197, by rfl⟩ : syracuseStep 3368263 = 5052395) B5052395
theorem B4491017 : Blo 1995435 4491017 := bstep (se 2 (by rfl) ⟨1684131, by rfl⟩ : syracuseStep 4491017 = 3368263) B3368263
theorem B2994011 : Blo 1995435 2994011 := bstep (se 1 (by rfl) ⟨2245508, by rfl⟩ : syracuseStep 2994011 = 4491017) B4491017
theorem B1996007 : Blo 1995435 1996007 := bstep (se 1 (by rfl) ⟨1497005, by rfl⟩ : syracuseStep 1996007 = 2994011) B2994011
theorem B2245513 : Blo 1995435 2245513 := bbase (se 2 (by rfl) ⟨842067, by rfl⟩ : syracuseStep 2245513 = 1684135) (by norm_num)
theorem B2994017 : Blo 1995435 2994017 := bstep (se 2 (by rfl) ⟨1122756, by rfl⟩ : syracuseStep 2994017 = 2245513) B2245513
theorem B1996011 : Blo 1995435 1996011 := bstep (se 1 (by rfl) ⟨1497008, by rfl⟩ : syracuseStep 1996011 = 2994017) B2994017
theorem B3240853 : Blo 1995435 3240853 := bbase (se 6 (by rfl) ⟨75957, by rfl⟩ : syracuseStep 3240853 = 151915) (by norm_num)
theorem B17284549 : Blo 1995435 17284549 := bstep (se 4 (by rfl) ⟨1620426, by rfl⟩ : syracuseStep 17284549 = 3240853) B3240853
theorem B23046065 : Blo 1995435 23046065 := bstep (se 2 (by rfl) ⟨8642274, by rfl⟩ : syracuseStep 23046065 = 17284549) B17284549
theorem B15364043 : Blo 1995435 15364043 := bstep (se 1 (by rfl) ⟨11523032, by rfl⟩ : syracuseStep 15364043 = 23046065) B23046065
theorem B10242695 : Blo 1995435 10242695 := bstep (se 1 (by rfl) ⟨7682021, by rfl⟩ : syracuseStep 10242695 = 15364043) B15364043
theorem B27313853 : Blo 1995435 27313853 := bstep (se 3 (by rfl) ⟨5121347, by rfl⟩ : syracuseStep 27313853 = 10242695) B10242695
theorem B291347765 : Blo 1995435 291347765 := bstep (se 5 (by rfl) ⟨13656926, by rfl⟩ : syracuseStep 291347765 = 27313853) B27313853
theorem B194231843 : Blo 1995435 194231843 := bstep (se 1 (by rfl) ⟨145673882, by rfl⟩ : syracuseStep 194231843 = 291347765) B291347765
theorem B129487895 : Blo 1995435 129487895 := bstep (se 1 (by rfl) ⟨97115921, by rfl⟩ : syracuseStep 129487895 = 194231843) B194231843
theorem B86325263 : Blo 1995435 86325263 := bstep (se 1 (by rfl) ⟨64743947, by rfl⟩ : syracuseStep 86325263 = 129487895) B129487895
theorem B57550175 : Blo 1995435 57550175 := bstep (se 1 (by rfl) ⟨43162631, by rfl⟩ : syracuseStep 57550175 = 86325263) B86325263
theorem B38366783 : Blo 1995435 38366783 := bstep (se 1 (by rfl) ⟨28775087, by rfl⟩ : syracuseStep 38366783 = 57550175) B57550175
theorem B25577855 : Blo 1995435 25577855 := bstep (se 1 (by rfl) ⟨19183391, by rfl⟩ : syracuseStep 25577855 = 38366783) B38366783
theorem B17051903 : Blo 1995435 17051903 := bstep (se 1 (by rfl) ⟨12788927, by rfl⟩ : syracuseStep 17051903 = 25577855) B25577855
theorem B11367935 : Blo 1995435 11367935 := bstep (se 1 (by rfl) ⟨8525951, by rfl⟩ : syracuseStep 11367935 = 17051903) B17051903
theorem B7578623 : Blo 1995435 7578623 := bstep (se 1 (by rfl) ⟨5683967, by rfl⟩ : syracuseStep 7578623 = 11367935) B11367935
theorem B5052415 : Blo 1995435 5052415 := bstep (se 1 (by rfl) ⟨3789311, by rfl⟩ : syracuseStep 5052415 = 7578623) B7578623
theorem B6736553 : Blo 1995435 6736553 := bstep (se 2 (by rfl) ⟨2526207, by rfl⟩ : syracuseStep 6736553 = 5052415) B5052415
theorem B4491035 : Blo 1995435 4491035 := bstep (se 1 (by rfl) ⟨3368276, by rfl⟩ : syracuseStep 4491035 = 6736553) B6736553
theorem B2994023 : Blo 1995435 2994023 := bstep (se 1 (by rfl) ⟨2245517, by rfl⟩ : syracuseStep 2994023 = 4491035) B4491035
theorem B1996015 : Blo 1995435 1996015 := bstep (se 1 (by rfl) ⟨1497011, by rfl⟩ : syracuseStep 1996015 = 2994023) B2994023
theorem B2994029 : Blo 1995435 2994029 := bbase (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) (by norm_num)
theorem B1996019 : Blo 1995435 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B4491053 : Blo 1995435 4491053 := bbase (se 3 (by rfl) ⟨842072, by rfl⟩ : syracuseStep 4491053 = 1684145) (by norm_num)
theorem B2994035 : Blo 1995435 2994035 := bstep (se 1 (by rfl) ⟨2245526, by rfl⟩ : syracuseStep 2994035 = 4491053) B4491053
theorem B1996023 : Blo 1995435 1996023 := bstep (se 1 (by rfl) ⟨1497017, by rfl⟩ : syracuseStep 1996023 = 2994035) B2994035
theorem B8526005 : Blo 1995435 8526005 := bbase (se 5 (by rfl) ⟨399656, by rfl⟩ : syracuseStep 8526005 = 799313) (by norm_num)
theorem B5684003 : Blo 1995435 5684003 := bstep (se 1 (by rfl) ⟨4263002, by rfl⟩ : syracuseStep 5684003 = 8526005) B8526005
theorem B3789335 : Blo 1995435 3789335 := bstep (se 1 (by rfl) ⟨2842001, by rfl⟩ : syracuseStep 3789335 = 5684003) B5684003
theorem B2526223 : Blo 1995435 2526223 := bstep (se 1 (by rfl) ⟨1894667, by rfl⟩ : syracuseStep 2526223 = 3789335) B3789335
theorem B3368297 : Blo 1995435 3368297 := bstep (se 2 (by rfl) ⟨1263111, by rfl⟩ : syracuseStep 3368297 = 2526223) B2526223
theorem B2245531 : Blo 1995435 2245531 := bstep (se 1 (by rfl) ⟨1684148, by rfl⟩ : syracuseStep 2245531 = 3368297) B3368297
theorem B2994041 : Blo 1995435 2994041 := bstep (se 2 (by rfl) ⟨1122765, by rfl⟩ : syracuseStep 2994041 = 2245531) B2245531
theorem B1996027 : Blo 1995435 1996027 := bstep (se 1 (by rfl) ⟨1497020, by rfl⟩ : syracuseStep 1996027 = 2994041) B2994041
theorem B2023265 : Blo 1995435 2023265 := bbase (se 2 (by rfl) ⟨758724, by rfl⟩ : syracuseStep 2023265 = 1517449) (by norm_num)
theorem B5395373 : Blo 1995435 5395373 := bstep (se 3 (by rfl) ⟨1011632, by rfl⟩ : syracuseStep 5395373 = 2023265) B2023265
theorem B3596915 : Blo 1995435 3596915 := bstep (se 1 (by rfl) ⟨2697686, by rfl⟩ : syracuseStep 3596915 = 5395373) B5395373
theorem B2397943 : Blo 1995435 2397943 := bstep (se 1 (by rfl) ⟨1798457, by rfl⟩ : syracuseStep 2397943 = 3596915) B3596915
theorem B12789029 : Blo 1995435 12789029 := bstep (se 4 (by rfl) ⟨1198971, by rfl⟩ : syracuseStep 12789029 = 2397943) B2397943
theorem B34104077 : Blo 1995435 34104077 := bstep (se 3 (by rfl) ⟨6394514, by rfl⟩ : syracuseStep 34104077 = 12789029) B12789029
theorem B22736051 : Blo 1995435 22736051 := bstep (se 1 (by rfl) ⟨17052038, by rfl⟩ : syracuseStep 22736051 = 34104077) B34104077
theorem B15157367 : Blo 1995435 15157367 := bstep (se 1 (by rfl) ⟨11368025, by rfl⟩ : syracuseStep 15157367 = 22736051) B22736051
theorem B10104911 : Blo 1995435 10104911 := bstep (se 1 (by rfl) ⟨7578683, by rfl⟩ : syracuseStep 10104911 = 15157367) B15157367
theorem B6736607 : Blo 1995435 6736607 := bstep (se 1 (by rfl) ⟨5052455, by rfl⟩ : syracuseStep 6736607 = 10104911) B10104911
theorem B4491071 : Blo 1995435 4491071 := bstep (se 1 (by rfl) ⟨3368303, by rfl⟩ : syracuseStep 4491071 = 6736607) B6736607
theorem B2994047 : Blo 1995435 2994047 := bstep (se 1 (by rfl) ⟨2245535, by rfl⟩ : syracuseStep 2994047 = 4491071) B4491071
theorem B1996031 : Blo 1995435 1996031 := bstep (se 1 (by rfl) ⟨1497023, by rfl⟩ : syracuseStep 1996031 = 2994047) B2994047
theorem B2994053 : Blo 1995435 2994053 := bbase (se 4 (by rfl) ⟨280692, by rfl⟩ : syracuseStep 2994053 = 561385) (by norm_num)
theorem B1996035 : Blo 1995435 1996035 := bstep (se 1 (by rfl) ⟨1497026, by rfl⟩ : syracuseStep 1996035 = 2994053) B2994053
theorem B3368317 : Blo 1995435 3368317 := bbase (se 3 (by rfl) ⟨631559, by rfl⟩ : syracuseStep 3368317 = 1263119) (by norm_num)
theorem B4491089 : Blo 1995435 4491089 := bstep (se 2 (by rfl) ⟨1684158, by rfl⟩ : syracuseStep 4491089 = 3368317) B3368317
theorem B2994059 : Blo 1995435 2994059 := bstep (se 1 (by rfl) ⟨2245544, by rfl⟩ : syracuseStep 2994059 = 4491089) B4491089
theorem B1996039 : Blo 1995435 1996039 := bstep (se 1 (by rfl) ⟨1497029, by rfl⟩ : syracuseStep 1996039 = 2994059) B2994059
theorem B2245549 : Blo 1995435 2245549 := bbase (se 3 (by rfl) ⟨421040, by rfl⟩ : syracuseStep 2245549 = 842081) (by norm_num)
theorem B2994065 : Blo 1995435 2994065 := bstep (se 2 (by rfl) ⟨1122774, by rfl⟩ : syracuseStep 2994065 = 2245549) B2245549
theorem B1996043 : Blo 1995435 1996043 := bstep (se 1 (by rfl) ⟨1497032, by rfl⟩ : syracuseStep 1996043 = 2994065) B2994065
theorem B6736661 : Blo 1995435 6736661 := bbase (se 6 (by rfl) ⟨157890, by rfl⟩ : syracuseStep 6736661 = 315781) (by norm_num)
theorem B4491107 : Blo 1995435 4491107 := bstep (se 1 (by rfl) ⟨3368330, by rfl⟩ : syracuseStep 4491107 = 6736661) B6736661
theorem B2994071 : Blo 1995435 2994071 := bstep (se 1 (by rfl) ⟨2245553, by rfl⟩ : syracuseStep 2994071 = 4491107) B4491107
theorem B1996047 : Blo 1995435 1996047 := bstep (se 1 (by rfl) ⟨1497035, by rfl⟩ : syracuseStep 1996047 = 2994071) B2994071
theorem B2994077 : Blo 1995435 2994077 := bbase (se 3 (by rfl) ⟨561389, by rfl⟩ : syracuseStep 2994077 = 1122779) (by norm_num)
theorem B1996051 : Blo 1995435 1996051 := bstep (se 1 (by rfl) ⟨1497038, by rfl⟩ : syracuseStep 1996051 = 2994077) B2994077
theorem B4491125 : Blo 1995435 4491125 := bbase (se 5 (by rfl) ⟨210521, by rfl⟩ : syracuseStep 4491125 = 421043) (by norm_num)
theorem B2994083 : Blo 1995435 2994083 := bstep (se 1 (by rfl) ⟨2245562, by rfl⟩ : syracuseStep 2994083 = 4491125) B4491125
theorem B1996055 : Blo 1995435 1996055 := bstep (se 1 (by rfl) ⟨1497041, by rfl⟩ : syracuseStep 1996055 = 2994083) B2994083
theorem B32372693 : Blo 1995435 32372693 := bbase (se 7 (by rfl) ⟨379367, by rfl⟩ : syracuseStep 32372693 = 758735) (by norm_num)
theorem B21581795 : Blo 1995435 21581795 := bstep (se 1 (by rfl) ⟨16186346, by rfl⟩ : syracuseStep 21581795 = 32372693) B32372693
theorem B14387863 : Blo 1995435 14387863 := bstep (se 1 (by rfl) ⟨10790897, by rfl⟩ : syracuseStep 14387863 = 21581795) B21581795
theorem B19183817 : Blo 1995435 19183817 := bstep (se 2 (by rfl) ⟨7193931, by rfl⟩ : syracuseStep 19183817 = 14387863) B14387863
theorem B12789211 : Blo 1995435 12789211 := bstep (se 1 (by rfl) ⟨9591908, by rfl⟩ : syracuseStep 12789211 = 19183817) B19183817
theorem B17052281 : Blo 1995435 17052281 := bstep (se 2 (by rfl) ⟨6394605, by rfl⟩ : syracuseStep 17052281 = 12789211) B12789211
theorem B11368187 : Blo 1995435 11368187 := bstep (se 1 (by rfl) ⟨8526140, by rfl⟩ : syracuseStep 11368187 = 17052281) B17052281
theorem B7578791 : Blo 1995435 7578791 := bstep (se 1 (by rfl) ⟨5684093, by rfl⟩ : syracuseStep 7578791 = 11368187) B11368187
theorem B5052527 : Blo 1995435 5052527 := bstep (se 1 (by rfl) ⟨3789395, by rfl⟩ : syracuseStep 5052527 = 7578791) B7578791
theorem B3368351 : Blo 1995435 3368351 := bstep (se 1 (by rfl) ⟨2526263, by rfl⟩ : syracuseStep 3368351 = 5052527) B5052527
theorem B2245567 : Blo 1995435 2245567 := bstep (se 1 (by rfl) ⟨1684175, by rfl⟩ : syracuseStep 2245567 = 3368351) B3368351
theorem B2994089 : Blo 1995435 2994089 := bstep (se 2 (by rfl) ⟨1122783, by rfl⟩ : syracuseStep 2994089 = 2245567) B2245567
theorem B1996059 : Blo 1995435 1996059 := bstep (se 1 (by rfl) ⟨1497044, by rfl⟩ : syracuseStep 1996059 = 2994089) B2994089
theorem B7578805 : Blo 1995435 7578805 := bbase (se 5 (by rfl) ⟨355256, by rfl⟩ : syracuseStep 7578805 = 710513) (by norm_num)
theorem B10105073 : Blo 1995435 10105073 := bstep (se 2 (by rfl) ⟨3789402, by rfl⟩ : syracuseStep 10105073 = 7578805) B7578805
theorem B6736715 : Blo 1995435 6736715 := bstep (se 1 (by rfl) ⟨5052536, by rfl⟩ : syracuseStep 6736715 = 10105073) B10105073
theorem B4491143 : Blo 1995435 4491143 := bstep (se 1 (by rfl) ⟨3368357, by rfl⟩ : syracuseStep 4491143 = 6736715) B6736715
theorem B2994095 : Blo 1995435 2994095 := bstep (se 1 (by rfl) ⟨2245571, by rfl⟩ : syracuseStep 2994095 = 4491143) B4491143
theorem B1996063 : Blo 1995435 1996063 := bstep (se 1 (by rfl) ⟨1497047, by rfl⟩ : syracuseStep 1996063 = 2994095) B2994095
theorem B2994101 : Blo 1995435 2994101 := bbase (se 5 (by rfl) ⟨140348, by rfl⟩ : syracuseStep 2994101 = 280697) (by norm_num)
theorem B1996067 : Blo 1995435 1996067 := bstep (se 1 (by rfl) ⟨1497050, by rfl⟩ : syracuseStep 1996067 = 2994101) B2994101
theorem B5052557 : Blo 1995435 5052557 := bbase (se 3 (by rfl) ⟨947354, by rfl⟩ : syracuseStep 5052557 = 1894709) (by norm_num)
theorem B3368371 : Blo 1995435 3368371 := bstep (se 1 (by rfl) ⟨2526278, by rfl⟩ : syracuseStep 3368371 = 5052557) B5052557
theorem B4491161 : Blo 1995435 4491161 := bstep (se 2 (by rfl) ⟨1684185, by rfl⟩ : syracuseStep 4491161 = 3368371) B3368371
theorem B2994107 : Blo 1995435 2994107 := bstep (se 1 (by rfl) ⟨2245580, by rfl⟩ : syracuseStep 2994107 = 4491161) B4491161
theorem B1996071 : Blo 1995435 1996071 := bstep (se 1 (by rfl) ⟨1497053, by rfl⟩ : syracuseStep 1996071 = 2994107) B2994107
theorem B2245585 : Blo 1995435 2245585 := bbase (se 2 (by rfl) ⟨842094, by rfl⟩ : syracuseStep 2245585 = 1684189) (by norm_num)
theorem B2994113 : Blo 1995435 2994113 := bstep (se 2 (by rfl) ⟨1122792, by rfl⟩ : syracuseStep 2994113 = 2245585) B2245585
theorem B1996075 : Blo 1995435 1996075 := bstep (se 1 (by rfl) ⟨1497056, by rfl⟩ : syracuseStep 1996075 = 2994113) B2994113
theorem B7194005 : Blo 1995435 7194005 := bbase (se 6 (by rfl) ⟨168609, by rfl⟩ : syracuseStep 7194005 = 337219) (by norm_num)
theorem B4796003 : Blo 1995435 4796003 := bstep (se 1 (by rfl) ⟨3597002, by rfl⟩ : syracuseStep 4796003 = 7194005) B7194005
theorem B3197335 : Blo 1995435 3197335 := bstep (se 1 (by rfl) ⟨2398001, by rfl⟩ : syracuseStep 3197335 = 4796003) B4796003
theorem B4263113 : Blo 1995435 4263113 := bstep (se 2 (by rfl) ⟨1598667, by rfl⟩ : syracuseStep 4263113 = 3197335) B3197335
theorem B2842075 : Blo 1995435 2842075 := bstep (se 1 (by rfl) ⟨2131556, by rfl⟩ : syracuseStep 2842075 = 4263113) B4263113
theorem B3789433 : Blo 1995435 3789433 := bstep (se 2 (by rfl) ⟨1421037, by rfl⟩ : syracuseStep 3789433 = 2842075) B2842075
theorem B5052577 : Blo 1995435 5052577 := bstep (se 2 (by rfl) ⟨1894716, by rfl⟩ : syracuseStep 5052577 = 3789433) B3789433
theorem B6736769 : Blo 1995435 6736769 := bstep (se 2 (by rfl) ⟨2526288, by rfl⟩ : syracuseStep 6736769 = 5052577) B5052577
theorem B4491179 : Blo 1995435 4491179 := bstep (se 1 (by rfl) ⟨3368384, by rfl⟩ : syracuseStep 4491179 = 6736769) B6736769
theorem B2994119 : Blo 1995435 2994119 := bstep (se 1 (by rfl) ⟨2245589, by rfl⟩ : syracuseStep 2994119 = 4491179) B4491179
theorem B1996079 : Blo 1995435 1996079 := bstep (se 1 (by rfl) ⟨1497059, by rfl⟩ : syracuseStep 1996079 = 2994119) B2994119
theorem B2994125 : Blo 1995435 2994125 := bbase (se 3 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 2994125 = 1122797) (by norm_num)
theorem B1996083 : Blo 1995435 1996083 := bstep (se 1 (by rfl) ⟨1497062, by rfl⟩ : syracuseStep 1996083 = 2994125) B2994125
theorem B4491197 : Blo 1995435 4491197 := bbase (se 3 (by rfl) ⟨842099, by rfl⟩ : syracuseStep 4491197 = 1684199) (by norm_num)
theorem B2994131 : Blo 1995435 2994131 := bstep (se 1 (by rfl) ⟨2245598, by rfl⟩ : syracuseStep 2994131 = 4491197) B4491197
theorem B1996087 : Blo 1995435 1996087 := bstep (se 1 (by rfl) ⟨1497065, by rfl⟩ : syracuseStep 1996087 = 2994131) B2994131
theorem B3368405 : Blo 1995435 3368405 := bbase (se 7 (by rfl) ⟨39473, by rfl⟩ : syracuseStep 3368405 = 78947) (by norm_num)
theorem B2245603 : Blo 1995435 2245603 := bstep (se 1 (by rfl) ⟨1684202, by rfl⟩ : syracuseStep 2245603 = 3368405) B3368405
theorem B2994137 : Blo 1995435 2994137 := bstep (se 2 (by rfl) ⟨1122801, by rfl⟩ : syracuseStep 2994137 = 2245603) B2245603
theorem B1996091 : Blo 1995435 1996091 := bstep (se 1 (by rfl) ⟨1497068, by rfl⟩ : syracuseStep 1996091 = 2994137) B2994137
theorem B8526293 : Blo 1995435 8526293 := bbase (se 7 (by rfl) ⟨99917, by rfl⟩ : syracuseStep 8526293 = 199835) (by norm_num)
theorem B5684195 : Blo 1995435 5684195 := bstep (se 1 (by rfl) ⟨4263146, by rfl⟩ : syracuseStep 5684195 = 8526293) B8526293
theorem B15157853 : Blo 1995435 15157853 := bstep (se 3 (by rfl) ⟨2842097, by rfl⟩ : syracuseStep 15157853 = 5684195) B5684195
theorem B10105235 : Blo 1995435 10105235 := bstep (se 1 (by rfl) ⟨7578926, by rfl⟩ : syracuseStep 10105235 = 15157853) B15157853
theorem B6736823 : Blo 1995435 6736823 := bstep (se 1 (by rfl) ⟨5052617, by rfl⟩ : syracuseStep 6736823 = 10105235) B10105235
theorem B4491215 : Blo 1995435 4491215 := bstep (se 1 (by rfl) ⟨3368411, by rfl⟩ : syracuseStep 4491215 = 6736823) B6736823
theorem B2994143 : Blo 1995435 2994143 := bstep (se 1 (by rfl) ⟨2245607, by rfl⟩ : syracuseStep 2994143 = 4491215) B4491215
theorem B1996095 : Blo 1995435 1996095 := bstep (se 1 (by rfl) ⟨1497071, by rfl⟩ : syracuseStep 1996095 = 2994143) B2994143
theorem B2994149 : Blo 1995435 2994149 := bbase (se 4 (by rfl) ⟨280701, by rfl⟩ : syracuseStep 2994149 = 561403) (by norm_num)
theorem B1996099 : Blo 1995435 1996099 := bstep (se 1 (by rfl) ⟨1497074, by rfl⟩ : syracuseStep 1996099 = 2994149) B2994149
theorem B28448405 : Blo 1995435 28448405 := bbase (se 6 (by rfl) ⟨666759, by rfl⟩ : syracuseStep 28448405 = 1333519) (by norm_num)
theorem B18965603 : Blo 1995435 18965603 := bstep (se 1 (by rfl) ⟨14224202, by rfl⟩ : syracuseStep 18965603 = 28448405) B28448405
theorem B12643735 : Blo 1995435 12643735 := bstep (se 1 (by rfl) ⟨9482801, by rfl⟩ : syracuseStep 12643735 = 18965603) B18965603
theorem B16858313 : Blo 1995435 16858313 := bstep (se 2 (by rfl) ⟨6321867, by rfl⟩ : syracuseStep 16858313 = 12643735) B12643735
theorem B11238875 : Blo 1995435 11238875 := bstep (se 1 (by rfl) ⟨8429156, by rfl⟩ : syracuseStep 11238875 = 16858313) B16858313
theorem B7492583 : Blo 1995435 7492583 := bstep (se 1 (by rfl) ⟨5619437, by rfl⟩ : syracuseStep 7492583 = 11238875) B11238875
theorem B4995055 : Blo 1995435 4995055 := bstep (se 1 (by rfl) ⟨3746291, by rfl⟩ : syracuseStep 4995055 = 7492583) B7492583
theorem B6660073 : Blo 1995435 6660073 := bstep (se 2 (by rfl) ⟨2497527, by rfl⟩ : syracuseStep 6660073 = 4995055) B4995055
theorem B8880097 : Blo 1995435 8880097 := bstep (se 2 (by rfl) ⟨3330036, by rfl⟩ : syracuseStep 8880097 = 6660073) B6660073
theorem B11840129 : Blo 1995435 11840129 := bstep (se 2 (by rfl) ⟨4440048, by rfl⟩ : syracuseStep 11840129 = 8880097) B8880097
theorem B126294709 : Blo 1995435 126294709 := bstep (se 5 (by rfl) ⟨5920064, by rfl⟩ : syracuseStep 126294709 = 11840129) B11840129
theorem B168392945 : Blo 1995435 168392945 := bstep (se 2 (by rfl) ⟨63147354, by rfl⟩ : syracuseStep 168392945 = 126294709) B126294709
theorem B112261963 : Blo 1995435 112261963 := bstep (se 1 (by rfl) ⟨84196472, by rfl⟩ : syracuseStep 112261963 = 168392945) B168392945
theorem B149682617 : Blo 1995435 149682617 := bstep (se 2 (by rfl) ⟨56130981, by rfl⟩ : syracuseStep 149682617 = 112261963) B112261963
theorem B99788411 : Blo 1995435 99788411 := bstep (se 1 (by rfl) ⟨74841308, by rfl⟩ : syracuseStep 99788411 = 149682617) B149682617
theorem B66525607 : Blo 1995435 66525607 := bstep (se 1 (by rfl) ⟨49894205, by rfl⟩ : syracuseStep 66525607 = 99788411) B99788411
theorem B354803237 : Blo 1995435 354803237 := bstep (se 4 (by rfl) ⟨33262803, by rfl⟩ : syracuseStep 354803237 = 66525607) B66525607
theorem B236535491 : Blo 1995435 236535491 := bstep (se 1 (by rfl) ⟨177401618, by rfl⟩ : syracuseStep 236535491 = 354803237) B354803237
theorem B157690327 : Blo 1995435 157690327 := bstep (se 1 (by rfl) ⟨118267745, by rfl⟩ : syracuseStep 157690327 = 236535491) B236535491
theorem B210253769 : Blo 1995435 210253769 := bstep (se 2 (by rfl) ⟨78845163, by rfl⟩ : syracuseStep 210253769 = 157690327) B157690327
theorem B140169179 : Blo 1995435 140169179 := bstep (se 1 (by rfl) ⟨105126884, by rfl⟩ : syracuseStep 140169179 = 210253769) B210253769
theorem B93446119 : Blo 1995435 93446119 := bstep (se 1 (by rfl) ⟨70084589, by rfl⟩ : syracuseStep 93446119 = 140169179) B140169179
theorem B498379301 : Blo 1995435 498379301 := bstep (se 4 (by rfl) ⟨46723059, by rfl⟩ : syracuseStep 498379301 = 93446119) B93446119
theorem B332252867 : Blo 1995435 332252867 := bstep (se 1 (by rfl) ⟨249189650, by rfl⟩ : syracuseStep 332252867 = 498379301) B498379301
theorem B886007645 : Blo 1995435 886007645 := bstep (se 3 (by rfl) ⟨166126433, by rfl⟩ : syracuseStep 886007645 = 332252867) B332252867
theorem B590671763 : Blo 1995435 590671763 := bstep (se 1 (by rfl) ⟨443003822, by rfl⟩ : syracuseStep 590671763 = 886007645) B886007645
theorem B393781175 : Blo 1995435 393781175 := bstep (se 1 (by rfl) ⟨295335881, by rfl⟩ : syracuseStep 393781175 = 590671763) B590671763
theorem B262520783 : Blo 1995435 262520783 := bstep (se 1 (by rfl) ⟨196890587, by rfl⟩ : syracuseStep 262520783 = 393781175) B393781175
theorem B175013855 : Blo 1995435 175013855 := bstep (se 1 (by rfl) ⟨131260391, by rfl⟩ : syracuseStep 175013855 = 262520783) B262520783
theorem B116675903 : Blo 1995435 116675903 := bstep (se 1 (by rfl) ⟨87506927, by rfl⟩ : syracuseStep 116675903 = 175013855) B175013855
theorem B77783935 : Blo 1995435 77783935 := bstep (se 1 (by rfl) ⟨58337951, by rfl⟩ : syracuseStep 77783935 = 116675903) B116675903
theorem B103711913 : Blo 1995435 103711913 := bstep (se 2 (by rfl) ⟨38891967, by rfl⟩ : syracuseStep 103711913 = 77783935) B77783935
theorem B69141275 : Blo 1995435 69141275 := bstep (se 1 (by rfl) ⟨51855956, by rfl⟩ : syracuseStep 69141275 = 103711913) B103711913
theorem B46094183 : Blo 1995435 46094183 := bstep (se 1 (by rfl) ⟨34570637, by rfl⟩ : syracuseStep 46094183 = 69141275) B69141275
theorem B30729455 : Blo 1995435 30729455 := bstep (se 1 (by rfl) ⟨23047091, by rfl⟩ : syracuseStep 30729455 = 46094183) B46094183
theorem B20486303 : Blo 1995435 20486303 := bstep (se 1 (by rfl) ⟨15364727, by rfl⟩ : syracuseStep 20486303 = 30729455) B30729455
theorem B13657535 : Blo 1995435 13657535 := bstep (se 1 (by rfl) ⟨10243151, by rfl⟩ : syracuseStep 13657535 = 20486303) B20486303
theorem B9105023 : Blo 1995435 9105023 := bstep (se 1 (by rfl) ⟨6828767, by rfl⟩ : syracuseStep 9105023 = 13657535) B13657535
theorem B6070015 : Blo 1995435 6070015 := bstep (se 1 (by rfl) ⟨4552511, by rfl⟩ : syracuseStep 6070015 = 9105023) B9105023
theorem B8093353 : Blo 1995435 8093353 := bstep (se 2 (by rfl) ⟨3035007, by rfl⟩ : syracuseStep 8093353 = 6070015) B6070015
theorem B10791137 : Blo 1995435 10791137 := bstep (se 2 (by rfl) ⟨4046676, by rfl⟩ : syracuseStep 10791137 = 8093353) B8093353
theorem B7194091 : Blo 1995435 7194091 := bstep (se 1 (by rfl) ⟨5395568, by rfl⟩ : syracuseStep 7194091 = 10791137) B10791137
theorem B9592121 : Blo 1995435 9592121 := bstep (se 2 (by rfl) ⟨3597045, by rfl⟩ : syracuseStep 9592121 = 7194091) B7194091
theorem B6394747 : Blo 1995435 6394747 := bstep (se 1 (by rfl) ⟨4796060, by rfl⟩ : syracuseStep 6394747 = 9592121) B9592121
theorem B8526329 : Blo 1995435 8526329 := bstep (se 2 (by rfl) ⟨3197373, by rfl⟩ : syracuseStep 8526329 = 6394747) B6394747
theorem B5684219 : Blo 1995435 5684219 := bstep (se 1 (by rfl) ⟨4263164, by rfl⟩ : syracuseStep 5684219 = 8526329) B8526329
theorem B3789479 : Blo 1995435 3789479 := bstep (se 1 (by rfl) ⟨2842109, by rfl⟩ : syracuseStep 3789479 = 5684219) B5684219
theorem B2526319 : Blo 1995435 2526319 := bstep (se 1 (by rfl) ⟨1894739, by rfl⟩ : syracuseStep 2526319 = 3789479) B3789479
theorem B3368425 : Blo 1995435 3368425 := bstep (se 2 (by rfl) ⟨1263159, by rfl⟩ : syracuseStep 3368425 = 2526319) B2526319
theorem B4491233 : Blo 1995435 4491233 := bstep (se 2 (by rfl) ⟨1684212, by rfl⟩ : syracuseStep 4491233 = 3368425) B3368425
theorem B2994155 : Blo 1995435 2994155 := bstep (se 1 (by rfl) ⟨2245616, by rfl⟩ : syracuseStep 2994155 = 4491233) B4491233
theorem B1996103 : Blo 1995435 1996103 := bstep (se 1 (by rfl) ⟨1497077, by rfl⟩ : syracuseStep 1996103 = 2994155) B2994155
theorem B2245621 : Blo 1995435 2245621 := bbase (se 5 (by rfl) ⟨105263, by rfl⟩ : syracuseStep 2245621 = 210527) (by norm_num)
theorem B2994161 : Blo 1995435 2994161 := bstep (se 2 (by rfl) ⟨1122810, by rfl⟩ : syracuseStep 2994161 = 2245621) B2245621
theorem B1996107 : Blo 1995435 1996107 := bstep (se 1 (by rfl) ⟨1497080, by rfl⟩ : syracuseStep 1996107 = 2994161) B2994161
theorem B2526329 : Blo 1995435 2526329 := bbase (se 2 (by rfl) ⟨947373, by rfl⟩ : syracuseStep 2526329 = 1894747) (by norm_num)
theorem B6736877 : Blo 1995435 6736877 := bstep (se 3 (by rfl) ⟨1263164, by rfl⟩ : syracuseStep 6736877 = 2526329) B2526329
theorem B4491251 : Blo 1995435 4491251 := bstep (se 1 (by rfl) ⟨3368438, by rfl⟩ : syracuseStep 4491251 = 6736877) B6736877
theorem B2994167 : Blo 1995435 2994167 := bstep (se 1 (by rfl) ⟨2245625, by rfl⟩ : syracuseStep 2994167 = 4491251) B4491251
theorem B1996111 : Blo 1995435 1996111 := bstep (se 1 (by rfl) ⟨1497083, by rfl⟩ : syracuseStep 1996111 = 2994167) B2994167
theorem B2994173 : Blo 1995435 2994173 := bbase (se 3 (by rfl) ⟨561407, by rfl⟩ : syracuseStep 2994173 = 1122815) (by norm_num)
theorem B1996115 : Blo 1995435 1996115 := bstep (se 1 (by rfl) ⟨1497086, by rfl⟩ : syracuseStep 1996115 = 2994173) B2994173
theorem B4491269 : Blo 1995435 4491269 := bbase (se 4 (by rfl) ⟨421056, by rfl⟩ : syracuseStep 4491269 = 842113) (by norm_num)
theorem B2994179 : Blo 1995435 2994179 := bstep (se 1 (by rfl) ⟨2245634, by rfl⟩ : syracuseStep 2994179 = 4491269) B4491269
theorem B1996119 : Blo 1995435 1996119 := bstep (se 1 (by rfl) ⟨1497089, by rfl⟩ : syracuseStep 1996119 = 2994179) B2994179
theorem B3789517 : Blo 1995435 3789517 := bbase (se 3 (by rfl) ⟨710534, by rfl⟩ : syracuseStep 3789517 = 1421069) (by norm_num)
theorem B5052689 : Blo 1995435 5052689 := bstep (se 2 (by rfl) ⟨1894758, by rfl⟩ : syracuseStep 5052689 = 3789517) B3789517
theorem B3368459 : Blo 1995435 3368459 := bstep (se 1 (by rfl) ⟨2526344, by rfl⟩ : syracuseStep 3368459 = 5052689) B5052689
theorem B2245639 : Blo 1995435 2245639 := bstep (se 1 (by rfl) ⟨1684229, by rfl⟩ : syracuseStep 2245639 = 3368459) B3368459
theorem B2994185 : Blo 1995435 2994185 := bstep (se 2 (by rfl) ⟨1122819, by rfl⟩ : syracuseStep 2994185 = 2245639) B2245639
theorem B1996123 : Blo 1995435 1996123 := bstep (se 1 (by rfl) ⟨1497092, by rfl⟩ : syracuseStep 1996123 = 2994185) B2994185
theorem B10105397 : Blo 1995435 10105397 := bbase (se 5 (by rfl) ⟨473690, by rfl⟩ : syracuseStep 10105397 = 947381) (by norm_num)
theorem B6736931 : Blo 1995435 6736931 := bstep (se 1 (by rfl) ⟨5052698, by rfl⟩ : syracuseStep 6736931 = 10105397) B10105397
theorem B4491287 : Blo 1995435 4491287 := bstep (se 1 (by rfl) ⟨3368465, by rfl⟩ : syracuseStep 4491287 = 6736931) B6736931
theorem B2994191 : Blo 1995435 2994191 := bstep (se 1 (by rfl) ⟨2245643, by rfl⟩ : syracuseStep 2994191 = 4491287) B4491287
theorem B1996127 : Blo 1995435 1996127 := bstep (se 1 (by rfl) ⟨1497095, by rfl⟩ : syracuseStep 1996127 = 2994191) B2994191
theorem B2994197 : Blo 1995435 2994197 := bbase (se 6 (by rfl) ⟨70176, by rfl⟩ : syracuseStep 2994197 = 140353) (by norm_num)
theorem B1996131 : Blo 1995435 1996131 := bstep (se 1 (by rfl) ⟨1497098, by rfl⟩ : syracuseStep 1996131 = 2994197) B2994197
theorem B4046741 : Blo 1995435 4046741 := bbase (se 6 (by rfl) ⟨94845, by rfl⟩ : syracuseStep 4046741 = 189691) (by norm_num)
theorem B2697827 : Blo 1995435 2697827 := bstep (se 1 (by rfl) ⟨2023370, by rfl⟩ : syracuseStep 2697827 = 4046741) B4046741
theorem B7194205 : Blo 1995435 7194205 := bstep (se 3 (by rfl) ⟨1348913, by rfl⟩ : syracuseStep 7194205 = 2697827) B2697827
theorem B9592273 : Blo 1995435 9592273 := bstep (se 2 (by rfl) ⟨3597102, by rfl⟩ : syracuseStep 9592273 = 7194205) B7194205
theorem B12789697 : Blo 1995435 12789697 := bstep (se 2 (by rfl) ⟨4796136, by rfl⟩ : syracuseStep 12789697 = 9592273) B9592273
theorem B17052929 : Blo 1995435 17052929 := bstep (se 2 (by rfl) ⟨6394848, by rfl⟩ : syracuseStep 17052929 = 12789697) B12789697
theorem B11368619 : Blo 1995435 11368619 := bstep (se 1 (by rfl) ⟨8526464, by rfl⟩ : syracuseStep 11368619 = 17052929) B17052929
theorem B7579079 : Blo 1995435 7579079 := bstep (se 1 (by rfl) ⟨5684309, by rfl⟩ : syracuseStep 7579079 = 11368619) B11368619
theorem B5052719 : Blo 1995435 5052719 := bstep (se 1 (by rfl) ⟨3789539, by rfl⟩ : syracuseStep 5052719 = 7579079) B7579079
theorem B3368479 : Blo 1995435 3368479 := bstep (se 1 (by rfl) ⟨2526359, by rfl⟩ : syracuseStep 3368479 = 5052719) B5052719
theorem B4491305 : Blo 1995435 4491305 := bstep (se 2 (by rfl) ⟨1684239, by rfl⟩ : syracuseStep 4491305 = 3368479) B3368479
theorem B2994203 : Blo 1995435 2994203 := bstep (se 1 (by rfl) ⟨2245652, by rfl⟩ : syracuseStep 2994203 = 4491305) B4491305
theorem B1996135 : Blo 1995435 1996135 := bstep (se 1 (by rfl) ⟨1497101, by rfl⟩ : syracuseStep 1996135 = 2994203) B2994203
theorem B2245657 : Blo 1995435 2245657 := bbase (se 2 (by rfl) ⟨842121, by rfl⟩ : syracuseStep 2245657 = 1684243) (by norm_num)
theorem B2994209 : Blo 1995435 2994209 := bstep (se 2 (by rfl) ⟨1122828, by rfl⟩ : syracuseStep 2994209 = 2245657) B2245657
theorem B1996139 : Blo 1995435 1996139 := bstep (se 1 (by rfl) ⟨1497104, by rfl⟩ : syracuseStep 1996139 = 2994209) B2994209
theorem B7579109 : Blo 1995435 7579109 := bbase (se 4 (by rfl) ⟨710541, by rfl⟩ : syracuseStep 7579109 = 1421083) (by norm_num)
theorem B5052739 : Blo 1995435 5052739 := bstep (se 1 (by rfl) ⟨3789554, by rfl⟩ : syracuseStep 5052739 = 7579109) B7579109
theorem B6736985 : Blo 1995435 6736985 := bstep (se 2 (by rfl) ⟨2526369, by rfl⟩ : syracuseStep 6736985 = 5052739) B5052739
theorem B4491323 : Blo 1995435 4491323 := bstep (se 1 (by rfl) ⟨3368492, by rfl⟩ : syracuseStep 4491323 = 6736985) B6736985
theorem B2994215 : Blo 1995435 2994215 := bstep (se 1 (by rfl) ⟨2245661, by rfl⟩ : syracuseStep 2994215 = 4491323) B4491323
theorem B1996143 : Blo 1995435 1996143 := bstep (se 1 (by rfl) ⟨1497107, by rfl⟩ : syracuseStep 1996143 = 2994215) B2994215
theorem B2994221 : Blo 1995435 2994221 := bbase (se 3 (by rfl) ⟨561416, by rfl⟩ : syracuseStep 2994221 = 1122833) (by norm_num)
theorem B1996147 : Blo 1995435 1996147 := bstep (se 1 (by rfl) ⟨1497110, by rfl⟩ : syracuseStep 1996147 = 2994221) B2994221
theorem B4491341 : Blo 1995435 4491341 := bbase (se 3 (by rfl) ⟨842126, by rfl⟩ : syracuseStep 4491341 = 1684253) (by norm_num)
theorem B2994227 : Blo 1995435 2994227 := bstep (se 1 (by rfl) ⟨2245670, by rfl⟩ : syracuseStep 2994227 = 4491341) B4491341
theorem B1996151 : Blo 1995435 1996151 := bstep (se 1 (by rfl) ⟨1497113, by rfl⟩ : syracuseStep 1996151 = 2994227) B2994227
theorem B2526385 : Blo 1995435 2526385 := bbase (se 2 (by rfl) ⟨947394, by rfl⟩ : syracuseStep 2526385 = 1894789) (by norm_num)
theorem B3368513 : Blo 1995435 3368513 := bstep (se 2 (by rfl) ⟨1263192, by rfl⟩ : syracuseStep 3368513 = 2526385) B2526385
theorem B2245675 : Blo 1995435 2245675 := bstep (se 1 (by rfl) ⟨1684256, by rfl⟩ : syracuseStep 2245675 = 3368513) B3368513
theorem B2994233 : Blo 1995435 2994233 := bstep (se 2 (by rfl) ⟨1122837, by rfl⟩ : syracuseStep 2994233 = 2245675) B2245675
theorem B1996155 : Blo 1995435 1996155 := bstep (se 1 (by rfl) ⟨1497116, by rfl⟩ : syracuseStep 1996155 = 2994233) B2994233
theorem B2398097 : Blo 1995435 2398097 := bbase (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) (by norm_num)
theorem B6394925 : Blo 1995435 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B4263283 : Blo 1995435 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B22737509 : Blo 1995435 22737509 := bstep (se 4 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 22737509 = 4263283) B4263283
theorem B15158339 : Blo 1995435 15158339 := bstep (se 1 (by rfl) ⟨11368754, by rfl⟩ : syracuseStep 15158339 = 22737509) B22737509
theorem B10105559 : Blo 1995435 10105559 := bstep (se 1 (by rfl) ⟨7579169, by rfl⟩ : syracuseStep 10105559 = 15158339) B15158339
theorem B6737039 : Blo 1995435 6737039 := bstep (se 1 (by rfl) ⟨5052779, by rfl⟩ : syracuseStep 6737039 = 10105559) B10105559
theorem B4491359 : Blo 1995435 4491359 := bstep (se 1 (by rfl) ⟨3368519, by rfl⟩ : syracuseStep 4491359 = 6737039) B6737039
theorem B2994239 : Blo 1995435 2994239 := bstep (se 1 (by rfl) ⟨2245679, by rfl⟩ : syracuseStep 2994239 = 4491359) B4491359
theorem B1996159 : Blo 1995435 1996159 := bstep (se 1 (by rfl) ⟨1497119, by rfl⟩ : syracuseStep 1996159 = 2994239) B2994239
theorem B2994245 : Blo 1995435 2994245 := bbase (se 4 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 2994245 = 561421) (by norm_num)
theorem B1996163 : Blo 1995435 1996163 := bstep (se 1 (by rfl) ⟨1497122, by rfl⟩ : syracuseStep 1996163 = 2994245) B2994245
theorem B3368533 : Blo 1995435 3368533 := bbase (se 8 (by rfl) ⟨19737, by rfl⟩ : syracuseStep 3368533 = 39475) (by norm_num)
theorem B4491377 : Blo 1995435 4491377 := bstep (se 2 (by rfl) ⟨1684266, by rfl⟩ : syracuseStep 4491377 = 3368533) B3368533
theorem B2994251 : Blo 1995435 2994251 := bstep (se 1 (by rfl) ⟨2245688, by rfl⟩ : syracuseStep 2994251 = 4491377) B4491377
theorem B1996167 : Blo 1995435 1996167 := bstep (se 1 (by rfl) ⟨1497125, by rfl⟩ : syracuseStep 1996167 = 2994251) B2994251
theorem B2245693 : Blo 1995435 2245693 := bbase (se 3 (by rfl) ⟨421067, by rfl⟩ : syracuseStep 2245693 = 842135) (by norm_num)
theorem B2994257 : Blo 1995435 2994257 := bstep (se 2 (by rfl) ⟨1122846, by rfl⟩ : syracuseStep 2994257 = 2245693) B2245693
theorem B1996171 : Blo 1995435 1996171 := bstep (se 1 (by rfl) ⟨1497128, by rfl⟩ : syracuseStep 1996171 = 2994257) B2994257
theorem B6737093 : Blo 1995435 6737093 := bbase (se 4 (by rfl) ⟨631602, by rfl⟩ : syracuseStep 6737093 = 1263205) (by norm_num)
theorem B4491395 : Blo 1995435 4491395 := bstep (se 1 (by rfl) ⟨3368546, by rfl⟩ : syracuseStep 4491395 = 6737093) B6737093
theorem B2994263 : Blo 1995435 2994263 := bstep (se 1 (by rfl) ⟨2245697, by rfl⟩ : syracuseStep 2994263 = 4491395) B4491395
theorem B1996175 : Blo 1995435 1996175 := bstep (se 1 (by rfl) ⟨1497131, by rfl⟩ : syracuseStep 1996175 = 2994263) B2994263
theorem B2994269 : Blo 1995435 2994269 := bbase (se 3 (by rfl) ⟨561425, by rfl⟩ : syracuseStep 2994269 = 1122851) (by norm_num)
theorem B1996179 : Blo 1995435 1996179 := bstep (se 1 (by rfl) ⟨1497134, by rfl⟩ : syracuseStep 1996179 = 2994269) B2994269
theorem B4491413 : Blo 1995435 4491413 := bbase (se 6 (by rfl) ⟨105267, by rfl⟩ : syracuseStep 4491413 = 210535) (by norm_num)
theorem B2994275 : Blo 1995435 2994275 := bstep (se 1 (by rfl) ⟨2245706, by rfl⟩ : syracuseStep 2994275 = 4491413) B4491413
theorem B1996183 : Blo 1995435 1996183 := bstep (se 1 (by rfl) ⟨1497137, by rfl⟩ : syracuseStep 1996183 = 2994275) B2994275
theorem B2842229 : Blo 1995435 2842229 := bbase (se 5 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 2842229 = 266459) (by norm_num)
theorem B7579277 : Blo 1995435 7579277 := bstep (se 3 (by rfl) ⟨1421114, by rfl⟩ : syracuseStep 7579277 = 2842229) B2842229
theorem B5052851 : Blo 1995435 5052851 := bstep (se 1 (by rfl) ⟨3789638, by rfl⟩ : syracuseStep 5052851 = 7579277) B7579277
theorem B3368567 : Blo 1995435 3368567 := bstep (se 1 (by rfl) ⟨2526425, by rfl⟩ : syracuseStep 3368567 = 5052851) B5052851
theorem B2245711 : Blo 1995435 2245711 := bstep (se 1 (by rfl) ⟨1684283, by rfl⟩ : syracuseStep 2245711 = 3368567) B3368567
theorem B2994281 : Blo 1995435 2994281 := bstep (se 2 (by rfl) ⟨1122855, by rfl⟩ : syracuseStep 2994281 = 2245711) B2245711
theorem B1996187 : Blo 1995435 1996187 := bstep (se 1 (by rfl) ⟨1497140, by rfl⟩ : syracuseStep 1996187 = 2994281) B2994281
theorem B3414533 : Blo 1995435 3414533 := bbase (se 4 (by rfl) ⟨320112, by rfl⟩ : syracuseStep 3414533 = 640225) (by norm_num)
theorem B9105421 : Blo 1995435 9105421 := bstep (se 3 (by rfl) ⟨1707266, by rfl⟩ : syracuseStep 9105421 = 3414533) B3414533
theorem B12140561 : Blo 1995435 12140561 := bstep (se 2 (by rfl) ⟨4552710, by rfl⟩ : syracuseStep 12140561 = 9105421) B9105421
theorem B32374829 : Blo 1995435 32374829 := bstep (se 3 (by rfl) ⟨6070280, by rfl⟩ : syracuseStep 32374829 = 12140561) B12140561
theorem B21583219 : Blo 1995435 21583219 := bstep (se 1 (by rfl) ⟨16187414, by rfl⟩ : syracuseStep 21583219 = 32374829) B32374829
theorem B28777625 : Blo 1995435 28777625 := bstep (se 2 (by rfl) ⟨10791609, by rfl⟩ : syracuseStep 28777625 = 21583219) B21583219
theorem B19185083 : Blo 1995435 19185083 := bstep (se 1 (by rfl) ⟨14388812, by rfl⟩ : syracuseStep 19185083 = 28777625) B28777625
theorem B12790055 : Blo 1995435 12790055 := bstep (se 1 (by rfl) ⟨9592541, by rfl⟩ : syracuseStep 12790055 = 19185083) B19185083
theorem B8526703 : Blo 1995435 8526703 := bstep (se 1 (by rfl) ⟨6395027, by rfl⟩ : syracuseStep 8526703 = 12790055) B12790055
theorem B11368937 : Blo 1995435 11368937 := bstep (se 2 (by rfl) ⟨4263351, by rfl⟩ : syracuseStep 11368937 = 8526703) B8526703
theorem B7579291 : Blo 1995435 7579291 := bstep (se 1 (by rfl) ⟨5684468, by rfl⟩ : syracuseStep 7579291 = 11368937) B11368937
theorem B10105721 : Blo 1995435 10105721 := bstep (se 2 (by rfl) ⟨3789645, by rfl⟩ : syracuseStep 10105721 = 7579291) B7579291
theorem B6737147 : Blo 1995435 6737147 := bstep (se 1 (by rfl) ⟨5052860, by rfl⟩ : syracuseStep 6737147 = 10105721) B10105721
theorem B4491431 : Blo 1995435 4491431 := bstep (se 1 (by rfl) ⟨3368573, by rfl⟩ : syracuseStep 4491431 = 6737147) B6737147
theorem B2994287 : Blo 1995435 2994287 := bstep (se 1 (by rfl) ⟨2245715, by rfl⟩ : syracuseStep 2994287 = 4491431) B4491431
theorem B1996191 : Blo 1995435 1996191 := bstep (se 1 (by rfl) ⟨1497143, by rfl⟩ : syracuseStep 1996191 = 2994287) B2994287
theorem B2994293 : Blo 1995435 2994293 := bbase (se 5 (by rfl) ⟨140357, by rfl⟩ : syracuseStep 2994293 = 280715) (by norm_num)
theorem B1996195 : Blo 1995435 1996195 := bstep (se 1 (by rfl) ⟨1497146, by rfl⟩ : syracuseStep 1996195 = 2994293) B2994293
theorem B3789661 : Blo 1995435 3789661 := bbase (se 3 (by rfl) ⟨710561, by rfl⟩ : syracuseStep 3789661 = 1421123) (by norm_num)
theorem B5052881 : Blo 1995435 5052881 := bstep (se 2 (by rfl) ⟨1894830, by rfl⟩ : syracuseStep 5052881 = 3789661) B3789661
theorem B3368587 : Blo 1995435 3368587 := bstep (se 1 (by rfl) ⟨2526440, by rfl⟩ : syracuseStep 3368587 = 5052881) B5052881
theorem B4491449 : Blo 1995435 4491449 := bstep (se 2 (by rfl) ⟨1684293, by rfl⟩ : syracuseStep 4491449 = 3368587) B3368587
theorem B2994299 : Blo 1995435 2994299 := bstep (se 1 (by rfl) ⟨2245724, by rfl⟩ : syracuseStep 2994299 = 4491449) B4491449
theorem B1996199 : Blo 1995435 1996199 := bstep (se 1 (by rfl) ⟨1497149, by rfl⟩ : syracuseStep 1996199 = 2994299) B2994299
theorem B2245729 : Blo 1995435 2245729 := bbase (se 2 (by rfl) ⟨842148, by rfl⟩ : syracuseStep 2245729 = 1684297) (by norm_num)
theorem B2994305 : Blo 1995435 2994305 := bstep (se 2 (by rfl) ⟨1122864, by rfl⟩ : syracuseStep 2994305 = 2245729) B2245729
theorem B1996203 : Blo 1995435 1996203 := bstep (se 1 (by rfl) ⟨1497152, by rfl⟩ : syracuseStep 1996203 = 2994305) B2994305
theorem B5052901 : Blo 1995435 5052901 := bbase (se 4 (by rfl) ⟨473709, by rfl⟩ : syracuseStep 5052901 = 947419) (by norm_num)
theorem B6737201 : Blo 1995435 6737201 := bstep (se 2 (by rfl) ⟨2526450, by rfl⟩ : syracuseStep 6737201 = 5052901) B5052901
theorem B4491467 : Blo 1995435 4491467 := bstep (se 1 (by rfl) ⟨3368600, by rfl⟩ : syracuseStep 4491467 = 6737201) B6737201
theorem B2994311 : Blo 1995435 2994311 := bstep (se 1 (by rfl) ⟨2245733, by rfl⟩ : syracuseStep 2994311 = 4491467) B4491467
theorem B1996207 : Blo 1995435 1996207 := bstep (se 1 (by rfl) ⟨1497155, by rfl⟩ : syracuseStep 1996207 = 2994311) B2994311
theorem B2994317 : Blo 1995435 2994317 := bbase (se 3 (by rfl) ⟨561434, by rfl⟩ : syracuseStep 2994317 = 1122869) (by norm_num)
theorem B1996211 : Blo 1995435 1996211 := bstep (se 1 (by rfl) ⟨1497158, by rfl⟩ : syracuseStep 1996211 = 2994317) B2994317
theorem B4491485 : Blo 1995435 4491485 := bbase (se 3 (by rfl) ⟨842153, by rfl⟩ : syracuseStep 4491485 = 1684307) (by norm_num)
theorem B2994323 : Blo 1995435 2994323 := bstep (se 1 (by rfl) ⟨2245742, by rfl⟩ : syracuseStep 2994323 = 4491485) B4491485
theorem B1996215 : Blo 1995435 1996215 := bstep (se 1 (by rfl) ⟨1497161, by rfl⟩ : syracuseStep 1996215 = 2994323) B2994323
theorem B3368621 : Blo 1995435 3368621 := bbase (se 3 (by rfl) ⟨631616, by rfl⟩ : syracuseStep 3368621 = 1263233) (by norm_num)
theorem B2245747 : Blo 1995435 2245747 := bstep (se 1 (by rfl) ⟨1684310, by rfl⟩ : syracuseStep 2245747 = 3368621) B3368621
theorem B2994329 : Blo 1995435 2994329 := bstep (se 2 (by rfl) ⟨1122873, by rfl⟩ : syracuseStep 2994329 = 2245747) B2245747
theorem B1996219 : Blo 1995435 1996219 := bstep (se 1 (by rfl) ⟨1497164, by rfl⟩ : syracuseStep 1996219 = 2994329) B2994329
theorem B5762117 : Blo 1995435 5762117 := bbase (se 4 (by rfl) ⟨540198, by rfl⟩ : syracuseStep 5762117 = 1080397) (by norm_num)
theorem B15365645 : Blo 1995435 15365645 := bstep (se 3 (by rfl) ⟨2881058, by rfl⟩ : syracuseStep 15365645 = 5762117) B5762117
theorem B10243763 : Blo 1995435 10243763 := bstep (se 1 (by rfl) ⟨7682822, by rfl⟩ : syracuseStep 10243763 = 15365645) B15365645
theorem B6829175 : Blo 1995435 6829175 := bstep (se 1 (by rfl) ⟨5121881, by rfl⟩ : syracuseStep 6829175 = 10243763) B10243763
theorem B4552783 : Blo 1995435 4552783 := bstep (se 1 (by rfl) ⟨3414587, by rfl⟩ : syracuseStep 4552783 = 6829175) B6829175
theorem B97126037 : Blo 1995435 97126037 := bstep (se 6 (by rfl) ⟨2276391, by rfl⟩ : syracuseStep 97126037 = 4552783) B4552783
theorem B64750691 : Blo 1995435 64750691 := bstep (se 1 (by rfl) ⟨48563018, by rfl⟩ : syracuseStep 64750691 = 97126037) B97126037
theorem B43167127 : Blo 1995435 43167127 := bstep (se 1 (by rfl) ⟨32375345, by rfl⟩ : syracuseStep 43167127 = 64750691) B64750691
theorem B57556169 : Blo 1995435 57556169 := bstep (se 2 (by rfl) ⟨21583563, by rfl⟩ : syracuseStep 57556169 = 43167127) B43167127
theorem B38370779 : Blo 1995435 38370779 := bstep (se 1 (by rfl) ⟨28778084, by rfl⟩ : syracuseStep 38370779 = 57556169) B57556169
theorem B25580519 : Blo 1995435 25580519 := bstep (se 1 (by rfl) ⟨19185389, by rfl⟩ : syracuseStep 25580519 = 38370779) B38370779
theorem B17053679 : Blo 1995435 17053679 := bstep (se 1 (by rfl) ⟨12790259, by rfl⟩ : syracuseStep 17053679 = 25580519) B25580519
theorem B11369119 : Blo 1995435 11369119 := bstep (se 1 (by rfl) ⟨8526839, by rfl⟩ : syracuseStep 11369119 = 17053679) B17053679
theorem B15158825 : Blo 1995435 15158825 := bstep (se 2 (by rfl) ⟨5684559, by rfl⟩ : syracuseStep 15158825 = 11369119) B11369119
theorem B10105883 : Blo 1995435 10105883 := bstep (se 1 (by rfl) ⟨7579412, by rfl⟩ : syracuseStep 10105883 = 15158825) B15158825
theorem B6737255 : Blo 1995435 6737255 := bstep (se 1 (by rfl) ⟨5052941, by rfl⟩ : syracuseStep 6737255 = 10105883) B10105883
theorem B4491503 : Blo 1995435 4491503 := bstep (se 1 (by rfl) ⟨3368627, by rfl⟩ : syracuseStep 4491503 = 6737255) B6737255
theorem B2994335 : Blo 1995435 2994335 := bstep (se 1 (by rfl) ⟨2245751, by rfl⟩ : syracuseStep 2994335 = 4491503) B4491503
theorem B1996223 : Blo 1995435 1996223 := bstep (se 1 (by rfl) ⟨1497167, by rfl⟩ : syracuseStep 1996223 = 2994335) B2994335
theorem B2994341 : Blo 1995435 2994341 := bbase (se 4 (by rfl) ⟨280719, by rfl⟩ : syracuseStep 2994341 = 561439) (by norm_num)
theorem B1996227 : Blo 1995435 1996227 := bstep (se 1 (by rfl) ⟨1497170, by rfl⟩ : syracuseStep 1996227 = 2994341) B2994341
theorem B2526481 : Blo 1995435 2526481 := bbase (se 2 (by rfl) ⟨947430, by rfl⟩ : syracuseStep 2526481 = 1894861) (by norm_num)
theorem B3368641 : Blo 1995435 3368641 := bstep (se 2 (by rfl) ⟨1263240, by rfl⟩ : syracuseStep 3368641 = 2526481) B2526481
theorem B4491521 : Blo 1995435 4491521 := bstep (se 2 (by rfl) ⟨1684320, by rfl⟩ : syracuseStep 4491521 = 3368641) B3368641
theorem B2994347 : Blo 1995435 2994347 := bstep (se 1 (by rfl) ⟨2245760, by rfl⟩ : syracuseStep 2994347 = 4491521) B4491521
theorem B1996231 : Blo 1995435 1996231 := bstep (se 1 (by rfl) ⟨1497173, by rfl⟩ : syracuseStep 1996231 = 2994347) B2994347
theorem B2245765 : Blo 1995435 2245765 := bbase (se 4 (by rfl) ⟨210540, by rfl⟩ : syracuseStep 2245765 = 421081) (by norm_num)
theorem B2994353 : Blo 1995435 2994353 := bstep (se 2 (by rfl) ⟨1122882, by rfl⟩ : syracuseStep 2994353 = 2245765) B2245765
theorem B1996235 : Blo 1995435 1996235 := bstep (se 1 (by rfl) ⟨1497176, by rfl⟩ : syracuseStep 1996235 = 2994353) B2994353
theorem B9229877 : Blo 1995435 9229877 := bbase (se 5 (by rfl) ⟨432650, by rfl⟩ : syracuseStep 9229877 = 865301) (by norm_num)
theorem B6153251 : Blo 1995435 6153251 := bstep (se 1 (by rfl) ⟨4614938, by rfl⟩ : syracuseStep 6153251 = 9229877) B9229877
theorem B16408669 : Blo 1995435 16408669 := bstep (se 3 (by rfl) ⟨3076625, by rfl⟩ : syracuseStep 16408669 = 6153251) B6153251
theorem B21878225 : Blo 1995435 21878225 := bstep (se 2 (by rfl) ⟨8204334, by rfl⟩ : syracuseStep 21878225 = 16408669) B16408669
theorem B14585483 : Blo 1995435 14585483 := bstep (se 1 (by rfl) ⟨10939112, by rfl⟩ : syracuseStep 14585483 = 21878225) B21878225
theorem B9723655 : Blo 1995435 9723655 := bstep (se 1 (by rfl) ⟨7292741, by rfl⟩ : syracuseStep 9723655 = 14585483) B14585483
theorem B12964873 : Blo 1995435 12964873 := bstep (se 2 (by rfl) ⟨4861827, by rfl⟩ : syracuseStep 12964873 = 9723655) B9723655
theorem B17286497 : Blo 1995435 17286497 := bstep (se 2 (by rfl) ⟨6482436, by rfl⟩ : syracuseStep 17286497 = 12964873) B12964873
theorem B11524331 : Blo 1995435 11524331 := bstep (se 1 (by rfl) ⟨8643248, by rfl⟩ : syracuseStep 11524331 = 17286497) B17286497
theorem B7682887 : Blo 1995435 7682887 := bstep (se 1 (by rfl) ⟨5762165, by rfl⟩ : syracuseStep 7682887 = 11524331) B11524331
theorem B10243849 : Blo 1995435 10243849 := bstep (se 2 (by rfl) ⟨3841443, by rfl⟩ : syracuseStep 10243849 = 7682887) B7682887
theorem B13658465 : Blo 1995435 13658465 := bstep (se 2 (by rfl) ⟨5121924, by rfl⟩ : syracuseStep 13658465 = 10243849) B10243849
theorem B9105643 : Blo 1995435 9105643 := bstep (se 1 (by rfl) ⟨6829232, by rfl⟩ : syracuseStep 9105643 = 13658465) B13658465
theorem B12140857 : Blo 1995435 12140857 := bstep (se 2 (by rfl) ⟨4552821, by rfl⟩ : syracuseStep 12140857 = 9105643) B9105643
theorem B16187809 : Blo 1995435 16187809 := bstep (se 2 (by rfl) ⟨6070428, by rfl⟩ : syracuseStep 16187809 = 12140857) B12140857
theorem B21583745 : Blo 1995435 21583745 := bstep (se 2 (by rfl) ⟨8093904, by rfl⟩ : syracuseStep 21583745 = 16187809) B16187809
theorem B14389163 : Blo 1995435 14389163 := bstep (se 1 (by rfl) ⟨10791872, by rfl⟩ : syracuseStep 14389163 = 21583745) B21583745
theorem B9592775 : Blo 1995435 9592775 := bstep (se 1 (by rfl) ⟨7194581, by rfl⟩ : syracuseStep 9592775 = 14389163) B14389163
theorem B6395183 : Blo 1995435 6395183 := bstep (se 1 (by rfl) ⟨4796387, by rfl⟩ : syracuseStep 6395183 = 9592775) B9592775
theorem B4263455 : Blo 1995435 4263455 := bstep (se 1 (by rfl) ⟨3197591, by rfl⟩ : syracuseStep 4263455 = 6395183) B6395183
theorem B2842303 : Blo 1995435 2842303 := bstep (se 1 (by rfl) ⟨2131727, by rfl⟩ : syracuseStep 2842303 = 4263455) B4263455
theorem B3789737 : Blo 1995435 3789737 := bstep (se 2 (by rfl) ⟨1421151, by rfl⟩ : syracuseStep 3789737 = 2842303) B2842303
theorem B2526491 : Blo 1995435 2526491 := bstep (se 1 (by rfl) ⟨1894868, by rfl⟩ : syracuseStep 2526491 = 3789737) B3789737
theorem B6737309 : Blo 1995435 6737309 := bstep (se 3 (by rfl) ⟨1263245, by rfl⟩ : syracuseStep 6737309 = 2526491) B2526491
theorem B4491539 : Blo 1995435 4491539 := bstep (se 1 (by rfl) ⟨3368654, by rfl⟩ : syracuseStep 4491539 = 6737309) B6737309
theorem B2994359 : Blo 1995435 2994359 := bstep (se 1 (by rfl) ⟨2245769, by rfl⟩ : syracuseStep 2994359 = 4491539) B4491539
theorem B1996239 : Blo 1995435 1996239 := bstep (se 1 (by rfl) ⟨1497179, by rfl⟩ : syracuseStep 1996239 = 2994359) B2994359
theorem B2994365 : Blo 1995435 2994365 := bbase (se 3 (by rfl) ⟨561443, by rfl⟩ : syracuseStep 2994365 = 1122887) (by norm_num)
theorem B1996243 : Blo 1995435 1996243 := bstep (se 1 (by rfl) ⟨1497182, by rfl⟩ : syracuseStep 1996243 = 2994365) B2994365
theorem B4491557 : Blo 1995435 4491557 := bbase (se 4 (by rfl) ⟨421083, by rfl⟩ : syracuseStep 4491557 = 842167) (by norm_num)
theorem B2994371 : Blo 1995435 2994371 := bstep (se 1 (by rfl) ⟨2245778, by rfl⟩ : syracuseStep 2994371 = 4491557) B4491557
theorem B1996247 : Blo 1995435 1996247 := bstep (se 1 (by rfl) ⟨1497185, by rfl⟩ : syracuseStep 1996247 = 2994371) B2994371
theorem B5053013 : Blo 1995435 5053013 := bbase (se 8 (by rfl) ⟨29607, by rfl⟩ : syracuseStep 5053013 = 59215) (by norm_num)
theorem B3368675 : Blo 1995435 3368675 := bstep (se 1 (by rfl) ⟨2526506, by rfl⟩ : syracuseStep 3368675 = 5053013) B5053013
theorem B2245783 : Blo 1995435 2245783 := bstep (se 1 (by rfl) ⟨1684337, by rfl⟩ : syracuseStep 2245783 = 3368675) B3368675
theorem B2994377 : Blo 1995435 2994377 := bstep (se 2 (by rfl) ⟨1122891, by rfl⟩ : syracuseStep 2994377 = 2245783) B2245783
theorem B1996251 : Blo 1995435 1996251 := bstep (se 1 (by rfl) ⟨1497188, by rfl⟩ : syracuseStep 1996251 = 2994377) B2994377
theorem B2276429 : Blo 1995435 2276429 := bbase (se 3 (by rfl) ⟨426830, by rfl⟩ : syracuseStep 2276429 = 853661) (by norm_num)
theorem B6070477 : Blo 1995435 6070477 := bstep (se 3 (by rfl) ⟨1138214, by rfl⟩ : syracuseStep 6070477 = 2276429) B2276429
theorem B8093969 : Blo 1995435 8093969 := bstep (se 2 (by rfl) ⟨3035238, by rfl⟩ : syracuseStep 8093969 = 6070477) B6070477
theorem B5395979 : Blo 1995435 5395979 := bstep (se 1 (by rfl) ⟨4046984, by rfl⟩ : syracuseStep 5395979 = 8093969) B8093969
theorem B3597319 : Blo 1995435 3597319 := bstep (se 1 (by rfl) ⟨2697989, by rfl⟩ : syracuseStep 3597319 = 5395979) B5395979
theorem B4796425 : Blo 1995435 4796425 := bstep (se 2 (by rfl) ⟨1798659, by rfl⟩ : syracuseStep 4796425 = 3597319) B3597319
theorem B6395233 : Blo 1995435 6395233 := bstep (se 2 (by rfl) ⟨2398212, by rfl⟩ : syracuseStep 6395233 = 4796425) B4796425
theorem B8526977 : Blo 1995435 8526977 := bstep (se 2 (by rfl) ⟨3197616, by rfl⟩ : syracuseStep 8526977 = 6395233) B6395233
theorem B5684651 : Blo 1995435 5684651 := bstep (se 1 (by rfl) ⟨4263488, by rfl⟩ : syracuseStep 5684651 = 8526977) B8526977
theorem B3789767 : Blo 1995435 3789767 := bstep (se 1 (by rfl) ⟨2842325, by rfl⟩ : syracuseStep 3789767 = 5684651) B5684651
theorem B10106045 : Blo 1995435 10106045 := bstep (se 3 (by rfl) ⟨1894883, by rfl⟩ : syracuseStep 10106045 = 3789767) B3789767
theorem B6737363 : Blo 1995435 6737363 := bstep (se 1 (by rfl) ⟨5053022, by rfl⟩ : syracuseStep 6737363 = 10106045) B10106045
theorem B4491575 : Blo 1995435 4491575 := bstep (se 1 (by rfl) ⟨3368681, by rfl⟩ : syracuseStep 4491575 = 6737363) B6737363
theorem B2994383 : Blo 1995435 2994383 := bstep (se 1 (by rfl) ⟨2245787, by rfl⟩ : syracuseStep 2994383 = 4491575) B4491575
theorem B1996255 : Blo 1995435 1996255 := bstep (se 1 (by rfl) ⟨1497191, by rfl⟩ : syracuseStep 1996255 = 2994383) B2994383
theorem B2994389 : Blo 1995435 2994389 := bbase (se 7 (by rfl) ⟨35090, by rfl⟩ : syracuseStep 2994389 = 70181) (by norm_num)
theorem B1996259 : Blo 1995435 1996259 := bstep (se 1 (by rfl) ⟨1497194, by rfl⟩ : syracuseStep 1996259 = 2994389) B2994389
theorem B2131753 : Blo 1995435 2131753 := bbase (se 2 (by rfl) ⟨799407, by rfl⟩ : syracuseStep 2131753 = 1598815) (by norm_num)
theorem B2842337 : Blo 1995435 2842337 := bstep (se 2 (by rfl) ⟨1065876, by rfl⟩ : syracuseStep 2842337 = 2131753) B2131753
theorem B7579565 : Blo 1995435 7579565 := bstep (se 3 (by rfl) ⟨1421168, by rfl⟩ : syracuseStep 7579565 = 2842337) B2842337
theorem B5053043 : Blo 1995435 5053043 := bstep (se 1 (by rfl) ⟨3789782, by rfl⟩ : syracuseStep 5053043 = 7579565) B7579565
theorem B3368695 : Blo 1995435 3368695 := bstep (se 1 (by rfl) ⟨2526521, by rfl⟩ : syracuseStep 3368695 = 5053043) B5053043
theorem B4491593 : Blo 1995435 4491593 := bstep (se 2 (by rfl) ⟨1684347, by rfl⟩ : syracuseStep 4491593 = 3368695) B3368695
theorem B2994395 : Blo 1995435 2994395 := bstep (se 1 (by rfl) ⟨2245796, by rfl⟩ : syracuseStep 2994395 = 4491593) B4491593
theorem B1996263 : Blo 1995435 1996263 := bstep (se 1 (by rfl) ⟨1497197, by rfl⟩ : syracuseStep 1996263 = 2994395) B2994395
theorem B2245801 : Blo 1995435 2245801 := bbase (se 2 (by rfl) ⟨842175, by rfl⟩ : syracuseStep 2245801 = 1684351) (by norm_num)
theorem B2994401 : Blo 1995435 2994401 := bstep (se 2 (by rfl) ⟨1122900, by rfl⟩ : syracuseStep 2994401 = 2245801) B2245801
theorem B1996267 : Blo 1995435 1996267 := bstep (se 1 (by rfl) ⟨1497200, by rfl⟩ : syracuseStep 1996267 = 2994401) B2994401
theorem B8527045 : Blo 1995435 8527045 := bbase (se 4 (by rfl) ⟨799410, by rfl⟩ : syracuseStep 8527045 = 1598821) (by norm_num)
theorem B11369393 : Blo 1995435 11369393 := bstep (se 2 (by rfl) ⟨4263522, by rfl⟩ : syracuseStep 11369393 = 8527045) B8527045
theorem B7579595 : Blo 1995435 7579595 := bstep (se 1 (by rfl) ⟨5684696, by rfl⟩ : syracuseStep 7579595 = 11369393) B11369393
theorem B5053063 : Blo 1995435 5053063 := bstep (se 1 (by rfl) ⟨3789797, by rfl⟩ : syracuseStep 5053063 = 7579595) B7579595
theorem B6737417 : Blo 1995435 6737417 := bstep (se 2 (by rfl) ⟨2526531, by rfl⟩ : syracuseStep 6737417 = 5053063) B5053063
theorem B4491611 : Blo 1995435 4491611 := bstep (se 1 (by rfl) ⟨3368708, by rfl⟩ : syracuseStep 4491611 = 6737417) B6737417
theorem B2994407 : Blo 1995435 2994407 := bstep (se 1 (by rfl) ⟨2245805, by rfl⟩ : syracuseStep 2994407 = 4491611) B4491611
theorem B1996271 : Blo 1995435 1996271 := bstep (se 1 (by rfl) ⟨1497203, by rfl⟩ : syracuseStep 1996271 = 2994407) B2994407
theorem B2994413 : Blo 1995435 2994413 := bbase (se 3 (by rfl) ⟨561452, by rfl⟩ : syracuseStep 2994413 = 1122905) (by norm_num)
theorem B1996275 : Blo 1995435 1996275 := bstep (se 1 (by rfl) ⟨1497206, by rfl⟩ : syracuseStep 1996275 = 2994413) B2994413
theorem B4491629 : Blo 1995435 4491629 := bbase (se 3 (by rfl) ⟨842180, by rfl⟩ : syracuseStep 4491629 = 1684361) (by norm_num)
theorem B2994419 : Blo 1995435 2994419 := bstep (se 1 (by rfl) ⟨2245814, by rfl⟩ : syracuseStep 2994419 = 4491629) B4491629
theorem B1996279 : Blo 1995435 1996279 := bstep (se 1 (by rfl) ⟨1497209, by rfl⟩ : syracuseStep 1996279 = 2994419) B2994419
theorem B3789821 : Blo 1995435 3789821 := bbase (se 3 (by rfl) ⟨710591, by rfl⟩ : syracuseStep 3789821 = 1421183) (by norm_num)
theorem B2526547 : Blo 1995435 2526547 := bstep (se 1 (by rfl) ⟨1894910, by rfl⟩ : syracuseStep 2526547 = 3789821) B3789821
theorem B3368729 : Blo 1995435 3368729 := bstep (se 2 (by rfl) ⟨1263273, by rfl⟩ : syracuseStep 3368729 = 2526547) B2526547
theorem B2245819 : Blo 1995435 2245819 := bstep (se 1 (by rfl) ⟨1684364, by rfl⟩ : syracuseStep 2245819 = 3368729) B3368729
theorem B2994425 : Blo 1995435 2994425 := bstep (se 2 (by rfl) ⟨1122909, by rfl⟩ : syracuseStep 2994425 = 2245819) B2245819
theorem B1996283 : Blo 1995435 1996283 := bstep (se 1 (by rfl) ⟨1497212, by rfl⟩ : syracuseStep 1996283 = 2994425) B2994425
theorem B4796501 : Blo 1995435 4796501 := bbase (se 8 (by rfl) ⟨28104, by rfl⟩ : syracuseStep 4796501 = 56209) (by norm_num)
theorem B51162677 : Blo 1995435 51162677 := bstep (se 5 (by rfl) ⟨2398250, by rfl⟩ : syracuseStep 51162677 = 4796501) B4796501
theorem B34108451 : Blo 1995435 34108451 := bstep (se 1 (by rfl) ⟨25581338, by rfl⟩ : syracuseStep 34108451 = 51162677) B51162677
theorem B22738967 : Blo 1995435 22738967 := bstep (se 1 (by rfl) ⟨17054225, by rfl⟩ : syracuseStep 22738967 = 34108451) B34108451
theorem B15159311 : Blo 1995435 15159311 := bstep (se 1 (by rfl) ⟨11369483, by rfl⟩ : syracuseStep 15159311 = 22738967) B22738967
theorem B10106207 : Blo 1995435 10106207 := bstep (se 1 (by rfl) ⟨7579655, by rfl⟩ : syracuseStep 10106207 = 15159311) B15159311
theorem B6737471 : Blo 1995435 6737471 := bstep (se 1 (by rfl) ⟨5053103, by rfl⟩ : syracuseStep 6737471 = 10106207) B10106207
theorem B4491647 : Blo 1995435 4491647 := bstep (se 1 (by rfl) ⟨3368735, by rfl⟩ : syracuseStep 4491647 = 6737471) B6737471
theorem B2994431 : Blo 1995435 2994431 := bstep (se 1 (by rfl) ⟨2245823, by rfl⟩ : syracuseStep 2994431 = 4491647) B4491647
theorem B1996287 : Blo 1995435 1996287 := bstep (se 1 (by rfl) ⟨1497215, by rfl⟩ : syracuseStep 1996287 = 2994431) B2994431
theorem B2994437 : Blo 1995435 2994437 := bbase (se 4 (by rfl) ⟨280728, by rfl⟩ : syracuseStep 2994437 = 561457) (by norm_num)
theorem B1996291 : Blo 1995435 1996291 := bstep (se 1 (by rfl) ⟨1497218, by rfl⟩ : syracuseStep 1996291 = 2994437) B2994437
theorem B3368749 : Blo 1995435 3368749 := bbase (se 3 (by rfl) ⟨631640, by rfl⟩ : syracuseStep 3368749 = 1263281) (by norm_num)
theorem B4491665 : Blo 1995435 4491665 := bstep (se 2 (by rfl) ⟨1684374, by rfl⟩ : syracuseStep 4491665 = 3368749) B3368749
theorem B2994443 : Blo 1995435 2994443 := bstep (se 1 (by rfl) ⟨2245832, by rfl⟩ : syracuseStep 2994443 = 4491665) B4491665
theorem B1996295 : Blo 1995435 1996295 := bstep (se 1 (by rfl) ⟨1497221, by rfl⟩ : syracuseStep 1996295 = 2994443) B2994443
theorem B2245837 : Blo 1995435 2245837 := bbase (se 3 (by rfl) ⟨421094, by rfl⟩ : syracuseStep 2245837 = 842189) (by norm_num)
theorem B2994449 : Blo 1995435 2994449 := bstep (se 2 (by rfl) ⟨1122918, by rfl⟩ : syracuseStep 2994449 = 2245837) B2245837
theorem B1996299 : Blo 1995435 1996299 := bstep (se 1 (by rfl) ⟨1497224, by rfl⟩ : syracuseStep 1996299 = 2994449) B2994449
theorem B6737525 : Blo 1995435 6737525 := bbase (se 5 (by rfl) ⟨315821, by rfl⟩ : syracuseStep 6737525 = 631643) (by norm_num)
theorem B4491683 : Blo 1995435 4491683 := bstep (se 1 (by rfl) ⟨3368762, by rfl⟩ : syracuseStep 4491683 = 6737525) B6737525
theorem B2994455 : Blo 1995435 2994455 := bstep (se 1 (by rfl) ⟨2245841, by rfl⟩ : syracuseStep 2994455 = 4491683) B4491683
theorem B1996303 : Blo 1995435 1996303 := bstep (se 1 (by rfl) ⟨1497227, by rfl⟩ : syracuseStep 1996303 = 2994455) B2994455
theorem B2994461 : Blo 1995435 2994461 := bbase (se 3 (by rfl) ⟨561461, by rfl⟩ : syracuseStep 2994461 = 1122923) (by norm_num)
theorem B1996307 : Blo 1995435 1996307 := bstep (se 1 (by rfl) ⟨1497230, by rfl⟩ : syracuseStep 1996307 = 2994461) B2994461
theorem B4491701 : Blo 1995435 4491701 := bbase (se 5 (by rfl) ⟨210548, by rfl⟩ : syracuseStep 4491701 = 421097) (by norm_num)
theorem B2994467 : Blo 1995435 2994467 := bstep (se 1 (by rfl) ⟨2245850, by rfl⟩ : syracuseStep 2994467 = 4491701) B4491701
theorem B1996311 : Blo 1995435 1996311 := bstep (se 1 (by rfl) ⟨1497233, by rfl⟩ : syracuseStep 1996311 = 2994467) B2994467
theorem B2398285 : Blo 1995435 2398285 := bbase (se 3 (by rfl) ⟨449678, by rfl⟩ : syracuseStep 2398285 = 899357) (by norm_num)
theorem B3197713 : Blo 1995435 3197713 := bstep (se 2 (by rfl) ⟨1199142, by rfl⟩ : syracuseStep 3197713 = 2398285) B2398285
theorem B4263617 : Blo 1995435 4263617 := bstep (se 2 (by rfl) ⟨1598856, by rfl⟩ : syracuseStep 4263617 = 3197713) B3197713
theorem B11369645 : Blo 1995435 11369645 := bstep (se 3 (by rfl) ⟨2131808, by rfl⟩ : syracuseStep 11369645 = 4263617) B4263617
theorem B7579763 : Blo 1995435 7579763 := bstep (se 1 (by rfl) ⟨5684822, by rfl⟩ : syracuseStep 7579763 = 11369645) B11369645
theorem B5053175 : Blo 1995435 5053175 := bstep (se 1 (by rfl) ⟨3789881, by rfl⟩ : syracuseStep 5053175 = 7579763) B7579763
theorem B3368783 : Blo 1995435 3368783 := bstep (se 1 (by rfl) ⟨2526587, by rfl⟩ : syracuseStep 3368783 = 5053175) B5053175
theorem B2245855 : Blo 1995435 2245855 := bstep (se 1 (by rfl) ⟨1684391, by rfl⟩ : syracuseStep 2245855 = 3368783) B3368783
theorem B2994473 : Blo 1995435 2994473 := bstep (se 2 (by rfl) ⟨1122927, by rfl⟩ : syracuseStep 2994473 = 2245855) B2245855
theorem B1996315 : Blo 1995435 1996315 := bstep (se 1 (by rfl) ⟨1497236, by rfl⟩ : syracuseStep 1996315 = 2994473) B2994473
theorem B7194869 : Blo 1995435 7194869 := bbase (se 5 (by rfl) ⟨337259, by rfl⟩ : syracuseStep 7194869 = 674519) (by norm_num)
theorem B4796579 : Blo 1995435 4796579 := bstep (se 1 (by rfl) ⟨3597434, by rfl⟩ : syracuseStep 4796579 = 7194869) B7194869
theorem B3197719 : Blo 1995435 3197719 := bstep (se 1 (by rfl) ⟨2398289, by rfl⟩ : syracuseStep 3197719 = 4796579) B4796579
theorem B4263625 : Blo 1995435 4263625 := bstep (se 2 (by rfl) ⟨1598859, by rfl⟩ : syracuseStep 4263625 = 3197719) B3197719
theorem B5684833 : Blo 1995435 5684833 := bstep (se 2 (by rfl) ⟨2131812, by rfl⟩ : syracuseStep 5684833 = 4263625) B4263625
theorem B7579777 : Blo 1995435 7579777 := bstep (se 2 (by rfl) ⟨2842416, by rfl⟩ : syracuseStep 7579777 = 5684833) B5684833
theorem B10106369 : Blo 1995435 10106369 := bstep (se 2 (by rfl) ⟨3789888, by rfl⟩ : syracuseStep 10106369 = 7579777) B7579777
theorem B6737579 : Blo 1995435 6737579 := bstep (se 1 (by rfl) ⟨5053184, by rfl⟩ : syracuseStep 6737579 = 10106369) B10106369
theorem B4491719 : Blo 1995435 4491719 := bstep (se 1 (by rfl) ⟨3368789, by rfl⟩ : syracuseStep 4491719 = 6737579) B6737579
theorem B2994479 : Blo 1995435 2994479 := bstep (se 1 (by rfl) ⟨2245859, by rfl⟩ : syracuseStep 2994479 = 4491719) B4491719
theorem B1996319 : Blo 1995435 1996319 := bstep (se 1 (by rfl) ⟨1497239, by rfl⟩ : syracuseStep 1996319 = 2994479) B2994479
theorem B2994485 : Blo 1995435 2994485 := bbase (se 5 (by rfl) ⟨140366, by rfl⟩ : syracuseStep 2994485 = 280733) (by norm_num)
theorem B1996323 : Blo 1995435 1996323 := bstep (se 1 (by rfl) ⟨1497242, by rfl⟩ : syracuseStep 1996323 = 2994485) B2994485
theorem B5053205 : Blo 1995435 5053205 := bbase (se 6 (by rfl) ⟨118434, by rfl⟩ : syracuseStep 5053205 = 236869) (by norm_num)
theorem B3368803 : Blo 1995435 3368803 := bstep (se 1 (by rfl) ⟨2526602, by rfl⟩ : syracuseStep 3368803 = 5053205) B5053205
theorem B4491737 : Blo 1995435 4491737 := bstep (se 2 (by rfl) ⟨1684401, by rfl⟩ : syracuseStep 4491737 = 3368803) B3368803
theorem B2994491 : Blo 1995435 2994491 := bstep (se 1 (by rfl) ⟨2245868, by rfl⟩ : syracuseStep 2994491 = 4491737) B4491737
theorem B1996327 : Blo 1995435 1996327 := bstep (se 1 (by rfl) ⟨1497245, by rfl⟩ : syracuseStep 1996327 = 2994491) B2994491
theorem B2245873 : Blo 1995435 2245873 := bbase (se 2 (by rfl) ⟨842202, by rfl⟩ : syracuseStep 2245873 = 1684405) (by norm_num)
theorem B2994497 : Blo 1995435 2994497 := bstep (se 2 (by rfl) ⟨1122936, by rfl⟩ : syracuseStep 2994497 = 2245873) B2245873
theorem B1996331 : Blo 1995435 1996331 := bstep (se 1 (by rfl) ⟨1497248, by rfl⟩ : syracuseStep 1996331 = 2994497) B2994497
theorem B8094293 : Blo 1995435 8094293 := bbase (se 8 (by rfl) ⟨47427, by rfl⟩ : syracuseStep 8094293 = 94855) (by norm_num)
theorem B5396195 : Blo 1995435 5396195 := bstep (se 1 (by rfl) ⟨4047146, by rfl⟩ : syracuseStep 5396195 = 8094293) B8094293
theorem B3597463 : Blo 1995435 3597463 := bstep (se 1 (by rfl) ⟨2698097, by rfl⟩ : syracuseStep 3597463 = 5396195) B5396195
theorem B19186469 : Blo 1995435 19186469 := bstep (se 4 (by rfl) ⟨1798731, by rfl⟩ : syracuseStep 19186469 = 3597463) B3597463
theorem B12790979 : Blo 1995435 12790979 := bstep (se 1 (by rfl) ⟨9593234, by rfl⟩ : syracuseStep 12790979 = 19186469) B19186469
theorem B8527319 : Blo 1995435 8527319 := bstep (se 1 (by rfl) ⟨6395489, by rfl⟩ : syracuseStep 8527319 = 12790979) B12790979
theorem B5684879 : Blo 1995435 5684879 := bstep (se 1 (by rfl) ⟨4263659, by rfl⟩ : syracuseStep 5684879 = 8527319) B8527319
theorem B3789919 : Blo 1995435 3789919 := bstep (se 1 (by rfl) ⟨2842439, by rfl⟩ : syracuseStep 3789919 = 5684879) B5684879
theorem B5053225 : Blo 1995435 5053225 := bstep (se 2 (by rfl) ⟨1894959, by rfl⟩ : syracuseStep 5053225 = 3789919) B3789919
theorem B6737633 : Blo 1995435 6737633 := bstep (se 2 (by rfl) ⟨2526612, by rfl⟩ : syracuseStep 6737633 = 5053225) B5053225
theorem B4491755 : Blo 1995435 4491755 := bstep (se 1 (by rfl) ⟨3368816, by rfl⟩ : syracuseStep 4491755 = 6737633) B6737633
theorem B2994503 : Blo 1995435 2994503 := bstep (se 1 (by rfl) ⟨2245877, by rfl⟩ : syracuseStep 2994503 = 4491755) B4491755
theorem B1996335 : Blo 1995435 1996335 := bstep (se 1 (by rfl) ⟨1497251, by rfl⟩ : syracuseStep 1996335 = 2994503) B2994503
theorem B2994509 : Blo 1995435 2994509 := bbase (se 3 (by rfl) ⟨561470, by rfl⟩ : syracuseStep 2994509 = 1122941) (by norm_num)
theorem B1996339 : Blo 1995435 1996339 := bstep (se 1 (by rfl) ⟨1497254, by rfl⟩ : syracuseStep 1996339 = 2994509) B2994509
theorem B4491773 : Blo 1995435 4491773 := bbase (se 3 (by rfl) ⟨842207, by rfl⟩ : syracuseStep 4491773 = 1684415) (by norm_num)
theorem B2994515 : Blo 1995435 2994515 := bstep (se 1 (by rfl) ⟨2245886, by rfl⟩ : syracuseStep 2994515 = 4491773) B4491773
theorem B1996343 : Blo 1995435 1996343 := bstep (se 1 (by rfl) ⟨1497257, by rfl⟩ : syracuseStep 1996343 = 2994515) B2994515
theorem B3368837 : Blo 1995435 3368837 := bbase (se 4 (by rfl) ⟨315828, by rfl⟩ : syracuseStep 3368837 = 631657) (by norm_num)
theorem B2245891 : Blo 1995435 2245891 := bstep (se 1 (by rfl) ⟨1684418, by rfl⟩ : syracuseStep 2245891 = 3368837) B3368837
theorem B2994521 : Blo 1995435 2994521 := bstep (se 2 (by rfl) ⟨1122945, by rfl⟩ : syracuseStep 2994521 = 2245891) B2245891
theorem B1996347 : Blo 1995435 1996347 := bstep (se 1 (by rfl) ⟨1497260, by rfl⟩ : syracuseStep 1996347 = 2994521) B2994521
theorem B15159797 : Blo 1995435 15159797 := bbase (se 5 (by rfl) ⟨710615, by rfl⟩ : syracuseStep 15159797 = 1421231) (by norm_num)
theorem B10106531 : Blo 1995435 10106531 := bstep (se 1 (by rfl) ⟨7579898, by rfl⟩ : syracuseStep 10106531 = 15159797) B15159797
theorem B6737687 : Blo 1995435 6737687 := bstep (se 1 (by rfl) ⟨5053265, by rfl⟩ : syracuseStep 6737687 = 10106531) B10106531
theorem B4491791 : Blo 1995435 4491791 := bstep (se 1 (by rfl) ⟨3368843, by rfl⟩ : syracuseStep 4491791 = 6737687) B6737687
theorem B2994527 : Blo 1995435 2994527 := bstep (se 1 (by rfl) ⟨2245895, by rfl⟩ : syracuseStep 2994527 = 4491791) B4491791
theorem B1996351 : Blo 1995435 1996351 := bstep (se 1 (by rfl) ⟨1497263, by rfl⟩ : syracuseStep 1996351 = 2994527) B2994527
theorem B2994533 : Blo 1995435 2994533 := bbase (se 4 (by rfl) ⟨280737, by rfl⟩ : syracuseStep 2994533 = 561475) (by norm_num)
theorem B1996355 : Blo 1995435 1996355 := bstep (se 1 (by rfl) ⟨1497266, by rfl⟩ : syracuseStep 1996355 = 2994533) B2994533
theorem B3789965 : Blo 1995435 3789965 := bbase (se 3 (by rfl) ⟨710618, by rfl⟩ : syracuseStep 3789965 = 1421237) (by norm_num)
theorem B2526643 : Blo 1995435 2526643 := bstep (se 1 (by rfl) ⟨1894982, by rfl⟩ : syracuseStep 2526643 = 3789965) B3789965
theorem B3368857 : Blo 1995435 3368857 := bstep (se 2 (by rfl) ⟨1263321, by rfl⟩ : syracuseStep 3368857 = 2526643) B2526643
theorem B4491809 : Blo 1995435 4491809 := bstep (se 2 (by rfl) ⟨1684428, by rfl⟩ : syracuseStep 4491809 = 3368857) B3368857
theorem B2994539 : Blo 1995435 2994539 := bstep (se 1 (by rfl) ⟨2245904, by rfl⟩ : syracuseStep 2994539 = 4491809) B4491809
theorem B1996359 : Blo 1995435 1996359 := bstep (se 1 (by rfl) ⟨1497269, by rfl⟩ : syracuseStep 1996359 = 2994539) B2994539
theorem B2245909 : Blo 1995435 2245909 := bbase (se 6 (by rfl) ⟨52638, by rfl⟩ : syracuseStep 2245909 = 105277) (by norm_num)
theorem B2994545 : Blo 1995435 2994545 := bstep (se 2 (by rfl) ⟨1122954, by rfl⟩ : syracuseStep 2994545 = 2245909) B2245909
theorem B1996363 : Blo 1995435 1996363 := bstep (se 1 (by rfl) ⟨1497272, by rfl⟩ : syracuseStep 1996363 = 2994545) B2994545
theorem B2526653 : Blo 1995435 2526653 := bbase (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) (by norm_num)
theorem B6737741 : Blo 1995435 6737741 := bstep (se 3 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 6737741 = 2526653) B2526653
theorem B4491827 : Blo 1995435 4491827 := bstep (se 1 (by rfl) ⟨3368870, by rfl⟩ : syracuseStep 4491827 = 6737741) B6737741
theorem B2994551 : Blo 1995435 2994551 := bstep (se 1 (by rfl) ⟨2245913, by rfl⟩ : syracuseStep 2994551 = 4491827) B4491827
theorem B1996367 : Blo 1995435 1996367 := bstep (se 1 (by rfl) ⟨1497275, by rfl⟩ : syracuseStep 1996367 = 2994551) B2994551
theorem B2994557 : Blo 1995435 2994557 := bbase (se 3 (by rfl) ⟨561479, by rfl⟩ : syracuseStep 2994557 = 1122959) (by norm_num)
theorem B1996371 : Blo 1995435 1996371 := bstep (se 1 (by rfl) ⟨1497278, by rfl⟩ : syracuseStep 1996371 = 2994557) B2994557
theorem B4491845 : Blo 1995435 4491845 := bbase (se 4 (by rfl) ⟨421110, by rfl⟩ : syracuseStep 4491845 = 842221) (by norm_num)
theorem B2994563 : Blo 1995435 2994563 := bstep (se 1 (by rfl) ⟨2245922, by rfl⟩ : syracuseStep 2994563 = 4491845) B4491845
theorem B1996375 : Blo 1995435 1996375 := bstep (se 1 (by rfl) ⟨1497281, by rfl⟩ : syracuseStep 1996375 = 2994563) B2994563
theorem B2131877 : Blo 1995435 2131877 := bbase (se 4 (by rfl) ⟨199863, by rfl⟩ : syracuseStep 2131877 = 399727) (by norm_num)
theorem B5685005 : Blo 1995435 5685005 := bstep (se 3 (by rfl) ⟨1065938, by rfl⟩ : syracuseStep 5685005 = 2131877) B2131877
theorem B3790003 : Blo 1995435 3790003 := bstep (se 1 (by rfl) ⟨2842502, by rfl⟩ : syracuseStep 3790003 = 5685005) B5685005
theorem B5053337 : Blo 1995435 5053337 := bstep (se 2 (by rfl) ⟨1895001, by rfl⟩ : syracuseStep 5053337 = 3790003) B3790003
theorem B3368891 : Blo 1995435 3368891 := bstep (se 1 (by rfl) ⟨2526668, by rfl⟩ : syracuseStep 3368891 = 5053337) B5053337
theorem B2245927 : Blo 1995435 2245927 := bstep (se 1 (by rfl) ⟨1684445, by rfl⟩ : syracuseStep 2245927 = 3368891) B3368891
theorem B2994569 : Blo 1995435 2994569 := bstep (se 2 (by rfl) ⟨1122963, by rfl⟩ : syracuseStep 2994569 = 2245927) B2245927
theorem B1996379 : Blo 1995435 1996379 := bstep (se 1 (by rfl) ⟨1497284, by rfl⟩ : syracuseStep 1996379 = 2994569) B2994569
theorem B10106693 : Blo 1995435 10106693 := bbase (se 4 (by rfl) ⟨947502, by rfl⟩ : syracuseStep 10106693 = 1895005) (by norm_num)
theorem B6737795 : Blo 1995435 6737795 := bstep (se 1 (by rfl) ⟨5053346, by rfl⟩ : syracuseStep 6737795 = 10106693) B10106693
theorem B4491863 : Blo 1995435 4491863 := bstep (se 1 (by rfl) ⟨3368897, by rfl⟩ : syracuseStep 4491863 = 6737795) B6737795
theorem B2994575 : Blo 1995435 2994575 := bstep (se 1 (by rfl) ⟨2245931, by rfl⟩ : syracuseStep 2994575 = 4491863) B4491863
theorem B1996383 : Blo 1995435 1996383 := bstep (se 1 (by rfl) ⟨1497287, by rfl⟩ : syracuseStep 1996383 = 2994575) B2994575
theorem B2994581 : Blo 1995435 2994581 := bbase (se 6 (by rfl) ⟨70185, by rfl⟩ : syracuseStep 2994581 = 140371) (by norm_num)
theorem B1996387 : Blo 1995435 1996387 := bstep (se 1 (by rfl) ⟨1497290, by rfl⟩ : syracuseStep 1996387 = 2994581) B2994581
theorem B6395669 : Blo 1995435 6395669 := bbase (se 6 (by rfl) ⟨149898, by rfl⟩ : syracuseStep 6395669 = 299797) (by norm_num)
theorem B4263779 : Blo 1995435 4263779 := bstep (se 1 (by rfl) ⟨3197834, by rfl⟩ : syracuseStep 4263779 = 6395669) B6395669
theorem B11370077 : Blo 1995435 11370077 := bstep (se 3 (by rfl) ⟨2131889, by rfl⟩ : syracuseStep 11370077 = 4263779) B4263779
theorem B7580051 : Blo 1995435 7580051 := bstep (se 1 (by rfl) ⟨5685038, by rfl⟩ : syracuseStep 7580051 = 11370077) B11370077
theorem B5053367 : Blo 1995435 5053367 := bstep (se 1 (by rfl) ⟨3790025, by rfl⟩ : syracuseStep 5053367 = 7580051) B7580051
theorem B3368911 : Blo 1995435 3368911 := bstep (se 1 (by rfl) ⟨2526683, by rfl⟩ : syracuseStep 3368911 = 5053367) B5053367
theorem B4491881 : Blo 1995435 4491881 := bstep (se 2 (by rfl) ⟨1684455, by rfl⟩ : syracuseStep 4491881 = 3368911) B3368911
theorem B2994587 : Blo 1995435 2994587 := bstep (se 1 (by rfl) ⟨2245940, by rfl⟩ : syracuseStep 2994587 = 4491881) B4491881
theorem B1996391 : Blo 1995435 1996391 := bstep (se 1 (by rfl) ⟨1497293, by rfl⟩ : syracuseStep 1996391 = 2994587) B2994587
theorem B2245945 : Blo 1995435 2245945 := bbase (se 2 (by rfl) ⟨842229, by rfl⟩ : syracuseStep 2245945 = 1684459) (by norm_num)
theorem B2994593 : Blo 1995435 2994593 := bstep (se 2 (by rfl) ⟨1122972, by rfl⟩ : syracuseStep 2994593 = 2245945) B2245945
theorem B1996395 : Blo 1995435 1996395 := bstep (se 1 (by rfl) ⟨1497296, by rfl⟩ : syracuseStep 1996395 = 2994593) B2994593
theorem B5685061 : Blo 1995435 5685061 := bbase (se 4 (by rfl) ⟨532974, by rfl⟩ : syracuseStep 5685061 = 1065949) (by norm_num)
theorem B7580081 : Blo 1995435 7580081 := bstep (se 2 (by rfl) ⟨2842530, by rfl⟩ : syracuseStep 7580081 = 5685061) B5685061
theorem B5053387 : Blo 1995435 5053387 := bstep (se 1 (by rfl) ⟨3790040, by rfl⟩ : syracuseStep 5053387 = 7580081) B7580081
theorem B6737849 : Blo 1995435 6737849 := bstep (se 2 (by rfl) ⟨2526693, by rfl⟩ : syracuseStep 6737849 = 5053387) B5053387
theorem B4491899 : Blo 1995435 4491899 := bstep (se 1 (by rfl) ⟨3368924, by rfl⟩ : syracuseStep 4491899 = 6737849) B6737849
theorem B2994599 : Blo 1995435 2994599 := bstep (se 1 (by rfl) ⟨2245949, by rfl⟩ : syracuseStep 2994599 = 4491899) B4491899
theorem B1996399 : Blo 1995435 1996399 := bstep (se 1 (by rfl) ⟨1497299, by rfl⟩ : syracuseStep 1996399 = 2994599) B2994599
theorem B2994605 : Blo 1995435 2994605 := bbase (se 3 (by rfl) ⟨561488, by rfl⟩ : syracuseStep 2994605 = 1122977) (by norm_num)
theorem B1996403 : Blo 1995435 1996403 := bstep (se 1 (by rfl) ⟨1497302, by rfl⟩ : syracuseStep 1996403 = 2994605) B2994605
theorem B4491917 : Blo 1995435 4491917 := bbase (se 3 (by rfl) ⟨842234, by rfl⟩ : syracuseStep 4491917 = 1684469) (by norm_num)
theorem B2994611 : Blo 1995435 2994611 := bstep (se 1 (by rfl) ⟨2245958, by rfl⟩ : syracuseStep 2994611 = 4491917) B4491917
theorem B1996407 : Blo 1995435 1996407 := bstep (se 1 (by rfl) ⟨1497305, by rfl⟩ : syracuseStep 1996407 = 2994611) B2994611
theorem B2526709 : Blo 1995435 2526709 := bbase (se 5 (by rfl) ⟨118439, by rfl⟩ : syracuseStep 2526709 = 236879) (by norm_num)
theorem B3368945 : Blo 1995435 3368945 := bstep (se 2 (by rfl) ⟨1263354, by rfl⟩ : syracuseStep 3368945 = 2526709) B2526709
theorem B2245963 : Blo 1995435 2245963 := bstep (se 1 (by rfl) ⟨1684472, by rfl⟩ : syracuseStep 2245963 = 3368945) B3368945
theorem B2994617 : Blo 1995435 2994617 := bstep (se 2 (by rfl) ⟨1122981, by rfl⟩ : syracuseStep 2994617 = 2245963) B2245963
theorem B1996411 : Blo 1995435 1996411 := bstep (se 1 (by rfl) ⟨1497308, by rfl⟩ : syracuseStep 1996411 = 2994617) B2994617
theorem B2698205 : Blo 1995435 2698205 := bbase (se 3 (by rfl) ⟨505913, by rfl⟩ : syracuseStep 2698205 = 1011827) (by norm_num)
theorem B7195213 : Blo 1995435 7195213 := bstep (se 3 (by rfl) ⟨1349102, by rfl⟩ : syracuseStep 7195213 = 2698205) B2698205
theorem B38374469 : Blo 1995435 38374469 := bstep (se 4 (by rfl) ⟨3597606, by rfl⟩ : syracuseStep 38374469 = 7195213) B7195213
theorem B25582979 : Blo 1995435 25582979 := bstep (se 1 (by rfl) ⟨19187234, by rfl⟩ : syracuseStep 25582979 = 38374469) B38374469
theorem B17055319 : Blo 1995435 17055319 := bstep (se 1 (by rfl) ⟨12791489, by rfl⟩ : syracuseStep 17055319 = 25582979) B25582979
theorem B22740425 : Blo 1995435 22740425 := bstep (se 2 (by rfl) ⟨8527659, by rfl⟩ : syracuseStep 22740425 = 17055319) B17055319
theorem B15160283 : Blo 1995435 15160283 := bstep (se 1 (by rfl) ⟨11370212, by rfl⟩ : syracuseStep 15160283 = 22740425) B22740425
theorem B10106855 : Blo 1995435 10106855 := bstep (se 1 (by rfl) ⟨7580141, by rfl⟩ : syracuseStep 10106855 = 15160283) B15160283
theorem B6737903 : Blo 1995435 6737903 := bstep (se 1 (by rfl) ⟨5053427, by rfl⟩ : syracuseStep 6737903 = 10106855) B10106855
theorem B4491935 : Blo 1995435 4491935 := bstep (se 1 (by rfl) ⟨3368951, by rfl⟩ : syracuseStep 4491935 = 6737903) B6737903
theorem B2994623 : Blo 1995435 2994623 := bstep (se 1 (by rfl) ⟨2245967, by rfl⟩ : syracuseStep 2994623 = 4491935) B4491935
theorem B1996415 : Blo 1995435 1996415 := bstep (se 1 (by rfl) ⟨1497311, by rfl⟩ : syracuseStep 1996415 = 2994623) B2994623
theorem B2994629 : Blo 1995435 2994629 := bbase (se 4 (by rfl) ⟨280746, by rfl⟩ : syracuseStep 2994629 = 561493) (by norm_num)
theorem B1996419 : Blo 1995435 1996419 := bstep (se 1 (by rfl) ⟨1497314, by rfl⟩ : syracuseStep 1996419 = 2994629) B2994629
theorem B3368965 : Blo 1995435 3368965 := bbase (se 4 (by rfl) ⟨315840, by rfl⟩ : syracuseStep 3368965 = 631681) (by norm_num)
theorem B4491953 : Blo 1995435 4491953 := bstep (se 2 (by rfl) ⟨1684482, by rfl⟩ : syracuseStep 4491953 = 3368965) B3368965
theorem B2994635 : Blo 1995435 2994635 := bstep (se 1 (by rfl) ⟨2245976, by rfl⟩ : syracuseStep 2994635 = 4491953) B4491953
theorem B1996423 : Blo 1995435 1996423 := bstep (se 1 (by rfl) ⟨1497317, by rfl⟩ : syracuseStep 1996423 = 2994635) B2994635
theorem B2245981 : Blo 1995435 2245981 := bbase (se 3 (by rfl) ⟨421121, by rfl⟩ : syracuseStep 2245981 = 842243) (by norm_num)
theorem B2994641 : Blo 1995435 2994641 := bstep (se 2 (by rfl) ⟨1122990, by rfl⟩ : syracuseStep 2994641 = 2245981) B2245981
theorem B1996427 : Blo 1995435 1996427 := bstep (se 1 (by rfl) ⟨1497320, by rfl⟩ : syracuseStep 1996427 = 2994641) B2994641
theorem B6737957 : Blo 1995435 6737957 := bbase (se 4 (by rfl) ⟨631683, by rfl⟩ : syracuseStep 6737957 = 1263367) (by norm_num)
theorem B4491971 : Blo 1995435 4491971 := bstep (se 1 (by rfl) ⟨3368978, by rfl⟩ : syracuseStep 4491971 = 6737957) B6737957
theorem B2994647 : Blo 1995435 2994647 := bstep (se 1 (by rfl) ⟨2245985, by rfl⟩ : syracuseStep 2994647 = 4491971) B4491971
theorem B1996431 : Blo 1995435 1996431 := bstep (se 1 (by rfl) ⟨1497323, by rfl⟩ : syracuseStep 1996431 = 2994647) B2994647
theorem B2994653 : Blo 1995435 2994653 := bbase (se 3 (by rfl) ⟨561497, by rfl⟩ : syracuseStep 2994653 = 1122995) (by norm_num)
theorem B1996435 : Blo 1995435 1996435 := bstep (se 1 (by rfl) ⟨1497326, by rfl⟩ : syracuseStep 1996435 = 2994653) B2994653
theorem B4491989 : Blo 1995435 4491989 := bbase (se 7 (by rfl) ⟨52640, by rfl⟩ : syracuseStep 4491989 = 105281) (by norm_num)
theorem B2994659 : Blo 1995435 2994659 := bstep (se 1 (by rfl) ⟨2245994, by rfl⟩ : syracuseStep 2994659 = 4491989) B4491989
theorem B1996439 : Blo 1995435 1996439 := bstep (se 1 (by rfl) ⟨1497329, by rfl⟩ : syracuseStep 1996439 = 2994659) B2994659
theorem B8527781 : Blo 1995435 8527781 := bbase (se 4 (by rfl) ⟨799479, by rfl⟩ : syracuseStep 8527781 = 1598959) (by norm_num)
theorem B5685187 : Blo 1995435 5685187 := bstep (se 1 (by rfl) ⟨4263890, by rfl⟩ : syracuseStep 5685187 = 8527781) B8527781
theorem B7580249 : Blo 1995435 7580249 := bstep (se 2 (by rfl) ⟨2842593, by rfl⟩ : syracuseStep 7580249 = 5685187) B5685187
theorem B5053499 : Blo 1995435 5053499 := bstep (se 1 (by rfl) ⟨3790124, by rfl⟩ : syracuseStep 5053499 = 7580249) B7580249
theorem B3368999 : Blo 1995435 3368999 := bstep (se 1 (by rfl) ⟨2526749, by rfl⟩ : syracuseStep 3368999 = 5053499) B5053499
theorem B2245999 : Blo 1995435 2245999 := bstep (se 1 (by rfl) ⟨1684499, by rfl⟩ : syracuseStep 2245999 = 3368999) B3368999
theorem B2994665 : Blo 1995435 2994665 := bstep (se 2 (by rfl) ⟨1122999, by rfl⟩ : syracuseStep 2994665 = 2245999) B2245999
theorem B1996443 : Blo 1995435 1996443 := bstep (se 1 (by rfl) ⟨1497332, by rfl⟩ : syracuseStep 1996443 = 2994665) B2994665
theorem B2161037 : Blo 1995435 2161037 := bbase (se 3 (by rfl) ⟨405194, by rfl⟩ : syracuseStep 2161037 = 810389) (by norm_num)
theorem B5762765 : Blo 1995435 5762765 := bstep (se 3 (by rfl) ⟨1080518, by rfl⟩ : syracuseStep 5762765 = 2161037) B2161037
theorem B3841843 : Blo 1995435 3841843 := bstep (se 1 (by rfl) ⟨2881382, by rfl⟩ : syracuseStep 3841843 = 5762765) B5762765
theorem B5122457 : Blo 1995435 5122457 := bstep (se 2 (by rfl) ⟨1920921, by rfl⟩ : syracuseStep 5122457 = 3841843) B3841843
theorem B3414971 : Blo 1995435 3414971 := bstep (se 1 (by rfl) ⟨2561228, by rfl⟩ : syracuseStep 3414971 = 5122457) B5122457
theorem B9106589 : Blo 1995435 9106589 := bstep (se 3 (by rfl) ⟨1707485, by rfl⟩ : syracuseStep 9106589 = 3414971) B3414971
theorem B6071059 : Blo 1995435 6071059 := bstep (se 1 (by rfl) ⟨4553294, by rfl⟩ : syracuseStep 6071059 = 9106589) B9106589
theorem B8094745 : Blo 1995435 8094745 := bstep (se 2 (by rfl) ⟨3035529, by rfl⟩ : syracuseStep 8094745 = 6071059) B6071059
theorem B43171973 : Blo 1995435 43171973 := bstep (se 4 (by rfl) ⟨4047372, by rfl⟩ : syracuseStep 43171973 = 8094745) B8094745
theorem B28781315 : Blo 1995435 28781315 := bstep (se 1 (by rfl) ⟨21585986, by rfl⟩ : syracuseStep 28781315 = 43171973) B43171973
theorem B19187543 : Blo 1995435 19187543 := bstep (se 1 (by rfl) ⟨14390657, by rfl⟩ : syracuseStep 19187543 = 28781315) B28781315
theorem B12791695 : Blo 1995435 12791695 := bstep (se 1 (by rfl) ⟨9593771, by rfl⟩ : syracuseStep 12791695 = 19187543) B19187543
theorem B17055593 : Blo 1995435 17055593 := bstep (se 2 (by rfl) ⟨6395847, by rfl⟩ : syracuseStep 17055593 = 12791695) B12791695
theorem B11370395 : Blo 1995435 11370395 := bstep (se 1 (by rfl) ⟨8527796, by rfl⟩ : syracuseStep 11370395 = 17055593) B17055593
theorem B7580263 : Blo 1995435 7580263 := bstep (se 1 (by rfl) ⟨5685197, by rfl⟩ : syracuseStep 7580263 = 11370395) B11370395
theorem B10107017 : Blo 1995435 10107017 := bstep (se 2 (by rfl) ⟨3790131, by rfl⟩ : syracuseStep 10107017 = 7580263) B7580263
theorem B6738011 : Blo 1995435 6738011 := bstep (se 1 (by rfl) ⟨5053508, by rfl⟩ : syracuseStep 6738011 = 10107017) B10107017
theorem B4492007 : Blo 1995435 4492007 := bstep (se 1 (by rfl) ⟨3369005, by rfl⟩ : syracuseStep 4492007 = 6738011) B6738011
theorem B2994671 : Blo 1995435 2994671 := bstep (se 1 (by rfl) ⟨2246003, by rfl⟩ : syracuseStep 2994671 = 4492007) B4492007
theorem B1996447 : Blo 1995435 1996447 := bstep (se 1 (by rfl) ⟨1497335, by rfl⟩ : syracuseStep 1996447 = 2994671) B2994671
theorem B2994677 : Blo 1995435 2994677 := bbase (se 5 (by rfl) ⟨140375, by rfl⟩ : syracuseStep 2994677 = 280751) (by norm_num)
theorem B1996451 : Blo 1995435 1996451 := bstep (se 1 (by rfl) ⟨1497338, by rfl⟩ : syracuseStep 1996451 = 2994677) B2994677
theorem B5685221 : Blo 1995435 5685221 := bbase (se 4 (by rfl) ⟨532989, by rfl⟩ : syracuseStep 5685221 = 1065979) (by norm_num)
theorem B3790147 : Blo 1995435 3790147 := bstep (se 1 (by rfl) ⟨2842610, by rfl⟩ : syracuseStep 3790147 = 5685221) B5685221
theorem B5053529 : Blo 1995435 5053529 := bstep (se 2 (by rfl) ⟨1895073, by rfl⟩ : syracuseStep 5053529 = 3790147) B3790147
theorem B3369019 : Blo 1995435 3369019 := bstep (se 1 (by rfl) ⟨2526764, by rfl⟩ : syracuseStep 3369019 = 5053529) B5053529
theorem B4492025 : Blo 1995435 4492025 := bstep (se 2 (by rfl) ⟨1684509, by rfl⟩ : syracuseStep 4492025 = 3369019) B3369019
theorem B2994683 : Blo 1995435 2994683 := bstep (se 1 (by rfl) ⟨2246012, by rfl⟩ : syracuseStep 2994683 = 4492025) B4492025
theorem B1996455 : Blo 1995435 1996455 := bstep (se 1 (by rfl) ⟨1497341, by rfl⟩ : syracuseStep 1996455 = 2994683) B2994683
theorem B2246017 : Blo 1995435 2246017 := bbase (se 2 (by rfl) ⟨842256, by rfl⟩ : syracuseStep 2246017 = 1684513) (by norm_num)
theorem B2994689 : Blo 1995435 2994689 := bstep (se 2 (by rfl) ⟨1123008, by rfl⟩ : syracuseStep 2994689 = 2246017) B2246017
theorem B1996459 : Blo 1995435 1996459 := bstep (se 1 (by rfl) ⟨1497344, by rfl⟩ : syracuseStep 1996459 = 2994689) B2994689
theorem B5053549 : Blo 1995435 5053549 := bbase (se 3 (by rfl) ⟨947540, by rfl⟩ : syracuseStep 5053549 = 1895081) (by norm_num)
theorem B6738065 : Blo 1995435 6738065 := bstep (se 2 (by rfl) ⟨2526774, by rfl⟩ : syracuseStep 6738065 = 5053549) B5053549
theorem B4492043 : Blo 1995435 4492043 := bstep (se 1 (by rfl) ⟨3369032, by rfl⟩ : syracuseStep 4492043 = 6738065) B6738065
theorem B2994695 : Blo 1995435 2994695 := bstep (se 1 (by rfl) ⟨2246021, by rfl⟩ : syracuseStep 2994695 = 4492043) B4492043
theorem B1996463 : Blo 1995435 1996463 := bstep (se 1 (by rfl) ⟨1497347, by rfl⟩ : syracuseStep 1996463 = 2994695) B2994695
theorem B2994701 : Blo 1995435 2994701 := bbase (se 3 (by rfl) ⟨561506, by rfl⟩ : syracuseStep 2994701 = 1123013) (by norm_num)
theorem B1996467 : Blo 1995435 1996467 := bstep (se 1 (by rfl) ⟨1497350, by rfl⟩ : syracuseStep 1996467 = 2994701) B2994701
theorem B4492061 : Blo 1995435 4492061 := bbase (se 3 (by rfl) ⟨842261, by rfl⟩ : syracuseStep 4492061 = 1684523) (by norm_num)
theorem B2994707 : Blo 1995435 2994707 := bstep (se 1 (by rfl) ⟨2246030, by rfl⟩ : syracuseStep 2994707 = 4492061) B4492061
theorem B1996471 : Blo 1995435 1996471 := bstep (se 1 (by rfl) ⟨1497353, by rfl⟩ : syracuseStep 1996471 = 2994707) B2994707
theorem B3369053 : Blo 1995435 3369053 := bbase (se 3 (by rfl) ⟨631697, by rfl⟩ : syracuseStep 3369053 = 1263395) (by norm_num)
theorem B2246035 : Blo 1995435 2246035 := bstep (se 1 (by rfl) ⟨1684526, by rfl⟩ : syracuseStep 2246035 = 3369053) B3369053
theorem B2994713 : Blo 1995435 2994713 := bstep (se 2 (by rfl) ⟨1123017, by rfl⟩ : syracuseStep 2994713 = 2246035) B2246035
theorem B1996475 : Blo 1995435 1996475 := bstep (se 1 (by rfl) ⟨1497356, by rfl⟩ : syracuseStep 1996475 = 2994713) B2994713
theorem B7195445 : Blo 1995435 7195445 := bbase (se 5 (by rfl) ⟨337286, by rfl⟩ : syracuseStep 7195445 = 674573) (by norm_num)
theorem B4796963 : Blo 1995435 4796963 := bstep (se 1 (by rfl) ⟨3597722, by rfl⟩ : syracuseStep 4796963 = 7195445) B7195445
theorem B3197975 : Blo 1995435 3197975 := bstep (se 1 (by rfl) ⟨2398481, by rfl⟩ : syracuseStep 3197975 = 4796963) B4796963
theorem B8527933 : Blo 1995435 8527933 := bstep (se 3 (by rfl) ⟨1598987, by rfl⟩ : syracuseStep 8527933 = 3197975) B3197975
theorem B11370577 : Blo 1995435 11370577 := bstep (se 2 (by rfl) ⟨4263966, by rfl⟩ : syracuseStep 11370577 = 8527933) B8527933
theorem B15160769 : Blo 1995435 15160769 := bstep (se 2 (by rfl) ⟨5685288, by rfl⟩ : syracuseStep 15160769 = 11370577) B11370577
theorem B10107179 : Blo 1995435 10107179 := bstep (se 1 (by rfl) ⟨7580384, by rfl⟩ : syracuseStep 10107179 = 15160769) B15160769
theorem B6738119 : Blo 1995435 6738119 := bstep (se 1 (by rfl) ⟨5053589, by rfl⟩ : syracuseStep 6738119 = 10107179) B10107179
theorem B4492079 : Blo 1995435 4492079 := bstep (se 1 (by rfl) ⟨3369059, by rfl⟩ : syracuseStep 4492079 = 6738119) B6738119
theorem B2994719 : Blo 1995435 2994719 := bstep (se 1 (by rfl) ⟨2246039, by rfl⟩ : syracuseStep 2994719 = 4492079) B4492079
theorem B1996479 : Blo 1995435 1996479 := bstep (se 1 (by rfl) ⟨1497359, by rfl⟩ : syracuseStep 1996479 = 2994719) B2994719
theorem B2994725 : Blo 1995435 2994725 := bbase (se 4 (by rfl) ⟨280755, by rfl⟩ : syracuseStep 2994725 = 561511) (by norm_num)
theorem B1996483 : Blo 1995435 1996483 := bstep (se 1 (by rfl) ⟨1497362, by rfl⟩ : syracuseStep 1996483 = 2994725) B2994725
theorem B2526805 : Blo 1995435 2526805 := bbase (se 8 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 2526805 = 29611) (by norm_num)
theorem B3369073 : Blo 1995435 3369073 := bstep (se 2 (by rfl) ⟨1263402, by rfl⟩ : syracuseStep 3369073 = 2526805) B2526805
theorem B4492097 : Blo 1995435 4492097 := bstep (se 2 (by rfl) ⟨1684536, by rfl⟩ : syracuseStep 4492097 = 3369073) B3369073
theorem B2994731 : Blo 1995435 2994731 := bstep (se 1 (by rfl) ⟨2246048, by rfl⟩ : syracuseStep 2994731 = 4492097) B4492097
theorem B1996487 : Blo 1995435 1996487 := bstep (se 1 (by rfl) ⟨1497365, by rfl⟩ : syracuseStep 1996487 = 2994731) B2994731
theorem B2246053 : Blo 1995435 2246053 := bbase (se 4 (by rfl) ⟨210567, by rfl⟩ : syracuseStep 2246053 = 421135) (by norm_num)
theorem B2994737 : Blo 1995435 2994737 := bstep (se 2 (by rfl) ⟨1123026, by rfl⟩ : syracuseStep 2994737 = 2246053) B2246053
theorem B1996491 : Blo 1995435 1996491 := bstep (se 1 (by rfl) ⟨1497368, by rfl⟩ : syracuseStep 1996491 = 2994737) B2994737
theorem B2398501 : Blo 1995435 2398501 := bbase (se 4 (by rfl) ⟨224859, by rfl⟩ : syracuseStep 2398501 = 449719) (by norm_num)
theorem B12792005 : Blo 1995435 12792005 := bstep (se 4 (by rfl) ⟨1199250, by rfl⟩ : syracuseStep 12792005 = 2398501) B2398501
theorem B8528003 : Blo 1995435 8528003 := bstep (se 1 (by rfl) ⟨6396002, by rfl⟩ : syracuseStep 8528003 = 12792005) B12792005
theorem B5685335 : Blo 1995435 5685335 := bstep (se 1 (by rfl) ⟨4264001, by rfl⟩ : syracuseStep 5685335 = 8528003) B8528003
theorem B3790223 : Blo 1995435 3790223 := bstep (se 1 (by rfl) ⟨2842667, by rfl⟩ : syracuseStep 3790223 = 5685335) B5685335
theorem B2526815 : Blo 1995435 2526815 := bstep (se 1 (by rfl) ⟨1895111, by rfl⟩ : syracuseStep 2526815 = 3790223) B3790223
theorem B6738173 : Blo 1995435 6738173 := bstep (se 3 (by rfl) ⟨1263407, by rfl⟩ : syracuseStep 6738173 = 2526815) B2526815
theorem B4492115 : Blo 1995435 4492115 := bstep (se 1 (by rfl) ⟨3369086, by rfl⟩ : syracuseStep 4492115 = 6738173) B6738173
theorem B2994743 : Blo 1995435 2994743 := bstep (se 1 (by rfl) ⟨2246057, by rfl⟩ : syracuseStep 2994743 = 4492115) B4492115
theorem B1996495 : Blo 1995435 1996495 := bstep (se 1 (by rfl) ⟨1497371, by rfl⟩ : syracuseStep 1996495 = 2994743) B2994743
theorem B2994749 : Blo 1995435 2994749 := bbase (se 3 (by rfl) ⟨561515, by rfl⟩ : syracuseStep 2994749 = 1123031) (by norm_num)
theorem B1996499 : Blo 1995435 1996499 := bstep (se 1 (by rfl) ⟨1497374, by rfl⟩ : syracuseStep 1996499 = 2994749) B2994749
theorem B4492133 : Blo 1995435 4492133 := bbase (se 4 (by rfl) ⟨421137, by rfl⟩ : syracuseStep 4492133 = 842275) (by norm_num)
theorem B2994755 : Blo 1995435 2994755 := bstep (se 1 (by rfl) ⟨2246066, by rfl⟩ : syracuseStep 2994755 = 4492133) B4492133
theorem B1996503 : Blo 1995435 1996503 := bstep (se 1 (by rfl) ⟨1497377, by rfl⟩ : syracuseStep 1996503 = 2994755) B2994755
theorem B5053661 : Blo 1995435 5053661 := bbase (se 3 (by rfl) ⟨947561, by rfl⟩ : syracuseStep 5053661 = 1895123) (by norm_num)
theorem B3369107 : Blo 1995435 3369107 := bstep (se 1 (by rfl) ⟨2526830, by rfl⟩ : syracuseStep 3369107 = 5053661) B5053661
theorem B2246071 : Blo 1995435 2246071 := bstep (se 1 (by rfl) ⟨1684553, by rfl⟩ : syracuseStep 2246071 = 3369107) B3369107
theorem B2994761 : Blo 1995435 2994761 := bstep (se 2 (by rfl) ⟨1123035, by rfl⟩ : syracuseStep 2994761 = 2246071) B2246071
theorem B1996507 : Blo 1995435 1996507 := bstep (se 1 (by rfl) ⟨1497380, by rfl⟩ : syracuseStep 1996507 = 2994761) B2994761
theorem B3790253 : Blo 1995435 3790253 := bbase (se 3 (by rfl) ⟨710672, by rfl⟩ : syracuseStep 3790253 = 1421345) (by norm_num)
theorem B10107341 : Blo 1995435 10107341 := bstep (se 3 (by rfl) ⟨1895126, by rfl⟩ : syracuseStep 10107341 = 3790253) B3790253
theorem B6738227 : Blo 1995435 6738227 := bstep (se 1 (by rfl) ⟨5053670, by rfl⟩ : syracuseStep 6738227 = 10107341) B10107341
theorem B4492151 : Blo 1995435 4492151 := bstep (se 1 (by rfl) ⟨3369113, by rfl⟩ : syracuseStep 4492151 = 6738227) B6738227
theorem B2994767 : Blo 1995435 2994767 := bstep (se 1 (by rfl) ⟨2246075, by rfl⟩ : syracuseStep 2994767 = 4492151) B4492151
theorem B1996511 : Blo 1995435 1996511 := bstep (se 1 (by rfl) ⟨1497383, by rfl⟩ : syracuseStep 1996511 = 2994767) B2994767
theorem B2994773 : Blo 1995435 2994773 := bbase (se 8 (by rfl) ⟨17547, by rfl⟩ : syracuseStep 2994773 = 35095) (by norm_num)
theorem B1996515 : Blo 1995435 1996515 := bstep (se 1 (by rfl) ⟨1497386, by rfl⟩ : syracuseStep 1996515 = 2994773) B2994773
theorem B2307793 : Blo 1995435 2307793 := bbase (se 2 (by rfl) ⟨865422, by rfl⟩ : syracuseStep 2307793 = 1730845) (by norm_num)
theorem B3077057 : Blo 1995435 3077057 := bstep (se 2 (by rfl) ⟨1153896, by rfl⟩ : syracuseStep 3077057 = 2307793) B2307793
theorem B2051371 : Blo 1995435 2051371 := bstep (se 1 (by rfl) ⟨1538528, by rfl⟩ : syracuseStep 2051371 = 3077057) B3077057
theorem B10940645 : Blo 1995435 10940645 := bstep (se 4 (by rfl) ⟨1025685, by rfl⟩ : syracuseStep 10940645 = 2051371) B2051371
theorem B7293763 : Blo 1995435 7293763 := bstep (se 1 (by rfl) ⟨5470322, by rfl⟩ : syracuseStep 7293763 = 10940645) B10940645
theorem B9725017 : Blo 1995435 9725017 := bstep (se 2 (by rfl) ⟨3646881, by rfl⟩ : syracuseStep 9725017 = 7293763) B7293763
theorem B12966689 : Blo 1995435 12966689 := bstep (se 2 (by rfl) ⟨4862508, by rfl⟩ : syracuseStep 12966689 = 9725017) B9725017
theorem B34577837 : Blo 1995435 34577837 := bstep (se 3 (by rfl) ⟨6483344, by rfl⟩ : syracuseStep 34577837 = 12966689) B12966689
theorem B23051891 : Blo 1995435 23051891 := bstep (se 1 (by rfl) ⟨17288918, by rfl⟩ : syracuseStep 23051891 = 34577837) B34577837
theorem B15367927 : Blo 1995435 15367927 := bstep (se 1 (by rfl) ⟨11525945, by rfl⟩ : syracuseStep 15367927 = 23051891) B23051891
theorem B20490569 : Blo 1995435 20490569 := bstep (se 2 (by rfl) ⟨7683963, by rfl⟩ : syracuseStep 20490569 = 15367927) B15367927
theorem B13660379 : Blo 1995435 13660379 := bstep (se 1 (by rfl) ⟨10245284, by rfl⟩ : syracuseStep 13660379 = 20490569) B20490569
theorem B9106919 : Blo 1995435 9106919 := bstep (se 1 (by rfl) ⟨6830189, by rfl⟩ : syracuseStep 9106919 = 13660379) B13660379
theorem B6071279 : Blo 1995435 6071279 := bstep (se 1 (by rfl) ⟨4553459, by rfl⟩ : syracuseStep 6071279 = 9106919) B9106919
theorem B16190077 : Blo 1995435 16190077 := bstep (se 3 (by rfl) ⟨3035639, by rfl⟩ : syracuseStep 16190077 = 6071279) B6071279
theorem B21586769 : Blo 1995435 21586769 := bstep (se 2 (by rfl) ⟨8095038, by rfl⟩ : syracuseStep 21586769 = 16190077) B16190077
theorem B14391179 : Blo 1995435 14391179 := bstep (se 1 (by rfl) ⟨10793384, by rfl⟩ : syracuseStep 14391179 = 21586769) B21586769
theorem B9594119 : Blo 1995435 9594119 := bstep (se 1 (by rfl) ⟨7195589, by rfl⟩ : syracuseStep 9594119 = 14391179) B14391179
theorem B6396079 : Blo 1995435 6396079 := bstep (se 1 (by rfl) ⟨4797059, by rfl⟩ : syracuseStep 6396079 = 9594119) B9594119
theorem B8528105 : Blo 1995435 8528105 := bstep (se 2 (by rfl) ⟨3198039, by rfl⟩ : syracuseStep 8528105 = 6396079) B6396079
theorem B5685403 : Blo 1995435 5685403 := bstep (se 1 (by rfl) ⟨4264052, by rfl⟩ : syracuseStep 5685403 = 8528105) B8528105
theorem B7580537 : Blo 1995435 7580537 := bstep (se 2 (by rfl) ⟨2842701, by rfl⟩ : syracuseStep 7580537 = 5685403) B5685403
theorem B5053691 : Blo 1995435 5053691 := bstep (se 1 (by rfl) ⟨3790268, by rfl⟩ : syracuseStep 5053691 = 7580537) B7580537
theorem B3369127 : Blo 1995435 3369127 := bstep (se 1 (by rfl) ⟨2526845, by rfl⟩ : syracuseStep 3369127 = 5053691) B5053691
theorem B4492169 : Blo 1995435 4492169 := bstep (se 2 (by rfl) ⟨1684563, by rfl⟩ : syracuseStep 4492169 = 3369127) B3369127
theorem B2994779 : Blo 1995435 2994779 := bstep (se 1 (by rfl) ⟨2246084, by rfl⟩ : syracuseStep 2994779 = 4492169) B4492169
theorem B1996519 : Blo 1995435 1996519 := bstep (se 1 (by rfl) ⟨1497389, by rfl⟩ : syracuseStep 1996519 = 2994779) B2994779
theorem B2246089 : Blo 1995435 2246089 := bbase (se 2 (by rfl) ⟨842283, by rfl⟩ : syracuseStep 2246089 = 1684567) (by norm_num)
theorem B2994785 : Blo 1995435 2994785 := bstep (se 2 (by rfl) ⟨1123044, by rfl⟩ : syracuseStep 2994785 = 2246089) B2246089
theorem B1996523 : Blo 1995435 1996523 := bstep (se 1 (by rfl) ⟨1497392, by rfl⟩ : syracuseStep 1996523 = 2994785) B2994785
theorem B17056277 : Blo 1995435 17056277 := bbase (se 6 (by rfl) ⟨399756, by rfl⟩ : syracuseStep 17056277 = 799513) (by norm_num)
theorem B11370851 : Blo 1995435 11370851 := bstep (se 1 (by rfl) ⟨8528138, by rfl⟩ : syracuseStep 11370851 = 17056277) B17056277
theorem B7580567 : Blo 1995435 7580567 := bstep (se 1 (by rfl) ⟨5685425, by rfl⟩ : syracuseStep 7580567 = 11370851) B11370851
theorem B5053711 : Blo 1995435 5053711 := bstep (se 1 (by rfl) ⟨3790283, by rfl⟩ : syracuseStep 5053711 = 7580567) B7580567
theorem B6738281 : Blo 1995435 6738281 := bstep (se 2 (by rfl) ⟨2526855, by rfl⟩ : syracuseStep 6738281 = 5053711) B5053711
theorem B4492187 : Blo 1995435 4492187 := bstep (se 1 (by rfl) ⟨3369140, by rfl⟩ : syracuseStep 4492187 = 6738281) B6738281
theorem B2994791 : Blo 1995435 2994791 := bstep (se 1 (by rfl) ⟨2246093, by rfl⟩ : syracuseStep 2994791 = 4492187) B4492187
theorem B1996527 : Blo 1995435 1996527 := bstep (se 1 (by rfl) ⟨1497395, by rfl⟩ : syracuseStep 1996527 = 2994791) B2994791
theorem B2994797 : Blo 1995435 2994797 := bbase (se 3 (by rfl) ⟨561524, by rfl⟩ : syracuseStep 2994797 = 1123049) (by norm_num)
theorem B1996531 : Blo 1995435 1996531 := bstep (se 1 (by rfl) ⟨1497398, by rfl⟩ : syracuseStep 1996531 = 2994797) B2994797
theorem B4492205 : Blo 1995435 4492205 := bbase (se 3 (by rfl) ⟨842288, by rfl⟩ : syracuseStep 4492205 = 1684577) (by norm_num)
theorem B2994803 : Blo 1995435 2994803 := bstep (se 1 (by rfl) ⟨2246102, by rfl⟩ : syracuseStep 2994803 = 4492205) B4492205
theorem B1996535 : Blo 1995435 1996535 := bstep (se 1 (by rfl) ⟨1497401, by rfl⟩ : syracuseStep 1996535 = 2994803) B2994803
theorem B5685461 : Blo 1995435 5685461 := bbase (se 7 (by rfl) ⟨66626, by rfl⟩ : syracuseStep 5685461 = 133253) (by norm_num)
theorem B3790307 : Blo 1995435 3790307 := bstep (se 1 (by rfl) ⟨2842730, by rfl⟩ : syracuseStep 3790307 = 5685461) B5685461
theorem B2526871 : Blo 1995435 2526871 := bstep (se 1 (by rfl) ⟨1895153, by rfl⟩ : syracuseStep 2526871 = 3790307) B3790307
theorem B3369161 : Blo 1995435 3369161 := bstep (se 2 (by rfl) ⟨1263435, by rfl⟩ : syracuseStep 3369161 = 2526871) B2526871
theorem B2246107 : Blo 1995435 2246107 := bstep (se 1 (by rfl) ⟨1684580, by rfl⟩ : syracuseStep 2246107 = 3369161) B3369161
theorem B2994809 : Blo 1995435 2994809 := bstep (se 2 (by rfl) ⟨1123053, by rfl⟩ : syracuseStep 2994809 = 2246107) B2246107
theorem B1996539 : Blo 1995435 1996539 := bstep (se 1 (by rfl) ⟨1497404, by rfl⟩ : syracuseStep 1996539 = 2994809) B2994809
theorem B27693845 : Blo 1995435 27693845 := bbase (se 6 (by rfl) ⟨649074, by rfl⟩ : syracuseStep 27693845 = 1298149) (by norm_num)
theorem B18462563 : Blo 1995435 18462563 := bstep (se 1 (by rfl) ⟨13846922, by rfl⟩ : syracuseStep 18462563 = 27693845) B27693845
theorem B12308375 : Blo 1995435 12308375 := bstep (se 1 (by rfl) ⟨9231281, by rfl⟩ : syracuseStep 12308375 = 18462563) B18462563
theorem B8205583 : Blo 1995435 8205583 := bstep (se 1 (by rfl) ⟨6154187, by rfl⟩ : syracuseStep 8205583 = 12308375) B12308375
theorem B10940777 : Blo 1995435 10940777 := bstep (se 2 (by rfl) ⟨4102791, by rfl⟩ : syracuseStep 10940777 = 8205583) B8205583
theorem B7293851 : Blo 1995435 7293851 := bstep (se 1 (by rfl) ⟨5470388, by rfl⟩ : syracuseStep 7293851 = 10940777) B10940777
theorem B4862567 : Blo 1995435 4862567 := bstep (se 1 (by rfl) ⟨3646925, by rfl⟩ : syracuseStep 4862567 = 7293851) B7293851
theorem B3241711 : Blo 1995435 3241711 := bstep (se 1 (by rfl) ⟨2431283, by rfl⟩ : syracuseStep 3241711 = 4862567) B4862567
theorem B4322281 : Blo 1995435 4322281 := bstep (se 2 (by rfl) ⟨1620855, by rfl⟩ : syracuseStep 4322281 = 3241711) B3241711
theorem B5763041 : Blo 1995435 5763041 := bstep (se 2 (by rfl) ⟨2161140, by rfl⟩ : syracuseStep 5763041 = 4322281) B4322281
theorem B3842027 : Blo 1995435 3842027 := bstep (se 1 (by rfl) ⟨2881520, by rfl⟩ : syracuseStep 3842027 = 5763041) B5763041
theorem B2561351 : Blo 1995435 2561351 := bstep (se 1 (by rfl) ⟨1921013, by rfl⟩ : syracuseStep 2561351 = 3842027) B3842027
theorem B27321077 : Blo 1995435 27321077 := bstep (se 5 (by rfl) ⟨1280675, by rfl⟩ : syracuseStep 27321077 = 2561351) B2561351
theorem B72856205 : Blo 1995435 72856205 := bstep (se 3 (by rfl) ⟨13660538, by rfl⟩ : syracuseStep 72856205 = 27321077) B27321077
theorem B48570803 : Blo 1995435 48570803 := bstep (se 1 (by rfl) ⟨36428102, by rfl⟩ : syracuseStep 48570803 = 72856205) B72856205
theorem B32380535 : Blo 1995435 32380535 := bstep (se 1 (by rfl) ⟨24285401, by rfl⟩ : syracuseStep 32380535 = 48570803) B48570803
theorem B21587023 : Blo 1995435 21587023 := bstep (se 1 (by rfl) ⟨16190267, by rfl⟩ : syracuseStep 21587023 = 32380535) B32380535
theorem B28782697 : Blo 1995435 28782697 := bstep (se 2 (by rfl) ⟨10793511, by rfl⟩ : syracuseStep 28782697 = 21587023) B21587023
theorem B38376929 : Blo 1995435 38376929 := bstep (se 2 (by rfl) ⟨14391348, by rfl⟩ : syracuseStep 38376929 = 28782697) B28782697
theorem B25584619 : Blo 1995435 25584619 := bstep (se 1 (by rfl) ⟨19188464, by rfl⟩ : syracuseStep 25584619 = 38376929) B38376929
theorem B34112825 : Blo 1995435 34112825 := bstep (se 2 (by rfl) ⟨12792309, by rfl⟩ : syracuseStep 34112825 = 25584619) B25584619
theorem B22741883 : Blo 1995435 22741883 := bstep (se 1 (by rfl) ⟨17056412, by rfl⟩ : syracuseStep 22741883 = 34112825) B34112825
theorem B15161255 : Blo 1995435 15161255 := bstep (se 1 (by rfl) ⟨11370941, by rfl⟩ : syracuseStep 15161255 = 22741883) B22741883
theorem B10107503 : Blo 1995435 10107503 := bstep (se 1 (by rfl) ⟨7580627, by rfl⟩ : syracuseStep 10107503 = 15161255) B15161255
theorem B6738335 : Blo 1995435 6738335 := bstep (se 1 (by rfl) ⟨5053751, by rfl⟩ : syracuseStep 6738335 = 10107503) B10107503
theorem B4492223 : Blo 1995435 4492223 := bstep (se 1 (by rfl) ⟨3369167, by rfl⟩ : syracuseStep 4492223 = 6738335) B6738335
theorem B2994815 : Blo 1995435 2994815 := bstep (se 1 (by rfl) ⟨2246111, by rfl⟩ : syracuseStep 2994815 = 4492223) B4492223
theorem B1996543 : Blo 1995435 1996543 := bstep (se 1 (by rfl) ⟨1497407, by rfl⟩ : syracuseStep 1996543 = 2994815) B2994815
theorem B2994821 : Blo 1995435 2994821 := bbase (se 4 (by rfl) ⟨280764, by rfl⟩ : syracuseStep 2994821 = 561529) (by norm_num)
theorem B1996547 : Blo 1995435 1996547 := bstep (se 1 (by rfl) ⟨1497410, by rfl⟩ : syracuseStep 1996547 = 2994821) B2994821
theorem B3369181 : Blo 1995435 3369181 := bbase (se 3 (by rfl) ⟨631721, by rfl⟩ : syracuseStep 3369181 = 1263443) (by norm_num)
theorem B4492241 : Blo 1995435 4492241 := bstep (se 2 (by rfl) ⟨1684590, by rfl⟩ : syracuseStep 4492241 = 3369181) B3369181
theorem B2994827 : Blo 1995435 2994827 := bstep (se 1 (by rfl) ⟨2246120, by rfl⟩ : syracuseStep 2994827 = 4492241) B4492241
theorem B1996551 : Blo 1995435 1996551 := bstep (se 1 (by rfl) ⟨1497413, by rfl⟩ : syracuseStep 1996551 = 2994827) B2994827
theorem B2246125 : Blo 1995435 2246125 := bbase (se 3 (by rfl) ⟨421148, by rfl⟩ : syracuseStep 2246125 = 842297) (by norm_num)
theorem B2994833 : Blo 1995435 2994833 := bstep (se 2 (by rfl) ⟨1123062, by rfl⟩ : syracuseStep 2994833 = 2246125) B2246125
theorem B1996555 : Blo 1995435 1996555 := bstep (se 1 (by rfl) ⟨1497416, by rfl⟩ : syracuseStep 1996555 = 2994833) B2994833
theorem B6738389 : Blo 1995435 6738389 := bbase (se 7 (by rfl) ⟨78965, by rfl⟩ : syracuseStep 6738389 = 157931) (by norm_num)
theorem B4492259 : Blo 1995435 4492259 := bstep (se 1 (by rfl) ⟨3369194, by rfl⟩ : syracuseStep 4492259 = 6738389) B6738389
theorem B2994839 : Blo 1995435 2994839 := bstep (se 1 (by rfl) ⟨2246129, by rfl⟩ : syracuseStep 2994839 = 4492259) B4492259
theorem B1996559 : Blo 1995435 1996559 := bstep (se 1 (by rfl) ⟨1497419, by rfl⟩ : syracuseStep 1996559 = 2994839) B2994839
theorem B2994845 : Blo 1995435 2994845 := bbase (se 3 (by rfl) ⟨561533, by rfl⟩ : syracuseStep 2994845 = 1123067) (by norm_num)
theorem B1996563 : Blo 1995435 1996563 := bstep (se 1 (by rfl) ⟨1497422, by rfl⟩ : syracuseStep 1996563 = 2994845) B2994845
theorem B4492277 : Blo 1995435 4492277 := bbase (se 5 (by rfl) ⟨210575, by rfl⟩ : syracuseStep 4492277 = 421151) (by norm_num)
theorem B2994851 : Blo 1995435 2994851 := bstep (se 1 (by rfl) ⟨2246138, by rfl⟩ : syracuseStep 2994851 = 4492277) B4492277
theorem B1996567 : Blo 1995435 1996567 := bstep (se 1 (by rfl) ⟨1497425, by rfl⟩ : syracuseStep 1996567 = 2994851) B2994851
theorem B2276789 : Blo 1995435 2276789 := bbase (se 5 (by rfl) ⟨106724, by rfl⟩ : syracuseStep 2276789 = 213449) (by norm_num)
theorem B6071437 : Blo 1995435 6071437 := bstep (se 3 (by rfl) ⟨1138394, by rfl⟩ : syracuseStep 6071437 = 2276789) B2276789
theorem B8095249 : Blo 1995435 8095249 := bstep (se 2 (by rfl) ⟨3035718, by rfl⟩ : syracuseStep 8095249 = 6071437) B6071437
theorem B10793665 : Blo 1995435 10793665 := bstep (se 2 (by rfl) ⟨4047624, by rfl⟩ : syracuseStep 10793665 = 8095249) B8095249
theorem B57566213 : Blo 1995435 57566213 := bstep (se 4 (by rfl) ⟨5396832, by rfl⟩ : syracuseStep 57566213 = 10793665) B10793665
theorem B38377475 : Blo 1995435 38377475 := bstep (se 1 (by rfl) ⟨28783106, by rfl⟩ : syracuseStep 38377475 = 57566213) B57566213
theorem B25584983 : Blo 1995435 25584983 := bstep (se 1 (by rfl) ⟨19188737, by rfl⟩ : syracuseStep 25584983 = 38377475) B38377475
theorem B17056655 : Blo 1995435 17056655 := bstep (se 1 (by rfl) ⟨12792491, by rfl⟩ : syracuseStep 17056655 = 25584983) B25584983
theorem B11371103 : Blo 1995435 11371103 := bstep (se 1 (by rfl) ⟨8528327, by rfl⟩ : syracuseStep 11371103 = 17056655) B17056655
theorem B7580735 : Blo 1995435 7580735 := bstep (se 1 (by rfl) ⟨5685551, by rfl⟩ : syracuseStep 7580735 = 11371103) B11371103
theorem B5053823 : Blo 1995435 5053823 := bstep (se 1 (by rfl) ⟨3790367, by rfl⟩ : syracuseStep 5053823 = 7580735) B7580735
theorem B3369215 : Blo 1995435 3369215 := bstep (se 1 (by rfl) ⟨2526911, by rfl⟩ : syracuseStep 3369215 = 5053823) B5053823
theorem B2246143 : Blo 1995435 2246143 := bstep (se 1 (by rfl) ⟨1684607, by rfl⟩ : syracuseStep 2246143 = 3369215) B3369215
theorem B2994857 : Blo 1995435 2994857 := bstep (se 2 (by rfl) ⟨1123071, by rfl⟩ : syracuseStep 2994857 = 2246143) B2246143
theorem B1996571 : Blo 1995435 1996571 := bstep (se 1 (by rfl) ⟨1497428, by rfl⟩ : syracuseStep 1996571 = 2994857) B2994857
theorem B2842781 : Blo 1995435 2842781 := bbase (se 3 (by rfl) ⟨533021, by rfl⟩ : syracuseStep 2842781 = 1066043) (by norm_num)
theorem B7580749 : Blo 1995435 7580749 := bstep (se 3 (by rfl) ⟨1421390, by rfl⟩ : syracuseStep 7580749 = 2842781) B2842781
theorem B10107665 : Blo 1995435 10107665 := bstep (se 2 (by rfl) ⟨3790374, by rfl⟩ : syracuseStep 10107665 = 7580749) B7580749
theorem B6738443 : Blo 1995435 6738443 := bstep (se 1 (by rfl) ⟨5053832, by rfl⟩ : syracuseStep 6738443 = 10107665) B10107665
theorem B4492295 : Blo 1995435 4492295 := bstep (se 1 (by rfl) ⟨3369221, by rfl⟩ : syracuseStep 4492295 = 6738443) B6738443
theorem B2994863 : Blo 1995435 2994863 := bstep (se 1 (by rfl) ⟨2246147, by rfl⟩ : syracuseStep 2994863 = 4492295) B4492295
theorem B1996575 : Blo 1995435 1996575 := bstep (se 1 (by rfl) ⟨1497431, by rfl⟩ : syracuseStep 1996575 = 2994863) B2994863
theorem B2994869 : Blo 1995435 2994869 := bbase (se 5 (by rfl) ⟨140384, by rfl⟩ : syracuseStep 2994869 = 280769) (by norm_num)
theorem B1996579 : Blo 1995435 1996579 := bstep (se 1 (by rfl) ⟨1497434, by rfl⟩ : syracuseStep 1996579 = 2994869) B2994869
theorem B5053853 : Blo 1995435 5053853 := bbase (se 3 (by rfl) ⟨947597, by rfl⟩ : syracuseStep 5053853 = 1895195) (by norm_num)
theorem B3369235 : Blo 1995435 3369235 := bstep (se 1 (by rfl) ⟨2526926, by rfl⟩ : syracuseStep 3369235 = 5053853) B5053853
theorem B4492313 : Blo 1995435 4492313 := bstep (se 2 (by rfl) ⟨1684617, by rfl⟩ : syracuseStep 4492313 = 3369235) B3369235
theorem B2994875 : Blo 1995435 2994875 := bstep (se 1 (by rfl) ⟨2246156, by rfl⟩ : syracuseStep 2994875 = 4492313) B4492313
theorem B1996583 : Blo 1995435 1996583 := bstep (se 1 (by rfl) ⟨1497437, by rfl⟩ : syracuseStep 1996583 = 2994875) B2994875
theorem B2246161 : Blo 1995435 2246161 := bbase (se 2 (by rfl) ⟨842310, by rfl⟩ : syracuseStep 2246161 = 1684621) (by norm_num)
theorem B2994881 : Blo 1995435 2994881 := bstep (se 2 (by rfl) ⟨1123080, by rfl⟩ : syracuseStep 2994881 = 2246161) B2246161
theorem B1996587 : Blo 1995435 1996587 := bstep (se 1 (by rfl) ⟨1497440, by rfl⟩ : syracuseStep 1996587 = 2994881) B2994881
theorem B3790405 : Blo 1995435 3790405 := bbase (se 4 (by rfl) ⟨355350, by rfl⟩ : syracuseStep 3790405 = 710701) (by norm_num)
theorem B5053873 : Blo 1995435 5053873 := bstep (se 2 (by rfl) ⟨1895202, by rfl⟩ : syracuseStep 5053873 = 3790405) B3790405
theorem B6738497 : Blo 1995435 6738497 := bstep (se 2 (by rfl) ⟨2526936, by rfl⟩ : syracuseStep 6738497 = 5053873) B5053873
theorem B4492331 : Blo 1995435 4492331 := bstep (se 1 (by rfl) ⟨3369248, by rfl⟩ : syracuseStep 4492331 = 6738497) B6738497
theorem B2994887 : Blo 1995435 2994887 := bstep (se 1 (by rfl) ⟨2246165, by rfl⟩ : syracuseStep 2994887 = 4492331) B4492331
theorem B1996591 : Blo 1995435 1996591 := bstep (se 1 (by rfl) ⟨1497443, by rfl⟩ : syracuseStep 1996591 = 2994887) B2994887
theorem B2994893 : Blo 1995435 2994893 := bbase (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) (by norm_num)
theorem B1996595 : Blo 1995435 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B4492349 : Blo 1995435 4492349 := bbase (se 3 (by rfl) ⟨842315, by rfl⟩ : syracuseStep 4492349 = 1684631) (by norm_num)
theorem B2994899 : Blo 1995435 2994899 := bstep (se 1 (by rfl) ⟨2246174, by rfl⟩ : syracuseStep 2994899 = 4492349) B4492349
theorem B1996599 : Blo 1995435 1996599 := bstep (se 1 (by rfl) ⟨1497449, by rfl⟩ : syracuseStep 1996599 = 2994899) B2994899
theorem B3369269 : Blo 1995435 3369269 := bbase (se 5 (by rfl) ⟨157934, by rfl⟩ : syracuseStep 3369269 = 315869) (by norm_num)
theorem B2246179 : Blo 1995435 2246179 := bstep (se 1 (by rfl) ⟨1684634, by rfl⟩ : syracuseStep 2246179 = 3369269) B3369269
theorem B2994905 : Blo 1995435 2994905 := bstep (se 2 (by rfl) ⟨1123089, by rfl⟩ : syracuseStep 2994905 = 2246179) B2246179
theorem B1996603 : Blo 1995435 1996603 := bstep (se 1 (by rfl) ⟨1497452, by rfl⟩ : syracuseStep 1996603 = 2994905) B2994905
theorem B5685653 : Blo 1995435 5685653 := bbase (se 6 (by rfl) ⟨133257, by rfl⟩ : syracuseStep 5685653 = 266515) (by norm_num)
theorem B15161741 : Blo 1995435 15161741 := bstep (se 3 (by rfl) ⟨2842826, by rfl⟩ : syracuseStep 15161741 = 5685653) B5685653
theorem B10107827 : Blo 1995435 10107827 := bstep (se 1 (by rfl) ⟨7580870, by rfl⟩ : syracuseStep 10107827 = 15161741) B15161741
theorem B6738551 : Blo 1995435 6738551 := bstep (se 1 (by rfl) ⟨5053913, by rfl⟩ : syracuseStep 6738551 = 10107827) B10107827
theorem B4492367 : Blo 1995435 4492367 := bstep (se 1 (by rfl) ⟨3369275, by rfl⟩ : syracuseStep 4492367 = 6738551) B6738551
theorem B2994911 : Blo 1995435 2994911 := bstep (se 1 (by rfl) ⟨2246183, by rfl⟩ : syracuseStep 2994911 = 4492367) B4492367
theorem B1996607 : Blo 1995435 1996607 := bstep (se 1 (by rfl) ⟨1497455, by rfl⟩ : syracuseStep 1996607 = 2994911) B2994911
theorem B2994917 : Blo 1995435 2994917 := bbase (se 4 (by rfl) ⟨280773, by rfl⟩ : syracuseStep 2994917 = 561547) (by norm_num)
theorem B1996611 : Blo 1995435 1996611 := bstep (se 1 (by rfl) ⟨1497458, by rfl⟩ : syracuseStep 1996611 = 2994917) B2994917
theorem B2132129 : Blo 1995435 2132129 := bbase (se 2 (by rfl) ⟨799548, by rfl⟩ : syracuseStep 2132129 = 1599097) (by norm_num)
theorem B5685677 : Blo 1995435 5685677 := bstep (se 3 (by rfl) ⟨1066064, by rfl⟩ : syracuseStep 5685677 = 2132129) B2132129
theorem B3790451 : Blo 1995435 3790451 := bstep (se 1 (by rfl) ⟨2842838, by rfl⟩ : syracuseStep 3790451 = 5685677) B5685677
theorem B2526967 : Blo 1995435 2526967 := bstep (se 1 (by rfl) ⟨1895225, by rfl⟩ : syracuseStep 2526967 = 3790451) B3790451
theorem B3369289 : Blo 1995435 3369289 := bstep (se 2 (by rfl) ⟨1263483, by rfl⟩ : syracuseStep 3369289 = 2526967) B2526967
theorem B4492385 : Blo 1995435 4492385 := bstep (se 2 (by rfl) ⟨1684644, by rfl⟩ : syracuseStep 4492385 = 3369289) B3369289
theorem B2994923 : Blo 1995435 2994923 := bstep (se 1 (by rfl) ⟨2246192, by rfl⟩ : syracuseStep 2994923 = 4492385) B4492385
theorem B1996615 : Blo 1995435 1996615 := bstep (se 1 (by rfl) ⟨1497461, by rfl⟩ : syracuseStep 1996615 = 2994923) B2994923
theorem B2246197 : Blo 1995435 2246197 := bbase (se 5 (by rfl) ⟨105290, by rfl⟩ : syracuseStep 2246197 = 210581) (by norm_num)
theorem B2994929 : Blo 1995435 2994929 := bstep (se 2 (by rfl) ⟨1123098, by rfl⟩ : syracuseStep 2994929 = 2246197) B2246197
theorem B1996619 : Blo 1995435 1996619 := bstep (se 1 (by rfl) ⟨1497464, by rfl⟩ : syracuseStep 1996619 = 2994929) B2994929
theorem B2526977 : Blo 1995435 2526977 := bbase (se 2 (by rfl) ⟨947616, by rfl⟩ : syracuseStep 2526977 = 1895233) (by norm_num)
theorem B6738605 : Blo 1995435 6738605 := bstep (se 3 (by rfl) ⟨1263488, by rfl⟩ : syracuseStep 6738605 = 2526977) B2526977
theorem B4492403 : Blo 1995435 4492403 := bstep (se 1 (by rfl) ⟨3369302, by rfl⟩ : syracuseStep 4492403 = 6738605) B6738605
theorem B2994935 : Blo 1995435 2994935 := bstep (se 1 (by rfl) ⟨2246201, by rfl⟩ : syracuseStep 2994935 = 4492403) B4492403
theorem B1996623 : Blo 1995435 1996623 := bstep (se 1 (by rfl) ⟨1497467, by rfl⟩ : syracuseStep 1996623 = 2994935) B2994935
theorem B2994941 : Blo 1995435 2994941 := bbase (se 3 (by rfl) ⟨561551, by rfl⟩ : syracuseStep 2994941 = 1123103) (by norm_num)
theorem B1996627 : Blo 1995435 1996627 := bstep (se 1 (by rfl) ⟨1497470, by rfl⟩ : syracuseStep 1996627 = 2994941) B2994941
theorem B4492421 : Blo 1995435 4492421 := bbase (se 4 (by rfl) ⟨421164, by rfl⟩ : syracuseStep 4492421 = 842329) (by norm_num)
theorem B2994947 : Blo 1995435 2994947 := bstep (se 1 (by rfl) ⟨2246210, by rfl⟩ : syracuseStep 2994947 = 4492421) B4492421
theorem B1996631 : Blo 1995435 1996631 := bstep (se 1 (by rfl) ⟨1497473, by rfl⟩ : syracuseStep 1996631 = 2994947) B2994947
theorem B4264301 : Blo 1995435 4264301 := bbase (se 3 (by rfl) ⟨799556, by rfl⟩ : syracuseStep 4264301 = 1599113) (by norm_num)
theorem B2842867 : Blo 1995435 2842867 := bstep (se 1 (by rfl) ⟨2132150, by rfl⟩ : syracuseStep 2842867 = 4264301) B4264301
theorem B3790489 : Blo 1995435 3790489 := bstep (se 2 (by rfl) ⟨1421433, by rfl⟩ : syracuseStep 3790489 = 2842867) B2842867
theorem B5053985 : Blo 1995435 5053985 := bstep (se 2 (by rfl) ⟨1895244, by rfl⟩ : syracuseStep 5053985 = 3790489) B3790489
theorem B3369323 : Blo 1995435 3369323 := bstep (se 1 (by rfl) ⟨2526992, by rfl⟩ : syracuseStep 3369323 = 5053985) B5053985
theorem B2246215 : Blo 1995435 2246215 := bstep (se 1 (by rfl) ⟨1684661, by rfl⟩ : syracuseStep 2246215 = 3369323) B3369323
theorem B2994953 : Blo 1995435 2994953 := bstep (se 2 (by rfl) ⟨1123107, by rfl⟩ : syracuseStep 2994953 = 2246215) B2246215
theorem B1996635 : Blo 1995435 1996635 := bstep (se 1 (by rfl) ⟨1497476, by rfl⟩ : syracuseStep 1996635 = 2994953) B2994953
theorem B10107989 : Blo 1995435 10107989 := bbase (se 8 (by rfl) ⟨59226, by rfl⟩ : syracuseStep 10107989 = 118453) (by norm_num)
theorem B6738659 : Blo 1995435 6738659 := bstep (se 1 (by rfl) ⟨5053994, by rfl⟩ : syracuseStep 6738659 = 10107989) B10107989
theorem B4492439 : Blo 1995435 4492439 := bstep (se 1 (by rfl) ⟨3369329, by rfl⟩ : syracuseStep 4492439 = 6738659) B6738659
theorem B2994959 : Blo 1995435 2994959 := bstep (se 1 (by rfl) ⟨2246219, by rfl⟩ : syracuseStep 2994959 = 4492439) B4492439
theorem B1996639 : Blo 1995435 1996639 := bstep (se 1 (by rfl) ⟨1497479, by rfl⟩ : syracuseStep 1996639 = 2994959) B2994959
theorem B2994965 : Blo 1995435 2994965 := bbase (se 6 (by rfl) ⟨70194, by rfl⟩ : syracuseStep 2994965 = 140389) (by norm_num)
theorem B1996643 : Blo 1995435 1996643 := bstep (se 1 (by rfl) ⟨1497482, by rfl⟩ : syracuseStep 1996643 = 2994965) B2994965
theorem B6071669 : Blo 1995435 6071669 := bbase (se 5 (by rfl) ⟨284609, by rfl⟩ : syracuseStep 6071669 = 569219) (by norm_num)
theorem B4047779 : Blo 1995435 4047779 := bstep (se 1 (by rfl) ⟨3035834, by rfl⟩ : syracuseStep 4047779 = 6071669) B6071669
theorem B2698519 : Blo 1995435 2698519 := bstep (se 1 (by rfl) ⟨2023889, by rfl⟩ : syracuseStep 2698519 = 4047779) B4047779
theorem B3598025 : Blo 1995435 3598025 := bstep (se 2 (by rfl) ⟨1349259, by rfl⟩ : syracuseStep 3598025 = 2698519) B2698519
theorem B38378933 : Blo 1995435 38378933 := bstep (se 5 (by rfl) ⟨1799012, by rfl⟩ : syracuseStep 38378933 = 3598025) B3598025
theorem B25585955 : Blo 1995435 25585955 := bstep (se 1 (by rfl) ⟨19189466, by rfl⟩ : syracuseStep 25585955 = 38378933) B38378933
theorem B17057303 : Blo 1995435 17057303 := bstep (se 1 (by rfl) ⟨12792977, by rfl⟩ : syracuseStep 17057303 = 25585955) B25585955
theorem B11371535 : Blo 1995435 11371535 := bstep (se 1 (by rfl) ⟨8528651, by rfl⟩ : syracuseStep 11371535 = 17057303) B17057303
theorem B7581023 : Blo 1995435 7581023 := bstep (se 1 (by rfl) ⟨5685767, by rfl⟩ : syracuseStep 7581023 = 11371535) B11371535
theorem B5054015 : Blo 1995435 5054015 := bstep (se 1 (by rfl) ⟨3790511, by rfl⟩ : syracuseStep 5054015 = 7581023) B7581023
theorem B3369343 : Blo 1995435 3369343 := bstep (se 1 (by rfl) ⟨2527007, by rfl⟩ : syracuseStep 3369343 = 5054015) B5054015
theorem B4492457 : Blo 1995435 4492457 := bstep (se 2 (by rfl) ⟨1684671, by rfl⟩ : syracuseStep 4492457 = 3369343) B3369343
theorem B2994971 : Blo 1995435 2994971 := bstep (se 1 (by rfl) ⟨2246228, by rfl⟩ : syracuseStep 2994971 = 4492457) B4492457
theorem B1996647 : Blo 1995435 1996647 := bstep (se 1 (by rfl) ⟨1497485, by rfl⟩ : syracuseStep 1996647 = 2994971) B2994971
theorem B2246233 : Blo 1995435 2246233 := bbase (se 2 (by rfl) ⟨842337, by rfl⟩ : syracuseStep 2246233 = 1684675) (by norm_num)
theorem B2994977 : Blo 1995435 2994977 := bstep (se 2 (by rfl) ⟨1123116, by rfl⟩ : syracuseStep 2994977 = 2246233) B2246233
theorem B1996651 : Blo 1995435 1996651 := bstep (se 1 (by rfl) ⟨1497488, by rfl⟩ : syracuseStep 1996651 = 2994977) B2994977
theorem B9594773 : Blo 1995435 9594773 := bbase (se 6 (by rfl) ⟨224877, by rfl⟩ : syracuseStep 9594773 = 449755) (by norm_num)
theorem B6396515 : Blo 1995435 6396515 := bstep (se 1 (by rfl) ⟨4797386, by rfl⟩ : syracuseStep 6396515 = 9594773) B9594773
theorem B4264343 : Blo 1995435 4264343 := bstep (se 1 (by rfl) ⟨3198257, by rfl⟩ : syracuseStep 4264343 = 6396515) B6396515
theorem B2842895 : Blo 1995435 2842895 := bstep (se 1 (by rfl) ⟨2132171, by rfl⟩ : syracuseStep 2842895 = 4264343) B4264343
theorem B7581053 : Blo 1995435 7581053 := bstep (se 3 (by rfl) ⟨1421447, by rfl⟩ : syracuseStep 7581053 = 2842895) B2842895
theorem B5054035 : Blo 1995435 5054035 := bstep (se 1 (by rfl) ⟨3790526, by rfl⟩ : syracuseStep 5054035 = 7581053) B7581053
theorem B6738713 : Blo 1995435 6738713 := bstep (se 2 (by rfl) ⟨2527017, by rfl⟩ : syracuseStep 6738713 = 5054035) B5054035
theorem B4492475 : Blo 1995435 4492475 := bstep (se 1 (by rfl) ⟨3369356, by rfl⟩ : syracuseStep 4492475 = 6738713) B6738713
theorem B2994983 : Blo 1995435 2994983 := bstep (se 1 (by rfl) ⟨2246237, by rfl⟩ : syracuseStep 2994983 = 4492475) B4492475
theorem B1996655 : Blo 1995435 1996655 := bstep (se 1 (by rfl) ⟨1497491, by rfl⟩ : syracuseStep 1996655 = 2994983) B2994983
theorem B2994989 : Blo 1995435 2994989 := bbase (se 3 (by rfl) ⟨561560, by rfl⟩ : syracuseStep 2994989 = 1123121) (by norm_num)
theorem B1996659 : Blo 1995435 1996659 := bstep (se 1 (by rfl) ⟨1497494, by rfl⟩ : syracuseStep 1996659 = 2994989) B2994989
theorem B4492493 : Blo 1995435 4492493 := bbase (se 3 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 4492493 = 1684685) (by norm_num)
theorem B2994995 : Blo 1995435 2994995 := bstep (se 1 (by rfl) ⟨2246246, by rfl⟩ : syracuseStep 2994995 = 4492493) B4492493
theorem B1996663 : Blo 1995435 1996663 := bstep (se 1 (by rfl) ⟨1497497, by rfl⟩ : syracuseStep 1996663 = 2994995) B2994995
theorem B2527033 : Blo 1995435 2527033 := bbase (se 2 (by rfl) ⟨947637, by rfl⟩ : syracuseStep 2527033 = 1895275) (by norm_num)
theorem B3369377 : Blo 1995435 3369377 := bstep (se 2 (by rfl) ⟨1263516, by rfl⟩ : syracuseStep 3369377 = 2527033) B2527033
theorem B2246251 : Blo 1995435 2246251 := bstep (se 1 (by rfl) ⟨1684688, by rfl⟩ : syracuseStep 2246251 = 3369377) B3369377
theorem B2995001 : Blo 1995435 2995001 := bstep (se 2 (by rfl) ⟨1123125, by rfl⟩ : syracuseStep 2995001 = 2246251) B2246251
theorem B1996667 : Blo 1995435 1996667 := bstep (se 1 (by rfl) ⟨1497500, by rfl⟩ : syracuseStep 1996667 = 2995001) B2995001
theorem B6396565 : Blo 1995435 6396565 := bbase (se 6 (by rfl) ⟨149919, by rfl⟩ : syracuseStep 6396565 = 299839) (by norm_num)
theorem B8528753 : Blo 1995435 8528753 := bstep (se 2 (by rfl) ⟨3198282, by rfl⟩ : syracuseStep 8528753 = 6396565) B6396565
theorem B22743341 : Blo 1995435 22743341 := bstep (se 3 (by rfl) ⟨4264376, by rfl⟩ : syracuseStep 22743341 = 8528753) B8528753
theorem B15162227 : Blo 1995435 15162227 := bstep (se 1 (by rfl) ⟨11371670, by rfl⟩ : syracuseStep 15162227 = 22743341) B22743341
theorem B10108151 : Blo 1995435 10108151 := bstep (se 1 (by rfl) ⟨7581113, by rfl⟩ : syracuseStep 10108151 = 15162227) B15162227
theorem B6738767 : Blo 1995435 6738767 := bstep (se 1 (by rfl) ⟨5054075, by rfl⟩ : syracuseStep 6738767 = 10108151) B10108151
theorem B4492511 : Blo 1995435 4492511 := bstep (se 1 (by rfl) ⟨3369383, by rfl⟩ : syracuseStep 4492511 = 6738767) B6738767
theorem B2995007 : Blo 1995435 2995007 := bstep (se 1 (by rfl) ⟨2246255, by rfl⟩ : syracuseStep 2995007 = 4492511) B4492511
theorem B1996671 : Blo 1995435 1996671 := bstep (se 1 (by rfl) ⟨1497503, by rfl⟩ : syracuseStep 1996671 = 2995007) B2995007
theorem B2995013 : Blo 1995435 2995013 := bbase (se 4 (by rfl) ⟨280782, by rfl⟩ : syracuseStep 2995013 = 561565) (by norm_num)
theorem B1996675 : Blo 1995435 1996675 := bstep (se 1 (by rfl) ⟨1497506, by rfl⟩ : syracuseStep 1996675 = 2995013) B2995013
theorem B3369397 : Blo 1995435 3369397 := bbase (se 5 (by rfl) ⟨157940, by rfl⟩ : syracuseStep 3369397 = 315881) (by norm_num)
theorem B4492529 : Blo 1995435 4492529 := bstep (se 2 (by rfl) ⟨1684698, by rfl⟩ : syracuseStep 4492529 = 3369397) B3369397
theorem B2995019 : Blo 1995435 2995019 := bstep (se 1 (by rfl) ⟨2246264, by rfl⟩ : syracuseStep 2995019 = 4492529) B4492529
theorem B1996679 : Blo 1995435 1996679 := bstep (se 1 (by rfl) ⟨1497509, by rfl⟩ : syracuseStep 1996679 = 2995019) B2995019
theorem B2246269 : Blo 1995435 2246269 := bbase (se 3 (by rfl) ⟨421175, by rfl⟩ : syracuseStep 2246269 = 842351) (by norm_num)
theorem B2995025 : Blo 1995435 2995025 := bstep (se 2 (by rfl) ⟨1123134, by rfl⟩ : syracuseStep 2995025 = 2246269) B2246269
theorem B1996683 : Blo 1995435 1996683 := bstep (se 1 (by rfl) ⟨1497512, by rfl⟩ : syracuseStep 1996683 = 2995025) B2995025
theorem B6738821 : Blo 1995435 6738821 := bbase (se 4 (by rfl) ⟨631764, by rfl⟩ : syracuseStep 6738821 = 1263529) (by norm_num)
theorem B4492547 : Blo 1995435 4492547 := bstep (se 1 (by rfl) ⟨3369410, by rfl⟩ : syracuseStep 4492547 = 6738821) B6738821
theorem B2995031 : Blo 1995435 2995031 := bstep (se 1 (by rfl) ⟨2246273, by rfl⟩ : syracuseStep 2995031 = 4492547) B4492547
theorem B1996687 : Blo 1995435 1996687 := bstep (se 1 (by rfl) ⟨1497515, by rfl⟩ : syracuseStep 1996687 = 2995031) B2995031
theorem B2995037 : Blo 1995435 2995037 := bbase (se 3 (by rfl) ⟨561569, by rfl⟩ : syracuseStep 2995037 = 1123139) (by norm_num)
theorem B1996691 : Blo 1995435 1996691 := bstep (se 1 (by rfl) ⟨1497518, by rfl⟩ : syracuseStep 1996691 = 2995037) B2995037
theorem B4492565 : Blo 1995435 4492565 := bbase (se 6 (by rfl) ⟨105294, by rfl⟩ : syracuseStep 4492565 = 210589) (by norm_num)
theorem B2995043 : Blo 1995435 2995043 := bstep (se 1 (by rfl) ⟨2246282, by rfl⟩ : syracuseStep 2995043 = 4492565) B4492565
theorem B1996695 : Blo 1995435 1996695 := bstep (se 1 (by rfl) ⟨1497521, by rfl⟩ : syracuseStep 1996695 = 2995043) B2995043
theorem B7581221 : Blo 1995435 7581221 := bbase (se 4 (by rfl) ⟨710739, by rfl⟩ : syracuseStep 7581221 = 1421479) (by norm_num)
theorem B5054147 : Blo 1995435 5054147 := bstep (se 1 (by rfl) ⟨3790610, by rfl⟩ : syracuseStep 5054147 = 7581221) B7581221
theorem B3369431 : Blo 1995435 3369431 := bstep (se 1 (by rfl) ⟨2527073, by rfl⟩ : syracuseStep 3369431 = 5054147) B5054147
theorem B2246287 : Blo 1995435 2246287 := bstep (se 1 (by rfl) ⟨1684715, by rfl⟩ : syracuseStep 2246287 = 3369431) B3369431
theorem B2995049 : Blo 1995435 2995049 := bstep (se 2 (by rfl) ⟨1123143, by rfl⟩ : syracuseStep 2995049 = 2246287) B2246287
theorem B1996699 : Blo 1995435 1996699 := bstep (se 1 (by rfl) ⟨1497524, by rfl⟩ : syracuseStep 1996699 = 2995049) B2995049
theorem B4264445 : Blo 1995435 4264445 := bbase (se 3 (by rfl) ⟨799583, by rfl⟩ : syracuseStep 4264445 = 1599167) (by norm_num)
theorem B11371853 : Blo 1995435 11371853 := bstep (se 3 (by rfl) ⟨2132222, by rfl⟩ : syracuseStep 11371853 = 4264445) B4264445
theorem B7581235 : Blo 1995435 7581235 := bstep (se 1 (by rfl) ⟨5685926, by rfl⟩ : syracuseStep 7581235 = 11371853) B11371853
theorem B10108313 : Blo 1995435 10108313 := bstep (se 2 (by rfl) ⟨3790617, by rfl⟩ : syracuseStep 10108313 = 7581235) B7581235
theorem B6738875 : Blo 1995435 6738875 := bstep (se 1 (by rfl) ⟨5054156, by rfl⟩ : syracuseStep 6738875 = 10108313) B10108313
theorem B4492583 : Blo 1995435 4492583 := bstep (se 1 (by rfl) ⟨3369437, by rfl⟩ : syracuseStep 4492583 = 6738875) B6738875
theorem B2995055 : Blo 1995435 2995055 := bstep (se 1 (by rfl) ⟨2246291, by rfl⟩ : syracuseStep 2995055 = 4492583) B4492583
theorem B1996703 : Blo 1995435 1996703 := bstep (se 1 (by rfl) ⟨1497527, by rfl⟩ : syracuseStep 1996703 = 2995055) B2995055
theorem B2995061 : Blo 1995435 2995061 := bbase (se 5 (by rfl) ⟨140393, by rfl⟩ : syracuseStep 2995061 = 280787) (by norm_num)
theorem B1996707 : Blo 1995435 1996707 := bstep (se 1 (by rfl) ⟨1497530, by rfl⟩ : syracuseStep 1996707 = 2995061) B2995061
theorem B14392565 : Blo 1995435 14392565 := bbase (se 5 (by rfl) ⟨674651, by rfl⟩ : syracuseStep 14392565 = 1349303) (by norm_num)
theorem B9595043 : Blo 1995435 9595043 := bstep (se 1 (by rfl) ⟨7196282, by rfl⟩ : syracuseStep 9595043 = 14392565) B14392565
theorem B6396695 : Blo 1995435 6396695 := bstep (se 1 (by rfl) ⟨4797521, by rfl⟩ : syracuseStep 6396695 = 9595043) B9595043
theorem B4264463 : Blo 1995435 4264463 := bstep (se 1 (by rfl) ⟨3198347, by rfl⟩ : syracuseStep 4264463 = 6396695) B6396695
theorem B2842975 : Blo 1995435 2842975 := bstep (se 1 (by rfl) ⟨2132231, by rfl⟩ : syracuseStep 2842975 = 4264463) B4264463
theorem B3790633 : Blo 1995435 3790633 := bstep (se 2 (by rfl) ⟨1421487, by rfl⟩ : syracuseStep 3790633 = 2842975) B2842975
theorem B5054177 : Blo 1995435 5054177 := bstep (se 2 (by rfl) ⟨1895316, by rfl⟩ : syracuseStep 5054177 = 3790633) B3790633
theorem B3369451 : Blo 1995435 3369451 := bstep (se 1 (by rfl) ⟨2527088, by rfl⟩ : syracuseStep 3369451 = 5054177) B5054177
theorem B4492601 : Blo 1995435 4492601 := bstep (se 2 (by rfl) ⟨1684725, by rfl⟩ : syracuseStep 4492601 = 3369451) B3369451
theorem B2995067 : Blo 1995435 2995067 := bstep (se 1 (by rfl) ⟨2246300, by rfl⟩ : syracuseStep 2995067 = 4492601) B4492601
theorem B1996711 : Blo 1995435 1996711 := bstep (se 1 (by rfl) ⟨1497533, by rfl⟩ : syracuseStep 1996711 = 2995067) B2995067
theorem B2246305 : Blo 1995435 2246305 := bbase (se 2 (by rfl) ⟨842364, by rfl⟩ : syracuseStep 2246305 = 1684729) (by norm_num)
theorem B2995073 : Blo 1995435 2995073 := bstep (se 2 (by rfl) ⟨1123152, by rfl⟩ : syracuseStep 2995073 = 2246305) B2246305
theorem B1996715 : Blo 1995435 1996715 := bstep (se 1 (by rfl) ⟨1497536, by rfl⟩ : syracuseStep 1996715 = 2995073) B2995073
theorem B5054197 : Blo 1995435 5054197 := bbase (se 5 (by rfl) ⟨236915, by rfl⟩ : syracuseStep 5054197 = 473831) (by norm_num)
theorem B6738929 : Blo 1995435 6738929 := bstep (se 2 (by rfl) ⟨2527098, by rfl⟩ : syracuseStep 6738929 = 5054197) B5054197
theorem B4492619 : Blo 1995435 4492619 := bstep (se 1 (by rfl) ⟨3369464, by rfl⟩ : syracuseStep 4492619 = 6738929) B6738929
theorem B2995079 : Blo 1995435 2995079 := bstep (se 1 (by rfl) ⟨2246309, by rfl⟩ : syracuseStep 2995079 = 4492619) B4492619
theorem B1996719 : Blo 1995435 1996719 := bstep (se 1 (by rfl) ⟨1497539, by rfl⟩ : syracuseStep 1996719 = 2995079) B2995079
theorem B2995085 : Blo 1995435 2995085 := bbase (se 3 (by rfl) ⟨561578, by rfl⟩ : syracuseStep 2995085 = 1123157) (by norm_num)
theorem B1996723 : Blo 1995435 1996723 := bstep (se 1 (by rfl) ⟨1497542, by rfl⟩ : syracuseStep 1996723 = 2995085) B2995085
theorem B4492637 : Blo 1995435 4492637 := bbase (se 3 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 4492637 = 1684739) (by norm_num)
theorem B2995091 : Blo 1995435 2995091 := bstep (se 1 (by rfl) ⟨2246318, by rfl⟩ : syracuseStep 2995091 = 4492637) B4492637
theorem B1996727 : Blo 1995435 1996727 := bstep (se 1 (by rfl) ⟨1497545, by rfl⟩ : syracuseStep 1996727 = 2995091) B2995091
theorem B3369485 : Blo 1995435 3369485 := bbase (se 3 (by rfl) ⟨631778, by rfl⟩ : syracuseStep 3369485 = 1263557) (by norm_num)
theorem B2246323 : Blo 1995435 2246323 := bstep (se 1 (by rfl) ⟨1684742, by rfl⟩ : syracuseStep 2246323 = 3369485) B3369485
theorem B2995097 : Blo 1995435 2995097 := bstep (se 2 (by rfl) ⟨1123161, by rfl⟩ : syracuseStep 2995097 = 2246323) B2246323
theorem B1996731 : Blo 1995435 1996731 := bstep (se 1 (by rfl) ⟨1497548, by rfl⟩ : syracuseStep 1996731 = 2995097) B2995097
theorem B2398789 : Blo 1995435 2398789 := bbase (se 4 (by rfl) ⟨224886, by rfl⟩ : syracuseStep 2398789 = 449773) (by norm_num)
theorem B3198385 : Blo 1995435 3198385 := bstep (se 2 (by rfl) ⟨1199394, by rfl⟩ : syracuseStep 3198385 = 2398789) B2398789
theorem B17058053 : Blo 1995435 17058053 := bstep (se 4 (by rfl) ⟨1599192, by rfl⟩ : syracuseStep 17058053 = 3198385) B3198385
theorem B11372035 : Blo 1995435 11372035 := bstep (se 1 (by rfl) ⟨8529026, by rfl⟩ : syracuseStep 11372035 = 17058053) B17058053
theorem B15162713 : Blo 1995435 15162713 := bstep (se 2 (by rfl) ⟨5686017, by rfl⟩ : syracuseStep 15162713 = 11372035) B11372035
theorem B10108475 : Blo 1995435 10108475 := bstep (se 1 (by rfl) ⟨7581356, by rfl⟩ : syracuseStep 10108475 = 15162713) B15162713
theorem B6738983 : Blo 1995435 6738983 := bstep (se 1 (by rfl) ⟨5054237, by rfl⟩ : syracuseStep 6738983 = 10108475) B10108475
theorem B4492655 : Blo 1995435 4492655 := bstep (se 1 (by rfl) ⟨3369491, by rfl⟩ : syracuseStep 4492655 = 6738983) B6738983
theorem B2995103 : Blo 1995435 2995103 := bstep (se 1 (by rfl) ⟨2246327, by rfl⟩ : syracuseStep 2995103 = 4492655) B4492655
theorem B1996735 : Blo 1995435 1996735 := bstep (se 1 (by rfl) ⟨1497551, by rfl⟩ : syracuseStep 1996735 = 2995103) B2995103
theorem B2995109 : Blo 1995435 2995109 := bbase (se 4 (by rfl) ⟨280791, by rfl⟩ : syracuseStep 2995109 = 561583) (by norm_num)
theorem B1996739 : Blo 1995435 1996739 := bstep (se 1 (by rfl) ⟨1497554, by rfl⟩ : syracuseStep 1996739 = 2995109) B2995109
theorem B2527129 : Blo 1995435 2527129 := bbase (se 2 (by rfl) ⟨947673, by rfl⟩ : syracuseStep 2527129 = 1895347) (by norm_num)
theorem B3369505 : Blo 1995435 3369505 := bstep (se 2 (by rfl) ⟨1263564, by rfl⟩ : syracuseStep 3369505 = 2527129) B2527129
theorem B4492673 : Blo 1995435 4492673 := bstep (se 2 (by rfl) ⟨1684752, by rfl⟩ : syracuseStep 4492673 = 3369505) B3369505
theorem B2995115 : Blo 1995435 2995115 := bstep (se 1 (by rfl) ⟨2246336, by rfl⟩ : syracuseStep 2995115 = 4492673) B4492673
theorem B1996743 : Blo 1995435 1996743 := bstep (se 1 (by rfl) ⟨1497557, by rfl⟩ : syracuseStep 1996743 = 2995115) B2995115
theorem B2246341 : Blo 1995435 2246341 := bbase (se 4 (by rfl) ⟨210594, by rfl⟩ : syracuseStep 2246341 = 421189) (by norm_num)
theorem B2995121 : Blo 1995435 2995121 := bstep (se 2 (by rfl) ⟨1123170, by rfl⟩ : syracuseStep 2995121 = 2246341) B2246341
theorem B1996747 : Blo 1995435 1996747 := bstep (se 1 (by rfl) ⟨1497560, by rfl⟩ : syracuseStep 1996747 = 2995121) B2995121
theorem B3790709 : Blo 1995435 3790709 := bbase (se 5 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 3790709 = 355379) (by norm_num)
theorem B2527139 : Blo 1995435 2527139 := bstep (se 1 (by rfl) ⟨1895354, by rfl⟩ : syracuseStep 2527139 = 3790709) B3790709
theorem B6739037 : Blo 1995435 6739037 := bstep (se 3 (by rfl) ⟨1263569, by rfl⟩ : syracuseStep 6739037 = 2527139) B2527139
theorem B4492691 : Blo 1995435 4492691 := bstep (se 1 (by rfl) ⟨3369518, by rfl⟩ : syracuseStep 4492691 = 6739037) B6739037
theorem B2995127 : Blo 1995435 2995127 := bstep (se 1 (by rfl) ⟨2246345, by rfl⟩ : syracuseStep 2995127 = 4492691) B4492691
theorem B1996751 : Blo 1995435 1996751 := bstep (se 1 (by rfl) ⟨1497563, by rfl⟩ : syracuseStep 1996751 = 2995127) B2995127
theorem B2995133 : Blo 1995435 2995133 := bbase (se 3 (by rfl) ⟨561587, by rfl⟩ : syracuseStep 2995133 = 1123175) (by norm_num)
theorem B1996755 : Blo 1995435 1996755 := bstep (se 1 (by rfl) ⟨1497566, by rfl⟩ : syracuseStep 1996755 = 2995133) B2995133
theorem B4492709 : Blo 1995435 4492709 := bbase (se 4 (by rfl) ⟨421191, by rfl⟩ : syracuseStep 4492709 = 842383) (by norm_num)
theorem B2995139 : Blo 1995435 2995139 := bstep (se 1 (by rfl) ⟨2246354, by rfl⟩ : syracuseStep 2995139 = 4492709) B4492709
theorem B1996759 : Blo 1995435 1996759 := bstep (se 1 (by rfl) ⟨1497569, by rfl⟩ : syracuseStep 1996759 = 2995139) B2995139
theorem B5054309 : Blo 1995435 5054309 := bbase (se 4 (by rfl) ⟨473841, by rfl⟩ : syracuseStep 5054309 = 947683) (by norm_num)
theorem B3369539 : Blo 1995435 3369539 := bstep (se 1 (by rfl) ⟨2527154, by rfl⟩ : syracuseStep 3369539 = 5054309) B5054309
theorem B2246359 : Blo 1995435 2246359 := bstep (se 1 (by rfl) ⟨1684769, by rfl⟩ : syracuseStep 2246359 = 3369539) B3369539
theorem B2995145 : Blo 1995435 2995145 := bstep (se 2 (by rfl) ⟨1123179, by rfl⟩ : syracuseStep 2995145 = 2246359) B2246359
theorem B1996763 : Blo 1995435 1996763 := bstep (se 1 (by rfl) ⟨1497572, by rfl⟩ : syracuseStep 1996763 = 2995145) B2995145
theorem B3198437 : Blo 1995435 3198437 := bbase (se 4 (by rfl) ⟨299853, by rfl⟩ : syracuseStep 3198437 = 599707) (by norm_num)
theorem B2132291 : Blo 1995435 2132291 := bstep (se 1 (by rfl) ⟨1599218, by rfl⟩ : syracuseStep 2132291 = 3198437) B3198437
theorem B5686109 : Blo 1995435 5686109 := bstep (se 3 (by rfl) ⟨1066145, by rfl⟩ : syracuseStep 5686109 = 2132291) B2132291
theorem B3790739 : Blo 1995435 3790739 := bstep (se 1 (by rfl) ⟨2843054, by rfl⟩ : syracuseStep 3790739 = 5686109) B5686109
theorem B10108637 : Blo 1995435 10108637 := bstep (se 3 (by rfl) ⟨1895369, by rfl⟩ : syracuseStep 10108637 = 3790739) B3790739
theorem B6739091 : Blo 1995435 6739091 := bstep (se 1 (by rfl) ⟨5054318, by rfl⟩ : syracuseStep 6739091 = 10108637) B10108637
theorem B4492727 : Blo 1995435 4492727 := bstep (se 1 (by rfl) ⟨3369545, by rfl⟩ : syracuseStep 4492727 = 6739091) B6739091
theorem B2995151 : Blo 1995435 2995151 := bstep (se 1 (by rfl) ⟨2246363, by rfl⟩ : syracuseStep 2995151 = 4492727) B4492727
theorem B1996767 : Blo 1995435 1996767 := bstep (se 1 (by rfl) ⟨1497575, by rfl⟩ : syracuseStep 1996767 = 2995151) B2995151
theorem B2995157 : Blo 1995435 2995157 := bbase (se 7 (by rfl) ⟨35099, by rfl⟩ : syracuseStep 2995157 = 70199) (by norm_num)
theorem B1996771 : Blo 1995435 1996771 := bstep (se 1 (by rfl) ⟨1497578, by rfl⟩ : syracuseStep 1996771 = 2995157) B2995157
theorem B7581509 : Blo 1995435 7581509 := bbase (se 4 (by rfl) ⟨710766, by rfl⟩ : syracuseStep 7581509 = 1421533) (by norm_num)
theorem B5054339 : Blo 1995435 5054339 := bstep (se 1 (by rfl) ⟨3790754, by rfl⟩ : syracuseStep 5054339 = 7581509) B7581509
theorem B3369559 : Blo 1995435 3369559 := bstep (se 1 (by rfl) ⟨2527169, by rfl⟩ : syracuseStep 3369559 = 5054339) B5054339
theorem B4492745 : Blo 1995435 4492745 := bstep (se 2 (by rfl) ⟨1684779, by rfl⟩ : syracuseStep 4492745 = 3369559) B3369559
theorem B2995163 : Blo 1995435 2995163 := bstep (se 1 (by rfl) ⟨2246372, by rfl⟩ : syracuseStep 2995163 = 4492745) B4492745
theorem B1996775 : Blo 1995435 1996775 := bstep (se 1 (by rfl) ⟨1497581, by rfl⟩ : syracuseStep 1996775 = 2995163) B2995163
theorem B2246377 : Blo 1995435 2246377 := bbase (se 2 (by rfl) ⟨842391, by rfl⟩ : syracuseStep 2246377 = 1684783) (by norm_num)
theorem B2995169 : Blo 1995435 2995169 := bstep (se 2 (by rfl) ⟨1123188, by rfl⟩ : syracuseStep 2995169 = 2246377) B2246377
theorem B1996779 : Blo 1995435 1996779 := bstep (se 1 (by rfl) ⟨1497584, by rfl⟩ : syracuseStep 1996779 = 2995169) B2995169
theorem B11372309 : Blo 1995435 11372309 := bbase (se 6 (by rfl) ⟨266538, by rfl⟩ : syracuseStep 11372309 = 533077) (by norm_num)
theorem B7581539 : Blo 1995435 7581539 := bstep (se 1 (by rfl) ⟨5686154, by rfl⟩ : syracuseStep 7581539 = 11372309) B11372309
theorem B5054359 : Blo 1995435 5054359 := bstep (se 1 (by rfl) ⟨3790769, by rfl⟩ : syracuseStep 5054359 = 7581539) B7581539
theorem B6739145 : Blo 1995435 6739145 := bstep (se 2 (by rfl) ⟨2527179, by rfl⟩ : syracuseStep 6739145 = 5054359) B5054359
theorem B4492763 : Blo 1995435 4492763 := bstep (se 1 (by rfl) ⟨3369572, by rfl⟩ : syracuseStep 4492763 = 6739145) B6739145
theorem B2995175 : Blo 1995435 2995175 := bstep (se 1 (by rfl) ⟨2246381, by rfl⟩ : syracuseStep 2995175 = 4492763) B4492763
theorem B1996783 : Blo 1995435 1996783 := bstep (se 1 (by rfl) ⟨1497587, by rfl⟩ : syracuseStep 1996783 = 2995175) B2995175
theorem B2995181 : Blo 1995435 2995181 := bbase (se 3 (by rfl) ⟨561596, by rfl⟩ : syracuseStep 2995181 = 1123193) (by norm_num)
theorem B1996787 : Blo 1995435 1996787 := bstep (se 1 (by rfl) ⟨1497590, by rfl⟩ : syracuseStep 1996787 = 2995181) B2995181
theorem B4492781 : Blo 1995435 4492781 := bbase (se 3 (by rfl) ⟨842396, by rfl⟩ : syracuseStep 4492781 = 1684793) (by norm_num)
theorem B2995187 : Blo 1995435 2995187 := bstep (se 1 (by rfl) ⟨2246390, by rfl⟩ : syracuseStep 2995187 = 4492781) B4492781
theorem B1996791 : Blo 1995435 1996791 := bstep (se 1 (by rfl) ⟨1497593, by rfl⟩ : syracuseStep 1996791 = 2995187) B2995187
theorem B6396965 : Blo 1995435 6396965 := bbase (se 4 (by rfl) ⟨599715, by rfl⟩ : syracuseStep 6396965 = 1199431) (by norm_num)
theorem B4264643 : Blo 1995435 4264643 := bstep (se 1 (by rfl) ⟨3198482, by rfl⟩ : syracuseStep 4264643 = 6396965) B6396965
theorem B2843095 : Blo 1995435 2843095 := bstep (se 1 (by rfl) ⟨2132321, by rfl⟩ : syracuseStep 2843095 = 4264643) B4264643
theorem B3790793 : Blo 1995435 3790793 := bstep (se 2 (by rfl) ⟨1421547, by rfl⟩ : syracuseStep 3790793 = 2843095) B2843095
theorem B2527195 : Blo 1995435 2527195 := bstep (se 1 (by rfl) ⟨1895396, by rfl⟩ : syracuseStep 2527195 = 3790793) B3790793
theorem B3369593 : Blo 1995435 3369593 := bstep (se 2 (by rfl) ⟨1263597, by rfl⟩ : syracuseStep 3369593 = 2527195) B2527195
theorem B2246395 : Blo 1995435 2246395 := bstep (se 1 (by rfl) ⟨1684796, by rfl⟩ : syracuseStep 2246395 = 3369593) B3369593
theorem B2995193 : Blo 1995435 2995193 := bstep (se 2 (by rfl) ⟨1123197, by rfl⟩ : syracuseStep 2995193 = 2246395) B2246395
theorem B1996795 : Blo 1995435 1996795 := bstep (se 1 (by rfl) ⟨1497596, by rfl⟩ : syracuseStep 1996795 = 2995193) B2995193
theorem B19452757 : Blo 1995435 19452757 := bbase (se 9 (by rfl) ⟨56990, by rfl⟩ : syracuseStep 19452757 = 113981) (by norm_num)
theorem B25937009 : Blo 1995435 25937009 := bstep (se 2 (by rfl) ⟨9726378, by rfl⟩ : syracuseStep 25937009 = 19452757) B19452757
theorem B17291339 : Blo 1995435 17291339 := bstep (se 1 (by rfl) ⟨12968504, by rfl⟩ : syracuseStep 17291339 = 25937009) B25937009
theorem B11527559 : Blo 1995435 11527559 := bstep (se 1 (by rfl) ⟨8645669, by rfl⟩ : syracuseStep 11527559 = 17291339) B17291339
theorem B7685039 : Blo 1995435 7685039 := bstep (se 1 (by rfl) ⟨5763779, by rfl⟩ : syracuseStep 7685039 = 11527559) B11527559
theorem B5123359 : Blo 1995435 5123359 := bstep (se 1 (by rfl) ⟨3842519, by rfl⟩ : syracuseStep 5123359 = 7685039) B7685039
theorem B6831145 : Blo 1995435 6831145 := bstep (se 2 (by rfl) ⟨2561679, by rfl⟩ : syracuseStep 6831145 = 5123359) B5123359
theorem B36432773 : Blo 1995435 36432773 := bstep (se 4 (by rfl) ⟨3415572, by rfl⟩ : syracuseStep 36432773 = 6831145) B6831145
theorem B24288515 : Blo 1995435 24288515 := bstep (se 1 (by rfl) ⟨18216386, by rfl⟩ : syracuseStep 24288515 = 36432773) B36432773
theorem B16192343 : Blo 1995435 16192343 := bstep (se 1 (by rfl) ⟨12144257, by rfl⟩ : syracuseStep 16192343 = 24288515) B24288515
theorem B43179581 : Blo 1995435 43179581 := bstep (se 3 (by rfl) ⟨8096171, by rfl⟩ : syracuseStep 43179581 = 16192343) B16192343
theorem B115145549 : Blo 1995435 115145549 := bstep (se 3 (by rfl) ⟨21589790, by rfl⟩ : syracuseStep 115145549 = 43179581) B43179581
theorem B76763699 : Blo 1995435 76763699 := bstep (se 1 (by rfl) ⟨57572774, by rfl⟩ : syracuseStep 76763699 = 115145549) B115145549
theorem B51175799 : Blo 1995435 51175799 := bstep (se 1 (by rfl) ⟨38381849, by rfl⟩ : syracuseStep 51175799 = 76763699) B76763699
theorem B34117199 : Blo 1995435 34117199 := bstep (se 1 (by rfl) ⟨25587899, by rfl⟩ : syracuseStep 34117199 = 51175799) B51175799
theorem B22744799 : Blo 1995435 22744799 := bstep (se 1 (by rfl) ⟨17058599, by rfl⟩ : syracuseStep 22744799 = 34117199) B34117199
theorem B15163199 : Blo 1995435 15163199 := bstep (se 1 (by rfl) ⟨11372399, by rfl⟩ : syracuseStep 15163199 = 22744799) B22744799
theorem B10108799 : Blo 1995435 10108799 := bstep (se 1 (by rfl) ⟨7581599, by rfl⟩ : syracuseStep 10108799 = 15163199) B15163199
theorem B6739199 : Blo 1995435 6739199 := bstep (se 1 (by rfl) ⟨5054399, by rfl⟩ : syracuseStep 6739199 = 10108799) B10108799
theorem B4492799 : Blo 1995435 4492799 := bstep (se 1 (by rfl) ⟨3369599, by rfl⟩ : syracuseStep 4492799 = 6739199) B6739199
theorem B2995199 : Blo 1995435 2995199 := bstep (se 1 (by rfl) ⟨2246399, by rfl⟩ : syracuseStep 2995199 = 4492799) B4492799
theorem B1996799 : Blo 1995435 1996799 := bstep (se 1 (by rfl) ⟨1497599, by rfl⟩ : syracuseStep 1996799 = 2995199) B2995199
theorem B2995205 : Blo 1995435 2995205 := bbase (se 4 (by rfl) ⟨280800, by rfl⟩ : syracuseStep 2995205 = 561601) (by norm_num)
theorem B1996803 : Blo 1995435 1996803 := bstep (se 1 (by rfl) ⟨1497602, by rfl⟩ : syracuseStep 1996803 = 2995205) B2995205
theorem B3369613 : Blo 1995435 3369613 := bbase (se 3 (by rfl) ⟨631802, by rfl⟩ : syracuseStep 3369613 = 1263605) (by norm_num)
theorem B4492817 : Blo 1995435 4492817 := bstep (se 2 (by rfl) ⟨1684806, by rfl⟩ : syracuseStep 4492817 = 3369613) B3369613
theorem B2995211 : Blo 1995435 2995211 := bstep (se 1 (by rfl) ⟨2246408, by rfl⟩ : syracuseStep 2995211 = 4492817) B4492817
theorem B1996807 : Blo 1995435 1996807 := bstep (se 1 (by rfl) ⟨1497605, by rfl⟩ : syracuseStep 1996807 = 2995211) B2995211
theorem B2246413 : Blo 1995435 2246413 := bbase (se 3 (by rfl) ⟨421202, by rfl⟩ : syracuseStep 2246413 = 842405) (by norm_num)
theorem B2995217 : Blo 1995435 2995217 := bstep (se 2 (by rfl) ⟨1123206, by rfl⟩ : syracuseStep 2995217 = 2246413) B2246413
theorem B1996811 : Blo 1995435 1996811 := bstep (se 1 (by rfl) ⟨1497608, by rfl⟩ : syracuseStep 1996811 = 2995217) B2995217
theorem B6739253 : Blo 1995435 6739253 := bbase (se 5 (by rfl) ⟨315902, by rfl⟩ : syracuseStep 6739253 = 631805) (by norm_num)
theorem B4492835 : Blo 1995435 4492835 := bstep (se 1 (by rfl) ⟨3369626, by rfl⟩ : syracuseStep 4492835 = 6739253) B6739253
theorem B2995223 : Blo 1995435 2995223 := bstep (se 1 (by rfl) ⟨2246417, by rfl⟩ : syracuseStep 2995223 = 4492835) B4492835
theorem B1996815 : Blo 1995435 1996815 := bstep (se 1 (by rfl) ⟨1497611, by rfl⟩ : syracuseStep 1996815 = 2995223) B2995223
theorem B2995229 : Blo 1995435 2995229 := bbase (se 3 (by rfl) ⟨561605, by rfl⟩ : syracuseStep 2995229 = 1123211) (by norm_num)
theorem B1996819 : Blo 1995435 1996819 := bstep (se 1 (by rfl) ⟨1497614, by rfl⟩ : syracuseStep 1996819 = 2995229) B2995229
theorem B4492853 : Blo 1995435 4492853 := bbase (se 5 (by rfl) ⟨210602, by rfl⟩ : syracuseStep 4492853 = 421205) (by norm_num)
theorem B2995235 : Blo 1995435 2995235 := bstep (se 1 (by rfl) ⟨2246426, by rfl⟩ : syracuseStep 2995235 = 4492853) B4492853
theorem B1996823 : Blo 1995435 1996823 := bstep (se 1 (by rfl) ⟨1497617, by rfl⟩ : syracuseStep 1996823 = 2995235) B2995235
theorem B3198533 : Blo 1995435 3198533 := bbase (se 4 (by rfl) ⟨299862, by rfl⟩ : syracuseStep 3198533 = 599725) (by norm_num)
theorem B8529421 : Blo 1995435 8529421 := bstep (se 3 (by rfl) ⟨1599266, by rfl⟩ : syracuseStep 8529421 = 3198533) B3198533
theorem B11372561 : Blo 1995435 11372561 := bstep (se 2 (by rfl) ⟨4264710, by rfl⟩ : syracuseStep 11372561 = 8529421) B8529421
theorem B7581707 : Blo 1995435 7581707 := bstep (se 1 (by rfl) ⟨5686280, by rfl⟩ : syracuseStep 7581707 = 11372561) B11372561
theorem B5054471 : Blo 1995435 5054471 := bstep (se 1 (by rfl) ⟨3790853, by rfl⟩ : syracuseStep 5054471 = 7581707) B7581707
theorem B3369647 : Blo 1995435 3369647 := bstep (se 1 (by rfl) ⟨2527235, by rfl⟩ : syracuseStep 3369647 = 5054471) B5054471
theorem B2246431 : Blo 1995435 2246431 := bstep (se 1 (by rfl) ⟨1684823, by rfl⟩ : syracuseStep 2246431 = 3369647) B3369647
theorem B2995241 : Blo 1995435 2995241 := bstep (se 2 (by rfl) ⟨1123215, by rfl⟩ : syracuseStep 2995241 = 2246431) B2246431
theorem B1996827 : Blo 1995435 1996827 := bstep (se 1 (by rfl) ⟨1497620, by rfl⟩ : syracuseStep 1996827 = 2995241) B2995241
theorem B3598357 : Blo 1995435 3598357 := bbase (se 6 (by rfl) ⟨84336, by rfl⟩ : syracuseStep 3598357 = 168673) (by norm_num)
theorem B4797809 : Blo 1995435 4797809 := bstep (se 2 (by rfl) ⟨1799178, by rfl⟩ : syracuseStep 4797809 = 3598357) B3598357
theorem B3198539 : Blo 1995435 3198539 := bstep (se 1 (by rfl) ⟨2398904, by rfl⟩ : syracuseStep 3198539 = 4797809) B4797809
theorem B8529437 : Blo 1995435 8529437 := bstep (se 3 (by rfl) ⟨1599269, by rfl⟩ : syracuseStep 8529437 = 3198539) B3198539
theorem B5686291 : Blo 1995435 5686291 := bstep (se 1 (by rfl) ⟨4264718, by rfl⟩ : syracuseStep 5686291 = 8529437) B8529437
theorem B7581721 : Blo 1995435 7581721 := bstep (se 2 (by rfl) ⟨2843145, by rfl⟩ : syracuseStep 7581721 = 5686291) B5686291
theorem B10108961 : Blo 1995435 10108961 := bstep (se 2 (by rfl) ⟨3790860, by rfl⟩ : syracuseStep 10108961 = 7581721) B7581721
theorem B6739307 : Blo 1995435 6739307 := bstep (se 1 (by rfl) ⟨5054480, by rfl⟩ : syracuseStep 6739307 = 10108961) B10108961
theorem B4492871 : Blo 1995435 4492871 := bstep (se 1 (by rfl) ⟨3369653, by rfl⟩ : syracuseStep 4492871 = 6739307) B6739307
theorem B2995247 : Blo 1995435 2995247 := bstep (se 1 (by rfl) ⟨2246435, by rfl⟩ : syracuseStep 2995247 = 4492871) B4492871
theorem B1996831 : Blo 1995435 1996831 := bstep (se 1 (by rfl) ⟨1497623, by rfl⟩ : syracuseStep 1996831 = 2995247) B2995247
theorem B2995253 : Blo 1995435 2995253 := bbase (se 5 (by rfl) ⟨140402, by rfl⟩ : syracuseStep 2995253 = 280805) (by norm_num)
theorem B1996835 : Blo 1995435 1996835 := bstep (se 1 (by rfl) ⟨1497626, by rfl⟩ : syracuseStep 1996835 = 2995253) B2995253
theorem B5054501 : Blo 1995435 5054501 := bbase (se 4 (by rfl) ⟨473859, by rfl⟩ : syracuseStep 5054501 = 947719) (by norm_num)
theorem B3369667 : Blo 1995435 3369667 := bstep (se 1 (by rfl) ⟨2527250, by rfl⟩ : syracuseStep 3369667 = 5054501) B5054501
theorem B4492889 : Blo 1995435 4492889 := bstep (se 2 (by rfl) ⟨1684833, by rfl⟩ : syracuseStep 4492889 = 3369667) B3369667
theorem B2995259 : Blo 1995435 2995259 := bstep (se 1 (by rfl) ⟨2246444, by rfl⟩ : syracuseStep 2995259 = 4492889) B4492889
theorem B1996839 : Blo 1995435 1996839 := bstep (se 1 (by rfl) ⟨1497629, by rfl⟩ : syracuseStep 1996839 = 2995259) B2995259
theorem B2246449 : Blo 1995435 2246449 := bbase (se 2 (by rfl) ⟨842418, by rfl⟩ : syracuseStep 2246449 = 1684837) (by norm_num)
theorem B2995265 : Blo 1995435 2995265 := bstep (se 2 (by rfl) ⟨1123224, by rfl⟩ : syracuseStep 2995265 = 2246449) B2246449
theorem B1996843 : Blo 1995435 1996843 := bstep (se 1 (by rfl) ⟨1497632, by rfl⟩ : syracuseStep 1996843 = 2995265) B2995265
theorem B3198565 : Blo 1995435 3198565 := bbase (se 4 (by rfl) ⟨299865, by rfl⟩ : syracuseStep 3198565 = 599731) (by norm_num)
theorem B4264753 : Blo 1995435 4264753 := bstep (se 2 (by rfl) ⟨1599282, by rfl⟩ : syracuseStep 4264753 = 3198565) B3198565
theorem B5686337 : Blo 1995435 5686337 := bstep (se 2 (by rfl) ⟨2132376, by rfl⟩ : syracuseStep 5686337 = 4264753) B4264753
theorem B3790891 : Blo 1995435 3790891 := bstep (se 1 (by rfl) ⟨2843168, by rfl⟩ : syracuseStep 3790891 = 5686337) B5686337
theorem B5054521 : Blo 1995435 5054521 := bstep (se 2 (by rfl) ⟨1895445, by rfl⟩ : syracuseStep 5054521 = 3790891) B3790891
theorem B6739361 : Blo 1995435 6739361 := bstep (se 2 (by rfl) ⟨2527260, by rfl⟩ : syracuseStep 6739361 = 5054521) B5054521
theorem B4492907 : Blo 1995435 4492907 := bstep (se 1 (by rfl) ⟨3369680, by rfl⟩ : syracuseStep 4492907 = 6739361) B6739361
theorem B2995271 : Blo 1995435 2995271 := bstep (se 1 (by rfl) ⟨2246453, by rfl⟩ : syracuseStep 2995271 = 4492907) B4492907
theorem B1996847 : Blo 1995435 1996847 := bstep (se 1 (by rfl) ⟨1497635, by rfl⟩ : syracuseStep 1996847 = 2995271) B2995271
theorem B2995277 : Blo 1995435 2995277 := bbase (se 3 (by rfl) ⟨561614, by rfl⟩ : syracuseStep 2995277 = 1123229) (by norm_num)
theorem B1996851 : Blo 1995435 1996851 := bstep (se 1 (by rfl) ⟨1497638, by rfl⟩ : syracuseStep 1996851 = 2995277) B2995277
theorem B4492925 : Blo 1995435 4492925 := bbase (se 3 (by rfl) ⟨842423, by rfl⟩ : syracuseStep 4492925 = 1684847) (by norm_num)
theorem B2995283 : Blo 1995435 2995283 := bstep (se 1 (by rfl) ⟨2246462, by rfl⟩ : syracuseStep 2995283 = 4492925) B4492925
theorem B1996855 : Blo 1995435 1996855 := bstep (se 1 (by rfl) ⟨1497641, by rfl⟩ : syracuseStep 1996855 = 2995283) B2995283
theorem B3369701 : Blo 1995435 3369701 := bbase (se 4 (by rfl) ⟨315909, by rfl⟩ : syracuseStep 3369701 = 631819) (by norm_num)
theorem B2246467 : Blo 1995435 2246467 := bstep (se 1 (by rfl) ⟨1684850, by rfl⟩ : syracuseStep 2246467 = 3369701) B3369701
theorem B2995289 : Blo 1995435 2995289 := bstep (se 2 (by rfl) ⟨1123233, by rfl⟩ : syracuseStep 2995289 = 2246467) B2246467
theorem B1996859 : Blo 1995435 1996859 := bstep (se 1 (by rfl) ⟨1497644, by rfl⟩ : syracuseStep 1996859 = 2995289) B2995289
theorem B4554245 : Blo 1995435 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B12144653 : Blo 1995435 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B8096435 : Blo 1995435 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B5397623 : Blo 1995435 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B3598415 : Blo 1995435 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B2398943 : Blo 1995435 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B6397181 : Blo 1995435 6397181 := bstep (se 3 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 6397181 = 2398943) B2398943
theorem B4264787 : Blo 1995435 4264787 := bstep (se 1 (by rfl) ⟨3198590, by rfl⟩ : syracuseStep 4264787 = 6397181) B6397181
theorem B2843191 : Blo 1995435 2843191 := bstep (se 1 (by rfl) ⟨2132393, by rfl⟩ : syracuseStep 2843191 = 4264787) B4264787
theorem B15163685 : Blo 1995435 15163685 := bstep (se 4 (by rfl) ⟨1421595, by rfl⟩ : syracuseStep 15163685 = 2843191) B2843191
theorem B10109123 : Blo 1995435 10109123 := bstep (se 1 (by rfl) ⟨7581842, by rfl⟩ : syracuseStep 10109123 = 15163685) B15163685
theorem B6739415 : Blo 1995435 6739415 := bstep (se 1 (by rfl) ⟨5054561, by rfl⟩ : syracuseStep 6739415 = 10109123) B10109123
theorem B4492943 : Blo 1995435 4492943 := bstep (se 1 (by rfl) ⟨3369707, by rfl⟩ : syracuseStep 4492943 = 6739415) B6739415
theorem B2995295 : Blo 1995435 2995295 := bstep (se 1 (by rfl) ⟨2246471, by rfl⟩ : syracuseStep 2995295 = 4492943) B4492943
theorem B1996863 : Blo 1995435 1996863 := bstep (se 1 (by rfl) ⟨1497647, by rfl⟩ : syracuseStep 1996863 = 2995295) B2995295
theorem B2995301 : Blo 1995435 2995301 := bbase (se 4 (by rfl) ⟨280809, by rfl⟩ : syracuseStep 2995301 = 561619) (by norm_num)
theorem B1996867 : Blo 1995435 1996867 := bstep (se 1 (by rfl) ⟨1497650, by rfl⟩ : syracuseStep 1996867 = 2995301) B2995301
theorem B4264805 : Blo 1995435 4264805 := bbase (se 4 (by rfl) ⟨399825, by rfl⟩ : syracuseStep 4264805 = 799651) (by norm_num)
theorem B2843203 : Blo 1995435 2843203 := bstep (se 1 (by rfl) ⟨2132402, by rfl⟩ : syracuseStep 2843203 = 4264805) B4264805
theorem B3790937 : Blo 1995435 3790937 := bstep (se 2 (by rfl) ⟨1421601, by rfl⟩ : syracuseStep 3790937 = 2843203) B2843203
theorem B2527291 : Blo 1995435 2527291 := bstep (se 1 (by rfl) ⟨1895468, by rfl⟩ : syracuseStep 2527291 = 3790937) B3790937
theorem B3369721 : Blo 1995435 3369721 := bstep (se 2 (by rfl) ⟨1263645, by rfl⟩ : syracuseStep 3369721 = 2527291) B2527291
theorem B4492961 : Blo 1995435 4492961 := bstep (se 2 (by rfl) ⟨1684860, by rfl⟩ : syracuseStep 4492961 = 3369721) B3369721
theorem B2995307 : Blo 1995435 2995307 := bstep (se 1 (by rfl) ⟨2246480, by rfl⟩ : syracuseStep 2995307 = 4492961) B4492961
theorem B1996871 : Blo 1995435 1996871 := bstep (se 1 (by rfl) ⟨1497653, by rfl⟩ : syracuseStep 1996871 = 2995307) B2995307
theorem B2246485 : Blo 1995435 2246485 := bbase (se 9 (by rfl) ⟨6581, by rfl⟩ : syracuseStep 2246485 = 13163) (by norm_num)
theorem B2995313 : Blo 1995435 2995313 := bstep (se 2 (by rfl) ⟨1123242, by rfl⟩ : syracuseStep 2995313 = 2246485) B2246485
theorem B1996875 : Blo 1995435 1996875 := bstep (se 1 (by rfl) ⟨1497656, by rfl⟩ : syracuseStep 1996875 = 2995313) B2995313
theorem B2527301 : Blo 1995435 2527301 := bbase (se 4 (by rfl) ⟨236934, by rfl⟩ : syracuseStep 2527301 = 473869) (by norm_num)
theorem B6739469 : Blo 1995435 6739469 := bstep (se 3 (by rfl) ⟨1263650, by rfl⟩ : syracuseStep 6739469 = 2527301) B2527301
theorem B4492979 : Blo 1995435 4492979 := bstep (se 1 (by rfl) ⟨3369734, by rfl⟩ : syracuseStep 4492979 = 6739469) B6739469
theorem B2995319 : Blo 1995435 2995319 := bstep (se 1 (by rfl) ⟨2246489, by rfl⟩ : syracuseStep 2995319 = 4492979) B4492979
theorem B1996879 : Blo 1995435 1996879 := bstep (se 1 (by rfl) ⟨1497659, by rfl⟩ : syracuseStep 1996879 = 2995319) B2995319
theorem B2995325 : Blo 1995435 2995325 := bbase (se 3 (by rfl) ⟨561623, by rfl⟩ : syracuseStep 2995325 = 1123247) (by norm_num)
theorem B1996883 : Blo 1995435 1996883 := bstep (se 1 (by rfl) ⟨1497662, by rfl⟩ : syracuseStep 1996883 = 2995325) B2995325
theorem B4492997 : Blo 1995435 4492997 := bbase (se 4 (by rfl) ⟨421218, by rfl⟩ : syracuseStep 4492997 = 842437) (by norm_num)
theorem B2995331 : Blo 1995435 2995331 := bstep (se 1 (by rfl) ⟨2246498, by rfl⟩ : syracuseStep 2995331 = 4492997) B4492997
theorem B1996887 : Blo 1995435 1996887 := bstep (se 1 (by rfl) ⟨1497665, by rfl⟩ : syracuseStep 1996887 = 2995331) B2995331
theorem B12144821 : Blo 1995435 12144821 := bbase (se 5 (by rfl) ⟨569288, by rfl⟩ : syracuseStep 12144821 = 1138577) (by norm_num)
theorem B32386189 : Blo 1995435 32386189 := bstep (se 3 (by rfl) ⟨6072410, by rfl⟩ : syracuseStep 32386189 = 12144821) B12144821
theorem B43181585 : Blo 1995435 43181585 := bstep (se 2 (by rfl) ⟨16193094, by rfl⟩ : syracuseStep 43181585 = 32386189) B32386189
theorem B28787723 : Blo 1995435 28787723 := bstep (se 1 (by rfl) ⟨21590792, by rfl⟩ : syracuseStep 28787723 = 43181585) B43181585
theorem B19191815 : Blo 1995435 19191815 := bstep (se 1 (by rfl) ⟨14393861, by rfl⟩ : syracuseStep 19191815 = 28787723) B28787723
theorem B12794543 : Blo 1995435 12794543 := bstep (se 1 (by rfl) ⟨9595907, by rfl⟩ : syracuseStep 12794543 = 19191815) B19191815
theorem B8529695 : Blo 1995435 8529695 := bstep (se 1 (by rfl) ⟨6397271, by rfl⟩ : syracuseStep 8529695 = 12794543) B12794543
theorem B5686463 : Blo 1995435 5686463 := bstep (se 1 (by rfl) ⟨4264847, by rfl⟩ : syracuseStep 5686463 = 8529695) B8529695
theorem B3790975 : Blo 1995435 3790975 := bstep (se 1 (by rfl) ⟨2843231, by rfl⟩ : syracuseStep 3790975 = 5686463) B5686463
theorem B5054633 : Blo 1995435 5054633 := bstep (se 2 (by rfl) ⟨1895487, by rfl⟩ : syracuseStep 5054633 = 3790975) B3790975
theorem B3369755 : Blo 1995435 3369755 := bstep (se 1 (by rfl) ⟨2527316, by rfl⟩ : syracuseStep 3369755 = 5054633) B5054633
theorem B2246503 : Blo 1995435 2246503 := bstep (se 1 (by rfl) ⟨1684877, by rfl⟩ : syracuseStep 2246503 = 3369755) B3369755
theorem B2995337 : Blo 1995435 2995337 := bstep (se 2 (by rfl) ⟨1123251, by rfl⟩ : syracuseStep 2995337 = 2246503) B2246503
theorem B1996891 : Blo 1995435 1996891 := bstep (se 1 (by rfl) ⟨1497668, by rfl⟩ : syracuseStep 1996891 = 2995337) B2995337
theorem B10109285 : Blo 1995435 10109285 := bbase (se 4 (by rfl) ⟨947745, by rfl⟩ : syracuseStep 10109285 = 1895491) (by norm_num)
theorem B6739523 : Blo 1995435 6739523 := bstep (se 1 (by rfl) ⟨5054642, by rfl⟩ : syracuseStep 6739523 = 10109285) B10109285
theorem B4493015 : Blo 1995435 4493015 := bstep (se 1 (by rfl) ⟨3369761, by rfl⟩ : syracuseStep 4493015 = 6739523) B6739523
theorem B2995343 : Blo 1995435 2995343 := bstep (se 1 (by rfl) ⟨2246507, by rfl⟩ : syracuseStep 2995343 = 4493015) B4493015
theorem B1996895 : Blo 1995435 1996895 := bstep (se 1 (by rfl) ⟨1497671, by rfl⟩ : syracuseStep 1996895 = 2995343) B2995343
theorem B2995349 : Blo 1995435 2995349 := bbase (se 6 (by rfl) ⟨70203, by rfl⟩ : syracuseStep 2995349 = 140407) (by norm_num)
theorem B1996899 : Blo 1995435 1996899 := bstep (se 1 (by rfl) ⟨1497674, by rfl⟩ : syracuseStep 1996899 = 2995349) B2995349
theorem B8096597 : Blo 1995435 8096597 := bbase (se 9 (by rfl) ⟨23720, by rfl⟩ : syracuseStep 8096597 = 47441) (by norm_num)
theorem B5397731 : Blo 1995435 5397731 := bstep (se 1 (by rfl) ⟨4048298, by rfl⟩ : syracuseStep 5397731 = 8096597) B8096597
theorem B3598487 : Blo 1995435 3598487 := bstep (se 1 (by rfl) ⟨2698865, by rfl⟩ : syracuseStep 3598487 = 5397731) B5397731
theorem B2398991 : Blo 1995435 2398991 := bstep (se 1 (by rfl) ⟨1799243, by rfl⟩ : syracuseStep 2398991 = 3598487) B3598487
theorem B6397309 : Blo 1995435 6397309 := bstep (se 3 (by rfl) ⟨1199495, by rfl⟩ : syracuseStep 6397309 = 2398991) B2398991
theorem B8529745 : Blo 1995435 8529745 := bstep (se 2 (by rfl) ⟨3198654, by rfl⟩ : syracuseStep 8529745 = 6397309) B6397309
theorem B11372993 : Blo 1995435 11372993 := bstep (se 2 (by rfl) ⟨4264872, by rfl⟩ : syracuseStep 11372993 = 8529745) B8529745
theorem B7581995 : Blo 1995435 7581995 := bstep (se 1 (by rfl) ⟨5686496, by rfl⟩ : syracuseStep 7581995 = 11372993) B11372993
theorem B5054663 : Blo 1995435 5054663 := bstep (se 1 (by rfl) ⟨3790997, by rfl⟩ : syracuseStep 5054663 = 7581995) B7581995
theorem B3369775 : Blo 1995435 3369775 := bstep (se 1 (by rfl) ⟨2527331, by rfl⟩ : syracuseStep 3369775 = 5054663) B5054663
theorem B4493033 : Blo 1995435 4493033 := bstep (se 2 (by rfl) ⟨1684887, by rfl⟩ : syracuseStep 4493033 = 3369775) B3369775
theorem B2995355 : Blo 1995435 2995355 := bstep (se 1 (by rfl) ⟨2246516, by rfl⟩ : syracuseStep 2995355 = 4493033) B4493033
theorem B1996903 : Blo 1995435 1996903 := bstep (se 1 (by rfl) ⟨1497677, by rfl⟩ : syracuseStep 1996903 = 2995355) B2995355
theorem B2246521 : Blo 1995435 2246521 := bbase (se 2 (by rfl) ⟨842445, by rfl⟩ : syracuseStep 2246521 = 1684891) (by norm_num)
theorem B2995361 : Blo 1995435 2995361 := bstep (se 2 (by rfl) ⟨1123260, by rfl⟩ : syracuseStep 2995361 = 2246521) B2246521
theorem B1996907 : Blo 1995435 1996907 := bstep (se 1 (by rfl) ⟨1497680, by rfl⟩ : syracuseStep 1996907 = 2995361) B2995361
theorem B3598501 : Blo 1995435 3598501 := bbase (se 4 (by rfl) ⟨337359, by rfl⟩ : syracuseStep 3598501 = 674719) (by norm_num)
theorem B4798001 : Blo 1995435 4798001 := bstep (se 2 (by rfl) ⟨1799250, by rfl⟩ : syracuseStep 4798001 = 3598501) B3598501
theorem B12794669 : Blo 1995435 12794669 := bstep (se 3 (by rfl) ⟨2399000, by rfl⟩ : syracuseStep 12794669 = 4798001) B4798001
theorem B8529779 : Blo 1995435 8529779 := bstep (se 1 (by rfl) ⟨6397334, by rfl⟩ : syracuseStep 8529779 = 12794669) B12794669
theorem B5686519 : Blo 1995435 5686519 := bstep (se 1 (by rfl) ⟨4264889, by rfl⟩ : syracuseStep 5686519 = 8529779) B8529779
theorem B7582025 : Blo 1995435 7582025 := bstep (se 2 (by rfl) ⟨2843259, by rfl⟩ : syracuseStep 7582025 = 5686519) B5686519
theorem B5054683 : Blo 1995435 5054683 := bstep (se 1 (by rfl) ⟨3791012, by rfl⟩ : syracuseStep 5054683 = 7582025) B7582025
theorem B6739577 : Blo 1995435 6739577 := bstep (se 2 (by rfl) ⟨2527341, by rfl⟩ : syracuseStep 6739577 = 5054683) B5054683
theorem B4493051 : Blo 1995435 4493051 := bstep (se 1 (by rfl) ⟨3369788, by rfl⟩ : syracuseStep 4493051 = 6739577) B6739577
theorem B2995367 : Blo 1995435 2995367 := bstep (se 1 (by rfl) ⟨2246525, by rfl⟩ : syracuseStep 2995367 = 4493051) B4493051
theorem B1996911 : Blo 1995435 1996911 := bstep (se 1 (by rfl) ⟨1497683, by rfl⟩ : syracuseStep 1996911 = 2995367) B2995367
theorem B2995373 : Blo 1995435 2995373 := bbase (se 3 (by rfl) ⟨561632, by rfl⟩ : syracuseStep 2995373 = 1123265) (by norm_num)
theorem B1996915 : Blo 1995435 1996915 := bstep (se 1 (by rfl) ⟨1497686, by rfl⟩ : syracuseStep 1996915 = 2995373) B2995373
theorem B4493069 : Blo 1995435 4493069 := bbase (se 3 (by rfl) ⟨842450, by rfl⟩ : syracuseStep 4493069 = 1684901) (by norm_num)
theorem B2995379 : Blo 1995435 2995379 := bstep (se 1 (by rfl) ⟨2246534, by rfl⟩ : syracuseStep 2995379 = 4493069) B4493069
theorem B1996919 : Blo 1995435 1996919 := bstep (se 1 (by rfl) ⟨1497689, by rfl⟩ : syracuseStep 1996919 = 2995379) B2995379
theorem B2527357 : Blo 1995435 2527357 := bbase (se 3 (by rfl) ⟨473879, by rfl⟩ : syracuseStep 2527357 = 947759) (by norm_num)
theorem B3369809 : Blo 1995435 3369809 := bstep (se 2 (by rfl) ⟨1263678, by rfl⟩ : syracuseStep 3369809 = 2527357) B2527357
theorem B2246539 : Blo 1995435 2246539 := bstep (se 1 (by rfl) ⟨1684904, by rfl⟩ : syracuseStep 2246539 = 3369809) B3369809
theorem B2995385 : Blo 1995435 2995385 := bstep (se 2 (by rfl) ⟨1123269, by rfl⟩ : syracuseStep 2995385 = 2246539) B2246539
theorem B1996923 : Blo 1995435 1996923 := bstep (se 1 (by rfl) ⟨1497692, by rfl⟩ : syracuseStep 1996923 = 2995385) B2995385
theorem B2024173 : Blo 1995435 2024173 := bbase (se 3 (by rfl) ⟨379532, by rfl⟩ : syracuseStep 2024173 = 759065) (by norm_num)
theorem B10795589 : Blo 1995435 10795589 := bstep (se 4 (by rfl) ⟨1012086, by rfl⟩ : syracuseStep 10795589 = 2024173) B2024173
theorem B7197059 : Blo 1995435 7197059 := bstep (se 1 (by rfl) ⟨5397794, by rfl⟩ : syracuseStep 7197059 = 10795589) B10795589
theorem B4798039 : Blo 1995435 4798039 := bstep (se 1 (by rfl) ⟨3598529, by rfl⟩ : syracuseStep 4798039 = 7197059) B7197059
theorem B6397385 : Blo 1995435 6397385 := bstep (se 2 (by rfl) ⟨2399019, by rfl⟩ : syracuseStep 6397385 = 4798039) B4798039
theorem B17059693 : Blo 1995435 17059693 := bstep (se 3 (by rfl) ⟨3198692, by rfl⟩ : syracuseStep 17059693 = 6397385) B6397385
theorem B22746257 : Blo 1995435 22746257 := bstep (se 2 (by rfl) ⟨8529846, by rfl⟩ : syracuseStep 22746257 = 17059693) B17059693
theorem B15164171 : Blo 1995435 15164171 := bstep (se 1 (by rfl) ⟨11373128, by rfl⟩ : syracuseStep 15164171 = 22746257) B22746257
theorem B10109447 : Blo 1995435 10109447 := bstep (se 1 (by rfl) ⟨7582085, by rfl⟩ : syracuseStep 10109447 = 15164171) B15164171
theorem B6739631 : Blo 1995435 6739631 := bstep (se 1 (by rfl) ⟨5054723, by rfl⟩ : syracuseStep 6739631 = 10109447) B10109447
theorem B4493087 : Blo 1995435 4493087 := bstep (se 1 (by rfl) ⟨3369815, by rfl⟩ : syracuseStep 4493087 = 6739631) B6739631
theorem B2995391 : Blo 1995435 2995391 := bstep (se 1 (by rfl) ⟨2246543, by rfl⟩ : syracuseStep 2995391 = 4493087) B4493087
theorem B1996927 : Blo 1995435 1996927 := bstep (se 1 (by rfl) ⟨1497695, by rfl⟩ : syracuseStep 1996927 = 2995391) B2995391
theorem B2995397 : Blo 1995435 2995397 := bbase (se 4 (by rfl) ⟨280818, by rfl⟩ : syracuseStep 2995397 = 561637) (by norm_num)
theorem B1996931 : Blo 1995435 1996931 := bstep (se 1 (by rfl) ⟨1497698, by rfl⟩ : syracuseStep 1996931 = 2995397) B2995397
theorem B3369829 : Blo 1995435 3369829 := bbase (se 4 (by rfl) ⟨315921, by rfl⟩ : syracuseStep 3369829 = 631843) (by norm_num)
theorem B4493105 : Blo 1995435 4493105 := bstep (se 2 (by rfl) ⟨1684914, by rfl⟩ : syracuseStep 4493105 = 3369829) B3369829
theorem B2995403 : Blo 1995435 2995403 := bstep (se 1 (by rfl) ⟨2246552, by rfl⟩ : syracuseStep 2995403 = 4493105) B4493105
theorem B1996935 : Blo 1995435 1996935 := bstep (se 1 (by rfl) ⟨1497701, by rfl⟩ : syracuseStep 1996935 = 2995403) B2995403
theorem B2246557 : Blo 1995435 2246557 := bbase (se 3 (by rfl) ⟨421229, by rfl⟩ : syracuseStep 2246557 = 842459) (by norm_num)
theorem B2995409 : Blo 1995435 2995409 := bstep (se 2 (by rfl) ⟨1123278, by rfl⟩ : syracuseStep 2995409 = 2246557) B2246557
theorem B1996939 : Blo 1995435 1996939 := bstep (se 1 (by rfl) ⟨1497704, by rfl⟩ : syracuseStep 1996939 = 2995409) B2995409
theorem B6739685 : Blo 1995435 6739685 := bbase (se 4 (by rfl) ⟨631845, by rfl⟩ : syracuseStep 6739685 = 1263691) (by norm_num)
theorem B4493123 : Blo 1995435 4493123 := bstep (se 1 (by rfl) ⟨3369842, by rfl⟩ : syracuseStep 4493123 = 6739685) B6739685
theorem B2995415 : Blo 1995435 2995415 := bstep (se 1 (by rfl) ⟨2246561, by rfl⟩ : syracuseStep 2995415 = 4493123) B4493123
theorem B1996943 : Blo 1995435 1996943 := bstep (se 1 (by rfl) ⟨1497707, by rfl⟩ : syracuseStep 1996943 = 2995415) B2995415
theorem B2995421 : Blo 1995435 2995421 := bbase (se 3 (by rfl) ⟨561641, by rfl⟩ : syracuseStep 2995421 = 1123283) (by norm_num)
theorem B1996947 : Blo 1995435 1996947 := bstep (se 1 (by rfl) ⟨1497710, by rfl⟩ : syracuseStep 1996947 = 2995421) B2995421
theorem B4493141 : Blo 1995435 4493141 := bbase (se 9 (by rfl) ⟨13163, by rfl⟩ : syracuseStep 4493141 = 26327) (by norm_num)
theorem B2995427 : Blo 1995435 2995427 := bstep (se 1 (by rfl) ⟨2246570, by rfl⟩ : syracuseStep 2995427 = 4493141) B4493141
theorem B1996951 : Blo 1995435 1996951 := bstep (se 1 (by rfl) ⟨1497713, by rfl⟩ : syracuseStep 1996951 = 2995427) B2995427
theorem B5686645 : Blo 1995435 5686645 := bbase (se 5 (by rfl) ⟨266561, by rfl⟩ : syracuseStep 5686645 = 533123) (by norm_num)
theorem B7582193 : Blo 1995435 7582193 := bstep (se 2 (by rfl) ⟨2843322, by rfl⟩ : syracuseStep 7582193 = 5686645) B5686645
theorem B5054795 : Blo 1995435 5054795 := bstep (se 1 (by rfl) ⟨3791096, by rfl⟩ : syracuseStep 5054795 = 7582193) B7582193
theorem B3369863 : Blo 1995435 3369863 := bstep (se 1 (by rfl) ⟨2527397, by rfl⟩ : syracuseStep 3369863 = 5054795) B5054795
theorem B2246575 : Blo 1995435 2246575 := bstep (se 1 (by rfl) ⟨1684931, by rfl⟩ : syracuseStep 2246575 = 3369863) B3369863
theorem B2995433 : Blo 1995435 2995433 := bstep (se 2 (by rfl) ⟨1123287, by rfl⟩ : syracuseStep 2995433 = 2246575) B2246575
theorem B1996955 : Blo 1995435 1996955 := bstep (se 1 (by rfl) ⟨1497716, by rfl⟩ : syracuseStep 1996955 = 2995433) B2995433
theorem B4323181 : Blo 1995435 4323181 := bbase (se 3 (by rfl) ⟨810596, by rfl⟩ : syracuseStep 4323181 = 1621193) (by norm_num)
theorem B5764241 : Blo 1995435 5764241 := bstep (se 2 (by rfl) ⟨2161590, by rfl⟩ : syracuseStep 5764241 = 4323181) B4323181
theorem B15371309 : Blo 1995435 15371309 := bstep (se 3 (by rfl) ⟨2882120, by rfl⟩ : syracuseStep 15371309 = 5764241) B5764241
theorem B10247539 : Blo 1995435 10247539 := bstep (se 1 (by rfl) ⟨7685654, by rfl⟩ : syracuseStep 10247539 = 15371309) B15371309
theorem B13663385 : Blo 1995435 13663385 := bstep (se 2 (by rfl) ⟨5123769, by rfl⟩ : syracuseStep 13663385 = 10247539) B10247539
theorem B145742773 : Blo 1995435 145742773 := bstep (se 5 (by rfl) ⟨6831692, by rfl⟩ : syracuseStep 145742773 = 13663385) B13663385
theorem B194323697 : Blo 1995435 194323697 := bstep (se 2 (by rfl) ⟨72871386, by rfl⟩ : syracuseStep 194323697 = 145742773) B145742773
theorem B129549131 : Blo 1995435 129549131 := bstep (se 1 (by rfl) ⟨97161848, by rfl⟩ : syracuseStep 129549131 = 194323697) B194323697
theorem B86366087 : Blo 1995435 86366087 := bstep (se 1 (by rfl) ⟨64774565, by rfl⟩ : syracuseStep 86366087 = 129549131) B129549131
theorem B57577391 : Blo 1995435 57577391 := bstep (se 1 (by rfl) ⟨43183043, by rfl⟩ : syracuseStep 57577391 = 86366087) B86366087
theorem B38384927 : Blo 1995435 38384927 := bstep (se 1 (by rfl) ⟨28788695, by rfl⟩ : syracuseStep 38384927 = 57577391) B57577391
theorem B25589951 : Blo 1995435 25589951 := bstep (se 1 (by rfl) ⟨19192463, by rfl⟩ : syracuseStep 25589951 = 38384927) B38384927
theorem B17059967 : Blo 1995435 17059967 := bstep (se 1 (by rfl) ⟨12794975, by rfl⟩ : syracuseStep 17059967 = 25589951) B25589951
theorem B11373311 : Blo 1995435 11373311 := bstep (se 1 (by rfl) ⟨8529983, by rfl⟩ : syracuseStep 11373311 = 17059967) B17059967
theorem B7582207 : Blo 1995435 7582207 := bstep (se 1 (by rfl) ⟨5686655, by rfl⟩ : syracuseStep 7582207 = 11373311) B11373311
theorem B10109609 : Blo 1995435 10109609 := bstep (se 2 (by rfl) ⟨3791103, by rfl⟩ : syracuseStep 10109609 = 7582207) B7582207
theorem B6739739 : Blo 1995435 6739739 := bstep (se 1 (by rfl) ⟨5054804, by rfl⟩ : syracuseStep 6739739 = 10109609) B10109609
theorem B4493159 : Blo 1995435 4493159 := bstep (se 1 (by rfl) ⟨3369869, by rfl⟩ : syracuseStep 4493159 = 6739739) B6739739
theorem B2995439 : Blo 1995435 2995439 := bstep (se 1 (by rfl) ⟨2246579, by rfl⟩ : syracuseStep 2995439 = 4493159) B4493159
theorem B1996959 : Blo 1995435 1996959 := bstep (se 1 (by rfl) ⟨1497719, by rfl⟩ : syracuseStep 1996959 = 2995439) B2995439
theorem B2995445 : Blo 1995435 2995445 := bbase (se 5 (by rfl) ⟨140411, by rfl⟩ : syracuseStep 2995445 = 280823) (by norm_num)
theorem B1996963 : Blo 1995435 1996963 := bstep (se 1 (by rfl) ⟨1497722, by rfl⟩ : syracuseStep 1996963 = 2995445) B2995445
theorem B12795029 : Blo 1995435 12795029 := bbase (se 6 (by rfl) ⟨299883, by rfl⟩ : syracuseStep 12795029 = 599767) (by norm_num)
theorem B8530019 : Blo 1995435 8530019 := bstep (se 1 (by rfl) ⟨6397514, by rfl⟩ : syracuseStep 8530019 = 12795029) B12795029
theorem B5686679 : Blo 1995435 5686679 := bstep (se 1 (by rfl) ⟨4265009, by rfl⟩ : syracuseStep 5686679 = 8530019) B8530019
theorem B3791119 : Blo 1995435 3791119 := bstep (se 1 (by rfl) ⟨2843339, by rfl⟩ : syracuseStep 3791119 = 5686679) B5686679
theorem B5054825 : Blo 1995435 5054825 := bstep (se 2 (by rfl) ⟨1895559, by rfl⟩ : syracuseStep 5054825 = 3791119) B3791119
theorem B3369883 : Blo 1995435 3369883 := bstep (se 1 (by rfl) ⟨2527412, by rfl⟩ : syracuseStep 3369883 = 5054825) B5054825
theorem B4493177 : Blo 1995435 4493177 := bstep (se 2 (by rfl) ⟨1684941, by rfl⟩ : syracuseStep 4493177 = 3369883) B3369883
theorem B2995451 : Blo 1995435 2995451 := bstep (se 1 (by rfl) ⟨2246588, by rfl⟩ : syracuseStep 2995451 = 4493177) B4493177
theorem B1996967 : Blo 1995435 1996967 := bstep (se 1 (by rfl) ⟨1497725, by rfl⟩ : syracuseStep 1996967 = 2995451) B2995451
theorem B2246593 : Blo 1995435 2246593 := bbase (se 2 (by rfl) ⟨842472, by rfl⟩ : syracuseStep 2246593 = 1684945) (by norm_num)
theorem B2995457 : Blo 1995435 2995457 := bstep (se 2 (by rfl) ⟨1123296, by rfl⟩ : syracuseStep 2995457 = 2246593) B2246593
theorem B1996971 : Blo 1995435 1996971 := bstep (se 1 (by rfl) ⟨1497728, by rfl⟩ : syracuseStep 1996971 = 2995457) B2995457
theorem B5054845 : Blo 1995435 5054845 := bbase (se 3 (by rfl) ⟨947783, by rfl⟩ : syracuseStep 5054845 = 1895567) (by norm_num)
theorem B6739793 : Blo 1995435 6739793 := bstep (se 2 (by rfl) ⟨2527422, by rfl⟩ : syracuseStep 6739793 = 5054845) B5054845
theorem B4493195 : Blo 1995435 4493195 := bstep (se 1 (by rfl) ⟨3369896, by rfl⟩ : syracuseStep 4493195 = 6739793) B6739793
theorem B2995463 : Blo 1995435 2995463 := bstep (se 1 (by rfl) ⟨2246597, by rfl⟩ : syracuseStep 2995463 = 4493195) B4493195
theorem B1996975 : Blo 1995435 1996975 := bstep (se 1 (by rfl) ⟨1497731, by rfl⟩ : syracuseStep 1996975 = 2995463) B2995463
theorem B2995469 : Blo 1995435 2995469 := bbase (se 3 (by rfl) ⟨561650, by rfl⟩ : syracuseStep 2995469 = 1123301) (by norm_num)
theorem B1996979 : Blo 1995435 1996979 := bstep (se 1 (by rfl) ⟨1497734, by rfl⟩ : syracuseStep 1996979 = 2995469) B2995469
theorem B4493213 : Blo 1995435 4493213 := bbase (se 3 (by rfl) ⟨842477, by rfl⟩ : syracuseStep 4493213 = 1684955) (by norm_num)
theorem B2995475 : Blo 1995435 2995475 := bstep (se 1 (by rfl) ⟨2246606, by rfl⟩ : syracuseStep 2995475 = 4493213) B4493213
theorem B1996983 : Blo 1995435 1996983 := bstep (se 1 (by rfl) ⟨1497737, by rfl⟩ : syracuseStep 1996983 = 2995475) B2995475
theorem B3369917 : Blo 1995435 3369917 := bbase (se 3 (by rfl) ⟨631859, by rfl⟩ : syracuseStep 3369917 = 1263719) (by norm_num)
theorem B2246611 : Blo 1995435 2246611 := bstep (se 1 (by rfl) ⟨1684958, by rfl⟩ : syracuseStep 2246611 = 3369917) B3369917
theorem B2995481 : Blo 1995435 2995481 := bstep (se 2 (by rfl) ⟨1123305, by rfl⟩ : syracuseStep 2995481 = 2246611) B2246611
theorem B1996987 : Blo 1995435 1996987 := bstep (se 1 (by rfl) ⟨1497740, by rfl⟩ : syracuseStep 1996987 = 2995481) B2995481
theorem B11373493 : Blo 1995435 11373493 := bbase (se 5 (by rfl) ⟨533132, by rfl⟩ : syracuseStep 11373493 = 1066265) (by norm_num)
theorem B15164657 : Blo 1995435 15164657 := bstep (se 2 (by rfl) ⟨5686746, by rfl⟩ : syracuseStep 15164657 = 11373493) B11373493
theorem B10109771 : Blo 1995435 10109771 := bstep (se 1 (by rfl) ⟨7582328, by rfl⟩ : syracuseStep 10109771 = 15164657) B15164657
theorem B6739847 : Blo 1995435 6739847 := bstep (se 1 (by rfl) ⟨5054885, by rfl⟩ : syracuseStep 6739847 = 10109771) B10109771
theorem B4493231 : Blo 1995435 4493231 := bstep (se 1 (by rfl) ⟨3369923, by rfl⟩ : syracuseStep 4493231 = 6739847) B6739847
theorem B2995487 : Blo 1995435 2995487 := bstep (se 1 (by rfl) ⟨2246615, by rfl⟩ : syracuseStep 2995487 = 4493231) B4493231
theorem B1996991 : Blo 1995435 1996991 := bstep (se 1 (by rfl) ⟨1497743, by rfl⟩ : syracuseStep 1996991 = 2995487) B2995487
theorem B2995493 : Blo 1995435 2995493 := bbase (se 4 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 2995493 = 561655) (by norm_num)
theorem B1996995 : Blo 1995435 1996995 := bstep (se 1 (by rfl) ⟨1497746, by rfl⟩ : syracuseStep 1996995 = 2995493) B2995493
theorem B2527453 : Blo 1995435 2527453 := bbase (se 3 (by rfl) ⟨473897, by rfl⟩ : syracuseStep 2527453 = 947795) (by norm_num)
theorem B3369937 : Blo 1995435 3369937 := bstep (se 2 (by rfl) ⟨1263726, by rfl⟩ : syracuseStep 3369937 = 2527453) B2527453
theorem B4493249 : Blo 1995435 4493249 := bstep (se 2 (by rfl) ⟨1684968, by rfl⟩ : syracuseStep 4493249 = 3369937) B3369937
theorem B2995499 : Blo 1995435 2995499 := bstep (se 1 (by rfl) ⟨2246624, by rfl⟩ : syracuseStep 2995499 = 4493249) B4493249
theorem B1996999 : Blo 1995435 1996999 := bstep (se 1 (by rfl) ⟨1497749, by rfl⟩ : syracuseStep 1996999 = 2995499) B2995499
theorem B2246629 : Blo 1995435 2246629 := bbase (se 4 (by rfl) ⟨210621, by rfl⟩ : syracuseStep 2246629 = 421243) (by norm_num)
theorem B2995505 : Blo 1995435 2995505 := bstep (se 2 (by rfl) ⟨1123314, by rfl⟩ : syracuseStep 2995505 = 2246629) B2246629
theorem B1997003 : Blo 1995435 1997003 := bstep (se 1 (by rfl) ⟨1497752, by rfl⟩ : syracuseStep 1997003 = 2995505) B2995505
theorem B7197349 : Blo 1995435 7197349 := bbase (se 4 (by rfl) ⟨674751, by rfl⟩ : syracuseStep 7197349 = 1349503) (by norm_num)
theorem B9596465 : Blo 1995435 9596465 := bstep (se 2 (by rfl) ⟨3598674, by rfl⟩ : syracuseStep 9596465 = 7197349) B7197349
theorem B6397643 : Blo 1995435 6397643 := bstep (se 1 (by rfl) ⟨4798232, by rfl⟩ : syracuseStep 6397643 = 9596465) B9596465
theorem B4265095 : Blo 1995435 4265095 := bstep (se 1 (by rfl) ⟨3198821, by rfl⟩ : syracuseStep 4265095 = 6397643) B6397643
theorem B5686793 : Blo 1995435 5686793 := bstep (se 2 (by rfl) ⟨2132547, by rfl⟩ : syracuseStep 5686793 = 4265095) B4265095
theorem B3791195 : Blo 1995435 3791195 := bstep (se 1 (by rfl) ⟨2843396, by rfl⟩ : syracuseStep 3791195 = 5686793) B5686793
theorem B2527463 : Blo 1995435 2527463 := bstep (se 1 (by rfl) ⟨1895597, by rfl⟩ : syracuseStep 2527463 = 3791195) B3791195
theorem B6739901 : Blo 1995435 6739901 := bstep (se 3 (by rfl) ⟨1263731, by rfl⟩ : syracuseStep 6739901 = 2527463) B2527463
theorem B4493267 : Blo 1995435 4493267 := bstep (se 1 (by rfl) ⟨3369950, by rfl⟩ : syracuseStep 4493267 = 6739901) B6739901
theorem B2995511 : Blo 1995435 2995511 := bstep (se 1 (by rfl) ⟨2246633, by rfl⟩ : syracuseStep 2995511 = 4493267) B4493267
theorem B1997007 : Blo 1995435 1997007 := bstep (se 1 (by rfl) ⟨1497755, by rfl⟩ : syracuseStep 1997007 = 2995511) B2995511
theorem B2995517 : Blo 1995435 2995517 := bbase (se 3 (by rfl) ⟨561659, by rfl⟩ : syracuseStep 2995517 = 1123319) (by norm_num)
theorem B1997011 : Blo 1995435 1997011 := bstep (se 1 (by rfl) ⟨1497758, by rfl⟩ : syracuseStep 1997011 = 2995517) B2995517
theorem B4493285 : Blo 1995435 4493285 := bbase (se 4 (by rfl) ⟨421245, by rfl⟩ : syracuseStep 4493285 = 842491) (by norm_num)
theorem B2995523 : Blo 1995435 2995523 := bstep (se 1 (by rfl) ⟨2246642, by rfl⟩ : syracuseStep 2995523 = 4493285) B4493285
theorem B1997015 : Blo 1995435 1997015 := bstep (se 1 (by rfl) ⟨1497761, by rfl⟩ : syracuseStep 1997015 = 2995523) B2995523
theorem B5054957 : Blo 1995435 5054957 := bbase (se 3 (by rfl) ⟨947804, by rfl⟩ : syracuseStep 5054957 = 1895609) (by norm_num)
theorem B3369971 : Blo 1995435 3369971 := bstep (se 1 (by rfl) ⟨2527478, by rfl⟩ : syracuseStep 3369971 = 5054957) B5054957
theorem B2246647 : Blo 1995435 2246647 := bstep (se 1 (by rfl) ⟨1684985, by rfl⟩ : syracuseStep 2246647 = 3369971) B3369971
theorem B2995529 : Blo 1995435 2995529 := bstep (se 2 (by rfl) ⟨1123323, by rfl⟩ : syracuseStep 2995529 = 2246647) B2246647
theorem B1997019 : Blo 1995435 1997019 := bstep (se 1 (by rfl) ⟨1497764, by rfl⟩ : syracuseStep 1997019 = 2995529) B2995529
theorem B13663829 : Blo 1995435 13663829 := bbase (se 8 (by rfl) ⟨80061, by rfl⟩ : syracuseStep 13663829 = 160123) (by norm_num)
theorem B36436877 : Blo 1995435 36436877 := bstep (se 3 (by rfl) ⟨6831914, by rfl⟩ : syracuseStep 36436877 = 13663829) B13663829
theorem B24291251 : Blo 1995435 24291251 := bstep (se 1 (by rfl) ⟨18218438, by rfl⟩ : syracuseStep 24291251 = 36436877) B36436877
theorem B16194167 : Blo 1995435 16194167 := bstep (se 1 (by rfl) ⟨12145625, by rfl⟩ : syracuseStep 16194167 = 24291251) B24291251
theorem B10796111 : Blo 1995435 10796111 := bstep (se 1 (by rfl) ⟨8097083, by rfl⟩ : syracuseStep 10796111 = 16194167) B16194167
theorem B7197407 : Blo 1995435 7197407 := bstep (se 1 (by rfl) ⟨5398055, by rfl⟩ : syracuseStep 7197407 = 10796111) B10796111
theorem B4798271 : Blo 1995435 4798271 := bstep (se 1 (by rfl) ⟨3598703, by rfl⟩ : syracuseStep 4798271 = 7197407) B7197407
theorem B3198847 : Blo 1995435 3198847 := bstep (se 1 (by rfl) ⟨2399135, by rfl⟩ : syracuseStep 3198847 = 4798271) B4798271
theorem B4265129 : Blo 1995435 4265129 := bstep (se 2 (by rfl) ⟨1599423, by rfl⟩ : syracuseStep 4265129 = 3198847) B3198847
theorem B2843419 : Blo 1995435 2843419 := bstep (se 1 (by rfl) ⟨2132564, by rfl⟩ : syracuseStep 2843419 = 4265129) B4265129
theorem B3791225 : Blo 1995435 3791225 := bstep (se 2 (by rfl) ⟨1421709, by rfl⟩ : syracuseStep 3791225 = 2843419) B2843419
theorem B10109933 : Blo 1995435 10109933 := bstep (se 3 (by rfl) ⟨1895612, by rfl⟩ : syracuseStep 10109933 = 3791225) B3791225
theorem B6739955 : Blo 1995435 6739955 := bstep (se 1 (by rfl) ⟨5054966, by rfl⟩ : syracuseStep 6739955 = 10109933) B10109933
theorem B4493303 : Blo 1995435 4493303 := bstep (se 1 (by rfl) ⟨3369977, by rfl⟩ : syracuseStep 4493303 = 6739955) B6739955
theorem B2995535 : Blo 1995435 2995535 := bstep (se 1 (by rfl) ⟨2246651, by rfl⟩ : syracuseStep 2995535 = 4493303) B4493303
theorem B1997023 : Blo 1995435 1997023 := bstep (se 1 (by rfl) ⟨1497767, by rfl⟩ : syracuseStep 1997023 = 2995535) B2995535
theorem B2995541 : Blo 1995435 2995541 := bbase (se 13 (by rfl) ⟨548, by rfl⟩ : syracuseStep 2995541 = 1097) (by norm_num)
theorem B1997027 : Blo 1995435 1997027 := bstep (se 1 (by rfl) ⟨1497770, by rfl⟩ : syracuseStep 1997027 = 2995541) B2995541
theorem B2132573 : Blo 1995435 2132573 := bbase (se 3 (by rfl) ⟨399857, by rfl⟩ : syracuseStep 2132573 = 799715) (by norm_num)
theorem B5686861 : Blo 1995435 5686861 := bstep (se 3 (by rfl) ⟨1066286, by rfl⟩ : syracuseStep 5686861 = 2132573) B2132573
theorem B7582481 : Blo 1995435 7582481 := bstep (se 2 (by rfl) ⟨2843430, by rfl⟩ : syracuseStep 7582481 = 5686861) B5686861
theorem B5054987 : Blo 1995435 5054987 := bstep (se 1 (by rfl) ⟨3791240, by rfl⟩ : syracuseStep 5054987 = 7582481) B7582481
theorem B3369991 : Blo 1995435 3369991 := bstep (se 1 (by rfl) ⟨2527493, by rfl⟩ : syracuseStep 3369991 = 5054987) B5054987
theorem B4493321 : Blo 1995435 4493321 := bstep (se 2 (by rfl) ⟨1684995, by rfl⟩ : syracuseStep 4493321 = 3369991) B3369991
theorem B2995547 : Blo 1995435 2995547 := bstep (se 1 (by rfl) ⟨2246660, by rfl⟩ : syracuseStep 2995547 = 4493321) B4493321
theorem B1997031 : Blo 1995435 1997031 := bstep (se 1 (by rfl) ⟨1497773, by rfl⟩ : syracuseStep 1997031 = 2995547) B2995547
theorem B2246665 : Blo 1995435 2246665 := bbase (se 2 (by rfl) ⟨842499, by rfl⟩ : syracuseStep 2246665 = 1684999) (by norm_num)
theorem B2995553 : Blo 1995435 2995553 := bstep (se 2 (by rfl) ⟨1123332, by rfl⟩ : syracuseStep 2995553 = 2246665) B2246665
theorem B1997035 : Blo 1995435 1997035 := bstep (se 1 (by rfl) ⟨1497776, by rfl⟩ : syracuseStep 1997035 = 2995553) B2995553
theorem B4048573 : Blo 1995435 4048573 := bbase (se 3 (by rfl) ⟨759107, by rfl⟩ : syracuseStep 4048573 = 1518215) (by norm_num)
theorem B5398097 : Blo 1995435 5398097 := bstep (se 2 (by rfl) ⟨2024286, by rfl⟩ : syracuseStep 5398097 = 4048573) B4048573
theorem B14394925 : Blo 1995435 14394925 := bstep (se 3 (by rfl) ⟨2699048, by rfl⟩ : syracuseStep 14394925 = 5398097) B5398097
theorem B19193233 : Blo 1995435 19193233 := bstep (se 2 (by rfl) ⟨7197462, by rfl⟩ : syracuseStep 19193233 = 14394925) B14394925
theorem B25590977 : Blo 1995435 25590977 := bstep (se 2 (by rfl) ⟨9596616, by rfl⟩ : syracuseStep 25590977 = 19193233) B19193233
theorem B17060651 : Blo 1995435 17060651 := bstep (se 1 (by rfl) ⟨12795488, by rfl⟩ : syracuseStep 17060651 = 25590977) B25590977
theorem B11373767 : Blo 1995435 11373767 := bstep (se 1 (by rfl) ⟨8530325, by rfl⟩ : syracuseStep 11373767 = 17060651) B17060651
theorem B7582511 : Blo 1995435 7582511 := bstep (se 1 (by rfl) ⟨5686883, by rfl⟩ : syracuseStep 7582511 = 11373767) B11373767
theorem B5055007 : Blo 1995435 5055007 := bstep (se 1 (by rfl) ⟨3791255, by rfl⟩ : syracuseStep 5055007 = 7582511) B7582511
theorem B6740009 : Blo 1995435 6740009 := bstep (se 2 (by rfl) ⟨2527503, by rfl⟩ : syracuseStep 6740009 = 5055007) B5055007
theorem B4493339 : Blo 1995435 4493339 := bstep (se 1 (by rfl) ⟨3370004, by rfl⟩ : syracuseStep 4493339 = 6740009) B6740009
theorem B2995559 : Blo 1995435 2995559 := bstep (se 1 (by rfl) ⟨2246669, by rfl⟩ : syracuseStep 2995559 = 4493339) B4493339
theorem B1997039 : Blo 1995435 1997039 := bstep (se 1 (by rfl) ⟨1497779, by rfl⟩ : syracuseStep 1997039 = 2995559) B2995559
theorem B2995565 : Blo 1995435 2995565 := bbase (se 3 (by rfl) ⟨561668, by rfl⟩ : syracuseStep 2995565 = 1123337) (by norm_num)
theorem B1997043 : Blo 1995435 1997043 := bstep (se 1 (by rfl) ⟨1497782, by rfl⟩ : syracuseStep 1997043 = 2995565) B2995565
theorem B4493357 : Blo 1995435 4493357 := bbase (se 3 (by rfl) ⟨842504, by rfl⟩ : syracuseStep 4493357 = 1685009) (by norm_num)
theorem B2995571 : Blo 1995435 2995571 := bstep (se 1 (by rfl) ⟨2246678, by rfl⟩ : syracuseStep 2995571 = 4493357) B4493357
theorem B1997047 : Blo 1995435 1997047 := bstep (se 1 (by rfl) ⟨1497785, by rfl⟩ : syracuseStep 1997047 = 2995571) B2995571
theorem B9596677 : Blo 1995435 9596677 := bbase (se 4 (by rfl) ⟨899688, by rfl⟩ : syracuseStep 9596677 = 1799377) (by norm_num)
theorem B12795569 : Blo 1995435 12795569 := bstep (se 2 (by rfl) ⟨4798338, by rfl⟩ : syracuseStep 12795569 = 9596677) B9596677
theorem B8530379 : Blo 1995435 8530379 := bstep (se 1 (by rfl) ⟨6397784, by rfl⟩ : syracuseStep 8530379 = 12795569) B12795569
theorem B5686919 : Blo 1995435 5686919 := bstep (se 1 (by rfl) ⟨4265189, by rfl⟩ : syracuseStep 5686919 = 8530379) B8530379
theorem B3791279 : Blo 1995435 3791279 := bstep (se 1 (by rfl) ⟨2843459, by rfl⟩ : syracuseStep 3791279 = 5686919) B5686919
theorem B2527519 : Blo 1995435 2527519 := bstep (se 1 (by rfl) ⟨1895639, by rfl⟩ : syracuseStep 2527519 = 3791279) B3791279
theorem B3370025 : Blo 1995435 3370025 := bstep (se 2 (by rfl) ⟨1263759, by rfl⟩ : syracuseStep 3370025 = 2527519) B2527519
theorem B2246683 : Blo 1995435 2246683 := bstep (se 1 (by rfl) ⟨1685012, by rfl⟩ : syracuseStep 2246683 = 3370025) B3370025
theorem B2995577 : Blo 1995435 2995577 := bstep (se 2 (by rfl) ⟨1123341, by rfl⟩ : syracuseStep 2995577 = 2246683) B2246683
theorem B1997051 : Blo 1995435 1997051 := bstep (se 1 (by rfl) ⟨1497788, by rfl⟩ : syracuseStep 1997051 = 2995577) B2995577
theorem B9596693 : Blo 1995435 9596693 := bbase (se 6 (by rfl) ⟨224922, by rfl⟩ : syracuseStep 9596693 = 449845) (by norm_num)
theorem B6397795 : Blo 1995435 6397795 := bstep (se 1 (by rfl) ⟨4798346, by rfl⟩ : syracuseStep 6397795 = 9596693) B9596693
theorem B34121573 : Blo 1995435 34121573 := bstep (se 4 (by rfl) ⟨3198897, by rfl⟩ : syracuseStep 34121573 = 6397795) B6397795
theorem B22747715 : Blo 1995435 22747715 := bstep (se 1 (by rfl) ⟨17060786, by rfl⟩ : syracuseStep 22747715 = 34121573) B34121573
theorem B15165143 : Blo 1995435 15165143 := bstep (se 1 (by rfl) ⟨11373857, by rfl⟩ : syracuseStep 15165143 = 22747715) B22747715
theorem B10110095 : Blo 1995435 10110095 := bstep (se 1 (by rfl) ⟨7582571, by rfl⟩ : syracuseStep 10110095 = 15165143) B15165143
theorem B6740063 : Blo 1995435 6740063 := bstep (se 1 (by rfl) ⟨5055047, by rfl⟩ : syracuseStep 6740063 = 10110095) B10110095
theorem B4493375 : Blo 1995435 4493375 := bstep (se 1 (by rfl) ⟨3370031, by rfl⟩ : syracuseStep 4493375 = 6740063) B6740063
theorem B2995583 : Blo 1995435 2995583 := bstep (se 1 (by rfl) ⟨2246687, by rfl⟩ : syracuseStep 2995583 = 4493375) B4493375
theorem B1997055 : Blo 1995435 1997055 := bstep (se 1 (by rfl) ⟨1497791, by rfl⟩ : syracuseStep 1997055 = 2995583) B2995583
theorem B2995589 : Blo 1995435 2995589 := bbase (se 4 (by rfl) ⟨280836, by rfl⟩ : syracuseStep 2995589 = 561673) (by norm_num)
theorem B1997059 : Blo 1995435 1997059 := bstep (se 1 (by rfl) ⟨1497794, by rfl⟩ : syracuseStep 1997059 = 2995589) B2995589
theorem B3370045 : Blo 1995435 3370045 := bbase (se 3 (by rfl) ⟨631883, by rfl⟩ : syracuseStep 3370045 = 1263767) (by norm_num)
theorem B4493393 : Blo 1995435 4493393 := bstep (se 2 (by rfl) ⟨1685022, by rfl⟩ : syracuseStep 4493393 = 3370045) B3370045
theorem B2995595 : Blo 1995435 2995595 := bstep (se 1 (by rfl) ⟨2246696, by rfl⟩ : syracuseStep 2995595 = 4493393) B4493393
theorem B1997063 : Blo 1995435 1997063 := bstep (se 1 (by rfl) ⟨1497797, by rfl⟩ : syracuseStep 1997063 = 2995595) B2995595
theorem B2246701 : Blo 1995435 2246701 := bbase (se 3 (by rfl) ⟨421256, by rfl⟩ : syracuseStep 2246701 = 842513) (by norm_num)
theorem B2995601 : Blo 1995435 2995601 := bstep (se 2 (by rfl) ⟨1123350, by rfl⟩ : syracuseStep 2995601 = 2246701) B2246701
theorem B1997067 : Blo 1995435 1997067 := bstep (se 1 (by rfl) ⟨1497800, by rfl⟩ : syracuseStep 1997067 = 2995601) B2995601
theorem B6740117 : Blo 1995435 6740117 := bbase (se 6 (by rfl) ⟨157971, by rfl⟩ : syracuseStep 6740117 = 315943) (by norm_num)
theorem B4493411 : Blo 1995435 4493411 := bstep (se 1 (by rfl) ⟨3370058, by rfl⟩ : syracuseStep 4493411 = 6740117) B6740117
theorem B2995607 : Blo 1995435 2995607 := bstep (se 1 (by rfl) ⟨2246705, by rfl⟩ : syracuseStep 2995607 = 4493411) B4493411
theorem B1997071 : Blo 1995435 1997071 := bstep (se 1 (by rfl) ⟨1497803, by rfl⟩ : syracuseStep 1997071 = 2995607) B2995607
theorem B2995613 : Blo 1995435 2995613 := bbase (se 3 (by rfl) ⟨561677, by rfl⟩ : syracuseStep 2995613 = 1123355) (by norm_num)
theorem B1997075 : Blo 1995435 1997075 := bstep (se 1 (by rfl) ⟨1497806, by rfl⟩ : syracuseStep 1997075 = 2995613) B2995613
theorem B4493429 : Blo 1995435 4493429 := bbase (se 5 (by rfl) ⟨210629, by rfl⟩ : syracuseStep 4493429 = 421259) (by norm_num)
theorem B2995619 : Blo 1995435 2995619 := bstep (se 1 (by rfl) ⟨2246714, by rfl⟩ : syracuseStep 2995619 = 4493429) B4493429
theorem B1997079 : Blo 1995435 1997079 := bstep (se 1 (by rfl) ⟨1497809, by rfl⟩ : syracuseStep 1997079 = 2995619) B2995619
theorem B9109493 : Blo 1995435 9109493 := bbase (se 5 (by rfl) ⟨427007, by rfl⟩ : syracuseStep 9109493 = 854015) (by norm_num)
theorem B6072995 : Blo 1995435 6072995 := bstep (se 1 (by rfl) ⟨4554746, by rfl⟩ : syracuseStep 6072995 = 9109493) B9109493
theorem B16194653 : Blo 1995435 16194653 := bstep (se 3 (by rfl) ⟨3036497, by rfl⟩ : syracuseStep 16194653 = 6072995) B6072995
theorem B10796435 : Blo 1995435 10796435 := bstep (se 1 (by rfl) ⟨8097326, by rfl⟩ : syracuseStep 10796435 = 16194653) B16194653
theorem B7197623 : Blo 1995435 7197623 := bstep (se 1 (by rfl) ⟨5398217, by rfl⟩ : syracuseStep 7197623 = 10796435) B10796435
theorem B4798415 : Blo 1995435 4798415 := bstep (se 1 (by rfl) ⟨3598811, by rfl⟩ : syracuseStep 4798415 = 7197623) B7197623
theorem B3198943 : Blo 1995435 3198943 := bstep (se 1 (by rfl) ⟨2399207, by rfl⟩ : syracuseStep 3198943 = 4798415) B4798415
theorem B17061029 : Blo 1995435 17061029 := bstep (se 4 (by rfl) ⟨1599471, by rfl⟩ : syracuseStep 17061029 = 3198943) B3198943
theorem B11374019 : Blo 1995435 11374019 := bstep (se 1 (by rfl) ⟨8530514, by rfl⟩ : syracuseStep 11374019 = 17061029) B17061029
theorem B7582679 : Blo 1995435 7582679 := bstep (se 1 (by rfl) ⟨5687009, by rfl⟩ : syracuseStep 7582679 = 11374019) B11374019
theorem B5055119 : Blo 1995435 5055119 := bstep (se 1 (by rfl) ⟨3791339, by rfl⟩ : syracuseStep 5055119 = 7582679) B7582679
theorem B3370079 : Blo 1995435 3370079 := bstep (se 1 (by rfl) ⟨2527559, by rfl⟩ : syracuseStep 3370079 = 5055119) B5055119
theorem B2246719 : Blo 1995435 2246719 := bstep (se 1 (by rfl) ⟨1685039, by rfl⟩ : syracuseStep 2246719 = 3370079) B3370079
theorem B2995625 : Blo 1995435 2995625 := bstep (se 2 (by rfl) ⟨1123359, by rfl⟩ : syracuseStep 2995625 = 2246719) B2246719
theorem B1997083 : Blo 1995435 1997083 := bstep (se 1 (by rfl) ⟨1497812, by rfl⟩ : syracuseStep 1997083 = 2995625) B2995625
theorem B7582693 : Blo 1995435 7582693 := bbase (se 4 (by rfl) ⟨710877, by rfl⟩ : syracuseStep 7582693 = 1421755) (by norm_num)
theorem B10110257 : Blo 1995435 10110257 := bstep (se 2 (by rfl) ⟨3791346, by rfl⟩ : syracuseStep 10110257 = 7582693) B7582693
theorem B6740171 : Blo 1995435 6740171 := bstep (se 1 (by rfl) ⟨5055128, by rfl⟩ : syracuseStep 6740171 = 10110257) B10110257
theorem B4493447 : Blo 1995435 4493447 := bstep (se 1 (by rfl) ⟨3370085, by rfl⟩ : syracuseStep 4493447 = 6740171) B6740171
theorem B2995631 : Blo 1995435 2995631 := bstep (se 1 (by rfl) ⟨2246723, by rfl⟩ : syracuseStep 2995631 = 4493447) B4493447
theorem B1997087 : Blo 1995435 1997087 := bstep (se 1 (by rfl) ⟨1497815, by rfl⟩ : syracuseStep 1997087 = 2995631) B2995631
theorem B2995637 : Blo 1995435 2995637 := bbase (se 5 (by rfl) ⟨140420, by rfl⟩ : syracuseStep 2995637 = 280841) (by norm_num)
theorem B1997091 : Blo 1995435 1997091 := bstep (se 1 (by rfl) ⟨1497818, by rfl⟩ : syracuseStep 1997091 = 2995637) B2995637
theorem B5055149 : Blo 1995435 5055149 := bbase (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) (by norm_num)
theorem B3370099 : Blo 1995435 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B4493465 : Blo 1995435 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B2995643 : Blo 1995435 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B1997095 : Blo 1995435 1997095 := bstep (se 1 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 1997095 = 2995643) B2995643
theorem B2246737 : Blo 1995435 2246737 := bbase (se 2 (by rfl) ⟨842526, by rfl⟩ : syracuseStep 2246737 = 1685053) (by norm_num)
theorem B2995649 : Blo 1995435 2995649 := bstep (se 2 (by rfl) ⟨1123368, by rfl⟩ : syracuseStep 2995649 = 2246737) B2246737
theorem B1997099 : Blo 1995435 1997099 := bstep (se 1 (by rfl) ⟨1497824, by rfl⟩ : syracuseStep 1997099 = 2995649) B2995649
theorem B2843533 : Blo 1995435 2843533 := bbase (se 3 (by rfl) ⟨533162, by rfl⟩ : syracuseStep 2843533 = 1066325) (by norm_num)
theorem B3791377 : Blo 1995435 3791377 := bstep (se 2 (by rfl) ⟨1421766, by rfl⟩ : syracuseStep 3791377 = 2843533) B2843533
theorem B5055169 : Blo 1995435 5055169 := bstep (se 2 (by rfl) ⟨1895688, by rfl⟩ : syracuseStep 5055169 = 3791377) B3791377
theorem B6740225 : Blo 1995435 6740225 := bstep (se 2 (by rfl) ⟨2527584, by rfl⟩ : syracuseStep 6740225 = 5055169) B5055169
theorem B4493483 : Blo 1995435 4493483 := bstep (se 1 (by rfl) ⟨3370112, by rfl⟩ : syracuseStep 4493483 = 6740225) B6740225
theorem B2995655 : Blo 1995435 2995655 := bstep (se 1 (by rfl) ⟨2246741, by rfl⟩ : syracuseStep 2995655 = 4493483) B4493483
theorem B1997103 : Blo 1995435 1997103 := bstep (se 1 (by rfl) ⟨1497827, by rfl⟩ : syracuseStep 1997103 = 2995655) B2995655
theorem B2995661 : Blo 1995435 2995661 := bbase (se 3 (by rfl) ⟨561686, by rfl⟩ : syracuseStep 2995661 = 1123373) (by norm_num)
theorem B1997107 : Blo 1995435 1997107 := bstep (se 1 (by rfl) ⟨1497830, by rfl⟩ : syracuseStep 1997107 = 2995661) B2995661
theorem B4493501 : Blo 1995435 4493501 := bbase (se 3 (by rfl) ⟨842531, by rfl⟩ : syracuseStep 4493501 = 1685063) (by norm_num)
theorem B2995667 : Blo 1995435 2995667 := bstep (se 1 (by rfl) ⟨2246750, by rfl⟩ : syracuseStep 2995667 = 4493501) B4493501
theorem B1997111 : Blo 1995435 1997111 := bstep (se 1 (by rfl) ⟨1497833, by rfl⟩ : syracuseStep 1997111 = 2995667) B2995667
theorem B3370133 : Blo 1995435 3370133 := bbase (se 6 (by rfl) ⟨78987, by rfl⟩ : syracuseStep 3370133 = 157975) (by norm_num)
theorem B2246755 : Blo 1995435 2246755 := bstep (se 1 (by rfl) ⟨1685066, by rfl⟩ : syracuseStep 2246755 = 3370133) B3370133
theorem B2995673 : Blo 1995435 2995673 := bstep (se 2 (by rfl) ⟨1123377, by rfl⟩ : syracuseStep 2995673 = 2246755) B2246755
theorem B1997115 : Blo 1995435 1997115 := bstep (se 1 (by rfl) ⟨1497836, by rfl⟩ : syracuseStep 1997115 = 2995673) B2995673
theorem B20496725 : Blo 1995435 20496725 := bbase (se 10 (by rfl) ⟨30024, by rfl⟩ : syracuseStep 20496725 = 60049) (by norm_num)
theorem B13664483 : Blo 1995435 13664483 := bstep (se 1 (by rfl) ⟨10248362, by rfl⟩ : syracuseStep 13664483 = 20496725) B20496725
theorem B9109655 : Blo 1995435 9109655 := bstep (se 1 (by rfl) ⟨6832241, by rfl⟩ : syracuseStep 9109655 = 13664483) B13664483
theorem B6073103 : Blo 1995435 6073103 := bstep (se 1 (by rfl) ⟨4554827, by rfl⟩ : syracuseStep 6073103 = 9109655) B9109655
theorem B16194941 : Blo 1995435 16194941 := bstep (se 3 (by rfl) ⟨3036551, by rfl⟩ : syracuseStep 16194941 = 6073103) B6073103
theorem B10796627 : Blo 1995435 10796627 := bstep (se 1 (by rfl) ⟨8097470, by rfl⟩ : syracuseStep 10796627 = 16194941) B16194941
theorem B7197751 : Blo 1995435 7197751 := bstep (se 1 (by rfl) ⟨5398313, by rfl⟩ : syracuseStep 7197751 = 10796627) B10796627
theorem B9597001 : Blo 1995435 9597001 := bstep (se 2 (by rfl) ⟨3598875, by rfl⟩ : syracuseStep 9597001 = 7197751) B7197751
theorem B12796001 : Blo 1995435 12796001 := bstep (se 2 (by rfl) ⟨4798500, by rfl⟩ : syracuseStep 12796001 = 9597001) B9597001
theorem B8530667 : Blo 1995435 8530667 := bstep (se 1 (by rfl) ⟨6398000, by rfl⟩ : syracuseStep 8530667 = 12796001) B12796001
theorem B5687111 : Blo 1995435 5687111 := bstep (se 1 (by rfl) ⟨4265333, by rfl⟩ : syracuseStep 5687111 = 8530667) B8530667
theorem B15165629 : Blo 1995435 15165629 := bstep (se 3 (by rfl) ⟨2843555, by rfl⟩ : syracuseStep 15165629 = 5687111) B5687111
theorem B10110419 : Blo 1995435 10110419 := bstep (se 1 (by rfl) ⟨7582814, by rfl⟩ : syracuseStep 10110419 = 15165629) B15165629
theorem B6740279 : Blo 1995435 6740279 := bstep (se 1 (by rfl) ⟨5055209, by rfl⟩ : syracuseStep 6740279 = 10110419) B10110419
theorem B4493519 : Blo 1995435 4493519 := bstep (se 1 (by rfl) ⟨3370139, by rfl⟩ : syracuseStep 4493519 = 6740279) B6740279
theorem B2995679 : Blo 1995435 2995679 := bstep (se 1 (by rfl) ⟨2246759, by rfl⟩ : syracuseStep 2995679 = 4493519) B4493519
theorem B1997119 : Blo 1995435 1997119 := bstep (se 1 (by rfl) ⟨1497839, by rfl⟩ : syracuseStep 1997119 = 2995679) B2995679
theorem B2995685 : Blo 1995435 2995685 := bbase (se 4 (by rfl) ⟨280845, by rfl⟩ : syracuseStep 2995685 = 561691) (by norm_num)
theorem B1997123 : Blo 1995435 1997123 := bstep (se 1 (by rfl) ⟨1497842, by rfl⟩ : syracuseStep 1997123 = 2995685) B2995685
theorem B28791125 : Blo 1995435 28791125 := bbase (se 10 (by rfl) ⟨42174, by rfl⟩ : syracuseStep 28791125 = 84349) (by norm_num)
theorem B19194083 : Blo 1995435 19194083 := bstep (se 1 (by rfl) ⟨14395562, by rfl⟩ : syracuseStep 19194083 = 28791125) B28791125
theorem B12796055 : Blo 1995435 12796055 := bstep (se 1 (by rfl) ⟨9597041, by rfl⟩ : syracuseStep 12796055 = 19194083) B19194083
theorem B8530703 : Blo 1995435 8530703 := bstep (se 1 (by rfl) ⟨6398027, by rfl⟩ : syracuseStep 8530703 = 12796055) B12796055
theorem B5687135 : Blo 1995435 5687135 := bstep (se 1 (by rfl) ⟨4265351, by rfl⟩ : syracuseStep 5687135 = 8530703) B8530703
theorem B3791423 : Blo 1995435 3791423 := bstep (se 1 (by rfl) ⟨2843567, by rfl⟩ : syracuseStep 3791423 = 5687135) B5687135
theorem B2527615 : Blo 1995435 2527615 := bstep (se 1 (by rfl) ⟨1895711, by rfl⟩ : syracuseStep 2527615 = 3791423) B3791423
theorem B3370153 : Blo 1995435 3370153 := bstep (se 2 (by rfl) ⟨1263807, by rfl⟩ : syracuseStep 3370153 = 2527615) B2527615
theorem B4493537 : Blo 1995435 4493537 := bstep (se 2 (by rfl) ⟨1685076, by rfl⟩ : syracuseStep 4493537 = 3370153) B3370153
theorem B2995691 : Blo 1995435 2995691 := bstep (se 1 (by rfl) ⟨2246768, by rfl⟩ : syracuseStep 2995691 = 4493537) B4493537
theorem B1997127 : Blo 1995435 1997127 := bstep (se 1 (by rfl) ⟨1497845, by rfl⟩ : syracuseStep 1997127 = 2995691) B2995691
theorem B2246773 : Blo 1995435 2246773 := bbase (se 5 (by rfl) ⟨105317, by rfl⟩ : syracuseStep 2246773 = 210635) (by norm_num)
theorem B2995697 : Blo 1995435 2995697 := bstep (se 2 (by rfl) ⟨1123386, by rfl⟩ : syracuseStep 2995697 = 2246773) B2246773
theorem B1997131 : Blo 1995435 1997131 := bstep (se 1 (by rfl) ⟨1497848, by rfl⟩ : syracuseStep 1997131 = 2995697) B2995697
theorem B2527625 : Blo 1995435 2527625 := bbase (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) (by norm_num)
theorem B6740333 : Blo 1995435 6740333 := bstep (se 3 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 6740333 = 2527625) B2527625
theorem B4493555 : Blo 1995435 4493555 := bstep (se 1 (by rfl) ⟨3370166, by rfl⟩ : syracuseStep 4493555 = 6740333) B6740333
theorem B2995703 : Blo 1995435 2995703 := bstep (se 1 (by rfl) ⟨2246777, by rfl⟩ : syracuseStep 2995703 = 4493555) B4493555
theorem B1997135 : Blo 1995435 1997135 := bstep (se 1 (by rfl) ⟨1497851, by rfl⟩ : syracuseStep 1997135 = 2995703) B2995703
theorem B2995709 : Blo 1995435 2995709 := bbase (se 3 (by rfl) ⟨561695, by rfl⟩ : syracuseStep 2995709 = 1123391) (by norm_num)
theorem B1997139 : Blo 1995435 1997139 := bstep (se 1 (by rfl) ⟨1497854, by rfl⟩ : syracuseStep 1997139 = 2995709) B2995709
theorem B4493573 : Blo 1995435 4493573 := bbase (se 4 (by rfl) ⟨421272, by rfl⟩ : syracuseStep 4493573 = 842545) (by norm_num)
theorem B2995715 : Blo 1995435 2995715 := bstep (se 1 (by rfl) ⟨2246786, by rfl⟩ : syracuseStep 2995715 = 4493573) B4493573
theorem B1997143 : Blo 1995435 1997143 := bstep (se 1 (by rfl) ⟨1497857, by rfl⟩ : syracuseStep 1997143 = 2995715) B2995715
theorem B3791461 : Blo 1995435 3791461 := bbase (se 4 (by rfl) ⟨355449, by rfl⟩ : syracuseStep 3791461 = 710899) (by norm_num)
theorem B5055281 : Blo 1995435 5055281 := bstep (se 2 (by rfl) ⟨1895730, by rfl⟩ : syracuseStep 5055281 = 3791461) B3791461
theorem B3370187 : Blo 1995435 3370187 := bstep (se 1 (by rfl) ⟨2527640, by rfl⟩ : syracuseStep 3370187 = 5055281) B5055281
theorem B2246791 : Blo 1995435 2246791 := bstep (se 1 (by rfl) ⟨1685093, by rfl⟩ : syracuseStep 2246791 = 3370187) B3370187
theorem B2995721 : Blo 1995435 2995721 := bstep (se 2 (by rfl) ⟨1123395, by rfl⟩ : syracuseStep 2995721 = 2246791) B2246791
theorem B1997147 : Blo 1995435 1997147 := bstep (se 1 (by rfl) ⟨1497860, by rfl⟩ : syracuseStep 1997147 = 2995721) B2995721
theorem B10110581 : Blo 1995435 10110581 := bbase (se 5 (by rfl) ⟨473933, by rfl⟩ : syracuseStep 10110581 = 947867) (by norm_num)
theorem B6740387 : Blo 1995435 6740387 := bstep (se 1 (by rfl) ⟨5055290, by rfl⟩ : syracuseStep 6740387 = 10110581) B10110581
theorem B4493591 : Blo 1995435 4493591 := bstep (se 1 (by rfl) ⟨3370193, by rfl⟩ : syracuseStep 4493591 = 6740387) B6740387
theorem B2995727 : Blo 1995435 2995727 := bstep (se 1 (by rfl) ⟨2246795, by rfl⟩ : syracuseStep 2995727 = 4493591) B4493591
theorem B1997151 : Blo 1995435 1997151 := bstep (se 1 (by rfl) ⟨1497863, by rfl⟩ : syracuseStep 1997151 = 2995727) B2995727
theorem B2995733 : Blo 1995435 2995733 := bbase (se 6 (by rfl) ⟨70212, by rfl⟩ : syracuseStep 2995733 = 140425) (by norm_num)
theorem B1997155 : Blo 1995435 1997155 := bstep (se 1 (by rfl) ⟨1497866, by rfl⟩ : syracuseStep 1997155 = 2995733) B2995733
theorem B4798597 : Blo 1995435 4798597 := bbase (se 4 (by rfl) ⟨449868, by rfl⟩ : syracuseStep 4798597 = 899737) (by norm_num)
theorem B6398129 : Blo 1995435 6398129 := bstep (se 2 (by rfl) ⟨2399298, by rfl⟩ : syracuseStep 6398129 = 4798597) B4798597
theorem B17061677 : Blo 1995435 17061677 := bstep (se 3 (by rfl) ⟨3199064, by rfl⟩ : syracuseStep 17061677 = 6398129) B6398129
theorem B11374451 : Blo 1995435 11374451 := bstep (se 1 (by rfl) ⟨8530838, by rfl⟩ : syracuseStep 11374451 = 17061677) B17061677
theorem B7582967 : Blo 1995435 7582967 := bstep (se 1 (by rfl) ⟨5687225, by rfl⟩ : syracuseStep 7582967 = 11374451) B11374451
theorem B5055311 : Blo 1995435 5055311 := bstep (se 1 (by rfl) ⟨3791483, by rfl⟩ : syracuseStep 5055311 = 7582967) B7582967
theorem B3370207 : Blo 1995435 3370207 := bstep (se 1 (by rfl) ⟨2527655, by rfl⟩ : syracuseStep 3370207 = 5055311) B5055311
theorem B4493609 : Blo 1995435 4493609 := bstep (se 2 (by rfl) ⟨1685103, by rfl⟩ : syracuseStep 4493609 = 3370207) B3370207
theorem B2995739 : Blo 1995435 2995739 := bstep (se 1 (by rfl) ⟨2246804, by rfl⟩ : syracuseStep 2995739 = 4493609) B4493609
theorem B1997159 : Blo 1995435 1997159 := bstep (se 1 (by rfl) ⟨1497869, by rfl⟩ : syracuseStep 1997159 = 2995739) B2995739
theorem B2246809 : Blo 1995435 2246809 := bbase (se 2 (by rfl) ⟨842553, by rfl⟩ : syracuseStep 2246809 = 1685107) (by norm_num)
theorem B2995745 : Blo 1995435 2995745 := bstep (se 2 (by rfl) ⟨1123404, by rfl⟩ : syracuseStep 2995745 = 2246809) B2246809
theorem B1997163 : Blo 1995435 1997163 := bstep (se 1 (by rfl) ⟨1497872, by rfl⟩ : syracuseStep 1997163 = 2995745) B2995745
theorem B7582997 : Blo 1995435 7582997 := bbase (se 6 (by rfl) ⟨177726, by rfl⟩ : syracuseStep 7582997 = 355453) (by norm_num)
theorem B5055331 : Blo 1995435 5055331 := bstep (se 1 (by rfl) ⟨3791498, by rfl⟩ : syracuseStep 5055331 = 7582997) B7582997
theorem B6740441 : Blo 1995435 6740441 := bstep (se 2 (by rfl) ⟨2527665, by rfl⟩ : syracuseStep 6740441 = 5055331) B5055331
theorem B4493627 : Blo 1995435 4493627 := bstep (se 1 (by rfl) ⟨3370220, by rfl⟩ : syracuseStep 4493627 = 6740441) B6740441
theorem B2995751 : Blo 1995435 2995751 := bstep (se 1 (by rfl) ⟨2246813, by rfl⟩ : syracuseStep 2995751 = 4493627) B4493627
theorem B1997167 : Blo 1995435 1997167 := bstep (se 1 (by rfl) ⟨1497875, by rfl⟩ : syracuseStep 1997167 = 2995751) B2995751
theorem B2995757 : Blo 1995435 2995757 := bbase (se 3 (by rfl) ⟨561704, by rfl⟩ : syracuseStep 2995757 = 1123409) (by norm_num)
theorem B1997171 : Blo 1995435 1997171 := bstep (se 1 (by rfl) ⟨1497878, by rfl⟩ : syracuseStep 1997171 = 2995757) B2995757
theorem B4493645 : Blo 1995435 4493645 := bbase (se 3 (by rfl) ⟨842558, by rfl⟩ : syracuseStep 4493645 = 1685117) (by norm_num)
theorem B2995763 : Blo 1995435 2995763 := bstep (se 1 (by rfl) ⟨2246822, by rfl⟩ : syracuseStep 2995763 = 4493645) B4493645
theorem B1997175 : Blo 1995435 1997175 := bstep (se 1 (by rfl) ⟨1497881, by rfl⟩ : syracuseStep 1997175 = 2995763) B2995763
theorem B2527681 : Blo 1995435 2527681 := bbase (se 2 (by rfl) ⟨947880, by rfl⟩ : syracuseStep 2527681 = 1895761) (by norm_num)
theorem B3370241 : Blo 1995435 3370241 := bstep (se 2 (by rfl) ⟨1263840, by rfl⟩ : syracuseStep 3370241 = 2527681) B2527681
theorem B2246827 : Blo 1995435 2246827 := bstep (se 1 (by rfl) ⟨1685120, by rfl⟩ : syracuseStep 2246827 = 3370241) B3370241
theorem B2995769 : Blo 1995435 2995769 := bstep (se 2 (by rfl) ⟨1123413, by rfl⟩ : syracuseStep 2995769 = 2246827) B2246827
theorem B1997179 : Blo 1995435 1997179 := bstep (se 1 (by rfl) ⟨1497884, by rfl⟩ : syracuseStep 1997179 = 2995769) B2995769
theorem B2562173 : Blo 1995435 2562173 := bbase (se 3 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 2562173 = 960815) (by norm_num)
theorem B27329845 : Blo 1995435 27329845 := bstep (se 5 (by rfl) ⟨1281086, by rfl⟩ : syracuseStep 27329845 = 2562173) B2562173
theorem B36439793 : Blo 1995435 36439793 := bstep (se 2 (by rfl) ⟨13664922, by rfl⟩ : syracuseStep 36439793 = 27329845) B27329845
theorem B24293195 : Blo 1995435 24293195 := bstep (se 1 (by rfl) ⟨18219896, by rfl⟩ : syracuseStep 24293195 = 36439793) B36439793
theorem B16195463 : Blo 1995435 16195463 := bstep (se 1 (by rfl) ⟨12146597, by rfl⟩ : syracuseStep 16195463 = 24293195) B24293195
theorem B10796975 : Blo 1995435 10796975 := bstep (se 1 (by rfl) ⟨8097731, by rfl⟩ : syracuseStep 10796975 = 16195463) B16195463
theorem B7197983 : Blo 1995435 7197983 := bstep (se 1 (by rfl) ⟨5398487, by rfl⟩ : syracuseStep 7197983 = 10796975) B10796975
theorem B4798655 : Blo 1995435 4798655 := bstep (se 1 (by rfl) ⟨3598991, by rfl⟩ : syracuseStep 4798655 = 7197983) B7197983
theorem B3199103 : Blo 1995435 3199103 := bstep (se 1 (by rfl) ⟨2399327, by rfl⟩ : syracuseStep 3199103 = 4798655) B4798655
theorem B2132735 : Blo 1995435 2132735 := bstep (se 1 (by rfl) ⟨1599551, by rfl⟩ : syracuseStep 2132735 = 3199103) B3199103
theorem B22749173 : Blo 1995435 22749173 := bstep (se 5 (by rfl) ⟨1066367, by rfl⟩ : syracuseStep 22749173 = 2132735) B2132735
theorem B15166115 : Blo 1995435 15166115 := bstep (se 1 (by rfl) ⟨11374586, by rfl⟩ : syracuseStep 15166115 = 22749173) B22749173
theorem B10110743 : Blo 1995435 10110743 := bstep (se 1 (by rfl) ⟨7583057, by rfl⟩ : syracuseStep 10110743 = 15166115) B15166115
theorem B6740495 : Blo 1995435 6740495 := bstep (se 1 (by rfl) ⟨5055371, by rfl⟩ : syracuseStep 6740495 = 10110743) B10110743
theorem B4493663 : Blo 1995435 4493663 := bstep (se 1 (by rfl) ⟨3370247, by rfl⟩ : syracuseStep 4493663 = 6740495) B6740495
theorem B2995775 : Blo 1995435 2995775 := bstep (se 1 (by rfl) ⟨2246831, by rfl⟩ : syracuseStep 2995775 = 4493663) B4493663
theorem B1997183 : Blo 1995435 1997183 := bstep (se 1 (by rfl) ⟨1497887, by rfl⟩ : syracuseStep 1997183 = 2995775) B2995775
theorem B2995781 : Blo 1995435 2995781 := bbase (se 4 (by rfl) ⟨280854, by rfl⟩ : syracuseStep 2995781 = 561709) (by norm_num)
theorem B1997187 : Blo 1995435 1997187 := bstep (se 1 (by rfl) ⟨1497890, by rfl⟩ : syracuseStep 1997187 = 2995781) B2995781
theorem B3370261 : Blo 1995435 3370261 := bbase (se 6 (by rfl) ⟨78990, by rfl⟩ : syracuseStep 3370261 = 157981) (by norm_num)
theorem B4493681 : Blo 1995435 4493681 := bstep (se 2 (by rfl) ⟨1685130, by rfl⟩ : syracuseStep 4493681 = 3370261) B3370261
theorem B2995787 : Blo 1995435 2995787 := bstep (se 1 (by rfl) ⟨2246840, by rfl⟩ : syracuseStep 2995787 = 4493681) B4493681
theorem B1997191 : Blo 1995435 1997191 := bstep (se 1 (by rfl) ⟨1497893, by rfl⟩ : syracuseStep 1997191 = 2995787) B2995787
theorem B2246845 : Blo 1995435 2246845 := bbase (se 3 (by rfl) ⟨421283, by rfl⟩ : syracuseStep 2246845 = 842567) (by norm_num)
theorem B2995793 : Blo 1995435 2995793 := bstep (se 2 (by rfl) ⟨1123422, by rfl⟩ : syracuseStep 2995793 = 2246845) B2246845
theorem B1997195 : Blo 1995435 1997195 := bstep (se 1 (by rfl) ⟨1497896, by rfl⟩ : syracuseStep 1997195 = 2995793) B2995793
theorem B6740549 : Blo 1995435 6740549 := bbase (se 4 (by rfl) ⟨631926, by rfl⟩ : syracuseStep 6740549 = 1263853) (by norm_num)
theorem B4493699 : Blo 1995435 4493699 := bstep (se 1 (by rfl) ⟨3370274, by rfl⟩ : syracuseStep 4493699 = 6740549) B6740549
theorem B2995799 : Blo 1995435 2995799 := bstep (se 1 (by rfl) ⟨2246849, by rfl⟩ : syracuseStep 2995799 = 4493699) B4493699
theorem B1997199 : Blo 1995435 1997199 := bstep (se 1 (by rfl) ⟨1497899, by rfl⟩ : syracuseStep 1997199 = 2995799) B2995799
theorem B2995805 : Blo 1995435 2995805 := bbase (se 3 (by rfl) ⟨561713, by rfl⟩ : syracuseStep 2995805 = 1123427) (by norm_num)
theorem B1997203 : Blo 1995435 1997203 := bstep (se 1 (by rfl) ⟨1497902, by rfl⟩ : syracuseStep 1997203 = 2995805) B2995805
theorem B4493717 : Blo 1995435 4493717 := bbase (se 6 (by rfl) ⟨105321, by rfl⟩ : syracuseStep 4493717 = 210643) (by norm_num)
theorem B2995811 : Blo 1995435 2995811 := bstep (se 1 (by rfl) ⟨2246858, by rfl⟩ : syracuseStep 2995811 = 4493717) B4493717
theorem B1997207 : Blo 1995435 1997207 := bstep (se 1 (by rfl) ⟨1497905, by rfl⟩ : syracuseStep 1997207 = 2995811) B2995811
theorem B7198085 : Blo 1995435 7198085 := bbase (se 4 (by rfl) ⟨674820, by rfl⟩ : syracuseStep 7198085 = 1349641) (by norm_num)
theorem B4798723 : Blo 1995435 4798723 := bstep (se 1 (by rfl) ⟨3599042, by rfl⟩ : syracuseStep 4798723 = 7198085) B7198085
theorem B6398297 : Blo 1995435 6398297 := bstep (se 2 (by rfl) ⟨2399361, by rfl⟩ : syracuseStep 6398297 = 4798723) B4798723
theorem B4265531 : Blo 1995435 4265531 := bstep (se 1 (by rfl) ⟨3199148, by rfl⟩ : syracuseStep 4265531 = 6398297) B6398297
theorem B2843687 : Blo 1995435 2843687 := bstep (se 1 (by rfl) ⟨2132765, by rfl⟩ : syracuseStep 2843687 = 4265531) B4265531
theorem B7583165 : Blo 1995435 7583165 := bstep (se 3 (by rfl) ⟨1421843, by rfl⟩ : syracuseStep 7583165 = 2843687) B2843687
theorem B5055443 : Blo 1995435 5055443 := bstep (se 1 (by rfl) ⟨3791582, by rfl⟩ : syracuseStep 5055443 = 7583165) B7583165
theorem B3370295 : Blo 1995435 3370295 := bstep (se 1 (by rfl) ⟨2527721, by rfl⟩ : syracuseStep 3370295 = 5055443) B5055443
theorem B2246863 : Blo 1995435 2246863 := bstep (se 1 (by rfl) ⟨1685147, by rfl⟩ : syracuseStep 2246863 = 3370295) B3370295
theorem B2995817 : Blo 1995435 2995817 := bstep (se 2 (by rfl) ⟨1123431, by rfl⟩ : syracuseStep 2995817 = 2246863) B2246863
theorem B1997211 : Blo 1995435 1997211 := bstep (se 1 (by rfl) ⟨1497908, by rfl⟩ : syracuseStep 1997211 = 2995817) B2995817
theorem B8531077 : Blo 1995435 8531077 := bbase (se 4 (by rfl) ⟨799788, by rfl⟩ : syracuseStep 8531077 = 1599577) (by norm_num)
theorem B11374769 : Blo 1995435 11374769 := bstep (se 2 (by rfl) ⟨4265538, by rfl⟩ : syracuseStep 11374769 = 8531077) B8531077
theorem B7583179 : Blo 1995435 7583179 := bstep (se 1 (by rfl) ⟨5687384, by rfl⟩ : syracuseStep 7583179 = 11374769) B11374769
theorem B10110905 : Blo 1995435 10110905 := bstep (se 2 (by rfl) ⟨3791589, by rfl⟩ : syracuseStep 10110905 = 7583179) B7583179
theorem B6740603 : Blo 1995435 6740603 := bstep (se 1 (by rfl) ⟨5055452, by rfl⟩ : syracuseStep 6740603 = 10110905) B10110905
theorem B4493735 : Blo 1995435 4493735 := bstep (se 1 (by rfl) ⟨3370301, by rfl⟩ : syracuseStep 4493735 = 6740603) B6740603
theorem B2995823 : Blo 1995435 2995823 := bstep (se 1 (by rfl) ⟨2246867, by rfl⟩ : syracuseStep 2995823 = 4493735) B4493735
theorem B1997215 : Blo 1995435 1997215 := bstep (se 1 (by rfl) ⟨1497911, by rfl⟩ : syracuseStep 1997215 = 2995823) B2995823
theorem B2995829 : Blo 1995435 2995829 := bbase (se 5 (by rfl) ⟨140429, by rfl⟩ : syracuseStep 2995829 = 280859) (by norm_num)
theorem B1997219 : Blo 1995435 1997219 := bstep (se 1 (by rfl) ⟨1497914, by rfl⟩ : syracuseStep 1997219 = 2995829) B2995829
theorem B3791605 : Blo 1995435 3791605 := bbase (se 5 (by rfl) ⟨177731, by rfl⟩ : syracuseStep 3791605 = 355463) (by norm_num)
theorem B5055473 : Blo 1995435 5055473 := bstep (se 2 (by rfl) ⟨1895802, by rfl⟩ : syracuseStep 5055473 = 3791605) B3791605
theorem B3370315 : Blo 1995435 3370315 := bstep (se 1 (by rfl) ⟨2527736, by rfl⟩ : syracuseStep 3370315 = 5055473) B5055473
theorem B4493753 : Blo 1995435 4493753 := bstep (se 2 (by rfl) ⟨1685157, by rfl⟩ : syracuseStep 4493753 = 3370315) B3370315
theorem B2995835 : Blo 1995435 2995835 := bstep (se 1 (by rfl) ⟨2246876, by rfl⟩ : syracuseStep 2995835 = 4493753) B4493753
theorem B1997223 : Blo 1995435 1997223 := bstep (se 1 (by rfl) ⟨1497917, by rfl⟩ : syracuseStep 1997223 = 2995835) B2995835
theorem B2246881 : Blo 1995435 2246881 := bbase (se 2 (by rfl) ⟨842580, by rfl⟩ : syracuseStep 2246881 = 1685161) (by norm_num)
theorem B2995841 : Blo 1995435 2995841 := bstep (se 2 (by rfl) ⟨1123440, by rfl⟩ : syracuseStep 2995841 = 2246881) B2246881
theorem B1997227 : Blo 1995435 1997227 := bstep (se 1 (by rfl) ⟨1497920, by rfl⟩ : syracuseStep 1997227 = 2995841) B2995841
theorem B5055493 : Blo 1995435 5055493 := bbase (se 4 (by rfl) ⟨473952, by rfl⟩ : syracuseStep 5055493 = 947905) (by norm_num)
theorem B6740657 : Blo 1995435 6740657 := bstep (se 2 (by rfl) ⟨2527746, by rfl⟩ : syracuseStep 6740657 = 5055493) B5055493
theorem B4493771 : Blo 1995435 4493771 := bstep (se 1 (by rfl) ⟨3370328, by rfl⟩ : syracuseStep 4493771 = 6740657) B6740657
theorem B2995847 : Blo 1995435 2995847 := bstep (se 1 (by rfl) ⟨2246885, by rfl⟩ : syracuseStep 2995847 = 4493771) B4493771
theorem B1997231 : Blo 1995435 1997231 := bstep (se 1 (by rfl) ⟨1497923, by rfl⟩ : syracuseStep 1997231 = 2995847) B2995847
theorem B2995853 : Blo 1995435 2995853 := bbase (se 3 (by rfl) ⟨561722, by rfl⟩ : syracuseStep 2995853 = 1123445) (by norm_num)
theorem B1997235 : Blo 1995435 1997235 := bstep (se 1 (by rfl) ⟨1497926, by rfl⟩ : syracuseStep 1997235 = 2995853) B2995853
theorem B4493789 : Blo 1995435 4493789 := bbase (se 3 (by rfl) ⟨842585, by rfl⟩ : syracuseStep 4493789 = 1685171) (by norm_num)
theorem B2995859 : Blo 1995435 2995859 := bstep (se 1 (by rfl) ⟨2246894, by rfl⟩ : syracuseStep 2995859 = 4493789) B4493789
theorem B1997239 : Blo 1995435 1997239 := bstep (se 1 (by rfl) ⟨1497929, by rfl⟩ : syracuseStep 1997239 = 2995859) B2995859
theorem B3370349 : Blo 1995435 3370349 := bbase (se 3 (by rfl) ⟨631940, by rfl⟩ : syracuseStep 3370349 = 1263881) (by norm_num)
theorem B2246899 : Blo 1995435 2246899 := bstep (se 1 (by rfl) ⟨1685174, by rfl⟩ : syracuseStep 2246899 = 3370349) B3370349
theorem B2995865 : Blo 1995435 2995865 := bstep (se 2 (by rfl) ⟨1123449, by rfl⟩ : syracuseStep 2995865 = 2246899) B2246899
theorem B1997243 : Blo 1995435 1997243 := bstep (se 1 (by rfl) ⟨1497932, by rfl⟩ : syracuseStep 1997243 = 2995865) B2995865
theorem B5124509 : Blo 1995435 5124509 := bbase (se 3 (by rfl) ⟨960845, by rfl⟩ : syracuseStep 5124509 = 1921691) (by norm_num)
theorem B3416339 : Blo 1995435 3416339 := bstep (se 1 (by rfl) ⟨2562254, by rfl⟩ : syracuseStep 3416339 = 5124509) B5124509
theorem B9110237 : Blo 1995435 9110237 := bstep (se 3 (by rfl) ⟨1708169, by rfl⟩ : syracuseStep 9110237 = 3416339) B3416339
theorem B97175861 : Blo 1995435 97175861 := bstep (se 5 (by rfl) ⟨4555118, by rfl⟩ : syracuseStep 97175861 = 9110237) B9110237
theorem B64783907 : Blo 1995435 64783907 := bstep (se 1 (by rfl) ⟨48587930, by rfl⟩ : syracuseStep 64783907 = 97175861) B97175861
theorem B43189271 : Blo 1995435 43189271 := bstep (se 1 (by rfl) ⟨32391953, by rfl⟩ : syracuseStep 43189271 = 64783907) B64783907
theorem B28792847 : Blo 1995435 28792847 := bstep (se 1 (by rfl) ⟨21594635, by rfl⟩ : syracuseStep 28792847 = 43189271) B43189271
theorem B19195231 : Blo 1995435 19195231 := bstep (se 1 (by rfl) ⟨14396423, by rfl⟩ : syracuseStep 19195231 = 28792847) B28792847
theorem B25593641 : Blo 1995435 25593641 := bstep (se 2 (by rfl) ⟨9597615, by rfl⟩ : syracuseStep 25593641 = 19195231) B19195231
theorem B17062427 : Blo 1995435 17062427 := bstep (se 1 (by rfl) ⟨12796820, by rfl⟩ : syracuseStep 17062427 = 25593641) B25593641
theorem B11374951 : Blo 1995435 11374951 := bstep (se 1 (by rfl) ⟨8531213, by rfl⟩ : syracuseStep 11374951 = 17062427) B17062427
theorem B15166601 : Blo 1995435 15166601 := bstep (se 2 (by rfl) ⟨5687475, by rfl⟩ : syracuseStep 15166601 = 11374951) B11374951
theorem B10111067 : Blo 1995435 10111067 := bstep (se 1 (by rfl) ⟨7583300, by rfl⟩ : syracuseStep 10111067 = 15166601) B15166601
theorem B6740711 : Blo 1995435 6740711 := bstep (se 1 (by rfl) ⟨5055533, by rfl⟩ : syracuseStep 6740711 = 10111067) B10111067
theorem B4493807 : Blo 1995435 4493807 := bstep (se 1 (by rfl) ⟨3370355, by rfl⟩ : syracuseStep 4493807 = 6740711) B6740711
theorem B2995871 : Blo 1995435 2995871 := bstep (se 1 (by rfl) ⟨2246903, by rfl⟩ : syracuseStep 2995871 = 4493807) B4493807
theorem B1997247 : Blo 1995435 1997247 := bstep (se 1 (by rfl) ⟨1497935, by rfl⟩ : syracuseStep 1997247 = 2995871) B2995871
theorem B2995877 : Blo 1995435 2995877 := bbase (se 4 (by rfl) ⟨280863, by rfl⟩ : syracuseStep 2995877 = 561727) (by norm_num)
theorem B1997251 : Blo 1995435 1997251 := bstep (se 1 (by rfl) ⟨1497938, by rfl⟩ : syracuseStep 1997251 = 2995877) B2995877
theorem B2527777 : Blo 1995435 2527777 := bbase (se 2 (by rfl) ⟨947916, by rfl⟩ : syracuseStep 2527777 = 1895833) (by norm_num)
theorem B3370369 : Blo 1995435 3370369 := bstep (se 2 (by rfl) ⟨1263888, by rfl⟩ : syracuseStep 3370369 = 2527777) B2527777
theorem B4493825 : Blo 1995435 4493825 := bstep (se 2 (by rfl) ⟨1685184, by rfl⟩ : syracuseStep 4493825 = 3370369) B3370369
theorem B2995883 : Blo 1995435 2995883 := bstep (se 1 (by rfl) ⟨2246912, by rfl⟩ : syracuseStep 2995883 = 4493825) B4493825
theorem B1997255 : Blo 1995435 1997255 := bstep (se 1 (by rfl) ⟨1497941, by rfl⟩ : syracuseStep 1997255 = 2995883) B2995883
theorem B2246917 : Blo 1995435 2246917 := bbase (se 4 (by rfl) ⟨210648, by rfl⟩ : syracuseStep 2246917 = 421297) (by norm_num)
theorem B2995889 : Blo 1995435 2995889 := bstep (se 2 (by rfl) ⟨1123458, by rfl⟩ : syracuseStep 2995889 = 2246917) B2246917
theorem B1997259 : Blo 1995435 1997259 := bstep (se 1 (by rfl) ⟨1497944, by rfl⟩ : syracuseStep 1997259 = 2995889) B2995889
theorem B2132821 : Blo 1995435 2132821 := bbase (se 9 (by rfl) ⟨6248, by rfl⟩ : syracuseStep 2132821 = 12497) (by norm_num)
theorem B2843761 : Blo 1995435 2843761 := bstep (se 2 (by rfl) ⟨1066410, by rfl⟩ : syracuseStep 2843761 = 2132821) B2132821
theorem B3791681 : Blo 1995435 3791681 := bstep (se 2 (by rfl) ⟨1421880, by rfl⟩ : syracuseStep 3791681 = 2843761) B2843761
theorem B2527787 : Blo 1995435 2527787 := bstep (se 1 (by rfl) ⟨1895840, by rfl⟩ : syracuseStep 2527787 = 3791681) B3791681
theorem B6740765 : Blo 1995435 6740765 := bstep (se 3 (by rfl) ⟨1263893, by rfl⟩ : syracuseStep 6740765 = 2527787) B2527787
theorem B4493843 : Blo 1995435 4493843 := bstep (se 1 (by rfl) ⟨3370382, by rfl⟩ : syracuseStep 4493843 = 6740765) B6740765
theorem B2995895 : Blo 1995435 2995895 := bstep (se 1 (by rfl) ⟨2246921, by rfl⟩ : syracuseStep 2995895 = 4493843) B4493843
theorem B1997263 : Blo 1995435 1997263 := bstep (se 1 (by rfl) ⟨1497947, by rfl⟩ : syracuseStep 1997263 = 2995895) B2995895
theorem B2995901 : Blo 1995435 2995901 := bbase (se 3 (by rfl) ⟨561731, by rfl⟩ : syracuseStep 2995901 = 1123463) (by norm_num)
theorem B1997267 : Blo 1995435 1997267 := bstep (se 1 (by rfl) ⟨1497950, by rfl⟩ : syracuseStep 1997267 = 2995901) B2995901
theorem B4493861 : Blo 1995435 4493861 := bbase (se 4 (by rfl) ⟨421299, by rfl⟩ : syracuseStep 4493861 = 842599) (by norm_num)
theorem B2995907 : Blo 1995435 2995907 := bstep (se 1 (by rfl) ⟨2246930, by rfl⟩ : syracuseStep 2995907 = 4493861) B4493861
theorem B1997271 : Blo 1995435 1997271 := bstep (se 1 (by rfl) ⟨1497953, by rfl⟩ : syracuseStep 1997271 = 2995907) B2995907
theorem B5055605 : Blo 1995435 5055605 := bbase (se 5 (by rfl) ⟨236981, by rfl⟩ : syracuseStep 5055605 = 473963) (by norm_num)
theorem B3370403 : Blo 1995435 3370403 := bstep (se 1 (by rfl) ⟨2527802, by rfl⟩ : syracuseStep 3370403 = 5055605) B5055605
theorem B2246935 : Blo 1995435 2246935 := bstep (se 1 (by rfl) ⟨1685201, by rfl⟩ : syracuseStep 2246935 = 3370403) B3370403
theorem B2995913 : Blo 1995435 2995913 := bstep (se 2 (by rfl) ⟨1123467, by rfl⟩ : syracuseStep 2995913 = 2246935) B2246935
theorem B1997275 : Blo 1995435 1997275 := bstep (se 1 (by rfl) ⟨1497956, by rfl⟩ : syracuseStep 1997275 = 2995913) B2995913
theorem B19195541 : Blo 1995435 19195541 := bbase (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) (by norm_num)
theorem B12797027 : Blo 1995435 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B8531351 : Blo 1995435 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B5687567 : Blo 1995435 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B3791711 : Blo 1995435 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B10111229 : Blo 1995435 10111229 := bstep (se 3 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 10111229 = 3791711) B3791711
theorem B6740819 : Blo 1995435 6740819 := bstep (se 1 (by rfl) ⟨5055614, by rfl⟩ : syracuseStep 6740819 = 10111229) B10111229
theorem B4493879 : Blo 1995435 4493879 := bstep (se 1 (by rfl) ⟨3370409, by rfl⟩ : syracuseStep 4493879 = 6740819) B6740819
theorem B2995919 : Blo 1995435 2995919 := bstep (se 1 (by rfl) ⟨2246939, by rfl⟩ : syracuseStep 2995919 = 4493879) B4493879
theorem B1997279 : Blo 1995435 1997279 := bstep (se 1 (by rfl) ⟨1497959, by rfl⟩ : syracuseStep 1997279 = 2995919) B2995919
theorem B2995925 : Blo 1995435 2995925 := bbase (se 7 (by rfl) ⟨35108, by rfl⟩ : syracuseStep 2995925 = 70217) (by norm_num)
theorem B1997283 : Blo 1995435 1997283 := bstep (se 1 (by rfl) ⟨1497962, by rfl⟩ : syracuseStep 1997283 = 2995925) B2995925
theorem B4265693 : Blo 1995435 4265693 := bbase (se 3 (by rfl) ⟨799817, by rfl⟩ : syracuseStep 4265693 = 1599635) (by norm_num)
theorem B2843795 : Blo 1995435 2843795 := bstep (se 1 (by rfl) ⟨2132846, by rfl⟩ : syracuseStep 2843795 = 4265693) B4265693
theorem B7583453 : Blo 1995435 7583453 := bstep (se 3 (by rfl) ⟨1421897, by rfl⟩ : syracuseStep 7583453 = 2843795) B2843795
theorem B5055635 : Blo 1995435 5055635 := bstep (se 1 (by rfl) ⟨3791726, by rfl⟩ : syracuseStep 5055635 = 7583453) B7583453
theorem B3370423 : Blo 1995435 3370423 := bstep (se 1 (by rfl) ⟨2527817, by rfl⟩ : syracuseStep 3370423 = 5055635) B5055635
theorem B4493897 : Blo 1995435 4493897 := bstep (se 2 (by rfl) ⟨1685211, by rfl⟩ : syracuseStep 4493897 = 3370423) B3370423
theorem B2995931 : Blo 1995435 2995931 := bstep (se 1 (by rfl) ⟨2246948, by rfl⟩ : syracuseStep 2995931 = 4493897) B4493897
theorem B1997287 : Blo 1995435 1997287 := bstep (se 1 (by rfl) ⟨1497965, by rfl⟩ : syracuseStep 1997287 = 2995931) B2995931
theorem B2246953 : Blo 1995435 2246953 := bbase (se 2 (by rfl) ⟨842607, by rfl⟩ : syracuseStep 2246953 = 1685215) (by norm_num)
theorem B2995937 : Blo 1995435 2995937 := bstep (se 2 (by rfl) ⟨1123476, by rfl⟩ : syracuseStep 2995937 = 2246953) B2246953
theorem B1997291 : Blo 1995435 1997291 := bstep (se 1 (by rfl) ⟨1497968, by rfl⟩ : syracuseStep 1997291 = 2995937) B2995937
theorem B21595157 : Blo 1995435 21595157 := bbase (se 6 (by rfl) ⟨506136, by rfl⟩ : syracuseStep 21595157 = 1012273) (by norm_num)
theorem B14396771 : Blo 1995435 14396771 := bstep (se 1 (by rfl) ⟨10797578, by rfl⟩ : syracuseStep 14396771 = 21595157) B21595157
theorem B9597847 : Blo 1995435 9597847 := bstep (se 1 (by rfl) ⟨7198385, by rfl⟩ : syracuseStep 9597847 = 14396771) B14396771
theorem B12797129 : Blo 1995435 12797129 := bstep (se 2 (by rfl) ⟨4798923, by rfl⟩ : syracuseStep 12797129 = 9597847) B9597847
theorem B8531419 : Blo 1995435 8531419 := bstep (se 1 (by rfl) ⟨6398564, by rfl⟩ : syracuseStep 8531419 = 12797129) B12797129
theorem B11375225 : Blo 1995435 11375225 := bstep (se 2 (by rfl) ⟨4265709, by rfl⟩ : syracuseStep 11375225 = 8531419) B8531419
theorem B7583483 : Blo 1995435 7583483 := bstep (se 1 (by rfl) ⟨5687612, by rfl⟩ : syracuseStep 7583483 = 11375225) B11375225
theorem B5055655 : Blo 1995435 5055655 := bstep (se 1 (by rfl) ⟨3791741, by rfl⟩ : syracuseStep 5055655 = 7583483) B7583483
theorem B6740873 : Blo 1995435 6740873 := bstep (se 2 (by rfl) ⟨2527827, by rfl⟩ : syracuseStep 6740873 = 5055655) B5055655
theorem B4493915 : Blo 1995435 4493915 := bstep (se 1 (by rfl) ⟨3370436, by rfl⟩ : syracuseStep 4493915 = 6740873) B6740873
theorem B2995943 : Blo 1995435 2995943 := bstep (se 1 (by rfl) ⟨2246957, by rfl⟩ : syracuseStep 2995943 = 4493915) B4493915
theorem B1997295 : Blo 1995435 1997295 := bstep (se 1 (by rfl) ⟨1497971, by rfl⟩ : syracuseStep 1997295 = 2995943) B2995943
theorem B2995949 : Blo 1995435 2995949 := bbase (se 3 (by rfl) ⟨561740, by rfl⟩ : syracuseStep 2995949 = 1123481) (by norm_num)
theorem B1997299 : Blo 1995435 1997299 := bstep (se 1 (by rfl) ⟨1497974, by rfl⟩ : syracuseStep 1997299 = 2995949) B2995949
theorem B4493933 : Blo 1995435 4493933 := bbase (se 3 (by rfl) ⟨842612, by rfl⟩ : syracuseStep 4493933 = 1685225) (by norm_num)
theorem B2995955 : Blo 1995435 2995955 := bstep (se 1 (by rfl) ⟨2246966, by rfl⟩ : syracuseStep 2995955 = 4493933) B4493933
theorem B1997303 : Blo 1995435 1997303 := bstep (se 1 (by rfl) ⟨1497977, by rfl⟩ : syracuseStep 1997303 = 2995955) B2995955
theorem B3791765 : Blo 1995435 3791765 := bbase (se 6 (by rfl) ⟨88869, by rfl⟩ : syracuseStep 3791765 = 177739) (by norm_num)
theorem B2527843 : Blo 1995435 2527843 := bstep (se 1 (by rfl) ⟨1895882, by rfl⟩ : syracuseStep 2527843 = 3791765) B3791765
theorem B3370457 : Blo 1995435 3370457 := bstep (se 2 (by rfl) ⟨1263921, by rfl⟩ : syracuseStep 3370457 = 2527843) B2527843
theorem B2246971 : Blo 1995435 2246971 := bstep (se 1 (by rfl) ⟨1685228, by rfl⟩ : syracuseStep 2246971 = 3370457) B3370457
theorem B2995961 : Blo 1995435 2995961 := bstep (se 2 (by rfl) ⟨1123485, by rfl⟩ : syracuseStep 2995961 = 2246971) B2246971
theorem B1997307 : Blo 1995435 1997307 := bstep (se 1 (by rfl) ⟨1497980, by rfl⟩ : syracuseStep 1997307 = 2995961) B2995961
theorem B2191469 : Blo 1995435 2191469 := bbase (se 3 (by rfl) ⟨410900, by rfl⟩ : syracuseStep 2191469 = 821801) (by norm_num)
theorem B5843917 : Blo 1995435 5843917 := bstep (se 3 (by rfl) ⟨1095734, by rfl⟩ : syracuseStep 5843917 = 2191469) B2191469
theorem B7791889 : Blo 1995435 7791889 := bstep (se 2 (by rfl) ⟨2921958, by rfl⟩ : syracuseStep 7791889 = 5843917) B5843917
theorem B10389185 : Blo 1995435 10389185 := bstep (se 2 (by rfl) ⟨3895944, by rfl⟩ : syracuseStep 10389185 = 7791889) B7791889
theorem B6926123 : Blo 1995435 6926123 := bstep (se 1 (by rfl) ⟨5194592, by rfl⟩ : syracuseStep 6926123 = 10389185) B10389185
theorem B4617415 : Blo 1995435 4617415 := bstep (se 1 (by rfl) ⟨3463061, by rfl⟩ : syracuseStep 4617415 = 6926123) B6926123
theorem B24626213 : Blo 1995435 24626213 := bstep (se 4 (by rfl) ⟨2308707, by rfl⟩ : syracuseStep 24626213 = 4617415) B4617415
theorem B16417475 : Blo 1995435 16417475 := bstep (se 1 (by rfl) ⟨12313106, by rfl⟩ : syracuseStep 16417475 = 24626213) B24626213
theorem B10944983 : Blo 1995435 10944983 := bstep (se 1 (by rfl) ⟨8208737, by rfl⟩ : syracuseStep 10944983 = 16417475) B16417475
theorem B7296655 : Blo 1995435 7296655 := bstep (se 1 (by rfl) ⟨5472491, by rfl⟩ : syracuseStep 7296655 = 10944983) B10944983
theorem B9728873 : Blo 1995435 9728873 := bstep (se 2 (by rfl) ⟨3648327, by rfl⟩ : syracuseStep 9728873 = 7296655) B7296655
theorem B6485915 : Blo 1995435 6485915 := bstep (se 1 (by rfl) ⟨4864436, by rfl⟩ : syracuseStep 6485915 = 9728873) B9728873
theorem B4323943 : Blo 1995435 4323943 := bstep (se 1 (by rfl) ⟨3242957, by rfl⟩ : syracuseStep 4323943 = 6485915) B6485915
theorem B5765257 : Blo 1995435 5765257 := bstep (se 2 (by rfl) ⟨2161971, by rfl⟩ : syracuseStep 5765257 = 4323943) B4323943
theorem B7687009 : Blo 1995435 7687009 := bstep (se 2 (by rfl) ⟨2882628, by rfl⟩ : syracuseStep 7687009 = 5765257) B5765257
theorem B10249345 : Blo 1995435 10249345 := bstep (se 2 (by rfl) ⟨3843504, by rfl⟩ : syracuseStep 10249345 = 7687009) B7687009
theorem B54663173 : Blo 1995435 54663173 := bstep (se 4 (by rfl) ⟨5124672, by rfl⟩ : syracuseStep 54663173 = 10249345) B10249345
theorem B36442115 : Blo 1995435 36442115 := bstep (se 1 (by rfl) ⟨27331586, by rfl⟩ : syracuseStep 36442115 = 54663173) B54663173
theorem B24294743 : Blo 1995435 24294743 := bstep (se 1 (by rfl) ⟨18221057, by rfl⟩ : syracuseStep 24294743 = 36442115) B36442115
theorem B16196495 : Blo 1995435 16196495 := bstep (se 1 (by rfl) ⟨12147371, by rfl⟩ : syracuseStep 16196495 = 24294743) B24294743
theorem B43190653 : Blo 1995435 43190653 := bstep (se 3 (by rfl) ⟨8098247, by rfl⟩ : syracuseStep 43190653 = 16196495) B16196495
theorem B57587537 : Blo 1995435 57587537 := bstep (se 2 (by rfl) ⟨21595326, by rfl⟩ : syracuseStep 57587537 = 43190653) B43190653
theorem B38391691 : Blo 1995435 38391691 := bstep (se 1 (by rfl) ⟨28793768, by rfl⟩ : syracuseStep 38391691 = 57587537) B57587537
theorem B51188921 : Blo 1995435 51188921 := bstep (se 2 (by rfl) ⟨19195845, by rfl⟩ : syracuseStep 51188921 = 38391691) B38391691
theorem B34125947 : Blo 1995435 34125947 := bstep (se 1 (by rfl) ⟨25594460, by rfl⟩ : syracuseStep 34125947 = 51188921) B51188921
theorem B22750631 : Blo 1995435 22750631 := bstep (se 1 (by rfl) ⟨17062973, by rfl⟩ : syracuseStep 22750631 = 34125947) B34125947
theorem B15167087 : Blo 1995435 15167087 := bstep (se 1 (by rfl) ⟨11375315, by rfl⟩ : syracuseStep 15167087 = 22750631) B22750631
theorem B10111391 : Blo 1995435 10111391 := bstep (se 1 (by rfl) ⟨7583543, by rfl⟩ : syracuseStep 10111391 = 15167087) B15167087
theorem B6740927 : Blo 1995435 6740927 := bstep (se 1 (by rfl) ⟨5055695, by rfl⟩ : syracuseStep 6740927 = 10111391) B10111391
theorem B4493951 : Blo 1995435 4493951 := bstep (se 1 (by rfl) ⟨3370463, by rfl⟩ : syracuseStep 4493951 = 6740927) B6740927
theorem B2995967 : Blo 1995435 2995967 := bstep (se 1 (by rfl) ⟨2246975, by rfl⟩ : syracuseStep 2995967 = 4493951) B4493951
theorem B1997311 : Blo 1995435 1997311 := bstep (se 1 (by rfl) ⟨1497983, by rfl⟩ : syracuseStep 1997311 = 2995967) B2995967
theorem B2995973 : Blo 1995435 2995973 := bbase (se 4 (by rfl) ⟨280872, by rfl⟩ : syracuseStep 2995973 = 561745) (by norm_num)
theorem B1997315 : Blo 1995435 1997315 := bstep (se 1 (by rfl) ⟨1497986, by rfl⟩ : syracuseStep 1997315 = 2995973) B2995973
theorem B3370477 : Blo 1995435 3370477 := bbase (se 3 (by rfl) ⟨631964, by rfl⟩ : syracuseStep 3370477 = 1263929) (by norm_num)
theorem B4493969 : Blo 1995435 4493969 := bstep (se 2 (by rfl) ⟨1685238, by rfl⟩ : syracuseStep 4493969 = 3370477) B3370477
theorem B2995979 : Blo 1995435 2995979 := bstep (se 1 (by rfl) ⟨2246984, by rfl⟩ : syracuseStep 2995979 = 4493969) B4493969
theorem B1997319 : Blo 1995435 1997319 := bstep (se 1 (by rfl) ⟨1497989, by rfl⟩ : syracuseStep 1997319 = 2995979) B2995979
theorem B2246989 : Blo 1995435 2246989 := bbase (se 3 (by rfl) ⟨421310, by rfl⟩ : syracuseStep 2246989 = 842621) (by norm_num)
theorem B2995985 : Blo 1995435 2995985 := bstep (se 2 (by rfl) ⟨1123494, by rfl⟩ : syracuseStep 2995985 = 2246989) B2246989
theorem B1997323 : Blo 1995435 1997323 := bstep (se 1 (by rfl) ⟨1497992, by rfl⟩ : syracuseStep 1997323 = 2995985) B2995985
theorem B6740981 : Blo 1995435 6740981 := bbase (se 5 (by rfl) ⟨315983, by rfl⟩ : syracuseStep 6740981 = 631967) (by norm_num)
theorem B4493987 : Blo 1995435 4493987 := bstep (se 1 (by rfl) ⟨3370490, by rfl⟩ : syracuseStep 4493987 = 6740981) B6740981
theorem B2995991 : Blo 1995435 2995991 := bstep (se 1 (by rfl) ⟨2246993, by rfl⟩ : syracuseStep 2995991 = 4493987) B4493987
theorem B1997327 : Blo 1995435 1997327 := bstep (se 1 (by rfl) ⟨1497995, by rfl⟩ : syracuseStep 1997327 = 2995991) B2995991
theorem B2995997 : Blo 1995435 2995997 := bbase (se 3 (by rfl) ⟨561749, by rfl⟩ : syracuseStep 2995997 = 1123499) (by norm_num)
theorem B1997331 : Blo 1995435 1997331 := bstep (se 1 (by rfl) ⟨1497998, by rfl⟩ : syracuseStep 1997331 = 2995997) B2995997
theorem B4494005 : Blo 1995435 4494005 := bbase (se 5 (by rfl) ⟨210656, by rfl⟩ : syracuseStep 4494005 = 421313) (by norm_num)
theorem B2996003 : Blo 1995435 2996003 := bstep (se 1 (by rfl) ⟨2247002, by rfl⟩ : syracuseStep 2996003 = 4494005) B4494005
theorem B1997335 : Blo 1995435 1997335 := bstep (se 1 (by rfl) ⟨1498001, by rfl⟩ : syracuseStep 1997335 = 2996003) B2996003
theorem B11375477 : Blo 1995435 11375477 := bbase (se 5 (by rfl) ⟨533225, by rfl⟩ : syracuseStep 11375477 = 1066451) (by norm_num)
theorem B7583651 : Blo 1995435 7583651 := bstep (se 1 (by rfl) ⟨5687738, by rfl⟩ : syracuseStep 7583651 = 11375477) B11375477
theorem B5055767 : Blo 1995435 5055767 := bstep (se 1 (by rfl) ⟨3791825, by rfl⟩ : syracuseStep 5055767 = 7583651) B7583651
theorem B3370511 : Blo 1995435 3370511 := bstep (se 1 (by rfl) ⟨2527883, by rfl⟩ : syracuseStep 3370511 = 5055767) B5055767
theorem B2247007 : Blo 1995435 2247007 := bstep (se 1 (by rfl) ⟨1685255, by rfl⟩ : syracuseStep 2247007 = 3370511) B3370511
theorem B2996009 : Blo 1995435 2996009 := bstep (se 2 (by rfl) ⟨1123503, by rfl⟩ : syracuseStep 2996009 = 2247007) B2247007
theorem B1997339 : Blo 1995435 1997339 := bstep (se 1 (by rfl) ⟨1498004, by rfl⟩ : syracuseStep 1997339 = 2996009) B2996009
theorem B5687749 : Blo 1995435 5687749 := bbase (se 4 (by rfl) ⟨533226, by rfl⟩ : syracuseStep 5687749 = 1066453) (by norm_num)
theorem B7583665 : Blo 1995435 7583665 := bstep (se 2 (by rfl) ⟨2843874, by rfl⟩ : syracuseStep 7583665 = 5687749) B5687749
theorem B10111553 : Blo 1995435 10111553 := bstep (se 2 (by rfl) ⟨3791832, by rfl⟩ : syracuseStep 10111553 = 7583665) B7583665
theorem B6741035 : Blo 1995435 6741035 := bstep (se 1 (by rfl) ⟨5055776, by rfl⟩ : syracuseStep 6741035 = 10111553) B10111553
theorem B4494023 : Blo 1995435 4494023 := bstep (se 1 (by rfl) ⟨3370517, by rfl⟩ : syracuseStep 4494023 = 6741035) B6741035
theorem B2996015 : Blo 1995435 2996015 := bstep (se 1 (by rfl) ⟨2247011, by rfl⟩ : syracuseStep 2996015 = 4494023) B4494023
theorem B1997343 : Blo 1995435 1997343 := bstep (se 1 (by rfl) ⟨1498007, by rfl⟩ : syracuseStep 1997343 = 2996015) B2996015
theorem B2996021 : Blo 1995435 2996021 := bbase (se 5 (by rfl) ⟨140438, by rfl⟩ : syracuseStep 2996021 = 280877) (by norm_num)
theorem B1997347 : Blo 1995435 1997347 := bstep (se 1 (by rfl) ⟨1498010, by rfl⟩ : syracuseStep 1997347 = 2996021) B2996021
theorem B5055797 : Blo 1995435 5055797 := bbase (se 5 (by rfl) ⟨236990, by rfl⟩ : syracuseStep 5055797 = 473981) (by norm_num)
theorem B3370531 : Blo 1995435 3370531 := bstep (se 1 (by rfl) ⟨2527898, by rfl⟩ : syracuseStep 3370531 = 5055797) B5055797
theorem B4494041 : Blo 1995435 4494041 := bstep (se 2 (by rfl) ⟨1685265, by rfl⟩ : syracuseStep 4494041 = 3370531) B3370531
theorem B2996027 : Blo 1995435 2996027 := bstep (se 1 (by rfl) ⟨2247020, by rfl⟩ : syracuseStep 2996027 = 4494041) B4494041
theorem B1997351 : Blo 1995435 1997351 := bstep (se 1 (by rfl) ⟨1498013, by rfl⟩ : syracuseStep 1997351 = 2996027) B2996027
theorem B2247025 : Blo 1995435 2247025 := bbase (se 2 (by rfl) ⟨842634, by rfl⟩ : syracuseStep 2247025 = 1685269) (by norm_num)
theorem B2996033 : Blo 1995435 2996033 := bstep (se 2 (by rfl) ⟨1123512, by rfl⟩ : syracuseStep 2996033 = 2247025) B2247025
theorem B1997355 : Blo 1995435 1997355 := bstep (se 1 (by rfl) ⟨1498016, by rfl⟩ : syracuseStep 1997355 = 2996033) B2996033
theorem B3599309 : Blo 1995435 3599309 := bbase (se 3 (by rfl) ⟨674870, by rfl⟩ : syracuseStep 3599309 = 1349741) (by norm_num)
theorem B2399539 : Blo 1995435 2399539 := bstep (se 1 (by rfl) ⟨1799654, by rfl⟩ : syracuseStep 2399539 = 3599309) B3599309
theorem B3199385 : Blo 1995435 3199385 := bstep (se 2 (by rfl) ⟨1199769, by rfl⟩ : syracuseStep 3199385 = 2399539) B2399539
theorem B8531693 : Blo 1995435 8531693 := bstep (se 3 (by rfl) ⟨1599692, by rfl⟩ : syracuseStep 8531693 = 3199385) B3199385
theorem B5687795 : Blo 1995435 5687795 := bstep (se 1 (by rfl) ⟨4265846, by rfl⟩ : syracuseStep 5687795 = 8531693) B8531693
theorem B3791863 : Blo 1995435 3791863 := bstep (se 1 (by rfl) ⟨2843897, by rfl⟩ : syracuseStep 3791863 = 5687795) B5687795
theorem B5055817 : Blo 1995435 5055817 := bstep (se 2 (by rfl) ⟨1895931, by rfl⟩ : syracuseStep 5055817 = 3791863) B3791863
theorem B6741089 : Blo 1995435 6741089 := bstep (se 2 (by rfl) ⟨2527908, by rfl⟩ : syracuseStep 6741089 = 5055817) B5055817
theorem B4494059 : Blo 1995435 4494059 := bstep (se 1 (by rfl) ⟨3370544, by rfl⟩ : syracuseStep 4494059 = 6741089) B6741089
theorem B2996039 : Blo 1995435 2996039 := bstep (se 1 (by rfl) ⟨2247029, by rfl⟩ : syracuseStep 2996039 = 4494059) B4494059
theorem B1997359 : Blo 1995435 1997359 := bstep (se 1 (by rfl) ⟨1498019, by rfl⟩ : syracuseStep 1997359 = 2996039) B2996039
theorem B2996045 : Blo 1995435 2996045 := bbase (se 3 (by rfl) ⟨561758, by rfl⟩ : syracuseStep 2996045 = 1123517) (by norm_num)
theorem B1997363 : Blo 1995435 1997363 := bstep (se 1 (by rfl) ⟨1498022, by rfl⟩ : syracuseStep 1997363 = 2996045) B2996045
theorem B4494077 : Blo 1995435 4494077 := bbase (se 3 (by rfl) ⟨842639, by rfl⟩ : syracuseStep 4494077 = 1685279) (by norm_num)
theorem B2996051 : Blo 1995435 2996051 := bstep (se 1 (by rfl) ⟨2247038, by rfl⟩ : syracuseStep 2996051 = 4494077) B4494077
theorem B1997367 : Blo 1995435 1997367 := bstep (se 1 (by rfl) ⟨1498025, by rfl⟩ : syracuseStep 1997367 = 2996051) B2996051
theorem B3370565 : Blo 1995435 3370565 := bbase (se 4 (by rfl) ⟨315990, by rfl⟩ : syracuseStep 3370565 = 631981) (by norm_num)
theorem B2247043 : Blo 1995435 2247043 := bstep (se 1 (by rfl) ⟨1685282, by rfl⟩ : syracuseStep 2247043 = 3370565) B3370565
theorem B2996057 : Blo 1995435 2996057 := bstep (se 2 (by rfl) ⟨1123521, by rfl⟩ : syracuseStep 2996057 = 2247043) B2247043
theorem B1997371 : Blo 1995435 1997371 := bstep (se 1 (by rfl) ⟨1498028, by rfl⟩ : syracuseStep 1997371 = 2996057) B2996057
theorem B15167573 : Blo 1995435 15167573 := bbase (se 8 (by rfl) ⟨88872, by rfl⟩ : syracuseStep 15167573 = 177745) (by norm_num)
theorem B10111715 : Blo 1995435 10111715 := bstep (se 1 (by rfl) ⟨7583786, by rfl⟩ : syracuseStep 10111715 = 15167573) B15167573
theorem B6741143 : Blo 1995435 6741143 := bstep (se 1 (by rfl) ⟨5055857, by rfl⟩ : syracuseStep 6741143 = 10111715) B10111715
theorem B4494095 : Blo 1995435 4494095 := bstep (se 1 (by rfl) ⟨3370571, by rfl⟩ : syracuseStep 4494095 = 6741143) B6741143
theorem B2996063 : Blo 1995435 2996063 := bstep (se 1 (by rfl) ⟨2247047, by rfl⟩ : syracuseStep 2996063 = 4494095) B4494095
theorem B1997375 : Blo 1995435 1997375 := bstep (se 1 (by rfl) ⟨1498031, by rfl⟩ : syracuseStep 1997375 = 2996063) B2996063
theorem B2996069 : Blo 1995435 2996069 := bbase (se 4 (by rfl) ⟨280881, by rfl⟩ : syracuseStep 2996069 = 561763) (by norm_num)
theorem B1997379 : Blo 1995435 1997379 := bstep (se 1 (by rfl) ⟨1498034, by rfl⟩ : syracuseStep 1997379 = 2996069) B2996069
theorem B3791909 : Blo 1995435 3791909 := bbase (se 4 (by rfl) ⟨355491, by rfl⟩ : syracuseStep 3791909 = 710983) (by norm_num)
theorem B2527939 : Blo 1995435 2527939 := bstep (se 1 (by rfl) ⟨1895954, by rfl⟩ : syracuseStep 2527939 = 3791909) B3791909
theorem B3370585 : Blo 1995435 3370585 := bstep (se 2 (by rfl) ⟨1263969, by rfl⟩ : syracuseStep 3370585 = 2527939) B2527939
theorem B4494113 : Blo 1995435 4494113 := bstep (se 2 (by rfl) ⟨1685292, by rfl⟩ : syracuseStep 4494113 = 3370585) B3370585
theorem B2996075 : Blo 1995435 2996075 := bstep (se 1 (by rfl) ⟨2247056, by rfl⟩ : syracuseStep 2996075 = 4494113) B4494113
theorem B1997383 : Blo 1995435 1997383 := bstep (se 1 (by rfl) ⟨1498037, by rfl⟩ : syracuseStep 1997383 = 2996075) B2996075
theorem B2247061 : Blo 1995435 2247061 := bbase (se 6 (by rfl) ⟨52665, by rfl⟩ : syracuseStep 2247061 = 105331) (by norm_num)
theorem B2996081 : Blo 1995435 2996081 := bstep (se 2 (by rfl) ⟨1123530, by rfl⟩ : syracuseStep 2996081 = 2247061) B2247061
theorem B1997387 : Blo 1995435 1997387 := bstep (se 1 (by rfl) ⟨1498040, by rfl⟩ : syracuseStep 1997387 = 2996081) B2996081
theorem B2527949 : Blo 1995435 2527949 := bbase (se 3 (by rfl) ⟨473990, by rfl⟩ : syracuseStep 2527949 = 947981) (by norm_num)
theorem B6741197 : Blo 1995435 6741197 := bstep (se 3 (by rfl) ⟨1263974, by rfl⟩ : syracuseStep 6741197 = 2527949) B2527949
theorem B4494131 : Blo 1995435 4494131 := bstep (se 1 (by rfl) ⟨3370598, by rfl⟩ : syracuseStep 4494131 = 6741197) B6741197
theorem B2996087 : Blo 1995435 2996087 := bstep (se 1 (by rfl) ⟨2247065, by rfl⟩ : syracuseStep 2996087 = 4494131) B4494131
theorem B1997391 : Blo 1995435 1997391 := bstep (se 1 (by rfl) ⟨1498043, by rfl⟩ : syracuseStep 1997391 = 2996087) B2996087
theorem B2996093 : Blo 1995435 2996093 := bbase (se 3 (by rfl) ⟨561767, by rfl⟩ : syracuseStep 2996093 = 1123535) (by norm_num)
theorem B1997395 : Blo 1995435 1997395 := bstep (se 1 (by rfl) ⟨1498046, by rfl⟩ : syracuseStep 1997395 = 2996093) B2996093
theorem B4494149 : Blo 1995435 4494149 := bbase (se 4 (by rfl) ⟨421326, by rfl⟩ : syracuseStep 4494149 = 842653) (by norm_num)
theorem B2996099 : Blo 1995435 2996099 := bstep (se 1 (by rfl) ⟨2247074, by rfl⟩ : syracuseStep 2996099 = 4494149) B4494149
theorem B1997399 : Blo 1995435 1997399 := bstep (se 1 (by rfl) ⟨1498049, by rfl⟩ : syracuseStep 1997399 = 2996099) B2996099
theorem B4265941 : Blo 1995435 4265941 := bbase (se 7 (by rfl) ⟨49991, by rfl⟩ : syracuseStep 4265941 = 99983) (by norm_num)
theorem B5687921 : Blo 1995435 5687921 := bstep (se 2 (by rfl) ⟨2132970, by rfl⟩ : syracuseStep 5687921 = 4265941) B4265941
theorem B3791947 : Blo 1995435 3791947 := bstep (se 1 (by rfl) ⟨2843960, by rfl⟩ : syracuseStep 3791947 = 5687921) B5687921
theorem B5055929 : Blo 1995435 5055929 := bstep (se 2 (by rfl) ⟨1895973, by rfl⟩ : syracuseStep 5055929 = 3791947) B3791947
theorem B3370619 : Blo 1995435 3370619 := bstep (se 1 (by rfl) ⟨2527964, by rfl⟩ : syracuseStep 3370619 = 5055929) B5055929
theorem B2247079 : Blo 1995435 2247079 := bstep (se 1 (by rfl) ⟨1685309, by rfl⟩ : syracuseStep 2247079 = 3370619) B3370619
theorem B2996105 : Blo 1995435 2996105 := bstep (se 2 (by rfl) ⟨1123539, by rfl⟩ : syracuseStep 2996105 = 2247079) B2247079
theorem B1997403 : Blo 1995435 1997403 := bstep (se 1 (by rfl) ⟨1498052, by rfl⟩ : syracuseStep 1997403 = 2996105) B2996105
theorem B10111877 : Blo 1995435 10111877 := bbase (se 4 (by rfl) ⟨947988, by rfl⟩ : syracuseStep 10111877 = 1895977) (by norm_num)
theorem B6741251 : Blo 1995435 6741251 := bstep (se 1 (by rfl) ⟨5055938, by rfl⟩ : syracuseStep 6741251 = 10111877) B10111877
theorem B4494167 : Blo 1995435 4494167 := bstep (se 1 (by rfl) ⟨3370625, by rfl⟩ : syracuseStep 4494167 = 6741251) B6741251
theorem B2996111 : Blo 1995435 2996111 := bstep (se 1 (by rfl) ⟨2247083, by rfl⟩ : syracuseStep 2996111 = 4494167) B4494167
theorem B1997407 : Blo 1995435 1997407 := bstep (se 1 (by rfl) ⟨1498055, by rfl⟩ : syracuseStep 1997407 = 2996111) B2996111
theorem B2996117 : Blo 1995435 2996117 := bbase (se 6 (by rfl) ⟨70221, by rfl⟩ : syracuseStep 2996117 = 140443) (by norm_num)
theorem B1997411 : Blo 1995435 1997411 := bstep (se 1 (by rfl) ⟨1498058, by rfl⟩ : syracuseStep 1997411 = 2996117) B2996117
theorem B4799213 : Blo 1995435 4799213 := bbase (se 3 (by rfl) ⟨899852, by rfl⟩ : syracuseStep 4799213 = 1799705) (by norm_num)
theorem B3199475 : Blo 1995435 3199475 := bstep (se 1 (by rfl) ⟨2399606, by rfl⟩ : syracuseStep 3199475 = 4799213) B4799213
theorem B2132983 : Blo 1995435 2132983 := bstep (se 1 (by rfl) ⟨1599737, by rfl⟩ : syracuseStep 2132983 = 3199475) B3199475
theorem B11375909 : Blo 1995435 11375909 := bstep (se 4 (by rfl) ⟨1066491, by rfl⟩ : syracuseStep 11375909 = 2132983) B2132983
theorem B7583939 : Blo 1995435 7583939 := bstep (se 1 (by rfl) ⟨5687954, by rfl⟩ : syracuseStep 7583939 = 11375909) B11375909
theorem B5055959 : Blo 1995435 5055959 := bstep (se 1 (by rfl) ⟨3791969, by rfl⟩ : syracuseStep 5055959 = 7583939) B7583939
theorem B3370639 : Blo 1995435 3370639 := bstep (se 1 (by rfl) ⟨2527979, by rfl⟩ : syracuseStep 3370639 = 5055959) B5055959
theorem B4494185 : Blo 1995435 4494185 := bstep (se 2 (by rfl) ⟨1685319, by rfl⟩ : syracuseStep 4494185 = 3370639) B3370639
theorem B2996123 : Blo 1995435 2996123 := bstep (se 1 (by rfl) ⟨2247092, by rfl⟩ : syracuseStep 2996123 = 4494185) B4494185
theorem B1997415 : Blo 1995435 1997415 := bstep (se 1 (by rfl) ⟨1498061, by rfl⟩ : syracuseStep 1997415 = 2996123) B2996123
theorem B2247097 : Blo 1995435 2247097 := bbase (se 2 (by rfl) ⟨842661, by rfl⟩ : syracuseStep 2247097 = 1685323) (by norm_num)
theorem B2996129 : Blo 1995435 2996129 := bstep (se 2 (by rfl) ⟨1123548, by rfl⟩ : syracuseStep 2996129 = 2247097) B2247097
theorem B1997419 : Blo 1995435 1997419 := bstep (se 1 (by rfl) ⟨1498064, by rfl⟩ : syracuseStep 1997419 = 2996129) B2996129
theorem B2162093 : Blo 1995435 2162093 := bbase (se 3 (by rfl) ⟨405392, by rfl⟩ : syracuseStep 2162093 = 810785) (by norm_num)
theorem B23062325 : Blo 1995435 23062325 := bstep (se 5 (by rfl) ⟨1081046, by rfl⟩ : syracuseStep 23062325 = 2162093) B2162093
theorem B245998133 : Blo 1995435 245998133 := bstep (se 5 (by rfl) ⟨11531162, by rfl⟩ : syracuseStep 245998133 = 23062325) B23062325
theorem B163998755 : Blo 1995435 163998755 := bstep (se 1 (by rfl) ⟨122999066, by rfl⟩ : syracuseStep 163998755 = 245998133) B245998133
theorem B109332503 : Blo 1995435 109332503 := bstep (se 1 (by rfl) ⟨81999377, by rfl⟩ : syracuseStep 109332503 = 163998755) B163998755
theorem B72888335 : Blo 1995435 72888335 := bstep (se 1 (by rfl) ⟨54666251, by rfl⟩ : syracuseStep 72888335 = 109332503) B109332503
theorem B48592223 : Blo 1995435 48592223 := bstep (se 1 (by rfl) ⟨36444167, by rfl⟩ : syracuseStep 48592223 = 72888335) B72888335
theorem B32394815 : Blo 1995435 32394815 := bstep (se 1 (by rfl) ⟨24296111, by rfl⟩ : syracuseStep 32394815 = 48592223) B48592223
theorem B21596543 : Blo 1995435 21596543 := bstep (se 1 (by rfl) ⟨16197407, by rfl⟩ : syracuseStep 21596543 = 32394815) B32394815
theorem B14397695 : Blo 1995435 14397695 := bstep (se 1 (by rfl) ⟨10798271, by rfl⟩ : syracuseStep 14397695 = 21596543) B21596543
theorem B9598463 : Blo 1995435 9598463 := bstep (se 1 (by rfl) ⟨7198847, by rfl⟩ : syracuseStep 9598463 = 14397695) B14397695
theorem B6398975 : Blo 1995435 6398975 := bstep (se 1 (by rfl) ⟨4799231, by rfl⟩ : syracuseStep 6398975 = 9598463) B9598463
theorem B4265983 : Blo 1995435 4265983 := bstep (se 1 (by rfl) ⟨3199487, by rfl⟩ : syracuseStep 4265983 = 6398975) B6398975
theorem B5687977 : Blo 1995435 5687977 := bstep (se 2 (by rfl) ⟨2132991, by rfl⟩ : syracuseStep 5687977 = 4265983) B4265983
theorem B7583969 : Blo 1995435 7583969 := bstep (se 2 (by rfl) ⟨2843988, by rfl⟩ : syracuseStep 7583969 = 5687977) B5687977
theorem B5055979 : Blo 1995435 5055979 := bstep (se 1 (by rfl) ⟨3791984, by rfl⟩ : syracuseStep 5055979 = 7583969) B7583969
theorem B6741305 : Blo 1995435 6741305 := bstep (se 2 (by rfl) ⟨2527989, by rfl⟩ : syracuseStep 6741305 = 5055979) B5055979
theorem B4494203 : Blo 1995435 4494203 := bstep (se 1 (by rfl) ⟨3370652, by rfl⟩ : syracuseStep 4494203 = 6741305) B6741305
theorem B2996135 : Blo 1995435 2996135 := bstep (se 1 (by rfl) ⟨2247101, by rfl⟩ : syracuseStep 2996135 = 4494203) B4494203
theorem B1997423 : Blo 1995435 1997423 := bstep (se 1 (by rfl) ⟨1498067, by rfl⟩ : syracuseStep 1997423 = 2996135) B2996135
theorem B2996141 : Blo 1995435 2996141 := bbase (se 3 (by rfl) ⟨561776, by rfl⟩ : syracuseStep 2996141 = 1123553) (by norm_num)
theorem B1997427 : Blo 1995435 1997427 := bstep (se 1 (by rfl) ⟨1498070, by rfl⟩ : syracuseStep 1997427 = 2996141) B2996141
theorem B4494221 : Blo 1995435 4494221 := bbase (se 3 (by rfl) ⟨842666, by rfl⟩ : syracuseStep 4494221 = 1685333) (by norm_num)
theorem B2996147 : Blo 1995435 2996147 := bstep (se 1 (by rfl) ⟨2247110, by rfl⟩ : syracuseStep 2996147 = 4494221) B4494221
theorem B1997431 : Blo 1995435 1997431 := bstep (se 1 (by rfl) ⟨1498073, by rfl⟩ : syracuseStep 1997431 = 2996147) B2996147
theorem B2528005 : Blo 1995435 2528005 := bbase (se 4 (by rfl) ⟨237000, by rfl⟩ : syracuseStep 2528005 = 474001) (by norm_num)
theorem B3370673 : Blo 1995435 3370673 := bstep (se 2 (by rfl) ⟨1264002, by rfl⟩ : syracuseStep 3370673 = 2528005) B2528005
theorem B2247115 : Blo 1995435 2247115 := bstep (se 1 (by rfl) ⟨1685336, by rfl⟩ : syracuseStep 2247115 = 3370673) B3370673
theorem B2996153 : Blo 1995435 2996153 := bstep (se 2 (by rfl) ⟨1123557, by rfl⟩ : syracuseStep 2996153 = 2247115) B2247115
theorem B1997435 : Blo 1995435 1997435 := bstep (se 1 (by rfl) ⟨1498076, by rfl⟩ : syracuseStep 1997435 = 2996153) B2996153
theorem C0 (j : ℕ) (h1 : 498858 ≤ j) (h2 : j ≤ 499358) : Blo 1995435 (4 * j + 3) := by
  interval_cases j
  · exact B1995435
  · exact B1995439
  · exact B1995443
  · exact B1995447
  · exact B1995451
  · exact B1995455
  · exact B1995459
  · exact B1995463
  · exact B1995467
  · exact B1995471
  · exact B1995475
  · exact B1995479
  · exact B1995483
  · exact B1995487
  · exact B1995491
  · exact B1995495
  · exact B1995499
  · exact B1995503
  · exact B1995507
  · exact B1995511
  · exact B1995515
  · exact B1995519
  · exact B1995523
  · exact B1995527
  · exact B1995531
  · exact B1995535
  · exact B1995539
  · exact B1995543
  · exact B1995547
  · exact B1995551
  · exact B1995555
  · exact B1995559
  · exact B1995563
  · exact B1995567
  · exact B1995571
  · exact B1995575
  · exact B1995579
  · exact B1995583
  · exact B1995587
  · exact B1995591
  · exact B1995595
  · exact B1995599
  · exact B1995603
  · exact B1995607
  · exact B1995611
  · exact B1995615
  · exact B1995619
  · exact B1995623
  · exact B1995627
  · exact B1995631
  · exact B1995635
  · exact B1995639
  · exact B1995643
  · exact B1995647
  · exact B1995651
  · exact B1995655
  · exact B1995659
  · exact B1995663
  · exact B1995667
  · exact B1995671
  · exact B1995675
  · exact B1995679
  · exact B1995683
  · exact B1995687
  · exact B1995691
  · exact B1995695
  · exact B1995699
  · exact B1995703
  · exact B1995707
  · exact B1995711
  · exact B1995715
  · exact B1995719
  · exact B1995723
  · exact B1995727
  · exact B1995731
  · exact B1995735
  · exact B1995739
  · exact B1995743
  · exact B1995747
  · exact B1995751
  · exact B1995755
  · exact B1995759
  · exact B1995763
  · exact B1995767
  · exact B1995771
  · exact B1995775
  · exact B1995779
  · exact B1995783
  · exact B1995787
  · exact B1995791
  · exact B1995795
  · exact B1995799
  · exact B1995803
  · exact B1995807
  · exact B1995811
  · exact B1995815
  · exact B1995819
  · exact B1995823
  · exact B1995827
  · exact B1995831
  · exact B1995835
  · exact B1995839
  · exact B1995843
  · exact B1995847
  · exact B1995851
  · exact B1995855
  · exact B1995859
  · exact B1995863
  · exact B1995867
  · exact B1995871
  · exact B1995875
  · exact B1995879
  · exact B1995883
  · exact B1995887
  · exact B1995891
  · exact B1995895
  · exact B1995899
  · exact B1995903
  · exact B1995907
  · exact B1995911
  · exact B1995915
  · exact B1995919
  · exact B1995923
  · exact B1995927
  · exact B1995931
  · exact B1995935
  · exact B1995939
  · exact B1995943
  · exact B1995947
  · exact B1995951
  · exact B1995955
  · exact B1995959
  · exact B1995963
  · exact B1995967
  · exact B1995971
  · exact B1995975
  · exact B1995979
  · exact B1995983
  · exact B1995987
  · exact B1995991
  · exact B1995995
  · exact B1995999
  · exact B1996003
  · exact B1996007
  · exact B1996011
  · exact B1996015
  · exact B1996019
  · exact B1996023
  · exact B1996027
  · exact B1996031
  · exact B1996035
  · exact B1996039
  · exact B1996043
  · exact B1996047
  · exact B1996051
  · exact B1996055
  · exact B1996059
  · exact B1996063
  · exact B1996067
  · exact B1996071
  · exact B1996075
  · exact B1996079
  · exact B1996083
  · exact B1996087
  · exact B1996091
  · exact B1996095
  · exact B1996099
  · exact B1996103
  · exact B1996107
  · exact B1996111
  · exact B1996115
  · exact B1996119
  · exact B1996123
  · exact B1996127
  · exact B1996131
  · exact B1996135
  · exact B1996139
  · exact B1996143
  · exact B1996147
  · exact B1996151
  · exact B1996155
  · exact B1996159
  · exact B1996163
  · exact B1996167
  · exact B1996171
  · exact B1996175
  · exact B1996179
  · exact B1996183
  · exact B1996187
  · exact B1996191
  · exact B1996195
  · exact B1996199
  · exact B1996203
  · exact B1996207
  · exact B1996211
  · exact B1996215
  · exact B1996219
  · exact B1996223
  · exact B1996227
  · exact B1996231
  · exact B1996235
  · exact B1996239
  · exact B1996243
  · exact B1996247
  · exact B1996251
  · exact B1996255
  · exact B1996259
  · exact B1996263
  · exact B1996267
  · exact B1996271
  · exact B1996275
  · exact B1996279
  · exact B1996283
  · exact B1996287
  · exact B1996291
  · exact B1996295
  · exact B1996299
  · exact B1996303
  · exact B1996307
  · exact B1996311
  · exact B1996315
  · exact B1996319
  · exact B1996323
  · exact B1996327
  · exact B1996331
  · exact B1996335
  · exact B1996339
  · exact B1996343
  · exact B1996347
  · exact B1996351
  · exact B1996355
  · exact B1996359
  · exact B1996363
  · exact B1996367
  · exact B1996371
  · exact B1996375
  · exact B1996379
  · exact B1996383
  · exact B1996387
  · exact B1996391
  · exact B1996395
  · exact B1996399
  · exact B1996403
  · exact B1996407
  · exact B1996411
  · exact B1996415
  · exact B1996419
  · exact B1996423
  · exact B1996427
  · exact B1996431
  · exact B1996435
  · exact B1996439
  · exact B1996443
  · exact B1996447
  · exact B1996451
  · exact B1996455
  · exact B1996459
  · exact B1996463
  · exact B1996467
  · exact B1996471
  · exact B1996475
  · exact B1996479
  · exact B1996483
  · exact B1996487
  · exact B1996491
  · exact B1996495
  · exact B1996499
  · exact B1996503
  · exact B1996507
  · exact B1996511
  · exact B1996515
  · exact B1996519
  · exact B1996523
  · exact B1996527
  · exact B1996531
  · exact B1996535
  · exact B1996539
  · exact B1996543
  · exact B1996547
  · exact B1996551
  · exact B1996555
  · exact B1996559
  · exact B1996563
  · exact B1996567
  · exact B1996571
  · exact B1996575
  · exact B1996579
  · exact B1996583
  · exact B1996587
  · exact B1996591
  · exact B1996595
  · exact B1996599
  · exact B1996603
  · exact B1996607
  · exact B1996611
  · exact B1996615
  · exact B1996619
  · exact B1996623
  · exact B1996627
  · exact B1996631
  · exact B1996635
  · exact B1996639
  · exact B1996643
  · exact B1996647
  · exact B1996651
  · exact B1996655
  · exact B1996659
  · exact B1996663
  · exact B1996667
  · exact B1996671
  · exact B1996675
  · exact B1996679
  · exact B1996683
  · exact B1996687
  · exact B1996691
  · exact B1996695
  · exact B1996699
  · exact B1996703
  · exact B1996707
  · exact B1996711
  · exact B1996715
  · exact B1996719
  · exact B1996723
  · exact B1996727
  · exact B1996731
  · exact B1996735
  · exact B1996739
  · exact B1996743
  · exact B1996747
  · exact B1996751
  · exact B1996755
  · exact B1996759
  · exact B1996763
  · exact B1996767
  · exact B1996771
  · exact B1996775
  · exact B1996779
  · exact B1996783
  · exact B1996787
  · exact B1996791
  · exact B1996795
  · exact B1996799
  · exact B1996803
  · exact B1996807
  · exact B1996811
  · exact B1996815
  · exact B1996819
  · exact B1996823
  · exact B1996827
  · exact B1996831
  · exact B1996835
  · exact B1996839
  · exact B1996843
  · exact B1996847
  · exact B1996851
  · exact B1996855
  · exact B1996859
  · exact B1996863
  · exact B1996867
  · exact B1996871
  · exact B1996875
  · exact B1996879
  · exact B1996883
  · exact B1996887
  · exact B1996891
  · exact B1996895
  · exact B1996899
  · exact B1996903
  · exact B1996907
  · exact B1996911
  · exact B1996915
  · exact B1996919
  · exact B1996923
  · exact B1996927
  · exact B1996931
  · exact B1996935
  · exact B1996939
  · exact B1996943
  · exact B1996947
  · exact B1996951
  · exact B1996955
  · exact B1996959
  · exact B1996963
  · exact B1996967
  · exact B1996971
  · exact B1996975
  · exact B1996979
  · exact B1996983
  · exact B1996987
  · exact B1996991
  · exact B1996995
  · exact B1996999
  · exact B1997003
  · exact B1997007
  · exact B1997011
  · exact B1997015
  · exact B1997019
  · exact B1997023
  · exact B1997027
  · exact B1997031
  · exact B1997035
  · exact B1997039
  · exact B1997043
  · exact B1997047
  · exact B1997051
  · exact B1997055
  · exact B1997059
  · exact B1997063
  · exact B1997067
  · exact B1997071
  · exact B1997075
  · exact B1997079
  · exact B1997083
  · exact B1997087
  · exact B1997091
  · exact B1997095
  · exact B1997099
  · exact B1997103
  · exact B1997107
  · exact B1997111
  · exact B1997115
  · exact B1997119
  · exact B1997123
  · exact B1997127
  · exact B1997131
  · exact B1997135
  · exact B1997139
  · exact B1997143
  · exact B1997147
  · exact B1997151
  · exact B1997155
  · exact B1997159
  · exact B1997163
  · exact B1997167
  · exact B1997171
  · exact B1997175
  · exact B1997179
  · exact B1997183
  · exact B1997187
  · exact B1997191
  · exact B1997195
  · exact B1997199
  · exact B1997203
  · exact B1997207
  · exact B1997211
  · exact B1997215
  · exact B1997219
  · exact B1997223
  · exact B1997227
  · exact B1997231
  · exact B1997235
  · exact B1997239
  · exact B1997243
  · exact B1997247
  · exact B1997251
  · exact B1997255
  · exact B1997259
  · exact B1997263
  · exact B1997267
  · exact B1997271
  · exact B1997275
  · exact B1997279
  · exact B1997283
  · exact B1997287
  · exact B1997291
  · exact B1997295
  · exact B1997299
  · exact B1997303
  · exact B1997307
  · exact B1997311
  · exact B1997315
  · exact B1997319
  · exact B1997323
  · exact B1997327
  · exact B1997331
  · exact B1997335
  · exact B1997339
  · exact B1997343
  · exact B1997347
  · exact B1997351
  · exact B1997355
  · exact B1997359
  · exact B1997363
  · exact B1997367
  · exact B1997371
  · exact B1997375
  · exact B1997379
  · exact B1997383
  · exact B1997387
  · exact B1997391
  · exact B1997395
  · exact B1997399
  · exact B1997403
  · exact B1997407
  · exact B1997411
  · exact B1997415
  · exact B1997419
  · exact B1997423
  · exact B1997427
  · exact B1997431
  · exact B1997435
theorem solution (m : ℕ) (hlo : 1995435 ≤ m) (hhi : m ≤ 1997435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 498858 ≤ j := by omega
    have hj2 : j ≤ 499358 := by omega
    have hb : Blo 1995435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
