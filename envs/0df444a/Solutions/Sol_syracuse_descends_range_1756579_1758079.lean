-- Prove2me | solution 1 for syracuse_descends_range_1756579_1758079
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:38:00.705846+00:00
-- url     : https://prove2.me/submissions/4a26286e-6c32-4513-97b6-529bd51a41ec

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


theorem B13713461 : Blo 1756579 13713461 := bbase (se 5 (by rfl) ⟨642818, by rfl⟩ : syracuseStep 13713461 = 1285637) (by norm_num)
theorem B4448317 : Blo 1756579 4448317 := bbase (se 3 (by rfl) ⟨834059, by rfl⟩ : syracuseStep 4448317 = 1668119) (by norm_num)
theorem B2965565 : Blo 1756579 2965565 := bbase (se 3 (by rfl) ⟨556043, by rfl⟩ : syracuseStep 2965565 = 1112087) (by norm_num)
theorem B3752021 : Blo 1756579 3752021 := bbase (se 8 (by rfl) ⟨21984, by rfl⟩ : syracuseStep 3752021 = 43969) (by norm_num)
theorem B4448429 : Blo 1756579 4448429 := bbase (se 3 (by rfl) ⟨834080, by rfl⟩ : syracuseStep 4448429 = 1668161) (by norm_num)
theorem B2965693 : Blo 1756579 2965693 := bbase (se 3 (by rfl) ⟨556067, by rfl⟩ : syracuseStep 2965693 = 1112135) (by norm_num)
theorem B1876169 : Blo 1756579 1876169 := bbase (se 2 (by rfl) ⟨703563, by rfl⟩ : syracuseStep 1876169 = 1407127) (by norm_num)
theorem B1876241 : Blo 1756579 1876241 := bbase (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) (by norm_num)
theorem B2965781 : Blo 1756579 2965781 := bbase (se 6 (by rfl) ⟨69510, by rfl⟩ : syracuseStep 2965781 = 139021) (by norm_num)
theorem B4448621 : Blo 1756579 4448621 := bbase (se 3 (by rfl) ⟨834116, by rfl⟩ : syracuseStep 4448621 = 1668233) (by norm_num)
theorem B5931413 : Blo 1756579 5931413 := bbase (se 6 (by rfl) ⟨139017, by rfl⟩ : syracuseStep 5931413 = 278035) (by norm_num)
theorem B2965909 : Blo 1756579 2965909 := bbase (se 6 (by rfl) ⟨69513, by rfl⟩ : syracuseStep 2965909 = 139027) (by norm_num)
theorem B1876429 : Blo 1756579 1876429 := bbase (se 3 (by rfl) ⟨351830, by rfl⟩ : syracuseStep 1876429 = 703661) (by norm_num)
theorem B9503189 : Blo 1756579 9503189 := bbase (se 7 (by rfl) ⟨111365, by rfl⟩ : syracuseStep 9503189 = 222731) (by norm_num)
theorem B2965997 : Blo 1756579 2965997 := bbase (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) (by norm_num)
theorem B2892277 : Blo 1756579 2892277 := bbase (se 5 (by rfl) ⟨135575, by rfl⟩ : syracuseStep 2892277 = 271151) (by norm_num)
theorem B10011221 : Blo 1756579 10011221 := bbase (se 8 (by rfl) ⟨58659, by rfl⟩ : syracuseStep 10011221 = 117319) (by norm_num)
theorem B3334765 : Blo 1756579 3334765 := bbase (se 3 (by rfl) ⟨625268, by rfl⟩ : syracuseStep 3334765 = 1250537) (by norm_num)
theorem B2966125 : Blo 1756579 2966125 := bbase (se 3 (by rfl) ⟨556148, by rfl⟩ : syracuseStep 2966125 = 1112297) (by norm_num)
theorem B1876613 : Blo 1756579 1876613 := bbase (se 4 (by rfl) ⟨175932, by rfl⟩ : syracuseStep 1876613 = 351865) (by norm_num)
theorem B4448965 : Blo 1756579 4448965 := bbase (se 4 (by rfl) ⟨417090, by rfl⟩ : syracuseStep 4448965 = 834181) (by norm_num)
theorem B2966213 : Blo 1756579 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B3334925 : Blo 1756579 3334925 := bbase (se 3 (by rfl) ⟨625298, by rfl⟩ : syracuseStep 3334925 = 1250597) (by norm_num)
theorem B4449077 : Blo 1756579 4449077 := bbase (se 5 (by rfl) ⟨208550, by rfl⟩ : syracuseStep 4449077 = 417101) (by norm_num)
theorem B5931845 : Blo 1756579 5931845 := bbase (se 4 (by rfl) ⟨556110, by rfl⟩ : syracuseStep 5931845 = 1112221) (by norm_num)
theorem B2966341 : Blo 1756579 2966341 := bbase (se 4 (by rfl) ⟨278094, by rfl⟩ : syracuseStep 2966341 = 556189) (by norm_num)
theorem B3335069 : Blo 1756579 3335069 := bbase (se 3 (by rfl) ⟨625325, by rfl⟩ : syracuseStep 3335069 = 1250651) (by norm_num)
theorem B2966429 : Blo 1756579 2966429 := bbase (se 3 (by rfl) ⟨556205, by rfl⟩ : syracuseStep 2966429 = 1112411) (by norm_num)
theorem B3752885 : Blo 1756579 3752885 := bbase (se 5 (by rfl) ⟨175916, by rfl⟩ : syracuseStep 3752885 = 351833) (by norm_num)
theorem B8897525 : Blo 1756579 8897525 := bbase (se 5 (by rfl) ⟨417071, by rfl⟩ : syracuseStep 8897525 = 834143) (by norm_num)
theorem B4449269 : Blo 1756579 4449269 := bbase (se 5 (by rfl) ⟨208559, by rfl⟩ : syracuseStep 4449269 = 417119) (by norm_num)
theorem B2966557 : Blo 1756579 2966557 := bbase (se 3 (by rfl) ⟨556229, by rfl⟩ : syracuseStep 2966557 = 1112459) (by norm_num)
theorem B2253889 : Blo 1756579 2253889 := bbase (se 2 (by rfl) ⟨845208, by rfl⟩ : syracuseStep 2253889 = 1690417) (by norm_num)
theorem B3753029 : Blo 1756579 3753029 := bbase (se 4 (by rfl) ⟨351846, by rfl⟩ : syracuseStep 3753029 = 703693) (by norm_num)
theorem B2966645 : Blo 1756579 2966645 := bbase (se 5 (by rfl) ⟨139061, by rfl⟩ : syracuseStep 2966645 = 278123) (by norm_num)
theorem B3335357 : Blo 1756579 3335357 := bbase (se 3 (by rfl) ⟨625379, by rfl⟩ : syracuseStep 3335357 = 1250759) (by norm_num)
theorem B5932277 : Blo 1756579 5932277 := bbase (se 5 (by rfl) ⟨278075, by rfl⟩ : syracuseStep 5932277 = 556151) (by norm_num)
theorem B8447237 : Blo 1756579 8447237 := bbase (se 4 (by rfl) ⟨791928, by rfl⟩ : syracuseStep 8447237 = 1583857) (by norm_num)
theorem B4449613 : Blo 1756579 4449613 := bbase (se 3 (by rfl) ⟨834302, by rfl⟩ : syracuseStep 4449613 = 1668605) (by norm_num)
theorem B3335509 : Blo 1756579 3335509 := bbase (se 12 (by rfl) ⟨1221, by rfl⟩ : syracuseStep 3335509 = 2443) (by norm_num)
theorem B7505237 : Blo 1756579 7505237 := bbase (se 12 (by rfl) ⟨2748, by rfl⟩ : syracuseStep 7505237 = 5497) (by norm_num)
theorem B1877365 : Blo 1756579 1877365 := bbase (se 5 (by rfl) ⟨88001, by rfl⟩ : syracuseStep 1877365 = 176003) (by norm_num)
theorem B4449725 : Blo 1756579 4449725 := bbase (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) (by norm_num)
theorem B27059669 : Blo 1756579 27059669 := bbase (se 7 (by rfl) ⟨317105, by rfl⟩ : syracuseStep 27059669 = 634211) (by norm_num)
theorem B2254321 : Blo 1756579 2254321 := bbase (se 2 (by rfl) ⟨845370, by rfl⟩ : syracuseStep 2254321 = 1690741) (by norm_num)
theorem B5629429 : Blo 1756579 5629429 := bbase (se 5 (by rfl) ⟨263879, by rfl⟩ : syracuseStep 5629429 = 527759) (by norm_num)
theorem B5629493 : Blo 1756579 5629493 := bbase (se 5 (by rfl) ⟨263882, by rfl⟩ : syracuseStep 5629493 = 527765) (by norm_num)
theorem B2672237 : Blo 1756579 2672237 := bbase (se 3 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 2672237 = 1002089) (by norm_num)
theorem B4449917 : Blo 1756579 4449917 := bbase (se 3 (by rfl) ⟨834359, by rfl⟩ : syracuseStep 4449917 = 1668719) (by norm_num)
theorem B3335813 : Blo 1756579 3335813 := bbase (se 4 (by rfl) ⟨312732, by rfl⟩ : syracuseStep 3335813 = 625465) (by norm_num)
theorem B5932709 : Blo 1756579 5932709 := bbase (se 4 (by rfl) ⟨556191, by rfl⟩ : syracuseStep 5932709 = 1112383) (by norm_num)
theorem B3753773 : Blo 1756579 3753773 := bbase (se 3 (by rfl) ⟨703832, by rfl⟩ : syracuseStep 3753773 = 1407665) (by norm_num)
theorem B1976161 : Blo 1756579 1976161 := bbase (se 2 (by rfl) ⟨741060, by rfl⟩ : syracuseStep 1976161 = 1482121) (by norm_num)
theorem B1976197 : Blo 1756579 1976197 := bbase (se 4 (by rfl) ⟨185268, by rfl⟩ : syracuseStep 1976197 = 370537) (by norm_num)
theorem B1976233 : Blo 1756579 1976233 := bbase (se 2 (by rfl) ⟨741087, by rfl⟩ : syracuseStep 1976233 = 1482175) (by norm_num)
theorem B1976269 : Blo 1756579 1976269 := bbase (se 3 (by rfl) ⟨370550, by rfl⟩ : syracuseStep 1976269 = 741101) (by norm_num)
theorem B1976305 : Blo 1756579 1976305 := bbase (se 2 (by rfl) ⟨741114, by rfl⟩ : syracuseStep 1976305 = 1482229) (by norm_num)
theorem B4507645 : Blo 1756579 4507645 := bbase (se 3 (by rfl) ⟨845183, by rfl⟩ : syracuseStep 4507645 = 1690367) (by norm_num)
theorem B1976341 : Blo 1756579 1976341 := bbase (se 6 (by rfl) ⟨46320, by rfl⟩ : syracuseStep 1976341 = 92641) (by norm_num)
theorem B1976377 : Blo 1756579 1976377 := bbase (se 2 (by rfl) ⟨741141, by rfl⟩ : syracuseStep 1976377 = 1482283) (by norm_num)
theorem B5933141 : Blo 1756579 5933141 := bbase (se 8 (by rfl) ⟨34764, by rfl⟩ : syracuseStep 5933141 = 69529) (by norm_num)
theorem B1976413 : Blo 1756579 1976413 := bbase (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) (by norm_num)
theorem B1976449 : Blo 1756579 1976449 := bbase (se 2 (by rfl) ⟨741168, by rfl⟩ : syracuseStep 1976449 = 1482337) (by norm_num)
theorem B1976485 : Blo 1756579 1976485 := bbase (se 4 (by rfl) ⟨185295, by rfl⟩ : syracuseStep 1976485 = 370591) (by norm_num)
theorem B1976521 : Blo 1756579 1976521 := bbase (se 2 (by rfl) ⟨741195, by rfl⟩ : syracuseStep 1976521 = 1482391) (by norm_num)
theorem B16894165 : Blo 1756579 16894165 := bbase (se 7 (by rfl) ⟨197978, by rfl⟩ : syracuseStep 16894165 = 395957) (by norm_num)
theorem B1976557 : Blo 1756579 1976557 := bbase (se 3 (by rfl) ⟨370604, by rfl⟩ : syracuseStep 1976557 = 741209) (by norm_num)
theorem B8898821 : Blo 1756579 8898821 := bbase (se 4 (by rfl) ⟨834264, by rfl⟩ : syracuseStep 8898821 = 1668529) (by norm_num)
theorem B1976593 : Blo 1756579 1976593 := bbase (se 2 (by rfl) ⟨741222, by rfl⟩ : syracuseStep 1976593 = 1482445) (by norm_num)
theorem B1976629 : Blo 1756579 1976629 := bbase (se 5 (by rfl) ⟨92654, by rfl⟩ : syracuseStep 1976629 = 185309) (by norm_num)
theorem B7506229 : Blo 1756579 7506229 := bbase (se 5 (by rfl) ⟨351854, by rfl⟩ : syracuseStep 7506229 = 703709) (by norm_num)
theorem B1976665 : Blo 1756579 1976665 := bbase (se 2 (by rfl) ⟨741249, by rfl⟩ : syracuseStep 1976665 = 1482499) (by norm_num)
theorem B3336565 : Blo 1756579 3336565 := bbase (se 5 (by rfl) ⟨156401, by rfl⟩ : syracuseStep 3336565 = 312803) (by norm_num)
theorem B1976701 : Blo 1756579 1976701 := bbase (se 3 (by rfl) ⟨370631, by rfl⟩ : syracuseStep 1976701 = 741263) (by norm_num)
theorem B1976737 : Blo 1756579 1976737 := bbase (se 2 (by rfl) ⟨741276, by rfl⟩ : syracuseStep 1976737 = 1482553) (by norm_num)
theorem B1976773 : Blo 1756579 1976773 := bbase (se 4 (by rfl) ⟨185322, by rfl⟩ : syracuseStep 1976773 = 370645) (by norm_num)
theorem B1976809 : Blo 1756579 1976809 := bbase (se 2 (by rfl) ⟨741303, by rfl⟩ : syracuseStep 1976809 = 1482607) (by norm_num)
theorem B3336709 : Blo 1756579 3336709 := bbase (se 4 (by rfl) ⟨312816, by rfl⟩ : syracuseStep 3336709 = 625633) (by norm_num)
theorem B1976845 : Blo 1756579 1976845 := bbase (se 3 (by rfl) ⟨370658, by rfl⟩ : syracuseStep 1976845 = 741317) (by norm_num)
theorem B3754525 : Blo 1756579 3754525 := bbase (se 3 (by rfl) ⟨703973, by rfl⟩ : syracuseStep 3754525 = 1407947) (by norm_num)
theorem B2501165 : Blo 1756579 2501165 := bbase (se 3 (by rfl) ⟨468968, by rfl⟩ : syracuseStep 2501165 = 937937) (by norm_num)
theorem B1976881 : Blo 1756579 1976881 := bbase (se 2 (by rfl) ⟨741330, by rfl⟩ : syracuseStep 1976881 = 1482661) (by norm_num)
theorem B1976917 : Blo 1756579 1976917 := bbase (se 8 (by rfl) ⟨11583, by rfl⟩ : syracuseStep 1976917 = 23167) (by norm_num)
theorem B1976953 : Blo 1756579 1976953 := bbase (se 2 (by rfl) ⟨741357, by rfl⟩ : syracuseStep 1976953 = 1482715) (by norm_num)
theorem B1976989 : Blo 1756579 1976989 := bbase (se 3 (by rfl) ⟨370685, by rfl⟩ : syracuseStep 1976989 = 741371) (by norm_num)
theorem B3336869 : Blo 1756579 3336869 := bbase (se 4 (by rfl) ⟨312831, by rfl⟩ : syracuseStep 3336869 = 625663) (by norm_num)
theorem B3754669 : Blo 1756579 3754669 := bbase (se 3 (by rfl) ⟨704000, by rfl⟩ : syracuseStep 3754669 = 1408001) (by norm_num)
theorem B1977025 : Blo 1756579 1977025 := bbase (se 2 (by rfl) ⟨741384, by rfl⟩ : syracuseStep 1977025 = 1482769) (by norm_num)
theorem B1977061 : Blo 1756579 1977061 := bbase (se 4 (by rfl) ⟨185349, by rfl⟩ : syracuseStep 1977061 = 370699) (by norm_num)
theorem B4008701 : Blo 1756579 4008701 := bbase (se 3 (by rfl) ⟨751631, by rfl⟩ : syracuseStep 4008701 = 1503263) (by norm_num)
theorem B1977097 : Blo 1756579 1977097 := bbase (se 2 (by rfl) ⟨741411, by rfl⟩ : syracuseStep 1977097 = 1482823) (by norm_num)
theorem B1977133 : Blo 1756579 1977133 := bbase (se 3 (by rfl) ⟨370712, by rfl⟩ : syracuseStep 1977133 = 741425) (by norm_num)
theorem B3337013 : Blo 1756579 3337013 := bbase (se 5 (by rfl) ⟨156422, by rfl⟩ : syracuseStep 3337013 = 312845) (by norm_num)
theorem B1977169 : Blo 1756579 1977169 := bbase (se 2 (by rfl) ⟨741438, by rfl⟩ : syracuseStep 1977169 = 1482877) (by norm_num)
theorem B1977205 : Blo 1756579 1977205 := bbase (se 5 (by rfl) ⟨92681, by rfl⟩ : syracuseStep 1977205 = 185363) (by norm_num)
theorem B1977241 : Blo 1756579 1977241 := bbase (se 2 (by rfl) ⟨741465, by rfl⟩ : syracuseStep 1977241 = 1482931) (by norm_num)
theorem B1977277 : Blo 1756579 1977277 := bbase (se 3 (by rfl) ⟨370739, by rfl⟩ : syracuseStep 1977277 = 741479) (by norm_num)
theorem B1977313 : Blo 1756579 1977313 := bbase (se 2 (by rfl) ⟨741492, by rfl⟩ : syracuseStep 1977313 = 1482985) (by norm_num)
theorem B17591285 : Blo 1756579 17591285 := bbase (se 5 (by rfl) ⟨824591, by rfl⟩ : syracuseStep 17591285 = 1649183) (by norm_num)
theorem B1977349 : Blo 1756579 1977349 := bbase (se 4 (by rfl) ⟨185376, by rfl⟩ : syracuseStep 1977349 = 370753) (by norm_num)
theorem B12028949 : Blo 1756579 12028949 := bbase (se 6 (by rfl) ⟨281928, by rfl⟩ : syracuseStep 12028949 = 563857) (by norm_num)
theorem B1977385 : Blo 1756579 1977385 := bbase (se 2 (by rfl) ⟨741519, by rfl⟩ : syracuseStep 1977385 = 1483039) (by norm_num)
theorem B6671429 : Blo 1756579 6671429 := bbase (se 4 (by rfl) ⟨625446, by rfl⟩ : syracuseStep 6671429 = 1250893) (by norm_num)
theorem B1977421 : Blo 1756579 1977421 := bbase (se 3 (by rfl) ⟨370766, by rfl⟩ : syracuseStep 1977421 = 741533) (by norm_num)
theorem B3337301 : Blo 1756579 3337301 := bbase (se 8 (by rfl) ⟨19554, by rfl⟩ : syracuseStep 3337301 = 39109) (by norm_num)
theorem B2223217 : Blo 1756579 2223217 := bbase (se 2 (by rfl) ⟨833706, by rfl⟩ : syracuseStep 2223217 = 1667413) (by norm_num)
theorem B1977457 : Blo 1756579 1977457 := bbase (se 2 (by rfl) ⟨741546, by rfl⟩ : syracuseStep 1977457 = 1483093) (by norm_num)
theorem B13347989 : Blo 1756579 13347989 := bbase (se 6 (by rfl) ⟨312843, by rfl⟩ : syracuseStep 13347989 = 625687) (by norm_num)
theorem B1977493 : Blo 1756579 1977493 := bbase (se 6 (by rfl) ⟨46347, by rfl⟩ : syracuseStep 1977493 = 92695) (by norm_num)
theorem B1977529 : Blo 1756579 1977529 := bbase (se 2 (by rfl) ⟨741573, by rfl⟩ : syracuseStep 1977529 = 1483147) (by norm_num)
theorem B22523093 : Blo 1756579 22523093 := bbase (se 7 (by rfl) ⟨263942, by rfl⟩ : syracuseStep 22523093 = 527885) (by norm_num)
theorem B1977565 : Blo 1756579 1977565 := bbase (se 3 (by rfl) ⟨370793, by rfl⟩ : syracuseStep 1977565 = 741587) (by norm_num)
theorem B3337453 : Blo 1756579 3337453 := bbase (se 3 (by rfl) ⟨625772, by rfl⟩ : syracuseStep 3337453 = 1251545) (by norm_num)
theorem B1977601 : Blo 1756579 1977601 := bbase (se 2 (by rfl) ⟨741600, by rfl⟩ : syracuseStep 1977601 = 1483201) (by norm_num)
theorem B2223389 : Blo 1756579 2223389 := bbase (se 3 (by rfl) ⟨416885, by rfl⟩ : syracuseStep 2223389 = 833771) (by norm_num)
theorem B1977637 : Blo 1756579 1977637 := bbase (se 4 (by rfl) ⟨185403, by rfl⟩ : syracuseStep 1977637 = 370807) (by norm_num)
theorem B5705029 : Blo 1756579 5705029 := bbase (se 4 (by rfl) ⟨534846, by rfl⟩ : syracuseStep 5705029 = 1069693) (by norm_num)
theorem B1977673 : Blo 1756579 1977673 := bbase (se 2 (by rfl) ⟨741627, by rfl⟩ : syracuseStep 1977673 = 1483255) (by norm_num)
theorem B2223445 : Blo 1756579 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B6671717 : Blo 1756579 6671717 := bbase (se 4 (by rfl) ⟨625473, by rfl⟩ : syracuseStep 6671717 = 1250947) (by norm_num)
theorem B1977709 : Blo 1756579 1977709 := bbase (se 3 (by rfl) ⟨370820, by rfl⟩ : syracuseStep 1977709 = 741641) (by norm_num)
theorem B1977745 : Blo 1756579 1977745 := bbase (se 2 (by rfl) ⟨741654, by rfl⟩ : syracuseStep 1977745 = 1483309) (by norm_num)
theorem B2223541 : Blo 1756579 2223541 := bbase (se 5 (by rfl) ⟨104228, by rfl⟩ : syracuseStep 2223541 = 208457) (by norm_num)
theorem B1977781 : Blo 1756579 1977781 := bbase (se 5 (by rfl) ⟨92708, by rfl⟩ : syracuseStep 1977781 = 185417) (by norm_num)
theorem B1977817 : Blo 1756579 1977817 := bbase (se 2 (by rfl) ⟨741681, by rfl⟩ : syracuseStep 1977817 = 1483363) (by norm_num)
theorem B4509173 : Blo 1756579 4509173 := bbase (se 5 (by rfl) ⟨211367, by rfl⟩ : syracuseStep 4509173 = 422735) (by norm_num)
theorem B8900117 : Blo 1756579 8900117 := bbase (se 6 (by rfl) ⟨208596, by rfl⟩ : syracuseStep 8900117 = 417193) (by norm_num)
theorem B13340213 : Blo 1756579 13340213 := bbase (se 5 (by rfl) ⟨625322, by rfl⟩ : syracuseStep 13340213 = 1250645) (by norm_num)
theorem B2223713 : Blo 1756579 2223713 := bbase (se 2 (by rfl) ⟨833892, by rfl⟩ : syracuseStep 2223713 = 1667785) (by norm_num)
theorem B18992789 : Blo 1756579 18992789 := bbase (se 6 (by rfl) ⟨445143, by rfl⟩ : syracuseStep 18992789 = 890287) (by norm_num)
theorem B6336149 : Blo 1756579 6336149 := bbase (se 6 (by rfl) ⟨148503, by rfl⟩ : syracuseStep 6336149 = 297007) (by norm_num)
theorem B2223769 : Blo 1756579 2223769 := bbase (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) (by norm_num)
theorem B3165869 : Blo 1756579 3165869 := bbase (se 3 (by rfl) ⟨593600, by rfl⟩ : syracuseStep 3165869 = 1187201) (by norm_num)
theorem B3952349 : Blo 1756579 3952349 := bbase (se 3 (by rfl) ⟨741065, by rfl⟩ : syracuseStep 3952349 = 1482131) (by norm_num)
theorem B2223865 : Blo 1756579 2223865 := bbase (se 2 (by rfl) ⟨833949, by rfl⟩ : syracuseStep 2223865 = 1667899) (by norm_num)
theorem B3952421 : Blo 1756579 3952421 := bbase (se 4 (by rfl) ⟨370539, by rfl⟩ : syracuseStep 3952421 = 741079) (by norm_num)
theorem B3166013 : Blo 1756579 3166013 := bbase (se 3 (by rfl) ⟨593627, by rfl⟩ : syracuseStep 3166013 = 1187255) (by norm_num)
theorem B2813773 : Blo 1756579 2813773 := bbase (se 3 (by rfl) ⟨527582, by rfl⟩ : syracuseStep 2813773 = 1055165) (by norm_num)
theorem B3952493 : Blo 1756579 3952493 := bbase (se 3 (by rfl) ⟨741092, by rfl⟩ : syracuseStep 3952493 = 1482185) (by norm_num)
theorem B2224037 : Blo 1756579 2224037 := bbase (se 4 (by rfl) ⟨208503, by rfl⟩ : syracuseStep 2224037 = 417007) (by norm_num)
theorem B1781677 : Blo 1756579 1781677 := bbase (se 3 (by rfl) ⟨334064, by rfl⟩ : syracuseStep 1781677 = 668129) (by norm_num)
theorem B3952565 : Blo 1756579 3952565 := bbase (se 5 (by rfl) ⟨185276, by rfl⟩ : syracuseStep 3952565 = 370553) (by norm_num)
theorem B2502589 : Blo 1756579 2502589 := bbase (se 3 (by rfl) ⟨469235, by rfl⟩ : syracuseStep 2502589 = 938471) (by norm_num)
theorem B4337621 : Blo 1756579 4337621 := bbase (se 7 (by rfl) ⟨50831, by rfl⟩ : syracuseStep 4337621 = 101663) (by norm_num)
theorem B2224093 : Blo 1756579 2224093 := bbase (se 3 (by rfl) ⟨417017, by rfl⟩ : syracuseStep 2224093 = 834035) (by norm_num)
theorem B3952637 : Blo 1756579 3952637 := bbase (se 3 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 3952637 = 1482239) (by norm_num)
theorem B2224189 : Blo 1756579 2224189 := bbase (se 3 (by rfl) ⟨417035, by rfl⟩ : syracuseStep 2224189 = 834071) (by norm_num)
theorem B3952709 : Blo 1756579 3952709 := bbase (se 4 (by rfl) ⟨370566, by rfl⟩ : syracuseStep 3952709 = 741133) (by norm_num)
theorem B2814029 : Blo 1756579 2814029 := bbase (se 3 (by rfl) ⟨527630, by rfl⟩ : syracuseStep 2814029 = 1055261) (by norm_num)
theorem B2535509 : Blo 1756579 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B4509829 : Blo 1756579 4509829 := bbase (se 4 (by rfl) ⟨422796, by rfl⟩ : syracuseStep 4509829 = 845593) (by norm_num)
theorem B3952781 : Blo 1756579 3952781 := bbase (se 3 (by rfl) ⟨741146, by rfl⟩ : syracuseStep 3952781 = 1482293) (by norm_num)
theorem B3952853 : Blo 1756579 3952853 := bbase (se 7 (by rfl) ⟨46322, by rfl⟩ : syracuseStep 3952853 = 92645) (by norm_num)
theorem B2224361 : Blo 1756579 2224361 := bbase (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) (by norm_num)
theorem B2814221 : Blo 1756579 2814221 := bbase (se 3 (by rfl) ⟨527666, by rfl⟩ : syracuseStep 2814221 = 1055333) (by norm_num)
theorem B3952925 : Blo 1756579 3952925 := bbase (se 3 (by rfl) ⟨741173, by rfl⟩ : syracuseStep 3952925 = 1482347) (by norm_num)
theorem B2224417 : Blo 1756579 2224417 := bbase (se 2 (by rfl) ⟨834156, by rfl⟩ : syracuseStep 2224417 = 1668313) (by norm_num)
theorem B3952997 : Blo 1756579 3952997 := bbase (se 4 (by rfl) ⟨370593, by rfl⟩ : syracuseStep 3952997 = 741187) (by norm_num)
theorem B2224513 : Blo 1756579 2224513 := bbase (se 2 (by rfl) ⟨834192, by rfl⟩ : syracuseStep 2224513 = 1668385) (by norm_num)
theorem B19001749 : Blo 1756579 19001749 := bbase (se 6 (by rfl) ⟨445353, by rfl⟩ : syracuseStep 19001749 = 890707) (by norm_num)
theorem B3953069 : Blo 1756579 3953069 := bbase (se 3 (by rfl) ⟨741200, by rfl⟩ : syracuseStep 3953069 = 1482401) (by norm_num)
theorem B3953141 : Blo 1756579 3953141 := bbase (se 5 (by rfl) ⟨185303, by rfl⟩ : syracuseStep 3953141 = 370607) (by norm_num)
theorem B2535925 : Blo 1756579 2535925 := bbase (se 5 (by rfl) ⟨118871, by rfl⟩ : syracuseStep 2535925 = 237743) (by norm_num)
theorem B6672901 : Blo 1756579 6672901 := bbase (se 4 (by rfl) ⟨625584, by rfl⟩ : syracuseStep 6672901 = 1251169) (by norm_num)
theorem B2503181 : Blo 1756579 2503181 := bbase (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) (by norm_num)
theorem B15430165 : Blo 1756579 15430165 := bbase (se 6 (by rfl) ⟨361644, by rfl⟩ : syracuseStep 15430165 = 723289) (by norm_num)
theorem B2224685 : Blo 1756579 2224685 := bbase (se 3 (by rfl) ⟨417128, by rfl⟩ : syracuseStep 2224685 = 834257) (by norm_num)
theorem B3953213 : Blo 1756579 3953213 := bbase (se 3 (by rfl) ⟨741227, by rfl⟩ : syracuseStep 3953213 = 1482455) (by norm_num)
theorem B2224741 : Blo 1756579 2224741 := bbase (se 4 (by rfl) ⟨208569, by rfl⟩ : syracuseStep 2224741 = 417139) (by norm_num)
theorem B7713397 : Blo 1756579 7713397 := bbase (se 5 (by rfl) ⟨361565, by rfl⟩ : syracuseStep 7713397 = 723131) (by norm_num)
theorem B5345909 : Blo 1756579 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B3953285 : Blo 1756579 3953285 := bbase (se 4 (by rfl) ⟨370620, by rfl⟩ : syracuseStep 3953285 = 741241) (by norm_num)
theorem B2003617 : Blo 1756579 2003617 := bbase (se 2 (by rfl) ⟨751356, by rfl⟩ : syracuseStep 2003617 = 1502713) (by norm_num)
theorem B2224837 : Blo 1756579 2224837 := bbase (se 4 (by rfl) ⟨208578, by rfl⟩ : syracuseStep 2224837 = 417157) (by norm_num)
theorem B3953357 : Blo 1756579 3953357 := bbase (se 3 (by rfl) ⟨741254, by rfl⟩ : syracuseStep 3953357 = 1482509) (by norm_num)
theorem B3953429 : Blo 1756579 3953429 := bbase (se 6 (by rfl) ⟨92658, by rfl⟩ : syracuseStep 3953429 = 185317) (by norm_num)
theorem B15012661 : Blo 1756579 15012661 := bbase (se 5 (by rfl) ⟨703718, by rfl⟩ : syracuseStep 15012661 = 1407437) (by norm_num)
theorem B6673205 : Blo 1756579 6673205 := bbase (se 5 (by rfl) ⟨312806, by rfl⟩ : syracuseStep 6673205 = 625613) (by norm_num)
theorem B3953501 : Blo 1756579 3953501 := bbase (se 3 (by rfl) ⟨741281, by rfl⟩ : syracuseStep 3953501 = 1482563) (by norm_num)
theorem B2225009 : Blo 1756579 2225009 := bbase (se 2 (by rfl) ⟨834378, by rfl⟩ : syracuseStep 2225009 = 1668757) (by norm_num)
theorem B3953573 : Blo 1756579 3953573 := bbase (se 4 (by rfl) ⟨370647, by rfl⟩ : syracuseStep 3953573 = 741295) (by norm_num)
theorem B2225065 : Blo 1756579 2225065 := bbase (se 2 (by rfl) ⟨834399, by rfl⟩ : syracuseStep 2225065 = 1668799) (by norm_num)
theorem B4223917 : Blo 1756579 4223917 := bbase (se 3 (by rfl) ⟨791984, by rfl⟩ : syracuseStep 4223917 = 1583969) (by norm_num)
theorem B2110421 : Blo 1756579 2110421 := bbase (se 7 (by rfl) ⟨24731, by rfl⟩ : syracuseStep 2110421 = 49463) (by norm_num)
theorem B9630677 : Blo 1756579 9630677 := bbase (se 7 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 9630677 = 225719) (by norm_num)
theorem B3953645 : Blo 1756579 3953645 := bbase (se 3 (by rfl) ⟨741308, by rfl⟩ : syracuseStep 3953645 = 1482617) (by norm_num)
theorem B3953717 : Blo 1756579 3953717 := bbase (se 5 (by rfl) ⟨185330, by rfl⟩ : syracuseStep 3953717 = 370661) (by norm_num)
theorem B5706821 : Blo 1756579 5706821 := bbase (se 4 (by rfl) ⟨535014, by rfl⟩ : syracuseStep 5706821 = 1070029) (by norm_num)
theorem B2634869 : Blo 1756579 2634869 := bbase (se 5 (by rfl) ⟨123509, by rfl⟩ : syracuseStep 2634869 = 247019) (by norm_num)
theorem B3953789 : Blo 1756579 3953789 := bbase (se 3 (by rfl) ⟨741335, by rfl⟩ : syracuseStep 3953789 = 1482671) (by norm_num)
theorem B2634893 : Blo 1756579 2634893 := bbase (se 3 (by rfl) ⟨494042, by rfl⟩ : syracuseStep 2634893 = 988085) (by norm_num)
theorem B2634917 : Blo 1756579 2634917 := bbase (se 4 (by rfl) ⟨247023, by rfl⟩ : syracuseStep 2634917 = 494047) (by norm_num)
theorem B2815157 : Blo 1756579 2815157 := bbase (se 5 (by rfl) ⟨131960, by rfl⟩ : syracuseStep 2815157 = 263921) (by norm_num)
theorem B2634941 : Blo 1756579 2634941 := bbase (se 3 (by rfl) ⟨494051, by rfl⟩ : syracuseStep 2634941 = 988103) (by norm_num)
theorem B8893637 : Blo 1756579 8893637 := bbase (se 4 (by rfl) ⟨833778, by rfl⟩ : syracuseStep 8893637 = 1667557) (by norm_num)
theorem B3953861 : Blo 1756579 3953861 := bbase (se 4 (by rfl) ⟨370674, by rfl⟩ : syracuseStep 3953861 = 741349) (by norm_num)
theorem B2634965 : Blo 1756579 2634965 := bbase (se 7 (by rfl) ⟨30878, by rfl⟩ : syracuseStep 2634965 = 61757) (by norm_num)
theorem B4748501 : Blo 1756579 4748501 := bbase (se 7 (by rfl) ⟨55646, by rfl⟩ : syracuseStep 4748501 = 111293) (by norm_num)
theorem B2634989 : Blo 1756579 2634989 := bbase (se 3 (by rfl) ⟨494060, by rfl⟩ : syracuseStep 2634989 = 988121) (by norm_num)
theorem B2635013 : Blo 1756579 2635013 := bbase (se 4 (by rfl) ⟨247032, by rfl⟩ : syracuseStep 2635013 = 494065) (by norm_num)
theorem B3953933 : Blo 1756579 3953933 := bbase (se 3 (by rfl) ⟨741362, by rfl⟩ : syracuseStep 3953933 = 1482725) (by norm_num)
theorem B2635037 : Blo 1756579 2635037 := bbase (se 3 (by rfl) ⟨494069, by rfl⟩ : syracuseStep 2635037 = 988139) (by norm_num)
theorem B2635061 : Blo 1756579 2635061 := bbase (se 5 (by rfl) ⟨123518, by rfl⟩ : syracuseStep 2635061 = 247037) (by norm_num)
theorem B2635085 : Blo 1756579 2635085 := bbase (se 3 (by rfl) ⟨494078, by rfl⟩ : syracuseStep 2635085 = 988157) (by norm_num)
theorem B3954005 : Blo 1756579 3954005 := bbase (se 16 (by rfl) ⟨90, by rfl⟩ : syracuseStep 3954005 = 181) (by norm_num)
theorem B2635109 : Blo 1756579 2635109 := bbase (se 4 (by rfl) ⟨247041, by rfl⟩ : syracuseStep 2635109 = 494083) (by norm_num)
theorem B2635133 : Blo 1756579 2635133 := bbase (se 3 (by rfl) ⟨494087, by rfl⟩ : syracuseStep 2635133 = 988175) (by norm_num)
theorem B2635157 : Blo 1756579 2635157 := bbase (se 6 (by rfl) ⟨61761, by rfl⟩ : syracuseStep 2635157 = 123523) (by norm_num)
theorem B3954077 : Blo 1756579 3954077 := bbase (se 3 (by rfl) ⟨741389, by rfl⟩ : syracuseStep 3954077 = 1482779) (by norm_num)
theorem B5002661 : Blo 1756579 5002661 := bbase (se 4 (by rfl) ⟨468999, by rfl⟩ : syracuseStep 5002661 = 937999) (by norm_num)
theorem B2635181 : Blo 1756579 2635181 := bbase (se 3 (by rfl) ⟨494096, by rfl⟩ : syracuseStep 2635181 = 988193) (by norm_num)
theorem B2110897 : Blo 1756579 2110897 := bbase (se 2 (by rfl) ⟨791586, by rfl⟩ : syracuseStep 2110897 = 1583173) (by norm_num)
theorem B2635205 : Blo 1756579 2635205 := bbase (se 4 (by rfl) ⟨247050, by rfl⟩ : syracuseStep 2635205 = 494101) (by norm_num)
theorem B2110925 : Blo 1756579 2110925 := bbase (se 3 (by rfl) ⟨395798, by rfl⟩ : syracuseStep 2110925 = 791597) (by norm_num)
theorem B2635229 : Blo 1756579 2635229 := bbase (se 3 (by rfl) ⟨494105, by rfl⟩ : syracuseStep 2635229 = 988211) (by norm_num)
theorem B3954149 : Blo 1756579 3954149 := bbase (se 4 (by rfl) ⟨370701, by rfl⟩ : syracuseStep 3954149 = 741403) (by norm_num)
theorem B2635253 : Blo 1756579 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B2635277 : Blo 1756579 2635277 := bbase (se 3 (by rfl) ⟨494114, by rfl⟩ : syracuseStep 2635277 = 988229) (by norm_num)
theorem B2004493 : Blo 1756579 2004493 := bbase (se 3 (by rfl) ⟨375842, by rfl⟩ : syracuseStep 2004493 = 751685) (by norm_num)
theorem B2635301 : Blo 1756579 2635301 := bbase (se 4 (by rfl) ⟨247059, by rfl⟩ : syracuseStep 2635301 = 494119) (by norm_num)
theorem B3954221 : Blo 1756579 3954221 := bbase (se 3 (by rfl) ⟨741416, by rfl⟩ : syracuseStep 3954221 = 1482833) (by norm_num)
theorem B2815541 : Blo 1756579 2815541 := bbase (se 5 (by rfl) ⟨131978, by rfl⟩ : syracuseStep 2815541 = 263957) (by norm_num)
theorem B2635325 : Blo 1756579 2635325 := bbase (se 3 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 2635325 = 988247) (by norm_num)
theorem B2635349 : Blo 1756579 2635349 := bbase (se 8 (by rfl) ⟨15441, by rfl⟩ : syracuseStep 2635349 = 30883) (by norm_num)
theorem B2635373 : Blo 1756579 2635373 := bbase (se 3 (by rfl) ⟨494132, by rfl⟩ : syracuseStep 2635373 = 988265) (by norm_num)
theorem B3954293 : Blo 1756579 3954293 := bbase (se 5 (by rfl) ⟨185357, by rfl⟩ : syracuseStep 3954293 = 370715) (by norm_num)
theorem B2635397 : Blo 1756579 2635397 := bbase (se 4 (by rfl) ⟨247068, by rfl⟩ : syracuseStep 2635397 = 494137) (by norm_num)
theorem B2111113 : Blo 1756579 2111113 := bbase (se 2 (by rfl) ⟨791667, by rfl⟩ : syracuseStep 2111113 = 1583335) (by norm_num)
theorem B2004625 : Blo 1756579 2004625 := bbase (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) (by norm_num)
theorem B2635421 : Blo 1756579 2635421 := bbase (se 3 (by rfl) ⟨494141, by rfl⟩ : syracuseStep 2635421 = 988283) (by norm_num)
theorem B2635445 : Blo 1756579 2635445 := bbase (se 5 (by rfl) ⟨123536, by rfl⟩ : syracuseStep 2635445 = 247073) (by norm_num)
theorem B2815669 : Blo 1756579 2815669 := bbase (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) (by norm_num)
theorem B3954365 : Blo 1756579 3954365 := bbase (se 3 (by rfl) ⟨741443, by rfl⟩ : syracuseStep 3954365 = 1482887) (by norm_num)
theorem B2635469 : Blo 1756579 2635469 := bbase (se 3 (by rfl) ⟨494150, by rfl⟩ : syracuseStep 2635469 = 988301) (by norm_num)
theorem B2537173 : Blo 1756579 2537173 := bbase (se 7 (by rfl) ⟨29732, by rfl⟩ : syracuseStep 2537173 = 59465) (by norm_num)
theorem B2635493 : Blo 1756579 2635493 := bbase (se 4 (by rfl) ⟨247077, by rfl⟩ : syracuseStep 2635493 = 494155) (by norm_num)
theorem B2635517 : Blo 1756579 2635517 := bbase (se 3 (by rfl) ⟨494159, by rfl⟩ : syracuseStep 2635517 = 988319) (by norm_num)
theorem B2111233 : Blo 1756579 2111233 := bbase (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) (by norm_num)
theorem B3954437 : Blo 1756579 3954437 := bbase (se 4 (by rfl) ⟨370728, by rfl⟩ : syracuseStep 3954437 = 741457) (by norm_num)
theorem B2635541 : Blo 1756579 2635541 := bbase (se 6 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 2635541 = 123541) (by norm_num)
theorem B2635565 : Blo 1756579 2635565 := bbase (se 3 (by rfl) ⟨494168, by rfl⟩ : syracuseStep 2635565 = 988337) (by norm_num)
theorem B2635589 : Blo 1756579 2635589 := bbase (se 4 (by rfl) ⟨247086, by rfl⟩ : syracuseStep 2635589 = 494173) (by norm_num)
theorem B3299141 : Blo 1756579 3299141 := bbase (se 4 (by rfl) ⟨309294, by rfl⟩ : syracuseStep 3299141 = 618589) (by norm_num)
theorem B3954509 : Blo 1756579 3954509 := bbase (se 3 (by rfl) ⟨741470, by rfl⟩ : syracuseStep 3954509 = 1482941) (by norm_num)
theorem B3610453 : Blo 1756579 3610453 := bbase (se 9 (by rfl) ⟨10577, by rfl⟩ : syracuseStep 3610453 = 21155) (by norm_num)
theorem B2635613 : Blo 1756579 2635613 := bbase (se 3 (by rfl) ⟨494177, by rfl⟩ : syracuseStep 2635613 = 988355) (by norm_num)
theorem B5928821 : Blo 1756579 5928821 := bbase (se 5 (by rfl) ⟨277913, by rfl⟩ : syracuseStep 5928821 = 555827) (by norm_num)
theorem B2635637 : Blo 1756579 2635637 := bbase (se 5 (by rfl) ⟨123545, by rfl⟩ : syracuseStep 2635637 = 247091) (by norm_num)
theorem B2930573 : Blo 1756579 2930573 := bbase (se 3 (by rfl) ⟨549482, by rfl⟩ : syracuseStep 2930573 = 1098965) (by norm_num)
theorem B2635661 : Blo 1756579 2635661 := bbase (se 3 (by rfl) ⟨494186, by rfl⟩ : syracuseStep 2635661 = 988373) (by norm_num)
theorem B3954581 : Blo 1756579 3954581 := bbase (se 6 (by rfl) ⟨92685, by rfl⟩ : syracuseStep 3954581 = 185371) (by norm_num)
theorem B2635685 : Blo 1756579 2635685 := bbase (se 4 (by rfl) ⟨247095, by rfl⟩ : syracuseStep 2635685 = 494191) (by norm_num)
theorem B2635709 : Blo 1756579 2635709 := bbase (se 3 (by rfl) ⟨494195, by rfl⟩ : syracuseStep 2635709 = 988391) (by norm_num)
theorem B2635733 : Blo 1756579 2635733 := bbase (se 7 (by rfl) ⟨30887, by rfl⟩ : syracuseStep 2635733 = 61775) (by norm_num)
theorem B3954653 : Blo 1756579 3954653 := bbase (se 3 (by rfl) ⟨741497, by rfl⟩ : syracuseStep 3954653 = 1482995) (by norm_num)
theorem B2635757 : Blo 1756579 2635757 := bbase (se 3 (by rfl) ⟨494204, by rfl⟩ : syracuseStep 2635757 = 988409) (by norm_num)
theorem B2635781 : Blo 1756579 2635781 := bbase (se 4 (by rfl) ⟨247104, by rfl⟩ : syracuseStep 2635781 = 494209) (by norm_num)
theorem B2635805 : Blo 1756579 2635805 := bbase (se 3 (by rfl) ⟨494213, by rfl⟩ : syracuseStep 2635805 = 988427) (by norm_num)
theorem B3954725 : Blo 1756579 3954725 := bbase (se 4 (by rfl) ⟨370755, by rfl⟩ : syracuseStep 3954725 = 741511) (by norm_num)
theorem B2635829 : Blo 1756579 2635829 := bbase (se 5 (by rfl) ⟨123554, by rfl⟩ : syracuseStep 2635829 = 247109) (by norm_num)
theorem B5003333 : Blo 1756579 5003333 := bbase (se 4 (by rfl) ⟨469062, by rfl⟩ : syracuseStep 5003333 = 938125) (by norm_num)
theorem B2635853 : Blo 1756579 2635853 := bbase (se 3 (by rfl) ⟨494222, by rfl⟩ : syracuseStep 2635853 = 988445) (by norm_num)
theorem B2635877 : Blo 1756579 2635877 := bbase (se 4 (by rfl) ⟨247113, by rfl⟩ : syracuseStep 2635877 = 494227) (by norm_num)
theorem B3954797 : Blo 1756579 3954797 := bbase (se 3 (by rfl) ⟨741524, by rfl⟩ : syracuseStep 3954797 = 1483049) (by norm_num)
theorem B2635901 : Blo 1756579 2635901 := bbase (se 3 (by rfl) ⟨494231, by rfl⟩ : syracuseStep 2635901 = 988463) (by norm_num)
theorem B8124565 : Blo 1756579 8124565 := bbase (se 6 (by rfl) ⟨190419, by rfl⟩ : syracuseStep 8124565 = 380839) (by norm_num)
theorem B2635925 : Blo 1756579 2635925 := bbase (se 6 (by rfl) ⟨61779, by rfl⟩ : syracuseStep 2635925 = 123559) (by norm_num)
theorem B4446373 : Blo 1756579 4446373 := bbase (se 4 (by rfl) ⟨416847, by rfl⟩ : syracuseStep 4446373 = 833695) (by norm_num)
theorem B2635949 : Blo 1756579 2635949 := bbase (se 3 (by rfl) ⟨494240, by rfl⟩ : syracuseStep 2635949 = 988481) (by norm_num)
theorem B3954869 : Blo 1756579 3954869 := bbase (se 5 (by rfl) ⟨185384, by rfl⟩ : syracuseStep 3954869 = 370769) (by norm_num)
theorem B2635973 : Blo 1756579 2635973 := bbase (se 4 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 2635973 = 494245) (by norm_num)
theorem B2635997 : Blo 1756579 2635997 := bbase (se 3 (by rfl) ⟨494249, by rfl⟩ : syracuseStep 2635997 = 988499) (by norm_num)
theorem B2636021 : Blo 1756579 2636021 := bbase (se 5 (by rfl) ⟨123563, by rfl⟩ : syracuseStep 2636021 = 247127) (by norm_num)
theorem B3954941 : Blo 1756579 3954941 := bbase (se 3 (by rfl) ⟨741551, by rfl⟩ : syracuseStep 3954941 = 1483103) (by norm_num)
theorem B2636045 : Blo 1756579 2636045 := bbase (se 3 (by rfl) ⟨494258, by rfl⟩ : syracuseStep 2636045 = 988517) (by norm_num)
theorem B4446485 : Blo 1756579 4446485 := bbase (se 6 (by rfl) ⟨104214, by rfl⟩ : syracuseStep 4446485 = 208429) (by norm_num)
theorem B5929253 : Blo 1756579 5929253 := bbase (se 4 (by rfl) ⟨555867, by rfl⟩ : syracuseStep 5929253 = 1111735) (by norm_num)
theorem B2636069 : Blo 1756579 2636069 := bbase (se 4 (by rfl) ⟨247131, by rfl⟩ : syracuseStep 2636069 = 494263) (by norm_num)
theorem B2636093 : Blo 1756579 2636093 := bbase (se 3 (by rfl) ⟨494267, by rfl⟩ : syracuseStep 2636093 = 988535) (by norm_num)
theorem B3561797 : Blo 1756579 3561797 := bbase (se 4 (by rfl) ⟨333918, by rfl⟩ : syracuseStep 3561797 = 667837) (by norm_num)
theorem B3955013 : Blo 1756579 3955013 := bbase (se 4 (by rfl) ⟨370782, by rfl⟩ : syracuseStep 3955013 = 741565) (by norm_num)
theorem B2636117 : Blo 1756579 2636117 := bbase (se 10 (by rfl) ⟨3861, by rfl⟩ : syracuseStep 2636117 = 7723) (by norm_num)
theorem B2636141 : Blo 1756579 2636141 := bbase (se 3 (by rfl) ⟨494276, by rfl⟩ : syracuseStep 2636141 = 988553) (by norm_num)
theorem B2636165 : Blo 1756579 2636165 := bbase (se 4 (by rfl) ⟨247140, by rfl⟩ : syracuseStep 2636165 = 494281) (by norm_num)
theorem B3955085 : Blo 1756579 3955085 := bbase (se 3 (by rfl) ⟨741578, by rfl⟩ : syracuseStep 3955085 = 1483157) (by norm_num)
theorem B2636189 : Blo 1756579 2636189 := bbase (se 3 (by rfl) ⟨494285, by rfl⟩ : syracuseStep 2636189 = 988571) (by norm_num)
theorem B2636213 : Blo 1756579 2636213 := bbase (se 5 (by rfl) ⟨123572, by rfl⟩ : syracuseStep 2636213 = 247145) (by norm_num)
theorem B8444357 : Blo 1756579 8444357 := bbase (se 4 (by rfl) ⟨791658, by rfl⟩ : syracuseStep 8444357 = 1583317) (by norm_num)
theorem B2636237 : Blo 1756579 2636237 := bbase (se 3 (by rfl) ⟨494294, by rfl⟩ : syracuseStep 2636237 = 988589) (by norm_num)
theorem B4446677 : Blo 1756579 4446677 := bbase (se 7 (by rfl) ⟨52109, by rfl⟩ : syracuseStep 4446677 = 104219) (by norm_num)
theorem B8894933 : Blo 1756579 8894933 := bbase (se 7 (by rfl) ⟨104237, by rfl⟩ : syracuseStep 8894933 = 208475) (by norm_num)
theorem B3955157 : Blo 1756579 3955157 := bbase (se 7 (by rfl) ⟨46349, by rfl⟩ : syracuseStep 3955157 = 92699) (by norm_num)
theorem B2636261 : Blo 1756579 2636261 := bbase (se 4 (by rfl) ⟨247149, by rfl⟩ : syracuseStep 2636261 = 494299) (by norm_num)
theorem B5003765 : Blo 1756579 5003765 := bbase (se 5 (by rfl) ⟨234551, by rfl⟩ : syracuseStep 5003765 = 469103) (by norm_num)
theorem B2636285 : Blo 1756579 2636285 := bbase (se 3 (by rfl) ⟨494303, by rfl⟩ : syracuseStep 2636285 = 988607) (by norm_num)
theorem B2636309 : Blo 1756579 2636309 := bbase (se 6 (by rfl) ⟨61788, by rfl⟩ : syracuseStep 2636309 = 123577) (by norm_num)
theorem B3955229 : Blo 1756579 3955229 := bbase (se 3 (by rfl) ⟨741605, by rfl⟩ : syracuseStep 3955229 = 1483211) (by norm_num)
theorem B2636333 : Blo 1756579 2636333 := bbase (se 3 (by rfl) ⟨494312, by rfl⟩ : syracuseStep 2636333 = 988625) (by norm_num)
theorem B2636357 : Blo 1756579 2636357 := bbase (se 4 (by rfl) ⟨247158, by rfl⟩ : syracuseStep 2636357 = 494317) (by norm_num)
theorem B2374229 : Blo 1756579 2374229 := bbase (se 8 (by rfl) ⟨13911, by rfl⟩ : syracuseStep 2374229 = 27823) (by norm_num)
theorem B20019797 : Blo 1756579 20019797 := bbase (se 8 (by rfl) ⟨117303, by rfl⟩ : syracuseStep 20019797 = 234607) (by norm_num)
theorem B2636381 : Blo 1756579 2636381 := bbase (se 3 (by rfl) ⟨494321, by rfl⟩ : syracuseStep 2636381 = 988643) (by norm_num)
theorem B3955301 : Blo 1756579 3955301 := bbase (se 4 (by rfl) ⟨370809, by rfl⟩ : syracuseStep 3955301 = 741619) (by norm_num)
theorem B2636405 : Blo 1756579 2636405 := bbase (se 5 (by rfl) ⟨123581, by rfl⟩ : syracuseStep 2636405 = 247163) (by norm_num)
theorem B2636429 : Blo 1756579 2636429 := bbase (se 3 (by rfl) ⟨494330, by rfl⟩ : syracuseStep 2636429 = 988661) (by norm_num)
theorem B2636453 : Blo 1756579 2636453 := bbase (se 4 (by rfl) ⟨247167, by rfl⟩ : syracuseStep 2636453 = 494335) (by norm_num)
theorem B3955373 : Blo 1756579 3955373 := bbase (se 3 (by rfl) ⟨741632, by rfl⟩ : syracuseStep 3955373 = 1483265) (by norm_num)
theorem B2636477 : Blo 1756579 2636477 := bbase (se 3 (by rfl) ⟨494339, by rfl⟩ : syracuseStep 2636477 = 988679) (by norm_num)
theorem B5929685 : Blo 1756579 5929685 := bbase (se 7 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 5929685 = 138977) (by norm_num)
theorem B2636501 : Blo 1756579 2636501 := bbase (se 7 (by rfl) ⟨30896, by rfl⟩ : syracuseStep 2636501 = 61793) (by norm_num)
theorem B3660517 : Blo 1756579 3660517 := bbase (se 4 (by rfl) ⟨343173, by rfl⟩ : syracuseStep 3660517 = 686347) (by norm_num)
theorem B2636525 : Blo 1756579 2636525 := bbase (se 3 (by rfl) ⟨494348, by rfl⟩ : syracuseStep 2636525 = 988697) (by norm_num)
theorem B15014645 : Blo 1756579 15014645 := bbase (se 5 (by rfl) ⟨703811, by rfl⟩ : syracuseStep 15014645 = 1407623) (by norm_num)
theorem B10148597 : Blo 1756579 10148597 := bbase (se 5 (by rfl) ⟨475715, by rfl⟩ : syracuseStep 10148597 = 951431) (by norm_num)
theorem B3955445 : Blo 1756579 3955445 := bbase (se 5 (by rfl) ⟨185411, by rfl⟩ : syracuseStep 3955445 = 370823) (by norm_num)
theorem B2636549 : Blo 1756579 2636549 := bbase (se 4 (by rfl) ⟨247176, by rfl⟩ : syracuseStep 2636549 = 494353) (by norm_num)
theorem B2636573 : Blo 1756579 2636573 := bbase (se 3 (by rfl) ⟨494357, by rfl⟩ : syracuseStep 2636573 = 988715) (by norm_num)
theorem B2964269 : Blo 1756579 2964269 := bbase (se 3 (by rfl) ⟨555800, by rfl⟩ : syracuseStep 2964269 = 1111601) (by norm_num)
theorem B4447021 : Blo 1756579 4447021 := bbase (se 3 (by rfl) ⟨833816, by rfl⟩ : syracuseStep 4447021 = 1667633) (by norm_num)
theorem B2374445 : Blo 1756579 2374445 := bbase (se 3 (by rfl) ⟨445208, by rfl⟩ : syracuseStep 2374445 = 890417) (by norm_num)
theorem B2636597 : Blo 1756579 2636597 := bbase (se 5 (by rfl) ⟨123590, by rfl⟩ : syracuseStep 2636597 = 247181) (by norm_num)
theorem B3955517 : Blo 1756579 3955517 := bbase (se 3 (by rfl) ⟨741659, by rfl⟩ : syracuseStep 3955517 = 1483319) (by norm_num)
theorem B2636621 : Blo 1756579 2636621 := bbase (se 3 (by rfl) ⟨494366, by rfl⟩ : syracuseStep 2636621 = 988733) (by norm_num)
theorem B2636645 : Blo 1756579 2636645 := bbase (se 4 (by rfl) ⟨247185, by rfl⟩ : syracuseStep 2636645 = 494371) (by norm_num)
theorem B2636669 : Blo 1756579 2636669 := bbase (se 3 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 2636669 = 988751) (by norm_num)
theorem B3955589 : Blo 1756579 3955589 := bbase (se 4 (by rfl) ⟨370836, by rfl⟩ : syracuseStep 3955589 = 741673) (by norm_num)
theorem B2636693 : Blo 1756579 2636693 := bbase (se 6 (by rfl) ⟨61797, by rfl⟩ : syracuseStep 2636693 = 123595) (by norm_num)
theorem B4447133 : Blo 1756579 4447133 := bbase (se 3 (by rfl) ⟨833837, by rfl⟩ : syracuseStep 4447133 = 1667675) (by norm_num)
theorem B2964397 : Blo 1756579 2964397 := bbase (se 3 (by rfl) ⟨555824, by rfl⟩ : syracuseStep 2964397 = 1111649) (by norm_num)
theorem B2636717 : Blo 1756579 2636717 := bbase (se 3 (by rfl) ⟨494384, by rfl⟩ : syracuseStep 2636717 = 988769) (by norm_num)
theorem B2636741 : Blo 1756579 2636741 := bbase (se 4 (by rfl) ⟨247194, by rfl⟩ : syracuseStep 2636741 = 494389) (by norm_num)
theorem B3955661 : Blo 1756579 3955661 := bbase (se 3 (by rfl) ⟨741686, by rfl⟩ : syracuseStep 3955661 = 1483373) (by norm_num)
theorem B2636765 : Blo 1756579 2636765 := bbase (se 3 (by rfl) ⟨494393, by rfl⟩ : syracuseStep 2636765 = 988787) (by norm_num)
theorem B2636789 : Blo 1756579 2636789 := bbase (se 5 (by rfl) ⟨123599, by rfl⟩ : syracuseStep 2636789 = 247199) (by norm_num)
theorem B2964485 : Blo 1756579 2964485 := bbase (se 4 (by rfl) ⟨277920, by rfl⟩ : syracuseStep 2964485 = 555841) (by norm_num)
theorem B2636813 : Blo 1756579 2636813 := bbase (se 3 (by rfl) ⟨494402, by rfl⟩ : syracuseStep 2636813 = 988805) (by norm_num)
theorem B2636837 : Blo 1756579 2636837 := bbase (se 4 (by rfl) ⟨247203, by rfl⟩ : syracuseStep 2636837 = 494407) (by norm_num)
theorem B2636861 : Blo 1756579 2636861 := bbase (se 3 (by rfl) ⟨494411, by rfl⟩ : syracuseStep 2636861 = 988823) (by norm_num)
theorem B24042581 : Blo 1756579 24042581 := bbase (se 8 (by rfl) ⟨140874, by rfl⟩ : syracuseStep 24042581 = 281749) (by norm_num)
theorem B2636885 : Blo 1756579 2636885 := bbase (se 8 (by rfl) ⟨15450, by rfl⟩ : syracuseStep 2636885 = 30901) (by norm_num)
theorem B4447325 : Blo 1756579 4447325 := bbase (se 3 (by rfl) ⟨833873, by rfl⟩ : syracuseStep 4447325 = 1667747) (by norm_num)
theorem B2636909 : Blo 1756579 2636909 := bbase (se 3 (by rfl) ⟨494420, by rfl⟩ : syracuseStep 2636909 = 988841) (by norm_num)
theorem B2964613 : Blo 1756579 2964613 := bbase (se 4 (by rfl) ⟨277932, by rfl⟩ : syracuseStep 2964613 = 555865) (by norm_num)
theorem B5930117 : Blo 1756579 5930117 := bbase (se 4 (by rfl) ⟨555948, by rfl⟩ : syracuseStep 5930117 = 1111897) (by norm_num)
theorem B2636933 : Blo 1756579 2636933 := bbase (se 4 (by rfl) ⟨247212, by rfl⟩ : syracuseStep 2636933 = 494425) (by norm_num)
theorem B2636957 : Blo 1756579 2636957 := bbase (se 3 (by rfl) ⟨494429, by rfl⟩ : syracuseStep 2636957 = 988859) (by norm_num)
theorem B2636981 : Blo 1756579 2636981 := bbase (se 5 (by rfl) ⟨123608, by rfl⟩ : syracuseStep 2636981 = 247217) (by norm_num)
theorem B2170037 : Blo 1756579 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B2637005 : Blo 1756579 2637005 := bbase (se 3 (by rfl) ⟨494438, by rfl⟩ : syracuseStep 2637005 = 988877) (by norm_num)
theorem B2964701 : Blo 1756579 2964701 := bbase (se 3 (by rfl) ⟨555881, by rfl⟩ : syracuseStep 2964701 = 1111763) (by norm_num)
theorem B5004517 : Blo 1756579 5004517 := bbase (se 4 (by rfl) ⟨469173, by rfl⟩ : syracuseStep 5004517 = 938347) (by norm_num)
theorem B2637029 : Blo 1756579 2637029 := bbase (se 4 (by rfl) ⟨247221, by rfl⟩ : syracuseStep 2637029 = 494443) (by norm_num)
theorem B2637053 : Blo 1756579 2637053 := bbase (se 3 (by rfl) ⟨494447, by rfl⟩ : syracuseStep 2637053 = 988895) (by norm_num)
theorem B2637077 : Blo 1756579 2637077 := bbase (se 6 (by rfl) ⟨61806, by rfl⟩ : syracuseStep 2637077 = 123613) (by norm_num)
theorem B2637101 : Blo 1756579 2637101 := bbase (se 3 (by rfl) ⟨494456, by rfl⟩ : syracuseStep 2637101 = 988913) (by norm_num)
theorem B2964829 : Blo 1756579 2964829 := bbase (se 3 (by rfl) ⟨555905, by rfl⟩ : syracuseStep 2964829 = 1111811) (by norm_num)
theorem B2375029 : Blo 1756579 2375029 := bbase (se 5 (by rfl) ⟨111329, by rfl⟩ : syracuseStep 2375029 = 222659) (by norm_num)
theorem B2030977 : Blo 1756579 2030977 := bbase (se 2 (by rfl) ⟨761616, by rfl⟩ : syracuseStep 2030977 = 1523233) (by norm_num)
theorem B16883093 : Blo 1756579 16883093 := bbase (se 6 (by rfl) ⟨395697, by rfl⟩ : syracuseStep 16883093 = 791395) (by norm_num)
theorem B2964917 : Blo 1756579 2964917 := bbase (se 5 (by rfl) ⟨138980, by rfl⟩ : syracuseStep 2964917 = 277961) (by norm_num)
theorem B4447669 : Blo 1756579 4447669 := bbase (se 5 (by rfl) ⟨208484, by rfl⟩ : syracuseStep 4447669 = 416969) (by norm_num)
theorem B11263445 : Blo 1756579 11263445 := bbase (se 7 (by rfl) ⟨131993, by rfl⟩ : syracuseStep 11263445 = 263987) (by norm_num)
theorem B4447781 : Blo 1756579 4447781 := bbase (se 4 (by rfl) ⟨416979, by rfl⟩ : syracuseStep 4447781 = 833959) (by norm_num)
theorem B2965045 : Blo 1756579 2965045 := bbase (se 5 (by rfl) ⟨138986, by rfl⟩ : syracuseStep 2965045 = 277973) (by norm_num)
theorem B5930549 : Blo 1756579 5930549 := bbase (se 5 (by rfl) ⟨277994, by rfl⟩ : syracuseStep 5930549 = 555989) (by norm_num)
theorem B7126613 : Blo 1756579 7126613 := bbase (se 8 (by rfl) ⟨41757, by rfl⟩ : syracuseStep 7126613 = 83515) (by norm_num)
theorem B7503461 : Blo 1756579 7503461 := bbase (se 4 (by rfl) ⟨703449, by rfl⟩ : syracuseStep 7503461 = 1406899) (by norm_num)
theorem B2965133 : Blo 1756579 2965133 := bbase (se 3 (by rfl) ⟨555962, by rfl⟩ : syracuseStep 2965133 = 1111925) (by norm_num)
theorem B4447973 : Blo 1756579 4447973 := bbase (se 4 (by rfl) ⟨416997, by rfl⟩ : syracuseStep 4447973 = 833995) (by norm_num)
theorem B8896229 : Blo 1756579 8896229 := bbase (se 4 (by rfl) ⟨834021, by rfl⟩ : syracuseStep 8896229 = 1668043) (by norm_num)
theorem B2965261 : Blo 1756579 2965261 := bbase (se 3 (by rfl) ⟨555986, by rfl⟩ : syracuseStep 2965261 = 1111973) (by norm_num)
theorem B2285329 : Blo 1756579 2285329 := bbase (se 2 (by rfl) ⟨856998, by rfl⟩ : syracuseStep 2285329 = 1713997) (by norm_num)
theorem B2965349 : Blo 1756579 2965349 := bbase (se 4 (by rfl) ⟨278001, by rfl⟩ : syracuseStep 2965349 = 556003) (by norm_num)
theorem B3563453 : Blo 1756579 3563453 := bbase (se 3 (by rfl) ⟨668147, by rfl⟩ : syracuseStep 3563453 = 1336295) (by norm_num)
theorem B2965477 : Blo 1756579 2965477 := bbase (se 4 (by rfl) ⟨278013, by rfl⟩ : syracuseStep 2965477 = 556027) (by norm_num)
theorem B5930981 : Blo 1756579 5930981 := bbase (se 4 (by rfl) ⟨556029, by rfl⟩ : syracuseStep 5930981 = 1112059) (by norm_num)
theorem B9142307 : Blo 1756579 9142307 := bstep (se 1 (by rfl) ⟨6856730, by rfl⟩ : syracuseStep 9142307 = 13713461) B13713461
theorem B1876019 : Blo 1756579 1876019 := bstep (se 1 (by rfl) ⟨1407014, by rfl⟩ : syracuseStep 1876019 = 2814029) B2814029
theorem B5931089 : Blo 1756579 5931089 := bstep (se 2 (by rfl) ⟨2224158, by rfl⟩ : syracuseStep 5931089 = 4448317) B4448317
theorem B2965585 : Blo 1756579 2965585 := bstep (se 2 (by rfl) ⟨1112094, by rfl⟩ : syracuseStep 2965585 = 2224189) B2224189
theorem B2965619 : Blo 1756579 2965619 := bstep (se 1 (by rfl) ⟨2224214, by rfl⟩ : syracuseStep 2965619 = 4448429) B4448429
theorem B2965747 : Blo 1756579 2965747 := bstep (se 1 (by rfl) ⟨2224310, by rfl⟩ : syracuseStep 2965747 = 4448621) B4448621
theorem B2965889 : Blo 1756579 2965889 := bstep (se 2 (by rfl) ⟨1112208, by rfl⟩ : syracuseStep 2965889 = 2224417) B2224417
theorem B3563939 : Blo 1756579 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B4448753 : Blo 1756579 4448753 := bstep (se 2 (by rfl) ⟨1668282, by rfl⟩ : syracuseStep 4448753 = 3336565) B3336565
theorem B2966017 : Blo 1756579 2966017 := bstep (se 2 (by rfl) ⟨1112256, by rfl⟩ : syracuseStep 2966017 = 2224513) B2224513
theorem B4448803 : Blo 1756579 4448803 := bstep (se 1 (by rfl) ⟨3336602, by rfl⟩ : syracuseStep 4448803 = 6673205) B6673205
theorem B2966051 : Blo 1756579 2966051 := bstep (se 1 (by rfl) ⟨2224538, by rfl⟩ : syracuseStep 2966051 = 4449077) B4449077
theorem B5931629 : Blo 1756579 5931629 := bstep (se 3 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 5931629 = 2224361) B2224361
theorem B5931683 : Blo 1756579 5931683 := bstep (se 1 (by rfl) ⟨4448762, by rfl⟩ : syracuseStep 5931683 = 8897525) B8897525
theorem B2966179 : Blo 1756579 2966179 := bstep (se 1 (by rfl) ⟨2224634, by rfl⟩ : syracuseStep 2966179 = 4449269) B4449269
theorem B8897201 : Blo 1756579 8897201 := bstep (se 2 (by rfl) ⟨3336450, by rfl⟩ : syracuseStep 8897201 = 6672901) B6672901
theorem B4448945 : Blo 1756579 4448945 := bstep (se 2 (by rfl) ⟨1668354, by rfl⟩ : syracuseStep 4448945 = 3336709) B3336709
theorem B24052421 : Blo 1756579 24052421 := bstep (se 4 (by rfl) ⟨2254914, by rfl⟩ : syracuseStep 24052421 = 4509829) B4509829
theorem B7504589 : Blo 1756579 7504589 := bstep (se 3 (by rfl) ⟨1407110, by rfl⟩ : syracuseStep 7504589 = 2814221) B2814221
theorem B5006033 : Blo 1756579 5006033 := bstep (se 2 (by rfl) ⟨1877262, by rfl⟩ : syracuseStep 5006033 = 3754525) B3754525
theorem B1876771 : Blo 1756579 1876771 := bstep (se 1 (by rfl) ⟨1407578, by rfl⟩ : syracuseStep 1876771 = 2815157) B2815157
theorem B2966321 : Blo 1756579 2966321 := bstep (se 2 (by rfl) ⟨1112370, by rfl⟩ : syracuseStep 2966321 = 2224741) B2224741
theorem B2671489 : Blo 1756579 2671489 := bstep (se 2 (by rfl) ⟨1001808, by rfl⟩ : syracuseStep 2671489 = 2003617) B2003617
theorem B20013965 : Blo 1756579 20013965 := bstep (se 3 (by rfl) ⟨3752618, by rfl⟩ : syracuseStep 20013965 = 7505237) B7505237
theorem B5006225 : Blo 1756579 5006225 := bstep (se 2 (by rfl) ⟨1877334, by rfl⟩ : syracuseStep 5006225 = 3754669) B3754669
theorem B5931953 : Blo 1756579 5931953 := bstep (se 2 (by rfl) ⟨2224482, by rfl⟩ : syracuseStep 5931953 = 4448965) B4448965
theorem B2966449 : Blo 1756579 2966449 := bstep (se 2 (by rfl) ⟨1112418, by rfl⟩ : syracuseStep 2966449 = 2224837) B2224837
theorem B3335107 : Blo 1756579 3335107 := bstep (se 1 (by rfl) ⟨2501330, by rfl⟩ : syracuseStep 3335107 = 5002661) B5002661
theorem B2966483 : Blo 1756579 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B18039779 : Blo 1756579 18039779 := bstep (se 1 (by rfl) ⟨13529834, by rfl⟩ : syracuseStep 18039779 = 27059669) B27059669
theorem B3752995 : Blo 1756579 3752995 := bstep (se 1 (by rfl) ⟨2814746, by rfl⟩ : syracuseStep 3752995 = 5629493) B5629493
theorem B1877027 : Blo 1756579 1877027 := bstep (se 1 (by rfl) ⟨1407770, by rfl⟩ : syracuseStep 1877027 = 2815541) B2815541
theorem B2966611 : Blo 1756579 2966611 := bstep (se 1 (by rfl) ⟨2224958, by rfl⟩ : syracuseStep 2966611 = 4449917) B4449917
theorem B19522757 : Blo 1756579 19522757 := bstep (se 4 (by rfl) ⟨1830258, by rfl⟩ : syracuseStep 19522757 = 3660517) B3660517
theorem B5629133 : Blo 1756579 5629133 := bstep (se 3 (by rfl) ⟨1055462, by rfl⟩ : syracuseStep 5629133 = 2110925) B2110925
theorem B2966753 : Blo 1756579 2966753 := bstep (se 2 (by rfl) ⟨1112532, by rfl⟩ : syracuseStep 2966753 = 2225065) B2225065
theorem B3335555 : Blo 1756579 3335555 := bstep (se 1 (by rfl) ⟨2501666, by rfl⟩ : syracuseStep 3335555 = 5003333) B5003333
theorem B6669773 : Blo 1756579 6669773 := bstep (se 3 (by rfl) ⟨1250582, by rfl⟩ : syracuseStep 6669773 = 2501165) B2501165
theorem B5932493 : Blo 1756579 5932493 := bstep (se 3 (by rfl) ⟨1112342, by rfl⟩ : syracuseStep 5932493 = 2224685) B2224685
theorem B5932547 : Blo 1756579 5932547 := bstep (se 1 (by rfl) ⟨4449410, by rfl⟩ : syracuseStep 5932547 = 8898821) B8898821
theorem B5629571 : Blo 1756579 5629571 := bstep (se 1 (by rfl) ⟨4222178, by rfl⟩ : syracuseStep 5629571 = 8444357) B8444357
theorem B4449937 : Blo 1756579 4449937 := bstep (se 2 (by rfl) ⟨1668726, by rfl⟩ : syracuseStep 4449937 = 3337453) B3337453
theorem B3335843 : Blo 1756579 3335843 := bstep (se 1 (by rfl) ⟨2501882, by rfl⟩ : syracuseStep 3335843 = 5003765) B5003765
theorem B13346531 : Blo 1756579 13346531 := bstep (se 1 (by rfl) ⟨10009898, by rfl⟩ : syracuseStep 13346531 = 20019797) B20019797
theorem B5932817 : Blo 1756579 5932817 := bstep (se 2 (by rfl) ⟨2224806, by rfl⟩ : syracuseStep 5932817 = 4449613) B4449613
theorem B1976179 : Blo 1756579 1976179 := bstep (se 1 (by rfl) ⟨1482134, by rfl⟩ : syracuseStep 1976179 = 2964269) B2964269
theorem B7505905 : Blo 1756579 7505905 := bstep (se 2 (by rfl) ⟨2814714, by rfl⟩ : syracuseStep 7505905 = 5629429) B5629429
theorem B1976323 : Blo 1756579 1976323 := bstep (se 1 (by rfl) ⟨1482242, by rfl⟩ : syracuseStep 1976323 = 2964485) B2964485
theorem B10831877 : Blo 1756579 10831877 := bstep (se 4 (by rfl) ⟨1015488, by rfl⟩ : syracuseStep 10831877 = 2030977) B2030977
theorem B2672657 : Blo 1756579 2672657 := bstep (se 2 (by rfl) ⟨1002246, by rfl⟩ : syracuseStep 2672657 = 2004493) B2004493
theorem B8898659 : Blo 1756579 8898659 := bstep (se 1 (by rfl) ⟨6673994, by rfl⟩ : syracuseStep 8898659 = 13347989) B13347989
theorem B1976467 : Blo 1756579 1976467 := bstep (se 1 (by rfl) ⟨1482350, by rfl⟩ : syracuseStep 1976467 = 2964701) B2964701
theorem B2672833 : Blo 1756579 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B3754225 : Blo 1756579 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B1976611 : Blo 1756579 1976611 := bstep (se 1 (by rfl) ⟨1482458, by rfl⟩ : syracuseStep 1976611 = 2964917) B2964917
theorem B5933357 : Blo 1756579 5933357 := bstep (se 3 (by rfl) ⟨1112504, by rfl⟩ : syracuseStep 5933357 = 2225009) B2225009
theorem B5933411 : Blo 1756579 5933411 := bstep (se 1 (by rfl) ⟨4450058, by rfl⟩ : syracuseStep 5933411 = 8900117) B8900117
theorem B1976755 : Blo 1756579 1976755 := bstep (se 1 (by rfl) ⟨1482566, by rfl⟩ : syracuseStep 1976755 = 2965133) B2965133
theorem B1976899 : Blo 1756579 1976899 := bstep (se 1 (by rfl) ⟨1482674, by rfl⟩ : syracuseStep 1976899 = 2965349) B2965349
theorem B3336785 : Blo 1756579 3336785 := bstep (se 2 (by rfl) ⟨1251294, by rfl⟩ : syracuseStep 3336785 = 2502589) B2502589
theorem B1977043 : Blo 1756579 1977043 := bstep (se 1 (by rfl) ⟨1482782, by rfl⟩ : syracuseStep 1977043 = 2965565) B2965565
theorem B1977187 : Blo 1756579 1977187 := bstep (se 1 (by rfl) ⟨1482890, by rfl⟩ : syracuseStep 1977187 = 2965781) B2965781
theorem B10832753 : Blo 1756579 10832753 := bstep (se 2 (by rfl) ⟨4062282, by rfl⟩ : syracuseStep 10832753 = 8124565) B8124565
theorem B10005389 : Blo 1756579 10005389 := bstep (se 3 (by rfl) ⟨1876010, by rfl⟩ : syracuseStep 10005389 = 3752021) B3752021
theorem B6761357 : Blo 1756579 6761357 := bstep (se 3 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 6761357 = 2535509) B2535509
theorem B8899469 : Blo 1756579 8899469 := bstep (se 3 (by rfl) ⟨1668650, by rfl⟩ : syracuseStep 8899469 = 3337301) B3337301
theorem B6335459 : Blo 1756579 6335459 := bstep (se 1 (by rfl) ⟨4751594, by rfl⟩ : syracuseStep 6335459 = 9503189) B9503189
theorem B1977331 : Blo 1756579 1977331 := bstep (se 1 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 1977331 = 2965997) B2965997
theorem B1977475 : Blo 1756579 1977475 := bstep (se 1 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 1977475 = 2966213) B2966213
theorem B5786765 : Blo 1756579 5786765 := bstep (se 3 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 5786765 = 2170037) B2170037
theorem B2223283 : Blo 1756579 2223283 := bstep (se 1 (by rfl) ⟨1667462, by rfl⟩ : syracuseStep 2223283 = 3334925) B3334925
theorem B2223379 : Blo 1756579 2223379 := bstep (se 1 (by rfl) ⟨1667534, by rfl⟩ : syracuseStep 2223379 = 3335069) B3335069
theorem B1977619 : Blo 1756579 1977619 := bstep (se 1 (by rfl) ⟨1483214, by rfl⟩ : syracuseStep 1977619 = 2966429) B2966429
theorem B2501923 : Blo 1756579 2501923 := bstep (se 1 (by rfl) ⟨1876442, by rfl⟩ : syracuseStep 2501923 = 3752885) B3752885
theorem B2502019 : Blo 1756579 2502019 := bstep (se 1 (by rfl) ⟨1876514, by rfl⟩ : syracuseStep 2502019 = 3753029) B3753029
theorem B11259269 : Blo 1756579 11259269 := bstep (se 4 (by rfl) ⟨1055556, by rfl⟩ : syracuseStep 11259269 = 2111113) B2111113
theorem B1756579 : Blo 1756579 1756579 := bstep (se 1 (by rfl) ⟨1317434, by rfl⟩ : syracuseStep 1756579 = 2634869) B2634869
theorem B1977763 : Blo 1756579 1977763 := bstep (se 1 (by rfl) ⟨1483322, by rfl⟩ : syracuseStep 1977763 = 2966645) B2966645
theorem B1756595 : Blo 1756579 1756595 := bstep (se 1 (by rfl) ⟨1317446, by rfl⟩ : syracuseStep 1756595 = 2634893) B2634893
theorem B1756611 : Blo 1756579 1756611 := bstep (se 1 (by rfl) ⟨1317458, by rfl⟩ : syracuseStep 1756611 = 2634917) B2634917
theorem B1756627 : Blo 1756579 1756627 := bstep (se 1 (by rfl) ⟨1317470, by rfl⟩ : syracuseStep 1756627 = 2634941) B2634941
theorem B1756643 : Blo 1756579 1756643 := bstep (se 1 (by rfl) ⟨1317482, by rfl⟩ : syracuseStep 1756643 = 2634965) B2634965
theorem B10284529 : Blo 1756579 10284529 := bstep (se 2 (by rfl) ⟨3856698, by rfl⟩ : syracuseStep 10284529 = 7713397) B7713397
theorem B1756659 : Blo 1756579 1756659 := bstep (se 1 (by rfl) ⟨1317494, by rfl⟩ : syracuseStep 1756659 = 2634989) B2634989
theorem B1756675 : Blo 1756579 1756675 := bstep (se 1 (by rfl) ⟨1317506, by rfl⟩ : syracuseStep 1756675 = 2635013) B2635013
theorem B5631491 : Blo 1756579 5631491 := bstep (se 1 (by rfl) ⟨4223618, by rfl⟩ : syracuseStep 5631491 = 8447237) B8447237
theorem B1756691 : Blo 1756579 1756691 := bstep (se 1 (by rfl) ⟨1317518, by rfl⟩ : syracuseStep 1756691 = 2635037) B2635037
theorem B1756707 : Blo 1756579 1756707 := bstep (se 1 (by rfl) ⟨1317530, by rfl⟩ : syracuseStep 1756707 = 2635061) B2635061
theorem B1756723 : Blo 1756579 1756723 := bstep (se 1 (by rfl) ⟨1317542, by rfl⟩ : syracuseStep 1756723 = 2635085) B2635085
theorem B1756739 : Blo 1756579 1756739 := bstep (se 1 (by rfl) ⟨1317554, by rfl⟩ : syracuseStep 1756739 = 2635109) B2635109
theorem B1756755 : Blo 1756579 1756755 := bstep (se 1 (by rfl) ⟨1317566, by rfl⟩ : syracuseStep 1756755 = 2635133) B2635133
theorem B1756771 : Blo 1756579 1756771 := bstep (se 1 (by rfl) ⟨1317578, by rfl⟩ : syracuseStep 1756771 = 2635157) B2635157
theorem B1756787 : Blo 1756579 1756787 := bstep (se 1 (by rfl) ⟨1317590, by rfl⟩ : syracuseStep 1756787 = 2635181) B2635181
theorem B1756803 : Blo 1756579 1756803 := bstep (se 1 (by rfl) ⟨1317602, by rfl⟩ : syracuseStep 1756803 = 2635205) B2635205
theorem B1756819 : Blo 1756579 1756819 := bstep (se 1 (by rfl) ⟨1317614, by rfl⟩ : syracuseStep 1756819 = 2635229) B2635229
theorem B1756835 : Blo 1756579 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B1756851 : Blo 1756579 1756851 := bstep (se 1 (by rfl) ⟨1317638, by rfl⟩ : syracuseStep 1756851 = 2635277) B2635277
theorem B1756867 : Blo 1756579 1756867 := bstep (se 1 (by rfl) ⟨1317650, by rfl⟩ : syracuseStep 1756867 = 2635301) B2635301
theorem B1756883 : Blo 1756579 1756883 := bstep (se 1 (by rfl) ⟨1317662, by rfl⟩ : syracuseStep 1756883 = 2635325) B2635325
theorem B1756899 : Blo 1756579 1756899 := bstep (se 1 (by rfl) ⟨1317674, by rfl⟩ : syracuseStep 1756899 = 2635349) B2635349
theorem B20016881 : Blo 1756579 20016881 := bstep (se 2 (by rfl) ⟨7506330, by rfl⟩ : syracuseStep 20016881 = 15012661) B15012661
theorem B1756915 : Blo 1756579 1756915 := bstep (se 1 (by rfl) ⟨1317686, by rfl⟩ : syracuseStep 1756915 = 2635373) B2635373
theorem B1756931 : Blo 1756579 1756931 := bstep (se 1 (by rfl) ⟨1317698, by rfl⟩ : syracuseStep 1756931 = 2635397) B2635397
theorem B2223875 : Blo 1756579 2223875 := bstep (se 1 (by rfl) ⟨1667906, by rfl⟩ : syracuseStep 2223875 = 3335813) B3335813
theorem B1756947 : Blo 1756579 1756947 := bstep (se 1 (by rfl) ⟨1317710, by rfl⟩ : syracuseStep 1756947 = 2635421) B2635421
theorem B1756963 : Blo 1756579 1756963 := bstep (se 1 (by rfl) ⟨1317722, by rfl⟩ : syracuseStep 1756963 = 2635445) B2635445
theorem B1756979 : Blo 1756579 1756979 := bstep (se 1 (by rfl) ⟨1317734, by rfl⟩ : syracuseStep 1756979 = 2635469) B2635469
theorem B1756995 : Blo 1756579 1756995 := bstep (se 1 (by rfl) ⟨1317746, by rfl⟩ : syracuseStep 1756995 = 2635493) B2635493
theorem B1757011 : Blo 1756579 1757011 := bstep (se 1 (by rfl) ⟨1317758, by rfl⟩ : syracuseStep 1757011 = 2635517) B2635517
theorem B1757027 : Blo 1756579 1757027 := bstep (se 1 (by rfl) ⟨1317770, by rfl⟩ : syracuseStep 1757027 = 2635541) B2635541
theorem B1757043 : Blo 1756579 1757043 := bstep (se 1 (by rfl) ⟨1317782, by rfl⟩ : syracuseStep 1757043 = 2635565) B2635565
theorem B2502515 : Blo 1756579 2502515 := bstep (se 1 (by rfl) ⟨1876886, by rfl⟩ : syracuseStep 2502515 = 3753773) B3753773
theorem B1757059 : Blo 1756579 1757059 := bstep (se 1 (by rfl) ⟨1317794, by rfl⟩ : syracuseStep 1757059 = 2635589) B2635589
theorem B3952529 : Blo 1756579 3952529 := bstep (se 2 (by rfl) ⟨1482198, by rfl⟩ : syracuseStep 3952529 = 2964397) B2964397
theorem B1757075 : Blo 1756579 1757075 := bstep (se 1 (by rfl) ⟨1317806, by rfl⟩ : syracuseStep 1757075 = 2635613) B2635613
theorem B3952547 : Blo 1756579 3952547 := bstep (se 1 (by rfl) ⟨2964410, by rfl⟩ : syracuseStep 3952547 = 5928821) B5928821
theorem B1757091 : Blo 1756579 1757091 := bstep (se 1 (by rfl) ⟨1317818, by rfl⟩ : syracuseStep 1757091 = 2635637) B2635637
theorem B1757107 : Blo 1756579 1757107 := bstep (se 1 (by rfl) ⟨1317830, by rfl⟩ : syracuseStep 1757107 = 2635661) B2635661
theorem B1953715 : Blo 1756579 1953715 := bstep (se 1 (by rfl) ⟨1465286, by rfl⟩ : syracuseStep 1953715 = 2930573) B2930573
theorem B1757123 : Blo 1756579 1757123 := bstep (se 1 (by rfl) ⟨1317842, by rfl⟩ : syracuseStep 1757123 = 2635685) B2635685
theorem B1757139 : Blo 1756579 1757139 := bstep (se 1 (by rfl) ⟨1317854, by rfl⟩ : syracuseStep 1757139 = 2635709) B2635709
theorem B1757155 : Blo 1756579 1757155 := bstep (se 1 (by rfl) ⟨1317866, by rfl⟩ : syracuseStep 1757155 = 2635733) B2635733
theorem B1757171 : Blo 1756579 1757171 := bstep (se 1 (by rfl) ⟨1317878, by rfl⟩ : syracuseStep 1757171 = 2635757) B2635757
theorem B1757187 : Blo 1756579 1757187 := bstep (se 1 (by rfl) ⟨1317890, by rfl⟩ : syracuseStep 1757187 = 2635781) B2635781
theorem B1757203 : Blo 1756579 1757203 := bstep (se 1 (by rfl) ⟨1317902, by rfl⟩ : syracuseStep 1757203 = 2635805) B2635805
theorem B1757219 : Blo 1756579 1757219 := bstep (se 1 (by rfl) ⟨1317914, by rfl⟩ : syracuseStep 1757219 = 2635829) B2635829
theorem B1757235 : Blo 1756579 1757235 := bstep (se 1 (by rfl) ⟨1317926, by rfl⟩ : syracuseStep 1757235 = 2635853) B2635853
theorem B1757251 : Blo 1756579 1757251 := bstep (se 1 (by rfl) ⟨1317938, by rfl⟩ : syracuseStep 1757251 = 2635877) B2635877
theorem B1757267 : Blo 1756579 1757267 := bstep (se 1 (by rfl) ⟨1317950, by rfl⟩ : syracuseStep 1757267 = 2635901) B2635901
theorem B1757283 : Blo 1756579 1757283 := bstep (se 1 (by rfl) ⟨1317962, by rfl⟩ : syracuseStep 1757283 = 2635925) B2635925
theorem B1757299 : Blo 1756579 1757299 := bstep (se 1 (by rfl) ⟨1317974, by rfl⟩ : syracuseStep 1757299 = 2635949) B2635949
theorem B1757315 : Blo 1756579 1757315 := bstep (se 1 (by rfl) ⟨1317986, by rfl⟩ : syracuseStep 1757315 = 2635973) B2635973
theorem B1757331 : Blo 1756579 1757331 := bstep (se 1 (by rfl) ⟨1317998, by rfl⟩ : syracuseStep 1757331 = 2635997) B2635997
theorem B1757347 : Blo 1756579 1757347 := bstep (se 1 (by rfl) ⟨1318010, by rfl⟩ : syracuseStep 1757347 = 2636021) B2636021
theorem B3952817 : Blo 1756579 3952817 := bstep (se 2 (by rfl) ⟨1482306, by rfl⟩ : syracuseStep 3952817 = 2964613) B2964613
theorem B1757363 : Blo 1756579 1757363 := bstep (se 1 (by rfl) ⟨1318022, by rfl⟩ : syracuseStep 1757363 = 2636045) B2636045
theorem B3952835 : Blo 1756579 3952835 := bstep (se 1 (by rfl) ⟨2964626, by rfl⟩ : syracuseStep 3952835 = 5929253) B5929253
theorem B1757379 : Blo 1756579 1757379 := bstep (se 1 (by rfl) ⟨1318034, by rfl⟩ : syracuseStep 1757379 = 2636069) B2636069
theorem B1757395 : Blo 1756579 1757395 := bstep (se 1 (by rfl) ⟨1318046, by rfl⟩ : syracuseStep 1757395 = 2636093) B2636093
theorem B1757411 : Blo 1756579 1757411 := bstep (se 1 (by rfl) ⟨1318058, by rfl⟩ : syracuseStep 1757411 = 2636117) B2636117
theorem B1757427 : Blo 1756579 1757427 := bstep (se 1 (by rfl) ⟨1318070, by rfl⟩ : syracuseStep 1757427 = 2636141) B2636141
theorem B1757443 : Blo 1756579 1757443 := bstep (se 1 (by rfl) ⟨1318082, by rfl⟩ : syracuseStep 1757443 = 2636165) B2636165
theorem B1757459 : Blo 1756579 1757459 := bstep (se 1 (by rfl) ⟨1318094, by rfl⟩ : syracuseStep 1757459 = 2636189) B2636189
theorem B1757475 : Blo 1756579 1757475 := bstep (se 1 (by rfl) ⟨1318106, by rfl⟩ : syracuseStep 1757475 = 2636213) B2636213
theorem B6672689 : Blo 1756579 6672689 := bstep (se 2 (by rfl) ⟨2502258, by rfl⟩ : syracuseStep 6672689 = 5004517) B5004517
theorem B1757491 : Blo 1756579 1757491 := bstep (se 1 (by rfl) ⟨1318118, by rfl⟩ : syracuseStep 1757491 = 2636237) B2636237
theorem B1757507 : Blo 1756579 1757507 := bstep (se 1 (by rfl) ⟨1318130, by rfl⟩ : syracuseStep 1757507 = 2636261) B2636261
theorem B1757523 : Blo 1756579 1757523 := bstep (se 1 (by rfl) ⟨1318142, by rfl⟩ : syracuseStep 1757523 = 2636285) B2636285
theorem B1757539 : Blo 1756579 1757539 := bstep (se 1 (by rfl) ⟨1318154, by rfl⟩ : syracuseStep 1757539 = 2636309) B2636309
theorem B1757555 : Blo 1756579 1757555 := bstep (se 1 (by rfl) ⟨1318166, by rfl⟩ : syracuseStep 1757555 = 2636333) B2636333
theorem B1757571 : Blo 1756579 1757571 := bstep (se 1 (by rfl) ⟨1318178, by rfl⟩ : syracuseStep 1757571 = 2636357) B2636357
theorem B16896397 : Blo 1756579 16896397 := bstep (se 3 (by rfl) ⟨3168074, by rfl⟩ : syracuseStep 16896397 = 6336149) B6336149
theorem B1757587 : Blo 1756579 1757587 := bstep (se 1 (by rfl) ⟨1318190, by rfl⟩ : syracuseStep 1757587 = 2636381) B2636381
theorem B1757603 : Blo 1756579 1757603 := bstep (se 1 (by rfl) ⟨1318202, by rfl⟩ : syracuseStep 1757603 = 2636405) B2636405
theorem B7606705 : Blo 1756579 7606705 := bstep (se 2 (by rfl) ⟨2852514, by rfl⟩ : syracuseStep 7606705 = 5705029) B5705029
theorem B1757619 : Blo 1756579 1757619 := bstep (se 1 (by rfl) ⟨1318214, by rfl⟩ : syracuseStep 1757619 = 2636429) B2636429
theorem B1757635 : Blo 1756579 1757635 := bstep (se 1 (by rfl) ⟨1318226, by rfl⟩ : syracuseStep 1757635 = 2636453) B2636453
theorem B2224579 : Blo 1756579 2224579 := bstep (se 1 (by rfl) ⟨1668434, by rfl⟩ : syracuseStep 2224579 = 3336869) B3336869
theorem B3953105 : Blo 1756579 3953105 := bstep (se 2 (by rfl) ⟨1482414, by rfl⟩ : syracuseStep 3953105 = 2964829) B2964829
theorem B1757651 : Blo 1756579 1757651 := bstep (se 1 (by rfl) ⟨1318238, by rfl⟩ : syracuseStep 1757651 = 2636477) B2636477
theorem B3953123 : Blo 1756579 3953123 := bstep (se 1 (by rfl) ⟨2964842, by rfl⟩ : syracuseStep 3953123 = 5929685) B5929685
theorem B1757667 : Blo 1756579 1757667 := bstep (se 1 (by rfl) ⟨1318250, by rfl⟩ : syracuseStep 1757667 = 2636501) B2636501
theorem B3166705 : Blo 1756579 3166705 := bstep (se 2 (by rfl) ⟨1187514, by rfl⟩ : syracuseStep 3166705 = 2375029) B2375029
theorem B2503153 : Blo 1756579 2503153 := bstep (se 2 (by rfl) ⟨938682, by rfl⟩ : syracuseStep 2503153 = 1877365) B1877365
theorem B1757683 : Blo 1756579 1757683 := bstep (se 1 (by rfl) ⟨1318262, by rfl⟩ : syracuseStep 1757683 = 2636525) B2636525
theorem B1757699 : Blo 1756579 1757699 := bstep (se 1 (by rfl) ⟨1318274, by rfl⟩ : syracuseStep 1757699 = 2636549) B2636549
theorem B1757715 : Blo 1756579 1757715 := bstep (se 1 (by rfl) ⟨1318286, by rfl⟩ : syracuseStep 1757715 = 2636573) B2636573
theorem B1757731 : Blo 1756579 1757731 := bstep (se 1 (by rfl) ⟨1318298, by rfl⟩ : syracuseStep 1757731 = 2636597) B2636597
theorem B2224675 : Blo 1756579 2224675 := bstep (se 1 (by rfl) ⟨1668506, by rfl⟩ : syracuseStep 2224675 = 3337013) B3337013
theorem B1757747 : Blo 1756579 1757747 := bstep (se 1 (by rfl) ⟨1318310, by rfl⟩ : syracuseStep 1757747 = 2636621) B2636621
theorem B2814529 : Blo 1756579 2814529 := bstep (se 2 (by rfl) ⟨1055448, by rfl⟩ : syracuseStep 2814529 = 2110897) B2110897
theorem B1757763 : Blo 1756579 1757763 := bstep (se 1 (by rfl) ⟨1318322, by rfl⟩ : syracuseStep 1757763 = 2636645) B2636645
theorem B1757779 : Blo 1756579 1757779 := bstep (se 1 (by rfl) ⟨1318334, by rfl⟩ : syracuseStep 1757779 = 2636669) B2636669
theorem B1757795 : Blo 1756579 1757795 := bstep (se 1 (by rfl) ⟨1318346, by rfl⟩ : syracuseStep 1757795 = 2636693) B2636693
theorem B1757811 : Blo 1756579 1757811 := bstep (se 1 (by rfl) ⟨1318358, by rfl⟩ : syracuseStep 1757811 = 2636717) B2636717
theorem B1757827 : Blo 1756579 1757827 := bstep (se 1 (by rfl) ⟨1318370, by rfl⟩ : syracuseStep 1757827 = 2636741) B2636741
theorem B1757843 : Blo 1756579 1757843 := bstep (se 1 (by rfl) ⟨1318382, by rfl⟩ : syracuseStep 1757843 = 2636765) B2636765
theorem B11727523 : Blo 1756579 11727523 := bstep (se 1 (by rfl) ⟨8795642, by rfl⟩ : syracuseStep 11727523 = 17591285) B17591285
theorem B1757859 : Blo 1756579 1757859 := bstep (se 1 (by rfl) ⟨1318394, by rfl⟩ : syracuseStep 1757859 = 2636789) B2636789
theorem B1757875 : Blo 1756579 1757875 := bstep (se 1 (by rfl) ⟨1318406, by rfl⟩ : syracuseStep 1757875 = 2636813) B2636813
theorem B1757891 : Blo 1756579 1757891 := bstep (se 1 (by rfl) ⟨1318418, by rfl⟩ : syracuseStep 1757891 = 2636837) B2636837
theorem B1757907 : Blo 1756579 1757907 := bstep (se 1 (by rfl) ⟨1318430, by rfl⟩ : syracuseStep 1757907 = 2636861) B2636861
theorem B16028387 : Blo 1756579 16028387 := bstep (se 1 (by rfl) ⟨12021290, by rfl⟩ : syracuseStep 16028387 = 24042581) B24042581
theorem B1757923 : Blo 1756579 1757923 := bstep (se 1 (by rfl) ⟨1318442, by rfl⟩ : syracuseStep 1757923 = 2636885) B2636885
theorem B3953393 : Blo 1756579 3953393 := bstep (se 2 (by rfl) ⟨1482522, by rfl⟩ : syracuseStep 3953393 = 2965045) B2965045
theorem B1757939 : Blo 1756579 1757939 := bstep (se 1 (by rfl) ⟨1318454, by rfl⟩ : syracuseStep 1757939 = 2636909) B2636909
theorem B3953411 : Blo 1756579 3953411 := bstep (se 1 (by rfl) ⟨2965058, by rfl⟩ : syracuseStep 3953411 = 5930117) B5930117
theorem B1757955 : Blo 1756579 1757955 := bstep (se 1 (by rfl) ⟨1318466, by rfl⟩ : syracuseStep 1757955 = 2636933) B2636933
theorem B1757971 : Blo 1756579 1757971 := bstep (se 1 (by rfl) ⟨1318478, by rfl⟩ : syracuseStep 1757971 = 2636957) B2636957
theorem B1757987 : Blo 1756579 1757987 := bstep (se 1 (by rfl) ⟨1318490, by rfl⟩ : syracuseStep 1757987 = 2636981) B2636981
theorem B1758003 : Blo 1756579 1758003 := bstep (se 1 (by rfl) ⟨1318502, by rfl⟩ : syracuseStep 1758003 = 2637005) B2637005
theorem B1758019 : Blo 1756579 1758019 := bstep (se 1 (by rfl) ⟨1318514, by rfl⟩ : syracuseStep 1758019 = 2637029) B2637029
theorem B8442701 : Blo 1756579 8442701 := bstep (se 3 (by rfl) ⟨1583006, by rfl⟩ : syracuseStep 8442701 = 3166013) B3166013
theorem B1758035 : Blo 1756579 1758035 := bstep (se 1 (by rfl) ⟨1318526, by rfl⟩ : syracuseStep 1758035 = 2637053) B2637053
theorem B1758051 : Blo 1756579 1758051 := bstep (se 1 (by rfl) ⟨1318538, by rfl⟩ : syracuseStep 1758051 = 2637077) B2637077
theorem B1758067 : Blo 1756579 1758067 := bstep (se 1 (by rfl) ⟨1318550, by rfl⟩ : syracuseStep 1758067 = 2637101) B2637101
theorem B7508963 : Blo 1756579 7508963 := bstep (se 1 (by rfl) ⟨5631722, by rfl⟩ : syracuseStep 7508963 = 11263445) B11263445
theorem B2814977 : Blo 1756579 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B3953681 : Blo 1756579 3953681 := bstep (se 2 (by rfl) ⟨1482630, by rfl⟩ : syracuseStep 3953681 = 2965261) B2965261
theorem B8893475 : Blo 1756579 8893475 := bstep (se 1 (by rfl) ⟨6670106, by rfl⟩ : syracuseStep 8893475 = 13340213) B13340213
theorem B3953699 : Blo 1756579 3953699 := bstep (se 1 (by rfl) ⟨2965274, by rfl⟩ : syracuseStep 3953699 = 5930549) B5930549
theorem B5002307 : Blo 1756579 5002307 := bstep (se 1 (by rfl) ⟨3751730, by rfl⟩ : syracuseStep 5002307 = 7503461) B7503461
theorem B10007621 : Blo 1756579 10007621 := bstep (se 4 (by rfl) ⟨938214, by rfl⟩ : syracuseStep 10007621 = 1876429) B1876429
theorem B12661859 : Blo 1756579 12661859 := bstep (se 1 (by rfl) ⟨9496394, by rfl⟩ : syracuseStep 12661859 = 18992789) B18992789
theorem B4813937 : Blo 1756579 4813937 := bstep (se 2 (by rfl) ⟨1805226, by rfl⟩ : syracuseStep 4813937 = 3610453) B3610453
theorem B2110579 : Blo 1756579 2110579 := bstep (se 1 (by rfl) ⟨1582934, by rfl⟩ : syracuseStep 2110579 = 3165869) B3165869
theorem B2634881 : Blo 1756579 2634881 := bstep (se 2 (by rfl) ⟨988080, by rfl⟩ : syracuseStep 2634881 = 1976161) B1976161
theorem B2634899 : Blo 1756579 2634899 := bstep (se 1 (by rfl) ⟨1976174, by rfl⟩ : syracuseStep 2634899 = 3952349) B3952349
theorem B2634929 : Blo 1756579 2634929 := bstep (se 2 (by rfl) ⟨988098, by rfl⟩ : syracuseStep 2634929 = 1976197) B1976197
theorem B2634947 : Blo 1756579 2634947 := bstep (se 1 (by rfl) ⟨1976210, by rfl⟩ : syracuseStep 2634947 = 3952421) B3952421
theorem B2634977 : Blo 1756579 2634977 := bstep (se 2 (by rfl) ⟨988116, by rfl⟩ : syracuseStep 2634977 = 1976233) B1976233
theorem B2634995 : Blo 1756579 2634995 := bstep (se 1 (by rfl) ⟨1976246, by rfl⟩ : syracuseStep 2634995 = 3952493) B3952493
theorem B2635025 : Blo 1756579 2635025 := bstep (se 2 (by rfl) ⟨988134, by rfl⟩ : syracuseStep 2635025 = 1976269) B1976269
theorem B2635043 : Blo 1756579 2635043 := bstep (se 1 (by rfl) ⟨1976282, by rfl⟩ : syracuseStep 2635043 = 3952565) B3952565
theorem B3953969 : Blo 1756579 3953969 := bstep (se 2 (by rfl) ⟨1482738, by rfl⟩ : syracuseStep 3953969 = 2965477) B2965477
theorem B2635073 : Blo 1756579 2635073 := bstep (se 2 (by rfl) ⟨988152, by rfl⟩ : syracuseStep 2635073 = 1976305) B1976305
theorem B3953987 : Blo 1756579 3953987 := bstep (se 1 (by rfl) ⟨2965490, by rfl⟩ : syracuseStep 3953987 = 5930981) B5930981
theorem B6010193 : Blo 1756579 6010193 := bstep (se 2 (by rfl) ⟨2253822, by rfl⟩ : syracuseStep 6010193 = 4507645) B4507645
theorem B2635091 : Blo 1756579 2635091 := bstep (se 1 (by rfl) ⟨1976318, by rfl⟩ : syracuseStep 2635091 = 3952637) B3952637
theorem B2635121 : Blo 1756579 2635121 := bstep (se 2 (by rfl) ⟨988170, by rfl⟩ : syracuseStep 2635121 = 1976341) B1976341
theorem B2635139 : Blo 1756579 2635139 := bstep (se 1 (by rfl) ⟨1976354, by rfl⟩ : syracuseStep 2635139 = 3952709) B3952709
theorem B2635169 : Blo 1756579 2635169 := bstep (se 2 (by rfl) ⟨988188, by rfl⟩ : syracuseStep 2635169 = 1976377) B1976377
theorem B2635187 : Blo 1756579 2635187 := bstep (se 1 (by rfl) ⟨1976390, by rfl⟩ : syracuseStep 2635187 = 3952781) B3952781
theorem B82294213 : Blo 1756579 82294213 := bstep (se 4 (by rfl) ⟨7715082, by rfl⟩ : syracuseStep 82294213 = 15430165) B15430165
theorem B2635217 : Blo 1756579 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B2635235 : Blo 1756579 2635235 := bstep (se 1 (by rfl) ⟨1976426, by rfl⟩ : syracuseStep 2635235 = 3952853) B3952853
theorem B2635265 : Blo 1756579 2635265 := bstep (se 2 (by rfl) ⟨988224, by rfl⟩ : syracuseStep 2635265 = 1976449) B1976449
theorem B15218189 : Blo 1756579 15218189 := bstep (se 3 (by rfl) ⟨2853410, by rfl⟩ : syracuseStep 15218189 = 5706821) B5706821
theorem B2635283 : Blo 1756579 2635283 := bstep (se 1 (by rfl) ⟨1976462, by rfl⟩ : syracuseStep 2635283 = 3952925) B3952925
theorem B5928497 : Blo 1756579 5928497 := bstep (se 2 (by rfl) ⟨2223186, by rfl⟩ : syracuseStep 5928497 = 4446373) B4446373
theorem B2635313 : Blo 1756579 2635313 := bstep (se 2 (by rfl) ⟨988242, by rfl⟩ : syracuseStep 2635313 = 1976485) B1976485
theorem B2635331 : Blo 1756579 2635331 := bstep (se 1 (by rfl) ⟨1976498, by rfl⟩ : syracuseStep 2635331 = 3952997) B3952997
theorem B3954257 : Blo 1756579 3954257 := bstep (se 2 (by rfl) ⟨1482846, by rfl⟩ : syracuseStep 3954257 = 2965693) B2965693
theorem B2635361 : Blo 1756579 2635361 := bstep (se 2 (by rfl) ⟨988260, by rfl⟩ : syracuseStep 2635361 = 1976521) B1976521
theorem B3954275 : Blo 1756579 3954275 := bstep (se 1 (by rfl) ⟨2965706, by rfl⟩ : syracuseStep 3954275 = 5931413) B5931413
theorem B22525553 : Blo 1756579 22525553 := bstep (se 2 (by rfl) ⟨8447082, by rfl⟩ : syracuseStep 22525553 = 16894165) B16894165
theorem B2635379 : Blo 1756579 2635379 := bstep (se 1 (by rfl) ⟨1976534, by rfl⟩ : syracuseStep 2635379 = 3953069) B3953069
theorem B2635409 : Blo 1756579 2635409 := bstep (se 2 (by rfl) ⟨988278, by rfl⟩ : syracuseStep 2635409 = 1976557) B1976557
theorem B2635427 : Blo 1756579 2635427 := bstep (se 1 (by rfl) ⟨1976570, by rfl⟩ : syracuseStep 2635427 = 3953141) B3953141
theorem B2635457 : Blo 1756579 2635457 := bstep (se 2 (by rfl) ⟨988296, by rfl⟩ : syracuseStep 2635457 = 1976593) B1976593
theorem B2635475 : Blo 1756579 2635475 := bstep (se 1 (by rfl) ⟨1976606, by rfl⟩ : syracuseStep 2635475 = 3953213) B3953213
theorem B6674147 : Blo 1756579 6674147 := bstep (se 1 (by rfl) ⟨5005610, by rfl⟩ : syracuseStep 6674147 = 10011221) B10011221
theorem B2635505 : Blo 1756579 2635505 := bstep (se 2 (by rfl) ⟨988314, by rfl⟩ : syracuseStep 2635505 = 1976629) B1976629
theorem B10008305 : Blo 1756579 10008305 := bstep (se 2 (by rfl) ⟨3753114, by rfl⟩ : syracuseStep 10008305 = 7506229) B7506229
theorem B2635523 : Blo 1756579 2635523 := bstep (se 1 (by rfl) ⟨1976642, by rfl⟩ : syracuseStep 2635523 = 3953285) B3953285
theorem B2635553 : Blo 1756579 2635553 := bstep (se 2 (by rfl) ⟨988332, by rfl⟩ : syracuseStep 2635553 = 1976665) B1976665
theorem B2635571 : Blo 1756579 2635571 := bstep (se 1 (by rfl) ⟨1976678, by rfl⟩ : syracuseStep 2635571 = 3953357) B3953357
theorem B8894285 : Blo 1756579 8894285 := bstep (se 3 (by rfl) ⟨1667678, by rfl⟩ : syracuseStep 8894285 = 3335357) B3335357
theorem B2635601 : Blo 1756579 2635601 := bstep (se 2 (by rfl) ⟨988350, by rfl⟩ : syracuseStep 2635601 = 1976701) B1976701
theorem B2635619 : Blo 1756579 2635619 := bstep (se 1 (by rfl) ⟨1976714, by rfl⟩ : syracuseStep 2635619 = 3953429) B3953429
theorem B5003117 : Blo 1756579 5003117 := bstep (se 3 (by rfl) ⟨938084, by rfl⟩ : syracuseStep 5003117 = 1876169) B1876169
theorem B25335665 : Blo 1756579 25335665 := bstep (se 2 (by rfl) ⟨9500874, by rfl⟩ : syracuseStep 25335665 = 19001749) B19001749
theorem B3954545 : Blo 1756579 3954545 := bstep (se 2 (by rfl) ⟨1482954, by rfl⟩ : syracuseStep 3954545 = 2965909) B2965909
theorem B2635649 : Blo 1756579 2635649 := bstep (se 2 (by rfl) ⟨988368, by rfl⟩ : syracuseStep 2635649 = 1976737) B1976737
theorem B3954563 : Blo 1756579 3954563 := bstep (se 1 (by rfl) ⟨2965922, by rfl⟩ : syracuseStep 3954563 = 5931845) B5931845
theorem B12662669 : Blo 1756579 12662669 := bstep (se 3 (by rfl) ⟨2374250, by rfl⟩ : syracuseStep 12662669 = 4748501) B4748501
theorem B2635667 : Blo 1756579 2635667 := bstep (se 1 (by rfl) ⟨1976750, by rfl⟩ : syracuseStep 2635667 = 3953501) B3953501
theorem B2635697 : Blo 1756579 2635697 := bstep (se 2 (by rfl) ⟨988386, by rfl⟩ : syracuseStep 2635697 = 1976773) B1976773
theorem B2635715 : Blo 1756579 2635715 := bstep (se 1 (by rfl) ⟨1976786, by rfl⟩ : syracuseStep 2635715 = 3953573) B3953573
theorem B2635745 : Blo 1756579 2635745 := bstep (se 2 (by rfl) ⟨988404, by rfl⟩ : syracuseStep 2635745 = 1976809) B1976809
theorem B3381233 : Blo 1756579 3381233 := bstep (se 2 (by rfl) ⟨1267962, by rfl⟩ : syracuseStep 3381233 = 2535925) B2535925
theorem B3856369 : Blo 1756579 3856369 := bstep (se 2 (by rfl) ⟨1446138, by rfl⟩ : syracuseStep 3856369 = 2892277) B2892277
theorem B2635763 : Blo 1756579 2635763 := bstep (se 1 (by rfl) ⟨1976822, by rfl⟩ : syracuseStep 2635763 = 3953645) B3953645
theorem B2635793 : Blo 1756579 2635793 := bstep (se 2 (by rfl) ⟨988422, by rfl⟩ : syracuseStep 2635793 = 1976845) B1976845
theorem B2635811 : Blo 1756579 2635811 := bstep (se 1 (by rfl) ⟨1976858, by rfl⟩ : syracuseStep 2635811 = 3953717) B3953717
theorem B5003309 : Blo 1756579 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B2635841 : Blo 1756579 2635841 := bstep (se 2 (by rfl) ⟨988440, by rfl⟩ : syracuseStep 2635841 = 1976881) B1976881
theorem B5929037 : Blo 1756579 5929037 := bstep (se 3 (by rfl) ⟨1111694, by rfl⟩ : syracuseStep 5929037 = 2223389) B2223389
theorem B2635859 : Blo 1756579 2635859 := bstep (se 1 (by rfl) ⟨1976894, by rfl⟩ : syracuseStep 2635859 = 3953789) B3953789
theorem B2635889 : Blo 1756579 2635889 := bstep (se 2 (by rfl) ⟨988458, by rfl⟩ : syracuseStep 2635889 = 1976917) B1976917
theorem B5929091 : Blo 1756579 5929091 := bstep (se 1 (by rfl) ⟨4446818, by rfl⟩ : syracuseStep 5929091 = 8893637) B8893637
theorem B2635907 : Blo 1756579 2635907 := bstep (se 1 (by rfl) ⟨1976930, by rfl⟩ : syracuseStep 2635907 = 3953861) B3953861
theorem B4446353 : Blo 1756579 4446353 := bstep (se 2 (by rfl) ⟨1667382, by rfl⟩ : syracuseStep 4446353 = 3334765) B3334765
theorem B3954833 : Blo 1756579 3954833 := bstep (se 2 (by rfl) ⟨1483062, by rfl⟩ : syracuseStep 3954833 = 2966125) B2966125
theorem B2635937 : Blo 1756579 2635937 := bstep (se 2 (by rfl) ⟨988476, by rfl⟩ : syracuseStep 2635937 = 1976953) B1976953
theorem B3954851 : Blo 1756579 3954851 := bstep (se 1 (by rfl) ⟨2966138, by rfl⟩ : syracuseStep 3954851 = 5932277) B5932277
theorem B2635955 : Blo 1756579 2635955 := bstep (se 1 (by rfl) ⟨1976966, by rfl⟩ : syracuseStep 2635955 = 3953933) B3953933
theorem B2635985 : Blo 1756579 2635985 := bstep (se 2 (by rfl) ⟨988494, by rfl⟩ : syracuseStep 2635985 = 1976989) B1976989
theorem B2636003 : Blo 1756579 2636003 := bstep (se 1 (by rfl) ⟨1977002, by rfl⟩ : syracuseStep 2636003 = 3954005) B3954005
theorem B2636033 : Blo 1756579 2636033 := bstep (se 2 (by rfl) ⟨988512, by rfl⟩ : syracuseStep 2636033 = 1977025) B1977025
theorem B2636051 : Blo 1756579 2636051 := bstep (se 1 (by rfl) ⟨1977038, by rfl⟩ : syracuseStep 2636051 = 3954077) B3954077
theorem B2636081 : Blo 1756579 2636081 := bstep (se 2 (by rfl) ⟨988530, by rfl⟩ : syracuseStep 2636081 = 1977061) B1977061
theorem B2636099 : Blo 1756579 2636099 := bstep (se 1 (by rfl) ⟨1977074, by rfl⟩ : syracuseStep 2636099 = 3954149) B3954149
theorem B2636129 : Blo 1756579 2636129 := bstep (se 2 (by rfl) ⟨988548, by rfl⟩ : syracuseStep 2636129 = 1977097) B1977097
theorem B2636147 : Blo 1756579 2636147 := bstep (se 1 (by rfl) ⟨1977110, by rfl⟩ : syracuseStep 2636147 = 3954221) B3954221
theorem B45021581 : Blo 1756579 45021581 := bstep (se 3 (by rfl) ⟨8441546, by rfl⟩ : syracuseStep 45021581 = 16883093) B16883093
theorem B5929361 : Blo 1756579 5929361 := bstep (se 2 (by rfl) ⟨2223510, by rfl⟩ : syracuseStep 5929361 = 4447021) B4447021
theorem B2636177 : Blo 1756579 2636177 := bstep (se 2 (by rfl) ⟨988566, by rfl⟩ : syracuseStep 2636177 = 1977133) B1977133
theorem B2636195 : Blo 1756579 2636195 := bstep (se 1 (by rfl) ⟨1977146, by rfl⟩ : syracuseStep 2636195 = 3954293) B3954293
theorem B3955121 : Blo 1756579 3955121 := bstep (se 2 (by rfl) ⟨1483170, by rfl⟩ : syracuseStep 3955121 = 2966341) B2966341
theorem B2636225 : Blo 1756579 2636225 := bstep (se 2 (by rfl) ⟨988584, by rfl⟩ : syracuseStep 2636225 = 1977169) B1977169
theorem B3955139 : Blo 1756579 3955139 := bstep (se 1 (by rfl) ⟨2966354, by rfl⟩ : syracuseStep 3955139 = 5932709) B5932709
theorem B2636243 : Blo 1756579 2636243 := bstep (se 1 (by rfl) ⟨1977182, by rfl⟩ : syracuseStep 2636243 = 3954365) B3954365
theorem B2636273 : Blo 1756579 2636273 := bstep (se 2 (by rfl) ⟨988602, by rfl⟩ : syracuseStep 2636273 = 1977205) B1977205
theorem B2636291 : Blo 1756579 2636291 := bstep (se 1 (by rfl) ⟨1977218, by rfl⟩ : syracuseStep 2636291 = 3954437) B3954437
theorem B2636321 : Blo 1756579 2636321 := bstep (se 2 (by rfl) ⟨988620, by rfl⟩ : syracuseStep 2636321 = 1977241) B1977241
theorem B2636339 : Blo 1756579 2636339 := bstep (se 1 (by rfl) ⟨1977254, by rfl⟩ : syracuseStep 2636339 = 3954509) B3954509
theorem B2636369 : Blo 1756579 2636369 := bstep (se 2 (by rfl) ⟨988638, by rfl⟩ : syracuseStep 2636369 = 1977277) B1977277
theorem B2636387 : Blo 1756579 2636387 := bstep (se 1 (by rfl) ⟨1977290, by rfl⟩ : syracuseStep 2636387 = 3954581) B3954581
theorem B2636417 : Blo 1756579 2636417 := bstep (se 2 (by rfl) ⟨988656, by rfl⟩ : syracuseStep 2636417 = 1977313) B1977313
theorem B2636435 : Blo 1756579 2636435 := bstep (se 1 (by rfl) ⟨1977326, by rfl⟩ : syracuseStep 2636435 = 3954653) B3954653
theorem B2636465 : Blo 1756579 2636465 := bstep (se 2 (by rfl) ⟨988674, by rfl⟩ : syracuseStep 2636465 = 1977349) B1977349
theorem B2636483 : Blo 1756579 2636483 := bstep (se 1 (by rfl) ⟨1977362, by rfl⟩ : syracuseStep 2636483 = 3954725) B3954725
theorem B6675149 : Blo 1756579 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B3955409 : Blo 1756579 3955409 := bstep (se 2 (by rfl) ⟨1483278, by rfl⟩ : syracuseStep 3955409 = 2966557) B2966557
theorem B2636513 : Blo 1756579 2636513 := bstep (se 2 (by rfl) ⟨988692, by rfl⟩ : syracuseStep 2636513 = 1977385) B1977385
theorem B3955427 : Blo 1756579 3955427 := bstep (se 1 (by rfl) ⟨2966570, by rfl⟩ : syracuseStep 3955427 = 5933141) B5933141
theorem B2636531 : Blo 1756579 2636531 := bstep (se 1 (by rfl) ⟨1977398, by rfl⟩ : syracuseStep 2636531 = 3954797) B3954797
theorem B3005185 : Blo 1756579 3005185 := bstep (se 2 (by rfl) ⟨1126944, by rfl⟩ : syracuseStep 3005185 = 2253889) B2253889
theorem B2636561 : Blo 1756579 2636561 := bstep (se 2 (by rfl) ⟨988710, by rfl⟩ : syracuseStep 2636561 = 1977421) B1977421
theorem B2636579 : Blo 1756579 2636579 := bstep (se 1 (by rfl) ⟨1977434, by rfl⟩ : syracuseStep 2636579 = 3954869) B3954869
theorem B2964289 : Blo 1756579 2964289 := bstep (se 2 (by rfl) ⟨1111608, by rfl⟩ : syracuseStep 2964289 = 2223217) B2223217
theorem B2636609 : Blo 1756579 2636609 := bstep (se 2 (by rfl) ⟨988728, by rfl⟩ : syracuseStep 2636609 = 1977457) B1977457
theorem B2636627 : Blo 1756579 2636627 := bstep (se 1 (by rfl) ⟨1977470, by rfl⟩ : syracuseStep 2636627 = 3954941) B3954941
theorem B2964323 : Blo 1756579 2964323 := bstep (se 1 (by rfl) ⟨2223242, by rfl⟩ : syracuseStep 2964323 = 4446485) B4446485
theorem B2636657 : Blo 1756579 2636657 := bstep (se 2 (by rfl) ⟨988746, by rfl⟩ : syracuseStep 2636657 = 1977493) B1977493
theorem B2374531 : Blo 1756579 2374531 := bstep (se 1 (by rfl) ⟨1780898, by rfl⟩ : syracuseStep 2374531 = 3561797) B3561797
theorem B2636675 : Blo 1756579 2636675 := bstep (se 1 (by rfl) ⟨1977506, by rfl⟩ : syracuseStep 2636675 = 3955013) B3955013
theorem B6331277 : Blo 1756579 6331277 := bstep (se 3 (by rfl) ⟨1187114, by rfl⟩ : syracuseStep 6331277 = 2374229) B2374229
theorem B2636705 : Blo 1756579 2636705 := bstep (se 2 (by rfl) ⟨988764, by rfl⟩ : syracuseStep 2636705 = 1977529) B1977529
theorem B5929901 : Blo 1756579 5929901 := bstep (se 3 (by rfl) ⟨1111856, by rfl⟩ : syracuseStep 5929901 = 2223713) B2223713
theorem B2636723 : Blo 1756579 2636723 := bstep (se 1 (by rfl) ⟨1977542, by rfl⟩ : syracuseStep 2636723 = 3955085) B3955085
theorem B7125965 : Blo 1756579 7125965 := bstep (se 3 (by rfl) ⟨1336118, by rfl⟩ : syracuseStep 7125965 = 2672237) B2672237
theorem B2636753 : Blo 1756579 2636753 := bstep (se 2 (by rfl) ⟨988782, by rfl⟩ : syracuseStep 2636753 = 1977565) B1977565
theorem B2964451 : Blo 1756579 2964451 := bstep (se 1 (by rfl) ⟨2223338, by rfl⟩ : syracuseStep 2964451 = 4446677) B4446677
theorem B5929955 : Blo 1756579 5929955 := bstep (se 1 (by rfl) ⟨4447466, by rfl⟩ : syracuseStep 5929955 = 8894933) B8894933
theorem B2636771 : Blo 1756579 2636771 := bstep (se 1 (by rfl) ⟨1977578, by rfl⟩ : syracuseStep 2636771 = 3955157) B3955157
theorem B2636801 : Blo 1756579 2636801 := bstep (se 2 (by rfl) ⟨988800, by rfl⟩ : syracuseStep 2636801 = 1977601) B1977601
theorem B5004301 : Blo 1756579 5004301 := bstep (se 3 (by rfl) ⟨938306, by rfl⟩ : syracuseStep 5004301 = 1876613) B1876613
theorem B2636819 : Blo 1756579 2636819 := bstep (se 1 (by rfl) ⟨1977614, by rfl⟩ : syracuseStep 2636819 = 3955229) B3955229
theorem B2636849 : Blo 1756579 2636849 := bstep (se 2 (by rfl) ⟨988818, by rfl⟩ : syracuseStep 2636849 = 1977637) B1977637
theorem B2636867 : Blo 1756579 2636867 := bstep (se 1 (by rfl) ⟨1977650, by rfl⟩ : syracuseStep 2636867 = 3955301) B3955301
theorem B2636897 : Blo 1756579 2636897 := bstep (se 2 (by rfl) ⟨988836, by rfl⟩ : syracuseStep 2636897 = 1977673) B1977673
theorem B2964593 : Blo 1756579 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B4447345 : Blo 1756579 4447345 := bstep (se 2 (by rfl) ⟨1667754, by rfl⟩ : syracuseStep 4447345 = 3335509) B3335509
theorem B2636915 : Blo 1756579 2636915 := bstep (se 1 (by rfl) ⟨1977686, by rfl⟩ : syracuseStep 2636915 = 3955373) B3955373
theorem B2636945 : Blo 1756579 2636945 := bstep (se 2 (by rfl) ⟨988854, by rfl⟩ : syracuseStep 2636945 = 1977709) B1977709
theorem B10009763 : Blo 1756579 10009763 := bstep (se 1 (by rfl) ⟨7507322, by rfl⟩ : syracuseStep 10009763 = 15014645) B15014645
theorem B6765731 : Blo 1756579 6765731 := bstep (se 1 (by rfl) ⟨5074298, by rfl⟩ : syracuseStep 6765731 = 10148597) B10148597
theorem B2636963 : Blo 1756579 2636963 := bstep (se 1 (by rfl) ⟨1977722, by rfl⟩ : syracuseStep 2636963 = 3955445) B3955445
theorem B2636993 : Blo 1756579 2636993 := bstep (se 2 (by rfl) ⟨988872, by rfl⟩ : syracuseStep 2636993 = 1977745) B1977745
theorem B2637011 : Blo 1756579 2637011 := bstep (se 1 (by rfl) ⟨1977758, by rfl⟩ : syracuseStep 2637011 = 3955517) B3955517
theorem B2964721 : Blo 1756579 2964721 := bstep (se 2 (by rfl) ⟨1111770, by rfl⟩ : syracuseStep 2964721 = 2223541) B2223541
theorem B5930225 : Blo 1756579 5930225 := bstep (se 2 (by rfl) ⟨2223834, by rfl⟩ : syracuseStep 5930225 = 4447669) B4447669
theorem B2637041 : Blo 1756579 2637041 := bstep (se 2 (by rfl) ⟨988890, by rfl⟩ : syracuseStep 2637041 = 1977781) B1977781
theorem B2637059 : Blo 1756579 2637059 := bstep (se 1 (by rfl) ⟨1977794, by rfl⟩ : syracuseStep 2637059 = 3955589) B3955589
theorem B2964755 : Blo 1756579 2964755 := bstep (se 1 (by rfl) ⟨2223566, by rfl⟩ : syracuseStep 2964755 = 4447133) B4447133
theorem B2637089 : Blo 1756579 2637089 := bstep (se 2 (by rfl) ⟨988908, by rfl⟩ : syracuseStep 2637089 = 1977817) B1977817
theorem B2637107 : Blo 1756579 2637107 := bstep (se 1 (by rfl) ⟨1977830, by rfl⟩ : syracuseStep 2637107 = 3955661) B3955661
theorem B3005761 : Blo 1756579 3005761 := bstep (se 2 (by rfl) ⟨1127160, by rfl⟩ : syracuseStep 3005761 = 2254321) B2254321
theorem B10689869 : Blo 1756579 10689869 := bstep (se 3 (by rfl) ⟨2004350, by rfl⟩ : syracuseStep 10689869 = 4008701) B4008701
theorem B8019299 : Blo 1756579 8019299 := bstep (se 1 (by rfl) ⟨6014474, by rfl⟩ : syracuseStep 8019299 = 12028949) B12028949
theorem B4447619 : Blo 1756579 4447619 := bstep (se 1 (by rfl) ⟨3335714, by rfl⟩ : syracuseStep 4447619 = 6671429) B6671429
theorem B2964883 : Blo 1756579 2964883 := bstep (se 1 (by rfl) ⟨2223662, by rfl⟩ : syracuseStep 2964883 = 4447325) B4447325
theorem B6331853 : Blo 1756579 6331853 := bstep (se 3 (by rfl) ⟨1187222, by rfl⟩ : syracuseStep 6331853 = 2374445) B2374445
theorem B15015395 : Blo 1756579 15015395 := bstep (se 1 (by rfl) ⟨11261546, by rfl⟩ : syracuseStep 15015395 = 22523093) B22523093
theorem B8797709 : Blo 1756579 8797709 := bstep (se 3 (by rfl) ⟨1649570, by rfl⟩ : syracuseStep 8797709 = 3299141) B3299141
theorem B2965025 : Blo 1756579 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B4447811 : Blo 1756579 4447811 := bstep (se 1 (by rfl) ⟨3335858, by rfl⟩ : syracuseStep 4447811 = 6671717) B6671717
theorem B22527557 : Blo 1756579 22527557 := bstep (se 4 (by rfl) ⟨2111958, by rfl⟩ : syracuseStep 22527557 = 4223917) B4223917
theorem B3382897 : Blo 1756579 3382897 := bstep (se 2 (by rfl) ⟨1268586, by rfl⟩ : syracuseStep 3382897 = 2537173) B2537173
theorem B2965153 : Blo 1756579 2965153 := bstep (se 2 (by rfl) ⟨1111932, by rfl⟩ : syracuseStep 2965153 = 2223865) B2223865
theorem B3006115 : Blo 1756579 3006115 := bstep (se 1 (by rfl) ⟨2254586, by rfl⟩ : syracuseStep 3006115 = 4509173) B4509173
theorem B3047105 : Blo 1756579 3047105 := bstep (se 2 (by rfl) ⟨1142664, by rfl⟩ : syracuseStep 3047105 = 2285329) B2285329
theorem B2965187 : Blo 1756579 2965187 := bstep (se 1 (by rfl) ⟨2223890, by rfl⟩ : syracuseStep 2965187 = 4447781) B4447781
theorem B4751075 : Blo 1756579 4751075 := bstep (se 1 (by rfl) ⟨3563306, by rfl⟩ : syracuseStep 4751075 = 7126613) B7126613
theorem B5930765 : Blo 1756579 5930765 := bstep (se 3 (by rfl) ⟨1112018, by rfl⟩ : syracuseStep 5930765 = 2224037) B2224037
theorem B3751697 : Blo 1756579 3751697 := bstep (se 2 (by rfl) ⟨1406886, by rfl⟩ : syracuseStep 3751697 = 2813773) B2813773
theorem B2965315 : Blo 1756579 2965315 := bstep (se 1 (by rfl) ⟨2223986, by rfl⟩ : syracuseStep 2965315 = 4447973) B4447973
theorem B5930819 : Blo 1756579 5930819 := bstep (se 1 (by rfl) ⟨4448114, by rfl⟩ : syracuseStep 5930819 = 8896229) B8896229
theorem B5627789 : Blo 1756579 5627789 := bstep (se 3 (by rfl) ⟨1055210, by rfl⟩ : syracuseStep 5627789 = 2110421) B2110421
theorem B25681805 : Blo 1756579 25681805 := bstep (se 3 (by rfl) ⟨4815338, by rfl⟩ : syracuseStep 25681805 = 9630677) B9630677
theorem B2375569 : Blo 1756579 2375569 := bstep (se 2 (by rfl) ⟨890838, by rfl⟩ : syracuseStep 2375569 = 1781677) B1781677
theorem B2965457 : Blo 1756579 2965457 := bstep (se 2 (by rfl) ⟨1112046, by rfl⟩ : syracuseStep 2965457 = 2224093) B2224093
theorem B2375635 : Blo 1756579 2375635 := bstep (se 1 (by rfl) ⟨1781726, by rfl⟩ : syracuseStep 2375635 = 3563453) B3563453
theorem B2891747 : Blo 1756579 2891747 := bstep (se 1 (by rfl) ⟨2168810, by rfl⟩ : syracuseStep 2891747 = 4337621) B4337621
theorem B6094871 : Blo 1756579 6094871 := bstep (se 1 (by rfl) ⟨4571153, by rfl⟩ : syracuseStep 6094871 = 9142307) B9142307
theorem B5005405 : Blo 1756579 5005405 := bstep (se 3 (by rfl) ⟨938513, by rfl⟩ : syracuseStep 5005405 = 1877027) B1877027
theorem B4448459 : Blo 1756579 4448459 := bstep (se 1 (by rfl) ⟨3336344, by rfl⟩ : syracuseStep 4448459 = 6672689) B6672689
theorem B3563777 : Blo 1756579 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B5005633 : Blo 1756579 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B2965835 : Blo 1756579 2965835 := bstep (se 1 (by rfl) ⟨2224376, by rfl⟩ : syracuseStep 2965835 = 4448753) B4448753
theorem B5931467 : Blo 1756579 5931467 := bstep (se 1 (by rfl) ⟨4448600, by rfl⟩ : syracuseStep 5931467 = 8897201) B8897201
theorem B2965963 : Blo 1756579 2965963 := bstep (se 1 (by rfl) ⟨2224472, by rfl⟩ : syracuseStep 2965963 = 4448945) B4448945
theorem B22528529 : Blo 1756579 22528529 := bstep (se 2 (by rfl) ⟨8448198, by rfl⟩ : syracuseStep 22528529 = 16896397) B16896397
theorem B5628467 : Blo 1756579 5628467 := bstep (se 1 (by rfl) ⟨4221350, by rfl⟩ : syracuseStep 5628467 = 8442701) B8442701
theorem B10142273 : Blo 1756579 10142273 := bstep (se 2 (by rfl) ⟨3803352, by rfl⟩ : syracuseStep 10142273 = 7606705) B7606705
theorem B2966105 : Blo 1756579 2966105 := bstep (se 2 (by rfl) ⟨1112289, by rfl⟩ : syracuseStep 2966105 = 2224579) B2224579
theorem B11256421 : Blo 1756579 11256421 := bstep (se 4 (by rfl) ⟨1055289, by rfl⟩ : syracuseStep 11256421 = 2110579) B2110579
theorem B12026519 : Blo 1756579 12026519 := bstep (se 1 (by rfl) ⟨9019889, by rfl⟩ : syracuseStep 12026519 = 18039779) B18039779
theorem B5005975 : Blo 1756579 5005975 := bstep (se 1 (by rfl) ⟨3754481, by rfl⟩ : syracuseStep 5005975 = 7508963) B7508963
theorem B1876651 : Blo 1756579 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B3334871 : Blo 1756579 3334871 := bstep (se 1 (by rfl) ⟨2501153, by rfl⟩ : syracuseStep 3334871 = 5002307) B5002307
theorem B5931737 : Blo 1756579 5931737 := bstep (se 2 (by rfl) ⟨2224401, by rfl⟩ : syracuseStep 5931737 = 4448803) B4448803
theorem B2966233 : Blo 1756579 2966233 := bstep (se 2 (by rfl) ⟨1112337, by rfl⟩ : syracuseStep 2966233 = 2224675) B2224675
theorem B3752705 : Blo 1756579 3752705 := bstep (se 2 (by rfl) ⟨1407264, by rfl⟩ : syracuseStep 3752705 = 2814529) B2814529
theorem B16032613 : Blo 1756579 16032613 := bstep (se 4 (by rfl) ⟨1503057, by rfl⟩ : syracuseStep 16032613 = 3006115) B3006115
theorem B62546789 : Blo 1756579 62546789 := bstep (se 4 (by rfl) ⟨5863761, by rfl⟩ : syracuseStep 62546789 = 11727523) B11727523
theorem B4006795 : Blo 1756579 4006795 := bstep (se 1 (by rfl) ⟨3005096, by rfl⟩ : syracuseStep 4006795 = 6010193) B6010193
theorem B4006913 : Blo 1756579 4006913 := bstep (se 2 (by rfl) ⟨1502592, by rfl⟩ : syracuseStep 4006913 = 3005185) B3005185
theorem B15017035 : Blo 1756579 15017035 := bstep (se 1 (by rfl) ⟨11262776, by rfl⟩ : syracuseStep 15017035 = 22525553) B22525553
theorem B3753047 : Blo 1756579 3753047 := bstep (se 1 (by rfl) ⟨2814785, by rfl⟩ : syracuseStep 3753047 = 5629571) B5629571
theorem B9503837 : Blo 1756579 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B8897687 : Blo 1756579 8897687 := bstep (se 1 (by rfl) ⟨6673265, by rfl⟩ : syracuseStep 8897687 = 13346531) B13346531
theorem B4449431 : Blo 1756579 4449431 := bstep (se 1 (by rfl) ⟨3337073, by rfl⟩ : syracuseStep 4449431 = 6674147) B6674147
theorem B3335411 : Blo 1756579 3335411 := bstep (se 1 (by rfl) ⟨2501558, by rfl⟩ : syracuseStep 3335411 = 5003117) B5003117
theorem B15017309 : Blo 1756579 15017309 := bstep (se 3 (by rfl) ⟨2815745, by rfl⟩ : syracuseStep 15017309 = 5631491) B5631491
theorem B5932439 : Blo 1756579 5932439 := bstep (se 1 (by rfl) ⟨4449329, by rfl⟩ : syracuseStep 5932439 = 8898659) B8898659
theorem B3335897 : Blo 1756579 3335897 := bstep (se 2 (by rfl) ⟨1250961, by rfl⟩ : syracuseStep 3335897 = 2501923) B2501923
theorem B4007681 : Blo 1756579 4007681 := bstep (se 2 (by rfl) ⟨1502880, by rfl⟩ : syracuseStep 4007681 = 3005761) B3005761
theorem B4450099 : Blo 1756579 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B1976215 : Blo 1756579 1976215 := bstep (se 1 (by rfl) ⟨1482161, by rfl⟩ : syracuseStep 1976215 = 2964323) B2964323
theorem B109725617 : Blo 1756579 109725617 := bstep (se 2 (by rfl) ⟨41147106, by rfl⟩ : syracuseStep 109725617 = 82294213) B82294213
theorem B6670259 : Blo 1756579 6670259 := bstep (se 1 (by rfl) ⟨5002694, by rfl⟩ : syracuseStep 6670259 = 10005389) B10005389
theorem B4220851 : Blo 1756579 4220851 := bstep (se 1 (by rfl) ⟨3165638, by rfl⟩ : syracuseStep 4220851 = 6331277) B6331277
theorem B4507571 : Blo 1756579 4507571 := bstep (se 1 (by rfl) ⟨3380678, by rfl⟩ : syracuseStep 4507571 = 6761357) B6761357
theorem B5932979 : Blo 1756579 5932979 := bstep (se 1 (by rfl) ⟨4449734, by rfl⟩ : syracuseStep 5932979 = 8899469) B8899469
theorem B1976395 : Blo 1756579 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B1976503 : Blo 1756579 1976503 := bstep (se 1 (by rfl) ⟨1482377, by rfl⟩ : syracuseStep 1976503 = 2964755) B2964755
theorem B5933249 : Blo 1756579 5933249 := bstep (se 2 (by rfl) ⟨2224968, by rfl⟩ : syracuseStep 5933249 = 4449937) B4449937
theorem B7506179 : Blo 1756579 7506179 := bstep (se 1 (by rfl) ⟨5629634, by rfl⟩ : syracuseStep 7506179 = 11259269) B11259269
theorem B4221235 : Blo 1756579 4221235 := bstep (se 1 (by rfl) ⟨3165926, by rfl⟩ : syracuseStep 4221235 = 6331853) B6331853
theorem B1976683 : Blo 1756579 1976683 := bstep (se 1 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 1976683 = 2965025) B2965025
theorem B15018371 : Blo 1756579 15018371 := bstep (se 1 (by rfl) ⟨11263778, by rfl⟩ : syracuseStep 15018371 = 22527557) B22527557
theorem B1976791 : Blo 1756579 1976791 := bstep (se 1 (by rfl) ⟨1482593, by rfl⟩ : syracuseStep 1976791 = 2965187) B2965187
theorem B2501131 : Blo 1756579 2501131 := bstep (se 1 (by rfl) ⟨1875848, by rfl⟩ : syracuseStep 2501131 = 3751697) B3751697
theorem B7711325 : Blo 1756579 7711325 := bstep (se 3 (by rfl) ⟨1445873, by rfl⟩ : syracuseStep 7711325 = 2891747) B2891747
theorem B1976971 : Blo 1756579 1976971 := bstep (se 1 (by rfl) ⟨1482728, by rfl⟩ : syracuseStep 1976971 = 2965457) B2965457
theorem B1977079 : Blo 1756579 1977079 := bstep (se 1 (by rfl) ⟨1482809, by rfl⟩ : syracuseStep 1977079 = 2965619) B2965619
theorem B1977259 : Blo 1756579 1977259 := bstep (se 1 (by rfl) ⟨1482944, by rfl⟩ : syracuseStep 1977259 = 2965889) B2965889
theorem B1977367 : Blo 1756579 1977367 := bstep (se 1 (by rfl) ⟨1483025, by rfl⟩ : syracuseStep 1977367 = 2966051) B2966051
theorem B3337355 : Blo 1756579 3337355 := bstep (se 1 (by rfl) ⟨2503016, by rfl⟩ : syracuseStep 3337355 = 5006033) B5006033
theorem B10685591 : Blo 1756579 10685591 := bstep (se 1 (by rfl) ⟨8014193, by rfl⟩ : syracuseStep 10685591 = 16028387) B16028387
theorem B1977547 : Blo 1756579 1977547 := bstep (se 1 (by rfl) ⟨1483160, by rfl⟩ : syracuseStep 1977547 = 2966321) B2966321
theorem B15011021 : Blo 1756579 15011021 := bstep (se 3 (by rfl) ⟨2814566, by rfl⟩ : syracuseStep 15011021 = 5629133) B5629133
theorem B1977655 : Blo 1756579 1977655 := bstep (se 1 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 1977655 = 2966483) B2966483
theorem B3337537 : Blo 1756579 3337537 := bstep (se 2 (by rfl) ⟨1251576, by rfl⟩ : syracuseStep 3337537 = 2503153) B2503153
theorem B6671747 : Blo 1756579 6671747 := bstep (se 1 (by rfl) ⟨5003810, by rfl⟩ : syracuseStep 6671747 = 10007621) B10007621
theorem B1756587 : Blo 1756579 1756587 := bstep (se 1 (by rfl) ⟨1317440, by rfl⟩ : syracuseStep 1756587 = 2634881) B2634881
theorem B1756599 : Blo 1756579 1756599 := bstep (se 1 (by rfl) ⟨1317449, by rfl⟩ : syracuseStep 1756599 = 2634899) B2634899
theorem B1756619 : Blo 1756579 1756619 := bstep (se 1 (by rfl) ⟨1317464, by rfl⟩ : syracuseStep 1756619 = 2634929) B2634929
theorem B1756631 : Blo 1756579 1756631 := bstep (se 1 (by rfl) ⟨1317473, by rfl⟩ : syracuseStep 1756631 = 2634947) B2634947
theorem B1756651 : Blo 1756579 1756651 := bstep (se 1 (by rfl) ⟨1317488, by rfl⟩ : syracuseStep 1756651 = 2634977) B2634977
theorem B1977835 : Blo 1756579 1977835 := bstep (se 1 (by rfl) ⟨1483376, by rfl⟩ : syracuseStep 1977835 = 2966753) B2966753
theorem B1756663 : Blo 1756579 1756663 := bstep (se 1 (by rfl) ⟨1317497, by rfl⟩ : syracuseStep 1756663 = 2634995) B2634995
theorem B1756683 : Blo 1756579 1756683 := bstep (se 1 (by rfl) ⟨1317512, by rfl⟩ : syracuseStep 1756683 = 2635025) B2635025
theorem B1756695 : Blo 1756579 1756695 := bstep (se 1 (by rfl) ⟨1317521, by rfl⟩ : syracuseStep 1756695 = 2635043) B2635043
theorem B1756715 : Blo 1756579 1756715 := bstep (se 1 (by rfl) ⟨1317536, by rfl⟩ : syracuseStep 1756715 = 2635073) B2635073
theorem B1756727 : Blo 1756579 1756727 := bstep (se 1 (by rfl) ⟨1317545, by rfl⟩ : syracuseStep 1756727 = 2635091) B2635091
theorem B1756747 : Blo 1756579 1756747 := bstep (se 1 (by rfl) ⟨1317560, by rfl⟩ : syracuseStep 1756747 = 2635121) B2635121
theorem B1756759 : Blo 1756579 1756759 := bstep (se 1 (by rfl) ⟨1317569, by rfl⟩ : syracuseStep 1756759 = 2635139) B2635139
theorem B2223703 : Blo 1756579 2223703 := bstep (se 1 (by rfl) ⟨1667777, by rfl⟩ : syracuseStep 2223703 = 3335555) B3335555
theorem B1756779 : Blo 1756579 1756779 := bstep (se 1 (by rfl) ⟨1317584, by rfl⟩ : syracuseStep 1756779 = 2635169) B2635169
theorem B1756791 : Blo 1756579 1756791 := bstep (se 1 (by rfl) ⟨1317593, by rfl⟩ : syracuseStep 1756791 = 2635187) B2635187
theorem B1756811 : Blo 1756579 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B1756823 : Blo 1756579 1756823 := bstep (se 1 (by rfl) ⟨1317617, by rfl⟩ : syracuseStep 1756823 = 2635235) B2635235
theorem B1756843 : Blo 1756579 1756843 := bstep (se 1 (by rfl) ⟨1317632, by rfl⟩ : syracuseStep 1756843 = 2635265) B2635265
theorem B10145459 : Blo 1756579 10145459 := bstep (se 1 (by rfl) ⟨7609094, by rfl⟩ : syracuseStep 10145459 = 15218189) B15218189
theorem B1756855 : Blo 1756579 1756855 := bstep (se 1 (by rfl) ⟨1317641, by rfl⟩ : syracuseStep 1756855 = 2635283) B2635283
theorem B3952331 : Blo 1756579 3952331 := bstep (se 1 (by rfl) ⟨2964248, by rfl⟩ : syracuseStep 3952331 = 5928497) B5928497
theorem B1756875 : Blo 1756579 1756875 := bstep (se 1 (by rfl) ⟨1317656, by rfl⟩ : syracuseStep 1756875 = 2635313) B2635313
theorem B1756887 : Blo 1756579 1756887 := bstep (se 1 (by rfl) ⟨1317665, by rfl⟩ : syracuseStep 1756887 = 2635331) B2635331
theorem B2502361 : Blo 1756579 2502361 := bstep (se 2 (by rfl) ⟨938385, by rfl⟩ : syracuseStep 2502361 = 1876771) B1876771
theorem B1756907 : Blo 1756579 1756907 := bstep (se 1 (by rfl) ⟨1317680, by rfl⟩ : syracuseStep 1756907 = 2635361) B2635361
theorem B1756919 : Blo 1756579 1756919 := bstep (se 1 (by rfl) ⟨1317689, by rfl⟩ : syracuseStep 1756919 = 2635379) B2635379
theorem B3952385 : Blo 1756579 3952385 := bstep (se 2 (by rfl) ⟨1482144, by rfl⟩ : syracuseStep 3952385 = 2964289) B2964289
theorem B1756939 : Blo 1756579 1756939 := bstep (se 1 (by rfl) ⟨1317704, by rfl⟩ : syracuseStep 1756939 = 2635409) B2635409
theorem B1756951 : Blo 1756579 1756951 := bstep (se 1 (by rfl) ⟨1317713, by rfl⟩ : syracuseStep 1756951 = 2635427) B2635427
theorem B1756971 : Blo 1756579 1756971 := bstep (se 1 (by rfl) ⟨1317728, by rfl⟩ : syracuseStep 1756971 = 2635457) B2635457
theorem B1756983 : Blo 1756579 1756983 := bstep (se 1 (by rfl) ⟨1317737, by rfl⟩ : syracuseStep 1756983 = 2635475) B2635475
theorem B6672203 : Blo 1756579 6672203 := bstep (se 1 (by rfl) ⟨5004152, by rfl⟩ : syracuseStep 6672203 = 10008305) B10008305
theorem B1757003 : Blo 1756579 1757003 := bstep (se 1 (by rfl) ⟨1317752, by rfl⟩ : syracuseStep 1757003 = 2635505) B2635505
theorem B1757015 : Blo 1756579 1757015 := bstep (se 1 (by rfl) ⟨1317761, by rfl⟩ : syracuseStep 1757015 = 2635523) B2635523
theorem B1757035 : Blo 1756579 1757035 := bstep (se 1 (by rfl) ⟨1317776, by rfl⟩ : syracuseStep 1757035 = 2635553) B2635553
theorem B1757047 : Blo 1756579 1757047 := bstep (se 1 (by rfl) ⟨1317785, by rfl⟩ : syracuseStep 1757047 = 2635571) B2635571
theorem B1757067 : Blo 1756579 1757067 := bstep (se 1 (by rfl) ⟨1317800, by rfl⟩ : syracuseStep 1757067 = 2635601) B2635601
theorem B1757079 : Blo 1756579 1757079 := bstep (se 1 (by rfl) ⟨1317809, by rfl⟩ : syracuseStep 1757079 = 2635619) B2635619
theorem B1757099 : Blo 1756579 1757099 := bstep (se 1 (by rfl) ⟨1317824, by rfl⟩ : syracuseStep 1757099 = 2635649) B2635649
theorem B8441779 : Blo 1756579 8441779 := bstep (se 1 (by rfl) ⟨6331334, by rfl⟩ : syracuseStep 8441779 = 12662669) B12662669
theorem B1757111 : Blo 1756579 1757111 := bstep (se 1 (by rfl) ⟨1317833, by rfl⟩ : syracuseStep 1757111 = 2635667) B2635667
theorem B1757131 : Blo 1756579 1757131 := bstep (se 1 (by rfl) ⟨1317848, by rfl⟩ : syracuseStep 1757131 = 2635697) B2635697
theorem B1757143 : Blo 1756579 1757143 := bstep (se 1 (by rfl) ⟨1317857, by rfl⟩ : syracuseStep 1757143 = 2635715) B2635715
theorem B3952601 : Blo 1756579 3952601 := bstep (se 2 (by rfl) ⟨1482225, by rfl⟩ : syracuseStep 3952601 = 2964451) B2964451
theorem B1757163 : Blo 1756579 1757163 := bstep (se 1 (by rfl) ⟨1317872, by rfl⟩ : syracuseStep 1757163 = 2635745) B2635745
theorem B1757175 : Blo 1756579 1757175 := bstep (se 1 (by rfl) ⟨1317881, by rfl⟩ : syracuseStep 1757175 = 2635763) B2635763
theorem B7221251 : Blo 1756579 7221251 := bstep (se 1 (by rfl) ⟨5415938, by rfl⟩ : syracuseStep 7221251 = 10831877) B10831877
theorem B1757195 : Blo 1756579 1757195 := bstep (se 1 (by rfl) ⟨1317896, by rfl⟩ : syracuseStep 1757195 = 2635793) B2635793
theorem B1781771 : Blo 1756579 1781771 := bstep (se 1 (by rfl) ⟨1336328, by rfl⟩ : syracuseStep 1781771 = 2672657) B2672657
theorem B6672401 : Blo 1756579 6672401 := bstep (se 2 (by rfl) ⟨2502150, by rfl⟩ : syracuseStep 6672401 = 5004301) B5004301
theorem B1757207 : Blo 1756579 1757207 := bstep (se 1 (by rfl) ⟨1317905, by rfl⟩ : syracuseStep 1757207 = 2635811) B2635811
theorem B1757227 : Blo 1756579 1757227 := bstep (se 1 (by rfl) ⟨1317920, by rfl⟩ : syracuseStep 1757227 = 2635841) B2635841
theorem B3952691 : Blo 1756579 3952691 := bstep (se 1 (by rfl) ⟨2964518, by rfl⟩ : syracuseStep 3952691 = 5929037) B5929037
theorem B1757239 : Blo 1756579 1757239 := bstep (se 1 (by rfl) ⟨1317929, by rfl⟩ : syracuseStep 1757239 = 2635859) B2635859
theorem B1757259 : Blo 1756579 1757259 := bstep (se 1 (by rfl) ⟨1317944, by rfl⟩ : syracuseStep 1757259 = 2635889) B2635889
theorem B3952727 : Blo 1756579 3952727 := bstep (se 1 (by rfl) ⟨2964545, by rfl⟩ : syracuseStep 3952727 = 5929091) B5929091
theorem B1757271 : Blo 1756579 1757271 := bstep (se 1 (by rfl) ⟨1317953, by rfl⟩ : syracuseStep 1757271 = 2635907) B2635907
theorem B1757291 : Blo 1756579 1757291 := bstep (se 1 (by rfl) ⟨1317968, by rfl⟩ : syracuseStep 1757291 = 2635937) B2635937
theorem B1757303 : Blo 1756579 1757303 := bstep (se 1 (by rfl) ⟨1317977, by rfl⟩ : syracuseStep 1757303 = 2635955) B2635955
theorem B1757323 : Blo 1756579 1757323 := bstep (se 1 (by rfl) ⟨1317992, by rfl⟩ : syracuseStep 1757323 = 2635985) B2635985
theorem B1757335 : Blo 1756579 1757335 := bstep (se 1 (by rfl) ⟨1318001, by rfl⟩ : syracuseStep 1757335 = 2636003) B2636003
theorem B1757355 : Blo 1756579 1757355 := bstep (se 1 (by rfl) ⟨1318016, by rfl⟩ : syracuseStep 1757355 = 2636033) B2636033
theorem B1757367 : Blo 1756579 1757367 := bstep (se 1 (by rfl) ⟨1318025, by rfl⟩ : syracuseStep 1757367 = 2636051) B2636051
theorem B1757387 : Blo 1756579 1757387 := bstep (se 1 (by rfl) ⟨1318040, by rfl⟩ : syracuseStep 1757387 = 2636081) B2636081
theorem B1757399 : Blo 1756579 1757399 := bstep (se 1 (by rfl) ⟨1318049, by rfl⟩ : syracuseStep 1757399 = 2636099) B2636099
theorem B1757419 : Blo 1756579 1757419 := bstep (se 1 (by rfl) ⟨1318064, by rfl⟩ : syracuseStep 1757419 = 2636129) B2636129
theorem B1757431 : Blo 1756579 1757431 := bstep (se 1 (by rfl) ⟨1318073, by rfl⟩ : syracuseStep 1757431 = 2636147) B2636147
theorem B3952907 : Blo 1756579 3952907 := bstep (se 1 (by rfl) ⟨2964680, by rfl⟩ : syracuseStep 3952907 = 5929361) B5929361
theorem B1757451 : Blo 1756579 1757451 := bstep (se 1 (by rfl) ⟨1318088, by rfl⟩ : syracuseStep 1757451 = 2636177) B2636177
theorem B1757463 : Blo 1756579 1757463 := bstep (se 1 (by rfl) ⟨1318097, by rfl⟩ : syracuseStep 1757463 = 2636195) B2636195
theorem B1757483 : Blo 1756579 1757483 := bstep (se 1 (by rfl) ⟨1318112, by rfl⟩ : syracuseStep 1757483 = 2636225) B2636225
theorem B1757495 : Blo 1756579 1757495 := bstep (se 1 (by rfl) ⟨1318121, by rfl⟩ : syracuseStep 1757495 = 2636243) B2636243
theorem B3952961 : Blo 1756579 3952961 := bstep (se 2 (by rfl) ⟨1482360, by rfl⟩ : syracuseStep 3952961 = 2964721) B2964721
theorem B1757515 : Blo 1756579 1757515 := bstep (se 1 (by rfl) ⟨1318136, by rfl⟩ : syracuseStep 1757515 = 2636273) B2636273
theorem B1757527 : Blo 1756579 1757527 := bstep (se 1 (by rfl) ⟨1318145, by rfl⟩ : syracuseStep 1757527 = 2636291) B2636291
theorem B1757547 : Blo 1756579 1757547 := bstep (se 1 (by rfl) ⟨1318160, by rfl⟩ : syracuseStep 1757547 = 2636321) B2636321
theorem B1757559 : Blo 1756579 1757559 := bstep (se 1 (by rfl) ⟨1318169, by rfl⟩ : syracuseStep 1757559 = 2636339) B2636339
theorem B1757579 : Blo 1756579 1757579 := bstep (se 1 (by rfl) ⟨1318184, by rfl⟩ : syracuseStep 1757579 = 2636369) B2636369
theorem B2224523 : Blo 1756579 2224523 := bstep (se 1 (by rfl) ⟨1668392, by rfl⟩ : syracuseStep 2224523 = 3336785) B3336785
theorem B1757591 : Blo 1756579 1757591 := bstep (se 1 (by rfl) ⟨1318193, by rfl⟩ : syracuseStep 1757591 = 2636387) B2636387
theorem B1757611 : Blo 1756579 1757611 := bstep (se 1 (by rfl) ⟨1318208, by rfl⟩ : syracuseStep 1757611 = 2636417) B2636417
theorem B1757623 : Blo 1756579 1757623 := bstep (se 1 (by rfl) ⟨1318217, by rfl⟩ : syracuseStep 1757623 = 2636435) B2636435
theorem B1757643 : Blo 1756579 1757643 := bstep (se 1 (by rfl) ⟨1318232, by rfl⟩ : syracuseStep 1757643 = 2636465) B2636465
theorem B1757655 : Blo 1756579 1757655 := bstep (se 1 (by rfl) ⟨1318241, by rfl⟩ : syracuseStep 1757655 = 2636483) B2636483
theorem B1757675 : Blo 1756579 1757675 := bstep (se 1 (by rfl) ⟨1318256, by rfl⟩ : syracuseStep 1757675 = 2636513) B2636513
theorem B1757687 : Blo 1756579 1757687 := bstep (se 1 (by rfl) ⟨1318265, by rfl⟩ : syracuseStep 1757687 = 2636531) B2636531
theorem B1757707 : Blo 1756579 1757707 := bstep (se 1 (by rfl) ⟨1318280, by rfl⟩ : syracuseStep 1757707 = 2636561) B2636561
theorem B64139789 : Blo 1756579 64139789 := bstep (se 3 (by rfl) ⟨12026210, by rfl⟩ : syracuseStep 64139789 = 24052421) B24052421
theorem B1757719 : Blo 1756579 1757719 := bstep (se 1 (by rfl) ⟨1318289, by rfl⟩ : syracuseStep 1757719 = 2636579) B2636579
theorem B3953177 : Blo 1756579 3953177 := bstep (se 2 (by rfl) ⟨1482441, by rfl⟩ : syracuseStep 3953177 = 2964883) B2964883
theorem B1757739 : Blo 1756579 1757739 := bstep (se 1 (by rfl) ⟨1318304, by rfl⟩ : syracuseStep 1757739 = 2636609) B2636609
theorem B1757751 : Blo 1756579 1757751 := bstep (se 1 (by rfl) ⟨1318313, by rfl⟩ : syracuseStep 1757751 = 2636627) B2636627
theorem B7221835 : Blo 1756579 7221835 := bstep (se 1 (by rfl) ⟨5416376, by rfl⟩ : syracuseStep 7221835 = 10832753) B10832753
theorem B1757771 : Blo 1756579 1757771 := bstep (se 1 (by rfl) ⟨1318328, by rfl⟩ : syracuseStep 1757771 = 2636657) B2636657
theorem B1757783 : Blo 1756579 1757783 := bstep (se 1 (by rfl) ⟨1318337, by rfl⟩ : syracuseStep 1757783 = 2636675) B2636675
theorem B12669533 : Blo 1756579 12669533 := bstep (se 3 (by rfl) ⟨2375537, by rfl⟩ : syracuseStep 12669533 = 4751075) B4751075
theorem B1757803 : Blo 1756579 1757803 := bstep (se 1 (by rfl) ⟨1318352, by rfl⟩ : syracuseStep 1757803 = 2636705) B2636705
theorem B3953267 : Blo 1756579 3953267 := bstep (se 1 (by rfl) ⟨2964950, by rfl⟩ : syracuseStep 3953267 = 5929901) B5929901
theorem B1757815 : Blo 1756579 1757815 := bstep (se 1 (by rfl) ⟨1318361, by rfl⟩ : syracuseStep 1757815 = 2636723) B2636723
theorem B1757835 : Blo 1756579 1757835 := bstep (se 1 (by rfl) ⟨1318376, by rfl⟩ : syracuseStep 1757835 = 2636753) B2636753
theorem B3953303 : Blo 1756579 3953303 := bstep (se 1 (by rfl) ⟨2964977, by rfl⟩ : syracuseStep 3953303 = 5929955) B5929955
theorem B1757847 : Blo 1756579 1757847 := bstep (se 1 (by rfl) ⟨1318385, by rfl⟩ : syracuseStep 1757847 = 2636771) B2636771
theorem B4223639 : Blo 1756579 4223639 := bstep (se 1 (by rfl) ⟨3167729, by rfl⟩ : syracuseStep 4223639 = 6335459) B6335459
theorem B1757867 : Blo 1756579 1757867 := bstep (se 1 (by rfl) ⟨1318400, by rfl⟩ : syracuseStep 1757867 = 2636801) B2636801
theorem B1757879 : Blo 1756579 1757879 := bstep (se 1 (by rfl) ⟨1318409, by rfl⟩ : syracuseStep 1757879 = 2636819) B2636819
theorem B1757899 : Blo 1756579 1757899 := bstep (se 1 (by rfl) ⟨1318424, by rfl⟩ : syracuseStep 1757899 = 2636849) B2636849
theorem B1757911 : Blo 1756579 1757911 := bstep (se 1 (by rfl) ⟨1318433, by rfl⟩ : syracuseStep 1757911 = 2636867) B2636867
theorem B1757931 : Blo 1756579 1757931 := bstep (se 1 (by rfl) ⟨1318448, by rfl⟩ : syracuseStep 1757931 = 2636897) B2636897
theorem B1757943 : Blo 1756579 1757943 := bstep (se 1 (by rfl) ⟨1318457, by rfl⟩ : syracuseStep 1757943 = 2636915) B2636915
theorem B12669701 : Blo 1756579 12669701 := bstep (se 4 (by rfl) ⟨1187784, by rfl⟩ : syracuseStep 12669701 = 2375569) B2375569
theorem B1757963 : Blo 1756579 1757963 := bstep (se 1 (by rfl) ⟨1318472, by rfl⟩ : syracuseStep 1757963 = 2636945) B2636945
theorem B6673175 : Blo 1756579 6673175 := bstep (se 1 (by rfl) ⟨5004881, by rfl⟩ : syracuseStep 6673175 = 10009763) B10009763
theorem B4510487 : Blo 1756579 4510487 := bstep (se 1 (by rfl) ⟨3382865, by rfl⟩ : syracuseStep 4510487 = 6765731) B6765731
theorem B1757975 : Blo 1756579 1757975 := bstep (se 1 (by rfl) ⟨1318481, by rfl⟩ : syracuseStep 1757975 = 2636963) B2636963
theorem B1757995 : Blo 1756579 1757995 := bstep (se 1 (by rfl) ⟨1318496, by rfl⟩ : syracuseStep 1757995 = 2636993) B2636993
theorem B1758007 : Blo 1756579 1758007 := bstep (se 1 (by rfl) ⟨1318505, by rfl⟩ : syracuseStep 1758007 = 2637011) B2637011
theorem B4510529 : Blo 1756579 4510529 := bstep (se 2 (by rfl) ⟨1691448, by rfl⟩ : syracuseStep 4510529 = 3382897) B3382897
theorem B3953483 : Blo 1756579 3953483 := bstep (se 1 (by rfl) ⟨2965112, by rfl⟩ : syracuseStep 3953483 = 5930225) B5930225
theorem B1758027 : Blo 1756579 1758027 := bstep (se 1 (by rfl) ⟨1318520, by rfl⟩ : syracuseStep 1758027 = 2637041) B2637041
theorem B1758039 : Blo 1756579 1758039 := bstep (se 1 (by rfl) ⟨1318529, by rfl⟩ : syracuseStep 1758039 = 2637059) B2637059
theorem B1758059 : Blo 1756579 1758059 := bstep (se 1 (by rfl) ⟨1318544, by rfl⟩ : syracuseStep 1758059 = 2637089) B2637089
theorem B1758071 : Blo 1756579 1758071 := bstep (se 1 (by rfl) ⟨1318553, by rfl⟩ : syracuseStep 1758071 = 2637107) B2637107
theorem B3953537 : Blo 1756579 3953537 := bstep (se 2 (by rfl) ⟨1482576, by rfl⟩ : syracuseStep 3953537 = 2965153) B2965153
theorem B5346199 : Blo 1756579 5346199 := bstep (se 1 (by rfl) ⟨4009649, by rfl⟩ : syracuseStep 5346199 = 8019299) B8019299
theorem B6673373 : Blo 1756579 6673373 := bstep (se 3 (by rfl) ⟨1251257, by rfl⟩ : syracuseStep 6673373 = 2502515) B2502515
theorem B13349933 : Blo 1756579 13349933 := bstep (se 3 (by rfl) ⟨2503112, by rfl⟩ : syracuseStep 13349933 = 5006225) B5006225
theorem B3953753 : Blo 1756579 3953753 := bstep (se 2 (by rfl) ⟨1482657, by rfl⟩ : syracuseStep 3953753 = 2965315) B2965315
theorem B2634905 : Blo 1756579 2634905 := bstep (se 2 (by rfl) ⟨988089, by rfl⟩ : syracuseStep 2634905 = 1976179) B1976179
theorem B3953843 : Blo 1756579 3953843 := bstep (se 1 (by rfl) ⟨2965382, by rfl⟩ : syracuseStep 3953843 = 5930765) B5930765
theorem B36066485 : Blo 1756579 36066485 := bstep (se 5 (by rfl) ⟨1690616, by rfl⟩ : syracuseStep 36066485 = 3381233) B3381233
theorem B3953879 : Blo 1756579 3953879 := bstep (se 1 (by rfl) ⟨2965409, by rfl⟩ : syracuseStep 3953879 = 5930819) B5930819
theorem B16889093 : Blo 1756579 16889093 := bstep (se 4 (by rfl) ⟨1583352, by rfl⟩ : syracuseStep 16889093 = 3166705) B3166705
theorem B2635019 : Blo 1756579 2635019 := bstep (se 1 (by rfl) ⟨1976264, by rfl⟩ : syracuseStep 2635019 = 3952529) B3952529
theorem B2635031 : Blo 1756579 2635031 := bstep (se 1 (by rfl) ⟨1976273, by rfl⟩ : syracuseStep 2635031 = 3952547) B3952547
theorem B3167513 : Blo 1756579 3167513 := bstep (se 2 (by rfl) ⟨1187817, by rfl⟩ : syracuseStep 3167513 = 2375635) B2375635
theorem B10007873 : Blo 1756579 10007873 := bstep (se 2 (by rfl) ⟨3752952, by rfl⟩ : syracuseStep 10007873 = 7505905) B7505905
theorem B5141825 : Blo 1756579 5141825 := bstep (se 2 (by rfl) ⟨1928184, by rfl⟩ : syracuseStep 5141825 = 3856369) B3856369
theorem B2635097 : Blo 1756579 2635097 := bstep (se 2 (by rfl) ⟨988161, by rfl⟩ : syracuseStep 2635097 = 1976323) B1976323
theorem B3954059 : Blo 1756579 3954059 := bstep (se 1 (by rfl) ⟨2965544, by rfl⟩ : syracuseStep 3954059 = 5931089) B5931089
theorem B50656661 : Blo 1756579 50656661 := bstep (se 6 (by rfl) ⟨1187265, by rfl⟩ : syracuseStep 50656661 = 2374531) B2374531
theorem B3954113 : Blo 1756579 3954113 := bstep (se 2 (by rfl) ⟨1482792, by rfl⟩ : syracuseStep 3954113 = 2965585) B2965585
theorem B2635211 : Blo 1756579 2635211 := bstep (se 1 (by rfl) ⟨1976408, by rfl⟩ : syracuseStep 2635211 = 3952817) B3952817
theorem B13342157 : Blo 1756579 13342157 := bstep (se 3 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 13342157 = 5003309) B5003309
theorem B2635223 : Blo 1756579 2635223 := bstep (se 1 (by rfl) ⟨1976417, by rfl⟩ : syracuseStep 2635223 = 3952835) B3952835
theorem B5002717 : Blo 1756579 5002717 := bstep (se 3 (by rfl) ⟨938009, by rfl⟩ : syracuseStep 5002717 = 1876019) B1876019
theorem B2635289 : Blo 1756579 2635289 := bstep (se 2 (by rfl) ⟨988233, by rfl⟩ : syracuseStep 2635289 = 1976467) B1976467
theorem B33764957 : Blo 1756579 33764957 := bstep (se 3 (by rfl) ⟨6330929, by rfl⟩ : syracuseStep 33764957 = 12661859) B12661859
theorem B2635403 : Blo 1756579 2635403 := bstep (se 1 (by rfl) ⟨1976552, by rfl⟩ : syracuseStep 2635403 = 3953105) B3953105
theorem B2635415 : Blo 1756579 2635415 := bstep (se 1 (by rfl) ⟨1976561, by rfl⟩ : syracuseStep 2635415 = 3953123) B3953123
theorem B3954329 : Blo 1756579 3954329 := bstep (se 2 (by rfl) ⟨1482873, by rfl⟩ : syracuseStep 3954329 = 2965747) B2965747
theorem B2635481 : Blo 1756579 2635481 := bstep (se 2 (by rfl) ⟨988305, by rfl⟩ : syracuseStep 2635481 = 1976611) B1976611
theorem B3954419 : Blo 1756579 3954419 := bstep (se 1 (by rfl) ⟨2965814, by rfl⟩ : syracuseStep 3954419 = 5931629) B5931629
theorem B3954455 : Blo 1756579 3954455 := bstep (se 1 (by rfl) ⟨2965841, by rfl⟩ : syracuseStep 3954455 = 5931683) B5931683
theorem B5003059 : Blo 1756579 5003059 := bstep (se 1 (by rfl) ⟨3752294, by rfl⟩ : syracuseStep 5003059 = 7504589) B7504589
theorem B2635595 : Blo 1756579 2635595 := bstep (se 1 (by rfl) ⟨1976696, by rfl⟩ : syracuseStep 2635595 = 3953393) B3953393
theorem B2635607 : Blo 1756579 2635607 := bstep (se 1 (by rfl) ⟨1976705, by rfl⟩ : syracuseStep 2635607 = 3953411) B3953411
theorem B2635673 : Blo 1756579 2635673 := bstep (se 2 (by rfl) ⟨988377, by rfl⟩ : syracuseStep 2635673 = 1976755) B1976755
theorem B13342643 : Blo 1756579 13342643 := bstep (se 1 (by rfl) ⟨10006982, by rfl⟩ : syracuseStep 13342643 = 20013965) B20013965
theorem B3954635 : Blo 1756579 3954635 := bstep (se 1 (by rfl) ⟨2965976, by rfl⟩ : syracuseStep 3954635 = 5931953) B5931953
theorem B3954689 : Blo 1756579 3954689 := bstep (se 2 (by rfl) ⟨1483008, by rfl⟩ : syracuseStep 3954689 = 2966017) B2966017
theorem B2635787 : Blo 1756579 2635787 := bstep (se 1 (by rfl) ⟨1976840, by rfl⟩ : syracuseStep 2635787 = 3953681) B3953681
theorem B5928983 : Blo 1756579 5928983 := bstep (se 1 (by rfl) ⟨4446737, by rfl⟩ : syracuseStep 5928983 = 8893475) B8893475
theorem B2635799 : Blo 1756579 2635799 := bstep (se 1 (by rfl) ⟨1976849, by rfl⟩ : syracuseStep 2635799 = 3953699) B3953699
theorem B3209291 : Blo 1756579 3209291 := bstep (se 1 (by rfl) ⟨2406968, by rfl⟩ : syracuseStep 3209291 = 4813937) B4813937
theorem B2635865 : Blo 1756579 2635865 := bstep (se 2 (by rfl) ⟨988449, by rfl⟩ : syracuseStep 2635865 = 1976899) B1976899
theorem B13015171 : Blo 1756579 13015171 := bstep (se 1 (by rfl) ⟨9761378, by rfl⟩ : syracuseStep 13015171 = 19522757) B19522757
theorem B2635979 : Blo 1756579 2635979 := bstep (se 1 (by rfl) ⟨1976984, by rfl⟩ : syracuseStep 2635979 = 3953969) B3953969
theorem B2635991 : Blo 1756579 2635991 := bstep (se 1 (by rfl) ⟨1976993, by rfl⟩ : syracuseStep 2635991 = 3953987) B3953987
theorem B3954905 : Blo 1756579 3954905 := bstep (se 2 (by rfl) ⟨1483089, by rfl⟩ : syracuseStep 3954905 = 2966179) B2966179
theorem B2636057 : Blo 1756579 2636057 := bstep (se 2 (by rfl) ⟨988521, by rfl⟩ : syracuseStep 2636057 = 1977043) B1977043
theorem B4446515 : Blo 1756579 4446515 := bstep (se 1 (by rfl) ⟨3334886, by rfl⟩ : syracuseStep 4446515 = 6669773) B6669773
theorem B3954995 : Blo 1756579 3954995 := bstep (se 1 (by rfl) ⟨2966246, by rfl⟩ : syracuseStep 3954995 = 5932493) B5932493
theorem B3955031 : Blo 1756579 3955031 := bstep (se 1 (by rfl) ⟨2966273, by rfl⟩ : syracuseStep 3955031 = 5932547) B5932547
theorem B2636171 : Blo 1756579 2636171 := bstep (se 1 (by rfl) ⟨1977128, by rfl⟩ : syracuseStep 2636171 = 3954257) B3954257
theorem B2636183 : Blo 1756579 2636183 := bstep (se 1 (by rfl) ⟨1977137, by rfl⟩ : syracuseStep 2636183 = 3954275) B3954275
theorem B2636249 : Blo 1756579 2636249 := bstep (se 2 (by rfl) ⟨988593, by rfl⟩ : syracuseStep 2636249 = 1977187) B1977187
theorem B3561985 : Blo 1756579 3561985 := bstep (se 2 (by rfl) ⟨1335744, by rfl⟩ : syracuseStep 3561985 = 2671489) B2671489
theorem B3955211 : Blo 1756579 3955211 := bstep (se 1 (by rfl) ⟨2966408, by rfl⟩ : syracuseStep 3955211 = 5932817) B5932817
theorem B5929523 : Blo 1756579 5929523 := bstep (se 1 (by rfl) ⟨4447142, by rfl⟩ : syracuseStep 5929523 = 8894285) B8894285
theorem B3955265 : Blo 1756579 3955265 := bstep (se 2 (by rfl) ⟨1483224, by rfl⟩ : syracuseStep 3955265 = 2966449) B2966449
theorem B16890443 : Blo 1756579 16890443 := bstep (se 1 (by rfl) ⟨12667832, by rfl⟩ : syracuseStep 16890443 = 25335665) B25335665
theorem B2636363 : Blo 1756579 2636363 := bstep (se 1 (by rfl) ⟨1977272, by rfl⟩ : syracuseStep 2636363 = 3954545) B3954545
theorem B2636375 : Blo 1756579 2636375 := bstep (se 1 (by rfl) ⟨1977281, by rfl⟩ : syracuseStep 2636375 = 3954563) B3954563
theorem B4446809 : Blo 1756579 4446809 := bstep (se 2 (by rfl) ⟨1667553, by rfl⟩ : syracuseStep 4446809 = 3335107) B3335107
theorem B2636441 : Blo 1756579 2636441 := bstep (se 2 (by rfl) ⟨988665, by rfl⟩ : syracuseStep 2636441 = 1977331) B1977331
theorem B5003993 : Blo 1756579 5003993 := bstep (se 2 (by rfl) ⟨1876497, by rfl⟩ : syracuseStep 5003993 = 3752995) B3752995
theorem B2964235 : Blo 1756579 2964235 := bstep (se 1 (by rfl) ⟨2223176, by rfl⟩ : syracuseStep 2964235 = 4446353) B4446353
theorem B2636555 : Blo 1756579 2636555 := bstep (se 1 (by rfl) ⟨1977416, by rfl⟩ : syracuseStep 2636555 = 3954833) B3954833
theorem B2636567 : Blo 1756579 2636567 := bstep (se 1 (by rfl) ⟨1977425, by rfl⟩ : syracuseStep 2636567 = 3954851) B3954851
theorem B3955481 : Blo 1756579 3955481 := bstep (se 2 (by rfl) ⟨1483305, by rfl⟩ : syracuseStep 3955481 = 2966611) B2966611
theorem B5929793 : Blo 1756579 5929793 := bstep (se 2 (by rfl) ⟨2223672, by rfl⟩ : syracuseStep 5929793 = 4447345) B4447345
theorem B2636633 : Blo 1756579 2636633 := bstep (se 2 (by rfl) ⟨988737, by rfl⟩ : syracuseStep 2636633 = 1977475) B1977475
theorem B3955571 : Blo 1756579 3955571 := bstep (se 1 (by rfl) ⟨2966678, by rfl⟩ : syracuseStep 3955571 = 5933357) B5933357
theorem B3955607 : Blo 1756579 3955607 := bstep (se 1 (by rfl) ⟨2966705, by rfl⟩ : syracuseStep 3955607 = 5933411) B5933411
theorem B2964377 : Blo 1756579 2964377 := bstep (se 2 (by rfl) ⟨1111641, by rfl⟩ : syracuseStep 2964377 = 2223283) B2223283
theorem B30014387 : Blo 1756579 30014387 := bstep (se 1 (by rfl) ⟨22510790, by rfl⟩ : syracuseStep 30014387 = 45021581) B45021581
theorem B2636747 : Blo 1756579 2636747 := bstep (se 1 (by rfl) ⟨1977560, by rfl⟩ : syracuseStep 2636747 = 3955121) B3955121
theorem B2636759 : Blo 1756579 2636759 := bstep (se 1 (by rfl) ⟨1977569, by rfl⟩ : syracuseStep 2636759 = 3955139) B3955139
theorem B2964505 : Blo 1756579 2964505 := bstep (se 2 (by rfl) ⟨1111689, by rfl⟩ : syracuseStep 2964505 = 2223379) B2223379
theorem B2636825 : Blo 1756579 2636825 := bstep (se 2 (by rfl) ⟨988809, by rfl⟩ : syracuseStep 2636825 = 1977619) B1977619
theorem B8895581 : Blo 1756579 8895581 := bstep (se 3 (by rfl) ⟨1667921, by rfl⟩ : syracuseStep 8895581 = 3335843) B3335843
theorem B2636939 : Blo 1756579 2636939 := bstep (se 1 (by rfl) ⟨1977704, by rfl⟩ : syracuseStep 2636939 = 3955409) B3955409
theorem B2636951 : Blo 1756579 2636951 := bstep (se 1 (by rfl) ⟨1977713, by rfl⟩ : syracuseStep 2636951 = 3955427) B3955427
theorem B2637017 : Blo 1756579 2637017 := bstep (se 2 (by rfl) ⟨988881, by rfl⟩ : syracuseStep 2637017 = 1977763) B1977763
theorem B4750643 : Blo 1756579 4750643 := bstep (se 1 (by rfl) ⟨3562982, by rfl⟩ : syracuseStep 4750643 = 7125965) B7125965
theorem B13712705 : Blo 1756579 13712705 := bstep (se 2 (by rfl) ⟨5142264, by rfl⟩ : syracuseStep 13712705 = 10284529) B10284529
theorem B5930333 : Blo 1756579 5930333 := bstep (se 3 (by rfl) ⟨1111937, by rfl⟩ : syracuseStep 5930333 = 2223875) B2223875
theorem B13344101 : Blo 1756579 13344101 := bstep (se 4 (by rfl) ⟨1251009, by rfl⟩ : syracuseStep 13344101 = 2502019) B2502019
theorem B3857843 : Blo 1756579 3857843 := bstep (se 1 (by rfl) ⟨2893382, by rfl⟩ : syracuseStep 3857843 = 5786765) B5786765
theorem B7126579 : Blo 1756579 7126579 := bstep (se 1 (by rfl) ⟨5344934, by rfl⟩ : syracuseStep 7126579 = 10689869) B10689869
theorem B2965079 : Blo 1756579 2965079 := bstep (se 1 (by rfl) ⟨2223809, by rfl⟩ : syracuseStep 2965079 = 4447619) B4447619
theorem B10010263 : Blo 1756579 10010263 := bstep (se 1 (by rfl) ⟨7507697, by rfl⟩ : syracuseStep 10010263 = 15015395) B15015395
theorem B5865139 : Blo 1756579 5865139 := bstep (se 1 (by rfl) ⟨4398854, by rfl⟩ : syracuseStep 5865139 = 8797709) B8797709
theorem B2965207 : Blo 1756579 2965207 := bstep (se 1 (by rfl) ⟨2223905, by rfl⟩ : syracuseStep 2965207 = 4447811) B4447811
theorem B2031403 : Blo 1756579 2031403 := bstep (se 1 (by rfl) ⟨1523552, by rfl⟩ : syracuseStep 2031403 = 3047105) B3047105
theorem B13344587 : Blo 1756579 13344587 := bstep (se 1 (by rfl) ⟨10008440, by rfl⟩ : syracuseStep 13344587 = 20016881) B20016881
theorem B2604953 : Blo 1756579 2604953 := bstep (se 2 (by rfl) ⟨976857, by rfl⟩ : syracuseStep 2604953 = 1953715) B1953715
theorem B3751859 : Blo 1756579 3751859 := bstep (se 1 (by rfl) ⟨2813894, by rfl⟩ : syracuseStep 3751859 = 5627789) B5627789
theorem B17121203 : Blo 1756579 17121203 := bstep (se 1 (by rfl) ⟨12840902, by rfl⟩ : syracuseStep 17121203 = 25681805) B25681805
theorem B18997253 : Blo 1756579 18997253 := bstep (se 4 (by rfl) ⟨1780992, by rfl⟩ : syracuseStep 18997253 = 3561985) B3561985
theorem B4448267 : Blo 1756579 4448267 := bstep (se 1 (by rfl) ⟨3336200, by rfl⟩ : syracuseStep 4448267 = 6672401) B6672401
theorem B4063247 : Blo 1756579 4063247 := bstep (se 1 (by rfl) ⟨3047435, by rfl⟩ : syracuseStep 4063247 = 6094871) B6094871
theorem B4751389 : Blo 1756579 4751389 := bstep (se 3 (by rfl) ⟨890885, by rfl⟩ : syracuseStep 4751389 = 1781771) B1781771
theorem B2965639 : Blo 1756579 2965639 := bstep (se 1 (by rfl) ⟨2224229, by rfl⟩ : syracuseStep 2965639 = 4448459) B4448459
theorem B8446355 : Blo 1756579 8446355 := bstep (se 1 (by rfl) ⟨6334766, by rfl⟩ : syracuseStep 8446355 = 12669533) B12669533
theorem B5628313 : Blo 1756579 5628313 := bstep (se 2 (by rfl) ⟨2110617, by rfl⟩ : syracuseStep 5628313 = 4221235) B4221235
theorem B4448783 : Blo 1756579 4448783 := bstep (se 1 (by rfl) ⟨3336587, by rfl⟩ : syracuseStep 4448783 = 6673175) B6673175
theorem B3006991 : Blo 1756579 3006991 := bstep (se 1 (by rfl) ⟨2255243, by rfl⟩ : syracuseStep 3006991 = 4510487) B4510487
theorem B3007019 : Blo 1756579 3007019 := bstep (se 1 (by rfl) ⟨2255264, by rfl⟩ : syracuseStep 3007019 = 4510529) B4510529
theorem B4448915 : Blo 1756579 4448915 := bstep (se 1 (by rfl) ⟨3336686, by rfl⟩ : syracuseStep 4448915 = 6673373) B6673373
theorem B9503405 : Blo 1756579 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B3334841 : Blo 1756579 3334841 := bstep (se 2 (by rfl) ⟨1250565, by rfl⟩ : syracuseStep 3334841 = 2501131) B2501131
theorem B5931791 : Blo 1756579 5931791 := bstep (se 1 (by rfl) ⟨4448843, by rfl⟩ : syracuseStep 5931791 = 8897687) B8897687
theorem B2966287 : Blo 1756579 2966287 := bstep (se 1 (by rfl) ⟨2224715, by rfl⟩ : syracuseStep 2966287 = 4449431) B4449431
theorem B24044323 : Blo 1756579 24044323 := bstep (se 1 (by rfl) ⟨18033242, by rfl⟩ : syracuseStep 24044323 = 36066485) B36066485
theorem B15008561 : Blo 1756579 15008561 := bstep (se 2 (by rfl) ⟨5628210, by rfl⟩ : syracuseStep 15008561 = 11256421) B11256421
theorem B10011539 : Blo 1756579 10011539 := bstep (se 1 (by rfl) ⟨7508654, by rfl⟩ : syracuseStep 10011539 = 15017309) B15017309
theorem B5932061 : Blo 1756579 5932061 := bstep (se 3 (by rfl) ⟨1112261, by rfl⟩ : syracuseStep 5932061 = 2224523) B2224523
theorem B2671787 : Blo 1756579 2671787 := bstep (se 1 (by rfl) ⟨2003840, by rfl⟩ : syracuseStep 2671787 = 4007681) B4007681
theorem B5342393 : Blo 1756579 5342393 := bstep (se 2 (by rfl) ⟨2003397, by rfl⟩ : syracuseStep 5342393 = 4006795) B4006795
theorem B7128265 : Blo 1756579 7128265 := bstep (se 2 (by rfl) ⟨2673099, by rfl⟩ : syracuseStep 7128265 = 5346199) B5346199
theorem B2139527 : Blo 1756579 2139527 := bstep (se 1 (by rfl) ⟨1604645, by rfl⟩ : syracuseStep 2139527 = 3209291) B3209291
theorem B20022713 : Blo 1756579 20022713 := bstep (se 2 (by rfl) ⟨7508517, by rfl⟩ : syracuseStep 20022713 = 15017035) B15017035
theorem B15009245 : Blo 1756579 15009245 := bstep (se 3 (by rfl) ⟨2814233, by rfl⟩ : syracuseStep 15009245 = 5628467) B5628467
theorem B10012247 : Blo 1756579 10012247 := bstep (se 1 (by rfl) ⟨7509185, by rfl⟩ : syracuseStep 10012247 = 15018371) B15018371
theorem B4450049 : Blo 1756579 4450049 := bstep (se 2 (by rfl) ⟨1668768, by rfl⟩ : syracuseStep 4450049 = 3337537) B3337537
theorem B3335995 : Blo 1756579 3335995 := bstep (se 1 (by rfl) ⟨2501996, by rfl⟩ : syracuseStep 3335995 = 5003993) B5003993
theorem B1976251 : Blo 1756579 1976251 := bstep (se 1 (by rfl) ⟨1482188, by rfl⟩ : syracuseStep 1976251 = 2964377) B2964377
theorem B6670289 : Blo 1756579 6670289 := bstep (se 2 (by rfl) ⟨2501358, by rfl⟩ : syracuseStep 6670289 = 5002717) B5002717
theorem B33785869 : Blo 1756579 33785869 := bstep (se 3 (by rfl) ⟨6334850, by rfl⟩ : syracuseStep 33785869 = 12669701) B12669701
theorem B13347017 : Blo 1756579 13347017 := bstep (se 2 (by rfl) ⟨5005131, by rfl⟩ : syracuseStep 13347017 = 10010263) B10010263
theorem B166791437 : Blo 1756579 166791437 := bstep (se 3 (by rfl) ⟨31273394, by rfl⟩ : syracuseStep 166791437 = 62546789) B62546789
theorem B3336481 : Blo 1756579 3336481 := bstep (se 2 (by rfl) ⟨1251180, by rfl⟩ : syracuseStep 3336481 = 2502361) B2502361
theorem B1976719 : Blo 1756579 1976719 := bstep (se 1 (by rfl) ⟨1482539, by rfl⟩ : syracuseStep 1976719 = 2965079) B2965079
theorem B6670745 : Blo 1756579 6670745 := bstep (se 2 (by rfl) ⟨2501529, by rfl⟩ : syracuseStep 6670745 = 5003059) B5003059
theorem B5933465 : Blo 1756579 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B10004957 : Blo 1756579 10004957 := bstep (se 3 (by rfl) ⟨1875929, by rfl⟩ : syracuseStep 10004957 = 3751859) B3751859
theorem B11414135 : Blo 1756579 11414135 := bstep (se 1 (by rfl) ⟨8560601, by rfl⟩ : syracuseStep 11414135 = 17121203) B17121203
theorem B42740405 : Blo 1756579 42740405 := bstep (se 5 (by rfl) ⟨2003456, by rfl⟩ : syracuseStep 42740405 = 4006913) B4006913
theorem B17353561 : Blo 1756579 17353561 := bstep (se 2 (by rfl) ⟨6507585, by rfl⟩ : syracuseStep 17353561 = 13015171) B13015171
theorem B1977223 : Blo 1756579 1977223 := bstep (se 1 (by rfl) ⟨1482917, by rfl⟩ : syracuseStep 1977223 = 2965835) B2965835
theorem B15019019 : Blo 1756579 15019019 := bstep (se 1 (by rfl) ⟨11264264, by rfl⟩ : syracuseStep 15019019 = 22528529) B22528529
theorem B1977403 : Blo 1756579 1977403 := bstep (se 1 (by rfl) ⟨1483052, by rfl⟩ : syracuseStep 1977403 = 2966105) B2966105
theorem B2501803 : Blo 1756579 2501803 := bstep (se 1 (by rfl) ⟨1876352, by rfl⟩ : syracuseStep 2501803 = 3752705) B3752705
theorem B8899955 : Blo 1756579 8899955 := bstep (se 1 (by rfl) ⟨6674966, by rfl⟩ : syracuseStep 8899955 = 13349933) B13349933
theorem B2502031 : Blo 1756579 2502031 := bstep (se 1 (by rfl) ⟨1876523, by rfl⟩ : syracuseStep 2502031 = 3753047) B3753047
theorem B6335891 : Blo 1756579 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B9629113 : Blo 1756579 9629113 := bstep (se 2 (by rfl) ⟨3610917, by rfl⟩ : syracuseStep 9629113 = 7221835) B7221835
theorem B1756603 : Blo 1756579 1756603 := bstep (se 1 (by rfl) ⟨1317452, by rfl⟩ : syracuseStep 1756603 = 2634905) B2634905
theorem B2223607 : Blo 1756579 2223607 := bstep (se 1 (by rfl) ⟨1667705, by rfl⟩ : syracuseStep 2223607 = 3335411) B3335411
theorem B11259395 : Blo 1756579 11259395 := bstep (se 1 (by rfl) ⟨8444546, by rfl⟩ : syracuseStep 11259395 = 16889093) B16889093
theorem B1756679 : Blo 1756579 1756679 := bstep (se 1 (by rfl) ⟨1317509, by rfl⟩ : syracuseStep 1756679 = 2635019) B2635019
theorem B1756687 : Blo 1756579 1756687 := bstep (se 1 (by rfl) ⟨1317515, by rfl⟩ : syracuseStep 1756687 = 2635031) B2635031
theorem B6671915 : Blo 1756579 6671915 := bstep (se 1 (by rfl) ⟨5003936, by rfl⟩ : syracuseStep 6671915 = 10007873) B10007873
theorem B3427883 : Blo 1756579 3427883 := bstep (se 1 (by rfl) ⟨2570912, by rfl⟩ : syracuseStep 3427883 = 5141825) B5141825
theorem B1756731 : Blo 1756579 1756731 := bstep (se 1 (by rfl) ⟨1317548, by rfl⟩ : syracuseStep 1756731 = 2635097) B2635097
theorem B33771107 : Blo 1756579 33771107 := bstep (se 1 (by rfl) ⟨25328330, by rfl⟩ : syracuseStep 33771107 = 50656661) B50656661
theorem B1756807 : Blo 1756579 1756807 := bstep (se 1 (by rfl) ⟨1317605, by rfl⟩ : syracuseStep 1756807 = 2635211) B2635211
theorem B1756815 : Blo 1756579 1756815 := bstep (se 1 (by rfl) ⟨1317611, by rfl⟩ : syracuseStep 1756815 = 2635223) B2635223
theorem B3952313 : Blo 1756579 3952313 := bstep (se 2 (by rfl) ⟨1482117, by rfl⟩ : syracuseStep 3952313 = 2964235) B2964235
theorem B1756859 : Blo 1756579 1756859 := bstep (se 1 (by rfl) ⟨1317644, by rfl⟩ : syracuseStep 1756859 = 2635289) B2635289
theorem B1756935 : Blo 1756579 1756935 := bstep (se 1 (by rfl) ⟨1317701, by rfl⟩ : syracuseStep 1756935 = 2635403) B2635403
theorem B1756943 : Blo 1756579 1756943 := bstep (se 1 (by rfl) ⟨1317707, by rfl⟩ : syracuseStep 1756943 = 2635415) B2635415
theorem B21376817 : Blo 1756579 21376817 := bstep (se 2 (by rfl) ⟨8016306, by rfl⟩ : syracuseStep 21376817 = 16032613) B16032613
theorem B1756987 : Blo 1756579 1756987 := bstep (se 1 (by rfl) ⟨1317740, by rfl⟩ : syracuseStep 1756987 = 2635481) B2635481
theorem B2223931 : Blo 1756579 2223931 := bstep (se 1 (by rfl) ⟨1667948, by rfl⟩ : syracuseStep 2223931 = 3335897) B3335897
theorem B1757063 : Blo 1756579 1757063 := bstep (se 1 (by rfl) ⟨1317797, by rfl⟩ : syracuseStep 1757063 = 2635595) B2635595
theorem B1757071 : Blo 1756579 1757071 := bstep (se 1 (by rfl) ⟨1317803, by rfl⟩ : syracuseStep 1757071 = 2635607) B2635607
theorem B1757115 : Blo 1756579 1757115 := bstep (se 1 (by rfl) ⟨1317836, by rfl⟩ : syracuseStep 1757115 = 2635673) B2635673
theorem B73150411 : Blo 1756579 73150411 := bstep (se 1 (by rfl) ⟨54862808, by rfl⟩ : syracuseStep 73150411 = 109725617) B109725617
theorem B1757191 : Blo 1756579 1757191 := bstep (se 1 (by rfl) ⟨1317893, by rfl⟩ : syracuseStep 1757191 = 2635787) B2635787
theorem B3952655 : Blo 1756579 3952655 := bstep (se 1 (by rfl) ⟨2964491, by rfl⟩ : syracuseStep 3952655 = 5928983) B5928983
theorem B1757199 : Blo 1756579 1757199 := bstep (se 1 (by rfl) ⟨1317899, by rfl⟩ : syracuseStep 1757199 = 2635799) B2635799
theorem B3952673 : Blo 1756579 3952673 := bstep (se 2 (by rfl) ⟨1482252, by rfl⟩ : syracuseStep 3952673 = 2964505) B2964505
theorem B1757243 : Blo 1756579 1757243 := bstep (se 1 (by rfl) ⟨1317932, by rfl⟩ : syracuseStep 1757243 = 2635865) B2635865
theorem B1757319 : Blo 1756579 1757319 := bstep (se 1 (by rfl) ⟨1317989, by rfl⟩ : syracuseStep 1757319 = 2635979) B2635979
theorem B1757327 : Blo 1756579 1757327 := bstep (se 1 (by rfl) ⟨1317995, by rfl⟩ : syracuseStep 1757327 = 2635991) B2635991
theorem B27046061 : Blo 1756579 27046061 := bstep (se 3 (by rfl) ⟨5071136, by rfl⟩ : syracuseStep 27046061 = 10142273) B10142273
theorem B1757371 : Blo 1756579 1757371 := bstep (se 1 (by rfl) ⟨1318028, by rfl⟩ : syracuseStep 1757371 = 2636057) B2636057
theorem B1757447 : Blo 1756579 1757447 := bstep (se 1 (by rfl) ⟨1318085, by rfl⟩ : syracuseStep 1757447 = 2636171) B2636171
theorem B1757455 : Blo 1756579 1757455 := bstep (se 1 (by rfl) ⟨1318091, by rfl⟩ : syracuseStep 1757455 = 2636183) B2636183
theorem B1757499 : Blo 1756579 1757499 := bstep (se 1 (by rfl) ⟨1318124, by rfl⟩ : syracuseStep 1757499 = 2636249) B2636249
theorem B3953015 : Blo 1756579 3953015 := bstep (se 1 (by rfl) ⟨2964761, by rfl⟩ : syracuseStep 3953015 = 5929523) B5929523
theorem B11260295 : Blo 1756579 11260295 := bstep (se 1 (by rfl) ⟨8445221, by rfl⟩ : syracuseStep 11260295 = 16890443) B16890443
theorem B1757575 : Blo 1756579 1757575 := bstep (se 1 (by rfl) ⟨1318181, by rfl⟩ : syracuseStep 1757575 = 2636363) B2636363
theorem B1757583 : Blo 1756579 1757583 := bstep (se 1 (by rfl) ⟨1318187, by rfl⟩ : syracuseStep 1757583 = 2636375) B2636375
theorem B5140883 : Blo 1756579 5140883 := bstep (se 1 (by rfl) ⟨3855662, by rfl⟩ : syracuseStep 5140883 = 7711325) B7711325
theorem B1757627 : Blo 1756579 1757627 := bstep (se 1 (by rfl) ⟨1318220, by rfl⟩ : syracuseStep 1757627 = 2636441) B2636441
theorem B27054557 : Blo 1756579 27054557 := bstep (se 3 (by rfl) ⟨5072729, by rfl⟩ : syracuseStep 27054557 = 10145459) B10145459
theorem B1757703 : Blo 1756579 1757703 := bstep (se 1 (by rfl) ⟨1318277, by rfl⟩ : syracuseStep 1757703 = 2636555) B2636555
theorem B1757711 : Blo 1756579 1757711 := bstep (se 1 (by rfl) ⟨1318283, by rfl⟩ : syracuseStep 1757711 = 2636567) B2636567
theorem B3953195 : Blo 1756579 3953195 := bstep (se 1 (by rfl) ⟨2964896, by rfl⟩ : syracuseStep 3953195 = 5929793) B5929793
theorem B1757755 : Blo 1756579 1757755 := bstep (se 1 (by rfl) ⟨1318316, by rfl⟩ : syracuseStep 1757755 = 2636633) B2636633
theorem B8892989 : Blo 1756579 8892989 := bstep (se 3 (by rfl) ⟨1667435, by rfl⟩ : syracuseStep 8892989 = 3334871) B3334871
theorem B20009591 : Blo 1756579 20009591 := bstep (se 1 (by rfl) ⟨15007193, by rfl⟩ : syracuseStep 20009591 = 30014387) B30014387
theorem B1757831 : Blo 1756579 1757831 := bstep (se 1 (by rfl) ⟨1318373, by rfl⟩ : syracuseStep 1757831 = 2636747) B2636747
theorem B1757839 : Blo 1756579 1757839 := bstep (se 1 (by rfl) ⟨1318379, by rfl⟩ : syracuseStep 1757839 = 2636759) B2636759
theorem B1757883 : Blo 1756579 1757883 := bstep (se 1 (by rfl) ⟨1318412, by rfl⟩ : syracuseStep 1757883 = 2636825) B2636825
theorem B2224903 : Blo 1756579 2224903 := bstep (se 1 (by rfl) ⟨1668677, by rfl⟩ : syracuseStep 2224903 = 3337355) B3337355
theorem B1757959 : Blo 1756579 1757959 := bstep (se 1 (by rfl) ⟨1318469, by rfl⟩ : syracuseStep 1757959 = 2636939) B2636939
theorem B7123727 : Blo 1756579 7123727 := bstep (se 1 (by rfl) ⟨5342795, by rfl⟩ : syracuseStep 7123727 = 10685591) B10685591
theorem B1757967 : Blo 1756579 1757967 := bstep (se 1 (by rfl) ⟨1318475, by rfl⟩ : syracuseStep 1757967 = 2636951) B2636951
theorem B10007347 : Blo 1756579 10007347 := bstep (se 1 (by rfl) ⟨7505510, by rfl⟩ : syracuseStep 10007347 = 15011021) B15011021
theorem B1758011 : Blo 1756579 1758011 := bstep (se 1 (by rfl) ⟨1318508, by rfl⟩ : syracuseStep 1758011 = 2637017) B2637017
theorem B3167095 : Blo 1756579 3167095 := bstep (se 1 (by rfl) ⟨2375321, by rfl⟩ : syracuseStep 3167095 = 4750643) B4750643
theorem B3953555 : Blo 1756579 3953555 := bstep (se 1 (by rfl) ⟨2965166, by rfl⟩ : syracuseStep 3953555 = 5930333) B5930333
theorem B7820185 : Blo 1756579 7820185 := bstep (se 2 (by rfl) ⟨2932569, by rfl⟩ : syracuseStep 7820185 = 5865139) B5865139
theorem B3953609 : Blo 1756579 3953609 := bstep (se 2 (by rfl) ⟨1482603, by rfl⟩ : syracuseStep 3953609 = 2965207) B2965207
theorem B2708537 : Blo 1756579 2708537 := bstep (se 2 (by rfl) ⟨1015701, by rfl⟩ : syracuseStep 2708537 = 2031403) B2031403
theorem B2634887 : Blo 1756579 2634887 := bstep (se 1 (by rfl) ⟨1976165, by rfl⟩ : syracuseStep 2634887 = 3952331) B3952331
theorem B2634923 : Blo 1756579 2634923 := bstep (se 1 (by rfl) ⟨1976192, by rfl⟩ : syracuseStep 2634923 = 3952385) B3952385
theorem B2634953 : Blo 1756579 2634953 := bstep (se 2 (by rfl) ⟨988107, by rfl⟩ : syracuseStep 2634953 = 1976215) B1976215
theorem B2635067 : Blo 1756579 2635067 := bstep (se 1 (by rfl) ⟨1976300, by rfl⟩ : syracuseStep 2635067 = 3952601) B3952601
theorem B4814167 : Blo 1756579 4814167 := bstep (se 1 (by rfl) ⟨3610625, by rfl⟩ : syracuseStep 4814167 = 7221251) B7221251
theorem B2635127 : Blo 1756579 2635127 := bstep (se 1 (by rfl) ⟨1976345, by rfl⟩ : syracuseStep 2635127 = 3952691) B3952691
theorem B2635151 : Blo 1756579 2635151 := bstep (se 1 (by rfl) ⟨1976363, by rfl⟩ : syracuseStep 2635151 = 3952727) B3952727
theorem B2635193 : Blo 1756579 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B6673873 : Blo 1756579 6673873 := bstep (se 2 (by rfl) ⟨2502702, by rfl⟩ : syracuseStep 6673873 = 5005405) B5005405
theorem B2635271 : Blo 1756579 2635271 := bstep (se 1 (by rfl) ⟨1976453, by rfl⟩ : syracuseStep 2635271 = 3952907) B3952907
theorem B2635307 : Blo 1756579 2635307 := bstep (se 1 (by rfl) ⟨1976480, by rfl⟩ : syracuseStep 2635307 = 3952961) B3952961
theorem B2635337 : Blo 1756579 2635337 := bstep (se 2 (by rfl) ⟨988251, by rfl⟩ : syracuseStep 2635337 = 1976503) B1976503
theorem B3954311 : Blo 1756579 3954311 := bstep (se 1 (by rfl) ⟨2965733, by rfl⟩ : syracuseStep 3954311 = 5931467) B5931467
theorem B42759859 : Blo 1756579 42759859 := bstep (se 1 (by rfl) ⟨32069894, by rfl⟩ : syracuseStep 42759859 = 64139789) B64139789
theorem B2635451 : Blo 1756579 2635451 := bstep (se 1 (by rfl) ⟨1976588, by rfl⟩ : syracuseStep 2635451 = 3953177) B3953177
theorem B2635511 : Blo 1756579 2635511 := bstep (se 1 (by rfl) ⟨1976633, by rfl⟩ : syracuseStep 2635511 = 3953267) B3953267
theorem B6674177 : Blo 1756579 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B2635535 : Blo 1756579 2635535 := bstep (se 1 (by rfl) ⟨1976651, by rfl⟩ : syracuseStep 2635535 = 3953303) B3953303
theorem B8017679 : Blo 1756579 8017679 := bstep (se 1 (by rfl) ⟨6013259, by rfl⟩ : syracuseStep 8017679 = 12026519) B12026519
theorem B2815759 : Blo 1756579 2815759 := bstep (se 1 (by rfl) ⟨2111819, by rfl⟩ : syracuseStep 2815759 = 4223639) B4223639
theorem B2635577 : Blo 1756579 2635577 := bstep (se 2 (by rfl) ⟨988341, by rfl⟩ : syracuseStep 2635577 = 1976683) B1976683
theorem B3954491 : Blo 1756579 3954491 := bstep (se 1 (by rfl) ⟨2965868, by rfl⟩ : syracuseStep 3954491 = 5931737) B5931737
theorem B2635655 : Blo 1756579 2635655 := bstep (se 1 (by rfl) ⟨1976741, by rfl⟩ : syracuseStep 2635655 = 3953483) B3953483
theorem B2635691 : Blo 1756579 2635691 := bstep (se 1 (by rfl) ⟨1976768, by rfl⟩ : syracuseStep 2635691 = 3953537) B3953537
theorem B3954617 : Blo 1756579 3954617 := bstep (se 2 (by rfl) ⟨1482981, by rfl⟩ : syracuseStep 3954617 = 2965963) B2965963
theorem B2635721 : Blo 1756579 2635721 := bstep (se 2 (by rfl) ⟨988395, by rfl⟩ : syracuseStep 2635721 = 1976791) B1976791
theorem B2635835 : Blo 1756579 2635835 := bstep (se 1 (by rfl) ⟨1976876, by rfl⟩ : syracuseStep 2635835 = 3953753) B3953753
theorem B2635895 : Blo 1756579 2635895 := bstep (se 1 (by rfl) ⟨1976921, by rfl⟩ : syracuseStep 2635895 = 3953843) B3953843
theorem B2635919 : Blo 1756579 2635919 := bstep (se 1 (by rfl) ⟨1976939, by rfl⟩ : syracuseStep 2635919 = 3953879) B3953879
theorem B2635961 : Blo 1756579 2635961 := bstep (se 2 (by rfl) ⟨988485, by rfl⟩ : syracuseStep 2635961 = 1976971) B1976971
theorem B2111675 : Blo 1756579 2111675 := bstep (se 1 (by rfl) ⟨1583756, by rfl⟩ : syracuseStep 2111675 = 3167513) B3167513
theorem B6674633 : Blo 1756579 6674633 := bstep (se 2 (by rfl) ⟨2502987, by rfl⟩ : syracuseStep 6674633 = 5005975) B5005975
theorem B10008805 : Blo 1756579 10008805 := bstep (se 4 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 10008805 = 1876651) B1876651
theorem B2636039 : Blo 1756579 2636039 := bstep (se 1 (by rfl) ⟨1977029, by rfl⟩ : syracuseStep 2636039 = 3954059) B3954059
theorem B3954959 : Blo 1756579 3954959 := bstep (se 1 (by rfl) ⟨2966219, by rfl⟩ : syracuseStep 3954959 = 5932439) B5932439
theorem B3954977 : Blo 1756579 3954977 := bstep (se 2 (by rfl) ⟨1483116, by rfl⟩ : syracuseStep 3954977 = 2966233) B2966233
theorem B2636075 : Blo 1756579 2636075 := bstep (se 1 (by rfl) ⟨1977056, by rfl⟩ : syracuseStep 2636075 = 3954113) B3954113
theorem B8894771 : Blo 1756579 8894771 := bstep (se 1 (by rfl) ⟨6671078, by rfl⟩ : syracuseStep 8894771 = 13342157) B13342157
theorem B2636105 : Blo 1756579 2636105 := bstep (se 2 (by rfl) ⟨988539, by rfl⟩ : syracuseStep 2636105 = 1977079) B1977079
theorem B22509971 : Blo 1756579 22509971 := bstep (se 1 (by rfl) ⟨16882478, by rfl⟩ : syracuseStep 22509971 = 33764957) B33764957
theorem B2636219 : Blo 1756579 2636219 := bstep (se 1 (by rfl) ⟨1977164, by rfl⟩ : syracuseStep 2636219 = 3954329) B3954329
theorem B2636279 : Blo 1756579 2636279 := bstep (se 1 (by rfl) ⟨1977209, by rfl⟩ : syracuseStep 2636279 = 3954419) B3954419
theorem B2636303 : Blo 1756579 2636303 := bstep (se 1 (by rfl) ⟨1977227, by rfl⟩ : syracuseStep 2636303 = 3954455) B3954455
theorem B2636345 : Blo 1756579 2636345 := bstep (se 2 (by rfl) ⟨988629, by rfl⟩ : syracuseStep 2636345 = 1977259) B1977259
theorem B4446839 : Blo 1756579 4446839 := bstep (se 1 (by rfl) ⟨3335129, by rfl⟩ : syracuseStep 4446839 = 6670259) B6670259
theorem B3005047 : Blo 1756579 3005047 := bstep (se 1 (by rfl) ⟨2253785, by rfl⟩ : syracuseStep 3005047 = 4507571) B4507571
theorem B8895095 : Blo 1756579 8895095 := bstep (se 1 (by rfl) ⟨6671321, by rfl⟩ : syracuseStep 8895095 = 13342643) B13342643
theorem B3955319 : Blo 1756579 3955319 := bstep (se 1 (by rfl) ⟨2966489, by rfl⟩ : syracuseStep 3955319 = 5932979) B5932979
theorem B2636423 : Blo 1756579 2636423 := bstep (se 1 (by rfl) ⟨1977317, by rfl⟩ : syracuseStep 2636423 = 3954635) B3954635
theorem B2636459 : Blo 1756579 2636459 := bstep (se 1 (by rfl) ⟨1977344, by rfl⟩ : syracuseStep 2636459 = 3954689) B3954689
theorem B2636489 : Blo 1756579 2636489 := bstep (se 2 (by rfl) ⟨988683, by rfl⟩ : syracuseStep 2636489 = 1977367) B1977367
theorem B3955499 : Blo 1756579 3955499 := bstep (se 1 (by rfl) ⟨2966624, by rfl⟩ : syracuseStep 3955499 = 5933249) B5933249
theorem B2636603 : Blo 1756579 2636603 := bstep (se 1 (by rfl) ⟨1977452, by rfl⟩ : syracuseStep 2636603 = 3954905) B3954905
theorem B5004119 : Blo 1756579 5004119 := bstep (se 1 (by rfl) ⟨3753089, by rfl⟩ : syracuseStep 5004119 = 7506179) B7506179
theorem B2964343 : Blo 1756579 2964343 := bstep (se 1 (by rfl) ⟨2223257, by rfl⟩ : syracuseStep 2964343 = 4446515) B4446515
theorem B2636663 : Blo 1756579 2636663 := bstep (se 1 (by rfl) ⟨1977497, by rfl⟩ : syracuseStep 2636663 = 3954995) B3954995
theorem B2636687 : Blo 1756579 2636687 := bstep (se 1 (by rfl) ⟨1977515, by rfl⟩ : syracuseStep 2636687 = 3955031) B3955031
theorem B2636729 : Blo 1756579 2636729 := bstep (se 2 (by rfl) ⟨988773, by rfl⟩ : syracuseStep 2636729 = 1977547) B1977547
theorem B2636807 : Blo 1756579 2636807 := bstep (se 1 (by rfl) ⟨1977605, by rfl⟩ : syracuseStep 2636807 = 3955211) B3955211
theorem B2636843 : Blo 1756579 2636843 := bstep (se 1 (by rfl) ⟨1977632, by rfl⟩ : syracuseStep 2636843 = 3955265) B3955265
theorem B2964539 : Blo 1756579 2964539 := bstep (se 1 (by rfl) ⟨2223404, by rfl⟩ : syracuseStep 2964539 = 4446809) B4446809
theorem B2636873 : Blo 1756579 2636873 := bstep (se 2 (by rfl) ⟨988827, by rfl⟩ : syracuseStep 2636873 = 1977655) B1977655
theorem B2636987 : Blo 1756579 2636987 := bstep (se 1 (by rfl) ⟨1977740, by rfl⟩ : syracuseStep 2636987 = 3955481) B3955481
theorem B2637047 : Blo 1756579 2637047 := bstep (se 1 (by rfl) ⟨1977785, by rfl⟩ : syracuseStep 2637047 = 3955571) B3955571
theorem B2637071 : Blo 1756579 2637071 := bstep (se 1 (by rfl) ⟨1977803, by rfl⟩ : syracuseStep 2637071 = 3955607) B3955607
theorem B2637113 : Blo 1756579 2637113 := bstep (se 2 (by rfl) ⟨988917, by rfl⟩ : syracuseStep 2637113 = 1977835) B1977835
theorem B5930387 : Blo 1756579 5930387 := bstep (se 1 (by rfl) ⟨4447790, by rfl⟩ : syracuseStep 5930387 = 8895581) B8895581
theorem B9502105 : Blo 1756579 9502105 := bstep (se 2 (by rfl) ⟨3563289, by rfl⟩ : syracuseStep 9502105 = 7126579) B7126579
theorem B2964937 : Blo 1756579 2964937 := bstep (se 2 (by rfl) ⟨1111851, by rfl⟩ : syracuseStep 2964937 = 2223703) B2223703
theorem B9141803 : Blo 1756579 9141803 := bstep (se 1 (by rfl) ⟨6856352, by rfl⟩ : syracuseStep 9141803 = 13712705) B13712705
theorem B8896067 : Blo 1756579 8896067 := bstep (se 1 (by rfl) ⟨6672050, by rfl⟩ : syracuseStep 8896067 = 13344101) B13344101
theorem B4447831 : Blo 1756579 4447831 := bstep (se 1 (by rfl) ⟨3335873, by rfl⟩ : syracuseStep 4447831 = 6671747) B6671747
theorem B2571895 : Blo 1756579 2571895 := bstep (se 1 (by rfl) ⟨1928921, by rfl⟩ : syracuseStep 2571895 = 3857843) B3857843
theorem B6946541 : Blo 1756579 6946541 := bstep (se 3 (by rfl) ⟨1302476, by rfl⟩ : syracuseStep 6946541 = 2604953) B2604953
theorem B4448135 : Blo 1756579 4448135 := bstep (se 1 (by rfl) ⟨3336101, by rfl⟩ : syracuseStep 4448135 = 6672203) B6672203
theorem B8896391 : Blo 1756579 8896391 := bstep (se 1 (by rfl) ⟨6672293, by rfl⟩ : syracuseStep 8896391 = 13344587) B13344587
theorem B5627801 : Blo 1756579 5627801 := bstep (se 2 (by rfl) ⟨2110425, by rfl⟩ : syracuseStep 5627801 = 4220851) B4220851
theorem B11255705 : Blo 1756579 11255705 := bstep (se 2 (by rfl) ⟨4220889, by rfl⟩ : syracuseStep 11255705 = 8441779) B8441779
theorem B12664835 : Blo 1756579 12664835 := bstep (se 1 (by rfl) ⟨9498626, by rfl⟩ : syracuseStep 12664835 = 18997253) B18997253
theorem B2965511 : Blo 1756579 2965511 := bstep (se 1 (by rfl) ⟨2224133, by rfl⟩ : syracuseStep 2965511 = 4448267) B4448267
theorem B45047825 : Blo 1756579 45047825 := bstep (se 2 (by rfl) ⟨16892934, by rfl⟩ : syracuseStep 45047825 = 33785869) B33785869
theorem B18030707 : Blo 1756579 18030707 := bstep (se 1 (by rfl) ⟨13523030, by rfl⟩ : syracuseStep 18030707 = 27046061) B27046061
theorem B13345073 : Blo 1756579 13345073 := bstep (se 2 (by rfl) ⟨5004402, by rfl⟩ : syracuseStep 13345073 = 10008805) B10008805
theorem B2965855 : Blo 1756579 2965855 := bstep (se 1 (by rfl) ⟨2224391, by rfl⟩ : syracuseStep 2965855 = 4448783) B4448783
theorem B4448641 : Blo 1756579 4448641 := bstep (se 2 (by rfl) ⟨1668240, by rfl⟩ : syracuseStep 4448641 = 3336481) B3336481
theorem B2965943 : Blo 1756579 2965943 := bstep (se 1 (by rfl) ⟨2224457, by rfl⟩ : syracuseStep 2965943 = 4448915) B4448915
theorem B14246381 : Blo 1756579 14246381 := bstep (se 3 (by rfl) ⟨2671196, by rfl⟩ : syracuseStep 14246381 = 5342393) B5342393
theorem B7504417 : Blo 1756579 7504417 := bstep (se 2 (by rfl) ⟨2814156, by rfl⟩ : syracuseStep 7504417 = 5628313) B5628313
theorem B2966537 : Blo 1756579 2966537 := bstep (se 2 (by rfl) ⟨1112451, by rfl⟩ : syracuseStep 2966537 = 2224903) B2224903
theorem B4449451 : Blo 1756579 4449451 := bstep (se 1 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 4449451 = 6674177) B6674177
theorem B2966699 : Blo 1756579 2966699 := bstep (se 1 (by rfl) ⟨2225024, by rfl⟩ : syracuseStep 2966699 = 4450049) B4450049
theorem B8898011 : Blo 1756579 8898011 := bstep (se 1 (by rfl) ⟨6673508, by rfl⟩ : syracuseStep 8898011 = 13347017) B13347017
theorem B4449755 : Blo 1756579 4449755 := bstep (se 1 (by rfl) ⟨3337316, by rfl⟩ : syracuseStep 4449755 = 6674633) B6674633
theorem B3335737 : Blo 1756579 3335737 := bstep (se 2 (by rfl) ⟨1250901, by rfl⟩ : syracuseStep 3335737 = 2501803) B2501803
theorem B9504353 : Blo 1756579 9504353 := bstep (se 2 (by rfl) ⟨3564132, by rfl⟩ : syracuseStep 9504353 = 7128265) B7128265
theorem B6669971 : Blo 1756579 6669971 := bstep (se 1 (by rfl) ⟨5002478, by rfl⟩ : syracuseStep 6669971 = 10004957) B10004957
theorem B28493603 : Blo 1756579 28493603 := bstep (se 1 (by rfl) ⟨21370202, by rfl⟩ : syracuseStep 28493603 = 42740405) B42740405
theorem B3336041 : Blo 1756579 3336041 := bstep (se 2 (by rfl) ⟨1251015, by rfl⟩ : syracuseStep 3336041 = 2502031) B2502031
theorem B3336079 : Blo 1756579 3336079 := bstep (se 1 (by rfl) ⟨2502059, by rfl⟩ : syracuseStep 3336079 = 5004119) B5004119
theorem B12838817 : Blo 1756579 12838817 := bstep (se 2 (by rfl) ⟨4814556, by rfl⟩ : syracuseStep 12838817 = 9629113) B9629113
theorem B8898497 : Blo 1756579 8898497 := bstep (se 2 (by rfl) ⟨3336936, by rfl⟩ : syracuseStep 8898497 = 6673873) B6673873
theorem B10012679 : Blo 1756579 10012679 := bstep (se 1 (by rfl) ⟨7509509, by rfl⟩ : syracuseStep 10012679 = 15019019) B15019019
theorem B1976359 : Blo 1756579 1976359 := bstep (se 1 (by rfl) ⟨1482269, by rfl⟩ : syracuseStep 1976359 = 2964539) B2964539
theorem B5933303 : Blo 1756579 5933303 := bstep (se 1 (by rfl) ⟨4449977, by rfl⟩ : syracuseStep 5933303 = 8899955) B8899955
theorem B7506263 : Blo 1756579 7506263 := bstep (se 1 (by rfl) ⟨5629697, by rfl⟩ : syracuseStep 7506263 = 11259395) B11259395
theorem B3754345 : Blo 1756579 3754345 := bstep (se 2 (by rfl) ⟨1407879, by rfl⟩ : syracuseStep 3754345 = 2815759) B2815759
theorem B22514071 : Blo 1756579 22514071 := bstep (se 1 (by rfl) ⟨16885553, by rfl⟩ : syracuseStep 22514071 = 33771107) B33771107
theorem B4631027 : Blo 1756579 4631027 := bstep (se 1 (by rfl) ⟨3473270, by rfl⟩ : syracuseStep 4631027 = 6946541) B6946541
theorem B6335185 : Blo 1756579 6335185 := bstep (se 2 (by rfl) ⟨2375694, by rfl⟩ : syracuseStep 6335185 = 4751389) B4751389
theorem B7506863 : Blo 1756579 7506863 := bstep (se 1 (by rfl) ⟨5630147, by rfl⟩ : syracuseStep 7506863 = 11260295) B11260295
theorem B3427255 : Blo 1756579 3427255 := bstep (se 1 (by rfl) ⟨2570441, by rfl⟩ : syracuseStep 3427255 = 5140883) B5140883
theorem B5630903 : Blo 1756579 5630903 := bstep (se 1 (by rfl) ⟨4223177, by rfl⟩ : syracuseStep 5630903 = 8446355) B8446355
theorem B13339727 : Blo 1756579 13339727 := bstep (se 1 (by rfl) ⟨10004795, by rfl⟩ : syracuseStep 13339727 = 20009591) B20009591
theorem B6335603 : Blo 1756579 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B2223227 : Blo 1756579 2223227 := bstep (se 1 (by rfl) ⟨1667420, by rfl⟩ : syracuseStep 2223227 = 3334841) B3334841
theorem B5631133 : Blo 1756579 5631133 := bstep (se 3 (by rfl) ⟨1055837, by rfl⟩ : syracuseStep 5631133 = 2111675) B2111675
theorem B10005707 : Blo 1756579 10005707 := bstep (se 1 (by rfl) ⟨7504280, by rfl⟩ : syracuseStep 10005707 = 15008561) B15008561
theorem B16026917 : Blo 1756579 16026917 := bstep (se 4 (by rfl) ⟨1502523, by rfl⟩ : syracuseStep 16026917 = 3005047) B3005047
theorem B13716773 : Blo 1756579 13716773 := bstep (se 4 (by rfl) ⟨1285947, by rfl⟩ : syracuseStep 13716773 = 2571895) B2571895
theorem B4009321 : Blo 1756579 4009321 := bstep (se 2 (by rfl) ⟨1503495, by rfl⟩ : syracuseStep 4009321 = 3006991) B3006991
theorem B1756591 : Blo 1756579 1756591 := bstep (se 1 (by rfl) ⟨1317443, by rfl⟩ : syracuseStep 1756591 = 2634887) B2634887
theorem B1756615 : Blo 1756579 1756615 := bstep (se 1 (by rfl) ⟨1317461, by rfl⟩ : syracuseStep 1756615 = 2634923) B2634923
theorem B1781191 : Blo 1756579 1781191 := bstep (se 1 (by rfl) ⟨1335893, by rfl⟩ : syracuseStep 1781191 = 2671787) B2671787
theorem B1756635 : Blo 1756579 1756635 := bstep (se 1 (by rfl) ⟨1317476, by rfl⟩ : syracuseStep 1756635 = 2634953) B2634953
theorem B1756711 : Blo 1756579 1756711 := bstep (se 1 (by rfl) ⟨1317533, by rfl⟩ : syracuseStep 1756711 = 2635067) B2635067
theorem B1756751 : Blo 1756579 1756751 := bstep (se 1 (by rfl) ⟨1317563, by rfl⟩ : syracuseStep 1756751 = 2635127) B2635127
theorem B1756767 : Blo 1756579 1756767 := bstep (se 1 (by rfl) ⟨1317575, by rfl⟩ : syracuseStep 1756767 = 2635151) B2635151
theorem B1756795 : Blo 1756579 1756795 := bstep (se 1 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 1756795 = 2635193) B2635193
theorem B13348475 : Blo 1756579 13348475 := bstep (se 1 (by rfl) ⟨10011356, by rfl⟩ : syracuseStep 13348475 = 20022713) B20022713
theorem B10006163 : Blo 1756579 10006163 := bstep (se 1 (by rfl) ⟨7504622, by rfl⟩ : syracuseStep 10006163 = 15009245) B15009245
theorem B1756847 : Blo 1756579 1756847 := bstep (se 1 (by rfl) ⟨1317635, by rfl⟩ : syracuseStep 1756847 = 2635271) B2635271
theorem B5705405 : Blo 1756579 5705405 := bstep (se 3 (by rfl) ⟨1069763, by rfl⟩ : syracuseStep 5705405 = 2139527) B2139527
theorem B1756871 : Blo 1756579 1756871 := bstep (se 1 (by rfl) ⟨1317653, by rfl⟩ : syracuseStep 1756871 = 2635307) B2635307
theorem B32059097 : Blo 1756579 32059097 := bstep (se 2 (by rfl) ⟨12022161, by rfl⟩ : syracuseStep 32059097 = 24044323) B24044323
theorem B1756891 : Blo 1756579 1756891 := bstep (se 1 (by rfl) ⟨1317668, by rfl⟩ : syracuseStep 1756891 = 2635337) B2635337
theorem B23138081 : Blo 1756579 23138081 := bstep (se 2 (by rfl) ⟨8676780, by rfl⟩ : syracuseStep 23138081 = 17353561) B17353561
theorem B1756967 : Blo 1756579 1756967 := bstep (se 1 (by rfl) ⟨1317725, by rfl⟩ : syracuseStep 1756967 = 2635451) B2635451
theorem B3952457 : Blo 1756579 3952457 := bstep (se 2 (by rfl) ⟨1482171, by rfl⟩ : syracuseStep 3952457 = 2964343) B2964343
theorem B4222793 : Blo 1756579 4222793 := bstep (se 2 (by rfl) ⟨1583547, by rfl⟩ : syracuseStep 4222793 = 3167095) B3167095
theorem B1757007 : Blo 1756579 1757007 := bstep (se 1 (by rfl) ⟨1317755, by rfl⟩ : syracuseStep 1757007 = 2635511) B2635511
theorem B1757023 : Blo 1756579 1757023 := bstep (se 1 (by rfl) ⟨1317767, by rfl⟩ : syracuseStep 1757023 = 2635535) B2635535
theorem B5345119 : Blo 1756579 5345119 := bstep (se 1 (by rfl) ⟨4008839, by rfl⟩ : syracuseStep 5345119 = 8017679) B8017679
theorem B1757051 : Blo 1756579 1757051 := bstep (se 1 (by rfl) ⟨1317788, by rfl⟩ : syracuseStep 1757051 = 2635577) B2635577
theorem B1757103 : Blo 1756579 1757103 := bstep (se 1 (by rfl) ⟨1317827, by rfl⟩ : syracuseStep 1757103 = 2635655) B2635655
theorem B1757127 : Blo 1756579 1757127 := bstep (se 1 (by rfl) ⟨1317845, by rfl⟩ : syracuseStep 1757127 = 2635691) B2635691
theorem B1757147 : Blo 1756579 1757147 := bstep (se 1 (by rfl) ⟨1317860, by rfl⟩ : syracuseStep 1757147 = 2635721) B2635721
theorem B1757223 : Blo 1756579 1757223 := bstep (se 1 (by rfl) ⟨1317917, by rfl⟩ : syracuseStep 1757223 = 2635835) B2635835
theorem B1757263 : Blo 1756579 1757263 := bstep (se 1 (by rfl) ⟨1317947, by rfl⟩ : syracuseStep 1757263 = 2635895) B2635895
theorem B1757279 : Blo 1756579 1757279 := bstep (se 1 (by rfl) ⟨1317959, by rfl⟩ : syracuseStep 1757279 = 2635919) B2635919
theorem B1757307 : Blo 1756579 1757307 := bstep (se 1 (by rfl) ⟨1317980, by rfl⟩ : syracuseStep 1757307 = 2635961) B2635961
theorem B1757359 : Blo 1756579 1757359 := bstep (se 1 (by rfl) ⟨1318019, by rfl⟩ : syracuseStep 1757359 = 2636039) B2636039
theorem B111194291 : Blo 1756579 111194291 := bstep (se 1 (by rfl) ⟨83395718, by rfl⟩ : syracuseStep 111194291 = 166791437) B166791437
theorem B1757383 : Blo 1756579 1757383 := bstep (se 1 (by rfl) ⟨1318037, by rfl⟩ : syracuseStep 1757383 = 2636075) B2636075
theorem B1757403 : Blo 1756579 1757403 := bstep (se 1 (by rfl) ⟨1318052, by rfl⟩ : syracuseStep 1757403 = 2636105) B2636105
theorem B1757479 : Blo 1756579 1757479 := bstep (se 1 (by rfl) ⟨1318109, by rfl⟩ : syracuseStep 1757479 = 2636219) B2636219
theorem B1757519 : Blo 1756579 1757519 := bstep (se 1 (by rfl) ⟨1318139, by rfl⟩ : syracuseStep 1757519 = 2636279) B2636279
theorem B1757535 : Blo 1756579 1757535 := bstep (se 1 (by rfl) ⟨1318151, by rfl⟩ : syracuseStep 1757535 = 2636303) B2636303
theorem B1757563 : Blo 1756579 1757563 := bstep (se 1 (by rfl) ⟨1318172, by rfl⟩ : syracuseStep 1757563 = 2636345) B2636345
theorem B1757615 : Blo 1756579 1757615 := bstep (se 1 (by rfl) ⟨1318211, by rfl⟩ : syracuseStep 1757615 = 2636423) B2636423
theorem B1757639 : Blo 1756579 1757639 := bstep (se 1 (by rfl) ⟨1318229, by rfl⟩ : syracuseStep 1757639 = 2636459) B2636459
theorem B6418889 : Blo 1756579 6418889 := bstep (se 2 (by rfl) ⟨2407083, by rfl⟩ : syracuseStep 6418889 = 4814167) B4814167
theorem B1757659 : Blo 1756579 1757659 := bstep (se 1 (by rfl) ⟨1318244, by rfl⟩ : syracuseStep 1757659 = 2636489) B2636489
theorem B12669473 : Blo 1756579 12669473 := bstep (se 2 (by rfl) ⟨4751052, by rfl⟩ : syracuseStep 12669473 = 9502105) B9502105
theorem B1757735 : Blo 1756579 1757735 := bstep (se 1 (by rfl) ⟨1318301, by rfl⟩ : syracuseStep 1757735 = 2636603) B2636603
theorem B1757775 : Blo 1756579 1757775 := bstep (se 1 (by rfl) ⟨1318331, by rfl⟩ : syracuseStep 1757775 = 2636663) B2636663
theorem B1757791 : Blo 1756579 1757791 := bstep (se 1 (by rfl) ⟨1318343, by rfl⟩ : syracuseStep 1757791 = 2636687) B2636687
theorem B3953249 : Blo 1756579 3953249 := bstep (se 2 (by rfl) ⟨1482468, by rfl⟩ : syracuseStep 3953249 = 2964937) B2964937
theorem B1757819 : Blo 1756579 1757819 := bstep (se 1 (by rfl) ⟨1318364, by rfl⟩ : syracuseStep 1757819 = 2636729) B2636729
theorem B1757871 : Blo 1756579 1757871 := bstep (se 1 (by rfl) ⟨1318403, by rfl⟩ : syracuseStep 1757871 = 2636807) B2636807
theorem B1757895 : Blo 1756579 1757895 := bstep (se 1 (by rfl) ⟨1318421, by rfl⟩ : syracuseStep 1757895 = 2636843) B2636843
theorem B1757915 : Blo 1756579 1757915 := bstep (se 1 (by rfl) ⟨1318436, by rfl⟩ : syracuseStep 1757915 = 2636873) B2636873
theorem B1757991 : Blo 1756579 1757991 := bstep (se 1 (by rfl) ⟨1318493, by rfl⟩ : syracuseStep 1757991 = 2636987) B2636987
theorem B1758031 : Blo 1756579 1758031 := bstep (se 1 (by rfl) ⟨1318523, by rfl⟩ : syracuseStep 1758031 = 2637047) B2637047
theorem B1758047 : Blo 1756579 1758047 := bstep (se 1 (by rfl) ⟨1318535, by rfl⟩ : syracuseStep 1758047 = 2637071) B2637071
theorem B1758075 : Blo 1756579 1758075 := bstep (se 1 (by rfl) ⟨1318556, by rfl⟩ : syracuseStep 1758075 = 2637113) B2637113
theorem B57013145 : Blo 1756579 57013145 := bstep (se 2 (by rfl) ⟨21379929, by rfl⟩ : syracuseStep 57013145 = 42759859) B42759859
theorem B3953591 : Blo 1756579 3953591 := bstep (se 1 (by rfl) ⟨2965193, by rfl⟩ : syracuseStep 3953591 = 5930387) B5930387
theorem B4223927 : Blo 1756579 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B2634875 : Blo 1756579 2634875 := bstep (se 1 (by rfl) ⟨1976156, by rfl⟩ : syracuseStep 2634875 = 3952313) B3952313
theorem B14251211 : Blo 1756579 14251211 := bstep (se 1 (by rfl) ⟨10688408, by rfl⟩ : syracuseStep 14251211 = 21376817) B21376817
theorem B2635001 : Blo 1756579 2635001 := bstep (se 2 (by rfl) ⟨988125, by rfl⟩ : syracuseStep 2635001 = 1976251) B1976251
theorem B2635103 : Blo 1756579 2635103 := bstep (se 1 (by rfl) ⟨1976327, by rfl⟩ : syracuseStep 2635103 = 3952655) B3952655
theorem B2708831 : Blo 1756579 2708831 := bstep (se 1 (by rfl) ⟨2031623, by rfl⟩ : syracuseStep 2708831 = 4063247) B4063247
theorem B2635115 : Blo 1756579 2635115 := bstep (se 1 (by rfl) ⟨1976336, by rfl⟩ : syracuseStep 2635115 = 3952673) B3952673
theorem B7222765 : Blo 1756579 7222765 := bstep (se 3 (by rfl) ⟨1354268, by rfl⟩ : syracuseStep 7222765 = 2708537) B2708537
theorem B3954185 : Blo 1756579 3954185 := bstep (se 2 (by rfl) ⟨1482819, by rfl⟩ : syracuseStep 3954185 = 2965639) B2965639
theorem B2635343 : Blo 1756579 2635343 := bstep (se 1 (by rfl) ⟨1976507, by rfl⟩ : syracuseStep 2635343 = 3953015) B3953015
theorem B18036371 : Blo 1756579 18036371 := bstep (se 1 (by rfl) ⟨13527278, by rfl⟩ : syracuseStep 18036371 = 27054557) B27054557
theorem B2635463 : Blo 1756579 2635463 := bstep (se 1 (by rfl) ⟨1976597, by rfl⟩ : syracuseStep 2635463 = 3953195) B3953195
theorem B2004679 : Blo 1756579 2004679 := bstep (se 1 (by rfl) ⟨1503509, by rfl⟩ : syracuseStep 2004679 = 3007019) B3007019
theorem B5928659 : Blo 1756579 5928659 := bstep (se 1 (by rfl) ⟨4446494, by rfl⟩ : syracuseStep 5928659 = 8892989) B8892989
theorem B4749151 : Blo 1756579 4749151 := bstep (se 1 (by rfl) ⟨3561863, by rfl⟩ : syracuseStep 4749151 = 7123727) B7123727
theorem B3954527 : Blo 1756579 3954527 := bstep (se 1 (by rfl) ⟨2965895, by rfl⟩ : syracuseStep 3954527 = 5931791) B5931791
theorem B2635625 : Blo 1756579 2635625 := bstep (se 2 (by rfl) ⟨988359, by rfl⟩ : syracuseStep 2635625 = 1976719) B1976719
theorem B2635703 : Blo 1756579 2635703 := bstep (se 1 (by rfl) ⟨1976777, by rfl⟩ : syracuseStep 2635703 = 3953555) B3953555
theorem B6674359 : Blo 1756579 6674359 := bstep (se 1 (by rfl) ⟨5005769, by rfl⟩ : syracuseStep 6674359 = 10011539) B10011539
theorem B2635739 : Blo 1756579 2635739 := bstep (se 1 (by rfl) ⟨1976804, by rfl⟩ : syracuseStep 2635739 = 3953609) B3953609
theorem B3954707 : Blo 1756579 3954707 := bstep (se 1 (by rfl) ⟨2966030, by rfl⟩ : syracuseStep 3954707 = 5932061) B5932061
theorem B3955049 : Blo 1756579 3955049 := bstep (se 2 (by rfl) ⟨1483143, by rfl⟩ : syracuseStep 3955049 = 2966287) B2966287
theorem B6674831 : Blo 1756579 6674831 := bstep (se 1 (by rfl) ⟨5006123, by rfl⟩ : syracuseStep 6674831 = 10012247) B10012247
theorem B13343129 : Blo 1756579 13343129 := bstep (se 2 (by rfl) ⟨5003673, by rfl⟩ : syracuseStep 13343129 = 10007347) B10007347
theorem B2636207 : Blo 1756579 2636207 := bstep (se 1 (by rfl) ⟨1977155, by rfl⟩ : syracuseStep 2636207 = 3954311) B3954311
theorem B2636297 : Blo 1756579 2636297 := bstep (se 2 (by rfl) ⟨988611, by rfl⟩ : syracuseStep 2636297 = 1977223) B1977223
theorem B10426913 : Blo 1756579 10426913 := bstep (se 2 (by rfl) ⟨3910092, by rfl⟩ : syracuseStep 10426913 = 7820185) B7820185
theorem B2636327 : Blo 1756579 2636327 := bstep (se 1 (by rfl) ⟨1977245, by rfl⟩ : syracuseStep 2636327 = 3954491) B3954491
theorem B2636411 : Blo 1756579 2636411 := bstep (se 1 (by rfl) ⟨1977308, by rfl⟩ : syracuseStep 2636411 = 3954617) B3954617
theorem B4446859 : Blo 1756579 4446859 := bstep (se 1 (by rfl) ⟨3335144, by rfl⟩ : syracuseStep 4446859 = 6670289) B6670289
theorem B2636537 : Blo 1756579 2636537 := bstep (se 2 (by rfl) ⟨988701, by rfl⟩ : syracuseStep 2636537 = 1977403) B1977403
theorem B2636639 : Blo 1756579 2636639 := bstep (se 1 (by rfl) ⟨1977479, by rfl⟩ : syracuseStep 2636639 = 3954959) B3954959
theorem B2636651 : Blo 1756579 2636651 := bstep (se 1 (by rfl) ⟨1977488, by rfl⟩ : syracuseStep 2636651 = 3954977) B3954977
theorem B5929847 : Blo 1756579 5929847 := bstep (se 1 (by rfl) ⟨4447385, by rfl⟩ : syracuseStep 5929847 = 8894771) B8894771
theorem B15006647 : Blo 1756579 15006647 := bstep (se 1 (by rfl) ⟨11254985, by rfl⟩ : syracuseStep 15006647 = 22509971) B22509971
theorem B4447163 : Blo 1756579 4447163 := bstep (se 1 (by rfl) ⟨3335372, by rfl⟩ : syracuseStep 4447163 = 6670745) B6670745
theorem B3955643 : Blo 1756579 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B2964559 : Blo 1756579 2964559 := bstep (se 1 (by rfl) ⟨2223419, by rfl⟩ : syracuseStep 2964559 = 4446839) B4446839
theorem B5930063 : Blo 1756579 5930063 := bstep (se 1 (by rfl) ⟨4447547, by rfl⟩ : syracuseStep 5930063 = 8895095) B8895095
theorem B7609423 : Blo 1756579 7609423 := bstep (se 1 (by rfl) ⟨5707067, by rfl⟩ : syracuseStep 7609423 = 11414135) B11414135
theorem B2636879 : Blo 1756579 2636879 := bstep (se 1 (by rfl) ⟨1977659, by rfl⟩ : syracuseStep 2636879 = 3955319) B3955319
theorem B2636999 : Blo 1756579 2636999 := bstep (se 1 (by rfl) ⟨1977749, by rfl⟩ : syracuseStep 2636999 = 3955499) B3955499
theorem B2964809 : Blo 1756579 2964809 := bstep (se 2 (by rfl) ⟨1111803, by rfl⟩ : syracuseStep 2964809 = 2223607) B2223607
theorem B5930441 : Blo 1756579 5930441 := bstep (se 2 (by rfl) ⟨2223915, by rfl⟩ : syracuseStep 5930441 = 4447831) B4447831
theorem B4447943 : Blo 1756579 4447943 := bstep (se 1 (by rfl) ⟨3335957, by rfl⟩ : syracuseStep 4447943 = 6671915) B6671915
theorem B2285255 : Blo 1756579 2285255 := bstep (se 1 (by rfl) ⟨1713941, by rfl⟩ : syracuseStep 2285255 = 3427883) B3427883
theorem B6094535 : Blo 1756579 6094535 := bstep (se 1 (by rfl) ⟨4570901, by rfl⟩ : syracuseStep 6094535 = 9141803) B9141803
theorem B5930711 : Blo 1756579 5930711 := bstep (se 1 (by rfl) ⟨4448033, by rfl⟩ : syracuseStep 5930711 = 8896067) B8896067
theorem B2965241 : Blo 1756579 2965241 := bstep (se 2 (by rfl) ⟨1111965, by rfl⟩ : syracuseStep 2965241 = 2223931) B2223931
theorem B4447993 : Blo 1756579 4447993 := bstep (se 2 (by rfl) ⟨1667997, by rfl⟩ : syracuseStep 4447993 = 3335995) B3335995
theorem B2965423 : Blo 1756579 2965423 := bstep (se 1 (by rfl) ⟨2224067, by rfl⟩ : syracuseStep 2965423 = 4448135) B4448135
theorem B5930927 : Blo 1756579 5930927 := bstep (se 1 (by rfl) ⟨4448195, by rfl⟩ : syracuseStep 5930927 = 8896391) B8896391
theorem B97533881 : Blo 1756579 97533881 := bstep (se 2 (by rfl) ⟨36575205, by rfl⟩ : syracuseStep 97533881 = 73150411) B73150411
theorem B3751867 : Blo 1756579 3751867 := bstep (se 1 (by rfl) ⟨2813900, by rfl⟩ : syracuseStep 3751867 = 5627801) B5627801
theorem B7503803 : Blo 1756579 7503803 := bstep (se 1 (by rfl) ⟨5627852, by rfl⟩ : syracuseStep 7503803 = 11255705) B11255705
theorem B30031883 : Blo 1756579 30031883 := bstep (se 1 (by rfl) ⟨22523912, by rfl⟩ : syracuseStep 30031883 = 45047825) B45047825
theorem B74129527 : Blo 1756579 74129527 := bstep (se 1 (by rfl) ⟨55597145, by rfl⟩ : syracuseStep 74129527 = 111194291) B111194291
theorem B8896715 : Blo 1756579 8896715 := bstep (se 1 (by rfl) ⟨6672536, by rfl⟩ : syracuseStep 8896715 = 13345073) B13345073
theorem B8446315 : Blo 1756579 8446315 := bstep (se 1 (by rfl) ⟨6334736, by rfl⟩ : syracuseStep 8446315 = 12669473) B12669473
theorem B5005793 : Blo 1756579 5005793 := bstep (se 2 (by rfl) ⟨1877172, by rfl⟩ : syracuseStep 5005793 = 3754345) B3754345
theorem B5931521 : Blo 1756579 5931521 := bstep (se 2 (by rfl) ⟨2224320, by rfl⟩ : syracuseStep 5931521 = 4448641) B4448641
theorem B42738445 : Blo 1756579 42738445 := bstep (se 3 (by rfl) ⟨8013458, by rfl⟩ : syracuseStep 42738445 = 16026917) B16026917
theorem B8446913 : Blo 1756579 8446913 := bstep (se 2 (by rfl) ⟨3167592, by rfl⟩ : syracuseStep 8446913 = 6335185) B6335185
theorem B5932007 : Blo 1756579 5932007 := bstep (se 1 (by rfl) ⟨4449005, by rfl⟩ : syracuseStep 5932007 = 8898011) B8898011
theorem B2966503 : Blo 1756579 2966503 := bstep (se 1 (by rfl) ⟨2224877, by rfl⟩ : syracuseStep 2966503 = 4449755) B4449755
theorem B5932331 : Blo 1756579 5932331 := bstep (se 1 (by rfl) ⟨4449248, by rfl⟩ : syracuseStep 5932331 = 8898497) B8898497
theorem B5932601 : Blo 1756579 5932601 := bstep (se 2 (by rfl) ⟨2224725, by rfl⟩ : syracuseStep 5932601 = 4449451) B4449451
theorem B4449887 : Blo 1756579 4449887 := bstep (se 1 (by rfl) ⟨3337415, by rfl⟩ : syracuseStep 4449887 = 6674831) B6674831
theorem B10004431 : Blo 1756579 10004431 := bstep (se 1 (by rfl) ⟨7503323, by rfl⟩ : syracuseStep 10004431 = 15006647) B15006647
theorem B3753935 : Blo 1756579 3753935 := bstep (se 1 (by rfl) ⟨2815451, by rfl⟩ : syracuseStep 3753935 = 5630903) B5630903
theorem B6670471 : Blo 1756579 6670471 := bstep (se 1 (by rfl) ⟨5002853, by rfl⟩ : syracuseStep 6670471 = 10005707) B10005707
theorem B9144515 : Blo 1756579 9144515 := bstep (se 1 (by rfl) ⟨6858386, by rfl⟩ : syracuseStep 9144515 = 13716773) B13716773
theorem B1976539 : Blo 1756579 1976539 := bstep (se 1 (by rfl) ⟨1482404, by rfl⟩ : syracuseStep 1976539 = 2964809) B2964809
theorem B2672905 : Blo 1756579 2672905 := bstep (se 2 (by rfl) ⟨1002339, by rfl⟩ : syracuseStep 2672905 = 2004679) B2004679
theorem B18278693 : Blo 1756579 18278693 := bstep (se 4 (by rfl) ⟨1713627, by rfl⟩ : syracuseStep 18278693 = 3427255) B3427255
theorem B8898983 : Blo 1756579 8898983 := bstep (se 1 (by rfl) ⟨6674237, by rfl⟩ : syracuseStep 8898983 = 13348475) B13348475
theorem B34236845 : Blo 1756579 34236845 := bstep (se 3 (by rfl) ⟨6419408, by rfl⟩ : syracuseStep 34236845 = 12838817) B12838817
theorem B6670775 : Blo 1756579 6670775 := bstep (se 1 (by rfl) ⟨5003081, by rfl⟩ : syracuseStep 6670775 = 10006163) B10006163
theorem B3803603 : Blo 1756579 3803603 := bstep (se 1 (by rfl) ⟨2852702, by rfl⟩ : syracuseStep 3803603 = 5705405) B5705405
theorem B1976827 : Blo 1756579 1976827 := bstep (se 1 (by rfl) ⟨1482620, by rfl⟩ : syracuseStep 1976827 = 2965241) B2965241
theorem B8899145 : Blo 1756579 8899145 := bstep (se 2 (by rfl) ⟨3337179, by rfl⟩ : syracuseStep 8899145 = 6674359) B6674359
theorem B65022587 : Blo 1756579 65022587 := bstep (se 1 (by rfl) ⟨48766940, by rfl⟩ : syracuseStep 65022587 = 97533881) B97533881
theorem B1977007 : Blo 1756579 1977007 := bstep (se 1 (by rfl) ⟨1482755, by rfl⟩ : syracuseStep 1977007 = 2965511) B2965511
theorem B12020471 : Blo 1756579 12020471 := bstep (se 1 (by rfl) ⟨9015353, by rfl⟩ : syracuseStep 12020471 = 18030707) B18030707
theorem B1977295 : Blo 1756579 1977295 := bstep (se 1 (by rfl) ⟨1482971, by rfl⟩ : syracuseStep 1977295 = 2965943) B2965943
theorem B4279259 : Blo 1756579 4279259 := bstep (se 1 (by rfl) ⟨3209444, by rfl⟩ : syracuseStep 4279259 = 6418889) B6418889
theorem B9497587 : Blo 1756579 9497587 := bstep (se 1 (by rfl) ⟨7123190, by rfl⟩ : syracuseStep 9497587 = 14246381) B14246381
theorem B30018761 : Blo 1756579 30018761 := bstep (se 2 (by rfl) ⟨11257035, by rfl⟩ : syracuseStep 30018761 = 22514071) B22514071
theorem B1977691 : Blo 1756579 1977691 := bstep (se 1 (by rfl) ⟨1483268, by rfl⟩ : syracuseStep 1977691 = 2966537) B2966537
theorem B10005889 : Blo 1756579 10005889 := bstep (se 2 (by rfl) ⟨3752208, by rfl⟩ : syracuseStep 10005889 = 7504417) B7504417
theorem B1756583 : Blo 1756579 1756583 := bstep (se 1 (by rfl) ⟨1317437, by rfl⟩ : syracuseStep 1756583 = 2634875) B2634875
theorem B1977799 : Blo 1756579 1977799 := bstep (se 1 (by rfl) ⟨1483349, by rfl⟩ : syracuseStep 1977799 = 2966699) B2966699
theorem B1756667 : Blo 1756579 1756667 := bstep (se 1 (by rfl) ⟨1317500, by rfl⟩ : syracuseStep 1756667 = 2635001) B2635001
theorem B1756735 : Blo 1756579 1756735 := bstep (se 1 (by rfl) ⟨1317551, by rfl⟩ : syracuseStep 1756735 = 2635103) B2635103
theorem B1805887 : Blo 1756579 1805887 := bstep (se 1 (by rfl) ⟨1354415, by rfl⟩ : syracuseStep 1805887 = 2708831) B2708831
theorem B1756743 : Blo 1756579 1756743 := bstep (se 1 (by rfl) ⟨1317557, by rfl⟩ : syracuseStep 1756743 = 2635115) B2635115
theorem B1756895 : Blo 1756579 1756895 := bstep (se 1 (by rfl) ⟨1317671, by rfl⟩ : syracuseStep 1756895 = 2635343) B2635343
theorem B6336235 : Blo 1756579 6336235 := bstep (se 1 (by rfl) ⟨4752176, by rfl⟩ : syracuseStep 6336235 = 9504353) B9504353
theorem B1756975 : Blo 1756579 1756975 := bstep (se 1 (by rfl) ⟨1317731, by rfl⟩ : syracuseStep 1756975 = 2635463) B2635463
theorem B3952439 : Blo 1756579 3952439 := bstep (se 1 (by rfl) ⟨2964329, by rfl⟩ : syracuseStep 3952439 = 5928659) B5928659
theorem B1757083 : Blo 1756579 1757083 := bstep (se 1 (by rfl) ⟨1317812, by rfl⟩ : syracuseStep 1757083 = 2635625) B2635625
theorem B2224027 : Blo 1756579 2224027 := bstep (se 1 (by rfl) ⟨1668020, by rfl⟩ : syracuseStep 2224027 = 3336041) B3336041
theorem B1757135 : Blo 1756579 1757135 := bstep (se 1 (by rfl) ⟨1317851, by rfl⟩ : syracuseStep 1757135 = 2635703) B2635703
theorem B1757159 : Blo 1756579 1757159 := bstep (se 1 (by rfl) ⟨1317869, by rfl⟩ : syracuseStep 1757159 = 2635739) B2635739
theorem B3952745 : Blo 1756579 3952745 := bstep (se 2 (by rfl) ⟨1482279, by rfl⟩ : syracuseStep 3952745 = 2964559) B2964559
theorem B10145897 : Blo 1756579 10145897 := bstep (se 2 (by rfl) ⟨3804711, by rfl⟩ : syracuseStep 10145897 = 7609423) B7609423
theorem B7508177 : Blo 1756579 7508177 := bstep (se 2 (by rfl) ⟨2815566, by rfl⟩ : syracuseStep 7508177 = 5631133) B5631133
theorem B1757471 : Blo 1756579 1757471 := bstep (se 1 (by rfl) ⟨1318103, by rfl⟩ : syracuseStep 1757471 = 2636207) B2636207
theorem B1757531 : Blo 1756579 1757531 := bstep (se 1 (by rfl) ⟨1318148, by rfl⟩ : syracuseStep 1757531 = 2636297) B2636297
theorem B6951275 : Blo 1756579 6951275 := bstep (se 1 (by rfl) ⟨5213456, by rfl⟩ : syracuseStep 6951275 = 10426913) B10426913
theorem B1757551 : Blo 1756579 1757551 := bstep (se 1 (by rfl) ⟨1318163, by rfl⟩ : syracuseStep 1757551 = 2636327) B2636327
theorem B1757607 : Blo 1756579 1757607 := bstep (se 1 (by rfl) ⟨1318205, by rfl⟩ : syracuseStep 1757607 = 2636411) B2636411
theorem B5345761 : Blo 1756579 5345761 := bstep (se 2 (by rfl) ⟨2004660, by rfl⟩ : syracuseStep 5345761 = 4009321) B4009321
theorem B1757691 : Blo 1756579 1757691 := bstep (se 1 (by rfl) ⟨1318268, by rfl⟩ : syracuseStep 1757691 = 2636537) B2636537
theorem B1757759 : Blo 1756579 1757759 := bstep (se 1 (by rfl) ⟨1318319, by rfl⟩ : syracuseStep 1757759 = 2636639) B2636639
theorem B1757767 : Blo 1756579 1757767 := bstep (se 1 (by rfl) ⟨1318325, by rfl⟩ : syracuseStep 1757767 = 2636651) B2636651
theorem B3953231 : Blo 1756579 3953231 := bstep (se 1 (by rfl) ⟨2964923, by rfl⟩ : syracuseStep 3953231 = 5929847) B5929847
theorem B9630353 : Blo 1756579 9630353 := bstep (se 2 (by rfl) ⟨3611382, by rfl⟩ : syracuseStep 9630353 = 7222765) B7222765
theorem B8893151 : Blo 1756579 8893151 := bstep (se 1 (by rfl) ⟨6669863, by rfl⟩ : syracuseStep 8893151 = 13339727) B13339727
theorem B3953375 : Blo 1756579 3953375 := bstep (se 1 (by rfl) ⟨2965031, by rfl⟩ : syracuseStep 3953375 = 5930063) B5930063
theorem B1757919 : Blo 1756579 1757919 := bstep (se 1 (by rfl) ⟨1318439, by rfl⟩ : syracuseStep 1757919 = 2636879) B2636879
theorem B4223735 : Blo 1756579 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B1757999 : Blo 1756579 1757999 := bstep (se 1 (by rfl) ⟨1318499, by rfl⟩ : syracuseStep 1757999 = 2636999) B2636999
theorem B11260781 : Blo 1756579 11260781 := bstep (se 3 (by rfl) ⟨2111396, by rfl⟩ : syracuseStep 11260781 = 4222793) B4222793
theorem B3953627 : Blo 1756579 3953627 := bstep (se 1 (by rfl) ⟨2965220, by rfl⟩ : syracuseStep 3953627 = 5930441) B5930441
theorem B3953807 : Blo 1756579 3953807 := bstep (se 1 (by rfl) ⟨2965355, by rfl⟩ : syracuseStep 3953807 = 5930711) B5930711
theorem B2634971 : Blo 1756579 2634971 := bstep (se 1 (by rfl) ⟨1976228, by rfl⟩ : syracuseStep 2634971 = 3952457) B3952457
theorem B3953897 : Blo 1756579 3953897 := bstep (se 2 (by rfl) ⟨1482711, by rfl⟩ : syracuseStep 3953897 = 2965423) B2965423
theorem B5002489 : Blo 1756579 5002489 := bstep (se 2 (by rfl) ⟨1875933, by rfl⟩ : syracuseStep 5002489 = 3751867) B3751867
theorem B3953951 : Blo 1756579 3953951 := bstep (se 1 (by rfl) ⟨2965463, by rfl⟩ : syracuseStep 3953951 = 5930927) B5930927
theorem B5002535 : Blo 1756579 5002535 := bstep (se 1 (by rfl) ⟨3751901, by rfl⟩ : syracuseStep 5002535 = 7503803) B7503803
theorem B8443223 : Blo 1756579 8443223 := bstep (se 1 (by rfl) ⟨6332417, by rfl⟩ : syracuseStep 8443223 = 12664835) B12664835
theorem B2635145 : Blo 1756579 2635145 := bstep (se 2 (by rfl) ⟨988179, by rfl⟩ : syracuseStep 2635145 = 1976359) B1976359
theorem B5928605 : Blo 1756579 5928605 := bstep (se 3 (by rfl) ⟨1111613, by rfl⟩ : syracuseStep 5928605 = 2223227) B2223227
theorem B2635499 : Blo 1756579 2635499 := bstep (se 1 (by rfl) ⟨1976624, by rfl⟩ : syracuseStep 2635499 = 3953249) B3953249
theorem B3954473 : Blo 1756579 3954473 := bstep (se 2 (by rfl) ⟨1482927, by rfl⟩ : syracuseStep 3954473 = 2965855) B2965855
theorem B38008763 : Blo 1756579 38008763 := bstep (se 1 (by rfl) ⟨28506572, by rfl⟩ : syracuseStep 38008763 = 57013145) B57013145
theorem B2635727 : Blo 1756579 2635727 := bstep (se 1 (by rfl) ⟨1976795, by rfl⟩ : syracuseStep 2635727 = 3953591) B3953591
theorem B2815951 : Blo 1756579 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B9500807 : Blo 1756579 9500807 := bstep (se 1 (by rfl) ⟨7125605, by rfl⟩ : syracuseStep 9500807 = 14251211) B14251211
theorem B5929145 : Blo 1756579 5929145 := bstep (se 2 (by rfl) ⟨2223429, by rfl⟩ : syracuseStep 5929145 = 4446859) B4446859
theorem B2636123 : Blo 1756579 2636123 := bstep (se 1 (by rfl) ⟨1977092, by rfl⟩ : syracuseStep 2636123 = 3954185) B3954185
theorem B4446647 : Blo 1756579 4446647 := bstep (se 1 (by rfl) ⟨3334985, by rfl⟩ : syracuseStep 4446647 = 6669971) B6669971
theorem B12024247 : Blo 1756579 12024247 := bstep (se 1 (by rfl) ⟨9018185, by rfl⟩ : syracuseStep 12024247 = 18036371) B18036371
theorem B18995735 : Blo 1756579 18995735 := bstep (se 1 (by rfl) ⟨14246801, by rfl⟩ : syracuseStep 18995735 = 28493603) B28493603
theorem B2636351 : Blo 1756579 2636351 := bstep (se 1 (by rfl) ⟨1977263, by rfl⟩ : syracuseStep 2636351 = 3954527) B3954527
theorem B6675119 : Blo 1756579 6675119 := bstep (se 1 (by rfl) ⟨5006339, by rfl⟩ : syracuseStep 6675119 = 10012679) B10012679
theorem B2636471 : Blo 1756579 2636471 := bstep (se 1 (by rfl) ⟨1977353, by rfl⟩ : syracuseStep 2636471 = 3954707) B3954707
theorem B3955535 : Blo 1756579 3955535 := bstep (se 1 (by rfl) ⟨2966651, by rfl⟩ : syracuseStep 3955535 = 5933303) B5933303
theorem B5004175 : Blo 1756579 5004175 := bstep (se 1 (by rfl) ⟨3753131, by rfl⟩ : syracuseStep 5004175 = 7506263) B7506263
theorem B2636699 : Blo 1756579 2636699 := bstep (se 1 (by rfl) ⟨1977524, by rfl⟩ : syracuseStep 2636699 = 3955049) B3955049
theorem B8895419 : Blo 1756579 8895419 := bstep (se 1 (by rfl) ⟨6671564, by rfl⟩ : syracuseStep 8895419 = 13343129) B13343129
theorem B6094013 : Blo 1756579 6094013 := bstep (se 3 (by rfl) ⟨1142627, by rfl⟩ : syracuseStep 6094013 = 2285255) B2285255
theorem B16252093 : Blo 1756579 16252093 := bstep (se 3 (by rfl) ⟨3047267, by rfl⟩ : syracuseStep 16252093 = 6094535) B6094535
theorem B2374921 : Blo 1756579 2374921 := bstep (se 2 (by rfl) ⟨890595, by rfl⟩ : syracuseStep 2374921 = 1781191) B1781191
theorem B5004575 : Blo 1756579 5004575 := bstep (se 1 (by rfl) ⟨3753431, by rfl⟩ : syracuseStep 5004575 = 7506863) B7506863
theorem B2964775 : Blo 1756579 2964775 := bstep (se 1 (by rfl) ⟨2223581, by rfl⟩ : syracuseStep 2964775 = 4447163) B4447163
theorem B2637095 : Blo 1756579 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B4447649 : Blo 1756579 4447649 := bstep (se 2 (by rfl) ⟨1667868, by rfl⟩ : syracuseStep 4447649 = 3335737) B3335737
theorem B5930657 : Blo 1756579 5930657 := bstep (se 2 (by rfl) ⟨2223996, by rfl⟩ : syracuseStep 5930657 = 4447993) B4447993
theorem B6332201 : Blo 1756579 6332201 := bstep (se 2 (by rfl) ⟨2374575, by rfl⟩ : syracuseStep 6332201 = 4749151) B4749151
theorem B7126825 : Blo 1756579 7126825 := bstep (se 2 (by rfl) ⟨2672559, by rfl⟩ : syracuseStep 7126825 = 5345119) B5345119
theorem B2965295 : Blo 1756579 2965295 := bstep (se 1 (by rfl) ⟨2223971, by rfl⟩ : syracuseStep 2965295 = 4447943) B4447943
theorem B21372731 : Blo 1756579 21372731 := bstep (se 1 (by rfl) ⟨16029548, by rfl⟩ : syracuseStep 21372731 = 32059097) B32059097
theorem B4448105 : Blo 1756579 4448105 := bstep (se 2 (by rfl) ⟨1668039, by rfl⟩ : syracuseStep 4448105 = 3336079) B3336079
theorem B15425387 : Blo 1756579 15425387 := bstep (se 1 (by rfl) ⟨11569040, by rfl⟩ : syracuseStep 15425387 = 23138081) B23138081
theorem B49397621 : Blo 1756579 49397621 := bstep (se 5 (by rfl) ⟨2315513, by rfl⟩ : syracuseStep 49397621 = 4631027) B4631027
theorem B20021255 : Blo 1756579 20021255 := bstep (se 1 (by rfl) ⟨15015941, by rfl⟩ : syracuseStep 20021255 = 30031883) B30031883
theorem B5931143 : Blo 1756579 5931143 := bstep (se 1 (by rfl) ⟨4448357, by rfl⟩ : syracuseStep 5931143 = 8896715) B8896715
theorem B5005451 : Blo 1756579 5005451 := bstep (se 1 (by rfl) ⟨3754088, by rfl⟩ : syracuseStep 5005451 = 7508177) B7508177
theorem B3563873 : Blo 1756579 3563873 := bstep (se 2 (by rfl) ⟨1336452, by rfl⟩ : syracuseStep 3563873 = 2672905) B2672905
theorem B16032329 : Blo 1756579 16032329 := bstep (se 2 (by rfl) ⟨6012123, by rfl⟩ : syracuseStep 16032329 = 12024247) B12024247
theorem B7127681 : Blo 1756579 7127681 := bstep (se 2 (by rfl) ⟨2672880, by rfl⟩ : syracuseStep 7127681 = 5345761) B5345761
theorem B3335023 : Blo 1756579 3335023 := bstep (se 1 (by rfl) ⟨2501267, by rfl⟩ : syracuseStep 3335023 = 5002535) B5002535
theorem B5628815 : Blo 1756579 5628815 := bstep (se 1 (by rfl) ⟨4221611, by rfl⟩ : syracuseStep 5628815 = 8443223) B8443223
theorem B56984593 : Blo 1756579 56984593 := bstep (se 2 (by rfl) ⟨21369222, by rfl⟩ : syracuseStep 56984593 = 42738445) B42738445
theorem B2966591 : Blo 1756579 2966591 := bstep (se 1 (by rfl) ⟨2224943, by rfl⟩ : syracuseStep 2966591 = 4449887) B4449887
theorem B10142941 : Blo 1756579 10142941 := bstep (se 3 (by rfl) ⟨1901801, by rfl⟩ : syracuseStep 10142941 = 3803603) B3803603
theorem B25339175 : Blo 1756579 25339175 := bstep (se 1 (by rfl) ⟨19004381, by rfl⟩ : syracuseStep 25339175 = 38008763) B38008763
theorem B6333871 : Blo 1756579 6333871 := bstep (se 1 (by rfl) ⟨4750403, by rfl⟩ : syracuseStep 6333871 = 9500807) B9500807
theorem B6096343 : Blo 1756579 6096343 := bstep (se 1 (by rfl) ⟨4572257, by rfl⟩ : syracuseStep 6096343 = 9144515) B9144515
theorem B21669457 : Blo 1756579 21669457 := bstep (se 2 (by rfl) ⟨8126046, by rfl⟩ : syracuseStep 21669457 = 16252093) B16252093
theorem B5932655 : Blo 1756579 5932655 := bstep (se 1 (by rfl) ⟨4449491, by rfl⟩ : syracuseStep 5932655 = 8898983) B8898983
theorem B22824563 : Blo 1756579 22824563 := bstep (se 1 (by rfl) ⟨17118422, by rfl⟩ : syracuseStep 22824563 = 34236845) B34236845
theorem B6669985 : Blo 1756579 6669985 := bstep (se 2 (by rfl) ⟨2501244, by rfl⟩ : syracuseStep 6669985 = 5002489) B5002489
theorem B5932763 : Blo 1756579 5932763 := bstep (se 1 (by rfl) ⟨4449572, by rfl⟩ : syracuseStep 5932763 = 8899145) B8899145
theorem B4450079 : Blo 1756579 4450079 := bstep (se 1 (by rfl) ⟨3337559, by rfl⟩ : syracuseStep 4450079 = 6675119) B6675119
theorem B8013647 : Blo 1756579 8013647 := bstep (se 1 (by rfl) ⟨6010235, by rfl⟩ : syracuseStep 8013647 = 12020471) B12020471
theorem B2852839 : Blo 1756579 2852839 := bstep (se 1 (by rfl) ⟨2139629, by rfl⟩ : syracuseStep 2852839 = 4279259) B4279259
theorem B3336383 : Blo 1756579 3336383 := bstep (se 1 (by rfl) ⟨2502287, by rfl⟩ : syracuseStep 3336383 = 5004575) B5004575
theorem B8448313 : Blo 1756579 8448313 := bstep (se 2 (by rfl) ⟨3168117, by rfl⟩ : syracuseStep 8448313 = 6336235) B6336235
theorem B4221467 : Blo 1756579 4221467 := bstep (se 1 (by rfl) ⟨3166100, by rfl⟩ : syracuseStep 4221467 = 6332201) B6332201
theorem B1976863 : Blo 1756579 1976863 := bstep (se 1 (by rfl) ⟨1482647, by rfl⟩ : syracuseStep 1976863 = 2965295) B2965295
theorem B14248487 : Blo 1756579 14248487 := bstep (se 1 (by rfl) ⟨10686365, by rfl⟩ : syracuseStep 14248487 = 21372731) B21372731
theorem B10283591 : Blo 1756579 10283591 := bstep (se 1 (by rfl) ⟨7712693, by rfl⟩ : syracuseStep 10283591 = 15425387) B15425387
theorem B13339241 : Blo 1756579 13339241 := bstep (se 2 (by rfl) ⟨5002215, by rfl⟩ : syracuseStep 13339241 = 10004431) B10004431
theorem B3754601 : Blo 1756579 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B98839369 : Blo 1756579 98839369 := bstep (se 2 (by rfl) ⟨37064763, by rfl⟩ : syracuseStep 98839369 = 74129527) B74129527
theorem B3337195 : Blo 1756579 3337195 := bstep (se 1 (by rfl) ⟨2502896, by rfl⟩ : syracuseStep 3337195 = 5005793) B5005793
theorem B7507187 : Blo 1756579 7507187 := bstep (se 1 (by rfl) ⟨5630390, by rfl⟩ : syracuseStep 7507187 = 11260781) B11260781
theorem B5631275 : Blo 1756579 5631275 := bstep (se 1 (by rfl) ⟨4223456, by rfl⟩ : syracuseStep 5631275 = 8446913) B8446913
theorem B1756647 : Blo 1756579 1756647 := bstep (se 1 (by rfl) ⟨1317485, by rfl⟩ : syracuseStep 1756647 = 2634971) B2634971
theorem B1756763 : Blo 1756579 1756763 := bstep (se 1 (by rfl) ⟨1317572, by rfl⟩ : syracuseStep 1756763 = 2635145) B2635145
theorem B3952403 : Blo 1756579 3952403 := bstep (se 1 (by rfl) ⟨2964302, by rfl⟩ : syracuseStep 3952403 = 5928605) B5928605
theorem B1756999 : Blo 1756579 1756999 := bstep (se 1 (by rfl) ⟨1317749, by rfl⟩ : syracuseStep 1756999 = 2635499) B2635499
theorem B6672233 : Blo 1756579 6672233 := bstep (se 2 (by rfl) ⟨2502087, by rfl⟩ : syracuseStep 6672233 = 5004175) B5004175
theorem B1757151 : Blo 1756579 1757151 := bstep (se 1 (by rfl) ⟨1317863, by rfl⟩ : syracuseStep 1757151 = 2635727) B2635727
theorem B2502623 : Blo 1756579 2502623 := bstep (se 1 (by rfl) ⟨1876967, by rfl⟩ : syracuseStep 2502623 = 3753935) B3753935
theorem B3952763 : Blo 1756579 3952763 := bstep (se 1 (by rfl) ⟨2964572, by rfl⟩ : syracuseStep 3952763 = 5929145) B5929145
theorem B12185795 : Blo 1756579 12185795 := bstep (se 1 (by rfl) ⟨9139346, by rfl⟩ : syracuseStep 12185795 = 18278693) B18278693
theorem B1757415 : Blo 1756579 1757415 := bstep (se 1 (by rfl) ⟨1318061, by rfl⟩ : syracuseStep 1757415 = 2636123) B2636123
theorem B3166561 : Blo 1756579 3166561 := bstep (se 2 (by rfl) ⟨1187460, by rfl⟩ : syracuseStep 3166561 = 2374921) B2374921
theorem B1757567 : Blo 1756579 1757567 := bstep (se 1 (by rfl) ⟨1318175, by rfl⟩ : syracuseStep 1757567 = 2636351) B2636351
theorem B3953033 : Blo 1756579 3953033 := bstep (se 2 (by rfl) ⟨1482387, by rfl⟩ : syracuseStep 3953033 = 2964775) B2964775
theorem B43348391 : Blo 1756579 43348391 := bstep (se 1 (by rfl) ⟨32511293, by rfl⟩ : syracuseStep 43348391 = 65022587) B65022587
theorem B1757647 : Blo 1756579 1757647 := bstep (se 1 (by rfl) ⟨1318235, by rfl⟩ : syracuseStep 1757647 = 2636471) B2636471
theorem B13341185 : Blo 1756579 13341185 := bstep (se 2 (by rfl) ⟨5002944, by rfl⟩ : syracuseStep 13341185 = 10005889) B10005889
theorem B1757799 : Blo 1756579 1757799 := bstep (se 1 (by rfl) ⟨1318349, by rfl⟩ : syracuseStep 1757799 = 2636699) B2636699
theorem B1758063 : Blo 1756579 1758063 := bstep (se 1 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 1758063 = 2637095) B2637095
theorem B3953771 : Blo 1756579 3953771 := bstep (se 1 (by rfl) ⟨2965328, by rfl⟩ : syracuseStep 3953771 = 5930657) B5930657
theorem B2634959 : Blo 1756579 2634959 := bstep (se 1 (by rfl) ⟨1976219, by rfl⟩ : syracuseStep 2634959 = 3952439) B3952439
theorem B2635163 : Blo 1756579 2635163 := bstep (se 1 (by rfl) ⟨1976372, by rfl⟩ : syracuseStep 2635163 = 3952745) B3952745
theorem B6763931 : Blo 1756579 6763931 := bstep (se 1 (by rfl) ⟨5072948, by rfl⟩ : syracuseStep 6763931 = 10145897) B10145897
theorem B8893961 : Blo 1756579 8893961 := bstep (se 2 (by rfl) ⟨3335235, by rfl⟩ : syracuseStep 8893961 = 6670471) B6670471
theorem B4634183 : Blo 1756579 4634183 := bstep (se 1 (by rfl) ⟨3475637, by rfl⟩ : syracuseStep 4634183 = 6951275) B6951275
theorem B2635385 : Blo 1756579 2635385 := bstep (se 2 (by rfl) ⟨988269, by rfl⟩ : syracuseStep 2635385 = 1976539) B1976539
theorem B3954347 : Blo 1756579 3954347 := bstep (se 1 (by rfl) ⟨2965760, by rfl⟩ : syracuseStep 3954347 = 5931521) B5931521
theorem B2635487 : Blo 1756579 2635487 := bstep (se 1 (by rfl) ⟨1976615, by rfl⟩ : syracuseStep 2635487 = 3953231) B3953231
theorem B6420235 : Blo 1756579 6420235 := bstep (se 1 (by rfl) ⟨4815176, by rfl⟩ : syracuseStep 6420235 = 9630353) B9630353
theorem B11261753 : Blo 1756579 11261753 := bstep (se 2 (by rfl) ⟨4223157, by rfl⟩ : syracuseStep 11261753 = 8446315) B8446315
theorem B5928767 : Blo 1756579 5928767 := bstep (se 1 (by rfl) ⟨4446575, by rfl⟩ : syracuseStep 5928767 = 8893151) B8893151
theorem B2635583 : Blo 1756579 2635583 := bstep (se 1 (by rfl) ⟨1976687, by rfl⟩ : syracuseStep 2635583 = 3953375) B3953375
theorem B16250701 : Blo 1756579 16250701 := bstep (se 3 (by rfl) ⟨3047006, by rfl⟩ : syracuseStep 16250701 = 6094013) B6094013
theorem B2815823 : Blo 1756579 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B2635751 : Blo 1756579 2635751 := bstep (se 1 (by rfl) ⟨1976813, by rfl⟩ : syracuseStep 2635751 = 3953627) B3953627
theorem B3954671 : Blo 1756579 3954671 := bstep (se 1 (by rfl) ⟨2966003, by rfl⟩ : syracuseStep 3954671 = 5932007) B5932007
theorem B2635769 : Blo 1756579 2635769 := bstep (se 2 (by rfl) ⟨988413, by rfl⟩ : syracuseStep 2635769 = 1976827) B1976827
theorem B2635871 : Blo 1756579 2635871 := bstep (se 1 (by rfl) ⟨1976903, by rfl⟩ : syracuseStep 2635871 = 3953807) B3953807
theorem B2635931 : Blo 1756579 2635931 := bstep (se 1 (by rfl) ⟨1976948, by rfl⟩ : syracuseStep 2635931 = 3953897) B3953897
theorem B2635967 : Blo 1756579 2635967 := bstep (se 1 (by rfl) ⟨1976975, by rfl⟩ : syracuseStep 2635967 = 3953951) B3953951
theorem B3954887 : Blo 1756579 3954887 := bstep (se 1 (by rfl) ⟨2966165, by rfl⟩ : syracuseStep 3954887 = 5932331) B5932331
theorem B2636009 : Blo 1756579 2636009 := bstep (se 2 (by rfl) ⟨988503, by rfl⟩ : syracuseStep 2636009 = 1977007) B1977007
theorem B3955067 : Blo 1756579 3955067 := bstep (se 1 (by rfl) ⟨2966300, by rfl⟩ : syracuseStep 3955067 = 5932601) B5932601
theorem B2636315 : Blo 1756579 2636315 := bstep (se 1 (by rfl) ⟨1977236, by rfl⟩ : syracuseStep 2636315 = 3954473) B3954473
theorem B2636393 : Blo 1756579 2636393 := bstep (se 2 (by rfl) ⟨988647, by rfl⟩ : syracuseStep 2636393 = 1977295) B1977295
theorem B3955337 : Blo 1756579 3955337 := bstep (se 2 (by rfl) ⟨1483251, by rfl⟩ : syracuseStep 3955337 = 2966503) B2966503
theorem B12663449 : Blo 1756579 12663449 := bstep (se 2 (by rfl) ⟨4748793, by rfl⟩ : syracuseStep 12663449 = 9497587) B9497587
theorem B2964431 : Blo 1756579 2964431 := bstep (se 1 (by rfl) ⟨2223323, by rfl⟩ : syracuseStep 2964431 = 4446647) B4446647
theorem B4447183 : Blo 1756579 4447183 := bstep (se 1 (by rfl) ⟨3335387, by rfl⟩ : syracuseStep 4447183 = 6670775) B6670775
theorem B12663823 : Blo 1756579 12663823 := bstep (se 1 (by rfl) ⟨9497867, by rfl⟩ : syracuseStep 12663823 = 18995735) B18995735
theorem B2636921 : Blo 1756579 2636921 := bstep (se 2 (by rfl) ⟨988845, by rfl⟩ : syracuseStep 2636921 = 1977691) B1977691
theorem B2637023 : Blo 1756579 2637023 := bstep (se 1 (by rfl) ⟨1977767, by rfl⟩ : syracuseStep 2637023 = 3955535) B3955535
theorem B2637065 : Blo 1756579 2637065 := bstep (se 2 (by rfl) ⟨988899, by rfl⟩ : syracuseStep 2637065 = 1977799) B1977799
theorem B5930279 : Blo 1756579 5930279 := bstep (se 1 (by rfl) ⟨4447709, by rfl⟩ : syracuseStep 5930279 = 8895419) B8895419
theorem B2407849 : Blo 1756579 2407849 := bstep (se 2 (by rfl) ⟨902943, by rfl⟩ : syracuseStep 2407849 = 1805887) B1805887
theorem B20012507 : Blo 1756579 20012507 := bstep (se 1 (by rfl) ⟨15009380, by rfl⟩ : syracuseStep 20012507 = 30018761) B30018761
theorem B2965099 : Blo 1756579 2965099 := bstep (se 1 (by rfl) ⟨2223824, by rfl⟩ : syracuseStep 2965099 = 4447649) B4447649
theorem B131726989 : Blo 1756579 131726989 := bstep (se 3 (by rfl) ⟨24698810, by rfl⟩ : syracuseStep 131726989 = 49397621) B49397621
theorem B9502433 : Blo 1756579 9502433 := bstep (se 2 (by rfl) ⟨3563412, by rfl⟩ : syracuseStep 9502433 = 7126825) B7126825
theorem B2965369 : Blo 1756579 2965369 := bstep (se 2 (by rfl) ⟨1112013, by rfl⟩ : syracuseStep 2965369 = 2224027) B2224027
theorem B2965403 : Blo 1756579 2965403 := bstep (se 1 (by rfl) ⟨2224052, by rfl⟩ : syracuseStep 2965403 = 4448105) B4448105
theorem B2375915 : Blo 1756579 2375915 := bstep (se 1 (by rfl) ⟨1781936, by rfl⟩ : syracuseStep 2375915 = 3563873) B3563873
theorem B11264417 : Blo 1756579 11264417 := bstep (se 2 (by rfl) ⟨4224156, by rfl⟩ : syracuseStep 11264417 = 8448313) B8448313
theorem B3752543 : Blo 1756579 3752543 := bstep (se 1 (by rfl) ⟨2814407, by rfl⟩ : syracuseStep 3752543 = 5628815) B5628815
theorem B16892783 : Blo 1756579 16892783 := bstep (se 1 (by rfl) ⟨12669587, by rfl⟩ : syracuseStep 16892783 = 25339175) B25339175
theorem B131785825 : Blo 1756579 131785825 := bstep (se 2 (by rfl) ⟨49419684, by rfl⟩ : syracuseStep 131785825 = 98839369) B98839369
theorem B2966719 : Blo 1756579 2966719 := bstep (se 1 (by rfl) ⟨2225039, by rfl⟩ : syracuseStep 2966719 = 4450079) B4450079
theorem B5342431 : Blo 1756579 5342431 := bstep (se 1 (by rfl) ⟨4006823, by rfl⟩ : syracuseStep 5342431 = 8013647) B8013647
theorem B4449593 : Blo 1756579 4449593 := bstep (se 2 (by rfl) ⟨1668597, by rfl⟩ : syracuseStep 4449593 = 3337195) B3337195
theorem B16885097 : Blo 1756579 16885097 := bstep (se 2 (by rfl) ⟨6331911, by rfl⟩ : syracuseStep 16885097 = 12663823) B12663823
theorem B19007149 : Blo 1756579 19007149 := bstep (se 3 (by rfl) ⟨3563840, by rfl⟩ : syracuseStep 19007149 = 7127681) B7127681
theorem B8128457 : Blo 1756579 8128457 := bstep (se 2 (by rfl) ⟨3048171, by rfl⟩ : syracuseStep 8128457 = 6096343) B6096343
theorem B1976287 : Blo 1756579 1976287 := bstep (se 1 (by rfl) ⟨1482215, by rfl⟩ : syracuseStep 1976287 = 2964431) B2964431
theorem B3754183 : Blo 1756579 3754183 := bstep (se 1 (by rfl) ⟨2815637, by rfl⟩ : syracuseStep 3754183 = 5631275) B5631275
theorem B6334955 : Blo 1756579 6334955 := bstep (se 1 (by rfl) ⟨4751216, by rfl⟩ : syracuseStep 6334955 = 9502433) B9502433
theorem B15215141 : Blo 1756579 15215141 := bstep (se 4 (by rfl) ⟨1426419, by rfl⟩ : syracuseStep 15215141 = 2852839) B2852839
theorem B1976935 : Blo 1756579 1976935 := bstep (se 1 (by rfl) ⟨1482701, by rfl⟩ : syracuseStep 1976935 = 2965403) B2965403
theorem B13347503 : Blo 1756579 13347503 := bstep (se 1 (by rfl) ⟨10010627, by rfl⟩ : syracuseStep 13347503 = 20021255) B20021255
theorem B3336967 : Blo 1756579 3336967 := bstep (se 1 (by rfl) ⟨2502725, by rfl⟩ : syracuseStep 3336967 = 5005451) B5005451
theorem B4222081 : Blo 1756579 4222081 := bstep (se 2 (by rfl) ⟨1583280, by rfl⟩ : syracuseStep 4222081 = 3166561) B3166561
theorem B1977727 : Blo 1756579 1977727 := bstep (se 1 (by rfl) ⟨1483295, by rfl⟩ : syracuseStep 1977727 = 2966591) B2966591
theorem B1756639 : Blo 1756579 1756639 := bstep (se 1 (by rfl) ⟨1317479, by rfl⟩ : syracuseStep 1756639 = 2634959) B2634959
theorem B51367445 : Blo 1756579 51367445 := bstep (se 6 (by rfl) ⟨1203924, by rfl⟩ : syracuseStep 51367445 = 2407849) B2407849
theorem B1756775 : Blo 1756579 1756775 := bstep (se 1 (by rfl) ⟨1317581, by rfl⟩ : syracuseStep 1756775 = 2635163) B2635163
theorem B4509287 : Blo 1756579 4509287 := bstep (se 1 (by rfl) ⟨3381965, by rfl⟩ : syracuseStep 4509287 = 6763931) B6763931
theorem B1756923 : Blo 1756579 1756923 := bstep (se 1 (by rfl) ⟨1317692, by rfl⟩ : syracuseStep 1756923 = 2635385) B2635385
theorem B1756991 : Blo 1756579 1756991 := bstep (se 1 (by rfl) ⟨1317743, by rfl⟩ : syracuseStep 1756991 = 2635487) B2635487
theorem B7507835 : Blo 1756579 7507835 := bstep (se 1 (by rfl) ⟨5630876, by rfl⟩ : syracuseStep 7507835 = 11261753) B11261753
theorem B3952511 : Blo 1756579 3952511 := bstep (se 1 (by rfl) ⟨2964383, by rfl⟩ : syracuseStep 3952511 = 5928767) B5928767
theorem B1757055 : Blo 1756579 1757055 := bstep (se 1 (by rfl) ⟨1317791, by rfl⟩ : syracuseStep 1757055 = 2635583) B2635583
theorem B1757167 : Blo 1756579 1757167 := bstep (se 1 (by rfl) ⟨1317875, by rfl⟩ : syracuseStep 1757167 = 2635751) B2635751
theorem B1757179 : Blo 1756579 1757179 := bstep (se 1 (by rfl) ⟨1317884, by rfl⟩ : syracuseStep 1757179 = 2635769) B2635769
theorem B1757247 : Blo 1756579 1757247 := bstep (se 1 (by rfl) ⟨1317935, by rfl⟩ : syracuseStep 1757247 = 2635871) B2635871
theorem B1757287 : Blo 1756579 1757287 := bstep (se 1 (by rfl) ⟨1317965, by rfl⟩ : syracuseStep 1757287 = 2635931) B2635931
theorem B1757311 : Blo 1756579 1757311 := bstep (se 1 (by rfl) ⟨1317983, by rfl⟩ : syracuseStep 1757311 = 2635967) B2635967
theorem B2224255 : Blo 1756579 2224255 := bstep (se 1 (by rfl) ⟨1668191, by rfl⟩ : syracuseStep 2224255 = 3336383) B3336383
theorem B1757339 : Blo 1756579 1757339 := bstep (se 1 (by rfl) ⟨1318004, by rfl⟩ : syracuseStep 1757339 = 2636009) B2636009
theorem B12357821 : Blo 1756579 12357821 := bstep (se 3 (by rfl) ⟨2317091, by rfl⟩ : syracuseStep 12357821 = 4634183) B4634183
theorem B2814311 : Blo 1756579 2814311 := bstep (se 1 (by rfl) ⟨2110733, by rfl⟩ : syracuseStep 2814311 = 4221467) B4221467
theorem B1757543 : Blo 1756579 1757543 := bstep (se 1 (by rfl) ⟨1318157, by rfl⟩ : syracuseStep 1757543 = 2636315) B2636315
theorem B9498991 : Blo 1756579 9498991 := bstep (se 1 (by rfl) ⟨7124243, by rfl⟩ : syracuseStep 9498991 = 14248487) B14248487
theorem B8892827 : Blo 1756579 8892827 := bstep (se 1 (by rfl) ⟨6669620, by rfl⟩ : syracuseStep 8892827 = 13339241) B13339241
theorem B1757595 : Blo 1756579 1757595 := bstep (se 1 (by rfl) ⟨1318196, by rfl⟩ : syracuseStep 1757595 = 2636393) B2636393
theorem B2503067 : Blo 1756579 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B8442299 : Blo 1756579 8442299 := bstep (se 1 (by rfl) ⟨6331724, by rfl⟩ : syracuseStep 8442299 = 12663449) B12663449
theorem B1757947 : Blo 1756579 1757947 := bstep (se 1 (by rfl) ⟨1318460, by rfl⟩ : syracuseStep 1757947 = 2636921) B2636921
theorem B3953465 : Blo 1756579 3953465 := bstep (se 2 (by rfl) ⟨1482549, by rfl⟩ : syracuseStep 3953465 = 2965099) B2965099
theorem B1758015 : Blo 1756579 1758015 := bstep (se 1 (by rfl) ⟨1318511, by rfl⟩ : syracuseStep 1758015 = 2637023) B2637023
theorem B1758043 : Blo 1756579 1758043 := bstep (se 1 (by rfl) ⟨1318532, by rfl⟩ : syracuseStep 1758043 = 2637065) B2637065
theorem B3953519 : Blo 1756579 3953519 := bstep (se 1 (by rfl) ⟨2965139, by rfl⟩ : syracuseStep 3953519 = 5930279) B5930279
theorem B7508861 : Blo 1756579 7508861 := bstep (se 3 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 7508861 = 2815823) B2815823
theorem B8893313 : Blo 1756579 8893313 := bstep (se 2 (by rfl) ⟨3334992, by rfl⟩ : syracuseStep 8893313 = 6669985) B6669985
theorem B13341671 : Blo 1756579 13341671 := bstep (se 1 (by rfl) ⟨10006253, by rfl⟩ : syracuseStep 13341671 = 20012507) B20012507
theorem B3953825 : Blo 1756579 3953825 := bstep (se 2 (by rfl) ⟨1482684, by rfl⟩ : syracuseStep 3953825 = 2965369) B2965369
theorem B2634935 : Blo 1756579 2634935 := bstep (se 1 (by rfl) ⟨1976201, by rfl⟩ : syracuseStep 2634935 = 3952403) B3952403
theorem B6673661 : Blo 1756579 6673661 := bstep (se 3 (by rfl) ⟨1251311, by rfl⟩ : syracuseStep 6673661 = 2502623) B2502623
theorem B2635175 : Blo 1756579 2635175 := bstep (se 1 (by rfl) ⟨1976381, by rfl⟩ : syracuseStep 2635175 = 3952763) B3952763
theorem B3954095 : Blo 1756579 3954095 := bstep (se 1 (by rfl) ⟨2965571, by rfl⟩ : syracuseStep 3954095 = 5931143) B5931143
theorem B8123863 : Blo 1756579 8123863 := bstep (se 1 (by rfl) ⟨6092897, by rfl⟩ : syracuseStep 8123863 = 12185795) B12185795
theorem B2635355 : Blo 1756579 2635355 := bstep (se 1 (by rfl) ⟨1976516, by rfl⟩ : syracuseStep 2635355 = 3953033) B3953033
theorem B28898927 : Blo 1756579 28898927 := bstep (se 1 (by rfl) ⟨21674195, by rfl⟩ : syracuseStep 28898927 = 43348391) B43348391
theorem B8894123 : Blo 1756579 8894123 := bstep (se 1 (by rfl) ⟨6670592, by rfl⟩ : syracuseStep 8894123 = 13341185) B13341185
theorem B10688219 : Blo 1756579 10688219 := bstep (se 1 (by rfl) ⟨8016164, by rfl⟩ : syracuseStep 10688219 = 16032329) B16032329
theorem B2635817 : Blo 1756579 2635817 := bstep (se 2 (by rfl) ⟨988431, by rfl⟩ : syracuseStep 2635817 = 1976863) B1976863
theorem B2635847 : Blo 1756579 2635847 := bstep (se 1 (by rfl) ⟨1976885, by rfl⟩ : syracuseStep 2635847 = 3953771) B3953771
theorem B5929307 : Blo 1756579 5929307 := bstep (se 1 (by rfl) ⟨4446980, by rfl⟩ : syracuseStep 5929307 = 8893961) B8893961
theorem B3955103 : Blo 1756579 3955103 := bstep (se 1 (by rfl) ⟨2966327, by rfl⟩ : syracuseStep 3955103 = 5932655) B5932655
theorem B2636231 : Blo 1756579 2636231 := bstep (se 1 (by rfl) ⟨1977173, by rfl⟩ : syracuseStep 2636231 = 3954347) B3954347
theorem B3955175 : Blo 1756579 3955175 := bstep (se 1 (by rfl) ⟨2966381, by rfl⟩ : syracuseStep 3955175 = 5932763) B5932763
theorem B4446697 : Blo 1756579 4446697 := bstep (se 2 (by rfl) ⟨1667511, by rfl⟩ : syracuseStep 4446697 = 3335023) B3335023
theorem B5929577 : Blo 1756579 5929577 := bstep (se 2 (by rfl) ⟨2223591, by rfl⟩ : syracuseStep 5929577 = 4447183) B4447183
theorem B2636447 : Blo 1756579 2636447 := bstep (se 1 (by rfl) ⟨1977335, by rfl⟩ : syracuseStep 2636447 = 3954671) B3954671
theorem B75979457 : Blo 1756579 75979457 := bstep (se 2 (by rfl) ⟨28492296, by rfl⟩ : syracuseStep 75979457 = 56984593) B56984593
theorem B2636591 : Blo 1756579 2636591 := bstep (se 1 (by rfl) ⟨1977443, by rfl⟩ : syracuseStep 2636591 = 3954887) B3954887
theorem B2636711 : Blo 1756579 2636711 := bstep (se 1 (by rfl) ⟨1977533, by rfl⟩ : syracuseStep 2636711 = 3955067) B3955067
theorem B13523921 : Blo 1756579 13523921 := bstep (se 2 (by rfl) ⟨5071470, by rfl⟩ : syracuseStep 13523921 = 10142941) B10142941
theorem B60865501 : Blo 1756579 60865501 := bstep (se 3 (by rfl) ⟨11412281, by rfl⟩ : syracuseStep 60865501 = 22824563) B22824563
theorem B6855727 : Blo 1756579 6855727 := bstep (se 1 (by rfl) ⟨5141795, by rfl⟩ : syracuseStep 6855727 = 10283591) B10283591
theorem B2636891 : Blo 1756579 2636891 := bstep (se 1 (by rfl) ⟨1977668, by rfl⟩ : syracuseStep 2636891 = 3955337) B3955337
theorem B8445161 : Blo 1756579 8445161 := bstep (se 2 (by rfl) ⟨3166935, by rfl⟩ : syracuseStep 8445161 = 6333871) B6333871
theorem B28892609 : Blo 1756579 28892609 := bstep (se 2 (by rfl) ⟨10834728, by rfl⟩ : syracuseStep 28892609 = 21669457) B21669457
theorem B5004791 : Blo 1756579 5004791 := bstep (se 1 (by rfl) ⟨3753593, by rfl⟩ : syracuseStep 5004791 = 7507187) B7507187
theorem B175635985 : Blo 1756579 175635985 := bstep (se 2 (by rfl) ⟨65863494, by rfl⟩ : syracuseStep 175635985 = 131726989) B131726989
theorem B8560313 : Blo 1756579 8560313 := bstep (se 2 (by rfl) ⟨3210117, by rfl⟩ : syracuseStep 8560313 = 6420235) B6420235
theorem B21667601 : Blo 1756579 21667601 := bstep (se 2 (by rfl) ⟨8125350, by rfl⟩ : syracuseStep 21667601 = 16250701) B16250701
theorem B4448155 : Blo 1756579 4448155 := bstep (se 1 (by rfl) ⟨3336116, by rfl⟩ : syracuseStep 4448155 = 6672233) B6672233
theorem B2965673 : Blo 1756579 2965673 := bstep (se 2 (by rfl) ⟨1112127, by rfl⟩ : syracuseStep 2965673 = 2224255) B2224255
theorem B1876207 : Blo 1756579 1876207 := bstep (se 1 (by rfl) ⟨1407155, by rfl⟩ : syracuseStep 1876207 = 2814311) B2814311
theorem B5005577 : Blo 1756579 5005577 := bstep (se 2 (by rfl) ⟨1877091, by rfl⟩ : syracuseStep 5005577 = 3754183) B3754183
theorem B5628199 : Blo 1756579 5628199 := bstep (se 1 (by rfl) ⟨4221149, by rfl⟩ : syracuseStep 5628199 = 8442299) B8442299
theorem B12665321 : Blo 1756579 12665321 := bstep (se 2 (by rfl) ⟨4749495, by rfl⟩ : syracuseStep 12665321 = 9498991) B9498991
theorem B5005907 : Blo 1756579 5005907 := bstep (se 1 (by rfl) ⟨3754430, by rfl⟩ : syracuseStep 5005907 = 7508861) B7508861
theorem B22520429 : Blo 1756579 22520429 := bstep (se 3 (by rfl) ⟨4222580, by rfl⟩ : syracuseStep 22520429 = 8445161) B8445161
theorem B4449107 : Blo 1756579 4449107 := bstep (se 1 (by rfl) ⟨3336830, by rfl⟩ : syracuseStep 4449107 = 6673661) B6673661
theorem B2966395 : Blo 1756579 2966395 := bstep (se 1 (by rfl) ⟨2224796, by rfl⟩ : syracuseStep 2966395 = 4449593) B4449593
theorem B11256731 : Blo 1756579 11256731 := bstep (se 1 (by rfl) ⟨8442548, by rfl⟩ : syracuseStep 11256731 = 16885097) B16885097
theorem B4449289 : Blo 1756579 4449289 := bstep (se 2 (by rfl) ⟨1668483, by rfl⟩ : syracuseStep 4449289 = 3336967) B3336967
theorem B5629441 : Blo 1756579 5629441 := bstep (se 2 (by rfl) ⟨2111040, by rfl⟩ : syracuseStep 5629441 = 4222081) B4222081
theorem B10143427 : Blo 1756579 10143427 := bstep (se 1 (by rfl) ⟨7607570, by rfl⟩ : syracuseStep 10143427 = 15215141) B15215141
theorem B8898335 : Blo 1756579 8898335 := bstep (se 1 (by rfl) ⟨6673751, by rfl⟩ : syracuseStep 8898335 = 13347503) B13347503
theorem B50652971 : Blo 1756579 50652971 := bstep (se 1 (by rfl) ⟨37989728, by rfl⟩ : syracuseStep 50652971 = 75979457) B75979457
theorem B10831817 : Blo 1756579 10831817 := bstep (se 2 (by rfl) ⟨4061931, by rfl⟩ : syracuseStep 10831817 = 8123863) B8123863
theorem B19261739 : Blo 1756579 19261739 := bstep (se 1 (by rfl) ⟨14446304, by rfl⟩ : syracuseStep 19261739 = 28892609) B28892609
theorem B3336527 : Blo 1756579 3336527 := bstep (se 1 (by rfl) ⟨2502395, by rfl⟩ : syracuseStep 3336527 = 5004791) B5004791
theorem B34244963 : Blo 1756579 34244963 := bstep (se 1 (by rfl) ⟨25683722, by rfl⟩ : syracuseStep 34244963 = 51367445) B51367445
theorem B14445067 : Blo 1756579 14445067 := bstep (se 1 (by rfl) ⟨10833800, by rfl⟩ : syracuseStep 14445067 = 21667601) B21667601
theorem B2501695 : Blo 1756579 2501695 := bstep (se 1 (by rfl) ⟨1876271, by rfl⟩ : syracuseStep 2501695 = 3752543) B3752543
theorem B1756623 : Blo 1756579 1756623 := bstep (se 1 (by rfl) ⟨1317467, by rfl⟩ : syracuseStep 1756623 = 2634935) B2634935
theorem B1756783 : Blo 1756579 1756783 := bstep (se 1 (by rfl) ⟨1317587, by rfl⟩ : syracuseStep 1756783 = 2635175) B2635175
theorem B1756903 : Blo 1756579 1756903 := bstep (se 1 (by rfl) ⟨1317677, by rfl⟩ : syracuseStep 1756903 = 2635355) B2635355
theorem B81154001 : Blo 1756579 81154001 := bstep (se 2 (by rfl) ⟨30432750, by rfl⟩ : syracuseStep 81154001 = 60865501) B60865501
theorem B5418971 : Blo 1756579 5418971 := bstep (se 1 (by rfl) ⟨4064228, by rfl⟩ : syracuseStep 5418971 = 8128457) B8128457
theorem B1757211 : Blo 1756579 1757211 := bstep (se 1 (by rfl) ⟨1317908, by rfl⟩ : syracuseStep 1757211 = 2635817) B2635817
theorem B1757231 : Blo 1756579 1757231 := bstep (se 1 (by rfl) ⟨1317923, by rfl⟩ : syracuseStep 1757231 = 2635847) B2635847
theorem B175714433 : Blo 1756579 175714433 := bstep (se 2 (by rfl) ⟨65892912, by rfl⟩ : syracuseStep 175714433 = 131785825) B131785825
theorem B3952871 : Blo 1756579 3952871 := bstep (se 1 (by rfl) ⟨2964653, by rfl⟩ : syracuseStep 3952871 = 5929307) B5929307
theorem B7123241 : Blo 1756579 7123241 := bstep (se 2 (by rfl) ⟨2671215, by rfl⟩ : syracuseStep 7123241 = 5342431) B5342431
theorem B1757487 : Blo 1756579 1757487 := bstep (se 1 (by rfl) ⟨1318115, by rfl⟩ : syracuseStep 1757487 = 2636231) B2636231
theorem B4223303 : Blo 1756579 4223303 := bstep (se 1 (by rfl) ⟨3167477, by rfl⟩ : syracuseStep 4223303 = 6334955) B6334955
theorem B3953051 : Blo 1756579 3953051 := bstep (se 1 (by rfl) ⟨2964788, by rfl⟩ : syracuseStep 3953051 = 5929577) B5929577
theorem B1757631 : Blo 1756579 1757631 := bstep (se 1 (by rfl) ⟨1318223, by rfl⟩ : syracuseStep 1757631 = 2636447) B2636447
theorem B1757727 : Blo 1756579 1757727 := bstep (se 1 (by rfl) ⟨1318295, by rfl⟩ : syracuseStep 1757727 = 2636591) B2636591
theorem B1757807 : Blo 1756579 1757807 := bstep (se 1 (by rfl) ⟨1318355, by rfl⟩ : syracuseStep 1757807 = 2636711) B2636711
theorem B9015947 : Blo 1756579 9015947 := bstep (se 1 (by rfl) ⟨6761960, by rfl⟩ : syracuseStep 9015947 = 13523921) B13523921
theorem B234181313 : Blo 1756579 234181313 := bstep (se 2 (by rfl) ⟨87817992, by rfl⟩ : syracuseStep 234181313 = 175635985) B175635985
theorem B1757927 : Blo 1756579 1757927 := bstep (se 1 (by rfl) ⟨1318445, by rfl⟩ : syracuseStep 1757927 = 2636891) B2636891
theorem B25342865 : Blo 1756579 25342865 := bstep (se 2 (by rfl) ⟨9503574, by rfl⟩ : syracuseStep 25342865 = 19007149) B19007149
theorem B25343093 : Blo 1756579 25343093 := bstep (se 5 (by rfl) ⟨1187957, by rfl⟩ : syracuseStep 25343093 = 2375915) B2375915
theorem B5706875 : Blo 1756579 5706875 := bstep (se 1 (by rfl) ⟨4280156, by rfl⟩ : syracuseStep 5706875 = 8560313) B8560313
theorem B2635007 : Blo 1756579 2635007 := bstep (se 1 (by rfl) ⟨1976255, by rfl⟩ : syracuseStep 2635007 = 3952511) B3952511
theorem B2635049 : Blo 1756579 2635049 := bstep (se 2 (by rfl) ⟨988143, by rfl⟩ : syracuseStep 2635049 = 1976287) B1976287
theorem B8238547 : Blo 1756579 8238547 := bstep (se 1 (by rfl) ⟨6178910, by rfl⟩ : syracuseStep 8238547 = 12357821) B12357821
theorem B5928551 : Blo 1756579 5928551 := bstep (se 1 (by rfl) ⟨4446413, by rfl⟩ : syracuseStep 5928551 = 8892827) B8892827
theorem B7509611 : Blo 1756579 7509611 := bstep (se 1 (by rfl) ⟨5632208, by rfl⟩ : syracuseStep 7509611 = 11264417) B11264417
theorem B2635643 : Blo 1756579 2635643 := bstep (se 1 (by rfl) ⟨1976732, by rfl⟩ : syracuseStep 2635643 = 3953465) B3953465
theorem B2635679 : Blo 1756579 2635679 := bstep (se 1 (by rfl) ⟨1976759, by rfl⟩ : syracuseStep 2635679 = 3953519) B3953519
theorem B11261855 : Blo 1756579 11261855 := bstep (se 1 (by rfl) ⟨8446391, by rfl⟩ : syracuseStep 11261855 = 16892783) B16892783
theorem B5928875 : Blo 1756579 5928875 := bstep (se 1 (by rfl) ⟨4446656, by rfl⟩ : syracuseStep 5928875 = 8893313) B8893313
theorem B5928929 : Blo 1756579 5928929 := bstep (se 2 (by rfl) ⟨2223348, by rfl⟩ : syracuseStep 5928929 = 4446697) B4446697
theorem B8894447 : Blo 1756579 8894447 := bstep (se 1 (by rfl) ⟨6670835, by rfl⟩ : syracuseStep 8894447 = 13341671) B13341671
theorem B2635883 : Blo 1756579 2635883 := bstep (se 1 (by rfl) ⟨1976912, by rfl⟩ : syracuseStep 2635883 = 3953825) B3953825
theorem B2635913 : Blo 1756579 2635913 := bstep (se 2 (by rfl) ⟨988467, by rfl⟩ : syracuseStep 2635913 = 1976935) B1976935
theorem B2636063 : Blo 1756579 2636063 := bstep (se 1 (by rfl) ⟨1977047, by rfl⟩ : syracuseStep 2636063 = 3954095) B3954095
theorem B6674845 : Blo 1756579 6674845 := bstep (se 3 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 6674845 = 2503067) B2503067
theorem B19265951 : Blo 1756579 19265951 := bstep (se 1 (by rfl) ⟨14449463, by rfl⟩ : syracuseStep 19265951 = 28898927) B28898927
theorem B5929415 : Blo 1756579 5929415 := bstep (se 1 (by rfl) ⟨4447061, by rfl⟩ : syracuseStep 5929415 = 8894123) B8894123
theorem B7125479 : Blo 1756579 7125479 := bstep (se 1 (by rfl) ⟨5344109, by rfl⟩ : syracuseStep 7125479 = 10688219) B10688219
theorem B9140969 : Blo 1756579 9140969 := bstep (se 2 (by rfl) ⟨3427863, by rfl⟩ : syracuseStep 9140969 = 6855727) B6855727
theorem B3955625 : Blo 1756579 3955625 := bstep (se 2 (by rfl) ⟨1483359, by rfl⟩ : syracuseStep 3955625 = 2966719) B2966719
theorem B2636735 : Blo 1756579 2636735 := bstep (se 1 (by rfl) ⟨1977551, by rfl⟩ : syracuseStep 2636735 = 3955103) B3955103
theorem B2636783 : Blo 1756579 2636783 := bstep (se 1 (by rfl) ⟨1977587, by rfl⟩ : syracuseStep 2636783 = 3955175) B3955175
theorem B2636969 : Blo 1756579 2636969 := bstep (se 2 (by rfl) ⟨988863, by rfl⟩ : syracuseStep 2636969 = 1977727) B1977727
theorem B3006191 : Blo 1756579 3006191 := bstep (se 1 (by rfl) ⟨2254643, by rfl⟩ : syracuseStep 3006191 = 4509287) B4509287
theorem B5930873 : Blo 1756579 5930873 := bstep (se 2 (by rfl) ⟨2224077, by rfl⟩ : syracuseStep 5930873 = 4448155) B4448155
theorem B5005223 : Blo 1756579 5005223 := bstep (se 1 (by rfl) ⟨3753917, by rfl⟩ : syracuseStep 5005223 = 7507835) B7507835
theorem B7504265 : Blo 1756579 7504265 := bstep (se 2 (by rfl) ⟨2814099, by rfl⟩ : syracuseStep 7504265 = 5628199) B5628199
theorem B2966071 : Blo 1756579 2966071 := bstep (se 1 (by rfl) ⟨2224553, by rfl⟩ : syracuseStep 2966071 = 4449107) B4449107
theorem B7504487 : Blo 1756579 7504487 := bstep (se 1 (by rfl) ⟨5628365, by rfl⟩ : syracuseStep 7504487 = 11256731) B11256731
theorem B19260089 : Blo 1756579 19260089 := bstep (se 2 (by rfl) ⟨7222533, by rfl⟩ : syracuseStep 19260089 = 14445067) B14445067
theorem B5932223 : Blo 1756579 5932223 := bstep (se 1 (by rfl) ⟨4449167, by rfl⟩ : syracuseStep 5932223 = 8898335) B8898335
theorem B33768647 : Blo 1756579 33768647 := bstep (se 1 (by rfl) ⟨25326485, by rfl⟩ : syracuseStep 33768647 = 50652971) B50652971
theorem B5932385 : Blo 1756579 5932385 := bstep (se 2 (by rfl) ⟨2224644, by rfl⟩ : syracuseStep 5932385 = 4449289) B4449289
theorem B3335593 : Blo 1756579 3335593 := bstep (se 2 (by rfl) ⟨1250847, by rfl⟩ : syracuseStep 3335593 = 2501695) B2501695
theorem B7505921 : Blo 1756579 7505921 := bstep (se 2 (by rfl) ⟨2814720, by rfl⟩ : syracuseStep 7505921 = 5629441) B5629441
theorem B3336815 : Blo 1756579 3336815 := bstep (se 1 (by rfl) ⟨2502611, by rfl⟩ : syracuseStep 3336815 = 5005223) B5005223
theorem B54102667 : Blo 1756579 54102667 := bstep (se 1 (by rfl) ⟨40577000, by rfl⟩ : syracuseStep 54102667 = 81154001) B81154001
theorem B1977115 : Blo 1756579 1977115 := bstep (se 1 (by rfl) ⟨1482836, by rfl⟩ : syracuseStep 1977115 = 2965673) B2965673
theorem B3337051 : Blo 1756579 3337051 := bstep (se 1 (by rfl) ⟨2502788, by rfl⟩ : syracuseStep 3337051 = 5005577) B5005577
theorem B2501609 : Blo 1756579 2501609 := bstep (se 2 (by rfl) ⟨938103, by rfl⟩ : syracuseStep 2501609 = 1876207) B1876207
theorem B3337271 : Blo 1756579 3337271 := bstep (se 1 (by rfl) ⟨2502953, by rfl⟩ : syracuseStep 3337271 = 5005907) B5005907
theorem B8899793 : Blo 1756579 8899793 := bstep (se 2 (by rfl) ⟨3337422, by rfl⟩ : syracuseStep 8899793 = 6674845) B6674845
theorem B16895243 : Blo 1756579 16895243 := bstep (se 1 (by rfl) ⟨12671432, by rfl⟩ : syracuseStep 16895243 = 25342865) B25342865
theorem B16895395 : Blo 1756579 16895395 := bstep (se 1 (by rfl) ⟨12671546, by rfl⟩ : syracuseStep 16895395 = 25343093) B25343093
theorem B3804583 : Blo 1756579 3804583 := bstep (se 1 (by rfl) ⟨2853437, by rfl⟩ : syracuseStep 3804583 = 5706875) B5706875
theorem B1756671 : Blo 1756579 1756671 := bstep (se 1 (by rfl) ⟨1317503, by rfl⟩ : syracuseStep 1756671 = 2635007) B2635007
theorem B1756699 : Blo 1756579 1756699 := bstep (se 1 (by rfl) ⟨1317524, by rfl⟩ : syracuseStep 1756699 = 2635049) B2635049
theorem B3952367 : Blo 1756579 3952367 := bstep (se 1 (by rfl) ⟨2964275, by rfl⟩ : syracuseStep 3952367 = 5928551) B5928551
theorem B1757095 : Blo 1756579 1757095 := bstep (se 1 (by rfl) ⟨1317821, by rfl⟩ : syracuseStep 1757095 = 2635643) B2635643
theorem B1757119 : Blo 1756579 1757119 := bstep (se 1 (by rfl) ⟨1317839, by rfl⟩ : syracuseStep 1757119 = 2635679) B2635679
theorem B7507903 : Blo 1756579 7507903 := bstep (se 1 (by rfl) ⟨5630927, by rfl⟩ : syracuseStep 7507903 = 11261855) B11261855
theorem B3952583 : Blo 1756579 3952583 := bstep (se 1 (by rfl) ⟨2964437, by rfl⟩ : syracuseStep 3952583 = 5928875) B5928875
theorem B3952619 : Blo 1756579 3952619 := bstep (se 1 (by rfl) ⟨2964464, by rfl⟩ : syracuseStep 3952619 = 5928929) B5928929
theorem B1757255 : Blo 1756579 1757255 := bstep (se 1 (by rfl) ⟨1317941, by rfl⟩ : syracuseStep 1757255 = 2635883) B2635883
theorem B1757275 : Blo 1756579 1757275 := bstep (se 1 (by rfl) ⟨1317956, by rfl⟩ : syracuseStep 1757275 = 2635913) B2635913
theorem B1757375 : Blo 1756579 1757375 := bstep (se 1 (by rfl) ⟨1318031, by rfl⟩ : syracuseStep 1757375 = 2636063) B2636063
theorem B12841159 : Blo 1756579 12841159 := bstep (se 1 (by rfl) ⟨9630869, by rfl⟩ : syracuseStep 12841159 = 19261739) B19261739
theorem B2224351 : Blo 1756579 2224351 := bstep (se 1 (by rfl) ⟨1668263, by rfl⟩ : syracuseStep 2224351 = 3336527) B3336527
theorem B20025629 : Blo 1756579 20025629 := bstep (se 3 (by rfl) ⟨3754805, by rfl⟩ : syracuseStep 20025629 = 7509611) B7509611
theorem B3952943 : Blo 1756579 3952943 := bstep (se 1 (by rfl) ⟨2964707, by rfl⟩ : syracuseStep 3952943 = 5929415) B5929415
theorem B24375917 : Blo 1756579 24375917 := bstep (se 3 (by rfl) ⟨4570484, by rfl⟩ : syracuseStep 24375917 = 9140969) B9140969
theorem B8016509 : Blo 1756579 8016509 := bstep (se 3 (by rfl) ⟨1503095, by rfl⟩ : syracuseStep 8016509 = 3006191) B3006191
theorem B1757823 : Blo 1756579 1757823 := bstep (se 1 (by rfl) ⟨1318367, by rfl⟩ : syracuseStep 1757823 = 2636735) B2636735
theorem B1757855 : Blo 1756579 1757855 := bstep (se 1 (by rfl) ⟨1318391, by rfl⟩ : syracuseStep 1757855 = 2636783) B2636783
theorem B1757979 : Blo 1756579 1757979 := bstep (se 1 (by rfl) ⟨1318484, by rfl⟩ : syracuseStep 1757979 = 2636969) B2636969
theorem B3953915 : Blo 1756579 3953915 := bstep (se 1 (by rfl) ⟨2965436, by rfl⟩ : syracuseStep 3953915 = 5930873) B5930873
theorem B117142955 : Blo 1756579 117142955 := bstep (se 1 (by rfl) ⟨87857216, by rfl⟩ : syracuseStep 117142955 = 175714433) B175714433
theorem B2635247 : Blo 1756579 2635247 := bstep (se 1 (by rfl) ⟨1976435, by rfl⟩ : syracuseStep 2635247 = 3952871) B3952871
theorem B4748827 : Blo 1756579 4748827 := bstep (se 1 (by rfl) ⟨3561620, by rfl⟩ : syracuseStep 4748827 = 7123241) B7123241
theorem B2815535 : Blo 1756579 2815535 := bstep (se 1 (by rfl) ⟨2111651, by rfl⟩ : syracuseStep 2815535 = 4223303) B4223303
theorem B2635367 : Blo 1756579 2635367 := bstep (se 1 (by rfl) ⟨1976525, by rfl⟩ : syracuseStep 2635367 = 3953051) B3953051
theorem B8443547 : Blo 1756579 8443547 := bstep (se 1 (by rfl) ⟨6332660, by rfl⟩ : syracuseStep 8443547 = 12665321) B12665321
theorem B15013619 : Blo 1756579 15013619 := bstep (se 1 (by rfl) ⟨11260214, by rfl⟩ : syracuseStep 15013619 = 22520429) B22520429
theorem B6010631 : Blo 1756579 6010631 := bstep (se 1 (by rfl) ⟨4507973, by rfl⟩ : syracuseStep 6010631 = 9015947) B9015947
theorem B156120875 : Blo 1756579 156120875 := bstep (se 1 (by rfl) ⟨117090656, by rfl⟩ : syracuseStep 156120875 = 234181313) B234181313
theorem B3955193 : Blo 1756579 3955193 := bstep (se 2 (by rfl) ⟨1483197, by rfl⟩ : syracuseStep 3955193 = 2966395) B2966395
theorem B5929631 : Blo 1756579 5929631 := bstep (se 1 (by rfl) ⟨4447223, by rfl⟩ : syracuseStep 5929631 = 8894447) B8894447
theorem B22829975 : Blo 1756579 22829975 := bstep (se 1 (by rfl) ⟨17122481, by rfl⟩ : syracuseStep 22829975 = 34244963) B34244963
theorem B12843967 : Blo 1756579 12843967 := bstep (se 1 (by rfl) ⟨9632975, by rfl⟩ : syracuseStep 12843967 = 19265951) B19265951
theorem B4750319 : Blo 1756579 4750319 := bstep (se 1 (by rfl) ⟨3562739, by rfl⟩ : syracuseStep 4750319 = 7125479) B7125479
theorem B10984729 : Blo 1756579 10984729 := bstep (se 2 (by rfl) ⟨4119273, by rfl⟩ : syracuseStep 10984729 = 8238547) B8238547
theorem B2637083 : Blo 1756579 2637083 := bstep (se 1 (by rfl) ⟨1977812, by rfl⟩ : syracuseStep 2637083 = 3955625) B3955625
theorem B13524569 : Blo 1756579 13524569 := bstep (se 2 (by rfl) ⟨5071713, by rfl⟩ : syracuseStep 13524569 = 10143427) B10143427
theorem B28884845 : Blo 1756579 28884845 := bstep (se 3 (by rfl) ⟨5415908, by rfl⟩ : syracuseStep 28884845 = 10831817) B10831817
theorem B3612647 : Blo 1756579 3612647 := bstep (se 1 (by rfl) ⟨2709485, by rfl⟩ : syracuseStep 3612647 = 5418971) B5418971
theorem B17121545 : Blo 1756579 17121545 := bstep (se 2 (by rfl) ⟨6420579, by rfl⟩ : syracuseStep 17121545 = 12841159) B12841159
theorem B2965801 : Blo 1756579 2965801 := bstep (se 2 (by rfl) ⟨1112175, by rfl⟩ : syracuseStep 2965801 = 2224351) B2224351
theorem B22512431 : Blo 1756579 22512431 := bstep (se 1 (by rfl) ⟨16884323, by rfl⟩ : syracuseStep 22512431 = 33768647) B33768647
theorem B78095303 : Blo 1756579 78095303 := bstep (se 1 (by rfl) ⟨58571477, by rfl⟩ : syracuseStep 78095303 = 117142955) B117142955
theorem B1877023 : Blo 1756579 1877023 := bstep (se 1 (by rfl) ⟨1407767, by rfl⟩ : syracuseStep 1877023 = 2815535) B2815535
theorem B5629031 : Blo 1756579 5629031 := bstep (se 1 (by rfl) ⟨4221773, by rfl⟩ : syracuseStep 5629031 = 8443547) B8443547
theorem B4449401 : Blo 1756579 4449401 := bstep (se 2 (by rfl) ⟨1668525, by rfl⟩ : syracuseStep 4449401 = 3337051) B3337051
theorem B4007087 : Blo 1756579 4007087 := bstep (se 1 (by rfl) ⟨3005315, by rfl⟩ : syracuseStep 4007087 = 6010631) B6010631
theorem B104080583 : Blo 1756579 104080583 := bstep (se 1 (by rfl) ⟨78060437, by rfl⟩ : syracuseStep 104080583 = 156120875) B156120875
theorem B8898173 : Blo 1756579 8898173 := bstep (se 3 (by rfl) ⟨1668407, by rfl⟩ : syracuseStep 8898173 = 3336815) B3336815
theorem B5072777 : Blo 1756579 5072777 := bstep (se 2 (by rfl) ⟨1902291, by rfl⟩ : syracuseStep 5072777 = 3804583) B3804583
theorem B5933195 : Blo 1756579 5933195 := bstep (se 1 (by rfl) ⟨4449896, by rfl⟩ : syracuseStep 5933195 = 8899793) B8899793
theorem B6670957 : Blo 1756579 6670957 := bstep (se 3 (by rfl) ⟨1250804, by rfl⟩ : syracuseStep 6670957 = 2501609) B2501609
theorem B12840059 : Blo 1756579 12840059 := bstep (se 1 (by rfl) ⟨9630044, by rfl⟩ : syracuseStep 12840059 = 19260089) B19260089
theorem B1756831 : Blo 1756579 1756831 := bstep (se 1 (by rfl) ⟨1317623, by rfl⟩ : syracuseStep 1756831 = 2635247) B2635247
theorem B1756911 : Blo 1756579 1756911 := bstep (se 1 (by rfl) ⟨1317683, by rfl⟩ : syracuseStep 1756911 = 2635367) B2635367
theorem B17125289 : Blo 1756579 17125289 := bstep (se 2 (by rfl) ⟨6421983, by rfl⟩ : syracuseStep 17125289 = 12843967) B12843967
theorem B21377357 : Blo 1756579 21377357 := bstep (se 3 (by rfl) ⟨4008254, by rfl⟩ : syracuseStep 21377357 = 8016509) B8016509
theorem B3953087 : Blo 1756579 3953087 := bstep (se 1 (by rfl) ⟨2964815, by rfl⟩ : syracuseStep 3953087 = 5929631) B5929631
theorem B3166879 : Blo 1756579 3166879 := bstep (se 1 (by rfl) ⟨2375159, by rfl⟩ : syracuseStep 3166879 = 4750319) B4750319
theorem B2224847 : Blo 1756579 2224847 := bstep (se 1 (by rfl) ⟨1668635, by rfl⟩ : syracuseStep 2224847 = 3337271) B3337271
theorem B1758055 : Blo 1756579 1758055 := bstep (se 1 (by rfl) ⟨1318541, by rfl⟩ : syracuseStep 1758055 = 2637083) B2637083
theorem B9016379 : Blo 1756579 9016379 := bstep (se 1 (by rfl) ⟨6762284, by rfl⟩ : syracuseStep 9016379 = 13524569) B13524569
theorem B2634911 : Blo 1756579 2634911 := bstep (se 1 (by rfl) ⟨1976183, by rfl⟩ : syracuseStep 2634911 = 3952367) B3952367
theorem B19256563 : Blo 1756579 19256563 := bstep (se 1 (by rfl) ⟨14442422, by rfl⟩ : syracuseStep 19256563 = 28884845) B28884845
theorem B2635055 : Blo 1756579 2635055 := bstep (se 1 (by rfl) ⟨1976291, by rfl⟩ : syracuseStep 2635055 = 3952583) B3952583
theorem B2635079 : Blo 1756579 2635079 := bstep (se 1 (by rfl) ⟨1976309, by rfl⟩ : syracuseStep 2635079 = 3952619) B3952619
theorem B13350419 : Blo 1756579 13350419 := bstep (se 1 (by rfl) ⟨10012814, by rfl⟩ : syracuseStep 13350419 = 20025629) B20025629
theorem B2635295 : Blo 1756579 2635295 := bstep (se 1 (by rfl) ⟨1976471, by rfl⟩ : syracuseStep 2635295 = 3952943) B3952943
theorem B5002843 : Blo 1756579 5002843 := bstep (se 1 (by rfl) ⟨3752132, by rfl⟩ : syracuseStep 5002843 = 7504265) B7504265
theorem B5002991 : Blo 1756579 5002991 := bstep (se 1 (by rfl) ⟨3752243, by rfl⟩ : syracuseStep 5002991 = 7504487) B7504487
theorem B16250611 : Blo 1756579 16250611 := bstep (se 1 (by rfl) ⟨12187958, by rfl⟩ : syracuseStep 16250611 = 24375917) B24375917
theorem B3954761 : Blo 1756579 3954761 := bstep (se 2 (by rfl) ⟨1483035, by rfl⟩ : syracuseStep 3954761 = 2966071) B2966071
theorem B3954815 : Blo 1756579 3954815 := bstep (se 1 (by rfl) ⟨2966111, by rfl⟩ : syracuseStep 3954815 = 5932223) B5932223
theorem B2635943 : Blo 1756579 2635943 := bstep (se 1 (by rfl) ⟨1976957, by rfl⟩ : syracuseStep 2635943 = 3953915) B3953915
theorem B72136889 : Blo 1756579 72136889 := bstep (se 2 (by rfl) ⟨27051333, by rfl⟩ : syracuseStep 72136889 = 54102667) B54102667
theorem B3954923 : Blo 1756579 3954923 := bstep (se 1 (by rfl) ⟨2966192, by rfl⟩ : syracuseStep 3954923 = 5932385) B5932385
theorem B2636153 : Blo 1756579 2636153 := bstep (se 2 (by rfl) ⟨988557, by rfl⟩ : syracuseStep 2636153 = 1977115) B1977115
theorem B10009079 : Blo 1756579 10009079 := bstep (se 1 (by rfl) ⟨7506809, by rfl⟩ : syracuseStep 10009079 = 15013619) B15013619
theorem B5003947 : Blo 1756579 5003947 := bstep (se 1 (by rfl) ⟨3752960, by rfl⟩ : syracuseStep 5003947 = 7505921) B7505921
theorem B2636795 : Blo 1756579 2636795 := bstep (se 1 (by rfl) ⟨1977596, by rfl⟩ : syracuseStep 2636795 = 3955193) B3955193
theorem B14646305 : Blo 1756579 14646305 := bstep (se 2 (by rfl) ⟨5492364, by rfl⟩ : syracuseStep 14646305 = 10984729) B10984729
theorem B22527193 : Blo 1756579 22527193 := bstep (se 2 (by rfl) ⟨8447697, by rfl⟩ : syracuseStep 22527193 = 16895395) B16895395
theorem B4447457 : Blo 1756579 4447457 := bstep (se 2 (by rfl) ⟨1667796, by rfl⟩ : syracuseStep 4447457 = 3335593) B3335593
theorem B15219983 : Blo 1756579 15219983 := bstep (se 1 (by rfl) ⟨11414987, by rfl⟩ : syracuseStep 15219983 = 22829975) B22829975
theorem B6331769 : Blo 1756579 6331769 := bstep (se 2 (by rfl) ⟨2374413, by rfl⟩ : syracuseStep 6331769 = 4748827) B4748827
theorem B11263495 : Blo 1756579 11263495 := bstep (se 1 (by rfl) ⟨8447621, by rfl⟩ : syracuseStep 11263495 = 16895243) B16895243
theorem B10010537 : Blo 1756579 10010537 := bstep (se 2 (by rfl) ⟨3753951, by rfl⟩ : syracuseStep 10010537 = 7507903) B7507903
theorem B9633725 : Blo 1756579 9633725 := bstep (se 3 (by rfl) ⟨1806323, by rfl⟩ : syracuseStep 9633725 = 3612647) B3612647
theorem B10010789 : Blo 1756579 10010789 := bstep (se 4 (by rfl) ⟨938511, by rfl⟩ : syracuseStep 10010789 = 1877023) B1877023
theorem B15008287 : Blo 1756579 15008287 := bstep (se 1 (by rfl) ⟨11256215, by rfl⟩ : syracuseStep 15008287 = 22512431) B22512431
theorem B3752687 : Blo 1756579 3752687 := bstep (se 1 (by rfl) ⟨2814515, by rfl⟩ : syracuseStep 3752687 = 5629031) B5629031
theorem B2966267 : Blo 1756579 2966267 := bstep (se 1 (by rfl) ⟨2224700, by rfl⟩ : syracuseStep 2966267 = 4449401) B4449401
theorem B2671391 : Blo 1756579 2671391 := bstep (se 1 (by rfl) ⟨2003543, by rfl⟩ : syracuseStep 2671391 = 4007087) B4007087
theorem B5932115 : Blo 1756579 5932115 := bstep (se 1 (by rfl) ⟨4449086, by rfl⟩ : syracuseStep 5932115 = 8898173) B8898173
theorem B3335327 : Blo 1756579 3335327 := bstep (se 1 (by rfl) ⟨2501495, by rfl⟩ : syracuseStep 3335327 = 5002991) B5002991
theorem B25675417 : Blo 1756579 25675417 := bstep (se 2 (by rfl) ⟨9628281, by rfl⟩ : syracuseStep 25675417 = 19256563) B19256563
theorem B5932925 : Blo 1756579 5932925 := bstep (se 3 (by rfl) ⟨1112423, by rfl⟩ : syracuseStep 5932925 = 2224847) B2224847
theorem B15017993 : Blo 1756579 15017993 := bstep (se 2 (by rfl) ⟨5631747, by rfl⟩ : syracuseStep 15017993 = 11263495) B11263495
theorem B6670457 : Blo 1756579 6670457 := bstep (se 2 (by rfl) ⟨2501421, by rfl⟩ : syracuseStep 6670457 = 5002843) B5002843
theorem B4221179 : Blo 1756579 4221179 := bstep (se 1 (by rfl) ⟨3165884, by rfl⟩ : syracuseStep 4221179 = 6331769) B6331769
theorem B11414363 : Blo 1756579 11414363 := bstep (se 1 (by rfl) ⟨8560772, by rfl⟩ : syracuseStep 11414363 = 17121545) B17121545
theorem B277548221 : Blo 1756579 277548221 := bstep (se 3 (by rfl) ⟨52040291, by rfl⟩ : syracuseStep 277548221 = 104080583) B104080583
theorem B52063535 : Blo 1756579 52063535 := bstep (se 1 (by rfl) ⟨39047651, by rfl⟩ : syracuseStep 52063535 = 78095303) B78095303
theorem B1756607 : Blo 1756579 1756607 := bstep (se 1 (by rfl) ⟨1317455, by rfl⟩ : syracuseStep 1756607 = 2634911) B2634911
theorem B1756703 : Blo 1756579 1756703 := bstep (se 1 (by rfl) ⟨1317527, by rfl⟩ : syracuseStep 1756703 = 2635055) B2635055
theorem B4222505 : Blo 1756579 4222505 := bstep (se 2 (by rfl) ⟨1583439, by rfl⟩ : syracuseStep 4222505 = 3166879) B3166879
theorem B1756719 : Blo 1756579 1756719 := bstep (se 1 (by rfl) ⟨1317539, by rfl⟩ : syracuseStep 1756719 = 2635079) B2635079
theorem B6671929 : Blo 1756579 6671929 := bstep (se 2 (by rfl) ⟨2501973, by rfl⟩ : syracuseStep 6671929 = 5003947) B5003947
theorem B8900279 : Blo 1756579 8900279 := bstep (se 1 (by rfl) ⟨6675209, by rfl⟩ : syracuseStep 8900279 = 13350419) B13350419
theorem B1756863 : Blo 1756579 1756863 := bstep (se 1 (by rfl) ⟨1317647, by rfl⟩ : syracuseStep 1756863 = 2635295) B2635295
theorem B1757295 : Blo 1756579 1757295 := bstep (se 1 (by rfl) ⟨1317971, by rfl⟩ : syracuseStep 1757295 = 2635943) B2635943
theorem B48091259 : Blo 1756579 48091259 := bstep (se 1 (by rfl) ⟨36068444, by rfl⟩ : syracuseStep 48091259 = 72136889) B72136889
theorem B1757435 : Blo 1756579 1757435 := bstep (se 1 (by rfl) ⟨1318076, by rfl⟩ : syracuseStep 1757435 = 2636153) B2636153
theorem B30036257 : Blo 1756579 30036257 := bstep (se 2 (by rfl) ⟨11263596, by rfl⟩ : syracuseStep 30036257 = 22527193) B22527193
theorem B6672719 : Blo 1756579 6672719 := bstep (se 1 (by rfl) ⟨5004539, by rfl⟩ : syracuseStep 6672719 = 10009079) B10009079
theorem B1757863 : Blo 1756579 1757863 := bstep (se 1 (by rfl) ⟨1318397, by rfl⟩ : syracuseStep 1757863 = 2636795) B2636795
theorem B10146655 : Blo 1756579 10146655 := bstep (se 1 (by rfl) ⟨7609991, by rfl⟩ : syracuseStep 10146655 = 15219983) B15219983
theorem B6673691 : Blo 1756579 6673691 := bstep (se 1 (by rfl) ⟨5005268, by rfl⟩ : syracuseStep 6673691 = 10010537) B10010537
theorem B11416859 : Blo 1756579 11416859 := bstep (se 1 (by rfl) ⟨8562644, by rfl⟩ : syracuseStep 11416859 = 17125289) B17125289
theorem B39056813 : Blo 1756579 39056813 := bstep (se 3 (by rfl) ⟨7323152, by rfl⟩ : syracuseStep 39056813 = 14646305) B14646305
theorem B14251571 : Blo 1756579 14251571 := bstep (se 1 (by rfl) ⟨10688678, by rfl⟩ : syracuseStep 14251571 = 21377357) B21377357
theorem B2635391 : Blo 1756579 2635391 := bstep (se 1 (by rfl) ⟨1976543, by rfl⟩ : syracuseStep 2635391 = 3953087) B3953087
theorem B3954401 : Blo 1756579 3954401 := bstep (se 2 (by rfl) ⟨1482900, by rfl⟩ : syracuseStep 3954401 = 2965801) B2965801
theorem B6010919 : Blo 1756579 6010919 := bstep (se 1 (by rfl) ⟨4508189, by rfl⟩ : syracuseStep 6010919 = 9016379) B9016379
theorem B8894609 : Blo 1756579 8894609 := bstep (se 2 (by rfl) ⟨3335478, by rfl⟩ : syracuseStep 8894609 = 6670957) B6670957
theorem B3381851 : Blo 1756579 3381851 := bstep (se 1 (by rfl) ⟨2536388, by rfl⟩ : syracuseStep 3381851 = 5072777) B5072777
theorem B2636507 : Blo 1756579 2636507 := bstep (se 1 (by rfl) ⟨1977380, by rfl⟩ : syracuseStep 2636507 = 3954761) B3954761
theorem B2636543 : Blo 1756579 2636543 := bstep (se 1 (by rfl) ⟨1977407, by rfl⟩ : syracuseStep 2636543 = 3954815) B3954815
theorem B3955463 : Blo 1756579 3955463 := bstep (se 1 (by rfl) ⟨2966597, by rfl⟩ : syracuseStep 3955463 = 5933195) B5933195
theorem B2636615 : Blo 1756579 2636615 := bstep (se 1 (by rfl) ⟨1977461, by rfl⟩ : syracuseStep 2636615 = 3954923) B3954923
theorem B8560039 : Blo 1756579 8560039 := bstep (se 1 (by rfl) ⟨6420029, by rfl⟩ : syracuseStep 8560039 = 12840059) B12840059
theorem B2964971 : Blo 1756579 2964971 := bstep (se 1 (by rfl) ⟨2223728, by rfl⟩ : syracuseStep 2964971 = 4447457) B4447457
theorem B21667481 : Blo 1756579 21667481 := bstep (se 2 (by rfl) ⟨8125305, by rfl⟩ : syracuseStep 21667481 = 16250611) B16250611
theorem B6422483 : Blo 1756579 6422483 := bstep (se 1 (by rfl) ⟨4816862, by rfl⟩ : syracuseStep 6422483 = 9633725) B9633725
theorem B4448479 : Blo 1756579 4448479 := bstep (se 1 (by rfl) ⟨3336359, by rfl⟩ : syracuseStep 4448479 = 6672719) B6672719
theorem B4449127 : Blo 1756579 4449127 := bstep (se 1 (by rfl) ⟨3336845, by rfl⟩ : syracuseStep 4449127 = 6673691) B6673691
theorem B7611239 : Blo 1756579 7611239 := bstep (se 1 (by rfl) ⟨5708429, by rfl⟩ : syracuseStep 7611239 = 11416859) B11416859
theorem B10011995 : Blo 1756579 10011995 := bstep (se 1 (by rfl) ⟨7508996, by rfl⟩ : syracuseStep 10011995 = 15017993) B15017993
theorem B4007279 : Blo 1756579 4007279 := bstep (se 1 (by rfl) ⟨3005459, by rfl⟩ : syracuseStep 4007279 = 6010919) B6010919
theorem B2254567 : Blo 1756579 2254567 := bstep (se 1 (by rfl) ⟨1690925, by rfl⟩ : syracuseStep 2254567 = 3381851) B3381851
theorem B11413385 : Blo 1756579 11413385 := bstep (se 2 (by rfl) ⟨4280019, by rfl⟩ : syracuseStep 11413385 = 8560039) B8560039
theorem B1976647 : Blo 1756579 1976647 := bstep (se 1 (by rfl) ⟨1482485, by rfl⟩ : syracuseStep 1976647 = 2964971) B2964971
theorem B14444987 : Blo 1756579 14444987 := bstep (se 1 (by rfl) ⟨10833740, by rfl⟩ : syracuseStep 14444987 = 21667481) B21667481
theorem B5933519 : Blo 1756579 5933519 := bstep (se 1 (by rfl) ⟨4450139, by rfl⟩ : syracuseStep 5933519 = 8900279) B8900279
theorem B20024171 : Blo 1756579 20024171 := bstep (se 1 (by rfl) ⟨15018128, by rfl⟩ : syracuseStep 20024171 = 30036257) B30036257
theorem B1977511 : Blo 1756579 1977511 := bstep (se 1 (by rfl) ⟨1483133, by rfl⟩ : syracuseStep 1977511 = 2966267) B2966267
theorem B2223551 : Blo 1756579 2223551 := bstep (se 1 (by rfl) ⟨1667663, by rfl⟩ : syracuseStep 2223551 = 3335327) B3335327
theorem B26037875 : Blo 1756579 26037875 := bstep (se 1 (by rfl) ⟨19528406, by rfl⟩ : syracuseStep 26037875 = 39056813) B39056813
theorem B1756927 : Blo 1756579 1756927 := bstep (se 1 (by rfl) ⟨1317695, by rfl⟩ : syracuseStep 1756927 = 2635391) B2635391
theorem B13528873 : Blo 1756579 13528873 := bstep (se 2 (by rfl) ⟨5073327, by rfl⟩ : syracuseStep 13528873 = 10146655) B10146655
theorem B2814119 : Blo 1756579 2814119 := bstep (se 1 (by rfl) ⟨2110589, by rfl⟩ : syracuseStep 2814119 = 4221179) B4221179
theorem B1757671 : Blo 1756579 1757671 := bstep (se 1 (by rfl) ⟨1318253, by rfl⟩ : syracuseStep 1757671 = 2636507) B2636507
theorem B1757695 : Blo 1756579 1757695 := bstep (se 1 (by rfl) ⟨1318271, by rfl⟩ : syracuseStep 1757695 = 2636543) B2636543
theorem B1757743 : Blo 1756579 1757743 := bstep (se 1 (by rfl) ⟨1318307, by rfl⟩ : syracuseStep 1757743 = 2636615) B2636615
theorem B10007165 : Blo 1756579 10007165 := bstep (se 3 (by rfl) ⟨1876343, by rfl⟩ : syracuseStep 10007165 = 3752687) B3752687
theorem B7123709 : Blo 1756579 7123709 := bstep (se 3 (by rfl) ⟨1335695, by rfl⟩ : syracuseStep 7123709 = 2671391) B2671391
theorem B30438301 : Blo 1756579 30438301 := bstep (se 3 (by rfl) ⟨5707181, by rfl⟩ : syracuseStep 30438301 = 11414363) B11414363
theorem B2815003 : Blo 1756579 2815003 := bstep (se 1 (by rfl) ⟨2111252, by rfl⟩ : syracuseStep 2815003 = 4222505) B4222505
theorem B4281655 : Blo 1756579 4281655 := bstep (se 1 (by rfl) ⟨3211241, by rfl⟩ : syracuseStep 4281655 = 6422483) B6422483
theorem B6673859 : Blo 1756579 6673859 := bstep (se 1 (by rfl) ⟨5005394, by rfl⟩ : syracuseStep 6673859 = 10010789) B10010789
theorem B128243357 : Blo 1756579 128243357 := bstep (se 3 (by rfl) ⟨24045629, by rfl⟩ : syracuseStep 128243357 = 48091259) B48091259
theorem B740128589 : Blo 1756579 740128589 := bstep (se 3 (by rfl) ⟨138774110, by rfl⟩ : syracuseStep 740128589 = 277548221) B277548221
theorem B20011049 : Blo 1756579 20011049 := bstep (se 2 (by rfl) ⟨7504143, by rfl⟩ : syracuseStep 20011049 = 15008287) B15008287
theorem B3954743 : Blo 1756579 3954743 := bstep (se 1 (by rfl) ⟨2966057, by rfl⟩ : syracuseStep 3954743 = 5932115) B5932115
theorem B9501047 : Blo 1756579 9501047 := bstep (se 1 (by rfl) ⟨7125785, by rfl⟩ : syracuseStep 9501047 = 14251571) B14251571
theorem B2636267 : Blo 1756579 2636267 := bstep (se 1 (by rfl) ⟨1977200, by rfl⟩ : syracuseStep 2636267 = 3954401) B3954401
theorem B3955283 : Blo 1756579 3955283 := bstep (se 1 (by rfl) ⟨2966462, by rfl⟩ : syracuseStep 3955283 = 5932925) B5932925
theorem B4446971 : Blo 1756579 4446971 := bstep (se 1 (by rfl) ⟨3335228, by rfl⟩ : syracuseStep 4446971 = 6670457) B6670457
theorem B5929739 : Blo 1756579 5929739 := bstep (se 1 (by rfl) ⟨4447304, by rfl⟩ : syracuseStep 5929739 = 8894609) B8894609
theorem B2636975 : Blo 1756579 2636975 := bstep (se 1 (by rfl) ⟨1977731, by rfl⟩ : syracuseStep 2636975 = 3955463) B3955463
theorem B8895905 : Blo 1756579 8895905 := bstep (se 2 (by rfl) ⟨3335964, by rfl⟩ : syracuseStep 8895905 = 6671929) B6671929
theorem B34709023 : Blo 1756579 34709023 := bstep (se 1 (by rfl) ⟨26031767, by rfl⟩ : syracuseStep 34709023 = 52063535) B52063535
theorem B34233889 : Blo 1756579 34233889 := bstep (se 2 (by rfl) ⟨12837708, by rfl⟩ : syracuseStep 34233889 = 25675417) B25675417
theorem B1876079 : Blo 1756579 1876079 := bstep (se 1 (by rfl) ⟨1407059, by rfl⟩ : syracuseStep 1876079 = 2814119) B2814119
theorem B5931305 : Blo 1756579 5931305 := bstep (se 2 (by rfl) ⟨2224239, by rfl⟩ : syracuseStep 5931305 = 4448479) B4448479
theorem B4449239 : Blo 1756579 4449239 := bstep (se 1 (by rfl) ⟨3336929, by rfl⟩ : syracuseStep 4449239 = 6673859) B6673859
theorem B5932169 : Blo 1756579 5932169 := bstep (se 2 (by rfl) ⟨2224563, by rfl⟩ : syracuseStep 5932169 = 4449127) B4449127
theorem B38519965 : Blo 1756579 38519965 := bstep (se 3 (by rfl) ⟨7222493, by rfl⟩ : syracuseStep 38519965 = 14444987) B14444987
theorem B40584401 : Blo 1756579 40584401 := bstep (se 2 (by rfl) ⟨15219150, by rfl⟩ : syracuseStep 40584401 = 30438301) B30438301
theorem B3753337 : Blo 1756579 3753337 := bstep (se 2 (by rfl) ⟨1407501, by rfl⟩ : syracuseStep 3753337 = 2815003) B2815003
theorem B6334031 : Blo 1756579 6334031 := bstep (se 1 (by rfl) ⟨4750523, by rfl⟩ : syracuseStep 6334031 = 9501047) B9501047
theorem B46278697 : Blo 1756579 46278697 := bstep (se 2 (by rfl) ⟨17354511, by rfl⟩ : syracuseStep 46278697 = 34709023) B34709023
theorem B6671443 : Blo 1756579 6671443 := bstep (se 1 (by rfl) ⟨5003582, by rfl⟩ : syracuseStep 6671443 = 10007165) B10007165
theorem B5074159 : Blo 1756579 5074159 := bstep (se 1 (by rfl) ⟨3805619, by rfl⟩ : syracuseStep 5074159 = 7611239) B7611239
theorem B10686077 : Blo 1756579 10686077 := bstep (se 3 (by rfl) ⟨2003639, by rfl⟩ : syracuseStep 10686077 = 4007279) B4007279
theorem B85495571 : Blo 1756579 85495571 := bstep (se 1 (by rfl) ⟨64121678, by rfl⟩ : syracuseStep 85495571 = 128243357) B128243357
theorem B13340699 : Blo 1756579 13340699 := bstep (se 1 (by rfl) ⟨10005524, by rfl⟩ : syracuseStep 13340699 = 20011049) B20011049
theorem B1757511 : Blo 1756579 1757511 := bstep (se 1 (by rfl) ⟨1318133, by rfl⟩ : syracuseStep 1757511 = 2636267) B2636267
theorem B3953159 : Blo 1756579 3953159 := bstep (se 1 (by rfl) ⟨2964869, by rfl⟩ : syracuseStep 3953159 = 5929739) B5929739
theorem B13349447 : Blo 1756579 13349447 := bstep (se 1 (by rfl) ⟨10012085, by rfl⟩ : syracuseStep 13349447 = 20024171) B20024171
theorem B1757983 : Blo 1756579 1757983 := bstep (se 1 (by rfl) ⟨1318487, by rfl⟩ : syracuseStep 1757983 = 2636975) B2636975
theorem B2635529 : Blo 1756579 2635529 := bstep (se 2 (by rfl) ⟨988323, by rfl⟩ : syracuseStep 2635529 = 1976647) B1976647
theorem B4749139 : Blo 1756579 4749139 := bstep (se 1 (by rfl) ⟨3561854, by rfl⟩ : syracuseStep 4749139 = 7123709) B7123709
theorem B6674663 : Blo 1756579 6674663 := bstep (se 1 (by rfl) ⟨5005997, by rfl⟩ : syracuseStep 6674663 = 10011995) B10011995
theorem B5929469 : Blo 1756579 5929469 := bstep (se 3 (by rfl) ⟨1111775, by rfl⟩ : syracuseStep 5929469 = 2223551) B2223551
theorem B493419059 : Blo 1756579 493419059 := bstep (se 1 (by rfl) ⟨370064294, by rfl⟩ : syracuseStep 493419059 = 740128589) B740128589
theorem B7608923 : Blo 1756579 7608923 := bstep (se 1 (by rfl) ⟨5706692, by rfl⟩ : syracuseStep 7608923 = 11413385) B11413385
theorem B2636495 : Blo 1756579 2636495 := bstep (se 1 (by rfl) ⟨1977371, by rfl⟩ : syracuseStep 2636495 = 3954743) B3954743
theorem B2636681 : Blo 1756579 2636681 := bstep (se 2 (by rfl) ⟨988755, by rfl⟩ : syracuseStep 2636681 = 1977511) B1977511
theorem B3955679 : Blo 1756579 3955679 := bstep (se 1 (by rfl) ⟨2966759, by rfl⟩ : syracuseStep 3955679 = 5933519) B5933519
theorem B2636855 : Blo 1756579 2636855 := bstep (se 1 (by rfl) ⟨1977641, by rfl⟩ : syracuseStep 2636855 = 3955283) B3955283
theorem B5708873 : Blo 1756579 5708873 := bstep (se 2 (by rfl) ⟨2140827, by rfl⟩ : syracuseStep 5708873 = 4281655) B4281655
theorem B2964647 : Blo 1756579 2964647 := bstep (se 1 (by rfl) ⟨2223485, by rfl⟩ : syracuseStep 2964647 = 4446971) B4446971
theorem B45645185 : Blo 1756579 45645185 := bstep (se 2 (by rfl) ⟨17116944, by rfl⟩ : syracuseStep 45645185 = 34233889) B34233889
theorem B5930603 : Blo 1756579 5930603 := bstep (se 1 (by rfl) ⟨4447952, by rfl⟩ : syracuseStep 5930603 = 8895905) B8895905
theorem B3006089 : Blo 1756579 3006089 := bstep (se 2 (by rfl) ⟨1127283, by rfl⟩ : syracuseStep 3006089 = 2254567) B2254567
theorem B18038497 : Blo 1756579 18038497 := bstep (se 2 (by rfl) ⟨6764436, by rfl⟩ : syracuseStep 18038497 = 13528873) B13528873
theorem B17358583 : Blo 1756579 17358583 := bstep (se 1 (by rfl) ⟨13018937, by rfl⟩ : syracuseStep 17358583 = 26037875) B26037875
theorem B2966159 : Blo 1756579 2966159 := bstep (se 1 (by rfl) ⟨2224619, by rfl⟩ : syracuseStep 2966159 = 4449239) B4449239
theorem B4449775 : Blo 1756579 4449775 := bstep (se 1 (by rfl) ⟨3337331, by rfl⟩ : syracuseStep 4449775 = 6674663) B6674663
theorem B5072615 : Blo 1756579 5072615 := bstep (se 1 (by rfl) ⟨3804461, by rfl⟩ : syracuseStep 5072615 = 7608923) B7608923
theorem B1976431 : Blo 1756579 1976431 := bstep (se 1 (by rfl) ⟨1482323, by rfl⟩ : syracuseStep 1976431 = 2964647) B2964647
theorem B23144777 : Blo 1756579 23144777 := bstep (se 2 (by rfl) ⟨8679291, by rfl⟩ : syracuseStep 23144777 = 17358583) B17358583
theorem B61704929 : Blo 1756579 61704929 := bstep (se 2 (by rfl) ⟨23139348, by rfl⟩ : syracuseStep 61704929 = 46278697) B46278697
theorem B8899631 : Blo 1756579 8899631 := bstep (se 1 (by rfl) ⟨6674723, by rfl⟩ : syracuseStep 8899631 = 13349447) B13349447
theorem B4222687 : Blo 1756579 4222687 := bstep (se 1 (by rfl) ⟨3167015, by rfl⟩ : syracuseStep 4222687 = 6334031) B6334031
theorem B1757019 : Blo 1756579 1757019 := bstep (se 1 (by rfl) ⟨1317764, by rfl⟩ : syracuseStep 1757019 = 2635529) B2635529
theorem B51359953 : Blo 1756579 51359953 := bstep (se 2 (by rfl) ⟨19259982, by rfl⟩ : syracuseStep 51359953 = 38519965) B38519965
theorem B3952979 : Blo 1756579 3952979 := bstep (se 1 (by rfl) ⟨2964734, by rfl⟩ : syracuseStep 3952979 = 5929469) B5929469
theorem B328946039 : Blo 1756579 328946039 := bstep (se 1 (by rfl) ⟨246709529, by rfl⟩ : syracuseStep 328946039 = 493419059) B493419059
theorem B1757663 : Blo 1756579 1757663 := bstep (se 1 (by rfl) ⟨1318247, by rfl⟩ : syracuseStep 1757663 = 2636495) B2636495
theorem B1757787 : Blo 1756579 1757787 := bstep (se 1 (by rfl) ⟨1318340, by rfl⟩ : syracuseStep 1757787 = 2636681) B2636681
theorem B1757903 : Blo 1756579 1757903 := bstep (se 1 (by rfl) ⟨1318427, by rfl⟩ : syracuseStep 1757903 = 2636855) B2636855
theorem B3805915 : Blo 1756579 3805915 := bstep (se 1 (by rfl) ⟨2854436, by rfl⟩ : syracuseStep 3805915 = 5708873) B5708873
theorem B30430123 : Blo 1756579 30430123 := bstep (se 1 (by rfl) ⟨22822592, by rfl⟩ : syracuseStep 30430123 = 45645185) B45645185
theorem B3953735 : Blo 1756579 3953735 := bstep (se 1 (by rfl) ⟨2965301, by rfl⟩ : syracuseStep 3953735 = 5930603) B5930603
theorem B7124051 : Blo 1756579 7124051 := bstep (se 1 (by rfl) ⟨5343038, by rfl⟩ : syracuseStep 7124051 = 10686077) B10686077
theorem B2004059 : Blo 1756579 2004059 := bstep (se 1 (by rfl) ⟨1503044, by rfl⟩ : syracuseStep 2004059 = 3006089) B3006089
theorem B56997047 : Blo 1756579 56997047 := bstep (se 1 (by rfl) ⟨42747785, by rfl⟩ : syracuseStep 56997047 = 85495571) B85495571
theorem B8893799 : Blo 1756579 8893799 := bstep (se 1 (by rfl) ⟨6670349, by rfl⟩ : syracuseStep 8893799 = 13340699) B13340699
theorem B3954203 : Blo 1756579 3954203 := bstep (se 1 (by rfl) ⟨2965652, by rfl⟩ : syracuseStep 3954203 = 5931305) B5931305
theorem B5002877 : Blo 1756579 5002877 := bstep (se 3 (by rfl) ⟨938039, by rfl⟩ : syracuseStep 5002877 = 1876079) B1876079
theorem B2635439 : Blo 1756579 2635439 := bstep (se 1 (by rfl) ⟨1976579, by rfl⟩ : syracuseStep 2635439 = 3953159) B3953159
theorem B3954779 : Blo 1756579 3954779 := bstep (se 1 (by rfl) ⟨2966084, by rfl⟩ : syracuseStep 3954779 = 5932169) B5932169
theorem B27056267 : Blo 1756579 27056267 := bstep (se 1 (by rfl) ⟨20292200, by rfl⟩ : syracuseStep 27056267 = 40584401) B40584401
theorem B8895257 : Blo 1756579 8895257 := bstep (se 2 (by rfl) ⟨3335721, by rfl⟩ : syracuseStep 8895257 = 6671443) B6671443
theorem B6765545 : Blo 1756579 6765545 := bstep (se 2 (by rfl) ⟨2537079, by rfl⟩ : syracuseStep 6765545 = 5074159) B5074159
theorem B5004449 : Blo 1756579 5004449 := bstep (se 2 (by rfl) ⟨1876668, by rfl⟩ : syracuseStep 5004449 = 3753337) B3753337
theorem B2637119 : Blo 1756579 2637119 := bstep (se 1 (by rfl) ⟨1977839, by rfl⟩ : syracuseStep 2637119 = 3955679) B3955679
theorem B24051329 : Blo 1756579 24051329 := bstep (se 2 (by rfl) ⟨9019248, by rfl⟩ : syracuseStep 24051329 = 18038497) B18038497
theorem B6332185 : Blo 1756579 6332185 := bstep (se 2 (by rfl) ⟨2374569, by rfl⟩ : syracuseStep 6332185 = 4749139) B4749139
theorem B3335251 : Blo 1756579 3335251 := bstep (se 1 (by rfl) ⟨2501438, by rfl⟩ : syracuseStep 3335251 = 5002877) B5002877
theorem B164546477 : Blo 1756579 164546477 := bstep (se 3 (by rfl) ⟨30852464, by rfl⟩ : syracuseStep 164546477 = 61704929) B61704929
theorem B5933033 : Blo 1756579 5933033 := bstep (se 2 (by rfl) ⟨2224887, by rfl⟩ : syracuseStep 5933033 = 4449775) B4449775
theorem B5933087 : Blo 1756579 5933087 := bstep (se 1 (by rfl) ⟨4449815, by rfl⟩ : syracuseStep 5933087 = 8899631) B8899631
theorem B3336299 : Blo 1756579 3336299 := bstep (se 1 (by rfl) ⟨2502224, by rfl⟩ : syracuseStep 3336299 = 5004449) B5004449
theorem B162293989 : Blo 1756579 162293989 := bstep (se 4 (by rfl) ⟨15215061, by rfl⟩ : syracuseStep 162293989 = 30430123) B30430123
theorem B5630249 : Blo 1756579 5630249 := bstep (se 2 (by rfl) ⟨2111343, by rfl⟩ : syracuseStep 5630249 = 4222687) B4222687
theorem B16034219 : Blo 1756579 16034219 := bstep (se 1 (by rfl) ⟨12025664, by rfl⟩ : syracuseStep 16034219 = 24051329) B24051329
theorem B18041453 : Blo 1756579 18041453 := bstep (se 3 (by rfl) ⟨3382772, by rfl⟩ : syracuseStep 18041453 = 6765545) B6765545
theorem B5344157 : Blo 1756579 5344157 := bstep (se 3 (by rfl) ⟨1002029, by rfl⟩ : syracuseStep 5344157 = 2004059) B2004059
theorem B68479937 : Blo 1756579 68479937 := bstep (se 2 (by rfl) ⟨25679976, by rfl⟩ : syracuseStep 68479937 = 51359953) B51359953
theorem B1977439 : Blo 1756579 1977439 := bstep (se 1 (by rfl) ⟨1483079, by rfl⟩ : syracuseStep 1977439 = 2966159) B2966159
theorem B5074553 : Blo 1756579 5074553 := bstep (se 2 (by rfl) ⟨1902957, by rfl⟩ : syracuseStep 5074553 = 3805915) B3805915
theorem B1756959 : Blo 1756579 1756959 := bstep (se 1 (by rfl) ⟨1317719, by rfl⟩ : syracuseStep 1756959 = 2635439) B2635439
theorem B33771653 : Blo 1756579 33771653 := bstep (se 4 (by rfl) ⟨3166092, by rfl⟩ : syracuseStep 33771653 = 6332185) B6332185
theorem B15429851 : Blo 1756579 15429851 := bstep (se 1 (by rfl) ⟨11572388, by rfl⟩ : syracuseStep 15429851 = 23144777) B23144777
theorem B1758079 : Blo 1756579 1758079 := bstep (se 1 (by rfl) ⟨1318559, by rfl⟩ : syracuseStep 1758079 = 2637119) B2637119
theorem B2635241 : Blo 1756579 2635241 := bstep (se 2 (by rfl) ⟨988215, by rfl⟩ : syracuseStep 2635241 = 1976431) B1976431
theorem B2635319 : Blo 1756579 2635319 := bstep (se 1 (by rfl) ⟨1976489, by rfl⟩ : syracuseStep 2635319 = 3952979) B3952979
theorem B219297359 : Blo 1756579 219297359 := bstep (se 1 (by rfl) ⟨164473019, by rfl⟩ : syracuseStep 219297359 = 328946039) B328946039
theorem B151992125 : Blo 1756579 151992125 := bstep (se 3 (by rfl) ⟨28498523, by rfl⟩ : syracuseStep 151992125 = 56997047) B56997047
theorem B2635823 : Blo 1756579 2635823 := bstep (se 1 (by rfl) ⟨1976867, by rfl⟩ : syracuseStep 2635823 = 3953735) B3953735
theorem B4749367 : Blo 1756579 4749367 := bstep (se 1 (by rfl) ⟨3562025, by rfl⟩ : syracuseStep 4749367 = 7124051) B7124051
theorem B5929199 : Blo 1756579 5929199 := bstep (se 1 (by rfl) ⟨4446899, by rfl⟩ : syracuseStep 5929199 = 8893799) B8893799
theorem B2636135 : Blo 1756579 2636135 := bstep (se 1 (by rfl) ⟨1977101, by rfl⟩ : syracuseStep 2636135 = 3954203) B3954203
theorem B3381743 : Blo 1756579 3381743 := bstep (se 1 (by rfl) ⟨2536307, by rfl⟩ : syracuseStep 3381743 = 5072615) B5072615
theorem B2636519 : Blo 1756579 2636519 := bstep (se 1 (by rfl) ⟨1977389, by rfl⟩ : syracuseStep 2636519 = 3954779) B3954779
theorem B18037511 : Blo 1756579 18037511 := bstep (se 1 (by rfl) ⟨13528133, by rfl⟩ : syracuseStep 18037511 = 27056267) B27056267
theorem B5930171 : Blo 1756579 5930171 := bstep (se 1 (by rfl) ⟨4447628, by rfl⟩ : syracuseStep 5930171 = 8895257) B8895257
theorem B6332489 : Blo 1756579 6332489 := bstep (se 2 (by rfl) ⟨2374683, by rfl⟩ : syracuseStep 6332489 = 4749367) B4749367
theorem B216391985 : Blo 1756579 216391985 := bstep (se 2 (by rfl) ⟨81146994, by rfl⟩ : syracuseStep 216391985 = 162293989) B162293989
theorem B101328083 : Blo 1756579 101328083 := bstep (se 1 (by rfl) ⟨75996062, by rfl⟩ : syracuseStep 101328083 = 151992125) B151992125
theorem B2254495 : Blo 1756579 2254495 := bstep (se 1 (by rfl) ⟨1690871, by rfl⟩ : syracuseStep 2254495 = 3381743) B3381743
theorem B12027635 : Blo 1756579 12027635 := bstep (se 1 (by rfl) ⟨9020726, by rfl⟩ : syracuseStep 12027635 = 18041453) B18041453
theorem B22514435 : Blo 1756579 22514435 := bstep (se 1 (by rfl) ⟨16885826, by rfl⟩ : syracuseStep 22514435 = 33771653) B33771653
theorem B1756827 : Blo 1756579 1756827 := bstep (se 1 (by rfl) ⟨1317620, by rfl⟩ : syracuseStep 1756827 = 2635241) B2635241
theorem B1756879 : Blo 1756579 1756879 := bstep (se 1 (by rfl) ⟨1317659, by rfl⟩ : syracuseStep 1756879 = 2635319) B2635319
theorem B146198239 : Blo 1756579 146198239 := bstep (se 1 (by rfl) ⟨109648679, by rfl⟩ : syracuseStep 146198239 = 219297359) B219297359
theorem B1757215 : Blo 1756579 1757215 := bstep (se 1 (by rfl) ⟨1317911, by rfl⟩ : syracuseStep 1757215 = 2635823) B2635823
theorem B2224199 : Blo 1756579 2224199 := bstep (se 1 (by rfl) ⟨1668149, by rfl⟩ : syracuseStep 2224199 = 3336299) B3336299
theorem B3952799 : Blo 1756579 3952799 := bstep (se 1 (by rfl) ⟨2964599, by rfl⟩ : syracuseStep 3952799 = 5929199) B5929199
theorem B1757423 : Blo 1756579 1757423 := bstep (se 1 (by rfl) ⟨1318067, by rfl⟩ : syracuseStep 1757423 = 2636135) B2636135
theorem B1757679 : Blo 1756579 1757679 := bstep (se 1 (by rfl) ⟨1318259, by rfl⟩ : syracuseStep 1757679 = 2636519) B2636519
theorem B3953447 : Blo 1756579 3953447 := bstep (se 1 (by rfl) ⟨2965085, by rfl⟩ : syracuseStep 3953447 = 5930171) B5930171
theorem B14251085 : Blo 1756579 14251085 := bstep (se 3 (by rfl) ⟨2672078, by rfl⟩ : syracuseStep 14251085 = 5344157) B5344157
theorem B10286567 : Blo 1756579 10286567 := bstep (se 1 (by rfl) ⟨7714925, by rfl⟩ : syracuseStep 10286567 = 15429851) B15429851
theorem B15013997 : Blo 1756579 15013997 := bstep (se 3 (by rfl) ⟨2815124, by rfl⟩ : syracuseStep 15013997 = 5630249) B5630249
theorem B109697651 : Blo 1756579 109697651 := bstep (se 1 (by rfl) ⟨82273238, by rfl⟩ : syracuseStep 109697651 = 164546477) B164546477
theorem B3955355 : Blo 1756579 3955355 := bstep (se 1 (by rfl) ⟨2966516, by rfl⟩ : syracuseStep 3955355 = 5933033) B5933033
theorem B3955391 : Blo 1756579 3955391 := bstep (se 1 (by rfl) ⟨2966543, by rfl⟩ : syracuseStep 3955391 = 5933087) B5933087
theorem B4447001 : Blo 1756579 4447001 := bstep (se 2 (by rfl) ⟨1667625, by rfl⟩ : syracuseStep 4447001 = 3335251) B3335251
theorem B2636585 : Blo 1756579 2636585 := bstep (se 2 (by rfl) ⟨988719, by rfl⟩ : syracuseStep 2636585 = 1977439) B1977439
theorem B10689479 : Blo 1756579 10689479 := bstep (se 1 (by rfl) ⟨8017109, by rfl⟩ : syracuseStep 10689479 = 16034219) B16034219
theorem B12025007 : Blo 1756579 12025007 := bstep (se 1 (by rfl) ⟨9018755, by rfl⟩ : syracuseStep 12025007 = 18037511) B18037511
theorem B45653291 : Blo 1756579 45653291 := bstep (se 1 (by rfl) ⟨34239968, by rfl⟩ : syracuseStep 45653291 = 68479937) B68479937
theorem B3383035 : Blo 1756579 3383035 := bstep (se 1 (by rfl) ⟨2537276, by rfl⟩ : syracuseStep 3383035 = 5074553) B5074553
theorem B5931197 : Blo 1756579 5931197 := bstep (se 3 (by rfl) ⟨1112099, by rfl⟩ : syracuseStep 5931197 = 2224199) B2224199
theorem B144261323 : Blo 1756579 144261323 := bstep (se 1 (by rfl) ⟨108195992, by rfl⟩ : syracuseStep 144261323 = 216391985) B216391985
theorem B67552055 : Blo 1756579 67552055 := bstep (se 1 (by rfl) ⟨50664041, by rfl⟩ : syracuseStep 67552055 = 101328083) B101328083
theorem B6857711 : Blo 1756579 6857711 := bstep (se 1 (by rfl) ⟨5143283, by rfl⟩ : syracuseStep 6857711 = 10286567) B10286567
theorem B779723941 : Blo 1756579 779723941 := bstep (se 4 (by rfl) ⟨73099119, by rfl⟩ : syracuseStep 779723941 = 146198239) B146198239
theorem B73131767 : Blo 1756579 73131767 := bstep (se 1 (by rfl) ⟨54848825, by rfl⟩ : syracuseStep 73131767 = 109697651) B109697651
theorem B15009623 : Blo 1756579 15009623 := bstep (se 1 (by rfl) ⟨11257217, by rfl⟩ : syracuseStep 15009623 = 22514435) B22514435
theorem B30435527 : Blo 1756579 30435527 := bstep (se 1 (by rfl) ⟨22826645, by rfl⟩ : syracuseStep 30435527 = 45653291) B45653291
theorem B4221659 : Blo 1756579 4221659 := bstep (se 1 (by rfl) ⟨3166244, by rfl⟩ : syracuseStep 4221659 = 6332489) B6332489
theorem B18042853 : Blo 1756579 18042853 := bstep (se 4 (by rfl) ⟨1691517, by rfl⟩ : syracuseStep 18042853 = 3383035) B3383035
theorem B1757723 : Blo 1756579 1757723 := bstep (se 1 (by rfl) ⟨1318292, by rfl⟩ : syracuseStep 1757723 = 2636585) B2636585
theorem B8016671 : Blo 1756579 8016671 := bstep (se 1 (by rfl) ⟨6012503, by rfl⟩ : syracuseStep 8016671 = 12025007) B12025007
theorem B2635199 : Blo 1756579 2635199 := bstep (se 1 (by rfl) ⟨1976399, by rfl⟩ : syracuseStep 2635199 = 3952799) B3952799
theorem B2635631 : Blo 1756579 2635631 := bstep (se 1 (by rfl) ⟨1976723, by rfl⟩ : syracuseStep 2635631 = 3953447) B3953447
theorem B9500723 : Blo 1756579 9500723 := bstep (se 1 (by rfl) ⟨7125542, by rfl⟩ : syracuseStep 9500723 = 14251085) B14251085
theorem B8018423 : Blo 1756579 8018423 := bstep (se 1 (by rfl) ⟨6013817, by rfl⟩ : syracuseStep 8018423 = 12027635) B12027635
theorem B10009331 : Blo 1756579 10009331 := bstep (se 1 (by rfl) ⟨7506998, by rfl⟩ : syracuseStep 10009331 = 15013997) B15013997
theorem B2636903 : Blo 1756579 2636903 := bstep (se 1 (by rfl) ⟨1977677, by rfl⟩ : syracuseStep 2636903 = 3955355) B3955355
theorem B2636927 : Blo 1756579 2636927 := bstep (se 1 (by rfl) ⟨1977695, by rfl⟩ : syracuseStep 2636927 = 3955391) B3955391
theorem B2964667 : Blo 1756579 2964667 := bstep (se 1 (by rfl) ⟨2223500, by rfl⟩ : syracuseStep 2964667 = 4447001) B4447001
theorem B7126319 : Blo 1756579 7126319 := bstep (se 1 (by rfl) ⟨5344739, by rfl⟩ : syracuseStep 7126319 = 10689479) B10689479
theorem B3005993 : Blo 1756579 3005993 := bstep (se 2 (by rfl) ⟨1127247, by rfl⟩ : syracuseStep 3005993 = 2254495) B2254495
theorem B96174215 : Blo 1756579 96174215 := bstep (se 1 (by rfl) ⟨72130661, by rfl⟩ : syracuseStep 96174215 = 144261323) B144261323
theorem B4571807 : Blo 1756579 4571807 := bstep (se 1 (by rfl) ⟨3428855, by rfl⟩ : syracuseStep 4571807 = 6857711) B6857711
theorem B6333815 : Blo 1756579 6333815 := bstep (se 1 (by rfl) ⟨4750361, by rfl⟩ : syracuseStep 6333815 = 9500723) B9500723
theorem B1039631921 : Blo 1756579 1039631921 := bstep (se 2 (by rfl) ⟨389861970, by rfl⟩ : syracuseStep 1039631921 = 779723941) B779723941
theorem B45034703 : Blo 1756579 45034703 := bstep (se 1 (by rfl) ⟨33776027, by rfl⟩ : syracuseStep 45034703 = 67552055) B67552055
theorem B1756799 : Blo 1756579 1756799 := bstep (se 1 (by rfl) ⟨1317599, by rfl⟩ : syracuseStep 1756799 = 2635199) B2635199
theorem B48754511 : Blo 1756579 48754511 := bstep (se 1 (by rfl) ⟨36565883, by rfl⟩ : syracuseStep 48754511 = 73131767) B73131767
theorem B10006415 : Blo 1756579 10006415 := bstep (se 1 (by rfl) ⟨7504811, by rfl⟩ : syracuseStep 10006415 = 15009623) B15009623
theorem B1757087 : Blo 1756579 1757087 := bstep (se 1 (by rfl) ⟨1317815, by rfl⟩ : syracuseStep 1757087 = 2635631) B2635631
theorem B3952889 : Blo 1756579 3952889 := bstep (se 2 (by rfl) ⟨1482333, by rfl⟩ : syracuseStep 3952889 = 2964667) B2964667
theorem B5345615 : Blo 1756579 5345615 := bstep (se 1 (by rfl) ⟨4009211, by rfl⟩ : syracuseStep 5345615 = 8018423) B8018423
theorem B2814439 : Blo 1756579 2814439 := bstep (se 1 (by rfl) ⟨2110829, by rfl⟩ : syracuseStep 2814439 = 4221659) B4221659
theorem B6672887 : Blo 1756579 6672887 := bstep (se 1 (by rfl) ⟨5004665, by rfl⟩ : syracuseStep 6672887 = 10009331) B10009331
theorem B1757935 : Blo 1756579 1757935 := bstep (se 1 (by rfl) ⟨1318451, by rfl⟩ : syracuseStep 1757935 = 2636903) B2636903
theorem B21377789 : Blo 1756579 21377789 := bstep (se 3 (by rfl) ⟨4008335, by rfl⟩ : syracuseStep 21377789 = 8016671) B8016671
theorem B1757951 : Blo 1756579 1757951 := bstep (se 1 (by rfl) ⟨1318463, by rfl⟩ : syracuseStep 1757951 = 2636927) B2636927
theorem B2003995 : Blo 1756579 2003995 := bstep (se 1 (by rfl) ⟨1502996, by rfl⟩ : syracuseStep 2003995 = 3005993) B3005993
theorem B24057137 : Blo 1756579 24057137 := bstep (se 2 (by rfl) ⟨9021426, by rfl⟩ : syracuseStep 24057137 = 18042853) B18042853
theorem B3954131 : Blo 1756579 3954131 := bstep (se 1 (by rfl) ⟨2965598, by rfl⟩ : syracuseStep 3954131 = 5931197) B5931197
theorem B19003517 : Blo 1756579 19003517 := bstep (se 3 (by rfl) ⟨3563159, by rfl⟩ : syracuseStep 19003517 = 7126319) B7126319
theorem B20290351 : Blo 1756579 20290351 := bstep (se 1 (by rfl) ⟨15217763, by rfl⟩ : syracuseStep 20290351 = 30435527) B30435527
theorem B4448591 : Blo 1756579 4448591 := bstep (se 1 (by rfl) ⟨3336443, by rfl⟩ : syracuseStep 4448591 = 6672887) B6672887
theorem B3752585 : Blo 1756579 3752585 := bstep (se 2 (by rfl) ⟨1407219, by rfl⟩ : syracuseStep 3752585 = 2814439) B2814439
theorem B14254973 : Blo 1756579 14254973 := bstep (se 3 (by rfl) ⟨2672807, by rfl⟩ : syracuseStep 14254973 = 5345615) B5345615
theorem B2671993 : Blo 1756579 2671993 := bstep (se 2 (by rfl) ⟨1001997, by rfl⟩ : syracuseStep 2671993 = 2003995) B2003995
theorem B12191485 : Blo 1756579 12191485 := bstep (se 3 (by rfl) ⟨2285903, by rfl⟩ : syracuseStep 12191485 = 4571807) B4571807
theorem B6670943 : Blo 1756579 6670943 := bstep (se 1 (by rfl) ⟨5003207, by rfl⟩ : syracuseStep 6670943 = 10006415) B10006415
theorem B4222543 : Blo 1756579 4222543 := bstep (se 1 (by rfl) ⟨3166907, by rfl⟩ : syracuseStep 4222543 = 6333815) B6333815
theorem B693087947 : Blo 1756579 693087947 := bstep (se 1 (by rfl) ⟨519815960, by rfl⟩ : syracuseStep 693087947 = 1039631921) B1039631921
theorem B27053801 : Blo 1756579 27053801 := bstep (se 2 (by rfl) ⟨10145175, by rfl⟩ : syracuseStep 27053801 = 20290351) B20290351
theorem B12669011 : Blo 1756579 12669011 := bstep (se 1 (by rfl) ⟨9501758, by rfl⟩ : syracuseStep 12669011 = 19003517) B19003517
theorem B32503007 : Blo 1756579 32503007 := bstep (se 1 (by rfl) ⟨24377255, by rfl⟩ : syracuseStep 32503007 = 48754511) B48754511
theorem B64116143 : Blo 1756579 64116143 := bstep (se 1 (by rfl) ⟨48087107, by rfl⟩ : syracuseStep 64116143 = 96174215) B96174215
theorem B2635259 : Blo 1756579 2635259 := bstep (se 1 (by rfl) ⟨1976444, by rfl⟩ : syracuseStep 2635259 = 3952889) B3952889
theorem B14251859 : Blo 1756579 14251859 := bstep (se 1 (by rfl) ⟨10688894, by rfl⟩ : syracuseStep 14251859 = 21377789) B21377789
theorem B16038091 : Blo 1756579 16038091 := bstep (se 1 (by rfl) ⟨12028568, by rfl⟩ : syracuseStep 16038091 = 24057137) B24057137
theorem B2636087 : Blo 1756579 2636087 := bstep (se 1 (by rfl) ⟨1977065, by rfl⟩ : syracuseStep 2636087 = 3954131) B3954131
theorem B30023135 : Blo 1756579 30023135 := bstep (se 1 (by rfl) ⟨22517351, by rfl⟩ : syracuseStep 30023135 = 45034703) B45034703
theorem B8446007 : Blo 1756579 8446007 := bstep (se 1 (by rfl) ⟨6334505, by rfl⟩ : syracuseStep 8446007 = 12669011) B12669011
theorem B2965727 : Blo 1756579 2965727 := bstep (se 1 (by rfl) ⟨2224295, by rfl⟩ : syracuseStep 2965727 = 4448591) B4448591
theorem B9503315 : Blo 1756579 9503315 := bstep (se 1 (by rfl) ⟨7127486, by rfl⟩ : syracuseStep 9503315 = 14254973) B14254973
theorem B21668671 : Blo 1756579 21668671 := bstep (se 1 (by rfl) ⟨16251503, by rfl⟩ : syracuseStep 21668671 = 32503007) B32503007
theorem B5630057 : Blo 1756579 5630057 := bstep (se 2 (by rfl) ⟨2111271, by rfl⟩ : syracuseStep 5630057 = 4222543) B4222543
theorem B20015423 : Blo 1756579 20015423 := bstep (se 1 (by rfl) ⟨15011567, by rfl⟩ : syracuseStep 20015423 = 30023135) B30023135
theorem B16255313 : Blo 1756579 16255313 := bstep (se 2 (by rfl) ⟨6095742, by rfl⟩ : syracuseStep 16255313 = 12191485) B12191485
theorem B21384121 : Blo 1756579 21384121 := bstep (se 2 (by rfl) ⟨8019045, by rfl⟩ : syracuseStep 21384121 = 16038091) B16038091
theorem B2501723 : Blo 1756579 2501723 := bstep (se 1 (by rfl) ⟨1876292, by rfl⟩ : syracuseStep 2501723 = 3752585) B3752585
theorem B1756839 : Blo 1756579 1756839 := bstep (se 1 (by rfl) ⟨1317629, by rfl⟩ : syracuseStep 1756839 = 2635259) B2635259
theorem B1757391 : Blo 1756579 1757391 := bstep (se 1 (by rfl) ⟨1318043, by rfl⟩ : syracuseStep 1757391 = 2636087) B2636087
theorem B14250629 : Blo 1756579 14250629 := bstep (se 4 (by rfl) ⟨1335996, by rfl⟩ : syracuseStep 14250629 = 2671993) B2671993
theorem B462058631 : Blo 1756579 462058631 := bstep (se 1 (by rfl) ⟨346543973, by rfl⟩ : syracuseStep 462058631 = 693087947) B693087947
theorem B18035867 : Blo 1756579 18035867 := bstep (se 1 (by rfl) ⟨13526900, by rfl⟩ : syracuseStep 18035867 = 27053801) B27053801
theorem B42744095 : Blo 1756579 42744095 := bstep (se 1 (by rfl) ⟨32058071, by rfl⟩ : syracuseStep 42744095 = 64116143) B64116143
theorem B9501239 : Blo 1756579 9501239 := bstep (se 1 (by rfl) ⟨7125929, by rfl⟩ : syracuseStep 9501239 = 14251859) B14251859
theorem B4447295 : Blo 1756579 4447295 := bstep (se 1 (by rfl) ⟨3335471, by rfl⟩ : syracuseStep 4447295 = 6670943) B6670943
theorem B3753371 : Blo 1756579 3753371 := bstep (se 1 (by rfl) ⟨2815028, by rfl⟩ : syracuseStep 3753371 = 5630057) B5630057
theorem B5630671 : Blo 1756579 5630671 := bstep (se 1 (by rfl) ⟨4223003, by rfl⟩ : syracuseStep 5630671 = 8446007) B8446007
theorem B1977151 : Blo 1756579 1977151 := bstep (se 1 (by rfl) ⟨1482863, by rfl⟩ : syracuseStep 1977151 = 2965727) B2965727
theorem B6671261 : Blo 1756579 6671261 := bstep (se 3 (by rfl) ⟨1250861, by rfl⟩ : syracuseStep 6671261 = 2501723) B2501723
theorem B6335543 : Blo 1756579 6335543 := bstep (se 1 (by rfl) ⟨4751657, by rfl⟩ : syracuseStep 6335543 = 9503315) B9503315
theorem B308039087 : Blo 1756579 308039087 := bstep (se 1 (by rfl) ⟨231029315, by rfl⟩ : syracuseStep 308039087 = 462058631) B462058631
theorem B28512161 : Blo 1756579 28512161 := bstep (se 2 (by rfl) ⟨10692060, by rfl⟩ : syracuseStep 28512161 = 21384121) B21384121
theorem B28496063 : Blo 1756579 28496063 := bstep (se 1 (by rfl) ⟨21372047, by rfl⟩ : syracuseStep 28496063 = 42744095) B42744095
theorem B9500419 : Blo 1756579 9500419 := bstep (se 1 (by rfl) ⟨7125314, by rfl⟩ : syracuseStep 9500419 = 14250629) B14250629
theorem B12023911 : Blo 1756579 12023911 := bstep (se 1 (by rfl) ⟨9017933, by rfl⟩ : syracuseStep 12023911 = 18035867) B18035867
theorem B28891561 : Blo 1756579 28891561 := bstep (se 2 (by rfl) ⟨10834335, by rfl⟩ : syracuseStep 28891561 = 21668671) B21668671
theorem B25336637 : Blo 1756579 25336637 := bstep (se 3 (by rfl) ⟨4750619, by rfl⟩ : syracuseStep 25336637 = 9501239) B9501239
theorem B13343615 : Blo 1756579 13343615 := bstep (se 1 (by rfl) ⟨10007711, by rfl⟩ : syracuseStep 13343615 = 20015423) B20015423
theorem B10836875 : Blo 1756579 10836875 := bstep (se 1 (by rfl) ⟨8127656, by rfl⟩ : syracuseStep 10836875 = 16255313) B16255313
theorem B2964863 : Blo 1756579 2964863 := bstep (se 1 (by rfl) ⟨2223647, by rfl⟩ : syracuseStep 2964863 = 4447295) B4447295
theorem B16031881 : Blo 1756579 16031881 := bstep (se 2 (by rfl) ⟨6011955, by rfl⟩ : syracuseStep 16031881 = 12023911) B12023911
theorem B75989501 : Blo 1756579 75989501 := bstep (se 3 (by rfl) ⟨14248031, by rfl⟩ : syracuseStep 75989501 = 28496063) B28496063
theorem B1976575 : Blo 1756579 1976575 := bstep (se 1 (by rfl) ⟨1482431, by rfl⟩ : syracuseStep 1976575 = 2964863) B2964863
theorem B205359391 : Blo 1756579 205359391 := bstep (se 1 (by rfl) ⟨154019543, by rfl⟩ : syracuseStep 205359391 = 308039087) B308039087
theorem B12667225 : Blo 1756579 12667225 := bstep (se 2 (by rfl) ⟨4750209, by rfl⟩ : syracuseStep 12667225 = 9500419) B9500419
theorem B19008107 : Blo 1756579 19008107 := bstep (se 1 (by rfl) ⟨14256080, by rfl⟩ : syracuseStep 19008107 = 28512161) B28512161
theorem B16894781 : Blo 1756579 16894781 := bstep (se 3 (by rfl) ⟨3167771, by rfl⟩ : syracuseStep 16894781 = 6335543) B6335543
theorem B38522081 : Blo 1756579 38522081 := bstep (se 2 (by rfl) ⟨14445780, by rfl⟩ : syracuseStep 38522081 = 28891561) B28891561
theorem B2502247 : Blo 1756579 2502247 := bstep (se 1 (by rfl) ⟨1876685, by rfl⟩ : syracuseStep 2502247 = 3753371) B3753371
theorem B7507561 : Blo 1756579 7507561 := bstep (se 2 (by rfl) ⟨2815335, by rfl⟩ : syracuseStep 7507561 = 5630671) B5630671
theorem B2636201 : Blo 1756579 2636201 := bstep (se 2 (by rfl) ⟨988575, by rfl⟩ : syracuseStep 2636201 = 1977151) B1977151
theorem B16891091 : Blo 1756579 16891091 := bstep (se 1 (by rfl) ⟨12668318, by rfl⟩ : syracuseStep 16891091 = 25336637) B25336637
theorem B8895743 : Blo 1756579 8895743 := bstep (se 1 (by rfl) ⟨6671807, by rfl⟩ : syracuseStep 8895743 = 13343615) B13343615
theorem B7224583 : Blo 1756579 7224583 := bstep (se 1 (by rfl) ⟨5418437, by rfl⟩ : syracuseStep 7224583 = 10836875) B10836875
theorem B4447507 : Blo 1756579 4447507 := bstep (se 1 (by rfl) ⟨3335630, by rfl⟩ : syracuseStep 4447507 = 6671261) B6671261
theorem B50659667 : Blo 1756579 50659667 := bstep (se 1 (by rfl) ⟨37994750, by rfl⟩ : syracuseStep 50659667 = 75989501) B75989501
theorem B3336329 : Blo 1756579 3336329 := bstep (se 2 (by rfl) ⟨1251123, by rfl⟩ : syracuseStep 3336329 = 2502247) B2502247
theorem B21375841 : Blo 1756579 21375841 := bstep (se 2 (by rfl) ⟨8015940, by rfl⟩ : syracuseStep 21375841 = 16031881) B16031881
theorem B273812521 : Blo 1756579 273812521 := bstep (se 2 (by rfl) ⟨102679695, by rfl⟩ : syracuseStep 273812521 = 205359391) B205359391
theorem B1757467 : Blo 1756579 1757467 := bstep (se 1 (by rfl) ⟨1318100, by rfl⟩ : syracuseStep 1757467 = 2636201) B2636201
theorem B11260727 : Blo 1756579 11260727 := bstep (se 1 (by rfl) ⟨8445545, by rfl⟩ : syracuseStep 11260727 = 16891091) B16891091
theorem B2635433 : Blo 1756579 2635433 := bstep (se 2 (by rfl) ⟨988287, by rfl⟩ : syracuseStep 2635433 = 1976575) B1976575
theorem B16889633 : Blo 1756579 16889633 := bstep (se 2 (by rfl) ⟨6333612, by rfl⟩ : syracuseStep 16889633 = 12667225) B12667225
theorem B9632777 : Blo 1756579 9632777 := bstep (se 2 (by rfl) ⟨3612291, by rfl⟩ : syracuseStep 9632777 = 7224583) B7224583
theorem B5930009 : Blo 1756579 5930009 := bstep (se 2 (by rfl) ⟨2223753, by rfl⟩ : syracuseStep 5930009 = 4447507) B4447507
theorem B12672071 : Blo 1756579 12672071 := bstep (se 1 (by rfl) ⟨9504053, by rfl⟩ : syracuseStep 12672071 = 19008107) B19008107
theorem B11263187 : Blo 1756579 11263187 := bstep (se 1 (by rfl) ⟨8447390, by rfl⟩ : syracuseStep 11263187 = 16894781) B16894781
theorem B10010081 : Blo 1756579 10010081 := bstep (se 2 (by rfl) ⟨3753780, by rfl⟩ : syracuseStep 10010081 = 7507561) B7507561
theorem B25681387 : Blo 1756579 25681387 := bstep (se 1 (by rfl) ⟨19261040, by rfl⟩ : syracuseStep 25681387 = 38522081) B38522081
theorem B5930495 : Blo 1756579 5930495 := bstep (se 1 (by rfl) ⟨4447871, by rfl⟩ : syracuseStep 5930495 = 8895743) B8895743
theorem B8896877 : Blo 1756579 8896877 := bstep (se 3 (by rfl) ⟨1668164, by rfl⟩ : syracuseStep 8896877 = 3336329) B3336329
theorem B28501121 : Blo 1756579 28501121 := bstep (se 2 (by rfl) ⟨10687920, by rfl⟩ : syracuseStep 28501121 = 21375841) B21375841
theorem B8448047 : Blo 1756579 8448047 := bstep (se 1 (by rfl) ⟨6336035, by rfl⟩ : syracuseStep 8448047 = 12672071) B12672071
theorem B7507151 : Blo 1756579 7507151 := bstep (se 1 (by rfl) ⟨5630363, by rfl⟩ : syracuseStep 7507151 = 11260727) B11260727
theorem B1756955 : Blo 1756579 1756955 := bstep (se 1 (by rfl) ⟨1317716, by rfl⟩ : syracuseStep 1756955 = 2635433) B2635433
theorem B11259755 : Blo 1756579 11259755 := bstep (se 1 (by rfl) ⟨8444816, by rfl⟩ : syracuseStep 11259755 = 16889633) B16889633
theorem B3953339 : Blo 1756579 3953339 := bstep (se 1 (by rfl) ⟨2965004, by rfl⟩ : syracuseStep 3953339 = 5930009) B5930009
theorem B7508791 : Blo 1756579 7508791 := bstep (se 1 (by rfl) ⟨5631593, by rfl⟩ : syracuseStep 7508791 = 11263187) B11263187
theorem B6673387 : Blo 1756579 6673387 := bstep (se 1 (by rfl) ⟨5005040, by rfl⟩ : syracuseStep 6673387 = 10010081) B10010081
theorem B3953663 : Blo 1756579 3953663 := bstep (se 1 (by rfl) ⟨2965247, by rfl⟩ : syracuseStep 3953663 = 5930495) B5930495
theorem B25687405 : Blo 1756579 25687405 := bstep (se 3 (by rfl) ⟨4816388, by rfl⟩ : syracuseStep 25687405 = 9632777) B9632777
theorem B33773111 : Blo 1756579 33773111 := bstep (se 1 (by rfl) ⟨25329833, by rfl⟩ : syracuseStep 33773111 = 50659667) B50659667
theorem B365083361 : Blo 1756579 365083361 := bstep (se 2 (by rfl) ⟨136906260, by rfl⟩ : syracuseStep 365083361 = 273812521) B273812521
theorem B34241849 : Blo 1756579 34241849 := bstep (se 2 (by rfl) ⟨12840693, by rfl⟩ : syracuseStep 34241849 = 25681387) B25681387
theorem B5931251 : Blo 1756579 5931251 := bstep (se 1 (by rfl) ⟨4448438, by rfl⟩ : syracuseStep 5931251 = 8896877) B8896877
theorem B10011721 : Blo 1756579 10011721 := bstep (se 2 (by rfl) ⟨3754395, by rfl⟩ : syracuseStep 10011721 = 7508791) B7508791
theorem B8897849 : Blo 1756579 8897849 := bstep (se 2 (by rfl) ⟨3336693, by rfl⟩ : syracuseStep 8897849 = 6673387) B6673387
theorem B7506503 : Blo 1756579 7506503 := bstep (se 1 (by rfl) ⟨5629877, by rfl⟩ : syracuseStep 7506503 = 11259755) B11259755
theorem B19000747 : Blo 1756579 19000747 := bstep (se 1 (by rfl) ⟨14250560, by rfl⟩ : syracuseStep 19000747 = 28501121) B28501121
theorem B22515407 : Blo 1756579 22515407 := bstep (se 1 (by rfl) ⟨16886555, by rfl⟩ : syracuseStep 22515407 = 33773111) B33773111
theorem B5632031 : Blo 1756579 5632031 := bstep (se 1 (by rfl) ⟨4224023, by rfl⟩ : syracuseStep 5632031 = 8448047) B8448047
theorem B243388907 : Blo 1756579 243388907 := bstep (se 1 (by rfl) ⟨182541680, by rfl⟩ : syracuseStep 243388907 = 365083361) B365083361
theorem B22827899 : Blo 1756579 22827899 := bstep (se 1 (by rfl) ⟨17120924, by rfl⟩ : syracuseStep 22827899 = 34241849) B34241849
theorem B2635559 : Blo 1756579 2635559 := bstep (se 1 (by rfl) ⟨1976669, by rfl⟩ : syracuseStep 2635559 = 3953339) B3953339
theorem B2635775 : Blo 1756579 2635775 := bstep (se 1 (by rfl) ⟨1976831, by rfl⟩ : syracuseStep 2635775 = 3953663) B3953663
theorem B34249873 : Blo 1756579 34249873 := bstep (se 2 (by rfl) ⟨12843702, by rfl⟩ : syracuseStep 34249873 = 25687405) B25687405
theorem B5004767 : Blo 1756579 5004767 := bstep (se 1 (by rfl) ⟨3753575, by rfl⟩ : syracuseStep 5004767 = 7507151) B7507151
theorem B162259271 : Blo 1756579 162259271 := bstep (se 1 (by rfl) ⟨121694453, by rfl⟩ : syracuseStep 162259271 = 243388907) B243388907
theorem B5931899 : Blo 1756579 5931899 := bstep (se 1 (by rfl) ⟨4448924, by rfl⟩ : syracuseStep 5931899 = 8897849) B8897849
theorem B13346045 : Blo 1756579 13346045 := bstep (se 3 (by rfl) ⟨2502383, by rfl⟩ : syracuseStep 13346045 = 5004767) B5004767
theorem B15010271 : Blo 1756579 15010271 := bstep (se 1 (by rfl) ⟨11257703, by rfl⟩ : syracuseStep 15010271 = 22515407) B22515407
theorem B3754687 : Blo 1756579 3754687 := bstep (se 1 (by rfl) ⟨2816015, by rfl⟩ : syracuseStep 3754687 = 5632031) B5632031
theorem B1757039 : Blo 1756579 1757039 := bstep (se 1 (by rfl) ⟨1317779, by rfl⟩ : syracuseStep 1757039 = 2635559) B2635559
theorem B1757183 : Blo 1756579 1757183 := bstep (se 1 (by rfl) ⟨1317887, by rfl⟩ : syracuseStep 1757183 = 2635775) B2635775
theorem B13348961 : Blo 1756579 13348961 := bstep (se 2 (by rfl) ⟨5005860, by rfl⟩ : syracuseStep 13348961 = 10011721) B10011721
theorem B45666497 : Blo 1756579 45666497 := bstep (se 2 (by rfl) ⟨17124936, by rfl⟩ : syracuseStep 45666497 = 34249873) B34249873
theorem B25334329 : Blo 1756579 25334329 := bstep (se 2 (by rfl) ⟨9500373, by rfl⟩ : syracuseStep 25334329 = 19000747) B19000747
theorem B3954167 : Blo 1756579 3954167 := bstep (se 1 (by rfl) ⟨2965625, by rfl⟩ : syracuseStep 3954167 = 5931251) B5931251
theorem B15218599 : Blo 1756579 15218599 := bstep (se 1 (by rfl) ⟨11413949, by rfl⟩ : syracuseStep 15218599 = 22827899) B22827899
theorem B5004335 : Blo 1756579 5004335 := bstep (se 1 (by rfl) ⟨3753251, by rfl⟩ : syracuseStep 5004335 = 7506503) B7506503
theorem B8897363 : Blo 1756579 8897363 := bstep (se 1 (by rfl) ⟨6673022, by rfl⟩ : syracuseStep 8897363 = 13346045) B13346045
theorem B5006249 : Blo 1756579 5006249 := bstep (se 2 (by rfl) ⟨1877343, by rfl⟩ : syracuseStep 5006249 = 3754687) B3754687
theorem B3336223 : Blo 1756579 3336223 := bstep (se 1 (by rfl) ⟨2502167, by rfl⟩ : syracuseStep 3336223 = 5004335) B5004335
theorem B8899307 : Blo 1756579 8899307 := bstep (se 1 (by rfl) ⟨6674480, by rfl⟩ : syracuseStep 8899307 = 13348961) B13348961
theorem B30444331 : Blo 1756579 30444331 := bstep (se 1 (by rfl) ⟨22833248, by rfl⟩ : syracuseStep 30444331 = 45666497) B45666497
theorem B33779105 : Blo 1756579 33779105 := bstep (se 2 (by rfl) ⟨12667164, by rfl⟩ : syracuseStep 33779105 = 25334329) B25334329
theorem B10006847 : Blo 1756579 10006847 := bstep (se 1 (by rfl) ⟨7505135, by rfl⟩ : syracuseStep 10006847 = 15010271) B15010271
theorem B108172847 : Blo 1756579 108172847 := bstep (se 1 (by rfl) ⟨81129635, by rfl⟩ : syracuseStep 108172847 = 162259271) B162259271
theorem B3954599 : Blo 1756579 3954599 := bstep (se 1 (by rfl) ⟨2965949, by rfl⟩ : syracuseStep 3954599 = 5931899) B5931899
theorem B2636111 : Blo 1756579 2636111 := bstep (se 1 (by rfl) ⟨1977083, by rfl⟩ : syracuseStep 2636111 = 3954167) B3954167
theorem B20291465 : Blo 1756579 20291465 := bstep (se 2 (by rfl) ⟨7609299, by rfl⟩ : syracuseStep 20291465 = 15218599) B15218599
theorem B4448297 : Blo 1756579 4448297 := bstep (se 2 (by rfl) ⟨1668111, by rfl⟩ : syracuseStep 4448297 = 3336223) B3336223
theorem B5931575 : Blo 1756579 5931575 := bstep (se 1 (by rfl) ⟨4448681, by rfl⟩ : syracuseStep 5931575 = 8897363) B8897363
theorem B72115231 : Blo 1756579 72115231 := bstep (se 1 (by rfl) ⟨54086423, by rfl⟩ : syracuseStep 72115231 = 108172847) B108172847
theorem B40592441 : Blo 1756579 40592441 := bstep (se 2 (by rfl) ⟨15222165, by rfl⟩ : syracuseStep 40592441 = 30444331) B30444331
theorem B5932871 : Blo 1756579 5932871 := bstep (se 1 (by rfl) ⟨4449653, by rfl⟩ : syracuseStep 5932871 = 8899307) B8899307
theorem B13527643 : Blo 1756579 13527643 := bstep (se 1 (by rfl) ⟨10145732, by rfl⟩ : syracuseStep 13527643 = 20291465) B20291465
theorem B6671231 : Blo 1756579 6671231 := bstep (se 1 (by rfl) ⟨5003423, by rfl⟩ : syracuseStep 6671231 = 10006847) B10006847
theorem B3337499 : Blo 1756579 3337499 := bstep (se 1 (by rfl) ⟨2503124, by rfl⟩ : syracuseStep 3337499 = 5006249) B5006249
theorem B1757407 : Blo 1756579 1757407 := bstep (se 1 (by rfl) ⟨1318055, by rfl⟩ : syracuseStep 1757407 = 2636111) B2636111
theorem B2636399 : Blo 1756579 2636399 := bstep (se 1 (by rfl) ⟨1977299, by rfl⟩ : syracuseStep 2636399 = 3954599) B3954599
theorem B22519403 : Blo 1756579 22519403 := bstep (se 1 (by rfl) ⟨16889552, by rfl⟩ : syracuseStep 22519403 = 33779105) B33779105
theorem B2965531 : Blo 1756579 2965531 := bstep (se 1 (by rfl) ⟨2224148, by rfl⟩ : syracuseStep 2965531 = 4448297) B4448297
theorem B27061627 : Blo 1756579 27061627 := bstep (se 1 (by rfl) ⟨20296220, by rfl⟩ : syracuseStep 27061627 = 40592441) B40592441
theorem B96153641 : Blo 1756579 96153641 := bstep (se 2 (by rfl) ⟨36057615, by rfl⟩ : syracuseStep 96153641 = 72115231) B72115231
theorem B1757599 : Blo 1756579 1757599 := bstep (se 1 (by rfl) ⟨1318199, by rfl⟩ : syracuseStep 1757599 = 2636399) B2636399
theorem B2224999 : Blo 1756579 2224999 := bstep (se 1 (by rfl) ⟨1668749, by rfl⟩ : syracuseStep 2224999 = 3337499) B3337499
theorem B15012935 : Blo 1756579 15012935 := bstep (se 1 (by rfl) ⟨11259701, by rfl⟩ : syracuseStep 15012935 = 22519403) B22519403
theorem B3954383 : Blo 1756579 3954383 := bstep (se 1 (by rfl) ⟨2965787, by rfl⟩ : syracuseStep 3954383 = 5931575) B5931575
theorem B18036857 : Blo 1756579 18036857 := bstep (se 2 (by rfl) ⟨6763821, by rfl⟩ : syracuseStep 18036857 = 13527643) B13527643
theorem B3955247 : Blo 1756579 3955247 := bstep (se 1 (by rfl) ⟨2966435, by rfl⟩ : syracuseStep 3955247 = 5932871) B5932871
theorem B4447487 : Blo 1756579 4447487 := bstep (se 1 (by rfl) ⟨3335615, by rfl⟩ : syracuseStep 4447487 = 6671231) B6671231
theorem B64102427 : Blo 1756579 64102427 := bstep (se 1 (by rfl) ⟨48076820, by rfl⟩ : syracuseStep 64102427 = 96153641) B96153641
theorem B2966665 : Blo 1756579 2966665 := bstep (se 2 (by rfl) ⟨1112499, by rfl⟩ : syracuseStep 2966665 = 2224999) B2224999
theorem B36082169 : Blo 1756579 36082169 := bstep (se 2 (by rfl) ⟨13530813, by rfl⟩ : syracuseStep 36082169 = 27061627) B27061627
theorem B3954041 : Blo 1756579 3954041 := bstep (se 2 (by rfl) ⟨1482765, by rfl⟩ : syracuseStep 3954041 = 2965531) B2965531
theorem B10008623 : Blo 1756579 10008623 := bstep (se 1 (by rfl) ⟨7506467, by rfl⟩ : syracuseStep 10008623 = 15012935) B15012935
theorem B2636255 : Blo 1756579 2636255 := bstep (se 1 (by rfl) ⟨1977191, by rfl⟩ : syracuseStep 2636255 = 3954383) B3954383
theorem B12024571 : Blo 1756579 12024571 := bstep (se 1 (by rfl) ⟨9018428, by rfl⟩ : syracuseStep 12024571 = 18036857) B18036857
theorem B2636831 : Blo 1756579 2636831 := bstep (se 1 (by rfl) ⟨1977623, by rfl⟩ : syracuseStep 2636831 = 3955247) B3955247
theorem B2964991 : Blo 1756579 2964991 := bstep (se 1 (by rfl) ⟨2223743, by rfl⟩ : syracuseStep 2964991 = 4447487) B4447487
theorem B16032761 : Blo 1756579 16032761 := bstep (se 2 (by rfl) ⟨6012285, by rfl⟩ : syracuseStep 16032761 = 12024571) B12024571
theorem B24054779 : Blo 1756579 24054779 := bstep (se 1 (by rfl) ⟨18041084, by rfl⟩ : syracuseStep 24054779 = 36082169) B36082169
theorem B6672415 : Blo 1756579 6672415 := bstep (se 1 (by rfl) ⟨5004311, by rfl⟩ : syracuseStep 6672415 = 10008623) B10008623
theorem B1757503 : Blo 1756579 1757503 := bstep (se 1 (by rfl) ⟨1318127, by rfl⟩ : syracuseStep 1757503 = 2636255) B2636255
theorem B3953321 : Blo 1756579 3953321 := bstep (se 2 (by rfl) ⟨1482495, by rfl⟩ : syracuseStep 3953321 = 2964991) B2964991
theorem B1757887 : Blo 1756579 1757887 := bstep (se 1 (by rfl) ⟨1318415, by rfl⟩ : syracuseStep 1757887 = 2636831) B2636831
theorem B42734951 : Blo 1756579 42734951 := bstep (se 1 (by rfl) ⟨32051213, by rfl⟩ : syracuseStep 42734951 = 64102427) B64102427
theorem B2636027 : Blo 1756579 2636027 := bstep (se 1 (by rfl) ⟨1977020, by rfl⟩ : syracuseStep 2636027 = 3954041) B3954041
theorem B3955553 : Blo 1756579 3955553 := bstep (se 2 (by rfl) ⟨1483332, by rfl⟩ : syracuseStep 3955553 = 2966665) B2966665
theorem B8896553 : Blo 1756579 8896553 := bstep (se 2 (by rfl) ⟨3336207, by rfl⟩ : syracuseStep 8896553 = 6672415) B6672415
theorem B64146077 : Blo 1756579 64146077 := bstep (se 3 (by rfl) ⟨12027389, by rfl⟩ : syracuseStep 64146077 = 24054779) B24054779
theorem B1757351 : Blo 1756579 1757351 := bstep (se 1 (by rfl) ⟨1318013, by rfl⟩ : syracuseStep 1757351 = 2636027) B2636027
theorem B2635547 : Blo 1756579 2635547 := bstep (se 1 (by rfl) ⟨1976660, by rfl⟩ : syracuseStep 2635547 = 3953321) B3953321
theorem B10688507 : Blo 1756579 10688507 := bstep (se 1 (by rfl) ⟨8016380, by rfl⟩ : syracuseStep 10688507 = 16032761) B16032761
theorem B28489967 : Blo 1756579 28489967 := bstep (se 1 (by rfl) ⟨21367475, by rfl⟩ : syracuseStep 28489967 = 42734951) B42734951
theorem B2637035 : Blo 1756579 2637035 := bstep (se 1 (by rfl) ⟨1977776, by rfl⟩ : syracuseStep 2637035 = 3955553) B3955553
theorem B5931035 : Blo 1756579 5931035 := bstep (se 1 (by rfl) ⟨4448276, by rfl⟩ : syracuseStep 5931035 = 8896553) B8896553
theorem B42764051 : Blo 1756579 42764051 := bstep (se 1 (by rfl) ⟨32073038, by rfl⟩ : syracuseStep 42764051 = 64146077) B64146077
theorem B1757031 : Blo 1756579 1757031 := bstep (se 1 (by rfl) ⟨1317773, by rfl⟩ : syracuseStep 1757031 = 2635547) B2635547
theorem B18993311 : Blo 1756579 18993311 := bstep (se 1 (by rfl) ⟨14244983, by rfl⟩ : syracuseStep 18993311 = 28489967) B28489967
theorem B1758023 : Blo 1756579 1758023 := bstep (se 1 (by rfl) ⟨1318517, by rfl⟩ : syracuseStep 1758023 = 2637035) B2637035
theorem B7125671 : Blo 1756579 7125671 := bstep (se 1 (by rfl) ⟨5344253, by rfl⟩ : syracuseStep 7125671 = 10688507) B10688507
theorem B28509367 : Blo 1756579 28509367 := bstep (se 1 (by rfl) ⟨21382025, by rfl⟩ : syracuseStep 28509367 = 42764051) B42764051
theorem B3954023 : Blo 1756579 3954023 := bstep (se 1 (by rfl) ⟨2965517, by rfl⟩ : syracuseStep 3954023 = 5931035) B5931035
theorem B12662207 : Blo 1756579 12662207 := bstep (se 1 (by rfl) ⟨9496655, by rfl⟩ : syracuseStep 12662207 = 18993311) B18993311
theorem B4750447 : Blo 1756579 4750447 := bstep (se 1 (by rfl) ⟨3562835, by rfl⟩ : syracuseStep 4750447 = 7125671) B7125671
theorem B6333929 : Blo 1756579 6333929 := bstep (se 2 (by rfl) ⟨2375223, by rfl⟩ : syracuseStep 6333929 = 4750447) B4750447
theorem B38012489 : Blo 1756579 38012489 := bstep (se 2 (by rfl) ⟨14254683, by rfl⟩ : syracuseStep 38012489 = 28509367) B28509367
theorem B8441471 : Blo 1756579 8441471 := bstep (se 1 (by rfl) ⟨6331103, by rfl⟩ : syracuseStep 8441471 = 12662207) B12662207
theorem B2636015 : Blo 1756579 2636015 := bstep (se 1 (by rfl) ⟨1977011, by rfl⟩ : syracuseStep 2636015 = 3954023) B3954023
theorem B4222619 : Blo 1756579 4222619 := bstep (se 1 (by rfl) ⟨3166964, by rfl⟩ : syracuseStep 4222619 = 6333929) B6333929
theorem B25341659 : Blo 1756579 25341659 := bstep (se 1 (by rfl) ⟨19006244, by rfl⟩ : syracuseStep 25341659 = 38012489) B38012489
theorem B1757343 : Blo 1756579 1757343 := bstep (se 1 (by rfl) ⟨1318007, by rfl⟩ : syracuseStep 1757343 = 2636015) B2636015
theorem B5627647 : Blo 1756579 5627647 := bstep (se 1 (by rfl) ⟨4220735, by rfl⟩ : syracuseStep 5627647 = 8441471) B8441471
theorem B16894439 : Blo 1756579 16894439 := bstep (se 1 (by rfl) ⟨12670829, by rfl⟩ : syracuseStep 16894439 = 25341659) B25341659
theorem B2815079 : Blo 1756579 2815079 := bstep (se 1 (by rfl) ⟨2111309, by rfl⟩ : syracuseStep 2815079 = 4222619) B4222619
theorem B7503529 : Blo 1756579 7503529 := bstep (se 2 (by rfl) ⟨2813823, by rfl⟩ : syracuseStep 7503529 = 5627647) B5627647
theorem B10004705 : Blo 1756579 10004705 := bstep (se 2 (by rfl) ⟨3751764, by rfl⟩ : syracuseStep 10004705 = 7503529) B7503529
theorem B30027509 : Blo 1756579 30027509 := bstep (se 5 (by rfl) ⟨1407539, by rfl⟩ : syracuseStep 30027509 = 2815079) B2815079
theorem B11262959 : Blo 1756579 11262959 := bstep (se 1 (by rfl) ⟨8447219, by rfl⟩ : syracuseStep 11262959 = 16894439) B16894439
theorem B6669803 : Blo 1756579 6669803 := bstep (se 1 (by rfl) ⟨5002352, by rfl⟩ : syracuseStep 6669803 = 10004705) B10004705
theorem B7508639 : Blo 1756579 7508639 := bstep (se 1 (by rfl) ⟨5631479, by rfl⟩ : syracuseStep 7508639 = 11262959) B11262959
theorem B20018339 : Blo 1756579 20018339 := bstep (se 1 (by rfl) ⟨15013754, by rfl⟩ : syracuseStep 20018339 = 30027509) B30027509
theorem B5005759 : Blo 1756579 5005759 := bstep (se 1 (by rfl) ⟨3754319, by rfl⟩ : syracuseStep 5005759 = 7508639) B7508639
theorem B13345559 : Blo 1756579 13345559 := bstep (se 1 (by rfl) ⟨10009169, by rfl⟩ : syracuseStep 13345559 = 20018339) B20018339
theorem B4446535 : Blo 1756579 4446535 := bstep (se 1 (by rfl) ⟨3334901, by rfl⟩ : syracuseStep 4446535 = 6669803) B6669803
theorem B8897039 : Blo 1756579 8897039 := bstep (se 1 (by rfl) ⟨6672779, by rfl⟩ : syracuseStep 8897039 = 13345559) B13345559
theorem B5928713 : Blo 1756579 5928713 := bstep (se 2 (by rfl) ⟨2223267, by rfl⟩ : syracuseStep 5928713 = 4446535) B4446535
theorem B6674345 : Blo 1756579 6674345 := bstep (se 2 (by rfl) ⟨2502879, by rfl⟩ : syracuseStep 6674345 = 5005759) B5005759
theorem B5931359 : Blo 1756579 5931359 := bstep (se 1 (by rfl) ⟨4448519, by rfl⟩ : syracuseStep 5931359 = 8897039) B8897039
theorem B4449563 : Blo 1756579 4449563 := bstep (se 1 (by rfl) ⟨3337172, by rfl⟩ : syracuseStep 4449563 = 6674345) B6674345
theorem B3952475 : Blo 1756579 3952475 := bstep (se 1 (by rfl) ⟨2964356, by rfl⟩ : syracuseStep 3952475 = 5928713) B5928713
theorem B2966375 : Blo 1756579 2966375 := bstep (se 1 (by rfl) ⟨2224781, by rfl⟩ : syracuseStep 2966375 = 4449563) B4449563
theorem B2634983 : Blo 1756579 2634983 := bstep (se 1 (by rfl) ⟨1976237, by rfl⟩ : syracuseStep 2634983 = 3952475) B3952475
theorem B3954239 : Blo 1756579 3954239 := bstep (se 1 (by rfl) ⟨2965679, by rfl⟩ : syracuseStep 3954239 = 5931359) B5931359
theorem B1977583 : Blo 1756579 1977583 := bstep (se 1 (by rfl) ⟨1483187, by rfl⟩ : syracuseStep 1977583 = 2966375) B2966375
theorem B1756655 : Blo 1756579 1756655 := bstep (se 1 (by rfl) ⟨1317491, by rfl⟩ : syracuseStep 1756655 = 2634983) B2634983
theorem B2636159 : Blo 1756579 2636159 := bstep (se 1 (by rfl) ⟨1977119, by rfl⟩ : syracuseStep 2636159 = 3954239) B3954239
theorem B1757439 : Blo 1756579 1757439 := bstep (se 1 (by rfl) ⟨1318079, by rfl⟩ : syracuseStep 1757439 = 2636159) B2636159
theorem B2636777 : Blo 1756579 2636777 := bstep (se 2 (by rfl) ⟨988791, by rfl⟩ : syracuseStep 2636777 = 1977583) B1977583
theorem B1757851 : Blo 1756579 1757851 := bstep (se 1 (by rfl) ⟨1318388, by rfl⟩ : syracuseStep 1757851 = 2636777) B2636777

theorem C0 (j : ℕ) (h1 : 439144 ≤ j) (h2 : j ≤ 439519) : Blo 1756579 (4 * j + 3) := by
  interval_cases j
  · exact B1756579
  · exact B1756583
  · exact B1756587
  · exact B1756591
  · exact B1756595
  · exact B1756599
  · exact B1756603
  · exact B1756607
  · exact B1756611
  · exact B1756615
  · exact B1756619
  · exact B1756623
  · exact B1756627
  · exact B1756631
  · exact B1756635
  · exact B1756639
  · exact B1756643
  · exact B1756647
  · exact B1756651
  · exact B1756655
  · exact B1756659
  · exact B1756663
  · exact B1756667
  · exact B1756671
  · exact B1756675
  · exact B1756679
  · exact B1756683
  · exact B1756687
  · exact B1756691
  · exact B1756695
  · exact B1756699
  · exact B1756703
  · exact B1756707
  · exact B1756711
  · exact B1756715
  · exact B1756719
  · exact B1756723
  · exact B1756727
  · exact B1756731
  · exact B1756735
  · exact B1756739
  · exact B1756743
  · exact B1756747
  · exact B1756751
  · exact B1756755
  · exact B1756759
  · exact B1756763
  · exact B1756767
  · exact B1756771
  · exact B1756775
  · exact B1756779
  · exact B1756783
  · exact B1756787
  · exact B1756791
  · exact B1756795
  · exact B1756799
  · exact B1756803
  · exact B1756807
  · exact B1756811
  · exact B1756815
  · exact B1756819
  · exact B1756823
  · exact B1756827
  · exact B1756831
  · exact B1756835
  · exact B1756839
  · exact B1756843
  · exact B1756847
  · exact B1756851
  · exact B1756855
  · exact B1756859
  · exact B1756863
  · exact B1756867
  · exact B1756871
  · exact B1756875
  · exact B1756879
  · exact B1756883
  · exact B1756887
  · exact B1756891
  · exact B1756895
  · exact B1756899
  · exact B1756903
  · exact B1756907
  · exact B1756911
  · exact B1756915
  · exact B1756919
  · exact B1756923
  · exact B1756927
  · exact B1756931
  · exact B1756935
  · exact B1756939
  · exact B1756943
  · exact B1756947
  · exact B1756951
  · exact B1756955
  · exact B1756959
  · exact B1756963
  · exact B1756967
  · exact B1756971
  · exact B1756975
  · exact B1756979
  · exact B1756983
  · exact B1756987
  · exact B1756991
  · exact B1756995
  · exact B1756999
  · exact B1757003
  · exact B1757007
  · exact B1757011
  · exact B1757015
  · exact B1757019
  · exact B1757023
  · exact B1757027
  · exact B1757031
  · exact B1757035
  · exact B1757039
  · exact B1757043
  · exact B1757047
  · exact B1757051
  · exact B1757055
  · exact B1757059
  · exact B1757063
  · exact B1757067
  · exact B1757071
  · exact B1757075
  · exact B1757079
  · exact B1757083
  · exact B1757087
  · exact B1757091
  · exact B1757095
  · exact B1757099
  · exact B1757103
  · exact B1757107
  · exact B1757111
  · exact B1757115
  · exact B1757119
  · exact B1757123
  · exact B1757127
  · exact B1757131
  · exact B1757135
  · exact B1757139
  · exact B1757143
  · exact B1757147
  · exact B1757151
  · exact B1757155
  · exact B1757159
  · exact B1757163
  · exact B1757167
  · exact B1757171
  · exact B1757175
  · exact B1757179
  · exact B1757183
  · exact B1757187
  · exact B1757191
  · exact B1757195
  · exact B1757199
  · exact B1757203
  · exact B1757207
  · exact B1757211
  · exact B1757215
  · exact B1757219
  · exact B1757223
  · exact B1757227
  · exact B1757231
  · exact B1757235
  · exact B1757239
  · exact B1757243
  · exact B1757247
  · exact B1757251
  · exact B1757255
  · exact B1757259
  · exact B1757263
  · exact B1757267
  · exact B1757271
  · exact B1757275
  · exact B1757279
  · exact B1757283
  · exact B1757287
  · exact B1757291
  · exact B1757295
  · exact B1757299
  · exact B1757303
  · exact B1757307
  · exact B1757311
  · exact B1757315
  · exact B1757319
  · exact B1757323
  · exact B1757327
  · exact B1757331
  · exact B1757335
  · exact B1757339
  · exact B1757343
  · exact B1757347
  · exact B1757351
  · exact B1757355
  · exact B1757359
  · exact B1757363
  · exact B1757367
  · exact B1757371
  · exact B1757375
  · exact B1757379
  · exact B1757383
  · exact B1757387
  · exact B1757391
  · exact B1757395
  · exact B1757399
  · exact B1757403
  · exact B1757407
  · exact B1757411
  · exact B1757415
  · exact B1757419
  · exact B1757423
  · exact B1757427
  · exact B1757431
  · exact B1757435
  · exact B1757439
  · exact B1757443
  · exact B1757447
  · exact B1757451
  · exact B1757455
  · exact B1757459
  · exact B1757463
  · exact B1757467
  · exact B1757471
  · exact B1757475
  · exact B1757479
  · exact B1757483
  · exact B1757487
  · exact B1757491
  · exact B1757495
  · exact B1757499
  · exact B1757503
  · exact B1757507
  · exact B1757511
  · exact B1757515
  · exact B1757519
  · exact B1757523
  · exact B1757527
  · exact B1757531
  · exact B1757535
  · exact B1757539
  · exact B1757543
  · exact B1757547
  · exact B1757551
  · exact B1757555
  · exact B1757559
  · exact B1757563
  · exact B1757567
  · exact B1757571
  · exact B1757575
  · exact B1757579
  · exact B1757583
  · exact B1757587
  · exact B1757591
  · exact B1757595
  · exact B1757599
  · exact B1757603
  · exact B1757607
  · exact B1757611
  · exact B1757615
  · exact B1757619
  · exact B1757623
  · exact B1757627
  · exact B1757631
  · exact B1757635
  · exact B1757639
  · exact B1757643
  · exact B1757647
  · exact B1757651
  · exact B1757655
  · exact B1757659
  · exact B1757663
  · exact B1757667
  · exact B1757671
  · exact B1757675
  · exact B1757679
  · exact B1757683
  · exact B1757687
  · exact B1757691
  · exact B1757695
  · exact B1757699
  · exact B1757703
  · exact B1757707
  · exact B1757711
  · exact B1757715
  · exact B1757719
  · exact B1757723
  · exact B1757727
  · exact B1757731
  · exact B1757735
  · exact B1757739
  · exact B1757743
  · exact B1757747
  · exact B1757751
  · exact B1757755
  · exact B1757759
  · exact B1757763
  · exact B1757767
  · exact B1757771
  · exact B1757775
  · exact B1757779
  · exact B1757783
  · exact B1757787
  · exact B1757791
  · exact B1757795
  · exact B1757799
  · exact B1757803
  · exact B1757807
  · exact B1757811
  · exact B1757815
  · exact B1757819
  · exact B1757823
  · exact B1757827
  · exact B1757831
  · exact B1757835
  · exact B1757839
  · exact B1757843
  · exact B1757847
  · exact B1757851
  · exact B1757855
  · exact B1757859
  · exact B1757863
  · exact B1757867
  · exact B1757871
  · exact B1757875
  · exact B1757879
  · exact B1757883
  · exact B1757887
  · exact B1757891
  · exact B1757895
  · exact B1757899
  · exact B1757903
  · exact B1757907
  · exact B1757911
  · exact B1757915
  · exact B1757919
  · exact B1757923
  · exact B1757927
  · exact B1757931
  · exact B1757935
  · exact B1757939
  · exact B1757943
  · exact B1757947
  · exact B1757951
  · exact B1757955
  · exact B1757959
  · exact B1757963
  · exact B1757967
  · exact B1757971
  · exact B1757975
  · exact B1757979
  · exact B1757983
  · exact B1757987
  · exact B1757991
  · exact B1757995
  · exact B1757999
  · exact B1758003
  · exact B1758007
  · exact B1758011
  · exact B1758015
  · exact B1758019
  · exact B1758023
  · exact B1758027
  · exact B1758031
  · exact B1758035
  · exact B1758039
  · exact B1758043
  · exact B1758047
  · exact B1758051
  · exact B1758055
  · exact B1758059
  · exact B1758063
  · exact B1758067
  · exact B1758071
  · exact B1758075
  · exact B1758079

theorem solution (m : ℕ) (hlo : 1756579 ≤ m) (hhi : m ≤ 1758079) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 439144 ≤ j := by omega
    have hj2 : j ≤ 439519 := by omega
    have hb : Blo 1756579 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
