-- Prove2me | solution 1 for syracuse_descends_range_2011435_2013435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:43.271263+00:00
-- url     : https://prove2.me/submissions/059dcbc1-a864-41f9-952e-16294f547686

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

theorem B2262865 : Blo 2011435 2262865 := bbase (se 2 (by rfl) ⟨848574, by rfl⟩ : syracuseStep 2262865 = 1697149) (by norm_num)
theorem B3017153 : Blo 2011435 3017153 := bstep (se 2 (by rfl) ⟨1131432, by rfl⟩ : syracuseStep 3017153 = 2262865) B2262865
theorem B2011435 : Blo 2011435 2011435 := bstep (se 1 (by rfl) ⟨1508576, by rfl⟩ : syracuseStep 2011435 = 3017153) B3017153
theorem B4832909 : Blo 2011435 4832909 := bbase (se 3 (by rfl) ⟨906170, by rfl⟩ : syracuseStep 4832909 = 1812341) (by norm_num)
theorem B3221939 : Blo 2011435 3221939 := bstep (se 1 (by rfl) ⟨2416454, by rfl⟩ : syracuseStep 3221939 = 4832909) B4832909
theorem B2147959 : Blo 2011435 2147959 := bstep (se 1 (by rfl) ⟨1610969, by rfl⟩ : syracuseStep 2147959 = 3221939) B3221939
theorem B2863945 : Blo 2011435 2863945 := bstep (se 2 (by rfl) ⟨1073979, by rfl⟩ : syracuseStep 2863945 = 2147959) B2147959
theorem B3818593 : Blo 2011435 3818593 := bstep (se 2 (by rfl) ⟨1431972, by rfl⟩ : syracuseStep 3818593 = 2863945) B2863945
theorem B5091457 : Blo 2011435 5091457 := bstep (se 2 (by rfl) ⟨1909296, by rfl⟩ : syracuseStep 5091457 = 3818593) B3818593
theorem B6788609 : Blo 2011435 6788609 := bstep (se 2 (by rfl) ⟨2545728, by rfl⟩ : syracuseStep 6788609 = 5091457) B5091457
theorem B4525739 : Blo 2011435 4525739 := bstep (se 1 (by rfl) ⟨3394304, by rfl⟩ : syracuseStep 4525739 = 6788609) B6788609
theorem B3017159 : Blo 2011435 3017159 := bstep (se 1 (by rfl) ⟨2262869, by rfl⟩ : syracuseStep 3017159 = 4525739) B4525739
theorem B2011439 : Blo 2011435 2011439 := bstep (se 1 (by rfl) ⟨1508579, by rfl⟩ : syracuseStep 2011439 = 3017159) B3017159
theorem B3017165 : Blo 2011435 3017165 := bbase (se 3 (by rfl) ⟨565718, by rfl⟩ : syracuseStep 3017165 = 1131437) (by norm_num)
theorem B2011443 : Blo 2011435 2011443 := bstep (se 1 (by rfl) ⟨1508582, by rfl⟩ : syracuseStep 2011443 = 3017165) B3017165
theorem B4525757 : Blo 2011435 4525757 := bbase (se 3 (by rfl) ⟨848579, by rfl⟩ : syracuseStep 4525757 = 1697159) (by norm_num)
theorem B3017171 : Blo 2011435 3017171 := bstep (se 1 (by rfl) ⟨2262878, by rfl⟩ : syracuseStep 3017171 = 4525757) B4525757
theorem B2011447 : Blo 2011435 2011447 := bstep (se 1 (by rfl) ⟨1508585, by rfl⟩ : syracuseStep 2011447 = 3017171) B3017171
theorem B3394325 : Blo 2011435 3394325 := bbase (se 6 (by rfl) ⟨79554, by rfl⟩ : syracuseStep 3394325 = 159109) (by norm_num)
theorem B2262883 : Blo 2011435 2262883 := bstep (se 1 (by rfl) ⟨1697162, by rfl⟩ : syracuseStep 2262883 = 3394325) B3394325
theorem B3017177 : Blo 2011435 3017177 := bstep (se 2 (by rfl) ⟨1131441, by rfl⟩ : syracuseStep 3017177 = 2262883) B2262883
theorem B2011451 : Blo 2011435 2011451 := bstep (se 1 (by rfl) ⟨1508588, by rfl⟩ : syracuseStep 2011451 = 3017177) B3017177
theorem B6881285 : Blo 2011435 6881285 := bbase (se 4 (by rfl) ⟨645120, by rfl⟩ : syracuseStep 6881285 = 1290241) (by norm_num)
theorem B4587523 : Blo 2011435 4587523 := bstep (se 1 (by rfl) ⟨3440642, by rfl⟩ : syracuseStep 4587523 = 6881285) B6881285
theorem B24466789 : Blo 2011435 24466789 := bstep (se 4 (by rfl) ⟨2293761, by rfl⟩ : syracuseStep 24466789 = 4587523) B4587523
theorem B32622385 : Blo 2011435 32622385 := bstep (se 2 (by rfl) ⟨12233394, by rfl⟩ : syracuseStep 32622385 = 24466789) B24466789
theorem B43496513 : Blo 2011435 43496513 := bstep (se 2 (by rfl) ⟨16311192, by rfl⟩ : syracuseStep 43496513 = 32622385) B32622385
theorem B28997675 : Blo 2011435 28997675 := bstep (se 1 (by rfl) ⟨21748256, by rfl⟩ : syracuseStep 28997675 = 43496513) B43496513
theorem B19331783 : Blo 2011435 19331783 := bstep (se 1 (by rfl) ⟨14498837, by rfl⟩ : syracuseStep 19331783 = 28997675) B28997675
theorem B12887855 : Blo 2011435 12887855 := bstep (se 1 (by rfl) ⟨9665891, by rfl⟩ : syracuseStep 12887855 = 19331783) B19331783
theorem B8591903 : Blo 2011435 8591903 := bstep (se 1 (by rfl) ⟨6443927, by rfl⟩ : syracuseStep 8591903 = 12887855) B12887855
theorem B5727935 : Blo 2011435 5727935 := bstep (se 1 (by rfl) ⟨4295951, by rfl⟩ : syracuseStep 5727935 = 8591903) B8591903
theorem B15274493 : Blo 2011435 15274493 := bstep (se 3 (by rfl) ⟨2863967, by rfl⟩ : syracuseStep 15274493 = 5727935) B5727935
theorem B10182995 : Blo 2011435 10182995 := bstep (se 1 (by rfl) ⟨7637246, by rfl⟩ : syracuseStep 10182995 = 15274493) B15274493
theorem B6788663 : Blo 2011435 6788663 := bstep (se 1 (by rfl) ⟨5091497, by rfl⟩ : syracuseStep 6788663 = 10182995) B10182995
theorem B4525775 : Blo 2011435 4525775 := bstep (se 1 (by rfl) ⟨3394331, by rfl⟩ : syracuseStep 4525775 = 6788663) B6788663
theorem B3017183 : Blo 2011435 3017183 := bstep (se 1 (by rfl) ⟨2262887, by rfl⟩ : syracuseStep 3017183 = 4525775) B4525775
theorem B2011455 : Blo 2011435 2011455 := bstep (se 1 (by rfl) ⟨1508591, by rfl⟩ : syracuseStep 2011455 = 3017183) B3017183
theorem B3017189 : Blo 2011435 3017189 := bbase (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) (by norm_num)
theorem B2011459 : Blo 2011435 2011459 := bstep (se 1 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 2011459 = 3017189) B3017189
theorem B3624725 : Blo 2011435 3624725 := bbase (se 6 (by rfl) ⟨84954, by rfl⟩ : syracuseStep 3624725 = 169909) (by norm_num)
theorem B2416483 : Blo 2011435 2416483 := bstep (se 1 (by rfl) ⟨1812362, by rfl⟩ : syracuseStep 2416483 = 3624725) B3624725
theorem B12887909 : Blo 2011435 12887909 := bstep (se 4 (by rfl) ⟨1208241, by rfl⟩ : syracuseStep 12887909 = 2416483) B2416483
theorem B8591939 : Blo 2011435 8591939 := bstep (se 1 (by rfl) ⟨6443954, by rfl⟩ : syracuseStep 8591939 = 12887909) B12887909
theorem B5727959 : Blo 2011435 5727959 := bstep (se 1 (by rfl) ⟨4295969, by rfl⟩ : syracuseStep 5727959 = 8591939) B8591939
theorem B3818639 : Blo 2011435 3818639 := bstep (se 1 (by rfl) ⟨2863979, by rfl⟩ : syracuseStep 3818639 = 5727959) B5727959
theorem B2545759 : Blo 2011435 2545759 := bstep (se 1 (by rfl) ⟨1909319, by rfl⟩ : syracuseStep 2545759 = 3818639) B3818639
theorem B3394345 : Blo 2011435 3394345 := bstep (se 2 (by rfl) ⟨1272879, by rfl⟩ : syracuseStep 3394345 = 2545759) B2545759
theorem B4525793 : Blo 2011435 4525793 := bstep (se 2 (by rfl) ⟨1697172, by rfl⟩ : syracuseStep 4525793 = 3394345) B3394345
theorem B3017195 : Blo 2011435 3017195 := bstep (se 1 (by rfl) ⟨2262896, by rfl⟩ : syracuseStep 3017195 = 4525793) B4525793
theorem B2011463 : Blo 2011435 2011463 := bstep (se 1 (by rfl) ⟨1508597, by rfl⟩ : syracuseStep 2011463 = 3017195) B3017195
theorem B2262901 : Blo 2011435 2262901 := bbase (se 5 (by rfl) ⟨106073, by rfl⟩ : syracuseStep 2262901 = 212147) (by norm_num)
theorem B3017201 : Blo 2011435 3017201 := bstep (se 2 (by rfl) ⟨1131450, by rfl⟩ : syracuseStep 3017201 = 2262901) B2262901
theorem B2011467 : Blo 2011435 2011467 := bstep (se 1 (by rfl) ⟨1508600, by rfl⟩ : syracuseStep 2011467 = 3017201) B3017201
theorem B2545769 : Blo 2011435 2545769 := bbase (se 2 (by rfl) ⟨954663, by rfl⟩ : syracuseStep 2545769 = 1909327) (by norm_num)
theorem B6788717 : Blo 2011435 6788717 := bstep (se 3 (by rfl) ⟨1272884, by rfl⟩ : syracuseStep 6788717 = 2545769) B2545769
theorem B4525811 : Blo 2011435 4525811 := bstep (se 1 (by rfl) ⟨3394358, by rfl⟩ : syracuseStep 4525811 = 6788717) B6788717
theorem B3017207 : Blo 2011435 3017207 := bstep (se 1 (by rfl) ⟨2262905, by rfl⟩ : syracuseStep 3017207 = 4525811) B4525811
theorem B2011471 : Blo 2011435 2011471 := bstep (se 1 (by rfl) ⟨1508603, by rfl⟩ : syracuseStep 2011471 = 3017207) B3017207
theorem B3017213 : Blo 2011435 3017213 := bbase (se 3 (by rfl) ⟨565727, by rfl⟩ : syracuseStep 3017213 = 1131455) (by norm_num)
theorem B2011475 : Blo 2011435 2011475 := bstep (se 1 (by rfl) ⟨1508606, by rfl⟩ : syracuseStep 2011475 = 3017213) B3017213
theorem B4525829 : Blo 2011435 4525829 := bbase (se 4 (by rfl) ⟨424296, by rfl⟩ : syracuseStep 4525829 = 848593) (by norm_num)
theorem B3017219 : Blo 2011435 3017219 := bstep (se 1 (by rfl) ⟨2262914, by rfl⟩ : syracuseStep 3017219 = 4525829) B4525829
theorem B2011479 : Blo 2011435 2011479 := bstep (se 1 (by rfl) ⟨1508609, by rfl⟩ : syracuseStep 2011479 = 3017219) B3017219
theorem B3818677 : Blo 2011435 3818677 := bbase (se 5 (by rfl) ⟨179000, by rfl⟩ : syracuseStep 3818677 = 358001) (by norm_num)
theorem B5091569 : Blo 2011435 5091569 := bstep (se 2 (by rfl) ⟨1909338, by rfl⟩ : syracuseStep 5091569 = 3818677) B3818677
theorem B3394379 : Blo 2011435 3394379 := bstep (se 1 (by rfl) ⟨2545784, by rfl⟩ : syracuseStep 3394379 = 5091569) B5091569
theorem B2262919 : Blo 2011435 2262919 := bstep (se 1 (by rfl) ⟨1697189, by rfl⟩ : syracuseStep 2262919 = 3394379) B3394379
theorem B3017225 : Blo 2011435 3017225 := bstep (se 2 (by rfl) ⟨1131459, by rfl⟩ : syracuseStep 3017225 = 2262919) B2262919
theorem B2011483 : Blo 2011435 2011483 := bstep (se 1 (by rfl) ⟨1508612, by rfl⟩ : syracuseStep 2011483 = 3017225) B3017225
theorem B10183157 : Blo 2011435 10183157 := bbase (se 5 (by rfl) ⟨477335, by rfl⟩ : syracuseStep 10183157 = 954671) (by norm_num)
theorem B6788771 : Blo 2011435 6788771 := bstep (se 1 (by rfl) ⟨5091578, by rfl⟩ : syracuseStep 6788771 = 10183157) B10183157
theorem B4525847 : Blo 2011435 4525847 := bstep (se 1 (by rfl) ⟨3394385, by rfl⟩ : syracuseStep 4525847 = 6788771) B6788771
theorem B3017231 : Blo 2011435 3017231 := bstep (se 1 (by rfl) ⟨2262923, by rfl⟩ : syracuseStep 3017231 = 4525847) B4525847
theorem B2011487 : Blo 2011435 2011487 := bstep (se 1 (by rfl) ⟨1508615, by rfl⟩ : syracuseStep 2011487 = 3017231) B3017231
theorem B3017237 : Blo 2011435 3017237 := bbase (se 6 (by rfl) ⟨70716, by rfl⟩ : syracuseStep 3017237 = 141433) (by norm_num)
theorem B2011491 : Blo 2011435 2011491 := bstep (se 1 (by rfl) ⟨1508618, by rfl⟩ : syracuseStep 2011491 = 3017237) B3017237
theorem B17184149 : Blo 2011435 17184149 := bbase (se 6 (by rfl) ⟨402753, by rfl⟩ : syracuseStep 17184149 = 805507) (by norm_num)
theorem B11456099 : Blo 2011435 11456099 := bstep (se 1 (by rfl) ⟨8592074, by rfl⟩ : syracuseStep 11456099 = 17184149) B17184149
theorem B7637399 : Blo 2011435 7637399 := bstep (se 1 (by rfl) ⟨5728049, by rfl⟩ : syracuseStep 7637399 = 11456099) B11456099
theorem B5091599 : Blo 2011435 5091599 := bstep (se 1 (by rfl) ⟨3818699, by rfl⟩ : syracuseStep 5091599 = 7637399) B7637399
theorem B3394399 : Blo 2011435 3394399 := bstep (se 1 (by rfl) ⟨2545799, by rfl⟩ : syracuseStep 3394399 = 5091599) B5091599
theorem B4525865 : Blo 2011435 4525865 := bstep (se 2 (by rfl) ⟨1697199, by rfl⟩ : syracuseStep 4525865 = 3394399) B3394399
theorem B3017243 : Blo 2011435 3017243 := bstep (se 1 (by rfl) ⟨2262932, by rfl⟩ : syracuseStep 3017243 = 4525865) B4525865
theorem B2011495 : Blo 2011435 2011495 := bstep (se 1 (by rfl) ⟨1508621, by rfl⟩ : syracuseStep 2011495 = 3017243) B3017243
theorem B2262937 : Blo 2011435 2262937 := bbase (se 2 (by rfl) ⟨848601, by rfl⟩ : syracuseStep 2262937 = 1697203) (by norm_num)
theorem B3017249 : Blo 2011435 3017249 := bstep (se 2 (by rfl) ⟨1131468, by rfl⟩ : syracuseStep 3017249 = 2262937) B2262937
theorem B2011499 : Blo 2011435 2011499 := bstep (se 1 (by rfl) ⟨1508624, by rfl⟩ : syracuseStep 2011499 = 3017249) B3017249
theorem B7637429 : Blo 2011435 7637429 := bbase (se 5 (by rfl) ⟨358004, by rfl⟩ : syracuseStep 7637429 = 716009) (by norm_num)
theorem B5091619 : Blo 2011435 5091619 := bstep (se 1 (by rfl) ⟨3818714, by rfl⟩ : syracuseStep 5091619 = 7637429) B7637429
theorem B6788825 : Blo 2011435 6788825 := bstep (se 2 (by rfl) ⟨2545809, by rfl⟩ : syracuseStep 6788825 = 5091619) B5091619
theorem B4525883 : Blo 2011435 4525883 := bstep (se 1 (by rfl) ⟨3394412, by rfl⟩ : syracuseStep 4525883 = 6788825) B6788825
theorem B3017255 : Blo 2011435 3017255 := bstep (se 1 (by rfl) ⟨2262941, by rfl⟩ : syracuseStep 3017255 = 4525883) B4525883
theorem B2011503 : Blo 2011435 2011503 := bstep (se 1 (by rfl) ⟨1508627, by rfl⟩ : syracuseStep 2011503 = 3017255) B3017255
theorem B3017261 : Blo 2011435 3017261 := bbase (se 3 (by rfl) ⟨565736, by rfl⟩ : syracuseStep 3017261 = 1131473) (by norm_num)
theorem B2011507 : Blo 2011435 2011507 := bstep (se 1 (by rfl) ⟨1508630, by rfl⟩ : syracuseStep 2011507 = 3017261) B3017261
theorem B4525901 : Blo 2011435 4525901 := bbase (se 3 (by rfl) ⟨848606, by rfl⟩ : syracuseStep 4525901 = 1697213) (by norm_num)
theorem B3017267 : Blo 2011435 3017267 := bstep (se 1 (by rfl) ⟨2262950, by rfl⟩ : syracuseStep 3017267 = 4525901) B4525901
theorem B2011511 : Blo 2011435 2011511 := bstep (se 1 (by rfl) ⟨1508633, by rfl⟩ : syracuseStep 2011511 = 3017267) B3017267
theorem B2545825 : Blo 2011435 2545825 := bbase (se 2 (by rfl) ⟨954684, by rfl⟩ : syracuseStep 2545825 = 1909369) (by norm_num)
theorem B3394433 : Blo 2011435 3394433 := bstep (se 2 (by rfl) ⟨1272912, by rfl⟩ : syracuseStep 3394433 = 2545825) B2545825
theorem B2262955 : Blo 2011435 2262955 := bstep (se 1 (by rfl) ⟨1697216, by rfl⟩ : syracuseStep 2262955 = 3394433) B3394433
theorem B3017273 : Blo 2011435 3017273 := bstep (se 2 (by rfl) ⟨1131477, by rfl⟩ : syracuseStep 3017273 = 2262955) B2262955
theorem B2011515 : Blo 2011435 2011515 := bstep (se 1 (by rfl) ⟨1508636, by rfl⟩ : syracuseStep 2011515 = 3017273) B3017273
theorem B22912469 : Blo 2011435 22912469 := bbase (se 7 (by rfl) ⟨268505, by rfl⟩ : syracuseStep 22912469 = 537011) (by norm_num)
theorem B15274979 : Blo 2011435 15274979 := bstep (se 1 (by rfl) ⟨11456234, by rfl⟩ : syracuseStep 15274979 = 22912469) B22912469
theorem B10183319 : Blo 2011435 10183319 := bstep (se 1 (by rfl) ⟨7637489, by rfl⟩ : syracuseStep 10183319 = 15274979) B15274979
theorem B6788879 : Blo 2011435 6788879 := bstep (se 1 (by rfl) ⟨5091659, by rfl⟩ : syracuseStep 6788879 = 10183319) B10183319
theorem B4525919 : Blo 2011435 4525919 := bstep (se 1 (by rfl) ⟨3394439, by rfl⟩ : syracuseStep 4525919 = 6788879) B6788879
theorem B3017279 : Blo 2011435 3017279 := bstep (se 1 (by rfl) ⟨2262959, by rfl⟩ : syracuseStep 3017279 = 4525919) B4525919
theorem B2011519 : Blo 2011435 2011519 := bstep (se 1 (by rfl) ⟨1508639, by rfl⟩ : syracuseStep 2011519 = 3017279) B3017279
theorem B3017285 : Blo 2011435 3017285 := bbase (se 4 (by rfl) ⟨282870, by rfl⟩ : syracuseStep 3017285 = 565741) (by norm_num)
theorem B2011523 : Blo 2011435 2011523 := bstep (se 1 (by rfl) ⟨1508642, by rfl⟩ : syracuseStep 2011523 = 3017285) B3017285
theorem B3394453 : Blo 2011435 3394453 := bbase (se 6 (by rfl) ⟨79557, by rfl⟩ : syracuseStep 3394453 = 159115) (by norm_num)
theorem B4525937 : Blo 2011435 4525937 := bstep (se 2 (by rfl) ⟨1697226, by rfl⟩ : syracuseStep 4525937 = 3394453) B3394453
theorem B3017291 : Blo 2011435 3017291 := bstep (se 1 (by rfl) ⟨2262968, by rfl⟩ : syracuseStep 3017291 = 4525937) B4525937
theorem B2011527 : Blo 2011435 2011527 := bstep (se 1 (by rfl) ⟨1508645, by rfl⟩ : syracuseStep 2011527 = 3017291) B3017291
theorem B2262973 : Blo 2011435 2262973 := bbase (se 3 (by rfl) ⟨424307, by rfl⟩ : syracuseStep 2262973 = 848615) (by norm_num)
theorem B3017297 : Blo 2011435 3017297 := bstep (se 2 (by rfl) ⟨1131486, by rfl⟩ : syracuseStep 3017297 = 2262973) B2262973
theorem B2011531 : Blo 2011435 2011531 := bstep (se 1 (by rfl) ⟨1508648, by rfl⟩ : syracuseStep 2011531 = 3017297) B3017297
theorem B6788933 : Blo 2011435 6788933 := bbase (se 4 (by rfl) ⟨636462, by rfl⟩ : syracuseStep 6788933 = 1272925) (by norm_num)
theorem B4525955 : Blo 2011435 4525955 := bstep (se 1 (by rfl) ⟨3394466, by rfl⟩ : syracuseStep 4525955 = 6788933) B6788933
theorem B3017303 : Blo 2011435 3017303 := bstep (se 1 (by rfl) ⟨2262977, by rfl⟩ : syracuseStep 3017303 = 4525955) B4525955
theorem B2011535 : Blo 2011435 2011535 := bstep (se 1 (by rfl) ⟨1508651, by rfl⟩ : syracuseStep 2011535 = 3017303) B3017303
theorem B3017309 : Blo 2011435 3017309 := bbase (se 3 (by rfl) ⟨565745, by rfl⟩ : syracuseStep 3017309 = 1131491) (by norm_num)
theorem B2011539 : Blo 2011435 2011539 := bstep (se 1 (by rfl) ⟨1508654, by rfl⟩ : syracuseStep 2011539 = 3017309) B3017309
theorem B4525973 : Blo 2011435 4525973 := bbase (se 6 (by rfl) ⟨106077, by rfl⟩ : syracuseStep 4525973 = 212155) (by norm_num)
theorem B3017315 : Blo 2011435 3017315 := bstep (se 1 (by rfl) ⟨2262986, by rfl⟩ : syracuseStep 3017315 = 4525973) B4525973
theorem B2011543 : Blo 2011435 2011543 := bstep (se 1 (by rfl) ⟨1508657, by rfl⟩ : syracuseStep 2011543 = 3017315) B3017315
theorem B4296149 : Blo 2011435 4296149 := bbase (se 7 (by rfl) ⟨50345, by rfl⟩ : syracuseStep 4296149 = 100691) (by norm_num)
theorem B2864099 : Blo 2011435 2864099 := bstep (se 1 (by rfl) ⟨2148074, by rfl⟩ : syracuseStep 2864099 = 4296149) B4296149
theorem B7637597 : Blo 2011435 7637597 := bstep (se 3 (by rfl) ⟨1432049, by rfl⟩ : syracuseStep 7637597 = 2864099) B2864099
theorem B5091731 : Blo 2011435 5091731 := bstep (se 1 (by rfl) ⟨3818798, by rfl⟩ : syracuseStep 5091731 = 7637597) B7637597
theorem B3394487 : Blo 2011435 3394487 := bstep (se 1 (by rfl) ⟨2545865, by rfl⟩ : syracuseStep 3394487 = 5091731) B5091731
theorem B2262991 : Blo 2011435 2262991 := bstep (se 1 (by rfl) ⟨1697243, by rfl⟩ : syracuseStep 2262991 = 3394487) B3394487
theorem B3017321 : Blo 2011435 3017321 := bstep (se 2 (by rfl) ⟨1131495, by rfl⟩ : syracuseStep 3017321 = 2262991) B2262991
theorem B2011547 : Blo 2011435 2011547 := bstep (se 1 (by rfl) ⟨1508660, by rfl⟩ : syracuseStep 2011547 = 3017321) B3017321
theorem B7249765 : Blo 2011435 7249765 := bbase (se 4 (by rfl) ⟨679665, by rfl⟩ : syracuseStep 7249765 = 1359331) (by norm_num)
theorem B9666353 : Blo 2011435 9666353 := bstep (se 2 (by rfl) ⟨3624882, by rfl⟩ : syracuseStep 9666353 = 7249765) B7249765
theorem B6444235 : Blo 2011435 6444235 := bstep (se 1 (by rfl) ⟨4833176, by rfl⟩ : syracuseStep 6444235 = 9666353) B9666353
theorem B8592313 : Blo 2011435 8592313 := bstep (se 2 (by rfl) ⟨3222117, by rfl⟩ : syracuseStep 8592313 = 6444235) B6444235
theorem B11456417 : Blo 2011435 11456417 := bstep (se 2 (by rfl) ⟨4296156, by rfl⟩ : syracuseStep 11456417 = 8592313) B8592313
theorem B7637611 : Blo 2011435 7637611 := bstep (se 1 (by rfl) ⟨5728208, by rfl⟩ : syracuseStep 7637611 = 11456417) B11456417
theorem B10183481 : Blo 2011435 10183481 := bstep (se 2 (by rfl) ⟨3818805, by rfl⟩ : syracuseStep 10183481 = 7637611) B7637611
theorem B6788987 : Blo 2011435 6788987 := bstep (se 1 (by rfl) ⟨5091740, by rfl⟩ : syracuseStep 6788987 = 10183481) B10183481
theorem B4525991 : Blo 2011435 4525991 := bstep (se 1 (by rfl) ⟨3394493, by rfl⟩ : syracuseStep 4525991 = 6788987) B6788987
theorem B3017327 : Blo 2011435 3017327 := bstep (se 1 (by rfl) ⟨2262995, by rfl⟩ : syracuseStep 3017327 = 4525991) B4525991
theorem B2011551 : Blo 2011435 2011551 := bstep (se 1 (by rfl) ⟨1508663, by rfl⟩ : syracuseStep 2011551 = 3017327) B3017327
theorem B3017333 : Blo 2011435 3017333 := bbase (se 5 (by rfl) ⟨141437, by rfl⟩ : syracuseStep 3017333 = 282875) (by norm_num)
theorem B2011555 : Blo 2011435 2011555 := bstep (se 1 (by rfl) ⟨1508666, by rfl⟩ : syracuseStep 2011555 = 3017333) B3017333
theorem B3818821 : Blo 2011435 3818821 := bbase (se 4 (by rfl) ⟨358014, by rfl⟩ : syracuseStep 3818821 = 716029) (by norm_num)
theorem B5091761 : Blo 2011435 5091761 := bstep (se 2 (by rfl) ⟨1909410, by rfl⟩ : syracuseStep 5091761 = 3818821) B3818821
theorem B3394507 : Blo 2011435 3394507 := bstep (se 1 (by rfl) ⟨2545880, by rfl⟩ : syracuseStep 3394507 = 5091761) B5091761
theorem B4526009 : Blo 2011435 4526009 := bstep (se 2 (by rfl) ⟨1697253, by rfl⟩ : syracuseStep 4526009 = 3394507) B3394507
theorem B3017339 : Blo 2011435 3017339 := bstep (se 1 (by rfl) ⟨2263004, by rfl⟩ : syracuseStep 3017339 = 4526009) B4526009
theorem B2011559 : Blo 2011435 2011559 := bstep (se 1 (by rfl) ⟨1508669, by rfl⟩ : syracuseStep 2011559 = 3017339) B3017339
theorem B2263009 : Blo 2011435 2263009 := bbase (se 2 (by rfl) ⟨848628, by rfl⟩ : syracuseStep 2263009 = 1697257) (by norm_num)
theorem B3017345 : Blo 2011435 3017345 := bstep (se 2 (by rfl) ⟨1131504, by rfl⟩ : syracuseStep 3017345 = 2263009) B2263009
theorem B2011563 : Blo 2011435 2011563 := bstep (se 1 (by rfl) ⟨1508672, by rfl⟩ : syracuseStep 2011563 = 3017345) B3017345
theorem B5091781 : Blo 2011435 5091781 := bbase (se 4 (by rfl) ⟨477354, by rfl⟩ : syracuseStep 5091781 = 954709) (by norm_num)
theorem B6789041 : Blo 2011435 6789041 := bstep (se 2 (by rfl) ⟨2545890, by rfl⟩ : syracuseStep 6789041 = 5091781) B5091781
theorem B4526027 : Blo 2011435 4526027 := bstep (se 1 (by rfl) ⟨3394520, by rfl⟩ : syracuseStep 4526027 = 6789041) B6789041
theorem B3017351 : Blo 2011435 3017351 := bstep (se 1 (by rfl) ⟨2263013, by rfl⟩ : syracuseStep 3017351 = 4526027) B4526027
theorem B2011567 : Blo 2011435 2011567 := bstep (se 1 (by rfl) ⟨1508675, by rfl⟩ : syracuseStep 2011567 = 3017351) B3017351
theorem B3017357 : Blo 2011435 3017357 := bbase (se 3 (by rfl) ⟨565754, by rfl⟩ : syracuseStep 3017357 = 1131509) (by norm_num)
theorem B2011571 : Blo 2011435 2011571 := bstep (se 1 (by rfl) ⟨1508678, by rfl⟩ : syracuseStep 2011571 = 3017357) B3017357
theorem B4526045 : Blo 2011435 4526045 := bbase (se 3 (by rfl) ⟨848633, by rfl⟩ : syracuseStep 4526045 = 1697267) (by norm_num)
theorem B3017363 : Blo 2011435 3017363 := bstep (se 1 (by rfl) ⟨2263022, by rfl⟩ : syracuseStep 3017363 = 4526045) B4526045
theorem B2011575 : Blo 2011435 2011575 := bstep (se 1 (by rfl) ⟨1508681, by rfl⟩ : syracuseStep 2011575 = 3017363) B3017363
theorem B3394541 : Blo 2011435 3394541 := bbase (se 3 (by rfl) ⟨636476, by rfl⟩ : syracuseStep 3394541 = 1272953) (by norm_num)
theorem B2263027 : Blo 2011435 2263027 := bstep (se 1 (by rfl) ⟨1697270, by rfl⟩ : syracuseStep 2263027 = 3394541) B3394541
theorem B3017369 : Blo 2011435 3017369 := bstep (se 2 (by rfl) ⟨1131513, by rfl⟩ : syracuseStep 3017369 = 2263027) B2263027
theorem B2011579 : Blo 2011435 2011579 := bstep (se 1 (by rfl) ⟨1508684, by rfl⟩ : syracuseStep 2011579 = 3017369) B3017369
theorem B4833253 : Blo 2011435 4833253 := bbase (se 4 (by rfl) ⟨453117, by rfl⟩ : syracuseStep 4833253 = 906235) (by norm_num)
theorem B25777349 : Blo 2011435 25777349 := bstep (se 4 (by rfl) ⟨2416626, by rfl⟩ : syracuseStep 25777349 = 4833253) B4833253
theorem B17184899 : Blo 2011435 17184899 := bstep (se 1 (by rfl) ⟨12888674, by rfl⟩ : syracuseStep 17184899 = 25777349) B25777349
theorem B11456599 : Blo 2011435 11456599 := bstep (se 1 (by rfl) ⟨8592449, by rfl⟩ : syracuseStep 11456599 = 17184899) B17184899
theorem B15275465 : Blo 2011435 15275465 := bstep (se 2 (by rfl) ⟨5728299, by rfl⟩ : syracuseStep 15275465 = 11456599) B11456599
theorem B10183643 : Blo 2011435 10183643 := bstep (se 1 (by rfl) ⟨7637732, by rfl⟩ : syracuseStep 10183643 = 15275465) B15275465
theorem B6789095 : Blo 2011435 6789095 := bstep (se 1 (by rfl) ⟨5091821, by rfl⟩ : syracuseStep 6789095 = 10183643) B10183643
theorem B4526063 : Blo 2011435 4526063 := bstep (se 1 (by rfl) ⟨3394547, by rfl⟩ : syracuseStep 4526063 = 6789095) B6789095
theorem B3017375 : Blo 2011435 3017375 := bstep (se 1 (by rfl) ⟨2263031, by rfl⟩ : syracuseStep 3017375 = 4526063) B4526063
theorem B2011583 : Blo 2011435 2011583 := bstep (se 1 (by rfl) ⟨1508687, by rfl⟩ : syracuseStep 2011583 = 3017375) B3017375
theorem B3017381 : Blo 2011435 3017381 := bbase (se 4 (by rfl) ⟨282879, by rfl⟩ : syracuseStep 3017381 = 565759) (by norm_num)
theorem B2011587 : Blo 2011435 2011587 := bstep (se 1 (by rfl) ⟨1508690, by rfl⟩ : syracuseStep 2011587 = 3017381) B3017381
theorem B2545921 : Blo 2011435 2545921 := bbase (se 2 (by rfl) ⟨954720, by rfl⟩ : syracuseStep 2545921 = 1909441) (by norm_num)
theorem B3394561 : Blo 2011435 3394561 := bstep (se 2 (by rfl) ⟨1272960, by rfl⟩ : syracuseStep 3394561 = 2545921) B2545921
theorem B4526081 : Blo 2011435 4526081 := bstep (se 2 (by rfl) ⟨1697280, by rfl⟩ : syracuseStep 4526081 = 3394561) B3394561
theorem B3017387 : Blo 2011435 3017387 := bstep (se 1 (by rfl) ⟨2263040, by rfl⟩ : syracuseStep 3017387 = 4526081) B4526081
theorem B2011591 : Blo 2011435 2011591 := bstep (se 1 (by rfl) ⟨1508693, by rfl⟩ : syracuseStep 2011591 = 3017387) B3017387
theorem B2263045 : Blo 2011435 2263045 := bbase (se 4 (by rfl) ⟨212160, by rfl⟩ : syracuseStep 2263045 = 424321) (by norm_num)
theorem B3017393 : Blo 2011435 3017393 := bstep (se 2 (by rfl) ⟨1131522, by rfl⟩ : syracuseStep 3017393 = 2263045) B2263045
theorem B2011595 : Blo 2011435 2011595 := bstep (se 1 (by rfl) ⟨1508696, by rfl⟩ : syracuseStep 2011595 = 3017393) B3017393
theorem B2864173 : Blo 2011435 2864173 := bbase (se 3 (by rfl) ⟨537032, by rfl⟩ : syracuseStep 2864173 = 1074065) (by norm_num)
theorem B3818897 : Blo 2011435 3818897 := bstep (se 2 (by rfl) ⟨1432086, by rfl⟩ : syracuseStep 3818897 = 2864173) B2864173
theorem B2545931 : Blo 2011435 2545931 := bstep (se 1 (by rfl) ⟨1909448, by rfl⟩ : syracuseStep 2545931 = 3818897) B3818897
theorem B6789149 : Blo 2011435 6789149 := bstep (se 3 (by rfl) ⟨1272965, by rfl⟩ : syracuseStep 6789149 = 2545931) B2545931
theorem B4526099 : Blo 2011435 4526099 := bstep (se 1 (by rfl) ⟨3394574, by rfl⟩ : syracuseStep 4526099 = 6789149) B6789149
theorem B3017399 : Blo 2011435 3017399 := bstep (se 1 (by rfl) ⟨2263049, by rfl⟩ : syracuseStep 3017399 = 4526099) B4526099
theorem B2011599 : Blo 2011435 2011599 := bstep (se 1 (by rfl) ⟨1508699, by rfl⟩ : syracuseStep 2011599 = 3017399) B3017399
theorem B3017405 : Blo 2011435 3017405 := bbase (se 3 (by rfl) ⟨565763, by rfl⟩ : syracuseStep 3017405 = 1131527) (by norm_num)
theorem B2011603 : Blo 2011435 2011603 := bstep (se 1 (by rfl) ⟨1508702, by rfl⟩ : syracuseStep 2011603 = 3017405) B3017405
theorem B4526117 : Blo 2011435 4526117 := bbase (se 4 (by rfl) ⟨424323, by rfl⟩ : syracuseStep 4526117 = 848647) (by norm_num)
theorem B3017411 : Blo 2011435 3017411 := bstep (se 1 (by rfl) ⟨2263058, by rfl⟩ : syracuseStep 3017411 = 4526117) B4526117
theorem B2011607 : Blo 2011435 2011607 := bstep (se 1 (by rfl) ⟨1508705, by rfl⟩ : syracuseStep 2011607 = 3017411) B3017411
theorem B5091893 : Blo 2011435 5091893 := bbase (se 5 (by rfl) ⟨238682, by rfl⟩ : syracuseStep 5091893 = 477365) (by norm_num)
theorem B3394595 : Blo 2011435 3394595 := bstep (se 1 (by rfl) ⟨2545946, by rfl⟩ : syracuseStep 3394595 = 5091893) B5091893
theorem B2263063 : Blo 2011435 2263063 := bstep (se 1 (by rfl) ⟨1697297, by rfl⟩ : syracuseStep 2263063 = 3394595) B3394595
theorem B3017417 : Blo 2011435 3017417 := bstep (se 2 (by rfl) ⟨1131531, by rfl⟩ : syracuseStep 3017417 = 2263063) B2263063
theorem B2011611 : Blo 2011435 2011611 := bstep (se 1 (by rfl) ⟨1508708, by rfl⟩ : syracuseStep 2011611 = 3017417) B3017417
theorem B9666661 : Blo 2011435 9666661 := bbase (se 4 (by rfl) ⟨906249, by rfl⟩ : syracuseStep 9666661 = 1812499) (by norm_num)
theorem B12888881 : Blo 2011435 12888881 := bstep (se 2 (by rfl) ⟨4833330, by rfl⟩ : syracuseStep 12888881 = 9666661) B9666661
theorem B8592587 : Blo 2011435 8592587 := bstep (se 1 (by rfl) ⟨6444440, by rfl⟩ : syracuseStep 8592587 = 12888881) B12888881
theorem B5728391 : Blo 2011435 5728391 := bstep (se 1 (by rfl) ⟨4296293, by rfl⟩ : syracuseStep 5728391 = 8592587) B8592587
theorem B3818927 : Blo 2011435 3818927 := bstep (se 1 (by rfl) ⟨2864195, by rfl⟩ : syracuseStep 3818927 = 5728391) B5728391
theorem B10183805 : Blo 2011435 10183805 := bstep (se 3 (by rfl) ⟨1909463, by rfl⟩ : syracuseStep 10183805 = 3818927) B3818927
theorem B6789203 : Blo 2011435 6789203 := bstep (se 1 (by rfl) ⟨5091902, by rfl⟩ : syracuseStep 6789203 = 10183805) B10183805
theorem B4526135 : Blo 2011435 4526135 := bstep (se 1 (by rfl) ⟨3394601, by rfl⟩ : syracuseStep 4526135 = 6789203) B6789203
theorem B3017423 : Blo 2011435 3017423 := bstep (se 1 (by rfl) ⟨2263067, by rfl⟩ : syracuseStep 3017423 = 4526135) B4526135
theorem B2011615 : Blo 2011435 2011615 := bstep (se 1 (by rfl) ⟨1508711, by rfl⟩ : syracuseStep 2011615 = 3017423) B3017423
theorem B3017429 : Blo 2011435 3017429 := bbase (se 7 (by rfl) ⟨35360, by rfl⟩ : syracuseStep 3017429 = 70721) (by norm_num)
theorem B2011619 : Blo 2011435 2011619 := bstep (se 1 (by rfl) ⟨1508714, by rfl⟩ : syracuseStep 2011619 = 3017429) B3017429
theorem B3625013 : Blo 2011435 3625013 := bbase (se 5 (by rfl) ⟨169922, by rfl⟩ : syracuseStep 3625013 = 339845) (by norm_num)
theorem B9666701 : Blo 2011435 9666701 := bstep (se 3 (by rfl) ⟨1812506, by rfl⟩ : syracuseStep 9666701 = 3625013) B3625013
theorem B6444467 : Blo 2011435 6444467 := bstep (se 1 (by rfl) ⟨4833350, by rfl⟩ : syracuseStep 6444467 = 9666701) B9666701
theorem B4296311 : Blo 2011435 4296311 := bstep (se 1 (by rfl) ⟨3222233, by rfl⟩ : syracuseStep 4296311 = 6444467) B6444467
theorem B2864207 : Blo 2011435 2864207 := bstep (se 1 (by rfl) ⟨2148155, by rfl⟩ : syracuseStep 2864207 = 4296311) B4296311
theorem B7637885 : Blo 2011435 7637885 := bstep (se 3 (by rfl) ⟨1432103, by rfl⟩ : syracuseStep 7637885 = 2864207) B2864207
theorem B5091923 : Blo 2011435 5091923 := bstep (se 1 (by rfl) ⟨3818942, by rfl⟩ : syracuseStep 5091923 = 7637885) B7637885
theorem B3394615 : Blo 2011435 3394615 := bstep (se 1 (by rfl) ⟨2545961, by rfl⟩ : syracuseStep 3394615 = 5091923) B5091923
theorem B4526153 : Blo 2011435 4526153 := bstep (se 2 (by rfl) ⟨1697307, by rfl⟩ : syracuseStep 4526153 = 3394615) B3394615
theorem B3017435 : Blo 2011435 3017435 := bstep (se 1 (by rfl) ⟨2263076, by rfl⟩ : syracuseStep 3017435 = 4526153) B4526153
theorem B2011623 : Blo 2011435 2011623 := bstep (se 1 (by rfl) ⟨1508717, by rfl⟩ : syracuseStep 2011623 = 3017435) B3017435
theorem B2263081 : Blo 2011435 2263081 := bbase (se 2 (by rfl) ⟨848655, by rfl⟩ : syracuseStep 2263081 = 1697311) (by norm_num)
theorem B3017441 : Blo 2011435 3017441 := bstep (se 2 (by rfl) ⟨1131540, by rfl⟩ : syracuseStep 3017441 = 2263081) B2263081
theorem B2011627 : Blo 2011435 2011627 := bstep (se 1 (by rfl) ⟨1508720, by rfl⟩ : syracuseStep 2011627 = 3017441) B3017441
theorem B29000213 : Blo 2011435 29000213 := bbase (se 6 (by rfl) ⟨679692, by rfl⟩ : syracuseStep 29000213 = 1359385) (by norm_num)
theorem B19333475 : Blo 2011435 19333475 := bstep (se 1 (by rfl) ⟨14500106, by rfl⟩ : syracuseStep 19333475 = 29000213) B29000213
theorem B12888983 : Blo 2011435 12888983 := bstep (se 1 (by rfl) ⟨9666737, by rfl⟩ : syracuseStep 12888983 = 19333475) B19333475
theorem B8592655 : Blo 2011435 8592655 := bstep (se 1 (by rfl) ⟨6444491, by rfl⟩ : syracuseStep 8592655 = 12888983) B12888983
theorem B11456873 : Blo 2011435 11456873 := bstep (se 2 (by rfl) ⟨4296327, by rfl⟩ : syracuseStep 11456873 = 8592655) B8592655
theorem B7637915 : Blo 2011435 7637915 := bstep (se 1 (by rfl) ⟨5728436, by rfl⟩ : syracuseStep 7637915 = 11456873) B11456873
theorem B5091943 : Blo 2011435 5091943 := bstep (se 1 (by rfl) ⟨3818957, by rfl⟩ : syracuseStep 5091943 = 7637915) B7637915
theorem B6789257 : Blo 2011435 6789257 := bstep (se 2 (by rfl) ⟨2545971, by rfl⟩ : syracuseStep 6789257 = 5091943) B5091943
theorem B4526171 : Blo 2011435 4526171 := bstep (se 1 (by rfl) ⟨3394628, by rfl⟩ : syracuseStep 4526171 = 6789257) B6789257
theorem B3017447 : Blo 2011435 3017447 := bstep (se 1 (by rfl) ⟨2263085, by rfl⟩ : syracuseStep 3017447 = 4526171) B4526171
theorem B2011631 : Blo 2011435 2011631 := bstep (se 1 (by rfl) ⟨1508723, by rfl⟩ : syracuseStep 2011631 = 3017447) B3017447
theorem B3017453 : Blo 2011435 3017453 := bbase (se 3 (by rfl) ⟨565772, by rfl⟩ : syracuseStep 3017453 = 1131545) (by norm_num)
theorem B2011635 : Blo 2011435 2011635 := bstep (se 1 (by rfl) ⟨1508726, by rfl⟩ : syracuseStep 2011635 = 3017453) B3017453
theorem B4526189 : Blo 2011435 4526189 := bbase (se 3 (by rfl) ⟨848660, by rfl⟩ : syracuseStep 4526189 = 1697321) (by norm_num)
theorem B3017459 : Blo 2011435 3017459 := bstep (se 1 (by rfl) ⟨2263094, by rfl⟩ : syracuseStep 3017459 = 4526189) B4526189
theorem B2011639 : Blo 2011435 2011639 := bstep (se 1 (by rfl) ⟨1508729, by rfl⟩ : syracuseStep 2011639 = 3017459) B3017459
theorem B3818981 : Blo 2011435 3818981 := bbase (se 4 (by rfl) ⟨358029, by rfl⟩ : syracuseStep 3818981 = 716059) (by norm_num)
theorem B2545987 : Blo 2011435 2545987 := bstep (se 1 (by rfl) ⟨1909490, by rfl⟩ : syracuseStep 2545987 = 3818981) B3818981
theorem B3394649 : Blo 2011435 3394649 := bstep (se 2 (by rfl) ⟨1272993, by rfl⟩ : syracuseStep 3394649 = 2545987) B2545987
theorem B2263099 : Blo 2011435 2263099 := bstep (se 1 (by rfl) ⟨1697324, by rfl⟩ : syracuseStep 2263099 = 3394649) B3394649
theorem B3017465 : Blo 2011435 3017465 := bstep (se 2 (by rfl) ⟨1131549, by rfl⟩ : syracuseStep 3017465 = 2263099) B2263099
theorem B2011643 : Blo 2011435 2011643 := bstep (se 1 (by rfl) ⟨1508732, by rfl⟩ : syracuseStep 2011643 = 3017465) B3017465
theorem B3871093 : Blo 2011435 3871093 := bbase (se 5 (by rfl) ⟨181457, by rfl⟩ : syracuseStep 3871093 = 362915) (by norm_num)
theorem B5161457 : Blo 2011435 5161457 := bstep (se 2 (by rfl) ⟨1935546, by rfl⟩ : syracuseStep 5161457 = 3871093) B3871093
theorem B3440971 : Blo 2011435 3440971 := bstep (se 1 (by rfl) ⟨2580728, by rfl⟩ : syracuseStep 3440971 = 5161457) B5161457
theorem B18351845 : Blo 2011435 18351845 := bstep (se 4 (by rfl) ⟨1720485, by rfl⟩ : syracuseStep 18351845 = 3440971) B3440971
theorem B12234563 : Blo 2011435 12234563 := bstep (se 1 (by rfl) ⟨9175922, by rfl⟩ : syracuseStep 12234563 = 18351845) B18351845
theorem B8156375 : Blo 2011435 8156375 := bstep (se 1 (by rfl) ⟨6117281, by rfl⟩ : syracuseStep 8156375 = 12234563) B12234563
theorem B5437583 : Blo 2011435 5437583 := bstep (se 1 (by rfl) ⟨4078187, by rfl⟩ : syracuseStep 5437583 = 8156375) B8156375
theorem B3625055 : Blo 2011435 3625055 := bstep (se 1 (by rfl) ⟨2718791, by rfl⟩ : syracuseStep 3625055 = 5437583) B5437583
theorem B38667253 : Blo 2011435 38667253 := bstep (se 5 (by rfl) ⟨1812527, by rfl⟩ : syracuseStep 38667253 = 3625055) B3625055
theorem B51556337 : Blo 2011435 51556337 := bstep (se 2 (by rfl) ⟨19333626, by rfl⟩ : syracuseStep 51556337 = 38667253) B38667253
theorem B34370891 : Blo 2011435 34370891 := bstep (se 1 (by rfl) ⟨25778168, by rfl⟩ : syracuseStep 34370891 = 51556337) B51556337
theorem B22913927 : Blo 2011435 22913927 := bstep (se 1 (by rfl) ⟨17185445, by rfl⟩ : syracuseStep 22913927 = 34370891) B34370891
theorem B15275951 : Blo 2011435 15275951 := bstep (se 1 (by rfl) ⟨11456963, by rfl⟩ : syracuseStep 15275951 = 22913927) B22913927
theorem B10183967 : Blo 2011435 10183967 := bstep (se 1 (by rfl) ⟨7637975, by rfl⟩ : syracuseStep 10183967 = 15275951) B15275951
theorem B6789311 : Blo 2011435 6789311 := bstep (se 1 (by rfl) ⟨5091983, by rfl⟩ : syracuseStep 6789311 = 10183967) B10183967
theorem B4526207 : Blo 2011435 4526207 := bstep (se 1 (by rfl) ⟨3394655, by rfl⟩ : syracuseStep 4526207 = 6789311) B6789311
theorem B3017471 : Blo 2011435 3017471 := bstep (se 1 (by rfl) ⟨2263103, by rfl⟩ : syracuseStep 3017471 = 4526207) B4526207
theorem B2011647 : Blo 2011435 2011647 := bstep (se 1 (by rfl) ⟨1508735, by rfl⟩ : syracuseStep 2011647 = 3017471) B3017471
theorem B3017477 : Blo 2011435 3017477 := bbase (se 4 (by rfl) ⟨282888, by rfl⟩ : syracuseStep 3017477 = 565777) (by norm_num)
theorem B2011651 : Blo 2011435 2011651 := bstep (se 1 (by rfl) ⟨1508738, by rfl⟩ : syracuseStep 2011651 = 3017477) B3017477
theorem B3394669 : Blo 2011435 3394669 := bbase (se 3 (by rfl) ⟨636500, by rfl⟩ : syracuseStep 3394669 = 1273001) (by norm_num)
theorem B4526225 : Blo 2011435 4526225 := bstep (se 2 (by rfl) ⟨1697334, by rfl⟩ : syracuseStep 4526225 = 3394669) B3394669
theorem B3017483 : Blo 2011435 3017483 := bstep (se 1 (by rfl) ⟨2263112, by rfl⟩ : syracuseStep 3017483 = 4526225) B4526225
theorem B2011655 : Blo 2011435 2011655 := bstep (se 1 (by rfl) ⟨1508741, by rfl⟩ : syracuseStep 2011655 = 3017483) B3017483
theorem B2263117 : Blo 2011435 2263117 := bbase (se 3 (by rfl) ⟨424334, by rfl⟩ : syracuseStep 2263117 = 848669) (by norm_num)
theorem B3017489 : Blo 2011435 3017489 := bstep (se 2 (by rfl) ⟨1131558, by rfl⟩ : syracuseStep 3017489 = 2263117) B2263117
theorem B2011659 : Blo 2011435 2011659 := bstep (se 1 (by rfl) ⟨1508744, by rfl⟩ : syracuseStep 2011659 = 3017489) B3017489
theorem B6789365 : Blo 2011435 6789365 := bbase (se 5 (by rfl) ⟨318251, by rfl⟩ : syracuseStep 6789365 = 636503) (by norm_num)
theorem B4526243 : Blo 2011435 4526243 := bstep (se 1 (by rfl) ⟨3394682, by rfl⟩ : syracuseStep 4526243 = 6789365) B6789365
theorem B3017495 : Blo 2011435 3017495 := bstep (se 1 (by rfl) ⟨2263121, by rfl⟩ : syracuseStep 3017495 = 4526243) B4526243
theorem B2011663 : Blo 2011435 2011663 := bstep (se 1 (by rfl) ⟨1508747, by rfl⟩ : syracuseStep 2011663 = 3017495) B3017495
theorem B3017501 : Blo 2011435 3017501 := bbase (se 3 (by rfl) ⟨565781, by rfl⟩ : syracuseStep 3017501 = 1131563) (by norm_num)
theorem B2011667 : Blo 2011435 2011667 := bstep (se 1 (by rfl) ⟨1508750, by rfl⟩ : syracuseStep 2011667 = 3017501) B3017501
theorem B4526261 : Blo 2011435 4526261 := bbase (se 5 (by rfl) ⟨212168, by rfl⟩ : syracuseStep 4526261 = 424337) (by norm_num)
theorem B3017507 : Blo 2011435 3017507 := bstep (se 1 (by rfl) ⟨2263130, by rfl⟩ : syracuseStep 3017507 = 4526261) B4526261
theorem B2011671 : Blo 2011435 2011671 := bstep (se 1 (by rfl) ⟨1508753, by rfl⟩ : syracuseStep 2011671 = 3017507) B3017507
theorem B3222317 : Blo 2011435 3222317 := bbase (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) (by norm_num)
theorem B2148211 : Blo 2011435 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B11457125 : Blo 2011435 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B7638083 : Blo 2011435 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B5092055 : Blo 2011435 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B3394703 : Blo 2011435 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B2263135 : Blo 2011435 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B3017513 : Blo 2011435 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B2011675 : Blo 2011435 2011675 := bstep (se 1 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 2011675 = 3017513) B3017513
theorem B4833485 : Blo 2011435 4833485 := bbase (se 3 (by rfl) ⟨906278, by rfl⟩ : syracuseStep 4833485 = 1812557) (by norm_num)
theorem B3222323 : Blo 2011435 3222323 := bstep (se 1 (by rfl) ⟨2416742, by rfl⟩ : syracuseStep 3222323 = 4833485) B4833485
theorem B2148215 : Blo 2011435 2148215 := bstep (se 1 (by rfl) ⟨1611161, by rfl⟩ : syracuseStep 2148215 = 3222323) B3222323
theorem B5728573 : Blo 2011435 5728573 := bstep (se 3 (by rfl) ⟨1074107, by rfl⟩ : syracuseStep 5728573 = 2148215) B2148215
theorem B7638097 : Blo 2011435 7638097 := bstep (se 2 (by rfl) ⟨2864286, by rfl⟩ : syracuseStep 7638097 = 5728573) B5728573
theorem B10184129 : Blo 2011435 10184129 := bstep (se 2 (by rfl) ⟨3819048, by rfl⟩ : syracuseStep 10184129 = 7638097) B7638097
theorem B6789419 : Blo 2011435 6789419 := bstep (se 1 (by rfl) ⟨5092064, by rfl⟩ : syracuseStep 6789419 = 10184129) B10184129
theorem B4526279 : Blo 2011435 4526279 := bstep (se 1 (by rfl) ⟨3394709, by rfl⟩ : syracuseStep 4526279 = 6789419) B6789419
theorem B3017519 : Blo 2011435 3017519 := bstep (se 1 (by rfl) ⟨2263139, by rfl⟩ : syracuseStep 3017519 = 4526279) B4526279
theorem B2011679 : Blo 2011435 2011679 := bstep (se 1 (by rfl) ⟨1508759, by rfl⟩ : syracuseStep 2011679 = 3017519) B3017519
theorem B3017525 : Blo 2011435 3017525 := bbase (se 5 (by rfl) ⟨141446, by rfl⟩ : syracuseStep 3017525 = 282893) (by norm_num)
theorem B2011683 : Blo 2011435 2011683 := bstep (se 1 (by rfl) ⟨1508762, by rfl⟩ : syracuseStep 2011683 = 3017525) B3017525
theorem B5092085 : Blo 2011435 5092085 := bbase (se 5 (by rfl) ⟨238691, by rfl⟩ : syracuseStep 5092085 = 477383) (by norm_num)
theorem B3394723 : Blo 2011435 3394723 := bstep (se 1 (by rfl) ⟨2546042, by rfl⟩ : syracuseStep 3394723 = 5092085) B5092085
theorem B4526297 : Blo 2011435 4526297 := bstep (se 2 (by rfl) ⟨1697361, by rfl⟩ : syracuseStep 4526297 = 3394723) B3394723
theorem B3017531 : Blo 2011435 3017531 := bstep (se 1 (by rfl) ⟨2263148, by rfl⟩ : syracuseStep 3017531 = 4526297) B4526297
theorem B2011687 : Blo 2011435 2011687 := bstep (se 1 (by rfl) ⟨1508765, by rfl⟩ : syracuseStep 2011687 = 3017531) B3017531
theorem B2263153 : Blo 2011435 2263153 := bbase (se 2 (by rfl) ⟨848682, by rfl⟩ : syracuseStep 2263153 = 1697365) (by norm_num)
theorem B3017537 : Blo 2011435 3017537 := bstep (se 2 (by rfl) ⟨1131576, by rfl⟩ : syracuseStep 3017537 = 2263153) B2263153
theorem B2011691 : Blo 2011435 2011691 := bstep (se 1 (by rfl) ⟨1508768, by rfl⟩ : syracuseStep 2011691 = 3017537) B3017537
theorem B2066965 : Blo 2011435 2066965 := bbase (se 6 (by rfl) ⟨48444, by rfl⟩ : syracuseStep 2066965 = 96889) (by norm_num)
theorem B11023813 : Blo 2011435 11023813 := bstep (se 4 (by rfl) ⟨1033482, by rfl⟩ : syracuseStep 11023813 = 2066965) B2066965
theorem B14698417 : Blo 2011435 14698417 := bstep (se 2 (by rfl) ⟨5511906, by rfl⟩ : syracuseStep 14698417 = 11023813) B11023813
theorem B19597889 : Blo 2011435 19597889 := bstep (se 2 (by rfl) ⟨7349208, by rfl⟩ : syracuseStep 19597889 = 14698417) B14698417
theorem B13065259 : Blo 2011435 13065259 := bstep (se 1 (by rfl) ⟨9798944, by rfl⟩ : syracuseStep 13065259 = 19597889) B19597889
theorem B17420345 : Blo 2011435 17420345 := bstep (se 2 (by rfl) ⟨6532629, by rfl⟩ : syracuseStep 17420345 = 13065259) B13065259
theorem B11613563 : Blo 2011435 11613563 := bstep (se 1 (by rfl) ⟨8710172, by rfl⟩ : syracuseStep 11613563 = 17420345) B17420345
theorem B7742375 : Blo 2011435 7742375 := bstep (se 1 (by rfl) ⟨5806781, by rfl⟩ : syracuseStep 7742375 = 11613563) B11613563
theorem B5161583 : Blo 2011435 5161583 := bstep (se 1 (by rfl) ⟨3871187, by rfl⟩ : syracuseStep 5161583 = 7742375) B7742375
theorem B3441055 : Blo 2011435 3441055 := bstep (se 1 (by rfl) ⟨2580791, by rfl⟩ : syracuseStep 3441055 = 5161583) B5161583
theorem B4588073 : Blo 2011435 4588073 := bstep (se 2 (by rfl) ⟨1720527, by rfl⟩ : syracuseStep 4588073 = 3441055) B3441055
theorem B3058715 : Blo 2011435 3058715 := bstep (se 1 (by rfl) ⟨2294036, by rfl⟩ : syracuseStep 3058715 = 4588073) B4588073
theorem B2039143 : Blo 2011435 2039143 := bstep (se 1 (by rfl) ⟨1529357, by rfl⟩ : syracuseStep 2039143 = 3058715) B3058715
theorem B2718857 : Blo 2011435 2718857 := bstep (se 2 (by rfl) ⟨1019571, by rfl⟩ : syracuseStep 2718857 = 2039143) B2039143
theorem B7250285 : Blo 2011435 7250285 := bstep (se 3 (by rfl) ⟨1359428, by rfl⟩ : syracuseStep 7250285 = 2718857) B2718857
theorem B4833523 : Blo 2011435 4833523 := bstep (se 1 (by rfl) ⟨3625142, by rfl⟩ : syracuseStep 4833523 = 7250285) B7250285
theorem B6444697 : Blo 2011435 6444697 := bstep (se 2 (by rfl) ⟨2416761, by rfl⟩ : syracuseStep 6444697 = 4833523) B4833523
theorem B8592929 : Blo 2011435 8592929 := bstep (se 2 (by rfl) ⟨3222348, by rfl⟩ : syracuseStep 8592929 = 6444697) B6444697
theorem B5728619 : Blo 2011435 5728619 := bstep (se 1 (by rfl) ⟨4296464, by rfl⟩ : syracuseStep 5728619 = 8592929) B8592929
theorem B3819079 : Blo 2011435 3819079 := bstep (se 1 (by rfl) ⟨2864309, by rfl⟩ : syracuseStep 3819079 = 5728619) B5728619
theorem B5092105 : Blo 2011435 5092105 := bstep (se 2 (by rfl) ⟨1909539, by rfl⟩ : syracuseStep 5092105 = 3819079) B3819079
theorem B6789473 : Blo 2011435 6789473 := bstep (se 2 (by rfl) ⟨2546052, by rfl⟩ : syracuseStep 6789473 = 5092105) B5092105
theorem B4526315 : Blo 2011435 4526315 := bstep (se 1 (by rfl) ⟨3394736, by rfl⟩ : syracuseStep 4526315 = 6789473) B6789473
theorem B3017543 : Blo 2011435 3017543 := bstep (se 1 (by rfl) ⟨2263157, by rfl⟩ : syracuseStep 3017543 = 4526315) B4526315
theorem B2011695 : Blo 2011435 2011695 := bstep (se 1 (by rfl) ⟨1508771, by rfl⟩ : syracuseStep 2011695 = 3017543) B3017543
theorem B3017549 : Blo 2011435 3017549 := bbase (se 3 (by rfl) ⟨565790, by rfl⟩ : syracuseStep 3017549 = 1131581) (by norm_num)
theorem B2011699 : Blo 2011435 2011699 := bstep (se 1 (by rfl) ⟨1508774, by rfl⟩ : syracuseStep 2011699 = 3017549) B3017549
theorem B4526333 : Blo 2011435 4526333 := bbase (se 3 (by rfl) ⟨848687, by rfl⟩ : syracuseStep 4526333 = 1697375) (by norm_num)
theorem B3017555 : Blo 2011435 3017555 := bstep (se 1 (by rfl) ⟨2263166, by rfl⟩ : syracuseStep 3017555 = 4526333) B4526333
theorem B2011703 : Blo 2011435 2011703 := bstep (se 1 (by rfl) ⟨1508777, by rfl⟩ : syracuseStep 2011703 = 3017555) B3017555
theorem B3394757 : Blo 2011435 3394757 := bbase (se 4 (by rfl) ⟨318258, by rfl⟩ : syracuseStep 3394757 = 636517) (by norm_num)
theorem B2263171 : Blo 2011435 2263171 := bstep (se 1 (by rfl) ⟨1697378, by rfl⟩ : syracuseStep 2263171 = 3394757) B3394757
theorem B3017561 : Blo 2011435 3017561 := bstep (se 2 (by rfl) ⟨1131585, by rfl⟩ : syracuseStep 3017561 = 2263171) B2263171
theorem B2011707 : Blo 2011435 2011707 := bstep (se 1 (by rfl) ⟨1508780, by rfl⟩ : syracuseStep 2011707 = 3017561) B3017561
theorem B15276437 : Blo 2011435 15276437 := bbase (se 6 (by rfl) ⟨358041, by rfl⟩ : syracuseStep 15276437 = 716083) (by norm_num)
theorem B10184291 : Blo 2011435 10184291 := bstep (se 1 (by rfl) ⟨7638218, by rfl⟩ : syracuseStep 10184291 = 15276437) B15276437
theorem B6789527 : Blo 2011435 6789527 := bstep (se 1 (by rfl) ⟨5092145, by rfl⟩ : syracuseStep 6789527 = 10184291) B10184291
theorem B4526351 : Blo 2011435 4526351 := bstep (se 1 (by rfl) ⟨3394763, by rfl⟩ : syracuseStep 4526351 = 6789527) B6789527
theorem B3017567 : Blo 2011435 3017567 := bstep (se 1 (by rfl) ⟨2263175, by rfl⟩ : syracuseStep 3017567 = 4526351) B4526351
theorem B2011711 : Blo 2011435 2011711 := bstep (se 1 (by rfl) ⟨1508783, by rfl⟩ : syracuseStep 2011711 = 3017567) B3017567
theorem B3017573 : Blo 2011435 3017573 := bbase (se 4 (by rfl) ⟨282897, by rfl⟩ : syracuseStep 3017573 = 565795) (by norm_num)
theorem B2011715 : Blo 2011435 2011715 := bstep (se 1 (by rfl) ⟨1508786, by rfl⟩ : syracuseStep 2011715 = 3017573) B3017573
theorem B3819125 : Blo 2011435 3819125 := bbase (se 5 (by rfl) ⟨179021, by rfl⟩ : syracuseStep 3819125 = 358043) (by norm_num)
theorem B2546083 : Blo 2011435 2546083 := bstep (se 1 (by rfl) ⟨1909562, by rfl⟩ : syracuseStep 2546083 = 3819125) B3819125
theorem B3394777 : Blo 2011435 3394777 := bstep (se 2 (by rfl) ⟨1273041, by rfl⟩ : syracuseStep 3394777 = 2546083) B2546083
theorem B4526369 : Blo 2011435 4526369 := bstep (se 2 (by rfl) ⟨1697388, by rfl⟩ : syracuseStep 4526369 = 3394777) B3394777
theorem B3017579 : Blo 2011435 3017579 := bstep (se 1 (by rfl) ⟨2263184, by rfl⟩ : syracuseStep 3017579 = 4526369) B4526369
theorem B2011719 : Blo 2011435 2011719 := bstep (se 1 (by rfl) ⟨1508789, by rfl⟩ : syracuseStep 2011719 = 3017579) B3017579
theorem B2263189 : Blo 2011435 2263189 := bbase (se 6 (by rfl) ⟨53043, by rfl⟩ : syracuseStep 2263189 = 106087) (by norm_num)
theorem B3017585 : Blo 2011435 3017585 := bstep (se 2 (by rfl) ⟨1131594, by rfl⟩ : syracuseStep 3017585 = 2263189) B2263189
theorem B2011723 : Blo 2011435 2011723 := bstep (se 1 (by rfl) ⟨1508792, by rfl⟩ : syracuseStep 2011723 = 3017585) B3017585
theorem B2546093 : Blo 2011435 2546093 := bbase (se 3 (by rfl) ⟨477392, by rfl⟩ : syracuseStep 2546093 = 954785) (by norm_num)
theorem B6789581 : Blo 2011435 6789581 := bstep (se 3 (by rfl) ⟨1273046, by rfl⟩ : syracuseStep 6789581 = 2546093) B2546093
theorem B4526387 : Blo 2011435 4526387 := bstep (se 1 (by rfl) ⟨3394790, by rfl⟩ : syracuseStep 4526387 = 6789581) B6789581
theorem B3017591 : Blo 2011435 3017591 := bstep (se 1 (by rfl) ⟨2263193, by rfl⟩ : syracuseStep 3017591 = 4526387) B4526387
theorem B2011727 : Blo 2011435 2011727 := bstep (se 1 (by rfl) ⟨1508795, by rfl⟩ : syracuseStep 2011727 = 3017591) B3017591
theorem B3017597 : Blo 2011435 3017597 := bbase (se 3 (by rfl) ⟨565799, by rfl⟩ : syracuseStep 3017597 = 1131599) (by norm_num)
theorem B2011731 : Blo 2011435 2011731 := bstep (se 1 (by rfl) ⟨1508798, by rfl⟩ : syracuseStep 2011731 = 3017597) B3017597
theorem B4526405 : Blo 2011435 4526405 := bbase (se 4 (by rfl) ⟨424350, by rfl⟩ : syracuseStep 4526405 = 848701) (by norm_num)
theorem B3017603 : Blo 2011435 3017603 := bstep (se 1 (by rfl) ⟨2263202, by rfl⟩ : syracuseStep 3017603 = 4526405) B4526405
theorem B2011735 : Blo 2011435 2011735 := bstep (se 1 (by rfl) ⟨1508801, by rfl⟩ : syracuseStep 2011735 = 3017603) B3017603
theorem B9799157 : Blo 2011435 9799157 := bbase (se 5 (by rfl) ⟨459335, by rfl⟩ : syracuseStep 9799157 = 918671) (by norm_num)
theorem B6532771 : Blo 2011435 6532771 := bstep (se 1 (by rfl) ⟨4899578, by rfl⟩ : syracuseStep 6532771 = 9799157) B9799157
theorem B8710361 : Blo 2011435 8710361 := bstep (se 2 (by rfl) ⟨3266385, by rfl⟩ : syracuseStep 8710361 = 6532771) B6532771
theorem B5806907 : Blo 2011435 5806907 := bstep (se 1 (by rfl) ⟨4355180, by rfl⟩ : syracuseStep 5806907 = 8710361) B8710361
theorem B3871271 : Blo 2011435 3871271 := bstep (se 1 (by rfl) ⟨2903453, by rfl⟩ : syracuseStep 3871271 = 5806907) B5806907
theorem B10323389 : Blo 2011435 10323389 := bstep (se 3 (by rfl) ⟨1935635, by rfl⟩ : syracuseStep 10323389 = 3871271) B3871271
theorem B6882259 : Blo 2011435 6882259 := bstep (se 1 (by rfl) ⟨5161694, by rfl⟩ : syracuseStep 6882259 = 10323389) B10323389
theorem B9176345 : Blo 2011435 9176345 := bstep (se 2 (by rfl) ⟨3441129, by rfl⟩ : syracuseStep 9176345 = 6882259) B6882259
theorem B6117563 : Blo 2011435 6117563 := bstep (se 1 (by rfl) ⟨4588172, by rfl⟩ : syracuseStep 6117563 = 9176345) B9176345
theorem B16313501 : Blo 2011435 16313501 := bstep (se 3 (by rfl) ⟨3058781, by rfl⟩ : syracuseStep 16313501 = 6117563) B6117563
theorem B10875667 : Blo 2011435 10875667 := bstep (se 1 (by rfl) ⟨8156750, by rfl⟩ : syracuseStep 10875667 = 16313501) B16313501
theorem B14500889 : Blo 2011435 14500889 := bstep (se 2 (by rfl) ⟨5437833, by rfl⟩ : syracuseStep 14500889 = 10875667) B10875667
theorem B9667259 : Blo 2011435 9667259 := bstep (se 1 (by rfl) ⟨7250444, by rfl⟩ : syracuseStep 9667259 = 14500889) B14500889
theorem B6444839 : Blo 2011435 6444839 := bstep (se 1 (by rfl) ⟨4833629, by rfl⟩ : syracuseStep 6444839 = 9667259) B9667259
theorem B4296559 : Blo 2011435 4296559 := bstep (se 1 (by rfl) ⟨3222419, by rfl⟩ : syracuseStep 4296559 = 6444839) B6444839
theorem B5728745 : Blo 2011435 5728745 := bstep (se 2 (by rfl) ⟨2148279, by rfl⟩ : syracuseStep 5728745 = 4296559) B4296559
theorem B3819163 : Blo 2011435 3819163 := bstep (se 1 (by rfl) ⟨2864372, by rfl⟩ : syracuseStep 3819163 = 5728745) B5728745
theorem B5092217 : Blo 2011435 5092217 := bstep (se 2 (by rfl) ⟨1909581, by rfl⟩ : syracuseStep 5092217 = 3819163) B3819163
theorem B3394811 : Blo 2011435 3394811 := bstep (se 1 (by rfl) ⟨2546108, by rfl⟩ : syracuseStep 3394811 = 5092217) B5092217
theorem B2263207 : Blo 2011435 2263207 := bstep (se 1 (by rfl) ⟨1697405, by rfl⟩ : syracuseStep 2263207 = 3394811) B3394811
theorem B3017609 : Blo 2011435 3017609 := bstep (se 2 (by rfl) ⟨1131603, by rfl⟩ : syracuseStep 3017609 = 2263207) B2263207
theorem B2011739 : Blo 2011435 2011739 := bstep (se 1 (by rfl) ⟨1508804, by rfl⟩ : syracuseStep 2011739 = 3017609) B3017609
theorem B10184453 : Blo 2011435 10184453 := bbase (se 4 (by rfl) ⟨954792, by rfl⟩ : syracuseStep 10184453 = 1909585) (by norm_num)
theorem B6789635 : Blo 2011435 6789635 := bstep (se 1 (by rfl) ⟨5092226, by rfl⟩ : syracuseStep 6789635 = 10184453) B10184453
theorem B4526423 : Blo 2011435 4526423 := bstep (se 1 (by rfl) ⟨3394817, by rfl⟩ : syracuseStep 4526423 = 6789635) B6789635
theorem B3017615 : Blo 2011435 3017615 := bstep (se 1 (by rfl) ⟨2263211, by rfl⟩ : syracuseStep 3017615 = 4526423) B4526423
theorem B2011743 : Blo 2011435 2011743 := bstep (se 1 (by rfl) ⟨1508807, by rfl⟩ : syracuseStep 2011743 = 3017615) B3017615
theorem B3017621 : Blo 2011435 3017621 := bbase (se 6 (by rfl) ⟨70725, by rfl⟩ : syracuseStep 3017621 = 141451) (by norm_num)
theorem B2011747 : Blo 2011435 2011747 := bstep (se 1 (by rfl) ⟨1508810, by rfl⟩ : syracuseStep 2011747 = 3017621) B3017621
theorem B11457557 : Blo 2011435 11457557 := bbase (se 6 (by rfl) ⟨268536, by rfl⟩ : syracuseStep 11457557 = 537073) (by norm_num)
theorem B7638371 : Blo 2011435 7638371 := bstep (se 1 (by rfl) ⟨5728778, by rfl⟩ : syracuseStep 7638371 = 11457557) B11457557
theorem B5092247 : Blo 2011435 5092247 := bstep (se 1 (by rfl) ⟨3819185, by rfl⟩ : syracuseStep 5092247 = 7638371) B7638371
theorem B3394831 : Blo 2011435 3394831 := bstep (se 1 (by rfl) ⟨2546123, by rfl⟩ : syracuseStep 3394831 = 5092247) B5092247
theorem B4526441 : Blo 2011435 4526441 := bstep (se 2 (by rfl) ⟨1697415, by rfl⟩ : syracuseStep 4526441 = 3394831) B3394831
theorem B3017627 : Blo 2011435 3017627 := bstep (se 1 (by rfl) ⟨2263220, by rfl⟩ : syracuseStep 3017627 = 4526441) B4526441
theorem B2011751 : Blo 2011435 2011751 := bstep (se 1 (by rfl) ⟨1508813, by rfl⟩ : syracuseStep 2011751 = 3017627) B3017627
theorem B2263225 : Blo 2011435 2263225 := bbase (se 2 (by rfl) ⟨848709, by rfl⟩ : syracuseStep 2263225 = 1697419) (by norm_num)
theorem B3017633 : Blo 2011435 3017633 := bstep (se 2 (by rfl) ⟨1131612, by rfl⟩ : syracuseStep 3017633 = 2263225) B2263225
theorem B2011755 : Blo 2011435 2011755 := bstep (se 1 (by rfl) ⟨1508816, by rfl⟩ : syracuseStep 2011755 = 3017633) B3017633
theorem B4833677 : Blo 2011435 4833677 := bbase (se 3 (by rfl) ⟨906314, by rfl⟩ : syracuseStep 4833677 = 1812629) (by norm_num)
theorem B3222451 : Blo 2011435 3222451 := bstep (se 1 (by rfl) ⟨2416838, by rfl⟩ : syracuseStep 3222451 = 4833677) B4833677
theorem B4296601 : Blo 2011435 4296601 := bstep (se 2 (by rfl) ⟨1611225, by rfl⟩ : syracuseStep 4296601 = 3222451) B3222451
theorem B5728801 : Blo 2011435 5728801 := bstep (se 2 (by rfl) ⟨2148300, by rfl⟩ : syracuseStep 5728801 = 4296601) B4296601
theorem B7638401 : Blo 2011435 7638401 := bstep (se 2 (by rfl) ⟨2864400, by rfl⟩ : syracuseStep 7638401 = 5728801) B5728801
theorem B5092267 : Blo 2011435 5092267 := bstep (se 1 (by rfl) ⟨3819200, by rfl⟩ : syracuseStep 5092267 = 7638401) B7638401
theorem B6789689 : Blo 2011435 6789689 := bstep (se 2 (by rfl) ⟨2546133, by rfl⟩ : syracuseStep 6789689 = 5092267) B5092267
theorem B4526459 : Blo 2011435 4526459 := bstep (se 1 (by rfl) ⟨3394844, by rfl⟩ : syracuseStep 4526459 = 6789689) B6789689
theorem B3017639 : Blo 2011435 3017639 := bstep (se 1 (by rfl) ⟨2263229, by rfl⟩ : syracuseStep 3017639 = 4526459) B4526459
theorem B2011759 : Blo 2011435 2011759 := bstep (se 1 (by rfl) ⟨1508819, by rfl⟩ : syracuseStep 2011759 = 3017639) B3017639
theorem B3017645 : Blo 2011435 3017645 := bbase (se 3 (by rfl) ⟨565808, by rfl⟩ : syracuseStep 3017645 = 1131617) (by norm_num)
theorem B2011763 : Blo 2011435 2011763 := bstep (se 1 (by rfl) ⟨1508822, by rfl⟩ : syracuseStep 2011763 = 3017645) B3017645
theorem B4526477 : Blo 2011435 4526477 := bbase (se 3 (by rfl) ⟨848714, by rfl⟩ : syracuseStep 4526477 = 1697429) (by norm_num)
theorem B3017651 : Blo 2011435 3017651 := bstep (se 1 (by rfl) ⟨2263238, by rfl⟩ : syracuseStep 3017651 = 4526477) B4526477
theorem B2011767 : Blo 2011435 2011767 := bstep (se 1 (by rfl) ⟨1508825, by rfl⟩ : syracuseStep 2011767 = 3017651) B3017651
theorem B2546149 : Blo 2011435 2546149 := bbase (se 4 (by rfl) ⟨238701, by rfl⟩ : syracuseStep 2546149 = 477403) (by norm_num)
theorem B3394865 : Blo 2011435 3394865 := bstep (se 2 (by rfl) ⟨1273074, by rfl⟩ : syracuseStep 3394865 = 2546149) B2546149
theorem B2263243 : Blo 2011435 2263243 := bstep (se 1 (by rfl) ⟨1697432, by rfl⟩ : syracuseStep 2263243 = 3394865) B3394865
theorem B3017657 : Blo 2011435 3017657 := bstep (se 2 (by rfl) ⟨1131621, by rfl⟩ : syracuseStep 3017657 = 2263243) B2263243
theorem B2011771 : Blo 2011435 2011771 := bstep (se 1 (by rfl) ⟨1508828, by rfl⟩ : syracuseStep 2011771 = 3017657) B3017657
theorem B4588253 : Blo 2011435 4588253 := bbase (se 3 (by rfl) ⟨860297, by rfl⟩ : syracuseStep 4588253 = 1720595) (by norm_num)
theorem B3058835 : Blo 2011435 3058835 := bstep (se 1 (by rfl) ⟨2294126, by rfl⟩ : syracuseStep 3058835 = 4588253) B4588253
theorem B32627573 : Blo 2011435 32627573 := bstep (se 5 (by rfl) ⟨1529417, by rfl⟩ : syracuseStep 32627573 = 3058835) B3058835
theorem B21751715 : Blo 2011435 21751715 := bstep (se 1 (by rfl) ⟨16313786, by rfl⟩ : syracuseStep 21751715 = 32627573) B32627573
theorem B14501143 : Blo 2011435 14501143 := bstep (se 1 (by rfl) ⟨10875857, by rfl⟩ : syracuseStep 14501143 = 21751715) B21751715
theorem B19334857 : Blo 2011435 19334857 := bstep (se 2 (by rfl) ⟨7250571, by rfl⟩ : syracuseStep 19334857 = 14501143) B14501143
theorem B25779809 : Blo 2011435 25779809 := bstep (se 2 (by rfl) ⟨9667428, by rfl⟩ : syracuseStep 25779809 = 19334857) B19334857
theorem B17186539 : Blo 2011435 17186539 := bstep (se 1 (by rfl) ⟨12889904, by rfl⟩ : syracuseStep 17186539 = 25779809) B25779809
theorem B22915385 : Blo 2011435 22915385 := bstep (se 2 (by rfl) ⟨8593269, by rfl⟩ : syracuseStep 22915385 = 17186539) B17186539
theorem B15276923 : Blo 2011435 15276923 := bstep (se 1 (by rfl) ⟨11457692, by rfl⟩ : syracuseStep 15276923 = 22915385) B22915385
theorem B10184615 : Blo 2011435 10184615 := bstep (se 1 (by rfl) ⟨7638461, by rfl⟩ : syracuseStep 10184615 = 15276923) B15276923
theorem B6789743 : Blo 2011435 6789743 := bstep (se 1 (by rfl) ⟨5092307, by rfl⟩ : syracuseStep 6789743 = 10184615) B10184615
theorem B4526495 : Blo 2011435 4526495 := bstep (se 1 (by rfl) ⟨3394871, by rfl⟩ : syracuseStep 4526495 = 6789743) B6789743
theorem B3017663 : Blo 2011435 3017663 := bstep (se 1 (by rfl) ⟨2263247, by rfl⟩ : syracuseStep 3017663 = 4526495) B4526495
theorem B2011775 : Blo 2011435 2011775 := bstep (se 1 (by rfl) ⟨1508831, by rfl⟩ : syracuseStep 2011775 = 3017663) B3017663
theorem B3017669 : Blo 2011435 3017669 := bbase (se 4 (by rfl) ⟨282906, by rfl⟩ : syracuseStep 3017669 = 565813) (by norm_num)
theorem B2011779 : Blo 2011435 2011779 := bstep (se 1 (by rfl) ⟨1508834, by rfl⟩ : syracuseStep 2011779 = 3017669) B3017669
theorem B3394885 : Blo 2011435 3394885 := bbase (se 4 (by rfl) ⟨318270, by rfl⟩ : syracuseStep 3394885 = 636541) (by norm_num)
theorem B4526513 : Blo 2011435 4526513 := bstep (se 2 (by rfl) ⟨1697442, by rfl⟩ : syracuseStep 4526513 = 3394885) B3394885
theorem B3017675 : Blo 2011435 3017675 := bstep (se 1 (by rfl) ⟨2263256, by rfl⟩ : syracuseStep 3017675 = 4526513) B4526513
theorem B2011783 : Blo 2011435 2011783 := bstep (se 1 (by rfl) ⟨1508837, by rfl⟩ : syracuseStep 2011783 = 3017675) B3017675
theorem B2263261 : Blo 2011435 2263261 := bbase (se 3 (by rfl) ⟨424361, by rfl⟩ : syracuseStep 2263261 = 848723) (by norm_num)
theorem B3017681 : Blo 2011435 3017681 := bstep (se 2 (by rfl) ⟨1131630, by rfl⟩ : syracuseStep 3017681 = 2263261) B2263261
theorem B2011787 : Blo 2011435 2011787 := bstep (se 1 (by rfl) ⟨1508840, by rfl⟩ : syracuseStep 2011787 = 3017681) B3017681
theorem B6789797 : Blo 2011435 6789797 := bbase (se 4 (by rfl) ⟨636543, by rfl⟩ : syracuseStep 6789797 = 1273087) (by norm_num)
theorem B4526531 : Blo 2011435 4526531 := bstep (se 1 (by rfl) ⟨3394898, by rfl⟩ : syracuseStep 4526531 = 6789797) B6789797
theorem B3017687 : Blo 2011435 3017687 := bstep (se 1 (by rfl) ⟨2263265, by rfl⟩ : syracuseStep 3017687 = 4526531) B4526531
theorem B2011791 : Blo 2011435 2011791 := bstep (se 1 (by rfl) ⟨1508843, by rfl⟩ : syracuseStep 2011791 = 3017687) B3017687
theorem B3017693 : Blo 2011435 3017693 := bbase (se 3 (by rfl) ⟨565817, by rfl⟩ : syracuseStep 3017693 = 1131635) (by norm_num)
theorem B2011795 : Blo 2011435 2011795 := bstep (se 1 (by rfl) ⟨1508846, by rfl⟩ : syracuseStep 2011795 = 3017693) B3017693
theorem B4526549 : Blo 2011435 4526549 := bbase (se 7 (by rfl) ⟨53045, by rfl⟩ : syracuseStep 4526549 = 106091) (by norm_num)
theorem B3017699 : Blo 2011435 3017699 := bstep (se 1 (by rfl) ⟨2263274, by rfl⟩ : syracuseStep 3017699 = 4526549) B4526549
theorem B2011799 : Blo 2011435 2011799 := bstep (se 1 (by rfl) ⟨1508849, by rfl⟩ : syracuseStep 2011799 = 3017699) B3017699
theorem B2756101 : Blo 2011435 2756101 := bbase (se 4 (by rfl) ⟨258384, by rfl⟩ : syracuseStep 2756101 = 516769) (by norm_num)
theorem B3674801 : Blo 2011435 3674801 := bstep (se 2 (by rfl) ⟨1378050, by rfl⟩ : syracuseStep 3674801 = 2756101) B2756101
theorem B2449867 : Blo 2011435 2449867 := bstep (se 1 (by rfl) ⟨1837400, by rfl⟩ : syracuseStep 2449867 = 3674801) B3674801
theorem B3266489 : Blo 2011435 3266489 := bstep (se 2 (by rfl) ⟨1224933, by rfl⟩ : syracuseStep 3266489 = 2449867) B2449867
theorem B2177659 : Blo 2011435 2177659 := bstep (se 1 (by rfl) ⟨1633244, by rfl⟩ : syracuseStep 2177659 = 3266489) B3266489
theorem B2903545 : Blo 2011435 2903545 := bstep (se 2 (by rfl) ⟨1088829, by rfl⟩ : syracuseStep 2903545 = 2177659) B2177659
theorem B15485573 : Blo 2011435 15485573 := bstep (se 4 (by rfl) ⟨1451772, by rfl⟩ : syracuseStep 15485573 = 2903545) B2903545
theorem B10323715 : Blo 2011435 10323715 := bstep (se 1 (by rfl) ⟨7742786, by rfl⟩ : syracuseStep 10323715 = 15485573) B15485573
theorem B13764953 : Blo 2011435 13764953 := bstep (se 2 (by rfl) ⟨5161857, by rfl⟩ : syracuseStep 13764953 = 10323715) B10323715
theorem B9176635 : Blo 2011435 9176635 := bstep (se 1 (by rfl) ⟨6882476, by rfl⟩ : syracuseStep 9176635 = 13764953) B13764953
theorem B48942053 : Blo 2011435 48942053 := bstep (se 4 (by rfl) ⟨4588317, by rfl⟩ : syracuseStep 48942053 = 9176635) B9176635
theorem B32628035 : Blo 2011435 32628035 := bstep (se 1 (by rfl) ⟨24471026, by rfl⟩ : syracuseStep 32628035 = 48942053) B48942053
theorem B21752023 : Blo 2011435 21752023 := bstep (se 1 (by rfl) ⟨16314017, by rfl⟩ : syracuseStep 21752023 = 32628035) B32628035
theorem B29002697 : Blo 2011435 29002697 := bstep (se 2 (by rfl) ⟨10876011, by rfl⟩ : syracuseStep 29002697 = 21752023) B21752023
theorem B19335131 : Blo 2011435 19335131 := bstep (se 1 (by rfl) ⟨14501348, by rfl⟩ : syracuseStep 19335131 = 29002697) B29002697
theorem B12890087 : Blo 2011435 12890087 := bstep (se 1 (by rfl) ⟨9667565, by rfl⟩ : syracuseStep 12890087 = 19335131) B19335131
theorem B8593391 : Blo 2011435 8593391 := bstep (se 1 (by rfl) ⟨6445043, by rfl⟩ : syracuseStep 8593391 = 12890087) B12890087
theorem B5728927 : Blo 2011435 5728927 := bstep (se 1 (by rfl) ⟨4296695, by rfl⟩ : syracuseStep 5728927 = 8593391) B8593391
theorem B7638569 : Blo 2011435 7638569 := bstep (se 2 (by rfl) ⟨2864463, by rfl⟩ : syracuseStep 7638569 = 5728927) B5728927
theorem B5092379 : Blo 2011435 5092379 := bstep (se 1 (by rfl) ⟨3819284, by rfl⟩ : syracuseStep 5092379 = 7638569) B7638569
theorem B3394919 : Blo 2011435 3394919 := bstep (se 1 (by rfl) ⟨2546189, by rfl⟩ : syracuseStep 3394919 = 5092379) B5092379
theorem B2263279 : Blo 2011435 2263279 := bstep (se 1 (by rfl) ⟨1697459, by rfl⟩ : syracuseStep 2263279 = 3394919) B3394919
theorem B3017705 : Blo 2011435 3017705 := bstep (se 2 (by rfl) ⟨1131639, by rfl⟩ : syracuseStep 3017705 = 2263279) B2263279
theorem B2011803 : Blo 2011435 2011803 := bstep (se 1 (by rfl) ⟨1508852, by rfl⟩ : syracuseStep 2011803 = 3017705) B3017705
theorem B5232293 : Blo 2011435 5232293 := bbase (se 4 (by rfl) ⟨490527, by rfl⟩ : syracuseStep 5232293 = 981055) (by norm_num)
theorem B3488195 : Blo 2011435 3488195 := bstep (se 1 (by rfl) ⟨2616146, by rfl⟩ : syracuseStep 3488195 = 5232293) B5232293
theorem B9301853 : Blo 2011435 9301853 := bstep (se 3 (by rfl) ⟨1744097, by rfl⟩ : syracuseStep 9301853 = 3488195) B3488195
theorem B6201235 : Blo 2011435 6201235 := bstep (se 1 (by rfl) ⟨4650926, by rfl⟩ : syracuseStep 6201235 = 9301853) B9301853
theorem B8268313 : Blo 2011435 8268313 := bstep (se 2 (by rfl) ⟨3100617, by rfl⟩ : syracuseStep 8268313 = 6201235) B6201235
theorem B11024417 : Blo 2011435 11024417 := bstep (se 2 (by rfl) ⟨4134156, by rfl⟩ : syracuseStep 11024417 = 8268313) B8268313
theorem B29398445 : Blo 2011435 29398445 := bstep (se 3 (by rfl) ⟨5512208, by rfl⟩ : syracuseStep 29398445 = 11024417) B11024417
theorem B19598963 : Blo 2011435 19598963 := bstep (se 1 (by rfl) ⟨14699222, by rfl⟩ : syracuseStep 19598963 = 29398445) B29398445
theorem B52263901 : Blo 2011435 52263901 := bstep (se 3 (by rfl) ⟨9799481, by rfl⟩ : syracuseStep 52263901 = 19598963) B19598963
theorem B69685201 : Blo 2011435 69685201 := bstep (se 2 (by rfl) ⟨26131950, by rfl⟩ : syracuseStep 69685201 = 52263901) B52263901
theorem B371654405 : Blo 2011435 371654405 := bstep (se 4 (by rfl) ⟨34842600, by rfl⟩ : syracuseStep 371654405 = 69685201) B69685201
theorem B247769603 : Blo 2011435 247769603 := bstep (se 1 (by rfl) ⟨185827202, by rfl⟩ : syracuseStep 247769603 = 371654405) B371654405
theorem B165179735 : Blo 2011435 165179735 := bstep (se 1 (by rfl) ⟨123884801, by rfl⟩ : syracuseStep 165179735 = 247769603) B247769603
theorem B110119823 : Blo 2011435 110119823 := bstep (se 1 (by rfl) ⟨82589867, by rfl⟩ : syracuseStep 110119823 = 165179735) B165179735
theorem B73413215 : Blo 2011435 73413215 := bstep (se 1 (by rfl) ⟨55059911, by rfl⟩ : syracuseStep 73413215 = 110119823) B110119823
theorem B48942143 : Blo 2011435 48942143 := bstep (se 1 (by rfl) ⟨36706607, by rfl⟩ : syracuseStep 48942143 = 73413215) B73413215
theorem B32628095 : Blo 2011435 32628095 := bstep (se 1 (by rfl) ⟨24471071, by rfl⟩ : syracuseStep 32628095 = 48942143) B48942143
theorem B21752063 : Blo 2011435 21752063 := bstep (se 1 (by rfl) ⟨16314047, by rfl⟩ : syracuseStep 21752063 = 32628095) B32628095
theorem B14501375 : Blo 2011435 14501375 := bstep (se 1 (by rfl) ⟨10876031, by rfl⟩ : syracuseStep 14501375 = 21752063) B21752063
theorem B9667583 : Blo 2011435 9667583 := bstep (se 1 (by rfl) ⟨7250687, by rfl⟩ : syracuseStep 9667583 = 14501375) B14501375
theorem B6445055 : Blo 2011435 6445055 := bstep (se 1 (by rfl) ⟨4833791, by rfl⟩ : syracuseStep 6445055 = 9667583) B9667583
theorem B17186813 : Blo 2011435 17186813 := bstep (se 3 (by rfl) ⟨3222527, by rfl⟩ : syracuseStep 17186813 = 6445055) B6445055
theorem B11457875 : Blo 2011435 11457875 := bstep (se 1 (by rfl) ⟨8593406, by rfl⟩ : syracuseStep 11457875 = 17186813) B17186813
theorem B7638583 : Blo 2011435 7638583 := bstep (se 1 (by rfl) ⟨5728937, by rfl⟩ : syracuseStep 7638583 = 11457875) B11457875
theorem B10184777 : Blo 2011435 10184777 := bstep (se 2 (by rfl) ⟨3819291, by rfl⟩ : syracuseStep 10184777 = 7638583) B7638583
theorem B6789851 : Blo 2011435 6789851 := bstep (se 1 (by rfl) ⟨5092388, by rfl⟩ : syracuseStep 6789851 = 10184777) B10184777
theorem B4526567 : Blo 2011435 4526567 := bstep (se 1 (by rfl) ⟨3394925, by rfl⟩ : syracuseStep 4526567 = 6789851) B6789851
theorem B3017711 : Blo 2011435 3017711 := bstep (se 1 (by rfl) ⟨2263283, by rfl⟩ : syracuseStep 3017711 = 4526567) B4526567
theorem B2011807 : Blo 2011435 2011807 := bstep (se 1 (by rfl) ⟨1508855, by rfl⟩ : syracuseStep 2011807 = 3017711) B3017711
theorem B3017717 : Blo 2011435 3017717 := bbase (se 5 (by rfl) ⟨141455, by rfl⟩ : syracuseStep 3017717 = 282911) (by norm_num)
theorem B2011811 : Blo 2011435 2011811 := bstep (se 1 (by rfl) ⟨1508858, by rfl⟩ : syracuseStep 2011811 = 3017717) B3017717
theorem B3222541 : Blo 2011435 3222541 := bbase (se 3 (by rfl) ⟨604226, by rfl⟩ : syracuseStep 3222541 = 1208453) (by norm_num)
theorem B4296721 : Blo 2011435 4296721 := bstep (se 2 (by rfl) ⟨1611270, by rfl⟩ : syracuseStep 4296721 = 3222541) B3222541
theorem B5728961 : Blo 2011435 5728961 := bstep (se 2 (by rfl) ⟨2148360, by rfl⟩ : syracuseStep 5728961 = 4296721) B4296721
theorem B3819307 : Blo 2011435 3819307 := bstep (se 1 (by rfl) ⟨2864480, by rfl⟩ : syracuseStep 3819307 = 5728961) B5728961
theorem B5092409 : Blo 2011435 5092409 := bstep (se 2 (by rfl) ⟨1909653, by rfl⟩ : syracuseStep 5092409 = 3819307) B3819307
theorem B3394939 : Blo 2011435 3394939 := bstep (se 1 (by rfl) ⟨2546204, by rfl⟩ : syracuseStep 3394939 = 5092409) B5092409
theorem B4526585 : Blo 2011435 4526585 := bstep (se 2 (by rfl) ⟨1697469, by rfl⟩ : syracuseStep 4526585 = 3394939) B3394939
theorem B3017723 : Blo 2011435 3017723 := bstep (se 1 (by rfl) ⟨2263292, by rfl⟩ : syracuseStep 3017723 = 4526585) B4526585
theorem B2011815 : Blo 2011435 2011815 := bstep (se 1 (by rfl) ⟨1508861, by rfl⟩ : syracuseStep 2011815 = 3017723) B3017723
theorem B2263297 : Blo 2011435 2263297 := bbase (se 2 (by rfl) ⟨848736, by rfl⟩ : syracuseStep 2263297 = 1697473) (by norm_num)
theorem B3017729 : Blo 2011435 3017729 := bstep (se 2 (by rfl) ⟨1131648, by rfl⟩ : syracuseStep 3017729 = 2263297) B2263297
theorem B2011819 : Blo 2011435 2011819 := bstep (se 1 (by rfl) ⟨1508864, by rfl⟩ : syracuseStep 2011819 = 3017729) B3017729
theorem B5092429 : Blo 2011435 5092429 := bbase (se 3 (by rfl) ⟨954830, by rfl⟩ : syracuseStep 5092429 = 1909661) (by norm_num)
theorem B6789905 : Blo 2011435 6789905 := bstep (se 2 (by rfl) ⟨2546214, by rfl⟩ : syracuseStep 6789905 = 5092429) B5092429
theorem B4526603 : Blo 2011435 4526603 := bstep (se 1 (by rfl) ⟨3394952, by rfl⟩ : syracuseStep 4526603 = 6789905) B6789905
theorem B3017735 : Blo 2011435 3017735 := bstep (se 1 (by rfl) ⟨2263301, by rfl⟩ : syracuseStep 3017735 = 4526603) B4526603
theorem B2011823 : Blo 2011435 2011823 := bstep (se 1 (by rfl) ⟨1508867, by rfl⟩ : syracuseStep 2011823 = 3017735) B3017735
theorem B3017741 : Blo 2011435 3017741 := bbase (se 3 (by rfl) ⟨565826, by rfl⟩ : syracuseStep 3017741 = 1131653) (by norm_num)
theorem B2011827 : Blo 2011435 2011827 := bstep (se 1 (by rfl) ⟨1508870, by rfl⟩ : syracuseStep 2011827 = 3017741) B3017741
theorem B4526621 : Blo 2011435 4526621 := bbase (se 3 (by rfl) ⟨848741, by rfl⟩ : syracuseStep 4526621 = 1697483) (by norm_num)
theorem B3017747 : Blo 2011435 3017747 := bstep (se 1 (by rfl) ⟨2263310, by rfl⟩ : syracuseStep 3017747 = 4526621) B4526621
theorem B2011831 : Blo 2011435 2011831 := bstep (se 1 (by rfl) ⟨1508873, by rfl⟩ : syracuseStep 2011831 = 3017747) B3017747
theorem B3394973 : Blo 2011435 3394973 := bbase (se 3 (by rfl) ⟨636557, by rfl⟩ : syracuseStep 3394973 = 1273115) (by norm_num)
theorem B2263315 : Blo 2011435 2263315 := bstep (se 1 (by rfl) ⟨1697486, by rfl⟩ : syracuseStep 2263315 = 3394973) B3394973
theorem B3017753 : Blo 2011435 3017753 := bstep (se 2 (by rfl) ⟨1131657, by rfl⟩ : syracuseStep 3017753 = 2263315) B2263315
theorem B2011835 : Blo 2011435 2011835 := bstep (se 1 (by rfl) ⟨1508876, by rfl⟩ : syracuseStep 2011835 = 3017753) B3017753
theorem B3058933 : Blo 2011435 3058933 := bbase (se 5 (by rfl) ⟨143387, by rfl⟩ : syracuseStep 3058933 = 286775) (by norm_num)
theorem B4078577 : Blo 2011435 4078577 := bstep (se 2 (by rfl) ⟨1529466, by rfl⟩ : syracuseStep 4078577 = 3058933) B3058933
theorem B2719051 : Blo 2011435 2719051 := bstep (se 1 (by rfl) ⟨2039288, by rfl⟩ : syracuseStep 2719051 = 4078577) B4078577
theorem B14501605 : Blo 2011435 14501605 := bstep (se 4 (by rfl) ⟨1359525, by rfl⟩ : syracuseStep 14501605 = 2719051) B2719051
theorem B19335473 : Blo 2011435 19335473 := bstep (se 2 (by rfl) ⟨7250802, by rfl⟩ : syracuseStep 19335473 = 14501605) B14501605
theorem B12890315 : Blo 2011435 12890315 := bstep (se 1 (by rfl) ⟨9667736, by rfl⟩ : syracuseStep 12890315 = 19335473) B19335473
theorem B8593543 : Blo 2011435 8593543 := bstep (se 1 (by rfl) ⟨6445157, by rfl⟩ : syracuseStep 8593543 = 12890315) B12890315
theorem B11458057 : Blo 2011435 11458057 := bstep (se 2 (by rfl) ⟨4296771, by rfl⟩ : syracuseStep 11458057 = 8593543) B8593543
theorem B15277409 : Blo 2011435 15277409 := bstep (se 2 (by rfl) ⟨5729028, by rfl⟩ : syracuseStep 15277409 = 11458057) B11458057
theorem B10184939 : Blo 2011435 10184939 := bstep (se 1 (by rfl) ⟨7638704, by rfl⟩ : syracuseStep 10184939 = 15277409) B15277409
theorem B6789959 : Blo 2011435 6789959 := bstep (se 1 (by rfl) ⟨5092469, by rfl⟩ : syracuseStep 6789959 = 10184939) B10184939
theorem B4526639 : Blo 2011435 4526639 := bstep (se 1 (by rfl) ⟨3394979, by rfl⟩ : syracuseStep 4526639 = 6789959) B6789959
theorem B3017759 : Blo 2011435 3017759 := bstep (se 1 (by rfl) ⟨2263319, by rfl⟩ : syracuseStep 3017759 = 4526639) B4526639
theorem B2011839 : Blo 2011435 2011839 := bstep (se 1 (by rfl) ⟨1508879, by rfl⟩ : syracuseStep 2011839 = 3017759) B3017759
theorem B3017765 : Blo 2011435 3017765 := bbase (se 4 (by rfl) ⟨282915, by rfl⟩ : syracuseStep 3017765 = 565831) (by norm_num)
theorem B2011843 : Blo 2011435 2011843 := bstep (se 1 (by rfl) ⟨1508882, by rfl⟩ : syracuseStep 2011843 = 3017765) B3017765
theorem B2546245 : Blo 2011435 2546245 := bbase (se 4 (by rfl) ⟨238710, by rfl⟩ : syracuseStep 2546245 = 477421) (by norm_num)
theorem B3394993 : Blo 2011435 3394993 := bstep (se 2 (by rfl) ⟨1273122, by rfl⟩ : syracuseStep 3394993 = 2546245) B2546245
theorem B4526657 : Blo 2011435 4526657 := bstep (se 2 (by rfl) ⟨1697496, by rfl⟩ : syracuseStep 4526657 = 3394993) B3394993
theorem B3017771 : Blo 2011435 3017771 := bstep (se 1 (by rfl) ⟨2263328, by rfl⟩ : syracuseStep 3017771 = 4526657) B4526657
theorem B2011847 : Blo 2011435 2011847 := bstep (se 1 (by rfl) ⟨1508885, by rfl⟩ : syracuseStep 2011847 = 3017771) B3017771
theorem B2263333 : Blo 2011435 2263333 := bbase (se 4 (by rfl) ⟨212187, by rfl⟩ : syracuseStep 2263333 = 424375) (by norm_num)
theorem B3017777 : Blo 2011435 3017777 := bstep (se 2 (by rfl) ⟨1131666, by rfl⟩ : syracuseStep 3017777 = 2263333) B2263333
theorem B2011851 : Blo 2011435 2011851 := bstep (se 1 (by rfl) ⟨1508888, by rfl⟩ : syracuseStep 2011851 = 3017777) B3017777
theorem B3222605 : Blo 2011435 3222605 := bbase (se 3 (by rfl) ⟨604238, by rfl⟩ : syracuseStep 3222605 = 1208477) (by norm_num)
theorem B8593613 : Blo 2011435 8593613 := bstep (se 3 (by rfl) ⟨1611302, by rfl⟩ : syracuseStep 8593613 = 3222605) B3222605
theorem B5729075 : Blo 2011435 5729075 := bstep (se 1 (by rfl) ⟨4296806, by rfl⟩ : syracuseStep 5729075 = 8593613) B8593613
theorem B3819383 : Blo 2011435 3819383 := bstep (se 1 (by rfl) ⟨2864537, by rfl⟩ : syracuseStep 3819383 = 5729075) B5729075
theorem B2546255 : Blo 2011435 2546255 := bstep (se 1 (by rfl) ⟨1909691, by rfl⟩ : syracuseStep 2546255 = 3819383) B3819383
theorem B6790013 : Blo 2011435 6790013 := bstep (se 3 (by rfl) ⟨1273127, by rfl⟩ : syracuseStep 6790013 = 2546255) B2546255
theorem B4526675 : Blo 2011435 4526675 := bstep (se 1 (by rfl) ⟨3395006, by rfl⟩ : syracuseStep 4526675 = 6790013) B6790013
theorem B3017783 : Blo 2011435 3017783 := bstep (se 1 (by rfl) ⟨2263337, by rfl⟩ : syracuseStep 3017783 = 4526675) B4526675
theorem B2011855 : Blo 2011435 2011855 := bstep (se 1 (by rfl) ⟨1508891, by rfl⟩ : syracuseStep 2011855 = 3017783) B3017783
theorem B3017789 : Blo 2011435 3017789 := bbase (se 3 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 3017789 = 1131671) (by norm_num)
theorem B2011859 : Blo 2011435 2011859 := bstep (se 1 (by rfl) ⟨1508894, by rfl⟩ : syracuseStep 2011859 = 3017789) B3017789
theorem B4526693 : Blo 2011435 4526693 := bbase (se 4 (by rfl) ⟨424377, by rfl⟩ : syracuseStep 4526693 = 848755) (by norm_num)
theorem B3017795 : Blo 2011435 3017795 := bstep (se 1 (by rfl) ⟨2263346, by rfl⟩ : syracuseStep 3017795 = 4526693) B4526693
theorem B2011863 : Blo 2011435 2011863 := bstep (se 1 (by rfl) ⟨1508897, by rfl⟩ : syracuseStep 2011863 = 3017795) B3017795
theorem B5092541 : Blo 2011435 5092541 := bbase (se 3 (by rfl) ⟨954851, by rfl⟩ : syracuseStep 5092541 = 1909703) (by norm_num)
theorem B3395027 : Blo 2011435 3395027 := bstep (se 1 (by rfl) ⟨2546270, by rfl⟩ : syracuseStep 3395027 = 5092541) B5092541
theorem B2263351 : Blo 2011435 2263351 := bstep (se 1 (by rfl) ⟨1697513, by rfl⟩ : syracuseStep 2263351 = 3395027) B3395027
theorem B3017801 : Blo 2011435 3017801 := bstep (se 2 (by rfl) ⟨1131675, by rfl⟩ : syracuseStep 3017801 = 2263351) B2263351
theorem B2011867 : Blo 2011435 2011867 := bstep (se 1 (by rfl) ⟨1508900, by rfl⟩ : syracuseStep 2011867 = 3017801) B3017801
theorem B3819413 : Blo 2011435 3819413 := bbase (se 6 (by rfl) ⟨89517, by rfl⟩ : syracuseStep 3819413 = 179035) (by norm_num)
theorem B10185101 : Blo 2011435 10185101 := bstep (se 3 (by rfl) ⟨1909706, by rfl⟩ : syracuseStep 10185101 = 3819413) B3819413
theorem B6790067 : Blo 2011435 6790067 := bstep (se 1 (by rfl) ⟨5092550, by rfl⟩ : syracuseStep 6790067 = 10185101) B10185101
theorem B4526711 : Blo 2011435 4526711 := bstep (se 1 (by rfl) ⟨3395033, by rfl⟩ : syracuseStep 4526711 = 6790067) B6790067
theorem B3017807 : Blo 2011435 3017807 := bstep (se 1 (by rfl) ⟨2263355, by rfl⟩ : syracuseStep 3017807 = 4526711) B4526711
theorem B2011871 : Blo 2011435 2011871 := bstep (se 1 (by rfl) ⟨1508903, by rfl⟩ : syracuseStep 2011871 = 3017807) B3017807
theorem B3017813 : Blo 2011435 3017813 := bbase (se 8 (by rfl) ⟨17682, by rfl⟩ : syracuseStep 3017813 = 35365) (by norm_num)
theorem B2011875 : Blo 2011435 2011875 := bstep (se 1 (by rfl) ⟨1508906, by rfl⟩ : syracuseStep 2011875 = 3017813) B3017813
theorem B4833965 : Blo 2011435 4833965 := bbase (se 3 (by rfl) ⟨906368, by rfl⟩ : syracuseStep 4833965 = 1812737) (by norm_num)
theorem B12890573 : Blo 2011435 12890573 := bstep (se 3 (by rfl) ⟨2416982, by rfl⟩ : syracuseStep 12890573 = 4833965) B4833965
theorem B8593715 : Blo 2011435 8593715 := bstep (se 1 (by rfl) ⟨6445286, by rfl⟩ : syracuseStep 8593715 = 12890573) B12890573
theorem B5729143 : Blo 2011435 5729143 := bstep (se 1 (by rfl) ⟨4296857, by rfl⟩ : syracuseStep 5729143 = 8593715) B8593715
theorem B7638857 : Blo 2011435 7638857 := bstep (se 2 (by rfl) ⟨2864571, by rfl⟩ : syracuseStep 7638857 = 5729143) B5729143
theorem B5092571 : Blo 2011435 5092571 := bstep (se 1 (by rfl) ⟨3819428, by rfl⟩ : syracuseStep 5092571 = 7638857) B7638857
theorem B3395047 : Blo 2011435 3395047 := bstep (se 1 (by rfl) ⟨2546285, by rfl⟩ : syracuseStep 3395047 = 5092571) B5092571
theorem B4526729 : Blo 2011435 4526729 := bstep (se 2 (by rfl) ⟨1697523, by rfl⟩ : syracuseStep 4526729 = 3395047) B3395047
theorem B3017819 : Blo 2011435 3017819 := bstep (se 1 (by rfl) ⟨2263364, by rfl⟩ : syracuseStep 3017819 = 4526729) B4526729
theorem B2011879 : Blo 2011435 2011879 := bstep (se 1 (by rfl) ⟨1508909, by rfl⟩ : syracuseStep 2011879 = 3017819) B3017819
theorem B2263369 : Blo 2011435 2263369 := bbase (se 2 (by rfl) ⟨848763, by rfl⟩ : syracuseStep 2263369 = 1697527) (by norm_num)
theorem B3017825 : Blo 2011435 3017825 := bstep (se 2 (by rfl) ⟨1131684, by rfl⟩ : syracuseStep 3017825 = 2263369) B2263369
theorem B2011883 : Blo 2011435 2011883 := bstep (se 1 (by rfl) ⟨1508912, by rfl⟩ : syracuseStep 2011883 = 3017825) B3017825
theorem B55813333 : Blo 2011435 55813333 := bbase (se 7 (by rfl) ⟨654062, by rfl⟩ : syracuseStep 55813333 = 1308125) (by norm_num)
theorem B74417777 : Blo 2011435 74417777 := bstep (se 2 (by rfl) ⟨27906666, by rfl⟩ : syracuseStep 74417777 = 55813333) B55813333
theorem B49611851 : Blo 2011435 49611851 := bstep (se 1 (by rfl) ⟨37208888, by rfl⟩ : syracuseStep 49611851 = 74417777) B74417777
theorem B33074567 : Blo 2011435 33074567 := bstep (se 1 (by rfl) ⟨24805925, by rfl⟩ : syracuseStep 33074567 = 49611851) B49611851
theorem B22049711 : Blo 2011435 22049711 := bstep (se 1 (by rfl) ⟨16537283, by rfl⟩ : syracuseStep 22049711 = 33074567) B33074567
theorem B14699807 : Blo 2011435 14699807 := bstep (se 1 (by rfl) ⟨11024855, by rfl⟩ : syracuseStep 14699807 = 22049711) B22049711
theorem B9799871 : Blo 2011435 9799871 := bstep (se 1 (by rfl) ⟨7349903, by rfl⟩ : syracuseStep 9799871 = 14699807) B14699807
theorem B26132989 : Blo 2011435 26132989 := bstep (se 3 (by rfl) ⟨4899935, by rfl⟩ : syracuseStep 26132989 = 9799871) B9799871
theorem B34843985 : Blo 2011435 34843985 := bstep (se 2 (by rfl) ⟨13066494, by rfl⟩ : syracuseStep 34843985 = 26132989) B26132989
theorem B23229323 : Blo 2011435 23229323 := bstep (se 1 (by rfl) ⟨17421992, by rfl⟩ : syracuseStep 23229323 = 34843985) B34843985
theorem B247779445 : Blo 2011435 247779445 := bstep (se 5 (by rfl) ⟨11614661, by rfl⟩ : syracuseStep 247779445 = 23229323) B23229323
theorem B330372593 : Blo 2011435 330372593 := bstep (se 2 (by rfl) ⟨123889722, by rfl⟩ : syracuseStep 330372593 = 247779445) B247779445
theorem B220248395 : Blo 2011435 220248395 := bstep (se 1 (by rfl) ⟨165186296, by rfl⟩ : syracuseStep 220248395 = 330372593) B330372593
theorem B146832263 : Blo 2011435 146832263 := bstep (se 1 (by rfl) ⟨110124197, by rfl⟩ : syracuseStep 146832263 = 220248395) B220248395
theorem B97888175 : Blo 2011435 97888175 := bstep (se 1 (by rfl) ⟨73416131, by rfl⟩ : syracuseStep 97888175 = 146832263) B146832263
theorem B65258783 : Blo 2011435 65258783 := bstep (se 1 (by rfl) ⟨48944087, by rfl⟩ : syracuseStep 65258783 = 97888175) B97888175
theorem B43505855 : Blo 2011435 43505855 := bstep (se 1 (by rfl) ⟨32629391, by rfl⟩ : syracuseStep 43505855 = 65258783) B65258783
theorem B29003903 : Blo 2011435 29003903 := bstep (se 1 (by rfl) ⟨21752927, by rfl⟩ : syracuseStep 29003903 = 43505855) B43505855
theorem B19335935 : Blo 2011435 19335935 := bstep (se 1 (by rfl) ⟨14501951, by rfl⟩ : syracuseStep 19335935 = 29003903) B29003903
theorem B12890623 : Blo 2011435 12890623 := bstep (se 1 (by rfl) ⟨9667967, by rfl⟩ : syracuseStep 12890623 = 19335935) B19335935
theorem B17187497 : Blo 2011435 17187497 := bstep (se 2 (by rfl) ⟨6445311, by rfl⟩ : syracuseStep 17187497 = 12890623) B12890623
theorem B11458331 : Blo 2011435 11458331 := bstep (se 1 (by rfl) ⟨8593748, by rfl⟩ : syracuseStep 11458331 = 17187497) B17187497
theorem B7638887 : Blo 2011435 7638887 := bstep (se 1 (by rfl) ⟨5729165, by rfl⟩ : syracuseStep 7638887 = 11458331) B11458331
theorem B5092591 : Blo 2011435 5092591 := bstep (se 1 (by rfl) ⟨3819443, by rfl⟩ : syracuseStep 5092591 = 7638887) B7638887
theorem B6790121 : Blo 2011435 6790121 := bstep (se 2 (by rfl) ⟨2546295, by rfl⟩ : syracuseStep 6790121 = 5092591) B5092591
theorem B4526747 : Blo 2011435 4526747 := bstep (se 1 (by rfl) ⟨3395060, by rfl⟩ : syracuseStep 4526747 = 6790121) B6790121
theorem B3017831 : Blo 2011435 3017831 := bstep (se 1 (by rfl) ⟨2263373, by rfl⟩ : syracuseStep 3017831 = 4526747) B4526747
theorem B2011887 : Blo 2011435 2011887 := bstep (se 1 (by rfl) ⟨1508915, by rfl⟩ : syracuseStep 2011887 = 3017831) B3017831
theorem B3017837 : Blo 2011435 3017837 := bbase (se 3 (by rfl) ⟨565844, by rfl⟩ : syracuseStep 3017837 = 1131689) (by norm_num)
theorem B2011891 : Blo 2011435 2011891 := bstep (se 1 (by rfl) ⟨1508918, by rfl⟩ : syracuseStep 2011891 = 3017837) B3017837
theorem B4526765 : Blo 2011435 4526765 := bbase (se 3 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 4526765 = 1697537) (by norm_num)
theorem B3017843 : Blo 2011435 3017843 := bstep (se 1 (by rfl) ⟨2263382, by rfl⟩ : syracuseStep 3017843 = 4526765) B4526765
theorem B2011895 : Blo 2011435 2011895 := bstep (se 1 (by rfl) ⟨1508921, by rfl⟩ : syracuseStep 2011895 = 3017843) B3017843
theorem B4296901 : Blo 2011435 4296901 := bbase (se 4 (by rfl) ⟨402834, by rfl⟩ : syracuseStep 4296901 = 805669) (by norm_num)
theorem B5729201 : Blo 2011435 5729201 := bstep (se 2 (by rfl) ⟨2148450, by rfl⟩ : syracuseStep 5729201 = 4296901) B4296901
theorem B3819467 : Blo 2011435 3819467 := bstep (se 1 (by rfl) ⟨2864600, by rfl⟩ : syracuseStep 3819467 = 5729201) B5729201
theorem B2546311 : Blo 2011435 2546311 := bstep (se 1 (by rfl) ⟨1909733, by rfl⟩ : syracuseStep 2546311 = 3819467) B3819467
theorem B3395081 : Blo 2011435 3395081 := bstep (se 2 (by rfl) ⟨1273155, by rfl⟩ : syracuseStep 3395081 = 2546311) B2546311
theorem B2263387 : Blo 2011435 2263387 := bstep (se 1 (by rfl) ⟨1697540, by rfl⟩ : syracuseStep 2263387 = 3395081) B3395081
theorem B3017849 : Blo 2011435 3017849 := bstep (se 2 (by rfl) ⟨1131693, by rfl⟩ : syracuseStep 3017849 = 2263387) B2263387
theorem B2011899 : Blo 2011435 2011899 := bstep (se 1 (by rfl) ⟨1508924, by rfl⟩ : syracuseStep 2011899 = 3017849) B3017849
theorem B2039353 : Blo 2011435 2039353 := bbase (se 2 (by rfl) ⟨764757, by rfl⟩ : syracuseStep 2039353 = 1529515) (by norm_num)
theorem B43506197 : Blo 2011435 43506197 := bstep (se 6 (by rfl) ⟨1019676, by rfl⟩ : syracuseStep 43506197 = 2039353) B2039353
theorem B29004131 : Blo 2011435 29004131 := bstep (se 1 (by rfl) ⟨21753098, by rfl⟩ : syracuseStep 29004131 = 43506197) B43506197
theorem B19336087 : Blo 2011435 19336087 := bstep (se 1 (by rfl) ⟨14502065, by rfl⟩ : syracuseStep 19336087 = 29004131) B29004131
theorem B25781449 : Blo 2011435 25781449 := bstep (se 2 (by rfl) ⟨9668043, by rfl⟩ : syracuseStep 25781449 = 19336087) B19336087
theorem B34375265 : Blo 2011435 34375265 := bstep (se 2 (by rfl) ⟨12890724, by rfl⟩ : syracuseStep 34375265 = 25781449) B25781449
theorem B22916843 : Blo 2011435 22916843 := bstep (se 1 (by rfl) ⟨17187632, by rfl⟩ : syracuseStep 22916843 = 34375265) B34375265
theorem B15277895 : Blo 2011435 15277895 := bstep (se 1 (by rfl) ⟨11458421, by rfl⟩ : syracuseStep 15277895 = 22916843) B22916843
theorem B10185263 : Blo 2011435 10185263 := bstep (se 1 (by rfl) ⟨7638947, by rfl⟩ : syracuseStep 10185263 = 15277895) B15277895
theorem B6790175 : Blo 2011435 6790175 := bstep (se 1 (by rfl) ⟨5092631, by rfl⟩ : syracuseStep 6790175 = 10185263) B10185263
theorem B4526783 : Blo 2011435 4526783 := bstep (se 1 (by rfl) ⟨3395087, by rfl⟩ : syracuseStep 4526783 = 6790175) B6790175
theorem B3017855 : Blo 2011435 3017855 := bstep (se 1 (by rfl) ⟨2263391, by rfl⟩ : syracuseStep 3017855 = 4526783) B4526783
theorem B2011903 : Blo 2011435 2011903 := bstep (se 1 (by rfl) ⟨1508927, by rfl⟩ : syracuseStep 2011903 = 3017855) B3017855
theorem B3017861 : Blo 2011435 3017861 := bbase (se 4 (by rfl) ⟨282924, by rfl⟩ : syracuseStep 3017861 = 565849) (by norm_num)
theorem B2011907 : Blo 2011435 2011907 := bstep (se 1 (by rfl) ⟨1508930, by rfl⟩ : syracuseStep 2011907 = 3017861) B3017861
theorem B3395101 : Blo 2011435 3395101 := bbase (se 3 (by rfl) ⟨636581, by rfl⟩ : syracuseStep 3395101 = 1273163) (by norm_num)
theorem B4526801 : Blo 2011435 4526801 := bstep (se 2 (by rfl) ⟨1697550, by rfl⟩ : syracuseStep 4526801 = 3395101) B3395101
theorem B3017867 : Blo 2011435 3017867 := bstep (se 1 (by rfl) ⟨2263400, by rfl⟩ : syracuseStep 3017867 = 4526801) B4526801
theorem B2011911 : Blo 2011435 2011911 := bstep (se 1 (by rfl) ⟨1508933, by rfl⟩ : syracuseStep 2011911 = 3017867) B3017867
theorem B2263405 : Blo 2011435 2263405 := bbase (se 3 (by rfl) ⟨424388, by rfl⟩ : syracuseStep 2263405 = 848777) (by norm_num)
theorem B3017873 : Blo 2011435 3017873 := bstep (se 2 (by rfl) ⟨1131702, by rfl⟩ : syracuseStep 3017873 = 2263405) B2263405
theorem B2011915 : Blo 2011435 2011915 := bstep (se 1 (by rfl) ⟨1508936, by rfl⟩ : syracuseStep 2011915 = 3017873) B3017873
theorem B6790229 : Blo 2011435 6790229 := bbase (se 8 (by rfl) ⟨39786, by rfl⟩ : syracuseStep 6790229 = 79573) (by norm_num)
theorem B4526819 : Blo 2011435 4526819 := bstep (se 1 (by rfl) ⟨3395114, by rfl⟩ : syracuseStep 4526819 = 6790229) B6790229
theorem B3017879 : Blo 2011435 3017879 := bstep (se 1 (by rfl) ⟨2263409, by rfl⟩ : syracuseStep 3017879 = 4526819) B4526819
theorem B2011919 : Blo 2011435 2011919 := bstep (se 1 (by rfl) ⟨1508939, by rfl⟩ : syracuseStep 2011919 = 3017879) B3017879
theorem B3017885 : Blo 2011435 3017885 := bbase (se 3 (by rfl) ⟨565853, by rfl⟩ : syracuseStep 3017885 = 1131707) (by norm_num)
theorem B2011923 : Blo 2011435 2011923 := bstep (se 1 (by rfl) ⟨1508942, by rfl⟩ : syracuseStep 2011923 = 3017885) B3017885
theorem B4526837 : Blo 2011435 4526837 := bbase (se 5 (by rfl) ⟨212195, by rfl⟩ : syracuseStep 4526837 = 424391) (by norm_num)
theorem B3017891 : Blo 2011435 3017891 := bstep (se 1 (by rfl) ⟨2263418, by rfl⟩ : syracuseStep 3017891 = 4526837) B4526837
theorem B2011927 : Blo 2011435 2011927 := bstep (se 1 (by rfl) ⟨1508945, by rfl⟩ : syracuseStep 2011927 = 3017891) B3017891
theorem B2417045 : Blo 2011435 2417045 := bbase (se 6 (by rfl) ⟨56649, by rfl⟩ : syracuseStep 2417045 = 113299) (by norm_num)
theorem B25781813 : Blo 2011435 25781813 := bstep (se 5 (by rfl) ⟨1208522, by rfl⟩ : syracuseStep 25781813 = 2417045) B2417045
theorem B17187875 : Blo 2011435 17187875 := bstep (se 1 (by rfl) ⟨12890906, by rfl⟩ : syracuseStep 17187875 = 25781813) B25781813
theorem B11458583 : Blo 2011435 11458583 := bstep (se 1 (by rfl) ⟨8593937, by rfl⟩ : syracuseStep 11458583 = 17187875) B17187875
theorem B7639055 : Blo 2011435 7639055 := bstep (se 1 (by rfl) ⟨5729291, by rfl⟩ : syracuseStep 7639055 = 11458583) B11458583
theorem B5092703 : Blo 2011435 5092703 := bstep (se 1 (by rfl) ⟨3819527, by rfl⟩ : syracuseStep 5092703 = 7639055) B7639055
theorem B3395135 : Blo 2011435 3395135 := bstep (se 1 (by rfl) ⟨2546351, by rfl⟩ : syracuseStep 3395135 = 5092703) B5092703
theorem B2263423 : Blo 2011435 2263423 := bstep (se 1 (by rfl) ⟨1697567, by rfl⟩ : syracuseStep 2263423 = 3395135) B3395135
theorem B3017897 : Blo 2011435 3017897 := bstep (se 2 (by rfl) ⟨1131711, by rfl⟩ : syracuseStep 3017897 = 2263423) B2263423
theorem B2011931 : Blo 2011435 2011931 := bstep (se 1 (by rfl) ⟨1508948, by rfl⟩ : syracuseStep 2011931 = 3017897) B3017897
theorem B3222733 : Blo 2011435 3222733 := bbase (se 3 (by rfl) ⟨604262, by rfl⟩ : syracuseStep 3222733 = 1208525) (by norm_num)
theorem B4296977 : Blo 2011435 4296977 := bstep (se 2 (by rfl) ⟨1611366, by rfl⟩ : syracuseStep 4296977 = 3222733) B3222733
theorem B2864651 : Blo 2011435 2864651 := bstep (se 1 (by rfl) ⟨2148488, by rfl⟩ : syracuseStep 2864651 = 4296977) B4296977
theorem B7639069 : Blo 2011435 7639069 := bstep (se 3 (by rfl) ⟨1432325, by rfl⟩ : syracuseStep 7639069 = 2864651) B2864651
theorem B10185425 : Blo 2011435 10185425 := bstep (se 2 (by rfl) ⟨3819534, by rfl⟩ : syracuseStep 10185425 = 7639069) B7639069
theorem B6790283 : Blo 2011435 6790283 := bstep (se 1 (by rfl) ⟨5092712, by rfl⟩ : syracuseStep 6790283 = 10185425) B10185425
theorem B4526855 : Blo 2011435 4526855 := bstep (se 1 (by rfl) ⟨3395141, by rfl⟩ : syracuseStep 4526855 = 6790283) B6790283
theorem B3017903 : Blo 2011435 3017903 := bstep (se 1 (by rfl) ⟨2263427, by rfl⟩ : syracuseStep 3017903 = 4526855) B4526855
theorem B2011935 : Blo 2011435 2011935 := bstep (se 1 (by rfl) ⟨1508951, by rfl⟩ : syracuseStep 2011935 = 3017903) B3017903
theorem B3017909 : Blo 2011435 3017909 := bbase (se 5 (by rfl) ⟨141464, by rfl⟩ : syracuseStep 3017909 = 282929) (by norm_num)
theorem B2011939 : Blo 2011435 2011939 := bstep (se 1 (by rfl) ⟨1508954, by rfl⟩ : syracuseStep 2011939 = 3017909) B3017909
theorem B5092733 : Blo 2011435 5092733 := bbase (se 3 (by rfl) ⟨954887, by rfl⟩ : syracuseStep 5092733 = 1909775) (by norm_num)
theorem B3395155 : Blo 2011435 3395155 := bstep (se 1 (by rfl) ⟨2546366, by rfl⟩ : syracuseStep 3395155 = 5092733) B5092733
theorem B4526873 : Blo 2011435 4526873 := bstep (se 2 (by rfl) ⟨1697577, by rfl⟩ : syracuseStep 4526873 = 3395155) B3395155
theorem B3017915 : Blo 2011435 3017915 := bstep (se 1 (by rfl) ⟨2263436, by rfl⟩ : syracuseStep 3017915 = 4526873) B4526873
theorem B2011943 : Blo 2011435 2011943 := bstep (se 1 (by rfl) ⟨1508957, by rfl⟩ : syracuseStep 2011943 = 3017915) B3017915
theorem B2263441 : Blo 2011435 2263441 := bbase (se 2 (by rfl) ⟨848790, by rfl⟩ : syracuseStep 2263441 = 1697581) (by norm_num)
theorem B3017921 : Blo 2011435 3017921 := bstep (se 2 (by rfl) ⟨1131720, by rfl⟩ : syracuseStep 3017921 = 2263441) B2263441
theorem B2011947 : Blo 2011435 2011947 := bstep (se 1 (by rfl) ⟨1508960, by rfl⟩ : syracuseStep 2011947 = 3017921) B3017921
theorem B3819565 : Blo 2011435 3819565 := bbase (se 3 (by rfl) ⟨716168, by rfl⟩ : syracuseStep 3819565 = 1432337) (by norm_num)
theorem B5092753 : Blo 2011435 5092753 := bstep (se 2 (by rfl) ⟨1909782, by rfl⟩ : syracuseStep 5092753 = 3819565) B3819565
theorem B6790337 : Blo 2011435 6790337 := bstep (se 2 (by rfl) ⟨2546376, by rfl⟩ : syracuseStep 6790337 = 5092753) B5092753
theorem B4526891 : Blo 2011435 4526891 := bstep (se 1 (by rfl) ⟨3395168, by rfl⟩ : syracuseStep 4526891 = 6790337) B6790337
theorem B3017927 : Blo 2011435 3017927 := bstep (se 1 (by rfl) ⟨2263445, by rfl⟩ : syracuseStep 3017927 = 4526891) B4526891
theorem B2011951 : Blo 2011435 2011951 := bstep (se 1 (by rfl) ⟨1508963, by rfl⟩ : syracuseStep 2011951 = 3017927) B3017927
theorem B3017933 : Blo 2011435 3017933 := bbase (se 3 (by rfl) ⟨565862, by rfl⟩ : syracuseStep 3017933 = 1131725) (by norm_num)
theorem B2011955 : Blo 2011435 2011955 := bstep (se 1 (by rfl) ⟨1508966, by rfl⟩ : syracuseStep 2011955 = 3017933) B3017933
theorem B4526909 : Blo 2011435 4526909 := bbase (se 3 (by rfl) ⟨848795, by rfl⟩ : syracuseStep 4526909 = 1697591) (by norm_num)
theorem B3017939 : Blo 2011435 3017939 := bstep (se 1 (by rfl) ⟨2263454, by rfl⟩ : syracuseStep 3017939 = 4526909) B4526909
theorem B2011959 : Blo 2011435 2011959 := bstep (se 1 (by rfl) ⟨1508969, by rfl⟩ : syracuseStep 2011959 = 3017939) B3017939
theorem B3395189 : Blo 2011435 3395189 := bbase (se 5 (by rfl) ⟨159149, by rfl⟩ : syracuseStep 3395189 = 318299) (by norm_num)
theorem B2263459 : Blo 2011435 2263459 := bstep (se 1 (by rfl) ⟨1697594, by rfl⟩ : syracuseStep 2263459 = 3395189) B3395189
theorem B3017945 : Blo 2011435 3017945 := bstep (se 2 (by rfl) ⟨1131729, by rfl⟩ : syracuseStep 3017945 = 2263459) B2263459
theorem B2011963 : Blo 2011435 2011963 := bstep (se 1 (by rfl) ⟨1508972, by rfl⟩ : syracuseStep 2011963 = 3017945) B3017945
theorem B4297045 : Blo 2011435 4297045 := bbase (se 10 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 4297045 = 12589) (by norm_num)
theorem B5729393 : Blo 2011435 5729393 := bstep (se 2 (by rfl) ⟨2148522, by rfl⟩ : syracuseStep 5729393 = 4297045) B4297045
theorem B15278381 : Blo 2011435 15278381 := bstep (se 3 (by rfl) ⟨2864696, by rfl⟩ : syracuseStep 15278381 = 5729393) B5729393
theorem B10185587 : Blo 2011435 10185587 := bstep (se 1 (by rfl) ⟨7639190, by rfl⟩ : syracuseStep 10185587 = 15278381) B15278381
theorem B6790391 : Blo 2011435 6790391 := bstep (se 1 (by rfl) ⟨5092793, by rfl⟩ : syracuseStep 6790391 = 10185587) B10185587
theorem B4526927 : Blo 2011435 4526927 := bstep (se 1 (by rfl) ⟨3395195, by rfl⟩ : syracuseStep 4526927 = 6790391) B6790391
theorem B3017951 : Blo 2011435 3017951 := bstep (se 1 (by rfl) ⟨2263463, by rfl⟩ : syracuseStep 3017951 = 4526927) B4526927
theorem B2011967 : Blo 2011435 2011967 := bstep (se 1 (by rfl) ⟨1508975, by rfl⟩ : syracuseStep 2011967 = 3017951) B3017951
theorem B3017957 : Blo 2011435 3017957 := bbase (se 4 (by rfl) ⟨282933, by rfl⟩ : syracuseStep 3017957 = 565867) (by norm_num)
theorem B2011971 : Blo 2011435 2011971 := bstep (se 1 (by rfl) ⟨1508978, by rfl⟩ : syracuseStep 2011971 = 3017957) B3017957
theorem B3441533 : Blo 2011435 3441533 := bbase (se 3 (by rfl) ⟨645287, by rfl⟩ : syracuseStep 3441533 = 1290575) (by norm_num)
theorem B36709685 : Blo 2011435 36709685 := bstep (se 5 (by rfl) ⟨1720766, by rfl⟩ : syracuseStep 36709685 = 3441533) B3441533
theorem B24473123 : Blo 2011435 24473123 := bstep (se 1 (by rfl) ⟨18354842, by rfl⟩ : syracuseStep 24473123 = 36709685) B36709685
theorem B16315415 : Blo 2011435 16315415 := bstep (se 1 (by rfl) ⟨12236561, by rfl⟩ : syracuseStep 16315415 = 24473123) B24473123
theorem B10876943 : Blo 2011435 10876943 := bstep (se 1 (by rfl) ⟨8157707, by rfl⟩ : syracuseStep 10876943 = 16315415) B16315415
theorem B7251295 : Blo 2011435 7251295 := bstep (se 1 (by rfl) ⟨5438471, by rfl⟩ : syracuseStep 7251295 = 10876943) B10876943
theorem B9668393 : Blo 2011435 9668393 := bstep (se 2 (by rfl) ⟨3625647, by rfl⟩ : syracuseStep 9668393 = 7251295) B7251295
theorem B6445595 : Blo 2011435 6445595 := bstep (se 1 (by rfl) ⟨4834196, by rfl⟩ : syracuseStep 6445595 = 9668393) B9668393
theorem B4297063 : Blo 2011435 4297063 := bstep (se 1 (by rfl) ⟨3222797, by rfl⟩ : syracuseStep 4297063 = 6445595) B6445595
theorem B5729417 : Blo 2011435 5729417 := bstep (se 2 (by rfl) ⟨2148531, by rfl⟩ : syracuseStep 5729417 = 4297063) B4297063
theorem B3819611 : Blo 2011435 3819611 := bstep (se 1 (by rfl) ⟨2864708, by rfl⟩ : syracuseStep 3819611 = 5729417) B5729417
theorem B2546407 : Blo 2011435 2546407 := bstep (se 1 (by rfl) ⟨1909805, by rfl⟩ : syracuseStep 2546407 = 3819611) B3819611
theorem B3395209 : Blo 2011435 3395209 := bstep (se 2 (by rfl) ⟨1273203, by rfl⟩ : syracuseStep 3395209 = 2546407) B2546407
theorem B4526945 : Blo 2011435 4526945 := bstep (se 2 (by rfl) ⟨1697604, by rfl⟩ : syracuseStep 4526945 = 3395209) B3395209
theorem B3017963 : Blo 2011435 3017963 := bstep (se 1 (by rfl) ⟨2263472, by rfl⟩ : syracuseStep 3017963 = 4526945) B4526945
theorem B2011975 : Blo 2011435 2011975 := bstep (se 1 (by rfl) ⟨1508981, by rfl⟩ : syracuseStep 2011975 = 3017963) B3017963
theorem B2263477 : Blo 2011435 2263477 := bbase (se 5 (by rfl) ⟨106100, by rfl⟩ : syracuseStep 2263477 = 212201) (by norm_num)
theorem B3017969 : Blo 2011435 3017969 := bstep (se 2 (by rfl) ⟨1131738, by rfl⟩ : syracuseStep 3017969 = 2263477) B2263477
theorem B2011979 : Blo 2011435 2011979 := bstep (se 1 (by rfl) ⟨1508984, by rfl⟩ : syracuseStep 2011979 = 3017969) B3017969
theorem B2546417 : Blo 2011435 2546417 := bbase (se 2 (by rfl) ⟨954906, by rfl⟩ : syracuseStep 2546417 = 1909813) (by norm_num)
theorem B6790445 : Blo 2011435 6790445 := bstep (se 3 (by rfl) ⟨1273208, by rfl⟩ : syracuseStep 6790445 = 2546417) B2546417
theorem B4526963 : Blo 2011435 4526963 := bstep (se 1 (by rfl) ⟨3395222, by rfl⟩ : syracuseStep 4526963 = 6790445) B6790445
theorem B3017975 : Blo 2011435 3017975 := bstep (se 1 (by rfl) ⟨2263481, by rfl⟩ : syracuseStep 3017975 = 4526963) B4526963
theorem B2011983 : Blo 2011435 2011983 := bstep (se 1 (by rfl) ⟨1508987, by rfl⟩ : syracuseStep 2011983 = 3017975) B3017975
theorem B3017981 : Blo 2011435 3017981 := bbase (se 3 (by rfl) ⟨565871, by rfl⟩ : syracuseStep 3017981 = 1131743) (by norm_num)
theorem B2011987 : Blo 2011435 2011987 := bstep (se 1 (by rfl) ⟨1508990, by rfl⟩ : syracuseStep 2011987 = 3017981) B3017981
theorem B4526981 : Blo 2011435 4526981 := bbase (se 4 (by rfl) ⟨424404, by rfl⟩ : syracuseStep 4526981 = 848809) (by norm_num)
theorem B3017987 : Blo 2011435 3017987 := bstep (se 1 (by rfl) ⟨2263490, by rfl⟩ : syracuseStep 3017987 = 4526981) B4526981
theorem B2011991 : Blo 2011435 2011991 := bstep (se 1 (by rfl) ⟨1508993, by rfl⟩ : syracuseStep 2011991 = 3017987) B3017987
theorem B2148553 : Blo 2011435 2148553 := bbase (se 2 (by rfl) ⟨805707, by rfl⟩ : syracuseStep 2148553 = 1611415) (by norm_num)
theorem B2864737 : Blo 2011435 2864737 := bstep (se 2 (by rfl) ⟨1074276, by rfl⟩ : syracuseStep 2864737 = 2148553) B2148553
theorem B3819649 : Blo 2011435 3819649 := bstep (se 2 (by rfl) ⟨1432368, by rfl⟩ : syracuseStep 3819649 = 2864737) B2864737
theorem B5092865 : Blo 2011435 5092865 := bstep (se 2 (by rfl) ⟨1909824, by rfl⟩ : syracuseStep 5092865 = 3819649) B3819649
theorem B3395243 : Blo 2011435 3395243 := bstep (se 1 (by rfl) ⟨2546432, by rfl⟩ : syracuseStep 3395243 = 5092865) B5092865
theorem B2263495 : Blo 2011435 2263495 := bstep (se 1 (by rfl) ⟨1697621, by rfl⟩ : syracuseStep 2263495 = 3395243) B3395243
theorem B3017993 : Blo 2011435 3017993 := bstep (se 2 (by rfl) ⟨1131747, by rfl⟩ : syracuseStep 3017993 = 2263495) B2263495
theorem B2011995 : Blo 2011435 2011995 := bstep (se 1 (by rfl) ⟨1508996, by rfl⟩ : syracuseStep 2011995 = 3017993) B3017993
theorem B10185749 : Blo 2011435 10185749 := bbase (se 6 (by rfl) ⟨238728, by rfl⟩ : syracuseStep 10185749 = 477457) (by norm_num)
theorem B6790499 : Blo 2011435 6790499 := bstep (se 1 (by rfl) ⟨5092874, by rfl⟩ : syracuseStep 6790499 = 10185749) B10185749
theorem B4526999 : Blo 2011435 4526999 := bstep (se 1 (by rfl) ⟨3395249, by rfl⟩ : syracuseStep 4526999 = 6790499) B6790499
theorem B3017999 : Blo 2011435 3017999 := bstep (se 1 (by rfl) ⟨2263499, by rfl⟩ : syracuseStep 3017999 = 4526999) B4526999
theorem B2011999 : Blo 2011435 2011999 := bstep (se 1 (by rfl) ⟨1508999, by rfl⟩ : syracuseStep 2011999 = 3017999) B3017999
theorem B3018005 : Blo 2011435 3018005 := bbase (se 6 (by rfl) ⟨70734, by rfl⟩ : syracuseStep 3018005 = 141469) (by norm_num)
theorem B2012003 : Blo 2011435 2012003 := bstep (se 1 (by rfl) ⟨1509002, by rfl⟩ : syracuseStep 2012003 = 3018005) B3018005
theorem B5162381 : Blo 2011435 5162381 := bbase (se 3 (by rfl) ⟨967946, by rfl⟩ : syracuseStep 5162381 = 1935893) (by norm_num)
theorem B3441587 : Blo 2011435 3441587 := bstep (se 1 (by rfl) ⟨2581190, by rfl⟩ : syracuseStep 3441587 = 5162381) B5162381
theorem B9177565 : Blo 2011435 9177565 := bstep (se 3 (by rfl) ⟨1720793, by rfl⟩ : syracuseStep 9177565 = 3441587) B3441587
theorem B12236753 : Blo 2011435 12236753 := bstep (se 2 (by rfl) ⟨4588782, by rfl⟩ : syracuseStep 12236753 = 9177565) B9177565
theorem B8157835 : Blo 2011435 8157835 := bstep (se 1 (by rfl) ⟨6118376, by rfl⟩ : syracuseStep 8157835 = 12236753) B12236753
theorem B10877113 : Blo 2011435 10877113 := bstep (se 2 (by rfl) ⟨4078917, by rfl⟩ : syracuseStep 10877113 = 8157835) B8157835
theorem B14502817 : Blo 2011435 14502817 := bstep (se 2 (by rfl) ⟨5438556, by rfl⟩ : syracuseStep 14502817 = 10877113) B10877113
theorem B19337089 : Blo 2011435 19337089 := bstep (se 2 (by rfl) ⟨7251408, by rfl⟩ : syracuseStep 19337089 = 14502817) B14502817
theorem B25782785 : Blo 2011435 25782785 := bstep (se 2 (by rfl) ⟨9668544, by rfl⟩ : syracuseStep 25782785 = 19337089) B19337089
theorem B17188523 : Blo 2011435 17188523 := bstep (se 1 (by rfl) ⟨12891392, by rfl⟩ : syracuseStep 17188523 = 25782785) B25782785
theorem B11459015 : Blo 2011435 11459015 := bstep (se 1 (by rfl) ⟨8594261, by rfl⟩ : syracuseStep 11459015 = 17188523) B17188523
theorem B7639343 : Blo 2011435 7639343 := bstep (se 1 (by rfl) ⟨5729507, by rfl⟩ : syracuseStep 7639343 = 11459015) B11459015
theorem B5092895 : Blo 2011435 5092895 := bstep (se 1 (by rfl) ⟨3819671, by rfl⟩ : syracuseStep 5092895 = 7639343) B7639343
theorem B3395263 : Blo 2011435 3395263 := bstep (se 1 (by rfl) ⟨2546447, by rfl⟩ : syracuseStep 3395263 = 5092895) B5092895
theorem B4527017 : Blo 2011435 4527017 := bstep (se 2 (by rfl) ⟨1697631, by rfl⟩ : syracuseStep 4527017 = 3395263) B3395263
theorem B3018011 : Blo 2011435 3018011 := bstep (se 1 (by rfl) ⟨2263508, by rfl⟩ : syracuseStep 3018011 = 4527017) B4527017
theorem B2012007 : Blo 2011435 2012007 := bstep (se 1 (by rfl) ⟨1509005, by rfl⟩ : syracuseStep 2012007 = 3018011) B3018011
theorem B2263513 : Blo 2011435 2263513 := bbase (se 2 (by rfl) ⟨848817, by rfl⟩ : syracuseStep 2263513 = 1697635) (by norm_num)
theorem B3018017 : Blo 2011435 3018017 := bstep (se 2 (by rfl) ⟨1131756, by rfl⟩ : syracuseStep 3018017 = 2263513) B2263513
theorem B2012011 : Blo 2011435 2012011 := bstep (se 1 (by rfl) ⟨1509008, by rfl⟩ : syracuseStep 2012011 = 3018017) B3018017
theorem B2864765 : Blo 2011435 2864765 := bbase (se 3 (by rfl) ⟨537143, by rfl⟩ : syracuseStep 2864765 = 1074287) (by norm_num)
theorem B7639373 : Blo 2011435 7639373 := bstep (se 3 (by rfl) ⟨1432382, by rfl⟩ : syracuseStep 7639373 = 2864765) B2864765
theorem B5092915 : Blo 2011435 5092915 := bstep (se 1 (by rfl) ⟨3819686, by rfl⟩ : syracuseStep 5092915 = 7639373) B7639373
theorem B6790553 : Blo 2011435 6790553 := bstep (se 2 (by rfl) ⟨2546457, by rfl⟩ : syracuseStep 6790553 = 5092915) B5092915
theorem B4527035 : Blo 2011435 4527035 := bstep (se 1 (by rfl) ⟨3395276, by rfl⟩ : syracuseStep 4527035 = 6790553) B6790553
theorem B3018023 : Blo 2011435 3018023 := bstep (se 1 (by rfl) ⟨2263517, by rfl⟩ : syracuseStep 3018023 = 4527035) B4527035
theorem B2012015 : Blo 2011435 2012015 := bstep (se 1 (by rfl) ⟨1509011, by rfl⟩ : syracuseStep 2012015 = 3018023) B3018023
theorem B3018029 : Blo 2011435 3018029 := bbase (se 3 (by rfl) ⟨565880, by rfl⟩ : syracuseStep 3018029 = 1131761) (by norm_num)
theorem B2012019 : Blo 2011435 2012019 := bstep (se 1 (by rfl) ⟨1509014, by rfl⟩ : syracuseStep 2012019 = 3018029) B3018029
theorem B4527053 : Blo 2011435 4527053 := bbase (se 3 (by rfl) ⟨848822, by rfl⟩ : syracuseStep 4527053 = 1697645) (by norm_num)
theorem B3018035 : Blo 2011435 3018035 := bstep (se 1 (by rfl) ⟨2263526, by rfl⟩ : syracuseStep 3018035 = 4527053) B4527053
theorem B2012023 : Blo 2011435 2012023 := bstep (se 1 (by rfl) ⟨1509017, by rfl⟩ : syracuseStep 2012023 = 3018035) B3018035
theorem B2546473 : Blo 2011435 2546473 := bbase (se 2 (by rfl) ⟨954927, by rfl⟩ : syracuseStep 2546473 = 1909855) (by norm_num)
theorem B3395297 : Blo 2011435 3395297 := bstep (se 2 (by rfl) ⟨1273236, by rfl⟩ : syracuseStep 3395297 = 2546473) B2546473
theorem B2263531 : Blo 2011435 2263531 := bstep (se 1 (by rfl) ⟨1697648, by rfl⟩ : syracuseStep 2263531 = 3395297) B3395297
theorem B3018041 : Blo 2011435 3018041 := bstep (se 2 (by rfl) ⟨1131765, by rfl⟩ : syracuseStep 3018041 = 2263531) B2263531
theorem B2012027 : Blo 2011435 2012027 := bstep (se 1 (by rfl) ⟨1509020, by rfl⟩ : syracuseStep 2012027 = 3018041) B3018041
theorem B3441629 : Blo 2011435 3441629 := bbase (se 3 (by rfl) ⟨645305, by rfl⟩ : syracuseStep 3441629 = 1290611) (by norm_num)
theorem B2294419 : Blo 2011435 2294419 := bstep (se 1 (by rfl) ⟨1720814, by rfl⟩ : syracuseStep 2294419 = 3441629) B3441629
theorem B3059225 : Blo 2011435 3059225 := bstep (se 2 (by rfl) ⟨1147209, by rfl⟩ : syracuseStep 3059225 = 2294419) B2294419
theorem B2039483 : Blo 2011435 2039483 := bstep (se 1 (by rfl) ⟨1529612, by rfl⟩ : syracuseStep 2039483 = 3059225) B3059225
theorem B5438621 : Blo 2011435 5438621 := bstep (se 3 (by rfl) ⟨1019741, by rfl⟩ : syracuseStep 5438621 = 2039483) B2039483
theorem B14502989 : Blo 2011435 14502989 := bstep (se 3 (by rfl) ⟨2719310, by rfl⟩ : syracuseStep 14502989 = 5438621) B5438621
theorem B9668659 : Blo 2011435 9668659 := bstep (se 1 (by rfl) ⟨7251494, by rfl⟩ : syracuseStep 9668659 = 14502989) B14502989
theorem B12891545 : Blo 2011435 12891545 := bstep (se 2 (by rfl) ⟨4834329, by rfl⟩ : syracuseStep 12891545 = 9668659) B9668659
theorem B8594363 : Blo 2011435 8594363 := bstep (se 1 (by rfl) ⟨6445772, by rfl⟩ : syracuseStep 8594363 = 12891545) B12891545
theorem B22918301 : Blo 2011435 22918301 := bstep (se 3 (by rfl) ⟨4297181, by rfl⟩ : syracuseStep 22918301 = 8594363) B8594363
theorem B15278867 : Blo 2011435 15278867 := bstep (se 1 (by rfl) ⟨11459150, by rfl⟩ : syracuseStep 15278867 = 22918301) B22918301
theorem B10185911 : Blo 2011435 10185911 := bstep (se 1 (by rfl) ⟨7639433, by rfl⟩ : syracuseStep 10185911 = 15278867) B15278867
theorem B6790607 : Blo 2011435 6790607 := bstep (se 1 (by rfl) ⟨5092955, by rfl⟩ : syracuseStep 6790607 = 10185911) B10185911
theorem B4527071 : Blo 2011435 4527071 := bstep (se 1 (by rfl) ⟨3395303, by rfl⟩ : syracuseStep 4527071 = 6790607) B6790607
theorem B3018047 : Blo 2011435 3018047 := bstep (se 1 (by rfl) ⟨2263535, by rfl⟩ : syracuseStep 3018047 = 4527071) B4527071
theorem B2012031 : Blo 2011435 2012031 := bstep (se 1 (by rfl) ⟨1509023, by rfl⟩ : syracuseStep 2012031 = 3018047) B3018047
theorem B3018053 : Blo 2011435 3018053 := bbase (se 4 (by rfl) ⟨282942, by rfl⟩ : syracuseStep 3018053 = 565885) (by norm_num)
theorem B2012035 : Blo 2011435 2012035 := bstep (se 1 (by rfl) ⟨1509026, by rfl⟩ : syracuseStep 2012035 = 3018053) B3018053
theorem B3395317 : Blo 2011435 3395317 := bbase (se 5 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 3395317 = 318311) (by norm_num)
theorem B4527089 : Blo 2011435 4527089 := bstep (se 2 (by rfl) ⟨1697658, by rfl⟩ : syracuseStep 4527089 = 3395317) B3395317
theorem B3018059 : Blo 2011435 3018059 := bstep (se 1 (by rfl) ⟨2263544, by rfl⟩ : syracuseStep 3018059 = 4527089) B4527089
theorem B2012039 : Blo 2011435 2012039 := bstep (se 1 (by rfl) ⟨1509029, by rfl⟩ : syracuseStep 2012039 = 3018059) B3018059
theorem B2263549 : Blo 2011435 2263549 := bbase (se 3 (by rfl) ⟨424415, by rfl⟩ : syracuseStep 2263549 = 848831) (by norm_num)
theorem B3018065 : Blo 2011435 3018065 := bstep (se 2 (by rfl) ⟨1131774, by rfl⟩ : syracuseStep 3018065 = 2263549) B2263549
theorem B2012043 : Blo 2011435 2012043 := bstep (se 1 (by rfl) ⟨1509032, by rfl⟩ : syracuseStep 2012043 = 3018065) B3018065
theorem B6790661 : Blo 2011435 6790661 := bbase (se 4 (by rfl) ⟨636624, by rfl⟩ : syracuseStep 6790661 = 1273249) (by norm_num)
theorem B4527107 : Blo 2011435 4527107 := bstep (se 1 (by rfl) ⟨3395330, by rfl⟩ : syracuseStep 4527107 = 6790661) B6790661
theorem B3018071 : Blo 2011435 3018071 := bstep (se 1 (by rfl) ⟨2263553, by rfl⟩ : syracuseStep 3018071 = 4527107) B4527107
theorem B2012047 : Blo 2011435 2012047 := bstep (se 1 (by rfl) ⟨1509035, by rfl⟩ : syracuseStep 2012047 = 3018071) B3018071
theorem B3018077 : Blo 2011435 3018077 := bbase (se 3 (by rfl) ⟨565889, by rfl⟩ : syracuseStep 3018077 = 1131779) (by norm_num)
theorem B2012051 : Blo 2011435 2012051 := bstep (se 1 (by rfl) ⟨1509038, by rfl⟩ : syracuseStep 2012051 = 3018077) B3018077
theorem B4527125 : Blo 2011435 4527125 := bbase (se 6 (by rfl) ⟨106104, by rfl⟩ : syracuseStep 4527125 = 212209) (by norm_num)
theorem B3018083 : Blo 2011435 3018083 := bstep (se 1 (by rfl) ⟨2263562, by rfl⟩ : syracuseStep 3018083 = 4527125) B4527125
theorem B2012055 : Blo 2011435 2012055 := bstep (se 1 (by rfl) ⟨1509041, by rfl⟩ : syracuseStep 2012055 = 3018083) B3018083
theorem B7639541 : Blo 2011435 7639541 := bbase (se 5 (by rfl) ⟨358103, by rfl⟩ : syracuseStep 7639541 = 716207) (by norm_num)
theorem B5093027 : Blo 2011435 5093027 := bstep (se 1 (by rfl) ⟨3819770, by rfl⟩ : syracuseStep 5093027 = 7639541) B7639541
theorem B3395351 : Blo 2011435 3395351 := bstep (se 1 (by rfl) ⟨2546513, by rfl⟩ : syracuseStep 3395351 = 5093027) B5093027
theorem B2263567 : Blo 2011435 2263567 := bstep (se 1 (by rfl) ⟨1697675, by rfl⟩ : syracuseStep 2263567 = 3395351) B3395351
theorem B3018089 : Blo 2011435 3018089 := bstep (se 2 (by rfl) ⟨1131783, by rfl⟩ : syracuseStep 3018089 = 2263567) B2263567
theorem B2012059 : Blo 2011435 2012059 := bstep (se 1 (by rfl) ⟨1509044, by rfl⟩ : syracuseStep 2012059 = 3018089) B3018089
theorem B2148625 : Blo 2011435 2148625 := bbase (se 2 (by rfl) ⟨805734, by rfl⟩ : syracuseStep 2148625 = 1611469) (by norm_num)
theorem B11459333 : Blo 2011435 11459333 := bstep (se 4 (by rfl) ⟨1074312, by rfl⟩ : syracuseStep 11459333 = 2148625) B2148625
theorem B7639555 : Blo 2011435 7639555 := bstep (se 1 (by rfl) ⟨5729666, by rfl⟩ : syracuseStep 7639555 = 11459333) B11459333
theorem B10186073 : Blo 2011435 10186073 := bstep (se 2 (by rfl) ⟨3819777, by rfl⟩ : syracuseStep 10186073 = 7639555) B7639555
theorem B6790715 : Blo 2011435 6790715 := bstep (se 1 (by rfl) ⟨5093036, by rfl⟩ : syracuseStep 6790715 = 10186073) B10186073
theorem B4527143 : Blo 2011435 4527143 := bstep (se 1 (by rfl) ⟨3395357, by rfl⟩ : syracuseStep 4527143 = 6790715) B6790715
theorem B3018095 : Blo 2011435 3018095 := bstep (se 1 (by rfl) ⟨2263571, by rfl⟩ : syracuseStep 3018095 = 4527143) B4527143
theorem B2012063 : Blo 2011435 2012063 := bstep (se 1 (by rfl) ⟨1509047, by rfl⟩ : syracuseStep 2012063 = 3018095) B3018095
theorem B3018101 : Blo 2011435 3018101 := bbase (se 5 (by rfl) ⟨141473, by rfl⟩ : syracuseStep 3018101 = 282947) (by norm_num)
theorem B2012067 : Blo 2011435 2012067 := bstep (se 1 (by rfl) ⟨1509050, by rfl⟩ : syracuseStep 2012067 = 3018101) B3018101
theorem B2864845 : Blo 2011435 2864845 := bbase (se 3 (by rfl) ⟨537158, by rfl⟩ : syracuseStep 2864845 = 1074317) (by norm_num)
theorem B3819793 : Blo 2011435 3819793 := bstep (se 2 (by rfl) ⟨1432422, by rfl⟩ : syracuseStep 3819793 = 2864845) B2864845
theorem B5093057 : Blo 2011435 5093057 := bstep (se 2 (by rfl) ⟨1909896, by rfl⟩ : syracuseStep 5093057 = 3819793) B3819793
theorem B3395371 : Blo 2011435 3395371 := bstep (se 1 (by rfl) ⟨2546528, by rfl⟩ : syracuseStep 3395371 = 5093057) B5093057
theorem B4527161 : Blo 2011435 4527161 := bstep (se 2 (by rfl) ⟨1697685, by rfl⟩ : syracuseStep 4527161 = 3395371) B3395371
theorem B3018107 : Blo 2011435 3018107 := bstep (se 1 (by rfl) ⟨2263580, by rfl⟩ : syracuseStep 3018107 = 4527161) B4527161
theorem B2012071 : Blo 2011435 2012071 := bstep (se 1 (by rfl) ⟨1509053, by rfl⟩ : syracuseStep 2012071 = 3018107) B3018107
theorem B2263585 : Blo 2011435 2263585 := bbase (se 2 (by rfl) ⟨848844, by rfl⟩ : syracuseStep 2263585 = 1697689) (by norm_num)
theorem B3018113 : Blo 2011435 3018113 := bstep (se 2 (by rfl) ⟨1131792, by rfl⟩ : syracuseStep 3018113 = 2263585) B2263585
theorem B2012075 : Blo 2011435 2012075 := bstep (se 1 (by rfl) ⟨1509056, by rfl⟩ : syracuseStep 2012075 = 3018113) B3018113
theorem B5093077 : Blo 2011435 5093077 := bbase (se 7 (by rfl) ⟨59684, by rfl⟩ : syracuseStep 5093077 = 119369) (by norm_num)
theorem B6790769 : Blo 2011435 6790769 := bstep (se 2 (by rfl) ⟨2546538, by rfl⟩ : syracuseStep 6790769 = 5093077) B5093077
theorem B4527179 : Blo 2011435 4527179 := bstep (se 1 (by rfl) ⟨3395384, by rfl⟩ : syracuseStep 4527179 = 6790769) B6790769
theorem B3018119 : Blo 2011435 3018119 := bstep (se 1 (by rfl) ⟨2263589, by rfl⟩ : syracuseStep 3018119 = 4527179) B4527179
theorem B2012079 : Blo 2011435 2012079 := bstep (se 1 (by rfl) ⟨1509059, by rfl⟩ : syracuseStep 2012079 = 3018119) B3018119
theorem B3018125 : Blo 2011435 3018125 := bbase (se 3 (by rfl) ⟨565898, by rfl⟩ : syracuseStep 3018125 = 1131797) (by norm_num)
theorem B2012083 : Blo 2011435 2012083 := bstep (se 1 (by rfl) ⟨1509062, by rfl⟩ : syracuseStep 2012083 = 3018125) B3018125
theorem B4527197 : Blo 2011435 4527197 := bbase (se 3 (by rfl) ⟨848849, by rfl⟩ : syracuseStep 4527197 = 1697699) (by norm_num)
theorem B3018131 : Blo 2011435 3018131 := bstep (se 1 (by rfl) ⟨2263598, by rfl⟩ : syracuseStep 3018131 = 4527197) B4527197
theorem B2012087 : Blo 2011435 2012087 := bstep (se 1 (by rfl) ⟨1509065, by rfl⟩ : syracuseStep 2012087 = 3018131) B3018131
theorem B3395405 : Blo 2011435 3395405 := bbase (se 3 (by rfl) ⟨636638, by rfl⟩ : syracuseStep 3395405 = 1273277) (by norm_num)
theorem B2263603 : Blo 2011435 2263603 := bstep (se 1 (by rfl) ⟨1697702, by rfl⟩ : syracuseStep 2263603 = 3395405) B3395405
theorem B3018137 : Blo 2011435 3018137 := bstep (se 2 (by rfl) ⟨1131801, by rfl⟩ : syracuseStep 3018137 = 2263603) B2263603
theorem B2012091 : Blo 2011435 2012091 := bstep (se 1 (by rfl) ⟨1509068, by rfl⟩ : syracuseStep 2012091 = 3018137) B3018137
theorem B2719397 : Blo 2011435 2719397 := bbase (se 4 (by rfl) ⟨254943, by rfl⟩ : syracuseStep 2719397 = 509887) (by norm_num)
theorem B7251725 : Blo 2011435 7251725 := bstep (se 3 (by rfl) ⟨1359698, by rfl⟩ : syracuseStep 7251725 = 2719397) B2719397
theorem B19337933 : Blo 2011435 19337933 := bstep (se 3 (by rfl) ⟨3625862, by rfl⟩ : syracuseStep 19337933 = 7251725) B7251725
theorem B12891955 : Blo 2011435 12891955 := bstep (se 1 (by rfl) ⟨9668966, by rfl⟩ : syracuseStep 12891955 = 19337933) B19337933
theorem B17189273 : Blo 2011435 17189273 := bstep (se 2 (by rfl) ⟨6445977, by rfl⟩ : syracuseStep 17189273 = 12891955) B12891955
theorem B11459515 : Blo 2011435 11459515 := bstep (se 1 (by rfl) ⟨8594636, by rfl⟩ : syracuseStep 11459515 = 17189273) B17189273
theorem B15279353 : Blo 2011435 15279353 := bstep (se 2 (by rfl) ⟨5729757, by rfl⟩ : syracuseStep 15279353 = 11459515) B11459515
theorem B10186235 : Blo 2011435 10186235 := bstep (se 1 (by rfl) ⟨7639676, by rfl⟩ : syracuseStep 10186235 = 15279353) B15279353
theorem B6790823 : Blo 2011435 6790823 := bstep (se 1 (by rfl) ⟨5093117, by rfl⟩ : syracuseStep 6790823 = 10186235) B10186235
theorem B4527215 : Blo 2011435 4527215 := bstep (se 1 (by rfl) ⟨3395411, by rfl⟩ : syracuseStep 4527215 = 6790823) B6790823
theorem B3018143 : Blo 2011435 3018143 := bstep (se 1 (by rfl) ⟨2263607, by rfl⟩ : syracuseStep 3018143 = 4527215) B4527215
theorem B2012095 : Blo 2011435 2012095 := bstep (se 1 (by rfl) ⟨1509071, by rfl⟩ : syracuseStep 2012095 = 3018143) B3018143
theorem B3018149 : Blo 2011435 3018149 := bbase (se 4 (by rfl) ⟨282951, by rfl⟩ : syracuseStep 3018149 = 565903) (by norm_num)
theorem B2012099 : Blo 2011435 2012099 := bstep (se 1 (by rfl) ⟨1509074, by rfl⟩ : syracuseStep 2012099 = 3018149) B3018149
theorem B2546569 : Blo 2011435 2546569 := bbase (se 2 (by rfl) ⟨954963, by rfl⟩ : syracuseStep 2546569 = 1909927) (by norm_num)
theorem B3395425 : Blo 2011435 3395425 := bstep (se 2 (by rfl) ⟨1273284, by rfl⟩ : syracuseStep 3395425 = 2546569) B2546569
theorem B4527233 : Blo 2011435 4527233 := bstep (se 2 (by rfl) ⟨1697712, by rfl⟩ : syracuseStep 4527233 = 3395425) B3395425
theorem B3018155 : Blo 2011435 3018155 := bstep (se 1 (by rfl) ⟨2263616, by rfl⟩ : syracuseStep 3018155 = 4527233) B4527233
theorem B2012103 : Blo 2011435 2012103 := bstep (se 1 (by rfl) ⟨1509077, by rfl⟩ : syracuseStep 2012103 = 3018155) B3018155
theorem B2263621 : Blo 2011435 2263621 := bbase (se 4 (by rfl) ⟨212214, by rfl⟩ : syracuseStep 2263621 = 424429) (by norm_num)
theorem B3018161 : Blo 2011435 3018161 := bstep (se 2 (by rfl) ⟨1131810, by rfl⟩ : syracuseStep 3018161 = 2263621) B2263621
theorem B2012107 : Blo 2011435 2012107 := bstep (se 1 (by rfl) ⟨1509080, by rfl⟩ : syracuseStep 2012107 = 3018161) B3018161
theorem B3819869 : Blo 2011435 3819869 := bbase (se 3 (by rfl) ⟨716225, by rfl⟩ : syracuseStep 3819869 = 1432451) (by norm_num)
theorem B2546579 : Blo 2011435 2546579 := bstep (se 1 (by rfl) ⟨1909934, by rfl⟩ : syracuseStep 2546579 = 3819869) B3819869
theorem B6790877 : Blo 2011435 6790877 := bstep (se 3 (by rfl) ⟨1273289, by rfl⟩ : syracuseStep 6790877 = 2546579) B2546579
theorem B4527251 : Blo 2011435 4527251 := bstep (se 1 (by rfl) ⟨3395438, by rfl⟩ : syracuseStep 4527251 = 6790877) B6790877
theorem B3018167 : Blo 2011435 3018167 := bstep (se 1 (by rfl) ⟨2263625, by rfl⟩ : syracuseStep 3018167 = 4527251) B4527251
theorem B2012111 : Blo 2011435 2012111 := bstep (se 1 (by rfl) ⟨1509083, by rfl⟩ : syracuseStep 2012111 = 3018167) B3018167
theorem B3018173 : Blo 2011435 3018173 := bbase (se 3 (by rfl) ⟨565907, by rfl⟩ : syracuseStep 3018173 = 1131815) (by norm_num)
theorem B2012115 : Blo 2011435 2012115 := bstep (se 1 (by rfl) ⟨1509086, by rfl⟩ : syracuseStep 2012115 = 3018173) B3018173
theorem B4527269 : Blo 2011435 4527269 := bbase (se 4 (by rfl) ⟨424431, by rfl⟩ : syracuseStep 4527269 = 848863) (by norm_num)
theorem B3018179 : Blo 2011435 3018179 := bstep (se 1 (by rfl) ⟨2263634, by rfl⟩ : syracuseStep 3018179 = 4527269) B4527269
theorem B2012119 : Blo 2011435 2012119 := bstep (se 1 (by rfl) ⟨1509089, by rfl⟩ : syracuseStep 2012119 = 3018179) B3018179
theorem B5093189 : Blo 2011435 5093189 := bbase (se 4 (by rfl) ⟨477486, by rfl⟩ : syracuseStep 5093189 = 954973) (by norm_num)
theorem B3395459 : Blo 2011435 3395459 := bstep (se 1 (by rfl) ⟨2546594, by rfl⟩ : syracuseStep 3395459 = 5093189) B5093189
theorem B2263639 : Blo 2011435 2263639 := bstep (se 1 (by rfl) ⟨1697729, by rfl⟩ : syracuseStep 2263639 = 3395459) B3395459
theorem B3018185 : Blo 2011435 3018185 := bstep (se 2 (by rfl) ⟨1131819, by rfl⟩ : syracuseStep 3018185 = 2263639) B2263639
theorem B2012123 : Blo 2011435 2012123 := bstep (se 1 (by rfl) ⟨1509092, by rfl⟩ : syracuseStep 2012123 = 3018185) B3018185
theorem B2039581 : Blo 2011435 2039581 := bbase (se 3 (by rfl) ⟨382421, by rfl⟩ : syracuseStep 2039581 = 764843) (by norm_num)
theorem B2719441 : Blo 2011435 2719441 := bstep (se 2 (by rfl) ⟨1019790, by rfl⟩ : syracuseStep 2719441 = 2039581) B2039581
theorem B3625921 : Blo 2011435 3625921 := bstep (se 2 (by rfl) ⟨1359720, by rfl⟩ : syracuseStep 3625921 = 2719441) B2719441
theorem B4834561 : Blo 2011435 4834561 := bstep (se 2 (by rfl) ⟨1812960, by rfl⟩ : syracuseStep 4834561 = 3625921) B3625921
theorem B6446081 : Blo 2011435 6446081 := bstep (se 2 (by rfl) ⟨2417280, by rfl⟩ : syracuseStep 6446081 = 4834561) B4834561
theorem B4297387 : Blo 2011435 4297387 := bstep (se 1 (by rfl) ⟨3223040, by rfl⟩ : syracuseStep 4297387 = 6446081) B6446081
theorem B5729849 : Blo 2011435 5729849 := bstep (se 2 (by rfl) ⟨2148693, by rfl⟩ : syracuseStep 5729849 = 4297387) B4297387
theorem B3819899 : Blo 2011435 3819899 := bstep (se 1 (by rfl) ⟨2864924, by rfl⟩ : syracuseStep 3819899 = 5729849) B5729849
theorem B10186397 : Blo 2011435 10186397 := bstep (se 3 (by rfl) ⟨1909949, by rfl⟩ : syracuseStep 10186397 = 3819899) B3819899
theorem B6790931 : Blo 2011435 6790931 := bstep (se 1 (by rfl) ⟨5093198, by rfl⟩ : syracuseStep 6790931 = 10186397) B10186397
theorem B4527287 : Blo 2011435 4527287 := bstep (se 1 (by rfl) ⟨3395465, by rfl⟩ : syracuseStep 4527287 = 6790931) B6790931
theorem B3018191 : Blo 2011435 3018191 := bstep (se 1 (by rfl) ⟨2263643, by rfl⟩ : syracuseStep 3018191 = 4527287) B4527287
theorem B2012127 : Blo 2011435 2012127 := bstep (se 1 (by rfl) ⟨1509095, by rfl⟩ : syracuseStep 2012127 = 3018191) B3018191
theorem B3018197 : Blo 2011435 3018197 := bbase (se 7 (by rfl) ⟨35369, by rfl⟩ : syracuseStep 3018197 = 70739) (by norm_num)
theorem B2012131 : Blo 2011435 2012131 := bstep (se 1 (by rfl) ⟨1509098, by rfl⟩ : syracuseStep 2012131 = 3018197) B3018197
theorem B7639829 : Blo 2011435 7639829 := bbase (se 6 (by rfl) ⟨179058, by rfl⟩ : syracuseStep 7639829 = 358117) (by norm_num)
theorem B5093219 : Blo 2011435 5093219 := bstep (se 1 (by rfl) ⟨3819914, by rfl⟩ : syracuseStep 5093219 = 7639829) B7639829
theorem B3395479 : Blo 2011435 3395479 := bstep (se 1 (by rfl) ⟨2546609, by rfl⟩ : syracuseStep 3395479 = 5093219) B5093219
theorem B4527305 : Blo 2011435 4527305 := bstep (se 2 (by rfl) ⟨1697739, by rfl⟩ : syracuseStep 4527305 = 3395479) B3395479
theorem B3018203 : Blo 2011435 3018203 := bstep (se 1 (by rfl) ⟨2263652, by rfl⟩ : syracuseStep 3018203 = 4527305) B4527305
theorem B2012135 : Blo 2011435 2012135 := bstep (se 1 (by rfl) ⟨1509101, by rfl⟩ : syracuseStep 2012135 = 3018203) B3018203
theorem B2263657 : Blo 2011435 2263657 := bbase (se 2 (by rfl) ⟨848871, by rfl⟩ : syracuseStep 2263657 = 1697743) (by norm_num)
theorem B3018209 : Blo 2011435 3018209 := bstep (se 2 (by rfl) ⟨1131828, by rfl⟩ : syracuseStep 3018209 = 2263657) B2263657
theorem B2012139 : Blo 2011435 2012139 := bstep (se 1 (by rfl) ⟨1509104, by rfl⟩ : syracuseStep 2012139 = 3018209) B3018209
theorem B4297421 : Blo 2011435 4297421 := bbase (se 3 (by rfl) ⟨805766, by rfl⟩ : syracuseStep 4297421 = 1611533) (by norm_num)
theorem B11459789 : Blo 2011435 11459789 := bstep (se 3 (by rfl) ⟨2148710, by rfl⟩ : syracuseStep 11459789 = 4297421) B4297421
theorem B7639859 : Blo 2011435 7639859 := bstep (se 1 (by rfl) ⟨5729894, by rfl⟩ : syracuseStep 7639859 = 11459789) B11459789
theorem B5093239 : Blo 2011435 5093239 := bstep (se 1 (by rfl) ⟨3819929, by rfl⟩ : syracuseStep 5093239 = 7639859) B7639859
theorem B6790985 : Blo 2011435 6790985 := bstep (se 2 (by rfl) ⟨2546619, by rfl⟩ : syracuseStep 6790985 = 5093239) B5093239
theorem B4527323 : Blo 2011435 4527323 := bstep (se 1 (by rfl) ⟨3395492, by rfl⟩ : syracuseStep 4527323 = 6790985) B6790985
theorem B3018215 : Blo 2011435 3018215 := bstep (se 1 (by rfl) ⟨2263661, by rfl⟩ : syracuseStep 3018215 = 4527323) B4527323
theorem B2012143 : Blo 2011435 2012143 := bstep (se 1 (by rfl) ⟨1509107, by rfl⟩ : syracuseStep 2012143 = 3018215) B3018215
theorem B3018221 : Blo 2011435 3018221 := bbase (se 3 (by rfl) ⟨565916, by rfl⟩ : syracuseStep 3018221 = 1131833) (by norm_num)
theorem B2012147 : Blo 2011435 2012147 := bstep (se 1 (by rfl) ⟨1509110, by rfl⟩ : syracuseStep 2012147 = 3018221) B3018221
theorem B4527341 : Blo 2011435 4527341 := bbase (se 3 (by rfl) ⟨848876, by rfl⟩ : syracuseStep 4527341 = 1697753) (by norm_num)
theorem B3018227 : Blo 2011435 3018227 := bstep (se 1 (by rfl) ⟨2263670, by rfl⟩ : syracuseStep 3018227 = 4527341) B4527341
theorem B2012151 : Blo 2011435 2012151 := bstep (se 1 (by rfl) ⟨1509113, by rfl⟩ : syracuseStep 2012151 = 3018227) B3018227
theorem B2864965 : Blo 2011435 2864965 := bbase (se 4 (by rfl) ⟨268590, by rfl⟩ : syracuseStep 2864965 = 537181) (by norm_num)
theorem B3819953 : Blo 2011435 3819953 := bstep (se 2 (by rfl) ⟨1432482, by rfl⟩ : syracuseStep 3819953 = 2864965) B2864965
theorem B2546635 : Blo 2011435 2546635 := bstep (se 1 (by rfl) ⟨1909976, by rfl⟩ : syracuseStep 2546635 = 3819953) B3819953
theorem B3395513 : Blo 2011435 3395513 := bstep (se 2 (by rfl) ⟨1273317, by rfl⟩ : syracuseStep 3395513 = 2546635) B2546635
theorem B2263675 : Blo 2011435 2263675 := bstep (se 1 (by rfl) ⟨1697756, by rfl⟩ : syracuseStep 2263675 = 3395513) B3395513
theorem B3018233 : Blo 2011435 3018233 := bstep (se 2 (by rfl) ⟨1131837, by rfl⟩ : syracuseStep 3018233 = 2263675) B2263675
theorem B2012155 : Blo 2011435 2012155 := bstep (se 1 (by rfl) ⟨1509116, by rfl⟩ : syracuseStep 2012155 = 3018233) B3018233
theorem B6202325 : Blo 2011435 6202325 := bbase (se 7 (by rfl) ⟨72683, by rfl⟩ : syracuseStep 6202325 = 145367) (by norm_num)
theorem B4134883 : Blo 2011435 4134883 := bstep (se 1 (by rfl) ⟨3101162, by rfl⟩ : syracuseStep 4134883 = 6202325) B6202325
theorem B5513177 : Blo 2011435 5513177 := bstep (se 2 (by rfl) ⟨2067441, by rfl⟩ : syracuseStep 5513177 = 4134883) B4134883
theorem B3675451 : Blo 2011435 3675451 := bstep (se 1 (by rfl) ⟨2756588, by rfl⟩ : syracuseStep 3675451 = 5513177) B5513177
theorem B4900601 : Blo 2011435 4900601 := bstep (se 2 (by rfl) ⟨1837725, by rfl⟩ : syracuseStep 4900601 = 3675451) B3675451
theorem B3267067 : Blo 2011435 3267067 := bstep (se 1 (by rfl) ⟨2450300, by rfl⟩ : syracuseStep 3267067 = 4900601) B4900601
theorem B4356089 : Blo 2011435 4356089 := bstep (se 2 (by rfl) ⟨1633533, by rfl⟩ : syracuseStep 4356089 = 3267067) B3267067
theorem B2904059 : Blo 2011435 2904059 := bstep (se 1 (by rfl) ⟨2178044, by rfl⟩ : syracuseStep 2904059 = 4356089) B4356089
theorem B7744157 : Blo 2011435 7744157 := bstep (se 3 (by rfl) ⟨1452029, by rfl⟩ : syracuseStep 7744157 = 2904059) B2904059
theorem B5162771 : Blo 2011435 5162771 := bstep (se 1 (by rfl) ⟨3872078, by rfl⟩ : syracuseStep 5162771 = 7744157) B7744157
theorem B3441847 : Blo 2011435 3441847 := bstep (se 1 (by rfl) ⟨2581385, by rfl⟩ : syracuseStep 3441847 = 5162771) B5162771
theorem B4589129 : Blo 2011435 4589129 := bstep (se 2 (by rfl) ⟨1720923, by rfl⟩ : syracuseStep 4589129 = 3441847) B3441847
theorem B3059419 : Blo 2011435 3059419 := bstep (se 1 (by rfl) ⟨2294564, by rfl⟩ : syracuseStep 3059419 = 4589129) B4589129
theorem B4079225 : Blo 2011435 4079225 := bstep (se 2 (by rfl) ⟨1529709, by rfl⟩ : syracuseStep 4079225 = 3059419) B3059419
theorem B10877933 : Blo 2011435 10877933 := bstep (se 3 (by rfl) ⟨2039612, by rfl⟩ : syracuseStep 10877933 = 4079225) B4079225
theorem B29007821 : Blo 2011435 29007821 := bstep (se 3 (by rfl) ⟨5438966, by rfl⟩ : syracuseStep 29007821 = 10877933) B10877933
theorem B77354189 : Blo 2011435 77354189 := bstep (se 3 (by rfl) ⟨14503910, by rfl⟩ : syracuseStep 77354189 = 29007821) B29007821
theorem B51569459 : Blo 2011435 51569459 := bstep (se 1 (by rfl) ⟨38677094, by rfl⟩ : syracuseStep 51569459 = 77354189) B77354189
theorem B34379639 : Blo 2011435 34379639 := bstep (se 1 (by rfl) ⟨25784729, by rfl⟩ : syracuseStep 34379639 = 51569459) B51569459
theorem B22919759 : Blo 2011435 22919759 := bstep (se 1 (by rfl) ⟨17189819, by rfl⟩ : syracuseStep 22919759 = 34379639) B34379639
theorem B15279839 : Blo 2011435 15279839 := bstep (se 1 (by rfl) ⟨11459879, by rfl⟩ : syracuseStep 15279839 = 22919759) B22919759
theorem B10186559 : Blo 2011435 10186559 := bstep (se 1 (by rfl) ⟨7639919, by rfl⟩ : syracuseStep 10186559 = 15279839) B15279839
theorem B6791039 : Blo 2011435 6791039 := bstep (se 1 (by rfl) ⟨5093279, by rfl⟩ : syracuseStep 6791039 = 10186559) B10186559
theorem B4527359 : Blo 2011435 4527359 := bstep (se 1 (by rfl) ⟨3395519, by rfl⟩ : syracuseStep 4527359 = 6791039) B6791039
theorem B3018239 : Blo 2011435 3018239 := bstep (se 1 (by rfl) ⟨2263679, by rfl⟩ : syracuseStep 3018239 = 4527359) B4527359
theorem B2012159 : Blo 2011435 2012159 := bstep (se 1 (by rfl) ⟨1509119, by rfl⟩ : syracuseStep 2012159 = 3018239) B3018239
theorem B3018245 : Blo 2011435 3018245 := bbase (se 4 (by rfl) ⟨282960, by rfl⟩ : syracuseStep 3018245 = 565921) (by norm_num)
theorem B2012163 : Blo 2011435 2012163 := bstep (se 1 (by rfl) ⟨1509122, by rfl⟩ : syracuseStep 2012163 = 3018245) B3018245
theorem B3395533 : Blo 2011435 3395533 := bbase (se 3 (by rfl) ⟨636662, by rfl⟩ : syracuseStep 3395533 = 1273325) (by norm_num)
theorem B4527377 : Blo 2011435 4527377 := bstep (se 2 (by rfl) ⟨1697766, by rfl⟩ : syracuseStep 4527377 = 3395533) B3395533
theorem B3018251 : Blo 2011435 3018251 := bstep (se 1 (by rfl) ⟨2263688, by rfl⟩ : syracuseStep 3018251 = 4527377) B4527377
theorem B2012167 : Blo 2011435 2012167 := bstep (se 1 (by rfl) ⟨1509125, by rfl⟩ : syracuseStep 2012167 = 3018251) B3018251
theorem B2263693 : Blo 2011435 2263693 := bbase (se 3 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 2263693 = 848885) (by norm_num)
theorem B3018257 : Blo 2011435 3018257 := bstep (se 2 (by rfl) ⟨1131846, by rfl⟩ : syracuseStep 3018257 = 2263693) B2263693
theorem B2012171 : Blo 2011435 2012171 := bstep (se 1 (by rfl) ⟨1509128, by rfl⟩ : syracuseStep 2012171 = 3018257) B3018257
theorem B6791093 : Blo 2011435 6791093 := bbase (se 5 (by rfl) ⟨318332, by rfl⟩ : syracuseStep 6791093 = 636665) (by norm_num)
theorem B4527395 : Blo 2011435 4527395 := bstep (se 1 (by rfl) ⟨3395546, by rfl⟩ : syracuseStep 4527395 = 6791093) B6791093
theorem B3018263 : Blo 2011435 3018263 := bstep (se 1 (by rfl) ⟨2263697, by rfl⟩ : syracuseStep 3018263 = 4527395) B4527395
theorem B2012175 : Blo 2011435 2012175 := bstep (se 1 (by rfl) ⟨1509131, by rfl⟩ : syracuseStep 2012175 = 3018263) B3018263
theorem B3018269 : Blo 2011435 3018269 := bbase (se 3 (by rfl) ⟨565925, by rfl⟩ : syracuseStep 3018269 = 1131851) (by norm_num)
theorem B2012179 : Blo 2011435 2012179 := bstep (se 1 (by rfl) ⟨1509134, by rfl⟩ : syracuseStep 2012179 = 3018269) B3018269
theorem B4527413 : Blo 2011435 4527413 := bbase (se 5 (by rfl) ⟨212222, by rfl⟩ : syracuseStep 4527413 = 424445) (by norm_num)
theorem B3018275 : Blo 2011435 3018275 := bstep (se 1 (by rfl) ⟨2263706, by rfl⟩ : syracuseStep 3018275 = 4527413) B4527413
theorem B2012183 : Blo 2011435 2012183 := bstep (se 1 (by rfl) ⟨1509137, by rfl⟩ : syracuseStep 2012183 = 3018275) B3018275
theorem B3626029 : Blo 2011435 3626029 := bbase (se 3 (by rfl) ⟨679880, by rfl⟩ : syracuseStep 3626029 = 1359761) (by norm_num)
theorem B19338821 : Blo 2011435 19338821 := bstep (se 4 (by rfl) ⟨1813014, by rfl⟩ : syracuseStep 19338821 = 3626029) B3626029
theorem B12892547 : Blo 2011435 12892547 := bstep (se 1 (by rfl) ⟨9669410, by rfl⟩ : syracuseStep 12892547 = 19338821) B19338821
theorem B8595031 : Blo 2011435 8595031 := bstep (se 1 (by rfl) ⟨6446273, by rfl⟩ : syracuseStep 8595031 = 12892547) B12892547
theorem B11460041 : Blo 2011435 11460041 := bstep (se 2 (by rfl) ⟨4297515, by rfl⟩ : syracuseStep 11460041 = 8595031) B8595031
theorem B7640027 : Blo 2011435 7640027 := bstep (se 1 (by rfl) ⟨5730020, by rfl⟩ : syracuseStep 7640027 = 11460041) B11460041
theorem B5093351 : Blo 2011435 5093351 := bstep (se 1 (by rfl) ⟨3820013, by rfl⟩ : syracuseStep 5093351 = 7640027) B7640027
theorem B3395567 : Blo 2011435 3395567 := bstep (se 1 (by rfl) ⟨2546675, by rfl⟩ : syracuseStep 3395567 = 5093351) B5093351
theorem B2263711 : Blo 2011435 2263711 := bstep (se 1 (by rfl) ⟨1697783, by rfl⟩ : syracuseStep 2263711 = 3395567) B3395567
theorem B3018281 : Blo 2011435 3018281 := bstep (se 2 (by rfl) ⟨1131855, by rfl⟩ : syracuseStep 3018281 = 2263711) B2263711
theorem B2012187 : Blo 2011435 2012187 := bstep (se 1 (by rfl) ⟨1509140, by rfl⟩ : syracuseStep 2012187 = 3018281) B3018281
theorem B2357641 : Blo 2011435 2357641 := bbase (se 2 (by rfl) ⟨884115, by rfl⟩ : syracuseStep 2357641 = 1768231) (by norm_num)
theorem B3143521 : Blo 2011435 3143521 := bstep (se 2 (by rfl) ⟨1178820, by rfl⟩ : syracuseStep 3143521 = 2357641) B2357641
theorem B4191361 : Blo 2011435 4191361 := bstep (se 2 (by rfl) ⟨1571760, by rfl⟩ : syracuseStep 4191361 = 3143521) B3143521
theorem B89415701 : Blo 2011435 89415701 := bstep (se 6 (by rfl) ⟨2095680, by rfl⟩ : syracuseStep 89415701 = 4191361) B4191361
theorem B59610467 : Blo 2011435 59610467 := bstep (se 1 (by rfl) ⟨44707850, by rfl⟩ : syracuseStep 59610467 = 89415701) B89415701
theorem B39740311 : Blo 2011435 39740311 := bstep (se 1 (by rfl) ⟨29805233, by rfl⟩ : syracuseStep 39740311 = 59610467) B59610467
theorem B52987081 : Blo 2011435 52987081 := bstep (se 2 (by rfl) ⟨19870155, by rfl⟩ : syracuseStep 52987081 = 39740311) B39740311
theorem B70649441 : Blo 2011435 70649441 := bstep (se 2 (by rfl) ⟨26493540, by rfl⟩ : syracuseStep 70649441 = 52987081) B52987081
theorem B47099627 : Blo 2011435 47099627 := bstep (se 1 (by rfl) ⟨35324720, by rfl⟩ : syracuseStep 47099627 = 70649441) B70649441
theorem B31399751 : Blo 2011435 31399751 := bstep (se 1 (by rfl) ⟨23549813, by rfl⟩ : syracuseStep 31399751 = 47099627) B47099627
theorem B20933167 : Blo 2011435 20933167 := bstep (se 1 (by rfl) ⟨15699875, by rfl⟩ : syracuseStep 20933167 = 31399751) B31399751
theorem B27910889 : Blo 2011435 27910889 := bstep (se 2 (by rfl) ⟨10466583, by rfl⟩ : syracuseStep 27910889 = 20933167) B20933167
theorem B18607259 : Blo 2011435 18607259 := bstep (se 1 (by rfl) ⟨13955444, by rfl⟩ : syracuseStep 18607259 = 27910889) B27910889
theorem B12404839 : Blo 2011435 12404839 := bstep (se 1 (by rfl) ⟨9303629, by rfl⟩ : syracuseStep 12404839 = 18607259) B18607259
theorem B16539785 : Blo 2011435 16539785 := bstep (se 2 (by rfl) ⟨6202419, by rfl⟩ : syracuseStep 16539785 = 12404839) B12404839
theorem B11026523 : Blo 2011435 11026523 := bstep (se 1 (by rfl) ⟨8269892, by rfl⟩ : syracuseStep 11026523 = 16539785) B16539785
theorem B7351015 : Blo 2011435 7351015 := bstep (se 1 (by rfl) ⟨5513261, by rfl⟩ : syracuseStep 7351015 = 11026523) B11026523
theorem B9801353 : Blo 2011435 9801353 := bstep (se 2 (by rfl) ⟨3675507, by rfl⟩ : syracuseStep 9801353 = 7351015) B7351015
theorem B6534235 : Blo 2011435 6534235 := bstep (se 1 (by rfl) ⟨4900676, by rfl⟩ : syracuseStep 6534235 = 9801353) B9801353
theorem B34849253 : Blo 2011435 34849253 := bstep (se 4 (by rfl) ⟨3267117, by rfl⟩ : syracuseStep 34849253 = 6534235) B6534235
theorem B23232835 : Blo 2011435 23232835 := bstep (se 1 (by rfl) ⟨17424626, by rfl⟩ : syracuseStep 23232835 = 34849253) B34849253
theorem B30977113 : Blo 2011435 30977113 := bstep (se 2 (by rfl) ⟨11616417, by rfl⟩ : syracuseStep 30977113 = 23232835) B23232835
theorem B41302817 : Blo 2011435 41302817 := bstep (se 2 (by rfl) ⟨15488556, by rfl⟩ : syracuseStep 41302817 = 30977113) B30977113
theorem B27535211 : Blo 2011435 27535211 := bstep (se 1 (by rfl) ⟨20651408, by rfl⟩ : syracuseStep 27535211 = 41302817) B41302817
theorem B18356807 : Blo 2011435 18356807 := bstep (se 1 (by rfl) ⟨13767605, by rfl⟩ : syracuseStep 18356807 = 27535211) B27535211
theorem B48951485 : Blo 2011435 48951485 := bstep (se 3 (by rfl) ⟨9178403, by rfl⟩ : syracuseStep 48951485 = 18356807) B18356807
theorem B32634323 : Blo 2011435 32634323 := bstep (se 1 (by rfl) ⟨24475742, by rfl⟩ : syracuseStep 32634323 = 48951485) B48951485
theorem B21756215 : Blo 2011435 21756215 := bstep (se 1 (by rfl) ⟨16317161, by rfl⟩ : syracuseStep 21756215 = 32634323) B32634323
theorem B14504143 : Blo 2011435 14504143 := bstep (se 1 (by rfl) ⟨10878107, by rfl⟩ : syracuseStep 14504143 = 21756215) B21756215
theorem B19338857 : Blo 2011435 19338857 := bstep (se 2 (by rfl) ⟨7252071, by rfl⟩ : syracuseStep 19338857 = 14504143) B14504143
theorem B12892571 : Blo 2011435 12892571 := bstep (se 1 (by rfl) ⟨9669428, by rfl⟩ : syracuseStep 12892571 = 19338857) B19338857
theorem B8595047 : Blo 2011435 8595047 := bstep (se 1 (by rfl) ⟨6446285, by rfl⟩ : syracuseStep 8595047 = 12892571) B12892571
theorem B5730031 : Blo 2011435 5730031 := bstep (se 1 (by rfl) ⟨4297523, by rfl⟩ : syracuseStep 5730031 = 8595047) B8595047
theorem B7640041 : Blo 2011435 7640041 := bstep (se 2 (by rfl) ⟨2865015, by rfl⟩ : syracuseStep 7640041 = 5730031) B5730031
theorem B10186721 : Blo 2011435 10186721 := bstep (se 2 (by rfl) ⟨3820020, by rfl⟩ : syracuseStep 10186721 = 7640041) B7640041
theorem B6791147 : Blo 2011435 6791147 := bstep (se 1 (by rfl) ⟨5093360, by rfl⟩ : syracuseStep 6791147 = 10186721) B10186721
theorem B4527431 : Blo 2011435 4527431 := bstep (se 1 (by rfl) ⟨3395573, by rfl⟩ : syracuseStep 4527431 = 6791147) B6791147
theorem B3018287 : Blo 2011435 3018287 := bstep (se 1 (by rfl) ⟨2263715, by rfl⟩ : syracuseStep 3018287 = 4527431) B4527431
theorem B2012191 : Blo 2011435 2012191 := bstep (se 1 (by rfl) ⟨1509143, by rfl⟩ : syracuseStep 2012191 = 3018287) B3018287
theorem B3018293 : Blo 2011435 3018293 := bbase (se 5 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 3018293 = 282965) (by norm_num)
theorem B2012195 : Blo 2011435 2012195 := bstep (se 1 (by rfl) ⟨1509146, by rfl⟩ : syracuseStep 2012195 = 3018293) B3018293
theorem B5093381 : Blo 2011435 5093381 := bbase (se 4 (by rfl) ⟨477504, by rfl⟩ : syracuseStep 5093381 = 955009) (by norm_num)
theorem B3395587 : Blo 2011435 3395587 := bstep (se 1 (by rfl) ⟨2546690, by rfl⟩ : syracuseStep 3395587 = 5093381) B5093381
theorem B4527449 : Blo 2011435 4527449 := bstep (se 2 (by rfl) ⟨1697793, by rfl⟩ : syracuseStep 4527449 = 3395587) B3395587
theorem B3018299 : Blo 2011435 3018299 := bstep (se 1 (by rfl) ⟨2263724, by rfl⟩ : syracuseStep 3018299 = 4527449) B4527449
theorem B2012199 : Blo 2011435 2012199 := bstep (se 1 (by rfl) ⟨1509149, by rfl⟩ : syracuseStep 2012199 = 3018299) B3018299
theorem B2263729 : Blo 2011435 2263729 := bbase (se 2 (by rfl) ⟨848898, by rfl⟩ : syracuseStep 2263729 = 1697797) (by norm_num)
theorem B3018305 : Blo 2011435 3018305 := bstep (se 2 (by rfl) ⟨1131864, by rfl⟩ : syracuseStep 3018305 = 2263729) B2263729
theorem B2012203 : Blo 2011435 2012203 := bstep (se 1 (by rfl) ⟨1509152, by rfl⟩ : syracuseStep 2012203 = 3018305) B3018305
theorem B2417377 : Blo 2011435 2417377 := bbase (se 2 (by rfl) ⟨906516, by rfl⟩ : syracuseStep 2417377 = 1813033) (by norm_num)
theorem B3223169 : Blo 2011435 3223169 := bstep (se 2 (by rfl) ⟨1208688, by rfl⟩ : syracuseStep 3223169 = 2417377) B2417377
theorem B2148779 : Blo 2011435 2148779 := bstep (se 1 (by rfl) ⟨1611584, by rfl⟩ : syracuseStep 2148779 = 3223169) B3223169
theorem B5730077 : Blo 2011435 5730077 := bstep (se 3 (by rfl) ⟨1074389, by rfl⟩ : syracuseStep 5730077 = 2148779) B2148779
theorem B3820051 : Blo 2011435 3820051 := bstep (se 1 (by rfl) ⟨2865038, by rfl⟩ : syracuseStep 3820051 = 5730077) B5730077
theorem B5093401 : Blo 2011435 5093401 := bstep (se 2 (by rfl) ⟨1910025, by rfl⟩ : syracuseStep 5093401 = 3820051) B3820051
theorem B6791201 : Blo 2011435 6791201 := bstep (se 2 (by rfl) ⟨2546700, by rfl⟩ : syracuseStep 6791201 = 5093401) B5093401
theorem B4527467 : Blo 2011435 4527467 := bstep (se 1 (by rfl) ⟨3395600, by rfl⟩ : syracuseStep 4527467 = 6791201) B6791201
theorem B3018311 : Blo 2011435 3018311 := bstep (se 1 (by rfl) ⟨2263733, by rfl⟩ : syracuseStep 3018311 = 4527467) B4527467
theorem B2012207 : Blo 2011435 2012207 := bstep (se 1 (by rfl) ⟨1509155, by rfl⟩ : syracuseStep 2012207 = 3018311) B3018311
theorem B3018317 : Blo 2011435 3018317 := bbase (se 3 (by rfl) ⟨565934, by rfl⟩ : syracuseStep 3018317 = 1131869) (by norm_num)
theorem B2012211 : Blo 2011435 2012211 := bstep (se 1 (by rfl) ⟨1509158, by rfl⟩ : syracuseStep 2012211 = 3018317) B3018317
theorem B4527485 : Blo 2011435 4527485 := bbase (se 3 (by rfl) ⟨848903, by rfl⟩ : syracuseStep 4527485 = 1697807) (by norm_num)
theorem B3018323 : Blo 2011435 3018323 := bstep (se 1 (by rfl) ⟨2263742, by rfl⟩ : syracuseStep 3018323 = 4527485) B4527485
theorem B2012215 : Blo 2011435 2012215 := bstep (se 1 (by rfl) ⟨1509161, by rfl⟩ : syracuseStep 2012215 = 3018323) B3018323
theorem B3395621 : Blo 2011435 3395621 := bbase (se 4 (by rfl) ⟨318339, by rfl⟩ : syracuseStep 3395621 = 636679) (by norm_num)
theorem B2263747 : Blo 2011435 2263747 := bstep (se 1 (by rfl) ⟨1697810, by rfl⟩ : syracuseStep 2263747 = 3395621) B3395621
theorem B3018329 : Blo 2011435 3018329 := bstep (se 2 (by rfl) ⟨1131873, by rfl⟩ : syracuseStep 3018329 = 2263747) B2263747
theorem B2012219 : Blo 2011435 2012219 := bstep (se 1 (by rfl) ⟨1509164, by rfl⟩ : syracuseStep 2012219 = 3018329) B3018329
theorem B2865061 : Blo 2011435 2865061 := bbase (se 4 (by rfl) ⟨268599, by rfl⟩ : syracuseStep 2865061 = 537199) (by norm_num)
theorem B15280325 : Blo 2011435 15280325 := bstep (se 4 (by rfl) ⟨1432530, by rfl⟩ : syracuseStep 15280325 = 2865061) B2865061
theorem B10186883 : Blo 2011435 10186883 := bstep (se 1 (by rfl) ⟨7640162, by rfl⟩ : syracuseStep 10186883 = 15280325) B15280325
theorem B6791255 : Blo 2011435 6791255 := bstep (se 1 (by rfl) ⟨5093441, by rfl⟩ : syracuseStep 6791255 = 10186883) B10186883
theorem B4527503 : Blo 2011435 4527503 := bstep (se 1 (by rfl) ⟨3395627, by rfl⟩ : syracuseStep 4527503 = 6791255) B6791255
theorem B3018335 : Blo 2011435 3018335 := bstep (se 1 (by rfl) ⟨2263751, by rfl⟩ : syracuseStep 3018335 = 4527503) B4527503
theorem B2012223 : Blo 2011435 2012223 := bstep (se 1 (by rfl) ⟨1509167, by rfl⟩ : syracuseStep 2012223 = 3018335) B3018335
theorem B3018341 : Blo 2011435 3018341 := bbase (se 4 (by rfl) ⟨282969, by rfl⟩ : syracuseStep 3018341 = 565939) (by norm_num)
theorem B2012227 : Blo 2011435 2012227 := bstep (se 1 (by rfl) ⟨1509170, by rfl⟩ : syracuseStep 2012227 = 3018341) B3018341
theorem B2148805 : Blo 2011435 2148805 := bbase (se 4 (by rfl) ⟨201450, by rfl⟩ : syracuseStep 2148805 = 402901) (by norm_num)
theorem B2865073 : Blo 2011435 2865073 := bstep (se 2 (by rfl) ⟨1074402, by rfl⟩ : syracuseStep 2865073 = 2148805) B2148805
theorem B3820097 : Blo 2011435 3820097 := bstep (se 2 (by rfl) ⟨1432536, by rfl⟩ : syracuseStep 3820097 = 2865073) B2865073
theorem B2546731 : Blo 2011435 2546731 := bstep (se 1 (by rfl) ⟨1910048, by rfl⟩ : syracuseStep 2546731 = 3820097) B3820097
theorem B3395641 : Blo 2011435 3395641 := bstep (se 2 (by rfl) ⟨1273365, by rfl⟩ : syracuseStep 3395641 = 2546731) B2546731
theorem B4527521 : Blo 2011435 4527521 := bstep (se 2 (by rfl) ⟨1697820, by rfl⟩ : syracuseStep 4527521 = 3395641) B3395641
theorem B3018347 : Blo 2011435 3018347 := bstep (se 1 (by rfl) ⟨2263760, by rfl⟩ : syracuseStep 3018347 = 4527521) B4527521
theorem B2012231 : Blo 2011435 2012231 := bstep (se 1 (by rfl) ⟨1509173, by rfl⟩ : syracuseStep 2012231 = 3018347) B3018347
theorem B2263765 : Blo 2011435 2263765 := bbase (se 7 (by rfl) ⟨26528, by rfl⟩ : syracuseStep 2263765 = 53057) (by norm_num)
theorem B3018353 : Blo 2011435 3018353 := bstep (se 2 (by rfl) ⟨1131882, by rfl⟩ : syracuseStep 3018353 = 2263765) B2263765
theorem B2012235 : Blo 2011435 2012235 := bstep (se 1 (by rfl) ⟨1509176, by rfl⟩ : syracuseStep 2012235 = 3018353) B3018353
theorem B2546741 : Blo 2011435 2546741 := bbase (se 5 (by rfl) ⟨119378, by rfl⟩ : syracuseStep 2546741 = 238757) (by norm_num)
theorem B6791309 : Blo 2011435 6791309 := bstep (se 3 (by rfl) ⟨1273370, by rfl⟩ : syracuseStep 6791309 = 2546741) B2546741
theorem B4527539 : Blo 2011435 4527539 := bstep (se 1 (by rfl) ⟨3395654, by rfl⟩ : syracuseStep 4527539 = 6791309) B6791309
theorem B3018359 : Blo 2011435 3018359 := bstep (se 1 (by rfl) ⟨2263769, by rfl⟩ : syracuseStep 3018359 = 4527539) B4527539
theorem B2012239 : Blo 2011435 2012239 := bstep (se 1 (by rfl) ⟨1509179, by rfl⟩ : syracuseStep 2012239 = 3018359) B3018359
theorem B3018365 : Blo 2011435 3018365 := bbase (se 3 (by rfl) ⟨565943, by rfl⟩ : syracuseStep 3018365 = 1131887) (by norm_num)
theorem B2012243 : Blo 2011435 2012243 := bstep (se 1 (by rfl) ⟨1509182, by rfl⟩ : syracuseStep 2012243 = 3018365) B3018365
theorem B4527557 : Blo 2011435 4527557 := bbase (se 4 (by rfl) ⟨424458, by rfl⟩ : syracuseStep 4527557 = 848917) (by norm_num)
theorem B3018371 : Blo 2011435 3018371 := bstep (se 1 (by rfl) ⟨2263778, by rfl⟩ : syracuseStep 3018371 = 4527557) B4527557
theorem B2012247 : Blo 2011435 2012247 := bstep (se 1 (by rfl) ⟨1509185, by rfl⟩ : syracuseStep 2012247 = 3018371) B3018371
theorem B4079413 : Blo 2011435 4079413 := bbase (se 5 (by rfl) ⟨191222, by rfl⟩ : syracuseStep 4079413 = 382445) (by norm_num)
theorem B21756869 : Blo 2011435 21756869 := bstep (se 4 (by rfl) ⟨2039706, by rfl⟩ : syracuseStep 21756869 = 4079413) B4079413
theorem B14504579 : Blo 2011435 14504579 := bstep (se 1 (by rfl) ⟨10878434, by rfl⟩ : syracuseStep 14504579 = 21756869) B21756869
theorem B9669719 : Blo 2011435 9669719 := bstep (se 1 (by rfl) ⟨7252289, by rfl⟩ : syracuseStep 9669719 = 14504579) B14504579
theorem B6446479 : Blo 2011435 6446479 := bstep (se 1 (by rfl) ⟨4834859, by rfl⟩ : syracuseStep 6446479 = 9669719) B9669719
theorem B8595305 : Blo 2011435 8595305 := bstep (se 2 (by rfl) ⟨3223239, by rfl⟩ : syracuseStep 8595305 = 6446479) B6446479
theorem B5730203 : Blo 2011435 5730203 := bstep (se 1 (by rfl) ⟨4297652, by rfl⟩ : syracuseStep 5730203 = 8595305) B8595305
theorem B3820135 : Blo 2011435 3820135 := bstep (se 1 (by rfl) ⟨2865101, by rfl⟩ : syracuseStep 3820135 = 5730203) B5730203
theorem B5093513 : Blo 2011435 5093513 := bstep (se 2 (by rfl) ⟨1910067, by rfl⟩ : syracuseStep 5093513 = 3820135) B3820135
theorem B3395675 : Blo 2011435 3395675 := bstep (se 1 (by rfl) ⟨2546756, by rfl⟩ : syracuseStep 3395675 = 5093513) B5093513
theorem B2263783 : Blo 2011435 2263783 := bstep (se 1 (by rfl) ⟨1697837, by rfl⟩ : syracuseStep 2263783 = 3395675) B3395675
theorem B3018377 : Blo 2011435 3018377 := bstep (se 2 (by rfl) ⟨1131891, by rfl⟩ : syracuseStep 3018377 = 2263783) B2263783
theorem B2012251 : Blo 2011435 2012251 := bstep (se 1 (by rfl) ⟨1509188, by rfl⟩ : syracuseStep 2012251 = 3018377) B3018377
theorem B10187045 : Blo 2011435 10187045 := bbase (se 4 (by rfl) ⟨955035, by rfl⟩ : syracuseStep 10187045 = 1910071) (by norm_num)
theorem B6791363 : Blo 2011435 6791363 := bstep (se 1 (by rfl) ⟨5093522, by rfl⟩ : syracuseStep 6791363 = 10187045) B10187045
theorem B4527575 : Blo 2011435 4527575 := bstep (se 1 (by rfl) ⟨3395681, by rfl⟩ : syracuseStep 4527575 = 6791363) B6791363
theorem B3018383 : Blo 2011435 3018383 := bstep (se 1 (by rfl) ⟨2263787, by rfl⟩ : syracuseStep 3018383 = 4527575) B4527575
theorem B2012255 : Blo 2011435 2012255 := bstep (se 1 (by rfl) ⟨1509191, by rfl⟩ : syracuseStep 2012255 = 3018383) B3018383
theorem B3018389 : Blo 2011435 3018389 := bbase (se 6 (by rfl) ⟨70743, by rfl⟩ : syracuseStep 3018389 = 141487) (by norm_num)
theorem B2012259 : Blo 2011435 2012259 := bstep (se 1 (by rfl) ⟨1509194, by rfl⟩ : syracuseStep 2012259 = 3018389) B3018389
theorem B8712629 : Blo 2011435 8712629 := bbase (se 5 (by rfl) ⟨408404, by rfl⟩ : syracuseStep 8712629 = 816809) (by norm_num)
theorem B5808419 : Blo 2011435 5808419 := bstep (se 1 (by rfl) ⟨4356314, by rfl⟩ : syracuseStep 5808419 = 8712629) B8712629
theorem B3872279 : Blo 2011435 3872279 := bstep (se 1 (by rfl) ⟨2904209, by rfl⟩ : syracuseStep 3872279 = 5808419) B5808419
theorem B2581519 : Blo 2011435 2581519 := bstep (se 1 (by rfl) ⟨1936139, by rfl⟩ : syracuseStep 2581519 = 3872279) B3872279
theorem B3442025 : Blo 2011435 3442025 := bstep (se 2 (by rfl) ⟨1290759, by rfl⟩ : syracuseStep 3442025 = 2581519) B2581519
theorem B9178733 : Blo 2011435 9178733 := bstep (se 3 (by rfl) ⟨1721012, by rfl⟩ : syracuseStep 9178733 = 3442025) B3442025
theorem B6119155 : Blo 2011435 6119155 := bstep (se 1 (by rfl) ⟨4589366, by rfl⟩ : syracuseStep 6119155 = 9178733) B9178733
theorem B32635493 : Blo 2011435 32635493 := bstep (se 4 (by rfl) ⟨3059577, by rfl⟩ : syracuseStep 32635493 = 6119155) B6119155
theorem B21756995 : Blo 2011435 21756995 := bstep (se 1 (by rfl) ⟨16317746, by rfl⟩ : syracuseStep 21756995 = 32635493) B32635493
theorem B14504663 : Blo 2011435 14504663 := bstep (se 1 (by rfl) ⟨10878497, by rfl⟩ : syracuseStep 14504663 = 21756995) B21756995
theorem B9669775 : Blo 2011435 9669775 := bstep (se 1 (by rfl) ⟨7252331, by rfl⟩ : syracuseStep 9669775 = 14504663) B14504663
theorem B12893033 : Blo 2011435 12893033 := bstep (se 2 (by rfl) ⟨4834887, by rfl⟩ : syracuseStep 12893033 = 9669775) B9669775
theorem B8595355 : Blo 2011435 8595355 := bstep (se 1 (by rfl) ⟨6446516, by rfl⟩ : syracuseStep 8595355 = 12893033) B12893033
theorem B11460473 : Blo 2011435 11460473 := bstep (se 2 (by rfl) ⟨4297677, by rfl⟩ : syracuseStep 11460473 = 8595355) B8595355
theorem B7640315 : Blo 2011435 7640315 := bstep (se 1 (by rfl) ⟨5730236, by rfl⟩ : syracuseStep 7640315 = 11460473) B11460473
theorem B5093543 : Blo 2011435 5093543 := bstep (se 1 (by rfl) ⟨3820157, by rfl⟩ : syracuseStep 5093543 = 7640315) B7640315
theorem B3395695 : Blo 2011435 3395695 := bstep (se 1 (by rfl) ⟨2546771, by rfl⟩ : syracuseStep 3395695 = 5093543) B5093543
theorem B4527593 : Blo 2011435 4527593 := bstep (se 2 (by rfl) ⟨1697847, by rfl⟩ : syracuseStep 4527593 = 3395695) B3395695
theorem B3018395 : Blo 2011435 3018395 := bstep (se 1 (by rfl) ⟨2263796, by rfl⟩ : syracuseStep 3018395 = 4527593) B4527593
theorem B2012263 : Blo 2011435 2012263 := bstep (se 1 (by rfl) ⟨1509197, by rfl⟩ : syracuseStep 2012263 = 3018395) B3018395
theorem B2263801 : Blo 2011435 2263801 := bbase (se 2 (by rfl) ⟨848925, by rfl⟩ : syracuseStep 2263801 = 1697851) (by norm_num)
theorem B3018401 : Blo 2011435 3018401 := bstep (se 2 (by rfl) ⟨1131900, by rfl⟩ : syracuseStep 3018401 = 2263801) B2263801
theorem B2012267 : Blo 2011435 2012267 := bstep (se 1 (by rfl) ⟨1509200, by rfl⟩ : syracuseStep 2012267 = 3018401) B3018401
theorem B2904221 : Blo 2011435 2904221 := bbase (se 3 (by rfl) ⟨544541, by rfl⟩ : syracuseStep 2904221 = 1089083) (by norm_num)
theorem B7744589 : Blo 2011435 7744589 := bstep (se 3 (by rfl) ⟨1452110, by rfl⟩ : syracuseStep 7744589 = 2904221) B2904221
theorem B5163059 : Blo 2011435 5163059 := bstep (se 1 (by rfl) ⟨3872294, by rfl⟩ : syracuseStep 5163059 = 7744589) B7744589
theorem B13768157 : Blo 2011435 13768157 := bstep (se 3 (by rfl) ⟨2581529, by rfl⟩ : syracuseStep 13768157 = 5163059) B5163059
theorem B9178771 : Blo 2011435 9178771 := bstep (se 1 (by rfl) ⟨6884078, by rfl⟩ : syracuseStep 9178771 = 13768157) B13768157
theorem B12238361 : Blo 2011435 12238361 := bstep (se 2 (by rfl) ⟨4589385, by rfl⟩ : syracuseStep 12238361 = 9178771) B9178771
theorem B8158907 : Blo 2011435 8158907 := bstep (se 1 (by rfl) ⟨6119180, by rfl⟩ : syracuseStep 8158907 = 12238361) B12238361
theorem B5439271 : Blo 2011435 5439271 := bstep (se 1 (by rfl) ⟨4079453, by rfl⟩ : syracuseStep 5439271 = 8158907) B8158907
theorem B7252361 : Blo 2011435 7252361 := bstep (se 2 (by rfl) ⟨2719635, by rfl⟩ : syracuseStep 7252361 = 5439271) B5439271
theorem B4834907 : Blo 2011435 4834907 := bstep (se 1 (by rfl) ⟨3626180, by rfl⟩ : syracuseStep 4834907 = 7252361) B7252361
theorem B3223271 : Blo 2011435 3223271 := bstep (se 1 (by rfl) ⟨2417453, by rfl⟩ : syracuseStep 3223271 = 4834907) B4834907
theorem B8595389 : Blo 2011435 8595389 := bstep (se 3 (by rfl) ⟨1611635, by rfl⟩ : syracuseStep 8595389 = 3223271) B3223271
theorem B5730259 : Blo 2011435 5730259 := bstep (se 1 (by rfl) ⟨4297694, by rfl⟩ : syracuseStep 5730259 = 8595389) B8595389
theorem B7640345 : Blo 2011435 7640345 := bstep (se 2 (by rfl) ⟨2865129, by rfl⟩ : syracuseStep 7640345 = 5730259) B5730259
theorem B5093563 : Blo 2011435 5093563 := bstep (se 1 (by rfl) ⟨3820172, by rfl⟩ : syracuseStep 5093563 = 7640345) B7640345
theorem B6791417 : Blo 2011435 6791417 := bstep (se 2 (by rfl) ⟨2546781, by rfl⟩ : syracuseStep 6791417 = 5093563) B5093563
theorem B4527611 : Blo 2011435 4527611 := bstep (se 1 (by rfl) ⟨3395708, by rfl⟩ : syracuseStep 4527611 = 6791417) B6791417
theorem B3018407 : Blo 2011435 3018407 := bstep (se 1 (by rfl) ⟨2263805, by rfl⟩ : syracuseStep 3018407 = 4527611) B4527611
theorem B2012271 : Blo 2011435 2012271 := bstep (se 1 (by rfl) ⟨1509203, by rfl⟩ : syracuseStep 2012271 = 3018407) B3018407
theorem B3018413 : Blo 2011435 3018413 := bbase (se 3 (by rfl) ⟨565952, by rfl⟩ : syracuseStep 3018413 = 1131905) (by norm_num)
theorem B2012275 : Blo 2011435 2012275 := bstep (se 1 (by rfl) ⟨1509206, by rfl⟩ : syracuseStep 2012275 = 3018413) B3018413
theorem B4527629 : Blo 2011435 4527629 := bbase (se 3 (by rfl) ⟨848930, by rfl⟩ : syracuseStep 4527629 = 1697861) (by norm_num)
theorem B3018419 : Blo 2011435 3018419 := bstep (se 1 (by rfl) ⟨2263814, by rfl⟩ : syracuseStep 3018419 = 4527629) B4527629
theorem B2012279 : Blo 2011435 2012279 := bstep (se 1 (by rfl) ⟨1509209, by rfl⟩ : syracuseStep 2012279 = 3018419) B3018419
theorem B2546797 : Blo 2011435 2546797 := bbase (se 3 (by rfl) ⟨477524, by rfl⟩ : syracuseStep 2546797 = 955049) (by norm_num)
theorem B3395729 : Blo 2011435 3395729 := bstep (se 2 (by rfl) ⟨1273398, by rfl⟩ : syracuseStep 3395729 = 2546797) B2546797
theorem B2263819 : Blo 2011435 2263819 := bstep (se 1 (by rfl) ⟨1697864, by rfl⟩ : syracuseStep 2263819 = 3395729) B3395729
theorem B3018425 : Blo 2011435 3018425 := bstep (se 2 (by rfl) ⟨1131909, by rfl⟩ : syracuseStep 3018425 = 2263819) B2263819
theorem B2012283 : Blo 2011435 2012283 := bstep (se 1 (by rfl) ⟨1509212, by rfl⟩ : syracuseStep 2012283 = 3018425) B3018425
theorem B4079485 : Blo 2011435 4079485 := bbase (se 3 (by rfl) ⟨764903, by rfl⟩ : syracuseStep 4079485 = 1529807) (by norm_num)
theorem B5439313 : Blo 2011435 5439313 := bstep (se 2 (by rfl) ⟨2039742, by rfl⟩ : syracuseStep 5439313 = 4079485) B4079485
theorem B7252417 : Blo 2011435 7252417 := bstep (se 2 (by rfl) ⟨2719656, by rfl⟩ : syracuseStep 7252417 = 5439313) B5439313
theorem B9669889 : Blo 2011435 9669889 := bstep (se 2 (by rfl) ⟨3626208, by rfl⟩ : syracuseStep 9669889 = 7252417) B7252417
theorem B12893185 : Blo 2011435 12893185 := bstep (se 2 (by rfl) ⟨4834944, by rfl⟩ : syracuseStep 12893185 = 9669889) B9669889
theorem B17190913 : Blo 2011435 17190913 := bstep (se 2 (by rfl) ⟨6446592, by rfl⟩ : syracuseStep 17190913 = 12893185) B12893185
theorem B22921217 : Blo 2011435 22921217 := bstep (se 2 (by rfl) ⟨8595456, by rfl⟩ : syracuseStep 22921217 = 17190913) B17190913
theorem B15280811 : Blo 2011435 15280811 := bstep (se 1 (by rfl) ⟨11460608, by rfl⟩ : syracuseStep 15280811 = 22921217) B22921217
theorem B10187207 : Blo 2011435 10187207 := bstep (se 1 (by rfl) ⟨7640405, by rfl⟩ : syracuseStep 10187207 = 15280811) B15280811
theorem B6791471 : Blo 2011435 6791471 := bstep (se 1 (by rfl) ⟨5093603, by rfl⟩ : syracuseStep 6791471 = 10187207) B10187207
theorem B4527647 : Blo 2011435 4527647 := bstep (se 1 (by rfl) ⟨3395735, by rfl⟩ : syracuseStep 4527647 = 6791471) B6791471
theorem B3018431 : Blo 2011435 3018431 := bstep (se 1 (by rfl) ⟨2263823, by rfl⟩ : syracuseStep 3018431 = 4527647) B4527647
theorem B2012287 : Blo 2011435 2012287 := bstep (se 1 (by rfl) ⟨1509215, by rfl⟩ : syracuseStep 2012287 = 3018431) B3018431
theorem B3018437 : Blo 2011435 3018437 := bbase (se 4 (by rfl) ⟨282978, by rfl⟩ : syracuseStep 3018437 = 565957) (by norm_num)
theorem B2012291 : Blo 2011435 2012291 := bstep (se 1 (by rfl) ⟨1509218, by rfl⟩ : syracuseStep 2012291 = 3018437) B3018437
theorem B3395749 : Blo 2011435 3395749 := bbase (se 4 (by rfl) ⟨318351, by rfl⟩ : syracuseStep 3395749 = 636703) (by norm_num)
theorem B4527665 : Blo 2011435 4527665 := bstep (se 2 (by rfl) ⟨1697874, by rfl⟩ : syracuseStep 4527665 = 3395749) B3395749
theorem B3018443 : Blo 2011435 3018443 := bstep (se 1 (by rfl) ⟨2263832, by rfl⟩ : syracuseStep 3018443 = 4527665) B4527665
theorem B2012295 : Blo 2011435 2012295 := bstep (se 1 (by rfl) ⟨1509221, by rfl⟩ : syracuseStep 2012295 = 3018443) B3018443
theorem B2263837 : Blo 2011435 2263837 := bbase (se 3 (by rfl) ⟨424469, by rfl⟩ : syracuseStep 2263837 = 848939) (by norm_num)
theorem B3018449 : Blo 2011435 3018449 := bstep (se 2 (by rfl) ⟨1131918, by rfl⟩ : syracuseStep 3018449 = 2263837) B2263837
theorem B2012299 : Blo 2011435 2012299 := bstep (se 1 (by rfl) ⟨1509224, by rfl⟩ : syracuseStep 2012299 = 3018449) B3018449
theorem B6791525 : Blo 2011435 6791525 := bbase (se 4 (by rfl) ⟨636705, by rfl⟩ : syracuseStep 6791525 = 1273411) (by norm_num)
theorem B4527683 : Blo 2011435 4527683 := bstep (se 1 (by rfl) ⟨3395762, by rfl⟩ : syracuseStep 4527683 = 6791525) B6791525
theorem B3018455 : Blo 2011435 3018455 := bstep (se 1 (by rfl) ⟨2263841, by rfl⟩ : syracuseStep 3018455 = 4527683) B4527683
theorem B2012303 : Blo 2011435 2012303 := bstep (se 1 (by rfl) ⟨1509227, by rfl⟩ : syracuseStep 2012303 = 3018455) B3018455
theorem B3018461 : Blo 2011435 3018461 := bbase (se 3 (by rfl) ⟨565961, by rfl⟩ : syracuseStep 3018461 = 1131923) (by norm_num)
theorem B2012307 : Blo 2011435 2012307 := bstep (se 1 (by rfl) ⟨1509230, by rfl⟩ : syracuseStep 2012307 = 3018461) B3018461
theorem B4527701 : Blo 2011435 4527701 := bbase (se 8 (by rfl) ⟨26529, by rfl⟩ : syracuseStep 4527701 = 53059) (by norm_num)
theorem B3018467 : Blo 2011435 3018467 := bstep (se 1 (by rfl) ⟨2263850, by rfl⟩ : syracuseStep 3018467 = 4527701) B4527701
theorem B2012311 : Blo 2011435 2012311 := bstep (se 1 (by rfl) ⟨1509233, by rfl⟩ : syracuseStep 2012311 = 3018467) B3018467
theorem B4297789 : Blo 2011435 4297789 := bbase (se 3 (by rfl) ⟨805835, by rfl⟩ : syracuseStep 4297789 = 1611671) (by norm_num)
theorem B5730385 : Blo 2011435 5730385 := bstep (se 2 (by rfl) ⟨2148894, by rfl⟩ : syracuseStep 5730385 = 4297789) B4297789
theorem B7640513 : Blo 2011435 7640513 := bstep (se 2 (by rfl) ⟨2865192, by rfl⟩ : syracuseStep 7640513 = 5730385) B5730385
theorem B5093675 : Blo 2011435 5093675 := bstep (se 1 (by rfl) ⟨3820256, by rfl⟩ : syracuseStep 5093675 = 7640513) B7640513
theorem B3395783 : Blo 2011435 3395783 := bstep (se 1 (by rfl) ⟨2546837, by rfl⟩ : syracuseStep 3395783 = 5093675) B5093675
theorem B2263855 : Blo 2011435 2263855 := bstep (se 1 (by rfl) ⟨1697891, by rfl⟩ : syracuseStep 2263855 = 3395783) B3395783
theorem B3018473 : Blo 2011435 3018473 := bstep (se 2 (by rfl) ⟨1131927, by rfl⟩ : syracuseStep 3018473 = 2263855) B2263855
theorem B2012315 : Blo 2011435 2012315 := bstep (se 1 (by rfl) ⟨1509236, by rfl⟩ : syracuseStep 2012315 = 3018473) B3018473
theorem B2178217 : Blo 2011435 2178217 := bbase (se 2 (by rfl) ⟨816831, by rfl⟩ : syracuseStep 2178217 = 1633663) (by norm_num)
theorem B11617157 : Blo 2011435 11617157 := bstep (se 4 (by rfl) ⟨1089108, by rfl⟩ : syracuseStep 11617157 = 2178217) B2178217
theorem B7744771 : Blo 2011435 7744771 := bstep (se 1 (by rfl) ⟨5808578, by rfl⟩ : syracuseStep 7744771 = 11617157) B11617157
theorem B10326361 : Blo 2011435 10326361 := bstep (se 2 (by rfl) ⟨3872385, by rfl⟩ : syracuseStep 10326361 = 7744771) B7744771
theorem B13768481 : Blo 2011435 13768481 := bstep (se 2 (by rfl) ⟨5163180, by rfl⟩ : syracuseStep 13768481 = 10326361) B10326361
theorem B36715949 : Blo 2011435 36715949 := bstep (se 3 (by rfl) ⟨6884240, by rfl⟩ : syracuseStep 36715949 = 13768481) B13768481
theorem B24477299 : Blo 2011435 24477299 := bstep (se 1 (by rfl) ⟨18357974, by rfl⟩ : syracuseStep 24477299 = 36715949) B36715949
theorem B16318199 : Blo 2011435 16318199 := bstep (se 1 (by rfl) ⟨12238649, by rfl⟩ : syracuseStep 16318199 = 24477299) B24477299
theorem B10878799 : Blo 2011435 10878799 := bstep (se 1 (by rfl) ⟨8159099, by rfl⟩ : syracuseStep 10878799 = 16318199) B16318199
theorem B14505065 : Blo 2011435 14505065 := bstep (se 2 (by rfl) ⟨5439399, by rfl⟩ : syracuseStep 14505065 = 10878799) B10878799
theorem B9670043 : Blo 2011435 9670043 := bstep (se 1 (by rfl) ⟨7252532, by rfl⟩ : syracuseStep 9670043 = 14505065) B14505065
theorem B25786781 : Blo 2011435 25786781 := bstep (se 3 (by rfl) ⟨4835021, by rfl⟩ : syracuseStep 25786781 = 9670043) B9670043
theorem B17191187 : Blo 2011435 17191187 := bstep (se 1 (by rfl) ⟨12893390, by rfl⟩ : syracuseStep 17191187 = 25786781) B25786781
theorem B11460791 : Blo 2011435 11460791 := bstep (se 1 (by rfl) ⟨8595593, by rfl⟩ : syracuseStep 11460791 = 17191187) B17191187
theorem B7640527 : Blo 2011435 7640527 := bstep (se 1 (by rfl) ⟨5730395, by rfl⟩ : syracuseStep 7640527 = 11460791) B11460791
theorem B10187369 : Blo 2011435 10187369 := bstep (se 2 (by rfl) ⟨3820263, by rfl⟩ : syracuseStep 10187369 = 7640527) B7640527
theorem B6791579 : Blo 2011435 6791579 := bstep (se 1 (by rfl) ⟨5093684, by rfl⟩ : syracuseStep 6791579 = 10187369) B10187369
theorem B4527719 : Blo 2011435 4527719 := bstep (se 1 (by rfl) ⟨3395789, by rfl⟩ : syracuseStep 4527719 = 6791579) B6791579
theorem B3018479 : Blo 2011435 3018479 := bstep (se 1 (by rfl) ⟨2263859, by rfl⟩ : syracuseStep 3018479 = 4527719) B4527719
theorem B2012319 : Blo 2011435 2012319 := bstep (se 1 (by rfl) ⟨1509239, by rfl⟩ : syracuseStep 2012319 = 3018479) B3018479
theorem B3018485 : Blo 2011435 3018485 := bbase (se 5 (by rfl) ⟨141491, by rfl⟩ : syracuseStep 3018485 = 282983) (by norm_num)
theorem B2012323 : Blo 2011435 2012323 := bstep (se 1 (by rfl) ⟨1509242, by rfl⟩ : syracuseStep 2012323 = 3018485) B3018485
theorem B2417521 : Blo 2011435 2417521 := bbase (se 2 (by rfl) ⟨906570, by rfl⟩ : syracuseStep 2417521 = 1813141) (by norm_num)
theorem B3223361 : Blo 2011435 3223361 := bstep (se 2 (by rfl) ⟨1208760, by rfl⟩ : syracuseStep 3223361 = 2417521) B2417521
theorem B8595629 : Blo 2011435 8595629 := bstep (se 3 (by rfl) ⟨1611680, by rfl⟩ : syracuseStep 8595629 = 3223361) B3223361
theorem B5730419 : Blo 2011435 5730419 := bstep (se 1 (by rfl) ⟨4297814, by rfl⟩ : syracuseStep 5730419 = 8595629) B8595629
theorem B3820279 : Blo 2011435 3820279 := bstep (se 1 (by rfl) ⟨2865209, by rfl⟩ : syracuseStep 3820279 = 5730419) B5730419
theorem B5093705 : Blo 2011435 5093705 := bstep (se 2 (by rfl) ⟨1910139, by rfl⟩ : syracuseStep 5093705 = 3820279) B3820279
theorem B3395803 : Blo 2011435 3395803 := bstep (se 1 (by rfl) ⟨2546852, by rfl⟩ : syracuseStep 3395803 = 5093705) B5093705
theorem B4527737 : Blo 2011435 4527737 := bstep (se 2 (by rfl) ⟨1697901, by rfl⟩ : syracuseStep 4527737 = 3395803) B3395803
theorem B3018491 : Blo 2011435 3018491 := bstep (se 1 (by rfl) ⟨2263868, by rfl⟩ : syracuseStep 3018491 = 4527737) B4527737
theorem B2012327 : Blo 2011435 2012327 := bstep (se 1 (by rfl) ⟨1509245, by rfl⟩ : syracuseStep 2012327 = 3018491) B3018491
theorem B2263873 : Blo 2011435 2263873 := bbase (se 2 (by rfl) ⟨848952, by rfl⟩ : syracuseStep 2263873 = 1697905) (by norm_num)
theorem B3018497 : Blo 2011435 3018497 := bstep (se 2 (by rfl) ⟨1131936, by rfl⟩ : syracuseStep 3018497 = 2263873) B2263873
theorem B2012331 : Blo 2011435 2012331 := bstep (se 1 (by rfl) ⟨1509248, by rfl⟩ : syracuseStep 2012331 = 3018497) B3018497
theorem B5093725 : Blo 2011435 5093725 := bbase (se 3 (by rfl) ⟨955073, by rfl⟩ : syracuseStep 5093725 = 1910147) (by norm_num)
theorem B6791633 : Blo 2011435 6791633 := bstep (se 2 (by rfl) ⟨2546862, by rfl⟩ : syracuseStep 6791633 = 5093725) B5093725
theorem B4527755 : Blo 2011435 4527755 := bstep (se 1 (by rfl) ⟨3395816, by rfl⟩ : syracuseStep 4527755 = 6791633) B6791633
theorem B3018503 : Blo 2011435 3018503 := bstep (se 1 (by rfl) ⟨2263877, by rfl⟩ : syracuseStep 3018503 = 4527755) B4527755
theorem B2012335 : Blo 2011435 2012335 := bstep (se 1 (by rfl) ⟨1509251, by rfl⟩ : syracuseStep 2012335 = 3018503) B3018503
theorem B3018509 : Blo 2011435 3018509 := bbase (se 3 (by rfl) ⟨565970, by rfl⟩ : syracuseStep 3018509 = 1131941) (by norm_num)
theorem B2012339 : Blo 2011435 2012339 := bstep (se 1 (by rfl) ⟨1509254, by rfl⟩ : syracuseStep 2012339 = 3018509) B3018509
theorem B4527773 : Blo 2011435 4527773 := bbase (se 3 (by rfl) ⟨848957, by rfl⟩ : syracuseStep 4527773 = 1697915) (by norm_num)
theorem B3018515 : Blo 2011435 3018515 := bstep (se 1 (by rfl) ⟨2263886, by rfl⟩ : syracuseStep 3018515 = 4527773) B4527773
theorem B2012343 : Blo 2011435 2012343 := bstep (se 1 (by rfl) ⟨1509257, by rfl⟩ : syracuseStep 2012343 = 3018515) B3018515
theorem B3395837 : Blo 2011435 3395837 := bbase (se 3 (by rfl) ⟨636719, by rfl⟩ : syracuseStep 3395837 = 1273439) (by norm_num)
theorem B2263891 : Blo 2011435 2263891 := bstep (se 1 (by rfl) ⟨1697918, by rfl⟩ : syracuseStep 2263891 = 3395837) B3395837
theorem B3018521 : Blo 2011435 3018521 := bstep (se 2 (by rfl) ⟨1131945, by rfl⟩ : syracuseStep 3018521 = 2263891) B2263891
theorem B2012347 : Blo 2011435 2012347 := bstep (se 1 (by rfl) ⟨1509260, by rfl⟩ : syracuseStep 2012347 = 3018521) B3018521
theorem B4306853 : Blo 2011435 4306853 := bbase (se 4 (by rfl) ⟨403767, by rfl⟩ : syracuseStep 4306853 = 807535) (by norm_num)
theorem B2871235 : Blo 2011435 2871235 := bstep (se 1 (by rfl) ⟨2153426, by rfl⟩ : syracuseStep 2871235 = 4306853) B4306853
theorem B3828313 : Blo 2011435 3828313 := bstep (se 2 (by rfl) ⟨1435617, by rfl⟩ : syracuseStep 3828313 = 2871235) B2871235
theorem B5104417 : Blo 2011435 5104417 := bstep (se 2 (by rfl) ⟨1914156, by rfl⟩ : syracuseStep 5104417 = 3828313) B3828313
theorem B6805889 : Blo 2011435 6805889 := bstep (se 2 (by rfl) ⟨2552208, by rfl⟩ : syracuseStep 6805889 = 5104417) B5104417
theorem B4537259 : Blo 2011435 4537259 := bstep (se 1 (by rfl) ⟨3402944, by rfl⟩ : syracuseStep 4537259 = 6805889) B6805889
theorem B48397429 : Blo 2011435 48397429 := bstep (se 5 (by rfl) ⟨2268629, by rfl⟩ : syracuseStep 48397429 = 4537259) B4537259
theorem B64529905 : Blo 2011435 64529905 := bstep (se 2 (by rfl) ⟨24198714, by rfl⟩ : syracuseStep 64529905 = 48397429) B48397429
theorem B86039873 : Blo 2011435 86039873 := bstep (se 2 (by rfl) ⟨32264952, by rfl⟩ : syracuseStep 86039873 = 64529905) B64529905
theorem B57359915 : Blo 2011435 57359915 := bstep (se 1 (by rfl) ⟨43019936, by rfl⟩ : syracuseStep 57359915 = 86039873) B86039873
theorem B38239943 : Blo 2011435 38239943 := bstep (se 1 (by rfl) ⟨28679957, by rfl⟩ : syracuseStep 38239943 = 57359915) B57359915
theorem B101973181 : Blo 2011435 101973181 := bstep (se 3 (by rfl) ⟨19119971, by rfl⟩ : syracuseStep 101973181 = 38239943) B38239943
theorem B135964241 : Blo 2011435 135964241 := bstep (se 2 (by rfl) ⟨50986590, by rfl⟩ : syracuseStep 135964241 = 101973181) B101973181
theorem B90642827 : Blo 2011435 90642827 := bstep (se 1 (by rfl) ⟨67982120, by rfl⟩ : syracuseStep 90642827 = 135964241) B135964241
theorem B60428551 : Blo 2011435 60428551 := bstep (se 1 (by rfl) ⟨45321413, by rfl⟩ : syracuseStep 60428551 = 90642827) B90642827
theorem B80571401 : Blo 2011435 80571401 := bstep (se 2 (by rfl) ⟨30214275, by rfl⟩ : syracuseStep 80571401 = 60428551) B60428551
theorem B53714267 : Blo 2011435 53714267 := bstep (se 1 (by rfl) ⟨40285700, by rfl⟩ : syracuseStep 53714267 = 80571401) B80571401
theorem B35809511 : Blo 2011435 35809511 := bstep (se 1 (by rfl) ⟨26857133, by rfl⟩ : syracuseStep 35809511 = 53714267) B53714267
theorem B95492029 : Blo 2011435 95492029 := bstep (se 3 (by rfl) ⟨17904755, by rfl⟩ : syracuseStep 95492029 = 35809511) B35809511
theorem B127322705 : Blo 2011435 127322705 := bstep (se 2 (by rfl) ⟨47746014, by rfl⟩ : syracuseStep 127322705 = 95492029) B95492029
theorem B84881803 : Blo 2011435 84881803 := bstep (se 1 (by rfl) ⟨63661352, by rfl⟩ : syracuseStep 84881803 = 127322705) B127322705
theorem B113175737 : Blo 2011435 113175737 := bstep (se 2 (by rfl) ⟨42440901, by rfl⟩ : syracuseStep 113175737 = 84881803) B84881803
theorem B75450491 : Blo 2011435 75450491 := bstep (se 1 (by rfl) ⟨56587868, by rfl⟩ : syracuseStep 75450491 = 113175737) B113175737
theorem B804805237 : Blo 2011435 804805237 := bstep (se 5 (by rfl) ⟨37725245, by rfl⟩ : syracuseStep 804805237 = 75450491) B75450491
theorem B4292294597 : Blo 2011435 4292294597 := bstep (se 4 (by rfl) ⟨402402618, by rfl⟩ : syracuseStep 4292294597 = 804805237) B804805237
theorem B2861529731 : Blo 2011435 2861529731 := bstep (se 1 (by rfl) ⟨2146147298, by rfl⟩ : syracuseStep 2861529731 = 4292294597) B4292294597
theorem B1907686487 : Blo 2011435 1907686487 := bstep (se 1 (by rfl) ⟨1430764865, by rfl⟩ : syracuseStep 1907686487 = 2861529731) B2861529731
theorem B1271790991 : Blo 2011435 1271790991 := bstep (se 1 (by rfl) ⟨953843243, by rfl⟩ : syracuseStep 1271790991 = 1907686487) B1907686487
theorem B1695721321 : Blo 2011435 1695721321 := bstep (se 2 (by rfl) ⟨635895495, by rfl⟩ : syracuseStep 1695721321 = 1271790991) B1271790991
theorem B2260961761 : Blo 2011435 2260961761 := bstep (se 2 (by rfl) ⟨847860660, by rfl⟩ : syracuseStep 2260961761 = 1695721321) B1695721321
theorem B3014615681 : Blo 2011435 3014615681 := bstep (se 2 (by rfl) ⟨1130480880, by rfl⟩ : syracuseStep 3014615681 = 2260961761) B2260961761
theorem B2009743787 : Blo 2011435 2009743787 := bstep (se 1 (by rfl) ⟨1507307840, by rfl⟩ : syracuseStep 2009743787 = 3014615681) B3014615681
theorem B1339829191 : Blo 2011435 1339829191 := bstep (se 1 (by rfl) ⟨1004871893, by rfl⟩ : syracuseStep 1339829191 = 2009743787) B2009743787
theorem B1786438921 : Blo 2011435 1786438921 := bstep (se 2 (by rfl) ⟨669914595, by rfl⟩ : syracuseStep 1786438921 = 1339829191) B1339829191
theorem B2381918561 : Blo 2011435 2381918561 := bstep (se 2 (by rfl) ⟨893219460, by rfl⟩ : syracuseStep 2381918561 = 1786438921) B1786438921
theorem B1587945707 : Blo 2011435 1587945707 := bstep (se 1 (by rfl) ⟨1190959280, by rfl⟩ : syracuseStep 1587945707 = 2381918561) B2381918561
theorem B1058630471 : Blo 2011435 1058630471 := bstep (se 1 (by rfl) ⟨793972853, by rfl⟩ : syracuseStep 1058630471 = 1587945707) B1587945707
theorem B705753647 : Blo 2011435 705753647 := bstep (se 1 (by rfl) ⟨529315235, by rfl⟩ : syracuseStep 705753647 = 1058630471) B1058630471
theorem B470502431 : Blo 2011435 470502431 := bstep (se 1 (by rfl) ⟨352876823, by rfl⟩ : syracuseStep 470502431 = 705753647) B705753647
theorem B313668287 : Blo 2011435 313668287 := bstep (se 1 (by rfl) ⟨235251215, by rfl⟩ : syracuseStep 313668287 = 470502431) B470502431
theorem B209112191 : Blo 2011435 209112191 := bstep (se 1 (by rfl) ⟨156834143, by rfl⟩ : syracuseStep 209112191 = 313668287) B313668287
theorem B139408127 : Blo 2011435 139408127 := bstep (se 1 (by rfl) ⟨104556095, by rfl⟩ : syracuseStep 139408127 = 209112191) B209112191
theorem B92938751 : Blo 2011435 92938751 := bstep (se 1 (by rfl) ⟨69704063, by rfl⟩ : syracuseStep 92938751 = 139408127) B139408127
theorem B61959167 : Blo 2011435 61959167 := bstep (se 1 (by rfl) ⟨46469375, by rfl⟩ : syracuseStep 61959167 = 92938751) B92938751
theorem B41306111 : Blo 2011435 41306111 := bstep (se 1 (by rfl) ⟨30979583, by rfl⟩ : syracuseStep 41306111 = 61959167) B61959167
theorem B27537407 : Blo 2011435 27537407 := bstep (se 1 (by rfl) ⟨20653055, by rfl⟩ : syracuseStep 27537407 = 41306111) B41306111
theorem B18358271 : Blo 2011435 18358271 := bstep (se 1 (by rfl) ⟨13768703, by rfl⟩ : syracuseStep 18358271 = 27537407) B27537407
theorem B12238847 : Blo 2011435 12238847 := bstep (se 1 (by rfl) ⟨9179135, by rfl⟩ : syracuseStep 12238847 = 18358271) B18358271
theorem B8159231 : Blo 2011435 8159231 := bstep (se 1 (by rfl) ⟨6119423, by rfl⟩ : syracuseStep 8159231 = 12238847) B12238847
theorem B5439487 : Blo 2011435 5439487 := bstep (se 1 (by rfl) ⟨4079615, by rfl⟩ : syracuseStep 5439487 = 8159231) B8159231
theorem B7252649 : Blo 2011435 7252649 := bstep (se 2 (by rfl) ⟨2719743, by rfl⟩ : syracuseStep 7252649 = 5439487) B5439487
theorem B4835099 : Blo 2011435 4835099 := bstep (se 1 (by rfl) ⟨3626324, by rfl⟩ : syracuseStep 4835099 = 7252649) B7252649
theorem B3223399 : Blo 2011435 3223399 := bstep (se 1 (by rfl) ⟨2417549, by rfl⟩ : syracuseStep 3223399 = 4835099) B4835099
theorem B4297865 : Blo 2011435 4297865 := bstep (se 2 (by rfl) ⟨1611699, by rfl⟩ : syracuseStep 4297865 = 3223399) B3223399
theorem B11460973 : Blo 2011435 11460973 := bstep (se 3 (by rfl) ⟨2148932, by rfl⟩ : syracuseStep 11460973 = 4297865) B4297865
theorem B15281297 : Blo 2011435 15281297 := bstep (se 2 (by rfl) ⟨5730486, by rfl⟩ : syracuseStep 15281297 = 11460973) B11460973
theorem B10187531 : Blo 2011435 10187531 := bstep (se 1 (by rfl) ⟨7640648, by rfl⟩ : syracuseStep 10187531 = 15281297) B15281297
theorem B6791687 : Blo 2011435 6791687 := bstep (se 1 (by rfl) ⟨5093765, by rfl⟩ : syracuseStep 6791687 = 10187531) B10187531
theorem B4527791 : Blo 2011435 4527791 := bstep (se 1 (by rfl) ⟨3395843, by rfl⟩ : syracuseStep 4527791 = 6791687) B6791687
theorem B3018527 : Blo 2011435 3018527 := bstep (se 1 (by rfl) ⟨2263895, by rfl⟩ : syracuseStep 3018527 = 4527791) B4527791
theorem B2012351 : Blo 2011435 2012351 := bstep (se 1 (by rfl) ⟨1509263, by rfl⟩ : syracuseStep 2012351 = 3018527) B3018527
theorem B3018533 : Blo 2011435 3018533 := bbase (se 4 (by rfl) ⟨282987, by rfl⟩ : syracuseStep 3018533 = 565975) (by norm_num)
theorem B2012355 : Blo 2011435 2012355 := bstep (se 1 (by rfl) ⟨1509266, by rfl⟩ : syracuseStep 2012355 = 3018533) B3018533
theorem B2546893 : Blo 2011435 2546893 := bbase (se 3 (by rfl) ⟨477542, by rfl⟩ : syracuseStep 2546893 = 955085) (by norm_num)
theorem B3395857 : Blo 2011435 3395857 := bstep (se 2 (by rfl) ⟨1273446, by rfl⟩ : syracuseStep 3395857 = 2546893) B2546893
theorem B4527809 : Blo 2011435 4527809 := bstep (se 2 (by rfl) ⟨1697928, by rfl⟩ : syracuseStep 4527809 = 3395857) B3395857
theorem B3018539 : Blo 2011435 3018539 := bstep (se 1 (by rfl) ⟨2263904, by rfl⟩ : syracuseStep 3018539 = 4527809) B4527809
theorem B2012359 : Blo 2011435 2012359 := bstep (se 1 (by rfl) ⟨1509269, by rfl⟩ : syracuseStep 2012359 = 3018539) B3018539
theorem B2263909 : Blo 2011435 2263909 := bbase (se 4 (by rfl) ⟨212241, by rfl⟩ : syracuseStep 2263909 = 424483) (by norm_num)
theorem B3018545 : Blo 2011435 3018545 := bstep (se 2 (by rfl) ⟨1131954, by rfl⟩ : syracuseStep 3018545 = 2263909) B2263909
theorem B2012363 : Blo 2011435 2012363 := bstep (se 1 (by rfl) ⟨1509272, by rfl⟩ : syracuseStep 2012363 = 3018545) B3018545
theorem B5730533 : Blo 2011435 5730533 := bbase (se 4 (by rfl) ⟨537237, by rfl⟩ : syracuseStep 5730533 = 1074475) (by norm_num)
theorem B3820355 : Blo 2011435 3820355 := bstep (se 1 (by rfl) ⟨2865266, by rfl⟩ : syracuseStep 3820355 = 5730533) B5730533
theorem B2546903 : Blo 2011435 2546903 := bstep (se 1 (by rfl) ⟨1910177, by rfl⟩ : syracuseStep 2546903 = 3820355) B3820355
theorem B6791741 : Blo 2011435 6791741 := bstep (se 3 (by rfl) ⟨1273451, by rfl⟩ : syracuseStep 6791741 = 2546903) B2546903
theorem B4527827 : Blo 2011435 4527827 := bstep (se 1 (by rfl) ⟨3395870, by rfl⟩ : syracuseStep 4527827 = 6791741) B6791741
theorem B3018551 : Blo 2011435 3018551 := bstep (se 1 (by rfl) ⟨2263913, by rfl⟩ : syracuseStep 3018551 = 4527827) B4527827
theorem B2012367 : Blo 2011435 2012367 := bstep (se 1 (by rfl) ⟨1509275, by rfl⟩ : syracuseStep 2012367 = 3018551) B3018551
theorem B3018557 : Blo 2011435 3018557 := bbase (se 3 (by rfl) ⟨565979, by rfl⟩ : syracuseStep 3018557 = 1131959) (by norm_num)
theorem B2012371 : Blo 2011435 2012371 := bstep (se 1 (by rfl) ⟨1509278, by rfl⟩ : syracuseStep 2012371 = 3018557) B3018557
theorem B4527845 : Blo 2011435 4527845 := bbase (se 4 (by rfl) ⟨424485, by rfl⟩ : syracuseStep 4527845 = 848971) (by norm_num)
theorem B3018563 : Blo 2011435 3018563 := bstep (se 1 (by rfl) ⟨2263922, by rfl⟩ : syracuseStep 3018563 = 4527845) B4527845
theorem B2012375 : Blo 2011435 2012375 := bstep (se 1 (by rfl) ⟨1509281, by rfl⟩ : syracuseStep 2012375 = 3018563) B3018563
theorem B5093837 : Blo 2011435 5093837 := bbase (se 3 (by rfl) ⟨955094, by rfl⟩ : syracuseStep 5093837 = 1910189) (by norm_num)
theorem B3395891 : Blo 2011435 3395891 := bstep (se 1 (by rfl) ⟨2546918, by rfl⟩ : syracuseStep 3395891 = 5093837) B5093837
theorem B2263927 : Blo 2011435 2263927 := bstep (se 1 (by rfl) ⟨1697945, by rfl⟩ : syracuseStep 2263927 = 3395891) B3395891
theorem B3018569 : Blo 2011435 3018569 := bstep (se 2 (by rfl) ⟨1131963, by rfl⟩ : syracuseStep 3018569 = 2263927) B2263927
theorem B2012379 : Blo 2011435 2012379 := bstep (se 1 (by rfl) ⟨1509284, by rfl⟩ : syracuseStep 2012379 = 3018569) B3018569
theorem B2294821 : Blo 2011435 2294821 := bbase (se 4 (by rfl) ⟨215139, by rfl⟩ : syracuseStep 2294821 = 430279) (by norm_num)
theorem B12239045 : Blo 2011435 12239045 := bstep (se 4 (by rfl) ⟨1147410, by rfl⟩ : syracuseStep 12239045 = 2294821) B2294821
theorem B8159363 : Blo 2011435 8159363 := bstep (se 1 (by rfl) ⟨6119522, by rfl⟩ : syracuseStep 8159363 = 12239045) B12239045
theorem B5439575 : Blo 2011435 5439575 := bstep (se 1 (by rfl) ⟨4079681, by rfl⟩ : syracuseStep 5439575 = 8159363) B8159363
theorem B3626383 : Blo 2011435 3626383 := bstep (se 1 (by rfl) ⟨2719787, by rfl⟩ : syracuseStep 3626383 = 5439575) B5439575
theorem B4835177 : Blo 2011435 4835177 := bstep (se 2 (by rfl) ⟨1813191, by rfl⟩ : syracuseStep 4835177 = 3626383) B3626383
theorem B3223451 : Blo 2011435 3223451 := bstep (se 1 (by rfl) ⟨2417588, by rfl⟩ : syracuseStep 3223451 = 4835177) B4835177
theorem B2148967 : Blo 2011435 2148967 := bstep (se 1 (by rfl) ⟨1611725, by rfl⟩ : syracuseStep 2148967 = 3223451) B3223451
theorem B2865289 : Blo 2011435 2865289 := bstep (se 2 (by rfl) ⟨1074483, by rfl⟩ : syracuseStep 2865289 = 2148967) B2148967
theorem B3820385 : Blo 2011435 3820385 := bstep (se 2 (by rfl) ⟨1432644, by rfl⟩ : syracuseStep 3820385 = 2865289) B2865289
theorem B10187693 : Blo 2011435 10187693 := bstep (se 3 (by rfl) ⟨1910192, by rfl⟩ : syracuseStep 10187693 = 3820385) B3820385
theorem B6791795 : Blo 2011435 6791795 := bstep (se 1 (by rfl) ⟨5093846, by rfl⟩ : syracuseStep 6791795 = 10187693) B10187693
theorem B4527863 : Blo 2011435 4527863 := bstep (se 1 (by rfl) ⟨3395897, by rfl⟩ : syracuseStep 4527863 = 6791795) B6791795
theorem B3018575 : Blo 2011435 3018575 := bstep (se 1 (by rfl) ⟨2263931, by rfl⟩ : syracuseStep 3018575 = 4527863) B4527863
theorem B2012383 : Blo 2011435 2012383 := bstep (se 1 (by rfl) ⟨1509287, by rfl⟩ : syracuseStep 2012383 = 3018575) B3018575
theorem B3018581 : Blo 2011435 3018581 := bbase (se 9 (by rfl) ⟨8843, by rfl⟩ : syracuseStep 3018581 = 17687) (by norm_num)
theorem B2012387 : Blo 2011435 2012387 := bstep (se 1 (by rfl) ⟨1509290, by rfl⟩ : syracuseStep 2012387 = 3018581) B3018581
theorem B7452053 : Blo 2011435 7452053 := bbase (se 6 (by rfl) ⟨174657, by rfl⟩ : syracuseStep 7452053 = 349315) (by norm_num)
theorem B4968035 : Blo 2011435 4968035 := bstep (se 1 (by rfl) ⟨3726026, by rfl⟩ : syracuseStep 4968035 = 7452053) B7452053
theorem B3312023 : Blo 2011435 3312023 := bstep (se 1 (by rfl) ⟨2484017, by rfl⟩ : syracuseStep 3312023 = 4968035) B4968035
theorem B8832061 : Blo 2011435 8832061 := bstep (se 3 (by rfl) ⟨1656011, by rfl⟩ : syracuseStep 8832061 = 3312023) B3312023
theorem B47104325 : Blo 2011435 47104325 := bstep (se 4 (by rfl) ⟨4416030, by rfl⟩ : syracuseStep 47104325 = 8832061) B8832061
theorem B31402883 : Blo 2011435 31402883 := bstep (se 1 (by rfl) ⟨23552162, by rfl⟩ : syracuseStep 31402883 = 47104325) B47104325
theorem B20935255 : Blo 2011435 20935255 := bstep (se 1 (by rfl) ⟨15701441, by rfl⟩ : syracuseStep 20935255 = 31402883) B31402883
theorem B27913673 : Blo 2011435 27913673 := bstep (se 2 (by rfl) ⟨10467627, by rfl⟩ : syracuseStep 27913673 = 20935255) B20935255
theorem B18609115 : Blo 2011435 18609115 := bstep (se 1 (by rfl) ⟨13956836, by rfl⟩ : syracuseStep 18609115 = 27913673) B27913673
theorem B24812153 : Blo 2011435 24812153 := bstep (se 2 (by rfl) ⟨9304557, by rfl⟩ : syracuseStep 24812153 = 18609115) B18609115
theorem B16541435 : Blo 2011435 16541435 := bstep (se 1 (by rfl) ⟨12406076, by rfl⟩ : syracuseStep 16541435 = 24812153) B24812153
theorem B44110493 : Blo 2011435 44110493 := bstep (se 3 (by rfl) ⟨8270717, by rfl⟩ : syracuseStep 44110493 = 16541435) B16541435
theorem B29406995 : Blo 2011435 29406995 := bstep (se 1 (by rfl) ⟨22055246, by rfl⟩ : syracuseStep 29406995 = 44110493) B44110493
theorem B19604663 : Blo 2011435 19604663 := bstep (se 1 (by rfl) ⟨14703497, by rfl⟩ : syracuseStep 19604663 = 29406995) B29406995
theorem B13069775 : Blo 2011435 13069775 := bstep (se 1 (by rfl) ⟨9802331, by rfl⟩ : syracuseStep 13069775 = 19604663) B19604663
theorem B8713183 : Blo 2011435 8713183 := bstep (se 1 (by rfl) ⟨6534887, by rfl⟩ : syracuseStep 8713183 = 13069775) B13069775
theorem B11617577 : Blo 2011435 11617577 := bstep (se 2 (by rfl) ⟨4356591, by rfl⟩ : syracuseStep 11617577 = 8713183) B8713183
theorem B7745051 : Blo 2011435 7745051 := bstep (se 1 (by rfl) ⟨5808788, by rfl⟩ : syracuseStep 7745051 = 11617577) B11617577
theorem B5163367 : Blo 2011435 5163367 := bstep (se 1 (by rfl) ⟨3872525, by rfl⟩ : syracuseStep 5163367 = 7745051) B7745051
theorem B6884489 : Blo 2011435 6884489 := bstep (se 2 (by rfl) ⟨2581683, by rfl⟩ : syracuseStep 6884489 = 5163367) B5163367
theorem B4589659 : Blo 2011435 4589659 := bstep (se 1 (by rfl) ⟨3442244, by rfl⟩ : syracuseStep 4589659 = 6884489) B6884489
theorem B6119545 : Blo 2011435 6119545 := bstep (se 2 (by rfl) ⟨2294829, by rfl⟩ : syracuseStep 6119545 = 4589659) B4589659
theorem B8159393 : Blo 2011435 8159393 := bstep (se 2 (by rfl) ⟨3059772, by rfl⟩ : syracuseStep 8159393 = 6119545) B6119545
theorem B21758381 : Blo 2011435 21758381 := bstep (se 3 (by rfl) ⟨4079696, by rfl⟩ : syracuseStep 21758381 = 8159393) B8159393
theorem B14505587 : Blo 2011435 14505587 := bstep (se 1 (by rfl) ⟨10879190, by rfl⟩ : syracuseStep 14505587 = 21758381) B21758381
theorem B9670391 : Blo 2011435 9670391 := bstep (se 1 (by rfl) ⟨7252793, by rfl⟩ : syracuseStep 9670391 = 14505587) B14505587
theorem B6446927 : Blo 2011435 6446927 := bstep (se 1 (by rfl) ⟨4835195, by rfl⟩ : syracuseStep 6446927 = 9670391) B9670391
theorem B4297951 : Blo 2011435 4297951 := bstep (se 1 (by rfl) ⟨3223463, by rfl⟩ : syracuseStep 4297951 = 6446927) B6446927
theorem B5730601 : Blo 2011435 5730601 := bstep (se 2 (by rfl) ⟨2148975, by rfl⟩ : syracuseStep 5730601 = 4297951) B4297951
theorem B7640801 : Blo 2011435 7640801 := bstep (se 2 (by rfl) ⟨2865300, by rfl⟩ : syracuseStep 7640801 = 5730601) B5730601
theorem B5093867 : Blo 2011435 5093867 := bstep (se 1 (by rfl) ⟨3820400, by rfl⟩ : syracuseStep 5093867 = 7640801) B7640801
theorem B3395911 : Blo 2011435 3395911 := bstep (se 1 (by rfl) ⟨2546933, by rfl⟩ : syracuseStep 3395911 = 5093867) B5093867
theorem B4527881 : Blo 2011435 4527881 := bstep (se 2 (by rfl) ⟨1697955, by rfl⟩ : syracuseStep 4527881 = 3395911) B3395911
theorem B3018587 : Blo 2011435 3018587 := bstep (se 1 (by rfl) ⟨2263940, by rfl⟩ : syracuseStep 3018587 = 4527881) B4527881
theorem B2012391 : Blo 2011435 2012391 := bstep (se 1 (by rfl) ⟨1509293, by rfl⟩ : syracuseStep 2012391 = 3018587) B3018587
theorem B2263945 : Blo 2011435 2263945 := bbase (se 2 (by rfl) ⟨848979, by rfl⟩ : syracuseStep 2263945 = 1697959) (by norm_num)
theorem B3018593 : Blo 2011435 3018593 := bstep (se 2 (by rfl) ⟨1131972, by rfl⟩ : syracuseStep 3018593 = 2263945) B2263945
theorem B2012395 : Blo 2011435 2012395 := bstep (se 1 (by rfl) ⟨1509296, by rfl⟩ : syracuseStep 2012395 = 3018593) B3018593
theorem B4135373 : Blo 2011435 4135373 := bbase (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) (by norm_num)
theorem B2756915 : Blo 2011435 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B29407093 : Blo 2011435 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B627351317 : Blo 2011435 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B418234211 : Blo 2011435 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B278822807 : Blo 2011435 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B185881871 : Blo 2011435 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B123921247 : Blo 2011435 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B165228329 : Blo 2011435 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B110152219 : Blo 2011435 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B146869625 : Blo 2011435 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B97913083 : Blo 2011435 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B130550777 : Blo 2011435 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B87033851 : Blo 2011435 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B58022567 : Blo 2011435 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B38681711 : Blo 2011435 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B25787807 : Blo 2011435 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B17191871 : Blo 2011435 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B11461247 : Blo 2011435 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B7640831 : Blo 2011435 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B5093887 : Blo 2011435 5093887 := bstep (se 1 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 5093887 = 7640831) B7640831
theorem B6791849 : Blo 2011435 6791849 := bstep (se 2 (by rfl) ⟨2546943, by rfl⟩ : syracuseStep 6791849 = 5093887) B5093887
theorem B4527899 : Blo 2011435 4527899 := bstep (se 1 (by rfl) ⟨3395924, by rfl⟩ : syracuseStep 4527899 = 6791849) B6791849
theorem B3018599 : Blo 2011435 3018599 := bstep (se 1 (by rfl) ⟨2263949, by rfl⟩ : syracuseStep 3018599 = 4527899) B4527899
theorem B2012399 : Blo 2011435 2012399 := bstep (se 1 (by rfl) ⟨1509299, by rfl⟩ : syracuseStep 2012399 = 3018599) B3018599
theorem B3018605 : Blo 2011435 3018605 := bbase (se 3 (by rfl) ⟨565988, by rfl⟩ : syracuseStep 3018605 = 1131977) (by norm_num)
theorem B2012403 : Blo 2011435 2012403 := bstep (se 1 (by rfl) ⟨1509302, by rfl⟩ : syracuseStep 2012403 = 3018605) B3018605
theorem B4527917 : Blo 2011435 4527917 := bbase (se 3 (by rfl) ⟨848984, by rfl⟩ : syracuseStep 4527917 = 1697969) (by norm_num)
theorem B3018611 : Blo 2011435 3018611 := bstep (se 1 (by rfl) ⟨2263958, by rfl⟩ : syracuseStep 3018611 = 4527917) B4527917
theorem B2012407 : Blo 2011435 2012407 := bstep (se 1 (by rfl) ⟨1509305, by rfl⟩ : syracuseStep 2012407 = 3018611) B3018611
theorem B8595989 : Blo 2011435 8595989 := bbase (se 6 (by rfl) ⟨201468, by rfl⟩ : syracuseStep 8595989 = 402937) (by norm_num)
theorem B5730659 : Blo 2011435 5730659 := bstep (se 1 (by rfl) ⟨4297994, by rfl⟩ : syracuseStep 5730659 = 8595989) B8595989
theorem B3820439 : Blo 2011435 3820439 := bstep (se 1 (by rfl) ⟨2865329, by rfl⟩ : syracuseStep 3820439 = 5730659) B5730659
theorem B2546959 : Blo 2011435 2546959 := bstep (se 1 (by rfl) ⟨1910219, by rfl⟩ : syracuseStep 2546959 = 3820439) B3820439
theorem B3395945 : Blo 2011435 3395945 := bstep (se 2 (by rfl) ⟨1273479, by rfl⟩ : syracuseStep 3395945 = 2546959) B2546959
theorem B2263963 : Blo 2011435 2263963 := bstep (se 1 (by rfl) ⟨1697972, by rfl⟩ : syracuseStep 2263963 = 3395945) B3395945
theorem B3018617 : Blo 2011435 3018617 := bstep (se 2 (by rfl) ⟨1131981, by rfl⟩ : syracuseStep 3018617 = 2263963) B2263963
theorem B2012411 : Blo 2011435 2012411 := bstep (se 1 (by rfl) ⟨1509308, by rfl⟩ : syracuseStep 2012411 = 3018617) B3018617
theorem B12894005 : Blo 2011435 12894005 := bbase (se 5 (by rfl) ⟨604406, by rfl⟩ : syracuseStep 12894005 = 1208813) (by norm_num)
theorem B34384013 : Blo 2011435 34384013 := bstep (se 3 (by rfl) ⟨6447002, by rfl⟩ : syracuseStep 34384013 = 12894005) B12894005
theorem B22922675 : Blo 2011435 22922675 := bstep (se 1 (by rfl) ⟨17192006, by rfl⟩ : syracuseStep 22922675 = 34384013) B34384013
theorem B15281783 : Blo 2011435 15281783 := bstep (se 1 (by rfl) ⟨11461337, by rfl⟩ : syracuseStep 15281783 = 22922675) B22922675
theorem B10187855 : Blo 2011435 10187855 := bstep (se 1 (by rfl) ⟨7640891, by rfl⟩ : syracuseStep 10187855 = 15281783) B15281783
theorem B6791903 : Blo 2011435 6791903 := bstep (se 1 (by rfl) ⟨5093927, by rfl⟩ : syracuseStep 6791903 = 10187855) B10187855
theorem B4527935 : Blo 2011435 4527935 := bstep (se 1 (by rfl) ⟨3395951, by rfl⟩ : syracuseStep 4527935 = 6791903) B6791903
theorem B3018623 : Blo 2011435 3018623 := bstep (se 1 (by rfl) ⟨2263967, by rfl⟩ : syracuseStep 3018623 = 4527935) B4527935
theorem B2012415 : Blo 2011435 2012415 := bstep (se 1 (by rfl) ⟨1509311, by rfl⟩ : syracuseStep 2012415 = 3018623) B3018623
theorem B3018629 : Blo 2011435 3018629 := bbase (se 4 (by rfl) ⟨282996, by rfl⟩ : syracuseStep 3018629 = 565993) (by norm_num)
theorem B2012419 : Blo 2011435 2012419 := bstep (se 1 (by rfl) ⟨1509314, by rfl⟩ : syracuseStep 2012419 = 3018629) B3018629
theorem B3395965 : Blo 2011435 3395965 := bbase (se 3 (by rfl) ⟨636743, by rfl⟩ : syracuseStep 3395965 = 1273487) (by norm_num)
theorem B4527953 : Blo 2011435 4527953 := bstep (se 2 (by rfl) ⟨1697982, by rfl⟩ : syracuseStep 4527953 = 3395965) B3395965
theorem B3018635 : Blo 2011435 3018635 := bstep (se 1 (by rfl) ⟨2263976, by rfl⟩ : syracuseStep 3018635 = 4527953) B4527953
theorem B2012423 : Blo 2011435 2012423 := bstep (se 1 (by rfl) ⟨1509317, by rfl⟩ : syracuseStep 2012423 = 3018635) B3018635
theorem B2263981 : Blo 2011435 2263981 := bbase (se 3 (by rfl) ⟨424496, by rfl⟩ : syracuseStep 2263981 = 848993) (by norm_num)
theorem B3018641 : Blo 2011435 3018641 := bstep (se 2 (by rfl) ⟨1131990, by rfl⟩ : syracuseStep 3018641 = 2263981) B2263981
theorem B2012427 : Blo 2011435 2012427 := bstep (se 1 (by rfl) ⟨1509320, by rfl⟩ : syracuseStep 2012427 = 3018641) B3018641
theorem B6791957 : Blo 2011435 6791957 := bbase (se 6 (by rfl) ⟨159186, by rfl⟩ : syracuseStep 6791957 = 318373) (by norm_num)
theorem B4527971 : Blo 2011435 4527971 := bstep (se 1 (by rfl) ⟨3395978, by rfl⟩ : syracuseStep 4527971 = 6791957) B6791957
theorem B3018647 : Blo 2011435 3018647 := bstep (se 1 (by rfl) ⟨2263985, by rfl⟩ : syracuseStep 3018647 = 4527971) B4527971
theorem B2012431 : Blo 2011435 2012431 := bstep (se 1 (by rfl) ⟨1509323, by rfl⟩ : syracuseStep 2012431 = 3018647) B3018647
theorem B3018653 : Blo 2011435 3018653 := bbase (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) (by norm_num)
theorem B2012435 : Blo 2011435 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B4527989 : Blo 2011435 4527989 := bbase (se 5 (by rfl) ⟨212249, by rfl⟩ : syracuseStep 4527989 = 424499) (by norm_num)
theorem B3018659 : Blo 2011435 3018659 := bstep (se 1 (by rfl) ⟨2263994, by rfl⟩ : syracuseStep 3018659 = 4527989) B4527989
theorem B2012439 : Blo 2011435 2012439 := bstep (se 1 (by rfl) ⟨1509329, by rfl⟩ : syracuseStep 2012439 = 3018659) B3018659
theorem B16767541 : Blo 2011435 16767541 := bbase (se 5 (by rfl) ⟨785978, by rfl⟩ : syracuseStep 16767541 = 1571957) (by norm_num)
theorem B89426885 : Blo 2011435 89426885 := bstep (se 4 (by rfl) ⟨8383770, by rfl⟩ : syracuseStep 89426885 = 16767541) B16767541
theorem B953886773 : Blo 2011435 953886773 := bstep (se 5 (by rfl) ⟨44713442, by rfl⟩ : syracuseStep 953886773 = 89426885) B89426885
theorem B635924515 : Blo 2011435 635924515 := bstep (se 1 (by rfl) ⟨476943386, by rfl⟩ : syracuseStep 635924515 = 953886773) B953886773
theorem B847899353 : Blo 2011435 847899353 := bstep (se 2 (by rfl) ⟨317962257, by rfl⟩ : syracuseStep 847899353 = 635924515) B635924515
theorem B2261064941 : Blo 2011435 2261064941 := bstep (se 3 (by rfl) ⟨423949676, by rfl⟩ : syracuseStep 2261064941 = 847899353) B847899353
theorem B1507376627 : Blo 2011435 1507376627 := bstep (se 1 (by rfl) ⟨1130532470, by rfl⟩ : syracuseStep 1507376627 = 2261064941) B2261064941
theorem B1004917751 : Blo 2011435 1004917751 := bstep (se 1 (by rfl) ⟨753688313, by rfl⟩ : syracuseStep 1004917751 = 1507376627) B1507376627
theorem B669945167 : Blo 2011435 669945167 := bstep (se 1 (by rfl) ⟨502458875, by rfl⟩ : syracuseStep 669945167 = 1004917751) B1004917751
theorem B446630111 : Blo 2011435 446630111 := bstep (se 1 (by rfl) ⟨334972583, by rfl⟩ : syracuseStep 446630111 = 669945167) B669945167
theorem B297753407 : Blo 2011435 297753407 := bstep (se 1 (by rfl) ⟨223315055, by rfl⟩ : syracuseStep 297753407 = 446630111) B446630111
theorem B198502271 : Blo 2011435 198502271 := bstep (se 1 (by rfl) ⟨148876703, by rfl⟩ : syracuseStep 198502271 = 297753407) B297753407
theorem B132334847 : Blo 2011435 132334847 := bstep (se 1 (by rfl) ⟨99251135, by rfl⟩ : syracuseStep 132334847 = 198502271) B198502271
theorem B88223231 : Blo 2011435 88223231 := bstep (se 1 (by rfl) ⟨66167423, by rfl⟩ : syracuseStep 88223231 = 132334847) B132334847
theorem B58815487 : Blo 2011435 58815487 := bstep (se 1 (by rfl) ⟨44111615, by rfl⟩ : syracuseStep 58815487 = 88223231) B88223231
theorem B78420649 : Blo 2011435 78420649 := bstep (se 2 (by rfl) ⟨29407743, by rfl⟩ : syracuseStep 78420649 = 58815487) B58815487
theorem B104560865 : Blo 2011435 104560865 := bstep (se 2 (by rfl) ⟨39210324, by rfl⟩ : syracuseStep 104560865 = 78420649) B78420649
theorem B69707243 : Blo 2011435 69707243 := bstep (se 1 (by rfl) ⟨52280432, by rfl⟩ : syracuseStep 69707243 = 104560865) B104560865
theorem B46471495 : Blo 2011435 46471495 := bstep (se 1 (by rfl) ⟨34853621, by rfl⟩ : syracuseStep 46471495 = 69707243) B69707243
theorem B61961993 : Blo 2011435 61961993 := bstep (se 2 (by rfl) ⟨23235747, by rfl⟩ : syracuseStep 61961993 = 46471495) B46471495
theorem B41307995 : Blo 2011435 41307995 := bstep (se 1 (by rfl) ⟨30980996, by rfl⟩ : syracuseStep 41307995 = 61961993) B61961993
theorem B27538663 : Blo 2011435 27538663 := bstep (se 1 (by rfl) ⟨20653997, by rfl⟩ : syracuseStep 27538663 = 41307995) B41307995
theorem B36718217 : Blo 2011435 36718217 := bstep (se 2 (by rfl) ⟨13769331, by rfl⟩ : syracuseStep 36718217 = 27538663) B27538663
theorem B24478811 : Blo 2011435 24478811 := bstep (se 1 (by rfl) ⟨18359108, by rfl⟩ : syracuseStep 24478811 = 36718217) B36718217
theorem B16319207 : Blo 2011435 16319207 := bstep (se 1 (by rfl) ⟨12239405, by rfl⟩ : syracuseStep 16319207 = 24478811) B24478811
theorem B10879471 : Blo 2011435 10879471 := bstep (se 1 (by rfl) ⟨8159603, by rfl⟩ : syracuseStep 10879471 = 16319207) B16319207
theorem B14505961 : Blo 2011435 14505961 := bstep (se 2 (by rfl) ⟨5439735, by rfl⟩ : syracuseStep 14505961 = 10879471) B10879471
theorem B19341281 : Blo 2011435 19341281 := bstep (se 2 (by rfl) ⟨7252980, by rfl⟩ : syracuseStep 19341281 = 14505961) B14505961
theorem B12894187 : Blo 2011435 12894187 := bstep (se 1 (by rfl) ⟨9670640, by rfl⟩ : syracuseStep 12894187 = 19341281) B19341281
theorem B17192249 : Blo 2011435 17192249 := bstep (se 2 (by rfl) ⟨6447093, by rfl⟩ : syracuseStep 17192249 = 12894187) B12894187
theorem B11461499 : Blo 2011435 11461499 := bstep (se 1 (by rfl) ⟨8596124, by rfl⟩ : syracuseStep 11461499 = 17192249) B17192249
theorem B7640999 : Blo 2011435 7640999 := bstep (se 1 (by rfl) ⟨5730749, by rfl⟩ : syracuseStep 7640999 = 11461499) B11461499
theorem B5093999 : Blo 2011435 5093999 := bstep (se 1 (by rfl) ⟨3820499, by rfl⟩ : syracuseStep 5093999 = 7640999) B7640999
theorem B3395999 : Blo 2011435 3395999 := bstep (se 1 (by rfl) ⟨2546999, by rfl⟩ : syracuseStep 3395999 = 5093999) B5093999
theorem B2263999 : Blo 2011435 2263999 := bstep (se 1 (by rfl) ⟨1697999, by rfl⟩ : syracuseStep 2263999 = 3395999) B3395999
theorem B3018665 : Blo 2011435 3018665 := bstep (se 2 (by rfl) ⟨1131999, by rfl⟩ : syracuseStep 3018665 = 2263999) B2263999
theorem B2012443 : Blo 2011435 2012443 := bstep (se 1 (by rfl) ⟨1509332, by rfl⟩ : syracuseStep 2012443 = 3018665) B3018665
theorem B7641013 : Blo 2011435 7641013 := bbase (se 5 (by rfl) ⟨358172, by rfl⟩ : syracuseStep 7641013 = 716345) (by norm_num)
theorem B10188017 : Blo 2011435 10188017 := bstep (se 2 (by rfl) ⟨3820506, by rfl⟩ : syracuseStep 10188017 = 7641013) B7641013
theorem B6792011 : Blo 2011435 6792011 := bstep (se 1 (by rfl) ⟨5094008, by rfl⟩ : syracuseStep 6792011 = 10188017) B10188017
theorem B4528007 : Blo 2011435 4528007 := bstep (se 1 (by rfl) ⟨3396005, by rfl⟩ : syracuseStep 4528007 = 6792011) B6792011
theorem B3018671 : Blo 2011435 3018671 := bstep (se 1 (by rfl) ⟨2264003, by rfl⟩ : syracuseStep 3018671 = 4528007) B4528007
theorem B2012447 : Blo 2011435 2012447 := bstep (se 1 (by rfl) ⟨1509335, by rfl⟩ : syracuseStep 2012447 = 3018671) B3018671
theorem B3018677 : Blo 2011435 3018677 := bbase (se 5 (by rfl) ⟨141500, by rfl⟩ : syracuseStep 3018677 = 283001) (by norm_num)
theorem B2012451 : Blo 2011435 2012451 := bstep (se 1 (by rfl) ⟨1509338, by rfl⟩ : syracuseStep 2012451 = 3018677) B3018677
theorem B5094029 : Blo 2011435 5094029 := bbase (se 3 (by rfl) ⟨955130, by rfl⟩ : syracuseStep 5094029 = 1910261) (by norm_num)
theorem B3396019 : Blo 2011435 3396019 := bstep (se 1 (by rfl) ⟨2547014, by rfl⟩ : syracuseStep 3396019 = 5094029) B5094029
theorem B4528025 : Blo 2011435 4528025 := bstep (se 2 (by rfl) ⟨1698009, by rfl⟩ : syracuseStep 4528025 = 3396019) B3396019
theorem B3018683 : Blo 2011435 3018683 := bstep (se 1 (by rfl) ⟨2264012, by rfl⟩ : syracuseStep 3018683 = 4528025) B4528025
theorem B2012455 : Blo 2011435 2012455 := bstep (se 1 (by rfl) ⟨1509341, by rfl⟩ : syracuseStep 2012455 = 3018683) B3018683
theorem B2264017 : Blo 2011435 2264017 := bbase (se 2 (by rfl) ⟨849006, by rfl⟩ : syracuseStep 2264017 = 1698013) (by norm_num)
theorem B3018689 : Blo 2011435 3018689 := bstep (se 2 (by rfl) ⟨1132008, by rfl⟩ : syracuseStep 3018689 = 2264017) B2264017
theorem B2012459 : Blo 2011435 2012459 := bstep (se 1 (by rfl) ⟨1509344, by rfl⟩ : syracuseStep 2012459 = 3018689) B3018689
theorem B5808997 : Blo 2011435 5808997 := bbase (se 4 (by rfl) ⟨544593, by rfl⟩ : syracuseStep 5808997 = 1089187) (by norm_num)
theorem B7745329 : Blo 2011435 7745329 := bstep (se 2 (by rfl) ⟨2904498, by rfl⟩ : syracuseStep 7745329 = 5808997) B5808997
theorem B10327105 : Blo 2011435 10327105 := bstep (se 2 (by rfl) ⟨3872664, by rfl⟩ : syracuseStep 10327105 = 7745329) B7745329
theorem B13769473 : Blo 2011435 13769473 := bstep (se 2 (by rfl) ⟨5163552, by rfl⟩ : syracuseStep 13769473 = 10327105) B10327105
theorem B18359297 : Blo 2011435 18359297 := bstep (se 2 (by rfl) ⟨6884736, by rfl⟩ : syracuseStep 18359297 = 13769473) B13769473
theorem B12239531 : Blo 2011435 12239531 := bstep (se 1 (by rfl) ⟨9179648, by rfl⟩ : syracuseStep 12239531 = 18359297) B18359297
theorem B8159687 : Blo 2011435 8159687 := bstep (se 1 (by rfl) ⟨6119765, by rfl⟩ : syracuseStep 8159687 = 12239531) B12239531
theorem B5439791 : Blo 2011435 5439791 := bstep (se 1 (by rfl) ⟨4079843, by rfl⟩ : syracuseStep 5439791 = 8159687) B8159687
theorem B3626527 : Blo 2011435 3626527 := bstep (se 1 (by rfl) ⟨2719895, by rfl⟩ : syracuseStep 3626527 = 5439791) B5439791
theorem B4835369 : Blo 2011435 4835369 := bstep (se 2 (by rfl) ⟨1813263, by rfl⟩ : syracuseStep 4835369 = 3626527) B3626527
theorem B3223579 : Blo 2011435 3223579 := bstep (se 1 (by rfl) ⟨2417684, by rfl⟩ : syracuseStep 3223579 = 4835369) B4835369
theorem B4298105 : Blo 2011435 4298105 := bstep (se 2 (by rfl) ⟨1611789, by rfl⟩ : syracuseStep 4298105 = 3223579) B3223579
theorem B2865403 : Blo 2011435 2865403 := bstep (se 1 (by rfl) ⟨2149052, by rfl⟩ : syracuseStep 2865403 = 4298105) B4298105
theorem B3820537 : Blo 2011435 3820537 := bstep (se 2 (by rfl) ⟨1432701, by rfl⟩ : syracuseStep 3820537 = 2865403) B2865403
theorem B5094049 : Blo 2011435 5094049 := bstep (se 2 (by rfl) ⟨1910268, by rfl⟩ : syracuseStep 5094049 = 3820537) B3820537
theorem B6792065 : Blo 2011435 6792065 := bstep (se 2 (by rfl) ⟨2547024, by rfl⟩ : syracuseStep 6792065 = 5094049) B5094049
theorem B4528043 : Blo 2011435 4528043 := bstep (se 1 (by rfl) ⟨3396032, by rfl⟩ : syracuseStep 4528043 = 6792065) B6792065
theorem B3018695 : Blo 2011435 3018695 := bstep (se 1 (by rfl) ⟨2264021, by rfl⟩ : syracuseStep 3018695 = 4528043) B4528043
theorem B2012463 : Blo 2011435 2012463 := bstep (se 1 (by rfl) ⟨1509347, by rfl⟩ : syracuseStep 2012463 = 3018695) B3018695
theorem B3018701 : Blo 2011435 3018701 := bbase (se 3 (by rfl) ⟨566006, by rfl⟩ : syracuseStep 3018701 = 1132013) (by norm_num)
theorem B2012467 : Blo 2011435 2012467 := bstep (se 1 (by rfl) ⟨1509350, by rfl⟩ : syracuseStep 2012467 = 3018701) B3018701
theorem B4528061 : Blo 2011435 4528061 := bbase (se 3 (by rfl) ⟨849011, by rfl⟩ : syracuseStep 4528061 = 1698023) (by norm_num)
theorem B3018707 : Blo 2011435 3018707 := bstep (se 1 (by rfl) ⟨2264030, by rfl⟩ : syracuseStep 3018707 = 4528061) B4528061
theorem B2012471 : Blo 2011435 2012471 := bstep (se 1 (by rfl) ⟨1509353, by rfl⟩ : syracuseStep 2012471 = 3018707) B3018707
theorem B3396053 : Blo 2011435 3396053 := bbase (se 7 (by rfl) ⟨39797, by rfl⟩ : syracuseStep 3396053 = 79595) (by norm_num)
theorem B2264035 : Blo 2011435 2264035 := bstep (se 1 (by rfl) ⟨1698026, by rfl⟩ : syracuseStep 2264035 = 3396053) B3396053
theorem B3018713 : Blo 2011435 3018713 := bstep (se 2 (by rfl) ⟨1132017, by rfl⟩ : syracuseStep 3018713 = 2264035) B2264035
theorem B2012475 : Blo 2011435 2012475 := bstep (se 1 (by rfl) ⟨1509356, by rfl⟩ : syracuseStep 2012475 = 3018713) B3018713
theorem B8596277 : Blo 2011435 8596277 := bbase (se 5 (by rfl) ⟨402950, by rfl⟩ : syracuseStep 8596277 = 805901) (by norm_num)
theorem B5730851 : Blo 2011435 5730851 := bstep (se 1 (by rfl) ⟨4298138, by rfl⟩ : syracuseStep 5730851 = 8596277) B8596277
theorem B15282269 : Blo 2011435 15282269 := bstep (se 3 (by rfl) ⟨2865425, by rfl⟩ : syracuseStep 15282269 = 5730851) B5730851
theorem B10188179 : Blo 2011435 10188179 := bstep (se 1 (by rfl) ⟨7641134, by rfl⟩ : syracuseStep 10188179 = 15282269) B15282269
theorem B6792119 : Blo 2011435 6792119 := bstep (se 1 (by rfl) ⟨5094089, by rfl⟩ : syracuseStep 6792119 = 10188179) B10188179
theorem B4528079 : Blo 2011435 4528079 := bstep (se 1 (by rfl) ⟨3396059, by rfl⟩ : syracuseStep 4528079 = 6792119) B6792119
theorem B3018719 : Blo 2011435 3018719 := bstep (se 1 (by rfl) ⟨2264039, by rfl⟩ : syracuseStep 3018719 = 4528079) B4528079
theorem B2012479 : Blo 2011435 2012479 := bstep (se 1 (by rfl) ⟨1509359, by rfl⟩ : syracuseStep 2012479 = 3018719) B3018719
theorem B3018725 : Blo 2011435 3018725 := bbase (se 4 (by rfl) ⟨283005, by rfl⟩ : syracuseStep 3018725 = 566011) (by norm_num)
theorem B2012483 : Blo 2011435 2012483 := bstep (se 1 (by rfl) ⟨1509362, by rfl⟩ : syracuseStep 2012483 = 3018725) B3018725
theorem B9670853 : Blo 2011435 9670853 := bbase (se 4 (by rfl) ⟨906642, by rfl⟩ : syracuseStep 9670853 = 1813285) (by norm_num)
theorem B6447235 : Blo 2011435 6447235 := bstep (se 1 (by rfl) ⟨4835426, by rfl⟩ : syracuseStep 6447235 = 9670853) B9670853
theorem B8596313 : Blo 2011435 8596313 := bstep (se 2 (by rfl) ⟨3223617, by rfl⟩ : syracuseStep 8596313 = 6447235) B6447235
theorem B5730875 : Blo 2011435 5730875 := bstep (se 1 (by rfl) ⟨4298156, by rfl⟩ : syracuseStep 5730875 = 8596313) B8596313
theorem B3820583 : Blo 2011435 3820583 := bstep (se 1 (by rfl) ⟨2865437, by rfl⟩ : syracuseStep 3820583 = 5730875) B5730875
theorem B2547055 : Blo 2011435 2547055 := bstep (se 1 (by rfl) ⟨1910291, by rfl⟩ : syracuseStep 2547055 = 3820583) B3820583
theorem B3396073 : Blo 2011435 3396073 := bstep (se 2 (by rfl) ⟨1273527, by rfl⟩ : syracuseStep 3396073 = 2547055) B2547055
theorem B4528097 : Blo 2011435 4528097 := bstep (se 2 (by rfl) ⟨1698036, by rfl⟩ : syracuseStep 4528097 = 3396073) B3396073
theorem B3018731 : Blo 2011435 3018731 := bstep (se 1 (by rfl) ⟨2264048, by rfl⟩ : syracuseStep 3018731 = 4528097) B4528097
theorem B2012487 : Blo 2011435 2012487 := bstep (se 1 (by rfl) ⟨1509365, by rfl⟩ : syracuseStep 2012487 = 3018731) B3018731
theorem B2264053 : Blo 2011435 2264053 := bbase (se 5 (by rfl) ⟨106127, by rfl⟩ : syracuseStep 2264053 = 212255) (by norm_num)
theorem B3018737 : Blo 2011435 3018737 := bstep (se 2 (by rfl) ⟨1132026, by rfl⟩ : syracuseStep 3018737 = 2264053) B2264053
theorem B2012491 : Blo 2011435 2012491 := bstep (se 1 (by rfl) ⟨1509368, by rfl⟩ : syracuseStep 2012491 = 3018737) B3018737
theorem B2547065 : Blo 2011435 2547065 := bbase (se 2 (by rfl) ⟨955149, by rfl⟩ : syracuseStep 2547065 = 1910299) (by norm_num)
theorem B6792173 : Blo 2011435 6792173 := bstep (se 3 (by rfl) ⟨1273532, by rfl⟩ : syracuseStep 6792173 = 2547065) B2547065
theorem B4528115 : Blo 2011435 4528115 := bstep (se 1 (by rfl) ⟨3396086, by rfl⟩ : syracuseStep 4528115 = 6792173) B6792173
theorem B3018743 : Blo 2011435 3018743 := bstep (se 1 (by rfl) ⟨2264057, by rfl⟩ : syracuseStep 3018743 = 4528115) B4528115
theorem B2012495 : Blo 2011435 2012495 := bstep (se 1 (by rfl) ⟨1509371, by rfl⟩ : syracuseStep 2012495 = 3018743) B3018743
theorem B3018749 : Blo 2011435 3018749 := bbase (se 3 (by rfl) ⟨566015, by rfl⟩ : syracuseStep 3018749 = 1132031) (by norm_num)
theorem B2012499 : Blo 2011435 2012499 := bstep (se 1 (by rfl) ⟨1509374, by rfl⟩ : syracuseStep 2012499 = 3018749) B3018749
theorem B4528133 : Blo 2011435 4528133 := bbase (se 4 (by rfl) ⟨424512, by rfl⟩ : syracuseStep 4528133 = 849025) (by norm_num)
theorem B3018755 : Blo 2011435 3018755 := bstep (se 1 (by rfl) ⟨2264066, by rfl⟩ : syracuseStep 3018755 = 4528133) B4528133
theorem B2012503 : Blo 2011435 2012503 := bstep (se 1 (by rfl) ⟨1509377, by rfl⟩ : syracuseStep 2012503 = 3018755) B3018755
theorem B3820621 : Blo 2011435 3820621 := bbase (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) (by norm_num)
theorem B5094161 : Blo 2011435 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B3396107 : Blo 2011435 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B2264071 : Blo 2011435 2264071 := bstep (se 1 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 2264071 = 3396107) B3396107
theorem B3018761 : Blo 2011435 3018761 := bstep (se 2 (by rfl) ⟨1132035, by rfl⟩ : syracuseStep 3018761 = 2264071) B2264071
theorem B2012507 : Blo 2011435 2012507 := bstep (se 1 (by rfl) ⟨1509380, by rfl⟩ : syracuseStep 2012507 = 3018761) B3018761
theorem B10188341 : Blo 2011435 10188341 := bbase (se 5 (by rfl) ⟨477578, by rfl⟩ : syracuseStep 10188341 = 955157) (by norm_num)
theorem B6792227 : Blo 2011435 6792227 := bstep (se 1 (by rfl) ⟨5094170, by rfl⟩ : syracuseStep 6792227 = 10188341) B10188341
theorem B4528151 : Blo 2011435 4528151 := bstep (se 1 (by rfl) ⟨3396113, by rfl⟩ : syracuseStep 4528151 = 6792227) B6792227
theorem B3018767 : Blo 2011435 3018767 := bstep (se 1 (by rfl) ⟨2264075, by rfl⟩ : syracuseStep 3018767 = 4528151) B4528151
theorem B2012511 : Blo 2011435 2012511 := bstep (se 1 (by rfl) ⟨1509383, by rfl⟩ : syracuseStep 2012511 = 3018767) B3018767
theorem B3018773 : Blo 2011435 3018773 := bbase (se 6 (by rfl) ⟨70752, by rfl⟩ : syracuseStep 3018773 = 141505) (by norm_num)
theorem B2012515 : Blo 2011435 2012515 := bstep (se 1 (by rfl) ⟨1509386, by rfl⟩ : syracuseStep 2012515 = 3018773) B3018773
theorem B5439941 : Blo 2011435 5439941 := bbase (se 4 (by rfl) ⟨509994, by rfl⟩ : syracuseStep 5439941 = 1019989) (by norm_num)
theorem B3626627 : Blo 2011435 3626627 := bstep (se 1 (by rfl) ⟨2719970, by rfl⟩ : syracuseStep 3626627 = 5439941) B5439941
theorem B9671005 : Blo 2011435 9671005 := bstep (se 3 (by rfl) ⟨1813313, by rfl⟩ : syracuseStep 9671005 = 3626627) B3626627
theorem B12894673 : Blo 2011435 12894673 := bstep (se 2 (by rfl) ⟨4835502, by rfl⟩ : syracuseStep 12894673 = 9671005) B9671005
theorem B17192897 : Blo 2011435 17192897 := bstep (se 2 (by rfl) ⟨6447336, by rfl⟩ : syracuseStep 17192897 = 12894673) B12894673
theorem B11461931 : Blo 2011435 11461931 := bstep (se 1 (by rfl) ⟨8596448, by rfl⟩ : syracuseStep 11461931 = 17192897) B17192897
theorem B7641287 : Blo 2011435 7641287 := bstep (se 1 (by rfl) ⟨5730965, by rfl⟩ : syracuseStep 7641287 = 11461931) B11461931
theorem B5094191 : Blo 2011435 5094191 := bstep (se 1 (by rfl) ⟨3820643, by rfl⟩ : syracuseStep 5094191 = 7641287) B7641287
theorem B3396127 : Blo 2011435 3396127 := bstep (se 1 (by rfl) ⟨2547095, by rfl⟩ : syracuseStep 3396127 = 5094191) B5094191
theorem B4528169 : Blo 2011435 4528169 := bstep (se 2 (by rfl) ⟨1698063, by rfl⟩ : syracuseStep 4528169 = 3396127) B3396127
theorem B3018779 : Blo 2011435 3018779 := bstep (se 1 (by rfl) ⟨2264084, by rfl⟩ : syracuseStep 3018779 = 4528169) B4528169
theorem B2012519 : Blo 2011435 2012519 := bstep (se 1 (by rfl) ⟨1509389, by rfl⟩ : syracuseStep 2012519 = 3018779) B3018779
theorem B2264089 : Blo 2011435 2264089 := bbase (se 2 (by rfl) ⟨849033, by rfl⟩ : syracuseStep 2264089 = 1698067) (by norm_num)
theorem B3018785 : Blo 2011435 3018785 := bstep (se 2 (by rfl) ⟨1132044, by rfl⟩ : syracuseStep 3018785 = 2264089) B2264089
theorem B2012523 : Blo 2011435 2012523 := bstep (se 1 (by rfl) ⟨1509392, by rfl⟩ : syracuseStep 2012523 = 3018785) B3018785
theorem B7641317 : Blo 2011435 7641317 := bbase (se 4 (by rfl) ⟨716373, by rfl⟩ : syracuseStep 7641317 = 1432747) (by norm_num)
theorem B5094211 : Blo 2011435 5094211 := bstep (se 1 (by rfl) ⟨3820658, by rfl⟩ : syracuseStep 5094211 = 7641317) B7641317
theorem B6792281 : Blo 2011435 6792281 := bstep (se 2 (by rfl) ⟨2547105, by rfl⟩ : syracuseStep 6792281 = 5094211) B5094211
theorem B4528187 : Blo 2011435 4528187 := bstep (se 1 (by rfl) ⟨3396140, by rfl⟩ : syracuseStep 4528187 = 6792281) B6792281
theorem B3018791 : Blo 2011435 3018791 := bstep (se 1 (by rfl) ⟨2264093, by rfl⟩ : syracuseStep 3018791 = 4528187) B4528187
theorem B2012527 : Blo 2011435 2012527 := bstep (se 1 (by rfl) ⟨1509395, by rfl⟩ : syracuseStep 2012527 = 3018791) B3018791
theorem B3018797 : Blo 2011435 3018797 := bbase (se 3 (by rfl) ⟨566024, by rfl⟩ : syracuseStep 3018797 = 1132049) (by norm_num)
theorem B2012531 : Blo 2011435 2012531 := bstep (se 1 (by rfl) ⟨1509398, by rfl⟩ : syracuseStep 2012531 = 3018797) B3018797
theorem B4528205 : Blo 2011435 4528205 := bbase (se 3 (by rfl) ⟨849038, by rfl⟩ : syracuseStep 4528205 = 1698077) (by norm_num)
theorem B3018803 : Blo 2011435 3018803 := bstep (se 1 (by rfl) ⟨2264102, by rfl⟩ : syracuseStep 3018803 = 4528205) B4528205
theorem B2012535 : Blo 2011435 2012535 := bstep (se 1 (by rfl) ⟨1509401, by rfl⟩ : syracuseStep 2012535 = 3018803) B3018803
theorem B2547121 : Blo 2011435 2547121 := bbase (se 2 (by rfl) ⟨955170, by rfl⟩ : syracuseStep 2547121 = 1910341) (by norm_num)
theorem B3396161 : Blo 2011435 3396161 := bstep (se 2 (by rfl) ⟨1273560, by rfl⟩ : syracuseStep 3396161 = 2547121) B2547121
theorem B2264107 : Blo 2011435 2264107 := bstep (se 1 (by rfl) ⟨1698080, by rfl⟩ : syracuseStep 2264107 = 3396161) B3396161
theorem B3018809 : Blo 2011435 3018809 := bstep (se 2 (by rfl) ⟨1132053, by rfl⟩ : syracuseStep 3018809 = 2264107) B2264107
theorem B2012539 : Blo 2011435 2012539 := bstep (se 1 (by rfl) ⟨1509404, by rfl⟩ : syracuseStep 2012539 = 3018809) B3018809
theorem B6447413 : Blo 2011435 6447413 := bbase (se 5 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 6447413 = 604445) (by norm_num)
theorem B4298275 : Blo 2011435 4298275 := bstep (se 1 (by rfl) ⟨3223706, by rfl⟩ : syracuseStep 4298275 = 6447413) B6447413
theorem B22924133 : Blo 2011435 22924133 := bstep (se 4 (by rfl) ⟨2149137, by rfl⟩ : syracuseStep 22924133 = 4298275) B4298275
theorem B15282755 : Blo 2011435 15282755 := bstep (se 1 (by rfl) ⟨11462066, by rfl⟩ : syracuseStep 15282755 = 22924133) B22924133
theorem B10188503 : Blo 2011435 10188503 := bstep (se 1 (by rfl) ⟨7641377, by rfl⟩ : syracuseStep 10188503 = 15282755) B15282755
theorem B6792335 : Blo 2011435 6792335 := bstep (se 1 (by rfl) ⟨5094251, by rfl⟩ : syracuseStep 6792335 = 10188503) B10188503
theorem B4528223 : Blo 2011435 4528223 := bstep (se 1 (by rfl) ⟨3396167, by rfl⟩ : syracuseStep 4528223 = 6792335) B6792335
theorem B3018815 : Blo 2011435 3018815 := bstep (se 1 (by rfl) ⟨2264111, by rfl⟩ : syracuseStep 3018815 = 4528223) B4528223
theorem B2012543 : Blo 2011435 2012543 := bstep (se 1 (by rfl) ⟨1509407, by rfl⟩ : syracuseStep 2012543 = 3018815) B3018815
theorem B3018821 : Blo 2011435 3018821 := bbase (se 4 (by rfl) ⟨283014, by rfl⟩ : syracuseStep 3018821 = 566029) (by norm_num)
theorem B2012547 : Blo 2011435 2012547 := bstep (se 1 (by rfl) ⟨1509410, by rfl⟩ : syracuseStep 2012547 = 3018821) B3018821
theorem B3396181 : Blo 2011435 3396181 := bbase (se 8 (by rfl) ⟨19899, by rfl⟩ : syracuseStep 3396181 = 39799) (by norm_num)
theorem B4528241 : Blo 2011435 4528241 := bstep (se 2 (by rfl) ⟨1698090, by rfl⟩ : syracuseStep 4528241 = 3396181) B3396181
theorem B3018827 : Blo 2011435 3018827 := bstep (se 1 (by rfl) ⟨2264120, by rfl⟩ : syracuseStep 3018827 = 4528241) B4528241
theorem B2012551 : Blo 2011435 2012551 := bstep (se 1 (by rfl) ⟨1509413, by rfl⟩ : syracuseStep 2012551 = 3018827) B3018827
theorem B2264125 : Blo 2011435 2264125 := bbase (se 3 (by rfl) ⟨424523, by rfl⟩ : syracuseStep 2264125 = 849047) (by norm_num)
theorem B3018833 : Blo 2011435 3018833 := bstep (se 2 (by rfl) ⟨1132062, by rfl⟩ : syracuseStep 3018833 = 2264125) B2264125
theorem B2012555 : Blo 2011435 2012555 := bstep (se 1 (by rfl) ⟨1509416, by rfl⟩ : syracuseStep 2012555 = 3018833) B3018833
theorem B6792389 : Blo 2011435 6792389 := bbase (se 4 (by rfl) ⟨636786, by rfl⟩ : syracuseStep 6792389 = 1273573) (by norm_num)
theorem B4528259 : Blo 2011435 4528259 := bstep (se 1 (by rfl) ⟨3396194, by rfl⟩ : syracuseStep 4528259 = 6792389) B6792389
theorem B3018839 : Blo 2011435 3018839 := bstep (se 1 (by rfl) ⟨2264129, by rfl⟩ : syracuseStep 3018839 = 4528259) B4528259
theorem B2012559 : Blo 2011435 2012559 := bstep (se 1 (by rfl) ⟨1509419, by rfl⟩ : syracuseStep 2012559 = 3018839) B3018839
theorem B3018845 : Blo 2011435 3018845 := bbase (se 3 (by rfl) ⟨566033, by rfl⟩ : syracuseStep 3018845 = 1132067) (by norm_num)
theorem B2012563 : Blo 2011435 2012563 := bstep (se 1 (by rfl) ⟨1509422, by rfl⟩ : syracuseStep 2012563 = 3018845) B3018845
theorem B4528277 : Blo 2011435 4528277 := bbase (se 6 (by rfl) ⟨106131, by rfl⟩ : syracuseStep 4528277 = 212263) (by norm_num)
theorem B3018851 : Blo 2011435 3018851 := bstep (se 1 (by rfl) ⟨2264138, by rfl⟩ : syracuseStep 3018851 = 4528277) B4528277
theorem B2012567 : Blo 2011435 2012567 := bstep (se 1 (by rfl) ⟨1509425, by rfl⟩ : syracuseStep 2012567 = 3018851) B3018851
theorem B2865557 : Blo 2011435 2865557 := bbase (se 6 (by rfl) ⟨67161, by rfl⟩ : syracuseStep 2865557 = 134323) (by norm_num)
theorem B7641485 : Blo 2011435 7641485 := bstep (se 3 (by rfl) ⟨1432778, by rfl⟩ : syracuseStep 7641485 = 2865557) B2865557
theorem B5094323 : Blo 2011435 5094323 := bstep (se 1 (by rfl) ⟨3820742, by rfl⟩ : syracuseStep 5094323 = 7641485) B7641485
theorem B3396215 : Blo 2011435 3396215 := bstep (se 1 (by rfl) ⟨2547161, by rfl⟩ : syracuseStep 3396215 = 5094323) B5094323
theorem B2264143 : Blo 2011435 2264143 := bstep (se 1 (by rfl) ⟨1698107, by rfl⟩ : syracuseStep 2264143 = 3396215) B3396215
theorem B3018857 : Blo 2011435 3018857 := bstep (se 2 (by rfl) ⟨1132071, by rfl⟩ : syracuseStep 3018857 = 2264143) B2264143
theorem B2012571 : Blo 2011435 2012571 := bstep (se 1 (by rfl) ⟨1509428, by rfl⟩ : syracuseStep 2012571 = 3018857) B3018857
theorem B13070965 : Blo 2011435 13070965 := bbase (se 5 (by rfl) ⟨612701, by rfl⟩ : syracuseStep 13070965 = 1225403) (by norm_num)
theorem B17427953 : Blo 2011435 17427953 := bstep (se 2 (by rfl) ⟨6535482, by rfl⟩ : syracuseStep 17427953 = 13070965) B13070965
theorem B11618635 : Blo 2011435 11618635 := bstep (se 1 (by rfl) ⟨8713976, by rfl⟩ : syracuseStep 11618635 = 17427953) B17427953
theorem B15491513 : Blo 2011435 15491513 := bstep (se 2 (by rfl) ⟨5809317, by rfl⟩ : syracuseStep 15491513 = 11618635) B11618635
theorem B10327675 : Blo 2011435 10327675 := bstep (se 1 (by rfl) ⟨7745756, by rfl⟩ : syracuseStep 10327675 = 15491513) B15491513
theorem B13770233 : Blo 2011435 13770233 := bstep (se 2 (by rfl) ⟨5163837, by rfl⟩ : syracuseStep 13770233 = 10327675) B10327675
theorem B9180155 : Blo 2011435 9180155 := bstep (se 1 (by rfl) ⟨6885116, by rfl⟩ : syracuseStep 9180155 = 13770233) B13770233
theorem B24480413 : Blo 2011435 24480413 := bstep (se 3 (by rfl) ⟨4590077, by rfl⟩ : syracuseStep 24480413 = 9180155) B9180155
theorem B16320275 : Blo 2011435 16320275 := bstep (se 1 (by rfl) ⟨12240206, by rfl⟩ : syracuseStep 16320275 = 24480413) B24480413
theorem B10880183 : Blo 2011435 10880183 := bstep (se 1 (by rfl) ⟨8160137, by rfl⟩ : syracuseStep 10880183 = 16320275) B16320275
theorem B29013821 : Blo 2011435 29013821 := bstep (se 3 (by rfl) ⟨5440091, by rfl⟩ : syracuseStep 29013821 = 10880183) B10880183
theorem B19342547 : Blo 2011435 19342547 := bstep (se 1 (by rfl) ⟨14506910, by rfl⟩ : syracuseStep 19342547 = 29013821) B29013821
theorem B12895031 : Blo 2011435 12895031 := bstep (se 1 (by rfl) ⟨9671273, by rfl⟩ : syracuseStep 12895031 = 19342547) B19342547
theorem B8596687 : Blo 2011435 8596687 := bstep (se 1 (by rfl) ⟨6447515, by rfl⟩ : syracuseStep 8596687 = 12895031) B12895031
theorem B11462249 : Blo 2011435 11462249 := bstep (se 2 (by rfl) ⟨4298343, by rfl⟩ : syracuseStep 11462249 = 8596687) B8596687
theorem B7641499 : Blo 2011435 7641499 := bstep (se 1 (by rfl) ⟨5731124, by rfl⟩ : syracuseStep 7641499 = 11462249) B11462249
theorem B10188665 : Blo 2011435 10188665 := bstep (se 2 (by rfl) ⟨3820749, by rfl⟩ : syracuseStep 10188665 = 7641499) B7641499
theorem B6792443 : Blo 2011435 6792443 := bstep (se 1 (by rfl) ⟨5094332, by rfl⟩ : syracuseStep 6792443 = 10188665) B10188665
theorem B4528295 : Blo 2011435 4528295 := bstep (se 1 (by rfl) ⟨3396221, by rfl⟩ : syracuseStep 4528295 = 6792443) B6792443
theorem B3018863 : Blo 2011435 3018863 := bstep (se 1 (by rfl) ⟨2264147, by rfl⟩ : syracuseStep 3018863 = 4528295) B4528295
theorem B2012575 : Blo 2011435 2012575 := bstep (se 1 (by rfl) ⟨1509431, by rfl⟩ : syracuseStep 2012575 = 3018863) B3018863
theorem B3018869 : Blo 2011435 3018869 := bbase (se 5 (by rfl) ⟨141509, by rfl⟩ : syracuseStep 3018869 = 283019) (by norm_num)
theorem B2012579 : Blo 2011435 2012579 := bstep (se 1 (by rfl) ⟨1509434, by rfl⟩ : syracuseStep 2012579 = 3018869) B3018869
theorem B3820765 : Blo 2011435 3820765 := bbase (se 3 (by rfl) ⟨716393, by rfl⟩ : syracuseStep 3820765 = 1432787) (by norm_num)
theorem B5094353 : Blo 2011435 5094353 := bstep (se 2 (by rfl) ⟨1910382, by rfl⟩ : syracuseStep 5094353 = 3820765) B3820765
theorem B3396235 : Blo 2011435 3396235 := bstep (se 1 (by rfl) ⟨2547176, by rfl⟩ : syracuseStep 3396235 = 5094353) B5094353
theorem B4528313 : Blo 2011435 4528313 := bstep (se 2 (by rfl) ⟨1698117, by rfl⟩ : syracuseStep 4528313 = 3396235) B3396235
theorem B3018875 : Blo 2011435 3018875 := bstep (se 1 (by rfl) ⟨2264156, by rfl⟩ : syracuseStep 3018875 = 4528313) B4528313
theorem B2012583 : Blo 2011435 2012583 := bstep (se 1 (by rfl) ⟨1509437, by rfl⟩ : syracuseStep 2012583 = 3018875) B3018875
theorem B2264161 : Blo 2011435 2264161 := bbase (se 2 (by rfl) ⟨849060, by rfl⟩ : syracuseStep 2264161 = 1698121) (by norm_num)
theorem B3018881 : Blo 2011435 3018881 := bstep (se 2 (by rfl) ⟨1132080, by rfl⟩ : syracuseStep 3018881 = 2264161) B2264161
theorem B2012587 : Blo 2011435 2012587 := bstep (se 1 (by rfl) ⟨1509440, by rfl⟩ : syracuseStep 2012587 = 3018881) B3018881
theorem B5094373 : Blo 2011435 5094373 := bbase (se 4 (by rfl) ⟨477597, by rfl⟩ : syracuseStep 5094373 = 955195) (by norm_num)
theorem B6792497 : Blo 2011435 6792497 := bstep (se 2 (by rfl) ⟨2547186, by rfl⟩ : syracuseStep 6792497 = 5094373) B5094373
theorem B4528331 : Blo 2011435 4528331 := bstep (se 1 (by rfl) ⟨3396248, by rfl⟩ : syracuseStep 4528331 = 6792497) B6792497
theorem B3018887 : Blo 2011435 3018887 := bstep (se 1 (by rfl) ⟨2264165, by rfl⟩ : syracuseStep 3018887 = 4528331) B4528331
theorem B2012591 : Blo 2011435 2012591 := bstep (se 1 (by rfl) ⟨1509443, by rfl⟩ : syracuseStep 2012591 = 3018887) B3018887
theorem B3018893 : Blo 2011435 3018893 := bbase (se 3 (by rfl) ⟨566042, by rfl⟩ : syracuseStep 3018893 = 1132085) (by norm_num)
theorem B2012595 : Blo 2011435 2012595 := bstep (se 1 (by rfl) ⟨1509446, by rfl⟩ : syracuseStep 2012595 = 3018893) B3018893
theorem B4528349 : Blo 2011435 4528349 := bbase (se 3 (by rfl) ⟨849065, by rfl⟩ : syracuseStep 4528349 = 1698131) (by norm_num)
theorem B3018899 : Blo 2011435 3018899 := bstep (se 1 (by rfl) ⟨2264174, by rfl⟩ : syracuseStep 3018899 = 4528349) B4528349
theorem B2012599 : Blo 2011435 2012599 := bstep (se 1 (by rfl) ⟨1509449, by rfl⟩ : syracuseStep 2012599 = 3018899) B3018899
theorem B3396269 : Blo 2011435 3396269 := bbase (se 3 (by rfl) ⟨636800, by rfl⟩ : syracuseStep 3396269 = 1273601) (by norm_num)
theorem B2264179 : Blo 2011435 2264179 := bstep (se 1 (by rfl) ⟨1698134, by rfl⟩ : syracuseStep 2264179 = 3396269) B3396269
theorem B3018905 : Blo 2011435 3018905 := bstep (se 2 (by rfl) ⟨1132089, by rfl⟩ : syracuseStep 3018905 = 2264179) B2264179
theorem B2012603 : Blo 2011435 2012603 := bstep (se 1 (by rfl) ⟨1509452, by rfl⟩ : syracuseStep 2012603 = 3018905) B3018905
theorem B16320533 : Blo 2011435 16320533 := bbase (se 6 (by rfl) ⟨382512, by rfl⟩ : syracuseStep 16320533 = 765025) (by norm_num)
theorem B43521421 : Blo 2011435 43521421 := bstep (se 3 (by rfl) ⟨8160266, by rfl⟩ : syracuseStep 43521421 = 16320533) B16320533
theorem B58028561 : Blo 2011435 58028561 := bstep (se 2 (by rfl) ⟨21760710, by rfl⟩ : syracuseStep 58028561 = 43521421) B43521421
theorem B38685707 : Blo 2011435 38685707 := bstep (se 1 (by rfl) ⟨29014280, by rfl⟩ : syracuseStep 38685707 = 58028561) B58028561
theorem B25790471 : Blo 2011435 25790471 := bstep (se 1 (by rfl) ⟨19342853, by rfl⟩ : syracuseStep 25790471 = 38685707) B38685707
theorem B17193647 : Blo 2011435 17193647 := bstep (se 1 (by rfl) ⟨12895235, by rfl⟩ : syracuseStep 17193647 = 25790471) B25790471
theorem B11462431 : Blo 2011435 11462431 := bstep (se 1 (by rfl) ⟨8596823, by rfl⟩ : syracuseStep 11462431 = 17193647) B17193647
theorem B15283241 : Blo 2011435 15283241 := bstep (se 2 (by rfl) ⟨5731215, by rfl⟩ : syracuseStep 15283241 = 11462431) B11462431
theorem B10188827 : Blo 2011435 10188827 := bstep (se 1 (by rfl) ⟨7641620, by rfl⟩ : syracuseStep 10188827 = 15283241) B15283241
theorem B6792551 : Blo 2011435 6792551 := bstep (se 1 (by rfl) ⟨5094413, by rfl⟩ : syracuseStep 6792551 = 10188827) B10188827
theorem B4528367 : Blo 2011435 4528367 := bstep (se 1 (by rfl) ⟨3396275, by rfl⟩ : syracuseStep 4528367 = 6792551) B6792551
theorem B3018911 : Blo 2011435 3018911 := bstep (se 1 (by rfl) ⟨2264183, by rfl⟩ : syracuseStep 3018911 = 4528367) B4528367
theorem B2012607 : Blo 2011435 2012607 := bstep (se 1 (by rfl) ⟨1509455, by rfl⟩ : syracuseStep 2012607 = 3018911) B3018911
theorem B3018917 : Blo 2011435 3018917 := bbase (se 4 (by rfl) ⟨283023, by rfl⟩ : syracuseStep 3018917 = 566047) (by norm_num)
theorem B2012611 : Blo 2011435 2012611 := bstep (se 1 (by rfl) ⟨1509458, by rfl⟩ : syracuseStep 2012611 = 3018917) B3018917
theorem B2547217 : Blo 2011435 2547217 := bbase (se 2 (by rfl) ⟨955206, by rfl⟩ : syracuseStep 2547217 = 1910413) (by norm_num)
theorem B3396289 : Blo 2011435 3396289 := bstep (se 2 (by rfl) ⟨1273608, by rfl⟩ : syracuseStep 3396289 = 2547217) B2547217
theorem B4528385 : Blo 2011435 4528385 := bstep (se 2 (by rfl) ⟨1698144, by rfl⟩ : syracuseStep 4528385 = 3396289) B3396289
theorem B3018923 : Blo 2011435 3018923 := bstep (se 1 (by rfl) ⟨2264192, by rfl⟩ : syracuseStep 3018923 = 4528385) B4528385
theorem B2012615 : Blo 2011435 2012615 := bstep (se 1 (by rfl) ⟨1509461, by rfl⟩ : syracuseStep 2012615 = 3018923) B3018923
theorem B2264197 : Blo 2011435 2264197 := bbase (se 4 (by rfl) ⟨212268, by rfl⟩ : syracuseStep 2264197 = 424537) (by norm_num)
theorem B3018929 : Blo 2011435 3018929 := bstep (se 2 (by rfl) ⟨1132098, by rfl⟩ : syracuseStep 3018929 = 2264197) B2264197
theorem B2012619 : Blo 2011435 2012619 := bstep (se 1 (by rfl) ⟨1509464, by rfl⟩ : syracuseStep 2012619 = 3018929) B3018929
theorem B10327925 : Blo 2011435 10327925 := bbase (se 5 (by rfl) ⟨484121, by rfl⟩ : syracuseStep 10327925 = 968243) (by norm_num)
theorem B27541133 : Blo 2011435 27541133 := bstep (se 3 (by rfl) ⟨5163962, by rfl⟩ : syracuseStep 27541133 = 10327925) B10327925
theorem B18360755 : Blo 2011435 18360755 := bstep (se 1 (by rfl) ⟨13770566, by rfl⟩ : syracuseStep 18360755 = 27541133) B27541133
theorem B12240503 : Blo 2011435 12240503 := bstep (se 1 (by rfl) ⟨9180377, by rfl⟩ : syracuseStep 12240503 = 18360755) B18360755
theorem B8160335 : Blo 2011435 8160335 := bstep (se 1 (by rfl) ⟨6120251, by rfl⟩ : syracuseStep 8160335 = 12240503) B12240503
theorem B5440223 : Blo 2011435 5440223 := bstep (se 1 (by rfl) ⟨4080167, by rfl⟩ : syracuseStep 5440223 = 8160335) B8160335
theorem B14507261 : Blo 2011435 14507261 := bstep (se 3 (by rfl) ⟨2720111, by rfl⟩ : syracuseStep 14507261 = 5440223) B5440223
theorem B9671507 : Blo 2011435 9671507 := bstep (se 1 (by rfl) ⟨7253630, by rfl⟩ : syracuseStep 9671507 = 14507261) B14507261
theorem B6447671 : Blo 2011435 6447671 := bstep (se 1 (by rfl) ⟨4835753, by rfl⟩ : syracuseStep 6447671 = 9671507) B9671507
theorem B4298447 : Blo 2011435 4298447 := bstep (se 1 (by rfl) ⟨3223835, by rfl⟩ : syracuseStep 4298447 = 6447671) B6447671
theorem B2865631 : Blo 2011435 2865631 := bstep (se 1 (by rfl) ⟨2149223, by rfl⟩ : syracuseStep 2865631 = 4298447) B4298447
theorem B3820841 : Blo 2011435 3820841 := bstep (se 2 (by rfl) ⟨1432815, by rfl⟩ : syracuseStep 3820841 = 2865631) B2865631
theorem B2547227 : Blo 2011435 2547227 := bstep (se 1 (by rfl) ⟨1910420, by rfl⟩ : syracuseStep 2547227 = 3820841) B3820841
theorem B6792605 : Blo 2011435 6792605 := bstep (se 3 (by rfl) ⟨1273613, by rfl⟩ : syracuseStep 6792605 = 2547227) B2547227
theorem B4528403 : Blo 2011435 4528403 := bstep (se 1 (by rfl) ⟨3396302, by rfl⟩ : syracuseStep 4528403 = 6792605) B6792605
theorem B3018935 : Blo 2011435 3018935 := bstep (se 1 (by rfl) ⟨2264201, by rfl⟩ : syracuseStep 3018935 = 4528403) B4528403
theorem B2012623 : Blo 2011435 2012623 := bstep (se 1 (by rfl) ⟨1509467, by rfl⟩ : syracuseStep 2012623 = 3018935) B3018935
theorem B3018941 : Blo 2011435 3018941 := bbase (se 3 (by rfl) ⟨566051, by rfl⟩ : syracuseStep 3018941 = 1132103) (by norm_num)
theorem B2012627 : Blo 2011435 2012627 := bstep (se 1 (by rfl) ⟨1509470, by rfl⟩ : syracuseStep 2012627 = 3018941) B3018941
theorem B4528421 : Blo 2011435 4528421 := bbase (se 4 (by rfl) ⟨424539, by rfl⟩ : syracuseStep 4528421 = 849079) (by norm_num)
theorem B3018947 : Blo 2011435 3018947 := bstep (se 1 (by rfl) ⟨2264210, by rfl⟩ : syracuseStep 3018947 = 4528421) B4528421
theorem B2012631 : Blo 2011435 2012631 := bstep (se 1 (by rfl) ⟨1509473, by rfl⟩ : syracuseStep 2012631 = 3018947) B3018947
theorem B5094485 : Blo 2011435 5094485 := bbase (se 8 (by rfl) ⟨29850, by rfl⟩ : syracuseStep 5094485 = 59701) (by norm_num)
theorem B3396323 : Blo 2011435 3396323 := bstep (se 1 (by rfl) ⟨2547242, by rfl⟩ : syracuseStep 3396323 = 5094485) B5094485
theorem B2264215 : Blo 2011435 2264215 := bstep (se 1 (by rfl) ⟨1698161, by rfl⟩ : syracuseStep 2264215 = 3396323) B3396323
theorem B3018953 : Blo 2011435 3018953 := bstep (se 2 (by rfl) ⟨1132107, by rfl⟩ : syracuseStep 3018953 = 2264215) B2264215
theorem B2012635 : Blo 2011435 2012635 := bstep (se 1 (by rfl) ⟨1509476, by rfl⟩ : syracuseStep 2012635 = 3018953) B3018953
theorem B7746005 : Blo 2011435 7746005 := bbase (se 7 (by rfl) ⟨90773, by rfl⟩ : syracuseStep 7746005 = 181547) (by norm_num)
theorem B5164003 : Blo 2011435 5164003 := bstep (se 1 (by rfl) ⟨3873002, by rfl⟩ : syracuseStep 5164003 = 7746005) B7746005
theorem B6885337 : Blo 2011435 6885337 := bstep (se 2 (by rfl) ⟨2582001, by rfl⟩ : syracuseStep 6885337 = 5164003) B5164003
theorem B9180449 : Blo 2011435 9180449 := bstep (se 2 (by rfl) ⟨3442668, by rfl⟩ : syracuseStep 9180449 = 6885337) B6885337
theorem B6120299 : Blo 2011435 6120299 := bstep (se 1 (by rfl) ⟨4590224, by rfl⟩ : syracuseStep 6120299 = 9180449) B9180449
theorem B16320797 : Blo 2011435 16320797 := bstep (se 3 (by rfl) ⟨3060149, by rfl⟩ : syracuseStep 16320797 = 6120299) B6120299
theorem B10880531 : Blo 2011435 10880531 := bstep (se 1 (by rfl) ⟨8160398, by rfl⟩ : syracuseStep 10880531 = 16320797) B16320797
theorem B7253687 : Blo 2011435 7253687 := bstep (se 1 (by rfl) ⟨5440265, by rfl⟩ : syracuseStep 7253687 = 10880531) B10880531
theorem B4835791 : Blo 2011435 4835791 := bstep (se 1 (by rfl) ⟨3626843, by rfl⟩ : syracuseStep 4835791 = 7253687) B7253687
theorem B6447721 : Blo 2011435 6447721 := bstep (se 2 (by rfl) ⟨2417895, by rfl⟩ : syracuseStep 6447721 = 4835791) B4835791
theorem B8596961 : Blo 2011435 8596961 := bstep (se 2 (by rfl) ⟨3223860, by rfl⟩ : syracuseStep 8596961 = 6447721) B6447721
theorem B5731307 : Blo 2011435 5731307 := bstep (se 1 (by rfl) ⟨4298480, by rfl⟩ : syracuseStep 5731307 = 8596961) B8596961
theorem B3820871 : Blo 2011435 3820871 := bstep (se 1 (by rfl) ⟨2865653, by rfl⟩ : syracuseStep 3820871 = 5731307) B5731307
theorem B10188989 : Blo 2011435 10188989 := bstep (se 3 (by rfl) ⟨1910435, by rfl⟩ : syracuseStep 10188989 = 3820871) B3820871
theorem B6792659 : Blo 2011435 6792659 := bstep (se 1 (by rfl) ⟨5094494, by rfl⟩ : syracuseStep 6792659 = 10188989) B10188989
theorem B4528439 : Blo 2011435 4528439 := bstep (se 1 (by rfl) ⟨3396329, by rfl⟩ : syracuseStep 4528439 = 6792659) B6792659
theorem B3018959 : Blo 2011435 3018959 := bstep (se 1 (by rfl) ⟨2264219, by rfl⟩ : syracuseStep 3018959 = 4528439) B4528439
theorem B2012639 : Blo 2011435 2012639 := bstep (se 1 (by rfl) ⟨1509479, by rfl⟩ : syracuseStep 2012639 = 3018959) B3018959
theorem B3018965 : Blo 2011435 3018965 := bbase (se 7 (by rfl) ⟨35378, by rfl⟩ : syracuseStep 3018965 = 70757) (by norm_num)
theorem B2012643 : Blo 2011435 2012643 := bstep (se 1 (by rfl) ⟨1509482, by rfl⟩ : syracuseStep 2012643 = 3018965) B3018965
theorem B2149249 : Blo 2011435 2149249 := bbase (se 2 (by rfl) ⟨805968, by rfl⟩ : syracuseStep 2149249 = 1611937) (by norm_num)
theorem B2865665 : Blo 2011435 2865665 := bstep (se 2 (by rfl) ⟨1074624, by rfl⟩ : syracuseStep 2865665 = 2149249) B2149249
theorem B7641773 : Blo 2011435 7641773 := bstep (se 3 (by rfl) ⟨1432832, by rfl⟩ : syracuseStep 7641773 = 2865665) B2865665
theorem B5094515 : Blo 2011435 5094515 := bstep (se 1 (by rfl) ⟨3820886, by rfl⟩ : syracuseStep 5094515 = 7641773) B7641773
theorem B3396343 : Blo 2011435 3396343 := bstep (se 1 (by rfl) ⟨2547257, by rfl⟩ : syracuseStep 3396343 = 5094515) B5094515
theorem B4528457 : Blo 2011435 4528457 := bstep (se 2 (by rfl) ⟨1698171, by rfl⟩ : syracuseStep 4528457 = 3396343) B3396343
theorem B3018971 : Blo 2011435 3018971 := bstep (se 1 (by rfl) ⟨2264228, by rfl⟩ : syracuseStep 3018971 = 4528457) B4528457
theorem B2012647 : Blo 2011435 2012647 := bstep (se 1 (by rfl) ⟨1509485, by rfl⟩ : syracuseStep 2012647 = 3018971) B3018971
theorem B2264233 : Blo 2011435 2264233 := bbase (se 2 (by rfl) ⟨849087, by rfl⟩ : syracuseStep 2264233 = 1698175) (by norm_num)
theorem B3018977 : Blo 2011435 3018977 := bstep (se 2 (by rfl) ⟨1132116, by rfl⟩ : syracuseStep 3018977 = 2264233) B2264233
theorem B2012651 : Blo 2011435 2012651 := bstep (se 1 (by rfl) ⟨1509488, by rfl⟩ : syracuseStep 2012651 = 3018977) B3018977
theorem B8597029 : Blo 2011435 8597029 := bbase (se 4 (by rfl) ⟨805971, by rfl⟩ : syracuseStep 8597029 = 1611943) (by norm_num)
theorem B11462705 : Blo 2011435 11462705 := bstep (se 2 (by rfl) ⟨4298514, by rfl⟩ : syracuseStep 11462705 = 8597029) B8597029
theorem B7641803 : Blo 2011435 7641803 := bstep (se 1 (by rfl) ⟨5731352, by rfl⟩ : syracuseStep 7641803 = 11462705) B11462705
theorem B5094535 : Blo 2011435 5094535 := bstep (se 1 (by rfl) ⟨3820901, by rfl⟩ : syracuseStep 5094535 = 7641803) B7641803
theorem B6792713 : Blo 2011435 6792713 := bstep (se 2 (by rfl) ⟨2547267, by rfl⟩ : syracuseStep 6792713 = 5094535) B5094535
theorem B4528475 : Blo 2011435 4528475 := bstep (se 1 (by rfl) ⟨3396356, by rfl⟩ : syracuseStep 4528475 = 6792713) B6792713
theorem B3018983 : Blo 2011435 3018983 := bstep (se 1 (by rfl) ⟨2264237, by rfl⟩ : syracuseStep 3018983 = 4528475) B4528475
theorem B2012655 : Blo 2011435 2012655 := bstep (se 1 (by rfl) ⟨1509491, by rfl⟩ : syracuseStep 2012655 = 3018983) B3018983
theorem B3018989 : Blo 2011435 3018989 := bbase (se 3 (by rfl) ⟨566060, by rfl⟩ : syracuseStep 3018989 = 1132121) (by norm_num)
theorem B2012659 : Blo 2011435 2012659 := bstep (se 1 (by rfl) ⟨1509494, by rfl⟩ : syracuseStep 2012659 = 3018989) B3018989
theorem B4528493 : Blo 2011435 4528493 := bbase (se 3 (by rfl) ⟨849092, by rfl⟩ : syracuseStep 4528493 = 1698185) (by norm_num)
theorem B3018995 : Blo 2011435 3018995 := bstep (se 1 (by rfl) ⟨2264246, by rfl⟩ : syracuseStep 3018995 = 4528493) B4528493
theorem B2012663 : Blo 2011435 2012663 := bstep (se 1 (by rfl) ⟨1509497, by rfl⟩ : syracuseStep 2012663 = 3018995) B3018995
theorem B3820925 : Blo 2011435 3820925 := bbase (se 3 (by rfl) ⟨716423, by rfl⟩ : syracuseStep 3820925 = 1432847) (by norm_num)
theorem B2547283 : Blo 2011435 2547283 := bstep (se 1 (by rfl) ⟨1910462, by rfl⟩ : syracuseStep 2547283 = 3820925) B3820925
theorem B3396377 : Blo 2011435 3396377 := bstep (se 2 (by rfl) ⟨1273641, by rfl⟩ : syracuseStep 3396377 = 2547283) B2547283
theorem B2264251 : Blo 2011435 2264251 := bstep (se 1 (by rfl) ⟨1698188, by rfl⟩ : syracuseStep 2264251 = 3396377) B3396377
theorem B3019001 : Blo 2011435 3019001 := bstep (se 2 (by rfl) ⟨1132125, by rfl⟩ : syracuseStep 3019001 = 2264251) B2264251
theorem B2012667 : Blo 2011435 2012667 := bstep (se 1 (by rfl) ⟨1509500, by rfl⟩ : syracuseStep 2012667 = 3019001) B3019001
theorem B27541781 : Blo 2011435 27541781 := bbase (se 6 (by rfl) ⟨645510, by rfl⟩ : syracuseStep 27541781 = 1291021) (by norm_num)
theorem B18361187 : Blo 2011435 18361187 := bstep (se 1 (by rfl) ⟨13770890, by rfl⟩ : syracuseStep 18361187 = 27541781) B27541781
theorem B12240791 : Blo 2011435 12240791 := bstep (se 1 (by rfl) ⟨9180593, by rfl⟩ : syracuseStep 12240791 = 18361187) B18361187
theorem B8160527 : Blo 2011435 8160527 := bstep (se 1 (by rfl) ⟨6120395, by rfl⟩ : syracuseStep 8160527 = 12240791) B12240791
theorem B5440351 : Blo 2011435 5440351 := bstep (se 1 (by rfl) ⟨4080263, by rfl⟩ : syracuseStep 5440351 = 8160527) B8160527
theorem B7253801 : Blo 2011435 7253801 := bstep (se 2 (by rfl) ⟨2720175, by rfl⟩ : syracuseStep 7253801 = 5440351) B5440351
theorem B4835867 : Blo 2011435 4835867 := bstep (se 1 (by rfl) ⟨3626900, by rfl⟩ : syracuseStep 4835867 = 7253801) B7253801
theorem B51582581 : Blo 2011435 51582581 := bstep (se 5 (by rfl) ⟨2417933, by rfl⟩ : syracuseStep 51582581 = 4835867) B4835867
theorem B34388387 : Blo 2011435 34388387 := bstep (se 1 (by rfl) ⟨25791290, by rfl⟩ : syracuseStep 34388387 = 51582581) B51582581
theorem B22925591 : Blo 2011435 22925591 := bstep (se 1 (by rfl) ⟨17194193, by rfl⟩ : syracuseStep 22925591 = 34388387) B34388387
theorem B15283727 : Blo 2011435 15283727 := bstep (se 1 (by rfl) ⟨11462795, by rfl⟩ : syracuseStep 15283727 = 22925591) B22925591
theorem B10189151 : Blo 2011435 10189151 := bstep (se 1 (by rfl) ⟨7641863, by rfl⟩ : syracuseStep 10189151 = 15283727) B15283727
theorem B6792767 : Blo 2011435 6792767 := bstep (se 1 (by rfl) ⟨5094575, by rfl⟩ : syracuseStep 6792767 = 10189151) B10189151
theorem B4528511 : Blo 2011435 4528511 := bstep (se 1 (by rfl) ⟨3396383, by rfl⟩ : syracuseStep 4528511 = 6792767) B6792767
theorem B3019007 : Blo 2011435 3019007 := bstep (se 1 (by rfl) ⟨2264255, by rfl⟩ : syracuseStep 3019007 = 4528511) B4528511
theorem B2012671 : Blo 2011435 2012671 := bstep (se 1 (by rfl) ⟨1509503, by rfl⟩ : syracuseStep 2012671 = 3019007) B3019007
theorem B3019013 : Blo 2011435 3019013 := bbase (se 4 (by rfl) ⟨283032, by rfl⟩ : syracuseStep 3019013 = 566065) (by norm_num)
theorem B2012675 : Blo 2011435 2012675 := bstep (se 1 (by rfl) ⟨1509506, by rfl⟩ : syracuseStep 2012675 = 3019013) B3019013
theorem B3396397 : Blo 2011435 3396397 := bbase (se 3 (by rfl) ⟨636824, by rfl⟩ : syracuseStep 3396397 = 1273649) (by norm_num)
theorem B4528529 : Blo 2011435 4528529 := bstep (se 2 (by rfl) ⟨1698198, by rfl⟩ : syracuseStep 4528529 = 3396397) B3396397
theorem B3019019 : Blo 2011435 3019019 := bstep (se 1 (by rfl) ⟨2264264, by rfl⟩ : syracuseStep 3019019 = 4528529) B4528529
theorem B2012679 : Blo 2011435 2012679 := bstep (se 1 (by rfl) ⟨1509509, by rfl⟩ : syracuseStep 2012679 = 3019019) B3019019
theorem B2264269 : Blo 2011435 2264269 := bbase (se 3 (by rfl) ⟨424550, by rfl⟩ : syracuseStep 2264269 = 849101) (by norm_num)
theorem B3019025 : Blo 2011435 3019025 := bstep (se 2 (by rfl) ⟨1132134, by rfl⟩ : syracuseStep 3019025 = 2264269) B2264269
theorem B2012683 : Blo 2011435 2012683 := bstep (se 1 (by rfl) ⟨1509512, by rfl⟩ : syracuseStep 2012683 = 3019025) B3019025
theorem B6792821 : Blo 2011435 6792821 := bbase (se 5 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 6792821 = 636827) (by norm_num)
theorem B4528547 : Blo 2011435 4528547 := bstep (se 1 (by rfl) ⟨3396410, by rfl⟩ : syracuseStep 4528547 = 6792821) B6792821
theorem B3019031 : Blo 2011435 3019031 := bstep (se 1 (by rfl) ⟨2264273, by rfl⟩ : syracuseStep 3019031 = 4528547) B4528547
theorem B2012687 : Blo 2011435 2012687 := bstep (se 1 (by rfl) ⟨1509515, by rfl⟩ : syracuseStep 2012687 = 3019031) B3019031
theorem B3019037 : Blo 2011435 3019037 := bbase (se 3 (by rfl) ⟨566069, by rfl⟩ : syracuseStep 3019037 = 1132139) (by norm_num)
theorem B2012691 : Blo 2011435 2012691 := bstep (se 1 (by rfl) ⟨1509518, by rfl⟩ : syracuseStep 2012691 = 3019037) B3019037
theorem B4528565 : Blo 2011435 4528565 := bbase (se 5 (by rfl) ⟨212276, by rfl⟩ : syracuseStep 4528565 = 424553) (by norm_num)
theorem B3019043 : Blo 2011435 3019043 := bstep (se 1 (by rfl) ⟨2264282, by rfl⟩ : syracuseStep 3019043 = 4528565) B4528565
theorem B2012695 : Blo 2011435 2012695 := bstep (se 1 (by rfl) ⟨1509521, by rfl⟩ : syracuseStep 2012695 = 3019043) B3019043
theorem B3223957 : Blo 2011435 3223957 := bbase (se 6 (by rfl) ⟨75561, by rfl⟩ : syracuseStep 3223957 = 151123) (by norm_num)
theorem B4298609 : Blo 2011435 4298609 := bstep (se 2 (by rfl) ⟨1611978, by rfl⟩ : syracuseStep 4298609 = 3223957) B3223957
theorem B11462957 : Blo 2011435 11462957 := bstep (se 3 (by rfl) ⟨2149304, by rfl⟩ : syracuseStep 11462957 = 4298609) B4298609
theorem B7641971 : Blo 2011435 7641971 := bstep (se 1 (by rfl) ⟨5731478, by rfl⟩ : syracuseStep 7641971 = 11462957) B11462957
theorem B5094647 : Blo 2011435 5094647 := bstep (se 1 (by rfl) ⟨3820985, by rfl⟩ : syracuseStep 5094647 = 7641971) B7641971
theorem B3396431 : Blo 2011435 3396431 := bstep (se 1 (by rfl) ⟨2547323, by rfl⟩ : syracuseStep 3396431 = 5094647) B5094647
theorem B2264287 : Blo 2011435 2264287 := bstep (se 1 (by rfl) ⟨1698215, by rfl⟩ : syracuseStep 2264287 = 3396431) B3396431
theorem B3019049 : Blo 2011435 3019049 := bstep (se 2 (by rfl) ⟨1132143, by rfl⟩ : syracuseStep 3019049 = 2264287) B2264287
theorem B2012699 : Blo 2011435 2012699 := bstep (se 1 (by rfl) ⟨1509524, by rfl⟩ : syracuseStep 2012699 = 3019049) B3019049
theorem B6885557 : Blo 2011435 6885557 := bbase (se 5 (by rfl) ⟨322760, by rfl⟩ : syracuseStep 6885557 = 645521) (by norm_num)
theorem B4590371 : Blo 2011435 4590371 := bstep (se 1 (by rfl) ⟨3442778, by rfl⟩ : syracuseStep 4590371 = 6885557) B6885557
theorem B12240989 : Blo 2011435 12240989 := bstep (se 3 (by rfl) ⟨2295185, by rfl⟩ : syracuseStep 12240989 = 4590371) B4590371
theorem B8160659 : Blo 2011435 8160659 := bstep (se 1 (by rfl) ⟨6120494, by rfl⟩ : syracuseStep 8160659 = 12240989) B12240989
theorem B5440439 : Blo 2011435 5440439 := bstep (se 1 (by rfl) ⟨4080329, by rfl⟩ : syracuseStep 5440439 = 8160659) B8160659
theorem B3626959 : Blo 2011435 3626959 := bstep (se 1 (by rfl) ⟨2720219, by rfl⟩ : syracuseStep 3626959 = 5440439) B5440439
theorem B4835945 : Blo 2011435 4835945 := bstep (se 2 (by rfl) ⟨1813479, by rfl⟩ : syracuseStep 4835945 = 3626959) B3626959
theorem B3223963 : Blo 2011435 3223963 := bstep (se 1 (by rfl) ⟨2417972, by rfl⟩ : syracuseStep 3223963 = 4835945) B4835945
theorem B4298617 : Blo 2011435 4298617 := bstep (se 2 (by rfl) ⟨1611981, by rfl⟩ : syracuseStep 4298617 = 3223963) B3223963
theorem B5731489 : Blo 2011435 5731489 := bstep (se 2 (by rfl) ⟨2149308, by rfl⟩ : syracuseStep 5731489 = 4298617) B4298617
theorem B7641985 : Blo 2011435 7641985 := bstep (se 2 (by rfl) ⟨2865744, by rfl⟩ : syracuseStep 7641985 = 5731489) B5731489
theorem B10189313 : Blo 2011435 10189313 := bstep (se 2 (by rfl) ⟨3820992, by rfl⟩ : syracuseStep 10189313 = 7641985) B7641985
theorem B6792875 : Blo 2011435 6792875 := bstep (se 1 (by rfl) ⟨5094656, by rfl⟩ : syracuseStep 6792875 = 10189313) B10189313
theorem B4528583 : Blo 2011435 4528583 := bstep (se 1 (by rfl) ⟨3396437, by rfl⟩ : syracuseStep 4528583 = 6792875) B6792875
theorem B3019055 : Blo 2011435 3019055 := bstep (se 1 (by rfl) ⟨2264291, by rfl⟩ : syracuseStep 3019055 = 4528583) B4528583
theorem B2012703 : Blo 2011435 2012703 := bstep (se 1 (by rfl) ⟨1509527, by rfl⟩ : syracuseStep 2012703 = 3019055) B3019055
theorem B3019061 : Blo 2011435 3019061 := bbase (se 5 (by rfl) ⟨141518, by rfl⟩ : syracuseStep 3019061 = 283037) (by norm_num)
theorem B2012707 : Blo 2011435 2012707 := bstep (se 1 (by rfl) ⟨1509530, by rfl⟩ : syracuseStep 2012707 = 3019061) B3019061
theorem B5094677 : Blo 2011435 5094677 := bbase (se 6 (by rfl) ⟨119406, by rfl⟩ : syracuseStep 5094677 = 238813) (by norm_num)
theorem B3396451 : Blo 2011435 3396451 := bstep (se 1 (by rfl) ⟨2547338, by rfl⟩ : syracuseStep 3396451 = 5094677) B5094677
theorem B4528601 : Blo 2011435 4528601 := bstep (se 2 (by rfl) ⟨1698225, by rfl⟩ : syracuseStep 4528601 = 3396451) B3396451
theorem B3019067 : Blo 2011435 3019067 := bstep (se 1 (by rfl) ⟨2264300, by rfl⟩ : syracuseStep 3019067 = 4528601) B4528601
theorem B2012711 : Blo 2011435 2012711 := bstep (se 1 (by rfl) ⟨1509533, by rfl⟩ : syracuseStep 2012711 = 3019067) B3019067
theorem B2264305 : Blo 2011435 2264305 := bbase (se 2 (by rfl) ⟨849114, by rfl⟩ : syracuseStep 2264305 = 1698229) (by norm_num)
theorem B3019073 : Blo 2011435 3019073 := bstep (se 2 (by rfl) ⟨1132152, by rfl⟩ : syracuseStep 3019073 = 2264305) B2264305
theorem B2012715 : Blo 2011435 2012715 := bstep (se 1 (by rfl) ⟨1509536, by rfl⟩ : syracuseStep 2012715 = 3019073) B3019073
theorem B5234669 : Blo 2011435 5234669 := bbase (se 3 (by rfl) ⟨981500, by rfl⟩ : syracuseStep 5234669 = 1963001) (by norm_num)
theorem B3489779 : Blo 2011435 3489779 := bstep (se 1 (by rfl) ⟨2617334, by rfl⟩ : syracuseStep 3489779 = 5234669) B5234669
theorem B2326519 : Blo 2011435 2326519 := bstep (se 1 (by rfl) ⟨1744889, by rfl⟩ : syracuseStep 2326519 = 3489779) B3489779
theorem B3102025 : Blo 2011435 3102025 := bstep (se 2 (by rfl) ⟨1163259, by rfl⟩ : syracuseStep 3102025 = 2326519) B2326519
theorem B4136033 : Blo 2011435 4136033 := bstep (se 2 (by rfl) ⟨1551012, by rfl⟩ : syracuseStep 4136033 = 3102025) B3102025
theorem B11029421 : Blo 2011435 11029421 := bstep (se 3 (by rfl) ⟨2068016, by rfl⟩ : syracuseStep 11029421 = 4136033) B4136033
theorem B7352947 : Blo 2011435 7352947 := bstep (se 1 (by rfl) ⟨5514710, by rfl⟩ : syracuseStep 7352947 = 11029421) B11029421
theorem B9803929 : Blo 2011435 9803929 := bstep (se 2 (by rfl) ⟨3676473, by rfl⟩ : syracuseStep 9803929 = 7352947) B7352947
theorem B13071905 : Blo 2011435 13071905 := bstep (se 2 (by rfl) ⟨4901964, by rfl⟩ : syracuseStep 13071905 = 9803929) B9803929
theorem B8714603 : Blo 2011435 8714603 := bstep (se 1 (by rfl) ⟨6535952, by rfl⟩ : syracuseStep 8714603 = 13071905) B13071905
theorem B5809735 : Blo 2011435 5809735 := bstep (se 1 (by rfl) ⟨4357301, by rfl⟩ : syracuseStep 5809735 = 8714603) B8714603
theorem B7746313 : Blo 2011435 7746313 := bstep (se 2 (by rfl) ⟨2904867, by rfl⟩ : syracuseStep 7746313 = 5809735) B5809735
theorem B10328417 : Blo 2011435 10328417 := bstep (se 2 (by rfl) ⟨3873156, by rfl⟩ : syracuseStep 10328417 = 7746313) B7746313
theorem B6885611 : Blo 2011435 6885611 := bstep (se 1 (by rfl) ⟨5164208, by rfl⟩ : syracuseStep 6885611 = 10328417) B10328417
theorem B4590407 : Blo 2011435 4590407 := bstep (se 1 (by rfl) ⟨3442805, by rfl⟩ : syracuseStep 4590407 = 6885611) B6885611
theorem B3060271 : Blo 2011435 3060271 := bstep (se 1 (by rfl) ⟨2295203, by rfl⟩ : syracuseStep 3060271 = 4590407) B4590407
theorem B16321445 : Blo 2011435 16321445 := bstep (se 4 (by rfl) ⟨1530135, by rfl⟩ : syracuseStep 16321445 = 3060271) B3060271
theorem B10880963 : Blo 2011435 10880963 := bstep (se 1 (by rfl) ⟨8160722, by rfl⟩ : syracuseStep 10880963 = 16321445) B16321445
theorem B7253975 : Blo 2011435 7253975 := bstep (se 1 (by rfl) ⟨5440481, by rfl⟩ : syracuseStep 7253975 = 10880963) B10880963
theorem B19343933 : Blo 2011435 19343933 := bstep (se 3 (by rfl) ⟨3626987, by rfl⟩ : syracuseStep 19343933 = 7253975) B7253975
theorem B12895955 : Blo 2011435 12895955 := bstep (se 1 (by rfl) ⟨9671966, by rfl⟩ : syracuseStep 12895955 = 19343933) B19343933
theorem B8597303 : Blo 2011435 8597303 := bstep (se 1 (by rfl) ⟨6447977, by rfl⟩ : syracuseStep 8597303 = 12895955) B12895955
theorem B5731535 : Blo 2011435 5731535 := bstep (se 1 (by rfl) ⟨4298651, by rfl⟩ : syracuseStep 5731535 = 8597303) B8597303
theorem B3821023 : Blo 2011435 3821023 := bstep (se 1 (by rfl) ⟨2865767, by rfl⟩ : syracuseStep 3821023 = 5731535) B5731535
theorem B5094697 : Blo 2011435 5094697 := bstep (se 2 (by rfl) ⟨1910511, by rfl⟩ : syracuseStep 5094697 = 3821023) B3821023
theorem B6792929 : Blo 2011435 6792929 := bstep (se 2 (by rfl) ⟨2547348, by rfl⟩ : syracuseStep 6792929 = 5094697) B5094697
theorem B4528619 : Blo 2011435 4528619 := bstep (se 1 (by rfl) ⟨3396464, by rfl⟩ : syracuseStep 4528619 = 6792929) B6792929
theorem B3019079 : Blo 2011435 3019079 := bstep (se 1 (by rfl) ⟨2264309, by rfl⟩ : syracuseStep 3019079 = 4528619) B4528619
theorem B2012719 : Blo 2011435 2012719 := bstep (se 1 (by rfl) ⟨1509539, by rfl⟩ : syracuseStep 2012719 = 3019079) B3019079
theorem B3019085 : Blo 2011435 3019085 := bbase (se 3 (by rfl) ⟨566078, by rfl⟩ : syracuseStep 3019085 = 1132157) (by norm_num)
theorem B2012723 : Blo 2011435 2012723 := bstep (se 1 (by rfl) ⟨1509542, by rfl⟩ : syracuseStep 2012723 = 3019085) B3019085
theorem B4528637 : Blo 2011435 4528637 := bbase (se 3 (by rfl) ⟨849119, by rfl⟩ : syracuseStep 4528637 = 1698239) (by norm_num)
theorem B3019091 : Blo 2011435 3019091 := bstep (se 1 (by rfl) ⟨2264318, by rfl⟩ : syracuseStep 3019091 = 4528637) B4528637
theorem B2012727 : Blo 2011435 2012727 := bstep (se 1 (by rfl) ⟨1509545, by rfl⟩ : syracuseStep 2012727 = 3019091) B3019091
theorem B3396485 : Blo 2011435 3396485 := bbase (se 4 (by rfl) ⟨318420, by rfl⟩ : syracuseStep 3396485 = 636841) (by norm_num)
theorem B2264323 : Blo 2011435 2264323 := bstep (se 1 (by rfl) ⟨1698242, by rfl⟩ : syracuseStep 2264323 = 3396485) B3396485
theorem B3019097 : Blo 2011435 3019097 := bstep (se 2 (by rfl) ⟨1132161, by rfl⟩ : syracuseStep 3019097 = 2264323) B2264323
theorem B2012731 : Blo 2011435 2012731 := bstep (se 1 (by rfl) ⟨1509548, by rfl⟩ : syracuseStep 2012731 = 3019097) B3019097
theorem B15284213 : Blo 2011435 15284213 := bbase (se 5 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 15284213 = 1432895) (by norm_num)
theorem B10189475 : Blo 2011435 10189475 := bstep (se 1 (by rfl) ⟨7642106, by rfl⟩ : syracuseStep 10189475 = 15284213) B15284213
theorem B6792983 : Blo 2011435 6792983 := bstep (se 1 (by rfl) ⟨5094737, by rfl⟩ : syracuseStep 6792983 = 10189475) B10189475
theorem B4528655 : Blo 2011435 4528655 := bstep (se 1 (by rfl) ⟨3396491, by rfl⟩ : syracuseStep 4528655 = 6792983) B6792983
theorem B3019103 : Blo 2011435 3019103 := bstep (se 1 (by rfl) ⟨2264327, by rfl⟩ : syracuseStep 3019103 = 4528655) B4528655
theorem B2012735 : Blo 2011435 2012735 := bstep (se 1 (by rfl) ⟨1509551, by rfl⟩ : syracuseStep 2012735 = 3019103) B3019103
theorem B3019109 : Blo 2011435 3019109 := bbase (se 4 (by rfl) ⟨283041, by rfl⟩ : syracuseStep 3019109 = 566083) (by norm_num)
theorem B2012739 : Blo 2011435 2012739 := bstep (se 1 (by rfl) ⟨1509554, by rfl⟩ : syracuseStep 2012739 = 3019109) B3019109
theorem B3821069 : Blo 2011435 3821069 := bbase (se 3 (by rfl) ⟨716450, by rfl⟩ : syracuseStep 3821069 = 1432901) (by norm_num)
theorem B2547379 : Blo 2011435 2547379 := bstep (se 1 (by rfl) ⟨1910534, by rfl⟩ : syracuseStep 2547379 = 3821069) B3821069
theorem B3396505 : Blo 2011435 3396505 := bstep (se 2 (by rfl) ⟨1273689, by rfl⟩ : syracuseStep 3396505 = 2547379) B2547379
theorem B4528673 : Blo 2011435 4528673 := bstep (se 2 (by rfl) ⟨1698252, by rfl⟩ : syracuseStep 4528673 = 3396505) B3396505
theorem B3019115 : Blo 2011435 3019115 := bstep (se 1 (by rfl) ⟨2264336, by rfl⟩ : syracuseStep 3019115 = 4528673) B4528673
theorem B2012743 : Blo 2011435 2012743 := bstep (se 1 (by rfl) ⟨1509557, by rfl⟩ : syracuseStep 2012743 = 3019115) B3019115
theorem B2264341 : Blo 2011435 2264341 := bbase (se 6 (by rfl) ⟨53070, by rfl⟩ : syracuseStep 2264341 = 106141) (by norm_num)
theorem B3019121 : Blo 2011435 3019121 := bstep (se 2 (by rfl) ⟨1132170, by rfl⟩ : syracuseStep 3019121 = 2264341) B2264341
theorem B2012747 : Blo 2011435 2012747 := bstep (se 1 (by rfl) ⟨1509560, by rfl⟩ : syracuseStep 2012747 = 3019121) B3019121
theorem B2547389 : Blo 2011435 2547389 := bbase (se 3 (by rfl) ⟨477635, by rfl⟩ : syracuseStep 2547389 = 955271) (by norm_num)
theorem B6793037 : Blo 2011435 6793037 := bstep (se 3 (by rfl) ⟨1273694, by rfl⟩ : syracuseStep 6793037 = 2547389) B2547389
theorem B4528691 : Blo 2011435 4528691 := bstep (se 1 (by rfl) ⟨3396518, by rfl⟩ : syracuseStep 4528691 = 6793037) B6793037
theorem B3019127 : Blo 2011435 3019127 := bstep (se 1 (by rfl) ⟨2264345, by rfl⟩ : syracuseStep 3019127 = 4528691) B4528691
theorem B2012751 : Blo 2011435 2012751 := bstep (se 1 (by rfl) ⟨1509563, by rfl⟩ : syracuseStep 2012751 = 3019127) B3019127
theorem B3019133 : Blo 2011435 3019133 := bbase (se 3 (by rfl) ⟨566087, by rfl⟩ : syracuseStep 3019133 = 1132175) (by norm_num)
theorem B2012755 : Blo 2011435 2012755 := bstep (se 1 (by rfl) ⟨1509566, by rfl⟩ : syracuseStep 2012755 = 3019133) B3019133
theorem B4528709 : Blo 2011435 4528709 := bbase (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) (by norm_num)
theorem B3019139 : Blo 2011435 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B2012759 : Blo 2011435 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B2149373 : Blo 2011435 2149373 := bbase (se 3 (by rfl) ⟨403007, by rfl⟩ : syracuseStep 2149373 = 806015) (by norm_num)
theorem B5731661 : Blo 2011435 5731661 := bstep (se 3 (by rfl) ⟨1074686, by rfl⟩ : syracuseStep 5731661 = 2149373) B2149373
theorem B3821107 : Blo 2011435 3821107 := bstep (se 1 (by rfl) ⟨2865830, by rfl⟩ : syracuseStep 3821107 = 5731661) B5731661
theorem B5094809 : Blo 2011435 5094809 := bstep (se 2 (by rfl) ⟨1910553, by rfl⟩ : syracuseStep 5094809 = 3821107) B3821107
theorem B3396539 : Blo 2011435 3396539 := bstep (se 1 (by rfl) ⟨2547404, by rfl⟩ : syracuseStep 3396539 = 5094809) B5094809
theorem B2264359 : Blo 2011435 2264359 := bstep (se 1 (by rfl) ⟨1698269, by rfl⟩ : syracuseStep 2264359 = 3396539) B3396539
theorem B3019145 : Blo 2011435 3019145 := bstep (se 2 (by rfl) ⟨1132179, by rfl⟩ : syracuseStep 3019145 = 2264359) B2264359
theorem B2012763 : Blo 2011435 2012763 := bstep (se 1 (by rfl) ⟨1509572, by rfl⟩ : syracuseStep 2012763 = 3019145) B3019145
theorem B10189637 : Blo 2011435 10189637 := bbase (se 4 (by rfl) ⟨955278, by rfl⟩ : syracuseStep 10189637 = 1910557) (by norm_num)
theorem B6793091 : Blo 2011435 6793091 := bstep (se 1 (by rfl) ⟨5094818, by rfl⟩ : syracuseStep 6793091 = 10189637) B10189637
theorem B4528727 : Blo 2011435 4528727 := bstep (se 1 (by rfl) ⟨3396545, by rfl⟩ : syracuseStep 4528727 = 6793091) B6793091
theorem B3019151 : Blo 2011435 3019151 := bstep (se 1 (by rfl) ⟨2264363, by rfl⟩ : syracuseStep 3019151 = 4528727) B4528727
theorem B2012767 : Blo 2011435 2012767 := bstep (se 1 (by rfl) ⟨1509575, by rfl⟩ : syracuseStep 2012767 = 3019151) B3019151
theorem B3019157 : Blo 2011435 3019157 := bbase (se 6 (by rfl) ⟨70761, by rfl⟩ : syracuseStep 3019157 = 141523) (by norm_num)
theorem B2012771 : Blo 2011435 2012771 := bstep (se 1 (by rfl) ⟨1509578, by rfl⟩ : syracuseStep 2012771 = 3019157) B3019157
theorem B2720317 : Blo 2011435 2720317 := bbase (se 3 (by rfl) ⟨510059, by rfl⟩ : syracuseStep 2720317 = 1020119) (by norm_num)
theorem B3627089 : Blo 2011435 3627089 := bstep (se 2 (by rfl) ⟨1360158, by rfl⟩ : syracuseStep 3627089 = 2720317) B2720317
theorem B2418059 : Blo 2011435 2418059 := bstep (se 1 (by rfl) ⟨1813544, by rfl⟩ : syracuseStep 2418059 = 3627089) B3627089
theorem B6448157 : Blo 2011435 6448157 := bstep (se 3 (by rfl) ⟨1209029, by rfl⟩ : syracuseStep 6448157 = 2418059) B2418059
theorem B4298771 : Blo 2011435 4298771 := bstep (se 1 (by rfl) ⟨3224078, by rfl⟩ : syracuseStep 4298771 = 6448157) B6448157
theorem B11463389 : Blo 2011435 11463389 := bstep (se 3 (by rfl) ⟨2149385, by rfl⟩ : syracuseStep 11463389 = 4298771) B4298771
theorem B7642259 : Blo 2011435 7642259 := bstep (se 1 (by rfl) ⟨5731694, by rfl⟩ : syracuseStep 7642259 = 11463389) B11463389
theorem B5094839 : Blo 2011435 5094839 := bstep (se 1 (by rfl) ⟨3821129, by rfl⟩ : syracuseStep 5094839 = 7642259) B7642259
theorem B3396559 : Blo 2011435 3396559 := bstep (se 1 (by rfl) ⟨2547419, by rfl⟩ : syracuseStep 3396559 = 5094839) B5094839
theorem B4528745 : Blo 2011435 4528745 := bstep (se 2 (by rfl) ⟨1698279, by rfl⟩ : syracuseStep 4528745 = 3396559) B3396559
theorem B3019163 : Blo 2011435 3019163 := bstep (se 1 (by rfl) ⟨2264372, by rfl⟩ : syracuseStep 3019163 = 4528745) B4528745
theorem B2012775 : Blo 2011435 2012775 := bstep (se 1 (by rfl) ⟨1509581, by rfl⟩ : syracuseStep 2012775 = 3019163) B3019163
theorem B2264377 : Blo 2011435 2264377 := bbase (se 2 (by rfl) ⟨849141, by rfl⟩ : syracuseStep 2264377 = 1698283) (by norm_num)
theorem B3019169 : Blo 2011435 3019169 := bstep (se 2 (by rfl) ⟨1132188, by rfl⟩ : syracuseStep 3019169 = 2264377) B2264377
theorem B2012779 : Blo 2011435 2012779 := bstep (se 1 (by rfl) ⟨1509584, by rfl⟩ : syracuseStep 2012779 = 3019169) B3019169
theorem B5731717 : Blo 2011435 5731717 := bbase (se 4 (by rfl) ⟨537348, by rfl⟩ : syracuseStep 5731717 = 1074697) (by norm_num)
theorem B7642289 : Blo 2011435 7642289 := bstep (se 2 (by rfl) ⟨2865858, by rfl⟩ : syracuseStep 7642289 = 5731717) B5731717
theorem B5094859 : Blo 2011435 5094859 := bstep (se 1 (by rfl) ⟨3821144, by rfl⟩ : syracuseStep 5094859 = 7642289) B7642289
theorem B6793145 : Blo 2011435 6793145 := bstep (se 2 (by rfl) ⟨2547429, by rfl⟩ : syracuseStep 6793145 = 5094859) B5094859
theorem B4528763 : Blo 2011435 4528763 := bstep (se 1 (by rfl) ⟨3396572, by rfl⟩ : syracuseStep 4528763 = 6793145) B6793145
theorem B3019175 : Blo 2011435 3019175 := bstep (se 1 (by rfl) ⟨2264381, by rfl⟩ : syracuseStep 3019175 = 4528763) B4528763
theorem B2012783 : Blo 2011435 2012783 := bstep (se 1 (by rfl) ⟨1509587, by rfl⟩ : syracuseStep 2012783 = 3019175) B3019175
theorem B3019181 : Blo 2011435 3019181 := bbase (se 3 (by rfl) ⟨566096, by rfl⟩ : syracuseStep 3019181 = 1132193) (by norm_num)
theorem B2012787 : Blo 2011435 2012787 := bstep (se 1 (by rfl) ⟨1509590, by rfl⟩ : syracuseStep 2012787 = 3019181) B3019181
theorem B4528781 : Blo 2011435 4528781 := bbase (se 3 (by rfl) ⟨849146, by rfl⟩ : syracuseStep 4528781 = 1698293) (by norm_num)
theorem B3019187 : Blo 2011435 3019187 := bstep (se 1 (by rfl) ⟨2264390, by rfl⟩ : syracuseStep 3019187 = 4528781) B4528781
theorem B2012791 : Blo 2011435 2012791 := bstep (se 1 (by rfl) ⟨1509593, by rfl⟩ : syracuseStep 2012791 = 3019187) B3019187
theorem B2547445 : Blo 2011435 2547445 := bbase (se 5 (by rfl) ⟨119411, by rfl⟩ : syracuseStep 2547445 = 238823) (by norm_num)
theorem B3396593 : Blo 2011435 3396593 := bstep (se 2 (by rfl) ⟨1273722, by rfl⟩ : syracuseStep 3396593 = 2547445) B2547445
theorem B2264395 : Blo 2011435 2264395 := bstep (se 1 (by rfl) ⟨1698296, by rfl⟩ : syracuseStep 2264395 = 3396593) B3396593
theorem B3019193 : Blo 2011435 3019193 := bstep (se 2 (by rfl) ⟨1132197, by rfl⟩ : syracuseStep 3019193 = 2264395) B2264395
theorem B2012795 : Blo 2011435 2012795 := bstep (se 1 (by rfl) ⟨1509596, by rfl⟩ : syracuseStep 2012795 = 3019193) B3019193
theorem B4590589 : Blo 2011435 4590589 := bbase (se 3 (by rfl) ⟨860735, by rfl⟩ : syracuseStep 4590589 = 1721471) (by norm_num)
theorem B6120785 : Blo 2011435 6120785 := bstep (se 2 (by rfl) ⟨2295294, by rfl⟩ : syracuseStep 6120785 = 4590589) B4590589
theorem B4080523 : Blo 2011435 4080523 := bstep (se 1 (by rfl) ⟨3060392, by rfl⟩ : syracuseStep 4080523 = 6120785) B6120785
theorem B5440697 : Blo 2011435 5440697 := bstep (se 2 (by rfl) ⟨2040261, by rfl⟩ : syracuseStep 5440697 = 4080523) B4080523
theorem B3627131 : Blo 2011435 3627131 := bstep (se 1 (by rfl) ⟨2720348, by rfl⟩ : syracuseStep 3627131 = 5440697) B5440697
theorem B38689397 : Blo 2011435 38689397 := bstep (se 5 (by rfl) ⟨1813565, by rfl⟩ : syracuseStep 38689397 = 3627131) B3627131
theorem B25792931 : Blo 2011435 25792931 := bstep (se 1 (by rfl) ⟨19344698, by rfl⟩ : syracuseStep 25792931 = 38689397) B38689397
theorem B17195287 : Blo 2011435 17195287 := bstep (se 1 (by rfl) ⟨12896465, by rfl⟩ : syracuseStep 17195287 = 25792931) B25792931
theorem B22927049 : Blo 2011435 22927049 := bstep (se 2 (by rfl) ⟨8597643, by rfl⟩ : syracuseStep 22927049 = 17195287) B17195287
theorem B15284699 : Blo 2011435 15284699 := bstep (se 1 (by rfl) ⟨11463524, by rfl⟩ : syracuseStep 15284699 = 22927049) B22927049
theorem B10189799 : Blo 2011435 10189799 := bstep (se 1 (by rfl) ⟨7642349, by rfl⟩ : syracuseStep 10189799 = 15284699) B15284699
theorem B6793199 : Blo 2011435 6793199 := bstep (se 1 (by rfl) ⟨5094899, by rfl⟩ : syracuseStep 6793199 = 10189799) B10189799
theorem B4528799 : Blo 2011435 4528799 := bstep (se 1 (by rfl) ⟨3396599, by rfl⟩ : syracuseStep 4528799 = 6793199) B6793199
theorem B3019199 : Blo 2011435 3019199 := bstep (se 1 (by rfl) ⟨2264399, by rfl⟩ : syracuseStep 3019199 = 4528799) B4528799
theorem B2012799 : Blo 2011435 2012799 := bstep (se 1 (by rfl) ⟨1509599, by rfl⟩ : syracuseStep 2012799 = 3019199) B3019199
theorem B3019205 : Blo 2011435 3019205 := bbase (se 4 (by rfl) ⟨283050, by rfl⟩ : syracuseStep 3019205 = 566101) (by norm_num)
theorem B2012803 : Blo 2011435 2012803 := bstep (se 1 (by rfl) ⟨1509602, by rfl⟩ : syracuseStep 2012803 = 3019205) B3019205
theorem B3396613 : Blo 2011435 3396613 := bbase (se 4 (by rfl) ⟨318432, by rfl⟩ : syracuseStep 3396613 = 636865) (by norm_num)
theorem B4528817 : Blo 2011435 4528817 := bstep (se 2 (by rfl) ⟨1698306, by rfl⟩ : syracuseStep 4528817 = 3396613) B3396613
theorem B3019211 : Blo 2011435 3019211 := bstep (se 1 (by rfl) ⟨2264408, by rfl⟩ : syracuseStep 3019211 = 4528817) B4528817
theorem B2012807 : Blo 2011435 2012807 := bstep (se 1 (by rfl) ⟨1509605, by rfl⟩ : syracuseStep 2012807 = 3019211) B3019211
theorem B2264413 : Blo 2011435 2264413 := bbase (se 3 (by rfl) ⟨424577, by rfl⟩ : syracuseStep 2264413 = 849155) (by norm_num)
theorem B3019217 : Blo 2011435 3019217 := bstep (se 2 (by rfl) ⟨1132206, by rfl⟩ : syracuseStep 3019217 = 2264413) B2264413
theorem B2012811 : Blo 2011435 2012811 := bstep (se 1 (by rfl) ⟨1509608, by rfl⟩ : syracuseStep 2012811 = 3019217) B3019217
theorem B6793253 : Blo 2011435 6793253 := bbase (se 4 (by rfl) ⟨636867, by rfl⟩ : syracuseStep 6793253 = 1273735) (by norm_num)
theorem B4528835 : Blo 2011435 4528835 := bstep (se 1 (by rfl) ⟨3396626, by rfl⟩ : syracuseStep 4528835 = 6793253) B6793253
theorem B3019223 : Blo 2011435 3019223 := bstep (se 1 (by rfl) ⟨2264417, by rfl⟩ : syracuseStep 3019223 = 4528835) B4528835
theorem B2012815 : Blo 2011435 2012815 := bstep (se 1 (by rfl) ⟨1509611, by rfl⟩ : syracuseStep 2012815 = 3019223) B3019223
theorem B3019229 : Blo 2011435 3019229 := bbase (se 3 (by rfl) ⟨566105, by rfl⟩ : syracuseStep 3019229 = 1132211) (by norm_num)
theorem B2012819 : Blo 2011435 2012819 := bstep (se 1 (by rfl) ⟨1509614, by rfl⟩ : syracuseStep 2012819 = 3019229) B3019229
theorem B4528853 : Blo 2011435 4528853 := bbase (se 7 (by rfl) ⟨53072, by rfl⟩ : syracuseStep 4528853 = 106145) (by norm_num)
theorem B3019235 : Blo 2011435 3019235 := bstep (se 1 (by rfl) ⟨2264426, by rfl⟩ : syracuseStep 3019235 = 4528853) B4528853
theorem B2012823 : Blo 2011435 2012823 := bstep (se 1 (by rfl) ⟨1509617, by rfl⟩ : syracuseStep 2012823 = 3019235) B3019235
theorem B8597765 : Blo 2011435 8597765 := bbase (se 4 (by rfl) ⟨806040, by rfl⟩ : syracuseStep 8597765 = 1612081) (by norm_num)
theorem B5731843 : Blo 2011435 5731843 := bstep (se 1 (by rfl) ⟨4298882, by rfl⟩ : syracuseStep 5731843 = 8597765) B8597765
theorem B7642457 : Blo 2011435 7642457 := bstep (se 2 (by rfl) ⟨2865921, by rfl⟩ : syracuseStep 7642457 = 5731843) B5731843
theorem B5094971 : Blo 2011435 5094971 := bstep (se 1 (by rfl) ⟨3821228, by rfl⟩ : syracuseStep 5094971 = 7642457) B7642457
theorem B3396647 : Blo 2011435 3396647 := bstep (se 1 (by rfl) ⟨2547485, by rfl⟩ : syracuseStep 3396647 = 5094971) B5094971
theorem B2264431 : Blo 2011435 2264431 := bstep (se 1 (by rfl) ⟨1698323, by rfl⟩ : syracuseStep 2264431 = 3396647) B3396647
theorem B3019241 : Blo 2011435 3019241 := bstep (se 2 (by rfl) ⟨1132215, by rfl⟩ : syracuseStep 3019241 = 2264431) B2264431
theorem B2012827 : Blo 2011435 2012827 := bstep (se 1 (by rfl) ⟨1509620, by rfl⟩ : syracuseStep 2012827 = 3019241) B3019241
theorem B39217877 : Blo 2011435 39217877 := bbase (se 7 (by rfl) ⟨459584, by rfl⟩ : syracuseStep 39217877 = 919169) (by norm_num)
theorem B26145251 : Blo 2011435 26145251 := bstep (se 1 (by rfl) ⟨19608938, by rfl⟩ : syracuseStep 26145251 = 39217877) B39217877
theorem B17430167 : Blo 2011435 17430167 := bstep (se 1 (by rfl) ⟨13072625, by rfl⟩ : syracuseStep 17430167 = 26145251) B26145251
theorem B46480445 : Blo 2011435 46480445 := bstep (se 3 (by rfl) ⟨8715083, by rfl⟩ : syracuseStep 46480445 = 17430167) B17430167
theorem B30986963 : Blo 2011435 30986963 := bstep (se 1 (by rfl) ⟨23240222, by rfl⟩ : syracuseStep 30986963 = 46480445) B46480445
theorem B20657975 : Blo 2011435 20657975 := bstep (se 1 (by rfl) ⟨15493481, by rfl⟩ : syracuseStep 20657975 = 30986963) B30986963
theorem B55087933 : Blo 2011435 55087933 := bstep (se 3 (by rfl) ⟨10328987, by rfl⟩ : syracuseStep 55087933 = 20657975) B20657975
theorem B73450577 : Blo 2011435 73450577 := bstep (se 2 (by rfl) ⟨27543966, by rfl⟩ : syracuseStep 73450577 = 55087933) B55087933
theorem B48967051 : Blo 2011435 48967051 := bstep (se 1 (by rfl) ⟨36725288, by rfl⟩ : syracuseStep 48967051 = 73450577) B73450577
theorem B65289401 : Blo 2011435 65289401 := bstep (se 2 (by rfl) ⟨24483525, by rfl⟩ : syracuseStep 65289401 = 48967051) B48967051
theorem B43526267 : Blo 2011435 43526267 := bstep (se 1 (by rfl) ⟨32644700, by rfl⟩ : syracuseStep 43526267 = 65289401) B65289401
theorem B29017511 : Blo 2011435 29017511 := bstep (se 1 (by rfl) ⟨21763133, by rfl⟩ : syracuseStep 29017511 = 43526267) B43526267
theorem B19345007 : Blo 2011435 19345007 := bstep (se 1 (by rfl) ⟨14508755, by rfl⟩ : syracuseStep 19345007 = 29017511) B29017511
theorem B12896671 : Blo 2011435 12896671 := bstep (se 1 (by rfl) ⟨9672503, by rfl⟩ : syracuseStep 12896671 = 19345007) B19345007
theorem B17195561 : Blo 2011435 17195561 := bstep (se 2 (by rfl) ⟨6448335, by rfl⟩ : syracuseStep 17195561 = 12896671) B12896671
theorem B11463707 : Blo 2011435 11463707 := bstep (se 1 (by rfl) ⟨8597780, by rfl⟩ : syracuseStep 11463707 = 17195561) B17195561
theorem B7642471 : Blo 2011435 7642471 := bstep (se 1 (by rfl) ⟨5731853, by rfl⟩ : syracuseStep 7642471 = 11463707) B11463707
theorem B10189961 : Blo 2011435 10189961 := bstep (se 2 (by rfl) ⟨3821235, by rfl⟩ : syracuseStep 10189961 = 7642471) B7642471
theorem B6793307 : Blo 2011435 6793307 := bstep (se 1 (by rfl) ⟨5094980, by rfl⟩ : syracuseStep 6793307 = 10189961) B10189961
theorem B4528871 : Blo 2011435 4528871 := bstep (se 1 (by rfl) ⟨3396653, by rfl⟩ : syracuseStep 4528871 = 6793307) B6793307
theorem B3019247 : Blo 2011435 3019247 := bstep (se 1 (by rfl) ⟨2264435, by rfl⟩ : syracuseStep 3019247 = 4528871) B4528871
theorem B2012831 : Blo 2011435 2012831 := bstep (se 1 (by rfl) ⟨1509623, by rfl⟩ : syracuseStep 2012831 = 3019247) B3019247
theorem B3019253 : Blo 2011435 3019253 := bbase (se 5 (by rfl) ⟨141527, by rfl⟩ : syracuseStep 3019253 = 283055) (by norm_num)
theorem B2012835 : Blo 2011435 2012835 := bstep (se 1 (by rfl) ⟨1509626, by rfl⟩ : syracuseStep 2012835 = 3019253) B3019253
theorem B5731877 : Blo 2011435 5731877 := bbase (se 4 (by rfl) ⟨537363, by rfl⟩ : syracuseStep 5731877 = 1074727) (by norm_num)
theorem B3821251 : Blo 2011435 3821251 := bstep (se 1 (by rfl) ⟨2865938, by rfl⟩ : syracuseStep 3821251 = 5731877) B5731877
theorem B5095001 : Blo 2011435 5095001 := bstep (se 2 (by rfl) ⟨1910625, by rfl⟩ : syracuseStep 5095001 = 3821251) B3821251
theorem B3396667 : Blo 2011435 3396667 := bstep (se 1 (by rfl) ⟨2547500, by rfl⟩ : syracuseStep 3396667 = 5095001) B5095001
theorem B4528889 : Blo 2011435 4528889 := bstep (se 2 (by rfl) ⟨1698333, by rfl⟩ : syracuseStep 4528889 = 3396667) B3396667
theorem B3019259 : Blo 2011435 3019259 := bstep (se 1 (by rfl) ⟨2264444, by rfl⟩ : syracuseStep 3019259 = 4528889) B4528889
theorem B2012839 : Blo 2011435 2012839 := bstep (se 1 (by rfl) ⟨1509629, by rfl⟩ : syracuseStep 2012839 = 3019259) B3019259
theorem B2264449 : Blo 2011435 2264449 := bbase (se 2 (by rfl) ⟨849168, by rfl⟩ : syracuseStep 2264449 = 1698337) (by norm_num)
theorem B3019265 : Blo 2011435 3019265 := bstep (se 2 (by rfl) ⟨1132224, by rfl⟩ : syracuseStep 3019265 = 2264449) B2264449
theorem B2012843 : Blo 2011435 2012843 := bstep (se 1 (by rfl) ⟨1509632, by rfl⟩ : syracuseStep 2012843 = 3019265) B3019265
theorem B5095021 : Blo 2011435 5095021 := bbase (se 3 (by rfl) ⟨955316, by rfl⟩ : syracuseStep 5095021 = 1910633) (by norm_num)
theorem B6793361 : Blo 2011435 6793361 := bstep (se 2 (by rfl) ⟨2547510, by rfl⟩ : syracuseStep 6793361 = 5095021) B5095021
theorem B4528907 : Blo 2011435 4528907 := bstep (se 1 (by rfl) ⟨3396680, by rfl⟩ : syracuseStep 4528907 = 6793361) B6793361
theorem B3019271 : Blo 2011435 3019271 := bstep (se 1 (by rfl) ⟨2264453, by rfl⟩ : syracuseStep 3019271 = 4528907) B4528907
theorem B2012847 : Blo 2011435 2012847 := bstep (se 1 (by rfl) ⟨1509635, by rfl⟩ : syracuseStep 2012847 = 3019271) B3019271
theorem B3019277 : Blo 2011435 3019277 := bbase (se 3 (by rfl) ⟨566114, by rfl⟩ : syracuseStep 3019277 = 1132229) (by norm_num)
theorem B2012851 : Blo 2011435 2012851 := bstep (se 1 (by rfl) ⟨1509638, by rfl⟩ : syracuseStep 2012851 = 3019277) B3019277
theorem B4528925 : Blo 2011435 4528925 := bbase (se 3 (by rfl) ⟨849173, by rfl⟩ : syracuseStep 4528925 = 1698347) (by norm_num)
theorem B3019283 : Blo 2011435 3019283 := bstep (se 1 (by rfl) ⟨2264462, by rfl⟩ : syracuseStep 3019283 = 4528925) B4528925
theorem B2012855 : Blo 2011435 2012855 := bstep (se 1 (by rfl) ⟨1509641, by rfl⟩ : syracuseStep 2012855 = 3019283) B3019283
theorem B3396701 : Blo 2011435 3396701 := bbase (se 3 (by rfl) ⟨636881, by rfl⟩ : syracuseStep 3396701 = 1273763) (by norm_num)
theorem B2264467 : Blo 2011435 2264467 := bstep (se 1 (by rfl) ⟨1698350, by rfl⟩ : syracuseStep 2264467 = 3396701) B3396701
theorem B3019289 : Blo 2011435 3019289 := bstep (se 2 (by rfl) ⟨1132233, by rfl⟩ : syracuseStep 3019289 = 2264467) B2264467
theorem B2012859 : Blo 2011435 2012859 := bstep (se 1 (by rfl) ⟨1509644, by rfl⟩ : syracuseStep 2012859 = 3019289) B3019289
theorem B9804629 : Blo 2011435 9804629 := bbase (se 9 (by rfl) ⟨28724, by rfl⟩ : syracuseStep 9804629 = 57449) (by norm_num)
theorem B6536419 : Blo 2011435 6536419 := bstep (se 1 (by rfl) ⟨4902314, by rfl⟩ : syracuseStep 6536419 = 9804629) B9804629
theorem B34860901 : Blo 2011435 34860901 := bstep (se 4 (by rfl) ⟨3268209, by rfl⟩ : syracuseStep 34860901 = 6536419) B6536419
theorem B46481201 : Blo 2011435 46481201 := bstep (se 2 (by rfl) ⟨17430450, by rfl⟩ : syracuseStep 46481201 = 34860901) B34860901
theorem B30987467 : Blo 2011435 30987467 := bstep (se 1 (by rfl) ⟨23240600, by rfl⟩ : syracuseStep 30987467 = 46481201) B46481201
theorem B20658311 : Blo 2011435 20658311 := bstep (se 1 (by rfl) ⟨15493733, by rfl⟩ : syracuseStep 20658311 = 30987467) B30987467
theorem B13772207 : Blo 2011435 13772207 := bstep (se 1 (by rfl) ⟨10329155, by rfl⟩ : syracuseStep 13772207 = 20658311) B20658311
theorem B9181471 : Blo 2011435 9181471 := bstep (se 1 (by rfl) ⟨6886103, by rfl⟩ : syracuseStep 9181471 = 13772207) B13772207
theorem B12241961 : Blo 2011435 12241961 := bstep (se 2 (by rfl) ⟨4590735, by rfl⟩ : syracuseStep 12241961 = 9181471) B9181471
theorem B8161307 : Blo 2011435 8161307 := bstep (se 1 (by rfl) ⟨6120980, by rfl⟩ : syracuseStep 8161307 = 12241961) B12241961
theorem B5440871 : Blo 2011435 5440871 := bstep (se 1 (by rfl) ⟨4080653, by rfl⟩ : syracuseStep 5440871 = 8161307) B8161307
theorem B3627247 : Blo 2011435 3627247 := bstep (se 1 (by rfl) ⟨2720435, by rfl⟩ : syracuseStep 3627247 = 5440871) B5440871
theorem B4836329 : Blo 2011435 4836329 := bstep (se 2 (by rfl) ⟨1813623, by rfl⟩ : syracuseStep 4836329 = 3627247) B3627247
theorem B3224219 : Blo 2011435 3224219 := bstep (se 1 (by rfl) ⟨2418164, by rfl⟩ : syracuseStep 3224219 = 4836329) B4836329
theorem B8597917 : Blo 2011435 8597917 := bstep (se 3 (by rfl) ⟨1612109, by rfl⟩ : syracuseStep 8597917 = 3224219) B3224219
theorem B11463889 : Blo 2011435 11463889 := bstep (se 2 (by rfl) ⟨4298958, by rfl⟩ : syracuseStep 11463889 = 8597917) B8597917
theorem B15285185 : Blo 2011435 15285185 := bstep (se 2 (by rfl) ⟨5731944, by rfl⟩ : syracuseStep 15285185 = 11463889) B11463889
theorem B10190123 : Blo 2011435 10190123 := bstep (se 1 (by rfl) ⟨7642592, by rfl⟩ : syracuseStep 10190123 = 15285185) B15285185
theorem B6793415 : Blo 2011435 6793415 := bstep (se 1 (by rfl) ⟨5095061, by rfl⟩ : syracuseStep 6793415 = 10190123) B10190123
theorem B4528943 : Blo 2011435 4528943 := bstep (se 1 (by rfl) ⟨3396707, by rfl⟩ : syracuseStep 4528943 = 6793415) B6793415
theorem B3019295 : Blo 2011435 3019295 := bstep (se 1 (by rfl) ⟨2264471, by rfl⟩ : syracuseStep 3019295 = 4528943) B4528943
theorem B2012863 : Blo 2011435 2012863 := bstep (se 1 (by rfl) ⟨1509647, by rfl⟩ : syracuseStep 2012863 = 3019295) B3019295
theorem B3019301 : Blo 2011435 3019301 := bbase (se 4 (by rfl) ⟨283059, by rfl⟩ : syracuseStep 3019301 = 566119) (by norm_num)
theorem B2012867 : Blo 2011435 2012867 := bstep (se 1 (by rfl) ⟨1509650, by rfl⟩ : syracuseStep 2012867 = 3019301) B3019301
theorem B2547541 : Blo 2011435 2547541 := bbase (se 9 (by rfl) ⟨7463, by rfl⟩ : syracuseStep 2547541 = 14927) (by norm_num)
theorem B3396721 : Blo 2011435 3396721 := bstep (se 2 (by rfl) ⟨1273770, by rfl⟩ : syracuseStep 3396721 = 2547541) B2547541
theorem B4528961 : Blo 2011435 4528961 := bstep (se 2 (by rfl) ⟨1698360, by rfl⟩ : syracuseStep 4528961 = 3396721) B3396721
theorem B3019307 : Blo 2011435 3019307 := bstep (se 1 (by rfl) ⟨2264480, by rfl⟩ : syracuseStep 3019307 = 4528961) B4528961
theorem B2012871 : Blo 2011435 2012871 := bstep (se 1 (by rfl) ⟨1509653, by rfl⟩ : syracuseStep 2012871 = 3019307) B3019307
theorem B2264485 : Blo 2011435 2264485 := bbase (se 4 (by rfl) ⟨212295, by rfl⟩ : syracuseStep 2264485 = 424591) (by norm_num)
theorem B3019313 : Blo 2011435 3019313 := bstep (se 2 (by rfl) ⟨1132242, by rfl⟩ : syracuseStep 3019313 = 2264485) B2264485
theorem B2012875 : Blo 2011435 2012875 := bstep (se 1 (by rfl) ⟨1509656, by rfl⟩ : syracuseStep 2012875 = 3019313) B3019313
theorem B12896981 : Blo 2011435 12896981 := bbase (se 7 (by rfl) ⟨151136, by rfl⟩ : syracuseStep 12896981 = 302273) (by norm_num)
theorem B8597987 : Blo 2011435 8597987 := bstep (se 1 (by rfl) ⟨6448490, by rfl⟩ : syracuseStep 8597987 = 12896981) B12896981
theorem B5731991 : Blo 2011435 5731991 := bstep (se 1 (by rfl) ⟨4298993, by rfl⟩ : syracuseStep 5731991 = 8597987) B8597987
theorem B3821327 : Blo 2011435 3821327 := bstep (se 1 (by rfl) ⟨2865995, by rfl⟩ : syracuseStep 3821327 = 5731991) B5731991
theorem B2547551 : Blo 2011435 2547551 := bstep (se 1 (by rfl) ⟨1910663, by rfl⟩ : syracuseStep 2547551 = 3821327) B3821327
theorem B6793469 : Blo 2011435 6793469 := bstep (se 3 (by rfl) ⟨1273775, by rfl⟩ : syracuseStep 6793469 = 2547551) B2547551
theorem B4528979 : Blo 2011435 4528979 := bstep (se 1 (by rfl) ⟨3396734, by rfl⟩ : syracuseStep 4528979 = 6793469) B6793469
theorem B3019319 : Blo 2011435 3019319 := bstep (se 1 (by rfl) ⟨2264489, by rfl⟩ : syracuseStep 3019319 = 4528979) B4528979
theorem B2012879 : Blo 2011435 2012879 := bstep (se 1 (by rfl) ⟨1509659, by rfl⟩ : syracuseStep 2012879 = 3019319) B3019319
theorem B3019325 : Blo 2011435 3019325 := bbase (se 3 (by rfl) ⟨566123, by rfl⟩ : syracuseStep 3019325 = 1132247) (by norm_num)
theorem B2012883 : Blo 2011435 2012883 := bstep (se 1 (by rfl) ⟨1509662, by rfl⟩ : syracuseStep 2012883 = 3019325) B3019325
theorem B4528997 : Blo 2011435 4528997 := bbase (se 4 (by rfl) ⟨424593, by rfl⟩ : syracuseStep 4528997 = 849187) (by norm_num)
theorem B3019331 : Blo 2011435 3019331 := bstep (se 1 (by rfl) ⟨2264498, by rfl⟩ : syracuseStep 3019331 = 4528997) B4528997
theorem B2012887 : Blo 2011435 2012887 := bstep (se 1 (by rfl) ⟨1509665, by rfl⟩ : syracuseStep 2012887 = 3019331) B3019331
theorem B5095133 : Blo 2011435 5095133 := bbase (se 3 (by rfl) ⟨955337, by rfl⟩ : syracuseStep 5095133 = 1910675) (by norm_num)
theorem B3396755 : Blo 2011435 3396755 := bstep (se 1 (by rfl) ⟨2547566, by rfl⟩ : syracuseStep 3396755 = 5095133) B5095133
theorem B2264503 : Blo 2011435 2264503 := bstep (se 1 (by rfl) ⟨1698377, by rfl⟩ : syracuseStep 2264503 = 3396755) B3396755
theorem B3019337 : Blo 2011435 3019337 := bstep (se 2 (by rfl) ⟨1132251, by rfl⟩ : syracuseStep 3019337 = 2264503) B2264503
theorem B2012891 : Blo 2011435 2012891 := bstep (se 1 (by rfl) ⟨1509668, by rfl⟩ : syracuseStep 2012891 = 3019337) B3019337
theorem B3821357 : Blo 2011435 3821357 := bbase (se 3 (by rfl) ⟨716504, by rfl⟩ : syracuseStep 3821357 = 1433009) (by norm_num)
theorem B10190285 : Blo 2011435 10190285 := bstep (se 3 (by rfl) ⟨1910678, by rfl⟩ : syracuseStep 10190285 = 3821357) B3821357
theorem B6793523 : Blo 2011435 6793523 := bstep (se 1 (by rfl) ⟨5095142, by rfl⟩ : syracuseStep 6793523 = 10190285) B10190285
theorem B4529015 : Blo 2011435 4529015 := bstep (se 1 (by rfl) ⟨3396761, by rfl⟩ : syracuseStep 4529015 = 6793523) B6793523
theorem B3019343 : Blo 2011435 3019343 := bstep (se 1 (by rfl) ⟨2264507, by rfl⟩ : syracuseStep 3019343 = 4529015) B4529015
theorem B2012895 : Blo 2011435 2012895 := bstep (se 1 (by rfl) ⟨1509671, by rfl⟩ : syracuseStep 2012895 = 3019343) B3019343
theorem B3019349 : Blo 2011435 3019349 := bbase (se 8 (by rfl) ⟨17691, by rfl⟩ : syracuseStep 3019349 = 35383) (by norm_num)
theorem B2012899 : Blo 2011435 2012899 := bstep (se 1 (by rfl) ⟨1509674, by rfl⟩ : syracuseStep 2012899 = 3019349) B3019349
theorem B5306573 : Blo 2011435 5306573 := bbase (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) (by norm_num)
theorem B14150861 : Blo 2011435 14150861 := bstep (se 3 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 14150861 = 5306573) B5306573
theorem B9433907 : Blo 2011435 9433907 := bstep (se 1 (by rfl) ⟨7075430, by rfl⟩ : syracuseStep 9433907 = 14150861) B14150861
theorem B6289271 : Blo 2011435 6289271 := bstep (se 1 (by rfl) ⟨4716953, by rfl⟩ : syracuseStep 6289271 = 9433907) B9433907
theorem B4192847 : Blo 2011435 4192847 := bstep (se 1 (by rfl) ⟨3144635, by rfl⟩ : syracuseStep 4192847 = 6289271) B6289271
theorem B2795231 : Blo 2011435 2795231 := bstep (se 1 (by rfl) ⟨2096423, by rfl⟩ : syracuseStep 2795231 = 4192847) B4192847
theorem B7453949 : Blo 2011435 7453949 := bstep (se 3 (by rfl) ⟨1397615, by rfl⟩ : syracuseStep 7453949 = 2795231) B2795231
theorem B79508789 : Blo 2011435 79508789 := bstep (se 5 (by rfl) ⟨3726974, by rfl⟩ : syracuseStep 79508789 = 7453949) B7453949
theorem B53005859 : Blo 2011435 53005859 := bstep (se 1 (by rfl) ⟨39754394, by rfl⟩ : syracuseStep 53005859 = 79508789) B79508789
theorem B35337239 : Blo 2011435 35337239 := bstep (se 1 (by rfl) ⟨26502929, by rfl⟩ : syracuseStep 35337239 = 53005859) B53005859
theorem B23558159 : Blo 2011435 23558159 := bstep (se 1 (by rfl) ⟨17668619, by rfl⟩ : syracuseStep 23558159 = 35337239) B35337239
theorem B62821757 : Blo 2011435 62821757 := bstep (se 3 (by rfl) ⟨11779079, by rfl⟩ : syracuseStep 62821757 = 23558159) B23558159
theorem B41881171 : Blo 2011435 41881171 := bstep (se 1 (by rfl) ⟨31410878, by rfl⟩ : syracuseStep 41881171 = 62821757) B62821757
theorem B55841561 : Blo 2011435 55841561 := bstep (se 2 (by rfl) ⟨20940585, by rfl⟩ : syracuseStep 55841561 = 41881171) B41881171
theorem B37227707 : Blo 2011435 37227707 := bstep (se 1 (by rfl) ⟨27920780, by rfl⟩ : syracuseStep 37227707 = 55841561) B55841561
theorem B24818471 : Blo 2011435 24818471 := bstep (se 1 (by rfl) ⟨18613853, by rfl⟩ : syracuseStep 24818471 = 37227707) B37227707
theorem B16545647 : Blo 2011435 16545647 := bstep (se 1 (by rfl) ⟨12409235, by rfl⟩ : syracuseStep 16545647 = 24818471) B24818471
theorem B11030431 : Blo 2011435 11030431 := bstep (se 1 (by rfl) ⟨8272823, by rfl⟩ : syracuseStep 11030431 = 16545647) B16545647
theorem B14707241 : Blo 2011435 14707241 := bstep (se 2 (by rfl) ⟨5515215, by rfl⟩ : syracuseStep 14707241 = 11030431) B11030431
theorem B9804827 : Blo 2011435 9804827 := bstep (se 1 (by rfl) ⟨7353620, by rfl⟩ : syracuseStep 9804827 = 14707241) B14707241
theorem B6536551 : Blo 2011435 6536551 := bstep (se 1 (by rfl) ⟨4902413, by rfl⟩ : syracuseStep 6536551 = 9804827) B9804827
theorem B8715401 : Blo 2011435 8715401 := bstep (se 2 (by rfl) ⟨3268275, by rfl⟩ : syracuseStep 8715401 = 6536551) B6536551
theorem B5810267 : Blo 2011435 5810267 := bstep (se 1 (by rfl) ⟨4357700, by rfl⟩ : syracuseStep 5810267 = 8715401) B8715401
theorem B3873511 : Blo 2011435 3873511 := bstep (se 1 (by rfl) ⟨2905133, by rfl⟩ : syracuseStep 3873511 = 5810267) B5810267
theorem B5164681 : Blo 2011435 5164681 := bstep (se 2 (by rfl) ⟨1936755, by rfl⟩ : syracuseStep 5164681 = 3873511) B3873511
theorem B6886241 : Blo 2011435 6886241 := bstep (se 2 (by rfl) ⟨2582340, by rfl⟩ : syracuseStep 6886241 = 5164681) B5164681
theorem B4590827 : Blo 2011435 4590827 := bstep (se 1 (by rfl) ⟨3443120, by rfl⟩ : syracuseStep 4590827 = 6886241) B6886241
theorem B3060551 : Blo 2011435 3060551 := bstep (se 1 (by rfl) ⟨2295413, by rfl⟩ : syracuseStep 3060551 = 4590827) B4590827
theorem B8161469 : Blo 2011435 8161469 := bstep (se 3 (by rfl) ⟨1530275, by rfl⟩ : syracuseStep 8161469 = 3060551) B3060551
theorem B5440979 : Blo 2011435 5440979 := bstep (se 1 (by rfl) ⟨4080734, by rfl⟩ : syracuseStep 5440979 = 8161469) B8161469
theorem B14509277 : Blo 2011435 14509277 := bstep (se 3 (by rfl) ⟨2720489, by rfl⟩ : syracuseStep 14509277 = 5440979) B5440979
theorem B9672851 : Blo 2011435 9672851 := bstep (se 1 (by rfl) ⟨7254638, by rfl⟩ : syracuseStep 9672851 = 14509277) B14509277
theorem B6448567 : Blo 2011435 6448567 := bstep (se 1 (by rfl) ⟨4836425, by rfl⟩ : syracuseStep 6448567 = 9672851) B9672851
theorem B8598089 : Blo 2011435 8598089 := bstep (se 2 (by rfl) ⟨3224283, by rfl⟩ : syracuseStep 8598089 = 6448567) B6448567
theorem B5732059 : Blo 2011435 5732059 := bstep (se 1 (by rfl) ⟨4299044, by rfl⟩ : syracuseStep 5732059 = 8598089) B8598089
theorem B7642745 : Blo 2011435 7642745 := bstep (se 2 (by rfl) ⟨2866029, by rfl⟩ : syracuseStep 7642745 = 5732059) B5732059
theorem B5095163 : Blo 2011435 5095163 := bstep (se 1 (by rfl) ⟨3821372, by rfl⟩ : syracuseStep 5095163 = 7642745) B7642745
theorem B3396775 : Blo 2011435 3396775 := bstep (se 1 (by rfl) ⟨2547581, by rfl⟩ : syracuseStep 3396775 = 5095163) B5095163
theorem B4529033 : Blo 2011435 4529033 := bstep (se 2 (by rfl) ⟨1698387, by rfl⟩ : syracuseStep 4529033 = 3396775) B3396775
theorem B3019355 : Blo 2011435 3019355 := bstep (se 1 (by rfl) ⟨2264516, by rfl⟩ : syracuseStep 3019355 = 4529033) B4529033
theorem B2012903 : Blo 2011435 2012903 := bstep (se 1 (by rfl) ⟨1509677, by rfl⟩ : syracuseStep 2012903 = 3019355) B3019355
theorem B2264521 : Blo 2011435 2264521 := bbase (se 2 (by rfl) ⟨849195, by rfl⟩ : syracuseStep 2264521 = 1698391) (by norm_num)
theorem B3019361 : Blo 2011435 3019361 := bstep (se 2 (by rfl) ⟨1132260, by rfl⟩ : syracuseStep 3019361 = 2264521) B2264521
theorem B2012907 : Blo 2011435 2012907 := bstep (se 1 (by rfl) ⟨1509680, by rfl⟩ : syracuseStep 2012907 = 3019361) B3019361
theorem B17196245 : Blo 2011435 17196245 := bbase (se 7 (by rfl) ⟨201518, by rfl⟩ : syracuseStep 17196245 = 403037) (by norm_num)
theorem B11464163 : Blo 2011435 11464163 := bstep (se 1 (by rfl) ⟨8598122, by rfl⟩ : syracuseStep 11464163 = 17196245) B17196245
theorem B7642775 : Blo 2011435 7642775 := bstep (se 1 (by rfl) ⟨5732081, by rfl⟩ : syracuseStep 7642775 = 11464163) B11464163
theorem B5095183 : Blo 2011435 5095183 := bstep (se 1 (by rfl) ⟨3821387, by rfl⟩ : syracuseStep 5095183 = 7642775) B7642775
theorem B6793577 : Blo 2011435 6793577 := bstep (se 2 (by rfl) ⟨2547591, by rfl⟩ : syracuseStep 6793577 = 5095183) B5095183
theorem B4529051 : Blo 2011435 4529051 := bstep (se 1 (by rfl) ⟨3396788, by rfl⟩ : syracuseStep 4529051 = 6793577) B6793577
theorem B3019367 : Blo 2011435 3019367 := bstep (se 1 (by rfl) ⟨2264525, by rfl⟩ : syracuseStep 3019367 = 4529051) B4529051
theorem B2012911 : Blo 2011435 2012911 := bstep (se 1 (by rfl) ⟨1509683, by rfl⟩ : syracuseStep 2012911 = 3019367) B3019367
theorem B3019373 : Blo 2011435 3019373 := bbase (se 3 (by rfl) ⟨566132, by rfl⟩ : syracuseStep 3019373 = 1132265) (by norm_num)
theorem B2012915 : Blo 2011435 2012915 := bstep (se 1 (by rfl) ⟨1509686, by rfl⟩ : syracuseStep 2012915 = 3019373) B3019373
theorem B4529069 : Blo 2011435 4529069 := bbase (se 3 (by rfl) ⟨849200, by rfl⟩ : syracuseStep 4529069 = 1698401) (by norm_num)
theorem B3019379 : Blo 2011435 3019379 := bstep (se 1 (by rfl) ⟨2264534, by rfl⟩ : syracuseStep 3019379 = 4529069) B4529069
theorem B2012919 : Blo 2011435 2012919 := bstep (se 1 (by rfl) ⟨1509689, by rfl⟩ : syracuseStep 2012919 = 3019379) B3019379
theorem B5732117 : Blo 2011435 5732117 := bbase (se 6 (by rfl) ⟨134346, by rfl⟩ : syracuseStep 5732117 = 268693) (by norm_num)
theorem B3821411 : Blo 2011435 3821411 := bstep (se 1 (by rfl) ⟨2866058, by rfl⟩ : syracuseStep 3821411 = 5732117) B5732117
theorem B2547607 : Blo 2011435 2547607 := bstep (se 1 (by rfl) ⟨1910705, by rfl⟩ : syracuseStep 2547607 = 3821411) B3821411
theorem B3396809 : Blo 2011435 3396809 := bstep (se 2 (by rfl) ⟨1273803, by rfl⟩ : syracuseStep 3396809 = 2547607) B2547607
theorem B2264539 : Blo 2011435 2264539 := bstep (se 1 (by rfl) ⟨1698404, by rfl⟩ : syracuseStep 2264539 = 3396809) B3396809
theorem B3019385 : Blo 2011435 3019385 := bstep (se 2 (by rfl) ⟨1132269, by rfl⟩ : syracuseStep 3019385 = 2264539) B2264539
theorem B2012923 : Blo 2011435 2012923 := bstep (se 1 (by rfl) ⟨1509692, by rfl⟩ : syracuseStep 2012923 = 3019385) B3019385
theorem B3873557 : Blo 2011435 3873557 := bbase (se 6 (by rfl) ⟨90786, by rfl⟩ : syracuseStep 3873557 = 181573) (by norm_num)
theorem B2582371 : Blo 2011435 2582371 := bstep (se 1 (by rfl) ⟨1936778, by rfl⟩ : syracuseStep 2582371 = 3873557) B3873557
theorem B3443161 : Blo 2011435 3443161 := bstep (se 2 (by rfl) ⟨1291185, by rfl⟩ : syracuseStep 3443161 = 2582371) B2582371
theorem B4590881 : Blo 2011435 4590881 := bstep (se 2 (by rfl) ⟨1721580, by rfl⟩ : syracuseStep 4590881 = 3443161) B3443161
theorem B3060587 : Blo 2011435 3060587 := bstep (se 1 (by rfl) ⟨2295440, by rfl⟩ : syracuseStep 3060587 = 4590881) B4590881
theorem B2040391 : Blo 2011435 2040391 := bstep (se 1 (by rfl) ⟨1530293, by rfl⟩ : syracuseStep 2040391 = 3060587) B3060587
theorem B10882085 : Blo 2011435 10882085 := bstep (se 4 (by rfl) ⟨1020195, by rfl⟩ : syracuseStep 10882085 = 2040391) B2040391
theorem B29018893 : Blo 2011435 29018893 := bstep (se 3 (by rfl) ⟨5441042, by rfl⟩ : syracuseStep 29018893 = 10882085) B10882085
theorem B38691857 : Blo 2011435 38691857 := bstep (se 2 (by rfl) ⟨14509446, by rfl⟩ : syracuseStep 38691857 = 29018893) B29018893
theorem B25794571 : Blo 2011435 25794571 := bstep (se 1 (by rfl) ⟨19345928, by rfl⟩ : syracuseStep 25794571 = 38691857) B38691857
theorem B34392761 : Blo 2011435 34392761 := bstep (se 2 (by rfl) ⟨12897285, by rfl⟩ : syracuseStep 34392761 = 25794571) B25794571
theorem B22928507 : Blo 2011435 22928507 := bstep (se 1 (by rfl) ⟨17196380, by rfl⟩ : syracuseStep 22928507 = 34392761) B34392761
theorem B15285671 : Blo 2011435 15285671 := bstep (se 1 (by rfl) ⟨11464253, by rfl⟩ : syracuseStep 15285671 = 22928507) B22928507
theorem B10190447 : Blo 2011435 10190447 := bstep (se 1 (by rfl) ⟨7642835, by rfl⟩ : syracuseStep 10190447 = 15285671) B15285671
theorem B6793631 : Blo 2011435 6793631 := bstep (se 1 (by rfl) ⟨5095223, by rfl⟩ : syracuseStep 6793631 = 10190447) B10190447
theorem B4529087 : Blo 2011435 4529087 := bstep (se 1 (by rfl) ⟨3396815, by rfl⟩ : syracuseStep 4529087 = 6793631) B6793631
theorem B3019391 : Blo 2011435 3019391 := bstep (se 1 (by rfl) ⟨2264543, by rfl⟩ : syracuseStep 3019391 = 4529087) B4529087
theorem B2012927 : Blo 2011435 2012927 := bstep (se 1 (by rfl) ⟨1509695, by rfl⟩ : syracuseStep 2012927 = 3019391) B3019391
theorem B3019397 : Blo 2011435 3019397 := bbase (se 4 (by rfl) ⟨283068, by rfl⟩ : syracuseStep 3019397 = 566137) (by norm_num)
theorem B2012931 : Blo 2011435 2012931 := bstep (se 1 (by rfl) ⟨1509698, by rfl⟩ : syracuseStep 2012931 = 3019397) B3019397
theorem B3396829 : Blo 2011435 3396829 := bbase (se 3 (by rfl) ⟨636905, by rfl⟩ : syracuseStep 3396829 = 1273811) (by norm_num)
theorem B4529105 : Blo 2011435 4529105 := bstep (se 2 (by rfl) ⟨1698414, by rfl⟩ : syracuseStep 4529105 = 3396829) B3396829
theorem B3019403 : Blo 2011435 3019403 := bstep (se 1 (by rfl) ⟨2264552, by rfl⟩ : syracuseStep 3019403 = 4529105) B4529105
theorem B2012935 : Blo 2011435 2012935 := bstep (se 1 (by rfl) ⟨1509701, by rfl⟩ : syracuseStep 2012935 = 3019403) B3019403
theorem B2264557 : Blo 2011435 2264557 := bbase (se 3 (by rfl) ⟨424604, by rfl⟩ : syracuseStep 2264557 = 849209) (by norm_num)
theorem B3019409 : Blo 2011435 3019409 := bstep (se 2 (by rfl) ⟨1132278, by rfl⟩ : syracuseStep 3019409 = 2264557) B2264557
theorem B2012939 : Blo 2011435 2012939 := bstep (se 1 (by rfl) ⟨1509704, by rfl⟩ : syracuseStep 2012939 = 3019409) B3019409
theorem B6793685 : Blo 2011435 6793685 := bbase (se 7 (by rfl) ⟨79613, by rfl⟩ : syracuseStep 6793685 = 159227) (by norm_num)
theorem B4529123 : Blo 2011435 4529123 := bstep (se 1 (by rfl) ⟨3396842, by rfl⟩ : syracuseStep 4529123 = 6793685) B6793685
theorem B3019415 : Blo 2011435 3019415 := bstep (se 1 (by rfl) ⟨2264561, by rfl⟩ : syracuseStep 3019415 = 4529123) B4529123
theorem B2012943 : Blo 2011435 2012943 := bstep (se 1 (by rfl) ⟨1509707, by rfl⟩ : syracuseStep 2012943 = 3019415) B3019415
theorem B3019421 : Blo 2011435 3019421 := bbase (se 3 (by rfl) ⟨566141, by rfl⟩ : syracuseStep 3019421 = 1132283) (by norm_num)
theorem B2012947 : Blo 2011435 2012947 := bstep (se 1 (by rfl) ⟨1509710, by rfl⟩ : syracuseStep 2012947 = 3019421) B3019421
theorem B4529141 : Blo 2011435 4529141 := bbase (se 5 (by rfl) ⟨212303, by rfl⟩ : syracuseStep 4529141 = 424607) (by norm_num)
theorem B3019427 : Blo 2011435 3019427 := bstep (se 1 (by rfl) ⟨2264570, by rfl⟩ : syracuseStep 3019427 = 4529141) B4529141
theorem B2012951 : Blo 2011435 2012951 := bstep (se 1 (by rfl) ⟨1509713, by rfl⟩ : syracuseStep 2012951 = 3019427) B3019427
theorem B5164813 : Blo 2011435 5164813 := bbase (se 3 (by rfl) ⟨968402, by rfl⟩ : syracuseStep 5164813 = 1936805) (by norm_num)
theorem B27545669 : Blo 2011435 27545669 := bstep (se 4 (by rfl) ⟨2582406, by rfl⟩ : syracuseStep 27545669 = 5164813) B5164813
theorem B18363779 : Blo 2011435 18363779 := bstep (se 1 (by rfl) ⟨13772834, by rfl⟩ : syracuseStep 18363779 = 27545669) B27545669
theorem B12242519 : Blo 2011435 12242519 := bstep (se 1 (by rfl) ⟨9181889, by rfl⟩ : syracuseStep 12242519 = 18363779) B18363779
theorem B8161679 : Blo 2011435 8161679 := bstep (se 1 (by rfl) ⟨6121259, by rfl⟩ : syracuseStep 8161679 = 12242519) B12242519
theorem B21764477 : Blo 2011435 21764477 := bstep (se 3 (by rfl) ⟨4080839, by rfl⟩ : syracuseStep 21764477 = 8161679) B8161679
theorem B58038605 : Blo 2011435 58038605 := bstep (se 3 (by rfl) ⟨10882238, by rfl⟩ : syracuseStep 58038605 = 21764477) B21764477
theorem B38692403 : Blo 2011435 38692403 := bstep (se 1 (by rfl) ⟨29019302, by rfl⟩ : syracuseStep 38692403 = 58038605) B58038605
theorem B25794935 : Blo 2011435 25794935 := bstep (se 1 (by rfl) ⟨19346201, by rfl⟩ : syracuseStep 25794935 = 38692403) B38692403
theorem B17196623 : Blo 2011435 17196623 := bstep (se 1 (by rfl) ⟨12897467, by rfl⟩ : syracuseStep 17196623 = 25794935) B25794935
theorem B11464415 : Blo 2011435 11464415 := bstep (se 1 (by rfl) ⟨8598311, by rfl⟩ : syracuseStep 11464415 = 17196623) B17196623
theorem B7642943 : Blo 2011435 7642943 := bstep (se 1 (by rfl) ⟨5732207, by rfl⟩ : syracuseStep 7642943 = 11464415) B11464415
theorem B5095295 : Blo 2011435 5095295 := bstep (se 1 (by rfl) ⟨3821471, by rfl⟩ : syracuseStep 5095295 = 7642943) B7642943
theorem B3396863 : Blo 2011435 3396863 := bstep (se 1 (by rfl) ⟨2547647, by rfl⟩ : syracuseStep 3396863 = 5095295) B5095295
theorem B2264575 : Blo 2011435 2264575 := bstep (se 1 (by rfl) ⟨1698431, by rfl⟩ : syracuseStep 2264575 = 3396863) B3396863
theorem B3019433 : Blo 2011435 3019433 := bstep (se 2 (by rfl) ⟨1132287, by rfl⟩ : syracuseStep 3019433 = 2264575) B2264575
theorem B2012955 : Blo 2011435 2012955 := bstep (se 1 (by rfl) ⟨1509716, by rfl⟩ : syracuseStep 2012955 = 3019433) B3019433
theorem B2866109 : Blo 2011435 2866109 := bbase (se 3 (by rfl) ⟨537395, by rfl⟩ : syracuseStep 2866109 = 1074791) (by norm_num)
theorem B7642957 : Blo 2011435 7642957 := bstep (se 3 (by rfl) ⟨1433054, by rfl⟩ : syracuseStep 7642957 = 2866109) B2866109
theorem B10190609 : Blo 2011435 10190609 := bstep (se 2 (by rfl) ⟨3821478, by rfl⟩ : syracuseStep 10190609 = 7642957) B7642957
theorem B6793739 : Blo 2011435 6793739 := bstep (se 1 (by rfl) ⟨5095304, by rfl⟩ : syracuseStep 6793739 = 10190609) B10190609
theorem B4529159 : Blo 2011435 4529159 := bstep (se 1 (by rfl) ⟨3396869, by rfl⟩ : syracuseStep 4529159 = 6793739) B6793739
theorem B3019439 : Blo 2011435 3019439 := bstep (se 1 (by rfl) ⟨2264579, by rfl⟩ : syracuseStep 3019439 = 4529159) B4529159
theorem B2012959 : Blo 2011435 2012959 := bstep (se 1 (by rfl) ⟨1509719, by rfl⟩ : syracuseStep 2012959 = 3019439) B3019439
theorem B3019445 : Blo 2011435 3019445 := bbase (se 5 (by rfl) ⟨141536, by rfl⟩ : syracuseStep 3019445 = 283073) (by norm_num)
theorem B2012963 : Blo 2011435 2012963 := bstep (se 1 (by rfl) ⟨1509722, by rfl⟩ : syracuseStep 2012963 = 3019445) B3019445
theorem B5095325 : Blo 2011435 5095325 := bbase (se 3 (by rfl) ⟨955373, by rfl⟩ : syracuseStep 5095325 = 1910747) (by norm_num)
theorem B3396883 : Blo 2011435 3396883 := bstep (se 1 (by rfl) ⟨2547662, by rfl⟩ : syracuseStep 3396883 = 5095325) B5095325
theorem B4529177 : Blo 2011435 4529177 := bstep (se 2 (by rfl) ⟨1698441, by rfl⟩ : syracuseStep 4529177 = 3396883) B3396883
theorem B3019451 : Blo 2011435 3019451 := bstep (se 1 (by rfl) ⟨2264588, by rfl⟩ : syracuseStep 3019451 = 4529177) B4529177
theorem B2012967 : Blo 2011435 2012967 := bstep (se 1 (by rfl) ⟨1509725, by rfl⟩ : syracuseStep 2012967 = 3019451) B3019451
theorem B2264593 : Blo 2011435 2264593 := bbase (se 2 (by rfl) ⟨849222, by rfl⟩ : syracuseStep 2264593 = 1698445) (by norm_num)
theorem B3019457 : Blo 2011435 3019457 := bstep (se 2 (by rfl) ⟨1132296, by rfl⟩ : syracuseStep 3019457 = 2264593) B2264593
theorem B2012971 : Blo 2011435 2012971 := bstep (se 1 (by rfl) ⟨1509728, by rfl⟩ : syracuseStep 2012971 = 3019457) B3019457
theorem B3821509 : Blo 2011435 3821509 := bbase (se 4 (by rfl) ⟨358266, by rfl⟩ : syracuseStep 3821509 = 716533) (by norm_num)
theorem B5095345 : Blo 2011435 5095345 := bstep (se 2 (by rfl) ⟨1910754, by rfl⟩ : syracuseStep 5095345 = 3821509) B3821509
theorem B6793793 : Blo 2011435 6793793 := bstep (se 2 (by rfl) ⟨2547672, by rfl⟩ : syracuseStep 6793793 = 5095345) B5095345
theorem B4529195 : Blo 2011435 4529195 := bstep (se 1 (by rfl) ⟨3396896, by rfl⟩ : syracuseStep 4529195 = 6793793) B6793793
theorem B3019463 : Blo 2011435 3019463 := bstep (se 1 (by rfl) ⟨2264597, by rfl⟩ : syracuseStep 3019463 = 4529195) B4529195
theorem B2012975 : Blo 2011435 2012975 := bstep (se 1 (by rfl) ⟨1509731, by rfl⟩ : syracuseStep 2012975 = 3019463) B3019463
theorem B3019469 : Blo 2011435 3019469 := bbase (se 3 (by rfl) ⟨566150, by rfl⟩ : syracuseStep 3019469 = 1132301) (by norm_num)
theorem B2012979 : Blo 2011435 2012979 := bstep (se 1 (by rfl) ⟨1509734, by rfl⟩ : syracuseStep 2012979 = 3019469) B3019469
theorem B4529213 : Blo 2011435 4529213 := bbase (se 3 (by rfl) ⟨849227, by rfl⟩ : syracuseStep 4529213 = 1698455) (by norm_num)
theorem B3019475 : Blo 2011435 3019475 := bstep (se 1 (by rfl) ⟨2264606, by rfl⟩ : syracuseStep 3019475 = 4529213) B4529213
theorem B2012983 : Blo 2011435 2012983 := bstep (se 1 (by rfl) ⟨1509737, by rfl⟩ : syracuseStep 2012983 = 3019475) B3019475
theorem B3396917 : Blo 2011435 3396917 := bbase (se 5 (by rfl) ⟨159230, by rfl⟩ : syracuseStep 3396917 = 318461) (by norm_num)
theorem B2264611 : Blo 2011435 2264611 := bstep (se 1 (by rfl) ⟨1698458, by rfl⟩ : syracuseStep 2264611 = 3396917) B3396917
theorem B3019481 : Blo 2011435 3019481 := bstep (se 2 (by rfl) ⟨1132305, by rfl⟩ : syracuseStep 3019481 = 2264611) B2264611
theorem B2012987 : Blo 2011435 2012987 := bstep (se 1 (by rfl) ⟨1509740, by rfl⟩ : syracuseStep 2012987 = 3019481) B3019481
theorem B5732309 : Blo 2011435 5732309 := bbase (se 7 (by rfl) ⟨67175, by rfl⟩ : syracuseStep 5732309 = 134351) (by norm_num)
theorem B15286157 : Blo 2011435 15286157 := bstep (se 3 (by rfl) ⟨2866154, by rfl⟩ : syracuseStep 15286157 = 5732309) B5732309
theorem B10190771 : Blo 2011435 10190771 := bstep (se 1 (by rfl) ⟨7643078, by rfl⟩ : syracuseStep 10190771 = 15286157) B15286157
theorem B6793847 : Blo 2011435 6793847 := bstep (se 1 (by rfl) ⟨5095385, by rfl⟩ : syracuseStep 6793847 = 10190771) B10190771
theorem B4529231 : Blo 2011435 4529231 := bstep (se 1 (by rfl) ⟨3396923, by rfl⟩ : syracuseStep 4529231 = 6793847) B6793847
theorem B3019487 : Blo 2011435 3019487 := bstep (se 1 (by rfl) ⟨2264615, by rfl⟩ : syracuseStep 3019487 = 4529231) B4529231
theorem B2012991 : Blo 2011435 2012991 := bstep (se 1 (by rfl) ⟨1509743, by rfl⟩ : syracuseStep 2012991 = 3019487) B3019487
theorem B3019493 : Blo 2011435 3019493 := bbase (se 4 (by rfl) ⟨283077, by rfl⟩ : syracuseStep 3019493 = 566155) (by norm_num)
theorem B2012995 : Blo 2011435 2012995 := bstep (se 1 (by rfl) ⟨1509746, by rfl⟩ : syracuseStep 2012995 = 3019493) B3019493
theorem B2149625 : Blo 2011435 2149625 := bbase (se 2 (by rfl) ⟨806109, by rfl⟩ : syracuseStep 2149625 = 1612219) (by norm_num)
theorem B5732333 : Blo 2011435 5732333 := bstep (se 3 (by rfl) ⟨1074812, by rfl⟩ : syracuseStep 5732333 = 2149625) B2149625
theorem B3821555 : Blo 2011435 3821555 := bstep (se 1 (by rfl) ⟨2866166, by rfl⟩ : syracuseStep 3821555 = 5732333) B5732333
theorem B2547703 : Blo 2011435 2547703 := bstep (se 1 (by rfl) ⟨1910777, by rfl⟩ : syracuseStep 2547703 = 3821555) B3821555
theorem B3396937 : Blo 2011435 3396937 := bstep (se 2 (by rfl) ⟨1273851, by rfl⟩ : syracuseStep 3396937 = 2547703) B2547703
theorem B4529249 : Blo 2011435 4529249 := bstep (se 2 (by rfl) ⟨1698468, by rfl⟩ : syracuseStep 4529249 = 3396937) B3396937
theorem B3019499 : Blo 2011435 3019499 := bstep (se 1 (by rfl) ⟨2264624, by rfl⟩ : syracuseStep 3019499 = 4529249) B4529249
theorem B2012999 : Blo 2011435 2012999 := bstep (se 1 (by rfl) ⟨1509749, by rfl⟩ : syracuseStep 2012999 = 3019499) B3019499
theorem B2264629 : Blo 2011435 2264629 := bbase (se 5 (by rfl) ⟨106154, by rfl⟩ : syracuseStep 2264629 = 212309) (by norm_num)
theorem B3019505 : Blo 2011435 3019505 := bstep (se 2 (by rfl) ⟨1132314, by rfl⟩ : syracuseStep 3019505 = 2264629) B2264629
theorem B2013003 : Blo 2011435 2013003 := bstep (se 1 (by rfl) ⟨1509752, by rfl⟩ : syracuseStep 2013003 = 3019505) B3019505
theorem B2547713 : Blo 2011435 2547713 := bbase (se 2 (by rfl) ⟨955392, by rfl⟩ : syracuseStep 2547713 = 1910785) (by norm_num)
theorem B6793901 : Blo 2011435 6793901 := bstep (se 3 (by rfl) ⟨1273856, by rfl⟩ : syracuseStep 6793901 = 2547713) B2547713
theorem B4529267 : Blo 2011435 4529267 := bstep (se 1 (by rfl) ⟨3396950, by rfl⟩ : syracuseStep 4529267 = 6793901) B6793901
theorem B3019511 : Blo 2011435 3019511 := bstep (se 1 (by rfl) ⟨2264633, by rfl⟩ : syracuseStep 3019511 = 4529267) B4529267
theorem B2013007 : Blo 2011435 2013007 := bstep (se 1 (by rfl) ⟨1509755, by rfl⟩ : syracuseStep 2013007 = 3019511) B3019511
theorem B3019517 : Blo 2011435 3019517 := bbase (se 3 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 3019517 = 1132319) (by norm_num)
theorem B2013011 : Blo 2011435 2013011 := bstep (se 1 (by rfl) ⟨1509758, by rfl⟩ : syracuseStep 2013011 = 3019517) B3019517
theorem B4529285 : Blo 2011435 4529285 := bbase (se 4 (by rfl) ⟨424620, by rfl⟩ : syracuseStep 4529285 = 849241) (by norm_num)
theorem B3019523 : Blo 2011435 3019523 := bstep (se 1 (by rfl) ⟨2264642, by rfl⟩ : syracuseStep 3019523 = 4529285) B4529285
theorem B2013015 : Blo 2011435 2013015 := bstep (se 1 (by rfl) ⟨1509761, by rfl⟩ : syracuseStep 2013015 = 3019523) B3019523
theorem B4299293 : Blo 2011435 4299293 := bbase (se 3 (by rfl) ⟨806117, by rfl⟩ : syracuseStep 4299293 = 1612235) (by norm_num)
theorem B2866195 : Blo 2011435 2866195 := bstep (se 1 (by rfl) ⟨2149646, by rfl⟩ : syracuseStep 2866195 = 4299293) B4299293
theorem B3821593 : Blo 2011435 3821593 := bstep (se 2 (by rfl) ⟨1433097, by rfl⟩ : syracuseStep 3821593 = 2866195) B2866195
theorem B5095457 : Blo 2011435 5095457 := bstep (se 2 (by rfl) ⟨1910796, by rfl⟩ : syracuseStep 5095457 = 3821593) B3821593
theorem B3396971 : Blo 2011435 3396971 := bstep (se 1 (by rfl) ⟨2547728, by rfl⟩ : syracuseStep 3396971 = 5095457) B5095457
theorem B2264647 : Blo 2011435 2264647 := bstep (se 1 (by rfl) ⟨1698485, by rfl⟩ : syracuseStep 2264647 = 3396971) B3396971
theorem B3019529 : Blo 2011435 3019529 := bstep (se 2 (by rfl) ⟨1132323, by rfl⟩ : syracuseStep 3019529 = 2264647) B2264647
theorem B2013019 : Blo 2011435 2013019 := bstep (se 1 (by rfl) ⟨1509764, by rfl⟩ : syracuseStep 2013019 = 3019529) B3019529
theorem B10190933 : Blo 2011435 10190933 := bbase (se 8 (by rfl) ⟨59712, by rfl⟩ : syracuseStep 10190933 = 119425) (by norm_num)
theorem B6793955 : Blo 2011435 6793955 := bstep (se 1 (by rfl) ⟨5095466, by rfl⟩ : syracuseStep 6793955 = 10190933) B10190933
theorem B4529303 : Blo 2011435 4529303 := bstep (se 1 (by rfl) ⟨3396977, by rfl⟩ : syracuseStep 4529303 = 6793955) B6793955
theorem B3019535 : Blo 2011435 3019535 := bstep (se 1 (by rfl) ⟨2264651, by rfl⟩ : syracuseStep 3019535 = 4529303) B4529303
theorem B2013023 : Blo 2011435 2013023 := bstep (se 1 (by rfl) ⟨1509767, by rfl⟩ : syracuseStep 2013023 = 3019535) B3019535
theorem B3019541 : Blo 2011435 3019541 := bbase (se 6 (by rfl) ⟨70770, by rfl⟩ : syracuseStep 3019541 = 141541) (by norm_num)
theorem B2013027 : Blo 2011435 2013027 := bstep (se 1 (by rfl) ⟨1509770, by rfl⟩ : syracuseStep 2013027 = 3019541) B3019541
theorem B3873757 : Blo 2011435 3873757 := bbase (se 3 (by rfl) ⟨726329, by rfl⟩ : syracuseStep 3873757 = 1452659) (by norm_num)
theorem B5165009 : Blo 2011435 5165009 := bstep (se 2 (by rfl) ⟨1936878, by rfl⟩ : syracuseStep 5165009 = 3873757) B3873757
theorem B3443339 : Blo 2011435 3443339 := bstep (se 1 (by rfl) ⟨2582504, by rfl⟩ : syracuseStep 3443339 = 5165009) B5165009
theorem B2295559 : Blo 2011435 2295559 := bstep (se 1 (by rfl) ⟨1721669, by rfl⟩ : syracuseStep 2295559 = 3443339) B3443339
theorem B12242981 : Blo 2011435 12242981 := bstep (se 4 (by rfl) ⟨1147779, by rfl⟩ : syracuseStep 12242981 = 2295559) B2295559
theorem B8161987 : Blo 2011435 8161987 := bstep (se 1 (by rfl) ⟨6121490, by rfl⟩ : syracuseStep 8161987 = 12242981) B12242981
theorem B10882649 : Blo 2011435 10882649 := bstep (se 2 (by rfl) ⟨4080993, by rfl⟩ : syracuseStep 10882649 = 8161987) B8161987
theorem B7255099 : Blo 2011435 7255099 := bstep (se 1 (by rfl) ⟨5441324, by rfl⟩ : syracuseStep 7255099 = 10882649) B10882649
theorem B38693861 : Blo 2011435 38693861 := bstep (se 4 (by rfl) ⟨3627549, by rfl⟩ : syracuseStep 38693861 = 7255099) B7255099
theorem B25795907 : Blo 2011435 25795907 := bstep (se 1 (by rfl) ⟨19346930, by rfl⟩ : syracuseStep 25795907 = 38693861) B38693861
theorem B17197271 : Blo 2011435 17197271 := bstep (se 1 (by rfl) ⟨12897953, by rfl⟩ : syracuseStep 17197271 = 25795907) B25795907
theorem B11464847 : Blo 2011435 11464847 := bstep (se 1 (by rfl) ⟨8598635, by rfl⟩ : syracuseStep 11464847 = 17197271) B17197271
theorem B7643231 : Blo 2011435 7643231 := bstep (se 1 (by rfl) ⟨5732423, by rfl⟩ : syracuseStep 7643231 = 11464847) B11464847
theorem B5095487 : Blo 2011435 5095487 := bstep (se 1 (by rfl) ⟨3821615, by rfl⟩ : syracuseStep 5095487 = 7643231) B7643231
theorem B3396991 : Blo 2011435 3396991 := bstep (se 1 (by rfl) ⟨2547743, by rfl⟩ : syracuseStep 3396991 = 5095487) B5095487
theorem B4529321 : Blo 2011435 4529321 := bstep (se 2 (by rfl) ⟨1698495, by rfl⟩ : syracuseStep 4529321 = 3396991) B3396991
theorem B3019547 : Blo 2011435 3019547 := bstep (se 1 (by rfl) ⟨2264660, by rfl⟩ : syracuseStep 3019547 = 4529321) B4529321
theorem B2013031 : Blo 2011435 2013031 := bstep (se 1 (by rfl) ⟨1509773, by rfl⟩ : syracuseStep 2013031 = 3019547) B3019547
theorem B2264665 : Blo 2011435 2264665 := bbase (se 2 (by rfl) ⟨849249, by rfl⟩ : syracuseStep 2264665 = 1698499) (by norm_num)
theorem B3019553 : Blo 2011435 3019553 := bstep (se 2 (by rfl) ⟨1132332, by rfl⟩ : syracuseStep 3019553 = 2264665) B2264665
theorem B2013035 : Blo 2011435 2013035 := bstep (se 1 (by rfl) ⟨1509776, by rfl⟩ : syracuseStep 2013035 = 3019553) B3019553
theorem B8162021 : Blo 2011435 8162021 := bbase (se 4 (by rfl) ⟨765189, by rfl⟩ : syracuseStep 8162021 = 1530379) (by norm_num)
theorem B5441347 : Blo 2011435 5441347 := bstep (se 1 (by rfl) ⟨4081010, by rfl⟩ : syracuseStep 5441347 = 8162021) B8162021
theorem B7255129 : Blo 2011435 7255129 := bstep (se 2 (by rfl) ⟨2720673, by rfl⟩ : syracuseStep 7255129 = 5441347) B5441347
theorem B9673505 : Blo 2011435 9673505 := bstep (se 2 (by rfl) ⟨3627564, by rfl⟩ : syracuseStep 9673505 = 7255129) B7255129
theorem B6449003 : Blo 2011435 6449003 := bstep (se 1 (by rfl) ⟨4836752, by rfl⟩ : syracuseStep 6449003 = 9673505) B9673505
theorem B4299335 : Blo 2011435 4299335 := bstep (se 1 (by rfl) ⟨3224501, by rfl⟩ : syracuseStep 4299335 = 6449003) B6449003
theorem B2866223 : Blo 2011435 2866223 := bstep (se 1 (by rfl) ⟨2149667, by rfl⟩ : syracuseStep 2866223 = 4299335) B4299335
theorem B7643261 : Blo 2011435 7643261 := bstep (se 3 (by rfl) ⟨1433111, by rfl⟩ : syracuseStep 7643261 = 2866223) B2866223
theorem B5095507 : Blo 2011435 5095507 := bstep (se 1 (by rfl) ⟨3821630, by rfl⟩ : syracuseStep 5095507 = 7643261) B7643261
theorem B6794009 : Blo 2011435 6794009 := bstep (se 2 (by rfl) ⟨2547753, by rfl⟩ : syracuseStep 6794009 = 5095507) B5095507
theorem B4529339 : Blo 2011435 4529339 := bstep (se 1 (by rfl) ⟨3397004, by rfl⟩ : syracuseStep 4529339 = 6794009) B6794009
theorem B3019559 : Blo 2011435 3019559 := bstep (se 1 (by rfl) ⟨2264669, by rfl⟩ : syracuseStep 3019559 = 4529339) B4529339
theorem B2013039 : Blo 2011435 2013039 := bstep (se 1 (by rfl) ⟨1509779, by rfl⟩ : syracuseStep 2013039 = 3019559) B3019559
theorem B3019565 : Blo 2011435 3019565 := bbase (se 3 (by rfl) ⟨566168, by rfl⟩ : syracuseStep 3019565 = 1132337) (by norm_num)
theorem B2013043 : Blo 2011435 2013043 := bstep (se 1 (by rfl) ⟨1509782, by rfl⟩ : syracuseStep 2013043 = 3019565) B3019565
theorem B4529357 : Blo 2011435 4529357 := bbase (se 3 (by rfl) ⟨849254, by rfl⟩ : syracuseStep 4529357 = 1698509) (by norm_num)
theorem B3019571 : Blo 2011435 3019571 := bstep (se 1 (by rfl) ⟨2264678, by rfl⟩ : syracuseStep 3019571 = 4529357) B4529357
theorem B2013047 : Blo 2011435 2013047 := bstep (se 1 (by rfl) ⟨1509785, by rfl⟩ : syracuseStep 2013047 = 3019571) B3019571
theorem B2547769 : Blo 2011435 2547769 := bbase (se 2 (by rfl) ⟨955413, by rfl⟩ : syracuseStep 2547769 = 1910827) (by norm_num)
theorem B3397025 : Blo 2011435 3397025 := bstep (se 2 (by rfl) ⟨1273884, by rfl⟩ : syracuseStep 3397025 = 2547769) B2547769
theorem B2264683 : Blo 2011435 2264683 := bstep (se 1 (by rfl) ⟨1698512, by rfl⟩ : syracuseStep 2264683 = 3397025) B3397025
theorem B3019577 : Blo 2011435 3019577 := bstep (se 2 (by rfl) ⟨1132341, by rfl⟩ : syracuseStep 3019577 = 2264683) B2264683
theorem B2013051 : Blo 2011435 2013051 := bstep (se 1 (by rfl) ⟨1509788, by rfl⟩ : syracuseStep 2013051 = 3019577) B3019577
theorem B3443381 : Blo 2011435 3443381 := bbase (se 5 (by rfl) ⟨161408, by rfl⟩ : syracuseStep 3443381 = 322817) (by norm_num)
theorem B2295587 : Blo 2011435 2295587 := bstep (se 1 (by rfl) ⟨1721690, by rfl⟩ : syracuseStep 2295587 = 3443381) B3443381
theorem B6121565 : Blo 2011435 6121565 := bstep (se 3 (by rfl) ⟨1147793, by rfl⟩ : syracuseStep 6121565 = 2295587) B2295587
theorem B4081043 : Blo 2011435 4081043 := bstep (se 1 (by rfl) ⟨3060782, by rfl⟩ : syracuseStep 4081043 = 6121565) B6121565
theorem B2720695 : Blo 2011435 2720695 := bstep (se 1 (by rfl) ⟨2040521, by rfl⟩ : syracuseStep 2720695 = 4081043) B4081043
theorem B3627593 : Blo 2011435 3627593 := bstep (se 2 (by rfl) ⟨1360347, by rfl⟩ : syracuseStep 3627593 = 2720695) B2720695
theorem B2418395 : Blo 2011435 2418395 := bstep (se 1 (by rfl) ⟨1813796, by rfl⟩ : syracuseStep 2418395 = 3627593) B3627593
theorem B6449053 : Blo 2011435 6449053 := bstep (se 3 (by rfl) ⟨1209197, by rfl⟩ : syracuseStep 6449053 = 2418395) B2418395
theorem B8598737 : Blo 2011435 8598737 := bstep (se 2 (by rfl) ⟨3224526, by rfl⟩ : syracuseStep 8598737 = 6449053) B6449053
theorem B22929965 : Blo 2011435 22929965 := bstep (se 3 (by rfl) ⟨4299368, by rfl⟩ : syracuseStep 22929965 = 8598737) B8598737
theorem B15286643 : Blo 2011435 15286643 := bstep (se 1 (by rfl) ⟨11464982, by rfl⟩ : syracuseStep 15286643 = 22929965) B22929965
theorem B10191095 : Blo 2011435 10191095 := bstep (se 1 (by rfl) ⟨7643321, by rfl⟩ : syracuseStep 10191095 = 15286643) B15286643
theorem B6794063 : Blo 2011435 6794063 := bstep (se 1 (by rfl) ⟨5095547, by rfl⟩ : syracuseStep 6794063 = 10191095) B10191095
theorem B4529375 : Blo 2011435 4529375 := bstep (se 1 (by rfl) ⟨3397031, by rfl⟩ : syracuseStep 4529375 = 6794063) B6794063
theorem B3019583 : Blo 2011435 3019583 := bstep (se 1 (by rfl) ⟨2264687, by rfl⟩ : syracuseStep 3019583 = 4529375) B4529375
theorem B2013055 : Blo 2011435 2013055 := bstep (se 1 (by rfl) ⟨1509791, by rfl⟩ : syracuseStep 2013055 = 3019583) B3019583
theorem B3019589 : Blo 2011435 3019589 := bbase (se 4 (by rfl) ⟨283086, by rfl⟩ : syracuseStep 3019589 = 566173) (by norm_num)
theorem B2013059 : Blo 2011435 2013059 := bstep (se 1 (by rfl) ⟨1509794, by rfl⟩ : syracuseStep 2013059 = 3019589) B3019589
theorem B3397045 : Blo 2011435 3397045 := bbase (se 5 (by rfl) ⟨159236, by rfl⟩ : syracuseStep 3397045 = 318473) (by norm_num)
theorem B4529393 : Blo 2011435 4529393 := bstep (se 2 (by rfl) ⟨1698522, by rfl⟩ : syracuseStep 4529393 = 3397045) B3397045
theorem B3019595 : Blo 2011435 3019595 := bstep (se 1 (by rfl) ⟨2264696, by rfl⟩ : syracuseStep 3019595 = 4529393) B4529393
theorem B2013063 : Blo 2011435 2013063 := bstep (se 1 (by rfl) ⟨1509797, by rfl⟩ : syracuseStep 2013063 = 3019595) B3019595
theorem B2264701 : Blo 2011435 2264701 := bbase (se 3 (by rfl) ⟨424631, by rfl⟩ : syracuseStep 2264701 = 849263) (by norm_num)
theorem B3019601 : Blo 2011435 3019601 := bstep (se 2 (by rfl) ⟨1132350, by rfl⟩ : syracuseStep 3019601 = 2264701) B2264701
theorem B2013067 : Blo 2011435 2013067 := bstep (se 1 (by rfl) ⟨1509800, by rfl⟩ : syracuseStep 2013067 = 3019601) B3019601
theorem B6794117 : Blo 2011435 6794117 := bbase (se 4 (by rfl) ⟨636948, by rfl⟩ : syracuseStep 6794117 = 1273897) (by norm_num)
theorem B4529411 : Blo 2011435 4529411 := bstep (se 1 (by rfl) ⟨3397058, by rfl⟩ : syracuseStep 4529411 = 6794117) B6794117
theorem B3019607 : Blo 2011435 3019607 := bstep (se 1 (by rfl) ⟨2264705, by rfl⟩ : syracuseStep 3019607 = 4529411) B4529411
theorem B2013071 : Blo 2011435 2013071 := bstep (se 1 (by rfl) ⟨1509803, by rfl⟩ : syracuseStep 2013071 = 3019607) B3019607
theorem B3019613 : Blo 2011435 3019613 := bbase (se 3 (by rfl) ⟨566177, by rfl⟩ : syracuseStep 3019613 = 1132355) (by norm_num)
theorem B2013075 : Blo 2011435 2013075 := bstep (se 1 (by rfl) ⟨1509806, by rfl⟩ : syracuseStep 2013075 = 3019613) B3019613
theorem B4529429 : Blo 2011435 4529429 := bbase (se 6 (by rfl) ⟨106158, by rfl⟩ : syracuseStep 4529429 = 212317) (by norm_num)
theorem B3019619 : Blo 2011435 3019619 := bstep (se 1 (by rfl) ⟨2264714, by rfl⟩ : syracuseStep 3019619 = 4529429) B4529429
theorem B2013079 : Blo 2011435 2013079 := bstep (se 1 (by rfl) ⟨1509809, by rfl⟩ : syracuseStep 2013079 = 3019619) B3019619
theorem B7643429 : Blo 2011435 7643429 := bbase (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) (by norm_num)
theorem B5095619 : Blo 2011435 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B3397079 : Blo 2011435 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B2264719 : Blo 2011435 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B3019625 : Blo 2011435 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B2013083 : Blo 2011435 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B4299437 : Blo 2011435 4299437 := bbase (se 3 (by rfl) ⟨806144, by rfl⟩ : syracuseStep 4299437 = 1612289) (by norm_num)
theorem B11465165 : Blo 2011435 11465165 := bstep (se 3 (by rfl) ⟨2149718, by rfl⟩ : syracuseStep 11465165 = 4299437) B4299437
theorem B7643443 : Blo 2011435 7643443 := bstep (se 1 (by rfl) ⟨5732582, by rfl⟩ : syracuseStep 7643443 = 11465165) B11465165
theorem B10191257 : Blo 2011435 10191257 := bstep (se 2 (by rfl) ⟨3821721, by rfl⟩ : syracuseStep 10191257 = 7643443) B7643443
theorem B6794171 : Blo 2011435 6794171 := bstep (se 1 (by rfl) ⟨5095628, by rfl⟩ : syracuseStep 6794171 = 10191257) B10191257
theorem B4529447 : Blo 2011435 4529447 := bstep (se 1 (by rfl) ⟨3397085, by rfl⟩ : syracuseStep 4529447 = 6794171) B6794171
theorem B3019631 : Blo 2011435 3019631 := bstep (se 1 (by rfl) ⟨2264723, by rfl⟩ : syracuseStep 3019631 = 4529447) B4529447
theorem B2013087 : Blo 2011435 2013087 := bstep (se 1 (by rfl) ⟨1509815, by rfl⟩ : syracuseStep 2013087 = 3019631) B3019631
theorem B3019637 : Blo 2011435 3019637 := bbase (se 5 (by rfl) ⟨141545, by rfl⟩ : syracuseStep 3019637 = 283091) (by norm_num)
theorem B2013091 : Blo 2011435 2013091 := bstep (se 1 (by rfl) ⟨1509818, by rfl⟩ : syracuseStep 2013091 = 3019637) B3019637
theorem B5165173 : Blo 2011435 5165173 := bbase (se 5 (by rfl) ⟨242117, by rfl⟩ : syracuseStep 5165173 = 484235) (by norm_num)
theorem B27547589 : Blo 2011435 27547589 := bstep (se 4 (by rfl) ⟨2582586, by rfl⟩ : syracuseStep 27547589 = 5165173) B5165173
theorem B18365059 : Blo 2011435 18365059 := bstep (se 1 (by rfl) ⟨13773794, by rfl⟩ : syracuseStep 18365059 = 27547589) B27547589
theorem B24486745 : Blo 2011435 24486745 := bstep (se 2 (by rfl) ⟨9182529, by rfl⟩ : syracuseStep 24486745 = 18365059) B18365059
theorem B32648993 : Blo 2011435 32648993 := bstep (se 2 (by rfl) ⟨12243372, by rfl⟩ : syracuseStep 32648993 = 24486745) B24486745
theorem B21765995 : Blo 2011435 21765995 := bstep (se 1 (by rfl) ⟨16324496, by rfl⟩ : syracuseStep 21765995 = 32648993) B32648993
theorem B14510663 : Blo 2011435 14510663 := bstep (se 1 (by rfl) ⟨10882997, by rfl⟩ : syracuseStep 14510663 = 21765995) B21765995
theorem B9673775 : Blo 2011435 9673775 := bstep (se 1 (by rfl) ⟨7255331, by rfl⟩ : syracuseStep 9673775 = 14510663) B14510663
theorem B6449183 : Blo 2011435 6449183 := bstep (se 1 (by rfl) ⟨4836887, by rfl⟩ : syracuseStep 6449183 = 9673775) B9673775
theorem B4299455 : Blo 2011435 4299455 := bstep (se 1 (by rfl) ⟨3224591, by rfl⟩ : syracuseStep 4299455 = 6449183) B6449183
theorem B2866303 : Blo 2011435 2866303 := bstep (se 1 (by rfl) ⟨2149727, by rfl⟩ : syracuseStep 2866303 = 4299455) B4299455
theorem B3821737 : Blo 2011435 3821737 := bstep (se 2 (by rfl) ⟨1433151, by rfl⟩ : syracuseStep 3821737 = 2866303) B2866303
theorem B5095649 : Blo 2011435 5095649 := bstep (se 2 (by rfl) ⟨1910868, by rfl⟩ : syracuseStep 5095649 = 3821737) B3821737
theorem B3397099 : Blo 2011435 3397099 := bstep (se 1 (by rfl) ⟨2547824, by rfl⟩ : syracuseStep 3397099 = 5095649) B5095649
theorem B4529465 : Blo 2011435 4529465 := bstep (se 2 (by rfl) ⟨1698549, by rfl⟩ : syracuseStep 4529465 = 3397099) B3397099
theorem B3019643 : Blo 2011435 3019643 := bstep (se 1 (by rfl) ⟨2264732, by rfl⟩ : syracuseStep 3019643 = 4529465) B4529465
theorem B2013095 : Blo 2011435 2013095 := bstep (se 1 (by rfl) ⟨1509821, by rfl⟩ : syracuseStep 2013095 = 3019643) B3019643
theorem B2264737 : Blo 2011435 2264737 := bbase (se 2 (by rfl) ⟨849276, by rfl⟩ : syracuseStep 2264737 = 1698553) (by norm_num)
theorem B3019649 : Blo 2011435 3019649 := bstep (se 2 (by rfl) ⟨1132368, by rfl⟩ : syracuseStep 3019649 = 2264737) B2264737
theorem B2013099 : Blo 2011435 2013099 := bstep (se 1 (by rfl) ⟨1509824, by rfl⟩ : syracuseStep 2013099 = 3019649) B3019649
theorem B5095669 : Blo 2011435 5095669 := bbase (se 5 (by rfl) ⟨238859, by rfl⟩ : syracuseStep 5095669 = 477719) (by norm_num)
theorem B6794225 : Blo 2011435 6794225 := bstep (se 2 (by rfl) ⟨2547834, by rfl⟩ : syracuseStep 6794225 = 5095669) B5095669
theorem B4529483 : Blo 2011435 4529483 := bstep (se 1 (by rfl) ⟨3397112, by rfl⟩ : syracuseStep 4529483 = 6794225) B6794225
theorem B3019655 : Blo 2011435 3019655 := bstep (se 1 (by rfl) ⟨2264741, by rfl⟩ : syracuseStep 3019655 = 4529483) B4529483
theorem B2013103 : Blo 2011435 2013103 := bstep (se 1 (by rfl) ⟨1509827, by rfl⟩ : syracuseStep 2013103 = 3019655) B3019655
theorem B3019661 : Blo 2011435 3019661 := bbase (se 3 (by rfl) ⟨566186, by rfl⟩ : syracuseStep 3019661 = 1132373) (by norm_num)
theorem B2013107 : Blo 2011435 2013107 := bstep (se 1 (by rfl) ⟨1509830, by rfl⟩ : syracuseStep 2013107 = 3019661) B3019661
theorem B4529501 : Blo 2011435 4529501 := bbase (se 3 (by rfl) ⟨849281, by rfl⟩ : syracuseStep 4529501 = 1698563) (by norm_num)
theorem B3019667 : Blo 2011435 3019667 := bstep (se 1 (by rfl) ⟨2264750, by rfl⟩ : syracuseStep 3019667 = 4529501) B4529501
theorem B2013111 : Blo 2011435 2013111 := bstep (se 1 (by rfl) ⟨1509833, by rfl⟩ : syracuseStep 2013111 = 3019667) B3019667
theorem B3397133 : Blo 2011435 3397133 := bbase (se 3 (by rfl) ⟨636962, by rfl⟩ : syracuseStep 3397133 = 1273925) (by norm_num)
theorem B2264755 : Blo 2011435 2264755 := bstep (se 1 (by rfl) ⟨1698566, by rfl⟩ : syracuseStep 2264755 = 3397133) B3397133
theorem B3019673 : Blo 2011435 3019673 := bstep (se 2 (by rfl) ⟨1132377, by rfl⟩ : syracuseStep 3019673 = 2264755) B2264755
theorem B2013115 : Blo 2011435 2013115 := bstep (se 1 (by rfl) ⟨1509836, by rfl⟩ : syracuseStep 2013115 = 3019673) B3019673
theorem B3224629 : Blo 2011435 3224629 := bbase (se 5 (by rfl) ⟨151154, by rfl⟩ : syracuseStep 3224629 = 302309) (by norm_num)
theorem B17198021 : Blo 2011435 17198021 := bstep (se 4 (by rfl) ⟨1612314, by rfl⟩ : syracuseStep 17198021 = 3224629) B3224629
theorem B11465347 : Blo 2011435 11465347 := bstep (se 1 (by rfl) ⟨8599010, by rfl⟩ : syracuseStep 11465347 = 17198021) B17198021
theorem B15287129 : Blo 2011435 15287129 := bstep (se 2 (by rfl) ⟨5732673, by rfl⟩ : syracuseStep 15287129 = 11465347) B11465347
theorem B10191419 : Blo 2011435 10191419 := bstep (se 1 (by rfl) ⟨7643564, by rfl⟩ : syracuseStep 10191419 = 15287129) B15287129
theorem B6794279 : Blo 2011435 6794279 := bstep (se 1 (by rfl) ⟨5095709, by rfl⟩ : syracuseStep 6794279 = 10191419) B10191419
theorem B4529519 : Blo 2011435 4529519 := bstep (se 1 (by rfl) ⟨3397139, by rfl⟩ : syracuseStep 4529519 = 6794279) B6794279
theorem B3019679 : Blo 2011435 3019679 := bstep (se 1 (by rfl) ⟨2264759, by rfl⟩ : syracuseStep 3019679 = 4529519) B4529519
theorem B2013119 : Blo 2011435 2013119 := bstep (se 1 (by rfl) ⟨1509839, by rfl⟩ : syracuseStep 2013119 = 3019679) B3019679
theorem B3019685 : Blo 2011435 3019685 := bbase (se 4 (by rfl) ⟨283095, by rfl⟩ : syracuseStep 3019685 = 566191) (by norm_num)
theorem B2013123 : Blo 2011435 2013123 := bstep (se 1 (by rfl) ⟨1509842, by rfl⟩ : syracuseStep 2013123 = 3019685) B3019685
theorem B2547865 : Blo 2011435 2547865 := bbase (se 2 (by rfl) ⟨955449, by rfl⟩ : syracuseStep 2547865 = 1910899) (by norm_num)
theorem B3397153 : Blo 2011435 3397153 := bstep (se 2 (by rfl) ⟨1273932, by rfl⟩ : syracuseStep 3397153 = 2547865) B2547865
theorem B4529537 : Blo 2011435 4529537 := bstep (se 2 (by rfl) ⟨1698576, by rfl⟩ : syracuseStep 4529537 = 3397153) B3397153
theorem B3019691 : Blo 2011435 3019691 := bstep (se 1 (by rfl) ⟨2264768, by rfl⟩ : syracuseStep 3019691 = 4529537) B4529537
theorem B2013127 : Blo 2011435 2013127 := bstep (se 1 (by rfl) ⟨1509845, by rfl⟩ : syracuseStep 2013127 = 3019691) B3019691
theorem B2264773 : Blo 2011435 2264773 := bbase (se 4 (by rfl) ⟨212322, by rfl⟩ : syracuseStep 2264773 = 424645) (by norm_num)
theorem B3019697 : Blo 2011435 3019697 := bstep (se 2 (by rfl) ⟨1132386, by rfl⟩ : syracuseStep 3019697 = 2264773) B2264773
theorem B2013131 : Blo 2011435 2013131 := bstep (se 1 (by rfl) ⟨1509848, by rfl⟩ : syracuseStep 2013131 = 3019697) B3019697
theorem B3821813 : Blo 2011435 3821813 := bbase (se 5 (by rfl) ⟨179147, by rfl⟩ : syracuseStep 3821813 = 358295) (by norm_num)
theorem B2547875 : Blo 2011435 2547875 := bstep (se 1 (by rfl) ⟨1910906, by rfl⟩ : syracuseStep 2547875 = 3821813) B3821813
theorem B6794333 : Blo 2011435 6794333 := bstep (se 3 (by rfl) ⟨1273937, by rfl⟩ : syracuseStep 6794333 = 2547875) B2547875
theorem B4529555 : Blo 2011435 4529555 := bstep (se 1 (by rfl) ⟨3397166, by rfl⟩ : syracuseStep 4529555 = 6794333) B6794333
theorem B3019703 : Blo 2011435 3019703 := bstep (se 1 (by rfl) ⟨2264777, by rfl⟩ : syracuseStep 3019703 = 4529555) B4529555
theorem B2013135 : Blo 2011435 2013135 := bstep (se 1 (by rfl) ⟨1509851, by rfl⟩ : syracuseStep 2013135 = 3019703) B3019703
theorem B3019709 : Blo 2011435 3019709 := bbase (se 3 (by rfl) ⟨566195, by rfl⟩ : syracuseStep 3019709 = 1132391) (by norm_num)
theorem B2013139 : Blo 2011435 2013139 := bstep (se 1 (by rfl) ⟨1509854, by rfl⟩ : syracuseStep 2013139 = 3019709) B3019709
theorem B4529573 : Blo 2011435 4529573 := bbase (se 4 (by rfl) ⟨424647, by rfl⟩ : syracuseStep 4529573 = 849295) (by norm_num)
theorem B3019715 : Blo 2011435 3019715 := bstep (se 1 (by rfl) ⟨2264786, by rfl⟩ : syracuseStep 3019715 = 4529573) B4529573
theorem B2013143 : Blo 2011435 2013143 := bstep (se 1 (by rfl) ⟨1509857, by rfl⟩ : syracuseStep 2013143 = 3019715) B3019715
theorem B5095781 : Blo 2011435 5095781 := bbase (se 4 (by rfl) ⟨477729, by rfl⟩ : syracuseStep 5095781 = 955459) (by norm_num)
theorem B3397187 : Blo 2011435 3397187 := bstep (se 1 (by rfl) ⟨2547890, by rfl⟩ : syracuseStep 3397187 = 5095781) B5095781
theorem B2264791 : Blo 2011435 2264791 := bstep (se 1 (by rfl) ⟨1698593, by rfl⟩ : syracuseStep 2264791 = 3397187) B3397187
theorem B3019721 : Blo 2011435 3019721 := bstep (se 2 (by rfl) ⟨1132395, by rfl⟩ : syracuseStep 3019721 = 2264791) B2264791
theorem B2013147 : Blo 2011435 2013147 := bstep (se 1 (by rfl) ⟨1509860, by rfl⟩ : syracuseStep 2013147 = 3019721) B3019721
theorem B2295697 : Blo 2011435 2295697 := bbase (se 2 (by rfl) ⟨860886, by rfl⟩ : syracuseStep 2295697 = 1721773) (by norm_num)
theorem B3060929 : Blo 2011435 3060929 := bstep (se 2 (by rfl) ⟨1147848, by rfl⟩ : syracuseStep 3060929 = 2295697) B2295697
theorem B8162477 : Blo 2011435 8162477 := bstep (se 3 (by rfl) ⟨1530464, by rfl⟩ : syracuseStep 8162477 = 3060929) B3060929
theorem B5441651 : Blo 2011435 5441651 := bstep (se 1 (by rfl) ⟨4081238, by rfl⟩ : syracuseStep 5441651 = 8162477) B8162477
theorem B3627767 : Blo 2011435 3627767 := bstep (se 1 (by rfl) ⟨2720825, by rfl⟩ : syracuseStep 3627767 = 5441651) B5441651
theorem B2418511 : Blo 2011435 2418511 := bstep (se 1 (by rfl) ⟨1813883, by rfl⟩ : syracuseStep 2418511 = 3627767) B3627767
theorem B3224681 : Blo 2011435 3224681 := bstep (se 2 (by rfl) ⟨1209255, by rfl⟩ : syracuseStep 3224681 = 2418511) B2418511
theorem B2149787 : Blo 2011435 2149787 := bstep (se 1 (by rfl) ⟨1612340, by rfl⟩ : syracuseStep 2149787 = 3224681) B3224681
theorem B5732765 : Blo 2011435 5732765 := bstep (se 3 (by rfl) ⟨1074893, by rfl⟩ : syracuseStep 5732765 = 2149787) B2149787
theorem B3821843 : Blo 2011435 3821843 := bstep (se 1 (by rfl) ⟨2866382, by rfl⟩ : syracuseStep 3821843 = 5732765) B5732765
theorem B10191581 : Blo 2011435 10191581 := bstep (se 3 (by rfl) ⟨1910921, by rfl⟩ : syracuseStep 10191581 = 3821843) B3821843
theorem B6794387 : Blo 2011435 6794387 := bstep (se 1 (by rfl) ⟨5095790, by rfl⟩ : syracuseStep 6794387 = 10191581) B10191581
theorem B4529591 : Blo 2011435 4529591 := bstep (se 1 (by rfl) ⟨3397193, by rfl⟩ : syracuseStep 4529591 = 6794387) B6794387
theorem B3019727 : Blo 2011435 3019727 := bstep (se 1 (by rfl) ⟨2264795, by rfl⟩ : syracuseStep 3019727 = 4529591) B4529591
theorem B2013151 : Blo 2011435 2013151 := bstep (se 1 (by rfl) ⟨1509863, by rfl⟩ : syracuseStep 2013151 = 3019727) B3019727
theorem B3019733 : Blo 2011435 3019733 := bbase (se 7 (by rfl) ⟨35387, by rfl⟩ : syracuseStep 3019733 = 70775) (by norm_num)
theorem B2013155 : Blo 2011435 2013155 := bstep (se 1 (by rfl) ⟨1509866, by rfl⟩ : syracuseStep 2013155 = 3019733) B3019733
theorem B7643717 : Blo 2011435 7643717 := bbase (se 4 (by rfl) ⟨716598, by rfl⟩ : syracuseStep 7643717 = 1433197) (by norm_num)
theorem B5095811 : Blo 2011435 5095811 := bstep (se 1 (by rfl) ⟨3821858, by rfl⟩ : syracuseStep 5095811 = 7643717) B7643717
theorem B3397207 : Blo 2011435 3397207 := bstep (se 1 (by rfl) ⟨2547905, by rfl⟩ : syracuseStep 3397207 = 5095811) B5095811
theorem B4529609 : Blo 2011435 4529609 := bstep (se 2 (by rfl) ⟨1698603, by rfl⟩ : syracuseStep 4529609 = 3397207) B3397207
theorem B3019739 : Blo 2011435 3019739 := bstep (se 1 (by rfl) ⟨2264804, by rfl⟩ : syracuseStep 3019739 = 4529609) B4529609
theorem B2013159 : Blo 2011435 2013159 := bstep (se 1 (by rfl) ⟨1509869, by rfl⟩ : syracuseStep 2013159 = 3019739) B3019739
theorem B2264809 : Blo 2011435 2264809 := bbase (se 2 (by rfl) ⟨849303, by rfl⟩ : syracuseStep 2264809 = 1698607) (by norm_num)
theorem B3019745 : Blo 2011435 3019745 := bstep (se 2 (by rfl) ⟨1132404, by rfl⟩ : syracuseStep 3019745 = 2264809) B2264809
theorem B2013163 : Blo 2011435 2013163 := bstep (se 1 (by rfl) ⟨1509872, by rfl⟩ : syracuseStep 2013163 = 3019745) B3019745
theorem B11465621 : Blo 2011435 11465621 := bbase (se 6 (by rfl) ⟨268725, by rfl⟩ : syracuseStep 11465621 = 537451) (by norm_num)
theorem B7643747 : Blo 2011435 7643747 := bstep (se 1 (by rfl) ⟨5732810, by rfl⟩ : syracuseStep 7643747 = 11465621) B11465621
theorem B5095831 : Blo 2011435 5095831 := bstep (se 1 (by rfl) ⟨3821873, by rfl⟩ : syracuseStep 5095831 = 7643747) B7643747
theorem B6794441 : Blo 2011435 6794441 := bstep (se 2 (by rfl) ⟨2547915, by rfl⟩ : syracuseStep 6794441 = 5095831) B5095831
theorem B4529627 : Blo 2011435 4529627 := bstep (se 1 (by rfl) ⟨3397220, by rfl⟩ : syracuseStep 4529627 = 6794441) B6794441
theorem B3019751 : Blo 2011435 3019751 := bstep (se 1 (by rfl) ⟨2264813, by rfl⟩ : syracuseStep 3019751 = 4529627) B4529627
theorem B2013167 : Blo 2011435 2013167 := bstep (se 1 (by rfl) ⟨1509875, by rfl⟩ : syracuseStep 2013167 = 3019751) B3019751
theorem B3019757 : Blo 2011435 3019757 := bbase (se 3 (by rfl) ⟨566204, by rfl⟩ : syracuseStep 3019757 = 1132409) (by norm_num)
theorem B2013171 : Blo 2011435 2013171 := bstep (se 1 (by rfl) ⟨1509878, by rfl⟩ : syracuseStep 2013171 = 3019757) B3019757
theorem B4529645 : Blo 2011435 4529645 := bbase (se 3 (by rfl) ⟨849308, by rfl⟩ : syracuseStep 4529645 = 1698617) (by norm_num)
theorem B3019763 : Blo 2011435 3019763 := bstep (se 1 (by rfl) ⟨2264822, by rfl⟩ : syracuseStep 3019763 = 4529645) B4529645
theorem B2013175 : Blo 2011435 2013175 := bstep (se 1 (by rfl) ⟨1509881, by rfl⟩ : syracuseStep 2013175 = 3019763) B3019763
theorem B2418545 : Blo 2011435 2418545 := bbase (se 2 (by rfl) ⟨906954, by rfl⟩ : syracuseStep 2418545 = 1813909) (by norm_num)
theorem B6449453 : Blo 2011435 6449453 := bstep (se 3 (by rfl) ⟨1209272, by rfl⟩ : syracuseStep 6449453 = 2418545) B2418545
theorem B4299635 : Blo 2011435 4299635 := bstep (se 1 (by rfl) ⟨3224726, by rfl⟩ : syracuseStep 4299635 = 6449453) B6449453
theorem B2866423 : Blo 2011435 2866423 := bstep (se 1 (by rfl) ⟨2149817, by rfl⟩ : syracuseStep 2866423 = 4299635) B4299635
theorem B3821897 : Blo 2011435 3821897 := bstep (se 2 (by rfl) ⟨1433211, by rfl⟩ : syracuseStep 3821897 = 2866423) B2866423
theorem B2547931 : Blo 2011435 2547931 := bstep (se 1 (by rfl) ⟨1910948, by rfl⟩ : syracuseStep 2547931 = 3821897) B3821897
theorem B3397241 : Blo 2011435 3397241 := bstep (se 2 (by rfl) ⟨1273965, by rfl⟩ : syracuseStep 3397241 = 2547931) B2547931
theorem B2264827 : Blo 2011435 2264827 := bstep (se 1 (by rfl) ⟨1698620, by rfl⟩ : syracuseStep 2264827 = 3397241) B3397241
theorem B3019769 : Blo 2011435 3019769 := bstep (se 2 (by rfl) ⟨1132413, by rfl⟩ : syracuseStep 3019769 = 2264827) B2264827
theorem B2013179 : Blo 2011435 2013179 := bstep (se 1 (by rfl) ⟨1509884, by rfl⟩ : syracuseStep 2013179 = 3019769) B3019769
theorem B14345909 : Blo 2011435 14345909 := bbase (se 5 (by rfl) ⟨672464, by rfl⟩ : syracuseStep 14345909 = 1344929) (by norm_num)
theorem B9563939 : Blo 2011435 9563939 := bstep (se 1 (by rfl) ⟨7172954, by rfl⟩ : syracuseStep 9563939 = 14345909) B14345909
theorem B6375959 : Blo 2011435 6375959 := bstep (se 1 (by rfl) ⟨4781969, by rfl⟩ : syracuseStep 6375959 = 9563939) B9563939
theorem B4250639 : Blo 2011435 4250639 := bstep (se 1 (by rfl) ⟨3187979, by rfl⟩ : syracuseStep 4250639 = 6375959) B6375959
theorem B2833759 : Blo 2011435 2833759 := bstep (se 1 (by rfl) ⟨2125319, by rfl⟩ : syracuseStep 2833759 = 4250639) B4250639
theorem B3778345 : Blo 2011435 3778345 := bstep (se 2 (by rfl) ⟨1416879, by rfl⟩ : syracuseStep 3778345 = 2833759) B2833759
theorem B20151173 : Blo 2011435 20151173 := bstep (se 4 (by rfl) ⟨1889172, by rfl⟩ : syracuseStep 20151173 = 3778345) B3778345
theorem B13434115 : Blo 2011435 13434115 := bstep (se 1 (by rfl) ⟨10075586, by rfl⟩ : syracuseStep 13434115 = 20151173) B20151173
theorem B286594453 : Blo 2011435 286594453 := bstep (se 6 (by rfl) ⟨6717057, by rfl⟩ : syracuseStep 286594453 = 13434115) B13434115
theorem B382125937 : Blo 2011435 382125937 := bstep (se 2 (by rfl) ⟨143297226, by rfl⟩ : syracuseStep 382125937 = 286594453) B286594453
theorem B509501249 : Blo 2011435 509501249 := bstep (se 2 (by rfl) ⟨191062968, by rfl⟩ : syracuseStep 509501249 = 382125937) B382125937
theorem B339667499 : Blo 2011435 339667499 := bstep (se 1 (by rfl) ⟨254750624, by rfl⟩ : syracuseStep 339667499 = 509501249) B509501249
theorem B226444999 : Blo 2011435 226444999 := bstep (se 1 (by rfl) ⟨169833749, by rfl⟩ : syracuseStep 226444999 = 339667499) B339667499
theorem B301926665 : Blo 2011435 301926665 := bstep (se 2 (by rfl) ⟨113222499, by rfl⟩ : syracuseStep 301926665 = 226444999) B226444999
theorem B201284443 : Blo 2011435 201284443 := bstep (se 1 (by rfl) ⟨150963332, by rfl⟩ : syracuseStep 201284443 = 301926665) B301926665
theorem B268379257 : Blo 2011435 268379257 := bstep (se 2 (by rfl) ⟨100642221, by rfl⟩ : syracuseStep 268379257 = 201284443) B201284443
theorem B357839009 : Blo 2011435 357839009 := bstep (se 2 (by rfl) ⟨134189628, by rfl⟩ : syracuseStep 357839009 = 268379257) B268379257
theorem B238559339 : Blo 2011435 238559339 := bstep (se 1 (by rfl) ⟨178919504, by rfl⟩ : syracuseStep 238559339 = 357839009) B357839009
theorem B159039559 : Blo 2011435 159039559 := bstep (se 1 (by rfl) ⟨119279669, by rfl⟩ : syracuseStep 159039559 = 238559339) B238559339
theorem B212052745 : Blo 2011435 212052745 := bstep (se 2 (by rfl) ⟨79519779, by rfl⟩ : syracuseStep 212052745 = 159039559) B159039559
theorem B282736993 : Blo 2011435 282736993 := bstep (se 2 (by rfl) ⟨106026372, by rfl⟩ : syracuseStep 282736993 = 212052745) B212052745
theorem B376982657 : Blo 2011435 376982657 := bstep (se 2 (by rfl) ⟨141368496, by rfl⟩ : syracuseStep 376982657 = 282736993) B282736993
theorem B251321771 : Blo 2011435 251321771 := bstep (se 1 (by rfl) ⟨188491328, by rfl⟩ : syracuseStep 251321771 = 376982657) B376982657
theorem B167547847 : Blo 2011435 167547847 := bstep (se 1 (by rfl) ⟨125660885, by rfl⟩ : syracuseStep 167547847 = 251321771) B251321771
theorem B223397129 : Blo 2011435 223397129 := bstep (se 2 (by rfl) ⟨83773923, by rfl⟩ : syracuseStep 223397129 = 167547847) B167547847
theorem B148931419 : Blo 2011435 148931419 := bstep (se 1 (by rfl) ⟨111698564, by rfl⟩ : syracuseStep 148931419 = 223397129) B223397129
theorem B198575225 : Blo 2011435 198575225 := bstep (se 2 (by rfl) ⟨74465709, by rfl⟩ : syracuseStep 198575225 = 148931419) B148931419
theorem B132383483 : Blo 2011435 132383483 := bstep (se 1 (by rfl) ⟨99287612, by rfl⟩ : syracuseStep 132383483 = 198575225) B198575225
theorem B88255655 : Blo 2011435 88255655 := bstep (se 1 (by rfl) ⟨66191741, by rfl⟩ : syracuseStep 88255655 = 132383483) B132383483
theorem B58837103 : Blo 2011435 58837103 := bstep (se 1 (by rfl) ⟨44127827, by rfl⟩ : syracuseStep 58837103 = 88255655) B88255655
theorem B39224735 : Blo 2011435 39224735 := bstep (se 1 (by rfl) ⟨29418551, by rfl⟩ : syracuseStep 39224735 = 58837103) B58837103
theorem B26149823 : Blo 2011435 26149823 := bstep (se 1 (by rfl) ⟨19612367, by rfl⟩ : syracuseStep 26149823 = 39224735) B39224735
theorem B17433215 : Blo 2011435 17433215 := bstep (se 1 (by rfl) ⟨13074911, by rfl⟩ : syracuseStep 17433215 = 26149823) B26149823
theorem B11622143 : Blo 2011435 11622143 := bstep (se 1 (by rfl) ⟨8716607, by rfl⟩ : syracuseStep 11622143 = 17433215) B17433215
theorem B30992381 : Blo 2011435 30992381 := bstep (se 3 (by rfl) ⟨5811071, by rfl⟩ : syracuseStep 30992381 = 11622143) B11622143
theorem B20661587 : Blo 2011435 20661587 := bstep (se 1 (by rfl) ⟨15496190, by rfl⟩ : syracuseStep 20661587 = 30992381) B30992381
theorem B13774391 : Blo 2011435 13774391 := bstep (se 1 (by rfl) ⟨10330793, by rfl⟩ : syracuseStep 13774391 = 20661587) B20661587
theorem B9182927 : Blo 2011435 9182927 := bstep (se 1 (by rfl) ⟨6887195, by rfl⟩ : syracuseStep 9182927 = 13774391) B13774391
theorem B24487805 : Blo 2011435 24487805 := bstep (se 3 (by rfl) ⟨4591463, by rfl⟩ : syracuseStep 24487805 = 9182927) B9182927
theorem B65300813 : Blo 2011435 65300813 := bstep (se 3 (by rfl) ⟨12243902, by rfl⟩ : syracuseStep 65300813 = 24487805) B24487805
theorem B43533875 : Blo 2011435 43533875 := bstep (se 1 (by rfl) ⟨32650406, by rfl⟩ : syracuseStep 43533875 = 65300813) B65300813
theorem B116090333 : Blo 2011435 116090333 := bstep (se 3 (by rfl) ⟨21766937, by rfl⟩ : syracuseStep 116090333 = 43533875) B43533875
theorem B77393555 : Blo 2011435 77393555 := bstep (se 1 (by rfl) ⟨58045166, by rfl⟩ : syracuseStep 77393555 = 116090333) B116090333
theorem B51595703 : Blo 2011435 51595703 := bstep (se 1 (by rfl) ⟨38696777, by rfl⟩ : syracuseStep 51595703 = 77393555) B77393555
theorem B34397135 : Blo 2011435 34397135 := bstep (se 1 (by rfl) ⟨25797851, by rfl⟩ : syracuseStep 34397135 = 51595703) B51595703
theorem B22931423 : Blo 2011435 22931423 := bstep (se 1 (by rfl) ⟨17198567, by rfl⟩ : syracuseStep 22931423 = 34397135) B34397135
theorem B15287615 : Blo 2011435 15287615 := bstep (se 1 (by rfl) ⟨11465711, by rfl⟩ : syracuseStep 15287615 = 22931423) B22931423
theorem B10191743 : Blo 2011435 10191743 := bstep (se 1 (by rfl) ⟨7643807, by rfl⟩ : syracuseStep 10191743 = 15287615) B15287615
theorem B6794495 : Blo 2011435 6794495 := bstep (se 1 (by rfl) ⟨5095871, by rfl⟩ : syracuseStep 6794495 = 10191743) B10191743
theorem B4529663 : Blo 2011435 4529663 := bstep (se 1 (by rfl) ⟨3397247, by rfl⟩ : syracuseStep 4529663 = 6794495) B6794495
theorem B3019775 : Blo 2011435 3019775 := bstep (se 1 (by rfl) ⟨2264831, by rfl⟩ : syracuseStep 3019775 = 4529663) B4529663
theorem B2013183 : Blo 2011435 2013183 := bstep (se 1 (by rfl) ⟨1509887, by rfl⟩ : syracuseStep 2013183 = 3019775) B3019775
theorem B3019781 : Blo 2011435 3019781 := bbase (se 4 (by rfl) ⟨283104, by rfl⟩ : syracuseStep 3019781 = 566209) (by norm_num)
theorem B2013187 : Blo 2011435 2013187 := bstep (se 1 (by rfl) ⟨1509890, by rfl⟩ : syracuseStep 2013187 = 3019781) B3019781
theorem B3397261 : Blo 2011435 3397261 := bbase (se 3 (by rfl) ⟨636986, by rfl⟩ : syracuseStep 3397261 = 1273973) (by norm_num)
theorem B4529681 : Blo 2011435 4529681 := bstep (se 2 (by rfl) ⟨1698630, by rfl⟩ : syracuseStep 4529681 = 3397261) B3397261
theorem B3019787 : Blo 2011435 3019787 := bstep (se 1 (by rfl) ⟨2264840, by rfl⟩ : syracuseStep 3019787 = 4529681) B4529681
theorem B2013191 : Blo 2011435 2013191 := bstep (se 1 (by rfl) ⟨1509893, by rfl⟩ : syracuseStep 2013191 = 3019787) B3019787
theorem B2264845 : Blo 2011435 2264845 := bbase (se 3 (by rfl) ⟨424658, by rfl⟩ : syracuseStep 2264845 = 849317) (by norm_num)
theorem B3019793 : Blo 2011435 3019793 := bstep (se 2 (by rfl) ⟨1132422, by rfl⟩ : syracuseStep 3019793 = 2264845) B2264845
theorem B2013195 : Blo 2011435 2013195 := bstep (se 1 (by rfl) ⟨1509896, by rfl⟩ : syracuseStep 2013195 = 3019793) B3019793
theorem B6794549 : Blo 2011435 6794549 := bbase (se 5 (by rfl) ⟨318494, by rfl⟩ : syracuseStep 6794549 = 636989) (by norm_num)
theorem B4529699 : Blo 2011435 4529699 := bstep (se 1 (by rfl) ⟨3397274, by rfl⟩ : syracuseStep 4529699 = 6794549) B6794549
theorem B3019799 : Blo 2011435 3019799 := bstep (se 1 (by rfl) ⟨2264849, by rfl⟩ : syracuseStep 3019799 = 4529699) B4529699
theorem B2013199 : Blo 2011435 2013199 := bstep (se 1 (by rfl) ⟨1509899, by rfl⟩ : syracuseStep 2013199 = 3019799) B3019799
theorem B3019805 : Blo 2011435 3019805 := bbase (se 3 (by rfl) ⟨566213, by rfl⟩ : syracuseStep 3019805 = 1132427) (by norm_num)
theorem B2013203 : Blo 2011435 2013203 := bstep (se 1 (by rfl) ⟨1509902, by rfl⟩ : syracuseStep 2013203 = 3019805) B3019805
theorem B4529717 : Blo 2011435 4529717 := bbase (se 5 (by rfl) ⟨212330, by rfl⟩ : syracuseStep 4529717 = 424661) (by norm_num)
theorem B3019811 : Blo 2011435 3019811 := bstep (se 1 (by rfl) ⟨2264858, by rfl⟩ : syracuseStep 3019811 = 4529717) B4529717
theorem B2013207 : Blo 2011435 2013207 := bstep (se 1 (by rfl) ⟨1509905, by rfl⟩ : syracuseStep 2013207 = 3019811) B3019811
theorem B5441813 : Blo 2011435 5441813 := bbase (se 6 (by rfl) ⟨127542, by rfl⟩ : syracuseStep 5441813 = 255085) (by norm_num)
theorem B3627875 : Blo 2011435 3627875 := bstep (se 1 (by rfl) ⟨2720906, by rfl⟩ : syracuseStep 3627875 = 5441813) B5441813
theorem B2418583 : Blo 2011435 2418583 := bstep (se 1 (by rfl) ⟨1813937, by rfl⟩ : syracuseStep 2418583 = 3627875) B3627875
theorem B3224777 : Blo 2011435 3224777 := bstep (se 2 (by rfl) ⟨1209291, by rfl⟩ : syracuseStep 3224777 = 2418583) B2418583
theorem B8599405 : Blo 2011435 8599405 := bstep (se 3 (by rfl) ⟨1612388, by rfl⟩ : syracuseStep 8599405 = 3224777) B3224777
theorem B11465873 : Blo 2011435 11465873 := bstep (se 2 (by rfl) ⟨4299702, by rfl⟩ : syracuseStep 11465873 = 8599405) B8599405
theorem B7643915 : Blo 2011435 7643915 := bstep (se 1 (by rfl) ⟨5732936, by rfl⟩ : syracuseStep 7643915 = 11465873) B11465873
theorem B5095943 : Blo 2011435 5095943 := bstep (se 1 (by rfl) ⟨3821957, by rfl⟩ : syracuseStep 5095943 = 7643915) B7643915
theorem B3397295 : Blo 2011435 3397295 := bstep (se 1 (by rfl) ⟨2547971, by rfl⟩ : syracuseStep 3397295 = 5095943) B5095943
theorem B2264863 : Blo 2011435 2264863 := bstep (se 1 (by rfl) ⟨1698647, by rfl⟩ : syracuseStep 2264863 = 3397295) B3397295
theorem B3019817 : Blo 2011435 3019817 := bstep (se 2 (by rfl) ⟨1132431, by rfl⟩ : syracuseStep 3019817 = 2264863) B2264863
theorem B2013211 : Blo 2011435 2013211 := bstep (se 1 (by rfl) ⟨1509908, by rfl⟩ : syracuseStep 2013211 = 3019817) B3019817
theorem B9183077 : Blo 2011435 9183077 := bbase (se 4 (by rfl) ⟨860913, by rfl⟩ : syracuseStep 9183077 = 1721827) (by norm_num)
theorem B6122051 : Blo 2011435 6122051 := bstep (se 1 (by rfl) ⟨4591538, by rfl⟩ : syracuseStep 6122051 = 9183077) B9183077
theorem B4081367 : Blo 2011435 4081367 := bstep (se 1 (by rfl) ⟨3061025, by rfl⟩ : syracuseStep 4081367 = 6122051) B6122051
theorem B10883645 : Blo 2011435 10883645 := bstep (se 3 (by rfl) ⟨2040683, by rfl⟩ : syracuseStep 10883645 = 4081367) B4081367
theorem B7255763 : Blo 2011435 7255763 := bstep (se 1 (by rfl) ⟨5441822, by rfl⟩ : syracuseStep 7255763 = 10883645) B10883645
theorem B4837175 : Blo 2011435 4837175 := bstep (se 1 (by rfl) ⟨3627881, by rfl⟩ : syracuseStep 4837175 = 7255763) B7255763
theorem B3224783 : Blo 2011435 3224783 := bstep (se 1 (by rfl) ⟨2418587, by rfl⟩ : syracuseStep 3224783 = 4837175) B4837175
theorem B8599421 : Blo 2011435 8599421 := bstep (se 3 (by rfl) ⟨1612391, by rfl⟩ : syracuseStep 8599421 = 3224783) B3224783
theorem B5732947 : Blo 2011435 5732947 := bstep (se 1 (by rfl) ⟨4299710, by rfl⟩ : syracuseStep 5732947 = 8599421) B8599421
theorem B7643929 : Blo 2011435 7643929 := bstep (se 2 (by rfl) ⟨2866473, by rfl⟩ : syracuseStep 7643929 = 5732947) B5732947
theorem B10191905 : Blo 2011435 10191905 := bstep (se 2 (by rfl) ⟨3821964, by rfl⟩ : syracuseStep 10191905 = 7643929) B7643929
theorem B6794603 : Blo 2011435 6794603 := bstep (se 1 (by rfl) ⟨5095952, by rfl⟩ : syracuseStep 6794603 = 10191905) B10191905
theorem B4529735 : Blo 2011435 4529735 := bstep (se 1 (by rfl) ⟨3397301, by rfl⟩ : syracuseStep 4529735 = 6794603) B6794603
theorem B3019823 : Blo 2011435 3019823 := bstep (se 1 (by rfl) ⟨2264867, by rfl⟩ : syracuseStep 3019823 = 4529735) B4529735
theorem B2013215 : Blo 2011435 2013215 := bstep (se 1 (by rfl) ⟨1509911, by rfl⟩ : syracuseStep 2013215 = 3019823) B3019823
theorem B3019829 : Blo 2011435 3019829 := bbase (se 5 (by rfl) ⟨141554, by rfl⟩ : syracuseStep 3019829 = 283109) (by norm_num)
theorem B2013219 : Blo 2011435 2013219 := bstep (se 1 (by rfl) ⟨1509914, by rfl⟩ : syracuseStep 2013219 = 3019829) B3019829
theorem B5095973 : Blo 2011435 5095973 := bbase (se 4 (by rfl) ⟨477747, by rfl⟩ : syracuseStep 5095973 = 955495) (by norm_num)
theorem B3397315 : Blo 2011435 3397315 := bstep (se 1 (by rfl) ⟨2547986, by rfl⟩ : syracuseStep 3397315 = 5095973) B5095973
theorem B4529753 : Blo 2011435 4529753 := bstep (se 2 (by rfl) ⟨1698657, by rfl⟩ : syracuseStep 4529753 = 3397315) B3397315
theorem B3019835 : Blo 2011435 3019835 := bstep (se 1 (by rfl) ⟨2264876, by rfl⟩ : syracuseStep 3019835 = 4529753) B4529753
theorem B2013223 : Blo 2011435 2013223 := bstep (se 1 (by rfl) ⟨1509917, by rfl⟩ : syracuseStep 2013223 = 3019835) B3019835
theorem B2264881 : Blo 2011435 2264881 := bbase (se 2 (by rfl) ⟨849330, by rfl⟩ : syracuseStep 2264881 = 1698661) (by norm_num)
theorem B3019841 : Blo 2011435 3019841 := bstep (se 2 (by rfl) ⟨1132440, by rfl⟩ : syracuseStep 3019841 = 2264881) B2264881
theorem B2013227 : Blo 2011435 2013227 := bstep (se 1 (by rfl) ⟨1509920, by rfl⟩ : syracuseStep 2013227 = 3019841) B3019841
theorem B6122101 : Blo 2011435 6122101 := bbase (se 5 (by rfl) ⟨286973, by rfl⟩ : syracuseStep 6122101 = 573947) (by norm_num)
theorem B8162801 : Blo 2011435 8162801 := bstep (se 2 (by rfl) ⟨3061050, by rfl⟩ : syracuseStep 8162801 = 6122101) B6122101
theorem B5441867 : Blo 2011435 5441867 := bstep (se 1 (by rfl) ⟨4081400, by rfl⟩ : syracuseStep 5441867 = 8162801) B8162801
theorem B3627911 : Blo 2011435 3627911 := bstep (se 1 (by rfl) ⟨2720933, by rfl⟩ : syracuseStep 3627911 = 5441867) B5441867
theorem B2418607 : Blo 2011435 2418607 := bstep (se 1 (by rfl) ⟨1813955, by rfl⟩ : syracuseStep 2418607 = 3627911) B3627911
theorem B3224809 : Blo 2011435 3224809 := bstep (se 2 (by rfl) ⟨1209303, by rfl⟩ : syracuseStep 3224809 = 2418607) B2418607
theorem B4299745 : Blo 2011435 4299745 := bstep (se 2 (by rfl) ⟨1612404, by rfl⟩ : syracuseStep 4299745 = 3224809) B3224809
theorem B5732993 : Blo 2011435 5732993 := bstep (se 2 (by rfl) ⟨2149872, by rfl⟩ : syracuseStep 5732993 = 4299745) B4299745
theorem B3821995 : Blo 2011435 3821995 := bstep (se 1 (by rfl) ⟨2866496, by rfl⟩ : syracuseStep 3821995 = 5732993) B5732993
theorem B5095993 : Blo 2011435 5095993 := bstep (se 2 (by rfl) ⟨1910997, by rfl⟩ : syracuseStep 5095993 = 3821995) B3821995
theorem B6794657 : Blo 2011435 6794657 := bstep (se 2 (by rfl) ⟨2547996, by rfl⟩ : syracuseStep 6794657 = 5095993) B5095993
theorem B4529771 : Blo 2011435 4529771 := bstep (se 1 (by rfl) ⟨3397328, by rfl⟩ : syracuseStep 4529771 = 6794657) B6794657
theorem B3019847 : Blo 2011435 3019847 := bstep (se 1 (by rfl) ⟨2264885, by rfl⟩ : syracuseStep 3019847 = 4529771) B4529771
theorem B2013231 : Blo 2011435 2013231 := bstep (se 1 (by rfl) ⟨1509923, by rfl⟩ : syracuseStep 2013231 = 3019847) B3019847
theorem B3019853 : Blo 2011435 3019853 := bbase (se 3 (by rfl) ⟨566222, by rfl⟩ : syracuseStep 3019853 = 1132445) (by norm_num)
theorem B2013235 : Blo 2011435 2013235 := bstep (se 1 (by rfl) ⟨1509926, by rfl⟩ : syracuseStep 2013235 = 3019853) B3019853
theorem B4529789 : Blo 2011435 4529789 := bbase (se 3 (by rfl) ⟨849335, by rfl⟩ : syracuseStep 4529789 = 1698671) (by norm_num)
theorem B3019859 : Blo 2011435 3019859 := bstep (se 1 (by rfl) ⟨2264894, by rfl⟩ : syracuseStep 3019859 = 4529789) B4529789
theorem B2013239 : Blo 2011435 2013239 := bstep (se 1 (by rfl) ⟨1509929, by rfl⟩ : syracuseStep 2013239 = 3019859) B3019859
theorem B3397349 : Blo 2011435 3397349 := bbase (se 4 (by rfl) ⟨318501, by rfl⟩ : syracuseStep 3397349 = 637003) (by norm_num)
theorem B2264899 : Blo 2011435 2264899 := bstep (se 1 (by rfl) ⟨1698674, by rfl⟩ : syracuseStep 2264899 = 3397349) B3397349
theorem B3019865 : Blo 2011435 3019865 := bstep (se 2 (by rfl) ⟨1132449, by rfl⟩ : syracuseStep 3019865 = 2264899) B2264899
theorem B2013243 : Blo 2011435 2013243 := bstep (se 1 (by rfl) ⟨1509932, by rfl⟩ : syracuseStep 2013243 = 3019865) B3019865
theorem B6449669 : Blo 2011435 6449669 := bbase (se 4 (by rfl) ⟨604656, by rfl⟩ : syracuseStep 6449669 = 1209313) (by norm_num)
theorem B4299779 : Blo 2011435 4299779 := bstep (se 1 (by rfl) ⟨3224834, by rfl⟩ : syracuseStep 4299779 = 6449669) B6449669
theorem B2866519 : Blo 2011435 2866519 := bstep (se 1 (by rfl) ⟨2149889, by rfl⟩ : syracuseStep 2866519 = 4299779) B4299779
theorem B15288101 : Blo 2011435 15288101 := bstep (se 4 (by rfl) ⟨1433259, by rfl⟩ : syracuseStep 15288101 = 2866519) B2866519
theorem B10192067 : Blo 2011435 10192067 := bstep (se 1 (by rfl) ⟨7644050, by rfl⟩ : syracuseStep 10192067 = 15288101) B15288101
theorem B6794711 : Blo 2011435 6794711 := bstep (se 1 (by rfl) ⟨5096033, by rfl⟩ : syracuseStep 6794711 = 10192067) B10192067
theorem B4529807 : Blo 2011435 4529807 := bstep (se 1 (by rfl) ⟨3397355, by rfl⟩ : syracuseStep 4529807 = 6794711) B6794711
theorem B3019871 : Blo 2011435 3019871 := bstep (se 1 (by rfl) ⟨2264903, by rfl⟩ : syracuseStep 3019871 = 4529807) B4529807
theorem B2013247 : Blo 2011435 2013247 := bstep (se 1 (by rfl) ⟨1509935, by rfl⟩ : syracuseStep 2013247 = 3019871) B3019871
theorem B3019877 : Blo 2011435 3019877 := bbase (se 4 (by rfl) ⟨283113, by rfl⟩ : syracuseStep 3019877 = 566227) (by norm_num)
theorem B2013251 : Blo 2011435 2013251 := bstep (se 1 (by rfl) ⟨1509938, by rfl⟩ : syracuseStep 2013251 = 3019877) B3019877
theorem B4299797 : Blo 2011435 4299797 := bbase (se 6 (by rfl) ⟨100776, by rfl⟩ : syracuseStep 4299797 = 201553) (by norm_num)
theorem B2866531 : Blo 2011435 2866531 := bstep (se 1 (by rfl) ⟨2149898, by rfl⟩ : syracuseStep 2866531 = 4299797) B4299797
theorem B3822041 : Blo 2011435 3822041 := bstep (se 2 (by rfl) ⟨1433265, by rfl⟩ : syracuseStep 3822041 = 2866531) B2866531
theorem B2548027 : Blo 2011435 2548027 := bstep (se 1 (by rfl) ⟨1911020, by rfl⟩ : syracuseStep 2548027 = 3822041) B3822041
theorem B3397369 : Blo 2011435 3397369 := bstep (se 2 (by rfl) ⟨1274013, by rfl⟩ : syracuseStep 3397369 = 2548027) B2548027
theorem B4529825 : Blo 2011435 4529825 := bstep (se 2 (by rfl) ⟨1698684, by rfl⟩ : syracuseStep 4529825 = 3397369) B3397369
theorem B3019883 : Blo 2011435 3019883 := bstep (se 1 (by rfl) ⟨2264912, by rfl⟩ : syracuseStep 3019883 = 4529825) B4529825
theorem B2013255 : Blo 2011435 2013255 := bstep (se 1 (by rfl) ⟨1509941, by rfl⟩ : syracuseStep 2013255 = 3019883) B3019883
theorem B2264917 : Blo 2011435 2264917 := bbase (se 9 (by rfl) ⟨6635, by rfl⟩ : syracuseStep 2264917 = 13271) (by norm_num)
theorem B3019889 : Blo 2011435 3019889 := bstep (se 2 (by rfl) ⟨1132458, by rfl⟩ : syracuseStep 3019889 = 2264917) B2264917
theorem B2013259 : Blo 2011435 2013259 := bstep (se 1 (by rfl) ⟨1509944, by rfl⟩ : syracuseStep 2013259 = 3019889) B3019889
theorem B2548037 : Blo 2011435 2548037 := bbase (se 4 (by rfl) ⟨238878, by rfl⟩ : syracuseStep 2548037 = 477757) (by norm_num)
theorem B6794765 : Blo 2011435 6794765 := bstep (se 3 (by rfl) ⟨1274018, by rfl⟩ : syracuseStep 6794765 = 2548037) B2548037
theorem B4529843 : Blo 2011435 4529843 := bstep (se 1 (by rfl) ⟨3397382, by rfl⟩ : syracuseStep 4529843 = 6794765) B6794765
theorem B3019895 : Blo 2011435 3019895 := bstep (se 1 (by rfl) ⟨2264921, by rfl⟩ : syracuseStep 3019895 = 4529843) B4529843
theorem B2013263 : Blo 2011435 2013263 := bstep (se 1 (by rfl) ⟨1509947, by rfl⟩ : syracuseStep 2013263 = 3019895) B3019895
theorem B3019901 : Blo 2011435 3019901 := bbase (se 3 (by rfl) ⟨566231, by rfl⟩ : syracuseStep 3019901 = 1132463) (by norm_num)
theorem B2013267 : Blo 2011435 2013267 := bstep (se 1 (by rfl) ⟨1509950, by rfl⟩ : syracuseStep 2013267 = 3019901) B3019901
theorem B4529861 : Blo 2011435 4529861 := bbase (se 4 (by rfl) ⟨424674, by rfl⟩ : syracuseStep 4529861 = 849349) (by norm_num)
theorem B3019907 : Blo 2011435 3019907 := bstep (se 1 (by rfl) ⟨2264930, by rfl⟩ : syracuseStep 3019907 = 4529861) B4529861
theorem B2013271 : Blo 2011435 2013271 := bstep (se 1 (by rfl) ⟨1509953, by rfl⟩ : syracuseStep 2013271 = 3019907) B3019907
theorem B19613269 : Blo 2011435 19613269 := bbase (se 8 (by rfl) ⟨114921, by rfl⟩ : syracuseStep 19613269 = 229843) (by norm_num)
theorem B26151025 : Blo 2011435 26151025 := bstep (se 2 (by rfl) ⟨9806634, by rfl⟩ : syracuseStep 26151025 = 19613269) B19613269
theorem B34868033 : Blo 2011435 34868033 := bstep (se 2 (by rfl) ⟨13075512, by rfl⟩ : syracuseStep 34868033 = 26151025) B26151025
theorem B23245355 : Blo 2011435 23245355 := bstep (se 1 (by rfl) ⟨17434016, by rfl⟩ : syracuseStep 23245355 = 34868033) B34868033
theorem B15496903 : Blo 2011435 15496903 := bstep (se 1 (by rfl) ⟨11622677, by rfl⟩ : syracuseStep 15496903 = 23245355) B23245355
theorem B20662537 : Blo 2011435 20662537 := bstep (se 2 (by rfl) ⟨7748451, by rfl⟩ : syracuseStep 20662537 = 15496903) B15496903
theorem B27550049 : Blo 2011435 27550049 := bstep (se 2 (by rfl) ⟨10331268, by rfl⟩ : syracuseStep 27550049 = 20662537) B20662537
theorem B73466797 : Blo 2011435 73466797 := bstep (se 3 (by rfl) ⟨13775024, by rfl⟩ : syracuseStep 73466797 = 27550049) B27550049
theorem B97955729 : Blo 2011435 97955729 := bstep (se 2 (by rfl) ⟨36733398, by rfl⟩ : syracuseStep 97955729 = 73466797) B73466797
theorem B65303819 : Blo 2011435 65303819 := bstep (se 1 (by rfl) ⟨48977864, by rfl⟩ : syracuseStep 65303819 = 97955729) B97955729
theorem B43535879 : Blo 2011435 43535879 := bstep (se 1 (by rfl) ⟨32651909, by rfl⟩ : syracuseStep 43535879 = 65303819) B65303819
theorem B29023919 : Blo 2011435 29023919 := bstep (se 1 (by rfl) ⟨21767939, by rfl⟩ : syracuseStep 29023919 = 43535879) B43535879
theorem B19349279 : Blo 2011435 19349279 := bstep (se 1 (by rfl) ⟨14511959, by rfl⟩ : syracuseStep 19349279 = 29023919) B29023919
theorem B12899519 : Blo 2011435 12899519 := bstep (se 1 (by rfl) ⟨9674639, by rfl⟩ : syracuseStep 12899519 = 19349279) B19349279
theorem B8599679 : Blo 2011435 8599679 := bstep (se 1 (by rfl) ⟨6449759, by rfl⟩ : syracuseStep 8599679 = 12899519) B12899519
theorem B5733119 : Blo 2011435 5733119 := bstep (se 1 (by rfl) ⟨4299839, by rfl⟩ : syracuseStep 5733119 = 8599679) B8599679
theorem B3822079 : Blo 2011435 3822079 := bstep (se 1 (by rfl) ⟨2866559, by rfl⟩ : syracuseStep 3822079 = 5733119) B5733119
theorem B5096105 : Blo 2011435 5096105 := bstep (se 2 (by rfl) ⟨1911039, by rfl⟩ : syracuseStep 5096105 = 3822079) B3822079
theorem B3397403 : Blo 2011435 3397403 := bstep (se 1 (by rfl) ⟨2548052, by rfl⟩ : syracuseStep 3397403 = 5096105) B5096105
theorem B2264935 : Blo 2011435 2264935 := bstep (se 1 (by rfl) ⟨1698701, by rfl⟩ : syracuseStep 2264935 = 3397403) B3397403
theorem B3019913 : Blo 2011435 3019913 := bstep (se 2 (by rfl) ⟨1132467, by rfl⟩ : syracuseStep 3019913 = 2264935) B2264935
theorem B2013275 : Blo 2011435 2013275 := bstep (se 1 (by rfl) ⟨1509956, by rfl⟩ : syracuseStep 2013275 = 3019913) B3019913
theorem B10192229 : Blo 2011435 10192229 := bbase (se 4 (by rfl) ⟨955521, by rfl⟩ : syracuseStep 10192229 = 1911043) (by norm_num)
theorem B6794819 : Blo 2011435 6794819 := bstep (se 1 (by rfl) ⟨5096114, by rfl⟩ : syracuseStep 6794819 = 10192229) B10192229
theorem B4529879 : Blo 2011435 4529879 := bstep (se 1 (by rfl) ⟨3397409, by rfl⟩ : syracuseStep 4529879 = 6794819) B6794819
theorem B3019919 : Blo 2011435 3019919 := bstep (se 1 (by rfl) ⟨2264939, by rfl⟩ : syracuseStep 3019919 = 4529879) B4529879
theorem B2013279 : Blo 2011435 2013279 := bstep (se 1 (by rfl) ⟨1509959, by rfl⟩ : syracuseStep 2013279 = 3019919) B3019919
theorem B3019925 : Blo 2011435 3019925 := bbase (se 6 (by rfl) ⟨70779, by rfl⟩ : syracuseStep 3019925 = 141559) (by norm_num)
theorem B2013283 : Blo 2011435 2013283 := bstep (se 1 (by rfl) ⟨1509962, by rfl⟩ : syracuseStep 2013283 = 3019925) B3019925
theorem B6449797 : Blo 2011435 6449797 := bbase (se 4 (by rfl) ⟨604668, by rfl⟩ : syracuseStep 6449797 = 1209337) (by norm_num)
theorem B8599729 : Blo 2011435 8599729 := bstep (se 2 (by rfl) ⟨3224898, by rfl⟩ : syracuseStep 8599729 = 6449797) B6449797
theorem B11466305 : Blo 2011435 11466305 := bstep (se 2 (by rfl) ⟨4299864, by rfl⟩ : syracuseStep 11466305 = 8599729) B8599729
theorem B7644203 : Blo 2011435 7644203 := bstep (se 1 (by rfl) ⟨5733152, by rfl⟩ : syracuseStep 7644203 = 11466305) B11466305
theorem B5096135 : Blo 2011435 5096135 := bstep (se 1 (by rfl) ⟨3822101, by rfl⟩ : syracuseStep 5096135 = 7644203) B7644203
theorem B3397423 : Blo 2011435 3397423 := bstep (se 1 (by rfl) ⟨2548067, by rfl⟩ : syracuseStep 3397423 = 5096135) B5096135
theorem B4529897 : Blo 2011435 4529897 := bstep (se 2 (by rfl) ⟨1698711, by rfl⟩ : syracuseStep 4529897 = 3397423) B3397423
theorem B3019931 : Blo 2011435 3019931 := bstep (se 1 (by rfl) ⟨2264948, by rfl⟩ : syracuseStep 3019931 = 4529897) B4529897
theorem B2013287 : Blo 2011435 2013287 := bstep (se 1 (by rfl) ⟨1509965, by rfl⟩ : syracuseStep 2013287 = 3019931) B3019931
theorem B2264953 : Blo 2011435 2264953 := bbase (se 2 (by rfl) ⟨849357, by rfl⟩ : syracuseStep 2264953 = 1698715) (by norm_num)
theorem B3019937 : Blo 2011435 3019937 := bstep (se 2 (by rfl) ⟨1132476, by rfl⟩ : syracuseStep 3019937 = 2264953) B2264953
theorem B2013291 : Blo 2011435 2013291 := bstep (se 1 (by rfl) ⟨1509968, by rfl⟩ : syracuseStep 2013291 = 3019937) B3019937
theorem B4358549 : Blo 2011435 4358549 := bbase (se 6 (by rfl) ⟨102153, by rfl⟩ : syracuseStep 4358549 = 204307) (by norm_num)
theorem B11622797 : Blo 2011435 11622797 := bstep (se 3 (by rfl) ⟨2179274, by rfl⟩ : syracuseStep 11622797 = 4358549) B4358549
theorem B7748531 : Blo 2011435 7748531 := bstep (se 1 (by rfl) ⟨5811398, by rfl⟩ : syracuseStep 7748531 = 11622797) B11622797
theorem B5165687 : Blo 2011435 5165687 := bstep (se 1 (by rfl) ⟨3874265, by rfl⟩ : syracuseStep 5165687 = 7748531) B7748531
theorem B3443791 : Blo 2011435 3443791 := bstep (se 1 (by rfl) ⟨2582843, by rfl⟩ : syracuseStep 3443791 = 5165687) B5165687
theorem B4591721 : Blo 2011435 4591721 := bstep (se 2 (by rfl) ⟨1721895, by rfl⟩ : syracuseStep 4591721 = 3443791) B3443791
theorem B3061147 : Blo 2011435 3061147 := bstep (se 1 (by rfl) ⟨2295860, by rfl⟩ : syracuseStep 3061147 = 4591721) B4591721
theorem B4081529 : Blo 2011435 4081529 := bstep (se 2 (by rfl) ⟨1530573, by rfl⟩ : syracuseStep 4081529 = 3061147) B3061147
theorem B10884077 : Blo 2011435 10884077 := bstep (se 3 (by rfl) ⟨2040764, by rfl⟩ : syracuseStep 10884077 = 4081529) B4081529
theorem B7256051 : Blo 2011435 7256051 := bstep (se 1 (by rfl) ⟨5442038, by rfl⟩ : syracuseStep 7256051 = 10884077) B10884077
theorem B4837367 : Blo 2011435 4837367 := bstep (se 1 (by rfl) ⟨3628025, by rfl⟩ : syracuseStep 4837367 = 7256051) B7256051
theorem B12899645 : Blo 2011435 12899645 := bstep (se 3 (by rfl) ⟨2418683, by rfl⟩ : syracuseStep 12899645 = 4837367) B4837367
theorem B8599763 : Blo 2011435 8599763 := bstep (se 1 (by rfl) ⟨6449822, by rfl⟩ : syracuseStep 8599763 = 12899645) B12899645
theorem B5733175 : Blo 2011435 5733175 := bstep (se 1 (by rfl) ⟨4299881, by rfl⟩ : syracuseStep 5733175 = 8599763) B8599763
theorem B7644233 : Blo 2011435 7644233 := bstep (se 2 (by rfl) ⟨2866587, by rfl⟩ : syracuseStep 7644233 = 5733175) B5733175
theorem B5096155 : Blo 2011435 5096155 := bstep (se 1 (by rfl) ⟨3822116, by rfl⟩ : syracuseStep 5096155 = 7644233) B7644233
theorem B6794873 : Blo 2011435 6794873 := bstep (se 2 (by rfl) ⟨2548077, by rfl⟩ : syracuseStep 6794873 = 5096155) B5096155
theorem B4529915 : Blo 2011435 4529915 := bstep (se 1 (by rfl) ⟨3397436, by rfl⟩ : syracuseStep 4529915 = 6794873) B6794873
theorem B3019943 : Blo 2011435 3019943 := bstep (se 1 (by rfl) ⟨2264957, by rfl⟩ : syracuseStep 3019943 = 4529915) B4529915
theorem B2013295 : Blo 2011435 2013295 := bstep (se 1 (by rfl) ⟨1509971, by rfl⟩ : syracuseStep 2013295 = 3019943) B3019943
theorem B3019949 : Blo 2011435 3019949 := bbase (se 3 (by rfl) ⟨566240, by rfl⟩ : syracuseStep 3019949 = 1132481) (by norm_num)
theorem B2013299 : Blo 2011435 2013299 := bstep (se 1 (by rfl) ⟨1509974, by rfl⟩ : syracuseStep 2013299 = 3019949) B3019949
theorem B4529933 : Blo 2011435 4529933 := bbase (se 3 (by rfl) ⟨849362, by rfl⟩ : syracuseStep 4529933 = 1698725) (by norm_num)
theorem B3019955 : Blo 2011435 3019955 := bstep (se 1 (by rfl) ⟨2264966, by rfl⟩ : syracuseStep 3019955 = 4529933) B4529933
theorem B2013303 : Blo 2011435 2013303 := bstep (se 1 (by rfl) ⟨1509977, by rfl⟩ : syracuseStep 2013303 = 3019955) B3019955
theorem B2548093 : Blo 2011435 2548093 := bbase (se 3 (by rfl) ⟨477767, by rfl⟩ : syracuseStep 2548093 = 955535) (by norm_num)
theorem B3397457 : Blo 2011435 3397457 := bstep (se 2 (by rfl) ⟨1274046, by rfl⟩ : syracuseStep 3397457 = 2548093) B2548093
theorem B2264971 : Blo 2011435 2264971 := bstep (se 1 (by rfl) ⟨1698728, by rfl⟩ : syracuseStep 2264971 = 3397457) B3397457
theorem B3019961 : Blo 2011435 3019961 := bstep (se 2 (by rfl) ⟨1132485, by rfl⟩ : syracuseStep 3019961 = 2264971) B2264971
theorem B2013307 : Blo 2011435 2013307 := bstep (se 1 (by rfl) ⟨1509980, by rfl⟩ : syracuseStep 2013307 = 3019961) B3019961
theorem B4837405 : Blo 2011435 4837405 := bbase (se 3 (by rfl) ⟨907013, by rfl⟩ : syracuseStep 4837405 = 1814027) (by norm_num)
theorem B6449873 : Blo 2011435 6449873 := bstep (se 2 (by rfl) ⟨2418702, by rfl⟩ : syracuseStep 6449873 = 4837405) B4837405
theorem B17199661 : Blo 2011435 17199661 := bstep (se 3 (by rfl) ⟨3224936, by rfl⟩ : syracuseStep 17199661 = 6449873) B6449873
theorem B22932881 : Blo 2011435 22932881 := bstep (se 2 (by rfl) ⟨8599830, by rfl⟩ : syracuseStep 22932881 = 17199661) B17199661
theorem B15288587 : Blo 2011435 15288587 := bstep (se 1 (by rfl) ⟨11466440, by rfl⟩ : syracuseStep 15288587 = 22932881) B22932881
theorem B10192391 : Blo 2011435 10192391 := bstep (se 1 (by rfl) ⟨7644293, by rfl⟩ : syracuseStep 10192391 = 15288587) B15288587
theorem B6794927 : Blo 2011435 6794927 := bstep (se 1 (by rfl) ⟨5096195, by rfl⟩ : syracuseStep 6794927 = 10192391) B10192391
theorem B4529951 : Blo 2011435 4529951 := bstep (se 1 (by rfl) ⟨3397463, by rfl⟩ : syracuseStep 4529951 = 6794927) B6794927
theorem B3019967 : Blo 2011435 3019967 := bstep (se 1 (by rfl) ⟨2264975, by rfl⟩ : syracuseStep 3019967 = 4529951) B4529951
theorem B2013311 : Blo 2011435 2013311 := bstep (se 1 (by rfl) ⟨1509983, by rfl⟩ : syracuseStep 2013311 = 3019967) B3019967
theorem B3019973 : Blo 2011435 3019973 := bbase (se 4 (by rfl) ⟨283122, by rfl⟩ : syracuseStep 3019973 = 566245) (by norm_num)
theorem B2013315 : Blo 2011435 2013315 := bstep (se 1 (by rfl) ⟨1509986, by rfl⟩ : syracuseStep 2013315 = 3019973) B3019973
theorem B3397477 : Blo 2011435 3397477 := bbase (se 4 (by rfl) ⟨318513, by rfl⟩ : syracuseStep 3397477 = 637027) (by norm_num)
theorem B4529969 : Blo 2011435 4529969 := bstep (se 2 (by rfl) ⟨1698738, by rfl⟩ : syracuseStep 4529969 = 3397477) B3397477
theorem B3019979 : Blo 2011435 3019979 := bstep (se 1 (by rfl) ⟨2264984, by rfl⟩ : syracuseStep 3019979 = 4529969) B4529969
theorem B2013319 : Blo 2011435 2013319 := bstep (se 1 (by rfl) ⟨1509989, by rfl⟩ : syracuseStep 2013319 = 3019979) B3019979
theorem B2264989 : Blo 2011435 2264989 := bbase (se 3 (by rfl) ⟨424685, by rfl⟩ : syracuseStep 2264989 = 849371) (by norm_num)
theorem B3019985 : Blo 2011435 3019985 := bstep (se 2 (by rfl) ⟨1132494, by rfl⟩ : syracuseStep 3019985 = 2264989) B2264989
theorem B2013323 : Blo 2011435 2013323 := bstep (se 1 (by rfl) ⟨1509992, by rfl⟩ : syracuseStep 2013323 = 3019985) B3019985
theorem B6794981 : Blo 2011435 6794981 := bbase (se 4 (by rfl) ⟨637029, by rfl⟩ : syracuseStep 6794981 = 1274059) (by norm_num)
theorem B4529987 : Blo 2011435 4529987 := bstep (se 1 (by rfl) ⟨3397490, by rfl⟩ : syracuseStep 4529987 = 6794981) B6794981
theorem B3019991 : Blo 2011435 3019991 := bstep (se 1 (by rfl) ⟨2264993, by rfl⟩ : syracuseStep 3019991 = 4529987) B4529987
theorem B2013327 : Blo 2011435 2013327 := bstep (se 1 (by rfl) ⟨1509995, by rfl⟩ : syracuseStep 2013327 = 3019991) B3019991
theorem B3019997 : Blo 2011435 3019997 := bbase (se 3 (by rfl) ⟨566249, by rfl⟩ : syracuseStep 3019997 = 1132499) (by norm_num)
theorem B2013331 : Blo 2011435 2013331 := bstep (se 1 (by rfl) ⟨1509998, by rfl⟩ : syracuseStep 2013331 = 3019997) B3019997
theorem B4530005 : Blo 2011435 4530005 := bbase (se 9 (by rfl) ⟨13271, by rfl⟩ : syracuseStep 4530005 = 26543) (by norm_num)
theorem B3020003 : Blo 2011435 3020003 := bstep (se 1 (by rfl) ⟨2265002, by rfl⟩ : syracuseStep 3020003 = 4530005) B4530005
theorem B2013335 : Blo 2011435 2013335 := bstep (se 1 (by rfl) ⟨1510001, by rfl⟩ : syracuseStep 2013335 = 3020003) B3020003
theorem B5733301 : Blo 2011435 5733301 := bbase (se 5 (by rfl) ⟨268748, by rfl⟩ : syracuseStep 5733301 = 537497) (by norm_num)
theorem B7644401 : Blo 2011435 7644401 := bstep (se 2 (by rfl) ⟨2866650, by rfl⟩ : syracuseStep 7644401 = 5733301) B5733301
theorem B5096267 : Blo 2011435 5096267 := bstep (se 1 (by rfl) ⟨3822200, by rfl⟩ : syracuseStep 5096267 = 7644401) B7644401
theorem B3397511 : Blo 2011435 3397511 := bstep (se 1 (by rfl) ⟨2548133, by rfl⟩ : syracuseStep 3397511 = 5096267) B5096267
theorem B2265007 : Blo 2011435 2265007 := bstep (se 1 (by rfl) ⟨1698755, by rfl⟩ : syracuseStep 2265007 = 3397511) B3397511
theorem B3020009 : Blo 2011435 3020009 := bstep (se 2 (by rfl) ⟨1132503, by rfl⟩ : syracuseStep 3020009 = 2265007) B2265007
theorem B2013339 : Blo 2011435 2013339 := bstep (se 1 (by rfl) ⟨1510004, by rfl⟩ : syracuseStep 2013339 = 3020009) B3020009
theorem B32280853 : Blo 2011435 32280853 := bbase (se 6 (by rfl) ⟨756582, by rfl⟩ : syracuseStep 32280853 = 1513165) (by norm_num)
theorem B43041137 : Blo 2011435 43041137 := bstep (se 2 (by rfl) ⟨16140426, by rfl⟩ : syracuseStep 43041137 = 32280853) B32280853
theorem B114776365 : Blo 2011435 114776365 := bstep (se 3 (by rfl) ⟨21520568, by rfl⟩ : syracuseStep 114776365 = 43041137) B43041137
theorem B153035153 : Blo 2011435 153035153 := bstep (se 2 (by rfl) ⟨57388182, by rfl⟩ : syracuseStep 153035153 = 114776365) B114776365
theorem B102023435 : Blo 2011435 102023435 := bstep (se 1 (by rfl) ⟨76517576, by rfl⟩ : syracuseStep 102023435 = 153035153) B153035153
theorem B272062493 : Blo 2011435 272062493 := bstep (se 3 (by rfl) ⟨51011717, by rfl⟩ : syracuseStep 272062493 = 102023435) B102023435
theorem B181374995 : Blo 2011435 181374995 := bstep (se 1 (by rfl) ⟨136031246, by rfl⟩ : syracuseStep 181374995 = 272062493) B272062493
theorem B483666653 : Blo 2011435 483666653 := bstep (se 3 (by rfl) ⟨90687497, by rfl⟩ : syracuseStep 483666653 = 181374995) B181374995
theorem B322444435 : Blo 2011435 322444435 := bstep (se 1 (by rfl) ⟨241833326, by rfl⟩ : syracuseStep 322444435 = 483666653) B483666653
theorem B429925913 : Blo 2011435 429925913 := bstep (se 2 (by rfl) ⟨161222217, by rfl⟩ : syracuseStep 429925913 = 322444435) B322444435
theorem B286617275 : Blo 2011435 286617275 := bstep (se 1 (by rfl) ⟨214962956, by rfl⟩ : syracuseStep 286617275 = 429925913) B429925913
theorem B191078183 : Blo 2011435 191078183 := bstep (se 1 (by rfl) ⟨143308637, by rfl⟩ : syracuseStep 191078183 = 286617275) B286617275
theorem B127385455 : Blo 2011435 127385455 := bstep (se 1 (by rfl) ⟨95539091, by rfl⟩ : syracuseStep 127385455 = 191078183) B191078183
theorem B169847273 : Blo 2011435 169847273 := bstep (se 2 (by rfl) ⟨63692727, by rfl⟩ : syracuseStep 169847273 = 127385455) B127385455
theorem B113231515 : Blo 2011435 113231515 := bstep (se 1 (by rfl) ⟨84923636, by rfl⟩ : syracuseStep 113231515 = 169847273) B169847273
theorem B150975353 : Blo 2011435 150975353 := bstep (se 2 (by rfl) ⟨56615757, by rfl⟩ : syracuseStep 150975353 = 113231515) B113231515
theorem B100650235 : Blo 2011435 100650235 := bstep (se 1 (by rfl) ⟨75487676, by rfl⟩ : syracuseStep 100650235 = 150975353) B150975353
theorem B134200313 : Blo 2011435 134200313 := bstep (se 2 (by rfl) ⟨50325117, by rfl⟩ : syracuseStep 134200313 = 100650235) B100650235
theorem B89466875 : Blo 2011435 89466875 := bstep (se 1 (by rfl) ⟨67100156, by rfl⟩ : syracuseStep 89466875 = 134200313) B134200313
theorem B59644583 : Blo 2011435 59644583 := bstep (se 1 (by rfl) ⟨44733437, by rfl⟩ : syracuseStep 59644583 = 89466875) B89466875
theorem B39763055 : Blo 2011435 39763055 := bstep (se 1 (by rfl) ⟨29822291, by rfl⟩ : syracuseStep 39763055 = 59644583) B59644583
theorem B26508703 : Blo 2011435 26508703 := bstep (se 1 (by rfl) ⟨19881527, by rfl⟩ : syracuseStep 26508703 = 39763055) B39763055
theorem B35344937 : Blo 2011435 35344937 := bstep (se 2 (by rfl) ⟨13254351, by rfl⟩ : syracuseStep 35344937 = 26508703) B26508703
theorem B23563291 : Blo 2011435 23563291 := bstep (se 1 (by rfl) ⟨17672468, by rfl⟩ : syracuseStep 23563291 = 35344937) B35344937
theorem B31417721 : Blo 2011435 31417721 := bstep (se 2 (by rfl) ⟨11781645, by rfl⟩ : syracuseStep 31417721 = 23563291) B23563291
theorem B20945147 : Blo 2011435 20945147 := bstep (se 1 (by rfl) ⟨15708860, by rfl⟩ : syracuseStep 20945147 = 31417721) B31417721
theorem B55853725 : Blo 2011435 55853725 := bstep (se 3 (by rfl) ⟨10472573, by rfl⟩ : syracuseStep 55853725 = 20945147) B20945147
theorem B74471633 : Blo 2011435 74471633 := bstep (se 2 (by rfl) ⟨27926862, by rfl⟩ : syracuseStep 74471633 = 55853725) B55853725
theorem B49647755 : Blo 2011435 49647755 := bstep (se 1 (by rfl) ⟨37235816, by rfl⟩ : syracuseStep 49647755 = 74471633) B74471633
theorem B33098503 : Blo 2011435 33098503 := bstep (se 1 (by rfl) ⟨24823877, by rfl⟩ : syracuseStep 33098503 = 49647755) B49647755
theorem B44131337 : Blo 2011435 44131337 := bstep (se 2 (by rfl) ⟨16549251, by rfl⟩ : syracuseStep 44131337 = 33098503) B33098503
theorem B29420891 : Blo 2011435 29420891 := bstep (se 1 (by rfl) ⟨22065668, by rfl⟩ : syracuseStep 29420891 = 44131337) B44131337
theorem B19613927 : Blo 2011435 19613927 := bstep (se 1 (by rfl) ⟨14710445, by rfl⟩ : syracuseStep 19613927 = 29420891) B29420891
theorem B52303805 : Blo 2011435 52303805 := bstep (se 3 (by rfl) ⟨9806963, by rfl⟩ : syracuseStep 52303805 = 19613927) B19613927
theorem B34869203 : Blo 2011435 34869203 := bstep (se 1 (by rfl) ⟨26151902, by rfl⟩ : syracuseStep 34869203 = 52303805) B52303805
theorem B23246135 : Blo 2011435 23246135 := bstep (se 1 (by rfl) ⟨17434601, by rfl⟩ : syracuseStep 23246135 = 34869203) B34869203
theorem B15497423 : Blo 2011435 15497423 := bstep (se 1 (by rfl) ⟨11623067, by rfl⟩ : syracuseStep 15497423 = 23246135) B23246135
theorem B10331615 : Blo 2011435 10331615 := bstep (se 1 (by rfl) ⟨7748711, by rfl⟩ : syracuseStep 10331615 = 15497423) B15497423
theorem B6887743 : Blo 2011435 6887743 := bstep (se 1 (by rfl) ⟨5165807, by rfl⟩ : syracuseStep 6887743 = 10331615) B10331615
theorem B36734629 : Blo 2011435 36734629 := bstep (se 4 (by rfl) ⟨3443871, by rfl⟩ : syracuseStep 36734629 = 6887743) B6887743
theorem B48979505 : Blo 2011435 48979505 := bstep (se 2 (by rfl) ⟨18367314, by rfl⟩ : syracuseStep 48979505 = 36734629) B36734629
theorem B130612013 : Blo 2011435 130612013 := bstep (se 3 (by rfl) ⟨24489752, by rfl⟩ : syracuseStep 130612013 = 48979505) B48979505
theorem B87074675 : Blo 2011435 87074675 := bstep (se 1 (by rfl) ⟨65306006, by rfl⟩ : syracuseStep 87074675 = 130612013) B130612013
theorem B58049783 : Blo 2011435 58049783 := bstep (se 1 (by rfl) ⟨43537337, by rfl⟩ : syracuseStep 58049783 = 87074675) B87074675
theorem B38699855 : Blo 2011435 38699855 := bstep (se 1 (by rfl) ⟨29024891, by rfl⟩ : syracuseStep 38699855 = 58049783) B58049783
theorem B25799903 : Blo 2011435 25799903 := bstep (se 1 (by rfl) ⟨19349927, by rfl⟩ : syracuseStep 25799903 = 38699855) B38699855
theorem B17199935 : Blo 2011435 17199935 := bstep (se 1 (by rfl) ⟨12899951, by rfl⟩ : syracuseStep 17199935 = 25799903) B25799903
theorem B11466623 : Blo 2011435 11466623 := bstep (se 1 (by rfl) ⟨8599967, by rfl⟩ : syracuseStep 11466623 = 17199935) B17199935
theorem B7644415 : Blo 2011435 7644415 := bstep (se 1 (by rfl) ⟨5733311, by rfl⟩ : syracuseStep 7644415 = 11466623) B11466623
theorem B10192553 : Blo 2011435 10192553 := bstep (se 2 (by rfl) ⟨3822207, by rfl⟩ : syracuseStep 10192553 = 7644415) B7644415
theorem B6795035 : Blo 2011435 6795035 := bstep (se 1 (by rfl) ⟨5096276, by rfl⟩ : syracuseStep 6795035 = 10192553) B10192553
theorem B4530023 : Blo 2011435 4530023 := bstep (se 1 (by rfl) ⟨3397517, by rfl⟩ : syracuseStep 4530023 = 6795035) B6795035
theorem B3020015 : Blo 2011435 3020015 := bstep (se 1 (by rfl) ⟨2265011, by rfl⟩ : syracuseStep 3020015 = 4530023) B4530023
theorem B2013343 : Blo 2011435 2013343 := bstep (se 1 (by rfl) ⟨1510007, by rfl⟩ : syracuseStep 2013343 = 3020015) B3020015
theorem B3020021 : Blo 2011435 3020021 := bbase (se 5 (by rfl) ⟨141563, by rfl⟩ : syracuseStep 3020021 = 283127) (by norm_num)
theorem B2013347 : Blo 2011435 2013347 := bstep (se 1 (by rfl) ⟨1510010, by rfl⟩ : syracuseStep 2013347 = 3020021) B3020021
theorem B3677629 : Blo 2011435 3677629 := bbase (se 3 (by rfl) ⟨689555, by rfl⟩ : syracuseStep 3677629 = 1379111) (by norm_num)
theorem B4903505 : Blo 2011435 4903505 := bstep (se 2 (by rfl) ⟨1838814, by rfl⟩ : syracuseStep 4903505 = 3677629) B3677629
theorem B3269003 : Blo 2011435 3269003 := bstep (se 1 (by rfl) ⟨2451752, by rfl⟩ : syracuseStep 3269003 = 4903505) B4903505
theorem B8717341 : Blo 2011435 8717341 := bstep (se 3 (by rfl) ⟨1634501, by rfl⟩ : syracuseStep 8717341 = 3269003) B3269003
theorem B11623121 : Blo 2011435 11623121 := bstep (se 2 (by rfl) ⟨4358670, by rfl⟩ : syracuseStep 11623121 = 8717341) B8717341
theorem B7748747 : Blo 2011435 7748747 := bstep (se 1 (by rfl) ⟨5811560, by rfl⟩ : syracuseStep 7748747 = 11623121) B11623121
theorem B5165831 : Blo 2011435 5165831 := bstep (se 1 (by rfl) ⟨3874373, by rfl⟩ : syracuseStep 5165831 = 7748747) B7748747
theorem B3443887 : Blo 2011435 3443887 := bstep (se 1 (by rfl) ⟨2582915, by rfl⟩ : syracuseStep 3443887 = 5165831) B5165831
theorem B18367397 : Blo 2011435 18367397 := bstep (se 4 (by rfl) ⟨1721943, by rfl⟩ : syracuseStep 18367397 = 3443887) B3443887
theorem B12244931 : Blo 2011435 12244931 := bstep (se 1 (by rfl) ⟨9183698, by rfl⟩ : syracuseStep 12244931 = 18367397) B18367397
theorem B8163287 : Blo 2011435 8163287 := bstep (se 1 (by rfl) ⟨6122465, by rfl⟩ : syracuseStep 8163287 = 12244931) B12244931
theorem B5442191 : Blo 2011435 5442191 := bstep (se 1 (by rfl) ⟨4081643, by rfl⟩ : syracuseStep 5442191 = 8163287) B8163287
theorem B3628127 : Blo 2011435 3628127 := bstep (se 1 (by rfl) ⟨2721095, by rfl⟩ : syracuseStep 3628127 = 5442191) B5442191
theorem B2418751 : Blo 2011435 2418751 := bstep (se 1 (by rfl) ⟨1814063, by rfl⟩ : syracuseStep 2418751 = 3628127) B3628127
theorem B12900005 : Blo 2011435 12900005 := bstep (se 4 (by rfl) ⟨1209375, by rfl⟩ : syracuseStep 12900005 = 2418751) B2418751
theorem B8600003 : Blo 2011435 8600003 := bstep (se 1 (by rfl) ⟨6450002, by rfl⟩ : syracuseStep 8600003 = 12900005) B12900005
theorem B5733335 : Blo 2011435 5733335 := bstep (se 1 (by rfl) ⟨4300001, by rfl⟩ : syracuseStep 5733335 = 8600003) B8600003
theorem B3822223 : Blo 2011435 3822223 := bstep (se 1 (by rfl) ⟨2866667, by rfl⟩ : syracuseStep 3822223 = 5733335) B5733335
theorem B5096297 : Blo 2011435 5096297 := bstep (se 2 (by rfl) ⟨1911111, by rfl⟩ : syracuseStep 5096297 = 3822223) B3822223
theorem B3397531 : Blo 2011435 3397531 := bstep (se 1 (by rfl) ⟨2548148, by rfl⟩ : syracuseStep 3397531 = 5096297) B5096297
theorem B4530041 : Blo 2011435 4530041 := bstep (se 2 (by rfl) ⟨1698765, by rfl⟩ : syracuseStep 4530041 = 3397531) B3397531
theorem B3020027 : Blo 2011435 3020027 := bstep (se 1 (by rfl) ⟨2265020, by rfl⟩ : syracuseStep 3020027 = 4530041) B4530041
theorem B2013351 : Blo 2011435 2013351 := bstep (se 1 (by rfl) ⟨1510013, by rfl⟩ : syracuseStep 2013351 = 3020027) B3020027
theorem B2265025 : Blo 2011435 2265025 := bbase (se 2 (by rfl) ⟨849384, by rfl⟩ : syracuseStep 2265025 = 1698769) (by norm_num)
theorem B3020033 : Blo 2011435 3020033 := bstep (se 2 (by rfl) ⟨1132512, by rfl⟩ : syracuseStep 3020033 = 2265025) B2265025
theorem B2013355 : Blo 2011435 2013355 := bstep (se 1 (by rfl) ⟨1510016, by rfl⟩ : syracuseStep 2013355 = 3020033) B3020033
theorem B5096317 : Blo 2011435 5096317 := bbase (se 3 (by rfl) ⟨955559, by rfl⟩ : syracuseStep 5096317 = 1911119) (by norm_num)
theorem B6795089 : Blo 2011435 6795089 := bstep (se 2 (by rfl) ⟨2548158, by rfl⟩ : syracuseStep 6795089 = 5096317) B5096317
theorem B4530059 : Blo 2011435 4530059 := bstep (se 1 (by rfl) ⟨3397544, by rfl⟩ : syracuseStep 4530059 = 6795089) B6795089
theorem B3020039 : Blo 2011435 3020039 := bstep (se 1 (by rfl) ⟨2265029, by rfl⟩ : syracuseStep 3020039 = 4530059) B4530059
theorem B2013359 : Blo 2011435 2013359 := bstep (se 1 (by rfl) ⟨1510019, by rfl⟩ : syracuseStep 2013359 = 3020039) B3020039
theorem B3020045 : Blo 2011435 3020045 := bbase (se 3 (by rfl) ⟨566258, by rfl⟩ : syracuseStep 3020045 = 1132517) (by norm_num)
theorem B2013363 : Blo 2011435 2013363 := bstep (se 1 (by rfl) ⟨1510022, by rfl⟩ : syracuseStep 2013363 = 3020045) B3020045
theorem B4530077 : Blo 2011435 4530077 := bbase (se 3 (by rfl) ⟨849389, by rfl⟩ : syracuseStep 4530077 = 1698779) (by norm_num)
theorem B3020051 : Blo 2011435 3020051 := bstep (se 1 (by rfl) ⟨2265038, by rfl⟩ : syracuseStep 3020051 = 4530077) B4530077
theorem B2013367 : Blo 2011435 2013367 := bstep (se 1 (by rfl) ⟨1510025, by rfl⟩ : syracuseStep 2013367 = 3020051) B3020051
theorem B3397565 : Blo 2011435 3397565 := bbase (se 3 (by rfl) ⟨637043, by rfl⟩ : syracuseStep 3397565 = 1274087) (by norm_num)
theorem B2265043 : Blo 2011435 2265043 := bstep (se 1 (by rfl) ⟨1698782, by rfl⟩ : syracuseStep 2265043 = 3397565) B3397565
theorem B3020057 : Blo 2011435 3020057 := bstep (se 2 (by rfl) ⟨1132521, by rfl⟩ : syracuseStep 3020057 = 2265043) B2265043
theorem B2013371 : Blo 2011435 2013371 := bstep (se 1 (by rfl) ⟨1510028, by rfl⟩ : syracuseStep 2013371 = 3020057) B3020057
theorem B11466805 : Blo 2011435 11466805 := bbase (se 5 (by rfl) ⟨537506, by rfl⟩ : syracuseStep 11466805 = 1075013) (by norm_num)
theorem B15289073 : Blo 2011435 15289073 := bstep (se 2 (by rfl) ⟨5733402, by rfl⟩ : syracuseStep 15289073 = 11466805) B11466805
theorem B10192715 : Blo 2011435 10192715 := bstep (se 1 (by rfl) ⟨7644536, by rfl⟩ : syracuseStep 10192715 = 15289073) B15289073
theorem B6795143 : Blo 2011435 6795143 := bstep (se 1 (by rfl) ⟨5096357, by rfl⟩ : syracuseStep 6795143 = 10192715) B10192715
theorem B4530095 : Blo 2011435 4530095 := bstep (se 1 (by rfl) ⟨3397571, by rfl⟩ : syracuseStep 4530095 = 6795143) B6795143
theorem B3020063 : Blo 2011435 3020063 := bstep (se 1 (by rfl) ⟨2265047, by rfl⟩ : syracuseStep 3020063 = 4530095) B4530095
theorem B2013375 : Blo 2011435 2013375 := bstep (se 1 (by rfl) ⟨1510031, by rfl⟩ : syracuseStep 2013375 = 3020063) B3020063
theorem B3020069 : Blo 2011435 3020069 := bbase (se 4 (by rfl) ⟨283131, by rfl⟩ : syracuseStep 3020069 = 566263) (by norm_num)
theorem B2013379 : Blo 2011435 2013379 := bstep (se 1 (by rfl) ⟨1510034, by rfl⟩ : syracuseStep 2013379 = 3020069) B3020069
theorem B2548189 : Blo 2011435 2548189 := bbase (se 3 (by rfl) ⟨477785, by rfl⟩ : syracuseStep 2548189 = 955571) (by norm_num)
theorem B3397585 : Blo 2011435 3397585 := bstep (se 2 (by rfl) ⟨1274094, by rfl⟩ : syracuseStep 3397585 = 2548189) B2548189
theorem B4530113 : Blo 2011435 4530113 := bstep (se 2 (by rfl) ⟨1698792, by rfl⟩ : syracuseStep 4530113 = 3397585) B3397585
theorem B3020075 : Blo 2011435 3020075 := bstep (se 1 (by rfl) ⟨2265056, by rfl⟩ : syracuseStep 3020075 = 4530113) B4530113
theorem B2013383 : Blo 2011435 2013383 := bstep (se 1 (by rfl) ⟨1510037, by rfl⟩ : syracuseStep 2013383 = 3020075) B3020075
theorem B2265061 : Blo 2011435 2265061 := bbase (se 4 (by rfl) ⟨212349, by rfl⟩ : syracuseStep 2265061 = 424699) (by norm_num)
theorem B3020081 : Blo 2011435 3020081 := bstep (se 2 (by rfl) ⟨1132530, by rfl⟩ : syracuseStep 3020081 = 2265061) B2265061
theorem B2013387 : Blo 2011435 2013387 := bstep (se 1 (by rfl) ⟨1510040, by rfl⟩ : syracuseStep 2013387 = 3020081) B3020081
theorem B14710805 : Blo 2011435 14710805 := bbase (se 6 (by rfl) ⟨344784, by rfl⟩ : syracuseStep 14710805 = 689569) (by norm_num)
theorem B9807203 : Blo 2011435 9807203 := bstep (se 1 (by rfl) ⟨7355402, by rfl⟩ : syracuseStep 9807203 = 14710805) B14710805
theorem B26152541 : Blo 2011435 26152541 := bstep (se 3 (by rfl) ⟨4903601, by rfl⟩ : syracuseStep 26152541 = 9807203) B9807203
theorem B17435027 : Blo 2011435 17435027 := bstep (se 1 (by rfl) ⟨13076270, by rfl⟩ : syracuseStep 17435027 = 26152541) B26152541
theorem B11623351 : Blo 2011435 11623351 := bstep (se 1 (by rfl) ⟨8717513, by rfl⟩ : syracuseStep 11623351 = 17435027) B17435027
theorem B15497801 : Blo 2011435 15497801 := bstep (se 2 (by rfl) ⟨5811675, by rfl⟩ : syracuseStep 15497801 = 11623351) B11623351
theorem B10331867 : Blo 2011435 10331867 := bstep (se 1 (by rfl) ⟨7748900, by rfl⟩ : syracuseStep 10331867 = 15497801) B15497801
theorem B6887911 : Blo 2011435 6887911 := bstep (se 1 (by rfl) ⟨5165933, by rfl⟩ : syracuseStep 6887911 = 10331867) B10331867
theorem B9183881 : Blo 2011435 9183881 := bstep (se 2 (by rfl) ⟨3443955, by rfl⟩ : syracuseStep 9183881 = 6887911) B6887911
theorem B6122587 : Blo 2011435 6122587 := bstep (se 1 (by rfl) ⟨4591940, by rfl⟩ : syracuseStep 6122587 = 9183881) B9183881
theorem B8163449 : Blo 2011435 8163449 := bstep (se 2 (by rfl) ⟨3061293, by rfl⟩ : syracuseStep 8163449 = 6122587) B6122587
theorem B5442299 : Blo 2011435 5442299 := bstep (se 1 (by rfl) ⟨4081724, by rfl⟩ : syracuseStep 5442299 = 8163449) B8163449
theorem B3628199 : Blo 2011435 3628199 := bstep (se 1 (by rfl) ⟨2721149, by rfl⟩ : syracuseStep 3628199 = 5442299) B5442299
theorem B9675197 : Blo 2011435 9675197 := bstep (se 3 (by rfl) ⟨1814099, by rfl⟩ : syracuseStep 9675197 = 3628199) B3628199
theorem B6450131 : Blo 2011435 6450131 := bstep (se 1 (by rfl) ⟨4837598, by rfl⟩ : syracuseStep 6450131 = 9675197) B9675197
theorem B4300087 : Blo 2011435 4300087 := bstep (se 1 (by rfl) ⟨3225065, by rfl⟩ : syracuseStep 4300087 = 6450131) B6450131
theorem B5733449 : Blo 2011435 5733449 := bstep (se 2 (by rfl) ⟨2150043, by rfl⟩ : syracuseStep 5733449 = 4300087) B4300087
theorem B3822299 : Blo 2011435 3822299 := bstep (se 1 (by rfl) ⟨2866724, by rfl⟩ : syracuseStep 3822299 = 5733449) B5733449
theorem B2548199 : Blo 2011435 2548199 := bstep (se 1 (by rfl) ⟨1911149, by rfl⟩ : syracuseStep 2548199 = 3822299) B3822299
theorem B6795197 : Blo 2011435 6795197 := bstep (se 3 (by rfl) ⟨1274099, by rfl⟩ : syracuseStep 6795197 = 2548199) B2548199
theorem B4530131 : Blo 2011435 4530131 := bstep (se 1 (by rfl) ⟨3397598, by rfl⟩ : syracuseStep 4530131 = 6795197) B6795197
theorem B3020087 : Blo 2011435 3020087 := bstep (se 1 (by rfl) ⟨2265065, by rfl⟩ : syracuseStep 3020087 = 4530131) B4530131
theorem B2013391 : Blo 2011435 2013391 := bstep (se 1 (by rfl) ⟨1510043, by rfl⟩ : syracuseStep 2013391 = 3020087) B3020087
theorem B3020093 : Blo 2011435 3020093 := bbase (se 3 (by rfl) ⟨566267, by rfl⟩ : syracuseStep 3020093 = 1132535) (by norm_num)
theorem B2013395 : Blo 2011435 2013395 := bstep (se 1 (by rfl) ⟨1510046, by rfl⟩ : syracuseStep 2013395 = 3020093) B3020093
theorem B4530149 : Blo 2011435 4530149 := bbase (se 4 (by rfl) ⟨424701, by rfl⟩ : syracuseStep 4530149 = 849403) (by norm_num)
theorem B3020099 : Blo 2011435 3020099 := bstep (se 1 (by rfl) ⟨2265074, by rfl⟩ : syracuseStep 3020099 = 4530149) B4530149
theorem B2013399 : Blo 2011435 2013399 := bstep (se 1 (by rfl) ⟨1510049, by rfl⟩ : syracuseStep 2013399 = 3020099) B3020099
theorem B5096429 : Blo 2011435 5096429 := bbase (se 3 (by rfl) ⟨955580, by rfl⟩ : syracuseStep 5096429 = 1911161) (by norm_num)
theorem B3397619 : Blo 2011435 3397619 := bstep (se 1 (by rfl) ⟨2548214, by rfl⟩ : syracuseStep 3397619 = 5096429) B5096429
theorem B2265079 : Blo 2011435 2265079 := bstep (se 1 (by rfl) ⟨1698809, by rfl⟩ : syracuseStep 2265079 = 3397619) B3397619
theorem B3020105 : Blo 2011435 3020105 := bstep (se 2 (by rfl) ⟨1132539, by rfl⟩ : syracuseStep 3020105 = 2265079) B2265079
theorem B2013403 : Blo 2011435 2013403 := bstep (se 1 (by rfl) ⟨1510052, by rfl⟩ : syracuseStep 2013403 = 3020105) B3020105
theorem B4837637 : Blo 2011435 4837637 := bbase (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) (by norm_num)
theorem B3225091 : Blo 2011435 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B4300121 : Blo 2011435 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B2866747 : Blo 2011435 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B3822329 : Blo 2011435 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B10192877 : Blo 2011435 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B6795251 : Blo 2011435 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B4530167 : Blo 2011435 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B3020111 : Blo 2011435 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B2013407 : Blo 2011435 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B3020117 : Blo 2011435 3020117 := bbase (se 14 (by rfl) ⟨276, by rfl⟩ : syracuseStep 3020117 = 553) (by norm_num)
theorem B2013411 : Blo 2011435 2013411 := bstep (se 1 (by rfl) ⟨1510058, by rfl⟩ : syracuseStep 2013411 = 3020117) B3020117
theorem B2150069 : Blo 2011435 2150069 := bbase (se 5 (by rfl) ⟨100784, by rfl⟩ : syracuseStep 2150069 = 201569) (by norm_num)
theorem B5733517 : Blo 2011435 5733517 := bstep (se 3 (by rfl) ⟨1075034, by rfl⟩ : syracuseStep 5733517 = 2150069) B2150069
theorem B7644689 : Blo 2011435 7644689 := bstep (se 2 (by rfl) ⟨2866758, by rfl⟩ : syracuseStep 7644689 = 5733517) B5733517
theorem B5096459 : Blo 2011435 5096459 := bstep (se 1 (by rfl) ⟨3822344, by rfl⟩ : syracuseStep 5096459 = 7644689) B7644689
theorem B3397639 : Blo 2011435 3397639 := bstep (se 1 (by rfl) ⟨2548229, by rfl⟩ : syracuseStep 3397639 = 5096459) B5096459
theorem B4530185 : Blo 2011435 4530185 := bstep (se 2 (by rfl) ⟨1698819, by rfl⟩ : syracuseStep 4530185 = 3397639) B3397639
theorem B3020123 : Blo 2011435 3020123 := bstep (se 1 (by rfl) ⟨2265092, by rfl⟩ : syracuseStep 3020123 = 4530185) B4530185
theorem B2013415 : Blo 2011435 2013415 := bstep (se 1 (by rfl) ⟨1510061, by rfl⟩ : syracuseStep 2013415 = 3020123) B3020123
theorem B2265097 : Blo 2011435 2265097 := bbase (se 2 (by rfl) ⟨849411, by rfl⟩ : syracuseStep 2265097 = 1698823) (by norm_num)
theorem B3020129 : Blo 2011435 3020129 := bstep (se 2 (by rfl) ⟨1132548, by rfl⟩ : syracuseStep 3020129 = 2265097) B2265097
theorem B2013419 : Blo 2011435 2013419 := bstep (se 1 (by rfl) ⟨1510064, by rfl⟩ : syracuseStep 2013419 = 3020129) B3020129
theorem B58844117 : Blo 2011435 58844117 := bbase (se 7 (by rfl) ⟨689579, by rfl⟩ : syracuseStep 58844117 = 1379159) (by norm_num)
theorem B156917645 : Blo 2011435 156917645 := bstep (se 3 (by rfl) ⟨29422058, by rfl⟩ : syracuseStep 156917645 = 58844117) B58844117
theorem B104611763 : Blo 2011435 104611763 := bstep (se 1 (by rfl) ⟨78458822, by rfl⟩ : syracuseStep 104611763 = 156917645) B156917645
theorem B69741175 : Blo 2011435 69741175 := bstep (se 1 (by rfl) ⟨52305881, by rfl⟩ : syracuseStep 69741175 = 104611763) B104611763
theorem B92988233 : Blo 2011435 92988233 := bstep (se 2 (by rfl) ⟨34870587, by rfl⟩ : syracuseStep 92988233 = 69741175) B69741175
theorem B61992155 : Blo 2011435 61992155 := bstep (se 1 (by rfl) ⟨46494116, by rfl⟩ : syracuseStep 61992155 = 92988233) B92988233
theorem B165312413 : Blo 2011435 165312413 := bstep (se 3 (by rfl) ⟨30996077, by rfl⟩ : syracuseStep 165312413 = 61992155) B61992155
theorem B110208275 : Blo 2011435 110208275 := bstep (se 1 (by rfl) ⟨82656206, by rfl⟩ : syracuseStep 110208275 = 165312413) B165312413
theorem B73472183 : Blo 2011435 73472183 := bstep (se 1 (by rfl) ⟨55104137, by rfl⟩ : syracuseStep 73472183 = 110208275) B110208275
theorem B48981455 : Blo 2011435 48981455 := bstep (se 1 (by rfl) ⟨36736091, by rfl⟩ : syracuseStep 48981455 = 73472183) B73472183
theorem B32654303 : Blo 2011435 32654303 := bstep (se 1 (by rfl) ⟨24490727, by rfl⟩ : syracuseStep 32654303 = 48981455) B48981455
theorem B21769535 : Blo 2011435 21769535 := bstep (se 1 (by rfl) ⟨16327151, by rfl⟩ : syracuseStep 21769535 = 32654303) B32654303
theorem B14513023 : Blo 2011435 14513023 := bstep (se 1 (by rfl) ⟨10884767, by rfl⟩ : syracuseStep 14513023 = 21769535) B21769535
theorem B19350697 : Blo 2011435 19350697 := bstep (se 2 (by rfl) ⟨7256511, by rfl⟩ : syracuseStep 19350697 = 14513023) B14513023
theorem B25800929 : Blo 2011435 25800929 := bstep (se 2 (by rfl) ⟨9675348, by rfl⟩ : syracuseStep 25800929 = 19350697) B19350697
theorem B17200619 : Blo 2011435 17200619 := bstep (se 1 (by rfl) ⟨12900464, by rfl⟩ : syracuseStep 17200619 = 25800929) B25800929
theorem B11467079 : Blo 2011435 11467079 := bstep (se 1 (by rfl) ⟨8600309, by rfl⟩ : syracuseStep 11467079 = 17200619) B17200619
theorem B7644719 : Blo 2011435 7644719 := bstep (se 1 (by rfl) ⟨5733539, by rfl⟩ : syracuseStep 7644719 = 11467079) B11467079
theorem B5096479 : Blo 2011435 5096479 := bstep (se 1 (by rfl) ⟨3822359, by rfl⟩ : syracuseStep 5096479 = 7644719) B7644719
theorem B6795305 : Blo 2011435 6795305 := bstep (se 2 (by rfl) ⟨2548239, by rfl⟩ : syracuseStep 6795305 = 5096479) B5096479
theorem B4530203 : Blo 2011435 4530203 := bstep (se 1 (by rfl) ⟨3397652, by rfl⟩ : syracuseStep 4530203 = 6795305) B6795305
theorem B3020135 : Blo 2011435 3020135 := bstep (se 1 (by rfl) ⟨2265101, by rfl⟩ : syracuseStep 3020135 = 4530203) B4530203
theorem B2013423 : Blo 2011435 2013423 := bstep (se 1 (by rfl) ⟨1510067, by rfl⟩ : syracuseStep 2013423 = 3020135) B3020135
theorem B3020141 : Blo 2011435 3020141 := bbase (se 3 (by rfl) ⟨566276, by rfl⟩ : syracuseStep 3020141 = 1132553) (by norm_num)
theorem B2013427 : Blo 2011435 2013427 := bstep (se 1 (by rfl) ⟨1510070, by rfl⟩ : syracuseStep 2013427 = 3020141) B3020141
theorem B4530221 : Blo 2011435 4530221 := bbase (se 3 (by rfl) ⟨849416, by rfl⟩ : syracuseStep 4530221 = 1698833) (by norm_num)
theorem B3020147 : Blo 2011435 3020147 := bstep (se 1 (by rfl) ⟨2265110, by rfl⟩ : syracuseStep 3020147 = 4530221) B4530221
theorem B2013431 : Blo 2011435 2013431 := bstep (se 1 (by rfl) ⟨1510073, by rfl⟩ : syracuseStep 2013431 = 3020147) B3020147
theorem B2296021 : Blo 2011435 2296021 := bbase (se 7 (by rfl) ⟨26906, by rfl⟩ : syracuseStep 2296021 = 53813) (by norm_num)
theorem B3061361 : Blo 2011435 3061361 := bstep (se 2 (by rfl) ⟨1148010, by rfl⟩ : syracuseStep 3061361 = 2296021) B2296021
theorem B2040907 : Blo 2011435 2040907 := bstep (se 1 (by rfl) ⟨1530680, by rfl⟩ : syracuseStep 2040907 = 3061361) B3061361
theorem B2721209 : Blo 2011435 2721209 := bstep (se 2 (by rfl) ⟨1020453, by rfl⟩ : syracuseStep 2721209 = 2040907) B2040907
theorem B7256557 : Blo 2011435 7256557 := bstep (se 3 (by rfl) ⟨1360604, by rfl⟩ : syracuseStep 7256557 = 2721209) B2721209
theorem B9675409 : Blo 2011435 9675409 := bstep (se 2 (by rfl) ⟨3628278, by rfl⟩ : syracuseStep 9675409 = 7256557) B7256557
theorem B12900545 : Blo 2011435 12900545 := bstep (se 2 (by rfl) ⟨4837704, by rfl⟩ : syracuseStep 12900545 = 9675409) B9675409
theorem B8600363 : Blo 2011435 8600363 := bstep (se 1 (by rfl) ⟨6450272, by rfl⟩ : syracuseStep 8600363 = 12900545) B12900545
theorem B5733575 : Blo 2011435 5733575 := bstep (se 1 (by rfl) ⟨4300181, by rfl⟩ : syracuseStep 5733575 = 8600363) B8600363
theorem B3822383 : Blo 2011435 3822383 := bstep (se 1 (by rfl) ⟨2866787, by rfl⟩ : syracuseStep 3822383 = 5733575) B5733575
theorem B2548255 : Blo 2011435 2548255 := bstep (se 1 (by rfl) ⟨1911191, by rfl⟩ : syracuseStep 2548255 = 3822383) B3822383
theorem B3397673 : Blo 2011435 3397673 := bstep (se 2 (by rfl) ⟨1274127, by rfl⟩ : syracuseStep 3397673 = 2548255) B2548255
theorem B2265115 : Blo 2011435 2265115 := bstep (se 1 (by rfl) ⟨1698836, by rfl⟩ : syracuseStep 2265115 = 3397673) B3397673
theorem B3020153 : Blo 2011435 3020153 := bstep (se 2 (by rfl) ⟨1132557, by rfl⟩ : syracuseStep 3020153 = 2265115) B2265115
theorem B2013435 : Blo 2011435 2013435 := bstep (se 1 (by rfl) ⟨1510076, by rfl⟩ : syracuseStep 2013435 = 3020153) B3020153
theorem C0 (j : ℕ) (h1 : 502858 ≤ j) (h2 : j ≤ 503358) : Blo 2011435 (4 * j + 3) := by
  interval_cases j
  · exact B2011435
  · exact B2011439
  · exact B2011443
  · exact B2011447
  · exact B2011451
  · exact B2011455
  · exact B2011459
  · exact B2011463
  · exact B2011467
  · exact B2011471
  · exact B2011475
  · exact B2011479
  · exact B2011483
  · exact B2011487
  · exact B2011491
  · exact B2011495
  · exact B2011499
  · exact B2011503
  · exact B2011507
  · exact B2011511
  · exact B2011515
  · exact B2011519
  · exact B2011523
  · exact B2011527
  · exact B2011531
  · exact B2011535
  · exact B2011539
  · exact B2011543
  · exact B2011547
  · exact B2011551
  · exact B2011555
  · exact B2011559
  · exact B2011563
  · exact B2011567
  · exact B2011571
  · exact B2011575
  · exact B2011579
  · exact B2011583
  · exact B2011587
  · exact B2011591
  · exact B2011595
  · exact B2011599
  · exact B2011603
  · exact B2011607
  · exact B2011611
  · exact B2011615
  · exact B2011619
  · exact B2011623
  · exact B2011627
  · exact B2011631
  · exact B2011635
  · exact B2011639
  · exact B2011643
  · exact B2011647
  · exact B2011651
  · exact B2011655
  · exact B2011659
  · exact B2011663
  · exact B2011667
  · exact B2011671
  · exact B2011675
  · exact B2011679
  · exact B2011683
  · exact B2011687
  · exact B2011691
  · exact B2011695
  · exact B2011699
  · exact B2011703
  · exact B2011707
  · exact B2011711
  · exact B2011715
  · exact B2011719
  · exact B2011723
  · exact B2011727
  · exact B2011731
  · exact B2011735
  · exact B2011739
  · exact B2011743
  · exact B2011747
  · exact B2011751
  · exact B2011755
  · exact B2011759
  · exact B2011763
  · exact B2011767
  · exact B2011771
  · exact B2011775
  · exact B2011779
  · exact B2011783
  · exact B2011787
  · exact B2011791
  · exact B2011795
  · exact B2011799
  · exact B2011803
  · exact B2011807
  · exact B2011811
  · exact B2011815
  · exact B2011819
  · exact B2011823
  · exact B2011827
  · exact B2011831
  · exact B2011835
  · exact B2011839
  · exact B2011843
  · exact B2011847
  · exact B2011851
  · exact B2011855
  · exact B2011859
  · exact B2011863
  · exact B2011867
  · exact B2011871
  · exact B2011875
  · exact B2011879
  · exact B2011883
  · exact B2011887
  · exact B2011891
  · exact B2011895
  · exact B2011899
  · exact B2011903
  · exact B2011907
  · exact B2011911
  · exact B2011915
  · exact B2011919
  · exact B2011923
  · exact B2011927
  · exact B2011931
  · exact B2011935
  · exact B2011939
  · exact B2011943
  · exact B2011947
  · exact B2011951
  · exact B2011955
  · exact B2011959
  · exact B2011963
  · exact B2011967
  · exact B2011971
  · exact B2011975
  · exact B2011979
  · exact B2011983
  · exact B2011987
  · exact B2011991
  · exact B2011995
  · exact B2011999
  · exact B2012003
  · exact B2012007
  · exact B2012011
  · exact B2012015
  · exact B2012019
  · exact B2012023
  · exact B2012027
  · exact B2012031
  · exact B2012035
  · exact B2012039
  · exact B2012043
  · exact B2012047
  · exact B2012051
  · exact B2012055
  · exact B2012059
  · exact B2012063
  · exact B2012067
  · exact B2012071
  · exact B2012075
  · exact B2012079
  · exact B2012083
  · exact B2012087
  · exact B2012091
  · exact B2012095
  · exact B2012099
  · exact B2012103
  · exact B2012107
  · exact B2012111
  · exact B2012115
  · exact B2012119
  · exact B2012123
  · exact B2012127
  · exact B2012131
  · exact B2012135
  · exact B2012139
  · exact B2012143
  · exact B2012147
  · exact B2012151
  · exact B2012155
  · exact B2012159
  · exact B2012163
  · exact B2012167
  · exact B2012171
  · exact B2012175
  · exact B2012179
  · exact B2012183
  · exact B2012187
  · exact B2012191
  · exact B2012195
  · exact B2012199
  · exact B2012203
  · exact B2012207
  · exact B2012211
  · exact B2012215
  · exact B2012219
  · exact B2012223
  · exact B2012227
  · exact B2012231
  · exact B2012235
  · exact B2012239
  · exact B2012243
  · exact B2012247
  · exact B2012251
  · exact B2012255
  · exact B2012259
  · exact B2012263
  · exact B2012267
  · exact B2012271
  · exact B2012275
  · exact B2012279
  · exact B2012283
  · exact B2012287
  · exact B2012291
  · exact B2012295
  · exact B2012299
  · exact B2012303
  · exact B2012307
  · exact B2012311
  · exact B2012315
  · exact B2012319
  · exact B2012323
  · exact B2012327
  · exact B2012331
  · exact B2012335
  · exact B2012339
  · exact B2012343
  · exact B2012347
  · exact B2012351
  · exact B2012355
  · exact B2012359
  · exact B2012363
  · exact B2012367
  · exact B2012371
  · exact B2012375
  · exact B2012379
  · exact B2012383
  · exact B2012387
  · exact B2012391
  · exact B2012395
  · exact B2012399
  · exact B2012403
  · exact B2012407
  · exact B2012411
  · exact B2012415
  · exact B2012419
  · exact B2012423
  · exact B2012427
  · exact B2012431
  · exact B2012435
  · exact B2012439
  · exact B2012443
  · exact B2012447
  · exact B2012451
  · exact B2012455
  · exact B2012459
  · exact B2012463
  · exact B2012467
  · exact B2012471
  · exact B2012475
  · exact B2012479
  · exact B2012483
  · exact B2012487
  · exact B2012491
  · exact B2012495
  · exact B2012499
  · exact B2012503
  · exact B2012507
  · exact B2012511
  · exact B2012515
  · exact B2012519
  · exact B2012523
  · exact B2012527
  · exact B2012531
  · exact B2012535
  · exact B2012539
  · exact B2012543
  · exact B2012547
  · exact B2012551
  · exact B2012555
  · exact B2012559
  · exact B2012563
  · exact B2012567
  · exact B2012571
  · exact B2012575
  · exact B2012579
  · exact B2012583
  · exact B2012587
  · exact B2012591
  · exact B2012595
  · exact B2012599
  · exact B2012603
  · exact B2012607
  · exact B2012611
  · exact B2012615
  · exact B2012619
  · exact B2012623
  · exact B2012627
  · exact B2012631
  · exact B2012635
  · exact B2012639
  · exact B2012643
  · exact B2012647
  · exact B2012651
  · exact B2012655
  · exact B2012659
  · exact B2012663
  · exact B2012667
  · exact B2012671
  · exact B2012675
  · exact B2012679
  · exact B2012683
  · exact B2012687
  · exact B2012691
  · exact B2012695
  · exact B2012699
  · exact B2012703
  · exact B2012707
  · exact B2012711
  · exact B2012715
  · exact B2012719
  · exact B2012723
  · exact B2012727
  · exact B2012731
  · exact B2012735
  · exact B2012739
  · exact B2012743
  · exact B2012747
  · exact B2012751
  · exact B2012755
  · exact B2012759
  · exact B2012763
  · exact B2012767
  · exact B2012771
  · exact B2012775
  · exact B2012779
  · exact B2012783
  · exact B2012787
  · exact B2012791
  · exact B2012795
  · exact B2012799
  · exact B2012803
  · exact B2012807
  · exact B2012811
  · exact B2012815
  · exact B2012819
  · exact B2012823
  · exact B2012827
  · exact B2012831
  · exact B2012835
  · exact B2012839
  · exact B2012843
  · exact B2012847
  · exact B2012851
  · exact B2012855
  · exact B2012859
  · exact B2012863
  · exact B2012867
  · exact B2012871
  · exact B2012875
  · exact B2012879
  · exact B2012883
  · exact B2012887
  · exact B2012891
  · exact B2012895
  · exact B2012899
  · exact B2012903
  · exact B2012907
  · exact B2012911
  · exact B2012915
  · exact B2012919
  · exact B2012923
  · exact B2012927
  · exact B2012931
  · exact B2012935
  · exact B2012939
  · exact B2012943
  · exact B2012947
  · exact B2012951
  · exact B2012955
  · exact B2012959
  · exact B2012963
  · exact B2012967
  · exact B2012971
  · exact B2012975
  · exact B2012979
  · exact B2012983
  · exact B2012987
  · exact B2012991
  · exact B2012995
  · exact B2012999
  · exact B2013003
  · exact B2013007
  · exact B2013011
  · exact B2013015
  · exact B2013019
  · exact B2013023
  · exact B2013027
  · exact B2013031
  · exact B2013035
  · exact B2013039
  · exact B2013043
  · exact B2013047
  · exact B2013051
  · exact B2013055
  · exact B2013059
  · exact B2013063
  · exact B2013067
  · exact B2013071
  · exact B2013075
  · exact B2013079
  · exact B2013083
  · exact B2013087
  · exact B2013091
  · exact B2013095
  · exact B2013099
  · exact B2013103
  · exact B2013107
  · exact B2013111
  · exact B2013115
  · exact B2013119
  · exact B2013123
  · exact B2013127
  · exact B2013131
  · exact B2013135
  · exact B2013139
  · exact B2013143
  · exact B2013147
  · exact B2013151
  · exact B2013155
  · exact B2013159
  · exact B2013163
  · exact B2013167
  · exact B2013171
  · exact B2013175
  · exact B2013179
  · exact B2013183
  · exact B2013187
  · exact B2013191
  · exact B2013195
  · exact B2013199
  · exact B2013203
  · exact B2013207
  · exact B2013211
  · exact B2013215
  · exact B2013219
  · exact B2013223
  · exact B2013227
  · exact B2013231
  · exact B2013235
  · exact B2013239
  · exact B2013243
  · exact B2013247
  · exact B2013251
  · exact B2013255
  · exact B2013259
  · exact B2013263
  · exact B2013267
  · exact B2013271
  · exact B2013275
  · exact B2013279
  · exact B2013283
  · exact B2013287
  · exact B2013291
  · exact B2013295
  · exact B2013299
  · exact B2013303
  · exact B2013307
  · exact B2013311
  · exact B2013315
  · exact B2013319
  · exact B2013323
  · exact B2013327
  · exact B2013331
  · exact B2013335
  · exact B2013339
  · exact B2013343
  · exact B2013347
  · exact B2013351
  · exact B2013355
  · exact B2013359
  · exact B2013363
  · exact B2013367
  · exact B2013371
  · exact B2013375
  · exact B2013379
  · exact B2013383
  · exact B2013387
  · exact B2013391
  · exact B2013395
  · exact B2013399
  · exact B2013403
  · exact B2013407
  · exact B2013411
  · exact B2013415
  · exact B2013419
  · exact B2013423
  · exact B2013427
  · exact B2013431
  · exact B2013435
theorem solution (m : ℕ) (hlo : 2011435 ≤ m) (hhi : m ≤ 2013435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 502858 ≤ j := by omega
    have hj2 : j ≤ 503358 := by omega
    have hb : Blo 2011435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
