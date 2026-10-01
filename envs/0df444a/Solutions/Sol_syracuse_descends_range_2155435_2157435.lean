-- Prove2me | solution 1 for syracuse_descends_range_2155435_2157435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:32.245923+00:00
-- url     : https://prove2.me/submissions/94c4213f-8a23-485b-a9ea-4af688ad615c

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

theorem B2424865 : Blo 2155435 2424865 := bbase (se 2 (by rfl) ⟨909324, by rfl⟩ : syracuseStep 2424865 = 1818649) (by norm_num)
theorem B3233153 : Blo 2155435 3233153 := bstep (se 2 (by rfl) ⟨1212432, by rfl⟩ : syracuseStep 3233153 = 2424865) B2424865
theorem B2155435 : Blo 2155435 2155435 := bstep (se 1 (by rfl) ⟨1616576, by rfl⟩ : syracuseStep 2155435 = 3233153) B3233153
theorem B5455957 : Blo 2155435 5455957 := bbase (se 8 (by rfl) ⟨31968, by rfl⟩ : syracuseStep 5455957 = 63937) (by norm_num)
theorem B7274609 : Blo 2155435 7274609 := bstep (se 2 (by rfl) ⟨2727978, by rfl⟩ : syracuseStep 7274609 = 5455957) B5455957
theorem B4849739 : Blo 2155435 4849739 := bstep (se 1 (by rfl) ⟨3637304, by rfl⟩ : syracuseStep 4849739 = 7274609) B7274609
theorem B3233159 : Blo 2155435 3233159 := bstep (se 1 (by rfl) ⟨2424869, by rfl⟩ : syracuseStep 3233159 = 4849739) B4849739
theorem B2155439 : Blo 2155435 2155439 := bstep (se 1 (by rfl) ⟨1616579, by rfl⟩ : syracuseStep 2155439 = 3233159) B3233159
theorem B3233165 : Blo 2155435 3233165 := bbase (se 3 (by rfl) ⟨606218, by rfl⟩ : syracuseStep 3233165 = 1212437) (by norm_num)
theorem B2155443 : Blo 2155435 2155443 := bstep (se 1 (by rfl) ⟨1616582, by rfl⟩ : syracuseStep 2155443 = 3233165) B3233165
theorem B4849757 : Blo 2155435 4849757 := bbase (se 3 (by rfl) ⟨909329, by rfl⟩ : syracuseStep 4849757 = 1818659) (by norm_num)
theorem B3233171 : Blo 2155435 3233171 := bstep (se 1 (by rfl) ⟨2424878, by rfl⟩ : syracuseStep 3233171 = 4849757) B4849757
theorem B2155447 : Blo 2155435 2155447 := bstep (se 1 (by rfl) ⟨1616585, by rfl⟩ : syracuseStep 2155447 = 3233171) B3233171
theorem B3637325 : Blo 2155435 3637325 := bbase (se 3 (by rfl) ⟨681998, by rfl⟩ : syracuseStep 3637325 = 1363997) (by norm_num)
theorem B2424883 : Blo 2155435 2424883 := bstep (se 1 (by rfl) ⟨1818662, by rfl⟩ : syracuseStep 2424883 = 3637325) B3637325
theorem B3233177 : Blo 2155435 3233177 := bstep (se 2 (by rfl) ⟨1212441, by rfl⟩ : syracuseStep 3233177 = 2424883) B2424883
theorem B2155451 : Blo 2155435 2155451 := bstep (se 1 (by rfl) ⟨1616588, by rfl⟩ : syracuseStep 2155451 = 3233177) B3233177
theorem B2624797 : Blo 2155435 2624797 := bbase (se 3 (by rfl) ⟨492149, by rfl⟩ : syracuseStep 2624797 = 984299) (by norm_num)
theorem B13998917 : Blo 2155435 13998917 := bstep (se 4 (by rfl) ⟨1312398, by rfl⟩ : syracuseStep 13998917 = 2624797) B2624797
theorem B37330445 : Blo 2155435 37330445 := bstep (se 3 (by rfl) ⟨6999458, by rfl⟩ : syracuseStep 37330445 = 13998917) B13998917
theorem B24886963 : Blo 2155435 24886963 := bstep (se 1 (by rfl) ⟨18665222, by rfl⟩ : syracuseStep 24886963 = 37330445) B37330445
theorem B33182617 : Blo 2155435 33182617 := bstep (se 2 (by rfl) ⟨12443481, by rfl⟩ : syracuseStep 33182617 = 24886963) B24886963
theorem B44243489 : Blo 2155435 44243489 := bstep (se 2 (by rfl) ⟨16591308, by rfl⟩ : syracuseStep 44243489 = 33182617) B33182617
theorem B29495659 : Blo 2155435 29495659 := bstep (se 1 (by rfl) ⟨22121744, by rfl⟩ : syracuseStep 29495659 = 44243489) B44243489
theorem B39327545 : Blo 2155435 39327545 := bstep (se 2 (by rfl) ⟨14747829, by rfl⟩ : syracuseStep 39327545 = 29495659) B29495659
theorem B104873453 : Blo 2155435 104873453 := bstep (se 3 (by rfl) ⟨19663772, by rfl⟩ : syracuseStep 104873453 = 39327545) B39327545
theorem B69915635 : Blo 2155435 69915635 := bstep (se 1 (by rfl) ⟨52436726, by rfl⟩ : syracuseStep 69915635 = 104873453) B104873453
theorem B46610423 : Blo 2155435 46610423 := bstep (se 1 (by rfl) ⟨34957817, by rfl⟩ : syracuseStep 46610423 = 69915635) B69915635
theorem B31073615 : Blo 2155435 31073615 := bstep (se 1 (by rfl) ⟨23305211, by rfl⟩ : syracuseStep 31073615 = 46610423) B46610423
theorem B20715743 : Blo 2155435 20715743 := bstep (se 1 (by rfl) ⟨15536807, by rfl⟩ : syracuseStep 20715743 = 31073615) B31073615
theorem B13810495 : Blo 2155435 13810495 := bstep (se 1 (by rfl) ⟨10357871, by rfl⟩ : syracuseStep 13810495 = 20715743) B20715743
theorem B18413993 : Blo 2155435 18413993 := bstep (se 2 (by rfl) ⟨6905247, by rfl⟩ : syracuseStep 18413993 = 13810495) B13810495
theorem B12275995 : Blo 2155435 12275995 := bstep (se 1 (by rfl) ⟨9206996, by rfl⟩ : syracuseStep 12275995 = 18413993) B18413993
theorem B16367993 : Blo 2155435 16367993 := bstep (se 2 (by rfl) ⟨6137997, by rfl⟩ : syracuseStep 16367993 = 12275995) B12275995
theorem B10911995 : Blo 2155435 10911995 := bstep (se 1 (by rfl) ⟨8183996, by rfl⟩ : syracuseStep 10911995 = 16367993) B16367993
theorem B7274663 : Blo 2155435 7274663 := bstep (se 1 (by rfl) ⟨5455997, by rfl⟩ : syracuseStep 7274663 = 10911995) B10911995
theorem B4849775 : Blo 2155435 4849775 := bstep (se 1 (by rfl) ⟨3637331, by rfl⟩ : syracuseStep 4849775 = 7274663) B7274663
theorem B3233183 : Blo 2155435 3233183 := bstep (se 1 (by rfl) ⟨2424887, by rfl⟩ : syracuseStep 3233183 = 4849775) B4849775
theorem B2155455 : Blo 2155435 2155455 := bstep (se 1 (by rfl) ⟨1616591, by rfl⟩ : syracuseStep 2155455 = 3233183) B3233183
theorem B3233189 : Blo 2155435 3233189 := bbase (se 4 (by rfl) ⟨303111, by rfl⟩ : syracuseStep 3233189 = 606223) (by norm_num)
theorem B2155459 : Blo 2155435 2155459 := bstep (se 1 (by rfl) ⟨1616594, by rfl⟩ : syracuseStep 2155459 = 3233189) B3233189
theorem B2728009 : Blo 2155435 2728009 := bbase (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) (by norm_num)
theorem B3637345 : Blo 2155435 3637345 := bstep (se 2 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 3637345 = 2728009) B2728009
theorem B4849793 : Blo 2155435 4849793 := bstep (se 2 (by rfl) ⟨1818672, by rfl⟩ : syracuseStep 4849793 = 3637345) B3637345
theorem B3233195 : Blo 2155435 3233195 := bstep (se 1 (by rfl) ⟨2424896, by rfl⟩ : syracuseStep 3233195 = 4849793) B4849793
theorem B2155463 : Blo 2155435 2155463 := bstep (se 1 (by rfl) ⟨1616597, by rfl⟩ : syracuseStep 2155463 = 3233195) B3233195
theorem B2424901 : Blo 2155435 2424901 := bbase (se 4 (by rfl) ⟨227334, by rfl⟩ : syracuseStep 2424901 = 454669) (by norm_num)
theorem B3233201 : Blo 2155435 3233201 := bstep (se 2 (by rfl) ⟨1212450, by rfl⟩ : syracuseStep 3233201 = 2424901) B2424901
theorem B2155467 : Blo 2155435 2155467 := bstep (se 1 (by rfl) ⟨1616600, by rfl⟩ : syracuseStep 2155467 = 3233201) B3233201
theorem B4092029 : Blo 2155435 4092029 := bbase (se 3 (by rfl) ⟨767255, by rfl⟩ : syracuseStep 4092029 = 1534511) (by norm_num)
theorem B2728019 : Blo 2155435 2728019 := bstep (se 1 (by rfl) ⟨2046014, by rfl⟩ : syracuseStep 2728019 = 4092029) B4092029
theorem B7274717 : Blo 2155435 7274717 := bstep (se 3 (by rfl) ⟨1364009, by rfl⟩ : syracuseStep 7274717 = 2728019) B2728019
theorem B4849811 : Blo 2155435 4849811 := bstep (se 1 (by rfl) ⟨3637358, by rfl⟩ : syracuseStep 4849811 = 7274717) B7274717
theorem B3233207 : Blo 2155435 3233207 := bstep (se 1 (by rfl) ⟨2424905, by rfl⟩ : syracuseStep 3233207 = 4849811) B4849811
theorem B2155471 : Blo 2155435 2155471 := bstep (se 1 (by rfl) ⟨1616603, by rfl⟩ : syracuseStep 2155471 = 3233207) B3233207
theorem B3233213 : Blo 2155435 3233213 := bbase (se 3 (by rfl) ⟨606227, by rfl⟩ : syracuseStep 3233213 = 1212455) (by norm_num)
theorem B2155475 : Blo 2155435 2155475 := bstep (se 1 (by rfl) ⟨1616606, by rfl⟩ : syracuseStep 2155475 = 3233213) B3233213
theorem B4849829 : Blo 2155435 4849829 := bbase (se 4 (by rfl) ⟨454671, by rfl⟩ : syracuseStep 4849829 = 909343) (by norm_num)
theorem B3233219 : Blo 2155435 3233219 := bstep (se 1 (by rfl) ⟨2424914, by rfl⟩ : syracuseStep 3233219 = 4849829) B4849829
theorem B2155479 : Blo 2155435 2155479 := bstep (se 1 (by rfl) ⟨1616609, by rfl⟩ : syracuseStep 2155479 = 3233219) B3233219
theorem B5456069 : Blo 2155435 5456069 := bbase (se 4 (by rfl) ⟨511506, by rfl⟩ : syracuseStep 5456069 = 1023013) (by norm_num)
theorem B3637379 : Blo 2155435 3637379 := bstep (se 1 (by rfl) ⟨2728034, by rfl⟩ : syracuseStep 3637379 = 5456069) B5456069
theorem B2424919 : Blo 2155435 2424919 := bstep (se 1 (by rfl) ⟨1818689, by rfl⟩ : syracuseStep 2424919 = 3637379) B3637379
theorem B3233225 : Blo 2155435 3233225 := bstep (se 2 (by rfl) ⟨1212459, by rfl⟩ : syracuseStep 3233225 = 2424919) B2424919
theorem B2155483 : Blo 2155435 2155483 := bstep (se 1 (by rfl) ⟨1616612, by rfl⟩ : syracuseStep 2155483 = 3233225) B3233225
theorem B2458009 : Blo 2155435 2458009 := bbase (se 2 (by rfl) ⟨921753, by rfl⟩ : syracuseStep 2458009 = 1843507) (by norm_num)
theorem B3277345 : Blo 2155435 3277345 := bstep (se 2 (by rfl) ⟨1229004, by rfl⟩ : syracuseStep 3277345 = 2458009) B2458009
theorem B4369793 : Blo 2155435 4369793 := bstep (se 2 (by rfl) ⟨1638672, by rfl⟩ : syracuseStep 4369793 = 3277345) B3277345
theorem B11652781 : Blo 2155435 11652781 := bstep (se 3 (by rfl) ⟨2184896, by rfl⟩ : syracuseStep 11652781 = 4369793) B4369793
theorem B15537041 : Blo 2155435 15537041 := bstep (se 2 (by rfl) ⟨5826390, by rfl⟩ : syracuseStep 15537041 = 11652781) B11652781
theorem B10358027 : Blo 2155435 10358027 := bstep (se 1 (by rfl) ⟨7768520, by rfl⟩ : syracuseStep 10358027 = 15537041) B15537041
theorem B6905351 : Blo 2155435 6905351 := bstep (se 1 (by rfl) ⟨5179013, by rfl⟩ : syracuseStep 6905351 = 10358027) B10358027
theorem B4603567 : Blo 2155435 4603567 := bstep (se 1 (by rfl) ⟨3452675, by rfl⟩ : syracuseStep 4603567 = 6905351) B6905351
theorem B6138089 : Blo 2155435 6138089 := bstep (se 2 (by rfl) ⟨2301783, by rfl⟩ : syracuseStep 6138089 = 4603567) B4603567
theorem B4092059 : Blo 2155435 4092059 := bstep (se 1 (by rfl) ⟨3069044, by rfl⟩ : syracuseStep 4092059 = 6138089) B6138089
theorem B10912157 : Blo 2155435 10912157 := bstep (se 3 (by rfl) ⟨2046029, by rfl⟩ : syracuseStep 10912157 = 4092059) B4092059
theorem B7274771 : Blo 2155435 7274771 := bstep (se 1 (by rfl) ⟨5456078, by rfl⟩ : syracuseStep 7274771 = 10912157) B10912157
theorem B4849847 : Blo 2155435 4849847 := bstep (se 1 (by rfl) ⟨3637385, by rfl⟩ : syracuseStep 4849847 = 7274771) B7274771
theorem B3233231 : Blo 2155435 3233231 := bstep (se 1 (by rfl) ⟨2424923, by rfl⟩ : syracuseStep 3233231 = 4849847) B4849847
theorem B2155487 : Blo 2155435 2155487 := bstep (se 1 (by rfl) ⟨1616615, by rfl⟩ : syracuseStep 2155487 = 3233231) B3233231
theorem B3233237 : Blo 2155435 3233237 := bbase (se 7 (by rfl) ⟨37889, by rfl⟩ : syracuseStep 3233237 = 75779) (by norm_num)
theorem B2155491 : Blo 2155435 2155491 := bstep (se 1 (by rfl) ⟨1616618, by rfl⟩ : syracuseStep 2155491 = 3233237) B3233237
theorem B8184149 : Blo 2155435 8184149 := bbase (se 10 (by rfl) ⟨11988, by rfl⟩ : syracuseStep 8184149 = 23977) (by norm_num)
theorem B5456099 : Blo 2155435 5456099 := bstep (se 1 (by rfl) ⟨4092074, by rfl⟩ : syracuseStep 5456099 = 8184149) B8184149
theorem B3637399 : Blo 2155435 3637399 := bstep (se 1 (by rfl) ⟨2728049, by rfl⟩ : syracuseStep 3637399 = 5456099) B5456099
theorem B4849865 : Blo 2155435 4849865 := bstep (se 2 (by rfl) ⟨1818699, by rfl⟩ : syracuseStep 4849865 = 3637399) B3637399
theorem B3233243 : Blo 2155435 3233243 := bstep (se 1 (by rfl) ⟨2424932, by rfl⟩ : syracuseStep 3233243 = 4849865) B4849865
theorem B2155495 : Blo 2155435 2155495 := bstep (se 1 (by rfl) ⟨1616621, by rfl⟩ : syracuseStep 2155495 = 3233243) B3233243
theorem B2424937 : Blo 2155435 2424937 := bbase (se 2 (by rfl) ⟨909351, by rfl⟩ : syracuseStep 2424937 = 1818703) (by norm_num)
theorem B3233249 : Blo 2155435 3233249 := bstep (se 2 (by rfl) ⟨1212468, by rfl⟩ : syracuseStep 3233249 = 2424937) B2424937
theorem B2155499 : Blo 2155435 2155499 := bstep (se 1 (by rfl) ⟨1616624, by rfl⟩ : syracuseStep 2155499 = 3233249) B3233249
theorem B3452701 : Blo 2155435 3452701 := bbase (se 3 (by rfl) ⟨647381, by rfl⟩ : syracuseStep 3452701 = 1294763) (by norm_num)
theorem B4603601 : Blo 2155435 4603601 := bstep (se 2 (by rfl) ⟨1726350, by rfl⟩ : syracuseStep 4603601 = 3452701) B3452701
theorem B12276269 : Blo 2155435 12276269 := bstep (se 3 (by rfl) ⟨2301800, by rfl⟩ : syracuseStep 12276269 = 4603601) B4603601
theorem B8184179 : Blo 2155435 8184179 := bstep (se 1 (by rfl) ⟨6138134, by rfl⟩ : syracuseStep 8184179 = 12276269) B12276269
theorem B5456119 : Blo 2155435 5456119 := bstep (se 1 (by rfl) ⟨4092089, by rfl⟩ : syracuseStep 5456119 = 8184179) B8184179
theorem B7274825 : Blo 2155435 7274825 := bstep (se 2 (by rfl) ⟨2728059, by rfl⟩ : syracuseStep 7274825 = 5456119) B5456119
theorem B4849883 : Blo 2155435 4849883 := bstep (se 1 (by rfl) ⟨3637412, by rfl⟩ : syracuseStep 4849883 = 7274825) B7274825
theorem B3233255 : Blo 2155435 3233255 := bstep (se 1 (by rfl) ⟨2424941, by rfl⟩ : syracuseStep 3233255 = 4849883) B4849883
theorem B2155503 : Blo 2155435 2155503 := bstep (se 1 (by rfl) ⟨1616627, by rfl⟩ : syracuseStep 2155503 = 3233255) B3233255
theorem B3233261 : Blo 2155435 3233261 := bbase (se 3 (by rfl) ⟨606236, by rfl⟩ : syracuseStep 3233261 = 1212473) (by norm_num)
theorem B2155507 : Blo 2155435 2155507 := bstep (se 1 (by rfl) ⟨1616630, by rfl⟩ : syracuseStep 2155507 = 3233261) B3233261
theorem B4849901 : Blo 2155435 4849901 := bbase (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) (by norm_num)
theorem B3233267 : Blo 2155435 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B2155511 : Blo 2155435 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B3069085 : Blo 2155435 3069085 := bbase (se 3 (by rfl) ⟨575453, by rfl⟩ : syracuseStep 3069085 = 1150907) (by norm_num)
theorem B4092113 : Blo 2155435 4092113 := bstep (se 2 (by rfl) ⟨1534542, by rfl⟩ : syracuseStep 4092113 = 3069085) B3069085
theorem B2728075 : Blo 2155435 2728075 := bstep (se 1 (by rfl) ⟨2046056, by rfl⟩ : syracuseStep 2728075 = 4092113) B4092113
theorem B3637433 : Blo 2155435 3637433 := bstep (se 2 (by rfl) ⟨1364037, by rfl⟩ : syracuseStep 3637433 = 2728075) B2728075
theorem B2424955 : Blo 2155435 2424955 := bstep (se 1 (by rfl) ⟨1818716, by rfl⟩ : syracuseStep 2424955 = 3637433) B3637433
theorem B3233273 : Blo 2155435 3233273 := bstep (se 2 (by rfl) ⟨1212477, by rfl⟩ : syracuseStep 3233273 = 2424955) B2424955
theorem B2155515 : Blo 2155435 2155515 := bstep (se 1 (by rfl) ⟨1616636, by rfl⟩ : syracuseStep 2155515 = 3233273) B3233273
theorem B3884317 : Blo 2155435 3884317 := bbase (se 3 (by rfl) ⟨728309, by rfl⟩ : syracuseStep 3884317 = 1456619) (by norm_num)
theorem B82865429 : Blo 2155435 82865429 := bstep (se 6 (by rfl) ⟨1942158, by rfl⟩ : syracuseStep 82865429 = 3884317) B3884317
theorem B55243619 : Blo 2155435 55243619 := bstep (se 1 (by rfl) ⟨41432714, by rfl⟩ : syracuseStep 55243619 = 82865429) B82865429
theorem B36829079 : Blo 2155435 36829079 := bstep (se 1 (by rfl) ⟨27621809, by rfl⟩ : syracuseStep 36829079 = 55243619) B55243619
theorem B24552719 : Blo 2155435 24552719 := bstep (se 1 (by rfl) ⟨18414539, by rfl⟩ : syracuseStep 24552719 = 36829079) B36829079
theorem B16368479 : Blo 2155435 16368479 := bstep (se 1 (by rfl) ⟨12276359, by rfl⟩ : syracuseStep 16368479 = 24552719) B24552719
theorem B10912319 : Blo 2155435 10912319 := bstep (se 1 (by rfl) ⟨8184239, by rfl⟩ : syracuseStep 10912319 = 16368479) B16368479
theorem B7274879 : Blo 2155435 7274879 := bstep (se 1 (by rfl) ⟨5456159, by rfl⟩ : syracuseStep 7274879 = 10912319) B10912319
theorem B4849919 : Blo 2155435 4849919 := bstep (se 1 (by rfl) ⟨3637439, by rfl⟩ : syracuseStep 4849919 = 7274879) B7274879
theorem B3233279 : Blo 2155435 3233279 := bstep (se 1 (by rfl) ⟨2424959, by rfl⟩ : syracuseStep 3233279 = 4849919) B4849919
theorem B2155519 : Blo 2155435 2155519 := bstep (se 1 (by rfl) ⟨1616639, by rfl⟩ : syracuseStep 2155519 = 3233279) B3233279
theorem B3233285 : Blo 2155435 3233285 := bbase (se 4 (by rfl) ⟨303120, by rfl⟩ : syracuseStep 3233285 = 606241) (by norm_num)
theorem B2155523 : Blo 2155435 2155523 := bstep (se 1 (by rfl) ⟨1616642, by rfl⟩ : syracuseStep 2155523 = 3233285) B3233285
theorem B3637453 : Blo 2155435 3637453 := bbase (se 3 (by rfl) ⟨682022, by rfl⟩ : syracuseStep 3637453 = 1364045) (by norm_num)
theorem B4849937 : Blo 2155435 4849937 := bstep (se 2 (by rfl) ⟨1818726, by rfl⟩ : syracuseStep 4849937 = 3637453) B3637453
theorem B3233291 : Blo 2155435 3233291 := bstep (se 1 (by rfl) ⟨2424968, by rfl⟩ : syracuseStep 3233291 = 4849937) B4849937
theorem B2155527 : Blo 2155435 2155527 := bstep (se 1 (by rfl) ⟨1616645, by rfl⟩ : syracuseStep 2155527 = 3233291) B3233291
theorem B2424973 : Blo 2155435 2424973 := bbase (se 3 (by rfl) ⟨454682, by rfl⟩ : syracuseStep 2424973 = 909365) (by norm_num)
theorem B3233297 : Blo 2155435 3233297 := bstep (se 2 (by rfl) ⟨1212486, by rfl⟩ : syracuseStep 3233297 = 2424973) B2424973
theorem B2155531 : Blo 2155435 2155531 := bstep (se 1 (by rfl) ⟨1616648, by rfl⟩ : syracuseStep 2155531 = 3233297) B3233297
theorem B7274933 : Blo 2155435 7274933 := bbase (se 5 (by rfl) ⟨341012, by rfl⟩ : syracuseStep 7274933 = 682025) (by norm_num)
theorem B4849955 : Blo 2155435 4849955 := bstep (se 1 (by rfl) ⟨3637466, by rfl⟩ : syracuseStep 4849955 = 7274933) B7274933
theorem B3233303 : Blo 2155435 3233303 := bstep (se 1 (by rfl) ⟨2424977, by rfl⟩ : syracuseStep 3233303 = 4849955) B4849955
theorem B2155535 : Blo 2155435 2155535 := bstep (se 1 (by rfl) ⟨1616651, by rfl⟩ : syracuseStep 2155535 = 3233303) B3233303
theorem B3233309 : Blo 2155435 3233309 := bbase (se 3 (by rfl) ⟨606245, by rfl⟩ : syracuseStep 3233309 = 1212491) (by norm_num)
theorem B2155539 : Blo 2155435 2155539 := bstep (se 1 (by rfl) ⟨1616654, by rfl⟩ : syracuseStep 2155539 = 3233309) B3233309
theorem B4849973 : Blo 2155435 4849973 := bbase (se 5 (by rfl) ⟨227342, by rfl⟩ : syracuseStep 4849973 = 454685) (by norm_num)
theorem B3233315 : Blo 2155435 3233315 := bstep (se 1 (by rfl) ⟨2424986, by rfl⟩ : syracuseStep 3233315 = 4849973) B4849973
theorem B2155543 : Blo 2155435 2155543 := bstep (se 1 (by rfl) ⟨1616657, by rfl⟩ : syracuseStep 2155543 = 3233315) B3233315
theorem B8739829 : Blo 2155435 8739829 := bbase (se 5 (by rfl) ⟨409679, by rfl⟩ : syracuseStep 8739829 = 819359) (by norm_num)
theorem B46612421 : Blo 2155435 46612421 := bstep (se 4 (by rfl) ⟨4369914, by rfl⟩ : syracuseStep 46612421 = 8739829) B8739829
theorem B31074947 : Blo 2155435 31074947 := bstep (se 1 (by rfl) ⟨23306210, by rfl⟩ : syracuseStep 31074947 = 46612421) B46612421
theorem B20716631 : Blo 2155435 20716631 := bstep (se 1 (by rfl) ⟨15537473, by rfl⟩ : syracuseStep 20716631 = 31074947) B31074947
theorem B13811087 : Blo 2155435 13811087 := bstep (se 1 (by rfl) ⟨10358315, by rfl⟩ : syracuseStep 13811087 = 20716631) B20716631
theorem B9207391 : Blo 2155435 9207391 := bstep (se 1 (by rfl) ⟨6905543, by rfl⟩ : syracuseStep 9207391 = 13811087) B13811087
theorem B12276521 : Blo 2155435 12276521 := bstep (se 2 (by rfl) ⟨4603695, by rfl⟩ : syracuseStep 12276521 = 9207391) B9207391
theorem B8184347 : Blo 2155435 8184347 := bstep (se 1 (by rfl) ⟨6138260, by rfl⟩ : syracuseStep 8184347 = 12276521) B12276521
theorem B5456231 : Blo 2155435 5456231 := bstep (se 1 (by rfl) ⟨4092173, by rfl⟩ : syracuseStep 5456231 = 8184347) B8184347
theorem B3637487 : Blo 2155435 3637487 := bstep (se 1 (by rfl) ⟨2728115, by rfl⟩ : syracuseStep 3637487 = 5456231) B5456231
theorem B2424991 : Blo 2155435 2424991 := bstep (se 1 (by rfl) ⟨1818743, by rfl⟩ : syracuseStep 2424991 = 3637487) B3637487
theorem B3233321 : Blo 2155435 3233321 := bstep (se 2 (by rfl) ⟨1212495, by rfl⟩ : syracuseStep 3233321 = 2424991) B2424991
theorem B2155547 : Blo 2155435 2155547 := bstep (se 1 (by rfl) ⟨1616660, by rfl⟩ : syracuseStep 2155547 = 3233321) B3233321
theorem B9832325 : Blo 2155435 9832325 := bbase (se 4 (by rfl) ⟨921780, by rfl⟩ : syracuseStep 9832325 = 1843561) (by norm_num)
theorem B26219533 : Blo 2155435 26219533 := bstep (se 3 (by rfl) ⟨4916162, by rfl⟩ : syracuseStep 26219533 = 9832325) B9832325
theorem B34959377 : Blo 2155435 34959377 := bstep (se 2 (by rfl) ⟨13109766, by rfl⟩ : syracuseStep 34959377 = 26219533) B26219533
theorem B23306251 : Blo 2155435 23306251 := bstep (se 1 (by rfl) ⟨17479688, by rfl⟩ : syracuseStep 23306251 = 34959377) B34959377
theorem B31075001 : Blo 2155435 31075001 := bstep (se 2 (by rfl) ⟨11653125, by rfl⟩ : syracuseStep 31075001 = 23306251) B23306251
theorem B20716667 : Blo 2155435 20716667 := bstep (se 1 (by rfl) ⟨15537500, by rfl⟩ : syracuseStep 20716667 = 31075001) B31075001
theorem B13811111 : Blo 2155435 13811111 := bstep (se 1 (by rfl) ⟨10358333, by rfl⟩ : syracuseStep 13811111 = 20716667) B20716667
theorem B9207407 : Blo 2155435 9207407 := bstep (se 1 (by rfl) ⟨6905555, by rfl⟩ : syracuseStep 9207407 = 13811111) B13811111
theorem B6138271 : Blo 2155435 6138271 := bstep (se 1 (by rfl) ⟨4603703, by rfl⟩ : syracuseStep 6138271 = 9207407) B9207407
theorem B8184361 : Blo 2155435 8184361 := bstep (se 2 (by rfl) ⟨3069135, by rfl⟩ : syracuseStep 8184361 = 6138271) B6138271
theorem B10912481 : Blo 2155435 10912481 := bstep (se 2 (by rfl) ⟨4092180, by rfl⟩ : syracuseStep 10912481 = 8184361) B8184361
theorem B7274987 : Blo 2155435 7274987 := bstep (se 1 (by rfl) ⟨5456240, by rfl⟩ : syracuseStep 7274987 = 10912481) B10912481
theorem B4849991 : Blo 2155435 4849991 := bstep (se 1 (by rfl) ⟨3637493, by rfl⟩ : syracuseStep 4849991 = 7274987) B7274987
theorem B3233327 : Blo 2155435 3233327 := bstep (se 1 (by rfl) ⟨2424995, by rfl⟩ : syracuseStep 3233327 = 4849991) B4849991
theorem B2155551 : Blo 2155435 2155551 := bstep (se 1 (by rfl) ⟨1616663, by rfl⟩ : syracuseStep 2155551 = 3233327) B3233327
theorem B3233333 : Blo 2155435 3233333 := bbase (se 5 (by rfl) ⟨151562, by rfl⟩ : syracuseStep 3233333 = 303125) (by norm_num)
theorem B2155555 : Blo 2155435 2155555 := bstep (se 1 (by rfl) ⟨1616666, by rfl⟩ : syracuseStep 2155555 = 3233333) B3233333
theorem B5456261 : Blo 2155435 5456261 := bbase (se 4 (by rfl) ⟨511524, by rfl⟩ : syracuseStep 5456261 = 1023049) (by norm_num)
theorem B3637507 : Blo 2155435 3637507 := bstep (se 1 (by rfl) ⟨2728130, by rfl⟩ : syracuseStep 3637507 = 5456261) B5456261
theorem B4850009 : Blo 2155435 4850009 := bstep (se 2 (by rfl) ⟨1818753, by rfl⟩ : syracuseStep 4850009 = 3637507) B3637507
theorem B3233339 : Blo 2155435 3233339 := bstep (se 1 (by rfl) ⟨2425004, by rfl⟩ : syracuseStep 3233339 = 4850009) B4850009
theorem B2155559 : Blo 2155435 2155559 := bstep (se 1 (by rfl) ⟨1616669, by rfl⟩ : syracuseStep 2155559 = 3233339) B3233339
theorem B2425009 : Blo 2155435 2425009 := bbase (se 2 (by rfl) ⟨909378, by rfl⟩ : syracuseStep 2425009 = 1818757) (by norm_num)
theorem B3233345 : Blo 2155435 3233345 := bstep (se 2 (by rfl) ⟨1212504, by rfl⟩ : syracuseStep 3233345 = 2425009) B2425009
theorem B2155563 : Blo 2155435 2155563 := bstep (se 1 (by rfl) ⟨1616672, by rfl⟩ : syracuseStep 2155563 = 3233345) B3233345
theorem B2301869 : Blo 2155435 2301869 := bbase (se 3 (by rfl) ⟨431600, by rfl⟩ : syracuseStep 2301869 = 863201) (by norm_num)
theorem B6138317 : Blo 2155435 6138317 := bstep (se 3 (by rfl) ⟨1150934, by rfl⟩ : syracuseStep 6138317 = 2301869) B2301869
theorem B4092211 : Blo 2155435 4092211 := bstep (se 1 (by rfl) ⟨3069158, by rfl⟩ : syracuseStep 4092211 = 6138317) B6138317
theorem B5456281 : Blo 2155435 5456281 := bstep (se 2 (by rfl) ⟨2046105, by rfl⟩ : syracuseStep 5456281 = 4092211) B4092211
theorem B7275041 : Blo 2155435 7275041 := bstep (se 2 (by rfl) ⟨2728140, by rfl⟩ : syracuseStep 7275041 = 5456281) B5456281
theorem B4850027 : Blo 2155435 4850027 := bstep (se 1 (by rfl) ⟨3637520, by rfl⟩ : syracuseStep 4850027 = 7275041) B7275041
theorem B3233351 : Blo 2155435 3233351 := bstep (se 1 (by rfl) ⟨2425013, by rfl⟩ : syracuseStep 3233351 = 4850027) B4850027
theorem B2155567 : Blo 2155435 2155567 := bstep (se 1 (by rfl) ⟨1616675, by rfl⟩ : syracuseStep 2155567 = 3233351) B3233351
theorem B3233357 : Blo 2155435 3233357 := bbase (se 3 (by rfl) ⟨606254, by rfl⟩ : syracuseStep 3233357 = 1212509) (by norm_num)
theorem B2155571 : Blo 2155435 2155571 := bstep (se 1 (by rfl) ⟨1616678, by rfl⟩ : syracuseStep 2155571 = 3233357) B3233357
theorem B4850045 : Blo 2155435 4850045 := bbase (se 3 (by rfl) ⟨909383, by rfl⟩ : syracuseStep 4850045 = 1818767) (by norm_num)
theorem B3233363 : Blo 2155435 3233363 := bstep (se 1 (by rfl) ⟨2425022, by rfl⟩ : syracuseStep 3233363 = 4850045) B4850045
theorem B2155575 : Blo 2155435 2155575 := bstep (se 1 (by rfl) ⟨1616681, by rfl⟩ : syracuseStep 2155575 = 3233363) B3233363
theorem B3637541 : Blo 2155435 3637541 := bbase (se 4 (by rfl) ⟨341019, by rfl⟩ : syracuseStep 3637541 = 682039) (by norm_num)
theorem B2425027 : Blo 2155435 2425027 := bstep (se 1 (by rfl) ⟨1818770, by rfl⟩ : syracuseStep 2425027 = 3637541) B3637541
theorem B3233369 : Blo 2155435 3233369 := bstep (se 2 (by rfl) ⟨1212513, by rfl⟩ : syracuseStep 3233369 = 2425027) B2425027
theorem B2155579 : Blo 2155435 2155579 := bstep (se 1 (by rfl) ⟨1616684, by rfl⟩ : syracuseStep 2155579 = 3233369) B3233369
theorem B3069181 : Blo 2155435 3069181 := bbase (se 3 (by rfl) ⟨575471, by rfl⟩ : syracuseStep 3069181 = 1150943) (by norm_num)
theorem B16368965 : Blo 2155435 16368965 := bstep (se 4 (by rfl) ⟨1534590, by rfl⟩ : syracuseStep 16368965 = 3069181) B3069181
theorem B10912643 : Blo 2155435 10912643 := bstep (se 1 (by rfl) ⟨8184482, by rfl⟩ : syracuseStep 10912643 = 16368965) B16368965
theorem B7275095 : Blo 2155435 7275095 := bstep (se 1 (by rfl) ⟨5456321, by rfl⟩ : syracuseStep 7275095 = 10912643) B10912643
theorem B4850063 : Blo 2155435 4850063 := bstep (se 1 (by rfl) ⟨3637547, by rfl⟩ : syracuseStep 4850063 = 7275095) B7275095
theorem B3233375 : Blo 2155435 3233375 := bstep (se 1 (by rfl) ⟨2425031, by rfl⟩ : syracuseStep 3233375 = 4850063) B4850063
theorem B2155583 : Blo 2155435 2155583 := bstep (se 1 (by rfl) ⟨1616687, by rfl⟩ : syracuseStep 2155583 = 3233375) B3233375
theorem B3233381 : Blo 2155435 3233381 := bbase (se 4 (by rfl) ⟨303129, by rfl⟩ : syracuseStep 3233381 = 606259) (by norm_num)
theorem B2155587 : Blo 2155435 2155587 := bstep (se 1 (by rfl) ⟨1616690, by rfl⟩ : syracuseStep 2155587 = 3233381) B3233381
theorem B2458129 : Blo 2155435 2458129 := bbase (se 2 (by rfl) ⟨921798, by rfl⟩ : syracuseStep 2458129 = 1843597) (by norm_num)
theorem B3277505 : Blo 2155435 3277505 := bstep (se 2 (by rfl) ⟨1229064, by rfl⟩ : syracuseStep 3277505 = 2458129) B2458129
theorem B2185003 : Blo 2155435 2185003 := bstep (se 1 (by rfl) ⟨1638752, by rfl⟩ : syracuseStep 2185003 = 3277505) B3277505
theorem B2913337 : Blo 2155435 2913337 := bstep (se 2 (by rfl) ⟨1092501, by rfl⟩ : syracuseStep 2913337 = 2185003) B2185003
theorem B3884449 : Blo 2155435 3884449 := bstep (se 2 (by rfl) ⟨1456668, by rfl⟩ : syracuseStep 3884449 = 2913337) B2913337
theorem B5179265 : Blo 2155435 5179265 := bstep (se 2 (by rfl) ⟨1942224, by rfl⟩ : syracuseStep 5179265 = 3884449) B3884449
theorem B3452843 : Blo 2155435 3452843 := bstep (se 1 (by rfl) ⟨2589632, by rfl⟩ : syracuseStep 3452843 = 5179265) B5179265
theorem B2301895 : Blo 2155435 2301895 := bstep (se 1 (by rfl) ⟨1726421, by rfl⟩ : syracuseStep 2301895 = 3452843) B3452843
theorem B3069193 : Blo 2155435 3069193 := bstep (se 2 (by rfl) ⟨1150947, by rfl⟩ : syracuseStep 3069193 = 2301895) B2301895
theorem B4092257 : Blo 2155435 4092257 := bstep (se 2 (by rfl) ⟨1534596, by rfl⟩ : syracuseStep 4092257 = 3069193) B3069193
theorem B2728171 : Blo 2155435 2728171 := bstep (se 1 (by rfl) ⟨2046128, by rfl⟩ : syracuseStep 2728171 = 4092257) B4092257
theorem B3637561 : Blo 2155435 3637561 := bstep (se 2 (by rfl) ⟨1364085, by rfl⟩ : syracuseStep 3637561 = 2728171) B2728171
theorem B4850081 : Blo 2155435 4850081 := bstep (se 2 (by rfl) ⟨1818780, by rfl⟩ : syracuseStep 4850081 = 3637561) B3637561
theorem B3233387 : Blo 2155435 3233387 := bstep (se 1 (by rfl) ⟨2425040, by rfl⟩ : syracuseStep 3233387 = 4850081) B4850081
theorem B2155591 : Blo 2155435 2155591 := bstep (se 1 (by rfl) ⟨1616693, by rfl⟩ : syracuseStep 2155591 = 3233387) B3233387
theorem B2425045 : Blo 2155435 2425045 := bbase (se 7 (by rfl) ⟨28418, by rfl⟩ : syracuseStep 2425045 = 56837) (by norm_num)
theorem B3233393 : Blo 2155435 3233393 := bstep (se 2 (by rfl) ⟨1212522, by rfl⟩ : syracuseStep 3233393 = 2425045) B2425045
theorem B2155595 : Blo 2155435 2155595 := bstep (se 1 (by rfl) ⟨1616696, by rfl⟩ : syracuseStep 2155595 = 3233393) B3233393
theorem B2728181 : Blo 2155435 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B7275149 : Blo 2155435 7275149 := bstep (se 3 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 7275149 = 2728181) B2728181
theorem B4850099 : Blo 2155435 4850099 := bstep (se 1 (by rfl) ⟨3637574, by rfl⟩ : syracuseStep 4850099 = 7275149) B7275149
theorem B3233399 : Blo 2155435 3233399 := bstep (se 1 (by rfl) ⟨2425049, by rfl⟩ : syracuseStep 3233399 = 4850099) B4850099
theorem B2155599 : Blo 2155435 2155599 := bstep (se 1 (by rfl) ⟨1616699, by rfl⟩ : syracuseStep 2155599 = 3233399) B3233399
theorem B3233405 : Blo 2155435 3233405 := bbase (se 3 (by rfl) ⟨606263, by rfl⟩ : syracuseStep 3233405 = 1212527) (by norm_num)
theorem B2155603 : Blo 2155435 2155603 := bstep (se 1 (by rfl) ⟨1616702, by rfl⟩ : syracuseStep 2155603 = 3233405) B3233405
theorem B4850117 : Blo 2155435 4850117 := bbase (se 4 (by rfl) ⟨454698, by rfl⟩ : syracuseStep 4850117 = 909397) (by norm_num)
theorem B3233411 : Blo 2155435 3233411 := bstep (se 1 (by rfl) ⟨2425058, by rfl⟩ : syracuseStep 3233411 = 4850117) B4850117
theorem B2155607 : Blo 2155435 2155607 := bstep (se 1 (by rfl) ⟨1616705, by rfl⟩ : syracuseStep 2155607 = 3233411) B3233411
theorem B6905749 : Blo 2155435 6905749 := bbase (se 6 (by rfl) ⟨161853, by rfl⟩ : syracuseStep 6905749 = 323707) (by norm_num)
theorem B9207665 : Blo 2155435 9207665 := bstep (se 2 (by rfl) ⟨3452874, by rfl⟩ : syracuseStep 9207665 = 6905749) B6905749
theorem B6138443 : Blo 2155435 6138443 := bstep (se 1 (by rfl) ⟨4603832, by rfl⟩ : syracuseStep 6138443 = 9207665) B9207665
theorem B4092295 : Blo 2155435 4092295 := bstep (se 1 (by rfl) ⟨3069221, by rfl⟩ : syracuseStep 4092295 = 6138443) B6138443
theorem B5456393 : Blo 2155435 5456393 := bstep (se 2 (by rfl) ⟨2046147, by rfl⟩ : syracuseStep 5456393 = 4092295) B4092295
theorem B3637595 : Blo 2155435 3637595 := bstep (se 1 (by rfl) ⟨2728196, by rfl⟩ : syracuseStep 3637595 = 5456393) B5456393
theorem B2425063 : Blo 2155435 2425063 := bstep (se 1 (by rfl) ⟨1818797, by rfl⟩ : syracuseStep 2425063 = 3637595) B3637595
theorem B3233417 : Blo 2155435 3233417 := bstep (se 2 (by rfl) ⟨1212531, by rfl⟩ : syracuseStep 3233417 = 2425063) B2425063
theorem B2155611 : Blo 2155435 2155611 := bstep (se 1 (by rfl) ⟨1616708, by rfl⟩ : syracuseStep 2155611 = 3233417) B3233417
theorem B10912805 : Blo 2155435 10912805 := bbase (se 4 (by rfl) ⟨1023075, by rfl⟩ : syracuseStep 10912805 = 2046151) (by norm_num)
theorem B7275203 : Blo 2155435 7275203 := bstep (se 1 (by rfl) ⟨5456402, by rfl⟩ : syracuseStep 7275203 = 10912805) B10912805
theorem B4850135 : Blo 2155435 4850135 := bstep (se 1 (by rfl) ⟨3637601, by rfl⟩ : syracuseStep 4850135 = 7275203) B7275203
theorem B3233423 : Blo 2155435 3233423 := bstep (se 1 (by rfl) ⟨2425067, by rfl⟩ : syracuseStep 3233423 = 4850135) B4850135
theorem B2155615 : Blo 2155435 2155615 := bstep (se 1 (by rfl) ⟨1616711, by rfl⟩ : syracuseStep 2155615 = 3233423) B3233423
theorem B3233429 : Blo 2155435 3233429 := bbase (se 6 (by rfl) ⟨75783, by rfl⟩ : syracuseStep 3233429 = 151567) (by norm_num)
theorem B2155619 : Blo 2155435 2155619 := bstep (se 1 (by rfl) ⟨1616714, by rfl⟩ : syracuseStep 2155619 = 3233429) B3233429
theorem B13811573 : Blo 2155435 13811573 := bbase (se 5 (by rfl) ⟨647417, by rfl⟩ : syracuseStep 13811573 = 1294835) (by norm_num)
theorem B9207715 : Blo 2155435 9207715 := bstep (se 1 (by rfl) ⟨6905786, by rfl⟩ : syracuseStep 9207715 = 13811573) B13811573
theorem B12276953 : Blo 2155435 12276953 := bstep (se 2 (by rfl) ⟨4603857, by rfl⟩ : syracuseStep 12276953 = 9207715) B9207715
theorem B8184635 : Blo 2155435 8184635 := bstep (se 1 (by rfl) ⟨6138476, by rfl⟩ : syracuseStep 8184635 = 12276953) B12276953
theorem B5456423 : Blo 2155435 5456423 := bstep (se 1 (by rfl) ⟨4092317, by rfl⟩ : syracuseStep 5456423 = 8184635) B8184635
theorem B3637615 : Blo 2155435 3637615 := bstep (se 1 (by rfl) ⟨2728211, by rfl⟩ : syracuseStep 3637615 = 5456423) B5456423
theorem B4850153 : Blo 2155435 4850153 := bstep (se 2 (by rfl) ⟨1818807, by rfl⟩ : syracuseStep 4850153 = 3637615) B3637615
theorem B3233435 : Blo 2155435 3233435 := bstep (se 1 (by rfl) ⟨2425076, by rfl⟩ : syracuseStep 3233435 = 4850153) B4850153
theorem B2155623 : Blo 2155435 2155623 := bstep (se 1 (by rfl) ⟨1616717, by rfl⟩ : syracuseStep 2155623 = 3233435) B3233435
theorem B2425081 : Blo 2155435 2425081 := bbase (se 2 (by rfl) ⟨909405, by rfl⟩ : syracuseStep 2425081 = 1818811) (by norm_num)
theorem B3233441 : Blo 2155435 3233441 := bstep (se 2 (by rfl) ⟨1212540, by rfl⟩ : syracuseStep 3233441 = 2425081) B2425081
theorem B2155627 : Blo 2155435 2155627 := bstep (se 1 (by rfl) ⟨1616720, by rfl⟩ : syracuseStep 2155627 = 3233441) B3233441
theorem B9207749 : Blo 2155435 9207749 := bbase (se 4 (by rfl) ⟨863226, by rfl⟩ : syracuseStep 9207749 = 1726453) (by norm_num)
theorem B6138499 : Blo 2155435 6138499 := bstep (se 1 (by rfl) ⟨4603874, by rfl⟩ : syracuseStep 6138499 = 9207749) B9207749
theorem B8184665 : Blo 2155435 8184665 := bstep (se 2 (by rfl) ⟨3069249, by rfl⟩ : syracuseStep 8184665 = 6138499) B6138499
theorem B5456443 : Blo 2155435 5456443 := bstep (se 1 (by rfl) ⟨4092332, by rfl⟩ : syracuseStep 5456443 = 8184665) B8184665
theorem B7275257 : Blo 2155435 7275257 := bstep (se 2 (by rfl) ⟨2728221, by rfl⟩ : syracuseStep 7275257 = 5456443) B5456443
theorem B4850171 : Blo 2155435 4850171 := bstep (se 1 (by rfl) ⟨3637628, by rfl⟩ : syracuseStep 4850171 = 7275257) B7275257
theorem B3233447 : Blo 2155435 3233447 := bstep (se 1 (by rfl) ⟨2425085, by rfl⟩ : syracuseStep 3233447 = 4850171) B4850171
theorem B2155631 : Blo 2155435 2155631 := bstep (se 1 (by rfl) ⟨1616723, by rfl⟩ : syracuseStep 2155631 = 3233447) B3233447
theorem B3233453 : Blo 2155435 3233453 := bbase (se 3 (by rfl) ⟨606272, by rfl⟩ : syracuseStep 3233453 = 1212545) (by norm_num)
theorem B2155635 : Blo 2155435 2155635 := bstep (se 1 (by rfl) ⟨1616726, by rfl⟩ : syracuseStep 2155635 = 3233453) B3233453
theorem B4850189 : Blo 2155435 4850189 := bbase (se 3 (by rfl) ⟨909410, by rfl⟩ : syracuseStep 4850189 = 1818821) (by norm_num)
theorem B3233459 : Blo 2155435 3233459 := bstep (se 1 (by rfl) ⟨2425094, by rfl⟩ : syracuseStep 3233459 = 4850189) B4850189
theorem B2155639 : Blo 2155435 2155639 := bstep (se 1 (by rfl) ⟨1616729, by rfl⟩ : syracuseStep 2155639 = 3233459) B3233459
theorem B2728237 : Blo 2155435 2728237 := bbase (se 3 (by rfl) ⟨511544, by rfl⟩ : syracuseStep 2728237 = 1023089) (by norm_num)
theorem B3637649 : Blo 2155435 3637649 := bstep (se 2 (by rfl) ⟨1364118, by rfl⟩ : syracuseStep 3637649 = 2728237) B2728237
theorem B2425099 : Blo 2155435 2425099 := bstep (se 1 (by rfl) ⟨1818824, by rfl⟩ : syracuseStep 2425099 = 3637649) B3637649
theorem B3233465 : Blo 2155435 3233465 := bstep (se 2 (by rfl) ⟨1212549, by rfl⟩ : syracuseStep 3233465 = 2425099) B2425099
theorem B2155643 : Blo 2155435 2155643 := bstep (se 1 (by rfl) ⟨1616732, by rfl⟩ : syracuseStep 2155643 = 3233465) B3233465
theorem B5179397 : Blo 2155435 5179397 := bbase (se 4 (by rfl) ⟨485568, by rfl⟩ : syracuseStep 5179397 = 971137) (by norm_num)
theorem B13811725 : Blo 2155435 13811725 := bstep (se 3 (by rfl) ⟨2589698, by rfl⟩ : syracuseStep 13811725 = 5179397) B5179397
theorem B18415633 : Blo 2155435 18415633 := bstep (se 2 (by rfl) ⟨6905862, by rfl⟩ : syracuseStep 18415633 = 13811725) B13811725
theorem B24554177 : Blo 2155435 24554177 := bstep (se 2 (by rfl) ⟨9207816, by rfl⟩ : syracuseStep 24554177 = 18415633) B18415633
theorem B16369451 : Blo 2155435 16369451 := bstep (se 1 (by rfl) ⟨12277088, by rfl⟩ : syracuseStep 16369451 = 24554177) B24554177
theorem B10912967 : Blo 2155435 10912967 := bstep (se 1 (by rfl) ⟨8184725, by rfl⟩ : syracuseStep 10912967 = 16369451) B16369451
theorem B7275311 : Blo 2155435 7275311 := bstep (se 1 (by rfl) ⟨5456483, by rfl⟩ : syracuseStep 7275311 = 10912967) B10912967
theorem B4850207 : Blo 2155435 4850207 := bstep (se 1 (by rfl) ⟨3637655, by rfl⟩ : syracuseStep 4850207 = 7275311) B7275311
theorem B3233471 : Blo 2155435 3233471 := bstep (se 1 (by rfl) ⟨2425103, by rfl⟩ : syracuseStep 3233471 = 4850207) B4850207
theorem B2155647 : Blo 2155435 2155647 := bstep (se 1 (by rfl) ⟨1616735, by rfl⟩ : syracuseStep 2155647 = 3233471) B3233471
theorem B3233477 : Blo 2155435 3233477 := bbase (se 4 (by rfl) ⟨303138, by rfl⟩ : syracuseStep 3233477 = 606277) (by norm_num)
theorem B2155651 : Blo 2155435 2155651 := bstep (se 1 (by rfl) ⟨1616738, by rfl⟩ : syracuseStep 2155651 = 3233477) B3233477
theorem B3637669 : Blo 2155435 3637669 := bbase (se 4 (by rfl) ⟨341031, by rfl⟩ : syracuseStep 3637669 = 682063) (by norm_num)
theorem B4850225 : Blo 2155435 4850225 := bstep (se 2 (by rfl) ⟨1818834, by rfl⟩ : syracuseStep 4850225 = 3637669) B3637669
theorem B3233483 : Blo 2155435 3233483 := bstep (se 1 (by rfl) ⟨2425112, by rfl⟩ : syracuseStep 3233483 = 4850225) B4850225
theorem B2155655 : Blo 2155435 2155655 := bstep (se 1 (by rfl) ⟨1616741, by rfl⟩ : syracuseStep 2155655 = 3233483) B3233483
theorem B2425117 : Blo 2155435 2425117 := bbase (se 3 (by rfl) ⟨454709, by rfl⟩ : syracuseStep 2425117 = 909419) (by norm_num)
theorem B3233489 : Blo 2155435 3233489 := bstep (se 2 (by rfl) ⟨1212558, by rfl⟩ : syracuseStep 3233489 = 2425117) B2425117
theorem B2155659 : Blo 2155435 2155659 := bstep (se 1 (by rfl) ⟨1616744, by rfl⟩ : syracuseStep 2155659 = 3233489) B3233489
theorem B7275365 : Blo 2155435 7275365 := bbase (se 4 (by rfl) ⟨682065, by rfl⟩ : syracuseStep 7275365 = 1364131) (by norm_num)
theorem B4850243 : Blo 2155435 4850243 := bstep (se 1 (by rfl) ⟨3637682, by rfl⟩ : syracuseStep 4850243 = 7275365) B7275365
theorem B3233495 : Blo 2155435 3233495 := bstep (se 1 (by rfl) ⟨2425121, by rfl⟩ : syracuseStep 3233495 = 4850243) B4850243
theorem B2155663 : Blo 2155435 2155663 := bstep (se 1 (by rfl) ⟨1616747, by rfl⟩ : syracuseStep 2155663 = 3233495) B3233495
theorem B3233501 : Blo 2155435 3233501 := bbase (se 3 (by rfl) ⟨606281, by rfl⟩ : syracuseStep 3233501 = 1212563) (by norm_num)
theorem B2155667 : Blo 2155435 2155667 := bstep (se 1 (by rfl) ⟨1616750, by rfl⟩ : syracuseStep 2155667 = 3233501) B3233501
theorem B4850261 : Blo 2155435 4850261 := bbase (se 8 (by rfl) ⟨28419, by rfl⟩ : syracuseStep 4850261 = 56839) (by norm_num)
theorem B3233507 : Blo 2155435 3233507 := bstep (se 1 (by rfl) ⟨2425130, by rfl⟩ : syracuseStep 3233507 = 4850261) B4850261
theorem B2155671 : Blo 2155435 2155671 := bstep (se 1 (by rfl) ⟨1616753, by rfl⟩ : syracuseStep 2155671 = 3233507) B3233507
theorem B2589733 : Blo 2155435 2589733 := bbase (se 4 (by rfl) ⟨242787, by rfl⟩ : syracuseStep 2589733 = 485575) (by norm_num)
theorem B3452977 : Blo 2155435 3452977 := bstep (se 2 (by rfl) ⟨1294866, by rfl⟩ : syracuseStep 3452977 = 2589733) B2589733
theorem B4603969 : Blo 2155435 4603969 := bstep (se 2 (by rfl) ⟨1726488, by rfl⟩ : syracuseStep 4603969 = 3452977) B3452977
theorem B6138625 : Blo 2155435 6138625 := bstep (se 2 (by rfl) ⟨2301984, by rfl⟩ : syracuseStep 6138625 = 4603969) B4603969
theorem B8184833 : Blo 2155435 8184833 := bstep (se 2 (by rfl) ⟨3069312, by rfl⟩ : syracuseStep 8184833 = 6138625) B6138625
theorem B5456555 : Blo 2155435 5456555 := bstep (se 1 (by rfl) ⟨4092416, by rfl⟩ : syracuseStep 5456555 = 8184833) B8184833
theorem B3637703 : Blo 2155435 3637703 := bstep (se 1 (by rfl) ⟨2728277, by rfl⟩ : syracuseStep 3637703 = 5456555) B5456555
theorem B2425135 : Blo 2155435 2425135 := bstep (se 1 (by rfl) ⟨1818851, by rfl⟩ : syracuseStep 2425135 = 3637703) B3637703
theorem B3233513 : Blo 2155435 3233513 := bstep (se 2 (by rfl) ⟨1212567, by rfl⟩ : syracuseStep 3233513 = 2425135) B2425135
theorem B2155675 : Blo 2155435 2155675 := bstep (se 1 (by rfl) ⟨1616756, by rfl⟩ : syracuseStep 2155675 = 3233513) B3233513
theorem B2589737 : Blo 2155435 2589737 := bbase (se 2 (by rfl) ⟨971151, by rfl⟩ : syracuseStep 2589737 = 1942303) (by norm_num)
theorem B27623861 : Blo 2155435 27623861 := bstep (se 5 (by rfl) ⟨1294868, by rfl⟩ : syracuseStep 27623861 = 2589737) B2589737
theorem B18415907 : Blo 2155435 18415907 := bstep (se 1 (by rfl) ⟨13811930, by rfl⟩ : syracuseStep 18415907 = 27623861) B27623861
theorem B12277271 : Blo 2155435 12277271 := bstep (se 1 (by rfl) ⟨9207953, by rfl⟩ : syracuseStep 12277271 = 18415907) B18415907
theorem B8184847 : Blo 2155435 8184847 := bstep (se 1 (by rfl) ⟨6138635, by rfl⟩ : syracuseStep 8184847 = 12277271) B12277271
theorem B10913129 : Blo 2155435 10913129 := bstep (se 2 (by rfl) ⟨4092423, by rfl⟩ : syracuseStep 10913129 = 8184847) B8184847
theorem B7275419 : Blo 2155435 7275419 := bstep (se 1 (by rfl) ⟨5456564, by rfl⟩ : syracuseStep 7275419 = 10913129) B10913129
theorem B4850279 : Blo 2155435 4850279 := bstep (se 1 (by rfl) ⟨3637709, by rfl⟩ : syracuseStep 4850279 = 7275419) B7275419
theorem B3233519 : Blo 2155435 3233519 := bstep (se 1 (by rfl) ⟨2425139, by rfl⟩ : syracuseStep 3233519 = 4850279) B4850279
theorem B2155679 : Blo 2155435 2155679 := bstep (se 1 (by rfl) ⟨1616759, by rfl⟩ : syracuseStep 2155679 = 3233519) B3233519
theorem B3233525 : Blo 2155435 3233525 := bbase (se 5 (by rfl) ⟨151571, by rfl⟩ : syracuseStep 3233525 = 303143) (by norm_num)
theorem B2155683 : Blo 2155435 2155683 := bstep (se 1 (by rfl) ⟨1616762, by rfl⟩ : syracuseStep 2155683 = 3233525) B3233525
theorem B9207989 : Blo 2155435 9207989 := bbase (se 5 (by rfl) ⟨431624, by rfl⟩ : syracuseStep 9207989 = 863249) (by norm_num)
theorem B6138659 : Blo 2155435 6138659 := bstep (se 1 (by rfl) ⟨4603994, by rfl⟩ : syracuseStep 6138659 = 9207989) B9207989
theorem B4092439 : Blo 2155435 4092439 := bstep (se 1 (by rfl) ⟨3069329, by rfl⟩ : syracuseStep 4092439 = 6138659) B6138659
theorem B5456585 : Blo 2155435 5456585 := bstep (se 2 (by rfl) ⟨2046219, by rfl⟩ : syracuseStep 5456585 = 4092439) B4092439
theorem B3637723 : Blo 2155435 3637723 := bstep (se 1 (by rfl) ⟨2728292, by rfl⟩ : syracuseStep 3637723 = 5456585) B5456585
theorem B4850297 : Blo 2155435 4850297 := bstep (se 2 (by rfl) ⟨1818861, by rfl⟩ : syracuseStep 4850297 = 3637723) B3637723
theorem B3233531 : Blo 2155435 3233531 := bstep (se 1 (by rfl) ⟨2425148, by rfl⟩ : syracuseStep 3233531 = 4850297) B4850297
theorem B2155687 : Blo 2155435 2155687 := bstep (se 1 (by rfl) ⟨1616765, by rfl⟩ : syracuseStep 2155687 = 3233531) B3233531
theorem B2425153 : Blo 2155435 2425153 := bbase (se 2 (by rfl) ⟨909432, by rfl⟩ : syracuseStep 2425153 = 1818865) (by norm_num)
theorem B3233537 : Blo 2155435 3233537 := bstep (se 2 (by rfl) ⟨1212576, by rfl⟩ : syracuseStep 3233537 = 2425153) B2425153
theorem B2155691 : Blo 2155435 2155691 := bstep (se 1 (by rfl) ⟨1616768, by rfl⟩ : syracuseStep 2155691 = 3233537) B3233537
theorem B5456605 : Blo 2155435 5456605 := bbase (se 3 (by rfl) ⟨1023113, by rfl⟩ : syracuseStep 5456605 = 2046227) (by norm_num)
theorem B7275473 : Blo 2155435 7275473 := bstep (se 2 (by rfl) ⟨2728302, by rfl⟩ : syracuseStep 7275473 = 5456605) B5456605
theorem B4850315 : Blo 2155435 4850315 := bstep (se 1 (by rfl) ⟨3637736, by rfl⟩ : syracuseStep 4850315 = 7275473) B7275473
theorem B3233543 : Blo 2155435 3233543 := bstep (se 1 (by rfl) ⟨2425157, by rfl⟩ : syracuseStep 3233543 = 4850315) B4850315
theorem B2155695 : Blo 2155435 2155695 := bstep (se 1 (by rfl) ⟨1616771, by rfl⟩ : syracuseStep 2155695 = 3233543) B3233543
theorem B3233549 : Blo 2155435 3233549 := bbase (se 3 (by rfl) ⟨606290, by rfl⟩ : syracuseStep 3233549 = 1212581) (by norm_num)
theorem B2155699 : Blo 2155435 2155699 := bstep (se 1 (by rfl) ⟨1616774, by rfl⟩ : syracuseStep 2155699 = 3233549) B3233549
theorem B4850333 : Blo 2155435 4850333 := bbase (se 3 (by rfl) ⟨909437, by rfl⟩ : syracuseStep 4850333 = 1818875) (by norm_num)
theorem B3233555 : Blo 2155435 3233555 := bstep (se 1 (by rfl) ⟨2425166, by rfl⟩ : syracuseStep 3233555 = 4850333) B4850333
theorem B2155703 : Blo 2155435 2155703 := bstep (se 1 (by rfl) ⟨1616777, by rfl⟩ : syracuseStep 2155703 = 3233555) B3233555
theorem B3637757 : Blo 2155435 3637757 := bbase (se 3 (by rfl) ⟨682079, by rfl⟩ : syracuseStep 3637757 = 1364159) (by norm_num)
theorem B2425171 : Blo 2155435 2425171 := bstep (se 1 (by rfl) ⟨1818878, by rfl⟩ : syracuseStep 2425171 = 3637757) B3637757
theorem B3233561 : Blo 2155435 3233561 := bstep (se 2 (by rfl) ⟨1212585, by rfl⟩ : syracuseStep 3233561 = 2425171) B2425171
theorem B2155707 : Blo 2155435 2155707 := bstep (se 1 (by rfl) ⟨1616780, by rfl⟩ : syracuseStep 2155707 = 3233561) B3233561
theorem B4604045 : Blo 2155435 4604045 := bbase (se 3 (by rfl) ⟨863258, by rfl⟩ : syracuseStep 4604045 = 1726517) (by norm_num)
theorem B12277453 : Blo 2155435 12277453 := bstep (se 3 (by rfl) ⟨2302022, by rfl⟩ : syracuseStep 12277453 = 4604045) B4604045
theorem B16369937 : Blo 2155435 16369937 := bstep (se 2 (by rfl) ⟨6138726, by rfl⟩ : syracuseStep 16369937 = 12277453) B12277453
theorem B10913291 : Blo 2155435 10913291 := bstep (se 1 (by rfl) ⟨8184968, by rfl⟩ : syracuseStep 10913291 = 16369937) B16369937
theorem B7275527 : Blo 2155435 7275527 := bstep (se 1 (by rfl) ⟨5456645, by rfl⟩ : syracuseStep 7275527 = 10913291) B10913291
theorem B4850351 : Blo 2155435 4850351 := bstep (se 1 (by rfl) ⟨3637763, by rfl⟩ : syracuseStep 4850351 = 7275527) B7275527
theorem B3233567 : Blo 2155435 3233567 := bstep (se 1 (by rfl) ⟨2425175, by rfl⟩ : syracuseStep 3233567 = 4850351) B4850351
theorem B2155711 : Blo 2155435 2155711 := bstep (se 1 (by rfl) ⟨1616783, by rfl⟩ : syracuseStep 2155711 = 3233567) B3233567
theorem B3233573 : Blo 2155435 3233573 := bbase (se 4 (by rfl) ⟨303147, by rfl⟩ : syracuseStep 3233573 = 606295) (by norm_num)
theorem B2155715 : Blo 2155435 2155715 := bstep (se 1 (by rfl) ⟨1616786, by rfl⟩ : syracuseStep 2155715 = 3233573) B3233573
theorem B2728333 : Blo 2155435 2728333 := bbase (se 3 (by rfl) ⟨511562, by rfl⟩ : syracuseStep 2728333 = 1023125) (by norm_num)
theorem B3637777 : Blo 2155435 3637777 := bstep (se 2 (by rfl) ⟨1364166, by rfl⟩ : syracuseStep 3637777 = 2728333) B2728333
theorem B4850369 : Blo 2155435 4850369 := bstep (se 2 (by rfl) ⟨1818888, by rfl⟩ : syracuseStep 4850369 = 3637777) B3637777
theorem B3233579 : Blo 2155435 3233579 := bstep (se 1 (by rfl) ⟨2425184, by rfl⟩ : syracuseStep 3233579 = 4850369) B4850369
theorem B2155719 : Blo 2155435 2155719 := bstep (se 1 (by rfl) ⟨1616789, by rfl⟩ : syracuseStep 2155719 = 3233579) B3233579
theorem B2425189 : Blo 2155435 2425189 := bbase (se 4 (by rfl) ⟨227361, by rfl⟩ : syracuseStep 2425189 = 454723) (by norm_num)
theorem B3233585 : Blo 2155435 3233585 := bstep (se 2 (by rfl) ⟨1212594, by rfl⟩ : syracuseStep 3233585 = 2425189) B2425189
theorem B2155723 : Blo 2155435 2155723 := bstep (se 1 (by rfl) ⟨1616792, by rfl⟩ : syracuseStep 2155723 = 3233585) B3233585
theorem B6138773 : Blo 2155435 6138773 := bbase (se 6 (by rfl) ⟨143877, by rfl⟩ : syracuseStep 6138773 = 287755) (by norm_num)
theorem B4092515 : Blo 2155435 4092515 := bstep (se 1 (by rfl) ⟨3069386, by rfl⟩ : syracuseStep 4092515 = 6138773) B6138773
theorem B2728343 : Blo 2155435 2728343 := bstep (se 1 (by rfl) ⟨2046257, by rfl⟩ : syracuseStep 2728343 = 4092515) B4092515
theorem B7275581 : Blo 2155435 7275581 := bstep (se 3 (by rfl) ⟨1364171, by rfl⟩ : syracuseStep 7275581 = 2728343) B2728343
theorem B4850387 : Blo 2155435 4850387 := bstep (se 1 (by rfl) ⟨3637790, by rfl⟩ : syracuseStep 4850387 = 7275581) B7275581
theorem B3233591 : Blo 2155435 3233591 := bstep (se 1 (by rfl) ⟨2425193, by rfl⟩ : syracuseStep 3233591 = 4850387) B4850387
theorem B2155727 : Blo 2155435 2155727 := bstep (se 1 (by rfl) ⟨1616795, by rfl⟩ : syracuseStep 2155727 = 3233591) B3233591
theorem B3233597 : Blo 2155435 3233597 := bbase (se 3 (by rfl) ⟨606299, by rfl⟩ : syracuseStep 3233597 = 1212599) (by norm_num)
theorem B2155731 : Blo 2155435 2155731 := bstep (se 1 (by rfl) ⟨1616798, by rfl⟩ : syracuseStep 2155731 = 3233597) B3233597
theorem B4850405 : Blo 2155435 4850405 := bbase (se 4 (by rfl) ⟨454725, by rfl⟩ : syracuseStep 4850405 = 909451) (by norm_num)
theorem B3233603 : Blo 2155435 3233603 := bstep (se 1 (by rfl) ⟨2425202, by rfl⟩ : syracuseStep 3233603 = 4850405) B4850405
theorem B2155735 : Blo 2155435 2155735 := bstep (se 1 (by rfl) ⟨1616801, by rfl⟩ : syracuseStep 2155735 = 3233603) B3233603
theorem B5456717 : Blo 2155435 5456717 := bbase (se 3 (by rfl) ⟨1023134, by rfl⟩ : syracuseStep 5456717 = 2046269) (by norm_num)
theorem B3637811 : Blo 2155435 3637811 := bstep (se 1 (by rfl) ⟨2728358, by rfl⟩ : syracuseStep 3637811 = 5456717) B5456717
theorem B2425207 : Blo 2155435 2425207 := bstep (se 1 (by rfl) ⟨1818905, by rfl⟩ : syracuseStep 2425207 = 3637811) B3637811
theorem B3233609 : Blo 2155435 3233609 := bstep (se 2 (by rfl) ⟨1212603, by rfl⟩ : syracuseStep 3233609 = 2425207) B2425207
theorem B2155739 : Blo 2155435 2155739 := bstep (se 1 (by rfl) ⟨1616804, by rfl⟩ : syracuseStep 2155739 = 3233609) B3233609
theorem B2302057 : Blo 2155435 2302057 := bbase (se 2 (by rfl) ⟨863271, by rfl⟩ : syracuseStep 2302057 = 1726543) (by norm_num)
theorem B3069409 : Blo 2155435 3069409 := bstep (se 2 (by rfl) ⟨1151028, by rfl⟩ : syracuseStep 3069409 = 2302057) B2302057
theorem B4092545 : Blo 2155435 4092545 := bstep (se 2 (by rfl) ⟨1534704, by rfl⟩ : syracuseStep 4092545 = 3069409) B3069409
theorem B10913453 : Blo 2155435 10913453 := bstep (se 3 (by rfl) ⟨2046272, by rfl⟩ : syracuseStep 10913453 = 4092545) B4092545
theorem B7275635 : Blo 2155435 7275635 := bstep (se 1 (by rfl) ⟨5456726, by rfl⟩ : syracuseStep 7275635 = 10913453) B10913453
theorem B4850423 : Blo 2155435 4850423 := bstep (se 1 (by rfl) ⟨3637817, by rfl⟩ : syracuseStep 4850423 = 7275635) B7275635
theorem B3233615 : Blo 2155435 3233615 := bstep (se 1 (by rfl) ⟨2425211, by rfl⟩ : syracuseStep 3233615 = 4850423) B4850423
theorem B2155743 : Blo 2155435 2155743 := bstep (se 1 (by rfl) ⟨1616807, by rfl⟩ : syracuseStep 2155743 = 3233615) B3233615
theorem B3233621 : Blo 2155435 3233621 := bbase (se 9 (by rfl) ⟨9473, by rfl⟩ : syracuseStep 3233621 = 18947) (by norm_num)
theorem B2155747 : Blo 2155435 2155747 := bstep (se 1 (by rfl) ⟨1616810, by rfl⟩ : syracuseStep 2155747 = 3233621) B3233621
theorem B6906197 : Blo 2155435 6906197 := bbase (se 10 (by rfl) ⟨10116, by rfl⟩ : syracuseStep 6906197 = 20233) (by norm_num)
theorem B4604131 : Blo 2155435 4604131 := bstep (se 1 (by rfl) ⟨3453098, by rfl⟩ : syracuseStep 4604131 = 6906197) B6906197
theorem B6138841 : Blo 2155435 6138841 := bstep (se 2 (by rfl) ⟨2302065, by rfl⟩ : syracuseStep 6138841 = 4604131) B4604131
theorem B8185121 : Blo 2155435 8185121 := bstep (se 2 (by rfl) ⟨3069420, by rfl⟩ : syracuseStep 8185121 = 6138841) B6138841
theorem B5456747 : Blo 2155435 5456747 := bstep (se 1 (by rfl) ⟨4092560, by rfl⟩ : syracuseStep 5456747 = 8185121) B8185121
theorem B3637831 : Blo 2155435 3637831 := bstep (se 1 (by rfl) ⟨2728373, by rfl⟩ : syracuseStep 3637831 = 5456747) B5456747
theorem B4850441 : Blo 2155435 4850441 := bstep (se 2 (by rfl) ⟨1818915, by rfl⟩ : syracuseStep 4850441 = 3637831) B3637831
theorem B3233627 : Blo 2155435 3233627 := bstep (se 1 (by rfl) ⟨2425220, by rfl⟩ : syracuseStep 3233627 = 4850441) B4850441
theorem B2155751 : Blo 2155435 2155751 := bstep (se 1 (by rfl) ⟨1616813, by rfl⟩ : syracuseStep 2155751 = 3233627) B3233627
theorem B2425225 : Blo 2155435 2425225 := bbase (se 2 (by rfl) ⟨909459, by rfl⟩ : syracuseStep 2425225 = 1818919) (by norm_num)
theorem B3233633 : Blo 2155435 3233633 := bstep (se 2 (by rfl) ⟨1212612, by rfl⟩ : syracuseStep 3233633 = 2425225) B2425225
theorem B2155755 : Blo 2155435 2155755 := bstep (se 1 (by rfl) ⟨1616816, by rfl⟩ : syracuseStep 2155755 = 3233633) B3233633
theorem B79739477 : Blo 2155435 79739477 := bbase (se 8 (by rfl) ⟨467223, by rfl⟩ : syracuseStep 79739477 = 934447) (by norm_num)
theorem B53159651 : Blo 2155435 53159651 := bstep (se 1 (by rfl) ⟨39869738, by rfl⟩ : syracuseStep 53159651 = 79739477) B79739477
theorem B35439767 : Blo 2155435 35439767 := bstep (se 1 (by rfl) ⟨26579825, by rfl⟩ : syracuseStep 35439767 = 53159651) B53159651
theorem B23626511 : Blo 2155435 23626511 := bstep (se 1 (by rfl) ⟨17719883, by rfl⟩ : syracuseStep 23626511 = 35439767) B35439767
theorem B15751007 : Blo 2155435 15751007 := bstep (se 1 (by rfl) ⟨11813255, by rfl⟩ : syracuseStep 15751007 = 23626511) B23626511
theorem B10500671 : Blo 2155435 10500671 := bstep (se 1 (by rfl) ⟨7875503, by rfl⟩ : syracuseStep 10500671 = 15751007) B15751007
theorem B7000447 : Blo 2155435 7000447 := bstep (se 1 (by rfl) ⟨5250335, by rfl⟩ : syracuseStep 7000447 = 10500671) B10500671
theorem B9333929 : Blo 2155435 9333929 := bstep (se 2 (by rfl) ⟨3500223, by rfl⟩ : syracuseStep 9333929 = 7000447) B7000447
theorem B6222619 : Blo 2155435 6222619 := bstep (se 1 (by rfl) ⟨4666964, by rfl⟩ : syracuseStep 6222619 = 9333929) B9333929
theorem B8296825 : Blo 2155435 8296825 := bstep (se 2 (by rfl) ⟨3111309, by rfl⟩ : syracuseStep 8296825 = 6222619) B6222619
theorem B11062433 : Blo 2155435 11062433 := bstep (se 2 (by rfl) ⟨4148412, by rfl⟩ : syracuseStep 11062433 = 8296825) B8296825
theorem B29499821 : Blo 2155435 29499821 := bstep (se 3 (by rfl) ⟨5531216, by rfl⟩ : syracuseStep 29499821 = 11062433) B11062433
theorem B19666547 : Blo 2155435 19666547 := bstep (se 1 (by rfl) ⟨14749910, by rfl⟩ : syracuseStep 19666547 = 29499821) B29499821
theorem B13111031 : Blo 2155435 13111031 := bstep (se 1 (by rfl) ⟨9833273, by rfl⟩ : syracuseStep 13111031 = 19666547) B19666547
theorem B34962749 : Blo 2155435 34962749 := bstep (se 3 (by rfl) ⟨6555515, by rfl⟩ : syracuseStep 34962749 = 13111031) B13111031
theorem B23308499 : Blo 2155435 23308499 := bstep (se 1 (by rfl) ⟨17481374, by rfl⟩ : syracuseStep 23308499 = 34962749) B34962749
theorem B62155997 : Blo 2155435 62155997 := bstep (se 3 (by rfl) ⟨11654249, by rfl⟩ : syracuseStep 62155997 = 23308499) B23308499
theorem B41437331 : Blo 2155435 41437331 := bstep (se 1 (by rfl) ⟨31077998, by rfl⟩ : syracuseStep 41437331 = 62155997) B62155997
theorem B27624887 : Blo 2155435 27624887 := bstep (se 1 (by rfl) ⟨20718665, by rfl⟩ : syracuseStep 27624887 = 41437331) B41437331
theorem B18416591 : Blo 2155435 18416591 := bstep (se 1 (by rfl) ⟨13812443, by rfl⟩ : syracuseStep 18416591 = 27624887) B27624887
theorem B12277727 : Blo 2155435 12277727 := bstep (se 1 (by rfl) ⟨9208295, by rfl⟩ : syracuseStep 12277727 = 18416591) B18416591
theorem B8185151 : Blo 2155435 8185151 := bstep (se 1 (by rfl) ⟨6138863, by rfl⟩ : syracuseStep 8185151 = 12277727) B12277727
theorem B5456767 : Blo 2155435 5456767 := bstep (se 1 (by rfl) ⟨4092575, by rfl⟩ : syracuseStep 5456767 = 8185151) B8185151
theorem B7275689 : Blo 2155435 7275689 := bstep (se 2 (by rfl) ⟨2728383, by rfl⟩ : syracuseStep 7275689 = 5456767) B5456767
theorem B4850459 : Blo 2155435 4850459 := bstep (se 1 (by rfl) ⟨3637844, by rfl⟩ : syracuseStep 4850459 = 7275689) B7275689
theorem B3233639 : Blo 2155435 3233639 := bstep (se 1 (by rfl) ⟨2425229, by rfl⟩ : syracuseStep 3233639 = 4850459) B4850459
theorem B2155759 : Blo 2155435 2155759 := bstep (se 1 (by rfl) ⟨1616819, by rfl⟩ : syracuseStep 2155759 = 3233639) B3233639
theorem B3233645 : Blo 2155435 3233645 := bbase (se 3 (by rfl) ⟨606308, by rfl⟩ : syracuseStep 3233645 = 1212617) (by norm_num)
theorem B2155763 : Blo 2155435 2155763 := bstep (se 1 (by rfl) ⟨1616822, by rfl⟩ : syracuseStep 2155763 = 3233645) B3233645
theorem B4850477 : Blo 2155435 4850477 := bbase (se 3 (by rfl) ⟨909464, by rfl⟩ : syracuseStep 4850477 = 1818929) (by norm_num)
theorem B3233651 : Blo 2155435 3233651 := bstep (se 1 (by rfl) ⟨2425238, by rfl⟩ : syracuseStep 3233651 = 4850477) B4850477
theorem B2155767 : Blo 2155435 2155767 := bstep (se 1 (by rfl) ⟨1616825, by rfl⟩ : syracuseStep 2155767 = 3233651) B3233651
theorem B3884773 : Blo 2155435 3884773 := bbase (se 4 (by rfl) ⟨364197, by rfl⟩ : syracuseStep 3884773 = 728395) (by norm_num)
theorem B5179697 : Blo 2155435 5179697 := bstep (se 2 (by rfl) ⟨1942386, by rfl⟩ : syracuseStep 5179697 = 3884773) B3884773
theorem B3453131 : Blo 2155435 3453131 := bstep (se 1 (by rfl) ⟨2589848, by rfl⟩ : syracuseStep 3453131 = 5179697) B5179697
theorem B9208349 : Blo 2155435 9208349 := bstep (se 3 (by rfl) ⟨1726565, by rfl⟩ : syracuseStep 9208349 = 3453131) B3453131
theorem B6138899 : Blo 2155435 6138899 := bstep (se 1 (by rfl) ⟨4604174, by rfl⟩ : syracuseStep 6138899 = 9208349) B9208349
theorem B4092599 : Blo 2155435 4092599 := bstep (se 1 (by rfl) ⟨3069449, by rfl⟩ : syracuseStep 4092599 = 6138899) B6138899
theorem B2728399 : Blo 2155435 2728399 := bstep (se 1 (by rfl) ⟨2046299, by rfl⟩ : syracuseStep 2728399 = 4092599) B4092599
theorem B3637865 : Blo 2155435 3637865 := bstep (se 2 (by rfl) ⟨1364199, by rfl⟩ : syracuseStep 3637865 = 2728399) B2728399
theorem B2425243 : Blo 2155435 2425243 := bstep (se 1 (by rfl) ⟨1818932, by rfl⟩ : syracuseStep 2425243 = 3637865) B3637865
theorem B3233657 : Blo 2155435 3233657 := bstep (se 2 (by rfl) ⟨1212621, by rfl⟩ : syracuseStep 3233657 = 2425243) B2425243
theorem B2155771 : Blo 2155435 2155771 := bstep (se 1 (by rfl) ⟨1616828, by rfl⟩ : syracuseStep 2155771 = 3233657) B3233657
theorem B7769557 : Blo 2155435 7769557 := bbase (se 7 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 7769557 = 182099) (by norm_num)
theorem B10359409 : Blo 2155435 10359409 := bstep (se 2 (by rfl) ⟨3884778, by rfl⟩ : syracuseStep 10359409 = 7769557) B7769557
theorem B13812545 : Blo 2155435 13812545 := bstep (se 2 (by rfl) ⟨5179704, by rfl⟩ : syracuseStep 13812545 = 10359409) B10359409
theorem B36833453 : Blo 2155435 36833453 := bstep (se 3 (by rfl) ⟨6906272, by rfl⟩ : syracuseStep 36833453 = 13812545) B13812545
theorem B24555635 : Blo 2155435 24555635 := bstep (se 1 (by rfl) ⟨18416726, by rfl⟩ : syracuseStep 24555635 = 36833453) B36833453
theorem B16370423 : Blo 2155435 16370423 := bstep (se 1 (by rfl) ⟨12277817, by rfl⟩ : syracuseStep 16370423 = 24555635) B24555635
theorem B10913615 : Blo 2155435 10913615 := bstep (se 1 (by rfl) ⟨8185211, by rfl⟩ : syracuseStep 10913615 = 16370423) B16370423
theorem B7275743 : Blo 2155435 7275743 := bstep (se 1 (by rfl) ⟨5456807, by rfl⟩ : syracuseStep 7275743 = 10913615) B10913615
theorem B4850495 : Blo 2155435 4850495 := bstep (se 1 (by rfl) ⟨3637871, by rfl⟩ : syracuseStep 4850495 = 7275743) B7275743
theorem B3233663 : Blo 2155435 3233663 := bstep (se 1 (by rfl) ⟨2425247, by rfl⟩ : syracuseStep 3233663 = 4850495) B4850495
theorem B2155775 : Blo 2155435 2155775 := bstep (se 1 (by rfl) ⟨1616831, by rfl⟩ : syracuseStep 2155775 = 3233663) B3233663
theorem B3233669 : Blo 2155435 3233669 := bbase (se 4 (by rfl) ⟨303156, by rfl⟩ : syracuseStep 3233669 = 606313) (by norm_num)
theorem B2155779 : Blo 2155435 2155779 := bstep (se 1 (by rfl) ⟨1616834, by rfl⟩ : syracuseStep 2155779 = 3233669) B3233669
theorem B3637885 : Blo 2155435 3637885 := bbase (se 3 (by rfl) ⟨682103, by rfl⟩ : syracuseStep 3637885 = 1364207) (by norm_num)
theorem B4850513 : Blo 2155435 4850513 := bstep (se 2 (by rfl) ⟨1818942, by rfl⟩ : syracuseStep 4850513 = 3637885) B3637885
theorem B3233675 : Blo 2155435 3233675 := bstep (se 1 (by rfl) ⟨2425256, by rfl⟩ : syracuseStep 3233675 = 4850513) B4850513
theorem B2155783 : Blo 2155435 2155783 := bstep (se 1 (by rfl) ⟨1616837, by rfl⟩ : syracuseStep 2155783 = 3233675) B3233675
theorem B2425261 : Blo 2155435 2425261 := bbase (se 3 (by rfl) ⟨454736, by rfl⟩ : syracuseStep 2425261 = 909473) (by norm_num)
theorem B3233681 : Blo 2155435 3233681 := bstep (se 2 (by rfl) ⟨1212630, by rfl⟩ : syracuseStep 3233681 = 2425261) B2425261
theorem B2155787 : Blo 2155435 2155787 := bstep (se 1 (by rfl) ⟨1616840, by rfl⟩ : syracuseStep 2155787 = 3233681) B3233681
theorem B7275797 : Blo 2155435 7275797 := bbase (se 6 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 7275797 = 341053) (by norm_num)
theorem B4850531 : Blo 2155435 4850531 := bstep (se 1 (by rfl) ⟨3637898, by rfl⟩ : syracuseStep 4850531 = 7275797) B7275797
theorem B3233687 : Blo 2155435 3233687 := bstep (se 1 (by rfl) ⟨2425265, by rfl⟩ : syracuseStep 3233687 = 4850531) B4850531
theorem B2155791 : Blo 2155435 2155791 := bstep (se 1 (by rfl) ⟨1616843, by rfl⟩ : syracuseStep 2155791 = 3233687) B3233687
theorem B3233693 : Blo 2155435 3233693 := bbase (se 3 (by rfl) ⟨606317, by rfl⟩ : syracuseStep 3233693 = 1212635) (by norm_num)
theorem B2155795 : Blo 2155435 2155795 := bstep (se 1 (by rfl) ⟨1616846, by rfl⟩ : syracuseStep 2155795 = 3233693) B3233693
theorem B4850549 : Blo 2155435 4850549 := bbase (se 5 (by rfl) ⟨227369, by rfl⟩ : syracuseStep 4850549 = 454739) (by norm_num)
theorem B3233699 : Blo 2155435 3233699 := bstep (se 1 (by rfl) ⟨2425274, by rfl⟩ : syracuseStep 3233699 = 4850549) B4850549
theorem B2155799 : Blo 2155435 2155799 := bstep (se 1 (by rfl) ⟨1616849, by rfl⟩ : syracuseStep 2155799 = 3233699) B3233699
theorem B2458369 : Blo 2155435 2458369 := bbase (se 2 (by rfl) ⟨921888, by rfl⟩ : syracuseStep 2458369 = 1843777) (by norm_num)
theorem B13111301 : Blo 2155435 13111301 := bstep (se 4 (by rfl) ⟨1229184, by rfl⟩ : syracuseStep 13111301 = 2458369) B2458369
theorem B8740867 : Blo 2155435 8740867 := bstep (se 1 (by rfl) ⟨6555650, by rfl⟩ : syracuseStep 8740867 = 13111301) B13111301
theorem B11654489 : Blo 2155435 11654489 := bstep (se 2 (by rfl) ⟨4370433, by rfl⟩ : syracuseStep 11654489 = 8740867) B8740867
theorem B31078637 : Blo 2155435 31078637 := bstep (se 3 (by rfl) ⟨5827244, by rfl⟩ : syracuseStep 31078637 = 11654489) B11654489
theorem B20719091 : Blo 2155435 20719091 := bstep (se 1 (by rfl) ⟨15539318, by rfl⟩ : syracuseStep 20719091 = 31078637) B31078637
theorem B13812727 : Blo 2155435 13812727 := bstep (se 1 (by rfl) ⟨10359545, by rfl⟩ : syracuseStep 13812727 = 20719091) B20719091
theorem B18416969 : Blo 2155435 18416969 := bstep (se 2 (by rfl) ⟨6906363, by rfl⟩ : syracuseStep 18416969 = 13812727) B13812727
theorem B12277979 : Blo 2155435 12277979 := bstep (se 1 (by rfl) ⟨9208484, by rfl⟩ : syracuseStep 12277979 = 18416969) B18416969
theorem B8185319 : Blo 2155435 8185319 := bstep (se 1 (by rfl) ⟨6138989, by rfl⟩ : syracuseStep 8185319 = 12277979) B12277979
theorem B5456879 : Blo 2155435 5456879 := bstep (se 1 (by rfl) ⟨4092659, by rfl⟩ : syracuseStep 5456879 = 8185319) B8185319
theorem B3637919 : Blo 2155435 3637919 := bstep (se 1 (by rfl) ⟨2728439, by rfl⟩ : syracuseStep 3637919 = 5456879) B5456879
theorem B2425279 : Blo 2155435 2425279 := bstep (se 1 (by rfl) ⟨1818959, by rfl⟩ : syracuseStep 2425279 = 3637919) B3637919
theorem B3233705 : Blo 2155435 3233705 := bstep (se 2 (by rfl) ⟨1212639, by rfl⟩ : syracuseStep 3233705 = 2425279) B2425279
theorem B2155803 : Blo 2155435 2155803 := bstep (se 1 (by rfl) ⟨1616852, by rfl⟩ : syracuseStep 2155803 = 3233705) B3233705
theorem B8185333 : Blo 2155435 8185333 := bbase (se 5 (by rfl) ⟨383687, by rfl⟩ : syracuseStep 8185333 = 767375) (by norm_num)
theorem B10913777 : Blo 2155435 10913777 := bstep (se 2 (by rfl) ⟨4092666, by rfl⟩ : syracuseStep 10913777 = 8185333) B8185333
theorem B7275851 : Blo 2155435 7275851 := bstep (se 1 (by rfl) ⟨5456888, by rfl⟩ : syracuseStep 7275851 = 10913777) B10913777
theorem B4850567 : Blo 2155435 4850567 := bstep (se 1 (by rfl) ⟨3637925, by rfl⟩ : syracuseStep 4850567 = 7275851) B7275851
theorem B3233711 : Blo 2155435 3233711 := bstep (se 1 (by rfl) ⟨2425283, by rfl⟩ : syracuseStep 3233711 = 4850567) B4850567
theorem B2155807 : Blo 2155435 2155807 := bstep (se 1 (by rfl) ⟨1616855, by rfl⟩ : syracuseStep 2155807 = 3233711) B3233711
theorem B3233717 : Blo 2155435 3233717 := bbase (se 5 (by rfl) ⟨151580, by rfl⟩ : syracuseStep 3233717 = 303161) (by norm_num)
theorem B2155811 : Blo 2155435 2155811 := bstep (se 1 (by rfl) ⟨1616858, by rfl⟩ : syracuseStep 2155811 = 3233717) B3233717
theorem B5456909 : Blo 2155435 5456909 := bbase (se 3 (by rfl) ⟨1023170, by rfl⟩ : syracuseStep 5456909 = 2046341) (by norm_num)
theorem B3637939 : Blo 2155435 3637939 := bstep (se 1 (by rfl) ⟨2728454, by rfl⟩ : syracuseStep 3637939 = 5456909) B5456909
theorem B4850585 : Blo 2155435 4850585 := bstep (se 2 (by rfl) ⟨1818969, by rfl⟩ : syracuseStep 4850585 = 3637939) B3637939
theorem B3233723 : Blo 2155435 3233723 := bstep (se 1 (by rfl) ⟨2425292, by rfl⟩ : syracuseStep 3233723 = 4850585) B4850585
theorem B2155815 : Blo 2155435 2155815 := bstep (se 1 (by rfl) ⟨1616861, by rfl⟩ : syracuseStep 2155815 = 3233723) B3233723
theorem B2425297 : Blo 2155435 2425297 := bbase (se 2 (by rfl) ⟨909486, by rfl⟩ : syracuseStep 2425297 = 1818973) (by norm_num)
theorem B3233729 : Blo 2155435 3233729 := bstep (se 2 (by rfl) ⟨1212648, by rfl⟩ : syracuseStep 3233729 = 2425297) B2425297
theorem B2155819 : Blo 2155435 2155819 := bstep (se 1 (by rfl) ⟨1616864, by rfl⟩ : syracuseStep 2155819 = 3233729) B3233729
theorem B4604285 : Blo 2155435 4604285 := bbase (se 3 (by rfl) ⟨863303, by rfl⟩ : syracuseStep 4604285 = 1726607) (by norm_num)
theorem B3069523 : Blo 2155435 3069523 := bstep (se 1 (by rfl) ⟨2302142, by rfl⟩ : syracuseStep 3069523 = 4604285) B4604285
theorem B4092697 : Blo 2155435 4092697 := bstep (se 2 (by rfl) ⟨1534761, by rfl⟩ : syracuseStep 4092697 = 3069523) B3069523
theorem B5456929 : Blo 2155435 5456929 := bstep (se 2 (by rfl) ⟨2046348, by rfl⟩ : syracuseStep 5456929 = 4092697) B4092697
theorem B7275905 : Blo 2155435 7275905 := bstep (se 2 (by rfl) ⟨2728464, by rfl⟩ : syracuseStep 7275905 = 5456929) B5456929
theorem B4850603 : Blo 2155435 4850603 := bstep (se 1 (by rfl) ⟨3637952, by rfl⟩ : syracuseStep 4850603 = 7275905) B7275905
theorem B3233735 : Blo 2155435 3233735 := bstep (se 1 (by rfl) ⟨2425301, by rfl⟩ : syracuseStep 3233735 = 4850603) B4850603
theorem B2155823 : Blo 2155435 2155823 := bstep (se 1 (by rfl) ⟨1616867, by rfl⟩ : syracuseStep 2155823 = 3233735) B3233735
theorem B3233741 : Blo 2155435 3233741 := bbase (se 3 (by rfl) ⟨606326, by rfl⟩ : syracuseStep 3233741 = 1212653) (by norm_num)
theorem B2155827 : Blo 2155435 2155827 := bstep (se 1 (by rfl) ⟨1616870, by rfl⟩ : syracuseStep 2155827 = 3233741) B3233741
theorem B4850621 : Blo 2155435 4850621 := bbase (se 3 (by rfl) ⟨909491, by rfl⟩ : syracuseStep 4850621 = 1818983) (by norm_num)
theorem B3233747 : Blo 2155435 3233747 := bstep (se 1 (by rfl) ⟨2425310, by rfl⟩ : syracuseStep 3233747 = 4850621) B4850621
theorem B2155831 : Blo 2155435 2155831 := bstep (se 1 (by rfl) ⟨1616873, by rfl⟩ : syracuseStep 2155831 = 3233747) B3233747
theorem B3637973 : Blo 2155435 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B2425315 : Blo 2155435 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B3233753 : Blo 2155435 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B2155835 : Blo 2155435 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B4916821 : Blo 2155435 4916821 := bbase (se 8 (by rfl) ⟨28809, by rfl⟩ : syracuseStep 4916821 = 57619) (by norm_num)
theorem B6555761 : Blo 2155435 6555761 := bstep (se 2 (by rfl) ⟨2458410, by rfl⟩ : syracuseStep 6555761 = 4916821) B4916821
theorem B4370507 : Blo 2155435 4370507 := bstep (se 1 (by rfl) ⟨3277880, by rfl⟩ : syracuseStep 4370507 = 6555761) B6555761
theorem B2913671 : Blo 2155435 2913671 := bstep (se 1 (by rfl) ⟨2185253, by rfl⟩ : syracuseStep 2913671 = 4370507) B4370507
theorem B7769789 : Blo 2155435 7769789 := bstep (se 3 (by rfl) ⟨1456835, by rfl⟩ : syracuseStep 7769789 = 2913671) B2913671
theorem B5179859 : Blo 2155435 5179859 := bstep (se 1 (by rfl) ⟨3884894, by rfl⟩ : syracuseStep 5179859 = 7769789) B7769789
theorem B3453239 : Blo 2155435 3453239 := bstep (se 1 (by rfl) ⟨2589929, by rfl⟩ : syracuseStep 3453239 = 5179859) B5179859
theorem B9208637 : Blo 2155435 9208637 := bstep (se 3 (by rfl) ⟨1726619, by rfl⟩ : syracuseStep 9208637 = 3453239) B3453239
theorem B6139091 : Blo 2155435 6139091 := bstep (se 1 (by rfl) ⟨4604318, by rfl⟩ : syracuseStep 6139091 = 9208637) B9208637
theorem B16370909 : Blo 2155435 16370909 := bstep (se 3 (by rfl) ⟨3069545, by rfl⟩ : syracuseStep 16370909 = 6139091) B6139091
theorem B10913939 : Blo 2155435 10913939 := bstep (se 1 (by rfl) ⟨8185454, by rfl⟩ : syracuseStep 10913939 = 16370909) B16370909
theorem B7275959 : Blo 2155435 7275959 := bstep (se 1 (by rfl) ⟨5456969, by rfl⟩ : syracuseStep 7275959 = 10913939) B10913939
theorem B4850639 : Blo 2155435 4850639 := bstep (se 1 (by rfl) ⟨3637979, by rfl⟩ : syracuseStep 4850639 = 7275959) B7275959
theorem B3233759 : Blo 2155435 3233759 := bstep (se 1 (by rfl) ⟨2425319, by rfl⟩ : syracuseStep 3233759 = 4850639) B4850639
theorem B2155839 : Blo 2155435 2155839 := bstep (se 1 (by rfl) ⟨1616879, by rfl⟩ : syracuseStep 2155839 = 3233759) B3233759
theorem B3233765 : Blo 2155435 3233765 := bbase (se 4 (by rfl) ⟨303165, by rfl⟩ : syracuseStep 3233765 = 606331) (by norm_num)
theorem B2155843 : Blo 2155435 2155843 := bstep (se 1 (by rfl) ⟨1616882, by rfl⟩ : syracuseStep 2155843 = 3233765) B3233765
theorem B3548125 : Blo 2155435 3548125 := bbase (se 3 (by rfl) ⟨665273, by rfl⟩ : syracuseStep 3548125 = 1330547) (by norm_num)
theorem B4730833 : Blo 2155435 4730833 := bstep (se 2 (by rfl) ⟨1774062, by rfl⟩ : syracuseStep 4730833 = 3548125) B3548125
theorem B6307777 : Blo 2155435 6307777 := bstep (se 2 (by rfl) ⟨2365416, by rfl⟩ : syracuseStep 6307777 = 4730833) B4730833
theorem B33641477 : Blo 2155435 33641477 := bstep (se 4 (by rfl) ⟨3153888, by rfl⟩ : syracuseStep 33641477 = 6307777) B6307777
theorem B22427651 : Blo 2155435 22427651 := bstep (se 1 (by rfl) ⟨16820738, by rfl⟩ : syracuseStep 22427651 = 33641477) B33641477
theorem B59807069 : Blo 2155435 59807069 := bstep (se 3 (by rfl) ⟨11213825, by rfl⟩ : syracuseStep 59807069 = 22427651) B22427651
theorem B39871379 : Blo 2155435 39871379 := bstep (se 1 (by rfl) ⟨29903534, by rfl⟩ : syracuseStep 39871379 = 59807069) B59807069
theorem B26580919 : Blo 2155435 26580919 := bstep (se 1 (by rfl) ⟨19935689, by rfl⟩ : syracuseStep 26580919 = 39871379) B39871379
theorem B35441225 : Blo 2155435 35441225 := bstep (se 2 (by rfl) ⟨13290459, by rfl⟩ : syracuseStep 35441225 = 26580919) B26580919
theorem B23627483 : Blo 2155435 23627483 := bstep (se 1 (by rfl) ⟨17720612, by rfl⟩ : syracuseStep 23627483 = 35441225) B35441225
theorem B15751655 : Blo 2155435 15751655 := bstep (se 1 (by rfl) ⟨11813741, by rfl⟩ : syracuseStep 15751655 = 23627483) B23627483
theorem B10501103 : Blo 2155435 10501103 := bstep (se 1 (by rfl) ⟨7875827, by rfl⟩ : syracuseStep 10501103 = 15751655) B15751655
theorem B28002941 : Blo 2155435 28002941 := bstep (se 3 (by rfl) ⟨5250551, by rfl⟩ : syracuseStep 28002941 = 10501103) B10501103
theorem B18668627 : Blo 2155435 18668627 := bstep (se 1 (by rfl) ⟨14001470, by rfl⟩ : syracuseStep 18668627 = 28002941) B28002941
theorem B12445751 : Blo 2155435 12445751 := bstep (se 1 (by rfl) ⟨9334313, by rfl⟩ : syracuseStep 12445751 = 18668627) B18668627
theorem B8297167 : Blo 2155435 8297167 := bstep (se 1 (by rfl) ⟨6222875, by rfl⟩ : syracuseStep 8297167 = 12445751) B12445751
theorem B11062889 : Blo 2155435 11062889 := bstep (se 2 (by rfl) ⟨4148583, by rfl⟩ : syracuseStep 11062889 = 8297167) B8297167
theorem B7375259 : Blo 2155435 7375259 := bstep (se 1 (by rfl) ⟨5531444, by rfl⟩ : syracuseStep 7375259 = 11062889) B11062889
theorem B19667357 : Blo 2155435 19667357 := bstep (se 3 (by rfl) ⟨3687629, by rfl⟩ : syracuseStep 19667357 = 7375259) B7375259
theorem B13111571 : Blo 2155435 13111571 := bstep (se 1 (by rfl) ⟨9833678, by rfl⟩ : syracuseStep 13111571 = 19667357) B19667357
theorem B8741047 : Blo 2155435 8741047 := bstep (se 1 (by rfl) ⟨6555785, by rfl⟩ : syracuseStep 8741047 = 13111571) B13111571
theorem B11654729 : Blo 2155435 11654729 := bstep (se 2 (by rfl) ⟨4370523, by rfl⟩ : syracuseStep 11654729 = 8741047) B8741047
theorem B7769819 : Blo 2155435 7769819 := bstep (se 1 (by rfl) ⟨5827364, by rfl⟩ : syracuseStep 7769819 = 11654729) B11654729
theorem B5179879 : Blo 2155435 5179879 := bstep (se 1 (by rfl) ⟨3884909, by rfl⟩ : syracuseStep 5179879 = 7769819) B7769819
theorem B6906505 : Blo 2155435 6906505 := bstep (se 2 (by rfl) ⟨2589939, by rfl⟩ : syracuseStep 6906505 = 5179879) B5179879
theorem B9208673 : Blo 2155435 9208673 := bstep (se 2 (by rfl) ⟨3453252, by rfl⟩ : syracuseStep 9208673 = 6906505) B6906505
theorem B6139115 : Blo 2155435 6139115 := bstep (se 1 (by rfl) ⟨4604336, by rfl⟩ : syracuseStep 6139115 = 9208673) B9208673
theorem B4092743 : Blo 2155435 4092743 := bstep (se 1 (by rfl) ⟨3069557, by rfl⟩ : syracuseStep 4092743 = 6139115) B6139115
theorem B2728495 : Blo 2155435 2728495 := bstep (se 1 (by rfl) ⟨2046371, by rfl⟩ : syracuseStep 2728495 = 4092743) B4092743
theorem B3637993 : Blo 2155435 3637993 := bstep (se 2 (by rfl) ⟨1364247, by rfl⟩ : syracuseStep 3637993 = 2728495) B2728495
theorem B4850657 : Blo 2155435 4850657 := bstep (se 2 (by rfl) ⟨1818996, by rfl⟩ : syracuseStep 4850657 = 3637993) B3637993
theorem B3233771 : Blo 2155435 3233771 := bstep (se 1 (by rfl) ⟨2425328, by rfl⟩ : syracuseStep 3233771 = 4850657) B4850657
theorem B2155847 : Blo 2155435 2155847 := bstep (se 1 (by rfl) ⟨1616885, by rfl⟩ : syracuseStep 2155847 = 3233771) B3233771
theorem B2425333 : Blo 2155435 2425333 := bbase (se 5 (by rfl) ⟨113687, by rfl⟩ : syracuseStep 2425333 = 227375) (by norm_num)
theorem B3233777 : Blo 2155435 3233777 := bstep (se 2 (by rfl) ⟨1212666, by rfl⟩ : syracuseStep 3233777 = 2425333) B2425333
theorem B2155851 : Blo 2155435 2155851 := bstep (se 1 (by rfl) ⟨1616888, by rfl⟩ : syracuseStep 2155851 = 3233777) B3233777
theorem B2728505 : Blo 2155435 2728505 := bbase (se 2 (by rfl) ⟨1023189, by rfl⟩ : syracuseStep 2728505 = 2046379) (by norm_num)
theorem B7276013 : Blo 2155435 7276013 := bstep (se 3 (by rfl) ⟨1364252, by rfl⟩ : syracuseStep 7276013 = 2728505) B2728505
theorem B4850675 : Blo 2155435 4850675 := bstep (se 1 (by rfl) ⟨3638006, by rfl⟩ : syracuseStep 4850675 = 7276013) B7276013
theorem B3233783 : Blo 2155435 3233783 := bstep (se 1 (by rfl) ⟨2425337, by rfl⟩ : syracuseStep 3233783 = 4850675) B4850675
theorem B2155855 : Blo 2155435 2155855 := bstep (se 1 (by rfl) ⟨1616891, by rfl⟩ : syracuseStep 2155855 = 3233783) B3233783
theorem B3233789 : Blo 2155435 3233789 := bbase (se 3 (by rfl) ⟨606335, by rfl⟩ : syracuseStep 3233789 = 1212671) (by norm_num)
theorem B2155859 : Blo 2155435 2155859 := bstep (se 1 (by rfl) ⟨1616894, by rfl⟩ : syracuseStep 2155859 = 3233789) B3233789
theorem B4850693 : Blo 2155435 4850693 := bbase (se 4 (by rfl) ⟨454752, by rfl⟩ : syracuseStep 4850693 = 909505) (by norm_num)
theorem B3233795 : Blo 2155435 3233795 := bstep (se 1 (by rfl) ⟨2425346, by rfl⟩ : syracuseStep 3233795 = 4850693) B4850693
theorem B2155863 : Blo 2155435 2155863 := bstep (se 1 (by rfl) ⟨1616897, by rfl⟩ : syracuseStep 2155863 = 3233795) B3233795
theorem B4092781 : Blo 2155435 4092781 := bbase (se 3 (by rfl) ⟨767396, by rfl⟩ : syracuseStep 4092781 = 1534793) (by norm_num)
theorem B5457041 : Blo 2155435 5457041 := bstep (se 2 (by rfl) ⟨2046390, by rfl⟩ : syracuseStep 5457041 = 4092781) B4092781
theorem B3638027 : Blo 2155435 3638027 := bstep (se 1 (by rfl) ⟨2728520, by rfl⟩ : syracuseStep 3638027 = 5457041) B5457041
theorem B2425351 : Blo 2155435 2425351 := bstep (se 1 (by rfl) ⟨1819013, by rfl⟩ : syracuseStep 2425351 = 3638027) B3638027
theorem B3233801 : Blo 2155435 3233801 := bstep (se 2 (by rfl) ⟨1212675, by rfl⟩ : syracuseStep 3233801 = 2425351) B2425351
theorem B2155867 : Blo 2155435 2155867 := bstep (se 1 (by rfl) ⟨1616900, by rfl⟩ : syracuseStep 2155867 = 3233801) B3233801
theorem B10914101 : Blo 2155435 10914101 := bbase (se 5 (by rfl) ⟨511598, by rfl⟩ : syracuseStep 10914101 = 1023197) (by norm_num)
theorem B7276067 : Blo 2155435 7276067 := bstep (se 1 (by rfl) ⟨5457050, by rfl⟩ : syracuseStep 7276067 = 10914101) B10914101
theorem B4850711 : Blo 2155435 4850711 := bstep (se 1 (by rfl) ⟨3638033, by rfl⟩ : syracuseStep 4850711 = 7276067) B7276067
theorem B3233807 : Blo 2155435 3233807 := bstep (se 1 (by rfl) ⟨2425355, by rfl⟩ : syracuseStep 3233807 = 4850711) B4850711
theorem B2155871 : Blo 2155435 2155871 := bstep (se 1 (by rfl) ⟨1616903, by rfl⟩ : syracuseStep 2155871 = 3233807) B3233807
theorem B3233813 : Blo 2155435 3233813 := bbase (se 6 (by rfl) ⟨75792, by rfl⟩ : syracuseStep 3233813 = 151585) (by norm_num)
theorem B2155875 : Blo 2155435 2155875 := bstep (se 1 (by rfl) ⟨1616906, by rfl⟩ : syracuseStep 2155875 = 3233813) B3233813
theorem B2913725 : Blo 2155435 2913725 := bbase (se 3 (by rfl) ⟨546323, by rfl⟩ : syracuseStep 2913725 = 1092647) (by norm_num)
theorem B7769933 : Blo 2155435 7769933 := bstep (se 3 (by rfl) ⟨1456862, by rfl⟩ : syracuseStep 7769933 = 2913725) B2913725
theorem B5179955 : Blo 2155435 5179955 := bstep (se 1 (by rfl) ⟨3884966, by rfl⟩ : syracuseStep 5179955 = 7769933) B7769933
theorem B13813213 : Blo 2155435 13813213 := bstep (se 3 (by rfl) ⟨2589977, by rfl⟩ : syracuseStep 13813213 = 5179955) B5179955
theorem B18417617 : Blo 2155435 18417617 := bstep (se 2 (by rfl) ⟨6906606, by rfl⟩ : syracuseStep 18417617 = 13813213) B13813213
theorem B12278411 : Blo 2155435 12278411 := bstep (se 1 (by rfl) ⟨9208808, by rfl⟩ : syracuseStep 12278411 = 18417617) B18417617
theorem B8185607 : Blo 2155435 8185607 := bstep (se 1 (by rfl) ⟨6139205, by rfl⟩ : syracuseStep 8185607 = 12278411) B12278411
theorem B5457071 : Blo 2155435 5457071 := bstep (se 1 (by rfl) ⟨4092803, by rfl⟩ : syracuseStep 5457071 = 8185607) B8185607
theorem B3638047 : Blo 2155435 3638047 := bstep (se 1 (by rfl) ⟨2728535, by rfl⟩ : syracuseStep 3638047 = 5457071) B5457071
theorem B4850729 : Blo 2155435 4850729 := bstep (se 2 (by rfl) ⟨1819023, by rfl⟩ : syracuseStep 4850729 = 3638047) B3638047
theorem B3233819 : Blo 2155435 3233819 := bstep (se 1 (by rfl) ⟨2425364, by rfl⟩ : syracuseStep 3233819 = 4850729) B4850729
theorem B2155879 : Blo 2155435 2155879 := bstep (se 1 (by rfl) ⟨1616909, by rfl⟩ : syracuseStep 2155879 = 3233819) B3233819
theorem B2425369 : Blo 2155435 2425369 := bbase (se 2 (by rfl) ⟨909513, by rfl⟩ : syracuseStep 2425369 = 1819027) (by norm_num)
theorem B3233825 : Blo 2155435 3233825 := bstep (se 2 (by rfl) ⟨1212684, by rfl⟩ : syracuseStep 3233825 = 2425369) B2425369
theorem B2155883 : Blo 2155435 2155883 := bstep (se 1 (by rfl) ⟨1616912, by rfl⟩ : syracuseStep 2155883 = 3233825) B3233825
theorem B8185637 : Blo 2155435 8185637 := bbase (se 4 (by rfl) ⟨767403, by rfl⟩ : syracuseStep 8185637 = 1534807) (by norm_num)
theorem B5457091 : Blo 2155435 5457091 := bstep (se 1 (by rfl) ⟨4092818, by rfl⟩ : syracuseStep 5457091 = 8185637) B8185637
theorem B7276121 : Blo 2155435 7276121 := bstep (se 2 (by rfl) ⟨2728545, by rfl⟩ : syracuseStep 7276121 = 5457091) B5457091
theorem B4850747 : Blo 2155435 4850747 := bstep (se 1 (by rfl) ⟨3638060, by rfl⟩ : syracuseStep 4850747 = 7276121) B7276121
theorem B3233831 : Blo 2155435 3233831 := bstep (se 1 (by rfl) ⟨2425373, by rfl⟩ : syracuseStep 3233831 = 4850747) B4850747
theorem B2155887 : Blo 2155435 2155887 := bstep (se 1 (by rfl) ⟨1616915, by rfl⟩ : syracuseStep 2155887 = 3233831) B3233831
theorem B3233837 : Blo 2155435 3233837 := bbase (se 3 (by rfl) ⟨606344, by rfl⟩ : syracuseStep 3233837 = 1212689) (by norm_num)
theorem B2155891 : Blo 2155435 2155891 := bstep (se 1 (by rfl) ⟨1616918, by rfl⟩ : syracuseStep 2155891 = 3233837) B3233837
theorem B4850765 : Blo 2155435 4850765 := bbase (se 3 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 4850765 = 1819037) (by norm_num)
theorem B3233843 : Blo 2155435 3233843 := bstep (se 1 (by rfl) ⟨2425382, by rfl⟩ : syracuseStep 3233843 = 4850765) B4850765
theorem B2155895 : Blo 2155435 2155895 := bstep (se 1 (by rfl) ⟨1616921, by rfl⟩ : syracuseStep 2155895 = 3233843) B3233843
theorem B2728561 : Blo 2155435 2728561 := bbase (se 2 (by rfl) ⟨1023210, by rfl⟩ : syracuseStep 2728561 = 2046421) (by norm_num)
theorem B3638081 : Blo 2155435 3638081 := bstep (se 2 (by rfl) ⟨1364280, by rfl⟩ : syracuseStep 3638081 = 2728561) B2728561
theorem B2425387 : Blo 2155435 2425387 := bstep (se 1 (by rfl) ⟨1819040, by rfl⟩ : syracuseStep 2425387 = 3638081) B3638081
theorem B3233849 : Blo 2155435 3233849 := bstep (se 2 (by rfl) ⟨1212693, by rfl⟩ : syracuseStep 3233849 = 2425387) B2425387
theorem B2155899 : Blo 2155435 2155899 := bstep (se 1 (by rfl) ⟨1616924, by rfl⟩ : syracuseStep 2155899 = 3233849) B3233849
theorem B11655029 : Blo 2155435 11655029 := bbase (se 5 (by rfl) ⟨546329, by rfl⟩ : syracuseStep 11655029 = 1092659) (by norm_num)
theorem B7770019 : Blo 2155435 7770019 := bstep (se 1 (by rfl) ⟨5827514, by rfl⟩ : syracuseStep 7770019 = 11655029) B11655029
theorem B10360025 : Blo 2155435 10360025 := bstep (se 2 (by rfl) ⟨3885009, by rfl⟩ : syracuseStep 10360025 = 7770019) B7770019
theorem B6906683 : Blo 2155435 6906683 := bstep (se 1 (by rfl) ⟨5180012, by rfl⟩ : syracuseStep 6906683 = 10360025) B10360025
theorem B4604455 : Blo 2155435 4604455 := bstep (se 1 (by rfl) ⟨3453341, by rfl⟩ : syracuseStep 4604455 = 6906683) B6906683
theorem B24557093 : Blo 2155435 24557093 := bstep (se 4 (by rfl) ⟨2302227, by rfl⟩ : syracuseStep 24557093 = 4604455) B4604455
theorem B16371395 : Blo 2155435 16371395 := bstep (se 1 (by rfl) ⟨12278546, by rfl⟩ : syracuseStep 16371395 = 24557093) B24557093
theorem B10914263 : Blo 2155435 10914263 := bstep (se 1 (by rfl) ⟨8185697, by rfl⟩ : syracuseStep 10914263 = 16371395) B16371395
theorem B7276175 : Blo 2155435 7276175 := bstep (se 1 (by rfl) ⟨5457131, by rfl⟩ : syracuseStep 7276175 = 10914263) B10914263
theorem B4850783 : Blo 2155435 4850783 := bstep (se 1 (by rfl) ⟨3638087, by rfl⟩ : syracuseStep 4850783 = 7276175) B7276175
theorem B3233855 : Blo 2155435 3233855 := bstep (se 1 (by rfl) ⟨2425391, by rfl⟩ : syracuseStep 3233855 = 4850783) B4850783
theorem B2155903 : Blo 2155435 2155903 := bstep (se 1 (by rfl) ⟨1616927, by rfl⟩ : syracuseStep 2155903 = 3233855) B3233855
theorem B3233861 : Blo 2155435 3233861 := bbase (se 4 (by rfl) ⟨303174, by rfl⟩ : syracuseStep 3233861 = 606349) (by norm_num)
theorem B2155907 : Blo 2155435 2155907 := bstep (se 1 (by rfl) ⟨1616930, by rfl⟩ : syracuseStep 2155907 = 3233861) B3233861
theorem B3638101 : Blo 2155435 3638101 := bbase (se 9 (by rfl) ⟨10658, by rfl⟩ : syracuseStep 3638101 = 21317) (by norm_num)
theorem B4850801 : Blo 2155435 4850801 := bstep (se 2 (by rfl) ⟨1819050, by rfl⟩ : syracuseStep 4850801 = 3638101) B3638101
theorem B3233867 : Blo 2155435 3233867 := bstep (se 1 (by rfl) ⟨2425400, by rfl⟩ : syracuseStep 3233867 = 4850801) B4850801
theorem B2155911 : Blo 2155435 2155911 := bstep (se 1 (by rfl) ⟨1616933, by rfl⟩ : syracuseStep 2155911 = 3233867) B3233867
theorem B2425405 : Blo 2155435 2425405 := bbase (se 3 (by rfl) ⟨454763, by rfl⟩ : syracuseStep 2425405 = 909527) (by norm_num)
theorem B3233873 : Blo 2155435 3233873 := bstep (se 2 (by rfl) ⟨1212702, by rfl⟩ : syracuseStep 3233873 = 2425405) B2425405
theorem B2155915 : Blo 2155435 2155915 := bstep (se 1 (by rfl) ⟨1616936, by rfl⟩ : syracuseStep 2155915 = 3233873) B3233873
theorem B7276229 : Blo 2155435 7276229 := bbase (se 4 (by rfl) ⟨682146, by rfl⟩ : syracuseStep 7276229 = 1364293) (by norm_num)
theorem B4850819 : Blo 2155435 4850819 := bstep (se 1 (by rfl) ⟨3638114, by rfl⟩ : syracuseStep 4850819 = 7276229) B7276229
theorem B3233879 : Blo 2155435 3233879 := bstep (se 1 (by rfl) ⟨2425409, by rfl⟩ : syracuseStep 3233879 = 4850819) B4850819
theorem B2155919 : Blo 2155435 2155919 := bstep (se 1 (by rfl) ⟨1616939, by rfl⟩ : syracuseStep 2155919 = 3233879) B3233879
theorem B3233885 : Blo 2155435 3233885 := bbase (se 3 (by rfl) ⟨606353, by rfl⟩ : syracuseStep 3233885 = 1212707) (by norm_num)
theorem B2155923 : Blo 2155435 2155923 := bstep (se 1 (by rfl) ⟨1616942, by rfl⟩ : syracuseStep 2155923 = 3233885) B3233885
theorem B4850837 : Blo 2155435 4850837 := bbase (se 6 (by rfl) ⟨113691, by rfl⟩ : syracuseStep 4850837 = 227383) (by norm_num)
theorem B3233891 : Blo 2155435 3233891 := bstep (se 1 (by rfl) ⟨2425418, by rfl⟩ : syracuseStep 3233891 = 4850837) B4850837
theorem B2155927 : Blo 2155435 2155927 := bstep (se 1 (by rfl) ⟨1616945, by rfl⟩ : syracuseStep 2155927 = 3233891) B3233891
theorem B3069677 : Blo 2155435 3069677 := bbase (se 3 (by rfl) ⟨575564, by rfl⟩ : syracuseStep 3069677 = 1151129) (by norm_num)
theorem B8185805 : Blo 2155435 8185805 := bstep (se 3 (by rfl) ⟨1534838, by rfl⟩ : syracuseStep 8185805 = 3069677) B3069677
theorem B5457203 : Blo 2155435 5457203 := bstep (se 1 (by rfl) ⟨4092902, by rfl⟩ : syracuseStep 5457203 = 8185805) B8185805
theorem B3638135 : Blo 2155435 3638135 := bstep (se 1 (by rfl) ⟨2728601, by rfl⟩ : syracuseStep 3638135 = 5457203) B5457203
theorem B2425423 : Blo 2155435 2425423 := bstep (se 1 (by rfl) ⟨1819067, by rfl⟩ : syracuseStep 2425423 = 3638135) B3638135
theorem B3233897 : Blo 2155435 3233897 := bstep (se 2 (by rfl) ⟨1212711, by rfl⟩ : syracuseStep 3233897 = 2425423) B2425423
theorem B2155931 : Blo 2155435 2155931 := bstep (se 1 (by rfl) ⟨1616948, by rfl⟩ : syracuseStep 2155931 = 3233897) B3233897
theorem B4370701 : Blo 2155435 4370701 := bbase (se 3 (by rfl) ⟨819506, by rfl⟩ : syracuseStep 4370701 = 1639013) (by norm_num)
theorem B5827601 : Blo 2155435 5827601 := bstep (se 2 (by rfl) ⟨2185350, by rfl⟩ : syracuseStep 5827601 = 4370701) B4370701
theorem B3885067 : Blo 2155435 3885067 := bstep (se 1 (by rfl) ⟨2913800, by rfl⟩ : syracuseStep 3885067 = 5827601) B5827601
theorem B20720357 : Blo 2155435 20720357 := bstep (se 4 (by rfl) ⟨1942533, by rfl⟩ : syracuseStep 20720357 = 3885067) B3885067
theorem B13813571 : Blo 2155435 13813571 := bstep (se 1 (by rfl) ⟨10360178, by rfl⟩ : syracuseStep 13813571 = 20720357) B20720357
theorem B9209047 : Blo 2155435 9209047 := bstep (se 1 (by rfl) ⟨6906785, by rfl⟩ : syracuseStep 9209047 = 13813571) B13813571
theorem B12278729 : Blo 2155435 12278729 := bstep (se 2 (by rfl) ⟨4604523, by rfl⟩ : syracuseStep 12278729 = 9209047) B9209047
theorem B8185819 : Blo 2155435 8185819 := bstep (se 1 (by rfl) ⟨6139364, by rfl⟩ : syracuseStep 8185819 = 12278729) B12278729
theorem B10914425 : Blo 2155435 10914425 := bstep (se 2 (by rfl) ⟨4092909, by rfl⟩ : syracuseStep 10914425 = 8185819) B8185819
theorem B7276283 : Blo 2155435 7276283 := bstep (se 1 (by rfl) ⟨5457212, by rfl⟩ : syracuseStep 7276283 = 10914425) B10914425
theorem B4850855 : Blo 2155435 4850855 := bstep (se 1 (by rfl) ⟨3638141, by rfl⟩ : syracuseStep 4850855 = 7276283) B7276283
theorem B3233903 : Blo 2155435 3233903 := bstep (se 1 (by rfl) ⟨2425427, by rfl⟩ : syracuseStep 3233903 = 4850855) B4850855
theorem B2155935 : Blo 2155435 2155935 := bstep (se 1 (by rfl) ⟨1616951, by rfl⟩ : syracuseStep 2155935 = 3233903) B3233903
theorem B3233909 : Blo 2155435 3233909 := bbase (se 5 (by rfl) ⟨151589, by rfl⟩ : syracuseStep 3233909 = 303179) (by norm_num)
theorem B2155939 : Blo 2155435 2155939 := bstep (se 1 (by rfl) ⟨1616954, by rfl⟩ : syracuseStep 2155939 = 3233909) B3233909
theorem B4092925 : Blo 2155435 4092925 := bbase (se 3 (by rfl) ⟨767423, by rfl⟩ : syracuseStep 4092925 = 1534847) (by norm_num)
theorem B5457233 : Blo 2155435 5457233 := bstep (se 2 (by rfl) ⟨2046462, by rfl⟩ : syracuseStep 5457233 = 4092925) B4092925
theorem B3638155 : Blo 2155435 3638155 := bstep (se 1 (by rfl) ⟨2728616, by rfl⟩ : syracuseStep 3638155 = 5457233) B5457233
theorem B4850873 : Blo 2155435 4850873 := bstep (se 2 (by rfl) ⟨1819077, by rfl⟩ : syracuseStep 4850873 = 3638155) B3638155
theorem B3233915 : Blo 2155435 3233915 := bstep (se 1 (by rfl) ⟨2425436, by rfl⟩ : syracuseStep 3233915 = 4850873) B4850873
theorem B2155943 : Blo 2155435 2155943 := bstep (se 1 (by rfl) ⟨1616957, by rfl⟩ : syracuseStep 2155943 = 3233915) B3233915
theorem B2425441 : Blo 2155435 2425441 := bbase (se 2 (by rfl) ⟨909540, by rfl⟩ : syracuseStep 2425441 = 1819081) (by norm_num)
theorem B3233921 : Blo 2155435 3233921 := bstep (se 2 (by rfl) ⟨1212720, by rfl⟩ : syracuseStep 3233921 = 2425441) B2425441
theorem B2155947 : Blo 2155435 2155947 := bstep (se 1 (by rfl) ⟨1616960, by rfl⟩ : syracuseStep 2155947 = 3233921) B3233921
theorem B5457253 : Blo 2155435 5457253 := bbase (se 4 (by rfl) ⟨511617, by rfl⟩ : syracuseStep 5457253 = 1023235) (by norm_num)
theorem B7276337 : Blo 2155435 7276337 := bstep (se 2 (by rfl) ⟨2728626, by rfl⟩ : syracuseStep 7276337 = 5457253) B5457253
theorem B4850891 : Blo 2155435 4850891 := bstep (se 1 (by rfl) ⟨3638168, by rfl⟩ : syracuseStep 4850891 = 7276337) B7276337
theorem B3233927 : Blo 2155435 3233927 := bstep (se 1 (by rfl) ⟨2425445, by rfl⟩ : syracuseStep 3233927 = 4850891) B4850891
theorem B2155951 : Blo 2155435 2155951 := bstep (se 1 (by rfl) ⟨1616963, by rfl⟩ : syracuseStep 2155951 = 3233927) B3233927
theorem B3233933 : Blo 2155435 3233933 := bbase (se 3 (by rfl) ⟨606362, by rfl⟩ : syracuseStep 3233933 = 1212725) (by norm_num)
theorem B2155955 : Blo 2155435 2155955 := bstep (se 1 (by rfl) ⟨1616966, by rfl⟩ : syracuseStep 2155955 = 3233933) B3233933
theorem B4850909 : Blo 2155435 4850909 := bbase (se 3 (by rfl) ⟨909545, by rfl⟩ : syracuseStep 4850909 = 1819091) (by norm_num)
theorem B3233939 : Blo 2155435 3233939 := bstep (se 1 (by rfl) ⟨2425454, by rfl⟩ : syracuseStep 3233939 = 4850909) B4850909
theorem B2155959 : Blo 2155435 2155959 := bstep (se 1 (by rfl) ⟨1616969, by rfl⟩ : syracuseStep 2155959 = 3233939) B3233939
theorem B3638189 : Blo 2155435 3638189 := bbase (se 3 (by rfl) ⟨682160, by rfl⟩ : syracuseStep 3638189 = 1364321) (by norm_num)
theorem B2425459 : Blo 2155435 2425459 := bstep (se 1 (by rfl) ⟨1819094, by rfl⟩ : syracuseStep 2425459 = 3638189) B3638189
theorem B3233945 : Blo 2155435 3233945 := bstep (se 2 (by rfl) ⟨1212729, by rfl⟩ : syracuseStep 3233945 = 2425459) B2425459
theorem B2155963 : Blo 2155435 2155963 := bstep (se 1 (by rfl) ⟨1616972, by rfl⟩ : syracuseStep 2155963 = 3233945) B3233945
theorem B7876261 : Blo 2155435 7876261 := bbase (se 4 (by rfl) ⟨738399, by rfl⟩ : syracuseStep 7876261 = 1476799) (by norm_num)
theorem B42006725 : Blo 2155435 42006725 := bstep (se 4 (by rfl) ⟨3938130, by rfl⟩ : syracuseStep 42006725 = 7876261) B7876261
theorem B28004483 : Blo 2155435 28004483 := bstep (se 1 (by rfl) ⟨21003362, by rfl⟩ : syracuseStep 28004483 = 42006725) B42006725
theorem B18669655 : Blo 2155435 18669655 := bstep (se 1 (by rfl) ⟨14002241, by rfl⟩ : syracuseStep 18669655 = 28004483) B28004483
theorem B99571493 : Blo 2155435 99571493 := bstep (se 4 (by rfl) ⟨9334827, by rfl⟩ : syracuseStep 99571493 = 18669655) B18669655
theorem B66380995 : Blo 2155435 66380995 := bstep (se 1 (by rfl) ⟨49785746, by rfl⟩ : syracuseStep 66380995 = 99571493) B99571493
theorem B88507993 : Blo 2155435 88507993 := bstep (se 2 (by rfl) ⟨33190497, by rfl⟩ : syracuseStep 88507993 = 66380995) B66380995
theorem B118010657 : Blo 2155435 118010657 := bstep (se 2 (by rfl) ⟨44253996, by rfl⟩ : syracuseStep 118010657 = 88507993) B88507993
theorem B78673771 : Blo 2155435 78673771 := bstep (se 1 (by rfl) ⟨59005328, by rfl⟩ : syracuseStep 78673771 = 118010657) B118010657
theorem B104898361 : Blo 2155435 104898361 := bstep (se 2 (by rfl) ⟨39336885, by rfl⟩ : syracuseStep 104898361 = 78673771) B78673771
theorem B139864481 : Blo 2155435 139864481 := bstep (se 2 (by rfl) ⟨52449180, by rfl⟩ : syracuseStep 139864481 = 104898361) B104898361
theorem B93242987 : Blo 2155435 93242987 := bstep (se 1 (by rfl) ⟨69932240, by rfl⟩ : syracuseStep 93242987 = 139864481) B139864481
theorem B62161991 : Blo 2155435 62161991 := bstep (se 1 (by rfl) ⟨46621493, by rfl⟩ : syracuseStep 62161991 = 93242987) B93242987
theorem B41441327 : Blo 2155435 41441327 := bstep (se 1 (by rfl) ⟨31080995, by rfl⟩ : syracuseStep 41441327 = 62161991) B62161991
theorem B27627551 : Blo 2155435 27627551 := bstep (se 1 (by rfl) ⟨20720663, by rfl⟩ : syracuseStep 27627551 = 41441327) B41441327
theorem B18418367 : Blo 2155435 18418367 := bstep (se 1 (by rfl) ⟨13813775, by rfl⟩ : syracuseStep 18418367 = 27627551) B27627551
theorem B12278911 : Blo 2155435 12278911 := bstep (se 1 (by rfl) ⟨9209183, by rfl⟩ : syracuseStep 12278911 = 18418367) B18418367
theorem B16371881 : Blo 2155435 16371881 := bstep (se 2 (by rfl) ⟨6139455, by rfl⟩ : syracuseStep 16371881 = 12278911) B12278911
theorem B10914587 : Blo 2155435 10914587 := bstep (se 1 (by rfl) ⟨8185940, by rfl⟩ : syracuseStep 10914587 = 16371881) B16371881
theorem B7276391 : Blo 2155435 7276391 := bstep (se 1 (by rfl) ⟨5457293, by rfl⟩ : syracuseStep 7276391 = 10914587) B10914587
theorem B4850927 : Blo 2155435 4850927 := bstep (se 1 (by rfl) ⟨3638195, by rfl⟩ : syracuseStep 4850927 = 7276391) B7276391
theorem B3233951 : Blo 2155435 3233951 := bstep (se 1 (by rfl) ⟨2425463, by rfl⟩ : syracuseStep 3233951 = 4850927) B4850927
theorem B2155967 : Blo 2155435 2155967 := bstep (se 1 (by rfl) ⟨1616975, by rfl⟩ : syracuseStep 2155967 = 3233951) B3233951
theorem B3233957 : Blo 2155435 3233957 := bbase (se 4 (by rfl) ⟨303183, by rfl⟩ : syracuseStep 3233957 = 606367) (by norm_num)
theorem B2155971 : Blo 2155435 2155971 := bstep (se 1 (by rfl) ⟨1616978, by rfl⟩ : syracuseStep 2155971 = 3233957) B3233957
theorem B2728657 : Blo 2155435 2728657 := bbase (se 2 (by rfl) ⟨1023246, by rfl⟩ : syracuseStep 2728657 = 2046493) (by norm_num)
theorem B3638209 : Blo 2155435 3638209 := bstep (se 2 (by rfl) ⟨1364328, by rfl⟩ : syracuseStep 3638209 = 2728657) B2728657
theorem B4850945 : Blo 2155435 4850945 := bstep (se 2 (by rfl) ⟨1819104, by rfl⟩ : syracuseStep 4850945 = 3638209) B3638209
theorem B3233963 : Blo 2155435 3233963 := bstep (se 1 (by rfl) ⟨2425472, by rfl⟩ : syracuseStep 3233963 = 4850945) B4850945
theorem B2155975 : Blo 2155435 2155975 := bstep (se 1 (by rfl) ⟨1616981, by rfl⟩ : syracuseStep 2155975 = 3233963) B3233963
theorem B2425477 : Blo 2155435 2425477 := bbase (se 4 (by rfl) ⟨227388, by rfl⟩ : syracuseStep 2425477 = 454777) (by norm_num)
theorem B3233969 : Blo 2155435 3233969 := bstep (se 2 (by rfl) ⟨1212738, by rfl⟩ : syracuseStep 3233969 = 2425477) B2425477
theorem B2155979 : Blo 2155435 2155979 := bstep (se 1 (by rfl) ⟨1616984, by rfl⟩ : syracuseStep 2155979 = 3233969) B3233969
theorem B5827733 : Blo 2155435 5827733 := bbase (se 6 (by rfl) ⟨136587, by rfl⟩ : syracuseStep 5827733 = 273175) (by norm_num)
theorem B3885155 : Blo 2155435 3885155 := bstep (se 1 (by rfl) ⟨2913866, by rfl⟩ : syracuseStep 3885155 = 5827733) B5827733
theorem B2590103 : Blo 2155435 2590103 := bstep (se 1 (by rfl) ⟨1942577, by rfl⟩ : syracuseStep 2590103 = 3885155) B3885155
theorem B6906941 : Blo 2155435 6906941 := bstep (se 3 (by rfl) ⟨1295051, by rfl⟩ : syracuseStep 6906941 = 2590103) B2590103
theorem B4604627 : Blo 2155435 4604627 := bstep (se 1 (by rfl) ⟨3453470, by rfl⟩ : syracuseStep 4604627 = 6906941) B6906941
theorem B3069751 : Blo 2155435 3069751 := bstep (se 1 (by rfl) ⟨2302313, by rfl⟩ : syracuseStep 3069751 = 4604627) B4604627
theorem B4093001 : Blo 2155435 4093001 := bstep (se 2 (by rfl) ⟨1534875, by rfl⟩ : syracuseStep 4093001 = 3069751) B3069751
theorem B2728667 : Blo 2155435 2728667 := bstep (se 1 (by rfl) ⟨2046500, by rfl⟩ : syracuseStep 2728667 = 4093001) B4093001
theorem B7276445 : Blo 2155435 7276445 := bstep (se 3 (by rfl) ⟨1364333, by rfl⟩ : syracuseStep 7276445 = 2728667) B2728667
theorem B4850963 : Blo 2155435 4850963 := bstep (se 1 (by rfl) ⟨3638222, by rfl⟩ : syracuseStep 4850963 = 7276445) B7276445
theorem B3233975 : Blo 2155435 3233975 := bstep (se 1 (by rfl) ⟨2425481, by rfl⟩ : syracuseStep 3233975 = 4850963) B4850963
theorem B2155983 : Blo 2155435 2155983 := bstep (se 1 (by rfl) ⟨1616987, by rfl⟩ : syracuseStep 2155983 = 3233975) B3233975
theorem B3233981 : Blo 2155435 3233981 := bbase (se 3 (by rfl) ⟨606371, by rfl⟩ : syracuseStep 3233981 = 1212743) (by norm_num)
theorem B2155987 : Blo 2155435 2155987 := bstep (se 1 (by rfl) ⟨1616990, by rfl⟩ : syracuseStep 2155987 = 3233981) B3233981
theorem B4850981 : Blo 2155435 4850981 := bbase (se 4 (by rfl) ⟨454779, by rfl⟩ : syracuseStep 4850981 = 909559) (by norm_num)
theorem B3233987 : Blo 2155435 3233987 := bstep (se 1 (by rfl) ⟨2425490, by rfl⟩ : syracuseStep 3233987 = 4850981) B4850981
theorem B2155991 : Blo 2155435 2155991 := bstep (se 1 (by rfl) ⟨1616993, by rfl⟩ : syracuseStep 2155991 = 3233987) B3233987
theorem B5457365 : Blo 2155435 5457365 := bbase (se 7 (by rfl) ⟨63953, by rfl⟩ : syracuseStep 5457365 = 127907) (by norm_num)
theorem B3638243 : Blo 2155435 3638243 := bstep (se 1 (by rfl) ⟨2728682, by rfl⟩ : syracuseStep 3638243 = 5457365) B5457365
theorem B2425495 : Blo 2155435 2425495 := bstep (se 1 (by rfl) ⟨1819121, by rfl⟩ : syracuseStep 2425495 = 3638243) B3638243
theorem B3233993 : Blo 2155435 3233993 := bstep (se 2 (by rfl) ⟨1212747, by rfl⟩ : syracuseStep 3233993 = 2425495) B2425495
theorem B2155995 : Blo 2155435 2155995 := bstep (se 1 (by rfl) ⟨1616996, by rfl⟩ : syracuseStep 2155995 = 3233993) B3233993
theorem B4667485 : Blo 2155435 4667485 := bbase (se 3 (by rfl) ⟨875153, by rfl⟩ : syracuseStep 4667485 = 1750307) (by norm_num)
theorem B6223313 : Blo 2155435 6223313 := bstep (se 2 (by rfl) ⟨2333742, by rfl⟩ : syracuseStep 6223313 = 4667485) B4667485
theorem B4148875 : Blo 2155435 4148875 := bstep (se 1 (by rfl) ⟨3111656, by rfl⟩ : syracuseStep 4148875 = 6223313) B6223313
theorem B5531833 : Blo 2155435 5531833 := bstep (se 2 (by rfl) ⟨2074437, by rfl⟩ : syracuseStep 5531833 = 4148875) B4148875
theorem B29503109 : Blo 2155435 29503109 := bstep (se 4 (by rfl) ⟨2765916, by rfl⟩ : syracuseStep 29503109 = 5531833) B5531833
theorem B19668739 : Blo 2155435 19668739 := bstep (se 1 (by rfl) ⟨14751554, by rfl⟩ : syracuseStep 19668739 = 29503109) B29503109
theorem B26224985 : Blo 2155435 26224985 := bstep (se 2 (by rfl) ⟨9834369, by rfl⟩ : syracuseStep 26224985 = 19668739) B19668739
theorem B17483323 : Blo 2155435 17483323 := bstep (se 1 (by rfl) ⟨13112492, by rfl⟩ : syracuseStep 17483323 = 26224985) B26224985
theorem B23311097 : Blo 2155435 23311097 := bstep (se 2 (by rfl) ⟨8741661, by rfl⟩ : syracuseStep 23311097 = 17483323) B17483323
theorem B15540731 : Blo 2155435 15540731 := bstep (se 1 (by rfl) ⟨11655548, by rfl⟩ : syracuseStep 15540731 = 23311097) B23311097
theorem B10360487 : Blo 2155435 10360487 := bstep (se 1 (by rfl) ⟨7770365, by rfl⟩ : syracuseStep 10360487 = 15540731) B15540731
theorem B6906991 : Blo 2155435 6906991 := bstep (se 1 (by rfl) ⟨5180243, by rfl⟩ : syracuseStep 6906991 = 10360487) B10360487
theorem B9209321 : Blo 2155435 9209321 := bstep (se 2 (by rfl) ⟨3453495, by rfl⟩ : syracuseStep 9209321 = 6906991) B6906991
theorem B6139547 : Blo 2155435 6139547 := bstep (se 1 (by rfl) ⟨4604660, by rfl⟩ : syracuseStep 6139547 = 9209321) B9209321
theorem B4093031 : Blo 2155435 4093031 := bstep (se 1 (by rfl) ⟨3069773, by rfl⟩ : syracuseStep 4093031 = 6139547) B6139547
theorem B10914749 : Blo 2155435 10914749 := bstep (se 3 (by rfl) ⟨2046515, by rfl⟩ : syracuseStep 10914749 = 4093031) B4093031
theorem B7276499 : Blo 2155435 7276499 := bstep (se 1 (by rfl) ⟨5457374, by rfl⟩ : syracuseStep 7276499 = 10914749) B10914749
theorem B4850999 : Blo 2155435 4850999 := bstep (se 1 (by rfl) ⟨3638249, by rfl⟩ : syracuseStep 4850999 = 7276499) B7276499
theorem B3233999 : Blo 2155435 3233999 := bstep (se 1 (by rfl) ⟨2425499, by rfl⟩ : syracuseStep 3233999 = 4850999) B4850999
theorem B2155999 : Blo 2155435 2155999 := bstep (se 1 (by rfl) ⟨1616999, by rfl⟩ : syracuseStep 2155999 = 3233999) B3233999
theorem B3234005 : Blo 2155435 3234005 := bbase (se 7 (by rfl) ⟨37898, by rfl⟩ : syracuseStep 3234005 = 75797) (by norm_num)
theorem B2156003 : Blo 2155435 2156003 := bstep (se 1 (by rfl) ⟨1617002, by rfl⟩ : syracuseStep 2156003 = 3234005) B3234005
theorem B3453509 : Blo 2155435 3453509 := bbase (se 4 (by rfl) ⟨323766, by rfl⟩ : syracuseStep 3453509 = 647533) (by norm_num)
theorem B2302339 : Blo 2155435 2302339 := bstep (se 1 (by rfl) ⟨1726754, by rfl⟩ : syracuseStep 2302339 = 3453509) B3453509
theorem B3069785 : Blo 2155435 3069785 := bstep (se 2 (by rfl) ⟨1151169, by rfl⟩ : syracuseStep 3069785 = 2302339) B2302339
theorem B8186093 : Blo 2155435 8186093 := bstep (se 3 (by rfl) ⟨1534892, by rfl⟩ : syracuseStep 8186093 = 3069785) B3069785
theorem B5457395 : Blo 2155435 5457395 := bstep (se 1 (by rfl) ⟨4093046, by rfl⟩ : syracuseStep 5457395 = 8186093) B8186093
theorem B3638263 : Blo 2155435 3638263 := bstep (se 1 (by rfl) ⟨2728697, by rfl⟩ : syracuseStep 3638263 = 5457395) B5457395
theorem B4851017 : Blo 2155435 4851017 := bstep (se 2 (by rfl) ⟨1819131, by rfl⟩ : syracuseStep 4851017 = 3638263) B3638263
theorem B3234011 : Blo 2155435 3234011 := bstep (se 1 (by rfl) ⟨2425508, by rfl⟩ : syracuseStep 3234011 = 4851017) B4851017
theorem B2156007 : Blo 2155435 2156007 := bstep (se 1 (by rfl) ⟨1617005, by rfl⟩ : syracuseStep 2156007 = 3234011) B3234011
theorem B2425513 : Blo 2155435 2425513 := bbase (se 2 (by rfl) ⟨909567, by rfl⟩ : syracuseStep 2425513 = 1819135) (by norm_num)
theorem B3234017 : Blo 2155435 3234017 := bstep (se 2 (by rfl) ⟨1212756, by rfl⟩ : syracuseStep 3234017 = 2425513) B2425513
theorem B2156011 : Blo 2155435 2156011 := bstep (se 1 (by rfl) ⟨1617008, by rfl⟩ : syracuseStep 2156011 = 3234017) B3234017
theorem B2590141 : Blo 2155435 2590141 := bbase (se 3 (by rfl) ⟨485651, by rfl⟩ : syracuseStep 2590141 = 971303) (by norm_num)
theorem B3453521 : Blo 2155435 3453521 := bstep (se 2 (by rfl) ⟨1295070, by rfl⟩ : syracuseStep 3453521 = 2590141) B2590141
theorem B9209389 : Blo 2155435 9209389 := bstep (se 3 (by rfl) ⟨1726760, by rfl⟩ : syracuseStep 9209389 = 3453521) B3453521
theorem B12279185 : Blo 2155435 12279185 := bstep (se 2 (by rfl) ⟨4604694, by rfl⟩ : syracuseStep 12279185 = 9209389) B9209389
theorem B8186123 : Blo 2155435 8186123 := bstep (se 1 (by rfl) ⟨6139592, by rfl⟩ : syracuseStep 8186123 = 12279185) B12279185
theorem B5457415 : Blo 2155435 5457415 := bstep (se 1 (by rfl) ⟨4093061, by rfl⟩ : syracuseStep 5457415 = 8186123) B8186123
theorem B7276553 : Blo 2155435 7276553 := bstep (se 2 (by rfl) ⟨2728707, by rfl⟩ : syracuseStep 7276553 = 5457415) B5457415
theorem B4851035 : Blo 2155435 4851035 := bstep (se 1 (by rfl) ⟨3638276, by rfl⟩ : syracuseStep 4851035 = 7276553) B7276553
theorem B3234023 : Blo 2155435 3234023 := bstep (se 1 (by rfl) ⟨2425517, by rfl⟩ : syracuseStep 3234023 = 4851035) B4851035
theorem B2156015 : Blo 2155435 2156015 := bstep (se 1 (by rfl) ⟨1617011, by rfl⟩ : syracuseStep 2156015 = 3234023) B3234023
theorem B3234029 : Blo 2155435 3234029 := bbase (se 3 (by rfl) ⟨606380, by rfl⟩ : syracuseStep 3234029 = 1212761) (by norm_num)
theorem B2156019 : Blo 2155435 2156019 := bstep (se 1 (by rfl) ⟨1617014, by rfl⟩ : syracuseStep 2156019 = 3234029) B3234029
theorem B4851053 : Blo 2155435 4851053 := bbase (se 3 (by rfl) ⟨909572, by rfl⟩ : syracuseStep 4851053 = 1819145) (by norm_num)
theorem B3234035 : Blo 2155435 3234035 := bstep (se 1 (by rfl) ⟨2425526, by rfl⟩ : syracuseStep 3234035 = 4851053) B4851053
theorem B2156023 : Blo 2155435 2156023 := bstep (se 1 (by rfl) ⟨1617017, by rfl⟩ : syracuseStep 2156023 = 3234035) B3234035
theorem B4093085 : Blo 2155435 4093085 := bbase (se 3 (by rfl) ⟨767453, by rfl⟩ : syracuseStep 4093085 = 1534907) (by norm_num)
theorem B2728723 : Blo 2155435 2728723 := bstep (se 1 (by rfl) ⟨2046542, by rfl⟩ : syracuseStep 2728723 = 4093085) B4093085
theorem B3638297 : Blo 2155435 3638297 := bstep (se 2 (by rfl) ⟨1364361, by rfl⟩ : syracuseStep 3638297 = 2728723) B2728723
theorem B2425531 : Blo 2155435 2425531 := bstep (se 1 (by rfl) ⟨1819148, by rfl⟩ : syracuseStep 2425531 = 3638297) B3638297
theorem B3234041 : Blo 2155435 3234041 := bstep (se 2 (by rfl) ⟨1212765, by rfl⟩ : syracuseStep 3234041 = 2425531) B2425531
theorem B2156027 : Blo 2155435 2156027 := bstep (se 1 (by rfl) ⟨1617020, by rfl⟩ : syracuseStep 2156027 = 3234041) B3234041
theorem B2765957 : Blo 2155435 2765957 := bbase (se 4 (by rfl) ⟨259308, by rfl⟩ : syracuseStep 2765957 = 518617) (by norm_num)
theorem B29503541 : Blo 2155435 29503541 := bstep (se 5 (by rfl) ⟨1382978, by rfl⟩ : syracuseStep 29503541 = 2765957) B2765957
theorem B78676109 : Blo 2155435 78676109 := bstep (se 3 (by rfl) ⟨14751770, by rfl⟩ : syracuseStep 78676109 = 29503541) B29503541
theorem B52450739 : Blo 2155435 52450739 := bstep (se 1 (by rfl) ⟨39338054, by rfl⟩ : syracuseStep 52450739 = 78676109) B78676109
theorem B34967159 : Blo 2155435 34967159 := bstep (se 1 (by rfl) ⟨26225369, by rfl⟩ : syracuseStep 34967159 = 52450739) B52450739
theorem B23311439 : Blo 2155435 23311439 := bstep (se 1 (by rfl) ⟨17483579, by rfl⟩ : syracuseStep 23311439 = 34967159) B34967159
theorem B15540959 : Blo 2155435 15540959 := bstep (se 1 (by rfl) ⟨11655719, by rfl⟩ : syracuseStep 15540959 = 23311439) B23311439
theorem B10360639 : Blo 2155435 10360639 := bstep (se 1 (by rfl) ⟨7770479, by rfl⟩ : syracuseStep 10360639 = 15540959) B15540959
theorem B55256741 : Blo 2155435 55256741 := bstep (se 4 (by rfl) ⟨5180319, by rfl⟩ : syracuseStep 55256741 = 10360639) B10360639
theorem B36837827 : Blo 2155435 36837827 := bstep (se 1 (by rfl) ⟨27628370, by rfl⟩ : syracuseStep 36837827 = 55256741) B55256741
theorem B24558551 : Blo 2155435 24558551 := bstep (se 1 (by rfl) ⟨18418913, by rfl⟩ : syracuseStep 24558551 = 36837827) B36837827
theorem B16372367 : Blo 2155435 16372367 := bstep (se 1 (by rfl) ⟨12279275, by rfl⟩ : syracuseStep 16372367 = 24558551) B24558551
theorem B10914911 : Blo 2155435 10914911 := bstep (se 1 (by rfl) ⟨8186183, by rfl⟩ : syracuseStep 10914911 = 16372367) B16372367
theorem B7276607 : Blo 2155435 7276607 := bstep (se 1 (by rfl) ⟨5457455, by rfl⟩ : syracuseStep 7276607 = 10914911) B10914911
theorem B4851071 : Blo 2155435 4851071 := bstep (se 1 (by rfl) ⟨3638303, by rfl⟩ : syracuseStep 4851071 = 7276607) B7276607
theorem B3234047 : Blo 2155435 3234047 := bstep (se 1 (by rfl) ⟨2425535, by rfl⟩ : syracuseStep 3234047 = 4851071) B4851071
theorem B2156031 : Blo 2155435 2156031 := bstep (se 1 (by rfl) ⟨1617023, by rfl⟩ : syracuseStep 2156031 = 3234047) B3234047
theorem B3234053 : Blo 2155435 3234053 := bbase (se 4 (by rfl) ⟨303192, by rfl⟩ : syracuseStep 3234053 = 606385) (by norm_num)
theorem B2156035 : Blo 2155435 2156035 := bstep (se 1 (by rfl) ⟨1617026, by rfl⟩ : syracuseStep 2156035 = 3234053) B3234053
theorem B3638317 : Blo 2155435 3638317 := bbase (se 3 (by rfl) ⟨682184, by rfl⟩ : syracuseStep 3638317 = 1364369) (by norm_num)
theorem B4851089 : Blo 2155435 4851089 := bstep (se 2 (by rfl) ⟨1819158, by rfl⟩ : syracuseStep 4851089 = 3638317) B3638317
theorem B3234059 : Blo 2155435 3234059 := bstep (se 1 (by rfl) ⟨2425544, by rfl⟩ : syracuseStep 3234059 = 4851089) B4851089
theorem B2156039 : Blo 2155435 2156039 := bstep (se 1 (by rfl) ⟨1617029, by rfl⟩ : syracuseStep 2156039 = 3234059) B3234059
theorem B2425549 : Blo 2155435 2425549 := bbase (se 3 (by rfl) ⟨454790, by rfl⟩ : syracuseStep 2425549 = 909581) (by norm_num)
theorem B3234065 : Blo 2155435 3234065 := bstep (se 2 (by rfl) ⟨1212774, by rfl⟩ : syracuseStep 3234065 = 2425549) B2425549
theorem B2156043 : Blo 2155435 2156043 := bstep (se 1 (by rfl) ⟨1617032, by rfl⟩ : syracuseStep 2156043 = 3234065) B3234065
theorem B7276661 : Blo 2155435 7276661 := bbase (se 5 (by rfl) ⟨341093, by rfl⟩ : syracuseStep 7276661 = 682187) (by norm_num)
theorem B4851107 : Blo 2155435 4851107 := bstep (se 1 (by rfl) ⟨3638330, by rfl⟩ : syracuseStep 4851107 = 7276661) B7276661
theorem B3234071 : Blo 2155435 3234071 := bstep (se 1 (by rfl) ⟨2425553, by rfl⟩ : syracuseStep 3234071 = 4851107) B4851107
theorem B2156047 : Blo 2155435 2156047 := bstep (se 1 (by rfl) ⟨1617035, by rfl⟩ : syracuseStep 2156047 = 3234071) B3234071
theorem B3234077 : Blo 2155435 3234077 := bbase (se 3 (by rfl) ⟨606389, by rfl⟩ : syracuseStep 3234077 = 1212779) (by norm_num)
theorem B2156051 : Blo 2155435 2156051 := bstep (se 1 (by rfl) ⟨1617038, by rfl⟩ : syracuseStep 2156051 = 3234077) B3234077
theorem B4851125 : Blo 2155435 4851125 := bbase (se 5 (by rfl) ⟨227396, by rfl⟩ : syracuseStep 4851125 = 454793) (by norm_num)
theorem B3234083 : Blo 2155435 3234083 := bstep (se 1 (by rfl) ⟨2425562, by rfl⟩ : syracuseStep 3234083 = 4851125) B4851125
theorem B2156055 : Blo 2155435 2156055 := bstep (se 1 (by rfl) ⟨1617041, by rfl⟩ : syracuseStep 2156055 = 3234083) B3234083
theorem B4604789 : Blo 2155435 4604789 := bbase (se 5 (by rfl) ⟨215849, by rfl⟩ : syracuseStep 4604789 = 431699) (by norm_num)
theorem B12279437 : Blo 2155435 12279437 := bstep (se 3 (by rfl) ⟨2302394, by rfl⟩ : syracuseStep 12279437 = 4604789) B4604789
theorem B8186291 : Blo 2155435 8186291 := bstep (se 1 (by rfl) ⟨6139718, by rfl⟩ : syracuseStep 8186291 = 12279437) B12279437
theorem B5457527 : Blo 2155435 5457527 := bstep (se 1 (by rfl) ⟨4093145, by rfl⟩ : syracuseStep 5457527 = 8186291) B8186291
theorem B3638351 : Blo 2155435 3638351 := bstep (se 1 (by rfl) ⟨2728763, by rfl⟩ : syracuseStep 3638351 = 5457527) B5457527
theorem B2425567 : Blo 2155435 2425567 := bstep (se 1 (by rfl) ⟨1819175, by rfl⟩ : syracuseStep 2425567 = 3638351) B3638351
theorem B3234089 : Blo 2155435 3234089 := bstep (se 2 (by rfl) ⟨1212783, by rfl⟩ : syracuseStep 3234089 = 2425567) B2425567
theorem B2156059 : Blo 2155435 2156059 := bstep (se 1 (by rfl) ⟨1617044, by rfl⟩ : syracuseStep 2156059 = 3234089) B3234089
theorem B4604797 : Blo 2155435 4604797 := bbase (se 3 (by rfl) ⟨863399, by rfl⟩ : syracuseStep 4604797 = 1726799) (by norm_num)
theorem B6139729 : Blo 2155435 6139729 := bstep (se 2 (by rfl) ⟨2302398, by rfl⟩ : syracuseStep 6139729 = 4604797) B4604797
theorem B8186305 : Blo 2155435 8186305 := bstep (se 2 (by rfl) ⟨3069864, by rfl⟩ : syracuseStep 8186305 = 6139729) B6139729
theorem B10915073 : Blo 2155435 10915073 := bstep (se 2 (by rfl) ⟨4093152, by rfl⟩ : syracuseStep 10915073 = 8186305) B8186305
theorem B7276715 : Blo 2155435 7276715 := bstep (se 1 (by rfl) ⟨5457536, by rfl⟩ : syracuseStep 7276715 = 10915073) B10915073
theorem B4851143 : Blo 2155435 4851143 := bstep (se 1 (by rfl) ⟨3638357, by rfl⟩ : syracuseStep 4851143 = 7276715) B7276715
theorem B3234095 : Blo 2155435 3234095 := bstep (se 1 (by rfl) ⟨2425571, by rfl⟩ : syracuseStep 3234095 = 4851143) B4851143
theorem B2156063 : Blo 2155435 2156063 := bstep (se 1 (by rfl) ⟨1617047, by rfl⟩ : syracuseStep 2156063 = 3234095) B3234095
theorem B3234101 : Blo 2155435 3234101 := bbase (se 5 (by rfl) ⟨151598, by rfl⟩ : syracuseStep 3234101 = 303197) (by norm_num)
theorem B2156067 : Blo 2155435 2156067 := bstep (se 1 (by rfl) ⟨1617050, by rfl⟩ : syracuseStep 2156067 = 3234101) B3234101
theorem B5457557 : Blo 2155435 5457557 := bbase (se 6 (by rfl) ⟨127911, by rfl⟩ : syracuseStep 5457557 = 255823) (by norm_num)
theorem B3638371 : Blo 2155435 3638371 := bstep (se 1 (by rfl) ⟨2728778, by rfl⟩ : syracuseStep 3638371 = 5457557) B5457557
theorem B4851161 : Blo 2155435 4851161 := bstep (se 2 (by rfl) ⟨1819185, by rfl⟩ : syracuseStep 4851161 = 3638371) B3638371
theorem B3234107 : Blo 2155435 3234107 := bstep (se 1 (by rfl) ⟨2425580, by rfl⟩ : syracuseStep 3234107 = 4851161) B4851161
theorem B2156071 : Blo 2155435 2156071 := bstep (se 1 (by rfl) ⟨1617053, by rfl⟩ : syracuseStep 2156071 = 3234107) B3234107
theorem B2425585 : Blo 2155435 2425585 := bbase (se 2 (by rfl) ⟨909594, by rfl⟩ : syracuseStep 2425585 = 1819189) (by norm_num)
theorem B3234113 : Blo 2155435 3234113 := bstep (se 2 (by rfl) ⟨1212792, by rfl⟩ : syracuseStep 3234113 = 2425585) B2425585
theorem B2156075 : Blo 2155435 2156075 := bstep (se 1 (by rfl) ⟨1617056, by rfl⟩ : syracuseStep 2156075 = 3234113) B3234113
theorem B4149029 : Blo 2155435 4149029 := bbase (se 4 (by rfl) ⟨388971, by rfl⟩ : syracuseStep 4149029 = 777943) (by norm_num)
theorem B11064077 : Blo 2155435 11064077 := bstep (se 3 (by rfl) ⟨2074514, by rfl⟩ : syracuseStep 11064077 = 4149029) B4149029
theorem B7376051 : Blo 2155435 7376051 := bstep (se 1 (by rfl) ⟨5532038, by rfl⟩ : syracuseStep 7376051 = 11064077) B11064077
theorem B4917367 : Blo 2155435 4917367 := bstep (se 1 (by rfl) ⟨3688025, by rfl⟩ : syracuseStep 4917367 = 7376051) B7376051
theorem B26225957 : Blo 2155435 26225957 := bstep (se 4 (by rfl) ⟨2458683, by rfl⟩ : syracuseStep 26225957 = 4917367) B4917367
theorem B69935885 : Blo 2155435 69935885 := bstep (se 3 (by rfl) ⟨13112978, by rfl⟩ : syracuseStep 69935885 = 26225957) B26225957
theorem B46623923 : Blo 2155435 46623923 := bstep (se 1 (by rfl) ⟨34967942, by rfl⟩ : syracuseStep 46623923 = 69935885) B69935885
theorem B31082615 : Blo 2155435 31082615 := bstep (se 1 (by rfl) ⟨23311961, by rfl⟩ : syracuseStep 31082615 = 46623923) B46623923
theorem B20721743 : Blo 2155435 20721743 := bstep (se 1 (by rfl) ⟨15541307, by rfl⟩ : syracuseStep 20721743 = 31082615) B31082615
theorem B13814495 : Blo 2155435 13814495 := bstep (se 1 (by rfl) ⟨10360871, by rfl⟩ : syracuseStep 13814495 = 20721743) B20721743
theorem B9209663 : Blo 2155435 9209663 := bstep (se 1 (by rfl) ⟨6907247, by rfl⟩ : syracuseStep 9209663 = 13814495) B13814495
theorem B6139775 : Blo 2155435 6139775 := bstep (se 1 (by rfl) ⟨4604831, by rfl⟩ : syracuseStep 6139775 = 9209663) B9209663
theorem B4093183 : Blo 2155435 4093183 := bstep (se 1 (by rfl) ⟨3069887, by rfl⟩ : syracuseStep 4093183 = 6139775) B6139775
theorem B5457577 : Blo 2155435 5457577 := bstep (se 2 (by rfl) ⟨2046591, by rfl⟩ : syracuseStep 5457577 = 4093183) B4093183
theorem B7276769 : Blo 2155435 7276769 := bstep (se 2 (by rfl) ⟨2728788, by rfl⟩ : syracuseStep 7276769 = 5457577) B5457577
theorem B4851179 : Blo 2155435 4851179 := bstep (se 1 (by rfl) ⟨3638384, by rfl⟩ : syracuseStep 4851179 = 7276769) B7276769
theorem B3234119 : Blo 2155435 3234119 := bstep (se 1 (by rfl) ⟨2425589, by rfl⟩ : syracuseStep 3234119 = 4851179) B4851179
theorem B2156079 : Blo 2155435 2156079 := bstep (se 1 (by rfl) ⟨1617059, by rfl⟩ : syracuseStep 2156079 = 3234119) B3234119
theorem B3234125 : Blo 2155435 3234125 := bbase (se 3 (by rfl) ⟨606398, by rfl⟩ : syracuseStep 3234125 = 1212797) (by norm_num)
theorem B2156083 : Blo 2155435 2156083 := bstep (se 1 (by rfl) ⟨1617062, by rfl⟩ : syracuseStep 2156083 = 3234125) B3234125
theorem B4851197 : Blo 2155435 4851197 := bbase (se 3 (by rfl) ⟨909599, by rfl⟩ : syracuseStep 4851197 = 1819199) (by norm_num)
theorem B3234131 : Blo 2155435 3234131 := bstep (se 1 (by rfl) ⟨2425598, by rfl⟩ : syracuseStep 3234131 = 4851197) B4851197
theorem B2156087 : Blo 2155435 2156087 := bstep (se 1 (by rfl) ⟨1617065, by rfl⟩ : syracuseStep 2156087 = 3234131) B3234131
theorem B3638405 : Blo 2155435 3638405 := bbase (se 4 (by rfl) ⟨341100, by rfl⟩ : syracuseStep 3638405 = 682201) (by norm_num)
theorem B2425603 : Blo 2155435 2425603 := bstep (se 1 (by rfl) ⟨1819202, by rfl⟩ : syracuseStep 2425603 = 3638405) B3638405
theorem B3234137 : Blo 2155435 3234137 := bstep (se 2 (by rfl) ⟨1212801, by rfl⟩ : syracuseStep 3234137 = 2425603) B2425603
theorem B2156091 : Blo 2155435 2156091 := bstep (se 1 (by rfl) ⟨1617068, by rfl⟩ : syracuseStep 2156091 = 3234137) B3234137
theorem B16372853 : Blo 2155435 16372853 := bbase (se 5 (by rfl) ⟨767477, by rfl⟩ : syracuseStep 16372853 = 1534955) (by norm_num)
theorem B10915235 : Blo 2155435 10915235 := bstep (se 1 (by rfl) ⟨8186426, by rfl⟩ : syracuseStep 10915235 = 16372853) B16372853
theorem B7276823 : Blo 2155435 7276823 := bstep (se 1 (by rfl) ⟨5457617, by rfl⟩ : syracuseStep 7276823 = 10915235) B10915235
theorem B4851215 : Blo 2155435 4851215 := bstep (se 1 (by rfl) ⟨3638411, by rfl⟩ : syracuseStep 4851215 = 7276823) B7276823
theorem B3234143 : Blo 2155435 3234143 := bstep (se 1 (by rfl) ⟨2425607, by rfl⟩ : syracuseStep 3234143 = 4851215) B4851215
theorem B2156095 : Blo 2155435 2156095 := bstep (se 1 (by rfl) ⟨1617071, by rfl⟩ : syracuseStep 2156095 = 3234143) B3234143
theorem B3234149 : Blo 2155435 3234149 := bbase (se 4 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 3234149 = 606403) (by norm_num)
theorem B2156099 : Blo 2155435 2156099 := bstep (se 1 (by rfl) ⟨1617074, by rfl⟩ : syracuseStep 2156099 = 3234149) B3234149
theorem B4093229 : Blo 2155435 4093229 := bbase (se 3 (by rfl) ⟨767480, by rfl⟩ : syracuseStep 4093229 = 1534961) (by norm_num)
theorem B2728819 : Blo 2155435 2728819 := bstep (se 1 (by rfl) ⟨2046614, by rfl⟩ : syracuseStep 2728819 = 4093229) B4093229
theorem B3638425 : Blo 2155435 3638425 := bstep (se 2 (by rfl) ⟨1364409, by rfl⟩ : syracuseStep 3638425 = 2728819) B2728819
theorem B4851233 : Blo 2155435 4851233 := bstep (se 2 (by rfl) ⟨1819212, by rfl⟩ : syracuseStep 4851233 = 3638425) B3638425
theorem B3234155 : Blo 2155435 3234155 := bstep (se 1 (by rfl) ⟨2425616, by rfl⟩ : syracuseStep 3234155 = 4851233) B4851233
theorem B2156103 : Blo 2155435 2156103 := bstep (se 1 (by rfl) ⟨1617077, by rfl⟩ : syracuseStep 2156103 = 3234155) B3234155
theorem B2425621 : Blo 2155435 2425621 := bbase (se 6 (by rfl) ⟨56850, by rfl⟩ : syracuseStep 2425621 = 113701) (by norm_num)
theorem B3234161 : Blo 2155435 3234161 := bstep (se 2 (by rfl) ⟨1212810, by rfl⟩ : syracuseStep 3234161 = 2425621) B2425621
theorem B2156107 : Blo 2155435 2156107 := bstep (se 1 (by rfl) ⟨1617080, by rfl⟩ : syracuseStep 2156107 = 3234161) B3234161
theorem B2728829 : Blo 2155435 2728829 := bbase (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) (by norm_num)
theorem B7276877 : Blo 2155435 7276877 := bstep (se 3 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 7276877 = 2728829) B2728829
theorem B4851251 : Blo 2155435 4851251 := bstep (se 1 (by rfl) ⟨3638438, by rfl⟩ : syracuseStep 4851251 = 7276877) B7276877
theorem B3234167 : Blo 2155435 3234167 := bstep (se 1 (by rfl) ⟨2425625, by rfl⟩ : syracuseStep 3234167 = 4851251) B4851251
theorem B2156111 : Blo 2155435 2156111 := bstep (se 1 (by rfl) ⟨1617083, by rfl⟩ : syracuseStep 2156111 = 3234167) B3234167
theorem B3234173 : Blo 2155435 3234173 := bbase (se 3 (by rfl) ⟨606407, by rfl⟩ : syracuseStep 3234173 = 1212815) (by norm_num)
theorem B2156115 : Blo 2155435 2156115 := bstep (se 1 (by rfl) ⟨1617086, by rfl⟩ : syracuseStep 2156115 = 3234173) B3234173
theorem B4851269 : Blo 2155435 4851269 := bbase (se 4 (by rfl) ⟨454806, by rfl⟩ : syracuseStep 4851269 = 909613) (by norm_num)
theorem B3234179 : Blo 2155435 3234179 := bstep (se 1 (by rfl) ⟨2425634, by rfl⟩ : syracuseStep 3234179 = 4851269) B4851269
theorem B2156119 : Blo 2155435 2156119 := bstep (se 1 (by rfl) ⟨1617089, by rfl⟩ : syracuseStep 2156119 = 3234179) B3234179
theorem B5395493 : Blo 2155435 5395493 := bbase (se 4 (by rfl) ⟨505827, by rfl⟩ : syracuseStep 5395493 = 1011655) (by norm_num)
theorem B3596995 : Blo 2155435 3596995 := bstep (se 1 (by rfl) ⟨2697746, by rfl⟩ : syracuseStep 3596995 = 5395493) B5395493
theorem B4795993 : Blo 2155435 4795993 := bstep (se 2 (by rfl) ⟨1798497, by rfl⟩ : syracuseStep 4795993 = 3596995) B3596995
theorem B25578629 : Blo 2155435 25578629 := bstep (se 4 (by rfl) ⟨2397996, by rfl⟩ : syracuseStep 25578629 = 4795993) B4795993
theorem B17052419 : Blo 2155435 17052419 := bstep (se 1 (by rfl) ⟨12789314, by rfl⟩ : syracuseStep 17052419 = 25578629) B25578629
theorem B11368279 : Blo 2155435 11368279 := bstep (se 1 (by rfl) ⟨8526209, by rfl⟩ : syracuseStep 11368279 = 17052419) B17052419
theorem B15157705 : Blo 2155435 15157705 := bstep (se 2 (by rfl) ⟨5684139, by rfl⟩ : syracuseStep 15157705 = 11368279) B11368279
theorem B20210273 : Blo 2155435 20210273 := bstep (se 2 (by rfl) ⟨7578852, by rfl⟩ : syracuseStep 20210273 = 15157705) B15157705
theorem B13473515 : Blo 2155435 13473515 := bstep (se 1 (by rfl) ⟨10105136, by rfl⟩ : syracuseStep 13473515 = 20210273) B20210273
theorem B8982343 : Blo 2155435 8982343 := bstep (se 1 (by rfl) ⟨6736757, by rfl⟩ : syracuseStep 8982343 = 13473515) B13473515
theorem B11976457 : Blo 2155435 11976457 := bstep (se 2 (by rfl) ⟨4491171, by rfl⟩ : syracuseStep 11976457 = 8982343) B8982343
theorem B15968609 : Blo 2155435 15968609 := bstep (se 2 (by rfl) ⟨5988228, by rfl⟩ : syracuseStep 15968609 = 11976457) B11976457
theorem B10645739 : Blo 2155435 10645739 := bstep (se 1 (by rfl) ⟨7984304, by rfl⟩ : syracuseStep 10645739 = 15968609) B15968609
theorem B7097159 : Blo 2155435 7097159 := bstep (se 1 (by rfl) ⟨5322869, by rfl⟩ : syracuseStep 7097159 = 10645739) B10645739
theorem B4731439 : Blo 2155435 4731439 := bstep (se 1 (by rfl) ⟨3548579, by rfl⟩ : syracuseStep 4731439 = 7097159) B7097159
theorem B6308585 : Blo 2155435 6308585 := bstep (se 2 (by rfl) ⟨2365719, by rfl⟩ : syracuseStep 6308585 = 4731439) B4731439
theorem B4205723 : Blo 2155435 4205723 := bstep (se 1 (by rfl) ⟨3154292, by rfl⟩ : syracuseStep 4205723 = 6308585) B6308585
theorem B11215261 : Blo 2155435 11215261 := bstep (se 3 (by rfl) ⟨2102861, by rfl⟩ : syracuseStep 11215261 = 4205723) B4205723
theorem B14953681 : Blo 2155435 14953681 := bstep (se 2 (by rfl) ⟨5607630, by rfl⟩ : syracuseStep 14953681 = 11215261) B11215261
theorem B19938241 : Blo 2155435 19938241 := bstep (se 2 (by rfl) ⟨7476840, by rfl⟩ : syracuseStep 19938241 = 14953681) B14953681
theorem B106337285 : Blo 2155435 106337285 := bstep (se 4 (by rfl) ⟨9969120, by rfl⟩ : syracuseStep 106337285 = 19938241) B19938241
theorem B70891523 : Blo 2155435 70891523 := bstep (se 1 (by rfl) ⟨53168642, by rfl⟩ : syracuseStep 70891523 = 106337285) B106337285
theorem B47261015 : Blo 2155435 47261015 := bstep (se 1 (by rfl) ⟨35445761, by rfl⟩ : syracuseStep 47261015 = 70891523) B70891523
theorem B31507343 : Blo 2155435 31507343 := bstep (se 1 (by rfl) ⟨23630507, by rfl⟩ : syracuseStep 31507343 = 47261015) B47261015
theorem B21004895 : Blo 2155435 21004895 := bstep (se 1 (by rfl) ⟨15753671, by rfl⟩ : syracuseStep 21004895 = 31507343) B31507343
theorem B14003263 : Blo 2155435 14003263 := bstep (se 1 (by rfl) ⟨10502447, by rfl⟩ : syracuseStep 14003263 = 21004895) B21004895
theorem B74684069 : Blo 2155435 74684069 := bstep (se 4 (by rfl) ⟨7001631, by rfl⟩ : syracuseStep 74684069 = 14003263) B14003263
theorem B49789379 : Blo 2155435 49789379 := bstep (se 1 (by rfl) ⟨37342034, by rfl⟩ : syracuseStep 49789379 = 74684069) B74684069
theorem B33192919 : Blo 2155435 33192919 := bstep (se 1 (by rfl) ⟨24894689, by rfl⟩ : syracuseStep 33192919 = 49789379) B49789379
theorem B44257225 : Blo 2155435 44257225 := bstep (se 2 (by rfl) ⟨16596459, by rfl⟩ : syracuseStep 44257225 = 33192919) B33192919
theorem B59009633 : Blo 2155435 59009633 := bstep (se 2 (by rfl) ⟨22128612, by rfl⟩ : syracuseStep 59009633 = 44257225) B44257225
theorem B39339755 : Blo 2155435 39339755 := bstep (se 1 (by rfl) ⟨29504816, by rfl⟩ : syracuseStep 39339755 = 59009633) B59009633
theorem B26226503 : Blo 2155435 26226503 := bstep (se 1 (by rfl) ⟨19669877, by rfl⟩ : syracuseStep 26226503 = 39339755) B39339755
theorem B17484335 : Blo 2155435 17484335 := bstep (se 1 (by rfl) ⟨13113251, by rfl⟩ : syracuseStep 17484335 = 26226503) B26226503
theorem B11656223 : Blo 2155435 11656223 := bstep (se 1 (by rfl) ⟨8742167, by rfl⟩ : syracuseStep 11656223 = 17484335) B17484335
theorem B7770815 : Blo 2155435 7770815 := bstep (se 1 (by rfl) ⟨5828111, by rfl⟩ : syracuseStep 7770815 = 11656223) B11656223
theorem B5180543 : Blo 2155435 5180543 := bstep (se 1 (by rfl) ⟨3885407, by rfl⟩ : syracuseStep 5180543 = 7770815) B7770815
theorem B3453695 : Blo 2155435 3453695 := bstep (se 1 (by rfl) ⟨2590271, by rfl⟩ : syracuseStep 3453695 = 5180543) B5180543
theorem B2302463 : Blo 2155435 2302463 := bstep (se 1 (by rfl) ⟨1726847, by rfl⟩ : syracuseStep 2302463 = 3453695) B3453695
theorem B6139901 : Blo 2155435 6139901 := bstep (se 3 (by rfl) ⟨1151231, by rfl⟩ : syracuseStep 6139901 = 2302463) B2302463
theorem B4093267 : Blo 2155435 4093267 := bstep (se 1 (by rfl) ⟨3069950, by rfl⟩ : syracuseStep 4093267 = 6139901) B6139901
theorem B5457689 : Blo 2155435 5457689 := bstep (se 2 (by rfl) ⟨2046633, by rfl⟩ : syracuseStep 5457689 = 4093267) B4093267
theorem B3638459 : Blo 2155435 3638459 := bstep (se 1 (by rfl) ⟨2728844, by rfl⟩ : syracuseStep 3638459 = 5457689) B5457689
theorem B2425639 : Blo 2155435 2425639 := bstep (se 1 (by rfl) ⟨1819229, by rfl⟩ : syracuseStep 2425639 = 3638459) B3638459
theorem B3234185 : Blo 2155435 3234185 := bstep (se 2 (by rfl) ⟨1212819, by rfl⟩ : syracuseStep 3234185 = 2425639) B2425639
theorem B2156123 : Blo 2155435 2156123 := bstep (se 1 (by rfl) ⟨1617092, by rfl⟩ : syracuseStep 2156123 = 3234185) B3234185
theorem B10915397 : Blo 2155435 10915397 := bbase (se 4 (by rfl) ⟨1023318, by rfl⟩ : syracuseStep 10915397 = 2046637) (by norm_num)
theorem B7276931 : Blo 2155435 7276931 := bstep (se 1 (by rfl) ⟨5457698, by rfl⟩ : syracuseStep 7276931 = 10915397) B10915397
theorem B4851287 : Blo 2155435 4851287 := bstep (se 1 (by rfl) ⟨3638465, by rfl⟩ : syracuseStep 4851287 = 7276931) B7276931
theorem B3234191 : Blo 2155435 3234191 := bstep (se 1 (by rfl) ⟨2425643, by rfl⟩ : syracuseStep 3234191 = 4851287) B4851287
theorem B2156127 : Blo 2155435 2156127 := bstep (se 1 (by rfl) ⟨1617095, by rfl⟩ : syracuseStep 2156127 = 3234191) B3234191
theorem B3234197 : Blo 2155435 3234197 := bbase (se 6 (by rfl) ⟨75801, by rfl⟩ : syracuseStep 3234197 = 151603) (by norm_num)
theorem B2156131 : Blo 2155435 2156131 := bstep (se 1 (by rfl) ⟨1617098, by rfl⟩ : syracuseStep 2156131 = 3234197) B3234197
theorem B10361141 : Blo 2155435 10361141 := bbase (se 5 (by rfl) ⟨485678, by rfl⟩ : syracuseStep 10361141 = 971357) (by norm_num)
theorem B6907427 : Blo 2155435 6907427 := bstep (se 1 (by rfl) ⟨5180570, by rfl⟩ : syracuseStep 6907427 = 10361141) B10361141
theorem B4604951 : Blo 2155435 4604951 := bstep (se 1 (by rfl) ⟨3453713, by rfl⟩ : syracuseStep 4604951 = 6907427) B6907427
theorem B12279869 : Blo 2155435 12279869 := bstep (se 3 (by rfl) ⟨2302475, by rfl⟩ : syracuseStep 12279869 = 4604951) B4604951
theorem B8186579 : Blo 2155435 8186579 := bstep (se 1 (by rfl) ⟨6139934, by rfl⟩ : syracuseStep 8186579 = 12279869) B12279869
theorem B5457719 : Blo 2155435 5457719 := bstep (se 1 (by rfl) ⟨4093289, by rfl⟩ : syracuseStep 5457719 = 8186579) B8186579
theorem B3638479 : Blo 2155435 3638479 := bstep (se 1 (by rfl) ⟨2728859, by rfl⟩ : syracuseStep 3638479 = 5457719) B5457719
theorem B4851305 : Blo 2155435 4851305 := bstep (se 2 (by rfl) ⟨1819239, by rfl⟩ : syracuseStep 4851305 = 3638479) B3638479
theorem B3234203 : Blo 2155435 3234203 := bstep (se 1 (by rfl) ⟨2425652, by rfl⟩ : syracuseStep 3234203 = 4851305) B4851305
theorem B2156135 : Blo 2155435 2156135 := bstep (se 1 (by rfl) ⟨1617101, by rfl⟩ : syracuseStep 2156135 = 3234203) B3234203
theorem B2425657 : Blo 2155435 2425657 := bbase (se 2 (by rfl) ⟨909621, by rfl⟩ : syracuseStep 2425657 = 1819243) (by norm_num)
theorem B3234209 : Blo 2155435 3234209 := bstep (se 2 (by rfl) ⟨1212828, by rfl⟩ : syracuseStep 3234209 = 2425657) B2425657
theorem B2156139 : Blo 2155435 2156139 := bstep (se 1 (by rfl) ⟨1617104, by rfl⟩ : syracuseStep 2156139 = 3234209) B3234209
theorem B6139957 : Blo 2155435 6139957 := bbase (se 5 (by rfl) ⟨287810, by rfl⟩ : syracuseStep 6139957 = 575621) (by norm_num)
theorem B8186609 : Blo 2155435 8186609 := bstep (se 2 (by rfl) ⟨3069978, by rfl⟩ : syracuseStep 8186609 = 6139957) B6139957
theorem B5457739 : Blo 2155435 5457739 := bstep (se 1 (by rfl) ⟨4093304, by rfl⟩ : syracuseStep 5457739 = 8186609) B8186609
theorem B7276985 : Blo 2155435 7276985 := bstep (se 2 (by rfl) ⟨2728869, by rfl⟩ : syracuseStep 7276985 = 5457739) B5457739
theorem B4851323 : Blo 2155435 4851323 := bstep (se 1 (by rfl) ⟨3638492, by rfl⟩ : syracuseStep 4851323 = 7276985) B7276985
theorem B3234215 : Blo 2155435 3234215 := bstep (se 1 (by rfl) ⟨2425661, by rfl⟩ : syracuseStep 3234215 = 4851323) B4851323
theorem B2156143 : Blo 2155435 2156143 := bstep (se 1 (by rfl) ⟨1617107, by rfl⟩ : syracuseStep 2156143 = 3234215) B3234215
theorem B3234221 : Blo 2155435 3234221 := bbase (se 3 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 3234221 = 1212833) (by norm_num)
theorem B2156147 : Blo 2155435 2156147 := bstep (se 1 (by rfl) ⟨1617110, by rfl⟩ : syracuseStep 2156147 = 3234221) B3234221
theorem B4851341 : Blo 2155435 4851341 := bbase (se 3 (by rfl) ⟨909626, by rfl⟩ : syracuseStep 4851341 = 1819253) (by norm_num)
theorem B3234227 : Blo 2155435 3234227 := bstep (se 1 (by rfl) ⟨2425670, by rfl⟩ : syracuseStep 3234227 = 4851341) B4851341
theorem B2156151 : Blo 2155435 2156151 := bstep (se 1 (by rfl) ⟨1617113, by rfl⟩ : syracuseStep 2156151 = 3234227) B3234227
theorem B2728885 : Blo 2155435 2728885 := bbase (se 5 (by rfl) ⟨127916, by rfl⟩ : syracuseStep 2728885 = 255833) (by norm_num)
theorem B3638513 : Blo 2155435 3638513 := bstep (se 2 (by rfl) ⟨1364442, by rfl⟩ : syracuseStep 3638513 = 2728885) B2728885
theorem B2425675 : Blo 2155435 2425675 := bstep (se 1 (by rfl) ⟨1819256, by rfl⟩ : syracuseStep 2425675 = 3638513) B3638513
theorem B3234233 : Blo 2155435 3234233 := bstep (se 2 (by rfl) ⟨1212837, by rfl⟩ : syracuseStep 3234233 = 2425675) B2425675
theorem B2156155 : Blo 2155435 2156155 := bstep (se 1 (by rfl) ⟨1617116, by rfl⟩ : syracuseStep 2156155 = 3234233) B3234233
theorem B11064485 : Blo 2155435 11064485 := bbase (se 4 (by rfl) ⟨1037295, by rfl⟩ : syracuseStep 11064485 = 2074591) (by norm_num)
theorem B29505293 : Blo 2155435 29505293 := bstep (se 3 (by rfl) ⟨5532242, by rfl⟩ : syracuseStep 29505293 = 11064485) B11064485
theorem B19670195 : Blo 2155435 19670195 := bstep (se 1 (by rfl) ⟨14752646, by rfl⟩ : syracuseStep 19670195 = 29505293) B29505293
theorem B13113463 : Blo 2155435 13113463 := bstep (se 1 (by rfl) ⟨9835097, by rfl⟩ : syracuseStep 13113463 = 19670195) B19670195
theorem B17484617 : Blo 2155435 17484617 := bstep (se 2 (by rfl) ⟨6556731, by rfl⟩ : syracuseStep 17484617 = 13113463) B13113463
theorem B46625645 : Blo 2155435 46625645 := bstep (se 3 (by rfl) ⟨8742308, by rfl⟩ : syracuseStep 46625645 = 17484617) B17484617
theorem B31083763 : Blo 2155435 31083763 := bstep (se 1 (by rfl) ⟨23312822, by rfl⟩ : syracuseStep 31083763 = 46625645) B46625645
theorem B41445017 : Blo 2155435 41445017 := bstep (se 2 (by rfl) ⟨15541881, by rfl⟩ : syracuseStep 41445017 = 31083763) B31083763
theorem B27630011 : Blo 2155435 27630011 := bstep (se 1 (by rfl) ⟨20722508, by rfl⟩ : syracuseStep 27630011 = 41445017) B41445017
theorem B18420007 : Blo 2155435 18420007 := bstep (se 1 (by rfl) ⟨13815005, by rfl⟩ : syracuseStep 18420007 = 27630011) B27630011
theorem B24560009 : Blo 2155435 24560009 := bstep (se 2 (by rfl) ⟨9210003, by rfl⟩ : syracuseStep 24560009 = 18420007) B18420007
theorem B16373339 : Blo 2155435 16373339 := bstep (se 1 (by rfl) ⟨12280004, by rfl⟩ : syracuseStep 16373339 = 24560009) B24560009
theorem B10915559 : Blo 2155435 10915559 := bstep (se 1 (by rfl) ⟨8186669, by rfl⟩ : syracuseStep 10915559 = 16373339) B16373339
theorem B7277039 : Blo 2155435 7277039 := bstep (se 1 (by rfl) ⟨5457779, by rfl⟩ : syracuseStep 7277039 = 10915559) B10915559
theorem B4851359 : Blo 2155435 4851359 := bstep (se 1 (by rfl) ⟨3638519, by rfl⟩ : syracuseStep 4851359 = 7277039) B7277039
theorem B3234239 : Blo 2155435 3234239 := bstep (se 1 (by rfl) ⟨2425679, by rfl⟩ : syracuseStep 3234239 = 4851359) B4851359
theorem B2156159 : Blo 2155435 2156159 := bstep (se 1 (by rfl) ⟨1617119, by rfl⟩ : syracuseStep 2156159 = 3234239) B3234239
theorem B3234245 : Blo 2155435 3234245 := bbase (se 4 (by rfl) ⟨303210, by rfl⟩ : syracuseStep 3234245 = 606421) (by norm_num)
theorem B2156163 : Blo 2155435 2156163 := bstep (se 1 (by rfl) ⟨1617122, by rfl⟩ : syracuseStep 2156163 = 3234245) B3234245
theorem B3638533 : Blo 2155435 3638533 := bbase (se 4 (by rfl) ⟨341112, by rfl⟩ : syracuseStep 3638533 = 682225) (by norm_num)
theorem B4851377 : Blo 2155435 4851377 := bstep (se 2 (by rfl) ⟨1819266, by rfl⟩ : syracuseStep 4851377 = 3638533) B3638533
theorem B3234251 : Blo 2155435 3234251 := bstep (se 1 (by rfl) ⟨2425688, by rfl⟩ : syracuseStep 3234251 = 4851377) B4851377
theorem B2156167 : Blo 2155435 2156167 := bstep (se 1 (by rfl) ⟨1617125, by rfl⟩ : syracuseStep 2156167 = 3234251) B3234251
theorem B2425693 : Blo 2155435 2425693 := bbase (se 3 (by rfl) ⟨454817, by rfl⟩ : syracuseStep 2425693 = 909635) (by norm_num)
theorem B3234257 : Blo 2155435 3234257 := bstep (se 2 (by rfl) ⟨1212846, by rfl⟩ : syracuseStep 3234257 = 2425693) B2425693
theorem B2156171 : Blo 2155435 2156171 := bstep (se 1 (by rfl) ⟨1617128, by rfl⟩ : syracuseStep 2156171 = 3234257) B3234257
theorem B7277093 : Blo 2155435 7277093 := bbase (se 4 (by rfl) ⟨682227, by rfl⟩ : syracuseStep 7277093 = 1364455) (by norm_num)
theorem B4851395 : Blo 2155435 4851395 := bstep (se 1 (by rfl) ⟨3638546, by rfl⟩ : syracuseStep 4851395 = 7277093) B7277093
theorem B3234263 : Blo 2155435 3234263 := bstep (se 1 (by rfl) ⟨2425697, by rfl⟩ : syracuseStep 3234263 = 4851395) B4851395
theorem B2156175 : Blo 2155435 2156175 := bstep (se 1 (by rfl) ⟨1617131, by rfl⟩ : syracuseStep 2156175 = 3234263) B3234263
theorem B3234269 : Blo 2155435 3234269 := bbase (se 3 (by rfl) ⟨606425, by rfl⟩ : syracuseStep 3234269 = 1212851) (by norm_num)
theorem B2156179 : Blo 2155435 2156179 := bstep (se 1 (by rfl) ⟨1617134, by rfl⟩ : syracuseStep 2156179 = 3234269) B3234269
theorem B4851413 : Blo 2155435 4851413 := bbase (se 7 (by rfl) ⟨56852, by rfl⟩ : syracuseStep 4851413 = 113705) (by norm_num)
theorem B3234275 : Blo 2155435 3234275 := bstep (se 1 (by rfl) ⟨2425706, by rfl⟩ : syracuseStep 3234275 = 4851413) B4851413
theorem B2156183 : Blo 2155435 2156183 := bstep (se 1 (by rfl) ⟨1617137, by rfl⟩ : syracuseStep 2156183 = 3234275) B3234275
theorem B3453797 : Blo 2155435 3453797 := bbase (se 4 (by rfl) ⟨323793, by rfl⟩ : syracuseStep 3453797 = 647587) (by norm_num)
theorem B9210125 : Blo 2155435 9210125 := bstep (se 3 (by rfl) ⟨1726898, by rfl⟩ : syracuseStep 9210125 = 3453797) B3453797
theorem B6140083 : Blo 2155435 6140083 := bstep (se 1 (by rfl) ⟨4605062, by rfl⟩ : syracuseStep 6140083 = 9210125) B9210125
theorem B8186777 : Blo 2155435 8186777 := bstep (se 2 (by rfl) ⟨3070041, by rfl⟩ : syracuseStep 8186777 = 6140083) B6140083
theorem B5457851 : Blo 2155435 5457851 := bstep (se 1 (by rfl) ⟨4093388, by rfl⟩ : syracuseStep 5457851 = 8186777) B8186777
theorem B3638567 : Blo 2155435 3638567 := bstep (se 1 (by rfl) ⟨2728925, by rfl⟩ : syracuseStep 3638567 = 5457851) B5457851
theorem B2425711 : Blo 2155435 2425711 := bstep (se 1 (by rfl) ⟨1819283, by rfl⟩ : syracuseStep 2425711 = 3638567) B3638567
theorem B3234281 : Blo 2155435 3234281 := bstep (se 2 (by rfl) ⟨1212855, by rfl⟩ : syracuseStep 3234281 = 2425711) B2425711
theorem B2156187 : Blo 2155435 2156187 := bstep (se 1 (by rfl) ⟨1617140, by rfl⟩ : syracuseStep 2156187 = 3234281) B3234281
theorem B22129301 : Blo 2155435 22129301 := bbase (se 6 (by rfl) ⟨518655, by rfl⟩ : syracuseStep 22129301 = 1037311) (by norm_num)
theorem B14752867 : Blo 2155435 14752867 := bstep (se 1 (by rfl) ⟨11064650, by rfl⟩ : syracuseStep 14752867 = 22129301) B22129301
theorem B19670489 : Blo 2155435 19670489 := bstep (se 2 (by rfl) ⟨7376433, by rfl⟩ : syracuseStep 19670489 = 14752867) B14752867
theorem B13113659 : Blo 2155435 13113659 := bstep (se 1 (by rfl) ⟨9835244, by rfl⟩ : syracuseStep 13113659 = 19670489) B19670489
theorem B8742439 : Blo 2155435 8742439 := bstep (se 1 (by rfl) ⟨6556829, by rfl⟩ : syracuseStep 8742439 = 13113659) B13113659
theorem B11656585 : Blo 2155435 11656585 := bstep (se 2 (by rfl) ⟨4371219, by rfl⟩ : syracuseStep 11656585 = 8742439) B8742439
theorem B15542113 : Blo 2155435 15542113 := bstep (se 2 (by rfl) ⟨5828292, by rfl⟩ : syracuseStep 15542113 = 11656585) B11656585
theorem B20722817 : Blo 2155435 20722817 := bstep (se 2 (by rfl) ⟨7771056, by rfl⟩ : syracuseStep 20722817 = 15542113) B15542113
theorem B13815211 : Blo 2155435 13815211 := bstep (se 1 (by rfl) ⟨10361408, by rfl⟩ : syracuseStep 13815211 = 20722817) B20722817
theorem B18420281 : Blo 2155435 18420281 := bstep (se 2 (by rfl) ⟨6907605, by rfl⟩ : syracuseStep 18420281 = 13815211) B13815211
theorem B12280187 : Blo 2155435 12280187 := bstep (se 1 (by rfl) ⟨9210140, by rfl⟩ : syracuseStep 12280187 = 18420281) B18420281
theorem B8186791 : Blo 2155435 8186791 := bstep (se 1 (by rfl) ⟨6140093, by rfl⟩ : syracuseStep 8186791 = 12280187) B12280187
theorem B10915721 : Blo 2155435 10915721 := bstep (se 2 (by rfl) ⟨4093395, by rfl⟩ : syracuseStep 10915721 = 8186791) B8186791
theorem B7277147 : Blo 2155435 7277147 := bstep (se 1 (by rfl) ⟨5457860, by rfl⟩ : syracuseStep 7277147 = 10915721) B10915721
theorem B4851431 : Blo 2155435 4851431 := bstep (se 1 (by rfl) ⟨3638573, by rfl⟩ : syracuseStep 4851431 = 7277147) B7277147
theorem B3234287 : Blo 2155435 3234287 := bstep (se 1 (by rfl) ⟨2425715, by rfl⟩ : syracuseStep 3234287 = 4851431) B4851431
theorem B2156191 : Blo 2155435 2156191 := bstep (se 1 (by rfl) ⟨1617143, by rfl⟩ : syracuseStep 2156191 = 3234287) B3234287
theorem B3234293 : Blo 2155435 3234293 := bbase (se 5 (by rfl) ⟨151607, by rfl⟩ : syracuseStep 3234293 = 303215) (by norm_num)
theorem B2156195 : Blo 2155435 2156195 := bstep (se 1 (by rfl) ⟨1617146, by rfl⟩ : syracuseStep 2156195 = 3234293) B3234293
theorem B6140117 : Blo 2155435 6140117 := bbase (se 7 (by rfl) ⟨71954, by rfl⟩ : syracuseStep 6140117 = 143909) (by norm_num)
theorem B4093411 : Blo 2155435 4093411 := bstep (se 1 (by rfl) ⟨3070058, by rfl⟩ : syracuseStep 4093411 = 6140117) B6140117
theorem B5457881 : Blo 2155435 5457881 := bstep (se 2 (by rfl) ⟨2046705, by rfl⟩ : syracuseStep 5457881 = 4093411) B4093411
theorem B3638587 : Blo 2155435 3638587 := bstep (se 1 (by rfl) ⟨2728940, by rfl⟩ : syracuseStep 3638587 = 5457881) B5457881
theorem B4851449 : Blo 2155435 4851449 := bstep (se 2 (by rfl) ⟨1819293, by rfl⟩ : syracuseStep 4851449 = 3638587) B3638587
theorem B3234299 : Blo 2155435 3234299 := bstep (se 1 (by rfl) ⟨2425724, by rfl⟩ : syracuseStep 3234299 = 4851449) B4851449
theorem B2156199 : Blo 2155435 2156199 := bstep (se 1 (by rfl) ⟨1617149, by rfl⟩ : syracuseStep 2156199 = 3234299) B3234299
theorem B2425729 : Blo 2155435 2425729 := bbase (se 2 (by rfl) ⟨909648, by rfl⟩ : syracuseStep 2425729 = 1819297) (by norm_num)
theorem B3234305 : Blo 2155435 3234305 := bstep (se 2 (by rfl) ⟨1212864, by rfl⟩ : syracuseStep 3234305 = 2425729) B2425729
theorem B2156203 : Blo 2155435 2156203 := bstep (se 1 (by rfl) ⟨1617152, by rfl⟩ : syracuseStep 2156203 = 3234305) B3234305
theorem B5457901 : Blo 2155435 5457901 := bbase (se 3 (by rfl) ⟨1023356, by rfl⟩ : syracuseStep 5457901 = 2046713) (by norm_num)
theorem B7277201 : Blo 2155435 7277201 := bstep (se 2 (by rfl) ⟨2728950, by rfl⟩ : syracuseStep 7277201 = 5457901) B5457901
theorem B4851467 : Blo 2155435 4851467 := bstep (se 1 (by rfl) ⟨3638600, by rfl⟩ : syracuseStep 4851467 = 7277201) B7277201
theorem B3234311 : Blo 2155435 3234311 := bstep (se 1 (by rfl) ⟨2425733, by rfl⟩ : syracuseStep 3234311 = 4851467) B4851467
theorem B2156207 : Blo 2155435 2156207 := bstep (se 1 (by rfl) ⟨1617155, by rfl⟩ : syracuseStep 2156207 = 3234311) B3234311
theorem B3234317 : Blo 2155435 3234317 := bbase (se 3 (by rfl) ⟨606434, by rfl⟩ : syracuseStep 3234317 = 1212869) (by norm_num)
theorem B2156211 : Blo 2155435 2156211 := bstep (se 1 (by rfl) ⟨1617158, by rfl⟩ : syracuseStep 2156211 = 3234317) B3234317
theorem B4851485 : Blo 2155435 4851485 := bbase (se 3 (by rfl) ⟨909653, by rfl⟩ : syracuseStep 4851485 = 1819307) (by norm_num)
theorem B3234323 : Blo 2155435 3234323 := bstep (se 1 (by rfl) ⟨2425742, by rfl⟩ : syracuseStep 3234323 = 4851485) B4851485
theorem B2156215 : Blo 2155435 2156215 := bstep (se 1 (by rfl) ⟨1617161, by rfl⟩ : syracuseStep 2156215 = 3234323) B3234323
theorem B3638621 : Blo 2155435 3638621 := bbase (se 3 (by rfl) ⟨682241, by rfl⟩ : syracuseStep 3638621 = 1364483) (by norm_num)
theorem B2425747 : Blo 2155435 2425747 := bstep (se 1 (by rfl) ⟨1819310, by rfl⟩ : syracuseStep 2425747 = 3638621) B3638621
theorem B3234329 : Blo 2155435 3234329 := bstep (se 2 (by rfl) ⟨1212873, by rfl⟩ : syracuseStep 3234329 = 2425747) B2425747
theorem B2156219 : Blo 2155435 2156219 := bstep (se 1 (by rfl) ⟨1617164, by rfl⟩ : syracuseStep 2156219 = 3234329) B3234329
theorem B9210277 : Blo 2155435 9210277 := bbase (se 4 (by rfl) ⟨863463, by rfl⟩ : syracuseStep 9210277 = 1726927) (by norm_num)
theorem B12280369 : Blo 2155435 12280369 := bstep (se 2 (by rfl) ⟨4605138, by rfl⟩ : syracuseStep 12280369 = 9210277) B9210277
theorem B16373825 : Blo 2155435 16373825 := bstep (se 2 (by rfl) ⟨6140184, by rfl⟩ : syracuseStep 16373825 = 12280369) B12280369
theorem B10915883 : Blo 2155435 10915883 := bstep (se 1 (by rfl) ⟨8186912, by rfl⟩ : syracuseStep 10915883 = 16373825) B16373825
theorem B7277255 : Blo 2155435 7277255 := bstep (se 1 (by rfl) ⟨5457941, by rfl⟩ : syracuseStep 7277255 = 10915883) B10915883
theorem B4851503 : Blo 2155435 4851503 := bstep (se 1 (by rfl) ⟨3638627, by rfl⟩ : syracuseStep 4851503 = 7277255) B7277255
theorem B3234335 : Blo 2155435 3234335 := bstep (se 1 (by rfl) ⟨2425751, by rfl⟩ : syracuseStep 3234335 = 4851503) B4851503
theorem B2156223 : Blo 2155435 2156223 := bstep (se 1 (by rfl) ⟨1617167, by rfl⟩ : syracuseStep 2156223 = 3234335) B3234335
theorem B3234341 : Blo 2155435 3234341 := bbase (se 4 (by rfl) ⟨303219, by rfl⟩ : syracuseStep 3234341 = 606439) (by norm_num)
theorem B2156227 : Blo 2155435 2156227 := bstep (se 1 (by rfl) ⟨1617170, by rfl⟩ : syracuseStep 2156227 = 3234341) B3234341
theorem B2728981 : Blo 2155435 2728981 := bbase (se 6 (by rfl) ⟨63960, by rfl⟩ : syracuseStep 2728981 = 127921) (by norm_num)
theorem B3638641 : Blo 2155435 3638641 := bstep (se 2 (by rfl) ⟨1364490, by rfl⟩ : syracuseStep 3638641 = 2728981) B2728981
theorem B4851521 : Blo 2155435 4851521 := bstep (se 2 (by rfl) ⟨1819320, by rfl⟩ : syracuseStep 4851521 = 3638641) B3638641
theorem B3234347 : Blo 2155435 3234347 := bstep (se 1 (by rfl) ⟨2425760, by rfl⟩ : syracuseStep 3234347 = 4851521) B4851521
theorem B2156231 : Blo 2155435 2156231 := bstep (se 1 (by rfl) ⟨1617173, by rfl⟩ : syracuseStep 2156231 = 3234347) B3234347
theorem B2425765 : Blo 2155435 2425765 := bbase (se 4 (by rfl) ⟨227415, by rfl⟩ : syracuseStep 2425765 = 454831) (by norm_num)
theorem B3234353 : Blo 2155435 3234353 := bstep (se 2 (by rfl) ⟨1212882, by rfl⟩ : syracuseStep 3234353 = 2425765) B2425765
theorem B2156235 : Blo 2155435 2156235 := bstep (se 1 (by rfl) ⟨1617176, by rfl⟩ : syracuseStep 2156235 = 3234353) B3234353
theorem B4668005 : Blo 2155435 4668005 := bbase (se 4 (by rfl) ⟨437625, by rfl⟩ : syracuseStep 4668005 = 875251) (by norm_num)
theorem B3112003 : Blo 2155435 3112003 := bstep (se 1 (by rfl) ⟨2334002, by rfl⟩ : syracuseStep 3112003 = 4668005) B4668005
theorem B16597349 : Blo 2155435 16597349 := bstep (se 4 (by rfl) ⟨1556001, by rfl⟩ : syracuseStep 16597349 = 3112003) B3112003
theorem B11064899 : Blo 2155435 11064899 := bstep (se 1 (by rfl) ⟨8298674, by rfl⟩ : syracuseStep 11064899 = 16597349) B16597349
theorem B7376599 : Blo 2155435 7376599 := bstep (se 1 (by rfl) ⟨5532449, by rfl⟩ : syracuseStep 7376599 = 11064899) B11064899
theorem B39341861 : Blo 2155435 39341861 := bstep (se 4 (by rfl) ⟨3688299, by rfl⟩ : syracuseStep 39341861 = 7376599) B7376599
theorem B26227907 : Blo 2155435 26227907 := bstep (se 1 (by rfl) ⟨19670930, by rfl⟩ : syracuseStep 26227907 = 39341861) B39341861
theorem B17485271 : Blo 2155435 17485271 := bstep (se 1 (by rfl) ⟨13113953, by rfl⟩ : syracuseStep 17485271 = 26227907) B26227907
theorem B11656847 : Blo 2155435 11656847 := bstep (se 1 (by rfl) ⟨8742635, by rfl⟩ : syracuseStep 11656847 = 17485271) B17485271
theorem B7771231 : Blo 2155435 7771231 := bstep (se 1 (by rfl) ⟨5828423, by rfl⟩ : syracuseStep 7771231 = 11656847) B11656847
theorem B10361641 : Blo 2155435 10361641 := bstep (se 2 (by rfl) ⟨3885615, by rfl⟩ : syracuseStep 10361641 = 7771231) B7771231
theorem B13815521 : Blo 2155435 13815521 := bstep (se 2 (by rfl) ⟨5180820, by rfl⟩ : syracuseStep 13815521 = 10361641) B10361641
theorem B9210347 : Blo 2155435 9210347 := bstep (se 1 (by rfl) ⟨6907760, by rfl⟩ : syracuseStep 9210347 = 13815521) B13815521
theorem B6140231 : Blo 2155435 6140231 := bstep (se 1 (by rfl) ⟨4605173, by rfl⟩ : syracuseStep 6140231 = 9210347) B9210347
theorem B4093487 : Blo 2155435 4093487 := bstep (se 1 (by rfl) ⟨3070115, by rfl⟩ : syracuseStep 4093487 = 6140231) B6140231
theorem B2728991 : Blo 2155435 2728991 := bstep (se 1 (by rfl) ⟨2046743, by rfl⟩ : syracuseStep 2728991 = 4093487) B4093487
theorem B7277309 : Blo 2155435 7277309 := bstep (se 3 (by rfl) ⟨1364495, by rfl⟩ : syracuseStep 7277309 = 2728991) B2728991
theorem B4851539 : Blo 2155435 4851539 := bstep (se 1 (by rfl) ⟨3638654, by rfl⟩ : syracuseStep 4851539 = 7277309) B7277309
theorem B3234359 : Blo 2155435 3234359 := bstep (se 1 (by rfl) ⟨2425769, by rfl⟩ : syracuseStep 3234359 = 4851539) B4851539
theorem B2156239 : Blo 2155435 2156239 := bstep (se 1 (by rfl) ⟨1617179, by rfl⟩ : syracuseStep 2156239 = 3234359) B3234359
theorem B3234365 : Blo 2155435 3234365 := bbase (se 3 (by rfl) ⟨606443, by rfl⟩ : syracuseStep 3234365 = 1212887) (by norm_num)
theorem B2156243 : Blo 2155435 2156243 := bstep (se 1 (by rfl) ⟨1617182, by rfl⟩ : syracuseStep 2156243 = 3234365) B3234365
theorem B4851557 : Blo 2155435 4851557 := bbase (se 4 (by rfl) ⟨454833, by rfl⟩ : syracuseStep 4851557 = 909667) (by norm_num)
theorem B3234371 : Blo 2155435 3234371 := bstep (se 1 (by rfl) ⟨2425778, by rfl⟩ : syracuseStep 3234371 = 4851557) B4851557
theorem B2156247 : Blo 2155435 2156247 := bstep (se 1 (by rfl) ⟨1617185, by rfl⟩ : syracuseStep 2156247 = 3234371) B3234371
theorem B5458013 : Blo 2155435 5458013 := bbase (se 3 (by rfl) ⟨1023377, by rfl⟩ : syracuseStep 5458013 = 2046755) (by norm_num)
theorem B3638675 : Blo 2155435 3638675 := bstep (se 1 (by rfl) ⟨2729006, by rfl⟩ : syracuseStep 3638675 = 5458013) B5458013
theorem B2425783 : Blo 2155435 2425783 := bstep (se 1 (by rfl) ⟨1819337, by rfl⟩ : syracuseStep 2425783 = 3638675) B3638675
theorem B3234377 : Blo 2155435 3234377 := bstep (se 2 (by rfl) ⟨1212891, by rfl⟩ : syracuseStep 3234377 = 2425783) B2425783
theorem B2156251 : Blo 2155435 2156251 := bstep (se 1 (by rfl) ⟨1617188, by rfl⟩ : syracuseStep 2156251 = 3234377) B3234377
theorem B4093517 : Blo 2155435 4093517 := bbase (se 3 (by rfl) ⟨767534, by rfl⟩ : syracuseStep 4093517 = 1535069) (by norm_num)
theorem B10916045 : Blo 2155435 10916045 := bstep (se 3 (by rfl) ⟨2046758, by rfl⟩ : syracuseStep 10916045 = 4093517) B4093517
theorem B7277363 : Blo 2155435 7277363 := bstep (se 1 (by rfl) ⟨5458022, by rfl⟩ : syracuseStep 7277363 = 10916045) B10916045
theorem B4851575 : Blo 2155435 4851575 := bstep (se 1 (by rfl) ⟨3638681, by rfl⟩ : syracuseStep 4851575 = 7277363) B7277363
theorem B3234383 : Blo 2155435 3234383 := bstep (se 1 (by rfl) ⟨2425787, by rfl⟩ : syracuseStep 3234383 = 4851575) B4851575
theorem B2156255 : Blo 2155435 2156255 := bstep (se 1 (by rfl) ⟨1617191, by rfl⟩ : syracuseStep 2156255 = 3234383) B3234383
theorem B3234389 : Blo 2155435 3234389 := bbase (se 8 (by rfl) ⟨18951, by rfl⟩ : syracuseStep 3234389 = 37903) (by norm_num)
theorem B2156259 : Blo 2155435 2156259 := bstep (se 1 (by rfl) ⟨1617194, by rfl⟩ : syracuseStep 2156259 = 3234389) B3234389
theorem B2334029 : Blo 2155435 2334029 := bbase (se 3 (by rfl) ⟨437630, by rfl⟩ : syracuseStep 2334029 = 875261) (by norm_num)
theorem B6224077 : Blo 2155435 6224077 := bstep (se 3 (by rfl) ⟨1167014, by rfl⟩ : syracuseStep 6224077 = 2334029) B2334029
theorem B8298769 : Blo 2155435 8298769 := bstep (se 2 (by rfl) ⟨3112038, by rfl⟩ : syracuseStep 8298769 = 6224077) B6224077
theorem B11065025 : Blo 2155435 11065025 := bstep (se 2 (by rfl) ⟨4149384, by rfl⟩ : syracuseStep 11065025 = 8298769) B8298769
theorem B7376683 : Blo 2155435 7376683 := bstep (se 1 (by rfl) ⟨5532512, by rfl⟩ : syracuseStep 7376683 = 11065025) B11065025
theorem B9835577 : Blo 2155435 9835577 := bstep (se 2 (by rfl) ⟨3688341, by rfl⟩ : syracuseStep 9835577 = 7376683) B7376683
theorem B6557051 : Blo 2155435 6557051 := bstep (se 1 (by rfl) ⟨4917788, by rfl⟩ : syracuseStep 6557051 = 9835577) B9835577
theorem B4371367 : Blo 2155435 4371367 := bstep (se 1 (by rfl) ⟨3278525, by rfl⟩ : syracuseStep 4371367 = 6557051) B6557051
theorem B5828489 : Blo 2155435 5828489 := bstep (se 2 (by rfl) ⟨2185683, by rfl⟩ : syracuseStep 5828489 = 4371367) B4371367
theorem B3885659 : Blo 2155435 3885659 := bstep (se 1 (by rfl) ⟨2914244, by rfl⟩ : syracuseStep 3885659 = 5828489) B5828489
theorem B2590439 : Blo 2155435 2590439 := bstep (se 1 (by rfl) ⟨1942829, by rfl⟩ : syracuseStep 2590439 = 3885659) B3885659
theorem B6907837 : Blo 2155435 6907837 := bstep (se 3 (by rfl) ⟨1295219, by rfl⟩ : syracuseStep 6907837 = 2590439) B2590439
theorem B9210449 : Blo 2155435 9210449 := bstep (se 2 (by rfl) ⟨3453918, by rfl⟩ : syracuseStep 9210449 = 6907837) B6907837
theorem B6140299 : Blo 2155435 6140299 := bstep (se 1 (by rfl) ⟨4605224, by rfl⟩ : syracuseStep 6140299 = 9210449) B9210449
theorem B8187065 : Blo 2155435 8187065 := bstep (se 2 (by rfl) ⟨3070149, by rfl⟩ : syracuseStep 8187065 = 6140299) B6140299
theorem B5458043 : Blo 2155435 5458043 := bstep (se 1 (by rfl) ⟨4093532, by rfl⟩ : syracuseStep 5458043 = 8187065) B8187065
theorem B3638695 : Blo 2155435 3638695 := bstep (se 1 (by rfl) ⟨2729021, by rfl⟩ : syracuseStep 3638695 = 5458043) B5458043
theorem B4851593 : Blo 2155435 4851593 := bstep (se 2 (by rfl) ⟨1819347, by rfl⟩ : syracuseStep 4851593 = 3638695) B3638695
theorem B3234395 : Blo 2155435 3234395 := bstep (se 1 (by rfl) ⟨2425796, by rfl⟩ : syracuseStep 3234395 = 4851593) B4851593
theorem B2156263 : Blo 2155435 2156263 := bstep (se 1 (by rfl) ⟨1617197, by rfl⟩ : syracuseStep 2156263 = 3234395) B3234395
theorem B2425801 : Blo 2155435 2425801 := bbase (se 2 (by rfl) ⟨909675, by rfl⟩ : syracuseStep 2425801 = 1819351) (by norm_num)
theorem B3234401 : Blo 2155435 3234401 := bstep (se 2 (by rfl) ⟨1212900, by rfl⟩ : syracuseStep 3234401 = 2425801) B2425801
theorem B2156267 : Blo 2155435 2156267 := bstep (se 1 (by rfl) ⟨1617200, by rfl⟩ : syracuseStep 2156267 = 3234401) B3234401
theorem B5532533 : Blo 2155435 5532533 := bbase (se 5 (by rfl) ⟨259337, by rfl⟩ : syracuseStep 5532533 = 518675) (by norm_num)
theorem B3688355 : Blo 2155435 3688355 := bstep (se 1 (by rfl) ⟨2766266, by rfl⟩ : syracuseStep 3688355 = 5532533) B5532533
theorem B9835613 : Blo 2155435 9835613 := bstep (se 3 (by rfl) ⟨1844177, by rfl⟩ : syracuseStep 9835613 = 3688355) B3688355
theorem B6557075 : Blo 2155435 6557075 := bstep (se 1 (by rfl) ⟨4917806, by rfl⟩ : syracuseStep 6557075 = 9835613) B9835613
theorem B4371383 : Blo 2155435 4371383 := bstep (se 1 (by rfl) ⟨3278537, by rfl⟩ : syracuseStep 4371383 = 6557075) B6557075
theorem B2914255 : Blo 2155435 2914255 := bstep (se 1 (by rfl) ⟨2185691, by rfl⟩ : syracuseStep 2914255 = 4371383) B4371383
theorem B3885673 : Blo 2155435 3885673 := bstep (se 2 (by rfl) ⟨1457127, by rfl⟩ : syracuseStep 3885673 = 2914255) B2914255
theorem B5180897 : Blo 2155435 5180897 := bstep (se 2 (by rfl) ⟨1942836, by rfl⟩ : syracuseStep 5180897 = 3885673) B3885673
theorem B3453931 : Blo 2155435 3453931 := bstep (se 1 (by rfl) ⟨2590448, by rfl⟩ : syracuseStep 3453931 = 5180897) B5180897
theorem B18420965 : Blo 2155435 18420965 := bstep (se 4 (by rfl) ⟨1726965, by rfl⟩ : syracuseStep 18420965 = 3453931) B3453931
theorem B12280643 : Blo 2155435 12280643 := bstep (se 1 (by rfl) ⟨9210482, by rfl⟩ : syracuseStep 12280643 = 18420965) B18420965
theorem B8187095 : Blo 2155435 8187095 := bstep (se 1 (by rfl) ⟨6140321, by rfl⟩ : syracuseStep 8187095 = 12280643) B12280643
theorem B5458063 : Blo 2155435 5458063 := bstep (se 1 (by rfl) ⟨4093547, by rfl⟩ : syracuseStep 5458063 = 8187095) B8187095
theorem B7277417 : Blo 2155435 7277417 := bstep (se 2 (by rfl) ⟨2729031, by rfl⟩ : syracuseStep 7277417 = 5458063) B5458063
theorem B4851611 : Blo 2155435 4851611 := bstep (se 1 (by rfl) ⟨3638708, by rfl⟩ : syracuseStep 4851611 = 7277417) B7277417
theorem B3234407 : Blo 2155435 3234407 := bstep (se 1 (by rfl) ⟨2425805, by rfl⟩ : syracuseStep 3234407 = 4851611) B4851611
theorem B2156271 : Blo 2155435 2156271 := bstep (se 1 (by rfl) ⟨1617203, by rfl⟩ : syracuseStep 2156271 = 3234407) B3234407
theorem B3234413 : Blo 2155435 3234413 := bbase (se 3 (by rfl) ⟨606452, by rfl⟩ : syracuseStep 3234413 = 1212905) (by norm_num)
theorem B2156275 : Blo 2155435 2156275 := bstep (se 1 (by rfl) ⟨1617206, by rfl⟩ : syracuseStep 2156275 = 3234413) B3234413
theorem B4851629 : Blo 2155435 4851629 := bbase (se 3 (by rfl) ⟨909680, by rfl⟩ : syracuseStep 4851629 = 1819361) (by norm_num)
theorem B3234419 : Blo 2155435 3234419 := bstep (se 1 (by rfl) ⟨2425814, by rfl⟩ : syracuseStep 3234419 = 4851629) B4851629
theorem B2156279 : Blo 2155435 2156279 := bstep (se 1 (by rfl) ⟨1617209, by rfl⟩ : syracuseStep 2156279 = 3234419) B3234419
theorem B6140357 : Blo 2155435 6140357 := bbase (se 4 (by rfl) ⟨575658, by rfl⟩ : syracuseStep 6140357 = 1151317) (by norm_num)
theorem B4093571 : Blo 2155435 4093571 := bstep (se 1 (by rfl) ⟨3070178, by rfl⟩ : syracuseStep 4093571 = 6140357) B6140357
theorem B2729047 : Blo 2155435 2729047 := bstep (se 1 (by rfl) ⟨2046785, by rfl⟩ : syracuseStep 2729047 = 4093571) B4093571
theorem B3638729 : Blo 2155435 3638729 := bstep (se 2 (by rfl) ⟨1364523, by rfl⟩ : syracuseStep 3638729 = 2729047) B2729047
theorem B2425819 : Blo 2155435 2425819 := bstep (se 1 (by rfl) ⟨1819364, by rfl⟩ : syracuseStep 2425819 = 3638729) B3638729
theorem B3234425 : Blo 2155435 3234425 := bstep (se 2 (by rfl) ⟨1212909, by rfl⟩ : syracuseStep 3234425 = 2425819) B2425819
theorem B2156283 : Blo 2155435 2156283 := bstep (se 1 (by rfl) ⟨1617212, by rfl⟩ : syracuseStep 2156283 = 3234425) B3234425
theorem B3885701 : Blo 2155435 3885701 := bbase (se 4 (by rfl) ⟨364284, by rfl⟩ : syracuseStep 3885701 = 728569) (by norm_num)
theorem B41447477 : Blo 2155435 41447477 := bstep (se 5 (by rfl) ⟨1942850, by rfl⟩ : syracuseStep 41447477 = 3885701) B3885701
theorem B27631651 : Blo 2155435 27631651 := bstep (se 1 (by rfl) ⟨20723738, by rfl⟩ : syracuseStep 27631651 = 41447477) B41447477
theorem B36842201 : Blo 2155435 36842201 := bstep (se 2 (by rfl) ⟨13815825, by rfl⟩ : syracuseStep 36842201 = 27631651) B27631651
theorem B24561467 : Blo 2155435 24561467 := bstep (se 1 (by rfl) ⟨18421100, by rfl⟩ : syracuseStep 24561467 = 36842201) B36842201
theorem B16374311 : Blo 2155435 16374311 := bstep (se 1 (by rfl) ⟨12280733, by rfl⟩ : syracuseStep 16374311 = 24561467) B24561467
theorem B10916207 : Blo 2155435 10916207 := bstep (se 1 (by rfl) ⟨8187155, by rfl⟩ : syracuseStep 10916207 = 16374311) B16374311
theorem B7277471 : Blo 2155435 7277471 := bstep (se 1 (by rfl) ⟨5458103, by rfl⟩ : syracuseStep 7277471 = 10916207) B10916207
theorem B4851647 : Blo 2155435 4851647 := bstep (se 1 (by rfl) ⟨3638735, by rfl⟩ : syracuseStep 4851647 = 7277471) B7277471
theorem B3234431 : Blo 2155435 3234431 := bstep (se 1 (by rfl) ⟨2425823, by rfl⟩ : syracuseStep 3234431 = 4851647) B4851647
theorem B2156287 : Blo 2155435 2156287 := bstep (se 1 (by rfl) ⟨1617215, by rfl⟩ : syracuseStep 2156287 = 3234431) B3234431
theorem B3234437 : Blo 2155435 3234437 := bbase (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) (by norm_num)
theorem B2156291 : Blo 2155435 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B3638749 : Blo 2155435 3638749 := bbase (se 3 (by rfl) ⟨682265, by rfl⟩ : syracuseStep 3638749 = 1364531) (by norm_num)
theorem B4851665 : Blo 2155435 4851665 := bstep (se 2 (by rfl) ⟨1819374, by rfl⟩ : syracuseStep 4851665 = 3638749) B3638749
theorem B3234443 : Blo 2155435 3234443 := bstep (se 1 (by rfl) ⟨2425832, by rfl⟩ : syracuseStep 3234443 = 4851665) B4851665
theorem B2156295 : Blo 2155435 2156295 := bstep (se 1 (by rfl) ⟨1617221, by rfl⟩ : syracuseStep 2156295 = 3234443) B3234443
theorem B2425837 : Blo 2155435 2425837 := bbase (se 3 (by rfl) ⟨454844, by rfl⟩ : syracuseStep 2425837 = 909689) (by norm_num)
theorem B3234449 : Blo 2155435 3234449 := bstep (se 2 (by rfl) ⟨1212918, by rfl⟩ : syracuseStep 3234449 = 2425837) B2425837
theorem B2156299 : Blo 2155435 2156299 := bstep (se 1 (by rfl) ⟨1617224, by rfl⟩ : syracuseStep 2156299 = 3234449) B3234449
theorem B7277525 : Blo 2155435 7277525 := bbase (se 7 (by rfl) ⟨85283, by rfl⟩ : syracuseStep 7277525 = 170567) (by norm_num)
theorem B4851683 : Blo 2155435 4851683 := bstep (se 1 (by rfl) ⟨3638762, by rfl⟩ : syracuseStep 4851683 = 7277525) B7277525
theorem B3234455 : Blo 2155435 3234455 := bstep (se 1 (by rfl) ⟨2425841, by rfl⟩ : syracuseStep 3234455 = 4851683) B4851683
theorem B2156303 : Blo 2155435 2156303 := bstep (se 1 (by rfl) ⟨1617227, by rfl⟩ : syracuseStep 2156303 = 3234455) B3234455
theorem B3234461 : Blo 2155435 3234461 := bbase (se 3 (by rfl) ⟨606461, by rfl⟩ : syracuseStep 3234461 = 1212923) (by norm_num)
theorem B2156307 : Blo 2155435 2156307 := bstep (se 1 (by rfl) ⟨1617230, by rfl⟩ : syracuseStep 2156307 = 3234461) B3234461
theorem B4851701 : Blo 2155435 4851701 := bbase (se 5 (by rfl) ⟨227423, by rfl⟩ : syracuseStep 4851701 = 454847) (by norm_num)
theorem B3234467 : Blo 2155435 3234467 := bstep (se 1 (by rfl) ⟨2425850, by rfl⟩ : syracuseStep 3234467 = 4851701) B4851701
theorem B2156311 : Blo 2155435 2156311 := bstep (se 1 (by rfl) ⟨1617233, by rfl⟩ : syracuseStep 2156311 = 3234467) B3234467
theorem B14753717 : Blo 2155435 14753717 := bbase (se 5 (by rfl) ⟨691580, by rfl⟩ : syracuseStep 14753717 = 1383161) (by norm_num)
theorem B9835811 : Blo 2155435 9835811 := bstep (se 1 (by rfl) ⟨7376858, by rfl⟩ : syracuseStep 9835811 = 14753717) B14753717
theorem B6557207 : Blo 2155435 6557207 := bstep (se 1 (by rfl) ⟨4917905, by rfl⟩ : syracuseStep 6557207 = 9835811) B9835811
theorem B17485885 : Blo 2155435 17485885 := bstep (se 3 (by rfl) ⟨3278603, by rfl⟩ : syracuseStep 17485885 = 6557207) B6557207
theorem B93258053 : Blo 2155435 93258053 := bstep (se 4 (by rfl) ⟨8742942, by rfl⟩ : syracuseStep 93258053 = 17485885) B17485885
theorem B62172035 : Blo 2155435 62172035 := bstep (se 1 (by rfl) ⟨46629026, by rfl⟩ : syracuseStep 62172035 = 93258053) B93258053
theorem B41448023 : Blo 2155435 41448023 := bstep (se 1 (by rfl) ⟨31086017, by rfl⟩ : syracuseStep 41448023 = 62172035) B62172035
theorem B27632015 : Blo 2155435 27632015 := bstep (se 1 (by rfl) ⟨20724011, by rfl⟩ : syracuseStep 27632015 = 41448023) B41448023
theorem B18421343 : Blo 2155435 18421343 := bstep (se 1 (by rfl) ⟨13816007, by rfl⟩ : syracuseStep 18421343 = 27632015) B27632015
theorem B12280895 : Blo 2155435 12280895 := bstep (se 1 (by rfl) ⟨9210671, by rfl⟩ : syracuseStep 12280895 = 18421343) B18421343
theorem B8187263 : Blo 2155435 8187263 := bstep (se 1 (by rfl) ⟨6140447, by rfl⟩ : syracuseStep 8187263 = 12280895) B12280895
theorem B5458175 : Blo 2155435 5458175 := bstep (se 1 (by rfl) ⟨4093631, by rfl⟩ : syracuseStep 5458175 = 8187263) B8187263
theorem B3638783 : Blo 2155435 3638783 := bstep (se 1 (by rfl) ⟨2729087, by rfl⟩ : syracuseStep 3638783 = 5458175) B5458175
theorem B2425855 : Blo 2155435 2425855 := bstep (se 1 (by rfl) ⟨1819391, by rfl⟩ : syracuseStep 2425855 = 3638783) B3638783
theorem B3234473 : Blo 2155435 3234473 := bstep (se 2 (by rfl) ⟨1212927, by rfl⟩ : syracuseStep 3234473 = 2425855) B2425855
theorem B2156315 : Blo 2155435 2156315 := bstep (se 1 (by rfl) ⟨1617236, by rfl⟩ : syracuseStep 2156315 = 3234473) B3234473
theorem B3070229 : Blo 2155435 3070229 := bbase (se 6 (by rfl) ⟨71958, by rfl⟩ : syracuseStep 3070229 = 143917) (by norm_num)
theorem B8187277 : Blo 2155435 8187277 := bstep (se 3 (by rfl) ⟨1535114, by rfl⟩ : syracuseStep 8187277 = 3070229) B3070229
theorem B10916369 : Blo 2155435 10916369 := bstep (se 2 (by rfl) ⟨4093638, by rfl⟩ : syracuseStep 10916369 = 8187277) B8187277
theorem B7277579 : Blo 2155435 7277579 := bstep (se 1 (by rfl) ⟨5458184, by rfl⟩ : syracuseStep 7277579 = 10916369) B10916369
theorem B4851719 : Blo 2155435 4851719 := bstep (se 1 (by rfl) ⟨3638789, by rfl⟩ : syracuseStep 4851719 = 7277579) B7277579
theorem B3234479 : Blo 2155435 3234479 := bstep (se 1 (by rfl) ⟨2425859, by rfl⟩ : syracuseStep 3234479 = 4851719) B4851719
theorem B2156319 : Blo 2155435 2156319 := bstep (se 1 (by rfl) ⟨1617239, by rfl⟩ : syracuseStep 2156319 = 3234479) B3234479
theorem B3234485 : Blo 2155435 3234485 := bbase (se 5 (by rfl) ⟨151616, by rfl⟩ : syracuseStep 3234485 = 303233) (by norm_num)
theorem B2156323 : Blo 2155435 2156323 := bstep (se 1 (by rfl) ⟨1617242, by rfl⟩ : syracuseStep 2156323 = 3234485) B3234485
theorem B5458205 : Blo 2155435 5458205 := bbase (se 3 (by rfl) ⟨1023413, by rfl⟩ : syracuseStep 5458205 = 2046827) (by norm_num)
theorem B3638803 : Blo 2155435 3638803 := bstep (se 1 (by rfl) ⟨2729102, by rfl⟩ : syracuseStep 3638803 = 5458205) B5458205
theorem B4851737 : Blo 2155435 4851737 := bstep (se 2 (by rfl) ⟨1819401, by rfl⟩ : syracuseStep 4851737 = 3638803) B3638803
theorem B3234491 : Blo 2155435 3234491 := bstep (se 1 (by rfl) ⟨2425868, by rfl⟩ : syracuseStep 3234491 = 4851737) B4851737
theorem B2156327 : Blo 2155435 2156327 := bstep (se 1 (by rfl) ⟨1617245, by rfl⟩ : syracuseStep 2156327 = 3234491) B3234491
theorem B2425873 : Blo 2155435 2425873 := bbase (se 2 (by rfl) ⟨909702, by rfl⟩ : syracuseStep 2425873 = 1819405) (by norm_num)
theorem B3234497 : Blo 2155435 3234497 := bstep (se 2 (by rfl) ⟨1212936, by rfl⟩ : syracuseStep 3234497 = 2425873) B2425873
theorem B2156331 : Blo 2155435 2156331 := bstep (se 1 (by rfl) ⟨1617248, by rfl⟩ : syracuseStep 2156331 = 3234497) B3234497
theorem B4093669 : Blo 2155435 4093669 := bbase (se 4 (by rfl) ⟨383781, by rfl⟩ : syracuseStep 4093669 = 767563) (by norm_num)
theorem B5458225 : Blo 2155435 5458225 := bstep (se 2 (by rfl) ⟨2046834, by rfl⟩ : syracuseStep 5458225 = 4093669) B4093669
theorem B7277633 : Blo 2155435 7277633 := bstep (se 2 (by rfl) ⟨2729112, by rfl⟩ : syracuseStep 7277633 = 5458225) B5458225
theorem B4851755 : Blo 2155435 4851755 := bstep (se 1 (by rfl) ⟨3638816, by rfl⟩ : syracuseStep 4851755 = 7277633) B7277633
theorem B3234503 : Blo 2155435 3234503 := bstep (se 1 (by rfl) ⟨2425877, by rfl⟩ : syracuseStep 3234503 = 4851755) B4851755
theorem B2156335 : Blo 2155435 2156335 := bstep (se 1 (by rfl) ⟨1617251, by rfl⟩ : syracuseStep 2156335 = 3234503) B3234503
theorem B3234509 : Blo 2155435 3234509 := bbase (se 3 (by rfl) ⟨606470, by rfl⟩ : syracuseStep 3234509 = 1212941) (by norm_num)
theorem B2156339 : Blo 2155435 2156339 := bstep (se 1 (by rfl) ⟨1617254, by rfl⟩ : syracuseStep 2156339 = 3234509) B3234509
theorem B4851773 : Blo 2155435 4851773 := bbase (se 3 (by rfl) ⟨909707, by rfl⟩ : syracuseStep 4851773 = 1819415) (by norm_num)
theorem B3234515 : Blo 2155435 3234515 := bstep (se 1 (by rfl) ⟨2425886, by rfl⟩ : syracuseStep 3234515 = 4851773) B4851773
theorem B2156343 : Blo 2155435 2156343 := bstep (se 1 (by rfl) ⟨1617257, by rfl⟩ : syracuseStep 2156343 = 3234515) B3234515
theorem B3638837 : Blo 2155435 3638837 := bbase (se 5 (by rfl) ⟨170570, by rfl⟩ : syracuseStep 3638837 = 341141) (by norm_num)
theorem B2425891 : Blo 2155435 2425891 := bstep (se 1 (by rfl) ⟨1819418, by rfl⟩ : syracuseStep 2425891 = 3638837) B3638837
theorem B3234521 : Blo 2155435 3234521 := bstep (se 2 (by rfl) ⟨1212945, by rfl⟩ : syracuseStep 3234521 = 2425891) B2425891
theorem B2156347 : Blo 2155435 2156347 := bstep (se 1 (by rfl) ⟨1617260, by rfl⟩ : syracuseStep 2156347 = 3234521) B3234521
theorem B6140549 : Blo 2155435 6140549 := bbase (se 4 (by rfl) ⟨575676, by rfl⟩ : syracuseStep 6140549 = 1151353) (by norm_num)
theorem B16374797 : Blo 2155435 16374797 := bstep (se 3 (by rfl) ⟨3070274, by rfl⟩ : syracuseStep 16374797 = 6140549) B6140549
theorem B10916531 : Blo 2155435 10916531 := bstep (se 1 (by rfl) ⟨8187398, by rfl⟩ : syracuseStep 10916531 = 16374797) B16374797
theorem B7277687 : Blo 2155435 7277687 := bstep (se 1 (by rfl) ⟨5458265, by rfl⟩ : syracuseStep 7277687 = 10916531) B10916531
theorem B4851791 : Blo 2155435 4851791 := bstep (se 1 (by rfl) ⟨3638843, by rfl⟩ : syracuseStep 4851791 = 7277687) B7277687
theorem B3234527 : Blo 2155435 3234527 := bstep (se 1 (by rfl) ⟨2425895, by rfl⟩ : syracuseStep 3234527 = 4851791) B4851791
theorem B2156351 : Blo 2155435 2156351 := bstep (se 1 (by rfl) ⟨1617263, by rfl⟩ : syracuseStep 2156351 = 3234527) B3234527
theorem B3234533 : Blo 2155435 3234533 := bbase (se 4 (by rfl) ⟨303237, by rfl⟩ : syracuseStep 3234533 = 606475) (by norm_num)
theorem B2156355 : Blo 2155435 2156355 := bstep (se 1 (by rfl) ⟨1617266, by rfl⟩ : syracuseStep 2156355 = 3234533) B3234533
theorem B6224357 : Blo 2155435 6224357 := bbase (se 4 (by rfl) ⟨583533, by rfl⟩ : syracuseStep 6224357 = 1167067) (by norm_num)
theorem B4149571 : Blo 2155435 4149571 := bstep (se 1 (by rfl) ⟨3112178, by rfl⟩ : syracuseStep 4149571 = 6224357) B6224357
theorem B5532761 : Blo 2155435 5532761 := bstep (se 2 (by rfl) ⟨2074785, by rfl⟩ : syracuseStep 5532761 = 4149571) B4149571
theorem B3688507 : Blo 2155435 3688507 := bstep (se 1 (by rfl) ⟨2766380, by rfl⟩ : syracuseStep 3688507 = 5532761) B5532761
theorem B4918009 : Blo 2155435 4918009 := bstep (se 2 (by rfl) ⟨1844253, by rfl⟩ : syracuseStep 4918009 = 3688507) B3688507
theorem B6557345 : Blo 2155435 6557345 := bstep (se 2 (by rfl) ⟨2459004, by rfl⟩ : syracuseStep 6557345 = 4918009) B4918009
theorem B4371563 : Blo 2155435 4371563 := bstep (se 1 (by rfl) ⟨3278672, by rfl⟩ : syracuseStep 4371563 = 6557345) B6557345
theorem B2914375 : Blo 2155435 2914375 := bstep (se 1 (by rfl) ⟨2185781, by rfl⟩ : syracuseStep 2914375 = 4371563) B4371563
theorem B3885833 : Blo 2155435 3885833 := bstep (se 2 (by rfl) ⟨1457187, by rfl⟩ : syracuseStep 3885833 = 2914375) B2914375
theorem B2590555 : Blo 2155435 2590555 := bstep (se 1 (by rfl) ⟨1942916, by rfl⟩ : syracuseStep 2590555 = 3885833) B3885833
theorem B3454073 : Blo 2155435 3454073 := bstep (se 2 (by rfl) ⟨1295277, by rfl⟩ : syracuseStep 3454073 = 2590555) B2590555
theorem B2302715 : Blo 2155435 2302715 := bstep (se 1 (by rfl) ⟨1727036, by rfl⟩ : syracuseStep 2302715 = 3454073) B3454073
theorem B6140573 : Blo 2155435 6140573 := bstep (se 3 (by rfl) ⟨1151357, by rfl⟩ : syracuseStep 6140573 = 2302715) B2302715
theorem B4093715 : Blo 2155435 4093715 := bstep (se 1 (by rfl) ⟨3070286, by rfl⟩ : syracuseStep 4093715 = 6140573) B6140573
theorem B2729143 : Blo 2155435 2729143 := bstep (se 1 (by rfl) ⟨2046857, by rfl⟩ : syracuseStep 2729143 = 4093715) B4093715
theorem B3638857 : Blo 2155435 3638857 := bstep (se 2 (by rfl) ⟨1364571, by rfl⟩ : syracuseStep 3638857 = 2729143) B2729143
theorem B4851809 : Blo 2155435 4851809 := bstep (se 2 (by rfl) ⟨1819428, by rfl⟩ : syracuseStep 4851809 = 3638857) B3638857
theorem B3234539 : Blo 2155435 3234539 := bstep (se 1 (by rfl) ⟨2425904, by rfl⟩ : syracuseStep 3234539 = 4851809) B4851809
theorem B2156359 : Blo 2155435 2156359 := bstep (se 1 (by rfl) ⟨1617269, by rfl⟩ : syracuseStep 2156359 = 3234539) B3234539
theorem B2425909 : Blo 2155435 2425909 := bbase (se 5 (by rfl) ⟨113714, by rfl⟩ : syracuseStep 2425909 = 227429) (by norm_num)
theorem B3234545 : Blo 2155435 3234545 := bstep (se 2 (by rfl) ⟨1212954, by rfl⟩ : syracuseStep 3234545 = 2425909) B2425909
theorem B2156363 : Blo 2155435 2156363 := bstep (se 1 (by rfl) ⟨1617272, by rfl⟩ : syracuseStep 2156363 = 3234545) B3234545
theorem B2729153 : Blo 2155435 2729153 := bbase (se 2 (by rfl) ⟨1023432, by rfl⟩ : syracuseStep 2729153 = 2046865) (by norm_num)
theorem B7277741 : Blo 2155435 7277741 := bstep (se 3 (by rfl) ⟨1364576, by rfl⟩ : syracuseStep 7277741 = 2729153) B2729153
theorem B4851827 : Blo 2155435 4851827 := bstep (se 1 (by rfl) ⟨3638870, by rfl⟩ : syracuseStep 4851827 = 7277741) B7277741
theorem B3234551 : Blo 2155435 3234551 := bstep (se 1 (by rfl) ⟨2425913, by rfl⟩ : syracuseStep 3234551 = 4851827) B4851827
theorem B2156367 : Blo 2155435 2156367 := bstep (se 1 (by rfl) ⟨1617275, by rfl⟩ : syracuseStep 2156367 = 3234551) B3234551
theorem B3234557 : Blo 2155435 3234557 := bbase (se 3 (by rfl) ⟨606479, by rfl⟩ : syracuseStep 3234557 = 1212959) (by norm_num)
theorem B2156371 : Blo 2155435 2156371 := bstep (se 1 (by rfl) ⟨1617278, by rfl⟩ : syracuseStep 2156371 = 3234557) B3234557
theorem B4851845 : Blo 2155435 4851845 := bbase (se 4 (by rfl) ⟨454860, by rfl⟩ : syracuseStep 4851845 = 909721) (by norm_num)
theorem B3234563 : Blo 2155435 3234563 := bstep (se 1 (by rfl) ⟨2425922, by rfl⟩ : syracuseStep 3234563 = 4851845) B4851845
theorem B2156375 : Blo 2155435 2156375 := bstep (se 1 (by rfl) ⟨1617281, by rfl⟩ : syracuseStep 2156375 = 3234563) B3234563
theorem B3885869 : Blo 2155435 3885869 := bbase (se 3 (by rfl) ⟨728600, by rfl⟩ : syracuseStep 3885869 = 1457201) (by norm_num)
theorem B2590579 : Blo 2155435 2590579 := bstep (se 1 (by rfl) ⟨1942934, by rfl⟩ : syracuseStep 2590579 = 3885869) B3885869
theorem B3454105 : Blo 2155435 3454105 := bstep (se 2 (by rfl) ⟨1295289, by rfl⟩ : syracuseStep 3454105 = 2590579) B2590579
theorem B4605473 : Blo 2155435 4605473 := bstep (se 2 (by rfl) ⟨1727052, by rfl⟩ : syracuseStep 4605473 = 3454105) B3454105
theorem B3070315 : Blo 2155435 3070315 := bstep (se 1 (by rfl) ⟨2302736, by rfl⟩ : syracuseStep 3070315 = 4605473) B4605473
theorem B4093753 : Blo 2155435 4093753 := bstep (se 2 (by rfl) ⟨1535157, by rfl⟩ : syracuseStep 4093753 = 3070315) B3070315
theorem B5458337 : Blo 2155435 5458337 := bstep (se 2 (by rfl) ⟨2046876, by rfl⟩ : syracuseStep 5458337 = 4093753) B4093753
theorem B3638891 : Blo 2155435 3638891 := bstep (se 1 (by rfl) ⟨2729168, by rfl⟩ : syracuseStep 3638891 = 5458337) B5458337
theorem B2425927 : Blo 2155435 2425927 := bstep (se 1 (by rfl) ⟨1819445, by rfl⟩ : syracuseStep 2425927 = 3638891) B3638891
theorem B3234569 : Blo 2155435 3234569 := bstep (se 2 (by rfl) ⟨1212963, by rfl⟩ : syracuseStep 3234569 = 2425927) B2425927
theorem B2156379 : Blo 2155435 2156379 := bstep (se 1 (by rfl) ⟨1617284, by rfl⟩ : syracuseStep 2156379 = 3234569) B3234569
theorem B10916693 : Blo 2155435 10916693 := bbase (se 9 (by rfl) ⟨31982, by rfl⟩ : syracuseStep 10916693 = 63965) (by norm_num)
theorem B7277795 : Blo 2155435 7277795 := bstep (se 1 (by rfl) ⟨5458346, by rfl⟩ : syracuseStep 7277795 = 10916693) B10916693
theorem B4851863 : Blo 2155435 4851863 := bstep (se 1 (by rfl) ⟨3638897, by rfl⟩ : syracuseStep 4851863 = 7277795) B7277795
theorem B3234575 : Blo 2155435 3234575 := bstep (se 1 (by rfl) ⟨2425931, by rfl⟩ : syracuseStep 3234575 = 4851863) B4851863
theorem B2156383 : Blo 2155435 2156383 := bstep (se 1 (by rfl) ⟨1617287, by rfl⟩ : syracuseStep 2156383 = 3234575) B3234575
theorem B3234581 : Blo 2155435 3234581 := bbase (se 6 (by rfl) ⟨75810, by rfl⟩ : syracuseStep 3234581 = 151621) (by norm_num)
theorem B2156387 : Blo 2155435 2156387 := bstep (se 1 (by rfl) ⟨1617290, by rfl⟩ : syracuseStep 2156387 = 3234581) B3234581
theorem B10503749 : Blo 2155435 10503749 := bbase (se 4 (by rfl) ⟨984726, by rfl⟩ : syracuseStep 10503749 = 1969453) (by norm_num)
theorem B7002499 : Blo 2155435 7002499 := bstep (se 1 (by rfl) ⟨5251874, by rfl⟩ : syracuseStep 7002499 = 10503749) B10503749
theorem B9336665 : Blo 2155435 9336665 := bstep (se 2 (by rfl) ⟨3501249, by rfl⟩ : syracuseStep 9336665 = 7002499) B7002499
theorem B24897773 : Blo 2155435 24897773 := bstep (se 3 (by rfl) ⟨4668332, by rfl⟩ : syracuseStep 24897773 = 9336665) B9336665
theorem B16598515 : Blo 2155435 16598515 := bstep (se 1 (by rfl) ⟨12448886, by rfl⟩ : syracuseStep 16598515 = 24897773) B24897773
theorem B22131353 : Blo 2155435 22131353 := bstep (se 2 (by rfl) ⟨8299257, by rfl⟩ : syracuseStep 22131353 = 16598515) B16598515
theorem B14754235 : Blo 2155435 14754235 := bstep (se 1 (by rfl) ⟨11065676, by rfl⟩ : syracuseStep 14754235 = 22131353) B22131353
theorem B19672313 : Blo 2155435 19672313 := bstep (se 2 (by rfl) ⟨7377117, by rfl⟩ : syracuseStep 19672313 = 14754235) B14754235
theorem B52459501 : Blo 2155435 52459501 := bstep (se 3 (by rfl) ⟨9836156, by rfl⟩ : syracuseStep 52459501 = 19672313) B19672313
theorem B69946001 : Blo 2155435 69946001 := bstep (se 2 (by rfl) ⟨26229750, by rfl⟩ : syracuseStep 69946001 = 52459501) B52459501
theorem B46630667 : Blo 2155435 46630667 := bstep (se 1 (by rfl) ⟨34973000, by rfl⟩ : syracuseStep 46630667 = 69946001) B69946001
theorem B31087111 : Blo 2155435 31087111 := bstep (se 1 (by rfl) ⟨23315333, by rfl⟩ : syracuseStep 31087111 = 46630667) B46630667
theorem B41449481 : Blo 2155435 41449481 := bstep (se 2 (by rfl) ⟨15543555, by rfl⟩ : syracuseStep 41449481 = 31087111) B31087111
theorem B27632987 : Blo 2155435 27632987 := bstep (se 1 (by rfl) ⟨20724740, by rfl⟩ : syracuseStep 27632987 = 41449481) B41449481
theorem B18421991 : Blo 2155435 18421991 := bstep (se 1 (by rfl) ⟨13816493, by rfl⟩ : syracuseStep 18421991 = 27632987) B27632987
theorem B12281327 : Blo 2155435 12281327 := bstep (se 1 (by rfl) ⟨9210995, by rfl⟩ : syracuseStep 12281327 = 18421991) B18421991
theorem B8187551 : Blo 2155435 8187551 := bstep (se 1 (by rfl) ⟨6140663, by rfl⟩ : syracuseStep 8187551 = 12281327) B12281327
theorem B5458367 : Blo 2155435 5458367 := bstep (se 1 (by rfl) ⟨4093775, by rfl⟩ : syracuseStep 5458367 = 8187551) B8187551
theorem B3638911 : Blo 2155435 3638911 := bstep (se 1 (by rfl) ⟨2729183, by rfl⟩ : syracuseStep 3638911 = 5458367) B5458367
theorem B4851881 : Blo 2155435 4851881 := bstep (se 2 (by rfl) ⟨1819455, by rfl⟩ : syracuseStep 4851881 = 3638911) B3638911
theorem B3234587 : Blo 2155435 3234587 := bstep (se 1 (by rfl) ⟨2425940, by rfl⟩ : syracuseStep 3234587 = 4851881) B4851881
theorem B2156391 : Blo 2155435 2156391 := bstep (se 1 (by rfl) ⟨1617293, by rfl⟩ : syracuseStep 2156391 = 3234587) B3234587
theorem B2425945 : Blo 2155435 2425945 := bbase (se 2 (by rfl) ⟨909729, by rfl⟩ : syracuseStep 2425945 = 1819459) (by norm_num)
theorem B3234593 : Blo 2155435 3234593 := bstep (se 2 (by rfl) ⟨1212972, by rfl⟩ : syracuseStep 3234593 = 2425945) B2425945
theorem B2156395 : Blo 2155435 2156395 := bstep (se 1 (by rfl) ⟨1617296, by rfl⟩ : syracuseStep 2156395 = 3234593) B3234593
theorem B5181205 : Blo 2155435 5181205 := bbase (se 6 (by rfl) ⟨121434, by rfl⟩ : syracuseStep 5181205 = 242869) (by norm_num)
theorem B6908273 : Blo 2155435 6908273 := bstep (se 2 (by rfl) ⟨2590602, by rfl⟩ : syracuseStep 6908273 = 5181205) B5181205
theorem B4605515 : Blo 2155435 4605515 := bstep (se 1 (by rfl) ⟨3454136, by rfl⟩ : syracuseStep 4605515 = 6908273) B6908273
theorem B3070343 : Blo 2155435 3070343 := bstep (se 1 (by rfl) ⟨2302757, by rfl⟩ : syracuseStep 3070343 = 4605515) B4605515
theorem B8187581 : Blo 2155435 8187581 := bstep (se 3 (by rfl) ⟨1535171, by rfl⟩ : syracuseStep 8187581 = 3070343) B3070343
theorem B5458387 : Blo 2155435 5458387 := bstep (se 1 (by rfl) ⟨4093790, by rfl⟩ : syracuseStep 5458387 = 8187581) B8187581
theorem B7277849 : Blo 2155435 7277849 := bstep (se 2 (by rfl) ⟨2729193, by rfl⟩ : syracuseStep 7277849 = 5458387) B5458387
theorem B4851899 : Blo 2155435 4851899 := bstep (se 1 (by rfl) ⟨3638924, by rfl⟩ : syracuseStep 4851899 = 7277849) B7277849
theorem B3234599 : Blo 2155435 3234599 := bstep (se 1 (by rfl) ⟨2425949, by rfl⟩ : syracuseStep 3234599 = 4851899) B4851899
theorem B2156399 : Blo 2155435 2156399 := bstep (se 1 (by rfl) ⟨1617299, by rfl⟩ : syracuseStep 2156399 = 3234599) B3234599
theorem B3234605 : Blo 2155435 3234605 := bbase (se 3 (by rfl) ⟨606488, by rfl⟩ : syracuseStep 3234605 = 1212977) (by norm_num)
theorem B2156403 : Blo 2155435 2156403 := bstep (se 1 (by rfl) ⟨1617302, by rfl⟩ : syracuseStep 2156403 = 3234605) B3234605
theorem B4851917 : Blo 2155435 4851917 := bbase (se 3 (by rfl) ⟨909734, by rfl⟩ : syracuseStep 4851917 = 1819469) (by norm_num)
theorem B3234611 : Blo 2155435 3234611 := bstep (se 1 (by rfl) ⟨2425958, by rfl⟩ : syracuseStep 3234611 = 4851917) B4851917
theorem B2156407 : Blo 2155435 2156407 := bstep (se 1 (by rfl) ⟨1617305, by rfl⟩ : syracuseStep 2156407 = 3234611) B3234611
theorem B2729209 : Blo 2155435 2729209 := bbase (se 2 (by rfl) ⟨1023453, by rfl⟩ : syracuseStep 2729209 = 2046907) (by norm_num)
theorem B3638945 : Blo 2155435 3638945 := bstep (se 2 (by rfl) ⟨1364604, by rfl⟩ : syracuseStep 3638945 = 2729209) B2729209
theorem B2425963 : Blo 2155435 2425963 := bstep (se 1 (by rfl) ⟨1819472, by rfl⟩ : syracuseStep 2425963 = 3638945) B3638945
theorem B3234617 : Blo 2155435 3234617 := bstep (se 2 (by rfl) ⟨1212981, by rfl⟩ : syracuseStep 3234617 = 2425963) B2425963
theorem B2156411 : Blo 2155435 2156411 := bstep (se 1 (by rfl) ⟨1617308, by rfl⟩ : syracuseStep 2156411 = 3234617) B3234617
theorem B10362485 : Blo 2155435 10362485 := bbase (se 5 (by rfl) ⟨485741, by rfl⟩ : syracuseStep 10362485 = 971483) (by norm_num)
theorem B6908323 : Blo 2155435 6908323 := bstep (se 1 (by rfl) ⟨5181242, by rfl⟩ : syracuseStep 6908323 = 10362485) B10362485
theorem B9211097 : Blo 2155435 9211097 := bstep (se 2 (by rfl) ⟨3454161, by rfl⟩ : syracuseStep 9211097 = 6908323) B6908323
theorem B24562925 : Blo 2155435 24562925 := bstep (se 3 (by rfl) ⟨4605548, by rfl⟩ : syracuseStep 24562925 = 9211097) B9211097
theorem B16375283 : Blo 2155435 16375283 := bstep (se 1 (by rfl) ⟨12281462, by rfl⟩ : syracuseStep 16375283 = 24562925) B24562925
theorem B10916855 : Blo 2155435 10916855 := bstep (se 1 (by rfl) ⟨8187641, by rfl⟩ : syracuseStep 10916855 = 16375283) B16375283
theorem B7277903 : Blo 2155435 7277903 := bstep (se 1 (by rfl) ⟨5458427, by rfl⟩ : syracuseStep 7277903 = 10916855) B10916855
theorem B4851935 : Blo 2155435 4851935 := bstep (se 1 (by rfl) ⟨3638951, by rfl⟩ : syracuseStep 4851935 = 7277903) B7277903
theorem B3234623 : Blo 2155435 3234623 := bstep (se 1 (by rfl) ⟨2425967, by rfl⟩ : syracuseStep 3234623 = 4851935) B4851935
theorem B2156415 : Blo 2155435 2156415 := bstep (se 1 (by rfl) ⟨1617311, by rfl⟩ : syracuseStep 2156415 = 3234623) B3234623
theorem B3234629 : Blo 2155435 3234629 := bbase (se 4 (by rfl) ⟨303246, by rfl⟩ : syracuseStep 3234629 = 606493) (by norm_num)
theorem B2156419 : Blo 2155435 2156419 := bstep (se 1 (by rfl) ⟨1617314, by rfl⟩ : syracuseStep 2156419 = 3234629) B3234629
theorem B3638965 : Blo 2155435 3638965 := bbase (se 5 (by rfl) ⟨170576, by rfl⟩ : syracuseStep 3638965 = 341153) (by norm_num)
theorem B4851953 : Blo 2155435 4851953 := bstep (se 2 (by rfl) ⟨1819482, by rfl⟩ : syracuseStep 4851953 = 3638965) B3638965
theorem B3234635 : Blo 2155435 3234635 := bstep (se 1 (by rfl) ⟨2425976, by rfl⟩ : syracuseStep 3234635 = 4851953) B4851953
theorem B2156423 : Blo 2155435 2156423 := bstep (se 1 (by rfl) ⟨1617317, by rfl⟩ : syracuseStep 2156423 = 3234635) B3234635
theorem B2425981 : Blo 2155435 2425981 := bbase (se 3 (by rfl) ⟨454871, by rfl⟩ : syracuseStep 2425981 = 909743) (by norm_num)
theorem B3234641 : Blo 2155435 3234641 := bstep (se 2 (by rfl) ⟨1212990, by rfl⟩ : syracuseStep 3234641 = 2425981) B2425981
theorem B2156427 : Blo 2155435 2156427 := bstep (se 1 (by rfl) ⟨1617320, by rfl⟩ : syracuseStep 2156427 = 3234641) B3234641
theorem B7277957 : Blo 2155435 7277957 := bbase (se 4 (by rfl) ⟨682308, by rfl⟩ : syracuseStep 7277957 = 1364617) (by norm_num)
theorem B4851971 : Blo 2155435 4851971 := bstep (se 1 (by rfl) ⟨3638978, by rfl⟩ : syracuseStep 4851971 = 7277957) B7277957
theorem B3234647 : Blo 2155435 3234647 := bstep (se 1 (by rfl) ⟨2425985, by rfl⟩ : syracuseStep 3234647 = 4851971) B4851971
theorem B2156431 : Blo 2155435 2156431 := bstep (se 1 (by rfl) ⟨1617323, by rfl⟩ : syracuseStep 2156431 = 3234647) B3234647
theorem B3234653 : Blo 2155435 3234653 := bbase (se 3 (by rfl) ⟨606497, by rfl⟩ : syracuseStep 3234653 = 1212995) (by norm_num)
theorem B2156435 : Blo 2155435 2156435 := bstep (se 1 (by rfl) ⟨1617326, by rfl⟩ : syracuseStep 2156435 = 3234653) B3234653
theorem B4851989 : Blo 2155435 4851989 := bbase (se 6 (by rfl) ⟨113718, by rfl⟩ : syracuseStep 4851989 = 227437) (by norm_num)
theorem B3234659 : Blo 2155435 3234659 := bstep (se 1 (by rfl) ⟨2425994, by rfl⟩ : syracuseStep 3234659 = 4851989) B4851989
theorem B2156439 : Blo 2155435 2156439 := bstep (se 1 (by rfl) ⟨1617329, by rfl⟩ : syracuseStep 2156439 = 3234659) B3234659
theorem B8187749 : Blo 2155435 8187749 := bbase (se 4 (by rfl) ⟨767601, by rfl⟩ : syracuseStep 8187749 = 1535203) (by norm_num)
theorem B5458499 : Blo 2155435 5458499 := bstep (se 1 (by rfl) ⟨4093874, by rfl⟩ : syracuseStep 5458499 = 8187749) B8187749
theorem B3638999 : Blo 2155435 3638999 := bstep (se 1 (by rfl) ⟨2729249, by rfl⟩ : syracuseStep 3638999 = 5458499) B5458499
theorem B2425999 : Blo 2155435 2425999 := bstep (se 1 (by rfl) ⟨1819499, by rfl⟩ : syracuseStep 2425999 = 3638999) B3638999
theorem B3234665 : Blo 2155435 3234665 := bstep (se 2 (by rfl) ⟨1212999, by rfl⟩ : syracuseStep 3234665 = 2425999) B2425999
theorem B2156443 : Blo 2155435 2156443 := bstep (se 1 (by rfl) ⟨1617332, by rfl⟩ : syracuseStep 2156443 = 3234665) B3234665
theorem B3454213 : Blo 2155435 3454213 := bbase (se 4 (by rfl) ⟨323832, by rfl⟩ : syracuseStep 3454213 = 647665) (by norm_num)
theorem B4605617 : Blo 2155435 4605617 := bstep (se 2 (by rfl) ⟨1727106, by rfl⟩ : syracuseStep 4605617 = 3454213) B3454213
theorem B12281645 : Blo 2155435 12281645 := bstep (se 3 (by rfl) ⟨2302808, by rfl⟩ : syracuseStep 12281645 = 4605617) B4605617
theorem B8187763 : Blo 2155435 8187763 := bstep (se 1 (by rfl) ⟨6140822, by rfl⟩ : syracuseStep 8187763 = 12281645) B12281645
theorem B10917017 : Blo 2155435 10917017 := bstep (se 2 (by rfl) ⟨4093881, by rfl⟩ : syracuseStep 10917017 = 8187763) B8187763
theorem B7278011 : Blo 2155435 7278011 := bstep (se 1 (by rfl) ⟨5458508, by rfl⟩ : syracuseStep 7278011 = 10917017) B10917017
theorem B4852007 : Blo 2155435 4852007 := bstep (se 1 (by rfl) ⟨3639005, by rfl⟩ : syracuseStep 4852007 = 7278011) B7278011
theorem B3234671 : Blo 2155435 3234671 := bstep (se 1 (by rfl) ⟨2426003, by rfl⟩ : syracuseStep 3234671 = 4852007) B4852007
theorem B2156447 : Blo 2155435 2156447 := bstep (se 1 (by rfl) ⟨1617335, by rfl⟩ : syracuseStep 2156447 = 3234671) B3234671
theorem B3234677 : Blo 2155435 3234677 := bbase (se 5 (by rfl) ⟨151625, by rfl⟩ : syracuseStep 3234677 = 303251) (by norm_num)
theorem B2156451 : Blo 2155435 2156451 := bstep (se 1 (by rfl) ⟨1617338, by rfl⟩ : syracuseStep 2156451 = 3234677) B3234677
theorem B6908453 : Blo 2155435 6908453 := bbase (se 4 (by rfl) ⟨647667, by rfl⟩ : syracuseStep 6908453 = 1295335) (by norm_num)
theorem B4605635 : Blo 2155435 4605635 := bstep (se 1 (by rfl) ⟨3454226, by rfl⟩ : syracuseStep 4605635 = 6908453) B6908453
theorem B3070423 : Blo 2155435 3070423 := bstep (se 1 (by rfl) ⟨2302817, by rfl⟩ : syracuseStep 3070423 = 4605635) B4605635
theorem B4093897 : Blo 2155435 4093897 := bstep (se 2 (by rfl) ⟨1535211, by rfl⟩ : syracuseStep 4093897 = 3070423) B3070423
theorem B5458529 : Blo 2155435 5458529 := bstep (se 2 (by rfl) ⟨2046948, by rfl⟩ : syracuseStep 5458529 = 4093897) B4093897
theorem B3639019 : Blo 2155435 3639019 := bstep (se 1 (by rfl) ⟨2729264, by rfl⟩ : syracuseStep 3639019 = 5458529) B5458529
theorem B4852025 : Blo 2155435 4852025 := bstep (se 2 (by rfl) ⟨1819509, by rfl⟩ : syracuseStep 4852025 = 3639019) B3639019
theorem B3234683 : Blo 2155435 3234683 := bstep (se 1 (by rfl) ⟨2426012, by rfl⟩ : syracuseStep 3234683 = 4852025) B4852025
theorem B2156455 : Blo 2155435 2156455 := bstep (se 1 (by rfl) ⟨1617341, by rfl⟩ : syracuseStep 2156455 = 3234683) B3234683
theorem B2426017 : Blo 2155435 2426017 := bbase (se 2 (by rfl) ⟨909756, by rfl⟩ : syracuseStep 2426017 = 1819513) (by norm_num)
theorem B3234689 : Blo 2155435 3234689 := bstep (se 2 (by rfl) ⟨1213008, by rfl⟩ : syracuseStep 3234689 = 2426017) B2426017
theorem B2156459 : Blo 2155435 2156459 := bstep (se 1 (by rfl) ⟨1617344, by rfl⟩ : syracuseStep 2156459 = 3234689) B3234689
theorem B5458549 : Blo 2155435 5458549 := bbase (se 5 (by rfl) ⟨255869, by rfl⟩ : syracuseStep 5458549 = 511739) (by norm_num)
theorem B7278065 : Blo 2155435 7278065 := bstep (se 2 (by rfl) ⟨2729274, by rfl⟩ : syracuseStep 7278065 = 5458549) B5458549
theorem B4852043 : Blo 2155435 4852043 := bstep (se 1 (by rfl) ⟨3639032, by rfl⟩ : syracuseStep 4852043 = 7278065) B7278065
theorem B3234695 : Blo 2155435 3234695 := bstep (se 1 (by rfl) ⟨2426021, by rfl⟩ : syracuseStep 3234695 = 4852043) B4852043
theorem B2156463 : Blo 2155435 2156463 := bstep (se 1 (by rfl) ⟨1617347, by rfl⟩ : syracuseStep 2156463 = 3234695) B3234695
theorem B3234701 : Blo 2155435 3234701 := bbase (se 3 (by rfl) ⟨606506, by rfl⟩ : syracuseStep 3234701 = 1213013) (by norm_num)
theorem B2156467 : Blo 2155435 2156467 := bstep (se 1 (by rfl) ⟨1617350, by rfl⟩ : syracuseStep 2156467 = 3234701) B3234701
theorem B4852061 : Blo 2155435 4852061 := bbase (se 3 (by rfl) ⟨909761, by rfl⟩ : syracuseStep 4852061 = 1819523) (by norm_num)
theorem B3234707 : Blo 2155435 3234707 := bstep (se 1 (by rfl) ⟨2426030, by rfl⟩ : syracuseStep 3234707 = 4852061) B4852061
theorem B2156471 : Blo 2155435 2156471 := bstep (se 1 (by rfl) ⟨1617353, by rfl⟩ : syracuseStep 2156471 = 3234707) B3234707
theorem B3639053 : Blo 2155435 3639053 := bbase (se 3 (by rfl) ⟨682322, by rfl⟩ : syracuseStep 3639053 = 1364645) (by norm_num)
theorem B2426035 : Blo 2155435 2426035 := bstep (se 1 (by rfl) ⟨1819526, by rfl⟩ : syracuseStep 2426035 = 3639053) B3639053
theorem B3234713 : Blo 2155435 3234713 := bstep (se 2 (by rfl) ⟨1213017, by rfl⟩ : syracuseStep 3234713 = 2426035) B2426035
theorem B2156475 : Blo 2155435 2156475 := bstep (se 1 (by rfl) ⟨1617356, by rfl⟩ : syracuseStep 2156475 = 3234713) B3234713
theorem B18422741 : Blo 2155435 18422741 := bbase (se 7 (by rfl) ⟨215891, by rfl⟩ : syracuseStep 18422741 = 431783) (by norm_num)
theorem B12281827 : Blo 2155435 12281827 := bstep (se 1 (by rfl) ⟨9211370, by rfl⟩ : syracuseStep 12281827 = 18422741) B18422741
theorem B16375769 : Blo 2155435 16375769 := bstep (se 2 (by rfl) ⟨6140913, by rfl⟩ : syracuseStep 16375769 = 12281827) B12281827
theorem B10917179 : Blo 2155435 10917179 := bstep (se 1 (by rfl) ⟨8187884, by rfl⟩ : syracuseStep 10917179 = 16375769) B16375769
theorem B7278119 : Blo 2155435 7278119 := bstep (se 1 (by rfl) ⟨5458589, by rfl⟩ : syracuseStep 7278119 = 10917179) B10917179
theorem B4852079 : Blo 2155435 4852079 := bstep (se 1 (by rfl) ⟨3639059, by rfl⟩ : syracuseStep 4852079 = 7278119) B7278119
theorem B3234719 : Blo 2155435 3234719 := bstep (se 1 (by rfl) ⟨2426039, by rfl⟩ : syracuseStep 3234719 = 4852079) B4852079
theorem B2156479 : Blo 2155435 2156479 := bstep (se 1 (by rfl) ⟨1617359, by rfl⟩ : syracuseStep 2156479 = 3234719) B3234719
theorem B3234725 : Blo 2155435 3234725 := bbase (se 4 (by rfl) ⟨303255, by rfl⟩ : syracuseStep 3234725 = 606511) (by norm_num)
theorem B2156483 : Blo 2155435 2156483 := bstep (se 1 (by rfl) ⟨1617362, by rfl⟩ : syracuseStep 2156483 = 3234725) B3234725
theorem B2729305 : Blo 2155435 2729305 := bbase (se 2 (by rfl) ⟨1023489, by rfl⟩ : syracuseStep 2729305 = 2046979) (by norm_num)
theorem B3639073 : Blo 2155435 3639073 := bstep (se 2 (by rfl) ⟨1364652, by rfl⟩ : syracuseStep 3639073 = 2729305) B2729305
theorem B4852097 : Blo 2155435 4852097 := bstep (se 2 (by rfl) ⟨1819536, by rfl⟩ : syracuseStep 4852097 = 3639073) B3639073
theorem B3234731 : Blo 2155435 3234731 := bstep (se 1 (by rfl) ⟨2426048, by rfl⟩ : syracuseStep 3234731 = 4852097) B4852097
theorem B2156487 : Blo 2155435 2156487 := bstep (se 1 (by rfl) ⟨1617365, by rfl⟩ : syracuseStep 2156487 = 3234731) B3234731
theorem B2426053 : Blo 2155435 2426053 := bbase (se 4 (by rfl) ⟨227442, by rfl⟩ : syracuseStep 2426053 = 454885) (by norm_num)
theorem B3234737 : Blo 2155435 3234737 := bstep (se 2 (by rfl) ⟨1213026, by rfl⟩ : syracuseStep 3234737 = 2426053) B2426053
theorem B2156491 : Blo 2155435 2156491 := bstep (se 1 (by rfl) ⟨1617368, by rfl⟩ : syracuseStep 2156491 = 3234737) B3234737
theorem B4093973 : Blo 2155435 4093973 := bbase (se 6 (by rfl) ⟨95952, by rfl⟩ : syracuseStep 4093973 = 191905) (by norm_num)
theorem B2729315 : Blo 2155435 2729315 := bstep (se 1 (by rfl) ⟨2046986, by rfl⟩ : syracuseStep 2729315 = 4093973) B4093973
theorem B7278173 : Blo 2155435 7278173 := bstep (se 3 (by rfl) ⟨1364657, by rfl⟩ : syracuseStep 7278173 = 2729315) B2729315
theorem B4852115 : Blo 2155435 4852115 := bstep (se 1 (by rfl) ⟨3639086, by rfl⟩ : syracuseStep 4852115 = 7278173) B7278173
theorem B3234743 : Blo 2155435 3234743 := bstep (se 1 (by rfl) ⟨2426057, by rfl⟩ : syracuseStep 3234743 = 4852115) B4852115
theorem B2156495 : Blo 2155435 2156495 := bstep (se 1 (by rfl) ⟨1617371, by rfl⟩ : syracuseStep 2156495 = 3234743) B3234743
theorem B3234749 : Blo 2155435 3234749 := bbase (se 3 (by rfl) ⟨606515, by rfl⟩ : syracuseStep 3234749 = 1213031) (by norm_num)
theorem B2156499 : Blo 2155435 2156499 := bstep (se 1 (by rfl) ⟨1617374, by rfl⟩ : syracuseStep 2156499 = 3234749) B3234749
theorem B4852133 : Blo 2155435 4852133 := bbase (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) (by norm_num)
theorem B3234755 : Blo 2155435 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B2156503 : Blo 2155435 2156503 := bstep (se 1 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 2156503 = 3234755) B3234755
theorem B5458661 : Blo 2155435 5458661 := bbase (se 4 (by rfl) ⟨511749, by rfl⟩ : syracuseStep 5458661 = 1023499) (by norm_num)
theorem B3639107 : Blo 2155435 3639107 := bstep (se 1 (by rfl) ⟨2729330, by rfl⟩ : syracuseStep 3639107 = 5458661) B5458661
theorem B2426071 : Blo 2155435 2426071 := bstep (se 1 (by rfl) ⟨1819553, by rfl⟩ : syracuseStep 2426071 = 3639107) B3639107
theorem B3234761 : Blo 2155435 3234761 := bstep (se 2 (by rfl) ⟨1213035, by rfl⟩ : syracuseStep 3234761 = 2426071) B2426071
theorem B2156507 : Blo 2155435 2156507 := bstep (se 1 (by rfl) ⟨1617380, by rfl⟩ : syracuseStep 2156507 = 3234761) B3234761
theorem B2302877 : Blo 2155435 2302877 := bbase (se 3 (by rfl) ⟨431789, by rfl⟩ : syracuseStep 2302877 = 863579) (by norm_num)
theorem B6141005 : Blo 2155435 6141005 := bstep (se 3 (by rfl) ⟨1151438, by rfl⟩ : syracuseStep 6141005 = 2302877) B2302877
theorem B4094003 : Blo 2155435 4094003 := bstep (se 1 (by rfl) ⟨3070502, by rfl⟩ : syracuseStep 4094003 = 6141005) B6141005
theorem B10917341 : Blo 2155435 10917341 := bstep (se 3 (by rfl) ⟨2047001, by rfl⟩ : syracuseStep 10917341 = 4094003) B4094003
theorem B7278227 : Blo 2155435 7278227 := bstep (se 1 (by rfl) ⟨5458670, by rfl⟩ : syracuseStep 7278227 = 10917341) B10917341
theorem B4852151 : Blo 2155435 4852151 := bstep (se 1 (by rfl) ⟨3639113, by rfl⟩ : syracuseStep 4852151 = 7278227) B7278227
theorem B3234767 : Blo 2155435 3234767 := bstep (se 1 (by rfl) ⟨2426075, by rfl⟩ : syracuseStep 3234767 = 4852151) B4852151
theorem B2156511 : Blo 2155435 2156511 := bstep (se 1 (by rfl) ⟨1617383, by rfl⟩ : syracuseStep 2156511 = 3234767) B3234767
theorem B3234773 : Blo 2155435 3234773 := bbase (se 7 (by rfl) ⟨37907, by rfl⟩ : syracuseStep 3234773 = 75815) (by norm_num)
theorem B2156515 : Blo 2155435 2156515 := bstep (se 1 (by rfl) ⟨1617386, by rfl⟩ : syracuseStep 2156515 = 3234773) B3234773
theorem B8188037 : Blo 2155435 8188037 := bbase (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) (by norm_num)
theorem B5458691 : Blo 2155435 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B3639127 : Blo 2155435 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B4852169 : Blo 2155435 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B3234779 : Blo 2155435 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B2156519 : Blo 2155435 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B2426089 : Blo 2155435 2426089 := bbase (se 2 (by rfl) ⟨909783, by rfl⟩ : syracuseStep 2426089 = 1819567) (by norm_num)
theorem B3234785 : Blo 2155435 3234785 := bstep (se 2 (by rfl) ⟨1213044, by rfl⟩ : syracuseStep 3234785 = 2426089) B2426089
theorem B2156523 : Blo 2155435 2156523 := bstep (se 1 (by rfl) ⟨1617392, by rfl⟩ : syracuseStep 2156523 = 3234785) B3234785
theorem B12282101 : Blo 2155435 12282101 := bbase (se 5 (by rfl) ⟨575723, by rfl⟩ : syracuseStep 12282101 = 1151447) (by norm_num)
theorem B8188067 : Blo 2155435 8188067 := bstep (se 1 (by rfl) ⟨6141050, by rfl⟩ : syracuseStep 8188067 = 12282101) B12282101
theorem B5458711 : Blo 2155435 5458711 := bstep (se 1 (by rfl) ⟨4094033, by rfl⟩ : syracuseStep 5458711 = 8188067) B8188067
theorem B7278281 : Blo 2155435 7278281 := bstep (se 2 (by rfl) ⟨2729355, by rfl⟩ : syracuseStep 7278281 = 5458711) B5458711
theorem B4852187 : Blo 2155435 4852187 := bstep (se 1 (by rfl) ⟨3639140, by rfl⟩ : syracuseStep 4852187 = 7278281) B7278281
theorem B3234791 : Blo 2155435 3234791 := bstep (se 1 (by rfl) ⟨2426093, by rfl⟩ : syracuseStep 3234791 = 4852187) B4852187
theorem B2156527 : Blo 2155435 2156527 := bstep (se 1 (by rfl) ⟨1617395, by rfl⟩ : syracuseStep 2156527 = 3234791) B3234791
theorem B3234797 : Blo 2155435 3234797 := bbase (se 3 (by rfl) ⟨606524, by rfl⟩ : syracuseStep 3234797 = 1213049) (by norm_num)
theorem B2156531 : Blo 2155435 2156531 := bstep (se 1 (by rfl) ⟨1617398, by rfl⟩ : syracuseStep 2156531 = 3234797) B3234797
theorem B4852205 : Blo 2155435 4852205 := bbase (se 3 (by rfl) ⟨909788, by rfl⟩ : syracuseStep 4852205 = 1819577) (by norm_num)
theorem B3234803 : Blo 2155435 3234803 := bstep (se 1 (by rfl) ⟨2426102, by rfl⟩ : syracuseStep 3234803 = 4852205) B4852205
theorem B2156535 : Blo 2155435 2156535 := bstep (se 1 (by rfl) ⟨1617401, by rfl⟩ : syracuseStep 2156535 = 3234803) B3234803
theorem B3886157 : Blo 2155435 3886157 := bbase (se 3 (by rfl) ⟨728654, by rfl⟩ : syracuseStep 3886157 = 1457309) (by norm_num)
theorem B10363085 : Blo 2155435 10363085 := bstep (se 3 (by rfl) ⟨1943078, by rfl⟩ : syracuseStep 10363085 = 3886157) B3886157
theorem B6908723 : Blo 2155435 6908723 := bstep (se 1 (by rfl) ⟨5181542, by rfl⟩ : syracuseStep 6908723 = 10363085) B10363085
theorem B4605815 : Blo 2155435 4605815 := bstep (se 1 (by rfl) ⟨3454361, by rfl⟩ : syracuseStep 4605815 = 6908723) B6908723
theorem B3070543 : Blo 2155435 3070543 := bstep (se 1 (by rfl) ⟨2302907, by rfl⟩ : syracuseStep 3070543 = 4605815) B4605815
theorem B4094057 : Blo 2155435 4094057 := bstep (se 2 (by rfl) ⟨1535271, by rfl⟩ : syracuseStep 4094057 = 3070543) B3070543
theorem B2729371 : Blo 2155435 2729371 := bstep (se 1 (by rfl) ⟨2047028, by rfl⟩ : syracuseStep 2729371 = 4094057) B4094057
theorem B3639161 : Blo 2155435 3639161 := bstep (se 2 (by rfl) ⟨1364685, by rfl⟩ : syracuseStep 3639161 = 2729371) B2729371
theorem B2426107 : Blo 2155435 2426107 := bstep (se 1 (by rfl) ⟨1819580, by rfl⟩ : syracuseStep 2426107 = 3639161) B3639161
theorem B3234809 : Blo 2155435 3234809 := bstep (se 2 (by rfl) ⟨1213053, by rfl⟩ : syracuseStep 3234809 = 2426107) B2426107
theorem B2156539 : Blo 2155435 2156539 := bstep (se 1 (by rfl) ⟨1617404, by rfl⟩ : syracuseStep 2156539 = 3234809) B3234809
theorem B4668661 : Blo 2155435 4668661 := bbase (se 5 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 4668661 = 437687) (by norm_num)
theorem B6224881 : Blo 2155435 6224881 := bstep (se 2 (by rfl) ⟨2334330, by rfl⟩ : syracuseStep 6224881 = 4668661) B4668661
theorem B8299841 : Blo 2155435 8299841 := bstep (se 2 (by rfl) ⟨3112440, by rfl⟩ : syracuseStep 8299841 = 6224881) B6224881
theorem B22132909 : Blo 2155435 22132909 := bstep (se 3 (by rfl) ⟨4149920, by rfl⟩ : syracuseStep 22132909 = 8299841) B8299841
theorem B118042181 : Blo 2155435 118042181 := bstep (se 4 (by rfl) ⟨11066454, by rfl⟩ : syracuseStep 118042181 = 22132909) B22132909
theorem B78694787 : Blo 2155435 78694787 := bstep (se 1 (by rfl) ⟨59021090, by rfl⟩ : syracuseStep 78694787 = 118042181) B118042181
theorem B209852765 : Blo 2155435 209852765 := bstep (se 3 (by rfl) ⟨39347393, by rfl⟩ : syracuseStep 209852765 = 78694787) B78694787
theorem B139901843 : Blo 2155435 139901843 := bstep (se 1 (by rfl) ⟨104926382, by rfl⟩ : syracuseStep 139901843 = 209852765) B209852765
theorem B93267895 : Blo 2155435 93267895 := bstep (se 1 (by rfl) ⟨69950921, by rfl⟩ : syracuseStep 93267895 = 139901843) B139901843
theorem B124357193 : Blo 2155435 124357193 := bstep (se 2 (by rfl) ⟨46633947, by rfl⟩ : syracuseStep 124357193 = 93267895) B93267895
theorem B82904795 : Blo 2155435 82904795 := bstep (se 1 (by rfl) ⟨62178596, by rfl⟩ : syracuseStep 82904795 = 124357193) B124357193
theorem B55269863 : Blo 2155435 55269863 := bstep (se 1 (by rfl) ⟨41452397, by rfl⟩ : syracuseStep 55269863 = 82904795) B82904795
theorem B36846575 : Blo 2155435 36846575 := bstep (se 1 (by rfl) ⟨27634931, by rfl⟩ : syracuseStep 36846575 = 55269863) B55269863
theorem B24564383 : Blo 2155435 24564383 := bstep (se 1 (by rfl) ⟨18423287, by rfl⟩ : syracuseStep 24564383 = 36846575) B36846575
theorem B16376255 : Blo 2155435 16376255 := bstep (se 1 (by rfl) ⟨12282191, by rfl⟩ : syracuseStep 16376255 = 24564383) B24564383
theorem B10917503 : Blo 2155435 10917503 := bstep (se 1 (by rfl) ⟨8188127, by rfl⟩ : syracuseStep 10917503 = 16376255) B16376255
theorem B7278335 : Blo 2155435 7278335 := bstep (se 1 (by rfl) ⟨5458751, by rfl⟩ : syracuseStep 7278335 = 10917503) B10917503
theorem B4852223 : Blo 2155435 4852223 := bstep (se 1 (by rfl) ⟨3639167, by rfl⟩ : syracuseStep 4852223 = 7278335) B7278335
theorem B3234815 : Blo 2155435 3234815 := bstep (se 1 (by rfl) ⟨2426111, by rfl⟩ : syracuseStep 3234815 = 4852223) B4852223
theorem B2156543 : Blo 2155435 2156543 := bstep (se 1 (by rfl) ⟨1617407, by rfl⟩ : syracuseStep 2156543 = 3234815) B3234815
theorem B3234821 : Blo 2155435 3234821 := bbase (se 4 (by rfl) ⟨303264, by rfl⟩ : syracuseStep 3234821 = 606529) (by norm_num)
theorem B2156547 : Blo 2155435 2156547 := bstep (se 1 (by rfl) ⟨1617410, by rfl⟩ : syracuseStep 2156547 = 3234821) B3234821
theorem B3639181 : Blo 2155435 3639181 := bbase (se 3 (by rfl) ⟨682346, by rfl⟩ : syracuseStep 3639181 = 1364693) (by norm_num)
theorem B4852241 : Blo 2155435 4852241 := bstep (se 2 (by rfl) ⟨1819590, by rfl⟩ : syracuseStep 4852241 = 3639181) B3639181
theorem B3234827 : Blo 2155435 3234827 := bstep (se 1 (by rfl) ⟨2426120, by rfl⟩ : syracuseStep 3234827 = 4852241) B4852241
theorem B2156551 : Blo 2155435 2156551 := bstep (se 1 (by rfl) ⟨1617413, by rfl⟩ : syracuseStep 2156551 = 3234827) B3234827
theorem B2426125 : Blo 2155435 2426125 := bbase (se 3 (by rfl) ⟨454898, by rfl⟩ : syracuseStep 2426125 = 909797) (by norm_num)
theorem B3234833 : Blo 2155435 3234833 := bstep (se 2 (by rfl) ⟨1213062, by rfl⟩ : syracuseStep 3234833 = 2426125) B2426125
theorem B2156555 : Blo 2155435 2156555 := bstep (se 1 (by rfl) ⟨1617416, by rfl⟩ : syracuseStep 2156555 = 3234833) B3234833
theorem B7278389 : Blo 2155435 7278389 := bbase (se 5 (by rfl) ⟨341174, by rfl⟩ : syracuseStep 7278389 = 682349) (by norm_num)
theorem B4852259 : Blo 2155435 4852259 := bstep (se 1 (by rfl) ⟨3639194, by rfl⟩ : syracuseStep 4852259 = 7278389) B7278389
theorem B3234839 : Blo 2155435 3234839 := bstep (se 1 (by rfl) ⟨2426129, by rfl⟩ : syracuseStep 3234839 = 4852259) B4852259
theorem B2156559 : Blo 2155435 2156559 := bstep (se 1 (by rfl) ⟨1617419, by rfl⟩ : syracuseStep 2156559 = 3234839) B3234839
theorem B3234845 : Blo 2155435 3234845 := bbase (se 3 (by rfl) ⟨606533, by rfl⟩ : syracuseStep 3234845 = 1213067) (by norm_num)
theorem B2156563 : Blo 2155435 2156563 := bstep (se 1 (by rfl) ⟨1617422, by rfl⟩ : syracuseStep 2156563 = 3234845) B3234845
theorem B4852277 : Blo 2155435 4852277 := bbase (se 5 (by rfl) ⟨227450, by rfl⟩ : syracuseStep 4852277 = 454901) (by norm_num)
theorem B3234851 : Blo 2155435 3234851 := bstep (se 1 (by rfl) ⟨2426138, by rfl⟩ : syracuseStep 3234851 = 4852277) B4852277
theorem B2156567 : Blo 2155435 2156567 := bstep (se 1 (by rfl) ⟨1617425, by rfl⟩ : syracuseStep 2156567 = 3234851) B3234851
theorem B9211765 : Blo 2155435 9211765 := bbase (se 5 (by rfl) ⟨431801, by rfl⟩ : syracuseStep 9211765 = 863603) (by norm_num)
theorem B12282353 : Blo 2155435 12282353 := bstep (se 2 (by rfl) ⟨4605882, by rfl⟩ : syracuseStep 12282353 = 9211765) B9211765
theorem B8188235 : Blo 2155435 8188235 := bstep (se 1 (by rfl) ⟨6141176, by rfl⟩ : syracuseStep 8188235 = 12282353) B12282353
theorem B5458823 : Blo 2155435 5458823 := bstep (se 1 (by rfl) ⟨4094117, by rfl⟩ : syracuseStep 5458823 = 8188235) B8188235
theorem B3639215 : Blo 2155435 3639215 := bstep (se 1 (by rfl) ⟨2729411, by rfl⟩ : syracuseStep 3639215 = 5458823) B5458823
theorem B2426143 : Blo 2155435 2426143 := bstep (se 1 (by rfl) ⟨1819607, by rfl⟩ : syracuseStep 2426143 = 3639215) B3639215
theorem B3234857 : Blo 2155435 3234857 := bstep (se 2 (by rfl) ⟨1213071, by rfl⟩ : syracuseStep 3234857 = 2426143) B2426143
theorem B2156571 : Blo 2155435 2156571 := bstep (se 1 (by rfl) ⟨1617428, by rfl⟩ : syracuseStep 2156571 = 3234857) B3234857
theorem B9211781 : Blo 2155435 9211781 := bbase (se 4 (by rfl) ⟨863604, by rfl⟩ : syracuseStep 9211781 = 1727209) (by norm_num)
theorem B6141187 : Blo 2155435 6141187 := bstep (se 1 (by rfl) ⟨4605890, by rfl⟩ : syracuseStep 6141187 = 9211781) B9211781
theorem B8188249 : Blo 2155435 8188249 := bstep (se 2 (by rfl) ⟨3070593, by rfl⟩ : syracuseStep 8188249 = 6141187) B6141187
theorem B10917665 : Blo 2155435 10917665 := bstep (se 2 (by rfl) ⟨4094124, by rfl⟩ : syracuseStep 10917665 = 8188249) B8188249
theorem B7278443 : Blo 2155435 7278443 := bstep (se 1 (by rfl) ⟨5458832, by rfl⟩ : syracuseStep 7278443 = 10917665) B10917665
theorem B4852295 : Blo 2155435 4852295 := bstep (se 1 (by rfl) ⟨3639221, by rfl⟩ : syracuseStep 4852295 = 7278443) B7278443
theorem B3234863 : Blo 2155435 3234863 := bstep (se 1 (by rfl) ⟨2426147, by rfl⟩ : syracuseStep 3234863 = 4852295) B4852295
theorem B2156575 : Blo 2155435 2156575 := bstep (se 1 (by rfl) ⟨1617431, by rfl⟩ : syracuseStep 2156575 = 3234863) B3234863
theorem B3234869 : Blo 2155435 3234869 := bbase (se 5 (by rfl) ⟨151634, by rfl⟩ : syracuseStep 3234869 = 303269) (by norm_num)
theorem B2156579 : Blo 2155435 2156579 := bstep (se 1 (by rfl) ⟨1617434, by rfl⟩ : syracuseStep 2156579 = 3234869) B3234869
theorem B5458853 : Blo 2155435 5458853 := bbase (se 4 (by rfl) ⟨511767, by rfl⟩ : syracuseStep 5458853 = 1023535) (by norm_num)
theorem B3639235 : Blo 2155435 3639235 := bstep (se 1 (by rfl) ⟨2729426, by rfl⟩ : syracuseStep 3639235 = 5458853) B5458853
theorem B4852313 : Blo 2155435 4852313 := bstep (se 2 (by rfl) ⟨1819617, by rfl⟩ : syracuseStep 4852313 = 3639235) B3639235
theorem B3234875 : Blo 2155435 3234875 := bstep (se 1 (by rfl) ⟨2426156, by rfl⟩ : syracuseStep 3234875 = 4852313) B4852313
theorem B2156583 : Blo 2155435 2156583 := bstep (se 1 (by rfl) ⟨1617437, by rfl⟩ : syracuseStep 2156583 = 3234875) B3234875
theorem B2426161 : Blo 2155435 2426161 := bbase (se 2 (by rfl) ⟨909810, by rfl⟩ : syracuseStep 2426161 = 1819621) (by norm_num)
theorem B3234881 : Blo 2155435 3234881 := bstep (se 2 (by rfl) ⟨1213080, by rfl⟩ : syracuseStep 3234881 = 2426161) B2426161
theorem B2156587 : Blo 2155435 2156587 := bstep (se 1 (by rfl) ⟨1617440, by rfl⟩ : syracuseStep 2156587 = 3234881) B3234881
theorem B4605925 : Blo 2155435 4605925 := bbase (se 4 (by rfl) ⟨431805, by rfl⟩ : syracuseStep 4605925 = 863611) (by norm_num)
theorem B6141233 : Blo 2155435 6141233 := bstep (se 2 (by rfl) ⟨2302962, by rfl⟩ : syracuseStep 6141233 = 4605925) B4605925
theorem B4094155 : Blo 2155435 4094155 := bstep (se 1 (by rfl) ⟨3070616, by rfl⟩ : syracuseStep 4094155 = 6141233) B6141233
theorem B5458873 : Blo 2155435 5458873 := bstep (se 2 (by rfl) ⟨2047077, by rfl⟩ : syracuseStep 5458873 = 4094155) B4094155
theorem B7278497 : Blo 2155435 7278497 := bstep (se 2 (by rfl) ⟨2729436, by rfl⟩ : syracuseStep 7278497 = 5458873) B5458873
theorem B4852331 : Blo 2155435 4852331 := bstep (se 1 (by rfl) ⟨3639248, by rfl⟩ : syracuseStep 4852331 = 7278497) B7278497
theorem B3234887 : Blo 2155435 3234887 := bstep (se 1 (by rfl) ⟨2426165, by rfl⟩ : syracuseStep 3234887 = 4852331) B4852331
theorem B2156591 : Blo 2155435 2156591 := bstep (se 1 (by rfl) ⟨1617443, by rfl⟩ : syracuseStep 2156591 = 3234887) B3234887
theorem B3234893 : Blo 2155435 3234893 := bbase (se 3 (by rfl) ⟨606542, by rfl⟩ : syracuseStep 3234893 = 1213085) (by norm_num)
theorem B2156595 : Blo 2155435 2156595 := bstep (se 1 (by rfl) ⟨1617446, by rfl⟩ : syracuseStep 2156595 = 3234893) B3234893
theorem B4852349 : Blo 2155435 4852349 := bbase (se 3 (by rfl) ⟨909815, by rfl⟩ : syracuseStep 4852349 = 1819631) (by norm_num)
theorem B3234899 : Blo 2155435 3234899 := bstep (se 1 (by rfl) ⟨2426174, by rfl⟩ : syracuseStep 3234899 = 4852349) B4852349
theorem B2156599 : Blo 2155435 2156599 := bstep (se 1 (by rfl) ⟨1617449, by rfl⟩ : syracuseStep 2156599 = 3234899) B3234899
theorem B3639269 : Blo 2155435 3639269 := bbase (se 4 (by rfl) ⟨341181, by rfl⟩ : syracuseStep 3639269 = 682363) (by norm_num)
theorem B2426179 : Blo 2155435 2426179 := bstep (se 1 (by rfl) ⟨1819634, by rfl⟩ : syracuseStep 2426179 = 3639269) B3639269
theorem B3234905 : Blo 2155435 3234905 := bstep (se 2 (by rfl) ⟨1213089, by rfl⟩ : syracuseStep 3234905 = 2426179) B2426179
theorem B2156603 : Blo 2155435 2156603 := bstep (se 1 (by rfl) ⟨1617452, by rfl⟩ : syracuseStep 2156603 = 3234905) B3234905
theorem B2914709 : Blo 2155435 2914709 := bbase (se 6 (by rfl) ⟨68313, by rfl⟩ : syracuseStep 2914709 = 136627) (by norm_num)
theorem B7772557 : Blo 2155435 7772557 := bstep (se 3 (by rfl) ⟨1457354, by rfl⟩ : syracuseStep 7772557 = 2914709) B2914709
theorem B10363409 : Blo 2155435 10363409 := bstep (se 2 (by rfl) ⟨3886278, by rfl⟩ : syracuseStep 10363409 = 7772557) B7772557
theorem B6908939 : Blo 2155435 6908939 := bstep (se 1 (by rfl) ⟨5181704, by rfl⟩ : syracuseStep 6908939 = 10363409) B10363409
theorem B4605959 : Blo 2155435 4605959 := bstep (se 1 (by rfl) ⟨3454469, by rfl⟩ : syracuseStep 4605959 = 6908939) B6908939
theorem B3070639 : Blo 2155435 3070639 := bstep (se 1 (by rfl) ⟨2302979, by rfl⟩ : syracuseStep 3070639 = 4605959) B4605959
theorem B16376741 : Blo 2155435 16376741 := bstep (se 4 (by rfl) ⟨1535319, by rfl⟩ : syracuseStep 16376741 = 3070639) B3070639
theorem B10917827 : Blo 2155435 10917827 := bstep (se 1 (by rfl) ⟨8188370, by rfl⟩ : syracuseStep 10917827 = 16376741) B16376741
theorem B7278551 : Blo 2155435 7278551 := bstep (se 1 (by rfl) ⟨5458913, by rfl⟩ : syracuseStep 7278551 = 10917827) B10917827
theorem B4852367 : Blo 2155435 4852367 := bstep (se 1 (by rfl) ⟨3639275, by rfl⟩ : syracuseStep 4852367 = 7278551) B7278551
theorem B3234911 : Blo 2155435 3234911 := bstep (se 1 (by rfl) ⟨2426183, by rfl⟩ : syracuseStep 3234911 = 4852367) B4852367
theorem B2156607 : Blo 2155435 2156607 := bstep (se 1 (by rfl) ⟨1617455, by rfl⟩ : syracuseStep 2156607 = 3234911) B3234911
theorem B3234917 : Blo 2155435 3234917 := bbase (se 4 (by rfl) ⟨303273, by rfl⟩ : syracuseStep 3234917 = 606547) (by norm_num)
theorem B2156611 : Blo 2155435 2156611 := bstep (se 1 (by rfl) ⟨1617458, by rfl⟩ : syracuseStep 2156611 = 3234917) B3234917
theorem B5181725 : Blo 2155435 5181725 := bbase (se 3 (by rfl) ⟨971573, by rfl⟩ : syracuseStep 5181725 = 1943147) (by norm_num)
theorem B3454483 : Blo 2155435 3454483 := bstep (se 1 (by rfl) ⟨2590862, by rfl⟩ : syracuseStep 3454483 = 5181725) B5181725
theorem B4605977 : Blo 2155435 4605977 := bstep (se 2 (by rfl) ⟨1727241, by rfl⟩ : syracuseStep 4605977 = 3454483) B3454483
theorem B3070651 : Blo 2155435 3070651 := bstep (se 1 (by rfl) ⟨2302988, by rfl⟩ : syracuseStep 3070651 = 4605977) B4605977
theorem B4094201 : Blo 2155435 4094201 := bstep (se 2 (by rfl) ⟨1535325, by rfl⟩ : syracuseStep 4094201 = 3070651) B3070651
theorem B2729467 : Blo 2155435 2729467 := bstep (se 1 (by rfl) ⟨2047100, by rfl⟩ : syracuseStep 2729467 = 4094201) B4094201
theorem B3639289 : Blo 2155435 3639289 := bstep (se 2 (by rfl) ⟨1364733, by rfl⟩ : syracuseStep 3639289 = 2729467) B2729467
theorem B4852385 : Blo 2155435 4852385 := bstep (se 2 (by rfl) ⟨1819644, by rfl⟩ : syracuseStep 4852385 = 3639289) B3639289
theorem B3234923 : Blo 2155435 3234923 := bstep (se 1 (by rfl) ⟨2426192, by rfl⟩ : syracuseStep 3234923 = 4852385) B4852385
theorem B2156615 : Blo 2155435 2156615 := bstep (se 1 (by rfl) ⟨1617461, by rfl⟩ : syracuseStep 2156615 = 3234923) B3234923
theorem B2426197 : Blo 2155435 2426197 := bbase (se 12 (by rfl) ⟨888, by rfl⟩ : syracuseStep 2426197 = 1777) (by norm_num)
theorem B3234929 : Blo 2155435 3234929 := bstep (se 2 (by rfl) ⟨1213098, by rfl⟩ : syracuseStep 3234929 = 2426197) B2426197
theorem B2156619 : Blo 2155435 2156619 := bstep (se 1 (by rfl) ⟨1617464, by rfl⟩ : syracuseStep 2156619 = 3234929) B3234929
theorem B2729477 : Blo 2155435 2729477 := bbase (se 4 (by rfl) ⟨255888, by rfl⟩ : syracuseStep 2729477 = 511777) (by norm_num)
theorem B7278605 : Blo 2155435 7278605 := bstep (se 3 (by rfl) ⟨1364738, by rfl⟩ : syracuseStep 7278605 = 2729477) B2729477
theorem B4852403 : Blo 2155435 4852403 := bstep (se 1 (by rfl) ⟨3639302, by rfl⟩ : syracuseStep 4852403 = 7278605) B7278605
theorem B3234935 : Blo 2155435 3234935 := bstep (se 1 (by rfl) ⟨2426201, by rfl⟩ : syracuseStep 3234935 = 4852403) B4852403
theorem B2156623 : Blo 2155435 2156623 := bstep (se 1 (by rfl) ⟨1617467, by rfl⟩ : syracuseStep 2156623 = 3234935) B3234935
theorem B3234941 : Blo 2155435 3234941 := bbase (se 3 (by rfl) ⟨606551, by rfl⟩ : syracuseStep 3234941 = 1213103) (by norm_num)
theorem B2156627 : Blo 2155435 2156627 := bstep (se 1 (by rfl) ⟨1617470, by rfl⟩ : syracuseStep 2156627 = 3234941) B3234941
theorem B4852421 : Blo 2155435 4852421 := bbase (se 4 (by rfl) ⟨454914, by rfl⟩ : syracuseStep 4852421 = 909829) (by norm_num)
theorem B3234947 : Blo 2155435 3234947 := bstep (se 1 (by rfl) ⟨2426210, by rfl⟩ : syracuseStep 3234947 = 4852421) B4852421
theorem B2156631 : Blo 2155435 2156631 := bstep (se 1 (by rfl) ⟨1617473, by rfl⟩ : syracuseStep 2156631 = 3234947) B3234947
theorem B4918637 : Blo 2155435 4918637 := bbase (se 3 (by rfl) ⟨922244, by rfl⟩ : syracuseStep 4918637 = 1844489) (by norm_num)
theorem B3279091 : Blo 2155435 3279091 := bstep (se 1 (by rfl) ⟨2459318, by rfl⟩ : syracuseStep 3279091 = 4918637) B4918637
theorem B4372121 : Blo 2155435 4372121 := bstep (se 2 (by rfl) ⟨1639545, by rfl⟩ : syracuseStep 4372121 = 3279091) B3279091
theorem B2914747 : Blo 2155435 2914747 := bstep (se 1 (by rfl) ⟨2186060, by rfl⟩ : syracuseStep 2914747 = 4372121) B4372121
theorem B15545317 : Blo 2155435 15545317 := bstep (se 4 (by rfl) ⟨1457373, by rfl⟩ : syracuseStep 15545317 = 2914747) B2914747
theorem B20727089 : Blo 2155435 20727089 := bstep (se 2 (by rfl) ⟨7772658, by rfl⟩ : syracuseStep 20727089 = 15545317) B15545317
theorem B13818059 : Blo 2155435 13818059 := bstep (se 1 (by rfl) ⟨10363544, by rfl⟩ : syracuseStep 13818059 = 20727089) B20727089
theorem B9212039 : Blo 2155435 9212039 := bstep (se 1 (by rfl) ⟨6909029, by rfl⟩ : syracuseStep 9212039 = 13818059) B13818059
theorem B6141359 : Blo 2155435 6141359 := bstep (se 1 (by rfl) ⟨4606019, by rfl⟩ : syracuseStep 6141359 = 9212039) B9212039
theorem B4094239 : Blo 2155435 4094239 := bstep (se 1 (by rfl) ⟨3070679, by rfl⟩ : syracuseStep 4094239 = 6141359) B6141359
theorem B5458985 : Blo 2155435 5458985 := bstep (se 2 (by rfl) ⟨2047119, by rfl⟩ : syracuseStep 5458985 = 4094239) B4094239
theorem B3639323 : Blo 2155435 3639323 := bstep (se 1 (by rfl) ⟨2729492, by rfl⟩ : syracuseStep 3639323 = 5458985) B5458985
theorem B2426215 : Blo 2155435 2426215 := bstep (se 1 (by rfl) ⟨1819661, by rfl⟩ : syracuseStep 2426215 = 3639323) B3639323
theorem B3234953 : Blo 2155435 3234953 := bstep (se 2 (by rfl) ⟨1213107, by rfl⟩ : syracuseStep 3234953 = 2426215) B2426215
theorem B2156635 : Blo 2155435 2156635 := bstep (se 1 (by rfl) ⟨1617476, by rfl⟩ : syracuseStep 2156635 = 3234953) B3234953
theorem B10917989 : Blo 2155435 10917989 := bbase (se 4 (by rfl) ⟨1023561, by rfl⟩ : syracuseStep 10917989 = 2047123) (by norm_num)
theorem B7278659 : Blo 2155435 7278659 := bstep (se 1 (by rfl) ⟨5458994, by rfl⟩ : syracuseStep 7278659 = 10917989) B10917989
theorem B4852439 : Blo 2155435 4852439 := bstep (se 1 (by rfl) ⟨3639329, by rfl⟩ : syracuseStep 4852439 = 7278659) B7278659
theorem B3234959 : Blo 2155435 3234959 := bstep (se 1 (by rfl) ⟨2426219, by rfl⟩ : syracuseStep 3234959 = 4852439) B4852439
theorem B2156639 : Blo 2155435 2156639 := bstep (se 1 (by rfl) ⟨1617479, by rfl⟩ : syracuseStep 2156639 = 3234959) B3234959
theorem B3234965 : Blo 2155435 3234965 := bbase (se 6 (by rfl) ⟨75819, by rfl⟩ : syracuseStep 3234965 = 151639) (by norm_num)
theorem B2156643 : Blo 2155435 2156643 := bstep (se 1 (by rfl) ⟨1617482, by rfl⟩ : syracuseStep 2156643 = 3234965) B3234965
theorem B3279109 : Blo 2155435 3279109 := bbase (se 4 (by rfl) ⟨307416, by rfl⟩ : syracuseStep 3279109 = 614833) (by norm_num)
theorem B4372145 : Blo 2155435 4372145 := bstep (se 2 (by rfl) ⟨1639554, by rfl⟩ : syracuseStep 4372145 = 3279109) B3279109
theorem B2914763 : Blo 2155435 2914763 := bstep (se 1 (by rfl) ⟨2186072, by rfl⟩ : syracuseStep 2914763 = 4372145) B4372145
theorem B7772701 : Blo 2155435 7772701 := bstep (se 3 (by rfl) ⟨1457381, by rfl⟩ : syracuseStep 7772701 = 2914763) B2914763
theorem B10363601 : Blo 2155435 10363601 := bstep (se 2 (by rfl) ⟨3886350, by rfl⟩ : syracuseStep 10363601 = 7772701) B7772701
theorem B6909067 : Blo 2155435 6909067 := bstep (se 1 (by rfl) ⟨5181800, by rfl⟩ : syracuseStep 6909067 = 10363601) B10363601
theorem B9212089 : Blo 2155435 9212089 := bstep (se 2 (by rfl) ⟨3454533, by rfl⟩ : syracuseStep 9212089 = 6909067) B6909067
theorem B12282785 : Blo 2155435 12282785 := bstep (se 2 (by rfl) ⟨4606044, by rfl⟩ : syracuseStep 12282785 = 9212089) B9212089
theorem B8188523 : Blo 2155435 8188523 := bstep (se 1 (by rfl) ⟨6141392, by rfl⟩ : syracuseStep 8188523 = 12282785) B12282785
theorem B5459015 : Blo 2155435 5459015 := bstep (se 1 (by rfl) ⟨4094261, by rfl⟩ : syracuseStep 5459015 = 8188523) B8188523
theorem B3639343 : Blo 2155435 3639343 := bstep (se 1 (by rfl) ⟨2729507, by rfl⟩ : syracuseStep 3639343 = 5459015) B5459015
theorem B4852457 : Blo 2155435 4852457 := bstep (se 2 (by rfl) ⟨1819671, by rfl⟩ : syracuseStep 4852457 = 3639343) B3639343
theorem B3234971 : Blo 2155435 3234971 := bstep (se 1 (by rfl) ⟨2426228, by rfl⟩ : syracuseStep 3234971 = 4852457) B4852457
theorem B2156647 : Blo 2155435 2156647 := bstep (se 1 (by rfl) ⟨1617485, by rfl⟩ : syracuseStep 2156647 = 3234971) B3234971
theorem B2426233 : Blo 2155435 2426233 := bbase (se 2 (by rfl) ⟨909837, by rfl⟩ : syracuseStep 2426233 = 1819675) (by norm_num)
theorem B3234977 : Blo 2155435 3234977 := bstep (se 2 (by rfl) ⟨1213116, by rfl⟩ : syracuseStep 3234977 = 2426233) B2426233
theorem B2156651 : Blo 2155435 2156651 := bstep (se 1 (by rfl) ⟨1617488, by rfl⟩ : syracuseStep 2156651 = 3234977) B3234977
theorem B5533517 : Blo 2155435 5533517 := bbase (se 3 (by rfl) ⟨1037534, by rfl⟩ : syracuseStep 5533517 = 2075069) (by norm_num)
theorem B3689011 : Blo 2155435 3689011 := bstep (se 1 (by rfl) ⟨2766758, by rfl⟩ : syracuseStep 3689011 = 5533517) B5533517
theorem B4918681 : Blo 2155435 4918681 := bstep (se 2 (by rfl) ⟨1844505, by rfl⟩ : syracuseStep 4918681 = 3689011) B3689011
theorem B6558241 : Blo 2155435 6558241 := bstep (se 2 (by rfl) ⟨2459340, by rfl⟩ : syracuseStep 6558241 = 4918681) B4918681
theorem B8744321 : Blo 2155435 8744321 := bstep (se 2 (by rfl) ⟨3279120, by rfl⟩ : syracuseStep 8744321 = 6558241) B6558241
theorem B23318189 : Blo 2155435 23318189 := bstep (se 3 (by rfl) ⟨4372160, by rfl⟩ : syracuseStep 23318189 = 8744321) B8744321
theorem B15545459 : Blo 2155435 15545459 := bstep (se 1 (by rfl) ⟨11659094, by rfl⟩ : syracuseStep 15545459 = 23318189) B23318189
theorem B10363639 : Blo 2155435 10363639 := bstep (se 1 (by rfl) ⟨7772729, by rfl⟩ : syracuseStep 10363639 = 15545459) B15545459
theorem B13818185 : Blo 2155435 13818185 := bstep (se 2 (by rfl) ⟨5181819, by rfl⟩ : syracuseStep 13818185 = 10363639) B10363639
theorem B9212123 : Blo 2155435 9212123 := bstep (se 1 (by rfl) ⟨6909092, by rfl⟩ : syracuseStep 9212123 = 13818185) B13818185
theorem B6141415 : Blo 2155435 6141415 := bstep (se 1 (by rfl) ⟨4606061, by rfl⟩ : syracuseStep 6141415 = 9212123) B9212123
theorem B8188553 : Blo 2155435 8188553 := bstep (se 2 (by rfl) ⟨3070707, by rfl⟩ : syracuseStep 8188553 = 6141415) B6141415
theorem B5459035 : Blo 2155435 5459035 := bstep (se 1 (by rfl) ⟨4094276, by rfl⟩ : syracuseStep 5459035 = 8188553) B8188553
theorem B7278713 : Blo 2155435 7278713 := bstep (se 2 (by rfl) ⟨2729517, by rfl⟩ : syracuseStep 7278713 = 5459035) B5459035
theorem B4852475 : Blo 2155435 4852475 := bstep (se 1 (by rfl) ⟨3639356, by rfl⟩ : syracuseStep 4852475 = 7278713) B7278713
theorem B3234983 : Blo 2155435 3234983 := bstep (se 1 (by rfl) ⟨2426237, by rfl⟩ : syracuseStep 3234983 = 4852475) B4852475
theorem B2156655 : Blo 2155435 2156655 := bstep (se 1 (by rfl) ⟨1617491, by rfl⟩ : syracuseStep 2156655 = 3234983) B3234983
theorem B3234989 : Blo 2155435 3234989 := bbase (se 3 (by rfl) ⟨606560, by rfl⟩ : syracuseStep 3234989 = 1213121) (by norm_num)
theorem B2156659 : Blo 2155435 2156659 := bstep (se 1 (by rfl) ⟨1617494, by rfl⟩ : syracuseStep 2156659 = 3234989) B3234989
theorem B4852493 : Blo 2155435 4852493 := bbase (se 3 (by rfl) ⟨909842, by rfl⟩ : syracuseStep 4852493 = 1819685) (by norm_num)
theorem B3234995 : Blo 2155435 3234995 := bstep (se 1 (by rfl) ⟨2426246, by rfl⟩ : syracuseStep 3234995 = 4852493) B4852493
theorem B2156663 : Blo 2155435 2156663 := bstep (se 1 (by rfl) ⟨1617497, by rfl⟩ : syracuseStep 2156663 = 3234995) B3234995
theorem B2729533 : Blo 2155435 2729533 := bbase (se 3 (by rfl) ⟨511787, by rfl⟩ : syracuseStep 2729533 = 1023575) (by norm_num)
theorem B3639377 : Blo 2155435 3639377 := bstep (se 2 (by rfl) ⟨1364766, by rfl⟩ : syracuseStep 3639377 = 2729533) B2729533
theorem B2426251 : Blo 2155435 2426251 := bstep (se 1 (by rfl) ⟨1819688, by rfl⟩ : syracuseStep 2426251 = 3639377) B3639377
theorem B3235001 : Blo 2155435 3235001 := bstep (se 2 (by rfl) ⟨1213125, by rfl⟩ : syracuseStep 3235001 = 2426251) B2426251
theorem B2156667 : Blo 2155435 2156667 := bstep (se 1 (by rfl) ⟨1617500, by rfl⟩ : syracuseStep 2156667 = 3235001) B3235001
theorem B4668941 : Blo 2155435 4668941 := bbase (se 3 (by rfl) ⟨875426, by rfl⟩ : syracuseStep 4668941 = 1750853) (by norm_num)
theorem B12450509 : Blo 2155435 12450509 := bstep (se 3 (by rfl) ⟨2334470, by rfl⟩ : syracuseStep 12450509 = 4668941) B4668941
theorem B8300339 : Blo 2155435 8300339 := bstep (se 1 (by rfl) ⟨6225254, by rfl⟩ : syracuseStep 8300339 = 12450509) B12450509
theorem B5533559 : Blo 2155435 5533559 := bstep (se 1 (by rfl) ⟨4150169, by rfl⟩ : syracuseStep 5533559 = 8300339) B8300339
theorem B3689039 : Blo 2155435 3689039 := bstep (se 1 (by rfl) ⟨2766779, by rfl⟩ : syracuseStep 3689039 = 5533559) B5533559
theorem B2459359 : Blo 2155435 2459359 := bstep (se 1 (by rfl) ⟨1844519, by rfl⟩ : syracuseStep 2459359 = 3689039) B3689039
theorem B3279145 : Blo 2155435 3279145 := bstep (se 2 (by rfl) ⟨1229679, by rfl⟩ : syracuseStep 3279145 = 2459359) B2459359
theorem B4372193 : Blo 2155435 4372193 := bstep (se 2 (by rfl) ⟨1639572, by rfl⟩ : syracuseStep 4372193 = 3279145) B3279145
theorem B2914795 : Blo 2155435 2914795 := bstep (se 1 (by rfl) ⟨2186096, by rfl⟩ : syracuseStep 2914795 = 4372193) B4372193
theorem B15545573 : Blo 2155435 15545573 := bstep (se 4 (by rfl) ⟨1457397, by rfl⟩ : syracuseStep 15545573 = 2914795) B2914795
theorem B10363715 : Blo 2155435 10363715 := bstep (se 1 (by rfl) ⟨7772786, by rfl⟩ : syracuseStep 10363715 = 15545573) B15545573
theorem B6909143 : Blo 2155435 6909143 := bstep (se 1 (by rfl) ⟨5181857, by rfl⟩ : syracuseStep 6909143 = 10363715) B10363715
theorem B18424381 : Blo 2155435 18424381 := bstep (se 3 (by rfl) ⟨3454571, by rfl⟩ : syracuseStep 18424381 = 6909143) B6909143
theorem B24565841 : Blo 2155435 24565841 := bstep (se 2 (by rfl) ⟨9212190, by rfl⟩ : syracuseStep 24565841 = 18424381) B18424381
theorem B16377227 : Blo 2155435 16377227 := bstep (se 1 (by rfl) ⟨12282920, by rfl⟩ : syracuseStep 16377227 = 24565841) B24565841
theorem B10918151 : Blo 2155435 10918151 := bstep (se 1 (by rfl) ⟨8188613, by rfl⟩ : syracuseStep 10918151 = 16377227) B16377227
theorem B7278767 : Blo 2155435 7278767 := bstep (se 1 (by rfl) ⟨5459075, by rfl⟩ : syracuseStep 7278767 = 10918151) B10918151
theorem B4852511 : Blo 2155435 4852511 := bstep (se 1 (by rfl) ⟨3639383, by rfl⟩ : syracuseStep 4852511 = 7278767) B7278767
theorem B3235007 : Blo 2155435 3235007 := bstep (se 1 (by rfl) ⟨2426255, by rfl⟩ : syracuseStep 3235007 = 4852511) B4852511
theorem B2156671 : Blo 2155435 2156671 := bstep (se 1 (by rfl) ⟨1617503, by rfl⟩ : syracuseStep 2156671 = 3235007) B3235007
theorem B3235013 : Blo 2155435 3235013 := bbase (se 4 (by rfl) ⟨303282, by rfl⟩ : syracuseStep 3235013 = 606565) (by norm_num)
theorem B2156675 : Blo 2155435 2156675 := bstep (se 1 (by rfl) ⟨1617506, by rfl⟩ : syracuseStep 2156675 = 3235013) B3235013
theorem B3639397 : Blo 2155435 3639397 := bbase (se 4 (by rfl) ⟨341193, by rfl⟩ : syracuseStep 3639397 = 682387) (by norm_num)
theorem B4852529 : Blo 2155435 4852529 := bstep (se 2 (by rfl) ⟨1819698, by rfl⟩ : syracuseStep 4852529 = 3639397) B3639397
theorem B3235019 : Blo 2155435 3235019 := bstep (se 1 (by rfl) ⟨2426264, by rfl⟩ : syracuseStep 3235019 = 4852529) B4852529
theorem B2156679 : Blo 2155435 2156679 := bstep (se 1 (by rfl) ⟨1617509, by rfl⟩ : syracuseStep 2156679 = 3235019) B3235019
theorem B2426269 : Blo 2155435 2426269 := bbase (se 3 (by rfl) ⟨454925, by rfl⟩ : syracuseStep 2426269 = 909851) (by norm_num)
theorem B3235025 : Blo 2155435 3235025 := bstep (se 2 (by rfl) ⟨1213134, by rfl⟩ : syracuseStep 3235025 = 2426269) B2426269
theorem B2156683 : Blo 2155435 2156683 := bstep (se 1 (by rfl) ⟨1617512, by rfl⟩ : syracuseStep 2156683 = 3235025) B3235025
theorem B7278821 : Blo 2155435 7278821 := bbase (se 4 (by rfl) ⟨682389, by rfl⟩ : syracuseStep 7278821 = 1364779) (by norm_num)
theorem B4852547 : Blo 2155435 4852547 := bstep (se 1 (by rfl) ⟨3639410, by rfl⟩ : syracuseStep 4852547 = 7278821) B7278821
theorem B3235031 : Blo 2155435 3235031 := bstep (se 1 (by rfl) ⟨2426273, by rfl⟩ : syracuseStep 3235031 = 4852547) B4852547
theorem B2156687 : Blo 2155435 2156687 := bstep (se 1 (by rfl) ⟨1617515, by rfl⟩ : syracuseStep 2156687 = 3235031) B3235031
theorem B3235037 : Blo 2155435 3235037 := bbase (se 3 (by rfl) ⟨606569, by rfl⟩ : syracuseStep 3235037 = 1213139) (by norm_num)
theorem B2156691 : Blo 2155435 2156691 := bstep (se 1 (by rfl) ⟨1617518, by rfl⟩ : syracuseStep 2156691 = 3235037) B3235037
theorem B4852565 : Blo 2155435 4852565 := bbase (se 9 (by rfl) ⟨14216, by rfl⟩ : syracuseStep 4852565 = 28433) (by norm_num)
theorem B3235043 : Blo 2155435 3235043 := bstep (se 1 (by rfl) ⟨2426282, by rfl⟩ : syracuseStep 3235043 = 4852565) B4852565
theorem B2156695 : Blo 2155435 2156695 := bstep (se 1 (by rfl) ⟨1617521, by rfl⟩ : syracuseStep 2156695 = 3235043) B3235043
theorem B6141541 : Blo 2155435 6141541 := bbase (se 4 (by rfl) ⟨575769, by rfl⟩ : syracuseStep 6141541 = 1151539) (by norm_num)
theorem B8188721 : Blo 2155435 8188721 := bstep (se 2 (by rfl) ⟨3070770, by rfl⟩ : syracuseStep 8188721 = 6141541) B6141541
theorem B5459147 : Blo 2155435 5459147 := bstep (se 1 (by rfl) ⟨4094360, by rfl⟩ : syracuseStep 5459147 = 8188721) B8188721
theorem B3639431 : Blo 2155435 3639431 := bstep (se 1 (by rfl) ⟨2729573, by rfl⟩ : syracuseStep 3639431 = 5459147) B5459147
theorem B2426287 : Blo 2155435 2426287 := bstep (se 1 (by rfl) ⟨1819715, by rfl⟩ : syracuseStep 2426287 = 3639431) B3639431
theorem B3235049 : Blo 2155435 3235049 := bstep (se 2 (by rfl) ⟨1213143, by rfl⟩ : syracuseStep 3235049 = 2426287) B2426287
theorem B2156699 : Blo 2155435 2156699 := bstep (se 1 (by rfl) ⟨1617524, by rfl⟩ : syracuseStep 2156699 = 3235049) B3235049
theorem B3689093 : Blo 2155435 3689093 := bbase (se 4 (by rfl) ⟨345852, by rfl⟩ : syracuseStep 3689093 = 691705) (by norm_num)
theorem B2459395 : Blo 2155435 2459395 := bstep (se 1 (by rfl) ⟨1844546, by rfl⟩ : syracuseStep 2459395 = 3689093) B3689093
theorem B3279193 : Blo 2155435 3279193 := bstep (se 2 (by rfl) ⟨1229697, by rfl⟩ : syracuseStep 3279193 = 2459395) B2459395
theorem B17489029 : Blo 2155435 17489029 := bstep (se 4 (by rfl) ⟨1639596, by rfl⟩ : syracuseStep 17489029 = 3279193) B3279193
theorem B23318705 : Blo 2155435 23318705 := bstep (se 2 (by rfl) ⟨8744514, by rfl⟩ : syracuseStep 23318705 = 17489029) B17489029
theorem B62183213 : Blo 2155435 62183213 := bstep (se 3 (by rfl) ⟨11659352, by rfl⟩ : syracuseStep 62183213 = 23318705) B23318705
theorem B41455475 : Blo 2155435 41455475 := bstep (se 1 (by rfl) ⟨31091606, by rfl⟩ : syracuseStep 41455475 = 62183213) B62183213
theorem B27636983 : Blo 2155435 27636983 := bstep (se 1 (by rfl) ⟨20727737, by rfl⟩ : syracuseStep 27636983 = 41455475) B41455475
theorem B18424655 : Blo 2155435 18424655 := bstep (se 1 (by rfl) ⟨13818491, by rfl⟩ : syracuseStep 18424655 = 27636983) B27636983
theorem B12283103 : Blo 2155435 12283103 := bstep (se 1 (by rfl) ⟨9212327, by rfl⟩ : syracuseStep 12283103 = 18424655) B18424655
theorem B8188735 : Blo 2155435 8188735 := bstep (se 1 (by rfl) ⟨6141551, by rfl⟩ : syracuseStep 8188735 = 12283103) B12283103
theorem B10918313 : Blo 2155435 10918313 := bstep (se 2 (by rfl) ⟨4094367, by rfl⟩ : syracuseStep 10918313 = 8188735) B8188735
theorem B7278875 : Blo 2155435 7278875 := bstep (se 1 (by rfl) ⟨5459156, by rfl⟩ : syracuseStep 7278875 = 10918313) B10918313
theorem B4852583 : Blo 2155435 4852583 := bstep (se 1 (by rfl) ⟨3639437, by rfl⟩ : syracuseStep 4852583 = 7278875) B7278875
theorem B3235055 : Blo 2155435 3235055 := bstep (se 1 (by rfl) ⟨2426291, by rfl⟩ : syracuseStep 3235055 = 4852583) B4852583
theorem B2156703 : Blo 2155435 2156703 := bstep (se 1 (by rfl) ⟨1617527, by rfl⟩ : syracuseStep 2156703 = 3235055) B3235055
theorem B3235061 : Blo 2155435 3235061 := bbase (se 5 (by rfl) ⟨151643, by rfl⟩ : syracuseStep 3235061 = 303287) (by norm_num)
theorem B2156707 : Blo 2155435 2156707 := bstep (se 1 (by rfl) ⟨1617530, by rfl⟩ : syracuseStep 2156707 = 3235061) B3235061
theorem B10363909 : Blo 2155435 10363909 := bbase (se 4 (by rfl) ⟨971616, by rfl⟩ : syracuseStep 10363909 = 1943233) (by norm_num)
theorem B13818545 : Blo 2155435 13818545 := bstep (se 2 (by rfl) ⟨5181954, by rfl⟩ : syracuseStep 13818545 = 10363909) B10363909
theorem B9212363 : Blo 2155435 9212363 := bstep (se 1 (by rfl) ⟨6909272, by rfl⟩ : syracuseStep 9212363 = 13818545) B13818545
theorem B6141575 : Blo 2155435 6141575 := bstep (se 1 (by rfl) ⟨4606181, by rfl⟩ : syracuseStep 6141575 = 9212363) B9212363
theorem B4094383 : Blo 2155435 4094383 := bstep (se 1 (by rfl) ⟨3070787, by rfl⟩ : syracuseStep 4094383 = 6141575) B6141575
theorem B5459177 : Blo 2155435 5459177 := bstep (se 2 (by rfl) ⟨2047191, by rfl⟩ : syracuseStep 5459177 = 4094383) B4094383
theorem B3639451 : Blo 2155435 3639451 := bstep (se 1 (by rfl) ⟨2729588, by rfl⟩ : syracuseStep 3639451 = 5459177) B5459177
theorem B4852601 : Blo 2155435 4852601 := bstep (se 2 (by rfl) ⟨1819725, by rfl⟩ : syracuseStep 4852601 = 3639451) B3639451
theorem B3235067 : Blo 2155435 3235067 := bstep (se 1 (by rfl) ⟨2426300, by rfl⟩ : syracuseStep 3235067 = 4852601) B4852601
theorem B2156711 : Blo 2155435 2156711 := bstep (se 1 (by rfl) ⟨1617533, by rfl⟩ : syracuseStep 2156711 = 3235067) B3235067
theorem B2426305 : Blo 2155435 2426305 := bbase (se 2 (by rfl) ⟨909864, by rfl⟩ : syracuseStep 2426305 = 1819729) (by norm_num)
theorem B3235073 : Blo 2155435 3235073 := bstep (se 2 (by rfl) ⟨1213152, by rfl⟩ : syracuseStep 3235073 = 2426305) B2426305
theorem B2156715 : Blo 2155435 2156715 := bstep (se 1 (by rfl) ⟨1617536, by rfl⟩ : syracuseStep 2156715 = 3235073) B3235073
theorem B5459197 : Blo 2155435 5459197 := bbase (se 3 (by rfl) ⟨1023599, by rfl⟩ : syracuseStep 5459197 = 2047199) (by norm_num)
theorem B7278929 : Blo 2155435 7278929 := bstep (se 2 (by rfl) ⟨2729598, by rfl⟩ : syracuseStep 7278929 = 5459197) B5459197
theorem B4852619 : Blo 2155435 4852619 := bstep (se 1 (by rfl) ⟨3639464, by rfl⟩ : syracuseStep 4852619 = 7278929) B7278929
theorem B3235079 : Blo 2155435 3235079 := bstep (se 1 (by rfl) ⟨2426309, by rfl⟩ : syracuseStep 3235079 = 4852619) B4852619
theorem B2156719 : Blo 2155435 2156719 := bstep (se 1 (by rfl) ⟨1617539, by rfl⟩ : syracuseStep 2156719 = 3235079) B3235079
theorem B3235085 : Blo 2155435 3235085 := bbase (se 3 (by rfl) ⟨606578, by rfl⟩ : syracuseStep 3235085 = 1213157) (by norm_num)
theorem B2156723 : Blo 2155435 2156723 := bstep (se 1 (by rfl) ⟨1617542, by rfl⟩ : syracuseStep 2156723 = 3235085) B3235085
theorem B4852637 : Blo 2155435 4852637 := bbase (se 3 (by rfl) ⟨909869, by rfl⟩ : syracuseStep 4852637 = 1819739) (by norm_num)
theorem B3235091 : Blo 2155435 3235091 := bstep (se 1 (by rfl) ⟨2426318, by rfl⟩ : syracuseStep 3235091 = 4852637) B4852637
theorem B2156727 : Blo 2155435 2156727 := bstep (se 1 (by rfl) ⟨1617545, by rfl⟩ : syracuseStep 2156727 = 3235091) B3235091
theorem B3639485 : Blo 2155435 3639485 := bbase (se 3 (by rfl) ⟨682403, by rfl⟩ : syracuseStep 3639485 = 1364807) (by norm_num)
theorem B2426323 : Blo 2155435 2426323 := bstep (se 1 (by rfl) ⟨1819742, by rfl⟩ : syracuseStep 2426323 = 3639485) B3639485
theorem B3235097 : Blo 2155435 3235097 := bstep (se 2 (by rfl) ⟨1213161, by rfl⟩ : syracuseStep 3235097 = 2426323) B2426323
theorem B2156731 : Blo 2155435 2156731 := bstep (se 1 (by rfl) ⟨1617548, by rfl⟩ : syracuseStep 2156731 = 3235097) B3235097
theorem B12283285 : Blo 2155435 12283285 := bbase (se 6 (by rfl) ⟨287889, by rfl⟩ : syracuseStep 12283285 = 575779) (by norm_num)
theorem B16377713 : Blo 2155435 16377713 := bstep (se 2 (by rfl) ⟨6141642, by rfl⟩ : syracuseStep 16377713 = 12283285) B12283285
theorem B10918475 : Blo 2155435 10918475 := bstep (se 1 (by rfl) ⟨8188856, by rfl⟩ : syracuseStep 10918475 = 16377713) B16377713
theorem B7278983 : Blo 2155435 7278983 := bstep (se 1 (by rfl) ⟨5459237, by rfl⟩ : syracuseStep 7278983 = 10918475) B10918475
theorem B4852655 : Blo 2155435 4852655 := bstep (se 1 (by rfl) ⟨3639491, by rfl⟩ : syracuseStep 4852655 = 7278983) B7278983
theorem B3235103 : Blo 2155435 3235103 := bstep (se 1 (by rfl) ⟨2426327, by rfl⟩ : syracuseStep 3235103 = 4852655) B4852655
theorem B2156735 : Blo 2155435 2156735 := bstep (se 1 (by rfl) ⟨1617551, by rfl⟩ : syracuseStep 2156735 = 3235103) B3235103
theorem B3235109 : Blo 2155435 3235109 := bbase (se 4 (by rfl) ⟨303291, by rfl⟩ : syracuseStep 3235109 = 606583) (by norm_num)
theorem B2156739 : Blo 2155435 2156739 := bstep (se 1 (by rfl) ⟨1617554, by rfl⟩ : syracuseStep 2156739 = 3235109) B3235109
theorem B2729629 : Blo 2155435 2729629 := bbase (se 3 (by rfl) ⟨511805, by rfl⟩ : syracuseStep 2729629 = 1023611) (by norm_num)
theorem B3639505 : Blo 2155435 3639505 := bstep (se 2 (by rfl) ⟨1364814, by rfl⟩ : syracuseStep 3639505 = 2729629) B2729629
theorem B4852673 : Blo 2155435 4852673 := bstep (se 2 (by rfl) ⟨1819752, by rfl⟩ : syracuseStep 4852673 = 3639505) B3639505
theorem B3235115 : Blo 2155435 3235115 := bstep (se 1 (by rfl) ⟨2426336, by rfl⟩ : syracuseStep 3235115 = 4852673) B4852673
theorem B2156743 : Blo 2155435 2156743 := bstep (se 1 (by rfl) ⟨1617557, by rfl⟩ : syracuseStep 2156743 = 3235115) B3235115
theorem B2426341 : Blo 2155435 2426341 := bbase (se 4 (by rfl) ⟨227469, by rfl⟩ : syracuseStep 2426341 = 454939) (by norm_num)
theorem B3235121 : Blo 2155435 3235121 := bstep (se 2 (by rfl) ⟨1213170, by rfl⟩ : syracuseStep 3235121 = 2426341) B2426341
theorem B2156747 : Blo 2155435 2156747 := bstep (se 1 (by rfl) ⟨1617560, by rfl⟩ : syracuseStep 2156747 = 3235121) B3235121
theorem B7773077 : Blo 2155435 7773077 := bbase (se 6 (by rfl) ⟨182181, by rfl⟩ : syracuseStep 7773077 = 364363) (by norm_num)
theorem B5182051 : Blo 2155435 5182051 := bstep (se 1 (by rfl) ⟨3886538, by rfl⟩ : syracuseStep 5182051 = 7773077) B7773077
theorem B6909401 : Blo 2155435 6909401 := bstep (se 2 (by rfl) ⟨2591025, by rfl⟩ : syracuseStep 6909401 = 5182051) B5182051
theorem B4606267 : Blo 2155435 4606267 := bstep (se 1 (by rfl) ⟨3454700, by rfl⟩ : syracuseStep 4606267 = 6909401) B6909401
theorem B6141689 : Blo 2155435 6141689 := bstep (se 2 (by rfl) ⟨2303133, by rfl⟩ : syracuseStep 6141689 = 4606267) B4606267
theorem B4094459 : Blo 2155435 4094459 := bstep (se 1 (by rfl) ⟨3070844, by rfl⟩ : syracuseStep 4094459 = 6141689) B6141689
theorem B2729639 : Blo 2155435 2729639 := bstep (se 1 (by rfl) ⟨2047229, by rfl⟩ : syracuseStep 2729639 = 4094459) B4094459
theorem B7279037 : Blo 2155435 7279037 := bstep (se 3 (by rfl) ⟨1364819, by rfl⟩ : syracuseStep 7279037 = 2729639) B2729639
theorem B4852691 : Blo 2155435 4852691 := bstep (se 1 (by rfl) ⟨3639518, by rfl⟩ : syracuseStep 4852691 = 7279037) B7279037
theorem B3235127 : Blo 2155435 3235127 := bstep (se 1 (by rfl) ⟨2426345, by rfl⟩ : syracuseStep 3235127 = 4852691) B4852691
theorem B2156751 : Blo 2155435 2156751 := bstep (se 1 (by rfl) ⟨1617563, by rfl⟩ : syracuseStep 2156751 = 3235127) B3235127
theorem B3235133 : Blo 2155435 3235133 := bbase (se 3 (by rfl) ⟨606587, by rfl⟩ : syracuseStep 3235133 = 1213175) (by norm_num)
theorem B2156755 : Blo 2155435 2156755 := bstep (se 1 (by rfl) ⟨1617566, by rfl⟩ : syracuseStep 2156755 = 3235133) B3235133
theorem B4852709 : Blo 2155435 4852709 := bbase (se 4 (by rfl) ⟨454941, by rfl⟩ : syracuseStep 4852709 = 909883) (by norm_num)
theorem B3235139 : Blo 2155435 3235139 := bstep (se 1 (by rfl) ⟨2426354, by rfl⟩ : syracuseStep 3235139 = 4852709) B4852709
theorem B2156759 : Blo 2155435 2156759 := bstep (se 1 (by rfl) ⟨1617569, by rfl⟩ : syracuseStep 2156759 = 3235139) B3235139
theorem B5459309 : Blo 2155435 5459309 := bbase (se 3 (by rfl) ⟨1023620, by rfl⟩ : syracuseStep 5459309 = 2047241) (by norm_num)
theorem B3639539 : Blo 2155435 3639539 := bstep (se 1 (by rfl) ⟨2729654, by rfl⟩ : syracuseStep 3639539 = 5459309) B5459309
theorem B2426359 : Blo 2155435 2426359 := bstep (se 1 (by rfl) ⟨1819769, by rfl⟩ : syracuseStep 2426359 = 3639539) B3639539
theorem B3235145 : Blo 2155435 3235145 := bstep (se 2 (by rfl) ⟨1213179, by rfl⟩ : syracuseStep 3235145 = 2426359) B2426359
theorem B2156763 : Blo 2155435 2156763 := bstep (se 1 (by rfl) ⟨1617572, by rfl⟩ : syracuseStep 2156763 = 3235145) B3235145
theorem B4606301 : Blo 2155435 4606301 := bbase (se 3 (by rfl) ⟨863681, by rfl⟩ : syracuseStep 4606301 = 1727363) (by norm_num)
theorem B3070867 : Blo 2155435 3070867 := bstep (se 1 (by rfl) ⟨2303150, by rfl⟩ : syracuseStep 3070867 = 4606301) B4606301
theorem B4094489 : Blo 2155435 4094489 := bstep (se 2 (by rfl) ⟨1535433, by rfl⟩ : syracuseStep 4094489 = 3070867) B3070867
theorem B10918637 : Blo 2155435 10918637 := bstep (se 3 (by rfl) ⟨2047244, by rfl⟩ : syracuseStep 10918637 = 4094489) B4094489
theorem B7279091 : Blo 2155435 7279091 := bstep (se 1 (by rfl) ⟨5459318, by rfl⟩ : syracuseStep 7279091 = 10918637) B10918637
theorem B4852727 : Blo 2155435 4852727 := bstep (se 1 (by rfl) ⟨3639545, by rfl⟩ : syracuseStep 4852727 = 7279091) B7279091
theorem B3235151 : Blo 2155435 3235151 := bstep (se 1 (by rfl) ⟨2426363, by rfl⟩ : syracuseStep 3235151 = 4852727) B4852727
theorem B2156767 : Blo 2155435 2156767 := bstep (se 1 (by rfl) ⟨1617575, by rfl⟩ : syracuseStep 2156767 = 3235151) B3235151
theorem B3235157 : Blo 2155435 3235157 := bbase (se 11 (by rfl) ⟨2369, by rfl⟩ : syracuseStep 3235157 = 4739) (by norm_num)
theorem B2156771 : Blo 2155435 2156771 := bstep (se 1 (by rfl) ⟨1617578, by rfl⟩ : syracuseStep 2156771 = 3235157) B3235157
theorem B5182109 : Blo 2155435 5182109 := bbase (se 3 (by rfl) ⟨971645, by rfl⟩ : syracuseStep 5182109 = 1943291) (by norm_num)
theorem B3454739 : Blo 2155435 3454739 := bstep (se 1 (by rfl) ⟨2591054, by rfl⟩ : syracuseStep 3454739 = 5182109) B5182109
theorem B2303159 : Blo 2155435 2303159 := bstep (se 1 (by rfl) ⟨1727369, by rfl⟩ : syracuseStep 2303159 = 3454739) B3454739
theorem B6141757 : Blo 2155435 6141757 := bstep (se 3 (by rfl) ⟨1151579, by rfl⟩ : syracuseStep 6141757 = 2303159) B2303159
theorem B8189009 : Blo 2155435 8189009 := bstep (se 2 (by rfl) ⟨3070878, by rfl⟩ : syracuseStep 8189009 = 6141757) B6141757
theorem B5459339 : Blo 2155435 5459339 := bstep (se 1 (by rfl) ⟨4094504, by rfl⟩ : syracuseStep 5459339 = 8189009) B8189009
theorem B3639559 : Blo 2155435 3639559 := bstep (se 1 (by rfl) ⟨2729669, by rfl⟩ : syracuseStep 3639559 = 5459339) B5459339
theorem B4852745 : Blo 2155435 4852745 := bstep (se 2 (by rfl) ⟨1819779, by rfl⟩ : syracuseStep 4852745 = 3639559) B3639559
theorem B3235163 : Blo 2155435 3235163 := bstep (se 1 (by rfl) ⟨2426372, by rfl⟩ : syracuseStep 3235163 = 4852745) B4852745
theorem B2156775 : Blo 2155435 2156775 := bstep (se 1 (by rfl) ⟨1617581, by rfl⟩ : syracuseStep 2156775 = 3235163) B3235163
theorem B2426377 : Blo 2155435 2426377 := bbase (se 2 (by rfl) ⟨909891, by rfl⟩ : syracuseStep 2426377 = 1819783) (by norm_num)
theorem B3235169 : Blo 2155435 3235169 := bstep (se 2 (by rfl) ⟨1213188, by rfl⟩ : syracuseStep 3235169 = 2426377) B2426377
theorem B2156779 : Blo 2155435 2156779 := bstep (se 1 (by rfl) ⟨1617584, by rfl⟩ : syracuseStep 2156779 = 3235169) B3235169
theorem B14756917 : Blo 2155435 14756917 := bbase (se 5 (by rfl) ⟨691730, by rfl⟩ : syracuseStep 14756917 = 1383461) (by norm_num)
theorem B19675889 : Blo 2155435 19675889 := bstep (se 2 (by rfl) ⟨7378458, by rfl⟩ : syracuseStep 19675889 = 14756917) B14756917
theorem B13117259 : Blo 2155435 13117259 := bstep (se 1 (by rfl) ⟨9837944, by rfl⟩ : syracuseStep 13117259 = 19675889) B19675889
theorem B34979357 : Blo 2155435 34979357 := bstep (se 3 (by rfl) ⟨6558629, by rfl⟩ : syracuseStep 34979357 = 13117259) B13117259
theorem B23319571 : Blo 2155435 23319571 := bstep (se 1 (by rfl) ⟨17489678, by rfl⟩ : syracuseStep 23319571 = 34979357) B34979357
theorem B31092761 : Blo 2155435 31092761 := bstep (se 2 (by rfl) ⟨11659785, by rfl⟩ : syracuseStep 31092761 = 23319571) B23319571
theorem B20728507 : Blo 2155435 20728507 := bstep (se 1 (by rfl) ⟨15546380, by rfl⟩ : syracuseStep 20728507 = 31092761) B31092761
theorem B27638009 : Blo 2155435 27638009 := bstep (se 2 (by rfl) ⟨10364253, by rfl⟩ : syracuseStep 27638009 = 20728507) B20728507
theorem B18425339 : Blo 2155435 18425339 := bstep (se 1 (by rfl) ⟨13819004, by rfl⟩ : syracuseStep 18425339 = 27638009) B27638009
theorem B12283559 : Blo 2155435 12283559 := bstep (se 1 (by rfl) ⟨9212669, by rfl⟩ : syracuseStep 12283559 = 18425339) B18425339
theorem B8189039 : Blo 2155435 8189039 := bstep (se 1 (by rfl) ⟨6141779, by rfl⟩ : syracuseStep 8189039 = 12283559) B12283559
theorem B5459359 : Blo 2155435 5459359 := bstep (se 1 (by rfl) ⟨4094519, by rfl⟩ : syracuseStep 5459359 = 8189039) B8189039
theorem B7279145 : Blo 2155435 7279145 := bstep (se 2 (by rfl) ⟨2729679, by rfl⟩ : syracuseStep 7279145 = 5459359) B5459359
theorem B4852763 : Blo 2155435 4852763 := bstep (se 1 (by rfl) ⟨3639572, by rfl⟩ : syracuseStep 4852763 = 7279145) B7279145
theorem B3235175 : Blo 2155435 3235175 := bstep (se 1 (by rfl) ⟨2426381, by rfl⟩ : syracuseStep 3235175 = 4852763) B4852763
theorem B2156783 : Blo 2155435 2156783 := bstep (se 1 (by rfl) ⟨1617587, by rfl⟩ : syracuseStep 2156783 = 3235175) B3235175
theorem B3235181 : Blo 2155435 3235181 := bbase (se 3 (by rfl) ⟨606596, by rfl⟩ : syracuseStep 3235181 = 1213193) (by norm_num)
theorem B2156787 : Blo 2155435 2156787 := bstep (se 1 (by rfl) ⟨1617590, by rfl⟩ : syracuseStep 2156787 = 3235181) B3235181
theorem B4852781 : Blo 2155435 4852781 := bbase (se 3 (by rfl) ⟨909896, by rfl⟩ : syracuseStep 4852781 = 1819793) (by norm_num)
theorem B3235187 : Blo 2155435 3235187 := bstep (se 1 (by rfl) ⟨2426390, by rfl⟩ : syracuseStep 3235187 = 4852781) B4852781
theorem B2156791 : Blo 2155435 2156791 := bstep (se 1 (by rfl) ⟨1617593, by rfl⟩ : syracuseStep 2156791 = 3235187) B3235187
theorem B5182157 : Blo 2155435 5182157 := bbase (se 3 (by rfl) ⟨971654, by rfl⟩ : syracuseStep 5182157 = 1943309) (by norm_num)
theorem B13819085 : Blo 2155435 13819085 := bstep (se 3 (by rfl) ⟨2591078, by rfl⟩ : syracuseStep 13819085 = 5182157) B5182157
theorem B9212723 : Blo 2155435 9212723 := bstep (se 1 (by rfl) ⟨6909542, by rfl⟩ : syracuseStep 9212723 = 13819085) B13819085
theorem B6141815 : Blo 2155435 6141815 := bstep (se 1 (by rfl) ⟨4606361, by rfl⟩ : syracuseStep 6141815 = 9212723) B9212723
theorem B4094543 : Blo 2155435 4094543 := bstep (se 1 (by rfl) ⟨3070907, by rfl⟩ : syracuseStep 4094543 = 6141815) B6141815
theorem B2729695 : Blo 2155435 2729695 := bstep (se 1 (by rfl) ⟨2047271, by rfl⟩ : syracuseStep 2729695 = 4094543) B4094543
theorem B3639593 : Blo 2155435 3639593 := bstep (se 2 (by rfl) ⟨1364847, by rfl⟩ : syracuseStep 3639593 = 2729695) B2729695
theorem B2426395 : Blo 2155435 2426395 := bstep (se 1 (by rfl) ⟨1819796, by rfl⟩ : syracuseStep 2426395 = 3639593) B3639593
theorem B3235193 : Blo 2155435 3235193 := bstep (se 2 (by rfl) ⟨1213197, by rfl⟩ : syracuseStep 3235193 = 2426395) B2426395
theorem B2156795 : Blo 2155435 2156795 := bstep (se 1 (by rfl) ⟨1617596, by rfl⟩ : syracuseStep 2156795 = 3235193) B3235193
theorem B5182165 : Blo 2155435 5182165 := bbase (se 7 (by rfl) ⟨60728, by rfl⟩ : syracuseStep 5182165 = 121457) (by norm_num)
theorem B6909553 : Blo 2155435 6909553 := bstep (se 2 (by rfl) ⟨2591082, by rfl⟩ : syracuseStep 6909553 = 5182165) B5182165
theorem B36850949 : Blo 2155435 36850949 := bstep (se 4 (by rfl) ⟨3454776, by rfl⟩ : syracuseStep 36850949 = 6909553) B6909553
theorem B24567299 : Blo 2155435 24567299 := bstep (se 1 (by rfl) ⟨18425474, by rfl⟩ : syracuseStep 24567299 = 36850949) B36850949
theorem B16378199 : Blo 2155435 16378199 := bstep (se 1 (by rfl) ⟨12283649, by rfl⟩ : syracuseStep 16378199 = 24567299) B24567299
theorem B10918799 : Blo 2155435 10918799 := bstep (se 1 (by rfl) ⟨8189099, by rfl⟩ : syracuseStep 10918799 = 16378199) B16378199
theorem B7279199 : Blo 2155435 7279199 := bstep (se 1 (by rfl) ⟨5459399, by rfl⟩ : syracuseStep 7279199 = 10918799) B10918799
theorem B4852799 : Blo 2155435 4852799 := bstep (se 1 (by rfl) ⟨3639599, by rfl⟩ : syracuseStep 4852799 = 7279199) B7279199
theorem B3235199 : Blo 2155435 3235199 := bstep (se 1 (by rfl) ⟨2426399, by rfl⟩ : syracuseStep 3235199 = 4852799) B4852799
theorem B2156799 : Blo 2155435 2156799 := bstep (se 1 (by rfl) ⟨1617599, by rfl⟩ : syracuseStep 2156799 = 3235199) B3235199
theorem B3235205 : Blo 2155435 3235205 := bbase (se 4 (by rfl) ⟨303300, by rfl⟩ : syracuseStep 3235205 = 606601) (by norm_num)
theorem B2156803 : Blo 2155435 2156803 := bstep (se 1 (by rfl) ⟨1617602, by rfl⟩ : syracuseStep 2156803 = 3235205) B3235205
theorem B3639613 : Blo 2155435 3639613 := bbase (se 3 (by rfl) ⟨682427, by rfl⟩ : syracuseStep 3639613 = 1364855) (by norm_num)
theorem B4852817 : Blo 2155435 4852817 := bstep (se 2 (by rfl) ⟨1819806, by rfl⟩ : syracuseStep 4852817 = 3639613) B3639613
theorem B3235211 : Blo 2155435 3235211 := bstep (se 1 (by rfl) ⟨2426408, by rfl⟩ : syracuseStep 3235211 = 4852817) B4852817
theorem B2156807 : Blo 2155435 2156807 := bstep (se 1 (by rfl) ⟨1617605, by rfl⟩ : syracuseStep 2156807 = 3235211) B3235211
theorem B2426413 : Blo 2155435 2426413 := bbase (se 3 (by rfl) ⟨454952, by rfl⟩ : syracuseStep 2426413 = 909905) (by norm_num)
theorem B3235217 : Blo 2155435 3235217 := bstep (se 2 (by rfl) ⟨1213206, by rfl⟩ : syracuseStep 3235217 = 2426413) B2426413
theorem B2156811 : Blo 2155435 2156811 := bstep (se 1 (by rfl) ⟨1617608, by rfl⟩ : syracuseStep 2156811 = 3235217) B3235217
theorem B7279253 : Blo 2155435 7279253 := bbase (se 6 (by rfl) ⟨170607, by rfl⟩ : syracuseStep 7279253 = 341215) (by norm_num)
theorem B4852835 : Blo 2155435 4852835 := bstep (se 1 (by rfl) ⟨3639626, by rfl⟩ : syracuseStep 4852835 = 7279253) B7279253
theorem B3235223 : Blo 2155435 3235223 := bstep (se 1 (by rfl) ⟨2426417, by rfl⟩ : syracuseStep 3235223 = 4852835) B4852835
theorem B2156815 : Blo 2155435 2156815 := bstep (se 1 (by rfl) ⟨1617611, by rfl⟩ : syracuseStep 2156815 = 3235223) B3235223
theorem B3235229 : Blo 2155435 3235229 := bbase (se 3 (by rfl) ⟨606605, by rfl⟩ : syracuseStep 3235229 = 1213211) (by norm_num)
theorem B2156819 : Blo 2155435 2156819 := bstep (se 1 (by rfl) ⟨1617614, by rfl⟩ : syracuseStep 2156819 = 3235229) B3235229
theorem B4852853 : Blo 2155435 4852853 := bbase (se 5 (by rfl) ⟨227477, by rfl⟩ : syracuseStep 4852853 = 454955) (by norm_num)
theorem B3235235 : Blo 2155435 3235235 := bstep (se 1 (by rfl) ⟨2426426, by rfl⟩ : syracuseStep 3235235 = 4852853) B4852853
theorem B2156823 : Blo 2155435 2156823 := bstep (se 1 (by rfl) ⟨1617617, by rfl⟩ : syracuseStep 2156823 = 3235235) B3235235
theorem B18425717 : Blo 2155435 18425717 := bbase (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) (by norm_num)
theorem B12283811 : Blo 2155435 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B8189207 : Blo 2155435 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B5459471 : Blo 2155435 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B3639647 : Blo 2155435 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B2426431 : Blo 2155435 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B3235241 : Blo 2155435 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B2156827 : Blo 2155435 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B8189221 : Blo 2155435 8189221 := bbase (se 4 (by rfl) ⟨767739, by rfl⟩ : syracuseStep 8189221 = 1535479) (by norm_num)
theorem B10918961 : Blo 2155435 10918961 := bstep (se 2 (by rfl) ⟨4094610, by rfl⟩ : syracuseStep 10918961 = 8189221) B8189221
theorem B7279307 : Blo 2155435 7279307 := bstep (se 1 (by rfl) ⟨5459480, by rfl⟩ : syracuseStep 7279307 = 10918961) B10918961
theorem B4852871 : Blo 2155435 4852871 := bstep (se 1 (by rfl) ⟨3639653, by rfl⟩ : syracuseStep 4852871 = 7279307) B7279307
theorem B3235247 : Blo 2155435 3235247 := bstep (se 1 (by rfl) ⟨2426435, by rfl⟩ : syracuseStep 3235247 = 4852871) B4852871
theorem B2156831 : Blo 2155435 2156831 := bstep (se 1 (by rfl) ⟨1617623, by rfl⟩ : syracuseStep 2156831 = 3235247) B3235247
theorem B3235253 : Blo 2155435 3235253 := bbase (se 5 (by rfl) ⟨151652, by rfl⟩ : syracuseStep 3235253 = 303305) (by norm_num)
theorem B2156835 : Blo 2155435 2156835 := bstep (se 1 (by rfl) ⟨1617626, by rfl⟩ : syracuseStep 2156835 = 3235253) B3235253
theorem B5459501 : Blo 2155435 5459501 := bbase (se 3 (by rfl) ⟨1023656, by rfl⟩ : syracuseStep 5459501 = 2047313) (by norm_num)
theorem B3639667 : Blo 2155435 3639667 := bstep (se 1 (by rfl) ⟨2729750, by rfl⟩ : syracuseStep 3639667 = 5459501) B5459501
theorem B4852889 : Blo 2155435 4852889 := bstep (se 2 (by rfl) ⟨1819833, by rfl⟩ : syracuseStep 4852889 = 3639667) B3639667
theorem B3235259 : Blo 2155435 3235259 := bstep (se 1 (by rfl) ⟨2426444, by rfl⟩ : syracuseStep 3235259 = 4852889) B4852889
theorem B2156839 : Blo 2155435 2156839 := bstep (se 1 (by rfl) ⟨1617629, by rfl⟩ : syracuseStep 2156839 = 3235259) B3235259
theorem B2426449 : Blo 2155435 2426449 := bbase (se 2 (by rfl) ⟨909918, by rfl⟩ : syracuseStep 2426449 = 1819837) (by norm_num)
theorem B3235265 : Blo 2155435 3235265 := bstep (se 2 (by rfl) ⟨1213224, by rfl⟩ : syracuseStep 3235265 = 2426449) B2426449
theorem B2156843 : Blo 2155435 2156843 := bstep (se 1 (by rfl) ⟨1617632, by rfl⟩ : syracuseStep 2156843 = 3235265) B3235265
theorem B3070981 : Blo 2155435 3070981 := bbase (se 4 (by rfl) ⟨287904, by rfl⟩ : syracuseStep 3070981 = 575809) (by norm_num)
theorem B4094641 : Blo 2155435 4094641 := bstep (se 2 (by rfl) ⟨1535490, by rfl⟩ : syracuseStep 4094641 = 3070981) B3070981
theorem B5459521 : Blo 2155435 5459521 := bstep (se 2 (by rfl) ⟨2047320, by rfl⟩ : syracuseStep 5459521 = 4094641) B4094641
theorem B7279361 : Blo 2155435 7279361 := bstep (se 2 (by rfl) ⟨2729760, by rfl⟩ : syracuseStep 7279361 = 5459521) B5459521
theorem B4852907 : Blo 2155435 4852907 := bstep (se 1 (by rfl) ⟨3639680, by rfl⟩ : syracuseStep 4852907 = 7279361) B7279361
theorem B3235271 : Blo 2155435 3235271 := bstep (se 1 (by rfl) ⟨2426453, by rfl⟩ : syracuseStep 3235271 = 4852907) B4852907
theorem B2156847 : Blo 2155435 2156847 := bstep (se 1 (by rfl) ⟨1617635, by rfl⟩ : syracuseStep 2156847 = 3235271) B3235271
theorem B3235277 : Blo 2155435 3235277 := bbase (se 3 (by rfl) ⟨606614, by rfl⟩ : syracuseStep 3235277 = 1213229) (by norm_num)
theorem B2156851 : Blo 2155435 2156851 := bstep (se 1 (by rfl) ⟨1617638, by rfl⟩ : syracuseStep 2156851 = 3235277) B3235277
theorem B4852925 : Blo 2155435 4852925 := bbase (se 3 (by rfl) ⟨909923, by rfl⟩ : syracuseStep 4852925 = 1819847) (by norm_num)
theorem B3235283 : Blo 2155435 3235283 := bstep (se 1 (by rfl) ⟨2426462, by rfl⟩ : syracuseStep 3235283 = 4852925) B4852925
theorem B2156855 : Blo 2155435 2156855 := bstep (se 1 (by rfl) ⟨1617641, by rfl⟩ : syracuseStep 2156855 = 3235283) B3235283
theorem B3639701 : Blo 2155435 3639701 := bbase (se 6 (by rfl) ⟨85305, by rfl⟩ : syracuseStep 3639701 = 170611) (by norm_num)
theorem B2426467 : Blo 2155435 2426467 := bstep (se 1 (by rfl) ⟨1819850, by rfl⟩ : syracuseStep 2426467 = 3639701) B3639701
theorem B3235289 : Blo 2155435 3235289 := bstep (se 2 (by rfl) ⟨1213233, by rfl⟩ : syracuseStep 3235289 = 2426467) B2426467
theorem B2156859 : Blo 2155435 2156859 := bstep (se 1 (by rfl) ⟨1617644, by rfl⟩ : syracuseStep 2156859 = 3235289) B3235289
theorem B2767025 : Blo 2155435 2767025 := bbase (se 2 (by rfl) ⟨1037634, by rfl⟩ : syracuseStep 2767025 = 2075269) (by norm_num)
theorem B7378733 : Blo 2155435 7378733 := bstep (se 3 (by rfl) ⟨1383512, by rfl⟩ : syracuseStep 7378733 = 2767025) B2767025
theorem B19676621 : Blo 2155435 19676621 := bstep (se 3 (by rfl) ⟨3689366, by rfl⟩ : syracuseStep 19676621 = 7378733) B7378733
theorem B13117747 : Blo 2155435 13117747 := bstep (se 1 (by rfl) ⟨9838310, by rfl⟩ : syracuseStep 13117747 = 19676621) B19676621
theorem B17490329 : Blo 2155435 17490329 := bstep (se 2 (by rfl) ⟨6558873, by rfl⟩ : syracuseStep 17490329 = 13117747) B13117747
theorem B11660219 : Blo 2155435 11660219 := bstep (se 1 (by rfl) ⟨8745164, by rfl⟩ : syracuseStep 11660219 = 17490329) B17490329
theorem B7773479 : Blo 2155435 7773479 := bstep (se 1 (by rfl) ⟨5830109, by rfl⟩ : syracuseStep 7773479 = 11660219) B11660219
theorem B5182319 : Blo 2155435 5182319 := bstep (se 1 (by rfl) ⟨3886739, by rfl⟩ : syracuseStep 5182319 = 7773479) B7773479
theorem B13819517 : Blo 2155435 13819517 := bstep (se 3 (by rfl) ⟨2591159, by rfl⟩ : syracuseStep 13819517 = 5182319) B5182319
theorem B9213011 : Blo 2155435 9213011 := bstep (se 1 (by rfl) ⟨6909758, by rfl⟩ : syracuseStep 9213011 = 13819517) B13819517
theorem B6142007 : Blo 2155435 6142007 := bstep (se 1 (by rfl) ⟨4606505, by rfl⟩ : syracuseStep 6142007 = 9213011) B9213011
theorem B16378685 : Blo 2155435 16378685 := bstep (se 3 (by rfl) ⟨3071003, by rfl⟩ : syracuseStep 16378685 = 6142007) B6142007
theorem B10919123 : Blo 2155435 10919123 := bstep (se 1 (by rfl) ⟨8189342, by rfl⟩ : syracuseStep 10919123 = 16378685) B16378685
theorem B7279415 : Blo 2155435 7279415 := bstep (se 1 (by rfl) ⟨5459561, by rfl⟩ : syracuseStep 7279415 = 10919123) B10919123
theorem B4852943 : Blo 2155435 4852943 := bstep (se 1 (by rfl) ⟨3639707, by rfl⟩ : syracuseStep 4852943 = 7279415) B7279415
theorem B3235295 : Blo 2155435 3235295 := bstep (se 1 (by rfl) ⟨2426471, by rfl⟩ : syracuseStep 3235295 = 4852943) B4852943
theorem B2156863 : Blo 2155435 2156863 := bstep (se 1 (by rfl) ⟨1617647, by rfl⟩ : syracuseStep 2156863 = 3235295) B3235295
theorem B3235301 : Blo 2155435 3235301 := bbase (se 4 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 3235301 = 606619) (by norm_num)
theorem B2156867 : Blo 2155435 2156867 := bstep (se 1 (by rfl) ⟨1617650, by rfl⟩ : syracuseStep 2156867 = 3235301) B3235301
theorem B7773509 : Blo 2155435 7773509 := bbase (se 4 (by rfl) ⟨728766, by rfl⟩ : syracuseStep 7773509 = 1457533) (by norm_num)
theorem B20729357 : Blo 2155435 20729357 := bstep (se 3 (by rfl) ⟨3886754, by rfl⟩ : syracuseStep 20729357 = 7773509) B7773509
theorem B13819571 : Blo 2155435 13819571 := bstep (se 1 (by rfl) ⟨10364678, by rfl⟩ : syracuseStep 13819571 = 20729357) B20729357
theorem B9213047 : Blo 2155435 9213047 := bstep (se 1 (by rfl) ⟨6909785, by rfl⟩ : syracuseStep 9213047 = 13819571) B13819571
theorem B6142031 : Blo 2155435 6142031 := bstep (se 1 (by rfl) ⟨4606523, by rfl⟩ : syracuseStep 6142031 = 9213047) B9213047
theorem B4094687 : Blo 2155435 4094687 := bstep (se 1 (by rfl) ⟨3071015, by rfl⟩ : syracuseStep 4094687 = 6142031) B6142031
theorem B2729791 : Blo 2155435 2729791 := bstep (se 1 (by rfl) ⟨2047343, by rfl⟩ : syracuseStep 2729791 = 4094687) B4094687
theorem B3639721 : Blo 2155435 3639721 := bstep (se 2 (by rfl) ⟨1364895, by rfl⟩ : syracuseStep 3639721 = 2729791) B2729791
theorem B4852961 : Blo 2155435 4852961 := bstep (se 2 (by rfl) ⟨1819860, by rfl⟩ : syracuseStep 4852961 = 3639721) B3639721
theorem B3235307 : Blo 2155435 3235307 := bstep (se 1 (by rfl) ⟨2426480, by rfl⟩ : syracuseStep 3235307 = 4852961) B4852961
theorem B2156871 : Blo 2155435 2156871 := bstep (se 1 (by rfl) ⟨1617653, by rfl⟩ : syracuseStep 2156871 = 3235307) B3235307
theorem B2426485 : Blo 2155435 2426485 := bbase (se 5 (by rfl) ⟨113741, by rfl⟩ : syracuseStep 2426485 = 227483) (by norm_num)
theorem B3235313 : Blo 2155435 3235313 := bstep (se 2 (by rfl) ⟨1213242, by rfl⟩ : syracuseStep 3235313 = 2426485) B2426485
theorem B2156875 : Blo 2155435 2156875 := bstep (se 1 (by rfl) ⟨1617656, by rfl⟩ : syracuseStep 2156875 = 3235313) B3235313
theorem B2729801 : Blo 2155435 2729801 := bbase (se 2 (by rfl) ⟨1023675, by rfl⟩ : syracuseStep 2729801 = 2047351) (by norm_num)
theorem B7279469 : Blo 2155435 7279469 := bstep (se 3 (by rfl) ⟨1364900, by rfl⟩ : syracuseStep 7279469 = 2729801) B2729801
theorem B4852979 : Blo 2155435 4852979 := bstep (se 1 (by rfl) ⟨3639734, by rfl⟩ : syracuseStep 4852979 = 7279469) B7279469
theorem B3235319 : Blo 2155435 3235319 := bstep (se 1 (by rfl) ⟨2426489, by rfl⟩ : syracuseStep 3235319 = 4852979) B4852979
theorem B2156879 : Blo 2155435 2156879 := bstep (se 1 (by rfl) ⟨1617659, by rfl⟩ : syracuseStep 2156879 = 3235319) B3235319
theorem B3235325 : Blo 2155435 3235325 := bbase (se 3 (by rfl) ⟨606623, by rfl⟩ : syracuseStep 3235325 = 1213247) (by norm_num)
theorem B2156883 : Blo 2155435 2156883 := bstep (se 1 (by rfl) ⟨1617662, by rfl⟩ : syracuseStep 2156883 = 3235325) B3235325
theorem B4852997 : Blo 2155435 4852997 := bbase (se 4 (by rfl) ⟨454968, by rfl⟩ : syracuseStep 4852997 = 909937) (by norm_num)
theorem B3235331 : Blo 2155435 3235331 := bstep (se 1 (by rfl) ⟨2426498, by rfl⟩ : syracuseStep 3235331 = 4852997) B4852997
theorem B2156887 : Blo 2155435 2156887 := bstep (se 1 (by rfl) ⟨1617665, by rfl⟩ : syracuseStep 2156887 = 3235331) B3235331
theorem B4094725 : Blo 2155435 4094725 := bbase (se 4 (by rfl) ⟨383880, by rfl⟩ : syracuseStep 4094725 = 767761) (by norm_num)
theorem B5459633 : Blo 2155435 5459633 := bstep (se 2 (by rfl) ⟨2047362, by rfl⟩ : syracuseStep 5459633 = 4094725) B4094725
theorem B3639755 : Blo 2155435 3639755 := bstep (se 1 (by rfl) ⟨2729816, by rfl⟩ : syracuseStep 3639755 = 5459633) B5459633
theorem B2426503 : Blo 2155435 2426503 := bstep (se 1 (by rfl) ⟨1819877, by rfl⟩ : syracuseStep 2426503 = 3639755) B3639755
theorem B3235337 : Blo 2155435 3235337 := bstep (se 2 (by rfl) ⟨1213251, by rfl⟩ : syracuseStep 3235337 = 2426503) B2426503
theorem B2156891 : Blo 2155435 2156891 := bstep (se 1 (by rfl) ⟨1617668, by rfl⟩ : syracuseStep 2156891 = 3235337) B3235337
theorem B10919285 : Blo 2155435 10919285 := bbase (se 5 (by rfl) ⟨511841, by rfl⟩ : syracuseStep 10919285 = 1023683) (by norm_num)
theorem B7279523 : Blo 2155435 7279523 := bstep (se 1 (by rfl) ⟨5459642, by rfl⟩ : syracuseStep 7279523 = 10919285) B10919285
theorem B4853015 : Blo 2155435 4853015 := bstep (se 1 (by rfl) ⟨3639761, by rfl⟩ : syracuseStep 4853015 = 7279523) B7279523
theorem B3235343 : Blo 2155435 3235343 := bstep (se 1 (by rfl) ⟨2426507, by rfl⟩ : syracuseStep 3235343 = 4853015) B4853015
theorem B2156895 : Blo 2155435 2156895 := bstep (se 1 (by rfl) ⟨1617671, by rfl⟩ : syracuseStep 2156895 = 3235343) B3235343
theorem B3235349 : Blo 2155435 3235349 := bbase (se 6 (by rfl) ⟨75828, by rfl⟩ : syracuseStep 3235349 = 151657) (by norm_num)
theorem B2156899 : Blo 2155435 2156899 := bstep (se 1 (by rfl) ⟨1617674, by rfl⟩ : syracuseStep 2156899 = 3235349) B3235349
theorem B2626561 : Blo 2155435 2626561 := bbase (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) (by norm_num)
theorem B3502081 : Blo 2155435 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B18677765 : Blo 2155435 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B12451843 : Blo 2155435 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B16602457 : Blo 2155435 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B22136609 : Blo 2155435 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B59030957 : Blo 2155435 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B39353971 : Blo 2155435 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B52471961 : Blo 2155435 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B34981307 : Blo 2155435 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B23320871 : Blo 2155435 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B15547247 : Blo 2155435 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B10364831 : Blo 2155435 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B6909887 : Blo 2155435 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B18426365 : Blo 2155435 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B12284243 : Blo 2155435 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B8189495 : Blo 2155435 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B5459663 : Blo 2155435 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B3639775 : Blo 2155435 3639775 := bstep (se 1 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 3639775 = 5459663) B5459663
theorem B4853033 : Blo 2155435 4853033 := bstep (se 2 (by rfl) ⟨1819887, by rfl⟩ : syracuseStep 4853033 = 3639775) B3639775
theorem B3235355 : Blo 2155435 3235355 := bstep (se 1 (by rfl) ⟨2426516, by rfl⟩ : syracuseStep 3235355 = 4853033) B4853033
theorem B2156903 : Blo 2155435 2156903 := bstep (se 1 (by rfl) ⟨1617677, by rfl⟩ : syracuseStep 2156903 = 3235355) B3235355
theorem B2426521 : Blo 2155435 2426521 := bbase (se 2 (by rfl) ⟨909945, by rfl⟩ : syracuseStep 2426521 = 1819891) (by norm_num)
theorem B3235361 : Blo 2155435 3235361 := bstep (se 2 (by rfl) ⟨1213260, by rfl⟩ : syracuseStep 3235361 = 2426521) B2426521
theorem B2156907 : Blo 2155435 2156907 := bstep (se 1 (by rfl) ⟨1617680, by rfl⟩ : syracuseStep 2156907 = 3235361) B3235361
theorem B8189525 : Blo 2155435 8189525 := bbase (se 8 (by rfl) ⟨47985, by rfl⟩ : syracuseStep 8189525 = 95971) (by norm_num)
theorem B5459683 : Blo 2155435 5459683 := bstep (se 1 (by rfl) ⟨4094762, by rfl⟩ : syracuseStep 5459683 = 8189525) B8189525
theorem B7279577 : Blo 2155435 7279577 := bstep (se 2 (by rfl) ⟨2729841, by rfl⟩ : syracuseStep 7279577 = 5459683) B5459683
theorem B4853051 : Blo 2155435 4853051 := bstep (se 1 (by rfl) ⟨3639788, by rfl⟩ : syracuseStep 4853051 = 7279577) B7279577
theorem B3235367 : Blo 2155435 3235367 := bstep (se 1 (by rfl) ⟨2426525, by rfl⟩ : syracuseStep 3235367 = 4853051) B4853051
theorem B2156911 : Blo 2155435 2156911 := bstep (se 1 (by rfl) ⟨1617683, by rfl⟩ : syracuseStep 2156911 = 3235367) B3235367
theorem B3235373 : Blo 2155435 3235373 := bbase (se 3 (by rfl) ⟨606632, by rfl⟩ : syracuseStep 3235373 = 1213265) (by norm_num)
theorem B2156915 : Blo 2155435 2156915 := bstep (se 1 (by rfl) ⟨1617686, by rfl⟩ : syracuseStep 2156915 = 3235373) B3235373
theorem B4853069 : Blo 2155435 4853069 := bbase (se 3 (by rfl) ⟨909950, by rfl⟩ : syracuseStep 4853069 = 1819901) (by norm_num)
theorem B3235379 : Blo 2155435 3235379 := bstep (se 1 (by rfl) ⟨2426534, by rfl⟩ : syracuseStep 3235379 = 4853069) B4853069
theorem B2156919 : Blo 2155435 2156919 := bstep (se 1 (by rfl) ⟨1617689, by rfl⟩ : syracuseStep 2156919 = 3235379) B3235379
theorem B2729857 : Blo 2155435 2729857 := bbase (se 2 (by rfl) ⟨1023696, by rfl⟩ : syracuseStep 2729857 = 2047393) (by norm_num)
theorem B3639809 : Blo 2155435 3639809 := bstep (se 2 (by rfl) ⟨1364928, by rfl⟩ : syracuseStep 3639809 = 2729857) B2729857
theorem B2426539 : Blo 2155435 2426539 := bstep (se 1 (by rfl) ⟨1819904, by rfl⟩ : syracuseStep 2426539 = 3639809) B3639809
theorem B3235385 : Blo 2155435 3235385 := bstep (se 2 (by rfl) ⟨1213269, by rfl⟩ : syracuseStep 3235385 = 2426539) B2426539
theorem B2156923 : Blo 2155435 2156923 := bstep (se 1 (by rfl) ⟨1617692, by rfl⟩ : syracuseStep 2156923 = 3235385) B3235385
theorem B2303321 : Blo 2155435 2303321 := bbase (se 2 (by rfl) ⟨863745, by rfl⟩ : syracuseStep 2303321 = 1727491) (by norm_num)
theorem B24568757 : Blo 2155435 24568757 := bstep (se 5 (by rfl) ⟨1151660, by rfl⟩ : syracuseStep 24568757 = 2303321) B2303321
theorem B16379171 : Blo 2155435 16379171 := bstep (se 1 (by rfl) ⟨12284378, by rfl⟩ : syracuseStep 16379171 = 24568757) B24568757
theorem B10919447 : Blo 2155435 10919447 := bstep (se 1 (by rfl) ⟨8189585, by rfl⟩ : syracuseStep 10919447 = 16379171) B16379171
theorem B7279631 : Blo 2155435 7279631 := bstep (se 1 (by rfl) ⟨5459723, by rfl⟩ : syracuseStep 7279631 = 10919447) B10919447
theorem B4853087 : Blo 2155435 4853087 := bstep (se 1 (by rfl) ⟨3639815, by rfl⟩ : syracuseStep 4853087 = 7279631) B7279631
theorem B3235391 : Blo 2155435 3235391 := bstep (se 1 (by rfl) ⟨2426543, by rfl⟩ : syracuseStep 3235391 = 4853087) B4853087
theorem B2156927 : Blo 2155435 2156927 := bstep (se 1 (by rfl) ⟨1617695, by rfl⟩ : syracuseStep 2156927 = 3235391) B3235391
theorem B3235397 : Blo 2155435 3235397 := bbase (se 4 (by rfl) ⟨303318, by rfl⟩ : syracuseStep 3235397 = 606637) (by norm_num)
theorem B2156931 : Blo 2155435 2156931 := bstep (se 1 (by rfl) ⟨1617698, by rfl⟩ : syracuseStep 2156931 = 3235397) B3235397
theorem B3639829 : Blo 2155435 3639829 := bbase (se 6 (by rfl) ⟨85308, by rfl⟩ : syracuseStep 3639829 = 170617) (by norm_num)
theorem B4853105 : Blo 2155435 4853105 := bstep (se 2 (by rfl) ⟨1819914, by rfl⟩ : syracuseStep 4853105 = 3639829) B3639829
theorem B3235403 : Blo 2155435 3235403 := bstep (se 1 (by rfl) ⟨2426552, by rfl⟩ : syracuseStep 3235403 = 4853105) B4853105
theorem B2156935 : Blo 2155435 2156935 := bstep (se 1 (by rfl) ⟨1617701, by rfl⟩ : syracuseStep 2156935 = 3235403) B3235403
theorem B2426557 : Blo 2155435 2426557 := bbase (se 3 (by rfl) ⟨454979, by rfl⟩ : syracuseStep 2426557 = 909959) (by norm_num)
theorem B3235409 : Blo 2155435 3235409 := bstep (se 2 (by rfl) ⟨1213278, by rfl⟩ : syracuseStep 3235409 = 2426557) B2426557
theorem B2156939 : Blo 2155435 2156939 := bstep (se 1 (by rfl) ⟨1617704, by rfl⟩ : syracuseStep 2156939 = 3235409) B3235409
theorem B7279685 : Blo 2155435 7279685 := bbase (se 4 (by rfl) ⟨682470, by rfl⟩ : syracuseStep 7279685 = 1364941) (by norm_num)
theorem B4853123 : Blo 2155435 4853123 := bstep (se 1 (by rfl) ⟨3639842, by rfl⟩ : syracuseStep 4853123 = 7279685) B7279685
theorem B3235415 : Blo 2155435 3235415 := bstep (se 1 (by rfl) ⟨2426561, by rfl⟩ : syracuseStep 3235415 = 4853123) B4853123
theorem B2156943 : Blo 2155435 2156943 := bstep (se 1 (by rfl) ⟨1617707, by rfl⟩ : syracuseStep 2156943 = 3235415) B3235415
theorem B3235421 : Blo 2155435 3235421 := bbase (se 3 (by rfl) ⟨606641, by rfl⟩ : syracuseStep 3235421 = 1213283) (by norm_num)
theorem B2156947 : Blo 2155435 2156947 := bstep (se 1 (by rfl) ⟨1617710, by rfl⟩ : syracuseStep 2156947 = 3235421) B3235421
theorem B4853141 : Blo 2155435 4853141 := bbase (se 6 (by rfl) ⟨113745, by rfl⟩ : syracuseStep 4853141 = 227491) (by norm_num)
theorem B3235427 : Blo 2155435 3235427 := bstep (se 1 (by rfl) ⟨2426570, by rfl⟩ : syracuseStep 3235427 = 4853141) B4853141
theorem B2156951 : Blo 2155435 2156951 := bstep (se 1 (by rfl) ⟨1617713, by rfl⟩ : syracuseStep 2156951 = 3235427) B3235427
theorem B2626625 : Blo 2155435 2626625 := bbase (se 2 (by rfl) ⟨984984, by rfl⟩ : syracuseStep 2626625 = 1969969) (by norm_num)
theorem B7004333 : Blo 2155435 7004333 := bstep (se 3 (by rfl) ⟨1313312, by rfl⟩ : syracuseStep 7004333 = 2626625) B2626625
theorem B18678221 : Blo 2155435 18678221 := bstep (se 3 (by rfl) ⟨3502166, by rfl⟩ : syracuseStep 18678221 = 7004333) B7004333
theorem B12452147 : Blo 2155435 12452147 := bstep (se 1 (by rfl) ⟨9339110, by rfl⟩ : syracuseStep 12452147 = 18678221) B18678221
theorem B8301431 : Blo 2155435 8301431 := bstep (se 1 (by rfl) ⟨6226073, by rfl⟩ : syracuseStep 8301431 = 12452147) B12452147
theorem B5534287 : Blo 2155435 5534287 := bstep (se 1 (by rfl) ⟨4150715, by rfl⟩ : syracuseStep 5534287 = 8301431) B8301431
theorem B29516197 : Blo 2155435 29516197 := bstep (se 4 (by rfl) ⟨2767143, by rfl⟩ : syracuseStep 29516197 = 5534287) B5534287
theorem B39354929 : Blo 2155435 39354929 := bstep (se 2 (by rfl) ⟨14758098, by rfl⟩ : syracuseStep 39354929 = 29516197) B29516197
theorem B26236619 : Blo 2155435 26236619 := bstep (se 1 (by rfl) ⟨19677464, by rfl⟩ : syracuseStep 26236619 = 39354929) B39354929
theorem B17491079 : Blo 2155435 17491079 := bstep (se 1 (by rfl) ⟨13118309, by rfl⟩ : syracuseStep 17491079 = 26236619) B26236619
theorem B11660719 : Blo 2155435 11660719 := bstep (se 1 (by rfl) ⟨8745539, by rfl⟩ : syracuseStep 11660719 = 17491079) B17491079
theorem B15547625 : Blo 2155435 15547625 := bstep (se 2 (by rfl) ⟨5830359, by rfl⟩ : syracuseStep 15547625 = 11660719) B11660719
theorem B10365083 : Blo 2155435 10365083 := bstep (se 1 (by rfl) ⟨7773812, by rfl⟩ : syracuseStep 10365083 = 15547625) B15547625
theorem B6910055 : Blo 2155435 6910055 := bstep (se 1 (by rfl) ⟨5182541, by rfl⟩ : syracuseStep 6910055 = 10365083) B10365083
theorem B4606703 : Blo 2155435 4606703 := bstep (se 1 (by rfl) ⟨3455027, by rfl⟩ : syracuseStep 4606703 = 6910055) B6910055
theorem B3071135 : Blo 2155435 3071135 := bstep (se 1 (by rfl) ⟨2303351, by rfl⟩ : syracuseStep 3071135 = 4606703) B4606703
theorem B8189693 : Blo 2155435 8189693 := bstep (se 3 (by rfl) ⟨1535567, by rfl⟩ : syracuseStep 8189693 = 3071135) B3071135
theorem B5459795 : Blo 2155435 5459795 := bstep (se 1 (by rfl) ⟨4094846, by rfl⟩ : syracuseStep 5459795 = 8189693) B8189693
theorem B3639863 : Blo 2155435 3639863 := bstep (se 1 (by rfl) ⟨2729897, by rfl⟩ : syracuseStep 3639863 = 5459795) B5459795
theorem B2426575 : Blo 2155435 2426575 := bstep (se 1 (by rfl) ⟨1819931, by rfl⟩ : syracuseStep 2426575 = 3639863) B3639863
theorem B3235433 : Blo 2155435 3235433 := bstep (se 2 (by rfl) ⟨1213287, by rfl⟩ : syracuseStep 3235433 = 2426575) B2426575
theorem B2156955 : Blo 2155435 2156955 := bstep (se 1 (by rfl) ⟨1617716, by rfl⟩ : syracuseStep 2156955 = 3235433) B3235433
theorem B2186389 : Blo 2155435 2186389 := bbase (se 6 (by rfl) ⟨51243, by rfl⟩ : syracuseStep 2186389 = 102487) (by norm_num)
theorem B2915185 : Blo 2155435 2915185 := bstep (se 2 (by rfl) ⟨1093194, by rfl⟩ : syracuseStep 2915185 = 2186389) B2186389
theorem B3886913 : Blo 2155435 3886913 := bstep (se 2 (by rfl) ⟨1457592, by rfl⟩ : syracuseStep 3886913 = 2915185) B2915185
theorem B2591275 : Blo 2155435 2591275 := bstep (se 1 (by rfl) ⟨1943456, by rfl⟩ : syracuseStep 2591275 = 3886913) B3886913
theorem B3455033 : Blo 2155435 3455033 := bstep (se 2 (by rfl) ⟨1295637, by rfl⟩ : syracuseStep 3455033 = 2591275) B2591275
theorem B9213421 : Blo 2155435 9213421 := bstep (se 3 (by rfl) ⟨1727516, by rfl⟩ : syracuseStep 9213421 = 3455033) B3455033
theorem B12284561 : Blo 2155435 12284561 := bstep (se 2 (by rfl) ⟨4606710, by rfl⟩ : syracuseStep 12284561 = 9213421) B9213421
theorem B8189707 : Blo 2155435 8189707 := bstep (se 1 (by rfl) ⟨6142280, by rfl⟩ : syracuseStep 8189707 = 12284561) B12284561
theorem B10919609 : Blo 2155435 10919609 := bstep (se 2 (by rfl) ⟨4094853, by rfl⟩ : syracuseStep 10919609 = 8189707) B8189707
theorem B7279739 : Blo 2155435 7279739 := bstep (se 1 (by rfl) ⟨5459804, by rfl⟩ : syracuseStep 7279739 = 10919609) B10919609
theorem B4853159 : Blo 2155435 4853159 := bstep (se 1 (by rfl) ⟨3639869, by rfl⟩ : syracuseStep 4853159 = 7279739) B7279739
theorem B3235439 : Blo 2155435 3235439 := bstep (se 1 (by rfl) ⟨2426579, by rfl⟩ : syracuseStep 3235439 = 4853159) B4853159
theorem B2156959 : Blo 2155435 2156959 := bstep (se 1 (by rfl) ⟨1617719, by rfl⟩ : syracuseStep 2156959 = 3235439) B3235439
theorem B3235445 : Blo 2155435 3235445 := bbase (se 5 (by rfl) ⟨151661, by rfl⟩ : syracuseStep 3235445 = 303323) (by norm_num)
theorem B2156963 : Blo 2155435 2156963 := bstep (se 1 (by rfl) ⟨1617722, by rfl⟩ : syracuseStep 2156963 = 3235445) B3235445
theorem B4094869 : Blo 2155435 4094869 := bbase (se 6 (by rfl) ⟨95973, by rfl⟩ : syracuseStep 4094869 = 191947) (by norm_num)
theorem B5459825 : Blo 2155435 5459825 := bstep (se 2 (by rfl) ⟨2047434, by rfl⟩ : syracuseStep 5459825 = 4094869) B4094869
theorem B3639883 : Blo 2155435 3639883 := bstep (se 1 (by rfl) ⟨2729912, by rfl⟩ : syracuseStep 3639883 = 5459825) B5459825
theorem B4853177 : Blo 2155435 4853177 := bstep (se 2 (by rfl) ⟨1819941, by rfl⟩ : syracuseStep 4853177 = 3639883) B3639883
theorem B3235451 : Blo 2155435 3235451 := bstep (se 1 (by rfl) ⟨2426588, by rfl⟩ : syracuseStep 3235451 = 4853177) B4853177
theorem B2156967 : Blo 2155435 2156967 := bstep (se 1 (by rfl) ⟨1617725, by rfl⟩ : syracuseStep 2156967 = 3235451) B3235451
theorem B2426593 : Blo 2155435 2426593 := bbase (se 2 (by rfl) ⟨909972, by rfl⟩ : syracuseStep 2426593 = 1819945) (by norm_num)
theorem B3235457 : Blo 2155435 3235457 := bstep (se 2 (by rfl) ⟨1213296, by rfl⟩ : syracuseStep 3235457 = 2426593) B2426593
theorem B2156971 : Blo 2155435 2156971 := bstep (se 1 (by rfl) ⟨1617728, by rfl⟩ : syracuseStep 2156971 = 3235457) B3235457
theorem B5459845 : Blo 2155435 5459845 := bbase (se 4 (by rfl) ⟨511860, by rfl⟩ : syracuseStep 5459845 = 1023721) (by norm_num)
theorem B7279793 : Blo 2155435 7279793 := bstep (se 2 (by rfl) ⟨2729922, by rfl⟩ : syracuseStep 7279793 = 5459845) B5459845
theorem B4853195 : Blo 2155435 4853195 := bstep (se 1 (by rfl) ⟨3639896, by rfl⟩ : syracuseStep 4853195 = 7279793) B7279793
theorem B3235463 : Blo 2155435 3235463 := bstep (se 1 (by rfl) ⟨2426597, by rfl⟩ : syracuseStep 3235463 = 4853195) B4853195
theorem B2156975 : Blo 2155435 2156975 := bstep (se 1 (by rfl) ⟨1617731, by rfl⟩ : syracuseStep 2156975 = 3235463) B3235463
theorem B3235469 : Blo 2155435 3235469 := bbase (se 3 (by rfl) ⟨606650, by rfl⟩ : syracuseStep 3235469 = 1213301) (by norm_num)
theorem B2156979 : Blo 2155435 2156979 := bstep (se 1 (by rfl) ⟨1617734, by rfl⟩ : syracuseStep 2156979 = 3235469) B3235469
theorem B4853213 : Blo 2155435 4853213 := bbase (se 3 (by rfl) ⟨909977, by rfl⟩ : syracuseStep 4853213 = 1819955) (by norm_num)
theorem B3235475 : Blo 2155435 3235475 := bstep (se 1 (by rfl) ⟨2426606, by rfl⟩ : syracuseStep 3235475 = 4853213) B4853213
theorem B2156983 : Blo 2155435 2156983 := bstep (se 1 (by rfl) ⟨1617737, by rfl⟩ : syracuseStep 2156983 = 3235475) B3235475
theorem B3639917 : Blo 2155435 3639917 := bbase (se 3 (by rfl) ⟨682484, by rfl⟩ : syracuseStep 3639917 = 1364969) (by norm_num)
theorem B2426611 : Blo 2155435 2426611 := bstep (se 1 (by rfl) ⟨1819958, by rfl⟩ : syracuseStep 2426611 = 3639917) B3639917
theorem B3235481 : Blo 2155435 3235481 := bstep (se 2 (by rfl) ⟨1213305, by rfl⟩ : syracuseStep 3235481 = 2426611) B2426611
theorem B2156987 : Blo 2155435 2156987 := bstep (se 1 (by rfl) ⟨1617740, by rfl⟩ : syracuseStep 2156987 = 3235481) B3235481
theorem B4986565 : Blo 2155435 4986565 := bbase (se 4 (by rfl) ⟨467490, by rfl⟩ : syracuseStep 4986565 = 934981) (by norm_num)
theorem B106380053 : Blo 2155435 106380053 := bstep (se 6 (by rfl) ⟨2493282, by rfl⟩ : syracuseStep 106380053 = 4986565) B4986565
theorem B70920035 : Blo 2155435 70920035 := bstep (se 1 (by rfl) ⟨53190026, by rfl⟩ : syracuseStep 70920035 = 106380053) B106380053
theorem B47280023 : Blo 2155435 47280023 := bstep (se 1 (by rfl) ⟨35460017, by rfl⟩ : syracuseStep 47280023 = 70920035) B70920035
theorem B31520015 : Blo 2155435 31520015 := bstep (se 1 (by rfl) ⟨23640011, by rfl⟩ : syracuseStep 31520015 = 47280023) B47280023
theorem B21013343 : Blo 2155435 21013343 := bstep (se 1 (by rfl) ⟨15760007, by rfl⟩ : syracuseStep 21013343 = 31520015) B31520015
theorem B14008895 : Blo 2155435 14008895 := bstep (se 1 (by rfl) ⟨10506671, by rfl⟩ : syracuseStep 14008895 = 21013343) B21013343
theorem B9339263 : Blo 2155435 9339263 := bstep (se 1 (by rfl) ⟨7004447, by rfl⟩ : syracuseStep 9339263 = 14008895) B14008895
theorem B6226175 : Blo 2155435 6226175 := bstep (se 1 (by rfl) ⟨4669631, by rfl⟩ : syracuseStep 6226175 = 9339263) B9339263
theorem B4150783 : Blo 2155435 4150783 := bstep (se 1 (by rfl) ⟨3113087, by rfl⟩ : syracuseStep 4150783 = 6226175) B6226175
theorem B22137509 : Blo 2155435 22137509 := bstep (se 4 (by rfl) ⟨2075391, by rfl⟩ : syracuseStep 22137509 = 4150783) B4150783
theorem B59033357 : Blo 2155435 59033357 := bstep (se 3 (by rfl) ⟨11068754, by rfl⟩ : syracuseStep 59033357 = 22137509) B22137509
theorem B39355571 : Blo 2155435 39355571 := bstep (se 1 (by rfl) ⟨29516678, by rfl⟩ : syracuseStep 39355571 = 59033357) B59033357
theorem B26237047 : Blo 2155435 26237047 := bstep (se 1 (by rfl) ⟨19677785, by rfl⟩ : syracuseStep 26237047 = 39355571) B39355571
theorem B34982729 : Blo 2155435 34982729 := bstep (se 2 (by rfl) ⟨13118523, by rfl⟩ : syracuseStep 34982729 = 26237047) B26237047
theorem B23321819 : Blo 2155435 23321819 := bstep (se 1 (by rfl) ⟨17491364, by rfl⟩ : syracuseStep 23321819 = 34982729) B34982729
theorem B15547879 : Blo 2155435 15547879 := bstep (se 1 (by rfl) ⟨11660909, by rfl⟩ : syracuseStep 15547879 = 23321819) B23321819
theorem B20730505 : Blo 2155435 20730505 := bstep (se 2 (by rfl) ⟨7773939, by rfl⟩ : syracuseStep 20730505 = 15547879) B15547879
theorem B27640673 : Blo 2155435 27640673 := bstep (se 2 (by rfl) ⟨10365252, by rfl⟩ : syracuseStep 27640673 = 20730505) B20730505
theorem B18427115 : Blo 2155435 18427115 := bstep (se 1 (by rfl) ⟨13820336, by rfl⟩ : syracuseStep 18427115 = 27640673) B27640673
theorem B12284743 : Blo 2155435 12284743 := bstep (se 1 (by rfl) ⟨9213557, by rfl⟩ : syracuseStep 12284743 = 18427115) B18427115
theorem B16379657 : Blo 2155435 16379657 := bstep (se 2 (by rfl) ⟨6142371, by rfl⟩ : syracuseStep 16379657 = 12284743) B12284743
theorem B10919771 : Blo 2155435 10919771 := bstep (se 1 (by rfl) ⟨8189828, by rfl⟩ : syracuseStep 10919771 = 16379657) B16379657
theorem B7279847 : Blo 2155435 7279847 := bstep (se 1 (by rfl) ⟨5459885, by rfl⟩ : syracuseStep 7279847 = 10919771) B10919771
theorem B4853231 : Blo 2155435 4853231 := bstep (se 1 (by rfl) ⟨3639923, by rfl⟩ : syracuseStep 4853231 = 7279847) B7279847
theorem B3235487 : Blo 2155435 3235487 := bstep (se 1 (by rfl) ⟨2426615, by rfl⟩ : syracuseStep 3235487 = 4853231) B4853231
theorem B2156991 : Blo 2155435 2156991 := bstep (se 1 (by rfl) ⟨1617743, by rfl⟩ : syracuseStep 2156991 = 3235487) B3235487
theorem B3235493 : Blo 2155435 3235493 := bbase (se 4 (by rfl) ⟨303327, by rfl⟩ : syracuseStep 3235493 = 606655) (by norm_num)
theorem B2156995 : Blo 2155435 2156995 := bstep (se 1 (by rfl) ⟨1617746, by rfl⟩ : syracuseStep 2156995 = 3235493) B3235493
theorem B2729953 : Blo 2155435 2729953 := bbase (se 2 (by rfl) ⟨1023732, by rfl⟩ : syracuseStep 2729953 = 2047465) (by norm_num)
theorem B3639937 : Blo 2155435 3639937 := bstep (se 2 (by rfl) ⟨1364976, by rfl⟩ : syracuseStep 3639937 = 2729953) B2729953
theorem B4853249 : Blo 2155435 4853249 := bstep (se 2 (by rfl) ⟨1819968, by rfl⟩ : syracuseStep 4853249 = 3639937) B3639937
theorem B3235499 : Blo 2155435 3235499 := bstep (se 1 (by rfl) ⟨2426624, by rfl⟩ : syracuseStep 3235499 = 4853249) B4853249
theorem B2156999 : Blo 2155435 2156999 := bstep (se 1 (by rfl) ⟨1617749, by rfl⟩ : syracuseStep 2156999 = 3235499) B3235499
theorem B2426629 : Blo 2155435 2426629 := bbase (se 4 (by rfl) ⟨227496, by rfl⟩ : syracuseStep 2426629 = 454993) (by norm_num)
theorem B3235505 : Blo 2155435 3235505 := bstep (se 2 (by rfl) ⟨1213314, by rfl⟩ : syracuseStep 3235505 = 2426629) B2426629
theorem B2157003 : Blo 2155435 2157003 := bstep (se 1 (by rfl) ⟨1617752, by rfl⟩ : syracuseStep 2157003 = 3235505) B3235505
theorem B5830501 : Blo 2155435 5830501 := bbase (se 4 (by rfl) ⟨546609, by rfl⟩ : syracuseStep 5830501 = 1093219) (by norm_num)
theorem B7774001 : Blo 2155435 7774001 := bstep (se 2 (by rfl) ⟨2915250, by rfl⟩ : syracuseStep 7774001 = 5830501) B5830501
theorem B5182667 : Blo 2155435 5182667 := bstep (se 1 (by rfl) ⟨3887000, by rfl⟩ : syracuseStep 5182667 = 7774001) B7774001
theorem B3455111 : Blo 2155435 3455111 := bstep (se 1 (by rfl) ⟨2591333, by rfl⟩ : syracuseStep 3455111 = 5182667) B5182667
theorem B2303407 : Blo 2155435 2303407 := bstep (se 1 (by rfl) ⟨1727555, by rfl⟩ : syracuseStep 2303407 = 3455111) B3455111
theorem B3071209 : Blo 2155435 3071209 := bstep (se 2 (by rfl) ⟨1151703, by rfl⟩ : syracuseStep 3071209 = 2303407) B2303407
theorem B4094945 : Blo 2155435 4094945 := bstep (se 2 (by rfl) ⟨1535604, by rfl⟩ : syracuseStep 4094945 = 3071209) B3071209
theorem B2729963 : Blo 2155435 2729963 := bstep (se 1 (by rfl) ⟨2047472, by rfl⟩ : syracuseStep 2729963 = 4094945) B4094945
theorem B7279901 : Blo 2155435 7279901 := bstep (se 3 (by rfl) ⟨1364981, by rfl⟩ : syracuseStep 7279901 = 2729963) B2729963
theorem B4853267 : Blo 2155435 4853267 := bstep (se 1 (by rfl) ⟨3639950, by rfl⟩ : syracuseStep 4853267 = 7279901) B7279901
theorem B3235511 : Blo 2155435 3235511 := bstep (se 1 (by rfl) ⟨2426633, by rfl⟩ : syracuseStep 3235511 = 4853267) B4853267
theorem B2157007 : Blo 2155435 2157007 := bstep (se 1 (by rfl) ⟨1617755, by rfl⟩ : syracuseStep 2157007 = 3235511) B3235511
theorem B3235517 : Blo 2155435 3235517 := bbase (se 3 (by rfl) ⟨606659, by rfl⟩ : syracuseStep 3235517 = 1213319) (by norm_num)
theorem B2157011 : Blo 2155435 2157011 := bstep (se 1 (by rfl) ⟨1617758, by rfl⟩ : syracuseStep 2157011 = 3235517) B3235517
theorem B4853285 : Blo 2155435 4853285 := bbase (se 4 (by rfl) ⟨454995, by rfl⟩ : syracuseStep 4853285 = 909991) (by norm_num)
theorem B3235523 : Blo 2155435 3235523 := bstep (se 1 (by rfl) ⟨2426642, by rfl⟩ : syracuseStep 3235523 = 4853285) B4853285
theorem B2157015 : Blo 2155435 2157015 := bstep (se 1 (by rfl) ⟨1617761, by rfl⟩ : syracuseStep 2157015 = 3235523) B3235523
theorem B5459957 : Blo 2155435 5459957 := bbase (se 5 (by rfl) ⟨255935, by rfl⟩ : syracuseStep 5459957 = 511871) (by norm_num)
theorem B3639971 : Blo 2155435 3639971 := bstep (se 1 (by rfl) ⟨2729978, by rfl⟩ : syracuseStep 3639971 = 5459957) B5459957
theorem B2426647 : Blo 2155435 2426647 := bstep (se 1 (by rfl) ⟨1819985, by rfl⟩ : syracuseStep 2426647 = 3639971) B3639971
theorem B3235529 : Blo 2155435 3235529 := bstep (se 2 (by rfl) ⟨1213323, by rfl⟩ : syracuseStep 3235529 = 2426647) B2426647
theorem B2157019 : Blo 2155435 2157019 := bstep (se 1 (by rfl) ⟨1617764, by rfl⟩ : syracuseStep 2157019 = 3235529) B3235529
theorem B12144917 : Blo 2155435 12144917 := bbase (se 6 (by rfl) ⟨284646, by rfl⟩ : syracuseStep 12144917 = 569293) (by norm_num)
theorem B8096611 : Blo 2155435 8096611 := bstep (se 1 (by rfl) ⟨6072458, by rfl⟩ : syracuseStep 8096611 = 12144917) B12144917
theorem B10795481 : Blo 2155435 10795481 := bstep (se 2 (by rfl) ⟨4048305, by rfl⟩ : syracuseStep 10795481 = 8096611) B8096611
theorem B7196987 : Blo 2155435 7196987 := bstep (se 1 (by rfl) ⟨5397740, by rfl⟩ : syracuseStep 7196987 = 10795481) B10795481
theorem B4797991 : Blo 2155435 4797991 := bstep (se 1 (by rfl) ⟨3598493, by rfl⟩ : syracuseStep 4797991 = 7196987) B7196987
theorem B6397321 : Blo 2155435 6397321 := bstep (se 2 (by rfl) ⟨2398995, by rfl⟩ : syracuseStep 6397321 = 4797991) B4797991
theorem B8529761 : Blo 2155435 8529761 := bstep (se 2 (by rfl) ⟨3198660, by rfl⟩ : syracuseStep 8529761 = 6397321) B6397321
theorem B5686507 : Blo 2155435 5686507 := bstep (se 1 (by rfl) ⟨4264880, by rfl⟩ : syracuseStep 5686507 = 8529761) B8529761
theorem B7582009 : Blo 2155435 7582009 := bstep (se 2 (by rfl) ⟨2843253, by rfl⟩ : syracuseStep 7582009 = 5686507) B5686507
theorem B10109345 : Blo 2155435 10109345 := bstep (se 2 (by rfl) ⟨3791004, by rfl⟩ : syracuseStep 10109345 = 7582009) B7582009
theorem B26958253 : Blo 2155435 26958253 := bstep (se 3 (by rfl) ⟨5054672, by rfl⟩ : syracuseStep 26958253 = 10109345) B10109345
theorem B35944337 : Blo 2155435 35944337 := bstep (se 2 (by rfl) ⟨13479126, by rfl⟩ : syracuseStep 35944337 = 26958253) B26958253
theorem B95851565 : Blo 2155435 95851565 := bstep (se 3 (by rfl) ⟨17972168, by rfl⟩ : syracuseStep 95851565 = 35944337) B35944337
theorem B63901043 : Blo 2155435 63901043 := bstep (se 1 (by rfl) ⟨47925782, by rfl⟩ : syracuseStep 63901043 = 95851565) B95851565
theorem B42600695 : Blo 2155435 42600695 := bstep (se 1 (by rfl) ⟨31950521, by rfl⟩ : syracuseStep 42600695 = 63901043) B63901043
theorem B113601853 : Blo 2155435 113601853 := bstep (se 3 (by rfl) ⟨21300347, by rfl⟩ : syracuseStep 113601853 = 42600695) B42600695
theorem B151469137 : Blo 2155435 151469137 := bstep (se 2 (by rfl) ⟨56800926, by rfl⟩ : syracuseStep 151469137 = 113601853) B113601853
theorem B201958849 : Blo 2155435 201958849 := bstep (se 2 (by rfl) ⟨75734568, by rfl⟩ : syracuseStep 201958849 = 151469137) B151469137
theorem B269278465 : Blo 2155435 269278465 := bstep (se 2 (by rfl) ⟨100979424, by rfl⟩ : syracuseStep 269278465 = 201958849) B201958849
theorem B359037953 : Blo 2155435 359037953 := bstep (se 2 (by rfl) ⟨134639232, by rfl⟩ : syracuseStep 359037953 = 269278465) B269278465
theorem B239358635 : Blo 2155435 239358635 := bstep (se 1 (by rfl) ⟨179518976, by rfl⟩ : syracuseStep 239358635 = 359037953) B359037953
theorem B159572423 : Blo 2155435 159572423 := bstep (se 1 (by rfl) ⟨119679317, by rfl⟩ : syracuseStep 159572423 = 239358635) B239358635
theorem B106381615 : Blo 2155435 106381615 := bstep (se 1 (by rfl) ⟨79786211, by rfl⟩ : syracuseStep 106381615 = 159572423) B159572423
theorem B141842153 : Blo 2155435 141842153 := bstep (se 2 (by rfl) ⟨53190807, by rfl⟩ : syracuseStep 141842153 = 106381615) B106381615
theorem B94561435 : Blo 2155435 94561435 := bstep (se 1 (by rfl) ⟨70921076, by rfl⟩ : syracuseStep 94561435 = 141842153) B141842153
theorem B504327653 : Blo 2155435 504327653 := bstep (se 4 (by rfl) ⟨47280717, by rfl⟩ : syracuseStep 504327653 = 94561435) B94561435
theorem B336218435 : Blo 2155435 336218435 := bstep (se 1 (by rfl) ⟨252163826, by rfl⟩ : syracuseStep 336218435 = 504327653) B504327653
theorem B224145623 : Blo 2155435 224145623 := bstep (se 1 (by rfl) ⟨168109217, by rfl⟩ : syracuseStep 224145623 = 336218435) B336218435
theorem B149430415 : Blo 2155435 149430415 := bstep (se 1 (by rfl) ⟨112072811, by rfl⟩ : syracuseStep 149430415 = 224145623) B224145623
theorem B199240553 : Blo 2155435 199240553 := bstep (se 2 (by rfl) ⟨74715207, by rfl⟩ : syracuseStep 199240553 = 149430415) B149430415
theorem B132827035 : Blo 2155435 132827035 := bstep (se 1 (by rfl) ⟨99620276, by rfl⟩ : syracuseStep 132827035 = 199240553) B199240553
theorem B177102713 : Blo 2155435 177102713 := bstep (se 2 (by rfl) ⟨66413517, by rfl⟩ : syracuseStep 177102713 = 132827035) B132827035
theorem B118068475 : Blo 2155435 118068475 := bstep (se 1 (by rfl) ⟨88551356, by rfl⟩ : syracuseStep 118068475 = 177102713) B177102713
theorem B157424633 : Blo 2155435 157424633 := bstep (se 2 (by rfl) ⟨59034237, by rfl⟩ : syracuseStep 157424633 = 118068475) B118068475
theorem B104949755 : Blo 2155435 104949755 := bstep (se 1 (by rfl) ⟨78712316, by rfl⟩ : syracuseStep 104949755 = 157424633) B157424633
theorem B69966503 : Blo 2155435 69966503 := bstep (se 1 (by rfl) ⟨52474877, by rfl⟩ : syracuseStep 69966503 = 104949755) B104949755
theorem B46644335 : Blo 2155435 46644335 := bstep (se 1 (by rfl) ⟨34983251, by rfl⟩ : syracuseStep 46644335 = 69966503) B69966503
theorem B31096223 : Blo 2155435 31096223 := bstep (se 1 (by rfl) ⟨23322167, by rfl⟩ : syracuseStep 31096223 = 46644335) B46644335
theorem B20730815 : Blo 2155435 20730815 := bstep (se 1 (by rfl) ⟨15548111, by rfl⟩ : syracuseStep 20730815 = 31096223) B31096223
theorem B13820543 : Blo 2155435 13820543 := bstep (se 1 (by rfl) ⟨10365407, by rfl⟩ : syracuseStep 13820543 = 20730815) B20730815
theorem B9213695 : Blo 2155435 9213695 := bstep (se 1 (by rfl) ⟨6910271, by rfl⟩ : syracuseStep 9213695 = 13820543) B13820543
theorem B6142463 : Blo 2155435 6142463 := bstep (se 1 (by rfl) ⟨4606847, by rfl⟩ : syracuseStep 6142463 = 9213695) B9213695
theorem B4094975 : Blo 2155435 4094975 := bstep (se 1 (by rfl) ⟨3071231, by rfl⟩ : syracuseStep 4094975 = 6142463) B6142463
theorem B10919933 : Blo 2155435 10919933 := bstep (se 3 (by rfl) ⟨2047487, by rfl⟩ : syracuseStep 10919933 = 4094975) B4094975
theorem B7279955 : Blo 2155435 7279955 := bstep (se 1 (by rfl) ⟨5459966, by rfl⟩ : syracuseStep 7279955 = 10919933) B10919933
theorem B4853303 : Blo 2155435 4853303 := bstep (se 1 (by rfl) ⟨3639977, by rfl⟩ : syracuseStep 4853303 = 7279955) B7279955
theorem B3235535 : Blo 2155435 3235535 := bstep (se 1 (by rfl) ⟨2426651, by rfl⟩ : syracuseStep 3235535 = 4853303) B4853303
theorem B2157023 : Blo 2155435 2157023 := bstep (se 1 (by rfl) ⟨1617767, by rfl⟩ : syracuseStep 2157023 = 3235535) B3235535
theorem B3235541 : Blo 2155435 3235541 := bbase (se 7 (by rfl) ⟨37916, by rfl⟩ : syracuseStep 3235541 = 75833) (by norm_num)
theorem B2157027 : Blo 2155435 2157027 := bstep (se 1 (by rfl) ⟨1617770, by rfl⟩ : syracuseStep 2157027 = 3235541) B3235541
theorem B3455149 : Blo 2155435 3455149 := bbase (se 3 (by rfl) ⟨647840, by rfl⟩ : syracuseStep 3455149 = 1295681) (by norm_num)
theorem B4606865 : Blo 2155435 4606865 := bstep (se 2 (by rfl) ⟨1727574, by rfl⟩ : syracuseStep 4606865 = 3455149) B3455149
theorem B3071243 : Blo 2155435 3071243 := bstep (se 1 (by rfl) ⟨2303432, by rfl⟩ : syracuseStep 3071243 = 4606865) B4606865
theorem B8189981 : Blo 2155435 8189981 := bstep (se 3 (by rfl) ⟨1535621, by rfl⟩ : syracuseStep 8189981 = 3071243) B3071243
theorem B5459987 : Blo 2155435 5459987 := bstep (se 1 (by rfl) ⟨4094990, by rfl⟩ : syracuseStep 5459987 = 8189981) B8189981
theorem B3639991 : Blo 2155435 3639991 := bstep (se 1 (by rfl) ⟨2729993, by rfl⟩ : syracuseStep 3639991 = 5459987) B5459987
theorem B4853321 : Blo 2155435 4853321 := bstep (se 2 (by rfl) ⟨1819995, by rfl⟩ : syracuseStep 4853321 = 3639991) B3639991
theorem B3235547 : Blo 2155435 3235547 := bstep (se 1 (by rfl) ⟨2426660, by rfl⟩ : syracuseStep 3235547 = 4853321) B4853321
theorem B2157031 : Blo 2155435 2157031 := bstep (se 1 (by rfl) ⟨1617773, by rfl⟩ : syracuseStep 2157031 = 3235547) B3235547
theorem B2426665 : Blo 2155435 2426665 := bbase (se 2 (by rfl) ⟨909999, by rfl⟩ : syracuseStep 2426665 = 1819999) (by norm_num)
theorem B3235553 : Blo 2155435 3235553 := bstep (se 2 (by rfl) ⟨1213332, by rfl⟩ : syracuseStep 3235553 = 2426665) B2426665
theorem B2157035 : Blo 2155435 2157035 := bstep (se 1 (by rfl) ⟨1617776, by rfl⟩ : syracuseStep 2157035 = 3235553) B3235553
theorem B2915293 : Blo 2155435 2915293 := bbase (se 3 (by rfl) ⟨546617, by rfl⟩ : syracuseStep 2915293 = 1093235) (by norm_num)
theorem B3887057 : Blo 2155435 3887057 := bstep (se 2 (by rfl) ⟨1457646, by rfl⟩ : syracuseStep 3887057 = 2915293) B2915293
theorem B2591371 : Blo 2155435 2591371 := bstep (se 1 (by rfl) ⟨1943528, by rfl⟩ : syracuseStep 2591371 = 3887057) B3887057
theorem B13820645 : Blo 2155435 13820645 := bstep (se 4 (by rfl) ⟨1295685, by rfl⟩ : syracuseStep 13820645 = 2591371) B2591371
theorem B9213763 : Blo 2155435 9213763 := bstep (se 1 (by rfl) ⟨6910322, by rfl⟩ : syracuseStep 9213763 = 13820645) B13820645
theorem B12285017 : Blo 2155435 12285017 := bstep (se 2 (by rfl) ⟨4606881, by rfl⟩ : syracuseStep 12285017 = 9213763) B9213763
theorem B8190011 : Blo 2155435 8190011 := bstep (se 1 (by rfl) ⟨6142508, by rfl⟩ : syracuseStep 8190011 = 12285017) B12285017
theorem B5460007 : Blo 2155435 5460007 := bstep (se 1 (by rfl) ⟨4095005, by rfl⟩ : syracuseStep 5460007 = 8190011) B8190011
theorem B7280009 : Blo 2155435 7280009 := bstep (se 2 (by rfl) ⟨2730003, by rfl⟩ : syracuseStep 7280009 = 5460007) B5460007
theorem B4853339 : Blo 2155435 4853339 := bstep (se 1 (by rfl) ⟨3640004, by rfl⟩ : syracuseStep 4853339 = 7280009) B7280009
theorem B3235559 : Blo 2155435 3235559 := bstep (se 1 (by rfl) ⟨2426669, by rfl⟩ : syracuseStep 3235559 = 4853339) B4853339
theorem B2157039 : Blo 2155435 2157039 := bstep (se 1 (by rfl) ⟨1617779, by rfl⟩ : syracuseStep 2157039 = 3235559) B3235559
theorem B3235565 : Blo 2155435 3235565 := bbase (se 3 (by rfl) ⟨606668, by rfl⟩ : syracuseStep 3235565 = 1213337) (by norm_num)
theorem B2157043 : Blo 2155435 2157043 := bstep (se 1 (by rfl) ⟨1617782, by rfl⟩ : syracuseStep 2157043 = 3235565) B3235565
theorem B4853357 : Blo 2155435 4853357 := bbase (se 3 (by rfl) ⟨910004, by rfl⟩ : syracuseStep 4853357 = 1820009) (by norm_num)
theorem B3235571 : Blo 2155435 3235571 := bstep (se 1 (by rfl) ⟨2426678, by rfl⟩ : syracuseStep 3235571 = 4853357) B4853357
theorem B2157047 : Blo 2155435 2157047 := bstep (se 1 (by rfl) ⟨1617785, by rfl⟩ : syracuseStep 2157047 = 3235571) B3235571
theorem B4095029 : Blo 2155435 4095029 := bbase (se 5 (by rfl) ⟨191954, by rfl⟩ : syracuseStep 4095029 = 383909) (by norm_num)
theorem B2730019 : Blo 2155435 2730019 := bstep (se 1 (by rfl) ⟨2047514, by rfl⟩ : syracuseStep 2730019 = 4095029) B4095029
theorem B3640025 : Blo 2155435 3640025 := bstep (se 2 (by rfl) ⟨1365009, by rfl⟩ : syracuseStep 3640025 = 2730019) B2730019
theorem B2426683 : Blo 2155435 2426683 := bstep (se 1 (by rfl) ⟨1820012, by rfl⟩ : syracuseStep 2426683 = 3640025) B3640025
theorem B3235577 : Blo 2155435 3235577 := bstep (se 2 (by rfl) ⟨1213341, by rfl⟩ : syracuseStep 3235577 = 2426683) B2426683
theorem B2157051 : Blo 2155435 2157051 := bstep (se 1 (by rfl) ⟨1617788, by rfl⟩ : syracuseStep 2157051 = 3235577) B3235577
theorem B11220101 : Blo 2155435 11220101 := bbase (se 4 (by rfl) ⟨1051884, by rfl⟩ : syracuseStep 11220101 = 2103769) (by norm_num)
theorem B7480067 : Blo 2155435 7480067 := bstep (se 1 (by rfl) ⟨5610050, by rfl⟩ : syracuseStep 7480067 = 11220101) B11220101
theorem B79787381 : Blo 2155435 79787381 := bstep (se 5 (by rfl) ⟨3740033, by rfl⟩ : syracuseStep 79787381 = 7480067) B7480067
theorem B212766349 : Blo 2155435 212766349 := bstep (se 3 (by rfl) ⟨39893690, by rfl⟩ : syracuseStep 212766349 = 79787381) B79787381
theorem B283688465 : Blo 2155435 283688465 := bstep (se 2 (by rfl) ⟨106383174, by rfl⟩ : syracuseStep 283688465 = 212766349) B212766349
theorem B756502573 : Blo 2155435 756502573 := bstep (se 3 (by rfl) ⟨141844232, by rfl⟩ : syracuseStep 756502573 = 283688465) B283688465
theorem B1008670097 : Blo 2155435 1008670097 := bstep (se 2 (by rfl) ⟨378251286, by rfl⟩ : syracuseStep 1008670097 = 756502573) B756502573
theorem B672446731 : Blo 2155435 672446731 := bstep (se 1 (by rfl) ⟨504335048, by rfl⟩ : syracuseStep 672446731 = 1008670097) B1008670097
theorem B896595641 : Blo 2155435 896595641 := bstep (se 2 (by rfl) ⟨336223365, by rfl⟩ : syracuseStep 896595641 = 672446731) B672446731
theorem B597730427 : Blo 2155435 597730427 := bstep (se 1 (by rfl) ⟨448297820, by rfl⟩ : syracuseStep 597730427 = 896595641) B896595641
theorem B398486951 : Blo 2155435 398486951 := bstep (se 1 (by rfl) ⟨298865213, by rfl⟩ : syracuseStep 398486951 = 597730427) B597730427
theorem B265657967 : Blo 2155435 265657967 := bstep (se 1 (by rfl) ⟨199243475, by rfl⟩ : syracuseStep 265657967 = 398486951) B398486951
theorem B177105311 : Blo 2155435 177105311 := bstep (se 1 (by rfl) ⟨132828983, by rfl⟩ : syracuseStep 177105311 = 265657967) B265657967
theorem B118070207 : Blo 2155435 118070207 := bstep (se 1 (by rfl) ⟨88552655, by rfl⟩ : syracuseStep 118070207 = 177105311) B177105311
theorem B78713471 : Blo 2155435 78713471 := bstep (se 1 (by rfl) ⟨59035103, by rfl⟩ : syracuseStep 78713471 = 118070207) B118070207
theorem B209902589 : Blo 2155435 209902589 := bstep (se 3 (by rfl) ⟨39356735, by rfl⟩ : syracuseStep 209902589 = 78713471) B78713471
theorem B139935059 : Blo 2155435 139935059 := bstep (se 1 (by rfl) ⟨104951294, by rfl⟩ : syracuseStep 139935059 = 209902589) B209902589
theorem B93290039 : Blo 2155435 93290039 := bstep (se 1 (by rfl) ⟨69967529, by rfl⟩ : syracuseStep 93290039 = 139935059) B139935059
theorem B62193359 : Blo 2155435 62193359 := bstep (se 1 (by rfl) ⟨46645019, by rfl⟩ : syracuseStep 62193359 = 93290039) B93290039
theorem B41462239 : Blo 2155435 41462239 := bstep (se 1 (by rfl) ⟨31096679, by rfl⟩ : syracuseStep 41462239 = 62193359) B62193359
theorem B55282985 : Blo 2155435 55282985 := bstep (se 2 (by rfl) ⟨20731119, by rfl⟩ : syracuseStep 55282985 = 41462239) B41462239
theorem B36855323 : Blo 2155435 36855323 := bstep (se 1 (by rfl) ⟨27641492, by rfl⟩ : syracuseStep 36855323 = 55282985) B55282985
theorem B24570215 : Blo 2155435 24570215 := bstep (se 1 (by rfl) ⟨18427661, by rfl⟩ : syracuseStep 24570215 = 36855323) B36855323
theorem B16380143 : Blo 2155435 16380143 := bstep (se 1 (by rfl) ⟨12285107, by rfl⟩ : syracuseStep 16380143 = 24570215) B24570215
theorem B10920095 : Blo 2155435 10920095 := bstep (se 1 (by rfl) ⟨8190071, by rfl⟩ : syracuseStep 10920095 = 16380143) B16380143
theorem B7280063 : Blo 2155435 7280063 := bstep (se 1 (by rfl) ⟨5460047, by rfl⟩ : syracuseStep 7280063 = 10920095) B10920095
theorem B4853375 : Blo 2155435 4853375 := bstep (se 1 (by rfl) ⟨3640031, by rfl⟩ : syracuseStep 4853375 = 7280063) B7280063
theorem B3235583 : Blo 2155435 3235583 := bstep (se 1 (by rfl) ⟨2426687, by rfl⟩ : syracuseStep 3235583 = 4853375) B4853375
theorem B2157055 : Blo 2155435 2157055 := bstep (se 1 (by rfl) ⟨1617791, by rfl⟩ : syracuseStep 2157055 = 3235583) B3235583
theorem B3235589 : Blo 2155435 3235589 := bbase (se 4 (by rfl) ⟨303336, by rfl⟩ : syracuseStep 3235589 = 606673) (by norm_num)
theorem B2157059 : Blo 2155435 2157059 := bstep (se 1 (by rfl) ⟨1617794, by rfl⟩ : syracuseStep 2157059 = 3235589) B3235589
theorem B3640045 : Blo 2155435 3640045 := bbase (se 3 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 3640045 = 1365017) (by norm_num)
theorem B4853393 : Blo 2155435 4853393 := bstep (se 2 (by rfl) ⟨1820022, by rfl⟩ : syracuseStep 4853393 = 3640045) B3640045
theorem B3235595 : Blo 2155435 3235595 := bstep (se 1 (by rfl) ⟨2426696, by rfl⟩ : syracuseStep 3235595 = 4853393) B4853393
theorem B2157063 : Blo 2155435 2157063 := bstep (se 1 (by rfl) ⟨1617797, by rfl⟩ : syracuseStep 2157063 = 3235595) B3235595
theorem B2426701 : Blo 2155435 2426701 := bbase (se 3 (by rfl) ⟨455006, by rfl⟩ : syracuseStep 2426701 = 910013) (by norm_num)
theorem B3235601 : Blo 2155435 3235601 := bstep (se 2 (by rfl) ⟨1213350, by rfl⟩ : syracuseStep 3235601 = 2426701) B2426701
theorem B2157067 : Blo 2155435 2157067 := bstep (se 1 (by rfl) ⟨1617800, by rfl⟩ : syracuseStep 2157067 = 3235601) B3235601
theorem B7280117 : Blo 2155435 7280117 := bbase (se 5 (by rfl) ⟨341255, by rfl⟩ : syracuseStep 7280117 = 682511) (by norm_num)
theorem B4853411 : Blo 2155435 4853411 := bstep (se 1 (by rfl) ⟨3640058, by rfl⟩ : syracuseStep 4853411 = 7280117) B7280117
theorem B3235607 : Blo 2155435 3235607 := bstep (se 1 (by rfl) ⟨2426705, by rfl⟩ : syracuseStep 3235607 = 4853411) B4853411
theorem B2157071 : Blo 2155435 2157071 := bstep (se 1 (by rfl) ⟨1617803, by rfl⟩ : syracuseStep 2157071 = 3235607) B3235607
theorem B3235613 : Blo 2155435 3235613 := bbase (se 3 (by rfl) ⟨606677, by rfl⟩ : syracuseStep 3235613 = 1213355) (by norm_num)
theorem B2157075 : Blo 2155435 2157075 := bstep (se 1 (by rfl) ⟨1617806, by rfl⟩ : syracuseStep 2157075 = 3235613) B3235613
theorem B4853429 : Blo 2155435 4853429 := bbase (se 5 (by rfl) ⟨227504, by rfl⟩ : syracuseStep 4853429 = 455009) (by norm_num)
theorem B3235619 : Blo 2155435 3235619 := bstep (se 1 (by rfl) ⟨2426714, by rfl⟩ : syracuseStep 3235619 = 4853429) B4853429
theorem B2157079 : Blo 2155435 2157079 := bstep (se 1 (by rfl) ⟨1617809, by rfl⟩ : syracuseStep 2157079 = 3235619) B3235619
theorem B12285269 : Blo 2155435 12285269 := bbase (se 13 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 12285269 = 4499) (by norm_num)
theorem B8190179 : Blo 2155435 8190179 := bstep (se 1 (by rfl) ⟨6142634, by rfl⟩ : syracuseStep 8190179 = 12285269) B12285269
theorem B5460119 : Blo 2155435 5460119 := bstep (se 1 (by rfl) ⟨4095089, by rfl⟩ : syracuseStep 5460119 = 8190179) B8190179
theorem B3640079 : Blo 2155435 3640079 := bstep (se 1 (by rfl) ⟨2730059, by rfl⟩ : syracuseStep 3640079 = 5460119) B5460119
theorem B2426719 : Blo 2155435 2426719 := bstep (se 1 (by rfl) ⟨1820039, by rfl⟩ : syracuseStep 2426719 = 3640079) B3640079
theorem B3235625 : Blo 2155435 3235625 := bstep (se 2 (by rfl) ⟨1213359, by rfl⟩ : syracuseStep 3235625 = 2426719) B2426719
theorem B2157083 : Blo 2155435 2157083 := bstep (se 1 (by rfl) ⟨1617812, by rfl⟩ : syracuseStep 2157083 = 3235625) B3235625
theorem B6142645 : Blo 2155435 6142645 := bbase (se 5 (by rfl) ⟨287936, by rfl⟩ : syracuseStep 6142645 = 575873) (by norm_num)
theorem B8190193 : Blo 2155435 8190193 := bstep (se 2 (by rfl) ⟨3071322, by rfl⟩ : syracuseStep 8190193 = 6142645) B6142645
theorem B10920257 : Blo 2155435 10920257 := bstep (se 2 (by rfl) ⟨4095096, by rfl⟩ : syracuseStep 10920257 = 8190193) B8190193
theorem B7280171 : Blo 2155435 7280171 := bstep (se 1 (by rfl) ⟨5460128, by rfl⟩ : syracuseStep 7280171 = 10920257) B10920257
theorem B4853447 : Blo 2155435 4853447 := bstep (se 1 (by rfl) ⟨3640085, by rfl⟩ : syracuseStep 4853447 = 7280171) B7280171
theorem B3235631 : Blo 2155435 3235631 := bstep (se 1 (by rfl) ⟨2426723, by rfl⟩ : syracuseStep 3235631 = 4853447) B4853447
theorem B2157087 : Blo 2155435 2157087 := bstep (se 1 (by rfl) ⟨1617815, by rfl⟩ : syracuseStep 2157087 = 3235631) B3235631
theorem B3235637 : Blo 2155435 3235637 := bbase (se 5 (by rfl) ⟨151670, by rfl⟩ : syracuseStep 3235637 = 303341) (by norm_num)
theorem B2157091 : Blo 2155435 2157091 := bstep (se 1 (by rfl) ⟨1617818, by rfl⟩ : syracuseStep 2157091 = 3235637) B3235637
theorem B5460149 : Blo 2155435 5460149 := bbase (se 5 (by rfl) ⟨255944, by rfl⟩ : syracuseStep 5460149 = 511889) (by norm_num)
theorem B3640099 : Blo 2155435 3640099 := bstep (se 1 (by rfl) ⟨2730074, by rfl⟩ : syracuseStep 3640099 = 5460149) B5460149
theorem B4853465 : Blo 2155435 4853465 := bstep (se 2 (by rfl) ⟨1820049, by rfl⟩ : syracuseStep 4853465 = 3640099) B3640099
theorem B3235643 : Blo 2155435 3235643 := bstep (se 1 (by rfl) ⟨2426732, by rfl⟩ : syracuseStep 3235643 = 4853465) B4853465
theorem B2157095 : Blo 2155435 2157095 := bstep (se 1 (by rfl) ⟨1617821, by rfl⟩ : syracuseStep 2157095 = 3235643) B3235643
theorem B2426737 : Blo 2155435 2426737 := bbase (se 2 (by rfl) ⟨910026, by rfl⟩ : syracuseStep 2426737 = 1820053) (by norm_num)
theorem B3235649 : Blo 2155435 3235649 := bstep (se 2 (by rfl) ⟨1213368, by rfl⟩ : syracuseStep 3235649 = 2426737) B2426737
theorem B2157099 : Blo 2155435 2157099 := bstep (se 1 (by rfl) ⟨1617824, by rfl⟩ : syracuseStep 2157099 = 3235649) B3235649
theorem B9214037 : Blo 2155435 9214037 := bbase (se 8 (by rfl) ⟨53988, by rfl⟩ : syracuseStep 9214037 = 107977) (by norm_num)
theorem B6142691 : Blo 2155435 6142691 := bstep (se 1 (by rfl) ⟨4607018, by rfl⟩ : syracuseStep 6142691 = 9214037) B9214037
theorem B4095127 : Blo 2155435 4095127 := bstep (se 1 (by rfl) ⟨3071345, by rfl⟩ : syracuseStep 4095127 = 6142691) B6142691
theorem B5460169 : Blo 2155435 5460169 := bstep (se 2 (by rfl) ⟨2047563, by rfl⟩ : syracuseStep 5460169 = 4095127) B4095127
theorem B7280225 : Blo 2155435 7280225 := bstep (se 2 (by rfl) ⟨2730084, by rfl⟩ : syracuseStep 7280225 = 5460169) B5460169
theorem B4853483 : Blo 2155435 4853483 := bstep (se 1 (by rfl) ⟨3640112, by rfl⟩ : syracuseStep 4853483 = 7280225) B7280225
theorem B3235655 : Blo 2155435 3235655 := bstep (se 1 (by rfl) ⟨2426741, by rfl⟩ : syracuseStep 3235655 = 4853483) B4853483
theorem B2157103 : Blo 2155435 2157103 := bstep (se 1 (by rfl) ⟨1617827, by rfl⟩ : syracuseStep 2157103 = 3235655) B3235655
theorem B3235661 : Blo 2155435 3235661 := bbase (se 3 (by rfl) ⟨606686, by rfl⟩ : syracuseStep 3235661 = 1213373) (by norm_num)
theorem B2157107 : Blo 2155435 2157107 := bstep (se 1 (by rfl) ⟨1617830, by rfl⟩ : syracuseStep 2157107 = 3235661) B3235661
theorem B4853501 : Blo 2155435 4853501 := bbase (se 3 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 4853501 = 1820063) (by norm_num)
theorem B3235667 : Blo 2155435 3235667 := bstep (se 1 (by rfl) ⟨2426750, by rfl⟩ : syracuseStep 3235667 = 4853501) B4853501
theorem B2157111 : Blo 2155435 2157111 := bstep (se 1 (by rfl) ⟨1617833, by rfl⟩ : syracuseStep 2157111 = 3235667) B3235667
theorem B3640133 : Blo 2155435 3640133 := bbase (se 4 (by rfl) ⟨341262, by rfl⟩ : syracuseStep 3640133 = 682525) (by norm_num)
theorem B2426755 : Blo 2155435 2426755 := bstep (se 1 (by rfl) ⟨1820066, by rfl⟩ : syracuseStep 2426755 = 3640133) B3640133
theorem B3235673 : Blo 2155435 3235673 := bstep (se 2 (by rfl) ⟨1213377, by rfl⟩ : syracuseStep 3235673 = 2426755) B2426755
theorem B2157115 : Blo 2155435 2157115 := bstep (se 1 (by rfl) ⟨1617836, by rfl⟩ : syracuseStep 2157115 = 3235673) B3235673
theorem B16380629 : Blo 2155435 16380629 := bbase (se 7 (by rfl) ⟨191960, by rfl⟩ : syracuseStep 16380629 = 383921) (by norm_num)
theorem B10920419 : Blo 2155435 10920419 := bstep (se 1 (by rfl) ⟨8190314, by rfl⟩ : syracuseStep 10920419 = 16380629) B16380629
theorem B7280279 : Blo 2155435 7280279 := bstep (se 1 (by rfl) ⟨5460209, by rfl⟩ : syracuseStep 7280279 = 10920419) B10920419
theorem B4853519 : Blo 2155435 4853519 := bstep (se 1 (by rfl) ⟨3640139, by rfl⟩ : syracuseStep 4853519 = 7280279) B7280279
theorem B3235679 : Blo 2155435 3235679 := bstep (se 1 (by rfl) ⟨2426759, by rfl⟩ : syracuseStep 3235679 = 4853519) B4853519
theorem B2157119 : Blo 2155435 2157119 := bstep (se 1 (by rfl) ⟨1617839, by rfl⟩ : syracuseStep 2157119 = 3235679) B3235679
theorem B3235685 : Blo 2155435 3235685 := bbase (se 4 (by rfl) ⟨303345, by rfl⟩ : syracuseStep 3235685 = 606691) (by norm_num)
theorem B2157123 : Blo 2155435 2157123 := bstep (se 1 (by rfl) ⟨1617842, by rfl⟩ : syracuseStep 2157123 = 3235685) B3235685
theorem B4095173 : Blo 2155435 4095173 := bbase (se 4 (by rfl) ⟨383922, by rfl⟩ : syracuseStep 4095173 = 767845) (by norm_num)
theorem B2730115 : Blo 2155435 2730115 := bstep (se 1 (by rfl) ⟨2047586, by rfl⟩ : syracuseStep 2730115 = 4095173) B4095173
theorem B3640153 : Blo 2155435 3640153 := bstep (se 2 (by rfl) ⟨1365057, by rfl⟩ : syracuseStep 3640153 = 2730115) B2730115
theorem B4853537 : Blo 2155435 4853537 := bstep (se 2 (by rfl) ⟨1820076, by rfl⟩ : syracuseStep 4853537 = 3640153) B3640153
theorem B3235691 : Blo 2155435 3235691 := bstep (se 1 (by rfl) ⟨2426768, by rfl⟩ : syracuseStep 3235691 = 4853537) B4853537
theorem B2157127 : Blo 2155435 2157127 := bstep (se 1 (by rfl) ⟨1617845, by rfl⟩ : syracuseStep 2157127 = 3235691) B3235691
theorem B2426773 : Blo 2155435 2426773 := bbase (se 6 (by rfl) ⟨56877, by rfl⟩ : syracuseStep 2426773 = 113755) (by norm_num)
theorem B3235697 : Blo 2155435 3235697 := bstep (se 2 (by rfl) ⟨1213386, by rfl⟩ : syracuseStep 3235697 = 2426773) B2426773
theorem B2157131 : Blo 2155435 2157131 := bstep (se 1 (by rfl) ⟨1617848, by rfl⟩ : syracuseStep 2157131 = 3235697) B3235697
theorem B2730125 : Blo 2155435 2730125 := bbase (se 3 (by rfl) ⟨511898, by rfl⟩ : syracuseStep 2730125 = 1023797) (by norm_num)
theorem B7280333 : Blo 2155435 7280333 := bstep (se 3 (by rfl) ⟨1365062, by rfl⟩ : syracuseStep 7280333 = 2730125) B2730125
theorem B4853555 : Blo 2155435 4853555 := bstep (se 1 (by rfl) ⟨3640166, by rfl⟩ : syracuseStep 4853555 = 7280333) B7280333
theorem B3235703 : Blo 2155435 3235703 := bstep (se 1 (by rfl) ⟨2426777, by rfl⟩ : syracuseStep 3235703 = 4853555) B4853555
theorem B2157135 : Blo 2155435 2157135 := bstep (se 1 (by rfl) ⟨1617851, by rfl⟩ : syracuseStep 2157135 = 3235703) B3235703
theorem B3235709 : Blo 2155435 3235709 := bbase (se 3 (by rfl) ⟨606695, by rfl⟩ : syracuseStep 3235709 = 1213391) (by norm_num)
theorem B2157139 : Blo 2155435 2157139 := bstep (se 1 (by rfl) ⟨1617854, by rfl⟩ : syracuseStep 2157139 = 3235709) B3235709
theorem B4853573 : Blo 2155435 4853573 := bbase (se 4 (by rfl) ⟨455022, by rfl⟩ : syracuseStep 4853573 = 910045) (by norm_num)
theorem B3235715 : Blo 2155435 3235715 := bstep (se 1 (by rfl) ⟨2426786, by rfl⟩ : syracuseStep 3235715 = 4853573) B4853573
theorem B2157143 : Blo 2155435 2157143 := bstep (se 1 (by rfl) ⟨1617857, by rfl⟩ : syracuseStep 2157143 = 3235715) B3235715
theorem B3740197 : Blo 2155435 3740197 := bbase (se 4 (by rfl) ⟨350643, by rfl⟩ : syracuseStep 3740197 = 701287) (by norm_num)
theorem B4986929 : Blo 2155435 4986929 := bstep (se 2 (by rfl) ⟨1870098, by rfl⟩ : syracuseStep 4986929 = 3740197) B3740197
theorem B3324619 : Blo 2155435 3324619 := bstep (se 1 (by rfl) ⟨2493464, by rfl⟩ : syracuseStep 3324619 = 4986929) B4986929
theorem B4432825 : Blo 2155435 4432825 := bstep (se 2 (by rfl) ⟨1662309, by rfl⟩ : syracuseStep 4432825 = 3324619) B3324619
theorem B23641733 : Blo 2155435 23641733 := bstep (se 4 (by rfl) ⟨2216412, by rfl⟩ : syracuseStep 23641733 = 4432825) B4432825
theorem B15761155 : Blo 2155435 15761155 := bstep (se 1 (by rfl) ⟨11820866, by rfl⟩ : syracuseStep 15761155 = 23641733) B23641733
theorem B21014873 : Blo 2155435 21014873 := bstep (se 2 (by rfl) ⟨7880577, by rfl⟩ : syracuseStep 21014873 = 15761155) B15761155
theorem B14009915 : Blo 2155435 14009915 := bstep (se 1 (by rfl) ⟨10507436, by rfl⟩ : syracuseStep 14009915 = 21014873) B21014873
theorem B9339943 : Blo 2155435 9339943 := bstep (se 1 (by rfl) ⟨7004957, by rfl⟩ : syracuseStep 9339943 = 14009915) B14009915
theorem B12453257 : Blo 2155435 12453257 := bstep (se 2 (by rfl) ⟨4669971, by rfl⟩ : syracuseStep 12453257 = 9339943) B9339943
theorem B8302171 : Blo 2155435 8302171 := bstep (se 1 (by rfl) ⟨6226628, by rfl⟩ : syracuseStep 8302171 = 12453257) B12453257
theorem B11069561 : Blo 2155435 11069561 := bstep (se 2 (by rfl) ⟨4151085, by rfl⟩ : syracuseStep 11069561 = 8302171) B8302171
theorem B29518829 : Blo 2155435 29518829 := bstep (se 3 (by rfl) ⟨5534780, by rfl⟩ : syracuseStep 29518829 = 11069561) B11069561
theorem B19679219 : Blo 2155435 19679219 := bstep (se 1 (by rfl) ⟨14759414, by rfl⟩ : syracuseStep 19679219 = 29518829) B29518829
theorem B13119479 : Blo 2155435 13119479 := bstep (se 1 (by rfl) ⟨9839609, by rfl⟩ : syracuseStep 13119479 = 19679219) B19679219
theorem B8746319 : Blo 2155435 8746319 := bstep (se 1 (by rfl) ⟨6559739, by rfl⟩ : syracuseStep 8746319 = 13119479) B13119479
theorem B5830879 : Blo 2155435 5830879 := bstep (se 1 (by rfl) ⟨4373159, by rfl⟩ : syracuseStep 5830879 = 8746319) B8746319
theorem B7774505 : Blo 2155435 7774505 := bstep (se 2 (by rfl) ⟨2915439, by rfl⟩ : syracuseStep 7774505 = 5830879) B5830879
theorem B5183003 : Blo 2155435 5183003 := bstep (se 1 (by rfl) ⟨3887252, by rfl⟩ : syracuseStep 5183003 = 7774505) B7774505
theorem B3455335 : Blo 2155435 3455335 := bstep (se 1 (by rfl) ⟨2591501, by rfl⟩ : syracuseStep 3455335 = 5183003) B5183003
theorem B4607113 : Blo 2155435 4607113 := bstep (se 2 (by rfl) ⟨1727667, by rfl⟩ : syracuseStep 4607113 = 3455335) B3455335
theorem B6142817 : Blo 2155435 6142817 := bstep (se 2 (by rfl) ⟨2303556, by rfl⟩ : syracuseStep 6142817 = 4607113) B4607113
theorem B4095211 : Blo 2155435 4095211 := bstep (se 1 (by rfl) ⟨3071408, by rfl⟩ : syracuseStep 4095211 = 6142817) B6142817
theorem B5460281 : Blo 2155435 5460281 := bstep (se 2 (by rfl) ⟨2047605, by rfl⟩ : syracuseStep 5460281 = 4095211) B4095211
theorem B3640187 : Blo 2155435 3640187 := bstep (se 1 (by rfl) ⟨2730140, by rfl⟩ : syracuseStep 3640187 = 5460281) B5460281
theorem B2426791 : Blo 2155435 2426791 := bstep (se 1 (by rfl) ⟨1820093, by rfl⟩ : syracuseStep 2426791 = 3640187) B3640187
theorem B3235721 : Blo 2155435 3235721 := bstep (se 2 (by rfl) ⟨1213395, by rfl⟩ : syracuseStep 3235721 = 2426791) B2426791
theorem B2157147 : Blo 2155435 2157147 := bstep (se 1 (by rfl) ⟨1617860, by rfl⟩ : syracuseStep 2157147 = 3235721) B3235721
theorem B10920581 : Blo 2155435 10920581 := bbase (se 4 (by rfl) ⟨1023804, by rfl⟩ : syracuseStep 10920581 = 2047609) (by norm_num)
theorem B7280387 : Blo 2155435 7280387 := bstep (se 1 (by rfl) ⟨5460290, by rfl⟩ : syracuseStep 7280387 = 10920581) B10920581
theorem B4853591 : Blo 2155435 4853591 := bstep (se 1 (by rfl) ⟨3640193, by rfl⟩ : syracuseStep 4853591 = 7280387) B7280387
theorem B3235727 : Blo 2155435 3235727 := bstep (se 1 (by rfl) ⟨2426795, by rfl⟩ : syracuseStep 3235727 = 4853591) B4853591
theorem B2157151 : Blo 2155435 2157151 := bstep (se 1 (by rfl) ⟨1617863, by rfl⟩ : syracuseStep 2157151 = 3235727) B3235727
theorem B3235733 : Blo 2155435 3235733 := bbase (se 6 (by rfl) ⟨75837, by rfl⟩ : syracuseStep 3235733 = 151675) (by norm_num)
theorem B2157155 : Blo 2155435 2157155 := bstep (se 1 (by rfl) ⟨1617866, by rfl⟩ : syracuseStep 2157155 = 3235733) B3235733
theorem B2303569 : Blo 2155435 2303569 := bbase (se 2 (by rfl) ⟨863838, by rfl⟩ : syracuseStep 2303569 = 1727677) (by norm_num)
theorem B12285701 : Blo 2155435 12285701 := bstep (se 4 (by rfl) ⟨1151784, by rfl⟩ : syracuseStep 12285701 = 2303569) B2303569
theorem B8190467 : Blo 2155435 8190467 := bstep (se 1 (by rfl) ⟨6142850, by rfl⟩ : syracuseStep 8190467 = 12285701) B12285701
theorem B5460311 : Blo 2155435 5460311 := bstep (se 1 (by rfl) ⟨4095233, by rfl⟩ : syracuseStep 5460311 = 8190467) B8190467
theorem B3640207 : Blo 2155435 3640207 := bstep (se 1 (by rfl) ⟨2730155, by rfl⟩ : syracuseStep 3640207 = 5460311) B5460311
theorem B4853609 : Blo 2155435 4853609 := bstep (se 2 (by rfl) ⟨1820103, by rfl⟩ : syracuseStep 4853609 = 3640207) B3640207
theorem B3235739 : Blo 2155435 3235739 := bstep (se 1 (by rfl) ⟨2426804, by rfl⟩ : syracuseStep 3235739 = 4853609) B4853609
theorem B2157159 : Blo 2155435 2157159 := bstep (se 1 (by rfl) ⟨1617869, by rfl⟩ : syracuseStep 2157159 = 3235739) B3235739
theorem B2426809 : Blo 2155435 2426809 := bbase (se 2 (by rfl) ⟨910053, by rfl⟩ : syracuseStep 2426809 = 1820107) (by norm_num)
theorem B3235745 : Blo 2155435 3235745 := bstep (se 2 (by rfl) ⟨1213404, by rfl⟩ : syracuseStep 3235745 = 2426809) B2426809
theorem B2157163 : Blo 2155435 2157163 := bstep (se 1 (by rfl) ⟨1617872, by rfl⟩ : syracuseStep 2157163 = 3235745) B3235745
theorem B2591525 : Blo 2155435 2591525 := bbase (se 4 (by rfl) ⟨242955, by rfl⟩ : syracuseStep 2591525 = 485911) (by norm_num)
theorem B6910733 : Blo 2155435 6910733 := bstep (se 3 (by rfl) ⟨1295762, by rfl⟩ : syracuseStep 6910733 = 2591525) B2591525
theorem B4607155 : Blo 2155435 4607155 := bstep (se 1 (by rfl) ⟨3455366, by rfl⟩ : syracuseStep 4607155 = 6910733) B6910733
theorem B6142873 : Blo 2155435 6142873 := bstep (se 2 (by rfl) ⟨2303577, by rfl⟩ : syracuseStep 6142873 = 4607155) B4607155
theorem B8190497 : Blo 2155435 8190497 := bstep (se 2 (by rfl) ⟨3071436, by rfl⟩ : syracuseStep 8190497 = 6142873) B6142873
theorem B5460331 : Blo 2155435 5460331 := bstep (se 1 (by rfl) ⟨4095248, by rfl⟩ : syracuseStep 5460331 = 8190497) B8190497
theorem B7280441 : Blo 2155435 7280441 := bstep (se 2 (by rfl) ⟨2730165, by rfl⟩ : syracuseStep 7280441 = 5460331) B5460331
theorem B4853627 : Blo 2155435 4853627 := bstep (se 1 (by rfl) ⟨3640220, by rfl⟩ : syracuseStep 4853627 = 7280441) B7280441
theorem B3235751 : Blo 2155435 3235751 := bstep (se 1 (by rfl) ⟨2426813, by rfl⟩ : syracuseStep 3235751 = 4853627) B4853627
theorem B2157167 : Blo 2155435 2157167 := bstep (se 1 (by rfl) ⟨1617875, by rfl⟩ : syracuseStep 2157167 = 3235751) B3235751
theorem B3235757 : Blo 2155435 3235757 := bbase (se 3 (by rfl) ⟨606704, by rfl⟩ : syracuseStep 3235757 = 1213409) (by norm_num)
theorem B2157171 : Blo 2155435 2157171 := bstep (se 1 (by rfl) ⟨1617878, by rfl⟩ : syracuseStep 2157171 = 3235757) B3235757
theorem B4853645 : Blo 2155435 4853645 := bbase (se 3 (by rfl) ⟨910058, by rfl⟩ : syracuseStep 4853645 = 1820117) (by norm_num)
theorem B3235763 : Blo 2155435 3235763 := bstep (se 1 (by rfl) ⟨2426822, by rfl⟩ : syracuseStep 3235763 = 4853645) B4853645
theorem B2157175 : Blo 2155435 2157175 := bstep (se 1 (by rfl) ⟨1617881, by rfl⟩ : syracuseStep 2157175 = 3235763) B3235763
theorem B2730181 : Blo 2155435 2730181 := bbase (se 4 (by rfl) ⟨255954, by rfl⟩ : syracuseStep 2730181 = 511909) (by norm_num)
theorem B3640241 : Blo 2155435 3640241 := bstep (se 2 (by rfl) ⟨1365090, by rfl⟩ : syracuseStep 3640241 = 2730181) B2730181
theorem B2426827 : Blo 2155435 2426827 := bstep (se 1 (by rfl) ⟨1820120, by rfl⟩ : syracuseStep 2426827 = 3640241) B3640241
theorem B3235769 : Blo 2155435 3235769 := bstep (se 2 (by rfl) ⟨1213413, by rfl⟩ : syracuseStep 3235769 = 2426827) B2426827
theorem B2157179 : Blo 2155435 2157179 := bstep (se 1 (by rfl) ⟨1617884, by rfl⟩ : syracuseStep 2157179 = 3235769) B3235769
theorem B3113365 : Blo 2155435 3113365 := bbase (se 6 (by rfl) ⟨72969, by rfl⟩ : syracuseStep 3113365 = 145939) (by norm_num)
theorem B4151153 : Blo 2155435 4151153 := bstep (se 2 (by rfl) ⟨1556682, by rfl⟩ : syracuseStep 4151153 = 3113365) B3113365
theorem B2767435 : Blo 2155435 2767435 := bstep (se 1 (by rfl) ⟨2075576, by rfl⟩ : syracuseStep 2767435 = 4151153) B4151153
theorem B14759653 : Blo 2155435 14759653 := bstep (se 4 (by rfl) ⟨1383717, by rfl⟩ : syracuseStep 14759653 = 2767435) B2767435
theorem B19679537 : Blo 2155435 19679537 := bstep (se 2 (by rfl) ⟨7379826, by rfl⟩ : syracuseStep 19679537 = 14759653) B14759653
theorem B52478765 : Blo 2155435 52478765 := bstep (se 3 (by rfl) ⟨9839768, by rfl⟩ : syracuseStep 52478765 = 19679537) B19679537
theorem B34985843 : Blo 2155435 34985843 := bstep (se 1 (by rfl) ⟨26239382, by rfl⟩ : syracuseStep 34985843 = 52478765) B52478765
theorem B23323895 : Blo 2155435 23323895 := bstep (se 1 (by rfl) ⟨17492921, by rfl⟩ : syracuseStep 23323895 = 34985843) B34985843
theorem B15549263 : Blo 2155435 15549263 := bstep (se 1 (by rfl) ⟨11661947, by rfl⟩ : syracuseStep 15549263 = 23323895) B23323895
theorem B10366175 : Blo 2155435 10366175 := bstep (se 1 (by rfl) ⟨7774631, by rfl⟩ : syracuseStep 10366175 = 15549263) B15549263
theorem B27643133 : Blo 2155435 27643133 := bstep (se 3 (by rfl) ⟨5183087, by rfl⟩ : syracuseStep 27643133 = 10366175) B10366175
theorem B18428755 : Blo 2155435 18428755 := bstep (se 1 (by rfl) ⟨13821566, by rfl⟩ : syracuseStep 18428755 = 27643133) B27643133
theorem B24571673 : Blo 2155435 24571673 := bstep (se 2 (by rfl) ⟨9214377, by rfl⟩ : syracuseStep 24571673 = 18428755) B18428755
theorem B16381115 : Blo 2155435 16381115 := bstep (se 1 (by rfl) ⟨12285836, by rfl⟩ : syracuseStep 16381115 = 24571673) B24571673
theorem B10920743 : Blo 2155435 10920743 := bstep (se 1 (by rfl) ⟨8190557, by rfl⟩ : syracuseStep 10920743 = 16381115) B16381115
theorem B7280495 : Blo 2155435 7280495 := bstep (se 1 (by rfl) ⟨5460371, by rfl⟩ : syracuseStep 7280495 = 10920743) B10920743
theorem B4853663 : Blo 2155435 4853663 := bstep (se 1 (by rfl) ⟨3640247, by rfl⟩ : syracuseStep 4853663 = 7280495) B7280495
theorem B3235775 : Blo 2155435 3235775 := bstep (se 1 (by rfl) ⟨2426831, by rfl⟩ : syracuseStep 3235775 = 4853663) B4853663
theorem B2157183 : Blo 2155435 2157183 := bstep (se 1 (by rfl) ⟨1617887, by rfl⟩ : syracuseStep 2157183 = 3235775) B3235775
theorem B3235781 : Blo 2155435 3235781 := bbase (se 4 (by rfl) ⟨303354, by rfl⟩ : syracuseStep 3235781 = 606709) (by norm_num)
theorem B2157187 : Blo 2155435 2157187 := bstep (se 1 (by rfl) ⟨1617890, by rfl⟩ : syracuseStep 2157187 = 3235781) B3235781
theorem B3640261 : Blo 2155435 3640261 := bbase (se 4 (by rfl) ⟨341274, by rfl⟩ : syracuseStep 3640261 = 682549) (by norm_num)
theorem B4853681 : Blo 2155435 4853681 := bstep (se 2 (by rfl) ⟨1820130, by rfl⟩ : syracuseStep 4853681 = 3640261) B3640261
theorem B3235787 : Blo 2155435 3235787 := bstep (se 1 (by rfl) ⟨2426840, by rfl⟩ : syracuseStep 3235787 = 4853681) B4853681
theorem B2157191 : Blo 2155435 2157191 := bstep (se 1 (by rfl) ⟨1617893, by rfl⟩ : syracuseStep 2157191 = 3235787) B3235787
theorem B2426845 : Blo 2155435 2426845 := bbase (se 3 (by rfl) ⟨455033, by rfl⟩ : syracuseStep 2426845 = 910067) (by norm_num)
theorem B3235793 : Blo 2155435 3235793 := bstep (se 2 (by rfl) ⟨1213422, by rfl⟩ : syracuseStep 3235793 = 2426845) B2426845
theorem B2157195 : Blo 2155435 2157195 := bstep (se 1 (by rfl) ⟨1617896, by rfl⟩ : syracuseStep 2157195 = 3235793) B3235793
theorem B7280549 : Blo 2155435 7280549 := bbase (se 4 (by rfl) ⟨682551, by rfl⟩ : syracuseStep 7280549 = 1365103) (by norm_num)
theorem B4853699 : Blo 2155435 4853699 := bstep (se 1 (by rfl) ⟨3640274, by rfl⟩ : syracuseStep 4853699 = 7280549) B7280549
theorem B3235799 : Blo 2155435 3235799 := bstep (se 1 (by rfl) ⟨2426849, by rfl⟩ : syracuseStep 3235799 = 4853699) B4853699
theorem B2157199 : Blo 2155435 2157199 := bstep (se 1 (by rfl) ⟨1617899, by rfl⟩ : syracuseStep 2157199 = 3235799) B3235799
theorem B3235805 : Blo 2155435 3235805 := bbase (se 3 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 3235805 = 1213427) (by norm_num)
theorem B2157203 : Blo 2155435 2157203 := bstep (se 1 (by rfl) ⟨1617902, by rfl⟩ : syracuseStep 2157203 = 3235805) B3235805
theorem B4853717 : Blo 2155435 4853717 := bbase (se 7 (by rfl) ⟨56879, by rfl⟩ : syracuseStep 4853717 = 113759) (by norm_num)
theorem B3235811 : Blo 2155435 3235811 := bstep (se 1 (by rfl) ⟨2426858, by rfl⟩ : syracuseStep 3235811 = 4853717) B4853717
theorem B2157207 : Blo 2155435 2157207 := bstep (se 1 (by rfl) ⟨1617905, by rfl⟩ : syracuseStep 2157207 = 3235811) B3235811
theorem B13821749 : Blo 2155435 13821749 := bbase (se 5 (by rfl) ⟨647894, by rfl⟩ : syracuseStep 13821749 = 1295789) (by norm_num)
theorem B9214499 : Blo 2155435 9214499 := bstep (se 1 (by rfl) ⟨6910874, by rfl⟩ : syracuseStep 9214499 = 13821749) B13821749
theorem B6142999 : Blo 2155435 6142999 := bstep (se 1 (by rfl) ⟨4607249, by rfl⟩ : syracuseStep 6142999 = 9214499) B9214499
theorem B8190665 : Blo 2155435 8190665 := bstep (se 2 (by rfl) ⟨3071499, by rfl⟩ : syracuseStep 8190665 = 6142999) B6142999
theorem B5460443 : Blo 2155435 5460443 := bstep (se 1 (by rfl) ⟨4095332, by rfl⟩ : syracuseStep 5460443 = 8190665) B8190665
theorem B3640295 : Blo 2155435 3640295 := bstep (se 1 (by rfl) ⟨2730221, by rfl⟩ : syracuseStep 3640295 = 5460443) B5460443
theorem B2426863 : Blo 2155435 2426863 := bstep (se 1 (by rfl) ⟨1820147, by rfl⟩ : syracuseStep 2426863 = 3640295) B3640295
theorem B3235817 : Blo 2155435 3235817 := bstep (se 2 (by rfl) ⟨1213431, by rfl⟩ : syracuseStep 3235817 = 2426863) B2426863
theorem B2157211 : Blo 2155435 2157211 := bstep (se 1 (by rfl) ⟨1617908, by rfl⟩ : syracuseStep 2157211 = 3235817) B3235817
theorem B5183165 : Blo 2155435 5183165 := bbase (se 3 (by rfl) ⟨971843, by rfl⟩ : syracuseStep 5183165 = 1943687) (by norm_num)
theorem B3455443 : Blo 2155435 3455443 := bstep (se 1 (by rfl) ⟨2591582, by rfl⟩ : syracuseStep 3455443 = 5183165) B5183165
theorem B18429029 : Blo 2155435 18429029 := bstep (se 4 (by rfl) ⟨1727721, by rfl⟩ : syracuseStep 18429029 = 3455443) B3455443
theorem B12286019 : Blo 2155435 12286019 := bstep (se 1 (by rfl) ⟨9214514, by rfl⟩ : syracuseStep 12286019 = 18429029) B18429029
theorem B8190679 : Blo 2155435 8190679 := bstep (se 1 (by rfl) ⟨6143009, by rfl⟩ : syracuseStep 8190679 = 12286019) B12286019
theorem B10920905 : Blo 2155435 10920905 := bstep (se 2 (by rfl) ⟨4095339, by rfl⟩ : syracuseStep 10920905 = 8190679) B8190679
theorem B7280603 : Blo 2155435 7280603 := bstep (se 1 (by rfl) ⟨5460452, by rfl⟩ : syracuseStep 7280603 = 10920905) B10920905
theorem B4853735 : Blo 2155435 4853735 := bstep (se 1 (by rfl) ⟨3640301, by rfl⟩ : syracuseStep 4853735 = 7280603) B7280603
theorem B3235823 : Blo 2155435 3235823 := bstep (se 1 (by rfl) ⟨2426867, by rfl⟩ : syracuseStep 3235823 = 4853735) B4853735
theorem B2157215 : Blo 2155435 2157215 := bstep (se 1 (by rfl) ⟨1617911, by rfl⟩ : syracuseStep 2157215 = 3235823) B3235823
theorem B3235829 : Blo 2155435 3235829 := bbase (se 5 (by rfl) ⟨151679, by rfl⟩ : syracuseStep 3235829 = 303359) (by norm_num)
theorem B2157219 : Blo 2155435 2157219 := bstep (se 1 (by rfl) ⟨1617914, by rfl⟩ : syracuseStep 2157219 = 3235829) B3235829
theorem B3887389 : Blo 2155435 3887389 := bbase (se 3 (by rfl) ⟨728885, by rfl⟩ : syracuseStep 3887389 = 1457771) (by norm_num)
theorem B5183185 : Blo 2155435 5183185 := bstep (se 2 (by rfl) ⟨1943694, by rfl⟩ : syracuseStep 5183185 = 3887389) B3887389
theorem B6910913 : Blo 2155435 6910913 := bstep (se 2 (by rfl) ⟨2591592, by rfl⟩ : syracuseStep 6910913 = 5183185) B5183185
theorem B4607275 : Blo 2155435 4607275 := bstep (se 1 (by rfl) ⟨3455456, by rfl⟩ : syracuseStep 4607275 = 6910913) B6910913
theorem B6143033 : Blo 2155435 6143033 := bstep (se 2 (by rfl) ⟨2303637, by rfl⟩ : syracuseStep 6143033 = 4607275) B4607275
theorem B4095355 : Blo 2155435 4095355 := bstep (se 1 (by rfl) ⟨3071516, by rfl⟩ : syracuseStep 4095355 = 6143033) B6143033
theorem B5460473 : Blo 2155435 5460473 := bstep (se 2 (by rfl) ⟨2047677, by rfl⟩ : syracuseStep 5460473 = 4095355) B4095355
theorem B3640315 : Blo 2155435 3640315 := bstep (se 1 (by rfl) ⟨2730236, by rfl⟩ : syracuseStep 3640315 = 5460473) B5460473
theorem B4853753 : Blo 2155435 4853753 := bstep (se 2 (by rfl) ⟨1820157, by rfl⟩ : syracuseStep 4853753 = 3640315) B3640315
theorem B3235835 : Blo 2155435 3235835 := bstep (se 1 (by rfl) ⟨2426876, by rfl⟩ : syracuseStep 3235835 = 4853753) B4853753
theorem B2157223 : Blo 2155435 2157223 := bstep (se 1 (by rfl) ⟨1617917, by rfl⟩ : syracuseStep 2157223 = 3235835) B3235835
theorem B2426881 : Blo 2155435 2426881 := bbase (se 2 (by rfl) ⟨910080, by rfl⟩ : syracuseStep 2426881 = 1820161) (by norm_num)
theorem B3235841 : Blo 2155435 3235841 := bstep (se 2 (by rfl) ⟨1213440, by rfl⟩ : syracuseStep 3235841 = 2426881) B2426881
theorem B2157227 : Blo 2155435 2157227 := bstep (se 1 (by rfl) ⟨1617920, by rfl⟩ : syracuseStep 2157227 = 3235841) B3235841
theorem B5460493 : Blo 2155435 5460493 := bbase (se 3 (by rfl) ⟨1023842, by rfl⟩ : syracuseStep 5460493 = 2047685) (by norm_num)
theorem B7280657 : Blo 2155435 7280657 := bstep (se 2 (by rfl) ⟨2730246, by rfl⟩ : syracuseStep 7280657 = 5460493) B5460493
theorem B4853771 : Blo 2155435 4853771 := bstep (se 1 (by rfl) ⟨3640328, by rfl⟩ : syracuseStep 4853771 = 7280657) B7280657
theorem B3235847 : Blo 2155435 3235847 := bstep (se 1 (by rfl) ⟨2426885, by rfl⟩ : syracuseStep 3235847 = 4853771) B4853771
theorem B2157231 : Blo 2155435 2157231 := bstep (se 1 (by rfl) ⟨1617923, by rfl⟩ : syracuseStep 2157231 = 3235847) B3235847
theorem B3235853 : Blo 2155435 3235853 := bbase (se 3 (by rfl) ⟨606722, by rfl⟩ : syracuseStep 3235853 = 1213445) (by norm_num)
theorem B2157235 : Blo 2155435 2157235 := bstep (se 1 (by rfl) ⟨1617926, by rfl⟩ : syracuseStep 2157235 = 3235853) B3235853
theorem B4853789 : Blo 2155435 4853789 := bbase (se 3 (by rfl) ⟨910085, by rfl⟩ : syracuseStep 4853789 = 1820171) (by norm_num)
theorem B3235859 : Blo 2155435 3235859 := bstep (se 1 (by rfl) ⟨2426894, by rfl⟩ : syracuseStep 3235859 = 4853789) B4853789
theorem B2157239 : Blo 2155435 2157239 := bstep (se 1 (by rfl) ⟨1617929, by rfl⟩ : syracuseStep 2157239 = 3235859) B3235859
theorem B3640349 : Blo 2155435 3640349 := bbase (se 3 (by rfl) ⟨682565, by rfl⟩ : syracuseStep 3640349 = 1365131) (by norm_num)
theorem B2426899 : Blo 2155435 2426899 := bstep (se 1 (by rfl) ⟨1820174, by rfl⟩ : syracuseStep 2426899 = 3640349) B3640349
theorem B3235865 : Blo 2155435 3235865 := bstep (se 2 (by rfl) ⟨1213449, by rfl⟩ : syracuseStep 3235865 = 2426899) B2426899
theorem B2157243 : Blo 2155435 2157243 := bstep (se 1 (by rfl) ⟨1617932, by rfl⟩ : syracuseStep 2157243 = 3235865) B3235865
theorem B9340373 : Blo 2155435 9340373 := bbase (se 7 (by rfl) ⟨109457, by rfl⟩ : syracuseStep 9340373 = 218915) (by norm_num)
theorem B24907661 : Blo 2155435 24907661 := bstep (se 3 (by rfl) ⟨4670186, by rfl⟩ : syracuseStep 24907661 = 9340373) B9340373
theorem B16605107 : Blo 2155435 16605107 := bstep (se 1 (by rfl) ⟨12453830, by rfl⟩ : syracuseStep 16605107 = 24907661) B24907661
theorem B11070071 : Blo 2155435 11070071 := bstep (se 1 (by rfl) ⟨8302553, by rfl⟩ : syracuseStep 11070071 = 16605107) B16605107
theorem B7380047 : Blo 2155435 7380047 := bstep (se 1 (by rfl) ⟨5535035, by rfl⟩ : syracuseStep 7380047 = 11070071) B11070071
theorem B4920031 : Blo 2155435 4920031 := bstep (se 1 (by rfl) ⟨3690023, by rfl⟩ : syracuseStep 4920031 = 7380047) B7380047
theorem B6560041 : Blo 2155435 6560041 := bstep (se 2 (by rfl) ⟨2460015, by rfl⟩ : syracuseStep 6560041 = 4920031) B4920031
theorem B8746721 : Blo 2155435 8746721 := bstep (se 2 (by rfl) ⟨3280020, by rfl⟩ : syracuseStep 8746721 = 6560041) B6560041
theorem B5831147 : Blo 2155435 5831147 := bstep (se 1 (by rfl) ⟨4373360, by rfl⟩ : syracuseStep 5831147 = 8746721) B8746721
theorem B15549725 : Blo 2155435 15549725 := bstep (se 3 (by rfl) ⟨2915573, by rfl⟩ : syracuseStep 15549725 = 5831147) B5831147
theorem B10366483 : Blo 2155435 10366483 := bstep (se 1 (by rfl) ⟨7774862, by rfl⟩ : syracuseStep 10366483 = 15549725) B15549725
theorem B13821977 : Blo 2155435 13821977 := bstep (se 2 (by rfl) ⟨5183241, by rfl⟩ : syracuseStep 13821977 = 10366483) B10366483
theorem B9214651 : Blo 2155435 9214651 := bstep (se 1 (by rfl) ⟨6910988, by rfl⟩ : syracuseStep 9214651 = 13821977) B13821977
theorem B12286201 : Blo 2155435 12286201 := bstep (se 2 (by rfl) ⟨4607325, by rfl⟩ : syracuseStep 12286201 = 9214651) B9214651
theorem B16381601 : Blo 2155435 16381601 := bstep (se 2 (by rfl) ⟨6143100, by rfl⟩ : syracuseStep 16381601 = 12286201) B12286201
theorem B10921067 : Blo 2155435 10921067 := bstep (se 1 (by rfl) ⟨8190800, by rfl⟩ : syracuseStep 10921067 = 16381601) B16381601
theorem B7280711 : Blo 2155435 7280711 := bstep (se 1 (by rfl) ⟨5460533, by rfl⟩ : syracuseStep 7280711 = 10921067) B10921067
theorem B4853807 : Blo 2155435 4853807 := bstep (se 1 (by rfl) ⟨3640355, by rfl⟩ : syracuseStep 4853807 = 7280711) B7280711
theorem B3235871 : Blo 2155435 3235871 := bstep (se 1 (by rfl) ⟨2426903, by rfl⟩ : syracuseStep 3235871 = 4853807) B4853807
theorem B2157247 : Blo 2155435 2157247 := bstep (se 1 (by rfl) ⟨1617935, by rfl⟩ : syracuseStep 2157247 = 3235871) B3235871
theorem B3235877 : Blo 2155435 3235877 := bbase (se 4 (by rfl) ⟨303363, by rfl⟩ : syracuseStep 3235877 = 606727) (by norm_num)
theorem B2157251 : Blo 2155435 2157251 := bstep (se 1 (by rfl) ⟨1617938, by rfl⟩ : syracuseStep 2157251 = 3235877) B3235877
theorem B2730277 : Blo 2155435 2730277 := bbase (se 4 (by rfl) ⟨255963, by rfl⟩ : syracuseStep 2730277 = 511927) (by norm_num)
theorem B3640369 : Blo 2155435 3640369 := bstep (se 2 (by rfl) ⟨1365138, by rfl⟩ : syracuseStep 3640369 = 2730277) B2730277
theorem B4853825 : Blo 2155435 4853825 := bstep (se 2 (by rfl) ⟨1820184, by rfl⟩ : syracuseStep 4853825 = 3640369) B3640369
theorem B3235883 : Blo 2155435 3235883 := bstep (se 1 (by rfl) ⟨2426912, by rfl⟩ : syracuseStep 3235883 = 4853825) B4853825
theorem B2157255 : Blo 2155435 2157255 := bstep (se 1 (by rfl) ⟨1617941, by rfl⟩ : syracuseStep 2157255 = 3235883) B3235883
theorem B2426917 : Blo 2155435 2426917 := bbase (se 4 (by rfl) ⟨227523, by rfl⟩ : syracuseStep 2426917 = 455047) (by norm_num)
theorem B3235889 : Blo 2155435 3235889 := bstep (se 2 (by rfl) ⟨1213458, by rfl⟩ : syracuseStep 3235889 = 2426917) B2426917
theorem B2157259 : Blo 2155435 2157259 := bstep (se 1 (by rfl) ⟨1617944, by rfl⟩ : syracuseStep 2157259 = 3235889) B3235889
theorem B3887461 : Blo 2155435 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B5183281 : Blo 2155435 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B6911041 : Blo 2155435 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B9214721 : Blo 2155435 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B6143147 : Blo 2155435 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B4095431 : Blo 2155435 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B2730287 : Blo 2155435 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B7280765 : Blo 2155435 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B4853843 : Blo 2155435 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B3235895 : Blo 2155435 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B2157263 : Blo 2155435 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B3235901 : Blo 2155435 3235901 := bbase (se 3 (by rfl) ⟨606731, by rfl⟩ : syracuseStep 3235901 = 1213463) (by norm_num)
theorem B2157267 : Blo 2155435 2157267 := bstep (se 1 (by rfl) ⟨1617950, by rfl⟩ : syracuseStep 2157267 = 3235901) B3235901
theorem B4853861 : Blo 2155435 4853861 := bbase (se 4 (by rfl) ⟨455049, by rfl⟩ : syracuseStep 4853861 = 910099) (by norm_num)
theorem B3235907 : Blo 2155435 3235907 := bstep (se 1 (by rfl) ⟨2426930, by rfl⟩ : syracuseStep 3235907 = 4853861) B4853861
theorem B2157271 : Blo 2155435 2157271 := bstep (se 1 (by rfl) ⟨1617953, by rfl⟩ : syracuseStep 2157271 = 3235907) B3235907
theorem B5460605 : Blo 2155435 5460605 := bbase (se 3 (by rfl) ⟨1023863, by rfl⟩ : syracuseStep 5460605 = 2047727) (by norm_num)
theorem B3640403 : Blo 2155435 3640403 := bstep (se 1 (by rfl) ⟨2730302, by rfl⟩ : syracuseStep 3640403 = 5460605) B5460605
theorem B2426935 : Blo 2155435 2426935 := bstep (se 1 (by rfl) ⟨1820201, by rfl⟩ : syracuseStep 2426935 = 3640403) B3640403
theorem B3235913 : Blo 2155435 3235913 := bstep (se 2 (by rfl) ⟨1213467, by rfl⟩ : syracuseStep 3235913 = 2426935) B2426935
theorem B2157275 : Blo 2155435 2157275 := bstep (se 1 (by rfl) ⟨1617956, by rfl⟩ : syracuseStep 2157275 = 3235913) B3235913
theorem B4095461 : Blo 2155435 4095461 := bbase (se 4 (by rfl) ⟨383949, by rfl⟩ : syracuseStep 4095461 = 767899) (by norm_num)
theorem B10921229 : Blo 2155435 10921229 := bstep (se 3 (by rfl) ⟨2047730, by rfl⟩ : syracuseStep 10921229 = 4095461) B4095461
theorem B7280819 : Blo 2155435 7280819 := bstep (se 1 (by rfl) ⟨5460614, by rfl⟩ : syracuseStep 7280819 = 10921229) B10921229
theorem B4853879 : Blo 2155435 4853879 := bstep (se 1 (by rfl) ⟨3640409, by rfl⟩ : syracuseStep 4853879 = 7280819) B7280819
theorem B3235919 : Blo 2155435 3235919 := bstep (se 1 (by rfl) ⟨2426939, by rfl⟩ : syracuseStep 3235919 = 4853879) B4853879
theorem B2157279 : Blo 2155435 2157279 := bstep (se 1 (by rfl) ⟨1617959, by rfl⟩ : syracuseStep 2157279 = 3235919) B3235919
theorem B3235925 : Blo 2155435 3235925 := bbase (se 8 (by rfl) ⟨18960, by rfl⟩ : syracuseStep 3235925 = 37921) (by norm_num)
theorem B2157283 : Blo 2155435 2157283 := bstep (se 1 (by rfl) ⟨1617962, by rfl⟩ : syracuseStep 2157283 = 3235925) B3235925
theorem B2627029 : Blo 2155435 2627029 := bbase (se 7 (by rfl) ⟨30785, by rfl⟩ : syracuseStep 2627029 = 61571) (by norm_num)
theorem B3502705 : Blo 2155435 3502705 := bstep (se 2 (by rfl) ⟨1313514, by rfl⟩ : syracuseStep 3502705 = 2627029) B2627029
theorem B4670273 : Blo 2155435 4670273 := bstep (se 2 (by rfl) ⟨1751352, by rfl⟩ : syracuseStep 4670273 = 3502705) B3502705
theorem B3113515 : Blo 2155435 3113515 := bstep (se 1 (by rfl) ⟨2335136, by rfl⟩ : syracuseStep 3113515 = 4670273) B4670273
theorem B16605413 : Blo 2155435 16605413 := bstep (se 4 (by rfl) ⟨1556757, by rfl⟩ : syracuseStep 16605413 = 3113515) B3113515
theorem B11070275 : Blo 2155435 11070275 := bstep (se 1 (by rfl) ⟨8302706, by rfl⟩ : syracuseStep 11070275 = 16605413) B16605413
theorem B118082933 : Blo 2155435 118082933 := bstep (se 5 (by rfl) ⟨5535137, by rfl⟩ : syracuseStep 118082933 = 11070275) B11070275
theorem B78721955 : Blo 2155435 78721955 := bstep (se 1 (by rfl) ⟨59041466, by rfl⟩ : syracuseStep 78721955 = 118082933) B118082933
theorem B52481303 : Blo 2155435 52481303 := bstep (se 1 (by rfl) ⟨39360977, by rfl⟩ : syracuseStep 52481303 = 78721955) B78721955
theorem B34987535 : Blo 2155435 34987535 := bstep (se 1 (by rfl) ⟨26240651, by rfl⟩ : syracuseStep 34987535 = 52481303) B52481303
theorem B23325023 : Blo 2155435 23325023 := bstep (se 1 (by rfl) ⟨17493767, by rfl⟩ : syracuseStep 23325023 = 34987535) B34987535
theorem B15550015 : Blo 2155435 15550015 := bstep (se 1 (by rfl) ⟨11662511, by rfl⟩ : syracuseStep 15550015 = 23325023) B23325023
theorem B20733353 : Blo 2155435 20733353 := bstep (se 2 (by rfl) ⟨7775007, by rfl⟩ : syracuseStep 20733353 = 15550015) B15550015
theorem B13822235 : Blo 2155435 13822235 := bstep (se 1 (by rfl) ⟨10366676, by rfl⟩ : syracuseStep 13822235 = 20733353) B20733353
theorem B9214823 : Blo 2155435 9214823 := bstep (se 1 (by rfl) ⟨6911117, by rfl⟩ : syracuseStep 9214823 = 13822235) B13822235
theorem B6143215 : Blo 2155435 6143215 := bstep (se 1 (by rfl) ⟨4607411, by rfl⟩ : syracuseStep 6143215 = 9214823) B9214823
theorem B8190953 : Blo 2155435 8190953 := bstep (se 2 (by rfl) ⟨3071607, by rfl⟩ : syracuseStep 8190953 = 6143215) B6143215
theorem B5460635 : Blo 2155435 5460635 := bstep (se 1 (by rfl) ⟨4095476, by rfl⟩ : syracuseStep 5460635 = 8190953) B8190953
theorem B3640423 : Blo 2155435 3640423 := bstep (se 1 (by rfl) ⟨2730317, by rfl⟩ : syracuseStep 3640423 = 5460635) B5460635
theorem B4853897 : Blo 2155435 4853897 := bstep (se 2 (by rfl) ⟨1820211, by rfl⟩ : syracuseStep 4853897 = 3640423) B3640423
theorem B3235931 : Blo 2155435 3235931 := bstep (se 1 (by rfl) ⟨2426948, by rfl⟩ : syracuseStep 3235931 = 4853897) B4853897
theorem B2157287 : Blo 2155435 2157287 := bstep (se 1 (by rfl) ⟨1617965, by rfl⟩ : syracuseStep 2157287 = 3235931) B3235931
theorem B2426953 : Blo 2155435 2426953 := bbase (se 2 (by rfl) ⟨910107, by rfl⟩ : syracuseStep 2426953 = 1820215) (by norm_num)
theorem B3235937 : Blo 2155435 3235937 := bstep (se 2 (by rfl) ⟨1213476, by rfl⟩ : syracuseStep 3235937 = 2426953) B2426953
theorem B2157291 : Blo 2155435 2157291 := bstep (se 1 (by rfl) ⟨1617968, by rfl⟩ : syracuseStep 2157291 = 3235937) B3235937
theorem B5183357 : Blo 2155435 5183357 := bbase (se 3 (by rfl) ⟨971879, by rfl⟩ : syracuseStep 5183357 = 1943759) (by norm_num)
theorem B13822285 : Blo 2155435 13822285 := bstep (se 3 (by rfl) ⟨2591678, by rfl⟩ : syracuseStep 13822285 = 5183357) B5183357
theorem B18429713 : Blo 2155435 18429713 := bstep (se 2 (by rfl) ⟨6911142, by rfl⟩ : syracuseStep 18429713 = 13822285) B13822285
theorem B12286475 : Blo 2155435 12286475 := bstep (se 1 (by rfl) ⟨9214856, by rfl⟩ : syracuseStep 12286475 = 18429713) B18429713
theorem B8190983 : Blo 2155435 8190983 := bstep (se 1 (by rfl) ⟨6143237, by rfl⟩ : syracuseStep 8190983 = 12286475) B12286475
theorem B5460655 : Blo 2155435 5460655 := bstep (se 1 (by rfl) ⟨4095491, by rfl⟩ : syracuseStep 5460655 = 8190983) B8190983
theorem B7280873 : Blo 2155435 7280873 := bstep (se 2 (by rfl) ⟨2730327, by rfl⟩ : syracuseStep 7280873 = 5460655) B5460655
theorem B4853915 : Blo 2155435 4853915 := bstep (se 1 (by rfl) ⟨3640436, by rfl⟩ : syracuseStep 4853915 = 7280873) B7280873
theorem B3235943 : Blo 2155435 3235943 := bstep (se 1 (by rfl) ⟨2426957, by rfl⟩ : syracuseStep 3235943 = 4853915) B4853915
theorem B2157295 : Blo 2155435 2157295 := bstep (se 1 (by rfl) ⟨1617971, by rfl⟩ : syracuseStep 2157295 = 3235943) B3235943
theorem B3235949 : Blo 2155435 3235949 := bbase (se 3 (by rfl) ⟨606740, by rfl⟩ : syracuseStep 3235949 = 1213481) (by norm_num)
theorem B2157299 : Blo 2155435 2157299 := bstep (se 1 (by rfl) ⟨1617974, by rfl⟩ : syracuseStep 2157299 = 3235949) B3235949
theorem B4853933 : Blo 2155435 4853933 := bbase (se 3 (by rfl) ⟨910112, by rfl⟩ : syracuseStep 4853933 = 1820225) (by norm_num)
theorem B3235955 : Blo 2155435 3235955 := bstep (se 1 (by rfl) ⟨2426966, by rfl⟩ : syracuseStep 3235955 = 4853933) B4853933
theorem B2157303 : Blo 2155435 2157303 := bstep (se 1 (by rfl) ⟨1617977, by rfl⟩ : syracuseStep 2157303 = 3235955) B3235955
theorem B5254109 : Blo 2155435 5254109 := bbase (se 3 (by rfl) ⟨985145, by rfl⟩ : syracuseStep 5254109 = 1970291) (by norm_num)
theorem B3502739 : Blo 2155435 3502739 := bstep (se 1 (by rfl) ⟨2627054, by rfl⟩ : syracuseStep 3502739 = 5254109) B5254109
theorem B2335159 : Blo 2155435 2335159 := bstep (se 1 (by rfl) ⟨1751369, by rfl⟩ : syracuseStep 2335159 = 3502739) B3502739
theorem B12454181 : Blo 2155435 12454181 := bstep (se 4 (by rfl) ⟨1167579, by rfl⟩ : syracuseStep 12454181 = 2335159) B2335159
theorem B8302787 : Blo 2155435 8302787 := bstep (se 1 (by rfl) ⟨6227090, by rfl⟩ : syracuseStep 8302787 = 12454181) B12454181
theorem B5535191 : Blo 2155435 5535191 := bstep (se 1 (by rfl) ⟨4151393, by rfl⟩ : syracuseStep 5535191 = 8302787) B8302787
theorem B3690127 : Blo 2155435 3690127 := bstep (se 1 (by rfl) ⟨2767595, by rfl⟩ : syracuseStep 3690127 = 5535191) B5535191
theorem B19680677 : Blo 2155435 19680677 := bstep (se 4 (by rfl) ⟨1845063, by rfl⟩ : syracuseStep 19680677 = 3690127) B3690127
theorem B13120451 : Blo 2155435 13120451 := bstep (se 1 (by rfl) ⟨9840338, by rfl⟩ : syracuseStep 13120451 = 19680677) B19680677
theorem B8746967 : Blo 2155435 8746967 := bstep (se 1 (by rfl) ⟨6560225, by rfl⟩ : syracuseStep 8746967 = 13120451) B13120451
theorem B23325245 : Blo 2155435 23325245 := bstep (se 3 (by rfl) ⟨4373483, by rfl⟩ : syracuseStep 23325245 = 8746967) B8746967
theorem B15550163 : Blo 2155435 15550163 := bstep (se 1 (by rfl) ⟨11662622, by rfl⟩ : syracuseStep 15550163 = 23325245) B23325245
theorem B10366775 : Blo 2155435 10366775 := bstep (se 1 (by rfl) ⟨7775081, by rfl⟩ : syracuseStep 10366775 = 15550163) B15550163
theorem B6911183 : Blo 2155435 6911183 := bstep (se 1 (by rfl) ⟨5183387, by rfl⟩ : syracuseStep 6911183 = 10366775) B10366775
theorem B4607455 : Blo 2155435 4607455 := bstep (se 1 (by rfl) ⟨3455591, by rfl⟩ : syracuseStep 4607455 = 6911183) B6911183
theorem B6143273 : Blo 2155435 6143273 := bstep (se 2 (by rfl) ⟨2303727, by rfl⟩ : syracuseStep 6143273 = 4607455) B4607455
theorem B4095515 : Blo 2155435 4095515 := bstep (se 1 (by rfl) ⟨3071636, by rfl⟩ : syracuseStep 4095515 = 6143273) B6143273
theorem B2730343 : Blo 2155435 2730343 := bstep (se 1 (by rfl) ⟨2047757, by rfl⟩ : syracuseStep 2730343 = 4095515) B4095515
theorem B3640457 : Blo 2155435 3640457 := bstep (se 2 (by rfl) ⟨1365171, by rfl⟩ : syracuseStep 3640457 = 2730343) B2730343
theorem B2426971 : Blo 2155435 2426971 := bstep (se 1 (by rfl) ⟨1820228, by rfl⟩ : syracuseStep 2426971 = 3640457) B3640457
theorem B3235961 : Blo 2155435 3235961 := bstep (se 2 (by rfl) ⟨1213485, by rfl⟩ : syracuseStep 3235961 = 2426971) B2426971
theorem B2157307 : Blo 2155435 2157307 := bstep (se 1 (by rfl) ⟨1617980, by rfl⟩ : syracuseStep 2157307 = 3235961) B3235961
theorem B7775093 : Blo 2155435 7775093 := bbase (se 5 (by rfl) ⟨364457, by rfl⟩ : syracuseStep 7775093 = 728915) (by norm_num)
theorem B5183395 : Blo 2155435 5183395 := bstep (se 1 (by rfl) ⟨3887546, by rfl⟩ : syracuseStep 5183395 = 7775093) B7775093
theorem B27644773 : Blo 2155435 27644773 := bstep (se 4 (by rfl) ⟨2591697, by rfl⟩ : syracuseStep 27644773 = 5183395) B5183395
theorem B36859697 : Blo 2155435 36859697 := bstep (se 2 (by rfl) ⟨13822386, by rfl⟩ : syracuseStep 36859697 = 27644773) B27644773
theorem B24573131 : Blo 2155435 24573131 := bstep (se 1 (by rfl) ⟨18429848, by rfl⟩ : syracuseStep 24573131 = 36859697) B36859697
theorem B16382087 : Blo 2155435 16382087 := bstep (se 1 (by rfl) ⟨12286565, by rfl⟩ : syracuseStep 16382087 = 24573131) B24573131
theorem B10921391 : Blo 2155435 10921391 := bstep (se 1 (by rfl) ⟨8191043, by rfl⟩ : syracuseStep 10921391 = 16382087) B16382087
theorem B7280927 : Blo 2155435 7280927 := bstep (se 1 (by rfl) ⟨5460695, by rfl⟩ : syracuseStep 7280927 = 10921391) B10921391
theorem B4853951 : Blo 2155435 4853951 := bstep (se 1 (by rfl) ⟨3640463, by rfl⟩ : syracuseStep 4853951 = 7280927) B7280927
theorem B3235967 : Blo 2155435 3235967 := bstep (se 1 (by rfl) ⟨2426975, by rfl⟩ : syracuseStep 3235967 = 4853951) B4853951
theorem B2157311 : Blo 2155435 2157311 := bstep (se 1 (by rfl) ⟨1617983, by rfl⟩ : syracuseStep 2157311 = 3235967) B3235967
theorem B3235973 : Blo 2155435 3235973 := bbase (se 4 (by rfl) ⟨303372, by rfl⟩ : syracuseStep 3235973 = 606745) (by norm_num)
theorem B2157315 : Blo 2155435 2157315 := bstep (se 1 (by rfl) ⟨1617986, by rfl⟩ : syracuseStep 2157315 = 3235973) B3235973
theorem B3640477 : Blo 2155435 3640477 := bbase (se 3 (by rfl) ⟨682589, by rfl⟩ : syracuseStep 3640477 = 1365179) (by norm_num)
theorem B4853969 : Blo 2155435 4853969 := bstep (se 2 (by rfl) ⟨1820238, by rfl⟩ : syracuseStep 4853969 = 3640477) B3640477
theorem B3235979 : Blo 2155435 3235979 := bstep (se 1 (by rfl) ⟨2426984, by rfl⟩ : syracuseStep 3235979 = 4853969) B4853969
theorem B2157319 : Blo 2155435 2157319 := bstep (se 1 (by rfl) ⟨1617989, by rfl⟩ : syracuseStep 2157319 = 3235979) B3235979
theorem B2426989 : Blo 2155435 2426989 := bbase (se 3 (by rfl) ⟨455060, by rfl⟩ : syracuseStep 2426989 = 910121) (by norm_num)
theorem B3235985 : Blo 2155435 3235985 := bstep (se 2 (by rfl) ⟨1213494, by rfl⟩ : syracuseStep 3235985 = 2426989) B2426989
theorem B2157323 : Blo 2155435 2157323 := bstep (se 1 (by rfl) ⟨1617992, by rfl⟩ : syracuseStep 2157323 = 3235985) B3235985
theorem B7280981 : Blo 2155435 7280981 := bbase (se 10 (by rfl) ⟨10665, by rfl⟩ : syracuseStep 7280981 = 21331) (by norm_num)
theorem B4853987 : Blo 2155435 4853987 := bstep (se 1 (by rfl) ⟨3640490, by rfl⟩ : syracuseStep 4853987 = 7280981) B7280981
theorem B3235991 : Blo 2155435 3235991 := bstep (se 1 (by rfl) ⟨2426993, by rfl⟩ : syracuseStep 3235991 = 4853987) B4853987
theorem B2157327 : Blo 2155435 2157327 := bstep (se 1 (by rfl) ⟨1617995, by rfl⟩ : syracuseStep 2157327 = 3235991) B3235991
theorem B3235997 : Blo 2155435 3235997 := bbase (se 3 (by rfl) ⟨606749, by rfl⟩ : syracuseStep 3235997 = 1213499) (by norm_num)
theorem B2157331 : Blo 2155435 2157331 := bstep (se 1 (by rfl) ⟨1617998, by rfl⟩ : syracuseStep 2157331 = 3235997) B3235997
theorem B4854005 : Blo 2155435 4854005 := bbase (se 5 (by rfl) ⟨227531, by rfl⟩ : syracuseStep 4854005 = 455063) (by norm_num)
theorem B3236003 : Blo 2155435 3236003 := bstep (se 1 (by rfl) ⟨2427002, by rfl⟩ : syracuseStep 3236003 = 4854005) B4854005
theorem B2157335 : Blo 2155435 2157335 := bstep (se 1 (by rfl) ⟨1618001, by rfl⟩ : syracuseStep 2157335 = 3236003) B3236003
theorem B3690181 : Blo 2155435 3690181 := bbase (se 4 (by rfl) ⟨345954, by rfl⟩ : syracuseStep 3690181 = 691909) (by norm_num)
theorem B19680965 : Blo 2155435 19680965 := bstep (se 4 (by rfl) ⟨1845090, by rfl⟩ : syracuseStep 19680965 = 3690181) B3690181
theorem B13120643 : Blo 2155435 13120643 := bstep (se 1 (by rfl) ⟨9840482, by rfl⟩ : syracuseStep 13120643 = 19680965) B19680965
theorem B8747095 : Blo 2155435 8747095 := bstep (se 1 (by rfl) ⟨6560321, by rfl⟩ : syracuseStep 8747095 = 13120643) B13120643
theorem B11662793 : Blo 2155435 11662793 := bstep (se 2 (by rfl) ⟨4373547, by rfl⟩ : syracuseStep 11662793 = 8747095) B8747095
theorem B7775195 : Blo 2155435 7775195 := bstep (se 1 (by rfl) ⟨5831396, by rfl⟩ : syracuseStep 7775195 = 11662793) B11662793
theorem B20733853 : Blo 2155435 20733853 := bstep (se 3 (by rfl) ⟨3887597, by rfl⟩ : syracuseStep 20733853 = 7775195) B7775195
theorem B27645137 : Blo 2155435 27645137 := bstep (se 2 (by rfl) ⟨10366926, by rfl⟩ : syracuseStep 27645137 = 20733853) B20733853
theorem B18430091 : Blo 2155435 18430091 := bstep (se 1 (by rfl) ⟨13822568, by rfl⟩ : syracuseStep 18430091 = 27645137) B27645137
theorem B12286727 : Blo 2155435 12286727 := bstep (se 1 (by rfl) ⟨9215045, by rfl⟩ : syracuseStep 12286727 = 18430091) B18430091
theorem B8191151 : Blo 2155435 8191151 := bstep (se 1 (by rfl) ⟨6143363, by rfl⟩ : syracuseStep 8191151 = 12286727) B12286727
theorem B5460767 : Blo 2155435 5460767 := bstep (se 1 (by rfl) ⟨4095575, by rfl⟩ : syracuseStep 5460767 = 8191151) B8191151
theorem B3640511 : Blo 2155435 3640511 := bstep (se 1 (by rfl) ⟨2730383, by rfl⟩ : syracuseStep 3640511 = 5460767) B5460767
theorem B2427007 : Blo 2155435 2427007 := bstep (se 1 (by rfl) ⟨1820255, by rfl⟩ : syracuseStep 2427007 = 3640511) B3640511
theorem B3236009 : Blo 2155435 3236009 := bstep (se 2 (by rfl) ⟨1213503, by rfl⟩ : syracuseStep 3236009 = 2427007) B2427007
theorem B2157339 : Blo 2155435 2157339 := bstep (se 1 (by rfl) ⟨1618004, by rfl⟩ : syracuseStep 2157339 = 3236009) B3236009
theorem B3887605 : Blo 2155435 3887605 := bbase (se 5 (by rfl) ⟨182231, by rfl⟩ : syracuseStep 3887605 = 364463) (by norm_num)
theorem B5183473 : Blo 2155435 5183473 := bstep (se 2 (by rfl) ⟨1943802, by rfl⟩ : syracuseStep 5183473 = 3887605) B3887605
theorem B6911297 : Blo 2155435 6911297 := bstep (se 2 (by rfl) ⟨2591736, by rfl⟩ : syracuseStep 6911297 = 5183473) B5183473
theorem B4607531 : Blo 2155435 4607531 := bstep (se 1 (by rfl) ⟨3455648, by rfl⟩ : syracuseStep 4607531 = 6911297) B6911297
theorem B3071687 : Blo 2155435 3071687 := bstep (se 1 (by rfl) ⟨2303765, by rfl⟩ : syracuseStep 3071687 = 4607531) B4607531
theorem B8191165 : Blo 2155435 8191165 := bstep (se 3 (by rfl) ⟨1535843, by rfl⟩ : syracuseStep 8191165 = 3071687) B3071687
theorem B10921553 : Blo 2155435 10921553 := bstep (se 2 (by rfl) ⟨4095582, by rfl⟩ : syracuseStep 10921553 = 8191165) B8191165
theorem B7281035 : Blo 2155435 7281035 := bstep (se 1 (by rfl) ⟨5460776, by rfl⟩ : syracuseStep 7281035 = 10921553) B10921553
theorem B4854023 : Blo 2155435 4854023 := bstep (se 1 (by rfl) ⟨3640517, by rfl⟩ : syracuseStep 4854023 = 7281035) B7281035
theorem B3236015 : Blo 2155435 3236015 := bstep (se 1 (by rfl) ⟨2427011, by rfl⟩ : syracuseStep 3236015 = 4854023) B4854023
theorem B2157343 : Blo 2155435 2157343 := bstep (se 1 (by rfl) ⟨1618007, by rfl⟩ : syracuseStep 2157343 = 3236015) B3236015
theorem B3236021 : Blo 2155435 3236021 := bbase (se 5 (by rfl) ⟨151688, by rfl⟩ : syracuseStep 3236021 = 303377) (by norm_num)
theorem B2157347 : Blo 2155435 2157347 := bstep (se 1 (by rfl) ⟨1618010, by rfl⟩ : syracuseStep 2157347 = 3236021) B3236021
theorem B5460797 : Blo 2155435 5460797 := bbase (se 3 (by rfl) ⟨1023899, by rfl⟩ : syracuseStep 5460797 = 2047799) (by norm_num)
theorem B3640531 : Blo 2155435 3640531 := bstep (se 1 (by rfl) ⟨2730398, by rfl⟩ : syracuseStep 3640531 = 5460797) B5460797
theorem B4854041 : Blo 2155435 4854041 := bstep (se 2 (by rfl) ⟨1820265, by rfl⟩ : syracuseStep 4854041 = 3640531) B3640531
theorem B3236027 : Blo 2155435 3236027 := bstep (se 1 (by rfl) ⟨2427020, by rfl⟩ : syracuseStep 3236027 = 4854041) B4854041
theorem B2157351 : Blo 2155435 2157351 := bstep (se 1 (by rfl) ⟨1618013, by rfl⟩ : syracuseStep 2157351 = 3236027) B3236027
theorem B2427025 : Blo 2155435 2427025 := bbase (se 2 (by rfl) ⟨910134, by rfl⟩ : syracuseStep 2427025 = 1820269) (by norm_num)
theorem B3236033 : Blo 2155435 3236033 := bstep (se 2 (by rfl) ⟨1213512, by rfl⟩ : syracuseStep 3236033 = 2427025) B2427025
theorem B2157355 : Blo 2155435 2157355 := bstep (se 1 (by rfl) ⟨1618016, by rfl⟩ : syracuseStep 2157355 = 3236033) B3236033
theorem B4095613 : Blo 2155435 4095613 := bbase (se 3 (by rfl) ⟨767927, by rfl⟩ : syracuseStep 4095613 = 1535855) (by norm_num)
theorem B5460817 : Blo 2155435 5460817 := bstep (se 2 (by rfl) ⟨2047806, by rfl⟩ : syracuseStep 5460817 = 4095613) B4095613
theorem B7281089 : Blo 2155435 7281089 := bstep (se 2 (by rfl) ⟨2730408, by rfl⟩ : syracuseStep 7281089 = 5460817) B5460817
theorem B4854059 : Blo 2155435 4854059 := bstep (se 1 (by rfl) ⟨3640544, by rfl⟩ : syracuseStep 4854059 = 7281089) B7281089
theorem B3236039 : Blo 2155435 3236039 := bstep (se 1 (by rfl) ⟨2427029, by rfl⟩ : syracuseStep 3236039 = 4854059) B4854059
theorem B2157359 : Blo 2155435 2157359 := bstep (se 1 (by rfl) ⟨1618019, by rfl⟩ : syracuseStep 2157359 = 3236039) B3236039
theorem B3236045 : Blo 2155435 3236045 := bbase (se 3 (by rfl) ⟨606758, by rfl⟩ : syracuseStep 3236045 = 1213517) (by norm_num)
theorem B2157363 : Blo 2155435 2157363 := bstep (se 1 (by rfl) ⟨1618022, by rfl⟩ : syracuseStep 2157363 = 3236045) B3236045
theorem B4854077 : Blo 2155435 4854077 := bbase (se 3 (by rfl) ⟨910139, by rfl⟩ : syracuseStep 4854077 = 1820279) (by norm_num)
theorem B3236051 : Blo 2155435 3236051 := bstep (se 1 (by rfl) ⟨2427038, by rfl⟩ : syracuseStep 3236051 = 4854077) B4854077
theorem B2157367 : Blo 2155435 2157367 := bstep (se 1 (by rfl) ⟨1618025, by rfl⟩ : syracuseStep 2157367 = 3236051) B3236051
theorem B3640565 : Blo 2155435 3640565 := bbase (se 5 (by rfl) ⟨170651, by rfl⟩ : syracuseStep 3640565 = 341303) (by norm_num)
theorem B2427043 : Blo 2155435 2427043 := bstep (se 1 (by rfl) ⟨1820282, by rfl⟩ : syracuseStep 2427043 = 3640565) B3640565
theorem B3236057 : Blo 2155435 3236057 := bstep (se 2 (by rfl) ⟨1213521, by rfl⟩ : syracuseStep 3236057 = 2427043) B2427043
theorem B2157371 : Blo 2155435 2157371 := bstep (se 1 (by rfl) ⟨1618028, by rfl⟩ : syracuseStep 2157371 = 3236057) B3236057
theorem B7380485 : Blo 2155435 7380485 := bbase (se 4 (by rfl) ⟨691920, by rfl⟩ : syracuseStep 7380485 = 1383841) (by norm_num)
theorem B4920323 : Blo 2155435 4920323 := bstep (se 1 (by rfl) ⟨3690242, by rfl⟩ : syracuseStep 4920323 = 7380485) B7380485
theorem B13120861 : Blo 2155435 13120861 := bstep (se 3 (by rfl) ⟨2460161, by rfl⟩ : syracuseStep 13120861 = 4920323) B4920323
theorem B17494481 : Blo 2155435 17494481 := bstep (se 2 (by rfl) ⟨6560430, by rfl⟩ : syracuseStep 17494481 = 13120861) B13120861
theorem B11662987 : Blo 2155435 11662987 := bstep (se 1 (by rfl) ⟨8747240, by rfl⟩ : syracuseStep 11662987 = 17494481) B17494481
theorem B15550649 : Blo 2155435 15550649 := bstep (se 2 (by rfl) ⟨5831493, by rfl⟩ : syracuseStep 15550649 = 11662987) B11662987
theorem B10367099 : Blo 2155435 10367099 := bstep (se 1 (by rfl) ⟨7775324, by rfl⟩ : syracuseStep 10367099 = 15550649) B15550649
theorem B6911399 : Blo 2155435 6911399 := bstep (se 1 (by rfl) ⟨5183549, by rfl⟩ : syracuseStep 6911399 = 10367099) B10367099
theorem B4607599 : Blo 2155435 4607599 := bstep (se 1 (by rfl) ⟨3455699, by rfl⟩ : syracuseStep 4607599 = 6911399) B6911399
theorem B6143465 : Blo 2155435 6143465 := bstep (se 2 (by rfl) ⟨2303799, by rfl⟩ : syracuseStep 6143465 = 4607599) B4607599
theorem B16382573 : Blo 2155435 16382573 := bstep (se 3 (by rfl) ⟨3071732, by rfl⟩ : syracuseStep 16382573 = 6143465) B6143465
theorem B10921715 : Blo 2155435 10921715 := bstep (se 1 (by rfl) ⟨8191286, by rfl⟩ : syracuseStep 10921715 = 16382573) B16382573
theorem B7281143 : Blo 2155435 7281143 := bstep (se 1 (by rfl) ⟨5460857, by rfl⟩ : syracuseStep 7281143 = 10921715) B10921715
theorem B4854095 : Blo 2155435 4854095 := bstep (se 1 (by rfl) ⟨3640571, by rfl⟩ : syracuseStep 4854095 = 7281143) B7281143
theorem B3236063 : Blo 2155435 3236063 := bstep (se 1 (by rfl) ⟨2427047, by rfl⟩ : syracuseStep 3236063 = 4854095) B4854095
theorem B2157375 : Blo 2155435 2157375 := bstep (se 1 (by rfl) ⟨1618031, by rfl⟩ : syracuseStep 2157375 = 3236063) B3236063
theorem B3236069 : Blo 2155435 3236069 := bbase (se 4 (by rfl) ⟨303381, by rfl⟩ : syracuseStep 3236069 = 606763) (by norm_num)
theorem B2157379 : Blo 2155435 2157379 := bstep (se 1 (by rfl) ⟨1618034, by rfl⟩ : syracuseStep 2157379 = 3236069) B3236069
theorem B2591785 : Blo 2155435 2591785 := bbase (se 2 (by rfl) ⟨971919, by rfl⟩ : syracuseStep 2591785 = 1943839) (by norm_num)
theorem B3455713 : Blo 2155435 3455713 := bstep (se 2 (by rfl) ⟨1295892, by rfl⟩ : syracuseStep 3455713 = 2591785) B2591785
theorem B4607617 : Blo 2155435 4607617 := bstep (se 2 (by rfl) ⟨1727856, by rfl⟩ : syracuseStep 4607617 = 3455713) B3455713
theorem B6143489 : Blo 2155435 6143489 := bstep (se 2 (by rfl) ⟨2303808, by rfl⟩ : syracuseStep 6143489 = 4607617) B4607617
theorem B4095659 : Blo 2155435 4095659 := bstep (se 1 (by rfl) ⟨3071744, by rfl⟩ : syracuseStep 4095659 = 6143489) B6143489
theorem B2730439 : Blo 2155435 2730439 := bstep (se 1 (by rfl) ⟨2047829, by rfl⟩ : syracuseStep 2730439 = 4095659) B4095659
theorem B3640585 : Blo 2155435 3640585 := bstep (se 2 (by rfl) ⟨1365219, by rfl⟩ : syracuseStep 3640585 = 2730439) B2730439
theorem B4854113 : Blo 2155435 4854113 := bstep (se 2 (by rfl) ⟨1820292, by rfl⟩ : syracuseStep 4854113 = 3640585) B3640585
theorem B3236075 : Blo 2155435 3236075 := bstep (se 1 (by rfl) ⟨2427056, by rfl⟩ : syracuseStep 3236075 = 4854113) B4854113
theorem B2157383 : Blo 2155435 2157383 := bstep (se 1 (by rfl) ⟨1618037, by rfl⟩ : syracuseStep 2157383 = 3236075) B3236075
theorem B2427061 : Blo 2155435 2427061 := bbase (se 5 (by rfl) ⟨113768, by rfl⟩ : syracuseStep 2427061 = 227537) (by norm_num)
theorem B3236081 : Blo 2155435 3236081 := bstep (se 2 (by rfl) ⟨1213530, by rfl⟩ : syracuseStep 3236081 = 2427061) B2427061
theorem B2157387 : Blo 2155435 2157387 := bstep (se 1 (by rfl) ⟨1618040, by rfl⟩ : syracuseStep 2157387 = 3236081) B3236081
theorem B2730449 : Blo 2155435 2730449 := bbase (se 2 (by rfl) ⟨1023918, by rfl⟩ : syracuseStep 2730449 = 2047837) (by norm_num)
theorem B7281197 : Blo 2155435 7281197 := bstep (se 3 (by rfl) ⟨1365224, by rfl⟩ : syracuseStep 7281197 = 2730449) B2730449
theorem B4854131 : Blo 2155435 4854131 := bstep (se 1 (by rfl) ⟨3640598, by rfl⟩ : syracuseStep 4854131 = 7281197) B7281197
theorem B3236087 : Blo 2155435 3236087 := bstep (se 1 (by rfl) ⟨2427065, by rfl⟩ : syracuseStep 3236087 = 4854131) B4854131
theorem B2157391 : Blo 2155435 2157391 := bstep (se 1 (by rfl) ⟨1618043, by rfl⟩ : syracuseStep 2157391 = 3236087) B3236087
theorem B3236093 : Blo 2155435 3236093 := bbase (se 3 (by rfl) ⟨606767, by rfl⟩ : syracuseStep 3236093 = 1213535) (by norm_num)
theorem B2157395 : Blo 2155435 2157395 := bstep (se 1 (by rfl) ⟨1618046, by rfl⟩ : syracuseStep 2157395 = 3236093) B3236093
theorem B4854149 : Blo 2155435 4854149 := bbase (se 4 (by rfl) ⟨455076, by rfl⟩ : syracuseStep 4854149 = 910153) (by norm_num)
theorem B3236099 : Blo 2155435 3236099 := bstep (se 1 (by rfl) ⟨2427074, by rfl⟩ : syracuseStep 3236099 = 4854149) B4854149
theorem B2157399 : Blo 2155435 2157399 := bstep (se 1 (by rfl) ⟨1618049, by rfl⟩ : syracuseStep 2157399 = 3236099) B3236099
theorem B3071773 : Blo 2155435 3071773 := bbase (se 3 (by rfl) ⟨575957, by rfl⟩ : syracuseStep 3071773 = 1151915) (by norm_num)
theorem B4095697 : Blo 2155435 4095697 := bstep (se 2 (by rfl) ⟨1535886, by rfl⟩ : syracuseStep 4095697 = 3071773) B3071773
theorem B5460929 : Blo 2155435 5460929 := bstep (se 2 (by rfl) ⟨2047848, by rfl⟩ : syracuseStep 5460929 = 4095697) B4095697
theorem B3640619 : Blo 2155435 3640619 := bstep (se 1 (by rfl) ⟨2730464, by rfl⟩ : syracuseStep 3640619 = 5460929) B5460929
theorem B2427079 : Blo 2155435 2427079 := bstep (se 1 (by rfl) ⟨1820309, by rfl⟩ : syracuseStep 2427079 = 3640619) B3640619
theorem B3236105 : Blo 2155435 3236105 := bstep (se 2 (by rfl) ⟨1213539, by rfl⟩ : syracuseStep 3236105 = 2427079) B2427079
theorem B2157403 : Blo 2155435 2157403 := bstep (se 1 (by rfl) ⟨1618052, by rfl⟩ : syracuseStep 2157403 = 3236105) B3236105
theorem B10921877 : Blo 2155435 10921877 := bbase (se 6 (by rfl) ⟨255981, by rfl⟩ : syracuseStep 10921877 = 511963) (by norm_num)
theorem B7281251 : Blo 2155435 7281251 := bstep (se 1 (by rfl) ⟨5460938, by rfl⟩ : syracuseStep 7281251 = 10921877) B10921877
theorem B4854167 : Blo 2155435 4854167 := bstep (se 1 (by rfl) ⟨3640625, by rfl⟩ : syracuseStep 4854167 = 7281251) B7281251
theorem B3236111 : Blo 2155435 3236111 := bstep (se 1 (by rfl) ⟨2427083, by rfl⟩ : syracuseStep 3236111 = 4854167) B4854167
theorem B2157407 : Blo 2155435 2157407 := bstep (se 1 (by rfl) ⟨1618055, by rfl⟩ : syracuseStep 2157407 = 3236111) B3236111
theorem B3236117 : Blo 2155435 3236117 := bbase (se 6 (by rfl) ⟨75846, by rfl⟩ : syracuseStep 3236117 = 151693) (by norm_num)
theorem B2157411 : Blo 2155435 2157411 := bstep (se 1 (by rfl) ⟨1618058, by rfl⟩ : syracuseStep 2157411 = 3236117) B3236117
theorem B17494805 : Blo 2155435 17494805 := bbase (se 6 (by rfl) ⟨410034, by rfl⟩ : syracuseStep 17494805 = 820069) (by norm_num)
theorem B11663203 : Blo 2155435 11663203 := bstep (se 1 (by rfl) ⟨8747402, by rfl⟩ : syracuseStep 11663203 = 17494805) B17494805
theorem B15550937 : Blo 2155435 15550937 := bstep (se 2 (by rfl) ⟨5831601, by rfl⟩ : syracuseStep 15550937 = 11663203) B11663203
theorem B10367291 : Blo 2155435 10367291 := bstep (se 1 (by rfl) ⟨7775468, by rfl⟩ : syracuseStep 10367291 = 15550937) B15550937
theorem B27646109 : Blo 2155435 27646109 := bstep (se 3 (by rfl) ⟨5183645, by rfl⟩ : syracuseStep 27646109 = 10367291) B10367291
theorem B18430739 : Blo 2155435 18430739 := bstep (se 1 (by rfl) ⟨13823054, by rfl⟩ : syracuseStep 18430739 = 27646109) B27646109
theorem B12287159 : Blo 2155435 12287159 := bstep (se 1 (by rfl) ⟨9215369, by rfl⟩ : syracuseStep 12287159 = 18430739) B18430739
theorem B8191439 : Blo 2155435 8191439 := bstep (se 1 (by rfl) ⟨6143579, by rfl⟩ : syracuseStep 8191439 = 12287159) B12287159
theorem B5460959 : Blo 2155435 5460959 := bstep (se 1 (by rfl) ⟨4095719, by rfl⟩ : syracuseStep 5460959 = 8191439) B8191439
theorem B3640639 : Blo 2155435 3640639 := bstep (se 1 (by rfl) ⟨2730479, by rfl⟩ : syracuseStep 3640639 = 5460959) B5460959
theorem B4854185 : Blo 2155435 4854185 := bstep (se 2 (by rfl) ⟨1820319, by rfl⟩ : syracuseStep 4854185 = 3640639) B3640639
theorem B3236123 : Blo 2155435 3236123 := bstep (se 1 (by rfl) ⟨2427092, by rfl⟩ : syracuseStep 3236123 = 4854185) B4854185
theorem B2157415 : Blo 2155435 2157415 := bstep (se 1 (by rfl) ⟨1618061, by rfl⟩ : syracuseStep 2157415 = 3236123) B3236123
theorem B2427097 : Blo 2155435 2427097 := bbase (se 2 (by rfl) ⟨910161, by rfl⟩ : syracuseStep 2427097 = 1820323) (by norm_num)
theorem B3236129 : Blo 2155435 3236129 := bstep (se 2 (by rfl) ⟨1213548, by rfl⟩ : syracuseStep 3236129 = 2427097) B2427097
theorem B2157419 : Blo 2155435 2157419 := bstep (se 1 (by rfl) ⟨1618064, by rfl⟩ : syracuseStep 2157419 = 3236129) B3236129
theorem B2591833 : Blo 2155435 2591833 := bbase (se 2 (by rfl) ⟨971937, by rfl⟩ : syracuseStep 2591833 = 1943875) (by norm_num)
theorem B3455777 : Blo 2155435 3455777 := bstep (se 2 (by rfl) ⟨1295916, by rfl⟩ : syracuseStep 3455777 = 2591833) B2591833
theorem B2303851 : Blo 2155435 2303851 := bstep (se 1 (by rfl) ⟨1727888, by rfl⟩ : syracuseStep 2303851 = 3455777) B3455777
theorem B3071801 : Blo 2155435 3071801 := bstep (se 2 (by rfl) ⟨1151925, by rfl⟩ : syracuseStep 3071801 = 2303851) B2303851
theorem B8191469 : Blo 2155435 8191469 := bstep (se 3 (by rfl) ⟨1535900, by rfl⟩ : syracuseStep 8191469 = 3071801) B3071801
theorem B5460979 : Blo 2155435 5460979 := bstep (se 1 (by rfl) ⟨4095734, by rfl⟩ : syracuseStep 5460979 = 8191469) B8191469
theorem B7281305 : Blo 2155435 7281305 := bstep (se 2 (by rfl) ⟨2730489, by rfl⟩ : syracuseStep 7281305 = 5460979) B5460979
theorem B4854203 : Blo 2155435 4854203 := bstep (se 1 (by rfl) ⟨3640652, by rfl⟩ : syracuseStep 4854203 = 7281305) B7281305
theorem B3236135 : Blo 2155435 3236135 := bstep (se 1 (by rfl) ⟨2427101, by rfl⟩ : syracuseStep 3236135 = 4854203) B4854203
theorem B2157423 : Blo 2155435 2157423 := bstep (se 1 (by rfl) ⟨1618067, by rfl⟩ : syracuseStep 2157423 = 3236135) B3236135
theorem B3236141 : Blo 2155435 3236141 := bbase (se 3 (by rfl) ⟨606776, by rfl⟩ : syracuseStep 3236141 = 1213553) (by norm_num)
theorem B2157427 : Blo 2155435 2157427 := bstep (se 1 (by rfl) ⟨1618070, by rfl⟩ : syracuseStep 2157427 = 3236141) B3236141
theorem B4854221 : Blo 2155435 4854221 := bbase (se 3 (by rfl) ⟨910166, by rfl⟩ : syracuseStep 4854221 = 1820333) (by norm_num)
theorem B3236147 : Blo 2155435 3236147 := bstep (se 1 (by rfl) ⟨2427110, by rfl⟩ : syracuseStep 3236147 = 4854221) B4854221
theorem B2157431 : Blo 2155435 2157431 := bstep (se 1 (by rfl) ⟨1618073, by rfl⟩ : syracuseStep 2157431 = 3236147) B3236147
theorem B2730505 : Blo 2155435 2730505 := bbase (se 2 (by rfl) ⟨1023939, by rfl⟩ : syracuseStep 2730505 = 2047879) (by norm_num)
theorem B3640673 : Blo 2155435 3640673 := bstep (se 2 (by rfl) ⟨1365252, by rfl⟩ : syracuseStep 3640673 = 2730505) B2730505
theorem B2427115 : Blo 2155435 2427115 := bstep (se 1 (by rfl) ⟨1820336, by rfl⟩ : syracuseStep 2427115 = 3640673) B3640673
theorem B3236153 : Blo 2155435 3236153 := bstep (se 2 (by rfl) ⟨1213557, by rfl⟩ : syracuseStep 3236153 = 2427115) B2427115
theorem B2157435 : Blo 2155435 2157435 := bstep (se 1 (by rfl) ⟨1618076, by rfl⟩ : syracuseStep 2157435 = 3236153) B3236153
theorem C0 (j : ℕ) (h1 : 538858 ≤ j) (h2 : j ≤ 539358) : Blo 2155435 (4 * j + 3) := by
  interval_cases j
  · exact B2155435
  · exact B2155439
  · exact B2155443
  · exact B2155447
  · exact B2155451
  · exact B2155455
  · exact B2155459
  · exact B2155463
  · exact B2155467
  · exact B2155471
  · exact B2155475
  · exact B2155479
  · exact B2155483
  · exact B2155487
  · exact B2155491
  · exact B2155495
  · exact B2155499
  · exact B2155503
  · exact B2155507
  · exact B2155511
  · exact B2155515
  · exact B2155519
  · exact B2155523
  · exact B2155527
  · exact B2155531
  · exact B2155535
  · exact B2155539
  · exact B2155543
  · exact B2155547
  · exact B2155551
  · exact B2155555
  · exact B2155559
  · exact B2155563
  · exact B2155567
  · exact B2155571
  · exact B2155575
  · exact B2155579
  · exact B2155583
  · exact B2155587
  · exact B2155591
  · exact B2155595
  · exact B2155599
  · exact B2155603
  · exact B2155607
  · exact B2155611
  · exact B2155615
  · exact B2155619
  · exact B2155623
  · exact B2155627
  · exact B2155631
  · exact B2155635
  · exact B2155639
  · exact B2155643
  · exact B2155647
  · exact B2155651
  · exact B2155655
  · exact B2155659
  · exact B2155663
  · exact B2155667
  · exact B2155671
  · exact B2155675
  · exact B2155679
  · exact B2155683
  · exact B2155687
  · exact B2155691
  · exact B2155695
  · exact B2155699
  · exact B2155703
  · exact B2155707
  · exact B2155711
  · exact B2155715
  · exact B2155719
  · exact B2155723
  · exact B2155727
  · exact B2155731
  · exact B2155735
  · exact B2155739
  · exact B2155743
  · exact B2155747
  · exact B2155751
  · exact B2155755
  · exact B2155759
  · exact B2155763
  · exact B2155767
  · exact B2155771
  · exact B2155775
  · exact B2155779
  · exact B2155783
  · exact B2155787
  · exact B2155791
  · exact B2155795
  · exact B2155799
  · exact B2155803
  · exact B2155807
  · exact B2155811
  · exact B2155815
  · exact B2155819
  · exact B2155823
  · exact B2155827
  · exact B2155831
  · exact B2155835
  · exact B2155839
  · exact B2155843
  · exact B2155847
  · exact B2155851
  · exact B2155855
  · exact B2155859
  · exact B2155863
  · exact B2155867
  · exact B2155871
  · exact B2155875
  · exact B2155879
  · exact B2155883
  · exact B2155887
  · exact B2155891
  · exact B2155895
  · exact B2155899
  · exact B2155903
  · exact B2155907
  · exact B2155911
  · exact B2155915
  · exact B2155919
  · exact B2155923
  · exact B2155927
  · exact B2155931
  · exact B2155935
  · exact B2155939
  · exact B2155943
  · exact B2155947
  · exact B2155951
  · exact B2155955
  · exact B2155959
  · exact B2155963
  · exact B2155967
  · exact B2155971
  · exact B2155975
  · exact B2155979
  · exact B2155983
  · exact B2155987
  · exact B2155991
  · exact B2155995
  · exact B2155999
  · exact B2156003
  · exact B2156007
  · exact B2156011
  · exact B2156015
  · exact B2156019
  · exact B2156023
  · exact B2156027
  · exact B2156031
  · exact B2156035
  · exact B2156039
  · exact B2156043
  · exact B2156047
  · exact B2156051
  · exact B2156055
  · exact B2156059
  · exact B2156063
  · exact B2156067
  · exact B2156071
  · exact B2156075
  · exact B2156079
  · exact B2156083
  · exact B2156087
  · exact B2156091
  · exact B2156095
  · exact B2156099
  · exact B2156103
  · exact B2156107
  · exact B2156111
  · exact B2156115
  · exact B2156119
  · exact B2156123
  · exact B2156127
  · exact B2156131
  · exact B2156135
  · exact B2156139
  · exact B2156143
  · exact B2156147
  · exact B2156151
  · exact B2156155
  · exact B2156159
  · exact B2156163
  · exact B2156167
  · exact B2156171
  · exact B2156175
  · exact B2156179
  · exact B2156183
  · exact B2156187
  · exact B2156191
  · exact B2156195
  · exact B2156199
  · exact B2156203
  · exact B2156207
  · exact B2156211
  · exact B2156215
  · exact B2156219
  · exact B2156223
  · exact B2156227
  · exact B2156231
  · exact B2156235
  · exact B2156239
  · exact B2156243
  · exact B2156247
  · exact B2156251
  · exact B2156255
  · exact B2156259
  · exact B2156263
  · exact B2156267
  · exact B2156271
  · exact B2156275
  · exact B2156279
  · exact B2156283
  · exact B2156287
  · exact B2156291
  · exact B2156295
  · exact B2156299
  · exact B2156303
  · exact B2156307
  · exact B2156311
  · exact B2156315
  · exact B2156319
  · exact B2156323
  · exact B2156327
  · exact B2156331
  · exact B2156335
  · exact B2156339
  · exact B2156343
  · exact B2156347
  · exact B2156351
  · exact B2156355
  · exact B2156359
  · exact B2156363
  · exact B2156367
  · exact B2156371
  · exact B2156375
  · exact B2156379
  · exact B2156383
  · exact B2156387
  · exact B2156391
  · exact B2156395
  · exact B2156399
  · exact B2156403
  · exact B2156407
  · exact B2156411
  · exact B2156415
  · exact B2156419
  · exact B2156423
  · exact B2156427
  · exact B2156431
  · exact B2156435
  · exact B2156439
  · exact B2156443
  · exact B2156447
  · exact B2156451
  · exact B2156455
  · exact B2156459
  · exact B2156463
  · exact B2156467
  · exact B2156471
  · exact B2156475
  · exact B2156479
  · exact B2156483
  · exact B2156487
  · exact B2156491
  · exact B2156495
  · exact B2156499
  · exact B2156503
  · exact B2156507
  · exact B2156511
  · exact B2156515
  · exact B2156519
  · exact B2156523
  · exact B2156527
  · exact B2156531
  · exact B2156535
  · exact B2156539
  · exact B2156543
  · exact B2156547
  · exact B2156551
  · exact B2156555
  · exact B2156559
  · exact B2156563
  · exact B2156567
  · exact B2156571
  · exact B2156575
  · exact B2156579
  · exact B2156583
  · exact B2156587
  · exact B2156591
  · exact B2156595
  · exact B2156599
  · exact B2156603
  · exact B2156607
  · exact B2156611
  · exact B2156615
  · exact B2156619
  · exact B2156623
  · exact B2156627
  · exact B2156631
  · exact B2156635
  · exact B2156639
  · exact B2156643
  · exact B2156647
  · exact B2156651
  · exact B2156655
  · exact B2156659
  · exact B2156663
  · exact B2156667
  · exact B2156671
  · exact B2156675
  · exact B2156679
  · exact B2156683
  · exact B2156687
  · exact B2156691
  · exact B2156695
  · exact B2156699
  · exact B2156703
  · exact B2156707
  · exact B2156711
  · exact B2156715
  · exact B2156719
  · exact B2156723
  · exact B2156727
  · exact B2156731
  · exact B2156735
  · exact B2156739
  · exact B2156743
  · exact B2156747
  · exact B2156751
  · exact B2156755
  · exact B2156759
  · exact B2156763
  · exact B2156767
  · exact B2156771
  · exact B2156775
  · exact B2156779
  · exact B2156783
  · exact B2156787
  · exact B2156791
  · exact B2156795
  · exact B2156799
  · exact B2156803
  · exact B2156807
  · exact B2156811
  · exact B2156815
  · exact B2156819
  · exact B2156823
  · exact B2156827
  · exact B2156831
  · exact B2156835
  · exact B2156839
  · exact B2156843
  · exact B2156847
  · exact B2156851
  · exact B2156855
  · exact B2156859
  · exact B2156863
  · exact B2156867
  · exact B2156871
  · exact B2156875
  · exact B2156879
  · exact B2156883
  · exact B2156887
  · exact B2156891
  · exact B2156895
  · exact B2156899
  · exact B2156903
  · exact B2156907
  · exact B2156911
  · exact B2156915
  · exact B2156919
  · exact B2156923
  · exact B2156927
  · exact B2156931
  · exact B2156935
  · exact B2156939
  · exact B2156943
  · exact B2156947
  · exact B2156951
  · exact B2156955
  · exact B2156959
  · exact B2156963
  · exact B2156967
  · exact B2156971
  · exact B2156975
  · exact B2156979
  · exact B2156983
  · exact B2156987
  · exact B2156991
  · exact B2156995
  · exact B2156999
  · exact B2157003
  · exact B2157007
  · exact B2157011
  · exact B2157015
  · exact B2157019
  · exact B2157023
  · exact B2157027
  · exact B2157031
  · exact B2157035
  · exact B2157039
  · exact B2157043
  · exact B2157047
  · exact B2157051
  · exact B2157055
  · exact B2157059
  · exact B2157063
  · exact B2157067
  · exact B2157071
  · exact B2157075
  · exact B2157079
  · exact B2157083
  · exact B2157087
  · exact B2157091
  · exact B2157095
  · exact B2157099
  · exact B2157103
  · exact B2157107
  · exact B2157111
  · exact B2157115
  · exact B2157119
  · exact B2157123
  · exact B2157127
  · exact B2157131
  · exact B2157135
  · exact B2157139
  · exact B2157143
  · exact B2157147
  · exact B2157151
  · exact B2157155
  · exact B2157159
  · exact B2157163
  · exact B2157167
  · exact B2157171
  · exact B2157175
  · exact B2157179
  · exact B2157183
  · exact B2157187
  · exact B2157191
  · exact B2157195
  · exact B2157199
  · exact B2157203
  · exact B2157207
  · exact B2157211
  · exact B2157215
  · exact B2157219
  · exact B2157223
  · exact B2157227
  · exact B2157231
  · exact B2157235
  · exact B2157239
  · exact B2157243
  · exact B2157247
  · exact B2157251
  · exact B2157255
  · exact B2157259
  · exact B2157263
  · exact B2157267
  · exact B2157271
  · exact B2157275
  · exact B2157279
  · exact B2157283
  · exact B2157287
  · exact B2157291
  · exact B2157295
  · exact B2157299
  · exact B2157303
  · exact B2157307
  · exact B2157311
  · exact B2157315
  · exact B2157319
  · exact B2157323
  · exact B2157327
  · exact B2157331
  · exact B2157335
  · exact B2157339
  · exact B2157343
  · exact B2157347
  · exact B2157351
  · exact B2157355
  · exact B2157359
  · exact B2157363
  · exact B2157367
  · exact B2157371
  · exact B2157375
  · exact B2157379
  · exact B2157383
  · exact B2157387
  · exact B2157391
  · exact B2157395
  · exact B2157399
  · exact B2157403
  · exact B2157407
  · exact B2157411
  · exact B2157415
  · exact B2157419
  · exact B2157423
  · exact B2157427
  · exact B2157431
  · exact B2157435
theorem solution (m : ℕ) (hlo : 2155435 ≤ m) (hhi : m ≤ 2157435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 538858 ≤ j := by omega
    have hj2 : j ≤ 539358 := by omega
    have hb : Blo 2155435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
