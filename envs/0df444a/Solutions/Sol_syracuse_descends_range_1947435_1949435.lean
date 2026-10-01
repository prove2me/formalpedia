-- Prove2me | solution 1 for syracuse_descends_range_1947435_1949435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:38.136365+00:00
-- url     : https://prove2.me/submissions/91a9182e-7c8b-4eed-9e3d-ab2553caadf9

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

theorem B2190865 : Blo 1947435 2190865 := bbase (se 2 (by rfl) ⟨821574, by rfl⟩ : syracuseStep 2190865 = 1643149) (by norm_num)
theorem B2921153 : Blo 1947435 2921153 := bstep (se 2 (by rfl) ⟨1095432, by rfl⟩ : syracuseStep 2921153 = 2190865) B2190865
theorem B1947435 : Blo 1947435 1947435 := bstep (se 1 (by rfl) ⟨1460576, by rfl⟩ : syracuseStep 1947435 = 2921153) B2921153
theorem B3697093 : Blo 1947435 3697093 := bbase (se 4 (by rfl) ⟨346602, by rfl⟩ : syracuseStep 3697093 = 693205) (by norm_num)
theorem B4929457 : Blo 1947435 4929457 := bstep (se 2 (by rfl) ⟨1848546, by rfl⟩ : syracuseStep 4929457 = 3697093) B3697093
theorem B6572609 : Blo 1947435 6572609 := bstep (se 2 (by rfl) ⟨2464728, by rfl⟩ : syracuseStep 6572609 = 4929457) B4929457
theorem B4381739 : Blo 1947435 4381739 := bstep (se 1 (by rfl) ⟨3286304, by rfl⟩ : syracuseStep 4381739 = 6572609) B6572609
theorem B2921159 : Blo 1947435 2921159 := bstep (se 1 (by rfl) ⟨2190869, by rfl⟩ : syracuseStep 2921159 = 4381739) B4381739
theorem B1947439 : Blo 1947435 1947439 := bstep (se 1 (by rfl) ⟨1460579, by rfl⟩ : syracuseStep 1947439 = 2921159) B2921159
theorem B2921165 : Blo 1947435 2921165 := bbase (se 3 (by rfl) ⟨547718, by rfl⟩ : syracuseStep 2921165 = 1095437) (by norm_num)
theorem B1947443 : Blo 1947435 1947443 := bstep (se 1 (by rfl) ⟨1460582, by rfl⟩ : syracuseStep 1947443 = 2921165) B2921165
theorem B4381757 : Blo 1947435 4381757 := bbase (se 3 (by rfl) ⟨821579, by rfl⟩ : syracuseStep 4381757 = 1643159) (by norm_num)
theorem B2921171 : Blo 1947435 2921171 := bstep (se 1 (by rfl) ⟨2190878, by rfl⟩ : syracuseStep 2921171 = 4381757) B4381757
theorem B1947447 : Blo 1947435 1947447 := bstep (se 1 (by rfl) ⟨1460585, by rfl⟩ : syracuseStep 1947447 = 2921171) B2921171
theorem B3286325 : Blo 1947435 3286325 := bbase (se 5 (by rfl) ⟨154046, by rfl⟩ : syracuseStep 3286325 = 308093) (by norm_num)
theorem B2190883 : Blo 1947435 2190883 := bstep (se 1 (by rfl) ⟨1643162, by rfl⟩ : syracuseStep 2190883 = 3286325) B3286325
theorem B2921177 : Blo 1947435 2921177 := bstep (se 2 (by rfl) ⟨1095441, by rfl⟩ : syracuseStep 2921177 = 2190883) B2190883
theorem B1947451 : Blo 1947435 1947451 := bstep (se 1 (by rfl) ⟨1460588, by rfl⟩ : syracuseStep 1947451 = 2921177) B2921177
theorem B5545685 : Blo 1947435 5545685 := bbase (se 7 (by rfl) ⟨64988, by rfl⟩ : syracuseStep 5545685 = 129977) (by norm_num)
theorem B14788493 : Blo 1947435 14788493 := bstep (se 3 (by rfl) ⟨2772842, by rfl⟩ : syracuseStep 14788493 = 5545685) B5545685
theorem B9858995 : Blo 1947435 9858995 := bstep (se 1 (by rfl) ⟨7394246, by rfl⟩ : syracuseStep 9858995 = 14788493) B14788493
theorem B6572663 : Blo 1947435 6572663 := bstep (se 1 (by rfl) ⟨4929497, by rfl⟩ : syracuseStep 6572663 = 9858995) B9858995
theorem B4381775 : Blo 1947435 4381775 := bstep (se 1 (by rfl) ⟨3286331, by rfl⟩ : syracuseStep 4381775 = 6572663) B6572663
theorem B2921183 : Blo 1947435 2921183 := bstep (se 1 (by rfl) ⟨2190887, by rfl⟩ : syracuseStep 2921183 = 4381775) B4381775
theorem B1947455 : Blo 1947435 1947455 := bstep (se 1 (by rfl) ⟨1460591, by rfl⟩ : syracuseStep 1947455 = 2921183) B2921183
theorem B2921189 : Blo 1947435 2921189 := bbase (se 4 (by rfl) ⟨273861, by rfl⟩ : syracuseStep 2921189 = 547723) (by norm_num)
theorem B1947459 : Blo 1947435 1947459 := bstep (se 1 (by rfl) ⟨1460594, by rfl⟩ : syracuseStep 1947459 = 2921189) B2921189
theorem B2079641 : Blo 1947435 2079641 := bbase (se 2 (by rfl) ⟨779865, by rfl⟩ : syracuseStep 2079641 = 1559731) (by norm_num)
theorem B5545709 : Blo 1947435 5545709 := bstep (se 3 (by rfl) ⟨1039820, by rfl⟩ : syracuseStep 5545709 = 2079641) B2079641
theorem B3697139 : Blo 1947435 3697139 := bstep (se 1 (by rfl) ⟨2772854, by rfl⟩ : syracuseStep 3697139 = 5545709) B5545709
theorem B2464759 : Blo 1947435 2464759 := bstep (se 1 (by rfl) ⟨1848569, by rfl⟩ : syracuseStep 2464759 = 3697139) B3697139
theorem B3286345 : Blo 1947435 3286345 := bstep (se 2 (by rfl) ⟨1232379, by rfl⟩ : syracuseStep 3286345 = 2464759) B2464759
theorem B4381793 : Blo 1947435 4381793 := bstep (se 2 (by rfl) ⟨1643172, by rfl⟩ : syracuseStep 4381793 = 3286345) B3286345
theorem B2921195 : Blo 1947435 2921195 := bstep (se 1 (by rfl) ⟨2190896, by rfl⟩ : syracuseStep 2921195 = 4381793) B4381793
theorem B1947463 : Blo 1947435 1947463 := bstep (se 1 (by rfl) ⟨1460597, by rfl⟩ : syracuseStep 1947463 = 2921195) B2921195
theorem B2190901 : Blo 1947435 2190901 := bbase (se 5 (by rfl) ⟨102698, by rfl⟩ : syracuseStep 2190901 = 205397) (by norm_num)
theorem B2921201 : Blo 1947435 2921201 := bstep (se 2 (by rfl) ⟨1095450, by rfl⟩ : syracuseStep 2921201 = 2190901) B2190901
theorem B1947467 : Blo 1947435 1947467 := bstep (se 1 (by rfl) ⟨1460600, by rfl⟩ : syracuseStep 1947467 = 2921201) B2921201
theorem B2464769 : Blo 1947435 2464769 := bbase (se 2 (by rfl) ⟨924288, by rfl⟩ : syracuseStep 2464769 = 1848577) (by norm_num)
theorem B6572717 : Blo 1947435 6572717 := bstep (se 3 (by rfl) ⟨1232384, by rfl⟩ : syracuseStep 6572717 = 2464769) B2464769
theorem B4381811 : Blo 1947435 4381811 := bstep (se 1 (by rfl) ⟨3286358, by rfl⟩ : syracuseStep 4381811 = 6572717) B6572717
theorem B2921207 : Blo 1947435 2921207 := bstep (se 1 (by rfl) ⟨2190905, by rfl⟩ : syracuseStep 2921207 = 4381811) B4381811
theorem B1947471 : Blo 1947435 1947471 := bstep (se 1 (by rfl) ⟨1460603, by rfl⟩ : syracuseStep 1947471 = 2921207) B2921207
theorem B2921213 : Blo 1947435 2921213 := bbase (se 3 (by rfl) ⟨547727, by rfl⟩ : syracuseStep 2921213 = 1095455) (by norm_num)
theorem B1947475 : Blo 1947435 1947475 := bstep (se 1 (by rfl) ⟨1460606, by rfl⟩ : syracuseStep 1947475 = 2921213) B2921213
theorem B4381829 : Blo 1947435 4381829 := bbase (se 4 (by rfl) ⟨410796, by rfl⟩ : syracuseStep 4381829 = 821593) (by norm_num)
theorem B2921219 : Blo 1947435 2921219 := bstep (se 1 (by rfl) ⟨2190914, by rfl⟩ : syracuseStep 2921219 = 4381829) B4381829
theorem B1947479 : Blo 1947435 1947479 := bstep (se 1 (by rfl) ⟨1460609, by rfl⟩ : syracuseStep 1947479 = 2921219) B2921219
theorem B4159325 : Blo 1947435 4159325 := bbase (se 3 (by rfl) ⟨779873, by rfl⟩ : syracuseStep 4159325 = 1559747) (by norm_num)
theorem B2772883 : Blo 1947435 2772883 := bstep (se 1 (by rfl) ⟨2079662, by rfl⟩ : syracuseStep 2772883 = 4159325) B4159325
theorem B3697177 : Blo 1947435 3697177 := bstep (se 2 (by rfl) ⟨1386441, by rfl⟩ : syracuseStep 3697177 = 2772883) B2772883
theorem B4929569 : Blo 1947435 4929569 := bstep (se 2 (by rfl) ⟨1848588, by rfl⟩ : syracuseStep 4929569 = 3697177) B3697177
theorem B3286379 : Blo 1947435 3286379 := bstep (se 1 (by rfl) ⟨2464784, by rfl⟩ : syracuseStep 3286379 = 4929569) B4929569
theorem B2190919 : Blo 1947435 2190919 := bstep (se 1 (by rfl) ⟨1643189, by rfl⟩ : syracuseStep 2190919 = 3286379) B3286379
theorem B2921225 : Blo 1947435 2921225 := bstep (se 2 (by rfl) ⟨1095459, by rfl⟩ : syracuseStep 2921225 = 2190919) B2190919
theorem B1947483 : Blo 1947435 1947483 := bstep (se 1 (by rfl) ⟨1460612, by rfl⟩ : syracuseStep 1947483 = 2921225) B2921225
theorem B9859157 : Blo 1947435 9859157 := bbase (se 8 (by rfl) ⟨57768, by rfl⟩ : syracuseStep 9859157 = 115537) (by norm_num)
theorem B6572771 : Blo 1947435 6572771 := bstep (se 1 (by rfl) ⟨4929578, by rfl⟩ : syracuseStep 6572771 = 9859157) B9859157
theorem B4381847 : Blo 1947435 4381847 := bstep (se 1 (by rfl) ⟨3286385, by rfl⟩ : syracuseStep 4381847 = 6572771) B6572771
theorem B2921231 : Blo 1947435 2921231 := bstep (se 1 (by rfl) ⟨2190923, by rfl⟩ : syracuseStep 2921231 = 4381847) B4381847
theorem B1947487 : Blo 1947435 1947487 := bstep (se 1 (by rfl) ⟨1460615, by rfl⟩ : syracuseStep 1947487 = 2921231) B2921231
theorem B2921237 : Blo 1947435 2921237 := bbase (se 6 (by rfl) ⟨68466, by rfl⟩ : syracuseStep 2921237 = 136933) (by norm_num)
theorem B1947491 : Blo 1947435 1947491 := bstep (se 1 (by rfl) ⟨1460618, by rfl⟩ : syracuseStep 1947491 = 2921237) B2921237
theorem B15792533 : Blo 1947435 15792533 := bbase (se 6 (by rfl) ⟨370137, by rfl⟩ : syracuseStep 15792533 = 740275) (by norm_num)
theorem B10528355 : Blo 1947435 10528355 := bstep (se 1 (by rfl) ⟨7896266, by rfl⟩ : syracuseStep 10528355 = 15792533) B15792533
theorem B7018903 : Blo 1947435 7018903 := bstep (se 1 (by rfl) ⟨5264177, by rfl⟩ : syracuseStep 7018903 = 10528355) B10528355
theorem B37434149 : Blo 1947435 37434149 := bstep (se 4 (by rfl) ⟨3509451, by rfl⟩ : syracuseStep 37434149 = 7018903) B7018903
theorem B24956099 : Blo 1947435 24956099 := bstep (se 1 (by rfl) ⟨18717074, by rfl⟩ : syracuseStep 24956099 = 37434149) B37434149
theorem B16637399 : Blo 1947435 16637399 := bstep (se 1 (by rfl) ⟨12478049, by rfl⟩ : syracuseStep 16637399 = 24956099) B24956099
theorem B11091599 : Blo 1947435 11091599 := bstep (se 1 (by rfl) ⟨8318699, by rfl⟩ : syracuseStep 11091599 = 16637399) B16637399
theorem B7394399 : Blo 1947435 7394399 := bstep (se 1 (by rfl) ⟨5545799, by rfl⟩ : syracuseStep 7394399 = 11091599) B11091599
theorem B4929599 : Blo 1947435 4929599 := bstep (se 1 (by rfl) ⟨3697199, by rfl⟩ : syracuseStep 4929599 = 7394399) B7394399
theorem B3286399 : Blo 1947435 3286399 := bstep (se 1 (by rfl) ⟨2464799, by rfl⟩ : syracuseStep 3286399 = 4929599) B4929599
theorem B4381865 : Blo 1947435 4381865 := bstep (se 2 (by rfl) ⟨1643199, by rfl⟩ : syracuseStep 4381865 = 3286399) B3286399
theorem B2921243 : Blo 1947435 2921243 := bstep (se 1 (by rfl) ⟨2190932, by rfl⟩ : syracuseStep 2921243 = 4381865) B4381865
theorem B1947495 : Blo 1947435 1947495 := bstep (se 1 (by rfl) ⟨1460621, by rfl⟩ : syracuseStep 1947495 = 2921243) B2921243
theorem B2190937 : Blo 1947435 2190937 := bbase (se 2 (by rfl) ⟨821601, by rfl⟩ : syracuseStep 2190937 = 1643203) (by norm_num)
theorem B2921249 : Blo 1947435 2921249 := bstep (se 2 (by rfl) ⟨1095468, by rfl⟩ : syracuseStep 2921249 = 2190937) B2190937
theorem B1947499 : Blo 1947435 1947499 := bstep (se 1 (by rfl) ⟨1460624, by rfl⟩ : syracuseStep 1947499 = 2921249) B2921249
theorem B7018933 : Blo 1947435 7018933 := bbase (se 5 (by rfl) ⟨329012, by rfl⟩ : syracuseStep 7018933 = 658025) (by norm_num)
theorem B9358577 : Blo 1947435 9358577 := bstep (se 2 (by rfl) ⟨3509466, by rfl⟩ : syracuseStep 9358577 = 7018933) B7018933
theorem B6239051 : Blo 1947435 6239051 := bstep (se 1 (by rfl) ⟨4679288, by rfl⟩ : syracuseStep 6239051 = 9358577) B9358577
theorem B4159367 : Blo 1947435 4159367 := bstep (se 1 (by rfl) ⟨3119525, by rfl⟩ : syracuseStep 4159367 = 6239051) B6239051
theorem B2772911 : Blo 1947435 2772911 := bstep (se 1 (by rfl) ⟨2079683, by rfl⟩ : syracuseStep 2772911 = 4159367) B4159367
theorem B7394429 : Blo 1947435 7394429 := bstep (se 3 (by rfl) ⟨1386455, by rfl⟩ : syracuseStep 7394429 = 2772911) B2772911
theorem B4929619 : Blo 1947435 4929619 := bstep (se 1 (by rfl) ⟨3697214, by rfl⟩ : syracuseStep 4929619 = 7394429) B7394429
theorem B6572825 : Blo 1947435 6572825 := bstep (se 2 (by rfl) ⟨2464809, by rfl⟩ : syracuseStep 6572825 = 4929619) B4929619
theorem B4381883 : Blo 1947435 4381883 := bstep (se 1 (by rfl) ⟨3286412, by rfl⟩ : syracuseStep 4381883 = 6572825) B6572825
theorem B2921255 : Blo 1947435 2921255 := bstep (se 1 (by rfl) ⟨2190941, by rfl⟩ : syracuseStep 2921255 = 4381883) B4381883
theorem B1947503 : Blo 1947435 1947503 := bstep (se 1 (by rfl) ⟨1460627, by rfl⟩ : syracuseStep 1947503 = 2921255) B2921255
theorem B2921261 : Blo 1947435 2921261 := bbase (se 3 (by rfl) ⟨547736, by rfl⟩ : syracuseStep 2921261 = 1095473) (by norm_num)
theorem B1947507 : Blo 1947435 1947507 := bstep (se 1 (by rfl) ⟨1460630, by rfl⟩ : syracuseStep 1947507 = 2921261) B2921261
theorem B4381901 : Blo 1947435 4381901 := bbase (se 3 (by rfl) ⟨821606, by rfl⟩ : syracuseStep 4381901 = 1643213) (by norm_num)
theorem B2921267 : Blo 1947435 2921267 := bstep (se 1 (by rfl) ⟨2190950, by rfl⟩ : syracuseStep 2921267 = 4381901) B4381901
theorem B1947511 : Blo 1947435 1947511 := bstep (se 1 (by rfl) ⟨1460633, by rfl⟩ : syracuseStep 1947511 = 2921267) B2921267
theorem B2464825 : Blo 1947435 2464825 := bbase (se 2 (by rfl) ⟨924309, by rfl⟩ : syracuseStep 2464825 = 1848619) (by norm_num)
theorem B3286433 : Blo 1947435 3286433 := bstep (se 2 (by rfl) ⟨1232412, by rfl⟩ : syracuseStep 3286433 = 2464825) B2464825
theorem B2190955 : Blo 1947435 2190955 := bstep (se 1 (by rfl) ⟨1643216, by rfl⟩ : syracuseStep 2190955 = 3286433) B3286433
theorem B2921273 : Blo 1947435 2921273 := bstep (se 2 (by rfl) ⟨1095477, by rfl⟩ : syracuseStep 2921273 = 2190955) B2190955
theorem B1947515 : Blo 1947435 1947515 := bstep (se 1 (by rfl) ⟨1460636, by rfl⟩ : syracuseStep 1947515 = 2921273) B2921273
theorem B2220853 : Blo 1947435 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B2961137 : Blo 1947435 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B7896365 : Blo 1947435 7896365 := bstep (se 3 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 7896365 = 2961137) B2961137
theorem B5264243 : Blo 1947435 5264243 := bstep (se 1 (by rfl) ⟨3948182, by rfl⟩ : syracuseStep 5264243 = 7896365) B7896365
theorem B3509495 : Blo 1947435 3509495 := bstep (se 1 (by rfl) ⟨2632121, by rfl⟩ : syracuseStep 3509495 = 5264243) B5264243
theorem B2339663 : Blo 1947435 2339663 := bstep (se 1 (by rfl) ⟨1754747, by rfl⟩ : syracuseStep 2339663 = 3509495) B3509495
theorem B6239101 : Blo 1947435 6239101 := bstep (se 3 (by rfl) ⟨1169831, by rfl⟩ : syracuseStep 6239101 = 2339663) B2339663
theorem B8318801 : Blo 1947435 8318801 := bstep (se 2 (by rfl) ⟨3119550, by rfl⟩ : syracuseStep 8318801 = 6239101) B6239101
theorem B22183469 : Blo 1947435 22183469 := bstep (se 3 (by rfl) ⟨4159400, by rfl⟩ : syracuseStep 22183469 = 8318801) B8318801
theorem B14788979 : Blo 1947435 14788979 := bstep (se 1 (by rfl) ⟨11091734, by rfl⟩ : syracuseStep 14788979 = 22183469) B22183469
theorem B9859319 : Blo 1947435 9859319 := bstep (se 1 (by rfl) ⟨7394489, by rfl⟩ : syracuseStep 9859319 = 14788979) B14788979
theorem B6572879 : Blo 1947435 6572879 := bstep (se 1 (by rfl) ⟨4929659, by rfl⟩ : syracuseStep 6572879 = 9859319) B9859319
theorem B4381919 : Blo 1947435 4381919 := bstep (se 1 (by rfl) ⟨3286439, by rfl⟩ : syracuseStep 4381919 = 6572879) B6572879
theorem B2921279 : Blo 1947435 2921279 := bstep (se 1 (by rfl) ⟨2190959, by rfl⟩ : syracuseStep 2921279 = 4381919) B4381919
theorem B1947519 : Blo 1947435 1947519 := bstep (se 1 (by rfl) ⟨1460639, by rfl⟩ : syracuseStep 1947519 = 2921279) B2921279
theorem B2921285 : Blo 1947435 2921285 := bbase (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) (by norm_num)
theorem B1947523 : Blo 1947435 1947523 := bstep (se 1 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 1947523 = 2921285) B2921285
theorem B3286453 : Blo 1947435 3286453 := bbase (se 5 (by rfl) ⟨154052, by rfl⟩ : syracuseStep 3286453 = 308105) (by norm_num)
theorem B4381937 : Blo 1947435 4381937 := bstep (se 2 (by rfl) ⟨1643226, by rfl⟩ : syracuseStep 4381937 = 3286453) B3286453
theorem B2921291 : Blo 1947435 2921291 := bstep (se 1 (by rfl) ⟨2190968, by rfl⟩ : syracuseStep 2921291 = 4381937) B4381937
theorem B1947527 : Blo 1947435 1947527 := bstep (se 1 (by rfl) ⟨1460645, by rfl⟩ : syracuseStep 1947527 = 2921291) B2921291
theorem B2190973 : Blo 1947435 2190973 := bbase (se 3 (by rfl) ⟨410807, by rfl⟩ : syracuseStep 2190973 = 821615) (by norm_num)
theorem B2921297 : Blo 1947435 2921297 := bstep (se 2 (by rfl) ⟨1095486, by rfl⟩ : syracuseStep 2921297 = 2190973) B2190973
theorem B1947531 : Blo 1947435 1947531 := bstep (se 1 (by rfl) ⟨1460648, by rfl⟩ : syracuseStep 1947531 = 2921297) B2921297
theorem B6572933 : Blo 1947435 6572933 := bbase (se 4 (by rfl) ⟨616212, by rfl⟩ : syracuseStep 6572933 = 1232425) (by norm_num)
theorem B4381955 : Blo 1947435 4381955 := bstep (se 1 (by rfl) ⟨3286466, by rfl⟩ : syracuseStep 4381955 = 6572933) B6572933
theorem B2921303 : Blo 1947435 2921303 := bstep (se 1 (by rfl) ⟨2190977, by rfl⟩ : syracuseStep 2921303 = 4381955) B4381955
theorem B1947535 : Blo 1947435 1947535 := bstep (se 1 (by rfl) ⟨1460651, by rfl⟩ : syracuseStep 1947535 = 2921303) B2921303
theorem B2921309 : Blo 1947435 2921309 := bbase (se 3 (by rfl) ⟨547745, by rfl⟩ : syracuseStep 2921309 = 1095491) (by norm_num)
theorem B1947539 : Blo 1947435 1947539 := bstep (se 1 (by rfl) ⟨1460654, by rfl⟩ : syracuseStep 1947539 = 2921309) B2921309
theorem B4381973 : Blo 1947435 4381973 := bbase (se 6 (by rfl) ⟨102702, by rfl⟩ : syracuseStep 4381973 = 205405) (by norm_num)
theorem B2921315 : Blo 1947435 2921315 := bstep (se 1 (by rfl) ⟨2190986, by rfl⟩ : syracuseStep 2921315 = 4381973) B4381973
theorem B1947543 : Blo 1947435 1947543 := bstep (se 1 (by rfl) ⟨1460657, by rfl⟩ : syracuseStep 1947543 = 2921315) B2921315
theorem B7394597 : Blo 1947435 7394597 := bbase (se 4 (by rfl) ⟨693243, by rfl⟩ : syracuseStep 7394597 = 1386487) (by norm_num)
theorem B4929731 : Blo 1947435 4929731 := bstep (se 1 (by rfl) ⟨3697298, by rfl⟩ : syracuseStep 4929731 = 7394597) B7394597
theorem B3286487 : Blo 1947435 3286487 := bstep (se 1 (by rfl) ⟨2464865, by rfl⟩ : syracuseStep 3286487 = 4929731) B4929731
theorem B2190991 : Blo 1947435 2190991 := bstep (se 1 (by rfl) ⟨1643243, by rfl⟩ : syracuseStep 2190991 = 3286487) B3286487
theorem B2921321 : Blo 1947435 2921321 := bstep (se 2 (by rfl) ⟨1095495, by rfl⟩ : syracuseStep 2921321 = 2190991) B2190991
theorem B1947547 : Blo 1947435 1947547 := bstep (se 1 (by rfl) ⟨1460660, by rfl⟩ : syracuseStep 1947547 = 2921321) B2921321
theorem B4159469 : Blo 1947435 4159469 := bbase (se 3 (by rfl) ⟨779900, by rfl⟩ : syracuseStep 4159469 = 1559801) (by norm_num)
theorem B11091917 : Blo 1947435 11091917 := bstep (se 3 (by rfl) ⟨2079734, by rfl⟩ : syracuseStep 11091917 = 4159469) B4159469
theorem B7394611 : Blo 1947435 7394611 := bstep (se 1 (by rfl) ⟨5545958, by rfl⟩ : syracuseStep 7394611 = 11091917) B11091917
theorem B9859481 : Blo 1947435 9859481 := bstep (se 2 (by rfl) ⟨3697305, by rfl⟩ : syracuseStep 9859481 = 7394611) B7394611
theorem B6572987 : Blo 1947435 6572987 := bstep (se 1 (by rfl) ⟨4929740, by rfl⟩ : syracuseStep 6572987 = 9859481) B9859481
theorem B4381991 : Blo 1947435 4381991 := bstep (se 1 (by rfl) ⟨3286493, by rfl⟩ : syracuseStep 4381991 = 6572987) B6572987
theorem B2921327 : Blo 1947435 2921327 := bstep (se 1 (by rfl) ⟨2190995, by rfl⟩ : syracuseStep 2921327 = 4381991) B4381991
theorem B1947551 : Blo 1947435 1947551 := bstep (se 1 (by rfl) ⟨1460663, by rfl⟩ : syracuseStep 1947551 = 2921327) B2921327
theorem B2921333 : Blo 1947435 2921333 := bbase (se 5 (by rfl) ⟨136937, by rfl⟩ : syracuseStep 2921333 = 273875) (by norm_num)
theorem B1947555 : Blo 1947435 1947555 := bstep (se 1 (by rfl) ⟨1460666, by rfl⟩ : syracuseStep 1947555 = 2921333) B2921333
theorem B4216237 : Blo 1947435 4216237 := bbase (se 3 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 4216237 = 1581089) (by norm_num)
theorem B89946389 : Blo 1947435 89946389 := bstep (se 6 (by rfl) ⟨2108118, by rfl⟩ : syracuseStep 89946389 = 4216237) B4216237
theorem B239857037 : Blo 1947435 239857037 := bstep (se 3 (by rfl) ⟨44973194, by rfl⟩ : syracuseStep 239857037 = 89946389) B89946389
theorem B159904691 : Blo 1947435 159904691 := bstep (se 1 (by rfl) ⟨119928518, by rfl⟩ : syracuseStep 159904691 = 239857037) B239857037
theorem B106603127 : Blo 1947435 106603127 := bstep (se 1 (by rfl) ⟨79952345, by rfl⟩ : syracuseStep 106603127 = 159904691) B159904691
theorem B71068751 : Blo 1947435 71068751 := bstep (se 1 (by rfl) ⟨53301563, by rfl⟩ : syracuseStep 71068751 = 106603127) B106603127
theorem B47379167 : Blo 1947435 47379167 := bstep (se 1 (by rfl) ⟨35534375, by rfl⟩ : syracuseStep 47379167 = 71068751) B71068751
theorem B31586111 : Blo 1947435 31586111 := bstep (se 1 (by rfl) ⟨23689583, by rfl⟩ : syracuseStep 31586111 = 47379167) B47379167
theorem B21057407 : Blo 1947435 21057407 := bstep (se 1 (by rfl) ⟨15793055, by rfl⟩ : syracuseStep 21057407 = 31586111) B31586111
theorem B14038271 : Blo 1947435 14038271 := bstep (se 1 (by rfl) ⟨10528703, by rfl⟩ : syracuseStep 14038271 = 21057407) B21057407
theorem B9358847 : Blo 1947435 9358847 := bstep (se 1 (by rfl) ⟨7019135, by rfl⟩ : syracuseStep 9358847 = 14038271) B14038271
theorem B6239231 : Blo 1947435 6239231 := bstep (se 1 (by rfl) ⟨4679423, by rfl⟩ : syracuseStep 6239231 = 9358847) B9358847
theorem B4159487 : Blo 1947435 4159487 := bstep (se 1 (by rfl) ⟨3119615, by rfl⟩ : syracuseStep 4159487 = 6239231) B6239231
theorem B2772991 : Blo 1947435 2772991 := bstep (se 1 (by rfl) ⟨2079743, by rfl⟩ : syracuseStep 2772991 = 4159487) B4159487
theorem B3697321 : Blo 1947435 3697321 := bstep (se 2 (by rfl) ⟨1386495, by rfl⟩ : syracuseStep 3697321 = 2772991) B2772991
theorem B4929761 : Blo 1947435 4929761 := bstep (se 2 (by rfl) ⟨1848660, by rfl⟩ : syracuseStep 4929761 = 3697321) B3697321
theorem B3286507 : Blo 1947435 3286507 := bstep (se 1 (by rfl) ⟨2464880, by rfl⟩ : syracuseStep 3286507 = 4929761) B4929761
theorem B4382009 : Blo 1947435 4382009 := bstep (se 2 (by rfl) ⟨1643253, by rfl⟩ : syracuseStep 4382009 = 3286507) B3286507
theorem B2921339 : Blo 1947435 2921339 := bstep (se 1 (by rfl) ⟨2191004, by rfl⟩ : syracuseStep 2921339 = 4382009) B4382009
theorem B1947559 : Blo 1947435 1947559 := bstep (se 1 (by rfl) ⟨1460669, by rfl⟩ : syracuseStep 1947559 = 2921339) B2921339
theorem B2191009 : Blo 1947435 2191009 := bbase (se 2 (by rfl) ⟨821628, by rfl⟩ : syracuseStep 2191009 = 1643257) (by norm_num)
theorem B2921345 : Blo 1947435 2921345 := bstep (se 2 (by rfl) ⟨1095504, by rfl⟩ : syracuseStep 2921345 = 2191009) B2191009
theorem B1947563 : Blo 1947435 1947563 := bstep (se 1 (by rfl) ⟨1460672, by rfl⟩ : syracuseStep 1947563 = 2921345) B2921345
theorem B4929781 : Blo 1947435 4929781 := bbase (se 5 (by rfl) ⟨231083, by rfl⟩ : syracuseStep 4929781 = 462167) (by norm_num)
theorem B6573041 : Blo 1947435 6573041 := bstep (se 2 (by rfl) ⟨2464890, by rfl⟩ : syracuseStep 6573041 = 4929781) B4929781
theorem B4382027 : Blo 1947435 4382027 := bstep (se 1 (by rfl) ⟨3286520, by rfl⟩ : syracuseStep 4382027 = 6573041) B6573041
theorem B2921351 : Blo 1947435 2921351 := bstep (se 1 (by rfl) ⟨2191013, by rfl⟩ : syracuseStep 2921351 = 4382027) B4382027
theorem B1947567 : Blo 1947435 1947567 := bstep (se 1 (by rfl) ⟨1460675, by rfl⟩ : syracuseStep 1947567 = 2921351) B2921351
theorem B2921357 : Blo 1947435 2921357 := bbase (se 3 (by rfl) ⟨547754, by rfl⟩ : syracuseStep 2921357 = 1095509) (by norm_num)
theorem B1947571 : Blo 1947435 1947571 := bstep (se 1 (by rfl) ⟨1460678, by rfl⟩ : syracuseStep 1947571 = 2921357) B2921357
theorem B4382045 : Blo 1947435 4382045 := bbase (se 3 (by rfl) ⟨821633, by rfl⟩ : syracuseStep 4382045 = 1643267) (by norm_num)
theorem B2921363 : Blo 1947435 2921363 := bstep (se 1 (by rfl) ⟨2191022, by rfl⟩ : syracuseStep 2921363 = 4382045) B4382045
theorem B1947575 : Blo 1947435 1947575 := bstep (se 1 (by rfl) ⟨1460681, by rfl⟩ : syracuseStep 1947575 = 2921363) B2921363
theorem B3286541 : Blo 1947435 3286541 := bbase (se 3 (by rfl) ⟨616226, by rfl⟩ : syracuseStep 3286541 = 1232453) (by norm_num)
theorem B2191027 : Blo 1947435 2191027 := bstep (se 1 (by rfl) ⟨1643270, by rfl⟩ : syracuseStep 2191027 = 3286541) B3286541
theorem B2921369 : Blo 1947435 2921369 := bstep (se 2 (by rfl) ⟨1095513, by rfl⟩ : syracuseStep 2921369 = 2191027) B2191027
theorem B1947579 : Blo 1947435 1947579 := bstep (se 1 (by rfl) ⟨1460684, by rfl⟩ : syracuseStep 1947579 = 2921369) B2921369
theorem B3119653 : Blo 1947435 3119653 := bbase (se 4 (by rfl) ⟨292467, by rfl⟩ : syracuseStep 3119653 = 584935) (by norm_num)
theorem B16638149 : Blo 1947435 16638149 := bstep (se 4 (by rfl) ⟨1559826, by rfl⟩ : syracuseStep 16638149 = 3119653) B3119653
theorem B11092099 : Blo 1947435 11092099 := bstep (se 1 (by rfl) ⟨8319074, by rfl⟩ : syracuseStep 11092099 = 16638149) B16638149
theorem B14789465 : Blo 1947435 14789465 := bstep (se 2 (by rfl) ⟨5546049, by rfl⟩ : syracuseStep 14789465 = 11092099) B11092099
theorem B9859643 : Blo 1947435 9859643 := bstep (se 1 (by rfl) ⟨7394732, by rfl⟩ : syracuseStep 9859643 = 14789465) B14789465
theorem B6573095 : Blo 1947435 6573095 := bstep (se 1 (by rfl) ⟨4929821, by rfl⟩ : syracuseStep 6573095 = 9859643) B9859643
theorem B4382063 : Blo 1947435 4382063 := bstep (se 1 (by rfl) ⟨3286547, by rfl⟩ : syracuseStep 4382063 = 6573095) B6573095
theorem B2921375 : Blo 1947435 2921375 := bstep (se 1 (by rfl) ⟨2191031, by rfl⟩ : syracuseStep 2921375 = 4382063) B4382063
theorem B1947583 : Blo 1947435 1947583 := bstep (se 1 (by rfl) ⟨1460687, by rfl⟩ : syracuseStep 1947583 = 2921375) B2921375
theorem B2921381 : Blo 1947435 2921381 := bbase (se 4 (by rfl) ⟨273879, by rfl⟩ : syracuseStep 2921381 = 547759) (by norm_num)
theorem B1947587 : Blo 1947435 1947587 := bstep (se 1 (by rfl) ⟨1460690, by rfl⟩ : syracuseStep 1947587 = 2921381) B2921381
theorem B2464921 : Blo 1947435 2464921 := bbase (se 2 (by rfl) ⟨924345, by rfl⟩ : syracuseStep 2464921 = 1848691) (by norm_num)
theorem B3286561 : Blo 1947435 3286561 := bstep (se 2 (by rfl) ⟨1232460, by rfl⟩ : syracuseStep 3286561 = 2464921) B2464921
theorem B4382081 : Blo 1947435 4382081 := bstep (se 2 (by rfl) ⟨1643280, by rfl⟩ : syracuseStep 4382081 = 3286561) B3286561
theorem B2921387 : Blo 1947435 2921387 := bstep (se 1 (by rfl) ⟨2191040, by rfl⟩ : syracuseStep 2921387 = 4382081) B4382081
theorem B1947591 : Blo 1947435 1947591 := bstep (se 1 (by rfl) ⟨1460693, by rfl⟩ : syracuseStep 1947591 = 2921387) B2921387
theorem B2191045 : Blo 1947435 2191045 := bbase (se 4 (by rfl) ⟨205410, by rfl⟩ : syracuseStep 2191045 = 410821) (by norm_num)
theorem B2921393 : Blo 1947435 2921393 := bstep (se 2 (by rfl) ⟨1095522, by rfl⟩ : syracuseStep 2921393 = 2191045) B2191045
theorem B1947595 : Blo 1947435 1947595 := bstep (se 1 (by rfl) ⟨1460696, by rfl⟩ : syracuseStep 1947595 = 2921393) B2921393
theorem B3697397 : Blo 1947435 3697397 := bbase (se 5 (by rfl) ⟨173315, by rfl⟩ : syracuseStep 3697397 = 346631) (by norm_num)
theorem B2464931 : Blo 1947435 2464931 := bstep (se 1 (by rfl) ⟨1848698, by rfl⟩ : syracuseStep 2464931 = 3697397) B3697397
theorem B6573149 : Blo 1947435 6573149 := bstep (se 3 (by rfl) ⟨1232465, by rfl⟩ : syracuseStep 6573149 = 2464931) B2464931
theorem B4382099 : Blo 1947435 4382099 := bstep (se 1 (by rfl) ⟨3286574, by rfl⟩ : syracuseStep 4382099 = 6573149) B6573149
theorem B2921399 : Blo 1947435 2921399 := bstep (se 1 (by rfl) ⟨2191049, by rfl⟩ : syracuseStep 2921399 = 4382099) B4382099
theorem B1947599 : Blo 1947435 1947599 := bstep (se 1 (by rfl) ⟨1460699, by rfl⟩ : syracuseStep 1947599 = 2921399) B2921399
theorem B2921405 : Blo 1947435 2921405 := bbase (se 3 (by rfl) ⟨547763, by rfl⟩ : syracuseStep 2921405 = 1095527) (by norm_num)
theorem B1947603 : Blo 1947435 1947603 := bstep (se 1 (by rfl) ⟨1460702, by rfl⟩ : syracuseStep 1947603 = 2921405) B2921405
theorem B4382117 : Blo 1947435 4382117 := bbase (se 4 (by rfl) ⟨410823, by rfl⟩ : syracuseStep 4382117 = 821647) (by norm_num)
theorem B2921411 : Blo 1947435 2921411 := bstep (se 1 (by rfl) ⟨2191058, by rfl⟩ : syracuseStep 2921411 = 4382117) B4382117
theorem B1947607 : Blo 1947435 1947607 := bstep (se 1 (by rfl) ⟨1460705, by rfl⟩ : syracuseStep 1947607 = 2921411) B2921411
theorem B4929893 : Blo 1947435 4929893 := bbase (se 4 (by rfl) ⟨462177, by rfl⟩ : syracuseStep 4929893 = 924355) (by norm_num)
theorem B3286595 : Blo 1947435 3286595 := bstep (se 1 (by rfl) ⟨2464946, by rfl⟩ : syracuseStep 3286595 = 4929893) B4929893
theorem B2191063 : Blo 1947435 2191063 := bstep (se 1 (by rfl) ⟨1643297, by rfl⟩ : syracuseStep 2191063 = 3286595) B3286595
theorem B2921417 : Blo 1947435 2921417 := bstep (se 2 (by rfl) ⟨1095531, by rfl⟩ : syracuseStep 2921417 = 2191063) B2191063
theorem B1947611 : Blo 1947435 1947611 := bstep (se 1 (by rfl) ⟨1460708, by rfl⟩ : syracuseStep 1947611 = 2921417) B2921417
theorem B3509669 : Blo 1947435 3509669 := bbase (se 4 (by rfl) ⟨329031, by rfl⟩ : syracuseStep 3509669 = 658063) (by norm_num)
theorem B2339779 : Blo 1947435 2339779 := bstep (se 1 (by rfl) ⟨1754834, by rfl⟩ : syracuseStep 2339779 = 3509669) B3509669
theorem B3119705 : Blo 1947435 3119705 := bstep (se 2 (by rfl) ⟨1169889, by rfl⟩ : syracuseStep 3119705 = 2339779) B2339779
theorem B2079803 : Blo 1947435 2079803 := bstep (se 1 (by rfl) ⟨1559852, by rfl⟩ : syracuseStep 2079803 = 3119705) B3119705
theorem B5546141 : Blo 1947435 5546141 := bstep (se 3 (by rfl) ⟨1039901, by rfl⟩ : syracuseStep 5546141 = 2079803) B2079803
theorem B3697427 : Blo 1947435 3697427 := bstep (se 1 (by rfl) ⟨2773070, by rfl⟩ : syracuseStep 3697427 = 5546141) B5546141
theorem B9859805 : Blo 1947435 9859805 := bstep (se 3 (by rfl) ⟨1848713, by rfl⟩ : syracuseStep 9859805 = 3697427) B3697427
theorem B6573203 : Blo 1947435 6573203 := bstep (se 1 (by rfl) ⟨4929902, by rfl⟩ : syracuseStep 6573203 = 9859805) B9859805
theorem B4382135 : Blo 1947435 4382135 := bstep (se 1 (by rfl) ⟨3286601, by rfl⟩ : syracuseStep 4382135 = 6573203) B6573203
theorem B2921423 : Blo 1947435 2921423 := bstep (se 1 (by rfl) ⟨2191067, by rfl⟩ : syracuseStep 2921423 = 4382135) B4382135
theorem B1947615 : Blo 1947435 1947615 := bstep (se 1 (by rfl) ⟨1460711, by rfl⟩ : syracuseStep 1947615 = 2921423) B2921423
theorem B2921429 : Blo 1947435 2921429 := bbase (se 7 (by rfl) ⟨34235, by rfl⟩ : syracuseStep 2921429 = 68471) (by norm_num)
theorem B1947619 : Blo 1947435 1947619 := bstep (se 1 (by rfl) ⟨1460714, by rfl⟩ : syracuseStep 1947619 = 2921429) B2921429
theorem B7394885 : Blo 1947435 7394885 := bbase (se 4 (by rfl) ⟨693270, by rfl⟩ : syracuseStep 7394885 = 1386541) (by norm_num)
theorem B4929923 : Blo 1947435 4929923 := bstep (se 1 (by rfl) ⟨3697442, by rfl⟩ : syracuseStep 4929923 = 7394885) B7394885
theorem B3286615 : Blo 1947435 3286615 := bstep (se 1 (by rfl) ⟨2464961, by rfl⟩ : syracuseStep 3286615 = 4929923) B4929923
theorem B4382153 : Blo 1947435 4382153 := bstep (se 2 (by rfl) ⟨1643307, by rfl⟩ : syracuseStep 4382153 = 3286615) B3286615
theorem B2921435 : Blo 1947435 2921435 := bstep (se 1 (by rfl) ⟨2191076, by rfl⟩ : syracuseStep 2921435 = 4382153) B4382153
theorem B1947623 : Blo 1947435 1947623 := bstep (se 1 (by rfl) ⟨1460717, by rfl⟩ : syracuseStep 1947623 = 2921435) B2921435
theorem B2191081 : Blo 1947435 2191081 := bbase (se 2 (by rfl) ⟨821655, by rfl⟩ : syracuseStep 2191081 = 1643311) (by norm_num)
theorem B2921441 : Blo 1947435 2921441 := bstep (se 2 (by rfl) ⟨1095540, by rfl⟩ : syracuseStep 2921441 = 2191081) B2191081
theorem B1947627 : Blo 1947435 1947627 := bstep (se 1 (by rfl) ⟨1460720, by rfl⟩ : syracuseStep 1947627 = 2921441) B2921441
theorem B11092373 : Blo 1947435 11092373 := bbase (se 6 (by rfl) ⟨259977, by rfl⟩ : syracuseStep 11092373 = 519955) (by norm_num)
theorem B7394915 : Blo 1947435 7394915 := bstep (se 1 (by rfl) ⟨5546186, by rfl⟩ : syracuseStep 7394915 = 11092373) B11092373
theorem B4929943 : Blo 1947435 4929943 := bstep (se 1 (by rfl) ⟨3697457, by rfl⟩ : syracuseStep 4929943 = 7394915) B7394915
theorem B6573257 : Blo 1947435 6573257 := bstep (se 2 (by rfl) ⟨2464971, by rfl⟩ : syracuseStep 6573257 = 4929943) B4929943
theorem B4382171 : Blo 1947435 4382171 := bstep (se 1 (by rfl) ⟨3286628, by rfl⟩ : syracuseStep 4382171 = 6573257) B6573257
theorem B2921447 : Blo 1947435 2921447 := bstep (se 1 (by rfl) ⟨2191085, by rfl⟩ : syracuseStep 2921447 = 4382171) B4382171
theorem B1947631 : Blo 1947435 1947631 := bstep (se 1 (by rfl) ⟨1460723, by rfl⟩ : syracuseStep 1947631 = 2921447) B2921447
theorem B2921453 : Blo 1947435 2921453 := bbase (se 3 (by rfl) ⟨547772, by rfl⟩ : syracuseStep 2921453 = 1095545) (by norm_num)
theorem B1947635 : Blo 1947435 1947635 := bstep (se 1 (by rfl) ⟨1460726, by rfl⟩ : syracuseStep 1947635 = 2921453) B2921453
theorem B4382189 : Blo 1947435 4382189 := bbase (se 3 (by rfl) ⟨821660, by rfl⟩ : syracuseStep 4382189 = 1643321) (by norm_num)
theorem B2921459 : Blo 1947435 2921459 := bstep (se 1 (by rfl) ⟨2191094, by rfl⟩ : syracuseStep 2921459 = 4382189) B4382189
theorem B1947639 : Blo 1947435 1947639 := bstep (se 1 (by rfl) ⟨1460729, by rfl⟩ : syracuseStep 1947639 = 2921459) B2921459
theorem B2339813 : Blo 1947435 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B6239501 : Blo 1947435 6239501 := bstep (se 3 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 6239501 = 2339813) B2339813
theorem B4159667 : Blo 1947435 4159667 := bstep (se 1 (by rfl) ⟨3119750, by rfl⟩ : syracuseStep 4159667 = 6239501) B6239501
theorem B2773111 : Blo 1947435 2773111 := bstep (se 1 (by rfl) ⟨2079833, by rfl⟩ : syracuseStep 2773111 = 4159667) B4159667
theorem B3697481 : Blo 1947435 3697481 := bstep (se 2 (by rfl) ⟨1386555, by rfl⟩ : syracuseStep 3697481 = 2773111) B2773111
theorem B2464987 : Blo 1947435 2464987 := bstep (se 1 (by rfl) ⟨1848740, by rfl⟩ : syracuseStep 2464987 = 3697481) B3697481
theorem B3286649 : Blo 1947435 3286649 := bstep (se 2 (by rfl) ⟨1232493, by rfl⟩ : syracuseStep 3286649 = 2464987) B2464987
theorem B2191099 : Blo 1947435 2191099 := bstep (se 1 (by rfl) ⟨1643324, by rfl⟩ : syracuseStep 2191099 = 3286649) B3286649
theorem B2921465 : Blo 1947435 2921465 := bstep (se 2 (by rfl) ⟨1095549, by rfl⟩ : syracuseStep 2921465 = 2191099) B2191099
theorem B1947643 : Blo 1947435 1947643 := bstep (se 1 (by rfl) ⟨1460732, by rfl⟩ : syracuseStep 1947643 = 2921465) B2921465
theorem B4940293 : Blo 1947435 4940293 := bbase (se 4 (by rfl) ⟨463152, by rfl⟩ : syracuseStep 4940293 = 926305) (by norm_num)
theorem B6587057 : Blo 1947435 6587057 := bstep (se 2 (by rfl) ⟨2470146, by rfl⟩ : syracuseStep 6587057 = 4940293) B4940293
theorem B4391371 : Blo 1947435 4391371 := bstep (se 1 (by rfl) ⟨3293528, by rfl⟩ : syracuseStep 4391371 = 6587057) B6587057
theorem B5855161 : Blo 1947435 5855161 := bstep (se 2 (by rfl) ⟨2195685, by rfl⟩ : syracuseStep 5855161 = 4391371) B4391371
theorem B7806881 : Blo 1947435 7806881 := bstep (se 2 (by rfl) ⟨2927580, by rfl⟩ : syracuseStep 7806881 = 5855161) B5855161
theorem B5204587 : Blo 1947435 5204587 := bstep (se 1 (by rfl) ⟨3903440, by rfl⟩ : syracuseStep 5204587 = 7806881) B7806881
theorem B6939449 : Blo 1947435 6939449 := bstep (se 2 (by rfl) ⟨2602293, by rfl⟩ : syracuseStep 6939449 = 5204587) B5204587
theorem B4626299 : Blo 1947435 4626299 := bstep (se 1 (by rfl) ⟨3469724, by rfl⟩ : syracuseStep 4626299 = 6939449) B6939449
theorem B3084199 : Blo 1947435 3084199 := bstep (se 1 (by rfl) ⟨2313149, by rfl⟩ : syracuseStep 3084199 = 4626299) B4626299
theorem B65796245 : Blo 1947435 65796245 := bstep (se 6 (by rfl) ⟨1542099, by rfl⟩ : syracuseStep 65796245 = 3084199) B3084199
theorem B43864163 : Blo 1947435 43864163 := bstep (se 1 (by rfl) ⟨32898122, by rfl⟩ : syracuseStep 43864163 = 65796245) B65796245
theorem B29242775 : Blo 1947435 29242775 := bstep (se 1 (by rfl) ⟨21932081, by rfl⟩ : syracuseStep 29242775 = 43864163) B43864163
theorem B19495183 : Blo 1947435 19495183 := bstep (se 1 (by rfl) ⟨14621387, by rfl⟩ : syracuseStep 19495183 = 29242775) B29242775
theorem B25993577 : Blo 1947435 25993577 := bstep (se 2 (by rfl) ⟨9747591, by rfl⟩ : syracuseStep 25993577 = 19495183) B19495183
theorem B17329051 : Blo 1947435 17329051 := bstep (se 1 (by rfl) ⟨12996788, by rfl⟩ : syracuseStep 17329051 = 25993577) B25993577
theorem B23105401 : Blo 1947435 23105401 := bstep (se 2 (by rfl) ⟨8664525, by rfl⟩ : syracuseStep 23105401 = 17329051) B17329051
theorem B123228805 : Blo 1947435 123228805 := bstep (se 4 (by rfl) ⟨11552700, by rfl⟩ : syracuseStep 123228805 = 23105401) B23105401
theorem B164305073 : Blo 1947435 164305073 := bstep (se 2 (by rfl) ⟨61614402, by rfl⟩ : syracuseStep 164305073 = 123228805) B123228805
theorem B109536715 : Blo 1947435 109536715 := bstep (se 1 (by rfl) ⟨82152536, by rfl⟩ : syracuseStep 109536715 = 164305073) B164305073
theorem B146048953 : Blo 1947435 146048953 := bstep (se 2 (by rfl) ⟨54768357, by rfl⟩ : syracuseStep 146048953 = 109536715) B109536715
theorem B194731937 : Blo 1947435 194731937 := bstep (se 2 (by rfl) ⟨73024476, by rfl⟩ : syracuseStep 194731937 = 146048953) B146048953
theorem B129821291 : Blo 1947435 129821291 := bstep (se 1 (by rfl) ⟨97365968, by rfl⟩ : syracuseStep 129821291 = 194731937) B194731937
theorem B86547527 : Blo 1947435 86547527 := bstep (se 1 (by rfl) ⟨64910645, by rfl⟩ : syracuseStep 86547527 = 129821291) B129821291
theorem B57698351 : Blo 1947435 57698351 := bstep (se 1 (by rfl) ⟨43273763, by rfl⟩ : syracuseStep 57698351 = 86547527) B86547527
theorem B38465567 : Blo 1947435 38465567 := bstep (se 1 (by rfl) ⟨28849175, by rfl⟩ : syracuseStep 38465567 = 57698351) B57698351
theorem B25643711 : Blo 1947435 25643711 := bstep (se 1 (by rfl) ⟨19232783, by rfl⟩ : syracuseStep 25643711 = 38465567) B38465567
theorem B17095807 : Blo 1947435 17095807 := bstep (se 1 (by rfl) ⟨12821855, by rfl⟩ : syracuseStep 17095807 = 25643711) B25643711
theorem B22794409 : Blo 1947435 22794409 := bstep (se 2 (by rfl) ⟨8547903, by rfl⟩ : syracuseStep 22794409 = 17095807) B17095807
theorem B30392545 : Blo 1947435 30392545 := bstep (se 2 (by rfl) ⟨11397204, by rfl⟩ : syracuseStep 30392545 = 22794409) B22794409
theorem B40523393 : Blo 1947435 40523393 := bstep (se 2 (by rfl) ⟨15196272, by rfl⟩ : syracuseStep 40523393 = 30392545) B30392545
theorem B108062381 : Blo 1947435 108062381 := bstep (se 3 (by rfl) ⟨20261696, by rfl⟩ : syracuseStep 108062381 = 40523393) B40523393
theorem B288166349 : Blo 1947435 288166349 := bstep (se 3 (by rfl) ⟨54031190, by rfl⟩ : syracuseStep 288166349 = 108062381) B108062381
theorem B192110899 : Blo 1947435 192110899 := bstep (se 1 (by rfl) ⟨144083174, by rfl⟩ : syracuseStep 192110899 = 288166349) B288166349
theorem B256147865 : Blo 1947435 256147865 := bstep (se 2 (by rfl) ⟨96055449, by rfl⟩ : syracuseStep 256147865 = 192110899) B192110899
theorem B170765243 : Blo 1947435 170765243 := bstep (se 1 (by rfl) ⟨128073932, by rfl⟩ : syracuseStep 170765243 = 256147865) B256147865
theorem B113843495 : Blo 1947435 113843495 := bstep (se 1 (by rfl) ⟨85382621, by rfl⟩ : syracuseStep 113843495 = 170765243) B170765243
theorem B75895663 : Blo 1947435 75895663 := bstep (se 1 (by rfl) ⟨56921747, by rfl⟩ : syracuseStep 75895663 = 113843495) B113843495
theorem B101194217 : Blo 1947435 101194217 := bstep (se 2 (by rfl) ⟨37947831, by rfl⟩ : syracuseStep 101194217 = 75895663) B75895663
theorem B67462811 : Blo 1947435 67462811 := bstep (se 1 (by rfl) ⟨50597108, by rfl⟩ : syracuseStep 67462811 = 101194217) B101194217
theorem B44975207 : Blo 1947435 44975207 := bstep (se 1 (by rfl) ⟨33731405, by rfl⟩ : syracuseStep 44975207 = 67462811) B67462811
theorem B119933885 : Blo 1947435 119933885 := bstep (se 3 (by rfl) ⟨22487603, by rfl⟩ : syracuseStep 119933885 = 44975207) B44975207
theorem B79955923 : Blo 1947435 79955923 := bstep (se 1 (by rfl) ⟨59966942, by rfl⟩ : syracuseStep 79955923 = 119933885) B119933885
theorem B106607897 : Blo 1947435 106607897 := bstep (se 2 (by rfl) ⟨39977961, by rfl⟩ : syracuseStep 106607897 = 79955923) B79955923
theorem B71071931 : Blo 1947435 71071931 := bstep (se 1 (by rfl) ⟨53303948, by rfl⟩ : syracuseStep 71071931 = 106607897) B106607897
theorem B47381287 : Blo 1947435 47381287 := bstep (se 1 (by rfl) ⟨35535965, by rfl⟩ : syracuseStep 47381287 = 71071931) B71071931
theorem B63175049 : Blo 1947435 63175049 := bstep (se 2 (by rfl) ⟨23690643, by rfl⟩ : syracuseStep 63175049 = 47381287) B47381287
theorem B42116699 : Blo 1947435 42116699 := bstep (se 1 (by rfl) ⟨31587524, by rfl⟩ : syracuseStep 42116699 = 63175049) B63175049
theorem B112311197 : Blo 1947435 112311197 := bstep (se 3 (by rfl) ⟨21058349, by rfl⟩ : syracuseStep 112311197 = 42116699) B42116699
theorem B74874131 : Blo 1947435 74874131 := bstep (se 1 (by rfl) ⟨56155598, by rfl⟩ : syracuseStep 74874131 = 112311197) B112311197
theorem B49916087 : Blo 1947435 49916087 := bstep (se 1 (by rfl) ⟨37437065, by rfl⟩ : syracuseStep 49916087 = 74874131) B74874131
theorem B33277391 : Blo 1947435 33277391 := bstep (se 1 (by rfl) ⟨24958043, by rfl⟩ : syracuseStep 33277391 = 49916087) B49916087
theorem B22184927 : Blo 1947435 22184927 := bstep (se 1 (by rfl) ⟨16638695, by rfl⟩ : syracuseStep 22184927 = 33277391) B33277391
theorem B14789951 : Blo 1947435 14789951 := bstep (se 1 (by rfl) ⟨11092463, by rfl⟩ : syracuseStep 14789951 = 22184927) B22184927
theorem B9859967 : Blo 1947435 9859967 := bstep (se 1 (by rfl) ⟨7394975, by rfl⟩ : syracuseStep 9859967 = 14789951) B14789951
theorem B6573311 : Blo 1947435 6573311 := bstep (se 1 (by rfl) ⟨4929983, by rfl⟩ : syracuseStep 6573311 = 9859967) B9859967
theorem B4382207 : Blo 1947435 4382207 := bstep (se 1 (by rfl) ⟨3286655, by rfl⟩ : syracuseStep 4382207 = 6573311) B6573311
theorem B2921471 : Blo 1947435 2921471 := bstep (se 1 (by rfl) ⟨2191103, by rfl⟩ : syracuseStep 2921471 = 4382207) B4382207
theorem B1947647 : Blo 1947435 1947647 := bstep (se 1 (by rfl) ⟨1460735, by rfl⟩ : syracuseStep 1947647 = 2921471) B2921471
theorem B2921477 : Blo 1947435 2921477 := bbase (se 4 (by rfl) ⟨273888, by rfl⟩ : syracuseStep 2921477 = 547777) (by norm_num)
theorem B1947651 : Blo 1947435 1947651 := bstep (se 1 (by rfl) ⟨1460738, by rfl⟩ : syracuseStep 1947651 = 2921477) B2921477
theorem B3286669 : Blo 1947435 3286669 := bbase (se 3 (by rfl) ⟨616250, by rfl⟩ : syracuseStep 3286669 = 1232501) (by norm_num)
theorem B4382225 : Blo 1947435 4382225 := bstep (se 2 (by rfl) ⟨1643334, by rfl⟩ : syracuseStep 4382225 = 3286669) B3286669
theorem B2921483 : Blo 1947435 2921483 := bstep (se 1 (by rfl) ⟨2191112, by rfl⟩ : syracuseStep 2921483 = 4382225) B4382225
theorem B1947655 : Blo 1947435 1947655 := bstep (se 1 (by rfl) ⟨1460741, by rfl⟩ : syracuseStep 1947655 = 2921483) B2921483
theorem B2191117 : Blo 1947435 2191117 := bbase (se 3 (by rfl) ⟨410834, by rfl⟩ : syracuseStep 2191117 = 821669) (by norm_num)
theorem B2921489 : Blo 1947435 2921489 := bstep (se 2 (by rfl) ⟨1095558, by rfl⟩ : syracuseStep 2921489 = 2191117) B2191117
theorem B1947659 : Blo 1947435 1947659 := bstep (se 1 (by rfl) ⟨1460744, by rfl⟩ : syracuseStep 1947659 = 2921489) B2921489
theorem B6573365 : Blo 1947435 6573365 := bbase (se 5 (by rfl) ⟨308126, by rfl⟩ : syracuseStep 6573365 = 616253) (by norm_num)
theorem B4382243 : Blo 1947435 4382243 := bstep (se 1 (by rfl) ⟨3286682, by rfl⟩ : syracuseStep 4382243 = 6573365) B6573365
theorem B2921495 : Blo 1947435 2921495 := bstep (se 1 (by rfl) ⟨2191121, by rfl⟩ : syracuseStep 2921495 = 4382243) B4382243
theorem B1947663 : Blo 1947435 1947663 := bstep (se 1 (by rfl) ⟨1460747, by rfl⟩ : syracuseStep 1947663 = 2921495) B2921495
theorem B2921501 : Blo 1947435 2921501 := bbase (se 3 (by rfl) ⟨547781, by rfl⟩ : syracuseStep 2921501 = 1095563) (by norm_num)
theorem B1947667 : Blo 1947435 1947667 := bstep (se 1 (by rfl) ⟨1460750, by rfl⟩ : syracuseStep 1947667 = 2921501) B2921501
theorem B4382261 : Blo 1947435 4382261 := bbase (se 5 (by rfl) ⟨205418, by rfl⟩ : syracuseStep 4382261 = 410837) (by norm_num)
theorem B2921507 : Blo 1947435 2921507 := bstep (se 1 (by rfl) ⟨2191130, by rfl⟩ : syracuseStep 2921507 = 4382261) B4382261
theorem B1947671 : Blo 1947435 1947671 := bstep (se 1 (by rfl) ⟨1460753, by rfl⟩ : syracuseStep 1947671 = 2921507) B2921507
theorem B2632333 : Blo 1947435 2632333 := bbase (se 3 (by rfl) ⟨493562, by rfl⟩ : syracuseStep 2632333 = 987125) (by norm_num)
theorem B3509777 : Blo 1947435 3509777 := bstep (se 2 (by rfl) ⟨1316166, by rfl⟩ : syracuseStep 3509777 = 2632333) B2632333
theorem B2339851 : Blo 1947435 2339851 := bstep (se 1 (by rfl) ⟨1754888, by rfl⟩ : syracuseStep 2339851 = 3509777) B3509777
theorem B3119801 : Blo 1947435 3119801 := bstep (se 2 (by rfl) ⟨1169925, by rfl⟩ : syracuseStep 3119801 = 2339851) B2339851
theorem B8319469 : Blo 1947435 8319469 := bstep (se 3 (by rfl) ⟨1559900, by rfl⟩ : syracuseStep 8319469 = 3119801) B3119801
theorem B11092625 : Blo 1947435 11092625 := bstep (se 2 (by rfl) ⟨4159734, by rfl⟩ : syracuseStep 11092625 = 8319469) B8319469
theorem B7395083 : Blo 1947435 7395083 := bstep (se 1 (by rfl) ⟨5546312, by rfl⟩ : syracuseStep 7395083 = 11092625) B11092625
theorem B4930055 : Blo 1947435 4930055 := bstep (se 1 (by rfl) ⟨3697541, by rfl⟩ : syracuseStep 4930055 = 7395083) B7395083
theorem B3286703 : Blo 1947435 3286703 := bstep (se 1 (by rfl) ⟨2465027, by rfl⟩ : syracuseStep 3286703 = 4930055) B4930055
theorem B2191135 : Blo 1947435 2191135 := bstep (se 1 (by rfl) ⟨1643351, by rfl⟩ : syracuseStep 2191135 = 3286703) B3286703
theorem B2921513 : Blo 1947435 2921513 := bstep (se 2 (by rfl) ⟨1095567, by rfl⟩ : syracuseStep 2921513 = 2191135) B2191135
theorem B1947675 : Blo 1947435 1947675 := bstep (se 1 (by rfl) ⟨1460756, by rfl⟩ : syracuseStep 1947675 = 2921513) B2921513
theorem B3747997 : Blo 1947435 3747997 := bbase (se 3 (by rfl) ⟨702749, by rfl⟩ : syracuseStep 3747997 = 1405499) (by norm_num)
theorem B19989317 : Blo 1947435 19989317 := bstep (se 4 (by rfl) ⟨1873998, by rfl⟩ : syracuseStep 19989317 = 3747997) B3747997
theorem B13326211 : Blo 1947435 13326211 := bstep (se 1 (by rfl) ⟨9994658, by rfl⟩ : syracuseStep 13326211 = 19989317) B19989317
theorem B17768281 : Blo 1947435 17768281 := bstep (se 2 (by rfl) ⟨6663105, by rfl⟩ : syracuseStep 17768281 = 13326211) B13326211
theorem B23691041 : Blo 1947435 23691041 := bstep (se 2 (by rfl) ⟨8884140, by rfl⟩ : syracuseStep 23691041 = 17768281) B17768281
theorem B15794027 : Blo 1947435 15794027 := bstep (se 1 (by rfl) ⟨11845520, by rfl⟩ : syracuseStep 15794027 = 23691041) B23691041
theorem B10529351 : Blo 1947435 10529351 := bstep (se 1 (by rfl) ⟨7897013, by rfl⟩ : syracuseStep 10529351 = 15794027) B15794027
theorem B7019567 : Blo 1947435 7019567 := bstep (se 1 (by rfl) ⟨5264675, by rfl⟩ : syracuseStep 7019567 = 10529351) B10529351
theorem B4679711 : Blo 1947435 4679711 := bstep (se 1 (by rfl) ⟨3509783, by rfl⟩ : syracuseStep 4679711 = 7019567) B7019567
theorem B3119807 : Blo 1947435 3119807 := bstep (se 1 (by rfl) ⟨2339855, by rfl⟩ : syracuseStep 3119807 = 4679711) B4679711
theorem B8319485 : Blo 1947435 8319485 := bstep (se 3 (by rfl) ⟨1559903, by rfl⟩ : syracuseStep 8319485 = 3119807) B3119807
theorem B5546323 : Blo 1947435 5546323 := bstep (se 1 (by rfl) ⟨4159742, by rfl⟩ : syracuseStep 5546323 = 8319485) B8319485
theorem B7395097 : Blo 1947435 7395097 := bstep (se 2 (by rfl) ⟨2773161, by rfl⟩ : syracuseStep 7395097 = 5546323) B5546323
theorem B9860129 : Blo 1947435 9860129 := bstep (se 2 (by rfl) ⟨3697548, by rfl⟩ : syracuseStep 9860129 = 7395097) B7395097
theorem B6573419 : Blo 1947435 6573419 := bstep (se 1 (by rfl) ⟨4930064, by rfl⟩ : syracuseStep 6573419 = 9860129) B9860129
theorem B4382279 : Blo 1947435 4382279 := bstep (se 1 (by rfl) ⟨3286709, by rfl⟩ : syracuseStep 4382279 = 6573419) B6573419
theorem B2921519 : Blo 1947435 2921519 := bstep (se 1 (by rfl) ⟨2191139, by rfl⟩ : syracuseStep 2921519 = 4382279) B4382279
theorem B1947679 : Blo 1947435 1947679 := bstep (se 1 (by rfl) ⟨1460759, by rfl⟩ : syracuseStep 1947679 = 2921519) B2921519
theorem B2921525 : Blo 1947435 2921525 := bbase (se 5 (by rfl) ⟨136946, by rfl⟩ : syracuseStep 2921525 = 273893) (by norm_num)
theorem B1947683 : Blo 1947435 1947683 := bstep (se 1 (by rfl) ⟨1460762, by rfl⟩ : syracuseStep 1947683 = 2921525) B2921525
theorem B4930085 : Blo 1947435 4930085 := bbase (se 4 (by rfl) ⟨462195, by rfl⟩ : syracuseStep 4930085 = 924391) (by norm_num)
theorem B3286723 : Blo 1947435 3286723 := bstep (se 1 (by rfl) ⟨2465042, by rfl⟩ : syracuseStep 3286723 = 4930085) B4930085
theorem B4382297 : Blo 1947435 4382297 := bstep (se 2 (by rfl) ⟨1643361, by rfl⟩ : syracuseStep 4382297 = 3286723) B3286723
theorem B2921531 : Blo 1947435 2921531 := bstep (se 1 (by rfl) ⟨2191148, by rfl⟩ : syracuseStep 2921531 = 4382297) B4382297
theorem B1947687 : Blo 1947435 1947687 := bstep (se 1 (by rfl) ⟨1460765, by rfl⟩ : syracuseStep 1947687 = 2921531) B2921531
theorem B2191153 : Blo 1947435 2191153 := bbase (se 2 (by rfl) ⟨821682, by rfl⟩ : syracuseStep 2191153 = 1643365) (by norm_num)
theorem B2921537 : Blo 1947435 2921537 := bstep (se 2 (by rfl) ⟨1095576, by rfl⟩ : syracuseStep 2921537 = 2191153) B2191153
theorem B1947691 : Blo 1947435 1947691 := bstep (se 1 (by rfl) ⟨1460768, by rfl⟩ : syracuseStep 1947691 = 2921537) B2921537
theorem B3509813 : Blo 1947435 3509813 := bbase (se 5 (by rfl) ⟨164522, by rfl⟩ : syracuseStep 3509813 = 329045) (by norm_num)
theorem B2339875 : Blo 1947435 2339875 := bstep (se 1 (by rfl) ⟨1754906, by rfl⟩ : syracuseStep 2339875 = 3509813) B3509813
theorem B3119833 : Blo 1947435 3119833 := bstep (se 2 (by rfl) ⟨1169937, by rfl⟩ : syracuseStep 3119833 = 2339875) B2339875
theorem B4159777 : Blo 1947435 4159777 := bstep (se 2 (by rfl) ⟨1559916, by rfl⟩ : syracuseStep 4159777 = 3119833) B3119833
theorem B5546369 : Blo 1947435 5546369 := bstep (se 2 (by rfl) ⟨2079888, by rfl⟩ : syracuseStep 5546369 = 4159777) B4159777
theorem B3697579 : Blo 1947435 3697579 := bstep (se 1 (by rfl) ⟨2773184, by rfl⟩ : syracuseStep 3697579 = 5546369) B5546369
theorem B4930105 : Blo 1947435 4930105 := bstep (se 2 (by rfl) ⟨1848789, by rfl⟩ : syracuseStep 4930105 = 3697579) B3697579
theorem B6573473 : Blo 1947435 6573473 := bstep (se 2 (by rfl) ⟨2465052, by rfl⟩ : syracuseStep 6573473 = 4930105) B4930105
theorem B4382315 : Blo 1947435 4382315 := bstep (se 1 (by rfl) ⟨3286736, by rfl⟩ : syracuseStep 4382315 = 6573473) B6573473
theorem B2921543 : Blo 1947435 2921543 := bstep (se 1 (by rfl) ⟨2191157, by rfl⟩ : syracuseStep 2921543 = 4382315) B4382315
theorem B1947695 : Blo 1947435 1947695 := bstep (se 1 (by rfl) ⟨1460771, by rfl⟩ : syracuseStep 1947695 = 2921543) B2921543
theorem B2921549 : Blo 1947435 2921549 := bbase (se 3 (by rfl) ⟨547790, by rfl⟩ : syracuseStep 2921549 = 1095581) (by norm_num)
theorem B1947699 : Blo 1947435 1947699 := bstep (se 1 (by rfl) ⟨1460774, by rfl⟩ : syracuseStep 1947699 = 2921549) B2921549
theorem B4382333 : Blo 1947435 4382333 := bbase (se 3 (by rfl) ⟨821687, by rfl⟩ : syracuseStep 4382333 = 1643375) (by norm_num)
theorem B2921555 : Blo 1947435 2921555 := bstep (se 1 (by rfl) ⟨2191166, by rfl⟩ : syracuseStep 2921555 = 4382333) B4382333
theorem B1947703 : Blo 1947435 1947703 := bstep (se 1 (by rfl) ⟨1460777, by rfl⟩ : syracuseStep 1947703 = 2921555) B2921555
theorem B3286757 : Blo 1947435 3286757 := bbase (se 4 (by rfl) ⟨308133, by rfl⟩ : syracuseStep 3286757 = 616267) (by norm_num)
theorem B2191171 : Blo 1947435 2191171 := bstep (se 1 (by rfl) ⟨1643378, by rfl⟩ : syracuseStep 2191171 = 3286757) B3286757
theorem B2921561 : Blo 1947435 2921561 := bstep (se 2 (by rfl) ⟨1095585, by rfl⟩ : syracuseStep 2921561 = 2191171) B2191171
theorem B1947707 : Blo 1947435 1947707 := bstep (se 1 (by rfl) ⟨1460780, by rfl⟩ : syracuseStep 1947707 = 2921561) B2921561
theorem B6239717 : Blo 1947435 6239717 := bbase (se 4 (by rfl) ⟨584973, by rfl⟩ : syracuseStep 6239717 = 1169947) (by norm_num)
theorem B4159811 : Blo 1947435 4159811 := bstep (se 1 (by rfl) ⟨3119858, by rfl⟩ : syracuseStep 4159811 = 6239717) B6239717
theorem B2773207 : Blo 1947435 2773207 := bstep (se 1 (by rfl) ⟨2079905, by rfl⟩ : syracuseStep 2773207 = 4159811) B4159811
theorem B14790437 : Blo 1947435 14790437 := bstep (se 4 (by rfl) ⟨1386603, by rfl⟩ : syracuseStep 14790437 = 2773207) B2773207
theorem B9860291 : Blo 1947435 9860291 := bstep (se 1 (by rfl) ⟨7395218, by rfl⟩ : syracuseStep 9860291 = 14790437) B14790437
theorem B6573527 : Blo 1947435 6573527 := bstep (se 1 (by rfl) ⟨4930145, by rfl⟩ : syracuseStep 6573527 = 9860291) B9860291
theorem B4382351 : Blo 1947435 4382351 := bstep (se 1 (by rfl) ⟨3286763, by rfl⟩ : syracuseStep 4382351 = 6573527) B6573527
theorem B2921567 : Blo 1947435 2921567 := bstep (se 1 (by rfl) ⟨2191175, by rfl⟩ : syracuseStep 2921567 = 4382351) B4382351
theorem B1947711 : Blo 1947435 1947711 := bstep (se 1 (by rfl) ⟨1460783, by rfl⟩ : syracuseStep 1947711 = 2921567) B2921567
theorem B2921573 : Blo 1947435 2921573 := bbase (se 4 (by rfl) ⟨273897, by rfl⟩ : syracuseStep 2921573 = 547795) (by norm_num)
theorem B1947715 : Blo 1947435 1947715 := bstep (se 1 (by rfl) ⟨1460786, by rfl⟩ : syracuseStep 1947715 = 2921573) B2921573
theorem B4159829 : Blo 1947435 4159829 := bbase (se 10 (by rfl) ⟨6093, by rfl⟩ : syracuseStep 4159829 = 12187) (by norm_num)
theorem B2773219 : Blo 1947435 2773219 := bstep (se 1 (by rfl) ⟨2079914, by rfl⟩ : syracuseStep 2773219 = 4159829) B4159829
theorem B3697625 : Blo 1947435 3697625 := bstep (se 2 (by rfl) ⟨1386609, by rfl⟩ : syracuseStep 3697625 = 2773219) B2773219
theorem B2465083 : Blo 1947435 2465083 := bstep (se 1 (by rfl) ⟨1848812, by rfl⟩ : syracuseStep 2465083 = 3697625) B3697625
theorem B3286777 : Blo 1947435 3286777 := bstep (se 2 (by rfl) ⟨1232541, by rfl⟩ : syracuseStep 3286777 = 2465083) B2465083
theorem B4382369 : Blo 1947435 4382369 := bstep (se 2 (by rfl) ⟨1643388, by rfl⟩ : syracuseStep 4382369 = 3286777) B3286777
theorem B2921579 : Blo 1947435 2921579 := bstep (se 1 (by rfl) ⟨2191184, by rfl⟩ : syracuseStep 2921579 = 4382369) B4382369
theorem B1947719 : Blo 1947435 1947719 := bstep (se 1 (by rfl) ⟨1460789, by rfl⟩ : syracuseStep 1947719 = 2921579) B2921579
theorem B2191189 : Blo 1947435 2191189 := bbase (se 9 (by rfl) ⟨6419, by rfl⟩ : syracuseStep 2191189 = 12839) (by norm_num)
theorem B2921585 : Blo 1947435 2921585 := bstep (se 2 (by rfl) ⟨1095594, by rfl⟩ : syracuseStep 2921585 = 2191189) B2191189
theorem B1947723 : Blo 1947435 1947723 := bstep (se 1 (by rfl) ⟨1460792, by rfl⟩ : syracuseStep 1947723 = 2921585) B2921585
theorem B2465093 : Blo 1947435 2465093 := bbase (se 4 (by rfl) ⟨231102, by rfl⟩ : syracuseStep 2465093 = 462205) (by norm_num)
theorem B6573581 : Blo 1947435 6573581 := bstep (se 3 (by rfl) ⟨1232546, by rfl⟩ : syracuseStep 6573581 = 2465093) B2465093
theorem B4382387 : Blo 1947435 4382387 := bstep (se 1 (by rfl) ⟨3286790, by rfl⟩ : syracuseStep 4382387 = 6573581) B6573581
theorem B2921591 : Blo 1947435 2921591 := bstep (se 1 (by rfl) ⟨2191193, by rfl⟩ : syracuseStep 2921591 = 4382387) B4382387
theorem B1947727 : Blo 1947435 1947727 := bstep (se 1 (by rfl) ⟨1460795, by rfl⟩ : syracuseStep 1947727 = 2921591) B2921591
theorem B2921597 : Blo 1947435 2921597 := bbase (se 3 (by rfl) ⟨547799, by rfl⟩ : syracuseStep 2921597 = 1095599) (by norm_num)
theorem B1947731 : Blo 1947435 1947731 := bstep (se 1 (by rfl) ⟨1460798, by rfl⟩ : syracuseStep 1947731 = 2921597) B2921597
theorem B4382405 : Blo 1947435 4382405 := bbase (se 4 (by rfl) ⟨410850, by rfl⟩ : syracuseStep 4382405 = 821701) (by norm_num)
theorem B2921603 : Blo 1947435 2921603 := bstep (se 1 (by rfl) ⟨2191202, by rfl⟩ : syracuseStep 2921603 = 4382405) B4382405
theorem B1947735 : Blo 1947435 1947735 := bstep (se 1 (by rfl) ⟨1460801, by rfl⟩ : syracuseStep 1947735 = 2921603) B2921603
theorem B4057109 : Blo 1947435 4057109 := bbase (se 6 (by rfl) ⟨95088, by rfl⟩ : syracuseStep 4057109 = 190177) (by norm_num)
theorem B2704739 : Blo 1947435 2704739 := bstep (se 1 (by rfl) ⟨2028554, by rfl⟩ : syracuseStep 2704739 = 4057109) B4057109
theorem B7212637 : Blo 1947435 7212637 := bstep (se 3 (by rfl) ⟨1352369, by rfl⟩ : syracuseStep 7212637 = 2704739) B2704739
theorem B9616849 : Blo 1947435 9616849 := bstep (se 2 (by rfl) ⟨3606318, by rfl⟩ : syracuseStep 9616849 = 7212637) B7212637
theorem B51289861 : Blo 1947435 51289861 := bstep (se 4 (by rfl) ⟨4808424, by rfl⟩ : syracuseStep 51289861 = 9616849) B9616849
theorem B68386481 : Blo 1947435 68386481 := bstep (se 2 (by rfl) ⟨25644930, by rfl⟩ : syracuseStep 68386481 = 51289861) B51289861
theorem B45590987 : Blo 1947435 45590987 := bstep (se 1 (by rfl) ⟨34193240, by rfl⟩ : syracuseStep 45590987 = 68386481) B68386481
theorem B30393991 : Blo 1947435 30393991 := bstep (se 1 (by rfl) ⟨22795493, by rfl⟩ : syracuseStep 30393991 = 45590987) B45590987
theorem B40525321 : Blo 1947435 40525321 := bstep (se 2 (by rfl) ⟨15196995, by rfl⟩ : syracuseStep 40525321 = 30393991) B30393991
theorem B54033761 : Blo 1947435 54033761 := bstep (se 2 (by rfl) ⟨20262660, by rfl⟩ : syracuseStep 54033761 = 40525321) B40525321
theorem B144090029 : Blo 1947435 144090029 := bstep (se 3 (by rfl) ⟨27016880, by rfl⟩ : syracuseStep 144090029 = 54033761) B54033761
theorem B96060019 : Blo 1947435 96060019 := bstep (se 1 (by rfl) ⟨72045014, by rfl⟩ : syracuseStep 96060019 = 144090029) B144090029
theorem B128080025 : Blo 1947435 128080025 := bstep (se 2 (by rfl) ⟨48030009, by rfl⟩ : syracuseStep 128080025 = 96060019) B96060019
theorem B85386683 : Blo 1947435 85386683 := bstep (se 1 (by rfl) ⟨64040012, by rfl⟩ : syracuseStep 85386683 = 128080025) B128080025
theorem B56924455 : Blo 1947435 56924455 := bstep (se 1 (by rfl) ⟨42693341, by rfl⟩ : syracuseStep 56924455 = 85386683) B85386683
theorem B75899273 : Blo 1947435 75899273 := bstep (se 2 (by rfl) ⟨28462227, by rfl⟩ : syracuseStep 75899273 = 56924455) B56924455
theorem B202398061 : Blo 1947435 202398061 := bstep (se 3 (by rfl) ⟨37949636, by rfl⟩ : syracuseStep 202398061 = 75899273) B75899273
theorem B269864081 : Blo 1947435 269864081 := bstep (se 2 (by rfl) ⟨101199030, by rfl⟩ : syracuseStep 269864081 = 202398061) B202398061
theorem B179909387 : Blo 1947435 179909387 := bstep (se 1 (by rfl) ⟨134932040, by rfl⟩ : syracuseStep 179909387 = 269864081) B269864081
theorem B119939591 : Blo 1947435 119939591 := bstep (se 1 (by rfl) ⟨89954693, by rfl⟩ : syracuseStep 119939591 = 179909387) B179909387
theorem B79959727 : Blo 1947435 79959727 := bstep (se 1 (by rfl) ⟨59969795, by rfl⟩ : syracuseStep 79959727 = 119939591) B119939591
theorem B106612969 : Blo 1947435 106612969 := bstep (se 2 (by rfl) ⟨39979863, by rfl⟩ : syracuseStep 106612969 = 79959727) B79959727
theorem B142150625 : Blo 1947435 142150625 := bstep (se 2 (by rfl) ⟨53306484, by rfl⟩ : syracuseStep 142150625 = 106612969) B106612969
theorem B94767083 : Blo 1947435 94767083 := bstep (se 1 (by rfl) ⟨71075312, by rfl⟩ : syracuseStep 94767083 = 142150625) B142150625
theorem B63178055 : Blo 1947435 63178055 := bstep (se 1 (by rfl) ⟨47383541, by rfl⟩ : syracuseStep 63178055 = 94767083) B94767083
theorem B42118703 : Blo 1947435 42118703 := bstep (se 1 (by rfl) ⟨31589027, by rfl⟩ : syracuseStep 42118703 = 63178055) B63178055
theorem B28079135 : Blo 1947435 28079135 := bstep (se 1 (by rfl) ⟨21059351, by rfl⟩ : syracuseStep 28079135 = 42118703) B42118703
theorem B18719423 : Blo 1947435 18719423 := bstep (se 1 (by rfl) ⟨14039567, by rfl⟩ : syracuseStep 18719423 = 28079135) B28079135
theorem B12479615 : Blo 1947435 12479615 := bstep (se 1 (by rfl) ⟨9359711, by rfl⟩ : syracuseStep 12479615 = 18719423) B18719423
theorem B8319743 : Blo 1947435 8319743 := bstep (se 1 (by rfl) ⟨6239807, by rfl⟩ : syracuseStep 8319743 = 12479615) B12479615
theorem B5546495 : Blo 1947435 5546495 := bstep (se 1 (by rfl) ⟨4159871, by rfl⟩ : syracuseStep 5546495 = 8319743) B8319743
theorem B3697663 : Blo 1947435 3697663 := bstep (se 1 (by rfl) ⟨2773247, by rfl⟩ : syracuseStep 3697663 = 5546495) B5546495
theorem B4930217 : Blo 1947435 4930217 := bstep (se 2 (by rfl) ⟨1848831, by rfl⟩ : syracuseStep 4930217 = 3697663) B3697663
theorem B3286811 : Blo 1947435 3286811 := bstep (se 1 (by rfl) ⟨2465108, by rfl⟩ : syracuseStep 3286811 = 4930217) B4930217
theorem B2191207 : Blo 1947435 2191207 := bstep (se 1 (by rfl) ⟨1643405, by rfl⟩ : syracuseStep 2191207 = 3286811) B3286811
theorem B2921609 : Blo 1947435 2921609 := bstep (se 2 (by rfl) ⟨1095603, by rfl⟩ : syracuseStep 2921609 = 2191207) B2191207
theorem B1947739 : Blo 1947435 1947739 := bstep (se 1 (by rfl) ⟨1460804, by rfl⟩ : syracuseStep 1947739 = 2921609) B2921609
theorem B9860453 : Blo 1947435 9860453 := bbase (se 4 (by rfl) ⟨924417, by rfl⟩ : syracuseStep 9860453 = 1848835) (by norm_num)
theorem B6573635 : Blo 1947435 6573635 := bstep (se 1 (by rfl) ⟨4930226, by rfl⟩ : syracuseStep 6573635 = 9860453) B9860453
theorem B4382423 : Blo 1947435 4382423 := bstep (se 1 (by rfl) ⟨3286817, by rfl⟩ : syracuseStep 4382423 = 6573635) B6573635
theorem B2921615 : Blo 1947435 2921615 := bstep (se 1 (by rfl) ⟨2191211, by rfl⟩ : syracuseStep 2921615 = 4382423) B4382423
theorem B1947743 : Blo 1947435 1947743 := bstep (se 1 (by rfl) ⟨1460807, by rfl⟩ : syracuseStep 1947743 = 2921615) B2921615
theorem B2921621 : Blo 1947435 2921621 := bbase (se 6 (by rfl) ⟨68475, by rfl⟩ : syracuseStep 2921621 = 136951) (by norm_num)
theorem B1947747 : Blo 1947435 1947747 := bstep (se 1 (by rfl) ⟨1460810, by rfl⟩ : syracuseStep 1947747 = 2921621) B2921621
theorem B6239845 : Blo 1947435 6239845 := bbase (se 4 (by rfl) ⟨584985, by rfl⟩ : syracuseStep 6239845 = 1169971) (by norm_num)
theorem B8319793 : Blo 1947435 8319793 := bstep (se 2 (by rfl) ⟨3119922, by rfl⟩ : syracuseStep 8319793 = 6239845) B6239845
theorem B11093057 : Blo 1947435 11093057 := bstep (se 2 (by rfl) ⟨4159896, by rfl⟩ : syracuseStep 11093057 = 8319793) B8319793
theorem B7395371 : Blo 1947435 7395371 := bstep (se 1 (by rfl) ⟨5546528, by rfl⟩ : syracuseStep 7395371 = 11093057) B11093057
theorem B4930247 : Blo 1947435 4930247 := bstep (se 1 (by rfl) ⟨3697685, by rfl⟩ : syracuseStep 4930247 = 7395371) B7395371
theorem B3286831 : Blo 1947435 3286831 := bstep (se 1 (by rfl) ⟨2465123, by rfl⟩ : syracuseStep 3286831 = 4930247) B4930247
theorem B4382441 : Blo 1947435 4382441 := bstep (se 2 (by rfl) ⟨1643415, by rfl⟩ : syracuseStep 4382441 = 3286831) B3286831
theorem B2921627 : Blo 1947435 2921627 := bstep (se 1 (by rfl) ⟨2191220, by rfl⟩ : syracuseStep 2921627 = 4382441) B4382441
theorem B1947751 : Blo 1947435 1947751 := bstep (se 1 (by rfl) ⟨1460813, by rfl⟩ : syracuseStep 1947751 = 2921627) B2921627
theorem B2191225 : Blo 1947435 2191225 := bbase (se 2 (by rfl) ⟨821709, by rfl⟩ : syracuseStep 2191225 = 1643419) (by norm_num)
theorem B2921633 : Blo 1947435 2921633 := bstep (se 2 (by rfl) ⟨1095612, by rfl⟩ : syracuseStep 2921633 = 2191225) B2191225
theorem B1947755 : Blo 1947435 1947755 := bstep (se 1 (by rfl) ⟨1460816, by rfl⟩ : syracuseStep 1947755 = 2921633) B2921633
theorem B5336725 : Blo 1947435 5336725 := bbase (se 6 (by rfl) ⟨125079, by rfl⟩ : syracuseStep 5336725 = 250159) (by norm_num)
theorem B7115633 : Blo 1947435 7115633 := bstep (se 2 (by rfl) ⟨2668362, by rfl⟩ : syracuseStep 7115633 = 5336725) B5336725
theorem B4743755 : Blo 1947435 4743755 := bstep (se 1 (by rfl) ⟨3557816, by rfl⟩ : syracuseStep 4743755 = 7115633) B7115633
theorem B3162503 : Blo 1947435 3162503 := bstep (se 1 (by rfl) ⟨2371877, by rfl⟩ : syracuseStep 3162503 = 4743755) B4743755
theorem B8433341 : Blo 1947435 8433341 := bstep (se 3 (by rfl) ⟨1581251, by rfl⟩ : syracuseStep 8433341 = 3162503) B3162503
theorem B5622227 : Blo 1947435 5622227 := bstep (se 1 (by rfl) ⟨4216670, by rfl⟩ : syracuseStep 5622227 = 8433341) B8433341
theorem B3748151 : Blo 1947435 3748151 := bstep (se 1 (by rfl) ⟨2811113, by rfl⟩ : syracuseStep 3748151 = 5622227) B5622227
theorem B9995069 : Blo 1947435 9995069 := bstep (se 3 (by rfl) ⟨1874075, by rfl⟩ : syracuseStep 9995069 = 3748151) B3748151
theorem B6663379 : Blo 1947435 6663379 := bstep (se 1 (by rfl) ⟨4997534, by rfl⟩ : syracuseStep 6663379 = 9995069) B9995069
theorem B8884505 : Blo 1947435 8884505 := bstep (se 2 (by rfl) ⟨3331689, by rfl⟩ : syracuseStep 8884505 = 6663379) B6663379
theorem B23692013 : Blo 1947435 23692013 := bstep (se 3 (by rfl) ⟨4442252, by rfl⟩ : syracuseStep 23692013 = 8884505) B8884505
theorem B15794675 : Blo 1947435 15794675 := bstep (se 1 (by rfl) ⟨11846006, by rfl⟩ : syracuseStep 15794675 = 23692013) B23692013
theorem B10529783 : Blo 1947435 10529783 := bstep (se 1 (by rfl) ⟨7897337, by rfl⟩ : syracuseStep 10529783 = 15794675) B15794675
theorem B7019855 : Blo 1947435 7019855 := bstep (se 1 (by rfl) ⟨5264891, by rfl⟩ : syracuseStep 7019855 = 10529783) B10529783
theorem B4679903 : Blo 1947435 4679903 := bstep (se 1 (by rfl) ⟨3509927, by rfl⟩ : syracuseStep 4679903 = 7019855) B7019855
theorem B12479741 : Blo 1947435 12479741 := bstep (se 3 (by rfl) ⟨2339951, by rfl⟩ : syracuseStep 12479741 = 4679903) B4679903
theorem B8319827 : Blo 1947435 8319827 := bstep (se 1 (by rfl) ⟨6239870, by rfl⟩ : syracuseStep 8319827 = 12479741) B12479741
theorem B5546551 : Blo 1947435 5546551 := bstep (se 1 (by rfl) ⟨4159913, by rfl⟩ : syracuseStep 5546551 = 8319827) B8319827
theorem B7395401 : Blo 1947435 7395401 := bstep (se 2 (by rfl) ⟨2773275, by rfl⟩ : syracuseStep 7395401 = 5546551) B5546551
theorem B4930267 : Blo 1947435 4930267 := bstep (se 1 (by rfl) ⟨3697700, by rfl⟩ : syracuseStep 4930267 = 7395401) B7395401
theorem B6573689 : Blo 1947435 6573689 := bstep (se 2 (by rfl) ⟨2465133, by rfl⟩ : syracuseStep 6573689 = 4930267) B4930267
theorem B4382459 : Blo 1947435 4382459 := bstep (se 1 (by rfl) ⟨3286844, by rfl⟩ : syracuseStep 4382459 = 6573689) B6573689
theorem B2921639 : Blo 1947435 2921639 := bstep (se 1 (by rfl) ⟨2191229, by rfl⟩ : syracuseStep 2921639 = 4382459) B4382459
theorem B1947759 : Blo 1947435 1947759 := bstep (se 1 (by rfl) ⟨1460819, by rfl⟩ : syracuseStep 1947759 = 2921639) B2921639
theorem B2921645 : Blo 1947435 2921645 := bbase (se 3 (by rfl) ⟨547808, by rfl⟩ : syracuseStep 2921645 = 1095617) (by norm_num)
theorem B1947763 : Blo 1947435 1947763 := bstep (se 1 (by rfl) ⟨1460822, by rfl⟩ : syracuseStep 1947763 = 2921645) B2921645
theorem B4382477 : Blo 1947435 4382477 := bbase (se 3 (by rfl) ⟨821714, by rfl⟩ : syracuseStep 4382477 = 1643429) (by norm_num)
theorem B2921651 : Blo 1947435 2921651 := bstep (se 1 (by rfl) ⟨2191238, by rfl⟩ : syracuseStep 2921651 = 4382477) B4382477
theorem B1947767 : Blo 1947435 1947767 := bstep (se 1 (by rfl) ⟨1460825, by rfl⟩ : syracuseStep 1947767 = 2921651) B2921651
theorem B2465149 : Blo 1947435 2465149 := bbase (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) (by norm_num)
theorem B3286865 : Blo 1947435 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B2191243 : Blo 1947435 2191243 := bstep (se 1 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 2191243 = 3286865) B3286865
theorem B2921657 : Blo 1947435 2921657 := bstep (se 2 (by rfl) ⟨1095621, by rfl⟩ : syracuseStep 2921657 = 2191243) B2191243
theorem B1947771 : Blo 1947435 1947771 := bstep (se 1 (by rfl) ⟨1460828, by rfl⟩ : syracuseStep 1947771 = 2921657) B2921657
theorem B4679941 : Blo 1947435 4679941 := bbase (se 4 (by rfl) ⟨438744, by rfl⟩ : syracuseStep 4679941 = 877489) (by norm_num)
theorem B6239921 : Blo 1947435 6239921 := bstep (se 2 (by rfl) ⟨2339970, by rfl⟩ : syracuseStep 6239921 = 4679941) B4679941
theorem B16639789 : Blo 1947435 16639789 := bstep (se 3 (by rfl) ⟨3119960, by rfl⟩ : syracuseStep 16639789 = 6239921) B6239921
theorem B22186385 : Blo 1947435 22186385 := bstep (se 2 (by rfl) ⟨8319894, by rfl⟩ : syracuseStep 22186385 = 16639789) B16639789
theorem B14790923 : Blo 1947435 14790923 := bstep (se 1 (by rfl) ⟨11093192, by rfl⟩ : syracuseStep 14790923 = 22186385) B22186385
theorem B9860615 : Blo 1947435 9860615 := bstep (se 1 (by rfl) ⟨7395461, by rfl⟩ : syracuseStep 9860615 = 14790923) B14790923
theorem B6573743 : Blo 1947435 6573743 := bstep (se 1 (by rfl) ⟨4930307, by rfl⟩ : syracuseStep 6573743 = 9860615) B9860615
theorem B4382495 : Blo 1947435 4382495 := bstep (se 1 (by rfl) ⟨3286871, by rfl⟩ : syracuseStep 4382495 = 6573743) B6573743
theorem B2921663 : Blo 1947435 2921663 := bstep (se 1 (by rfl) ⟨2191247, by rfl⟩ : syracuseStep 2921663 = 4382495) B4382495
theorem B1947775 : Blo 1947435 1947775 := bstep (se 1 (by rfl) ⟨1460831, by rfl⟩ : syracuseStep 1947775 = 2921663) B2921663
theorem B2921669 : Blo 1947435 2921669 := bbase (se 4 (by rfl) ⟨273906, by rfl⟩ : syracuseStep 2921669 = 547813) (by norm_num)
theorem B1947779 : Blo 1947435 1947779 := bstep (se 1 (by rfl) ⟨1460834, by rfl⟩ : syracuseStep 1947779 = 2921669) B2921669
theorem B3286885 : Blo 1947435 3286885 := bbase (se 4 (by rfl) ⟨308145, by rfl⟩ : syracuseStep 3286885 = 616291) (by norm_num)
theorem B4382513 : Blo 1947435 4382513 := bstep (se 2 (by rfl) ⟨1643442, by rfl⟩ : syracuseStep 4382513 = 3286885) B3286885
theorem B2921675 : Blo 1947435 2921675 := bstep (se 1 (by rfl) ⟨2191256, by rfl⟩ : syracuseStep 2921675 = 4382513) B4382513
theorem B1947783 : Blo 1947435 1947783 := bstep (se 1 (by rfl) ⟨1460837, by rfl⟩ : syracuseStep 1947783 = 2921675) B2921675
theorem B2191261 : Blo 1947435 2191261 := bbase (se 3 (by rfl) ⟨410861, by rfl⟩ : syracuseStep 2191261 = 821723) (by norm_num)
theorem B2921681 : Blo 1947435 2921681 := bstep (se 2 (by rfl) ⟨1095630, by rfl⟩ : syracuseStep 2921681 = 2191261) B2191261
theorem B1947787 : Blo 1947435 1947787 := bstep (se 1 (by rfl) ⟨1460840, by rfl⟩ : syracuseStep 1947787 = 2921681) B2921681
theorem B6573797 : Blo 1947435 6573797 := bbase (se 4 (by rfl) ⟨616293, by rfl⟩ : syracuseStep 6573797 = 1232587) (by norm_num)
theorem B4382531 : Blo 1947435 4382531 := bstep (se 1 (by rfl) ⟨3286898, by rfl⟩ : syracuseStep 4382531 = 6573797) B6573797
theorem B2921687 : Blo 1947435 2921687 := bstep (se 1 (by rfl) ⟨2191265, by rfl⟩ : syracuseStep 2921687 = 4382531) B4382531
theorem B1947791 : Blo 1947435 1947791 := bstep (se 1 (by rfl) ⟨1460843, by rfl⟩ : syracuseStep 1947791 = 2921687) B2921687
theorem B2921693 : Blo 1947435 2921693 := bbase (se 3 (by rfl) ⟨547817, by rfl⟩ : syracuseStep 2921693 = 1095635) (by norm_num)
theorem B1947795 : Blo 1947435 1947795 := bstep (se 1 (by rfl) ⟨1460846, by rfl⟩ : syracuseStep 1947795 = 2921693) B2921693
theorem B4382549 : Blo 1947435 4382549 := bbase (se 9 (by rfl) ⟨12839, by rfl⟩ : syracuseStep 4382549 = 25679) (by norm_num)
theorem B2921699 : Blo 1947435 2921699 := bstep (se 1 (by rfl) ⟨2191274, by rfl⟩ : syracuseStep 2921699 = 4382549) B4382549
theorem B1947799 : Blo 1947435 1947799 := bstep (se 1 (by rfl) ⟨1460849, by rfl⟩ : syracuseStep 1947799 = 2921699) B2921699
theorem B5546677 : Blo 1947435 5546677 := bbase (se 5 (by rfl) ⟨260000, by rfl⟩ : syracuseStep 5546677 = 520001) (by norm_num)
theorem B7395569 : Blo 1947435 7395569 := bstep (se 2 (by rfl) ⟨2773338, by rfl⟩ : syracuseStep 7395569 = 5546677) B5546677
theorem B4930379 : Blo 1947435 4930379 := bstep (se 1 (by rfl) ⟨3697784, by rfl⟩ : syracuseStep 4930379 = 7395569) B7395569
theorem B3286919 : Blo 1947435 3286919 := bstep (se 1 (by rfl) ⟨2465189, by rfl⟩ : syracuseStep 3286919 = 4930379) B4930379
theorem B2191279 : Blo 1947435 2191279 := bstep (se 1 (by rfl) ⟨1643459, by rfl⟩ : syracuseStep 2191279 = 3286919) B3286919
theorem B2921705 : Blo 1947435 2921705 := bstep (se 2 (by rfl) ⟨1095639, by rfl⟩ : syracuseStep 2921705 = 2191279) B2191279
theorem B1947803 : Blo 1947435 1947803 := bstep (se 1 (by rfl) ⟨1460852, by rfl⟩ : syracuseStep 1947803 = 2921705) B2921705
theorem B4743869 : Blo 1947435 4743869 := bbase (se 3 (by rfl) ⟨889475, by rfl⟩ : syracuseStep 4743869 = 1778951) (by norm_num)
theorem B50601269 : Blo 1947435 50601269 := bstep (se 5 (by rfl) ⟨2371934, by rfl⟩ : syracuseStep 50601269 = 4743869) B4743869
theorem B33734179 : Blo 1947435 33734179 := bstep (se 1 (by rfl) ⟨25300634, by rfl⟩ : syracuseStep 33734179 = 50601269) B50601269
theorem B44978905 : Blo 1947435 44978905 := bstep (se 2 (by rfl) ⟨16867089, by rfl⟩ : syracuseStep 44978905 = 33734179) B33734179
theorem B59971873 : Blo 1947435 59971873 := bstep (se 2 (by rfl) ⟨22489452, by rfl⟩ : syracuseStep 59971873 = 44978905) B44978905
theorem B79962497 : Blo 1947435 79962497 := bstep (se 2 (by rfl) ⟨29985936, by rfl⟩ : syracuseStep 79962497 = 59971873) B59971873
theorem B53308331 : Blo 1947435 53308331 := bstep (se 1 (by rfl) ⟨39981248, by rfl⟩ : syracuseStep 53308331 = 79962497) B79962497
theorem B35538887 : Blo 1947435 35538887 := bstep (se 1 (by rfl) ⟨26654165, by rfl⟩ : syracuseStep 35538887 = 53308331) B53308331
theorem B23692591 : Blo 1947435 23692591 := bstep (se 1 (by rfl) ⟨17769443, by rfl⟩ : syracuseStep 23692591 = 35538887) B35538887
theorem B126360485 : Blo 1947435 126360485 := bstep (se 4 (by rfl) ⟨11846295, by rfl⟩ : syracuseStep 126360485 = 23692591) B23692591
theorem B84240323 : Blo 1947435 84240323 := bstep (se 1 (by rfl) ⟨63180242, by rfl⟩ : syracuseStep 84240323 = 126360485) B126360485
theorem B56160215 : Blo 1947435 56160215 := bstep (se 1 (by rfl) ⟨42120161, by rfl⟩ : syracuseStep 56160215 = 84240323) B84240323
theorem B37440143 : Blo 1947435 37440143 := bstep (se 1 (by rfl) ⟨28080107, by rfl⟩ : syracuseStep 37440143 = 56160215) B56160215
theorem B24960095 : Blo 1947435 24960095 := bstep (se 1 (by rfl) ⟨18720071, by rfl⟩ : syracuseStep 24960095 = 37440143) B37440143
theorem B16640063 : Blo 1947435 16640063 := bstep (se 1 (by rfl) ⟨12480047, by rfl⟩ : syracuseStep 16640063 = 24960095) B24960095
theorem B11093375 : Blo 1947435 11093375 := bstep (se 1 (by rfl) ⟨8320031, by rfl⟩ : syracuseStep 11093375 = 16640063) B16640063
theorem B7395583 : Blo 1947435 7395583 := bstep (se 1 (by rfl) ⟨5546687, by rfl⟩ : syracuseStep 7395583 = 11093375) B11093375
theorem B9860777 : Blo 1947435 9860777 := bstep (se 2 (by rfl) ⟨3697791, by rfl⟩ : syracuseStep 9860777 = 7395583) B7395583
theorem B6573851 : Blo 1947435 6573851 := bstep (se 1 (by rfl) ⟨4930388, by rfl⟩ : syracuseStep 6573851 = 9860777) B9860777
theorem B4382567 : Blo 1947435 4382567 := bstep (se 1 (by rfl) ⟨3286925, by rfl⟩ : syracuseStep 4382567 = 6573851) B6573851
theorem B2921711 : Blo 1947435 2921711 := bstep (se 1 (by rfl) ⟨2191283, by rfl⟩ : syracuseStep 2921711 = 4382567) B4382567
theorem B1947807 : Blo 1947435 1947807 := bstep (se 1 (by rfl) ⟨1460855, by rfl⟩ : syracuseStep 1947807 = 2921711) B2921711
theorem B2921717 : Blo 1947435 2921717 := bbase (se 5 (by rfl) ⟨136955, by rfl⟩ : syracuseStep 2921717 = 273911) (by norm_num)
theorem B1947811 : Blo 1947435 1947811 := bstep (se 1 (by rfl) ⟨1460858, by rfl⟩ : syracuseStep 1947811 = 2921717) B2921717
theorem B3510029 : Blo 1947435 3510029 := bbase (se 3 (by rfl) ⟨658130, by rfl⟩ : syracuseStep 3510029 = 1316261) (by norm_num)
theorem B2340019 : Blo 1947435 2340019 := bstep (se 1 (by rfl) ⟨1755014, by rfl⟩ : syracuseStep 2340019 = 3510029) B3510029
theorem B12480101 : Blo 1947435 12480101 := bstep (se 4 (by rfl) ⟨1170009, by rfl⟩ : syracuseStep 12480101 = 2340019) B2340019
theorem B8320067 : Blo 1947435 8320067 := bstep (se 1 (by rfl) ⟨6240050, by rfl⟩ : syracuseStep 8320067 = 12480101) B12480101
theorem B5546711 : Blo 1947435 5546711 := bstep (se 1 (by rfl) ⟨4160033, by rfl⟩ : syracuseStep 5546711 = 8320067) B8320067
theorem B3697807 : Blo 1947435 3697807 := bstep (se 1 (by rfl) ⟨2773355, by rfl⟩ : syracuseStep 3697807 = 5546711) B5546711
theorem B4930409 : Blo 1947435 4930409 := bstep (se 2 (by rfl) ⟨1848903, by rfl⟩ : syracuseStep 4930409 = 3697807) B3697807
theorem B3286939 : Blo 1947435 3286939 := bstep (se 1 (by rfl) ⟨2465204, by rfl⟩ : syracuseStep 3286939 = 4930409) B4930409
theorem B4382585 : Blo 1947435 4382585 := bstep (se 2 (by rfl) ⟨1643469, by rfl⟩ : syracuseStep 4382585 = 3286939) B3286939
theorem B2921723 : Blo 1947435 2921723 := bstep (se 1 (by rfl) ⟨2191292, by rfl⟩ : syracuseStep 2921723 = 4382585) B4382585
theorem B1947815 : Blo 1947435 1947815 := bstep (se 1 (by rfl) ⟨1460861, by rfl⟩ : syracuseStep 1947815 = 2921723) B2921723
theorem B2191297 : Blo 1947435 2191297 := bbase (se 2 (by rfl) ⟨821736, by rfl⟩ : syracuseStep 2191297 = 1643473) (by norm_num)
theorem B2921729 : Blo 1947435 2921729 := bstep (se 2 (by rfl) ⟨1095648, by rfl⟩ : syracuseStep 2921729 = 2191297) B2191297
theorem B1947819 : Blo 1947435 1947819 := bstep (se 1 (by rfl) ⟨1460864, by rfl⟩ : syracuseStep 1947819 = 2921729) B2921729
theorem B4930429 : Blo 1947435 4930429 := bbase (se 3 (by rfl) ⟨924455, by rfl⟩ : syracuseStep 4930429 = 1848911) (by norm_num)
theorem B6573905 : Blo 1947435 6573905 := bstep (se 2 (by rfl) ⟨2465214, by rfl⟩ : syracuseStep 6573905 = 4930429) B4930429
theorem B4382603 : Blo 1947435 4382603 := bstep (se 1 (by rfl) ⟨3286952, by rfl⟩ : syracuseStep 4382603 = 6573905) B6573905
theorem B2921735 : Blo 1947435 2921735 := bstep (se 1 (by rfl) ⟨2191301, by rfl⟩ : syracuseStep 2921735 = 4382603) B4382603
theorem B1947823 : Blo 1947435 1947823 := bstep (se 1 (by rfl) ⟨1460867, by rfl⟩ : syracuseStep 1947823 = 2921735) B2921735
theorem B2921741 : Blo 1947435 2921741 := bbase (se 3 (by rfl) ⟨547826, by rfl⟩ : syracuseStep 2921741 = 1095653) (by norm_num)
theorem B1947827 : Blo 1947435 1947827 := bstep (se 1 (by rfl) ⟨1460870, by rfl⟩ : syracuseStep 1947827 = 2921741) B2921741
theorem B4382621 : Blo 1947435 4382621 := bbase (se 3 (by rfl) ⟨821741, by rfl⟩ : syracuseStep 4382621 = 1643483) (by norm_num)
theorem B2921747 : Blo 1947435 2921747 := bstep (se 1 (by rfl) ⟨2191310, by rfl⟩ : syracuseStep 2921747 = 4382621) B4382621
theorem B1947831 : Blo 1947435 1947831 := bstep (se 1 (by rfl) ⟨1460873, by rfl⟩ : syracuseStep 1947831 = 2921747) B2921747
theorem B3286973 : Blo 1947435 3286973 := bbase (se 3 (by rfl) ⟨616307, by rfl⟩ : syracuseStep 3286973 = 1232615) (by norm_num)
theorem B2191315 : Blo 1947435 2191315 := bstep (se 1 (by rfl) ⟨1643486, by rfl⟩ : syracuseStep 2191315 = 3286973) B3286973
theorem B2921753 : Blo 1947435 2921753 := bstep (se 2 (by rfl) ⟨1095657, by rfl⟩ : syracuseStep 2921753 = 2191315) B2191315
theorem B1947835 : Blo 1947435 1947835 := bstep (se 1 (by rfl) ⟨1460876, by rfl⟩ : syracuseStep 1947835 = 2921753) B2921753
theorem B11093557 : Blo 1947435 11093557 := bbase (se 5 (by rfl) ⟨520010, by rfl⟩ : syracuseStep 11093557 = 1040021) (by norm_num)
theorem B14791409 : Blo 1947435 14791409 := bstep (se 2 (by rfl) ⟨5546778, by rfl⟩ : syracuseStep 14791409 = 11093557) B11093557
theorem B9860939 : Blo 1947435 9860939 := bstep (se 1 (by rfl) ⟨7395704, by rfl⟩ : syracuseStep 9860939 = 14791409) B14791409
theorem B6573959 : Blo 1947435 6573959 := bstep (se 1 (by rfl) ⟨4930469, by rfl⟩ : syracuseStep 6573959 = 9860939) B9860939
theorem B4382639 : Blo 1947435 4382639 := bstep (se 1 (by rfl) ⟨3286979, by rfl⟩ : syracuseStep 4382639 = 6573959) B6573959
theorem B2921759 : Blo 1947435 2921759 := bstep (se 1 (by rfl) ⟨2191319, by rfl⟩ : syracuseStep 2921759 = 4382639) B4382639
theorem B1947839 : Blo 1947435 1947839 := bstep (se 1 (by rfl) ⟨1460879, by rfl⟩ : syracuseStep 1947839 = 2921759) B2921759
theorem B2921765 : Blo 1947435 2921765 := bbase (se 4 (by rfl) ⟨273915, by rfl⟩ : syracuseStep 2921765 = 547831) (by norm_num)
theorem B1947843 : Blo 1947435 1947843 := bstep (se 1 (by rfl) ⟨1460882, by rfl⟩ : syracuseStep 1947843 = 2921765) B2921765
theorem B2465245 : Blo 1947435 2465245 := bbase (se 3 (by rfl) ⟨462233, by rfl⟩ : syracuseStep 2465245 = 924467) (by norm_num)
theorem B3286993 : Blo 1947435 3286993 := bstep (se 2 (by rfl) ⟨1232622, by rfl⟩ : syracuseStep 3286993 = 2465245) B2465245
theorem B4382657 : Blo 1947435 4382657 := bstep (se 2 (by rfl) ⟨1643496, by rfl⟩ : syracuseStep 4382657 = 3286993) B3286993
theorem B2921771 : Blo 1947435 2921771 := bstep (se 1 (by rfl) ⟨2191328, by rfl⟩ : syracuseStep 2921771 = 4382657) B4382657
theorem B1947847 : Blo 1947435 1947847 := bstep (se 1 (by rfl) ⟨1460885, by rfl⟩ : syracuseStep 1947847 = 2921771) B2921771
theorem B2191333 : Blo 1947435 2191333 := bbase (se 4 (by rfl) ⟨205437, by rfl⟩ : syracuseStep 2191333 = 410875) (by norm_num)
theorem B2921777 : Blo 1947435 2921777 := bstep (se 2 (by rfl) ⟨1095666, by rfl⟩ : syracuseStep 2921777 = 2191333) B2191333
theorem B1947851 : Blo 1947435 1947851 := bstep (se 1 (by rfl) ⟨1460888, by rfl⟩ : syracuseStep 1947851 = 2921777) B2921777
theorem B3510101 : Blo 1947435 3510101 := bbase (se 9 (by rfl) ⟨10283, by rfl⟩ : syracuseStep 3510101 = 20567) (by norm_num)
theorem B9360269 : Blo 1947435 9360269 := bstep (se 3 (by rfl) ⟨1755050, by rfl⟩ : syracuseStep 9360269 = 3510101) B3510101
theorem B6240179 : Blo 1947435 6240179 := bstep (se 1 (by rfl) ⟨4680134, by rfl⟩ : syracuseStep 6240179 = 9360269) B9360269
theorem B4160119 : Blo 1947435 4160119 := bstep (se 1 (by rfl) ⟨3120089, by rfl⟩ : syracuseStep 4160119 = 6240179) B6240179
theorem B5546825 : Blo 1947435 5546825 := bstep (se 2 (by rfl) ⟨2080059, by rfl⟩ : syracuseStep 5546825 = 4160119) B4160119
theorem B3697883 : Blo 1947435 3697883 := bstep (se 1 (by rfl) ⟨2773412, by rfl⟩ : syracuseStep 3697883 = 5546825) B5546825
theorem B2465255 : Blo 1947435 2465255 := bstep (se 1 (by rfl) ⟨1848941, by rfl⟩ : syracuseStep 2465255 = 3697883) B3697883
theorem B6574013 : Blo 1947435 6574013 := bstep (se 3 (by rfl) ⟨1232627, by rfl⟩ : syracuseStep 6574013 = 2465255) B2465255
theorem B4382675 : Blo 1947435 4382675 := bstep (se 1 (by rfl) ⟨3287006, by rfl⟩ : syracuseStep 4382675 = 6574013) B6574013
theorem B2921783 : Blo 1947435 2921783 := bstep (se 1 (by rfl) ⟨2191337, by rfl⟩ : syracuseStep 2921783 = 4382675) B4382675
theorem B1947855 : Blo 1947435 1947855 := bstep (se 1 (by rfl) ⟨1460891, by rfl⟩ : syracuseStep 1947855 = 2921783) B2921783
theorem B2921789 : Blo 1947435 2921789 := bbase (se 3 (by rfl) ⟨547835, by rfl⟩ : syracuseStep 2921789 = 1095671) (by norm_num)
theorem B1947859 : Blo 1947435 1947859 := bstep (se 1 (by rfl) ⟨1460894, by rfl⟩ : syracuseStep 1947859 = 2921789) B2921789
theorem B4382693 : Blo 1947435 4382693 := bbase (se 4 (by rfl) ⟨410877, by rfl⟩ : syracuseStep 4382693 = 821755) (by norm_num)
theorem B2921795 : Blo 1947435 2921795 := bstep (se 1 (by rfl) ⟨2191346, by rfl⟩ : syracuseStep 2921795 = 4382693) B4382693
theorem B1947863 : Blo 1947435 1947863 := bstep (se 1 (by rfl) ⟨1460897, by rfl⟩ : syracuseStep 1947863 = 2921795) B2921795
theorem B4930541 : Blo 1947435 4930541 := bbase (se 3 (by rfl) ⟨924476, by rfl⟩ : syracuseStep 4930541 = 1848953) (by norm_num)
theorem B3287027 : Blo 1947435 3287027 := bstep (se 1 (by rfl) ⟨2465270, by rfl⟩ : syracuseStep 3287027 = 4930541) B4930541
theorem B2191351 : Blo 1947435 2191351 := bstep (se 1 (by rfl) ⟨1643513, by rfl⟩ : syracuseStep 2191351 = 3287027) B3287027
theorem B2921801 : Blo 1947435 2921801 := bstep (se 2 (by rfl) ⟨1095675, by rfl⟩ : syracuseStep 2921801 = 2191351) B2191351
theorem B1947867 : Blo 1947435 1947867 := bstep (se 1 (by rfl) ⟨1460900, by rfl⟩ : syracuseStep 1947867 = 2921801) B2921801
theorem B4680173 : Blo 1947435 4680173 := bbase (se 3 (by rfl) ⟨877532, by rfl⟩ : syracuseStep 4680173 = 1755065) (by norm_num)
theorem B3120115 : Blo 1947435 3120115 := bstep (se 1 (by rfl) ⟨2340086, by rfl⟩ : syracuseStep 3120115 = 4680173) B4680173
theorem B4160153 : Blo 1947435 4160153 := bstep (se 2 (by rfl) ⟨1560057, by rfl⟩ : syracuseStep 4160153 = 3120115) B3120115
theorem B2773435 : Blo 1947435 2773435 := bstep (se 1 (by rfl) ⟨2080076, by rfl⟩ : syracuseStep 2773435 = 4160153) B4160153
theorem B3697913 : Blo 1947435 3697913 := bstep (se 2 (by rfl) ⟨1386717, by rfl⟩ : syracuseStep 3697913 = 2773435) B2773435
theorem B9861101 : Blo 1947435 9861101 := bstep (se 3 (by rfl) ⟨1848956, by rfl⟩ : syracuseStep 9861101 = 3697913) B3697913
theorem B6574067 : Blo 1947435 6574067 := bstep (se 1 (by rfl) ⟨4930550, by rfl⟩ : syracuseStep 6574067 = 9861101) B9861101
theorem B4382711 : Blo 1947435 4382711 := bstep (se 1 (by rfl) ⟨3287033, by rfl⟩ : syracuseStep 4382711 = 6574067) B6574067
theorem B2921807 : Blo 1947435 2921807 := bstep (se 1 (by rfl) ⟨2191355, by rfl⟩ : syracuseStep 2921807 = 4382711) B4382711
theorem B1947871 : Blo 1947435 1947871 := bstep (se 1 (by rfl) ⟨1460903, by rfl⟩ : syracuseStep 1947871 = 2921807) B2921807
theorem B2921813 : Blo 1947435 2921813 := bbase (se 14 (by rfl) ⟨267, by rfl⟩ : syracuseStep 2921813 = 535) (by norm_num)
theorem B1947875 : Blo 1947435 1947875 := bstep (se 1 (by rfl) ⟨1460906, by rfl⟩ : syracuseStep 1947875 = 2921813) B2921813
theorem B2080085 : Blo 1947435 2080085 := bbase (se 11 (by rfl) ⟨1523, by rfl⟩ : syracuseStep 2080085 = 3047) (by norm_num)
theorem B5546893 : Blo 1947435 5546893 := bstep (se 3 (by rfl) ⟨1040042, by rfl⟩ : syracuseStep 5546893 = 2080085) B2080085
theorem B7395857 : Blo 1947435 7395857 := bstep (se 2 (by rfl) ⟨2773446, by rfl⟩ : syracuseStep 7395857 = 5546893) B5546893
theorem B4930571 : Blo 1947435 4930571 := bstep (se 1 (by rfl) ⟨3697928, by rfl⟩ : syracuseStep 4930571 = 7395857) B7395857
theorem B3287047 : Blo 1947435 3287047 := bstep (se 1 (by rfl) ⟨2465285, by rfl⟩ : syracuseStep 3287047 = 4930571) B4930571
theorem B4382729 : Blo 1947435 4382729 := bstep (se 2 (by rfl) ⟨1643523, by rfl⟩ : syracuseStep 4382729 = 3287047) B3287047
theorem B2921819 : Blo 1947435 2921819 := bstep (se 1 (by rfl) ⟨2191364, by rfl⟩ : syracuseStep 2921819 = 4382729) B4382729
theorem B1947879 : Blo 1947435 1947879 := bstep (se 1 (by rfl) ⟨1460909, by rfl⟩ : syracuseStep 1947879 = 2921819) B2921819
theorem B2191369 : Blo 1947435 2191369 := bbase (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) (by norm_num)
theorem B2921825 : Blo 1947435 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B1947883 : Blo 1947435 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B2567585 : Blo 1947435 2567585 := bbase (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) (by norm_num)
theorem B6846893 : Blo 1947435 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B4564595 : Blo 1947435 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B3043063 : Blo 1947435 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B4057417 : Blo 1947435 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B21639557 : Blo 1947435 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B14426371 : Blo 1947435 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B19235161 : Blo 1947435 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B25646881 : Blo 1947435 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B34195841 : Blo 1947435 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B22797227 : Blo 1947435 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B15198151 : Blo 1947435 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B20264201 : Blo 1947435 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B13509467 : Blo 1947435 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B9006311 : Blo 1947435 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B6004207 : Blo 1947435 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B8005609 : Blo 1947435 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B10674145 : Blo 1947435 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B14232193 : Blo 1947435 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B75905029 : Blo 1947435 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B101206705 : Blo 1947435 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B134942273 : Blo 1947435 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B89961515 : Blo 1947435 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B59974343 : Blo 1947435 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B39982895 : Blo 1947435 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B26655263 : Blo 1947435 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B17770175 : Blo 1947435 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B11846783 : Blo 1947435 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B31591421 : Blo 1947435 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B21060947 : Blo 1947435 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B14040631 : Blo 1947435 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B18720841 : Blo 1947435 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B24961121 : Blo 1947435 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B16640747 : Blo 1947435 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B11093831 : Blo 1947435 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B7395887 : Blo 1947435 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B4930591 : Blo 1947435 4930591 := bstep (se 1 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 4930591 = 7395887) B7395887
theorem B6574121 : Blo 1947435 6574121 := bstep (se 2 (by rfl) ⟨2465295, by rfl⟩ : syracuseStep 6574121 = 4930591) B4930591
theorem B4382747 : Blo 1947435 4382747 := bstep (se 1 (by rfl) ⟨3287060, by rfl⟩ : syracuseStep 4382747 = 6574121) B6574121
theorem B2921831 : Blo 1947435 2921831 := bstep (se 1 (by rfl) ⟨2191373, by rfl⟩ : syracuseStep 2921831 = 4382747) B4382747
theorem B1947887 : Blo 1947435 1947887 := bstep (se 1 (by rfl) ⟨1460915, by rfl⟩ : syracuseStep 1947887 = 2921831) B2921831
theorem B2921837 : Blo 1947435 2921837 := bbase (se 3 (by rfl) ⟨547844, by rfl⟩ : syracuseStep 2921837 = 1095689) (by norm_num)
theorem B1947891 : Blo 1947435 1947891 := bstep (se 1 (by rfl) ⟨1460918, by rfl⟩ : syracuseStep 1947891 = 2921837) B2921837
theorem B4382765 : Blo 1947435 4382765 := bbase (se 3 (by rfl) ⟨821768, by rfl⟩ : syracuseStep 4382765 = 1643537) (by norm_num)
theorem B2921843 : Blo 1947435 2921843 := bstep (se 1 (by rfl) ⟨2191382, by rfl⟩ : syracuseStep 2921843 = 4382765) B4382765
theorem B1947895 : Blo 1947435 1947895 := bstep (se 1 (by rfl) ⟨1460921, by rfl⟩ : syracuseStep 1947895 = 2921843) B2921843
theorem B4442573 : Blo 1947435 4442573 := bbase (se 3 (by rfl) ⟨832982, by rfl⟩ : syracuseStep 4442573 = 1665965) (by norm_num)
theorem B11846861 : Blo 1947435 11846861 := bstep (se 3 (by rfl) ⟨2221286, by rfl⟩ : syracuseStep 11846861 = 4442573) B4442573
theorem B7897907 : Blo 1947435 7897907 := bstep (se 1 (by rfl) ⟨5923430, by rfl⟩ : syracuseStep 7897907 = 11846861) B11846861
theorem B5265271 : Blo 1947435 5265271 := bstep (se 1 (by rfl) ⟨3948953, by rfl⟩ : syracuseStep 5265271 = 7897907) B7897907
theorem B7020361 : Blo 1947435 7020361 := bstep (se 2 (by rfl) ⟨2632635, by rfl⟩ : syracuseStep 7020361 = 5265271) B5265271
theorem B9360481 : Blo 1947435 9360481 := bstep (se 2 (by rfl) ⟨3510180, by rfl⟩ : syracuseStep 9360481 = 7020361) B7020361
theorem B12480641 : Blo 1947435 12480641 := bstep (se 2 (by rfl) ⟨4680240, by rfl⟩ : syracuseStep 12480641 = 9360481) B9360481
theorem B8320427 : Blo 1947435 8320427 := bstep (se 1 (by rfl) ⟨6240320, by rfl⟩ : syracuseStep 8320427 = 12480641) B12480641
theorem B5546951 : Blo 1947435 5546951 := bstep (se 1 (by rfl) ⟨4160213, by rfl⟩ : syracuseStep 5546951 = 8320427) B8320427
theorem B3697967 : Blo 1947435 3697967 := bstep (se 1 (by rfl) ⟨2773475, by rfl⟩ : syracuseStep 3697967 = 5546951) B5546951
theorem B2465311 : Blo 1947435 2465311 := bstep (se 1 (by rfl) ⟨1848983, by rfl⟩ : syracuseStep 2465311 = 3697967) B3697967
theorem B3287081 : Blo 1947435 3287081 := bstep (se 2 (by rfl) ⟨1232655, by rfl⟩ : syracuseStep 3287081 = 2465311) B2465311
theorem B2191387 : Blo 1947435 2191387 := bstep (se 1 (by rfl) ⟨1643540, by rfl⟩ : syracuseStep 2191387 = 3287081) B3287081
theorem B2921849 : Blo 1947435 2921849 := bstep (se 2 (by rfl) ⟨1095693, by rfl⟩ : syracuseStep 2921849 = 2191387) B2191387
theorem B1947899 : Blo 1947435 1947899 := bstep (se 1 (by rfl) ⟨1460924, by rfl⟩ : syracuseStep 1947899 = 2921849) B2921849
theorem B7020373 : Blo 1947435 7020373 := bbase (se 9 (by rfl) ⟨20567, by rfl⟩ : syracuseStep 7020373 = 41135) (by norm_num)
theorem B9360497 : Blo 1947435 9360497 := bstep (se 2 (by rfl) ⟨3510186, by rfl⟩ : syracuseStep 9360497 = 7020373) B7020373
theorem B6240331 : Blo 1947435 6240331 := bstep (se 1 (by rfl) ⟨4680248, by rfl⟩ : syracuseStep 6240331 = 9360497) B9360497
theorem B33281765 : Blo 1947435 33281765 := bstep (se 4 (by rfl) ⟨3120165, by rfl⟩ : syracuseStep 33281765 = 6240331) B6240331
theorem B22187843 : Blo 1947435 22187843 := bstep (se 1 (by rfl) ⟨16640882, by rfl⟩ : syracuseStep 22187843 = 33281765) B33281765
theorem B14791895 : Blo 1947435 14791895 := bstep (se 1 (by rfl) ⟨11093921, by rfl⟩ : syracuseStep 14791895 = 22187843) B22187843
theorem B9861263 : Blo 1947435 9861263 := bstep (se 1 (by rfl) ⟨7395947, by rfl⟩ : syracuseStep 9861263 = 14791895) B14791895
theorem B6574175 : Blo 1947435 6574175 := bstep (se 1 (by rfl) ⟨4930631, by rfl⟩ : syracuseStep 6574175 = 9861263) B9861263
theorem B4382783 : Blo 1947435 4382783 := bstep (se 1 (by rfl) ⟨3287087, by rfl⟩ : syracuseStep 4382783 = 6574175) B6574175
theorem B2921855 : Blo 1947435 2921855 := bstep (se 1 (by rfl) ⟨2191391, by rfl⟩ : syracuseStep 2921855 = 4382783) B4382783
theorem B1947903 : Blo 1947435 1947903 := bstep (se 1 (by rfl) ⟨1460927, by rfl⟩ : syracuseStep 1947903 = 2921855) B2921855
theorem B2921861 : Blo 1947435 2921861 := bbase (se 4 (by rfl) ⟨273924, by rfl⟩ : syracuseStep 2921861 = 547849) (by norm_num)
theorem B1947907 : Blo 1947435 1947907 := bstep (se 1 (by rfl) ⟨1460930, by rfl⟩ : syracuseStep 1947907 = 2921861) B2921861
theorem B3287101 : Blo 1947435 3287101 := bbase (se 3 (by rfl) ⟨616331, by rfl⟩ : syracuseStep 3287101 = 1232663) (by norm_num)
theorem B4382801 : Blo 1947435 4382801 := bstep (se 2 (by rfl) ⟨1643550, by rfl⟩ : syracuseStep 4382801 = 3287101) B3287101
theorem B2921867 : Blo 1947435 2921867 := bstep (se 1 (by rfl) ⟨2191400, by rfl⟩ : syracuseStep 2921867 = 4382801) B4382801
theorem B1947911 : Blo 1947435 1947911 := bstep (se 1 (by rfl) ⟨1460933, by rfl⟩ : syracuseStep 1947911 = 2921867) B2921867
theorem B2191405 : Blo 1947435 2191405 := bbase (se 3 (by rfl) ⟨410888, by rfl⟩ : syracuseStep 2191405 = 821777) (by norm_num)
theorem B2921873 : Blo 1947435 2921873 := bstep (se 2 (by rfl) ⟨1095702, by rfl⟩ : syracuseStep 2921873 = 2191405) B2191405
theorem B1947915 : Blo 1947435 1947915 := bstep (se 1 (by rfl) ⟨1460936, by rfl⟩ : syracuseStep 1947915 = 2921873) B2921873
theorem B6574229 : Blo 1947435 6574229 := bbase (se 6 (by rfl) ⟨154083, by rfl⟩ : syracuseStep 6574229 = 308167) (by norm_num)
theorem B4382819 : Blo 1947435 4382819 := bstep (se 1 (by rfl) ⟨3287114, by rfl⟩ : syracuseStep 4382819 = 6574229) B6574229
theorem B2921879 : Blo 1947435 2921879 := bstep (se 1 (by rfl) ⟨2191409, by rfl⟩ : syracuseStep 2921879 = 4382819) B4382819
theorem B1947919 : Blo 1947435 1947919 := bstep (se 1 (by rfl) ⟨1460939, by rfl⟩ : syracuseStep 1947919 = 2921879) B2921879
theorem B2921885 : Blo 1947435 2921885 := bbase (se 3 (by rfl) ⟨547853, by rfl⟩ : syracuseStep 2921885 = 1095707) (by norm_num)
theorem B1947923 : Blo 1947435 1947923 := bstep (se 1 (by rfl) ⟨1460942, by rfl⟩ : syracuseStep 1947923 = 2921885) B2921885
theorem B4382837 : Blo 1947435 4382837 := bbase (se 5 (by rfl) ⟨205445, by rfl⟩ : syracuseStep 4382837 = 410891) (by norm_num)
theorem B2921891 : Blo 1947435 2921891 := bstep (se 1 (by rfl) ⟨2191418, by rfl⟩ : syracuseStep 2921891 = 4382837) B4382837
theorem B1947927 : Blo 1947435 1947927 := bstep (se 1 (by rfl) ⟨1460945, by rfl⟩ : syracuseStep 1947927 = 2921891) B2921891
theorem B4680317 : Blo 1947435 4680317 := bbase (se 3 (by rfl) ⟨877559, by rfl⟩ : syracuseStep 4680317 = 1755119) (by norm_num)
theorem B3120211 : Blo 1947435 3120211 := bstep (se 1 (by rfl) ⟨2340158, by rfl⟩ : syracuseStep 3120211 = 4680317) B4680317
theorem B16641125 : Blo 1947435 16641125 := bstep (se 4 (by rfl) ⟨1560105, by rfl⟩ : syracuseStep 16641125 = 3120211) B3120211
theorem B11094083 : Blo 1947435 11094083 := bstep (se 1 (by rfl) ⟨8320562, by rfl⟩ : syracuseStep 11094083 = 16641125) B16641125
theorem B7396055 : Blo 1947435 7396055 := bstep (se 1 (by rfl) ⟨5547041, by rfl⟩ : syracuseStep 7396055 = 11094083) B11094083
theorem B4930703 : Blo 1947435 4930703 := bstep (se 1 (by rfl) ⟨3698027, by rfl⟩ : syracuseStep 4930703 = 7396055) B7396055
theorem B3287135 : Blo 1947435 3287135 := bstep (se 1 (by rfl) ⟨2465351, by rfl⟩ : syracuseStep 3287135 = 4930703) B4930703
theorem B2191423 : Blo 1947435 2191423 := bstep (se 1 (by rfl) ⟨1643567, by rfl⟩ : syracuseStep 2191423 = 3287135) B3287135
theorem B2921897 : Blo 1947435 2921897 := bstep (se 2 (by rfl) ⟨1095711, by rfl⟩ : syracuseStep 2921897 = 2191423) B2191423
theorem B1947931 : Blo 1947435 1947931 := bstep (se 1 (by rfl) ⟨1460948, by rfl⟩ : syracuseStep 1947931 = 2921897) B2921897
theorem B7396069 : Blo 1947435 7396069 := bbase (se 4 (by rfl) ⟨693381, by rfl⟩ : syracuseStep 7396069 = 1386763) (by norm_num)
theorem B9861425 : Blo 1947435 9861425 := bstep (se 2 (by rfl) ⟨3698034, by rfl⟩ : syracuseStep 9861425 = 7396069) B7396069
theorem B6574283 : Blo 1947435 6574283 := bstep (se 1 (by rfl) ⟨4930712, by rfl⟩ : syracuseStep 6574283 = 9861425) B9861425
theorem B4382855 : Blo 1947435 4382855 := bstep (se 1 (by rfl) ⟨3287141, by rfl⟩ : syracuseStep 4382855 = 6574283) B6574283
theorem B2921903 : Blo 1947435 2921903 := bstep (se 1 (by rfl) ⟨2191427, by rfl⟩ : syracuseStep 2921903 = 4382855) B4382855
theorem B1947935 : Blo 1947435 1947935 := bstep (se 1 (by rfl) ⟨1460951, by rfl⟩ : syracuseStep 1947935 = 2921903) B2921903
theorem B2921909 : Blo 1947435 2921909 := bbase (se 5 (by rfl) ⟨136964, by rfl⟩ : syracuseStep 2921909 = 273929) (by norm_num)
theorem B1947939 : Blo 1947435 1947939 := bstep (se 1 (by rfl) ⟨1460954, by rfl⟩ : syracuseStep 1947939 = 2921909) B2921909
theorem B4930733 : Blo 1947435 4930733 := bbase (se 3 (by rfl) ⟨924512, by rfl⟩ : syracuseStep 4930733 = 1849025) (by norm_num)
theorem B3287155 : Blo 1947435 3287155 := bstep (se 1 (by rfl) ⟨2465366, by rfl⟩ : syracuseStep 3287155 = 4930733) B4930733
theorem B4382873 : Blo 1947435 4382873 := bstep (se 2 (by rfl) ⟨1643577, by rfl⟩ : syracuseStep 4382873 = 3287155) B3287155
theorem B2921915 : Blo 1947435 2921915 := bstep (se 1 (by rfl) ⟨2191436, by rfl⟩ : syracuseStep 2921915 = 4382873) B4382873
theorem B1947943 : Blo 1947435 1947943 := bstep (se 1 (by rfl) ⟨1460957, by rfl⟩ : syracuseStep 1947943 = 2921915) B2921915
theorem B2191441 : Blo 1947435 2191441 := bbase (se 2 (by rfl) ⟨821790, by rfl⟩ : syracuseStep 2191441 = 1643581) (by norm_num)
theorem B2921921 : Blo 1947435 2921921 := bstep (se 2 (by rfl) ⟨1095720, by rfl⟩ : syracuseStep 2921921 = 2191441) B2191441
theorem B1947947 : Blo 1947435 1947947 := bstep (se 1 (by rfl) ⟨1460960, by rfl⟩ : syracuseStep 1947947 = 2921921) B2921921
theorem B2773549 : Blo 1947435 2773549 := bbase (se 3 (by rfl) ⟨520040, by rfl⟩ : syracuseStep 2773549 = 1040081) (by norm_num)
theorem B3698065 : Blo 1947435 3698065 := bstep (se 2 (by rfl) ⟨1386774, by rfl⟩ : syracuseStep 3698065 = 2773549) B2773549
theorem B4930753 : Blo 1947435 4930753 := bstep (se 2 (by rfl) ⟨1849032, by rfl⟩ : syracuseStep 4930753 = 3698065) B3698065
theorem B6574337 : Blo 1947435 6574337 := bstep (se 2 (by rfl) ⟨2465376, by rfl⟩ : syracuseStep 6574337 = 4930753) B4930753
theorem B4382891 : Blo 1947435 4382891 := bstep (se 1 (by rfl) ⟨3287168, by rfl⟩ : syracuseStep 4382891 = 6574337) B6574337
theorem B2921927 : Blo 1947435 2921927 := bstep (se 1 (by rfl) ⟨2191445, by rfl⟩ : syracuseStep 2921927 = 4382891) B4382891
theorem B1947951 : Blo 1947435 1947951 := bstep (se 1 (by rfl) ⟨1460963, by rfl⟩ : syracuseStep 1947951 = 2921927) B2921927
theorem B2921933 : Blo 1947435 2921933 := bbase (se 3 (by rfl) ⟨547862, by rfl⟩ : syracuseStep 2921933 = 1095725) (by norm_num)
theorem B1947955 : Blo 1947435 1947955 := bstep (se 1 (by rfl) ⟨1460966, by rfl⟩ : syracuseStep 1947955 = 2921933) B2921933
theorem B4382909 : Blo 1947435 4382909 := bbase (se 3 (by rfl) ⟨821795, by rfl⟩ : syracuseStep 4382909 = 1643591) (by norm_num)
theorem B2921939 : Blo 1947435 2921939 := bstep (se 1 (by rfl) ⟨2191454, by rfl⟩ : syracuseStep 2921939 = 4382909) B4382909
theorem B1947959 : Blo 1947435 1947959 := bstep (se 1 (by rfl) ⟨1460969, by rfl⟩ : syracuseStep 1947959 = 2921939) B2921939
theorem B3287189 : Blo 1947435 3287189 := bbase (se 6 (by rfl) ⟨77043, by rfl⟩ : syracuseStep 3287189 = 154087) (by norm_num)
theorem B2191459 : Blo 1947435 2191459 := bstep (se 1 (by rfl) ⟨1643594, by rfl⟩ : syracuseStep 2191459 = 3287189) B3287189
theorem B2921945 : Blo 1947435 2921945 := bstep (se 2 (by rfl) ⟨1095729, by rfl⟩ : syracuseStep 2921945 = 2191459) B2191459
theorem B1947963 : Blo 1947435 1947963 := bstep (se 1 (by rfl) ⟨1460972, by rfl⟩ : syracuseStep 1947963 = 2921945) B2921945
theorem B9360805 : Blo 1947435 9360805 := bbase (se 4 (by rfl) ⟨877575, by rfl⟩ : syracuseStep 9360805 = 1755151) (by norm_num)
theorem B12481073 : Blo 1947435 12481073 := bstep (se 2 (by rfl) ⟨4680402, by rfl⟩ : syracuseStep 12481073 = 9360805) B9360805
theorem B8320715 : Blo 1947435 8320715 := bstep (se 1 (by rfl) ⟨6240536, by rfl⟩ : syracuseStep 8320715 = 12481073) B12481073
theorem B5547143 : Blo 1947435 5547143 := bstep (se 1 (by rfl) ⟨4160357, by rfl⟩ : syracuseStep 5547143 = 8320715) B8320715
theorem B14792381 : Blo 1947435 14792381 := bstep (se 3 (by rfl) ⟨2773571, by rfl⟩ : syracuseStep 14792381 = 5547143) B5547143
theorem B9861587 : Blo 1947435 9861587 := bstep (se 1 (by rfl) ⟨7396190, by rfl⟩ : syracuseStep 9861587 = 14792381) B14792381
theorem B6574391 : Blo 1947435 6574391 := bstep (se 1 (by rfl) ⟨4930793, by rfl⟩ : syracuseStep 6574391 = 9861587) B9861587
theorem B4382927 : Blo 1947435 4382927 := bstep (se 1 (by rfl) ⟨3287195, by rfl⟩ : syracuseStep 4382927 = 6574391) B6574391
theorem B2921951 : Blo 1947435 2921951 := bstep (se 1 (by rfl) ⟨2191463, by rfl⟩ : syracuseStep 2921951 = 4382927) B4382927
theorem B1947967 : Blo 1947435 1947967 := bstep (se 1 (by rfl) ⟨1460975, by rfl⟩ : syracuseStep 1947967 = 2921951) B2921951
theorem B2921957 : Blo 1947435 2921957 := bbase (se 4 (by rfl) ⟨273933, by rfl⟩ : syracuseStep 2921957 = 547867) (by norm_num)
theorem B1947971 : Blo 1947435 1947971 := bstep (se 1 (by rfl) ⟨1460978, by rfl⟩ : syracuseStep 1947971 = 2921957) B2921957
theorem B8434277 : Blo 1947435 8434277 := bbase (se 4 (by rfl) ⟨790713, by rfl⟩ : syracuseStep 8434277 = 1581427) (by norm_num)
theorem B5622851 : Blo 1947435 5622851 := bstep (se 1 (by rfl) ⟨4217138, by rfl⟩ : syracuseStep 5622851 = 8434277) B8434277
theorem B3748567 : Blo 1947435 3748567 := bstep (se 1 (by rfl) ⟨2811425, by rfl⟩ : syracuseStep 3748567 = 5622851) B5622851
theorem B4998089 : Blo 1947435 4998089 := bstep (se 2 (by rfl) ⟨1874283, by rfl⟩ : syracuseStep 4998089 = 3748567) B3748567
theorem B3332059 : Blo 1947435 3332059 := bstep (se 1 (by rfl) ⟨2499044, by rfl⟩ : syracuseStep 3332059 = 4998089) B4998089
theorem B71083925 : Blo 1947435 71083925 := bstep (se 6 (by rfl) ⟨1666029, by rfl⟩ : syracuseStep 71083925 = 3332059) B3332059
theorem B47389283 : Blo 1947435 47389283 := bstep (se 1 (by rfl) ⟨35541962, by rfl⟩ : syracuseStep 47389283 = 71083925) B71083925
theorem B31592855 : Blo 1947435 31592855 := bstep (se 1 (by rfl) ⟨23694641, by rfl⟩ : syracuseStep 31592855 = 47389283) B47389283
theorem B21061903 : Blo 1947435 21061903 := bstep (se 1 (by rfl) ⟨15796427, by rfl⟩ : syracuseStep 21061903 = 31592855) B31592855
theorem B28082537 : Blo 1947435 28082537 := bstep (se 2 (by rfl) ⟨10530951, by rfl⟩ : syracuseStep 28082537 = 21061903) B21061903
theorem B18721691 : Blo 1947435 18721691 := bstep (se 1 (by rfl) ⟨14041268, by rfl⟩ : syracuseStep 18721691 = 28082537) B28082537
theorem B12481127 : Blo 1947435 12481127 := bstep (se 1 (by rfl) ⟨9360845, by rfl⟩ : syracuseStep 12481127 = 18721691) B18721691
theorem B8320751 : Blo 1947435 8320751 := bstep (se 1 (by rfl) ⟨6240563, by rfl⟩ : syracuseStep 8320751 = 12481127) B12481127
theorem B5547167 : Blo 1947435 5547167 := bstep (se 1 (by rfl) ⟨4160375, by rfl⟩ : syracuseStep 5547167 = 8320751) B8320751
theorem B3698111 : Blo 1947435 3698111 := bstep (se 1 (by rfl) ⟨2773583, by rfl⟩ : syracuseStep 3698111 = 5547167) B5547167
theorem B2465407 : Blo 1947435 2465407 := bstep (se 1 (by rfl) ⟨1849055, by rfl⟩ : syracuseStep 2465407 = 3698111) B3698111
theorem B3287209 : Blo 1947435 3287209 := bstep (se 2 (by rfl) ⟨1232703, by rfl⟩ : syracuseStep 3287209 = 2465407) B2465407
theorem B4382945 : Blo 1947435 4382945 := bstep (se 2 (by rfl) ⟨1643604, by rfl⟩ : syracuseStep 4382945 = 3287209) B3287209
theorem B2921963 : Blo 1947435 2921963 := bstep (se 1 (by rfl) ⟨2191472, by rfl⟩ : syracuseStep 2921963 = 4382945) B4382945
theorem B1947975 : Blo 1947435 1947975 := bstep (se 1 (by rfl) ⟨1460981, by rfl⟩ : syracuseStep 1947975 = 2921963) B2921963
theorem B2191477 : Blo 1947435 2191477 := bbase (se 5 (by rfl) ⟨102725, by rfl⟩ : syracuseStep 2191477 = 205451) (by norm_num)
theorem B2921969 : Blo 1947435 2921969 := bstep (se 2 (by rfl) ⟨1095738, by rfl⟩ : syracuseStep 2921969 = 2191477) B2191477
theorem B1947979 : Blo 1947435 1947979 := bstep (se 1 (by rfl) ⟨1460984, by rfl⟩ : syracuseStep 1947979 = 2921969) B2921969
theorem B2465417 : Blo 1947435 2465417 := bbase (se 2 (by rfl) ⟨924531, by rfl⟩ : syracuseStep 2465417 = 1849063) (by norm_num)
theorem B6574445 : Blo 1947435 6574445 := bstep (se 3 (by rfl) ⟨1232708, by rfl⟩ : syracuseStep 6574445 = 2465417) B2465417
theorem B4382963 : Blo 1947435 4382963 := bstep (se 1 (by rfl) ⟨3287222, by rfl⟩ : syracuseStep 4382963 = 6574445) B6574445
theorem B2921975 : Blo 1947435 2921975 := bstep (se 1 (by rfl) ⟨2191481, by rfl⟩ : syracuseStep 2921975 = 4382963) B4382963
theorem B1947983 : Blo 1947435 1947983 := bstep (se 1 (by rfl) ⟨1460987, by rfl⟩ : syracuseStep 1947983 = 2921975) B2921975
theorem B2921981 : Blo 1947435 2921981 := bbase (se 3 (by rfl) ⟨547871, by rfl⟩ : syracuseStep 2921981 = 1095743) (by norm_num)
theorem B1947987 : Blo 1947435 1947987 := bstep (se 1 (by rfl) ⟨1460990, by rfl⟩ : syracuseStep 1947987 = 2921981) B2921981
theorem B4382981 : Blo 1947435 4382981 := bbase (se 4 (by rfl) ⟨410904, by rfl⟩ : syracuseStep 4382981 = 821809) (by norm_num)
theorem B2921987 : Blo 1947435 2921987 := bstep (se 1 (by rfl) ⟨2191490, by rfl⟩ : syracuseStep 2921987 = 4382981) B4382981
theorem B1947991 : Blo 1947435 1947991 := bstep (se 1 (by rfl) ⟨1460993, by rfl⟩ : syracuseStep 1947991 = 2921987) B2921987
theorem B3698149 : Blo 1947435 3698149 := bbase (se 4 (by rfl) ⟨346701, by rfl⟩ : syracuseStep 3698149 = 693403) (by norm_num)
theorem B4930865 : Blo 1947435 4930865 := bstep (se 2 (by rfl) ⟨1849074, by rfl⟩ : syracuseStep 4930865 = 3698149) B3698149
theorem B3287243 : Blo 1947435 3287243 := bstep (se 1 (by rfl) ⟨2465432, by rfl⟩ : syracuseStep 3287243 = 4930865) B4930865
theorem B2191495 : Blo 1947435 2191495 := bstep (se 1 (by rfl) ⟨1643621, by rfl⟩ : syracuseStep 2191495 = 3287243) B3287243
theorem B2921993 : Blo 1947435 2921993 := bstep (se 2 (by rfl) ⟨1095747, by rfl⟩ : syracuseStep 2921993 = 2191495) B2191495
theorem B1947995 : Blo 1947435 1947995 := bstep (se 1 (by rfl) ⟨1460996, by rfl⟩ : syracuseStep 1947995 = 2921993) B2921993
theorem B9861749 : Blo 1947435 9861749 := bbase (se 5 (by rfl) ⟨462269, by rfl⟩ : syracuseStep 9861749 = 924539) (by norm_num)
theorem B6574499 : Blo 1947435 6574499 := bstep (se 1 (by rfl) ⟨4930874, by rfl⟩ : syracuseStep 6574499 = 9861749) B9861749
theorem B4382999 : Blo 1947435 4382999 := bstep (se 1 (by rfl) ⟨3287249, by rfl⟩ : syracuseStep 4382999 = 6574499) B6574499
theorem B2921999 : Blo 1947435 2921999 := bstep (se 1 (by rfl) ⟨2191499, by rfl⟩ : syracuseStep 2921999 = 4382999) B4382999
theorem B1947999 : Blo 1947435 1947999 := bstep (se 1 (by rfl) ⟨1460999, by rfl⟩ : syracuseStep 1947999 = 2921999) B2921999
theorem B2922005 : Blo 1947435 2922005 := bbase (se 6 (by rfl) ⟨68484, by rfl⟩ : syracuseStep 2922005 = 136969) (by norm_num)
theorem B1948003 : Blo 1947435 1948003 := bstep (se 1 (by rfl) ⟨1461002, by rfl⟩ : syracuseStep 1948003 = 2922005) B2922005
theorem B2632781 : Blo 1947435 2632781 := bbase (se 3 (by rfl) ⟨493646, by rfl⟩ : syracuseStep 2632781 = 987293) (by norm_num)
theorem B7020749 : Blo 1947435 7020749 := bstep (se 3 (by rfl) ⟨1316390, by rfl⟩ : syracuseStep 7020749 = 2632781) B2632781
theorem B4680499 : Blo 1947435 4680499 := bstep (se 1 (by rfl) ⟨3510374, by rfl⟩ : syracuseStep 4680499 = 7020749) B7020749
theorem B6240665 : Blo 1947435 6240665 := bstep (se 2 (by rfl) ⟨2340249, by rfl⟩ : syracuseStep 6240665 = 4680499) B4680499
theorem B16641773 : Blo 1947435 16641773 := bstep (se 3 (by rfl) ⟨3120332, by rfl⟩ : syracuseStep 16641773 = 6240665) B6240665
theorem B11094515 : Blo 1947435 11094515 := bstep (se 1 (by rfl) ⟨8320886, by rfl⟩ : syracuseStep 11094515 = 16641773) B16641773
theorem B7396343 : Blo 1947435 7396343 := bstep (se 1 (by rfl) ⟨5547257, by rfl⟩ : syracuseStep 7396343 = 11094515) B11094515
theorem B4930895 : Blo 1947435 4930895 := bstep (se 1 (by rfl) ⟨3698171, by rfl⟩ : syracuseStep 4930895 = 7396343) B7396343
theorem B3287263 : Blo 1947435 3287263 := bstep (se 1 (by rfl) ⟨2465447, by rfl⟩ : syracuseStep 3287263 = 4930895) B4930895
theorem B4383017 : Blo 1947435 4383017 := bstep (se 2 (by rfl) ⟨1643631, by rfl⟩ : syracuseStep 4383017 = 3287263) B3287263
theorem B2922011 : Blo 1947435 2922011 := bstep (se 1 (by rfl) ⟨2191508, by rfl⟩ : syracuseStep 2922011 = 4383017) B4383017
theorem B1948007 : Blo 1947435 1948007 := bstep (se 1 (by rfl) ⟨1461005, by rfl⟩ : syracuseStep 1948007 = 2922011) B2922011
theorem B2191513 : Blo 1947435 2191513 := bbase (se 2 (by rfl) ⟨821817, by rfl⟩ : syracuseStep 2191513 = 1643635) (by norm_num)
theorem B2922017 : Blo 1947435 2922017 := bstep (se 2 (by rfl) ⟨1095756, by rfl⟩ : syracuseStep 2922017 = 2191513) B2191513
theorem B1948011 : Blo 1947435 1948011 := bstep (se 1 (by rfl) ⟨1461008, by rfl⟩ : syracuseStep 1948011 = 2922017) B2922017
theorem B7396373 : Blo 1947435 7396373 := bbase (se 6 (by rfl) ⟨173352, by rfl⟩ : syracuseStep 7396373 = 346705) (by norm_num)
theorem B4930915 : Blo 1947435 4930915 := bstep (se 1 (by rfl) ⟨3698186, by rfl⟩ : syracuseStep 4930915 = 7396373) B7396373
theorem B6574553 : Blo 1947435 6574553 := bstep (se 2 (by rfl) ⟨2465457, by rfl⟩ : syracuseStep 6574553 = 4930915) B4930915
theorem B4383035 : Blo 1947435 4383035 := bstep (se 1 (by rfl) ⟨3287276, by rfl⟩ : syracuseStep 4383035 = 6574553) B6574553
theorem B2922023 : Blo 1947435 2922023 := bstep (se 1 (by rfl) ⟨2191517, by rfl⟩ : syracuseStep 2922023 = 4383035) B4383035
theorem B1948015 : Blo 1947435 1948015 := bstep (se 1 (by rfl) ⟨1461011, by rfl⟩ : syracuseStep 1948015 = 2922023) B2922023
theorem B2922029 : Blo 1947435 2922029 := bbase (se 3 (by rfl) ⟨547880, by rfl⟩ : syracuseStep 2922029 = 1095761) (by norm_num)
theorem B1948019 : Blo 1947435 1948019 := bstep (se 1 (by rfl) ⟨1461014, by rfl⟩ : syracuseStep 1948019 = 2922029) B2922029
theorem B4383053 : Blo 1947435 4383053 := bbase (se 3 (by rfl) ⟨821822, by rfl⟩ : syracuseStep 4383053 = 1643645) (by norm_num)
theorem B2922035 : Blo 1947435 2922035 := bstep (se 1 (by rfl) ⟨2191526, by rfl⟩ : syracuseStep 2922035 = 4383053) B4383053
theorem B1948023 : Blo 1947435 1948023 := bstep (se 1 (by rfl) ⟨1461017, by rfl⟩ : syracuseStep 1948023 = 2922035) B2922035
theorem B2465473 : Blo 1947435 2465473 := bbase (se 2 (by rfl) ⟨924552, by rfl⟩ : syracuseStep 2465473 = 1849105) (by norm_num)
theorem B3287297 : Blo 1947435 3287297 := bstep (se 2 (by rfl) ⟨1232736, by rfl⟩ : syracuseStep 3287297 = 2465473) B2465473
theorem B2191531 : Blo 1947435 2191531 := bstep (se 1 (by rfl) ⟨1643648, by rfl⟩ : syracuseStep 2191531 = 3287297) B3287297
theorem B2922041 : Blo 1947435 2922041 := bstep (se 2 (by rfl) ⟨1095765, by rfl⟩ : syracuseStep 2922041 = 2191531) B2191531
theorem B1948027 : Blo 1947435 1948027 := bstep (se 1 (by rfl) ⟨1461020, by rfl⟩ : syracuseStep 1948027 = 2922041) B2922041
theorem B4680557 : Blo 1947435 4680557 := bbase (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) (by norm_num)
theorem B3120371 : Blo 1947435 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B2080247 : Blo 1947435 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B22189301 : Blo 1947435 22189301 := bstep (se 5 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 22189301 = 2080247) B2080247
theorem B14792867 : Blo 1947435 14792867 := bstep (se 1 (by rfl) ⟨11094650, by rfl⟩ : syracuseStep 14792867 = 22189301) B22189301
theorem B9861911 : Blo 1947435 9861911 := bstep (se 1 (by rfl) ⟨7396433, by rfl⟩ : syracuseStep 9861911 = 14792867) B14792867
theorem B6574607 : Blo 1947435 6574607 := bstep (se 1 (by rfl) ⟨4930955, by rfl⟩ : syracuseStep 6574607 = 9861911) B9861911
theorem B4383071 : Blo 1947435 4383071 := bstep (se 1 (by rfl) ⟨3287303, by rfl⟩ : syracuseStep 4383071 = 6574607) B6574607
theorem B2922047 : Blo 1947435 2922047 := bstep (se 1 (by rfl) ⟨2191535, by rfl⟩ : syracuseStep 2922047 = 4383071) B4383071
theorem B1948031 : Blo 1947435 1948031 := bstep (se 1 (by rfl) ⟨1461023, by rfl⟩ : syracuseStep 1948031 = 2922047) B2922047
theorem B2922053 : Blo 1947435 2922053 := bbase (se 4 (by rfl) ⟨273942, by rfl⟩ : syracuseStep 2922053 = 547885) (by norm_num)
theorem B1948035 : Blo 1947435 1948035 := bstep (se 1 (by rfl) ⟨1461026, by rfl⟩ : syracuseStep 1948035 = 2922053) B2922053
theorem B3287317 : Blo 1947435 3287317 := bbase (se 6 (by rfl) ⟨77046, by rfl⟩ : syracuseStep 3287317 = 154093) (by norm_num)
theorem B4383089 : Blo 1947435 4383089 := bstep (se 2 (by rfl) ⟨1643658, by rfl⟩ : syracuseStep 4383089 = 3287317) B3287317
theorem B2922059 : Blo 1947435 2922059 := bstep (se 1 (by rfl) ⟨2191544, by rfl⟩ : syracuseStep 2922059 = 4383089) B4383089
theorem B1948039 : Blo 1947435 1948039 := bstep (se 1 (by rfl) ⟨1461029, by rfl⟩ : syracuseStep 1948039 = 2922059) B2922059
theorem B2191549 : Blo 1947435 2191549 := bbase (se 3 (by rfl) ⟨410915, by rfl⟩ : syracuseStep 2191549 = 821831) (by norm_num)
theorem B2922065 : Blo 1947435 2922065 := bstep (se 2 (by rfl) ⟨1095774, by rfl⟩ : syracuseStep 2922065 = 2191549) B2191549
theorem B1948043 : Blo 1947435 1948043 := bstep (se 1 (by rfl) ⟨1461032, by rfl⟩ : syracuseStep 1948043 = 2922065) B2922065
theorem B6574661 : Blo 1947435 6574661 := bbase (se 4 (by rfl) ⟨616374, by rfl⟩ : syracuseStep 6574661 = 1232749) (by norm_num)
theorem B4383107 : Blo 1947435 4383107 := bstep (se 1 (by rfl) ⟨3287330, by rfl⟩ : syracuseStep 4383107 = 6574661) B6574661
theorem B2922071 : Blo 1947435 2922071 := bstep (se 1 (by rfl) ⟨2191553, by rfl⟩ : syracuseStep 2922071 = 4383107) B4383107
theorem B1948047 : Blo 1947435 1948047 := bstep (se 1 (by rfl) ⟨1461035, by rfl⟩ : syracuseStep 1948047 = 2922071) B2922071
theorem B2922077 : Blo 1947435 2922077 := bbase (se 3 (by rfl) ⟨547889, by rfl⟩ : syracuseStep 2922077 = 1095779) (by norm_num)
theorem B1948051 : Blo 1947435 1948051 := bstep (se 1 (by rfl) ⟨1461038, by rfl⟩ : syracuseStep 1948051 = 2922077) B2922077
theorem B4383125 : Blo 1947435 4383125 := bbase (se 6 (by rfl) ⟨102729, by rfl⟩ : syracuseStep 4383125 = 205459) (by norm_num)
theorem B2922083 : Blo 1947435 2922083 := bstep (se 1 (by rfl) ⟨2191562, by rfl⟩ : syracuseStep 2922083 = 4383125) B4383125
theorem B1948055 : Blo 1947435 1948055 := bstep (se 1 (by rfl) ⟨1461041, by rfl⟩ : syracuseStep 1948055 = 2922083) B2922083
theorem B3510469 : Blo 1947435 3510469 := bbase (se 4 (by rfl) ⟨329106, by rfl⟩ : syracuseStep 3510469 = 658213) (by norm_num)
theorem B4680625 : Blo 1947435 4680625 := bstep (se 2 (by rfl) ⟨1755234, by rfl⟩ : syracuseStep 4680625 = 3510469) B3510469
theorem B6240833 : Blo 1947435 6240833 := bstep (se 2 (by rfl) ⟨2340312, by rfl⟩ : syracuseStep 6240833 = 4680625) B4680625
theorem B4160555 : Blo 1947435 4160555 := bstep (se 1 (by rfl) ⟨3120416, by rfl⟩ : syracuseStep 4160555 = 6240833) B6240833
theorem B2773703 : Blo 1947435 2773703 := bstep (se 1 (by rfl) ⟨2080277, by rfl⟩ : syracuseStep 2773703 = 4160555) B4160555
theorem B7396541 : Blo 1947435 7396541 := bstep (se 3 (by rfl) ⟨1386851, by rfl⟩ : syracuseStep 7396541 = 2773703) B2773703
theorem B4931027 : Blo 1947435 4931027 := bstep (se 1 (by rfl) ⟨3698270, by rfl⟩ : syracuseStep 4931027 = 7396541) B7396541
theorem B3287351 : Blo 1947435 3287351 := bstep (se 1 (by rfl) ⟨2465513, by rfl⟩ : syracuseStep 3287351 = 4931027) B4931027
theorem B2191567 : Blo 1947435 2191567 := bstep (se 1 (by rfl) ⟨1643675, by rfl⟩ : syracuseStep 2191567 = 3287351) B3287351
theorem B2922089 : Blo 1947435 2922089 := bstep (se 2 (by rfl) ⟨1095783, by rfl⟩ : syracuseStep 2922089 = 2191567) B2191567
theorem B1948059 : Blo 1947435 1948059 := bstep (se 1 (by rfl) ⟨1461044, by rfl⟩ : syracuseStep 1948059 = 2922089) B2922089
theorem B8321125 : Blo 1947435 8321125 := bbase (se 4 (by rfl) ⟨780105, by rfl⟩ : syracuseStep 8321125 = 1560211) (by norm_num)
theorem B11094833 : Blo 1947435 11094833 := bstep (se 2 (by rfl) ⟨4160562, by rfl⟩ : syracuseStep 11094833 = 8321125) B8321125
theorem B7396555 : Blo 1947435 7396555 := bstep (se 1 (by rfl) ⟨5547416, by rfl⟩ : syracuseStep 7396555 = 11094833) B11094833
theorem B9862073 : Blo 1947435 9862073 := bstep (se 2 (by rfl) ⟨3698277, by rfl⟩ : syracuseStep 9862073 = 7396555) B7396555
theorem B6574715 : Blo 1947435 6574715 := bstep (se 1 (by rfl) ⟨4931036, by rfl⟩ : syracuseStep 6574715 = 9862073) B9862073
theorem B4383143 : Blo 1947435 4383143 := bstep (se 1 (by rfl) ⟨3287357, by rfl⟩ : syracuseStep 4383143 = 6574715) B6574715
theorem B2922095 : Blo 1947435 2922095 := bstep (se 1 (by rfl) ⟨2191571, by rfl⟩ : syracuseStep 2922095 = 4383143) B4383143
theorem B1948063 : Blo 1947435 1948063 := bstep (se 1 (by rfl) ⟨1461047, by rfl⟩ : syracuseStep 1948063 = 2922095) B2922095
theorem B2922101 : Blo 1947435 2922101 := bbase (se 5 (by rfl) ⟨136973, by rfl⟩ : syracuseStep 2922101 = 273947) (by norm_num)
theorem B1948067 : Blo 1947435 1948067 := bstep (se 1 (by rfl) ⟨1461050, by rfl⟩ : syracuseStep 1948067 = 2922101) B2922101
theorem B3698293 : Blo 1947435 3698293 := bbase (se 5 (by rfl) ⟨173357, by rfl⟩ : syracuseStep 3698293 = 346715) (by norm_num)
theorem B4931057 : Blo 1947435 4931057 := bstep (se 2 (by rfl) ⟨1849146, by rfl⟩ : syracuseStep 4931057 = 3698293) B3698293
theorem B3287371 : Blo 1947435 3287371 := bstep (se 1 (by rfl) ⟨2465528, by rfl⟩ : syracuseStep 3287371 = 4931057) B4931057
theorem B4383161 : Blo 1947435 4383161 := bstep (se 2 (by rfl) ⟨1643685, by rfl⟩ : syracuseStep 4383161 = 3287371) B3287371
theorem B2922107 : Blo 1947435 2922107 := bstep (se 1 (by rfl) ⟨2191580, by rfl⟩ : syracuseStep 2922107 = 4383161) B4383161
theorem B1948071 : Blo 1947435 1948071 := bstep (se 1 (by rfl) ⟨1461053, by rfl⟩ : syracuseStep 1948071 = 2922107) B2922107
theorem B2191585 : Blo 1947435 2191585 := bbase (se 2 (by rfl) ⟨821844, by rfl⟩ : syracuseStep 2191585 = 1643689) (by norm_num)
theorem B2922113 : Blo 1947435 2922113 := bstep (se 2 (by rfl) ⟨1095792, by rfl⟩ : syracuseStep 2922113 = 2191585) B2191585
theorem B1948075 : Blo 1947435 1948075 := bstep (se 1 (by rfl) ⟨1461056, by rfl⟩ : syracuseStep 1948075 = 2922113) B2922113
theorem B4931077 : Blo 1947435 4931077 := bbase (se 4 (by rfl) ⟨462288, by rfl⟩ : syracuseStep 4931077 = 924577) (by norm_num)
theorem B6574769 : Blo 1947435 6574769 := bstep (se 2 (by rfl) ⟨2465538, by rfl⟩ : syracuseStep 6574769 = 4931077) B4931077
theorem B4383179 : Blo 1947435 4383179 := bstep (se 1 (by rfl) ⟨3287384, by rfl⟩ : syracuseStep 4383179 = 6574769) B6574769
theorem B2922119 : Blo 1947435 2922119 := bstep (se 1 (by rfl) ⟨2191589, by rfl⟩ : syracuseStep 2922119 = 4383179) B4383179
theorem B1948079 : Blo 1947435 1948079 := bstep (se 1 (by rfl) ⟨1461059, by rfl⟩ : syracuseStep 1948079 = 2922119) B2922119
theorem B2922125 : Blo 1947435 2922125 := bbase (se 3 (by rfl) ⟨547898, by rfl⟩ : syracuseStep 2922125 = 1095797) (by norm_num)
theorem B1948083 : Blo 1947435 1948083 := bstep (se 1 (by rfl) ⟨1461062, by rfl⟩ : syracuseStep 1948083 = 2922125) B2922125
theorem B4383197 : Blo 1947435 4383197 := bbase (se 3 (by rfl) ⟨821849, by rfl⟩ : syracuseStep 4383197 = 1643699) (by norm_num)
theorem B2922131 : Blo 1947435 2922131 := bstep (se 1 (by rfl) ⟨2191598, by rfl⟩ : syracuseStep 2922131 = 4383197) B4383197
theorem B1948087 : Blo 1947435 1948087 := bstep (se 1 (by rfl) ⟨1461065, by rfl⟩ : syracuseStep 1948087 = 2922131) B2922131
theorem B3287405 : Blo 1947435 3287405 := bbase (se 3 (by rfl) ⟨616388, by rfl⟩ : syracuseStep 3287405 = 1232777) (by norm_num)
theorem B2191603 : Blo 1947435 2191603 := bstep (se 1 (by rfl) ⟨1643702, by rfl⟩ : syracuseStep 2191603 = 3287405) B3287405
theorem B2922137 : Blo 1947435 2922137 := bstep (se 2 (by rfl) ⟨1095801, by rfl⟩ : syracuseStep 2922137 = 2191603) B2191603
theorem B1948091 : Blo 1947435 1948091 := bstep (se 1 (by rfl) ⟨1461068, by rfl⟩ : syracuseStep 1948091 = 2922137) B2922137
theorem B3949349 : Blo 1947435 3949349 := bbase (se 4 (by rfl) ⟨370251, by rfl⟩ : syracuseStep 3949349 = 740503) (by norm_num)
theorem B42126389 : Blo 1947435 42126389 := bstep (se 5 (by rfl) ⟨1974674, by rfl⟩ : syracuseStep 42126389 = 3949349) B3949349
theorem B28084259 : Blo 1947435 28084259 := bstep (se 1 (by rfl) ⟨21063194, by rfl⟩ : syracuseStep 28084259 = 42126389) B42126389
theorem B18722839 : Blo 1947435 18722839 := bstep (se 1 (by rfl) ⟨14042129, by rfl⟩ : syracuseStep 18722839 = 28084259) B28084259
theorem B24963785 : Blo 1947435 24963785 := bstep (se 2 (by rfl) ⟨9361419, by rfl⟩ : syracuseStep 24963785 = 18722839) B18722839
theorem B16642523 : Blo 1947435 16642523 := bstep (se 1 (by rfl) ⟨12481892, by rfl⟩ : syracuseStep 16642523 = 24963785) B24963785
theorem B11095015 : Blo 1947435 11095015 := bstep (se 1 (by rfl) ⟨8321261, by rfl⟩ : syracuseStep 11095015 = 16642523) B16642523
theorem B14793353 : Blo 1947435 14793353 := bstep (se 2 (by rfl) ⟨5547507, by rfl⟩ : syracuseStep 14793353 = 11095015) B11095015
theorem B9862235 : Blo 1947435 9862235 := bstep (se 1 (by rfl) ⟨7396676, by rfl⟩ : syracuseStep 9862235 = 14793353) B14793353
theorem B6574823 : Blo 1947435 6574823 := bstep (se 1 (by rfl) ⟨4931117, by rfl⟩ : syracuseStep 6574823 = 9862235) B9862235
theorem B4383215 : Blo 1947435 4383215 := bstep (se 1 (by rfl) ⟨3287411, by rfl⟩ : syracuseStep 4383215 = 6574823) B6574823
theorem B2922143 : Blo 1947435 2922143 := bstep (se 1 (by rfl) ⟨2191607, by rfl⟩ : syracuseStep 2922143 = 4383215) B4383215
theorem B1948095 : Blo 1947435 1948095 := bstep (se 1 (by rfl) ⟨1461071, by rfl⟩ : syracuseStep 1948095 = 2922143) B2922143
theorem B2922149 : Blo 1947435 2922149 := bbase (se 4 (by rfl) ⟨273951, by rfl⟩ : syracuseStep 2922149 = 547903) (by norm_num)
theorem B1948099 : Blo 1947435 1948099 := bstep (se 1 (by rfl) ⟨1461074, by rfl⟩ : syracuseStep 1948099 = 2922149) B2922149
theorem B2465569 : Blo 1947435 2465569 := bbase (se 2 (by rfl) ⟨924588, by rfl⟩ : syracuseStep 2465569 = 1849177) (by norm_num)
theorem B3287425 : Blo 1947435 3287425 := bstep (se 2 (by rfl) ⟨1232784, by rfl⟩ : syracuseStep 3287425 = 2465569) B2465569
theorem B4383233 : Blo 1947435 4383233 := bstep (se 2 (by rfl) ⟨1643712, by rfl⟩ : syracuseStep 4383233 = 3287425) B3287425
theorem B2922155 : Blo 1947435 2922155 := bstep (se 1 (by rfl) ⟨2191616, by rfl⟩ : syracuseStep 2922155 = 4383233) B4383233
theorem B1948103 : Blo 1947435 1948103 := bstep (se 1 (by rfl) ⟨1461077, by rfl⟩ : syracuseStep 1948103 = 2922155) B2922155
theorem B2191621 : Blo 1947435 2191621 := bbase (se 4 (by rfl) ⟨205464, by rfl⟩ : syracuseStep 2191621 = 410929) (by norm_num)
theorem B2922161 : Blo 1947435 2922161 := bstep (se 2 (by rfl) ⟨1095810, by rfl⟩ : syracuseStep 2922161 = 2191621) B2191621
theorem B1948107 : Blo 1947435 1948107 := bstep (se 1 (by rfl) ⟨1461080, by rfl⟩ : syracuseStep 1948107 = 2922161) B2922161
theorem B2080333 : Blo 1947435 2080333 := bbase (se 3 (by rfl) ⟨390062, by rfl⟩ : syracuseStep 2080333 = 780125) (by norm_num)
theorem B2773777 : Blo 1947435 2773777 := bstep (se 2 (by rfl) ⟨1040166, by rfl⟩ : syracuseStep 2773777 = 2080333) B2080333
theorem B3698369 : Blo 1947435 3698369 := bstep (se 2 (by rfl) ⟨1386888, by rfl⟩ : syracuseStep 3698369 = 2773777) B2773777
theorem B2465579 : Blo 1947435 2465579 := bstep (se 1 (by rfl) ⟨1849184, by rfl⟩ : syracuseStep 2465579 = 3698369) B3698369
theorem B6574877 : Blo 1947435 6574877 := bstep (se 3 (by rfl) ⟨1232789, by rfl⟩ : syracuseStep 6574877 = 2465579) B2465579
theorem B4383251 : Blo 1947435 4383251 := bstep (se 1 (by rfl) ⟨3287438, by rfl⟩ : syracuseStep 4383251 = 6574877) B6574877
theorem B2922167 : Blo 1947435 2922167 := bstep (se 1 (by rfl) ⟨2191625, by rfl⟩ : syracuseStep 2922167 = 4383251) B4383251
theorem B1948111 : Blo 1947435 1948111 := bstep (se 1 (by rfl) ⟨1461083, by rfl⟩ : syracuseStep 1948111 = 2922167) B2922167
theorem B2922173 : Blo 1947435 2922173 := bbase (se 3 (by rfl) ⟨547907, by rfl⟩ : syracuseStep 2922173 = 1095815) (by norm_num)
theorem B1948115 : Blo 1947435 1948115 := bstep (se 1 (by rfl) ⟨1461086, by rfl⟩ : syracuseStep 1948115 = 2922173) B2922173
theorem B4383269 : Blo 1947435 4383269 := bbase (se 4 (by rfl) ⟨410931, by rfl⟩ : syracuseStep 4383269 = 821863) (by norm_num)
theorem B2922179 : Blo 1947435 2922179 := bstep (se 1 (by rfl) ⟨2191634, by rfl⟩ : syracuseStep 2922179 = 4383269) B4383269
theorem B1948119 : Blo 1947435 1948119 := bstep (se 1 (by rfl) ⟨1461089, by rfl⟩ : syracuseStep 1948119 = 2922179) B2922179
theorem B4931189 : Blo 1947435 4931189 := bbase (se 5 (by rfl) ⟨231149, by rfl⟩ : syracuseStep 4931189 = 462299) (by norm_num)
theorem B3287459 : Blo 1947435 3287459 := bstep (se 1 (by rfl) ⟨2465594, by rfl⟩ : syracuseStep 3287459 = 4931189) B4931189
theorem B2191639 : Blo 1947435 2191639 := bstep (se 1 (by rfl) ⟨1643729, by rfl⟩ : syracuseStep 2191639 = 3287459) B3287459
theorem B2922185 : Blo 1947435 2922185 := bstep (se 2 (by rfl) ⟨1095819, by rfl⟩ : syracuseStep 2922185 = 2191639) B2191639
theorem B1948123 : Blo 1947435 1948123 := bstep (se 1 (by rfl) ⟨1461092, by rfl⟩ : syracuseStep 1948123 = 2922185) B2922185
theorem B6004949 : Blo 1947435 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B16013197 : Blo 1947435 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B85403717 : Blo 1947435 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B56935811 : Blo 1947435 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B37957207 : Blo 1947435 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B50609609 : Blo 1947435 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B33739739 : Blo 1947435 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B22493159 : Blo 1947435 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B14995439 : Blo 1947435 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B9996959 : Blo 1947435 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B6664639 : Blo 1947435 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B8886185 : Blo 1947435 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B5924123 : Blo 1947435 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B3949415 : Blo 1947435 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B2632943 : Blo 1947435 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B7021181 : Blo 1947435 7021181 := bstep (se 3 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 7021181 = 2632943) B2632943
theorem B18723149 : Blo 1947435 18723149 := bstep (se 3 (by rfl) ⟨3510590, by rfl⟩ : syracuseStep 18723149 = 7021181) B7021181
theorem B12482099 : Blo 1947435 12482099 := bstep (se 1 (by rfl) ⟨9361574, by rfl⟩ : syracuseStep 12482099 = 18723149) B18723149
theorem B8321399 : Blo 1947435 8321399 := bstep (se 1 (by rfl) ⟨6241049, by rfl⟩ : syracuseStep 8321399 = 12482099) B12482099
theorem B5547599 : Blo 1947435 5547599 := bstep (se 1 (by rfl) ⟨4160699, by rfl⟩ : syracuseStep 5547599 = 8321399) B8321399
theorem B3698399 : Blo 1947435 3698399 := bstep (se 1 (by rfl) ⟨2773799, by rfl⟩ : syracuseStep 3698399 = 5547599) B5547599
theorem B9862397 : Blo 1947435 9862397 := bstep (se 3 (by rfl) ⟨1849199, by rfl⟩ : syracuseStep 9862397 = 3698399) B3698399
theorem B6574931 : Blo 1947435 6574931 := bstep (se 1 (by rfl) ⟨4931198, by rfl⟩ : syracuseStep 6574931 = 9862397) B9862397
theorem B4383287 : Blo 1947435 4383287 := bstep (se 1 (by rfl) ⟨3287465, by rfl⟩ : syracuseStep 4383287 = 6574931) B6574931
theorem B2922191 : Blo 1947435 2922191 := bstep (se 1 (by rfl) ⟨2191643, by rfl⟩ : syracuseStep 2922191 = 4383287) B4383287
theorem B1948127 : Blo 1947435 1948127 := bstep (se 1 (by rfl) ⟨1461095, by rfl⟩ : syracuseStep 1948127 = 2922191) B2922191
theorem B2922197 : Blo 1947435 2922197 := bbase (se 7 (by rfl) ⟨34244, by rfl⟩ : syracuseStep 2922197 = 68489) (by norm_num)
theorem B1948131 : Blo 1947435 1948131 := bstep (se 1 (by rfl) ⟨1461098, by rfl⟩ : syracuseStep 1948131 = 2922197) B2922197
theorem B4160717 : Blo 1947435 4160717 := bbase (se 3 (by rfl) ⟨780134, by rfl⟩ : syracuseStep 4160717 = 1560269) (by norm_num)
theorem B2773811 : Blo 1947435 2773811 := bstep (se 1 (by rfl) ⟨2080358, by rfl⟩ : syracuseStep 2773811 = 4160717) B4160717
theorem B7396829 : Blo 1947435 7396829 := bstep (se 3 (by rfl) ⟨1386905, by rfl⟩ : syracuseStep 7396829 = 2773811) B2773811
theorem B4931219 : Blo 1947435 4931219 := bstep (se 1 (by rfl) ⟨3698414, by rfl⟩ : syracuseStep 4931219 = 7396829) B7396829
theorem B3287479 : Blo 1947435 3287479 := bstep (se 1 (by rfl) ⟨2465609, by rfl⟩ : syracuseStep 3287479 = 4931219) B4931219
theorem B4383305 : Blo 1947435 4383305 := bstep (se 2 (by rfl) ⟨1643739, by rfl⟩ : syracuseStep 4383305 = 3287479) B3287479
theorem B2922203 : Blo 1947435 2922203 := bstep (se 1 (by rfl) ⟨2191652, by rfl⟩ : syracuseStep 2922203 = 4383305) B4383305
theorem B1948135 : Blo 1947435 1948135 := bstep (se 1 (by rfl) ⟨1461101, by rfl⟩ : syracuseStep 1948135 = 2922203) B2922203
theorem B2191657 : Blo 1947435 2191657 := bbase (se 2 (by rfl) ⟨821871, by rfl⟩ : syracuseStep 2191657 = 1643743) (by norm_num)
theorem B2922209 : Blo 1947435 2922209 := bstep (se 2 (by rfl) ⟨1095828, by rfl⟩ : syracuseStep 2922209 = 2191657) B2191657
theorem B1948139 : Blo 1947435 1948139 := bstep (se 1 (by rfl) ⟨1461104, by rfl⟩ : syracuseStep 1948139 = 2922209) B2922209
theorem B6664693 : Blo 1947435 6664693 := bbase (se 5 (by rfl) ⟨312407, by rfl⟩ : syracuseStep 6664693 = 624815) (by norm_num)
theorem B8886257 : Blo 1947435 8886257 := bstep (se 2 (by rfl) ⟨3332346, by rfl⟩ : syracuseStep 8886257 = 6664693) B6664693
theorem B5924171 : Blo 1947435 5924171 := bstep (se 1 (by rfl) ⟨4443128, by rfl⟩ : syracuseStep 5924171 = 8886257) B8886257
theorem B3949447 : Blo 1947435 3949447 := bstep (se 1 (by rfl) ⟨2962085, by rfl⟩ : syracuseStep 3949447 = 5924171) B5924171
theorem B5265929 : Blo 1947435 5265929 := bstep (se 2 (by rfl) ⟨1974723, by rfl⟩ : syracuseStep 5265929 = 3949447) B3949447
theorem B14042477 : Blo 1947435 14042477 := bstep (se 3 (by rfl) ⟨2632964, by rfl⟩ : syracuseStep 14042477 = 5265929) B5265929
theorem B9361651 : Blo 1947435 9361651 := bstep (se 1 (by rfl) ⟨7021238, by rfl⟩ : syracuseStep 9361651 = 14042477) B14042477
theorem B12482201 : Blo 1947435 12482201 := bstep (se 2 (by rfl) ⟨4680825, by rfl⟩ : syracuseStep 12482201 = 9361651) B9361651
theorem B8321467 : Blo 1947435 8321467 := bstep (se 1 (by rfl) ⟨6241100, by rfl⟩ : syracuseStep 8321467 = 12482201) B12482201
theorem B11095289 : Blo 1947435 11095289 := bstep (se 2 (by rfl) ⟨4160733, by rfl⟩ : syracuseStep 11095289 = 8321467) B8321467
theorem B7396859 : Blo 1947435 7396859 := bstep (se 1 (by rfl) ⟨5547644, by rfl⟩ : syracuseStep 7396859 = 11095289) B11095289
theorem B4931239 : Blo 1947435 4931239 := bstep (se 1 (by rfl) ⟨3698429, by rfl⟩ : syracuseStep 4931239 = 7396859) B7396859
theorem B6574985 : Blo 1947435 6574985 := bstep (se 2 (by rfl) ⟨2465619, by rfl⟩ : syracuseStep 6574985 = 4931239) B4931239
theorem B4383323 : Blo 1947435 4383323 := bstep (se 1 (by rfl) ⟨3287492, by rfl⟩ : syracuseStep 4383323 = 6574985) B6574985
theorem B2922215 : Blo 1947435 2922215 := bstep (se 1 (by rfl) ⟨2191661, by rfl⟩ : syracuseStep 2922215 = 4383323) B4383323
theorem B1948143 : Blo 1947435 1948143 := bstep (se 1 (by rfl) ⟨1461107, by rfl⟩ : syracuseStep 1948143 = 2922215) B2922215
theorem B2922221 : Blo 1947435 2922221 := bbase (se 3 (by rfl) ⟨547916, by rfl⟩ : syracuseStep 2922221 = 1095833) (by norm_num)
theorem B1948147 : Blo 1947435 1948147 := bstep (se 1 (by rfl) ⟨1461110, by rfl⟩ : syracuseStep 1948147 = 2922221) B2922221
theorem B4383341 : Blo 1947435 4383341 := bbase (se 3 (by rfl) ⟨821876, by rfl⟩ : syracuseStep 4383341 = 1643753) (by norm_num)
theorem B2922227 : Blo 1947435 2922227 := bstep (se 1 (by rfl) ⟨2191670, by rfl⟩ : syracuseStep 2922227 = 4383341) B4383341
theorem B1948151 : Blo 1947435 1948151 := bstep (se 1 (by rfl) ⟨1461113, by rfl⟩ : syracuseStep 1948151 = 2922227) B2922227
theorem B3698453 : Blo 1947435 3698453 := bbase (se 6 (by rfl) ⟨86682, by rfl⟩ : syracuseStep 3698453 = 173365) (by norm_num)
theorem B2465635 : Blo 1947435 2465635 := bstep (se 1 (by rfl) ⟨1849226, by rfl⟩ : syracuseStep 2465635 = 3698453) B3698453
theorem B3287513 : Blo 1947435 3287513 := bstep (se 2 (by rfl) ⟨1232817, by rfl⟩ : syracuseStep 3287513 = 2465635) B2465635
theorem B2191675 : Blo 1947435 2191675 := bstep (se 1 (by rfl) ⟨1643756, by rfl⟩ : syracuseStep 2191675 = 3287513) B3287513
theorem B2922233 : Blo 1947435 2922233 := bstep (se 2 (by rfl) ⟨1095837, by rfl⟩ : syracuseStep 2922233 = 2191675) B2191675
theorem B1948155 : Blo 1947435 1948155 := bstep (se 1 (by rfl) ⟨1461116, by rfl⟩ : syracuseStep 1948155 = 2922233) B2922233
theorem B2668909 : Blo 1947435 2668909 := bbase (se 3 (by rfl) ⟨500420, by rfl⟩ : syracuseStep 2668909 = 1000841) (by norm_num)
theorem B3558545 : Blo 1947435 3558545 := bstep (se 2 (by rfl) ⟨1334454, by rfl⟩ : syracuseStep 3558545 = 2668909) B2668909
theorem B2372363 : Blo 1947435 2372363 := bstep (se 1 (by rfl) ⟨1779272, by rfl⟩ : syracuseStep 2372363 = 3558545) B3558545
theorem B25305205 : Blo 1947435 25305205 := bstep (se 5 (by rfl) ⟨1186181, by rfl⟩ : syracuseStep 25305205 = 2372363) B2372363
theorem B33740273 : Blo 1947435 33740273 := bstep (se 2 (by rfl) ⟨12652602, by rfl⟩ : syracuseStep 33740273 = 25305205) B25305205
theorem B89974061 : Blo 1947435 89974061 := bstep (se 3 (by rfl) ⟨16870136, by rfl⟩ : syracuseStep 89974061 = 33740273) B33740273
theorem B59982707 : Blo 1947435 59982707 := bstep (se 1 (by rfl) ⟨44987030, by rfl⟩ : syracuseStep 59982707 = 89974061) B89974061
theorem B159953885 : Blo 1947435 159953885 := bstep (se 3 (by rfl) ⟨29991353, by rfl⟩ : syracuseStep 159953885 = 59982707) B59982707
theorem B106635923 : Blo 1947435 106635923 := bstep (se 1 (by rfl) ⟨79976942, by rfl⟩ : syracuseStep 106635923 = 159953885) B159953885
theorem B71090615 : Blo 1947435 71090615 := bstep (se 1 (by rfl) ⟨53317961, by rfl⟩ : syracuseStep 71090615 = 106635923) B106635923
theorem B47393743 : Blo 1947435 47393743 := bstep (se 1 (by rfl) ⟨35545307, by rfl⟩ : syracuseStep 47393743 = 71090615) B71090615
theorem B63191657 : Blo 1947435 63191657 := bstep (se 2 (by rfl) ⟨23696871, by rfl⟩ : syracuseStep 63191657 = 47393743) B47393743
theorem B42127771 : Blo 1947435 42127771 := bstep (se 1 (by rfl) ⟨31595828, by rfl⟩ : syracuseStep 42127771 = 63191657) B63191657
theorem B56170361 : Blo 1947435 56170361 := bstep (se 2 (by rfl) ⟨21063885, by rfl⟩ : syracuseStep 56170361 = 42127771) B42127771
theorem B37446907 : Blo 1947435 37446907 := bstep (se 1 (by rfl) ⟨28085180, by rfl⟩ : syracuseStep 37446907 = 56170361) B56170361
theorem B49929209 : Blo 1947435 49929209 := bstep (se 2 (by rfl) ⟨18723453, by rfl⟩ : syracuseStep 49929209 = 37446907) B37446907
theorem B33286139 : Blo 1947435 33286139 := bstep (se 1 (by rfl) ⟨24964604, by rfl⟩ : syracuseStep 33286139 = 49929209) B49929209
theorem B22190759 : Blo 1947435 22190759 := bstep (se 1 (by rfl) ⟨16643069, by rfl⟩ : syracuseStep 22190759 = 33286139) B33286139
theorem B14793839 : Blo 1947435 14793839 := bstep (se 1 (by rfl) ⟨11095379, by rfl⟩ : syracuseStep 14793839 = 22190759) B22190759
theorem B9862559 : Blo 1947435 9862559 := bstep (se 1 (by rfl) ⟨7396919, by rfl⟩ : syracuseStep 9862559 = 14793839) B14793839
theorem B6575039 : Blo 1947435 6575039 := bstep (se 1 (by rfl) ⟨4931279, by rfl⟩ : syracuseStep 6575039 = 9862559) B9862559
theorem B4383359 : Blo 1947435 4383359 := bstep (se 1 (by rfl) ⟨3287519, by rfl⟩ : syracuseStep 4383359 = 6575039) B6575039
theorem B2922239 : Blo 1947435 2922239 := bstep (se 1 (by rfl) ⟨2191679, by rfl⟩ : syracuseStep 2922239 = 4383359) B4383359
theorem B1948159 : Blo 1947435 1948159 := bstep (se 1 (by rfl) ⟨1461119, by rfl⟩ : syracuseStep 1948159 = 2922239) B2922239
theorem B2922245 : Blo 1947435 2922245 := bbase (se 4 (by rfl) ⟨273960, by rfl⟩ : syracuseStep 2922245 = 547921) (by norm_num)
theorem B1948163 : Blo 1947435 1948163 := bstep (se 1 (by rfl) ⟨1461122, by rfl⟩ : syracuseStep 1948163 = 2922245) B2922245
theorem B3287533 : Blo 1947435 3287533 := bbase (se 3 (by rfl) ⟨616412, by rfl⟩ : syracuseStep 3287533 = 1232825) (by norm_num)
theorem B4383377 : Blo 1947435 4383377 := bstep (se 2 (by rfl) ⟨1643766, by rfl⟩ : syracuseStep 4383377 = 3287533) B3287533
theorem B2922251 : Blo 1947435 2922251 := bstep (se 1 (by rfl) ⟨2191688, by rfl⟩ : syracuseStep 2922251 = 4383377) B4383377
theorem B1948167 : Blo 1947435 1948167 := bstep (se 1 (by rfl) ⟨1461125, by rfl⟩ : syracuseStep 1948167 = 2922251) B2922251
theorem B2191693 : Blo 1947435 2191693 := bbase (se 3 (by rfl) ⟨410942, by rfl⟩ : syracuseStep 2191693 = 821885) (by norm_num)
theorem B2922257 : Blo 1947435 2922257 := bstep (se 2 (by rfl) ⟨1095846, by rfl⟩ : syracuseStep 2922257 = 2191693) B2191693
theorem B1948171 : Blo 1947435 1948171 := bstep (se 1 (by rfl) ⟨1461128, by rfl⟩ : syracuseStep 1948171 = 2922257) B2922257
theorem B6575093 : Blo 1947435 6575093 := bbase (se 5 (by rfl) ⟨308207, by rfl⟩ : syracuseStep 6575093 = 616415) (by norm_num)
theorem B4383395 : Blo 1947435 4383395 := bstep (se 1 (by rfl) ⟨3287546, by rfl⟩ : syracuseStep 4383395 = 6575093) B6575093
theorem B2922263 : Blo 1947435 2922263 := bstep (se 1 (by rfl) ⟨2191697, by rfl⟩ : syracuseStep 2922263 = 4383395) B4383395
theorem B1948175 : Blo 1947435 1948175 := bstep (se 1 (by rfl) ⟨1461131, by rfl⟩ : syracuseStep 1948175 = 2922263) B2922263
theorem B2922269 : Blo 1947435 2922269 := bbase (se 3 (by rfl) ⟨547925, by rfl⟩ : syracuseStep 2922269 = 1095851) (by norm_num)
theorem B1948179 : Blo 1947435 1948179 := bstep (se 1 (by rfl) ⟨1461134, by rfl⟩ : syracuseStep 1948179 = 2922269) B2922269
theorem B4383413 : Blo 1947435 4383413 := bbase (se 5 (by rfl) ⟨205472, by rfl⟩ : syracuseStep 4383413 = 410945) (by norm_num)
theorem B2922275 : Blo 1947435 2922275 := bstep (se 1 (by rfl) ⟨2191706, by rfl⟩ : syracuseStep 2922275 = 4383413) B4383413
theorem B1948183 : Blo 1947435 1948183 := bstep (se 1 (by rfl) ⟨1461137, by rfl⟩ : syracuseStep 1948183 = 2922275) B2922275
theorem B11095541 : Blo 1947435 11095541 := bbase (se 5 (by rfl) ⟨520103, by rfl⟩ : syracuseStep 11095541 = 1040207) (by norm_num)
theorem B7397027 : Blo 1947435 7397027 := bstep (se 1 (by rfl) ⟨5547770, by rfl⟩ : syracuseStep 7397027 = 11095541) B11095541
theorem B4931351 : Blo 1947435 4931351 := bstep (se 1 (by rfl) ⟨3698513, by rfl⟩ : syracuseStep 4931351 = 7397027) B7397027
theorem B3287567 : Blo 1947435 3287567 := bstep (se 1 (by rfl) ⟨2465675, by rfl⟩ : syracuseStep 3287567 = 4931351) B4931351
theorem B2191711 : Blo 1947435 2191711 := bstep (se 1 (by rfl) ⟨1643783, by rfl⟩ : syracuseStep 2191711 = 3287567) B3287567
theorem B2922281 : Blo 1947435 2922281 := bstep (se 2 (by rfl) ⟨1095855, by rfl⟩ : syracuseStep 2922281 = 2191711) B2191711
theorem B1948187 : Blo 1947435 1948187 := bstep (se 1 (by rfl) ⟨1461140, by rfl⟩ : syracuseStep 1948187 = 2922281) B2922281
theorem B5547781 : Blo 1947435 5547781 := bbase (se 4 (by rfl) ⟨520104, by rfl⟩ : syracuseStep 5547781 = 1040209) (by norm_num)
theorem B7397041 : Blo 1947435 7397041 := bstep (se 2 (by rfl) ⟨2773890, by rfl⟩ : syracuseStep 7397041 = 5547781) B5547781
theorem B9862721 : Blo 1947435 9862721 := bstep (se 2 (by rfl) ⟨3698520, by rfl⟩ : syracuseStep 9862721 = 7397041) B7397041
theorem B6575147 : Blo 1947435 6575147 := bstep (se 1 (by rfl) ⟨4931360, by rfl⟩ : syracuseStep 6575147 = 9862721) B9862721
theorem B4383431 : Blo 1947435 4383431 := bstep (se 1 (by rfl) ⟨3287573, by rfl⟩ : syracuseStep 4383431 = 6575147) B6575147
theorem B2922287 : Blo 1947435 2922287 := bstep (se 1 (by rfl) ⟨2191715, by rfl⟩ : syracuseStep 2922287 = 4383431) B4383431
theorem B1948191 : Blo 1947435 1948191 := bstep (se 1 (by rfl) ⟨1461143, by rfl⟩ : syracuseStep 1948191 = 2922287) B2922287
theorem B2922293 : Blo 1947435 2922293 := bbase (se 5 (by rfl) ⟨136982, by rfl⟩ : syracuseStep 2922293 = 273965) (by norm_num)
theorem B1948195 : Blo 1947435 1948195 := bstep (se 1 (by rfl) ⟨1461146, by rfl⟩ : syracuseStep 1948195 = 2922293) B2922293
theorem B4931381 : Blo 1947435 4931381 := bbase (se 5 (by rfl) ⟨231158, by rfl⟩ : syracuseStep 4931381 = 462317) (by norm_num)
theorem B3287587 : Blo 1947435 3287587 := bstep (se 1 (by rfl) ⟨2465690, by rfl⟩ : syracuseStep 3287587 = 4931381) B4931381
theorem B4383449 : Blo 1947435 4383449 := bstep (se 2 (by rfl) ⟨1643793, by rfl⟩ : syracuseStep 4383449 = 3287587) B3287587
theorem B2922299 : Blo 1947435 2922299 := bstep (se 1 (by rfl) ⟨2191724, by rfl⟩ : syracuseStep 2922299 = 4383449) B4383449
theorem B1948199 : Blo 1947435 1948199 := bstep (se 1 (by rfl) ⟨1461149, by rfl⟩ : syracuseStep 1948199 = 2922299) B2922299
theorem B2191729 : Blo 1947435 2191729 := bbase (se 2 (by rfl) ⟨821898, by rfl⟩ : syracuseStep 2191729 = 1643797) (by norm_num)
theorem B2922305 : Blo 1947435 2922305 := bstep (se 2 (by rfl) ⟨1095864, by rfl⟩ : syracuseStep 2922305 = 2191729) B2191729
theorem B1948203 : Blo 1947435 1948203 := bstep (se 1 (by rfl) ⟨1461152, by rfl⟩ : syracuseStep 1948203 = 2922305) B2922305
theorem B3120653 : Blo 1947435 3120653 := bbase (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) (by norm_num)
theorem B8321741 : Blo 1947435 8321741 := bstep (se 3 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 8321741 = 3120653) B3120653
theorem B5547827 : Blo 1947435 5547827 := bstep (se 1 (by rfl) ⟨4160870, by rfl⟩ : syracuseStep 5547827 = 8321741) B8321741
theorem B3698551 : Blo 1947435 3698551 := bstep (se 1 (by rfl) ⟨2773913, by rfl⟩ : syracuseStep 3698551 = 5547827) B5547827
theorem B4931401 : Blo 1947435 4931401 := bstep (se 2 (by rfl) ⟨1849275, by rfl⟩ : syracuseStep 4931401 = 3698551) B3698551
theorem B6575201 : Blo 1947435 6575201 := bstep (se 2 (by rfl) ⟨2465700, by rfl⟩ : syracuseStep 6575201 = 4931401) B4931401
theorem B4383467 : Blo 1947435 4383467 := bstep (se 1 (by rfl) ⟨3287600, by rfl⟩ : syracuseStep 4383467 = 6575201) B6575201
theorem B2922311 : Blo 1947435 2922311 := bstep (se 1 (by rfl) ⟨2191733, by rfl⟩ : syracuseStep 2922311 = 4383467) B4383467
theorem B1948207 : Blo 1947435 1948207 := bstep (se 1 (by rfl) ⟨1461155, by rfl⟩ : syracuseStep 1948207 = 2922311) B2922311
theorem B2922317 : Blo 1947435 2922317 := bbase (se 3 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 2922317 = 1095869) (by norm_num)
theorem B1948211 : Blo 1947435 1948211 := bstep (se 1 (by rfl) ⟨1461158, by rfl⟩ : syracuseStep 1948211 = 2922317) B2922317
theorem B4383485 : Blo 1947435 4383485 := bbase (se 3 (by rfl) ⟨821903, by rfl⟩ : syracuseStep 4383485 = 1643807) (by norm_num)
theorem B2922323 : Blo 1947435 2922323 := bstep (se 1 (by rfl) ⟨2191742, by rfl⟩ : syracuseStep 2922323 = 4383485) B4383485
theorem B1948215 : Blo 1947435 1948215 := bstep (se 1 (by rfl) ⟨1461161, by rfl⟩ : syracuseStep 1948215 = 2922323) B2922323
theorem B3287621 : Blo 1947435 3287621 := bbase (se 4 (by rfl) ⟨308214, by rfl⟩ : syracuseStep 3287621 = 616429) (by norm_num)
theorem B2191747 : Blo 1947435 2191747 := bstep (se 1 (by rfl) ⟨1643810, by rfl⟩ : syracuseStep 2191747 = 3287621) B3287621
theorem B2922329 : Blo 1947435 2922329 := bstep (se 2 (by rfl) ⟨1095873, by rfl⟩ : syracuseStep 2922329 = 2191747) B2191747
theorem B1948219 : Blo 1947435 1948219 := bstep (se 1 (by rfl) ⟨1461164, by rfl⟩ : syracuseStep 1948219 = 2922329) B2922329
theorem B14794325 : Blo 1947435 14794325 := bbase (se 8 (by rfl) ⟨86685, by rfl⟩ : syracuseStep 14794325 = 173371) (by norm_num)
theorem B9862883 : Blo 1947435 9862883 := bstep (se 1 (by rfl) ⟨7397162, by rfl⟩ : syracuseStep 9862883 = 14794325) B14794325
theorem B6575255 : Blo 1947435 6575255 := bstep (se 1 (by rfl) ⟨4931441, by rfl⟩ : syracuseStep 6575255 = 9862883) B9862883
theorem B4383503 : Blo 1947435 4383503 := bstep (se 1 (by rfl) ⟨3287627, by rfl⟩ : syracuseStep 4383503 = 6575255) B6575255
theorem B2922335 : Blo 1947435 2922335 := bstep (se 1 (by rfl) ⟨2191751, by rfl⟩ : syracuseStep 2922335 = 4383503) B4383503
theorem B1948223 : Blo 1947435 1948223 := bstep (se 1 (by rfl) ⟨1461167, by rfl⟩ : syracuseStep 1948223 = 2922335) B2922335
theorem B2922341 : Blo 1947435 2922341 := bbase (se 4 (by rfl) ⟨273969, by rfl⟩ : syracuseStep 2922341 = 547939) (by norm_num)
theorem B1948227 : Blo 1947435 1948227 := bstep (se 1 (by rfl) ⟨1461170, by rfl⟩ : syracuseStep 1948227 = 2922341) B2922341
theorem B3698597 : Blo 1947435 3698597 := bbase (se 4 (by rfl) ⟨346743, by rfl⟩ : syracuseStep 3698597 = 693487) (by norm_num)
theorem B2465731 : Blo 1947435 2465731 := bstep (se 1 (by rfl) ⟨1849298, by rfl⟩ : syracuseStep 2465731 = 3698597) B3698597
theorem B3287641 : Blo 1947435 3287641 := bstep (se 2 (by rfl) ⟨1232865, by rfl⟩ : syracuseStep 3287641 = 2465731) B2465731
theorem B4383521 : Blo 1947435 4383521 := bstep (se 2 (by rfl) ⟨1643820, by rfl⟩ : syracuseStep 4383521 = 3287641) B3287641
theorem B2922347 : Blo 1947435 2922347 := bstep (se 1 (by rfl) ⟨2191760, by rfl⟩ : syracuseStep 2922347 = 4383521) B4383521
theorem B1948231 : Blo 1947435 1948231 := bstep (se 1 (by rfl) ⟨1461173, by rfl⟩ : syracuseStep 1948231 = 2922347) B2922347
theorem B2191765 : Blo 1947435 2191765 := bbase (se 6 (by rfl) ⟨51369, by rfl⟩ : syracuseStep 2191765 = 102739) (by norm_num)
theorem B2922353 : Blo 1947435 2922353 := bstep (se 2 (by rfl) ⟨1095882, by rfl⟩ : syracuseStep 2922353 = 2191765) B2191765
theorem B1948235 : Blo 1947435 1948235 := bstep (se 1 (by rfl) ⟨1461176, by rfl⟩ : syracuseStep 1948235 = 2922353) B2922353
theorem B2465741 : Blo 1947435 2465741 := bbase (se 3 (by rfl) ⟨462326, by rfl⟩ : syracuseStep 2465741 = 924653) (by norm_num)
theorem B6575309 : Blo 1947435 6575309 := bstep (se 3 (by rfl) ⟨1232870, by rfl⟩ : syracuseStep 6575309 = 2465741) B2465741
theorem B4383539 : Blo 1947435 4383539 := bstep (se 1 (by rfl) ⟨3287654, by rfl⟩ : syracuseStep 4383539 = 6575309) B6575309
theorem B2922359 : Blo 1947435 2922359 := bstep (se 1 (by rfl) ⟨2191769, by rfl⟩ : syracuseStep 2922359 = 4383539) B4383539
theorem B1948239 : Blo 1947435 1948239 := bstep (se 1 (by rfl) ⟨1461179, by rfl⟩ : syracuseStep 1948239 = 2922359) B2922359
theorem B2922365 : Blo 1947435 2922365 := bbase (se 3 (by rfl) ⟨547943, by rfl⟩ : syracuseStep 2922365 = 1095887) (by norm_num)
theorem B1948243 : Blo 1947435 1948243 := bstep (se 1 (by rfl) ⟨1461182, by rfl⟩ : syracuseStep 1948243 = 2922365) B2922365
theorem B4383557 : Blo 1947435 4383557 := bbase (se 4 (by rfl) ⟨410958, by rfl⟩ : syracuseStep 4383557 = 821917) (by norm_num)
theorem B2922371 : Blo 1947435 2922371 := bstep (se 1 (by rfl) ⟨2191778, by rfl⟩ : syracuseStep 2922371 = 4383557) B4383557
theorem B1948247 : Blo 1947435 1948247 := bstep (se 1 (by rfl) ⟨1461185, by rfl⟩ : syracuseStep 1948247 = 2922371) B2922371
theorem B4160965 : Blo 1947435 4160965 := bbase (se 4 (by rfl) ⟨390090, by rfl⟩ : syracuseStep 4160965 = 780181) (by norm_num)
theorem B5547953 : Blo 1947435 5547953 := bstep (se 2 (by rfl) ⟨2080482, by rfl⟩ : syracuseStep 5547953 = 4160965) B4160965
theorem B3698635 : Blo 1947435 3698635 := bstep (se 1 (by rfl) ⟨2773976, by rfl⟩ : syracuseStep 3698635 = 5547953) B5547953
theorem B4931513 : Blo 1947435 4931513 := bstep (se 2 (by rfl) ⟨1849317, by rfl⟩ : syracuseStep 4931513 = 3698635) B3698635
theorem B3287675 : Blo 1947435 3287675 := bstep (se 1 (by rfl) ⟨2465756, by rfl⟩ : syracuseStep 3287675 = 4931513) B4931513
theorem B2191783 : Blo 1947435 2191783 := bstep (se 1 (by rfl) ⟨1643837, by rfl⟩ : syracuseStep 2191783 = 3287675) B3287675
theorem B2922377 : Blo 1947435 2922377 := bstep (se 2 (by rfl) ⟨1095891, by rfl⟩ : syracuseStep 2922377 = 2191783) B2191783
theorem B1948251 : Blo 1947435 1948251 := bstep (se 1 (by rfl) ⟨1461188, by rfl⟩ : syracuseStep 1948251 = 2922377) B2922377
theorem B9863045 : Blo 1947435 9863045 := bbase (se 4 (by rfl) ⟨924660, by rfl⟩ : syracuseStep 9863045 = 1849321) (by norm_num)
theorem B6575363 : Blo 1947435 6575363 := bstep (se 1 (by rfl) ⟨4931522, by rfl⟩ : syracuseStep 6575363 = 9863045) B9863045
theorem B4383575 : Blo 1947435 4383575 := bstep (se 1 (by rfl) ⟨3287681, by rfl⟩ : syracuseStep 4383575 = 6575363) B6575363
theorem B2922383 : Blo 1947435 2922383 := bstep (se 1 (by rfl) ⟨2191787, by rfl⟩ : syracuseStep 2922383 = 4383575) B4383575
theorem B1948255 : Blo 1947435 1948255 := bstep (se 1 (by rfl) ⟨1461191, by rfl⟩ : syracuseStep 1948255 = 2922383) B2922383
theorem B2922389 : Blo 1947435 2922389 := bbase (se 6 (by rfl) ⟨68493, by rfl⟩ : syracuseStep 2922389 = 136987) (by norm_num)
theorem B1948259 : Blo 1947435 1948259 := bstep (se 1 (by rfl) ⟨1461194, by rfl⟩ : syracuseStep 1948259 = 2922389) B2922389
theorem B4998829 : Blo 1947435 4998829 := bbase (se 3 (by rfl) ⟨937280, by rfl⟩ : syracuseStep 4998829 = 1874561) (by norm_num)
theorem B6665105 : Blo 1947435 6665105 := bstep (se 2 (by rfl) ⟨2499414, by rfl⟩ : syracuseStep 6665105 = 4998829) B4998829
theorem B17773613 : Blo 1947435 17773613 := bstep (se 3 (by rfl) ⟨3332552, by rfl⟩ : syracuseStep 17773613 = 6665105) B6665105
theorem B11849075 : Blo 1947435 11849075 := bstep (se 1 (by rfl) ⟨8886806, by rfl⟩ : syracuseStep 11849075 = 17773613) B17773613
theorem B7899383 : Blo 1947435 7899383 := bstep (se 1 (by rfl) ⟨5924537, by rfl⟩ : syracuseStep 7899383 = 11849075) B11849075
theorem B5266255 : Blo 1947435 5266255 := bstep (se 1 (by rfl) ⟨3949691, by rfl⟩ : syracuseStep 5266255 = 7899383) B7899383
theorem B7021673 : Blo 1947435 7021673 := bstep (se 2 (by rfl) ⟨2633127, by rfl⟩ : syracuseStep 7021673 = 5266255) B5266255
theorem B4681115 : Blo 1947435 4681115 := bstep (se 1 (by rfl) ⟨3510836, by rfl⟩ : syracuseStep 4681115 = 7021673) B7021673
theorem B3120743 : Blo 1947435 3120743 := bstep (se 1 (by rfl) ⟨2340557, by rfl⟩ : syracuseStep 3120743 = 4681115) B4681115
theorem B2080495 : Blo 1947435 2080495 := bstep (se 1 (by rfl) ⟨1560371, by rfl⟩ : syracuseStep 2080495 = 3120743) B3120743
theorem B11095973 : Blo 1947435 11095973 := bstep (se 4 (by rfl) ⟨1040247, by rfl⟩ : syracuseStep 11095973 = 2080495) B2080495
theorem B7397315 : Blo 1947435 7397315 := bstep (se 1 (by rfl) ⟨5547986, by rfl⟩ : syracuseStep 7397315 = 11095973) B11095973
theorem B4931543 : Blo 1947435 4931543 := bstep (se 1 (by rfl) ⟨3698657, by rfl⟩ : syracuseStep 4931543 = 7397315) B7397315
theorem B3287695 : Blo 1947435 3287695 := bstep (se 1 (by rfl) ⟨2465771, by rfl⟩ : syracuseStep 3287695 = 4931543) B4931543
theorem B4383593 : Blo 1947435 4383593 := bstep (se 2 (by rfl) ⟨1643847, by rfl⟩ : syracuseStep 4383593 = 3287695) B3287695
theorem B2922395 : Blo 1947435 2922395 := bstep (se 1 (by rfl) ⟨2191796, by rfl⟩ : syracuseStep 2922395 = 4383593) B4383593
theorem B1948263 : Blo 1947435 1948263 := bstep (se 1 (by rfl) ⟨1461197, by rfl⟩ : syracuseStep 1948263 = 2922395) B2922395
theorem B2191801 : Blo 1947435 2191801 := bbase (se 2 (by rfl) ⟨821925, by rfl⟩ : syracuseStep 2191801 = 1643851) (by norm_num)
theorem B2922401 : Blo 1947435 2922401 := bstep (se 2 (by rfl) ⟨1095900, by rfl⟩ : syracuseStep 2922401 = 2191801) B2191801
theorem B1948267 : Blo 1947435 1948267 := bstep (se 1 (by rfl) ⟨1461200, by rfl⟩ : syracuseStep 1948267 = 2922401) B2922401
theorem B13330261 : Blo 1947435 13330261 := bbase (se 9 (by rfl) ⟨39053, by rfl⟩ : syracuseStep 13330261 = 78107) (by norm_num)
theorem B17773681 : Blo 1947435 17773681 := bstep (se 2 (by rfl) ⟨6665130, by rfl⟩ : syracuseStep 17773681 = 13330261) B13330261
theorem B23698241 : Blo 1947435 23698241 := bstep (se 2 (by rfl) ⟨8886840, by rfl⟩ : syracuseStep 23698241 = 17773681) B17773681
theorem B15798827 : Blo 1947435 15798827 := bstep (se 1 (by rfl) ⟨11849120, by rfl⟩ : syracuseStep 15798827 = 23698241) B23698241
theorem B10532551 : Blo 1947435 10532551 := bstep (se 1 (by rfl) ⟨7899413, by rfl⟩ : syracuseStep 10532551 = 15798827) B15798827
theorem B14043401 : Blo 1947435 14043401 := bstep (se 2 (by rfl) ⟨5266275, by rfl⟩ : syracuseStep 14043401 = 10532551) B10532551
theorem B9362267 : Blo 1947435 9362267 := bstep (se 1 (by rfl) ⟨7021700, by rfl⟩ : syracuseStep 9362267 = 14043401) B14043401
theorem B6241511 : Blo 1947435 6241511 := bstep (se 1 (by rfl) ⟨4681133, by rfl⟩ : syracuseStep 6241511 = 9362267) B9362267
theorem B4161007 : Blo 1947435 4161007 := bstep (se 1 (by rfl) ⟨3120755, by rfl⟩ : syracuseStep 4161007 = 6241511) B6241511
theorem B5548009 : Blo 1947435 5548009 := bstep (se 2 (by rfl) ⟨2080503, by rfl⟩ : syracuseStep 5548009 = 4161007) B4161007
theorem B7397345 : Blo 1947435 7397345 := bstep (se 2 (by rfl) ⟨2774004, by rfl⟩ : syracuseStep 7397345 = 5548009) B5548009
theorem B4931563 : Blo 1947435 4931563 := bstep (se 1 (by rfl) ⟨3698672, by rfl⟩ : syracuseStep 4931563 = 7397345) B7397345
theorem B6575417 : Blo 1947435 6575417 := bstep (se 2 (by rfl) ⟨2465781, by rfl⟩ : syracuseStep 6575417 = 4931563) B4931563
theorem B4383611 : Blo 1947435 4383611 := bstep (se 1 (by rfl) ⟨3287708, by rfl⟩ : syracuseStep 4383611 = 6575417) B6575417
theorem B2922407 : Blo 1947435 2922407 := bstep (se 1 (by rfl) ⟨2191805, by rfl⟩ : syracuseStep 2922407 = 4383611) B4383611
theorem B1948271 : Blo 1947435 1948271 := bstep (se 1 (by rfl) ⟨1461203, by rfl⟩ : syracuseStep 1948271 = 2922407) B2922407
theorem B2922413 : Blo 1947435 2922413 := bbase (se 3 (by rfl) ⟨547952, by rfl⟩ : syracuseStep 2922413 = 1095905) (by norm_num)
theorem B1948275 : Blo 1947435 1948275 := bstep (se 1 (by rfl) ⟨1461206, by rfl⟩ : syracuseStep 1948275 = 2922413) B2922413
theorem B4383629 : Blo 1947435 4383629 := bbase (se 3 (by rfl) ⟨821930, by rfl⟩ : syracuseStep 4383629 = 1643861) (by norm_num)
theorem B2922419 : Blo 1947435 2922419 := bstep (se 1 (by rfl) ⟨2191814, by rfl⟩ : syracuseStep 2922419 = 4383629) B4383629
theorem B1948279 : Blo 1947435 1948279 := bstep (se 1 (by rfl) ⟨1461209, by rfl⟩ : syracuseStep 1948279 = 2922419) B2922419
theorem B2465797 : Blo 1947435 2465797 := bbase (se 4 (by rfl) ⟨231168, by rfl⟩ : syracuseStep 2465797 = 462337) (by norm_num)
theorem B3287729 : Blo 1947435 3287729 := bstep (se 2 (by rfl) ⟨1232898, by rfl⟩ : syracuseStep 3287729 = 2465797) B2465797
theorem B2191819 : Blo 1947435 2191819 := bstep (se 1 (by rfl) ⟨1643864, by rfl⟩ : syracuseStep 2191819 = 3287729) B3287729
theorem B2922425 : Blo 1947435 2922425 := bstep (se 2 (by rfl) ⟨1095909, by rfl⟩ : syracuseStep 2922425 = 2191819) B2191819
theorem B1948283 : Blo 1947435 1948283 := bstep (se 1 (by rfl) ⟨1461212, by rfl⟩ : syracuseStep 1948283 = 2922425) B2922425
theorem B2499445 : Blo 1947435 2499445 := bbase (se 5 (by rfl) ⟨117161, by rfl⟩ : syracuseStep 2499445 = 234323) (by norm_num)
theorem B3332593 : Blo 1947435 3332593 := bstep (se 2 (by rfl) ⟨1249722, by rfl⟩ : syracuseStep 3332593 = 2499445) B2499445
theorem B4443457 : Blo 1947435 4443457 := bstep (se 2 (by rfl) ⟨1666296, by rfl⟩ : syracuseStep 4443457 = 3332593) B3332593
theorem B5924609 : Blo 1947435 5924609 := bstep (se 2 (by rfl) ⟨2221728, by rfl⟩ : syracuseStep 5924609 = 4443457) B4443457
theorem B3949739 : Blo 1947435 3949739 := bstep (se 1 (by rfl) ⟨2962304, by rfl⟩ : syracuseStep 3949739 = 5924609) B5924609
theorem B2633159 : Blo 1947435 2633159 := bstep (se 1 (by rfl) ⟨1974869, by rfl⟩ : syracuseStep 2633159 = 3949739) B3949739
theorem B7021757 : Blo 1947435 7021757 := bstep (se 3 (by rfl) ⟨1316579, by rfl⟩ : syracuseStep 7021757 = 2633159) B2633159
theorem B4681171 : Blo 1947435 4681171 := bstep (se 1 (by rfl) ⟨3510878, by rfl⟩ : syracuseStep 4681171 = 7021757) B7021757
theorem B24966245 : Blo 1947435 24966245 := bstep (se 4 (by rfl) ⟨2340585, by rfl⟩ : syracuseStep 24966245 = 4681171) B4681171
theorem B16644163 : Blo 1947435 16644163 := bstep (se 1 (by rfl) ⟨12483122, by rfl⟩ : syracuseStep 16644163 = 24966245) B24966245
theorem B22192217 : Blo 1947435 22192217 := bstep (se 2 (by rfl) ⟨8322081, by rfl⟩ : syracuseStep 22192217 = 16644163) B16644163
theorem B14794811 : Blo 1947435 14794811 := bstep (se 1 (by rfl) ⟨11096108, by rfl⟩ : syracuseStep 14794811 = 22192217) B22192217
theorem B9863207 : Blo 1947435 9863207 := bstep (se 1 (by rfl) ⟨7397405, by rfl⟩ : syracuseStep 9863207 = 14794811) B14794811
theorem B6575471 : Blo 1947435 6575471 := bstep (se 1 (by rfl) ⟨4931603, by rfl⟩ : syracuseStep 6575471 = 9863207) B9863207
theorem B4383647 : Blo 1947435 4383647 := bstep (se 1 (by rfl) ⟨3287735, by rfl⟩ : syracuseStep 4383647 = 6575471) B6575471
theorem B2922431 : Blo 1947435 2922431 := bstep (se 1 (by rfl) ⟨2191823, by rfl⟩ : syracuseStep 2922431 = 4383647) B4383647
theorem B1948287 : Blo 1947435 1948287 := bstep (se 1 (by rfl) ⟨1461215, by rfl⟩ : syracuseStep 1948287 = 2922431) B2922431
theorem B2922437 : Blo 1947435 2922437 := bbase (se 4 (by rfl) ⟨273978, by rfl⟩ : syracuseStep 2922437 = 547957) (by norm_num)
theorem B1948291 : Blo 1947435 1948291 := bstep (se 1 (by rfl) ⟨1461218, by rfl⟩ : syracuseStep 1948291 = 2922437) B2922437
theorem B3287749 : Blo 1947435 3287749 := bbase (se 4 (by rfl) ⟨308226, by rfl⟩ : syracuseStep 3287749 = 616453) (by norm_num)
theorem B4383665 : Blo 1947435 4383665 := bstep (se 2 (by rfl) ⟨1643874, by rfl⟩ : syracuseStep 4383665 = 3287749) B3287749
theorem B2922443 : Blo 1947435 2922443 := bstep (se 1 (by rfl) ⟨2191832, by rfl⟩ : syracuseStep 2922443 = 4383665) B4383665
theorem B1948295 : Blo 1947435 1948295 := bstep (se 1 (by rfl) ⟨1461221, by rfl⟩ : syracuseStep 1948295 = 2922443) B2922443
theorem B2191837 : Blo 1947435 2191837 := bbase (se 3 (by rfl) ⟨410969, by rfl⟩ : syracuseStep 2191837 = 821939) (by norm_num)
theorem B2922449 : Blo 1947435 2922449 := bstep (se 2 (by rfl) ⟨1095918, by rfl⟩ : syracuseStep 2922449 = 2191837) B2191837
theorem B1948299 : Blo 1947435 1948299 := bstep (se 1 (by rfl) ⟨1461224, by rfl⟩ : syracuseStep 1948299 = 2922449) B2922449
theorem B6575525 : Blo 1947435 6575525 := bbase (se 4 (by rfl) ⟨616455, by rfl⟩ : syracuseStep 6575525 = 1232911) (by norm_num)
theorem B4383683 : Blo 1947435 4383683 := bstep (se 1 (by rfl) ⟨3287762, by rfl⟩ : syracuseStep 4383683 = 6575525) B6575525
theorem B2922455 : Blo 1947435 2922455 := bstep (se 1 (by rfl) ⟨2191841, by rfl⟩ : syracuseStep 2922455 = 4383683) B4383683
theorem B1948303 : Blo 1947435 1948303 := bstep (se 1 (by rfl) ⟨1461227, by rfl⟩ : syracuseStep 1948303 = 2922455) B2922455
theorem B2922461 : Blo 1947435 2922461 := bbase (se 3 (by rfl) ⟨547961, by rfl⟩ : syracuseStep 2922461 = 1095923) (by norm_num)
theorem B1948307 : Blo 1947435 1948307 := bstep (se 1 (by rfl) ⟨1461230, by rfl⟩ : syracuseStep 1948307 = 2922461) B2922461
theorem B4383701 : Blo 1947435 4383701 := bbase (se 7 (by rfl) ⟨51371, by rfl⟩ : syracuseStep 4383701 = 102743) (by norm_num)
theorem B2922467 : Blo 1947435 2922467 := bstep (se 1 (by rfl) ⟨2191850, by rfl⟩ : syracuseStep 2922467 = 4383701) B4383701
theorem B1948311 : Blo 1947435 1948311 := bstep (se 1 (by rfl) ⟨1461233, by rfl⟩ : syracuseStep 1948311 = 2922467) B2922467
theorem B3749221 : Blo 1947435 3749221 := bbase (se 4 (by rfl) ⟨351489, by rfl⟩ : syracuseStep 3749221 = 702979) (by norm_num)
theorem B4998961 : Blo 1947435 4998961 := bstep (se 2 (by rfl) ⟨1874610, by rfl⟩ : syracuseStep 4998961 = 3749221) B3749221
theorem B26661125 : Blo 1947435 26661125 := bstep (se 4 (by rfl) ⟨2499480, by rfl⟩ : syracuseStep 26661125 = 4998961) B4998961
theorem B17774083 : Blo 1947435 17774083 := bstep (se 1 (by rfl) ⟨13330562, by rfl⟩ : syracuseStep 17774083 = 26661125) B26661125
theorem B23698777 : Blo 1947435 23698777 := bstep (se 2 (by rfl) ⟨8887041, by rfl⟩ : syracuseStep 23698777 = 17774083) B17774083
theorem B31598369 : Blo 1947435 31598369 := bstep (se 2 (by rfl) ⟨11849388, by rfl⟩ : syracuseStep 31598369 = 23698777) B23698777
theorem B21065579 : Blo 1947435 21065579 := bstep (se 1 (by rfl) ⟨15799184, by rfl⟩ : syracuseStep 21065579 = 31598369) B31598369
theorem B14043719 : Blo 1947435 14043719 := bstep (se 1 (by rfl) ⟨10532789, by rfl⟩ : syracuseStep 14043719 = 21065579) B21065579
theorem B9362479 : Blo 1947435 9362479 := bstep (se 1 (by rfl) ⟨7021859, by rfl⟩ : syracuseStep 9362479 = 14043719) B14043719
theorem B12483305 : Blo 1947435 12483305 := bstep (se 2 (by rfl) ⟨4681239, by rfl⟩ : syracuseStep 12483305 = 9362479) B9362479
theorem B8322203 : Blo 1947435 8322203 := bstep (se 1 (by rfl) ⟨6241652, by rfl⟩ : syracuseStep 8322203 = 12483305) B12483305
theorem B5548135 : Blo 1947435 5548135 := bstep (se 1 (by rfl) ⟨4161101, by rfl⟩ : syracuseStep 5548135 = 8322203) B8322203
theorem B7397513 : Blo 1947435 7397513 := bstep (se 2 (by rfl) ⟨2774067, by rfl⟩ : syracuseStep 7397513 = 5548135) B5548135
theorem B4931675 : Blo 1947435 4931675 := bstep (se 1 (by rfl) ⟨3698756, by rfl⟩ : syracuseStep 4931675 = 7397513) B7397513
theorem B3287783 : Blo 1947435 3287783 := bstep (se 1 (by rfl) ⟨2465837, by rfl⟩ : syracuseStep 3287783 = 4931675) B4931675
theorem B2191855 : Blo 1947435 2191855 := bstep (se 1 (by rfl) ⟨1643891, by rfl⟩ : syracuseStep 2191855 = 3287783) B3287783
theorem B2922473 : Blo 1947435 2922473 := bstep (se 2 (by rfl) ⟨1095927, by rfl⟩ : syracuseStep 2922473 = 2191855) B2191855
theorem B1948315 : Blo 1947435 1948315 := bstep (se 1 (by rfl) ⟨1461236, by rfl⟩ : syracuseStep 1948315 = 2922473) B2922473
theorem B16644437 : Blo 1947435 16644437 := bbase (se 10 (by rfl) ⟨24381, by rfl⟩ : syracuseStep 16644437 = 48763) (by norm_num)
theorem B11096291 : Blo 1947435 11096291 := bstep (se 1 (by rfl) ⟨8322218, by rfl⟩ : syracuseStep 11096291 = 16644437) B16644437
theorem B7397527 : Blo 1947435 7397527 := bstep (se 1 (by rfl) ⟨5548145, by rfl⟩ : syracuseStep 7397527 = 11096291) B11096291
theorem B9863369 : Blo 1947435 9863369 := bstep (se 2 (by rfl) ⟨3698763, by rfl⟩ : syracuseStep 9863369 = 7397527) B7397527
theorem B6575579 : Blo 1947435 6575579 := bstep (se 1 (by rfl) ⟨4931684, by rfl⟩ : syracuseStep 6575579 = 9863369) B9863369
theorem B4383719 : Blo 1947435 4383719 := bstep (se 1 (by rfl) ⟨3287789, by rfl⟩ : syracuseStep 4383719 = 6575579) B6575579
theorem B2922479 : Blo 1947435 2922479 := bstep (se 1 (by rfl) ⟨2191859, by rfl⟩ : syracuseStep 2922479 = 4383719) B4383719
theorem B1948319 : Blo 1947435 1948319 := bstep (se 1 (by rfl) ⟨1461239, by rfl⟩ : syracuseStep 1948319 = 2922479) B2922479
theorem B2922485 : Blo 1947435 2922485 := bbase (se 5 (by rfl) ⟨136991, by rfl⟩ : syracuseStep 2922485 = 273983) (by norm_num)
theorem B1948323 : Blo 1947435 1948323 := bstep (se 1 (by rfl) ⟨1461242, by rfl⟩ : syracuseStep 1948323 = 2922485) B2922485
theorem B9490277 : Blo 1947435 9490277 := bbase (se 4 (by rfl) ⟨889713, by rfl⟩ : syracuseStep 9490277 = 1779427) (by norm_num)
theorem B6326851 : Blo 1947435 6326851 := bstep (se 1 (by rfl) ⟨4745138, by rfl⟩ : syracuseStep 6326851 = 9490277) B9490277
theorem B8435801 : Blo 1947435 8435801 := bstep (se 2 (by rfl) ⟨3163425, by rfl⟩ : syracuseStep 8435801 = 6326851) B6326851
theorem B5623867 : Blo 1947435 5623867 := bstep (se 1 (by rfl) ⟨4217900, by rfl⟩ : syracuseStep 5623867 = 8435801) B8435801
theorem B7498489 : Blo 1947435 7498489 := bstep (se 2 (by rfl) ⟨2811933, by rfl⟩ : syracuseStep 7498489 = 5623867) B5623867
theorem B9997985 : Blo 1947435 9997985 := bstep (se 2 (by rfl) ⟨3749244, by rfl⟩ : syracuseStep 9997985 = 7498489) B7498489
theorem B6665323 : Blo 1947435 6665323 := bstep (se 1 (by rfl) ⟨4998992, by rfl⟩ : syracuseStep 6665323 = 9997985) B9997985
theorem B8887097 : Blo 1947435 8887097 := bstep (se 2 (by rfl) ⟨3332661, by rfl⟩ : syracuseStep 8887097 = 6665323) B6665323
theorem B23698925 : Blo 1947435 23698925 := bstep (se 3 (by rfl) ⟨4443548, by rfl⟩ : syracuseStep 23698925 = 8887097) B8887097
theorem B15799283 : Blo 1947435 15799283 := bstep (se 1 (by rfl) ⟨11849462, by rfl⟩ : syracuseStep 15799283 = 23698925) B23698925
theorem B10532855 : Blo 1947435 10532855 := bstep (se 1 (by rfl) ⟨7899641, by rfl⟩ : syracuseStep 10532855 = 15799283) B15799283
theorem B7021903 : Blo 1947435 7021903 := bstep (se 1 (by rfl) ⟨5266427, by rfl⟩ : syracuseStep 7021903 = 10532855) B10532855
theorem B9362537 : Blo 1947435 9362537 := bstep (se 2 (by rfl) ⟨3510951, by rfl⟩ : syracuseStep 9362537 = 7021903) B7021903
theorem B6241691 : Blo 1947435 6241691 := bstep (se 1 (by rfl) ⟨4681268, by rfl⟩ : syracuseStep 6241691 = 9362537) B9362537
theorem B4161127 : Blo 1947435 4161127 := bstep (se 1 (by rfl) ⟨3120845, by rfl⟩ : syracuseStep 4161127 = 6241691) B6241691
theorem B5548169 : Blo 1947435 5548169 := bstep (se 2 (by rfl) ⟨2080563, by rfl⟩ : syracuseStep 5548169 = 4161127) B4161127
theorem B3698779 : Blo 1947435 3698779 := bstep (se 1 (by rfl) ⟨2774084, by rfl⟩ : syracuseStep 3698779 = 5548169) B5548169
theorem B4931705 : Blo 1947435 4931705 := bstep (se 2 (by rfl) ⟨1849389, by rfl⟩ : syracuseStep 4931705 = 3698779) B3698779
theorem B3287803 : Blo 1947435 3287803 := bstep (se 1 (by rfl) ⟨2465852, by rfl⟩ : syracuseStep 3287803 = 4931705) B4931705
theorem B4383737 : Blo 1947435 4383737 := bstep (se 2 (by rfl) ⟨1643901, by rfl⟩ : syracuseStep 4383737 = 3287803) B3287803
theorem B2922491 : Blo 1947435 2922491 := bstep (se 1 (by rfl) ⟨2191868, by rfl⟩ : syracuseStep 2922491 = 4383737) B4383737
theorem B1948327 : Blo 1947435 1948327 := bstep (se 1 (by rfl) ⟨1461245, by rfl⟩ : syracuseStep 1948327 = 2922491) B2922491
theorem B2191873 : Blo 1947435 2191873 := bbase (se 2 (by rfl) ⟨821952, by rfl⟩ : syracuseStep 2191873 = 1643905) (by norm_num)
theorem B2922497 : Blo 1947435 2922497 := bstep (se 2 (by rfl) ⟨1095936, by rfl⟩ : syracuseStep 2922497 = 2191873) B2191873
theorem B1948331 : Blo 1947435 1948331 := bstep (se 1 (by rfl) ⟨1461248, by rfl⟩ : syracuseStep 1948331 = 2922497) B2922497
theorem B4931725 : Blo 1947435 4931725 := bbase (se 3 (by rfl) ⟨924698, by rfl⟩ : syracuseStep 4931725 = 1849397) (by norm_num)
theorem B6575633 : Blo 1947435 6575633 := bstep (se 2 (by rfl) ⟨2465862, by rfl⟩ : syracuseStep 6575633 = 4931725) B4931725
theorem B4383755 : Blo 1947435 4383755 := bstep (se 1 (by rfl) ⟨3287816, by rfl⟩ : syracuseStep 4383755 = 6575633) B6575633
theorem B2922503 : Blo 1947435 2922503 := bstep (se 1 (by rfl) ⟨2191877, by rfl⟩ : syracuseStep 2922503 = 4383755) B4383755
theorem B1948335 : Blo 1947435 1948335 := bstep (se 1 (by rfl) ⟨1461251, by rfl⟩ : syracuseStep 1948335 = 2922503) B2922503
theorem B2922509 : Blo 1947435 2922509 := bbase (se 3 (by rfl) ⟨547970, by rfl⟩ : syracuseStep 2922509 = 1095941) (by norm_num)
theorem B1948339 : Blo 1947435 1948339 := bstep (se 1 (by rfl) ⟨1461254, by rfl⟩ : syracuseStep 1948339 = 2922509) B2922509
theorem B4383773 : Blo 1947435 4383773 := bbase (se 3 (by rfl) ⟨821957, by rfl⟩ : syracuseStep 4383773 = 1643915) (by norm_num)
theorem B2922515 : Blo 1947435 2922515 := bstep (se 1 (by rfl) ⟨2191886, by rfl⟩ : syracuseStep 2922515 = 4383773) B4383773
theorem B1948343 : Blo 1947435 1948343 := bstep (se 1 (by rfl) ⟨1461257, by rfl⟩ : syracuseStep 1948343 = 2922515) B2922515
theorem B3287837 : Blo 1947435 3287837 := bbase (se 3 (by rfl) ⟨616469, by rfl⟩ : syracuseStep 3287837 = 1232939) (by norm_num)
theorem B2191891 : Blo 1947435 2191891 := bstep (se 1 (by rfl) ⟨1643918, by rfl⟩ : syracuseStep 2191891 = 3287837) B3287837
theorem B2922521 : Blo 1947435 2922521 := bstep (se 2 (by rfl) ⟨1095945, by rfl⟩ : syracuseStep 2922521 = 2191891) B2191891
theorem B1948347 : Blo 1947435 1948347 := bstep (se 1 (by rfl) ⟨1461260, by rfl⟩ : syracuseStep 1948347 = 2922521) B2922521
theorem B4681325 : Blo 1947435 4681325 := bbase (se 3 (by rfl) ⟨877748, by rfl⟩ : syracuseStep 4681325 = 1755497) (by norm_num)
theorem B12483533 : Blo 1947435 12483533 := bstep (se 3 (by rfl) ⟨2340662, by rfl⟩ : syracuseStep 12483533 = 4681325) B4681325
theorem B8322355 : Blo 1947435 8322355 := bstep (se 1 (by rfl) ⟨6241766, by rfl⟩ : syracuseStep 8322355 = 12483533) B12483533
theorem B11096473 : Blo 1947435 11096473 := bstep (se 2 (by rfl) ⟨4161177, by rfl⟩ : syracuseStep 11096473 = 8322355) B8322355
theorem B14795297 : Blo 1947435 14795297 := bstep (se 2 (by rfl) ⟨5548236, by rfl⟩ : syracuseStep 14795297 = 11096473) B11096473
theorem B9863531 : Blo 1947435 9863531 := bstep (se 1 (by rfl) ⟨7397648, by rfl⟩ : syracuseStep 9863531 = 14795297) B14795297
theorem B6575687 : Blo 1947435 6575687 := bstep (se 1 (by rfl) ⟨4931765, by rfl⟩ : syracuseStep 6575687 = 9863531) B9863531
theorem B4383791 : Blo 1947435 4383791 := bstep (se 1 (by rfl) ⟨3287843, by rfl⟩ : syracuseStep 4383791 = 6575687) B6575687
theorem B2922527 : Blo 1947435 2922527 := bstep (se 1 (by rfl) ⟨2191895, by rfl⟩ : syracuseStep 2922527 = 4383791) B4383791
theorem B1948351 : Blo 1947435 1948351 := bstep (se 1 (by rfl) ⟨1461263, by rfl⟩ : syracuseStep 1948351 = 2922527) B2922527
theorem B2922533 : Blo 1947435 2922533 := bbase (se 4 (by rfl) ⟨273987, by rfl⟩ : syracuseStep 2922533 = 547975) (by norm_num)
theorem B1948355 : Blo 1947435 1948355 := bstep (se 1 (by rfl) ⟨1461266, by rfl⟩ : syracuseStep 1948355 = 2922533) B2922533
theorem B2465893 : Blo 1947435 2465893 := bbase (se 4 (by rfl) ⟨231177, by rfl⟩ : syracuseStep 2465893 = 462355) (by norm_num)
theorem B3287857 : Blo 1947435 3287857 := bstep (se 2 (by rfl) ⟨1232946, by rfl⟩ : syracuseStep 3287857 = 2465893) B2465893
theorem B4383809 : Blo 1947435 4383809 := bstep (se 2 (by rfl) ⟨1643928, by rfl⟩ : syracuseStep 4383809 = 3287857) B3287857
theorem B2922539 : Blo 1947435 2922539 := bstep (se 1 (by rfl) ⟨2191904, by rfl⟩ : syracuseStep 2922539 = 4383809) B4383809
theorem B1948359 : Blo 1947435 1948359 := bstep (se 1 (by rfl) ⟨1461269, by rfl⟩ : syracuseStep 1948359 = 2922539) B2922539
theorem B2191909 : Blo 1947435 2191909 := bbase (se 4 (by rfl) ⟨205491, by rfl⟩ : syracuseStep 2191909 = 410983) (by norm_num)
theorem B2922545 : Blo 1947435 2922545 := bstep (se 2 (by rfl) ⟨1095954, by rfl⟩ : syracuseStep 2922545 = 2191909) B2191909
theorem B1948363 : Blo 1947435 1948363 := bstep (se 1 (by rfl) ⟨1461272, by rfl⟩ : syracuseStep 1948363 = 2922545) B2922545
theorem B21353557 : Blo 1947435 21353557 := bbase (se 8 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 21353557 = 250237) (by norm_num)
theorem B28471409 : Blo 1947435 28471409 := bstep (se 2 (by rfl) ⟨10676778, by rfl⟩ : syracuseStep 28471409 = 21353557) B21353557
theorem B18980939 : Blo 1947435 18980939 := bstep (se 1 (by rfl) ⟨14235704, by rfl⟩ : syracuseStep 18980939 = 28471409) B28471409
theorem B50615837 : Blo 1947435 50615837 := bstep (se 3 (by rfl) ⟨9490469, by rfl⟩ : syracuseStep 50615837 = 18980939) B18980939
theorem B33743891 : Blo 1947435 33743891 := bstep (se 1 (by rfl) ⟨25307918, by rfl⟩ : syracuseStep 33743891 = 50615837) B50615837
theorem B22495927 : Blo 1947435 22495927 := bstep (se 1 (by rfl) ⟨16871945, by rfl⟩ : syracuseStep 22495927 = 33743891) B33743891
theorem B29994569 : Blo 1947435 29994569 := bstep (se 2 (by rfl) ⟨11247963, by rfl⟩ : syracuseStep 29994569 = 22495927) B22495927
theorem B19996379 : Blo 1947435 19996379 := bstep (se 1 (by rfl) ⟨14997284, by rfl⟩ : syracuseStep 19996379 = 29994569) B29994569
theorem B13330919 : Blo 1947435 13330919 := bstep (se 1 (by rfl) ⟨9998189, by rfl⟩ : syracuseStep 13330919 = 19996379) B19996379
theorem B35549117 : Blo 1947435 35549117 := bstep (se 3 (by rfl) ⟨6665459, by rfl⟩ : syracuseStep 35549117 = 13330919) B13330919
theorem B23699411 : Blo 1947435 23699411 := bstep (se 1 (by rfl) ⟨17774558, by rfl⟩ : syracuseStep 23699411 = 35549117) B35549117
theorem B15799607 : Blo 1947435 15799607 := bstep (se 1 (by rfl) ⟨11849705, by rfl⟩ : syracuseStep 15799607 = 23699411) B23699411
theorem B10533071 : Blo 1947435 10533071 := bstep (se 1 (by rfl) ⟨7899803, by rfl⟩ : syracuseStep 10533071 = 15799607) B15799607
theorem B7022047 : Blo 1947435 7022047 := bstep (se 1 (by rfl) ⟨5266535, by rfl⟩ : syracuseStep 7022047 = 10533071) B10533071
theorem B9362729 : Blo 1947435 9362729 := bstep (se 2 (by rfl) ⟨3511023, by rfl⟩ : syracuseStep 9362729 = 7022047) B7022047
theorem B6241819 : Blo 1947435 6241819 := bstep (se 1 (by rfl) ⟨4681364, by rfl⟩ : syracuseStep 6241819 = 9362729) B9362729
theorem B8322425 : Blo 1947435 8322425 := bstep (se 2 (by rfl) ⟨3120909, by rfl⟩ : syracuseStep 8322425 = 6241819) B6241819
theorem B5548283 : Blo 1947435 5548283 := bstep (se 1 (by rfl) ⟨4161212, by rfl⟩ : syracuseStep 5548283 = 8322425) B8322425
theorem B3698855 : Blo 1947435 3698855 := bstep (se 1 (by rfl) ⟨2774141, by rfl⟩ : syracuseStep 3698855 = 5548283) B5548283
theorem B2465903 : Blo 1947435 2465903 := bstep (se 1 (by rfl) ⟨1849427, by rfl⟩ : syracuseStep 2465903 = 3698855) B3698855
theorem B6575741 : Blo 1947435 6575741 := bstep (se 3 (by rfl) ⟨1232951, by rfl⟩ : syracuseStep 6575741 = 2465903) B2465903
theorem B4383827 : Blo 1947435 4383827 := bstep (se 1 (by rfl) ⟨3287870, by rfl⟩ : syracuseStep 4383827 = 6575741) B6575741
theorem B2922551 : Blo 1947435 2922551 := bstep (se 1 (by rfl) ⟨2191913, by rfl⟩ : syracuseStep 2922551 = 4383827) B4383827
theorem B1948367 : Blo 1947435 1948367 := bstep (se 1 (by rfl) ⟨1461275, by rfl⟩ : syracuseStep 1948367 = 2922551) B2922551
theorem B2922557 : Blo 1947435 2922557 := bbase (se 3 (by rfl) ⟨547979, by rfl⟩ : syracuseStep 2922557 = 1095959) (by norm_num)
theorem B1948371 : Blo 1947435 1948371 := bstep (se 1 (by rfl) ⟨1461278, by rfl⟩ : syracuseStep 1948371 = 2922557) B2922557
theorem B4383845 : Blo 1947435 4383845 := bbase (se 4 (by rfl) ⟨410985, by rfl⟩ : syracuseStep 4383845 = 821971) (by norm_num)
theorem B2922563 : Blo 1947435 2922563 := bstep (se 1 (by rfl) ⟨2191922, by rfl⟩ : syracuseStep 2922563 = 4383845) B4383845
theorem B1948375 : Blo 1947435 1948375 := bstep (se 1 (by rfl) ⟨1461281, by rfl⟩ : syracuseStep 1948375 = 2922563) B2922563
theorem B4931837 : Blo 1947435 4931837 := bbase (se 3 (by rfl) ⟨924719, by rfl⟩ : syracuseStep 4931837 = 1849439) (by norm_num)
theorem B3287891 : Blo 1947435 3287891 := bstep (se 1 (by rfl) ⟨2465918, by rfl⟩ : syracuseStep 3287891 = 4931837) B4931837
theorem B2191927 : Blo 1947435 2191927 := bstep (se 1 (by rfl) ⟨1643945, by rfl⟩ : syracuseStep 2191927 = 3287891) B3287891
theorem B2922569 : Blo 1947435 2922569 := bstep (se 2 (by rfl) ⟨1095963, by rfl⟩ : syracuseStep 2922569 = 2191927) B2191927
theorem B1948379 : Blo 1947435 1948379 := bstep (se 1 (by rfl) ⟨1461284, by rfl⟩ : syracuseStep 1948379 = 2922569) B2922569
theorem B3698885 : Blo 1947435 3698885 := bbase (se 4 (by rfl) ⟨346770, by rfl⟩ : syracuseStep 3698885 = 693541) (by norm_num)
theorem B9863693 : Blo 1947435 9863693 := bstep (se 3 (by rfl) ⟨1849442, by rfl⟩ : syracuseStep 9863693 = 3698885) B3698885
theorem B6575795 : Blo 1947435 6575795 := bstep (se 1 (by rfl) ⟨4931846, by rfl⟩ : syracuseStep 6575795 = 9863693) B9863693
theorem B4383863 : Blo 1947435 4383863 := bstep (se 1 (by rfl) ⟨3287897, by rfl⟩ : syracuseStep 4383863 = 6575795) B6575795
theorem B2922575 : Blo 1947435 2922575 := bstep (se 1 (by rfl) ⟨2191931, by rfl⟩ : syracuseStep 2922575 = 4383863) B4383863
theorem B1948383 : Blo 1947435 1948383 := bstep (se 1 (by rfl) ⟨1461287, by rfl⟩ : syracuseStep 1948383 = 2922575) B2922575
theorem B2922581 : Blo 1947435 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B1948387 : Blo 1947435 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B2252161 : Blo 1947435 2252161 := bbase (se 2 (by rfl) ⟨844560, by rfl⟩ : syracuseStep 2252161 = 1689121) (by norm_num)
theorem B3002881 : Blo 1947435 3002881 := bstep (se 2 (by rfl) ⟨1126080, by rfl⟩ : syracuseStep 3002881 = 2252161) B2252161
theorem B4003841 : Blo 1947435 4003841 := bstep (se 2 (by rfl) ⟨1501440, by rfl⟩ : syracuseStep 4003841 = 3002881) B3002881
theorem B10676909 : Blo 1947435 10676909 := bstep (se 3 (by rfl) ⟨2001920, by rfl⟩ : syracuseStep 10676909 = 4003841) B4003841
theorem B7117939 : Blo 1947435 7117939 := bstep (se 1 (by rfl) ⟨5338454, by rfl⟩ : syracuseStep 7117939 = 10676909) B10676909
theorem B37962341 : Blo 1947435 37962341 := bstep (se 4 (by rfl) ⟨3558969, by rfl⟩ : syracuseStep 37962341 = 7117939) B7117939
theorem B25308227 : Blo 1947435 25308227 := bstep (se 1 (by rfl) ⟨18981170, by rfl⟩ : syracuseStep 25308227 = 37962341) B37962341
theorem B16872151 : Blo 1947435 16872151 := bstep (se 1 (by rfl) ⟨12654113, by rfl⟩ : syracuseStep 16872151 = 25308227) B25308227
theorem B22496201 : Blo 1947435 22496201 := bstep (se 2 (by rfl) ⟨8436075, by rfl⟩ : syracuseStep 22496201 = 16872151) B16872151
theorem B14997467 : Blo 1947435 14997467 := bstep (se 1 (by rfl) ⟨11248100, by rfl⟩ : syracuseStep 14997467 = 22496201) B22496201
theorem B9998311 : Blo 1947435 9998311 := bstep (se 1 (by rfl) ⟨7498733, by rfl⟩ : syracuseStep 9998311 = 14997467) B14997467
theorem B13331081 : Blo 1947435 13331081 := bstep (se 2 (by rfl) ⟨4999155, by rfl⟩ : syracuseStep 13331081 = 9998311) B9998311
theorem B35549549 : Blo 1947435 35549549 := bstep (se 3 (by rfl) ⟨6665540, by rfl⟩ : syracuseStep 35549549 = 13331081) B13331081
theorem B23699699 : Blo 1947435 23699699 := bstep (se 1 (by rfl) ⟨17774774, by rfl⟩ : syracuseStep 23699699 = 35549549) B35549549
theorem B15799799 : Blo 1947435 15799799 := bstep (se 1 (by rfl) ⟨11849849, by rfl⟩ : syracuseStep 15799799 = 23699699) B23699699
theorem B42132797 : Blo 1947435 42132797 := bstep (se 3 (by rfl) ⟨7899899, by rfl⟩ : syracuseStep 42132797 = 15799799) B15799799
theorem B28088531 : Blo 1947435 28088531 := bstep (se 1 (by rfl) ⟨21066398, by rfl⟩ : syracuseStep 28088531 = 42132797) B42132797
theorem B18725687 : Blo 1947435 18725687 := bstep (se 1 (by rfl) ⟨14044265, by rfl⟩ : syracuseStep 18725687 = 28088531) B28088531
theorem B12483791 : Blo 1947435 12483791 := bstep (se 1 (by rfl) ⟨9362843, by rfl⟩ : syracuseStep 12483791 = 18725687) B18725687
theorem B8322527 : Blo 1947435 8322527 := bstep (se 1 (by rfl) ⟨6241895, by rfl⟩ : syracuseStep 8322527 = 12483791) B12483791
theorem B5548351 : Blo 1947435 5548351 := bstep (se 1 (by rfl) ⟨4161263, by rfl⟩ : syracuseStep 5548351 = 8322527) B8322527
theorem B7397801 : Blo 1947435 7397801 := bstep (se 2 (by rfl) ⟨2774175, by rfl⟩ : syracuseStep 7397801 = 5548351) B5548351
theorem B4931867 : Blo 1947435 4931867 := bstep (se 1 (by rfl) ⟨3698900, by rfl⟩ : syracuseStep 4931867 = 7397801) B7397801
theorem B3287911 : Blo 1947435 3287911 := bstep (se 1 (by rfl) ⟨2465933, by rfl⟩ : syracuseStep 3287911 = 4931867) B4931867
theorem B4383881 : Blo 1947435 4383881 := bstep (se 2 (by rfl) ⟨1643955, by rfl⟩ : syracuseStep 4383881 = 3287911) B3287911
theorem B2922587 : Blo 1947435 2922587 := bstep (se 1 (by rfl) ⟨2191940, by rfl⟩ : syracuseStep 2922587 = 4383881) B4383881
theorem B1948391 : Blo 1947435 1948391 := bstep (se 1 (by rfl) ⟨1461293, by rfl⟩ : syracuseStep 1948391 = 2922587) B2922587
theorem B2191945 : Blo 1947435 2191945 := bbase (se 2 (by rfl) ⟨821979, by rfl⟩ : syracuseStep 2191945 = 1643959) (by norm_num)
theorem B2922593 : Blo 1947435 2922593 := bstep (se 2 (by rfl) ⟨1095972, by rfl⟩ : syracuseStep 2922593 = 2191945) B2191945
theorem B1948395 : Blo 1947435 1948395 := bstep (se 1 (by rfl) ⟨1461296, by rfl⟩ : syracuseStep 1948395 = 2922593) B2922593
theorem B2499589 : Blo 1947435 2499589 := bbase (se 4 (by rfl) ⟨234336, by rfl⟩ : syracuseStep 2499589 = 468673) (by norm_num)
theorem B3332785 : Blo 1947435 3332785 := bstep (se 2 (by rfl) ⟨1249794, by rfl⟩ : syracuseStep 3332785 = 2499589) B2499589
theorem B4443713 : Blo 1947435 4443713 := bstep (se 2 (by rfl) ⟨1666392, by rfl⟩ : syracuseStep 4443713 = 3332785) B3332785
theorem B2962475 : Blo 1947435 2962475 := bstep (se 1 (by rfl) ⟨2221856, by rfl⟩ : syracuseStep 2962475 = 4443713) B4443713
theorem B1974983 : Blo 1947435 1974983 := bstep (se 1 (by rfl) ⟨1481237, by rfl⟩ : syracuseStep 1974983 = 2962475) B2962475
theorem B5266621 : Blo 1947435 5266621 := bstep (se 3 (by rfl) ⟨987491, by rfl⟩ : syracuseStep 5266621 = 1974983) B1974983
theorem B7022161 : Blo 1947435 7022161 := bstep (se 2 (by rfl) ⟨2633310, by rfl⟩ : syracuseStep 7022161 = 5266621) B5266621
theorem B9362881 : Blo 1947435 9362881 := bstep (se 2 (by rfl) ⟨3511080, by rfl⟩ : syracuseStep 9362881 = 7022161) B7022161
theorem B12483841 : Blo 1947435 12483841 := bstep (se 2 (by rfl) ⟨4681440, by rfl⟩ : syracuseStep 12483841 = 9362881) B9362881
theorem B16645121 : Blo 1947435 16645121 := bstep (se 2 (by rfl) ⟨6241920, by rfl⟩ : syracuseStep 16645121 = 12483841) B12483841
theorem B11096747 : Blo 1947435 11096747 := bstep (se 1 (by rfl) ⟨8322560, by rfl⟩ : syracuseStep 11096747 = 16645121) B16645121
theorem B7397831 : Blo 1947435 7397831 := bstep (se 1 (by rfl) ⟨5548373, by rfl⟩ : syracuseStep 7397831 = 11096747) B11096747
theorem B4931887 : Blo 1947435 4931887 := bstep (se 1 (by rfl) ⟨3698915, by rfl⟩ : syracuseStep 4931887 = 7397831) B7397831
theorem B6575849 : Blo 1947435 6575849 := bstep (se 2 (by rfl) ⟨2465943, by rfl⟩ : syracuseStep 6575849 = 4931887) B4931887
theorem B4383899 : Blo 1947435 4383899 := bstep (se 1 (by rfl) ⟨3287924, by rfl⟩ : syracuseStep 4383899 = 6575849) B6575849
theorem B2922599 : Blo 1947435 2922599 := bstep (se 1 (by rfl) ⟨2191949, by rfl⟩ : syracuseStep 2922599 = 4383899) B4383899
theorem B1948399 : Blo 1947435 1948399 := bstep (se 1 (by rfl) ⟨1461299, by rfl⟩ : syracuseStep 1948399 = 2922599) B2922599
theorem B2922605 : Blo 1947435 2922605 := bbase (se 3 (by rfl) ⟨547988, by rfl⟩ : syracuseStep 2922605 = 1095977) (by norm_num)
theorem B1948403 : Blo 1947435 1948403 := bstep (se 1 (by rfl) ⟨1461302, by rfl⟩ : syracuseStep 1948403 = 2922605) B2922605
theorem B4383917 : Blo 1947435 4383917 := bbase (se 3 (by rfl) ⟨821984, by rfl⟩ : syracuseStep 4383917 = 1643969) (by norm_num)
theorem B2922611 : Blo 1947435 2922611 := bstep (se 1 (by rfl) ⟨2191958, by rfl⟩ : syracuseStep 2922611 = 4383917) B4383917
theorem B1948407 : Blo 1947435 1948407 := bstep (se 1 (by rfl) ⟨1461305, by rfl⟩ : syracuseStep 1948407 = 2922611) B2922611
theorem B16234037 : Blo 1947435 16234037 := bbase (se 5 (by rfl) ⟨760970, by rfl⟩ : syracuseStep 16234037 = 1521941) (by norm_num)
theorem B10822691 : Blo 1947435 10822691 := bstep (se 1 (by rfl) ⟨8117018, by rfl⟩ : syracuseStep 10822691 = 16234037) B16234037
theorem B28860509 : Blo 1947435 28860509 := bstep (se 3 (by rfl) ⟨5411345, by rfl⟩ : syracuseStep 28860509 = 10822691) B10822691
theorem B19240339 : Blo 1947435 19240339 := bstep (se 1 (by rfl) ⟨14430254, by rfl⟩ : syracuseStep 19240339 = 28860509) B28860509
theorem B25653785 : Blo 1947435 25653785 := bstep (se 2 (by rfl) ⟨9620169, by rfl⟩ : syracuseStep 25653785 = 19240339) B19240339
theorem B68410093 : Blo 1947435 68410093 := bstep (se 3 (by rfl) ⟨12826892, by rfl⟩ : syracuseStep 68410093 = 25653785) B25653785
theorem B91213457 : Blo 1947435 91213457 := bstep (se 2 (by rfl) ⟨34205046, by rfl⟩ : syracuseStep 91213457 = 68410093) B68410093
theorem B243235885 : Blo 1947435 243235885 := bstep (se 3 (by rfl) ⟨45606728, by rfl⟩ : syracuseStep 243235885 = 91213457) B91213457
theorem B324314513 : Blo 1947435 324314513 := bstep (se 2 (by rfl) ⟨121617942, by rfl⟩ : syracuseStep 324314513 = 243235885) B243235885
theorem B216209675 : Blo 1947435 216209675 := bstep (se 1 (by rfl) ⟨162157256, by rfl⟩ : syracuseStep 216209675 = 324314513) B324314513
theorem B144139783 : Blo 1947435 144139783 := bstep (se 1 (by rfl) ⟨108104837, by rfl⟩ : syracuseStep 144139783 = 216209675) B216209675
theorem B192186377 : Blo 1947435 192186377 := bstep (se 2 (by rfl) ⟨72069891, by rfl⟩ : syracuseStep 192186377 = 144139783) B144139783
theorem B128124251 : Blo 1947435 128124251 := bstep (se 1 (by rfl) ⟨96093188, by rfl⟩ : syracuseStep 128124251 = 192186377) B192186377
theorem B85416167 : Blo 1947435 85416167 := bstep (se 1 (by rfl) ⟨64062125, by rfl⟩ : syracuseStep 85416167 = 128124251) B128124251
theorem B227776445 : Blo 1947435 227776445 := bstep (se 3 (by rfl) ⟨42708083, by rfl⟩ : syracuseStep 227776445 = 85416167) B85416167
theorem B151850963 : Blo 1947435 151850963 := bstep (se 1 (by rfl) ⟨113888222, by rfl⟩ : syracuseStep 151850963 = 227776445) B227776445
theorem B101233975 : Blo 1947435 101233975 := bstep (se 1 (by rfl) ⟨75925481, by rfl⟩ : syracuseStep 101233975 = 151850963) B151850963
theorem B134978633 : Blo 1947435 134978633 := bstep (se 2 (by rfl) ⟨50616987, by rfl⟩ : syracuseStep 134978633 = 101233975) B101233975
theorem B89985755 : Blo 1947435 89985755 := bstep (se 1 (by rfl) ⟨67489316, by rfl⟩ : syracuseStep 89985755 = 134978633) B134978633
theorem B59990503 : Blo 1947435 59990503 := bstep (se 1 (by rfl) ⟨44992877, by rfl⟩ : syracuseStep 59990503 = 89985755) B89985755
theorem B79987337 : Blo 1947435 79987337 := bstep (se 2 (by rfl) ⟨29995251, by rfl⟩ : syracuseStep 79987337 = 59990503) B59990503
theorem B53324891 : Blo 1947435 53324891 := bstep (se 1 (by rfl) ⟨39993668, by rfl⟩ : syracuseStep 53324891 = 79987337) B79987337
theorem B35549927 : Blo 1947435 35549927 := bstep (se 1 (by rfl) ⟨26662445, by rfl⟩ : syracuseStep 35549927 = 53324891) B53324891
theorem B23699951 : Blo 1947435 23699951 := bstep (se 1 (by rfl) ⟨17774963, by rfl⟩ : syracuseStep 23699951 = 35549927) B35549927
theorem B15799967 : Blo 1947435 15799967 := bstep (se 1 (by rfl) ⟨11849975, by rfl⟩ : syracuseStep 15799967 = 23699951) B23699951
theorem B10533311 : Blo 1947435 10533311 := bstep (se 1 (by rfl) ⟨7899983, by rfl⟩ : syracuseStep 10533311 = 15799967) B15799967
theorem B7022207 : Blo 1947435 7022207 := bstep (se 1 (by rfl) ⟨5266655, by rfl⟩ : syracuseStep 7022207 = 10533311) B10533311
theorem B4681471 : Blo 1947435 4681471 := bstep (se 1 (by rfl) ⟨3511103, by rfl⟩ : syracuseStep 4681471 = 7022207) B7022207
theorem B6241961 : Blo 1947435 6241961 := bstep (se 2 (by rfl) ⟨2340735, by rfl⟩ : syracuseStep 6241961 = 4681471) B4681471
theorem B4161307 : Blo 1947435 4161307 := bstep (se 1 (by rfl) ⟨3120980, by rfl⟩ : syracuseStep 4161307 = 6241961) B6241961
theorem B5548409 : Blo 1947435 5548409 := bstep (se 2 (by rfl) ⟨2080653, by rfl⟩ : syracuseStep 5548409 = 4161307) B4161307
theorem B3698939 : Blo 1947435 3698939 := bstep (se 1 (by rfl) ⟨2774204, by rfl⟩ : syracuseStep 3698939 = 5548409) B5548409
theorem B2465959 : Blo 1947435 2465959 := bstep (se 1 (by rfl) ⟨1849469, by rfl⟩ : syracuseStep 2465959 = 3698939) B3698939
theorem B3287945 : Blo 1947435 3287945 := bstep (se 2 (by rfl) ⟨1232979, by rfl⟩ : syracuseStep 3287945 = 2465959) B2465959
theorem B2191963 : Blo 1947435 2191963 := bstep (se 1 (by rfl) ⟨1643972, by rfl⟩ : syracuseStep 2191963 = 3287945) B3287945
theorem B2922617 : Blo 1947435 2922617 := bstep (se 2 (by rfl) ⟨1095981, by rfl⟩ : syracuseStep 2922617 = 2191963) B2191963
theorem B1948411 : Blo 1947435 1948411 := bstep (se 1 (by rfl) ⟨1461308, by rfl⟩ : syracuseStep 1948411 = 2922617) B2922617
theorem B3511109 : Blo 1947435 3511109 := bbase (se 4 (by rfl) ⟨329166, by rfl⟩ : syracuseStep 3511109 = 658333) (by norm_num)
theorem B9362957 : Blo 1947435 9362957 := bstep (se 3 (by rfl) ⟨1755554, by rfl⟩ : syracuseStep 9362957 = 3511109) B3511109
theorem B24967885 : Blo 1947435 24967885 := bstep (se 3 (by rfl) ⟨4681478, by rfl⟩ : syracuseStep 24967885 = 9362957) B9362957
theorem B33290513 : Blo 1947435 33290513 := bstep (se 2 (by rfl) ⟨12483942, by rfl⟩ : syracuseStep 33290513 = 24967885) B24967885
theorem B22193675 : Blo 1947435 22193675 := bstep (se 1 (by rfl) ⟨16645256, by rfl⟩ : syracuseStep 22193675 = 33290513) B33290513
theorem B14795783 : Blo 1947435 14795783 := bstep (se 1 (by rfl) ⟨11096837, by rfl⟩ : syracuseStep 14795783 = 22193675) B22193675
theorem B9863855 : Blo 1947435 9863855 := bstep (se 1 (by rfl) ⟨7397891, by rfl⟩ : syracuseStep 9863855 = 14795783) B14795783
theorem B6575903 : Blo 1947435 6575903 := bstep (se 1 (by rfl) ⟨4931927, by rfl⟩ : syracuseStep 6575903 = 9863855) B9863855
theorem B4383935 : Blo 1947435 4383935 := bstep (se 1 (by rfl) ⟨3287951, by rfl⟩ : syracuseStep 4383935 = 6575903) B6575903
theorem B2922623 : Blo 1947435 2922623 := bstep (se 1 (by rfl) ⟨2191967, by rfl⟩ : syracuseStep 2922623 = 4383935) B4383935
theorem B1948415 : Blo 1947435 1948415 := bstep (se 1 (by rfl) ⟨1461311, by rfl⟩ : syracuseStep 1948415 = 2922623) B2922623
theorem B2922629 : Blo 1947435 2922629 := bbase (se 4 (by rfl) ⟨273996, by rfl⟩ : syracuseStep 2922629 = 547993) (by norm_num)
theorem B1948419 : Blo 1947435 1948419 := bstep (se 1 (by rfl) ⟨1461314, by rfl⟩ : syracuseStep 1948419 = 2922629) B2922629
theorem B3287965 : Blo 1947435 3287965 := bbase (se 3 (by rfl) ⟨616493, by rfl⟩ : syracuseStep 3287965 = 1232987) (by norm_num)
theorem B4383953 : Blo 1947435 4383953 := bstep (se 2 (by rfl) ⟨1643982, by rfl⟩ : syracuseStep 4383953 = 3287965) B3287965
theorem B2922635 : Blo 1947435 2922635 := bstep (se 1 (by rfl) ⟨2191976, by rfl⟩ : syracuseStep 2922635 = 4383953) B4383953
theorem B1948423 : Blo 1947435 1948423 := bstep (se 1 (by rfl) ⟨1461317, by rfl⟩ : syracuseStep 1948423 = 2922635) B2922635
theorem B2191981 : Blo 1947435 2191981 := bbase (se 3 (by rfl) ⟨410996, by rfl⟩ : syracuseStep 2191981 = 821993) (by norm_num)
theorem B2922641 : Blo 1947435 2922641 := bstep (se 2 (by rfl) ⟨1095990, by rfl⟩ : syracuseStep 2922641 = 2191981) B2191981
theorem B1948427 : Blo 1947435 1948427 := bstep (se 1 (by rfl) ⟨1461320, by rfl⟩ : syracuseStep 1948427 = 2922641) B2922641
theorem B6575957 : Blo 1947435 6575957 := bbase (se 9 (by rfl) ⟨19265, by rfl⟩ : syracuseStep 6575957 = 38531) (by norm_num)
theorem B4383971 : Blo 1947435 4383971 := bstep (se 1 (by rfl) ⟨3287978, by rfl⟩ : syracuseStep 4383971 = 6575957) B6575957
theorem B2922647 : Blo 1947435 2922647 := bstep (se 1 (by rfl) ⟨2191985, by rfl⟩ : syracuseStep 2922647 = 4383971) B4383971
theorem B1948431 : Blo 1947435 1948431 := bstep (se 1 (by rfl) ⟨1461323, by rfl⟩ : syracuseStep 1948431 = 2922647) B2922647
theorem B2922653 : Blo 1947435 2922653 := bbase (se 3 (by rfl) ⟨547997, by rfl⟩ : syracuseStep 2922653 = 1095995) (by norm_num)
theorem B1948435 : Blo 1947435 1948435 := bstep (se 1 (by rfl) ⟨1461326, by rfl⟩ : syracuseStep 1948435 = 2922653) B2922653
theorem B4383989 : Blo 1947435 4383989 := bbase (se 5 (by rfl) ⟨205499, by rfl⟩ : syracuseStep 4383989 = 410999) (by norm_num)
theorem B2922659 : Blo 1947435 2922659 := bstep (se 1 (by rfl) ⟨2191994, by rfl⟩ : syracuseStep 2922659 = 4383989) B4383989
theorem B1948439 : Blo 1947435 1948439 := bstep (se 1 (by rfl) ⟨1461329, by rfl⟩ : syracuseStep 1948439 = 2922659) B2922659
theorem B4003949 : Blo 1947435 4003949 := bbase (se 3 (by rfl) ⟨750740, by rfl⟩ : syracuseStep 4003949 = 1501481) (by norm_num)
theorem B10677197 : Blo 1947435 10677197 := bstep (se 3 (by rfl) ⟨2001974, by rfl⟩ : syracuseStep 10677197 = 4003949) B4003949
theorem B7118131 : Blo 1947435 7118131 := bstep (se 1 (by rfl) ⟨5338598, by rfl⟩ : syracuseStep 7118131 = 10677197) B10677197
theorem B9490841 : Blo 1947435 9490841 := bstep (se 2 (by rfl) ⟨3559065, by rfl⟩ : syracuseStep 9490841 = 7118131) B7118131
theorem B6327227 : Blo 1947435 6327227 := bstep (se 1 (by rfl) ⟨4745420, by rfl⟩ : syracuseStep 6327227 = 9490841) B9490841
theorem B4218151 : Blo 1947435 4218151 := bstep (se 1 (by rfl) ⟨3163613, by rfl⟩ : syracuseStep 4218151 = 6327227) B6327227
theorem B5624201 : Blo 1947435 5624201 := bstep (se 2 (by rfl) ⟨2109075, by rfl⟩ : syracuseStep 5624201 = 4218151) B4218151
theorem B14997869 : Blo 1947435 14997869 := bstep (se 3 (by rfl) ⟨2812100, by rfl⟩ : syracuseStep 14997869 = 5624201) B5624201
theorem B9998579 : Blo 1947435 9998579 := bstep (se 1 (by rfl) ⟨7498934, by rfl⟩ : syracuseStep 9998579 = 14997869) B14997869
theorem B6665719 : Blo 1947435 6665719 := bstep (se 1 (by rfl) ⟨4999289, by rfl⟩ : syracuseStep 6665719 = 9998579) B9998579
theorem B8887625 : Blo 1947435 8887625 := bstep (se 2 (by rfl) ⟨3332859, by rfl⟩ : syracuseStep 8887625 = 6665719) B6665719
theorem B5925083 : Blo 1947435 5925083 := bstep (se 1 (by rfl) ⟨4443812, by rfl⟩ : syracuseStep 5925083 = 8887625) B8887625
theorem B15800221 : Blo 1947435 15800221 := bstep (se 3 (by rfl) ⟨2962541, by rfl⟩ : syracuseStep 15800221 = 5925083) B5925083
theorem B21066961 : Blo 1947435 21066961 := bstep (se 2 (by rfl) ⟨7900110, by rfl⟩ : syracuseStep 21066961 = 15800221) B15800221
theorem B28089281 : Blo 1947435 28089281 := bstep (se 2 (by rfl) ⟨10533480, by rfl⟩ : syracuseStep 28089281 = 21066961) B21066961
theorem B18726187 : Blo 1947435 18726187 := bstep (se 1 (by rfl) ⟨14044640, by rfl⟩ : syracuseStep 18726187 = 28089281) B28089281
theorem B24968249 : Blo 1947435 24968249 := bstep (se 2 (by rfl) ⟨9363093, by rfl⟩ : syracuseStep 24968249 = 18726187) B18726187
theorem B16645499 : Blo 1947435 16645499 := bstep (se 1 (by rfl) ⟨12484124, by rfl⟩ : syracuseStep 16645499 = 24968249) B24968249
theorem B11096999 : Blo 1947435 11096999 := bstep (se 1 (by rfl) ⟨8322749, by rfl⟩ : syracuseStep 11096999 = 16645499) B16645499
theorem B7397999 : Blo 1947435 7397999 := bstep (se 1 (by rfl) ⟨5548499, by rfl⟩ : syracuseStep 7397999 = 11096999) B11096999
theorem B4931999 : Blo 1947435 4931999 := bstep (se 1 (by rfl) ⟨3698999, by rfl⟩ : syracuseStep 4931999 = 7397999) B7397999
theorem B3287999 : Blo 1947435 3287999 := bstep (se 1 (by rfl) ⟨2465999, by rfl⟩ : syracuseStep 3287999 = 4931999) B4931999
theorem B2191999 : Blo 1947435 2191999 := bstep (se 1 (by rfl) ⟨1643999, by rfl⟩ : syracuseStep 2191999 = 3287999) B3287999
theorem B2922665 : Blo 1947435 2922665 := bstep (se 2 (by rfl) ⟨1095999, by rfl⟩ : syracuseStep 2922665 = 2191999) B2191999
theorem B1948443 : Blo 1947435 1948443 := bstep (se 1 (by rfl) ⟨1461332, by rfl⟩ : syracuseStep 1948443 = 2922665) B2922665
theorem B13002133 : Blo 1947435 13002133 := bbase (se 6 (by rfl) ⟨304737, by rfl⟩ : syracuseStep 13002133 = 609475) (by norm_num)
theorem B17336177 : Blo 1947435 17336177 := bstep (se 2 (by rfl) ⟨6501066, by rfl⟩ : syracuseStep 17336177 = 13002133) B13002133
theorem B11557451 : Blo 1947435 11557451 := bstep (se 1 (by rfl) ⟨8668088, by rfl⟩ : syracuseStep 11557451 = 17336177) B17336177
theorem B7704967 : Blo 1947435 7704967 := bstep (se 1 (by rfl) ⟨5778725, by rfl⟩ : syracuseStep 7704967 = 11557451) B11557451
theorem B10273289 : Blo 1947435 10273289 := bstep (se 2 (by rfl) ⟨3852483, by rfl⟩ : syracuseStep 10273289 = 7704967) B7704967
theorem B27395437 : Blo 1947435 27395437 := bstep (se 3 (by rfl) ⟨5136644, by rfl⟩ : syracuseStep 27395437 = 10273289) B10273289
theorem B36527249 : Blo 1947435 36527249 := bstep (se 2 (by rfl) ⟨13697718, by rfl⟩ : syracuseStep 36527249 = 27395437) B27395437
theorem B24351499 : Blo 1947435 24351499 := bstep (se 1 (by rfl) ⟨18263624, by rfl⟩ : syracuseStep 24351499 = 36527249) B36527249
theorem B129874661 : Blo 1947435 129874661 := bstep (se 4 (by rfl) ⟨12175749, by rfl⟩ : syracuseStep 129874661 = 24351499) B24351499
theorem B86583107 : Blo 1947435 86583107 := bstep (se 1 (by rfl) ⟨64937330, by rfl⟩ : syracuseStep 86583107 = 129874661) B129874661
theorem B57722071 : Blo 1947435 57722071 := bstep (se 1 (by rfl) ⟨43291553, by rfl⟩ : syracuseStep 57722071 = 86583107) B86583107
theorem B76962761 : Blo 1947435 76962761 := bstep (se 2 (by rfl) ⟨28861035, by rfl⟩ : syracuseStep 76962761 = 57722071) B57722071
theorem B51308507 : Blo 1947435 51308507 := bstep (se 1 (by rfl) ⟨38481380, by rfl⟩ : syracuseStep 51308507 = 76962761) B76962761
theorem B34205671 : Blo 1947435 34205671 := bstep (se 1 (by rfl) ⟨25654253, by rfl⟩ : syracuseStep 34205671 = 51308507) B51308507
theorem B182430245 : Blo 1947435 182430245 := bstep (se 4 (by rfl) ⟨17102835, by rfl⟩ : syracuseStep 182430245 = 34205671) B34205671
theorem B486480653 : Blo 1947435 486480653 := bstep (se 3 (by rfl) ⟨91215122, by rfl⟩ : syracuseStep 486480653 = 182430245) B182430245
theorem B324320435 : Blo 1947435 324320435 := bstep (se 1 (by rfl) ⟨243240326, by rfl⟩ : syracuseStep 324320435 = 486480653) B486480653
theorem B216213623 : Blo 1947435 216213623 := bstep (se 1 (by rfl) ⟨162160217, by rfl⟩ : syracuseStep 216213623 = 324320435) B324320435
theorem B144142415 : Blo 1947435 144142415 := bstep (se 1 (by rfl) ⟨108106811, by rfl⟩ : syracuseStep 144142415 = 216213623) B216213623
theorem B96094943 : Blo 1947435 96094943 := bstep (se 1 (by rfl) ⟨72071207, by rfl⟩ : syracuseStep 96094943 = 144142415) B144142415
theorem B64063295 : Blo 1947435 64063295 := bstep (se 1 (by rfl) ⟨48047471, by rfl⟩ : syracuseStep 64063295 = 96094943) B96094943
theorem B42708863 : Blo 1947435 42708863 := bstep (se 1 (by rfl) ⟨32031647, by rfl⟩ : syracuseStep 42708863 = 64063295) B64063295
theorem B28472575 : Blo 1947435 28472575 := bstep (se 1 (by rfl) ⟨21354431, by rfl⟩ : syracuseStep 28472575 = 42708863) B42708863
theorem B37963433 : Blo 1947435 37963433 := bstep (se 2 (by rfl) ⟨14236287, by rfl⟩ : syracuseStep 37963433 = 28472575) B28472575
theorem B25308955 : Blo 1947435 25308955 := bstep (se 1 (by rfl) ⟨18981716, by rfl⟩ : syracuseStep 25308955 = 37963433) B37963433
theorem B134981093 : Blo 1947435 134981093 := bstep (se 4 (by rfl) ⟨12654477, by rfl⟩ : syracuseStep 134981093 = 25308955) B25308955
theorem B89987395 : Blo 1947435 89987395 := bstep (se 1 (by rfl) ⟨67490546, by rfl⟩ : syracuseStep 89987395 = 134981093) B134981093
theorem B119983193 : Blo 1947435 119983193 := bstep (se 2 (by rfl) ⟨44993697, by rfl⟩ : syracuseStep 119983193 = 89987395) B89987395
theorem B79988795 : Blo 1947435 79988795 := bstep (se 1 (by rfl) ⟨59991596, by rfl⟩ : syracuseStep 79988795 = 119983193) B119983193
theorem B53325863 : Blo 1947435 53325863 := bstep (se 1 (by rfl) ⟨39994397, by rfl⟩ : syracuseStep 53325863 = 79988795) B79988795
theorem B35550575 : Blo 1947435 35550575 := bstep (se 1 (by rfl) ⟨26662931, by rfl⟩ : syracuseStep 35550575 = 53325863) B53325863
theorem B23700383 : Blo 1947435 23700383 := bstep (se 1 (by rfl) ⟨17775287, by rfl⟩ : syracuseStep 23700383 = 35550575) B35550575
theorem B15800255 : Blo 1947435 15800255 := bstep (se 1 (by rfl) ⟨11850191, by rfl⟩ : syracuseStep 15800255 = 23700383) B23700383
theorem B10533503 : Blo 1947435 10533503 := bstep (se 1 (by rfl) ⟨7900127, by rfl⟩ : syracuseStep 10533503 = 15800255) B15800255
theorem B7022335 : Blo 1947435 7022335 := bstep (se 1 (by rfl) ⟨5266751, by rfl⟩ : syracuseStep 7022335 = 10533503) B10533503
theorem B9363113 : Blo 1947435 9363113 := bstep (se 2 (by rfl) ⟨3511167, by rfl⟩ : syracuseStep 9363113 = 7022335) B7022335
theorem B6242075 : Blo 1947435 6242075 := bstep (se 1 (by rfl) ⟨4681556, by rfl⟩ : syracuseStep 6242075 = 9363113) B9363113
theorem B4161383 : Blo 1947435 4161383 := bstep (se 1 (by rfl) ⟨3121037, by rfl⟩ : syracuseStep 4161383 = 6242075) B6242075
theorem B2774255 : Blo 1947435 2774255 := bstep (se 1 (by rfl) ⟨2080691, by rfl⟩ : syracuseStep 2774255 = 4161383) B4161383
theorem B7398013 : Blo 1947435 7398013 := bstep (se 3 (by rfl) ⟨1387127, by rfl⟩ : syracuseStep 7398013 = 2774255) B2774255
theorem B9864017 : Blo 1947435 9864017 := bstep (se 2 (by rfl) ⟨3699006, by rfl⟩ : syracuseStep 9864017 = 7398013) B7398013
theorem B6576011 : Blo 1947435 6576011 := bstep (se 1 (by rfl) ⟨4932008, by rfl⟩ : syracuseStep 6576011 = 9864017) B9864017
theorem B4384007 : Blo 1947435 4384007 := bstep (se 1 (by rfl) ⟨3288005, by rfl⟩ : syracuseStep 4384007 = 6576011) B6576011
theorem B2922671 : Blo 1947435 2922671 := bstep (se 1 (by rfl) ⟨2192003, by rfl⟩ : syracuseStep 2922671 = 4384007) B4384007
theorem B1948447 : Blo 1947435 1948447 := bstep (se 1 (by rfl) ⟨1461335, by rfl⟩ : syracuseStep 1948447 = 2922671) B2922671
theorem B2922677 : Blo 1947435 2922677 := bbase (se 5 (by rfl) ⟨137000, by rfl⟩ : syracuseStep 2922677 = 274001) (by norm_num)
theorem B1948451 : Blo 1947435 1948451 := bstep (se 1 (by rfl) ⟨1461338, by rfl⟩ : syracuseStep 1948451 = 2922677) B2922677
theorem B4932029 : Blo 1947435 4932029 := bbase (se 3 (by rfl) ⟨924755, by rfl⟩ : syracuseStep 4932029 = 1849511) (by norm_num)
theorem B3288019 : Blo 1947435 3288019 := bstep (se 1 (by rfl) ⟨2466014, by rfl⟩ : syracuseStep 3288019 = 4932029) B4932029
theorem B4384025 : Blo 1947435 4384025 := bstep (se 2 (by rfl) ⟨1644009, by rfl⟩ : syracuseStep 4384025 = 3288019) B3288019
theorem B2922683 : Blo 1947435 2922683 := bstep (se 1 (by rfl) ⟨2192012, by rfl⟩ : syracuseStep 2922683 = 4384025) B4384025
theorem B1948455 : Blo 1947435 1948455 := bstep (se 1 (by rfl) ⟨1461341, by rfl⟩ : syracuseStep 1948455 = 2922683) B2922683
theorem B2192017 : Blo 1947435 2192017 := bbase (se 2 (by rfl) ⟨822006, by rfl⟩ : syracuseStep 2192017 = 1644013) (by norm_num)
theorem B2922689 : Blo 1947435 2922689 := bstep (se 2 (by rfl) ⟨1096008, by rfl⟩ : syracuseStep 2922689 = 2192017) B2192017
theorem B1948459 : Blo 1947435 1948459 := bstep (se 1 (by rfl) ⟨1461344, by rfl⟩ : syracuseStep 1948459 = 2922689) B2922689
theorem B3699037 : Blo 1947435 3699037 := bbase (se 3 (by rfl) ⟨693569, by rfl⟩ : syracuseStep 3699037 = 1387139) (by norm_num)
theorem B4932049 : Blo 1947435 4932049 := bstep (se 2 (by rfl) ⟨1849518, by rfl⟩ : syracuseStep 4932049 = 3699037) B3699037
theorem B6576065 : Blo 1947435 6576065 := bstep (se 2 (by rfl) ⟨2466024, by rfl⟩ : syracuseStep 6576065 = 4932049) B4932049
theorem B4384043 : Blo 1947435 4384043 := bstep (se 1 (by rfl) ⟨3288032, by rfl⟩ : syracuseStep 4384043 = 6576065) B6576065
theorem B2922695 : Blo 1947435 2922695 := bstep (se 1 (by rfl) ⟨2192021, by rfl⟩ : syracuseStep 2922695 = 4384043) B4384043
theorem B1948463 : Blo 1947435 1948463 := bstep (se 1 (by rfl) ⟨1461347, by rfl⟩ : syracuseStep 1948463 = 2922695) B2922695
theorem B2922701 : Blo 1947435 2922701 := bbase (se 3 (by rfl) ⟨548006, by rfl⟩ : syracuseStep 2922701 = 1096013) (by norm_num)
theorem B1948467 : Blo 1947435 1948467 := bstep (se 1 (by rfl) ⟨1461350, by rfl⟩ : syracuseStep 1948467 = 2922701) B2922701
theorem B4384061 : Blo 1947435 4384061 := bbase (se 3 (by rfl) ⟨822011, by rfl⟩ : syracuseStep 4384061 = 1644023) (by norm_num)
theorem B2922707 : Blo 1947435 2922707 := bstep (se 1 (by rfl) ⟨2192030, by rfl⟩ : syracuseStep 2922707 = 4384061) B4384061
theorem B1948471 : Blo 1947435 1948471 := bstep (se 1 (by rfl) ⟨1461353, by rfl⟩ : syracuseStep 1948471 = 2922707) B2922707
theorem B3288053 : Blo 1947435 3288053 := bbase (se 5 (by rfl) ⟨154127, by rfl⟩ : syracuseStep 3288053 = 308255) (by norm_num)
theorem B2192035 : Blo 1947435 2192035 := bstep (se 1 (by rfl) ⟨1644026, by rfl⟩ : syracuseStep 2192035 = 3288053) B3288053
theorem B2922713 : Blo 1947435 2922713 := bstep (se 2 (by rfl) ⟨1096017, by rfl⟩ : syracuseStep 2922713 = 2192035) B2192035
theorem B1948475 : Blo 1947435 1948475 := bstep (se 1 (by rfl) ⟨1461356, by rfl⟩ : syracuseStep 1948475 = 2922713) B2922713
theorem B2962597 : Blo 1947435 2962597 := bbase (se 4 (by rfl) ⟨277743, by rfl⟩ : syracuseStep 2962597 = 555487) (by norm_num)
theorem B3950129 : Blo 1947435 3950129 := bstep (se 2 (by rfl) ⟨1481298, by rfl⟩ : syracuseStep 3950129 = 2962597) B2962597
theorem B2633419 : Blo 1947435 2633419 := bstep (se 1 (by rfl) ⟨1975064, by rfl⟩ : syracuseStep 2633419 = 3950129) B3950129
theorem B3511225 : Blo 1947435 3511225 := bstep (se 2 (by rfl) ⟨1316709, by rfl⟩ : syracuseStep 3511225 = 2633419) B2633419
theorem B4681633 : Blo 1947435 4681633 := bstep (se 2 (by rfl) ⟨1755612, by rfl⟩ : syracuseStep 4681633 = 3511225) B3511225
theorem B6242177 : Blo 1947435 6242177 := bstep (se 2 (by rfl) ⟨2340816, by rfl⟩ : syracuseStep 6242177 = 4681633) B4681633
theorem B4161451 : Blo 1947435 4161451 := bstep (se 1 (by rfl) ⟨3121088, by rfl⟩ : syracuseStep 4161451 = 6242177) B6242177
theorem B5548601 : Blo 1947435 5548601 := bstep (se 2 (by rfl) ⟨2080725, by rfl⟩ : syracuseStep 5548601 = 4161451) B4161451
theorem B14796269 : Blo 1947435 14796269 := bstep (se 3 (by rfl) ⟨2774300, by rfl⟩ : syracuseStep 14796269 = 5548601) B5548601
theorem B9864179 : Blo 1947435 9864179 := bstep (se 1 (by rfl) ⟨7398134, by rfl⟩ : syracuseStep 9864179 = 14796269) B14796269
theorem B6576119 : Blo 1947435 6576119 := bstep (se 1 (by rfl) ⟨4932089, by rfl⟩ : syracuseStep 6576119 = 9864179) B9864179
theorem B4384079 : Blo 1947435 4384079 := bstep (se 1 (by rfl) ⟨3288059, by rfl⟩ : syracuseStep 4384079 = 6576119) B6576119
theorem B2922719 : Blo 1947435 2922719 := bstep (se 1 (by rfl) ⟨2192039, by rfl⟩ : syracuseStep 2922719 = 4384079) B4384079
theorem B1948479 : Blo 1947435 1948479 := bstep (se 1 (by rfl) ⟨1461359, by rfl⟩ : syracuseStep 1948479 = 2922719) B2922719
theorem B2922725 : Blo 1947435 2922725 := bbase (se 4 (by rfl) ⟨274005, by rfl⟩ : syracuseStep 2922725 = 548011) (by norm_num)
theorem B1948483 : Blo 1947435 1948483 := bstep (se 1 (by rfl) ⟨1461362, by rfl⟩ : syracuseStep 1948483 = 2922725) B2922725
theorem B4161469 : Blo 1947435 4161469 := bbase (se 3 (by rfl) ⟨780275, by rfl⟩ : syracuseStep 4161469 = 1560551) (by norm_num)
theorem B5548625 : Blo 1947435 5548625 := bstep (se 2 (by rfl) ⟨2080734, by rfl⟩ : syracuseStep 5548625 = 4161469) B4161469
theorem B3699083 : Blo 1947435 3699083 := bstep (se 1 (by rfl) ⟨2774312, by rfl⟩ : syracuseStep 3699083 = 5548625) B5548625
theorem B2466055 : Blo 1947435 2466055 := bstep (se 1 (by rfl) ⟨1849541, by rfl⟩ : syracuseStep 2466055 = 3699083) B3699083
theorem B3288073 : Blo 1947435 3288073 := bstep (se 2 (by rfl) ⟨1233027, by rfl⟩ : syracuseStep 3288073 = 2466055) B2466055
theorem B4384097 : Blo 1947435 4384097 := bstep (se 2 (by rfl) ⟨1644036, by rfl⟩ : syracuseStep 4384097 = 3288073) B3288073
theorem B2922731 : Blo 1947435 2922731 := bstep (se 1 (by rfl) ⟨2192048, by rfl⟩ : syracuseStep 2922731 = 4384097) B4384097
theorem B1948487 : Blo 1947435 1948487 := bstep (se 1 (by rfl) ⟨1461365, by rfl⟩ : syracuseStep 1948487 = 2922731) B2922731
theorem B2192053 : Blo 1947435 2192053 := bbase (se 5 (by rfl) ⟨102752, by rfl⟩ : syracuseStep 2192053 = 205505) (by norm_num)
theorem B2922737 : Blo 1947435 2922737 := bstep (se 2 (by rfl) ⟨1096026, by rfl⟩ : syracuseStep 2922737 = 2192053) B2192053
theorem B1948491 : Blo 1947435 1948491 := bstep (se 1 (by rfl) ⟨1461368, by rfl⟩ : syracuseStep 1948491 = 2922737) B2922737
theorem B2466065 : Blo 1947435 2466065 := bbase (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) (by norm_num)
theorem B6576173 : Blo 1947435 6576173 := bstep (se 3 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 6576173 = 2466065) B2466065
theorem B4384115 : Blo 1947435 4384115 := bstep (se 1 (by rfl) ⟨3288086, by rfl⟩ : syracuseStep 4384115 = 6576173) B6576173
theorem B2922743 : Blo 1947435 2922743 := bstep (se 1 (by rfl) ⟨2192057, by rfl⟩ : syracuseStep 2922743 = 4384115) B4384115
theorem B1948495 : Blo 1947435 1948495 := bstep (se 1 (by rfl) ⟨1461371, by rfl⟩ : syracuseStep 1948495 = 2922743) B2922743
theorem B2922749 : Blo 1947435 2922749 := bbase (se 3 (by rfl) ⟨548015, by rfl⟩ : syracuseStep 2922749 = 1096031) (by norm_num)
theorem B1948499 : Blo 1947435 1948499 := bstep (se 1 (by rfl) ⟨1461374, by rfl⟩ : syracuseStep 1948499 = 2922749) B2922749
theorem B4384133 : Blo 1947435 4384133 := bbase (se 4 (by rfl) ⟨411012, by rfl⟩ : syracuseStep 4384133 = 822025) (by norm_num)
theorem B2922755 : Blo 1947435 2922755 := bstep (se 1 (by rfl) ⟨2192066, by rfl⟩ : syracuseStep 2922755 = 4384133) B4384133
theorem B1948503 : Blo 1947435 1948503 := bstep (se 1 (by rfl) ⟨1461377, by rfl⟩ : syracuseStep 1948503 = 2922755) B2922755
theorem B2774341 : Blo 1947435 2774341 := bbase (se 4 (by rfl) ⟨260094, by rfl⟩ : syracuseStep 2774341 = 520189) (by norm_num)
theorem B3699121 : Blo 1947435 3699121 := bstep (se 2 (by rfl) ⟨1387170, by rfl⟩ : syracuseStep 3699121 = 2774341) B2774341
theorem B4932161 : Blo 1947435 4932161 := bstep (se 2 (by rfl) ⟨1849560, by rfl⟩ : syracuseStep 4932161 = 3699121) B3699121
theorem B3288107 : Blo 1947435 3288107 := bstep (se 1 (by rfl) ⟨2466080, by rfl⟩ : syracuseStep 3288107 = 4932161) B4932161
theorem B2192071 : Blo 1947435 2192071 := bstep (se 1 (by rfl) ⟨1644053, by rfl⟩ : syracuseStep 2192071 = 3288107) B3288107
theorem B2922761 : Blo 1947435 2922761 := bstep (se 2 (by rfl) ⟨1096035, by rfl⟩ : syracuseStep 2922761 = 2192071) B2192071
theorem B1948507 : Blo 1947435 1948507 := bstep (se 1 (by rfl) ⟨1461380, by rfl⟩ : syracuseStep 1948507 = 2922761) B2922761
theorem B9864341 : Blo 1947435 9864341 := bbase (se 6 (by rfl) ⟨231195, by rfl⟩ : syracuseStep 9864341 = 462391) (by norm_num)
theorem B6576227 : Blo 1947435 6576227 := bstep (se 1 (by rfl) ⟨4932170, by rfl⟩ : syracuseStep 6576227 = 9864341) B9864341
theorem B4384151 : Blo 1947435 4384151 := bstep (se 1 (by rfl) ⟨3288113, by rfl⟩ : syracuseStep 4384151 = 6576227) B6576227
theorem B2922767 : Blo 1947435 2922767 := bstep (se 1 (by rfl) ⟨2192075, by rfl⟩ : syracuseStep 2922767 = 4384151) B4384151
theorem B1948511 : Blo 1947435 1948511 := bstep (se 1 (by rfl) ⟨1461383, by rfl⟩ : syracuseStep 1948511 = 2922767) B2922767
theorem B2922773 : Blo 1947435 2922773 := bbase (se 6 (by rfl) ⟨68502, by rfl⟩ : syracuseStep 2922773 = 137005) (by norm_num)
theorem B1948515 : Blo 1947435 1948515 := bstep (se 1 (by rfl) ⟨1461386, by rfl⟩ : syracuseStep 1948515 = 2922773) B2922773
theorem B1975105 : Blo 1947435 1975105 := bbase (se 2 (by rfl) ⟨740664, by rfl⟩ : syracuseStep 1975105 = 1481329) (by norm_num)
theorem B2633473 : Blo 1947435 2633473 := bstep (se 2 (by rfl) ⟨987552, by rfl⟩ : syracuseStep 2633473 = 1975105) B1975105
theorem B3511297 : Blo 1947435 3511297 := bstep (se 2 (by rfl) ⟨1316736, by rfl⟩ : syracuseStep 3511297 = 2633473) B2633473
theorem B4681729 : Blo 1947435 4681729 := bstep (se 2 (by rfl) ⟨1755648, by rfl⟩ : syracuseStep 4681729 = 3511297) B3511297
theorem B24969221 : Blo 1947435 24969221 := bstep (se 4 (by rfl) ⟨2340864, by rfl⟩ : syracuseStep 24969221 = 4681729) B4681729
theorem B16646147 : Blo 1947435 16646147 := bstep (se 1 (by rfl) ⟨12484610, by rfl⟩ : syracuseStep 16646147 = 24969221) B24969221
theorem B11097431 : Blo 1947435 11097431 := bstep (se 1 (by rfl) ⟨8323073, by rfl⟩ : syracuseStep 11097431 = 16646147) B16646147
theorem B7398287 : Blo 1947435 7398287 := bstep (se 1 (by rfl) ⟨5548715, by rfl⟩ : syracuseStep 7398287 = 11097431) B11097431
theorem B4932191 : Blo 1947435 4932191 := bstep (se 1 (by rfl) ⟨3699143, by rfl⟩ : syracuseStep 4932191 = 7398287) B7398287
theorem B3288127 : Blo 1947435 3288127 := bstep (se 1 (by rfl) ⟨2466095, by rfl⟩ : syracuseStep 3288127 = 4932191) B4932191
theorem B4384169 : Blo 1947435 4384169 := bstep (se 2 (by rfl) ⟨1644063, by rfl⟩ : syracuseStep 4384169 = 3288127) B3288127
theorem B2922779 : Blo 1947435 2922779 := bstep (se 1 (by rfl) ⟨2192084, by rfl⟩ : syracuseStep 2922779 = 4384169) B4384169
theorem B1948519 : Blo 1947435 1948519 := bstep (se 1 (by rfl) ⟨1461389, by rfl⟩ : syracuseStep 1948519 = 2922779) B2922779
theorem B2192089 : Blo 1947435 2192089 := bbase (se 2 (by rfl) ⟨822033, by rfl⟩ : syracuseStep 2192089 = 1644067) (by norm_num)
theorem B2922785 : Blo 1947435 2922785 := bstep (se 2 (by rfl) ⟨1096044, by rfl⟩ : syracuseStep 2922785 = 2192089) B2192089
theorem B1948523 : Blo 1947435 1948523 := bstep (se 1 (by rfl) ⟨1461392, by rfl⟩ : syracuseStep 1948523 = 2922785) B2922785
theorem B2080777 : Blo 1947435 2080777 := bbase (se 2 (by rfl) ⟨780291, by rfl⟩ : syracuseStep 2080777 = 1560583) (by norm_num)
theorem B2774369 : Blo 1947435 2774369 := bstep (se 2 (by rfl) ⟨1040388, by rfl⟩ : syracuseStep 2774369 = 2080777) B2080777
theorem B7398317 : Blo 1947435 7398317 := bstep (se 3 (by rfl) ⟨1387184, by rfl⟩ : syracuseStep 7398317 = 2774369) B2774369
theorem B4932211 : Blo 1947435 4932211 := bstep (se 1 (by rfl) ⟨3699158, by rfl⟩ : syracuseStep 4932211 = 7398317) B7398317
theorem B6576281 : Blo 1947435 6576281 := bstep (se 2 (by rfl) ⟨2466105, by rfl⟩ : syracuseStep 6576281 = 4932211) B4932211
theorem B4384187 : Blo 1947435 4384187 := bstep (se 1 (by rfl) ⟨3288140, by rfl⟩ : syracuseStep 4384187 = 6576281) B6576281
theorem B2922791 : Blo 1947435 2922791 := bstep (se 1 (by rfl) ⟨2192093, by rfl⟩ : syracuseStep 2922791 = 4384187) B4384187
theorem B1948527 : Blo 1947435 1948527 := bstep (se 1 (by rfl) ⟨1461395, by rfl⟩ : syracuseStep 1948527 = 2922791) B2922791
theorem B2922797 : Blo 1947435 2922797 := bbase (se 3 (by rfl) ⟨548024, by rfl⟩ : syracuseStep 2922797 = 1096049) (by norm_num)
theorem B1948531 : Blo 1947435 1948531 := bstep (se 1 (by rfl) ⟨1461398, by rfl⟩ : syracuseStep 1948531 = 2922797) B2922797
theorem B4384205 : Blo 1947435 4384205 := bbase (se 3 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 4384205 = 1644077) (by norm_num)
theorem B2922803 : Blo 1947435 2922803 := bstep (se 1 (by rfl) ⟨2192102, by rfl⟩ : syracuseStep 2922803 = 4384205) B4384205
theorem B1948535 : Blo 1947435 1948535 := bstep (se 1 (by rfl) ⟨1461401, by rfl⟩ : syracuseStep 1948535 = 2922803) B2922803
theorem B2466121 : Blo 1947435 2466121 := bbase (se 2 (by rfl) ⟨924795, by rfl⟩ : syracuseStep 2466121 = 1849591) (by norm_num)
theorem B3288161 : Blo 1947435 3288161 := bstep (se 2 (by rfl) ⟨1233060, by rfl⟩ : syracuseStep 3288161 = 2466121) B2466121
theorem B2192107 : Blo 1947435 2192107 := bstep (se 1 (by rfl) ⟨1644080, by rfl⟩ : syracuseStep 2192107 = 3288161) B3288161
theorem B2922809 : Blo 1947435 2922809 := bstep (se 2 (by rfl) ⟨1096053, by rfl⟩ : syracuseStep 2922809 = 2192107) B2192107
theorem B1948539 : Blo 1947435 1948539 := bstep (se 1 (by rfl) ⟨1461404, by rfl⟩ : syracuseStep 1948539 = 2922809) B2922809
theorem B29997269 : Blo 1947435 29997269 := bbase (se 7 (by rfl) ⟨351530, by rfl⟩ : syracuseStep 29997269 = 703061) (by norm_num)
theorem B19998179 : Blo 1947435 19998179 := bstep (se 1 (by rfl) ⟨14998634, by rfl⟩ : syracuseStep 19998179 = 29997269) B29997269
theorem B13332119 : Blo 1947435 13332119 := bstep (se 1 (by rfl) ⟨9999089, by rfl⟩ : syracuseStep 13332119 = 19998179) B19998179
theorem B35552317 : Blo 1947435 35552317 := bstep (se 3 (by rfl) ⟨6666059, by rfl⟩ : syracuseStep 35552317 = 13332119) B13332119
theorem B47403089 : Blo 1947435 47403089 := bstep (se 2 (by rfl) ⟨17776158, by rfl⟩ : syracuseStep 47403089 = 35552317) B35552317
theorem B31602059 : Blo 1947435 31602059 := bstep (se 1 (by rfl) ⟨23701544, by rfl⟩ : syracuseStep 31602059 = 47403089) B47403089
theorem B21068039 : Blo 1947435 21068039 := bstep (se 1 (by rfl) ⟨15801029, by rfl⟩ : syracuseStep 21068039 = 31602059) B31602059
theorem B14045359 : Blo 1947435 14045359 := bstep (se 1 (by rfl) ⟨10534019, by rfl⟩ : syracuseStep 14045359 = 21068039) B21068039
theorem B18727145 : Blo 1947435 18727145 := bstep (se 2 (by rfl) ⟨7022679, by rfl⟩ : syracuseStep 18727145 = 14045359) B14045359
theorem B12484763 : Blo 1947435 12484763 := bstep (se 1 (by rfl) ⟨9363572, by rfl⟩ : syracuseStep 12484763 = 18727145) B18727145
theorem B8323175 : Blo 1947435 8323175 := bstep (se 1 (by rfl) ⟨6242381, by rfl⟩ : syracuseStep 8323175 = 12484763) B12484763
theorem B22195133 : Blo 1947435 22195133 := bstep (se 3 (by rfl) ⟨4161587, by rfl⟩ : syracuseStep 22195133 = 8323175) B8323175
theorem B14796755 : Blo 1947435 14796755 := bstep (se 1 (by rfl) ⟨11097566, by rfl⟩ : syracuseStep 14796755 = 22195133) B22195133
theorem B9864503 : Blo 1947435 9864503 := bstep (se 1 (by rfl) ⟨7398377, by rfl⟩ : syracuseStep 9864503 = 14796755) B14796755
theorem B6576335 : Blo 1947435 6576335 := bstep (se 1 (by rfl) ⟨4932251, by rfl⟩ : syracuseStep 6576335 = 9864503) B9864503
theorem B4384223 : Blo 1947435 4384223 := bstep (se 1 (by rfl) ⟨3288167, by rfl⟩ : syracuseStep 4384223 = 6576335) B6576335
theorem B2922815 : Blo 1947435 2922815 := bstep (se 1 (by rfl) ⟨2192111, by rfl⟩ : syracuseStep 2922815 = 4384223) B4384223
theorem B1948543 : Blo 1947435 1948543 := bstep (se 1 (by rfl) ⟨1461407, by rfl⟩ : syracuseStep 1948543 = 2922815) B2922815
theorem B2922821 : Blo 1947435 2922821 := bbase (se 4 (by rfl) ⟨274014, by rfl⟩ : syracuseStep 2922821 = 548029) (by norm_num)
theorem B1948547 : Blo 1947435 1948547 := bstep (se 1 (by rfl) ⟨1461410, by rfl⟩ : syracuseStep 1948547 = 2922821) B2922821
theorem B3288181 : Blo 1947435 3288181 := bbase (se 5 (by rfl) ⟨154133, by rfl⟩ : syracuseStep 3288181 = 308267) (by norm_num)
theorem B4384241 : Blo 1947435 4384241 := bstep (se 2 (by rfl) ⟨1644090, by rfl⟩ : syracuseStep 4384241 = 3288181) B3288181
theorem B2922827 : Blo 1947435 2922827 := bstep (se 1 (by rfl) ⟨2192120, by rfl⟩ : syracuseStep 2922827 = 4384241) B4384241
theorem B1948551 : Blo 1947435 1948551 := bstep (se 1 (by rfl) ⟨1461413, by rfl⟩ : syracuseStep 1948551 = 2922827) B2922827
theorem B2192125 : Blo 1947435 2192125 := bbase (se 3 (by rfl) ⟨411023, by rfl⟩ : syracuseStep 2192125 = 822047) (by norm_num)
theorem B2922833 : Blo 1947435 2922833 := bstep (se 2 (by rfl) ⟨1096062, by rfl⟩ : syracuseStep 2922833 = 2192125) B2192125
theorem B1948555 : Blo 1947435 1948555 := bstep (se 1 (by rfl) ⟨1461416, by rfl⟩ : syracuseStep 1948555 = 2922833) B2922833
theorem B6576389 : Blo 1947435 6576389 := bbase (se 4 (by rfl) ⟨616536, by rfl⟩ : syracuseStep 6576389 = 1233073) (by norm_num)
theorem B4384259 : Blo 1947435 4384259 := bstep (se 1 (by rfl) ⟨3288194, by rfl⟩ : syracuseStep 4384259 = 6576389) B6576389
theorem B2922839 : Blo 1947435 2922839 := bstep (se 1 (by rfl) ⟨2192129, by rfl⟩ : syracuseStep 2922839 = 4384259) B4384259
theorem B1948559 : Blo 1947435 1948559 := bstep (se 1 (by rfl) ⟨1461419, by rfl⟩ : syracuseStep 1948559 = 2922839) B2922839
theorem B2922845 : Blo 1947435 2922845 := bbase (se 3 (by rfl) ⟨548033, by rfl⟩ : syracuseStep 2922845 = 1096067) (by norm_num)
theorem B1948563 : Blo 1947435 1948563 := bstep (se 1 (by rfl) ⟨1461422, by rfl⟩ : syracuseStep 1948563 = 2922845) B2922845
theorem B4384277 : Blo 1947435 4384277 := bbase (se 6 (by rfl) ⟨102756, by rfl⟩ : syracuseStep 4384277 = 205513) (by norm_num)
theorem B2922851 : Blo 1947435 2922851 := bstep (se 1 (by rfl) ⟨2192138, by rfl⟩ : syracuseStep 2922851 = 4384277) B4384277
theorem B1948567 : Blo 1947435 1948567 := bstep (se 1 (by rfl) ⟨1461425, by rfl⟩ : syracuseStep 1948567 = 2922851) B2922851
theorem B7398485 : Blo 1947435 7398485 := bbase (se 8 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 7398485 = 86701) (by norm_num)
theorem B4932323 : Blo 1947435 4932323 := bstep (se 1 (by rfl) ⟨3699242, by rfl⟩ : syracuseStep 4932323 = 7398485) B7398485
theorem B3288215 : Blo 1947435 3288215 := bstep (se 1 (by rfl) ⟨2466161, by rfl⟩ : syracuseStep 3288215 = 4932323) B4932323
theorem B2192143 : Blo 1947435 2192143 := bstep (se 1 (by rfl) ⟨1644107, by rfl⟩ : syracuseStep 2192143 = 3288215) B3288215
theorem B2922857 : Blo 1947435 2922857 := bstep (se 2 (by rfl) ⟨1096071, by rfl⟩ : syracuseStep 2922857 = 2192143) B2192143
theorem B1948571 : Blo 1947435 1948571 := bstep (se 1 (by rfl) ⟨1461428, by rfl⟩ : syracuseStep 1948571 = 2922857) B2922857
theorem B11097749 : Blo 1947435 11097749 := bbase (se 6 (by rfl) ⟨260103, by rfl⟩ : syracuseStep 11097749 = 520207) (by norm_num)
theorem B7398499 : Blo 1947435 7398499 := bstep (se 1 (by rfl) ⟨5548874, by rfl⟩ : syracuseStep 7398499 = 11097749) B11097749
theorem B9864665 : Blo 1947435 9864665 := bstep (se 2 (by rfl) ⟨3699249, by rfl⟩ : syracuseStep 9864665 = 7398499) B7398499
theorem B6576443 : Blo 1947435 6576443 := bstep (se 1 (by rfl) ⟨4932332, by rfl⟩ : syracuseStep 6576443 = 9864665) B9864665
theorem B4384295 : Blo 1947435 4384295 := bstep (se 1 (by rfl) ⟨3288221, by rfl⟩ : syracuseStep 4384295 = 6576443) B6576443
theorem B2922863 : Blo 1947435 2922863 := bstep (se 1 (by rfl) ⟨2192147, by rfl⟩ : syracuseStep 2922863 = 4384295) B4384295
theorem B1948575 : Blo 1947435 1948575 := bstep (se 1 (by rfl) ⟨1461431, by rfl⟩ : syracuseStep 1948575 = 2922863) B2922863
theorem B2922869 : Blo 1947435 2922869 := bbase (se 5 (by rfl) ⟨137009, by rfl⟩ : syracuseStep 2922869 = 274019) (by norm_num)
theorem B1948579 : Blo 1947435 1948579 := bstep (se 1 (by rfl) ⟨1461434, by rfl⟩ : syracuseStep 1948579 = 2922869) B2922869
theorem B2080837 : Blo 1947435 2080837 := bbase (se 4 (by rfl) ⟨195078, by rfl⟩ : syracuseStep 2080837 = 390157) (by norm_num)
theorem B2774449 : Blo 1947435 2774449 := bstep (se 2 (by rfl) ⟨1040418, by rfl⟩ : syracuseStep 2774449 = 2080837) B2080837
theorem B3699265 : Blo 1947435 3699265 := bstep (se 2 (by rfl) ⟨1387224, by rfl⟩ : syracuseStep 3699265 = 2774449) B2774449
theorem B4932353 : Blo 1947435 4932353 := bstep (se 2 (by rfl) ⟨1849632, by rfl⟩ : syracuseStep 4932353 = 3699265) B3699265
theorem B3288235 : Blo 1947435 3288235 := bstep (se 1 (by rfl) ⟨2466176, by rfl⟩ : syracuseStep 3288235 = 4932353) B4932353
theorem B4384313 : Blo 1947435 4384313 := bstep (se 2 (by rfl) ⟨1644117, by rfl⟩ : syracuseStep 4384313 = 3288235) B3288235
theorem B2922875 : Blo 1947435 2922875 := bstep (se 1 (by rfl) ⟨2192156, by rfl⟩ : syracuseStep 2922875 = 4384313) B4384313
theorem B1948583 : Blo 1947435 1948583 := bstep (se 1 (by rfl) ⟨1461437, by rfl⟩ : syracuseStep 1948583 = 2922875) B2922875
theorem B2192161 : Blo 1947435 2192161 := bbase (se 2 (by rfl) ⟨822060, by rfl⟩ : syracuseStep 2192161 = 1644121) (by norm_num)
theorem B2922881 : Blo 1947435 2922881 := bstep (se 2 (by rfl) ⟨1096080, by rfl⟩ : syracuseStep 2922881 = 2192161) B2192161
theorem B1948587 : Blo 1947435 1948587 := bstep (se 1 (by rfl) ⟨1461440, by rfl⟩ : syracuseStep 1948587 = 2922881) B2922881
theorem B4932373 : Blo 1947435 4932373 := bbase (se 6 (by rfl) ⟨115602, by rfl⟩ : syracuseStep 4932373 = 231205) (by norm_num)
theorem B6576497 : Blo 1947435 6576497 := bstep (se 2 (by rfl) ⟨2466186, by rfl⟩ : syracuseStep 6576497 = 4932373) B4932373
theorem B4384331 : Blo 1947435 4384331 := bstep (se 1 (by rfl) ⟨3288248, by rfl⟩ : syracuseStep 4384331 = 6576497) B6576497
theorem B2922887 : Blo 1947435 2922887 := bstep (se 1 (by rfl) ⟨2192165, by rfl⟩ : syracuseStep 2922887 = 4384331) B4384331
theorem B1948591 : Blo 1947435 1948591 := bstep (se 1 (by rfl) ⟨1461443, by rfl⟩ : syracuseStep 1948591 = 2922887) B2922887
theorem B2922893 : Blo 1947435 2922893 := bbase (se 3 (by rfl) ⟨548042, by rfl⟩ : syracuseStep 2922893 = 1096085) (by norm_num)
theorem B1948595 : Blo 1947435 1948595 := bstep (se 1 (by rfl) ⟨1461446, by rfl⟩ : syracuseStep 1948595 = 2922893) B2922893
theorem B4384349 : Blo 1947435 4384349 := bbase (se 3 (by rfl) ⟨822065, by rfl⟩ : syracuseStep 4384349 = 1644131) (by norm_num)
theorem B2922899 : Blo 1947435 2922899 := bstep (se 1 (by rfl) ⟨2192174, by rfl⟩ : syracuseStep 2922899 = 4384349) B4384349
theorem B1948599 : Blo 1947435 1948599 := bstep (se 1 (by rfl) ⟨1461449, by rfl⟩ : syracuseStep 1948599 = 2922899) B2922899
theorem B3288269 : Blo 1947435 3288269 := bbase (se 3 (by rfl) ⟨616550, by rfl⟩ : syracuseStep 3288269 = 1233101) (by norm_num)
theorem B2192179 : Blo 1947435 2192179 := bstep (se 1 (by rfl) ⟨1644134, by rfl⟩ : syracuseStep 2192179 = 3288269) B3288269
theorem B2922905 : Blo 1947435 2922905 := bstep (se 2 (by rfl) ⟨1096089, by rfl⟩ : syracuseStep 2922905 = 2192179) B2192179
theorem B1948603 : Blo 1947435 1948603 := bstep (se 1 (by rfl) ⟨1461452, by rfl⟩ : syracuseStep 1948603 = 2922905) B2922905
theorem B12485173 : Blo 1947435 12485173 := bbase (se 5 (by rfl) ⟨585242, by rfl⟩ : syracuseStep 12485173 = 1170485) (by norm_num)
theorem B16646897 : Blo 1947435 16646897 := bstep (se 2 (by rfl) ⟨6242586, by rfl⟩ : syracuseStep 16646897 = 12485173) B12485173
theorem B11097931 : Blo 1947435 11097931 := bstep (se 1 (by rfl) ⟨8323448, by rfl⟩ : syracuseStep 11097931 = 16646897) B16646897
theorem B14797241 : Blo 1947435 14797241 := bstep (se 2 (by rfl) ⟨5548965, by rfl⟩ : syracuseStep 14797241 = 11097931) B11097931
theorem B9864827 : Blo 1947435 9864827 := bstep (se 1 (by rfl) ⟨7398620, by rfl⟩ : syracuseStep 9864827 = 14797241) B14797241
theorem B6576551 : Blo 1947435 6576551 := bstep (se 1 (by rfl) ⟨4932413, by rfl⟩ : syracuseStep 6576551 = 9864827) B9864827
theorem B4384367 : Blo 1947435 4384367 := bstep (se 1 (by rfl) ⟨3288275, by rfl⟩ : syracuseStep 4384367 = 6576551) B6576551
theorem B2922911 : Blo 1947435 2922911 := bstep (se 1 (by rfl) ⟨2192183, by rfl⟩ : syracuseStep 2922911 = 4384367) B4384367
theorem B1948607 : Blo 1947435 1948607 := bstep (se 1 (by rfl) ⟨1461455, by rfl⟩ : syracuseStep 1948607 = 2922911) B2922911
theorem B2922917 : Blo 1947435 2922917 := bbase (se 4 (by rfl) ⟨274023, by rfl⟩ : syracuseStep 2922917 = 548047) (by norm_num)
theorem B1948611 : Blo 1947435 1948611 := bstep (se 1 (by rfl) ⟨1461458, by rfl⟩ : syracuseStep 1948611 = 2922917) B2922917
theorem B2466217 : Blo 1947435 2466217 := bbase (se 2 (by rfl) ⟨924831, by rfl⟩ : syracuseStep 2466217 = 1849663) (by norm_num)
theorem B3288289 : Blo 1947435 3288289 := bstep (se 2 (by rfl) ⟨1233108, by rfl⟩ : syracuseStep 3288289 = 2466217) B2466217
theorem B4384385 : Blo 1947435 4384385 := bstep (se 2 (by rfl) ⟨1644144, by rfl⟩ : syracuseStep 4384385 = 3288289) B3288289
theorem B2922923 : Blo 1947435 2922923 := bstep (se 1 (by rfl) ⟨2192192, by rfl⟩ : syracuseStep 2922923 = 4384385) B4384385
theorem B1948615 : Blo 1947435 1948615 := bstep (se 1 (by rfl) ⟨1461461, by rfl⟩ : syracuseStep 1948615 = 2922923) B2922923
theorem B2192197 : Blo 1947435 2192197 := bbase (se 4 (by rfl) ⟨205518, by rfl⟩ : syracuseStep 2192197 = 411037) (by norm_num)
theorem B2922929 : Blo 1947435 2922929 := bstep (se 2 (by rfl) ⟨1096098, by rfl⟩ : syracuseStep 2922929 = 2192197) B2192197
theorem B1948619 : Blo 1947435 1948619 := bstep (se 1 (by rfl) ⟨1461464, by rfl⟩ : syracuseStep 1948619 = 2922929) B2922929
theorem B3699341 : Blo 1947435 3699341 := bbase (se 3 (by rfl) ⟨693626, by rfl⟩ : syracuseStep 3699341 = 1387253) (by norm_num)
theorem B2466227 : Blo 1947435 2466227 := bstep (se 1 (by rfl) ⟨1849670, by rfl⟩ : syracuseStep 2466227 = 3699341) B3699341
theorem B6576605 : Blo 1947435 6576605 := bstep (se 3 (by rfl) ⟨1233113, by rfl⟩ : syracuseStep 6576605 = 2466227) B2466227
theorem B4384403 : Blo 1947435 4384403 := bstep (se 1 (by rfl) ⟨3288302, by rfl⟩ : syracuseStep 4384403 = 6576605) B6576605
theorem B2922935 : Blo 1947435 2922935 := bstep (se 1 (by rfl) ⟨2192201, by rfl⟩ : syracuseStep 2922935 = 4384403) B4384403
theorem B1948623 : Blo 1947435 1948623 := bstep (se 1 (by rfl) ⟨1461467, by rfl⟩ : syracuseStep 1948623 = 2922935) B2922935
theorem B2922941 : Blo 1947435 2922941 := bbase (se 3 (by rfl) ⟨548051, by rfl⟩ : syracuseStep 2922941 = 1096103) (by norm_num)
theorem B1948627 : Blo 1947435 1948627 := bstep (se 1 (by rfl) ⟨1461470, by rfl⟩ : syracuseStep 1948627 = 2922941) B2922941
theorem B4384421 : Blo 1947435 4384421 := bbase (se 4 (by rfl) ⟨411039, by rfl⟩ : syracuseStep 4384421 = 822079) (by norm_num)
theorem B2922947 : Blo 1947435 2922947 := bstep (se 1 (by rfl) ⟨2192210, by rfl⟩ : syracuseStep 2922947 = 4384421) B4384421
theorem B1948631 : Blo 1947435 1948631 := bstep (se 1 (by rfl) ⟨1461473, by rfl⟩ : syracuseStep 1948631 = 2922947) B2922947
theorem B4932485 : Blo 1947435 4932485 := bbase (se 4 (by rfl) ⟨462420, by rfl⟩ : syracuseStep 4932485 = 924841) (by norm_num)
theorem B3288323 : Blo 1947435 3288323 := bstep (se 1 (by rfl) ⟨2466242, by rfl⟩ : syracuseStep 3288323 = 4932485) B4932485
theorem B2192215 : Blo 1947435 2192215 := bstep (se 1 (by rfl) ⟨1644161, by rfl⟩ : syracuseStep 2192215 = 3288323) B3288323
theorem B2922953 : Blo 1947435 2922953 := bstep (se 2 (by rfl) ⟨1096107, by rfl⟩ : syracuseStep 2922953 = 2192215) B2192215
theorem B1948635 : Blo 1947435 1948635 := bstep (se 1 (by rfl) ⟨1461476, by rfl⟩ : syracuseStep 1948635 = 2922953) B2922953
theorem B2341009 : Blo 1947435 2341009 := bbase (se 2 (by rfl) ⟨877878, by rfl⟩ : syracuseStep 2341009 = 1755757) (by norm_num)
theorem B3121345 : Blo 1947435 3121345 := bstep (se 2 (by rfl) ⟨1170504, by rfl⟩ : syracuseStep 3121345 = 2341009) B2341009
theorem B4161793 : Blo 1947435 4161793 := bstep (se 2 (by rfl) ⟨1560672, by rfl⟩ : syracuseStep 4161793 = 3121345) B3121345
theorem B5549057 : Blo 1947435 5549057 := bstep (se 2 (by rfl) ⟨2080896, by rfl⟩ : syracuseStep 5549057 = 4161793) B4161793
theorem B3699371 : Blo 1947435 3699371 := bstep (se 1 (by rfl) ⟨2774528, by rfl⟩ : syracuseStep 3699371 = 5549057) B5549057
theorem B9864989 : Blo 1947435 9864989 := bstep (se 3 (by rfl) ⟨1849685, by rfl⟩ : syracuseStep 9864989 = 3699371) B3699371
theorem B6576659 : Blo 1947435 6576659 := bstep (se 1 (by rfl) ⟨4932494, by rfl⟩ : syracuseStep 6576659 = 9864989) B9864989
theorem B4384439 : Blo 1947435 4384439 := bstep (se 1 (by rfl) ⟨3288329, by rfl⟩ : syracuseStep 4384439 = 6576659) B6576659
theorem B2922959 : Blo 1947435 2922959 := bstep (se 1 (by rfl) ⟨2192219, by rfl⟩ : syracuseStep 2922959 = 4384439) B4384439
theorem B1948639 : Blo 1947435 1948639 := bstep (se 1 (by rfl) ⟨1461479, by rfl⟩ : syracuseStep 1948639 = 2922959) B2922959
theorem B2922965 : Blo 1947435 2922965 := bbase (se 7 (by rfl) ⟨34253, by rfl⟩ : syracuseStep 2922965 = 68507) (by norm_num)
theorem B1948643 : Blo 1947435 1948643 := bstep (se 1 (by rfl) ⟨1461482, by rfl⟩ : syracuseStep 1948643 = 2922965) B2922965
theorem B7398773 : Blo 1947435 7398773 := bbase (se 5 (by rfl) ⟨346817, by rfl⟩ : syracuseStep 7398773 = 693635) (by norm_num)
theorem B4932515 : Blo 1947435 4932515 := bstep (se 1 (by rfl) ⟨3699386, by rfl⟩ : syracuseStep 4932515 = 7398773) B7398773
theorem B3288343 : Blo 1947435 3288343 := bstep (se 1 (by rfl) ⟨2466257, by rfl⟩ : syracuseStep 3288343 = 4932515) B4932515
theorem B4384457 : Blo 1947435 4384457 := bstep (se 2 (by rfl) ⟨1644171, by rfl⟩ : syracuseStep 4384457 = 3288343) B3288343
theorem B2922971 : Blo 1947435 2922971 := bstep (se 1 (by rfl) ⟨2192228, by rfl⟩ : syracuseStep 2922971 = 4384457) B4384457
theorem B1948647 : Blo 1947435 1948647 := bstep (se 1 (by rfl) ⟨1461485, by rfl⟩ : syracuseStep 1948647 = 2922971) B2922971
theorem B2192233 : Blo 1947435 2192233 := bbase (se 2 (by rfl) ⟨822087, by rfl⟩ : syracuseStep 2192233 = 1644175) (by norm_num)
theorem B2922977 : Blo 1947435 2922977 := bstep (se 2 (by rfl) ⟨1096116, by rfl⟩ : syracuseStep 2922977 = 2192233) B2192233
theorem B1948651 : Blo 1947435 1948651 := bstep (se 1 (by rfl) ⟨1461488, by rfl⟩ : syracuseStep 1948651 = 2922977) B2922977
theorem B6242741 : Blo 1947435 6242741 := bbase (se 5 (by rfl) ⟨292628, by rfl⟩ : syracuseStep 6242741 = 585257) (by norm_num)
theorem B4161827 : Blo 1947435 4161827 := bstep (se 1 (by rfl) ⟨3121370, by rfl⟩ : syracuseStep 4161827 = 6242741) B6242741
theorem B11098205 : Blo 1947435 11098205 := bstep (se 3 (by rfl) ⟨2080913, by rfl⟩ : syracuseStep 11098205 = 4161827) B4161827
theorem B7398803 : Blo 1947435 7398803 := bstep (se 1 (by rfl) ⟨5549102, by rfl⟩ : syracuseStep 7398803 = 11098205) B11098205
theorem B4932535 : Blo 1947435 4932535 := bstep (se 1 (by rfl) ⟨3699401, by rfl⟩ : syracuseStep 4932535 = 7398803) B7398803
theorem B6576713 : Blo 1947435 6576713 := bstep (se 2 (by rfl) ⟨2466267, by rfl⟩ : syracuseStep 6576713 = 4932535) B4932535
theorem B4384475 : Blo 1947435 4384475 := bstep (se 1 (by rfl) ⟨3288356, by rfl⟩ : syracuseStep 4384475 = 6576713) B6576713
theorem B2922983 : Blo 1947435 2922983 := bstep (se 1 (by rfl) ⟨2192237, by rfl⟩ : syracuseStep 2922983 = 4384475) B4384475
theorem B1948655 : Blo 1947435 1948655 := bstep (se 1 (by rfl) ⟨1461491, by rfl⟩ : syracuseStep 1948655 = 2922983) B2922983
theorem B2922989 : Blo 1947435 2922989 := bbase (se 3 (by rfl) ⟨548060, by rfl⟩ : syracuseStep 2922989 = 1096121) (by norm_num)
theorem B1948659 : Blo 1947435 1948659 := bstep (se 1 (by rfl) ⟨1461494, by rfl⟩ : syracuseStep 1948659 = 2922989) B2922989
theorem B4384493 : Blo 1947435 4384493 := bbase (se 3 (by rfl) ⟨822092, by rfl⟩ : syracuseStep 4384493 = 1644185) (by norm_num)
theorem B2922995 : Blo 1947435 2922995 := bstep (se 1 (by rfl) ⟨2192246, by rfl⟩ : syracuseStep 2922995 = 4384493) B4384493
theorem B1948663 : Blo 1947435 1948663 := bstep (se 1 (by rfl) ⟨1461497, by rfl⟩ : syracuseStep 1948663 = 2922995) B2922995
theorem B39998933 : Blo 1947435 39998933 := bbase (se 7 (by rfl) ⟨468737, by rfl⟩ : syracuseStep 39998933 = 937475) (by norm_num)
theorem B26665955 : Blo 1947435 26665955 := bstep (se 1 (by rfl) ⟨19999466, by rfl⟩ : syracuseStep 26665955 = 39998933) B39998933
theorem B17777303 : Blo 1947435 17777303 := bstep (se 1 (by rfl) ⟨13332977, by rfl⟩ : syracuseStep 17777303 = 26665955) B26665955
theorem B11851535 : Blo 1947435 11851535 := bstep (se 1 (by rfl) ⟨8888651, by rfl⟩ : syracuseStep 11851535 = 17777303) B17777303
theorem B7901023 : Blo 1947435 7901023 := bstep (se 1 (by rfl) ⟨5925767, by rfl⟩ : syracuseStep 7901023 = 11851535) B11851535
theorem B10534697 : Blo 1947435 10534697 := bstep (se 2 (by rfl) ⟨3950511, by rfl⟩ : syracuseStep 10534697 = 7901023) B7901023
theorem B7023131 : Blo 1947435 7023131 := bstep (se 1 (by rfl) ⟨5267348, by rfl⟩ : syracuseStep 7023131 = 10534697) B10534697
theorem B4682087 : Blo 1947435 4682087 := bstep (se 1 (by rfl) ⟨3511565, by rfl⟩ : syracuseStep 4682087 = 7023131) B7023131
theorem B3121391 : Blo 1947435 3121391 := bstep (se 1 (by rfl) ⟨2341043, by rfl⟩ : syracuseStep 3121391 = 4682087) B4682087
theorem B2080927 : Blo 1947435 2080927 := bstep (se 1 (by rfl) ⟨1560695, by rfl⟩ : syracuseStep 2080927 = 3121391) B3121391
theorem B2774569 : Blo 1947435 2774569 := bstep (se 2 (by rfl) ⟨1040463, by rfl⟩ : syracuseStep 2774569 = 2080927) B2080927
theorem B3699425 : Blo 1947435 3699425 := bstep (se 2 (by rfl) ⟨1387284, by rfl⟩ : syracuseStep 3699425 = 2774569) B2774569
theorem B2466283 : Blo 1947435 2466283 := bstep (se 1 (by rfl) ⟨1849712, by rfl⟩ : syracuseStep 2466283 = 3699425) B3699425
theorem B3288377 : Blo 1947435 3288377 := bstep (se 2 (by rfl) ⟨1233141, by rfl⟩ : syracuseStep 3288377 = 2466283) B2466283
theorem B2192251 : Blo 1947435 2192251 := bstep (se 1 (by rfl) ⟨1644188, by rfl⟩ : syracuseStep 2192251 = 3288377) B3288377
theorem B2923001 : Blo 1947435 2923001 := bstep (se 2 (by rfl) ⟨1096125, by rfl⟩ : syracuseStep 2923001 = 2192251) B2192251
theorem B1948667 : Blo 1947435 1948667 := bstep (se 1 (by rfl) ⟨1461500, by rfl⟩ : syracuseStep 1948667 = 2923001) B2923001
theorem B2812429 : Blo 1947435 2812429 := bbase (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) (by norm_num)
theorem B3749905 : Blo 1947435 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B19999493 : Blo 1947435 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B13332995 : Blo 1947435 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B8888663 : Blo 1947435 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B5925775 : Blo 1947435 5925775 := bstep (se 1 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 5925775 = 8888663) B8888663
theorem B7901033 : Blo 1947435 7901033 := bstep (se 2 (by rfl) ⟨2962887, by rfl⟩ : syracuseStep 7901033 = 5925775) B5925775
theorem B84277685 : Blo 1947435 84277685 := bstep (se 5 (by rfl) ⟨3950516, by rfl⟩ : syracuseStep 84277685 = 7901033) B7901033
theorem B56185123 : Blo 1947435 56185123 := bstep (se 1 (by rfl) ⟨42138842, by rfl⟩ : syracuseStep 56185123 = 84277685) B84277685
theorem B74913497 : Blo 1947435 74913497 := bstep (se 2 (by rfl) ⟨28092561, by rfl⟩ : syracuseStep 74913497 = 56185123) B56185123
theorem B49942331 : Blo 1947435 49942331 := bstep (se 1 (by rfl) ⟨37456748, by rfl⟩ : syracuseStep 49942331 = 74913497) B74913497
theorem B33294887 : Blo 1947435 33294887 := bstep (se 1 (by rfl) ⟨24971165, by rfl⟩ : syracuseStep 33294887 = 49942331) B49942331
theorem B22196591 : Blo 1947435 22196591 := bstep (se 1 (by rfl) ⟨16647443, by rfl⟩ : syracuseStep 22196591 = 33294887) B33294887
theorem B14797727 : Blo 1947435 14797727 := bstep (se 1 (by rfl) ⟨11098295, by rfl⟩ : syracuseStep 14797727 = 22196591) B22196591
theorem B9865151 : Blo 1947435 9865151 := bstep (se 1 (by rfl) ⟨7398863, by rfl⟩ : syracuseStep 9865151 = 14797727) B14797727
theorem B6576767 : Blo 1947435 6576767 := bstep (se 1 (by rfl) ⟨4932575, by rfl⟩ : syracuseStep 6576767 = 9865151) B9865151
theorem B4384511 : Blo 1947435 4384511 := bstep (se 1 (by rfl) ⟨3288383, by rfl⟩ : syracuseStep 4384511 = 6576767) B6576767
theorem B2923007 : Blo 1947435 2923007 := bstep (se 1 (by rfl) ⟨2192255, by rfl⟩ : syracuseStep 2923007 = 4384511) B4384511
theorem B1948671 : Blo 1947435 1948671 := bstep (se 1 (by rfl) ⟨1461503, by rfl⟩ : syracuseStep 1948671 = 2923007) B2923007
theorem B2923013 : Blo 1947435 2923013 := bbase (se 4 (by rfl) ⟨274032, by rfl⟩ : syracuseStep 2923013 = 548065) (by norm_num)
theorem B1948675 : Blo 1947435 1948675 := bstep (se 1 (by rfl) ⟨1461506, by rfl⟩ : syracuseStep 1948675 = 2923013) B2923013
theorem B3288397 : Blo 1947435 3288397 := bbase (se 3 (by rfl) ⟨616574, by rfl⟩ : syracuseStep 3288397 = 1233149) (by norm_num)
theorem B4384529 : Blo 1947435 4384529 := bstep (se 2 (by rfl) ⟨1644198, by rfl⟩ : syracuseStep 4384529 = 3288397) B3288397
theorem B2923019 : Blo 1947435 2923019 := bstep (se 1 (by rfl) ⟨2192264, by rfl⟩ : syracuseStep 2923019 = 4384529) B4384529
theorem B1948679 : Blo 1947435 1948679 := bstep (se 1 (by rfl) ⟨1461509, by rfl⟩ : syracuseStep 1948679 = 2923019) B2923019
theorem B2192269 : Blo 1947435 2192269 := bbase (se 3 (by rfl) ⟨411050, by rfl⟩ : syracuseStep 2192269 = 822101) (by norm_num)
theorem B2923025 : Blo 1947435 2923025 := bstep (se 2 (by rfl) ⟨1096134, by rfl⟩ : syracuseStep 2923025 = 2192269) B2192269
theorem B1948683 : Blo 1947435 1948683 := bstep (se 1 (by rfl) ⟨1461512, by rfl⟩ : syracuseStep 1948683 = 2923025) B2923025
theorem B6576821 : Blo 1947435 6576821 := bbase (se 5 (by rfl) ⟨308288, by rfl⟩ : syracuseStep 6576821 = 616577) (by norm_num)
theorem B4384547 : Blo 1947435 4384547 := bstep (se 1 (by rfl) ⟨3288410, by rfl⟩ : syracuseStep 4384547 = 6576821) B6576821
theorem B2923031 : Blo 1947435 2923031 := bstep (se 1 (by rfl) ⟨2192273, by rfl⟩ : syracuseStep 2923031 = 4384547) B4384547
theorem B1948687 : Blo 1947435 1948687 := bstep (se 1 (by rfl) ⟨1461515, by rfl⟩ : syracuseStep 1948687 = 2923031) B2923031
theorem B2923037 : Blo 1947435 2923037 := bbase (se 3 (by rfl) ⟨548069, by rfl⟩ : syracuseStep 2923037 = 1096139) (by norm_num)
theorem B1948691 : Blo 1947435 1948691 := bstep (se 1 (by rfl) ⟨1461518, by rfl⟩ : syracuseStep 1948691 = 2923037) B2923037
theorem B4384565 : Blo 1947435 4384565 := bbase (se 5 (by rfl) ⟨205526, by rfl⟩ : syracuseStep 4384565 = 411053) (by norm_num)
theorem B2923043 : Blo 1947435 2923043 := bstep (se 1 (by rfl) ⟨2192282, by rfl⟩ : syracuseStep 2923043 = 4384565) B4384565
theorem B1948695 : Blo 1947435 1948695 := bstep (se 1 (by rfl) ⟨1461521, by rfl⟩ : syracuseStep 1948695 = 2923043) B2923043
theorem B2341081 : Blo 1947435 2341081 := bbase (se 2 (by rfl) ⟨877905, by rfl⟩ : syracuseStep 2341081 = 1755811) (by norm_num)
theorem B12485765 : Blo 1947435 12485765 := bstep (se 4 (by rfl) ⟨1170540, by rfl⟩ : syracuseStep 12485765 = 2341081) B2341081
theorem B8323843 : Blo 1947435 8323843 := bstep (se 1 (by rfl) ⟨6242882, by rfl⟩ : syracuseStep 8323843 = 12485765) B12485765
theorem B11098457 : Blo 1947435 11098457 := bstep (se 2 (by rfl) ⟨4161921, by rfl⟩ : syracuseStep 11098457 = 8323843) B8323843
theorem B7398971 : Blo 1947435 7398971 := bstep (se 1 (by rfl) ⟨5549228, by rfl⟩ : syracuseStep 7398971 = 11098457) B11098457
theorem B4932647 : Blo 1947435 4932647 := bstep (se 1 (by rfl) ⟨3699485, by rfl⟩ : syracuseStep 4932647 = 7398971) B7398971
theorem B3288431 : Blo 1947435 3288431 := bstep (se 1 (by rfl) ⟨2466323, by rfl⟩ : syracuseStep 3288431 = 4932647) B4932647
theorem B2192287 : Blo 1947435 2192287 := bstep (se 1 (by rfl) ⟨1644215, by rfl⟩ : syracuseStep 2192287 = 3288431) B3288431
theorem B2923049 : Blo 1947435 2923049 := bstep (se 2 (by rfl) ⟨1096143, by rfl⟩ : syracuseStep 2923049 = 2192287) B2192287
theorem B1948699 : Blo 1947435 1948699 := bstep (se 1 (by rfl) ⟨1461524, by rfl⟩ : syracuseStep 1948699 = 2923049) B2923049
theorem B2812477 : Blo 1947435 2812477 := bbase (se 3 (by rfl) ⟨527339, by rfl⟩ : syracuseStep 2812477 = 1054679) (by norm_num)
theorem B3749969 : Blo 1947435 3749969 := bstep (se 2 (by rfl) ⟨1406238, by rfl⟩ : syracuseStep 3749969 = 2812477) B2812477
theorem B2499979 : Blo 1947435 2499979 := bstep (se 1 (by rfl) ⟨1874984, by rfl⟩ : syracuseStep 2499979 = 3749969) B3749969
theorem B3333305 : Blo 1947435 3333305 := bstep (se 2 (by rfl) ⟨1249989, by rfl⟩ : syracuseStep 3333305 = 2499979) B2499979
theorem B2222203 : Blo 1947435 2222203 := bstep (se 1 (by rfl) ⟨1666652, by rfl⟩ : syracuseStep 2222203 = 3333305) B3333305
theorem B2962937 : Blo 1947435 2962937 := bstep (se 2 (by rfl) ⟨1111101, by rfl⟩ : syracuseStep 2962937 = 2222203) B2222203
theorem B7901165 : Blo 1947435 7901165 := bstep (se 3 (by rfl) ⟨1481468, by rfl⟩ : syracuseStep 7901165 = 2962937) B2962937
theorem B5267443 : Blo 1947435 5267443 := bstep (se 1 (by rfl) ⟨3950582, by rfl⟩ : syracuseStep 5267443 = 7901165) B7901165
theorem B7023257 : Blo 1947435 7023257 := bstep (se 2 (by rfl) ⟨2633721, by rfl⟩ : syracuseStep 7023257 = 5267443) B5267443
theorem B4682171 : Blo 1947435 4682171 := bstep (se 1 (by rfl) ⟨3511628, by rfl⟩ : syracuseStep 4682171 = 7023257) B7023257
theorem B12485789 : Blo 1947435 12485789 := bstep (se 3 (by rfl) ⟨2341085, by rfl⟩ : syracuseStep 12485789 = 4682171) B4682171
theorem B8323859 : Blo 1947435 8323859 := bstep (se 1 (by rfl) ⟨6242894, by rfl⟩ : syracuseStep 8323859 = 12485789) B12485789
theorem B5549239 : Blo 1947435 5549239 := bstep (se 1 (by rfl) ⟨4161929, by rfl⟩ : syracuseStep 5549239 = 8323859) B8323859
theorem B7398985 : Blo 1947435 7398985 := bstep (se 2 (by rfl) ⟨2774619, by rfl⟩ : syracuseStep 7398985 = 5549239) B5549239
theorem B9865313 : Blo 1947435 9865313 := bstep (se 2 (by rfl) ⟨3699492, by rfl⟩ : syracuseStep 9865313 = 7398985) B7398985
theorem B6576875 : Blo 1947435 6576875 := bstep (se 1 (by rfl) ⟨4932656, by rfl⟩ : syracuseStep 6576875 = 9865313) B9865313
theorem B4384583 : Blo 1947435 4384583 := bstep (se 1 (by rfl) ⟨3288437, by rfl⟩ : syracuseStep 4384583 = 6576875) B6576875
theorem B2923055 : Blo 1947435 2923055 := bstep (se 1 (by rfl) ⟨2192291, by rfl⟩ : syracuseStep 2923055 = 4384583) B4384583
theorem B1948703 : Blo 1947435 1948703 := bstep (se 1 (by rfl) ⟨1461527, by rfl⟩ : syracuseStep 1948703 = 2923055) B2923055
theorem B2923061 : Blo 1947435 2923061 := bbase (se 5 (by rfl) ⟨137018, by rfl⟩ : syracuseStep 2923061 = 274037) (by norm_num)
theorem B1948707 : Blo 1947435 1948707 := bstep (se 1 (by rfl) ⟨1461530, by rfl⟩ : syracuseStep 1948707 = 2923061) B2923061
theorem B4932677 : Blo 1947435 4932677 := bbase (se 4 (by rfl) ⟨462438, by rfl⟩ : syracuseStep 4932677 = 924877) (by norm_num)
theorem B3288451 : Blo 1947435 3288451 := bstep (se 1 (by rfl) ⟨2466338, by rfl⟩ : syracuseStep 3288451 = 4932677) B4932677
theorem B4384601 : Blo 1947435 4384601 := bstep (se 2 (by rfl) ⟨1644225, by rfl⟩ : syracuseStep 4384601 = 3288451) B3288451
theorem B2923067 : Blo 1947435 2923067 := bstep (se 1 (by rfl) ⟨2192300, by rfl⟩ : syracuseStep 2923067 = 4384601) B4384601
theorem B1948711 : Blo 1947435 1948711 := bstep (se 1 (by rfl) ⟨1461533, by rfl⟩ : syracuseStep 1948711 = 2923067) B2923067
theorem B2192305 : Blo 1947435 2192305 := bbase (se 2 (by rfl) ⟨822114, by rfl⟩ : syracuseStep 2192305 = 1644229) (by norm_num)
theorem B2923073 : Blo 1947435 2923073 := bstep (se 2 (by rfl) ⟨1096152, by rfl⟩ : syracuseStep 2923073 = 2192305) B2192305
theorem B1948715 : Blo 1947435 1948715 := bstep (se 1 (by rfl) ⟨1461536, by rfl⟩ : syracuseStep 1948715 = 2923073) B2923073
theorem B5549285 : Blo 1947435 5549285 := bbase (se 4 (by rfl) ⟨520245, by rfl⟩ : syracuseStep 5549285 = 1040491) (by norm_num)
theorem B3699523 : Blo 1947435 3699523 := bstep (se 1 (by rfl) ⟨2774642, by rfl⟩ : syracuseStep 3699523 = 5549285) B5549285
theorem B4932697 : Blo 1947435 4932697 := bstep (se 2 (by rfl) ⟨1849761, by rfl⟩ : syracuseStep 4932697 = 3699523) B3699523
theorem B6576929 : Blo 1947435 6576929 := bstep (se 2 (by rfl) ⟨2466348, by rfl⟩ : syracuseStep 6576929 = 4932697) B4932697
theorem B4384619 : Blo 1947435 4384619 := bstep (se 1 (by rfl) ⟨3288464, by rfl⟩ : syracuseStep 4384619 = 6576929) B6576929
theorem B2923079 : Blo 1947435 2923079 := bstep (se 1 (by rfl) ⟨2192309, by rfl⟩ : syracuseStep 2923079 = 4384619) B4384619
theorem B1948719 : Blo 1947435 1948719 := bstep (se 1 (by rfl) ⟨1461539, by rfl⟩ : syracuseStep 1948719 = 2923079) B2923079
theorem B2923085 : Blo 1947435 2923085 := bbase (se 3 (by rfl) ⟨548078, by rfl⟩ : syracuseStep 2923085 = 1096157) (by norm_num)
theorem B1948723 : Blo 1947435 1948723 := bstep (se 1 (by rfl) ⟨1461542, by rfl⟩ : syracuseStep 1948723 = 2923085) B2923085
theorem B4384637 : Blo 1947435 4384637 := bbase (se 3 (by rfl) ⟨822119, by rfl⟩ : syracuseStep 4384637 = 1644239) (by norm_num)
theorem B2923091 : Blo 1947435 2923091 := bstep (se 1 (by rfl) ⟨2192318, by rfl⟩ : syracuseStep 2923091 = 4384637) B4384637
theorem B1948727 : Blo 1947435 1948727 := bstep (se 1 (by rfl) ⟨1461545, by rfl⟩ : syracuseStep 1948727 = 2923091) B2923091
theorem B3288485 : Blo 1947435 3288485 := bbase (se 4 (by rfl) ⟨308295, by rfl⟩ : syracuseStep 3288485 = 616591) (by norm_num)
theorem B2192323 : Blo 1947435 2192323 := bstep (se 1 (by rfl) ⟨1644242, by rfl⟩ : syracuseStep 2192323 = 3288485) B3288485
theorem B2923097 : Blo 1947435 2923097 := bstep (se 2 (by rfl) ⟨1096161, by rfl⟩ : syracuseStep 2923097 = 2192323) B2192323
theorem B1948731 : Blo 1947435 1948731 := bstep (se 1 (by rfl) ⟨1461548, by rfl⟩ : syracuseStep 1948731 = 2923097) B2923097
theorem B5925973 : Blo 1947435 5925973 := bbase (se 8 (by rfl) ⟨34722, by rfl⟩ : syracuseStep 5925973 = 69445) (by norm_num)
theorem B7901297 : Blo 1947435 7901297 := bstep (se 2 (by rfl) ⟨2962986, by rfl⟩ : syracuseStep 7901297 = 5925973) B5925973
theorem B5267531 : Blo 1947435 5267531 := bstep (se 1 (by rfl) ⟨3950648, by rfl⟩ : syracuseStep 5267531 = 7901297) B7901297
theorem B3511687 : Blo 1947435 3511687 := bstep (se 1 (by rfl) ⟨2633765, by rfl⟩ : syracuseStep 3511687 = 5267531) B5267531
theorem B4682249 : Blo 1947435 4682249 := bstep (se 2 (by rfl) ⟨1755843, by rfl⟩ : syracuseStep 4682249 = 3511687) B3511687
theorem B3121499 : Blo 1947435 3121499 := bstep (se 1 (by rfl) ⟨2341124, by rfl⟩ : syracuseStep 3121499 = 4682249) B4682249
theorem B2080999 : Blo 1947435 2080999 := bstep (se 1 (by rfl) ⟨1560749, by rfl⟩ : syracuseStep 2080999 = 3121499) B3121499
theorem B2774665 : Blo 1947435 2774665 := bstep (se 2 (by rfl) ⟨1040499, by rfl⟩ : syracuseStep 2774665 = 2080999) B2080999
theorem B14798213 : Blo 1947435 14798213 := bstep (se 4 (by rfl) ⟨1387332, by rfl⟩ : syracuseStep 14798213 = 2774665) B2774665
theorem B9865475 : Blo 1947435 9865475 := bstep (se 1 (by rfl) ⟨7399106, by rfl⟩ : syracuseStep 9865475 = 14798213) B14798213
theorem B6576983 : Blo 1947435 6576983 := bstep (se 1 (by rfl) ⟨4932737, by rfl⟩ : syracuseStep 6576983 = 9865475) B9865475
theorem B4384655 : Blo 1947435 4384655 := bstep (se 1 (by rfl) ⟨3288491, by rfl⟩ : syracuseStep 4384655 = 6576983) B6576983
theorem B2923103 : Blo 1947435 2923103 := bstep (se 1 (by rfl) ⟨2192327, by rfl⟩ : syracuseStep 2923103 = 4384655) B4384655
theorem B1948735 : Blo 1947435 1948735 := bstep (se 1 (by rfl) ⟨1461551, by rfl⟩ : syracuseStep 1948735 = 2923103) B2923103
theorem B2923109 : Blo 1947435 2923109 := bbase (se 4 (by rfl) ⟨274041, by rfl⟩ : syracuseStep 2923109 = 548083) (by norm_num)
theorem B1948739 : Blo 1947435 1948739 := bstep (se 1 (by rfl) ⟨1461554, by rfl⟩ : syracuseStep 1948739 = 2923109) B2923109
theorem B2774677 : Blo 1947435 2774677 := bbase (se 6 (by rfl) ⟨65031, by rfl⟩ : syracuseStep 2774677 = 130063) (by norm_num)
theorem B3699569 : Blo 1947435 3699569 := bstep (se 2 (by rfl) ⟨1387338, by rfl⟩ : syracuseStep 3699569 = 2774677) B2774677
theorem B2466379 : Blo 1947435 2466379 := bstep (se 1 (by rfl) ⟨1849784, by rfl⟩ : syracuseStep 2466379 = 3699569) B3699569
theorem B3288505 : Blo 1947435 3288505 := bstep (se 2 (by rfl) ⟨1233189, by rfl⟩ : syracuseStep 3288505 = 2466379) B2466379
theorem B4384673 : Blo 1947435 4384673 := bstep (se 2 (by rfl) ⟨1644252, by rfl⟩ : syracuseStep 4384673 = 3288505) B3288505
theorem B2923115 : Blo 1947435 2923115 := bstep (se 1 (by rfl) ⟨2192336, by rfl⟩ : syracuseStep 2923115 = 4384673) B4384673
theorem B1948743 : Blo 1947435 1948743 := bstep (se 1 (by rfl) ⟨1461557, by rfl⟩ : syracuseStep 1948743 = 2923115) B2923115
theorem B2192341 : Blo 1947435 2192341 := bbase (se 7 (by rfl) ⟨25691, by rfl⟩ : syracuseStep 2192341 = 51383) (by norm_num)
theorem B2923121 : Blo 1947435 2923121 := bstep (se 2 (by rfl) ⟨1096170, by rfl⟩ : syracuseStep 2923121 = 2192341) B2192341
theorem B1948747 : Blo 1947435 1948747 := bstep (se 1 (by rfl) ⟨1461560, by rfl⟩ : syracuseStep 1948747 = 2923121) B2923121
theorem B2466389 : Blo 1947435 2466389 := bbase (se 8 (by rfl) ⟨14451, by rfl⟩ : syracuseStep 2466389 = 28903) (by norm_num)
theorem B6577037 : Blo 1947435 6577037 := bstep (se 3 (by rfl) ⟨1233194, by rfl⟩ : syracuseStep 6577037 = 2466389) B2466389
theorem B4384691 : Blo 1947435 4384691 := bstep (se 1 (by rfl) ⟨3288518, by rfl⟩ : syracuseStep 4384691 = 6577037) B6577037
theorem B2923127 : Blo 1947435 2923127 := bstep (se 1 (by rfl) ⟨2192345, by rfl⟩ : syracuseStep 2923127 = 4384691) B4384691
theorem B1948751 : Blo 1947435 1948751 := bstep (se 1 (by rfl) ⟨1461563, by rfl⟩ : syracuseStep 1948751 = 2923127) B2923127
theorem B2923133 : Blo 1947435 2923133 := bbase (se 3 (by rfl) ⟨548087, by rfl⟩ : syracuseStep 2923133 = 1096175) (by norm_num)
theorem B1948755 : Blo 1947435 1948755 := bstep (se 1 (by rfl) ⟨1461566, by rfl⟩ : syracuseStep 1948755 = 2923133) B2923133
theorem B4384709 : Blo 1947435 4384709 := bbase (se 4 (by rfl) ⟨411066, by rfl⟩ : syracuseStep 4384709 = 822133) (by norm_num)
theorem B2923139 : Blo 1947435 2923139 := bstep (se 1 (by rfl) ⟨2192354, by rfl⟩ : syracuseStep 2923139 = 4384709) B4384709
theorem B1948759 : Blo 1947435 1948759 := bstep (se 1 (by rfl) ⟨1461569, by rfl⟩ : syracuseStep 1948759 = 2923139) B2923139
theorem B8324117 : Blo 1947435 8324117 := bbase (se 6 (by rfl) ⟨195096, by rfl⟩ : syracuseStep 8324117 = 390193) (by norm_num)
theorem B5549411 : Blo 1947435 5549411 := bstep (se 1 (by rfl) ⟨4162058, by rfl⟩ : syracuseStep 5549411 = 8324117) B8324117
theorem B3699607 : Blo 1947435 3699607 := bstep (se 1 (by rfl) ⟨2774705, by rfl⟩ : syracuseStep 3699607 = 5549411) B5549411
theorem B4932809 : Blo 1947435 4932809 := bstep (se 2 (by rfl) ⟨1849803, by rfl⟩ : syracuseStep 4932809 = 3699607) B3699607
theorem B3288539 : Blo 1947435 3288539 := bstep (se 1 (by rfl) ⟨2466404, by rfl⟩ : syracuseStep 3288539 = 4932809) B4932809
theorem B2192359 : Blo 1947435 2192359 := bstep (se 1 (by rfl) ⟨1644269, by rfl⟩ : syracuseStep 2192359 = 3288539) B3288539
theorem B2923145 : Blo 1947435 2923145 := bstep (se 2 (by rfl) ⟨1096179, by rfl⟩ : syracuseStep 2923145 = 2192359) B2192359
theorem B1948763 : Blo 1947435 1948763 := bstep (se 1 (by rfl) ⟨1461572, by rfl⟩ : syracuseStep 1948763 = 2923145) B2923145
theorem B9865637 : Blo 1947435 9865637 := bbase (se 4 (by rfl) ⟨924903, by rfl⟩ : syracuseStep 9865637 = 1849807) (by norm_num)
theorem B6577091 : Blo 1947435 6577091 := bstep (se 1 (by rfl) ⟨4932818, by rfl⟩ : syracuseStep 6577091 = 9865637) B9865637
theorem B4384727 : Blo 1947435 4384727 := bstep (se 1 (by rfl) ⟨3288545, by rfl⟩ : syracuseStep 4384727 = 6577091) B6577091
theorem B2923151 : Blo 1947435 2923151 := bstep (se 1 (by rfl) ⟨2192363, by rfl⟩ : syracuseStep 2923151 = 4384727) B4384727
theorem B1948767 : Blo 1947435 1948767 := bstep (se 1 (by rfl) ⟨1461575, by rfl⟩ : syracuseStep 1948767 = 2923151) B2923151
theorem B2923157 : Blo 1947435 2923157 := bbase (se 6 (by rfl) ⟨68511, by rfl⟩ : syracuseStep 2923157 = 137023) (by norm_num)
theorem B1948771 : Blo 1947435 1948771 := bstep (se 1 (by rfl) ⟨1461578, by rfl⟩ : syracuseStep 1948771 = 2923157) B2923157
theorem B5000141 : Blo 1947435 5000141 := bbase (se 3 (by rfl) ⟨937526, by rfl⟩ : syracuseStep 5000141 = 1875053) (by norm_num)
theorem B13333709 : Blo 1947435 13333709 := bstep (se 3 (by rfl) ⟨2500070, by rfl⟩ : syracuseStep 13333709 = 5000141) B5000141
theorem B8889139 : Blo 1947435 8889139 := bstep (se 1 (by rfl) ⟨6666854, by rfl⟩ : syracuseStep 8889139 = 13333709) B13333709
theorem B11852185 : Blo 1947435 11852185 := bstep (se 2 (by rfl) ⟨4444569, by rfl⟩ : syracuseStep 11852185 = 8889139) B8889139
theorem B15802913 : Blo 1947435 15802913 := bstep (se 2 (by rfl) ⟨5926092, by rfl⟩ : syracuseStep 15802913 = 11852185) B11852185
theorem B10535275 : Blo 1947435 10535275 := bstep (se 1 (by rfl) ⟨7901456, by rfl⟩ : syracuseStep 10535275 = 15802913) B15802913
theorem B14047033 : Blo 1947435 14047033 := bstep (se 2 (by rfl) ⟨5267637, by rfl⟩ : syracuseStep 14047033 = 10535275) B10535275
theorem B18729377 : Blo 1947435 18729377 := bstep (se 2 (by rfl) ⟨7023516, by rfl⟩ : syracuseStep 18729377 = 14047033) B14047033
theorem B12486251 : Blo 1947435 12486251 := bstep (se 1 (by rfl) ⟨9364688, by rfl⟩ : syracuseStep 12486251 = 18729377) B18729377
theorem B8324167 : Blo 1947435 8324167 := bstep (se 1 (by rfl) ⟨6243125, by rfl⟩ : syracuseStep 8324167 = 12486251) B12486251
theorem B11098889 : Blo 1947435 11098889 := bstep (se 2 (by rfl) ⟨4162083, by rfl⟩ : syracuseStep 11098889 = 8324167) B8324167
theorem B7399259 : Blo 1947435 7399259 := bstep (se 1 (by rfl) ⟨5549444, by rfl⟩ : syracuseStep 7399259 = 11098889) B11098889
theorem B4932839 : Blo 1947435 4932839 := bstep (se 1 (by rfl) ⟨3699629, by rfl⟩ : syracuseStep 4932839 = 7399259) B7399259
theorem B3288559 : Blo 1947435 3288559 := bstep (se 1 (by rfl) ⟨2466419, by rfl⟩ : syracuseStep 3288559 = 4932839) B4932839
theorem B4384745 : Blo 1947435 4384745 := bstep (se 2 (by rfl) ⟨1644279, by rfl⟩ : syracuseStep 4384745 = 3288559) B3288559
theorem B2923163 : Blo 1947435 2923163 := bstep (se 1 (by rfl) ⟨2192372, by rfl⟩ : syracuseStep 2923163 = 4384745) B4384745
theorem B1948775 : Blo 1947435 1948775 := bstep (se 1 (by rfl) ⟨1461581, by rfl⟩ : syracuseStep 1948775 = 2923163) B2923163
theorem B2192377 : Blo 1947435 2192377 := bbase (se 2 (by rfl) ⟨822141, by rfl⟩ : syracuseStep 2192377 = 1644283) (by norm_num)
theorem B2923169 : Blo 1947435 2923169 := bstep (se 2 (by rfl) ⟨1096188, by rfl⟩ : syracuseStep 2923169 = 2192377) B2192377
theorem B1948779 : Blo 1947435 1948779 := bstep (se 1 (by rfl) ⟨1461584, by rfl⟩ : syracuseStep 1948779 = 2923169) B2923169
theorem B5926117 : Blo 1947435 5926117 := bbase (se 4 (by rfl) ⟨555573, by rfl⟩ : syracuseStep 5926117 = 1111147) (by norm_num)
theorem B7901489 : Blo 1947435 7901489 := bstep (se 2 (by rfl) ⟨2963058, by rfl⟩ : syracuseStep 7901489 = 5926117) B5926117
theorem B21070637 : Blo 1947435 21070637 := bstep (se 3 (by rfl) ⟨3950744, by rfl⟩ : syracuseStep 21070637 = 7901489) B7901489
theorem B14047091 : Blo 1947435 14047091 := bstep (se 1 (by rfl) ⟨10535318, by rfl⟩ : syracuseStep 14047091 = 21070637) B21070637
theorem B9364727 : Blo 1947435 9364727 := bstep (se 1 (by rfl) ⟨7023545, by rfl⟩ : syracuseStep 9364727 = 14047091) B14047091
theorem B6243151 : Blo 1947435 6243151 := bstep (se 1 (by rfl) ⟨4682363, by rfl⟩ : syracuseStep 6243151 = 9364727) B9364727
theorem B8324201 : Blo 1947435 8324201 := bstep (se 2 (by rfl) ⟨3121575, by rfl⟩ : syracuseStep 8324201 = 6243151) B6243151
theorem B5549467 : Blo 1947435 5549467 := bstep (se 1 (by rfl) ⟨4162100, by rfl⟩ : syracuseStep 5549467 = 8324201) B8324201
theorem B7399289 : Blo 1947435 7399289 := bstep (se 2 (by rfl) ⟨2774733, by rfl⟩ : syracuseStep 7399289 = 5549467) B5549467
theorem B4932859 : Blo 1947435 4932859 := bstep (se 1 (by rfl) ⟨3699644, by rfl⟩ : syracuseStep 4932859 = 7399289) B7399289
theorem B6577145 : Blo 1947435 6577145 := bstep (se 2 (by rfl) ⟨2466429, by rfl⟩ : syracuseStep 6577145 = 4932859) B4932859
theorem B4384763 : Blo 1947435 4384763 := bstep (se 1 (by rfl) ⟨3288572, by rfl⟩ : syracuseStep 4384763 = 6577145) B6577145
theorem B2923175 : Blo 1947435 2923175 := bstep (se 1 (by rfl) ⟨2192381, by rfl⟩ : syracuseStep 2923175 = 4384763) B4384763
theorem B1948783 : Blo 1947435 1948783 := bstep (se 1 (by rfl) ⟨1461587, by rfl⟩ : syracuseStep 1948783 = 2923175) B2923175
theorem B2923181 : Blo 1947435 2923181 := bbase (se 3 (by rfl) ⟨548096, by rfl⟩ : syracuseStep 2923181 = 1096193) (by norm_num)
theorem B1948787 : Blo 1947435 1948787 := bstep (se 1 (by rfl) ⟨1461590, by rfl⟩ : syracuseStep 1948787 = 2923181) B2923181
theorem B4384781 : Blo 1947435 4384781 := bbase (se 3 (by rfl) ⟨822146, by rfl⟩ : syracuseStep 4384781 = 1644293) (by norm_num)
theorem B2923187 : Blo 1947435 2923187 := bstep (se 1 (by rfl) ⟨2192390, by rfl⟩ : syracuseStep 2923187 = 4384781) B4384781
theorem B1948791 : Blo 1947435 1948791 := bstep (se 1 (by rfl) ⟨1461593, by rfl⟩ : syracuseStep 1948791 = 2923187) B2923187
theorem B2466445 : Blo 1947435 2466445 := bbase (se 3 (by rfl) ⟨462458, by rfl⟩ : syracuseStep 2466445 = 924917) (by norm_num)
theorem B3288593 : Blo 1947435 3288593 := bstep (se 2 (by rfl) ⟨1233222, by rfl⟩ : syracuseStep 3288593 = 2466445) B2466445
theorem B2192395 : Blo 1947435 2192395 := bstep (se 1 (by rfl) ⟨1644296, by rfl⟩ : syracuseStep 2192395 = 3288593) B3288593
theorem B2923193 : Blo 1947435 2923193 := bstep (se 2 (by rfl) ⟨1096197, by rfl⟩ : syracuseStep 2923193 = 2192395) B2192395
theorem B1948795 : Blo 1947435 1948795 := bstep (se 1 (by rfl) ⟨1461596, by rfl⟩ : syracuseStep 1948795 = 2923193) B2923193
theorem B3333469 : Blo 1947435 3333469 := bbase (se 3 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 3333469 = 1250051) (by norm_num)
theorem B4444625 : Blo 1947435 4444625 := bstep (se 2 (by rfl) ⟨1666734, by rfl⟩ : syracuseStep 4444625 = 3333469) B3333469
theorem B2963083 : Blo 1947435 2963083 := bstep (se 1 (by rfl) ⟨2222312, by rfl⟩ : syracuseStep 2963083 = 4444625) B4444625
theorem B3950777 : Blo 1947435 3950777 := bstep (se 2 (by rfl) ⟨1481541, by rfl⟩ : syracuseStep 3950777 = 2963083) B2963083
theorem B2633851 : Blo 1947435 2633851 := bstep (se 1 (by rfl) ⟨1975388, by rfl⟩ : syracuseStep 2633851 = 3950777) B3950777
theorem B3511801 : Blo 1947435 3511801 := bstep (se 2 (by rfl) ⟨1316925, by rfl⟩ : syracuseStep 3511801 = 2633851) B2633851
theorem B18729605 : Blo 1947435 18729605 := bstep (se 4 (by rfl) ⟨1755900, by rfl⟩ : syracuseStep 18729605 = 3511801) B3511801
theorem B12486403 : Blo 1947435 12486403 := bstep (se 1 (by rfl) ⟨9364802, by rfl⟩ : syracuseStep 12486403 = 18729605) B18729605
theorem B16648537 : Blo 1947435 16648537 := bstep (se 2 (by rfl) ⟨6243201, by rfl⟩ : syracuseStep 16648537 = 12486403) B12486403
theorem B22198049 : Blo 1947435 22198049 := bstep (se 2 (by rfl) ⟨8324268, by rfl⟩ : syracuseStep 22198049 = 16648537) B16648537
theorem B14798699 : Blo 1947435 14798699 := bstep (se 1 (by rfl) ⟨11099024, by rfl⟩ : syracuseStep 14798699 = 22198049) B22198049
theorem B9865799 : Blo 1947435 9865799 := bstep (se 1 (by rfl) ⟨7399349, by rfl⟩ : syracuseStep 9865799 = 14798699) B14798699
theorem B6577199 : Blo 1947435 6577199 := bstep (se 1 (by rfl) ⟨4932899, by rfl⟩ : syracuseStep 6577199 = 9865799) B9865799
theorem B4384799 : Blo 1947435 4384799 := bstep (se 1 (by rfl) ⟨3288599, by rfl⟩ : syracuseStep 4384799 = 6577199) B6577199
theorem B2923199 : Blo 1947435 2923199 := bstep (se 1 (by rfl) ⟨2192399, by rfl⟩ : syracuseStep 2923199 = 4384799) B4384799
theorem B1948799 : Blo 1947435 1948799 := bstep (se 1 (by rfl) ⟨1461599, by rfl⟩ : syracuseStep 1948799 = 2923199) B2923199
theorem B2923205 : Blo 1947435 2923205 := bbase (se 4 (by rfl) ⟨274050, by rfl⟩ : syracuseStep 2923205 = 548101) (by norm_num)
theorem B1948803 : Blo 1947435 1948803 := bstep (se 1 (by rfl) ⟨1461602, by rfl⟩ : syracuseStep 1948803 = 2923205) B2923205
theorem B3288613 : Blo 1947435 3288613 := bbase (se 4 (by rfl) ⟨308307, by rfl⟩ : syracuseStep 3288613 = 616615) (by norm_num)
theorem B4384817 : Blo 1947435 4384817 := bstep (se 2 (by rfl) ⟨1644306, by rfl⟩ : syracuseStep 4384817 = 3288613) B3288613
theorem B2923211 : Blo 1947435 2923211 := bstep (se 1 (by rfl) ⟨2192408, by rfl⟩ : syracuseStep 2923211 = 4384817) B4384817
theorem B1948807 : Blo 1947435 1948807 := bstep (se 1 (by rfl) ⟨1461605, by rfl⟩ : syracuseStep 1948807 = 2923211) B2923211
theorem B2192413 : Blo 1947435 2192413 := bbase (se 3 (by rfl) ⟨411077, by rfl⟩ : syracuseStep 2192413 = 822155) (by norm_num)
theorem B2923217 : Blo 1947435 2923217 := bstep (se 2 (by rfl) ⟨1096206, by rfl⟩ : syracuseStep 2923217 = 2192413) B2192413
theorem B1948811 : Blo 1947435 1948811 := bstep (se 1 (by rfl) ⟨1461608, by rfl⟩ : syracuseStep 1948811 = 2923217) B2923217
theorem B6577253 : Blo 1947435 6577253 := bbase (se 4 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 6577253 = 1233235) (by norm_num)
theorem B4384835 : Blo 1947435 4384835 := bstep (se 1 (by rfl) ⟨3288626, by rfl⟩ : syracuseStep 4384835 = 6577253) B6577253
theorem B2923223 : Blo 1947435 2923223 := bstep (se 1 (by rfl) ⟨2192417, by rfl⟩ : syracuseStep 2923223 = 4384835) B4384835
theorem B1948815 : Blo 1947435 1948815 := bstep (se 1 (by rfl) ⟨1461611, by rfl⟩ : syracuseStep 1948815 = 2923223) B2923223
theorem B2923229 : Blo 1947435 2923229 := bbase (se 3 (by rfl) ⟨548105, by rfl⟩ : syracuseStep 2923229 = 1096211) (by norm_num)
theorem B1948819 : Blo 1947435 1948819 := bstep (se 1 (by rfl) ⟨1461614, by rfl⟩ : syracuseStep 1948819 = 2923229) B2923229
theorem B4384853 : Blo 1947435 4384853 := bbase (se 8 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 4384853 = 51385) (by norm_num)
theorem B2923235 : Blo 1947435 2923235 := bstep (se 1 (by rfl) ⟨2192426, by rfl⟩ : syracuseStep 2923235 = 4384853) B4384853
theorem B1948823 : Blo 1947435 1948823 := bstep (se 1 (by rfl) ⟨1461617, by rfl⟩ : syracuseStep 1948823 = 2923235) B2923235
theorem B3511853 : Blo 1947435 3511853 := bbase (se 3 (by rfl) ⟨658472, by rfl⟩ : syracuseStep 3511853 = 1316945) (by norm_num)
theorem B2341235 : Blo 1947435 2341235 := bstep (se 1 (by rfl) ⟨1755926, by rfl⟩ : syracuseStep 2341235 = 3511853) B3511853
theorem B6243293 : Blo 1947435 6243293 := bstep (se 3 (by rfl) ⟨1170617, by rfl⟩ : syracuseStep 6243293 = 2341235) B2341235
theorem B4162195 : Blo 1947435 4162195 := bstep (se 1 (by rfl) ⟨3121646, by rfl⟩ : syracuseStep 4162195 = 6243293) B6243293
theorem B5549593 : Blo 1947435 5549593 := bstep (se 2 (by rfl) ⟨2081097, by rfl⟩ : syracuseStep 5549593 = 4162195) B4162195
theorem B7399457 : Blo 1947435 7399457 := bstep (se 2 (by rfl) ⟨2774796, by rfl⟩ : syracuseStep 7399457 = 5549593) B5549593
theorem B4932971 : Blo 1947435 4932971 := bstep (se 1 (by rfl) ⟨3699728, by rfl⟩ : syracuseStep 4932971 = 7399457) B7399457
theorem B3288647 : Blo 1947435 3288647 := bstep (se 1 (by rfl) ⟨2466485, by rfl⟩ : syracuseStep 3288647 = 4932971) B4932971
theorem B2192431 : Blo 1947435 2192431 := bstep (se 1 (by rfl) ⟨1644323, by rfl⟩ : syracuseStep 2192431 = 3288647) B3288647
theorem B2923241 : Blo 1947435 2923241 := bstep (se 2 (by rfl) ⟨1096215, by rfl⟩ : syracuseStep 2923241 = 2192431) B2192431
theorem B1948827 : Blo 1947435 1948827 := bstep (se 1 (by rfl) ⟨1461620, by rfl⟩ : syracuseStep 1948827 = 2923241) B2923241
theorem B5000285 : Blo 1947435 5000285 := bbase (se 3 (by rfl) ⟨937553, by rfl⟩ : syracuseStep 5000285 = 1875107) (by norm_num)
theorem B3333523 : Blo 1947435 3333523 := bstep (se 1 (by rfl) ⟨2500142, by rfl⟩ : syracuseStep 3333523 = 5000285) B5000285
theorem B4444697 : Blo 1947435 4444697 := bstep (se 2 (by rfl) ⟨1666761, by rfl⟩ : syracuseStep 4444697 = 3333523) B3333523
theorem B2963131 : Blo 1947435 2963131 := bstep (se 1 (by rfl) ⟨2222348, by rfl⟩ : syracuseStep 2963131 = 4444697) B4444697
theorem B15803365 : Blo 1947435 15803365 := bstep (se 4 (by rfl) ⟨1481565, by rfl⟩ : syracuseStep 15803365 = 2963131) B2963131
theorem B21071153 : Blo 1947435 21071153 := bstep (se 2 (by rfl) ⟨7901682, by rfl⟩ : syracuseStep 21071153 = 15803365) B15803365
theorem B14047435 : Blo 1947435 14047435 := bstep (se 1 (by rfl) ⟨10535576, by rfl⟩ : syracuseStep 14047435 = 21071153) B21071153
theorem B18729913 : Blo 1947435 18729913 := bstep (se 2 (by rfl) ⟨7023717, by rfl⟩ : syracuseStep 18729913 = 14047435) B14047435
theorem B24973217 : Blo 1947435 24973217 := bstep (se 2 (by rfl) ⟨9364956, by rfl⟩ : syracuseStep 24973217 = 18729913) B18729913
theorem B16648811 : Blo 1947435 16648811 := bstep (se 1 (by rfl) ⟨12486608, by rfl⟩ : syracuseStep 16648811 = 24973217) B24973217
theorem B11099207 : Blo 1947435 11099207 := bstep (se 1 (by rfl) ⟨8324405, by rfl⟩ : syracuseStep 11099207 = 16648811) B16648811
theorem B7399471 : Blo 1947435 7399471 := bstep (se 1 (by rfl) ⟨5549603, by rfl⟩ : syracuseStep 7399471 = 11099207) B11099207
theorem B9865961 : Blo 1947435 9865961 := bstep (se 2 (by rfl) ⟨3699735, by rfl⟩ : syracuseStep 9865961 = 7399471) B7399471
theorem B6577307 : Blo 1947435 6577307 := bstep (se 1 (by rfl) ⟨4932980, by rfl⟩ : syracuseStep 6577307 = 9865961) B9865961
theorem B4384871 : Blo 1947435 4384871 := bstep (se 1 (by rfl) ⟨3288653, by rfl⟩ : syracuseStep 4384871 = 6577307) B6577307
theorem B2923247 : Blo 1947435 2923247 := bstep (se 1 (by rfl) ⟨2192435, by rfl⟩ : syracuseStep 2923247 = 4384871) B4384871
theorem B1948831 : Blo 1947435 1948831 := bstep (se 1 (by rfl) ⟨1461623, by rfl⟩ : syracuseStep 1948831 = 2923247) B2923247
theorem B2923253 : Blo 1947435 2923253 := bbase (se 5 (by rfl) ⟨137027, by rfl⟩ : syracuseStep 2923253 = 274055) (by norm_num)
theorem B1948835 : Blo 1947435 1948835 := bstep (se 1 (by rfl) ⟨1461626, by rfl⟩ : syracuseStep 1948835 = 2923253) B2923253
theorem B9364997 : Blo 1947435 9364997 := bbase (se 4 (by rfl) ⟨877968, by rfl⟩ : syracuseStep 9364997 = 1755937) (by norm_num)
theorem B6243331 : Blo 1947435 6243331 := bstep (se 1 (by rfl) ⟨4682498, by rfl⟩ : syracuseStep 6243331 = 9364997) B9364997
theorem B8324441 : Blo 1947435 8324441 := bstep (se 2 (by rfl) ⟨3121665, by rfl⟩ : syracuseStep 8324441 = 6243331) B6243331
theorem B5549627 : Blo 1947435 5549627 := bstep (se 1 (by rfl) ⟨4162220, by rfl⟩ : syracuseStep 5549627 = 8324441) B8324441
theorem B3699751 : Blo 1947435 3699751 := bstep (se 1 (by rfl) ⟨2774813, by rfl⟩ : syracuseStep 3699751 = 5549627) B5549627
theorem B4933001 : Blo 1947435 4933001 := bstep (se 2 (by rfl) ⟨1849875, by rfl⟩ : syracuseStep 4933001 = 3699751) B3699751
theorem B3288667 : Blo 1947435 3288667 := bstep (se 1 (by rfl) ⟨2466500, by rfl⟩ : syracuseStep 3288667 = 4933001) B4933001
theorem B4384889 : Blo 1947435 4384889 := bstep (se 2 (by rfl) ⟨1644333, by rfl⟩ : syracuseStep 4384889 = 3288667) B3288667
theorem B2923259 : Blo 1947435 2923259 := bstep (se 1 (by rfl) ⟨2192444, by rfl⟩ : syracuseStep 2923259 = 4384889) B4384889
theorem B1948839 : Blo 1947435 1948839 := bstep (se 1 (by rfl) ⟨1461629, by rfl⟩ : syracuseStep 1948839 = 2923259) B2923259
theorem B2192449 : Blo 1947435 2192449 := bbase (se 2 (by rfl) ⟨822168, by rfl⟩ : syracuseStep 2192449 = 1644337) (by norm_num)
theorem B2923265 : Blo 1947435 2923265 := bstep (se 2 (by rfl) ⟨1096224, by rfl⟩ : syracuseStep 2923265 = 2192449) B2192449
theorem B1948843 : Blo 1947435 1948843 := bstep (se 1 (by rfl) ⟨1461632, by rfl⟩ : syracuseStep 1948843 = 2923265) B2923265
theorem B4933021 : Blo 1947435 4933021 := bbase (se 3 (by rfl) ⟨924941, by rfl⟩ : syracuseStep 4933021 = 1849883) (by norm_num)
theorem B6577361 : Blo 1947435 6577361 := bstep (se 2 (by rfl) ⟨2466510, by rfl⟩ : syracuseStep 6577361 = 4933021) B4933021
theorem B4384907 : Blo 1947435 4384907 := bstep (se 1 (by rfl) ⟨3288680, by rfl⟩ : syracuseStep 4384907 = 6577361) B6577361
theorem B2923271 : Blo 1947435 2923271 := bstep (se 1 (by rfl) ⟨2192453, by rfl⟩ : syracuseStep 2923271 = 4384907) B4384907
theorem B1948847 : Blo 1947435 1948847 := bstep (se 1 (by rfl) ⟨1461635, by rfl⟩ : syracuseStep 1948847 = 2923271) B2923271
theorem B2923277 : Blo 1947435 2923277 := bbase (se 3 (by rfl) ⟨548114, by rfl⟩ : syracuseStep 2923277 = 1096229) (by norm_num)
theorem B1948851 : Blo 1947435 1948851 := bstep (se 1 (by rfl) ⟨1461638, by rfl⟩ : syracuseStep 1948851 = 2923277) B2923277
theorem B4384925 : Blo 1947435 4384925 := bbase (se 3 (by rfl) ⟨822173, by rfl⟩ : syracuseStep 4384925 = 1644347) (by norm_num)
theorem B2923283 : Blo 1947435 2923283 := bstep (se 1 (by rfl) ⟨2192462, by rfl⟩ : syracuseStep 2923283 = 4384925) B4384925
theorem B1948855 : Blo 1947435 1948855 := bstep (se 1 (by rfl) ⟨1461641, by rfl⟩ : syracuseStep 1948855 = 2923283) B2923283
theorem B3288701 : Blo 1947435 3288701 := bbase (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) (by norm_num)
theorem B2192467 : Blo 1947435 2192467 := bstep (se 1 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 2192467 = 3288701) B3288701
theorem B2923289 : Blo 1947435 2923289 := bstep (se 2 (by rfl) ⟨1096233, by rfl⟩ : syracuseStep 2923289 = 2192467) B2192467
theorem B1948859 : Blo 1947435 1948859 := bstep (se 1 (by rfl) ⟨1461644, by rfl⟩ : syracuseStep 1948859 = 2923289) B2923289
theorem B7901813 : Blo 1947435 7901813 := bbase (se 5 (by rfl) ⟨370397, by rfl⟩ : syracuseStep 7901813 = 740795) (by norm_num)
theorem B21071501 : Blo 1947435 21071501 := bstep (se 3 (by rfl) ⟨3950906, by rfl⟩ : syracuseStep 21071501 = 7901813) B7901813
theorem B14047667 : Blo 1947435 14047667 := bstep (se 1 (by rfl) ⟨10535750, by rfl⟩ : syracuseStep 14047667 = 21071501) B21071501
theorem B9365111 : Blo 1947435 9365111 := bstep (se 1 (by rfl) ⟨7023833, by rfl⟩ : syracuseStep 9365111 = 14047667) B14047667
theorem B6243407 : Blo 1947435 6243407 := bstep (se 1 (by rfl) ⟨4682555, by rfl⟩ : syracuseStep 6243407 = 9365111) B9365111
theorem B4162271 : Blo 1947435 4162271 := bstep (se 1 (by rfl) ⟨3121703, by rfl⟩ : syracuseStep 4162271 = 6243407) B6243407
theorem B11099389 : Blo 1947435 11099389 := bstep (se 3 (by rfl) ⟨2081135, by rfl⟩ : syracuseStep 11099389 = 4162271) B4162271
theorem B14799185 : Blo 1947435 14799185 := bstep (se 2 (by rfl) ⟨5549694, by rfl⟩ : syracuseStep 14799185 = 11099389) B11099389
theorem B9866123 : Blo 1947435 9866123 := bstep (se 1 (by rfl) ⟨7399592, by rfl⟩ : syracuseStep 9866123 = 14799185) B14799185
theorem B6577415 : Blo 1947435 6577415 := bstep (se 1 (by rfl) ⟨4933061, by rfl⟩ : syracuseStep 6577415 = 9866123) B9866123
theorem B4384943 : Blo 1947435 4384943 := bstep (se 1 (by rfl) ⟨3288707, by rfl⟩ : syracuseStep 4384943 = 6577415) B6577415
theorem B2923295 : Blo 1947435 2923295 := bstep (se 1 (by rfl) ⟨2192471, by rfl⟩ : syracuseStep 2923295 = 4384943) B4384943
theorem B1948863 : Blo 1947435 1948863 := bstep (se 1 (by rfl) ⟨1461647, by rfl⟩ : syracuseStep 1948863 = 2923295) B2923295
theorem B2923301 : Blo 1947435 2923301 := bbase (se 4 (by rfl) ⟨274059, by rfl⟩ : syracuseStep 2923301 = 548119) (by norm_num)
theorem B1948867 : Blo 1947435 1948867 := bstep (se 1 (by rfl) ⟨1461650, by rfl⟩ : syracuseStep 1948867 = 2923301) B2923301
theorem B2466541 : Blo 1947435 2466541 := bbase (se 3 (by rfl) ⟨462476, by rfl⟩ : syracuseStep 2466541 = 924953) (by norm_num)
theorem B3288721 : Blo 1947435 3288721 := bstep (se 2 (by rfl) ⟨1233270, by rfl⟩ : syracuseStep 3288721 = 2466541) B2466541
theorem B4384961 : Blo 1947435 4384961 := bstep (se 2 (by rfl) ⟨1644360, by rfl⟩ : syracuseStep 4384961 = 3288721) B3288721
theorem B2923307 : Blo 1947435 2923307 := bstep (se 1 (by rfl) ⟨2192480, by rfl⟩ : syracuseStep 2923307 = 4384961) B4384961
theorem B1948871 : Blo 1947435 1948871 := bstep (se 1 (by rfl) ⟨1461653, by rfl⟩ : syracuseStep 1948871 = 2923307) B2923307
theorem B2192485 : Blo 1947435 2192485 := bbase (se 4 (by rfl) ⟨205545, by rfl⟩ : syracuseStep 2192485 = 411091) (by norm_num)
theorem B2923313 : Blo 1947435 2923313 := bstep (se 2 (by rfl) ⟨1096242, by rfl⟩ : syracuseStep 2923313 = 2192485) B2192485
theorem B1948875 : Blo 1947435 1948875 := bstep (se 1 (by rfl) ⟨1461656, by rfl⟩ : syracuseStep 1948875 = 2923313) B2923313
theorem B2081153 : Blo 1947435 2081153 := bbase (se 2 (by rfl) ⟨780432, by rfl⟩ : syracuseStep 2081153 = 1560865) (by norm_num)
theorem B5549741 : Blo 1947435 5549741 := bstep (se 3 (by rfl) ⟨1040576, by rfl⟩ : syracuseStep 5549741 = 2081153) B2081153
theorem B3699827 : Blo 1947435 3699827 := bstep (se 1 (by rfl) ⟨2774870, by rfl⟩ : syracuseStep 3699827 = 5549741) B5549741
theorem B2466551 : Blo 1947435 2466551 := bstep (se 1 (by rfl) ⟨1849913, by rfl⟩ : syracuseStep 2466551 = 3699827) B3699827
theorem B6577469 : Blo 1947435 6577469 := bstep (se 3 (by rfl) ⟨1233275, by rfl⟩ : syracuseStep 6577469 = 2466551) B2466551
theorem B4384979 : Blo 1947435 4384979 := bstep (se 1 (by rfl) ⟨3288734, by rfl⟩ : syracuseStep 4384979 = 6577469) B6577469
theorem B2923319 : Blo 1947435 2923319 := bstep (se 1 (by rfl) ⟨2192489, by rfl⟩ : syracuseStep 2923319 = 4384979) B4384979
theorem B1948879 : Blo 1947435 1948879 := bstep (se 1 (by rfl) ⟨1461659, by rfl⟩ : syracuseStep 1948879 = 2923319) B2923319
theorem B2923325 : Blo 1947435 2923325 := bbase (se 3 (by rfl) ⟨548123, by rfl⟩ : syracuseStep 2923325 = 1096247) (by norm_num)
theorem B1948883 : Blo 1947435 1948883 := bstep (se 1 (by rfl) ⟨1461662, by rfl⟩ : syracuseStep 1948883 = 2923325) B2923325
theorem B4384997 : Blo 1947435 4384997 := bbase (se 4 (by rfl) ⟨411093, by rfl⟩ : syracuseStep 4384997 = 822187) (by norm_num)
theorem B2923331 : Blo 1947435 2923331 := bstep (se 1 (by rfl) ⟨2192498, by rfl⟩ : syracuseStep 2923331 = 4384997) B4384997
theorem B1948887 : Blo 1947435 1948887 := bstep (se 1 (by rfl) ⟨1461665, by rfl⟩ : syracuseStep 1948887 = 2923331) B2923331
theorem B4933133 : Blo 1947435 4933133 := bbase (se 3 (by rfl) ⟨924962, by rfl⟩ : syracuseStep 4933133 = 1849925) (by norm_num)
theorem B3288755 : Blo 1947435 3288755 := bstep (se 1 (by rfl) ⟨2466566, by rfl⟩ : syracuseStep 3288755 = 4933133) B4933133
theorem B2192503 : Blo 1947435 2192503 := bstep (se 1 (by rfl) ⟨1644377, by rfl⟩ : syracuseStep 2192503 = 3288755) B3288755
theorem B2923337 : Blo 1947435 2923337 := bstep (se 2 (by rfl) ⟨1096251, by rfl⟩ : syracuseStep 2923337 = 2192503) B2192503
theorem B1948891 : Blo 1947435 1948891 := bstep (se 1 (by rfl) ⟨1461668, by rfl⟩ : syracuseStep 1948891 = 2923337) B2923337
theorem B2774893 : Blo 1947435 2774893 := bbase (se 3 (by rfl) ⟨520292, by rfl⟩ : syracuseStep 2774893 = 1040585) (by norm_num)
theorem B3699857 : Blo 1947435 3699857 := bstep (se 2 (by rfl) ⟨1387446, by rfl⟩ : syracuseStep 3699857 = 2774893) B2774893
theorem B9866285 : Blo 1947435 9866285 := bstep (se 3 (by rfl) ⟨1849928, by rfl⟩ : syracuseStep 9866285 = 3699857) B3699857
theorem B6577523 : Blo 1947435 6577523 := bstep (se 1 (by rfl) ⟨4933142, by rfl⟩ : syracuseStep 6577523 = 9866285) B9866285
theorem B4385015 : Blo 1947435 4385015 := bstep (se 1 (by rfl) ⟨3288761, by rfl⟩ : syracuseStep 4385015 = 6577523) B6577523
theorem B2923343 : Blo 1947435 2923343 := bstep (se 1 (by rfl) ⟨2192507, by rfl⟩ : syracuseStep 2923343 = 4385015) B4385015
theorem B1948895 : Blo 1947435 1948895 := bstep (se 1 (by rfl) ⟨1461671, by rfl⟩ : syracuseStep 1948895 = 2923343) B2923343
theorem B2923349 : Blo 1947435 2923349 := bbase (se 9 (by rfl) ⟨8564, by rfl⟩ : syracuseStep 2923349 = 17129) (by norm_num)
theorem B1948899 : Blo 1947435 1948899 := bstep (se 1 (by rfl) ⟨1461674, by rfl⟩ : syracuseStep 1948899 = 2923349) B2923349
theorem B4162357 : Blo 1947435 4162357 := bbase (se 5 (by rfl) ⟨195110, by rfl⟩ : syracuseStep 4162357 = 390221) (by norm_num)
theorem B5549809 : Blo 1947435 5549809 := bstep (se 2 (by rfl) ⟨2081178, by rfl⟩ : syracuseStep 5549809 = 4162357) B4162357
theorem B7399745 : Blo 1947435 7399745 := bstep (se 2 (by rfl) ⟨2774904, by rfl⟩ : syracuseStep 7399745 = 5549809) B5549809
theorem B4933163 : Blo 1947435 4933163 := bstep (se 1 (by rfl) ⟨3699872, by rfl⟩ : syracuseStep 4933163 = 7399745) B7399745
theorem B3288775 : Blo 1947435 3288775 := bstep (se 1 (by rfl) ⟨2466581, by rfl⟩ : syracuseStep 3288775 = 4933163) B4933163
theorem B4385033 : Blo 1947435 4385033 := bstep (se 2 (by rfl) ⟨1644387, by rfl⟩ : syracuseStep 4385033 = 3288775) B3288775
theorem B2923355 : Blo 1947435 2923355 := bstep (se 1 (by rfl) ⟨2192516, by rfl⟩ : syracuseStep 2923355 = 4385033) B4385033
theorem B1948903 : Blo 1947435 1948903 := bstep (se 1 (by rfl) ⟨1461677, by rfl⟩ : syracuseStep 1948903 = 2923355) B2923355
theorem B2192521 : Blo 1947435 2192521 := bbase (se 2 (by rfl) ⟨822195, by rfl⟩ : syracuseStep 2192521 = 1644391) (by norm_num)
theorem B2923361 : Blo 1947435 2923361 := bstep (se 2 (by rfl) ⟨1096260, by rfl⟩ : syracuseStep 2923361 = 2192521) B2192521
theorem B1948907 : Blo 1947435 1948907 := bstep (se 1 (by rfl) ⟨1461680, by rfl⟩ : syracuseStep 1948907 = 2923361) B2923361
theorem B5268005 : Blo 1947435 5268005 := bbase (se 4 (by rfl) ⟨493875, by rfl⟩ : syracuseStep 5268005 = 987751) (by norm_num)
theorem B3512003 : Blo 1947435 3512003 := bstep (se 1 (by rfl) ⟨2634002, by rfl⟩ : syracuseStep 3512003 = 5268005) B5268005
theorem B37461365 : Blo 1947435 37461365 := bstep (se 5 (by rfl) ⟨1756001, by rfl⟩ : syracuseStep 37461365 = 3512003) B3512003
theorem B24974243 : Blo 1947435 24974243 := bstep (se 1 (by rfl) ⟨18730682, by rfl⟩ : syracuseStep 24974243 = 37461365) B37461365
theorem B16649495 : Blo 1947435 16649495 := bstep (se 1 (by rfl) ⟨12487121, by rfl⟩ : syracuseStep 16649495 = 24974243) B24974243
theorem B11099663 : Blo 1947435 11099663 := bstep (se 1 (by rfl) ⟨8324747, by rfl⟩ : syracuseStep 11099663 = 16649495) B16649495
theorem B7399775 : Blo 1947435 7399775 := bstep (se 1 (by rfl) ⟨5549831, by rfl⟩ : syracuseStep 7399775 = 11099663) B11099663
theorem B4933183 : Blo 1947435 4933183 := bstep (se 1 (by rfl) ⟨3699887, by rfl⟩ : syracuseStep 4933183 = 7399775) B7399775
theorem B6577577 : Blo 1947435 6577577 := bstep (se 2 (by rfl) ⟨2466591, by rfl⟩ : syracuseStep 6577577 = 4933183) B4933183
theorem B4385051 : Blo 1947435 4385051 := bstep (se 1 (by rfl) ⟨3288788, by rfl⟩ : syracuseStep 4385051 = 6577577) B6577577
theorem B2923367 : Blo 1947435 2923367 := bstep (se 1 (by rfl) ⟨2192525, by rfl⟩ : syracuseStep 2923367 = 4385051) B4385051
theorem B1948911 : Blo 1947435 1948911 := bstep (se 1 (by rfl) ⟨1461683, by rfl⟩ : syracuseStep 1948911 = 2923367) B2923367
theorem B2923373 : Blo 1947435 2923373 := bbase (se 3 (by rfl) ⟨548132, by rfl⟩ : syracuseStep 2923373 = 1096265) (by norm_num)
theorem B1948915 : Blo 1947435 1948915 := bstep (se 1 (by rfl) ⟨1461686, by rfl⟩ : syracuseStep 1948915 = 2923373) B2923373
theorem B4385069 : Blo 1947435 4385069 := bbase (se 3 (by rfl) ⟨822200, by rfl⟩ : syracuseStep 4385069 = 1644401) (by norm_num)
theorem B2923379 : Blo 1947435 2923379 := bstep (se 1 (by rfl) ⟨2192534, by rfl⟩ : syracuseStep 2923379 = 4385069) B4385069
theorem B1948919 : Blo 1947435 1948919 := bstep (se 1 (by rfl) ⟨1461689, by rfl⟩ : syracuseStep 1948919 = 2923379) B2923379
theorem B4682701 : Blo 1947435 4682701 := bbase (se 3 (by rfl) ⟨878006, by rfl⟩ : syracuseStep 4682701 = 1756013) (by norm_num)
theorem B6243601 : Blo 1947435 6243601 := bstep (se 2 (by rfl) ⟨2341350, by rfl⟩ : syracuseStep 6243601 = 4682701) B4682701
theorem B8324801 : Blo 1947435 8324801 := bstep (se 2 (by rfl) ⟨3121800, by rfl⟩ : syracuseStep 8324801 = 6243601) B6243601
theorem B5549867 : Blo 1947435 5549867 := bstep (se 1 (by rfl) ⟨4162400, by rfl⟩ : syracuseStep 5549867 = 8324801) B8324801
theorem B3699911 : Blo 1947435 3699911 := bstep (se 1 (by rfl) ⟨2774933, by rfl⟩ : syracuseStep 3699911 = 5549867) B5549867
theorem B2466607 : Blo 1947435 2466607 := bstep (se 1 (by rfl) ⟨1849955, by rfl⟩ : syracuseStep 2466607 = 3699911) B3699911
theorem B3288809 : Blo 1947435 3288809 := bstep (se 2 (by rfl) ⟨1233303, by rfl⟩ : syracuseStep 3288809 = 2466607) B2466607
theorem B2192539 : Blo 1947435 2192539 := bstep (se 1 (by rfl) ⟨1644404, by rfl⟩ : syracuseStep 2192539 = 3288809) B3288809
theorem B2923385 : Blo 1947435 2923385 := bstep (se 2 (by rfl) ⟨1096269, by rfl⟩ : syracuseStep 2923385 = 2192539) B2192539
theorem B1948923 : Blo 1947435 1948923 := bstep (se 1 (by rfl) ⟨1461692, by rfl⟩ : syracuseStep 1948923 = 2923385) B2923385
theorem B57736277 : Blo 1947435 57736277 := bbase (se 8 (by rfl) ⟨338298, by rfl⟩ : syracuseStep 57736277 = 676597) (by norm_num)
theorem B38490851 : Blo 1947435 38490851 := bstep (se 1 (by rfl) ⟨28868138, by rfl⟩ : syracuseStep 38490851 = 57736277) B57736277
theorem B25660567 : Blo 1947435 25660567 := bstep (se 1 (by rfl) ⟨19245425, by rfl⟩ : syracuseStep 25660567 = 38490851) B38490851
theorem B34214089 : Blo 1947435 34214089 := bstep (se 2 (by rfl) ⟨12830283, by rfl⟩ : syracuseStep 34214089 = 25660567) B25660567
theorem B45618785 : Blo 1947435 45618785 := bstep (se 2 (by rfl) ⟨17107044, by rfl⟩ : syracuseStep 45618785 = 34214089) B34214089
theorem B30412523 : Blo 1947435 30412523 := bstep (se 1 (by rfl) ⟨22809392, by rfl⟩ : syracuseStep 30412523 = 45618785) B45618785
theorem B81100061 : Blo 1947435 81100061 := bstep (se 3 (by rfl) ⟨15206261, by rfl⟩ : syracuseStep 81100061 = 30412523) B30412523
theorem B54066707 : Blo 1947435 54066707 := bstep (se 1 (by rfl) ⟨40550030, by rfl⟩ : syracuseStep 54066707 = 81100061) B81100061
theorem B36044471 : Blo 1947435 36044471 := bstep (se 1 (by rfl) ⟨27033353, by rfl⟩ : syracuseStep 36044471 = 54066707) B54066707
theorem B96118589 : Blo 1947435 96118589 := bstep (se 3 (by rfl) ⟨18022235, by rfl⟩ : syracuseStep 96118589 = 36044471) B36044471
theorem B64079059 : Blo 1947435 64079059 := bstep (se 1 (by rfl) ⟨48059294, by rfl⟩ : syracuseStep 64079059 = 96118589) B96118589
theorem B85438745 : Blo 1947435 85438745 := bstep (se 2 (by rfl) ⟨32039529, by rfl⟩ : syracuseStep 85438745 = 64079059) B64079059
theorem B56959163 : Blo 1947435 56959163 := bstep (se 1 (by rfl) ⟨42719372, by rfl⟩ : syracuseStep 56959163 = 85438745) B85438745
theorem B37972775 : Blo 1947435 37972775 := bstep (se 1 (by rfl) ⟨28479581, by rfl⟩ : syracuseStep 37972775 = 56959163) B56959163
theorem B25315183 : Blo 1947435 25315183 := bstep (se 1 (by rfl) ⟨18986387, by rfl⟩ : syracuseStep 25315183 = 37972775) B37972775
theorem B135014309 : Blo 1947435 135014309 := bstep (se 4 (by rfl) ⟨12657591, by rfl⟩ : syracuseStep 135014309 = 25315183) B25315183
theorem B90009539 : Blo 1947435 90009539 := bstep (se 1 (by rfl) ⟨67507154, by rfl⟩ : syracuseStep 90009539 = 135014309) B135014309
theorem B60006359 : Blo 1947435 60006359 := bstep (se 1 (by rfl) ⟨45004769, by rfl⟩ : syracuseStep 60006359 = 90009539) B90009539
theorem B40004239 : Blo 1947435 40004239 := bstep (se 1 (by rfl) ⟨30003179, by rfl⟩ : syracuseStep 40004239 = 60006359) B60006359
theorem B53338985 : Blo 1947435 53338985 := bstep (se 2 (by rfl) ⟨20002119, by rfl⟩ : syracuseStep 53338985 = 40004239) B40004239
theorem B35559323 : Blo 1947435 35559323 := bstep (se 1 (by rfl) ⟨26669492, by rfl⟩ : syracuseStep 35559323 = 53338985) B53338985
theorem B23706215 : Blo 1947435 23706215 := bstep (se 1 (by rfl) ⟨17779661, by rfl⟩ : syracuseStep 23706215 = 35559323) B35559323
theorem B15804143 : Blo 1947435 15804143 := bstep (se 1 (by rfl) ⟨11853107, by rfl⟩ : syracuseStep 15804143 = 23706215) B23706215
theorem B10536095 : Blo 1947435 10536095 := bstep (se 1 (by rfl) ⟨7902071, by rfl⟩ : syracuseStep 10536095 = 15804143) B15804143
theorem B28096253 : Blo 1947435 28096253 := bstep (se 3 (by rfl) ⟨5268047, by rfl⟩ : syracuseStep 28096253 = 10536095) B10536095
theorem B18730835 : Blo 1947435 18730835 := bstep (se 1 (by rfl) ⟨14048126, by rfl⟩ : syracuseStep 18730835 = 28096253) B28096253
theorem B12487223 : Blo 1947435 12487223 := bstep (se 1 (by rfl) ⟨9365417, by rfl⟩ : syracuseStep 12487223 = 18730835) B18730835
theorem B33299261 : Blo 1947435 33299261 := bstep (se 3 (by rfl) ⟨6243611, by rfl⟩ : syracuseStep 33299261 = 12487223) B12487223
theorem B22199507 : Blo 1947435 22199507 := bstep (se 1 (by rfl) ⟨16649630, by rfl⟩ : syracuseStep 22199507 = 33299261) B33299261
theorem B14799671 : Blo 1947435 14799671 := bstep (se 1 (by rfl) ⟨11099753, by rfl⟩ : syracuseStep 14799671 = 22199507) B22199507
theorem B9866447 : Blo 1947435 9866447 := bstep (se 1 (by rfl) ⟨7399835, by rfl⟩ : syracuseStep 9866447 = 14799671) B14799671
theorem B6577631 : Blo 1947435 6577631 := bstep (se 1 (by rfl) ⟨4933223, by rfl⟩ : syracuseStep 6577631 = 9866447) B9866447
theorem B4385087 : Blo 1947435 4385087 := bstep (se 1 (by rfl) ⟨3288815, by rfl⟩ : syracuseStep 4385087 = 6577631) B6577631
theorem B2923391 : Blo 1947435 2923391 := bstep (se 1 (by rfl) ⟨2192543, by rfl⟩ : syracuseStep 2923391 = 4385087) B4385087
theorem B1948927 : Blo 1947435 1948927 := bstep (se 1 (by rfl) ⟨1461695, by rfl⟩ : syracuseStep 1948927 = 2923391) B2923391
theorem B2923397 : Blo 1947435 2923397 := bbase (se 4 (by rfl) ⟨274068, by rfl⟩ : syracuseStep 2923397 = 548137) (by norm_num)
theorem B1948931 : Blo 1947435 1948931 := bstep (se 1 (by rfl) ⟨1461698, by rfl⟩ : syracuseStep 1948931 = 2923397) B2923397
theorem B3288829 : Blo 1947435 3288829 := bbase (se 3 (by rfl) ⟨616655, by rfl⟩ : syracuseStep 3288829 = 1233311) (by norm_num)
theorem B4385105 : Blo 1947435 4385105 := bstep (se 2 (by rfl) ⟨1644414, by rfl⟩ : syracuseStep 4385105 = 3288829) B3288829
theorem B2923403 : Blo 1947435 2923403 := bstep (se 1 (by rfl) ⟨2192552, by rfl⟩ : syracuseStep 2923403 = 4385105) B4385105
theorem B1948935 : Blo 1947435 1948935 := bstep (se 1 (by rfl) ⟨1461701, by rfl⟩ : syracuseStep 1948935 = 2923403) B2923403
theorem B2192557 : Blo 1947435 2192557 := bbase (se 3 (by rfl) ⟨411104, by rfl⟩ : syracuseStep 2192557 = 822209) (by norm_num)
theorem B2923409 : Blo 1947435 2923409 := bstep (se 2 (by rfl) ⟨1096278, by rfl⟩ : syracuseStep 2923409 = 2192557) B2192557
theorem B1948939 : Blo 1947435 1948939 := bstep (se 1 (by rfl) ⟨1461704, by rfl⟩ : syracuseStep 1948939 = 2923409) B2923409
theorem B6577685 : Blo 1947435 6577685 := bbase (se 6 (by rfl) ⟨154164, by rfl⟩ : syracuseStep 6577685 = 308329) (by norm_num)
theorem B4385123 : Blo 1947435 4385123 := bstep (se 1 (by rfl) ⟨3288842, by rfl⟩ : syracuseStep 4385123 = 6577685) B6577685
theorem B2923415 : Blo 1947435 2923415 := bstep (se 1 (by rfl) ⟨2192561, by rfl⟩ : syracuseStep 2923415 = 4385123) B4385123
theorem B1948943 : Blo 1947435 1948943 := bstep (se 1 (by rfl) ⟨1461707, by rfl⟩ : syracuseStep 1948943 = 2923415) B2923415
theorem B2923421 : Blo 1947435 2923421 := bbase (se 3 (by rfl) ⟨548141, by rfl⟩ : syracuseStep 2923421 = 1096283) (by norm_num)
theorem B1948947 : Blo 1947435 1948947 := bstep (se 1 (by rfl) ⟨1461710, by rfl⟩ : syracuseStep 1948947 = 2923421) B2923421
theorem B4385141 : Blo 1947435 4385141 := bbase (se 5 (by rfl) ⟨205553, by rfl⟩ : syracuseStep 4385141 = 411107) (by norm_num)
theorem B2923427 : Blo 1947435 2923427 := bstep (se 1 (by rfl) ⟨2192570, by rfl⟩ : syracuseStep 2923427 = 4385141) B4385141
theorem B1948951 : Blo 1947435 1948951 := bstep (se 1 (by rfl) ⟨1461713, by rfl⟩ : syracuseStep 1948951 = 2923427) B2923427
theorem B7603253 : Blo 1947435 7603253 := bbase (se 5 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 7603253 = 712805) (by norm_num)
theorem B5068835 : Blo 1947435 5068835 := bstep (se 1 (by rfl) ⟨3801626, by rfl⟩ : syracuseStep 5068835 = 7603253) B7603253
theorem B3379223 : Blo 1947435 3379223 := bstep (se 1 (by rfl) ⟨2534417, by rfl⟩ : syracuseStep 3379223 = 5068835) B5068835
theorem B2252815 : Blo 1947435 2252815 := bstep (se 1 (by rfl) ⟨1689611, by rfl⟩ : syracuseStep 2252815 = 3379223) B3379223
theorem B12015013 : Blo 1947435 12015013 := bstep (se 4 (by rfl) ⟨1126407, by rfl⟩ : syracuseStep 12015013 = 2252815) B2252815
theorem B16020017 : Blo 1947435 16020017 := bstep (se 2 (by rfl) ⟨6007506, by rfl⟩ : syracuseStep 16020017 = 12015013) B12015013
theorem B10680011 : Blo 1947435 10680011 := bstep (se 1 (by rfl) ⟨8010008, by rfl⟩ : syracuseStep 10680011 = 16020017) B16020017
theorem B7120007 : Blo 1947435 7120007 := bstep (se 1 (by rfl) ⟨5340005, by rfl⟩ : syracuseStep 7120007 = 10680011) B10680011
theorem B4746671 : Blo 1947435 4746671 := bstep (se 1 (by rfl) ⟨3560003, by rfl⟩ : syracuseStep 4746671 = 7120007) B7120007
theorem B3164447 : Blo 1947435 3164447 := bstep (se 1 (by rfl) ⟨2373335, by rfl⟩ : syracuseStep 3164447 = 4746671) B4746671
theorem B8438525 : Blo 1947435 8438525 := bstep (se 3 (by rfl) ⟨1582223, by rfl⟩ : syracuseStep 8438525 = 3164447) B3164447
theorem B5625683 : Blo 1947435 5625683 := bstep (se 1 (by rfl) ⟨4219262, by rfl⟩ : syracuseStep 5625683 = 8438525) B8438525
theorem B3750455 : Blo 1947435 3750455 := bstep (se 1 (by rfl) ⟨2812841, by rfl⟩ : syracuseStep 3750455 = 5625683) B5625683
theorem B2500303 : Blo 1947435 2500303 := bstep (se 1 (by rfl) ⟨1875227, by rfl⟩ : syracuseStep 2500303 = 3750455) B3750455
theorem B3333737 : Blo 1947435 3333737 := bstep (se 2 (by rfl) ⟨1250151, by rfl⟩ : syracuseStep 3333737 = 2500303) B2500303
theorem B2222491 : Blo 1947435 2222491 := bstep (se 1 (by rfl) ⟨1666868, by rfl⟩ : syracuseStep 2222491 = 3333737) B3333737
theorem B2963321 : Blo 1947435 2963321 := bstep (se 2 (by rfl) ⟨1111245, by rfl⟩ : syracuseStep 2963321 = 2222491) B2222491
theorem B1975547 : Blo 1947435 1975547 := bstep (se 1 (by rfl) ⟨1481660, by rfl⟩ : syracuseStep 1975547 = 2963321) B2963321
theorem B5268125 : Blo 1947435 5268125 := bstep (se 3 (by rfl) ⟨987773, by rfl⟩ : syracuseStep 5268125 = 1975547) B1975547
theorem B3512083 : Blo 1947435 3512083 := bstep (se 1 (by rfl) ⟨2634062, by rfl⟩ : syracuseStep 3512083 = 5268125) B5268125
theorem B4682777 : Blo 1947435 4682777 := bstep (se 2 (by rfl) ⟨1756041, by rfl⟩ : syracuseStep 4682777 = 3512083) B3512083
theorem B12487405 : Blo 1947435 12487405 := bstep (se 3 (by rfl) ⟨2341388, by rfl⟩ : syracuseStep 12487405 = 4682777) B4682777
theorem B16649873 : Blo 1947435 16649873 := bstep (se 2 (by rfl) ⟨6243702, by rfl⟩ : syracuseStep 16649873 = 12487405) B12487405
theorem B11099915 : Blo 1947435 11099915 := bstep (se 1 (by rfl) ⟨8324936, by rfl⟩ : syracuseStep 11099915 = 16649873) B16649873
theorem B7399943 : Blo 1947435 7399943 := bstep (se 1 (by rfl) ⟨5549957, by rfl⟩ : syracuseStep 7399943 = 11099915) B11099915
theorem B4933295 : Blo 1947435 4933295 := bstep (se 1 (by rfl) ⟨3699971, by rfl⟩ : syracuseStep 4933295 = 7399943) B7399943
theorem B3288863 : Blo 1947435 3288863 := bstep (se 1 (by rfl) ⟨2466647, by rfl⟩ : syracuseStep 3288863 = 4933295) B4933295
theorem B2192575 : Blo 1947435 2192575 := bstep (se 1 (by rfl) ⟨1644431, by rfl⟩ : syracuseStep 2192575 = 3288863) B3288863
theorem B2923433 : Blo 1947435 2923433 := bstep (se 2 (by rfl) ⟨1096287, by rfl⟩ : syracuseStep 2923433 = 2192575) B2192575
theorem B1948955 : Blo 1947435 1948955 := bstep (se 1 (by rfl) ⟨1461716, by rfl⟩ : syracuseStep 1948955 = 2923433) B2923433
theorem B7399957 : Blo 1947435 7399957 := bbase (se 6 (by rfl) ⟨173436, by rfl⟩ : syracuseStep 7399957 = 346873) (by norm_num)
theorem B9866609 : Blo 1947435 9866609 := bstep (se 2 (by rfl) ⟨3699978, by rfl⟩ : syracuseStep 9866609 = 7399957) B7399957
theorem B6577739 : Blo 1947435 6577739 := bstep (se 1 (by rfl) ⟨4933304, by rfl⟩ : syracuseStep 6577739 = 9866609) B9866609
theorem B4385159 : Blo 1947435 4385159 := bstep (se 1 (by rfl) ⟨3288869, by rfl⟩ : syracuseStep 4385159 = 6577739) B6577739
theorem B2923439 : Blo 1947435 2923439 := bstep (se 1 (by rfl) ⟨2192579, by rfl⟩ : syracuseStep 2923439 = 4385159) B4385159
theorem B1948959 : Blo 1947435 1948959 := bstep (se 1 (by rfl) ⟨1461719, by rfl⟩ : syracuseStep 1948959 = 2923439) B2923439
theorem B2923445 : Blo 1947435 2923445 := bbase (se 5 (by rfl) ⟨137036, by rfl⟩ : syracuseStep 2923445 = 274073) (by norm_num)
theorem B1948963 : Blo 1947435 1948963 := bstep (se 1 (by rfl) ⟨1461722, by rfl⟩ : syracuseStep 1948963 = 2923445) B2923445
theorem B4933325 : Blo 1947435 4933325 := bbase (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) (by norm_num)
theorem B3288883 : Blo 1947435 3288883 := bstep (se 1 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 3288883 = 4933325) B4933325
theorem B4385177 : Blo 1947435 4385177 := bstep (se 2 (by rfl) ⟨1644441, by rfl⟩ : syracuseStep 4385177 = 3288883) B3288883
theorem B2923451 : Blo 1947435 2923451 := bstep (se 1 (by rfl) ⟨2192588, by rfl⟩ : syracuseStep 2923451 = 4385177) B4385177
theorem B1948967 : Blo 1947435 1948967 := bstep (se 1 (by rfl) ⟨1461725, by rfl⟩ : syracuseStep 1948967 = 2923451) B2923451
theorem B2192593 : Blo 1947435 2192593 := bbase (se 2 (by rfl) ⟨822222, by rfl⟩ : syracuseStep 2192593 = 1644445) (by norm_num)
theorem B2923457 : Blo 1947435 2923457 := bstep (se 2 (by rfl) ⟨1096296, by rfl⟩ : syracuseStep 2923457 = 2192593) B2192593
theorem B1948971 : Blo 1947435 1948971 := bstep (se 1 (by rfl) ⟨1461728, by rfl⟩ : syracuseStep 1948971 = 2923457) B2923457
theorem B6667541 : Blo 1947435 6667541 := bbase (se 6 (by rfl) ⟨156270, by rfl⟩ : syracuseStep 6667541 = 312541) (by norm_num)
theorem B4445027 : Blo 1947435 4445027 := bstep (se 1 (by rfl) ⟨3333770, by rfl⟩ : syracuseStep 4445027 = 6667541) B6667541
theorem B2963351 : Blo 1947435 2963351 := bstep (se 1 (by rfl) ⟨2222513, by rfl⟩ : syracuseStep 2963351 = 4445027) B4445027
theorem B7902269 : Blo 1947435 7902269 := bstep (se 3 (by rfl) ⟨1481675, by rfl⟩ : syracuseStep 7902269 = 2963351) B2963351
theorem B5268179 : Blo 1947435 5268179 := bstep (se 1 (by rfl) ⟨3951134, by rfl⟩ : syracuseStep 5268179 = 7902269) B7902269
theorem B14048477 : Blo 1947435 14048477 := bstep (se 3 (by rfl) ⟨2634089, by rfl⟩ : syracuseStep 14048477 = 5268179) B5268179
theorem B9365651 : Blo 1947435 9365651 := bstep (se 1 (by rfl) ⟨7024238, by rfl⟩ : syracuseStep 9365651 = 14048477) B14048477
theorem B6243767 : Blo 1947435 6243767 := bstep (se 1 (by rfl) ⟨4682825, by rfl⟩ : syracuseStep 6243767 = 9365651) B9365651
theorem B4162511 : Blo 1947435 4162511 := bstep (se 1 (by rfl) ⟨3121883, by rfl⟩ : syracuseStep 4162511 = 6243767) B6243767
theorem B2775007 : Blo 1947435 2775007 := bstep (se 1 (by rfl) ⟨2081255, by rfl⟩ : syracuseStep 2775007 = 4162511) B4162511
theorem B3700009 : Blo 1947435 3700009 := bstep (se 2 (by rfl) ⟨1387503, by rfl⟩ : syracuseStep 3700009 = 2775007) B2775007
theorem B4933345 : Blo 1947435 4933345 := bstep (se 2 (by rfl) ⟨1850004, by rfl⟩ : syracuseStep 4933345 = 3700009) B3700009
theorem B6577793 : Blo 1947435 6577793 := bstep (se 2 (by rfl) ⟨2466672, by rfl⟩ : syracuseStep 6577793 = 4933345) B4933345
theorem B4385195 : Blo 1947435 4385195 := bstep (se 1 (by rfl) ⟨3288896, by rfl⟩ : syracuseStep 4385195 = 6577793) B6577793
theorem B2923463 : Blo 1947435 2923463 := bstep (se 1 (by rfl) ⟨2192597, by rfl⟩ : syracuseStep 2923463 = 4385195) B4385195
theorem B1948975 : Blo 1947435 1948975 := bstep (se 1 (by rfl) ⟨1461731, by rfl⟩ : syracuseStep 1948975 = 2923463) B2923463
theorem B2923469 : Blo 1947435 2923469 := bbase (se 3 (by rfl) ⟨548150, by rfl⟩ : syracuseStep 2923469 = 1096301) (by norm_num)
theorem B1948979 : Blo 1947435 1948979 := bstep (se 1 (by rfl) ⟨1461734, by rfl⟩ : syracuseStep 1948979 = 2923469) B2923469
theorem B4385213 : Blo 1947435 4385213 := bbase (se 3 (by rfl) ⟨822227, by rfl⟩ : syracuseStep 4385213 = 1644455) (by norm_num)
theorem B2923475 : Blo 1947435 2923475 := bstep (se 1 (by rfl) ⟨2192606, by rfl⟩ : syracuseStep 2923475 = 4385213) B4385213
theorem B1948983 : Blo 1947435 1948983 := bstep (se 1 (by rfl) ⟨1461737, by rfl⟩ : syracuseStep 1948983 = 2923475) B2923475
theorem B3288917 : Blo 1947435 3288917 := bbase (se 9 (by rfl) ⟨9635, by rfl⟩ : syracuseStep 3288917 = 19271) (by norm_num)
theorem B2192611 : Blo 1947435 2192611 := bstep (se 1 (by rfl) ⟨1644458, by rfl⟩ : syracuseStep 2192611 = 3288917) B3288917
theorem B2923481 : Blo 1947435 2923481 := bstep (se 2 (by rfl) ⟨1096305, by rfl⟩ : syracuseStep 2923481 = 2192611) B2192611
theorem B1948987 : Blo 1947435 1948987 := bstep (se 1 (by rfl) ⟨1461740, by rfl⟩ : syracuseStep 1948987 = 2923481) B2923481
theorem B7120133 : Blo 1947435 7120133 := bbase (se 4 (by rfl) ⟨667512, by rfl⟩ : syracuseStep 7120133 = 1335025) (by norm_num)
theorem B4746755 : Blo 1947435 4746755 := bstep (se 1 (by rfl) ⟨3560066, by rfl⟩ : syracuseStep 4746755 = 7120133) B7120133
theorem B3164503 : Blo 1947435 3164503 := bstep (se 1 (by rfl) ⟨2373377, by rfl⟩ : syracuseStep 3164503 = 4746755) B4746755
theorem B4219337 : Blo 1947435 4219337 := bstep (se 2 (by rfl) ⟨1582251, by rfl⟩ : syracuseStep 4219337 = 3164503) B3164503
theorem B11251565 : Blo 1947435 11251565 := bstep (se 3 (by rfl) ⟨2109668, by rfl⟩ : syracuseStep 11251565 = 4219337) B4219337
theorem B7501043 : Blo 1947435 7501043 := bstep (se 1 (by rfl) ⟨5625782, by rfl⟩ : syracuseStep 7501043 = 11251565) B11251565
theorem B20002781 : Blo 1947435 20002781 := bstep (se 3 (by rfl) ⟨3750521, by rfl⟩ : syracuseStep 20002781 = 7501043) B7501043
theorem B13335187 : Blo 1947435 13335187 := bstep (se 1 (by rfl) ⟨10001390, by rfl⟩ : syracuseStep 13335187 = 20002781) B20002781
theorem B17780249 : Blo 1947435 17780249 := bstep (se 2 (by rfl) ⟨6667593, by rfl⟩ : syracuseStep 17780249 = 13335187) B13335187
theorem B11853499 : Blo 1947435 11853499 := bstep (se 1 (by rfl) ⟨8890124, by rfl⟩ : syracuseStep 11853499 = 17780249) B17780249
theorem B15804665 : Blo 1947435 15804665 := bstep (se 2 (by rfl) ⟨5926749, by rfl⟩ : syracuseStep 15804665 = 11853499) B11853499
theorem B10536443 : Blo 1947435 10536443 := bstep (se 1 (by rfl) ⟨7902332, by rfl⟩ : syracuseStep 10536443 = 15804665) B15804665
theorem B7024295 : Blo 1947435 7024295 := bstep (se 1 (by rfl) ⟨5268221, by rfl⟩ : syracuseStep 7024295 = 10536443) B10536443
theorem B4682863 : Blo 1947435 4682863 := bstep (se 1 (by rfl) ⟨3512147, by rfl⟩ : syracuseStep 4682863 = 7024295) B7024295
theorem B6243817 : Blo 1947435 6243817 := bstep (se 2 (by rfl) ⟨2341431, by rfl⟩ : syracuseStep 6243817 = 4682863) B4682863
theorem B8325089 : Blo 1947435 8325089 := bstep (se 2 (by rfl) ⟨3121908, by rfl⟩ : syracuseStep 8325089 = 6243817) B6243817
theorem B5550059 : Blo 1947435 5550059 := bstep (se 1 (by rfl) ⟨4162544, by rfl⟩ : syracuseStep 5550059 = 8325089) B8325089
theorem B14800157 : Blo 1947435 14800157 := bstep (se 3 (by rfl) ⟨2775029, by rfl⟩ : syracuseStep 14800157 = 5550059) B5550059
theorem B9866771 : Blo 1947435 9866771 := bstep (se 1 (by rfl) ⟨7400078, by rfl⟩ : syracuseStep 9866771 = 14800157) B14800157
theorem B6577847 : Blo 1947435 6577847 := bstep (se 1 (by rfl) ⟨4933385, by rfl⟩ : syracuseStep 6577847 = 9866771) B9866771
theorem B4385231 : Blo 1947435 4385231 := bstep (se 1 (by rfl) ⟨3288923, by rfl⟩ : syracuseStep 4385231 = 6577847) B6577847
theorem B2923487 : Blo 1947435 2923487 := bstep (se 1 (by rfl) ⟨2192615, by rfl⟩ : syracuseStep 2923487 = 4385231) B4385231
theorem B1948991 : Blo 1947435 1948991 := bstep (se 1 (by rfl) ⟨1461743, by rfl⟩ : syracuseStep 1948991 = 2923487) B2923487
theorem B2923493 : Blo 1947435 2923493 := bbase (se 4 (by rfl) ⟨274077, by rfl⟩ : syracuseStep 2923493 = 548155) (by norm_num)
theorem B1948995 : Blo 1947435 1948995 := bstep (se 1 (by rfl) ⟨1461746, by rfl⟩ : syracuseStep 1948995 = 2923493) B2923493
theorem B8325125 : Blo 1947435 8325125 := bbase (se 4 (by rfl) ⟨780480, by rfl⟩ : syracuseStep 8325125 = 1560961) (by norm_num)
theorem B5550083 : Blo 1947435 5550083 := bstep (se 1 (by rfl) ⟨4162562, by rfl⟩ : syracuseStep 5550083 = 8325125) B8325125
theorem B3700055 : Blo 1947435 3700055 := bstep (se 1 (by rfl) ⟨2775041, by rfl⟩ : syracuseStep 3700055 = 5550083) B5550083
theorem B2466703 : Blo 1947435 2466703 := bstep (se 1 (by rfl) ⟨1850027, by rfl⟩ : syracuseStep 2466703 = 3700055) B3700055
theorem B3288937 : Blo 1947435 3288937 := bstep (se 2 (by rfl) ⟨1233351, by rfl⟩ : syracuseStep 3288937 = 2466703) B2466703
theorem B4385249 : Blo 1947435 4385249 := bstep (se 2 (by rfl) ⟨1644468, by rfl⟩ : syracuseStep 4385249 = 3288937) B3288937
theorem B2923499 : Blo 1947435 2923499 := bstep (se 1 (by rfl) ⟨2192624, by rfl⟩ : syracuseStep 2923499 = 4385249) B4385249
theorem B1948999 : Blo 1947435 1948999 := bstep (se 1 (by rfl) ⟨1461749, by rfl⟩ : syracuseStep 1948999 = 2923499) B2923499
theorem B2192629 : Blo 1947435 2192629 := bbase (se 5 (by rfl) ⟨102779, by rfl⟩ : syracuseStep 2192629 = 205559) (by norm_num)
theorem B2923505 : Blo 1947435 2923505 := bstep (se 2 (by rfl) ⟨1096314, by rfl⟩ : syracuseStep 2923505 = 2192629) B2192629
theorem B1949003 : Blo 1947435 1949003 := bstep (se 1 (by rfl) ⟨1461752, by rfl⟩ : syracuseStep 1949003 = 2923505) B2923505
theorem B2466713 : Blo 1947435 2466713 := bbase (se 2 (by rfl) ⟨925017, by rfl⟩ : syracuseStep 2466713 = 1850035) (by norm_num)
theorem B6577901 : Blo 1947435 6577901 := bstep (se 3 (by rfl) ⟨1233356, by rfl⟩ : syracuseStep 6577901 = 2466713) B2466713
theorem B4385267 : Blo 1947435 4385267 := bstep (se 1 (by rfl) ⟨3288950, by rfl⟩ : syracuseStep 4385267 = 6577901) B6577901
theorem B2923511 : Blo 1947435 2923511 := bstep (se 1 (by rfl) ⟨2192633, by rfl⟩ : syracuseStep 2923511 = 4385267) B4385267
theorem B1949007 : Blo 1947435 1949007 := bstep (se 1 (by rfl) ⟨1461755, by rfl⟩ : syracuseStep 1949007 = 2923511) B2923511
theorem B2923517 : Blo 1947435 2923517 := bbase (se 3 (by rfl) ⟨548159, by rfl⟩ : syracuseStep 2923517 = 1096319) (by norm_num)
theorem B1949011 : Blo 1947435 1949011 := bstep (se 1 (by rfl) ⟨1461758, by rfl⟩ : syracuseStep 1949011 = 2923517) B2923517
theorem B4385285 : Blo 1947435 4385285 := bbase (se 4 (by rfl) ⟨411120, by rfl⟩ : syracuseStep 4385285 = 822241) (by norm_num)
theorem B2923523 : Blo 1947435 2923523 := bstep (se 1 (by rfl) ⟨2192642, by rfl⟩ : syracuseStep 2923523 = 4385285) B4385285
theorem B1949015 : Blo 1947435 1949015 := bstep (se 1 (by rfl) ⟨1461761, by rfl⟩ : syracuseStep 1949015 = 2923523) B2923523
theorem B3700093 : Blo 1947435 3700093 := bbase (se 3 (by rfl) ⟨693767, by rfl⟩ : syracuseStep 3700093 = 1387535) (by norm_num)
theorem B4933457 : Blo 1947435 4933457 := bstep (se 2 (by rfl) ⟨1850046, by rfl⟩ : syracuseStep 4933457 = 3700093) B3700093
theorem B3288971 : Blo 1947435 3288971 := bstep (se 1 (by rfl) ⟨2466728, by rfl⟩ : syracuseStep 3288971 = 4933457) B4933457
theorem B2192647 : Blo 1947435 2192647 := bstep (se 1 (by rfl) ⟨1644485, by rfl⟩ : syracuseStep 2192647 = 3288971) B3288971
theorem B2923529 : Blo 1947435 2923529 := bstep (se 2 (by rfl) ⟨1096323, by rfl⟩ : syracuseStep 2923529 = 2192647) B2192647
theorem B1949019 : Blo 1947435 1949019 := bstep (se 1 (by rfl) ⟨1461764, by rfl⟩ : syracuseStep 1949019 = 2923529) B2923529
theorem B9866933 : Blo 1947435 9866933 := bbase (se 5 (by rfl) ⟨462512, by rfl⟩ : syracuseStep 9866933 = 925025) (by norm_num)
theorem B6577955 : Blo 1947435 6577955 := bstep (se 1 (by rfl) ⟨4933466, by rfl⟩ : syracuseStep 6577955 = 9866933) B9866933
theorem B4385303 : Blo 1947435 4385303 := bstep (se 1 (by rfl) ⟨3288977, by rfl⟩ : syracuseStep 4385303 = 6577955) B6577955
theorem B2923535 : Blo 1947435 2923535 := bstep (se 1 (by rfl) ⟨2192651, by rfl⟩ : syracuseStep 2923535 = 4385303) B4385303
theorem B1949023 : Blo 1947435 1949023 := bstep (se 1 (by rfl) ⟨1461767, by rfl⟩ : syracuseStep 1949023 = 2923535) B2923535
theorem B2923541 : Blo 1947435 2923541 := bbase (se 6 (by rfl) ⟨68520, by rfl⟩ : syracuseStep 2923541 = 137041) (by norm_num)
theorem B1949027 : Blo 1947435 1949027 := bstep (se 1 (by rfl) ⟨1461770, by rfl⟩ : syracuseStep 1949027 = 2923541) B2923541
theorem B4746853 : Blo 1947435 4746853 := bbase (se 4 (by rfl) ⟨445017, by rfl⟩ : syracuseStep 4746853 = 890035) (by norm_num)
theorem B6329137 : Blo 1947435 6329137 := bstep (se 2 (by rfl) ⟨2373426, by rfl⟩ : syracuseStep 6329137 = 4746853) B4746853
theorem B8438849 : Blo 1947435 8438849 := bstep (se 2 (by rfl) ⟨3164568, by rfl⟩ : syracuseStep 8438849 = 6329137) B6329137
theorem B5625899 : Blo 1947435 5625899 := bstep (se 1 (by rfl) ⟨4219424, by rfl⟩ : syracuseStep 5625899 = 8438849) B8438849
theorem B3750599 : Blo 1947435 3750599 := bstep (se 1 (by rfl) ⟨2812949, by rfl⟩ : syracuseStep 3750599 = 5625899) B5625899
theorem B2500399 : Blo 1947435 2500399 := bstep (se 1 (by rfl) ⟨1875299, by rfl⟩ : syracuseStep 2500399 = 3750599) B3750599
theorem B13335461 : Blo 1947435 13335461 := bstep (se 4 (by rfl) ⟨1250199, by rfl⟩ : syracuseStep 13335461 = 2500399) B2500399
theorem B8890307 : Blo 1947435 8890307 := bstep (se 1 (by rfl) ⟨6667730, by rfl⟩ : syracuseStep 8890307 = 13335461) B13335461
theorem B5926871 : Blo 1947435 5926871 := bstep (se 1 (by rfl) ⟨4445153, by rfl⟩ : syracuseStep 5926871 = 8890307) B8890307
theorem B15804989 : Blo 1947435 15804989 := bstep (se 3 (by rfl) ⟨2963435, by rfl⟩ : syracuseStep 15804989 = 5926871) B5926871
theorem B10536659 : Blo 1947435 10536659 := bstep (se 1 (by rfl) ⟨7902494, by rfl⟩ : syracuseStep 10536659 = 15804989) B15804989
theorem B7024439 : Blo 1947435 7024439 := bstep (se 1 (by rfl) ⟨5268329, by rfl⟩ : syracuseStep 7024439 = 10536659) B10536659
theorem B18731837 : Blo 1947435 18731837 := bstep (se 3 (by rfl) ⟨3512219, by rfl⟩ : syracuseStep 18731837 = 7024439) B7024439
theorem B12487891 : Blo 1947435 12487891 := bstep (se 1 (by rfl) ⟨9365918, by rfl⟩ : syracuseStep 12487891 = 18731837) B18731837
theorem B16650521 : Blo 1947435 16650521 := bstep (se 2 (by rfl) ⟨6243945, by rfl⟩ : syracuseStep 16650521 = 12487891) B12487891
theorem B11100347 : Blo 1947435 11100347 := bstep (se 1 (by rfl) ⟨8325260, by rfl⟩ : syracuseStep 11100347 = 16650521) B16650521
theorem B7400231 : Blo 1947435 7400231 := bstep (se 1 (by rfl) ⟨5550173, by rfl⟩ : syracuseStep 7400231 = 11100347) B11100347
theorem B4933487 : Blo 1947435 4933487 := bstep (se 1 (by rfl) ⟨3700115, by rfl⟩ : syracuseStep 4933487 = 7400231) B7400231
theorem B3288991 : Blo 1947435 3288991 := bstep (se 1 (by rfl) ⟨2466743, by rfl⟩ : syracuseStep 3288991 = 4933487) B4933487
theorem B4385321 : Blo 1947435 4385321 := bstep (se 2 (by rfl) ⟨1644495, by rfl⟩ : syracuseStep 4385321 = 3288991) B3288991
theorem B2923547 : Blo 1947435 2923547 := bstep (se 1 (by rfl) ⟨2192660, by rfl⟩ : syracuseStep 2923547 = 4385321) B4385321
theorem B1949031 : Blo 1947435 1949031 := bstep (se 1 (by rfl) ⟨1461773, by rfl⟩ : syracuseStep 1949031 = 2923547) B2923547
theorem B2192665 : Blo 1947435 2192665 := bbase (se 2 (by rfl) ⟨822249, by rfl⟩ : syracuseStep 2192665 = 1644499) (by norm_num)
theorem B2923553 : Blo 1947435 2923553 := bstep (se 2 (by rfl) ⟨1096332, by rfl⟩ : syracuseStep 2923553 = 2192665) B2192665
theorem B1949035 : Blo 1947435 1949035 := bstep (se 1 (by rfl) ⟨1461776, by rfl⟩ : syracuseStep 1949035 = 2923553) B2923553
theorem B7400261 : Blo 1947435 7400261 := bbase (se 4 (by rfl) ⟨693774, by rfl⟩ : syracuseStep 7400261 = 1387549) (by norm_num)
theorem B4933507 : Blo 1947435 4933507 := bstep (se 1 (by rfl) ⟨3700130, by rfl⟩ : syracuseStep 4933507 = 7400261) B7400261
theorem B6578009 : Blo 1947435 6578009 := bstep (se 2 (by rfl) ⟨2466753, by rfl⟩ : syracuseStep 6578009 = 4933507) B4933507
theorem B4385339 : Blo 1947435 4385339 := bstep (se 1 (by rfl) ⟨3289004, by rfl⟩ : syracuseStep 4385339 = 6578009) B6578009
theorem B2923559 : Blo 1947435 2923559 := bstep (se 1 (by rfl) ⟨2192669, by rfl⟩ : syracuseStep 2923559 = 4385339) B4385339
theorem B1949039 : Blo 1947435 1949039 := bstep (se 1 (by rfl) ⟨1461779, by rfl⟩ : syracuseStep 1949039 = 2923559) B2923559
theorem B2923565 : Blo 1947435 2923565 := bbase (se 3 (by rfl) ⟨548168, by rfl⟩ : syracuseStep 2923565 = 1096337) (by norm_num)
theorem B1949043 : Blo 1947435 1949043 := bstep (se 1 (by rfl) ⟨1461782, by rfl⟩ : syracuseStep 1949043 = 2923565) B2923565
theorem B4385357 : Blo 1947435 4385357 := bbase (se 3 (by rfl) ⟨822254, by rfl⟩ : syracuseStep 4385357 = 1644509) (by norm_num)
theorem B2923571 : Blo 1947435 2923571 := bstep (se 1 (by rfl) ⟨2192678, by rfl⟩ : syracuseStep 2923571 = 4385357) B4385357
theorem B1949047 : Blo 1947435 1949047 := bstep (se 1 (by rfl) ⟨1461785, by rfl⟩ : syracuseStep 1949047 = 2923571) B2923571
theorem B2466769 : Blo 1947435 2466769 := bbase (se 2 (by rfl) ⟨925038, by rfl⟩ : syracuseStep 2466769 = 1850077) (by norm_num)
theorem B3289025 : Blo 1947435 3289025 := bstep (se 2 (by rfl) ⟨1233384, by rfl⟩ : syracuseStep 3289025 = 2466769) B2466769
theorem B2192683 : Blo 1947435 2192683 := bstep (se 1 (by rfl) ⟨1644512, by rfl⟩ : syracuseStep 2192683 = 3289025) B3289025
theorem B2923577 : Blo 1947435 2923577 := bstep (se 2 (by rfl) ⟨1096341, by rfl⟩ : syracuseStep 2923577 = 2192683) B2192683
theorem B1949051 : Blo 1947435 1949051 := bstep (se 1 (by rfl) ⟨1461788, by rfl⟩ : syracuseStep 1949051 = 2923577) B2923577
theorem B5000861 : Blo 1947435 5000861 := bbase (se 3 (by rfl) ⟨937661, by rfl⟩ : syracuseStep 5000861 = 1875323) (by norm_num)
theorem B3333907 : Blo 1947435 3333907 := bstep (se 1 (by rfl) ⟨2500430, by rfl⟩ : syracuseStep 3333907 = 5000861) B5000861
theorem B4445209 : Blo 1947435 4445209 := bstep (se 2 (by rfl) ⟨1666953, by rfl⟩ : syracuseStep 4445209 = 3333907) B3333907
theorem B5926945 : Blo 1947435 5926945 := bstep (se 2 (by rfl) ⟨2222604, by rfl⟩ : syracuseStep 5926945 = 4445209) B4445209
theorem B7902593 : Blo 1947435 7902593 := bstep (se 2 (by rfl) ⟨2963472, by rfl⟩ : syracuseStep 7902593 = 5926945) B5926945
theorem B5268395 : Blo 1947435 5268395 := bstep (se 1 (by rfl) ⟨3951296, by rfl⟩ : syracuseStep 5268395 = 7902593) B7902593
theorem B3512263 : Blo 1947435 3512263 := bstep (se 1 (by rfl) ⟨2634197, by rfl⟩ : syracuseStep 3512263 = 5268395) B5268395
theorem B4683017 : Blo 1947435 4683017 := bstep (se 2 (by rfl) ⟨1756131, by rfl⟩ : syracuseStep 4683017 = 3512263) B3512263
theorem B3122011 : Blo 1947435 3122011 := bstep (se 1 (by rfl) ⟨2341508, by rfl⟩ : syracuseStep 3122011 = 4683017) B4683017
theorem B4162681 : Blo 1947435 4162681 := bstep (se 2 (by rfl) ⟨1561005, by rfl⟩ : syracuseStep 4162681 = 3122011) B3122011
theorem B22200965 : Blo 1947435 22200965 := bstep (se 4 (by rfl) ⟨2081340, by rfl⟩ : syracuseStep 22200965 = 4162681) B4162681
theorem B14800643 : Blo 1947435 14800643 := bstep (se 1 (by rfl) ⟨11100482, by rfl⟩ : syracuseStep 14800643 = 22200965) B22200965
theorem B9867095 : Blo 1947435 9867095 := bstep (se 1 (by rfl) ⟨7400321, by rfl⟩ : syracuseStep 9867095 = 14800643) B14800643
theorem B6578063 : Blo 1947435 6578063 := bstep (se 1 (by rfl) ⟨4933547, by rfl⟩ : syracuseStep 6578063 = 9867095) B9867095
theorem B4385375 : Blo 1947435 4385375 := bstep (se 1 (by rfl) ⟨3289031, by rfl⟩ : syracuseStep 4385375 = 6578063) B6578063
theorem B2923583 : Blo 1947435 2923583 := bstep (se 1 (by rfl) ⟨2192687, by rfl⟩ : syracuseStep 2923583 = 4385375) B4385375
theorem B1949055 : Blo 1947435 1949055 := bstep (se 1 (by rfl) ⟨1461791, by rfl⟩ : syracuseStep 1949055 = 2923583) B2923583
theorem B2923589 : Blo 1947435 2923589 := bbase (se 4 (by rfl) ⟨274086, by rfl⟩ : syracuseStep 2923589 = 548173) (by norm_num)
theorem B1949059 : Blo 1947435 1949059 := bstep (se 1 (by rfl) ⟨1461794, by rfl⟩ : syracuseStep 1949059 = 2923589) B2923589
theorem B3289045 : Blo 1947435 3289045 := bbase (se 7 (by rfl) ⟨38543, by rfl⟩ : syracuseStep 3289045 = 77087) (by norm_num)
theorem B4385393 : Blo 1947435 4385393 := bstep (se 2 (by rfl) ⟨1644522, by rfl⟩ : syracuseStep 4385393 = 3289045) B3289045
theorem B2923595 : Blo 1947435 2923595 := bstep (se 1 (by rfl) ⟨2192696, by rfl⟩ : syracuseStep 2923595 = 4385393) B4385393
theorem B1949063 : Blo 1947435 1949063 := bstep (se 1 (by rfl) ⟨1461797, by rfl⟩ : syracuseStep 1949063 = 2923595) B2923595
theorem B2192701 : Blo 1947435 2192701 := bbase (se 3 (by rfl) ⟨411131, by rfl⟩ : syracuseStep 2192701 = 822263) (by norm_num)
theorem B2923601 : Blo 1947435 2923601 := bstep (se 2 (by rfl) ⟨1096350, by rfl⟩ : syracuseStep 2923601 = 2192701) B2192701
theorem B1949067 : Blo 1947435 1949067 := bstep (se 1 (by rfl) ⟨1461800, by rfl⟩ : syracuseStep 1949067 = 2923601) B2923601
theorem B6578117 : Blo 1947435 6578117 := bbase (se 4 (by rfl) ⟨616698, by rfl⟩ : syracuseStep 6578117 = 1233397) (by norm_num)
theorem B4385411 : Blo 1947435 4385411 := bstep (se 1 (by rfl) ⟨3289058, by rfl⟩ : syracuseStep 4385411 = 6578117) B6578117
theorem B2923607 : Blo 1947435 2923607 := bstep (se 1 (by rfl) ⟨2192705, by rfl⟩ : syracuseStep 2923607 = 4385411) B4385411
theorem B1949071 : Blo 1947435 1949071 := bstep (se 1 (by rfl) ⟨1461803, by rfl⟩ : syracuseStep 1949071 = 2923607) B2923607
theorem B2923613 : Blo 1947435 2923613 := bbase (se 3 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 2923613 = 1096355) (by norm_num)
theorem B1949075 : Blo 1947435 1949075 := bstep (se 1 (by rfl) ⟨1461806, by rfl⟩ : syracuseStep 1949075 = 2923613) B2923613
theorem B4385429 : Blo 1947435 4385429 := bbase (se 6 (by rfl) ⟨102783, by rfl⟩ : syracuseStep 4385429 = 205567) (by norm_num)
theorem B2923619 : Blo 1947435 2923619 := bstep (se 1 (by rfl) ⟨2192714, by rfl⟩ : syracuseStep 2923619 = 4385429) B4385429
theorem B1949079 : Blo 1947435 1949079 := bstep (se 1 (by rfl) ⟨1461809, by rfl⟩ : syracuseStep 1949079 = 2923619) B2923619
theorem B8010533 : Blo 1947435 8010533 := bbase (se 4 (by rfl) ⟨750987, by rfl⟩ : syracuseStep 8010533 = 1501975) (by norm_num)
theorem B21361421 : Blo 1947435 21361421 := bstep (se 3 (by rfl) ⟨4005266, by rfl⟩ : syracuseStep 21361421 = 8010533) B8010533
theorem B14240947 : Blo 1947435 14240947 := bstep (se 1 (by rfl) ⟨10680710, by rfl⟩ : syracuseStep 14240947 = 21361421) B21361421
theorem B18987929 : Blo 1947435 18987929 := bstep (se 2 (by rfl) ⟨7120473, by rfl⟩ : syracuseStep 18987929 = 14240947) B14240947
theorem B12658619 : Blo 1947435 12658619 := bstep (se 1 (by rfl) ⟨9493964, by rfl⟩ : syracuseStep 12658619 = 18987929) B18987929
theorem B8439079 : Blo 1947435 8439079 := bstep (se 1 (by rfl) ⟨6329309, by rfl⟩ : syracuseStep 8439079 = 12658619) B12658619
theorem B11252105 : Blo 1947435 11252105 := bstep (se 2 (by rfl) ⟨4219539, by rfl⟩ : syracuseStep 11252105 = 8439079) B8439079
theorem B7501403 : Blo 1947435 7501403 := bstep (se 1 (by rfl) ⟨5626052, by rfl⟩ : syracuseStep 7501403 = 11252105) B11252105
theorem B5000935 : Blo 1947435 5000935 := bstep (se 1 (by rfl) ⟨3750701, by rfl⟩ : syracuseStep 5000935 = 7501403) B7501403
theorem B6667913 : Blo 1947435 6667913 := bstep (se 2 (by rfl) ⟨2500467, by rfl⟩ : syracuseStep 6667913 = 5000935) B5000935
theorem B4445275 : Blo 1947435 4445275 := bstep (se 1 (by rfl) ⟨3333956, by rfl⟩ : syracuseStep 4445275 = 6667913) B6667913
theorem B5927033 : Blo 1947435 5927033 := bstep (se 2 (by rfl) ⟨2222637, by rfl⟩ : syracuseStep 5927033 = 4445275) B4445275
theorem B3951355 : Blo 1947435 3951355 := bstep (se 1 (by rfl) ⟨2963516, by rfl⟩ : syracuseStep 3951355 = 5927033) B5927033
theorem B5268473 : Blo 1947435 5268473 := bstep (se 2 (by rfl) ⟨1975677, by rfl⟩ : syracuseStep 5268473 = 3951355) B3951355
theorem B3512315 : Blo 1947435 3512315 := bstep (se 1 (by rfl) ⟨2634236, by rfl⟩ : syracuseStep 3512315 = 5268473) B5268473
theorem B2341543 : Blo 1947435 2341543 := bstep (se 1 (by rfl) ⟨1756157, by rfl⟩ : syracuseStep 2341543 = 3512315) B3512315
theorem B3122057 : Blo 1947435 3122057 := bstep (se 2 (by rfl) ⟨1170771, by rfl⟩ : syracuseStep 3122057 = 2341543) B2341543
theorem B2081371 : Blo 1947435 2081371 := bstep (se 1 (by rfl) ⟨1561028, by rfl⟩ : syracuseStep 2081371 = 3122057) B3122057
theorem B2775161 : Blo 1947435 2775161 := bstep (se 2 (by rfl) ⟨1040685, by rfl⟩ : syracuseStep 2775161 = 2081371) B2081371
theorem B7400429 : Blo 1947435 7400429 := bstep (se 3 (by rfl) ⟨1387580, by rfl⟩ : syracuseStep 7400429 = 2775161) B2775161
theorem B4933619 : Blo 1947435 4933619 := bstep (se 1 (by rfl) ⟨3700214, by rfl⟩ : syracuseStep 4933619 = 7400429) B7400429
theorem B3289079 : Blo 1947435 3289079 := bstep (se 1 (by rfl) ⟨2466809, by rfl⟩ : syracuseStep 3289079 = 4933619) B4933619
theorem B2192719 : Blo 1947435 2192719 := bstep (se 1 (by rfl) ⟨1644539, by rfl⟩ : syracuseStep 2192719 = 3289079) B3289079
theorem B2923625 : Blo 1947435 2923625 := bstep (se 2 (by rfl) ⟨1096359, by rfl⟩ : syracuseStep 2923625 = 2192719) B2192719
theorem B1949083 : Blo 1947435 1949083 := bstep (se 1 (by rfl) ⟨1461812, by rfl⟩ : syracuseStep 1949083 = 2923625) B2923625
theorem B2109773 : Blo 1947435 2109773 := bbase (se 3 (by rfl) ⟨395582, by rfl⟩ : syracuseStep 2109773 = 791165) (by norm_num)
theorem B5626061 : Blo 1947435 5626061 := bstep (se 3 (by rfl) ⟨1054886, by rfl⟩ : syracuseStep 5626061 = 2109773) B2109773
theorem B3750707 : Blo 1947435 3750707 := bstep (se 1 (by rfl) ⟨2813030, by rfl⟩ : syracuseStep 3750707 = 5626061) B5626061
theorem B2500471 : Blo 1947435 2500471 := bstep (se 1 (by rfl) ⟨1875353, by rfl⟩ : syracuseStep 2500471 = 3750707) B3750707
theorem B3333961 : Blo 1947435 3333961 := bstep (se 2 (by rfl) ⟨1250235, by rfl⟩ : syracuseStep 3333961 = 2500471) B2500471
theorem B4445281 : Blo 1947435 4445281 := bstep (se 2 (by rfl) ⟨1666980, by rfl⟩ : syracuseStep 4445281 = 3333961) B3333961
theorem B5927041 : Blo 1947435 5927041 := bstep (se 2 (by rfl) ⟨2222640, by rfl⟩ : syracuseStep 5927041 = 4445281) B4445281
theorem B7902721 : Blo 1947435 7902721 := bstep (se 2 (by rfl) ⟨2963520, by rfl⟩ : syracuseStep 7902721 = 5927041) B5927041
theorem B10536961 : Blo 1947435 10536961 := bstep (se 2 (by rfl) ⟨3951360, by rfl⟩ : syracuseStep 10536961 = 7902721) B7902721
theorem B14049281 : Blo 1947435 14049281 := bstep (se 2 (by rfl) ⟨5268480, by rfl⟩ : syracuseStep 14049281 = 10536961) B10536961
theorem B9366187 : Blo 1947435 9366187 := bstep (se 1 (by rfl) ⟨7024640, by rfl⟩ : syracuseStep 9366187 = 14049281) B14049281
theorem B12488249 : Blo 1947435 12488249 := bstep (se 2 (by rfl) ⟨4683093, by rfl⟩ : syracuseStep 12488249 = 9366187) B9366187
theorem B8325499 : Blo 1947435 8325499 := bstep (se 1 (by rfl) ⟨6244124, by rfl⟩ : syracuseStep 8325499 = 12488249) B12488249
theorem B11100665 : Blo 1947435 11100665 := bstep (se 2 (by rfl) ⟨4162749, by rfl⟩ : syracuseStep 11100665 = 8325499) B8325499
theorem B7400443 : Blo 1947435 7400443 := bstep (se 1 (by rfl) ⟨5550332, by rfl⟩ : syracuseStep 7400443 = 11100665) B11100665
theorem B9867257 : Blo 1947435 9867257 := bstep (se 2 (by rfl) ⟨3700221, by rfl⟩ : syracuseStep 9867257 = 7400443) B7400443
theorem B6578171 : Blo 1947435 6578171 := bstep (se 1 (by rfl) ⟨4933628, by rfl⟩ : syracuseStep 6578171 = 9867257) B9867257
theorem B4385447 : Blo 1947435 4385447 := bstep (se 1 (by rfl) ⟨3289085, by rfl⟩ : syracuseStep 4385447 = 6578171) B6578171
theorem B2923631 : Blo 1947435 2923631 := bstep (se 1 (by rfl) ⟨2192723, by rfl⟩ : syracuseStep 2923631 = 4385447) B4385447
theorem B1949087 : Blo 1947435 1949087 := bstep (se 1 (by rfl) ⟨1461815, by rfl⟩ : syracuseStep 1949087 = 2923631) B2923631
theorem B2923637 : Blo 1947435 2923637 := bbase (se 5 (by rfl) ⟨137045, by rfl⟩ : syracuseStep 2923637 = 274091) (by norm_num)
theorem B1949091 : Blo 1947435 1949091 := bstep (se 1 (by rfl) ⟨1461818, by rfl⟩ : syracuseStep 1949091 = 2923637) B2923637
theorem B3700237 : Blo 1947435 3700237 := bbase (se 3 (by rfl) ⟨693794, by rfl⟩ : syracuseStep 3700237 = 1387589) (by norm_num)
theorem B4933649 : Blo 1947435 4933649 := bstep (se 2 (by rfl) ⟨1850118, by rfl⟩ : syracuseStep 4933649 = 3700237) B3700237
theorem B3289099 : Blo 1947435 3289099 := bstep (se 1 (by rfl) ⟨2466824, by rfl⟩ : syracuseStep 3289099 = 4933649) B4933649
theorem B4385465 : Blo 1947435 4385465 := bstep (se 2 (by rfl) ⟨1644549, by rfl⟩ : syracuseStep 4385465 = 3289099) B3289099
theorem B2923643 : Blo 1947435 2923643 := bstep (se 1 (by rfl) ⟨2192732, by rfl⟩ : syracuseStep 2923643 = 4385465) B4385465
theorem B1949095 : Blo 1947435 1949095 := bstep (se 1 (by rfl) ⟨1461821, by rfl⟩ : syracuseStep 1949095 = 2923643) B2923643
theorem B2192737 : Blo 1947435 2192737 := bbase (se 2 (by rfl) ⟨822276, by rfl⟩ : syracuseStep 2192737 = 1644553) (by norm_num)
theorem B2923649 : Blo 1947435 2923649 := bstep (se 2 (by rfl) ⟨1096368, by rfl⟩ : syracuseStep 2923649 = 2192737) B2192737
theorem B1949099 : Blo 1947435 1949099 := bstep (se 1 (by rfl) ⟨1461824, by rfl⟩ : syracuseStep 1949099 = 2923649) B2923649
theorem B4933669 : Blo 1947435 4933669 := bbase (se 4 (by rfl) ⟨462531, by rfl⟩ : syracuseStep 4933669 = 925063) (by norm_num)
theorem B6578225 : Blo 1947435 6578225 := bstep (se 2 (by rfl) ⟨2466834, by rfl⟩ : syracuseStep 6578225 = 4933669) B4933669
theorem B4385483 : Blo 1947435 4385483 := bstep (se 1 (by rfl) ⟨3289112, by rfl⟩ : syracuseStep 4385483 = 6578225) B6578225
theorem B2923655 : Blo 1947435 2923655 := bstep (se 1 (by rfl) ⟨2192741, by rfl⟩ : syracuseStep 2923655 = 4385483) B4385483
theorem B1949103 : Blo 1947435 1949103 := bstep (se 1 (by rfl) ⟨1461827, by rfl⟩ : syracuseStep 1949103 = 2923655) B2923655
theorem B2923661 : Blo 1947435 2923661 := bbase (se 3 (by rfl) ⟨548186, by rfl⟩ : syracuseStep 2923661 = 1096373) (by norm_num)
theorem B1949107 : Blo 1947435 1949107 := bstep (se 1 (by rfl) ⟨1461830, by rfl⟩ : syracuseStep 1949107 = 2923661) B2923661
theorem B4385501 : Blo 1947435 4385501 := bbase (se 3 (by rfl) ⟨822281, by rfl⟩ : syracuseStep 4385501 = 1644563) (by norm_num)
theorem B2923667 : Blo 1947435 2923667 := bstep (se 1 (by rfl) ⟨2192750, by rfl⟩ : syracuseStep 2923667 = 4385501) B4385501
theorem B1949111 : Blo 1947435 1949111 := bstep (se 1 (by rfl) ⟨1461833, by rfl⟩ : syracuseStep 1949111 = 2923667) B2923667
theorem B3289133 : Blo 1947435 3289133 := bbase (se 3 (by rfl) ⟨616712, by rfl⟩ : syracuseStep 3289133 = 1233425) (by norm_num)
theorem B2192755 : Blo 1947435 2192755 := bstep (se 1 (by rfl) ⟨1644566, by rfl⟩ : syracuseStep 2192755 = 3289133) B3289133
theorem B2923673 : Blo 1947435 2923673 := bstep (se 2 (by rfl) ⟨1096377, by rfl⟩ : syracuseStep 2923673 = 2192755) B2192755
theorem B1949115 : Blo 1947435 1949115 := bstep (se 1 (by rfl) ⟨1461836, by rfl⟩ : syracuseStep 1949115 = 2923673) B2923673
theorem B2222677 : Blo 1947435 2222677 := bbase (se 8 (by rfl) ⟨13023, by rfl⟩ : syracuseStep 2222677 = 26047) (by norm_num)
theorem B2963569 : Blo 1947435 2963569 := bstep (se 2 (by rfl) ⟨1111338, by rfl⟩ : syracuseStep 2963569 = 2222677) B2222677
theorem B3951425 : Blo 1947435 3951425 := bstep (se 2 (by rfl) ⟨1481784, by rfl⟩ : syracuseStep 3951425 = 2963569) B2963569
theorem B10537133 : Blo 1947435 10537133 := bstep (se 3 (by rfl) ⟨1975712, by rfl⟩ : syracuseStep 10537133 = 3951425) B3951425
theorem B28099021 : Blo 1947435 28099021 := bstep (se 3 (by rfl) ⟨5268566, by rfl⟩ : syracuseStep 28099021 = 10537133) B10537133
theorem B37465361 : Blo 1947435 37465361 := bstep (se 2 (by rfl) ⟨14049510, by rfl⟩ : syracuseStep 37465361 = 28099021) B28099021
theorem B24976907 : Blo 1947435 24976907 := bstep (se 1 (by rfl) ⟨18732680, by rfl⟩ : syracuseStep 24976907 = 37465361) B37465361
theorem B16651271 : Blo 1947435 16651271 := bstep (se 1 (by rfl) ⟨12488453, by rfl⟩ : syracuseStep 16651271 = 24976907) B24976907
theorem B11100847 : Blo 1947435 11100847 := bstep (se 1 (by rfl) ⟨8325635, by rfl⟩ : syracuseStep 11100847 = 16651271) B16651271
theorem B14801129 : Blo 1947435 14801129 := bstep (se 2 (by rfl) ⟨5550423, by rfl⟩ : syracuseStep 14801129 = 11100847) B11100847
theorem B9867419 : Blo 1947435 9867419 := bstep (se 1 (by rfl) ⟨7400564, by rfl⟩ : syracuseStep 9867419 = 14801129) B14801129
theorem B6578279 : Blo 1947435 6578279 := bstep (se 1 (by rfl) ⟨4933709, by rfl⟩ : syracuseStep 6578279 = 9867419) B9867419
theorem B4385519 : Blo 1947435 4385519 := bstep (se 1 (by rfl) ⟨3289139, by rfl⟩ : syracuseStep 4385519 = 6578279) B6578279
theorem B2923679 : Blo 1947435 2923679 := bstep (se 1 (by rfl) ⟨2192759, by rfl⟩ : syracuseStep 2923679 = 4385519) B4385519
theorem B1949119 : Blo 1947435 1949119 := bstep (se 1 (by rfl) ⟨1461839, by rfl⟩ : syracuseStep 1949119 = 2923679) B2923679
theorem B2923685 : Blo 1947435 2923685 := bbase (se 4 (by rfl) ⟨274095, by rfl⟩ : syracuseStep 2923685 = 548191) (by norm_num)
theorem B1949123 : Blo 1947435 1949123 := bstep (se 1 (by rfl) ⟨1461842, by rfl⟩ : syracuseStep 1949123 = 2923685) B2923685
theorem B2466865 : Blo 1947435 2466865 := bbase (se 2 (by rfl) ⟨925074, by rfl⟩ : syracuseStep 2466865 = 1850149) (by norm_num)
theorem B3289153 : Blo 1947435 3289153 := bstep (se 2 (by rfl) ⟨1233432, by rfl⟩ : syracuseStep 3289153 = 2466865) B2466865
theorem B4385537 : Blo 1947435 4385537 := bstep (se 2 (by rfl) ⟨1644576, by rfl⟩ : syracuseStep 4385537 = 3289153) B3289153
theorem B2923691 : Blo 1947435 2923691 := bstep (se 1 (by rfl) ⟨2192768, by rfl⟩ : syracuseStep 2923691 = 4385537) B4385537
theorem B1949127 : Blo 1947435 1949127 := bstep (se 1 (by rfl) ⟨1461845, by rfl⟩ : syracuseStep 1949127 = 2923691) B2923691
theorem B2192773 : Blo 1947435 2192773 := bbase (se 4 (by rfl) ⟨205572, by rfl⟩ : syracuseStep 2192773 = 411145) (by norm_num)
theorem B2923697 : Blo 1947435 2923697 := bstep (se 2 (by rfl) ⟨1096386, by rfl⟩ : syracuseStep 2923697 = 2192773) B2192773
theorem B1949131 : Blo 1947435 1949131 := bstep (se 1 (by rfl) ⟨1461848, by rfl⟩ : syracuseStep 1949131 = 2923697) B2923697
theorem B4162853 : Blo 1947435 4162853 := bbase (se 4 (by rfl) ⟨390267, by rfl⟩ : syracuseStep 4162853 = 780535) (by norm_num)
theorem B2775235 : Blo 1947435 2775235 := bstep (se 1 (by rfl) ⟨2081426, by rfl⟩ : syracuseStep 2775235 = 4162853) B4162853
theorem B3700313 : Blo 1947435 3700313 := bstep (se 2 (by rfl) ⟨1387617, by rfl⟩ : syracuseStep 3700313 = 2775235) B2775235
theorem B2466875 : Blo 1947435 2466875 := bstep (se 1 (by rfl) ⟨1850156, by rfl⟩ : syracuseStep 2466875 = 3700313) B3700313
theorem B6578333 : Blo 1947435 6578333 := bstep (se 3 (by rfl) ⟨1233437, by rfl⟩ : syracuseStep 6578333 = 2466875) B2466875
theorem B4385555 : Blo 1947435 4385555 := bstep (se 1 (by rfl) ⟨3289166, by rfl⟩ : syracuseStep 4385555 = 6578333) B6578333
theorem B2923703 : Blo 1947435 2923703 := bstep (se 1 (by rfl) ⟨2192777, by rfl⟩ : syracuseStep 2923703 = 4385555) B4385555
theorem B1949135 : Blo 1947435 1949135 := bstep (se 1 (by rfl) ⟨1461851, by rfl⟩ : syracuseStep 1949135 = 2923703) B2923703
theorem B2923709 : Blo 1947435 2923709 := bbase (se 3 (by rfl) ⟨548195, by rfl⟩ : syracuseStep 2923709 = 1096391) (by norm_num)
theorem B1949139 : Blo 1947435 1949139 := bstep (se 1 (by rfl) ⟨1461854, by rfl⟩ : syracuseStep 1949139 = 2923709) B2923709
theorem B4385573 : Blo 1947435 4385573 := bbase (se 4 (by rfl) ⟨411147, by rfl⟩ : syracuseStep 4385573 = 822295) (by norm_num)
theorem B2923715 : Blo 1947435 2923715 := bstep (se 1 (by rfl) ⟨2192786, by rfl⟩ : syracuseStep 2923715 = 4385573) B4385573
theorem B1949143 : Blo 1947435 1949143 := bstep (se 1 (by rfl) ⟨1461857, by rfl⟩ : syracuseStep 1949143 = 2923715) B2923715
theorem B4933781 : Blo 1947435 4933781 := bbase (se 6 (by rfl) ⟨115635, by rfl⟩ : syracuseStep 4933781 = 231271) (by norm_num)
theorem B3289187 : Blo 1947435 3289187 := bstep (se 1 (by rfl) ⟨2466890, by rfl⟩ : syracuseStep 3289187 = 4933781) B4933781
theorem B2192791 : Blo 1947435 2192791 := bstep (se 1 (by rfl) ⟨1644593, by rfl⟩ : syracuseStep 2192791 = 3289187) B3289187
theorem B2923721 : Blo 1947435 2923721 := bstep (se 2 (by rfl) ⟨1096395, by rfl⟩ : syracuseStep 2923721 = 2192791) B2192791
theorem B1949147 : Blo 1947435 1949147 := bstep (se 1 (by rfl) ⟨1461860, by rfl⟩ : syracuseStep 1949147 = 2923721) B2923721
theorem B3122165 : Blo 1947435 3122165 := bbase (se 5 (by rfl) ⟨146351, by rfl⟩ : syracuseStep 3122165 = 292703) (by norm_num)
theorem B8325773 : Blo 1947435 8325773 := bstep (se 3 (by rfl) ⟨1561082, by rfl⟩ : syracuseStep 8325773 = 3122165) B3122165
theorem B5550515 : Blo 1947435 5550515 := bstep (se 1 (by rfl) ⟨4162886, by rfl⟩ : syracuseStep 5550515 = 8325773) B8325773
theorem B3700343 : Blo 1947435 3700343 := bstep (se 1 (by rfl) ⟨2775257, by rfl⟩ : syracuseStep 3700343 = 5550515) B5550515
theorem B9867581 : Blo 1947435 9867581 := bstep (se 3 (by rfl) ⟨1850171, by rfl⟩ : syracuseStep 9867581 = 3700343) B3700343
theorem B6578387 : Blo 1947435 6578387 := bstep (se 1 (by rfl) ⟨4933790, by rfl⟩ : syracuseStep 6578387 = 9867581) B9867581
theorem B4385591 : Blo 1947435 4385591 := bstep (se 1 (by rfl) ⟨3289193, by rfl⟩ : syracuseStep 4385591 = 6578387) B6578387
theorem B2923727 : Blo 1947435 2923727 := bstep (se 1 (by rfl) ⟨2192795, by rfl⟩ : syracuseStep 2923727 = 4385591) B4385591
theorem B1949151 : Blo 1947435 1949151 := bstep (se 1 (by rfl) ⟨1461863, by rfl⟩ : syracuseStep 1949151 = 2923727) B2923727
theorem B2923733 : Blo 1947435 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B1949155 : Blo 1947435 1949155 := bstep (se 1 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 1949155 = 2923733) B2923733
theorem B2775269 : Blo 1947435 2775269 := bbase (se 4 (by rfl) ⟨260181, by rfl⟩ : syracuseStep 2775269 = 520363) (by norm_num)
theorem B7400717 : Blo 1947435 7400717 := bstep (se 3 (by rfl) ⟨1387634, by rfl⟩ : syracuseStep 7400717 = 2775269) B2775269
theorem B4933811 : Blo 1947435 4933811 := bstep (se 1 (by rfl) ⟨3700358, by rfl⟩ : syracuseStep 4933811 = 7400717) B7400717
theorem B3289207 : Blo 1947435 3289207 := bstep (se 1 (by rfl) ⟨2466905, by rfl⟩ : syracuseStep 3289207 = 4933811) B4933811
theorem B4385609 : Blo 1947435 4385609 := bstep (se 2 (by rfl) ⟨1644603, by rfl⟩ : syracuseStep 4385609 = 3289207) B3289207
theorem B2923739 : Blo 1947435 2923739 := bstep (se 1 (by rfl) ⟨2192804, by rfl⟩ : syracuseStep 2923739 = 4385609) B4385609
theorem B1949159 : Blo 1947435 1949159 := bstep (se 1 (by rfl) ⟨1461869, by rfl⟩ : syracuseStep 1949159 = 2923739) B2923739
theorem B2192809 : Blo 1947435 2192809 := bbase (se 2 (by rfl) ⟨822303, by rfl⟩ : syracuseStep 2192809 = 1644607) (by norm_num)
theorem B2923745 : Blo 1947435 2923745 := bstep (se 2 (by rfl) ⟨1096404, by rfl⟩ : syracuseStep 2923745 = 2192809) B2192809
theorem B1949163 : Blo 1947435 1949163 := bstep (se 1 (by rfl) ⟨1461872, by rfl⟩ : syracuseStep 1949163 = 2923745) B2923745
theorem B2634349 : Blo 1947435 2634349 := bbase (se 3 (by rfl) ⟨493940, by rfl⟩ : syracuseStep 2634349 = 987881) (by norm_num)
theorem B3512465 : Blo 1947435 3512465 := bstep (se 2 (by rfl) ⟨1317174, by rfl⟩ : syracuseStep 3512465 = 2634349) B2634349
theorem B2341643 : Blo 1947435 2341643 := bstep (se 1 (by rfl) ⟨1756232, by rfl⟩ : syracuseStep 2341643 = 3512465) B3512465
theorem B6244381 : Blo 1947435 6244381 := bstep (se 3 (by rfl) ⟨1170821, by rfl⟩ : syracuseStep 6244381 = 2341643) B2341643
theorem B8325841 : Blo 1947435 8325841 := bstep (se 2 (by rfl) ⟨3122190, by rfl⟩ : syracuseStep 8325841 = 6244381) B6244381
theorem B11101121 : Blo 1947435 11101121 := bstep (se 2 (by rfl) ⟨4162920, by rfl⟩ : syracuseStep 11101121 = 8325841) B8325841
theorem B7400747 : Blo 1947435 7400747 := bstep (se 1 (by rfl) ⟨5550560, by rfl⟩ : syracuseStep 7400747 = 11101121) B11101121
theorem B4933831 : Blo 1947435 4933831 := bstep (se 1 (by rfl) ⟨3700373, by rfl⟩ : syracuseStep 4933831 = 7400747) B7400747
theorem B6578441 : Blo 1947435 6578441 := bstep (se 2 (by rfl) ⟨2466915, by rfl⟩ : syracuseStep 6578441 = 4933831) B4933831
theorem B4385627 : Blo 1947435 4385627 := bstep (se 1 (by rfl) ⟨3289220, by rfl⟩ : syracuseStep 4385627 = 6578441) B6578441
theorem B2923751 : Blo 1947435 2923751 := bstep (se 1 (by rfl) ⟨2192813, by rfl⟩ : syracuseStep 2923751 = 4385627) B4385627
theorem B1949167 : Blo 1947435 1949167 := bstep (se 1 (by rfl) ⟨1461875, by rfl⟩ : syracuseStep 1949167 = 2923751) B2923751
theorem B2923757 : Blo 1947435 2923757 := bbase (se 3 (by rfl) ⟨548204, by rfl⟩ : syracuseStep 2923757 = 1096409) (by norm_num)
theorem B1949171 : Blo 1947435 1949171 := bstep (se 1 (by rfl) ⟨1461878, by rfl⟩ : syracuseStep 1949171 = 2923757) B2923757
theorem B4385645 : Blo 1947435 4385645 := bbase (se 3 (by rfl) ⟨822308, by rfl⟩ : syracuseStep 4385645 = 1644617) (by norm_num)
theorem B2923763 : Blo 1947435 2923763 := bstep (se 1 (by rfl) ⟨2192822, by rfl⟩ : syracuseStep 2923763 = 4385645) B4385645
theorem B1949175 : Blo 1947435 1949175 := bstep (se 1 (by rfl) ⟨1461881, by rfl⟩ : syracuseStep 1949175 = 2923763) B2923763
theorem B3700397 : Blo 1947435 3700397 := bbase (se 3 (by rfl) ⟨693824, by rfl⟩ : syracuseStep 3700397 = 1387649) (by norm_num)
theorem B2466931 : Blo 1947435 2466931 := bstep (se 1 (by rfl) ⟨1850198, by rfl⟩ : syracuseStep 2466931 = 3700397) B3700397
theorem B3289241 : Blo 1947435 3289241 := bstep (se 2 (by rfl) ⟨1233465, by rfl⟩ : syracuseStep 3289241 = 2466931) B2466931
theorem B2192827 : Blo 1947435 2192827 := bstep (se 1 (by rfl) ⟨1644620, by rfl⟩ : syracuseStep 2192827 = 3289241) B3289241
theorem B2923769 : Blo 1947435 2923769 := bstep (se 2 (by rfl) ⟨1096413, by rfl⟩ : syracuseStep 2923769 = 2192827) B2192827
theorem B1949179 : Blo 1947435 1949179 := bstep (se 1 (by rfl) ⟨1461884, by rfl⟩ : syracuseStep 1949179 = 2923769) B2923769
theorem B2851549 : Blo 1947435 2851549 := bbase (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) (by norm_num)
theorem B60833045 : Blo 1947435 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B40555363 : Blo 1947435 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B54073817 : Blo 1947435 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B36049211 : Blo 1947435 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B24032807 : Blo 1947435 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B16021871 : Blo 1947435 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B10681247 : Blo 1947435 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B7120831 : Blo 1947435 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B9494441 : Blo 1947435 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B6329627 : Blo 1947435 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B4219751 : Blo 1947435 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B180042709 : Blo 1947435 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B240056945 : Blo 1947435 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B160037963 : Blo 1947435 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B106691975 : Blo 1947435 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B71127983 : Blo 1947435 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B47418655 : Blo 1947435 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B63224873 : Blo 1947435 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B42149915 : Blo 1947435 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B28099943 : Blo 1947435 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B18733295 : Blo 1947435 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B49955453 : Blo 1947435 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B33303635 : Blo 1947435 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B22202423 : Blo 1947435 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B14801615 : Blo 1947435 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B9867743 : Blo 1947435 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B6578495 : Blo 1947435 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B4385663 : Blo 1947435 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B2923775 : Blo 1947435 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B1949183 : Blo 1947435 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B2923781 : Blo 1947435 2923781 := bbase (se 4 (by rfl) ⟨274104, by rfl⟩ : syracuseStep 2923781 = 548209) (by norm_num)
theorem B1949187 : Blo 1947435 1949187 := bstep (se 1 (by rfl) ⟨1461890, by rfl⟩ : syracuseStep 1949187 = 2923781) B2923781
theorem B3289261 : Blo 1947435 3289261 := bbase (se 3 (by rfl) ⟨616736, by rfl⟩ : syracuseStep 3289261 = 1233473) (by norm_num)
theorem B4385681 : Blo 1947435 4385681 := bstep (se 2 (by rfl) ⟨1644630, by rfl⟩ : syracuseStep 4385681 = 3289261) B3289261
theorem B2923787 : Blo 1947435 2923787 := bstep (se 1 (by rfl) ⟨2192840, by rfl⟩ : syracuseStep 2923787 = 4385681) B4385681
theorem B1949191 : Blo 1947435 1949191 := bstep (se 1 (by rfl) ⟨1461893, by rfl⟩ : syracuseStep 1949191 = 2923787) B2923787
theorem B2192845 : Blo 1947435 2192845 := bbase (se 3 (by rfl) ⟨411158, by rfl⟩ : syracuseStep 2192845 = 822317) (by norm_num)
theorem B2923793 : Blo 1947435 2923793 := bstep (se 2 (by rfl) ⟨1096422, by rfl⟩ : syracuseStep 2923793 = 2192845) B2192845
theorem B1949195 : Blo 1947435 1949195 := bstep (se 1 (by rfl) ⟨1461896, by rfl⟩ : syracuseStep 1949195 = 2923793) B2923793
theorem B6578549 : Blo 1947435 6578549 := bbase (se 5 (by rfl) ⟨308369, by rfl⟩ : syracuseStep 6578549 = 616739) (by norm_num)
theorem B4385699 : Blo 1947435 4385699 := bstep (se 1 (by rfl) ⟨3289274, by rfl⟩ : syracuseStep 4385699 = 6578549) B6578549
theorem B2923799 : Blo 1947435 2923799 := bstep (se 1 (by rfl) ⟨2192849, by rfl⟩ : syracuseStep 2923799 = 4385699) B4385699
theorem B1949199 : Blo 1947435 1949199 := bstep (se 1 (by rfl) ⟨1461899, by rfl⟩ : syracuseStep 1949199 = 2923799) B2923799
theorem B2923805 : Blo 1947435 2923805 := bbase (se 3 (by rfl) ⟨548213, by rfl⟩ : syracuseStep 2923805 = 1096427) (by norm_num)
theorem B1949203 : Blo 1947435 1949203 := bstep (se 1 (by rfl) ⟨1461902, by rfl⟩ : syracuseStep 1949203 = 2923805) B2923805
theorem B4385717 : Blo 1947435 4385717 := bbase (se 5 (by rfl) ⟨205580, by rfl⟩ : syracuseStep 4385717 = 411161) (by norm_num)
theorem B2923811 : Blo 1947435 2923811 := bstep (se 1 (by rfl) ⟨2192858, by rfl⟩ : syracuseStep 2923811 = 4385717) B4385717
theorem B1949207 : Blo 1947435 1949207 := bstep (se 1 (by rfl) ⟨1461905, by rfl⟩ : syracuseStep 1949207 = 2923811) B2923811
theorem B3951613 : Blo 1947435 3951613 := bbase (se 3 (by rfl) ⟨740927, by rfl⟩ : syracuseStep 3951613 = 1481855) (by norm_num)
theorem B5268817 : Blo 1947435 5268817 := bstep (se 2 (by rfl) ⟨1975806, by rfl⟩ : syracuseStep 5268817 = 3951613) B3951613
theorem B7025089 : Blo 1947435 7025089 := bstep (se 2 (by rfl) ⟨2634408, by rfl⟩ : syracuseStep 7025089 = 5268817) B5268817
theorem B9366785 : Blo 1947435 9366785 := bstep (se 2 (by rfl) ⟨3512544, by rfl⟩ : syracuseStep 9366785 = 7025089) B7025089
theorem B6244523 : Blo 1947435 6244523 := bstep (se 1 (by rfl) ⟨4683392, by rfl⟩ : syracuseStep 6244523 = 9366785) B9366785
theorem B4163015 : Blo 1947435 4163015 := bstep (se 1 (by rfl) ⟨3122261, by rfl⟩ : syracuseStep 4163015 = 6244523) B6244523
theorem B11101373 : Blo 1947435 11101373 := bstep (se 3 (by rfl) ⟨2081507, by rfl⟩ : syracuseStep 11101373 = 4163015) B4163015
theorem B7400915 : Blo 1947435 7400915 := bstep (se 1 (by rfl) ⟨5550686, by rfl⟩ : syracuseStep 7400915 = 11101373) B11101373
theorem B4933943 : Blo 1947435 4933943 := bstep (se 1 (by rfl) ⟨3700457, by rfl⟩ : syracuseStep 4933943 = 7400915) B7400915
theorem B3289295 : Blo 1947435 3289295 := bstep (se 1 (by rfl) ⟨2466971, by rfl⟩ : syracuseStep 3289295 = 4933943) B4933943
theorem B2192863 : Blo 1947435 2192863 := bstep (se 1 (by rfl) ⟨1644647, by rfl⟩ : syracuseStep 2192863 = 3289295) B3289295
theorem B2923817 : Blo 1947435 2923817 := bstep (se 2 (by rfl) ⟨1096431, by rfl⟩ : syracuseStep 2923817 = 2192863) B2192863
theorem B1949211 : Blo 1947435 1949211 := bstep (se 1 (by rfl) ⟨1461908, by rfl⟩ : syracuseStep 1949211 = 2923817) B2923817
theorem B10681429 : Blo 1947435 10681429 := bbase (se 8 (by rfl) ⟨62586, by rfl⟩ : syracuseStep 10681429 = 125173) (by norm_num)
theorem B14241905 : Blo 1947435 14241905 := bstep (se 2 (by rfl) ⟨5340714, by rfl⟩ : syracuseStep 14241905 = 10681429) B10681429
theorem B9494603 : Blo 1947435 9494603 := bstep (se 1 (by rfl) ⟨7120952, by rfl⟩ : syracuseStep 9494603 = 14241905) B14241905
theorem B6329735 : Blo 1947435 6329735 := bstep (se 1 (by rfl) ⟨4747301, by rfl⟩ : syracuseStep 6329735 = 9494603) B9494603
theorem B4219823 : Blo 1947435 4219823 := bstep (se 1 (by rfl) ⟨3164867, by rfl⟩ : syracuseStep 4219823 = 6329735) B6329735
theorem B2813215 : Blo 1947435 2813215 := bstep (se 1 (by rfl) ⟨2109911, by rfl⟩ : syracuseStep 2813215 = 4219823) B4219823
theorem B3750953 : Blo 1947435 3750953 := bstep (se 2 (by rfl) ⟨1406607, by rfl⟩ : syracuseStep 3750953 = 2813215) B2813215
theorem B10002541 : Blo 1947435 10002541 := bstep (se 3 (by rfl) ⟨1875476, by rfl⟩ : syracuseStep 10002541 = 3750953) B3750953
theorem B13336721 : Blo 1947435 13336721 := bstep (se 2 (by rfl) ⟨5001270, by rfl⟩ : syracuseStep 13336721 = 10002541) B10002541
theorem B8891147 : Blo 1947435 8891147 := bstep (se 1 (by rfl) ⟨6668360, by rfl⟩ : syracuseStep 8891147 = 13336721) B13336721
theorem B5927431 : Blo 1947435 5927431 := bstep (se 1 (by rfl) ⟨4445573, by rfl⟩ : syracuseStep 5927431 = 8891147) B8891147
theorem B7903241 : Blo 1947435 7903241 := bstep (se 2 (by rfl) ⟨2963715, by rfl⟩ : syracuseStep 7903241 = 5927431) B5927431
theorem B5268827 : Blo 1947435 5268827 := bstep (se 1 (by rfl) ⟨3951620, by rfl⟩ : syracuseStep 5268827 = 7903241) B7903241
theorem B14050205 : Blo 1947435 14050205 := bstep (se 3 (by rfl) ⟨2634413, by rfl⟩ : syracuseStep 14050205 = 5268827) B5268827
theorem B9366803 : Blo 1947435 9366803 := bstep (se 1 (by rfl) ⟨7025102, by rfl⟩ : syracuseStep 9366803 = 14050205) B14050205
theorem B6244535 : Blo 1947435 6244535 := bstep (se 1 (by rfl) ⟨4683401, by rfl⟩ : syracuseStep 6244535 = 9366803) B9366803
theorem B4163023 : Blo 1947435 4163023 := bstep (se 1 (by rfl) ⟨3122267, by rfl⟩ : syracuseStep 4163023 = 6244535) B6244535
theorem B5550697 : Blo 1947435 5550697 := bstep (se 2 (by rfl) ⟨2081511, by rfl⟩ : syracuseStep 5550697 = 4163023) B4163023
theorem B7400929 : Blo 1947435 7400929 := bstep (se 2 (by rfl) ⟨2775348, by rfl⟩ : syracuseStep 7400929 = 5550697) B5550697
theorem B9867905 : Blo 1947435 9867905 := bstep (se 2 (by rfl) ⟨3700464, by rfl⟩ : syracuseStep 9867905 = 7400929) B7400929
theorem B6578603 : Blo 1947435 6578603 := bstep (se 1 (by rfl) ⟨4933952, by rfl⟩ : syracuseStep 6578603 = 9867905) B9867905
theorem B4385735 : Blo 1947435 4385735 := bstep (se 1 (by rfl) ⟨3289301, by rfl⟩ : syracuseStep 4385735 = 6578603) B6578603
theorem B2923823 : Blo 1947435 2923823 := bstep (se 1 (by rfl) ⟨2192867, by rfl⟩ : syracuseStep 2923823 = 4385735) B4385735
theorem B1949215 : Blo 1947435 1949215 := bstep (se 1 (by rfl) ⟨1461911, by rfl⟩ : syracuseStep 1949215 = 2923823) B2923823
theorem B2923829 : Blo 1947435 2923829 := bbase (se 5 (by rfl) ⟨137054, by rfl⟩ : syracuseStep 2923829 = 274109) (by norm_num)
theorem B1949219 : Blo 1947435 1949219 := bstep (se 1 (by rfl) ⟨1461914, by rfl⟩ : syracuseStep 1949219 = 2923829) B2923829
theorem B4933973 : Blo 1947435 4933973 := bbase (se 10 (by rfl) ⟨7227, by rfl⟩ : syracuseStep 4933973 = 14455) (by norm_num)
theorem B3289315 : Blo 1947435 3289315 := bstep (se 1 (by rfl) ⟨2466986, by rfl⟩ : syracuseStep 3289315 = 4933973) B4933973
theorem B4385753 : Blo 1947435 4385753 := bstep (se 2 (by rfl) ⟨1644657, by rfl⟩ : syracuseStep 4385753 = 3289315) B3289315
theorem B2923835 : Blo 1947435 2923835 := bstep (se 1 (by rfl) ⟨2192876, by rfl⟩ : syracuseStep 2923835 = 4385753) B4385753
theorem B1949223 : Blo 1947435 1949223 := bstep (se 1 (by rfl) ⟨1461917, by rfl⟩ : syracuseStep 1949223 = 2923835) B2923835
theorem B2192881 : Blo 1947435 2192881 := bbase (se 2 (by rfl) ⟨822330, by rfl⟩ : syracuseStep 2192881 = 1644661) (by norm_num)
theorem B2923841 : Blo 1947435 2923841 := bstep (se 2 (by rfl) ⟨1096440, by rfl⟩ : syracuseStep 2923841 = 2192881) B2192881
theorem B1949227 : Blo 1947435 1949227 := bstep (se 1 (by rfl) ⟨1461920, by rfl⟩ : syracuseStep 1949227 = 2923841) B2923841
theorem B12489173 : Blo 1947435 12489173 := bbase (se 7 (by rfl) ⟨146357, by rfl⟩ : syracuseStep 12489173 = 292715) (by norm_num)
theorem B8326115 : Blo 1947435 8326115 := bstep (se 1 (by rfl) ⟨6244586, by rfl⟩ : syracuseStep 8326115 = 12489173) B12489173
theorem B5550743 : Blo 1947435 5550743 := bstep (se 1 (by rfl) ⟨4163057, by rfl⟩ : syracuseStep 5550743 = 8326115) B8326115
theorem B3700495 : Blo 1947435 3700495 := bstep (se 1 (by rfl) ⟨2775371, by rfl⟩ : syracuseStep 3700495 = 5550743) B5550743
theorem B4933993 : Blo 1947435 4933993 := bstep (se 2 (by rfl) ⟨1850247, by rfl⟩ : syracuseStep 4933993 = 3700495) B3700495
theorem B6578657 : Blo 1947435 6578657 := bstep (se 2 (by rfl) ⟨2466996, by rfl⟩ : syracuseStep 6578657 = 4933993) B4933993
theorem B4385771 : Blo 1947435 4385771 := bstep (se 1 (by rfl) ⟨3289328, by rfl⟩ : syracuseStep 4385771 = 6578657) B6578657
theorem B2923847 : Blo 1947435 2923847 := bstep (se 1 (by rfl) ⟨2192885, by rfl⟩ : syracuseStep 2923847 = 4385771) B4385771
theorem B1949231 : Blo 1947435 1949231 := bstep (se 1 (by rfl) ⟨1461923, by rfl⟩ : syracuseStep 1949231 = 2923847) B2923847
theorem B2923853 : Blo 1947435 2923853 := bbase (se 3 (by rfl) ⟨548222, by rfl⟩ : syracuseStep 2923853 = 1096445) (by norm_num)
theorem B1949235 : Blo 1947435 1949235 := bstep (se 1 (by rfl) ⟨1461926, by rfl⟩ : syracuseStep 1949235 = 2923853) B2923853
theorem B4385789 : Blo 1947435 4385789 := bbase (se 3 (by rfl) ⟨822335, by rfl⟩ : syracuseStep 4385789 = 1644671) (by norm_num)
theorem B2923859 : Blo 1947435 2923859 := bstep (se 1 (by rfl) ⟨2192894, by rfl⟩ : syracuseStep 2923859 = 4385789) B4385789
theorem B1949239 : Blo 1947435 1949239 := bstep (se 1 (by rfl) ⟨1461929, by rfl⟩ : syracuseStep 1949239 = 2923859) B2923859
theorem B3289349 : Blo 1947435 3289349 := bbase (se 4 (by rfl) ⟨308376, by rfl⟩ : syracuseStep 3289349 = 616753) (by norm_num)
theorem B2192899 : Blo 1947435 2192899 := bstep (se 1 (by rfl) ⟨1644674, by rfl⟩ : syracuseStep 2192899 = 3289349) B3289349
theorem B2923865 : Blo 1947435 2923865 := bstep (se 2 (by rfl) ⟨1096449, by rfl⟩ : syracuseStep 2923865 = 2192899) B2192899
theorem B1949243 : Blo 1947435 1949243 := bstep (se 1 (by rfl) ⟨1461932, by rfl⟩ : syracuseStep 1949243 = 2923865) B2923865
theorem B14802101 : Blo 1947435 14802101 := bbase (se 5 (by rfl) ⟨693848, by rfl⟩ : syracuseStep 14802101 = 1387697) (by norm_num)
theorem B9868067 : Blo 1947435 9868067 := bstep (se 1 (by rfl) ⟨7401050, by rfl⟩ : syracuseStep 9868067 = 14802101) B14802101
theorem B6578711 : Blo 1947435 6578711 := bstep (se 1 (by rfl) ⟨4934033, by rfl⟩ : syracuseStep 6578711 = 9868067) B9868067
theorem B4385807 : Blo 1947435 4385807 := bstep (se 1 (by rfl) ⟨3289355, by rfl⟩ : syracuseStep 4385807 = 6578711) B6578711
theorem B2923871 : Blo 1947435 2923871 := bstep (se 1 (by rfl) ⟨2192903, by rfl⟩ : syracuseStep 2923871 = 4385807) B4385807
theorem B1949247 : Blo 1947435 1949247 := bstep (se 1 (by rfl) ⟨1461935, by rfl⟩ : syracuseStep 1949247 = 2923871) B2923871
theorem B2923877 : Blo 1947435 2923877 := bbase (se 4 (by rfl) ⟨274113, by rfl⟩ : syracuseStep 2923877 = 548227) (by norm_num)
theorem B1949251 : Blo 1947435 1949251 := bstep (se 1 (by rfl) ⟨1461938, by rfl⟩ : syracuseStep 1949251 = 2923877) B2923877
theorem B3700541 : Blo 1947435 3700541 := bbase (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) (by norm_num)
theorem B2467027 : Blo 1947435 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B3289369 : Blo 1947435 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B4385825 : Blo 1947435 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B2923883 : Blo 1947435 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B1949255 : Blo 1947435 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B2192917 : Blo 1947435 2192917 := bbase (se 6 (by rfl) ⟨51396, by rfl⟩ : syracuseStep 2192917 = 102793) (by norm_num)
theorem B2923889 : Blo 1947435 2923889 := bstep (se 2 (by rfl) ⟨1096458, by rfl⟩ : syracuseStep 2923889 = 2192917) B2192917
theorem B1949259 : Blo 1947435 1949259 := bstep (se 1 (by rfl) ⟨1461944, by rfl⟩ : syracuseStep 1949259 = 2923889) B2923889
theorem B2467037 : Blo 1947435 2467037 := bbase (se 3 (by rfl) ⟨462569, by rfl⟩ : syracuseStep 2467037 = 925139) (by norm_num)
theorem B6578765 : Blo 1947435 6578765 := bstep (se 3 (by rfl) ⟨1233518, by rfl⟩ : syracuseStep 6578765 = 2467037) B2467037
theorem B4385843 : Blo 1947435 4385843 := bstep (se 1 (by rfl) ⟨3289382, by rfl⟩ : syracuseStep 4385843 = 6578765) B6578765
theorem B2923895 : Blo 1947435 2923895 := bstep (se 1 (by rfl) ⟨2192921, by rfl⟩ : syracuseStep 2923895 = 4385843) B4385843
theorem B1949263 : Blo 1947435 1949263 := bstep (se 1 (by rfl) ⟨1461947, by rfl⟩ : syracuseStep 1949263 = 2923895) B2923895
theorem B2923901 : Blo 1947435 2923901 := bbase (se 3 (by rfl) ⟨548231, by rfl⟩ : syracuseStep 2923901 = 1096463) (by norm_num)
theorem B1949267 : Blo 1947435 1949267 := bstep (se 1 (by rfl) ⟨1461950, by rfl⟩ : syracuseStep 1949267 = 2923901) B2923901
theorem B4385861 : Blo 1947435 4385861 := bbase (se 4 (by rfl) ⟨411174, by rfl⟩ : syracuseStep 4385861 = 822349) (by norm_num)
theorem B2923907 : Blo 1947435 2923907 := bstep (se 1 (by rfl) ⟨2192930, by rfl⟩ : syracuseStep 2923907 = 4385861) B4385861
theorem B1949271 : Blo 1947435 1949271 := bstep (se 1 (by rfl) ⟨1461953, by rfl⟩ : syracuseStep 1949271 = 2923907) B2923907
theorem B5550869 : Blo 1947435 5550869 := bbase (se 6 (by rfl) ⟨130098, by rfl⟩ : syracuseStep 5550869 = 260197) (by norm_num)
theorem B3700579 : Blo 1947435 3700579 := bstep (se 1 (by rfl) ⟨2775434, by rfl⟩ : syracuseStep 3700579 = 5550869) B5550869
theorem B4934105 : Blo 1947435 4934105 := bstep (se 2 (by rfl) ⟨1850289, by rfl⟩ : syracuseStep 4934105 = 3700579) B3700579
theorem B3289403 : Blo 1947435 3289403 := bstep (se 1 (by rfl) ⟨2467052, by rfl⟩ : syracuseStep 3289403 = 4934105) B4934105
theorem B2192935 : Blo 1947435 2192935 := bstep (se 1 (by rfl) ⟨1644701, by rfl⟩ : syracuseStep 2192935 = 3289403) B3289403
theorem B2923913 : Blo 1947435 2923913 := bstep (se 2 (by rfl) ⟨1096467, by rfl⟩ : syracuseStep 2923913 = 2192935) B2192935
theorem B1949275 : Blo 1947435 1949275 := bstep (se 1 (by rfl) ⟨1461956, by rfl⟩ : syracuseStep 1949275 = 2923913) B2923913
theorem B9868229 : Blo 1947435 9868229 := bbase (se 4 (by rfl) ⟨925146, by rfl⟩ : syracuseStep 9868229 = 1850293) (by norm_num)
theorem B6578819 : Blo 1947435 6578819 := bstep (se 1 (by rfl) ⟨4934114, by rfl⟩ : syracuseStep 6578819 = 9868229) B9868229
theorem B4385879 : Blo 1947435 4385879 := bstep (se 1 (by rfl) ⟨3289409, by rfl⟩ : syracuseStep 4385879 = 6578819) B6578819
theorem B2923919 : Blo 1947435 2923919 := bstep (se 1 (by rfl) ⟨2192939, by rfl⟩ : syracuseStep 2923919 = 4385879) B4385879
theorem B1949279 : Blo 1947435 1949279 := bstep (se 1 (by rfl) ⟨1461959, by rfl⟩ : syracuseStep 1949279 = 2923919) B2923919
theorem B2923925 : Blo 1947435 2923925 := bbase (se 6 (by rfl) ⟨68529, by rfl⟩ : syracuseStep 2923925 = 137059) (by norm_num)
theorem B1949283 : Blo 1947435 1949283 := bstep (se 1 (by rfl) ⟨1461962, by rfl⟩ : syracuseStep 1949283 = 2923925) B2923925
theorem B8891477 : Blo 1947435 8891477 := bbase (se 8 (by rfl) ⟨52098, by rfl⟩ : syracuseStep 8891477 = 104197) (by norm_num)
theorem B5927651 : Blo 1947435 5927651 := bstep (se 1 (by rfl) ⟨4445738, by rfl⟩ : syracuseStep 5927651 = 8891477) B8891477
theorem B3951767 : Blo 1947435 3951767 := bstep (se 1 (by rfl) ⟨2963825, by rfl⟩ : syracuseStep 3951767 = 5927651) B5927651
theorem B10538045 : Blo 1947435 10538045 := bstep (se 3 (by rfl) ⟨1975883, by rfl⟩ : syracuseStep 10538045 = 3951767) B3951767
theorem B7025363 : Blo 1947435 7025363 := bstep (se 1 (by rfl) ⟨5269022, by rfl⟩ : syracuseStep 7025363 = 10538045) B10538045
theorem B4683575 : Blo 1947435 4683575 := bstep (se 1 (by rfl) ⟨3512681, by rfl⟩ : syracuseStep 4683575 = 7025363) B7025363
theorem B3122383 : Blo 1947435 3122383 := bstep (se 1 (by rfl) ⟨2341787, by rfl⟩ : syracuseStep 3122383 = 4683575) B4683575
theorem B4163177 : Blo 1947435 4163177 := bstep (se 2 (by rfl) ⟨1561191, by rfl⟩ : syracuseStep 4163177 = 3122383) B3122383
theorem B11101805 : Blo 1947435 11101805 := bstep (se 3 (by rfl) ⟨2081588, by rfl⟩ : syracuseStep 11101805 = 4163177) B4163177
theorem B7401203 : Blo 1947435 7401203 := bstep (se 1 (by rfl) ⟨5550902, by rfl⟩ : syracuseStep 7401203 = 11101805) B11101805
theorem B4934135 : Blo 1947435 4934135 := bstep (se 1 (by rfl) ⟨3700601, by rfl⟩ : syracuseStep 4934135 = 7401203) B7401203
theorem B3289423 : Blo 1947435 3289423 := bstep (se 1 (by rfl) ⟨2467067, by rfl⟩ : syracuseStep 3289423 = 4934135) B4934135
theorem B4385897 : Blo 1947435 4385897 := bstep (se 2 (by rfl) ⟨1644711, by rfl⟩ : syracuseStep 4385897 = 3289423) B3289423
theorem B2923931 : Blo 1947435 2923931 := bstep (se 1 (by rfl) ⟨2192948, by rfl⟩ : syracuseStep 2923931 = 4385897) B4385897
theorem B1949287 : Blo 1947435 1949287 := bstep (se 1 (by rfl) ⟨1461965, by rfl⟩ : syracuseStep 1949287 = 2923931) B2923931
theorem B2192953 : Blo 1947435 2192953 := bbase (se 2 (by rfl) ⟨822357, by rfl⟩ : syracuseStep 2192953 = 1644715) (by norm_num)
theorem B2923937 : Blo 1947435 2923937 := bstep (se 2 (by rfl) ⟨1096476, by rfl⟩ : syracuseStep 2923937 = 2192953) B2192953
theorem B1949291 : Blo 1947435 1949291 := bstep (se 1 (by rfl) ⟨1461968, by rfl⟩ : syracuseStep 1949291 = 2923937) B2923937
theorem B2081597 : Blo 1947435 2081597 := bbase (se 3 (by rfl) ⟨390299, by rfl⟩ : syracuseStep 2081597 = 780599) (by norm_num)
theorem B5550925 : Blo 1947435 5550925 := bstep (se 3 (by rfl) ⟨1040798, by rfl⟩ : syracuseStep 5550925 = 2081597) B2081597
theorem B7401233 : Blo 1947435 7401233 := bstep (se 2 (by rfl) ⟨2775462, by rfl⟩ : syracuseStep 7401233 = 5550925) B5550925
theorem B4934155 : Blo 1947435 4934155 := bstep (se 1 (by rfl) ⟨3700616, by rfl⟩ : syracuseStep 4934155 = 7401233) B7401233
theorem B6578873 : Blo 1947435 6578873 := bstep (se 2 (by rfl) ⟨2467077, by rfl⟩ : syracuseStep 6578873 = 4934155) B4934155
theorem B4385915 : Blo 1947435 4385915 := bstep (se 1 (by rfl) ⟨3289436, by rfl⟩ : syracuseStep 4385915 = 6578873) B6578873
theorem B2923943 : Blo 1947435 2923943 := bstep (se 1 (by rfl) ⟨2192957, by rfl⟩ : syracuseStep 2923943 = 4385915) B4385915
theorem B1949295 : Blo 1947435 1949295 := bstep (se 1 (by rfl) ⟨1461971, by rfl⟩ : syracuseStep 1949295 = 2923943) B2923943
theorem B2923949 : Blo 1947435 2923949 := bbase (se 3 (by rfl) ⟨548240, by rfl⟩ : syracuseStep 2923949 = 1096481) (by norm_num)
theorem B1949299 : Blo 1947435 1949299 := bstep (se 1 (by rfl) ⟨1461974, by rfl⟩ : syracuseStep 1949299 = 2923949) B2923949
theorem B4385933 : Blo 1947435 4385933 := bbase (se 3 (by rfl) ⟨822362, by rfl⟩ : syracuseStep 4385933 = 1644725) (by norm_num)
theorem B2923955 : Blo 1947435 2923955 := bstep (se 1 (by rfl) ⟨2192966, by rfl⟩ : syracuseStep 2923955 = 4385933) B4385933
theorem B1949303 : Blo 1947435 1949303 := bstep (se 1 (by rfl) ⟨1461977, by rfl⟩ : syracuseStep 1949303 = 2923955) B2923955
theorem B2467093 : Blo 1947435 2467093 := bbase (se 6 (by rfl) ⟨57822, by rfl⟩ : syracuseStep 2467093 = 115645) (by norm_num)
theorem B3289457 : Blo 1947435 3289457 := bstep (se 2 (by rfl) ⟨1233546, by rfl⟩ : syracuseStep 3289457 = 2467093) B2467093
theorem B2192971 : Blo 1947435 2192971 := bstep (se 1 (by rfl) ⟨1644728, by rfl⟩ : syracuseStep 2192971 = 3289457) B3289457
theorem B2923961 : Blo 1947435 2923961 := bstep (se 2 (by rfl) ⟨1096485, by rfl⟩ : syracuseStep 2923961 = 2192971) B2192971
theorem B1949307 : Blo 1947435 1949307 := bstep (se 1 (by rfl) ⟨1461980, by rfl⟩ : syracuseStep 1949307 = 2923961) B2923961
theorem B12660085 : Blo 1947435 12660085 := bbase (se 5 (by rfl) ⟨593441, by rfl⟩ : syracuseStep 12660085 = 1186883) (by norm_num)
theorem B16880113 : Blo 1947435 16880113 := bstep (se 2 (by rfl) ⟨6330042, by rfl⟩ : syracuseStep 16880113 = 12660085) B12660085
theorem B22506817 : Blo 1947435 22506817 := bstep (se 2 (by rfl) ⟨8440056, by rfl⟩ : syracuseStep 22506817 = 16880113) B16880113
theorem B30009089 : Blo 1947435 30009089 := bstep (se 2 (by rfl) ⟨11253408, by rfl⟩ : syracuseStep 30009089 = 22506817) B22506817
theorem B80024237 : Blo 1947435 80024237 := bstep (se 3 (by rfl) ⟨15004544, by rfl⟩ : syracuseStep 80024237 = 30009089) B30009089
theorem B53349491 : Blo 1947435 53349491 := bstep (se 1 (by rfl) ⟨40012118, by rfl⟩ : syracuseStep 53349491 = 80024237) B80024237
theorem B35566327 : Blo 1947435 35566327 := bstep (se 1 (by rfl) ⟨26674745, by rfl⟩ : syracuseStep 35566327 = 53349491) B53349491
theorem B47421769 : Blo 1947435 47421769 := bstep (se 2 (by rfl) ⟨17783163, by rfl⟩ : syracuseStep 47421769 = 35566327) B35566327
theorem B63229025 : Blo 1947435 63229025 := bstep (se 2 (by rfl) ⟨23710884, by rfl⟩ : syracuseStep 63229025 = 47421769) B47421769
theorem B42152683 : Blo 1947435 42152683 := bstep (se 1 (by rfl) ⟨31614512, by rfl⟩ : syracuseStep 42152683 = 63229025) B63229025
theorem B56203577 : Blo 1947435 56203577 := bstep (se 2 (by rfl) ⟨21076341, by rfl⟩ : syracuseStep 56203577 = 42152683) B42152683
theorem B37469051 : Blo 1947435 37469051 := bstep (se 1 (by rfl) ⟨28101788, by rfl⟩ : syracuseStep 37469051 = 56203577) B56203577
theorem B24979367 : Blo 1947435 24979367 := bstep (se 1 (by rfl) ⟨18734525, by rfl⟩ : syracuseStep 24979367 = 37469051) B37469051
theorem B16652911 : Blo 1947435 16652911 := bstep (se 1 (by rfl) ⟨12489683, by rfl⟩ : syracuseStep 16652911 = 24979367) B24979367
theorem B22203881 : Blo 1947435 22203881 := bstep (se 2 (by rfl) ⟨8326455, by rfl⟩ : syracuseStep 22203881 = 16652911) B16652911
theorem B14802587 : Blo 1947435 14802587 := bstep (se 1 (by rfl) ⟨11101940, by rfl⟩ : syracuseStep 14802587 = 22203881) B22203881
theorem B9868391 : Blo 1947435 9868391 := bstep (se 1 (by rfl) ⟨7401293, by rfl⟩ : syracuseStep 9868391 = 14802587) B14802587
theorem B6578927 : Blo 1947435 6578927 := bstep (se 1 (by rfl) ⟨4934195, by rfl⟩ : syracuseStep 6578927 = 9868391) B9868391
theorem B4385951 : Blo 1947435 4385951 := bstep (se 1 (by rfl) ⟨3289463, by rfl⟩ : syracuseStep 4385951 = 6578927) B6578927
theorem B2923967 : Blo 1947435 2923967 := bstep (se 1 (by rfl) ⟨2192975, by rfl⟩ : syracuseStep 2923967 = 4385951) B4385951
theorem B1949311 : Blo 1947435 1949311 := bstep (se 1 (by rfl) ⟨1461983, by rfl⟩ : syracuseStep 1949311 = 2923967) B2923967
theorem B2923973 : Blo 1947435 2923973 := bbase (se 4 (by rfl) ⟨274122, by rfl⟩ : syracuseStep 2923973 = 548245) (by norm_num)
theorem B1949315 : Blo 1947435 1949315 := bstep (se 1 (by rfl) ⟨1461986, by rfl⟩ : syracuseStep 1949315 = 2923973) B2923973
theorem B3289477 : Blo 1947435 3289477 := bbase (se 4 (by rfl) ⟨308388, by rfl⟩ : syracuseStep 3289477 = 616777) (by norm_num)
theorem B4385969 : Blo 1947435 4385969 := bstep (se 2 (by rfl) ⟨1644738, by rfl⟩ : syracuseStep 4385969 = 3289477) B3289477
theorem B2923979 : Blo 1947435 2923979 := bstep (se 1 (by rfl) ⟨2192984, by rfl⟩ : syracuseStep 2923979 = 4385969) B4385969
theorem B1949319 : Blo 1947435 1949319 := bstep (se 1 (by rfl) ⟨1461989, by rfl⟩ : syracuseStep 1949319 = 2923979) B2923979
theorem B2192989 : Blo 1947435 2192989 := bbase (se 3 (by rfl) ⟨411185, by rfl⟩ : syracuseStep 2192989 = 822371) (by norm_num)
theorem B2923985 : Blo 1947435 2923985 := bstep (se 2 (by rfl) ⟨1096494, by rfl⟩ : syracuseStep 2923985 = 2192989) B2192989
theorem B1949323 : Blo 1947435 1949323 := bstep (se 1 (by rfl) ⟨1461992, by rfl⟩ : syracuseStep 1949323 = 2923985) B2923985
theorem B6578981 : Blo 1947435 6578981 := bbase (se 4 (by rfl) ⟨616779, by rfl⟩ : syracuseStep 6578981 = 1233559) (by norm_num)
theorem B4385987 : Blo 1947435 4385987 := bstep (se 1 (by rfl) ⟨3289490, by rfl⟩ : syracuseStep 4385987 = 6578981) B6578981
theorem B2923991 : Blo 1947435 2923991 := bstep (se 1 (by rfl) ⟨2192993, by rfl⟩ : syracuseStep 2923991 = 4385987) B4385987
theorem B1949327 : Blo 1947435 1949327 := bstep (se 1 (by rfl) ⟨1461995, by rfl⟩ : syracuseStep 1949327 = 2923991) B2923991
theorem B2923997 : Blo 1947435 2923997 := bbase (se 3 (by rfl) ⟨548249, by rfl⟩ : syracuseStep 2923997 = 1096499) (by norm_num)
theorem B1949331 : Blo 1947435 1949331 := bstep (se 1 (by rfl) ⟨1461998, by rfl⟩ : syracuseStep 1949331 = 2923997) B2923997
theorem B4386005 : Blo 1947435 4386005 := bbase (se 7 (by rfl) ⟨51398, by rfl⟩ : syracuseStep 4386005 = 102797) (by norm_num)
theorem B2924003 : Blo 1947435 2924003 := bstep (se 1 (by rfl) ⟨2193002, by rfl⟩ : syracuseStep 2924003 = 4386005) B4386005
theorem B1949335 : Blo 1947435 1949335 := bstep (se 1 (by rfl) ⟨1462001, by rfl⟩ : syracuseStep 1949335 = 2924003) B2924003
theorem B6244933 : Blo 1947435 6244933 := bbase (se 4 (by rfl) ⟨585462, by rfl⟩ : syracuseStep 6244933 = 1170925) (by norm_num)
theorem B8326577 : Blo 1947435 8326577 := bstep (se 2 (by rfl) ⟨3122466, by rfl⟩ : syracuseStep 8326577 = 6244933) B6244933
theorem B5551051 : Blo 1947435 5551051 := bstep (se 1 (by rfl) ⟨4163288, by rfl⟩ : syracuseStep 5551051 = 8326577) B8326577
theorem B7401401 : Blo 1947435 7401401 := bstep (se 2 (by rfl) ⟨2775525, by rfl⟩ : syracuseStep 7401401 = 5551051) B5551051
theorem B4934267 : Blo 1947435 4934267 := bstep (se 1 (by rfl) ⟨3700700, by rfl⟩ : syracuseStep 4934267 = 7401401) B7401401
theorem B3289511 : Blo 1947435 3289511 := bstep (se 1 (by rfl) ⟨2467133, by rfl⟩ : syracuseStep 3289511 = 4934267) B4934267
theorem B2193007 : Blo 1947435 2193007 := bstep (se 1 (by rfl) ⟨1644755, by rfl⟩ : syracuseStep 2193007 = 3289511) B3289511
theorem B2924009 : Blo 1947435 2924009 := bstep (se 2 (by rfl) ⟨1096503, by rfl⟩ : syracuseStep 2924009 = 2193007) B2193007
theorem B1949339 : Blo 1947435 1949339 := bstep (se 1 (by rfl) ⟨1462004, by rfl⟩ : syracuseStep 1949339 = 2924009) B2924009
theorem B14242837 : Blo 1947435 14242837 := bbase (se 6 (by rfl) ⟨333816, by rfl⟩ : syracuseStep 14242837 = 667633) (by norm_num)
theorem B18990449 : Blo 1947435 18990449 := bstep (se 2 (by rfl) ⟨7121418, by rfl⟩ : syracuseStep 18990449 = 14242837) B14242837
theorem B12660299 : Blo 1947435 12660299 := bstep (se 1 (by rfl) ⟨9495224, by rfl⟩ : syracuseStep 12660299 = 18990449) B18990449
theorem B8440199 : Blo 1947435 8440199 := bstep (se 1 (by rfl) ⟨6330149, by rfl⟩ : syracuseStep 8440199 = 12660299) B12660299
theorem B5626799 : Blo 1947435 5626799 := bstep (se 1 (by rfl) ⟨4220099, by rfl⟩ : syracuseStep 5626799 = 8440199) B8440199
theorem B3751199 : Blo 1947435 3751199 := bstep (se 1 (by rfl) ⟨2813399, by rfl⟩ : syracuseStep 3751199 = 5626799) B5626799
theorem B2500799 : Blo 1947435 2500799 := bstep (se 1 (by rfl) ⟨1875599, by rfl⟩ : syracuseStep 2500799 = 3751199) B3751199
theorem B26675189 : Blo 1947435 26675189 := bstep (se 5 (by rfl) ⟨1250399, by rfl⟩ : syracuseStep 26675189 = 2500799) B2500799
theorem B17783459 : Blo 1947435 17783459 := bstep (se 1 (by rfl) ⟨13337594, by rfl⟩ : syracuseStep 17783459 = 26675189) B26675189
theorem B11855639 : Blo 1947435 11855639 := bstep (se 1 (by rfl) ⟨8891729, by rfl⟩ : syracuseStep 11855639 = 17783459) B17783459
theorem B7903759 : Blo 1947435 7903759 := bstep (se 1 (by rfl) ⟨5927819, by rfl⟩ : syracuseStep 7903759 = 11855639) B11855639
theorem B10538345 : Blo 1947435 10538345 := bstep (se 2 (by rfl) ⟨3951879, by rfl⟩ : syracuseStep 10538345 = 7903759) B7903759
theorem B7025563 : Blo 1947435 7025563 := bstep (se 1 (by rfl) ⟨5269172, by rfl⟩ : syracuseStep 7025563 = 10538345) B10538345
theorem B9367417 : Blo 1947435 9367417 := bstep (se 2 (by rfl) ⟨3512781, by rfl⟩ : syracuseStep 9367417 = 7025563) B7025563
theorem B12489889 : Blo 1947435 12489889 := bstep (se 2 (by rfl) ⟨4683708, by rfl⟩ : syracuseStep 12489889 = 9367417) B9367417
theorem B16653185 : Blo 1947435 16653185 := bstep (se 2 (by rfl) ⟨6244944, by rfl⟩ : syracuseStep 16653185 = 12489889) B12489889
theorem B11102123 : Blo 1947435 11102123 := bstep (se 1 (by rfl) ⟨8326592, by rfl⟩ : syracuseStep 11102123 = 16653185) B16653185
theorem B7401415 : Blo 1947435 7401415 := bstep (se 1 (by rfl) ⟨5551061, by rfl⟩ : syracuseStep 7401415 = 11102123) B11102123
theorem B9868553 : Blo 1947435 9868553 := bstep (se 2 (by rfl) ⟨3700707, by rfl⟩ : syracuseStep 9868553 = 7401415) B7401415
theorem B6579035 : Blo 1947435 6579035 := bstep (se 1 (by rfl) ⟨4934276, by rfl⟩ : syracuseStep 6579035 = 9868553) B9868553
theorem B4386023 : Blo 1947435 4386023 := bstep (se 1 (by rfl) ⟨3289517, by rfl⟩ : syracuseStep 4386023 = 6579035) B6579035
theorem B2924015 : Blo 1947435 2924015 := bstep (se 1 (by rfl) ⟨2193011, by rfl⟩ : syracuseStep 2924015 = 4386023) B4386023
theorem B1949343 : Blo 1947435 1949343 := bstep (se 1 (by rfl) ⟨1462007, by rfl⟩ : syracuseStep 1949343 = 2924015) B2924015
theorem B2924021 : Blo 1947435 2924021 := bbase (se 5 (by rfl) ⟨137063, by rfl⟩ : syracuseStep 2924021 = 274127) (by norm_num)
theorem B1949347 : Blo 1947435 1949347 := bstep (se 1 (by rfl) ⟨1462010, by rfl⟩ : syracuseStep 1949347 = 2924021) B2924021
theorem B2081657 : Blo 1947435 2081657 := bbase (se 2 (by rfl) ⟨780621, by rfl⟩ : syracuseStep 2081657 = 1561243) (by norm_num)
theorem B5551085 : Blo 1947435 5551085 := bstep (se 3 (by rfl) ⟨1040828, by rfl⟩ : syracuseStep 5551085 = 2081657) B2081657
theorem B3700723 : Blo 1947435 3700723 := bstep (se 1 (by rfl) ⟨2775542, by rfl⟩ : syracuseStep 3700723 = 5551085) B5551085
theorem B4934297 : Blo 1947435 4934297 := bstep (se 2 (by rfl) ⟨1850361, by rfl⟩ : syracuseStep 4934297 = 3700723) B3700723
theorem B3289531 : Blo 1947435 3289531 := bstep (se 1 (by rfl) ⟨2467148, by rfl⟩ : syracuseStep 3289531 = 4934297) B4934297
theorem B4386041 : Blo 1947435 4386041 := bstep (se 2 (by rfl) ⟨1644765, by rfl⟩ : syracuseStep 4386041 = 3289531) B3289531
theorem B2924027 : Blo 1947435 2924027 := bstep (se 1 (by rfl) ⟨2193020, by rfl⟩ : syracuseStep 2924027 = 4386041) B4386041
theorem B1949351 : Blo 1947435 1949351 := bstep (se 1 (by rfl) ⟨1462013, by rfl⟩ : syracuseStep 1949351 = 2924027) B2924027
theorem B2193025 : Blo 1947435 2193025 := bbase (se 2 (by rfl) ⟨822384, by rfl⟩ : syracuseStep 2193025 = 1644769) (by norm_num)
theorem B2924033 : Blo 1947435 2924033 := bstep (se 2 (by rfl) ⟨1096512, by rfl⟩ : syracuseStep 2924033 = 2193025) B2193025
theorem B1949355 : Blo 1947435 1949355 := bstep (se 1 (by rfl) ⟨1462016, by rfl⟩ : syracuseStep 1949355 = 2924033) B2924033
theorem B4934317 : Blo 1947435 4934317 := bbase (se 3 (by rfl) ⟨925184, by rfl⟩ : syracuseStep 4934317 = 1850369) (by norm_num)
theorem B6579089 : Blo 1947435 6579089 := bstep (se 2 (by rfl) ⟨2467158, by rfl⟩ : syracuseStep 6579089 = 4934317) B4934317
theorem B4386059 : Blo 1947435 4386059 := bstep (se 1 (by rfl) ⟨3289544, by rfl⟩ : syracuseStep 4386059 = 6579089) B6579089
theorem B2924039 : Blo 1947435 2924039 := bstep (se 1 (by rfl) ⟨2193029, by rfl⟩ : syracuseStep 2924039 = 4386059) B4386059
theorem B1949359 : Blo 1947435 1949359 := bstep (se 1 (by rfl) ⟨1462019, by rfl⟩ : syracuseStep 1949359 = 2924039) B2924039
theorem B2924045 : Blo 1947435 2924045 := bbase (se 3 (by rfl) ⟨548258, by rfl⟩ : syracuseStep 2924045 = 1096517) (by norm_num)
theorem B1949363 : Blo 1947435 1949363 := bstep (se 1 (by rfl) ⟨1462022, by rfl⟩ : syracuseStep 1949363 = 2924045) B2924045
theorem B4386077 : Blo 1947435 4386077 := bbase (se 3 (by rfl) ⟨822389, by rfl⟩ : syracuseStep 4386077 = 1644779) (by norm_num)
theorem B2924051 : Blo 1947435 2924051 := bstep (se 1 (by rfl) ⟨2193038, by rfl⟩ : syracuseStep 2924051 = 4386077) B4386077
theorem B1949367 : Blo 1947435 1949367 := bstep (se 1 (by rfl) ⟨1462025, by rfl⟩ : syracuseStep 1949367 = 2924051) B2924051
theorem B3289565 : Blo 1947435 3289565 := bbase (se 3 (by rfl) ⟨616793, by rfl⟩ : syracuseStep 3289565 = 1233587) (by norm_num)
theorem B2193043 : Blo 1947435 2193043 := bstep (se 1 (by rfl) ⟨1644782, by rfl⟩ : syracuseStep 2193043 = 3289565) B3289565
theorem B2924057 : Blo 1947435 2924057 := bstep (se 2 (by rfl) ⟨1096521, by rfl⟩ : syracuseStep 2924057 = 2193043) B2193043
theorem B1949371 : Blo 1947435 1949371 := bstep (se 1 (by rfl) ⟨1462028, by rfl⟩ : syracuseStep 1949371 = 2924057) B2924057
theorem B2222969 : Blo 1947435 2222969 := bbase (se 2 (by rfl) ⟨833613, by rfl⟩ : syracuseStep 2222969 = 1667227) (by norm_num)
theorem B5927917 : Blo 1947435 5927917 := bstep (se 3 (by rfl) ⟨1111484, by rfl⟩ : syracuseStep 5927917 = 2222969) B2222969
theorem B7903889 : Blo 1947435 7903889 := bstep (se 2 (by rfl) ⟨2963958, by rfl⟩ : syracuseStep 7903889 = 5927917) B5927917
theorem B5269259 : Blo 1947435 5269259 := bstep (se 1 (by rfl) ⟨3951944, by rfl⟩ : syracuseStep 5269259 = 7903889) B7903889
theorem B14051357 : Blo 1947435 14051357 := bstep (se 3 (by rfl) ⟨2634629, by rfl⟩ : syracuseStep 14051357 = 5269259) B5269259
theorem B9367571 : Blo 1947435 9367571 := bstep (se 1 (by rfl) ⟨7025678, by rfl⟩ : syracuseStep 9367571 = 14051357) B14051357
theorem B6245047 : Blo 1947435 6245047 := bstep (se 1 (by rfl) ⟨4683785, by rfl⟩ : syracuseStep 6245047 = 9367571) B9367571
theorem B8326729 : Blo 1947435 8326729 := bstep (se 2 (by rfl) ⟨3122523, by rfl⟩ : syracuseStep 8326729 = 6245047) B6245047
theorem B11102305 : Blo 1947435 11102305 := bstep (se 2 (by rfl) ⟨4163364, by rfl⟩ : syracuseStep 11102305 = 8326729) B8326729
theorem B14803073 : Blo 1947435 14803073 := bstep (se 2 (by rfl) ⟨5551152, by rfl⟩ : syracuseStep 14803073 = 11102305) B11102305
theorem B9868715 : Blo 1947435 9868715 := bstep (se 1 (by rfl) ⟨7401536, by rfl⟩ : syracuseStep 9868715 = 14803073) B14803073
theorem B6579143 : Blo 1947435 6579143 := bstep (se 1 (by rfl) ⟨4934357, by rfl⟩ : syracuseStep 6579143 = 9868715) B9868715
theorem B4386095 : Blo 1947435 4386095 := bstep (se 1 (by rfl) ⟨3289571, by rfl⟩ : syracuseStep 4386095 = 6579143) B6579143
theorem B2924063 : Blo 1947435 2924063 := bstep (se 1 (by rfl) ⟨2193047, by rfl⟩ : syracuseStep 2924063 = 4386095) B4386095
theorem B1949375 : Blo 1947435 1949375 := bstep (se 1 (by rfl) ⟨1462031, by rfl⟩ : syracuseStep 1949375 = 2924063) B2924063
theorem B2924069 : Blo 1947435 2924069 := bbase (se 4 (by rfl) ⟨274131, by rfl⟩ : syracuseStep 2924069 = 548263) (by norm_num)
theorem B1949379 : Blo 1947435 1949379 := bstep (se 1 (by rfl) ⟨1462034, by rfl⟩ : syracuseStep 1949379 = 2924069) B2924069
theorem B2467189 : Blo 1947435 2467189 := bbase (se 5 (by rfl) ⟨115649, by rfl⟩ : syracuseStep 2467189 = 231299) (by norm_num)
theorem B3289585 : Blo 1947435 3289585 := bstep (se 2 (by rfl) ⟨1233594, by rfl⟩ : syracuseStep 3289585 = 2467189) B2467189
theorem B4386113 : Blo 1947435 4386113 := bstep (se 2 (by rfl) ⟨1644792, by rfl⟩ : syracuseStep 4386113 = 3289585) B3289585
theorem B2924075 : Blo 1947435 2924075 := bstep (se 1 (by rfl) ⟨2193056, by rfl⟩ : syracuseStep 2924075 = 4386113) B4386113
theorem B1949383 : Blo 1947435 1949383 := bstep (se 1 (by rfl) ⟨1462037, by rfl⟩ : syracuseStep 1949383 = 2924075) B2924075
theorem B2193061 : Blo 1947435 2193061 := bbase (se 4 (by rfl) ⟨205599, by rfl⟩ : syracuseStep 2193061 = 411199) (by norm_num)
theorem B2924081 : Blo 1947435 2924081 := bstep (se 2 (by rfl) ⟨1096530, by rfl⟩ : syracuseStep 2924081 = 2193061) B2193061
theorem B1949387 : Blo 1947435 1949387 := bstep (se 1 (by rfl) ⟨1462040, by rfl⟩ : syracuseStep 1949387 = 2924081) B2924081
theorem B10003445 : Blo 1947435 10003445 := bbase (se 5 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 10003445 = 937823) (by norm_num)
theorem B6668963 : Blo 1947435 6668963 := bstep (se 1 (by rfl) ⟨5001722, by rfl⟩ : syracuseStep 6668963 = 10003445) B10003445
theorem B4445975 : Blo 1947435 4445975 := bstep (se 1 (by rfl) ⟨3334481, by rfl⟩ : syracuseStep 4445975 = 6668963) B6668963
theorem B11855933 : Blo 1947435 11855933 := bstep (se 3 (by rfl) ⟨2222987, by rfl⟩ : syracuseStep 11855933 = 4445975) B4445975
theorem B7903955 : Blo 1947435 7903955 := bstep (se 1 (by rfl) ⟨5927966, by rfl⟩ : syracuseStep 7903955 = 11855933) B11855933
theorem B5269303 : Blo 1947435 5269303 := bstep (se 1 (by rfl) ⟨3951977, by rfl⟩ : syracuseStep 5269303 = 7903955) B7903955
theorem B28102949 : Blo 1947435 28102949 := bstep (se 4 (by rfl) ⟨2634651, by rfl⟩ : syracuseStep 28102949 = 5269303) B5269303
theorem B18735299 : Blo 1947435 18735299 := bstep (se 1 (by rfl) ⟨14051474, by rfl⟩ : syracuseStep 18735299 = 28102949) B28102949
theorem B12490199 : Blo 1947435 12490199 := bstep (se 1 (by rfl) ⟨9367649, by rfl⟩ : syracuseStep 12490199 = 18735299) B18735299
theorem B8326799 : Blo 1947435 8326799 := bstep (se 1 (by rfl) ⟨6245099, by rfl⟩ : syracuseStep 8326799 = 12490199) B12490199
theorem B5551199 : Blo 1947435 5551199 := bstep (se 1 (by rfl) ⟨4163399, by rfl⟩ : syracuseStep 5551199 = 8326799) B8326799
theorem B3700799 : Blo 1947435 3700799 := bstep (se 1 (by rfl) ⟨2775599, by rfl⟩ : syracuseStep 3700799 = 5551199) B5551199
theorem B2467199 : Blo 1947435 2467199 := bstep (se 1 (by rfl) ⟨1850399, by rfl⟩ : syracuseStep 2467199 = 3700799) B3700799
theorem B6579197 : Blo 1947435 6579197 := bstep (se 3 (by rfl) ⟨1233599, by rfl⟩ : syracuseStep 6579197 = 2467199) B2467199
theorem B4386131 : Blo 1947435 4386131 := bstep (se 1 (by rfl) ⟨3289598, by rfl⟩ : syracuseStep 4386131 = 6579197) B6579197
theorem B2924087 : Blo 1947435 2924087 := bstep (se 1 (by rfl) ⟨2193065, by rfl⟩ : syracuseStep 2924087 = 4386131) B4386131
theorem B1949391 : Blo 1947435 1949391 := bstep (se 1 (by rfl) ⟨1462043, by rfl⟩ : syracuseStep 1949391 = 2924087) B2924087
theorem B2924093 : Blo 1947435 2924093 := bbase (se 3 (by rfl) ⟨548267, by rfl⟩ : syracuseStep 2924093 = 1096535) (by norm_num)
theorem B1949395 : Blo 1947435 1949395 := bstep (se 1 (by rfl) ⟨1462046, by rfl⟩ : syracuseStep 1949395 = 2924093) B2924093
theorem B4386149 : Blo 1947435 4386149 := bbase (se 4 (by rfl) ⟨411201, by rfl⟩ : syracuseStep 4386149 = 822403) (by norm_num)
theorem B2924099 : Blo 1947435 2924099 := bstep (se 1 (by rfl) ⟨2193074, by rfl⟩ : syracuseStep 2924099 = 4386149) B4386149
theorem B1949399 : Blo 1947435 1949399 := bstep (se 1 (by rfl) ⟨1462049, by rfl⟩ : syracuseStep 1949399 = 2924099) B2924099
theorem B4934429 : Blo 1947435 4934429 := bbase (se 3 (by rfl) ⟨925205, by rfl⟩ : syracuseStep 4934429 = 1850411) (by norm_num)
theorem B3289619 : Blo 1947435 3289619 := bstep (se 1 (by rfl) ⟨2467214, by rfl⟩ : syracuseStep 3289619 = 4934429) B4934429
theorem B2193079 : Blo 1947435 2193079 := bstep (se 1 (by rfl) ⟨1644809, by rfl⟩ : syracuseStep 2193079 = 3289619) B3289619
theorem B2924105 : Blo 1947435 2924105 := bstep (se 2 (by rfl) ⟨1096539, by rfl⟩ : syracuseStep 2924105 = 2193079) B2193079
theorem B1949403 : Blo 1947435 1949403 := bstep (se 1 (by rfl) ⟨1462052, by rfl⟩ : syracuseStep 1949403 = 2924105) B2924105
theorem B3700829 : Blo 1947435 3700829 := bbase (se 3 (by rfl) ⟨693905, by rfl⟩ : syracuseStep 3700829 = 1387811) (by norm_num)
theorem B9868877 : Blo 1947435 9868877 := bstep (se 3 (by rfl) ⟨1850414, by rfl⟩ : syracuseStep 9868877 = 3700829) B3700829
theorem B6579251 : Blo 1947435 6579251 := bstep (se 1 (by rfl) ⟨4934438, by rfl⟩ : syracuseStep 6579251 = 9868877) B9868877
theorem B4386167 : Blo 1947435 4386167 := bstep (se 1 (by rfl) ⟨3289625, by rfl⟩ : syracuseStep 4386167 = 6579251) B6579251
theorem B2924111 : Blo 1947435 2924111 := bstep (se 1 (by rfl) ⟨2193083, by rfl⟩ : syracuseStep 2924111 = 4386167) B4386167
theorem B1949407 : Blo 1947435 1949407 := bstep (se 1 (by rfl) ⟨1462055, by rfl⟩ : syracuseStep 1949407 = 2924111) B2924111
theorem B2924117 : Blo 1947435 2924117 := bbase (se 8 (by rfl) ⟨17133, by rfl⟩ : syracuseStep 2924117 = 34267) (by norm_num)
theorem B1949411 : Blo 1947435 1949411 := bstep (se 1 (by rfl) ⟨1462058, by rfl⟩ : syracuseStep 1949411 = 2924117) B2924117
theorem B8326901 : Blo 1947435 8326901 := bbase (se 5 (by rfl) ⟨390323, by rfl⟩ : syracuseStep 8326901 = 780647) (by norm_num)
theorem B5551267 : Blo 1947435 5551267 := bstep (se 1 (by rfl) ⟨4163450, by rfl⟩ : syracuseStep 5551267 = 8326901) B8326901
theorem B7401689 : Blo 1947435 7401689 := bstep (se 2 (by rfl) ⟨2775633, by rfl⟩ : syracuseStep 7401689 = 5551267) B5551267
theorem B4934459 : Blo 1947435 4934459 := bstep (se 1 (by rfl) ⟨3700844, by rfl⟩ : syracuseStep 4934459 = 7401689) B7401689
theorem B3289639 : Blo 1947435 3289639 := bstep (se 1 (by rfl) ⟨2467229, by rfl⟩ : syracuseStep 3289639 = 4934459) B4934459
theorem B4386185 : Blo 1947435 4386185 := bstep (se 2 (by rfl) ⟨1644819, by rfl⟩ : syracuseStep 4386185 = 3289639) B3289639
theorem B2924123 : Blo 1947435 2924123 := bstep (se 1 (by rfl) ⟨2193092, by rfl⟩ : syracuseStep 2924123 = 4386185) B4386185
theorem B1949415 : Blo 1947435 1949415 := bstep (se 1 (by rfl) ⟨1462061, by rfl⟩ : syracuseStep 1949415 = 2924123) B2924123
theorem B2193097 : Blo 1947435 2193097 := bbase (se 2 (by rfl) ⟨822411, by rfl⟩ : syracuseStep 2193097 = 1644823) (by norm_num)
theorem B2924129 : Blo 1947435 2924129 := bstep (se 2 (by rfl) ⟨1096548, by rfl⟩ : syracuseStep 2924129 = 2193097) B2193097
theorem B1949419 : Blo 1947435 1949419 := bstep (se 1 (by rfl) ⟨1462064, by rfl⟩ : syracuseStep 1949419 = 2924129) B2924129
theorem B4683901 : Blo 1947435 4683901 := bbase (se 3 (by rfl) ⟨878231, by rfl⟩ : syracuseStep 4683901 = 1756463) (by norm_num)
theorem B6245201 : Blo 1947435 6245201 := bstep (se 2 (by rfl) ⟨2341950, by rfl⟩ : syracuseStep 6245201 = 4683901) B4683901
theorem B16653869 : Blo 1947435 16653869 := bstep (se 3 (by rfl) ⟨3122600, by rfl⟩ : syracuseStep 16653869 = 6245201) B6245201
theorem B11102579 : Blo 1947435 11102579 := bstep (se 1 (by rfl) ⟨8326934, by rfl⟩ : syracuseStep 11102579 = 16653869) B16653869
theorem B7401719 : Blo 1947435 7401719 := bstep (se 1 (by rfl) ⟨5551289, by rfl⟩ : syracuseStep 7401719 = 11102579) B11102579
theorem B4934479 : Blo 1947435 4934479 := bstep (se 1 (by rfl) ⟨3700859, by rfl⟩ : syracuseStep 4934479 = 7401719) B7401719
theorem B6579305 : Blo 1947435 6579305 := bstep (se 2 (by rfl) ⟨2467239, by rfl⟩ : syracuseStep 6579305 = 4934479) B4934479
theorem B4386203 : Blo 1947435 4386203 := bstep (se 1 (by rfl) ⟨3289652, by rfl⟩ : syracuseStep 4386203 = 6579305) B6579305
theorem B2924135 : Blo 1947435 2924135 := bstep (se 1 (by rfl) ⟨2193101, by rfl⟩ : syracuseStep 2924135 = 4386203) B4386203
theorem B1949423 : Blo 1947435 1949423 := bstep (se 1 (by rfl) ⟨1462067, by rfl⟩ : syracuseStep 1949423 = 2924135) B2924135
theorem B2924141 : Blo 1947435 2924141 := bbase (se 3 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 2924141 = 1096553) (by norm_num)
theorem B1949427 : Blo 1947435 1949427 := bstep (se 1 (by rfl) ⟨1462070, by rfl⟩ : syracuseStep 1949427 = 2924141) B2924141
theorem B4386221 : Blo 1947435 4386221 := bbase (se 3 (by rfl) ⟨822416, by rfl⟩ : syracuseStep 4386221 = 1644833) (by norm_num)
theorem B2924147 : Blo 1947435 2924147 := bstep (se 1 (by rfl) ⟨2193110, by rfl⟩ : syracuseStep 2924147 = 4386221) B4386221
theorem B1949431 : Blo 1947435 1949431 := bstep (se 1 (by rfl) ⟨1462073, by rfl⟩ : syracuseStep 1949431 = 2924147) B2924147
theorem B3122621 : Blo 1947435 3122621 := bbase (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) (by norm_num)
theorem B2081747 : Blo 1947435 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B5551325 : Blo 1947435 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B3700883 : Blo 1947435 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B2467255 : Blo 1947435 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B3289673 : Blo 1947435 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B2193115 : Blo 1947435 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B2924153 : Blo 1947435 2924153 := bstep (se 2 (by rfl) ⟨1096557, by rfl⟩ : syracuseStep 2924153 = 2193115) B2193115
theorem B1949435 : Blo 1947435 1949435 := bstep (se 1 (by rfl) ⟨1462076, by rfl⟩ : syracuseStep 1949435 = 2924153) B2924153
theorem C0 (j : ℕ) (h1 : 486858 ≤ j) (h2 : j ≤ 487358) : Blo 1947435 (4 * j + 3) := by
  interval_cases j
  · exact B1947435
  · exact B1947439
  · exact B1947443
  · exact B1947447
  · exact B1947451
  · exact B1947455
  · exact B1947459
  · exact B1947463
  · exact B1947467
  · exact B1947471
  · exact B1947475
  · exact B1947479
  · exact B1947483
  · exact B1947487
  · exact B1947491
  · exact B1947495
  · exact B1947499
  · exact B1947503
  · exact B1947507
  · exact B1947511
  · exact B1947515
  · exact B1947519
  · exact B1947523
  · exact B1947527
  · exact B1947531
  · exact B1947535
  · exact B1947539
  · exact B1947543
  · exact B1947547
  · exact B1947551
  · exact B1947555
  · exact B1947559
  · exact B1947563
  · exact B1947567
  · exact B1947571
  · exact B1947575
  · exact B1947579
  · exact B1947583
  · exact B1947587
  · exact B1947591
  · exact B1947595
  · exact B1947599
  · exact B1947603
  · exact B1947607
  · exact B1947611
  · exact B1947615
  · exact B1947619
  · exact B1947623
  · exact B1947627
  · exact B1947631
  · exact B1947635
  · exact B1947639
  · exact B1947643
  · exact B1947647
  · exact B1947651
  · exact B1947655
  · exact B1947659
  · exact B1947663
  · exact B1947667
  · exact B1947671
  · exact B1947675
  · exact B1947679
  · exact B1947683
  · exact B1947687
  · exact B1947691
  · exact B1947695
  · exact B1947699
  · exact B1947703
  · exact B1947707
  · exact B1947711
  · exact B1947715
  · exact B1947719
  · exact B1947723
  · exact B1947727
  · exact B1947731
  · exact B1947735
  · exact B1947739
  · exact B1947743
  · exact B1947747
  · exact B1947751
  · exact B1947755
  · exact B1947759
  · exact B1947763
  · exact B1947767
  · exact B1947771
  · exact B1947775
  · exact B1947779
  · exact B1947783
  · exact B1947787
  · exact B1947791
  · exact B1947795
  · exact B1947799
  · exact B1947803
  · exact B1947807
  · exact B1947811
  · exact B1947815
  · exact B1947819
  · exact B1947823
  · exact B1947827
  · exact B1947831
  · exact B1947835
  · exact B1947839
  · exact B1947843
  · exact B1947847
  · exact B1947851
  · exact B1947855
  · exact B1947859
  · exact B1947863
  · exact B1947867
  · exact B1947871
  · exact B1947875
  · exact B1947879
  · exact B1947883
  · exact B1947887
  · exact B1947891
  · exact B1947895
  · exact B1947899
  · exact B1947903
  · exact B1947907
  · exact B1947911
  · exact B1947915
  · exact B1947919
  · exact B1947923
  · exact B1947927
  · exact B1947931
  · exact B1947935
  · exact B1947939
  · exact B1947943
  · exact B1947947
  · exact B1947951
  · exact B1947955
  · exact B1947959
  · exact B1947963
  · exact B1947967
  · exact B1947971
  · exact B1947975
  · exact B1947979
  · exact B1947983
  · exact B1947987
  · exact B1947991
  · exact B1947995
  · exact B1947999
  · exact B1948003
  · exact B1948007
  · exact B1948011
  · exact B1948015
  · exact B1948019
  · exact B1948023
  · exact B1948027
  · exact B1948031
  · exact B1948035
  · exact B1948039
  · exact B1948043
  · exact B1948047
  · exact B1948051
  · exact B1948055
  · exact B1948059
  · exact B1948063
  · exact B1948067
  · exact B1948071
  · exact B1948075
  · exact B1948079
  · exact B1948083
  · exact B1948087
  · exact B1948091
  · exact B1948095
  · exact B1948099
  · exact B1948103
  · exact B1948107
  · exact B1948111
  · exact B1948115
  · exact B1948119
  · exact B1948123
  · exact B1948127
  · exact B1948131
  · exact B1948135
  · exact B1948139
  · exact B1948143
  · exact B1948147
  · exact B1948151
  · exact B1948155
  · exact B1948159
  · exact B1948163
  · exact B1948167
  · exact B1948171
  · exact B1948175
  · exact B1948179
  · exact B1948183
  · exact B1948187
  · exact B1948191
  · exact B1948195
  · exact B1948199
  · exact B1948203
  · exact B1948207
  · exact B1948211
  · exact B1948215
  · exact B1948219
  · exact B1948223
  · exact B1948227
  · exact B1948231
  · exact B1948235
  · exact B1948239
  · exact B1948243
  · exact B1948247
  · exact B1948251
  · exact B1948255
  · exact B1948259
  · exact B1948263
  · exact B1948267
  · exact B1948271
  · exact B1948275
  · exact B1948279
  · exact B1948283
  · exact B1948287
  · exact B1948291
  · exact B1948295
  · exact B1948299
  · exact B1948303
  · exact B1948307
  · exact B1948311
  · exact B1948315
  · exact B1948319
  · exact B1948323
  · exact B1948327
  · exact B1948331
  · exact B1948335
  · exact B1948339
  · exact B1948343
  · exact B1948347
  · exact B1948351
  · exact B1948355
  · exact B1948359
  · exact B1948363
  · exact B1948367
  · exact B1948371
  · exact B1948375
  · exact B1948379
  · exact B1948383
  · exact B1948387
  · exact B1948391
  · exact B1948395
  · exact B1948399
  · exact B1948403
  · exact B1948407
  · exact B1948411
  · exact B1948415
  · exact B1948419
  · exact B1948423
  · exact B1948427
  · exact B1948431
  · exact B1948435
  · exact B1948439
  · exact B1948443
  · exact B1948447
  · exact B1948451
  · exact B1948455
  · exact B1948459
  · exact B1948463
  · exact B1948467
  · exact B1948471
  · exact B1948475
  · exact B1948479
  · exact B1948483
  · exact B1948487
  · exact B1948491
  · exact B1948495
  · exact B1948499
  · exact B1948503
  · exact B1948507
  · exact B1948511
  · exact B1948515
  · exact B1948519
  · exact B1948523
  · exact B1948527
  · exact B1948531
  · exact B1948535
  · exact B1948539
  · exact B1948543
  · exact B1948547
  · exact B1948551
  · exact B1948555
  · exact B1948559
  · exact B1948563
  · exact B1948567
  · exact B1948571
  · exact B1948575
  · exact B1948579
  · exact B1948583
  · exact B1948587
  · exact B1948591
  · exact B1948595
  · exact B1948599
  · exact B1948603
  · exact B1948607
  · exact B1948611
  · exact B1948615
  · exact B1948619
  · exact B1948623
  · exact B1948627
  · exact B1948631
  · exact B1948635
  · exact B1948639
  · exact B1948643
  · exact B1948647
  · exact B1948651
  · exact B1948655
  · exact B1948659
  · exact B1948663
  · exact B1948667
  · exact B1948671
  · exact B1948675
  · exact B1948679
  · exact B1948683
  · exact B1948687
  · exact B1948691
  · exact B1948695
  · exact B1948699
  · exact B1948703
  · exact B1948707
  · exact B1948711
  · exact B1948715
  · exact B1948719
  · exact B1948723
  · exact B1948727
  · exact B1948731
  · exact B1948735
  · exact B1948739
  · exact B1948743
  · exact B1948747
  · exact B1948751
  · exact B1948755
  · exact B1948759
  · exact B1948763
  · exact B1948767
  · exact B1948771
  · exact B1948775
  · exact B1948779
  · exact B1948783
  · exact B1948787
  · exact B1948791
  · exact B1948795
  · exact B1948799
  · exact B1948803
  · exact B1948807
  · exact B1948811
  · exact B1948815
  · exact B1948819
  · exact B1948823
  · exact B1948827
  · exact B1948831
  · exact B1948835
  · exact B1948839
  · exact B1948843
  · exact B1948847
  · exact B1948851
  · exact B1948855
  · exact B1948859
  · exact B1948863
  · exact B1948867
  · exact B1948871
  · exact B1948875
  · exact B1948879
  · exact B1948883
  · exact B1948887
  · exact B1948891
  · exact B1948895
  · exact B1948899
  · exact B1948903
  · exact B1948907
  · exact B1948911
  · exact B1948915
  · exact B1948919
  · exact B1948923
  · exact B1948927
  · exact B1948931
  · exact B1948935
  · exact B1948939
  · exact B1948943
  · exact B1948947
  · exact B1948951
  · exact B1948955
  · exact B1948959
  · exact B1948963
  · exact B1948967
  · exact B1948971
  · exact B1948975
  · exact B1948979
  · exact B1948983
  · exact B1948987
  · exact B1948991
  · exact B1948995
  · exact B1948999
  · exact B1949003
  · exact B1949007
  · exact B1949011
  · exact B1949015
  · exact B1949019
  · exact B1949023
  · exact B1949027
  · exact B1949031
  · exact B1949035
  · exact B1949039
  · exact B1949043
  · exact B1949047
  · exact B1949051
  · exact B1949055
  · exact B1949059
  · exact B1949063
  · exact B1949067
  · exact B1949071
  · exact B1949075
  · exact B1949079
  · exact B1949083
  · exact B1949087
  · exact B1949091
  · exact B1949095
  · exact B1949099
  · exact B1949103
  · exact B1949107
  · exact B1949111
  · exact B1949115
  · exact B1949119
  · exact B1949123
  · exact B1949127
  · exact B1949131
  · exact B1949135
  · exact B1949139
  · exact B1949143
  · exact B1949147
  · exact B1949151
  · exact B1949155
  · exact B1949159
  · exact B1949163
  · exact B1949167
  · exact B1949171
  · exact B1949175
  · exact B1949179
  · exact B1949183
  · exact B1949187
  · exact B1949191
  · exact B1949195
  · exact B1949199
  · exact B1949203
  · exact B1949207
  · exact B1949211
  · exact B1949215
  · exact B1949219
  · exact B1949223
  · exact B1949227
  · exact B1949231
  · exact B1949235
  · exact B1949239
  · exact B1949243
  · exact B1949247
  · exact B1949251
  · exact B1949255
  · exact B1949259
  · exact B1949263
  · exact B1949267
  · exact B1949271
  · exact B1949275
  · exact B1949279
  · exact B1949283
  · exact B1949287
  · exact B1949291
  · exact B1949295
  · exact B1949299
  · exact B1949303
  · exact B1949307
  · exact B1949311
  · exact B1949315
  · exact B1949319
  · exact B1949323
  · exact B1949327
  · exact B1949331
  · exact B1949335
  · exact B1949339
  · exact B1949343
  · exact B1949347
  · exact B1949351
  · exact B1949355
  · exact B1949359
  · exact B1949363
  · exact B1949367
  · exact B1949371
  · exact B1949375
  · exact B1949379
  · exact B1949383
  · exact B1949387
  · exact B1949391
  · exact B1949395
  · exact B1949399
  · exact B1949403
  · exact B1949407
  · exact B1949411
  · exact B1949415
  · exact B1949419
  · exact B1949423
  · exact B1949427
  · exact B1949431
  · exact B1949435
theorem solution (m : ℕ) (hlo : 1947435 ≤ m) (hhi : m ≤ 1949435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 486858 ≤ j := by omega
    have hj2 : j ≤ 487358 := by omega
    have hb : Blo 1947435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
