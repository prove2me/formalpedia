-- Prove2me | solution 1 for syracuse_descends_range_2091435_2093435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:26.574036+00:00
-- url     : https://prove2.me/submissions/1b78db20-b72c-4049-9f42-200762bed46a

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

theorem B2352865 : Blo 2091435 2352865 := bbase (se 2 (by rfl) ⟨882324, by rfl⟩ : syracuseStep 2352865 = 1764649) (by norm_num)
theorem B3137153 : Blo 2091435 3137153 := bstep (se 2 (by rfl) ⟨1176432, by rfl⟩ : syracuseStep 3137153 = 2352865) B2352865
theorem B2091435 : Blo 2091435 2091435 := bstep (se 1 (by rfl) ⟨1568576, by rfl⟩ : syracuseStep 2091435 = 3137153) B3137153
theorem B5293957 : Blo 2091435 5293957 := bbase (se 4 (by rfl) ⟨496308, by rfl⟩ : syracuseStep 5293957 = 992617) (by norm_num)
theorem B7058609 : Blo 2091435 7058609 := bstep (se 2 (by rfl) ⟨2646978, by rfl⟩ : syracuseStep 7058609 = 5293957) B5293957
theorem B4705739 : Blo 2091435 4705739 := bstep (se 1 (by rfl) ⟨3529304, by rfl⟩ : syracuseStep 4705739 = 7058609) B7058609
theorem B3137159 : Blo 2091435 3137159 := bstep (se 1 (by rfl) ⟨2352869, by rfl⟩ : syracuseStep 3137159 = 4705739) B4705739
theorem B2091439 : Blo 2091435 2091439 := bstep (se 1 (by rfl) ⟨1568579, by rfl⟩ : syracuseStep 2091439 = 3137159) B3137159
theorem B3137165 : Blo 2091435 3137165 := bbase (se 3 (by rfl) ⟨588218, by rfl⟩ : syracuseStep 3137165 = 1176437) (by norm_num)
theorem B2091443 : Blo 2091435 2091443 := bstep (se 1 (by rfl) ⟨1568582, by rfl⟩ : syracuseStep 2091443 = 3137165) B3137165
theorem B4705757 : Blo 2091435 4705757 := bbase (se 3 (by rfl) ⟨882329, by rfl⟩ : syracuseStep 4705757 = 1764659) (by norm_num)
theorem B3137171 : Blo 2091435 3137171 := bstep (se 1 (by rfl) ⟨2352878, by rfl⟩ : syracuseStep 3137171 = 4705757) B4705757
theorem B2091447 : Blo 2091435 2091447 := bstep (se 1 (by rfl) ⟨1568585, by rfl⟩ : syracuseStep 2091447 = 3137171) B3137171
theorem B3529325 : Blo 2091435 3529325 := bbase (se 3 (by rfl) ⟨661748, by rfl⟩ : syracuseStep 3529325 = 1323497) (by norm_num)
theorem B2352883 : Blo 2091435 2352883 := bstep (se 1 (by rfl) ⟨1764662, by rfl⟩ : syracuseStep 2352883 = 3529325) B3529325
theorem B3137177 : Blo 2091435 3137177 := bstep (se 2 (by rfl) ⟨1176441, by rfl⟩ : syracuseStep 3137177 = 2352883) B2352883
theorem B2091451 : Blo 2091435 2091451 := bstep (se 1 (by rfl) ⟨1568588, by rfl⟩ : syracuseStep 2091451 = 3137177) B3137177
theorem B3626293 : Blo 2091435 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B4835057 : Blo 2091435 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B51573941 : Blo 2091435 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B34382627 : Blo 2091435 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B22921751 : Blo 2091435 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B15281167 : Blo 2091435 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B325998229 : Blo 2091435 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B434664305 : Blo 2091435 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B289776203 : Blo 2091435 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B193184135 : Blo 2091435 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B128789423 : Blo 2091435 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B85859615 : Blo 2091435 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B57239743 : Blo 2091435 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B76319657 : Blo 2091435 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B50879771 : Blo 2091435 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B33919847 : Blo 2091435 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B22613231 : Blo 2091435 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B15075487 : Blo 2091435 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B20100649 : Blo 2091435 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B26800865 : Blo 2091435 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B17867243 : Blo 2091435 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B11911495 : Blo 2091435 11911495 := bstep (se 1 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 11911495 = 17867243) B17867243
theorem B15881993 : Blo 2091435 15881993 := bstep (se 2 (by rfl) ⟨5955747, by rfl⟩ : syracuseStep 15881993 = 11911495) B11911495
theorem B10587995 : Blo 2091435 10587995 := bstep (se 1 (by rfl) ⟨7940996, by rfl⟩ : syracuseStep 10587995 = 15881993) B15881993
theorem B7058663 : Blo 2091435 7058663 := bstep (se 1 (by rfl) ⟨5293997, by rfl⟩ : syracuseStep 7058663 = 10587995) B10587995
theorem B4705775 : Blo 2091435 4705775 := bstep (se 1 (by rfl) ⟨3529331, by rfl⟩ : syracuseStep 4705775 = 7058663) B7058663
theorem B3137183 : Blo 2091435 3137183 := bstep (se 1 (by rfl) ⟨2352887, by rfl⟩ : syracuseStep 3137183 = 4705775) B4705775
theorem B2091455 : Blo 2091435 2091455 := bstep (se 1 (by rfl) ⟨1568591, by rfl⟩ : syracuseStep 2091455 = 3137183) B3137183
theorem B3137189 : Blo 2091435 3137189 := bbase (se 4 (by rfl) ⟨294111, by rfl⟩ : syracuseStep 3137189 = 588223) (by norm_num)
theorem B2091459 : Blo 2091435 2091459 := bstep (se 1 (by rfl) ⟨1568594, by rfl⟩ : syracuseStep 2091459 = 3137189) B3137189
theorem B2647009 : Blo 2091435 2647009 := bbase (se 2 (by rfl) ⟨992628, by rfl⟩ : syracuseStep 2647009 = 1985257) (by norm_num)
theorem B3529345 : Blo 2091435 3529345 := bstep (se 2 (by rfl) ⟨1323504, by rfl⟩ : syracuseStep 3529345 = 2647009) B2647009
theorem B4705793 : Blo 2091435 4705793 := bstep (se 2 (by rfl) ⟨1764672, by rfl⟩ : syracuseStep 4705793 = 3529345) B3529345
theorem B3137195 : Blo 2091435 3137195 := bstep (se 1 (by rfl) ⟨2352896, by rfl⟩ : syracuseStep 3137195 = 4705793) B4705793
theorem B2091463 : Blo 2091435 2091463 := bstep (se 1 (by rfl) ⟨1568597, by rfl⟩ : syracuseStep 2091463 = 3137195) B3137195
theorem B2352901 : Blo 2091435 2352901 := bbase (se 4 (by rfl) ⟨220584, by rfl⟩ : syracuseStep 2352901 = 441169) (by norm_num)
theorem B3137201 : Blo 2091435 3137201 := bstep (se 2 (by rfl) ⟨1176450, by rfl⟩ : syracuseStep 3137201 = 2352901) B2352901
theorem B2091467 : Blo 2091435 2091467 := bstep (se 1 (by rfl) ⟨1568600, by rfl⟩ : syracuseStep 2091467 = 3137201) B3137201
theorem B2826677 : Blo 2091435 2826677 := bbase (se 5 (by rfl) ⟨132500, by rfl⟩ : syracuseStep 2826677 = 265001) (by norm_num)
theorem B7537805 : Blo 2091435 7537805 := bstep (se 3 (by rfl) ⟨1413338, by rfl⟩ : syracuseStep 7537805 = 2826677) B2826677
theorem B5025203 : Blo 2091435 5025203 := bstep (se 1 (by rfl) ⟨3768902, by rfl⟩ : syracuseStep 5025203 = 7537805) B7537805
theorem B3350135 : Blo 2091435 3350135 := bstep (se 1 (by rfl) ⟨2512601, by rfl⟩ : syracuseStep 3350135 = 5025203) B5025203
theorem B2233423 : Blo 2091435 2233423 := bstep (se 1 (by rfl) ⟨1675067, by rfl⟩ : syracuseStep 2233423 = 3350135) B3350135
theorem B2977897 : Blo 2091435 2977897 := bstep (se 2 (by rfl) ⟨1116711, by rfl⟩ : syracuseStep 2977897 = 2233423) B2233423
theorem B3970529 : Blo 2091435 3970529 := bstep (se 2 (by rfl) ⟨1488948, by rfl⟩ : syracuseStep 3970529 = 2977897) B2977897
theorem B2647019 : Blo 2091435 2647019 := bstep (se 1 (by rfl) ⟨1985264, by rfl⟩ : syracuseStep 2647019 = 3970529) B3970529
theorem B7058717 : Blo 2091435 7058717 := bstep (se 3 (by rfl) ⟨1323509, by rfl⟩ : syracuseStep 7058717 = 2647019) B2647019
theorem B4705811 : Blo 2091435 4705811 := bstep (se 1 (by rfl) ⟨3529358, by rfl⟩ : syracuseStep 4705811 = 7058717) B7058717
theorem B3137207 : Blo 2091435 3137207 := bstep (se 1 (by rfl) ⟨2352905, by rfl⟩ : syracuseStep 3137207 = 4705811) B4705811
theorem B2091471 : Blo 2091435 2091471 := bstep (se 1 (by rfl) ⟨1568603, by rfl⟩ : syracuseStep 2091471 = 3137207) B3137207
theorem B3137213 : Blo 2091435 3137213 := bbase (se 3 (by rfl) ⟨588227, by rfl⟩ : syracuseStep 3137213 = 1176455) (by norm_num)
theorem B2091475 : Blo 2091435 2091475 := bstep (se 1 (by rfl) ⟨1568606, by rfl⟩ : syracuseStep 2091475 = 3137213) B3137213
theorem B4705829 : Blo 2091435 4705829 := bbase (se 4 (by rfl) ⟨441171, by rfl⟩ : syracuseStep 4705829 = 882343) (by norm_num)
theorem B3137219 : Blo 2091435 3137219 := bstep (se 1 (by rfl) ⟨2352914, by rfl⟩ : syracuseStep 3137219 = 4705829) B4705829
theorem B2091479 : Blo 2091435 2091479 := bstep (se 1 (by rfl) ⟨1568609, by rfl⟩ : syracuseStep 2091479 = 3137219) B3137219
theorem B5294069 : Blo 2091435 5294069 := bbase (se 5 (by rfl) ⟨248159, by rfl⟩ : syracuseStep 5294069 = 496319) (by norm_num)
theorem B3529379 : Blo 2091435 3529379 := bstep (se 1 (by rfl) ⟨2647034, by rfl⟩ : syracuseStep 3529379 = 5294069) B5294069
theorem B2352919 : Blo 2091435 2352919 := bstep (se 1 (by rfl) ⟨1764689, by rfl⟩ : syracuseStep 2352919 = 3529379) B3529379
theorem B3137225 : Blo 2091435 3137225 := bstep (se 2 (by rfl) ⟨1176459, by rfl⟩ : syracuseStep 3137225 = 2352919) B2352919
theorem B2091483 : Blo 2091435 2091483 := bstep (se 1 (by rfl) ⟨1568612, by rfl⟩ : syracuseStep 2091483 = 3137225) B3137225
theorem B101761109 : Blo 2091435 101761109 := bbase (se 8 (by rfl) ⟨596256, by rfl⟩ : syracuseStep 101761109 = 1192513) (by norm_num)
theorem B67840739 : Blo 2091435 67840739 := bstep (se 1 (by rfl) ⟨50880554, by rfl⟩ : syracuseStep 67840739 = 101761109) B101761109
theorem B45227159 : Blo 2091435 45227159 := bstep (se 1 (by rfl) ⟨33920369, by rfl⟩ : syracuseStep 45227159 = 67840739) B67840739
theorem B30151439 : Blo 2091435 30151439 := bstep (se 1 (by rfl) ⟨22613579, by rfl⟩ : syracuseStep 30151439 = 45227159) B45227159
theorem B20100959 : Blo 2091435 20100959 := bstep (se 1 (by rfl) ⟨15075719, by rfl⟩ : syracuseStep 20100959 = 30151439) B30151439
theorem B13400639 : Blo 2091435 13400639 := bstep (se 1 (by rfl) ⟨10050479, by rfl⟩ : syracuseStep 13400639 = 20100959) B20100959
theorem B8933759 : Blo 2091435 8933759 := bstep (se 1 (by rfl) ⟨6700319, by rfl⟩ : syracuseStep 8933759 = 13400639) B13400639
theorem B5955839 : Blo 2091435 5955839 := bstep (se 1 (by rfl) ⟨4466879, by rfl⟩ : syracuseStep 5955839 = 8933759) B8933759
theorem B3970559 : Blo 2091435 3970559 := bstep (se 1 (by rfl) ⟨2977919, by rfl⟩ : syracuseStep 3970559 = 5955839) B5955839
theorem B10588157 : Blo 2091435 10588157 := bstep (se 3 (by rfl) ⟨1985279, by rfl⟩ : syracuseStep 10588157 = 3970559) B3970559
theorem B7058771 : Blo 2091435 7058771 := bstep (se 1 (by rfl) ⟨5294078, by rfl⟩ : syracuseStep 7058771 = 10588157) B10588157
theorem B4705847 : Blo 2091435 4705847 := bstep (se 1 (by rfl) ⟨3529385, by rfl⟩ : syracuseStep 4705847 = 7058771) B7058771
theorem B3137231 : Blo 2091435 3137231 := bstep (se 1 (by rfl) ⟨2352923, by rfl⟩ : syracuseStep 3137231 = 4705847) B4705847
theorem B2091487 : Blo 2091435 2091487 := bstep (se 1 (by rfl) ⟨1568615, by rfl⟩ : syracuseStep 2091487 = 3137231) B3137231
theorem B3137237 : Blo 2091435 3137237 := bbase (se 7 (by rfl) ⟨36764, by rfl⟩ : syracuseStep 3137237 = 73529) (by norm_num)
theorem B2091491 : Blo 2091435 2091491 := bstep (se 1 (by rfl) ⟨1568618, by rfl⟩ : syracuseStep 2091491 = 3137237) B3137237
theorem B3350173 : Blo 2091435 3350173 := bbase (se 3 (by rfl) ⟨628157, by rfl⟩ : syracuseStep 3350173 = 1256315) (by norm_num)
theorem B4466897 : Blo 2091435 4466897 := bstep (se 2 (by rfl) ⟨1675086, by rfl⟩ : syracuseStep 4466897 = 3350173) B3350173
theorem B2977931 : Blo 2091435 2977931 := bstep (se 1 (by rfl) ⟨2233448, by rfl⟩ : syracuseStep 2977931 = 4466897) B4466897
theorem B7941149 : Blo 2091435 7941149 := bstep (se 3 (by rfl) ⟨1488965, by rfl⟩ : syracuseStep 7941149 = 2977931) B2977931
theorem B5294099 : Blo 2091435 5294099 := bstep (se 1 (by rfl) ⟨3970574, by rfl⟩ : syracuseStep 5294099 = 7941149) B7941149
theorem B3529399 : Blo 2091435 3529399 := bstep (se 1 (by rfl) ⟨2647049, by rfl⟩ : syracuseStep 3529399 = 5294099) B5294099
theorem B4705865 : Blo 2091435 4705865 := bstep (se 2 (by rfl) ⟨1764699, by rfl⟩ : syracuseStep 4705865 = 3529399) B3529399
theorem B3137243 : Blo 2091435 3137243 := bstep (se 1 (by rfl) ⟨2352932, by rfl⟩ : syracuseStep 3137243 = 4705865) B4705865
theorem B2091495 : Blo 2091435 2091495 := bstep (se 1 (by rfl) ⟨1568621, by rfl⟩ : syracuseStep 2091495 = 3137243) B3137243
theorem B2352937 : Blo 2091435 2352937 := bbase (se 2 (by rfl) ⟨882351, by rfl⟩ : syracuseStep 2352937 = 1764703) (by norm_num)
theorem B3137249 : Blo 2091435 3137249 := bstep (se 2 (by rfl) ⟨1176468, by rfl⟩ : syracuseStep 3137249 = 2352937) B2352937
theorem B2091499 : Blo 2091435 2091499 := bstep (se 1 (by rfl) ⟨1568624, by rfl⟩ : syracuseStep 2091499 = 3137249) B3137249
theorem B3820381 : Blo 2091435 3820381 := bbase (se 3 (by rfl) ⟨716321, by rfl⟩ : syracuseStep 3820381 = 1432643) (by norm_num)
theorem B81501461 : Blo 2091435 81501461 := bstep (se 6 (by rfl) ⟨1910190, by rfl⟩ : syracuseStep 81501461 = 3820381) B3820381
theorem B54334307 : Blo 2091435 54334307 := bstep (se 1 (by rfl) ⟨40750730, by rfl⟩ : syracuseStep 54334307 = 81501461) B81501461
theorem B36222871 : Blo 2091435 36222871 := bstep (se 1 (by rfl) ⟨27167153, by rfl⟩ : syracuseStep 36222871 = 54334307) B54334307
theorem B48297161 : Blo 2091435 48297161 := bstep (se 2 (by rfl) ⟨18111435, by rfl⟩ : syracuseStep 48297161 = 36222871) B36222871
theorem B32198107 : Blo 2091435 32198107 := bstep (se 1 (by rfl) ⟨24148580, by rfl⟩ : syracuseStep 32198107 = 48297161) B48297161
theorem B42930809 : Blo 2091435 42930809 := bstep (se 2 (by rfl) ⟨16099053, by rfl⟩ : syracuseStep 42930809 = 32198107) B32198107
theorem B28620539 : Blo 2091435 28620539 := bstep (se 1 (by rfl) ⟨21465404, by rfl⟩ : syracuseStep 28620539 = 42930809) B42930809
theorem B19080359 : Blo 2091435 19080359 := bstep (se 1 (by rfl) ⟨14310269, by rfl⟩ : syracuseStep 19080359 = 28620539) B28620539
theorem B12720239 : Blo 2091435 12720239 := bstep (se 1 (by rfl) ⟨9540179, by rfl⟩ : syracuseStep 12720239 = 19080359) B19080359
theorem B8480159 : Blo 2091435 8480159 := bstep (se 1 (by rfl) ⟨6360119, by rfl⟩ : syracuseStep 8480159 = 12720239) B12720239
theorem B5653439 : Blo 2091435 5653439 := bstep (se 1 (by rfl) ⟨4240079, by rfl⟩ : syracuseStep 5653439 = 8480159) B8480159
theorem B3768959 : Blo 2091435 3768959 := bstep (se 1 (by rfl) ⟨2826719, by rfl⟩ : syracuseStep 3768959 = 5653439) B5653439
theorem B2512639 : Blo 2091435 2512639 := bstep (se 1 (by rfl) ⟨1884479, by rfl⟩ : syracuseStep 2512639 = 3768959) B3768959
theorem B13400741 : Blo 2091435 13400741 := bstep (se 4 (by rfl) ⟨1256319, by rfl⟩ : syracuseStep 13400741 = 2512639) B2512639
theorem B8933827 : Blo 2091435 8933827 := bstep (se 1 (by rfl) ⟨6700370, by rfl⟩ : syracuseStep 8933827 = 13400741) B13400741
theorem B11911769 : Blo 2091435 11911769 := bstep (se 2 (by rfl) ⟨4466913, by rfl⟩ : syracuseStep 11911769 = 8933827) B8933827
theorem B7941179 : Blo 2091435 7941179 := bstep (se 1 (by rfl) ⟨5955884, by rfl⟩ : syracuseStep 7941179 = 11911769) B11911769
theorem B5294119 : Blo 2091435 5294119 := bstep (se 1 (by rfl) ⟨3970589, by rfl⟩ : syracuseStep 5294119 = 7941179) B7941179
theorem B7058825 : Blo 2091435 7058825 := bstep (se 2 (by rfl) ⟨2647059, by rfl⟩ : syracuseStep 7058825 = 5294119) B5294119
theorem B4705883 : Blo 2091435 4705883 := bstep (se 1 (by rfl) ⟨3529412, by rfl⟩ : syracuseStep 4705883 = 7058825) B7058825
theorem B3137255 : Blo 2091435 3137255 := bstep (se 1 (by rfl) ⟨2352941, by rfl⟩ : syracuseStep 3137255 = 4705883) B4705883
theorem B2091503 : Blo 2091435 2091503 := bstep (se 1 (by rfl) ⟨1568627, by rfl⟩ : syracuseStep 2091503 = 3137255) B3137255
theorem B3137261 : Blo 2091435 3137261 := bbase (se 3 (by rfl) ⟨588236, by rfl⟩ : syracuseStep 3137261 = 1176473) (by norm_num)
theorem B2091507 : Blo 2091435 2091507 := bstep (se 1 (by rfl) ⟨1568630, by rfl⟩ : syracuseStep 2091507 = 3137261) B3137261
theorem B4705901 : Blo 2091435 4705901 := bbase (se 3 (by rfl) ⟨882356, by rfl⟩ : syracuseStep 4705901 = 1764713) (by norm_num)
theorem B3137267 : Blo 2091435 3137267 := bstep (se 1 (by rfl) ⟨2352950, by rfl⟩ : syracuseStep 3137267 = 4705901) B4705901
theorem B2091511 : Blo 2091435 2091511 := bstep (se 1 (by rfl) ⟨1568633, by rfl⟩ : syracuseStep 2091511 = 3137267) B3137267
theorem B3970613 : Blo 2091435 3970613 := bbase (se 5 (by rfl) ⟨186122, by rfl⟩ : syracuseStep 3970613 = 372245) (by norm_num)
theorem B2647075 : Blo 2091435 2647075 := bstep (se 1 (by rfl) ⟨1985306, by rfl⟩ : syracuseStep 2647075 = 3970613) B3970613
theorem B3529433 : Blo 2091435 3529433 := bstep (se 2 (by rfl) ⟨1323537, by rfl⟩ : syracuseStep 3529433 = 2647075) B2647075
theorem B2352955 : Blo 2091435 2352955 := bstep (se 1 (by rfl) ⟨1764716, by rfl⟩ : syracuseStep 2352955 = 3529433) B3529433
theorem B3137273 : Blo 2091435 3137273 := bstep (se 2 (by rfl) ⟨1176477, by rfl⟩ : syracuseStep 3137273 = 2352955) B2352955
theorem B2091515 : Blo 2091435 2091515 := bstep (se 1 (by rfl) ⟨1568636, by rfl⟩ : syracuseStep 2091515 = 3137273) B3137273
theorem B22922453 : Blo 2091435 22922453 := bbase (se 7 (by rfl) ⟨268622, by rfl⟩ : syracuseStep 22922453 = 537245) (by norm_num)
theorem B15281635 : Blo 2091435 15281635 := bstep (se 1 (by rfl) ⟨11461226, by rfl⟩ : syracuseStep 15281635 = 22922453) B22922453
theorem B20375513 : Blo 2091435 20375513 := bstep (se 2 (by rfl) ⟨7640817, by rfl⟩ : syracuseStep 20375513 = 15281635) B15281635
theorem B13583675 : Blo 2091435 13583675 := bstep (se 1 (by rfl) ⟨10187756, by rfl⟩ : syracuseStep 13583675 = 20375513) B20375513
theorem B9055783 : Blo 2091435 9055783 := bstep (se 1 (by rfl) ⟨6791837, by rfl⟩ : syracuseStep 9055783 = 13583675) B13583675
theorem B48297509 : Blo 2091435 48297509 := bstep (se 4 (by rfl) ⟨4527891, by rfl⟩ : syracuseStep 48297509 = 9055783) B9055783
theorem B32198339 : Blo 2091435 32198339 := bstep (se 1 (by rfl) ⟨24148754, by rfl⟩ : syracuseStep 32198339 = 48297509) B48297509
theorem B21465559 : Blo 2091435 21465559 := bstep (se 1 (by rfl) ⟨16099169, by rfl⟩ : syracuseStep 21465559 = 32198339) B32198339
theorem B28620745 : Blo 2091435 28620745 := bstep (se 2 (by rfl) ⟨10732779, by rfl⟩ : syracuseStep 28620745 = 21465559) B21465559
theorem B152643973 : Blo 2091435 152643973 := bstep (se 4 (by rfl) ⟨14310372, by rfl⟩ : syracuseStep 152643973 = 28620745) B28620745
theorem B203525297 : Blo 2091435 203525297 := bstep (se 2 (by rfl) ⟨76321986, by rfl⟩ : syracuseStep 203525297 = 152643973) B152643973
theorem B135683531 : Blo 2091435 135683531 := bstep (se 1 (by rfl) ⟨101762648, by rfl⟩ : syracuseStep 135683531 = 203525297) B203525297
theorem B90455687 : Blo 2091435 90455687 := bstep (se 1 (by rfl) ⟨67841765, by rfl⟩ : syracuseStep 90455687 = 135683531) B135683531
theorem B60303791 : Blo 2091435 60303791 := bstep (se 1 (by rfl) ⟨45227843, by rfl⟩ : syracuseStep 60303791 = 90455687) B90455687
theorem B40202527 : Blo 2091435 40202527 := bstep (se 1 (by rfl) ⟨30151895, by rfl⟩ : syracuseStep 40202527 = 60303791) B60303791
theorem B53603369 : Blo 2091435 53603369 := bstep (se 2 (by rfl) ⟨20101263, by rfl⟩ : syracuseStep 53603369 = 40202527) B40202527
theorem B35735579 : Blo 2091435 35735579 := bstep (se 1 (by rfl) ⟨26801684, by rfl⟩ : syracuseStep 35735579 = 53603369) B53603369
theorem B23823719 : Blo 2091435 23823719 := bstep (se 1 (by rfl) ⟨17867789, by rfl⟩ : syracuseStep 23823719 = 35735579) B35735579
theorem B15882479 : Blo 2091435 15882479 := bstep (se 1 (by rfl) ⟨11911859, by rfl⟩ : syracuseStep 15882479 = 23823719) B23823719
theorem B10588319 : Blo 2091435 10588319 := bstep (se 1 (by rfl) ⟨7941239, by rfl⟩ : syracuseStep 10588319 = 15882479) B15882479
theorem B7058879 : Blo 2091435 7058879 := bstep (se 1 (by rfl) ⟨5294159, by rfl⟩ : syracuseStep 7058879 = 10588319) B10588319
theorem B4705919 : Blo 2091435 4705919 := bstep (se 1 (by rfl) ⟨3529439, by rfl⟩ : syracuseStep 4705919 = 7058879) B7058879
theorem B3137279 : Blo 2091435 3137279 := bstep (se 1 (by rfl) ⟨2352959, by rfl⟩ : syracuseStep 3137279 = 4705919) B4705919
theorem B2091519 : Blo 2091435 2091519 := bstep (se 1 (by rfl) ⟨1568639, by rfl⟩ : syracuseStep 2091519 = 3137279) B3137279
theorem B3137285 : Blo 2091435 3137285 := bbase (se 4 (by rfl) ⟨294120, by rfl⟩ : syracuseStep 3137285 = 588241) (by norm_num)
theorem B2091523 : Blo 2091435 2091523 := bstep (se 1 (by rfl) ⟨1568642, by rfl⟩ : syracuseStep 2091523 = 3137285) B3137285
theorem B3529453 : Blo 2091435 3529453 := bbase (se 3 (by rfl) ⟨661772, by rfl⟩ : syracuseStep 3529453 = 1323545) (by norm_num)
theorem B4705937 : Blo 2091435 4705937 := bstep (se 2 (by rfl) ⟨1764726, by rfl⟩ : syracuseStep 4705937 = 3529453) B3529453
theorem B3137291 : Blo 2091435 3137291 := bstep (se 1 (by rfl) ⟨2352968, by rfl⟩ : syracuseStep 3137291 = 4705937) B4705937
theorem B2091527 : Blo 2091435 2091527 := bstep (se 1 (by rfl) ⟨1568645, by rfl⟩ : syracuseStep 2091527 = 3137291) B3137291
theorem B2352973 : Blo 2091435 2352973 := bbase (se 3 (by rfl) ⟨441182, by rfl⟩ : syracuseStep 2352973 = 882365) (by norm_num)
theorem B3137297 : Blo 2091435 3137297 := bstep (se 2 (by rfl) ⟨1176486, by rfl⟩ : syracuseStep 3137297 = 2352973) B2352973
theorem B2091531 : Blo 2091435 2091531 := bstep (se 1 (by rfl) ⟨1568648, by rfl⟩ : syracuseStep 2091531 = 3137297) B3137297
theorem B7058933 : Blo 2091435 7058933 := bbase (se 5 (by rfl) ⟨330887, by rfl⟩ : syracuseStep 7058933 = 661775) (by norm_num)
theorem B4705955 : Blo 2091435 4705955 := bstep (se 1 (by rfl) ⟨3529466, by rfl⟩ : syracuseStep 4705955 = 7058933) B7058933
theorem B3137303 : Blo 2091435 3137303 := bstep (se 1 (by rfl) ⟨2352977, by rfl⟩ : syracuseStep 3137303 = 4705955) B4705955
theorem B2091535 : Blo 2091435 2091535 := bstep (se 1 (by rfl) ⟨1568651, by rfl⟩ : syracuseStep 2091535 = 3137303) B3137303
theorem B3137309 : Blo 2091435 3137309 := bbase (se 3 (by rfl) ⟨588245, by rfl⟩ : syracuseStep 3137309 = 1176491) (by norm_num)
theorem B2091539 : Blo 2091435 2091539 := bstep (se 1 (by rfl) ⟨1568654, by rfl⟩ : syracuseStep 2091539 = 3137309) B3137309
theorem B4705973 : Blo 2091435 4705973 := bbase (se 5 (by rfl) ⟨220592, by rfl⟩ : syracuseStep 4705973 = 441185) (by norm_num)
theorem B3137315 : Blo 2091435 3137315 := bstep (se 1 (by rfl) ⟨2352986, by rfl⟩ : syracuseStep 3137315 = 4705973) B4705973
theorem B2091543 : Blo 2091435 2091543 := bstep (se 1 (by rfl) ⟨1568657, by rfl⟩ : syracuseStep 2091543 = 3137315) B3137315
theorem B11912021 : Blo 2091435 11912021 := bbase (se 9 (by rfl) ⟨34898, by rfl⟩ : syracuseStep 11912021 = 69797) (by norm_num)
theorem B7941347 : Blo 2091435 7941347 := bstep (se 1 (by rfl) ⟨5956010, by rfl⟩ : syracuseStep 7941347 = 11912021) B11912021
theorem B5294231 : Blo 2091435 5294231 := bstep (se 1 (by rfl) ⟨3970673, by rfl⟩ : syracuseStep 5294231 = 7941347) B7941347
theorem B3529487 : Blo 2091435 3529487 := bstep (se 1 (by rfl) ⟨2647115, by rfl⟩ : syracuseStep 3529487 = 5294231) B5294231
theorem B2352991 : Blo 2091435 2352991 := bstep (se 1 (by rfl) ⟨1764743, by rfl⟩ : syracuseStep 2352991 = 3529487) B3529487
theorem B3137321 : Blo 2091435 3137321 := bstep (se 2 (by rfl) ⟨1176495, by rfl⟩ : syracuseStep 3137321 = 2352991) B2352991
theorem B2091547 : Blo 2091435 2091547 := bstep (se 1 (by rfl) ⟨1568660, by rfl⟩ : syracuseStep 2091547 = 3137321) B3137321
theorem B5956021 : Blo 2091435 5956021 := bbase (se 5 (by rfl) ⟨279188, by rfl⟩ : syracuseStep 5956021 = 558377) (by norm_num)
theorem B7941361 : Blo 2091435 7941361 := bstep (se 2 (by rfl) ⟨2978010, by rfl⟩ : syracuseStep 7941361 = 5956021) B5956021
theorem B10588481 : Blo 2091435 10588481 := bstep (se 2 (by rfl) ⟨3970680, by rfl⟩ : syracuseStep 10588481 = 7941361) B7941361
theorem B7058987 : Blo 2091435 7058987 := bstep (se 1 (by rfl) ⟨5294240, by rfl⟩ : syracuseStep 7058987 = 10588481) B10588481
theorem B4705991 : Blo 2091435 4705991 := bstep (se 1 (by rfl) ⟨3529493, by rfl⟩ : syracuseStep 4705991 = 7058987) B7058987
theorem B3137327 : Blo 2091435 3137327 := bstep (se 1 (by rfl) ⟨2352995, by rfl⟩ : syracuseStep 3137327 = 4705991) B4705991
theorem B2091551 : Blo 2091435 2091551 := bstep (se 1 (by rfl) ⟨1568663, by rfl⟩ : syracuseStep 2091551 = 3137327) B3137327
theorem B3137333 : Blo 2091435 3137333 := bbase (se 5 (by rfl) ⟨147062, by rfl⟩ : syracuseStep 3137333 = 294125) (by norm_num)
theorem B2091555 : Blo 2091435 2091555 := bstep (se 1 (by rfl) ⟨1568666, by rfl⟩ : syracuseStep 2091555 = 3137333) B3137333
theorem B5294261 : Blo 2091435 5294261 := bbase (se 5 (by rfl) ⟨248168, by rfl⟩ : syracuseStep 5294261 = 496337) (by norm_num)
theorem B3529507 : Blo 2091435 3529507 := bstep (se 1 (by rfl) ⟨2647130, by rfl⟩ : syracuseStep 3529507 = 5294261) B5294261
theorem B4706009 : Blo 2091435 4706009 := bstep (se 2 (by rfl) ⟨1764753, by rfl⟩ : syracuseStep 4706009 = 3529507) B3529507
theorem B3137339 : Blo 2091435 3137339 := bstep (se 1 (by rfl) ⟨2353004, by rfl⟩ : syracuseStep 3137339 = 4706009) B4706009
theorem B2091559 : Blo 2091435 2091559 := bstep (se 1 (by rfl) ⟨1568669, by rfl⟩ : syracuseStep 2091559 = 3137339) B3137339
theorem B2353009 : Blo 2091435 2353009 := bbase (se 2 (by rfl) ⟨882378, by rfl⟩ : syracuseStep 2353009 = 1764757) (by norm_num)
theorem B3137345 : Blo 2091435 3137345 := bstep (se 2 (by rfl) ⟨1176504, by rfl⟩ : syracuseStep 3137345 = 2353009) B2353009
theorem B2091563 : Blo 2091435 2091563 := bstep (se 1 (by rfl) ⟨1568672, by rfl⟩ : syracuseStep 2091563 = 3137345) B3137345
theorem B8934101 : Blo 2091435 8934101 := bbase (se 7 (by rfl) ⟨104696, by rfl⟩ : syracuseStep 8934101 = 209393) (by norm_num)
theorem B5956067 : Blo 2091435 5956067 := bstep (se 1 (by rfl) ⟨4467050, by rfl⟩ : syracuseStep 5956067 = 8934101) B8934101
theorem B3970711 : Blo 2091435 3970711 := bstep (se 1 (by rfl) ⟨2978033, by rfl⟩ : syracuseStep 3970711 = 5956067) B5956067
theorem B5294281 : Blo 2091435 5294281 := bstep (se 2 (by rfl) ⟨1985355, by rfl⟩ : syracuseStep 5294281 = 3970711) B3970711
theorem B7059041 : Blo 2091435 7059041 := bstep (se 2 (by rfl) ⟨2647140, by rfl⟩ : syracuseStep 7059041 = 5294281) B5294281
theorem B4706027 : Blo 2091435 4706027 := bstep (se 1 (by rfl) ⟨3529520, by rfl⟩ : syracuseStep 4706027 = 7059041) B7059041
theorem B3137351 : Blo 2091435 3137351 := bstep (se 1 (by rfl) ⟨2353013, by rfl⟩ : syracuseStep 3137351 = 4706027) B4706027
theorem B2091567 : Blo 2091435 2091567 := bstep (se 1 (by rfl) ⟨1568675, by rfl⟩ : syracuseStep 2091567 = 3137351) B3137351
theorem B3137357 : Blo 2091435 3137357 := bbase (se 3 (by rfl) ⟨588254, by rfl⟩ : syracuseStep 3137357 = 1176509) (by norm_num)
theorem B2091571 : Blo 2091435 2091571 := bstep (se 1 (by rfl) ⟨1568678, by rfl⟩ : syracuseStep 2091571 = 3137357) B3137357
theorem B4706045 : Blo 2091435 4706045 := bbase (se 3 (by rfl) ⟨882383, by rfl⟩ : syracuseStep 4706045 = 1764767) (by norm_num)
theorem B3137363 : Blo 2091435 3137363 := bstep (se 1 (by rfl) ⟨2353022, by rfl⟩ : syracuseStep 3137363 = 4706045) B4706045
theorem B2091575 : Blo 2091435 2091575 := bstep (se 1 (by rfl) ⟨1568681, by rfl⟩ : syracuseStep 2091575 = 3137363) B3137363
theorem B3529541 : Blo 2091435 3529541 := bbase (se 4 (by rfl) ⟨330894, by rfl⟩ : syracuseStep 3529541 = 661789) (by norm_num)
theorem B2353027 : Blo 2091435 2353027 := bstep (se 1 (by rfl) ⟨1764770, by rfl⟩ : syracuseStep 2353027 = 3529541) B3529541
theorem B3137369 : Blo 2091435 3137369 := bstep (se 2 (by rfl) ⟨1176513, by rfl⟩ : syracuseStep 3137369 = 2353027) B2353027
theorem B2091579 : Blo 2091435 2091579 := bstep (se 1 (by rfl) ⟨1568684, by rfl⟩ : syracuseStep 2091579 = 3137369) B3137369
theorem B15882965 : Blo 2091435 15882965 := bbase (se 7 (by rfl) ⟨186128, by rfl⟩ : syracuseStep 15882965 = 372257) (by norm_num)
theorem B10588643 : Blo 2091435 10588643 := bstep (se 1 (by rfl) ⟨7941482, by rfl⟩ : syracuseStep 10588643 = 15882965) B15882965
theorem B7059095 : Blo 2091435 7059095 := bstep (se 1 (by rfl) ⟨5294321, by rfl⟩ : syracuseStep 7059095 = 10588643) B10588643
theorem B4706063 : Blo 2091435 4706063 := bstep (se 1 (by rfl) ⟨3529547, by rfl⟩ : syracuseStep 4706063 = 7059095) B7059095
theorem B3137375 : Blo 2091435 3137375 := bstep (se 1 (by rfl) ⟨2353031, by rfl⟩ : syracuseStep 3137375 = 4706063) B4706063
theorem B2091583 : Blo 2091435 2091583 := bstep (se 1 (by rfl) ⟨1568687, by rfl⟩ : syracuseStep 2091583 = 3137375) B3137375
theorem B3137381 : Blo 2091435 3137381 := bbase (se 4 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 3137381 = 588259) (by norm_num)
theorem B2091587 : Blo 2091435 2091587 := bstep (se 1 (by rfl) ⟨1568690, by rfl⟩ : syracuseStep 2091587 = 3137381) B3137381
theorem B3970757 : Blo 2091435 3970757 := bbase (se 4 (by rfl) ⟨372258, by rfl⟩ : syracuseStep 3970757 = 744517) (by norm_num)
theorem B2647171 : Blo 2091435 2647171 := bstep (se 1 (by rfl) ⟨1985378, by rfl⟩ : syracuseStep 2647171 = 3970757) B3970757
theorem B3529561 : Blo 2091435 3529561 := bstep (se 2 (by rfl) ⟨1323585, by rfl⟩ : syracuseStep 3529561 = 2647171) B2647171
theorem B4706081 : Blo 2091435 4706081 := bstep (se 2 (by rfl) ⟨1764780, by rfl⟩ : syracuseStep 4706081 = 3529561) B3529561
theorem B3137387 : Blo 2091435 3137387 := bstep (se 1 (by rfl) ⟨2353040, by rfl⟩ : syracuseStep 3137387 = 4706081) B4706081
theorem B2091591 : Blo 2091435 2091591 := bstep (se 1 (by rfl) ⟨1568693, by rfl⟩ : syracuseStep 2091591 = 3137387) B3137387
theorem B2353045 : Blo 2091435 2353045 := bbase (se 6 (by rfl) ⟨55149, by rfl⟩ : syracuseStep 2353045 = 110299) (by norm_num)
theorem B3137393 : Blo 2091435 3137393 := bstep (se 2 (by rfl) ⟨1176522, by rfl⟩ : syracuseStep 3137393 = 2353045) B2353045
theorem B2091595 : Blo 2091435 2091595 := bstep (se 1 (by rfl) ⟨1568696, by rfl⟩ : syracuseStep 2091595 = 3137393) B3137393
theorem B2647181 : Blo 2091435 2647181 := bbase (se 3 (by rfl) ⟨496346, by rfl⟩ : syracuseStep 2647181 = 992693) (by norm_num)
theorem B7059149 : Blo 2091435 7059149 := bstep (se 3 (by rfl) ⟨1323590, by rfl⟩ : syracuseStep 7059149 = 2647181) B2647181
theorem B4706099 : Blo 2091435 4706099 := bstep (se 1 (by rfl) ⟨3529574, by rfl⟩ : syracuseStep 4706099 = 7059149) B7059149
theorem B3137399 : Blo 2091435 3137399 := bstep (se 1 (by rfl) ⟨2353049, by rfl⟩ : syracuseStep 3137399 = 4706099) B4706099
theorem B2091599 : Blo 2091435 2091599 := bstep (se 1 (by rfl) ⟨1568699, by rfl⟩ : syracuseStep 2091599 = 3137399) B3137399
theorem B3137405 : Blo 2091435 3137405 := bbase (se 3 (by rfl) ⟨588263, by rfl⟩ : syracuseStep 3137405 = 1176527) (by norm_num)
theorem B2091603 : Blo 2091435 2091603 := bstep (se 1 (by rfl) ⟨1568702, by rfl⟩ : syracuseStep 2091603 = 3137405) B3137405
theorem B4706117 : Blo 2091435 4706117 := bbase (se 4 (by rfl) ⟨441198, by rfl⟩ : syracuseStep 4706117 = 882397) (by norm_num)
theorem B3137411 : Blo 2091435 3137411 := bstep (se 1 (by rfl) ⟨2353058, by rfl⟩ : syracuseStep 3137411 = 4706117) B4706117
theorem B2091607 : Blo 2091435 2091607 := bstep (se 1 (by rfl) ⟨1568705, by rfl⟩ : syracuseStep 2091607 = 3137411) B3137411
theorem B7538309 : Blo 2091435 7538309 := bbase (se 4 (by rfl) ⟨706716, by rfl⟩ : syracuseStep 7538309 = 1413433) (by norm_num)
theorem B5025539 : Blo 2091435 5025539 := bstep (se 1 (by rfl) ⟨3769154, by rfl⟩ : syracuseStep 5025539 = 7538309) B7538309
theorem B3350359 : Blo 2091435 3350359 := bstep (se 1 (by rfl) ⟨2512769, by rfl⟩ : syracuseStep 3350359 = 5025539) B5025539
theorem B4467145 : Blo 2091435 4467145 := bstep (se 2 (by rfl) ⟨1675179, by rfl⟩ : syracuseStep 4467145 = 3350359) B3350359
theorem B5956193 : Blo 2091435 5956193 := bstep (se 2 (by rfl) ⟨2233572, by rfl⟩ : syracuseStep 5956193 = 4467145) B4467145
theorem B3970795 : Blo 2091435 3970795 := bstep (se 1 (by rfl) ⟨2978096, by rfl⟩ : syracuseStep 3970795 = 5956193) B5956193
theorem B5294393 : Blo 2091435 5294393 := bstep (se 2 (by rfl) ⟨1985397, by rfl⟩ : syracuseStep 5294393 = 3970795) B3970795
theorem B3529595 : Blo 2091435 3529595 := bstep (se 1 (by rfl) ⟨2647196, by rfl⟩ : syracuseStep 3529595 = 5294393) B5294393
theorem B2353063 : Blo 2091435 2353063 := bstep (se 1 (by rfl) ⟨1764797, by rfl⟩ : syracuseStep 2353063 = 3529595) B3529595
theorem B3137417 : Blo 2091435 3137417 := bstep (se 2 (by rfl) ⟨1176531, by rfl⟩ : syracuseStep 3137417 = 2353063) B2353063
theorem B2091611 : Blo 2091435 2091611 := bstep (se 1 (by rfl) ⟨1568708, by rfl⟩ : syracuseStep 2091611 = 3137417) B3137417
theorem B10588805 : Blo 2091435 10588805 := bbase (se 4 (by rfl) ⟨992700, by rfl⟩ : syracuseStep 10588805 = 1985401) (by norm_num)
theorem B7059203 : Blo 2091435 7059203 := bstep (se 1 (by rfl) ⟨5294402, by rfl⟩ : syracuseStep 7059203 = 10588805) B10588805
theorem B4706135 : Blo 2091435 4706135 := bstep (se 1 (by rfl) ⟨3529601, by rfl⟩ : syracuseStep 4706135 = 7059203) B7059203
theorem B3137423 : Blo 2091435 3137423 := bstep (se 1 (by rfl) ⟨2353067, by rfl⟩ : syracuseStep 3137423 = 4706135) B4706135
theorem B2091615 : Blo 2091435 2091615 := bstep (se 1 (by rfl) ⟨1568711, by rfl⟩ : syracuseStep 2091615 = 3137423) B3137423
theorem B3137429 : Blo 2091435 3137429 := bbase (se 6 (by rfl) ⟨73533, by rfl⟩ : syracuseStep 3137429 = 147067) (by norm_num)
theorem B2091619 : Blo 2091435 2091619 := bstep (se 1 (by rfl) ⟨1568714, by rfl⟩ : syracuseStep 2091619 = 3137429) B3137429
theorem B2233585 : Blo 2091435 2233585 := bbase (se 2 (by rfl) ⟨837594, by rfl⟩ : syracuseStep 2233585 = 1675189) (by norm_num)
theorem B11912453 : Blo 2091435 11912453 := bstep (se 4 (by rfl) ⟨1116792, by rfl⟩ : syracuseStep 11912453 = 2233585) B2233585
theorem B7941635 : Blo 2091435 7941635 := bstep (se 1 (by rfl) ⟨5956226, by rfl⟩ : syracuseStep 7941635 = 11912453) B11912453
theorem B5294423 : Blo 2091435 5294423 := bstep (se 1 (by rfl) ⟨3970817, by rfl⟩ : syracuseStep 5294423 = 7941635) B7941635
theorem B3529615 : Blo 2091435 3529615 := bstep (se 1 (by rfl) ⟨2647211, by rfl⟩ : syracuseStep 3529615 = 5294423) B5294423
theorem B4706153 : Blo 2091435 4706153 := bstep (se 2 (by rfl) ⟨1764807, by rfl⟩ : syracuseStep 4706153 = 3529615) B3529615
theorem B3137435 : Blo 2091435 3137435 := bstep (se 1 (by rfl) ⟨2353076, by rfl⟩ : syracuseStep 3137435 = 4706153) B4706153
theorem B2091623 : Blo 2091435 2091623 := bstep (se 1 (by rfl) ⟨1568717, by rfl⟩ : syracuseStep 2091623 = 3137435) B3137435
theorem B2353081 : Blo 2091435 2353081 := bbase (se 2 (by rfl) ⟨882405, by rfl⟩ : syracuseStep 2353081 = 1764811) (by norm_num)
theorem B3137441 : Blo 2091435 3137441 := bstep (se 2 (by rfl) ⟨1176540, by rfl⟩ : syracuseStep 3137441 = 2353081) B2353081
theorem B2091627 : Blo 2091435 2091627 := bstep (se 1 (by rfl) ⟨1568720, by rfl⟩ : syracuseStep 2091627 = 3137441) B3137441
theorem B2512793 : Blo 2091435 2512793 := bbase (se 2 (by rfl) ⟨942297, by rfl⟩ : syracuseStep 2512793 = 1884595) (by norm_num)
theorem B6700781 : Blo 2091435 6700781 := bstep (se 3 (by rfl) ⟨1256396, by rfl⟩ : syracuseStep 6700781 = 2512793) B2512793
theorem B4467187 : Blo 2091435 4467187 := bstep (se 1 (by rfl) ⟨3350390, by rfl⟩ : syracuseStep 4467187 = 6700781) B6700781
theorem B5956249 : Blo 2091435 5956249 := bstep (se 2 (by rfl) ⟨2233593, by rfl⟩ : syracuseStep 5956249 = 4467187) B4467187
theorem B7941665 : Blo 2091435 7941665 := bstep (se 2 (by rfl) ⟨2978124, by rfl⟩ : syracuseStep 7941665 = 5956249) B5956249
theorem B5294443 : Blo 2091435 5294443 := bstep (se 1 (by rfl) ⟨3970832, by rfl⟩ : syracuseStep 5294443 = 7941665) B7941665
theorem B7059257 : Blo 2091435 7059257 := bstep (se 2 (by rfl) ⟨2647221, by rfl⟩ : syracuseStep 7059257 = 5294443) B5294443
theorem B4706171 : Blo 2091435 4706171 := bstep (se 1 (by rfl) ⟨3529628, by rfl⟩ : syracuseStep 4706171 = 7059257) B7059257
theorem B3137447 : Blo 2091435 3137447 := bstep (se 1 (by rfl) ⟨2353085, by rfl⟩ : syracuseStep 3137447 = 4706171) B4706171
theorem B2091631 : Blo 2091435 2091631 := bstep (se 1 (by rfl) ⟨1568723, by rfl⟩ : syracuseStep 2091631 = 3137447) B3137447
theorem B3137453 : Blo 2091435 3137453 := bbase (se 3 (by rfl) ⟨588272, by rfl⟩ : syracuseStep 3137453 = 1176545) (by norm_num)
theorem B2091635 : Blo 2091435 2091635 := bstep (se 1 (by rfl) ⟨1568726, by rfl⟩ : syracuseStep 2091635 = 3137453) B3137453
theorem B4706189 : Blo 2091435 4706189 := bbase (se 3 (by rfl) ⟨882410, by rfl⟩ : syracuseStep 4706189 = 1764821) (by norm_num)
theorem B3137459 : Blo 2091435 3137459 := bstep (se 1 (by rfl) ⟨2353094, by rfl⟩ : syracuseStep 3137459 = 4706189) B4706189
theorem B2091639 : Blo 2091435 2091639 := bstep (se 1 (by rfl) ⟨1568729, by rfl⟩ : syracuseStep 2091639 = 3137459) B3137459
theorem B2647237 : Blo 2091435 2647237 := bbase (se 4 (by rfl) ⟨248178, by rfl⟩ : syracuseStep 2647237 = 496357) (by norm_num)
theorem B3529649 : Blo 2091435 3529649 := bstep (se 2 (by rfl) ⟨1323618, by rfl⟩ : syracuseStep 3529649 = 2647237) B2647237
theorem B2353099 : Blo 2091435 2353099 := bstep (se 1 (by rfl) ⟨1764824, by rfl⟩ : syracuseStep 2353099 = 3529649) B3529649
theorem B3137465 : Blo 2091435 3137465 := bstep (se 2 (by rfl) ⟨1176549, by rfl⟩ : syracuseStep 3137465 = 2353099) B2353099
theorem B2091643 : Blo 2091435 2091643 := bstep (se 1 (by rfl) ⟨1568732, by rfl⟩ : syracuseStep 2091643 = 3137465) B3137465
theorem B7283621 : Blo 2091435 7283621 := bbase (se 4 (by rfl) ⟨682839, by rfl⟩ : syracuseStep 7283621 = 1365679) (by norm_num)
theorem B19422989 : Blo 2091435 19422989 := bstep (se 3 (by rfl) ⟨3641810, by rfl⟩ : syracuseStep 19422989 = 7283621) B7283621
theorem B12948659 : Blo 2091435 12948659 := bstep (se 1 (by rfl) ⟨9711494, by rfl⟩ : syracuseStep 12948659 = 19422989) B19422989
theorem B8632439 : Blo 2091435 8632439 := bstep (se 1 (by rfl) ⟨6474329, by rfl⟩ : syracuseStep 8632439 = 12948659) B12948659
theorem B5754959 : Blo 2091435 5754959 := bstep (se 1 (by rfl) ⟨4316219, by rfl⟩ : syracuseStep 5754959 = 8632439) B8632439
theorem B3836639 : Blo 2091435 3836639 := bstep (se 1 (by rfl) ⟨2877479, by rfl⟩ : syracuseStep 3836639 = 5754959) B5754959
theorem B2557759 : Blo 2091435 2557759 := bstep (se 1 (by rfl) ⟨1918319, by rfl⟩ : syracuseStep 2557759 = 3836639) B3836639
theorem B3410345 : Blo 2091435 3410345 := bstep (se 2 (by rfl) ⟨1278879, by rfl⟩ : syracuseStep 3410345 = 2557759) B2557759
theorem B2273563 : Blo 2091435 2273563 := bstep (se 1 (by rfl) ⟨1705172, by rfl⟩ : syracuseStep 2273563 = 3410345) B3410345
theorem B3031417 : Blo 2091435 3031417 := bstep (se 2 (by rfl) ⟨1136781, by rfl⟩ : syracuseStep 3031417 = 2273563) B2273563
theorem B16167557 : Blo 2091435 16167557 := bstep (se 4 (by rfl) ⟨1515708, by rfl⟩ : syracuseStep 16167557 = 3031417) B3031417
theorem B43113485 : Blo 2091435 43113485 := bstep (se 3 (by rfl) ⟨8083778, by rfl⟩ : syracuseStep 43113485 = 16167557) B16167557
theorem B114969293 : Blo 2091435 114969293 := bstep (se 3 (by rfl) ⟨21556742, by rfl⟩ : syracuseStep 114969293 = 43113485) B43113485
theorem B76646195 : Blo 2091435 76646195 := bstep (se 1 (by rfl) ⟨57484646, by rfl⟩ : syracuseStep 76646195 = 114969293) B114969293
theorem B51097463 : Blo 2091435 51097463 := bstep (se 1 (by rfl) ⟨38323097, by rfl⟩ : syracuseStep 51097463 = 76646195) B76646195
theorem B34064975 : Blo 2091435 34064975 := bstep (se 1 (by rfl) ⟨25548731, by rfl⟩ : syracuseStep 34064975 = 51097463) B51097463
theorem B22709983 : Blo 2091435 22709983 := bstep (se 1 (by rfl) ⟨17032487, by rfl⟩ : syracuseStep 22709983 = 34064975) B34064975
theorem B30279977 : Blo 2091435 30279977 := bstep (se 2 (by rfl) ⟨11354991, by rfl⟩ : syracuseStep 30279977 = 22709983) B22709983
theorem B20186651 : Blo 2091435 20186651 := bstep (se 1 (by rfl) ⟨15139988, by rfl⟩ : syracuseStep 20186651 = 30279977) B30279977
theorem B13457767 : Blo 2091435 13457767 := bstep (se 1 (by rfl) ⟨10093325, by rfl⟩ : syracuseStep 13457767 = 20186651) B20186651
theorem B17943689 : Blo 2091435 17943689 := bstep (se 2 (by rfl) ⟨6728883, by rfl⟩ : syracuseStep 17943689 = 13457767) B13457767
theorem B11962459 : Blo 2091435 11962459 := bstep (se 1 (by rfl) ⟨8971844, by rfl⟩ : syracuseStep 11962459 = 17943689) B17943689
theorem B15949945 : Blo 2091435 15949945 := bstep (se 2 (by rfl) ⟨5981229, by rfl⟩ : syracuseStep 15949945 = 11962459) B11962459
theorem B21266593 : Blo 2091435 21266593 := bstep (se 2 (by rfl) ⟨7974972, by rfl⟩ : syracuseStep 21266593 = 15949945) B15949945
theorem B113421829 : Blo 2091435 113421829 := bstep (se 4 (by rfl) ⟨10633296, by rfl⟩ : syracuseStep 113421829 = 21266593) B21266593
theorem B151229105 : Blo 2091435 151229105 := bstep (se 2 (by rfl) ⟨56710914, by rfl⟩ : syracuseStep 151229105 = 113421829) B113421829
theorem B100819403 : Blo 2091435 100819403 := bstep (se 1 (by rfl) ⟨75614552, by rfl⟩ : syracuseStep 100819403 = 151229105) B151229105
theorem B67212935 : Blo 2091435 67212935 := bstep (se 1 (by rfl) ⟨50409701, by rfl⟩ : syracuseStep 67212935 = 100819403) B100819403
theorem B44808623 : Blo 2091435 44808623 := bstep (se 1 (by rfl) ⟨33606467, by rfl⟩ : syracuseStep 44808623 = 67212935) B67212935
theorem B29872415 : Blo 2091435 29872415 := bstep (se 1 (by rfl) ⟨22404311, by rfl⟩ : syracuseStep 29872415 = 44808623) B44808623
theorem B19914943 : Blo 2091435 19914943 := bstep (se 1 (by rfl) ⟨14936207, by rfl⟩ : syracuseStep 19914943 = 29872415) B29872415
theorem B26553257 : Blo 2091435 26553257 := bstep (se 2 (by rfl) ⟨9957471, by rfl⟩ : syracuseStep 26553257 = 19914943) B19914943
theorem B17702171 : Blo 2091435 17702171 := bstep (se 1 (by rfl) ⟨13276628, by rfl⟩ : syracuseStep 17702171 = 26553257) B26553257
theorem B11801447 : Blo 2091435 11801447 := bstep (se 1 (by rfl) ⟨8851085, by rfl⟩ : syracuseStep 11801447 = 17702171) B17702171
theorem B7867631 : Blo 2091435 7867631 := bstep (se 1 (by rfl) ⟨5900723, by rfl⟩ : syracuseStep 7867631 = 11801447) B11801447
theorem B5245087 : Blo 2091435 5245087 := bstep (se 1 (by rfl) ⟨3933815, by rfl⟩ : syracuseStep 5245087 = 7867631) B7867631
theorem B6993449 : Blo 2091435 6993449 := bstep (se 2 (by rfl) ⟨2622543, by rfl⟩ : syracuseStep 6993449 = 5245087) B5245087
theorem B4662299 : Blo 2091435 4662299 := bstep (se 1 (by rfl) ⟨3496724, by rfl⟩ : syracuseStep 4662299 = 6993449) B6993449
theorem B12432797 : Blo 2091435 12432797 := bstep (se 3 (by rfl) ⟨2331149, by rfl⟩ : syracuseStep 12432797 = 4662299) B4662299
theorem B8288531 : Blo 2091435 8288531 := bstep (se 1 (by rfl) ⟨6216398, by rfl⟩ : syracuseStep 8288531 = 12432797) B12432797
theorem B5525687 : Blo 2091435 5525687 := bstep (se 1 (by rfl) ⟨4144265, by rfl⟩ : syracuseStep 5525687 = 8288531) B8288531
theorem B3683791 : Blo 2091435 3683791 := bstep (se 1 (by rfl) ⟨2762843, by rfl⟩ : syracuseStep 3683791 = 5525687) B5525687
theorem B4911721 : Blo 2091435 4911721 := bstep (se 2 (by rfl) ⟨1841895, by rfl⟩ : syracuseStep 4911721 = 3683791) B3683791
theorem B26195845 : Blo 2091435 26195845 := bstep (se 4 (by rfl) ⟨2455860, by rfl⟩ : syracuseStep 26195845 = 4911721) B4911721
theorem B34927793 : Blo 2091435 34927793 := bstep (se 2 (by rfl) ⟨13097922, by rfl⟩ : syracuseStep 34927793 = 26195845) B26195845
theorem B23285195 : Blo 2091435 23285195 := bstep (se 1 (by rfl) ⟨17463896, by rfl⟩ : syracuseStep 23285195 = 34927793) B34927793
theorem B15523463 : Blo 2091435 15523463 := bstep (se 1 (by rfl) ⟨11642597, by rfl⟩ : syracuseStep 15523463 = 23285195) B23285195
theorem B41395901 : Blo 2091435 41395901 := bstep (se 3 (by rfl) ⟨7761731, by rfl⟩ : syracuseStep 41395901 = 15523463) B15523463
theorem B110389069 : Blo 2091435 110389069 := bstep (se 3 (by rfl) ⟨20697950, by rfl⟩ : syracuseStep 110389069 = 41395901) B41395901
theorem B147185425 : Blo 2091435 147185425 := bstep (se 2 (by rfl) ⟨55194534, by rfl⟩ : syracuseStep 147185425 = 110389069) B110389069
theorem B196247233 : Blo 2091435 196247233 := bstep (se 2 (by rfl) ⟨73592712, by rfl⟩ : syracuseStep 196247233 = 147185425) B147185425
theorem B261662977 : Blo 2091435 261662977 := bstep (se 2 (by rfl) ⟨98123616, by rfl⟩ : syracuseStep 261662977 = 196247233) B196247233
theorem B1395535877 : Blo 2091435 1395535877 := bstep (se 4 (by rfl) ⟨130831488, by rfl⟩ : syracuseStep 1395535877 = 261662977) B261662977
theorem B930357251 : Blo 2091435 930357251 := bstep (se 1 (by rfl) ⟨697767938, by rfl⟩ : syracuseStep 930357251 = 1395535877) B1395535877
theorem B620238167 : Blo 2091435 620238167 := bstep (se 1 (by rfl) ⟨465178625, by rfl⟩ : syracuseStep 620238167 = 930357251) B930357251
theorem B413492111 : Blo 2091435 413492111 := bstep (se 1 (by rfl) ⟨310119083, by rfl⟩ : syracuseStep 413492111 = 620238167) B620238167
theorem B275661407 : Blo 2091435 275661407 := bstep (se 1 (by rfl) ⟨206746055, by rfl⟩ : syracuseStep 275661407 = 413492111) B413492111
theorem B183774271 : Blo 2091435 183774271 := bstep (se 1 (by rfl) ⟨137830703, by rfl⟩ : syracuseStep 183774271 = 275661407) B275661407
theorem B245032361 : Blo 2091435 245032361 := bstep (se 2 (by rfl) ⟨91887135, by rfl⟩ : syracuseStep 245032361 = 183774271) B183774271
theorem B163354907 : Blo 2091435 163354907 := bstep (se 1 (by rfl) ⟨122516180, by rfl⟩ : syracuseStep 163354907 = 245032361) B245032361
theorem B435613085 : Blo 2091435 435613085 := bstep (se 3 (by rfl) ⟨81677453, by rfl⟩ : syracuseStep 435613085 = 163354907) B163354907
theorem B290408723 : Blo 2091435 290408723 := bstep (se 1 (by rfl) ⟨217806542, by rfl⟩ : syracuseStep 290408723 = 435613085) B435613085
theorem B193605815 : Blo 2091435 193605815 := bstep (se 1 (by rfl) ⟨145204361, by rfl⟩ : syracuseStep 193605815 = 290408723) B290408723
theorem B516282173 : Blo 2091435 516282173 := bstep (se 3 (by rfl) ⟨96802907, by rfl⟩ : syracuseStep 516282173 = 193605815) B193605815
theorem B344188115 : Blo 2091435 344188115 := bstep (se 1 (by rfl) ⟨258141086, by rfl⟩ : syracuseStep 344188115 = 516282173) B516282173
theorem B229458743 : Blo 2091435 229458743 := bstep (se 1 (by rfl) ⟨172094057, by rfl⟩ : syracuseStep 229458743 = 344188115) B344188115
theorem B152972495 : Blo 2091435 152972495 := bstep (se 1 (by rfl) ⟨114729371, by rfl⟩ : syracuseStep 152972495 = 229458743) B229458743
theorem B101981663 : Blo 2091435 101981663 := bstep (se 1 (by rfl) ⟨76486247, by rfl⟩ : syracuseStep 101981663 = 152972495) B152972495
theorem B67987775 : Blo 2091435 67987775 := bstep (se 1 (by rfl) ⟨50990831, by rfl⟩ : syracuseStep 67987775 = 101981663) B101981663
theorem B45325183 : Blo 2091435 45325183 := bstep (se 1 (by rfl) ⟨33993887, by rfl⟩ : syracuseStep 45325183 = 67987775) B67987775
theorem B60433577 : Blo 2091435 60433577 := bstep (se 2 (by rfl) ⟨22662591, by rfl⟩ : syracuseStep 60433577 = 45325183) B45325183
theorem B40289051 : Blo 2091435 40289051 := bstep (se 1 (by rfl) ⟨30216788, by rfl⟩ : syracuseStep 40289051 = 60433577) B60433577
theorem B26859367 : Blo 2091435 26859367 := bstep (se 1 (by rfl) ⟨20144525, by rfl⟩ : syracuseStep 26859367 = 40289051) B40289051
theorem B35812489 : Blo 2091435 35812489 := bstep (se 2 (by rfl) ⟨13429683, by rfl⟩ : syracuseStep 35812489 = 26859367) B26859367
theorem B47749985 : Blo 2091435 47749985 := bstep (se 2 (by rfl) ⟨17906244, by rfl⟩ : syracuseStep 47749985 = 35812489) B35812489
theorem B31833323 : Blo 2091435 31833323 := bstep (se 1 (by rfl) ⟨23874992, by rfl⟩ : syracuseStep 31833323 = 47749985) B47749985
theorem B21222215 : Blo 2091435 21222215 := bstep (se 1 (by rfl) ⟨15916661, by rfl⟩ : syracuseStep 21222215 = 31833323) B31833323
theorem B14148143 : Blo 2091435 14148143 := bstep (se 1 (by rfl) ⟨10611107, by rfl⟩ : syracuseStep 14148143 = 21222215) B21222215
theorem B150913525 : Blo 2091435 150913525 := bstep (se 5 (by rfl) ⟨7074071, by rfl⟩ : syracuseStep 150913525 = 14148143) B14148143
theorem B201218033 : Blo 2091435 201218033 := bstep (se 2 (by rfl) ⟨75456762, by rfl⟩ : syracuseStep 201218033 = 150913525) B150913525
theorem B536581421 : Blo 2091435 536581421 := bstep (se 3 (by rfl) ⟨100609016, by rfl⟩ : syracuseStep 536581421 = 201218033) B201218033
theorem B357720947 : Blo 2091435 357720947 := bstep (se 1 (by rfl) ⟨268290710, by rfl⟩ : syracuseStep 357720947 = 536581421) B536581421
theorem B238480631 : Blo 2091435 238480631 := bstep (se 1 (by rfl) ⟨178860473, by rfl⟩ : syracuseStep 238480631 = 357720947) B357720947
theorem B158987087 : Blo 2091435 158987087 := bstep (se 1 (by rfl) ⟨119240315, by rfl⟩ : syracuseStep 158987087 = 238480631) B238480631
theorem B105991391 : Blo 2091435 105991391 := bstep (se 1 (by rfl) ⟨79493543, by rfl⟩ : syracuseStep 105991391 = 158987087) B158987087
theorem B70660927 : Blo 2091435 70660927 := bstep (se 1 (by rfl) ⟨52995695, by rfl⟩ : syracuseStep 70660927 = 105991391) B105991391
theorem B94214569 : Blo 2091435 94214569 := bstep (se 2 (by rfl) ⟨35330463, by rfl⟩ : syracuseStep 94214569 = 70660927) B70660927
theorem B125619425 : Blo 2091435 125619425 := bstep (se 2 (by rfl) ⟨47107284, by rfl⟩ : syracuseStep 125619425 = 94214569) B94214569
theorem B83746283 : Blo 2091435 83746283 := bstep (se 1 (by rfl) ⟨62809712, by rfl⟩ : syracuseStep 83746283 = 125619425) B125619425
theorem B223323421 : Blo 2091435 223323421 := bstep (se 3 (by rfl) ⟨41873141, by rfl⟩ : syracuseStep 223323421 = 83746283) B83746283
theorem B297764561 : Blo 2091435 297764561 := bstep (se 2 (by rfl) ⟨111661710, by rfl⟩ : syracuseStep 297764561 = 223323421) B223323421
theorem B198509707 : Blo 2091435 198509707 := bstep (se 1 (by rfl) ⟨148882280, by rfl⟩ : syracuseStep 198509707 = 297764561) B297764561
theorem B264679609 : Blo 2091435 264679609 := bstep (se 2 (by rfl) ⟨99254853, by rfl⟩ : syracuseStep 264679609 = 198509707) B198509707
theorem B352906145 : Blo 2091435 352906145 := bstep (se 2 (by rfl) ⟨132339804, by rfl⟩ : syracuseStep 352906145 = 264679609) B264679609
theorem B235270763 : Blo 2091435 235270763 := bstep (se 1 (by rfl) ⟨176453072, by rfl⟩ : syracuseStep 235270763 = 352906145) B352906145
theorem B156847175 : Blo 2091435 156847175 := bstep (se 1 (by rfl) ⟨117635381, by rfl⟩ : syracuseStep 156847175 = 235270763) B235270763
theorem B104564783 : Blo 2091435 104564783 := bstep (se 1 (by rfl) ⟨78423587, by rfl⟩ : syracuseStep 104564783 = 156847175) B156847175
theorem B69709855 : Blo 2091435 69709855 := bstep (se 1 (by rfl) ⟨52282391, by rfl⟩ : syracuseStep 69709855 = 104564783) B104564783
theorem B92946473 : Blo 2091435 92946473 := bstep (se 2 (by rfl) ⟨34854927, by rfl⟩ : syracuseStep 92946473 = 69709855) B69709855
theorem B61964315 : Blo 2091435 61964315 := bstep (se 1 (by rfl) ⟨46473236, by rfl⟩ : syracuseStep 61964315 = 92946473) B92946473
theorem B41309543 : Blo 2091435 41309543 := bstep (se 1 (by rfl) ⟨30982157, by rfl⟩ : syracuseStep 41309543 = 61964315) B61964315
theorem B27539695 : Blo 2091435 27539695 := bstep (se 1 (by rfl) ⟨20654771, by rfl⟩ : syracuseStep 27539695 = 41309543) B41309543
theorem B146878373 : Blo 2091435 146878373 := bstep (se 4 (by rfl) ⟨13769847, by rfl⟩ : syracuseStep 146878373 = 27539695) B27539695
theorem B391675661 : Blo 2091435 391675661 := bstep (se 3 (by rfl) ⟨73439186, by rfl⟩ : syracuseStep 391675661 = 146878373) B146878373
theorem B261117107 : Blo 2091435 261117107 := bstep (se 1 (by rfl) ⟨195837830, by rfl⟩ : syracuseStep 261117107 = 391675661) B391675661
theorem B174078071 : Blo 2091435 174078071 := bstep (se 1 (by rfl) ⟨130558553, by rfl⟩ : syracuseStep 174078071 = 261117107) B261117107
theorem B116052047 : Blo 2091435 116052047 := bstep (se 1 (by rfl) ⟨87039035, by rfl⟩ : syracuseStep 116052047 = 174078071) B174078071
theorem B77368031 : Blo 2091435 77368031 := bstep (se 1 (by rfl) ⟨58026023, by rfl⟩ : syracuseStep 77368031 = 116052047) B116052047
theorem B51578687 : Blo 2091435 51578687 := bstep (se 1 (by rfl) ⟨38684015, by rfl⟩ : syracuseStep 51578687 = 77368031) B77368031
theorem B34385791 : Blo 2091435 34385791 := bstep (se 1 (by rfl) ⟨25789343, by rfl⟩ : syracuseStep 34385791 = 51578687) B51578687
theorem B45847721 : Blo 2091435 45847721 := bstep (se 2 (by rfl) ⟨17192895, by rfl⟩ : syracuseStep 45847721 = 34385791) B34385791
theorem B30565147 : Blo 2091435 30565147 := bstep (se 1 (by rfl) ⟨22923860, by rfl⟩ : syracuseStep 30565147 = 45847721) B45847721
theorem B40753529 : Blo 2091435 40753529 := bstep (se 2 (by rfl) ⟨15282573, by rfl⟩ : syracuseStep 40753529 = 30565147) B30565147
theorem B27169019 : Blo 2091435 27169019 := bstep (se 1 (by rfl) ⟨20376764, by rfl⟩ : syracuseStep 27169019 = 40753529) B40753529
theorem B18112679 : Blo 2091435 18112679 := bstep (se 1 (by rfl) ⟨13584509, by rfl⟩ : syracuseStep 18112679 = 27169019) B27169019
theorem B12075119 : Blo 2091435 12075119 := bstep (se 1 (by rfl) ⟨9056339, by rfl⟩ : syracuseStep 12075119 = 18112679) B18112679
theorem B8050079 : Blo 2091435 8050079 := bstep (se 1 (by rfl) ⟨6037559, by rfl⟩ : syracuseStep 8050079 = 12075119) B12075119
theorem B5366719 : Blo 2091435 5366719 := bstep (se 1 (by rfl) ⟨4025039, by rfl⟩ : syracuseStep 5366719 = 8050079) B8050079
theorem B7155625 : Blo 2091435 7155625 := bstep (se 2 (by rfl) ⟨2683359, by rfl⟩ : syracuseStep 7155625 = 5366719) B5366719
theorem B9540833 : Blo 2091435 9540833 := bstep (se 2 (by rfl) ⟨3577812, by rfl⟩ : syracuseStep 9540833 = 7155625) B7155625
theorem B25442221 : Blo 2091435 25442221 := bstep (se 3 (by rfl) ⟨4770416, by rfl⟩ : syracuseStep 25442221 = 9540833) B9540833
theorem B33922961 : Blo 2091435 33922961 := bstep (se 2 (by rfl) ⟨12721110, by rfl⟩ : syracuseStep 33922961 = 25442221) B25442221
theorem B22615307 : Blo 2091435 22615307 := bstep (se 1 (by rfl) ⟨16961480, by rfl⟩ : syracuseStep 22615307 = 33922961) B33922961
theorem B15076871 : Blo 2091435 15076871 := bstep (se 1 (by rfl) ⟨11307653, by rfl⟩ : syracuseStep 15076871 = 22615307) B22615307
theorem B10051247 : Blo 2091435 10051247 := bstep (se 1 (by rfl) ⟨7538435, by rfl⟩ : syracuseStep 10051247 = 15076871) B15076871
theorem B26803325 : Blo 2091435 26803325 := bstep (se 3 (by rfl) ⟨5025623, by rfl⟩ : syracuseStep 26803325 = 10051247) B10051247
theorem B17868883 : Blo 2091435 17868883 := bstep (se 1 (by rfl) ⟨13401662, by rfl⟩ : syracuseStep 17868883 = 26803325) B26803325
theorem B23825177 : Blo 2091435 23825177 := bstep (se 2 (by rfl) ⟨8934441, by rfl⟩ : syracuseStep 23825177 = 17868883) B17868883
theorem B15883451 : Blo 2091435 15883451 := bstep (se 1 (by rfl) ⟨11912588, by rfl⟩ : syracuseStep 15883451 = 23825177) B23825177
theorem B10588967 : Blo 2091435 10588967 := bstep (se 1 (by rfl) ⟨7941725, by rfl⟩ : syracuseStep 10588967 = 15883451) B15883451
theorem B7059311 : Blo 2091435 7059311 := bstep (se 1 (by rfl) ⟨5294483, by rfl⟩ : syracuseStep 7059311 = 10588967) B10588967
theorem B4706207 : Blo 2091435 4706207 := bstep (se 1 (by rfl) ⟨3529655, by rfl⟩ : syracuseStep 4706207 = 7059311) B7059311
theorem B3137471 : Blo 2091435 3137471 := bstep (se 1 (by rfl) ⟨2353103, by rfl⟩ : syracuseStep 3137471 = 4706207) B4706207
theorem B2091647 : Blo 2091435 2091647 := bstep (se 1 (by rfl) ⟨1568735, by rfl⟩ : syracuseStep 2091647 = 3137471) B3137471
theorem B3137477 : Blo 2091435 3137477 := bbase (se 4 (by rfl) ⟨294138, by rfl⟩ : syracuseStep 3137477 = 588277) (by norm_num)
theorem B2091651 : Blo 2091435 2091651 := bstep (se 1 (by rfl) ⟨1568738, by rfl⟩ : syracuseStep 2091651 = 3137477) B3137477
theorem B3529669 : Blo 2091435 3529669 := bbase (se 4 (by rfl) ⟨330906, by rfl⟩ : syracuseStep 3529669 = 661813) (by norm_num)
theorem B4706225 : Blo 2091435 4706225 := bstep (se 2 (by rfl) ⟨1764834, by rfl⟩ : syracuseStep 4706225 = 3529669) B3529669
theorem B3137483 : Blo 2091435 3137483 := bstep (se 1 (by rfl) ⟨2353112, by rfl⟩ : syracuseStep 3137483 = 4706225) B4706225
theorem B2091655 : Blo 2091435 2091655 := bstep (se 1 (by rfl) ⟨1568741, by rfl⟩ : syracuseStep 2091655 = 3137483) B3137483
theorem B2353117 : Blo 2091435 2353117 := bbase (se 3 (by rfl) ⟨441209, by rfl⟩ : syracuseStep 2353117 = 882419) (by norm_num)
theorem B3137489 : Blo 2091435 3137489 := bstep (se 2 (by rfl) ⟨1176558, by rfl⟩ : syracuseStep 3137489 = 2353117) B2353117
theorem B2091659 : Blo 2091435 2091659 := bstep (se 1 (by rfl) ⟨1568744, by rfl⟩ : syracuseStep 2091659 = 3137489) B3137489
theorem B7059365 : Blo 2091435 7059365 := bbase (se 4 (by rfl) ⟨661815, by rfl⟩ : syracuseStep 7059365 = 1323631) (by norm_num)
theorem B4706243 : Blo 2091435 4706243 := bstep (se 1 (by rfl) ⟨3529682, by rfl⟩ : syracuseStep 4706243 = 7059365) B7059365
theorem B3137495 : Blo 2091435 3137495 := bstep (se 1 (by rfl) ⟨2353121, by rfl⟩ : syracuseStep 3137495 = 4706243) B4706243
theorem B2091663 : Blo 2091435 2091663 := bstep (se 1 (by rfl) ⟨1568747, by rfl⟩ : syracuseStep 2091663 = 3137495) B3137495
theorem B3137501 : Blo 2091435 3137501 := bbase (se 3 (by rfl) ⟨588281, by rfl⟩ : syracuseStep 3137501 = 1176563) (by norm_num)
theorem B2091667 : Blo 2091435 2091667 := bstep (se 1 (by rfl) ⟨1568750, by rfl⟩ : syracuseStep 2091667 = 3137501) B3137501
theorem B4706261 : Blo 2091435 4706261 := bbase (se 7 (by rfl) ⟨55151, by rfl⟩ : syracuseStep 4706261 = 110303) (by norm_num)
theorem B3137507 : Blo 2091435 3137507 := bstep (se 1 (by rfl) ⟨2353130, by rfl⟩ : syracuseStep 3137507 = 4706261) B4706261
theorem B2091671 : Blo 2091435 2091671 := bstep (se 1 (by rfl) ⟨1568753, by rfl⟩ : syracuseStep 2091671 = 3137507) B3137507
theorem B13401845 : Blo 2091435 13401845 := bbase (se 5 (by rfl) ⟨628211, by rfl⟩ : syracuseStep 13401845 = 1256423) (by norm_num)
theorem B8934563 : Blo 2091435 8934563 := bstep (se 1 (by rfl) ⟨6700922, by rfl⟩ : syracuseStep 8934563 = 13401845) B13401845
theorem B5956375 : Blo 2091435 5956375 := bstep (se 1 (by rfl) ⟨4467281, by rfl⟩ : syracuseStep 5956375 = 8934563) B8934563
theorem B7941833 : Blo 2091435 7941833 := bstep (se 2 (by rfl) ⟨2978187, by rfl⟩ : syracuseStep 7941833 = 5956375) B5956375
theorem B5294555 : Blo 2091435 5294555 := bstep (se 1 (by rfl) ⟨3970916, by rfl⟩ : syracuseStep 5294555 = 7941833) B7941833
theorem B3529703 : Blo 2091435 3529703 := bstep (se 1 (by rfl) ⟨2647277, by rfl⟩ : syracuseStep 3529703 = 5294555) B5294555
theorem B2353135 : Blo 2091435 2353135 := bstep (se 1 (by rfl) ⟨1764851, by rfl⟩ : syracuseStep 2353135 = 3529703) B3529703
theorem B3137513 : Blo 2091435 3137513 := bstep (se 2 (by rfl) ⟨1176567, by rfl⟩ : syracuseStep 3137513 = 2353135) B2353135
theorem B2091675 : Blo 2091435 2091675 := bstep (se 1 (by rfl) ⟨1568756, by rfl⟩ : syracuseStep 2091675 = 3137513) B3137513
theorem B5025701 : Blo 2091435 5025701 := bbase (se 4 (by rfl) ⟨471159, by rfl⟩ : syracuseStep 5025701 = 942319) (by norm_num)
theorem B3350467 : Blo 2091435 3350467 := bstep (se 1 (by rfl) ⟨2512850, by rfl⟩ : syracuseStep 3350467 = 5025701) B5025701
theorem B17869157 : Blo 2091435 17869157 := bstep (se 4 (by rfl) ⟨1675233, by rfl⟩ : syracuseStep 17869157 = 3350467) B3350467
theorem B11912771 : Blo 2091435 11912771 := bstep (se 1 (by rfl) ⟨8934578, by rfl⟩ : syracuseStep 11912771 = 17869157) B17869157
theorem B7941847 : Blo 2091435 7941847 := bstep (se 1 (by rfl) ⟨5956385, by rfl⟩ : syracuseStep 7941847 = 11912771) B11912771
theorem B10589129 : Blo 2091435 10589129 := bstep (se 2 (by rfl) ⟨3970923, by rfl⟩ : syracuseStep 10589129 = 7941847) B7941847
theorem B7059419 : Blo 2091435 7059419 := bstep (se 1 (by rfl) ⟨5294564, by rfl⟩ : syracuseStep 7059419 = 10589129) B10589129
theorem B4706279 : Blo 2091435 4706279 := bstep (se 1 (by rfl) ⟨3529709, by rfl⟩ : syracuseStep 4706279 = 7059419) B7059419
theorem B3137519 : Blo 2091435 3137519 := bstep (se 1 (by rfl) ⟨2353139, by rfl⟩ : syracuseStep 3137519 = 4706279) B4706279
theorem B2091679 : Blo 2091435 2091679 := bstep (se 1 (by rfl) ⟨1568759, by rfl⟩ : syracuseStep 2091679 = 3137519) B3137519
theorem B3137525 : Blo 2091435 3137525 := bbase (se 5 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 3137525 = 294143) (by norm_num)
theorem B2091683 : Blo 2091435 2091683 := bstep (se 1 (by rfl) ⟨1568762, by rfl⟩ : syracuseStep 2091683 = 3137525) B3137525
theorem B4240453 : Blo 2091435 4240453 := bbase (se 4 (by rfl) ⟨397542, by rfl⟩ : syracuseStep 4240453 = 795085) (by norm_num)
theorem B5653937 : Blo 2091435 5653937 := bstep (se 2 (by rfl) ⟨2120226, by rfl⟩ : syracuseStep 5653937 = 4240453) B4240453
theorem B3769291 : Blo 2091435 3769291 := bstep (se 1 (by rfl) ⟨2826968, by rfl⟩ : syracuseStep 3769291 = 5653937) B5653937
theorem B5025721 : Blo 2091435 5025721 := bstep (se 2 (by rfl) ⟨1884645, by rfl⟩ : syracuseStep 5025721 = 3769291) B3769291
theorem B6700961 : Blo 2091435 6700961 := bstep (se 2 (by rfl) ⟨2512860, by rfl⟩ : syracuseStep 6700961 = 5025721) B5025721
theorem B4467307 : Blo 2091435 4467307 := bstep (se 1 (by rfl) ⟨3350480, by rfl⟩ : syracuseStep 4467307 = 6700961) B6700961
theorem B5956409 : Blo 2091435 5956409 := bstep (se 2 (by rfl) ⟨2233653, by rfl⟩ : syracuseStep 5956409 = 4467307) B4467307
theorem B3970939 : Blo 2091435 3970939 := bstep (se 1 (by rfl) ⟨2978204, by rfl⟩ : syracuseStep 3970939 = 5956409) B5956409
theorem B5294585 : Blo 2091435 5294585 := bstep (se 2 (by rfl) ⟨1985469, by rfl⟩ : syracuseStep 5294585 = 3970939) B3970939
theorem B3529723 : Blo 2091435 3529723 := bstep (se 1 (by rfl) ⟨2647292, by rfl⟩ : syracuseStep 3529723 = 5294585) B5294585
theorem B4706297 : Blo 2091435 4706297 := bstep (se 2 (by rfl) ⟨1764861, by rfl⟩ : syracuseStep 4706297 = 3529723) B3529723
theorem B3137531 : Blo 2091435 3137531 := bstep (se 1 (by rfl) ⟨2353148, by rfl⟩ : syracuseStep 3137531 = 4706297) B4706297
theorem B2091687 : Blo 2091435 2091687 := bstep (se 1 (by rfl) ⟨1568765, by rfl⟩ : syracuseStep 2091687 = 3137531) B3137531
theorem B2353153 : Blo 2091435 2353153 := bbase (se 2 (by rfl) ⟨882432, by rfl⟩ : syracuseStep 2353153 = 1764865) (by norm_num)
theorem B3137537 : Blo 2091435 3137537 := bstep (se 2 (by rfl) ⟨1176576, by rfl⟩ : syracuseStep 3137537 = 2353153) B2353153
theorem B2091691 : Blo 2091435 2091691 := bstep (se 1 (by rfl) ⟨1568768, by rfl⟩ : syracuseStep 2091691 = 3137537) B3137537
theorem B5294605 : Blo 2091435 5294605 := bbase (se 3 (by rfl) ⟨992738, by rfl⟩ : syracuseStep 5294605 = 1985477) (by norm_num)
theorem B7059473 : Blo 2091435 7059473 := bstep (se 2 (by rfl) ⟨2647302, by rfl⟩ : syracuseStep 7059473 = 5294605) B5294605
theorem B4706315 : Blo 2091435 4706315 := bstep (se 1 (by rfl) ⟨3529736, by rfl⟩ : syracuseStep 4706315 = 7059473) B7059473
theorem B3137543 : Blo 2091435 3137543 := bstep (se 1 (by rfl) ⟨2353157, by rfl⟩ : syracuseStep 3137543 = 4706315) B4706315
theorem B2091695 : Blo 2091435 2091695 := bstep (se 1 (by rfl) ⟨1568771, by rfl⟩ : syracuseStep 2091695 = 3137543) B3137543
theorem B3137549 : Blo 2091435 3137549 := bbase (se 3 (by rfl) ⟨588290, by rfl⟩ : syracuseStep 3137549 = 1176581) (by norm_num)
theorem B2091699 : Blo 2091435 2091699 := bstep (se 1 (by rfl) ⟨1568774, by rfl⟩ : syracuseStep 2091699 = 3137549) B3137549
theorem B4706333 : Blo 2091435 4706333 := bbase (se 3 (by rfl) ⟨882437, by rfl⟩ : syracuseStep 4706333 = 1764875) (by norm_num)
theorem B3137555 : Blo 2091435 3137555 := bstep (se 1 (by rfl) ⟨2353166, by rfl⟩ : syracuseStep 3137555 = 4706333) B4706333
theorem B2091703 : Blo 2091435 2091703 := bstep (se 1 (by rfl) ⟨1568777, by rfl⟩ : syracuseStep 2091703 = 3137555) B3137555
theorem B3529757 : Blo 2091435 3529757 := bbase (se 3 (by rfl) ⟨661829, by rfl⟩ : syracuseStep 3529757 = 1323659) (by norm_num)
theorem B2353171 : Blo 2091435 2353171 := bstep (se 1 (by rfl) ⟨1764878, by rfl⟩ : syracuseStep 2353171 = 3529757) B3529757
theorem B3137561 : Blo 2091435 3137561 := bstep (se 2 (by rfl) ⟨1176585, by rfl⟩ : syracuseStep 3137561 = 2353171) B2353171
theorem B2091707 : Blo 2091435 2091707 := bstep (se 1 (by rfl) ⟨1568780, by rfl⟩ : syracuseStep 2091707 = 3137561) B3137561
theorem B15077333 : Blo 2091435 15077333 := bbase (se 7 (by rfl) ⟨176687, by rfl⟩ : syracuseStep 15077333 = 353375) (by norm_num)
theorem B10051555 : Blo 2091435 10051555 := bstep (se 1 (by rfl) ⟨7538666, by rfl⟩ : syracuseStep 10051555 = 15077333) B15077333
theorem B13402073 : Blo 2091435 13402073 := bstep (se 2 (by rfl) ⟨5025777, by rfl⟩ : syracuseStep 13402073 = 10051555) B10051555
theorem B8934715 : Blo 2091435 8934715 := bstep (se 1 (by rfl) ⟨6701036, by rfl⟩ : syracuseStep 8934715 = 13402073) B13402073
theorem B11912953 : Blo 2091435 11912953 := bstep (se 2 (by rfl) ⟨4467357, by rfl⟩ : syracuseStep 11912953 = 8934715) B8934715
theorem B15883937 : Blo 2091435 15883937 := bstep (se 2 (by rfl) ⟨5956476, by rfl⟩ : syracuseStep 15883937 = 11912953) B11912953
theorem B10589291 : Blo 2091435 10589291 := bstep (se 1 (by rfl) ⟨7941968, by rfl⟩ : syracuseStep 10589291 = 15883937) B15883937
theorem B7059527 : Blo 2091435 7059527 := bstep (se 1 (by rfl) ⟨5294645, by rfl⟩ : syracuseStep 7059527 = 10589291) B10589291
theorem B4706351 : Blo 2091435 4706351 := bstep (se 1 (by rfl) ⟨3529763, by rfl⟩ : syracuseStep 4706351 = 7059527) B7059527
theorem B3137567 : Blo 2091435 3137567 := bstep (se 1 (by rfl) ⟨2353175, by rfl⟩ : syracuseStep 3137567 = 4706351) B4706351
theorem B2091711 : Blo 2091435 2091711 := bstep (se 1 (by rfl) ⟨1568783, by rfl⟩ : syracuseStep 2091711 = 3137567) B3137567
theorem B3137573 : Blo 2091435 3137573 := bbase (se 4 (by rfl) ⟨294147, by rfl⟩ : syracuseStep 3137573 = 588295) (by norm_num)
theorem B2091715 : Blo 2091435 2091715 := bstep (se 1 (by rfl) ⟨1568786, by rfl⟩ : syracuseStep 2091715 = 3137573) B3137573
theorem B2647333 : Blo 2091435 2647333 := bbase (se 4 (by rfl) ⟨248187, by rfl⟩ : syracuseStep 2647333 = 496375) (by norm_num)
theorem B3529777 : Blo 2091435 3529777 := bstep (se 2 (by rfl) ⟨1323666, by rfl⟩ : syracuseStep 3529777 = 2647333) B2647333
theorem B4706369 : Blo 2091435 4706369 := bstep (se 2 (by rfl) ⟨1764888, by rfl⟩ : syracuseStep 4706369 = 3529777) B3529777
theorem B3137579 : Blo 2091435 3137579 := bstep (se 1 (by rfl) ⟨2353184, by rfl⟩ : syracuseStep 3137579 = 4706369) B4706369
theorem B2091719 : Blo 2091435 2091719 := bstep (se 1 (by rfl) ⟨1568789, by rfl⟩ : syracuseStep 2091719 = 3137579) B3137579
theorem B2353189 : Blo 2091435 2353189 := bbase (se 4 (by rfl) ⟨220611, by rfl⟩ : syracuseStep 2353189 = 441223) (by norm_num)
theorem B3137585 : Blo 2091435 3137585 := bstep (se 2 (by rfl) ⟨1176594, by rfl⟩ : syracuseStep 3137585 = 2353189) B2353189
theorem B2091723 : Blo 2091435 2091723 := bstep (se 1 (by rfl) ⟨1568792, by rfl⟩ : syracuseStep 2091723 = 3137585) B3137585
theorem B2385301 : Blo 2091435 2385301 := bbase (se 6 (by rfl) ⟨55905, by rfl⟩ : syracuseStep 2385301 = 111811) (by norm_num)
theorem B3180401 : Blo 2091435 3180401 := bstep (se 2 (by rfl) ⟨1192650, by rfl⟩ : syracuseStep 3180401 = 2385301) B2385301
theorem B2120267 : Blo 2091435 2120267 := bstep (se 1 (by rfl) ⟨1590200, by rfl⟩ : syracuseStep 2120267 = 3180401) B3180401
theorem B5654045 : Blo 2091435 5654045 := bstep (se 3 (by rfl) ⟨1060133, by rfl⟩ : syracuseStep 5654045 = 2120267) B2120267
theorem B3769363 : Blo 2091435 3769363 := bstep (se 1 (by rfl) ⟨2827022, by rfl⟩ : syracuseStep 3769363 = 5654045) B5654045
theorem B5025817 : Blo 2091435 5025817 := bstep (se 2 (by rfl) ⟨1884681, by rfl⟩ : syracuseStep 5025817 = 3769363) B3769363
theorem B6701089 : Blo 2091435 6701089 := bstep (se 2 (by rfl) ⟨2512908, by rfl⟩ : syracuseStep 6701089 = 5025817) B5025817
theorem B8934785 : Blo 2091435 8934785 := bstep (se 2 (by rfl) ⟨3350544, by rfl⟩ : syracuseStep 8934785 = 6701089) B6701089
theorem B5956523 : Blo 2091435 5956523 := bstep (se 1 (by rfl) ⟨4467392, by rfl⟩ : syracuseStep 5956523 = 8934785) B8934785
theorem B3971015 : Blo 2091435 3971015 := bstep (se 1 (by rfl) ⟨2978261, by rfl⟩ : syracuseStep 3971015 = 5956523) B5956523
theorem B2647343 : Blo 2091435 2647343 := bstep (se 1 (by rfl) ⟨1985507, by rfl⟩ : syracuseStep 2647343 = 3971015) B3971015
theorem B7059581 : Blo 2091435 7059581 := bstep (se 3 (by rfl) ⟨1323671, by rfl⟩ : syracuseStep 7059581 = 2647343) B2647343
theorem B4706387 : Blo 2091435 4706387 := bstep (se 1 (by rfl) ⟨3529790, by rfl⟩ : syracuseStep 4706387 = 7059581) B7059581
theorem B3137591 : Blo 2091435 3137591 := bstep (se 1 (by rfl) ⟨2353193, by rfl⟩ : syracuseStep 3137591 = 4706387) B4706387
theorem B2091727 : Blo 2091435 2091727 := bstep (se 1 (by rfl) ⟨1568795, by rfl⟩ : syracuseStep 2091727 = 3137591) B3137591
theorem B3137597 : Blo 2091435 3137597 := bbase (se 3 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 3137597 = 1176599) (by norm_num)
theorem B2091731 : Blo 2091435 2091731 := bstep (se 1 (by rfl) ⟨1568798, by rfl⟩ : syracuseStep 2091731 = 3137597) B3137597
theorem B4706405 : Blo 2091435 4706405 := bbase (se 4 (by rfl) ⟨441225, by rfl⟩ : syracuseStep 4706405 = 882451) (by norm_num)
theorem B3137603 : Blo 2091435 3137603 := bstep (se 1 (by rfl) ⟨2353202, by rfl⟩ : syracuseStep 3137603 = 4706405) B4706405
theorem B2091735 : Blo 2091435 2091735 := bstep (se 1 (by rfl) ⟨1568801, by rfl⟩ : syracuseStep 2091735 = 3137603) B3137603
theorem B5294717 : Blo 2091435 5294717 := bbase (se 3 (by rfl) ⟨992759, by rfl⟩ : syracuseStep 5294717 = 1985519) (by norm_num)
theorem B3529811 : Blo 2091435 3529811 := bstep (se 1 (by rfl) ⟨2647358, by rfl⟩ : syracuseStep 3529811 = 5294717) B5294717
theorem B2353207 : Blo 2091435 2353207 := bstep (se 1 (by rfl) ⟨1764905, by rfl⟩ : syracuseStep 2353207 = 3529811) B3529811
theorem B3137609 : Blo 2091435 3137609 := bstep (se 2 (by rfl) ⟨1176603, by rfl⟩ : syracuseStep 3137609 = 2353207) B2353207
theorem B2091739 : Blo 2091435 2091739 := bstep (se 1 (by rfl) ⟨1568804, by rfl⟩ : syracuseStep 2091739 = 3137609) B3137609
theorem B3971045 : Blo 2091435 3971045 := bbase (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) (by norm_num)
theorem B10589453 : Blo 2091435 10589453 := bstep (se 3 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 10589453 = 3971045) B3971045
theorem B7059635 : Blo 2091435 7059635 := bstep (se 1 (by rfl) ⟨5294726, by rfl⟩ : syracuseStep 7059635 = 10589453) B10589453
theorem B4706423 : Blo 2091435 4706423 := bstep (se 1 (by rfl) ⟨3529817, by rfl⟩ : syracuseStep 4706423 = 7059635) B7059635
theorem B3137615 : Blo 2091435 3137615 := bstep (se 1 (by rfl) ⟨2353211, by rfl⟩ : syracuseStep 3137615 = 4706423) B4706423
theorem B2091743 : Blo 2091435 2091743 := bstep (se 1 (by rfl) ⟨1568807, by rfl⟩ : syracuseStep 2091743 = 3137615) B3137615
theorem B3137621 : Blo 2091435 3137621 := bbase (se 8 (by rfl) ⟨18384, by rfl⟩ : syracuseStep 3137621 = 36769) (by norm_num)
theorem B2091747 : Blo 2091435 2091747 := bstep (se 1 (by rfl) ⟨1568810, by rfl⟩ : syracuseStep 2091747 = 3137621) B3137621
theorem B6037861 : Blo 2091435 6037861 := bbase (se 4 (by rfl) ⟨566049, by rfl⟩ : syracuseStep 6037861 = 1132099) (by norm_num)
theorem B8050481 : Blo 2091435 8050481 := bstep (se 2 (by rfl) ⟨3018930, by rfl⟩ : syracuseStep 8050481 = 6037861) B6037861
theorem B5366987 : Blo 2091435 5366987 := bstep (se 1 (by rfl) ⟨4025240, by rfl⟩ : syracuseStep 5366987 = 8050481) B8050481
theorem B3577991 : Blo 2091435 3577991 := bstep (se 1 (by rfl) ⟨2683493, by rfl⟩ : syracuseStep 3577991 = 5366987) B5366987
theorem B9541309 : Blo 2091435 9541309 := bstep (se 3 (by rfl) ⟨1788995, by rfl⟩ : syracuseStep 9541309 = 3577991) B3577991
theorem B12721745 : Blo 2091435 12721745 := bstep (se 2 (by rfl) ⟨4770654, by rfl⟩ : syracuseStep 12721745 = 9541309) B9541309
theorem B33924653 : Blo 2091435 33924653 := bstep (se 3 (by rfl) ⟨6360872, by rfl⟩ : syracuseStep 33924653 = 12721745) B12721745
theorem B22616435 : Blo 2091435 22616435 := bstep (se 1 (by rfl) ⟨16962326, by rfl⟩ : syracuseStep 22616435 = 33924653) B33924653
theorem B15077623 : Blo 2091435 15077623 := bstep (se 1 (by rfl) ⟨11308217, by rfl⟩ : syracuseStep 15077623 = 22616435) B22616435
theorem B20103497 : Blo 2091435 20103497 := bstep (se 2 (by rfl) ⟨7538811, by rfl⟩ : syracuseStep 20103497 = 15077623) B15077623
theorem B13402331 : Blo 2091435 13402331 := bstep (se 1 (by rfl) ⟨10051748, by rfl⟩ : syracuseStep 13402331 = 20103497) B20103497
theorem B8934887 : Blo 2091435 8934887 := bstep (se 1 (by rfl) ⟨6701165, by rfl⟩ : syracuseStep 8934887 = 13402331) B13402331
theorem B5956591 : Blo 2091435 5956591 := bstep (se 1 (by rfl) ⟨4467443, by rfl⟩ : syracuseStep 5956591 = 8934887) B8934887
theorem B7942121 : Blo 2091435 7942121 := bstep (se 2 (by rfl) ⟨2978295, by rfl⟩ : syracuseStep 7942121 = 5956591) B5956591
theorem B5294747 : Blo 2091435 5294747 := bstep (se 1 (by rfl) ⟨3971060, by rfl⟩ : syracuseStep 5294747 = 7942121) B7942121
theorem B3529831 : Blo 2091435 3529831 := bstep (se 1 (by rfl) ⟨2647373, by rfl⟩ : syracuseStep 3529831 = 5294747) B5294747
theorem B4706441 : Blo 2091435 4706441 := bstep (se 2 (by rfl) ⟨1764915, by rfl⟩ : syracuseStep 4706441 = 3529831) B3529831
theorem B3137627 : Blo 2091435 3137627 := bstep (se 1 (by rfl) ⟨2353220, by rfl⟩ : syracuseStep 3137627 = 4706441) B4706441
theorem B2091751 : Blo 2091435 2091751 := bstep (se 1 (by rfl) ⟨1568813, by rfl⟩ : syracuseStep 2091751 = 3137627) B3137627
theorem B2353225 : Blo 2091435 2353225 := bbase (se 2 (by rfl) ⟨882459, by rfl⟩ : syracuseStep 2353225 = 1764919) (by norm_num)
theorem B3137633 : Blo 2091435 3137633 := bstep (se 2 (by rfl) ⟨1176612, by rfl⟩ : syracuseStep 3137633 = 2353225) B2353225
theorem B2091755 : Blo 2091435 2091755 := bstep (se 1 (by rfl) ⟨1568816, by rfl⟩ : syracuseStep 2091755 = 3137633) B3137633
theorem B5025893 : Blo 2091435 5025893 := bbase (se 4 (by rfl) ⟨471177, by rfl⟩ : syracuseStep 5025893 = 942355) (by norm_num)
theorem B13402381 : Blo 2091435 13402381 := bstep (se 3 (by rfl) ⟨2512946, by rfl⟩ : syracuseStep 13402381 = 5025893) B5025893
theorem B17869841 : Blo 2091435 17869841 := bstep (se 2 (by rfl) ⟨6701190, by rfl⟩ : syracuseStep 17869841 = 13402381) B13402381
theorem B11913227 : Blo 2091435 11913227 := bstep (se 1 (by rfl) ⟨8934920, by rfl⟩ : syracuseStep 11913227 = 17869841) B17869841
theorem B7942151 : Blo 2091435 7942151 := bstep (se 1 (by rfl) ⟨5956613, by rfl⟩ : syracuseStep 7942151 = 11913227) B11913227
theorem B5294767 : Blo 2091435 5294767 := bstep (se 1 (by rfl) ⟨3971075, by rfl⟩ : syracuseStep 5294767 = 7942151) B7942151
theorem B7059689 : Blo 2091435 7059689 := bstep (se 2 (by rfl) ⟨2647383, by rfl⟩ : syracuseStep 7059689 = 5294767) B5294767
theorem B4706459 : Blo 2091435 4706459 := bstep (se 1 (by rfl) ⟨3529844, by rfl⟩ : syracuseStep 4706459 = 7059689) B7059689
theorem B3137639 : Blo 2091435 3137639 := bstep (se 1 (by rfl) ⟨2353229, by rfl⟩ : syracuseStep 3137639 = 4706459) B4706459
theorem B2091759 : Blo 2091435 2091759 := bstep (se 1 (by rfl) ⟨1568819, by rfl⟩ : syracuseStep 2091759 = 3137639) B3137639
theorem B3137645 : Blo 2091435 3137645 := bbase (se 3 (by rfl) ⟨588308, by rfl⟩ : syracuseStep 3137645 = 1176617) (by norm_num)
theorem B2091763 : Blo 2091435 2091763 := bstep (se 1 (by rfl) ⟨1568822, by rfl⟩ : syracuseStep 2091763 = 3137645) B3137645
theorem B4706477 : Blo 2091435 4706477 := bbase (se 3 (by rfl) ⟨882464, by rfl⟩ : syracuseStep 4706477 = 1764929) (by norm_num)
theorem B3137651 : Blo 2091435 3137651 := bstep (se 1 (by rfl) ⟨2353238, by rfl⟩ : syracuseStep 3137651 = 4706477) B4706477
theorem B2091767 : Blo 2091435 2091767 := bstep (se 1 (by rfl) ⟨1568825, by rfl⟩ : syracuseStep 2091767 = 3137651) B3137651
theorem B3676325 : Blo 2091435 3676325 := bbase (se 4 (by rfl) ⟨344655, by rfl⟩ : syracuseStep 3676325 = 689311) (by norm_num)
theorem B9803533 : Blo 2091435 9803533 := bstep (se 3 (by rfl) ⟨1838162, by rfl⟩ : syracuseStep 9803533 = 3676325) B3676325
theorem B13071377 : Blo 2091435 13071377 := bstep (se 2 (by rfl) ⟨4901766, by rfl⟩ : syracuseStep 13071377 = 9803533) B9803533
theorem B8714251 : Blo 2091435 8714251 := bstep (se 1 (by rfl) ⟨6535688, by rfl⟩ : syracuseStep 8714251 = 13071377) B13071377
theorem B743616085 : Blo 2091435 743616085 := bstep (se 8 (by rfl) ⟨4357125, by rfl⟩ : syracuseStep 743616085 = 8714251) B8714251
theorem B991488113 : Blo 2091435 991488113 := bstep (se 2 (by rfl) ⟨371808042, by rfl⟩ : syracuseStep 991488113 = 743616085) B743616085
theorem B660992075 : Blo 2091435 660992075 := bstep (se 1 (by rfl) ⟨495744056, by rfl⟩ : syracuseStep 660992075 = 991488113) B991488113
theorem B440661383 : Blo 2091435 440661383 := bstep (se 1 (by rfl) ⟨330496037, by rfl⟩ : syracuseStep 440661383 = 660992075) B660992075
theorem B293774255 : Blo 2091435 293774255 := bstep (se 1 (by rfl) ⟨220330691, by rfl⟩ : syracuseStep 293774255 = 440661383) B440661383
theorem B195849503 : Blo 2091435 195849503 := bstep (se 1 (by rfl) ⟨146887127, by rfl⟩ : syracuseStep 195849503 = 293774255) B293774255
theorem B130566335 : Blo 2091435 130566335 := bstep (se 1 (by rfl) ⟨97924751, by rfl⟩ : syracuseStep 130566335 = 195849503) B195849503
theorem B348176893 : Blo 2091435 348176893 := bstep (se 3 (by rfl) ⟨65283167, by rfl⟩ : syracuseStep 348176893 = 130566335) B130566335
theorem B464235857 : Blo 2091435 464235857 := bstep (se 2 (by rfl) ⟨174088446, by rfl⟩ : syracuseStep 464235857 = 348176893) B348176893
theorem B309490571 : Blo 2091435 309490571 := bstep (se 1 (by rfl) ⟨232117928, by rfl⟩ : syracuseStep 309490571 = 464235857) B464235857
theorem B206327047 : Blo 2091435 206327047 := bstep (se 1 (by rfl) ⟨154745285, by rfl⟩ : syracuseStep 206327047 = 309490571) B309490571
theorem B275102729 : Blo 2091435 275102729 := bstep (se 2 (by rfl) ⟨103163523, by rfl⟩ : syracuseStep 275102729 = 206327047) B206327047
theorem B183401819 : Blo 2091435 183401819 := bstep (se 1 (by rfl) ⟨137551364, by rfl⟩ : syracuseStep 183401819 = 275102729) B275102729
theorem B122267879 : Blo 2091435 122267879 := bstep (se 1 (by rfl) ⟨91700909, by rfl⟩ : syracuseStep 122267879 = 183401819) B183401819
theorem B81511919 : Blo 2091435 81511919 := bstep (se 1 (by rfl) ⟨61133939, by rfl⟩ : syracuseStep 81511919 = 122267879) B122267879
theorem B54341279 : Blo 2091435 54341279 := bstep (se 1 (by rfl) ⟨40755959, by rfl⟩ : syracuseStep 54341279 = 81511919) B81511919
theorem B36227519 : Blo 2091435 36227519 := bstep (se 1 (by rfl) ⟨27170639, by rfl⟩ : syracuseStep 36227519 = 54341279) B54341279
theorem B24151679 : Blo 2091435 24151679 := bstep (se 1 (by rfl) ⟨18113759, by rfl⟩ : syracuseStep 24151679 = 36227519) B36227519
theorem B16101119 : Blo 2091435 16101119 := bstep (se 1 (by rfl) ⟨12075839, by rfl⟩ : syracuseStep 16101119 = 24151679) B24151679
theorem B10734079 : Blo 2091435 10734079 := bstep (se 1 (by rfl) ⟨8050559, by rfl⟩ : syracuseStep 10734079 = 16101119) B16101119
theorem B14312105 : Blo 2091435 14312105 := bstep (se 2 (by rfl) ⟨5367039, by rfl⟩ : syracuseStep 14312105 = 10734079) B10734079
theorem B9541403 : Blo 2091435 9541403 := bstep (se 1 (by rfl) ⟨7156052, by rfl⟩ : syracuseStep 9541403 = 14312105) B14312105
theorem B6360935 : Blo 2091435 6360935 := bstep (se 1 (by rfl) ⟨4770701, by rfl⟩ : syracuseStep 6360935 = 9541403) B9541403
theorem B16962493 : Blo 2091435 16962493 := bstep (se 3 (by rfl) ⟨3180467, by rfl⟩ : syracuseStep 16962493 = 6360935) B6360935
theorem B22616657 : Blo 2091435 22616657 := bstep (se 2 (by rfl) ⟨8481246, by rfl⟩ : syracuseStep 22616657 = 16962493) B16962493
theorem B15077771 : Blo 2091435 15077771 := bstep (se 1 (by rfl) ⟨11308328, by rfl⟩ : syracuseStep 15077771 = 22616657) B22616657
theorem B10051847 : Blo 2091435 10051847 := bstep (se 1 (by rfl) ⟨7538885, by rfl⟩ : syracuseStep 10051847 = 15077771) B15077771
theorem B6701231 : Blo 2091435 6701231 := bstep (se 1 (by rfl) ⟨5025923, by rfl⟩ : syracuseStep 6701231 = 10051847) B10051847
theorem B4467487 : Blo 2091435 4467487 := bstep (se 1 (by rfl) ⟨3350615, by rfl⟩ : syracuseStep 4467487 = 6701231) B6701231
theorem B5956649 : Blo 2091435 5956649 := bstep (se 2 (by rfl) ⟨2233743, by rfl⟩ : syracuseStep 5956649 = 4467487) B4467487
theorem B3971099 : Blo 2091435 3971099 := bstep (se 1 (by rfl) ⟨2978324, by rfl⟩ : syracuseStep 3971099 = 5956649) B5956649
theorem B2647399 : Blo 2091435 2647399 := bstep (se 1 (by rfl) ⟨1985549, by rfl⟩ : syracuseStep 2647399 = 3971099) B3971099
theorem B3529865 : Blo 2091435 3529865 := bstep (se 2 (by rfl) ⟨1323699, by rfl⟩ : syracuseStep 3529865 = 2647399) B2647399
theorem B2353243 : Blo 2091435 2353243 := bstep (se 1 (by rfl) ⟨1764932, by rfl⟩ : syracuseStep 2353243 = 3529865) B3529865
theorem B3137657 : Blo 2091435 3137657 := bstep (se 2 (by rfl) ⟨1176621, by rfl⟩ : syracuseStep 3137657 = 2353243) B2353243
theorem B2091771 : Blo 2091435 2091771 := bstep (se 1 (by rfl) ⟨1568828, by rfl⟩ : syracuseStep 2091771 = 3137657) B3137657
theorem B2683525 : Blo 2091435 2683525 := bbase (se 4 (by rfl) ⟨251580, by rfl⟩ : syracuseStep 2683525 = 503161) (by norm_num)
theorem B3578033 : Blo 2091435 3578033 := bstep (se 2 (by rfl) ⟨1341762, by rfl⟩ : syracuseStep 3578033 = 2683525) B2683525
theorem B2385355 : Blo 2091435 2385355 := bstep (se 1 (by rfl) ⟨1789016, by rfl⟩ : syracuseStep 2385355 = 3578033) B3578033
theorem B3180473 : Blo 2091435 3180473 := bstep (se 2 (by rfl) ⟨1192677, by rfl⟩ : syracuseStep 3180473 = 2385355) B2385355
theorem B2120315 : Blo 2091435 2120315 := bstep (se 1 (by rfl) ⟨1590236, by rfl⟩ : syracuseStep 2120315 = 3180473) B3180473
theorem B5654173 : Blo 2091435 5654173 := bstep (se 3 (by rfl) ⟨1060157, by rfl⟩ : syracuseStep 5654173 = 2120315) B2120315
theorem B7538897 : Blo 2091435 7538897 := bstep (se 2 (by rfl) ⟨2827086, by rfl⟩ : syracuseStep 7538897 = 5654173) B5654173
theorem B5025931 : Blo 2091435 5025931 := bstep (se 1 (by rfl) ⟨3769448, by rfl⟩ : syracuseStep 5025931 = 7538897) B7538897
theorem B26804965 : Blo 2091435 26804965 := bstep (se 4 (by rfl) ⟨2512965, by rfl⟩ : syracuseStep 26804965 = 5025931) B5025931
theorem B35739953 : Blo 2091435 35739953 := bstep (se 2 (by rfl) ⟨13402482, by rfl⟩ : syracuseStep 35739953 = 26804965) B26804965
theorem B23826635 : Blo 2091435 23826635 := bstep (se 1 (by rfl) ⟨17869976, by rfl⟩ : syracuseStep 23826635 = 35739953) B35739953
theorem B15884423 : Blo 2091435 15884423 := bstep (se 1 (by rfl) ⟨11913317, by rfl⟩ : syracuseStep 15884423 = 23826635) B23826635
theorem B10589615 : Blo 2091435 10589615 := bstep (se 1 (by rfl) ⟨7942211, by rfl⟩ : syracuseStep 10589615 = 15884423) B15884423
theorem B7059743 : Blo 2091435 7059743 := bstep (se 1 (by rfl) ⟨5294807, by rfl⟩ : syracuseStep 7059743 = 10589615) B10589615
theorem B4706495 : Blo 2091435 4706495 := bstep (se 1 (by rfl) ⟨3529871, by rfl⟩ : syracuseStep 4706495 = 7059743) B7059743
theorem B3137663 : Blo 2091435 3137663 := bstep (se 1 (by rfl) ⟨2353247, by rfl⟩ : syracuseStep 3137663 = 4706495) B4706495
theorem B2091775 : Blo 2091435 2091775 := bstep (se 1 (by rfl) ⟨1568831, by rfl⟩ : syracuseStep 2091775 = 3137663) B3137663
theorem B3137669 : Blo 2091435 3137669 := bbase (se 4 (by rfl) ⟨294156, by rfl⟩ : syracuseStep 3137669 = 588313) (by norm_num)
theorem B2091779 : Blo 2091435 2091779 := bstep (se 1 (by rfl) ⟨1568834, by rfl⟩ : syracuseStep 2091779 = 3137669) B3137669
theorem B3529885 : Blo 2091435 3529885 := bbase (se 3 (by rfl) ⟨661853, by rfl⟩ : syracuseStep 3529885 = 1323707) (by norm_num)
theorem B4706513 : Blo 2091435 4706513 := bstep (se 2 (by rfl) ⟨1764942, by rfl⟩ : syracuseStep 4706513 = 3529885) B3529885
theorem B3137675 : Blo 2091435 3137675 := bstep (se 1 (by rfl) ⟨2353256, by rfl⟩ : syracuseStep 3137675 = 4706513) B4706513
theorem B2091783 : Blo 2091435 2091783 := bstep (se 1 (by rfl) ⟨1568837, by rfl⟩ : syracuseStep 2091783 = 3137675) B3137675
theorem B2353261 : Blo 2091435 2353261 := bbase (se 3 (by rfl) ⟨441236, by rfl⟩ : syracuseStep 2353261 = 882473) (by norm_num)
theorem B3137681 : Blo 2091435 3137681 := bstep (se 2 (by rfl) ⟨1176630, by rfl⟩ : syracuseStep 3137681 = 2353261) B2353261
theorem B2091787 : Blo 2091435 2091787 := bstep (se 1 (by rfl) ⟨1568840, by rfl⟩ : syracuseStep 2091787 = 3137681) B3137681
theorem B7059797 : Blo 2091435 7059797 := bbase (se 10 (by rfl) ⟨10341, by rfl⟩ : syracuseStep 7059797 = 20683) (by norm_num)
theorem B4706531 : Blo 2091435 4706531 := bstep (se 1 (by rfl) ⟨3529898, by rfl⟩ : syracuseStep 4706531 = 7059797) B7059797
theorem B3137687 : Blo 2091435 3137687 := bstep (se 1 (by rfl) ⟨2353265, by rfl⟩ : syracuseStep 3137687 = 4706531) B4706531
theorem B2091791 : Blo 2091435 2091791 := bstep (se 1 (by rfl) ⟨1568843, by rfl⟩ : syracuseStep 2091791 = 3137687) B3137687
theorem B3137693 : Blo 2091435 3137693 := bbase (se 3 (by rfl) ⟨588317, by rfl⟩ : syracuseStep 3137693 = 1176635) (by norm_num)
theorem B2091795 : Blo 2091435 2091795 := bstep (se 1 (by rfl) ⟨1568846, by rfl⟩ : syracuseStep 2091795 = 3137693) B3137693
theorem B4706549 : Blo 2091435 4706549 := bbase (se 5 (by rfl) ⟨220619, by rfl⟩ : syracuseStep 4706549 = 441239) (by norm_num)
theorem B3137699 : Blo 2091435 3137699 := bstep (se 1 (by rfl) ⟨2353274, by rfl⟩ : syracuseStep 3137699 = 4706549) B4706549
theorem B2091799 : Blo 2091435 2091799 := bstep (se 1 (by rfl) ⟨1568849, by rfl⟩ : syracuseStep 2091799 = 3137699) B3137699
theorem B2149273 : Blo 2091435 2149273 := bbase (se 2 (by rfl) ⟨805977, by rfl⟩ : syracuseStep 2149273 = 1611955) (by norm_num)
theorem B11462789 : Blo 2091435 11462789 := bstep (se 4 (by rfl) ⟨1074636, by rfl⟩ : syracuseStep 11462789 = 2149273) B2149273
theorem B7641859 : Blo 2091435 7641859 := bstep (se 1 (by rfl) ⟨5731394, by rfl⟩ : syracuseStep 7641859 = 11462789) B11462789
theorem B10189145 : Blo 2091435 10189145 := bstep (se 2 (by rfl) ⟨3820929, by rfl⟩ : syracuseStep 10189145 = 7641859) B7641859
theorem B6792763 : Blo 2091435 6792763 := bstep (se 1 (by rfl) ⟨5094572, by rfl⟩ : syracuseStep 6792763 = 10189145) B10189145
theorem B9057017 : Blo 2091435 9057017 := bstep (se 2 (by rfl) ⟨3396381, by rfl⟩ : syracuseStep 9057017 = 6792763) B6792763
theorem B6038011 : Blo 2091435 6038011 := bstep (se 1 (by rfl) ⟨4528508, by rfl⟩ : syracuseStep 6038011 = 9057017) B9057017
theorem B8050681 : Blo 2091435 8050681 := bstep (se 2 (by rfl) ⟨3019005, by rfl⟩ : syracuseStep 8050681 = 6038011) B6038011
theorem B10734241 : Blo 2091435 10734241 := bstep (se 2 (by rfl) ⟨4025340, by rfl⟩ : syracuseStep 10734241 = 8050681) B8050681
theorem B14312321 : Blo 2091435 14312321 := bstep (se 2 (by rfl) ⟨5367120, by rfl⟩ : syracuseStep 14312321 = 10734241) B10734241
theorem B9541547 : Blo 2091435 9541547 := bstep (se 1 (by rfl) ⟨7156160, by rfl⟩ : syracuseStep 9541547 = 14312321) B14312321
theorem B6361031 : Blo 2091435 6361031 := bstep (se 1 (by rfl) ⟨4770773, by rfl⟩ : syracuseStep 6361031 = 9541547) B9541547
theorem B16962749 : Blo 2091435 16962749 := bstep (se 3 (by rfl) ⟨3180515, by rfl⟩ : syracuseStep 16962749 = 6361031) B6361031
theorem B11308499 : Blo 2091435 11308499 := bstep (se 1 (by rfl) ⟨8481374, by rfl⟩ : syracuseStep 11308499 = 16962749) B16962749
theorem B7538999 : Blo 2091435 7538999 := bstep (se 1 (by rfl) ⟨5654249, by rfl⟩ : syracuseStep 7538999 = 11308499) B11308499
theorem B20103997 : Blo 2091435 20103997 := bstep (se 3 (by rfl) ⟨3769499, by rfl⟩ : syracuseStep 20103997 = 7538999) B7538999
theorem B26805329 : Blo 2091435 26805329 := bstep (se 2 (by rfl) ⟨10051998, by rfl⟩ : syracuseStep 26805329 = 20103997) B20103997
theorem B17870219 : Blo 2091435 17870219 := bstep (se 1 (by rfl) ⟨13402664, by rfl⟩ : syracuseStep 17870219 = 26805329) B26805329
theorem B11913479 : Blo 2091435 11913479 := bstep (se 1 (by rfl) ⟨8935109, by rfl⟩ : syracuseStep 11913479 = 17870219) B17870219
theorem B7942319 : Blo 2091435 7942319 := bstep (se 1 (by rfl) ⟨5956739, by rfl⟩ : syracuseStep 7942319 = 11913479) B11913479
theorem B5294879 : Blo 2091435 5294879 := bstep (se 1 (by rfl) ⟨3971159, by rfl⟩ : syracuseStep 5294879 = 7942319) B7942319
theorem B3529919 : Blo 2091435 3529919 := bstep (se 1 (by rfl) ⟨2647439, by rfl⟩ : syracuseStep 3529919 = 5294879) B5294879
theorem B2353279 : Blo 2091435 2353279 := bstep (se 1 (by rfl) ⟨1764959, by rfl⟩ : syracuseStep 2353279 = 3529919) B3529919
theorem B3137705 : Blo 2091435 3137705 := bstep (se 2 (by rfl) ⟨1176639, by rfl⟩ : syracuseStep 3137705 = 2353279) B2353279
theorem B2091803 : Blo 2091435 2091803 := bstep (se 1 (by rfl) ⟨1568852, by rfl⟩ : syracuseStep 2091803 = 3137705) B3137705
theorem B5654261 : Blo 2091435 5654261 := bbase (se 5 (by rfl) ⟨265043, by rfl⟩ : syracuseStep 5654261 = 530087) (by norm_num)
theorem B3769507 : Blo 2091435 3769507 := bstep (se 1 (by rfl) ⟨2827130, by rfl⟩ : syracuseStep 3769507 = 5654261) B5654261
theorem B5026009 : Blo 2091435 5026009 := bstep (se 2 (by rfl) ⟨1884753, by rfl⟩ : syracuseStep 5026009 = 3769507) B3769507
theorem B6701345 : Blo 2091435 6701345 := bstep (se 2 (by rfl) ⟨2513004, by rfl⟩ : syracuseStep 6701345 = 5026009) B5026009
theorem B4467563 : Blo 2091435 4467563 := bstep (se 1 (by rfl) ⟨3350672, by rfl⟩ : syracuseStep 4467563 = 6701345) B6701345
theorem B2978375 : Blo 2091435 2978375 := bstep (se 1 (by rfl) ⟨2233781, by rfl⟩ : syracuseStep 2978375 = 4467563) B4467563
theorem B7942333 : Blo 2091435 7942333 := bstep (se 3 (by rfl) ⟨1489187, by rfl⟩ : syracuseStep 7942333 = 2978375) B2978375
theorem B10589777 : Blo 2091435 10589777 := bstep (se 2 (by rfl) ⟨3971166, by rfl⟩ : syracuseStep 10589777 = 7942333) B7942333
theorem B7059851 : Blo 2091435 7059851 := bstep (se 1 (by rfl) ⟨5294888, by rfl⟩ : syracuseStep 7059851 = 10589777) B10589777
theorem B4706567 : Blo 2091435 4706567 := bstep (se 1 (by rfl) ⟨3529925, by rfl⟩ : syracuseStep 4706567 = 7059851) B7059851
theorem B3137711 : Blo 2091435 3137711 := bstep (se 1 (by rfl) ⟨2353283, by rfl⟩ : syracuseStep 3137711 = 4706567) B4706567
theorem B2091807 : Blo 2091435 2091807 := bstep (se 1 (by rfl) ⟨1568855, by rfl⟩ : syracuseStep 2091807 = 3137711) B3137711
theorem B3137717 : Blo 2091435 3137717 := bbase (se 5 (by rfl) ⟨147080, by rfl⟩ : syracuseStep 3137717 = 294161) (by norm_num)
theorem B2091811 : Blo 2091435 2091811 := bstep (se 1 (by rfl) ⟨1568858, by rfl⟩ : syracuseStep 2091811 = 3137717) B3137717
theorem B5294909 : Blo 2091435 5294909 := bbase (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) (by norm_num)
theorem B3529939 : Blo 2091435 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B4706585 : Blo 2091435 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B3137723 : Blo 2091435 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B2091815 : Blo 2091435 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B2353297 : Blo 2091435 2353297 := bbase (se 2 (by rfl) ⟨882486, by rfl⟩ : syracuseStep 2353297 = 1764973) (by norm_num)
theorem B3137729 : Blo 2091435 3137729 := bstep (se 2 (by rfl) ⟨1176648, by rfl⟩ : syracuseStep 3137729 = 2353297) B2353297
theorem B2091819 : Blo 2091435 2091819 := bstep (se 1 (by rfl) ⟨1568864, by rfl⟩ : syracuseStep 2091819 = 3137729) B3137729
theorem B3971197 : Blo 2091435 3971197 := bbase (se 3 (by rfl) ⟨744599, by rfl⟩ : syracuseStep 3971197 = 1489199) (by norm_num)
theorem B5294929 : Blo 2091435 5294929 := bstep (se 2 (by rfl) ⟨1985598, by rfl⟩ : syracuseStep 5294929 = 3971197) B3971197
theorem B7059905 : Blo 2091435 7059905 := bstep (se 2 (by rfl) ⟨2647464, by rfl⟩ : syracuseStep 7059905 = 5294929) B5294929
theorem B4706603 : Blo 2091435 4706603 := bstep (se 1 (by rfl) ⟨3529952, by rfl⟩ : syracuseStep 4706603 = 7059905) B7059905
theorem B3137735 : Blo 2091435 3137735 := bstep (se 1 (by rfl) ⟨2353301, by rfl⟩ : syracuseStep 3137735 = 4706603) B4706603
theorem B2091823 : Blo 2091435 2091823 := bstep (se 1 (by rfl) ⟨1568867, by rfl⟩ : syracuseStep 2091823 = 3137735) B3137735
theorem B3137741 : Blo 2091435 3137741 := bbase (se 3 (by rfl) ⟨588326, by rfl⟩ : syracuseStep 3137741 = 1176653) (by norm_num)
theorem B2091827 : Blo 2091435 2091827 := bstep (se 1 (by rfl) ⟨1568870, by rfl⟩ : syracuseStep 2091827 = 3137741) B3137741
theorem B4706621 : Blo 2091435 4706621 := bbase (se 3 (by rfl) ⟨882491, by rfl⟩ : syracuseStep 4706621 = 1764983) (by norm_num)
theorem B3137747 : Blo 2091435 3137747 := bstep (se 1 (by rfl) ⟨2353310, by rfl⟩ : syracuseStep 3137747 = 4706621) B4706621
theorem B2091831 : Blo 2091435 2091831 := bstep (se 1 (by rfl) ⟨1568873, by rfl⟩ : syracuseStep 2091831 = 3137747) B3137747
theorem B3529973 : Blo 2091435 3529973 := bbase (se 5 (by rfl) ⟨165467, by rfl⟩ : syracuseStep 3529973 = 330935) (by norm_num)
theorem B2353315 : Blo 2091435 2353315 := bstep (se 1 (by rfl) ⟨1764986, by rfl⟩ : syracuseStep 2353315 = 3529973) B3529973
theorem B3137753 : Blo 2091435 3137753 := bstep (se 2 (by rfl) ⟨1176657, by rfl⟩ : syracuseStep 3137753 = 2353315) B2353315
theorem B2091835 : Blo 2091435 2091835 := bstep (se 1 (by rfl) ⟨1568876, by rfl⟩ : syracuseStep 2091835 = 3137753) B3137753
theorem B11308693 : Blo 2091435 11308693 := bbase (se 6 (by rfl) ⟨265047, by rfl⟩ : syracuseStep 11308693 = 530095) (by norm_num)
theorem B15078257 : Blo 2091435 15078257 := bstep (se 2 (by rfl) ⟨5654346, by rfl⟩ : syracuseStep 15078257 = 11308693) B11308693
theorem B10052171 : Blo 2091435 10052171 := bstep (se 1 (by rfl) ⟨7539128, by rfl⟩ : syracuseStep 10052171 = 15078257) B15078257
theorem B6701447 : Blo 2091435 6701447 := bstep (se 1 (by rfl) ⟨5026085, by rfl⟩ : syracuseStep 6701447 = 10052171) B10052171
theorem B4467631 : Blo 2091435 4467631 := bstep (se 1 (by rfl) ⟨3350723, by rfl⟩ : syracuseStep 4467631 = 6701447) B6701447
theorem B5956841 : Blo 2091435 5956841 := bstep (se 2 (by rfl) ⟨2233815, by rfl⟩ : syracuseStep 5956841 = 4467631) B4467631
theorem B15884909 : Blo 2091435 15884909 := bstep (se 3 (by rfl) ⟨2978420, by rfl⟩ : syracuseStep 15884909 = 5956841) B5956841
theorem B10589939 : Blo 2091435 10589939 := bstep (se 1 (by rfl) ⟨7942454, by rfl⟩ : syracuseStep 10589939 = 15884909) B15884909
theorem B7059959 : Blo 2091435 7059959 := bstep (se 1 (by rfl) ⟨5294969, by rfl⟩ : syracuseStep 7059959 = 10589939) B10589939
theorem B4706639 : Blo 2091435 4706639 := bstep (se 1 (by rfl) ⟨3529979, by rfl⟩ : syracuseStep 4706639 = 7059959) B7059959
theorem B3137759 : Blo 2091435 3137759 := bstep (se 1 (by rfl) ⟨2353319, by rfl⟩ : syracuseStep 3137759 = 4706639) B4706639
theorem B2091839 : Blo 2091435 2091839 := bstep (se 1 (by rfl) ⟨1568879, by rfl⟩ : syracuseStep 2091839 = 3137759) B3137759
theorem B3137765 : Blo 2091435 3137765 := bbase (se 4 (by rfl) ⟨294165, by rfl⟩ : syracuseStep 3137765 = 588331) (by norm_num)
theorem B2091843 : Blo 2091435 2091843 := bstep (se 1 (by rfl) ⟨1568882, by rfl⟩ : syracuseStep 2091843 = 3137765) B3137765
theorem B2513053 : Blo 2091435 2513053 := bbase (se 3 (by rfl) ⟨471197, by rfl⟩ : syracuseStep 2513053 = 942395) (by norm_num)
theorem B3350737 : Blo 2091435 3350737 := bstep (se 2 (by rfl) ⟨1256526, by rfl⟩ : syracuseStep 3350737 = 2513053) B2513053
theorem B4467649 : Blo 2091435 4467649 := bstep (se 2 (by rfl) ⟨1675368, by rfl⟩ : syracuseStep 4467649 = 3350737) B3350737
theorem B5956865 : Blo 2091435 5956865 := bstep (se 2 (by rfl) ⟨2233824, by rfl⟩ : syracuseStep 5956865 = 4467649) B4467649
theorem B3971243 : Blo 2091435 3971243 := bstep (se 1 (by rfl) ⟨2978432, by rfl⟩ : syracuseStep 3971243 = 5956865) B5956865
theorem B2647495 : Blo 2091435 2647495 := bstep (se 1 (by rfl) ⟨1985621, by rfl⟩ : syracuseStep 2647495 = 3971243) B3971243
theorem B3529993 : Blo 2091435 3529993 := bstep (se 2 (by rfl) ⟨1323747, by rfl⟩ : syracuseStep 3529993 = 2647495) B2647495
theorem B4706657 : Blo 2091435 4706657 := bstep (se 2 (by rfl) ⟨1764996, by rfl⟩ : syracuseStep 4706657 = 3529993) B3529993
theorem B3137771 : Blo 2091435 3137771 := bstep (se 1 (by rfl) ⟨2353328, by rfl⟩ : syracuseStep 3137771 = 4706657) B4706657
theorem B2091847 : Blo 2091435 2091847 := bstep (se 1 (by rfl) ⟨1568885, by rfl⟩ : syracuseStep 2091847 = 3137771) B3137771
theorem B2353333 : Blo 2091435 2353333 := bbase (se 5 (by rfl) ⟨110312, by rfl⟩ : syracuseStep 2353333 = 220625) (by norm_num)
theorem B3137777 : Blo 2091435 3137777 := bstep (se 2 (by rfl) ⟨1176666, by rfl⟩ : syracuseStep 3137777 = 2353333) B2353333
theorem B2091851 : Blo 2091435 2091851 := bstep (se 1 (by rfl) ⟨1568888, by rfl⟩ : syracuseStep 2091851 = 3137777) B3137777
theorem B2647505 : Blo 2091435 2647505 := bbase (se 2 (by rfl) ⟨992814, by rfl⟩ : syracuseStep 2647505 = 1985629) (by norm_num)
theorem B7060013 : Blo 2091435 7060013 := bstep (se 3 (by rfl) ⟨1323752, by rfl⟩ : syracuseStep 7060013 = 2647505) B2647505
theorem B4706675 : Blo 2091435 4706675 := bstep (se 1 (by rfl) ⟨3530006, by rfl⟩ : syracuseStep 4706675 = 7060013) B7060013
theorem B3137783 : Blo 2091435 3137783 := bstep (se 1 (by rfl) ⟨2353337, by rfl⟩ : syracuseStep 3137783 = 4706675) B4706675
theorem B2091855 : Blo 2091435 2091855 := bstep (se 1 (by rfl) ⟨1568891, by rfl⟩ : syracuseStep 2091855 = 3137783) B3137783
theorem B3137789 : Blo 2091435 3137789 := bbase (se 3 (by rfl) ⟨588335, by rfl⟩ : syracuseStep 3137789 = 1176671) (by norm_num)
theorem B2091859 : Blo 2091435 2091859 := bstep (se 1 (by rfl) ⟨1568894, by rfl⟩ : syracuseStep 2091859 = 3137789) B3137789
theorem B4706693 : Blo 2091435 4706693 := bbase (se 4 (by rfl) ⟨441252, by rfl⟩ : syracuseStep 4706693 = 882505) (by norm_num)
theorem B3137795 : Blo 2091435 3137795 := bstep (se 1 (by rfl) ⟨2353346, by rfl⟩ : syracuseStep 3137795 = 4706693) B4706693
theorem B2091863 : Blo 2091435 2091863 := bstep (se 1 (by rfl) ⟨1568897, by rfl⟩ : syracuseStep 2091863 = 3137795) B3137795
theorem B2978461 : Blo 2091435 2978461 := bbase (se 3 (by rfl) ⟨558461, by rfl⟩ : syracuseStep 2978461 = 1116923) (by norm_num)
theorem B3971281 : Blo 2091435 3971281 := bstep (se 2 (by rfl) ⟨1489230, by rfl⟩ : syracuseStep 3971281 = 2978461) B2978461
theorem B5295041 : Blo 2091435 5295041 := bstep (se 2 (by rfl) ⟨1985640, by rfl⟩ : syracuseStep 5295041 = 3971281) B3971281
theorem B3530027 : Blo 2091435 3530027 := bstep (se 1 (by rfl) ⟨2647520, by rfl⟩ : syracuseStep 3530027 = 5295041) B5295041
theorem B2353351 : Blo 2091435 2353351 := bstep (se 1 (by rfl) ⟨1765013, by rfl⟩ : syracuseStep 2353351 = 3530027) B3530027
theorem B3137801 : Blo 2091435 3137801 := bstep (se 2 (by rfl) ⟨1176675, by rfl⟩ : syracuseStep 3137801 = 2353351) B2353351
theorem B2091867 : Blo 2091435 2091867 := bstep (se 1 (by rfl) ⟨1568900, by rfl⟩ : syracuseStep 2091867 = 3137801) B3137801
theorem B10590101 : Blo 2091435 10590101 := bbase (se 6 (by rfl) ⟨248205, by rfl⟩ : syracuseStep 10590101 = 496411) (by norm_num)
theorem B7060067 : Blo 2091435 7060067 := bstep (se 1 (by rfl) ⟨5295050, by rfl⟩ : syracuseStep 7060067 = 10590101) B10590101
theorem B4706711 : Blo 2091435 4706711 := bstep (se 1 (by rfl) ⟨3530033, by rfl⟩ : syracuseStep 4706711 = 7060067) B7060067
theorem B3137807 : Blo 2091435 3137807 := bstep (se 1 (by rfl) ⟨2353355, by rfl⟩ : syracuseStep 3137807 = 4706711) B4706711
theorem B2091871 : Blo 2091435 2091871 := bstep (se 1 (by rfl) ⟨1568903, by rfl⟩ : syracuseStep 2091871 = 3137807) B3137807
theorem B3137813 : Blo 2091435 3137813 := bbase (se 6 (by rfl) ⟨73542, by rfl⟩ : syracuseStep 3137813 = 147085) (by norm_num)
theorem B2091875 : Blo 2091435 2091875 := bstep (se 1 (by rfl) ⟨1568906, by rfl⟩ : syracuseStep 2091875 = 3137813) B3137813
theorem B7156421 : Blo 2091435 7156421 := bbase (se 4 (by rfl) ⟨670914, by rfl⟩ : syracuseStep 7156421 = 1341829) (by norm_num)
theorem B4770947 : Blo 2091435 4770947 := bstep (se 1 (by rfl) ⟨3578210, by rfl⟩ : syracuseStep 4770947 = 7156421) B7156421
theorem B3180631 : Blo 2091435 3180631 := bstep (se 1 (by rfl) ⟨2385473, by rfl⟩ : syracuseStep 3180631 = 4770947) B4770947
theorem B4240841 : Blo 2091435 4240841 := bstep (se 2 (by rfl) ⟨1590315, by rfl⟩ : syracuseStep 4240841 = 3180631) B3180631
theorem B11308909 : Blo 2091435 11308909 := bstep (se 3 (by rfl) ⟨2120420, by rfl⟩ : syracuseStep 11308909 = 4240841) B4240841
theorem B15078545 : Blo 2091435 15078545 := bstep (se 2 (by rfl) ⟨5654454, by rfl⟩ : syracuseStep 15078545 = 11308909) B11308909
theorem B10052363 : Blo 2091435 10052363 := bstep (se 1 (by rfl) ⟨7539272, by rfl⟩ : syracuseStep 10052363 = 15078545) B15078545
theorem B26806301 : Blo 2091435 26806301 := bstep (se 3 (by rfl) ⟨5026181, by rfl⟩ : syracuseStep 26806301 = 10052363) B10052363
theorem B17870867 : Blo 2091435 17870867 := bstep (se 1 (by rfl) ⟨13403150, by rfl⟩ : syracuseStep 17870867 = 26806301) B26806301
theorem B11913911 : Blo 2091435 11913911 := bstep (se 1 (by rfl) ⟨8935433, by rfl⟩ : syracuseStep 11913911 = 17870867) B17870867
theorem B7942607 : Blo 2091435 7942607 := bstep (se 1 (by rfl) ⟨5956955, by rfl⟩ : syracuseStep 7942607 = 11913911) B11913911
theorem B5295071 : Blo 2091435 5295071 := bstep (se 1 (by rfl) ⟨3971303, by rfl⟩ : syracuseStep 5295071 = 7942607) B7942607
theorem B3530047 : Blo 2091435 3530047 := bstep (se 1 (by rfl) ⟨2647535, by rfl⟩ : syracuseStep 3530047 = 5295071) B5295071
theorem B4706729 : Blo 2091435 4706729 := bstep (se 2 (by rfl) ⟨1765023, by rfl⟩ : syracuseStep 4706729 = 3530047) B3530047
theorem B3137819 : Blo 2091435 3137819 := bstep (se 1 (by rfl) ⟨2353364, by rfl⟩ : syracuseStep 3137819 = 4706729) B4706729
theorem B2091879 : Blo 2091435 2091879 := bstep (se 1 (by rfl) ⟨1568909, by rfl⟩ : syracuseStep 2091879 = 3137819) B3137819
theorem B2353369 : Blo 2091435 2353369 := bbase (se 2 (by rfl) ⟨882513, by rfl⟩ : syracuseStep 2353369 = 1765027) (by norm_num)
theorem B3137825 : Blo 2091435 3137825 := bstep (se 2 (by rfl) ⟨1176684, by rfl⟩ : syracuseStep 3137825 = 2353369) B2353369
theorem B2091883 : Blo 2091435 2091883 := bstep (se 1 (by rfl) ⟨1568912, by rfl⟩ : syracuseStep 2091883 = 3137825) B3137825
theorem B2513101 : Blo 2091435 2513101 := bbase (se 3 (by rfl) ⟨471206, by rfl⟩ : syracuseStep 2513101 = 942413) (by norm_num)
theorem B3350801 : Blo 2091435 3350801 := bstep (se 2 (by rfl) ⟨1256550, by rfl⟩ : syracuseStep 3350801 = 2513101) B2513101
theorem B2233867 : Blo 2091435 2233867 := bstep (se 1 (by rfl) ⟨1675400, by rfl⟩ : syracuseStep 2233867 = 3350801) B3350801
theorem B2978489 : Blo 2091435 2978489 := bstep (se 2 (by rfl) ⟨1116933, by rfl⟩ : syracuseStep 2978489 = 2233867) B2233867
theorem B7942637 : Blo 2091435 7942637 := bstep (se 3 (by rfl) ⟨1489244, by rfl⟩ : syracuseStep 7942637 = 2978489) B2978489
theorem B5295091 : Blo 2091435 5295091 := bstep (se 1 (by rfl) ⟨3971318, by rfl⟩ : syracuseStep 5295091 = 7942637) B7942637
theorem B7060121 : Blo 2091435 7060121 := bstep (se 2 (by rfl) ⟨2647545, by rfl⟩ : syracuseStep 7060121 = 5295091) B5295091
theorem B4706747 : Blo 2091435 4706747 := bstep (se 1 (by rfl) ⟨3530060, by rfl⟩ : syracuseStep 4706747 = 7060121) B7060121
theorem B3137831 : Blo 2091435 3137831 := bstep (se 1 (by rfl) ⟨2353373, by rfl⟩ : syracuseStep 3137831 = 4706747) B4706747
theorem B2091887 : Blo 2091435 2091887 := bstep (se 1 (by rfl) ⟨1568915, by rfl⟩ : syracuseStep 2091887 = 3137831) B3137831
theorem B3137837 : Blo 2091435 3137837 := bbase (se 3 (by rfl) ⟨588344, by rfl⟩ : syracuseStep 3137837 = 1176689) (by norm_num)
theorem B2091891 : Blo 2091435 2091891 := bstep (se 1 (by rfl) ⟨1568918, by rfl⟩ : syracuseStep 2091891 = 3137837) B3137837
theorem B4706765 : Blo 2091435 4706765 := bbase (se 3 (by rfl) ⟨882518, by rfl⟩ : syracuseStep 4706765 = 1765037) (by norm_num)
theorem B3137843 : Blo 2091435 3137843 := bstep (se 1 (by rfl) ⟨2353382, by rfl⟩ : syracuseStep 3137843 = 4706765) B4706765
theorem B2091895 : Blo 2091435 2091895 := bstep (se 1 (by rfl) ⟨1568921, by rfl⟩ : syracuseStep 2091895 = 3137843) B3137843
theorem B2647561 : Blo 2091435 2647561 := bbase (se 2 (by rfl) ⟨992835, by rfl⟩ : syracuseStep 2647561 = 1985671) (by norm_num)
theorem B3530081 : Blo 2091435 3530081 := bstep (se 2 (by rfl) ⟨1323780, by rfl⟩ : syracuseStep 3530081 = 2647561) B2647561
theorem B2353387 : Blo 2091435 2353387 := bstep (se 1 (by rfl) ⟨1765040, by rfl⟩ : syracuseStep 2353387 = 3530081) B3530081
theorem B3137849 : Blo 2091435 3137849 := bstep (se 2 (by rfl) ⟨1176693, by rfl⟩ : syracuseStep 3137849 = 2353387) B2353387
theorem B2091899 : Blo 2091435 2091899 := bstep (se 1 (by rfl) ⟨1568924, by rfl⟩ : syracuseStep 2091899 = 3137849) B3137849
theorem B2944565 : Blo 2091435 2944565 := bbase (se 5 (by rfl) ⟨138026, by rfl⟩ : syracuseStep 2944565 = 276053) (by norm_num)
theorem B125634773 : Blo 2091435 125634773 := bstep (se 7 (by rfl) ⟨1472282, by rfl⟩ : syracuseStep 125634773 = 2944565) B2944565
theorem B335026061 : Blo 2091435 335026061 := bstep (se 3 (by rfl) ⟨62817386, by rfl⟩ : syracuseStep 335026061 = 125634773) B125634773
theorem B223350707 : Blo 2091435 223350707 := bstep (se 1 (by rfl) ⟨167513030, by rfl⟩ : syracuseStep 223350707 = 335026061) B335026061
theorem B595601885 : Blo 2091435 595601885 := bstep (se 3 (by rfl) ⟨111675353, by rfl⟩ : syracuseStep 595601885 = 223350707) B223350707
theorem B397067923 : Blo 2091435 397067923 := bstep (se 1 (by rfl) ⟨297800942, by rfl⟩ : syracuseStep 397067923 = 595601885) B595601885
theorem B2117695589 : Blo 2091435 2117695589 := bstep (se 4 (by rfl) ⟨198533961, by rfl⟩ : syracuseStep 2117695589 = 397067923) B397067923
theorem B1411797059 : Blo 2091435 1411797059 := bstep (se 1 (by rfl) ⟨1058847794, by rfl⟩ : syracuseStep 1411797059 = 2117695589) B2117695589
theorem B941198039 : Blo 2091435 941198039 := bstep (se 1 (by rfl) ⟨705898529, by rfl⟩ : syracuseStep 941198039 = 1411797059) B1411797059
theorem B627465359 : Blo 2091435 627465359 := bstep (se 1 (by rfl) ⟨470599019, by rfl⟩ : syracuseStep 627465359 = 941198039) B941198039
theorem B418310239 : Blo 2091435 418310239 := bstep (se 1 (by rfl) ⟨313732679, by rfl⟩ : syracuseStep 418310239 = 627465359) B627465359
theorem B557746985 : Blo 2091435 557746985 := bstep (se 2 (by rfl) ⟨209155119, by rfl⟩ : syracuseStep 557746985 = 418310239) B418310239
theorem B371831323 : Blo 2091435 371831323 := bstep (se 1 (by rfl) ⟨278873492, by rfl⟩ : syracuseStep 371831323 = 557746985) B557746985
theorem B495775097 : Blo 2091435 495775097 := bstep (se 2 (by rfl) ⟨185915661, by rfl⟩ : syracuseStep 495775097 = 371831323) B371831323
theorem B330516731 : Blo 2091435 330516731 := bstep (se 1 (by rfl) ⟨247887548, by rfl⟩ : syracuseStep 330516731 = 495775097) B495775097
theorem B881377949 : Blo 2091435 881377949 := bstep (se 3 (by rfl) ⟨165258365, by rfl⟩ : syracuseStep 881377949 = 330516731) B330516731
theorem B587585299 : Blo 2091435 587585299 := bstep (se 1 (by rfl) ⟨440688974, by rfl⟩ : syracuseStep 587585299 = 881377949) B881377949
theorem B783447065 : Blo 2091435 783447065 := bstep (se 2 (by rfl) ⟨293792649, by rfl⟩ : syracuseStep 783447065 = 587585299) B587585299
theorem B522298043 : Blo 2091435 522298043 := bstep (se 1 (by rfl) ⟨391723532, by rfl⟩ : syracuseStep 522298043 = 783447065) B783447065
theorem B348198695 : Blo 2091435 348198695 := bstep (se 1 (by rfl) ⟨261149021, by rfl⟩ : syracuseStep 348198695 = 522298043) B522298043
theorem B232132463 : Blo 2091435 232132463 := bstep (se 1 (by rfl) ⟨174099347, by rfl⟩ : syracuseStep 232132463 = 348198695) B348198695
theorem B154754975 : Blo 2091435 154754975 := bstep (se 1 (by rfl) ⟨116066231, by rfl⟩ : syracuseStep 154754975 = 232132463) B232132463
theorem B103169983 : Blo 2091435 103169983 := bstep (se 1 (by rfl) ⟨77377487, by rfl⟩ : syracuseStep 103169983 = 154754975) B154754975
theorem B137559977 : Blo 2091435 137559977 := bstep (se 2 (by rfl) ⟨51584991, by rfl⟩ : syracuseStep 137559977 = 103169983) B103169983
theorem B91706651 : Blo 2091435 91706651 := bstep (se 1 (by rfl) ⟨68779988, by rfl⟩ : syracuseStep 91706651 = 137559977) B137559977
theorem B61137767 : Blo 2091435 61137767 := bstep (se 1 (by rfl) ⟨45853325, by rfl⟩ : syracuseStep 61137767 = 91706651) B91706651
theorem B40758511 : Blo 2091435 40758511 := bstep (se 1 (by rfl) ⟨30568883, by rfl⟩ : syracuseStep 40758511 = 61137767) B61137767
theorem B54344681 : Blo 2091435 54344681 := bstep (se 2 (by rfl) ⟨20379255, by rfl⟩ : syracuseStep 54344681 = 40758511) B40758511
theorem B36229787 : Blo 2091435 36229787 := bstep (se 1 (by rfl) ⟨27172340, by rfl⟩ : syracuseStep 36229787 = 54344681) B54344681
theorem B24153191 : Blo 2091435 24153191 := bstep (se 1 (by rfl) ⟨18114893, by rfl⟩ : syracuseStep 24153191 = 36229787) B36229787
theorem B16102127 : Blo 2091435 16102127 := bstep (se 1 (by rfl) ⟨12076595, by rfl⟩ : syracuseStep 16102127 = 24153191) B24153191
theorem B10734751 : Blo 2091435 10734751 := bstep (se 1 (by rfl) ⟨8051063, by rfl⟩ : syracuseStep 10734751 = 16102127) B16102127
theorem B57252005 : Blo 2091435 57252005 := bstep (se 4 (by rfl) ⟨5367375, by rfl⟩ : syracuseStep 57252005 = 10734751) B10734751
theorem B38168003 : Blo 2091435 38168003 := bstep (se 1 (by rfl) ⟨28626002, by rfl⟩ : syracuseStep 38168003 = 57252005) B57252005
theorem B25445335 : Blo 2091435 25445335 := bstep (se 1 (by rfl) ⟨19084001, by rfl⟩ : syracuseStep 25445335 = 38168003) B38168003
theorem B33927113 : Blo 2091435 33927113 := bstep (se 2 (by rfl) ⟨12722667, by rfl⟩ : syracuseStep 33927113 = 25445335) B25445335
theorem B22618075 : Blo 2091435 22618075 := bstep (se 1 (by rfl) ⟨16963556, by rfl⟩ : syracuseStep 22618075 = 33927113) B33927113
theorem B30157433 : Blo 2091435 30157433 := bstep (se 2 (by rfl) ⟨11309037, by rfl⟩ : syracuseStep 30157433 = 22618075) B22618075
theorem B20104955 : Blo 2091435 20104955 := bstep (se 1 (by rfl) ⟨15078716, by rfl⟩ : syracuseStep 20104955 = 30157433) B30157433
theorem B13403303 : Blo 2091435 13403303 := bstep (se 1 (by rfl) ⟨10052477, by rfl⟩ : syracuseStep 13403303 = 20104955) B20104955
theorem B8935535 : Blo 2091435 8935535 := bstep (se 1 (by rfl) ⟨6701651, by rfl⟩ : syracuseStep 8935535 = 13403303) B13403303
theorem B23828093 : Blo 2091435 23828093 := bstep (se 3 (by rfl) ⟨4467767, by rfl⟩ : syracuseStep 23828093 = 8935535) B8935535
theorem B15885395 : Blo 2091435 15885395 := bstep (se 1 (by rfl) ⟨11914046, by rfl⟩ : syracuseStep 15885395 = 23828093) B23828093
theorem B10590263 : Blo 2091435 10590263 := bstep (se 1 (by rfl) ⟨7942697, by rfl⟩ : syracuseStep 10590263 = 15885395) B15885395
theorem B7060175 : Blo 2091435 7060175 := bstep (se 1 (by rfl) ⟨5295131, by rfl⟩ : syracuseStep 7060175 = 10590263) B10590263
theorem B4706783 : Blo 2091435 4706783 := bstep (se 1 (by rfl) ⟨3530087, by rfl⟩ : syracuseStep 4706783 = 7060175) B7060175
theorem B3137855 : Blo 2091435 3137855 := bstep (se 1 (by rfl) ⟨2353391, by rfl⟩ : syracuseStep 3137855 = 4706783) B4706783
theorem B2091903 : Blo 2091435 2091903 := bstep (se 1 (by rfl) ⟨1568927, by rfl⟩ : syracuseStep 2091903 = 3137855) B3137855
theorem B3137861 : Blo 2091435 3137861 := bbase (se 4 (by rfl) ⟨294174, by rfl⟩ : syracuseStep 3137861 = 588349) (by norm_num)
theorem B2091907 : Blo 2091435 2091907 := bstep (se 1 (by rfl) ⟨1568930, by rfl⟩ : syracuseStep 2091907 = 3137861) B3137861
theorem B3530101 : Blo 2091435 3530101 := bbase (se 5 (by rfl) ⟨165473, by rfl⟩ : syracuseStep 3530101 = 330947) (by norm_num)
theorem B4706801 : Blo 2091435 4706801 := bstep (se 2 (by rfl) ⟨1765050, by rfl⟩ : syracuseStep 4706801 = 3530101) B3530101
theorem B3137867 : Blo 2091435 3137867 := bstep (se 1 (by rfl) ⟨2353400, by rfl⟩ : syracuseStep 3137867 = 4706801) B4706801
theorem B2091911 : Blo 2091435 2091911 := bstep (se 1 (by rfl) ⟨1568933, by rfl⟩ : syracuseStep 2091911 = 3137867) B3137867
theorem B2353405 : Blo 2091435 2353405 := bbase (se 3 (by rfl) ⟨441263, by rfl⟩ : syracuseStep 2353405 = 882527) (by norm_num)
theorem B3137873 : Blo 2091435 3137873 := bstep (se 2 (by rfl) ⟨1176702, by rfl⟩ : syracuseStep 3137873 = 2353405) B2353405
theorem B2091915 : Blo 2091435 2091915 := bstep (se 1 (by rfl) ⟨1568936, by rfl⟩ : syracuseStep 2091915 = 3137873) B3137873
theorem B7060229 : Blo 2091435 7060229 := bbase (se 4 (by rfl) ⟨661896, by rfl⟩ : syracuseStep 7060229 = 1323793) (by norm_num)
theorem B4706819 : Blo 2091435 4706819 := bstep (se 1 (by rfl) ⟨3530114, by rfl⟩ : syracuseStep 4706819 = 7060229) B7060229
theorem B3137879 : Blo 2091435 3137879 := bstep (se 1 (by rfl) ⟨2353409, by rfl⟩ : syracuseStep 3137879 = 4706819) B4706819
theorem B2091919 : Blo 2091435 2091919 := bstep (se 1 (by rfl) ⟨1568939, by rfl⟩ : syracuseStep 2091919 = 3137879) B3137879
theorem B3137885 : Blo 2091435 3137885 := bbase (se 3 (by rfl) ⟨588353, by rfl⟩ : syracuseStep 3137885 = 1176707) (by norm_num)
theorem B2091923 : Blo 2091435 2091923 := bstep (se 1 (by rfl) ⟨1568942, by rfl⟩ : syracuseStep 2091923 = 3137885) B3137885
theorem B4706837 : Blo 2091435 4706837 := bbase (se 6 (by rfl) ⟨110316, by rfl⟩ : syracuseStep 4706837 = 220633) (by norm_num)
theorem B3137891 : Blo 2091435 3137891 := bstep (se 1 (by rfl) ⟨2353418, by rfl⟩ : syracuseStep 3137891 = 4706837) B4706837
theorem B2091927 : Blo 2091435 2091927 := bstep (se 1 (by rfl) ⟨1568945, by rfl⟩ : syracuseStep 2091927 = 3137891) B3137891
theorem B7942805 : Blo 2091435 7942805 := bbase (se 6 (by rfl) ⟨186159, by rfl⟩ : syracuseStep 7942805 = 372319) (by norm_num)
theorem B5295203 : Blo 2091435 5295203 := bstep (se 1 (by rfl) ⟨3971402, by rfl⟩ : syracuseStep 5295203 = 7942805) B7942805
theorem B3530135 : Blo 2091435 3530135 := bstep (se 1 (by rfl) ⟨2647601, by rfl⟩ : syracuseStep 3530135 = 5295203) B5295203
theorem B2353423 : Blo 2091435 2353423 := bstep (se 1 (by rfl) ⟨1765067, by rfl⟩ : syracuseStep 2353423 = 3530135) B3530135
theorem B3137897 : Blo 2091435 3137897 := bstep (se 2 (by rfl) ⟨1176711, by rfl⟩ : syracuseStep 3137897 = 2353423) B2353423
theorem B2091931 : Blo 2091435 2091931 := bstep (se 1 (by rfl) ⟨1568948, by rfl⟩ : syracuseStep 2091931 = 3137897) B3137897
theorem B11914229 : Blo 2091435 11914229 := bbase (se 5 (by rfl) ⟨558479, by rfl⟩ : syracuseStep 11914229 = 1116959) (by norm_num)
theorem B7942819 : Blo 2091435 7942819 := bstep (se 1 (by rfl) ⟨5957114, by rfl⟩ : syracuseStep 7942819 = 11914229) B11914229
theorem B10590425 : Blo 2091435 10590425 := bstep (se 2 (by rfl) ⟨3971409, by rfl⟩ : syracuseStep 10590425 = 7942819) B7942819
theorem B7060283 : Blo 2091435 7060283 := bstep (se 1 (by rfl) ⟨5295212, by rfl⟩ : syracuseStep 7060283 = 10590425) B10590425
theorem B4706855 : Blo 2091435 4706855 := bstep (se 1 (by rfl) ⟨3530141, by rfl⟩ : syracuseStep 4706855 = 7060283) B7060283
theorem B3137903 : Blo 2091435 3137903 := bstep (se 1 (by rfl) ⟨2353427, by rfl⟩ : syracuseStep 3137903 = 4706855) B4706855
theorem B2091935 : Blo 2091435 2091935 := bstep (se 1 (by rfl) ⟨1568951, by rfl⟩ : syracuseStep 2091935 = 3137903) B3137903
theorem B3137909 : Blo 2091435 3137909 := bbase (se 5 (by rfl) ⟨147089, by rfl⟩ : syracuseStep 3137909 = 294179) (by norm_num)
theorem B2091939 : Blo 2091435 2091939 := bstep (se 1 (by rfl) ⟨1568954, by rfl⟩ : syracuseStep 2091939 = 3137909) B3137909
theorem B4240973 : Blo 2091435 4240973 := bbase (se 3 (by rfl) ⟨795182, by rfl⟩ : syracuseStep 4240973 = 1590365) (by norm_num)
theorem B2827315 : Blo 2091435 2827315 := bstep (se 1 (by rfl) ⟨2120486, by rfl⟩ : syracuseStep 2827315 = 4240973) B4240973
theorem B3769753 : Blo 2091435 3769753 := bstep (se 2 (by rfl) ⟨1413657, by rfl⟩ : syracuseStep 3769753 = 2827315) B2827315
theorem B5026337 : Blo 2091435 5026337 := bstep (se 2 (by rfl) ⟨1884876, by rfl⟩ : syracuseStep 5026337 = 3769753) B3769753
theorem B3350891 : Blo 2091435 3350891 := bstep (se 1 (by rfl) ⟨2513168, by rfl⟩ : syracuseStep 3350891 = 5026337) B5026337
theorem B2233927 : Blo 2091435 2233927 := bstep (se 1 (by rfl) ⟨1675445, by rfl⟩ : syracuseStep 2233927 = 3350891) B3350891
theorem B2978569 : Blo 2091435 2978569 := bstep (se 2 (by rfl) ⟨1116963, by rfl⟩ : syracuseStep 2978569 = 2233927) B2233927
theorem B3971425 : Blo 2091435 3971425 := bstep (se 2 (by rfl) ⟨1489284, by rfl⟩ : syracuseStep 3971425 = 2978569) B2978569
theorem B5295233 : Blo 2091435 5295233 := bstep (se 2 (by rfl) ⟨1985712, by rfl⟩ : syracuseStep 5295233 = 3971425) B3971425
theorem B3530155 : Blo 2091435 3530155 := bstep (se 1 (by rfl) ⟨2647616, by rfl⟩ : syracuseStep 3530155 = 5295233) B5295233
theorem B4706873 : Blo 2091435 4706873 := bstep (se 2 (by rfl) ⟨1765077, by rfl⟩ : syracuseStep 4706873 = 3530155) B3530155
theorem B3137915 : Blo 2091435 3137915 := bstep (se 1 (by rfl) ⟨2353436, by rfl⟩ : syracuseStep 3137915 = 4706873) B4706873
theorem B2091943 : Blo 2091435 2091943 := bstep (se 1 (by rfl) ⟨1568957, by rfl⟩ : syracuseStep 2091943 = 3137915) B3137915
theorem B2353441 : Blo 2091435 2353441 := bbase (se 2 (by rfl) ⟨882540, by rfl⟩ : syracuseStep 2353441 = 1765081) (by norm_num)
theorem B3137921 : Blo 2091435 3137921 := bstep (se 2 (by rfl) ⟨1176720, by rfl⟩ : syracuseStep 3137921 = 2353441) B2353441
theorem B2091947 : Blo 2091435 2091947 := bstep (se 1 (by rfl) ⟨1568960, by rfl⟩ : syracuseStep 2091947 = 3137921) B3137921
theorem B5295253 : Blo 2091435 5295253 := bbase (se 6 (by rfl) ⟨124107, by rfl⟩ : syracuseStep 5295253 = 248215) (by norm_num)
theorem B7060337 : Blo 2091435 7060337 := bstep (se 2 (by rfl) ⟨2647626, by rfl⟩ : syracuseStep 7060337 = 5295253) B5295253
theorem B4706891 : Blo 2091435 4706891 := bstep (se 1 (by rfl) ⟨3530168, by rfl⟩ : syracuseStep 4706891 = 7060337) B7060337
theorem B3137927 : Blo 2091435 3137927 := bstep (se 1 (by rfl) ⟨2353445, by rfl⟩ : syracuseStep 3137927 = 4706891) B4706891
theorem B2091951 : Blo 2091435 2091951 := bstep (se 1 (by rfl) ⟨1568963, by rfl⟩ : syracuseStep 2091951 = 3137927) B3137927
theorem B3137933 : Blo 2091435 3137933 := bbase (se 3 (by rfl) ⟨588362, by rfl⟩ : syracuseStep 3137933 = 1176725) (by norm_num)
theorem B2091955 : Blo 2091435 2091955 := bstep (se 1 (by rfl) ⟨1568966, by rfl⟩ : syracuseStep 2091955 = 3137933) B3137933
theorem B4706909 : Blo 2091435 4706909 := bbase (se 3 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 4706909 = 1765091) (by norm_num)
theorem B3137939 : Blo 2091435 3137939 := bstep (se 1 (by rfl) ⟨2353454, by rfl⟩ : syracuseStep 3137939 = 4706909) B4706909
theorem B2091959 : Blo 2091435 2091959 := bstep (se 1 (by rfl) ⟨1568969, by rfl⟩ : syracuseStep 2091959 = 3137939) B3137939
theorem B3530189 : Blo 2091435 3530189 := bbase (se 3 (by rfl) ⟨661910, by rfl⟩ : syracuseStep 3530189 = 1323821) (by norm_num)
theorem B2353459 : Blo 2091435 2353459 := bstep (se 1 (by rfl) ⟨1765094, by rfl⟩ : syracuseStep 2353459 = 3530189) B3530189
theorem B3137945 : Blo 2091435 3137945 := bstep (se 2 (by rfl) ⟨1176729, by rfl⟩ : syracuseStep 3137945 = 2353459) B2353459
theorem B2091963 : Blo 2091435 2091963 := bstep (se 1 (by rfl) ⟨1568972, by rfl⟩ : syracuseStep 2091963 = 3137945) B3137945
theorem B7539589 : Blo 2091435 7539589 := bbase (se 4 (by rfl) ⟨706836, by rfl⟩ : syracuseStep 7539589 = 1413673) (by norm_num)
theorem B10052785 : Blo 2091435 10052785 := bstep (se 2 (by rfl) ⟨3769794, by rfl⟩ : syracuseStep 10052785 = 7539589) B7539589
theorem B13403713 : Blo 2091435 13403713 := bstep (se 2 (by rfl) ⟨5026392, by rfl⟩ : syracuseStep 13403713 = 10052785) B10052785
theorem B17871617 : Blo 2091435 17871617 := bstep (se 2 (by rfl) ⟨6701856, by rfl⟩ : syracuseStep 17871617 = 13403713) B13403713
theorem B11914411 : Blo 2091435 11914411 := bstep (se 1 (by rfl) ⟨8935808, by rfl⟩ : syracuseStep 11914411 = 17871617) B17871617
theorem B15885881 : Blo 2091435 15885881 := bstep (se 2 (by rfl) ⟨5957205, by rfl⟩ : syracuseStep 15885881 = 11914411) B11914411
theorem B10590587 : Blo 2091435 10590587 := bstep (se 1 (by rfl) ⟨7942940, by rfl⟩ : syracuseStep 10590587 = 15885881) B15885881
theorem B7060391 : Blo 2091435 7060391 := bstep (se 1 (by rfl) ⟨5295293, by rfl⟩ : syracuseStep 7060391 = 10590587) B10590587
theorem B4706927 : Blo 2091435 4706927 := bstep (se 1 (by rfl) ⟨3530195, by rfl⟩ : syracuseStep 4706927 = 7060391) B7060391
theorem B3137951 : Blo 2091435 3137951 := bstep (se 1 (by rfl) ⟨2353463, by rfl⟩ : syracuseStep 3137951 = 4706927) B4706927
theorem B2091967 : Blo 2091435 2091967 := bstep (se 1 (by rfl) ⟨1568975, by rfl⟩ : syracuseStep 2091967 = 3137951) B3137951
theorem B3137957 : Blo 2091435 3137957 := bbase (se 4 (by rfl) ⟨294183, by rfl⟩ : syracuseStep 3137957 = 588367) (by norm_num)
theorem B2091971 : Blo 2091435 2091971 := bstep (se 1 (by rfl) ⟨1568978, by rfl⟩ : syracuseStep 2091971 = 3137957) B3137957
theorem B2647657 : Blo 2091435 2647657 := bbase (se 2 (by rfl) ⟨992871, by rfl⟩ : syracuseStep 2647657 = 1985743) (by norm_num)
theorem B3530209 : Blo 2091435 3530209 := bstep (se 2 (by rfl) ⟨1323828, by rfl⟩ : syracuseStep 3530209 = 2647657) B2647657
theorem B4706945 : Blo 2091435 4706945 := bstep (se 2 (by rfl) ⟨1765104, by rfl⟩ : syracuseStep 4706945 = 3530209) B3530209
theorem B3137963 : Blo 2091435 3137963 := bstep (se 1 (by rfl) ⟨2353472, by rfl⟩ : syracuseStep 3137963 = 4706945) B4706945
theorem B2091975 : Blo 2091435 2091975 := bstep (se 1 (by rfl) ⟨1568981, by rfl⟩ : syracuseStep 2091975 = 3137963) B3137963
theorem B2353477 : Blo 2091435 2353477 := bbase (se 4 (by rfl) ⟨220638, by rfl⟩ : syracuseStep 2353477 = 441277) (by norm_num)
theorem B3137969 : Blo 2091435 3137969 := bstep (se 2 (by rfl) ⟨1176738, by rfl⟩ : syracuseStep 3137969 = 2353477) B2353477
theorem B2091979 : Blo 2091435 2091979 := bstep (se 1 (by rfl) ⟨1568984, by rfl⟩ : syracuseStep 2091979 = 3137969) B3137969
theorem B3971501 : Blo 2091435 3971501 := bbase (se 3 (by rfl) ⟨744656, by rfl⟩ : syracuseStep 3971501 = 1489313) (by norm_num)
theorem B2647667 : Blo 2091435 2647667 := bstep (se 1 (by rfl) ⟨1985750, by rfl⟩ : syracuseStep 2647667 = 3971501) B3971501
theorem B7060445 : Blo 2091435 7060445 := bstep (se 3 (by rfl) ⟨1323833, by rfl⟩ : syracuseStep 7060445 = 2647667) B2647667
theorem B4706963 : Blo 2091435 4706963 := bstep (se 1 (by rfl) ⟨3530222, by rfl⟩ : syracuseStep 4706963 = 7060445) B7060445
theorem B3137975 : Blo 2091435 3137975 := bstep (se 1 (by rfl) ⟨2353481, by rfl⟩ : syracuseStep 3137975 = 4706963) B4706963
theorem B2091983 : Blo 2091435 2091983 := bstep (se 1 (by rfl) ⟨1568987, by rfl⟩ : syracuseStep 2091983 = 3137975) B3137975
theorem B3137981 : Blo 2091435 3137981 := bbase (se 3 (by rfl) ⟨588371, by rfl⟩ : syracuseStep 3137981 = 1176743) (by norm_num)
theorem B2091987 : Blo 2091435 2091987 := bstep (se 1 (by rfl) ⟨1568990, by rfl⟩ : syracuseStep 2091987 = 3137981) B3137981
theorem B4706981 : Blo 2091435 4706981 := bbase (se 4 (by rfl) ⟨441279, by rfl⟩ : syracuseStep 4706981 = 882559) (by norm_num)
theorem B3137987 : Blo 2091435 3137987 := bstep (se 1 (by rfl) ⟨2353490, by rfl⟩ : syracuseStep 3137987 = 4706981) B4706981
theorem B2091991 : Blo 2091435 2091991 := bstep (se 1 (by rfl) ⟨1568993, by rfl⟩ : syracuseStep 2091991 = 3137987) B3137987
theorem B5295365 : Blo 2091435 5295365 := bbase (se 4 (by rfl) ⟨496440, by rfl⟩ : syracuseStep 5295365 = 992881) (by norm_num)
theorem B3530243 : Blo 2091435 3530243 := bstep (se 1 (by rfl) ⟨2647682, by rfl⟩ : syracuseStep 3530243 = 5295365) B5295365
theorem B2353495 : Blo 2091435 2353495 := bstep (se 1 (by rfl) ⟨1765121, by rfl⟩ : syracuseStep 2353495 = 3530243) B3530243
theorem B3137993 : Blo 2091435 3137993 := bstep (se 2 (by rfl) ⟨1176747, by rfl⟩ : syracuseStep 3137993 = 2353495) B2353495
theorem B2091995 : Blo 2091435 2091995 := bstep (se 1 (by rfl) ⟨1568996, by rfl⟩ : syracuseStep 2091995 = 3137993) B3137993
theorem B4467973 : Blo 2091435 4467973 := bbase (se 4 (by rfl) ⟨418872, by rfl⟩ : syracuseStep 4467973 = 837745) (by norm_num)
theorem B5957297 : Blo 2091435 5957297 := bstep (se 2 (by rfl) ⟨2233986, by rfl⟩ : syracuseStep 5957297 = 4467973) B4467973
theorem B3971531 : Blo 2091435 3971531 := bstep (se 1 (by rfl) ⟨2978648, by rfl⟩ : syracuseStep 3971531 = 5957297) B5957297
theorem B10590749 : Blo 2091435 10590749 := bstep (se 3 (by rfl) ⟨1985765, by rfl⟩ : syracuseStep 10590749 = 3971531) B3971531
theorem B7060499 : Blo 2091435 7060499 := bstep (se 1 (by rfl) ⟨5295374, by rfl⟩ : syracuseStep 7060499 = 10590749) B10590749
theorem B4706999 : Blo 2091435 4706999 := bstep (se 1 (by rfl) ⟨3530249, by rfl⟩ : syracuseStep 4706999 = 7060499) B7060499
theorem B3137999 : Blo 2091435 3137999 := bstep (se 1 (by rfl) ⟨2353499, by rfl⟩ : syracuseStep 3137999 = 4706999) B4706999
theorem B2091999 : Blo 2091435 2091999 := bstep (se 1 (by rfl) ⟨1568999, by rfl⟩ : syracuseStep 2091999 = 3137999) B3137999
theorem B3138005 : Blo 2091435 3138005 := bbase (se 7 (by rfl) ⟨36773, by rfl⟩ : syracuseStep 3138005 = 73547) (by norm_num)
theorem B2092003 : Blo 2091435 2092003 := bstep (se 1 (by rfl) ⟨1569002, by rfl⟩ : syracuseStep 2092003 = 3138005) B3138005
theorem B7943093 : Blo 2091435 7943093 := bbase (se 5 (by rfl) ⟨372332, by rfl⟩ : syracuseStep 7943093 = 744665) (by norm_num)
theorem B5295395 : Blo 2091435 5295395 := bstep (se 1 (by rfl) ⟨3971546, by rfl⟩ : syracuseStep 5295395 = 7943093) B7943093
theorem B3530263 : Blo 2091435 3530263 := bstep (se 1 (by rfl) ⟨2647697, by rfl⟩ : syracuseStep 3530263 = 5295395) B5295395
theorem B4707017 : Blo 2091435 4707017 := bstep (se 2 (by rfl) ⟨1765131, by rfl⟩ : syracuseStep 4707017 = 3530263) B3530263
theorem B3138011 : Blo 2091435 3138011 := bstep (se 1 (by rfl) ⟨2353508, by rfl⟩ : syracuseStep 3138011 = 4707017) B4707017
theorem B2092007 : Blo 2091435 2092007 := bstep (se 1 (by rfl) ⟨1569005, by rfl⟩ : syracuseStep 2092007 = 3138011) B3138011
theorem B2353513 : Blo 2091435 2353513 := bbase (se 2 (by rfl) ⟨882567, by rfl⟩ : syracuseStep 2353513 = 1765135) (by norm_num)
theorem B3138017 : Blo 2091435 3138017 := bstep (se 2 (by rfl) ⟨1176756, by rfl⟩ : syracuseStep 3138017 = 2353513) B2353513
theorem B2092011 : Blo 2091435 2092011 := bstep (se 1 (by rfl) ⟨1569008, by rfl⟩ : syracuseStep 2092011 = 3138017) B3138017
theorem B4241117 : Blo 2091435 4241117 := bbase (se 3 (by rfl) ⟨795209, by rfl⟩ : syracuseStep 4241117 = 1590419) (by norm_num)
theorem B11309645 : Blo 2091435 11309645 := bstep (se 3 (by rfl) ⟨2120558, by rfl⟩ : syracuseStep 11309645 = 4241117) B4241117
theorem B7539763 : Blo 2091435 7539763 := bstep (se 1 (by rfl) ⟨5654822, by rfl⟩ : syracuseStep 7539763 = 11309645) B11309645
theorem B10053017 : Blo 2091435 10053017 := bstep (se 2 (by rfl) ⟨3769881, by rfl⟩ : syracuseStep 10053017 = 7539763) B7539763
theorem B6702011 : Blo 2091435 6702011 := bstep (se 1 (by rfl) ⟨5026508, by rfl⟩ : syracuseStep 6702011 = 10053017) B10053017
theorem B4468007 : Blo 2091435 4468007 := bstep (se 1 (by rfl) ⟨3351005, by rfl⟩ : syracuseStep 4468007 = 6702011) B6702011
theorem B11914685 : Blo 2091435 11914685 := bstep (se 3 (by rfl) ⟨2234003, by rfl⟩ : syracuseStep 11914685 = 4468007) B4468007
theorem B7943123 : Blo 2091435 7943123 := bstep (se 1 (by rfl) ⟨5957342, by rfl⟩ : syracuseStep 7943123 = 11914685) B11914685
theorem B5295415 : Blo 2091435 5295415 := bstep (se 1 (by rfl) ⟨3971561, by rfl⟩ : syracuseStep 5295415 = 7943123) B7943123
theorem B7060553 : Blo 2091435 7060553 := bstep (se 2 (by rfl) ⟨2647707, by rfl⟩ : syracuseStep 7060553 = 5295415) B5295415
theorem B4707035 : Blo 2091435 4707035 := bstep (se 1 (by rfl) ⟨3530276, by rfl⟩ : syracuseStep 4707035 = 7060553) B7060553
theorem B3138023 : Blo 2091435 3138023 := bstep (se 1 (by rfl) ⟨2353517, by rfl⟩ : syracuseStep 3138023 = 4707035) B4707035
theorem B2092015 : Blo 2091435 2092015 := bstep (se 1 (by rfl) ⟨1569011, by rfl⟩ : syracuseStep 2092015 = 3138023) B3138023
theorem B3138029 : Blo 2091435 3138029 := bbase (se 3 (by rfl) ⟨588380, by rfl⟩ : syracuseStep 3138029 = 1176761) (by norm_num)
theorem B2092019 : Blo 2091435 2092019 := bstep (se 1 (by rfl) ⟨1569014, by rfl⟩ : syracuseStep 2092019 = 3138029) B3138029
theorem B4707053 : Blo 2091435 4707053 := bbase (se 3 (by rfl) ⟨882572, by rfl⟩ : syracuseStep 4707053 = 1765145) (by norm_num)
theorem B3138035 : Blo 2091435 3138035 := bstep (se 1 (by rfl) ⟨2353526, by rfl⟩ : syracuseStep 3138035 = 4707053) B4707053
theorem B2092023 : Blo 2091435 2092023 := bstep (se 1 (by rfl) ⟨1569017, by rfl⟩ : syracuseStep 2092023 = 3138035) B3138035
theorem B2234017 : Blo 2091435 2234017 := bbase (se 2 (by rfl) ⟨837756, by rfl⟩ : syracuseStep 2234017 = 1675513) (by norm_num)
theorem B2978689 : Blo 2091435 2978689 := bstep (se 2 (by rfl) ⟨1117008, by rfl⟩ : syracuseStep 2978689 = 2234017) B2234017
theorem B3971585 : Blo 2091435 3971585 := bstep (se 2 (by rfl) ⟨1489344, by rfl⟩ : syracuseStep 3971585 = 2978689) B2978689
theorem B2647723 : Blo 2091435 2647723 := bstep (se 1 (by rfl) ⟨1985792, by rfl⟩ : syracuseStep 2647723 = 3971585) B3971585
theorem B3530297 : Blo 2091435 3530297 := bstep (se 2 (by rfl) ⟨1323861, by rfl⟩ : syracuseStep 3530297 = 2647723) B2647723
theorem B2353531 : Blo 2091435 2353531 := bstep (se 1 (by rfl) ⟨1765148, by rfl⟩ : syracuseStep 2353531 = 3530297) B3530297
theorem B3138041 : Blo 2091435 3138041 := bstep (se 2 (by rfl) ⟨1176765, by rfl⟩ : syracuseStep 3138041 = 2353531) B2353531
theorem B2092027 : Blo 2091435 2092027 := bstep (se 1 (by rfl) ⟨1569020, by rfl⟩ : syracuseStep 2092027 = 3138041) B3138041
theorem B12723445 : Blo 2091435 12723445 := bbase (se 5 (by rfl) ⟨596411, by rfl⟩ : syracuseStep 12723445 = 1192823) (by norm_num)
theorem B67858373 : Blo 2091435 67858373 := bstep (se 4 (by rfl) ⟨6361722, by rfl⟩ : syracuseStep 67858373 = 12723445) B12723445
theorem B45238915 : Blo 2091435 45238915 := bstep (se 1 (by rfl) ⟨33929186, by rfl⟩ : syracuseStep 45238915 = 67858373) B67858373
theorem B60318553 : Blo 2091435 60318553 := bstep (se 2 (by rfl) ⟨22619457, by rfl⟩ : syracuseStep 60318553 = 45238915) B45238915
theorem B80424737 : Blo 2091435 80424737 := bstep (se 2 (by rfl) ⟨30159276, by rfl⟩ : syracuseStep 80424737 = 60318553) B60318553
theorem B53616491 : Blo 2091435 53616491 := bstep (se 1 (by rfl) ⟨40212368, by rfl⟩ : syracuseStep 53616491 = 80424737) B80424737
theorem B35744327 : Blo 2091435 35744327 := bstep (se 1 (by rfl) ⟨26808245, by rfl⟩ : syracuseStep 35744327 = 53616491) B53616491
theorem B23829551 : Blo 2091435 23829551 := bstep (se 1 (by rfl) ⟨17872163, by rfl⟩ : syracuseStep 23829551 = 35744327) B35744327
theorem B15886367 : Blo 2091435 15886367 := bstep (se 1 (by rfl) ⟨11914775, by rfl⟩ : syracuseStep 15886367 = 23829551) B23829551
theorem B10590911 : Blo 2091435 10590911 := bstep (se 1 (by rfl) ⟨7943183, by rfl⟩ : syracuseStep 10590911 = 15886367) B15886367
theorem B7060607 : Blo 2091435 7060607 := bstep (se 1 (by rfl) ⟨5295455, by rfl⟩ : syracuseStep 7060607 = 10590911) B10590911
theorem B4707071 : Blo 2091435 4707071 := bstep (se 1 (by rfl) ⟨3530303, by rfl⟩ : syracuseStep 4707071 = 7060607) B7060607
theorem B3138047 : Blo 2091435 3138047 := bstep (se 1 (by rfl) ⟨2353535, by rfl⟩ : syracuseStep 3138047 = 4707071) B4707071
theorem B2092031 : Blo 2091435 2092031 := bstep (se 1 (by rfl) ⟨1569023, by rfl⟩ : syracuseStep 2092031 = 3138047) B3138047
theorem B3138053 : Blo 2091435 3138053 := bbase (se 4 (by rfl) ⟨294192, by rfl⟩ : syracuseStep 3138053 = 588385) (by norm_num)
theorem B2092035 : Blo 2091435 2092035 := bstep (se 1 (by rfl) ⟨1569026, by rfl⟩ : syracuseStep 2092035 = 3138053) B3138053
theorem B3530317 : Blo 2091435 3530317 := bbase (se 3 (by rfl) ⟨661934, by rfl⟩ : syracuseStep 3530317 = 1323869) (by norm_num)
theorem B4707089 : Blo 2091435 4707089 := bstep (se 2 (by rfl) ⟨1765158, by rfl⟩ : syracuseStep 4707089 = 3530317) B3530317
theorem B3138059 : Blo 2091435 3138059 := bstep (se 1 (by rfl) ⟨2353544, by rfl⟩ : syracuseStep 3138059 = 4707089) B4707089
theorem B2092039 : Blo 2091435 2092039 := bstep (se 1 (by rfl) ⟨1569029, by rfl⟩ : syracuseStep 2092039 = 3138059) B3138059
theorem B2353549 : Blo 2091435 2353549 := bbase (se 3 (by rfl) ⟨441290, by rfl⟩ : syracuseStep 2353549 = 882581) (by norm_num)
theorem B3138065 : Blo 2091435 3138065 := bstep (se 2 (by rfl) ⟨1176774, by rfl⟩ : syracuseStep 3138065 = 2353549) B2353549
theorem B2092043 : Blo 2091435 2092043 := bstep (se 1 (by rfl) ⟨1569032, by rfl⟩ : syracuseStep 2092043 = 3138065) B3138065
theorem B7060661 : Blo 2091435 7060661 := bbase (se 5 (by rfl) ⟨330968, by rfl⟩ : syracuseStep 7060661 = 661937) (by norm_num)
theorem B4707107 : Blo 2091435 4707107 := bstep (se 1 (by rfl) ⟨3530330, by rfl⟩ : syracuseStep 4707107 = 7060661) B7060661
theorem B3138071 : Blo 2091435 3138071 := bstep (se 1 (by rfl) ⟨2353553, by rfl⟩ : syracuseStep 3138071 = 4707107) B4707107
theorem B2092047 : Blo 2091435 2092047 := bstep (se 1 (by rfl) ⟨1569035, by rfl⟩ : syracuseStep 2092047 = 3138071) B3138071
theorem B3138077 : Blo 2091435 3138077 := bbase (se 3 (by rfl) ⟨588389, by rfl⟩ : syracuseStep 3138077 = 1176779) (by norm_num)
theorem B2092051 : Blo 2091435 2092051 := bstep (se 1 (by rfl) ⟨1569038, by rfl⟩ : syracuseStep 2092051 = 3138077) B3138077
theorem B4707125 : Blo 2091435 4707125 := bbase (se 5 (by rfl) ⟨220646, by rfl⟩ : syracuseStep 4707125 = 441293) (by norm_num)
theorem B3138083 : Blo 2091435 3138083 := bstep (se 1 (by rfl) ⟨2353562, by rfl⟩ : syracuseStep 3138083 = 4707125) B4707125
theorem B2092055 : Blo 2091435 2092055 := bstep (se 1 (by rfl) ⟨1569041, by rfl⟩ : syracuseStep 2092055 = 3138083) B3138083
theorem B8051669 : Blo 2091435 8051669 := bbase (se 7 (by rfl) ⟨94355, by rfl⟩ : syracuseStep 8051669 = 188711) (by norm_num)
theorem B5367779 : Blo 2091435 5367779 := bstep (se 1 (by rfl) ⟨4025834, by rfl⟩ : syracuseStep 5367779 = 8051669) B8051669
theorem B3578519 : Blo 2091435 3578519 := bstep (se 1 (by rfl) ⟨2683889, by rfl⟩ : syracuseStep 3578519 = 5367779) B5367779
theorem B9542717 : Blo 2091435 9542717 := bstep (se 3 (by rfl) ⟨1789259, by rfl⟩ : syracuseStep 9542717 = 3578519) B3578519
theorem B6361811 : Blo 2091435 6361811 := bstep (se 1 (by rfl) ⟨4771358, by rfl⟩ : syracuseStep 6361811 = 9542717) B9542717
theorem B4241207 : Blo 2091435 4241207 := bstep (se 1 (by rfl) ⟨3180905, by rfl⟩ : syracuseStep 4241207 = 6361811) B6361811
theorem B2827471 : Blo 2091435 2827471 := bstep (se 1 (by rfl) ⟨2120603, by rfl⟩ : syracuseStep 2827471 = 4241207) B4241207
theorem B3769961 : Blo 2091435 3769961 := bstep (se 2 (by rfl) ⟨1413735, by rfl⟩ : syracuseStep 3769961 = 2827471) B2827471
theorem B10053229 : Blo 2091435 10053229 := bstep (se 3 (by rfl) ⟨1884980, by rfl⟩ : syracuseStep 10053229 = 3769961) B3769961
theorem B13404305 : Blo 2091435 13404305 := bstep (se 2 (by rfl) ⟨5026614, by rfl⟩ : syracuseStep 13404305 = 10053229) B10053229
theorem B8936203 : Blo 2091435 8936203 := bstep (se 1 (by rfl) ⟨6702152, by rfl⟩ : syracuseStep 8936203 = 13404305) B13404305
theorem B11914937 : Blo 2091435 11914937 := bstep (se 2 (by rfl) ⟨4468101, by rfl⟩ : syracuseStep 11914937 = 8936203) B8936203
theorem B7943291 : Blo 2091435 7943291 := bstep (se 1 (by rfl) ⟨5957468, by rfl⟩ : syracuseStep 7943291 = 11914937) B11914937
theorem B5295527 : Blo 2091435 5295527 := bstep (se 1 (by rfl) ⟨3971645, by rfl⟩ : syracuseStep 5295527 = 7943291) B7943291
theorem B3530351 : Blo 2091435 3530351 := bstep (se 1 (by rfl) ⟨2647763, by rfl⟩ : syracuseStep 3530351 = 5295527) B5295527
theorem B2353567 : Blo 2091435 2353567 := bstep (se 1 (by rfl) ⟨1765175, by rfl⟩ : syracuseStep 2353567 = 3530351) B3530351
theorem B3138089 : Blo 2091435 3138089 := bstep (se 2 (by rfl) ⟨1176783, by rfl⟩ : syracuseStep 3138089 = 2353567) B2353567
theorem B2092059 : Blo 2091435 2092059 := bstep (se 1 (by rfl) ⟨1569044, by rfl⟩ : syracuseStep 2092059 = 3138089) B3138089
theorem B3676837 : Blo 2091435 3676837 := bbase (se 4 (by rfl) ⟨344703, by rfl⟩ : syracuseStep 3676837 = 689407) (by norm_num)
theorem B4902449 : Blo 2091435 4902449 := bstep (se 2 (by rfl) ⟨1838418, by rfl⟩ : syracuseStep 4902449 = 3676837) B3676837
theorem B52292789 : Blo 2091435 52292789 := bstep (se 5 (by rfl) ⟨2451224, by rfl⟩ : syracuseStep 52292789 = 4902449) B4902449
theorem B34861859 : Blo 2091435 34861859 := bstep (se 1 (by rfl) ⟨26146394, by rfl⟩ : syracuseStep 34861859 = 52292789) B52292789
theorem B23241239 : Blo 2091435 23241239 := bstep (se 1 (by rfl) ⟨17430929, by rfl⟩ : syracuseStep 23241239 = 34861859) B34861859
theorem B15494159 : Blo 2091435 15494159 := bstep (se 1 (by rfl) ⟨11620619, by rfl⟩ : syracuseStep 15494159 = 23241239) B23241239
theorem B10329439 : Blo 2091435 10329439 := bstep (se 1 (by rfl) ⟨7747079, by rfl⟩ : syracuseStep 10329439 = 15494159) B15494159
theorem B13772585 : Blo 2091435 13772585 := bstep (se 2 (by rfl) ⟨5164719, by rfl⟩ : syracuseStep 13772585 = 10329439) B10329439
theorem B9181723 : Blo 2091435 9181723 := bstep (se 1 (by rfl) ⟨6886292, by rfl⟩ : syracuseStep 9181723 = 13772585) B13772585
theorem B12242297 : Blo 2091435 12242297 := bstep (se 2 (by rfl) ⟨4590861, by rfl⟩ : syracuseStep 12242297 = 9181723) B9181723
theorem B32646125 : Blo 2091435 32646125 := bstep (se 3 (by rfl) ⟨6121148, by rfl⟩ : syracuseStep 32646125 = 12242297) B12242297
theorem B87056333 : Blo 2091435 87056333 := bstep (se 3 (by rfl) ⟨16323062, by rfl⟩ : syracuseStep 87056333 = 32646125) B32646125
theorem B58037555 : Blo 2091435 58037555 := bstep (se 1 (by rfl) ⟨43528166, by rfl⟩ : syracuseStep 58037555 = 87056333) B87056333
theorem B38691703 : Blo 2091435 38691703 := bstep (se 1 (by rfl) ⟨29018777, by rfl⟩ : syracuseStep 38691703 = 58037555) B58037555
theorem B51588937 : Blo 2091435 51588937 := bstep (se 2 (by rfl) ⟨19345851, by rfl⟩ : syracuseStep 51588937 = 38691703) B38691703
theorem B68785249 : Blo 2091435 68785249 := bstep (se 2 (by rfl) ⟨25794468, by rfl⟩ : syracuseStep 68785249 = 51588937) B51588937
theorem B91713665 : Blo 2091435 91713665 := bstep (se 2 (by rfl) ⟨34392624, by rfl⟩ : syracuseStep 91713665 = 68785249) B68785249
theorem B244569773 : Blo 2091435 244569773 := bstep (se 3 (by rfl) ⟨45856832, by rfl⟩ : syracuseStep 244569773 = 91713665) B91713665
theorem B163046515 : Blo 2091435 163046515 := bstep (se 1 (by rfl) ⟨122284886, by rfl⟩ : syracuseStep 163046515 = 244569773) B244569773
theorem B217395353 : Blo 2091435 217395353 := bstep (se 2 (by rfl) ⟨81523257, by rfl⟩ : syracuseStep 217395353 = 163046515) B163046515
theorem B144930235 : Blo 2091435 144930235 := bstep (se 1 (by rfl) ⟨108697676, by rfl⟩ : syracuseStep 144930235 = 217395353) B217395353
theorem B193240313 : Blo 2091435 193240313 := bstep (se 2 (by rfl) ⟨72465117, by rfl⟩ : syracuseStep 193240313 = 144930235) B144930235
theorem B128826875 : Blo 2091435 128826875 := bstep (se 1 (by rfl) ⟨96620156, by rfl⟩ : syracuseStep 128826875 = 193240313) B193240313
theorem B85884583 : Blo 2091435 85884583 := bstep (se 1 (by rfl) ⟨64413437, by rfl⟩ : syracuseStep 85884583 = 128826875) B128826875
theorem B114512777 : Blo 2091435 114512777 := bstep (se 2 (by rfl) ⟨42942291, by rfl⟩ : syracuseStep 114512777 = 85884583) B85884583
theorem B76341851 : Blo 2091435 76341851 := bstep (se 1 (by rfl) ⟨57256388, by rfl⟩ : syracuseStep 76341851 = 114512777) B114512777
theorem B50894567 : Blo 2091435 50894567 := bstep (se 1 (by rfl) ⟨38170925, by rfl⟩ : syracuseStep 50894567 = 76341851) B76341851
theorem B33929711 : Blo 2091435 33929711 := bstep (se 1 (by rfl) ⟨25447283, by rfl⟩ : syracuseStep 33929711 = 50894567) B50894567
theorem B22619807 : Blo 2091435 22619807 := bstep (se 1 (by rfl) ⟨16964855, by rfl⟩ : syracuseStep 22619807 = 33929711) B33929711
theorem B15079871 : Blo 2091435 15079871 := bstep (se 1 (by rfl) ⟨11309903, by rfl⟩ : syracuseStep 15079871 = 22619807) B22619807
theorem B10053247 : Blo 2091435 10053247 := bstep (se 1 (by rfl) ⟨7539935, by rfl⟩ : syracuseStep 10053247 = 15079871) B15079871
theorem B13404329 : Blo 2091435 13404329 := bstep (se 2 (by rfl) ⟨5026623, by rfl⟩ : syracuseStep 13404329 = 10053247) B10053247
theorem B8936219 : Blo 2091435 8936219 := bstep (se 1 (by rfl) ⟨6702164, by rfl⟩ : syracuseStep 8936219 = 13404329) B13404329
theorem B5957479 : Blo 2091435 5957479 := bstep (se 1 (by rfl) ⟨4468109, by rfl⟩ : syracuseStep 5957479 = 8936219) B8936219
theorem B7943305 : Blo 2091435 7943305 := bstep (se 2 (by rfl) ⟨2978739, by rfl⟩ : syracuseStep 7943305 = 5957479) B5957479
theorem B10591073 : Blo 2091435 10591073 := bstep (se 2 (by rfl) ⟨3971652, by rfl⟩ : syracuseStep 10591073 = 7943305) B7943305
theorem B7060715 : Blo 2091435 7060715 := bstep (se 1 (by rfl) ⟨5295536, by rfl⟩ : syracuseStep 7060715 = 10591073) B10591073
theorem B4707143 : Blo 2091435 4707143 := bstep (se 1 (by rfl) ⟨3530357, by rfl⟩ : syracuseStep 4707143 = 7060715) B7060715
theorem B3138095 : Blo 2091435 3138095 := bstep (se 1 (by rfl) ⟨2353571, by rfl⟩ : syracuseStep 3138095 = 4707143) B4707143
theorem B2092063 : Blo 2091435 2092063 := bstep (se 1 (by rfl) ⟨1569047, by rfl⟩ : syracuseStep 2092063 = 3138095) B3138095
theorem B3138101 : Blo 2091435 3138101 := bbase (se 5 (by rfl) ⟨147098, by rfl⟩ : syracuseStep 3138101 = 294197) (by norm_num)
theorem B2092067 : Blo 2091435 2092067 := bstep (se 1 (by rfl) ⟨1569050, by rfl⟩ : syracuseStep 2092067 = 3138101) B3138101
theorem B5295557 : Blo 2091435 5295557 := bbase (se 4 (by rfl) ⟨496458, by rfl⟩ : syracuseStep 5295557 = 992917) (by norm_num)
theorem B3530371 : Blo 2091435 3530371 := bstep (se 1 (by rfl) ⟨2647778, by rfl⟩ : syracuseStep 3530371 = 5295557) B5295557
theorem B4707161 : Blo 2091435 4707161 := bstep (se 2 (by rfl) ⟨1765185, by rfl⟩ : syracuseStep 4707161 = 3530371) B3530371
theorem B3138107 : Blo 2091435 3138107 := bstep (se 1 (by rfl) ⟨2353580, by rfl⟩ : syracuseStep 3138107 = 4707161) B4707161
theorem B2092071 : Blo 2091435 2092071 := bstep (se 1 (by rfl) ⟨1569053, by rfl⟩ : syracuseStep 2092071 = 3138107) B3138107
theorem B2353585 : Blo 2091435 2353585 := bbase (se 2 (by rfl) ⟨882594, by rfl⟩ : syracuseStep 2353585 = 1765189) (by norm_num)
theorem B3138113 : Blo 2091435 3138113 := bstep (se 2 (by rfl) ⟨1176792, by rfl⟩ : syracuseStep 3138113 = 2353585) B2353585
theorem B2092075 : Blo 2091435 2092075 := bstep (se 1 (by rfl) ⟨1569056, by rfl⟩ : syracuseStep 2092075 = 3138113) B3138113
theorem B5957525 : Blo 2091435 5957525 := bbase (se 6 (by rfl) ⟨139629, by rfl⟩ : syracuseStep 5957525 = 279259) (by norm_num)
theorem B3971683 : Blo 2091435 3971683 := bstep (se 1 (by rfl) ⟨2978762, by rfl⟩ : syracuseStep 3971683 = 5957525) B5957525
theorem B5295577 : Blo 2091435 5295577 := bstep (se 2 (by rfl) ⟨1985841, by rfl⟩ : syracuseStep 5295577 = 3971683) B3971683
theorem B7060769 : Blo 2091435 7060769 := bstep (se 2 (by rfl) ⟨2647788, by rfl⟩ : syracuseStep 7060769 = 5295577) B5295577
theorem B4707179 : Blo 2091435 4707179 := bstep (se 1 (by rfl) ⟨3530384, by rfl⟩ : syracuseStep 4707179 = 7060769) B7060769
theorem B3138119 : Blo 2091435 3138119 := bstep (se 1 (by rfl) ⟨2353589, by rfl⟩ : syracuseStep 3138119 = 4707179) B4707179
theorem B2092079 : Blo 2091435 2092079 := bstep (se 1 (by rfl) ⟨1569059, by rfl⟩ : syracuseStep 2092079 = 3138119) B3138119
theorem B3138125 : Blo 2091435 3138125 := bbase (se 3 (by rfl) ⟨588398, by rfl⟩ : syracuseStep 3138125 = 1176797) (by norm_num)
theorem B2092083 : Blo 2091435 2092083 := bstep (se 1 (by rfl) ⟨1569062, by rfl⟩ : syracuseStep 2092083 = 3138125) B3138125
theorem B4707197 : Blo 2091435 4707197 := bbase (se 3 (by rfl) ⟨882599, by rfl⟩ : syracuseStep 4707197 = 1765199) (by norm_num)
theorem B3138131 : Blo 2091435 3138131 := bstep (se 1 (by rfl) ⟨2353598, by rfl⟩ : syracuseStep 3138131 = 4707197) B4707197
theorem B2092087 : Blo 2091435 2092087 := bstep (se 1 (by rfl) ⟨1569065, by rfl⟩ : syracuseStep 2092087 = 3138131) B3138131
theorem B3530405 : Blo 2091435 3530405 := bbase (se 4 (by rfl) ⟨330975, by rfl⟩ : syracuseStep 3530405 = 661951) (by norm_num)
theorem B2353603 : Blo 2091435 2353603 := bstep (se 1 (by rfl) ⟨1765202, by rfl⟩ : syracuseStep 2353603 = 3530405) B3530405
theorem B3138137 : Blo 2091435 3138137 := bstep (se 2 (by rfl) ⟨1176801, by rfl⟩ : syracuseStep 3138137 = 2353603) B2353603
theorem B2092091 : Blo 2091435 2092091 := bstep (se 1 (by rfl) ⟨1569068, by rfl⟩ : syracuseStep 2092091 = 3138137) B3138137
theorem B2234089 : Blo 2091435 2234089 := bbase (se 2 (by rfl) ⟨837783, by rfl⟩ : syracuseStep 2234089 = 1675567) (by norm_num)
theorem B2978785 : Blo 2091435 2978785 := bstep (se 2 (by rfl) ⟨1117044, by rfl⟩ : syracuseStep 2978785 = 2234089) B2234089
theorem B15886853 : Blo 2091435 15886853 := bstep (se 4 (by rfl) ⟨1489392, by rfl⟩ : syracuseStep 15886853 = 2978785) B2978785
theorem B10591235 : Blo 2091435 10591235 := bstep (se 1 (by rfl) ⟨7943426, by rfl⟩ : syracuseStep 10591235 = 15886853) B15886853
theorem B7060823 : Blo 2091435 7060823 := bstep (se 1 (by rfl) ⟨5295617, by rfl⟩ : syracuseStep 7060823 = 10591235) B10591235
theorem B4707215 : Blo 2091435 4707215 := bstep (se 1 (by rfl) ⟨3530411, by rfl⟩ : syracuseStep 4707215 = 7060823) B7060823
theorem B3138143 : Blo 2091435 3138143 := bstep (se 1 (by rfl) ⟨2353607, by rfl⟩ : syracuseStep 3138143 = 4707215) B4707215
theorem B2092095 : Blo 2091435 2092095 := bstep (se 1 (by rfl) ⟨1569071, by rfl⟩ : syracuseStep 2092095 = 3138143) B3138143
theorem B3138149 : Blo 2091435 3138149 := bbase (se 4 (by rfl) ⟨294201, by rfl⟩ : syracuseStep 3138149 = 588403) (by norm_num)
theorem B2092099 : Blo 2091435 2092099 := bstep (se 1 (by rfl) ⟨1569074, by rfl⟩ : syracuseStep 2092099 = 3138149) B3138149
theorem B2978797 : Blo 2091435 2978797 := bbase (se 3 (by rfl) ⟨558524, by rfl⟩ : syracuseStep 2978797 = 1117049) (by norm_num)
theorem B3971729 : Blo 2091435 3971729 := bstep (se 2 (by rfl) ⟨1489398, by rfl⟩ : syracuseStep 3971729 = 2978797) B2978797
theorem B2647819 : Blo 2091435 2647819 := bstep (se 1 (by rfl) ⟨1985864, by rfl⟩ : syracuseStep 2647819 = 3971729) B3971729
theorem B3530425 : Blo 2091435 3530425 := bstep (se 2 (by rfl) ⟨1323909, by rfl⟩ : syracuseStep 3530425 = 2647819) B2647819
theorem B4707233 : Blo 2091435 4707233 := bstep (se 2 (by rfl) ⟨1765212, by rfl⟩ : syracuseStep 4707233 = 3530425) B3530425
theorem B3138155 : Blo 2091435 3138155 := bstep (se 1 (by rfl) ⟨2353616, by rfl⟩ : syracuseStep 3138155 = 4707233) B4707233
theorem B2092103 : Blo 2091435 2092103 := bstep (se 1 (by rfl) ⟨1569077, by rfl⟩ : syracuseStep 2092103 = 3138155) B3138155
theorem B2353621 : Blo 2091435 2353621 := bbase (se 7 (by rfl) ⟨27581, by rfl⟩ : syracuseStep 2353621 = 55163) (by norm_num)
theorem B3138161 : Blo 2091435 3138161 := bstep (se 2 (by rfl) ⟨1176810, by rfl⟩ : syracuseStep 3138161 = 2353621) B2353621
theorem B2092107 : Blo 2091435 2092107 := bstep (se 1 (by rfl) ⟨1569080, by rfl⟩ : syracuseStep 2092107 = 3138161) B3138161
theorem B2647829 : Blo 2091435 2647829 := bbase (se 6 (by rfl) ⟨62058, by rfl⟩ : syracuseStep 2647829 = 124117) (by norm_num)
theorem B7060877 : Blo 2091435 7060877 := bstep (se 3 (by rfl) ⟨1323914, by rfl⟩ : syracuseStep 7060877 = 2647829) B2647829
theorem B4707251 : Blo 2091435 4707251 := bstep (se 1 (by rfl) ⟨3530438, by rfl⟩ : syracuseStep 4707251 = 7060877) B7060877
theorem B3138167 : Blo 2091435 3138167 := bstep (se 1 (by rfl) ⟨2353625, by rfl⟩ : syracuseStep 3138167 = 4707251) B4707251
theorem B2092111 : Blo 2091435 2092111 := bstep (se 1 (by rfl) ⟨1569083, by rfl⟩ : syracuseStep 2092111 = 3138167) B3138167
theorem B3138173 : Blo 2091435 3138173 := bbase (se 3 (by rfl) ⟨588407, by rfl⟩ : syracuseStep 3138173 = 1176815) (by norm_num)
theorem B2092115 : Blo 2091435 2092115 := bstep (se 1 (by rfl) ⟨1569086, by rfl⟩ : syracuseStep 2092115 = 3138173) B3138173
theorem B4707269 : Blo 2091435 4707269 := bbase (se 4 (by rfl) ⟨441306, by rfl⟩ : syracuseStep 4707269 = 882613) (by norm_num)
theorem B3138179 : Blo 2091435 3138179 := bstep (se 1 (by rfl) ⟨2353634, by rfl⟩ : syracuseStep 3138179 = 4707269) B4707269
theorem B2092119 : Blo 2091435 2092119 := bstep (se 1 (by rfl) ⟨1569089, by rfl⟩ : syracuseStep 2092119 = 3138179) B3138179
theorem B3770077 : Blo 2091435 3770077 := bbase (se 3 (by rfl) ⟨706889, by rfl⟩ : syracuseStep 3770077 = 1413779) (by norm_num)
theorem B5026769 : Blo 2091435 5026769 := bstep (se 2 (by rfl) ⟨1885038, by rfl⟩ : syracuseStep 5026769 = 3770077) B3770077
theorem B3351179 : Blo 2091435 3351179 := bstep (se 1 (by rfl) ⟨2513384, by rfl⟩ : syracuseStep 3351179 = 5026769) B5026769
theorem B8936477 : Blo 2091435 8936477 := bstep (se 3 (by rfl) ⟨1675589, by rfl⟩ : syracuseStep 8936477 = 3351179) B3351179
theorem B5957651 : Blo 2091435 5957651 := bstep (se 1 (by rfl) ⟨4468238, by rfl⟩ : syracuseStep 5957651 = 8936477) B8936477
theorem B3971767 : Blo 2091435 3971767 := bstep (se 1 (by rfl) ⟨2978825, by rfl⟩ : syracuseStep 3971767 = 5957651) B5957651
theorem B5295689 : Blo 2091435 5295689 := bstep (se 2 (by rfl) ⟨1985883, by rfl⟩ : syracuseStep 5295689 = 3971767) B3971767
theorem B3530459 : Blo 2091435 3530459 := bstep (se 1 (by rfl) ⟨2647844, by rfl⟩ : syracuseStep 3530459 = 5295689) B5295689
theorem B2353639 : Blo 2091435 2353639 := bstep (se 1 (by rfl) ⟨1765229, by rfl⟩ : syracuseStep 2353639 = 3530459) B3530459
theorem B3138185 : Blo 2091435 3138185 := bstep (se 2 (by rfl) ⟨1176819, by rfl⟩ : syracuseStep 3138185 = 2353639) B2353639
theorem B2092123 : Blo 2091435 2092123 := bstep (se 1 (by rfl) ⟨1569092, by rfl⟩ : syracuseStep 2092123 = 3138185) B3138185
theorem B10591397 : Blo 2091435 10591397 := bbase (se 4 (by rfl) ⟨992943, by rfl⟩ : syracuseStep 10591397 = 1985887) (by norm_num)
theorem B7060931 : Blo 2091435 7060931 := bstep (se 1 (by rfl) ⟨5295698, by rfl⟩ : syracuseStep 7060931 = 10591397) B10591397
theorem B4707287 : Blo 2091435 4707287 := bstep (se 1 (by rfl) ⟨3530465, by rfl⟩ : syracuseStep 4707287 = 7060931) B7060931
theorem B3138191 : Blo 2091435 3138191 := bstep (se 1 (by rfl) ⟨2353643, by rfl⟩ : syracuseStep 3138191 = 4707287) B4707287
theorem B2092127 : Blo 2091435 2092127 := bstep (se 1 (by rfl) ⟨1569095, by rfl⟩ : syracuseStep 2092127 = 3138191) B3138191
theorem B3138197 : Blo 2091435 3138197 := bbase (se 6 (by rfl) ⟨73551, by rfl⟩ : syracuseStep 3138197 = 147103) (by norm_num)
theorem B2092131 : Blo 2091435 2092131 := bstep (se 1 (by rfl) ⟨1569098, by rfl⟩ : syracuseStep 2092131 = 3138197) B3138197
theorem B11310293 : Blo 2091435 11310293 := bbase (se 7 (by rfl) ⟨132542, by rfl⟩ : syracuseStep 11310293 = 265085) (by norm_num)
theorem B30160781 : Blo 2091435 30160781 := bstep (se 3 (by rfl) ⟨5655146, by rfl⟩ : syracuseStep 30160781 = 11310293) B11310293
theorem B20107187 : Blo 2091435 20107187 := bstep (se 1 (by rfl) ⟨15080390, by rfl⟩ : syracuseStep 20107187 = 30160781) B30160781
theorem B13404791 : Blo 2091435 13404791 := bstep (se 1 (by rfl) ⟨10053593, by rfl⟩ : syracuseStep 13404791 = 20107187) B20107187
theorem B8936527 : Blo 2091435 8936527 := bstep (se 1 (by rfl) ⟨6702395, by rfl⟩ : syracuseStep 8936527 = 13404791) B13404791
theorem B11915369 : Blo 2091435 11915369 := bstep (se 2 (by rfl) ⟨4468263, by rfl⟩ : syracuseStep 11915369 = 8936527) B8936527
theorem B7943579 : Blo 2091435 7943579 := bstep (se 1 (by rfl) ⟨5957684, by rfl⟩ : syracuseStep 7943579 = 11915369) B11915369
theorem B5295719 : Blo 2091435 5295719 := bstep (se 1 (by rfl) ⟨3971789, by rfl⟩ : syracuseStep 5295719 = 7943579) B7943579
theorem B3530479 : Blo 2091435 3530479 := bstep (se 1 (by rfl) ⟨2647859, by rfl⟩ : syracuseStep 3530479 = 5295719) B5295719
theorem B4707305 : Blo 2091435 4707305 := bstep (se 2 (by rfl) ⟨1765239, by rfl⟩ : syracuseStep 4707305 = 3530479) B3530479
theorem B3138203 : Blo 2091435 3138203 := bstep (se 1 (by rfl) ⟨2353652, by rfl⟩ : syracuseStep 3138203 = 4707305) B4707305
theorem B2092135 : Blo 2091435 2092135 := bstep (se 1 (by rfl) ⟨1569101, by rfl⟩ : syracuseStep 2092135 = 3138203) B3138203
theorem B2353657 : Blo 2091435 2353657 := bbase (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) (by norm_num)
theorem B3138209 : Blo 2091435 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B2092139 : Blo 2091435 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B6702421 : Blo 2091435 6702421 := bbase (se 12 (by rfl) ⟨2454, by rfl⟩ : syracuseStep 6702421 = 4909) (by norm_num)
theorem B8936561 : Blo 2091435 8936561 := bstep (se 2 (by rfl) ⟨3351210, by rfl⟩ : syracuseStep 8936561 = 6702421) B6702421
theorem B5957707 : Blo 2091435 5957707 := bstep (se 1 (by rfl) ⟨4468280, by rfl⟩ : syracuseStep 5957707 = 8936561) B8936561
theorem B7943609 : Blo 2091435 7943609 := bstep (se 2 (by rfl) ⟨2978853, by rfl⟩ : syracuseStep 7943609 = 5957707) B5957707
theorem B5295739 : Blo 2091435 5295739 := bstep (se 1 (by rfl) ⟨3971804, by rfl⟩ : syracuseStep 5295739 = 7943609) B7943609
theorem B7060985 : Blo 2091435 7060985 := bstep (se 2 (by rfl) ⟨2647869, by rfl⟩ : syracuseStep 7060985 = 5295739) B5295739
theorem B4707323 : Blo 2091435 4707323 := bstep (se 1 (by rfl) ⟨3530492, by rfl⟩ : syracuseStep 4707323 = 7060985) B7060985
theorem B3138215 : Blo 2091435 3138215 := bstep (se 1 (by rfl) ⟨2353661, by rfl⟩ : syracuseStep 3138215 = 4707323) B4707323
theorem B2092143 : Blo 2091435 2092143 := bstep (se 1 (by rfl) ⟨1569107, by rfl⟩ : syracuseStep 2092143 = 3138215) B3138215
theorem B3138221 : Blo 2091435 3138221 := bbase (se 3 (by rfl) ⟨588416, by rfl⟩ : syracuseStep 3138221 = 1176833) (by norm_num)
theorem B2092147 : Blo 2091435 2092147 := bstep (se 1 (by rfl) ⟨1569110, by rfl⟩ : syracuseStep 2092147 = 3138221) B3138221
theorem B4707341 : Blo 2091435 4707341 := bbase (se 3 (by rfl) ⟨882626, by rfl⟩ : syracuseStep 4707341 = 1765253) (by norm_num)
theorem B3138227 : Blo 2091435 3138227 := bstep (se 1 (by rfl) ⟨2353670, by rfl⟩ : syracuseStep 3138227 = 4707341) B4707341
theorem B2092151 : Blo 2091435 2092151 := bstep (se 1 (by rfl) ⟨1569113, by rfl⟩ : syracuseStep 2092151 = 3138227) B3138227
theorem B2647885 : Blo 2091435 2647885 := bbase (se 3 (by rfl) ⟨496478, by rfl⟩ : syracuseStep 2647885 = 992957) (by norm_num)
theorem B3530513 : Blo 2091435 3530513 := bstep (se 2 (by rfl) ⟨1323942, by rfl⟩ : syracuseStep 3530513 = 2647885) B2647885
theorem B2353675 : Blo 2091435 2353675 := bstep (se 1 (by rfl) ⟨1765256, by rfl⟩ : syracuseStep 2353675 = 3530513) B3530513
theorem B3138233 : Blo 2091435 3138233 := bstep (se 2 (by rfl) ⟨1176837, by rfl⟩ : syracuseStep 3138233 = 2353675) B2353675
theorem B2092155 : Blo 2091435 2092155 := bstep (se 1 (by rfl) ⟨1569116, by rfl⟩ : syracuseStep 2092155 = 3138233) B3138233
theorem B45241685 : Blo 2091435 45241685 := bbase (se 16 (by rfl) ⟨1035, by rfl⟩ : syracuseStep 45241685 = 2071) (by norm_num)
theorem B30161123 : Blo 2091435 30161123 := bstep (se 1 (by rfl) ⟨22620842, by rfl⟩ : syracuseStep 30161123 = 45241685) B45241685
theorem B20107415 : Blo 2091435 20107415 := bstep (se 1 (by rfl) ⟨15080561, by rfl⟩ : syracuseStep 20107415 = 30161123) B30161123
theorem B13404943 : Blo 2091435 13404943 := bstep (se 1 (by rfl) ⟨10053707, by rfl⟩ : syracuseStep 13404943 = 20107415) B20107415
theorem B17873257 : Blo 2091435 17873257 := bstep (se 2 (by rfl) ⟨6702471, by rfl⟩ : syracuseStep 17873257 = 13404943) B13404943
theorem B23831009 : Blo 2091435 23831009 := bstep (se 2 (by rfl) ⟨8936628, by rfl⟩ : syracuseStep 23831009 = 17873257) B17873257
theorem B15887339 : Blo 2091435 15887339 := bstep (se 1 (by rfl) ⟨11915504, by rfl⟩ : syracuseStep 15887339 = 23831009) B23831009
theorem B10591559 : Blo 2091435 10591559 := bstep (se 1 (by rfl) ⟨7943669, by rfl⟩ : syracuseStep 10591559 = 15887339) B15887339
theorem B7061039 : Blo 2091435 7061039 := bstep (se 1 (by rfl) ⟨5295779, by rfl⟩ : syracuseStep 7061039 = 10591559) B10591559
theorem B4707359 : Blo 2091435 4707359 := bstep (se 1 (by rfl) ⟨3530519, by rfl⟩ : syracuseStep 4707359 = 7061039) B7061039
theorem B3138239 : Blo 2091435 3138239 := bstep (se 1 (by rfl) ⟨2353679, by rfl⟩ : syracuseStep 3138239 = 4707359) B4707359
theorem B2092159 : Blo 2091435 2092159 := bstep (se 1 (by rfl) ⟨1569119, by rfl⟩ : syracuseStep 2092159 = 3138239) B3138239
theorem B3138245 : Blo 2091435 3138245 := bbase (se 4 (by rfl) ⟨294210, by rfl⟩ : syracuseStep 3138245 = 588421) (by norm_num)
theorem B2092163 : Blo 2091435 2092163 := bstep (se 1 (by rfl) ⟨1569122, by rfl⟩ : syracuseStep 2092163 = 3138245) B3138245
theorem B3530533 : Blo 2091435 3530533 := bbase (se 4 (by rfl) ⟨330987, by rfl⟩ : syracuseStep 3530533 = 661975) (by norm_num)
theorem B4707377 : Blo 2091435 4707377 := bstep (se 2 (by rfl) ⟨1765266, by rfl⟩ : syracuseStep 4707377 = 3530533) B3530533
theorem B3138251 : Blo 2091435 3138251 := bstep (se 1 (by rfl) ⟨2353688, by rfl⟩ : syracuseStep 3138251 = 4707377) B4707377
theorem B2092167 : Blo 2091435 2092167 := bstep (se 1 (by rfl) ⟨1569125, by rfl⟩ : syracuseStep 2092167 = 3138251) B3138251
theorem B2353693 : Blo 2091435 2353693 := bbase (se 3 (by rfl) ⟨441317, by rfl⟩ : syracuseStep 2353693 = 882635) (by norm_num)
theorem B3138257 : Blo 2091435 3138257 := bstep (se 2 (by rfl) ⟨1176846, by rfl⟩ : syracuseStep 3138257 = 2353693) B2353693
theorem B2092171 : Blo 2091435 2092171 := bstep (se 1 (by rfl) ⟨1569128, by rfl⟩ : syracuseStep 2092171 = 3138257) B3138257
theorem B7061093 : Blo 2091435 7061093 := bbase (se 4 (by rfl) ⟨661977, by rfl⟩ : syracuseStep 7061093 = 1323955) (by norm_num)
theorem B4707395 : Blo 2091435 4707395 := bstep (se 1 (by rfl) ⟨3530546, by rfl⟩ : syracuseStep 4707395 = 7061093) B7061093
theorem B3138263 : Blo 2091435 3138263 := bstep (se 1 (by rfl) ⟨2353697, by rfl⟩ : syracuseStep 3138263 = 4707395) B4707395
theorem B2092175 : Blo 2091435 2092175 := bstep (se 1 (by rfl) ⟨1569131, by rfl⟩ : syracuseStep 2092175 = 3138263) B3138263
theorem B3138269 : Blo 2091435 3138269 := bbase (se 3 (by rfl) ⟨588425, by rfl⟩ : syracuseStep 3138269 = 1176851) (by norm_num)
theorem B2092179 : Blo 2091435 2092179 := bstep (se 1 (by rfl) ⟨1569134, by rfl⟩ : syracuseStep 2092179 = 3138269) B3138269
theorem B4707413 : Blo 2091435 4707413 := bbase (se 8 (by rfl) ⟨27582, by rfl⟩ : syracuseStep 4707413 = 55165) (by norm_num)
theorem B3138275 : Blo 2091435 3138275 := bstep (se 1 (by rfl) ⟨2353706, by rfl⟩ : syracuseStep 3138275 = 4707413) B4707413
theorem B2092183 : Blo 2091435 2092183 := bstep (se 1 (by rfl) ⟨1569137, by rfl⟩ : syracuseStep 2092183 = 3138275) B3138275
theorem B10053845 : Blo 2091435 10053845 := bbase (se 7 (by rfl) ⟨117818, by rfl⟩ : syracuseStep 10053845 = 235637) (by norm_num)
theorem B6702563 : Blo 2091435 6702563 := bstep (se 1 (by rfl) ⟨5026922, by rfl⟩ : syracuseStep 6702563 = 10053845) B10053845
theorem B4468375 : Blo 2091435 4468375 := bstep (se 1 (by rfl) ⟨3351281, by rfl⟩ : syracuseStep 4468375 = 6702563) B6702563
theorem B5957833 : Blo 2091435 5957833 := bstep (se 2 (by rfl) ⟨2234187, by rfl⟩ : syracuseStep 5957833 = 4468375) B4468375
theorem B7943777 : Blo 2091435 7943777 := bstep (se 2 (by rfl) ⟨2978916, by rfl⟩ : syracuseStep 7943777 = 5957833) B5957833
theorem B5295851 : Blo 2091435 5295851 := bstep (se 1 (by rfl) ⟨3971888, by rfl⟩ : syracuseStep 5295851 = 7943777) B7943777
theorem B3530567 : Blo 2091435 3530567 := bstep (se 1 (by rfl) ⟨2647925, by rfl⟩ : syracuseStep 3530567 = 5295851) B5295851
theorem B2353711 : Blo 2091435 2353711 := bstep (se 1 (by rfl) ⟨1765283, by rfl⟩ : syracuseStep 2353711 = 3530567) B3530567
theorem B3138281 : Blo 2091435 3138281 := bstep (se 2 (by rfl) ⟨1176855, by rfl⟩ : syracuseStep 3138281 = 2353711) B2353711
theorem B2092187 : Blo 2091435 2092187 := bstep (se 1 (by rfl) ⟨1569140, by rfl⟩ : syracuseStep 2092187 = 3138281) B3138281
theorem B2385829 : Blo 2091435 2385829 := bbase (se 4 (by rfl) ⟨223671, by rfl⟩ : syracuseStep 2385829 = 447343) (by norm_num)
theorem B3181105 : Blo 2091435 3181105 := bstep (se 2 (by rfl) ⟨1192914, by rfl⟩ : syracuseStep 3181105 = 2385829) B2385829
theorem B4241473 : Blo 2091435 4241473 := bstep (se 2 (by rfl) ⟨1590552, by rfl⟩ : syracuseStep 4241473 = 3181105) B3181105
theorem B22621189 : Blo 2091435 22621189 := bstep (se 4 (by rfl) ⟨2120736, by rfl⟩ : syracuseStep 22621189 = 4241473) B4241473
theorem B30161585 : Blo 2091435 30161585 := bstep (se 2 (by rfl) ⟨11310594, by rfl⟩ : syracuseStep 30161585 = 22621189) B22621189
theorem B20107723 : Blo 2091435 20107723 := bstep (se 1 (by rfl) ⟨15080792, by rfl⟩ : syracuseStep 20107723 = 30161585) B30161585
theorem B26810297 : Blo 2091435 26810297 := bstep (se 2 (by rfl) ⟨10053861, by rfl⟩ : syracuseStep 26810297 = 20107723) B20107723
theorem B17873531 : Blo 2091435 17873531 := bstep (se 1 (by rfl) ⟨13405148, by rfl⟩ : syracuseStep 17873531 = 26810297) B26810297
theorem B11915687 : Blo 2091435 11915687 := bstep (se 1 (by rfl) ⟨8936765, by rfl⟩ : syracuseStep 11915687 = 17873531) B17873531
theorem B7943791 : Blo 2091435 7943791 := bstep (se 1 (by rfl) ⟨5957843, by rfl⟩ : syracuseStep 7943791 = 11915687) B11915687
theorem B10591721 : Blo 2091435 10591721 := bstep (se 2 (by rfl) ⟨3971895, by rfl⟩ : syracuseStep 10591721 = 7943791) B7943791
theorem B7061147 : Blo 2091435 7061147 := bstep (se 1 (by rfl) ⟨5295860, by rfl⟩ : syracuseStep 7061147 = 10591721) B10591721
theorem B4707431 : Blo 2091435 4707431 := bstep (se 1 (by rfl) ⟨3530573, by rfl⟩ : syracuseStep 4707431 = 7061147) B7061147
theorem B3138287 : Blo 2091435 3138287 := bstep (se 1 (by rfl) ⟨2353715, by rfl⟩ : syracuseStep 3138287 = 4707431) B4707431
theorem B2092191 : Blo 2091435 2092191 := bstep (se 1 (by rfl) ⟨1569143, by rfl⟩ : syracuseStep 2092191 = 3138287) B3138287
theorem B3138293 : Blo 2091435 3138293 := bbase (se 5 (by rfl) ⟨147107, by rfl⟩ : syracuseStep 3138293 = 294215) (by norm_num)
theorem B2092195 : Blo 2091435 2092195 := bstep (se 1 (by rfl) ⟨1569146, by rfl⟩ : syracuseStep 2092195 = 3138293) B3138293
theorem B8482981 : Blo 2091435 8482981 := bbase (se 4 (by rfl) ⟨795279, by rfl⟩ : syracuseStep 8482981 = 1590559) (by norm_num)
theorem B11310641 : Blo 2091435 11310641 := bstep (se 2 (by rfl) ⟨4241490, by rfl⟩ : syracuseStep 11310641 = 8482981) B8482981
theorem B7540427 : Blo 2091435 7540427 := bstep (se 1 (by rfl) ⟨5655320, by rfl⟩ : syracuseStep 7540427 = 11310641) B11310641
theorem B5026951 : Blo 2091435 5026951 := bstep (se 1 (by rfl) ⟨3770213, by rfl⟩ : syracuseStep 5026951 = 7540427) B7540427
theorem B6702601 : Blo 2091435 6702601 := bstep (se 2 (by rfl) ⟨2513475, by rfl⟩ : syracuseStep 6702601 = 5026951) B5026951
theorem B8936801 : Blo 2091435 8936801 := bstep (se 2 (by rfl) ⟨3351300, by rfl⟩ : syracuseStep 8936801 = 6702601) B6702601
theorem B5957867 : Blo 2091435 5957867 := bstep (se 1 (by rfl) ⟨4468400, by rfl⟩ : syracuseStep 5957867 = 8936801) B8936801
theorem B3971911 : Blo 2091435 3971911 := bstep (se 1 (by rfl) ⟨2978933, by rfl⟩ : syracuseStep 3971911 = 5957867) B5957867
theorem B5295881 : Blo 2091435 5295881 := bstep (se 2 (by rfl) ⟨1985955, by rfl⟩ : syracuseStep 5295881 = 3971911) B3971911
theorem B3530587 : Blo 2091435 3530587 := bstep (se 1 (by rfl) ⟨2647940, by rfl⟩ : syracuseStep 3530587 = 5295881) B5295881
theorem B4707449 : Blo 2091435 4707449 := bstep (se 2 (by rfl) ⟨1765293, by rfl⟩ : syracuseStep 4707449 = 3530587) B3530587
theorem B3138299 : Blo 2091435 3138299 := bstep (se 1 (by rfl) ⟨2353724, by rfl⟩ : syracuseStep 3138299 = 4707449) B4707449
theorem B2092199 : Blo 2091435 2092199 := bstep (se 1 (by rfl) ⟨1569149, by rfl⟩ : syracuseStep 2092199 = 3138299) B3138299
theorem B2353729 : Blo 2091435 2353729 := bbase (se 2 (by rfl) ⟨882648, by rfl⟩ : syracuseStep 2353729 = 1765297) (by norm_num)
theorem B3138305 : Blo 2091435 3138305 := bstep (se 2 (by rfl) ⟨1176864, by rfl⟩ : syracuseStep 3138305 = 2353729) B2353729
theorem B2092203 : Blo 2091435 2092203 := bstep (se 1 (by rfl) ⟨1569152, by rfl⟩ : syracuseStep 2092203 = 3138305) B3138305
theorem B5295901 : Blo 2091435 5295901 := bbase (se 3 (by rfl) ⟨992981, by rfl⟩ : syracuseStep 5295901 = 1985963) (by norm_num)
theorem B7061201 : Blo 2091435 7061201 := bstep (se 2 (by rfl) ⟨2647950, by rfl⟩ : syracuseStep 7061201 = 5295901) B5295901
theorem B4707467 : Blo 2091435 4707467 := bstep (se 1 (by rfl) ⟨3530600, by rfl⟩ : syracuseStep 4707467 = 7061201) B7061201
theorem B3138311 : Blo 2091435 3138311 := bstep (se 1 (by rfl) ⟨2353733, by rfl⟩ : syracuseStep 3138311 = 4707467) B4707467
theorem B2092207 : Blo 2091435 2092207 := bstep (se 1 (by rfl) ⟨1569155, by rfl⟩ : syracuseStep 2092207 = 3138311) B3138311
theorem B3138317 : Blo 2091435 3138317 := bbase (se 3 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 3138317 = 1176869) (by norm_num)
theorem B2092211 : Blo 2091435 2092211 := bstep (se 1 (by rfl) ⟨1569158, by rfl⟩ : syracuseStep 2092211 = 3138317) B3138317
theorem B4707485 : Blo 2091435 4707485 := bbase (se 3 (by rfl) ⟨882653, by rfl⟩ : syracuseStep 4707485 = 1765307) (by norm_num)
theorem B3138323 : Blo 2091435 3138323 := bstep (se 1 (by rfl) ⟨2353742, by rfl⟩ : syracuseStep 3138323 = 4707485) B4707485
theorem B2092215 : Blo 2091435 2092215 := bstep (se 1 (by rfl) ⟨1569161, by rfl⟩ : syracuseStep 2092215 = 3138323) B3138323
theorem B3530621 : Blo 2091435 3530621 := bbase (se 3 (by rfl) ⟨661991, by rfl⟩ : syracuseStep 3530621 = 1323983) (by norm_num)
theorem B2353747 : Blo 2091435 2353747 := bstep (se 1 (by rfl) ⟨1765310, by rfl⟩ : syracuseStep 2353747 = 3530621) B3530621
theorem B3138329 : Blo 2091435 3138329 := bstep (se 2 (by rfl) ⟨1176873, by rfl⟩ : syracuseStep 3138329 = 2353747) B2353747
theorem B2092219 : Blo 2091435 2092219 := bstep (se 1 (by rfl) ⟨1569164, by rfl⟩ : syracuseStep 2092219 = 3138329) B3138329
theorem B6702677 : Blo 2091435 6702677 := bbase (se 8 (by rfl) ⟨39273, by rfl⟩ : syracuseStep 6702677 = 78547) (by norm_num)
theorem B4468451 : Blo 2091435 4468451 := bstep (se 1 (by rfl) ⟨3351338, by rfl⟩ : syracuseStep 4468451 = 6702677) B6702677
theorem B11915869 : Blo 2091435 11915869 := bstep (se 3 (by rfl) ⟨2234225, by rfl⟩ : syracuseStep 11915869 = 4468451) B4468451
theorem B15887825 : Blo 2091435 15887825 := bstep (se 2 (by rfl) ⟨5957934, by rfl⟩ : syracuseStep 15887825 = 11915869) B11915869
theorem B10591883 : Blo 2091435 10591883 := bstep (se 1 (by rfl) ⟨7943912, by rfl⟩ : syracuseStep 10591883 = 15887825) B15887825
theorem B7061255 : Blo 2091435 7061255 := bstep (se 1 (by rfl) ⟨5295941, by rfl⟩ : syracuseStep 7061255 = 10591883) B10591883
theorem B4707503 : Blo 2091435 4707503 := bstep (se 1 (by rfl) ⟨3530627, by rfl⟩ : syracuseStep 4707503 = 7061255) B7061255
theorem B3138335 : Blo 2091435 3138335 := bstep (se 1 (by rfl) ⟨2353751, by rfl⟩ : syracuseStep 3138335 = 4707503) B4707503
theorem B2092223 : Blo 2091435 2092223 := bstep (se 1 (by rfl) ⟨1569167, by rfl⟩ : syracuseStep 2092223 = 3138335) B3138335
theorem B3138341 : Blo 2091435 3138341 := bbase (se 4 (by rfl) ⟨294219, by rfl⟩ : syracuseStep 3138341 = 588439) (by norm_num)
theorem B2092227 : Blo 2091435 2092227 := bstep (se 1 (by rfl) ⟨1569170, by rfl⟩ : syracuseStep 2092227 = 3138341) B3138341
theorem B2647981 : Blo 2091435 2647981 := bbase (se 3 (by rfl) ⟨496496, by rfl⟩ : syracuseStep 2647981 = 992993) (by norm_num)
theorem B3530641 : Blo 2091435 3530641 := bstep (se 2 (by rfl) ⟨1323990, by rfl⟩ : syracuseStep 3530641 = 2647981) B2647981
theorem B4707521 : Blo 2091435 4707521 := bstep (se 2 (by rfl) ⟨1765320, by rfl⟩ : syracuseStep 4707521 = 3530641) B3530641
theorem B3138347 : Blo 2091435 3138347 := bstep (se 1 (by rfl) ⟨2353760, by rfl⟩ : syracuseStep 3138347 = 4707521) B4707521
theorem B2092231 : Blo 2091435 2092231 := bstep (se 1 (by rfl) ⟨1569173, by rfl⟩ : syracuseStep 2092231 = 3138347) B3138347
theorem B2353765 : Blo 2091435 2353765 := bbase (se 4 (by rfl) ⟨220665, by rfl⟩ : syracuseStep 2353765 = 441331) (by norm_num)
theorem B3138353 : Blo 2091435 3138353 := bstep (se 2 (by rfl) ⟨1176882, by rfl⟩ : syracuseStep 3138353 = 2353765) B2353765
theorem B2092235 : Blo 2091435 2092235 := bstep (se 1 (by rfl) ⟨1569176, by rfl⟩ : syracuseStep 2092235 = 3138353) B3138353
theorem B3351365 : Blo 2091435 3351365 := bbase (se 4 (by rfl) ⟨314190, by rfl⟩ : syracuseStep 3351365 = 628381) (by norm_num)
theorem B2234243 : Blo 2091435 2234243 := bstep (se 1 (by rfl) ⟨1675682, by rfl⟩ : syracuseStep 2234243 = 3351365) B3351365
theorem B5957981 : Blo 2091435 5957981 := bstep (se 3 (by rfl) ⟨1117121, by rfl⟩ : syracuseStep 5957981 = 2234243) B2234243
theorem B3971987 : Blo 2091435 3971987 := bstep (se 1 (by rfl) ⟨2978990, by rfl⟩ : syracuseStep 3971987 = 5957981) B5957981
theorem B2647991 : Blo 2091435 2647991 := bstep (se 1 (by rfl) ⟨1985993, by rfl⟩ : syracuseStep 2647991 = 3971987) B3971987
theorem B7061309 : Blo 2091435 7061309 := bstep (se 3 (by rfl) ⟨1323995, by rfl⟩ : syracuseStep 7061309 = 2647991) B2647991
theorem B4707539 : Blo 2091435 4707539 := bstep (se 1 (by rfl) ⟨3530654, by rfl⟩ : syracuseStep 4707539 = 7061309) B7061309
theorem B3138359 : Blo 2091435 3138359 := bstep (se 1 (by rfl) ⟨2353769, by rfl⟩ : syracuseStep 3138359 = 4707539) B4707539
theorem B2092239 : Blo 2091435 2092239 := bstep (se 1 (by rfl) ⟨1569179, by rfl⟩ : syracuseStep 2092239 = 3138359) B3138359
theorem B3138365 : Blo 2091435 3138365 := bbase (se 3 (by rfl) ⟨588443, by rfl⟩ : syracuseStep 3138365 = 1176887) (by norm_num)
theorem B2092243 : Blo 2091435 2092243 := bstep (se 1 (by rfl) ⟨1569182, by rfl⟩ : syracuseStep 2092243 = 3138365) B3138365
theorem B4707557 : Blo 2091435 4707557 := bbase (se 4 (by rfl) ⟨441333, by rfl⟩ : syracuseStep 4707557 = 882667) (by norm_num)
theorem B3138371 : Blo 2091435 3138371 := bstep (se 1 (by rfl) ⟨2353778, by rfl⟩ : syracuseStep 3138371 = 4707557) B4707557
theorem B2092247 : Blo 2091435 2092247 := bstep (se 1 (by rfl) ⟨1569185, by rfl⟩ : syracuseStep 2092247 = 3138371) B3138371
theorem B5296013 : Blo 2091435 5296013 := bbase (se 3 (by rfl) ⟨993002, by rfl⟩ : syracuseStep 5296013 = 1986005) (by norm_num)
theorem B3530675 : Blo 2091435 3530675 := bstep (se 1 (by rfl) ⟨2648006, by rfl⟩ : syracuseStep 3530675 = 5296013) B5296013
theorem B2353783 : Blo 2091435 2353783 := bstep (se 1 (by rfl) ⟨1765337, by rfl⟩ : syracuseStep 2353783 = 3530675) B3530675
theorem B3138377 : Blo 2091435 3138377 := bstep (se 2 (by rfl) ⟨1176891, by rfl⟩ : syracuseStep 3138377 = 2353783) B2353783
theorem B2092251 : Blo 2091435 2092251 := bstep (se 1 (by rfl) ⟨1569188, by rfl⟩ : syracuseStep 2092251 = 3138377) B3138377
theorem B2979013 : Blo 2091435 2979013 := bbase (se 4 (by rfl) ⟨279282, by rfl⟩ : syracuseStep 2979013 = 558565) (by norm_num)
theorem B3972017 : Blo 2091435 3972017 := bstep (se 2 (by rfl) ⟨1489506, by rfl⟩ : syracuseStep 3972017 = 2979013) B2979013
theorem B10592045 : Blo 2091435 10592045 := bstep (se 3 (by rfl) ⟨1986008, by rfl⟩ : syracuseStep 10592045 = 3972017) B3972017
theorem B7061363 : Blo 2091435 7061363 := bstep (se 1 (by rfl) ⟨5296022, by rfl⟩ : syracuseStep 7061363 = 10592045) B10592045
theorem B4707575 : Blo 2091435 4707575 := bstep (se 1 (by rfl) ⟨3530681, by rfl⟩ : syracuseStep 4707575 = 7061363) B7061363
theorem B3138383 : Blo 2091435 3138383 := bstep (se 1 (by rfl) ⟨2353787, by rfl⟩ : syracuseStep 3138383 = 4707575) B4707575
theorem B2092255 : Blo 2091435 2092255 := bstep (se 1 (by rfl) ⟨1569191, by rfl⟩ : syracuseStep 2092255 = 3138383) B3138383
theorem B3138389 : Blo 2091435 3138389 := bbase (se 9 (by rfl) ⟨9194, by rfl⟩ : syracuseStep 3138389 = 18389) (by norm_num)
theorem B2092259 : Blo 2091435 2092259 := bstep (se 1 (by rfl) ⟨1569194, by rfl⟩ : syracuseStep 2092259 = 3138389) B3138389
theorem B4241621 : Blo 2091435 4241621 := bbase (se 7 (by rfl) ⟨49706, by rfl⟩ : syracuseStep 4241621 = 99413) (by norm_num)
theorem B2827747 : Blo 2091435 2827747 := bstep (se 1 (by rfl) ⟨2120810, by rfl⟩ : syracuseStep 2827747 = 4241621) B4241621
theorem B3770329 : Blo 2091435 3770329 := bstep (se 2 (by rfl) ⟨1413873, by rfl⟩ : syracuseStep 3770329 = 2827747) B2827747
theorem B5027105 : Blo 2091435 5027105 := bstep (se 2 (by rfl) ⟨1885164, by rfl⟩ : syracuseStep 5027105 = 3770329) B3770329
theorem B3351403 : Blo 2091435 3351403 := bstep (se 1 (by rfl) ⟨2513552, by rfl⟩ : syracuseStep 3351403 = 5027105) B5027105
theorem B4468537 : Blo 2091435 4468537 := bstep (se 2 (by rfl) ⟨1675701, by rfl⟩ : syracuseStep 4468537 = 3351403) B3351403
theorem B5958049 : Blo 2091435 5958049 := bstep (se 2 (by rfl) ⟨2234268, by rfl⟩ : syracuseStep 5958049 = 4468537) B4468537
theorem B7944065 : Blo 2091435 7944065 := bstep (se 2 (by rfl) ⟨2979024, by rfl⟩ : syracuseStep 7944065 = 5958049) B5958049
theorem B5296043 : Blo 2091435 5296043 := bstep (se 1 (by rfl) ⟨3972032, by rfl⟩ : syracuseStep 5296043 = 7944065) B7944065
theorem B3530695 : Blo 2091435 3530695 := bstep (se 1 (by rfl) ⟨2648021, by rfl⟩ : syracuseStep 3530695 = 5296043) B5296043
theorem B4707593 : Blo 2091435 4707593 := bstep (se 2 (by rfl) ⟨1765347, by rfl⟩ : syracuseStep 4707593 = 3530695) B3530695
theorem B3138395 : Blo 2091435 3138395 := bstep (se 1 (by rfl) ⟨2353796, by rfl⟩ : syracuseStep 3138395 = 4707593) B4707593
theorem B2092263 : Blo 2091435 2092263 := bstep (se 1 (by rfl) ⟨1569197, by rfl⟩ : syracuseStep 2092263 = 3138395) B3138395
theorem B2353801 : Blo 2091435 2353801 := bbase (se 2 (by rfl) ⟨882675, by rfl⟩ : syracuseStep 2353801 = 1765351) (by norm_num)
theorem B3138401 : Blo 2091435 3138401 := bstep (se 2 (by rfl) ⟨1176900, by rfl⟩ : syracuseStep 3138401 = 2353801) B2353801
theorem B2092267 : Blo 2091435 2092267 := bstep (se 1 (by rfl) ⟨1569200, by rfl⟩ : syracuseStep 2092267 = 3138401) B3138401
theorem B6362453 : Blo 2091435 6362453 := bbase (se 14 (by rfl) ⟨582, by rfl⟩ : syracuseStep 6362453 = 1165) (by norm_num)
theorem B16966541 : Blo 2091435 16966541 := bstep (se 3 (by rfl) ⟨3181226, by rfl⟩ : syracuseStep 16966541 = 6362453) B6362453
theorem B45244109 : Blo 2091435 45244109 := bstep (se 3 (by rfl) ⟨8483270, by rfl⟩ : syracuseStep 45244109 = 16966541) B16966541
theorem B30162739 : Blo 2091435 30162739 := bstep (se 1 (by rfl) ⟨22622054, by rfl⟩ : syracuseStep 30162739 = 45244109) B45244109
theorem B40216985 : Blo 2091435 40216985 := bstep (se 2 (by rfl) ⟨15081369, by rfl⟩ : syracuseStep 40216985 = 30162739) B30162739
theorem B26811323 : Blo 2091435 26811323 := bstep (se 1 (by rfl) ⟨20108492, by rfl⟩ : syracuseStep 26811323 = 40216985) B40216985
theorem B17874215 : Blo 2091435 17874215 := bstep (se 1 (by rfl) ⟨13405661, by rfl⟩ : syracuseStep 17874215 = 26811323) B26811323
theorem B11916143 : Blo 2091435 11916143 := bstep (se 1 (by rfl) ⟨8937107, by rfl⟩ : syracuseStep 11916143 = 17874215) B17874215
theorem B7944095 : Blo 2091435 7944095 := bstep (se 1 (by rfl) ⟨5958071, by rfl⟩ : syracuseStep 7944095 = 11916143) B11916143
theorem B5296063 : Blo 2091435 5296063 := bstep (se 1 (by rfl) ⟨3972047, by rfl⟩ : syracuseStep 5296063 = 7944095) B7944095
theorem B7061417 : Blo 2091435 7061417 := bstep (se 2 (by rfl) ⟨2648031, by rfl⟩ : syracuseStep 7061417 = 5296063) B5296063
theorem B4707611 : Blo 2091435 4707611 := bstep (se 1 (by rfl) ⟨3530708, by rfl⟩ : syracuseStep 4707611 = 7061417) B7061417
theorem B3138407 : Blo 2091435 3138407 := bstep (se 1 (by rfl) ⟨2353805, by rfl⟩ : syracuseStep 3138407 = 4707611) B4707611
theorem B2092271 : Blo 2091435 2092271 := bstep (se 1 (by rfl) ⟨1569203, by rfl⟩ : syracuseStep 2092271 = 3138407) B3138407
theorem B3138413 : Blo 2091435 3138413 := bbase (se 3 (by rfl) ⟨588452, by rfl⟩ : syracuseStep 3138413 = 1176905) (by norm_num)
theorem B2092275 : Blo 2091435 2092275 := bstep (se 1 (by rfl) ⟨1569206, by rfl⟩ : syracuseStep 2092275 = 3138413) B3138413
theorem B4707629 : Blo 2091435 4707629 := bbase (se 3 (by rfl) ⟨882680, by rfl⟩ : syracuseStep 4707629 = 1765361) (by norm_num)
theorem B3138419 : Blo 2091435 3138419 := bstep (se 1 (by rfl) ⟨2353814, by rfl⟩ : syracuseStep 3138419 = 4707629) B4707629
theorem B2092279 : Blo 2091435 2092279 := bstep (se 1 (by rfl) ⟨1569209, by rfl⟩ : syracuseStep 2092279 = 3138419) B3138419
theorem B15081461 : Blo 2091435 15081461 := bbase (se 5 (by rfl) ⟨706943, by rfl⟩ : syracuseStep 15081461 = 1413887) (by norm_num)
theorem B10054307 : Blo 2091435 10054307 := bstep (se 1 (by rfl) ⟨7540730, by rfl⟩ : syracuseStep 10054307 = 15081461) B15081461
theorem B6702871 : Blo 2091435 6702871 := bstep (se 1 (by rfl) ⟨5027153, by rfl⟩ : syracuseStep 6702871 = 10054307) B10054307
theorem B8937161 : Blo 2091435 8937161 := bstep (se 2 (by rfl) ⟨3351435, by rfl⟩ : syracuseStep 8937161 = 6702871) B6702871
theorem B5958107 : Blo 2091435 5958107 := bstep (se 1 (by rfl) ⟨4468580, by rfl⟩ : syracuseStep 5958107 = 8937161) B8937161
theorem B3972071 : Blo 2091435 3972071 := bstep (se 1 (by rfl) ⟨2979053, by rfl⟩ : syracuseStep 3972071 = 5958107) B5958107
theorem B2648047 : Blo 2091435 2648047 := bstep (se 1 (by rfl) ⟨1986035, by rfl⟩ : syracuseStep 2648047 = 3972071) B3972071
theorem B3530729 : Blo 2091435 3530729 := bstep (se 2 (by rfl) ⟨1324023, by rfl⟩ : syracuseStep 3530729 = 2648047) B2648047
theorem B2353819 : Blo 2091435 2353819 := bstep (se 1 (by rfl) ⟨1765364, by rfl⟩ : syracuseStep 2353819 = 3530729) B3530729
theorem B3138425 : Blo 2091435 3138425 := bstep (se 2 (by rfl) ⟨1176909, by rfl⟩ : syracuseStep 3138425 = 2353819) B2353819
theorem B2092283 : Blo 2091435 2092283 := bstep (se 1 (by rfl) ⟨1569212, by rfl⟩ : syracuseStep 2092283 = 3138425) B3138425
theorem B5655557 : Blo 2091435 5655557 := bbase (se 4 (by rfl) ⟨530208, by rfl⟩ : syracuseStep 5655557 = 1060417) (by norm_num)
theorem B3770371 : Blo 2091435 3770371 := bstep (se 1 (by rfl) ⟨2827778, by rfl⟩ : syracuseStep 3770371 = 5655557) B5655557
theorem B20108645 : Blo 2091435 20108645 := bstep (se 4 (by rfl) ⟨1885185, by rfl⟩ : syracuseStep 20108645 = 3770371) B3770371
theorem B13405763 : Blo 2091435 13405763 := bstep (se 1 (by rfl) ⟨10054322, by rfl⟩ : syracuseStep 13405763 = 20108645) B20108645
theorem B35748701 : Blo 2091435 35748701 := bstep (se 3 (by rfl) ⟨6702881, by rfl⟩ : syracuseStep 35748701 = 13405763) B13405763
theorem B23832467 : Blo 2091435 23832467 := bstep (se 1 (by rfl) ⟨17874350, by rfl⟩ : syracuseStep 23832467 = 35748701) B35748701
theorem B15888311 : Blo 2091435 15888311 := bstep (se 1 (by rfl) ⟨11916233, by rfl⟩ : syracuseStep 15888311 = 23832467) B23832467
theorem B10592207 : Blo 2091435 10592207 := bstep (se 1 (by rfl) ⟨7944155, by rfl⟩ : syracuseStep 10592207 = 15888311) B15888311
theorem B7061471 : Blo 2091435 7061471 := bstep (se 1 (by rfl) ⟨5296103, by rfl⟩ : syracuseStep 7061471 = 10592207) B10592207
theorem B4707647 : Blo 2091435 4707647 := bstep (se 1 (by rfl) ⟨3530735, by rfl⟩ : syracuseStep 4707647 = 7061471) B7061471
theorem B3138431 : Blo 2091435 3138431 := bstep (se 1 (by rfl) ⟨2353823, by rfl⟩ : syracuseStep 3138431 = 4707647) B4707647
theorem B2092287 : Blo 2091435 2092287 := bstep (se 1 (by rfl) ⟨1569215, by rfl⟩ : syracuseStep 2092287 = 3138431) B3138431
theorem B3138437 : Blo 2091435 3138437 := bbase (se 4 (by rfl) ⟨294228, by rfl⟩ : syracuseStep 3138437 = 588457) (by norm_num)
theorem B2092291 : Blo 2091435 2092291 := bstep (se 1 (by rfl) ⟨1569218, by rfl⟩ : syracuseStep 2092291 = 3138437) B3138437
theorem B3530749 : Blo 2091435 3530749 := bbase (se 3 (by rfl) ⟨662015, by rfl⟩ : syracuseStep 3530749 = 1324031) (by norm_num)
theorem B4707665 : Blo 2091435 4707665 := bstep (se 2 (by rfl) ⟨1765374, by rfl⟩ : syracuseStep 4707665 = 3530749) B3530749
theorem B3138443 : Blo 2091435 3138443 := bstep (se 1 (by rfl) ⟨2353832, by rfl⟩ : syracuseStep 3138443 = 4707665) B4707665
theorem B2092295 : Blo 2091435 2092295 := bstep (se 1 (by rfl) ⟨1569221, by rfl⟩ : syracuseStep 2092295 = 3138443) B3138443
theorem B2353837 : Blo 2091435 2353837 := bbase (se 3 (by rfl) ⟨441344, by rfl⟩ : syracuseStep 2353837 = 882689) (by norm_num)
theorem B3138449 : Blo 2091435 3138449 := bstep (se 2 (by rfl) ⟨1176918, by rfl⟩ : syracuseStep 3138449 = 2353837) B2353837
theorem B2092299 : Blo 2091435 2092299 := bstep (se 1 (by rfl) ⟨1569224, by rfl⟩ : syracuseStep 2092299 = 3138449) B3138449
theorem B7061525 : Blo 2091435 7061525 := bbase (se 6 (by rfl) ⟨165504, by rfl⟩ : syracuseStep 7061525 = 331009) (by norm_num)
theorem B4707683 : Blo 2091435 4707683 := bstep (se 1 (by rfl) ⟨3530762, by rfl⟩ : syracuseStep 4707683 = 7061525) B7061525
theorem B3138455 : Blo 2091435 3138455 := bstep (se 1 (by rfl) ⟨2353841, by rfl⟩ : syracuseStep 3138455 = 4707683) B4707683
theorem B2092303 : Blo 2091435 2092303 := bstep (se 1 (by rfl) ⟨1569227, by rfl⟩ : syracuseStep 2092303 = 3138455) B3138455
theorem B3138461 : Blo 2091435 3138461 := bbase (se 3 (by rfl) ⟨588461, by rfl⟩ : syracuseStep 3138461 = 1176923) (by norm_num)
theorem B2092307 : Blo 2091435 2092307 := bstep (se 1 (by rfl) ⟨1569230, by rfl⟩ : syracuseStep 2092307 = 3138461) B3138461
theorem B4707701 : Blo 2091435 4707701 := bbase (se 5 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 4707701 = 441347) (by norm_num)
theorem B3138467 : Blo 2091435 3138467 := bstep (se 1 (by rfl) ⟨2353850, by rfl⟩ : syracuseStep 3138467 = 4707701) B4707701
theorem B2092311 : Blo 2091435 2092311 := bstep (se 1 (by rfl) ⟨1569233, by rfl⟩ : syracuseStep 2092311 = 3138467) B3138467
theorem B16966901 : Blo 2091435 16966901 := bbase (se 5 (by rfl) ⟨795323, by rfl⟩ : syracuseStep 16966901 = 1590647) (by norm_num)
theorem B11311267 : Blo 2091435 11311267 := bstep (se 1 (by rfl) ⟨8483450, by rfl⟩ : syracuseStep 11311267 = 16966901) B16966901
theorem B15081689 : Blo 2091435 15081689 := bstep (se 2 (by rfl) ⟨5655633, by rfl⟩ : syracuseStep 15081689 = 11311267) B11311267
theorem B10054459 : Blo 2091435 10054459 := bstep (se 1 (by rfl) ⟨7540844, by rfl⟩ : syracuseStep 10054459 = 15081689) B15081689
theorem B13405945 : Blo 2091435 13405945 := bstep (se 2 (by rfl) ⟨5027229, by rfl⟩ : syracuseStep 13405945 = 10054459) B10054459
theorem B17874593 : Blo 2091435 17874593 := bstep (se 2 (by rfl) ⟨6702972, by rfl⟩ : syracuseStep 17874593 = 13405945) B13405945
theorem B11916395 : Blo 2091435 11916395 := bstep (se 1 (by rfl) ⟨8937296, by rfl⟩ : syracuseStep 11916395 = 17874593) B17874593
theorem B7944263 : Blo 2091435 7944263 := bstep (se 1 (by rfl) ⟨5958197, by rfl⟩ : syracuseStep 7944263 = 11916395) B11916395
theorem B5296175 : Blo 2091435 5296175 := bstep (se 1 (by rfl) ⟨3972131, by rfl⟩ : syracuseStep 5296175 = 7944263) B7944263
theorem B3530783 : Blo 2091435 3530783 := bstep (se 1 (by rfl) ⟨2648087, by rfl⟩ : syracuseStep 3530783 = 5296175) B5296175
theorem B2353855 : Blo 2091435 2353855 := bstep (se 1 (by rfl) ⟨1765391, by rfl⟩ : syracuseStep 2353855 = 3530783) B3530783
theorem B3138473 : Blo 2091435 3138473 := bstep (se 2 (by rfl) ⟨1176927, by rfl⟩ : syracuseStep 3138473 = 2353855) B2353855
theorem B2092315 : Blo 2091435 2092315 := bstep (se 1 (by rfl) ⟨1569236, by rfl⟩ : syracuseStep 2092315 = 3138473) B3138473
theorem B7944277 : Blo 2091435 7944277 := bbase (se 8 (by rfl) ⟨46548, by rfl⟩ : syracuseStep 7944277 = 93097) (by norm_num)
theorem B10592369 : Blo 2091435 10592369 := bstep (se 2 (by rfl) ⟨3972138, by rfl⟩ : syracuseStep 10592369 = 7944277) B7944277
theorem B7061579 : Blo 2091435 7061579 := bstep (se 1 (by rfl) ⟨5296184, by rfl⟩ : syracuseStep 7061579 = 10592369) B10592369
theorem B4707719 : Blo 2091435 4707719 := bstep (se 1 (by rfl) ⟨3530789, by rfl⟩ : syracuseStep 4707719 = 7061579) B7061579
theorem B3138479 : Blo 2091435 3138479 := bstep (se 1 (by rfl) ⟨2353859, by rfl⟩ : syracuseStep 3138479 = 4707719) B4707719
theorem B2092319 : Blo 2091435 2092319 := bstep (se 1 (by rfl) ⟨1569239, by rfl⟩ : syracuseStep 2092319 = 3138479) B3138479
theorem B3138485 : Blo 2091435 3138485 := bbase (se 5 (by rfl) ⟨147116, by rfl⟩ : syracuseStep 3138485 = 294233) (by norm_num)
theorem B2092323 : Blo 2091435 2092323 := bstep (se 1 (by rfl) ⟨1569242, by rfl⟩ : syracuseStep 2092323 = 3138485) B3138485
theorem B5296205 : Blo 2091435 5296205 := bbase (se 3 (by rfl) ⟨993038, by rfl⟩ : syracuseStep 5296205 = 1986077) (by norm_num)
theorem B3530803 : Blo 2091435 3530803 := bstep (se 1 (by rfl) ⟨2648102, by rfl⟩ : syracuseStep 3530803 = 5296205) B5296205
theorem B4707737 : Blo 2091435 4707737 := bstep (se 2 (by rfl) ⟨1765401, by rfl⟩ : syracuseStep 4707737 = 3530803) B3530803
theorem B3138491 : Blo 2091435 3138491 := bstep (se 1 (by rfl) ⟨2353868, by rfl⟩ : syracuseStep 3138491 = 4707737) B4707737
theorem B2092327 : Blo 2091435 2092327 := bstep (se 1 (by rfl) ⟨1569245, by rfl⟩ : syracuseStep 2092327 = 3138491) B3138491
theorem B2353873 : Blo 2091435 2353873 := bbase (se 2 (by rfl) ⟨882702, by rfl⟩ : syracuseStep 2353873 = 1765405) (by norm_num)
theorem B3138497 : Blo 2091435 3138497 := bstep (se 2 (by rfl) ⟨1176936, by rfl⟩ : syracuseStep 3138497 = 2353873) B2353873
theorem B2092331 : Blo 2091435 2092331 := bstep (se 1 (by rfl) ⟨1569248, by rfl⟩ : syracuseStep 2092331 = 3138497) B3138497
theorem B39759893 : Blo 2091435 39759893 := bbase (se 6 (by rfl) ⟨931872, by rfl⟩ : syracuseStep 39759893 = 1863745) (by norm_num)
theorem B26506595 : Blo 2091435 26506595 := bstep (se 1 (by rfl) ⟨19879946, by rfl⟩ : syracuseStep 26506595 = 39759893) B39759893
theorem B17671063 : Blo 2091435 17671063 := bstep (se 1 (by rfl) ⟨13253297, by rfl⟩ : syracuseStep 17671063 = 26506595) B26506595
theorem B23561417 : Blo 2091435 23561417 := bstep (se 2 (by rfl) ⟨8835531, by rfl⟩ : syracuseStep 23561417 = 17671063) B17671063
theorem B15707611 : Blo 2091435 15707611 := bstep (se 1 (by rfl) ⟨11780708, by rfl⟩ : syracuseStep 15707611 = 23561417) B23561417
theorem B83773925 : Blo 2091435 83773925 := bstep (se 4 (by rfl) ⟨7853805, by rfl⟩ : syracuseStep 83773925 = 15707611) B15707611
theorem B55849283 : Blo 2091435 55849283 := bstep (se 1 (by rfl) ⟨41886962, by rfl⟩ : syracuseStep 55849283 = 83773925) B83773925
theorem B37232855 : Blo 2091435 37232855 := bstep (se 1 (by rfl) ⟨27924641, by rfl⟩ : syracuseStep 37232855 = 55849283) B55849283
theorem B24821903 : Blo 2091435 24821903 := bstep (se 1 (by rfl) ⟨18616427, by rfl⟩ : syracuseStep 24821903 = 37232855) B37232855
theorem B16547935 : Blo 2091435 16547935 := bstep (se 1 (by rfl) ⟨12410951, by rfl⟩ : syracuseStep 16547935 = 24821903) B24821903
theorem B22063913 : Blo 2091435 22063913 := bstep (se 2 (by rfl) ⟨8273967, by rfl⟩ : syracuseStep 22063913 = 16547935) B16547935
theorem B14709275 : Blo 2091435 14709275 := bstep (se 1 (by rfl) ⟨11031956, by rfl⟩ : syracuseStep 14709275 = 22063913) B22063913
theorem B9806183 : Blo 2091435 9806183 := bstep (se 1 (by rfl) ⟨7354637, by rfl⟩ : syracuseStep 9806183 = 14709275) B14709275
theorem B6537455 : Blo 2091435 6537455 := bstep (se 1 (by rfl) ⟨4903091, by rfl⟩ : syracuseStep 6537455 = 9806183) B9806183
theorem B4358303 : Blo 2091435 4358303 := bstep (se 1 (by rfl) ⟨3268727, by rfl⟩ : syracuseStep 4358303 = 6537455) B6537455
theorem B2905535 : Blo 2091435 2905535 := bstep (se 1 (by rfl) ⟨2179151, by rfl⟩ : syracuseStep 2905535 = 4358303) B4358303
theorem B7748093 : Blo 2091435 7748093 := bstep (se 3 (by rfl) ⟨1452767, by rfl⟩ : syracuseStep 7748093 = 2905535) B2905535
theorem B20661581 : Blo 2091435 20661581 := bstep (se 3 (by rfl) ⟨3874046, by rfl⟩ : syracuseStep 20661581 = 7748093) B7748093
theorem B13774387 : Blo 2091435 13774387 := bstep (se 1 (by rfl) ⟨10330790, by rfl⟩ : syracuseStep 13774387 = 20661581) B20661581
theorem B18365849 : Blo 2091435 18365849 := bstep (se 2 (by rfl) ⟨6887193, by rfl⟩ : syracuseStep 18365849 = 13774387) B13774387
theorem B12243899 : Blo 2091435 12243899 := bstep (se 1 (by rfl) ⟨9182924, by rfl⟩ : syracuseStep 12243899 = 18365849) B18365849
theorem B32650397 : Blo 2091435 32650397 := bstep (se 3 (by rfl) ⟨6121949, by rfl⟩ : syracuseStep 32650397 = 12243899) B12243899
theorem B21766931 : Blo 2091435 21766931 := bstep (se 1 (by rfl) ⟨16325198, by rfl⟩ : syracuseStep 21766931 = 32650397) B32650397
theorem B14511287 : Blo 2091435 14511287 := bstep (se 1 (by rfl) ⟨10883465, by rfl⟩ : syracuseStep 14511287 = 21766931) B21766931
theorem B9674191 : Blo 2091435 9674191 := bstep (se 1 (by rfl) ⟨7255643, by rfl⟩ : syracuseStep 9674191 = 14511287) B14511287
theorem B12898921 : Blo 2091435 12898921 := bstep (se 2 (by rfl) ⟨4837095, by rfl⟩ : syracuseStep 12898921 = 9674191) B9674191
theorem B17198561 : Blo 2091435 17198561 := bstep (se 2 (by rfl) ⟨6449460, by rfl⟩ : syracuseStep 17198561 = 12898921) B12898921
theorem B11465707 : Blo 2091435 11465707 := bstep (se 1 (by rfl) ⟨8599280, by rfl⟩ : syracuseStep 11465707 = 17198561) B17198561
theorem B15287609 : Blo 2091435 15287609 := bstep (se 2 (by rfl) ⟨5732853, by rfl⟩ : syracuseStep 15287609 = 11465707) B11465707
theorem B10191739 : Blo 2091435 10191739 := bstep (se 1 (by rfl) ⟨7643804, by rfl⟩ : syracuseStep 10191739 = 15287609) B15287609
theorem B13588985 : Blo 2091435 13588985 := bstep (se 2 (by rfl) ⟨5095869, by rfl⟩ : syracuseStep 13588985 = 10191739) B10191739
theorem B36237293 : Blo 2091435 36237293 := bstep (se 3 (by rfl) ⟨6794492, by rfl⟩ : syracuseStep 36237293 = 13588985) B13588985
theorem B24158195 : Blo 2091435 24158195 := bstep (se 1 (by rfl) ⟨18118646, by rfl⟩ : syracuseStep 24158195 = 36237293) B36237293
theorem B16105463 : Blo 2091435 16105463 := bstep (se 1 (by rfl) ⟨12079097, by rfl⟩ : syracuseStep 16105463 = 24158195) B24158195
theorem B10736975 : Blo 2091435 10736975 := bstep (se 1 (by rfl) ⟨8052731, by rfl⟩ : syracuseStep 10736975 = 16105463) B16105463
theorem B7157983 : Blo 2091435 7157983 := bstep (se 1 (by rfl) ⟨5368487, by rfl⟩ : syracuseStep 7157983 = 10736975) B10736975
theorem B9543977 : Blo 2091435 9543977 := bstep (se 2 (by rfl) ⟨3578991, by rfl⟩ : syracuseStep 9543977 = 7157983) B7157983
theorem B6362651 : Blo 2091435 6362651 := bstep (se 1 (by rfl) ⟨4771988, by rfl⟩ : syracuseStep 6362651 = 9543977) B9543977
theorem B4241767 : Blo 2091435 4241767 := bstep (se 1 (by rfl) ⟨3181325, by rfl⟩ : syracuseStep 4241767 = 6362651) B6362651
theorem B5655689 : Blo 2091435 5655689 := bstep (se 2 (by rfl) ⟨2120883, by rfl⟩ : syracuseStep 5655689 = 4241767) B4241767
theorem B3770459 : Blo 2091435 3770459 := bstep (se 1 (by rfl) ⟨2827844, by rfl⟩ : syracuseStep 3770459 = 5655689) B5655689
theorem B2513639 : Blo 2091435 2513639 := bstep (se 1 (by rfl) ⟨1885229, by rfl⟩ : syracuseStep 2513639 = 3770459) B3770459
theorem B6703037 : Blo 2091435 6703037 := bstep (se 3 (by rfl) ⟨1256819, by rfl⟩ : syracuseStep 6703037 = 2513639) B2513639
theorem B4468691 : Blo 2091435 4468691 := bstep (se 1 (by rfl) ⟨3351518, by rfl⟩ : syracuseStep 4468691 = 6703037) B6703037
theorem B2979127 : Blo 2091435 2979127 := bstep (se 1 (by rfl) ⟨2234345, by rfl⟩ : syracuseStep 2979127 = 4468691) B4468691
theorem B3972169 : Blo 2091435 3972169 := bstep (se 2 (by rfl) ⟨1489563, by rfl⟩ : syracuseStep 3972169 = 2979127) B2979127
theorem B5296225 : Blo 2091435 5296225 := bstep (se 2 (by rfl) ⟨1986084, by rfl⟩ : syracuseStep 5296225 = 3972169) B3972169
theorem B7061633 : Blo 2091435 7061633 := bstep (se 2 (by rfl) ⟨2648112, by rfl⟩ : syracuseStep 7061633 = 5296225) B5296225
theorem B4707755 : Blo 2091435 4707755 := bstep (se 1 (by rfl) ⟨3530816, by rfl⟩ : syracuseStep 4707755 = 7061633) B7061633
theorem B3138503 : Blo 2091435 3138503 := bstep (se 1 (by rfl) ⟨2353877, by rfl⟩ : syracuseStep 3138503 = 4707755) B4707755
theorem B2092335 : Blo 2091435 2092335 := bstep (se 1 (by rfl) ⟨1569251, by rfl⟩ : syracuseStep 2092335 = 3138503) B3138503
theorem B3138509 : Blo 2091435 3138509 := bbase (se 3 (by rfl) ⟨588470, by rfl⟩ : syracuseStep 3138509 = 1176941) (by norm_num)
theorem B2092339 : Blo 2091435 2092339 := bstep (se 1 (by rfl) ⟨1569254, by rfl⟩ : syracuseStep 2092339 = 3138509) B3138509
theorem B4707773 : Blo 2091435 4707773 := bbase (se 3 (by rfl) ⟨882707, by rfl⟩ : syracuseStep 4707773 = 1765415) (by norm_num)
theorem B3138515 : Blo 2091435 3138515 := bstep (se 1 (by rfl) ⟨2353886, by rfl⟩ : syracuseStep 3138515 = 4707773) B4707773
theorem B2092343 : Blo 2091435 2092343 := bstep (se 1 (by rfl) ⟨1569257, by rfl⟩ : syracuseStep 2092343 = 3138515) B3138515
theorem B3530837 : Blo 2091435 3530837 := bbase (se 8 (by rfl) ⟨20688, by rfl⟩ : syracuseStep 3530837 = 41377) (by norm_num)
theorem B2353891 : Blo 2091435 2353891 := bstep (se 1 (by rfl) ⟨1765418, by rfl⟩ : syracuseStep 2353891 = 3530837) B3530837
theorem B3138521 : Blo 2091435 3138521 := bstep (se 2 (by rfl) ⟨1176945, by rfl⟩ : syracuseStep 3138521 = 2353891) B2353891
theorem B2092347 : Blo 2091435 2092347 := bstep (se 1 (by rfl) ⟨1569260, by rfl⟩ : syracuseStep 2092347 = 3138521) B3138521
theorem B21767093 : Blo 2091435 21767093 := bbase (se 5 (by rfl) ⟨1020332, by rfl⟩ : syracuseStep 21767093 = 2040665) (by norm_num)
theorem B14511395 : Blo 2091435 14511395 := bstep (se 1 (by rfl) ⟨10883546, by rfl⟩ : syracuseStep 14511395 = 21767093) B21767093
theorem B9674263 : Blo 2091435 9674263 := bstep (se 1 (by rfl) ⟨7255697, by rfl⟩ : syracuseStep 9674263 = 14511395) B14511395
theorem B12899017 : Blo 2091435 12899017 := bstep (se 2 (by rfl) ⟨4837131, by rfl⟩ : syracuseStep 12899017 = 9674263) B9674263
theorem B17198689 : Blo 2091435 17198689 := bstep (se 2 (by rfl) ⟨6449508, by rfl⟩ : syracuseStep 17198689 = 12899017) B12899017
theorem B22931585 : Blo 2091435 22931585 := bstep (se 2 (by rfl) ⟨8599344, by rfl⟩ : syracuseStep 22931585 = 17198689) B17198689
theorem B15287723 : Blo 2091435 15287723 := bstep (se 1 (by rfl) ⟨11465792, by rfl⟩ : syracuseStep 15287723 = 22931585) B22931585
theorem B10191815 : Blo 2091435 10191815 := bstep (se 1 (by rfl) ⟨7643861, by rfl⟩ : syracuseStep 10191815 = 15287723) B15287723
theorem B6794543 : Blo 2091435 6794543 := bstep (se 1 (by rfl) ⟨5095907, by rfl⟩ : syracuseStep 6794543 = 10191815) B10191815
theorem B4529695 : Blo 2091435 4529695 := bstep (se 1 (by rfl) ⟨3397271, by rfl⟩ : syracuseStep 4529695 = 6794543) B6794543
theorem B6039593 : Blo 2091435 6039593 := bstep (se 2 (by rfl) ⟨2264847, by rfl⟩ : syracuseStep 6039593 = 4529695) B4529695
theorem B4026395 : Blo 2091435 4026395 := bstep (se 1 (by rfl) ⟨3019796, by rfl⟩ : syracuseStep 4026395 = 6039593) B6039593
theorem B2684263 : Blo 2091435 2684263 := bstep (se 1 (by rfl) ⟨2013197, by rfl⟩ : syracuseStep 2684263 = 4026395) B4026395
theorem B3579017 : Blo 2091435 3579017 := bstep (se 2 (by rfl) ⟨1342131, by rfl⟩ : syracuseStep 3579017 = 2684263) B2684263
theorem B38176181 : Blo 2091435 38176181 := bstep (se 5 (by rfl) ⟨1789508, by rfl⟩ : syracuseStep 38176181 = 3579017) B3579017
theorem B25450787 : Blo 2091435 25450787 := bstep (se 1 (by rfl) ⟨19088090, by rfl⟩ : syracuseStep 25450787 = 38176181) B38176181
theorem B16967191 : Blo 2091435 16967191 := bstep (se 1 (by rfl) ⟨12725393, by rfl⟩ : syracuseStep 16967191 = 25450787) B25450787
theorem B22622921 : Blo 2091435 22622921 := bstep (se 2 (by rfl) ⟨8483595, by rfl⟩ : syracuseStep 22622921 = 16967191) B16967191
theorem B15081947 : Blo 2091435 15081947 := bstep (se 1 (by rfl) ⟨11311460, by rfl⟩ : syracuseStep 15081947 = 22622921) B22622921
theorem B10054631 : Blo 2091435 10054631 := bstep (se 1 (by rfl) ⟨7540973, by rfl⟩ : syracuseStep 10054631 = 15081947) B15081947
theorem B6703087 : Blo 2091435 6703087 := bstep (se 1 (by rfl) ⟨5027315, by rfl⟩ : syracuseStep 6703087 = 10054631) B10054631
theorem B8937449 : Blo 2091435 8937449 := bstep (se 2 (by rfl) ⟨3351543, by rfl⟩ : syracuseStep 8937449 = 6703087) B6703087
theorem B5958299 : Blo 2091435 5958299 := bstep (se 1 (by rfl) ⟨4468724, by rfl⟩ : syracuseStep 5958299 = 8937449) B8937449
theorem B15888797 : Blo 2091435 15888797 := bstep (se 3 (by rfl) ⟨2979149, by rfl⟩ : syracuseStep 15888797 = 5958299) B5958299
theorem B10592531 : Blo 2091435 10592531 := bstep (se 1 (by rfl) ⟨7944398, by rfl⟩ : syracuseStep 10592531 = 15888797) B15888797
theorem B7061687 : Blo 2091435 7061687 := bstep (se 1 (by rfl) ⟨5296265, by rfl⟩ : syracuseStep 7061687 = 10592531) B10592531
theorem B4707791 : Blo 2091435 4707791 := bstep (se 1 (by rfl) ⟨3530843, by rfl⟩ : syracuseStep 4707791 = 7061687) B7061687
theorem B3138527 : Blo 2091435 3138527 := bstep (se 1 (by rfl) ⟨2353895, by rfl⟩ : syracuseStep 3138527 = 4707791) B4707791
theorem B2092351 : Blo 2091435 2092351 := bstep (se 1 (by rfl) ⟨1569263, by rfl⟩ : syracuseStep 2092351 = 3138527) B3138527
theorem B3138533 : Blo 2091435 3138533 := bbase (se 4 (by rfl) ⟨294237, by rfl⟩ : syracuseStep 3138533 = 588475) (by norm_num)
theorem B2092355 : Blo 2091435 2092355 := bstep (se 1 (by rfl) ⟨1569266, by rfl⟩ : syracuseStep 2092355 = 3138533) B3138533
theorem B3351557 : Blo 2091435 3351557 := bbase (se 4 (by rfl) ⟨314208, by rfl⟩ : syracuseStep 3351557 = 628417) (by norm_num)
theorem B8937485 : Blo 2091435 8937485 := bstep (se 3 (by rfl) ⟨1675778, by rfl⟩ : syracuseStep 8937485 = 3351557) B3351557
theorem B5958323 : Blo 2091435 5958323 := bstep (se 1 (by rfl) ⟨4468742, by rfl⟩ : syracuseStep 5958323 = 8937485) B8937485
theorem B3972215 : Blo 2091435 3972215 := bstep (se 1 (by rfl) ⟨2979161, by rfl⟩ : syracuseStep 3972215 = 5958323) B5958323
theorem B2648143 : Blo 2091435 2648143 := bstep (se 1 (by rfl) ⟨1986107, by rfl⟩ : syracuseStep 2648143 = 3972215) B3972215
theorem B3530857 : Blo 2091435 3530857 := bstep (se 2 (by rfl) ⟨1324071, by rfl⟩ : syracuseStep 3530857 = 2648143) B2648143
theorem B4707809 : Blo 2091435 4707809 := bstep (se 2 (by rfl) ⟨1765428, by rfl⟩ : syracuseStep 4707809 = 3530857) B3530857
theorem B3138539 : Blo 2091435 3138539 := bstep (se 1 (by rfl) ⟨2353904, by rfl⟩ : syracuseStep 3138539 = 4707809) B4707809
theorem B2092359 : Blo 2091435 2092359 := bstep (se 1 (by rfl) ⟨1569269, by rfl⟩ : syracuseStep 2092359 = 3138539) B3138539
theorem B2353909 : Blo 2091435 2353909 := bbase (se 5 (by rfl) ⟨110339, by rfl⟩ : syracuseStep 2353909 = 220679) (by norm_num)
theorem B3138545 : Blo 2091435 3138545 := bstep (se 2 (by rfl) ⟨1176954, by rfl⟩ : syracuseStep 3138545 = 2353909) B2353909
theorem B2092363 : Blo 2091435 2092363 := bstep (se 1 (by rfl) ⟨1569272, by rfl⟩ : syracuseStep 2092363 = 3138545) B3138545
theorem B2648153 : Blo 2091435 2648153 := bbase (se 2 (by rfl) ⟨993057, by rfl⟩ : syracuseStep 2648153 = 1986115) (by norm_num)
theorem B7061741 : Blo 2091435 7061741 := bstep (se 3 (by rfl) ⟨1324076, by rfl⟩ : syracuseStep 7061741 = 2648153) B2648153
theorem B4707827 : Blo 2091435 4707827 := bstep (se 1 (by rfl) ⟨3530870, by rfl⟩ : syracuseStep 4707827 = 7061741) B7061741
theorem B3138551 : Blo 2091435 3138551 := bstep (se 1 (by rfl) ⟨2353913, by rfl⟩ : syracuseStep 3138551 = 4707827) B4707827
theorem B2092367 : Blo 2091435 2092367 := bstep (se 1 (by rfl) ⟨1569275, by rfl⟩ : syracuseStep 2092367 = 3138551) B3138551
theorem B3138557 : Blo 2091435 3138557 := bbase (se 3 (by rfl) ⟨588479, by rfl⟩ : syracuseStep 3138557 = 1176959) (by norm_num)
theorem B2092371 : Blo 2091435 2092371 := bstep (se 1 (by rfl) ⟨1569278, by rfl⟩ : syracuseStep 2092371 = 3138557) B3138557
theorem B4707845 : Blo 2091435 4707845 := bbase (se 4 (by rfl) ⟨441360, by rfl⟩ : syracuseStep 4707845 = 882721) (by norm_num)
theorem B3138563 : Blo 2091435 3138563 := bstep (se 1 (by rfl) ⟨2353922, by rfl⟩ : syracuseStep 3138563 = 4707845) B4707845
theorem B2092375 : Blo 2091435 2092375 := bstep (se 1 (by rfl) ⟨1569281, by rfl⟩ : syracuseStep 2092375 = 3138563) B3138563
theorem B3972253 : Blo 2091435 3972253 := bbase (se 3 (by rfl) ⟨744797, by rfl⟩ : syracuseStep 3972253 = 1489595) (by norm_num)
theorem B5296337 : Blo 2091435 5296337 := bstep (se 2 (by rfl) ⟨1986126, by rfl⟩ : syracuseStep 5296337 = 3972253) B3972253
theorem B3530891 : Blo 2091435 3530891 := bstep (se 1 (by rfl) ⟨2648168, by rfl⟩ : syracuseStep 3530891 = 5296337) B5296337
theorem B2353927 : Blo 2091435 2353927 := bstep (se 1 (by rfl) ⟨1765445, by rfl⟩ : syracuseStep 2353927 = 3530891) B3530891
theorem B3138569 : Blo 2091435 3138569 := bstep (se 2 (by rfl) ⟨1176963, by rfl⟩ : syracuseStep 3138569 = 2353927) B2353927
theorem B2092379 : Blo 2091435 2092379 := bstep (se 1 (by rfl) ⟨1569284, by rfl⟩ : syracuseStep 2092379 = 3138569) B3138569
theorem B10592693 : Blo 2091435 10592693 := bbase (se 5 (by rfl) ⟨496532, by rfl⟩ : syracuseStep 10592693 = 993065) (by norm_num)
theorem B7061795 : Blo 2091435 7061795 := bstep (se 1 (by rfl) ⟨5296346, by rfl⟩ : syracuseStep 7061795 = 10592693) B10592693
theorem B4707863 : Blo 2091435 4707863 := bstep (se 1 (by rfl) ⟨3530897, by rfl⟩ : syracuseStep 4707863 = 7061795) B7061795
theorem B3138575 : Blo 2091435 3138575 := bstep (se 1 (by rfl) ⟨2353931, by rfl⟩ : syracuseStep 3138575 = 4707863) B4707863
theorem B2092383 : Blo 2091435 2092383 := bstep (se 1 (by rfl) ⟨1569287, by rfl⟩ : syracuseStep 2092383 = 3138575) B3138575
theorem B3138581 : Blo 2091435 3138581 := bbase (se 6 (by rfl) ⟨73560, by rfl⟩ : syracuseStep 3138581 = 147121) (by norm_num)
theorem B2092387 : Blo 2091435 2092387 := bstep (se 1 (by rfl) ⟨1569290, by rfl⟩ : syracuseStep 2092387 = 3138581) B3138581
theorem B3627917 : Blo 2091435 3627917 := bbase (se 3 (by rfl) ⟨680234, by rfl⟩ : syracuseStep 3627917 = 1360469) (by norm_num)
theorem B2418611 : Blo 2091435 2418611 := bstep (se 1 (by rfl) ⟨1813958, by rfl⟩ : syracuseStep 2418611 = 3627917) B3627917
theorem B6449629 : Blo 2091435 6449629 := bstep (se 3 (by rfl) ⟨1209305, by rfl⟩ : syracuseStep 6449629 = 2418611) B2418611
theorem B8599505 : Blo 2091435 8599505 := bstep (se 2 (by rfl) ⟨3224814, by rfl⟩ : syracuseStep 8599505 = 6449629) B6449629
theorem B22932013 : Blo 2091435 22932013 := bstep (se 3 (by rfl) ⟨4299752, by rfl⟩ : syracuseStep 22932013 = 8599505) B8599505
theorem B30576017 : Blo 2091435 30576017 := bstep (se 2 (by rfl) ⟨11466006, by rfl⟩ : syracuseStep 30576017 = 22932013) B22932013
theorem B20384011 : Blo 2091435 20384011 := bstep (se 1 (by rfl) ⟨15288008, by rfl⟩ : syracuseStep 20384011 = 30576017) B30576017
theorem B27178681 : Blo 2091435 27178681 := bstep (se 2 (by rfl) ⟨10192005, by rfl⟩ : syracuseStep 27178681 = 20384011) B20384011
theorem B36238241 : Blo 2091435 36238241 := bstep (se 2 (by rfl) ⟨13589340, by rfl⟩ : syracuseStep 36238241 = 27178681) B27178681
theorem B24158827 : Blo 2091435 24158827 := bstep (se 1 (by rfl) ⟨18119120, by rfl⟩ : syracuseStep 24158827 = 36238241) B36238241
theorem B32211769 : Blo 2091435 32211769 := bstep (se 2 (by rfl) ⟨12079413, by rfl⟩ : syracuseStep 32211769 = 24158827) B24158827
theorem B42949025 : Blo 2091435 42949025 := bstep (se 2 (by rfl) ⟨16105884, by rfl⟩ : syracuseStep 42949025 = 32211769) B32211769
theorem B28632683 : Blo 2091435 28632683 := bstep (se 1 (by rfl) ⟨21474512, by rfl⟩ : syracuseStep 28632683 = 42949025) B42949025
theorem B19088455 : Blo 2091435 19088455 := bstep (se 1 (by rfl) ⟨14316341, by rfl⟩ : syracuseStep 19088455 = 28632683) B28632683
theorem B25451273 : Blo 2091435 25451273 := bstep (se 2 (by rfl) ⟨9544227, by rfl⟩ : syracuseStep 25451273 = 19088455) B19088455
theorem B67870061 : Blo 2091435 67870061 := bstep (se 3 (by rfl) ⟨12725636, by rfl⟩ : syracuseStep 67870061 = 25451273) B25451273
theorem B45246707 : Blo 2091435 45246707 := bstep (se 1 (by rfl) ⟨33935030, by rfl⟩ : syracuseStep 45246707 = 67870061) B67870061
theorem B30164471 : Blo 2091435 30164471 := bstep (se 1 (by rfl) ⟨22623353, by rfl⟩ : syracuseStep 30164471 = 45246707) B45246707
theorem B20109647 : Blo 2091435 20109647 := bstep (se 1 (by rfl) ⟨15082235, by rfl⟩ : syracuseStep 20109647 = 30164471) B30164471
theorem B13406431 : Blo 2091435 13406431 := bstep (se 1 (by rfl) ⟨10054823, by rfl⟩ : syracuseStep 13406431 = 20109647) B20109647
theorem B17875241 : Blo 2091435 17875241 := bstep (se 2 (by rfl) ⟨6703215, by rfl⟩ : syracuseStep 17875241 = 13406431) B13406431
theorem B11916827 : Blo 2091435 11916827 := bstep (se 1 (by rfl) ⟨8937620, by rfl⟩ : syracuseStep 11916827 = 17875241) B17875241
theorem B7944551 : Blo 2091435 7944551 := bstep (se 1 (by rfl) ⟨5958413, by rfl⟩ : syracuseStep 7944551 = 11916827) B11916827
theorem B5296367 : Blo 2091435 5296367 := bstep (se 1 (by rfl) ⟨3972275, by rfl⟩ : syracuseStep 5296367 = 7944551) B7944551
theorem B3530911 : Blo 2091435 3530911 := bstep (se 1 (by rfl) ⟨2648183, by rfl⟩ : syracuseStep 3530911 = 5296367) B5296367
theorem B4707881 : Blo 2091435 4707881 := bstep (se 2 (by rfl) ⟨1765455, by rfl⟩ : syracuseStep 4707881 = 3530911) B3530911
theorem B3138587 : Blo 2091435 3138587 := bstep (se 1 (by rfl) ⟨2353940, by rfl⟩ : syracuseStep 3138587 = 4707881) B4707881
theorem B2092391 : Blo 2091435 2092391 := bstep (se 1 (by rfl) ⟨1569293, by rfl⟩ : syracuseStep 2092391 = 3138587) B3138587
theorem B2353945 : Blo 2091435 2353945 := bbase (se 2 (by rfl) ⟨882729, by rfl⟩ : syracuseStep 2353945 = 1765459) (by norm_num)
theorem B3138593 : Blo 2091435 3138593 := bstep (se 2 (by rfl) ⟨1176972, by rfl⟩ : syracuseStep 3138593 = 2353945) B2353945
theorem B2092395 : Blo 2091435 2092395 := bstep (se 1 (by rfl) ⟨1569296, by rfl⟩ : syracuseStep 2092395 = 3138593) B3138593
theorem B7944581 : Blo 2091435 7944581 := bbase (se 4 (by rfl) ⟨744804, by rfl⟩ : syracuseStep 7944581 = 1489609) (by norm_num)
theorem B5296387 : Blo 2091435 5296387 := bstep (se 1 (by rfl) ⟨3972290, by rfl⟩ : syracuseStep 5296387 = 7944581) B7944581
theorem B7061849 : Blo 2091435 7061849 := bstep (se 2 (by rfl) ⟨2648193, by rfl⟩ : syracuseStep 7061849 = 5296387) B5296387
theorem B4707899 : Blo 2091435 4707899 := bstep (se 1 (by rfl) ⟨3530924, by rfl⟩ : syracuseStep 4707899 = 7061849) B7061849
theorem B3138599 : Blo 2091435 3138599 := bstep (se 1 (by rfl) ⟨2353949, by rfl⟩ : syracuseStep 3138599 = 4707899) B4707899
theorem B2092399 : Blo 2091435 2092399 := bstep (se 1 (by rfl) ⟨1569299, by rfl⟩ : syracuseStep 2092399 = 3138599) B3138599
theorem B3138605 : Blo 2091435 3138605 := bbase (se 3 (by rfl) ⟨588488, by rfl⟩ : syracuseStep 3138605 = 1176977) (by norm_num)
theorem B2092403 : Blo 2091435 2092403 := bstep (se 1 (by rfl) ⟨1569302, by rfl⟩ : syracuseStep 2092403 = 3138605) B3138605
theorem B4707917 : Blo 2091435 4707917 := bbase (se 3 (by rfl) ⟨882734, by rfl⟩ : syracuseStep 4707917 = 1765469) (by norm_num)
theorem B3138611 : Blo 2091435 3138611 := bstep (se 1 (by rfl) ⟨2353958, by rfl⟩ : syracuseStep 3138611 = 4707917) B4707917
theorem B2092407 : Blo 2091435 2092407 := bstep (se 1 (by rfl) ⟨1569305, by rfl⟩ : syracuseStep 2092407 = 3138611) B3138611
theorem B2648209 : Blo 2091435 2648209 := bbase (se 2 (by rfl) ⟨993078, by rfl⟩ : syracuseStep 2648209 = 1986157) (by norm_num)
theorem B3530945 : Blo 2091435 3530945 := bstep (se 2 (by rfl) ⟨1324104, by rfl⟩ : syracuseStep 3530945 = 2648209) B2648209
theorem B2353963 : Blo 2091435 2353963 := bstep (se 1 (by rfl) ⟨1765472, by rfl⟩ : syracuseStep 2353963 = 3530945) B3530945
theorem B3138617 : Blo 2091435 3138617 := bstep (se 2 (by rfl) ⟨1176981, by rfl⟩ : syracuseStep 3138617 = 2353963) B2353963
theorem B2092411 : Blo 2091435 2092411 := bstep (se 1 (by rfl) ⟨1569308, by rfl⟩ : syracuseStep 2092411 = 3138617) B3138617
theorem B4468861 : Blo 2091435 4468861 := bbase (se 3 (by rfl) ⟨837911, by rfl⟩ : syracuseStep 4468861 = 1675823) (by norm_num)
theorem B23833925 : Blo 2091435 23833925 := bstep (se 4 (by rfl) ⟨2234430, by rfl⟩ : syracuseStep 23833925 = 4468861) B4468861
theorem B15889283 : Blo 2091435 15889283 := bstep (se 1 (by rfl) ⟨11916962, by rfl⟩ : syracuseStep 15889283 = 23833925) B23833925
theorem B10592855 : Blo 2091435 10592855 := bstep (se 1 (by rfl) ⟨7944641, by rfl⟩ : syracuseStep 10592855 = 15889283) B15889283
theorem B7061903 : Blo 2091435 7061903 := bstep (se 1 (by rfl) ⟨5296427, by rfl⟩ : syracuseStep 7061903 = 10592855) B10592855
theorem B4707935 : Blo 2091435 4707935 := bstep (se 1 (by rfl) ⟨3530951, by rfl⟩ : syracuseStep 4707935 = 7061903) B7061903
theorem B3138623 : Blo 2091435 3138623 := bstep (se 1 (by rfl) ⟨2353967, by rfl⟩ : syracuseStep 3138623 = 4707935) B4707935
theorem B2092415 : Blo 2091435 2092415 := bstep (se 1 (by rfl) ⟨1569311, by rfl⟩ : syracuseStep 2092415 = 3138623) B3138623
theorem B3138629 : Blo 2091435 3138629 := bbase (se 4 (by rfl) ⟨294246, by rfl⟩ : syracuseStep 3138629 = 588493) (by norm_num)
theorem B2092419 : Blo 2091435 2092419 := bstep (se 1 (by rfl) ⟨1569314, by rfl⟩ : syracuseStep 2092419 = 3138629) B3138629
theorem B3530965 : Blo 2091435 3530965 := bbase (se 7 (by rfl) ⟨41378, by rfl⟩ : syracuseStep 3530965 = 82757) (by norm_num)
theorem B4707953 : Blo 2091435 4707953 := bstep (se 2 (by rfl) ⟨1765482, by rfl⟩ : syracuseStep 4707953 = 3530965) B3530965
theorem B3138635 : Blo 2091435 3138635 := bstep (se 1 (by rfl) ⟨2353976, by rfl⟩ : syracuseStep 3138635 = 4707953) B4707953
theorem B2092423 : Blo 2091435 2092423 := bstep (se 1 (by rfl) ⟨1569317, by rfl⟩ : syracuseStep 2092423 = 3138635) B3138635
theorem B2353981 : Blo 2091435 2353981 := bbase (se 3 (by rfl) ⟨441371, by rfl⟩ : syracuseStep 2353981 = 882743) (by norm_num)
theorem B3138641 : Blo 2091435 3138641 := bstep (se 2 (by rfl) ⟨1176990, by rfl⟩ : syracuseStep 3138641 = 2353981) B2353981
theorem B2092427 : Blo 2091435 2092427 := bstep (se 1 (by rfl) ⟨1569320, by rfl⟩ : syracuseStep 2092427 = 3138641) B3138641
theorem B7061957 : Blo 2091435 7061957 := bbase (se 4 (by rfl) ⟨662058, by rfl⟩ : syracuseStep 7061957 = 1324117) (by norm_num)
theorem B4707971 : Blo 2091435 4707971 := bstep (se 1 (by rfl) ⟨3530978, by rfl⟩ : syracuseStep 4707971 = 7061957) B7061957
theorem B3138647 : Blo 2091435 3138647 := bstep (se 1 (by rfl) ⟨2353985, by rfl⟩ : syracuseStep 3138647 = 4707971) B4707971
theorem B2092431 : Blo 2091435 2092431 := bstep (se 1 (by rfl) ⟨1569323, by rfl⟩ : syracuseStep 2092431 = 3138647) B3138647
theorem B3138653 : Blo 2091435 3138653 := bbase (se 3 (by rfl) ⟨588497, by rfl⟩ : syracuseStep 3138653 = 1176995) (by norm_num)
theorem B2092435 : Blo 2091435 2092435 := bstep (se 1 (by rfl) ⟨1569326, by rfl⟩ : syracuseStep 2092435 = 3138653) B3138653
theorem B4707989 : Blo 2091435 4707989 := bbase (se 6 (by rfl) ⟨110343, by rfl⟩ : syracuseStep 4707989 = 220687) (by norm_num)
theorem B3138659 : Blo 2091435 3138659 := bstep (se 1 (by rfl) ⟨2353994, by rfl⟩ : syracuseStep 3138659 = 4707989) B4707989
theorem B2092439 : Blo 2091435 2092439 := bstep (se 1 (by rfl) ⟨1569329, by rfl⟩ : syracuseStep 2092439 = 3138659) B3138659
theorem B2234461 : Blo 2091435 2234461 := bbase (se 3 (by rfl) ⟨418961, by rfl⟩ : syracuseStep 2234461 = 837923) (by norm_num)
theorem B2979281 : Blo 2091435 2979281 := bstep (se 2 (by rfl) ⟨1117230, by rfl⟩ : syracuseStep 2979281 = 2234461) B2234461
theorem B7944749 : Blo 2091435 7944749 := bstep (se 3 (by rfl) ⟨1489640, by rfl⟩ : syracuseStep 7944749 = 2979281) B2979281
theorem B5296499 : Blo 2091435 5296499 := bstep (se 1 (by rfl) ⟨3972374, by rfl⟩ : syracuseStep 5296499 = 7944749) B7944749
theorem B3530999 : Blo 2091435 3530999 := bstep (se 1 (by rfl) ⟨2648249, by rfl⟩ : syracuseStep 3530999 = 5296499) B5296499
theorem B2353999 : Blo 2091435 2353999 := bstep (se 1 (by rfl) ⟨1765499, by rfl⟩ : syracuseStep 2353999 = 3530999) B3530999
theorem B3138665 : Blo 2091435 3138665 := bstep (se 2 (by rfl) ⟨1176999, by rfl⟩ : syracuseStep 3138665 = 2353999) B2353999
theorem B2092443 : Blo 2091435 2092443 := bstep (se 1 (by rfl) ⟨1569332, by rfl⟩ : syracuseStep 2092443 = 3138665) B3138665
theorem B2513773 : Blo 2091435 2513773 := bbase (se 3 (by rfl) ⟨471332, by rfl⟩ : syracuseStep 2513773 = 942665) (by norm_num)
theorem B13406789 : Blo 2091435 13406789 := bstep (se 4 (by rfl) ⟨1256886, by rfl⟩ : syracuseStep 13406789 = 2513773) B2513773
theorem B8937859 : Blo 2091435 8937859 := bstep (se 1 (by rfl) ⟨6703394, by rfl⟩ : syracuseStep 8937859 = 13406789) B13406789
theorem B11917145 : Blo 2091435 11917145 := bstep (se 2 (by rfl) ⟨4468929, by rfl⟩ : syracuseStep 11917145 = 8937859) B8937859
theorem B7944763 : Blo 2091435 7944763 := bstep (se 1 (by rfl) ⟨5958572, by rfl⟩ : syracuseStep 7944763 = 11917145) B11917145
theorem B10593017 : Blo 2091435 10593017 := bstep (se 2 (by rfl) ⟨3972381, by rfl⟩ : syracuseStep 10593017 = 7944763) B7944763
theorem B7062011 : Blo 2091435 7062011 := bstep (se 1 (by rfl) ⟨5296508, by rfl⟩ : syracuseStep 7062011 = 10593017) B10593017
theorem B4708007 : Blo 2091435 4708007 := bstep (se 1 (by rfl) ⟨3531005, by rfl⟩ : syracuseStep 4708007 = 7062011) B7062011
theorem B3138671 : Blo 2091435 3138671 := bstep (se 1 (by rfl) ⟨2354003, by rfl⟩ : syracuseStep 3138671 = 4708007) B4708007
theorem B2092447 : Blo 2091435 2092447 := bstep (se 1 (by rfl) ⟨1569335, by rfl⟩ : syracuseStep 2092447 = 3138671) B3138671
theorem B3138677 : Blo 2091435 3138677 := bbase (se 5 (by rfl) ⟨147125, by rfl⟩ : syracuseStep 3138677 = 294251) (by norm_num)
theorem B2092451 : Blo 2091435 2092451 := bstep (se 1 (by rfl) ⟨1569338, by rfl⟩ : syracuseStep 2092451 = 3138677) B3138677
theorem B3972397 : Blo 2091435 3972397 := bbase (se 3 (by rfl) ⟨744824, by rfl⟩ : syracuseStep 3972397 = 1489649) (by norm_num)
theorem B5296529 : Blo 2091435 5296529 := bstep (se 2 (by rfl) ⟨1986198, by rfl⟩ : syracuseStep 5296529 = 3972397) B3972397
theorem B3531019 : Blo 2091435 3531019 := bstep (se 1 (by rfl) ⟨2648264, by rfl⟩ : syracuseStep 3531019 = 5296529) B5296529
theorem B4708025 : Blo 2091435 4708025 := bstep (se 2 (by rfl) ⟨1765509, by rfl⟩ : syracuseStep 4708025 = 3531019) B3531019
theorem B3138683 : Blo 2091435 3138683 := bstep (se 1 (by rfl) ⟨2354012, by rfl⟩ : syracuseStep 3138683 = 4708025) B4708025
theorem B2092455 : Blo 2091435 2092455 := bstep (se 1 (by rfl) ⟨1569341, by rfl⟩ : syracuseStep 2092455 = 3138683) B3138683
theorem B2354017 : Blo 2091435 2354017 := bbase (se 2 (by rfl) ⟨882756, by rfl⟩ : syracuseStep 2354017 = 1765513) (by norm_num)
theorem B3138689 : Blo 2091435 3138689 := bstep (se 2 (by rfl) ⟨1177008, by rfl⟩ : syracuseStep 3138689 = 2354017) B2354017
theorem B2092459 : Blo 2091435 2092459 := bstep (se 1 (by rfl) ⟨1569344, by rfl⟩ : syracuseStep 2092459 = 3138689) B3138689
theorem B5296549 : Blo 2091435 5296549 := bbase (se 4 (by rfl) ⟨496551, by rfl⟩ : syracuseStep 5296549 = 993103) (by norm_num)
theorem B7062065 : Blo 2091435 7062065 := bstep (se 2 (by rfl) ⟨2648274, by rfl⟩ : syracuseStep 7062065 = 5296549) B5296549
theorem B4708043 : Blo 2091435 4708043 := bstep (se 1 (by rfl) ⟨3531032, by rfl⟩ : syracuseStep 4708043 = 7062065) B7062065
theorem B3138695 : Blo 2091435 3138695 := bstep (se 1 (by rfl) ⟨2354021, by rfl⟩ : syracuseStep 3138695 = 4708043) B4708043
theorem B2092463 : Blo 2091435 2092463 := bstep (se 1 (by rfl) ⟨1569347, by rfl⟩ : syracuseStep 2092463 = 3138695) B3138695
theorem B3138701 : Blo 2091435 3138701 := bbase (se 3 (by rfl) ⟨588506, by rfl⟩ : syracuseStep 3138701 = 1177013) (by norm_num)
theorem B2092467 : Blo 2091435 2092467 := bstep (se 1 (by rfl) ⟨1569350, by rfl⟩ : syracuseStep 2092467 = 3138701) B3138701
theorem B4708061 : Blo 2091435 4708061 := bbase (se 3 (by rfl) ⟨882761, by rfl⟩ : syracuseStep 4708061 = 1765523) (by norm_num)
theorem B3138707 : Blo 2091435 3138707 := bstep (se 1 (by rfl) ⟨2354030, by rfl⟩ : syracuseStep 3138707 = 4708061) B4708061
theorem B2092471 : Blo 2091435 2092471 := bstep (se 1 (by rfl) ⟨1569353, by rfl⟩ : syracuseStep 2092471 = 3138707) B3138707
theorem B3531053 : Blo 2091435 3531053 := bbase (se 3 (by rfl) ⟨662072, by rfl⟩ : syracuseStep 3531053 = 1324145) (by norm_num)
theorem B2354035 : Blo 2091435 2354035 := bstep (se 1 (by rfl) ⟨1765526, by rfl⟩ : syracuseStep 2354035 = 3531053) B3531053
theorem B3138713 : Blo 2091435 3138713 := bstep (se 2 (by rfl) ⟨1177017, by rfl⟩ : syracuseStep 3138713 = 2354035) B2354035
theorem B2092475 : Blo 2091435 2092475 := bstep (se 1 (by rfl) ⟨1569356, by rfl⟩ : syracuseStep 2092475 = 3138713) B3138713
theorem B3770717 : Blo 2091435 3770717 := bbase (se 3 (by rfl) ⟨707009, by rfl⟩ : syracuseStep 3770717 = 1414019) (by norm_num)
theorem B40220981 : Blo 2091435 40220981 := bstep (se 5 (by rfl) ⟨1885358, by rfl⟩ : syracuseStep 40220981 = 3770717) B3770717
theorem B26813987 : Blo 2091435 26813987 := bstep (se 1 (by rfl) ⟨20110490, by rfl⟩ : syracuseStep 26813987 = 40220981) B40220981
theorem B17875991 : Blo 2091435 17875991 := bstep (se 1 (by rfl) ⟨13406993, by rfl⟩ : syracuseStep 17875991 = 26813987) B26813987
theorem B11917327 : Blo 2091435 11917327 := bstep (se 1 (by rfl) ⟨8937995, by rfl⟩ : syracuseStep 11917327 = 17875991) B17875991
theorem B15889769 : Blo 2091435 15889769 := bstep (se 2 (by rfl) ⟨5958663, by rfl⟩ : syracuseStep 15889769 = 11917327) B11917327
theorem B10593179 : Blo 2091435 10593179 := bstep (se 1 (by rfl) ⟨7944884, by rfl⟩ : syracuseStep 10593179 = 15889769) B15889769
theorem B7062119 : Blo 2091435 7062119 := bstep (se 1 (by rfl) ⟨5296589, by rfl⟩ : syracuseStep 7062119 = 10593179) B10593179
theorem B4708079 : Blo 2091435 4708079 := bstep (se 1 (by rfl) ⟨3531059, by rfl⟩ : syracuseStep 4708079 = 7062119) B7062119
theorem B3138719 : Blo 2091435 3138719 := bstep (se 1 (by rfl) ⟨2354039, by rfl⟩ : syracuseStep 3138719 = 4708079) B4708079
theorem B2092479 : Blo 2091435 2092479 := bstep (se 1 (by rfl) ⟨1569359, by rfl⟩ : syracuseStep 2092479 = 3138719) B3138719
theorem B3138725 : Blo 2091435 3138725 := bbase (se 4 (by rfl) ⟨294255, by rfl⟩ : syracuseStep 3138725 = 588511) (by norm_num)
theorem B2092483 : Blo 2091435 2092483 := bstep (se 1 (by rfl) ⟨1569362, by rfl⟩ : syracuseStep 2092483 = 3138725) B3138725
theorem B2648305 : Blo 2091435 2648305 := bbase (se 2 (by rfl) ⟨993114, by rfl⟩ : syracuseStep 2648305 = 1986229) (by norm_num)
theorem B3531073 : Blo 2091435 3531073 := bstep (se 2 (by rfl) ⟨1324152, by rfl⟩ : syracuseStep 3531073 = 2648305) B2648305
theorem B4708097 : Blo 2091435 4708097 := bstep (se 2 (by rfl) ⟨1765536, by rfl⟩ : syracuseStep 4708097 = 3531073) B3531073
theorem B3138731 : Blo 2091435 3138731 := bstep (se 1 (by rfl) ⟨2354048, by rfl⟩ : syracuseStep 3138731 = 4708097) B4708097
theorem B2092487 : Blo 2091435 2092487 := bstep (se 1 (by rfl) ⟨1569365, by rfl⟩ : syracuseStep 2092487 = 3138731) B3138731
theorem B2354053 : Blo 2091435 2354053 := bbase (se 4 (by rfl) ⟨220692, by rfl⟩ : syracuseStep 2354053 = 441385) (by norm_num)
theorem B3138737 : Blo 2091435 3138737 := bstep (se 2 (by rfl) ⟨1177026, by rfl⟩ : syracuseStep 3138737 = 2354053) B2354053
theorem B2092491 : Blo 2091435 2092491 := bstep (se 1 (by rfl) ⟨1569368, by rfl⟩ : syracuseStep 2092491 = 3138737) B3138737
theorem B2684449 : Blo 2091435 2684449 := bbase (se 2 (by rfl) ⟨1006668, by rfl⟩ : syracuseStep 2684449 = 2013337) (by norm_num)
theorem B3579265 : Blo 2091435 3579265 := bstep (se 2 (by rfl) ⟨1342224, by rfl⟩ : syracuseStep 3579265 = 2684449) B2684449
theorem B4772353 : Blo 2091435 4772353 := bstep (se 2 (by rfl) ⟨1789632, by rfl⟩ : syracuseStep 4772353 = 3579265) B3579265
theorem B6363137 : Blo 2091435 6363137 := bstep (se 2 (by rfl) ⟨2386176, by rfl⟩ : syracuseStep 6363137 = 4772353) B4772353
theorem B16968365 : Blo 2091435 16968365 := bstep (se 3 (by rfl) ⟨3181568, by rfl⟩ : syracuseStep 16968365 = 6363137) B6363137
theorem B11312243 : Blo 2091435 11312243 := bstep (se 1 (by rfl) ⟨8484182, by rfl⟩ : syracuseStep 11312243 = 16968365) B16968365
theorem B7541495 : Blo 2091435 7541495 := bstep (se 1 (by rfl) ⟨5656121, by rfl⟩ : syracuseStep 7541495 = 11312243) B11312243
theorem B5027663 : Blo 2091435 5027663 := bstep (se 1 (by rfl) ⟨3770747, by rfl⟩ : syracuseStep 5027663 = 7541495) B7541495
theorem B3351775 : Blo 2091435 3351775 := bstep (se 1 (by rfl) ⟨2513831, by rfl⟩ : syracuseStep 3351775 = 5027663) B5027663
theorem B4469033 : Blo 2091435 4469033 := bstep (se 2 (by rfl) ⟨1675887, by rfl⟩ : syracuseStep 4469033 = 3351775) B3351775
theorem B2979355 : Blo 2091435 2979355 := bstep (se 1 (by rfl) ⟨2234516, by rfl⟩ : syracuseStep 2979355 = 4469033) B4469033
theorem B3972473 : Blo 2091435 3972473 := bstep (se 2 (by rfl) ⟨1489677, by rfl⟩ : syracuseStep 3972473 = 2979355) B2979355
theorem B2648315 : Blo 2091435 2648315 := bstep (se 1 (by rfl) ⟨1986236, by rfl⟩ : syracuseStep 2648315 = 3972473) B3972473
theorem B7062173 : Blo 2091435 7062173 := bstep (se 3 (by rfl) ⟨1324157, by rfl⟩ : syracuseStep 7062173 = 2648315) B2648315
theorem B4708115 : Blo 2091435 4708115 := bstep (se 1 (by rfl) ⟨3531086, by rfl⟩ : syracuseStep 4708115 = 7062173) B7062173
theorem B3138743 : Blo 2091435 3138743 := bstep (se 1 (by rfl) ⟨2354057, by rfl⟩ : syracuseStep 3138743 = 4708115) B4708115
theorem B2092495 : Blo 2091435 2092495 := bstep (se 1 (by rfl) ⟨1569371, by rfl⟩ : syracuseStep 2092495 = 3138743) B3138743
theorem B3138749 : Blo 2091435 3138749 := bbase (se 3 (by rfl) ⟨588515, by rfl⟩ : syracuseStep 3138749 = 1177031) (by norm_num)
theorem B2092499 : Blo 2091435 2092499 := bstep (se 1 (by rfl) ⟨1569374, by rfl⟩ : syracuseStep 2092499 = 3138749) B3138749
theorem B4708133 : Blo 2091435 4708133 := bbase (se 4 (by rfl) ⟨441387, by rfl⟩ : syracuseStep 4708133 = 882775) (by norm_num)
theorem B3138755 : Blo 2091435 3138755 := bstep (se 1 (by rfl) ⟨2354066, by rfl⟩ : syracuseStep 3138755 = 4708133) B4708133
theorem B2092503 : Blo 2091435 2092503 := bstep (se 1 (by rfl) ⟨1569377, by rfl⟩ : syracuseStep 2092503 = 3138755) B3138755
theorem B5296661 : Blo 2091435 5296661 := bbase (se 6 (by rfl) ⟨124140, by rfl⟩ : syracuseStep 5296661 = 248281) (by norm_num)
theorem B3531107 : Blo 2091435 3531107 := bstep (se 1 (by rfl) ⟨2648330, by rfl⟩ : syracuseStep 3531107 = 5296661) B5296661
theorem B2354071 : Blo 2091435 2354071 := bstep (se 1 (by rfl) ⟨1765553, by rfl⟩ : syracuseStep 2354071 = 3531107) B3531107
theorem B3138761 : Blo 2091435 3138761 := bstep (se 2 (by rfl) ⟨1177035, by rfl⟩ : syracuseStep 3138761 = 2354071) B2354071
theorem B2092507 : Blo 2091435 2092507 := bstep (se 1 (by rfl) ⟨1569380, by rfl⟩ : syracuseStep 2092507 = 3138761) B3138761
theorem B8938133 : Blo 2091435 8938133 := bbase (se 6 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 8938133 = 418975) (by norm_num)
theorem B5958755 : Blo 2091435 5958755 := bstep (se 1 (by rfl) ⟨4469066, by rfl⟩ : syracuseStep 5958755 = 8938133) B8938133
theorem B3972503 : Blo 2091435 3972503 := bstep (se 1 (by rfl) ⟨2979377, by rfl⟩ : syracuseStep 3972503 = 5958755) B5958755
theorem B10593341 : Blo 2091435 10593341 := bstep (se 3 (by rfl) ⟨1986251, by rfl⟩ : syracuseStep 10593341 = 3972503) B3972503
theorem B7062227 : Blo 2091435 7062227 := bstep (se 1 (by rfl) ⟨5296670, by rfl⟩ : syracuseStep 7062227 = 10593341) B10593341
theorem B4708151 : Blo 2091435 4708151 := bstep (se 1 (by rfl) ⟨3531113, by rfl⟩ : syracuseStep 4708151 = 7062227) B7062227
theorem B3138767 : Blo 2091435 3138767 := bstep (se 1 (by rfl) ⟨2354075, by rfl⟩ : syracuseStep 3138767 = 4708151) B4708151
theorem B2092511 : Blo 2091435 2092511 := bstep (se 1 (by rfl) ⟨1569383, by rfl⟩ : syracuseStep 2092511 = 3138767) B3138767
theorem B3138773 : Blo 2091435 3138773 := bbase (se 7 (by rfl) ⟨36782, by rfl⟩ : syracuseStep 3138773 = 73565) (by norm_num)
theorem B2092515 : Blo 2091435 2092515 := bstep (se 1 (by rfl) ⟨1569386, by rfl⟩ : syracuseStep 2092515 = 3138773) B3138773
theorem B2979389 : Blo 2091435 2979389 := bbase (se 3 (by rfl) ⟨558635, by rfl⟩ : syracuseStep 2979389 = 1117271) (by norm_num)
theorem B7945037 : Blo 2091435 7945037 := bstep (se 3 (by rfl) ⟨1489694, by rfl⟩ : syracuseStep 7945037 = 2979389) B2979389
theorem B5296691 : Blo 2091435 5296691 := bstep (se 1 (by rfl) ⟨3972518, by rfl⟩ : syracuseStep 5296691 = 7945037) B7945037
theorem B3531127 : Blo 2091435 3531127 := bstep (se 1 (by rfl) ⟨2648345, by rfl⟩ : syracuseStep 3531127 = 5296691) B5296691
theorem B4708169 : Blo 2091435 4708169 := bstep (se 2 (by rfl) ⟨1765563, by rfl⟩ : syracuseStep 4708169 = 3531127) B3531127
theorem B3138779 : Blo 2091435 3138779 := bstep (se 1 (by rfl) ⟨2354084, by rfl⟩ : syracuseStep 3138779 = 4708169) B4708169
theorem B2092519 : Blo 2091435 2092519 := bstep (se 1 (by rfl) ⟨1569389, by rfl⟩ : syracuseStep 2092519 = 3138779) B3138779
theorem B2354089 : Blo 2091435 2354089 := bbase (se 2 (by rfl) ⟨882783, by rfl⟩ : syracuseStep 2354089 = 1765567) (by norm_num)
theorem B3138785 : Blo 2091435 3138785 := bstep (se 2 (by rfl) ⟨1177044, by rfl⟩ : syracuseStep 3138785 = 2354089) B2354089
theorem B2092523 : Blo 2091435 2092523 := bstep (se 1 (by rfl) ⟨1569392, by rfl⟩ : syracuseStep 2092523 = 3138785) B3138785
theorem B10055477 : Blo 2091435 10055477 := bbase (se 5 (by rfl) ⟨471350, by rfl⟩ : syracuseStep 10055477 = 942701) (by norm_num)
theorem B6703651 : Blo 2091435 6703651 := bstep (se 1 (by rfl) ⟨5027738, by rfl⟩ : syracuseStep 6703651 = 10055477) B10055477
theorem B8938201 : Blo 2091435 8938201 := bstep (se 2 (by rfl) ⟨3351825, by rfl⟩ : syracuseStep 8938201 = 6703651) B6703651
theorem B11917601 : Blo 2091435 11917601 := bstep (se 2 (by rfl) ⟨4469100, by rfl⟩ : syracuseStep 11917601 = 8938201) B8938201
theorem B7945067 : Blo 2091435 7945067 := bstep (se 1 (by rfl) ⟨5958800, by rfl⟩ : syracuseStep 7945067 = 11917601) B11917601
theorem B5296711 : Blo 2091435 5296711 := bstep (se 1 (by rfl) ⟨3972533, by rfl⟩ : syracuseStep 5296711 = 7945067) B7945067
theorem B7062281 : Blo 2091435 7062281 := bstep (se 2 (by rfl) ⟨2648355, by rfl⟩ : syracuseStep 7062281 = 5296711) B5296711
theorem B4708187 : Blo 2091435 4708187 := bstep (se 1 (by rfl) ⟨3531140, by rfl⟩ : syracuseStep 4708187 = 7062281) B7062281
theorem B3138791 : Blo 2091435 3138791 := bstep (se 1 (by rfl) ⟨2354093, by rfl⟩ : syracuseStep 3138791 = 4708187) B4708187
theorem B2092527 : Blo 2091435 2092527 := bstep (se 1 (by rfl) ⟨1569395, by rfl⟩ : syracuseStep 2092527 = 3138791) B3138791
theorem B3138797 : Blo 2091435 3138797 := bbase (se 3 (by rfl) ⟨588524, by rfl⟩ : syracuseStep 3138797 = 1177049) (by norm_num)
theorem B2092531 : Blo 2091435 2092531 := bstep (se 1 (by rfl) ⟨1569398, by rfl⟩ : syracuseStep 2092531 = 3138797) B3138797
theorem B4708205 : Blo 2091435 4708205 := bbase (se 3 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 4708205 = 1765577) (by norm_num)
theorem B3138803 : Blo 2091435 3138803 := bstep (se 1 (by rfl) ⟨2354102, by rfl⟩ : syracuseStep 3138803 = 4708205) B4708205
theorem B2092535 : Blo 2091435 2092535 := bstep (se 1 (by rfl) ⟨1569401, by rfl⟩ : syracuseStep 2092535 = 3138803) B3138803
theorem B3972557 : Blo 2091435 3972557 := bbase (se 3 (by rfl) ⟨744854, by rfl⟩ : syracuseStep 3972557 = 1489709) (by norm_num)
theorem B2648371 : Blo 2091435 2648371 := bstep (se 1 (by rfl) ⟨1986278, by rfl⟩ : syracuseStep 2648371 = 3972557) B3972557
theorem B3531161 : Blo 2091435 3531161 := bstep (se 2 (by rfl) ⟨1324185, by rfl⟩ : syracuseStep 3531161 = 2648371) B2648371
theorem B2354107 : Blo 2091435 2354107 := bstep (se 1 (by rfl) ⟨1765580, by rfl⟩ : syracuseStep 2354107 = 3531161) B3531161
theorem B3138809 : Blo 2091435 3138809 := bstep (se 2 (by rfl) ⟨1177053, by rfl⟩ : syracuseStep 3138809 = 2354107) B2354107
theorem B2092539 : Blo 2091435 2092539 := bstep (se 1 (by rfl) ⟨1569404, by rfl⟩ : syracuseStep 2092539 = 3138809) B3138809
theorem B8484373 : Blo 2091435 8484373 := bbase (se 6 (by rfl) ⟨198852, by rfl⟩ : syracuseStep 8484373 = 397705) (by norm_num)
theorem B11312497 : Blo 2091435 11312497 := bstep (se 2 (by rfl) ⟨4242186, by rfl⟩ : syracuseStep 11312497 = 8484373) B8484373
theorem B15083329 : Blo 2091435 15083329 := bstep (se 2 (by rfl) ⟨5656248, by rfl⟩ : syracuseStep 15083329 = 11312497) B11312497
theorem B20111105 : Blo 2091435 20111105 := bstep (se 2 (by rfl) ⟨7541664, by rfl⟩ : syracuseStep 20111105 = 15083329) B15083329
theorem B53629613 : Blo 2091435 53629613 := bstep (se 3 (by rfl) ⟨10055552, by rfl⟩ : syracuseStep 53629613 = 20111105) B20111105
theorem B35753075 : Blo 2091435 35753075 := bstep (se 1 (by rfl) ⟨26814806, by rfl⟩ : syracuseStep 35753075 = 53629613) B53629613
theorem B23835383 : Blo 2091435 23835383 := bstep (se 1 (by rfl) ⟨17876537, by rfl⟩ : syracuseStep 23835383 = 35753075) B35753075
theorem B15890255 : Blo 2091435 15890255 := bstep (se 1 (by rfl) ⟨11917691, by rfl⟩ : syracuseStep 15890255 = 23835383) B23835383
theorem B10593503 : Blo 2091435 10593503 := bstep (se 1 (by rfl) ⟨7945127, by rfl⟩ : syracuseStep 10593503 = 15890255) B15890255
theorem B7062335 : Blo 2091435 7062335 := bstep (se 1 (by rfl) ⟨5296751, by rfl⟩ : syracuseStep 7062335 = 10593503) B10593503
theorem B4708223 : Blo 2091435 4708223 := bstep (se 1 (by rfl) ⟨3531167, by rfl⟩ : syracuseStep 4708223 = 7062335) B7062335
theorem B3138815 : Blo 2091435 3138815 := bstep (se 1 (by rfl) ⟨2354111, by rfl⟩ : syracuseStep 3138815 = 4708223) B4708223
theorem B2092543 : Blo 2091435 2092543 := bstep (se 1 (by rfl) ⟨1569407, by rfl⟩ : syracuseStep 2092543 = 3138815) B3138815
theorem B3138821 : Blo 2091435 3138821 := bbase (se 4 (by rfl) ⟨294264, by rfl⟩ : syracuseStep 3138821 = 588529) (by norm_num)
theorem B2092547 : Blo 2091435 2092547 := bstep (se 1 (by rfl) ⟨1569410, by rfl⟩ : syracuseStep 2092547 = 3138821) B3138821
theorem B3531181 : Blo 2091435 3531181 := bbase (se 3 (by rfl) ⟨662096, by rfl⟩ : syracuseStep 3531181 = 1324193) (by norm_num)
theorem B4708241 : Blo 2091435 4708241 := bstep (se 2 (by rfl) ⟨1765590, by rfl⟩ : syracuseStep 4708241 = 3531181) B3531181
theorem B3138827 : Blo 2091435 3138827 := bstep (se 1 (by rfl) ⟨2354120, by rfl⟩ : syracuseStep 3138827 = 4708241) B4708241
theorem B2092551 : Blo 2091435 2092551 := bstep (se 1 (by rfl) ⟨1569413, by rfl⟩ : syracuseStep 2092551 = 3138827) B3138827
theorem B2354125 : Blo 2091435 2354125 := bbase (se 3 (by rfl) ⟨441398, by rfl⟩ : syracuseStep 2354125 = 882797) (by norm_num)
theorem B3138833 : Blo 2091435 3138833 := bstep (se 2 (by rfl) ⟨1177062, by rfl⟩ : syracuseStep 3138833 = 2354125) B2354125
theorem B2092555 : Blo 2091435 2092555 := bstep (se 1 (by rfl) ⟨1569416, by rfl⟩ : syracuseStep 2092555 = 3138833) B3138833
theorem B7062389 : Blo 2091435 7062389 := bbase (se 5 (by rfl) ⟨331049, by rfl⟩ : syracuseStep 7062389 = 662099) (by norm_num)
theorem B4708259 : Blo 2091435 4708259 := bstep (se 1 (by rfl) ⟨3531194, by rfl⟩ : syracuseStep 4708259 = 7062389) B7062389
theorem B3138839 : Blo 2091435 3138839 := bstep (se 1 (by rfl) ⟨2354129, by rfl⟩ : syracuseStep 3138839 = 4708259) B4708259
theorem B2092559 : Blo 2091435 2092559 := bstep (se 1 (by rfl) ⟨1569419, by rfl⟩ : syracuseStep 2092559 = 3138839) B3138839
theorem B3138845 : Blo 2091435 3138845 := bbase (se 3 (by rfl) ⟨588533, by rfl⟩ : syracuseStep 3138845 = 1177067) (by norm_num)
theorem B2092563 : Blo 2091435 2092563 := bstep (se 1 (by rfl) ⟨1569422, by rfl⟩ : syracuseStep 2092563 = 3138845) B3138845
theorem B4708277 : Blo 2091435 4708277 := bbase (se 5 (by rfl) ⟨220700, by rfl⟩ : syracuseStep 4708277 = 441401) (by norm_num)
theorem B3138851 : Blo 2091435 3138851 := bstep (se 1 (by rfl) ⟨2354138, by rfl⟩ : syracuseStep 3138851 = 4708277) B4708277
theorem B2092567 : Blo 2091435 2092567 := bstep (se 1 (by rfl) ⟨1569425, by rfl⟩ : syracuseStep 2092567 = 3138851) B3138851
theorem B5027845 : Blo 2091435 5027845 := bbase (se 4 (by rfl) ⟨471360, by rfl⟩ : syracuseStep 5027845 = 942721) (by norm_num)
theorem B6703793 : Blo 2091435 6703793 := bstep (se 2 (by rfl) ⟨2513922, by rfl⟩ : syracuseStep 6703793 = 5027845) B5027845
theorem B4469195 : Blo 2091435 4469195 := bstep (se 1 (by rfl) ⟨3351896, by rfl⟩ : syracuseStep 4469195 = 6703793) B6703793
theorem B11917853 : Blo 2091435 11917853 := bstep (se 3 (by rfl) ⟨2234597, by rfl⟩ : syracuseStep 11917853 = 4469195) B4469195
theorem B7945235 : Blo 2091435 7945235 := bstep (se 1 (by rfl) ⟨5958926, by rfl⟩ : syracuseStep 7945235 = 11917853) B11917853
theorem B5296823 : Blo 2091435 5296823 := bstep (se 1 (by rfl) ⟨3972617, by rfl⟩ : syracuseStep 5296823 = 7945235) B7945235
theorem B3531215 : Blo 2091435 3531215 := bstep (se 1 (by rfl) ⟨2648411, by rfl⟩ : syracuseStep 3531215 = 5296823) B5296823
theorem B2354143 : Blo 2091435 2354143 := bstep (se 1 (by rfl) ⟨1765607, by rfl⟩ : syracuseStep 2354143 = 3531215) B3531215
theorem B3138857 : Blo 2091435 3138857 := bstep (se 2 (by rfl) ⟨1177071, by rfl⟩ : syracuseStep 3138857 = 2354143) B2354143
theorem B2092571 : Blo 2091435 2092571 := bstep (se 1 (by rfl) ⟨1569428, by rfl⟩ : syracuseStep 2092571 = 3138857) B3138857
theorem B4242253 : Blo 2091435 4242253 := bbase (se 3 (by rfl) ⟨795422, by rfl⟩ : syracuseStep 4242253 = 1590845) (by norm_num)
theorem B5656337 : Blo 2091435 5656337 := bstep (se 2 (by rfl) ⟨2121126, by rfl⟩ : syracuseStep 5656337 = 4242253) B4242253
theorem B3770891 : Blo 2091435 3770891 := bstep (se 1 (by rfl) ⟨2828168, by rfl⟩ : syracuseStep 3770891 = 5656337) B5656337
theorem B2513927 : Blo 2091435 2513927 := bstep (se 1 (by rfl) ⟨1885445, by rfl⟩ : syracuseStep 2513927 = 3770891) B3770891
theorem B6703805 : Blo 2091435 6703805 := bstep (se 3 (by rfl) ⟨1256963, by rfl⟩ : syracuseStep 6703805 = 2513927) B2513927
theorem B4469203 : Blo 2091435 4469203 := bstep (se 1 (by rfl) ⟨3351902, by rfl⟩ : syracuseStep 4469203 = 6703805) B6703805
theorem B5958937 : Blo 2091435 5958937 := bstep (se 2 (by rfl) ⟨2234601, by rfl⟩ : syracuseStep 5958937 = 4469203) B4469203
theorem B7945249 : Blo 2091435 7945249 := bstep (se 2 (by rfl) ⟨2979468, by rfl⟩ : syracuseStep 7945249 = 5958937) B5958937
theorem B10593665 : Blo 2091435 10593665 := bstep (se 2 (by rfl) ⟨3972624, by rfl⟩ : syracuseStep 10593665 = 7945249) B7945249
theorem B7062443 : Blo 2091435 7062443 := bstep (se 1 (by rfl) ⟨5296832, by rfl⟩ : syracuseStep 7062443 = 10593665) B10593665
theorem B4708295 : Blo 2091435 4708295 := bstep (se 1 (by rfl) ⟨3531221, by rfl⟩ : syracuseStep 4708295 = 7062443) B7062443
theorem B3138863 : Blo 2091435 3138863 := bstep (se 1 (by rfl) ⟨2354147, by rfl⟩ : syracuseStep 3138863 = 4708295) B4708295
theorem B2092575 : Blo 2091435 2092575 := bstep (se 1 (by rfl) ⟨1569431, by rfl⟩ : syracuseStep 2092575 = 3138863) B3138863
theorem B3138869 : Blo 2091435 3138869 := bbase (se 5 (by rfl) ⟨147134, by rfl⟩ : syracuseStep 3138869 = 294269) (by norm_num)
theorem B2092579 : Blo 2091435 2092579 := bstep (se 1 (by rfl) ⟨1569434, by rfl⟩ : syracuseStep 2092579 = 3138869) B3138869
theorem B5296853 : Blo 2091435 5296853 := bbase (se 7 (by rfl) ⟨62072, by rfl⟩ : syracuseStep 5296853 = 124145) (by norm_num)
theorem B3531235 : Blo 2091435 3531235 := bstep (se 1 (by rfl) ⟨2648426, by rfl⟩ : syracuseStep 3531235 = 5296853) B5296853
theorem B4708313 : Blo 2091435 4708313 := bstep (se 2 (by rfl) ⟨1765617, by rfl⟩ : syracuseStep 4708313 = 3531235) B3531235
theorem B3138875 : Blo 2091435 3138875 := bstep (se 1 (by rfl) ⟨2354156, by rfl⟩ : syracuseStep 3138875 = 4708313) B4708313
theorem B2092583 : Blo 2091435 2092583 := bstep (se 1 (by rfl) ⟨1569437, by rfl⟩ : syracuseStep 2092583 = 3138875) B3138875
theorem B2354161 : Blo 2091435 2354161 := bbase (se 2 (by rfl) ⟨882810, by rfl⟩ : syracuseStep 2354161 = 1765621) (by norm_num)
theorem B3138881 : Blo 2091435 3138881 := bstep (se 2 (by rfl) ⟨1177080, by rfl⟩ : syracuseStep 3138881 = 2354161) B2354161
theorem B2092587 : Blo 2091435 2092587 := bstep (se 1 (by rfl) ⟨1569440, by rfl⟩ : syracuseStep 2092587 = 3138881) B3138881
theorem B9545141 : Blo 2091435 9545141 := bbase (se 5 (by rfl) ⟨447428, by rfl⟩ : syracuseStep 9545141 = 894857) (by norm_num)
theorem B25453709 : Blo 2091435 25453709 := bstep (se 3 (by rfl) ⟨4772570, by rfl⟩ : syracuseStep 25453709 = 9545141) B9545141
theorem B16969139 : Blo 2091435 16969139 := bstep (se 1 (by rfl) ⟨12726854, by rfl⟩ : syracuseStep 16969139 = 25453709) B25453709
theorem B11312759 : Blo 2091435 11312759 := bstep (se 1 (by rfl) ⟨8484569, by rfl⟩ : syracuseStep 11312759 = 16969139) B16969139
theorem B7541839 : Blo 2091435 7541839 := bstep (se 1 (by rfl) ⟨5656379, by rfl⟩ : syracuseStep 7541839 = 11312759) B11312759
theorem B10055785 : Blo 2091435 10055785 := bstep (se 2 (by rfl) ⟨3770919, by rfl⟩ : syracuseStep 10055785 = 7541839) B7541839
theorem B13407713 : Blo 2091435 13407713 := bstep (se 2 (by rfl) ⟨5027892, by rfl⟩ : syracuseStep 13407713 = 10055785) B10055785
theorem B8938475 : Blo 2091435 8938475 := bstep (se 1 (by rfl) ⟨6703856, by rfl⟩ : syracuseStep 8938475 = 13407713) B13407713
theorem B5958983 : Blo 2091435 5958983 := bstep (se 1 (by rfl) ⟨4469237, by rfl⟩ : syracuseStep 5958983 = 8938475) B8938475
theorem B3972655 : Blo 2091435 3972655 := bstep (se 1 (by rfl) ⟨2979491, by rfl⟩ : syracuseStep 3972655 = 5958983) B5958983
theorem B5296873 : Blo 2091435 5296873 := bstep (se 2 (by rfl) ⟨1986327, by rfl⟩ : syracuseStep 5296873 = 3972655) B3972655
theorem B7062497 : Blo 2091435 7062497 := bstep (se 2 (by rfl) ⟨2648436, by rfl⟩ : syracuseStep 7062497 = 5296873) B5296873
theorem B4708331 : Blo 2091435 4708331 := bstep (se 1 (by rfl) ⟨3531248, by rfl⟩ : syracuseStep 4708331 = 7062497) B7062497
theorem B3138887 : Blo 2091435 3138887 := bstep (se 1 (by rfl) ⟨2354165, by rfl⟩ : syracuseStep 3138887 = 4708331) B4708331
theorem B2092591 : Blo 2091435 2092591 := bstep (se 1 (by rfl) ⟨1569443, by rfl⟩ : syracuseStep 2092591 = 3138887) B3138887
theorem B3138893 : Blo 2091435 3138893 := bbase (se 3 (by rfl) ⟨588542, by rfl⟩ : syracuseStep 3138893 = 1177085) (by norm_num)
theorem B2092595 : Blo 2091435 2092595 := bstep (se 1 (by rfl) ⟨1569446, by rfl⟩ : syracuseStep 2092595 = 3138893) B3138893
theorem B4708349 : Blo 2091435 4708349 := bbase (se 3 (by rfl) ⟨882815, by rfl⟩ : syracuseStep 4708349 = 1765631) (by norm_num)
theorem B3138899 : Blo 2091435 3138899 := bstep (se 1 (by rfl) ⟨2354174, by rfl⟩ : syracuseStep 3138899 = 4708349) B4708349
theorem B2092599 : Blo 2091435 2092599 := bstep (se 1 (by rfl) ⟨1569449, by rfl⟩ : syracuseStep 2092599 = 3138899) B3138899
theorem B3531269 : Blo 2091435 3531269 := bbase (se 4 (by rfl) ⟨331056, by rfl⟩ : syracuseStep 3531269 = 662113) (by norm_num)
theorem B2354179 : Blo 2091435 2354179 := bstep (se 1 (by rfl) ⟨1765634, by rfl⟩ : syracuseStep 2354179 = 3531269) B3531269
theorem B3138905 : Blo 2091435 3138905 := bstep (se 2 (by rfl) ⟨1177089, by rfl⟩ : syracuseStep 3138905 = 2354179) B2354179
theorem B2092603 : Blo 2091435 2092603 := bstep (se 1 (by rfl) ⟨1569452, by rfl⟩ : syracuseStep 2092603 = 3138905) B3138905
theorem B15890741 : Blo 2091435 15890741 := bbase (se 5 (by rfl) ⟨744878, by rfl⟩ : syracuseStep 15890741 = 1489757) (by norm_num)
theorem B10593827 : Blo 2091435 10593827 := bstep (se 1 (by rfl) ⟨7945370, by rfl⟩ : syracuseStep 10593827 = 15890741) B15890741
theorem B7062551 : Blo 2091435 7062551 := bstep (se 1 (by rfl) ⟨5296913, by rfl⟩ : syracuseStep 7062551 = 10593827) B10593827
theorem B4708367 : Blo 2091435 4708367 := bstep (se 1 (by rfl) ⟨3531275, by rfl⟩ : syracuseStep 4708367 = 7062551) B7062551
theorem B3138911 : Blo 2091435 3138911 := bstep (se 1 (by rfl) ⟨2354183, by rfl⟩ : syracuseStep 3138911 = 4708367) B4708367
theorem B2092607 : Blo 2091435 2092607 := bstep (se 1 (by rfl) ⟨1569455, by rfl⟩ : syracuseStep 2092607 = 3138911) B3138911
theorem B3138917 : Blo 2091435 3138917 := bbase (se 4 (by rfl) ⟨294273, by rfl⟩ : syracuseStep 3138917 = 588547) (by norm_num)
theorem B2092611 : Blo 2091435 2092611 := bstep (se 1 (by rfl) ⟨1569458, by rfl⟩ : syracuseStep 2092611 = 3138917) B3138917
theorem B3972701 : Blo 2091435 3972701 := bbase (se 3 (by rfl) ⟨744881, by rfl⟩ : syracuseStep 3972701 = 1489763) (by norm_num)
theorem B2648467 : Blo 2091435 2648467 := bstep (se 1 (by rfl) ⟨1986350, by rfl⟩ : syracuseStep 2648467 = 3972701) B3972701
theorem B3531289 : Blo 2091435 3531289 := bstep (se 2 (by rfl) ⟨1324233, by rfl⟩ : syracuseStep 3531289 = 2648467) B2648467
theorem B4708385 : Blo 2091435 4708385 := bstep (se 2 (by rfl) ⟨1765644, by rfl⟩ : syracuseStep 4708385 = 3531289) B3531289
theorem B3138923 : Blo 2091435 3138923 := bstep (se 1 (by rfl) ⟨2354192, by rfl⟩ : syracuseStep 3138923 = 4708385) B4708385
theorem B2092615 : Blo 2091435 2092615 := bstep (se 1 (by rfl) ⟨1569461, by rfl⟩ : syracuseStep 2092615 = 3138923) B3138923
theorem B2354197 : Blo 2091435 2354197 := bbase (se 6 (by rfl) ⟨55176, by rfl⟩ : syracuseStep 2354197 = 110353) (by norm_num)
theorem B3138929 : Blo 2091435 3138929 := bstep (se 2 (by rfl) ⟨1177098, by rfl⟩ : syracuseStep 3138929 = 2354197) B2354197
theorem B2092619 : Blo 2091435 2092619 := bstep (se 1 (by rfl) ⟨1569464, by rfl⟩ : syracuseStep 2092619 = 3138929) B3138929
theorem B2648477 : Blo 2091435 2648477 := bbase (se 3 (by rfl) ⟨496589, by rfl⟩ : syracuseStep 2648477 = 993179) (by norm_num)
theorem B7062605 : Blo 2091435 7062605 := bstep (se 3 (by rfl) ⟨1324238, by rfl⟩ : syracuseStep 7062605 = 2648477) B2648477
theorem B4708403 : Blo 2091435 4708403 := bstep (se 1 (by rfl) ⟨3531302, by rfl⟩ : syracuseStep 4708403 = 7062605) B7062605
theorem B3138935 : Blo 2091435 3138935 := bstep (se 1 (by rfl) ⟨2354201, by rfl⟩ : syracuseStep 3138935 = 4708403) B4708403
theorem B2092623 : Blo 2091435 2092623 := bstep (se 1 (by rfl) ⟨1569467, by rfl⟩ : syracuseStep 2092623 = 3138935) B3138935
theorem B3138941 : Blo 2091435 3138941 := bbase (se 3 (by rfl) ⟨588551, by rfl⟩ : syracuseStep 3138941 = 1177103) (by norm_num)
theorem B2092627 : Blo 2091435 2092627 := bstep (se 1 (by rfl) ⟨1569470, by rfl⟩ : syracuseStep 2092627 = 3138941) B3138941
theorem B4708421 : Blo 2091435 4708421 := bbase (se 4 (by rfl) ⟨441414, by rfl⟩ : syracuseStep 4708421 = 882829) (by norm_num)
theorem B3138947 : Blo 2091435 3138947 := bstep (se 1 (by rfl) ⟨2354210, by rfl⟩ : syracuseStep 3138947 = 4708421) B4708421
theorem B2092631 : Blo 2091435 2092631 := bstep (se 1 (by rfl) ⟨1569473, by rfl⟩ : syracuseStep 2092631 = 3138947) B3138947
theorem B5959109 : Blo 2091435 5959109 := bbase (se 4 (by rfl) ⟨558666, by rfl⟩ : syracuseStep 5959109 = 1117333) (by norm_num)
theorem B3972739 : Blo 2091435 3972739 := bstep (se 1 (by rfl) ⟨2979554, by rfl⟩ : syracuseStep 3972739 = 5959109) B5959109
theorem B5296985 : Blo 2091435 5296985 := bstep (se 2 (by rfl) ⟨1986369, by rfl⟩ : syracuseStep 5296985 = 3972739) B3972739
theorem B3531323 : Blo 2091435 3531323 := bstep (se 1 (by rfl) ⟨2648492, by rfl⟩ : syracuseStep 3531323 = 5296985) B5296985
theorem B2354215 : Blo 2091435 2354215 := bstep (se 1 (by rfl) ⟨1765661, by rfl⟩ : syracuseStep 2354215 = 3531323) B3531323
theorem B3138953 : Blo 2091435 3138953 := bstep (se 2 (by rfl) ⟨1177107, by rfl⟩ : syracuseStep 3138953 = 2354215) B2354215
theorem B2092635 : Blo 2091435 2092635 := bstep (se 1 (by rfl) ⟨1569476, by rfl⟩ : syracuseStep 2092635 = 3138953) B3138953
theorem B10593989 : Blo 2091435 10593989 := bbase (se 4 (by rfl) ⟨993186, by rfl⟩ : syracuseStep 10593989 = 1986373) (by norm_num)
theorem B7062659 : Blo 2091435 7062659 := bstep (se 1 (by rfl) ⟨5296994, by rfl⟩ : syracuseStep 7062659 = 10593989) B10593989
theorem B4708439 : Blo 2091435 4708439 := bstep (se 1 (by rfl) ⟨3531329, by rfl⟩ : syracuseStep 4708439 = 7062659) B7062659
theorem B3138959 : Blo 2091435 3138959 := bstep (se 1 (by rfl) ⟨2354219, by rfl⟩ : syracuseStep 3138959 = 4708439) B4708439
theorem B2092639 : Blo 2091435 2092639 := bstep (se 1 (by rfl) ⟨1569479, by rfl⟩ : syracuseStep 2092639 = 3138959) B3138959
theorem B3138965 : Blo 2091435 3138965 := bbase (se 6 (by rfl) ⟨73569, by rfl⟩ : syracuseStep 3138965 = 147139) (by norm_num)
theorem B2092643 : Blo 2091435 2092643 := bstep (se 1 (by rfl) ⟨1569482, by rfl⟩ : syracuseStep 2092643 = 3138965) B3138965
theorem B4469357 : Blo 2091435 4469357 := bbase (se 3 (by rfl) ⟨838004, by rfl⟩ : syracuseStep 4469357 = 1676009) (by norm_num)
theorem B11918285 : Blo 2091435 11918285 := bstep (se 3 (by rfl) ⟨2234678, by rfl⟩ : syracuseStep 11918285 = 4469357) B4469357
theorem B7945523 : Blo 2091435 7945523 := bstep (se 1 (by rfl) ⟨5959142, by rfl⟩ : syracuseStep 7945523 = 11918285) B11918285
theorem B5297015 : Blo 2091435 5297015 := bstep (se 1 (by rfl) ⟨3972761, by rfl⟩ : syracuseStep 5297015 = 7945523) B7945523
theorem B3531343 : Blo 2091435 3531343 := bstep (se 1 (by rfl) ⟨2648507, by rfl⟩ : syracuseStep 3531343 = 5297015) B5297015
theorem B4708457 : Blo 2091435 4708457 := bstep (se 2 (by rfl) ⟨1765671, by rfl⟩ : syracuseStep 4708457 = 3531343) B3531343
theorem B3138971 : Blo 2091435 3138971 := bstep (se 1 (by rfl) ⟨2354228, by rfl⟩ : syracuseStep 3138971 = 4708457) B4708457
theorem B2092647 : Blo 2091435 2092647 := bstep (se 1 (by rfl) ⟨1569485, by rfl⟩ : syracuseStep 2092647 = 3138971) B3138971
theorem B2354233 : Blo 2091435 2354233 := bbase (se 2 (by rfl) ⟨882837, by rfl⟩ : syracuseStep 2354233 = 1765675) (by norm_num)
theorem B3138977 : Blo 2091435 3138977 := bstep (se 2 (by rfl) ⟨1177116, by rfl⟩ : syracuseStep 3138977 = 2354233) B2354233
theorem B2092651 : Blo 2091435 2092651 := bstep (se 1 (by rfl) ⟨1569488, by rfl⟩ : syracuseStep 2092651 = 3138977) B3138977
theorem B13591061 : Blo 2091435 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B9060707 : Blo 2091435 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B24161885 : Blo 2091435 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B16107923 : Blo 2091435 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B10738615 : Blo 2091435 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B14318153 : Blo 2091435 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B9545435 : Blo 2091435 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B6363623 : Blo 2091435 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B16969661 : Blo 2091435 16969661 := bstep (se 3 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 16969661 = 6363623) B6363623
theorem B11313107 : Blo 2091435 11313107 := bstep (se 1 (by rfl) ⟨8484830, by rfl⟩ : syracuseStep 11313107 = 16969661) B16969661
theorem B7542071 : Blo 2091435 7542071 := bstep (se 1 (by rfl) ⟨5656553, by rfl⟩ : syracuseStep 7542071 = 11313107) B11313107
theorem B5028047 : Blo 2091435 5028047 := bstep (se 1 (by rfl) ⟨3771035, by rfl⟩ : syracuseStep 5028047 = 7542071) B7542071
theorem B3352031 : Blo 2091435 3352031 := bstep (se 1 (by rfl) ⟨2514023, by rfl⟩ : syracuseStep 3352031 = 5028047) B5028047
theorem B2234687 : Blo 2091435 2234687 := bstep (se 1 (by rfl) ⟨1676015, by rfl⟩ : syracuseStep 2234687 = 3352031) B3352031
theorem B5959165 : Blo 2091435 5959165 := bstep (se 3 (by rfl) ⟨1117343, by rfl⟩ : syracuseStep 5959165 = 2234687) B2234687
theorem B7945553 : Blo 2091435 7945553 := bstep (se 2 (by rfl) ⟨2979582, by rfl⟩ : syracuseStep 7945553 = 5959165) B5959165
theorem B5297035 : Blo 2091435 5297035 := bstep (se 1 (by rfl) ⟨3972776, by rfl⟩ : syracuseStep 5297035 = 7945553) B7945553
theorem B7062713 : Blo 2091435 7062713 := bstep (se 2 (by rfl) ⟨2648517, by rfl⟩ : syracuseStep 7062713 = 5297035) B5297035
theorem B4708475 : Blo 2091435 4708475 := bstep (se 1 (by rfl) ⟨3531356, by rfl⟩ : syracuseStep 4708475 = 7062713) B7062713
theorem B3138983 : Blo 2091435 3138983 := bstep (se 1 (by rfl) ⟨2354237, by rfl⟩ : syracuseStep 3138983 = 4708475) B4708475
theorem B2092655 : Blo 2091435 2092655 := bstep (se 1 (by rfl) ⟨1569491, by rfl⟩ : syracuseStep 2092655 = 3138983) B3138983
theorem B3138989 : Blo 2091435 3138989 := bbase (se 3 (by rfl) ⟨588560, by rfl⟩ : syracuseStep 3138989 = 1177121) (by norm_num)
theorem B2092659 : Blo 2091435 2092659 := bstep (se 1 (by rfl) ⟨1569494, by rfl⟩ : syracuseStep 2092659 = 3138989) B3138989
theorem B4708493 : Blo 2091435 4708493 := bbase (se 3 (by rfl) ⟨882842, by rfl⟩ : syracuseStep 4708493 = 1765685) (by norm_num)
theorem B3138995 : Blo 2091435 3138995 := bstep (se 1 (by rfl) ⟨2354246, by rfl⟩ : syracuseStep 3138995 = 4708493) B4708493
theorem B2092663 : Blo 2091435 2092663 := bstep (se 1 (by rfl) ⟨1569497, by rfl⟩ : syracuseStep 2092663 = 3138995) B3138995
theorem B2648533 : Blo 2091435 2648533 := bbase (se 7 (by rfl) ⟨31037, by rfl⟩ : syracuseStep 2648533 = 62075) (by norm_num)
theorem B3531377 : Blo 2091435 3531377 := bstep (se 2 (by rfl) ⟨1324266, by rfl⟩ : syracuseStep 3531377 = 2648533) B2648533
theorem B2354251 : Blo 2091435 2354251 := bstep (se 1 (by rfl) ⟨1765688, by rfl⟩ : syracuseStep 2354251 = 3531377) B3531377
theorem B3139001 : Blo 2091435 3139001 := bstep (se 2 (by rfl) ⟨1177125, by rfl⟩ : syracuseStep 3139001 = 2354251) B2354251
theorem B2092667 : Blo 2091435 2092667 := bstep (se 1 (by rfl) ⟨1569500, by rfl⟩ : syracuseStep 2092667 = 3139001) B3139001
theorem B10885205 : Blo 2091435 10885205 := bbase (se 8 (by rfl) ⟨63780, by rfl⟩ : syracuseStep 10885205 = 127561) (by norm_num)
theorem B7256803 : Blo 2091435 7256803 := bstep (se 1 (by rfl) ⟨5442602, by rfl⟩ : syracuseStep 7256803 = 10885205) B10885205
theorem B9675737 : Blo 2091435 9675737 := bstep (se 2 (by rfl) ⟨3628401, by rfl⟩ : syracuseStep 9675737 = 7256803) B7256803
theorem B6450491 : Blo 2091435 6450491 := bstep (se 1 (by rfl) ⟨4837868, by rfl⟩ : syracuseStep 6450491 = 9675737) B9675737
theorem B4300327 : Blo 2091435 4300327 := bstep (se 1 (by rfl) ⟨3225245, by rfl⟩ : syracuseStep 4300327 = 6450491) B6450491
theorem B22935077 : Blo 2091435 22935077 := bstep (se 4 (by rfl) ⟨2150163, by rfl⟩ : syracuseStep 22935077 = 4300327) B4300327
theorem B15290051 : Blo 2091435 15290051 := bstep (se 1 (by rfl) ⟨11467538, by rfl⟩ : syracuseStep 15290051 = 22935077) B22935077
theorem B40773469 : Blo 2091435 40773469 := bstep (se 3 (by rfl) ⟨7645025, by rfl⟩ : syracuseStep 40773469 = 15290051) B15290051
theorem B54364625 : Blo 2091435 54364625 := bstep (se 2 (by rfl) ⟨20386734, by rfl⟩ : syracuseStep 54364625 = 40773469) B40773469
theorem B36243083 : Blo 2091435 36243083 := bstep (se 1 (by rfl) ⟨27182312, by rfl⟩ : syracuseStep 36243083 = 54364625) B54364625
theorem B96648221 : Blo 2091435 96648221 := bstep (se 3 (by rfl) ⟨18121541, by rfl⟩ : syracuseStep 96648221 = 36243083) B36243083
theorem B64432147 : Blo 2091435 64432147 := bstep (se 1 (by rfl) ⟨48324110, by rfl⟩ : syracuseStep 64432147 = 96648221) B96648221
theorem B85909529 : Blo 2091435 85909529 := bstep (se 2 (by rfl) ⟨32216073, by rfl⟩ : syracuseStep 85909529 = 64432147) B64432147
theorem B229092077 : Blo 2091435 229092077 := bstep (se 3 (by rfl) ⟨42954764, by rfl⟩ : syracuseStep 229092077 = 85909529) B85909529
theorem B152728051 : Blo 2091435 152728051 := bstep (se 1 (by rfl) ⟨114546038, by rfl⟩ : syracuseStep 152728051 = 229092077) B229092077
theorem B203637401 : Blo 2091435 203637401 := bstep (se 2 (by rfl) ⟨76364025, by rfl⟩ : syracuseStep 203637401 = 152728051) B152728051
theorem B135758267 : Blo 2091435 135758267 := bstep (se 1 (by rfl) ⟨101818700, by rfl⟩ : syracuseStep 135758267 = 203637401) B203637401
theorem B90505511 : Blo 2091435 90505511 := bstep (se 1 (by rfl) ⟨67879133, by rfl⟩ : syracuseStep 90505511 = 135758267) B135758267
theorem B60337007 : Blo 2091435 60337007 := bstep (se 1 (by rfl) ⟨45252755, by rfl⟩ : syracuseStep 60337007 = 90505511) B90505511
theorem B40224671 : Blo 2091435 40224671 := bstep (se 1 (by rfl) ⟨30168503, by rfl⟩ : syracuseStep 40224671 = 60337007) B60337007
theorem B26816447 : Blo 2091435 26816447 := bstep (se 1 (by rfl) ⟨20112335, by rfl⟩ : syracuseStep 26816447 = 40224671) B40224671
theorem B17877631 : Blo 2091435 17877631 := bstep (se 1 (by rfl) ⟨13408223, by rfl⟩ : syracuseStep 17877631 = 26816447) B26816447
theorem B23836841 : Blo 2091435 23836841 := bstep (se 2 (by rfl) ⟨8938815, by rfl⟩ : syracuseStep 23836841 = 17877631) B17877631
theorem B15891227 : Blo 2091435 15891227 := bstep (se 1 (by rfl) ⟨11918420, by rfl⟩ : syracuseStep 15891227 = 23836841) B23836841
theorem B10594151 : Blo 2091435 10594151 := bstep (se 1 (by rfl) ⟨7945613, by rfl⟩ : syracuseStep 10594151 = 15891227) B15891227
theorem B7062767 : Blo 2091435 7062767 := bstep (se 1 (by rfl) ⟨5297075, by rfl⟩ : syracuseStep 7062767 = 10594151) B10594151
theorem B4708511 : Blo 2091435 4708511 := bstep (se 1 (by rfl) ⟨3531383, by rfl⟩ : syracuseStep 4708511 = 7062767) B7062767
theorem B3139007 : Blo 2091435 3139007 := bstep (se 1 (by rfl) ⟨2354255, by rfl⟩ : syracuseStep 3139007 = 4708511) B4708511
theorem B2092671 : Blo 2091435 2092671 := bstep (se 1 (by rfl) ⟨1569503, by rfl⟩ : syracuseStep 2092671 = 3139007) B3139007
theorem B3139013 : Blo 2091435 3139013 := bbase (se 4 (by rfl) ⟨294282, by rfl⟩ : syracuseStep 3139013 = 588565) (by norm_num)
theorem B2092675 : Blo 2091435 2092675 := bstep (se 1 (by rfl) ⟨1569506, by rfl⟩ : syracuseStep 2092675 = 3139013) B3139013
theorem B3531397 : Blo 2091435 3531397 := bbase (se 4 (by rfl) ⟨331068, by rfl⟩ : syracuseStep 3531397 = 662137) (by norm_num)
theorem B4708529 : Blo 2091435 4708529 := bstep (se 2 (by rfl) ⟨1765698, by rfl⟩ : syracuseStep 4708529 = 3531397) B3531397
theorem B3139019 : Blo 2091435 3139019 := bstep (se 1 (by rfl) ⟨2354264, by rfl⟩ : syracuseStep 3139019 = 4708529) B4708529
theorem B2092679 : Blo 2091435 2092679 := bstep (se 1 (by rfl) ⟨1569509, by rfl⟩ : syracuseStep 2092679 = 3139019) B3139019
theorem B2354269 : Blo 2091435 2354269 := bbase (se 3 (by rfl) ⟨441425, by rfl⟩ : syracuseStep 2354269 = 882851) (by norm_num)
theorem B3139025 : Blo 2091435 3139025 := bstep (se 2 (by rfl) ⟨1177134, by rfl⟩ : syracuseStep 3139025 = 2354269) B2354269
theorem B2092683 : Blo 2091435 2092683 := bstep (se 1 (by rfl) ⟨1569512, by rfl⟩ : syracuseStep 2092683 = 3139025) B3139025
theorem B7062821 : Blo 2091435 7062821 := bbase (se 4 (by rfl) ⟨662139, by rfl⟩ : syracuseStep 7062821 = 1324279) (by norm_num)
theorem B4708547 : Blo 2091435 4708547 := bstep (se 1 (by rfl) ⟨3531410, by rfl⟩ : syracuseStep 4708547 = 7062821) B7062821
theorem B3139031 : Blo 2091435 3139031 := bstep (se 1 (by rfl) ⟨2354273, by rfl⟩ : syracuseStep 3139031 = 4708547) B4708547
theorem B2092687 : Blo 2091435 2092687 := bstep (se 1 (by rfl) ⟨1569515, by rfl⟩ : syracuseStep 2092687 = 3139031) B3139031
theorem B3139037 : Blo 2091435 3139037 := bbase (se 3 (by rfl) ⟨588569, by rfl⟩ : syracuseStep 3139037 = 1177139) (by norm_num)
theorem B2092691 : Blo 2091435 2092691 := bstep (se 1 (by rfl) ⟨1569518, by rfl⟩ : syracuseStep 2092691 = 3139037) B3139037
theorem B4708565 : Blo 2091435 4708565 := bbase (se 7 (by rfl) ⟨55178, by rfl⟩ : syracuseStep 4708565 = 110357) (by norm_num)
theorem B3139043 : Blo 2091435 3139043 := bstep (se 1 (by rfl) ⟨2354282, by rfl⟩ : syracuseStep 3139043 = 4708565) B4708565
theorem B2092695 : Blo 2091435 2092695 := bstep (se 1 (by rfl) ⟨1569521, by rfl⟩ : syracuseStep 2092695 = 3139043) B3139043
theorem B7542229 : Blo 2091435 7542229 := bbase (se 7 (by rfl) ⟨88385, by rfl⟩ : syracuseStep 7542229 = 176771) (by norm_num)
theorem B10056305 : Blo 2091435 10056305 := bstep (se 2 (by rfl) ⟨3771114, by rfl⟩ : syracuseStep 10056305 = 7542229) B7542229
theorem B6704203 : Blo 2091435 6704203 := bstep (se 1 (by rfl) ⟨5028152, by rfl⟩ : syracuseStep 6704203 = 10056305) B10056305
theorem B8938937 : Blo 2091435 8938937 := bstep (se 2 (by rfl) ⟨3352101, by rfl⟩ : syracuseStep 8938937 = 6704203) B6704203
theorem B5959291 : Blo 2091435 5959291 := bstep (se 1 (by rfl) ⟨4469468, by rfl⟩ : syracuseStep 5959291 = 8938937) B8938937
theorem B7945721 : Blo 2091435 7945721 := bstep (se 2 (by rfl) ⟨2979645, by rfl⟩ : syracuseStep 7945721 = 5959291) B5959291
theorem B5297147 : Blo 2091435 5297147 := bstep (se 1 (by rfl) ⟨3972860, by rfl⟩ : syracuseStep 5297147 = 7945721) B7945721
theorem B3531431 : Blo 2091435 3531431 := bstep (se 1 (by rfl) ⟨2648573, by rfl⟩ : syracuseStep 3531431 = 5297147) B5297147
theorem B2354287 : Blo 2091435 2354287 := bstep (se 1 (by rfl) ⟨1765715, by rfl⟩ : syracuseStep 2354287 = 3531431) B3531431
theorem B3139049 : Blo 2091435 3139049 := bstep (se 2 (by rfl) ⟨1177143, by rfl⟩ : syracuseStep 3139049 = 2354287) B2354287
theorem B2092699 : Blo 2091435 2092699 := bstep (se 1 (by rfl) ⟨1569524, by rfl⟩ : syracuseStep 2092699 = 3139049) B3139049
theorem B2828341 : Blo 2091435 2828341 := bbase (se 5 (by rfl) ⟨132578, by rfl⟩ : syracuseStep 2828341 = 265157) (by norm_num)
theorem B3771121 : Blo 2091435 3771121 := bstep (se 2 (by rfl) ⟨1414170, by rfl⟩ : syracuseStep 3771121 = 2828341) B2828341
theorem B5028161 : Blo 2091435 5028161 := bstep (se 2 (by rfl) ⟨1885560, by rfl⟩ : syracuseStep 5028161 = 3771121) B3771121
theorem B13408429 : Blo 2091435 13408429 := bstep (se 3 (by rfl) ⟨2514080, by rfl⟩ : syracuseStep 13408429 = 5028161) B5028161
theorem B17877905 : Blo 2091435 17877905 := bstep (se 2 (by rfl) ⟨6704214, by rfl⟩ : syracuseStep 17877905 = 13408429) B13408429
theorem B11918603 : Blo 2091435 11918603 := bstep (se 1 (by rfl) ⟨8938952, by rfl⟩ : syracuseStep 11918603 = 17877905) B17877905
theorem B7945735 : Blo 2091435 7945735 := bstep (se 1 (by rfl) ⟨5959301, by rfl⟩ : syracuseStep 7945735 = 11918603) B11918603
theorem B10594313 : Blo 2091435 10594313 := bstep (se 2 (by rfl) ⟨3972867, by rfl⟩ : syracuseStep 10594313 = 7945735) B7945735
theorem B7062875 : Blo 2091435 7062875 := bstep (se 1 (by rfl) ⟨5297156, by rfl⟩ : syracuseStep 7062875 = 10594313) B10594313
theorem B4708583 : Blo 2091435 4708583 := bstep (se 1 (by rfl) ⟨3531437, by rfl⟩ : syracuseStep 4708583 = 7062875) B7062875
theorem B3139055 : Blo 2091435 3139055 := bstep (se 1 (by rfl) ⟨2354291, by rfl⟩ : syracuseStep 3139055 = 4708583) B4708583
theorem B2092703 : Blo 2091435 2092703 := bstep (se 1 (by rfl) ⟨1569527, by rfl⟩ : syracuseStep 2092703 = 3139055) B3139055
theorem B3139061 : Blo 2091435 3139061 := bbase (se 5 (by rfl) ⟨147143, by rfl⟩ : syracuseStep 3139061 = 294287) (by norm_num)
theorem B2092707 : Blo 2091435 2092707 := bstep (se 1 (by rfl) ⟨1569530, by rfl⟩ : syracuseStep 2092707 = 3139061) B3139061
theorem B2121265 : Blo 2091435 2121265 := bbase (se 2 (by rfl) ⟨795474, by rfl⟩ : syracuseStep 2121265 = 1590949) (by norm_num)
theorem B2828353 : Blo 2091435 2828353 := bstep (se 2 (by rfl) ⟨1060632, by rfl⟩ : syracuseStep 2828353 = 2121265) B2121265
theorem B3771137 : Blo 2091435 3771137 := bstep (se 2 (by rfl) ⟨1414176, by rfl⟩ : syracuseStep 3771137 = 2828353) B2828353
theorem B2514091 : Blo 2091435 2514091 := bstep (se 1 (by rfl) ⟨1885568, by rfl⟩ : syracuseStep 2514091 = 3771137) B3771137
theorem B3352121 : Blo 2091435 3352121 := bstep (se 2 (by rfl) ⟨1257045, by rfl⟩ : syracuseStep 3352121 = 2514091) B2514091
theorem B2234747 : Blo 2091435 2234747 := bstep (se 1 (by rfl) ⟨1676060, by rfl⟩ : syracuseStep 2234747 = 3352121) B3352121
theorem B5959325 : Blo 2091435 5959325 := bstep (se 3 (by rfl) ⟨1117373, by rfl⟩ : syracuseStep 5959325 = 2234747) B2234747
theorem B3972883 : Blo 2091435 3972883 := bstep (se 1 (by rfl) ⟨2979662, by rfl⟩ : syracuseStep 3972883 = 5959325) B5959325
theorem B5297177 : Blo 2091435 5297177 := bstep (se 2 (by rfl) ⟨1986441, by rfl⟩ : syracuseStep 5297177 = 3972883) B3972883
theorem B3531451 : Blo 2091435 3531451 := bstep (se 1 (by rfl) ⟨2648588, by rfl⟩ : syracuseStep 3531451 = 5297177) B5297177
theorem B4708601 : Blo 2091435 4708601 := bstep (se 2 (by rfl) ⟨1765725, by rfl⟩ : syracuseStep 4708601 = 3531451) B3531451
theorem B3139067 : Blo 2091435 3139067 := bstep (se 1 (by rfl) ⟨2354300, by rfl⟩ : syracuseStep 3139067 = 4708601) B4708601
theorem B2092711 : Blo 2091435 2092711 := bstep (se 1 (by rfl) ⟨1569533, by rfl⟩ : syracuseStep 2092711 = 3139067) B3139067
theorem B2354305 : Blo 2091435 2354305 := bbase (se 2 (by rfl) ⟨882864, by rfl⟩ : syracuseStep 2354305 = 1765729) (by norm_num)
theorem B3139073 : Blo 2091435 3139073 := bstep (se 2 (by rfl) ⟨1177152, by rfl⟩ : syracuseStep 3139073 = 2354305) B2354305
theorem B2092715 : Blo 2091435 2092715 := bstep (se 1 (by rfl) ⟨1569536, by rfl⟩ : syracuseStep 2092715 = 3139073) B3139073
theorem B5297197 : Blo 2091435 5297197 := bbase (se 3 (by rfl) ⟨993224, by rfl⟩ : syracuseStep 5297197 = 1986449) (by norm_num)
theorem B7062929 : Blo 2091435 7062929 := bstep (se 2 (by rfl) ⟨2648598, by rfl⟩ : syracuseStep 7062929 = 5297197) B5297197
theorem B4708619 : Blo 2091435 4708619 := bstep (se 1 (by rfl) ⟨3531464, by rfl⟩ : syracuseStep 4708619 = 7062929) B7062929
theorem B3139079 : Blo 2091435 3139079 := bstep (se 1 (by rfl) ⟨2354309, by rfl⟩ : syracuseStep 3139079 = 4708619) B4708619
theorem B2092719 : Blo 2091435 2092719 := bstep (se 1 (by rfl) ⟨1569539, by rfl⟩ : syracuseStep 2092719 = 3139079) B3139079
theorem B3139085 : Blo 2091435 3139085 := bbase (se 3 (by rfl) ⟨588578, by rfl⟩ : syracuseStep 3139085 = 1177157) (by norm_num)
theorem B2092723 : Blo 2091435 2092723 := bstep (se 1 (by rfl) ⟨1569542, by rfl⟩ : syracuseStep 2092723 = 3139085) B3139085
theorem B4708637 : Blo 2091435 4708637 := bbase (se 3 (by rfl) ⟨882869, by rfl⟩ : syracuseStep 4708637 = 1765739) (by norm_num)
theorem B3139091 : Blo 2091435 3139091 := bstep (se 1 (by rfl) ⟨2354318, by rfl⟩ : syracuseStep 3139091 = 4708637) B4708637
theorem B2092727 : Blo 2091435 2092727 := bstep (se 1 (by rfl) ⟨1569545, by rfl⟩ : syracuseStep 2092727 = 3139091) B3139091
theorem B3531485 : Blo 2091435 3531485 := bbase (se 3 (by rfl) ⟨662153, by rfl⟩ : syracuseStep 3531485 = 1324307) (by norm_num)
theorem B2354323 : Blo 2091435 2354323 := bstep (se 1 (by rfl) ⟨1765742, by rfl⟩ : syracuseStep 2354323 = 3531485) B3531485
theorem B3139097 : Blo 2091435 3139097 := bstep (se 2 (by rfl) ⟨1177161, by rfl⟩ : syracuseStep 3139097 = 2354323) B2354323
theorem B2092731 : Blo 2091435 2092731 := bstep (se 1 (by rfl) ⟨1569548, by rfl⟩ : syracuseStep 2092731 = 3139097) B3139097
theorem B3181933 : Blo 2091435 3181933 := bbase (se 3 (by rfl) ⟨596612, by rfl⟩ : syracuseStep 3181933 = 1193225) (by norm_num)
theorem B4242577 : Blo 2091435 4242577 := bstep (se 2 (by rfl) ⟨1590966, by rfl⟩ : syracuseStep 4242577 = 3181933) B3181933
theorem B5656769 : Blo 2091435 5656769 := bstep (se 2 (by rfl) ⟨2121288, by rfl⟩ : syracuseStep 5656769 = 4242577) B4242577
theorem B3771179 : Blo 2091435 3771179 := bstep (se 1 (by rfl) ⟨2828384, by rfl⟩ : syracuseStep 3771179 = 5656769) B5656769
theorem B2514119 : Blo 2091435 2514119 := bstep (se 1 (by rfl) ⟨1885589, by rfl⟩ : syracuseStep 2514119 = 3771179) B3771179
theorem B6704317 : Blo 2091435 6704317 := bstep (se 3 (by rfl) ⟨1257059, by rfl⟩ : syracuseStep 6704317 = 2514119) B2514119
theorem B8939089 : Blo 2091435 8939089 := bstep (se 2 (by rfl) ⟨3352158, by rfl⟩ : syracuseStep 8939089 = 6704317) B6704317
theorem B11918785 : Blo 2091435 11918785 := bstep (se 2 (by rfl) ⟨4469544, by rfl⟩ : syracuseStep 11918785 = 8939089) B8939089
theorem B15891713 : Blo 2091435 15891713 := bstep (se 2 (by rfl) ⟨5959392, by rfl⟩ : syracuseStep 15891713 = 11918785) B11918785
theorem B10594475 : Blo 2091435 10594475 := bstep (se 1 (by rfl) ⟨7945856, by rfl⟩ : syracuseStep 10594475 = 15891713) B15891713
theorem B7062983 : Blo 2091435 7062983 := bstep (se 1 (by rfl) ⟨5297237, by rfl⟩ : syracuseStep 7062983 = 10594475) B10594475
theorem B4708655 : Blo 2091435 4708655 := bstep (se 1 (by rfl) ⟨3531491, by rfl⟩ : syracuseStep 4708655 = 7062983) B7062983
theorem B3139103 : Blo 2091435 3139103 := bstep (se 1 (by rfl) ⟨2354327, by rfl⟩ : syracuseStep 3139103 = 4708655) B4708655
theorem B2092735 : Blo 2091435 2092735 := bstep (se 1 (by rfl) ⟨1569551, by rfl⟩ : syracuseStep 2092735 = 3139103) B3139103
theorem B3139109 : Blo 2091435 3139109 := bbase (se 4 (by rfl) ⟨294291, by rfl⟩ : syracuseStep 3139109 = 588583) (by norm_num)
theorem B2092739 : Blo 2091435 2092739 := bstep (se 1 (by rfl) ⟨1569554, by rfl⟩ : syracuseStep 2092739 = 3139109) B3139109
theorem B2648629 : Blo 2091435 2648629 := bbase (se 5 (by rfl) ⟨124154, by rfl⟩ : syracuseStep 2648629 = 248309) (by norm_num)
theorem B3531505 : Blo 2091435 3531505 := bstep (se 2 (by rfl) ⟨1324314, by rfl⟩ : syracuseStep 3531505 = 2648629) B2648629
theorem B4708673 : Blo 2091435 4708673 := bstep (se 2 (by rfl) ⟨1765752, by rfl⟩ : syracuseStep 4708673 = 3531505) B3531505
theorem B3139115 : Blo 2091435 3139115 := bstep (se 1 (by rfl) ⟨2354336, by rfl⟩ : syracuseStep 3139115 = 4708673) B4708673
theorem B2092743 : Blo 2091435 2092743 := bstep (se 1 (by rfl) ⟨1569557, by rfl⟩ : syracuseStep 2092743 = 3139115) B3139115
theorem B2354341 : Blo 2091435 2354341 := bbase (se 4 (by rfl) ⟨220719, by rfl⟩ : syracuseStep 2354341 = 441439) (by norm_num)
theorem B3139121 : Blo 2091435 3139121 := bstep (se 2 (by rfl) ⟨1177170, by rfl⟩ : syracuseStep 3139121 = 2354341) B2354341
theorem B2092747 : Blo 2091435 2092747 := bstep (se 1 (by rfl) ⟨1569560, by rfl⟩ : syracuseStep 2092747 = 3139121) B3139121
theorem B20113109 : Blo 2091435 20113109 := bbase (se 7 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 20113109 = 471401) (by norm_num)
theorem B13408739 : Blo 2091435 13408739 := bstep (se 1 (by rfl) ⟨10056554, by rfl⟩ : syracuseStep 13408739 = 20113109) B20113109
theorem B8939159 : Blo 2091435 8939159 := bstep (se 1 (by rfl) ⟨6704369, by rfl⟩ : syracuseStep 8939159 = 13408739) B13408739
theorem B5959439 : Blo 2091435 5959439 := bstep (se 1 (by rfl) ⟨4469579, by rfl⟩ : syracuseStep 5959439 = 8939159) B8939159
theorem B3972959 : Blo 2091435 3972959 := bstep (se 1 (by rfl) ⟨2979719, by rfl⟩ : syracuseStep 3972959 = 5959439) B5959439
theorem B2648639 : Blo 2091435 2648639 := bstep (se 1 (by rfl) ⟨1986479, by rfl⟩ : syracuseStep 2648639 = 3972959) B3972959
theorem B7063037 : Blo 2091435 7063037 := bstep (se 3 (by rfl) ⟨1324319, by rfl⟩ : syracuseStep 7063037 = 2648639) B2648639
theorem B4708691 : Blo 2091435 4708691 := bstep (se 1 (by rfl) ⟨3531518, by rfl⟩ : syracuseStep 4708691 = 7063037) B7063037
theorem B3139127 : Blo 2091435 3139127 := bstep (se 1 (by rfl) ⟨2354345, by rfl⟩ : syracuseStep 3139127 = 4708691) B4708691
theorem B2092751 : Blo 2091435 2092751 := bstep (se 1 (by rfl) ⟨1569563, by rfl⟩ : syracuseStep 2092751 = 3139127) B3139127
theorem B3139133 : Blo 2091435 3139133 := bbase (se 3 (by rfl) ⟨588587, by rfl⟩ : syracuseStep 3139133 = 1177175) (by norm_num)
theorem B2092755 : Blo 2091435 2092755 := bstep (se 1 (by rfl) ⟨1569566, by rfl⟩ : syracuseStep 2092755 = 3139133) B3139133
theorem B4708709 : Blo 2091435 4708709 := bbase (se 4 (by rfl) ⟨441441, by rfl⟩ : syracuseStep 4708709 = 882883) (by norm_num)
theorem B3139139 : Blo 2091435 3139139 := bstep (se 1 (by rfl) ⟨2354354, by rfl⟩ : syracuseStep 3139139 = 4708709) B4708709
theorem B2092759 : Blo 2091435 2092759 := bstep (se 1 (by rfl) ⟨1569569, by rfl⟩ : syracuseStep 2092759 = 3139139) B3139139
theorem B5297309 : Blo 2091435 5297309 := bbase (se 3 (by rfl) ⟨993245, by rfl⟩ : syracuseStep 5297309 = 1986491) (by norm_num)
theorem B3531539 : Blo 2091435 3531539 := bstep (se 1 (by rfl) ⟨2648654, by rfl⟩ : syracuseStep 3531539 = 5297309) B5297309
theorem B2354359 : Blo 2091435 2354359 := bstep (se 1 (by rfl) ⟨1765769, by rfl⟩ : syracuseStep 2354359 = 3531539) B3531539
theorem B3139145 : Blo 2091435 3139145 := bstep (se 2 (by rfl) ⟨1177179, by rfl⟩ : syracuseStep 3139145 = 2354359) B2354359
theorem B2092763 : Blo 2091435 2092763 := bstep (se 1 (by rfl) ⟨1569572, by rfl⟩ : syracuseStep 2092763 = 3139145) B3139145
theorem B3972989 : Blo 2091435 3972989 := bbase (se 3 (by rfl) ⟨744935, by rfl⟩ : syracuseStep 3972989 = 1489871) (by norm_num)
theorem B10594637 : Blo 2091435 10594637 := bstep (se 3 (by rfl) ⟨1986494, by rfl⟩ : syracuseStep 10594637 = 3972989) B3972989
theorem B7063091 : Blo 2091435 7063091 := bstep (se 1 (by rfl) ⟨5297318, by rfl⟩ : syracuseStep 7063091 = 10594637) B10594637
theorem B4708727 : Blo 2091435 4708727 := bstep (se 1 (by rfl) ⟨3531545, by rfl⟩ : syracuseStep 4708727 = 7063091) B7063091
theorem B3139151 : Blo 2091435 3139151 := bstep (se 1 (by rfl) ⟨2354363, by rfl⟩ : syracuseStep 3139151 = 4708727) B4708727
theorem B2092767 : Blo 2091435 2092767 := bstep (se 1 (by rfl) ⟨1569575, by rfl⟩ : syracuseStep 2092767 = 3139151) B3139151
theorem B3139157 : Blo 2091435 3139157 := bbase (se 8 (by rfl) ⟨18393, by rfl⟩ : syracuseStep 3139157 = 36787) (by norm_num)
theorem B2092771 : Blo 2091435 2092771 := bstep (se 1 (by rfl) ⟨1569578, by rfl⟩ : syracuseStep 2092771 = 3139157) B3139157
theorem B8736661 : Blo 2091435 8736661 := bbase (se 6 (by rfl) ⟨204765, by rfl⟩ : syracuseStep 8736661 = 409531) (by norm_num)
theorem B11648881 : Blo 2091435 11648881 := bstep (se 2 (by rfl) ⟨4368330, by rfl⟩ : syracuseStep 11648881 = 8736661) B8736661
theorem B15531841 : Blo 2091435 15531841 := bstep (se 2 (by rfl) ⟨5824440, by rfl⟩ : syracuseStep 15531841 = 11648881) B11648881
theorem B20709121 : Blo 2091435 20709121 := bstep (se 2 (by rfl) ⟨7765920, by rfl⟩ : syracuseStep 20709121 = 15531841) B15531841
theorem B27612161 : Blo 2091435 27612161 := bstep (se 2 (by rfl) ⟨10354560, by rfl⟩ : syracuseStep 27612161 = 20709121) B20709121
theorem B18408107 : Blo 2091435 18408107 := bstep (se 1 (by rfl) ⟨13806080, by rfl⟩ : syracuseStep 18408107 = 27612161) B27612161
theorem B12272071 : Blo 2091435 12272071 := bstep (se 1 (by rfl) ⟨9204053, by rfl⟩ : syracuseStep 12272071 = 18408107) B18408107
theorem B16362761 : Blo 2091435 16362761 := bstep (se 2 (by rfl) ⟨6136035, by rfl⟩ : syracuseStep 16362761 = 12272071) B12272071
theorem B174536117 : Blo 2091435 174536117 := bstep (se 5 (by rfl) ⟨8181380, by rfl⟩ : syracuseStep 174536117 = 16362761) B16362761
theorem B116357411 : Blo 2091435 116357411 := bstep (se 1 (by rfl) ⟨87268058, by rfl⟩ : syracuseStep 116357411 = 174536117) B174536117
theorem B77571607 : Blo 2091435 77571607 := bstep (se 1 (by rfl) ⟨58178705, by rfl⟩ : syracuseStep 77571607 = 116357411) B116357411
theorem B103428809 : Blo 2091435 103428809 := bstep (se 2 (by rfl) ⟨38785803, by rfl⟩ : syracuseStep 103428809 = 77571607) B77571607
theorem B68952539 : Blo 2091435 68952539 := bstep (se 1 (by rfl) ⟨51714404, by rfl⟩ : syracuseStep 68952539 = 103428809) B103428809
theorem B45968359 : Blo 2091435 45968359 := bstep (se 1 (by rfl) ⟨34476269, by rfl⟩ : syracuseStep 45968359 = 68952539) B68952539
theorem B61291145 : Blo 2091435 61291145 := bstep (se 2 (by rfl) ⟨22984179, by rfl⟩ : syracuseStep 61291145 = 45968359) B45968359
theorem B40860763 : Blo 2091435 40860763 := bstep (se 1 (by rfl) ⟨30645572, by rfl⟩ : syracuseStep 40860763 = 61291145) B61291145
theorem B217924069 : Blo 2091435 217924069 := bstep (se 4 (by rfl) ⟨20430381, by rfl⟩ : syracuseStep 217924069 = 40860763) B40860763
theorem B290565425 : Blo 2091435 290565425 := bstep (se 2 (by rfl) ⟨108962034, by rfl⟩ : syracuseStep 290565425 = 217924069) B217924069
theorem B774841133 : Blo 2091435 774841133 := bstep (se 3 (by rfl) ⟨145282712, by rfl⟩ : syracuseStep 774841133 = 290565425) B290565425
theorem B516560755 : Blo 2091435 516560755 := bstep (se 1 (by rfl) ⟨387420566, by rfl⟩ : syracuseStep 516560755 = 774841133) B774841133
theorem B688747673 : Blo 2091435 688747673 := bstep (se 2 (by rfl) ⟨258280377, by rfl⟩ : syracuseStep 688747673 = 516560755) B516560755
theorem B459165115 : Blo 2091435 459165115 := bstep (se 1 (by rfl) ⟨344373836, by rfl⟩ : syracuseStep 459165115 = 688747673) B688747673
theorem B612220153 : Blo 2091435 612220153 := bstep (se 2 (by rfl) ⟨229582557, by rfl⟩ : syracuseStep 612220153 = 459165115) B459165115
theorem B816293537 : Blo 2091435 816293537 := bstep (se 2 (by rfl) ⟨306110076, by rfl⟩ : syracuseStep 816293537 = 612220153) B612220153
theorem B544195691 : Blo 2091435 544195691 := bstep (se 1 (by rfl) ⟨408146768, by rfl⟩ : syracuseStep 544195691 = 816293537) B816293537
theorem B362797127 : Blo 2091435 362797127 := bstep (se 1 (by rfl) ⟨272097845, by rfl⟩ : syracuseStep 362797127 = 544195691) B544195691
theorem B241864751 : Blo 2091435 241864751 := bstep (se 1 (by rfl) ⟨181398563, by rfl⟩ : syracuseStep 241864751 = 362797127) B362797127
theorem B161243167 : Blo 2091435 161243167 := bstep (se 1 (by rfl) ⟨120932375, by rfl⟩ : syracuseStep 161243167 = 241864751) B241864751
theorem B3439854229 : Blo 2091435 3439854229 := bstep (se 6 (by rfl) ⟨80621583, by rfl⟩ : syracuseStep 3439854229 = 161243167) B161243167
theorem B4586472305 : Blo 2091435 4586472305 := bstep (se 2 (by rfl) ⟨1719927114, by rfl⟩ : syracuseStep 4586472305 = 3439854229) B3439854229
theorem B3057648203 : Blo 2091435 3057648203 := bstep (se 1 (by rfl) ⟨2293236152, by rfl⟩ : syracuseStep 3057648203 = 4586472305) B4586472305
theorem B8153728541 : Blo 2091435 8153728541 := bstep (se 3 (by rfl) ⟨1528824101, by rfl⟩ : syracuseStep 8153728541 = 3057648203) B3057648203
theorem B5435819027 : Blo 2091435 5435819027 := bstep (se 1 (by rfl) ⟨4076864270, by rfl⟩ : syracuseStep 5435819027 = 8153728541) B8153728541
theorem B3623879351 : Blo 2091435 3623879351 := bstep (se 1 (by rfl) ⟨2717909513, by rfl⟩ : syracuseStep 3623879351 = 5435819027) B5435819027
theorem B2415919567 : Blo 2091435 2415919567 := bstep (se 1 (by rfl) ⟨1811939675, by rfl⟩ : syracuseStep 2415919567 = 3623879351) B3623879351
theorem B3221226089 : Blo 2091435 3221226089 := bstep (se 2 (by rfl) ⟨1207959783, by rfl⟩ : syracuseStep 3221226089 = 2415919567) B2415919567
theorem B2147484059 : Blo 2091435 2147484059 := bstep (se 1 (by rfl) ⟨1610613044, by rfl⟩ : syracuseStep 2147484059 = 3221226089) B3221226089
theorem B1431656039 : Blo 2091435 1431656039 := bstep (se 1 (by rfl) ⟨1073742029, by rfl⟩ : syracuseStep 1431656039 = 2147484059) B2147484059
theorem B954437359 : Blo 2091435 954437359 := bstep (se 1 (by rfl) ⟨715828019, by rfl⟩ : syracuseStep 954437359 = 1431656039) B1431656039
theorem B1272583145 : Blo 2091435 1272583145 := bstep (se 2 (by rfl) ⟨477218679, by rfl⟩ : syracuseStep 1272583145 = 954437359) B954437359
theorem B848388763 : Blo 2091435 848388763 := bstep (se 1 (by rfl) ⟨636291572, by rfl⟩ : syracuseStep 848388763 = 1272583145) B1272583145
theorem B1131185017 : Blo 2091435 1131185017 := bstep (se 2 (by rfl) ⟨424194381, by rfl⟩ : syracuseStep 1131185017 = 848388763) B848388763
theorem B1508246689 : Blo 2091435 1508246689 := bstep (se 2 (by rfl) ⟨565592508, by rfl⟩ : syracuseStep 1508246689 = 1131185017) B1131185017
theorem B2010995585 : Blo 2091435 2010995585 := bstep (se 2 (by rfl) ⟨754123344, by rfl⟩ : syracuseStep 2010995585 = 1508246689) B1508246689
theorem B1340663723 : Blo 2091435 1340663723 := bstep (se 1 (by rfl) ⟨1005497792, by rfl⟩ : syracuseStep 1340663723 = 2010995585) B2010995585
theorem B893775815 : Blo 2091435 893775815 := bstep (se 1 (by rfl) ⟨670331861, by rfl⟩ : syracuseStep 893775815 = 1340663723) B1340663723
theorem B595850543 : Blo 2091435 595850543 := bstep (se 1 (by rfl) ⟨446887907, by rfl⟩ : syracuseStep 595850543 = 893775815) B893775815
theorem B397233695 : Blo 2091435 397233695 := bstep (se 1 (by rfl) ⟨297925271, by rfl⟩ : syracuseStep 397233695 = 595850543) B595850543
theorem B264822463 : Blo 2091435 264822463 := bstep (se 1 (by rfl) ⟨198616847, by rfl⟩ : syracuseStep 264822463 = 397233695) B397233695
theorem B1412386469 : Blo 2091435 1412386469 := bstep (se 4 (by rfl) ⟨132411231, by rfl⟩ : syracuseStep 1412386469 = 264822463) B264822463
theorem B941590979 : Blo 2091435 941590979 := bstep (se 1 (by rfl) ⟨706193234, by rfl⟩ : syracuseStep 941590979 = 1412386469) B1412386469
theorem B627727319 : Blo 2091435 627727319 := bstep (se 1 (by rfl) ⟨470795489, by rfl⟩ : syracuseStep 627727319 = 941590979) B941590979
theorem B418484879 : Blo 2091435 418484879 := bstep (se 1 (by rfl) ⟨313863659, by rfl⟩ : syracuseStep 418484879 = 627727319) B627727319
theorem B278989919 : Blo 2091435 278989919 := bstep (se 1 (by rfl) ⟨209242439, by rfl⟩ : syracuseStep 278989919 = 418484879) B418484879
theorem B185993279 : Blo 2091435 185993279 := bstep (se 1 (by rfl) ⟨139494959, by rfl⟩ : syracuseStep 185993279 = 278989919) B278989919
theorem B123995519 : Blo 2091435 123995519 := bstep (se 1 (by rfl) ⟨92996639, by rfl⟩ : syracuseStep 123995519 = 185993279) B185993279
theorem B82663679 : Blo 2091435 82663679 := bstep (se 1 (by rfl) ⟨61997759, by rfl⟩ : syracuseStep 82663679 = 123995519) B123995519
theorem B55109119 : Blo 2091435 55109119 := bstep (se 1 (by rfl) ⟨41331839, by rfl⟩ : syracuseStep 55109119 = 82663679) B82663679
theorem B73478825 : Blo 2091435 73478825 := bstep (se 2 (by rfl) ⟨27554559, by rfl⟩ : syracuseStep 73478825 = 55109119) B55109119
theorem B48985883 : Blo 2091435 48985883 := bstep (se 1 (by rfl) ⟨36739412, by rfl⟩ : syracuseStep 48985883 = 73478825) B73478825
theorem B32657255 : Blo 2091435 32657255 := bstep (se 1 (by rfl) ⟨24492941, by rfl⟩ : syracuseStep 32657255 = 48985883) B48985883
theorem B21771503 : Blo 2091435 21771503 := bstep (se 1 (by rfl) ⟨16328627, by rfl⟩ : syracuseStep 21771503 = 32657255) B32657255
theorem B14514335 : Blo 2091435 14514335 := bstep (se 1 (by rfl) ⟨10885751, by rfl⟩ : syracuseStep 14514335 = 21771503) B21771503
theorem B9676223 : Blo 2091435 9676223 := bstep (se 1 (by rfl) ⟨7257167, by rfl⟩ : syracuseStep 9676223 = 14514335) B14514335
theorem B6450815 : Blo 2091435 6450815 := bstep (se 1 (by rfl) ⟨4838111, by rfl⟩ : syracuseStep 6450815 = 9676223) B9676223
theorem B4300543 : Blo 2091435 4300543 := bstep (se 1 (by rfl) ⟨3225407, by rfl⟩ : syracuseStep 4300543 = 6450815) B6450815
theorem B22936229 : Blo 2091435 22936229 := bstep (se 4 (by rfl) ⟨2150271, by rfl⟩ : syracuseStep 22936229 = 4300543) B4300543
theorem B15290819 : Blo 2091435 15290819 := bstep (se 1 (by rfl) ⟨11468114, by rfl⟩ : syracuseStep 15290819 = 22936229) B22936229
theorem B10193879 : Blo 2091435 10193879 := bstep (se 1 (by rfl) ⟨7645409, by rfl⟩ : syracuseStep 10193879 = 15290819) B15290819
theorem B6795919 : Blo 2091435 6795919 := bstep (se 1 (by rfl) ⟨5096939, by rfl⟩ : syracuseStep 6795919 = 10193879) B10193879
theorem B36244901 : Blo 2091435 36244901 := bstep (se 4 (by rfl) ⟨3397959, by rfl⟩ : syracuseStep 36244901 = 6795919) B6795919
theorem B24163267 : Blo 2091435 24163267 := bstep (se 1 (by rfl) ⟨18122450, by rfl⟩ : syracuseStep 24163267 = 36244901) B36244901
theorem B32217689 : Blo 2091435 32217689 := bstep (se 2 (by rfl) ⟨12081633, by rfl⟩ : syracuseStep 32217689 = 24163267) B24163267
theorem B21478459 : Blo 2091435 21478459 := bstep (se 1 (by rfl) ⟨16108844, by rfl⟩ : syracuseStep 21478459 = 32217689) B32217689
theorem B28637945 : Blo 2091435 28637945 := bstep (se 2 (by rfl) ⟨10739229, by rfl⟩ : syracuseStep 28637945 = 21478459) B21478459
theorem B19091963 : Blo 2091435 19091963 := bstep (se 1 (by rfl) ⟨14318972, by rfl⟩ : syracuseStep 19091963 = 28637945) B28637945
theorem B12727975 : Blo 2091435 12727975 := bstep (se 1 (by rfl) ⟨9545981, by rfl⟩ : syracuseStep 12727975 = 19091963) B19091963
theorem B16970633 : Blo 2091435 16970633 := bstep (se 2 (by rfl) ⟨6363987, by rfl⟩ : syracuseStep 16970633 = 12727975) B12727975
theorem B11313755 : Blo 2091435 11313755 := bstep (se 1 (by rfl) ⟨8485316, by rfl⟩ : syracuseStep 11313755 = 16970633) B16970633
theorem B7542503 : Blo 2091435 7542503 := bstep (se 1 (by rfl) ⟨5656877, by rfl⟩ : syracuseStep 7542503 = 11313755) B11313755
theorem B5028335 : Blo 2091435 5028335 := bstep (se 1 (by rfl) ⟨3771251, by rfl⟩ : syracuseStep 5028335 = 7542503) B7542503
theorem B3352223 : Blo 2091435 3352223 := bstep (se 1 (by rfl) ⟨2514167, by rfl⟩ : syracuseStep 3352223 = 5028335) B5028335
theorem B8939261 : Blo 2091435 8939261 := bstep (se 3 (by rfl) ⟨1676111, by rfl⟩ : syracuseStep 8939261 = 3352223) B3352223
theorem B5959507 : Blo 2091435 5959507 := bstep (se 1 (by rfl) ⟨4469630, by rfl⟩ : syracuseStep 5959507 = 8939261) B8939261
theorem B7946009 : Blo 2091435 7946009 := bstep (se 2 (by rfl) ⟨2979753, by rfl⟩ : syracuseStep 7946009 = 5959507) B5959507
theorem B5297339 : Blo 2091435 5297339 := bstep (se 1 (by rfl) ⟨3973004, by rfl⟩ : syracuseStep 5297339 = 7946009) B7946009
theorem B3531559 : Blo 2091435 3531559 := bstep (se 1 (by rfl) ⟨2648669, by rfl⟩ : syracuseStep 3531559 = 5297339) B5297339
theorem B4708745 : Blo 2091435 4708745 := bstep (se 2 (by rfl) ⟨1765779, by rfl⟩ : syracuseStep 4708745 = 3531559) B3531559
theorem B3139163 : Blo 2091435 3139163 := bstep (se 1 (by rfl) ⟨2354372, by rfl⟩ : syracuseStep 3139163 = 4708745) B4708745
theorem B2092775 : Blo 2091435 2092775 := bstep (se 1 (by rfl) ⟨1569581, by rfl⟩ : syracuseStep 2092775 = 3139163) B3139163
theorem B2354377 : Blo 2091435 2354377 := bbase (se 2 (by rfl) ⟨882891, by rfl⟩ : syracuseStep 2354377 = 1765783) (by norm_num)
theorem B3139169 : Blo 2091435 3139169 := bstep (se 2 (by rfl) ⟨1177188, by rfl⟩ : syracuseStep 3139169 = 2354377) B2354377
theorem B2092779 : Blo 2091435 2092779 := bstep (se 1 (by rfl) ⟨1569584, by rfl⟩ : syracuseStep 2092779 = 3139169) B3139169
theorem B2121337 : Blo 2091435 2121337 := bbase (se 2 (by rfl) ⟨795501, by rfl⟩ : syracuseStep 2121337 = 1591003) (by norm_num)
theorem B2828449 : Blo 2091435 2828449 := bstep (se 2 (by rfl) ⟨1060668, by rfl⟩ : syracuseStep 2828449 = 2121337) B2121337
theorem B15085061 : Blo 2091435 15085061 := bstep (se 4 (by rfl) ⟨1414224, by rfl⟩ : syracuseStep 15085061 = 2828449) B2828449
theorem B10056707 : Blo 2091435 10056707 := bstep (se 1 (by rfl) ⟨7542530, by rfl⟩ : syracuseStep 10056707 = 15085061) B15085061
theorem B6704471 : Blo 2091435 6704471 := bstep (se 1 (by rfl) ⟨5028353, by rfl⟩ : syracuseStep 6704471 = 10056707) B10056707
theorem B17878589 : Blo 2091435 17878589 := bstep (se 3 (by rfl) ⟨3352235, by rfl⟩ : syracuseStep 17878589 = 6704471) B6704471
theorem B11919059 : Blo 2091435 11919059 := bstep (se 1 (by rfl) ⟨8939294, by rfl⟩ : syracuseStep 11919059 = 17878589) B17878589
theorem B7946039 : Blo 2091435 7946039 := bstep (se 1 (by rfl) ⟨5959529, by rfl⟩ : syracuseStep 7946039 = 11919059) B11919059
theorem B5297359 : Blo 2091435 5297359 := bstep (se 1 (by rfl) ⟨3973019, by rfl⟩ : syracuseStep 5297359 = 7946039) B7946039
theorem B7063145 : Blo 2091435 7063145 := bstep (se 2 (by rfl) ⟨2648679, by rfl⟩ : syracuseStep 7063145 = 5297359) B5297359
theorem B4708763 : Blo 2091435 4708763 := bstep (se 1 (by rfl) ⟨3531572, by rfl⟩ : syracuseStep 4708763 = 7063145) B7063145
theorem B3139175 : Blo 2091435 3139175 := bstep (se 1 (by rfl) ⟨2354381, by rfl⟩ : syracuseStep 3139175 = 4708763) B4708763
theorem B2092783 : Blo 2091435 2092783 := bstep (se 1 (by rfl) ⟨1569587, by rfl⟩ : syracuseStep 2092783 = 3139175) B3139175
theorem B3139181 : Blo 2091435 3139181 := bbase (se 3 (by rfl) ⟨588596, by rfl⟩ : syracuseStep 3139181 = 1177193) (by norm_num)
theorem B2092787 : Blo 2091435 2092787 := bstep (se 1 (by rfl) ⟨1569590, by rfl⟩ : syracuseStep 2092787 = 3139181) B3139181
theorem B4708781 : Blo 2091435 4708781 := bbase (se 3 (by rfl) ⟨882896, by rfl⟩ : syracuseStep 4708781 = 1765793) (by norm_num)
theorem B3139187 : Blo 2091435 3139187 := bstep (se 1 (by rfl) ⟨2354390, by rfl⟩ : syracuseStep 3139187 = 4708781) B4708781
theorem B2092791 : Blo 2091435 2092791 := bstep (se 1 (by rfl) ⟨1569593, by rfl⟩ : syracuseStep 2092791 = 3139187) B3139187
theorem B2234837 : Blo 2091435 2234837 := bbase (se 7 (by rfl) ⟨26189, by rfl⟩ : syracuseStep 2234837 = 52379) (by norm_num)
theorem B5959565 : Blo 2091435 5959565 := bstep (se 3 (by rfl) ⟨1117418, by rfl⟩ : syracuseStep 5959565 = 2234837) B2234837
theorem B3973043 : Blo 2091435 3973043 := bstep (se 1 (by rfl) ⟨2979782, by rfl⟩ : syracuseStep 3973043 = 5959565) B5959565
theorem B2648695 : Blo 2091435 2648695 := bstep (se 1 (by rfl) ⟨1986521, by rfl⟩ : syracuseStep 2648695 = 3973043) B3973043
theorem B3531593 : Blo 2091435 3531593 := bstep (se 2 (by rfl) ⟨1324347, by rfl⟩ : syracuseStep 3531593 = 2648695) B2648695
theorem B2354395 : Blo 2091435 2354395 := bstep (se 1 (by rfl) ⟨1765796, by rfl⟩ : syracuseStep 2354395 = 3531593) B3531593
theorem B3139193 : Blo 2091435 3139193 := bstep (se 2 (by rfl) ⟨1177197, by rfl⟩ : syracuseStep 3139193 = 2354395) B2354395
theorem B2092795 : Blo 2091435 2092795 := bstep (se 1 (by rfl) ⟨1569596, by rfl⟩ : syracuseStep 2092795 = 3139193) B3139193
theorem B3182029 : Blo 2091435 3182029 := bbase (se 3 (by rfl) ⟨596630, by rfl⟩ : syracuseStep 3182029 = 1193261) (by norm_num)
theorem B67883285 : Blo 2091435 67883285 := bstep (se 6 (by rfl) ⟨1591014, by rfl⟩ : syracuseStep 67883285 = 3182029) B3182029
theorem B45255523 : Blo 2091435 45255523 := bstep (se 1 (by rfl) ⟨33941642, by rfl⟩ : syracuseStep 45255523 = 67883285) B67883285
theorem B60340697 : Blo 2091435 60340697 := bstep (se 2 (by rfl) ⟨22627761, by rfl⟩ : syracuseStep 60340697 = 45255523) B45255523
theorem B40227131 : Blo 2091435 40227131 := bstep (se 1 (by rfl) ⟨30170348, by rfl⟩ : syracuseStep 40227131 = 60340697) B60340697
theorem B26818087 : Blo 2091435 26818087 := bstep (se 1 (by rfl) ⟨20113565, by rfl⟩ : syracuseStep 26818087 = 40227131) B40227131
theorem B35757449 : Blo 2091435 35757449 := bstep (se 2 (by rfl) ⟨13409043, by rfl⟩ : syracuseStep 35757449 = 26818087) B26818087
theorem B23838299 : Blo 2091435 23838299 := bstep (se 1 (by rfl) ⟨17878724, by rfl⟩ : syracuseStep 23838299 = 35757449) B35757449
theorem B15892199 : Blo 2091435 15892199 := bstep (se 1 (by rfl) ⟨11919149, by rfl⟩ : syracuseStep 15892199 = 23838299) B23838299
theorem B10594799 : Blo 2091435 10594799 := bstep (se 1 (by rfl) ⟨7946099, by rfl⟩ : syracuseStep 10594799 = 15892199) B15892199
theorem B7063199 : Blo 2091435 7063199 := bstep (se 1 (by rfl) ⟨5297399, by rfl⟩ : syracuseStep 7063199 = 10594799) B10594799
theorem B4708799 : Blo 2091435 4708799 := bstep (se 1 (by rfl) ⟨3531599, by rfl⟩ : syracuseStep 4708799 = 7063199) B7063199
theorem B3139199 : Blo 2091435 3139199 := bstep (se 1 (by rfl) ⟨2354399, by rfl⟩ : syracuseStep 3139199 = 4708799) B4708799
theorem B2092799 : Blo 2091435 2092799 := bstep (se 1 (by rfl) ⟨1569599, by rfl⟩ : syracuseStep 2092799 = 3139199) B3139199
theorem B3139205 : Blo 2091435 3139205 := bbase (se 4 (by rfl) ⟨294300, by rfl⟩ : syracuseStep 3139205 = 588601) (by norm_num)
theorem B2092803 : Blo 2091435 2092803 := bstep (se 1 (by rfl) ⟨1569602, by rfl⟩ : syracuseStep 2092803 = 3139205) B3139205
theorem B3531613 : Blo 2091435 3531613 := bbase (se 3 (by rfl) ⟨662177, by rfl⟩ : syracuseStep 3531613 = 1324355) (by norm_num)
theorem B4708817 : Blo 2091435 4708817 := bstep (se 2 (by rfl) ⟨1765806, by rfl⟩ : syracuseStep 4708817 = 3531613) B3531613
theorem B3139211 : Blo 2091435 3139211 := bstep (se 1 (by rfl) ⟨2354408, by rfl⟩ : syracuseStep 3139211 = 4708817) B4708817
theorem B2092807 : Blo 2091435 2092807 := bstep (se 1 (by rfl) ⟨1569605, by rfl⟩ : syracuseStep 2092807 = 3139211) B3139211
theorem B2354413 : Blo 2091435 2354413 := bbase (se 3 (by rfl) ⟨441452, by rfl⟩ : syracuseStep 2354413 = 882905) (by norm_num)
theorem B3139217 : Blo 2091435 3139217 := bstep (se 2 (by rfl) ⟨1177206, by rfl⟩ : syracuseStep 3139217 = 2354413) B2354413
theorem B2092811 : Blo 2091435 2092811 := bstep (se 1 (by rfl) ⟨1569608, by rfl⟩ : syracuseStep 2092811 = 3139217) B3139217
theorem B7063253 : Blo 2091435 7063253 := bbase (se 7 (by rfl) ⟨82772, by rfl⟩ : syracuseStep 7063253 = 165545) (by norm_num)
theorem B4708835 : Blo 2091435 4708835 := bstep (se 1 (by rfl) ⟨3531626, by rfl⟩ : syracuseStep 4708835 = 7063253) B7063253
theorem B3139223 : Blo 2091435 3139223 := bstep (se 1 (by rfl) ⟨2354417, by rfl⟩ : syracuseStep 3139223 = 4708835) B4708835
theorem B2092815 : Blo 2091435 2092815 := bstep (se 1 (by rfl) ⟨1569611, by rfl⟩ : syracuseStep 2092815 = 3139223) B3139223
theorem B3139229 : Blo 2091435 3139229 := bbase (se 3 (by rfl) ⟨588605, by rfl⟩ : syracuseStep 3139229 = 1177211) (by norm_num)
theorem B2092819 : Blo 2091435 2092819 := bstep (se 1 (by rfl) ⟨1569614, by rfl⟩ : syracuseStep 2092819 = 3139229) B3139229
theorem B4708853 : Blo 2091435 4708853 := bbase (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) (by norm_num)
theorem B3139235 : Blo 2091435 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B2092823 : Blo 2091435 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B4773109 : Blo 2091435 4773109 := bbase (se 5 (by rfl) ⟨223739, by rfl⟩ : syracuseStep 4773109 = 447479) (by norm_num)
theorem B6364145 : Blo 2091435 6364145 := bstep (se 2 (by rfl) ⟨2386554, by rfl⟩ : syracuseStep 6364145 = 4773109) B4773109
theorem B4242763 : Blo 2091435 4242763 := bstep (se 1 (by rfl) ⟨3182072, by rfl⟩ : syracuseStep 4242763 = 6364145) B6364145
theorem B22628069 : Blo 2091435 22628069 := bstep (se 4 (by rfl) ⟨2121381, by rfl⟩ : syracuseStep 22628069 = 4242763) B4242763
theorem B15085379 : Blo 2091435 15085379 := bstep (se 1 (by rfl) ⟨11314034, by rfl⟩ : syracuseStep 15085379 = 22628069) B22628069
theorem B40227677 : Blo 2091435 40227677 := bstep (se 3 (by rfl) ⟨7542689, by rfl⟩ : syracuseStep 40227677 = 15085379) B15085379
theorem B26818451 : Blo 2091435 26818451 := bstep (se 1 (by rfl) ⟨20113838, by rfl⟩ : syracuseStep 26818451 = 40227677) B40227677
theorem B17878967 : Blo 2091435 17878967 := bstep (se 1 (by rfl) ⟨13409225, by rfl⟩ : syracuseStep 17878967 = 26818451) B26818451
theorem B11919311 : Blo 2091435 11919311 := bstep (se 1 (by rfl) ⟨8939483, by rfl⟩ : syracuseStep 11919311 = 17878967) B17878967
theorem B7946207 : Blo 2091435 7946207 := bstep (se 1 (by rfl) ⟨5959655, by rfl⟩ : syracuseStep 7946207 = 11919311) B11919311
theorem B5297471 : Blo 2091435 5297471 := bstep (se 1 (by rfl) ⟨3973103, by rfl⟩ : syracuseStep 5297471 = 7946207) B7946207
theorem B3531647 : Blo 2091435 3531647 := bstep (se 1 (by rfl) ⟨2648735, by rfl⟩ : syracuseStep 3531647 = 5297471) B5297471
theorem B2354431 : Blo 2091435 2354431 := bstep (se 1 (by rfl) ⟨1765823, by rfl⟩ : syracuseStep 2354431 = 3531647) B3531647
theorem B3139241 : Blo 2091435 3139241 := bstep (se 2 (by rfl) ⟨1177215, by rfl⟩ : syracuseStep 3139241 = 2354431) B2354431
theorem B2092827 : Blo 2091435 2092827 := bstep (se 1 (by rfl) ⟨1569620, by rfl⟩ : syracuseStep 2092827 = 3139241) B3139241
theorem B4242773 : Blo 2091435 4242773 := bbase (se 11 (by rfl) ⟨3107, by rfl⟩ : syracuseStep 4242773 = 6215) (by norm_num)
theorem B2828515 : Blo 2091435 2828515 := bstep (se 1 (by rfl) ⟨2121386, by rfl⟩ : syracuseStep 2828515 = 4242773) B4242773
theorem B3771353 : Blo 2091435 3771353 := bstep (se 2 (by rfl) ⟨1414257, by rfl⟩ : syracuseStep 3771353 = 2828515) B2828515
theorem B2514235 : Blo 2091435 2514235 := bstep (se 1 (by rfl) ⟨1885676, by rfl⟩ : syracuseStep 2514235 = 3771353) B3771353
theorem B3352313 : Blo 2091435 3352313 := bstep (se 2 (by rfl) ⟨1257117, by rfl⟩ : syracuseStep 3352313 = 2514235) B2514235
theorem B2234875 : Blo 2091435 2234875 := bstep (se 1 (by rfl) ⟨1676156, by rfl⟩ : syracuseStep 2234875 = 3352313) B3352313
theorem B2979833 : Blo 2091435 2979833 := bstep (se 2 (by rfl) ⟨1117437, by rfl⟩ : syracuseStep 2979833 = 2234875) B2234875
theorem B7946221 : Blo 2091435 7946221 := bstep (se 3 (by rfl) ⟨1489916, by rfl⟩ : syracuseStep 7946221 = 2979833) B2979833
theorem B10594961 : Blo 2091435 10594961 := bstep (se 2 (by rfl) ⟨3973110, by rfl⟩ : syracuseStep 10594961 = 7946221) B7946221
theorem B7063307 : Blo 2091435 7063307 := bstep (se 1 (by rfl) ⟨5297480, by rfl⟩ : syracuseStep 7063307 = 10594961) B10594961
theorem B4708871 : Blo 2091435 4708871 := bstep (se 1 (by rfl) ⟨3531653, by rfl⟩ : syracuseStep 4708871 = 7063307) B7063307
theorem B3139247 : Blo 2091435 3139247 := bstep (se 1 (by rfl) ⟨2354435, by rfl⟩ : syracuseStep 3139247 = 4708871) B4708871
theorem B2092831 : Blo 2091435 2092831 := bstep (se 1 (by rfl) ⟨1569623, by rfl⟩ : syracuseStep 2092831 = 3139247) B3139247
theorem B3139253 : Blo 2091435 3139253 := bbase (se 5 (by rfl) ⟨147152, by rfl⟩ : syracuseStep 3139253 = 294305) (by norm_num)
theorem B2092835 : Blo 2091435 2092835 := bstep (se 1 (by rfl) ⟨1569626, by rfl⟩ : syracuseStep 2092835 = 3139253) B3139253
theorem B5297501 : Blo 2091435 5297501 := bbase (se 3 (by rfl) ⟨993281, by rfl⟩ : syracuseStep 5297501 = 1986563) (by norm_num)
theorem B3531667 : Blo 2091435 3531667 := bstep (se 1 (by rfl) ⟨2648750, by rfl⟩ : syracuseStep 3531667 = 5297501) B5297501
theorem B4708889 : Blo 2091435 4708889 := bstep (se 2 (by rfl) ⟨1765833, by rfl⟩ : syracuseStep 4708889 = 3531667) B3531667
theorem B3139259 : Blo 2091435 3139259 := bstep (se 1 (by rfl) ⟨2354444, by rfl⟩ : syracuseStep 3139259 = 4708889) B4708889
theorem B2092839 : Blo 2091435 2092839 := bstep (se 1 (by rfl) ⟨1569629, by rfl⟩ : syracuseStep 2092839 = 3139259) B3139259
theorem B2354449 : Blo 2091435 2354449 := bbase (se 2 (by rfl) ⟨882918, by rfl⟩ : syracuseStep 2354449 = 1765837) (by norm_num)
theorem B3139265 : Blo 2091435 3139265 := bstep (se 2 (by rfl) ⟨1177224, by rfl⟩ : syracuseStep 3139265 = 2354449) B2354449
theorem B2092843 : Blo 2091435 2092843 := bstep (se 1 (by rfl) ⟨1569632, by rfl⟩ : syracuseStep 2092843 = 3139265) B3139265
theorem B3973141 : Blo 2091435 3973141 := bbase (se 6 (by rfl) ⟨93120, by rfl⟩ : syracuseStep 3973141 = 186241) (by norm_num)
theorem B5297521 : Blo 2091435 5297521 := bstep (se 2 (by rfl) ⟨1986570, by rfl⟩ : syracuseStep 5297521 = 3973141) B3973141
theorem B7063361 : Blo 2091435 7063361 := bstep (se 2 (by rfl) ⟨2648760, by rfl⟩ : syracuseStep 7063361 = 5297521) B5297521
theorem B4708907 : Blo 2091435 4708907 := bstep (se 1 (by rfl) ⟨3531680, by rfl⟩ : syracuseStep 4708907 = 7063361) B7063361
theorem B3139271 : Blo 2091435 3139271 := bstep (se 1 (by rfl) ⟨2354453, by rfl⟩ : syracuseStep 3139271 = 4708907) B4708907
theorem B2092847 : Blo 2091435 2092847 := bstep (se 1 (by rfl) ⟨1569635, by rfl⟩ : syracuseStep 2092847 = 3139271) B3139271
theorem B3139277 : Blo 2091435 3139277 := bbase (se 3 (by rfl) ⟨588614, by rfl⟩ : syracuseStep 3139277 = 1177229) (by norm_num)
theorem B2092851 : Blo 2091435 2092851 := bstep (se 1 (by rfl) ⟨1569638, by rfl⟩ : syracuseStep 2092851 = 3139277) B3139277
theorem B4708925 : Blo 2091435 4708925 := bbase (se 3 (by rfl) ⟨882923, by rfl⟩ : syracuseStep 4708925 = 1765847) (by norm_num)
theorem B3139283 : Blo 2091435 3139283 := bstep (se 1 (by rfl) ⟨2354462, by rfl⟩ : syracuseStep 3139283 = 4708925) B4708925
theorem B2092855 : Blo 2091435 2092855 := bstep (se 1 (by rfl) ⟨1569641, by rfl⟩ : syracuseStep 2092855 = 3139283) B3139283
theorem B3531701 : Blo 2091435 3531701 := bbase (se 5 (by rfl) ⟨165548, by rfl⟩ : syracuseStep 3531701 = 331097) (by norm_num)
theorem B2354467 : Blo 2091435 2354467 := bstep (se 1 (by rfl) ⟨1765850, by rfl⟩ : syracuseStep 2354467 = 3531701) B3531701
theorem B3139289 : Blo 2091435 3139289 := bstep (se 2 (by rfl) ⟨1177233, by rfl⟩ : syracuseStep 3139289 = 2354467) B2354467
theorem B2092859 : Blo 2091435 2092859 := bstep (se 1 (by rfl) ⟨1569644, by rfl⟩ : syracuseStep 2092859 = 3139289) B3139289
theorem B2234909 : Blo 2091435 2234909 := bbase (se 3 (by rfl) ⟨419045, by rfl⟩ : syracuseStep 2234909 = 838091) (by norm_num)
theorem B5959757 : Blo 2091435 5959757 := bstep (se 3 (by rfl) ⟨1117454, by rfl⟩ : syracuseStep 5959757 = 2234909) B2234909
theorem B15892685 : Blo 2091435 15892685 := bstep (se 3 (by rfl) ⟨2979878, by rfl⟩ : syracuseStep 15892685 = 5959757) B5959757
theorem B10595123 : Blo 2091435 10595123 := bstep (se 1 (by rfl) ⟨7946342, by rfl⟩ : syracuseStep 10595123 = 15892685) B15892685
theorem B7063415 : Blo 2091435 7063415 := bstep (se 1 (by rfl) ⟨5297561, by rfl⟩ : syracuseStep 7063415 = 10595123) B10595123
theorem B4708943 : Blo 2091435 4708943 := bstep (se 1 (by rfl) ⟨3531707, by rfl⟩ : syracuseStep 4708943 = 7063415) B7063415
theorem B3139295 : Blo 2091435 3139295 := bstep (se 1 (by rfl) ⟨2354471, by rfl⟩ : syracuseStep 3139295 = 4708943) B4708943
theorem B2092863 : Blo 2091435 2092863 := bstep (se 1 (by rfl) ⟨1569647, by rfl⟩ : syracuseStep 2092863 = 3139295) B3139295
theorem B3139301 : Blo 2091435 3139301 := bbase (se 4 (by rfl) ⟨294309, by rfl⟩ : syracuseStep 3139301 = 588619) (by norm_num)
theorem B2092867 : Blo 2091435 2092867 := bstep (se 1 (by rfl) ⟨1569650, by rfl⟩ : syracuseStep 2092867 = 3139301) B3139301
theorem B5959781 : Blo 2091435 5959781 := bbase (se 4 (by rfl) ⟨558729, by rfl⟩ : syracuseStep 5959781 = 1117459) (by norm_num)
theorem B3973187 : Blo 2091435 3973187 := bstep (se 1 (by rfl) ⟨2979890, by rfl⟩ : syracuseStep 3973187 = 5959781) B5959781
theorem B2648791 : Blo 2091435 2648791 := bstep (se 1 (by rfl) ⟨1986593, by rfl⟩ : syracuseStep 2648791 = 3973187) B3973187
theorem B3531721 : Blo 2091435 3531721 := bstep (se 2 (by rfl) ⟨1324395, by rfl⟩ : syracuseStep 3531721 = 2648791) B2648791
theorem B4708961 : Blo 2091435 4708961 := bstep (se 2 (by rfl) ⟨1765860, by rfl⟩ : syracuseStep 4708961 = 3531721) B3531721
theorem B3139307 : Blo 2091435 3139307 := bstep (se 1 (by rfl) ⟨2354480, by rfl⟩ : syracuseStep 3139307 = 4708961) B4708961
theorem B2092871 : Blo 2091435 2092871 := bstep (se 1 (by rfl) ⟨1569653, by rfl⟩ : syracuseStep 2092871 = 3139307) B3139307
theorem B2354485 : Blo 2091435 2354485 := bbase (se 5 (by rfl) ⟨110366, by rfl⟩ : syracuseStep 2354485 = 220733) (by norm_num)
theorem B3139313 : Blo 2091435 3139313 := bstep (se 2 (by rfl) ⟨1177242, by rfl⟩ : syracuseStep 3139313 = 2354485) B2354485
theorem B2092875 : Blo 2091435 2092875 := bstep (se 1 (by rfl) ⟨1569656, by rfl⟩ : syracuseStep 2092875 = 3139313) B3139313
theorem B2648801 : Blo 2091435 2648801 := bbase (se 2 (by rfl) ⟨993300, by rfl⟩ : syracuseStep 2648801 = 1986601) (by norm_num)
theorem B7063469 : Blo 2091435 7063469 := bstep (se 3 (by rfl) ⟨1324400, by rfl⟩ : syracuseStep 7063469 = 2648801) B2648801
theorem B4708979 : Blo 2091435 4708979 := bstep (se 1 (by rfl) ⟨3531734, by rfl⟩ : syracuseStep 4708979 = 7063469) B7063469
theorem B3139319 : Blo 2091435 3139319 := bstep (se 1 (by rfl) ⟨2354489, by rfl⟩ : syracuseStep 3139319 = 4708979) B4708979
theorem B2092879 : Blo 2091435 2092879 := bstep (se 1 (by rfl) ⟨1569659, by rfl⟩ : syracuseStep 2092879 = 3139319) B3139319
theorem B3139325 : Blo 2091435 3139325 := bbase (se 3 (by rfl) ⟨588623, by rfl⟩ : syracuseStep 3139325 = 1177247) (by norm_num)
theorem B2092883 : Blo 2091435 2092883 := bstep (se 1 (by rfl) ⟨1569662, by rfl⟩ : syracuseStep 2092883 = 3139325) B3139325
theorem B4708997 : Blo 2091435 4708997 := bbase (se 4 (by rfl) ⟨441468, by rfl⟩ : syracuseStep 4708997 = 882937) (by norm_num)
theorem B3139331 : Blo 2091435 3139331 := bstep (se 1 (by rfl) ⟨2354498, by rfl⟩ : syracuseStep 3139331 = 4708997) B4708997
theorem B2092887 : Blo 2091435 2092887 := bstep (se 1 (by rfl) ⟨1569665, by rfl⟩ : syracuseStep 2092887 = 3139331) B3139331
theorem B3771461 : Blo 2091435 3771461 := bbase (se 4 (by rfl) ⟨353574, by rfl⟩ : syracuseStep 3771461 = 707149) (by norm_num)
theorem B10057229 : Blo 2091435 10057229 := bstep (se 3 (by rfl) ⟨1885730, by rfl⟩ : syracuseStep 10057229 = 3771461) B3771461
theorem B6704819 : Blo 2091435 6704819 := bstep (se 1 (by rfl) ⟨5028614, by rfl⟩ : syracuseStep 6704819 = 10057229) B10057229
theorem B4469879 : Blo 2091435 4469879 := bstep (se 1 (by rfl) ⟨3352409, by rfl⟩ : syracuseStep 4469879 = 6704819) B6704819
theorem B2979919 : Blo 2091435 2979919 := bstep (se 1 (by rfl) ⟨2234939, by rfl⟩ : syracuseStep 2979919 = 4469879) B4469879
theorem B3973225 : Blo 2091435 3973225 := bstep (se 2 (by rfl) ⟨1489959, by rfl⟩ : syracuseStep 3973225 = 2979919) B2979919
theorem B5297633 : Blo 2091435 5297633 := bstep (se 2 (by rfl) ⟨1986612, by rfl⟩ : syracuseStep 5297633 = 3973225) B3973225
theorem B3531755 : Blo 2091435 3531755 := bstep (se 1 (by rfl) ⟨2648816, by rfl⟩ : syracuseStep 3531755 = 5297633) B5297633
theorem B2354503 : Blo 2091435 2354503 := bstep (se 1 (by rfl) ⟨1765877, by rfl⟩ : syracuseStep 2354503 = 3531755) B3531755
theorem B3139337 : Blo 2091435 3139337 := bstep (se 2 (by rfl) ⟨1177251, by rfl⟩ : syracuseStep 3139337 = 2354503) B2354503
theorem B2092891 : Blo 2091435 2092891 := bstep (se 1 (by rfl) ⟨1569668, by rfl⟩ : syracuseStep 2092891 = 3139337) B3139337
theorem B10595285 : Blo 2091435 10595285 := bbase (se 7 (by rfl) ⟨124163, by rfl⟩ : syracuseStep 10595285 = 248327) (by norm_num)
theorem B7063523 : Blo 2091435 7063523 := bstep (se 1 (by rfl) ⟨5297642, by rfl⟩ : syracuseStep 7063523 = 10595285) B10595285
theorem B4709015 : Blo 2091435 4709015 := bstep (se 1 (by rfl) ⟨3531761, by rfl⟩ : syracuseStep 4709015 = 7063523) B7063523
theorem B3139343 : Blo 2091435 3139343 := bstep (se 1 (by rfl) ⟨2354507, by rfl⟩ : syracuseStep 3139343 = 4709015) B4709015
theorem B2092895 : Blo 2091435 2092895 := bstep (se 1 (by rfl) ⟨1569671, by rfl⟩ : syracuseStep 2092895 = 3139343) B3139343
theorem B3139349 : Blo 2091435 3139349 := bbase (se 6 (by rfl) ⟨73578, by rfl⟩ : syracuseStep 3139349 = 147157) (by norm_num)
theorem B2092899 : Blo 2091435 2092899 := bstep (se 1 (by rfl) ⟨1569674, by rfl⟩ : syracuseStep 2092899 = 3139349) B3139349
theorem B2265445 : Blo 2091435 2265445 := bbase (se 4 (by rfl) ⟨212385, by rfl⟩ : syracuseStep 2265445 = 424771) (by norm_num)
theorem B3020593 : Blo 2091435 3020593 := bstep (se 2 (by rfl) ⟨1132722, by rfl⟩ : syracuseStep 3020593 = 2265445) B2265445
theorem B4027457 : Blo 2091435 4027457 := bstep (se 2 (by rfl) ⟨1510296, by rfl⟩ : syracuseStep 4027457 = 3020593) B3020593
theorem B2684971 : Blo 2091435 2684971 := bstep (se 1 (by rfl) ⟨2013728, by rfl⟩ : syracuseStep 2684971 = 4027457) B4027457
theorem B14319845 : Blo 2091435 14319845 := bstep (se 4 (by rfl) ⟨1342485, by rfl⟩ : syracuseStep 14319845 = 2684971) B2684971
theorem B9546563 : Blo 2091435 9546563 := bstep (se 1 (by rfl) ⟨7159922, by rfl⟩ : syracuseStep 9546563 = 14319845) B14319845
theorem B6364375 : Blo 2091435 6364375 := bstep (se 1 (by rfl) ⟨4773281, by rfl⟩ : syracuseStep 6364375 = 9546563) B9546563
theorem B135773333 : Blo 2091435 135773333 := bstep (se 6 (by rfl) ⟨3182187, by rfl⟩ : syracuseStep 135773333 = 6364375) B6364375
theorem B90515555 : Blo 2091435 90515555 := bstep (se 1 (by rfl) ⟨67886666, by rfl⟩ : syracuseStep 90515555 = 135773333) B135773333
theorem B60343703 : Blo 2091435 60343703 := bstep (se 1 (by rfl) ⟨45257777, by rfl⟩ : syracuseStep 60343703 = 90515555) B90515555
theorem B40229135 : Blo 2091435 40229135 := bstep (se 1 (by rfl) ⟨30171851, by rfl⟩ : syracuseStep 40229135 = 60343703) B60343703
theorem B26819423 : Blo 2091435 26819423 := bstep (se 1 (by rfl) ⟨20114567, by rfl⟩ : syracuseStep 26819423 = 40229135) B40229135
theorem B17879615 : Blo 2091435 17879615 := bstep (se 1 (by rfl) ⟨13409711, by rfl⟩ : syracuseStep 17879615 = 26819423) B26819423
theorem B11919743 : Blo 2091435 11919743 := bstep (se 1 (by rfl) ⟨8939807, by rfl⟩ : syracuseStep 11919743 = 17879615) B17879615
theorem B7946495 : Blo 2091435 7946495 := bstep (se 1 (by rfl) ⟨5959871, by rfl⟩ : syracuseStep 7946495 = 11919743) B11919743
theorem B5297663 : Blo 2091435 5297663 := bstep (se 1 (by rfl) ⟨3973247, by rfl⟩ : syracuseStep 5297663 = 7946495) B7946495
theorem B3531775 : Blo 2091435 3531775 := bstep (se 1 (by rfl) ⟨2648831, by rfl⟩ : syracuseStep 3531775 = 5297663) B5297663
theorem B4709033 : Blo 2091435 4709033 := bstep (se 2 (by rfl) ⟨1765887, by rfl⟩ : syracuseStep 4709033 = 3531775) B3531775
theorem B3139355 : Blo 2091435 3139355 := bstep (se 1 (by rfl) ⟨2354516, by rfl⟩ : syracuseStep 3139355 = 4709033) B4709033
theorem B2092903 : Blo 2091435 2092903 := bstep (se 1 (by rfl) ⟨1569677, by rfl⟩ : syracuseStep 2092903 = 3139355) B3139355
theorem B2354521 : Blo 2091435 2354521 := bbase (se 2 (by rfl) ⟨882945, by rfl⟩ : syracuseStep 2354521 = 1765891) (by norm_num)
theorem B3139361 : Blo 2091435 3139361 := bstep (se 2 (by rfl) ⟨1177260, by rfl⟩ : syracuseStep 3139361 = 2354521) B2354521
theorem B2092907 : Blo 2091435 2092907 := bstep (se 1 (by rfl) ⟨1569680, by rfl⟩ : syracuseStep 2092907 = 3139361) B3139361
theorem B8601653 : Blo 2091435 8601653 := bbase (se 5 (by rfl) ⟨403202, by rfl⟩ : syracuseStep 8601653 = 806405) (by norm_num)
theorem B5734435 : Blo 2091435 5734435 := bstep (se 1 (by rfl) ⟨4300826, by rfl⟩ : syracuseStep 5734435 = 8601653) B8601653
theorem B7645913 : Blo 2091435 7645913 := bstep (se 2 (by rfl) ⟨2867217, by rfl⟩ : syracuseStep 7645913 = 5734435) B5734435
theorem B5097275 : Blo 2091435 5097275 := bstep (se 1 (by rfl) ⟨3822956, by rfl⟩ : syracuseStep 5097275 = 7645913) B7645913
theorem B3398183 : Blo 2091435 3398183 := bstep (se 1 (by rfl) ⟨2548637, by rfl⟩ : syracuseStep 3398183 = 5097275) B5097275
theorem B2265455 : Blo 2091435 2265455 := bstep (se 1 (by rfl) ⟨1699091, by rfl⟩ : syracuseStep 2265455 = 3398183) B3398183
theorem B6041213 : Blo 2091435 6041213 := bstep (se 3 (by rfl) ⟨1132727, by rfl⟩ : syracuseStep 6041213 = 2265455) B2265455
theorem B4027475 : Blo 2091435 4027475 := bstep (se 1 (by rfl) ⟨3020606, by rfl⟩ : syracuseStep 4027475 = 6041213) B6041213
theorem B2684983 : Blo 2091435 2684983 := bstep (se 1 (by rfl) ⟨2013737, by rfl⟩ : syracuseStep 2684983 = 4027475) B4027475
theorem B3579977 : Blo 2091435 3579977 := bstep (se 2 (by rfl) ⟨1342491, by rfl⟩ : syracuseStep 3579977 = 2684983) B2684983
theorem B9546605 : Blo 2091435 9546605 := bstep (se 3 (by rfl) ⟨1789988, by rfl⟩ : syracuseStep 9546605 = 3579977) B3579977
theorem B6364403 : Blo 2091435 6364403 := bstep (se 1 (by rfl) ⟨4773302, by rfl⟩ : syracuseStep 6364403 = 9546605) B9546605
theorem B4242935 : Blo 2091435 4242935 := bstep (se 1 (by rfl) ⟨3182201, by rfl⟩ : syracuseStep 4242935 = 6364403) B6364403
theorem B2828623 : Blo 2091435 2828623 := bstep (se 1 (by rfl) ⟨2121467, by rfl⟩ : syracuseStep 2828623 = 4242935) B4242935
theorem B3771497 : Blo 2091435 3771497 := bstep (se 2 (by rfl) ⟨1414311, by rfl⟩ : syracuseStep 3771497 = 2828623) B2828623
theorem B2514331 : Blo 2091435 2514331 := bstep (se 1 (by rfl) ⟨1885748, by rfl⟩ : syracuseStep 2514331 = 3771497) B3771497
theorem B3352441 : Blo 2091435 3352441 := bstep (se 2 (by rfl) ⟨1257165, by rfl⟩ : syracuseStep 3352441 = 2514331) B2514331
theorem B4469921 : Blo 2091435 4469921 := bstep (se 2 (by rfl) ⟨1676220, by rfl⟩ : syracuseStep 4469921 = 3352441) B3352441
theorem B2979947 : Blo 2091435 2979947 := bstep (se 1 (by rfl) ⟨2234960, by rfl⟩ : syracuseStep 2979947 = 4469921) B4469921
theorem B7946525 : Blo 2091435 7946525 := bstep (se 3 (by rfl) ⟨1489973, by rfl⟩ : syracuseStep 7946525 = 2979947) B2979947
theorem B5297683 : Blo 2091435 5297683 := bstep (se 1 (by rfl) ⟨3973262, by rfl⟩ : syracuseStep 5297683 = 7946525) B7946525
theorem B7063577 : Blo 2091435 7063577 := bstep (se 2 (by rfl) ⟨2648841, by rfl⟩ : syracuseStep 7063577 = 5297683) B5297683
theorem B4709051 : Blo 2091435 4709051 := bstep (se 1 (by rfl) ⟨3531788, by rfl⟩ : syracuseStep 4709051 = 7063577) B7063577
theorem B3139367 : Blo 2091435 3139367 := bstep (se 1 (by rfl) ⟨2354525, by rfl⟩ : syracuseStep 3139367 = 4709051) B4709051
theorem B2092911 : Blo 2091435 2092911 := bstep (se 1 (by rfl) ⟨1569683, by rfl⟩ : syracuseStep 2092911 = 3139367) B3139367
theorem B3139373 : Blo 2091435 3139373 := bbase (se 3 (by rfl) ⟨588632, by rfl⟩ : syracuseStep 3139373 = 1177265) (by norm_num)
theorem B2092915 : Blo 2091435 2092915 := bstep (se 1 (by rfl) ⟨1569686, by rfl⟩ : syracuseStep 2092915 = 3139373) B3139373
theorem B4709069 : Blo 2091435 4709069 := bbase (se 3 (by rfl) ⟨882950, by rfl⟩ : syracuseStep 4709069 = 1765901) (by norm_num)
theorem B3139379 : Blo 2091435 3139379 := bstep (se 1 (by rfl) ⟨2354534, by rfl⟩ : syracuseStep 3139379 = 4709069) B4709069
theorem B2092919 : Blo 2091435 2092919 := bstep (se 1 (by rfl) ⟨1569689, by rfl⟩ : syracuseStep 2092919 = 3139379) B3139379
theorem B2648857 : Blo 2091435 2648857 := bbase (se 2 (by rfl) ⟨993321, by rfl⟩ : syracuseStep 2648857 = 1986643) (by norm_num)
theorem B3531809 : Blo 2091435 3531809 := bstep (se 2 (by rfl) ⟨1324428, by rfl⟩ : syracuseStep 3531809 = 2648857) B2648857
theorem B2354539 : Blo 2091435 2354539 := bstep (se 1 (by rfl) ⟨1765904, by rfl⟩ : syracuseStep 2354539 = 3531809) B3531809
theorem B3139385 : Blo 2091435 3139385 := bstep (se 2 (by rfl) ⟨1177269, by rfl⟩ : syracuseStep 3139385 = 2354539) B2354539
theorem B2092923 : Blo 2091435 2092923 := bstep (se 1 (by rfl) ⟨1569692, by rfl⟩ : syracuseStep 2092923 = 3139385) B3139385
theorem B8939909 : Blo 2091435 8939909 := bbase (se 4 (by rfl) ⟨838116, by rfl⟩ : syracuseStep 8939909 = 1676233) (by norm_num)
theorem B23839757 : Blo 2091435 23839757 := bstep (se 3 (by rfl) ⟨4469954, by rfl⟩ : syracuseStep 23839757 = 8939909) B8939909
theorem B15893171 : Blo 2091435 15893171 := bstep (se 1 (by rfl) ⟨11919878, by rfl⟩ : syracuseStep 15893171 = 23839757) B23839757
theorem B10595447 : Blo 2091435 10595447 := bstep (se 1 (by rfl) ⟨7946585, by rfl⟩ : syracuseStep 10595447 = 15893171) B15893171
theorem B7063631 : Blo 2091435 7063631 := bstep (se 1 (by rfl) ⟨5297723, by rfl⟩ : syracuseStep 7063631 = 10595447) B10595447
theorem B4709087 : Blo 2091435 4709087 := bstep (se 1 (by rfl) ⟨3531815, by rfl⟩ : syracuseStep 4709087 = 7063631) B7063631
theorem B3139391 : Blo 2091435 3139391 := bstep (se 1 (by rfl) ⟨2354543, by rfl⟩ : syracuseStep 3139391 = 4709087) B4709087
theorem B2092927 : Blo 2091435 2092927 := bstep (se 1 (by rfl) ⟨1569695, by rfl⟩ : syracuseStep 2092927 = 3139391) B3139391
theorem B3139397 : Blo 2091435 3139397 := bbase (se 4 (by rfl) ⟨294318, by rfl⟩ : syracuseStep 3139397 = 588637) (by norm_num)
theorem B2092931 : Blo 2091435 2092931 := bstep (se 1 (by rfl) ⟨1569698, by rfl⟩ : syracuseStep 2092931 = 3139397) B3139397
theorem B3531829 : Blo 2091435 3531829 := bbase (se 5 (by rfl) ⟨165554, by rfl⟩ : syracuseStep 3531829 = 331109) (by norm_num)
theorem B4709105 : Blo 2091435 4709105 := bstep (se 2 (by rfl) ⟨1765914, by rfl⟩ : syracuseStep 4709105 = 3531829) B3531829
theorem B3139403 : Blo 2091435 3139403 := bstep (se 1 (by rfl) ⟨2354552, by rfl⟩ : syracuseStep 3139403 = 4709105) B4709105
theorem B2092935 : Blo 2091435 2092935 := bstep (se 1 (by rfl) ⟨1569701, by rfl⟩ : syracuseStep 2092935 = 3139403) B3139403
theorem B2354557 : Blo 2091435 2354557 := bbase (se 3 (by rfl) ⟨441479, by rfl⟩ : syracuseStep 2354557 = 882959) (by norm_num)
theorem B3139409 : Blo 2091435 3139409 := bstep (se 2 (by rfl) ⟨1177278, by rfl⟩ : syracuseStep 3139409 = 2354557) B2354557
theorem B2092939 : Blo 2091435 2092939 := bstep (se 1 (by rfl) ⟨1569704, by rfl⟩ : syracuseStep 2092939 = 3139409) B3139409
theorem B7063685 : Blo 2091435 7063685 := bbase (se 4 (by rfl) ⟨662220, by rfl⟩ : syracuseStep 7063685 = 1324441) (by norm_num)
theorem B4709123 : Blo 2091435 4709123 := bstep (se 1 (by rfl) ⟨3531842, by rfl⟩ : syracuseStep 4709123 = 7063685) B7063685
theorem B3139415 : Blo 2091435 3139415 := bstep (se 1 (by rfl) ⟨2354561, by rfl⟩ : syracuseStep 3139415 = 4709123) B4709123
theorem B2092943 : Blo 2091435 2092943 := bstep (se 1 (by rfl) ⟨1569707, by rfl⟩ : syracuseStep 2092943 = 3139415) B3139415
theorem B3139421 : Blo 2091435 3139421 := bbase (se 3 (by rfl) ⟨588641, by rfl⟩ : syracuseStep 3139421 = 1177283) (by norm_num)
theorem B2092947 : Blo 2091435 2092947 := bstep (se 1 (by rfl) ⟨1569710, by rfl⟩ : syracuseStep 2092947 = 3139421) B3139421
theorem B4709141 : Blo 2091435 4709141 := bbase (se 6 (by rfl) ⟨110370, by rfl⟩ : syracuseStep 4709141 = 220741) (by norm_num)
theorem B3139427 : Blo 2091435 3139427 := bstep (se 1 (by rfl) ⟨2354570, by rfl⟩ : syracuseStep 3139427 = 4709141) B4709141
theorem B2092951 : Blo 2091435 2092951 := bstep (se 1 (by rfl) ⟨1569713, by rfl⟩ : syracuseStep 2092951 = 3139427) B3139427
theorem B7946693 : Blo 2091435 7946693 := bbase (se 4 (by rfl) ⟨745002, by rfl⟩ : syracuseStep 7946693 = 1490005) (by norm_num)
theorem B5297795 : Blo 2091435 5297795 := bstep (se 1 (by rfl) ⟨3973346, by rfl⟩ : syracuseStep 5297795 = 7946693) B7946693
theorem B3531863 : Blo 2091435 3531863 := bstep (se 1 (by rfl) ⟨2648897, by rfl⟩ : syracuseStep 3531863 = 5297795) B5297795
theorem B2354575 : Blo 2091435 2354575 := bstep (se 1 (by rfl) ⟨1765931, by rfl⟩ : syracuseStep 2354575 = 3531863) B3531863
theorem B3139433 : Blo 2091435 3139433 := bstep (se 2 (by rfl) ⟨1177287, by rfl⟩ : syracuseStep 3139433 = 2354575) B2354575
theorem B2092955 : Blo 2091435 2092955 := bstep (se 1 (by rfl) ⟨1569716, by rfl⟩ : syracuseStep 2092955 = 3139433) B3139433
theorem B9546821 : Blo 2091435 9546821 := bbase (se 4 (by rfl) ⟨895014, by rfl⟩ : syracuseStep 9546821 = 1790029) (by norm_num)
theorem B6364547 : Blo 2091435 6364547 := bstep (se 1 (by rfl) ⟨4773410, by rfl⟩ : syracuseStep 6364547 = 9546821) B9546821
theorem B4243031 : Blo 2091435 4243031 := bstep (se 1 (by rfl) ⟨3182273, by rfl⟩ : syracuseStep 4243031 = 6364547) B6364547
theorem B2828687 : Blo 2091435 2828687 := bstep (se 1 (by rfl) ⟨2121515, by rfl⟩ : syracuseStep 2828687 = 4243031) B4243031
theorem B7543165 : Blo 2091435 7543165 := bstep (se 3 (by rfl) ⟨1414343, by rfl⟩ : syracuseStep 7543165 = 2828687) B2828687
theorem B10057553 : Blo 2091435 10057553 := bstep (se 2 (by rfl) ⟨3771582, by rfl⟩ : syracuseStep 10057553 = 7543165) B7543165
theorem B6705035 : Blo 2091435 6705035 := bstep (se 1 (by rfl) ⟨5028776, by rfl⟩ : syracuseStep 6705035 = 10057553) B10057553
theorem B4470023 : Blo 2091435 4470023 := bstep (se 1 (by rfl) ⟨3352517, by rfl⟩ : syracuseStep 4470023 = 6705035) B6705035
theorem B11920061 : Blo 2091435 11920061 := bstep (se 3 (by rfl) ⟨2235011, by rfl⟩ : syracuseStep 11920061 = 4470023) B4470023
theorem B7946707 : Blo 2091435 7946707 := bstep (se 1 (by rfl) ⟨5960030, by rfl⟩ : syracuseStep 7946707 = 11920061) B11920061
theorem B10595609 : Blo 2091435 10595609 := bstep (se 2 (by rfl) ⟨3973353, by rfl⟩ : syracuseStep 10595609 = 7946707) B7946707
theorem B7063739 : Blo 2091435 7063739 := bstep (se 1 (by rfl) ⟨5297804, by rfl⟩ : syracuseStep 7063739 = 10595609) B10595609
theorem B4709159 : Blo 2091435 4709159 := bstep (se 1 (by rfl) ⟨3531869, by rfl⟩ : syracuseStep 4709159 = 7063739) B7063739
theorem B3139439 : Blo 2091435 3139439 := bstep (se 1 (by rfl) ⟨2354579, by rfl⟩ : syracuseStep 3139439 = 4709159) B4709159
theorem B2092959 : Blo 2091435 2092959 := bstep (se 1 (by rfl) ⟨1569719, by rfl⟩ : syracuseStep 2092959 = 3139439) B3139439
theorem B3139445 : Blo 2091435 3139445 := bbase (se 5 (by rfl) ⟨147161, by rfl⟩ : syracuseStep 3139445 = 294323) (by norm_num)
theorem B2092963 : Blo 2091435 2092963 := bstep (se 1 (by rfl) ⟨1569722, by rfl⟩ : syracuseStep 2092963 = 3139445) B3139445
theorem B5028797 : Blo 2091435 5028797 := bbase (se 3 (by rfl) ⟨942899, by rfl⟩ : syracuseStep 5028797 = 1885799) (by norm_num)
theorem B3352531 : Blo 2091435 3352531 := bstep (se 1 (by rfl) ⟨2514398, by rfl⟩ : syracuseStep 3352531 = 5028797) B5028797
theorem B4470041 : Blo 2091435 4470041 := bstep (se 2 (by rfl) ⟨1676265, by rfl⟩ : syracuseStep 4470041 = 3352531) B3352531
theorem B2980027 : Blo 2091435 2980027 := bstep (se 1 (by rfl) ⟨2235020, by rfl⟩ : syracuseStep 2980027 = 4470041) B4470041
theorem B3973369 : Blo 2091435 3973369 := bstep (se 2 (by rfl) ⟨1490013, by rfl⟩ : syracuseStep 3973369 = 2980027) B2980027
theorem B5297825 : Blo 2091435 5297825 := bstep (se 2 (by rfl) ⟨1986684, by rfl⟩ : syracuseStep 5297825 = 3973369) B3973369
theorem B3531883 : Blo 2091435 3531883 := bstep (se 1 (by rfl) ⟨2648912, by rfl⟩ : syracuseStep 3531883 = 5297825) B5297825
theorem B4709177 : Blo 2091435 4709177 := bstep (se 2 (by rfl) ⟨1765941, by rfl⟩ : syracuseStep 4709177 = 3531883) B3531883
theorem B3139451 : Blo 2091435 3139451 := bstep (se 1 (by rfl) ⟨2354588, by rfl⟩ : syracuseStep 3139451 = 4709177) B4709177
theorem B2092967 : Blo 2091435 2092967 := bstep (se 1 (by rfl) ⟨1569725, by rfl⟩ : syracuseStep 2092967 = 3139451) B3139451
theorem B2354593 : Blo 2091435 2354593 := bbase (se 2 (by rfl) ⟨882972, by rfl⟩ : syracuseStep 2354593 = 1765945) (by norm_num)
theorem B3139457 : Blo 2091435 3139457 := bstep (se 2 (by rfl) ⟨1177296, by rfl⟩ : syracuseStep 3139457 = 2354593) B2354593
theorem B2092971 : Blo 2091435 2092971 := bstep (se 1 (by rfl) ⟨1569728, by rfl⟩ : syracuseStep 2092971 = 3139457) B3139457
theorem B5297845 : Blo 2091435 5297845 := bbase (se 5 (by rfl) ⟨248336, by rfl⟩ : syracuseStep 5297845 = 496673) (by norm_num)
theorem B7063793 : Blo 2091435 7063793 := bstep (se 2 (by rfl) ⟨2648922, by rfl⟩ : syracuseStep 7063793 = 5297845) B5297845
theorem B4709195 : Blo 2091435 4709195 := bstep (se 1 (by rfl) ⟨3531896, by rfl⟩ : syracuseStep 4709195 = 7063793) B7063793
theorem B3139463 : Blo 2091435 3139463 := bstep (se 1 (by rfl) ⟨2354597, by rfl⟩ : syracuseStep 3139463 = 4709195) B4709195
theorem B2092975 : Blo 2091435 2092975 := bstep (se 1 (by rfl) ⟨1569731, by rfl⟩ : syracuseStep 2092975 = 3139463) B3139463
theorem B3139469 : Blo 2091435 3139469 := bbase (se 3 (by rfl) ⟨588650, by rfl⟩ : syracuseStep 3139469 = 1177301) (by norm_num)
theorem B2092979 : Blo 2091435 2092979 := bstep (se 1 (by rfl) ⟨1569734, by rfl⟩ : syracuseStep 2092979 = 3139469) B3139469
theorem B4709213 : Blo 2091435 4709213 := bbase (se 3 (by rfl) ⟨882977, by rfl⟩ : syracuseStep 4709213 = 1765955) (by norm_num)
theorem B3139475 : Blo 2091435 3139475 := bstep (se 1 (by rfl) ⟨2354606, by rfl⟩ : syracuseStep 3139475 = 4709213) B4709213
theorem B2092983 : Blo 2091435 2092983 := bstep (se 1 (by rfl) ⟨1569737, by rfl⟩ : syracuseStep 2092983 = 3139475) B3139475
theorem B3531917 : Blo 2091435 3531917 := bbase (se 3 (by rfl) ⟨662234, by rfl⟩ : syracuseStep 3531917 = 1324469) (by norm_num)
theorem B2354611 : Blo 2091435 2354611 := bstep (se 1 (by rfl) ⟨1765958, by rfl⟩ : syracuseStep 2354611 = 3531917) B3531917
theorem B3139481 : Blo 2091435 3139481 := bstep (se 2 (by rfl) ⟨1177305, by rfl⟩ : syracuseStep 3139481 = 2354611) B2354611
theorem B2092987 : Blo 2091435 2092987 := bstep (se 1 (by rfl) ⟨1569740, by rfl⟩ : syracuseStep 2092987 = 3139481) B3139481
theorem B5028853 : Blo 2091435 5028853 := bbase (se 5 (by rfl) ⟨235727, by rfl⟩ : syracuseStep 5028853 = 471455) (by norm_num)
theorem B6705137 : Blo 2091435 6705137 := bstep (se 2 (by rfl) ⟨2514426, by rfl⟩ : syracuseStep 6705137 = 5028853) B5028853
theorem B17880365 : Blo 2091435 17880365 := bstep (se 3 (by rfl) ⟨3352568, by rfl⟩ : syracuseStep 17880365 = 6705137) B6705137
theorem B11920243 : Blo 2091435 11920243 := bstep (se 1 (by rfl) ⟨8940182, by rfl⟩ : syracuseStep 11920243 = 17880365) B17880365
theorem B15893657 : Blo 2091435 15893657 := bstep (se 2 (by rfl) ⟨5960121, by rfl⟩ : syracuseStep 15893657 = 11920243) B11920243
theorem B10595771 : Blo 2091435 10595771 := bstep (se 1 (by rfl) ⟨7946828, by rfl⟩ : syracuseStep 10595771 = 15893657) B15893657
theorem B7063847 : Blo 2091435 7063847 := bstep (se 1 (by rfl) ⟨5297885, by rfl⟩ : syracuseStep 7063847 = 10595771) B10595771
theorem B4709231 : Blo 2091435 4709231 := bstep (se 1 (by rfl) ⟨3531923, by rfl⟩ : syracuseStep 4709231 = 7063847) B7063847
theorem B3139487 : Blo 2091435 3139487 := bstep (se 1 (by rfl) ⟨2354615, by rfl⟩ : syracuseStep 3139487 = 4709231) B4709231
theorem B2092991 : Blo 2091435 2092991 := bstep (se 1 (by rfl) ⟨1569743, by rfl⟩ : syracuseStep 2092991 = 3139487) B3139487
theorem B3139493 : Blo 2091435 3139493 := bbase (se 4 (by rfl) ⟨294327, by rfl⟩ : syracuseStep 3139493 = 588655) (by norm_num)
theorem B2092995 : Blo 2091435 2092995 := bstep (se 1 (by rfl) ⟨1569746, by rfl⟩ : syracuseStep 2092995 = 3139493) B3139493
theorem B2648953 : Blo 2091435 2648953 := bbase (se 2 (by rfl) ⟨993357, by rfl⟩ : syracuseStep 2648953 = 1986715) (by norm_num)
theorem B3531937 : Blo 2091435 3531937 := bstep (se 2 (by rfl) ⟨1324476, by rfl⟩ : syracuseStep 3531937 = 2648953) B2648953
theorem B4709249 : Blo 2091435 4709249 := bstep (se 2 (by rfl) ⟨1765968, by rfl⟩ : syracuseStep 4709249 = 3531937) B3531937
theorem B3139499 : Blo 2091435 3139499 := bstep (se 1 (by rfl) ⟨2354624, by rfl⟩ : syracuseStep 3139499 = 4709249) B4709249
theorem B2092999 : Blo 2091435 2092999 := bstep (se 1 (by rfl) ⟨1569749, by rfl⟩ : syracuseStep 2092999 = 3139499) B3139499
theorem B2354629 : Blo 2091435 2354629 := bbase (se 4 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 2354629 = 441493) (by norm_num)
theorem B3139505 : Blo 2091435 3139505 := bstep (se 2 (by rfl) ⟨1177314, by rfl⟩ : syracuseStep 3139505 = 2354629) B2354629
theorem B2093003 : Blo 2091435 2093003 := bstep (se 1 (by rfl) ⟨1569752, by rfl⟩ : syracuseStep 2093003 = 3139505) B3139505
theorem B3973445 : Blo 2091435 3973445 := bbase (se 4 (by rfl) ⟨372510, by rfl⟩ : syracuseStep 3973445 = 745021) (by norm_num)
theorem B2648963 : Blo 2091435 2648963 := bstep (se 1 (by rfl) ⟨1986722, by rfl⟩ : syracuseStep 2648963 = 3973445) B3973445
theorem B7063901 : Blo 2091435 7063901 := bstep (se 3 (by rfl) ⟨1324481, by rfl⟩ : syracuseStep 7063901 = 2648963) B2648963
theorem B4709267 : Blo 2091435 4709267 := bstep (se 1 (by rfl) ⟨3531950, by rfl⟩ : syracuseStep 4709267 = 7063901) B7063901
theorem B3139511 : Blo 2091435 3139511 := bstep (se 1 (by rfl) ⟨2354633, by rfl⟩ : syracuseStep 3139511 = 4709267) B4709267
theorem B2093007 : Blo 2091435 2093007 := bstep (se 1 (by rfl) ⟨1569755, by rfl⟩ : syracuseStep 2093007 = 3139511) B3139511
theorem B3139517 : Blo 2091435 3139517 := bbase (se 3 (by rfl) ⟨588659, by rfl⟩ : syracuseStep 3139517 = 1177319) (by norm_num)
theorem B2093011 : Blo 2091435 2093011 := bstep (se 1 (by rfl) ⟨1569758, by rfl⟩ : syracuseStep 2093011 = 3139517) B3139517
theorem B4709285 : Blo 2091435 4709285 := bbase (se 4 (by rfl) ⟨441495, by rfl⟩ : syracuseStep 4709285 = 882991) (by norm_num)
theorem B3139523 : Blo 2091435 3139523 := bstep (se 1 (by rfl) ⟨2354642, by rfl⟩ : syracuseStep 3139523 = 4709285) B4709285
theorem B2093015 : Blo 2091435 2093015 := bstep (se 1 (by rfl) ⟨1569761, by rfl⟩ : syracuseStep 2093015 = 3139523) B3139523
theorem B5297957 : Blo 2091435 5297957 := bbase (se 4 (by rfl) ⟨496683, by rfl⟩ : syracuseStep 5297957 = 993367) (by norm_num)
theorem B3531971 : Blo 2091435 3531971 := bstep (se 1 (by rfl) ⟨2648978, by rfl⟩ : syracuseStep 3531971 = 5297957) B5297957
theorem B2354647 : Blo 2091435 2354647 := bstep (se 1 (by rfl) ⟨1765985, by rfl⟩ : syracuseStep 2354647 = 3531971) B3531971
theorem B3139529 : Blo 2091435 3139529 := bstep (se 2 (by rfl) ⟨1177323, by rfl⟩ : syracuseStep 3139529 = 2354647) B2354647
theorem B2093019 : Blo 2091435 2093019 := bstep (se 1 (by rfl) ⟨1569764, by rfl⟩ : syracuseStep 2093019 = 3139529) B3139529
theorem B5960213 : Blo 2091435 5960213 := bbase (se 6 (by rfl) ⟨139692, by rfl⟩ : syracuseStep 5960213 = 279385) (by norm_num)
theorem B3973475 : Blo 2091435 3973475 := bstep (se 1 (by rfl) ⟨2980106, by rfl⟩ : syracuseStep 3973475 = 5960213) B5960213
theorem B10595933 : Blo 2091435 10595933 := bstep (se 3 (by rfl) ⟨1986737, by rfl⟩ : syracuseStep 10595933 = 3973475) B3973475
theorem B7063955 : Blo 2091435 7063955 := bstep (se 1 (by rfl) ⟨5297966, by rfl⟩ : syracuseStep 7063955 = 10595933) B10595933
theorem B4709303 : Blo 2091435 4709303 := bstep (se 1 (by rfl) ⟨3531977, by rfl⟩ : syracuseStep 4709303 = 7063955) B7063955
theorem B3139535 : Blo 2091435 3139535 := bstep (se 1 (by rfl) ⟨2354651, by rfl⟩ : syracuseStep 3139535 = 4709303) B4709303
theorem B2093023 : Blo 2091435 2093023 := bstep (se 1 (by rfl) ⟨1569767, by rfl⟩ : syracuseStep 2093023 = 3139535) B3139535
theorem B3139541 : Blo 2091435 3139541 := bbase (se 7 (by rfl) ⟨36791, by rfl⟩ : syracuseStep 3139541 = 73583) (by norm_num)
theorem B2093027 : Blo 2091435 2093027 := bstep (se 1 (by rfl) ⟨1569770, by rfl⟩ : syracuseStep 2093027 = 3139541) B3139541
theorem B7946981 : Blo 2091435 7946981 := bbase (se 4 (by rfl) ⟨745029, by rfl⟩ : syracuseStep 7946981 = 1490059) (by norm_num)
theorem B5297987 : Blo 2091435 5297987 := bstep (se 1 (by rfl) ⟨3973490, by rfl⟩ : syracuseStep 5297987 = 7946981) B7946981
theorem B3531991 : Blo 2091435 3531991 := bstep (se 1 (by rfl) ⟨2648993, by rfl⟩ : syracuseStep 3531991 = 5297987) B5297987
theorem B4709321 : Blo 2091435 4709321 := bstep (se 2 (by rfl) ⟨1765995, by rfl⟩ : syracuseStep 4709321 = 3531991) B3531991
theorem B3139547 : Blo 2091435 3139547 := bstep (se 1 (by rfl) ⟨2354660, by rfl⟩ : syracuseStep 3139547 = 4709321) B4709321
theorem B2093031 : Blo 2091435 2093031 := bstep (se 1 (by rfl) ⟨1569773, by rfl⟩ : syracuseStep 2093031 = 3139547) B3139547
theorem B2354665 : Blo 2091435 2354665 := bbase (se 2 (by rfl) ⟨882999, by rfl⟩ : syracuseStep 2354665 = 1765999) (by norm_num)
theorem B3139553 : Blo 2091435 3139553 := bstep (se 2 (by rfl) ⟨1177332, by rfl⟩ : syracuseStep 3139553 = 2354665) B2354665
theorem B2093035 : Blo 2091435 2093035 := bstep (se 1 (by rfl) ⟨1569776, by rfl⟩ : syracuseStep 2093035 = 3139553) B3139553
theorem B2235097 : Blo 2091435 2235097 := bbase (se 2 (by rfl) ⟨838161, by rfl⟩ : syracuseStep 2235097 = 1676323) (by norm_num)
theorem B11920517 : Blo 2091435 11920517 := bstep (se 4 (by rfl) ⟨1117548, by rfl⟩ : syracuseStep 11920517 = 2235097) B2235097
theorem B7947011 : Blo 2091435 7947011 := bstep (se 1 (by rfl) ⟨5960258, by rfl⟩ : syracuseStep 7947011 = 11920517) B11920517
theorem B5298007 : Blo 2091435 5298007 := bstep (se 1 (by rfl) ⟨3973505, by rfl⟩ : syracuseStep 5298007 = 7947011) B7947011
theorem B7064009 : Blo 2091435 7064009 := bstep (se 2 (by rfl) ⟨2649003, by rfl⟩ : syracuseStep 7064009 = 5298007) B5298007
theorem B4709339 : Blo 2091435 4709339 := bstep (se 1 (by rfl) ⟨3532004, by rfl⟩ : syracuseStep 4709339 = 7064009) B7064009
theorem B3139559 : Blo 2091435 3139559 := bstep (se 1 (by rfl) ⟨2354669, by rfl⟩ : syracuseStep 3139559 = 4709339) B4709339
theorem B2093039 : Blo 2091435 2093039 := bstep (se 1 (by rfl) ⟨1569779, by rfl⟩ : syracuseStep 2093039 = 3139559) B3139559
theorem B3139565 : Blo 2091435 3139565 := bbase (se 3 (by rfl) ⟨588668, by rfl⟩ : syracuseStep 3139565 = 1177337) (by norm_num)
theorem B2093043 : Blo 2091435 2093043 := bstep (se 1 (by rfl) ⟨1569782, by rfl⟩ : syracuseStep 2093043 = 3139565) B3139565
theorem B4709357 : Blo 2091435 4709357 := bbase (se 3 (by rfl) ⟨883004, by rfl⟩ : syracuseStep 4709357 = 1766009) (by norm_num)
theorem B3139571 : Blo 2091435 3139571 := bstep (se 1 (by rfl) ⟨2354678, by rfl⟩ : syracuseStep 3139571 = 4709357) B4709357
theorem B2093047 : Blo 2091435 2093047 := bstep (se 1 (by rfl) ⟨1569785, by rfl⟩ : syracuseStep 2093047 = 3139571) B3139571
theorem B4470221 : Blo 2091435 4470221 := bbase (se 3 (by rfl) ⟨838166, by rfl⟩ : syracuseStep 4470221 = 1676333) (by norm_num)
theorem B2980147 : Blo 2091435 2980147 := bstep (se 1 (by rfl) ⟨2235110, by rfl⟩ : syracuseStep 2980147 = 4470221) B4470221
theorem B3973529 : Blo 2091435 3973529 := bstep (se 2 (by rfl) ⟨1490073, by rfl⟩ : syracuseStep 3973529 = 2980147) B2980147
theorem B2649019 : Blo 2091435 2649019 := bstep (se 1 (by rfl) ⟨1986764, by rfl⟩ : syracuseStep 2649019 = 3973529) B3973529
theorem B3532025 : Blo 2091435 3532025 := bstep (se 2 (by rfl) ⟨1324509, by rfl⟩ : syracuseStep 3532025 = 2649019) B2649019
theorem B2354683 : Blo 2091435 2354683 := bstep (se 1 (by rfl) ⟨1766012, by rfl⟩ : syracuseStep 2354683 = 3532025) B3532025
theorem B3139577 : Blo 2091435 3139577 := bstep (se 2 (by rfl) ⟨1177341, by rfl⟩ : syracuseStep 3139577 = 2354683) B2354683
theorem B2093051 : Blo 2091435 2093051 := bstep (se 1 (by rfl) ⟨1569788, by rfl⟩ : syracuseStep 2093051 = 3139577) B3139577
theorem B69756757 : Blo 2091435 69756757 := bbase (se 9 (by rfl) ⟨204365, by rfl⟩ : syracuseStep 69756757 = 408731) (by norm_num)
theorem B372036037 : Blo 2091435 372036037 := bstep (se 4 (by rfl) ⟨34878378, by rfl⟩ : syracuseStep 372036037 = 69756757) B69756757
theorem B496048049 : Blo 2091435 496048049 := bstep (se 2 (by rfl) ⟨186018018, by rfl⟩ : syracuseStep 496048049 = 372036037) B372036037
theorem B330698699 : Blo 2091435 330698699 := bstep (se 1 (by rfl) ⟨248024024, by rfl⟩ : syracuseStep 330698699 = 496048049) B496048049
theorem B220465799 : Blo 2091435 220465799 := bstep (se 1 (by rfl) ⟨165349349, by rfl⟩ : syracuseStep 220465799 = 330698699) B330698699
theorem B146977199 : Blo 2091435 146977199 := bstep (se 1 (by rfl) ⟨110232899, by rfl⟩ : syracuseStep 146977199 = 220465799) B220465799
theorem B97984799 : Blo 2091435 97984799 := bstep (se 1 (by rfl) ⟨73488599, by rfl⟩ : syracuseStep 97984799 = 146977199) B146977199
theorem B65323199 : Blo 2091435 65323199 := bstep (se 1 (by rfl) ⟨48992399, by rfl⟩ : syracuseStep 65323199 = 97984799) B97984799
theorem B43548799 : Blo 2091435 43548799 := bstep (se 1 (by rfl) ⟨32661599, by rfl⟩ : syracuseStep 43548799 = 65323199) B65323199
theorem B58065065 : Blo 2091435 58065065 := bstep (se 2 (by rfl) ⟨21774399, by rfl⟩ : syracuseStep 58065065 = 43548799) B43548799
theorem B38710043 : Blo 2091435 38710043 := bstep (se 1 (by rfl) ⟨29032532, by rfl⟩ : syracuseStep 38710043 = 58065065) B58065065
theorem B25806695 : Blo 2091435 25806695 := bstep (se 1 (by rfl) ⟨19355021, by rfl⟩ : syracuseStep 25806695 = 38710043) B38710043
theorem B68817853 : Blo 2091435 68817853 := bstep (se 3 (by rfl) ⟨12903347, by rfl⟩ : syracuseStep 68817853 = 25806695) B25806695
theorem B91757137 : Blo 2091435 91757137 := bstep (se 2 (by rfl) ⟨34408926, by rfl⟩ : syracuseStep 91757137 = 68817853) B68817853
theorem B122342849 : Blo 2091435 122342849 := bstep (se 2 (by rfl) ⟨45878568, by rfl⟩ : syracuseStep 122342849 = 91757137) B91757137
theorem B81561899 : Blo 2091435 81561899 := bstep (se 1 (by rfl) ⟨61171424, by rfl⟩ : syracuseStep 81561899 = 122342849) B122342849
theorem B54374599 : Blo 2091435 54374599 := bstep (se 1 (by rfl) ⟨40780949, by rfl⟩ : syracuseStep 54374599 = 81561899) B81561899
theorem B72499465 : Blo 2091435 72499465 := bstep (se 2 (by rfl) ⟨27187299, by rfl⟩ : syracuseStep 72499465 = 54374599) B54374599
theorem B96665953 : Blo 2091435 96665953 := bstep (se 2 (by rfl) ⟨36249732, by rfl⟩ : syracuseStep 96665953 = 72499465) B72499465
theorem B128887937 : Blo 2091435 128887937 := bstep (se 2 (by rfl) ⟨48332976, by rfl⟩ : syracuseStep 128887937 = 96665953) B96665953
theorem B85925291 : Blo 2091435 85925291 := bstep (se 1 (by rfl) ⟨64443968, by rfl⟩ : syracuseStep 85925291 = 128887937) B128887937
theorem B229134109 : Blo 2091435 229134109 := bstep (se 3 (by rfl) ⟨42962645, by rfl⟩ : syracuseStep 229134109 = 85925291) B85925291
theorem B305512145 : Blo 2091435 305512145 := bstep (se 2 (by rfl) ⟨114567054, by rfl⟩ : syracuseStep 305512145 = 229134109) B229134109
theorem B203674763 : Blo 2091435 203674763 := bstep (se 1 (by rfl) ⟨152756072, by rfl⟩ : syracuseStep 203674763 = 305512145) B305512145
theorem B135783175 : Blo 2091435 135783175 := bstep (se 1 (by rfl) ⟨101837381, by rfl⟩ : syracuseStep 135783175 = 203674763) B203674763
theorem B181044233 : Blo 2091435 181044233 := bstep (se 2 (by rfl) ⟨67891587, by rfl⟩ : syracuseStep 181044233 = 135783175) B135783175
theorem B120696155 : Blo 2091435 120696155 := bstep (se 1 (by rfl) ⟨90522116, by rfl⟩ : syracuseStep 120696155 = 181044233) B181044233
theorem B80464103 : Blo 2091435 80464103 := bstep (se 1 (by rfl) ⟨60348077, by rfl⟩ : syracuseStep 80464103 = 120696155) B120696155
theorem B53642735 : Blo 2091435 53642735 := bstep (se 1 (by rfl) ⟨40232051, by rfl⟩ : syracuseStep 53642735 = 80464103) B80464103
theorem B35761823 : Blo 2091435 35761823 := bstep (se 1 (by rfl) ⟨26821367, by rfl⟩ : syracuseStep 35761823 = 53642735) B53642735
theorem B23841215 : Blo 2091435 23841215 := bstep (se 1 (by rfl) ⟨17880911, by rfl⟩ : syracuseStep 23841215 = 35761823) B35761823
theorem B15894143 : Blo 2091435 15894143 := bstep (se 1 (by rfl) ⟨11920607, by rfl⟩ : syracuseStep 15894143 = 23841215) B23841215
theorem B10596095 : Blo 2091435 10596095 := bstep (se 1 (by rfl) ⟨7947071, by rfl⟩ : syracuseStep 10596095 = 15894143) B15894143
theorem B7064063 : Blo 2091435 7064063 := bstep (se 1 (by rfl) ⟨5298047, by rfl⟩ : syracuseStep 7064063 = 10596095) B10596095
theorem B4709375 : Blo 2091435 4709375 := bstep (se 1 (by rfl) ⟨3532031, by rfl⟩ : syracuseStep 4709375 = 7064063) B7064063
theorem B3139583 : Blo 2091435 3139583 := bstep (se 1 (by rfl) ⟨2354687, by rfl⟩ : syracuseStep 3139583 = 4709375) B4709375
theorem B2093055 : Blo 2091435 2093055 := bstep (se 1 (by rfl) ⟨1569791, by rfl⟩ : syracuseStep 2093055 = 3139583) B3139583
theorem B3139589 : Blo 2091435 3139589 := bbase (se 4 (by rfl) ⟨294336, by rfl⟩ : syracuseStep 3139589 = 588673) (by norm_num)
theorem B2093059 : Blo 2091435 2093059 := bstep (se 1 (by rfl) ⟨1569794, by rfl⟩ : syracuseStep 2093059 = 3139589) B3139589
theorem B3532045 : Blo 2091435 3532045 := bbase (se 3 (by rfl) ⟨662258, by rfl⟩ : syracuseStep 3532045 = 1324517) (by norm_num)
theorem B4709393 : Blo 2091435 4709393 := bstep (se 2 (by rfl) ⟨1766022, by rfl⟩ : syracuseStep 4709393 = 3532045) B3532045
theorem B3139595 : Blo 2091435 3139595 := bstep (se 1 (by rfl) ⟨2354696, by rfl⟩ : syracuseStep 3139595 = 4709393) B4709393
theorem B2093063 : Blo 2091435 2093063 := bstep (se 1 (by rfl) ⟨1569797, by rfl⟩ : syracuseStep 2093063 = 3139595) B3139595
theorem B2354701 : Blo 2091435 2354701 := bbase (se 3 (by rfl) ⟨441506, by rfl⟩ : syracuseStep 2354701 = 883013) (by norm_num)
theorem B3139601 : Blo 2091435 3139601 := bstep (se 2 (by rfl) ⟨1177350, by rfl⟩ : syracuseStep 3139601 = 2354701) B2354701
theorem B2093067 : Blo 2091435 2093067 := bstep (se 1 (by rfl) ⟨1569800, by rfl⟩ : syracuseStep 2093067 = 3139601) B3139601
theorem B7064117 : Blo 2091435 7064117 := bbase (se 5 (by rfl) ⟨331130, by rfl⟩ : syracuseStep 7064117 = 662261) (by norm_num)
theorem B4709411 : Blo 2091435 4709411 := bstep (se 1 (by rfl) ⟨3532058, by rfl⟩ : syracuseStep 4709411 = 7064117) B7064117
theorem B3139607 : Blo 2091435 3139607 := bstep (se 1 (by rfl) ⟨2354705, by rfl⟩ : syracuseStep 3139607 = 4709411) B4709411
theorem B2093071 : Blo 2091435 2093071 := bstep (se 1 (by rfl) ⟨1569803, by rfl⟩ : syracuseStep 2093071 = 3139607) B3139607
theorem B3139613 : Blo 2091435 3139613 := bbase (se 3 (by rfl) ⟨588677, by rfl⟩ : syracuseStep 3139613 = 1177355) (by norm_num)
theorem B2093075 : Blo 2091435 2093075 := bstep (se 1 (by rfl) ⟨1569806, by rfl⟩ : syracuseStep 2093075 = 3139613) B3139613
theorem B4709429 : Blo 2091435 4709429 := bbase (se 5 (by rfl) ⟨220754, by rfl⟩ : syracuseStep 4709429 = 441509) (by norm_num)
theorem B3139619 : Blo 2091435 3139619 := bstep (se 1 (by rfl) ⟨2354714, by rfl⟩ : syracuseStep 3139619 = 4709429) B4709429
theorem B2093079 : Blo 2091435 2093079 := bstep (se 1 (by rfl) ⟨1569809, by rfl⟩ : syracuseStep 2093079 = 3139619) B3139619
theorem B13593845 : Blo 2091435 13593845 := bbase (se 5 (by rfl) ⟨637211, by rfl⟩ : syracuseStep 13593845 = 1274423) (by norm_num)
theorem B9062563 : Blo 2091435 9062563 := bstep (se 1 (by rfl) ⟨6796922, by rfl⟩ : syracuseStep 9062563 = 13593845) B13593845
theorem B12083417 : Blo 2091435 12083417 := bstep (se 2 (by rfl) ⟨4531281, by rfl⟩ : syracuseStep 12083417 = 9062563) B9062563
theorem B8055611 : Blo 2091435 8055611 := bstep (se 1 (by rfl) ⟨6041708, by rfl⟩ : syracuseStep 8055611 = 12083417) B12083417
theorem B5370407 : Blo 2091435 5370407 := bstep (se 1 (by rfl) ⟨4027805, by rfl⟩ : syracuseStep 5370407 = 8055611) B8055611
theorem B3580271 : Blo 2091435 3580271 := bstep (se 1 (by rfl) ⟨2685203, by rfl⟩ : syracuseStep 3580271 = 5370407) B5370407
theorem B2386847 : Blo 2091435 2386847 := bstep (se 1 (by rfl) ⟨1790135, by rfl⟩ : syracuseStep 2386847 = 3580271) B3580271
theorem B6364925 : Blo 2091435 6364925 := bstep (se 3 (by rfl) ⟨1193423, by rfl⟩ : syracuseStep 6364925 = 2386847) B2386847
theorem B4243283 : Blo 2091435 4243283 := bstep (se 1 (by rfl) ⟨3182462, by rfl⟩ : syracuseStep 4243283 = 6364925) B6364925
theorem B2828855 : Blo 2091435 2828855 := bstep (se 1 (by rfl) ⟨2121641, by rfl⟩ : syracuseStep 2828855 = 4243283) B4243283
theorem B7543613 : Blo 2091435 7543613 := bstep (se 3 (by rfl) ⟨1414427, by rfl⟩ : syracuseStep 7543613 = 2828855) B2828855
theorem B5029075 : Blo 2091435 5029075 := bstep (se 1 (by rfl) ⟨3771806, by rfl⟩ : syracuseStep 5029075 = 7543613) B7543613
theorem B6705433 : Blo 2091435 6705433 := bstep (se 2 (by rfl) ⟨2514537, by rfl⟩ : syracuseStep 6705433 = 5029075) B5029075
theorem B8940577 : Blo 2091435 8940577 := bstep (se 2 (by rfl) ⟨3352716, by rfl⟩ : syracuseStep 8940577 = 6705433) B6705433
theorem B11920769 : Blo 2091435 11920769 := bstep (se 2 (by rfl) ⟨4470288, by rfl⟩ : syracuseStep 11920769 = 8940577) B8940577
theorem B7947179 : Blo 2091435 7947179 := bstep (se 1 (by rfl) ⟨5960384, by rfl⟩ : syracuseStep 7947179 = 11920769) B11920769
theorem B5298119 : Blo 2091435 5298119 := bstep (se 1 (by rfl) ⟨3973589, by rfl⟩ : syracuseStep 5298119 = 7947179) B7947179
theorem B3532079 : Blo 2091435 3532079 := bstep (se 1 (by rfl) ⟨2649059, by rfl⟩ : syracuseStep 3532079 = 5298119) B5298119
theorem B2354719 : Blo 2091435 2354719 := bstep (se 1 (by rfl) ⟨1766039, by rfl⟩ : syracuseStep 2354719 = 3532079) B3532079
theorem B3139625 : Blo 2091435 3139625 := bstep (se 2 (by rfl) ⟨1177359, by rfl⟩ : syracuseStep 3139625 = 2354719) B2354719
theorem B2093083 : Blo 2091435 2093083 := bstep (se 1 (by rfl) ⟨1569812, by rfl⟩ : syracuseStep 2093083 = 3139625) B3139625
theorem B6705445 : Blo 2091435 6705445 := bbase (se 4 (by rfl) ⟨628635, by rfl⟩ : syracuseStep 6705445 = 1257271) (by norm_num)
theorem B8940593 : Blo 2091435 8940593 := bstep (se 2 (by rfl) ⟨3352722, by rfl⟩ : syracuseStep 8940593 = 6705445) B6705445
theorem B5960395 : Blo 2091435 5960395 := bstep (se 1 (by rfl) ⟨4470296, by rfl⟩ : syracuseStep 5960395 = 8940593) B8940593
theorem B7947193 : Blo 2091435 7947193 := bstep (se 2 (by rfl) ⟨2980197, by rfl⟩ : syracuseStep 7947193 = 5960395) B5960395
theorem B10596257 : Blo 2091435 10596257 := bstep (se 2 (by rfl) ⟨3973596, by rfl⟩ : syracuseStep 10596257 = 7947193) B7947193
theorem B7064171 : Blo 2091435 7064171 := bstep (se 1 (by rfl) ⟨5298128, by rfl⟩ : syracuseStep 7064171 = 10596257) B10596257
theorem B4709447 : Blo 2091435 4709447 := bstep (se 1 (by rfl) ⟨3532085, by rfl⟩ : syracuseStep 4709447 = 7064171) B7064171
theorem B3139631 : Blo 2091435 3139631 := bstep (se 1 (by rfl) ⟨2354723, by rfl⟩ : syracuseStep 3139631 = 4709447) B4709447
theorem B2093087 : Blo 2091435 2093087 := bstep (se 1 (by rfl) ⟨1569815, by rfl⟩ : syracuseStep 2093087 = 3139631) B3139631
theorem B3139637 : Blo 2091435 3139637 := bbase (se 5 (by rfl) ⟨147170, by rfl⟩ : syracuseStep 3139637 = 294341) (by norm_num)
theorem B2093091 : Blo 2091435 2093091 := bstep (se 1 (by rfl) ⟨1569818, by rfl⟩ : syracuseStep 2093091 = 3139637) B3139637
theorem B5298149 : Blo 2091435 5298149 := bbase (se 4 (by rfl) ⟨496701, by rfl⟩ : syracuseStep 5298149 = 993403) (by norm_num)
theorem B3532099 : Blo 2091435 3532099 := bstep (se 1 (by rfl) ⟨2649074, by rfl⟩ : syracuseStep 3532099 = 5298149) B5298149
theorem B4709465 : Blo 2091435 4709465 := bstep (se 2 (by rfl) ⟨1766049, by rfl⟩ : syracuseStep 4709465 = 3532099) B3532099
theorem B3139643 : Blo 2091435 3139643 := bstep (se 1 (by rfl) ⟨2354732, by rfl⟩ : syracuseStep 3139643 = 4709465) B4709465
theorem B2093095 : Blo 2091435 2093095 := bstep (se 1 (by rfl) ⟨1569821, by rfl⟩ : syracuseStep 2093095 = 3139643) B3139643
theorem B2354737 : Blo 2091435 2354737 := bbase (se 2 (by rfl) ⟨883026, by rfl⟩ : syracuseStep 2354737 = 1766053) (by norm_num)
theorem B3139649 : Blo 2091435 3139649 := bstep (se 2 (by rfl) ⟨1177368, by rfl⟩ : syracuseStep 3139649 = 2354737) B2354737
theorem B2093099 : Blo 2091435 2093099 := bstep (se 1 (by rfl) ⟨1569824, by rfl⟩ : syracuseStep 2093099 = 3139649) B3139649
theorem B7543685 : Blo 2091435 7543685 := bbase (se 4 (by rfl) ⟨707220, by rfl⟩ : syracuseStep 7543685 = 1414441) (by norm_num)
theorem B5029123 : Blo 2091435 5029123 := bstep (se 1 (by rfl) ⟨3771842, by rfl⟩ : syracuseStep 5029123 = 7543685) B7543685
theorem B6705497 : Blo 2091435 6705497 := bstep (se 2 (by rfl) ⟨2514561, by rfl⟩ : syracuseStep 6705497 = 5029123) B5029123
theorem B4470331 : Blo 2091435 4470331 := bstep (se 1 (by rfl) ⟨3352748, by rfl⟩ : syracuseStep 4470331 = 6705497) B6705497
theorem B5960441 : Blo 2091435 5960441 := bstep (se 2 (by rfl) ⟨2235165, by rfl⟩ : syracuseStep 5960441 = 4470331) B4470331
theorem B3973627 : Blo 2091435 3973627 := bstep (se 1 (by rfl) ⟨2980220, by rfl⟩ : syracuseStep 3973627 = 5960441) B5960441
theorem B5298169 : Blo 2091435 5298169 := bstep (se 2 (by rfl) ⟨1986813, by rfl⟩ : syracuseStep 5298169 = 3973627) B3973627
theorem B7064225 : Blo 2091435 7064225 := bstep (se 2 (by rfl) ⟨2649084, by rfl⟩ : syracuseStep 7064225 = 5298169) B5298169
theorem B4709483 : Blo 2091435 4709483 := bstep (se 1 (by rfl) ⟨3532112, by rfl⟩ : syracuseStep 4709483 = 7064225) B7064225
theorem B3139655 : Blo 2091435 3139655 := bstep (se 1 (by rfl) ⟨2354741, by rfl⟩ : syracuseStep 3139655 = 4709483) B4709483
theorem B2093103 : Blo 2091435 2093103 := bstep (se 1 (by rfl) ⟨1569827, by rfl⟩ : syracuseStep 2093103 = 3139655) B3139655
theorem B3139661 : Blo 2091435 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B2093107 : Blo 2091435 2093107 := bstep (se 1 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 2093107 = 3139661) B3139661
theorem B4709501 : Blo 2091435 4709501 := bbase (se 3 (by rfl) ⟨883031, by rfl⟩ : syracuseStep 4709501 = 1766063) (by norm_num)
theorem B3139667 : Blo 2091435 3139667 := bstep (se 1 (by rfl) ⟨2354750, by rfl⟩ : syracuseStep 3139667 = 4709501) B4709501
theorem B2093111 : Blo 2091435 2093111 := bstep (se 1 (by rfl) ⟨1569833, by rfl⟩ : syracuseStep 2093111 = 3139667) B3139667
theorem B3532133 : Blo 2091435 3532133 := bbase (se 4 (by rfl) ⟨331137, by rfl⟩ : syracuseStep 3532133 = 662275) (by norm_num)
theorem B2354755 : Blo 2091435 2354755 := bstep (se 1 (by rfl) ⟨1766066, by rfl⟩ : syracuseStep 2354755 = 3532133) B3532133
theorem B3139673 : Blo 2091435 3139673 := bstep (se 2 (by rfl) ⟨1177377, by rfl⟩ : syracuseStep 3139673 = 2354755) B2354755
theorem B2093115 : Blo 2091435 2093115 := bstep (se 1 (by rfl) ⟨1569836, by rfl⟩ : syracuseStep 2093115 = 3139673) B3139673
theorem B4470365 : Blo 2091435 4470365 := bbase (se 3 (by rfl) ⟨838193, by rfl⟩ : syracuseStep 4470365 = 1676387) (by norm_num)
theorem B2980243 : Blo 2091435 2980243 := bstep (se 1 (by rfl) ⟨2235182, by rfl⟩ : syracuseStep 2980243 = 4470365) B4470365
theorem B15894629 : Blo 2091435 15894629 := bstep (se 4 (by rfl) ⟨1490121, by rfl⟩ : syracuseStep 15894629 = 2980243) B2980243
theorem B10596419 : Blo 2091435 10596419 := bstep (se 1 (by rfl) ⟨7947314, by rfl⟩ : syracuseStep 10596419 = 15894629) B15894629
theorem B7064279 : Blo 2091435 7064279 := bstep (se 1 (by rfl) ⟨5298209, by rfl⟩ : syracuseStep 7064279 = 10596419) B10596419
theorem B4709519 : Blo 2091435 4709519 := bstep (se 1 (by rfl) ⟨3532139, by rfl⟩ : syracuseStep 4709519 = 7064279) B7064279
theorem B3139679 : Blo 2091435 3139679 := bstep (se 1 (by rfl) ⟨2354759, by rfl⟩ : syracuseStep 3139679 = 4709519) B4709519
theorem B2093119 : Blo 2091435 2093119 := bstep (se 1 (by rfl) ⟨1569839, by rfl⟩ : syracuseStep 2093119 = 3139679) B3139679
theorem B3139685 : Blo 2091435 3139685 := bbase (se 4 (by rfl) ⟨294345, by rfl⟩ : syracuseStep 3139685 = 588691) (by norm_num)
theorem B2093123 : Blo 2091435 2093123 := bstep (se 1 (by rfl) ⟨1569842, by rfl⟩ : syracuseStep 2093123 = 3139685) B3139685
theorem B2386897 : Blo 2091435 2386897 := bbase (se 2 (by rfl) ⟨895086, by rfl⟩ : syracuseStep 2386897 = 1790173) (by norm_num)
theorem B12730117 : Blo 2091435 12730117 := bstep (se 4 (by rfl) ⟨1193448, by rfl⟩ : syracuseStep 12730117 = 2386897) B2386897
theorem B16973489 : Blo 2091435 16973489 := bstep (se 2 (by rfl) ⟨6365058, by rfl⟩ : syracuseStep 16973489 = 12730117) B12730117
theorem B11315659 : Blo 2091435 11315659 := bstep (se 1 (by rfl) ⟨8486744, by rfl⟩ : syracuseStep 11315659 = 16973489) B16973489
theorem B15087545 : Blo 2091435 15087545 := bstep (se 2 (by rfl) ⟨5657829, by rfl⟩ : syracuseStep 15087545 = 11315659) B11315659
theorem B10058363 : Blo 2091435 10058363 := bstep (se 1 (by rfl) ⟨7543772, by rfl⟩ : syracuseStep 10058363 = 15087545) B15087545
theorem B6705575 : Blo 2091435 6705575 := bstep (se 1 (by rfl) ⟨5029181, by rfl⟩ : syracuseStep 6705575 = 10058363) B10058363
theorem B4470383 : Blo 2091435 4470383 := bstep (se 1 (by rfl) ⟨3352787, by rfl⟩ : syracuseStep 4470383 = 6705575) B6705575
theorem B2980255 : Blo 2091435 2980255 := bstep (se 1 (by rfl) ⟨2235191, by rfl⟩ : syracuseStep 2980255 = 4470383) B4470383
theorem B3973673 : Blo 2091435 3973673 := bstep (se 2 (by rfl) ⟨1490127, by rfl⟩ : syracuseStep 3973673 = 2980255) B2980255
theorem B2649115 : Blo 2091435 2649115 := bstep (se 1 (by rfl) ⟨1986836, by rfl⟩ : syracuseStep 2649115 = 3973673) B3973673
theorem B3532153 : Blo 2091435 3532153 := bstep (se 2 (by rfl) ⟨1324557, by rfl⟩ : syracuseStep 3532153 = 2649115) B2649115
theorem B4709537 : Blo 2091435 4709537 := bstep (se 2 (by rfl) ⟨1766076, by rfl⟩ : syracuseStep 4709537 = 3532153) B3532153
theorem B3139691 : Blo 2091435 3139691 := bstep (se 1 (by rfl) ⟨2354768, by rfl⟩ : syracuseStep 3139691 = 4709537) B4709537
theorem B2093127 : Blo 2091435 2093127 := bstep (se 1 (by rfl) ⟨1569845, by rfl⟩ : syracuseStep 2093127 = 3139691) B3139691
theorem B2354773 : Blo 2091435 2354773 := bbase (se 8 (by rfl) ⟨13797, by rfl⟩ : syracuseStep 2354773 = 27595) (by norm_num)
theorem B3139697 : Blo 2091435 3139697 := bstep (se 2 (by rfl) ⟨1177386, by rfl⟩ : syracuseStep 3139697 = 2354773) B2354773
theorem B2093131 : Blo 2091435 2093131 := bstep (se 1 (by rfl) ⟨1569848, by rfl⟩ : syracuseStep 2093131 = 3139697) B3139697
theorem B2649125 : Blo 2091435 2649125 := bbase (se 4 (by rfl) ⟨248355, by rfl⟩ : syracuseStep 2649125 = 496711) (by norm_num)
theorem B7064333 : Blo 2091435 7064333 := bstep (se 3 (by rfl) ⟨1324562, by rfl⟩ : syracuseStep 7064333 = 2649125) B2649125
theorem B4709555 : Blo 2091435 4709555 := bstep (se 1 (by rfl) ⟨3532166, by rfl⟩ : syracuseStep 4709555 = 7064333) B7064333
theorem B3139703 : Blo 2091435 3139703 := bstep (se 1 (by rfl) ⟨2354777, by rfl⟩ : syracuseStep 3139703 = 4709555) B4709555
theorem B2093135 : Blo 2091435 2093135 := bstep (se 1 (by rfl) ⟨1569851, by rfl⟩ : syracuseStep 2093135 = 3139703) B3139703
theorem B3139709 : Blo 2091435 3139709 := bbase (se 3 (by rfl) ⟨588695, by rfl⟩ : syracuseStep 3139709 = 1177391) (by norm_num)
theorem B2093139 : Blo 2091435 2093139 := bstep (se 1 (by rfl) ⟨1569854, by rfl⟩ : syracuseStep 2093139 = 3139709) B3139709
theorem B4709573 : Blo 2091435 4709573 := bbase (se 4 (by rfl) ⟨441522, by rfl⟩ : syracuseStep 4709573 = 883045) (by norm_num)
theorem B3139715 : Blo 2091435 3139715 := bstep (se 1 (by rfl) ⟨2354786, by rfl⟩ : syracuseStep 3139715 = 4709573) B4709573
theorem B2093143 : Blo 2091435 2093143 := bstep (se 1 (by rfl) ⟨1569857, by rfl⟩ : syracuseStep 2093143 = 3139715) B3139715
theorem B5029229 : Blo 2091435 5029229 := bbase (se 3 (by rfl) ⟨942980, by rfl⟩ : syracuseStep 5029229 = 1885961) (by norm_num)
theorem B13411277 : Blo 2091435 13411277 := bstep (se 3 (by rfl) ⟨2514614, by rfl⟩ : syracuseStep 13411277 = 5029229) B5029229
theorem B8940851 : Blo 2091435 8940851 := bstep (se 1 (by rfl) ⟨6705638, by rfl⟩ : syracuseStep 8940851 = 13411277) B13411277
theorem B5960567 : Blo 2091435 5960567 := bstep (se 1 (by rfl) ⟨4470425, by rfl⟩ : syracuseStep 5960567 = 8940851) B8940851
theorem B3973711 : Blo 2091435 3973711 := bstep (se 1 (by rfl) ⟨2980283, by rfl⟩ : syracuseStep 3973711 = 5960567) B5960567
theorem B5298281 : Blo 2091435 5298281 := bstep (se 2 (by rfl) ⟨1986855, by rfl⟩ : syracuseStep 5298281 = 3973711) B3973711
theorem B3532187 : Blo 2091435 3532187 := bstep (se 1 (by rfl) ⟨2649140, by rfl⟩ : syracuseStep 3532187 = 5298281) B5298281
theorem B2354791 : Blo 2091435 2354791 := bstep (se 1 (by rfl) ⟨1766093, by rfl⟩ : syracuseStep 2354791 = 3532187) B3532187
theorem B3139721 : Blo 2091435 3139721 := bstep (se 2 (by rfl) ⟨1177395, by rfl⟩ : syracuseStep 3139721 = 2354791) B2354791
theorem B2093147 : Blo 2091435 2093147 := bstep (se 1 (by rfl) ⟨1569860, by rfl⟩ : syracuseStep 2093147 = 3139721) B3139721
theorem B10596581 : Blo 2091435 10596581 := bbase (se 4 (by rfl) ⟨993429, by rfl⟩ : syracuseStep 10596581 = 1986859) (by norm_num)
theorem B7064387 : Blo 2091435 7064387 := bstep (se 1 (by rfl) ⟨5298290, by rfl⟩ : syracuseStep 7064387 = 10596581) B10596581
theorem B4709591 : Blo 2091435 4709591 := bstep (se 1 (by rfl) ⟨3532193, by rfl⟩ : syracuseStep 4709591 = 7064387) B7064387
theorem B3139727 : Blo 2091435 3139727 := bstep (se 1 (by rfl) ⟨2354795, by rfl⟩ : syracuseStep 3139727 = 4709591) B4709591
theorem B2093151 : Blo 2091435 2093151 := bstep (se 1 (by rfl) ⟨1569863, by rfl⟩ : syracuseStep 2093151 = 3139727) B3139727
theorem B3139733 : Blo 2091435 3139733 := bbase (se 6 (by rfl) ⟨73587, by rfl⟩ : syracuseStep 3139733 = 147175) (by norm_num)
theorem B2093155 : Blo 2091435 2093155 := bstep (se 1 (by rfl) ⟨1569866, by rfl⟩ : syracuseStep 2093155 = 3139733) B3139733
theorem B8940901 : Blo 2091435 8940901 := bbase (se 4 (by rfl) ⟨838209, by rfl⟩ : syracuseStep 8940901 = 1676419) (by norm_num)
theorem B11921201 : Blo 2091435 11921201 := bstep (se 2 (by rfl) ⟨4470450, by rfl⟩ : syracuseStep 11921201 = 8940901) B8940901
theorem B7947467 : Blo 2091435 7947467 := bstep (se 1 (by rfl) ⟨5960600, by rfl⟩ : syracuseStep 7947467 = 11921201) B11921201
theorem B5298311 : Blo 2091435 5298311 := bstep (se 1 (by rfl) ⟨3973733, by rfl⟩ : syracuseStep 5298311 = 7947467) B7947467
theorem B3532207 : Blo 2091435 3532207 := bstep (se 1 (by rfl) ⟨2649155, by rfl⟩ : syracuseStep 3532207 = 5298311) B5298311
theorem B4709609 : Blo 2091435 4709609 := bstep (se 2 (by rfl) ⟨1766103, by rfl⟩ : syracuseStep 4709609 = 3532207) B3532207
theorem B3139739 : Blo 2091435 3139739 := bstep (se 1 (by rfl) ⟨2354804, by rfl⟩ : syracuseStep 3139739 = 4709609) B4709609
theorem B2093159 : Blo 2091435 2093159 := bstep (se 1 (by rfl) ⟨1569869, by rfl⟩ : syracuseStep 2093159 = 3139739) B3139739
theorem B2354809 : Blo 2091435 2354809 := bbase (se 2 (by rfl) ⟨883053, by rfl⟩ : syracuseStep 2354809 = 1766107) (by norm_num)
theorem B3139745 : Blo 2091435 3139745 := bstep (se 2 (by rfl) ⟨1177404, by rfl⟩ : syracuseStep 3139745 = 2354809) B2354809
theorem B2093163 : Blo 2091435 2093163 := bstep (se 1 (by rfl) ⟨1569872, by rfl⟩ : syracuseStep 2093163 = 3139745) B3139745
theorem B15087829 : Blo 2091435 15087829 := bbase (se 7 (by rfl) ⟨176810, by rfl⟩ : syracuseStep 15087829 = 353621) (by norm_num)
theorem B20117105 : Blo 2091435 20117105 := bstep (se 2 (by rfl) ⟨7543914, by rfl⟩ : syracuseStep 20117105 = 15087829) B15087829
theorem B13411403 : Blo 2091435 13411403 := bstep (se 1 (by rfl) ⟨10058552, by rfl⟩ : syracuseStep 13411403 = 20117105) B20117105
theorem B8940935 : Blo 2091435 8940935 := bstep (se 1 (by rfl) ⟨6705701, by rfl⟩ : syracuseStep 8940935 = 13411403) B13411403
theorem B5960623 : Blo 2091435 5960623 := bstep (se 1 (by rfl) ⟨4470467, by rfl⟩ : syracuseStep 5960623 = 8940935) B8940935
theorem B7947497 : Blo 2091435 7947497 := bstep (se 2 (by rfl) ⟨2980311, by rfl⟩ : syracuseStep 7947497 = 5960623) B5960623
theorem B5298331 : Blo 2091435 5298331 := bstep (se 1 (by rfl) ⟨3973748, by rfl⟩ : syracuseStep 5298331 = 7947497) B7947497
theorem B7064441 : Blo 2091435 7064441 := bstep (se 2 (by rfl) ⟨2649165, by rfl⟩ : syracuseStep 7064441 = 5298331) B5298331
theorem B4709627 : Blo 2091435 4709627 := bstep (se 1 (by rfl) ⟨3532220, by rfl⟩ : syracuseStep 4709627 = 7064441) B7064441
theorem B3139751 : Blo 2091435 3139751 := bstep (se 1 (by rfl) ⟨2354813, by rfl⟩ : syracuseStep 3139751 = 4709627) B4709627
theorem B2093167 : Blo 2091435 2093167 := bstep (se 1 (by rfl) ⟨1569875, by rfl⟩ : syracuseStep 2093167 = 3139751) B3139751
theorem B3139757 : Blo 2091435 3139757 := bbase (se 3 (by rfl) ⟨588704, by rfl⟩ : syracuseStep 3139757 = 1177409) (by norm_num)
theorem B2093171 : Blo 2091435 2093171 := bstep (se 1 (by rfl) ⟨1569878, by rfl⟩ : syracuseStep 2093171 = 3139757) B3139757
theorem B4709645 : Blo 2091435 4709645 := bbase (se 3 (by rfl) ⟨883058, by rfl⟩ : syracuseStep 4709645 = 1766117) (by norm_num)
theorem B3139763 : Blo 2091435 3139763 := bstep (se 1 (by rfl) ⟨2354822, by rfl⟩ : syracuseStep 3139763 = 4709645) B4709645
theorem B2093175 : Blo 2091435 2093175 := bstep (se 1 (by rfl) ⟨1569881, by rfl⟩ : syracuseStep 2093175 = 3139763) B3139763
theorem B2649181 : Blo 2091435 2649181 := bbase (se 3 (by rfl) ⟨496721, by rfl⟩ : syracuseStep 2649181 = 993443) (by norm_num)
theorem B3532241 : Blo 2091435 3532241 := bstep (se 2 (by rfl) ⟨1324590, by rfl⟩ : syracuseStep 3532241 = 2649181) B2649181
theorem B2354827 : Blo 2091435 2354827 := bstep (se 1 (by rfl) ⟨1766120, by rfl⟩ : syracuseStep 2354827 = 3532241) B3532241
theorem B3139769 : Blo 2091435 3139769 := bstep (se 2 (by rfl) ⟨1177413, by rfl⟩ : syracuseStep 3139769 = 2354827) B2354827
theorem B2093179 : Blo 2091435 2093179 := bstep (se 1 (by rfl) ⟨1569884, by rfl⟩ : syracuseStep 2093179 = 3139769) B3139769
theorem B17882005 : Blo 2091435 17882005 := bbase (se 6 (by rfl) ⟨419109, by rfl⟩ : syracuseStep 17882005 = 838219) (by norm_num)
theorem B23842673 : Blo 2091435 23842673 := bstep (se 2 (by rfl) ⟨8941002, by rfl⟩ : syracuseStep 23842673 = 17882005) B17882005
theorem B15895115 : Blo 2091435 15895115 := bstep (se 1 (by rfl) ⟨11921336, by rfl⟩ : syracuseStep 15895115 = 23842673) B23842673
theorem B10596743 : Blo 2091435 10596743 := bstep (se 1 (by rfl) ⟨7947557, by rfl⟩ : syracuseStep 10596743 = 15895115) B15895115
theorem B7064495 : Blo 2091435 7064495 := bstep (se 1 (by rfl) ⟨5298371, by rfl⟩ : syracuseStep 7064495 = 10596743) B10596743
theorem B4709663 : Blo 2091435 4709663 := bstep (se 1 (by rfl) ⟨3532247, by rfl⟩ : syracuseStep 4709663 = 7064495) B7064495
theorem B3139775 : Blo 2091435 3139775 := bstep (se 1 (by rfl) ⟨2354831, by rfl⟩ : syracuseStep 3139775 = 4709663) B4709663
theorem B2093183 : Blo 2091435 2093183 := bstep (se 1 (by rfl) ⟨1569887, by rfl⟩ : syracuseStep 2093183 = 3139775) B3139775
theorem B3139781 : Blo 2091435 3139781 := bbase (se 4 (by rfl) ⟨294354, by rfl⟩ : syracuseStep 3139781 = 588709) (by norm_num)
theorem B2093187 : Blo 2091435 2093187 := bstep (se 1 (by rfl) ⟨1569890, by rfl⟩ : syracuseStep 2093187 = 3139781) B3139781
theorem B3532261 : Blo 2091435 3532261 := bbase (se 4 (by rfl) ⟨331149, by rfl⟩ : syracuseStep 3532261 = 662299) (by norm_num)
theorem B4709681 : Blo 2091435 4709681 := bstep (se 2 (by rfl) ⟨1766130, by rfl⟩ : syracuseStep 4709681 = 3532261) B3532261
theorem B3139787 : Blo 2091435 3139787 := bstep (se 1 (by rfl) ⟨2354840, by rfl⟩ : syracuseStep 3139787 = 4709681) B4709681
theorem B2093191 : Blo 2091435 2093191 := bstep (se 1 (by rfl) ⟨1569893, by rfl⟩ : syracuseStep 2093191 = 3139787) B3139787
theorem B2354845 : Blo 2091435 2354845 := bbase (se 3 (by rfl) ⟨441533, by rfl⟩ : syracuseStep 2354845 = 883067) (by norm_num)
theorem B3139793 : Blo 2091435 3139793 := bstep (se 2 (by rfl) ⟨1177422, by rfl⟩ : syracuseStep 3139793 = 2354845) B2354845
theorem B2093195 : Blo 2091435 2093195 := bstep (se 1 (by rfl) ⟨1569896, by rfl⟩ : syracuseStep 2093195 = 3139793) B3139793
theorem B7064549 : Blo 2091435 7064549 := bbase (se 4 (by rfl) ⟨662301, by rfl⟩ : syracuseStep 7064549 = 1324603) (by norm_num)
theorem B4709699 : Blo 2091435 4709699 := bstep (se 1 (by rfl) ⟨3532274, by rfl⟩ : syracuseStep 4709699 = 7064549) B7064549
theorem B3139799 : Blo 2091435 3139799 := bstep (se 1 (by rfl) ⟨2354849, by rfl⟩ : syracuseStep 3139799 = 4709699) B4709699
theorem B2093199 : Blo 2091435 2093199 := bstep (se 1 (by rfl) ⟨1569899, by rfl⟩ : syracuseStep 2093199 = 3139799) B3139799
theorem B3139805 : Blo 2091435 3139805 := bbase (se 3 (by rfl) ⟨588713, by rfl⟩ : syracuseStep 3139805 = 1177427) (by norm_num)
theorem B2093203 : Blo 2091435 2093203 := bstep (se 1 (by rfl) ⟨1569902, by rfl⟩ : syracuseStep 2093203 = 3139805) B3139805
theorem B4709717 : Blo 2091435 4709717 := bbase (se 11 (by rfl) ⟨3449, by rfl⟩ : syracuseStep 4709717 = 6899) (by norm_num)
theorem B3139811 : Blo 2091435 3139811 := bstep (se 1 (by rfl) ⟨2354858, by rfl⟩ : syracuseStep 3139811 = 4709717) B4709717
theorem B2093207 : Blo 2091435 2093207 := bstep (se 1 (by rfl) ⟨1569905, by rfl⟩ : syracuseStep 2093207 = 3139811) B3139811
theorem B2235281 : Blo 2091435 2235281 := bbase (se 2 (by rfl) ⟨838230, by rfl⟩ : syracuseStep 2235281 = 1676461) (by norm_num)
theorem B5960749 : Blo 2091435 5960749 := bstep (se 3 (by rfl) ⟨1117640, by rfl⟩ : syracuseStep 5960749 = 2235281) B2235281
theorem B7947665 : Blo 2091435 7947665 := bstep (se 2 (by rfl) ⟨2980374, by rfl⟩ : syracuseStep 7947665 = 5960749) B5960749
theorem B5298443 : Blo 2091435 5298443 := bstep (se 1 (by rfl) ⟨3973832, by rfl⟩ : syracuseStep 5298443 = 7947665) B7947665
theorem B3532295 : Blo 2091435 3532295 := bstep (se 1 (by rfl) ⟨2649221, by rfl⟩ : syracuseStep 3532295 = 5298443) B5298443
theorem B2354863 : Blo 2091435 2354863 := bstep (se 1 (by rfl) ⟨1766147, by rfl⟩ : syracuseStep 2354863 = 3532295) B3532295
theorem B3139817 : Blo 2091435 3139817 := bstep (se 2 (by rfl) ⟨1177431, by rfl⟩ : syracuseStep 3139817 = 2354863) B2354863
theorem B2093211 : Blo 2091435 2093211 := bstep (se 1 (by rfl) ⟨1569908, by rfl⟩ : syracuseStep 2093211 = 3139817) B3139817
theorem B4593389 : Blo 2091435 4593389 := bbase (se 3 (by rfl) ⟨861260, by rfl⟩ : syracuseStep 4593389 = 1722521) (by norm_num)
theorem B12249037 : Blo 2091435 12249037 := bstep (se 3 (by rfl) ⟨2296694, by rfl⟩ : syracuseStep 12249037 = 4593389) B4593389
theorem B16332049 : Blo 2091435 16332049 := bstep (se 2 (by rfl) ⟨6124518, by rfl⟩ : syracuseStep 16332049 = 12249037) B12249037
theorem B87104261 : Blo 2091435 87104261 := bstep (se 4 (by rfl) ⟨8166024, by rfl⟩ : syracuseStep 87104261 = 16332049) B16332049
theorem B232278029 : Blo 2091435 232278029 := bstep (se 3 (by rfl) ⟨43552130, by rfl⟩ : syracuseStep 232278029 = 87104261) B87104261
theorem B154852019 : Blo 2091435 154852019 := bstep (se 1 (by rfl) ⟨116139014, by rfl⟩ : syracuseStep 154852019 = 232278029) B232278029
theorem B103234679 : Blo 2091435 103234679 := bstep (se 1 (by rfl) ⟨77426009, by rfl⟩ : syracuseStep 103234679 = 154852019) B154852019
theorem B68823119 : Blo 2091435 68823119 := bstep (se 1 (by rfl) ⟨51617339, by rfl⟩ : syracuseStep 68823119 = 103234679) B103234679
theorem B183528317 : Blo 2091435 183528317 := bstep (se 3 (by rfl) ⟨34411559, by rfl⟩ : syracuseStep 183528317 = 68823119) B68823119
theorem B122352211 : Blo 2091435 122352211 := bstep (se 1 (by rfl) ⟨91764158, by rfl⟩ : syracuseStep 122352211 = 183528317) B183528317
theorem B163136281 : Blo 2091435 163136281 := bstep (se 2 (by rfl) ⟨61176105, by rfl⟩ : syracuseStep 163136281 = 122352211) B122352211
theorem B217515041 : Blo 2091435 217515041 := bstep (se 2 (by rfl) ⟨81568140, by rfl⟩ : syracuseStep 217515041 = 163136281) B163136281
theorem B145010027 : Blo 2091435 145010027 := bstep (se 1 (by rfl) ⟨108757520, by rfl⟩ : syracuseStep 145010027 = 217515041) B217515041
theorem B96673351 : Blo 2091435 96673351 := bstep (se 1 (by rfl) ⟨72505013, by rfl⟩ : syracuseStep 96673351 = 145010027) B145010027
theorem B128897801 : Blo 2091435 128897801 := bstep (se 2 (by rfl) ⟨48336675, by rfl⟩ : syracuseStep 128897801 = 96673351) B96673351
theorem B85931867 : Blo 2091435 85931867 := bstep (se 1 (by rfl) ⟨64448900, by rfl⟩ : syracuseStep 85931867 = 128897801) B128897801
theorem B57287911 : Blo 2091435 57287911 := bstep (se 1 (by rfl) ⟨42965933, by rfl⟩ : syracuseStep 57287911 = 85931867) B85931867
theorem B76383881 : Blo 2091435 76383881 := bstep (se 2 (by rfl) ⟨28643955, by rfl⟩ : syracuseStep 76383881 = 57287911) B57287911
theorem B50922587 : Blo 2091435 50922587 := bstep (se 1 (by rfl) ⟨38191940, by rfl⟩ : syracuseStep 50922587 = 76383881) B76383881
theorem B33948391 : Blo 2091435 33948391 := bstep (se 1 (by rfl) ⟨25461293, by rfl⟩ : syracuseStep 33948391 = 50922587) B50922587
theorem B45264521 : Blo 2091435 45264521 := bstep (se 2 (by rfl) ⟨16974195, by rfl⟩ : syracuseStep 45264521 = 33948391) B33948391
theorem B30176347 : Blo 2091435 30176347 := bstep (se 1 (by rfl) ⟨22632260, by rfl⟩ : syracuseStep 30176347 = 45264521) B45264521
theorem B40235129 : Blo 2091435 40235129 := bstep (se 2 (by rfl) ⟨15088173, by rfl⟩ : syracuseStep 40235129 = 30176347) B30176347
theorem B26823419 : Blo 2091435 26823419 := bstep (se 1 (by rfl) ⟨20117564, by rfl⟩ : syracuseStep 26823419 = 40235129) B40235129
theorem B17882279 : Blo 2091435 17882279 := bstep (se 1 (by rfl) ⟨13411709, by rfl⟩ : syracuseStep 17882279 = 26823419) B26823419
theorem B11921519 : Blo 2091435 11921519 := bstep (se 1 (by rfl) ⟨8941139, by rfl⟩ : syracuseStep 11921519 = 17882279) B17882279
theorem B7947679 : Blo 2091435 7947679 := bstep (se 1 (by rfl) ⟨5960759, by rfl⟩ : syracuseStep 7947679 = 11921519) B11921519
theorem B10596905 : Blo 2091435 10596905 := bstep (se 2 (by rfl) ⟨3973839, by rfl⟩ : syracuseStep 10596905 = 7947679) B7947679
theorem B7064603 : Blo 2091435 7064603 := bstep (se 1 (by rfl) ⟨5298452, by rfl⟩ : syracuseStep 7064603 = 10596905) B10596905
theorem B4709735 : Blo 2091435 4709735 := bstep (se 1 (by rfl) ⟨3532301, by rfl⟩ : syracuseStep 4709735 = 7064603) B7064603
theorem B3139823 : Blo 2091435 3139823 := bstep (se 1 (by rfl) ⟨2354867, by rfl⟩ : syracuseStep 3139823 = 4709735) B4709735
theorem B2093215 : Blo 2091435 2093215 := bstep (se 1 (by rfl) ⟨1569911, by rfl⟩ : syracuseStep 2093215 = 3139823) B3139823
theorem B3139829 : Blo 2091435 3139829 := bbase (se 5 (by rfl) ⟨147179, by rfl⟩ : syracuseStep 3139829 = 294359) (by norm_num)
theorem B2093219 : Blo 2091435 2093219 := bstep (se 1 (by rfl) ⟨1569914, by rfl⟩ : syracuseStep 2093219 = 3139829) B3139829
theorem B7544117 : Blo 2091435 7544117 := bbase (se 5 (by rfl) ⟨353630, by rfl⟩ : syracuseStep 7544117 = 707261) (by norm_num)
theorem B20117645 : Blo 2091435 20117645 := bstep (se 3 (by rfl) ⟨3772058, by rfl⟩ : syracuseStep 20117645 = 7544117) B7544117
theorem B13411763 : Blo 2091435 13411763 := bstep (se 1 (by rfl) ⟨10058822, by rfl⟩ : syracuseStep 13411763 = 20117645) B20117645
theorem B8941175 : Blo 2091435 8941175 := bstep (se 1 (by rfl) ⟨6705881, by rfl⟩ : syracuseStep 8941175 = 13411763) B13411763
theorem B5960783 : Blo 2091435 5960783 := bstep (se 1 (by rfl) ⟨4470587, by rfl⟩ : syracuseStep 5960783 = 8941175) B8941175
theorem B3973855 : Blo 2091435 3973855 := bstep (se 1 (by rfl) ⟨2980391, by rfl⟩ : syracuseStep 3973855 = 5960783) B5960783
theorem B5298473 : Blo 2091435 5298473 := bstep (se 2 (by rfl) ⟨1986927, by rfl⟩ : syracuseStep 5298473 = 3973855) B3973855
theorem B3532315 : Blo 2091435 3532315 := bstep (se 1 (by rfl) ⟨2649236, by rfl⟩ : syracuseStep 3532315 = 5298473) B5298473
theorem B4709753 : Blo 2091435 4709753 := bstep (se 2 (by rfl) ⟨1766157, by rfl⟩ : syracuseStep 4709753 = 3532315) B3532315
theorem B3139835 : Blo 2091435 3139835 := bstep (se 1 (by rfl) ⟨2354876, by rfl⟩ : syracuseStep 3139835 = 4709753) B4709753
theorem B2093223 : Blo 2091435 2093223 := bstep (se 1 (by rfl) ⟨1569917, by rfl⟩ : syracuseStep 2093223 = 3139835) B3139835
theorem B2354881 : Blo 2091435 2354881 := bbase (se 2 (by rfl) ⟨883080, by rfl⟩ : syracuseStep 2354881 = 1766161) (by norm_num)
theorem B3139841 : Blo 2091435 3139841 := bstep (se 2 (by rfl) ⟨1177440, by rfl⟩ : syracuseStep 3139841 = 2354881) B2354881
theorem B2093227 : Blo 2091435 2093227 := bstep (se 1 (by rfl) ⟨1569920, by rfl⟩ : syracuseStep 2093227 = 3139841) B3139841
theorem B5298493 : Blo 2091435 5298493 := bbase (se 3 (by rfl) ⟨993467, by rfl⟩ : syracuseStep 5298493 = 1986935) (by norm_num)
theorem B7064657 : Blo 2091435 7064657 := bstep (se 2 (by rfl) ⟨2649246, by rfl⟩ : syracuseStep 7064657 = 5298493) B5298493
theorem B4709771 : Blo 2091435 4709771 := bstep (se 1 (by rfl) ⟨3532328, by rfl⟩ : syracuseStep 4709771 = 7064657) B7064657
theorem B3139847 : Blo 2091435 3139847 := bstep (se 1 (by rfl) ⟨2354885, by rfl⟩ : syracuseStep 3139847 = 4709771) B4709771
theorem B2093231 : Blo 2091435 2093231 := bstep (se 1 (by rfl) ⟨1569923, by rfl⟩ : syracuseStep 2093231 = 3139847) B3139847
theorem B3139853 : Blo 2091435 3139853 := bbase (se 3 (by rfl) ⟨588722, by rfl⟩ : syracuseStep 3139853 = 1177445) (by norm_num)
theorem B2093235 : Blo 2091435 2093235 := bstep (se 1 (by rfl) ⟨1569926, by rfl⟩ : syracuseStep 2093235 = 3139853) B3139853
theorem B4709789 : Blo 2091435 4709789 := bbase (se 3 (by rfl) ⟨883085, by rfl⟩ : syracuseStep 4709789 = 1766171) (by norm_num)
theorem B3139859 : Blo 2091435 3139859 := bstep (se 1 (by rfl) ⟨2354894, by rfl⟩ : syracuseStep 3139859 = 4709789) B4709789
theorem B2093239 : Blo 2091435 2093239 := bstep (se 1 (by rfl) ⟨1569929, by rfl⟩ : syracuseStep 2093239 = 3139859) B3139859
theorem B3532349 : Blo 2091435 3532349 := bbase (se 3 (by rfl) ⟨662315, by rfl⟩ : syracuseStep 3532349 = 1324631) (by norm_num)
theorem B2354899 : Blo 2091435 2354899 := bstep (se 1 (by rfl) ⟨1766174, by rfl⟩ : syracuseStep 2354899 = 3532349) B3532349
theorem B3139865 : Blo 2091435 3139865 := bstep (se 2 (by rfl) ⟨1177449, by rfl⟩ : syracuseStep 3139865 = 2354899) B2354899
theorem B2093243 : Blo 2091435 2093243 := bstep (se 1 (by rfl) ⟨1569932, by rfl⟩ : syracuseStep 2093243 = 3139865) B3139865
theorem B5029469 : Blo 2091435 5029469 := bbase (se 3 (by rfl) ⟨943025, by rfl⟩ : syracuseStep 5029469 = 1886051) (by norm_num)
theorem B3352979 : Blo 2091435 3352979 := bstep (se 1 (by rfl) ⟨2514734, by rfl⟩ : syracuseStep 3352979 = 5029469) B5029469
theorem B2235319 : Blo 2091435 2235319 := bstep (se 1 (by rfl) ⟨1676489, by rfl⟩ : syracuseStep 2235319 = 3352979) B3352979
theorem B11921701 : Blo 2091435 11921701 := bstep (se 4 (by rfl) ⟨1117659, by rfl⟩ : syracuseStep 11921701 = 2235319) B2235319
theorem B15895601 : Blo 2091435 15895601 := bstep (se 2 (by rfl) ⟨5960850, by rfl⟩ : syracuseStep 15895601 = 11921701) B11921701
theorem B10597067 : Blo 2091435 10597067 := bstep (se 1 (by rfl) ⟨7947800, by rfl⟩ : syracuseStep 10597067 = 15895601) B15895601
theorem B7064711 : Blo 2091435 7064711 := bstep (se 1 (by rfl) ⟨5298533, by rfl⟩ : syracuseStep 7064711 = 10597067) B10597067
theorem B4709807 : Blo 2091435 4709807 := bstep (se 1 (by rfl) ⟨3532355, by rfl⟩ : syracuseStep 4709807 = 7064711) B7064711
theorem B3139871 : Blo 2091435 3139871 := bstep (se 1 (by rfl) ⟨2354903, by rfl⟩ : syracuseStep 3139871 = 4709807) B4709807
theorem B2093247 : Blo 2091435 2093247 := bstep (se 1 (by rfl) ⟨1569935, by rfl⟩ : syracuseStep 2093247 = 3139871) B3139871
theorem B3139877 : Blo 2091435 3139877 := bbase (se 4 (by rfl) ⟨294363, by rfl⟩ : syracuseStep 3139877 = 588727) (by norm_num)
theorem B2093251 : Blo 2091435 2093251 := bstep (se 1 (by rfl) ⟨1569938, by rfl⟩ : syracuseStep 2093251 = 3139877) B3139877
theorem B2649277 : Blo 2091435 2649277 := bbase (se 3 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 2649277 = 993479) (by norm_num)
theorem B3532369 : Blo 2091435 3532369 := bstep (se 2 (by rfl) ⟨1324638, by rfl⟩ : syracuseStep 3532369 = 2649277) B2649277
theorem B4709825 : Blo 2091435 4709825 := bstep (se 2 (by rfl) ⟨1766184, by rfl⟩ : syracuseStep 4709825 = 3532369) B3532369
theorem B3139883 : Blo 2091435 3139883 := bstep (se 1 (by rfl) ⟨2354912, by rfl⟩ : syracuseStep 3139883 = 4709825) B4709825
theorem B2093255 : Blo 2091435 2093255 := bstep (se 1 (by rfl) ⟨1569941, by rfl⟩ : syracuseStep 2093255 = 3139883) B3139883
theorem B2354917 : Blo 2091435 2354917 := bbase (se 4 (by rfl) ⟨220773, by rfl⟩ : syracuseStep 2354917 = 441547) (by norm_num)
theorem B3139889 : Blo 2091435 3139889 := bstep (se 2 (by rfl) ⟨1177458, by rfl⟩ : syracuseStep 3139889 = 2354917) B2354917
theorem B2093259 : Blo 2091435 2093259 := bstep (se 1 (by rfl) ⟨1569944, by rfl⟩ : syracuseStep 2093259 = 3139889) B3139889
theorem B3353005 : Blo 2091435 3353005 := bbase (se 3 (by rfl) ⟨628688, by rfl⟩ : syracuseStep 3353005 = 1257377) (by norm_num)
theorem B4470673 : Blo 2091435 4470673 := bstep (se 2 (by rfl) ⟨1676502, by rfl⟩ : syracuseStep 4470673 = 3353005) B3353005
theorem B5960897 : Blo 2091435 5960897 := bstep (se 2 (by rfl) ⟨2235336, by rfl⟩ : syracuseStep 5960897 = 4470673) B4470673
theorem B3973931 : Blo 2091435 3973931 := bstep (se 1 (by rfl) ⟨2980448, by rfl⟩ : syracuseStep 3973931 = 5960897) B5960897
theorem B2649287 : Blo 2091435 2649287 := bstep (se 1 (by rfl) ⟨1986965, by rfl⟩ : syracuseStep 2649287 = 3973931) B3973931
theorem B7064765 : Blo 2091435 7064765 := bstep (se 3 (by rfl) ⟨1324643, by rfl⟩ : syracuseStep 7064765 = 2649287) B2649287
theorem B4709843 : Blo 2091435 4709843 := bstep (se 1 (by rfl) ⟨3532382, by rfl⟩ : syracuseStep 4709843 = 7064765) B7064765
theorem B3139895 : Blo 2091435 3139895 := bstep (se 1 (by rfl) ⟨2354921, by rfl⟩ : syracuseStep 3139895 = 4709843) B4709843
theorem B2093263 : Blo 2091435 2093263 := bstep (se 1 (by rfl) ⟨1569947, by rfl⟩ : syracuseStep 2093263 = 3139895) B3139895
theorem B3139901 : Blo 2091435 3139901 := bbase (se 3 (by rfl) ⟨588731, by rfl⟩ : syracuseStep 3139901 = 1177463) (by norm_num)
theorem B2093267 : Blo 2091435 2093267 := bstep (se 1 (by rfl) ⟨1569950, by rfl⟩ : syracuseStep 2093267 = 3139901) B3139901
theorem B4709861 : Blo 2091435 4709861 := bbase (se 4 (by rfl) ⟨441549, by rfl⟩ : syracuseStep 4709861 = 883099) (by norm_num)
theorem B3139907 : Blo 2091435 3139907 := bstep (se 1 (by rfl) ⟨2354930, by rfl⟩ : syracuseStep 3139907 = 4709861) B4709861
theorem B2093271 : Blo 2091435 2093271 := bstep (se 1 (by rfl) ⟨1569953, by rfl⟩ : syracuseStep 2093271 = 3139907) B3139907
theorem B5298605 : Blo 2091435 5298605 := bbase (se 3 (by rfl) ⟨993488, by rfl⟩ : syracuseStep 5298605 = 1986977) (by norm_num)
theorem B3532403 : Blo 2091435 3532403 := bstep (se 1 (by rfl) ⟨2649302, by rfl⟩ : syracuseStep 3532403 = 5298605) B5298605
theorem B2354935 : Blo 2091435 2354935 := bstep (se 1 (by rfl) ⟨1766201, by rfl⟩ : syracuseStep 2354935 = 3532403) B3532403
theorem B3139913 : Blo 2091435 3139913 := bstep (se 2 (by rfl) ⟨1177467, by rfl⟩ : syracuseStep 3139913 = 2354935) B2354935
theorem B2093275 : Blo 2091435 2093275 := bstep (se 1 (by rfl) ⟨1569956, by rfl⟩ : syracuseStep 2093275 = 3139913) B3139913
theorem B2514773 : Blo 2091435 2514773 := bbase (se 9 (by rfl) ⟨7367, by rfl⟩ : syracuseStep 2514773 = 14735) (by norm_num)
theorem B6706061 : Blo 2091435 6706061 := bstep (se 3 (by rfl) ⟨1257386, by rfl⟩ : syracuseStep 6706061 = 2514773) B2514773
theorem B4470707 : Blo 2091435 4470707 := bstep (se 1 (by rfl) ⟨3353030, by rfl⟩ : syracuseStep 4470707 = 6706061) B6706061
theorem B2980471 : Blo 2091435 2980471 := bstep (se 1 (by rfl) ⟨2235353, by rfl⟩ : syracuseStep 2980471 = 4470707) B4470707
theorem B3973961 : Blo 2091435 3973961 := bstep (se 2 (by rfl) ⟨1490235, by rfl⟩ : syracuseStep 3973961 = 2980471) B2980471
theorem B10597229 : Blo 2091435 10597229 := bstep (se 3 (by rfl) ⟨1986980, by rfl⟩ : syracuseStep 10597229 = 3973961) B3973961
theorem B7064819 : Blo 2091435 7064819 := bstep (se 1 (by rfl) ⟨5298614, by rfl⟩ : syracuseStep 7064819 = 10597229) B10597229
theorem B4709879 : Blo 2091435 4709879 := bstep (se 1 (by rfl) ⟨3532409, by rfl⟩ : syracuseStep 4709879 = 7064819) B7064819
theorem B3139919 : Blo 2091435 3139919 := bstep (se 1 (by rfl) ⟨2354939, by rfl⟩ : syracuseStep 3139919 = 4709879) B4709879
theorem B2093279 : Blo 2091435 2093279 := bstep (se 1 (by rfl) ⟨1569959, by rfl⟩ : syracuseStep 2093279 = 3139919) B3139919
theorem B3139925 : Blo 2091435 3139925 := bbase (se 10 (by rfl) ⟨4599, by rfl⟩ : syracuseStep 3139925 = 9199) (by norm_num)
theorem B2093283 : Blo 2091435 2093283 := bstep (se 1 (by rfl) ⟨1569962, by rfl⟩ : syracuseStep 2093283 = 3139925) B3139925
theorem B5960965 : Blo 2091435 5960965 := bbase (se 4 (by rfl) ⟨558840, by rfl⟩ : syracuseStep 5960965 = 1117681) (by norm_num)
theorem B7947953 : Blo 2091435 7947953 := bstep (se 2 (by rfl) ⟨2980482, by rfl⟩ : syracuseStep 7947953 = 5960965) B5960965
theorem B5298635 : Blo 2091435 5298635 := bstep (se 1 (by rfl) ⟨3973976, by rfl⟩ : syracuseStep 5298635 = 7947953) B7947953
theorem B3532423 : Blo 2091435 3532423 := bstep (se 1 (by rfl) ⟨2649317, by rfl⟩ : syracuseStep 3532423 = 5298635) B5298635
theorem B4709897 : Blo 2091435 4709897 := bstep (se 2 (by rfl) ⟨1766211, by rfl⟩ : syracuseStep 4709897 = 3532423) B3532423
theorem B3139931 : Blo 2091435 3139931 := bstep (se 1 (by rfl) ⟨2354948, by rfl⟩ : syracuseStep 3139931 = 4709897) B4709897
theorem B2093287 : Blo 2091435 2093287 := bstep (se 1 (by rfl) ⟨1569965, by rfl⟩ : syracuseStep 2093287 = 3139931) B3139931
theorem B2354953 : Blo 2091435 2354953 := bbase (se 2 (by rfl) ⟨883107, by rfl⟩ : syracuseStep 2354953 = 1766215) (by norm_num)
theorem B3139937 : Blo 2091435 3139937 := bstep (se 2 (by rfl) ⟨1177476, by rfl⟩ : syracuseStep 3139937 = 2354953) B2354953
theorem B2093291 : Blo 2091435 2093291 := bstep (se 1 (by rfl) ⟨1569968, by rfl⟩ : syracuseStep 2093291 = 3139937) B3139937
theorem B8720597 : Blo 2091435 8720597 := bbase (se 7 (by rfl) ⟨102194, by rfl⟩ : syracuseStep 8720597 = 204389) (by norm_num)
theorem B5813731 : Blo 2091435 5813731 := bstep (se 1 (by rfl) ⟨4360298, by rfl⟩ : syracuseStep 5813731 = 8720597) B8720597
theorem B31006565 : Blo 2091435 31006565 := bstep (se 4 (by rfl) ⟨2906865, by rfl⟩ : syracuseStep 31006565 = 5813731) B5813731
theorem B20671043 : Blo 2091435 20671043 := bstep (se 1 (by rfl) ⟨15503282, by rfl⟩ : syracuseStep 20671043 = 31006565) B31006565
theorem B55122781 : Blo 2091435 55122781 := bstep (se 3 (by rfl) ⟨10335521, by rfl⟩ : syracuseStep 55122781 = 20671043) B20671043
theorem B73497041 : Blo 2091435 73497041 := bstep (se 2 (by rfl) ⟨27561390, by rfl⟩ : syracuseStep 73497041 = 55122781) B55122781
theorem B48998027 : Blo 2091435 48998027 := bstep (se 1 (by rfl) ⟨36748520, by rfl⟩ : syracuseStep 48998027 = 73497041) B73497041
theorem B32665351 : Blo 2091435 32665351 := bstep (se 1 (by rfl) ⟨24499013, by rfl⟩ : syracuseStep 32665351 = 48998027) B48998027
theorem B43553801 : Blo 2091435 43553801 := bstep (se 2 (by rfl) ⟨16332675, by rfl⟩ : syracuseStep 43553801 = 32665351) B32665351
theorem B29035867 : Blo 2091435 29035867 := bstep (se 1 (by rfl) ⟨21776900, by rfl⟩ : syracuseStep 29035867 = 43553801) B43553801
theorem B38714489 : Blo 2091435 38714489 := bstep (se 2 (by rfl) ⟨14517933, by rfl⟩ : syracuseStep 38714489 = 29035867) B29035867
theorem B25809659 : Blo 2091435 25809659 := bstep (se 1 (by rfl) ⟨19357244, by rfl⟩ : syracuseStep 25809659 = 38714489) B38714489
theorem B17206439 : Blo 2091435 17206439 := bstep (se 1 (by rfl) ⟨12904829, by rfl⟩ : syracuseStep 17206439 = 25809659) B25809659
theorem B45883837 : Blo 2091435 45883837 := bstep (se 3 (by rfl) ⟨8603219, by rfl⟩ : syracuseStep 45883837 = 17206439) B17206439
theorem B244713797 : Blo 2091435 244713797 := bstep (se 4 (by rfl) ⟨22941918, by rfl⟩ : syracuseStep 244713797 = 45883837) B45883837
theorem B163142531 : Blo 2091435 163142531 := bstep (se 1 (by rfl) ⟨122356898, by rfl⟩ : syracuseStep 163142531 = 244713797) B244713797
theorem B108761687 : Blo 2091435 108761687 := bstep (se 1 (by rfl) ⟨81571265, by rfl⟩ : syracuseStep 108761687 = 163142531) B163142531
theorem B72507791 : Blo 2091435 72507791 := bstep (se 1 (by rfl) ⟨54380843, by rfl⟩ : syracuseStep 72507791 = 108761687) B108761687
theorem B48338527 : Blo 2091435 48338527 := bstep (se 1 (by rfl) ⟨36253895, by rfl⟩ : syracuseStep 48338527 = 72507791) B72507791
theorem B64451369 : Blo 2091435 64451369 := bstep (se 2 (by rfl) ⟨24169263, by rfl⟩ : syracuseStep 64451369 = 48338527) B48338527
theorem B42967579 : Blo 2091435 42967579 := bstep (se 1 (by rfl) ⟨32225684, by rfl⟩ : syracuseStep 42967579 = 64451369) B64451369
theorem B57290105 : Blo 2091435 57290105 := bstep (se 2 (by rfl) ⟨21483789, by rfl⟩ : syracuseStep 57290105 = 42967579) B42967579
theorem B38193403 : Blo 2091435 38193403 := bstep (se 1 (by rfl) ⟨28645052, by rfl⟩ : syracuseStep 38193403 = 57290105) B57290105
theorem B50924537 : Blo 2091435 50924537 := bstep (se 2 (by rfl) ⟨19096701, by rfl⟩ : syracuseStep 50924537 = 38193403) B38193403
theorem B33949691 : Blo 2091435 33949691 := bstep (se 1 (by rfl) ⟨25462268, by rfl⟩ : syracuseStep 33949691 = 50924537) B50924537
theorem B22633127 : Blo 2091435 22633127 := bstep (se 1 (by rfl) ⟨16974845, by rfl⟩ : syracuseStep 22633127 = 33949691) B33949691
theorem B15088751 : Blo 2091435 15088751 := bstep (se 1 (by rfl) ⟨11316563, by rfl⟩ : syracuseStep 15088751 = 22633127) B22633127
theorem B10059167 : Blo 2091435 10059167 := bstep (se 1 (by rfl) ⟨7544375, by rfl⟩ : syracuseStep 10059167 = 15088751) B15088751
theorem B26824445 : Blo 2091435 26824445 := bstep (se 3 (by rfl) ⟨5029583, by rfl⟩ : syracuseStep 26824445 = 10059167) B10059167
theorem B17882963 : Blo 2091435 17882963 := bstep (se 1 (by rfl) ⟨13412222, by rfl⟩ : syracuseStep 17882963 = 26824445) B26824445
theorem B11921975 : Blo 2091435 11921975 := bstep (se 1 (by rfl) ⟨8941481, by rfl⟩ : syracuseStep 11921975 = 17882963) B17882963
theorem B7947983 : Blo 2091435 7947983 := bstep (se 1 (by rfl) ⟨5960987, by rfl⟩ : syracuseStep 7947983 = 11921975) B11921975
theorem B5298655 : Blo 2091435 5298655 := bstep (se 1 (by rfl) ⟨3973991, by rfl⟩ : syracuseStep 5298655 = 7947983) B7947983
theorem B7064873 : Blo 2091435 7064873 := bstep (se 2 (by rfl) ⟨2649327, by rfl⟩ : syracuseStep 7064873 = 5298655) B5298655
theorem B4709915 : Blo 2091435 4709915 := bstep (se 1 (by rfl) ⟨3532436, by rfl⟩ : syracuseStep 4709915 = 7064873) B7064873
theorem B3139943 : Blo 2091435 3139943 := bstep (se 1 (by rfl) ⟨2354957, by rfl⟩ : syracuseStep 3139943 = 4709915) B4709915
theorem B2093295 : Blo 2091435 2093295 := bstep (se 1 (by rfl) ⟨1569971, by rfl⟩ : syracuseStep 2093295 = 3139943) B3139943
theorem B3139949 : Blo 2091435 3139949 := bbase (se 3 (by rfl) ⟨588740, by rfl⟩ : syracuseStep 3139949 = 1177481) (by norm_num)
theorem B2093299 : Blo 2091435 2093299 := bstep (se 1 (by rfl) ⟨1569974, by rfl⟩ : syracuseStep 2093299 = 3139949) B3139949
theorem B4709933 : Blo 2091435 4709933 := bbase (se 3 (by rfl) ⟨883112, by rfl⟩ : syracuseStep 4709933 = 1766225) (by norm_num)
theorem B3139955 : Blo 2091435 3139955 := bstep (se 1 (by rfl) ⟨2354966, by rfl⟩ : syracuseStep 3139955 = 4709933) B4709933
theorem B2093303 : Blo 2091435 2093303 := bstep (se 1 (by rfl) ⟨1569977, by rfl⟩ : syracuseStep 2093303 = 3139955) B3139955
theorem B25462421 : Blo 2091435 25462421 := bbase (se 6 (by rfl) ⟨596775, by rfl⟩ : syracuseStep 25462421 = 1193551) (by norm_num)
theorem B16974947 : Blo 2091435 16974947 := bstep (se 1 (by rfl) ⟨12731210, by rfl⟩ : syracuseStep 16974947 = 25462421) B25462421
theorem B45266525 : Blo 2091435 45266525 := bstep (se 3 (by rfl) ⟨8487473, by rfl⟩ : syracuseStep 45266525 = 16974947) B16974947
theorem B30177683 : Blo 2091435 30177683 := bstep (se 1 (by rfl) ⟨22633262, by rfl⟩ : syracuseStep 30177683 = 45266525) B45266525
theorem B20118455 : Blo 2091435 20118455 := bstep (se 1 (by rfl) ⟨15088841, by rfl⟩ : syracuseStep 20118455 = 30177683) B30177683
theorem B13412303 : Blo 2091435 13412303 := bstep (se 1 (by rfl) ⟨10059227, by rfl⟩ : syracuseStep 13412303 = 20118455) B20118455
theorem B8941535 : Blo 2091435 8941535 := bstep (se 1 (by rfl) ⟨6706151, by rfl⟩ : syracuseStep 8941535 = 13412303) B13412303
theorem B5961023 : Blo 2091435 5961023 := bstep (se 1 (by rfl) ⟨4470767, by rfl⟩ : syracuseStep 5961023 = 8941535) B8941535
theorem B3974015 : Blo 2091435 3974015 := bstep (se 1 (by rfl) ⟨2980511, by rfl⟩ : syracuseStep 3974015 = 5961023) B5961023
theorem B2649343 : Blo 2091435 2649343 := bstep (se 1 (by rfl) ⟨1987007, by rfl⟩ : syracuseStep 2649343 = 3974015) B3974015
theorem B3532457 : Blo 2091435 3532457 := bstep (se 2 (by rfl) ⟨1324671, by rfl⟩ : syracuseStep 3532457 = 2649343) B2649343
theorem B2354971 : Blo 2091435 2354971 := bstep (se 1 (by rfl) ⟨1766228, by rfl⟩ : syracuseStep 2354971 = 3532457) B3532457
theorem B3139961 : Blo 2091435 3139961 := bstep (se 2 (by rfl) ⟨1177485, by rfl⟩ : syracuseStep 3139961 = 2354971) B2354971
theorem B2093307 : Blo 2091435 2093307 := bstep (se 1 (by rfl) ⟨1569980, by rfl⟩ : syracuseStep 2093307 = 3139961) B3139961
theorem B3580661 : Blo 2091435 3580661 := bbase (se 5 (by rfl) ⟨167843, by rfl⟩ : syracuseStep 3580661 = 335687) (by norm_num)
theorem B2387107 : Blo 2091435 2387107 := bstep (se 1 (by rfl) ⟨1790330, by rfl⟩ : syracuseStep 2387107 = 3580661) B3580661
theorem B3182809 : Blo 2091435 3182809 := bstep (se 2 (by rfl) ⟨1193553, by rfl⟩ : syracuseStep 3182809 = 2387107) B2387107
theorem B4243745 : Blo 2091435 4243745 := bstep (se 2 (by rfl) ⟨1591404, by rfl⟩ : syracuseStep 4243745 = 3182809) B3182809
theorem B2829163 : Blo 2091435 2829163 := bstep (se 1 (by rfl) ⟨2121872, by rfl⟩ : syracuseStep 2829163 = 4243745) B4243745
theorem B3772217 : Blo 2091435 3772217 := bstep (se 2 (by rfl) ⟨1414581, by rfl⟩ : syracuseStep 3772217 = 2829163) B2829163
theorem B2514811 : Blo 2091435 2514811 := bstep (se 1 (by rfl) ⟨1886108, by rfl⟩ : syracuseStep 2514811 = 3772217) B3772217
theorem B3353081 : Blo 2091435 3353081 := bstep (se 2 (by rfl) ⟨1257405, by rfl⟩ : syracuseStep 3353081 = 2514811) B2514811
theorem B35766197 : Blo 2091435 35766197 := bstep (se 5 (by rfl) ⟨1676540, by rfl⟩ : syracuseStep 35766197 = 3353081) B3353081
theorem B23844131 : Blo 2091435 23844131 := bstep (se 1 (by rfl) ⟨17883098, by rfl⟩ : syracuseStep 23844131 = 35766197) B35766197
theorem B15896087 : Blo 2091435 15896087 := bstep (se 1 (by rfl) ⟨11922065, by rfl⟩ : syracuseStep 15896087 = 23844131) B23844131
theorem B10597391 : Blo 2091435 10597391 := bstep (se 1 (by rfl) ⟨7948043, by rfl⟩ : syracuseStep 10597391 = 15896087) B15896087
theorem B7064927 : Blo 2091435 7064927 := bstep (se 1 (by rfl) ⟨5298695, by rfl⟩ : syracuseStep 7064927 = 10597391) B10597391
theorem B4709951 : Blo 2091435 4709951 := bstep (se 1 (by rfl) ⟨3532463, by rfl⟩ : syracuseStep 4709951 = 7064927) B7064927
theorem B3139967 : Blo 2091435 3139967 := bstep (se 1 (by rfl) ⟨2354975, by rfl⟩ : syracuseStep 3139967 = 4709951) B4709951
theorem B2093311 : Blo 2091435 2093311 := bstep (se 1 (by rfl) ⟨1569983, by rfl⟩ : syracuseStep 2093311 = 3139967) B3139967
theorem B3139973 : Blo 2091435 3139973 := bbase (se 4 (by rfl) ⟨294372, by rfl⟩ : syracuseStep 3139973 = 588745) (by norm_num)
theorem B2093315 : Blo 2091435 2093315 := bstep (se 1 (by rfl) ⟨1569986, by rfl⟩ : syracuseStep 2093315 = 3139973) B3139973
theorem B3532477 : Blo 2091435 3532477 := bbase (se 3 (by rfl) ⟨662339, by rfl⟩ : syracuseStep 3532477 = 1324679) (by norm_num)
theorem B4709969 : Blo 2091435 4709969 := bstep (se 2 (by rfl) ⟨1766238, by rfl⟩ : syracuseStep 4709969 = 3532477) B3532477
theorem B3139979 : Blo 2091435 3139979 := bstep (se 1 (by rfl) ⟨2354984, by rfl⟩ : syracuseStep 3139979 = 4709969) B4709969
theorem B2093319 : Blo 2091435 2093319 := bstep (se 1 (by rfl) ⟨1569989, by rfl⟩ : syracuseStep 2093319 = 3139979) B3139979
theorem B2354989 : Blo 2091435 2354989 := bbase (se 3 (by rfl) ⟨441560, by rfl⟩ : syracuseStep 2354989 = 883121) (by norm_num)
theorem B3139985 : Blo 2091435 3139985 := bstep (se 2 (by rfl) ⟨1177494, by rfl⟩ : syracuseStep 3139985 = 2354989) B2354989
theorem B2093323 : Blo 2091435 2093323 := bstep (se 1 (by rfl) ⟨1569992, by rfl⟩ : syracuseStep 2093323 = 3139985) B3139985
theorem B7064981 : Blo 2091435 7064981 := bbase (se 6 (by rfl) ⟨165585, by rfl⟩ : syracuseStep 7064981 = 331171) (by norm_num)
theorem B4709987 : Blo 2091435 4709987 := bstep (se 1 (by rfl) ⟨3532490, by rfl⟩ : syracuseStep 4709987 = 7064981) B7064981
theorem B3139991 : Blo 2091435 3139991 := bstep (se 1 (by rfl) ⟨2354993, by rfl⟩ : syracuseStep 3139991 = 4709987) B4709987
theorem B2093327 : Blo 2091435 2093327 := bstep (se 1 (by rfl) ⟨1569995, by rfl⟩ : syracuseStep 2093327 = 3139991) B3139991
theorem B3139997 : Blo 2091435 3139997 := bbase (se 3 (by rfl) ⟨588749, by rfl⟩ : syracuseStep 3139997 = 1177499) (by norm_num)
theorem B2093331 : Blo 2091435 2093331 := bstep (se 1 (by rfl) ⟨1569998, by rfl⟩ : syracuseStep 2093331 = 3139997) B3139997
theorem B4710005 : Blo 2091435 4710005 := bbase (se 5 (by rfl) ⟨220781, by rfl⟩ : syracuseStep 4710005 = 441563) (by norm_num)
theorem B3140003 : Blo 2091435 3140003 := bstep (se 1 (by rfl) ⟨2355002, by rfl⟩ : syracuseStep 3140003 = 4710005) B4710005
theorem B2093335 : Blo 2091435 2093335 := bstep (se 1 (by rfl) ⟨1570001, by rfl⟩ : syracuseStep 2093335 = 3140003) B3140003
theorem B2514845 : Blo 2091435 2514845 := bbase (se 3 (by rfl) ⟨471533, by rfl⟩ : syracuseStep 2514845 = 943067) (by norm_num)
theorem B6706253 : Blo 2091435 6706253 := bstep (se 3 (by rfl) ⟨1257422, by rfl⟩ : syracuseStep 6706253 = 2514845) B2514845
theorem B17883341 : Blo 2091435 17883341 := bstep (se 3 (by rfl) ⟨3353126, by rfl⟩ : syracuseStep 17883341 = 6706253) B6706253
theorem B11922227 : Blo 2091435 11922227 := bstep (se 1 (by rfl) ⟨8941670, by rfl⟩ : syracuseStep 11922227 = 17883341) B17883341
theorem B7948151 : Blo 2091435 7948151 := bstep (se 1 (by rfl) ⟨5961113, by rfl⟩ : syracuseStep 7948151 = 11922227) B11922227
theorem B5298767 : Blo 2091435 5298767 := bstep (se 1 (by rfl) ⟨3974075, by rfl⟩ : syracuseStep 5298767 = 7948151) B7948151
theorem B3532511 : Blo 2091435 3532511 := bstep (se 1 (by rfl) ⟨2649383, by rfl⟩ : syracuseStep 3532511 = 5298767) B5298767
theorem B2355007 : Blo 2091435 2355007 := bstep (se 1 (by rfl) ⟨1766255, by rfl⟩ : syracuseStep 2355007 = 3532511) B3532511
theorem B3140009 : Blo 2091435 3140009 := bstep (se 2 (by rfl) ⟨1177503, by rfl⟩ : syracuseStep 3140009 = 2355007) B2355007
theorem B2093339 : Blo 2091435 2093339 := bstep (se 1 (by rfl) ⟨1570004, by rfl⟩ : syracuseStep 2093339 = 3140009) B3140009
theorem B7948165 : Blo 2091435 7948165 := bbase (se 4 (by rfl) ⟨745140, by rfl⟩ : syracuseStep 7948165 = 1490281) (by norm_num)
theorem B10597553 : Blo 2091435 10597553 := bstep (se 2 (by rfl) ⟨3974082, by rfl⟩ : syracuseStep 10597553 = 7948165) B7948165
theorem B7065035 : Blo 2091435 7065035 := bstep (se 1 (by rfl) ⟨5298776, by rfl⟩ : syracuseStep 7065035 = 10597553) B10597553
theorem B4710023 : Blo 2091435 4710023 := bstep (se 1 (by rfl) ⟨3532517, by rfl⟩ : syracuseStep 4710023 = 7065035) B7065035
theorem B3140015 : Blo 2091435 3140015 := bstep (se 1 (by rfl) ⟨2355011, by rfl⟩ : syracuseStep 3140015 = 4710023) B4710023
theorem B2093343 : Blo 2091435 2093343 := bstep (se 1 (by rfl) ⟨1570007, by rfl⟩ : syracuseStep 2093343 = 3140015) B3140015
theorem B3140021 : Blo 2091435 3140021 := bbase (se 5 (by rfl) ⟨147188, by rfl⟩ : syracuseStep 3140021 = 294377) (by norm_num)
theorem B2093347 : Blo 2091435 2093347 := bstep (se 1 (by rfl) ⟨1570010, by rfl⟩ : syracuseStep 2093347 = 3140021) B3140021
theorem B5298797 : Blo 2091435 5298797 := bbase (se 3 (by rfl) ⟨993524, by rfl⟩ : syracuseStep 5298797 = 1987049) (by norm_num)
theorem B3532531 : Blo 2091435 3532531 := bstep (se 1 (by rfl) ⟨2649398, by rfl⟩ : syracuseStep 3532531 = 5298797) B5298797
theorem B4710041 : Blo 2091435 4710041 := bstep (se 2 (by rfl) ⟨1766265, by rfl⟩ : syracuseStep 4710041 = 3532531) B3532531
theorem B3140027 : Blo 2091435 3140027 := bstep (se 1 (by rfl) ⟨2355020, by rfl⟩ : syracuseStep 3140027 = 4710041) B4710041
theorem B2093351 : Blo 2091435 2093351 := bstep (se 1 (by rfl) ⟨1570013, by rfl⟩ : syracuseStep 2093351 = 3140027) B3140027
theorem B2355025 : Blo 2091435 2355025 := bbase (se 2 (by rfl) ⟨883134, by rfl⟩ : syracuseStep 2355025 = 1766269) (by norm_num)
theorem B3140033 : Blo 2091435 3140033 := bstep (se 2 (by rfl) ⟨1177512, by rfl⟩ : syracuseStep 3140033 = 2355025) B2355025
theorem B2093355 : Blo 2091435 2093355 := bstep (se 1 (by rfl) ⟨1570016, by rfl⟩ : syracuseStep 2093355 = 3140033) B3140033
theorem B6365765 : Blo 2091435 6365765 := bbase (se 4 (by rfl) ⟨596790, by rfl⟩ : syracuseStep 6365765 = 1193581) (by norm_num)
theorem B4243843 : Blo 2091435 4243843 := bstep (se 1 (by rfl) ⟨3182882, by rfl⟩ : syracuseStep 4243843 = 6365765) B6365765
theorem B5658457 : Blo 2091435 5658457 := bstep (se 2 (by rfl) ⟨2121921, by rfl⟩ : syracuseStep 5658457 = 4243843) B4243843
theorem B7544609 : Blo 2091435 7544609 := bstep (se 2 (by rfl) ⟨2829228, by rfl⟩ : syracuseStep 7544609 = 5658457) B5658457
theorem B5029739 : Blo 2091435 5029739 := bstep (se 1 (by rfl) ⟨3772304, by rfl⟩ : syracuseStep 5029739 = 7544609) B7544609
theorem B3353159 : Blo 2091435 3353159 := bstep (se 1 (by rfl) ⟨2514869, by rfl⟩ : syracuseStep 3353159 = 5029739) B5029739
theorem B2235439 : Blo 2091435 2235439 := bstep (se 1 (by rfl) ⟨1676579, by rfl⟩ : syracuseStep 2235439 = 3353159) B3353159
theorem B2980585 : Blo 2091435 2980585 := bstep (se 2 (by rfl) ⟨1117719, by rfl⟩ : syracuseStep 2980585 = 2235439) B2235439
theorem B3974113 : Blo 2091435 3974113 := bstep (se 2 (by rfl) ⟨1490292, by rfl⟩ : syracuseStep 3974113 = 2980585) B2980585
theorem B5298817 : Blo 2091435 5298817 := bstep (se 2 (by rfl) ⟨1987056, by rfl⟩ : syracuseStep 5298817 = 3974113) B3974113
theorem B7065089 : Blo 2091435 7065089 := bstep (se 2 (by rfl) ⟨2649408, by rfl⟩ : syracuseStep 7065089 = 5298817) B5298817
theorem B4710059 : Blo 2091435 4710059 := bstep (se 1 (by rfl) ⟨3532544, by rfl⟩ : syracuseStep 4710059 = 7065089) B7065089
theorem B3140039 : Blo 2091435 3140039 := bstep (se 1 (by rfl) ⟨2355029, by rfl⟩ : syracuseStep 3140039 = 4710059) B4710059
theorem B2093359 : Blo 2091435 2093359 := bstep (se 1 (by rfl) ⟨1570019, by rfl⟩ : syracuseStep 2093359 = 3140039) B3140039
theorem B3140045 : Blo 2091435 3140045 := bbase (se 3 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 3140045 = 1177517) (by norm_num)
theorem B2093363 : Blo 2091435 2093363 := bstep (se 1 (by rfl) ⟨1570022, by rfl⟩ : syracuseStep 2093363 = 3140045) B3140045
theorem B4710077 : Blo 2091435 4710077 := bbase (se 3 (by rfl) ⟨883139, by rfl⟩ : syracuseStep 4710077 = 1766279) (by norm_num)
theorem B3140051 : Blo 2091435 3140051 := bstep (se 1 (by rfl) ⟨2355038, by rfl⟩ : syracuseStep 3140051 = 4710077) B4710077
theorem B2093367 : Blo 2091435 2093367 := bstep (se 1 (by rfl) ⟨1570025, by rfl⟩ : syracuseStep 2093367 = 3140051) B3140051
theorem B3532565 : Blo 2091435 3532565 := bbase (se 6 (by rfl) ⟨82794, by rfl⟩ : syracuseStep 3532565 = 165589) (by norm_num)
theorem B2355043 : Blo 2091435 2355043 := bstep (se 1 (by rfl) ⟨1766282, by rfl⟩ : syracuseStep 2355043 = 3532565) B3532565
theorem B3140057 : Blo 2091435 3140057 := bstep (se 2 (by rfl) ⟨1177521, by rfl⟩ : syracuseStep 3140057 = 2355043) B2355043
theorem B2093371 : Blo 2091435 2093371 := bstep (se 1 (by rfl) ⟨1570028, by rfl⟩ : syracuseStep 2093371 = 3140057) B3140057
theorem B3398933 : Blo 2091435 3398933 := bbase (se 6 (by rfl) ⟨79662, by rfl⟩ : syracuseStep 3398933 = 159325) (by norm_num)
theorem B9063821 : Blo 2091435 9063821 := bstep (se 3 (by rfl) ⟨1699466, by rfl⟩ : syracuseStep 9063821 = 3398933) B3398933
theorem B6042547 : Blo 2091435 6042547 := bstep (se 1 (by rfl) ⟨4531910, by rfl⟩ : syracuseStep 6042547 = 9063821) B9063821
theorem B8056729 : Blo 2091435 8056729 := bstep (se 2 (by rfl) ⟨3021273, by rfl⟩ : syracuseStep 8056729 = 6042547) B6042547
theorem B10742305 : Blo 2091435 10742305 := bstep (se 2 (by rfl) ⟨4028364, by rfl⟩ : syracuseStep 10742305 = 8056729) B8056729
theorem B14323073 : Blo 2091435 14323073 := bstep (se 2 (by rfl) ⟨5371152, by rfl⟩ : syracuseStep 14323073 = 10742305) B10742305
theorem B152779445 : Blo 2091435 152779445 := bstep (se 5 (by rfl) ⟨7161536, by rfl⟩ : syracuseStep 152779445 = 14323073) B14323073
theorem B101852963 : Blo 2091435 101852963 := bstep (se 1 (by rfl) ⟨76389722, by rfl⟩ : syracuseStep 101852963 = 152779445) B152779445
theorem B67901975 : Blo 2091435 67901975 := bstep (se 1 (by rfl) ⟨50926481, by rfl⟩ : syracuseStep 67901975 = 101852963) B101852963
theorem B45267983 : Blo 2091435 45267983 := bstep (se 1 (by rfl) ⟨33950987, by rfl⟩ : syracuseStep 45267983 = 67901975) B67901975
theorem B30178655 : Blo 2091435 30178655 := bstep (se 1 (by rfl) ⟨22633991, by rfl⟩ : syracuseStep 30178655 = 45267983) B45267983
theorem B20119103 : Blo 2091435 20119103 := bstep (se 1 (by rfl) ⟨15089327, by rfl⟩ : syracuseStep 20119103 = 30178655) B30178655
theorem B13412735 : Blo 2091435 13412735 := bstep (se 1 (by rfl) ⟨10059551, by rfl⟩ : syracuseStep 13412735 = 20119103) B20119103
theorem B8941823 : Blo 2091435 8941823 := bstep (se 1 (by rfl) ⟨6706367, by rfl⟩ : syracuseStep 8941823 = 13412735) B13412735
theorem B5961215 : Blo 2091435 5961215 := bstep (se 1 (by rfl) ⟨4470911, by rfl⟩ : syracuseStep 5961215 = 8941823) B8941823
theorem B15896573 : Blo 2091435 15896573 := bstep (se 3 (by rfl) ⟨2980607, by rfl⟩ : syracuseStep 15896573 = 5961215) B5961215
theorem B10597715 : Blo 2091435 10597715 := bstep (se 1 (by rfl) ⟨7948286, by rfl⟩ : syracuseStep 10597715 = 15896573) B15896573
theorem B7065143 : Blo 2091435 7065143 := bstep (se 1 (by rfl) ⟨5298857, by rfl⟩ : syracuseStep 7065143 = 10597715) B10597715
theorem B4710095 : Blo 2091435 4710095 := bstep (se 1 (by rfl) ⟨3532571, by rfl⟩ : syracuseStep 4710095 = 7065143) B7065143
theorem B3140063 : Blo 2091435 3140063 := bstep (se 1 (by rfl) ⟨2355047, by rfl⟩ : syracuseStep 3140063 = 4710095) B4710095
theorem B2093375 : Blo 2091435 2093375 := bstep (se 1 (by rfl) ⟨1570031, by rfl⟩ : syracuseStep 2093375 = 3140063) B3140063
theorem B3140069 : Blo 2091435 3140069 := bbase (se 4 (by rfl) ⟨294381, by rfl⟩ : syracuseStep 3140069 = 588763) (by norm_num)
theorem B2093379 : Blo 2091435 2093379 := bstep (se 1 (by rfl) ⟨1570034, by rfl⟩ : syracuseStep 2093379 = 3140069) B3140069
theorem B13412789 : Blo 2091435 13412789 := bbase (se 5 (by rfl) ⟨628724, by rfl⟩ : syracuseStep 13412789 = 1257449) (by norm_num)
theorem B8941859 : Blo 2091435 8941859 := bstep (se 1 (by rfl) ⟨6706394, by rfl⟩ : syracuseStep 8941859 = 13412789) B13412789
theorem B5961239 : Blo 2091435 5961239 := bstep (se 1 (by rfl) ⟨4470929, by rfl⟩ : syracuseStep 5961239 = 8941859) B8941859
theorem B3974159 : Blo 2091435 3974159 := bstep (se 1 (by rfl) ⟨2980619, by rfl⟩ : syracuseStep 3974159 = 5961239) B5961239
theorem B2649439 : Blo 2091435 2649439 := bstep (se 1 (by rfl) ⟨1987079, by rfl⟩ : syracuseStep 2649439 = 3974159) B3974159
theorem B3532585 : Blo 2091435 3532585 := bstep (se 2 (by rfl) ⟨1324719, by rfl⟩ : syracuseStep 3532585 = 2649439) B2649439
theorem B4710113 : Blo 2091435 4710113 := bstep (se 2 (by rfl) ⟨1766292, by rfl⟩ : syracuseStep 4710113 = 3532585) B3532585
theorem B3140075 : Blo 2091435 3140075 := bstep (se 1 (by rfl) ⟨2355056, by rfl⟩ : syracuseStep 3140075 = 4710113) B4710113
theorem B2093383 : Blo 2091435 2093383 := bstep (se 1 (by rfl) ⟨1570037, by rfl⟩ : syracuseStep 2093383 = 3140075) B3140075
theorem B2355061 : Blo 2091435 2355061 := bbase (se 5 (by rfl) ⟨110393, by rfl⟩ : syracuseStep 2355061 = 220787) (by norm_num)
theorem B3140081 : Blo 2091435 3140081 := bstep (se 2 (by rfl) ⟨1177530, by rfl⟩ : syracuseStep 3140081 = 2355061) B2355061
theorem B2093387 : Blo 2091435 2093387 := bstep (se 1 (by rfl) ⟨1570040, by rfl⟩ : syracuseStep 2093387 = 3140081) B3140081
theorem B2649449 : Blo 2091435 2649449 := bbase (se 2 (by rfl) ⟨993543, by rfl⟩ : syracuseStep 2649449 = 1987087) (by norm_num)
theorem B7065197 : Blo 2091435 7065197 := bstep (se 3 (by rfl) ⟨1324724, by rfl⟩ : syracuseStep 7065197 = 2649449) B2649449
theorem B4710131 : Blo 2091435 4710131 := bstep (se 1 (by rfl) ⟨3532598, by rfl⟩ : syracuseStep 4710131 = 7065197) B7065197
theorem B3140087 : Blo 2091435 3140087 := bstep (se 1 (by rfl) ⟨2355065, by rfl⟩ : syracuseStep 3140087 = 4710131) B4710131
theorem B2093391 : Blo 2091435 2093391 := bstep (se 1 (by rfl) ⟨1570043, by rfl⟩ : syracuseStep 2093391 = 3140087) B3140087
theorem B3140093 : Blo 2091435 3140093 := bbase (se 3 (by rfl) ⟨588767, by rfl⟩ : syracuseStep 3140093 = 1177535) (by norm_num)
theorem B2093395 : Blo 2091435 2093395 := bstep (se 1 (by rfl) ⟨1570046, by rfl⟩ : syracuseStep 2093395 = 3140093) B3140093
theorem B4710149 : Blo 2091435 4710149 := bbase (se 4 (by rfl) ⟨441576, by rfl⟩ : syracuseStep 4710149 = 883153) (by norm_num)
theorem B3140099 : Blo 2091435 3140099 := bstep (se 1 (by rfl) ⟨2355074, by rfl⟩ : syracuseStep 3140099 = 4710149) B4710149
theorem B2093399 : Blo 2091435 2093399 := bstep (se 1 (by rfl) ⟨1570049, by rfl⟩ : syracuseStep 2093399 = 3140099) B3140099
theorem B3974197 : Blo 2091435 3974197 := bbase (se 5 (by rfl) ⟨186290, by rfl⟩ : syracuseStep 3974197 = 372581) (by norm_num)
theorem B5298929 : Blo 2091435 5298929 := bstep (se 2 (by rfl) ⟨1987098, by rfl⟩ : syracuseStep 5298929 = 3974197) B3974197
theorem B3532619 : Blo 2091435 3532619 := bstep (se 1 (by rfl) ⟨2649464, by rfl⟩ : syracuseStep 3532619 = 5298929) B5298929
theorem B2355079 : Blo 2091435 2355079 := bstep (se 1 (by rfl) ⟨1766309, by rfl⟩ : syracuseStep 2355079 = 3532619) B3532619
theorem B3140105 : Blo 2091435 3140105 := bstep (se 2 (by rfl) ⟨1177539, by rfl⟩ : syracuseStep 3140105 = 2355079) B2355079
theorem B2093403 : Blo 2091435 2093403 := bstep (se 1 (by rfl) ⟨1570052, by rfl⟩ : syracuseStep 2093403 = 3140105) B3140105
theorem B10597877 : Blo 2091435 10597877 := bbase (se 5 (by rfl) ⟨496775, by rfl⟩ : syracuseStep 10597877 = 993551) (by norm_num)
theorem B7065251 : Blo 2091435 7065251 := bstep (se 1 (by rfl) ⟨5298938, by rfl⟩ : syracuseStep 7065251 = 10597877) B10597877
theorem B4710167 : Blo 2091435 4710167 := bstep (se 1 (by rfl) ⟨3532625, by rfl⟩ : syracuseStep 4710167 = 7065251) B7065251
theorem B3140111 : Blo 2091435 3140111 := bstep (se 1 (by rfl) ⟨2355083, by rfl⟩ : syracuseStep 3140111 = 4710167) B4710167
theorem B2093407 : Blo 2091435 2093407 := bstep (se 1 (by rfl) ⟨1570055, by rfl⟩ : syracuseStep 2093407 = 3140111) B3140111
theorem B3140117 : Blo 2091435 3140117 := bbase (se 6 (by rfl) ⟨73596, by rfl⟩ : syracuseStep 3140117 = 147193) (by norm_num)
theorem B2093411 : Blo 2091435 2093411 := bstep (se 1 (by rfl) ⟨1570058, by rfl⟩ : syracuseStep 2093411 = 3140117) B3140117
theorem B17883989 : Blo 2091435 17883989 := bbase (se 9 (by rfl) ⟨52394, by rfl⟩ : syracuseStep 17883989 = 104789) (by norm_num)
theorem B11922659 : Blo 2091435 11922659 := bstep (se 1 (by rfl) ⟨8941994, by rfl⟩ : syracuseStep 11922659 = 17883989) B17883989
theorem B7948439 : Blo 2091435 7948439 := bstep (se 1 (by rfl) ⟨5961329, by rfl⟩ : syracuseStep 7948439 = 11922659) B11922659
theorem B5298959 : Blo 2091435 5298959 := bstep (se 1 (by rfl) ⟨3974219, by rfl⟩ : syracuseStep 5298959 = 7948439) B7948439
theorem B3532639 : Blo 2091435 3532639 := bstep (se 1 (by rfl) ⟨2649479, by rfl⟩ : syracuseStep 3532639 = 5298959) B5298959
theorem B4710185 : Blo 2091435 4710185 := bstep (se 2 (by rfl) ⟨1766319, by rfl⟩ : syracuseStep 4710185 = 3532639) B3532639
theorem B3140123 : Blo 2091435 3140123 := bstep (se 1 (by rfl) ⟨2355092, by rfl⟩ : syracuseStep 3140123 = 4710185) B4710185
theorem B2093415 : Blo 2091435 2093415 := bstep (se 1 (by rfl) ⟨1570061, by rfl⟩ : syracuseStep 2093415 = 3140123) B3140123
theorem B2355097 : Blo 2091435 2355097 := bbase (se 2 (by rfl) ⟨883161, by rfl⟩ : syracuseStep 2355097 = 1766323) (by norm_num)
theorem B3140129 : Blo 2091435 3140129 := bstep (se 2 (by rfl) ⟨1177548, by rfl⟩ : syracuseStep 3140129 = 2355097) B2355097
theorem B2093419 : Blo 2091435 2093419 := bstep (se 1 (by rfl) ⟨1570064, by rfl⟩ : syracuseStep 2093419 = 3140129) B3140129
theorem B7948469 : Blo 2091435 7948469 := bbase (se 5 (by rfl) ⟨372584, by rfl⟩ : syracuseStep 7948469 = 745169) (by norm_num)
theorem B5298979 : Blo 2091435 5298979 := bstep (se 1 (by rfl) ⟨3974234, by rfl⟩ : syracuseStep 5298979 = 7948469) B7948469
theorem B7065305 : Blo 2091435 7065305 := bstep (se 2 (by rfl) ⟨2649489, by rfl⟩ : syracuseStep 7065305 = 5298979) B5298979
theorem B4710203 : Blo 2091435 4710203 := bstep (se 1 (by rfl) ⟨3532652, by rfl⟩ : syracuseStep 4710203 = 7065305) B7065305
theorem B3140135 : Blo 2091435 3140135 := bstep (se 1 (by rfl) ⟨2355101, by rfl⟩ : syracuseStep 3140135 = 4710203) B4710203
theorem B2093423 : Blo 2091435 2093423 := bstep (se 1 (by rfl) ⟨1570067, by rfl⟩ : syracuseStep 2093423 = 3140135) B3140135
theorem B3140141 : Blo 2091435 3140141 := bbase (se 3 (by rfl) ⟨588776, by rfl⟩ : syracuseStep 3140141 = 1177553) (by norm_num)
theorem B2093427 : Blo 2091435 2093427 := bstep (se 1 (by rfl) ⟨1570070, by rfl⟩ : syracuseStep 2093427 = 3140141) B3140141
theorem B4710221 : Blo 2091435 4710221 := bbase (se 3 (by rfl) ⟨883166, by rfl⟩ : syracuseStep 4710221 = 1766333) (by norm_num)
theorem B3140147 : Blo 2091435 3140147 := bstep (se 1 (by rfl) ⟨2355110, by rfl⟩ : syracuseStep 3140147 = 4710221) B4710221
theorem B2093431 : Blo 2091435 2093431 := bstep (se 1 (by rfl) ⟨1570073, by rfl⟩ : syracuseStep 2093431 = 3140147) B3140147
theorem B2649505 : Blo 2091435 2649505 := bbase (se 2 (by rfl) ⟨993564, by rfl⟩ : syracuseStep 2649505 = 1987129) (by norm_num)
theorem B3532673 : Blo 2091435 3532673 := bstep (se 2 (by rfl) ⟨1324752, by rfl⟩ : syracuseStep 3532673 = 2649505) B2649505
theorem B2355115 : Blo 2091435 2355115 := bstep (se 1 (by rfl) ⟨1766336, by rfl⟩ : syracuseStep 2355115 = 3532673) B3532673
theorem B3140153 : Blo 2091435 3140153 := bstep (se 2 (by rfl) ⟨1177557, by rfl⟩ : syracuseStep 3140153 = 2355115) B2355115
theorem B2093435 : Blo 2091435 2093435 := bstep (se 1 (by rfl) ⟨1570076, by rfl⟩ : syracuseStep 2093435 = 3140153) B3140153
theorem C0 (j : ℕ) (h1 : 522858 ≤ j) (h2 : j ≤ 523358) : Blo 2091435 (4 * j + 3) := by
  interval_cases j
  · exact B2091435
  · exact B2091439
  · exact B2091443
  · exact B2091447
  · exact B2091451
  · exact B2091455
  · exact B2091459
  · exact B2091463
  · exact B2091467
  · exact B2091471
  · exact B2091475
  · exact B2091479
  · exact B2091483
  · exact B2091487
  · exact B2091491
  · exact B2091495
  · exact B2091499
  · exact B2091503
  · exact B2091507
  · exact B2091511
  · exact B2091515
  · exact B2091519
  · exact B2091523
  · exact B2091527
  · exact B2091531
  · exact B2091535
  · exact B2091539
  · exact B2091543
  · exact B2091547
  · exact B2091551
  · exact B2091555
  · exact B2091559
  · exact B2091563
  · exact B2091567
  · exact B2091571
  · exact B2091575
  · exact B2091579
  · exact B2091583
  · exact B2091587
  · exact B2091591
  · exact B2091595
  · exact B2091599
  · exact B2091603
  · exact B2091607
  · exact B2091611
  · exact B2091615
  · exact B2091619
  · exact B2091623
  · exact B2091627
  · exact B2091631
  · exact B2091635
  · exact B2091639
  · exact B2091643
  · exact B2091647
  · exact B2091651
  · exact B2091655
  · exact B2091659
  · exact B2091663
  · exact B2091667
  · exact B2091671
  · exact B2091675
  · exact B2091679
  · exact B2091683
  · exact B2091687
  · exact B2091691
  · exact B2091695
  · exact B2091699
  · exact B2091703
  · exact B2091707
  · exact B2091711
  · exact B2091715
  · exact B2091719
  · exact B2091723
  · exact B2091727
  · exact B2091731
  · exact B2091735
  · exact B2091739
  · exact B2091743
  · exact B2091747
  · exact B2091751
  · exact B2091755
  · exact B2091759
  · exact B2091763
  · exact B2091767
  · exact B2091771
  · exact B2091775
  · exact B2091779
  · exact B2091783
  · exact B2091787
  · exact B2091791
  · exact B2091795
  · exact B2091799
  · exact B2091803
  · exact B2091807
  · exact B2091811
  · exact B2091815
  · exact B2091819
  · exact B2091823
  · exact B2091827
  · exact B2091831
  · exact B2091835
  · exact B2091839
  · exact B2091843
  · exact B2091847
  · exact B2091851
  · exact B2091855
  · exact B2091859
  · exact B2091863
  · exact B2091867
  · exact B2091871
  · exact B2091875
  · exact B2091879
  · exact B2091883
  · exact B2091887
  · exact B2091891
  · exact B2091895
  · exact B2091899
  · exact B2091903
  · exact B2091907
  · exact B2091911
  · exact B2091915
  · exact B2091919
  · exact B2091923
  · exact B2091927
  · exact B2091931
  · exact B2091935
  · exact B2091939
  · exact B2091943
  · exact B2091947
  · exact B2091951
  · exact B2091955
  · exact B2091959
  · exact B2091963
  · exact B2091967
  · exact B2091971
  · exact B2091975
  · exact B2091979
  · exact B2091983
  · exact B2091987
  · exact B2091991
  · exact B2091995
  · exact B2091999
  · exact B2092003
  · exact B2092007
  · exact B2092011
  · exact B2092015
  · exact B2092019
  · exact B2092023
  · exact B2092027
  · exact B2092031
  · exact B2092035
  · exact B2092039
  · exact B2092043
  · exact B2092047
  · exact B2092051
  · exact B2092055
  · exact B2092059
  · exact B2092063
  · exact B2092067
  · exact B2092071
  · exact B2092075
  · exact B2092079
  · exact B2092083
  · exact B2092087
  · exact B2092091
  · exact B2092095
  · exact B2092099
  · exact B2092103
  · exact B2092107
  · exact B2092111
  · exact B2092115
  · exact B2092119
  · exact B2092123
  · exact B2092127
  · exact B2092131
  · exact B2092135
  · exact B2092139
  · exact B2092143
  · exact B2092147
  · exact B2092151
  · exact B2092155
  · exact B2092159
  · exact B2092163
  · exact B2092167
  · exact B2092171
  · exact B2092175
  · exact B2092179
  · exact B2092183
  · exact B2092187
  · exact B2092191
  · exact B2092195
  · exact B2092199
  · exact B2092203
  · exact B2092207
  · exact B2092211
  · exact B2092215
  · exact B2092219
  · exact B2092223
  · exact B2092227
  · exact B2092231
  · exact B2092235
  · exact B2092239
  · exact B2092243
  · exact B2092247
  · exact B2092251
  · exact B2092255
  · exact B2092259
  · exact B2092263
  · exact B2092267
  · exact B2092271
  · exact B2092275
  · exact B2092279
  · exact B2092283
  · exact B2092287
  · exact B2092291
  · exact B2092295
  · exact B2092299
  · exact B2092303
  · exact B2092307
  · exact B2092311
  · exact B2092315
  · exact B2092319
  · exact B2092323
  · exact B2092327
  · exact B2092331
  · exact B2092335
  · exact B2092339
  · exact B2092343
  · exact B2092347
  · exact B2092351
  · exact B2092355
  · exact B2092359
  · exact B2092363
  · exact B2092367
  · exact B2092371
  · exact B2092375
  · exact B2092379
  · exact B2092383
  · exact B2092387
  · exact B2092391
  · exact B2092395
  · exact B2092399
  · exact B2092403
  · exact B2092407
  · exact B2092411
  · exact B2092415
  · exact B2092419
  · exact B2092423
  · exact B2092427
  · exact B2092431
  · exact B2092435
  · exact B2092439
  · exact B2092443
  · exact B2092447
  · exact B2092451
  · exact B2092455
  · exact B2092459
  · exact B2092463
  · exact B2092467
  · exact B2092471
  · exact B2092475
  · exact B2092479
  · exact B2092483
  · exact B2092487
  · exact B2092491
  · exact B2092495
  · exact B2092499
  · exact B2092503
  · exact B2092507
  · exact B2092511
  · exact B2092515
  · exact B2092519
  · exact B2092523
  · exact B2092527
  · exact B2092531
  · exact B2092535
  · exact B2092539
  · exact B2092543
  · exact B2092547
  · exact B2092551
  · exact B2092555
  · exact B2092559
  · exact B2092563
  · exact B2092567
  · exact B2092571
  · exact B2092575
  · exact B2092579
  · exact B2092583
  · exact B2092587
  · exact B2092591
  · exact B2092595
  · exact B2092599
  · exact B2092603
  · exact B2092607
  · exact B2092611
  · exact B2092615
  · exact B2092619
  · exact B2092623
  · exact B2092627
  · exact B2092631
  · exact B2092635
  · exact B2092639
  · exact B2092643
  · exact B2092647
  · exact B2092651
  · exact B2092655
  · exact B2092659
  · exact B2092663
  · exact B2092667
  · exact B2092671
  · exact B2092675
  · exact B2092679
  · exact B2092683
  · exact B2092687
  · exact B2092691
  · exact B2092695
  · exact B2092699
  · exact B2092703
  · exact B2092707
  · exact B2092711
  · exact B2092715
  · exact B2092719
  · exact B2092723
  · exact B2092727
  · exact B2092731
  · exact B2092735
  · exact B2092739
  · exact B2092743
  · exact B2092747
  · exact B2092751
  · exact B2092755
  · exact B2092759
  · exact B2092763
  · exact B2092767
  · exact B2092771
  · exact B2092775
  · exact B2092779
  · exact B2092783
  · exact B2092787
  · exact B2092791
  · exact B2092795
  · exact B2092799
  · exact B2092803
  · exact B2092807
  · exact B2092811
  · exact B2092815
  · exact B2092819
  · exact B2092823
  · exact B2092827
  · exact B2092831
  · exact B2092835
  · exact B2092839
  · exact B2092843
  · exact B2092847
  · exact B2092851
  · exact B2092855
  · exact B2092859
  · exact B2092863
  · exact B2092867
  · exact B2092871
  · exact B2092875
  · exact B2092879
  · exact B2092883
  · exact B2092887
  · exact B2092891
  · exact B2092895
  · exact B2092899
  · exact B2092903
  · exact B2092907
  · exact B2092911
  · exact B2092915
  · exact B2092919
  · exact B2092923
  · exact B2092927
  · exact B2092931
  · exact B2092935
  · exact B2092939
  · exact B2092943
  · exact B2092947
  · exact B2092951
  · exact B2092955
  · exact B2092959
  · exact B2092963
  · exact B2092967
  · exact B2092971
  · exact B2092975
  · exact B2092979
  · exact B2092983
  · exact B2092987
  · exact B2092991
  · exact B2092995
  · exact B2092999
  · exact B2093003
  · exact B2093007
  · exact B2093011
  · exact B2093015
  · exact B2093019
  · exact B2093023
  · exact B2093027
  · exact B2093031
  · exact B2093035
  · exact B2093039
  · exact B2093043
  · exact B2093047
  · exact B2093051
  · exact B2093055
  · exact B2093059
  · exact B2093063
  · exact B2093067
  · exact B2093071
  · exact B2093075
  · exact B2093079
  · exact B2093083
  · exact B2093087
  · exact B2093091
  · exact B2093095
  · exact B2093099
  · exact B2093103
  · exact B2093107
  · exact B2093111
  · exact B2093115
  · exact B2093119
  · exact B2093123
  · exact B2093127
  · exact B2093131
  · exact B2093135
  · exact B2093139
  · exact B2093143
  · exact B2093147
  · exact B2093151
  · exact B2093155
  · exact B2093159
  · exact B2093163
  · exact B2093167
  · exact B2093171
  · exact B2093175
  · exact B2093179
  · exact B2093183
  · exact B2093187
  · exact B2093191
  · exact B2093195
  · exact B2093199
  · exact B2093203
  · exact B2093207
  · exact B2093211
  · exact B2093215
  · exact B2093219
  · exact B2093223
  · exact B2093227
  · exact B2093231
  · exact B2093235
  · exact B2093239
  · exact B2093243
  · exact B2093247
  · exact B2093251
  · exact B2093255
  · exact B2093259
  · exact B2093263
  · exact B2093267
  · exact B2093271
  · exact B2093275
  · exact B2093279
  · exact B2093283
  · exact B2093287
  · exact B2093291
  · exact B2093295
  · exact B2093299
  · exact B2093303
  · exact B2093307
  · exact B2093311
  · exact B2093315
  · exact B2093319
  · exact B2093323
  · exact B2093327
  · exact B2093331
  · exact B2093335
  · exact B2093339
  · exact B2093343
  · exact B2093347
  · exact B2093351
  · exact B2093355
  · exact B2093359
  · exact B2093363
  · exact B2093367
  · exact B2093371
  · exact B2093375
  · exact B2093379
  · exact B2093383
  · exact B2093387
  · exact B2093391
  · exact B2093395
  · exact B2093399
  · exact B2093403
  · exact B2093407
  · exact B2093411
  · exact B2093415
  · exact B2093419
  · exact B2093423
  · exact B2093427
  · exact B2093431
  · exact B2093435
theorem solution (m : ℕ) (hlo : 2091435 ≤ m) (hhi : m ≤ 2093435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 522858 ≤ j := by omega
    have hj2 : j ≤ 523358 := by omega
    have hb : Blo 2091435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
