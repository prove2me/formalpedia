-- Prove2me | solution 1 for syracuse_descends_range_2083435_2085435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:18.343249+00:00
-- url     : https://prove2.me/submissions/dad8fce4-2f3e-426d-a71b-c594c44b2685

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

theorem B2343865 : Blo 2083435 2343865 := bbase (se 2 (by rfl) ⟨878949, by rfl⟩ : syracuseStep 2343865 = 1757899) (by norm_num)
theorem B3125153 : Blo 2083435 3125153 := bstep (se 2 (by rfl) ⟨1171932, by rfl⟩ : syracuseStep 3125153 = 2343865) B2343865
theorem B2083435 : Blo 2083435 2083435 := bstep (se 1 (by rfl) ⟨1562576, by rfl⟩ : syracuseStep 2083435 = 3125153) B3125153
theorem B2375849 : Blo 2083435 2375849 := bbase (se 2 (by rfl) ⟨890943, by rfl⟩ : syracuseStep 2375849 = 1781887) (by norm_num)
theorem B6335597 : Blo 2083435 6335597 := bstep (se 3 (by rfl) ⟨1187924, by rfl⟩ : syracuseStep 6335597 = 2375849) B2375849
theorem B16894925 : Blo 2083435 16894925 := bstep (se 3 (by rfl) ⟨3167798, by rfl⟩ : syracuseStep 16894925 = 6335597) B6335597
theorem B11263283 : Blo 2083435 11263283 := bstep (se 1 (by rfl) ⟨8447462, by rfl⟩ : syracuseStep 11263283 = 16894925) B16894925
theorem B7508855 : Blo 2083435 7508855 := bstep (se 1 (by rfl) ⟨5631641, by rfl⟩ : syracuseStep 7508855 = 11263283) B11263283
theorem B5005903 : Blo 2083435 5005903 := bstep (se 1 (by rfl) ⟨3754427, by rfl⟩ : syracuseStep 5005903 = 7508855) B7508855
theorem B6674537 : Blo 2083435 6674537 := bstep (se 2 (by rfl) ⟨2502951, by rfl⟩ : syracuseStep 6674537 = 5005903) B5005903
theorem B4449691 : Blo 2083435 4449691 := bstep (se 1 (by rfl) ⟨3337268, by rfl⟩ : syracuseStep 4449691 = 6674537) B6674537
theorem B5932921 : Blo 2083435 5932921 := bstep (se 2 (by rfl) ⟨2224845, by rfl⟩ : syracuseStep 5932921 = 4449691) B4449691
theorem B7910561 : Blo 2083435 7910561 := bstep (se 2 (by rfl) ⟨2966460, by rfl⟩ : syracuseStep 7910561 = 5932921) B5932921
theorem B5273707 : Blo 2083435 5273707 := bstep (se 1 (by rfl) ⟨3955280, by rfl⟩ : syracuseStep 5273707 = 7910561) B7910561
theorem B7031609 : Blo 2083435 7031609 := bstep (se 2 (by rfl) ⟨2636853, by rfl⟩ : syracuseStep 7031609 = 5273707) B5273707
theorem B4687739 : Blo 2083435 4687739 := bstep (se 1 (by rfl) ⟨3515804, by rfl⟩ : syracuseStep 4687739 = 7031609) B7031609
theorem B3125159 : Blo 2083435 3125159 := bstep (se 1 (by rfl) ⟨2343869, by rfl⟩ : syracuseStep 3125159 = 4687739) B4687739
theorem B2083439 : Blo 2083435 2083439 := bstep (se 1 (by rfl) ⟨1562579, by rfl⟩ : syracuseStep 2083439 = 3125159) B3125159
theorem B3125165 : Blo 2083435 3125165 := bbase (se 3 (by rfl) ⟨585968, by rfl⟩ : syracuseStep 3125165 = 1171937) (by norm_num)
theorem B2083443 : Blo 2083435 2083443 := bstep (se 1 (by rfl) ⟨1562582, by rfl⟩ : syracuseStep 2083443 = 3125165) B3125165
theorem B4687757 : Blo 2083435 4687757 := bbase (se 3 (by rfl) ⟨878954, by rfl⟩ : syracuseStep 4687757 = 1757909) (by norm_num)
theorem B3125171 : Blo 2083435 3125171 := bstep (se 1 (by rfl) ⟨2343878, by rfl⟩ : syracuseStep 3125171 = 4687757) B4687757
theorem B2083447 : Blo 2083435 2083447 := bstep (se 1 (by rfl) ⟨1562585, by rfl⟩ : syracuseStep 2083447 = 3125171) B3125171
theorem B2636869 : Blo 2083435 2636869 := bbase (se 4 (by rfl) ⟨247206, by rfl⟩ : syracuseStep 2636869 = 494413) (by norm_num)
theorem B3515825 : Blo 2083435 3515825 := bstep (se 2 (by rfl) ⟨1318434, by rfl⟩ : syracuseStep 3515825 = 2636869) B2636869
theorem B2343883 : Blo 2083435 2343883 := bstep (se 1 (by rfl) ⟨1757912, by rfl⟩ : syracuseStep 2343883 = 3515825) B3515825
theorem B3125177 : Blo 2083435 3125177 := bstep (se 2 (by rfl) ⟨1171941, by rfl⟩ : syracuseStep 3125177 = 2343883) B2343883
theorem B2083451 : Blo 2083435 2083451 := bstep (se 1 (by rfl) ⟨1562588, by rfl⟩ : syracuseStep 2083451 = 3125177) B3125177
theorem B19006933 : Blo 2083435 19006933 := bbase (se 7 (by rfl) ⟨222737, by rfl⟩ : syracuseStep 19006933 = 445475) (by norm_num)
theorem B25342577 : Blo 2083435 25342577 := bstep (se 2 (by rfl) ⟨9503466, by rfl⟩ : syracuseStep 25342577 = 19006933) B19006933
theorem B16895051 : Blo 2083435 16895051 := bstep (se 1 (by rfl) ⟨12671288, by rfl⟩ : syracuseStep 16895051 = 25342577) B25342577
theorem B11263367 : Blo 2083435 11263367 := bstep (se 1 (by rfl) ⟨8447525, by rfl⟩ : syracuseStep 11263367 = 16895051) B16895051
theorem B7508911 : Blo 2083435 7508911 := bstep (se 1 (by rfl) ⟨5631683, by rfl⟩ : syracuseStep 7508911 = 11263367) B11263367
theorem B10011881 : Blo 2083435 10011881 := bstep (se 2 (by rfl) ⟨3754455, by rfl⟩ : syracuseStep 10011881 = 7508911) B7508911
theorem B26698349 : Blo 2083435 26698349 := bstep (se 3 (by rfl) ⟨5005940, by rfl⟩ : syracuseStep 26698349 = 10011881) B10011881
theorem B17798899 : Blo 2083435 17798899 := bstep (se 1 (by rfl) ⟨13349174, by rfl⟩ : syracuseStep 17798899 = 26698349) B26698349
theorem B23731865 : Blo 2083435 23731865 := bstep (se 2 (by rfl) ⟨8899449, by rfl⟩ : syracuseStep 23731865 = 17798899) B17798899
theorem B15821243 : Blo 2083435 15821243 := bstep (se 1 (by rfl) ⟨11865932, by rfl⟩ : syracuseStep 15821243 = 23731865) B23731865
theorem B10547495 : Blo 2083435 10547495 := bstep (se 1 (by rfl) ⟨7910621, by rfl⟩ : syracuseStep 10547495 = 15821243) B15821243
theorem B7031663 : Blo 2083435 7031663 := bstep (se 1 (by rfl) ⟨5273747, by rfl⟩ : syracuseStep 7031663 = 10547495) B10547495
theorem B4687775 : Blo 2083435 4687775 := bstep (se 1 (by rfl) ⟨3515831, by rfl⟩ : syracuseStep 4687775 = 7031663) B7031663
theorem B3125183 : Blo 2083435 3125183 := bstep (se 1 (by rfl) ⟨2343887, by rfl⟩ : syracuseStep 3125183 = 4687775) B4687775
theorem B2083455 : Blo 2083435 2083455 := bstep (se 1 (by rfl) ⟨1562591, by rfl⟩ : syracuseStep 2083455 = 3125183) B3125183
theorem B3125189 : Blo 2083435 3125189 := bbase (se 4 (by rfl) ⟨292986, by rfl⟩ : syracuseStep 3125189 = 585973) (by norm_num)
theorem B2083459 : Blo 2083435 2083459 := bstep (se 1 (by rfl) ⟨1562594, by rfl⟩ : syracuseStep 2083459 = 3125189) B3125189
theorem B3515845 : Blo 2083435 3515845 := bbase (se 4 (by rfl) ⟨329610, by rfl⟩ : syracuseStep 3515845 = 659221) (by norm_num)
theorem B4687793 : Blo 2083435 4687793 := bstep (se 2 (by rfl) ⟨1757922, by rfl⟩ : syracuseStep 4687793 = 3515845) B3515845
theorem B3125195 : Blo 2083435 3125195 := bstep (se 1 (by rfl) ⟨2343896, by rfl⟩ : syracuseStep 3125195 = 4687793) B4687793
theorem B2083463 : Blo 2083435 2083463 := bstep (se 1 (by rfl) ⟨1562597, by rfl⟩ : syracuseStep 2083463 = 3125195) B3125195
theorem B2343901 : Blo 2083435 2343901 := bbase (se 3 (by rfl) ⟨439481, by rfl⟩ : syracuseStep 2343901 = 878963) (by norm_num)
theorem B3125201 : Blo 2083435 3125201 := bstep (se 2 (by rfl) ⟨1171950, by rfl⟩ : syracuseStep 3125201 = 2343901) B2343901
theorem B2083467 : Blo 2083435 2083467 := bstep (se 1 (by rfl) ⟨1562600, by rfl⟩ : syracuseStep 2083467 = 3125201) B3125201
theorem B7031717 : Blo 2083435 7031717 := bbase (se 4 (by rfl) ⟨659223, by rfl⟩ : syracuseStep 7031717 = 1318447) (by norm_num)
theorem B4687811 : Blo 2083435 4687811 := bstep (se 1 (by rfl) ⟨3515858, by rfl⟩ : syracuseStep 4687811 = 7031717) B7031717
theorem B3125207 : Blo 2083435 3125207 := bstep (se 1 (by rfl) ⟨2343905, by rfl⟩ : syracuseStep 3125207 = 4687811) B4687811
theorem B2083471 : Blo 2083435 2083471 := bstep (se 1 (by rfl) ⟨1562603, by rfl⟩ : syracuseStep 2083471 = 3125207) B3125207
theorem B3125213 : Blo 2083435 3125213 := bbase (se 3 (by rfl) ⟨585977, by rfl⟩ : syracuseStep 3125213 = 1171955) (by norm_num)
theorem B2083475 : Blo 2083435 2083475 := bstep (se 1 (by rfl) ⟨1562606, by rfl⟩ : syracuseStep 2083475 = 3125213) B3125213
theorem B4687829 : Blo 2083435 4687829 := bbase (se 7 (by rfl) ⟨54935, by rfl⟩ : syracuseStep 4687829 = 109871) (by norm_num)
theorem B3125219 : Blo 2083435 3125219 := bstep (se 1 (by rfl) ⟨2343914, by rfl⟩ : syracuseStep 3125219 = 4687829) B4687829
theorem B2083479 : Blo 2083435 2083479 := bstep (se 1 (by rfl) ⟨1562609, by rfl⟩ : syracuseStep 2083479 = 3125219) B3125219
theorem B4223821 : Blo 2083435 4223821 := bbase (se 3 (by rfl) ⟨791966, by rfl⟩ : syracuseStep 4223821 = 1583933) (by norm_num)
theorem B5631761 : Blo 2083435 5631761 := bstep (se 2 (by rfl) ⟨2111910, by rfl⟩ : syracuseStep 5631761 = 4223821) B4223821
theorem B3754507 : Blo 2083435 3754507 := bstep (se 1 (by rfl) ⟨2815880, by rfl⟩ : syracuseStep 3754507 = 5631761) B5631761
theorem B5006009 : Blo 2083435 5006009 := bstep (se 2 (by rfl) ⟨1877253, by rfl⟩ : syracuseStep 5006009 = 3754507) B3754507
theorem B13349357 : Blo 2083435 13349357 := bstep (se 3 (by rfl) ⟨2503004, by rfl⟩ : syracuseStep 13349357 = 5006009) B5006009
theorem B8899571 : Blo 2083435 8899571 := bstep (se 1 (by rfl) ⟨6674678, by rfl⟩ : syracuseStep 8899571 = 13349357) B13349357
theorem B5933047 : Blo 2083435 5933047 := bstep (se 1 (by rfl) ⟨4449785, by rfl⟩ : syracuseStep 5933047 = 8899571) B8899571
theorem B7910729 : Blo 2083435 7910729 := bstep (se 2 (by rfl) ⟨2966523, by rfl⟩ : syracuseStep 7910729 = 5933047) B5933047
theorem B5273819 : Blo 2083435 5273819 := bstep (se 1 (by rfl) ⟨3955364, by rfl⟩ : syracuseStep 5273819 = 7910729) B7910729
theorem B3515879 : Blo 2083435 3515879 := bstep (se 1 (by rfl) ⟨2636909, by rfl⟩ : syracuseStep 3515879 = 5273819) B5273819
theorem B2343919 : Blo 2083435 2343919 := bstep (se 1 (by rfl) ⟨1757939, by rfl⟩ : syracuseStep 2343919 = 3515879) B3515879
theorem B3125225 : Blo 2083435 3125225 := bstep (se 2 (by rfl) ⟨1171959, by rfl⟩ : syracuseStep 3125225 = 2343919) B2343919
theorem B2083483 : Blo 2083435 2083483 := bstep (se 1 (by rfl) ⟨1562612, by rfl⟩ : syracuseStep 2083483 = 3125225) B3125225
theorem B2503009 : Blo 2083435 2503009 := bbase (se 2 (by rfl) ⟨938628, by rfl⟩ : syracuseStep 2503009 = 1877257) (by norm_num)
theorem B3337345 : Blo 2083435 3337345 := bstep (se 2 (by rfl) ⟨1251504, by rfl⟩ : syracuseStep 3337345 = 2503009) B2503009
theorem B17799173 : Blo 2083435 17799173 := bstep (se 4 (by rfl) ⟨1668672, by rfl⟩ : syracuseStep 17799173 = 3337345) B3337345
theorem B11866115 : Blo 2083435 11866115 := bstep (se 1 (by rfl) ⟨8899586, by rfl⟩ : syracuseStep 11866115 = 17799173) B17799173
theorem B7910743 : Blo 2083435 7910743 := bstep (se 1 (by rfl) ⟨5933057, by rfl⟩ : syracuseStep 7910743 = 11866115) B11866115
theorem B10547657 : Blo 2083435 10547657 := bstep (se 2 (by rfl) ⟨3955371, by rfl⟩ : syracuseStep 10547657 = 7910743) B7910743
theorem B7031771 : Blo 2083435 7031771 := bstep (se 1 (by rfl) ⟨5273828, by rfl⟩ : syracuseStep 7031771 = 10547657) B10547657
theorem B4687847 : Blo 2083435 4687847 := bstep (se 1 (by rfl) ⟨3515885, by rfl⟩ : syracuseStep 4687847 = 7031771) B7031771
theorem B3125231 : Blo 2083435 3125231 := bstep (se 1 (by rfl) ⟨2343923, by rfl⟩ : syracuseStep 3125231 = 4687847) B4687847
theorem B2083487 : Blo 2083435 2083487 := bstep (se 1 (by rfl) ⟨1562615, by rfl⟩ : syracuseStep 2083487 = 3125231) B3125231
theorem B3125237 : Blo 2083435 3125237 := bbase (se 5 (by rfl) ⟨146495, by rfl⟩ : syracuseStep 3125237 = 292991) (by norm_num)
theorem B2083491 : Blo 2083435 2083491 := bstep (se 1 (by rfl) ⟨1562618, by rfl⟩ : syracuseStep 2083491 = 3125237) B3125237
theorem B3167885 : Blo 2083435 3167885 := bbase (se 3 (by rfl) ⟨593978, by rfl⟩ : syracuseStep 3167885 = 1187957) (by norm_num)
theorem B2111923 : Blo 2083435 2111923 := bstep (se 1 (by rfl) ⟨1583942, by rfl⟩ : syracuseStep 2111923 = 3167885) B3167885
theorem B2815897 : Blo 2083435 2815897 := bstep (se 2 (by rfl) ⟨1055961, by rfl⟩ : syracuseStep 2815897 = 2111923) B2111923
theorem B3754529 : Blo 2083435 3754529 := bstep (se 2 (by rfl) ⟨1407948, by rfl⟩ : syracuseStep 3754529 = 2815897) B2815897
theorem B2503019 : Blo 2083435 2503019 := bstep (se 1 (by rfl) ⟨1877264, by rfl⟩ : syracuseStep 2503019 = 3754529) B3754529
theorem B6674717 : Blo 2083435 6674717 := bstep (se 3 (by rfl) ⟨1251509, by rfl⟩ : syracuseStep 6674717 = 2503019) B2503019
theorem B4449811 : Blo 2083435 4449811 := bstep (se 1 (by rfl) ⟨3337358, by rfl⟩ : syracuseStep 4449811 = 6674717) B6674717
theorem B5933081 : Blo 2083435 5933081 := bstep (se 2 (by rfl) ⟨2224905, by rfl⟩ : syracuseStep 5933081 = 4449811) B4449811
theorem B3955387 : Blo 2083435 3955387 := bstep (se 1 (by rfl) ⟨2966540, by rfl⟩ : syracuseStep 3955387 = 5933081) B5933081
theorem B5273849 : Blo 2083435 5273849 := bstep (se 2 (by rfl) ⟨1977693, by rfl⟩ : syracuseStep 5273849 = 3955387) B3955387
theorem B3515899 : Blo 2083435 3515899 := bstep (se 1 (by rfl) ⟨2636924, by rfl⟩ : syracuseStep 3515899 = 5273849) B5273849
theorem B4687865 : Blo 2083435 4687865 := bstep (se 2 (by rfl) ⟨1757949, by rfl⟩ : syracuseStep 4687865 = 3515899) B3515899
theorem B3125243 : Blo 2083435 3125243 := bstep (se 1 (by rfl) ⟨2343932, by rfl⟩ : syracuseStep 3125243 = 4687865) B4687865
theorem B2083495 : Blo 2083435 2083495 := bstep (se 1 (by rfl) ⟨1562621, by rfl⟩ : syracuseStep 2083495 = 3125243) B3125243
theorem B2343937 : Blo 2083435 2343937 := bbase (se 2 (by rfl) ⟨878976, by rfl⟩ : syracuseStep 2343937 = 1757953) (by norm_num)
theorem B3125249 : Blo 2083435 3125249 := bstep (se 2 (by rfl) ⟨1171968, by rfl⟩ : syracuseStep 3125249 = 2343937) B2343937
theorem B2083499 : Blo 2083435 2083499 := bstep (se 1 (by rfl) ⟨1562624, by rfl⟩ : syracuseStep 2083499 = 3125249) B3125249
theorem B5273869 : Blo 2083435 5273869 := bbase (se 3 (by rfl) ⟨988850, by rfl⟩ : syracuseStep 5273869 = 1977701) (by norm_num)
theorem B7031825 : Blo 2083435 7031825 := bstep (se 2 (by rfl) ⟨2636934, by rfl⟩ : syracuseStep 7031825 = 5273869) B5273869
theorem B4687883 : Blo 2083435 4687883 := bstep (se 1 (by rfl) ⟨3515912, by rfl⟩ : syracuseStep 4687883 = 7031825) B7031825
theorem B3125255 : Blo 2083435 3125255 := bstep (se 1 (by rfl) ⟨2343941, by rfl⟩ : syracuseStep 3125255 = 4687883) B4687883
theorem B2083503 : Blo 2083435 2083503 := bstep (se 1 (by rfl) ⟨1562627, by rfl⟩ : syracuseStep 2083503 = 3125255) B3125255
theorem B3125261 : Blo 2083435 3125261 := bbase (se 3 (by rfl) ⟨585986, by rfl⟩ : syracuseStep 3125261 = 1171973) (by norm_num)
theorem B2083507 : Blo 2083435 2083507 := bstep (se 1 (by rfl) ⟨1562630, by rfl⟩ : syracuseStep 2083507 = 3125261) B3125261
theorem B4687901 : Blo 2083435 4687901 := bbase (se 3 (by rfl) ⟨878981, by rfl⟩ : syracuseStep 4687901 = 1757963) (by norm_num)
theorem B3125267 : Blo 2083435 3125267 := bstep (se 1 (by rfl) ⟨2343950, by rfl⟩ : syracuseStep 3125267 = 4687901) B4687901
theorem B2083511 : Blo 2083435 2083511 := bstep (se 1 (by rfl) ⟨1562633, by rfl⟩ : syracuseStep 2083511 = 3125267) B3125267
theorem B3515933 : Blo 2083435 3515933 := bbase (se 3 (by rfl) ⟨659237, by rfl⟩ : syracuseStep 3515933 = 1318475) (by norm_num)
theorem B2343955 : Blo 2083435 2343955 := bstep (se 1 (by rfl) ⟨1757966, by rfl⟩ : syracuseStep 2343955 = 3515933) B3515933
theorem B3125273 : Blo 2083435 3125273 := bstep (se 2 (by rfl) ⟨1171977, by rfl⟩ : syracuseStep 3125273 = 2343955) B2343955
theorem B2083515 : Blo 2083435 2083515 := bstep (se 1 (by rfl) ⟨1562636, by rfl⟩ : syracuseStep 2083515 = 3125273) B3125273
theorem B4223893 : Blo 2083435 4223893 := bbase (se 6 (by rfl) ⟨98997, by rfl⟩ : syracuseStep 4223893 = 197995) (by norm_num)
theorem B5631857 : Blo 2083435 5631857 := bstep (se 2 (by rfl) ⟨2111946, by rfl⟩ : syracuseStep 5631857 = 4223893) B4223893
theorem B3754571 : Blo 2083435 3754571 := bstep (se 1 (by rfl) ⟨2815928, by rfl⟩ : syracuseStep 3754571 = 5631857) B5631857
theorem B10012189 : Blo 2083435 10012189 := bstep (se 3 (by rfl) ⟨1877285, by rfl⟩ : syracuseStep 10012189 = 3754571) B3754571
theorem B13349585 : Blo 2083435 13349585 := bstep (se 2 (by rfl) ⟨5006094, by rfl⟩ : syracuseStep 13349585 = 10012189) B10012189
theorem B8899723 : Blo 2083435 8899723 := bstep (se 1 (by rfl) ⟨6674792, by rfl⟩ : syracuseStep 8899723 = 13349585) B13349585
theorem B11866297 : Blo 2083435 11866297 := bstep (se 2 (by rfl) ⟨4449861, by rfl⟩ : syracuseStep 11866297 = 8899723) B8899723
theorem B15821729 : Blo 2083435 15821729 := bstep (se 2 (by rfl) ⟨5933148, by rfl⟩ : syracuseStep 15821729 = 11866297) B11866297
theorem B10547819 : Blo 2083435 10547819 := bstep (se 1 (by rfl) ⟨7910864, by rfl⟩ : syracuseStep 10547819 = 15821729) B15821729
theorem B7031879 : Blo 2083435 7031879 := bstep (se 1 (by rfl) ⟨5273909, by rfl⟩ : syracuseStep 7031879 = 10547819) B10547819
theorem B4687919 : Blo 2083435 4687919 := bstep (se 1 (by rfl) ⟨3515939, by rfl⟩ : syracuseStep 4687919 = 7031879) B7031879
theorem B3125279 : Blo 2083435 3125279 := bstep (se 1 (by rfl) ⟨2343959, by rfl⟩ : syracuseStep 3125279 = 4687919) B4687919
theorem B2083519 : Blo 2083435 2083519 := bstep (se 1 (by rfl) ⟨1562639, by rfl⟩ : syracuseStep 2083519 = 3125279) B3125279
theorem B3125285 : Blo 2083435 3125285 := bbase (se 4 (by rfl) ⟨292995, by rfl⟩ : syracuseStep 3125285 = 585991) (by norm_num)
theorem B2083523 : Blo 2083435 2083523 := bstep (se 1 (by rfl) ⟨1562642, by rfl⟩ : syracuseStep 2083523 = 3125285) B3125285
theorem B2636965 : Blo 2083435 2636965 := bbase (se 4 (by rfl) ⟨247215, by rfl⟩ : syracuseStep 2636965 = 494431) (by norm_num)
theorem B3515953 : Blo 2083435 3515953 := bstep (se 2 (by rfl) ⟨1318482, by rfl⟩ : syracuseStep 3515953 = 2636965) B2636965
theorem B4687937 : Blo 2083435 4687937 := bstep (se 2 (by rfl) ⟨1757976, by rfl⟩ : syracuseStep 4687937 = 3515953) B3515953
theorem B3125291 : Blo 2083435 3125291 := bstep (se 1 (by rfl) ⟨2343968, by rfl⟩ : syracuseStep 3125291 = 4687937) B4687937
theorem B2083527 : Blo 2083435 2083527 := bstep (se 1 (by rfl) ⟨1562645, by rfl⟩ : syracuseStep 2083527 = 3125291) B3125291
theorem B2343973 : Blo 2083435 2343973 := bbase (se 4 (by rfl) ⟨219747, by rfl⟩ : syracuseStep 2343973 = 439495) (by norm_num)
theorem B3125297 : Blo 2083435 3125297 := bstep (se 2 (by rfl) ⟨1171986, by rfl⟩ : syracuseStep 3125297 = 2343973) B2343973
theorem B2083531 : Blo 2083435 2083531 := bstep (se 1 (by rfl) ⟨1562648, by rfl⟩ : syracuseStep 2083531 = 3125297) B3125297
theorem B5345909 : Blo 2083435 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B3563939 : Blo 2083435 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B9503837 : Blo 2083435 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B6335891 : Blo 2083435 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B4223927 : Blo 2083435 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B2815951 : Blo 2083435 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B3754601 : Blo 2083435 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B2503067 : Blo 2083435 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B6674845 : Blo 2083435 6674845 := bstep (se 3 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 6674845 = 2503067) B2503067
theorem B8899793 : Blo 2083435 8899793 := bstep (se 2 (by rfl) ⟨3337422, by rfl⟩ : syracuseStep 8899793 = 6674845) B6674845
theorem B5933195 : Blo 2083435 5933195 := bstep (se 1 (by rfl) ⟨4449896, by rfl⟩ : syracuseStep 5933195 = 8899793) B8899793
theorem B3955463 : Blo 2083435 3955463 := bstep (se 1 (by rfl) ⟨2966597, by rfl⟩ : syracuseStep 3955463 = 5933195) B5933195
theorem B2636975 : Blo 2083435 2636975 := bstep (se 1 (by rfl) ⟨1977731, by rfl⟩ : syracuseStep 2636975 = 3955463) B3955463
theorem B7031933 : Blo 2083435 7031933 := bstep (se 3 (by rfl) ⟨1318487, by rfl⟩ : syracuseStep 7031933 = 2636975) B2636975
theorem B4687955 : Blo 2083435 4687955 := bstep (se 1 (by rfl) ⟨3515966, by rfl⟩ : syracuseStep 4687955 = 7031933) B7031933
theorem B3125303 : Blo 2083435 3125303 := bstep (se 1 (by rfl) ⟨2343977, by rfl⟩ : syracuseStep 3125303 = 4687955) B4687955
theorem B2083535 : Blo 2083435 2083535 := bstep (se 1 (by rfl) ⟨1562651, by rfl⟩ : syracuseStep 2083535 = 3125303) B3125303
theorem B3125309 : Blo 2083435 3125309 := bbase (se 3 (by rfl) ⟨585995, by rfl⟩ : syracuseStep 3125309 = 1171991) (by norm_num)
theorem B2083539 : Blo 2083435 2083539 := bstep (se 1 (by rfl) ⟨1562654, by rfl⟩ : syracuseStep 2083539 = 3125309) B3125309
theorem B4687973 : Blo 2083435 4687973 := bbase (se 4 (by rfl) ⟨439497, by rfl⟩ : syracuseStep 4687973 = 878995) (by norm_num)
theorem B3125315 : Blo 2083435 3125315 := bstep (se 1 (by rfl) ⟨2343986, by rfl⟩ : syracuseStep 3125315 = 4687973) B4687973
theorem B2083543 : Blo 2083435 2083543 := bstep (se 1 (by rfl) ⟨1562657, by rfl⟩ : syracuseStep 2083543 = 3125315) B3125315
theorem B5273981 : Blo 2083435 5273981 := bbase (se 3 (by rfl) ⟨988871, by rfl⟩ : syracuseStep 5273981 = 1977743) (by norm_num)
theorem B3515987 : Blo 2083435 3515987 := bstep (se 1 (by rfl) ⟨2636990, by rfl⟩ : syracuseStep 3515987 = 5273981) B5273981
theorem B2343991 : Blo 2083435 2343991 := bstep (se 1 (by rfl) ⟨1757993, by rfl⟩ : syracuseStep 2343991 = 3515987) B3515987
theorem B3125321 : Blo 2083435 3125321 := bstep (se 2 (by rfl) ⟨1171995, by rfl⟩ : syracuseStep 3125321 = 2343991) B2343991
theorem B2083547 : Blo 2083435 2083547 := bstep (se 1 (by rfl) ⟨1562660, by rfl⟩ : syracuseStep 2083547 = 3125321) B3125321
theorem B3955493 : Blo 2083435 3955493 := bbase (se 4 (by rfl) ⟨370827, by rfl⟩ : syracuseStep 3955493 = 741655) (by norm_num)
theorem B10547981 : Blo 2083435 10547981 := bstep (se 3 (by rfl) ⟨1977746, by rfl⟩ : syracuseStep 10547981 = 3955493) B3955493
theorem B7031987 : Blo 2083435 7031987 := bstep (se 1 (by rfl) ⟨5273990, by rfl⟩ : syracuseStep 7031987 = 10547981) B10547981
theorem B4687991 : Blo 2083435 4687991 := bstep (se 1 (by rfl) ⟨3515993, by rfl⟩ : syracuseStep 4687991 = 7031987) B7031987
theorem B3125327 : Blo 2083435 3125327 := bstep (se 1 (by rfl) ⟨2343995, by rfl⟩ : syracuseStep 3125327 = 4687991) B4687991
theorem B2083551 : Blo 2083435 2083551 := bstep (se 1 (by rfl) ⟨1562663, by rfl⟩ : syracuseStep 2083551 = 3125327) B3125327
theorem B3125333 : Blo 2083435 3125333 := bbase (se 8 (by rfl) ⟨18312, by rfl⟩ : syracuseStep 3125333 = 36625) (by norm_num)
theorem B2083555 : Blo 2083435 2083555 := bstep (se 1 (by rfl) ⟨1562666, by rfl⟩ : syracuseStep 2083555 = 3125333) B3125333
theorem B7127957 : Blo 2083435 7127957 := bbase (se 6 (by rfl) ⟨167061, by rfl⟩ : syracuseStep 7127957 = 334123) (by norm_num)
theorem B19007885 : Blo 2083435 19007885 := bstep (se 3 (by rfl) ⟨3563978, by rfl⟩ : syracuseStep 19007885 = 7127957) B7127957
theorem B12671923 : Blo 2083435 12671923 := bstep (se 1 (by rfl) ⟨9503942, by rfl⟩ : syracuseStep 12671923 = 19007885) B19007885
theorem B16895897 : Blo 2083435 16895897 := bstep (se 2 (by rfl) ⟨6335961, by rfl⟩ : syracuseStep 16895897 = 12671923) B12671923
theorem B11263931 : Blo 2083435 11263931 := bstep (se 1 (by rfl) ⟨8447948, by rfl⟩ : syracuseStep 11263931 = 16895897) B16895897
theorem B7509287 : Blo 2083435 7509287 := bstep (se 1 (by rfl) ⟨5631965, by rfl⟩ : syracuseStep 7509287 = 11263931) B11263931
theorem B20024765 : Blo 2083435 20024765 := bstep (se 3 (by rfl) ⟨3754643, by rfl⟩ : syracuseStep 20024765 = 7509287) B7509287
theorem B13349843 : Blo 2083435 13349843 := bstep (se 1 (by rfl) ⟨10012382, by rfl⟩ : syracuseStep 13349843 = 20024765) B20024765
theorem B8899895 : Blo 2083435 8899895 := bstep (se 1 (by rfl) ⟨6674921, by rfl⟩ : syracuseStep 8899895 = 13349843) B13349843
theorem B5933263 : Blo 2083435 5933263 := bstep (se 1 (by rfl) ⟨4449947, by rfl⟩ : syracuseStep 5933263 = 8899895) B8899895
theorem B7911017 : Blo 2083435 7911017 := bstep (se 2 (by rfl) ⟨2966631, by rfl⟩ : syracuseStep 7911017 = 5933263) B5933263
theorem B5274011 : Blo 2083435 5274011 := bstep (se 1 (by rfl) ⟨3955508, by rfl⟩ : syracuseStep 5274011 = 7911017) B7911017
theorem B3516007 : Blo 2083435 3516007 := bstep (se 1 (by rfl) ⟨2637005, by rfl⟩ : syracuseStep 3516007 = 5274011) B5274011
theorem B4688009 : Blo 2083435 4688009 := bstep (se 2 (by rfl) ⟨1758003, by rfl⟩ : syracuseStep 4688009 = 3516007) B3516007
theorem B3125339 : Blo 2083435 3125339 := bstep (se 1 (by rfl) ⟨2344004, by rfl⟩ : syracuseStep 3125339 = 4688009) B4688009
theorem B2083559 : Blo 2083435 2083559 := bstep (se 1 (by rfl) ⟨1562669, by rfl⟩ : syracuseStep 2083559 = 3125339) B3125339
theorem B2344009 : Blo 2083435 2344009 := bbase (se 2 (by rfl) ⟨879003, by rfl⟩ : syracuseStep 2344009 = 1758007) (by norm_num)
theorem B3125345 : Blo 2083435 3125345 := bstep (se 2 (by rfl) ⟨1172004, by rfl⟩ : syracuseStep 3125345 = 2344009) B2344009
theorem B2083563 : Blo 2083435 2083563 := bstep (se 1 (by rfl) ⟨1562672, by rfl⟩ : syracuseStep 2083563 = 3125345) B3125345
theorem B2503105 : Blo 2083435 2503105 := bbase (se 2 (by rfl) ⟨938664, by rfl⟩ : syracuseStep 2503105 = 1877329) (by norm_num)
theorem B13349893 : Blo 2083435 13349893 := bstep (se 4 (by rfl) ⟨1251552, by rfl⟩ : syracuseStep 13349893 = 2503105) B2503105
theorem B17799857 : Blo 2083435 17799857 := bstep (se 2 (by rfl) ⟨6674946, by rfl⟩ : syracuseStep 17799857 = 13349893) B13349893
theorem B11866571 : Blo 2083435 11866571 := bstep (se 1 (by rfl) ⟨8899928, by rfl⟩ : syracuseStep 11866571 = 17799857) B17799857
theorem B7911047 : Blo 2083435 7911047 := bstep (se 1 (by rfl) ⟨5933285, by rfl⟩ : syracuseStep 7911047 = 11866571) B11866571
theorem B5274031 : Blo 2083435 5274031 := bstep (se 1 (by rfl) ⟨3955523, by rfl⟩ : syracuseStep 5274031 = 7911047) B7911047
theorem B7032041 : Blo 2083435 7032041 := bstep (se 2 (by rfl) ⟨2637015, by rfl⟩ : syracuseStep 7032041 = 5274031) B5274031
theorem B4688027 : Blo 2083435 4688027 := bstep (se 1 (by rfl) ⟨3516020, by rfl⟩ : syracuseStep 4688027 = 7032041) B7032041
theorem B3125351 : Blo 2083435 3125351 := bstep (se 1 (by rfl) ⟨2344013, by rfl⟩ : syracuseStep 3125351 = 4688027) B4688027
theorem B2083567 : Blo 2083435 2083567 := bstep (se 1 (by rfl) ⟨1562675, by rfl⟩ : syracuseStep 2083567 = 3125351) B3125351
theorem B3125357 : Blo 2083435 3125357 := bbase (se 3 (by rfl) ⟨586004, by rfl⟩ : syracuseStep 3125357 = 1172009) (by norm_num)
theorem B2083571 : Blo 2083435 2083571 := bstep (se 1 (by rfl) ⟨1562678, by rfl⟩ : syracuseStep 2083571 = 3125357) B3125357
theorem B4688045 : Blo 2083435 4688045 := bbase (se 3 (by rfl) ⟨879008, by rfl⟩ : syracuseStep 4688045 = 1758017) (by norm_num)
theorem B3125363 : Blo 2083435 3125363 := bstep (se 1 (by rfl) ⟨2344022, by rfl⟩ : syracuseStep 3125363 = 4688045) B4688045
theorem B2083575 : Blo 2083435 2083575 := bstep (se 1 (by rfl) ⟨1562681, by rfl⟩ : syracuseStep 2083575 = 3125363) B3125363
theorem B5632021 : Blo 2083435 5632021 := bbase (se 6 (by rfl) ⟨132000, by rfl⟩ : syracuseStep 5632021 = 264001) (by norm_num)
theorem B7509361 : Blo 2083435 7509361 := bstep (se 2 (by rfl) ⟨2816010, by rfl⟩ : syracuseStep 7509361 = 5632021) B5632021
theorem B10012481 : Blo 2083435 10012481 := bstep (se 2 (by rfl) ⟨3754680, by rfl⟩ : syracuseStep 10012481 = 7509361) B7509361
theorem B6674987 : Blo 2083435 6674987 := bstep (se 1 (by rfl) ⟨5006240, by rfl⟩ : syracuseStep 6674987 = 10012481) B10012481
theorem B4449991 : Blo 2083435 4449991 := bstep (se 1 (by rfl) ⟨3337493, by rfl⟩ : syracuseStep 4449991 = 6674987) B6674987
theorem B5933321 : Blo 2083435 5933321 := bstep (se 2 (by rfl) ⟨2224995, by rfl⟩ : syracuseStep 5933321 = 4449991) B4449991
theorem B3955547 : Blo 2083435 3955547 := bstep (se 1 (by rfl) ⟨2966660, by rfl⟩ : syracuseStep 3955547 = 5933321) B5933321
theorem B2637031 : Blo 2083435 2637031 := bstep (se 1 (by rfl) ⟨1977773, by rfl⟩ : syracuseStep 2637031 = 3955547) B3955547
theorem B3516041 : Blo 2083435 3516041 := bstep (se 2 (by rfl) ⟨1318515, by rfl⟩ : syracuseStep 3516041 = 2637031) B2637031
theorem B2344027 : Blo 2083435 2344027 := bstep (se 1 (by rfl) ⟨1758020, by rfl⟩ : syracuseStep 2344027 = 3516041) B3516041
theorem B3125369 : Blo 2083435 3125369 := bstep (se 2 (by rfl) ⟨1172013, by rfl⟩ : syracuseStep 3125369 = 2344027) B2344027
theorem B2083579 : Blo 2083435 2083579 := bstep (se 1 (by rfl) ⟨1562684, by rfl⟩ : syracuseStep 2083579 = 3125369) B3125369
theorem B26699989 : Blo 2083435 26699989 := bbase (se 7 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 26699989 = 625781) (by norm_num)
theorem B35599985 : Blo 2083435 35599985 := bstep (se 2 (by rfl) ⟨13349994, by rfl⟩ : syracuseStep 35599985 = 26699989) B26699989
theorem B23733323 : Blo 2083435 23733323 := bstep (se 1 (by rfl) ⟨17799992, by rfl⟩ : syracuseStep 23733323 = 35599985) B35599985
theorem B15822215 : Blo 2083435 15822215 := bstep (se 1 (by rfl) ⟨11866661, by rfl⟩ : syracuseStep 15822215 = 23733323) B23733323
theorem B10548143 : Blo 2083435 10548143 := bstep (se 1 (by rfl) ⟨7911107, by rfl⟩ : syracuseStep 10548143 = 15822215) B15822215
theorem B7032095 : Blo 2083435 7032095 := bstep (se 1 (by rfl) ⟨5274071, by rfl⟩ : syracuseStep 7032095 = 10548143) B10548143
theorem B4688063 : Blo 2083435 4688063 := bstep (se 1 (by rfl) ⟨3516047, by rfl⟩ : syracuseStep 4688063 = 7032095) B7032095
theorem B3125375 : Blo 2083435 3125375 := bstep (se 1 (by rfl) ⟨2344031, by rfl⟩ : syracuseStep 3125375 = 4688063) B4688063
theorem B2083583 : Blo 2083435 2083583 := bstep (se 1 (by rfl) ⟨1562687, by rfl⟩ : syracuseStep 2083583 = 3125375) B3125375
theorem B3125381 : Blo 2083435 3125381 := bbase (se 4 (by rfl) ⟨293004, by rfl⟩ : syracuseStep 3125381 = 586009) (by norm_num)
theorem B2083587 : Blo 2083435 2083587 := bstep (se 1 (by rfl) ⟨1562690, by rfl⟩ : syracuseStep 2083587 = 3125381) B3125381
theorem B3516061 : Blo 2083435 3516061 := bbase (se 3 (by rfl) ⟨659261, by rfl⟩ : syracuseStep 3516061 = 1318523) (by norm_num)
theorem B4688081 : Blo 2083435 4688081 := bstep (se 2 (by rfl) ⟨1758030, by rfl⟩ : syracuseStep 4688081 = 3516061) B3516061
theorem B3125387 : Blo 2083435 3125387 := bstep (se 1 (by rfl) ⟨2344040, by rfl⟩ : syracuseStep 3125387 = 4688081) B4688081
theorem B2083591 : Blo 2083435 2083591 := bstep (se 1 (by rfl) ⟨1562693, by rfl⟩ : syracuseStep 2083591 = 3125387) B3125387
theorem B2344045 : Blo 2083435 2344045 := bbase (se 3 (by rfl) ⟨439508, by rfl⟩ : syracuseStep 2344045 = 879017) (by norm_num)
theorem B3125393 : Blo 2083435 3125393 := bstep (se 2 (by rfl) ⟨1172022, by rfl⟩ : syracuseStep 3125393 = 2344045) B2344045
theorem B2083595 : Blo 2083435 2083595 := bstep (se 1 (by rfl) ⟨1562696, by rfl⟩ : syracuseStep 2083595 = 3125393) B3125393
theorem B7032149 : Blo 2083435 7032149 := bbase (se 11 (by rfl) ⟨5150, by rfl⟩ : syracuseStep 7032149 = 10301) (by norm_num)
theorem B4688099 : Blo 2083435 4688099 := bstep (se 1 (by rfl) ⟨3516074, by rfl⟩ : syracuseStep 4688099 = 7032149) B7032149
theorem B3125399 : Blo 2083435 3125399 := bstep (se 1 (by rfl) ⟨2344049, by rfl⟩ : syracuseStep 3125399 = 4688099) B4688099
theorem B2083599 : Blo 2083435 2083599 := bstep (se 1 (by rfl) ⟨1562699, by rfl⟩ : syracuseStep 2083599 = 3125399) B3125399
theorem B3125405 : Blo 2083435 3125405 := bbase (se 3 (by rfl) ⟨586013, by rfl⟩ : syracuseStep 3125405 = 1172027) (by norm_num)
theorem B2083603 : Blo 2083435 2083603 := bstep (se 1 (by rfl) ⟨1562702, by rfl⟩ : syracuseStep 2083603 = 3125405) B3125405
theorem B4688117 : Blo 2083435 4688117 := bbase (se 5 (by rfl) ⟨219755, by rfl⟩ : syracuseStep 4688117 = 439511) (by norm_num)
theorem B3125411 : Blo 2083435 3125411 := bstep (se 1 (by rfl) ⟨2344058, by rfl⟩ : syracuseStep 3125411 = 4688117) B4688117
theorem B2083607 : Blo 2083435 2083607 := bstep (se 1 (by rfl) ⟨1562705, by rfl⟩ : syracuseStep 2083607 = 3125411) B3125411
theorem B2816053 : Blo 2083435 2816053 := bbase (se 5 (by rfl) ⟨132002, by rfl⟩ : syracuseStep 2816053 = 264005) (by norm_num)
theorem B15018949 : Blo 2083435 15018949 := bstep (se 4 (by rfl) ⟨1408026, by rfl⟩ : syracuseStep 15018949 = 2816053) B2816053
theorem B20025265 : Blo 2083435 20025265 := bstep (se 2 (by rfl) ⟨7509474, by rfl⟩ : syracuseStep 20025265 = 15018949) B15018949
theorem B26700353 : Blo 2083435 26700353 := bstep (se 2 (by rfl) ⟨10012632, by rfl⟩ : syracuseStep 26700353 = 20025265) B20025265
theorem B17800235 : Blo 2083435 17800235 := bstep (se 1 (by rfl) ⟨13350176, by rfl⟩ : syracuseStep 17800235 = 26700353) B26700353
theorem B11866823 : Blo 2083435 11866823 := bstep (se 1 (by rfl) ⟨8900117, by rfl⟩ : syracuseStep 11866823 = 17800235) B17800235
theorem B7911215 : Blo 2083435 7911215 := bstep (se 1 (by rfl) ⟨5933411, by rfl⟩ : syracuseStep 7911215 = 11866823) B11866823
theorem B5274143 : Blo 2083435 5274143 := bstep (se 1 (by rfl) ⟨3955607, by rfl⟩ : syracuseStep 5274143 = 7911215) B7911215
theorem B3516095 : Blo 2083435 3516095 := bstep (se 1 (by rfl) ⟨2637071, by rfl⟩ : syracuseStep 3516095 = 5274143) B5274143
theorem B2344063 : Blo 2083435 2344063 := bstep (se 1 (by rfl) ⟨1758047, by rfl⟩ : syracuseStep 2344063 = 3516095) B3516095
theorem B3125417 : Blo 2083435 3125417 := bstep (se 2 (by rfl) ⟨1172031, by rfl⟩ : syracuseStep 3125417 = 2344063) B2344063
theorem B2083611 : Blo 2083435 2083611 := bstep (se 1 (by rfl) ⟨1562708, by rfl⟩ : syracuseStep 2083611 = 3125417) B3125417
theorem B4752101 : Blo 2083435 4752101 := bbase (se 4 (by rfl) ⟨445509, by rfl⟩ : syracuseStep 4752101 = 891019) (by norm_num)
theorem B3168067 : Blo 2083435 3168067 := bstep (se 1 (by rfl) ⟨2376050, by rfl⟩ : syracuseStep 3168067 = 4752101) B4752101
theorem B4224089 : Blo 2083435 4224089 := bstep (se 2 (by rfl) ⟨1584033, by rfl⟩ : syracuseStep 4224089 = 3168067) B3168067
theorem B2816059 : Blo 2083435 2816059 := bstep (se 1 (by rfl) ⟨2112044, by rfl⟩ : syracuseStep 2816059 = 4224089) B4224089
theorem B3754745 : Blo 2083435 3754745 := bstep (se 2 (by rfl) ⟨1408029, by rfl⟩ : syracuseStep 3754745 = 2816059) B2816059
theorem B2503163 : Blo 2083435 2503163 := bstep (se 1 (by rfl) ⟨1877372, by rfl⟩ : syracuseStep 2503163 = 3754745) B3754745
theorem B6675101 : Blo 2083435 6675101 := bstep (se 3 (by rfl) ⟨1251581, by rfl⟩ : syracuseStep 6675101 = 2503163) B2503163
theorem B4450067 : Blo 2083435 4450067 := bstep (se 1 (by rfl) ⟨3337550, by rfl⟩ : syracuseStep 4450067 = 6675101) B6675101
theorem B2966711 : Blo 2083435 2966711 := bstep (se 1 (by rfl) ⟨2225033, by rfl⟩ : syracuseStep 2966711 = 4450067) B4450067
theorem B7911229 : Blo 2083435 7911229 := bstep (se 3 (by rfl) ⟨1483355, by rfl⟩ : syracuseStep 7911229 = 2966711) B2966711
theorem B10548305 : Blo 2083435 10548305 := bstep (se 2 (by rfl) ⟨3955614, by rfl⟩ : syracuseStep 10548305 = 7911229) B7911229
theorem B7032203 : Blo 2083435 7032203 := bstep (se 1 (by rfl) ⟨5274152, by rfl⟩ : syracuseStep 7032203 = 10548305) B10548305
theorem B4688135 : Blo 2083435 4688135 := bstep (se 1 (by rfl) ⟨3516101, by rfl⟩ : syracuseStep 4688135 = 7032203) B7032203
theorem B3125423 : Blo 2083435 3125423 := bstep (se 1 (by rfl) ⟨2344067, by rfl⟩ : syracuseStep 3125423 = 4688135) B4688135
theorem B2083615 : Blo 2083435 2083615 := bstep (se 1 (by rfl) ⟨1562711, by rfl⟩ : syracuseStep 2083615 = 3125423) B3125423
theorem B3125429 : Blo 2083435 3125429 := bbase (se 5 (by rfl) ⟨146504, by rfl⟩ : syracuseStep 3125429 = 293009) (by norm_num)
theorem B2083619 : Blo 2083435 2083619 := bstep (se 1 (by rfl) ⟨1562714, by rfl⟩ : syracuseStep 2083619 = 3125429) B3125429
theorem B5274173 : Blo 2083435 5274173 := bbase (se 3 (by rfl) ⟨988907, by rfl⟩ : syracuseStep 5274173 = 1977815) (by norm_num)
theorem B3516115 : Blo 2083435 3516115 := bstep (se 1 (by rfl) ⟨2637086, by rfl⟩ : syracuseStep 3516115 = 5274173) B5274173
theorem B4688153 : Blo 2083435 4688153 := bstep (se 2 (by rfl) ⟨1758057, by rfl⟩ : syracuseStep 4688153 = 3516115) B3516115
theorem B3125435 : Blo 2083435 3125435 := bstep (se 1 (by rfl) ⟨2344076, by rfl⟩ : syracuseStep 3125435 = 4688153) B4688153
theorem B2083623 : Blo 2083435 2083623 := bstep (se 1 (by rfl) ⟨1562717, by rfl⟩ : syracuseStep 2083623 = 3125435) B3125435
theorem B2344081 : Blo 2083435 2344081 := bbase (se 2 (by rfl) ⟨879030, by rfl⟩ : syracuseStep 2344081 = 1758061) (by norm_num)
theorem B3125441 : Blo 2083435 3125441 := bstep (se 2 (by rfl) ⟨1172040, by rfl⟩ : syracuseStep 3125441 = 2344081) B2344081
theorem B2083627 : Blo 2083435 2083627 := bstep (se 1 (by rfl) ⟨1562720, by rfl⟩ : syracuseStep 2083627 = 3125441) B3125441
theorem B3955645 : Blo 2083435 3955645 := bbase (se 3 (by rfl) ⟨741683, by rfl⟩ : syracuseStep 3955645 = 1483367) (by norm_num)
theorem B5274193 : Blo 2083435 5274193 := bstep (se 2 (by rfl) ⟨1977822, by rfl⟩ : syracuseStep 5274193 = 3955645) B3955645
theorem B7032257 : Blo 2083435 7032257 := bstep (se 2 (by rfl) ⟨2637096, by rfl⟩ : syracuseStep 7032257 = 5274193) B5274193
theorem B4688171 : Blo 2083435 4688171 := bstep (se 1 (by rfl) ⟨3516128, by rfl⟩ : syracuseStep 4688171 = 7032257) B7032257
theorem B3125447 : Blo 2083435 3125447 := bstep (se 1 (by rfl) ⟨2344085, by rfl⟩ : syracuseStep 3125447 = 4688171) B4688171
theorem B2083631 : Blo 2083435 2083631 := bstep (se 1 (by rfl) ⟨1562723, by rfl⟩ : syracuseStep 2083631 = 3125447) B3125447
theorem B3125453 : Blo 2083435 3125453 := bbase (se 3 (by rfl) ⟨586022, by rfl⟩ : syracuseStep 3125453 = 1172045) (by norm_num)
theorem B2083635 : Blo 2083435 2083635 := bstep (se 1 (by rfl) ⟨1562726, by rfl⟩ : syracuseStep 2083635 = 3125453) B3125453
theorem B4688189 : Blo 2083435 4688189 := bbase (se 3 (by rfl) ⟨879035, by rfl⟩ : syracuseStep 4688189 = 1758071) (by norm_num)
theorem B3125459 : Blo 2083435 3125459 := bstep (se 1 (by rfl) ⟨2344094, by rfl⟩ : syracuseStep 3125459 = 4688189) B4688189
theorem B2083639 : Blo 2083435 2083639 := bstep (se 1 (by rfl) ⟨1562729, by rfl⟩ : syracuseStep 2083639 = 3125459) B3125459
theorem B3516149 : Blo 2083435 3516149 := bbase (se 5 (by rfl) ⟨164819, by rfl⟩ : syracuseStep 3516149 = 329639) (by norm_num)
theorem B2344099 : Blo 2083435 2344099 := bstep (se 1 (by rfl) ⟨1758074, by rfl⟩ : syracuseStep 2344099 = 3516149) B3516149
theorem B3125465 : Blo 2083435 3125465 := bstep (se 2 (by rfl) ⟨1172049, by rfl⟩ : syracuseStep 3125465 = 2344099) B2344099
theorem B2083643 : Blo 2083435 2083643 := bstep (se 1 (by rfl) ⟨1562732, by rfl⟩ : syracuseStep 2083643 = 3125465) B3125465
theorem B10012805 : Blo 2083435 10012805 := bbase (se 4 (by rfl) ⟨938700, by rfl⟩ : syracuseStep 10012805 = 1877401) (by norm_num)
theorem B6675203 : Blo 2083435 6675203 := bstep (se 1 (by rfl) ⟨5006402, by rfl⟩ : syracuseStep 6675203 = 10012805) B10012805
theorem B4450135 : Blo 2083435 4450135 := bstep (se 1 (by rfl) ⟨3337601, by rfl⟩ : syracuseStep 4450135 = 6675203) B6675203
theorem B5933513 : Blo 2083435 5933513 := bstep (se 2 (by rfl) ⟨2225067, by rfl⟩ : syracuseStep 5933513 = 4450135) B4450135
theorem B15822701 : Blo 2083435 15822701 := bstep (se 3 (by rfl) ⟨2966756, by rfl⟩ : syracuseStep 15822701 = 5933513) B5933513
theorem B10548467 : Blo 2083435 10548467 := bstep (se 1 (by rfl) ⟨7911350, by rfl⟩ : syracuseStep 10548467 = 15822701) B15822701
theorem B7032311 : Blo 2083435 7032311 := bstep (se 1 (by rfl) ⟨5274233, by rfl⟩ : syracuseStep 7032311 = 10548467) B10548467
theorem B4688207 : Blo 2083435 4688207 := bstep (se 1 (by rfl) ⟨3516155, by rfl⟩ : syracuseStep 4688207 = 7032311) B7032311
theorem B3125471 : Blo 2083435 3125471 := bstep (se 1 (by rfl) ⟨2344103, by rfl⟩ : syracuseStep 3125471 = 4688207) B4688207
theorem B2083647 : Blo 2083435 2083647 := bstep (se 1 (by rfl) ⟨1562735, by rfl⟩ : syracuseStep 2083647 = 3125471) B3125471
theorem B3125477 : Blo 2083435 3125477 := bbase (se 4 (by rfl) ⟨293013, by rfl⟩ : syracuseStep 3125477 = 586027) (by norm_num)
theorem B2083651 : Blo 2083435 2083651 := bstep (se 1 (by rfl) ⟨1562738, by rfl⟩ : syracuseStep 2083651 = 3125477) B3125477
theorem B2112085 : Blo 2083435 2112085 := bbase (se 8 (by rfl) ⟨12375, by rfl⟩ : syracuseStep 2112085 = 24751) (by norm_num)
theorem B11264453 : Blo 2083435 11264453 := bstep (se 4 (by rfl) ⟨1056042, by rfl⟩ : syracuseStep 11264453 = 2112085) B2112085
theorem B7509635 : Blo 2083435 7509635 := bstep (se 1 (by rfl) ⟨5632226, by rfl⟩ : syracuseStep 7509635 = 11264453) B11264453
theorem B5006423 : Blo 2083435 5006423 := bstep (se 1 (by rfl) ⟨3754817, by rfl⟩ : syracuseStep 5006423 = 7509635) B7509635
theorem B3337615 : Blo 2083435 3337615 := bstep (se 1 (by rfl) ⟨2503211, by rfl⟩ : syracuseStep 3337615 = 5006423) B5006423
theorem B4450153 : Blo 2083435 4450153 := bstep (se 2 (by rfl) ⟨1668807, by rfl⟩ : syracuseStep 4450153 = 3337615) B3337615
theorem B5933537 : Blo 2083435 5933537 := bstep (se 2 (by rfl) ⟨2225076, by rfl⟩ : syracuseStep 5933537 = 4450153) B4450153
theorem B3955691 : Blo 2083435 3955691 := bstep (se 1 (by rfl) ⟨2966768, by rfl⟩ : syracuseStep 3955691 = 5933537) B5933537
theorem B2637127 : Blo 2083435 2637127 := bstep (se 1 (by rfl) ⟨1977845, by rfl⟩ : syracuseStep 2637127 = 3955691) B3955691
theorem B3516169 : Blo 2083435 3516169 := bstep (se 2 (by rfl) ⟨1318563, by rfl⟩ : syracuseStep 3516169 = 2637127) B2637127
theorem B4688225 : Blo 2083435 4688225 := bstep (se 2 (by rfl) ⟨1758084, by rfl⟩ : syracuseStep 4688225 = 3516169) B3516169
theorem B3125483 : Blo 2083435 3125483 := bstep (se 1 (by rfl) ⟨2344112, by rfl⟩ : syracuseStep 3125483 = 4688225) B4688225
theorem B2083655 : Blo 2083435 2083655 := bstep (se 1 (by rfl) ⟨1562741, by rfl⟩ : syracuseStep 2083655 = 3125483) B3125483
theorem B2344117 : Blo 2083435 2344117 := bbase (se 5 (by rfl) ⟨109880, by rfl⟩ : syracuseStep 2344117 = 219761) (by norm_num)
theorem B3125489 : Blo 2083435 3125489 := bstep (se 2 (by rfl) ⟨1172058, by rfl⟩ : syracuseStep 3125489 = 2344117) B2344117
theorem B2083659 : Blo 2083435 2083659 := bstep (se 1 (by rfl) ⟨1562744, by rfl⟩ : syracuseStep 2083659 = 3125489) B3125489
theorem B2637137 : Blo 2083435 2637137 := bbase (se 2 (by rfl) ⟨988926, by rfl⟩ : syracuseStep 2637137 = 1977853) (by norm_num)
theorem B7032365 : Blo 2083435 7032365 := bstep (se 3 (by rfl) ⟨1318568, by rfl⟩ : syracuseStep 7032365 = 2637137) B2637137
theorem B4688243 : Blo 2083435 4688243 := bstep (se 1 (by rfl) ⟨3516182, by rfl⟩ : syracuseStep 4688243 = 7032365) B7032365
theorem B3125495 : Blo 2083435 3125495 := bstep (se 1 (by rfl) ⟨2344121, by rfl⟩ : syracuseStep 3125495 = 4688243) B4688243
theorem B2083663 : Blo 2083435 2083663 := bstep (se 1 (by rfl) ⟨1562747, by rfl⟩ : syracuseStep 2083663 = 3125495) B3125495
theorem B3125501 : Blo 2083435 3125501 := bbase (se 3 (by rfl) ⟨586031, by rfl⟩ : syracuseStep 3125501 = 1172063) (by norm_num)
theorem B2083667 : Blo 2083435 2083667 := bstep (se 1 (by rfl) ⟨1562750, by rfl⟩ : syracuseStep 2083667 = 3125501) B3125501
theorem B4688261 : Blo 2083435 4688261 := bbase (se 4 (by rfl) ⟨439524, by rfl⟩ : syracuseStep 4688261 = 879049) (by norm_num)
theorem B3125507 : Blo 2083435 3125507 := bstep (se 1 (by rfl) ⟨2344130, by rfl⟩ : syracuseStep 3125507 = 4688261) B4688261
theorem B2083671 : Blo 2083435 2083671 := bstep (se 1 (by rfl) ⟨1562753, by rfl⟩ : syracuseStep 2083671 = 3125507) B3125507
theorem B2966797 : Blo 2083435 2966797 := bbase (se 3 (by rfl) ⟨556274, by rfl⟩ : syracuseStep 2966797 = 1112549) (by norm_num)
theorem B3955729 : Blo 2083435 3955729 := bstep (se 2 (by rfl) ⟨1483398, by rfl⟩ : syracuseStep 3955729 = 2966797) B2966797
theorem B5274305 : Blo 2083435 5274305 := bstep (se 2 (by rfl) ⟨1977864, by rfl⟩ : syracuseStep 5274305 = 3955729) B3955729
theorem B3516203 : Blo 2083435 3516203 := bstep (se 1 (by rfl) ⟨2637152, by rfl⟩ : syracuseStep 3516203 = 5274305) B5274305
theorem B2344135 : Blo 2083435 2344135 := bstep (se 1 (by rfl) ⟨1758101, by rfl⟩ : syracuseStep 2344135 = 3516203) B3516203
theorem B3125513 : Blo 2083435 3125513 := bstep (se 2 (by rfl) ⟨1172067, by rfl⟩ : syracuseStep 3125513 = 2344135) B2344135
theorem B2083675 : Blo 2083435 2083675 := bstep (se 1 (by rfl) ⟨1562756, by rfl⟩ : syracuseStep 2083675 = 3125513) B3125513
theorem B10548629 : Blo 2083435 10548629 := bbase (se 6 (by rfl) ⟨247233, by rfl⟩ : syracuseStep 10548629 = 494467) (by norm_num)
theorem B7032419 : Blo 2083435 7032419 := bstep (se 1 (by rfl) ⟨5274314, by rfl⟩ : syracuseStep 7032419 = 10548629) B10548629
theorem B4688279 : Blo 2083435 4688279 := bstep (se 1 (by rfl) ⟨3516209, by rfl⟩ : syracuseStep 4688279 = 7032419) B7032419
theorem B3125519 : Blo 2083435 3125519 := bstep (se 1 (by rfl) ⟨2344139, by rfl⟩ : syracuseStep 3125519 = 4688279) B4688279
theorem B2083679 : Blo 2083435 2083679 := bstep (se 1 (by rfl) ⟨1562759, by rfl⟩ : syracuseStep 2083679 = 3125519) B3125519
theorem B3125525 : Blo 2083435 3125525 := bbase (se 6 (by rfl) ⟨73254, by rfl⟩ : syracuseStep 3125525 = 146509) (by norm_num)
theorem B2083683 : Blo 2083435 2083683 := bstep (se 1 (by rfl) ⟨1562762, by rfl⟩ : syracuseStep 2083683 = 3125525) B3125525
theorem B10012997 : Blo 2083435 10012997 := bbase (se 4 (by rfl) ⟨938718, by rfl⟩ : syracuseStep 10012997 = 1877437) (by norm_num)
theorem B26701325 : Blo 2083435 26701325 := bstep (se 3 (by rfl) ⟨5006498, by rfl⟩ : syracuseStep 26701325 = 10012997) B10012997
theorem B17800883 : Blo 2083435 17800883 := bstep (se 1 (by rfl) ⟨13350662, by rfl⟩ : syracuseStep 17800883 = 26701325) B26701325
theorem B11867255 : Blo 2083435 11867255 := bstep (se 1 (by rfl) ⟨8900441, by rfl⟩ : syracuseStep 11867255 = 17800883) B17800883
theorem B7911503 : Blo 2083435 7911503 := bstep (se 1 (by rfl) ⟨5933627, by rfl⟩ : syracuseStep 7911503 = 11867255) B11867255
theorem B5274335 : Blo 2083435 5274335 := bstep (se 1 (by rfl) ⟨3955751, by rfl⟩ : syracuseStep 5274335 = 7911503) B7911503
theorem B3516223 : Blo 2083435 3516223 := bstep (se 1 (by rfl) ⟨2637167, by rfl⟩ : syracuseStep 3516223 = 5274335) B5274335
theorem B4688297 : Blo 2083435 4688297 := bstep (se 2 (by rfl) ⟨1758111, by rfl⟩ : syracuseStep 4688297 = 3516223) B3516223
theorem B3125531 : Blo 2083435 3125531 := bstep (se 1 (by rfl) ⟨2344148, by rfl⟩ : syracuseStep 3125531 = 4688297) B4688297
theorem B2083687 : Blo 2083435 2083687 := bstep (se 1 (by rfl) ⟨1562765, by rfl⟩ : syracuseStep 2083687 = 3125531) B3125531
theorem B2344153 : Blo 2083435 2344153 := bbase (se 2 (by rfl) ⟨879057, by rfl⟩ : syracuseStep 2344153 = 1758115) (by norm_num)
theorem B3125537 : Blo 2083435 3125537 := bstep (se 2 (by rfl) ⟨1172076, by rfl⟩ : syracuseStep 3125537 = 2344153) B2344153
theorem B2083691 : Blo 2083435 2083691 := bstep (se 1 (by rfl) ⟨1562768, by rfl⟩ : syracuseStep 2083691 = 3125537) B3125537
theorem B18043829 : Blo 2083435 18043829 := bbase (se 5 (by rfl) ⟨845804, by rfl⟩ : syracuseStep 18043829 = 1691609) (by norm_num)
theorem B12029219 : Blo 2083435 12029219 := bstep (se 1 (by rfl) ⟨9021914, by rfl⟩ : syracuseStep 12029219 = 18043829) B18043829
theorem B8019479 : Blo 2083435 8019479 := bstep (se 1 (by rfl) ⟨6014609, by rfl⟩ : syracuseStep 8019479 = 12029219) B12029219
theorem B5346319 : Blo 2083435 5346319 := bstep (se 1 (by rfl) ⟨4009739, by rfl⟩ : syracuseStep 5346319 = 8019479) B8019479
theorem B7128425 : Blo 2083435 7128425 := bstep (se 2 (by rfl) ⟨2673159, by rfl⟩ : syracuseStep 7128425 = 5346319) B5346319
theorem B4752283 : Blo 2083435 4752283 := bstep (se 1 (by rfl) ⟨3564212, by rfl⟩ : syracuseStep 4752283 = 7128425) B7128425
theorem B6336377 : Blo 2083435 6336377 := bstep (se 2 (by rfl) ⟨2376141, by rfl⟩ : syracuseStep 6336377 = 4752283) B4752283
theorem B4224251 : Blo 2083435 4224251 := bstep (se 1 (by rfl) ⟨3168188, by rfl⟩ : syracuseStep 4224251 = 6336377) B6336377
theorem B11264669 : Blo 2083435 11264669 := bstep (se 3 (by rfl) ⟨2112125, by rfl⟩ : syracuseStep 11264669 = 4224251) B4224251
theorem B7509779 : Blo 2083435 7509779 := bstep (se 1 (by rfl) ⟨5632334, by rfl⟩ : syracuseStep 7509779 = 11264669) B11264669
theorem B5006519 : Blo 2083435 5006519 := bstep (se 1 (by rfl) ⟨3754889, by rfl⟩ : syracuseStep 5006519 = 7509779) B7509779
theorem B3337679 : Blo 2083435 3337679 := bstep (se 1 (by rfl) ⟨2503259, by rfl⟩ : syracuseStep 3337679 = 5006519) B5006519
theorem B2225119 : Blo 2083435 2225119 := bstep (se 1 (by rfl) ⟨1668839, by rfl⟩ : syracuseStep 2225119 = 3337679) B3337679
theorem B2966825 : Blo 2083435 2966825 := bstep (se 2 (by rfl) ⟨1112559, by rfl⟩ : syracuseStep 2966825 = 2225119) B2225119
theorem B7911533 : Blo 2083435 7911533 := bstep (se 3 (by rfl) ⟨1483412, by rfl⟩ : syracuseStep 7911533 = 2966825) B2966825
theorem B5274355 : Blo 2083435 5274355 := bstep (se 1 (by rfl) ⟨3955766, by rfl⟩ : syracuseStep 5274355 = 7911533) B7911533
theorem B7032473 : Blo 2083435 7032473 := bstep (se 2 (by rfl) ⟨2637177, by rfl⟩ : syracuseStep 7032473 = 5274355) B5274355
theorem B4688315 : Blo 2083435 4688315 := bstep (se 1 (by rfl) ⟨3516236, by rfl⟩ : syracuseStep 4688315 = 7032473) B7032473
theorem B3125543 : Blo 2083435 3125543 := bstep (se 1 (by rfl) ⟨2344157, by rfl⟩ : syracuseStep 3125543 = 4688315) B4688315
theorem B2083695 : Blo 2083435 2083695 := bstep (se 1 (by rfl) ⟨1562771, by rfl⟩ : syracuseStep 2083695 = 3125543) B3125543
theorem B3125549 : Blo 2083435 3125549 := bbase (se 3 (by rfl) ⟨586040, by rfl⟩ : syracuseStep 3125549 = 1172081) (by norm_num)
theorem B2083699 : Blo 2083435 2083699 := bstep (se 1 (by rfl) ⟨1562774, by rfl⟩ : syracuseStep 2083699 = 3125549) B3125549
theorem B4688333 : Blo 2083435 4688333 := bbase (se 3 (by rfl) ⟨879062, by rfl⟩ : syracuseStep 4688333 = 1758125) (by norm_num)
theorem B3125555 : Blo 2083435 3125555 := bstep (se 1 (by rfl) ⟨2344166, by rfl⟩ : syracuseStep 3125555 = 4688333) B4688333
theorem B2083703 : Blo 2083435 2083703 := bstep (se 1 (by rfl) ⟨1562777, by rfl⟩ : syracuseStep 2083703 = 3125555) B3125555
theorem B2637193 : Blo 2083435 2637193 := bbase (se 2 (by rfl) ⟨988947, by rfl⟩ : syracuseStep 2637193 = 1977895) (by norm_num)
theorem B3516257 : Blo 2083435 3516257 := bstep (se 2 (by rfl) ⟨1318596, by rfl⟩ : syracuseStep 3516257 = 2637193) B2637193
theorem B2344171 : Blo 2083435 2344171 := bstep (se 1 (by rfl) ⟨1758128, by rfl⟩ : syracuseStep 2344171 = 3516257) B3516257
theorem B3125561 : Blo 2083435 3125561 := bstep (se 2 (by rfl) ⟨1172085, by rfl⟩ : syracuseStep 3125561 = 2344171) B2344171
theorem B2083707 : Blo 2083435 2083707 := bstep (se 1 (by rfl) ⟨1562780, by rfl⟩ : syracuseStep 2083707 = 3125561) B3125561
theorem B5709221 : Blo 2083435 5709221 := bbase (se 4 (by rfl) ⟨535239, by rfl⟩ : syracuseStep 5709221 = 1070479) (by norm_num)
theorem B3806147 : Blo 2083435 3806147 := bstep (se 1 (by rfl) ⟨2854610, by rfl⟩ : syracuseStep 3806147 = 5709221) B5709221
theorem B10149725 : Blo 2083435 10149725 := bstep (se 3 (by rfl) ⟨1903073, by rfl⟩ : syracuseStep 10149725 = 3806147) B3806147
theorem B27065933 : Blo 2083435 27065933 := bstep (se 3 (by rfl) ⟨5074862, by rfl⟩ : syracuseStep 27065933 = 10149725) B10149725
theorem B18043955 : Blo 2083435 18043955 := bstep (se 1 (by rfl) ⟨13532966, by rfl⟩ : syracuseStep 18043955 = 27065933) B27065933
theorem B12029303 : Blo 2083435 12029303 := bstep (se 1 (by rfl) ⟨9021977, by rfl⟩ : syracuseStep 12029303 = 18043955) B18043955
theorem B8019535 : Blo 2083435 8019535 := bstep (se 1 (by rfl) ⟨6014651, by rfl⟩ : syracuseStep 8019535 = 12029303) B12029303
theorem B10692713 : Blo 2083435 10692713 := bstep (se 2 (by rfl) ⟨4009767, by rfl⟩ : syracuseStep 10692713 = 8019535) B8019535
theorem B28513901 : Blo 2083435 28513901 := bstep (se 3 (by rfl) ⟨5346356, by rfl⟩ : syracuseStep 28513901 = 10692713) B10692713
theorem B76037069 : Blo 2083435 76037069 := bstep (se 3 (by rfl) ⟨14256950, by rfl⟩ : syracuseStep 76037069 = 28513901) B28513901
theorem B50691379 : Blo 2083435 50691379 := bstep (se 1 (by rfl) ⟨38018534, by rfl⟩ : syracuseStep 50691379 = 76037069) B76037069
theorem B67588505 : Blo 2083435 67588505 := bstep (se 2 (by rfl) ⟨25345689, by rfl⟩ : syracuseStep 67588505 = 50691379) B50691379
theorem B45059003 : Blo 2083435 45059003 := bstep (se 1 (by rfl) ⟨33794252, by rfl⟩ : syracuseStep 45059003 = 67588505) B67588505
theorem B30039335 : Blo 2083435 30039335 := bstep (se 1 (by rfl) ⟨22529501, by rfl⟩ : syracuseStep 30039335 = 45059003) B45059003
theorem B20026223 : Blo 2083435 20026223 := bstep (se 1 (by rfl) ⟨15019667, by rfl⟩ : syracuseStep 20026223 = 30039335) B30039335
theorem B13350815 : Blo 2083435 13350815 := bstep (se 1 (by rfl) ⟨10013111, by rfl⟩ : syracuseStep 13350815 = 20026223) B20026223
theorem B8900543 : Blo 2083435 8900543 := bstep (se 1 (by rfl) ⟨6675407, by rfl⟩ : syracuseStep 8900543 = 13350815) B13350815
theorem B23734781 : Blo 2083435 23734781 := bstep (se 3 (by rfl) ⟨4450271, by rfl⟩ : syracuseStep 23734781 = 8900543) B8900543
theorem B15823187 : Blo 2083435 15823187 := bstep (se 1 (by rfl) ⟨11867390, by rfl⟩ : syracuseStep 15823187 = 23734781) B23734781
theorem B10548791 : Blo 2083435 10548791 := bstep (se 1 (by rfl) ⟨7911593, by rfl⟩ : syracuseStep 10548791 = 15823187) B15823187
theorem B7032527 : Blo 2083435 7032527 := bstep (se 1 (by rfl) ⟨5274395, by rfl⟩ : syracuseStep 7032527 = 10548791) B10548791
theorem B4688351 : Blo 2083435 4688351 := bstep (se 1 (by rfl) ⟨3516263, by rfl⟩ : syracuseStep 4688351 = 7032527) B7032527
theorem B3125567 : Blo 2083435 3125567 := bstep (se 1 (by rfl) ⟨2344175, by rfl⟩ : syracuseStep 3125567 = 4688351) B4688351
theorem B2083711 : Blo 2083435 2083711 := bstep (se 1 (by rfl) ⟨1562783, by rfl⟩ : syracuseStep 2083711 = 3125567) B3125567
theorem B3125573 : Blo 2083435 3125573 := bbase (se 4 (by rfl) ⟨293022, by rfl⟩ : syracuseStep 3125573 = 586045) (by norm_num)
theorem B2083715 : Blo 2083435 2083715 := bstep (se 1 (by rfl) ⟨1562786, by rfl⟩ : syracuseStep 2083715 = 3125573) B3125573
theorem B3516277 : Blo 2083435 3516277 := bbase (se 5 (by rfl) ⟨164825, by rfl⟩ : syracuseStep 3516277 = 329651) (by norm_num)
theorem B4688369 : Blo 2083435 4688369 := bstep (se 2 (by rfl) ⟨1758138, by rfl⟩ : syracuseStep 4688369 = 3516277) B3516277
theorem B3125579 : Blo 2083435 3125579 := bstep (se 1 (by rfl) ⟨2344184, by rfl⟩ : syracuseStep 3125579 = 4688369) B4688369
theorem B2083719 : Blo 2083435 2083719 := bstep (se 1 (by rfl) ⟨1562789, by rfl⟩ : syracuseStep 2083719 = 3125579) B3125579
theorem B2344189 : Blo 2083435 2344189 := bbase (se 3 (by rfl) ⟨439535, by rfl⟩ : syracuseStep 2344189 = 879071) (by norm_num)
theorem B3125585 : Blo 2083435 3125585 := bstep (se 2 (by rfl) ⟨1172094, by rfl⟩ : syracuseStep 3125585 = 2344189) B2344189
theorem B2083723 : Blo 2083435 2083723 := bstep (se 1 (by rfl) ⟨1562792, by rfl⟩ : syracuseStep 2083723 = 3125585) B3125585
theorem B7032581 : Blo 2083435 7032581 := bbase (se 4 (by rfl) ⟨659304, by rfl⟩ : syracuseStep 7032581 = 1318609) (by norm_num)
theorem B4688387 : Blo 2083435 4688387 := bstep (se 1 (by rfl) ⟨3516290, by rfl⟩ : syracuseStep 4688387 = 7032581) B7032581
theorem B3125591 : Blo 2083435 3125591 := bstep (se 1 (by rfl) ⟨2344193, by rfl⟩ : syracuseStep 3125591 = 4688387) B4688387
theorem B2083727 : Blo 2083435 2083727 := bstep (se 1 (by rfl) ⟨1562795, by rfl⟩ : syracuseStep 2083727 = 3125591) B3125591
theorem B3125597 : Blo 2083435 3125597 := bbase (se 3 (by rfl) ⟨586049, by rfl⟩ : syracuseStep 3125597 = 1172099) (by norm_num)
theorem B2083731 : Blo 2083435 2083731 := bstep (se 1 (by rfl) ⟨1562798, by rfl⟩ : syracuseStep 2083731 = 3125597) B3125597
theorem B4688405 : Blo 2083435 4688405 := bbase (se 6 (by rfl) ⟨109884, by rfl⟩ : syracuseStep 4688405 = 219769) (by norm_num)
theorem B3125603 : Blo 2083435 3125603 := bstep (se 1 (by rfl) ⟨2344202, by rfl⟩ : syracuseStep 3125603 = 4688405) B4688405
theorem B2083735 : Blo 2083435 2083735 := bstep (se 1 (by rfl) ⟨1562801, by rfl⟩ : syracuseStep 2083735 = 3125603) B3125603
theorem B7911701 : Blo 2083435 7911701 := bbase (se 6 (by rfl) ⟨185430, by rfl⟩ : syracuseStep 7911701 = 370861) (by norm_num)
theorem B5274467 : Blo 2083435 5274467 := bstep (se 1 (by rfl) ⟨3955850, by rfl⟩ : syracuseStep 5274467 = 7911701) B7911701
theorem B3516311 : Blo 2083435 3516311 := bstep (se 1 (by rfl) ⟨2637233, by rfl⟩ : syracuseStep 3516311 = 5274467) B5274467
theorem B2344207 : Blo 2083435 2344207 := bstep (se 1 (by rfl) ⟨1758155, by rfl⟩ : syracuseStep 2344207 = 3516311) B3516311
theorem B3125609 : Blo 2083435 3125609 := bstep (se 2 (by rfl) ⟨1172103, by rfl⟩ : syracuseStep 3125609 = 2344207) B2344207
theorem B2083739 : Blo 2083435 2083739 := bstep (se 1 (by rfl) ⟨1562804, by rfl⟩ : syracuseStep 2083739 = 3125609) B3125609
theorem B11867573 : Blo 2083435 11867573 := bbase (se 5 (by rfl) ⟨556292, by rfl⟩ : syracuseStep 11867573 = 1112585) (by norm_num)
theorem B7911715 : Blo 2083435 7911715 := bstep (se 1 (by rfl) ⟨5933786, by rfl⟩ : syracuseStep 7911715 = 11867573) B11867573
theorem B10548953 : Blo 2083435 10548953 := bstep (se 2 (by rfl) ⟨3955857, by rfl⟩ : syracuseStep 10548953 = 7911715) B7911715
theorem B7032635 : Blo 2083435 7032635 := bstep (se 1 (by rfl) ⟨5274476, by rfl⟩ : syracuseStep 7032635 = 10548953) B10548953
theorem B4688423 : Blo 2083435 4688423 := bstep (se 1 (by rfl) ⟨3516317, by rfl⟩ : syracuseStep 4688423 = 7032635) B7032635
theorem B3125615 : Blo 2083435 3125615 := bstep (se 1 (by rfl) ⟨2344211, by rfl⟩ : syracuseStep 3125615 = 4688423) B4688423
theorem B2083743 : Blo 2083435 2083743 := bstep (se 1 (by rfl) ⟨1562807, by rfl⟩ : syracuseStep 2083743 = 3125615) B3125615
theorem B3125621 : Blo 2083435 3125621 := bbase (se 5 (by rfl) ⟨146513, by rfl⟩ : syracuseStep 3125621 = 293027) (by norm_num)
theorem B2083747 : Blo 2083435 2083747 := bstep (se 1 (by rfl) ⟨1562810, by rfl⟩ : syracuseStep 2083747 = 3125621) B3125621
theorem B7225877 : Blo 2083435 7225877 := bbase (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) (by norm_num)
theorem B4817251 : Blo 2083435 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B25692005 : Blo 2083435 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B68512013 : Blo 2083435 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B45674675 : Blo 2083435 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B30449783 : Blo 2083435 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B20299855 : Blo 2083435 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B27066473 : Blo 2083435 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B18044315 : Blo 2083435 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B12029543 : Blo 2083435 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B8019695 : Blo 2083435 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B21385853 : Blo 2083435 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B14257235 : Blo 2083435 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B9504823 : Blo 2083435 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B12673097 : Blo 2083435 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B8448731 : Blo 2083435 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B5632487 : Blo 2083435 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B3754991 : Blo 2083435 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B2503327 : Blo 2083435 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B3337769 : Blo 2083435 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B2225179 : Blo 2083435 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B2966905 : Blo 2083435 2966905 := bstep (se 2 (by rfl) ⟨1112589, by rfl⟩ : syracuseStep 2966905 = 2225179) B2225179
theorem B3955873 : Blo 2083435 3955873 := bstep (se 2 (by rfl) ⟨1483452, by rfl⟩ : syracuseStep 3955873 = 2966905) B2966905
theorem B5274497 : Blo 2083435 5274497 := bstep (se 2 (by rfl) ⟨1977936, by rfl⟩ : syracuseStep 5274497 = 3955873) B3955873
theorem B3516331 : Blo 2083435 3516331 := bstep (se 1 (by rfl) ⟨2637248, by rfl⟩ : syracuseStep 3516331 = 5274497) B5274497
theorem B4688441 : Blo 2083435 4688441 := bstep (se 2 (by rfl) ⟨1758165, by rfl⟩ : syracuseStep 4688441 = 3516331) B3516331
theorem B3125627 : Blo 2083435 3125627 := bstep (se 1 (by rfl) ⟨2344220, by rfl⟩ : syracuseStep 3125627 = 4688441) B4688441
theorem B2083751 : Blo 2083435 2083751 := bstep (se 1 (by rfl) ⟨1562813, by rfl⟩ : syracuseStep 2083751 = 3125627) B3125627
theorem B2344225 : Blo 2083435 2344225 := bbase (se 2 (by rfl) ⟨879084, by rfl⟩ : syracuseStep 2344225 = 1758169) (by norm_num)
theorem B3125633 : Blo 2083435 3125633 := bstep (se 2 (by rfl) ⟨1172112, by rfl⟩ : syracuseStep 3125633 = 2344225) B2344225
theorem B2083755 : Blo 2083435 2083755 := bstep (se 1 (by rfl) ⟨1562816, by rfl⟩ : syracuseStep 2083755 = 3125633) B3125633
theorem B5274517 : Blo 2083435 5274517 := bbase (se 6 (by rfl) ⟨123621, by rfl⟩ : syracuseStep 5274517 = 247243) (by norm_num)
theorem B7032689 : Blo 2083435 7032689 := bstep (se 2 (by rfl) ⟨2637258, by rfl⟩ : syracuseStep 7032689 = 5274517) B5274517
theorem B4688459 : Blo 2083435 4688459 := bstep (se 1 (by rfl) ⟨3516344, by rfl⟩ : syracuseStep 4688459 = 7032689) B7032689
theorem B3125639 : Blo 2083435 3125639 := bstep (se 1 (by rfl) ⟨2344229, by rfl⟩ : syracuseStep 3125639 = 4688459) B4688459
theorem B2083759 : Blo 2083435 2083759 := bstep (se 1 (by rfl) ⟨1562819, by rfl⟩ : syracuseStep 2083759 = 3125639) B3125639
theorem B3125645 : Blo 2083435 3125645 := bbase (se 3 (by rfl) ⟨586058, by rfl⟩ : syracuseStep 3125645 = 1172117) (by norm_num)
theorem B2083763 : Blo 2083435 2083763 := bstep (se 1 (by rfl) ⟨1562822, by rfl⟩ : syracuseStep 2083763 = 3125645) B3125645
theorem B4688477 : Blo 2083435 4688477 := bbase (se 3 (by rfl) ⟨879089, by rfl⟩ : syracuseStep 4688477 = 1758179) (by norm_num)
theorem B3125651 : Blo 2083435 3125651 := bstep (se 1 (by rfl) ⟨2344238, by rfl⟩ : syracuseStep 3125651 = 4688477) B4688477
theorem B2083767 : Blo 2083435 2083767 := bstep (se 1 (by rfl) ⟨1562825, by rfl⟩ : syracuseStep 2083767 = 3125651) B3125651
theorem B3516365 : Blo 2083435 3516365 := bbase (se 3 (by rfl) ⟨659318, by rfl⟩ : syracuseStep 3516365 = 1318637) (by norm_num)
theorem B2344243 : Blo 2083435 2344243 := bstep (se 1 (by rfl) ⟨1758182, by rfl⟩ : syracuseStep 2344243 = 3516365) B3516365
theorem B3125657 : Blo 2083435 3125657 := bstep (se 2 (by rfl) ⟨1172121, by rfl⟩ : syracuseStep 3125657 = 2344243) B2344243
theorem B2083771 : Blo 2083435 2083771 := bstep (se 1 (by rfl) ⟨1562828, by rfl⟩ : syracuseStep 2083771 = 3125657) B3125657
theorem B6014837 : Blo 2083435 6014837 := bbase (se 5 (by rfl) ⟨281945, by rfl⟩ : syracuseStep 6014837 = 563891) (by norm_num)
theorem B16039565 : Blo 2083435 16039565 := bstep (se 3 (by rfl) ⟨3007418, by rfl⟩ : syracuseStep 16039565 = 6014837) B6014837
theorem B10693043 : Blo 2083435 10693043 := bstep (se 1 (by rfl) ⟨8019782, by rfl⟩ : syracuseStep 10693043 = 16039565) B16039565
theorem B7128695 : Blo 2083435 7128695 := bstep (se 1 (by rfl) ⟨5346521, by rfl⟩ : syracuseStep 7128695 = 10693043) B10693043
theorem B19009853 : Blo 2083435 19009853 := bstep (se 3 (by rfl) ⟨3564347, by rfl⟩ : syracuseStep 19009853 = 7128695) B7128695
theorem B12673235 : Blo 2083435 12673235 := bstep (se 1 (by rfl) ⟨9504926, by rfl⟩ : syracuseStep 12673235 = 19009853) B19009853
theorem B8448823 : Blo 2083435 8448823 := bstep (se 1 (by rfl) ⟨6336617, by rfl⟩ : syracuseStep 8448823 = 12673235) B12673235
theorem B11265097 : Blo 2083435 11265097 := bstep (se 2 (by rfl) ⟨4224411, by rfl⟩ : syracuseStep 11265097 = 8448823) B8448823
theorem B15020129 : Blo 2083435 15020129 := bstep (se 2 (by rfl) ⟨5632548, by rfl⟩ : syracuseStep 15020129 = 11265097) B11265097
theorem B10013419 : Blo 2083435 10013419 := bstep (se 1 (by rfl) ⟨7510064, by rfl⟩ : syracuseStep 10013419 = 15020129) B15020129
theorem B13351225 : Blo 2083435 13351225 := bstep (se 2 (by rfl) ⟨5006709, by rfl⟩ : syracuseStep 13351225 = 10013419) B10013419
theorem B17801633 : Blo 2083435 17801633 := bstep (se 2 (by rfl) ⟨6675612, by rfl⟩ : syracuseStep 17801633 = 13351225) B13351225
theorem B11867755 : Blo 2083435 11867755 := bstep (se 1 (by rfl) ⟨8900816, by rfl⟩ : syracuseStep 11867755 = 17801633) B17801633
theorem B15823673 : Blo 2083435 15823673 := bstep (se 2 (by rfl) ⟨5933877, by rfl⟩ : syracuseStep 15823673 = 11867755) B11867755
theorem B10549115 : Blo 2083435 10549115 := bstep (se 1 (by rfl) ⟨7911836, by rfl⟩ : syracuseStep 10549115 = 15823673) B15823673
theorem B7032743 : Blo 2083435 7032743 := bstep (se 1 (by rfl) ⟨5274557, by rfl⟩ : syracuseStep 7032743 = 10549115) B10549115
theorem B4688495 : Blo 2083435 4688495 := bstep (se 1 (by rfl) ⟨3516371, by rfl⟩ : syracuseStep 4688495 = 7032743) B7032743
theorem B3125663 : Blo 2083435 3125663 := bstep (se 1 (by rfl) ⟨2344247, by rfl⟩ : syracuseStep 3125663 = 4688495) B4688495
theorem B2083775 : Blo 2083435 2083775 := bstep (se 1 (by rfl) ⟨1562831, by rfl⟩ : syracuseStep 2083775 = 3125663) B3125663
theorem B3125669 : Blo 2083435 3125669 := bbase (se 4 (by rfl) ⟨293031, by rfl⟩ : syracuseStep 3125669 = 586063) (by norm_num)
theorem B2083779 : Blo 2083435 2083779 := bstep (se 1 (by rfl) ⟨1562834, by rfl⟩ : syracuseStep 2083779 = 3125669) B3125669
theorem B2637289 : Blo 2083435 2637289 := bbase (se 2 (by rfl) ⟨988983, by rfl⟩ : syracuseStep 2637289 = 1977967) (by norm_num)
theorem B3516385 : Blo 2083435 3516385 := bstep (se 2 (by rfl) ⟨1318644, by rfl⟩ : syracuseStep 3516385 = 2637289) B2637289
theorem B4688513 : Blo 2083435 4688513 := bstep (se 2 (by rfl) ⟨1758192, by rfl⟩ : syracuseStep 4688513 = 3516385) B3516385
theorem B3125675 : Blo 2083435 3125675 := bstep (se 1 (by rfl) ⟨2344256, by rfl⟩ : syracuseStep 3125675 = 4688513) B4688513
theorem B2083783 : Blo 2083435 2083783 := bstep (se 1 (by rfl) ⟨1562837, by rfl⟩ : syracuseStep 2083783 = 3125675) B3125675
theorem B2344261 : Blo 2083435 2344261 := bbase (se 4 (by rfl) ⟨219774, by rfl⟩ : syracuseStep 2344261 = 439549) (by norm_num)
theorem B3125681 : Blo 2083435 3125681 := bstep (se 2 (by rfl) ⟨1172130, by rfl⟩ : syracuseStep 3125681 = 2344261) B2344261
theorem B2083787 : Blo 2083435 2083787 := bstep (se 1 (by rfl) ⟨1562840, by rfl⟩ : syracuseStep 2083787 = 3125681) B3125681
theorem B3955949 : Blo 2083435 3955949 := bbase (se 3 (by rfl) ⟨741740, by rfl⟩ : syracuseStep 3955949 = 1483481) (by norm_num)
theorem B2637299 : Blo 2083435 2637299 := bstep (se 1 (by rfl) ⟨1977974, by rfl⟩ : syracuseStep 2637299 = 3955949) B3955949
theorem B7032797 : Blo 2083435 7032797 := bstep (se 3 (by rfl) ⟨1318649, by rfl⟩ : syracuseStep 7032797 = 2637299) B2637299
theorem B4688531 : Blo 2083435 4688531 := bstep (se 1 (by rfl) ⟨3516398, by rfl⟩ : syracuseStep 4688531 = 7032797) B7032797
theorem B3125687 : Blo 2083435 3125687 := bstep (se 1 (by rfl) ⟨2344265, by rfl⟩ : syracuseStep 3125687 = 4688531) B4688531
theorem B2083791 : Blo 2083435 2083791 := bstep (se 1 (by rfl) ⟨1562843, by rfl⟩ : syracuseStep 2083791 = 3125687) B3125687
theorem B3125693 : Blo 2083435 3125693 := bbase (se 3 (by rfl) ⟨586067, by rfl⟩ : syracuseStep 3125693 = 1172135) (by norm_num)
theorem B2083795 : Blo 2083435 2083795 := bstep (se 1 (by rfl) ⟨1562846, by rfl⟩ : syracuseStep 2083795 = 3125693) B3125693
theorem B4688549 : Blo 2083435 4688549 := bbase (se 4 (by rfl) ⟨439551, by rfl⟩ : syracuseStep 4688549 = 879103) (by norm_num)
theorem B3125699 : Blo 2083435 3125699 := bstep (se 1 (by rfl) ⟨2344274, by rfl⟩ : syracuseStep 3125699 = 4688549) B4688549
theorem B2083799 : Blo 2083435 2083799 := bstep (se 1 (by rfl) ⟨1562849, by rfl⟩ : syracuseStep 2083799 = 3125699) B3125699
theorem B5274629 : Blo 2083435 5274629 := bbase (se 4 (by rfl) ⟨494496, by rfl⟩ : syracuseStep 5274629 = 988993) (by norm_num)
theorem B3516419 : Blo 2083435 3516419 := bstep (se 1 (by rfl) ⟨2637314, by rfl⟩ : syracuseStep 3516419 = 5274629) B5274629
theorem B2344279 : Blo 2083435 2344279 := bstep (se 1 (by rfl) ⟨1758209, by rfl⟩ : syracuseStep 2344279 = 3516419) B3516419
theorem B3125705 : Blo 2083435 3125705 := bstep (se 2 (by rfl) ⟨1172139, by rfl⟩ : syracuseStep 3125705 = 2344279) B2344279
theorem B2083803 : Blo 2083435 2083803 := bstep (se 1 (by rfl) ⟨1562852, by rfl⟩ : syracuseStep 2083803 = 3125705) B3125705
theorem B4450477 : Blo 2083435 4450477 := bbase (se 3 (by rfl) ⟨834464, by rfl⟩ : syracuseStep 4450477 = 1668929) (by norm_num)
theorem B5933969 : Blo 2083435 5933969 := bstep (se 2 (by rfl) ⟨2225238, by rfl⟩ : syracuseStep 5933969 = 4450477) B4450477
theorem B3955979 : Blo 2083435 3955979 := bstep (se 1 (by rfl) ⟨2966984, by rfl⟩ : syracuseStep 3955979 = 5933969) B5933969
theorem B10549277 : Blo 2083435 10549277 := bstep (se 3 (by rfl) ⟨1977989, by rfl⟩ : syracuseStep 10549277 = 3955979) B3955979
theorem B7032851 : Blo 2083435 7032851 := bstep (se 1 (by rfl) ⟨5274638, by rfl⟩ : syracuseStep 7032851 = 10549277) B10549277
theorem B4688567 : Blo 2083435 4688567 := bstep (se 1 (by rfl) ⟨3516425, by rfl⟩ : syracuseStep 4688567 = 7032851) B7032851
theorem B3125711 : Blo 2083435 3125711 := bstep (se 1 (by rfl) ⟨2344283, by rfl⟩ : syracuseStep 3125711 = 4688567) B4688567
theorem B2083807 : Blo 2083435 2083807 := bstep (se 1 (by rfl) ⟨1562855, by rfl⟩ : syracuseStep 2083807 = 3125711) B3125711
theorem B3125717 : Blo 2083435 3125717 := bbase (se 7 (by rfl) ⟨36629, by rfl⟩ : syracuseStep 3125717 = 73259) (by norm_num)
theorem B2083811 : Blo 2083435 2083811 := bstep (se 1 (by rfl) ⟨1562858, by rfl⟩ : syracuseStep 2083811 = 3125717) B3125717
theorem B7911989 : Blo 2083435 7911989 := bbase (se 5 (by rfl) ⟨370874, by rfl⟩ : syracuseStep 7911989 = 741749) (by norm_num)
theorem B5274659 : Blo 2083435 5274659 := bstep (se 1 (by rfl) ⟨3955994, by rfl⟩ : syracuseStep 5274659 = 7911989) B7911989
theorem B3516439 : Blo 2083435 3516439 := bstep (se 1 (by rfl) ⟨2637329, by rfl⟩ : syracuseStep 3516439 = 5274659) B5274659
theorem B4688585 : Blo 2083435 4688585 := bstep (se 2 (by rfl) ⟨1758219, by rfl⟩ : syracuseStep 4688585 = 3516439) B3516439
theorem B3125723 : Blo 2083435 3125723 := bstep (se 1 (by rfl) ⟨2344292, by rfl⟩ : syracuseStep 3125723 = 4688585) B4688585
theorem B2083815 : Blo 2083435 2083815 := bstep (se 1 (by rfl) ⟨1562861, by rfl⟩ : syracuseStep 2083815 = 3125723) B3125723
theorem B2344297 : Blo 2083435 2344297 := bbase (se 2 (by rfl) ⟨879111, by rfl⟩ : syracuseStep 2344297 = 1758223) (by norm_num)
theorem B3125729 : Blo 2083435 3125729 := bstep (se 2 (by rfl) ⟨1172148, by rfl⟩ : syracuseStep 3125729 = 2344297) B2344297
theorem B2083819 : Blo 2083435 2083819 := bstep (se 1 (by rfl) ⟨1562864, by rfl⟩ : syracuseStep 2083819 = 3125729) B3125729
theorem B2854765 : Blo 2083435 2854765 := bbase (se 3 (by rfl) ⟨535268, by rfl⟩ : syracuseStep 2854765 = 1070537) (by norm_num)
theorem B3806353 : Blo 2083435 3806353 := bstep (se 2 (by rfl) ⟨1427382, by rfl⟩ : syracuseStep 3806353 = 2854765) B2854765
theorem B5075137 : Blo 2083435 5075137 := bstep (se 2 (by rfl) ⟨1903176, by rfl⟩ : syracuseStep 5075137 = 3806353) B3806353
theorem B6766849 : Blo 2083435 6766849 := bstep (se 2 (by rfl) ⟨2537568, by rfl⟩ : syracuseStep 6766849 = 5075137) B5075137
theorem B9022465 : Blo 2083435 9022465 := bstep (se 2 (by rfl) ⟨3383424, by rfl⟩ : syracuseStep 9022465 = 6766849) B6766849
theorem B12029953 : Blo 2083435 12029953 := bstep (se 2 (by rfl) ⟨4511232, by rfl⟩ : syracuseStep 12029953 = 9022465) B9022465
theorem B16039937 : Blo 2083435 16039937 := bstep (se 2 (by rfl) ⟨6014976, by rfl⟩ : syracuseStep 16039937 = 12029953) B12029953
theorem B10693291 : Blo 2083435 10693291 := bstep (se 1 (by rfl) ⟨8019968, by rfl⟩ : syracuseStep 10693291 = 16039937) B16039937
theorem B14257721 : Blo 2083435 14257721 := bstep (se 2 (by rfl) ⟨5346645, by rfl⟩ : syracuseStep 14257721 = 10693291) B10693291
theorem B9505147 : Blo 2083435 9505147 := bstep (se 1 (by rfl) ⟨7128860, by rfl⟩ : syracuseStep 9505147 = 14257721) B14257721
theorem B12673529 : Blo 2083435 12673529 := bstep (se 2 (by rfl) ⟨4752573, by rfl⟩ : syracuseStep 12673529 = 9505147) B9505147
theorem B8449019 : Blo 2083435 8449019 := bstep (se 1 (by rfl) ⟨6336764, by rfl⟩ : syracuseStep 8449019 = 12673529) B12673529
theorem B5632679 : Blo 2083435 5632679 := bstep (se 1 (by rfl) ⟨4224509, by rfl⟩ : syracuseStep 5632679 = 8449019) B8449019
theorem B15020477 : Blo 2083435 15020477 := bstep (se 3 (by rfl) ⟨2816339, by rfl⟩ : syracuseStep 15020477 = 5632679) B5632679
theorem B10013651 : Blo 2083435 10013651 := bstep (se 1 (by rfl) ⟨7510238, by rfl⟩ : syracuseStep 10013651 = 15020477) B15020477
theorem B6675767 : Blo 2083435 6675767 := bstep (se 1 (by rfl) ⟨5006825, by rfl⟩ : syracuseStep 6675767 = 10013651) B10013651
theorem B4450511 : Blo 2083435 4450511 := bstep (se 1 (by rfl) ⟨3337883, by rfl⟩ : syracuseStep 4450511 = 6675767) B6675767
theorem B11868029 : Blo 2083435 11868029 := bstep (se 3 (by rfl) ⟨2225255, by rfl⟩ : syracuseStep 11868029 = 4450511) B4450511
theorem B7912019 : Blo 2083435 7912019 := bstep (se 1 (by rfl) ⟨5934014, by rfl⟩ : syracuseStep 7912019 = 11868029) B11868029
theorem B5274679 : Blo 2083435 5274679 := bstep (se 1 (by rfl) ⟨3956009, by rfl⟩ : syracuseStep 5274679 = 7912019) B7912019
theorem B7032905 : Blo 2083435 7032905 := bstep (se 2 (by rfl) ⟨2637339, by rfl⟩ : syracuseStep 7032905 = 5274679) B5274679
theorem B4688603 : Blo 2083435 4688603 := bstep (se 1 (by rfl) ⟨3516452, by rfl⟩ : syracuseStep 4688603 = 7032905) B7032905
theorem B3125735 : Blo 2083435 3125735 := bstep (se 1 (by rfl) ⟨2344301, by rfl⟩ : syracuseStep 3125735 = 4688603) B4688603
theorem B2083823 : Blo 2083435 2083823 := bstep (se 1 (by rfl) ⟨1562867, by rfl⟩ : syracuseStep 2083823 = 3125735) B3125735
theorem B3125741 : Blo 2083435 3125741 := bbase (se 3 (by rfl) ⟨586076, by rfl⟩ : syracuseStep 3125741 = 1172153) (by norm_num)
theorem B2083827 : Blo 2083435 2083827 := bstep (se 1 (by rfl) ⟨1562870, by rfl⟩ : syracuseStep 2083827 = 3125741) B3125741
theorem B4688621 : Blo 2083435 4688621 := bbase (se 3 (by rfl) ⟨879116, by rfl⟩ : syracuseStep 4688621 = 1758233) (by norm_num)
theorem B3125747 : Blo 2083435 3125747 := bstep (se 1 (by rfl) ⟨2344310, by rfl⟩ : syracuseStep 3125747 = 4688621) B4688621
theorem B2083831 : Blo 2083435 2083831 := bstep (se 1 (by rfl) ⟨1562873, by rfl⟩ : syracuseStep 2083831 = 3125747) B3125747
theorem B2225269 : Blo 2083435 2225269 := bbase (se 5 (by rfl) ⟨104309, by rfl⟩ : syracuseStep 2225269 = 208619) (by norm_num)
theorem B2967025 : Blo 2083435 2967025 := bstep (se 2 (by rfl) ⟨1112634, by rfl⟩ : syracuseStep 2967025 = 2225269) B2225269
theorem B3956033 : Blo 2083435 3956033 := bstep (se 2 (by rfl) ⟨1483512, by rfl⟩ : syracuseStep 3956033 = 2967025) B2967025
theorem B2637355 : Blo 2083435 2637355 := bstep (se 1 (by rfl) ⟨1978016, by rfl⟩ : syracuseStep 2637355 = 3956033) B3956033
theorem B3516473 : Blo 2083435 3516473 := bstep (se 2 (by rfl) ⟨1318677, by rfl⟩ : syracuseStep 3516473 = 2637355) B2637355
theorem B2344315 : Blo 2083435 2344315 := bstep (se 1 (by rfl) ⟨1758236, by rfl⟩ : syracuseStep 2344315 = 3516473) B3516473
theorem B3125753 : Blo 2083435 3125753 := bstep (se 2 (by rfl) ⟨1172157, by rfl⟩ : syracuseStep 3125753 = 2344315) B2344315
theorem B2083835 : Blo 2083435 2083835 := bstep (se 1 (by rfl) ⟨1562876, by rfl⟩ : syracuseStep 2083835 = 3125753) B3125753
theorem B4224541 : Blo 2083435 4224541 := bbase (se 3 (by rfl) ⟨792101, by rfl⟩ : syracuseStep 4224541 = 1584203) (by norm_num)
theorem B5632721 : Blo 2083435 5632721 := bstep (se 2 (by rfl) ⟨2112270, by rfl⟩ : syracuseStep 5632721 = 4224541) B4224541
theorem B60082357 : Blo 2083435 60082357 := bstep (se 5 (by rfl) ⟨2816360, by rfl⟩ : syracuseStep 60082357 = 5632721) B5632721
theorem B80109809 : Blo 2083435 80109809 := bstep (se 2 (by rfl) ⟨30041178, by rfl⟩ : syracuseStep 80109809 = 60082357) B60082357
theorem B53406539 : Blo 2083435 53406539 := bstep (se 1 (by rfl) ⟨40054904, by rfl⟩ : syracuseStep 53406539 = 80109809) B80109809
theorem B35604359 : Blo 2083435 35604359 := bstep (se 1 (by rfl) ⟨26703269, by rfl⟩ : syracuseStep 35604359 = 53406539) B53406539
theorem B23736239 : Blo 2083435 23736239 := bstep (se 1 (by rfl) ⟨17802179, by rfl⟩ : syracuseStep 23736239 = 35604359) B35604359
theorem B15824159 : Blo 2083435 15824159 := bstep (se 1 (by rfl) ⟨11868119, by rfl⟩ : syracuseStep 15824159 = 23736239) B23736239
theorem B10549439 : Blo 2083435 10549439 := bstep (se 1 (by rfl) ⟨7912079, by rfl⟩ : syracuseStep 10549439 = 15824159) B15824159
theorem B7032959 : Blo 2083435 7032959 := bstep (se 1 (by rfl) ⟨5274719, by rfl⟩ : syracuseStep 7032959 = 10549439) B10549439
theorem B4688639 : Blo 2083435 4688639 := bstep (se 1 (by rfl) ⟨3516479, by rfl⟩ : syracuseStep 4688639 = 7032959) B7032959
theorem B3125759 : Blo 2083435 3125759 := bstep (se 1 (by rfl) ⟨2344319, by rfl⟩ : syracuseStep 3125759 = 4688639) B4688639
theorem B2083839 : Blo 2083435 2083839 := bstep (se 1 (by rfl) ⟨1562879, by rfl⟩ : syracuseStep 2083839 = 3125759) B3125759
theorem B3125765 : Blo 2083435 3125765 := bbase (se 4 (by rfl) ⟨293040, by rfl⟩ : syracuseStep 3125765 = 586081) (by norm_num)
theorem B2083843 : Blo 2083435 2083843 := bstep (se 1 (by rfl) ⟨1562882, by rfl⟩ : syracuseStep 2083843 = 3125765) B3125765
theorem B3516493 : Blo 2083435 3516493 := bbase (se 3 (by rfl) ⟨659342, by rfl⟩ : syracuseStep 3516493 = 1318685) (by norm_num)
theorem B4688657 : Blo 2083435 4688657 := bstep (se 2 (by rfl) ⟨1758246, by rfl⟩ : syracuseStep 4688657 = 3516493) B3516493
theorem B3125771 : Blo 2083435 3125771 := bstep (se 1 (by rfl) ⟨2344328, by rfl⟩ : syracuseStep 3125771 = 4688657) B4688657
theorem B2083847 : Blo 2083435 2083847 := bstep (se 1 (by rfl) ⟨1562885, by rfl⟩ : syracuseStep 2083847 = 3125771) B3125771
theorem B2344333 : Blo 2083435 2344333 := bbase (se 3 (by rfl) ⟨439562, by rfl⟩ : syracuseStep 2344333 = 879125) (by norm_num)
theorem B3125777 : Blo 2083435 3125777 := bstep (se 2 (by rfl) ⟨1172166, by rfl⟩ : syracuseStep 3125777 = 2344333) B2344333
theorem B2083851 : Blo 2083435 2083851 := bstep (se 1 (by rfl) ⟨1562888, by rfl⟩ : syracuseStep 2083851 = 3125777) B3125777
theorem B7033013 : Blo 2083435 7033013 := bbase (se 5 (by rfl) ⟨329672, by rfl⟩ : syracuseStep 7033013 = 659345) (by norm_num)
theorem B4688675 : Blo 2083435 4688675 := bstep (se 1 (by rfl) ⟨3516506, by rfl⟩ : syracuseStep 4688675 = 7033013) B7033013
theorem B3125783 : Blo 2083435 3125783 := bstep (se 1 (by rfl) ⟨2344337, by rfl⟩ : syracuseStep 3125783 = 4688675) B4688675
theorem B2083855 : Blo 2083435 2083855 := bstep (se 1 (by rfl) ⟨1562891, by rfl⟩ : syracuseStep 2083855 = 3125783) B3125783
theorem B3125789 : Blo 2083435 3125789 := bbase (se 3 (by rfl) ⟨586085, by rfl⟩ : syracuseStep 3125789 = 1172171) (by norm_num)
theorem B2083859 : Blo 2083435 2083859 := bstep (se 1 (by rfl) ⟨1562894, by rfl⟩ : syracuseStep 2083859 = 3125789) B3125789
theorem B4688693 : Blo 2083435 4688693 := bbase (se 5 (by rfl) ⟨219782, by rfl⟩ : syracuseStep 4688693 = 439565) (by norm_num)
theorem B3125795 : Blo 2083435 3125795 := bstep (se 1 (by rfl) ⟨2344346, by rfl⟩ : syracuseStep 3125795 = 4688693) B4688693
theorem B2083863 : Blo 2083435 2083863 := bstep (se 1 (by rfl) ⟨1562897, by rfl⟩ : syracuseStep 2083863 = 3125795) B3125795
theorem B10839413 : Blo 2083435 10839413 := bbase (se 5 (by rfl) ⟨508097, by rfl⟩ : syracuseStep 10839413 = 1016195) (by norm_num)
theorem B28905101 : Blo 2083435 28905101 := bstep (se 3 (by rfl) ⟨5419706, by rfl⟩ : syracuseStep 28905101 = 10839413) B10839413
theorem B19270067 : Blo 2083435 19270067 := bstep (se 1 (by rfl) ⟨14452550, by rfl⟩ : syracuseStep 19270067 = 28905101) B28905101
theorem B51386845 : Blo 2083435 51386845 := bstep (se 3 (by rfl) ⟨9635033, by rfl⟩ : syracuseStep 51386845 = 19270067) B19270067
theorem B68515793 : Blo 2083435 68515793 := bstep (se 2 (by rfl) ⟨25693422, by rfl⟩ : syracuseStep 68515793 = 51386845) B51386845
theorem B45677195 : Blo 2083435 45677195 := bstep (se 1 (by rfl) ⟨34257896, by rfl⟩ : syracuseStep 45677195 = 68515793) B68515793
theorem B30451463 : Blo 2083435 30451463 := bstep (se 1 (by rfl) ⟨22838597, by rfl⟩ : syracuseStep 30451463 = 45677195) B45677195
theorem B20300975 : Blo 2083435 20300975 := bstep (se 1 (by rfl) ⟨15225731, by rfl⟩ : syracuseStep 20300975 = 30451463) B30451463
theorem B13533983 : Blo 2083435 13533983 := bstep (se 1 (by rfl) ⟨10150487, by rfl⟩ : syracuseStep 13533983 = 20300975) B20300975
theorem B9022655 : Blo 2083435 9022655 := bstep (se 1 (by rfl) ⟨6766991, by rfl⟩ : syracuseStep 9022655 = 13533983) B13533983
theorem B6015103 : Blo 2083435 6015103 := bstep (se 1 (by rfl) ⟨4511327, by rfl⟩ : syracuseStep 6015103 = 9022655) B9022655
theorem B32080549 : Blo 2083435 32080549 := bstep (se 4 (by rfl) ⟨3007551, by rfl⟩ : syracuseStep 32080549 = 6015103) B6015103
theorem B42774065 : Blo 2083435 42774065 := bstep (se 2 (by rfl) ⟨16040274, by rfl⟩ : syracuseStep 42774065 = 32080549) B32080549
theorem B28516043 : Blo 2083435 28516043 := bstep (se 1 (by rfl) ⟨21387032, by rfl⟩ : syracuseStep 28516043 = 42774065) B42774065
theorem B19010695 : Blo 2083435 19010695 := bstep (se 1 (by rfl) ⟨14258021, by rfl⟩ : syracuseStep 19010695 = 28516043) B28516043
theorem B25347593 : Blo 2083435 25347593 := bstep (se 2 (by rfl) ⟨9505347, by rfl⟩ : syracuseStep 25347593 = 19010695) B19010695
theorem B16898395 : Blo 2083435 16898395 := bstep (se 1 (by rfl) ⟨12673796, by rfl⟩ : syracuseStep 16898395 = 25347593) B25347593
theorem B22531193 : Blo 2083435 22531193 := bstep (se 2 (by rfl) ⟨8449197, by rfl⟩ : syracuseStep 22531193 = 16898395) B16898395
theorem B15020795 : Blo 2083435 15020795 := bstep (se 1 (by rfl) ⟨11265596, by rfl⟩ : syracuseStep 15020795 = 22531193) B22531193
theorem B10013863 : Blo 2083435 10013863 := bstep (se 1 (by rfl) ⟨7510397, by rfl⟩ : syracuseStep 10013863 = 15020795) B15020795
theorem B13351817 : Blo 2083435 13351817 := bstep (se 2 (by rfl) ⟨5006931, by rfl⟩ : syracuseStep 13351817 = 10013863) B10013863
theorem B8901211 : Blo 2083435 8901211 := bstep (se 1 (by rfl) ⟨6675908, by rfl⟩ : syracuseStep 8901211 = 13351817) B13351817
theorem B11868281 : Blo 2083435 11868281 := bstep (se 2 (by rfl) ⟨4450605, by rfl⟩ : syracuseStep 11868281 = 8901211) B8901211
theorem B7912187 : Blo 2083435 7912187 := bstep (se 1 (by rfl) ⟨5934140, by rfl⟩ : syracuseStep 7912187 = 11868281) B11868281
theorem B5274791 : Blo 2083435 5274791 := bstep (se 1 (by rfl) ⟨3956093, by rfl⟩ : syracuseStep 5274791 = 7912187) B7912187
theorem B3516527 : Blo 2083435 3516527 := bstep (se 1 (by rfl) ⟨2637395, by rfl⟩ : syracuseStep 3516527 = 5274791) B5274791
theorem B2344351 : Blo 2083435 2344351 := bstep (se 1 (by rfl) ⟨1758263, by rfl⟩ : syracuseStep 2344351 = 3516527) B3516527
theorem B3125801 : Blo 2083435 3125801 := bstep (se 2 (by rfl) ⟨1172175, by rfl⟩ : syracuseStep 3125801 = 2344351) B2344351
theorem B2083867 : Blo 2083435 2083867 := bstep (se 1 (by rfl) ⟨1562900, by rfl⟩ : syracuseStep 2083867 = 3125801) B3125801
theorem B4010077 : Blo 2083435 4010077 := bbase (se 3 (by rfl) ⟨751889, by rfl⟩ : syracuseStep 4010077 = 1503779) (by norm_num)
theorem B5346769 : Blo 2083435 5346769 := bstep (se 2 (by rfl) ⟨2005038, by rfl⟩ : syracuseStep 5346769 = 4010077) B4010077
theorem B7129025 : Blo 2083435 7129025 := bstep (se 2 (by rfl) ⟨2673384, by rfl⟩ : syracuseStep 7129025 = 5346769) B5346769
theorem B4752683 : Blo 2083435 4752683 := bstep (se 1 (by rfl) ⟨3564512, by rfl⟩ : syracuseStep 4752683 = 7129025) B7129025
theorem B3168455 : Blo 2083435 3168455 := bstep (se 1 (by rfl) ⟨2376341, by rfl⟩ : syracuseStep 3168455 = 4752683) B4752683
theorem B8449213 : Blo 2083435 8449213 := bstep (se 3 (by rfl) ⟨1584227, by rfl⟩ : syracuseStep 8449213 = 3168455) B3168455
theorem B11265617 : Blo 2083435 11265617 := bstep (se 2 (by rfl) ⟨4224606, by rfl⟩ : syracuseStep 11265617 = 8449213) B8449213
theorem B7510411 : Blo 2083435 7510411 := bstep (se 1 (by rfl) ⟨5632808, by rfl⟩ : syracuseStep 7510411 = 11265617) B11265617
theorem B10013881 : Blo 2083435 10013881 := bstep (se 2 (by rfl) ⟨3755205, by rfl⟩ : syracuseStep 10013881 = 7510411) B7510411
theorem B13351841 : Blo 2083435 13351841 := bstep (se 2 (by rfl) ⟨5006940, by rfl⟩ : syracuseStep 13351841 = 10013881) B10013881
theorem B8901227 : Blo 2083435 8901227 := bstep (se 1 (by rfl) ⟨6675920, by rfl⟩ : syracuseStep 8901227 = 13351841) B13351841
theorem B5934151 : Blo 2083435 5934151 := bstep (se 1 (by rfl) ⟨4450613, by rfl⟩ : syracuseStep 5934151 = 8901227) B8901227
theorem B7912201 : Blo 2083435 7912201 := bstep (se 2 (by rfl) ⟨2967075, by rfl⟩ : syracuseStep 7912201 = 5934151) B5934151
theorem B10549601 : Blo 2083435 10549601 := bstep (se 2 (by rfl) ⟨3956100, by rfl⟩ : syracuseStep 10549601 = 7912201) B7912201
theorem B7033067 : Blo 2083435 7033067 := bstep (se 1 (by rfl) ⟨5274800, by rfl⟩ : syracuseStep 7033067 = 10549601) B10549601
theorem B4688711 : Blo 2083435 4688711 := bstep (se 1 (by rfl) ⟨3516533, by rfl⟩ : syracuseStep 4688711 = 7033067) B7033067
theorem B3125807 : Blo 2083435 3125807 := bstep (se 1 (by rfl) ⟨2344355, by rfl⟩ : syracuseStep 3125807 = 4688711) B4688711
theorem B2083871 : Blo 2083435 2083871 := bstep (se 1 (by rfl) ⟨1562903, by rfl⟩ : syracuseStep 2083871 = 3125807) B3125807
theorem B3125813 : Blo 2083435 3125813 := bbase (se 5 (by rfl) ⟨146522, by rfl⟩ : syracuseStep 3125813 = 293045) (by norm_num)
theorem B2083875 : Blo 2083435 2083875 := bstep (se 1 (by rfl) ⟨1562906, by rfl⟩ : syracuseStep 2083875 = 3125813) B3125813
theorem B5274821 : Blo 2083435 5274821 := bbase (se 4 (by rfl) ⟨494514, by rfl⟩ : syracuseStep 5274821 = 989029) (by norm_num)
theorem B3516547 : Blo 2083435 3516547 := bstep (se 1 (by rfl) ⟨2637410, by rfl⟩ : syracuseStep 3516547 = 5274821) B5274821
theorem B4688729 : Blo 2083435 4688729 := bstep (se 2 (by rfl) ⟨1758273, by rfl⟩ : syracuseStep 4688729 = 3516547) B3516547
theorem B3125819 : Blo 2083435 3125819 := bstep (se 1 (by rfl) ⟨2344364, by rfl⟩ : syracuseStep 3125819 = 4688729) B4688729
theorem B2083879 : Blo 2083435 2083879 := bstep (se 1 (by rfl) ⟨1562909, by rfl⟩ : syracuseStep 2083879 = 3125819) B3125819
theorem B2344369 : Blo 2083435 2344369 := bbase (se 2 (by rfl) ⟨879138, by rfl⟩ : syracuseStep 2344369 = 1758277) (by norm_num)
theorem B3125825 : Blo 2083435 3125825 := bstep (se 2 (by rfl) ⟨1172184, by rfl⟩ : syracuseStep 3125825 = 2344369) B2344369
theorem B2083883 : Blo 2083435 2083883 := bstep (se 1 (by rfl) ⟨1562912, by rfl⟩ : syracuseStep 2083883 = 3125825) B3125825
theorem B5934197 : Blo 2083435 5934197 := bbase (se 5 (by rfl) ⟨278165, by rfl⟩ : syracuseStep 5934197 = 556331) (by norm_num)
theorem B3956131 : Blo 2083435 3956131 := bstep (se 1 (by rfl) ⟨2967098, by rfl⟩ : syracuseStep 3956131 = 5934197) B5934197
theorem B5274841 : Blo 2083435 5274841 := bstep (se 2 (by rfl) ⟨1978065, by rfl⟩ : syracuseStep 5274841 = 3956131) B3956131
theorem B7033121 : Blo 2083435 7033121 := bstep (se 2 (by rfl) ⟨2637420, by rfl⟩ : syracuseStep 7033121 = 5274841) B5274841
theorem B4688747 : Blo 2083435 4688747 := bstep (se 1 (by rfl) ⟨3516560, by rfl⟩ : syracuseStep 4688747 = 7033121) B7033121
theorem B3125831 : Blo 2083435 3125831 := bstep (se 1 (by rfl) ⟨2344373, by rfl⟩ : syracuseStep 3125831 = 4688747) B4688747
theorem B2083887 : Blo 2083435 2083887 := bstep (se 1 (by rfl) ⟨1562915, by rfl⟩ : syracuseStep 2083887 = 3125831) B3125831
theorem B3125837 : Blo 2083435 3125837 := bbase (se 3 (by rfl) ⟨586094, by rfl⟩ : syracuseStep 3125837 = 1172189) (by norm_num)
theorem B2083891 : Blo 2083435 2083891 := bstep (se 1 (by rfl) ⟨1562918, by rfl⟩ : syracuseStep 2083891 = 3125837) B3125837
theorem B4688765 : Blo 2083435 4688765 := bbase (se 3 (by rfl) ⟨879143, by rfl⟩ : syracuseStep 4688765 = 1758287) (by norm_num)
theorem B3125843 : Blo 2083435 3125843 := bstep (se 1 (by rfl) ⟨2344382, by rfl⟩ : syracuseStep 3125843 = 4688765) B4688765
theorem B2083895 : Blo 2083435 2083895 := bstep (se 1 (by rfl) ⟨1562921, by rfl⟩ : syracuseStep 2083895 = 3125843) B3125843
theorem B3516581 : Blo 2083435 3516581 := bbase (se 4 (by rfl) ⟨329679, by rfl⟩ : syracuseStep 3516581 = 659359) (by norm_num)
theorem B2344387 : Blo 2083435 2344387 := bstep (se 1 (by rfl) ⟨1758290, by rfl⟩ : syracuseStep 2344387 = 3516581) B3516581
theorem B3125849 : Blo 2083435 3125849 := bstep (se 2 (by rfl) ⟨1172193, by rfl⟩ : syracuseStep 3125849 = 2344387) B2344387
theorem B2083899 : Blo 2083435 2083899 := bstep (se 1 (by rfl) ⟨1562924, by rfl⟩ : syracuseStep 2083899 = 3125849) B3125849
theorem B2225341 : Blo 2083435 2225341 := bbase (se 3 (by rfl) ⟨417251, by rfl⟩ : syracuseStep 2225341 = 834503) (by norm_num)
theorem B2967121 : Blo 2083435 2967121 := bstep (se 2 (by rfl) ⟨1112670, by rfl⟩ : syracuseStep 2967121 = 2225341) B2225341
theorem B15824645 : Blo 2083435 15824645 := bstep (se 4 (by rfl) ⟨1483560, by rfl⟩ : syracuseStep 15824645 = 2967121) B2967121
theorem B10549763 : Blo 2083435 10549763 := bstep (se 1 (by rfl) ⟨7912322, by rfl⟩ : syracuseStep 10549763 = 15824645) B15824645
theorem B7033175 : Blo 2083435 7033175 := bstep (se 1 (by rfl) ⟨5274881, by rfl⟩ : syracuseStep 7033175 = 10549763) B10549763
theorem B4688783 : Blo 2083435 4688783 := bstep (se 1 (by rfl) ⟨3516587, by rfl⟩ : syracuseStep 4688783 = 7033175) B7033175
theorem B3125855 : Blo 2083435 3125855 := bstep (se 1 (by rfl) ⟨2344391, by rfl⟩ : syracuseStep 3125855 = 4688783) B4688783
theorem B2083903 : Blo 2083435 2083903 := bstep (se 1 (by rfl) ⟨1562927, by rfl⟩ : syracuseStep 2083903 = 3125855) B3125855
theorem B3125861 : Blo 2083435 3125861 := bbase (se 4 (by rfl) ⟨293049, by rfl⟩ : syracuseStep 3125861 = 586099) (by norm_num)
theorem B2083907 : Blo 2083435 2083907 := bstep (se 1 (by rfl) ⟨1562930, by rfl⟩ : syracuseStep 2083907 = 3125861) B3125861
theorem B2967133 : Blo 2083435 2967133 := bbase (se 3 (by rfl) ⟨556337, by rfl⟩ : syracuseStep 2967133 = 1112675) (by norm_num)
theorem B3956177 : Blo 2083435 3956177 := bstep (se 2 (by rfl) ⟨1483566, by rfl⟩ : syracuseStep 3956177 = 2967133) B2967133
theorem B2637451 : Blo 2083435 2637451 := bstep (se 1 (by rfl) ⟨1978088, by rfl⟩ : syracuseStep 2637451 = 3956177) B3956177
theorem B3516601 : Blo 2083435 3516601 := bstep (se 2 (by rfl) ⟨1318725, by rfl⟩ : syracuseStep 3516601 = 2637451) B2637451
theorem B4688801 : Blo 2083435 4688801 := bstep (se 2 (by rfl) ⟨1758300, by rfl⟩ : syracuseStep 4688801 = 3516601) B3516601
theorem B3125867 : Blo 2083435 3125867 := bstep (se 1 (by rfl) ⟨2344400, by rfl⟩ : syracuseStep 3125867 = 4688801) B4688801
theorem B2083911 : Blo 2083435 2083911 := bstep (se 1 (by rfl) ⟨1562933, by rfl⟩ : syracuseStep 2083911 = 3125867) B3125867
theorem B2344405 : Blo 2083435 2344405 := bbase (se 7 (by rfl) ⟨27473, by rfl⟩ : syracuseStep 2344405 = 54947) (by norm_num)
theorem B3125873 : Blo 2083435 3125873 := bstep (se 2 (by rfl) ⟨1172202, by rfl⟩ : syracuseStep 3125873 = 2344405) B2344405
theorem B2083915 : Blo 2083435 2083915 := bstep (se 1 (by rfl) ⟨1562936, by rfl⟩ : syracuseStep 2083915 = 3125873) B3125873
theorem B2637461 : Blo 2083435 2637461 := bbase (se 6 (by rfl) ⟨61815, by rfl⟩ : syracuseStep 2637461 = 123631) (by norm_num)
theorem B7033229 : Blo 2083435 7033229 := bstep (se 3 (by rfl) ⟨1318730, by rfl⟩ : syracuseStep 7033229 = 2637461) B2637461
theorem B4688819 : Blo 2083435 4688819 := bstep (se 1 (by rfl) ⟨3516614, by rfl⟩ : syracuseStep 4688819 = 7033229) B7033229
theorem B3125879 : Blo 2083435 3125879 := bstep (se 1 (by rfl) ⟨2344409, by rfl⟩ : syracuseStep 3125879 = 4688819) B4688819
theorem B2083919 : Blo 2083435 2083919 := bstep (se 1 (by rfl) ⟨1562939, by rfl⟩ : syracuseStep 2083919 = 3125879) B3125879
theorem B3125885 : Blo 2083435 3125885 := bbase (se 3 (by rfl) ⟨586103, by rfl⟩ : syracuseStep 3125885 = 1172207) (by norm_num)
theorem B2083923 : Blo 2083435 2083923 := bstep (se 1 (by rfl) ⟨1562942, by rfl⟩ : syracuseStep 2083923 = 3125885) B3125885
theorem B4688837 : Blo 2083435 4688837 := bbase (se 4 (by rfl) ⟨439578, by rfl⟩ : syracuseStep 4688837 = 879157) (by norm_num)
theorem B3125891 : Blo 2083435 3125891 := bstep (se 1 (by rfl) ⟨2344418, by rfl⟩ : syracuseStep 3125891 = 4688837) B4688837
theorem B2083927 : Blo 2083435 2083927 := bstep (se 1 (by rfl) ⟨1562945, by rfl⟩ : syracuseStep 2083927 = 3125891) B3125891
theorem B2112365 : Blo 2083435 2112365 := bbase (se 3 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 2112365 = 792137) (by norm_num)
theorem B5632973 : Blo 2083435 5632973 := bstep (se 3 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 5632973 = 2112365) B2112365
theorem B3755315 : Blo 2083435 3755315 := bstep (se 1 (by rfl) ⟨2816486, by rfl⟩ : syracuseStep 3755315 = 5632973) B5632973
theorem B2503543 : Blo 2083435 2503543 := bstep (se 1 (by rfl) ⟨1877657, by rfl⟩ : syracuseStep 2503543 = 3755315) B3755315
theorem B3338057 : Blo 2083435 3338057 := bstep (se 2 (by rfl) ⟨1251771, by rfl⟩ : syracuseStep 3338057 = 2503543) B2503543
theorem B8901485 : Blo 2083435 8901485 := bstep (se 3 (by rfl) ⟨1669028, by rfl⟩ : syracuseStep 8901485 = 3338057) B3338057
theorem B5934323 : Blo 2083435 5934323 := bstep (se 1 (by rfl) ⟨4450742, by rfl⟩ : syracuseStep 5934323 = 8901485) B8901485
theorem B3956215 : Blo 2083435 3956215 := bstep (se 1 (by rfl) ⟨2967161, by rfl⟩ : syracuseStep 3956215 = 5934323) B5934323
theorem B5274953 : Blo 2083435 5274953 := bstep (se 2 (by rfl) ⟨1978107, by rfl⟩ : syracuseStep 5274953 = 3956215) B3956215
theorem B3516635 : Blo 2083435 3516635 := bstep (se 1 (by rfl) ⟨2637476, by rfl⟩ : syracuseStep 3516635 = 5274953) B5274953
theorem B2344423 : Blo 2083435 2344423 := bstep (se 1 (by rfl) ⟨1758317, by rfl⟩ : syracuseStep 2344423 = 3516635) B3516635
theorem B3125897 : Blo 2083435 3125897 := bstep (se 2 (by rfl) ⟨1172211, by rfl⟩ : syracuseStep 3125897 = 2344423) B2344423
theorem B2083931 : Blo 2083435 2083931 := bstep (se 1 (by rfl) ⟨1562948, by rfl⟩ : syracuseStep 2083931 = 3125897) B3125897
theorem B10549925 : Blo 2083435 10549925 := bbase (se 4 (by rfl) ⟨989055, by rfl⟩ : syracuseStep 10549925 = 1978111) (by norm_num)
theorem B7033283 : Blo 2083435 7033283 := bstep (se 1 (by rfl) ⟨5274962, by rfl⟩ : syracuseStep 7033283 = 10549925) B10549925
theorem B4688855 : Blo 2083435 4688855 := bstep (se 1 (by rfl) ⟨3516641, by rfl⟩ : syracuseStep 4688855 = 7033283) B7033283
theorem B3125903 : Blo 2083435 3125903 := bstep (se 1 (by rfl) ⟨2344427, by rfl⟩ : syracuseStep 3125903 = 4688855) B4688855
theorem B2083935 : Blo 2083435 2083935 := bstep (se 1 (by rfl) ⟨1562951, by rfl⟩ : syracuseStep 2083935 = 3125903) B3125903
theorem B3125909 : Blo 2083435 3125909 := bbase (se 6 (by rfl) ⟨73263, by rfl⟩ : syracuseStep 3125909 = 146527) (by norm_num)
theorem B2083939 : Blo 2083435 2083939 := bstep (se 1 (by rfl) ⟨1562954, by rfl⟩ : syracuseStep 2083939 = 3125909) B3125909
theorem B2141197 : Blo 2083435 2141197 := bbase (se 3 (by rfl) ⟨401474, by rfl⟩ : syracuseStep 2141197 = 802949) (by norm_num)
theorem B11419717 : Blo 2083435 11419717 := bstep (se 4 (by rfl) ⟨1070598, by rfl⟩ : syracuseStep 11419717 = 2141197) B2141197
theorem B15226289 : Blo 2083435 15226289 := bstep (se 2 (by rfl) ⟨5709858, by rfl⟩ : syracuseStep 15226289 = 11419717) B11419717
theorem B10150859 : Blo 2083435 10150859 := bstep (se 1 (by rfl) ⟨7613144, by rfl⟩ : syracuseStep 10150859 = 15226289) B15226289
theorem B6767239 : Blo 2083435 6767239 := bstep (se 1 (by rfl) ⟨5075429, by rfl⟩ : syracuseStep 6767239 = 10150859) B10150859
theorem B9022985 : Blo 2083435 9022985 := bstep (se 2 (by rfl) ⟨3383619, by rfl⟩ : syracuseStep 9022985 = 6767239) B6767239
theorem B6015323 : Blo 2083435 6015323 := bstep (se 1 (by rfl) ⟨4511492, by rfl⟩ : syracuseStep 6015323 = 9022985) B9022985
theorem B4010215 : Blo 2083435 4010215 := bstep (se 1 (by rfl) ⟨3007661, by rfl⟩ : syracuseStep 4010215 = 6015323) B6015323
theorem B5346953 : Blo 2083435 5346953 := bstep (se 2 (by rfl) ⟨2005107, by rfl⟩ : syracuseStep 5346953 = 4010215) B4010215
theorem B3564635 : Blo 2083435 3564635 := bstep (se 1 (by rfl) ⟨2673476, by rfl⟩ : syracuseStep 3564635 = 5346953) B5346953
theorem B9505693 : Blo 2083435 9505693 := bstep (se 3 (by rfl) ⟨1782317, by rfl⟩ : syracuseStep 9505693 = 3564635) B3564635
theorem B50697029 : Blo 2083435 50697029 := bstep (se 4 (by rfl) ⟨4752846, by rfl⟩ : syracuseStep 50697029 = 9505693) B9505693
theorem B33798019 : Blo 2083435 33798019 := bstep (se 1 (by rfl) ⟨25348514, by rfl⟩ : syracuseStep 33798019 = 50697029) B50697029
theorem B45064025 : Blo 2083435 45064025 := bstep (se 2 (by rfl) ⟨16899009, by rfl⟩ : syracuseStep 45064025 = 33798019) B33798019
theorem B30042683 : Blo 2083435 30042683 := bstep (se 1 (by rfl) ⟨22532012, by rfl⟩ : syracuseStep 30042683 = 45064025) B45064025
theorem B20028455 : Blo 2083435 20028455 := bstep (se 1 (by rfl) ⟨15021341, by rfl⟩ : syracuseStep 20028455 = 30042683) B30042683
theorem B13352303 : Blo 2083435 13352303 := bstep (se 1 (by rfl) ⟨10014227, by rfl⟩ : syracuseStep 13352303 = 20028455) B20028455
theorem B8901535 : Blo 2083435 8901535 := bstep (se 1 (by rfl) ⟨6676151, by rfl⟩ : syracuseStep 8901535 = 13352303) B13352303
theorem B11868713 : Blo 2083435 11868713 := bstep (se 2 (by rfl) ⟨4450767, by rfl⟩ : syracuseStep 11868713 = 8901535) B8901535
theorem B7912475 : Blo 2083435 7912475 := bstep (se 1 (by rfl) ⟨5934356, by rfl⟩ : syracuseStep 7912475 = 11868713) B11868713
theorem B5274983 : Blo 2083435 5274983 := bstep (se 1 (by rfl) ⟨3956237, by rfl⟩ : syracuseStep 5274983 = 7912475) B7912475
theorem B3516655 : Blo 2083435 3516655 := bstep (se 1 (by rfl) ⟨2637491, by rfl⟩ : syracuseStep 3516655 = 5274983) B5274983
theorem B4688873 : Blo 2083435 4688873 := bstep (se 2 (by rfl) ⟨1758327, by rfl⟩ : syracuseStep 4688873 = 3516655) B3516655
theorem B3125915 : Blo 2083435 3125915 := bstep (se 1 (by rfl) ⟨2344436, by rfl⟩ : syracuseStep 3125915 = 4688873) B4688873
theorem B2083943 : Blo 2083435 2083943 := bstep (se 1 (by rfl) ⟨1562957, by rfl⟩ : syracuseStep 2083943 = 3125915) B3125915
theorem B2344441 : Blo 2083435 2344441 := bbase (se 2 (by rfl) ⟨879165, by rfl⟩ : syracuseStep 2344441 = 1758331) (by norm_num)
theorem B3125921 : Blo 2083435 3125921 := bstep (se 2 (by rfl) ⟨1172220, by rfl⟩ : syracuseStep 3125921 = 2344441) B2344441
theorem B2083947 : Blo 2083435 2083947 := bstep (se 1 (by rfl) ⟨1562960, by rfl⟩ : syracuseStep 2083947 = 3125921) B3125921
theorem B5007133 : Blo 2083435 5007133 := bbase (se 3 (by rfl) ⟨938837, by rfl⟩ : syracuseStep 5007133 = 1877675) (by norm_num)
theorem B6676177 : Blo 2083435 6676177 := bstep (se 2 (by rfl) ⟨2503566, by rfl⟩ : syracuseStep 6676177 = 5007133) B5007133
theorem B8901569 : Blo 2083435 8901569 := bstep (se 2 (by rfl) ⟨3338088, by rfl⟩ : syracuseStep 8901569 = 6676177) B6676177
theorem B5934379 : Blo 2083435 5934379 := bstep (se 1 (by rfl) ⟨4450784, by rfl⟩ : syracuseStep 5934379 = 8901569) B8901569
theorem B7912505 : Blo 2083435 7912505 := bstep (se 2 (by rfl) ⟨2967189, by rfl⟩ : syracuseStep 7912505 = 5934379) B5934379
theorem B5275003 : Blo 2083435 5275003 := bstep (se 1 (by rfl) ⟨3956252, by rfl⟩ : syracuseStep 5275003 = 7912505) B7912505
theorem B7033337 : Blo 2083435 7033337 := bstep (se 2 (by rfl) ⟨2637501, by rfl⟩ : syracuseStep 7033337 = 5275003) B5275003
theorem B4688891 : Blo 2083435 4688891 := bstep (se 1 (by rfl) ⟨3516668, by rfl⟩ : syracuseStep 4688891 = 7033337) B7033337
theorem B3125927 : Blo 2083435 3125927 := bstep (se 1 (by rfl) ⟨2344445, by rfl⟩ : syracuseStep 3125927 = 4688891) B4688891
theorem B2083951 : Blo 2083435 2083951 := bstep (se 1 (by rfl) ⟨1562963, by rfl⟩ : syracuseStep 2083951 = 3125927) B3125927
theorem B3125933 : Blo 2083435 3125933 := bbase (se 3 (by rfl) ⟨586112, by rfl⟩ : syracuseStep 3125933 = 1172225) (by norm_num)
theorem B2083955 : Blo 2083435 2083955 := bstep (se 1 (by rfl) ⟨1562966, by rfl⟩ : syracuseStep 2083955 = 3125933) B3125933
theorem B4688909 : Blo 2083435 4688909 := bbase (se 3 (by rfl) ⟨879170, by rfl⟩ : syracuseStep 4688909 = 1758341) (by norm_num)
theorem B3125939 : Blo 2083435 3125939 := bstep (se 1 (by rfl) ⟨2344454, by rfl⟩ : syracuseStep 3125939 = 4688909) B4688909
theorem B2083959 : Blo 2083435 2083959 := bstep (se 1 (by rfl) ⟨1562969, by rfl⟩ : syracuseStep 2083959 = 3125939) B3125939
theorem B2637517 : Blo 2083435 2637517 := bbase (se 3 (by rfl) ⟨494534, by rfl⟩ : syracuseStep 2637517 = 989069) (by norm_num)
theorem B3516689 : Blo 2083435 3516689 := bstep (se 2 (by rfl) ⟨1318758, by rfl⟩ : syracuseStep 3516689 = 2637517) B2637517
theorem B2344459 : Blo 2083435 2344459 := bstep (se 1 (by rfl) ⟨1758344, by rfl⟩ : syracuseStep 2344459 = 3516689) B3516689
theorem B3125945 : Blo 2083435 3125945 := bstep (se 2 (by rfl) ⟨1172229, by rfl⟩ : syracuseStep 3125945 = 2344459) B2344459
theorem B2083963 : Blo 2083435 2083963 := bstep (se 1 (by rfl) ⟨1562972, by rfl⟩ : syracuseStep 2083963 = 3125945) B3125945
theorem B4752901 : Blo 2083435 4752901 := bbase (se 4 (by rfl) ⟨445584, by rfl⟩ : syracuseStep 4752901 = 891169) (by norm_num)
theorem B6337201 : Blo 2083435 6337201 := bstep (se 2 (by rfl) ⟨2376450, by rfl⟩ : syracuseStep 6337201 = 4752901) B4752901
theorem B8449601 : Blo 2083435 8449601 := bstep (se 2 (by rfl) ⟨3168600, by rfl⟩ : syracuseStep 8449601 = 6337201) B6337201
theorem B22532269 : Blo 2083435 22532269 := bstep (se 3 (by rfl) ⟨4224800, by rfl⟩ : syracuseStep 22532269 = 8449601) B8449601
theorem B30043025 : Blo 2083435 30043025 := bstep (se 2 (by rfl) ⟨11266134, by rfl⟩ : syracuseStep 30043025 = 22532269) B22532269
theorem B20028683 : Blo 2083435 20028683 := bstep (se 1 (by rfl) ⟨15021512, by rfl⟩ : syracuseStep 20028683 = 30043025) B30043025
theorem B13352455 : Blo 2083435 13352455 := bstep (se 1 (by rfl) ⟨10014341, by rfl⟩ : syracuseStep 13352455 = 20028683) B20028683
theorem B17803273 : Blo 2083435 17803273 := bstep (se 2 (by rfl) ⟨6676227, by rfl⟩ : syracuseStep 17803273 = 13352455) B13352455
theorem B23737697 : Blo 2083435 23737697 := bstep (se 2 (by rfl) ⟨8901636, by rfl⟩ : syracuseStep 23737697 = 17803273) B17803273
theorem B15825131 : Blo 2083435 15825131 := bstep (se 1 (by rfl) ⟨11868848, by rfl⟩ : syracuseStep 15825131 = 23737697) B23737697
theorem B10550087 : Blo 2083435 10550087 := bstep (se 1 (by rfl) ⟨7912565, by rfl⟩ : syracuseStep 10550087 = 15825131) B15825131
theorem B7033391 : Blo 2083435 7033391 := bstep (se 1 (by rfl) ⟨5275043, by rfl⟩ : syracuseStep 7033391 = 10550087) B10550087
theorem B4688927 : Blo 2083435 4688927 := bstep (se 1 (by rfl) ⟨3516695, by rfl⟩ : syracuseStep 4688927 = 7033391) B7033391
theorem B3125951 : Blo 2083435 3125951 := bstep (se 1 (by rfl) ⟨2344463, by rfl⟩ : syracuseStep 3125951 = 4688927) B4688927
theorem B2083967 : Blo 2083435 2083967 := bstep (se 1 (by rfl) ⟨1562975, by rfl⟩ : syracuseStep 2083967 = 3125951) B3125951
theorem B3125957 : Blo 2083435 3125957 := bbase (se 4 (by rfl) ⟨293058, by rfl⟩ : syracuseStep 3125957 = 586117) (by norm_num)
theorem B2083971 : Blo 2083435 2083971 := bstep (se 1 (by rfl) ⟨1562978, by rfl⟩ : syracuseStep 2083971 = 3125957) B3125957
theorem B3516709 : Blo 2083435 3516709 := bbase (se 4 (by rfl) ⟨329691, by rfl⟩ : syracuseStep 3516709 = 659383) (by norm_num)
theorem B4688945 : Blo 2083435 4688945 := bstep (se 2 (by rfl) ⟨1758354, by rfl⟩ : syracuseStep 4688945 = 3516709) B3516709
theorem B3125963 : Blo 2083435 3125963 := bstep (se 1 (by rfl) ⟨2344472, by rfl⟩ : syracuseStep 3125963 = 4688945) B4688945
theorem B2083975 : Blo 2083435 2083975 := bstep (se 1 (by rfl) ⟨1562981, by rfl⟩ : syracuseStep 2083975 = 3125963) B3125963
theorem B2344477 : Blo 2083435 2344477 := bbase (se 3 (by rfl) ⟨439589, by rfl⟩ : syracuseStep 2344477 = 879179) (by norm_num)
theorem B3125969 : Blo 2083435 3125969 := bstep (se 2 (by rfl) ⟨1172238, by rfl⟩ : syracuseStep 3125969 = 2344477) B2344477
theorem B2083979 : Blo 2083435 2083979 := bstep (se 1 (by rfl) ⟨1562984, by rfl⟩ : syracuseStep 2083979 = 3125969) B3125969
theorem B7033445 : Blo 2083435 7033445 := bbase (se 4 (by rfl) ⟨659385, by rfl⟩ : syracuseStep 7033445 = 1318771) (by norm_num)
theorem B4688963 : Blo 2083435 4688963 := bstep (se 1 (by rfl) ⟨3516722, by rfl⟩ : syracuseStep 4688963 = 7033445) B7033445
theorem B3125975 : Blo 2083435 3125975 := bstep (se 1 (by rfl) ⟨2344481, by rfl⟩ : syracuseStep 3125975 = 4688963) B4688963
theorem B2083983 : Blo 2083435 2083983 := bstep (se 1 (by rfl) ⟨1562987, by rfl⟩ : syracuseStep 2083983 = 3125975) B3125975
theorem B3125981 : Blo 2083435 3125981 := bbase (se 3 (by rfl) ⟨586121, by rfl⟩ : syracuseStep 3125981 = 1172243) (by norm_num)
theorem B2083987 : Blo 2083435 2083987 := bstep (se 1 (by rfl) ⟨1562990, by rfl⟩ : syracuseStep 2083987 = 3125981) B3125981
theorem B4688981 : Blo 2083435 4688981 := bbase (se 8 (by rfl) ⟨27474, by rfl⟩ : syracuseStep 4688981 = 54949) (by norm_num)
theorem B3125987 : Blo 2083435 3125987 := bstep (se 1 (by rfl) ⟨2344490, by rfl⟩ : syracuseStep 3125987 = 4688981) B4688981
theorem B2083991 : Blo 2083435 2083991 := bstep (se 1 (by rfl) ⟨1562993, by rfl⟩ : syracuseStep 2083991 = 3125987) B3125987
theorem B33798869 : Blo 2083435 33798869 := bbase (se 7 (by rfl) ⟨396080, by rfl⟩ : syracuseStep 33798869 = 792161) (by norm_num)
theorem B22532579 : Blo 2083435 22532579 := bstep (se 1 (by rfl) ⟨16899434, by rfl⟩ : syracuseStep 22532579 = 33798869) B33798869
theorem B15021719 : Blo 2083435 15021719 := bstep (se 1 (by rfl) ⟨11266289, by rfl⟩ : syracuseStep 15021719 = 22532579) B22532579
theorem B10014479 : Blo 2083435 10014479 := bstep (se 1 (by rfl) ⟨7510859, by rfl⟩ : syracuseStep 10014479 = 15021719) B15021719
theorem B6676319 : Blo 2083435 6676319 := bstep (se 1 (by rfl) ⟨5007239, by rfl⟩ : syracuseStep 6676319 = 10014479) B10014479
theorem B4450879 : Blo 2083435 4450879 := bstep (se 1 (by rfl) ⟨3338159, by rfl⟩ : syracuseStep 4450879 = 6676319) B6676319
theorem B5934505 : Blo 2083435 5934505 := bstep (se 2 (by rfl) ⟨2225439, by rfl⟩ : syracuseStep 5934505 = 4450879) B4450879
theorem B7912673 : Blo 2083435 7912673 := bstep (se 2 (by rfl) ⟨2967252, by rfl⟩ : syracuseStep 7912673 = 5934505) B5934505
theorem B5275115 : Blo 2083435 5275115 := bstep (se 1 (by rfl) ⟨3956336, by rfl⟩ : syracuseStep 5275115 = 7912673) B7912673
theorem B3516743 : Blo 2083435 3516743 := bstep (se 1 (by rfl) ⟨2637557, by rfl⟩ : syracuseStep 3516743 = 5275115) B5275115
theorem B2344495 : Blo 2083435 2344495 := bstep (se 1 (by rfl) ⟨1758371, by rfl⟩ : syracuseStep 2344495 = 3516743) B3516743
theorem B3125993 : Blo 2083435 3125993 := bstep (se 2 (by rfl) ⟨1172247, by rfl⟩ : syracuseStep 3125993 = 2344495) B2344495
theorem B2083995 : Blo 2083435 2083995 := bstep (se 1 (by rfl) ⟨1562996, by rfl⟩ : syracuseStep 2083995 = 3125993) B3125993
theorem B5144813 : Blo 2083435 5144813 := bbase (se 3 (by rfl) ⟨964652, by rfl⟩ : syracuseStep 5144813 = 1929305) (by norm_num)
theorem B3429875 : Blo 2083435 3429875 := bstep (se 1 (by rfl) ⟨2572406, by rfl⟩ : syracuseStep 3429875 = 5144813) B5144813
theorem B9146333 : Blo 2083435 9146333 := bstep (se 3 (by rfl) ⟨1714937, by rfl⟩ : syracuseStep 9146333 = 3429875) B3429875
theorem B6097555 : Blo 2083435 6097555 := bstep (se 1 (by rfl) ⟨4573166, by rfl⟩ : syracuseStep 6097555 = 9146333) B9146333
theorem B8130073 : Blo 2083435 8130073 := bstep (se 2 (by rfl) ⟨3048777, by rfl⟩ : syracuseStep 8130073 = 6097555) B6097555
theorem B10840097 : Blo 2083435 10840097 := bstep (se 2 (by rfl) ⟨4065036, by rfl⟩ : syracuseStep 10840097 = 8130073) B8130073
theorem B7226731 : Blo 2083435 7226731 := bstep (se 1 (by rfl) ⟨5420048, by rfl⟩ : syracuseStep 7226731 = 10840097) B10840097
theorem B9635641 : Blo 2083435 9635641 := bstep (se 2 (by rfl) ⟨3613365, by rfl⟩ : syracuseStep 9635641 = 7226731) B7226731
theorem B51390085 : Blo 2083435 51390085 := bstep (se 4 (by rfl) ⟨4817820, by rfl⟩ : syracuseStep 51390085 = 9635641) B9635641
theorem B68520113 : Blo 2083435 68520113 := bstep (se 2 (by rfl) ⟨25695042, by rfl⟩ : syracuseStep 68520113 = 51390085) B51390085
theorem B45680075 : Blo 2083435 45680075 := bstep (se 1 (by rfl) ⟨34260056, by rfl⟩ : syracuseStep 45680075 = 68520113) B68520113
theorem B30453383 : Blo 2083435 30453383 := bstep (se 1 (by rfl) ⟨22840037, by rfl⟩ : syracuseStep 30453383 = 45680075) B45680075
theorem B20302255 : Blo 2083435 20302255 := bstep (se 1 (by rfl) ⟨15226691, by rfl⟩ : syracuseStep 20302255 = 30453383) B30453383
theorem B27069673 : Blo 2083435 27069673 := bstep (se 2 (by rfl) ⟨10151127, by rfl⟩ : syracuseStep 27069673 = 20302255) B20302255
theorem B36092897 : Blo 2083435 36092897 := bstep (se 2 (by rfl) ⟨13534836, by rfl⟩ : syracuseStep 36092897 = 27069673) B27069673
theorem B24061931 : Blo 2083435 24061931 := bstep (se 1 (by rfl) ⟨18046448, by rfl⟩ : syracuseStep 24061931 = 36092897) B36092897
theorem B16041287 : Blo 2083435 16041287 := bstep (se 1 (by rfl) ⟨12030965, by rfl⟩ : syracuseStep 16041287 = 24061931) B24061931
theorem B10694191 : Blo 2083435 10694191 := bstep (se 1 (by rfl) ⟨8020643, by rfl⟩ : syracuseStep 10694191 = 16041287) B16041287
theorem B14258921 : Blo 2083435 14258921 := bstep (se 2 (by rfl) ⟨5347095, by rfl⟩ : syracuseStep 14258921 = 10694191) B10694191
theorem B152095157 : Blo 2083435 152095157 := bstep (se 5 (by rfl) ⟨7129460, by rfl⟩ : syracuseStep 152095157 = 14258921) B14258921
theorem B101396771 : Blo 2083435 101396771 := bstep (se 1 (by rfl) ⟨76047578, by rfl⟩ : syracuseStep 101396771 = 152095157) B152095157
theorem B67597847 : Blo 2083435 67597847 := bstep (se 1 (by rfl) ⟨50698385, by rfl⟩ : syracuseStep 67597847 = 101396771) B101396771
theorem B45065231 : Blo 2083435 45065231 := bstep (se 1 (by rfl) ⟨33798923, by rfl⟩ : syracuseStep 45065231 = 67597847) B67597847
theorem B30043487 : Blo 2083435 30043487 := bstep (se 1 (by rfl) ⟨22532615, by rfl⟩ : syracuseStep 30043487 = 45065231) B45065231
theorem B20028991 : Blo 2083435 20028991 := bstep (se 1 (by rfl) ⟨15021743, by rfl⟩ : syracuseStep 20028991 = 30043487) B30043487
theorem B26705321 : Blo 2083435 26705321 := bstep (se 2 (by rfl) ⟨10014495, by rfl⟩ : syracuseStep 26705321 = 20028991) B20028991
theorem B17803547 : Blo 2083435 17803547 := bstep (se 1 (by rfl) ⟨13352660, by rfl⟩ : syracuseStep 17803547 = 26705321) B26705321
theorem B11869031 : Blo 2083435 11869031 := bstep (se 1 (by rfl) ⟨8901773, by rfl⟩ : syracuseStep 11869031 = 17803547) B17803547
theorem B7912687 : Blo 2083435 7912687 := bstep (se 1 (by rfl) ⟨5934515, by rfl⟩ : syracuseStep 7912687 = 11869031) B11869031
theorem B10550249 : Blo 2083435 10550249 := bstep (se 2 (by rfl) ⟨3956343, by rfl⟩ : syracuseStep 10550249 = 7912687) B7912687
theorem B7033499 : Blo 2083435 7033499 := bstep (se 1 (by rfl) ⟨5275124, by rfl⟩ : syracuseStep 7033499 = 10550249) B10550249
theorem B4688999 : Blo 2083435 4688999 := bstep (se 1 (by rfl) ⟨3516749, by rfl⟩ : syracuseStep 4688999 = 7033499) B7033499
theorem B3125999 : Blo 2083435 3125999 := bstep (se 1 (by rfl) ⟨2344499, by rfl⟩ : syracuseStep 3125999 = 4688999) B4688999
theorem B2083999 : Blo 2083435 2083999 := bstep (se 1 (by rfl) ⟨1562999, by rfl⟩ : syracuseStep 2083999 = 3125999) B3125999
theorem B3126005 : Blo 2083435 3126005 := bbase (se 5 (by rfl) ⟨146531, by rfl⟩ : syracuseStep 3126005 = 293063) (by norm_num)
theorem B2084003 : Blo 2083435 2084003 := bstep (se 1 (by rfl) ⟨1563002, by rfl⟩ : syracuseStep 2084003 = 3126005) B3126005
theorem B6676357 : Blo 2083435 6676357 := bbase (se 4 (by rfl) ⟨625908, by rfl⟩ : syracuseStep 6676357 = 1251817) (by norm_num)
theorem B8901809 : Blo 2083435 8901809 := bstep (se 2 (by rfl) ⟨3338178, by rfl⟩ : syracuseStep 8901809 = 6676357) B6676357
theorem B5934539 : Blo 2083435 5934539 := bstep (se 1 (by rfl) ⟨4450904, by rfl⟩ : syracuseStep 5934539 = 8901809) B8901809
theorem B3956359 : Blo 2083435 3956359 := bstep (se 1 (by rfl) ⟨2967269, by rfl⟩ : syracuseStep 3956359 = 5934539) B5934539
theorem B5275145 : Blo 2083435 5275145 := bstep (se 2 (by rfl) ⟨1978179, by rfl⟩ : syracuseStep 5275145 = 3956359) B3956359
theorem B3516763 : Blo 2083435 3516763 := bstep (se 1 (by rfl) ⟨2637572, by rfl⟩ : syracuseStep 3516763 = 5275145) B5275145
theorem B4689017 : Blo 2083435 4689017 := bstep (se 2 (by rfl) ⟨1758381, by rfl⟩ : syracuseStep 4689017 = 3516763) B3516763
theorem B3126011 : Blo 2083435 3126011 := bstep (se 1 (by rfl) ⟨2344508, by rfl⟩ : syracuseStep 3126011 = 4689017) B4689017
theorem B2084007 : Blo 2083435 2084007 := bstep (se 1 (by rfl) ⟨1563005, by rfl⟩ : syracuseStep 2084007 = 3126011) B3126011
theorem B2344513 : Blo 2083435 2344513 := bbase (se 2 (by rfl) ⟨879192, by rfl⟩ : syracuseStep 2344513 = 1758385) (by norm_num)
theorem B3126017 : Blo 2083435 3126017 := bstep (se 2 (by rfl) ⟨1172256, by rfl⟩ : syracuseStep 3126017 = 2344513) B2344513
theorem B2084011 : Blo 2083435 2084011 := bstep (se 1 (by rfl) ⟨1563008, by rfl⟩ : syracuseStep 2084011 = 3126017) B3126017
theorem B5275165 : Blo 2083435 5275165 := bbase (se 3 (by rfl) ⟨989093, by rfl⟩ : syracuseStep 5275165 = 1978187) (by norm_num)
theorem B7033553 : Blo 2083435 7033553 := bstep (se 2 (by rfl) ⟨2637582, by rfl⟩ : syracuseStep 7033553 = 5275165) B5275165
theorem B4689035 : Blo 2083435 4689035 := bstep (se 1 (by rfl) ⟨3516776, by rfl⟩ : syracuseStep 4689035 = 7033553) B7033553
theorem B3126023 : Blo 2083435 3126023 := bstep (se 1 (by rfl) ⟨2344517, by rfl⟩ : syracuseStep 3126023 = 4689035) B4689035
theorem B2084015 : Blo 2083435 2084015 := bstep (se 1 (by rfl) ⟨1563011, by rfl⟩ : syracuseStep 2084015 = 3126023) B3126023
theorem B3126029 : Blo 2083435 3126029 := bbase (se 3 (by rfl) ⟨586130, by rfl⟩ : syracuseStep 3126029 = 1172261) (by norm_num)
theorem B2084019 : Blo 2083435 2084019 := bstep (se 1 (by rfl) ⟨1563014, by rfl⟩ : syracuseStep 2084019 = 3126029) B3126029
theorem B4689053 : Blo 2083435 4689053 := bbase (se 3 (by rfl) ⟨879197, by rfl⟩ : syracuseStep 4689053 = 1758395) (by norm_num)
theorem B3126035 : Blo 2083435 3126035 := bstep (se 1 (by rfl) ⟨2344526, by rfl⟩ : syracuseStep 3126035 = 4689053) B4689053
theorem B2084023 : Blo 2083435 2084023 := bstep (se 1 (by rfl) ⟨1563017, by rfl⟩ : syracuseStep 2084023 = 3126035) B3126035
theorem B3516797 : Blo 2083435 3516797 := bbase (se 3 (by rfl) ⟨659399, by rfl⟩ : syracuseStep 3516797 = 1318799) (by norm_num)
theorem B2344531 : Blo 2083435 2344531 := bstep (se 1 (by rfl) ⟨1758398, by rfl⟩ : syracuseStep 2344531 = 3516797) B3516797
theorem B3126041 : Blo 2083435 3126041 := bstep (se 2 (by rfl) ⟨1172265, by rfl⟩ : syracuseStep 3126041 = 2344531) B2344531
theorem B2084027 : Blo 2083435 2084027 := bstep (se 1 (by rfl) ⟨1563020, by rfl⟩ : syracuseStep 2084027 = 3126041) B3126041
theorem B5007325 : Blo 2083435 5007325 := bbase (se 3 (by rfl) ⟨938873, by rfl⟩ : syracuseStep 5007325 = 1877747) (by norm_num)
theorem B6676433 : Blo 2083435 6676433 := bstep (se 2 (by rfl) ⟨2503662, by rfl⟩ : syracuseStep 6676433 = 5007325) B5007325
theorem B4450955 : Blo 2083435 4450955 := bstep (se 1 (by rfl) ⟨3338216, by rfl⟩ : syracuseStep 4450955 = 6676433) B6676433
theorem B11869213 : Blo 2083435 11869213 := bstep (se 3 (by rfl) ⟨2225477, by rfl⟩ : syracuseStep 11869213 = 4450955) B4450955
theorem B15825617 : Blo 2083435 15825617 := bstep (se 2 (by rfl) ⟨5934606, by rfl⟩ : syracuseStep 15825617 = 11869213) B11869213
theorem B10550411 : Blo 2083435 10550411 := bstep (se 1 (by rfl) ⟨7912808, by rfl⟩ : syracuseStep 10550411 = 15825617) B15825617
theorem B7033607 : Blo 2083435 7033607 := bstep (se 1 (by rfl) ⟨5275205, by rfl⟩ : syracuseStep 7033607 = 10550411) B10550411
theorem B4689071 : Blo 2083435 4689071 := bstep (se 1 (by rfl) ⟨3516803, by rfl⟩ : syracuseStep 4689071 = 7033607) B7033607
theorem B3126047 : Blo 2083435 3126047 := bstep (se 1 (by rfl) ⟨2344535, by rfl⟩ : syracuseStep 3126047 = 4689071) B4689071
theorem B2084031 : Blo 2083435 2084031 := bstep (se 1 (by rfl) ⟨1563023, by rfl⟩ : syracuseStep 2084031 = 3126047) B3126047
theorem B3126053 : Blo 2083435 3126053 := bbase (se 4 (by rfl) ⟨293067, by rfl⟩ : syracuseStep 3126053 = 586135) (by norm_num)
theorem B2084035 : Blo 2083435 2084035 := bstep (se 1 (by rfl) ⟨1563026, by rfl⟩ : syracuseStep 2084035 = 3126053) B3126053
theorem B2637613 : Blo 2083435 2637613 := bbase (se 3 (by rfl) ⟨494552, by rfl⟩ : syracuseStep 2637613 = 989105) (by norm_num)
theorem B3516817 : Blo 2083435 3516817 := bstep (se 2 (by rfl) ⟨1318806, by rfl⟩ : syracuseStep 3516817 = 2637613) B2637613
theorem B4689089 : Blo 2083435 4689089 := bstep (se 2 (by rfl) ⟨1758408, by rfl⟩ : syracuseStep 4689089 = 3516817) B3516817
theorem B3126059 : Blo 2083435 3126059 := bstep (se 1 (by rfl) ⟨2344544, by rfl⟩ : syracuseStep 3126059 = 4689089) B4689089
theorem B2084039 : Blo 2083435 2084039 := bstep (se 1 (by rfl) ⟨1563029, by rfl⟩ : syracuseStep 2084039 = 3126059) B3126059
theorem B2344549 : Blo 2083435 2344549 := bbase (se 4 (by rfl) ⟨219801, by rfl⟩ : syracuseStep 2344549 = 439603) (by norm_num)
theorem B3126065 : Blo 2083435 3126065 := bstep (se 2 (by rfl) ⟨1172274, by rfl⟩ : syracuseStep 3126065 = 2344549) B2344549
theorem B2084043 : Blo 2083435 2084043 := bstep (se 1 (by rfl) ⟨1563032, by rfl⟩ : syracuseStep 2084043 = 3126065) B3126065
theorem B5007365 : Blo 2083435 5007365 := bbase (se 4 (by rfl) ⟨469440, by rfl⟩ : syracuseStep 5007365 = 938881) (by norm_num)
theorem B3338243 : Blo 2083435 3338243 := bstep (se 1 (by rfl) ⟨2503682, by rfl⟩ : syracuseStep 3338243 = 5007365) B5007365
theorem B2225495 : Blo 2083435 2225495 := bstep (se 1 (by rfl) ⟨1669121, by rfl⟩ : syracuseStep 2225495 = 3338243) B3338243
theorem B5934653 : Blo 2083435 5934653 := bstep (se 3 (by rfl) ⟨1112747, by rfl⟩ : syracuseStep 5934653 = 2225495) B2225495
theorem B3956435 : Blo 2083435 3956435 := bstep (se 1 (by rfl) ⟨2967326, by rfl⟩ : syracuseStep 3956435 = 5934653) B5934653
theorem B2637623 : Blo 2083435 2637623 := bstep (se 1 (by rfl) ⟨1978217, by rfl⟩ : syracuseStep 2637623 = 3956435) B3956435
theorem B7033661 : Blo 2083435 7033661 := bstep (se 3 (by rfl) ⟨1318811, by rfl⟩ : syracuseStep 7033661 = 2637623) B2637623
theorem B4689107 : Blo 2083435 4689107 := bstep (se 1 (by rfl) ⟨3516830, by rfl⟩ : syracuseStep 4689107 = 7033661) B7033661
theorem B3126071 : Blo 2083435 3126071 := bstep (se 1 (by rfl) ⟨2344553, by rfl⟩ : syracuseStep 3126071 = 4689107) B4689107
theorem B2084047 : Blo 2083435 2084047 := bstep (se 1 (by rfl) ⟨1563035, by rfl⟩ : syracuseStep 2084047 = 3126071) B3126071
theorem B3126077 : Blo 2083435 3126077 := bbase (se 3 (by rfl) ⟨586139, by rfl⟩ : syracuseStep 3126077 = 1172279) (by norm_num)
theorem B2084051 : Blo 2083435 2084051 := bstep (se 1 (by rfl) ⟨1563038, by rfl⟩ : syracuseStep 2084051 = 3126077) B3126077
theorem B4689125 : Blo 2083435 4689125 := bbase (se 4 (by rfl) ⟨439605, by rfl⟩ : syracuseStep 4689125 = 879211) (by norm_num)
theorem B3126083 : Blo 2083435 3126083 := bstep (se 1 (by rfl) ⟨2344562, by rfl⟩ : syracuseStep 3126083 = 4689125) B4689125
theorem B2084055 : Blo 2083435 2084055 := bstep (se 1 (by rfl) ⟨1563041, by rfl⟩ : syracuseStep 2084055 = 3126083) B3126083
theorem B5275277 : Blo 2083435 5275277 := bbase (se 3 (by rfl) ⟨989114, by rfl⟩ : syracuseStep 5275277 = 1978229) (by norm_num)
theorem B3516851 : Blo 2083435 3516851 := bstep (se 1 (by rfl) ⟨2637638, by rfl⟩ : syracuseStep 3516851 = 5275277) B5275277
theorem B2344567 : Blo 2083435 2344567 := bstep (se 1 (by rfl) ⟨1758425, by rfl⟩ : syracuseStep 2344567 = 3516851) B3516851
theorem B3126089 : Blo 2083435 3126089 := bstep (se 2 (by rfl) ⟨1172283, by rfl⟩ : syracuseStep 3126089 = 2344567) B2344567
theorem B2084059 : Blo 2083435 2084059 := bstep (se 1 (by rfl) ⟨1563044, by rfl⟩ : syracuseStep 2084059 = 3126089) B3126089
theorem B2967349 : Blo 2083435 2967349 := bbase (se 5 (by rfl) ⟨139094, by rfl⟩ : syracuseStep 2967349 = 278189) (by norm_num)
theorem B3956465 : Blo 2083435 3956465 := bstep (se 2 (by rfl) ⟨1483674, by rfl⟩ : syracuseStep 3956465 = 2967349) B2967349
theorem B10550573 : Blo 2083435 10550573 := bstep (se 3 (by rfl) ⟨1978232, by rfl⟩ : syracuseStep 10550573 = 3956465) B3956465
theorem B7033715 : Blo 2083435 7033715 := bstep (se 1 (by rfl) ⟨5275286, by rfl⟩ : syracuseStep 7033715 = 10550573) B10550573
theorem B4689143 : Blo 2083435 4689143 := bstep (se 1 (by rfl) ⟨3516857, by rfl⟩ : syracuseStep 4689143 = 7033715) B7033715
theorem B3126095 : Blo 2083435 3126095 := bstep (se 1 (by rfl) ⟨2344571, by rfl⟩ : syracuseStep 3126095 = 4689143) B4689143
theorem B2084063 : Blo 2083435 2084063 := bstep (se 1 (by rfl) ⟨1563047, by rfl⟩ : syracuseStep 2084063 = 3126095) B3126095
theorem B3126101 : Blo 2083435 3126101 := bbase (se 9 (by rfl) ⟨9158, by rfl⟩ : syracuseStep 3126101 = 18317) (by norm_num)
theorem B2084067 : Blo 2083435 2084067 := bstep (se 1 (by rfl) ⟨1563050, by rfl⟩ : syracuseStep 2084067 = 3126101) B3126101
theorem B4120645 : Blo 2083435 4120645 := bbase (se 4 (by rfl) ⟨386310, by rfl⟩ : syracuseStep 4120645 = 772621) (by norm_num)
theorem B5494193 : Blo 2083435 5494193 := bstep (se 2 (by rfl) ⟨2060322, by rfl⟩ : syracuseStep 5494193 = 4120645) B4120645
theorem B3662795 : Blo 2083435 3662795 := bstep (se 1 (by rfl) ⟨2747096, by rfl⟩ : syracuseStep 3662795 = 5494193) B5494193
theorem B2441863 : Blo 2083435 2441863 := bstep (se 1 (by rfl) ⟨1831397, by rfl⟩ : syracuseStep 2441863 = 3662795) B3662795
theorem B3255817 : Blo 2083435 3255817 := bstep (se 2 (by rfl) ⟨1220931, by rfl⟩ : syracuseStep 3255817 = 2441863) B2441863
theorem B4341089 : Blo 2083435 4341089 := bstep (se 2 (by rfl) ⟨1627908, by rfl⟩ : syracuseStep 4341089 = 3255817) B3255817
theorem B2894059 : Blo 2083435 2894059 := bstep (se 1 (by rfl) ⟨2170544, by rfl⟩ : syracuseStep 2894059 = 4341089) B4341089
theorem B15434981 : Blo 2083435 15434981 := bstep (se 4 (by rfl) ⟨1447029, by rfl⟩ : syracuseStep 15434981 = 2894059) B2894059
theorem B10289987 : Blo 2083435 10289987 := bstep (se 1 (by rfl) ⟨7717490, by rfl⟩ : syracuseStep 10289987 = 15434981) B15434981
theorem B6859991 : Blo 2083435 6859991 := bstep (se 1 (by rfl) ⟨5144993, by rfl⟩ : syracuseStep 6859991 = 10289987) B10289987
theorem B18293309 : Blo 2083435 18293309 := bstep (se 3 (by rfl) ⟨3429995, by rfl⟩ : syracuseStep 18293309 = 6859991) B6859991
theorem B12195539 : Blo 2083435 12195539 := bstep (se 1 (by rfl) ⟨9146654, by rfl⟩ : syracuseStep 12195539 = 18293309) B18293309
theorem B8130359 : Blo 2083435 8130359 := bstep (se 1 (by rfl) ⟨6097769, by rfl⟩ : syracuseStep 8130359 = 12195539) B12195539
theorem B5420239 : Blo 2083435 5420239 := bstep (se 1 (by rfl) ⟨4065179, by rfl⟩ : syracuseStep 5420239 = 8130359) B8130359
theorem B28907941 : Blo 2083435 28907941 := bstep (se 4 (by rfl) ⟨2710119, by rfl⟩ : syracuseStep 28907941 = 5420239) B5420239
theorem B38543921 : Blo 2083435 38543921 := bstep (se 2 (by rfl) ⟨14453970, by rfl⟩ : syracuseStep 38543921 = 28907941) B28907941
theorem B25695947 : Blo 2083435 25695947 := bstep (se 1 (by rfl) ⟨19271960, by rfl⟩ : syracuseStep 25695947 = 38543921) B38543921
theorem B17130631 : Blo 2083435 17130631 := bstep (se 1 (by rfl) ⟨12847973, by rfl⟩ : syracuseStep 17130631 = 25695947) B25695947
theorem B22840841 : Blo 2083435 22840841 := bstep (se 2 (by rfl) ⟨8565315, by rfl⟩ : syracuseStep 22840841 = 17130631) B17130631
theorem B15227227 : Blo 2083435 15227227 := bstep (se 1 (by rfl) ⟨11420420, by rfl⟩ : syracuseStep 15227227 = 22840841) B22840841
theorem B20302969 : Blo 2083435 20302969 := bstep (se 2 (by rfl) ⟨7613613, by rfl⟩ : syracuseStep 20302969 = 15227227) B15227227
theorem B27070625 : Blo 2083435 27070625 := bstep (se 2 (by rfl) ⟨10151484, by rfl⟩ : syracuseStep 27070625 = 20302969) B20302969
theorem B18047083 : Blo 2083435 18047083 := bstep (se 1 (by rfl) ⟨13535312, by rfl⟩ : syracuseStep 18047083 = 27070625) B27070625
theorem B24062777 : Blo 2083435 24062777 := bstep (se 2 (by rfl) ⟨9023541, by rfl⟩ : syracuseStep 24062777 = 18047083) B18047083
theorem B16041851 : Blo 2083435 16041851 := bstep (se 1 (by rfl) ⟨12031388, by rfl⟩ : syracuseStep 16041851 = 24062777) B24062777
theorem B10694567 : Blo 2083435 10694567 := bstep (se 1 (by rfl) ⟨8020925, by rfl⟩ : syracuseStep 10694567 = 16041851) B16041851
theorem B7129711 : Blo 2083435 7129711 := bstep (se 1 (by rfl) ⟨5347283, by rfl⟩ : syracuseStep 7129711 = 10694567) B10694567
theorem B9506281 : Blo 2083435 9506281 := bstep (se 2 (by rfl) ⟨3564855, by rfl⟩ : syracuseStep 9506281 = 7129711) B7129711
theorem B12675041 : Blo 2083435 12675041 := bstep (se 2 (by rfl) ⟨4753140, by rfl⟩ : syracuseStep 12675041 = 9506281) B9506281
theorem B8450027 : Blo 2083435 8450027 := bstep (se 1 (by rfl) ⟨6337520, by rfl⟩ : syracuseStep 8450027 = 12675041) B12675041
theorem B5633351 : Blo 2083435 5633351 := bstep (se 1 (by rfl) ⟨4225013, by rfl⟩ : syracuseStep 5633351 = 8450027) B8450027
theorem B3755567 : Blo 2083435 3755567 := bstep (se 1 (by rfl) ⟨2816675, by rfl⟩ : syracuseStep 3755567 = 5633351) B5633351
theorem B2503711 : Blo 2083435 2503711 := bstep (se 1 (by rfl) ⟨1877783, by rfl⟩ : syracuseStep 2503711 = 3755567) B3755567
theorem B3338281 : Blo 2083435 3338281 := bstep (se 2 (by rfl) ⟨1251855, by rfl⟩ : syracuseStep 3338281 = 2503711) B2503711
theorem B4451041 : Blo 2083435 4451041 := bstep (se 2 (by rfl) ⟨1669140, by rfl⟩ : syracuseStep 4451041 = 3338281) B3338281
theorem B5934721 : Blo 2083435 5934721 := bstep (se 2 (by rfl) ⟨2225520, by rfl⟩ : syracuseStep 5934721 = 4451041) B4451041
theorem B7912961 : Blo 2083435 7912961 := bstep (se 2 (by rfl) ⟨2967360, by rfl⟩ : syracuseStep 7912961 = 5934721) B5934721
theorem B5275307 : Blo 2083435 5275307 := bstep (se 1 (by rfl) ⟨3956480, by rfl⟩ : syracuseStep 5275307 = 7912961) B7912961
theorem B3516871 : Blo 2083435 3516871 := bstep (se 1 (by rfl) ⟨2637653, by rfl⟩ : syracuseStep 3516871 = 5275307) B5275307
theorem B4689161 : Blo 2083435 4689161 := bstep (se 2 (by rfl) ⟨1758435, by rfl⟩ : syracuseStep 4689161 = 3516871) B3516871
theorem B3126107 : Blo 2083435 3126107 := bstep (se 1 (by rfl) ⟨2344580, by rfl⟩ : syracuseStep 3126107 = 4689161) B4689161
theorem B2084071 : Blo 2083435 2084071 := bstep (se 1 (by rfl) ⟨1563053, by rfl⟩ : syracuseStep 2084071 = 3126107) B3126107
theorem B2344585 : Blo 2083435 2344585 := bbase (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) (by norm_num)
theorem B3126113 : Blo 2083435 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B2084075 : Blo 2083435 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B5347301 : Blo 2083435 5347301 := bbase (se 4 (by rfl) ⟨501309, by rfl⟩ : syracuseStep 5347301 = 1002619) (by norm_num)
theorem B57037877 : Blo 2083435 57037877 := bstep (se 5 (by rfl) ⟨2673650, by rfl⟩ : syracuseStep 57037877 = 5347301) B5347301
theorem B38025251 : Blo 2083435 38025251 := bstep (se 1 (by rfl) ⟨28518938, by rfl⟩ : syracuseStep 38025251 = 57037877) B57037877
theorem B25350167 : Blo 2083435 25350167 := bstep (se 1 (by rfl) ⟨19012625, by rfl⟩ : syracuseStep 25350167 = 38025251) B38025251
theorem B16900111 : Blo 2083435 16900111 := bstep (se 1 (by rfl) ⟨12675083, by rfl⟩ : syracuseStep 16900111 = 25350167) B25350167
theorem B22533481 : Blo 2083435 22533481 := bstep (se 2 (by rfl) ⟨8450055, by rfl⟩ : syracuseStep 22533481 = 16900111) B16900111
theorem B30044641 : Blo 2083435 30044641 := bstep (se 2 (by rfl) ⟨11266740, by rfl⟩ : syracuseStep 30044641 = 22533481) B22533481
theorem B40059521 : Blo 2083435 40059521 := bstep (se 2 (by rfl) ⟨15022320, by rfl⟩ : syracuseStep 40059521 = 30044641) B30044641
theorem B26706347 : Blo 2083435 26706347 := bstep (se 1 (by rfl) ⟨20029760, by rfl⟩ : syracuseStep 26706347 = 40059521) B40059521
theorem B17804231 : Blo 2083435 17804231 := bstep (se 1 (by rfl) ⟨13353173, by rfl⟩ : syracuseStep 17804231 = 26706347) B26706347
theorem B11869487 : Blo 2083435 11869487 := bstep (se 1 (by rfl) ⟨8902115, by rfl⟩ : syracuseStep 11869487 = 17804231) B17804231
theorem B7912991 : Blo 2083435 7912991 := bstep (se 1 (by rfl) ⟨5934743, by rfl⟩ : syracuseStep 7912991 = 11869487) B11869487
theorem B5275327 : Blo 2083435 5275327 := bstep (se 1 (by rfl) ⟨3956495, by rfl⟩ : syracuseStep 5275327 = 7912991) B7912991
theorem B7033769 : Blo 2083435 7033769 := bstep (se 2 (by rfl) ⟨2637663, by rfl⟩ : syracuseStep 7033769 = 5275327) B5275327
theorem B4689179 : Blo 2083435 4689179 := bstep (se 1 (by rfl) ⟨3516884, by rfl⟩ : syracuseStep 4689179 = 7033769) B7033769
theorem B3126119 : Blo 2083435 3126119 := bstep (se 1 (by rfl) ⟨2344589, by rfl⟩ : syracuseStep 3126119 = 4689179) B4689179
theorem B2084079 : Blo 2083435 2084079 := bstep (se 1 (by rfl) ⟨1563059, by rfl⟩ : syracuseStep 2084079 = 3126119) B3126119
theorem B3126125 : Blo 2083435 3126125 := bbase (se 3 (by rfl) ⟨586148, by rfl⟩ : syracuseStep 3126125 = 1172297) (by norm_num)
theorem B2084083 : Blo 2083435 2084083 := bstep (se 1 (by rfl) ⟨1563062, by rfl⟩ : syracuseStep 2084083 = 3126125) B3126125
theorem B4689197 : Blo 2083435 4689197 := bbase (se 3 (by rfl) ⟨879224, by rfl⟩ : syracuseStep 4689197 = 1758449) (by norm_num)
theorem B3126131 : Blo 2083435 3126131 := bstep (se 1 (by rfl) ⟨2344598, by rfl⟩ : syracuseStep 3126131 = 4689197) B4689197
theorem B2084087 : Blo 2083435 2084087 := bstep (se 1 (by rfl) ⟨1563065, by rfl⟩ : syracuseStep 2084087 = 3126131) B3126131
theorem B7129781 : Blo 2083435 7129781 := bbase (se 5 (by rfl) ⟨334208, by rfl⟩ : syracuseStep 7129781 = 668417) (by norm_num)
theorem B4753187 : Blo 2083435 4753187 := bstep (se 1 (by rfl) ⟨3564890, by rfl⟩ : syracuseStep 4753187 = 7129781) B7129781
theorem B3168791 : Blo 2083435 3168791 := bstep (se 1 (by rfl) ⟨2376593, by rfl⟩ : syracuseStep 3168791 = 4753187) B4753187
theorem B2112527 : Blo 2083435 2112527 := bstep (se 1 (by rfl) ⟨1584395, by rfl⟩ : syracuseStep 2112527 = 3168791) B3168791
theorem B5633405 : Blo 2083435 5633405 := bstep (se 3 (by rfl) ⟨1056263, by rfl⟩ : syracuseStep 5633405 = 2112527) B2112527
theorem B3755603 : Blo 2083435 3755603 := bstep (se 1 (by rfl) ⟨2816702, by rfl⟩ : syracuseStep 3755603 = 5633405) B5633405
theorem B10014941 : Blo 2083435 10014941 := bstep (se 3 (by rfl) ⟨1877801, by rfl⟩ : syracuseStep 10014941 = 3755603) B3755603
theorem B6676627 : Blo 2083435 6676627 := bstep (se 1 (by rfl) ⟨5007470, by rfl⟩ : syracuseStep 6676627 = 10014941) B10014941
theorem B8902169 : Blo 2083435 8902169 := bstep (se 2 (by rfl) ⟨3338313, by rfl⟩ : syracuseStep 8902169 = 6676627) B6676627
theorem B5934779 : Blo 2083435 5934779 := bstep (se 1 (by rfl) ⟨4451084, by rfl⟩ : syracuseStep 5934779 = 8902169) B8902169
theorem B3956519 : Blo 2083435 3956519 := bstep (se 1 (by rfl) ⟨2967389, by rfl⟩ : syracuseStep 3956519 = 5934779) B5934779
theorem B2637679 : Blo 2083435 2637679 := bstep (se 1 (by rfl) ⟨1978259, by rfl⟩ : syracuseStep 2637679 = 3956519) B3956519
theorem B3516905 : Blo 2083435 3516905 := bstep (se 2 (by rfl) ⟨1318839, by rfl⟩ : syracuseStep 3516905 = 2637679) B2637679
theorem B2344603 : Blo 2083435 2344603 := bstep (se 1 (by rfl) ⟨1758452, by rfl⟩ : syracuseStep 2344603 = 3516905) B3516905
theorem B3126137 : Blo 2083435 3126137 := bstep (se 2 (by rfl) ⟨1172301, by rfl⟩ : syracuseStep 3126137 = 2344603) B2344603
theorem B2084091 : Blo 2083435 2084091 := bstep (se 1 (by rfl) ⟨1563068, by rfl⟩ : syracuseStep 2084091 = 3126137) B3126137
theorem B22533653 : Blo 2083435 22533653 := bbase (se 6 (by rfl) ⟨528132, by rfl⟩ : syracuseStep 22533653 = 1056265) (by norm_num)
theorem B15022435 : Blo 2083435 15022435 := bstep (se 1 (by rfl) ⟨11266826, by rfl⟩ : syracuseStep 15022435 = 22533653) B22533653
theorem B20029913 : Blo 2083435 20029913 := bstep (se 2 (by rfl) ⟨7511217, by rfl⟩ : syracuseStep 20029913 = 15022435) B15022435
theorem B13353275 : Blo 2083435 13353275 := bstep (se 1 (by rfl) ⟨10014956, by rfl⟩ : syracuseStep 13353275 = 20029913) B20029913
theorem B35608733 : Blo 2083435 35608733 := bstep (se 3 (by rfl) ⟨6676637, by rfl⟩ : syracuseStep 35608733 = 13353275) B13353275
theorem B23739155 : Blo 2083435 23739155 := bstep (se 1 (by rfl) ⟨17804366, by rfl⟩ : syracuseStep 23739155 = 35608733) B35608733
theorem B15826103 : Blo 2083435 15826103 := bstep (se 1 (by rfl) ⟨11869577, by rfl⟩ : syracuseStep 15826103 = 23739155) B23739155
theorem B10550735 : Blo 2083435 10550735 := bstep (se 1 (by rfl) ⟨7913051, by rfl⟩ : syracuseStep 10550735 = 15826103) B15826103
theorem B7033823 : Blo 2083435 7033823 := bstep (se 1 (by rfl) ⟨5275367, by rfl⟩ : syracuseStep 7033823 = 10550735) B10550735
theorem B4689215 : Blo 2083435 4689215 := bstep (se 1 (by rfl) ⟨3516911, by rfl⟩ : syracuseStep 4689215 = 7033823) B7033823
theorem B3126143 : Blo 2083435 3126143 := bstep (se 1 (by rfl) ⟨2344607, by rfl⟩ : syracuseStep 3126143 = 4689215) B4689215
theorem B2084095 : Blo 2083435 2084095 := bstep (se 1 (by rfl) ⟨1563071, by rfl⟩ : syracuseStep 2084095 = 3126143) B3126143
theorem B3126149 : Blo 2083435 3126149 := bbase (se 4 (by rfl) ⟨293076, by rfl⟩ : syracuseStep 3126149 = 586153) (by norm_num)
theorem B2084099 : Blo 2083435 2084099 := bstep (se 1 (by rfl) ⟨1563074, by rfl⟩ : syracuseStep 2084099 = 3126149) B3126149
theorem B3516925 : Blo 2083435 3516925 := bbase (se 3 (by rfl) ⟨659423, by rfl⟩ : syracuseStep 3516925 = 1318847) (by norm_num)
theorem B4689233 : Blo 2083435 4689233 := bstep (se 2 (by rfl) ⟨1758462, by rfl⟩ : syracuseStep 4689233 = 3516925) B3516925
theorem B3126155 : Blo 2083435 3126155 := bstep (se 1 (by rfl) ⟨2344616, by rfl⟩ : syracuseStep 3126155 = 4689233) B4689233
theorem B2084103 : Blo 2083435 2084103 := bstep (se 1 (by rfl) ⟨1563077, by rfl⟩ : syracuseStep 2084103 = 3126155) B3126155
theorem B2344621 : Blo 2083435 2344621 := bbase (se 3 (by rfl) ⟨439616, by rfl⟩ : syracuseStep 2344621 = 879233) (by norm_num)
theorem B3126161 : Blo 2083435 3126161 := bstep (se 2 (by rfl) ⟨1172310, by rfl⟩ : syracuseStep 3126161 = 2344621) B2344621
theorem B2084107 : Blo 2083435 2084107 := bstep (se 1 (by rfl) ⟨1563080, by rfl⟩ : syracuseStep 2084107 = 3126161) B3126161
theorem B7033877 : Blo 2083435 7033877 := bbase (se 6 (by rfl) ⟨164856, by rfl⟩ : syracuseStep 7033877 = 329713) (by norm_num)
theorem B4689251 : Blo 2083435 4689251 := bstep (se 1 (by rfl) ⟨3516938, by rfl⟩ : syracuseStep 4689251 = 7033877) B7033877
theorem B3126167 : Blo 2083435 3126167 := bstep (se 1 (by rfl) ⟨2344625, by rfl⟩ : syracuseStep 3126167 = 4689251) B4689251
theorem B2084111 : Blo 2083435 2084111 := bstep (se 1 (by rfl) ⟨1563083, by rfl⟩ : syracuseStep 2084111 = 3126167) B3126167
theorem B3126173 : Blo 2083435 3126173 := bbase (se 3 (by rfl) ⟨586157, by rfl⟩ : syracuseStep 3126173 = 1172315) (by norm_num)
theorem B2084115 : Blo 2083435 2084115 := bstep (se 1 (by rfl) ⟨1563086, by rfl⟩ : syracuseStep 2084115 = 3126173) B3126173
theorem B4689269 : Blo 2083435 4689269 := bbase (se 5 (by rfl) ⟨219809, by rfl⟩ : syracuseStep 4689269 = 439619) (by norm_num)
theorem B3126179 : Blo 2083435 3126179 := bstep (se 1 (by rfl) ⟨2344634, by rfl⟩ : syracuseStep 3126179 = 4689269) B4689269
theorem B2084119 : Blo 2083435 2084119 := bstep (se 1 (by rfl) ⟨1563089, by rfl⟩ : syracuseStep 2084119 = 3126179) B3126179
theorem B10015093 : Blo 2083435 10015093 := bbase (se 5 (by rfl) ⟨469457, by rfl⟩ : syracuseStep 10015093 = 938915) (by norm_num)
theorem B13353457 : Blo 2083435 13353457 := bstep (se 2 (by rfl) ⟨5007546, by rfl⟩ : syracuseStep 13353457 = 10015093) B10015093
theorem B17804609 : Blo 2083435 17804609 := bstep (se 2 (by rfl) ⟨6676728, by rfl⟩ : syracuseStep 17804609 = 13353457) B13353457
theorem B11869739 : Blo 2083435 11869739 := bstep (se 1 (by rfl) ⟨8902304, by rfl⟩ : syracuseStep 11869739 = 17804609) B17804609
theorem B7913159 : Blo 2083435 7913159 := bstep (se 1 (by rfl) ⟨5934869, by rfl⟩ : syracuseStep 7913159 = 11869739) B11869739
theorem B5275439 : Blo 2083435 5275439 := bstep (se 1 (by rfl) ⟨3956579, by rfl⟩ : syracuseStep 5275439 = 7913159) B7913159
theorem B3516959 : Blo 2083435 3516959 := bstep (se 1 (by rfl) ⟨2637719, by rfl⟩ : syracuseStep 3516959 = 5275439) B5275439
theorem B2344639 : Blo 2083435 2344639 := bstep (se 1 (by rfl) ⟨1758479, by rfl⟩ : syracuseStep 2344639 = 3516959) B3516959
theorem B3126185 : Blo 2083435 3126185 := bstep (se 2 (by rfl) ⟨1172319, by rfl⟩ : syracuseStep 3126185 = 2344639) B2344639
theorem B2084123 : Blo 2083435 2084123 := bstep (se 1 (by rfl) ⟨1563092, by rfl⟩ : syracuseStep 2084123 = 3126185) B3126185
theorem B7913173 : Blo 2083435 7913173 := bbase (se 7 (by rfl) ⟨92732, by rfl⟩ : syracuseStep 7913173 = 185465) (by norm_num)
theorem B10550897 : Blo 2083435 10550897 := bstep (se 2 (by rfl) ⟨3956586, by rfl⟩ : syracuseStep 10550897 = 7913173) B7913173
theorem B7033931 : Blo 2083435 7033931 := bstep (se 1 (by rfl) ⟨5275448, by rfl⟩ : syracuseStep 7033931 = 10550897) B10550897
theorem B4689287 : Blo 2083435 4689287 := bstep (se 1 (by rfl) ⟨3516965, by rfl⟩ : syracuseStep 4689287 = 7033931) B7033931
theorem B3126191 : Blo 2083435 3126191 := bstep (se 1 (by rfl) ⟨2344643, by rfl⟩ : syracuseStep 3126191 = 4689287) B4689287
theorem B2084127 : Blo 2083435 2084127 := bstep (se 1 (by rfl) ⟨1563095, by rfl⟩ : syracuseStep 2084127 = 3126191) B3126191
theorem B3126197 : Blo 2083435 3126197 := bbase (se 5 (by rfl) ⟨146540, by rfl⟩ : syracuseStep 3126197 = 293081) (by norm_num)
theorem B2084131 : Blo 2083435 2084131 := bstep (se 1 (by rfl) ⟨1563098, by rfl⟩ : syracuseStep 2084131 = 3126197) B3126197
theorem B5275469 : Blo 2083435 5275469 := bbase (se 3 (by rfl) ⟨989150, by rfl⟩ : syracuseStep 5275469 = 1978301) (by norm_num)
theorem B3516979 : Blo 2083435 3516979 := bstep (se 1 (by rfl) ⟨2637734, by rfl⟩ : syracuseStep 3516979 = 5275469) B5275469
theorem B4689305 : Blo 2083435 4689305 := bstep (se 2 (by rfl) ⟨1758489, by rfl⟩ : syracuseStep 4689305 = 3516979) B3516979
theorem B3126203 : Blo 2083435 3126203 := bstep (se 1 (by rfl) ⟨2344652, by rfl⟩ : syracuseStep 3126203 = 4689305) B4689305
theorem B2084135 : Blo 2083435 2084135 := bstep (se 1 (by rfl) ⟨1563101, by rfl⟩ : syracuseStep 2084135 = 3126203) B3126203
theorem B2344657 : Blo 2083435 2344657 := bbase (se 2 (by rfl) ⟨879246, by rfl⟩ : syracuseStep 2344657 = 1758493) (by norm_num)
theorem B3126209 : Blo 2083435 3126209 := bstep (se 2 (by rfl) ⟨1172328, by rfl⟩ : syracuseStep 3126209 = 2344657) B2344657
theorem B2084139 : Blo 2083435 2084139 := bstep (se 1 (by rfl) ⟨1563104, by rfl⟩ : syracuseStep 2084139 = 3126209) B3126209
theorem B7129957 : Blo 2083435 7129957 := bbase (se 4 (by rfl) ⟨668433, by rfl⟩ : syracuseStep 7129957 = 1336867) (by norm_num)
theorem B9506609 : Blo 2083435 9506609 := bstep (se 2 (by rfl) ⟨3564978, by rfl⟩ : syracuseStep 9506609 = 7129957) B7129957
theorem B6337739 : Blo 2083435 6337739 := bstep (se 1 (by rfl) ⟨4753304, by rfl⟩ : syracuseStep 6337739 = 9506609) B9506609
theorem B4225159 : Blo 2083435 4225159 := bstep (se 1 (by rfl) ⟨3168869, by rfl⟩ : syracuseStep 4225159 = 6337739) B6337739
theorem B5633545 : Blo 2083435 5633545 := bstep (se 2 (by rfl) ⟨2112579, by rfl⟩ : syracuseStep 5633545 = 4225159) B4225159
theorem B7511393 : Blo 2083435 7511393 := bstep (se 2 (by rfl) ⟨2816772, by rfl⟩ : syracuseStep 7511393 = 5633545) B5633545
theorem B5007595 : Blo 2083435 5007595 := bstep (se 1 (by rfl) ⟨3755696, by rfl⟩ : syracuseStep 5007595 = 7511393) B7511393
theorem B6676793 : Blo 2083435 6676793 := bstep (se 2 (by rfl) ⟨2503797, by rfl⟩ : syracuseStep 6676793 = 5007595) B5007595
theorem B4451195 : Blo 2083435 4451195 := bstep (se 1 (by rfl) ⟨3338396, by rfl⟩ : syracuseStep 4451195 = 6676793) B6676793
theorem B2967463 : Blo 2083435 2967463 := bstep (se 1 (by rfl) ⟨2225597, by rfl⟩ : syracuseStep 2967463 = 4451195) B4451195
theorem B3956617 : Blo 2083435 3956617 := bstep (se 2 (by rfl) ⟨1483731, by rfl⟩ : syracuseStep 3956617 = 2967463) B2967463
theorem B5275489 : Blo 2083435 5275489 := bstep (se 2 (by rfl) ⟨1978308, by rfl⟩ : syracuseStep 5275489 = 3956617) B3956617
theorem B7033985 : Blo 2083435 7033985 := bstep (se 2 (by rfl) ⟨2637744, by rfl⟩ : syracuseStep 7033985 = 5275489) B5275489
theorem B4689323 : Blo 2083435 4689323 := bstep (se 1 (by rfl) ⟨3516992, by rfl⟩ : syracuseStep 4689323 = 7033985) B7033985
theorem B3126215 : Blo 2083435 3126215 := bstep (se 1 (by rfl) ⟨2344661, by rfl⟩ : syracuseStep 3126215 = 4689323) B4689323
theorem B2084143 : Blo 2083435 2084143 := bstep (se 1 (by rfl) ⟨1563107, by rfl⟩ : syracuseStep 2084143 = 3126215) B3126215
theorem B3126221 : Blo 2083435 3126221 := bbase (se 3 (by rfl) ⟨586166, by rfl⟩ : syracuseStep 3126221 = 1172333) (by norm_num)
theorem B2084147 : Blo 2083435 2084147 := bstep (se 1 (by rfl) ⟨1563110, by rfl⟩ : syracuseStep 2084147 = 3126221) B3126221
theorem B4689341 : Blo 2083435 4689341 := bbase (se 3 (by rfl) ⟨879251, by rfl⟩ : syracuseStep 4689341 = 1758503) (by norm_num)
theorem B3126227 : Blo 2083435 3126227 := bstep (se 1 (by rfl) ⟨2344670, by rfl⟩ : syracuseStep 3126227 = 4689341) B4689341
theorem B2084151 : Blo 2083435 2084151 := bstep (se 1 (by rfl) ⟨1563113, by rfl⟩ : syracuseStep 2084151 = 3126227) B3126227
theorem B3517013 : Blo 2083435 3517013 := bbase (se 8 (by rfl) ⟨20607, by rfl⟩ : syracuseStep 3517013 = 41215) (by norm_num)
theorem B2344675 : Blo 2083435 2344675 := bstep (se 1 (by rfl) ⟨1758506, by rfl⟩ : syracuseStep 2344675 = 3517013) B3517013
theorem B3126233 : Blo 2083435 3126233 := bstep (se 2 (by rfl) ⟨1172337, by rfl⟩ : syracuseStep 3126233 = 2344675) B2344675
theorem B2084155 : Blo 2083435 2084155 := bstep (se 1 (by rfl) ⟨1563116, by rfl⟩ : syracuseStep 2084155 = 3126233) B3126233
theorem B3168893 : Blo 2083435 3168893 := bbase (se 3 (by rfl) ⟨594167, by rfl⟩ : syracuseStep 3168893 = 1188335) (by norm_num)
theorem B8450381 : Blo 2083435 8450381 := bstep (se 3 (by rfl) ⟨1584446, by rfl⟩ : syracuseStep 8450381 = 3168893) B3168893
theorem B5633587 : Blo 2083435 5633587 := bstep (se 1 (by rfl) ⟨4225190, by rfl⟩ : syracuseStep 5633587 = 8450381) B8450381
theorem B7511449 : Blo 2083435 7511449 := bstep (se 2 (by rfl) ⟨2816793, by rfl⟩ : syracuseStep 7511449 = 5633587) B5633587
theorem B10015265 : Blo 2083435 10015265 := bstep (se 2 (by rfl) ⟨3755724, by rfl⟩ : syracuseStep 10015265 = 7511449) B7511449
theorem B6676843 : Blo 2083435 6676843 := bstep (se 1 (by rfl) ⟨5007632, by rfl⟩ : syracuseStep 6676843 = 10015265) B10015265
theorem B8902457 : Blo 2083435 8902457 := bstep (se 2 (by rfl) ⟨3338421, by rfl⟩ : syracuseStep 8902457 = 6676843) B6676843
theorem B5934971 : Blo 2083435 5934971 := bstep (se 1 (by rfl) ⟨4451228, by rfl⟩ : syracuseStep 5934971 = 8902457) B8902457
theorem B15826589 : Blo 2083435 15826589 := bstep (se 3 (by rfl) ⟨2967485, by rfl⟩ : syracuseStep 15826589 = 5934971) B5934971
theorem B10551059 : Blo 2083435 10551059 := bstep (se 1 (by rfl) ⟨7913294, by rfl⟩ : syracuseStep 10551059 = 15826589) B15826589
theorem B7034039 : Blo 2083435 7034039 := bstep (se 1 (by rfl) ⟨5275529, by rfl⟩ : syracuseStep 7034039 = 10551059) B10551059
theorem B4689359 : Blo 2083435 4689359 := bstep (se 1 (by rfl) ⟨3517019, by rfl⟩ : syracuseStep 4689359 = 7034039) B7034039
theorem B3126239 : Blo 2083435 3126239 := bstep (se 1 (by rfl) ⟨2344679, by rfl⟩ : syracuseStep 3126239 = 4689359) B4689359
theorem B2084159 : Blo 2083435 2084159 := bstep (se 1 (by rfl) ⟨1563119, by rfl⟩ : syracuseStep 2084159 = 3126239) B3126239
theorem B3126245 : Blo 2083435 3126245 := bbase (se 4 (by rfl) ⟨293085, by rfl⟩ : syracuseStep 3126245 = 586171) (by norm_num)
theorem B2084163 : Blo 2083435 2084163 := bstep (se 1 (by rfl) ⟨1563122, by rfl⟩ : syracuseStep 2084163 = 3126245) B3126245
theorem B5007653 : Blo 2083435 5007653 := bbase (se 4 (by rfl) ⟨469467, by rfl⟩ : syracuseStep 5007653 = 938935) (by norm_num)
theorem B3338435 : Blo 2083435 3338435 := bstep (se 1 (by rfl) ⟨2503826, by rfl⟩ : syracuseStep 3338435 = 5007653) B5007653
theorem B8902493 : Blo 2083435 8902493 := bstep (se 3 (by rfl) ⟨1669217, by rfl⟩ : syracuseStep 8902493 = 3338435) B3338435
theorem B5934995 : Blo 2083435 5934995 := bstep (se 1 (by rfl) ⟨4451246, by rfl⟩ : syracuseStep 5934995 = 8902493) B8902493
theorem B3956663 : Blo 2083435 3956663 := bstep (se 1 (by rfl) ⟨2967497, by rfl⟩ : syracuseStep 3956663 = 5934995) B5934995
theorem B2637775 : Blo 2083435 2637775 := bstep (se 1 (by rfl) ⟨1978331, by rfl⟩ : syracuseStep 2637775 = 3956663) B3956663
theorem B3517033 : Blo 2083435 3517033 := bstep (se 2 (by rfl) ⟨1318887, by rfl⟩ : syracuseStep 3517033 = 2637775) B2637775
theorem B4689377 : Blo 2083435 4689377 := bstep (se 2 (by rfl) ⟨1758516, by rfl⟩ : syracuseStep 4689377 = 3517033) B3517033
theorem B3126251 : Blo 2083435 3126251 := bstep (se 1 (by rfl) ⟨2344688, by rfl⟩ : syracuseStep 3126251 = 4689377) B4689377
theorem B2084167 : Blo 2083435 2084167 := bstep (se 1 (by rfl) ⟨1563125, by rfl⟩ : syracuseStep 2084167 = 3126251) B3126251
theorem B2344693 : Blo 2083435 2344693 := bbase (se 5 (by rfl) ⟨109907, by rfl⟩ : syracuseStep 2344693 = 219815) (by norm_num)
theorem B3126257 : Blo 2083435 3126257 := bstep (se 2 (by rfl) ⟨1172346, by rfl⟩ : syracuseStep 3126257 = 2344693) B2344693
theorem B2084171 : Blo 2083435 2084171 := bstep (se 1 (by rfl) ⟨1563128, by rfl⟩ : syracuseStep 2084171 = 3126257) B3126257
theorem B2637785 : Blo 2083435 2637785 := bbase (se 2 (by rfl) ⟨989169, by rfl⟩ : syracuseStep 2637785 = 1978339) (by norm_num)
theorem B7034093 : Blo 2083435 7034093 := bstep (se 3 (by rfl) ⟨1318892, by rfl⟩ : syracuseStep 7034093 = 2637785) B2637785
theorem B4689395 : Blo 2083435 4689395 := bstep (se 1 (by rfl) ⟨3517046, by rfl⟩ : syracuseStep 4689395 = 7034093) B7034093
theorem B3126263 : Blo 2083435 3126263 := bstep (se 1 (by rfl) ⟨2344697, by rfl⟩ : syracuseStep 3126263 = 4689395) B4689395
theorem B2084175 : Blo 2083435 2084175 := bstep (se 1 (by rfl) ⟨1563131, by rfl⟩ : syracuseStep 2084175 = 3126263) B3126263
theorem B3126269 : Blo 2083435 3126269 := bbase (se 3 (by rfl) ⟨586175, by rfl⟩ : syracuseStep 3126269 = 1172351) (by norm_num)
theorem B2084179 : Blo 2083435 2084179 := bstep (se 1 (by rfl) ⟨1563134, by rfl⟩ : syracuseStep 2084179 = 3126269) B3126269
theorem B4689413 : Blo 2083435 4689413 := bbase (se 4 (by rfl) ⟨439632, by rfl⟩ : syracuseStep 4689413 = 879265) (by norm_num)
theorem B3126275 : Blo 2083435 3126275 := bstep (se 1 (by rfl) ⟨2344706, by rfl⟩ : syracuseStep 3126275 = 4689413) B4689413
theorem B2084183 : Blo 2083435 2084183 := bstep (se 1 (by rfl) ⟨1563137, by rfl⟩ : syracuseStep 2084183 = 3126275) B3126275
theorem B3956701 : Blo 2083435 3956701 := bbase (se 3 (by rfl) ⟨741881, by rfl⟩ : syracuseStep 3956701 = 1483763) (by norm_num)
theorem B5275601 : Blo 2083435 5275601 := bstep (se 2 (by rfl) ⟨1978350, by rfl⟩ : syracuseStep 5275601 = 3956701) B3956701
theorem B3517067 : Blo 2083435 3517067 := bstep (se 1 (by rfl) ⟨2637800, by rfl⟩ : syracuseStep 3517067 = 5275601) B5275601
theorem B2344711 : Blo 2083435 2344711 := bstep (se 1 (by rfl) ⟨1758533, by rfl⟩ : syracuseStep 2344711 = 3517067) B3517067
theorem B3126281 : Blo 2083435 3126281 := bstep (se 2 (by rfl) ⟨1172355, by rfl⟩ : syracuseStep 3126281 = 2344711) B2344711
theorem B2084187 : Blo 2083435 2084187 := bstep (se 1 (by rfl) ⟨1563140, by rfl⟩ : syracuseStep 2084187 = 3126281) B3126281
theorem B10551221 : Blo 2083435 10551221 := bbase (se 5 (by rfl) ⟨494588, by rfl⟩ : syracuseStep 10551221 = 989177) (by norm_num)
theorem B7034147 : Blo 2083435 7034147 := bstep (se 1 (by rfl) ⟨5275610, by rfl⟩ : syracuseStep 7034147 = 10551221) B10551221
theorem B4689431 : Blo 2083435 4689431 := bstep (se 1 (by rfl) ⟨3517073, by rfl⟩ : syracuseStep 4689431 = 7034147) B7034147
theorem B3126287 : Blo 2083435 3126287 := bstep (se 1 (by rfl) ⟨2344715, by rfl⟩ : syracuseStep 3126287 = 4689431) B4689431
theorem B2084191 : Blo 2083435 2084191 := bstep (se 1 (by rfl) ⟨1563143, by rfl⟩ : syracuseStep 2084191 = 3126287) B3126287
theorem B3126293 : Blo 2083435 3126293 := bbase (se 6 (by rfl) ⟨73272, by rfl⟩ : syracuseStep 3126293 = 146545) (by norm_num)
theorem B2084195 : Blo 2083435 2084195 := bstep (se 1 (by rfl) ⟨1563146, by rfl⟩ : syracuseStep 2084195 = 3126293) B3126293
theorem B3212189 : Blo 2083435 3212189 := bbase (se 3 (by rfl) ⟨602285, by rfl⟩ : syracuseStep 3212189 = 1204571) (by norm_num)
theorem B137053397 : Blo 2083435 137053397 := bstep (se 7 (by rfl) ⟨1606094, by rfl⟩ : syracuseStep 137053397 = 3212189) B3212189
theorem B91368931 : Blo 2083435 91368931 := bstep (se 1 (by rfl) ⟨68526698, by rfl⟩ : syracuseStep 91368931 = 137053397) B137053397
theorem B121825241 : Blo 2083435 121825241 := bstep (se 2 (by rfl) ⟨45684465, by rfl⟩ : syracuseStep 121825241 = 91368931) B91368931
theorem B81216827 : Blo 2083435 81216827 := bstep (se 1 (by rfl) ⟨60912620, by rfl⟩ : syracuseStep 81216827 = 121825241) B121825241
theorem B54144551 : Blo 2083435 54144551 := bstep (se 1 (by rfl) ⟨40608413, by rfl⟩ : syracuseStep 54144551 = 81216827) B81216827
theorem B36096367 : Blo 2083435 36096367 := bstep (se 1 (by rfl) ⟨27072275, by rfl⟩ : syracuseStep 36096367 = 54144551) B54144551
theorem B48128489 : Blo 2083435 48128489 := bstep (se 2 (by rfl) ⟨18048183, by rfl⟩ : syracuseStep 48128489 = 36096367) B36096367
theorem B32085659 : Blo 2083435 32085659 := bstep (se 1 (by rfl) ⟨24064244, by rfl⟩ : syracuseStep 32085659 = 48128489) B48128489
theorem B21390439 : Blo 2083435 21390439 := bstep (se 1 (by rfl) ⟨16042829, by rfl⟩ : syracuseStep 21390439 = 32085659) B32085659
theorem B28520585 : Blo 2083435 28520585 := bstep (se 2 (by rfl) ⟨10695219, by rfl⟩ : syracuseStep 28520585 = 21390439) B21390439
theorem B19013723 : Blo 2083435 19013723 := bstep (se 1 (by rfl) ⟨14260292, by rfl⟩ : syracuseStep 19013723 = 28520585) B28520585
theorem B12675815 : Blo 2083435 12675815 := bstep (se 1 (by rfl) ⟨9506861, by rfl⟩ : syracuseStep 12675815 = 19013723) B19013723
theorem B8450543 : Blo 2083435 8450543 := bstep (se 1 (by rfl) ⟨6337907, by rfl⟩ : syracuseStep 8450543 = 12675815) B12675815
theorem B5633695 : Blo 2083435 5633695 := bstep (se 1 (by rfl) ⟨4225271, by rfl⟩ : syracuseStep 5633695 = 8450543) B8450543
theorem B30046373 : Blo 2083435 30046373 := bstep (se 4 (by rfl) ⟨2816847, by rfl⟩ : syracuseStep 30046373 = 5633695) B5633695
theorem B20030915 : Blo 2083435 20030915 := bstep (se 1 (by rfl) ⟨15023186, by rfl⟩ : syracuseStep 20030915 = 30046373) B30046373
theorem B13353943 : Blo 2083435 13353943 := bstep (se 1 (by rfl) ⟨10015457, by rfl⟩ : syracuseStep 13353943 = 20030915) B20030915
theorem B17805257 : Blo 2083435 17805257 := bstep (se 2 (by rfl) ⟨6676971, by rfl⟩ : syracuseStep 17805257 = 13353943) B13353943
theorem B11870171 : Blo 2083435 11870171 := bstep (se 1 (by rfl) ⟨8902628, by rfl⟩ : syracuseStep 11870171 = 17805257) B17805257
theorem B7913447 : Blo 2083435 7913447 := bstep (se 1 (by rfl) ⟨5935085, by rfl⟩ : syracuseStep 7913447 = 11870171) B11870171
theorem B5275631 : Blo 2083435 5275631 := bstep (se 1 (by rfl) ⟨3956723, by rfl⟩ : syracuseStep 5275631 = 7913447) B7913447
theorem B3517087 : Blo 2083435 3517087 := bstep (se 1 (by rfl) ⟨2637815, by rfl⟩ : syracuseStep 3517087 = 5275631) B5275631
theorem B4689449 : Blo 2083435 4689449 := bstep (se 2 (by rfl) ⟨1758543, by rfl⟩ : syracuseStep 4689449 = 3517087) B3517087
theorem B3126299 : Blo 2083435 3126299 := bstep (se 1 (by rfl) ⟨2344724, by rfl⟩ : syracuseStep 3126299 = 4689449) B4689449
theorem B2084199 : Blo 2083435 2084199 := bstep (se 1 (by rfl) ⟨1563149, by rfl⟩ : syracuseStep 2084199 = 3126299) B3126299
theorem B2344729 : Blo 2083435 2344729 := bbase (se 2 (by rfl) ⟨879273, by rfl⟩ : syracuseStep 2344729 = 1758547) (by norm_num)
theorem B3126305 : Blo 2083435 3126305 := bstep (se 2 (by rfl) ⟨1172364, by rfl⟩ : syracuseStep 3126305 = 2344729) B2344729
theorem B2084203 : Blo 2083435 2084203 := bstep (se 1 (by rfl) ⟨1563152, by rfl⟩ : syracuseStep 2084203 = 3126305) B3126305
theorem B7913477 : Blo 2083435 7913477 := bbase (se 4 (by rfl) ⟨741888, by rfl⟩ : syracuseStep 7913477 = 1483777) (by norm_num)
theorem B5275651 : Blo 2083435 5275651 := bstep (se 1 (by rfl) ⟨3956738, by rfl⟩ : syracuseStep 5275651 = 7913477) B7913477
theorem B7034201 : Blo 2083435 7034201 := bstep (se 2 (by rfl) ⟨2637825, by rfl⟩ : syracuseStep 7034201 = 5275651) B5275651
theorem B4689467 : Blo 2083435 4689467 := bstep (se 1 (by rfl) ⟨3517100, by rfl⟩ : syracuseStep 4689467 = 7034201) B7034201
theorem B3126311 : Blo 2083435 3126311 := bstep (se 1 (by rfl) ⟨2344733, by rfl⟩ : syracuseStep 3126311 = 4689467) B4689467
theorem B2084207 : Blo 2083435 2084207 := bstep (se 1 (by rfl) ⟨1563155, by rfl⟩ : syracuseStep 2084207 = 3126311) B3126311
theorem B3126317 : Blo 2083435 3126317 := bbase (se 3 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 3126317 = 1172369) (by norm_num)
theorem B2084211 : Blo 2083435 2084211 := bstep (se 1 (by rfl) ⟨1563158, by rfl⟩ : syracuseStep 2084211 = 3126317) B3126317
theorem B4689485 : Blo 2083435 4689485 := bbase (se 3 (by rfl) ⟨879278, by rfl⟩ : syracuseStep 4689485 = 1758557) (by norm_num)
theorem B3126323 : Blo 2083435 3126323 := bstep (se 1 (by rfl) ⟨2344742, by rfl⟩ : syracuseStep 3126323 = 4689485) B4689485
theorem B2084215 : Blo 2083435 2084215 := bstep (se 1 (by rfl) ⟨1563161, by rfl⟩ : syracuseStep 2084215 = 3126323) B3126323
theorem B2637841 : Blo 2083435 2637841 := bbase (se 2 (by rfl) ⟨989190, by rfl⟩ : syracuseStep 2637841 = 1978381) (by norm_num)
theorem B3517121 : Blo 2083435 3517121 := bstep (se 2 (by rfl) ⟨1318920, by rfl⟩ : syracuseStep 3517121 = 2637841) B2637841
theorem B2344747 : Blo 2083435 2344747 := bstep (se 1 (by rfl) ⟨1758560, by rfl⟩ : syracuseStep 2344747 = 3517121) B3517121
theorem B3126329 : Blo 2083435 3126329 := bstep (se 2 (by rfl) ⟨1172373, by rfl⟩ : syracuseStep 3126329 = 2344747) B2344747
theorem B2084219 : Blo 2083435 2084219 := bstep (se 1 (by rfl) ⟨1563164, by rfl⟩ : syracuseStep 2084219 = 3126329) B3126329
theorem B4451365 : Blo 2083435 4451365 := bbase (se 4 (by rfl) ⟨417315, by rfl⟩ : syracuseStep 4451365 = 834631) (by norm_num)
theorem B23740613 : Blo 2083435 23740613 := bstep (se 4 (by rfl) ⟨2225682, by rfl⟩ : syracuseStep 23740613 = 4451365) B4451365
theorem B15827075 : Blo 2083435 15827075 := bstep (se 1 (by rfl) ⟨11870306, by rfl⟩ : syracuseStep 15827075 = 23740613) B23740613
theorem B10551383 : Blo 2083435 10551383 := bstep (se 1 (by rfl) ⟨7913537, by rfl⟩ : syracuseStep 10551383 = 15827075) B15827075
theorem B7034255 : Blo 2083435 7034255 := bstep (se 1 (by rfl) ⟨5275691, by rfl⟩ : syracuseStep 7034255 = 10551383) B10551383
theorem B4689503 : Blo 2083435 4689503 := bstep (se 1 (by rfl) ⟨3517127, by rfl⟩ : syracuseStep 4689503 = 7034255) B7034255
theorem B3126335 : Blo 2083435 3126335 := bstep (se 1 (by rfl) ⟨2344751, by rfl⟩ : syracuseStep 3126335 = 4689503) B4689503
theorem B2084223 : Blo 2083435 2084223 := bstep (se 1 (by rfl) ⟨1563167, by rfl⟩ : syracuseStep 2084223 = 3126335) B3126335
theorem B3126341 : Blo 2083435 3126341 := bbase (se 4 (by rfl) ⟨293094, by rfl⟩ : syracuseStep 3126341 = 586189) (by norm_num)
theorem B2084227 : Blo 2083435 2084227 := bstep (se 1 (by rfl) ⟨1563170, by rfl⟩ : syracuseStep 2084227 = 3126341) B3126341
theorem B3517141 : Blo 2083435 3517141 := bbase (se 7 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 3517141 = 82433) (by norm_num)
theorem B4689521 : Blo 2083435 4689521 := bstep (se 2 (by rfl) ⟨1758570, by rfl⟩ : syracuseStep 4689521 = 3517141) B3517141
theorem B3126347 : Blo 2083435 3126347 := bstep (se 1 (by rfl) ⟨2344760, by rfl⟩ : syracuseStep 3126347 = 4689521) B4689521
theorem B2084231 : Blo 2083435 2084231 := bstep (se 1 (by rfl) ⟨1563173, by rfl⟩ : syracuseStep 2084231 = 3126347) B3126347
theorem B2344765 : Blo 2083435 2344765 := bbase (se 3 (by rfl) ⟨439643, by rfl⟩ : syracuseStep 2344765 = 879287) (by norm_num)
theorem B3126353 : Blo 2083435 3126353 := bstep (se 2 (by rfl) ⟨1172382, by rfl⟩ : syracuseStep 3126353 = 2344765) B2344765
theorem B2084235 : Blo 2083435 2084235 := bstep (se 1 (by rfl) ⟨1563176, by rfl⟩ : syracuseStep 2084235 = 3126353) B3126353
theorem B7034309 : Blo 2083435 7034309 := bbase (se 4 (by rfl) ⟨659466, by rfl⟩ : syracuseStep 7034309 = 1318933) (by norm_num)
theorem B4689539 : Blo 2083435 4689539 := bstep (se 1 (by rfl) ⟨3517154, by rfl⟩ : syracuseStep 4689539 = 7034309) B7034309
theorem B3126359 : Blo 2083435 3126359 := bstep (se 1 (by rfl) ⟨2344769, by rfl⟩ : syracuseStep 3126359 = 4689539) B4689539
theorem B2084239 : Blo 2083435 2084239 := bstep (se 1 (by rfl) ⟨1563179, by rfl⟩ : syracuseStep 2084239 = 3126359) B3126359
theorem B3126365 : Blo 2083435 3126365 := bbase (se 3 (by rfl) ⟨586193, by rfl⟩ : syracuseStep 3126365 = 1172387) (by norm_num)
theorem B2084243 : Blo 2083435 2084243 := bstep (se 1 (by rfl) ⟨1563182, by rfl⟩ : syracuseStep 2084243 = 3126365) B3126365
theorem B4689557 : Blo 2083435 4689557 := bbase (se 6 (by rfl) ⟨109911, by rfl⟩ : syracuseStep 4689557 = 219823) (by norm_num)
theorem B3126371 : Blo 2083435 3126371 := bstep (se 1 (by rfl) ⟨2344778, by rfl⟩ : syracuseStep 3126371 = 4689557) B4689557
theorem B2084247 : Blo 2083435 2084247 := bstep (se 1 (by rfl) ⟨1563185, by rfl⟩ : syracuseStep 2084247 = 3126371) B3126371
theorem B2225713 : Blo 2083435 2225713 := bbase (se 2 (by rfl) ⟨834642, by rfl⟩ : syracuseStep 2225713 = 1669285) (by norm_num)
theorem B2967617 : Blo 2083435 2967617 := bstep (se 2 (by rfl) ⟨1112856, by rfl⟩ : syracuseStep 2967617 = 2225713) B2225713
theorem B7913645 : Blo 2083435 7913645 := bstep (se 3 (by rfl) ⟨1483808, by rfl⟩ : syracuseStep 7913645 = 2967617) B2967617
theorem B5275763 : Blo 2083435 5275763 := bstep (se 1 (by rfl) ⟨3956822, by rfl⟩ : syracuseStep 5275763 = 7913645) B7913645
theorem B3517175 : Blo 2083435 3517175 := bstep (se 1 (by rfl) ⟨2637881, by rfl⟩ : syracuseStep 3517175 = 5275763) B5275763
theorem B2344783 : Blo 2083435 2344783 := bstep (se 1 (by rfl) ⟨1758587, by rfl⟩ : syracuseStep 2344783 = 3517175) B3517175
theorem B3126377 : Blo 2083435 3126377 := bstep (se 2 (by rfl) ⟨1172391, by rfl⟩ : syracuseStep 3126377 = 2344783) B2344783
theorem B2084251 : Blo 2083435 2084251 := bstep (se 1 (by rfl) ⟨1563188, by rfl⟩ : syracuseStep 2084251 = 3126377) B3126377
theorem B10695509 : Blo 2083435 10695509 := bbase (se 9 (by rfl) ⟨31334, by rfl⟩ : syracuseStep 10695509 = 62669) (by norm_num)
theorem B7130339 : Blo 2083435 7130339 := bstep (se 1 (by rfl) ⟨5347754, by rfl⟩ : syracuseStep 7130339 = 10695509) B10695509
theorem B4753559 : Blo 2083435 4753559 := bstep (se 1 (by rfl) ⟨3565169, by rfl⟩ : syracuseStep 4753559 = 7130339) B7130339
theorem B3169039 : Blo 2083435 3169039 := bstep (se 1 (by rfl) ⟨2376779, by rfl⟩ : syracuseStep 3169039 = 4753559) B4753559
theorem B4225385 : Blo 2083435 4225385 := bstep (se 2 (by rfl) ⟨1584519, by rfl⟩ : syracuseStep 4225385 = 3169039) B3169039
theorem B11267693 : Blo 2083435 11267693 := bstep (se 3 (by rfl) ⟨2112692, by rfl⟩ : syracuseStep 11267693 = 4225385) B4225385
theorem B7511795 : Blo 2083435 7511795 := bstep (se 1 (by rfl) ⟨5633846, by rfl⟩ : syracuseStep 7511795 = 11267693) B11267693
theorem B5007863 : Blo 2083435 5007863 := bstep (se 1 (by rfl) ⟨3755897, by rfl⟩ : syracuseStep 5007863 = 7511795) B7511795
theorem B13354301 : Blo 2083435 13354301 := bstep (se 3 (by rfl) ⟨2503931, by rfl⟩ : syracuseStep 13354301 = 5007863) B5007863
theorem B8902867 : Blo 2083435 8902867 := bstep (se 1 (by rfl) ⟨6677150, by rfl⟩ : syracuseStep 8902867 = 13354301) B13354301
theorem B11870489 : Blo 2083435 11870489 := bstep (se 2 (by rfl) ⟨4451433, by rfl⟩ : syracuseStep 11870489 = 8902867) B8902867
theorem B7913659 : Blo 2083435 7913659 := bstep (se 1 (by rfl) ⟨5935244, by rfl⟩ : syracuseStep 7913659 = 11870489) B11870489
theorem B10551545 : Blo 2083435 10551545 := bstep (se 2 (by rfl) ⟨3956829, by rfl⟩ : syracuseStep 10551545 = 7913659) B7913659
theorem B7034363 : Blo 2083435 7034363 := bstep (se 1 (by rfl) ⟨5275772, by rfl⟩ : syracuseStep 7034363 = 10551545) B10551545
theorem B4689575 : Blo 2083435 4689575 := bstep (se 1 (by rfl) ⟨3517181, by rfl⟩ : syracuseStep 4689575 = 7034363) B7034363
theorem B3126383 : Blo 2083435 3126383 := bstep (se 1 (by rfl) ⟨2344787, by rfl⟩ : syracuseStep 3126383 = 4689575) B4689575
theorem B2084255 : Blo 2083435 2084255 := bstep (se 1 (by rfl) ⟨1563191, by rfl⟩ : syracuseStep 2084255 = 3126383) B3126383
theorem B3126389 : Blo 2083435 3126389 := bbase (se 5 (by rfl) ⟨146549, by rfl⟩ : syracuseStep 3126389 = 293099) (by norm_num)
theorem B2084259 : Blo 2083435 2084259 := bstep (se 1 (by rfl) ⟨1563194, by rfl⟩ : syracuseStep 2084259 = 3126389) B3126389
theorem B3956845 : Blo 2083435 3956845 := bbase (se 3 (by rfl) ⟨741908, by rfl⟩ : syracuseStep 3956845 = 1483817) (by norm_num)
theorem B5275793 : Blo 2083435 5275793 := bstep (se 2 (by rfl) ⟨1978422, by rfl⟩ : syracuseStep 5275793 = 3956845) B3956845
theorem B3517195 : Blo 2083435 3517195 := bstep (se 1 (by rfl) ⟨2637896, by rfl⟩ : syracuseStep 3517195 = 5275793) B5275793
theorem B4689593 : Blo 2083435 4689593 := bstep (se 2 (by rfl) ⟨1758597, by rfl⟩ : syracuseStep 4689593 = 3517195) B3517195
theorem B3126395 : Blo 2083435 3126395 := bstep (se 1 (by rfl) ⟨2344796, by rfl⟩ : syracuseStep 3126395 = 4689593) B4689593
theorem B2084263 : Blo 2083435 2084263 := bstep (se 1 (by rfl) ⟨1563197, by rfl⟩ : syracuseStep 2084263 = 3126395) B3126395
theorem B2344801 : Blo 2083435 2344801 := bbase (se 2 (by rfl) ⟨879300, by rfl⟩ : syracuseStep 2344801 = 1758601) (by norm_num)
theorem B3126401 : Blo 2083435 3126401 := bstep (se 2 (by rfl) ⟨1172400, by rfl⟩ : syracuseStep 3126401 = 2344801) B2344801
theorem B2084267 : Blo 2083435 2084267 := bstep (se 1 (by rfl) ⟨1563200, by rfl⟩ : syracuseStep 2084267 = 3126401) B3126401
theorem B5275813 : Blo 2083435 5275813 := bbase (se 4 (by rfl) ⟨494607, by rfl⟩ : syracuseStep 5275813 = 989215) (by norm_num)
theorem B7034417 : Blo 2083435 7034417 := bstep (se 2 (by rfl) ⟨2637906, by rfl⟩ : syracuseStep 7034417 = 5275813) B5275813
theorem B4689611 : Blo 2083435 4689611 := bstep (se 1 (by rfl) ⟨3517208, by rfl⟩ : syracuseStep 4689611 = 7034417) B7034417
theorem B3126407 : Blo 2083435 3126407 := bstep (se 1 (by rfl) ⟨2344805, by rfl⟩ : syracuseStep 3126407 = 4689611) B4689611
theorem B2084271 : Blo 2083435 2084271 := bstep (se 1 (by rfl) ⟨1563203, by rfl⟩ : syracuseStep 2084271 = 3126407) B3126407
theorem B3126413 : Blo 2083435 3126413 := bbase (se 3 (by rfl) ⟨586202, by rfl⟩ : syracuseStep 3126413 = 1172405) (by norm_num)
theorem B2084275 : Blo 2083435 2084275 := bstep (se 1 (by rfl) ⟨1563206, by rfl⟩ : syracuseStep 2084275 = 3126413) B3126413
theorem B4689629 : Blo 2083435 4689629 := bbase (se 3 (by rfl) ⟨879305, by rfl⟩ : syracuseStep 4689629 = 1758611) (by norm_num)
theorem B3126419 : Blo 2083435 3126419 := bstep (se 1 (by rfl) ⟨2344814, by rfl⟩ : syracuseStep 3126419 = 4689629) B4689629
theorem B2084279 : Blo 2083435 2084279 := bstep (se 1 (by rfl) ⟨1563209, by rfl⟩ : syracuseStep 2084279 = 3126419) B3126419
theorem B3517229 : Blo 2083435 3517229 := bbase (se 3 (by rfl) ⟨659480, by rfl⟩ : syracuseStep 3517229 = 1318961) (by norm_num)
theorem B2344819 : Blo 2083435 2344819 := bstep (se 1 (by rfl) ⟨1758614, by rfl⟩ : syracuseStep 2344819 = 3517229) B3517229
theorem B3126425 : Blo 2083435 3126425 := bstep (se 2 (by rfl) ⟨1172409, by rfl⟩ : syracuseStep 3126425 = 2344819) B2344819
theorem B2084283 : Blo 2083435 2084283 := bstep (se 1 (by rfl) ⟨1563212, by rfl⟩ : syracuseStep 2084283 = 3126425) B3126425
theorem B10152533 : Blo 2083435 10152533 := bbase (se 8 (by rfl) ⟨59487, by rfl⟩ : syracuseStep 10152533 = 118975) (by norm_num)
theorem B6768355 : Blo 2083435 6768355 := bstep (se 1 (by rfl) ⟨5076266, by rfl⟩ : syracuseStep 6768355 = 10152533) B10152533
theorem B9024473 : Blo 2083435 9024473 := bstep (se 2 (by rfl) ⟨3384177, by rfl⟩ : syracuseStep 9024473 = 6768355) B6768355
theorem B24065261 : Blo 2083435 24065261 := bstep (se 3 (by rfl) ⟨4512236, by rfl⟩ : syracuseStep 24065261 = 9024473) B9024473
theorem B16043507 : Blo 2083435 16043507 := bstep (se 1 (by rfl) ⟨12032630, by rfl⟩ : syracuseStep 16043507 = 24065261) B24065261
theorem B10695671 : Blo 2083435 10695671 := bstep (se 1 (by rfl) ⟨8021753, by rfl⟩ : syracuseStep 10695671 = 16043507) B16043507
theorem B7130447 : Blo 2083435 7130447 := bstep (se 1 (by rfl) ⟨5347835, by rfl⟩ : syracuseStep 7130447 = 10695671) B10695671
theorem B4753631 : Blo 2083435 4753631 := bstep (se 1 (by rfl) ⟨3565223, by rfl⟩ : syracuseStep 4753631 = 7130447) B7130447
theorem B3169087 : Blo 2083435 3169087 := bstep (se 1 (by rfl) ⟨2376815, by rfl⟩ : syracuseStep 3169087 = 4753631) B4753631
theorem B16901797 : Blo 2083435 16901797 := bstep (se 4 (by rfl) ⟨1584543, by rfl⟩ : syracuseStep 16901797 = 3169087) B3169087
theorem B22535729 : Blo 2083435 22535729 := bstep (se 2 (by rfl) ⟨8450898, by rfl⟩ : syracuseStep 22535729 = 16901797) B16901797
theorem B15023819 : Blo 2083435 15023819 := bstep (se 1 (by rfl) ⟨11267864, by rfl⟩ : syracuseStep 15023819 = 22535729) B22535729
theorem B40063517 : Blo 2083435 40063517 := bstep (se 3 (by rfl) ⟨7511909, by rfl⟩ : syracuseStep 40063517 = 15023819) B15023819
theorem B26709011 : Blo 2083435 26709011 := bstep (se 1 (by rfl) ⟨20031758, by rfl⟩ : syracuseStep 26709011 = 40063517) B40063517
theorem B17806007 : Blo 2083435 17806007 := bstep (se 1 (by rfl) ⟨13354505, by rfl⟩ : syracuseStep 17806007 = 26709011) B26709011
theorem B11870671 : Blo 2083435 11870671 := bstep (se 1 (by rfl) ⟨8903003, by rfl⟩ : syracuseStep 11870671 = 17806007) B17806007
theorem B15827561 : Blo 2083435 15827561 := bstep (se 2 (by rfl) ⟨5935335, by rfl⟩ : syracuseStep 15827561 = 11870671) B11870671
theorem B10551707 : Blo 2083435 10551707 := bstep (se 1 (by rfl) ⟨7913780, by rfl⟩ : syracuseStep 10551707 = 15827561) B15827561
theorem B7034471 : Blo 2083435 7034471 := bstep (se 1 (by rfl) ⟨5275853, by rfl⟩ : syracuseStep 7034471 = 10551707) B10551707
theorem B4689647 : Blo 2083435 4689647 := bstep (se 1 (by rfl) ⟨3517235, by rfl⟩ : syracuseStep 4689647 = 7034471) B7034471
theorem B3126431 : Blo 2083435 3126431 := bstep (se 1 (by rfl) ⟨2344823, by rfl⟩ : syracuseStep 3126431 = 4689647) B4689647
theorem B2084287 : Blo 2083435 2084287 := bstep (se 1 (by rfl) ⟨1563215, by rfl⟩ : syracuseStep 2084287 = 3126431) B3126431
theorem B3126437 : Blo 2083435 3126437 := bbase (se 4 (by rfl) ⟨293103, by rfl⟩ : syracuseStep 3126437 = 586207) (by norm_num)
theorem B2084291 : Blo 2083435 2084291 := bstep (se 1 (by rfl) ⟨1563218, by rfl⟩ : syracuseStep 2084291 = 3126437) B3126437
theorem B2637937 : Blo 2083435 2637937 := bbase (se 2 (by rfl) ⟨989226, by rfl⟩ : syracuseStep 2637937 = 1978453) (by norm_num)
theorem B3517249 : Blo 2083435 3517249 := bstep (se 2 (by rfl) ⟨1318968, by rfl⟩ : syracuseStep 3517249 = 2637937) B2637937
theorem B4689665 : Blo 2083435 4689665 := bstep (se 2 (by rfl) ⟨1758624, by rfl⟩ : syracuseStep 4689665 = 3517249) B3517249
theorem B3126443 : Blo 2083435 3126443 := bstep (se 1 (by rfl) ⟨2344832, by rfl⟩ : syracuseStep 3126443 = 4689665) B4689665
theorem B2084295 : Blo 2083435 2084295 := bstep (se 1 (by rfl) ⟨1563221, by rfl⟩ : syracuseStep 2084295 = 3126443) B3126443
theorem B2344837 : Blo 2083435 2344837 := bbase (se 4 (by rfl) ⟨219828, by rfl⟩ : syracuseStep 2344837 = 439657) (by norm_num)
theorem B3126449 : Blo 2083435 3126449 := bstep (se 2 (by rfl) ⟨1172418, by rfl⟩ : syracuseStep 3126449 = 2344837) B2344837
theorem B2084299 : Blo 2083435 2084299 := bstep (se 1 (by rfl) ⟨1563224, by rfl⟩ : syracuseStep 2084299 = 3126449) B3126449
theorem B3338653 : Blo 2083435 3338653 := bbase (se 3 (by rfl) ⟨625997, by rfl⟩ : syracuseStep 3338653 = 1251995) (by norm_num)
theorem B4451537 : Blo 2083435 4451537 := bstep (se 2 (by rfl) ⟨1669326, by rfl⟩ : syracuseStep 4451537 = 3338653) B3338653
theorem B2967691 : Blo 2083435 2967691 := bstep (se 1 (by rfl) ⟨2225768, by rfl⟩ : syracuseStep 2967691 = 4451537) B4451537
theorem B3956921 : Blo 2083435 3956921 := bstep (se 2 (by rfl) ⟨1483845, by rfl⟩ : syracuseStep 3956921 = 2967691) B2967691
theorem B2637947 : Blo 2083435 2637947 := bstep (se 1 (by rfl) ⟨1978460, by rfl⟩ : syracuseStep 2637947 = 3956921) B3956921
theorem B7034525 : Blo 2083435 7034525 := bstep (se 3 (by rfl) ⟨1318973, by rfl⟩ : syracuseStep 7034525 = 2637947) B2637947
theorem B4689683 : Blo 2083435 4689683 := bstep (se 1 (by rfl) ⟨3517262, by rfl⟩ : syracuseStep 4689683 = 7034525) B7034525
theorem B3126455 : Blo 2083435 3126455 := bstep (se 1 (by rfl) ⟨2344841, by rfl⟩ : syracuseStep 3126455 = 4689683) B4689683
theorem B2084303 : Blo 2083435 2084303 := bstep (se 1 (by rfl) ⟨1563227, by rfl⟩ : syracuseStep 2084303 = 3126455) B3126455
theorem B3126461 : Blo 2083435 3126461 := bbase (se 3 (by rfl) ⟨586211, by rfl⟩ : syracuseStep 3126461 = 1172423) (by norm_num)
theorem B2084307 : Blo 2083435 2084307 := bstep (se 1 (by rfl) ⟨1563230, by rfl⟩ : syracuseStep 2084307 = 3126461) B3126461
theorem B4689701 : Blo 2083435 4689701 := bbase (se 4 (by rfl) ⟨439659, by rfl⟩ : syracuseStep 4689701 = 879319) (by norm_num)
theorem B3126467 : Blo 2083435 3126467 := bstep (se 1 (by rfl) ⟨2344850, by rfl⟩ : syracuseStep 3126467 = 4689701) B4689701
theorem B2084311 : Blo 2083435 2084311 := bstep (se 1 (by rfl) ⟨1563233, by rfl⟩ : syracuseStep 2084311 = 3126467) B3126467
theorem B5275925 : Blo 2083435 5275925 := bbase (se 6 (by rfl) ⟨123654, by rfl⟩ : syracuseStep 5275925 = 247309) (by norm_num)
theorem B3517283 : Blo 2083435 3517283 := bstep (se 1 (by rfl) ⟨2637962, by rfl⟩ : syracuseStep 3517283 = 5275925) B5275925
theorem B2344855 : Blo 2083435 2344855 := bstep (se 1 (by rfl) ⟨1758641, by rfl⟩ : syracuseStep 2344855 = 3517283) B3517283
theorem B3126473 : Blo 2083435 3126473 := bstep (se 2 (by rfl) ⟨1172427, by rfl⟩ : syracuseStep 3126473 = 2344855) B2344855
theorem B2084315 : Blo 2083435 2084315 := bstep (se 1 (by rfl) ⟨1563236, by rfl⟩ : syracuseStep 2084315 = 3126473) B3126473
theorem B8903141 : Blo 2083435 8903141 := bbase (se 4 (by rfl) ⟨834669, by rfl⟩ : syracuseStep 8903141 = 1669339) (by norm_num)
theorem B5935427 : Blo 2083435 5935427 := bstep (se 1 (by rfl) ⟨4451570, by rfl⟩ : syracuseStep 5935427 = 8903141) B8903141
theorem B3956951 : Blo 2083435 3956951 := bstep (se 1 (by rfl) ⟨2967713, by rfl⟩ : syracuseStep 3956951 = 5935427) B5935427
theorem B10551869 : Blo 2083435 10551869 := bstep (se 3 (by rfl) ⟨1978475, by rfl⟩ : syracuseStep 10551869 = 3956951) B3956951
theorem B7034579 : Blo 2083435 7034579 := bstep (se 1 (by rfl) ⟨5275934, by rfl⟩ : syracuseStep 7034579 = 10551869) B10551869
theorem B4689719 : Blo 2083435 4689719 := bstep (se 1 (by rfl) ⟨3517289, by rfl⟩ : syracuseStep 4689719 = 7034579) B7034579
theorem B3126479 : Blo 2083435 3126479 := bstep (se 1 (by rfl) ⟨2344859, by rfl⟩ : syracuseStep 3126479 = 4689719) B4689719
theorem B2084319 : Blo 2083435 2084319 := bstep (se 1 (by rfl) ⟨1563239, by rfl⟩ : syracuseStep 2084319 = 3126479) B3126479
theorem B3126485 : Blo 2083435 3126485 := bbase (se 7 (by rfl) ⟨36638, by rfl⟩ : syracuseStep 3126485 = 73277) (by norm_num)
theorem B2084323 : Blo 2083435 2084323 := bstep (se 1 (by rfl) ⟨1563242, by rfl⟩ : syracuseStep 2084323 = 3126485) B3126485
theorem B2967725 : Blo 2083435 2967725 := bbase (se 3 (by rfl) ⟨556448, by rfl⟩ : syracuseStep 2967725 = 1112897) (by norm_num)
theorem B7913933 : Blo 2083435 7913933 := bstep (se 3 (by rfl) ⟨1483862, by rfl⟩ : syracuseStep 7913933 = 2967725) B2967725
theorem B5275955 : Blo 2083435 5275955 := bstep (se 1 (by rfl) ⟨3956966, by rfl⟩ : syracuseStep 5275955 = 7913933) B7913933
theorem B3517303 : Blo 2083435 3517303 := bstep (se 1 (by rfl) ⟨2637977, by rfl⟩ : syracuseStep 3517303 = 5275955) B5275955
theorem B4689737 : Blo 2083435 4689737 := bstep (se 2 (by rfl) ⟨1758651, by rfl⟩ : syracuseStep 4689737 = 3517303) B3517303
theorem B3126491 : Blo 2083435 3126491 := bstep (se 1 (by rfl) ⟨2344868, by rfl⟩ : syracuseStep 3126491 = 4689737) B4689737
theorem B2084327 : Blo 2083435 2084327 := bstep (se 1 (by rfl) ⟨1563245, by rfl⟩ : syracuseStep 2084327 = 3126491) B3126491
theorem B2344873 : Blo 2083435 2344873 := bbase (se 2 (by rfl) ⟨879327, by rfl⟩ : syracuseStep 2344873 = 1758655) (by norm_num)
theorem B3126497 : Blo 2083435 3126497 := bstep (se 2 (by rfl) ⟨1172436, by rfl⟩ : syracuseStep 3126497 = 2344873) B2344873
theorem B2084331 : Blo 2083435 2084331 := bstep (se 1 (by rfl) ⟨1563248, by rfl⟩ : syracuseStep 2084331 = 3126497) B3126497
theorem B4512341 : Blo 2083435 4512341 := bbase (se 8 (by rfl) ⟨26439, by rfl⟩ : syracuseStep 4512341 = 52879) (by norm_num)
theorem B3008227 : Blo 2083435 3008227 := bstep (se 1 (by rfl) ⟨2256170, by rfl⟩ : syracuseStep 3008227 = 4512341) B4512341
theorem B4010969 : Blo 2083435 4010969 := bstep (se 2 (by rfl) ⟨1504113, by rfl⟩ : syracuseStep 4010969 = 3008227) B3008227
theorem B10695917 : Blo 2083435 10695917 := bstep (se 3 (by rfl) ⟨2005484, by rfl⟩ : syracuseStep 10695917 = 4010969) B4010969
theorem B7130611 : Blo 2083435 7130611 := bstep (se 1 (by rfl) ⟨5347958, by rfl⟩ : syracuseStep 7130611 = 10695917) B10695917
theorem B38029925 : Blo 2083435 38029925 := bstep (se 4 (by rfl) ⟨3565305, by rfl⟩ : syracuseStep 38029925 = 7130611) B7130611
theorem B25353283 : Blo 2083435 25353283 := bstep (se 1 (by rfl) ⟨19014962, by rfl⟩ : syracuseStep 25353283 = 38029925) B38029925
theorem B33804377 : Blo 2083435 33804377 := bstep (se 2 (by rfl) ⟨12676641, by rfl⟩ : syracuseStep 33804377 = 25353283) B25353283
theorem B22536251 : Blo 2083435 22536251 := bstep (se 1 (by rfl) ⟨16902188, by rfl⟩ : syracuseStep 22536251 = 33804377) B33804377
theorem B15024167 : Blo 2083435 15024167 := bstep (se 1 (by rfl) ⟨11268125, by rfl⟩ : syracuseStep 15024167 = 22536251) B22536251
theorem B10016111 : Blo 2083435 10016111 := bstep (se 1 (by rfl) ⟨7512083, by rfl⟩ : syracuseStep 10016111 = 15024167) B15024167
theorem B6677407 : Blo 2083435 6677407 := bstep (se 1 (by rfl) ⟨5008055, by rfl⟩ : syracuseStep 6677407 = 10016111) B10016111
theorem B8903209 : Blo 2083435 8903209 := bstep (se 2 (by rfl) ⟨3338703, by rfl⟩ : syracuseStep 8903209 = 6677407) B6677407
theorem B11870945 : Blo 2083435 11870945 := bstep (se 2 (by rfl) ⟨4451604, by rfl⟩ : syracuseStep 11870945 = 8903209) B8903209
theorem B7913963 : Blo 2083435 7913963 := bstep (se 1 (by rfl) ⟨5935472, by rfl⟩ : syracuseStep 7913963 = 11870945) B11870945
theorem B5275975 : Blo 2083435 5275975 := bstep (se 1 (by rfl) ⟨3956981, by rfl⟩ : syracuseStep 5275975 = 7913963) B7913963
theorem B7034633 : Blo 2083435 7034633 := bstep (se 2 (by rfl) ⟨2637987, by rfl⟩ : syracuseStep 7034633 = 5275975) B5275975
theorem B4689755 : Blo 2083435 4689755 := bstep (se 1 (by rfl) ⟨3517316, by rfl⟩ : syracuseStep 4689755 = 7034633) B7034633
theorem B3126503 : Blo 2083435 3126503 := bstep (se 1 (by rfl) ⟨2344877, by rfl⟩ : syracuseStep 3126503 = 4689755) B4689755
theorem B2084335 : Blo 2083435 2084335 := bstep (se 1 (by rfl) ⟨1563251, by rfl⟩ : syracuseStep 2084335 = 3126503) B3126503
theorem B3126509 : Blo 2083435 3126509 := bbase (se 3 (by rfl) ⟨586220, by rfl⟩ : syracuseStep 3126509 = 1172441) (by norm_num)
theorem B2084339 : Blo 2083435 2084339 := bstep (se 1 (by rfl) ⟨1563254, by rfl⟩ : syracuseStep 2084339 = 3126509) B3126509
theorem B4689773 : Blo 2083435 4689773 := bbase (se 3 (by rfl) ⟨879332, by rfl⟩ : syracuseStep 4689773 = 1758665) (by norm_num)
theorem B3126515 : Blo 2083435 3126515 := bstep (se 1 (by rfl) ⟨2344886, by rfl⟩ : syracuseStep 3126515 = 4689773) B4689773
theorem B2084343 : Blo 2083435 2084343 := bstep (se 1 (by rfl) ⟨1563257, by rfl⟩ : syracuseStep 2084343 = 3126515) B3126515
theorem B3957005 : Blo 2083435 3957005 := bbase (se 3 (by rfl) ⟨741938, by rfl⟩ : syracuseStep 3957005 = 1483877) (by norm_num)
theorem B2638003 : Blo 2083435 2638003 := bstep (se 1 (by rfl) ⟨1978502, by rfl⟩ : syracuseStep 2638003 = 3957005) B3957005
theorem B3517337 : Blo 2083435 3517337 := bstep (se 2 (by rfl) ⟨1319001, by rfl⟩ : syracuseStep 3517337 = 2638003) B2638003
theorem B2344891 : Blo 2083435 2344891 := bstep (se 1 (by rfl) ⟨1758668, by rfl⟩ : syracuseStep 2344891 = 3517337) B3517337
theorem B3126521 : Blo 2083435 3126521 := bstep (se 2 (by rfl) ⟨1172445, by rfl⟩ : syracuseStep 3126521 = 2344891) B2344891
theorem B2084347 : Blo 2083435 2084347 := bstep (se 1 (by rfl) ⟨1563260, by rfl⟩ : syracuseStep 2084347 = 3126521) B3126521
theorem B20032373 : Blo 2083435 20032373 := bbase (se 5 (by rfl) ⟨939017, by rfl⟩ : syracuseStep 20032373 = 1878035) (by norm_num)
theorem B53419661 : Blo 2083435 53419661 := bstep (se 3 (by rfl) ⟨10016186, by rfl⟩ : syracuseStep 53419661 = 20032373) B20032373
theorem B35613107 : Blo 2083435 35613107 := bstep (se 1 (by rfl) ⟨26709830, by rfl⟩ : syracuseStep 35613107 = 53419661) B53419661
theorem B23742071 : Blo 2083435 23742071 := bstep (se 1 (by rfl) ⟨17806553, by rfl⟩ : syracuseStep 23742071 = 35613107) B35613107
theorem B15828047 : Blo 2083435 15828047 := bstep (se 1 (by rfl) ⟨11871035, by rfl⟩ : syracuseStep 15828047 = 23742071) B23742071
theorem B10552031 : Blo 2083435 10552031 := bstep (se 1 (by rfl) ⟨7914023, by rfl⟩ : syracuseStep 10552031 = 15828047) B15828047
theorem B7034687 : Blo 2083435 7034687 := bstep (se 1 (by rfl) ⟨5276015, by rfl⟩ : syracuseStep 7034687 = 10552031) B10552031
theorem B4689791 : Blo 2083435 4689791 := bstep (se 1 (by rfl) ⟨3517343, by rfl⟩ : syracuseStep 4689791 = 7034687) B7034687
theorem B3126527 : Blo 2083435 3126527 := bstep (se 1 (by rfl) ⟨2344895, by rfl⟩ : syracuseStep 3126527 = 4689791) B4689791
theorem B2084351 : Blo 2083435 2084351 := bstep (se 1 (by rfl) ⟨1563263, by rfl⟩ : syracuseStep 2084351 = 3126527) B3126527
theorem B3126533 : Blo 2083435 3126533 := bbase (se 4 (by rfl) ⟨293112, by rfl⟩ : syracuseStep 3126533 = 586225) (by norm_num)
theorem B2084355 : Blo 2083435 2084355 := bstep (se 1 (by rfl) ⟨1563266, by rfl⟩ : syracuseStep 2084355 = 3126533) B3126533
theorem B3517357 : Blo 2083435 3517357 := bbase (se 3 (by rfl) ⟨659504, by rfl⟩ : syracuseStep 3517357 = 1319009) (by norm_num)
theorem B4689809 : Blo 2083435 4689809 := bstep (se 2 (by rfl) ⟨1758678, by rfl⟩ : syracuseStep 4689809 = 3517357) B3517357
theorem B3126539 : Blo 2083435 3126539 := bstep (se 1 (by rfl) ⟨2344904, by rfl⟩ : syracuseStep 3126539 = 4689809) B4689809
theorem B2084359 : Blo 2083435 2084359 := bstep (se 1 (by rfl) ⟨1563269, by rfl⟩ : syracuseStep 2084359 = 3126539) B3126539
theorem B2344909 : Blo 2083435 2344909 := bbase (se 3 (by rfl) ⟨439670, by rfl⟩ : syracuseStep 2344909 = 879341) (by norm_num)
theorem B3126545 : Blo 2083435 3126545 := bstep (se 2 (by rfl) ⟨1172454, by rfl⟩ : syracuseStep 3126545 = 2344909) B2344909
theorem B2084363 : Blo 2083435 2084363 := bstep (se 1 (by rfl) ⟨1563272, by rfl⟩ : syracuseStep 2084363 = 3126545) B3126545
theorem B7034741 : Blo 2083435 7034741 := bbase (se 5 (by rfl) ⟨329753, by rfl⟩ : syracuseStep 7034741 = 659507) (by norm_num)
theorem B4689827 : Blo 2083435 4689827 := bstep (se 1 (by rfl) ⟨3517370, by rfl⟩ : syracuseStep 4689827 = 7034741) B7034741
theorem B3126551 : Blo 2083435 3126551 := bstep (se 1 (by rfl) ⟨2344913, by rfl⟩ : syracuseStep 3126551 = 4689827) B4689827
theorem B2084367 : Blo 2083435 2084367 := bstep (se 1 (by rfl) ⟨1563275, by rfl⟩ : syracuseStep 2084367 = 3126551) B3126551
theorem B3126557 : Blo 2083435 3126557 := bbase (se 3 (by rfl) ⟨586229, by rfl⟩ : syracuseStep 3126557 = 1172459) (by norm_num)
theorem B2084371 : Blo 2083435 2084371 := bstep (se 1 (by rfl) ⟨1563278, by rfl⟩ : syracuseStep 2084371 = 3126557) B3126557
theorem B4689845 : Blo 2083435 4689845 := bbase (se 5 (by rfl) ⟨219836, by rfl⟩ : syracuseStep 4689845 = 439673) (by norm_num)
theorem B3126563 : Blo 2083435 3126563 := bstep (se 1 (by rfl) ⟨2344922, by rfl⟩ : syracuseStep 3126563 = 4689845) B4689845
theorem B2084375 : Blo 2083435 2084375 := bstep (se 1 (by rfl) ⟨1563281, by rfl⟩ : syracuseStep 2084375 = 3126563) B3126563
theorem B2504081 : Blo 2083435 2504081 := bbase (se 2 (by rfl) ⟨939030, by rfl⟩ : syracuseStep 2504081 = 1878061) (by norm_num)
theorem B6677549 : Blo 2083435 6677549 := bstep (se 3 (by rfl) ⟨1252040, by rfl⟩ : syracuseStep 6677549 = 2504081) B2504081
theorem B4451699 : Blo 2083435 4451699 := bstep (se 1 (by rfl) ⟨3338774, by rfl⟩ : syracuseStep 4451699 = 6677549) B6677549
theorem B11871197 : Blo 2083435 11871197 := bstep (se 3 (by rfl) ⟨2225849, by rfl⟩ : syracuseStep 11871197 = 4451699) B4451699
theorem B7914131 : Blo 2083435 7914131 := bstep (se 1 (by rfl) ⟨5935598, by rfl⟩ : syracuseStep 7914131 = 11871197) B11871197
theorem B5276087 : Blo 2083435 5276087 := bstep (se 1 (by rfl) ⟨3957065, by rfl⟩ : syracuseStep 5276087 = 7914131) B7914131
theorem B3517391 : Blo 2083435 3517391 := bstep (se 1 (by rfl) ⟨2638043, by rfl⟩ : syracuseStep 3517391 = 5276087) B5276087
theorem B2344927 : Blo 2083435 2344927 := bstep (se 1 (by rfl) ⟨1758695, by rfl⟩ : syracuseStep 2344927 = 3517391) B3517391
theorem B3126569 : Blo 2083435 3126569 := bstep (se 2 (by rfl) ⟨1172463, by rfl⟩ : syracuseStep 3126569 = 2344927) B2344927
theorem B2084379 : Blo 2083435 2084379 := bstep (se 1 (by rfl) ⟨1563284, by rfl⟩ : syracuseStep 2084379 = 3126569) B3126569
theorem B4225645 : Blo 2083435 4225645 := bbase (se 3 (by rfl) ⟨792308, by rfl⟩ : syracuseStep 4225645 = 1584617) (by norm_num)
theorem B5634193 : Blo 2083435 5634193 := bstep (se 2 (by rfl) ⟨2112822, by rfl⟩ : syracuseStep 5634193 = 4225645) B4225645
theorem B7512257 : Blo 2083435 7512257 := bstep (se 2 (by rfl) ⟨2817096, by rfl⟩ : syracuseStep 7512257 = 5634193) B5634193
theorem B5008171 : Blo 2083435 5008171 := bstep (se 1 (by rfl) ⟨3756128, by rfl⟩ : syracuseStep 5008171 = 7512257) B7512257
theorem B6677561 : Blo 2083435 6677561 := bstep (se 2 (by rfl) ⟨2504085, by rfl⟩ : syracuseStep 6677561 = 5008171) B5008171
theorem B4451707 : Blo 2083435 4451707 := bstep (se 1 (by rfl) ⟨3338780, by rfl⟩ : syracuseStep 4451707 = 6677561) B6677561
theorem B5935609 : Blo 2083435 5935609 := bstep (se 2 (by rfl) ⟨2225853, by rfl⟩ : syracuseStep 5935609 = 4451707) B4451707
theorem B7914145 : Blo 2083435 7914145 := bstep (se 2 (by rfl) ⟨2967804, by rfl⟩ : syracuseStep 7914145 = 5935609) B5935609
theorem B10552193 : Blo 2083435 10552193 := bstep (se 2 (by rfl) ⟨3957072, by rfl⟩ : syracuseStep 10552193 = 7914145) B7914145
theorem B7034795 : Blo 2083435 7034795 := bstep (se 1 (by rfl) ⟨5276096, by rfl⟩ : syracuseStep 7034795 = 10552193) B10552193
theorem B4689863 : Blo 2083435 4689863 := bstep (se 1 (by rfl) ⟨3517397, by rfl⟩ : syracuseStep 4689863 = 7034795) B7034795
theorem B3126575 : Blo 2083435 3126575 := bstep (se 1 (by rfl) ⟨2344931, by rfl⟩ : syracuseStep 3126575 = 4689863) B4689863
theorem B2084383 : Blo 2083435 2084383 := bstep (se 1 (by rfl) ⟨1563287, by rfl⟩ : syracuseStep 2084383 = 3126575) B3126575
theorem B3126581 : Blo 2083435 3126581 := bbase (se 5 (by rfl) ⟨146558, by rfl⟩ : syracuseStep 3126581 = 293117) (by norm_num)
theorem B2084387 : Blo 2083435 2084387 := bstep (se 1 (by rfl) ⟨1563290, by rfl⟩ : syracuseStep 2084387 = 3126581) B3126581
theorem B5276117 : Blo 2083435 5276117 := bbase (se 7 (by rfl) ⟨61829, by rfl⟩ : syracuseStep 5276117 = 123659) (by norm_num)
theorem B3517411 : Blo 2083435 3517411 := bstep (se 1 (by rfl) ⟨2638058, by rfl⟩ : syracuseStep 3517411 = 5276117) B5276117
theorem B4689881 : Blo 2083435 4689881 := bstep (se 2 (by rfl) ⟨1758705, by rfl⟩ : syracuseStep 4689881 = 3517411) B3517411
theorem B3126587 : Blo 2083435 3126587 := bstep (se 1 (by rfl) ⟨2344940, by rfl⟩ : syracuseStep 3126587 = 4689881) B4689881
theorem B2084391 : Blo 2083435 2084391 := bstep (se 1 (by rfl) ⟨1563293, by rfl⟩ : syracuseStep 2084391 = 3126587) B3126587
theorem B2344945 : Blo 2083435 2344945 := bbase (se 2 (by rfl) ⟨879354, by rfl⟩ : syracuseStep 2344945 = 1758709) (by norm_num)
theorem B3126593 : Blo 2083435 3126593 := bstep (se 2 (by rfl) ⟨1172472, by rfl⟩ : syracuseStep 3126593 = 2344945) B2344945
theorem B2084395 : Blo 2083435 2084395 := bstep (se 1 (by rfl) ⟨1563296, by rfl⟩ : syracuseStep 2084395 = 3126593) B3126593
theorem B15024629 : Blo 2083435 15024629 := bbase (se 5 (by rfl) ⟨704279, by rfl⟩ : syracuseStep 15024629 = 1408559) (by norm_num)
theorem B10016419 : Blo 2083435 10016419 := bstep (se 1 (by rfl) ⟨7512314, by rfl⟩ : syracuseStep 10016419 = 15024629) B15024629
theorem B13355225 : Blo 2083435 13355225 := bstep (se 2 (by rfl) ⟨5008209, by rfl⟩ : syracuseStep 13355225 = 10016419) B10016419
theorem B8903483 : Blo 2083435 8903483 := bstep (se 1 (by rfl) ⟨6677612, by rfl⟩ : syracuseStep 8903483 = 13355225) B13355225
theorem B5935655 : Blo 2083435 5935655 := bstep (se 1 (by rfl) ⟨4451741, by rfl⟩ : syracuseStep 5935655 = 8903483) B8903483
theorem B3957103 : Blo 2083435 3957103 := bstep (se 1 (by rfl) ⟨2967827, by rfl⟩ : syracuseStep 3957103 = 5935655) B5935655
theorem B5276137 : Blo 2083435 5276137 := bstep (se 2 (by rfl) ⟨1978551, by rfl⟩ : syracuseStep 5276137 = 3957103) B3957103
theorem B7034849 : Blo 2083435 7034849 := bstep (se 2 (by rfl) ⟨2638068, by rfl⟩ : syracuseStep 7034849 = 5276137) B5276137
theorem B4689899 : Blo 2083435 4689899 := bstep (se 1 (by rfl) ⟨3517424, by rfl⟩ : syracuseStep 4689899 = 7034849) B7034849
theorem B3126599 : Blo 2083435 3126599 := bstep (se 1 (by rfl) ⟨2344949, by rfl⟩ : syracuseStep 3126599 = 4689899) B4689899
theorem B2084399 : Blo 2083435 2084399 := bstep (se 1 (by rfl) ⟨1563299, by rfl⟩ : syracuseStep 2084399 = 3126599) B3126599
theorem B3126605 : Blo 2083435 3126605 := bbase (se 3 (by rfl) ⟨586238, by rfl⟩ : syracuseStep 3126605 = 1172477) (by norm_num)
theorem B2084403 : Blo 2083435 2084403 := bstep (se 1 (by rfl) ⟨1563302, by rfl⟩ : syracuseStep 2084403 = 3126605) B3126605
theorem B4689917 : Blo 2083435 4689917 := bbase (se 3 (by rfl) ⟨879359, by rfl⟩ : syracuseStep 4689917 = 1758719) (by norm_num)
theorem B3126611 : Blo 2083435 3126611 := bstep (se 1 (by rfl) ⟨2344958, by rfl⟩ : syracuseStep 3126611 = 4689917) B4689917
theorem B2084407 : Blo 2083435 2084407 := bstep (se 1 (by rfl) ⟨1563305, by rfl⟩ : syracuseStep 2084407 = 3126611) B3126611
theorem B3517445 : Blo 2083435 3517445 := bbase (se 4 (by rfl) ⟨329760, by rfl⟩ : syracuseStep 3517445 = 659521) (by norm_num)
theorem B2344963 : Blo 2083435 2344963 := bstep (se 1 (by rfl) ⟨1758722, by rfl⟩ : syracuseStep 2344963 = 3517445) B3517445
theorem B3126617 : Blo 2083435 3126617 := bstep (se 2 (by rfl) ⟨1172481, by rfl⟩ : syracuseStep 3126617 = 2344963) B2344963
theorem B2084411 : Blo 2083435 2084411 := bstep (se 1 (by rfl) ⟨1563308, by rfl⟩ : syracuseStep 2084411 = 3126617) B3126617
theorem B15828533 : Blo 2083435 15828533 := bbase (se 5 (by rfl) ⟨741962, by rfl⟩ : syracuseStep 15828533 = 1483925) (by norm_num)
theorem B10552355 : Blo 2083435 10552355 := bstep (se 1 (by rfl) ⟨7914266, by rfl⟩ : syracuseStep 10552355 = 15828533) B15828533
theorem B7034903 : Blo 2083435 7034903 := bstep (se 1 (by rfl) ⟨5276177, by rfl⟩ : syracuseStep 7034903 = 10552355) B10552355
theorem B4689935 : Blo 2083435 4689935 := bstep (se 1 (by rfl) ⟨3517451, by rfl⟩ : syracuseStep 4689935 = 7034903) B7034903
theorem B3126623 : Blo 2083435 3126623 := bstep (se 1 (by rfl) ⟨2344967, by rfl⟩ : syracuseStep 3126623 = 4689935) B4689935
theorem B2084415 : Blo 2083435 2084415 := bstep (se 1 (by rfl) ⟨1563311, by rfl⟩ : syracuseStep 2084415 = 3126623) B3126623
theorem B3126629 : Blo 2083435 3126629 := bbase (se 4 (by rfl) ⟨293121, by rfl⟩ : syracuseStep 3126629 = 586243) (by norm_num)
theorem B2084419 : Blo 2083435 2084419 := bstep (se 1 (by rfl) ⟨1563314, by rfl⟩ : syracuseStep 2084419 = 3126629) B3126629
theorem B3957149 : Blo 2083435 3957149 := bbase (se 3 (by rfl) ⟨741965, by rfl⟩ : syracuseStep 3957149 = 1483931) (by norm_num)
theorem B2638099 : Blo 2083435 2638099 := bstep (se 1 (by rfl) ⟨1978574, by rfl⟩ : syracuseStep 2638099 = 3957149) B3957149
theorem B3517465 : Blo 2083435 3517465 := bstep (se 2 (by rfl) ⟨1319049, by rfl⟩ : syracuseStep 3517465 = 2638099) B2638099
theorem B4689953 : Blo 2083435 4689953 := bstep (se 2 (by rfl) ⟨1758732, by rfl⟩ : syracuseStep 4689953 = 3517465) B3517465
theorem B3126635 : Blo 2083435 3126635 := bstep (se 1 (by rfl) ⟨2344976, by rfl⟩ : syracuseStep 3126635 = 4689953) B4689953
theorem B2084423 : Blo 2083435 2084423 := bstep (se 1 (by rfl) ⟨1563317, by rfl⟩ : syracuseStep 2084423 = 3126635) B3126635
theorem B2344981 : Blo 2083435 2344981 := bbase (se 6 (by rfl) ⟨54960, by rfl⟩ : syracuseStep 2344981 = 109921) (by norm_num)
theorem B3126641 : Blo 2083435 3126641 := bstep (se 2 (by rfl) ⟨1172490, by rfl⟩ : syracuseStep 3126641 = 2344981) B2344981
theorem B2084427 : Blo 2083435 2084427 := bstep (se 1 (by rfl) ⟨1563320, by rfl⟩ : syracuseStep 2084427 = 3126641) B3126641
theorem B2638109 : Blo 2083435 2638109 := bbase (se 3 (by rfl) ⟨494645, by rfl⟩ : syracuseStep 2638109 = 989291) (by norm_num)
theorem B7034957 : Blo 2083435 7034957 := bstep (se 3 (by rfl) ⟨1319054, by rfl⟩ : syracuseStep 7034957 = 2638109) B2638109
theorem B4689971 : Blo 2083435 4689971 := bstep (se 1 (by rfl) ⟨3517478, by rfl⟩ : syracuseStep 4689971 = 7034957) B7034957
theorem B3126647 : Blo 2083435 3126647 := bstep (se 1 (by rfl) ⟨2344985, by rfl⟩ : syracuseStep 3126647 = 4689971) B4689971
theorem B2084431 : Blo 2083435 2084431 := bstep (se 1 (by rfl) ⟨1563323, by rfl⟩ : syracuseStep 2084431 = 3126647) B3126647
theorem B3126653 : Blo 2083435 3126653 := bbase (se 3 (by rfl) ⟨586247, by rfl⟩ : syracuseStep 3126653 = 1172495) (by norm_num)
theorem B2084435 : Blo 2083435 2084435 := bstep (se 1 (by rfl) ⟨1563326, by rfl⟩ : syracuseStep 2084435 = 3126653) B3126653
theorem B4689989 : Blo 2083435 4689989 := bbase (se 4 (by rfl) ⟨439686, by rfl⟩ : syracuseStep 4689989 = 879373) (by norm_num)
theorem B3126659 : Blo 2083435 3126659 := bstep (se 1 (by rfl) ⟨2344994, by rfl⟩ : syracuseStep 3126659 = 4689989) B4689989
theorem B2084439 : Blo 2083435 2084439 := bstep (se 1 (by rfl) ⟨1563329, by rfl⟩ : syracuseStep 2084439 = 3126659) B3126659
theorem B5935781 : Blo 2083435 5935781 := bbase (se 4 (by rfl) ⟨556479, by rfl⟩ : syracuseStep 5935781 = 1112959) (by norm_num)
theorem B3957187 : Blo 2083435 3957187 := bstep (se 1 (by rfl) ⟨2967890, by rfl⟩ : syracuseStep 3957187 = 5935781) B5935781
theorem B5276249 : Blo 2083435 5276249 := bstep (se 2 (by rfl) ⟨1978593, by rfl⟩ : syracuseStep 5276249 = 3957187) B3957187
theorem B3517499 : Blo 2083435 3517499 := bstep (se 1 (by rfl) ⟨2638124, by rfl⟩ : syracuseStep 3517499 = 5276249) B5276249
theorem B2344999 : Blo 2083435 2344999 := bstep (se 1 (by rfl) ⟨1758749, by rfl⟩ : syracuseStep 2344999 = 3517499) B3517499
theorem B3126665 : Blo 2083435 3126665 := bstep (se 2 (by rfl) ⟨1172499, by rfl⟩ : syracuseStep 3126665 = 2344999) B2344999
theorem B2084443 : Blo 2083435 2084443 := bstep (se 1 (by rfl) ⟨1563332, by rfl⟩ : syracuseStep 2084443 = 3126665) B3126665
theorem B10552517 : Blo 2083435 10552517 := bbase (se 4 (by rfl) ⟨989298, by rfl⟩ : syracuseStep 10552517 = 1978597) (by norm_num)
theorem B7035011 : Blo 2083435 7035011 := bstep (se 1 (by rfl) ⟨5276258, by rfl⟩ : syracuseStep 7035011 = 10552517) B10552517
theorem B4690007 : Blo 2083435 4690007 := bstep (se 1 (by rfl) ⟨3517505, by rfl⟩ : syracuseStep 4690007 = 7035011) B7035011
theorem B3126671 : Blo 2083435 3126671 := bstep (se 1 (by rfl) ⟨2345003, by rfl⟩ : syracuseStep 3126671 = 4690007) B4690007
theorem B2084447 : Blo 2083435 2084447 := bstep (se 1 (by rfl) ⟨1563335, by rfl⟩ : syracuseStep 2084447 = 3126671) B3126671
theorem B3126677 : Blo 2083435 3126677 := bbase (se 6 (by rfl) ⟨73281, by rfl⟩ : syracuseStep 3126677 = 146563) (by norm_num)
theorem B2084451 : Blo 2083435 2084451 := bstep (se 1 (by rfl) ⟨1563338, by rfl⟩ : syracuseStep 2084451 = 3126677) B3126677
theorem B4451861 : Blo 2083435 4451861 := bbase (se 6 (by rfl) ⟨104340, by rfl⟩ : syracuseStep 4451861 = 208681) (by norm_num)
theorem B11871629 : Blo 2083435 11871629 := bstep (se 3 (by rfl) ⟨2225930, by rfl⟩ : syracuseStep 11871629 = 4451861) B4451861
theorem B7914419 : Blo 2083435 7914419 := bstep (se 1 (by rfl) ⟨5935814, by rfl⟩ : syracuseStep 7914419 = 11871629) B11871629
theorem B5276279 : Blo 2083435 5276279 := bstep (se 1 (by rfl) ⟨3957209, by rfl⟩ : syracuseStep 5276279 = 7914419) B7914419
theorem B3517519 : Blo 2083435 3517519 := bstep (se 1 (by rfl) ⟨2638139, by rfl⟩ : syracuseStep 3517519 = 5276279) B5276279
theorem B4690025 : Blo 2083435 4690025 := bstep (se 2 (by rfl) ⟨1758759, by rfl⟩ : syracuseStep 4690025 = 3517519) B3517519
theorem B3126683 : Blo 2083435 3126683 := bstep (se 1 (by rfl) ⟨2345012, by rfl⟩ : syracuseStep 3126683 = 4690025) B4690025
theorem B2084455 : Blo 2083435 2084455 := bstep (se 1 (by rfl) ⟨1563341, by rfl⟩ : syracuseStep 2084455 = 3126683) B3126683
theorem B2345017 : Blo 2083435 2345017 := bbase (se 2 (by rfl) ⟨879381, by rfl⟩ : syracuseStep 2345017 = 1758763) (by norm_num)
theorem B3126689 : Blo 2083435 3126689 := bstep (se 2 (by rfl) ⟨1172508, by rfl⟩ : syracuseStep 3126689 = 2345017) B2345017
theorem B2084459 : Blo 2083435 2084459 := bstep (se 1 (by rfl) ⟨1563344, by rfl⟩ : syracuseStep 2084459 = 3126689) B3126689
theorem B3338909 : Blo 2083435 3338909 := bbase (se 3 (by rfl) ⟨626045, by rfl⟩ : syracuseStep 3338909 = 1252091) (by norm_num)
theorem B2225939 : Blo 2083435 2225939 := bstep (se 1 (by rfl) ⟨1669454, by rfl⟩ : syracuseStep 2225939 = 3338909) B3338909
theorem B5935837 : Blo 2083435 5935837 := bstep (se 3 (by rfl) ⟨1112969, by rfl⟩ : syracuseStep 5935837 = 2225939) B2225939
theorem B7914449 : Blo 2083435 7914449 := bstep (se 2 (by rfl) ⟨2967918, by rfl⟩ : syracuseStep 7914449 = 5935837) B5935837
theorem B5276299 : Blo 2083435 5276299 := bstep (se 1 (by rfl) ⟨3957224, by rfl⟩ : syracuseStep 5276299 = 7914449) B7914449
theorem B7035065 : Blo 2083435 7035065 := bstep (se 2 (by rfl) ⟨2638149, by rfl⟩ : syracuseStep 7035065 = 5276299) B5276299
theorem B4690043 : Blo 2083435 4690043 := bstep (se 1 (by rfl) ⟨3517532, by rfl⟩ : syracuseStep 4690043 = 7035065) B7035065
theorem B3126695 : Blo 2083435 3126695 := bstep (se 1 (by rfl) ⟨2345021, by rfl⟩ : syracuseStep 3126695 = 4690043) B4690043
theorem B2084463 : Blo 2083435 2084463 := bstep (se 1 (by rfl) ⟨1563347, by rfl⟩ : syracuseStep 2084463 = 3126695) B3126695
theorem B3126701 : Blo 2083435 3126701 := bbase (se 3 (by rfl) ⟨586256, by rfl⟩ : syracuseStep 3126701 = 1172513) (by norm_num)
theorem B2084467 : Blo 2083435 2084467 := bstep (se 1 (by rfl) ⟨1563350, by rfl⟩ : syracuseStep 2084467 = 3126701) B3126701
theorem B4690061 : Blo 2083435 4690061 := bbase (se 3 (by rfl) ⟨879386, by rfl⟩ : syracuseStep 4690061 = 1758773) (by norm_num)
theorem B3126707 : Blo 2083435 3126707 := bstep (se 1 (by rfl) ⟨2345030, by rfl⟩ : syracuseStep 3126707 = 4690061) B4690061
theorem B2084471 : Blo 2083435 2084471 := bstep (se 1 (by rfl) ⟨1563353, by rfl⟩ : syracuseStep 2084471 = 3126707) B3126707
theorem B2638165 : Blo 2083435 2638165 := bbase (se 10 (by rfl) ⟨3864, by rfl⟩ : syracuseStep 2638165 = 7729) (by norm_num)
theorem B3517553 : Blo 2083435 3517553 := bstep (se 2 (by rfl) ⟨1319082, by rfl⟩ : syracuseStep 3517553 = 2638165) B2638165
theorem B2345035 : Blo 2083435 2345035 := bstep (se 1 (by rfl) ⟨1758776, by rfl⟩ : syracuseStep 2345035 = 3517553) B3517553
theorem B3126713 : Blo 2083435 3126713 := bstep (se 2 (by rfl) ⟨1172517, by rfl⟩ : syracuseStep 3126713 = 2345035) B2345035
theorem B2084475 : Blo 2083435 2084475 := bstep (se 1 (by rfl) ⟨1563356, by rfl⟩ : syracuseStep 2084475 = 3126713) B3126713
theorem B20306933 : Blo 2083435 20306933 := bbase (se 5 (by rfl) ⟨951887, by rfl⟩ : syracuseStep 20306933 = 1903775) (by norm_num)
theorem B13537955 : Blo 2083435 13537955 := bstep (se 1 (by rfl) ⟨10153466, by rfl⟩ : syracuseStep 13537955 = 20306933) B20306933
theorem B9025303 : Blo 2083435 9025303 := bstep (se 1 (by rfl) ⟨6768977, by rfl⟩ : syracuseStep 9025303 = 13537955) B13537955
theorem B12033737 : Blo 2083435 12033737 := bstep (se 2 (by rfl) ⟨4512651, by rfl⟩ : syracuseStep 12033737 = 9025303) B9025303
theorem B8022491 : Blo 2083435 8022491 := bstep (se 1 (by rfl) ⟨6016868, by rfl⟩ : syracuseStep 8022491 = 12033737) B12033737
theorem B5348327 : Blo 2083435 5348327 := bstep (se 1 (by rfl) ⟨4011245, by rfl⟩ : syracuseStep 5348327 = 8022491) B8022491
theorem B14262205 : Blo 2083435 14262205 := bstep (se 3 (by rfl) ⟨2674163, by rfl⟩ : syracuseStep 14262205 = 5348327) B5348327
theorem B19016273 : Blo 2083435 19016273 := bstep (se 2 (by rfl) ⟨7131102, by rfl⟩ : syracuseStep 19016273 = 14262205) B14262205
theorem B12677515 : Blo 2083435 12677515 := bstep (se 1 (by rfl) ⟨9508136, by rfl⟩ : syracuseStep 12677515 = 19016273) B19016273
theorem B67613413 : Blo 2083435 67613413 := bstep (se 4 (by rfl) ⟨6338757, by rfl⟩ : syracuseStep 67613413 = 12677515) B12677515
theorem B90151217 : Blo 2083435 90151217 := bstep (se 2 (by rfl) ⟨33806706, by rfl⟩ : syracuseStep 90151217 = 67613413) B67613413
theorem B60100811 : Blo 2083435 60100811 := bstep (se 1 (by rfl) ⟨45075608, by rfl⟩ : syracuseStep 60100811 = 90151217) B90151217
theorem B40067207 : Blo 2083435 40067207 := bstep (se 1 (by rfl) ⟨30050405, by rfl⟩ : syracuseStep 40067207 = 60100811) B60100811
theorem B26711471 : Blo 2083435 26711471 := bstep (se 1 (by rfl) ⟨20033603, by rfl⟩ : syracuseStep 26711471 = 40067207) B40067207
theorem B17807647 : Blo 2083435 17807647 := bstep (se 1 (by rfl) ⟨13355735, by rfl⟩ : syracuseStep 17807647 = 26711471) B26711471
theorem B23743529 : Blo 2083435 23743529 := bstep (se 2 (by rfl) ⟨8903823, by rfl⟩ : syracuseStep 23743529 = 17807647) B17807647
theorem B15829019 : Blo 2083435 15829019 := bstep (se 1 (by rfl) ⟨11871764, by rfl⟩ : syracuseStep 15829019 = 23743529) B23743529
theorem B10552679 : Blo 2083435 10552679 := bstep (se 1 (by rfl) ⟨7914509, by rfl⟩ : syracuseStep 10552679 = 15829019) B15829019
theorem B7035119 : Blo 2083435 7035119 := bstep (se 1 (by rfl) ⟨5276339, by rfl⟩ : syracuseStep 7035119 = 10552679) B10552679
theorem B4690079 : Blo 2083435 4690079 := bstep (se 1 (by rfl) ⟨3517559, by rfl⟩ : syracuseStep 4690079 = 7035119) B7035119
theorem B3126719 : Blo 2083435 3126719 := bstep (se 1 (by rfl) ⟨2345039, by rfl⟩ : syracuseStep 3126719 = 4690079) B4690079
theorem B2084479 : Blo 2083435 2084479 := bstep (se 1 (by rfl) ⟨1563359, by rfl⟩ : syracuseStep 2084479 = 3126719) B3126719
theorem B3126725 : Blo 2083435 3126725 := bbase (se 4 (by rfl) ⟨293130, by rfl⟩ : syracuseStep 3126725 = 586261) (by norm_num)
theorem B2084483 : Blo 2083435 2084483 := bstep (se 1 (by rfl) ⟨1563362, by rfl⟩ : syracuseStep 2084483 = 3126725) B3126725
theorem B3517573 : Blo 2083435 3517573 := bbase (se 4 (by rfl) ⟨329772, by rfl⟩ : syracuseStep 3517573 = 659545) (by norm_num)
theorem B4690097 : Blo 2083435 4690097 := bstep (se 2 (by rfl) ⟨1758786, by rfl⟩ : syracuseStep 4690097 = 3517573) B3517573
theorem B3126731 : Blo 2083435 3126731 := bstep (se 1 (by rfl) ⟨2345048, by rfl⟩ : syracuseStep 3126731 = 4690097) B4690097
theorem B2084487 : Blo 2083435 2084487 := bstep (se 1 (by rfl) ⟨1563365, by rfl⟩ : syracuseStep 2084487 = 3126731) B3126731
theorem B2345053 : Blo 2083435 2345053 := bbase (se 3 (by rfl) ⟨439697, by rfl⟩ : syracuseStep 2345053 = 879395) (by norm_num)
theorem B3126737 : Blo 2083435 3126737 := bstep (se 2 (by rfl) ⟨1172526, by rfl⟩ : syracuseStep 3126737 = 2345053) B2345053
theorem B2084491 : Blo 2083435 2084491 := bstep (se 1 (by rfl) ⟨1563368, by rfl⟩ : syracuseStep 2084491 = 3126737) B3126737
theorem B7035173 : Blo 2083435 7035173 := bbase (se 4 (by rfl) ⟨659547, by rfl⟩ : syracuseStep 7035173 = 1319095) (by norm_num)
theorem B4690115 : Blo 2083435 4690115 := bstep (se 1 (by rfl) ⟨3517586, by rfl⟩ : syracuseStep 4690115 = 7035173) B7035173
theorem B3126743 : Blo 2083435 3126743 := bstep (se 1 (by rfl) ⟨2345057, by rfl⟩ : syracuseStep 3126743 = 4690115) B4690115
theorem B2084495 : Blo 2083435 2084495 := bstep (se 1 (by rfl) ⟨1563371, by rfl⟩ : syracuseStep 2084495 = 3126743) B3126743
theorem B3126749 : Blo 2083435 3126749 := bbase (se 3 (by rfl) ⟨586265, by rfl⟩ : syracuseStep 3126749 = 1172531) (by norm_num)
theorem B2084499 : Blo 2083435 2084499 := bstep (se 1 (by rfl) ⟨1563374, by rfl⟩ : syracuseStep 2084499 = 3126749) B3126749
theorem B4690133 : Blo 2083435 4690133 := bbase (se 7 (by rfl) ⟨54962, by rfl⟩ : syracuseStep 4690133 = 109925) (by norm_num)
theorem B3126755 : Blo 2083435 3126755 := bstep (se 1 (by rfl) ⟨2345066, by rfl⟩ : syracuseStep 3126755 = 4690133) B4690133
theorem B2084503 : Blo 2083435 2084503 := bstep (se 1 (by rfl) ⟨1563377, by rfl⟩ : syracuseStep 2084503 = 3126755) B3126755
theorem B2674201 : Blo 2083435 2674201 := bbase (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) (by norm_num)
theorem B3565601 : Blo 2083435 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B2377067 : Blo 2083435 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B6338845 : Blo 2083435 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B8451793 : Blo 2083435 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B11269057 : Blo 2083435 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B15025409 : Blo 2083435 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B10016939 : Blo 2083435 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B6677959 : Blo 2083435 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B8903945 : Blo 2083435 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B5935963 : Blo 2083435 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B7914617 : Blo 2083435 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B5276411 : Blo 2083435 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B3517607 : Blo 2083435 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B2345071 : Blo 2083435 2345071 := bstep (se 1 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 2345071 = 3517607) B3517607
theorem B3126761 : Blo 2083435 3126761 := bstep (se 2 (by rfl) ⟨1172535, by rfl⟩ : syracuseStep 3126761 = 2345071) B2345071
theorem B2084507 : Blo 2083435 2084507 := bstep (se 1 (by rfl) ⟨1563380, by rfl⟩ : syracuseStep 2084507 = 3126761) B3126761
theorem B9025445 : Blo 2083435 9025445 := bbase (se 4 (by rfl) ⟨846135, by rfl⟩ : syracuseStep 9025445 = 1692271) (by norm_num)
theorem B24067853 : Blo 2083435 24067853 := bstep (se 3 (by rfl) ⟨4512722, by rfl⟩ : syracuseStep 24067853 = 9025445) B9025445
theorem B16045235 : Blo 2083435 16045235 := bstep (se 1 (by rfl) ⟨12033926, by rfl⟩ : syracuseStep 16045235 = 24067853) B24067853
theorem B10696823 : Blo 2083435 10696823 := bstep (se 1 (by rfl) ⟨8022617, by rfl⟩ : syracuseStep 10696823 = 16045235) B16045235
theorem B7131215 : Blo 2083435 7131215 := bstep (se 1 (by rfl) ⟨5348411, by rfl⟩ : syracuseStep 7131215 = 10696823) B10696823
theorem B4754143 : Blo 2083435 4754143 := bstep (se 1 (by rfl) ⟨3565607, by rfl⟩ : syracuseStep 4754143 = 7131215) B7131215
theorem B6338857 : Blo 2083435 6338857 := bstep (se 2 (by rfl) ⟨2377071, by rfl⟩ : syracuseStep 6338857 = 4754143) B4754143
theorem B8451809 : Blo 2083435 8451809 := bstep (se 2 (by rfl) ⟨3169428, by rfl⟩ : syracuseStep 8451809 = 6338857) B6338857
theorem B5634539 : Blo 2083435 5634539 := bstep (se 1 (by rfl) ⟨4225904, by rfl⟩ : syracuseStep 5634539 = 8451809) B8451809
theorem B3756359 : Blo 2083435 3756359 := bstep (se 1 (by rfl) ⟨2817269, by rfl⟩ : syracuseStep 3756359 = 5634539) B5634539
theorem B2504239 : Blo 2083435 2504239 := bstep (se 1 (by rfl) ⟨1878179, by rfl⟩ : syracuseStep 2504239 = 3756359) B3756359
theorem B13355941 : Blo 2083435 13355941 := bstep (se 4 (by rfl) ⟨1252119, by rfl⟩ : syracuseStep 13355941 = 2504239) B2504239
theorem B17807921 : Blo 2083435 17807921 := bstep (se 2 (by rfl) ⟨6677970, by rfl⟩ : syracuseStep 17807921 = 13355941) B13355941
theorem B11871947 : Blo 2083435 11871947 := bstep (se 1 (by rfl) ⟨8903960, by rfl⟩ : syracuseStep 11871947 = 17807921) B17807921
theorem B7914631 : Blo 2083435 7914631 := bstep (se 1 (by rfl) ⟨5935973, by rfl⟩ : syracuseStep 7914631 = 11871947) B11871947
theorem B10552841 : Blo 2083435 10552841 := bstep (se 2 (by rfl) ⟨3957315, by rfl⟩ : syracuseStep 10552841 = 7914631) B7914631
theorem B7035227 : Blo 2083435 7035227 := bstep (se 1 (by rfl) ⟨5276420, by rfl⟩ : syracuseStep 7035227 = 10552841) B10552841
theorem B4690151 : Blo 2083435 4690151 := bstep (se 1 (by rfl) ⟨3517613, by rfl⟩ : syracuseStep 4690151 = 7035227) B7035227
theorem B3126767 : Blo 2083435 3126767 := bstep (se 1 (by rfl) ⟨2345075, by rfl⟩ : syracuseStep 3126767 = 4690151) B4690151
theorem B2084511 : Blo 2083435 2084511 := bstep (se 1 (by rfl) ⟨1563383, by rfl⟩ : syracuseStep 2084511 = 3126767) B3126767
theorem B3126773 : Blo 2083435 3126773 := bbase (se 5 (by rfl) ⟨146567, by rfl⟩ : syracuseStep 3126773 = 293135) (by norm_num)
theorem B2084515 : Blo 2083435 2084515 := bstep (se 1 (by rfl) ⟨1563386, by rfl⟩ : syracuseStep 2084515 = 3126773) B3126773
theorem B2112961 : Blo 2083435 2112961 := bbase (se 2 (by rfl) ⟨792360, by rfl⟩ : syracuseStep 2112961 = 1584721) (by norm_num)
theorem B2817281 : Blo 2083435 2817281 := bstep (se 2 (by rfl) ⟨1056480, by rfl⟩ : syracuseStep 2817281 = 2112961) B2112961
theorem B7512749 : Blo 2083435 7512749 := bstep (se 3 (by rfl) ⟨1408640, by rfl⟩ : syracuseStep 7512749 = 2817281) B2817281
theorem B5008499 : Blo 2083435 5008499 := bstep (se 1 (by rfl) ⟨3756374, by rfl⟩ : syracuseStep 5008499 = 7512749) B7512749
theorem B3338999 : Blo 2083435 3338999 := bstep (se 1 (by rfl) ⟨2504249, by rfl⟩ : syracuseStep 3338999 = 5008499) B5008499
theorem B2225999 : Blo 2083435 2225999 := bstep (se 1 (by rfl) ⟨1669499, by rfl⟩ : syracuseStep 2225999 = 3338999) B3338999
theorem B5935997 : Blo 2083435 5935997 := bstep (se 3 (by rfl) ⟨1112999, by rfl⟩ : syracuseStep 5935997 = 2225999) B2225999
theorem B3957331 : Blo 2083435 3957331 := bstep (se 1 (by rfl) ⟨2967998, by rfl⟩ : syracuseStep 3957331 = 5935997) B5935997
theorem B5276441 : Blo 2083435 5276441 := bstep (se 2 (by rfl) ⟨1978665, by rfl⟩ : syracuseStep 5276441 = 3957331) B3957331
theorem B3517627 : Blo 2083435 3517627 := bstep (se 1 (by rfl) ⟨2638220, by rfl⟩ : syracuseStep 3517627 = 5276441) B5276441
theorem B4690169 : Blo 2083435 4690169 := bstep (se 2 (by rfl) ⟨1758813, by rfl⟩ : syracuseStep 4690169 = 3517627) B3517627
theorem B3126779 : Blo 2083435 3126779 := bstep (se 1 (by rfl) ⟨2345084, by rfl⟩ : syracuseStep 3126779 = 4690169) B4690169
theorem B2084519 : Blo 2083435 2084519 := bstep (se 1 (by rfl) ⟨1563389, by rfl⟩ : syracuseStep 2084519 = 3126779) B3126779
theorem B2345089 : Blo 2083435 2345089 := bbase (se 2 (by rfl) ⟨879408, by rfl⟩ : syracuseStep 2345089 = 1758817) (by norm_num)
theorem B3126785 : Blo 2083435 3126785 := bstep (se 2 (by rfl) ⟨1172544, by rfl⟩ : syracuseStep 3126785 = 2345089) B2345089
theorem B2084523 : Blo 2083435 2084523 := bstep (se 1 (by rfl) ⟨1563392, by rfl⟩ : syracuseStep 2084523 = 3126785) B3126785
theorem B5276461 : Blo 2083435 5276461 := bbase (se 3 (by rfl) ⟨989336, by rfl⟩ : syracuseStep 5276461 = 1978673) (by norm_num)
theorem B7035281 : Blo 2083435 7035281 := bstep (se 2 (by rfl) ⟨2638230, by rfl⟩ : syracuseStep 7035281 = 5276461) B5276461
theorem B4690187 : Blo 2083435 4690187 := bstep (se 1 (by rfl) ⟨3517640, by rfl⟩ : syracuseStep 4690187 = 7035281) B7035281
theorem B3126791 : Blo 2083435 3126791 := bstep (se 1 (by rfl) ⟨2345093, by rfl⟩ : syracuseStep 3126791 = 4690187) B4690187
theorem B2084527 : Blo 2083435 2084527 := bstep (se 1 (by rfl) ⟨1563395, by rfl⟩ : syracuseStep 2084527 = 3126791) B3126791
theorem B3126797 : Blo 2083435 3126797 := bbase (se 3 (by rfl) ⟨586274, by rfl⟩ : syracuseStep 3126797 = 1172549) (by norm_num)
theorem B2084531 : Blo 2083435 2084531 := bstep (se 1 (by rfl) ⟨1563398, by rfl⟩ : syracuseStep 2084531 = 3126797) B3126797
theorem B4690205 : Blo 2083435 4690205 := bbase (se 3 (by rfl) ⟨879413, by rfl⟩ : syracuseStep 4690205 = 1758827) (by norm_num)
theorem B3126803 : Blo 2083435 3126803 := bstep (se 1 (by rfl) ⟨2345102, by rfl⟩ : syracuseStep 3126803 = 4690205) B4690205
theorem B2084535 : Blo 2083435 2084535 := bstep (se 1 (by rfl) ⟨1563401, by rfl⟩ : syracuseStep 2084535 = 3126803) B3126803
theorem B3517661 : Blo 2083435 3517661 := bbase (se 3 (by rfl) ⟨659561, by rfl⟩ : syracuseStep 3517661 = 1319123) (by norm_num)
theorem B2345107 : Blo 2083435 2345107 := bstep (se 1 (by rfl) ⟨1758830, by rfl⟩ : syracuseStep 2345107 = 3517661) B3517661
theorem B3126809 : Blo 2083435 3126809 := bstep (se 2 (by rfl) ⟨1172553, by rfl⟩ : syracuseStep 3126809 = 2345107) B2345107
theorem B2084539 : Blo 2083435 2084539 := bstep (se 1 (by rfl) ⟨1563404, by rfl⟩ : syracuseStep 2084539 = 3126809) B3126809
theorem B3169477 : Blo 2083435 3169477 := bbase (se 4 (by rfl) ⟨297138, by rfl⟩ : syracuseStep 3169477 = 594277) (by norm_num)
theorem B4225969 : Blo 2083435 4225969 := bstep (se 2 (by rfl) ⟨1584738, by rfl⟩ : syracuseStep 4225969 = 3169477) B3169477
theorem B5634625 : Blo 2083435 5634625 := bstep (se 2 (by rfl) ⟨2112984, by rfl⟩ : syracuseStep 5634625 = 4225969) B4225969
theorem B7512833 : Blo 2083435 7512833 := bstep (se 2 (by rfl) ⟨2817312, by rfl⟩ : syracuseStep 7512833 = 5634625) B5634625
theorem B5008555 : Blo 2083435 5008555 := bstep (se 1 (by rfl) ⟨3756416, by rfl⟩ : syracuseStep 5008555 = 7512833) B7512833
theorem B6678073 : Blo 2083435 6678073 := bstep (se 2 (by rfl) ⟨2504277, by rfl⟩ : syracuseStep 6678073 = 5008555) B5008555
theorem B8904097 : Blo 2083435 8904097 := bstep (se 2 (by rfl) ⟨3339036, by rfl⟩ : syracuseStep 8904097 = 6678073) B6678073
theorem B11872129 : Blo 2083435 11872129 := bstep (se 2 (by rfl) ⟨4452048, by rfl⟩ : syracuseStep 11872129 = 8904097) B8904097
theorem B15829505 : Blo 2083435 15829505 := bstep (se 2 (by rfl) ⟨5936064, by rfl⟩ : syracuseStep 15829505 = 11872129) B11872129
theorem B10553003 : Blo 2083435 10553003 := bstep (se 1 (by rfl) ⟨7914752, by rfl⟩ : syracuseStep 10553003 = 15829505) B15829505
theorem B7035335 : Blo 2083435 7035335 := bstep (se 1 (by rfl) ⟨5276501, by rfl⟩ : syracuseStep 7035335 = 10553003) B10553003
theorem B4690223 : Blo 2083435 4690223 := bstep (se 1 (by rfl) ⟨3517667, by rfl⟩ : syracuseStep 4690223 = 7035335) B7035335
theorem B3126815 : Blo 2083435 3126815 := bstep (se 1 (by rfl) ⟨2345111, by rfl⟩ : syracuseStep 3126815 = 4690223) B4690223
theorem B2084543 : Blo 2083435 2084543 := bstep (se 1 (by rfl) ⟨1563407, by rfl⟩ : syracuseStep 2084543 = 3126815) B3126815
theorem B3126821 : Blo 2083435 3126821 := bbase (se 4 (by rfl) ⟨293139, by rfl⟩ : syracuseStep 3126821 = 586279) (by norm_num)
theorem B2084547 : Blo 2083435 2084547 := bstep (se 1 (by rfl) ⟨1563410, by rfl⟩ : syracuseStep 2084547 = 3126821) B3126821
theorem B2638261 : Blo 2083435 2638261 := bbase (se 5 (by rfl) ⟨123668, by rfl⟩ : syracuseStep 2638261 = 247337) (by norm_num)
theorem B3517681 : Blo 2083435 3517681 := bstep (se 2 (by rfl) ⟨1319130, by rfl⟩ : syracuseStep 3517681 = 2638261) B2638261
theorem B4690241 : Blo 2083435 4690241 := bstep (se 2 (by rfl) ⟨1758840, by rfl⟩ : syracuseStep 4690241 = 3517681) B3517681
theorem B3126827 : Blo 2083435 3126827 := bstep (se 1 (by rfl) ⟨2345120, by rfl⟩ : syracuseStep 3126827 = 4690241) B4690241
theorem B2084551 : Blo 2083435 2084551 := bstep (se 1 (by rfl) ⟨1563413, by rfl⟩ : syracuseStep 2084551 = 3126827) B3126827
theorem B2345125 : Blo 2083435 2345125 := bbase (se 4 (by rfl) ⟨219855, by rfl⟩ : syracuseStep 2345125 = 439711) (by norm_num)
theorem B3126833 : Blo 2083435 3126833 := bstep (se 2 (by rfl) ⟨1172562, by rfl⟩ : syracuseStep 3126833 = 2345125) B2345125
theorem B2084555 : Blo 2083435 2084555 := bstep (se 1 (by rfl) ⟨1563416, by rfl⟩ : syracuseStep 2084555 = 3126833) B3126833
theorem B12678005 : Blo 2083435 12678005 := bbase (se 5 (by rfl) ⟨594281, by rfl⟩ : syracuseStep 12678005 = 1188563) (by norm_num)
theorem B33808013 : Blo 2083435 33808013 := bstep (se 3 (by rfl) ⟨6339002, by rfl⟩ : syracuseStep 33808013 = 12678005) B12678005
theorem B22538675 : Blo 2083435 22538675 := bstep (se 1 (by rfl) ⟨16904006, by rfl⟩ : syracuseStep 22538675 = 33808013) B33808013
theorem B15025783 : Blo 2083435 15025783 := bstep (se 1 (by rfl) ⟨11269337, by rfl⟩ : syracuseStep 15025783 = 22538675) B22538675
theorem B20034377 : Blo 2083435 20034377 := bstep (se 2 (by rfl) ⟨7512891, by rfl⟩ : syracuseStep 20034377 = 15025783) B15025783
theorem B13356251 : Blo 2083435 13356251 := bstep (se 1 (by rfl) ⟨10017188, by rfl⟩ : syracuseStep 13356251 = 20034377) B20034377
theorem B8904167 : Blo 2083435 8904167 := bstep (se 1 (by rfl) ⟨6678125, by rfl⟩ : syracuseStep 8904167 = 13356251) B13356251
theorem B5936111 : Blo 2083435 5936111 := bstep (se 1 (by rfl) ⟨4452083, by rfl⟩ : syracuseStep 5936111 = 8904167) B8904167
theorem B3957407 : Blo 2083435 3957407 := bstep (se 1 (by rfl) ⟨2968055, by rfl⟩ : syracuseStep 3957407 = 5936111) B5936111
theorem B2638271 : Blo 2083435 2638271 := bstep (se 1 (by rfl) ⟨1978703, by rfl⟩ : syracuseStep 2638271 = 3957407) B3957407
theorem B7035389 : Blo 2083435 7035389 := bstep (se 3 (by rfl) ⟨1319135, by rfl⟩ : syracuseStep 7035389 = 2638271) B2638271
theorem B4690259 : Blo 2083435 4690259 := bstep (se 1 (by rfl) ⟨3517694, by rfl⟩ : syracuseStep 4690259 = 7035389) B7035389
theorem B3126839 : Blo 2083435 3126839 := bstep (se 1 (by rfl) ⟨2345129, by rfl⟩ : syracuseStep 3126839 = 4690259) B4690259
theorem B2084559 : Blo 2083435 2084559 := bstep (se 1 (by rfl) ⟨1563419, by rfl⟩ : syracuseStep 2084559 = 3126839) B3126839
theorem B3126845 : Blo 2083435 3126845 := bbase (se 3 (by rfl) ⟨586283, by rfl⟩ : syracuseStep 3126845 = 1172567) (by norm_num)
theorem B2084563 : Blo 2083435 2084563 := bstep (se 1 (by rfl) ⟨1563422, by rfl⟩ : syracuseStep 2084563 = 3126845) B3126845
theorem B4690277 : Blo 2083435 4690277 := bbase (se 4 (by rfl) ⟨439713, by rfl⟩ : syracuseStep 4690277 = 879427) (by norm_num)
theorem B3126851 : Blo 2083435 3126851 := bstep (se 1 (by rfl) ⟨2345138, by rfl⟩ : syracuseStep 3126851 = 4690277) B4690277
theorem B2084567 : Blo 2083435 2084567 := bstep (se 1 (by rfl) ⟨1563425, by rfl⟩ : syracuseStep 2084567 = 3126851) B3126851
theorem B5276573 : Blo 2083435 5276573 := bbase (se 3 (by rfl) ⟨989357, by rfl⟩ : syracuseStep 5276573 = 1978715) (by norm_num)
theorem B3517715 : Blo 2083435 3517715 := bstep (se 1 (by rfl) ⟨2638286, by rfl⟩ : syracuseStep 3517715 = 5276573) B5276573
theorem B2345143 : Blo 2083435 2345143 := bstep (se 1 (by rfl) ⟨1758857, by rfl⟩ : syracuseStep 2345143 = 3517715) B3517715
theorem B3126857 : Blo 2083435 3126857 := bstep (se 2 (by rfl) ⟨1172571, by rfl⟩ : syracuseStep 3126857 = 2345143) B2345143
theorem B2084571 : Blo 2083435 2084571 := bstep (se 1 (by rfl) ⟨1563428, by rfl⟩ : syracuseStep 2084571 = 3126857) B3126857
theorem B3957437 : Blo 2083435 3957437 := bbase (se 3 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 3957437 = 1484039) (by norm_num)
theorem B10553165 : Blo 2083435 10553165 := bstep (se 3 (by rfl) ⟨1978718, by rfl⟩ : syracuseStep 10553165 = 3957437) B3957437
theorem B7035443 : Blo 2083435 7035443 := bstep (se 1 (by rfl) ⟨5276582, by rfl⟩ : syracuseStep 7035443 = 10553165) B10553165
theorem B4690295 : Blo 2083435 4690295 := bstep (se 1 (by rfl) ⟨3517721, by rfl⟩ : syracuseStep 4690295 = 7035443) B7035443
theorem B3126863 : Blo 2083435 3126863 := bstep (se 1 (by rfl) ⟨2345147, by rfl⟩ : syracuseStep 3126863 = 4690295) B4690295
theorem B2084575 : Blo 2083435 2084575 := bstep (se 1 (by rfl) ⟨1563431, by rfl⟩ : syracuseStep 2084575 = 3126863) B3126863
theorem B3126869 : Blo 2083435 3126869 := bbase (se 8 (by rfl) ⟨18321, by rfl⟩ : syracuseStep 3126869 = 36643) (by norm_num)
theorem B2084579 : Blo 2083435 2084579 := bstep (se 1 (by rfl) ⟨1563434, by rfl⟩ : syracuseStep 2084579 = 3126869) B3126869
theorem B3339101 : Blo 2083435 3339101 := bbase (se 3 (by rfl) ⟨626081, by rfl⟩ : syracuseStep 3339101 = 1252163) (by norm_num)
theorem B8904269 : Blo 2083435 8904269 := bstep (se 3 (by rfl) ⟨1669550, by rfl⟩ : syracuseStep 8904269 = 3339101) B3339101
theorem B5936179 : Blo 2083435 5936179 := bstep (se 1 (by rfl) ⟨4452134, by rfl⟩ : syracuseStep 5936179 = 8904269) B8904269
theorem B7914905 : Blo 2083435 7914905 := bstep (se 2 (by rfl) ⟨2968089, by rfl⟩ : syracuseStep 7914905 = 5936179) B5936179
theorem B5276603 : Blo 2083435 5276603 := bstep (se 1 (by rfl) ⟨3957452, by rfl⟩ : syracuseStep 5276603 = 7914905) B7914905
theorem B3517735 : Blo 2083435 3517735 := bstep (se 1 (by rfl) ⟨2638301, by rfl⟩ : syracuseStep 3517735 = 5276603) B5276603
theorem B4690313 : Blo 2083435 4690313 := bstep (se 2 (by rfl) ⟨1758867, by rfl⟩ : syracuseStep 4690313 = 3517735) B3517735
theorem B3126875 : Blo 2083435 3126875 := bstep (se 1 (by rfl) ⟨2345156, by rfl⟩ : syracuseStep 3126875 = 4690313) B4690313
theorem B2084583 : Blo 2083435 2084583 := bstep (se 1 (by rfl) ⟨1563437, by rfl⟩ : syracuseStep 2084583 = 3126875) B3126875
theorem B2345161 : Blo 2083435 2345161 := bbase (se 2 (by rfl) ⟨879435, by rfl⟩ : syracuseStep 2345161 = 1758871) (by norm_num)
theorem B3126881 : Blo 2083435 3126881 := bstep (se 2 (by rfl) ⟨1172580, by rfl⟩ : syracuseStep 3126881 = 2345161) B2345161
theorem B2084587 : Blo 2083435 2084587 := bstep (se 1 (by rfl) ⟨1563440, by rfl⟩ : syracuseStep 2084587 = 3126881) B3126881
theorem B8452133 : Blo 2083435 8452133 := bbase (se 4 (by rfl) ⟨792387, by rfl⟩ : syracuseStep 8452133 = 1584775) (by norm_num)
theorem B5634755 : Blo 2083435 5634755 := bstep (se 1 (by rfl) ⟨4226066, by rfl⟩ : syracuseStep 5634755 = 8452133) B8452133
theorem B3756503 : Blo 2083435 3756503 := bstep (se 1 (by rfl) ⟨2817377, by rfl⟩ : syracuseStep 3756503 = 5634755) B5634755
theorem B10017341 : Blo 2083435 10017341 := bstep (se 3 (by rfl) ⟨1878251, by rfl⟩ : syracuseStep 10017341 = 3756503) B3756503
theorem B6678227 : Blo 2083435 6678227 := bstep (se 1 (by rfl) ⟨5008670, by rfl⟩ : syracuseStep 6678227 = 10017341) B10017341
theorem B17808605 : Blo 2083435 17808605 := bstep (se 3 (by rfl) ⟨3339113, by rfl⟩ : syracuseStep 17808605 = 6678227) B6678227
theorem B11872403 : Blo 2083435 11872403 := bstep (se 1 (by rfl) ⟨8904302, by rfl⟩ : syracuseStep 11872403 = 17808605) B17808605
theorem B7914935 : Blo 2083435 7914935 := bstep (se 1 (by rfl) ⟨5936201, by rfl⟩ : syracuseStep 7914935 = 11872403) B11872403
theorem B5276623 : Blo 2083435 5276623 := bstep (se 1 (by rfl) ⟨3957467, by rfl⟩ : syracuseStep 5276623 = 7914935) B7914935
theorem B7035497 : Blo 2083435 7035497 := bstep (se 2 (by rfl) ⟨2638311, by rfl⟩ : syracuseStep 7035497 = 5276623) B5276623
theorem B4690331 : Blo 2083435 4690331 := bstep (se 1 (by rfl) ⟨3517748, by rfl⟩ : syracuseStep 4690331 = 7035497) B7035497
theorem B3126887 : Blo 2083435 3126887 := bstep (se 1 (by rfl) ⟨2345165, by rfl⟩ : syracuseStep 3126887 = 4690331) B4690331
theorem B2084591 : Blo 2083435 2084591 := bstep (se 1 (by rfl) ⟨1563443, by rfl⟩ : syracuseStep 2084591 = 3126887) B3126887
theorem B3126893 : Blo 2083435 3126893 := bbase (se 3 (by rfl) ⟨586292, by rfl⟩ : syracuseStep 3126893 = 1172585) (by norm_num)
theorem B2084595 : Blo 2083435 2084595 := bstep (se 1 (by rfl) ⟨1563446, by rfl⟩ : syracuseStep 2084595 = 3126893) B3126893
theorem B4690349 : Blo 2083435 4690349 := bbase (se 3 (by rfl) ⟨879440, by rfl⟩ : syracuseStep 4690349 = 1758881) (by norm_num)
theorem B3126899 : Blo 2083435 3126899 := bstep (se 1 (by rfl) ⟨2345174, by rfl⟩ : syracuseStep 3126899 = 4690349) B4690349
theorem B2084599 : Blo 2083435 2084599 := bstep (se 1 (by rfl) ⟨1563449, by rfl⟩ : syracuseStep 2084599 = 3126899) B3126899
theorem B2226089 : Blo 2083435 2226089 := bbase (se 2 (by rfl) ⟨834783, by rfl⟩ : syracuseStep 2226089 = 1669567) (by norm_num)
theorem B5936237 : Blo 2083435 5936237 := bstep (se 3 (by rfl) ⟨1113044, by rfl⟩ : syracuseStep 5936237 = 2226089) B2226089
theorem B3957491 : Blo 2083435 3957491 := bstep (se 1 (by rfl) ⟨2968118, by rfl⟩ : syracuseStep 3957491 = 5936237) B5936237
theorem B2638327 : Blo 2083435 2638327 := bstep (se 1 (by rfl) ⟨1978745, by rfl⟩ : syracuseStep 2638327 = 3957491) B3957491
theorem B3517769 : Blo 2083435 3517769 := bstep (se 2 (by rfl) ⟨1319163, by rfl⟩ : syracuseStep 3517769 = 2638327) B2638327
theorem B2345179 : Blo 2083435 2345179 := bstep (se 1 (by rfl) ⟨1758884, by rfl⟩ : syracuseStep 2345179 = 3517769) B3517769
theorem B3126905 : Blo 2083435 3126905 := bstep (se 2 (by rfl) ⟨1172589, by rfl⟩ : syracuseStep 3126905 = 2345179) B2345179
theorem B2084603 : Blo 2083435 2084603 := bstep (se 1 (by rfl) ⟨1563452, by rfl⟩ : syracuseStep 2084603 = 3126905) B3126905
theorem B2113049 : Blo 2083435 2113049 := bbase (se 2 (by rfl) ⟨792393, by rfl⟩ : syracuseStep 2113049 = 1584787) (by norm_num)
theorem B5634797 : Blo 2083435 5634797 := bstep (se 3 (by rfl) ⟨1056524, by rfl⟩ : syracuseStep 5634797 = 2113049) B2113049
theorem B60104501 : Blo 2083435 60104501 := bstep (se 5 (by rfl) ⟨2817398, by rfl⟩ : syracuseStep 60104501 = 5634797) B5634797
theorem B40069667 : Blo 2083435 40069667 := bstep (se 1 (by rfl) ⟨30052250, by rfl⟩ : syracuseStep 40069667 = 60104501) B60104501
theorem B26713111 : Blo 2083435 26713111 := bstep (se 1 (by rfl) ⟨20034833, by rfl⟩ : syracuseStep 26713111 = 40069667) B40069667
theorem B35617481 : Blo 2083435 35617481 := bstep (se 2 (by rfl) ⟨13356555, by rfl⟩ : syracuseStep 35617481 = 26713111) B26713111
theorem B23744987 : Blo 2083435 23744987 := bstep (se 1 (by rfl) ⟨17808740, by rfl⟩ : syracuseStep 23744987 = 35617481) B35617481
theorem B15829991 : Blo 2083435 15829991 := bstep (se 1 (by rfl) ⟨11872493, by rfl⟩ : syracuseStep 15829991 = 23744987) B23744987
theorem B10553327 : Blo 2083435 10553327 := bstep (se 1 (by rfl) ⟨7914995, by rfl⟩ : syracuseStep 10553327 = 15829991) B15829991
theorem B7035551 : Blo 2083435 7035551 := bstep (se 1 (by rfl) ⟨5276663, by rfl⟩ : syracuseStep 7035551 = 10553327) B10553327
theorem B4690367 : Blo 2083435 4690367 := bstep (se 1 (by rfl) ⟨3517775, by rfl⟩ : syracuseStep 4690367 = 7035551) B7035551
theorem B3126911 : Blo 2083435 3126911 := bstep (se 1 (by rfl) ⟨2345183, by rfl⟩ : syracuseStep 3126911 = 4690367) B4690367
theorem B2084607 : Blo 2083435 2084607 := bstep (se 1 (by rfl) ⟨1563455, by rfl⟩ : syracuseStep 2084607 = 3126911) B3126911
theorem B3126917 : Blo 2083435 3126917 := bbase (se 4 (by rfl) ⟨293148, by rfl⟩ : syracuseStep 3126917 = 586297) (by norm_num)
theorem B2084611 : Blo 2083435 2084611 := bstep (se 1 (by rfl) ⟨1563458, by rfl⟩ : syracuseStep 2084611 = 3126917) B3126917
theorem B3517789 : Blo 2083435 3517789 := bbase (se 3 (by rfl) ⟨659585, by rfl⟩ : syracuseStep 3517789 = 1319171) (by norm_num)
theorem B4690385 : Blo 2083435 4690385 := bstep (se 2 (by rfl) ⟨1758894, by rfl⟩ : syracuseStep 4690385 = 3517789) B3517789
theorem B3126923 : Blo 2083435 3126923 := bstep (se 1 (by rfl) ⟨2345192, by rfl⟩ : syracuseStep 3126923 = 4690385) B4690385
theorem B2084615 : Blo 2083435 2084615 := bstep (se 1 (by rfl) ⟨1563461, by rfl⟩ : syracuseStep 2084615 = 3126923) B3126923
theorem B2345197 : Blo 2083435 2345197 := bbase (se 3 (by rfl) ⟨439724, by rfl⟩ : syracuseStep 2345197 = 879449) (by norm_num)
theorem B3126929 : Blo 2083435 3126929 := bstep (se 2 (by rfl) ⟨1172598, by rfl⟩ : syracuseStep 3126929 = 2345197) B2345197
theorem B2084619 : Blo 2083435 2084619 := bstep (se 1 (by rfl) ⟨1563464, by rfl⟩ : syracuseStep 2084619 = 3126929) B3126929
theorem B7035605 : Blo 2083435 7035605 := bbase (se 7 (by rfl) ⟨82448, by rfl⟩ : syracuseStep 7035605 = 164897) (by norm_num)
theorem B4690403 : Blo 2083435 4690403 := bstep (se 1 (by rfl) ⟨3517802, by rfl⟩ : syracuseStep 4690403 = 7035605) B7035605
theorem B3126935 : Blo 2083435 3126935 := bstep (se 1 (by rfl) ⟨2345201, by rfl⟩ : syracuseStep 3126935 = 4690403) B4690403
theorem B2084623 : Blo 2083435 2084623 := bstep (se 1 (by rfl) ⟨1563467, by rfl⟩ : syracuseStep 2084623 = 3126935) B3126935
theorem B3126941 : Blo 2083435 3126941 := bbase (se 3 (by rfl) ⟨586301, by rfl⟩ : syracuseStep 3126941 = 1172603) (by norm_num)
theorem B2084627 : Blo 2083435 2084627 := bstep (se 1 (by rfl) ⟨1563470, by rfl⟩ : syracuseStep 2084627 = 3126941) B3126941
theorem B4690421 : Blo 2083435 4690421 := bbase (se 5 (by rfl) ⟨219863, by rfl⟩ : syracuseStep 4690421 = 439727) (by norm_num)
theorem B3126947 : Blo 2083435 3126947 := bstep (se 1 (by rfl) ⟨2345210, by rfl⟩ : syracuseStep 3126947 = 4690421) B4690421
theorem B2084631 : Blo 2083435 2084631 := bstep (se 1 (by rfl) ⟨1563473, by rfl⟩ : syracuseStep 2084631 = 3126947) B3126947
theorem B2817437 : Blo 2083435 2817437 := bbase (se 3 (by rfl) ⟨528269, by rfl⟩ : syracuseStep 2817437 = 1056539) (by norm_num)
theorem B7513165 : Blo 2083435 7513165 := bstep (se 3 (by rfl) ⟨1408718, by rfl⟩ : syracuseStep 7513165 = 2817437) B2817437
theorem B40070213 : Blo 2083435 40070213 := bstep (se 4 (by rfl) ⟨3756582, by rfl⟩ : syracuseStep 40070213 = 7513165) B7513165
theorem B26713475 : Blo 2083435 26713475 := bstep (se 1 (by rfl) ⟨20035106, by rfl⟩ : syracuseStep 26713475 = 40070213) B40070213
theorem B17808983 : Blo 2083435 17808983 := bstep (se 1 (by rfl) ⟨13356737, by rfl⟩ : syracuseStep 17808983 = 26713475) B26713475
theorem B11872655 : Blo 2083435 11872655 := bstep (se 1 (by rfl) ⟨8904491, by rfl⟩ : syracuseStep 11872655 = 17808983) B17808983
theorem B7915103 : Blo 2083435 7915103 := bstep (se 1 (by rfl) ⟨5936327, by rfl⟩ : syracuseStep 7915103 = 11872655) B11872655
theorem B5276735 : Blo 2083435 5276735 := bstep (se 1 (by rfl) ⟨3957551, by rfl⟩ : syracuseStep 5276735 = 7915103) B7915103
theorem B3517823 : Blo 2083435 3517823 := bstep (se 1 (by rfl) ⟨2638367, by rfl⟩ : syracuseStep 3517823 = 5276735) B5276735
theorem B2345215 : Blo 2083435 2345215 := bstep (se 1 (by rfl) ⟨1758911, by rfl⟩ : syracuseStep 2345215 = 3517823) B3517823
theorem B3126953 : Blo 2083435 3126953 := bstep (se 2 (by rfl) ⟨1172607, by rfl⟩ : syracuseStep 3126953 = 2345215) B2345215
theorem B2084635 : Blo 2083435 2084635 := bstep (se 1 (by rfl) ⟨1563476, by rfl⟩ : syracuseStep 2084635 = 3126953) B3126953
theorem B4226165 : Blo 2083435 4226165 := bbase (se 5 (by rfl) ⟨198101, by rfl⟩ : syracuseStep 4226165 = 396203) (by norm_num)
theorem B2817443 : Blo 2083435 2817443 := bstep (se 1 (by rfl) ⟨2113082, by rfl⟩ : syracuseStep 2817443 = 4226165) B4226165
theorem B7513181 : Blo 2083435 7513181 := bstep (se 3 (by rfl) ⟨1408721, by rfl⟩ : syracuseStep 7513181 = 2817443) B2817443
theorem B5008787 : Blo 2083435 5008787 := bstep (se 1 (by rfl) ⟨3756590, by rfl⟩ : syracuseStep 5008787 = 7513181) B7513181
theorem B3339191 : Blo 2083435 3339191 := bstep (se 1 (by rfl) ⟨2504393, by rfl⟩ : syracuseStep 3339191 = 5008787) B5008787
theorem B2226127 : Blo 2083435 2226127 := bstep (se 1 (by rfl) ⟨1669595, by rfl⟩ : syracuseStep 2226127 = 3339191) B3339191
theorem B2968169 : Blo 2083435 2968169 := bstep (se 2 (by rfl) ⟨1113063, by rfl⟩ : syracuseStep 2968169 = 2226127) B2226127
theorem B7915117 : Blo 2083435 7915117 := bstep (se 3 (by rfl) ⟨1484084, by rfl⟩ : syracuseStep 7915117 = 2968169) B2968169
theorem B10553489 : Blo 2083435 10553489 := bstep (se 2 (by rfl) ⟨3957558, by rfl⟩ : syracuseStep 10553489 = 7915117) B7915117
theorem B7035659 : Blo 2083435 7035659 := bstep (se 1 (by rfl) ⟨5276744, by rfl⟩ : syracuseStep 7035659 = 10553489) B10553489
theorem B4690439 : Blo 2083435 4690439 := bstep (se 1 (by rfl) ⟨3517829, by rfl⟩ : syracuseStep 4690439 = 7035659) B7035659
theorem B3126959 : Blo 2083435 3126959 := bstep (se 1 (by rfl) ⟨2345219, by rfl⟩ : syracuseStep 3126959 = 4690439) B4690439
theorem B2084639 : Blo 2083435 2084639 := bstep (se 1 (by rfl) ⟨1563479, by rfl⟩ : syracuseStep 2084639 = 3126959) B3126959
theorem B3126965 : Blo 2083435 3126965 := bbase (se 5 (by rfl) ⟨146576, by rfl⟩ : syracuseStep 3126965 = 293153) (by norm_num)
theorem B2084643 : Blo 2083435 2084643 := bstep (se 1 (by rfl) ⟨1563482, by rfl⟩ : syracuseStep 2084643 = 3126965) B3126965
theorem B5276765 : Blo 2083435 5276765 := bbase (se 3 (by rfl) ⟨989393, by rfl⟩ : syracuseStep 5276765 = 1978787) (by norm_num)
theorem B3517843 : Blo 2083435 3517843 := bstep (se 1 (by rfl) ⟨2638382, by rfl⟩ : syracuseStep 3517843 = 5276765) B5276765
theorem B4690457 : Blo 2083435 4690457 := bstep (se 2 (by rfl) ⟨1758921, by rfl⟩ : syracuseStep 4690457 = 3517843) B3517843
theorem B3126971 : Blo 2083435 3126971 := bstep (se 1 (by rfl) ⟨2345228, by rfl⟩ : syracuseStep 3126971 = 4690457) B4690457
theorem B2084647 : Blo 2083435 2084647 := bstep (se 1 (by rfl) ⟨1563485, by rfl⟩ : syracuseStep 2084647 = 3126971) B3126971
theorem B2345233 : Blo 2083435 2345233 := bbase (se 2 (by rfl) ⟨879462, by rfl⟩ : syracuseStep 2345233 = 1758925) (by norm_num)
theorem B3126977 : Blo 2083435 3126977 := bstep (se 2 (by rfl) ⟨1172616, by rfl⟩ : syracuseStep 3126977 = 2345233) B2345233
theorem B2084651 : Blo 2083435 2084651 := bstep (se 1 (by rfl) ⟨1563488, by rfl⟩ : syracuseStep 2084651 = 3126977) B3126977
theorem B3957589 : Blo 2083435 3957589 := bbase (se 9 (by rfl) ⟨11594, by rfl⟩ : syracuseStep 3957589 = 23189) (by norm_num)
theorem B5276785 : Blo 2083435 5276785 := bstep (se 2 (by rfl) ⟨1978794, by rfl⟩ : syracuseStep 5276785 = 3957589) B3957589
theorem B7035713 : Blo 2083435 7035713 := bstep (se 2 (by rfl) ⟨2638392, by rfl⟩ : syracuseStep 7035713 = 5276785) B5276785
theorem B4690475 : Blo 2083435 4690475 := bstep (se 1 (by rfl) ⟨3517856, by rfl⟩ : syracuseStep 4690475 = 7035713) B7035713
theorem B3126983 : Blo 2083435 3126983 := bstep (se 1 (by rfl) ⟨2345237, by rfl⟩ : syracuseStep 3126983 = 4690475) B4690475
theorem B2084655 : Blo 2083435 2084655 := bstep (se 1 (by rfl) ⟨1563491, by rfl⟩ : syracuseStep 2084655 = 3126983) B3126983
theorem B3126989 : Blo 2083435 3126989 := bbase (se 3 (by rfl) ⟨586310, by rfl⟩ : syracuseStep 3126989 = 1172621) (by norm_num)
theorem B2084659 : Blo 2083435 2084659 := bstep (se 1 (by rfl) ⟨1563494, by rfl⟩ : syracuseStep 2084659 = 3126989) B3126989
theorem B4690493 : Blo 2083435 4690493 := bbase (se 3 (by rfl) ⟨879467, by rfl⟩ : syracuseStep 4690493 = 1758935) (by norm_num)
theorem B3126995 : Blo 2083435 3126995 := bstep (se 1 (by rfl) ⟨2345246, by rfl⟩ : syracuseStep 3126995 = 4690493) B4690493
theorem B2084663 : Blo 2083435 2084663 := bstep (se 1 (by rfl) ⟨1563497, by rfl⟩ : syracuseStep 2084663 = 3126995) B3126995
theorem B3517877 : Blo 2083435 3517877 := bbase (se 5 (by rfl) ⟨164900, by rfl⟩ : syracuseStep 3517877 = 329801) (by norm_num)
theorem B2345251 : Blo 2083435 2345251 := bstep (se 1 (by rfl) ⟨1758938, by rfl⟩ : syracuseStep 2345251 = 3517877) B3517877
theorem B3127001 : Blo 2083435 3127001 := bstep (se 2 (by rfl) ⟨1172625, by rfl⟩ : syracuseStep 3127001 = 2345251) B2345251
theorem B2084667 : Blo 2083435 2084667 := bstep (se 1 (by rfl) ⟨1563500, by rfl⟩ : syracuseStep 2084667 = 3127001) B3127001
theorem B2226161 : Blo 2083435 2226161 := bbase (se 2 (by rfl) ⟨834810, by rfl⟩ : syracuseStep 2226161 = 1669621) (by norm_num)
theorem B5936429 : Blo 2083435 5936429 := bstep (se 3 (by rfl) ⟨1113080, by rfl⟩ : syracuseStep 5936429 = 2226161) B2226161
theorem B15830477 : Blo 2083435 15830477 := bstep (se 3 (by rfl) ⟨2968214, by rfl⟩ : syracuseStep 15830477 = 5936429) B5936429
theorem B10553651 : Blo 2083435 10553651 := bstep (se 1 (by rfl) ⟨7915238, by rfl⟩ : syracuseStep 10553651 = 15830477) B15830477
theorem B7035767 : Blo 2083435 7035767 := bstep (se 1 (by rfl) ⟨5276825, by rfl⟩ : syracuseStep 7035767 = 10553651) B10553651
theorem B4690511 : Blo 2083435 4690511 := bstep (se 1 (by rfl) ⟨3517883, by rfl⟩ : syracuseStep 4690511 = 7035767) B7035767
theorem B3127007 : Blo 2083435 3127007 := bstep (se 1 (by rfl) ⟨2345255, by rfl⟩ : syracuseStep 3127007 = 4690511) B4690511
theorem B2084671 : Blo 2083435 2084671 := bstep (se 1 (by rfl) ⟨1563503, by rfl⟩ : syracuseStep 2084671 = 3127007) B3127007
theorem B3127013 : Blo 2083435 3127013 := bbase (se 4 (by rfl) ⟨293157, by rfl⟩ : syracuseStep 3127013 = 586315) (by norm_num)
theorem B2084675 : Blo 2083435 2084675 := bstep (se 1 (by rfl) ⟨1563506, by rfl⟩ : syracuseStep 2084675 = 3127013) B3127013
theorem B5936453 : Blo 2083435 5936453 := bbase (se 4 (by rfl) ⟨556542, by rfl⟩ : syracuseStep 5936453 = 1113085) (by norm_num)
theorem B3957635 : Blo 2083435 3957635 := bstep (se 1 (by rfl) ⟨2968226, by rfl⟩ : syracuseStep 3957635 = 5936453) B5936453
theorem B2638423 : Blo 2083435 2638423 := bstep (se 1 (by rfl) ⟨1978817, by rfl⟩ : syracuseStep 2638423 = 3957635) B3957635
theorem B3517897 : Blo 2083435 3517897 := bstep (se 2 (by rfl) ⟨1319211, by rfl⟩ : syracuseStep 3517897 = 2638423) B2638423
theorem B4690529 : Blo 2083435 4690529 := bstep (se 2 (by rfl) ⟨1758948, by rfl⟩ : syracuseStep 4690529 = 3517897) B3517897
theorem B3127019 : Blo 2083435 3127019 := bstep (se 1 (by rfl) ⟨2345264, by rfl⟩ : syracuseStep 3127019 = 4690529) B4690529
theorem B2084679 : Blo 2083435 2084679 := bstep (se 1 (by rfl) ⟨1563509, by rfl⟩ : syracuseStep 2084679 = 3127019) B3127019
theorem B2345269 : Blo 2083435 2345269 := bbase (se 5 (by rfl) ⟨109934, by rfl⟩ : syracuseStep 2345269 = 219869) (by norm_num)
theorem B3127025 : Blo 2083435 3127025 := bstep (se 2 (by rfl) ⟨1172634, by rfl⟩ : syracuseStep 3127025 = 2345269) B2345269
theorem B2084683 : Blo 2083435 2084683 := bstep (se 1 (by rfl) ⟨1563512, by rfl⟩ : syracuseStep 2084683 = 3127025) B3127025
theorem B2638433 : Blo 2083435 2638433 := bbase (se 2 (by rfl) ⟨989412, by rfl⟩ : syracuseStep 2638433 = 1978825) (by norm_num)
theorem B7035821 : Blo 2083435 7035821 := bstep (se 3 (by rfl) ⟨1319216, by rfl⟩ : syracuseStep 7035821 = 2638433) B2638433
theorem B4690547 : Blo 2083435 4690547 := bstep (se 1 (by rfl) ⟨3517910, by rfl⟩ : syracuseStep 4690547 = 7035821) B7035821
theorem B3127031 : Blo 2083435 3127031 := bstep (se 1 (by rfl) ⟨2345273, by rfl⟩ : syracuseStep 3127031 = 4690547) B4690547
theorem B2084687 : Blo 2083435 2084687 := bstep (se 1 (by rfl) ⟨1563515, by rfl⟩ : syracuseStep 2084687 = 3127031) B3127031
theorem B3127037 : Blo 2083435 3127037 := bbase (se 3 (by rfl) ⟨586319, by rfl⟩ : syracuseStep 3127037 = 1172639) (by norm_num)
theorem B2084691 : Blo 2083435 2084691 := bstep (se 1 (by rfl) ⟨1563518, by rfl⟩ : syracuseStep 2084691 = 3127037) B3127037
theorem B4690565 : Blo 2083435 4690565 := bbase (se 4 (by rfl) ⟨439740, by rfl⟩ : syracuseStep 4690565 = 879481) (by norm_num)
theorem B3127043 : Blo 2083435 3127043 := bstep (se 1 (by rfl) ⟨2345282, by rfl⟩ : syracuseStep 3127043 = 4690565) B4690565
theorem B2084695 : Blo 2083435 2084695 := bstep (se 1 (by rfl) ⟨1563521, by rfl⟩ : syracuseStep 2084695 = 3127043) B3127043
theorem B9026261 : Blo 2083435 9026261 := bbase (se 7 (by rfl) ⟨105776, by rfl⟩ : syracuseStep 9026261 = 211553) (by norm_num)
theorem B6017507 : Blo 2083435 6017507 := bstep (se 1 (by rfl) ⟨4513130, by rfl⟩ : syracuseStep 6017507 = 9026261) B9026261
theorem B4011671 : Blo 2083435 4011671 := bstep (se 1 (by rfl) ⟨3008753, by rfl⟩ : syracuseStep 4011671 = 6017507) B6017507
theorem B2674447 : Blo 2083435 2674447 := bstep (se 1 (by rfl) ⟨2005835, by rfl⟩ : syracuseStep 2674447 = 4011671) B4011671
theorem B14263717 : Blo 2083435 14263717 := bstep (se 4 (by rfl) ⟨1337223, by rfl⟩ : syracuseStep 14263717 = 2674447) B2674447
theorem B19018289 : Blo 2083435 19018289 := bstep (se 2 (by rfl) ⟨7131858, by rfl⟩ : syracuseStep 19018289 = 14263717) B14263717
theorem B12678859 : Blo 2083435 12678859 := bstep (se 1 (by rfl) ⟨9509144, by rfl⟩ : syracuseStep 12678859 = 19018289) B19018289
theorem B16905145 : Blo 2083435 16905145 := bstep (se 2 (by rfl) ⟨6339429, by rfl⟩ : syracuseStep 16905145 = 12678859) B12678859
theorem B22540193 : Blo 2083435 22540193 := bstep (se 2 (by rfl) ⟨8452572, by rfl⟩ : syracuseStep 22540193 = 16905145) B16905145
theorem B15026795 : Blo 2083435 15026795 := bstep (se 1 (by rfl) ⟨11270096, by rfl⟩ : syracuseStep 15026795 = 22540193) B22540193
theorem B10017863 : Blo 2083435 10017863 := bstep (se 1 (by rfl) ⟨7513397, by rfl⟩ : syracuseStep 10017863 = 15026795) B15026795
theorem B6678575 : Blo 2083435 6678575 := bstep (se 1 (by rfl) ⟨5008931, by rfl⟩ : syracuseStep 6678575 = 10017863) B10017863
theorem B4452383 : Blo 2083435 4452383 := bstep (se 1 (by rfl) ⟨3339287, by rfl⟩ : syracuseStep 4452383 = 6678575) B6678575
theorem B2968255 : Blo 2083435 2968255 := bstep (se 1 (by rfl) ⟨2226191, by rfl⟩ : syracuseStep 2968255 = 4452383) B4452383
theorem B3957673 : Blo 2083435 3957673 := bstep (se 2 (by rfl) ⟨1484127, by rfl⟩ : syracuseStep 3957673 = 2968255) B2968255
theorem B5276897 : Blo 2083435 5276897 := bstep (se 2 (by rfl) ⟨1978836, by rfl⟩ : syracuseStep 5276897 = 3957673) B3957673
theorem B3517931 : Blo 2083435 3517931 := bstep (se 1 (by rfl) ⟨2638448, by rfl⟩ : syracuseStep 3517931 = 5276897) B5276897
theorem B2345287 : Blo 2083435 2345287 := bstep (se 1 (by rfl) ⟨1758965, by rfl⟩ : syracuseStep 2345287 = 3517931) B3517931
theorem B3127049 : Blo 2083435 3127049 := bstep (se 2 (by rfl) ⟨1172643, by rfl⟩ : syracuseStep 3127049 = 2345287) B2345287
theorem B2084699 : Blo 2083435 2084699 := bstep (se 1 (by rfl) ⟨1563524, by rfl⟩ : syracuseStep 2084699 = 3127049) B3127049
theorem B10553813 : Blo 2083435 10553813 := bbase (se 7 (by rfl) ⟨123677, by rfl⟩ : syracuseStep 10553813 = 247355) (by norm_num)
theorem B7035875 : Blo 2083435 7035875 := bstep (se 1 (by rfl) ⟨5276906, by rfl⟩ : syracuseStep 7035875 = 10553813) B10553813
theorem B4690583 : Blo 2083435 4690583 := bstep (se 1 (by rfl) ⟨3517937, by rfl⟩ : syracuseStep 4690583 = 7035875) B7035875
theorem B3127055 : Blo 2083435 3127055 := bstep (se 1 (by rfl) ⟨2345291, by rfl⟩ : syracuseStep 3127055 = 4690583) B4690583
theorem B2084703 : Blo 2083435 2084703 := bstep (se 1 (by rfl) ⟨1563527, by rfl⟩ : syracuseStep 2084703 = 3127055) B3127055
theorem B3127061 : Blo 2083435 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B2084707 : Blo 2083435 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B9638933 : Blo 2083435 9638933 := bbase (se 6 (by rfl) ⟨225912, by rfl⟩ : syracuseStep 9638933 = 451825) (by norm_num)
theorem B25703821 : Blo 2083435 25703821 := bstep (se 3 (by rfl) ⟨4819466, by rfl⟩ : syracuseStep 25703821 = 9638933) B9638933
theorem B34271761 : Blo 2083435 34271761 := bstep (se 2 (by rfl) ⟨12851910, by rfl⟩ : syracuseStep 34271761 = 25703821) B25703821
theorem B45695681 : Blo 2083435 45695681 := bstep (se 2 (by rfl) ⟨17135880, by rfl⟩ : syracuseStep 45695681 = 34271761) B34271761
theorem B30463787 : Blo 2083435 30463787 := bstep (se 1 (by rfl) ⟨22847840, by rfl⟩ : syracuseStep 30463787 = 45695681) B45695681
theorem B81236765 : Blo 2083435 81236765 := bstep (se 3 (by rfl) ⟨15231893, by rfl⟩ : syracuseStep 81236765 = 30463787) B30463787
theorem B54157843 : Blo 2083435 54157843 := bstep (se 1 (by rfl) ⟨40618382, by rfl⟩ : syracuseStep 54157843 = 81236765) B81236765
theorem B72210457 : Blo 2083435 72210457 := bstep (se 2 (by rfl) ⟨27078921, by rfl⟩ : syracuseStep 72210457 = 54157843) B54157843
theorem B96280609 : Blo 2083435 96280609 := bstep (se 2 (by rfl) ⟨36105228, by rfl⟩ : syracuseStep 96280609 = 72210457) B72210457
theorem B128374145 : Blo 2083435 128374145 := bstep (se 2 (by rfl) ⟨48140304, by rfl⟩ : syracuseStep 128374145 = 96280609) B96280609
theorem B85582763 : Blo 2083435 85582763 := bstep (se 1 (by rfl) ⟨64187072, by rfl⟩ : syracuseStep 85582763 = 128374145) B128374145
theorem B57055175 : Blo 2083435 57055175 := bstep (se 1 (by rfl) ⟨42791381, by rfl⟩ : syracuseStep 57055175 = 85582763) B85582763
theorem B38036783 : Blo 2083435 38036783 := bstep (se 1 (by rfl) ⟨28527587, by rfl⟩ : syracuseStep 38036783 = 57055175) B57055175
theorem B25357855 : Blo 2083435 25357855 := bstep (se 1 (by rfl) ⟨19018391, by rfl⟩ : syracuseStep 25357855 = 38036783) B38036783
theorem B33810473 : Blo 2083435 33810473 := bstep (se 2 (by rfl) ⟨12678927, by rfl⟩ : syracuseStep 33810473 = 25357855) B25357855
theorem B90161261 : Blo 2083435 90161261 := bstep (se 3 (by rfl) ⟨16905236, by rfl⟩ : syracuseStep 90161261 = 33810473) B33810473
theorem B60107507 : Blo 2083435 60107507 := bstep (se 1 (by rfl) ⟨45080630, by rfl⟩ : syracuseStep 60107507 = 90161261) B90161261
theorem B40071671 : Blo 2083435 40071671 := bstep (se 1 (by rfl) ⟨30053753, by rfl⟩ : syracuseStep 40071671 = 60107507) B60107507
theorem B26714447 : Blo 2083435 26714447 := bstep (se 1 (by rfl) ⟨20035835, by rfl⟩ : syracuseStep 26714447 = 40071671) B40071671
theorem B17809631 : Blo 2083435 17809631 := bstep (se 1 (by rfl) ⟨13357223, by rfl⟩ : syracuseStep 17809631 = 26714447) B26714447
theorem B11873087 : Blo 2083435 11873087 := bstep (se 1 (by rfl) ⟨8904815, by rfl⟩ : syracuseStep 11873087 = 17809631) B17809631
theorem B7915391 : Blo 2083435 7915391 := bstep (se 1 (by rfl) ⟨5936543, by rfl⟩ : syracuseStep 7915391 = 11873087) B11873087
theorem B5276927 : Blo 2083435 5276927 := bstep (se 1 (by rfl) ⟨3957695, by rfl⟩ : syracuseStep 5276927 = 7915391) B7915391
theorem B3517951 : Blo 2083435 3517951 := bstep (se 1 (by rfl) ⟨2638463, by rfl⟩ : syracuseStep 3517951 = 5276927) B5276927
theorem B4690601 : Blo 2083435 4690601 := bstep (se 2 (by rfl) ⟨1758975, by rfl⟩ : syracuseStep 4690601 = 3517951) B3517951
theorem B3127067 : Blo 2083435 3127067 := bstep (se 1 (by rfl) ⟨2345300, by rfl⟩ : syracuseStep 3127067 = 4690601) B4690601
theorem B2084711 : Blo 2083435 2084711 := bstep (se 1 (by rfl) ⟨1563533, by rfl⟩ : syracuseStep 2084711 = 3127067) B3127067
theorem B2345305 : Blo 2083435 2345305 := bbase (se 2 (by rfl) ⟨879489, by rfl⟩ : syracuseStep 2345305 = 1758979) (by norm_num)
theorem B3127073 : Blo 2083435 3127073 := bstep (se 2 (by rfl) ⟨1172652, by rfl⟩ : syracuseStep 3127073 = 2345305) B2345305
theorem B2084715 : Blo 2083435 2084715 := bstep (se 1 (by rfl) ⟨1563536, by rfl⟩ : syracuseStep 2084715 = 3127073) B3127073
theorem B9509237 : Blo 2083435 9509237 := bbase (se 5 (by rfl) ⟨445745, by rfl⟩ : syracuseStep 9509237 = 891491) (by norm_num)
theorem B6339491 : Blo 2083435 6339491 := bstep (se 1 (by rfl) ⟨4754618, by rfl⟩ : syracuseStep 6339491 = 9509237) B9509237
theorem B4226327 : Blo 2083435 4226327 := bstep (se 1 (by rfl) ⟨3169745, by rfl⟩ : syracuseStep 4226327 = 6339491) B6339491
theorem B2817551 : Blo 2083435 2817551 := bstep (se 1 (by rfl) ⟨2113163, by rfl⟩ : syracuseStep 2817551 = 4226327) B4226327
theorem B7513469 : Blo 2083435 7513469 := bstep (se 3 (by rfl) ⟨1408775, by rfl⟩ : syracuseStep 7513469 = 2817551) B2817551
theorem B5008979 : Blo 2083435 5008979 := bstep (se 1 (by rfl) ⟨3756734, by rfl⟩ : syracuseStep 5008979 = 7513469) B7513469
theorem B3339319 : Blo 2083435 3339319 := bstep (se 1 (by rfl) ⟨2504489, by rfl⟩ : syracuseStep 3339319 = 5008979) B5008979
theorem B4452425 : Blo 2083435 4452425 := bstep (se 2 (by rfl) ⟨1669659, by rfl⟩ : syracuseStep 4452425 = 3339319) B3339319
theorem B2968283 : Blo 2083435 2968283 := bstep (se 1 (by rfl) ⟨2226212, by rfl⟩ : syracuseStep 2968283 = 4452425) B4452425
theorem B7915421 : Blo 2083435 7915421 := bstep (se 3 (by rfl) ⟨1484141, by rfl⟩ : syracuseStep 7915421 = 2968283) B2968283
theorem B5276947 : Blo 2083435 5276947 := bstep (se 1 (by rfl) ⟨3957710, by rfl⟩ : syracuseStep 5276947 = 7915421) B7915421
theorem B7035929 : Blo 2083435 7035929 := bstep (se 2 (by rfl) ⟨2638473, by rfl⟩ : syracuseStep 7035929 = 5276947) B5276947
theorem B4690619 : Blo 2083435 4690619 := bstep (se 1 (by rfl) ⟨3517964, by rfl⟩ : syracuseStep 4690619 = 7035929) B7035929
theorem B3127079 : Blo 2083435 3127079 := bstep (se 1 (by rfl) ⟨2345309, by rfl⟩ : syracuseStep 3127079 = 4690619) B4690619
theorem B2084719 : Blo 2083435 2084719 := bstep (se 1 (by rfl) ⟨1563539, by rfl⟩ : syracuseStep 2084719 = 3127079) B3127079
theorem B3127085 : Blo 2083435 3127085 := bbase (se 3 (by rfl) ⟨586328, by rfl⟩ : syracuseStep 3127085 = 1172657) (by norm_num)
theorem B2084723 : Blo 2083435 2084723 := bstep (se 1 (by rfl) ⟨1563542, by rfl⟩ : syracuseStep 2084723 = 3127085) B3127085
theorem B4690637 : Blo 2083435 4690637 := bbase (se 3 (by rfl) ⟨879494, by rfl⟩ : syracuseStep 4690637 = 1758989) (by norm_num)
theorem B3127091 : Blo 2083435 3127091 := bstep (se 1 (by rfl) ⟨2345318, by rfl⟩ : syracuseStep 3127091 = 4690637) B4690637
theorem B2084727 : Blo 2083435 2084727 := bstep (se 1 (by rfl) ⟨1563545, by rfl⟩ : syracuseStep 2084727 = 3127091) B3127091
theorem B2638489 : Blo 2083435 2638489 := bbase (se 2 (by rfl) ⟨989433, by rfl⟩ : syracuseStep 2638489 = 1978867) (by norm_num)
theorem B3517985 : Blo 2083435 3517985 := bstep (se 2 (by rfl) ⟨1319244, by rfl⟩ : syracuseStep 3517985 = 2638489) B2638489
theorem B2345323 : Blo 2083435 2345323 := bstep (se 1 (by rfl) ⟨1758992, by rfl⟩ : syracuseStep 2345323 = 3517985) B3517985
theorem B3127097 : Blo 2083435 3127097 := bstep (se 2 (by rfl) ⟨1172661, by rfl⟩ : syracuseStep 3127097 = 2345323) B2345323
theorem B2084731 : Blo 2083435 2084731 := bstep (se 1 (by rfl) ⟨1563548, by rfl⟩ : syracuseStep 2084731 = 3127097) B3127097
theorem B8904917 : Blo 2083435 8904917 := bbase (se 7 (by rfl) ⟨104354, by rfl⟩ : syracuseStep 8904917 = 208709) (by norm_num)
theorem B23746445 : Blo 2083435 23746445 := bstep (se 3 (by rfl) ⟨4452458, by rfl⟩ : syracuseStep 23746445 = 8904917) B8904917
theorem B15830963 : Blo 2083435 15830963 := bstep (se 1 (by rfl) ⟨11873222, by rfl⟩ : syracuseStep 15830963 = 23746445) B23746445
theorem B10553975 : Blo 2083435 10553975 := bstep (se 1 (by rfl) ⟨7915481, by rfl⟩ : syracuseStep 10553975 = 15830963) B15830963
theorem B7035983 : Blo 2083435 7035983 := bstep (se 1 (by rfl) ⟨5276987, by rfl⟩ : syracuseStep 7035983 = 10553975) B10553975
theorem B4690655 : Blo 2083435 4690655 := bstep (se 1 (by rfl) ⟨3517991, by rfl⟩ : syracuseStep 4690655 = 7035983) B7035983
theorem B3127103 : Blo 2083435 3127103 := bstep (se 1 (by rfl) ⟨2345327, by rfl⟩ : syracuseStep 3127103 = 4690655) B4690655
theorem B2084735 : Blo 2083435 2084735 := bstep (se 1 (by rfl) ⟨1563551, by rfl⟩ : syracuseStep 2084735 = 3127103) B3127103
theorem B3127109 : Blo 2083435 3127109 := bbase (se 4 (by rfl) ⟨293166, by rfl⟩ : syracuseStep 3127109 = 586333) (by norm_num)
theorem B2084739 : Blo 2083435 2084739 := bstep (se 1 (by rfl) ⟨1563554, by rfl⟩ : syracuseStep 2084739 = 3127109) B3127109
theorem B3518005 : Blo 2083435 3518005 := bbase (se 5 (by rfl) ⟨164906, by rfl⟩ : syracuseStep 3518005 = 329813) (by norm_num)
theorem B4690673 : Blo 2083435 4690673 := bstep (se 2 (by rfl) ⟨1759002, by rfl⟩ : syracuseStep 4690673 = 3518005) B3518005
theorem B3127115 : Blo 2083435 3127115 := bstep (se 1 (by rfl) ⟨2345336, by rfl⟩ : syracuseStep 3127115 = 4690673) B4690673
theorem B2084743 : Blo 2083435 2084743 := bstep (se 1 (by rfl) ⟨1563557, by rfl⟩ : syracuseStep 2084743 = 3127115) B3127115
theorem B2345341 : Blo 2083435 2345341 := bbase (se 3 (by rfl) ⟨439751, by rfl⟩ : syracuseStep 2345341 = 879503) (by norm_num)
theorem B3127121 : Blo 2083435 3127121 := bstep (se 2 (by rfl) ⟨1172670, by rfl⟩ : syracuseStep 3127121 = 2345341) B2345341
theorem B2084747 : Blo 2083435 2084747 := bstep (se 1 (by rfl) ⟨1563560, by rfl⟩ : syracuseStep 2084747 = 3127121) B3127121
theorem B7036037 : Blo 2083435 7036037 := bbase (se 4 (by rfl) ⟨659628, by rfl⟩ : syracuseStep 7036037 = 1319257) (by norm_num)
theorem B4690691 : Blo 2083435 4690691 := bstep (se 1 (by rfl) ⟨3518018, by rfl⟩ : syracuseStep 4690691 = 7036037) B7036037
theorem B3127127 : Blo 2083435 3127127 := bstep (se 1 (by rfl) ⟨2345345, by rfl⟩ : syracuseStep 3127127 = 4690691) B4690691
theorem B2084751 : Blo 2083435 2084751 := bstep (se 1 (by rfl) ⟨1563563, by rfl⟩ : syracuseStep 2084751 = 3127127) B3127127
theorem B3127133 : Blo 2083435 3127133 := bbase (se 3 (by rfl) ⟨586337, by rfl⟩ : syracuseStep 3127133 = 1172675) (by norm_num)
theorem B2084755 : Blo 2083435 2084755 := bstep (se 1 (by rfl) ⟨1563566, by rfl⟩ : syracuseStep 2084755 = 3127133) B3127133
theorem B4690709 : Blo 2083435 4690709 := bbase (se 6 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 4690709 = 219877) (by norm_num)
theorem B3127139 : Blo 2083435 3127139 := bstep (se 1 (by rfl) ⟨2345354, by rfl⟩ : syracuseStep 3127139 = 4690709) B4690709
theorem B2084759 : Blo 2083435 2084759 := bstep (se 1 (by rfl) ⟨1563569, by rfl⟩ : syracuseStep 2084759 = 3127139) B3127139
theorem B7915589 : Blo 2083435 7915589 := bbase (se 4 (by rfl) ⟨742086, by rfl⟩ : syracuseStep 7915589 = 1484173) (by norm_num)
theorem B5277059 : Blo 2083435 5277059 := bstep (se 1 (by rfl) ⟨3957794, by rfl⟩ : syracuseStep 5277059 = 7915589) B7915589
theorem B3518039 : Blo 2083435 3518039 := bstep (se 1 (by rfl) ⟨2638529, by rfl⟩ : syracuseStep 3518039 = 5277059) B5277059
theorem B2345359 : Blo 2083435 2345359 := bstep (se 1 (by rfl) ⟨1759019, by rfl⟩ : syracuseStep 2345359 = 3518039) B3518039
theorem B3127145 : Blo 2083435 3127145 := bstep (se 2 (by rfl) ⟨1172679, by rfl⟩ : syracuseStep 3127145 = 2345359) B2345359
theorem B2084763 : Blo 2083435 2084763 := bstep (se 1 (by rfl) ⟨1563572, by rfl⟩ : syracuseStep 2084763 = 3127145) B3127145
theorem B3566045 : Blo 2083435 3566045 := bbase (se 3 (by rfl) ⟨668633, by rfl⟩ : syracuseStep 3566045 = 1337267) (by norm_num)
theorem B9509453 : Blo 2083435 9509453 := bstep (se 3 (by rfl) ⟨1783022, by rfl⟩ : syracuseStep 9509453 = 3566045) B3566045
theorem B6339635 : Blo 2083435 6339635 := bstep (se 1 (by rfl) ⟨4754726, by rfl⟩ : syracuseStep 6339635 = 9509453) B9509453
theorem B4226423 : Blo 2083435 4226423 := bstep (se 1 (by rfl) ⟨3169817, by rfl⟩ : syracuseStep 4226423 = 6339635) B6339635
theorem B11270461 : Blo 2083435 11270461 := bstep (se 3 (by rfl) ⟨2113211, by rfl⟩ : syracuseStep 11270461 = 4226423) B4226423
theorem B15027281 : Blo 2083435 15027281 := bstep (se 2 (by rfl) ⟨5635230, by rfl⟩ : syracuseStep 15027281 = 11270461) B11270461
theorem B10018187 : Blo 2083435 10018187 := bstep (se 1 (by rfl) ⟨7513640, by rfl⟩ : syracuseStep 10018187 = 15027281) B15027281
theorem B6678791 : Blo 2083435 6678791 := bstep (se 1 (by rfl) ⟨5009093, by rfl⟩ : syracuseStep 6678791 = 10018187) B10018187
theorem B4452527 : Blo 2083435 4452527 := bstep (se 1 (by rfl) ⟨3339395, by rfl⟩ : syracuseStep 4452527 = 6678791) B6678791
theorem B11873405 : Blo 2083435 11873405 := bstep (se 3 (by rfl) ⟨2226263, by rfl⟩ : syracuseStep 11873405 = 4452527) B4452527
theorem B7915603 : Blo 2083435 7915603 := bstep (se 1 (by rfl) ⟨5936702, by rfl⟩ : syracuseStep 7915603 = 11873405) B11873405
theorem B10554137 : Blo 2083435 10554137 := bstep (se 2 (by rfl) ⟨3957801, by rfl⟩ : syracuseStep 10554137 = 7915603) B7915603
theorem B7036091 : Blo 2083435 7036091 := bstep (se 1 (by rfl) ⟨5277068, by rfl⟩ : syracuseStep 7036091 = 10554137) B10554137
theorem B4690727 : Blo 2083435 4690727 := bstep (se 1 (by rfl) ⟨3518045, by rfl⟩ : syracuseStep 4690727 = 7036091) B7036091
theorem B3127151 : Blo 2083435 3127151 := bstep (se 1 (by rfl) ⟨2345363, by rfl⟩ : syracuseStep 3127151 = 4690727) B4690727
theorem B2084767 : Blo 2083435 2084767 := bstep (se 1 (by rfl) ⟨1563575, by rfl⟩ : syracuseStep 2084767 = 3127151) B3127151
theorem B3127157 : Blo 2083435 3127157 := bbase (se 5 (by rfl) ⟨146585, by rfl⟩ : syracuseStep 3127157 = 293171) (by norm_num)
theorem B2084771 : Blo 2083435 2084771 := bstep (se 1 (by rfl) ⟨1563578, by rfl⟩ : syracuseStep 2084771 = 3127157) B3127157
theorem B2504557 : Blo 2083435 2504557 := bbase (se 3 (by rfl) ⟨469604, by rfl⟩ : syracuseStep 2504557 = 939209) (by norm_num)
theorem B3339409 : Blo 2083435 3339409 := bstep (se 2 (by rfl) ⟨1252278, by rfl⟩ : syracuseStep 3339409 = 2504557) B2504557
theorem B4452545 : Blo 2083435 4452545 := bstep (se 2 (by rfl) ⟨1669704, by rfl⟩ : syracuseStep 4452545 = 3339409) B3339409
theorem B2968363 : Blo 2083435 2968363 := bstep (se 1 (by rfl) ⟨2226272, by rfl⟩ : syracuseStep 2968363 = 4452545) B4452545
theorem B3957817 : Blo 2083435 3957817 := bstep (se 2 (by rfl) ⟨1484181, by rfl⟩ : syracuseStep 3957817 = 2968363) B2968363
theorem B5277089 : Blo 2083435 5277089 := bstep (se 2 (by rfl) ⟨1978908, by rfl⟩ : syracuseStep 5277089 = 3957817) B3957817
theorem B3518059 : Blo 2083435 3518059 := bstep (se 1 (by rfl) ⟨2638544, by rfl⟩ : syracuseStep 3518059 = 5277089) B5277089
theorem B4690745 : Blo 2083435 4690745 := bstep (se 2 (by rfl) ⟨1759029, by rfl⟩ : syracuseStep 4690745 = 3518059) B3518059
theorem B3127163 : Blo 2083435 3127163 := bstep (se 1 (by rfl) ⟨2345372, by rfl⟩ : syracuseStep 3127163 = 4690745) B4690745
theorem B2084775 : Blo 2083435 2084775 := bstep (se 1 (by rfl) ⟨1563581, by rfl⟩ : syracuseStep 2084775 = 3127163) B3127163
theorem B2345377 : Blo 2083435 2345377 := bbase (se 2 (by rfl) ⟨879516, by rfl⟩ : syracuseStep 2345377 = 1759033) (by norm_num)
theorem B3127169 : Blo 2083435 3127169 := bstep (se 2 (by rfl) ⟨1172688, by rfl⟩ : syracuseStep 3127169 = 2345377) B2345377
theorem B2084779 : Blo 2083435 2084779 := bstep (se 1 (by rfl) ⟨1563584, by rfl⟩ : syracuseStep 2084779 = 3127169) B3127169
theorem B5277109 : Blo 2083435 5277109 := bbase (se 5 (by rfl) ⟨247364, by rfl⟩ : syracuseStep 5277109 = 494729) (by norm_num)
theorem B7036145 : Blo 2083435 7036145 := bstep (se 2 (by rfl) ⟨2638554, by rfl⟩ : syracuseStep 7036145 = 5277109) B5277109
theorem B4690763 : Blo 2083435 4690763 := bstep (se 1 (by rfl) ⟨3518072, by rfl⟩ : syracuseStep 4690763 = 7036145) B7036145
theorem B3127175 : Blo 2083435 3127175 := bstep (se 1 (by rfl) ⟨2345381, by rfl⟩ : syracuseStep 3127175 = 4690763) B4690763
theorem B2084783 : Blo 2083435 2084783 := bstep (se 1 (by rfl) ⟨1563587, by rfl⟩ : syracuseStep 2084783 = 3127175) B3127175
theorem B3127181 : Blo 2083435 3127181 := bbase (se 3 (by rfl) ⟨586346, by rfl⟩ : syracuseStep 3127181 = 1172693) (by norm_num)
theorem B2084787 : Blo 2083435 2084787 := bstep (se 1 (by rfl) ⟨1563590, by rfl⟩ : syracuseStep 2084787 = 3127181) B3127181
theorem B4690781 : Blo 2083435 4690781 := bbase (se 3 (by rfl) ⟨879521, by rfl⟩ : syracuseStep 4690781 = 1759043) (by norm_num)
theorem B3127187 : Blo 2083435 3127187 := bstep (se 1 (by rfl) ⟨2345390, by rfl⟩ : syracuseStep 3127187 = 4690781) B4690781
theorem B2084791 : Blo 2083435 2084791 := bstep (se 1 (by rfl) ⟨1563593, by rfl⟩ : syracuseStep 2084791 = 3127187) B3127187
theorem B3518093 : Blo 2083435 3518093 := bbase (se 3 (by rfl) ⟨659642, by rfl⟩ : syracuseStep 3518093 = 1319285) (by norm_num)
theorem B2345395 : Blo 2083435 2345395 := bstep (se 1 (by rfl) ⟨1759046, by rfl⟩ : syracuseStep 2345395 = 3518093) B3518093
theorem B3127193 : Blo 2083435 3127193 := bstep (se 2 (by rfl) ⟨1172697, by rfl⟩ : syracuseStep 3127193 = 2345395) B2345395
theorem B2084795 : Blo 2083435 2084795 := bstep (se 1 (by rfl) ⟨1563596, by rfl⟩ : syracuseStep 2084795 = 3127193) B3127193
theorem B2504585 : Blo 2083435 2504585 := bbase (se 2 (by rfl) ⟨939219, by rfl⟩ : syracuseStep 2504585 = 1878439) (by norm_num)
theorem B6678893 : Blo 2083435 6678893 := bstep (se 3 (by rfl) ⟨1252292, by rfl⟩ : syracuseStep 6678893 = 2504585) B2504585
theorem B17810381 : Blo 2083435 17810381 := bstep (se 3 (by rfl) ⟨3339446, by rfl⟩ : syracuseStep 17810381 = 6678893) B6678893
theorem B11873587 : Blo 2083435 11873587 := bstep (se 1 (by rfl) ⟨8905190, by rfl⟩ : syracuseStep 11873587 = 17810381) B17810381
theorem B15831449 : Blo 2083435 15831449 := bstep (se 2 (by rfl) ⟨5936793, by rfl⟩ : syracuseStep 15831449 = 11873587) B11873587
theorem B10554299 : Blo 2083435 10554299 := bstep (se 1 (by rfl) ⟨7915724, by rfl⟩ : syracuseStep 10554299 = 15831449) B15831449
theorem B7036199 : Blo 2083435 7036199 := bstep (se 1 (by rfl) ⟨5277149, by rfl⟩ : syracuseStep 7036199 = 10554299) B10554299
theorem B4690799 : Blo 2083435 4690799 := bstep (se 1 (by rfl) ⟨3518099, by rfl⟩ : syracuseStep 4690799 = 7036199) B7036199
theorem B3127199 : Blo 2083435 3127199 := bstep (se 1 (by rfl) ⟨2345399, by rfl⟩ : syracuseStep 3127199 = 4690799) B4690799
theorem B2084799 : Blo 2083435 2084799 := bstep (se 1 (by rfl) ⟨1563599, by rfl⟩ : syracuseStep 2084799 = 3127199) B3127199
theorem B3127205 : Blo 2083435 3127205 := bbase (se 4 (by rfl) ⟨293175, by rfl⟩ : syracuseStep 3127205 = 586351) (by norm_num)
theorem B2084803 : Blo 2083435 2084803 := bstep (se 1 (by rfl) ⟨1563602, by rfl⟩ : syracuseStep 2084803 = 3127205) B3127205
theorem B2638585 : Blo 2083435 2638585 := bbase (se 2 (by rfl) ⟨989469, by rfl⟩ : syracuseStep 2638585 = 1978939) (by norm_num)
theorem B3518113 : Blo 2083435 3518113 := bstep (se 2 (by rfl) ⟨1319292, by rfl⟩ : syracuseStep 3518113 = 2638585) B2638585
theorem B4690817 : Blo 2083435 4690817 := bstep (se 2 (by rfl) ⟨1759056, by rfl⟩ : syracuseStep 4690817 = 3518113) B3518113
theorem B3127211 : Blo 2083435 3127211 := bstep (se 1 (by rfl) ⟨2345408, by rfl⟩ : syracuseStep 3127211 = 4690817) B4690817
theorem B2084807 : Blo 2083435 2084807 := bstep (se 1 (by rfl) ⟨1563605, by rfl⟩ : syracuseStep 2084807 = 3127211) B3127211
theorem B2345413 : Blo 2083435 2345413 := bbase (se 4 (by rfl) ⟨219882, by rfl⟩ : syracuseStep 2345413 = 439765) (by norm_num)
theorem B3127217 : Blo 2083435 3127217 := bstep (se 2 (by rfl) ⟨1172706, by rfl⟩ : syracuseStep 3127217 = 2345413) B2345413
theorem B2084811 : Blo 2083435 2084811 := bstep (se 1 (by rfl) ⟨1563608, by rfl⟩ : syracuseStep 2084811 = 3127217) B3127217
theorem B3957893 : Blo 2083435 3957893 := bbase (se 4 (by rfl) ⟨371052, by rfl⟩ : syracuseStep 3957893 = 742105) (by norm_num)
theorem B2638595 : Blo 2083435 2638595 := bstep (se 1 (by rfl) ⟨1978946, by rfl⟩ : syracuseStep 2638595 = 3957893) B3957893
theorem B7036253 : Blo 2083435 7036253 := bstep (se 3 (by rfl) ⟨1319297, by rfl⟩ : syracuseStep 7036253 = 2638595) B2638595
theorem B4690835 : Blo 2083435 4690835 := bstep (se 1 (by rfl) ⟨3518126, by rfl⟩ : syracuseStep 4690835 = 7036253) B7036253
theorem B3127223 : Blo 2083435 3127223 := bstep (se 1 (by rfl) ⟨2345417, by rfl⟩ : syracuseStep 3127223 = 4690835) B4690835
theorem B2084815 : Blo 2083435 2084815 := bstep (se 1 (by rfl) ⟨1563611, by rfl⟩ : syracuseStep 2084815 = 3127223) B3127223
theorem B3127229 : Blo 2083435 3127229 := bbase (se 3 (by rfl) ⟨586355, by rfl⟩ : syracuseStep 3127229 = 1172711) (by norm_num)
theorem B2084819 : Blo 2083435 2084819 := bstep (se 1 (by rfl) ⟨1563614, by rfl⟩ : syracuseStep 2084819 = 3127229) B3127229
theorem B4690853 : Blo 2083435 4690853 := bbase (se 4 (by rfl) ⟨439767, by rfl⟩ : syracuseStep 4690853 = 879535) (by norm_num)
theorem B3127235 : Blo 2083435 3127235 := bstep (se 1 (by rfl) ⟨2345426, by rfl⟩ : syracuseStep 3127235 = 4690853) B4690853
theorem B2084823 : Blo 2083435 2084823 := bstep (se 1 (by rfl) ⟨1563617, by rfl⟩ : syracuseStep 2084823 = 3127235) B3127235
theorem B5277221 : Blo 2083435 5277221 := bbase (se 4 (by rfl) ⟨494739, by rfl⟩ : syracuseStep 5277221 = 989479) (by norm_num)
theorem B3518147 : Blo 2083435 3518147 := bstep (se 1 (by rfl) ⟨2638610, by rfl⟩ : syracuseStep 3518147 = 5277221) B5277221
theorem B2345431 : Blo 2083435 2345431 := bstep (se 1 (by rfl) ⟨1759073, by rfl⟩ : syracuseStep 2345431 = 3518147) B3518147
theorem B3127241 : Blo 2083435 3127241 := bstep (se 2 (by rfl) ⟨1172715, by rfl⟩ : syracuseStep 3127241 = 2345431) B2345431
theorem B2084827 : Blo 2083435 2084827 := bstep (se 1 (by rfl) ⟨1563620, by rfl⟩ : syracuseStep 2084827 = 3127241) B3127241
theorem B5936885 : Blo 2083435 5936885 := bbase (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) (by norm_num)
theorem B3957923 : Blo 2083435 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B10554461 : Blo 2083435 10554461 := bstep (se 3 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 10554461 = 3957923) B3957923
theorem B7036307 : Blo 2083435 7036307 := bstep (se 1 (by rfl) ⟨5277230, by rfl⟩ : syracuseStep 7036307 = 10554461) B10554461
theorem B4690871 : Blo 2083435 4690871 := bstep (se 1 (by rfl) ⟨3518153, by rfl⟩ : syracuseStep 4690871 = 7036307) B7036307
theorem B3127247 : Blo 2083435 3127247 := bstep (se 1 (by rfl) ⟨2345435, by rfl⟩ : syracuseStep 3127247 = 4690871) B4690871
theorem B2084831 : Blo 2083435 2084831 := bstep (se 1 (by rfl) ⟨1563623, by rfl⟩ : syracuseStep 2084831 = 3127247) B3127247
theorem B3127253 : Blo 2083435 3127253 := bbase (se 7 (by rfl) ⟨36647, by rfl⟩ : syracuseStep 3127253 = 73295) (by norm_num)
theorem B2084835 : Blo 2083435 2084835 := bstep (se 1 (by rfl) ⟨1563626, by rfl⟩ : syracuseStep 2084835 = 3127253) B3127253
theorem B7915877 : Blo 2083435 7915877 := bbase (se 4 (by rfl) ⟨742113, by rfl⟩ : syracuseStep 7915877 = 1484227) (by norm_num)
theorem B5277251 : Blo 2083435 5277251 := bstep (se 1 (by rfl) ⟨3957938, by rfl⟩ : syracuseStep 5277251 = 7915877) B7915877
theorem B3518167 : Blo 2083435 3518167 := bstep (se 1 (by rfl) ⟨2638625, by rfl⟩ : syracuseStep 3518167 = 5277251) B5277251
theorem B4690889 : Blo 2083435 4690889 := bstep (se 2 (by rfl) ⟨1759083, by rfl⟩ : syracuseStep 4690889 = 3518167) B3518167
theorem B3127259 : Blo 2083435 3127259 := bstep (se 1 (by rfl) ⟨2345444, by rfl⟩ : syracuseStep 3127259 = 4690889) B4690889
theorem B2084839 : Blo 2083435 2084839 := bstep (se 1 (by rfl) ⟨1563629, by rfl⟩ : syracuseStep 2084839 = 3127259) B3127259
theorem B2345449 : Blo 2083435 2345449 := bbase (se 2 (by rfl) ⟨879543, by rfl⟩ : syracuseStep 2345449 = 1759087) (by norm_num)
theorem B3127265 : Blo 2083435 3127265 := bstep (se 2 (by rfl) ⟨1172724, by rfl⟩ : syracuseStep 3127265 = 2345449) B2345449
theorem B2084843 : Blo 2083435 2084843 := bstep (se 1 (by rfl) ⟨1563632, by rfl⟩ : syracuseStep 2084843 = 3127265) B3127265
theorem B2226349 : Blo 2083435 2226349 := bbase (se 3 (by rfl) ⟨417440, by rfl⟩ : syracuseStep 2226349 = 834881) (by norm_num)
theorem B11873861 : Blo 2083435 11873861 := bstep (se 4 (by rfl) ⟨1113174, by rfl⟩ : syracuseStep 11873861 = 2226349) B2226349
theorem B7915907 : Blo 2083435 7915907 := bstep (se 1 (by rfl) ⟨5936930, by rfl⟩ : syracuseStep 7915907 = 11873861) B11873861
theorem B5277271 : Blo 2083435 5277271 := bstep (se 1 (by rfl) ⟨3957953, by rfl⟩ : syracuseStep 5277271 = 7915907) B7915907
theorem B7036361 : Blo 2083435 7036361 := bstep (se 2 (by rfl) ⟨2638635, by rfl⟩ : syracuseStep 7036361 = 5277271) B5277271
theorem B4690907 : Blo 2083435 4690907 := bstep (se 1 (by rfl) ⟨3518180, by rfl⟩ : syracuseStep 4690907 = 7036361) B7036361
theorem B3127271 : Blo 2083435 3127271 := bstep (se 1 (by rfl) ⟨2345453, by rfl⟩ : syracuseStep 3127271 = 4690907) B4690907
theorem B2084847 : Blo 2083435 2084847 := bstep (se 1 (by rfl) ⟨1563635, by rfl⟩ : syracuseStep 2084847 = 3127271) B3127271
theorem B3127277 : Blo 2083435 3127277 := bbase (se 3 (by rfl) ⟨586364, by rfl⟩ : syracuseStep 3127277 = 1172729) (by norm_num)
theorem B2084851 : Blo 2083435 2084851 := bstep (se 1 (by rfl) ⟨1563638, by rfl⟩ : syracuseStep 2084851 = 3127277) B3127277
theorem B4690925 : Blo 2083435 4690925 := bbase (se 3 (by rfl) ⟨879548, by rfl⟩ : syracuseStep 4690925 = 1759097) (by norm_num)
theorem B3127283 : Blo 2083435 3127283 := bstep (se 1 (by rfl) ⟨2345462, by rfl⟩ : syracuseStep 3127283 = 4690925) B4690925
theorem B2084855 : Blo 2083435 2084855 := bstep (se 1 (by rfl) ⟨1563641, by rfl⟩ : syracuseStep 2084855 = 3127283) B3127283
theorem B4452725 : Blo 2083435 4452725 := bbase (se 5 (by rfl) ⟨208721, by rfl⟩ : syracuseStep 4452725 = 417443) (by norm_num)
theorem B2968483 : Blo 2083435 2968483 := bstep (se 1 (by rfl) ⟨2226362, by rfl⟩ : syracuseStep 2968483 = 4452725) B4452725
theorem B3957977 : Blo 2083435 3957977 := bstep (se 2 (by rfl) ⟨1484241, by rfl⟩ : syracuseStep 3957977 = 2968483) B2968483
theorem B2638651 : Blo 2083435 2638651 := bstep (se 1 (by rfl) ⟨1978988, by rfl⟩ : syracuseStep 2638651 = 3957977) B3957977
theorem B3518201 : Blo 2083435 3518201 := bstep (se 2 (by rfl) ⟨1319325, by rfl⟩ : syracuseStep 3518201 = 2638651) B2638651
theorem B2345467 : Blo 2083435 2345467 := bstep (se 1 (by rfl) ⟨1759100, by rfl⟩ : syracuseStep 2345467 = 3518201) B3518201
theorem B3127289 : Blo 2083435 3127289 := bstep (se 2 (by rfl) ⟨1172733, by rfl⟩ : syracuseStep 3127289 = 2345467) B2345467
theorem B2084859 : Blo 2083435 2084859 := bstep (se 1 (by rfl) ⟨1563644, by rfl⟩ : syracuseStep 2084859 = 3127289) B3127289
theorem B33497429 : Blo 2083435 33497429 := bbase (se 10 (by rfl) ⟨49068, by rfl⟩ : syracuseStep 33497429 = 98137) (by norm_num)
theorem B357305909 : Blo 2083435 357305909 := bstep (se 5 (by rfl) ⟨16748714, by rfl⟩ : syracuseStep 357305909 = 33497429) B33497429
theorem B3811263029 : Blo 2083435 3811263029 := bstep (se 5 (by rfl) ⟨178652954, by rfl⟩ : syracuseStep 3811263029 = 357305909) B357305909
theorem B2540842019 : Blo 2083435 2540842019 := bstep (se 1 (by rfl) ⟨1905631514, by rfl⟩ : syracuseStep 2540842019 = 3811263029) B3811263029
theorem B1693894679 : Blo 2083435 1693894679 := bstep (se 1 (by rfl) ⟨1270421009, by rfl⟩ : syracuseStep 1693894679 = 2540842019) B2540842019
theorem B1129263119 : Blo 2083435 1129263119 := bstep (se 1 (by rfl) ⟨846947339, by rfl⟩ : syracuseStep 1129263119 = 1693894679) B1693894679
theorem B752842079 : Blo 2083435 752842079 := bstep (se 1 (by rfl) ⟨564631559, by rfl⟩ : syracuseStep 752842079 = 1129263119) B1129263119
theorem B501894719 : Blo 2083435 501894719 := bstep (se 1 (by rfl) ⟨376421039, by rfl⟩ : syracuseStep 501894719 = 752842079) B752842079
theorem B334596479 : Blo 2083435 334596479 := bstep (se 1 (by rfl) ⟨250947359, by rfl⟩ : syracuseStep 334596479 = 501894719) B501894719
theorem B892257277 : Blo 2083435 892257277 := bstep (se 3 (by rfl) ⟨167298239, by rfl⟩ : syracuseStep 892257277 = 334596479) B334596479
theorem B1189676369 : Blo 2083435 1189676369 := bstep (se 2 (by rfl) ⟨446128638, by rfl⟩ : syracuseStep 1189676369 = 892257277) B892257277
theorem B3172470317 : Blo 2083435 3172470317 := bstep (se 3 (by rfl) ⟨594838184, by rfl⟩ : syracuseStep 3172470317 = 1189676369) B1189676369
theorem B2114980211 : Blo 2083435 2114980211 := bstep (se 1 (by rfl) ⟨1586235158, by rfl⟩ : syracuseStep 2114980211 = 3172470317) B3172470317
theorem B1409986807 : Blo 2083435 1409986807 := bstep (se 1 (by rfl) ⟨1057490105, by rfl⟩ : syracuseStep 1409986807 = 2114980211) B2114980211
theorem B30079718549 : Blo 2083435 30079718549 := bstep (se 6 (by rfl) ⟨704993403, by rfl⟩ : syracuseStep 30079718549 = 1409986807) B1409986807
theorem B20053145699 : Blo 2083435 20053145699 := bstep (se 1 (by rfl) ⟨15039859274, by rfl⟩ : syracuseStep 20053145699 = 30079718549) B30079718549
theorem B13368763799 : Blo 2083435 13368763799 := bstep (se 1 (by rfl) ⟨10026572849, by rfl⟩ : syracuseStep 13368763799 = 20053145699) B20053145699
theorem B8912509199 : Blo 2083435 8912509199 := bstep (se 1 (by rfl) ⟨6684381899, by rfl⟩ : syracuseStep 8912509199 = 13368763799) B13368763799
theorem B5941672799 : Blo 2083435 5941672799 := bstep (se 1 (by rfl) ⟨4456254599, by rfl⟩ : syracuseStep 5941672799 = 8912509199) B8912509199
theorem B15844460797 : Blo 2083435 15844460797 := bstep (se 3 (by rfl) ⟨2970836399, by rfl⟩ : syracuseStep 15844460797 = 5941672799) B5941672799
theorem B21125947729 : Blo 2083435 21125947729 := bstep (se 2 (by rfl) ⟨7922230398, by rfl⟩ : syracuseStep 21125947729 = 15844460797) B15844460797
theorem B28167930305 : Blo 2083435 28167930305 := bstep (se 2 (by rfl) ⟨10562973864, by rfl⟩ : syracuseStep 28167930305 = 21125947729) B21125947729
theorem B18778620203 : Blo 2083435 18778620203 := bstep (se 1 (by rfl) ⟨14083965152, by rfl⟩ : syracuseStep 18778620203 = 28167930305) B28167930305
theorem B12519080135 : Blo 2083435 12519080135 := bstep (se 1 (by rfl) ⟨9389310101, by rfl⟩ : syracuseStep 12519080135 = 18778620203) B18778620203
theorem B8346053423 : Blo 2083435 8346053423 := bstep (se 1 (by rfl) ⟨6259540067, by rfl⟩ : syracuseStep 8346053423 = 12519080135) B12519080135
theorem B22256142461 : Blo 2083435 22256142461 := bstep (se 3 (by rfl) ⟨4173026711, by rfl⟩ : syracuseStep 22256142461 = 8346053423) B8346053423
theorem B14837428307 : Blo 2083435 14837428307 := bstep (se 1 (by rfl) ⟨11128071230, by rfl⟩ : syracuseStep 14837428307 = 22256142461) B22256142461
theorem B9891618871 : Blo 2083435 9891618871 := bstep (se 1 (by rfl) ⟨7418714153, by rfl⟩ : syracuseStep 9891618871 = 14837428307) B14837428307
theorem B13188825161 : Blo 2083435 13188825161 := bstep (se 2 (by rfl) ⟨4945809435, by rfl⟩ : syracuseStep 13188825161 = 9891618871) B9891618871
theorem B8792550107 : Blo 2083435 8792550107 := bstep (se 1 (by rfl) ⟨6594412580, by rfl⟩ : syracuseStep 8792550107 = 13188825161) B13188825161
theorem B5861700071 : Blo 2083435 5861700071 := bstep (se 1 (by rfl) ⟨4396275053, by rfl⟩ : syracuseStep 5861700071 = 8792550107) B8792550107
theorem B3907800047 : Blo 2083435 3907800047 := bstep (se 1 (by rfl) ⟨2930850035, by rfl⟩ : syracuseStep 3907800047 = 5861700071) B5861700071
theorem B2605200031 : Blo 2083435 2605200031 := bstep (se 1 (by rfl) ⟨1953900023, by rfl⟩ : syracuseStep 2605200031 = 3907800047) B3907800047
theorem B3473600041 : Blo 2083435 3473600041 := bstep (se 2 (by rfl) ⟨1302600015, by rfl⟩ : syracuseStep 3473600041 = 2605200031) B2605200031
theorem B4631466721 : Blo 2083435 4631466721 := bstep (se 2 (by rfl) ⟨1736800020, by rfl⟩ : syracuseStep 4631466721 = 3473600041) B3473600041
theorem B6175288961 : Blo 2083435 6175288961 := bstep (se 2 (by rfl) ⟨2315733360, by rfl⟩ : syracuseStep 6175288961 = 4631466721) B4631466721
theorem B4116859307 : Blo 2083435 4116859307 := bstep (se 1 (by rfl) ⟨3087644480, by rfl⟩ : syracuseStep 4116859307 = 6175288961) B6175288961
theorem B2744572871 : Blo 2083435 2744572871 := bstep (se 1 (by rfl) ⟨2058429653, by rfl⟩ : syracuseStep 2744572871 = 4116859307) B4116859307
theorem B1829715247 : Blo 2083435 1829715247 := bstep (se 1 (by rfl) ⟨1372286435, by rfl⟩ : syracuseStep 1829715247 = 2744572871) B2744572871
theorem B2439620329 : Blo 2083435 2439620329 := bstep (se 2 (by rfl) ⟨914857623, by rfl⟩ : syracuseStep 2439620329 = 1829715247) B1829715247
theorem B3252827105 : Blo 2083435 3252827105 := bstep (se 2 (by rfl) ⟨1219810164, by rfl⟩ : syracuseStep 3252827105 = 2439620329) B2439620329
theorem B2168551403 : Blo 2083435 2168551403 := bstep (se 1 (by rfl) ⟨1626413552, by rfl⟩ : syracuseStep 2168551403 = 3252827105) B3252827105
theorem B1445700935 : Blo 2083435 1445700935 := bstep (se 1 (by rfl) ⟨1084275701, by rfl⟩ : syracuseStep 1445700935 = 2168551403) B2168551403
theorem B963800623 : Blo 2083435 963800623 := bstep (se 1 (by rfl) ⟨722850467, by rfl⟩ : syracuseStep 963800623 = 1445700935) B1445700935
theorem B5140269989 : Blo 2083435 5140269989 := bstep (se 4 (by rfl) ⟨481900311, by rfl⟩ : syracuseStep 5140269989 = 963800623) B963800623
theorem B3426846659 : Blo 2083435 3426846659 := bstep (se 1 (by rfl) ⟨2570134994, by rfl⟩ : syracuseStep 3426846659 = 5140269989) B5140269989
theorem B2284564439 : Blo 2083435 2284564439 := bstep (se 1 (by rfl) ⟨1713423329, by rfl⟩ : syracuseStep 2284564439 = 3426846659) B3426846659
theorem B1523042959 : Blo 2083435 1523042959 := bstep (se 1 (by rfl) ⟨1142282219, by rfl⟩ : syracuseStep 1523042959 = 2284564439) B2284564439
theorem B2030723945 : Blo 2083435 2030723945 := bstep (se 2 (by rfl) ⟨761521479, by rfl⟩ : syracuseStep 2030723945 = 1523042959) B1523042959
theorem B1353815963 : Blo 2083435 1353815963 := bstep (se 1 (by rfl) ⟨1015361972, by rfl⟩ : syracuseStep 1353815963 = 2030723945) B2030723945
theorem B902543975 : Blo 2083435 902543975 := bstep (se 1 (by rfl) ⟨676907981, by rfl⟩ : syracuseStep 902543975 = 1353815963) B1353815963
theorem B601695983 : Blo 2083435 601695983 := bstep (se 1 (by rfl) ⟨451271987, by rfl⟩ : syracuseStep 601695983 = 902543975) B902543975
theorem B1604522621 : Blo 2083435 1604522621 := bstep (se 3 (by rfl) ⟨300847991, by rfl⟩ : syracuseStep 1604522621 = 601695983) B601695983
theorem B4278726989 : Blo 2083435 4278726989 := bstep (se 3 (by rfl) ⟨802261310, by rfl⟩ : syracuseStep 4278726989 = 1604522621) B1604522621
theorem B2852484659 : Blo 2083435 2852484659 := bstep (se 1 (by rfl) ⟨2139363494, by rfl⟩ : syracuseStep 2852484659 = 4278726989) B4278726989
theorem B1901656439 : Blo 2083435 1901656439 := bstep (se 1 (by rfl) ⟨1426242329, by rfl⟩ : syracuseStep 1901656439 = 2852484659) B2852484659
theorem B1267770959 : Blo 2083435 1267770959 := bstep (se 1 (by rfl) ⟨950828219, by rfl⟩ : syracuseStep 1267770959 = 1901656439) B1901656439
theorem B845180639 : Blo 2083435 845180639 := bstep (se 1 (by rfl) ⟨633885479, by rfl⟩ : syracuseStep 845180639 = 1267770959) B1267770959
theorem B563453759 : Blo 2083435 563453759 := bstep (se 1 (by rfl) ⟨422590319, by rfl⟩ : syracuseStep 563453759 = 845180639) B845180639
theorem B1502543357 : Blo 2083435 1502543357 := bstep (se 3 (by rfl) ⟨281726879, by rfl⟩ : syracuseStep 1502543357 = 563453759) B563453759
theorem B1001695571 : Blo 2083435 1001695571 := bstep (se 1 (by rfl) ⟨751271678, by rfl⟩ : syracuseStep 1001695571 = 1502543357) B1502543357
theorem B667797047 : Blo 2083435 667797047 := bstep (se 1 (by rfl) ⟨500847785, by rfl⟩ : syracuseStep 667797047 = 1001695571) B1001695571
theorem B445198031 : Blo 2083435 445198031 := bstep (se 1 (by rfl) ⟨333898523, by rfl⟩ : syracuseStep 445198031 = 667797047) B667797047
theorem B296798687 : Blo 2083435 296798687 := bstep (se 1 (by rfl) ⟨222599015, by rfl⟩ : syracuseStep 296798687 = 445198031) B445198031
theorem B197865791 : Blo 2083435 197865791 := bstep (se 1 (by rfl) ⟨148399343, by rfl⟩ : syracuseStep 197865791 = 296798687) B296798687
theorem B131910527 : Blo 2083435 131910527 := bstep (se 1 (by rfl) ⟨98932895, by rfl⟩ : syracuseStep 131910527 = 197865791) B197865791
theorem B87940351 : Blo 2083435 87940351 := bstep (se 1 (by rfl) ⟨65955263, by rfl⟩ : syracuseStep 87940351 = 131910527) B131910527
theorem B117253801 : Blo 2083435 117253801 := bstep (se 2 (by rfl) ⟨43970175, by rfl⟩ : syracuseStep 117253801 = 87940351) B87940351
theorem B625353605 : Blo 2083435 625353605 := bstep (se 4 (by rfl) ⟨58626900, by rfl⟩ : syracuseStep 625353605 = 117253801) B117253801
theorem B416902403 : Blo 2083435 416902403 := bstep (se 1 (by rfl) ⟨312676802, by rfl⟩ : syracuseStep 416902403 = 625353605) B625353605
theorem B1111739741 : Blo 2083435 1111739741 := bstep (se 3 (by rfl) ⟨208451201, by rfl⟩ : syracuseStep 1111739741 = 416902403) B416902403
theorem B741159827 : Blo 2083435 741159827 := bstep (se 1 (by rfl) ⟨555869870, by rfl⟩ : syracuseStep 741159827 = 1111739741) B1111739741
theorem B494106551 : Blo 2083435 494106551 := bstep (se 1 (by rfl) ⟨370579913, by rfl⟩ : syracuseStep 494106551 = 741159827) B741159827
theorem B329404367 : Blo 2083435 329404367 := bstep (se 1 (by rfl) ⟨247053275, by rfl⟩ : syracuseStep 329404367 = 494106551) B494106551
theorem B219602911 : Blo 2083435 219602911 := bstep (se 1 (by rfl) ⟨164702183, by rfl⟩ : syracuseStep 219602911 = 329404367) B329404367
theorem B292803881 : Blo 2083435 292803881 := bstep (se 2 (by rfl) ⟨109801455, by rfl⟩ : syracuseStep 292803881 = 219602911) B219602911
theorem B780810349 : Blo 2083435 780810349 := bstep (se 3 (by rfl) ⟨146401940, by rfl⟩ : syracuseStep 780810349 = 292803881) B292803881
theorem B1041080465 : Blo 2083435 1041080465 := bstep (se 2 (by rfl) ⟨390405174, by rfl⟩ : syracuseStep 1041080465 = 780810349) B780810349
theorem B694053643 : Blo 2083435 694053643 := bstep (se 1 (by rfl) ⟨520540232, by rfl⟩ : syracuseStep 694053643 = 1041080465) B1041080465
theorem B925404857 : Blo 2083435 925404857 := bstep (se 2 (by rfl) ⟨347026821, by rfl⟩ : syracuseStep 925404857 = 694053643) B694053643
theorem B616936571 : Blo 2083435 616936571 := bstep (se 1 (by rfl) ⟨462702428, by rfl⟩ : syracuseStep 616936571 = 925404857) B925404857
theorem B411291047 : Blo 2083435 411291047 := bstep (se 1 (by rfl) ⟨308468285, by rfl⟩ : syracuseStep 411291047 = 616936571) B616936571
theorem B1096776125 : Blo 2083435 1096776125 := bstep (se 3 (by rfl) ⟨205645523, by rfl⟩ : syracuseStep 1096776125 = 411291047) B411291047
theorem B731184083 : Blo 2083435 731184083 := bstep (se 1 (by rfl) ⟨548388062, by rfl⟩ : syracuseStep 731184083 = 1096776125) B1096776125
theorem B487456055 : Blo 2083435 487456055 := bstep (se 1 (by rfl) ⟨365592041, by rfl⟩ : syracuseStep 487456055 = 731184083) B731184083
theorem B324970703 : Blo 2083435 324970703 := bstep (se 1 (by rfl) ⟨243728027, by rfl⟩ : syracuseStep 324970703 = 487456055) B487456055
theorem B216647135 : Blo 2083435 216647135 := bstep (se 1 (by rfl) ⟨162485351, by rfl⟩ : syracuseStep 216647135 = 324970703) B324970703
theorem B144431423 : Blo 2083435 144431423 := bstep (se 1 (by rfl) ⟨108323567, by rfl⟩ : syracuseStep 144431423 = 216647135) B216647135
theorem B96287615 : Blo 2083435 96287615 := bstep (se 1 (by rfl) ⟨72215711, by rfl⟩ : syracuseStep 96287615 = 144431423) B144431423
theorem B64191743 : Blo 2083435 64191743 := bstep (se 1 (by rfl) ⟨48143807, by rfl⟩ : syracuseStep 64191743 = 96287615) B96287615
theorem B42794495 : Blo 2083435 42794495 := bstep (se 1 (by rfl) ⟨32095871, by rfl⟩ : syracuseStep 42794495 = 64191743) B64191743
theorem B28529663 : Blo 2083435 28529663 := bstep (se 1 (by rfl) ⟨21397247, by rfl⟩ : syracuseStep 28529663 = 42794495) B42794495
theorem B76079101 : Blo 2083435 76079101 := bstep (se 3 (by rfl) ⟨14264831, by rfl⟩ : syracuseStep 76079101 = 28529663) B28529663
theorem B101438801 : Blo 2083435 101438801 := bstep (se 2 (by rfl) ⟨38039550, by rfl⟩ : syracuseStep 101438801 = 76079101) B76079101
theorem B67625867 : Blo 2083435 67625867 := bstep (se 1 (by rfl) ⟨50719400, by rfl⟩ : syracuseStep 67625867 = 101438801) B101438801
theorem B180335645 : Blo 2083435 180335645 := bstep (se 3 (by rfl) ⟨33812933, by rfl⟩ : syracuseStep 180335645 = 67625867) B67625867
theorem B120223763 : Blo 2083435 120223763 := bstep (se 1 (by rfl) ⟨90167822, by rfl⟩ : syracuseStep 120223763 = 180335645) B180335645
theorem B80149175 : Blo 2083435 80149175 := bstep (se 1 (by rfl) ⟨60111881, by rfl⟩ : syracuseStep 80149175 = 120223763) B120223763
theorem B53432783 : Blo 2083435 53432783 := bstep (se 1 (by rfl) ⟨40074587, by rfl⟩ : syracuseStep 53432783 = 80149175) B80149175
theorem B35621855 : Blo 2083435 35621855 := bstep (se 1 (by rfl) ⟨26716391, by rfl⟩ : syracuseStep 35621855 = 53432783) B53432783
theorem B23747903 : Blo 2083435 23747903 := bstep (se 1 (by rfl) ⟨17810927, by rfl⟩ : syracuseStep 23747903 = 35621855) B35621855
theorem B15831935 : Blo 2083435 15831935 := bstep (se 1 (by rfl) ⟨11873951, by rfl⟩ : syracuseStep 15831935 = 23747903) B23747903
theorem B10554623 : Blo 2083435 10554623 := bstep (se 1 (by rfl) ⟨7915967, by rfl⟩ : syracuseStep 10554623 = 15831935) B15831935
theorem B7036415 : Blo 2083435 7036415 := bstep (se 1 (by rfl) ⟨5277311, by rfl⟩ : syracuseStep 7036415 = 10554623) B10554623
theorem B4690943 : Blo 2083435 4690943 := bstep (se 1 (by rfl) ⟨3518207, by rfl⟩ : syracuseStep 4690943 = 7036415) B7036415
theorem B3127295 : Blo 2083435 3127295 := bstep (se 1 (by rfl) ⟨2345471, by rfl⟩ : syracuseStep 3127295 = 4690943) B4690943
theorem B2084863 : Blo 2083435 2084863 := bstep (se 1 (by rfl) ⟨1563647, by rfl⟩ : syracuseStep 2084863 = 3127295) B3127295
theorem B3127301 : Blo 2083435 3127301 := bbase (se 4 (by rfl) ⟨293184, by rfl⟩ : syracuseStep 3127301 = 586369) (by norm_num)
theorem B2084867 : Blo 2083435 2084867 := bstep (se 1 (by rfl) ⟨1563650, by rfl⟩ : syracuseStep 2084867 = 3127301) B3127301
theorem B3518221 : Blo 2083435 3518221 := bbase (se 3 (by rfl) ⟨659666, by rfl⟩ : syracuseStep 3518221 = 1319333) (by norm_num)
theorem B4690961 : Blo 2083435 4690961 := bstep (se 2 (by rfl) ⟨1759110, by rfl⟩ : syracuseStep 4690961 = 3518221) B3518221
theorem B3127307 : Blo 2083435 3127307 := bstep (se 1 (by rfl) ⟨2345480, by rfl⟩ : syracuseStep 3127307 = 4690961) B4690961
theorem B2084871 : Blo 2083435 2084871 := bstep (se 1 (by rfl) ⟨1563653, by rfl⟩ : syracuseStep 2084871 = 3127307) B3127307
theorem B2345485 : Blo 2083435 2345485 := bbase (se 3 (by rfl) ⟨439778, by rfl⟩ : syracuseStep 2345485 = 879557) (by norm_num)
theorem B3127313 : Blo 2083435 3127313 := bstep (se 2 (by rfl) ⟨1172742, by rfl⟩ : syracuseStep 3127313 = 2345485) B2345485
theorem B2084875 : Blo 2083435 2084875 := bstep (se 1 (by rfl) ⟨1563656, by rfl⟩ : syracuseStep 2084875 = 3127313) B3127313
theorem B7036469 : Blo 2083435 7036469 := bbase (se 5 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 7036469 = 659669) (by norm_num)
theorem B4690979 : Blo 2083435 4690979 := bstep (se 1 (by rfl) ⟨3518234, by rfl⟩ : syracuseStep 4690979 = 7036469) B7036469
theorem B3127319 : Blo 2083435 3127319 := bstep (se 1 (by rfl) ⟨2345489, by rfl⟩ : syracuseStep 3127319 = 4690979) B4690979
theorem B2084879 : Blo 2083435 2084879 := bstep (se 1 (by rfl) ⟨1563659, by rfl⟩ : syracuseStep 2084879 = 3127319) B3127319
theorem B3127325 : Blo 2083435 3127325 := bbase (se 3 (by rfl) ⟨586373, by rfl⟩ : syracuseStep 3127325 = 1172747) (by norm_num)
theorem B2084883 : Blo 2083435 2084883 := bstep (se 1 (by rfl) ⟨1563662, by rfl⟩ : syracuseStep 2084883 = 3127325) B3127325
theorem B4690997 : Blo 2083435 4690997 := bbase (se 5 (by rfl) ⟨219890, by rfl⟩ : syracuseStep 4690997 = 439781) (by norm_num)
theorem B3127331 : Blo 2083435 3127331 := bstep (se 1 (by rfl) ⟨2345498, by rfl⟩ : syracuseStep 3127331 = 4690997) B4690997
theorem B2084887 : Blo 2083435 2084887 := bstep (se 1 (by rfl) ⟨1563665, by rfl⟩ : syracuseStep 2084887 = 3127331) B3127331
theorem B6679189 : Blo 2083435 6679189 := bbase (se 6 (by rfl) ⟨156543, by rfl⟩ : syracuseStep 6679189 = 313087) (by norm_num)
theorem B8905585 : Blo 2083435 8905585 := bstep (se 2 (by rfl) ⟨3339594, by rfl⟩ : syracuseStep 8905585 = 6679189) B6679189
theorem B11874113 : Blo 2083435 11874113 := bstep (se 2 (by rfl) ⟨4452792, by rfl⟩ : syracuseStep 11874113 = 8905585) B8905585
theorem B7916075 : Blo 2083435 7916075 := bstep (se 1 (by rfl) ⟨5937056, by rfl⟩ : syracuseStep 7916075 = 11874113) B11874113
theorem B5277383 : Blo 2083435 5277383 := bstep (se 1 (by rfl) ⟨3958037, by rfl⟩ : syracuseStep 5277383 = 7916075) B7916075
theorem B3518255 : Blo 2083435 3518255 := bstep (se 1 (by rfl) ⟨2638691, by rfl⟩ : syracuseStep 3518255 = 5277383) B5277383
theorem B2345503 : Blo 2083435 2345503 := bstep (se 1 (by rfl) ⟨1759127, by rfl⟩ : syracuseStep 2345503 = 3518255) B3518255
theorem B3127337 : Blo 2083435 3127337 := bstep (se 2 (by rfl) ⟨1172751, by rfl⟩ : syracuseStep 3127337 = 2345503) B2345503
theorem B2084891 : Blo 2083435 2084891 := bstep (se 1 (by rfl) ⟨1563668, by rfl⟩ : syracuseStep 2084891 = 3127337) B3127337
theorem B5349397 : Blo 2083435 5349397 := bbase (se 6 (by rfl) ⟨125376, by rfl⟩ : syracuseStep 5349397 = 250753) (by norm_num)
theorem B7132529 : Blo 2083435 7132529 := bstep (se 2 (by rfl) ⟨2674698, by rfl⟩ : syracuseStep 7132529 = 5349397) B5349397
theorem B4755019 : Blo 2083435 4755019 := bstep (se 1 (by rfl) ⟨3566264, by rfl⟩ : syracuseStep 4755019 = 7132529) B7132529
theorem B6340025 : Blo 2083435 6340025 := bstep (se 2 (by rfl) ⟨2377509, by rfl⟩ : syracuseStep 6340025 = 4755019) B4755019
theorem B4226683 : Blo 2083435 4226683 := bstep (se 1 (by rfl) ⟨3170012, by rfl⟩ : syracuseStep 4226683 = 6340025) B6340025
theorem B5635577 : Blo 2083435 5635577 := bstep (se 2 (by rfl) ⟨2113341, by rfl⟩ : syracuseStep 5635577 = 4226683) B4226683
theorem B3757051 : Blo 2083435 3757051 := bstep (se 1 (by rfl) ⟨2817788, by rfl⟩ : syracuseStep 3757051 = 5635577) B5635577
theorem B5009401 : Blo 2083435 5009401 := bstep (se 2 (by rfl) ⟨1878525, by rfl⟩ : syracuseStep 5009401 = 3757051) B3757051
theorem B6679201 : Blo 2083435 6679201 := bstep (se 2 (by rfl) ⟨2504700, by rfl⟩ : syracuseStep 6679201 = 5009401) B5009401
theorem B8905601 : Blo 2083435 8905601 := bstep (se 2 (by rfl) ⟨3339600, by rfl⟩ : syracuseStep 8905601 = 6679201) B6679201
theorem B5937067 : Blo 2083435 5937067 := bstep (se 1 (by rfl) ⟨4452800, by rfl⟩ : syracuseStep 5937067 = 8905601) B8905601
theorem B7916089 : Blo 2083435 7916089 := bstep (se 2 (by rfl) ⟨2968533, by rfl⟩ : syracuseStep 7916089 = 5937067) B5937067
theorem B10554785 : Blo 2083435 10554785 := bstep (se 2 (by rfl) ⟨3958044, by rfl⟩ : syracuseStep 10554785 = 7916089) B7916089
theorem B7036523 : Blo 2083435 7036523 := bstep (se 1 (by rfl) ⟨5277392, by rfl⟩ : syracuseStep 7036523 = 10554785) B10554785
theorem B4691015 : Blo 2083435 4691015 := bstep (se 1 (by rfl) ⟨3518261, by rfl⟩ : syracuseStep 4691015 = 7036523) B7036523
theorem B3127343 : Blo 2083435 3127343 := bstep (se 1 (by rfl) ⟨2345507, by rfl⟩ : syracuseStep 3127343 = 4691015) B4691015
theorem B2084895 : Blo 2083435 2084895 := bstep (se 1 (by rfl) ⟨1563671, by rfl⟩ : syracuseStep 2084895 = 3127343) B3127343
theorem B3127349 : Blo 2083435 3127349 := bbase (se 5 (by rfl) ⟨146594, by rfl⟩ : syracuseStep 3127349 = 293189) (by norm_num)
theorem B2084899 : Blo 2083435 2084899 := bstep (se 1 (by rfl) ⟨1563674, by rfl⟩ : syracuseStep 2084899 = 3127349) B3127349
theorem B5277413 : Blo 2083435 5277413 := bbase (se 4 (by rfl) ⟨494757, by rfl⟩ : syracuseStep 5277413 = 989515) (by norm_num)
theorem B3518275 : Blo 2083435 3518275 := bstep (se 1 (by rfl) ⟨2638706, by rfl⟩ : syracuseStep 3518275 = 5277413) B5277413
theorem B4691033 : Blo 2083435 4691033 := bstep (se 2 (by rfl) ⟨1759137, by rfl⟩ : syracuseStep 4691033 = 3518275) B3518275
theorem B3127355 : Blo 2083435 3127355 := bstep (se 1 (by rfl) ⟨2345516, by rfl⟩ : syracuseStep 3127355 = 4691033) B4691033
theorem B2084903 : Blo 2083435 2084903 := bstep (se 1 (by rfl) ⟨1563677, by rfl⟩ : syracuseStep 2084903 = 3127355) B3127355
theorem B2345521 : Blo 2083435 2345521 := bbase (se 2 (by rfl) ⟨879570, by rfl⟩ : syracuseStep 2345521 = 1759141) (by norm_num)
theorem B3127361 : Blo 2083435 3127361 := bstep (se 2 (by rfl) ⟨1172760, by rfl⟩ : syracuseStep 3127361 = 2345521) B2345521
theorem B2084907 : Blo 2083435 2084907 := bstep (se 1 (by rfl) ⟨1563680, by rfl⟩ : syracuseStep 2084907 = 3127361) B3127361
theorem B6679253 : Blo 2083435 6679253 := bbase (se 7 (by rfl) ⟨78272, by rfl⟩ : syracuseStep 6679253 = 156545) (by norm_num)
theorem B4452835 : Blo 2083435 4452835 := bstep (se 1 (by rfl) ⟨3339626, by rfl⟩ : syracuseStep 4452835 = 6679253) B6679253
theorem B5937113 : Blo 2083435 5937113 := bstep (se 2 (by rfl) ⟨2226417, by rfl⟩ : syracuseStep 5937113 = 4452835) B4452835
theorem B3958075 : Blo 2083435 3958075 := bstep (se 1 (by rfl) ⟨2968556, by rfl⟩ : syracuseStep 3958075 = 5937113) B5937113
theorem B5277433 : Blo 2083435 5277433 := bstep (se 2 (by rfl) ⟨1979037, by rfl⟩ : syracuseStep 5277433 = 3958075) B3958075
theorem B7036577 : Blo 2083435 7036577 := bstep (se 2 (by rfl) ⟨2638716, by rfl⟩ : syracuseStep 7036577 = 5277433) B5277433
theorem B4691051 : Blo 2083435 4691051 := bstep (se 1 (by rfl) ⟨3518288, by rfl⟩ : syracuseStep 4691051 = 7036577) B7036577
theorem B3127367 : Blo 2083435 3127367 := bstep (se 1 (by rfl) ⟨2345525, by rfl⟩ : syracuseStep 3127367 = 4691051) B4691051
theorem B2084911 : Blo 2083435 2084911 := bstep (se 1 (by rfl) ⟨1563683, by rfl⟩ : syracuseStep 2084911 = 3127367) B3127367
theorem B3127373 : Blo 2083435 3127373 := bbase (se 3 (by rfl) ⟨586382, by rfl⟩ : syracuseStep 3127373 = 1172765) (by norm_num)
theorem B2084915 : Blo 2083435 2084915 := bstep (se 1 (by rfl) ⟨1563686, by rfl⟩ : syracuseStep 2084915 = 3127373) B3127373
theorem B4691069 : Blo 2083435 4691069 := bbase (se 3 (by rfl) ⟨879575, by rfl⟩ : syracuseStep 4691069 = 1759151) (by norm_num)
theorem B3127379 : Blo 2083435 3127379 := bstep (se 1 (by rfl) ⟨2345534, by rfl⟩ : syracuseStep 3127379 = 4691069) B4691069
theorem B2084919 : Blo 2083435 2084919 := bstep (se 1 (by rfl) ⟨1563689, by rfl⟩ : syracuseStep 2084919 = 3127379) B3127379
theorem B3518309 : Blo 2083435 3518309 := bbase (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) (by norm_num)
theorem B2345539 : Blo 2083435 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B3127385 : Blo 2083435 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B2084923 : Blo 2083435 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B4452869 : Blo 2083435 4452869 := bbase (se 4 (by rfl) ⟨417456, by rfl⟩ : syracuseStep 4452869 = 834913) (by norm_num)
theorem B2968579 : Blo 2083435 2968579 := bstep (se 1 (by rfl) ⟨2226434, by rfl⟩ : syracuseStep 2968579 = 4452869) B4452869
theorem B15832421 : Blo 2083435 15832421 := bstep (se 4 (by rfl) ⟨1484289, by rfl⟩ : syracuseStep 15832421 = 2968579) B2968579
theorem B10554947 : Blo 2083435 10554947 := bstep (se 1 (by rfl) ⟨7916210, by rfl⟩ : syracuseStep 10554947 = 15832421) B15832421
theorem B7036631 : Blo 2083435 7036631 := bstep (se 1 (by rfl) ⟨5277473, by rfl⟩ : syracuseStep 7036631 = 10554947) B10554947
theorem B4691087 : Blo 2083435 4691087 := bstep (se 1 (by rfl) ⟨3518315, by rfl⟩ : syracuseStep 4691087 = 7036631) B7036631
theorem B3127391 : Blo 2083435 3127391 := bstep (se 1 (by rfl) ⟨2345543, by rfl⟩ : syracuseStep 3127391 = 4691087) B4691087
theorem B2084927 : Blo 2083435 2084927 := bstep (se 1 (by rfl) ⟨1563695, by rfl⟩ : syracuseStep 2084927 = 3127391) B3127391
theorem B3127397 : Blo 2083435 3127397 := bbase (se 4 (by rfl) ⟨293193, by rfl⟩ : syracuseStep 3127397 = 586387) (by norm_num)
theorem B2084931 : Blo 2083435 2084931 := bstep (se 1 (by rfl) ⟨1563698, by rfl⟩ : syracuseStep 2084931 = 3127397) B3127397
theorem B10018997 : Blo 2083435 10018997 := bbase (se 5 (by rfl) ⟨469640, by rfl⟩ : syracuseStep 10018997 = 939281) (by norm_num)
theorem B6679331 : Blo 2083435 6679331 := bstep (se 1 (by rfl) ⟨5009498, by rfl⟩ : syracuseStep 6679331 = 10018997) B10018997
theorem B4452887 : Blo 2083435 4452887 := bstep (se 1 (by rfl) ⟨3339665, by rfl⟩ : syracuseStep 4452887 = 6679331) B6679331
theorem B2968591 : Blo 2083435 2968591 := bstep (se 1 (by rfl) ⟨2226443, by rfl⟩ : syracuseStep 2968591 = 4452887) B4452887
theorem B3958121 : Blo 2083435 3958121 := bstep (se 2 (by rfl) ⟨1484295, by rfl⟩ : syracuseStep 3958121 = 2968591) B2968591
theorem B2638747 : Blo 2083435 2638747 := bstep (se 1 (by rfl) ⟨1979060, by rfl⟩ : syracuseStep 2638747 = 3958121) B3958121
theorem B3518329 : Blo 2083435 3518329 := bstep (se 2 (by rfl) ⟨1319373, by rfl⟩ : syracuseStep 3518329 = 2638747) B2638747
theorem B4691105 : Blo 2083435 4691105 := bstep (se 2 (by rfl) ⟨1759164, by rfl⟩ : syracuseStep 4691105 = 3518329) B3518329
theorem B3127403 : Blo 2083435 3127403 := bstep (se 1 (by rfl) ⟨2345552, by rfl⟩ : syracuseStep 3127403 = 4691105) B4691105
theorem B2084935 : Blo 2083435 2084935 := bstep (se 1 (by rfl) ⟨1563701, by rfl⟩ : syracuseStep 2084935 = 3127403) B3127403
theorem B2345557 : Blo 2083435 2345557 := bbase (se 8 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 2345557 = 27487) (by norm_num)
theorem B3127409 : Blo 2083435 3127409 := bstep (se 2 (by rfl) ⟨1172778, by rfl⟩ : syracuseStep 3127409 = 2345557) B2345557
theorem B2084939 : Blo 2083435 2084939 := bstep (se 1 (by rfl) ⟨1563704, by rfl⟩ : syracuseStep 2084939 = 3127409) B3127409
theorem B2638757 : Blo 2083435 2638757 := bbase (se 4 (by rfl) ⟨247383, by rfl⟩ : syracuseStep 2638757 = 494767) (by norm_num)
theorem B7036685 : Blo 2083435 7036685 := bstep (se 3 (by rfl) ⟨1319378, by rfl⟩ : syracuseStep 7036685 = 2638757) B2638757
theorem B4691123 : Blo 2083435 4691123 := bstep (se 1 (by rfl) ⟨3518342, by rfl⟩ : syracuseStep 4691123 = 7036685) B7036685
theorem B3127415 : Blo 2083435 3127415 := bstep (se 1 (by rfl) ⟨2345561, by rfl⟩ : syracuseStep 3127415 = 4691123) B4691123
theorem B2084943 : Blo 2083435 2084943 := bstep (se 1 (by rfl) ⟨1563707, by rfl⟩ : syracuseStep 2084943 = 3127415) B3127415
theorem B3127421 : Blo 2083435 3127421 := bbase (se 3 (by rfl) ⟨586391, by rfl⟩ : syracuseStep 3127421 = 1172783) (by norm_num)
theorem B2084947 : Blo 2083435 2084947 := bstep (se 1 (by rfl) ⟨1563710, by rfl⟩ : syracuseStep 2084947 = 3127421) B3127421
theorem B4691141 : Blo 2083435 4691141 := bbase (se 4 (by rfl) ⟨439794, by rfl⟩ : syracuseStep 4691141 = 879589) (by norm_num)
theorem B3127427 : Blo 2083435 3127427 := bstep (se 1 (by rfl) ⟨2345570, by rfl⟩ : syracuseStep 3127427 = 4691141) B4691141
theorem B2084951 : Blo 2083435 2084951 := bstep (se 1 (by rfl) ⟨1563713, by rfl⟩ : syracuseStep 2084951 = 3127427) B3127427
theorem B2504773 : Blo 2083435 2504773 := bbase (se 4 (by rfl) ⟨234822, by rfl⟩ : syracuseStep 2504773 = 469645) (by norm_num)
theorem B13358789 : Blo 2083435 13358789 := bstep (se 4 (by rfl) ⟨1252386, by rfl⟩ : syracuseStep 13358789 = 2504773) B2504773
theorem B8905859 : Blo 2083435 8905859 := bstep (se 1 (by rfl) ⟨6679394, by rfl⟩ : syracuseStep 8905859 = 13358789) B13358789
theorem B5937239 : Blo 2083435 5937239 := bstep (se 1 (by rfl) ⟨4452929, by rfl⟩ : syracuseStep 5937239 = 8905859) B8905859
theorem B3958159 : Blo 2083435 3958159 := bstep (se 1 (by rfl) ⟨2968619, by rfl⟩ : syracuseStep 3958159 = 5937239) B5937239
theorem B5277545 : Blo 2083435 5277545 := bstep (se 2 (by rfl) ⟨1979079, by rfl⟩ : syracuseStep 5277545 = 3958159) B3958159
theorem B3518363 : Blo 2083435 3518363 := bstep (se 1 (by rfl) ⟨2638772, by rfl⟩ : syracuseStep 3518363 = 5277545) B5277545
theorem B2345575 : Blo 2083435 2345575 := bstep (se 1 (by rfl) ⟨1759181, by rfl⟩ : syracuseStep 2345575 = 3518363) B3518363
theorem B3127433 : Blo 2083435 3127433 := bstep (se 2 (by rfl) ⟨1172787, by rfl⟩ : syracuseStep 3127433 = 2345575) B2345575
theorem B2084955 : Blo 2083435 2084955 := bstep (se 1 (by rfl) ⟨1563716, by rfl⟩ : syracuseStep 2084955 = 3127433) B3127433
theorem B10555109 : Blo 2083435 10555109 := bbase (se 4 (by rfl) ⟨989541, by rfl⟩ : syracuseStep 10555109 = 1979083) (by norm_num)
theorem B7036739 : Blo 2083435 7036739 := bstep (se 1 (by rfl) ⟨5277554, by rfl⟩ : syracuseStep 7036739 = 10555109) B10555109
theorem B4691159 : Blo 2083435 4691159 := bstep (se 1 (by rfl) ⟨3518369, by rfl⟩ : syracuseStep 4691159 = 7036739) B7036739
theorem B3127439 : Blo 2083435 3127439 := bstep (se 1 (by rfl) ⟨2345579, by rfl⟩ : syracuseStep 3127439 = 4691159) B4691159
theorem B2084959 : Blo 2083435 2084959 := bstep (se 1 (by rfl) ⟨1563719, by rfl⟩ : syracuseStep 2084959 = 3127439) B3127439
theorem B3127445 : Blo 2083435 3127445 := bbase (se 6 (by rfl) ⟨73299, by rfl⟩ : syracuseStep 3127445 = 146599) (by norm_num)
theorem B2084963 : Blo 2083435 2084963 := bstep (se 1 (by rfl) ⟨1563722, by rfl⟩ : syracuseStep 2084963 = 3127445) B3127445
theorem B8905909 : Blo 2083435 8905909 := bbase (se 5 (by rfl) ⟨417464, by rfl⟩ : syracuseStep 8905909 = 834929) (by norm_num)
theorem B11874545 : Blo 2083435 11874545 := bstep (se 2 (by rfl) ⟨4452954, by rfl⟩ : syracuseStep 11874545 = 8905909) B8905909
theorem B7916363 : Blo 2083435 7916363 := bstep (se 1 (by rfl) ⟨5937272, by rfl⟩ : syracuseStep 7916363 = 11874545) B11874545
theorem B5277575 : Blo 2083435 5277575 := bstep (se 1 (by rfl) ⟨3958181, by rfl⟩ : syracuseStep 5277575 = 7916363) B7916363
theorem B3518383 : Blo 2083435 3518383 := bstep (se 1 (by rfl) ⟨2638787, by rfl⟩ : syracuseStep 3518383 = 5277575) B5277575
theorem B4691177 : Blo 2083435 4691177 := bstep (se 2 (by rfl) ⟨1759191, by rfl⟩ : syracuseStep 4691177 = 3518383) B3518383
theorem B3127451 : Blo 2083435 3127451 := bstep (se 1 (by rfl) ⟨2345588, by rfl⟩ : syracuseStep 3127451 = 4691177) B4691177
theorem B2084967 : Blo 2083435 2084967 := bstep (se 1 (by rfl) ⟨1563725, by rfl⟩ : syracuseStep 2084967 = 3127451) B3127451
theorem B2345593 : Blo 2083435 2345593 := bbase (se 2 (by rfl) ⟨879597, by rfl⟩ : syracuseStep 2345593 = 1759195) (by norm_num)
theorem B3127457 : Blo 2083435 3127457 := bstep (se 2 (by rfl) ⟨1172796, by rfl⟩ : syracuseStep 3127457 = 2345593) B2345593
theorem B2084971 : Blo 2083435 2084971 := bstep (se 1 (by rfl) ⟨1563728, by rfl⟩ : syracuseStep 2084971 = 3127457) B3127457
theorem B4226845 : Blo 2083435 4226845 := bbase (se 3 (by rfl) ⟨792533, by rfl⟩ : syracuseStep 4226845 = 1585067) (by norm_num)
theorem B5635793 : Blo 2083435 5635793 := bstep (se 2 (by rfl) ⟨2113422, by rfl⟩ : syracuseStep 5635793 = 4226845) B4226845
theorem B3757195 : Blo 2083435 3757195 := bstep (se 1 (by rfl) ⟨2817896, by rfl⟩ : syracuseStep 3757195 = 5635793) B5635793
theorem B20038373 : Blo 2083435 20038373 := bstep (se 4 (by rfl) ⟨1878597, by rfl⟩ : syracuseStep 20038373 = 3757195) B3757195
theorem B13358915 : Blo 2083435 13358915 := bstep (se 1 (by rfl) ⟨10019186, by rfl⟩ : syracuseStep 13358915 = 20038373) B20038373
theorem B8905943 : Blo 2083435 8905943 := bstep (se 1 (by rfl) ⟨6679457, by rfl⟩ : syracuseStep 8905943 = 13358915) B13358915
theorem B5937295 : Blo 2083435 5937295 := bstep (se 1 (by rfl) ⟨4452971, by rfl⟩ : syracuseStep 5937295 = 8905943) B8905943
theorem B7916393 : Blo 2083435 7916393 := bstep (se 2 (by rfl) ⟨2968647, by rfl⟩ : syracuseStep 7916393 = 5937295) B5937295
theorem B5277595 : Blo 2083435 5277595 := bstep (se 1 (by rfl) ⟨3958196, by rfl⟩ : syracuseStep 5277595 = 7916393) B7916393
theorem B7036793 : Blo 2083435 7036793 := bstep (se 2 (by rfl) ⟨2638797, by rfl⟩ : syracuseStep 7036793 = 5277595) B5277595
theorem B4691195 : Blo 2083435 4691195 := bstep (se 1 (by rfl) ⟨3518396, by rfl⟩ : syracuseStep 4691195 = 7036793) B7036793
theorem B3127463 : Blo 2083435 3127463 := bstep (se 1 (by rfl) ⟨2345597, by rfl⟩ : syracuseStep 3127463 = 4691195) B4691195
theorem B2084975 : Blo 2083435 2084975 := bstep (se 1 (by rfl) ⟨1563731, by rfl⟩ : syracuseStep 2084975 = 3127463) B3127463
theorem B3127469 : Blo 2083435 3127469 := bbase (se 3 (by rfl) ⟨586400, by rfl⟩ : syracuseStep 3127469 = 1172801) (by norm_num)
theorem B2084979 : Blo 2083435 2084979 := bstep (se 1 (by rfl) ⟨1563734, by rfl⟩ : syracuseStep 2084979 = 3127469) B3127469
theorem B4691213 : Blo 2083435 4691213 := bbase (se 3 (by rfl) ⟨879602, by rfl⟩ : syracuseStep 4691213 = 1759205) (by norm_num)
theorem B3127475 : Blo 2083435 3127475 := bstep (se 1 (by rfl) ⟨2345606, by rfl⟩ : syracuseStep 3127475 = 4691213) B4691213
theorem B2084983 : Blo 2083435 2084983 := bstep (se 1 (by rfl) ⟨1563737, by rfl⟩ : syracuseStep 2084983 = 3127475) B3127475
theorem B2638813 : Blo 2083435 2638813 := bbase (se 3 (by rfl) ⟨494777, by rfl⟩ : syracuseStep 2638813 = 989555) (by norm_num)
theorem B3518417 : Blo 2083435 3518417 := bstep (se 2 (by rfl) ⟨1319406, by rfl⟩ : syracuseStep 3518417 = 2638813) B2638813
theorem B2345611 : Blo 2083435 2345611 := bstep (se 1 (by rfl) ⟨1759208, by rfl⟩ : syracuseStep 2345611 = 3518417) B3518417
theorem B3127481 : Blo 2083435 3127481 := bstep (se 2 (by rfl) ⟨1172805, by rfl⟩ : syracuseStep 3127481 = 2345611) B2345611
theorem B2084987 : Blo 2083435 2084987 := bstep (se 1 (by rfl) ⟨1563740, by rfl⟩ : syracuseStep 2084987 = 3127481) B3127481
theorem B17812021 : Blo 2083435 17812021 := bbase (se 5 (by rfl) ⟨834938, by rfl⟩ : syracuseStep 17812021 = 1669877) (by norm_num)
theorem B23749361 : Blo 2083435 23749361 := bstep (se 2 (by rfl) ⟨8906010, by rfl⟩ : syracuseStep 23749361 = 17812021) B17812021
theorem B15832907 : Blo 2083435 15832907 := bstep (se 1 (by rfl) ⟨11874680, by rfl⟩ : syracuseStep 15832907 = 23749361) B23749361
theorem B10555271 : Blo 2083435 10555271 := bstep (se 1 (by rfl) ⟨7916453, by rfl⟩ : syracuseStep 10555271 = 15832907) B15832907
theorem B7036847 : Blo 2083435 7036847 := bstep (se 1 (by rfl) ⟨5277635, by rfl⟩ : syracuseStep 7036847 = 10555271) B10555271
theorem B4691231 : Blo 2083435 4691231 := bstep (se 1 (by rfl) ⟨3518423, by rfl⟩ : syracuseStep 4691231 = 7036847) B7036847
theorem B3127487 : Blo 2083435 3127487 := bstep (se 1 (by rfl) ⟨2345615, by rfl⟩ : syracuseStep 3127487 = 4691231) B4691231
theorem B2084991 : Blo 2083435 2084991 := bstep (se 1 (by rfl) ⟨1563743, by rfl⟩ : syracuseStep 2084991 = 3127487) B3127487
theorem B3127493 : Blo 2083435 3127493 := bbase (se 4 (by rfl) ⟨293202, by rfl⟩ : syracuseStep 3127493 = 586405) (by norm_num)
theorem B2084995 : Blo 2083435 2084995 := bstep (se 1 (by rfl) ⟨1563746, by rfl⟩ : syracuseStep 2084995 = 3127493) B3127493
theorem B3518437 : Blo 2083435 3518437 := bbase (se 4 (by rfl) ⟨329853, by rfl⟩ : syracuseStep 3518437 = 659707) (by norm_num)
theorem B4691249 : Blo 2083435 4691249 := bstep (se 2 (by rfl) ⟨1759218, by rfl⟩ : syracuseStep 4691249 = 3518437) B3518437
theorem B3127499 : Blo 2083435 3127499 := bstep (se 1 (by rfl) ⟨2345624, by rfl⟩ : syracuseStep 3127499 = 4691249) B4691249
theorem B2084999 : Blo 2083435 2084999 := bstep (se 1 (by rfl) ⟨1563749, by rfl⟩ : syracuseStep 2084999 = 3127499) B3127499
theorem B2345629 : Blo 2083435 2345629 := bbase (se 3 (by rfl) ⟨439805, by rfl⟩ : syracuseStep 2345629 = 879611) (by norm_num)
theorem B3127505 : Blo 2083435 3127505 := bstep (se 2 (by rfl) ⟨1172814, by rfl⟩ : syracuseStep 3127505 = 2345629) B2345629
theorem B2085003 : Blo 2083435 2085003 := bstep (se 1 (by rfl) ⟨1563752, by rfl⟩ : syracuseStep 2085003 = 3127505) B3127505
theorem B7036901 : Blo 2083435 7036901 := bbase (se 4 (by rfl) ⟨659709, by rfl⟩ : syracuseStep 7036901 = 1319419) (by norm_num)
theorem B4691267 : Blo 2083435 4691267 := bstep (se 1 (by rfl) ⟨3518450, by rfl⟩ : syracuseStep 4691267 = 7036901) B7036901
theorem B3127511 : Blo 2083435 3127511 := bstep (se 1 (by rfl) ⟨2345633, by rfl⟩ : syracuseStep 3127511 = 4691267) B4691267
theorem B2085007 : Blo 2083435 2085007 := bstep (se 1 (by rfl) ⟨1563755, by rfl⟩ : syracuseStep 2085007 = 3127511) B3127511
theorem B3127517 : Blo 2083435 3127517 := bbase (se 3 (by rfl) ⟨586409, by rfl⟩ : syracuseStep 3127517 = 1172819) (by norm_num)
theorem B2085011 : Blo 2083435 2085011 := bstep (se 1 (by rfl) ⟨1563758, by rfl⟩ : syracuseStep 2085011 = 3127517) B3127517
theorem B4691285 : Blo 2083435 4691285 := bbase (se 14 (by rfl) ⟨429, by rfl⟩ : syracuseStep 4691285 = 859) (by norm_num)
theorem B3127523 : Blo 2083435 3127523 := bstep (se 1 (by rfl) ⟨2345642, by rfl⟩ : syracuseStep 3127523 = 4691285) B4691285
theorem B2085015 : Blo 2083435 2085015 := bstep (se 1 (by rfl) ⟨1563761, by rfl⟩ : syracuseStep 2085015 = 3127523) B3127523
theorem B2226533 : Blo 2083435 2226533 := bbase (se 4 (by rfl) ⟨208737, by rfl⟩ : syracuseStep 2226533 = 417475) (by norm_num)
theorem B5937421 : Blo 2083435 5937421 := bstep (se 3 (by rfl) ⟨1113266, by rfl⟩ : syracuseStep 5937421 = 2226533) B2226533
theorem B7916561 : Blo 2083435 7916561 := bstep (se 2 (by rfl) ⟨2968710, by rfl⟩ : syracuseStep 7916561 = 5937421) B5937421
theorem B5277707 : Blo 2083435 5277707 := bstep (se 1 (by rfl) ⟨3958280, by rfl⟩ : syracuseStep 5277707 = 7916561) B7916561
theorem B3518471 : Blo 2083435 3518471 := bstep (se 1 (by rfl) ⟨2638853, by rfl⟩ : syracuseStep 3518471 = 5277707) B5277707
theorem B2345647 : Blo 2083435 2345647 := bstep (se 1 (by rfl) ⟨1759235, by rfl⟩ : syracuseStep 2345647 = 3518471) B3518471
theorem B3127529 : Blo 2083435 3127529 := bstep (se 2 (by rfl) ⟨1172823, by rfl⟩ : syracuseStep 3127529 = 2345647) B2345647
theorem B2085019 : Blo 2083435 2085019 := bstep (se 1 (by rfl) ⟨1563764, by rfl⟩ : syracuseStep 2085019 = 3127529) B3127529
theorem B14460565 : Blo 2083435 14460565 := bbase (se 6 (by rfl) ⟨338919, by rfl⟩ : syracuseStep 14460565 = 677839) (by norm_num)
theorem B19280753 : Blo 2083435 19280753 := bstep (se 2 (by rfl) ⟨7230282, by rfl⟩ : syracuseStep 19280753 = 14460565) B14460565
theorem B12853835 : Blo 2083435 12853835 := bstep (se 1 (by rfl) ⟨9640376, by rfl⟩ : syracuseStep 12853835 = 19280753) B19280753
theorem B8569223 : Blo 2083435 8569223 := bstep (se 1 (by rfl) ⟨6426917, by rfl⟩ : syracuseStep 8569223 = 12853835) B12853835
theorem B5712815 : Blo 2083435 5712815 := bstep (se 1 (by rfl) ⟨4284611, by rfl⟩ : syracuseStep 5712815 = 8569223) B8569223
theorem B15234173 : Blo 2083435 15234173 := bstep (se 3 (by rfl) ⟨2856407, by rfl⟩ : syracuseStep 15234173 = 5712815) B5712815
theorem B10156115 : Blo 2083435 10156115 := bstep (se 1 (by rfl) ⟨7617086, by rfl⟩ : syracuseStep 10156115 = 15234173) B15234173
theorem B27082973 : Blo 2083435 27082973 := bstep (se 3 (by rfl) ⟨5078057, by rfl⟩ : syracuseStep 27082973 = 10156115) B10156115
theorem B18055315 : Blo 2083435 18055315 := bstep (se 1 (by rfl) ⟨13541486, by rfl⟩ : syracuseStep 18055315 = 27082973) B27082973
theorem B96295013 : Blo 2083435 96295013 := bstep (se 4 (by rfl) ⟨9027657, by rfl⟩ : syracuseStep 96295013 = 18055315) B18055315
theorem B64196675 : Blo 2083435 64196675 := bstep (se 1 (by rfl) ⟨48147506, by rfl⟩ : syracuseStep 64196675 = 96295013) B96295013
theorem B42797783 : Blo 2083435 42797783 := bstep (se 1 (by rfl) ⟨32098337, by rfl⟩ : syracuseStep 42797783 = 64196675) B64196675
theorem B28531855 : Blo 2083435 28531855 := bstep (se 1 (by rfl) ⟨21398891, by rfl⟩ : syracuseStep 28531855 = 42797783) B42797783
theorem B38042473 : Blo 2083435 38042473 := bstep (se 2 (by rfl) ⟨14265927, by rfl⟩ : syracuseStep 38042473 = 28531855) B28531855
theorem B50723297 : Blo 2083435 50723297 := bstep (se 2 (by rfl) ⟨19021236, by rfl⟩ : syracuseStep 50723297 = 38042473) B38042473
theorem B33815531 : Blo 2083435 33815531 := bstep (se 1 (by rfl) ⟨25361648, by rfl⟩ : syracuseStep 33815531 = 50723297) B50723297
theorem B22543687 : Blo 2083435 22543687 := bstep (se 1 (by rfl) ⟨16907765, by rfl⟩ : syracuseStep 22543687 = 33815531) B33815531
theorem B30058249 : Blo 2083435 30058249 := bstep (se 2 (by rfl) ⟨11271843, by rfl⟩ : syracuseStep 30058249 = 22543687) B22543687
theorem B40077665 : Blo 2083435 40077665 := bstep (se 2 (by rfl) ⟨15029124, by rfl⟩ : syracuseStep 40077665 = 30058249) B30058249
theorem B26718443 : Blo 2083435 26718443 := bstep (se 1 (by rfl) ⟨20038832, by rfl⟩ : syracuseStep 26718443 = 40077665) B40077665
theorem B17812295 : Blo 2083435 17812295 := bstep (se 1 (by rfl) ⟨13359221, by rfl⟩ : syracuseStep 17812295 = 26718443) B26718443
theorem B11874863 : Blo 2083435 11874863 := bstep (se 1 (by rfl) ⟨8906147, by rfl⟩ : syracuseStep 11874863 = 17812295) B17812295
theorem B7916575 : Blo 2083435 7916575 := bstep (se 1 (by rfl) ⟨5937431, by rfl⟩ : syracuseStep 7916575 = 11874863) B11874863
theorem B10555433 : Blo 2083435 10555433 := bstep (se 2 (by rfl) ⟨3958287, by rfl⟩ : syracuseStep 10555433 = 7916575) B7916575
theorem B7036955 : Blo 2083435 7036955 := bstep (se 1 (by rfl) ⟨5277716, by rfl⟩ : syracuseStep 7036955 = 10555433) B10555433
theorem B4691303 : Blo 2083435 4691303 := bstep (se 1 (by rfl) ⟨3518477, by rfl⟩ : syracuseStep 4691303 = 7036955) B7036955
theorem B3127535 : Blo 2083435 3127535 := bstep (se 1 (by rfl) ⟨2345651, by rfl⟩ : syracuseStep 3127535 = 4691303) B4691303
theorem B2085023 : Blo 2083435 2085023 := bstep (se 1 (by rfl) ⟨1563767, by rfl⟩ : syracuseStep 2085023 = 3127535) B3127535
theorem B3127541 : Blo 2083435 3127541 := bbase (se 5 (by rfl) ⟨146603, by rfl⟩ : syracuseStep 3127541 = 293207) (by norm_num)
theorem B2085027 : Blo 2083435 2085027 := bstep (se 1 (by rfl) ⟨1563770, by rfl⟩ : syracuseStep 2085027 = 3127541) B3127541
theorem B2674873 : Blo 2083435 2674873 := bbase (se 2 (by rfl) ⟨1003077, by rfl⟩ : syracuseStep 2674873 = 2006155) (by norm_num)
theorem B3566497 : Blo 2083435 3566497 := bstep (se 2 (by rfl) ⟨1337436, by rfl⟩ : syracuseStep 3566497 = 2674873) B2674873
theorem B4755329 : Blo 2083435 4755329 := bstep (se 2 (by rfl) ⟨1783248, by rfl⟩ : syracuseStep 4755329 = 3566497) B3566497
theorem B3170219 : Blo 2083435 3170219 := bstep (se 1 (by rfl) ⟨2377664, by rfl⟩ : syracuseStep 3170219 = 4755329) B4755329
theorem B8453917 : Blo 2083435 8453917 := bstep (se 3 (by rfl) ⟨1585109, by rfl⟩ : syracuseStep 8453917 = 3170219) B3170219
theorem B11271889 : Blo 2083435 11271889 := bstep (se 2 (by rfl) ⟨4226958, by rfl⟩ : syracuseStep 11271889 = 8453917) B8453917
theorem B15029185 : Blo 2083435 15029185 := bstep (se 2 (by rfl) ⟨5635944, by rfl⟩ : syracuseStep 15029185 = 11271889) B11271889
theorem B20038913 : Blo 2083435 20038913 := bstep (se 2 (by rfl) ⟨7514592, by rfl⟩ : syracuseStep 20038913 = 15029185) B15029185
theorem B13359275 : Blo 2083435 13359275 := bstep (se 1 (by rfl) ⟨10019456, by rfl⟩ : syracuseStep 13359275 = 20038913) B20038913
theorem B8906183 : Blo 2083435 8906183 := bstep (se 1 (by rfl) ⟨6679637, by rfl⟩ : syracuseStep 8906183 = 13359275) B13359275
theorem B5937455 : Blo 2083435 5937455 := bstep (se 1 (by rfl) ⟨4453091, by rfl⟩ : syracuseStep 5937455 = 8906183) B8906183
theorem B3958303 : Blo 2083435 3958303 := bstep (se 1 (by rfl) ⟨2968727, by rfl⟩ : syracuseStep 3958303 = 5937455) B5937455
theorem B5277737 : Blo 2083435 5277737 := bstep (se 2 (by rfl) ⟨1979151, by rfl⟩ : syracuseStep 5277737 = 3958303) B3958303
theorem B3518491 : Blo 2083435 3518491 := bstep (se 1 (by rfl) ⟨2638868, by rfl⟩ : syracuseStep 3518491 = 5277737) B5277737
theorem B4691321 : Blo 2083435 4691321 := bstep (se 2 (by rfl) ⟨1759245, by rfl⟩ : syracuseStep 4691321 = 3518491) B3518491
theorem B3127547 : Blo 2083435 3127547 := bstep (se 1 (by rfl) ⟨2345660, by rfl⟩ : syracuseStep 3127547 = 4691321) B4691321
theorem B2085031 : Blo 2083435 2085031 := bstep (se 1 (by rfl) ⟨1563773, by rfl⟩ : syracuseStep 2085031 = 3127547) B3127547
theorem B2345665 : Blo 2083435 2345665 := bbase (se 2 (by rfl) ⟨879624, by rfl⟩ : syracuseStep 2345665 = 1759249) (by norm_num)
theorem B3127553 : Blo 2083435 3127553 := bstep (se 2 (by rfl) ⟨1172832, by rfl⟩ : syracuseStep 3127553 = 2345665) B2345665
theorem B2085035 : Blo 2083435 2085035 := bstep (se 1 (by rfl) ⟨1563776, by rfl⟩ : syracuseStep 2085035 = 3127553) B3127553
theorem B5277757 : Blo 2083435 5277757 := bbase (se 3 (by rfl) ⟨989579, by rfl⟩ : syracuseStep 5277757 = 1979159) (by norm_num)
theorem B7037009 : Blo 2083435 7037009 := bstep (se 2 (by rfl) ⟨2638878, by rfl⟩ : syracuseStep 7037009 = 5277757) B5277757
theorem B4691339 : Blo 2083435 4691339 := bstep (se 1 (by rfl) ⟨3518504, by rfl⟩ : syracuseStep 4691339 = 7037009) B7037009
theorem B3127559 : Blo 2083435 3127559 := bstep (se 1 (by rfl) ⟨2345669, by rfl⟩ : syracuseStep 3127559 = 4691339) B4691339
theorem B2085039 : Blo 2083435 2085039 := bstep (se 1 (by rfl) ⟨1563779, by rfl⟩ : syracuseStep 2085039 = 3127559) B3127559
theorem B3127565 : Blo 2083435 3127565 := bbase (se 3 (by rfl) ⟨586418, by rfl⟩ : syracuseStep 3127565 = 1172837) (by norm_num)
theorem B2085043 : Blo 2083435 2085043 := bstep (se 1 (by rfl) ⟨1563782, by rfl⟩ : syracuseStep 2085043 = 3127565) B3127565
theorem B4691357 : Blo 2083435 4691357 := bbase (se 3 (by rfl) ⟨879629, by rfl⟩ : syracuseStep 4691357 = 1759259) (by norm_num)
theorem B3127571 : Blo 2083435 3127571 := bstep (se 1 (by rfl) ⟨2345678, by rfl⟩ : syracuseStep 3127571 = 4691357) B4691357
theorem B2085047 : Blo 2083435 2085047 := bstep (se 1 (by rfl) ⟨1563785, by rfl⟩ : syracuseStep 2085047 = 3127571) B3127571
theorem B3518525 : Blo 2083435 3518525 := bbase (se 3 (by rfl) ⟨659723, by rfl⟩ : syracuseStep 3518525 = 1319447) (by norm_num)
theorem B2345683 : Blo 2083435 2345683 := bstep (se 1 (by rfl) ⟨1759262, by rfl⟩ : syracuseStep 2345683 = 3518525) B3518525
theorem B3127577 : Blo 2083435 3127577 := bstep (se 2 (by rfl) ⟨1172841, by rfl⟩ : syracuseStep 3127577 = 2345683) B2345683
theorem B2085051 : Blo 2083435 2085051 := bstep (se 1 (by rfl) ⟨1563788, by rfl⟩ : syracuseStep 2085051 = 3127577) B3127577
theorem B2504893 : Blo 2083435 2504893 := bbase (se 3 (by rfl) ⟨469667, by rfl⟩ : syracuseStep 2504893 = 939335) (by norm_num)
theorem B3339857 : Blo 2083435 3339857 := bstep (se 2 (by rfl) ⟨1252446, by rfl⟩ : syracuseStep 3339857 = 2504893) B2504893
theorem B2226571 : Blo 2083435 2226571 := bstep (se 1 (by rfl) ⟨1669928, by rfl⟩ : syracuseStep 2226571 = 3339857) B3339857
theorem B11875045 : Blo 2083435 11875045 := bstep (se 4 (by rfl) ⟨1113285, by rfl⟩ : syracuseStep 11875045 = 2226571) B2226571
theorem B15833393 : Blo 2083435 15833393 := bstep (se 2 (by rfl) ⟨5937522, by rfl⟩ : syracuseStep 15833393 = 11875045) B11875045
theorem B10555595 : Blo 2083435 10555595 := bstep (se 1 (by rfl) ⟨7916696, by rfl⟩ : syracuseStep 10555595 = 15833393) B15833393
theorem B7037063 : Blo 2083435 7037063 := bstep (se 1 (by rfl) ⟨5277797, by rfl⟩ : syracuseStep 7037063 = 10555595) B10555595
theorem B4691375 : Blo 2083435 4691375 := bstep (se 1 (by rfl) ⟨3518531, by rfl⟩ : syracuseStep 4691375 = 7037063) B7037063
theorem B3127583 : Blo 2083435 3127583 := bstep (se 1 (by rfl) ⟨2345687, by rfl⟩ : syracuseStep 3127583 = 4691375) B4691375
theorem B2085055 : Blo 2083435 2085055 := bstep (se 1 (by rfl) ⟨1563791, by rfl⟩ : syracuseStep 2085055 = 3127583) B3127583
theorem B3127589 : Blo 2083435 3127589 := bbase (se 4 (by rfl) ⟨293211, by rfl⟩ : syracuseStep 3127589 = 586423) (by norm_num)
theorem B2085059 : Blo 2083435 2085059 := bstep (se 1 (by rfl) ⟨1563794, by rfl⟩ : syracuseStep 2085059 = 3127589) B3127589
theorem B2638909 : Blo 2083435 2638909 := bbase (se 3 (by rfl) ⟨494795, by rfl⟩ : syracuseStep 2638909 = 989591) (by norm_num)
theorem B3518545 : Blo 2083435 3518545 := bstep (se 2 (by rfl) ⟨1319454, by rfl⟩ : syracuseStep 3518545 = 2638909) B2638909
theorem B4691393 : Blo 2083435 4691393 := bstep (se 2 (by rfl) ⟨1759272, by rfl⟩ : syracuseStep 4691393 = 3518545) B3518545
theorem B3127595 : Blo 2083435 3127595 := bstep (se 1 (by rfl) ⟨2345696, by rfl⟩ : syracuseStep 3127595 = 4691393) B4691393
theorem B2085063 : Blo 2083435 2085063 := bstep (se 1 (by rfl) ⟨1563797, by rfl⟩ : syracuseStep 2085063 = 3127595) B3127595
theorem B2345701 : Blo 2083435 2345701 := bbase (se 4 (by rfl) ⟨219909, by rfl⟩ : syracuseStep 2345701 = 439819) (by norm_num)
theorem B3127601 : Blo 2083435 3127601 := bstep (se 2 (by rfl) ⟨1172850, by rfl⟩ : syracuseStep 3127601 = 2345701) B2345701
theorem B2085067 : Blo 2083435 2085067 := bstep (se 1 (by rfl) ⟨1563800, by rfl⟩ : syracuseStep 2085067 = 3127601) B3127601
theorem B13541813 : Blo 2083435 13541813 := bbase (se 5 (by rfl) ⟨634772, by rfl⟩ : syracuseStep 13541813 = 1269545) (by norm_num)
theorem B9027875 : Blo 2083435 9027875 := bstep (se 1 (by rfl) ⟨6770906, by rfl⟩ : syracuseStep 9027875 = 13541813) B13541813
theorem B6018583 : Blo 2083435 6018583 := bstep (se 1 (by rfl) ⟨4513937, by rfl⟩ : syracuseStep 6018583 = 9027875) B9027875
theorem B8024777 : Blo 2083435 8024777 := bstep (se 2 (by rfl) ⟨3009291, by rfl⟩ : syracuseStep 8024777 = 6018583) B6018583
theorem B5349851 : Blo 2083435 5349851 := bstep (se 1 (by rfl) ⟨4012388, by rfl⟩ : syracuseStep 5349851 = 8024777) B8024777
theorem B3566567 : Blo 2083435 3566567 := bstep (se 1 (by rfl) ⟨2674925, by rfl⟩ : syracuseStep 3566567 = 5349851) B5349851
theorem B2377711 : Blo 2083435 2377711 := bstep (se 1 (by rfl) ⟨1783283, by rfl⟩ : syracuseStep 2377711 = 3566567) B3566567
theorem B3170281 : Blo 2083435 3170281 := bstep (se 2 (by rfl) ⟨1188855, by rfl⟩ : syracuseStep 3170281 = 2377711) B2377711
theorem B4227041 : Blo 2083435 4227041 := bstep (se 2 (by rfl) ⟨1585140, by rfl⟩ : syracuseStep 4227041 = 3170281) B3170281
theorem B2818027 : Blo 2083435 2818027 := bstep (se 1 (by rfl) ⟨2113520, by rfl⟩ : syracuseStep 2818027 = 4227041) B4227041
theorem B3757369 : Blo 2083435 3757369 := bstep (se 2 (by rfl) ⟨1409013, by rfl⟩ : syracuseStep 3757369 = 2818027) B2818027
theorem B5009825 : Blo 2083435 5009825 := bstep (se 2 (by rfl) ⟨1878684, by rfl⟩ : syracuseStep 5009825 = 3757369) B3757369
theorem B3339883 : Blo 2083435 3339883 := bstep (se 1 (by rfl) ⟨2504912, by rfl⟩ : syracuseStep 3339883 = 5009825) B5009825
theorem B4453177 : Blo 2083435 4453177 := bstep (se 2 (by rfl) ⟨1669941, by rfl⟩ : syracuseStep 4453177 = 3339883) B3339883
theorem B5937569 : Blo 2083435 5937569 := bstep (se 2 (by rfl) ⟨2226588, by rfl⟩ : syracuseStep 5937569 = 4453177) B4453177
theorem B3958379 : Blo 2083435 3958379 := bstep (se 1 (by rfl) ⟨2968784, by rfl⟩ : syracuseStep 3958379 = 5937569) B5937569
theorem B2638919 : Blo 2083435 2638919 := bstep (se 1 (by rfl) ⟨1979189, by rfl⟩ : syracuseStep 2638919 = 3958379) B3958379
theorem B7037117 : Blo 2083435 7037117 := bstep (se 3 (by rfl) ⟨1319459, by rfl⟩ : syracuseStep 7037117 = 2638919) B2638919
theorem B4691411 : Blo 2083435 4691411 := bstep (se 1 (by rfl) ⟨3518558, by rfl⟩ : syracuseStep 4691411 = 7037117) B7037117
theorem B3127607 : Blo 2083435 3127607 := bstep (se 1 (by rfl) ⟨2345705, by rfl⟩ : syracuseStep 3127607 = 4691411) B4691411
theorem B2085071 : Blo 2083435 2085071 := bstep (se 1 (by rfl) ⟨1563803, by rfl⟩ : syracuseStep 2085071 = 3127607) B3127607
theorem B3127613 : Blo 2083435 3127613 := bbase (se 3 (by rfl) ⟨586427, by rfl⟩ : syracuseStep 3127613 = 1172855) (by norm_num)
theorem B2085075 : Blo 2083435 2085075 := bstep (se 1 (by rfl) ⟨1563806, by rfl⟩ : syracuseStep 2085075 = 3127613) B3127613
theorem B4691429 : Blo 2083435 4691429 := bbase (se 4 (by rfl) ⟨439821, by rfl⟩ : syracuseStep 4691429 = 879643) (by norm_num)
theorem B3127619 : Blo 2083435 3127619 := bstep (se 1 (by rfl) ⟨2345714, by rfl⟩ : syracuseStep 3127619 = 4691429) B4691429
theorem B2085079 : Blo 2083435 2085079 := bstep (se 1 (by rfl) ⟨1563809, by rfl⟩ : syracuseStep 2085079 = 3127619) B3127619
theorem B5277869 : Blo 2083435 5277869 := bbase (se 3 (by rfl) ⟨989600, by rfl⟩ : syracuseStep 5277869 = 1979201) (by norm_num)
theorem B3518579 : Blo 2083435 3518579 := bstep (se 1 (by rfl) ⟨2638934, by rfl⟩ : syracuseStep 3518579 = 5277869) B5277869
theorem B2345719 : Blo 2083435 2345719 := bstep (se 1 (by rfl) ⟨1759289, by rfl⟩ : syracuseStep 2345719 = 3518579) B3518579
theorem B3127625 : Blo 2083435 3127625 := bstep (se 2 (by rfl) ⟨1172859, by rfl⟩ : syracuseStep 3127625 = 2345719) B2345719
theorem B2085083 : Blo 2083435 2085083 := bstep (se 1 (by rfl) ⟨1563812, by rfl⟩ : syracuseStep 2085083 = 3127625) B3127625
theorem B2674945 : Blo 2083435 2674945 := bbase (se 2 (by rfl) ⟨1003104, by rfl⟩ : syracuseStep 2674945 = 2006209) (by norm_num)
theorem B3566593 : Blo 2083435 3566593 := bstep (se 2 (by rfl) ⟨1337472, by rfl⟩ : syracuseStep 3566593 = 2674945) B2674945
theorem B4755457 : Blo 2083435 4755457 := bstep (se 2 (by rfl) ⟨1783296, by rfl⟩ : syracuseStep 4755457 = 3566593) B3566593
theorem B6340609 : Blo 2083435 6340609 := bstep (se 2 (by rfl) ⟨2377728, by rfl⟩ : syracuseStep 6340609 = 4755457) B4755457
theorem B8454145 : Blo 2083435 8454145 := bstep (se 2 (by rfl) ⟨3170304, by rfl⟩ : syracuseStep 8454145 = 6340609) B6340609
theorem B11272193 : Blo 2083435 11272193 := bstep (se 2 (by rfl) ⟨4227072, by rfl⟩ : syracuseStep 11272193 = 8454145) B8454145
theorem B7514795 : Blo 2083435 7514795 := bstep (se 1 (by rfl) ⟨5636096, by rfl⟩ : syracuseStep 7514795 = 11272193) B11272193
theorem B5009863 : Blo 2083435 5009863 := bstep (se 1 (by rfl) ⟨3757397, by rfl⟩ : syracuseStep 5009863 = 7514795) B7514795
theorem B6679817 : Blo 2083435 6679817 := bstep (se 2 (by rfl) ⟨2504931, by rfl⟩ : syracuseStep 6679817 = 5009863) B5009863
theorem B4453211 : Blo 2083435 4453211 := bstep (se 1 (by rfl) ⟨3339908, by rfl⟩ : syracuseStep 4453211 = 6679817) B6679817
theorem B2968807 : Blo 2083435 2968807 := bstep (se 1 (by rfl) ⟨2226605, by rfl⟩ : syracuseStep 2968807 = 4453211) B4453211
theorem B3958409 : Blo 2083435 3958409 := bstep (se 2 (by rfl) ⟨1484403, by rfl⟩ : syracuseStep 3958409 = 2968807) B2968807
theorem B10555757 : Blo 2083435 10555757 := bstep (se 3 (by rfl) ⟨1979204, by rfl⟩ : syracuseStep 10555757 = 3958409) B3958409
theorem B7037171 : Blo 2083435 7037171 := bstep (se 1 (by rfl) ⟨5277878, by rfl⟩ : syracuseStep 7037171 = 10555757) B10555757
theorem B4691447 : Blo 2083435 4691447 := bstep (se 1 (by rfl) ⟨3518585, by rfl⟩ : syracuseStep 4691447 = 7037171) B7037171
theorem B3127631 : Blo 2083435 3127631 := bstep (se 1 (by rfl) ⟨2345723, by rfl⟩ : syracuseStep 3127631 = 4691447) B4691447
theorem B2085087 : Blo 2083435 2085087 := bstep (se 1 (by rfl) ⟨1563815, by rfl⟩ : syracuseStep 2085087 = 3127631) B3127631
theorem B3127637 : Blo 2083435 3127637 := bbase (se 10 (by rfl) ⟨4581, by rfl⟩ : syracuseStep 3127637 = 9163) (by norm_num)
theorem B2085091 : Blo 2083435 2085091 := bstep (se 1 (by rfl) ⟨1563818, by rfl⟩ : syracuseStep 2085091 = 3127637) B3127637
theorem B5937637 : Blo 2083435 5937637 := bbase (se 4 (by rfl) ⟨556653, by rfl⟩ : syracuseStep 5937637 = 1113307) (by norm_num)
theorem B7916849 : Blo 2083435 7916849 := bstep (se 2 (by rfl) ⟨2968818, by rfl⟩ : syracuseStep 7916849 = 5937637) B5937637
theorem B5277899 : Blo 2083435 5277899 := bstep (se 1 (by rfl) ⟨3958424, by rfl⟩ : syracuseStep 5277899 = 7916849) B7916849
theorem B3518599 : Blo 2083435 3518599 := bstep (se 1 (by rfl) ⟨2638949, by rfl⟩ : syracuseStep 3518599 = 5277899) B5277899
theorem B4691465 : Blo 2083435 4691465 := bstep (se 2 (by rfl) ⟨1759299, by rfl⟩ : syracuseStep 4691465 = 3518599) B3518599
theorem B3127643 : Blo 2083435 3127643 := bstep (se 1 (by rfl) ⟨2345732, by rfl⟩ : syracuseStep 3127643 = 4691465) B4691465
theorem B2085095 : Blo 2083435 2085095 := bstep (se 1 (by rfl) ⟨1563821, by rfl⟩ : syracuseStep 2085095 = 3127643) B3127643
theorem B2345737 : Blo 2083435 2345737 := bbase (se 2 (by rfl) ⟨879651, by rfl⟩ : syracuseStep 2345737 = 1759303) (by norm_num)
theorem B3127649 : Blo 2083435 3127649 := bstep (se 2 (by rfl) ⟨1172868, by rfl⟩ : syracuseStep 3127649 = 2345737) B2345737
theorem B2085099 : Blo 2083435 2085099 := bstep (se 1 (by rfl) ⟨1563824, by rfl⟩ : syracuseStep 2085099 = 3127649) B3127649
theorem B11272277 : Blo 2083435 11272277 := bbase (se 8 (by rfl) ⟨66048, by rfl⟩ : syracuseStep 11272277 = 132097) (by norm_num)
theorem B7514851 : Blo 2083435 7514851 := bstep (se 1 (by rfl) ⟨5636138, by rfl⟩ : syracuseStep 7514851 = 11272277) B11272277
theorem B10019801 : Blo 2083435 10019801 := bstep (se 2 (by rfl) ⟨3757425, by rfl⟩ : syracuseStep 10019801 = 7514851) B7514851
theorem B26719469 : Blo 2083435 26719469 := bstep (se 3 (by rfl) ⟨5009900, by rfl⟩ : syracuseStep 26719469 = 10019801) B10019801
theorem B17812979 : Blo 2083435 17812979 := bstep (se 1 (by rfl) ⟨13359734, by rfl⟩ : syracuseStep 17812979 = 26719469) B26719469
theorem B11875319 : Blo 2083435 11875319 := bstep (se 1 (by rfl) ⟨8906489, by rfl⟩ : syracuseStep 11875319 = 17812979) B17812979
theorem B7916879 : Blo 2083435 7916879 := bstep (se 1 (by rfl) ⟨5937659, by rfl⟩ : syracuseStep 7916879 = 11875319) B11875319
theorem B5277919 : Blo 2083435 5277919 := bstep (se 1 (by rfl) ⟨3958439, by rfl⟩ : syracuseStep 5277919 = 7916879) B7916879
theorem B7037225 : Blo 2083435 7037225 := bstep (se 2 (by rfl) ⟨2638959, by rfl⟩ : syracuseStep 7037225 = 5277919) B5277919
theorem B4691483 : Blo 2083435 4691483 := bstep (se 1 (by rfl) ⟨3518612, by rfl⟩ : syracuseStep 4691483 = 7037225) B7037225
theorem B3127655 : Blo 2083435 3127655 := bstep (se 1 (by rfl) ⟨2345741, by rfl⟩ : syracuseStep 3127655 = 4691483) B4691483
theorem B2085103 : Blo 2083435 2085103 := bstep (se 1 (by rfl) ⟨1563827, by rfl⟩ : syracuseStep 2085103 = 3127655) B3127655
theorem B3127661 : Blo 2083435 3127661 := bbase (se 3 (by rfl) ⟨586436, by rfl⟩ : syracuseStep 3127661 = 1172873) (by norm_num)
theorem B2085107 : Blo 2083435 2085107 := bstep (se 1 (by rfl) ⟨1563830, by rfl⟩ : syracuseStep 2085107 = 3127661) B3127661
theorem B4691501 : Blo 2083435 4691501 := bbase (se 3 (by rfl) ⟨879656, by rfl⟩ : syracuseStep 4691501 = 1759313) (by norm_num)
theorem B3127667 : Blo 2083435 3127667 := bstep (se 1 (by rfl) ⟨2345750, by rfl⟩ : syracuseStep 3127667 = 4691501) B4691501
theorem B2085111 : Blo 2083435 2085111 := bstep (se 1 (by rfl) ⟨1563833, by rfl⟩ : syracuseStep 2085111 = 3127667) B3127667
theorem B2674981 : Blo 2083435 2674981 := bbase (se 4 (by rfl) ⟨250779, by rfl⟩ : syracuseStep 2674981 = 501559) (by norm_num)
theorem B3566641 : Blo 2083435 3566641 := bstep (se 2 (by rfl) ⟨1337490, by rfl⟩ : syracuseStep 3566641 = 2674981) B2674981
theorem B4755521 : Blo 2083435 4755521 := bstep (se 2 (by rfl) ⟨1783320, by rfl⟩ : syracuseStep 4755521 = 3566641) B3566641
theorem B3170347 : Blo 2083435 3170347 := bstep (se 1 (by rfl) ⟨2377760, by rfl⟩ : syracuseStep 3170347 = 4755521) B4755521
theorem B16908517 : Blo 2083435 16908517 := bstep (se 4 (by rfl) ⟨1585173, by rfl⟩ : syracuseStep 16908517 = 3170347) B3170347
theorem B22544689 : Blo 2083435 22544689 := bstep (se 2 (by rfl) ⟨8454258, by rfl⟩ : syracuseStep 22544689 = 16908517) B16908517
theorem B30059585 : Blo 2083435 30059585 := bstep (se 2 (by rfl) ⟨11272344, by rfl⟩ : syracuseStep 30059585 = 22544689) B22544689
theorem B20039723 : Blo 2083435 20039723 := bstep (se 1 (by rfl) ⟨15029792, by rfl⟩ : syracuseStep 20039723 = 30059585) B30059585
theorem B13359815 : Blo 2083435 13359815 := bstep (se 1 (by rfl) ⟨10019861, by rfl⟩ : syracuseStep 13359815 = 20039723) B20039723
theorem B8906543 : Blo 2083435 8906543 := bstep (se 1 (by rfl) ⟨6679907, by rfl⟩ : syracuseStep 8906543 = 13359815) B13359815
theorem B5937695 : Blo 2083435 5937695 := bstep (se 1 (by rfl) ⟨4453271, by rfl⟩ : syracuseStep 5937695 = 8906543) B8906543
theorem B3958463 : Blo 2083435 3958463 := bstep (se 1 (by rfl) ⟨2968847, by rfl⟩ : syracuseStep 3958463 = 5937695) B5937695
theorem B2638975 : Blo 2083435 2638975 := bstep (se 1 (by rfl) ⟨1979231, by rfl⟩ : syracuseStep 2638975 = 3958463) B3958463
theorem B3518633 : Blo 2083435 3518633 := bstep (se 2 (by rfl) ⟨1319487, by rfl⟩ : syracuseStep 3518633 = 2638975) B2638975
theorem B2345755 : Blo 2083435 2345755 := bstep (se 1 (by rfl) ⟨1759316, by rfl⟩ : syracuseStep 2345755 = 3518633) B3518633
theorem B3127673 : Blo 2083435 3127673 := bstep (se 2 (by rfl) ⟨1172877, by rfl⟩ : syracuseStep 3127673 = 2345755) B2345755
theorem B2085115 : Blo 2083435 2085115 := bstep (se 1 (by rfl) ⟨1563836, by rfl⟩ : syracuseStep 2085115 = 3127673) B3127673
theorem B2377765 : Blo 2083435 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B3170353 : Blo 2083435 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B4227137 : Blo 2083435 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B2818091 : Blo 2083435 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B7514909 : Blo 2083435 7514909 := bstep (se 3 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 7514909 = 2818091) B2818091
theorem B5009939 : Blo 2083435 5009939 := bstep (se 1 (by rfl) ⟨3757454, by rfl⟩ : syracuseStep 5009939 = 7514909) B7514909
theorem B3339959 : Blo 2083435 3339959 := bstep (se 1 (by rfl) ⟨2504969, by rfl⟩ : syracuseStep 3339959 = 5009939) B5009939
theorem B35626229 : Blo 2083435 35626229 := bstep (se 5 (by rfl) ⟨1669979, by rfl⟩ : syracuseStep 35626229 = 3339959) B3339959
theorem B23750819 : Blo 2083435 23750819 := bstep (se 1 (by rfl) ⟨17813114, by rfl⟩ : syracuseStep 23750819 = 35626229) B35626229
theorem B15833879 : Blo 2083435 15833879 := bstep (se 1 (by rfl) ⟨11875409, by rfl⟩ : syracuseStep 15833879 = 23750819) B23750819
theorem B10555919 : Blo 2083435 10555919 := bstep (se 1 (by rfl) ⟨7916939, by rfl⟩ : syracuseStep 10555919 = 15833879) B15833879
theorem B7037279 : Blo 2083435 7037279 := bstep (se 1 (by rfl) ⟨5277959, by rfl⟩ : syracuseStep 7037279 = 10555919) B10555919
theorem B4691519 : Blo 2083435 4691519 := bstep (se 1 (by rfl) ⟨3518639, by rfl⟩ : syracuseStep 4691519 = 7037279) B7037279
theorem B3127679 : Blo 2083435 3127679 := bstep (se 1 (by rfl) ⟨2345759, by rfl⟩ : syracuseStep 3127679 = 4691519) B4691519
theorem B2085119 : Blo 2083435 2085119 := bstep (se 1 (by rfl) ⟨1563839, by rfl⟩ : syracuseStep 2085119 = 3127679) B3127679
theorem B3127685 : Blo 2083435 3127685 := bbase (se 4 (by rfl) ⟨293220, by rfl⟩ : syracuseStep 3127685 = 586441) (by norm_num)
theorem B2085123 : Blo 2083435 2085123 := bstep (se 1 (by rfl) ⟨1563842, by rfl⟩ : syracuseStep 2085123 = 3127685) B3127685
theorem B3518653 : Blo 2083435 3518653 := bbase (se 3 (by rfl) ⟨659747, by rfl⟩ : syracuseStep 3518653 = 1319495) (by norm_num)
theorem B4691537 : Blo 2083435 4691537 := bstep (se 2 (by rfl) ⟨1759326, by rfl⟩ : syracuseStep 4691537 = 3518653) B3518653
theorem B3127691 : Blo 2083435 3127691 := bstep (se 1 (by rfl) ⟨2345768, by rfl⟩ : syracuseStep 3127691 = 4691537) B4691537
theorem B2085127 : Blo 2083435 2085127 := bstep (se 1 (by rfl) ⟨1563845, by rfl⟩ : syracuseStep 2085127 = 3127691) B3127691
theorem B2345773 : Blo 2083435 2345773 := bbase (se 3 (by rfl) ⟨439832, by rfl⟩ : syracuseStep 2345773 = 879665) (by norm_num)
theorem B3127697 : Blo 2083435 3127697 := bstep (se 2 (by rfl) ⟨1172886, by rfl⟩ : syracuseStep 3127697 = 2345773) B2345773
theorem B2085131 : Blo 2083435 2085131 := bstep (se 1 (by rfl) ⟨1563848, by rfl⟩ : syracuseStep 2085131 = 3127697) B3127697
theorem B7037333 : Blo 2083435 7037333 := bbase (se 6 (by rfl) ⟨164937, by rfl⟩ : syracuseStep 7037333 = 329875) (by norm_num)
theorem B4691555 : Blo 2083435 4691555 := bstep (se 1 (by rfl) ⟨3518666, by rfl⟩ : syracuseStep 4691555 = 7037333) B7037333
theorem B3127703 : Blo 2083435 3127703 := bstep (se 1 (by rfl) ⟨2345777, by rfl⟩ : syracuseStep 3127703 = 4691555) B4691555
theorem B2085135 : Blo 2083435 2085135 := bstep (se 1 (by rfl) ⟨1563851, by rfl⟩ : syracuseStep 2085135 = 3127703) B3127703
theorem B3127709 : Blo 2083435 3127709 := bbase (se 3 (by rfl) ⟨586445, by rfl⟩ : syracuseStep 3127709 = 1172891) (by norm_num)
theorem B2085139 : Blo 2083435 2085139 := bstep (se 1 (by rfl) ⟨1563854, by rfl⟩ : syracuseStep 2085139 = 3127709) B3127709
theorem B4691573 : Blo 2083435 4691573 := bbase (se 5 (by rfl) ⟨219917, by rfl⟩ : syracuseStep 4691573 = 439835) (by norm_num)
theorem B3127715 : Blo 2083435 3127715 := bstep (se 1 (by rfl) ⟨2345786, by rfl⟩ : syracuseStep 3127715 = 4691573) B4691573
theorem B2085143 : Blo 2083435 2085143 := bstep (se 1 (by rfl) ⟨1563857, by rfl⟩ : syracuseStep 2085143 = 3127715) B3127715
theorem B2113597 : Blo 2083435 2113597 := bbase (se 3 (by rfl) ⟨396299, by rfl⟩ : syracuseStep 2113597 = 792599) (by norm_num)
theorem B11272517 : Blo 2083435 11272517 := bstep (se 4 (by rfl) ⟨1056798, by rfl⟩ : syracuseStep 11272517 = 2113597) B2113597
theorem B7515011 : Blo 2083435 7515011 := bstep (se 1 (by rfl) ⟨5636258, by rfl⟩ : syracuseStep 7515011 = 11272517) B11272517
theorem B5010007 : Blo 2083435 5010007 := bstep (se 1 (by rfl) ⟨3757505, by rfl⟩ : syracuseStep 5010007 = 7515011) B7515011
theorem B6680009 : Blo 2083435 6680009 := bstep (se 2 (by rfl) ⟨2505003, by rfl⟩ : syracuseStep 6680009 = 5010007) B5010007
theorem B17813357 : Blo 2083435 17813357 := bstep (se 3 (by rfl) ⟨3340004, by rfl⟩ : syracuseStep 17813357 = 6680009) B6680009
theorem B11875571 : Blo 2083435 11875571 := bstep (se 1 (by rfl) ⟨8906678, by rfl⟩ : syracuseStep 11875571 = 17813357) B17813357
theorem B7917047 : Blo 2083435 7917047 := bstep (se 1 (by rfl) ⟨5937785, by rfl⟩ : syracuseStep 7917047 = 11875571) B11875571
theorem B5278031 : Blo 2083435 5278031 := bstep (se 1 (by rfl) ⟨3958523, by rfl⟩ : syracuseStep 5278031 = 7917047) B7917047
theorem B3518687 : Blo 2083435 3518687 := bstep (se 1 (by rfl) ⟨2639015, by rfl⟩ : syracuseStep 3518687 = 5278031) B5278031
theorem B2345791 : Blo 2083435 2345791 := bstep (se 1 (by rfl) ⟨1759343, by rfl⟩ : syracuseStep 2345791 = 3518687) B3518687
theorem B3127721 : Blo 2083435 3127721 := bstep (se 2 (by rfl) ⟨1172895, by rfl⟩ : syracuseStep 3127721 = 2345791) B2345791
theorem B2085147 : Blo 2083435 2085147 := bstep (se 1 (by rfl) ⟨1563860, by rfl⟩ : syracuseStep 2085147 = 3127721) B3127721
theorem B7917061 : Blo 2083435 7917061 := bbase (se 4 (by rfl) ⟨742224, by rfl⟩ : syracuseStep 7917061 = 1484449) (by norm_num)
theorem B10556081 : Blo 2083435 10556081 := bstep (se 2 (by rfl) ⟨3958530, by rfl⟩ : syracuseStep 10556081 = 7917061) B7917061
theorem B7037387 : Blo 2083435 7037387 := bstep (se 1 (by rfl) ⟨5278040, by rfl⟩ : syracuseStep 7037387 = 10556081) B10556081
theorem B4691591 : Blo 2083435 4691591 := bstep (se 1 (by rfl) ⟨3518693, by rfl⟩ : syracuseStep 4691591 = 7037387) B7037387
theorem B3127727 : Blo 2083435 3127727 := bstep (se 1 (by rfl) ⟨2345795, by rfl⟩ : syracuseStep 3127727 = 4691591) B4691591
theorem B2085151 : Blo 2083435 2085151 := bstep (se 1 (by rfl) ⟨1563863, by rfl⟩ : syracuseStep 2085151 = 3127727) B3127727
theorem B3127733 : Blo 2083435 3127733 := bbase (se 5 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 3127733 = 293225) (by norm_num)
theorem B2085155 : Blo 2083435 2085155 := bstep (se 1 (by rfl) ⟨1563866, by rfl⟩ : syracuseStep 2085155 = 3127733) B3127733
theorem B5278061 : Blo 2083435 5278061 := bbase (se 3 (by rfl) ⟨989636, by rfl⟩ : syracuseStep 5278061 = 1979273) (by norm_num)
theorem B3518707 : Blo 2083435 3518707 := bstep (se 1 (by rfl) ⟨2639030, by rfl⟩ : syracuseStep 3518707 = 5278061) B5278061
theorem B4691609 : Blo 2083435 4691609 := bstep (se 2 (by rfl) ⟨1759353, by rfl⟩ : syracuseStep 4691609 = 3518707) B3518707
theorem B3127739 : Blo 2083435 3127739 := bstep (se 1 (by rfl) ⟨2345804, by rfl⟩ : syracuseStep 3127739 = 4691609) B4691609
theorem B2085159 : Blo 2083435 2085159 := bstep (se 1 (by rfl) ⟨1563869, by rfl⟩ : syracuseStep 2085159 = 3127739) B3127739
theorem B2345809 : Blo 2083435 2345809 := bbase (se 2 (by rfl) ⟨879678, by rfl⟩ : syracuseStep 2345809 = 1759357) (by norm_num)
theorem B3127745 : Blo 2083435 3127745 := bstep (se 2 (by rfl) ⟨1172904, by rfl⟩ : syracuseStep 3127745 = 2345809) B2345809
theorem B2085163 : Blo 2083435 2085163 := bstep (se 1 (by rfl) ⟨1563872, by rfl⟩ : syracuseStep 2085163 = 3127745) B3127745
theorem B3340037 : Blo 2083435 3340037 := bbase (se 4 (by rfl) ⟨313128, by rfl⟩ : syracuseStep 3340037 = 626257) (by norm_num)
theorem B2226691 : Blo 2083435 2226691 := bstep (se 1 (by rfl) ⟨1670018, by rfl⟩ : syracuseStep 2226691 = 3340037) B3340037
theorem B2968921 : Blo 2083435 2968921 := bstep (se 2 (by rfl) ⟨1113345, by rfl⟩ : syracuseStep 2968921 = 2226691) B2226691
theorem B3958561 : Blo 2083435 3958561 := bstep (se 2 (by rfl) ⟨1484460, by rfl⟩ : syracuseStep 3958561 = 2968921) B2968921
theorem B5278081 : Blo 2083435 5278081 := bstep (se 2 (by rfl) ⟨1979280, by rfl⟩ : syracuseStep 5278081 = 3958561) B3958561
theorem B7037441 : Blo 2083435 7037441 := bstep (se 2 (by rfl) ⟨2639040, by rfl⟩ : syracuseStep 7037441 = 5278081) B5278081
theorem B4691627 : Blo 2083435 4691627 := bstep (se 1 (by rfl) ⟨3518720, by rfl⟩ : syracuseStep 4691627 = 7037441) B7037441
theorem B3127751 : Blo 2083435 3127751 := bstep (se 1 (by rfl) ⟨2345813, by rfl⟩ : syracuseStep 3127751 = 4691627) B4691627
theorem B2085167 : Blo 2083435 2085167 := bstep (se 1 (by rfl) ⟨1563875, by rfl⟩ : syracuseStep 2085167 = 3127751) B3127751
theorem B3127757 : Blo 2083435 3127757 := bbase (se 3 (by rfl) ⟨586454, by rfl⟩ : syracuseStep 3127757 = 1172909) (by norm_num)
theorem B2085171 : Blo 2083435 2085171 := bstep (se 1 (by rfl) ⟨1563878, by rfl⟩ : syracuseStep 2085171 = 3127757) B3127757
theorem B4691645 : Blo 2083435 4691645 := bbase (se 3 (by rfl) ⟨879683, by rfl⟩ : syracuseStep 4691645 = 1759367) (by norm_num)
theorem B3127763 : Blo 2083435 3127763 := bstep (se 1 (by rfl) ⟨2345822, by rfl⟩ : syracuseStep 3127763 = 4691645) B4691645
theorem B2085175 : Blo 2083435 2085175 := bstep (se 1 (by rfl) ⟨1563881, by rfl⟩ : syracuseStep 2085175 = 3127763) B3127763
theorem B3518741 : Blo 2083435 3518741 := bbase (se 6 (by rfl) ⟨82470, by rfl⟩ : syracuseStep 3518741 = 164941) (by norm_num)
theorem B2345827 : Blo 2083435 2345827 := bstep (se 1 (by rfl) ⟨1759370, by rfl⟩ : syracuseStep 2345827 = 3518741) B3518741
theorem B3127769 : Blo 2083435 3127769 := bstep (se 2 (by rfl) ⟨1172913, by rfl⟩ : syracuseStep 3127769 = 2345827) B2345827
theorem B2085179 : Blo 2083435 2085179 := bstep (se 1 (by rfl) ⟨1563884, by rfl⟩ : syracuseStep 2085179 = 3127769) B3127769
theorem B2113633 : Blo 2083435 2113633 := bbase (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) (by norm_num)
theorem B11272709 : Blo 2083435 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B30060557 : Blo 2083435 30060557 := bstep (se 3 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 30060557 = 11272709) B11272709
theorem B20040371 : Blo 2083435 20040371 := bstep (se 1 (by rfl) ⟨15030278, by rfl⟩ : syracuseStep 20040371 = 30060557) B30060557
theorem B13360247 : Blo 2083435 13360247 := bstep (se 1 (by rfl) ⟨10020185, by rfl⟩ : syracuseStep 13360247 = 20040371) B20040371
theorem B8906831 : Blo 2083435 8906831 := bstep (se 1 (by rfl) ⟨6680123, by rfl⟩ : syracuseStep 8906831 = 13360247) B13360247
theorem B5937887 : Blo 2083435 5937887 := bstep (se 1 (by rfl) ⟨4453415, by rfl⟩ : syracuseStep 5937887 = 8906831) B8906831
theorem B15834365 : Blo 2083435 15834365 := bstep (se 3 (by rfl) ⟨2968943, by rfl⟩ : syracuseStep 15834365 = 5937887) B5937887
theorem B10556243 : Blo 2083435 10556243 := bstep (se 1 (by rfl) ⟨7917182, by rfl⟩ : syracuseStep 10556243 = 15834365) B15834365
theorem B7037495 : Blo 2083435 7037495 := bstep (se 1 (by rfl) ⟨5278121, by rfl⟩ : syracuseStep 7037495 = 10556243) B10556243
theorem B4691663 : Blo 2083435 4691663 := bstep (se 1 (by rfl) ⟨3518747, by rfl⟩ : syracuseStep 4691663 = 7037495) B7037495
theorem B3127775 : Blo 2083435 3127775 := bstep (se 1 (by rfl) ⟨2345831, by rfl⟩ : syracuseStep 3127775 = 4691663) B4691663
theorem B2085183 : Blo 2083435 2085183 := bstep (se 1 (by rfl) ⟨1563887, by rfl⟩ : syracuseStep 2085183 = 3127775) B3127775
theorem B3127781 : Blo 2083435 3127781 := bbase (se 4 (by rfl) ⟨293229, by rfl⟩ : syracuseStep 3127781 = 586459) (by norm_num)
theorem B2085187 : Blo 2083435 2085187 := bstep (se 1 (by rfl) ⟨1563890, by rfl⟩ : syracuseStep 2085187 = 3127781) B3127781
theorem B2818189 : Blo 2083435 2818189 := bbase (se 3 (by rfl) ⟨528410, by rfl⟩ : syracuseStep 2818189 = 1056821) (by norm_num)
theorem B3757585 : Blo 2083435 3757585 := bstep (se 2 (by rfl) ⟨1409094, by rfl⟩ : syracuseStep 3757585 = 2818189) B2818189
theorem B5010113 : Blo 2083435 5010113 := bstep (se 2 (by rfl) ⟨1878792, by rfl⟩ : syracuseStep 5010113 = 3757585) B3757585
theorem B13360301 : Blo 2083435 13360301 := bstep (se 3 (by rfl) ⟨2505056, by rfl⟩ : syracuseStep 13360301 = 5010113) B5010113
theorem B8906867 : Blo 2083435 8906867 := bstep (se 1 (by rfl) ⟨6680150, by rfl⟩ : syracuseStep 8906867 = 13360301) B13360301
theorem B5937911 : Blo 2083435 5937911 := bstep (se 1 (by rfl) ⟨4453433, by rfl⟩ : syracuseStep 5937911 = 8906867) B8906867
theorem B3958607 : Blo 2083435 3958607 := bstep (se 1 (by rfl) ⟨2968955, by rfl⟩ : syracuseStep 3958607 = 5937911) B5937911
theorem B2639071 : Blo 2083435 2639071 := bstep (se 1 (by rfl) ⟨1979303, by rfl⟩ : syracuseStep 2639071 = 3958607) B3958607
theorem B3518761 : Blo 2083435 3518761 := bstep (se 2 (by rfl) ⟨1319535, by rfl⟩ : syracuseStep 3518761 = 2639071) B2639071
theorem B4691681 : Blo 2083435 4691681 := bstep (se 2 (by rfl) ⟨1759380, by rfl⟩ : syracuseStep 4691681 = 3518761) B3518761
theorem B3127787 : Blo 2083435 3127787 := bstep (se 1 (by rfl) ⟨2345840, by rfl⟩ : syracuseStep 3127787 = 4691681) B4691681
theorem B2085191 : Blo 2083435 2085191 := bstep (se 1 (by rfl) ⟨1563893, by rfl⟩ : syracuseStep 2085191 = 3127787) B3127787
theorem B2345845 : Blo 2083435 2345845 := bbase (se 5 (by rfl) ⟨109961, by rfl⟩ : syracuseStep 2345845 = 219923) (by norm_num)
theorem B3127793 : Blo 2083435 3127793 := bstep (se 2 (by rfl) ⟨1172922, by rfl⟩ : syracuseStep 3127793 = 2345845) B2345845
theorem B2085195 : Blo 2083435 2085195 := bstep (se 1 (by rfl) ⟨1563896, by rfl⟩ : syracuseStep 2085195 = 3127793) B3127793
theorem B2639081 : Blo 2083435 2639081 := bbase (se 2 (by rfl) ⟨989655, by rfl⟩ : syracuseStep 2639081 = 1979311) (by norm_num)
theorem B7037549 : Blo 2083435 7037549 := bstep (se 3 (by rfl) ⟨1319540, by rfl⟩ : syracuseStep 7037549 = 2639081) B2639081
theorem B4691699 : Blo 2083435 4691699 := bstep (se 1 (by rfl) ⟨3518774, by rfl⟩ : syracuseStep 4691699 = 7037549) B7037549
theorem B3127799 : Blo 2083435 3127799 := bstep (se 1 (by rfl) ⟨2345849, by rfl⟩ : syracuseStep 3127799 = 4691699) B4691699
theorem B2085199 : Blo 2083435 2085199 := bstep (se 1 (by rfl) ⟨1563899, by rfl⟩ : syracuseStep 2085199 = 3127799) B3127799
theorem B3127805 : Blo 2083435 3127805 := bbase (se 3 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 3127805 = 1172927) (by norm_num)
theorem B2085203 : Blo 2083435 2085203 := bstep (se 1 (by rfl) ⟨1563902, by rfl⟩ : syracuseStep 2085203 = 3127805) B3127805
theorem B4691717 : Blo 2083435 4691717 := bbase (se 4 (by rfl) ⟨439848, by rfl⟩ : syracuseStep 4691717 = 879697) (by norm_num)
theorem B3127811 : Blo 2083435 3127811 := bstep (se 1 (by rfl) ⟨2345858, by rfl⟩ : syracuseStep 3127811 = 4691717) B4691717
theorem B2085207 : Blo 2083435 2085207 := bstep (se 1 (by rfl) ⟨1563905, by rfl⟩ : syracuseStep 2085207 = 3127811) B3127811
theorem B3958645 : Blo 2083435 3958645 := bbase (se 5 (by rfl) ⟨185561, by rfl⟩ : syracuseStep 3958645 = 371123) (by norm_num)
theorem B5278193 : Blo 2083435 5278193 := bstep (se 2 (by rfl) ⟨1979322, by rfl⟩ : syracuseStep 5278193 = 3958645) B3958645
theorem B3518795 : Blo 2083435 3518795 := bstep (se 1 (by rfl) ⟨2639096, by rfl⟩ : syracuseStep 3518795 = 5278193) B5278193
theorem B2345863 : Blo 2083435 2345863 := bstep (se 1 (by rfl) ⟨1759397, by rfl⟩ : syracuseStep 2345863 = 3518795) B3518795
theorem B3127817 : Blo 2083435 3127817 := bstep (se 2 (by rfl) ⟨1172931, by rfl⟩ : syracuseStep 3127817 = 2345863) B2345863
theorem B2085211 : Blo 2083435 2085211 := bstep (se 1 (by rfl) ⟨1563908, by rfl⟩ : syracuseStep 2085211 = 3127817) B3127817
theorem B10556405 : Blo 2083435 10556405 := bbase (se 5 (by rfl) ⟨494831, by rfl⟩ : syracuseStep 10556405 = 989663) (by norm_num)
theorem B7037603 : Blo 2083435 7037603 := bstep (se 1 (by rfl) ⟨5278202, by rfl⟩ : syracuseStep 7037603 = 10556405) B10556405
theorem B4691735 : Blo 2083435 4691735 := bstep (se 1 (by rfl) ⟨3518801, by rfl⟩ : syracuseStep 4691735 = 7037603) B7037603
theorem B3127823 : Blo 2083435 3127823 := bstep (se 1 (by rfl) ⟨2345867, by rfl⟩ : syracuseStep 3127823 = 4691735) B4691735
theorem B2085215 : Blo 2083435 2085215 := bstep (se 1 (by rfl) ⟨1563911, by rfl⟩ : syracuseStep 2085215 = 3127823) B3127823
theorem B3127829 : Blo 2083435 3127829 := bbase (se 6 (by rfl) ⟨73308, by rfl⟩ : syracuseStep 3127829 = 146617) (by norm_num)
theorem B2085219 : Blo 2083435 2085219 := bstep (se 1 (by rfl) ⟨1563914, by rfl⟩ : syracuseStep 2085219 = 3127829) B3127829
theorem B17814005 : Blo 2083435 17814005 := bbase (se 5 (by rfl) ⟨835031, by rfl⟩ : syracuseStep 17814005 = 1670063) (by norm_num)
theorem B11876003 : Blo 2083435 11876003 := bstep (se 1 (by rfl) ⟨8907002, by rfl⟩ : syracuseStep 11876003 = 17814005) B17814005
theorem B7917335 : Blo 2083435 7917335 := bstep (se 1 (by rfl) ⟨5938001, by rfl⟩ : syracuseStep 7917335 = 11876003) B11876003
theorem B5278223 : Blo 2083435 5278223 := bstep (se 1 (by rfl) ⟨3958667, by rfl⟩ : syracuseStep 5278223 = 7917335) B7917335
theorem B3518815 : Blo 2083435 3518815 := bstep (se 1 (by rfl) ⟨2639111, by rfl⟩ : syracuseStep 3518815 = 5278223) B5278223
theorem B4691753 : Blo 2083435 4691753 := bstep (se 2 (by rfl) ⟨1759407, by rfl⟩ : syracuseStep 4691753 = 3518815) B3518815
theorem B3127835 : Blo 2083435 3127835 := bstep (se 1 (by rfl) ⟨2345876, by rfl⟩ : syracuseStep 3127835 = 4691753) B4691753
theorem B2085223 : Blo 2083435 2085223 := bstep (se 1 (by rfl) ⟨1563917, by rfl⟩ : syracuseStep 2085223 = 3127835) B3127835
theorem B2345881 : Blo 2083435 2345881 := bbase (se 2 (by rfl) ⟨879705, by rfl⟩ : syracuseStep 2345881 = 1759411) (by norm_num)
theorem B3127841 : Blo 2083435 3127841 := bstep (se 2 (by rfl) ⟨1172940, by rfl⟩ : syracuseStep 3127841 = 2345881) B2345881
theorem B2085227 : Blo 2083435 2085227 := bstep (se 1 (by rfl) ⟨1563920, by rfl⟩ : syracuseStep 2085227 = 3127841) B3127841
theorem B7917365 : Blo 2083435 7917365 := bbase (se 5 (by rfl) ⟨371126, by rfl⟩ : syracuseStep 7917365 = 742253) (by norm_num)
theorem B5278243 : Blo 2083435 5278243 := bstep (se 1 (by rfl) ⟨3958682, by rfl⟩ : syracuseStep 5278243 = 7917365) B7917365
theorem B7037657 : Blo 2083435 7037657 := bstep (se 2 (by rfl) ⟨2639121, by rfl⟩ : syracuseStep 7037657 = 5278243) B5278243
theorem B4691771 : Blo 2083435 4691771 := bstep (se 1 (by rfl) ⟨3518828, by rfl⟩ : syracuseStep 4691771 = 7037657) B7037657
theorem B3127847 : Blo 2083435 3127847 := bstep (se 1 (by rfl) ⟨2345885, by rfl⟩ : syracuseStep 3127847 = 4691771) B4691771
theorem B2085231 : Blo 2083435 2085231 := bstep (se 1 (by rfl) ⟨1563923, by rfl⟩ : syracuseStep 2085231 = 3127847) B3127847
theorem B3127853 : Blo 2083435 3127853 := bbase (se 3 (by rfl) ⟨586472, by rfl⟩ : syracuseStep 3127853 = 1172945) (by norm_num)
theorem B2085235 : Blo 2083435 2085235 := bstep (se 1 (by rfl) ⟨1563926, by rfl⟩ : syracuseStep 2085235 = 3127853) B3127853
theorem B4691789 : Blo 2083435 4691789 := bbase (se 3 (by rfl) ⟨879710, by rfl⟩ : syracuseStep 4691789 = 1759421) (by norm_num)
theorem B3127859 : Blo 2083435 3127859 := bstep (se 1 (by rfl) ⟨2345894, by rfl⟩ : syracuseStep 3127859 = 4691789) B4691789
theorem B2085239 : Blo 2083435 2085239 := bstep (se 1 (by rfl) ⟨1563929, by rfl⟩ : syracuseStep 2085239 = 3127859) B3127859
theorem B2639137 : Blo 2083435 2639137 := bbase (se 2 (by rfl) ⟨989676, by rfl⟩ : syracuseStep 2639137 = 1979353) (by norm_num)
theorem B3518849 : Blo 2083435 3518849 := bstep (se 2 (by rfl) ⟨1319568, by rfl⟩ : syracuseStep 3518849 = 2639137) B2639137
theorem B2345899 : Blo 2083435 2345899 := bstep (se 1 (by rfl) ⟨1759424, by rfl⟩ : syracuseStep 2345899 = 3518849) B3518849
theorem B3127865 : Blo 2083435 3127865 := bstep (se 2 (by rfl) ⟨1172949, by rfl⟩ : syracuseStep 3127865 = 2345899) B2345899
theorem B2085243 : Blo 2083435 2085243 := bstep (se 1 (by rfl) ⟨1563932, by rfl⟩ : syracuseStep 2085243 = 3127865) B3127865
theorem B23752277 : Blo 2083435 23752277 := bbase (se 8 (by rfl) ⟨139173, by rfl⟩ : syracuseStep 23752277 = 278347) (by norm_num)
theorem B15834851 : Blo 2083435 15834851 := bstep (se 1 (by rfl) ⟨11876138, by rfl⟩ : syracuseStep 15834851 = 23752277) B23752277
theorem B10556567 : Blo 2083435 10556567 := bstep (se 1 (by rfl) ⟨7917425, by rfl⟩ : syracuseStep 10556567 = 15834851) B15834851
theorem B7037711 : Blo 2083435 7037711 := bstep (se 1 (by rfl) ⟨5278283, by rfl⟩ : syracuseStep 7037711 = 10556567) B10556567
theorem B4691807 : Blo 2083435 4691807 := bstep (se 1 (by rfl) ⟨3518855, by rfl⟩ : syracuseStep 4691807 = 7037711) B7037711
theorem B3127871 : Blo 2083435 3127871 := bstep (se 1 (by rfl) ⟨2345903, by rfl⟩ : syracuseStep 3127871 = 4691807) B4691807
theorem B2085247 : Blo 2083435 2085247 := bstep (se 1 (by rfl) ⟨1563935, by rfl⟩ : syracuseStep 2085247 = 3127871) B3127871
theorem B3127877 : Blo 2083435 3127877 := bbase (se 4 (by rfl) ⟨293238, by rfl⟩ : syracuseStep 3127877 = 586477) (by norm_num)
theorem B2085251 : Blo 2083435 2085251 := bstep (se 1 (by rfl) ⟨1563938, by rfl⟩ : syracuseStep 2085251 = 3127877) B3127877
theorem B3518869 : Blo 2083435 3518869 := bbase (se 6 (by rfl) ⟨82473, by rfl⟩ : syracuseStep 3518869 = 164947) (by norm_num)
theorem B4691825 : Blo 2083435 4691825 := bstep (se 2 (by rfl) ⟨1759434, by rfl⟩ : syracuseStep 4691825 = 3518869) B3518869
theorem B3127883 : Blo 2083435 3127883 := bstep (se 1 (by rfl) ⟨2345912, by rfl⟩ : syracuseStep 3127883 = 4691825) B4691825
theorem B2085255 : Blo 2083435 2085255 := bstep (se 1 (by rfl) ⟨1563941, by rfl⟩ : syracuseStep 2085255 = 3127883) B3127883
theorem B2345917 : Blo 2083435 2345917 := bbase (se 3 (by rfl) ⟨439859, by rfl⟩ : syracuseStep 2345917 = 879719) (by norm_num)
theorem B3127889 : Blo 2083435 3127889 := bstep (se 2 (by rfl) ⟨1172958, by rfl⟩ : syracuseStep 3127889 = 2345917) B2345917
theorem B2085259 : Blo 2083435 2085259 := bstep (se 1 (by rfl) ⟨1563944, by rfl⟩ : syracuseStep 2085259 = 3127889) B3127889
theorem B7037765 : Blo 2083435 7037765 := bbase (se 4 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 7037765 = 1319581) (by norm_num)
theorem B4691843 : Blo 2083435 4691843 := bstep (se 1 (by rfl) ⟨3518882, by rfl⟩ : syracuseStep 4691843 = 7037765) B7037765
theorem B3127895 : Blo 2083435 3127895 := bstep (se 1 (by rfl) ⟨2345921, by rfl⟩ : syracuseStep 3127895 = 4691843) B4691843
theorem B2085263 : Blo 2083435 2085263 := bstep (se 1 (by rfl) ⟨1563947, by rfl⟩ : syracuseStep 2085263 = 3127895) B3127895
theorem B3127901 : Blo 2083435 3127901 := bbase (se 3 (by rfl) ⟨586481, by rfl⟩ : syracuseStep 3127901 = 1172963) (by norm_num)
theorem B2085267 : Blo 2083435 2085267 := bstep (se 1 (by rfl) ⟨1563950, by rfl⟩ : syracuseStep 2085267 = 3127901) B3127901
theorem B4691861 : Blo 2083435 4691861 := bbase (se 6 (by rfl) ⟨109965, by rfl⟩ : syracuseStep 4691861 = 219931) (by norm_num)
theorem B3127907 : Blo 2083435 3127907 := bstep (se 1 (by rfl) ⟨2345930, by rfl⟩ : syracuseStep 3127907 = 4691861) B4691861
theorem B2085271 : Blo 2083435 2085271 := bstep (se 1 (by rfl) ⟨1563953, by rfl⟩ : syracuseStep 2085271 = 3127907) B3127907
theorem B4453613 : Blo 2083435 4453613 := bbase (se 3 (by rfl) ⟨835052, by rfl⟩ : syracuseStep 4453613 = 1670105) (by norm_num)
theorem B2969075 : Blo 2083435 2969075 := bstep (se 1 (by rfl) ⟨2226806, by rfl⟩ : syracuseStep 2969075 = 4453613) B4453613
theorem B7917533 : Blo 2083435 7917533 := bstep (se 3 (by rfl) ⟨1484537, by rfl⟩ : syracuseStep 7917533 = 2969075) B2969075
theorem B5278355 : Blo 2083435 5278355 := bstep (se 1 (by rfl) ⟨3958766, by rfl⟩ : syracuseStep 5278355 = 7917533) B7917533
theorem B3518903 : Blo 2083435 3518903 := bstep (se 1 (by rfl) ⟨2639177, by rfl⟩ : syracuseStep 3518903 = 5278355) B5278355
theorem B2345935 : Blo 2083435 2345935 := bstep (se 1 (by rfl) ⟨1759451, by rfl⟩ : syracuseStep 2345935 = 3518903) B3518903
theorem B3127913 : Blo 2083435 3127913 := bstep (se 2 (by rfl) ⟨1172967, by rfl⟩ : syracuseStep 3127913 = 2345935) B2345935
theorem B2085275 : Blo 2083435 2085275 := bstep (se 1 (by rfl) ⟨1563956, by rfl⟩ : syracuseStep 2085275 = 3127913) B3127913
theorem B12038357 : Blo 2083435 12038357 := bbase (se 7 (by rfl) ⟨141074, by rfl⟩ : syracuseStep 12038357 = 282149) (by norm_num)
theorem B8025571 : Blo 2083435 8025571 := bstep (se 1 (by rfl) ⟨6019178, by rfl⟩ : syracuseStep 8025571 = 12038357) B12038357
theorem B10700761 : Blo 2083435 10700761 := bstep (se 2 (by rfl) ⟨4012785, by rfl⟩ : syracuseStep 10700761 = 8025571) B8025571
theorem B14267681 : Blo 2083435 14267681 := bstep (se 2 (by rfl) ⟨5350380, by rfl⟩ : syracuseStep 14267681 = 10700761) B10700761
theorem B9511787 : Blo 2083435 9511787 := bstep (se 1 (by rfl) ⟨7133840, by rfl⟩ : syracuseStep 9511787 = 14267681) B14267681
theorem B25364765 : Blo 2083435 25364765 := bstep (se 3 (by rfl) ⟨4755893, by rfl⟩ : syracuseStep 25364765 = 9511787) B9511787
theorem B16909843 : Blo 2083435 16909843 := bstep (se 1 (by rfl) ⟨12682382, by rfl⟩ : syracuseStep 16909843 = 25364765) B25364765
theorem B22546457 : Blo 2083435 22546457 := bstep (se 2 (by rfl) ⟨8454921, by rfl⟩ : syracuseStep 22546457 = 16909843) B16909843
theorem B15030971 : Blo 2083435 15030971 := bstep (se 1 (by rfl) ⟨11273228, by rfl⟩ : syracuseStep 15030971 = 22546457) B22546457
theorem B10020647 : Blo 2083435 10020647 := bstep (se 1 (by rfl) ⟨7515485, by rfl⟩ : syracuseStep 10020647 = 15030971) B15030971
theorem B6680431 : Blo 2083435 6680431 := bstep (se 1 (by rfl) ⟨5010323, by rfl⟩ : syracuseStep 6680431 = 10020647) B10020647
theorem B8907241 : Blo 2083435 8907241 := bstep (se 2 (by rfl) ⟨3340215, by rfl⟩ : syracuseStep 8907241 = 6680431) B6680431
theorem B11876321 : Blo 2083435 11876321 := bstep (se 2 (by rfl) ⟨4453620, by rfl⟩ : syracuseStep 11876321 = 8907241) B8907241
theorem B7917547 : Blo 2083435 7917547 := bstep (se 1 (by rfl) ⟨5938160, by rfl⟩ : syracuseStep 7917547 = 11876321) B11876321
theorem B10556729 : Blo 2083435 10556729 := bstep (se 2 (by rfl) ⟨3958773, by rfl⟩ : syracuseStep 10556729 = 7917547) B7917547
theorem B7037819 : Blo 2083435 7037819 := bstep (se 1 (by rfl) ⟨5278364, by rfl⟩ : syracuseStep 7037819 = 10556729) B10556729
theorem B4691879 : Blo 2083435 4691879 := bstep (se 1 (by rfl) ⟨3518909, by rfl⟩ : syracuseStep 4691879 = 7037819) B7037819
theorem B3127919 : Blo 2083435 3127919 := bstep (se 1 (by rfl) ⟨2345939, by rfl⟩ : syracuseStep 3127919 = 4691879) B4691879
theorem B2085279 : Blo 2083435 2085279 := bstep (se 1 (by rfl) ⟨1563959, by rfl⟩ : syracuseStep 2085279 = 3127919) B3127919
theorem B3127925 : Blo 2083435 3127925 := bbase (se 5 (by rfl) ⟨146621, by rfl⟩ : syracuseStep 3127925 = 293243) (by norm_num)
theorem B2085283 : Blo 2083435 2085283 := bstep (se 1 (by rfl) ⟨1563962, by rfl⟩ : syracuseStep 2085283 = 3127925) B3127925
theorem B3958789 : Blo 2083435 3958789 := bbase (se 4 (by rfl) ⟨371136, by rfl⟩ : syracuseStep 3958789 = 742273) (by norm_num)
theorem B5278385 : Blo 2083435 5278385 := bstep (se 2 (by rfl) ⟨1979394, by rfl⟩ : syracuseStep 5278385 = 3958789) B3958789
theorem B3518923 : Blo 2083435 3518923 := bstep (se 1 (by rfl) ⟨2639192, by rfl⟩ : syracuseStep 3518923 = 5278385) B5278385
theorem B4691897 : Blo 2083435 4691897 := bstep (se 2 (by rfl) ⟨1759461, by rfl⟩ : syracuseStep 4691897 = 3518923) B3518923
theorem B3127931 : Blo 2083435 3127931 := bstep (se 1 (by rfl) ⟨2345948, by rfl⟩ : syracuseStep 3127931 = 4691897) B4691897
theorem B2085287 : Blo 2083435 2085287 := bstep (se 1 (by rfl) ⟨1563965, by rfl⟩ : syracuseStep 2085287 = 3127931) B3127931
theorem B2345953 : Blo 2083435 2345953 := bbase (se 2 (by rfl) ⟨879732, by rfl⟩ : syracuseStep 2345953 = 1759465) (by norm_num)
theorem B3127937 : Blo 2083435 3127937 := bstep (se 2 (by rfl) ⟨1172976, by rfl⟩ : syracuseStep 3127937 = 2345953) B2345953
theorem B2085291 : Blo 2083435 2085291 := bstep (se 1 (by rfl) ⟨1563968, by rfl⟩ : syracuseStep 2085291 = 3127937) B3127937
theorem B5278405 : Blo 2083435 5278405 := bbase (se 4 (by rfl) ⟨494850, by rfl⟩ : syracuseStep 5278405 = 989701) (by norm_num)
theorem B7037873 : Blo 2083435 7037873 := bstep (se 2 (by rfl) ⟨2639202, by rfl⟩ : syracuseStep 7037873 = 5278405) B5278405
theorem B4691915 : Blo 2083435 4691915 := bstep (se 1 (by rfl) ⟨3518936, by rfl⟩ : syracuseStep 4691915 = 7037873) B7037873
theorem B3127943 : Blo 2083435 3127943 := bstep (se 1 (by rfl) ⟨2345957, by rfl⟩ : syracuseStep 3127943 = 4691915) B4691915
theorem B2085295 : Blo 2083435 2085295 := bstep (se 1 (by rfl) ⟨1563971, by rfl⟩ : syracuseStep 2085295 = 3127943) B3127943
theorem B3127949 : Blo 2083435 3127949 := bbase (se 3 (by rfl) ⟨586490, by rfl⟩ : syracuseStep 3127949 = 1172981) (by norm_num)
theorem B2085299 : Blo 2083435 2085299 := bstep (se 1 (by rfl) ⟨1563974, by rfl⟩ : syracuseStep 2085299 = 3127949) B3127949
theorem B4691933 : Blo 2083435 4691933 := bbase (se 3 (by rfl) ⟨879737, by rfl⟩ : syracuseStep 4691933 = 1759475) (by norm_num)
theorem B3127955 : Blo 2083435 3127955 := bstep (se 1 (by rfl) ⟨2345966, by rfl⟩ : syracuseStep 3127955 = 4691933) B4691933
theorem B2085303 : Blo 2083435 2085303 := bstep (se 1 (by rfl) ⟨1563977, by rfl⟩ : syracuseStep 2085303 = 3127955) B3127955
theorem B3518957 : Blo 2083435 3518957 := bbase (se 3 (by rfl) ⟨659804, by rfl⟩ : syracuseStep 3518957 = 1319609) (by norm_num)
theorem B2345971 : Blo 2083435 2345971 := bstep (se 1 (by rfl) ⟨1759478, by rfl⟩ : syracuseStep 2345971 = 3518957) B3518957
theorem B3127961 : Blo 2083435 3127961 := bstep (se 2 (by rfl) ⟨1172985, by rfl⟩ : syracuseStep 3127961 = 2345971) B2345971
theorem B2085307 : Blo 2083435 2085307 := bstep (se 1 (by rfl) ⟨1563980, by rfl⟩ : syracuseStep 2085307 = 3127961) B3127961
theorem B26722133 : Blo 2083435 26722133 := bbase (se 9 (by rfl) ⟨78287, by rfl⟩ : syracuseStep 26722133 = 156575) (by norm_num)
theorem B17814755 : Blo 2083435 17814755 := bstep (se 1 (by rfl) ⟨13361066, by rfl⟩ : syracuseStep 17814755 = 26722133) B26722133
theorem B11876503 : Blo 2083435 11876503 := bstep (se 1 (by rfl) ⟨8907377, by rfl⟩ : syracuseStep 11876503 = 17814755) B17814755
theorem B15835337 : Blo 2083435 15835337 := bstep (se 2 (by rfl) ⟨5938251, by rfl⟩ : syracuseStep 15835337 = 11876503) B11876503
theorem B10556891 : Blo 2083435 10556891 := bstep (se 1 (by rfl) ⟨7917668, by rfl⟩ : syracuseStep 10556891 = 15835337) B15835337
theorem B7037927 : Blo 2083435 7037927 := bstep (se 1 (by rfl) ⟨5278445, by rfl⟩ : syracuseStep 7037927 = 10556891) B10556891
theorem B4691951 : Blo 2083435 4691951 := bstep (se 1 (by rfl) ⟨3518963, by rfl⟩ : syracuseStep 4691951 = 7037927) B7037927
theorem B3127967 : Blo 2083435 3127967 := bstep (se 1 (by rfl) ⟨2345975, by rfl⟩ : syracuseStep 3127967 = 4691951) B4691951
theorem B2085311 : Blo 2083435 2085311 := bstep (se 1 (by rfl) ⟨1563983, by rfl⟩ : syracuseStep 2085311 = 3127967) B3127967
theorem B3127973 : Blo 2083435 3127973 := bbase (se 4 (by rfl) ⟨293247, by rfl⟩ : syracuseStep 3127973 = 586495) (by norm_num)
theorem B2085315 : Blo 2083435 2085315 := bstep (se 1 (by rfl) ⟨1563986, by rfl⟩ : syracuseStep 2085315 = 3127973) B3127973
theorem B2639233 : Blo 2083435 2639233 := bbase (se 2 (by rfl) ⟨989712, by rfl⟩ : syracuseStep 2639233 = 1979425) (by norm_num)
theorem B3518977 : Blo 2083435 3518977 := bstep (se 2 (by rfl) ⟨1319616, by rfl⟩ : syracuseStep 3518977 = 2639233) B2639233
theorem B4691969 : Blo 2083435 4691969 := bstep (se 2 (by rfl) ⟨1759488, by rfl⟩ : syracuseStep 4691969 = 3518977) B3518977
theorem B3127979 : Blo 2083435 3127979 := bstep (se 1 (by rfl) ⟨2345984, by rfl⟩ : syracuseStep 3127979 = 4691969) B4691969
theorem B2085319 : Blo 2083435 2085319 := bstep (se 1 (by rfl) ⟨1563989, by rfl⟩ : syracuseStep 2085319 = 3127979) B3127979
theorem B2345989 : Blo 2083435 2345989 := bbase (se 4 (by rfl) ⟨219936, by rfl⟩ : syracuseStep 2345989 = 439873) (by norm_num)
theorem B3127985 : Blo 2083435 3127985 := bstep (se 2 (by rfl) ⟨1172994, by rfl⟩ : syracuseStep 3127985 = 2345989) B2345989
theorem B2085323 : Blo 2083435 2085323 := bstep (se 1 (by rfl) ⟨1563992, by rfl⟩ : syracuseStep 2085323 = 3127985) B3127985
theorem B2969149 : Blo 2083435 2969149 := bbase (se 3 (by rfl) ⟨556715, by rfl⟩ : syracuseStep 2969149 = 1113431) (by norm_num)
theorem B3958865 : Blo 2083435 3958865 := bstep (se 2 (by rfl) ⟨1484574, by rfl⟩ : syracuseStep 3958865 = 2969149) B2969149
theorem B2639243 : Blo 2083435 2639243 := bstep (se 1 (by rfl) ⟨1979432, by rfl⟩ : syracuseStep 2639243 = 3958865) B3958865
theorem B7037981 : Blo 2083435 7037981 := bstep (se 3 (by rfl) ⟨1319621, by rfl⟩ : syracuseStep 7037981 = 2639243) B2639243
theorem B4691987 : Blo 2083435 4691987 := bstep (se 1 (by rfl) ⟨3518990, by rfl⟩ : syracuseStep 4691987 = 7037981) B7037981
theorem B3127991 : Blo 2083435 3127991 := bstep (se 1 (by rfl) ⟨2345993, by rfl⟩ : syracuseStep 3127991 = 4691987) B4691987
theorem B2085327 : Blo 2083435 2085327 := bstep (se 1 (by rfl) ⟨1563995, by rfl⟩ : syracuseStep 2085327 = 3127991) B3127991
theorem B3127997 : Blo 2083435 3127997 := bbase (se 3 (by rfl) ⟨586499, by rfl⟩ : syracuseStep 3127997 = 1172999) (by norm_num)
theorem B2085331 : Blo 2083435 2085331 := bstep (se 1 (by rfl) ⟨1563998, by rfl⟩ : syracuseStep 2085331 = 3127997) B3127997
theorem B4692005 : Blo 2083435 4692005 := bbase (se 4 (by rfl) ⟨439875, by rfl⟩ : syracuseStep 4692005 = 879751) (by norm_num)
theorem B3128003 : Blo 2083435 3128003 := bstep (se 1 (by rfl) ⟨2346002, by rfl⟩ : syracuseStep 3128003 = 4692005) B4692005
theorem B2085335 : Blo 2083435 2085335 := bstep (se 1 (by rfl) ⟨1564001, by rfl⟩ : syracuseStep 2085335 = 3128003) B3128003
theorem B5278517 : Blo 2083435 5278517 := bbase (se 5 (by rfl) ⟨247430, by rfl⟩ : syracuseStep 5278517 = 494861) (by norm_num)
theorem B3519011 : Blo 2083435 3519011 := bstep (se 1 (by rfl) ⟨2639258, by rfl⟩ : syracuseStep 3519011 = 5278517) B5278517
theorem B2346007 : Blo 2083435 2346007 := bstep (se 1 (by rfl) ⟨1759505, by rfl⟩ : syracuseStep 2346007 = 3519011) B3519011
theorem B3128009 : Blo 2083435 3128009 := bstep (se 2 (by rfl) ⟨1173003, by rfl⟩ : syracuseStep 3128009 = 2346007) B2346007
theorem B2085339 : Blo 2083435 2085339 := bstep (se 1 (by rfl) ⟨1564004, by rfl⟩ : syracuseStep 2085339 = 3128009) B3128009
theorem B4576117 : Blo 2083435 4576117 := bbase (se 5 (by rfl) ⟨214505, by rfl⟩ : syracuseStep 4576117 = 429011) (by norm_num)
theorem B6101489 : Blo 2083435 6101489 := bstep (se 2 (by rfl) ⟨2288058, by rfl⟩ : syracuseStep 6101489 = 4576117) B4576117
theorem B4067659 : Blo 2083435 4067659 := bstep (se 1 (by rfl) ⟨3050744, by rfl⟩ : syracuseStep 4067659 = 6101489) B6101489
theorem B5423545 : Blo 2083435 5423545 := bstep (se 2 (by rfl) ⟨2033829, by rfl⟩ : syracuseStep 5423545 = 4067659) B4067659
theorem B7231393 : Blo 2083435 7231393 := bstep (se 2 (by rfl) ⟨2711772, by rfl⟩ : syracuseStep 7231393 = 5423545) B5423545
theorem B9641857 : Blo 2083435 9641857 := bstep (se 2 (by rfl) ⟨3615696, by rfl⟩ : syracuseStep 9641857 = 7231393) B7231393
theorem B12855809 : Blo 2083435 12855809 := bstep (se 2 (by rfl) ⟨4820928, by rfl⟩ : syracuseStep 12855809 = 9641857) B9641857
theorem B8570539 : Blo 2083435 8570539 := bstep (se 1 (by rfl) ⟨6427904, by rfl⟩ : syracuseStep 8570539 = 12855809) B12855809
theorem B45709541 : Blo 2083435 45709541 := bstep (se 4 (by rfl) ⟨4285269, by rfl⟩ : syracuseStep 45709541 = 8570539) B8570539
theorem B30473027 : Blo 2083435 30473027 := bstep (se 1 (by rfl) ⟨22854770, by rfl⟩ : syracuseStep 30473027 = 45709541) B45709541
theorem B20315351 : Blo 2083435 20315351 := bstep (se 1 (by rfl) ⟨15236513, by rfl⟩ : syracuseStep 20315351 = 30473027) B30473027
theorem B13543567 : Blo 2083435 13543567 := bstep (se 1 (by rfl) ⟨10157675, by rfl⟩ : syracuseStep 13543567 = 20315351) B20315351
theorem B72232357 : Blo 2083435 72232357 := bstep (se 4 (by rfl) ⟨6771783, by rfl⟩ : syracuseStep 72232357 = 13543567) B13543567
theorem B96309809 : Blo 2083435 96309809 := bstep (se 2 (by rfl) ⟨36116178, by rfl⟩ : syracuseStep 96309809 = 72232357) B72232357
theorem B64206539 : Blo 2083435 64206539 := bstep (se 1 (by rfl) ⟨48154904, by rfl⟩ : syracuseStep 64206539 = 96309809) B96309809
theorem B42804359 : Blo 2083435 42804359 := bstep (se 1 (by rfl) ⟨32103269, by rfl⟩ : syracuseStep 42804359 = 64206539) B64206539
theorem B28536239 : Blo 2083435 28536239 := bstep (se 1 (by rfl) ⟨21402179, by rfl⟩ : syracuseStep 28536239 = 42804359) B42804359
theorem B19024159 : Blo 2083435 19024159 := bstep (se 1 (by rfl) ⟨14268119, by rfl⟩ : syracuseStep 19024159 = 28536239) B28536239
theorem B25365545 : Blo 2083435 25365545 := bstep (se 2 (by rfl) ⟨9512079, by rfl⟩ : syracuseStep 25365545 = 19024159) B19024159
theorem B16910363 : Blo 2083435 16910363 := bstep (se 1 (by rfl) ⟨12682772, by rfl⟩ : syracuseStep 16910363 = 25365545) B25365545
theorem B11273575 : Blo 2083435 11273575 := bstep (se 1 (by rfl) ⟨8455181, by rfl⟩ : syracuseStep 11273575 = 16910363) B16910363
theorem B15031433 : Blo 2083435 15031433 := bstep (se 2 (by rfl) ⟨5636787, by rfl⟩ : syracuseStep 15031433 = 11273575) B11273575
theorem B10020955 : Blo 2083435 10020955 := bstep (se 1 (by rfl) ⟨7515716, by rfl⟩ : syracuseStep 10020955 = 15031433) B15031433
theorem B13361273 : Blo 2083435 13361273 := bstep (se 2 (by rfl) ⟨5010477, by rfl⟩ : syracuseStep 13361273 = 10020955) B10020955
theorem B8907515 : Blo 2083435 8907515 := bstep (se 1 (by rfl) ⟨6680636, by rfl⟩ : syracuseStep 8907515 = 13361273) B13361273
theorem B5938343 : Blo 2083435 5938343 := bstep (se 1 (by rfl) ⟨4453757, by rfl⟩ : syracuseStep 5938343 = 8907515) B8907515
theorem B3958895 : Blo 2083435 3958895 := bstep (se 1 (by rfl) ⟨2969171, by rfl⟩ : syracuseStep 3958895 = 5938343) B5938343
theorem B10557053 : Blo 2083435 10557053 := bstep (se 3 (by rfl) ⟨1979447, by rfl⟩ : syracuseStep 10557053 = 3958895) B3958895
theorem B7038035 : Blo 2083435 7038035 := bstep (se 1 (by rfl) ⟨5278526, by rfl⟩ : syracuseStep 7038035 = 10557053) B10557053
theorem B4692023 : Blo 2083435 4692023 := bstep (se 1 (by rfl) ⟨3519017, by rfl⟩ : syracuseStep 4692023 = 7038035) B7038035
theorem B3128015 : Blo 2083435 3128015 := bstep (se 1 (by rfl) ⟨2346011, by rfl⟩ : syracuseStep 3128015 = 4692023) B4692023
theorem B2085343 : Blo 2083435 2085343 := bstep (se 1 (by rfl) ⟨1564007, by rfl⟩ : syracuseStep 2085343 = 3128015) B3128015
theorem B3128021 : Blo 2083435 3128021 := bbase (se 7 (by rfl) ⟨36656, by rfl⟩ : syracuseStep 3128021 = 73313) (by norm_num)
theorem B2085347 : Blo 2083435 2085347 := bstep (se 1 (by rfl) ⟨1564010, by rfl⟩ : syracuseStep 2085347 = 3128021) B3128021
theorem B2818405 : Blo 2083435 2818405 := bbase (se 4 (by rfl) ⟨264225, by rfl⟩ : syracuseStep 2818405 = 528451) (by norm_num)
theorem B15031493 : Blo 2083435 15031493 := bstep (se 4 (by rfl) ⟨1409202, by rfl⟩ : syracuseStep 15031493 = 2818405) B2818405
theorem B10020995 : Blo 2083435 10020995 := bstep (se 1 (by rfl) ⟨7515746, by rfl⟩ : syracuseStep 10020995 = 15031493) B15031493
theorem B6680663 : Blo 2083435 6680663 := bstep (se 1 (by rfl) ⟨5010497, by rfl⟩ : syracuseStep 6680663 = 10020995) B10020995
theorem B4453775 : Blo 2083435 4453775 := bstep (se 1 (by rfl) ⟨3340331, by rfl⟩ : syracuseStep 4453775 = 6680663) B6680663
theorem B2969183 : Blo 2083435 2969183 := bstep (se 1 (by rfl) ⟨2226887, by rfl⟩ : syracuseStep 2969183 = 4453775) B4453775
theorem B7917821 : Blo 2083435 7917821 := bstep (se 3 (by rfl) ⟨1484591, by rfl⟩ : syracuseStep 7917821 = 2969183) B2969183
theorem B5278547 : Blo 2083435 5278547 := bstep (se 1 (by rfl) ⟨3958910, by rfl⟩ : syracuseStep 5278547 = 7917821) B7917821
theorem B3519031 : Blo 2083435 3519031 := bstep (se 1 (by rfl) ⟨2639273, by rfl⟩ : syracuseStep 3519031 = 5278547) B5278547
theorem B4692041 : Blo 2083435 4692041 := bstep (se 2 (by rfl) ⟨1759515, by rfl⟩ : syracuseStep 4692041 = 3519031) B3519031
theorem B3128027 : Blo 2083435 3128027 := bstep (se 1 (by rfl) ⟨2346020, by rfl⟩ : syracuseStep 3128027 = 4692041) B4692041
theorem B2085351 : Blo 2083435 2085351 := bstep (se 1 (by rfl) ⟨1564013, by rfl⟩ : syracuseStep 2085351 = 3128027) B3128027
theorem B2346025 : Blo 2083435 2346025 := bbase (se 2 (by rfl) ⟨879759, by rfl⟩ : syracuseStep 2346025 = 1759519) (by norm_num)
theorem B3128033 : Blo 2083435 3128033 := bstep (se 2 (by rfl) ⟨1173012, by rfl⟩ : syracuseStep 3128033 = 2346025) B2346025
theorem B2085355 : Blo 2083435 2085355 := bstep (se 1 (by rfl) ⟨1564016, by rfl⟩ : syracuseStep 2085355 = 3128033) B3128033
theorem B3615725 : Blo 2083435 3615725 := bbase (se 3 (by rfl) ⟨677948, by rfl⟩ : syracuseStep 3615725 = 1355897) (by norm_num)
theorem B2410483 : Blo 2083435 2410483 := bstep (se 1 (by rfl) ⟨1807862, by rfl⟩ : syracuseStep 2410483 = 3615725) B3615725
theorem B3213977 : Blo 2083435 3213977 := bstep (se 2 (by rfl) ⟨1205241, by rfl⟩ : syracuseStep 3213977 = 2410483) B2410483
theorem B8570605 : Blo 2083435 8570605 := bstep (se 3 (by rfl) ⟨1606988, by rfl⟩ : syracuseStep 8570605 = 3213977) B3213977
theorem B11427473 : Blo 2083435 11427473 := bstep (se 2 (by rfl) ⟨4285302, by rfl⟩ : syracuseStep 11427473 = 8570605) B8570605
theorem B7618315 : Blo 2083435 7618315 := bstep (se 1 (by rfl) ⟨5713736, by rfl⟩ : syracuseStep 7618315 = 11427473) B11427473
theorem B10157753 : Blo 2083435 10157753 := bstep (se 2 (by rfl) ⟨3809157, by rfl⟩ : syracuseStep 10157753 = 7618315) B7618315
theorem B6771835 : Blo 2083435 6771835 := bstep (se 1 (by rfl) ⟨5078876, by rfl⟩ : syracuseStep 6771835 = 10157753) B10157753
theorem B9029113 : Blo 2083435 9029113 := bstep (se 2 (by rfl) ⟨3385917, by rfl⟩ : syracuseStep 9029113 = 6771835) B6771835
theorem B48155269 : Blo 2083435 48155269 := bstep (se 4 (by rfl) ⟨4514556, by rfl⟩ : syracuseStep 48155269 = 9029113) B9029113
theorem B64207025 : Blo 2083435 64207025 := bstep (se 2 (by rfl) ⟨24077634, by rfl⟩ : syracuseStep 64207025 = 48155269) B48155269
theorem B42804683 : Blo 2083435 42804683 := bstep (se 1 (by rfl) ⟨32103512, by rfl⟩ : syracuseStep 42804683 = 64207025) B64207025
theorem B28536455 : Blo 2083435 28536455 := bstep (se 1 (by rfl) ⟨21402341, by rfl⟩ : syracuseStep 28536455 = 42804683) B42804683
theorem B19024303 : Blo 2083435 19024303 := bstep (se 1 (by rfl) ⟨14268227, by rfl⟩ : syracuseStep 19024303 = 28536455) B28536455
theorem B25365737 : Blo 2083435 25365737 := bstep (se 2 (by rfl) ⟨9512151, by rfl⟩ : syracuseStep 25365737 = 19024303) B19024303
theorem B67641965 : Blo 2083435 67641965 := bstep (se 3 (by rfl) ⟨12682868, by rfl⟩ : syracuseStep 67641965 = 25365737) B25365737
theorem B45094643 : Blo 2083435 45094643 := bstep (se 1 (by rfl) ⟨33820982, by rfl⟩ : syracuseStep 45094643 = 67641965) B67641965
theorem B30063095 : Blo 2083435 30063095 := bstep (se 1 (by rfl) ⟨22547321, by rfl⟩ : syracuseStep 30063095 = 45094643) B45094643
theorem B20042063 : Blo 2083435 20042063 := bstep (se 1 (by rfl) ⟨15031547, by rfl⟩ : syracuseStep 20042063 = 30063095) B30063095
theorem B13361375 : Blo 2083435 13361375 := bstep (se 1 (by rfl) ⟨10021031, by rfl⟩ : syracuseStep 13361375 = 20042063) B20042063
theorem B8907583 : Blo 2083435 8907583 := bstep (se 1 (by rfl) ⟨6680687, by rfl⟩ : syracuseStep 8907583 = 13361375) B13361375
theorem B11876777 : Blo 2083435 11876777 := bstep (se 2 (by rfl) ⟨4453791, by rfl⟩ : syracuseStep 11876777 = 8907583) B8907583
theorem B7917851 : Blo 2083435 7917851 := bstep (se 1 (by rfl) ⟨5938388, by rfl⟩ : syracuseStep 7917851 = 11876777) B11876777
theorem B5278567 : Blo 2083435 5278567 := bstep (se 1 (by rfl) ⟨3958925, by rfl⟩ : syracuseStep 5278567 = 7917851) B7917851
theorem B7038089 : Blo 2083435 7038089 := bstep (se 2 (by rfl) ⟨2639283, by rfl⟩ : syracuseStep 7038089 = 5278567) B5278567
theorem B4692059 : Blo 2083435 4692059 := bstep (se 1 (by rfl) ⟨3519044, by rfl⟩ : syracuseStep 4692059 = 7038089) B7038089
theorem B3128039 : Blo 2083435 3128039 := bstep (se 1 (by rfl) ⟨2346029, by rfl⟩ : syracuseStep 3128039 = 4692059) B4692059
theorem B2085359 : Blo 2083435 2085359 := bstep (se 1 (by rfl) ⟨1564019, by rfl⟩ : syracuseStep 2085359 = 3128039) B3128039
theorem B3128045 : Blo 2083435 3128045 := bbase (se 3 (by rfl) ⟨586508, by rfl⟩ : syracuseStep 3128045 = 1173017) (by norm_num)
theorem B2085363 : Blo 2083435 2085363 := bstep (se 1 (by rfl) ⟨1564022, by rfl⟩ : syracuseStep 2085363 = 3128045) B3128045
theorem B4692077 : Blo 2083435 4692077 := bbase (se 3 (by rfl) ⟨879764, by rfl⟩ : syracuseStep 4692077 = 1759529) (by norm_num)
theorem B3128051 : Blo 2083435 3128051 := bstep (se 1 (by rfl) ⟨2346038, by rfl⟩ : syracuseStep 3128051 = 4692077) B4692077
theorem B2085367 : Blo 2083435 2085367 := bstep (se 1 (by rfl) ⟨1564025, by rfl⟩ : syracuseStep 2085367 = 3128051) B3128051
theorem B3958949 : Blo 2083435 3958949 := bbase (se 4 (by rfl) ⟨371151, by rfl⟩ : syracuseStep 3958949 = 742303) (by norm_num)
theorem B2639299 : Blo 2083435 2639299 := bstep (se 1 (by rfl) ⟨1979474, by rfl⟩ : syracuseStep 2639299 = 3958949) B3958949
theorem B3519065 : Blo 2083435 3519065 := bstep (se 2 (by rfl) ⟨1319649, by rfl⟩ : syracuseStep 3519065 = 2639299) B2639299
theorem B2346043 : Blo 2083435 2346043 := bstep (se 1 (by rfl) ⟨1759532, by rfl⟩ : syracuseStep 2346043 = 3519065) B3519065
theorem B3128057 : Blo 2083435 3128057 := bstep (se 2 (by rfl) ⟨1173021, by rfl⟩ : syracuseStep 3128057 = 2346043) B2346043
theorem B2085371 : Blo 2083435 2085371 := bstep (se 1 (by rfl) ⟨1564028, by rfl⟩ : syracuseStep 2085371 = 3128057) B3128057
theorem B8025941 : Blo 2083435 8025941 := bbase (se 9 (by rfl) ⟨23513, by rfl⟩ : syracuseStep 8025941 = 47027) (by norm_num)
theorem B5350627 : Blo 2083435 5350627 := bstep (se 1 (by rfl) ⟨4012970, by rfl⟩ : syracuseStep 5350627 = 8025941) B8025941
theorem B7134169 : Blo 2083435 7134169 := bstep (se 2 (by rfl) ⟨2675313, by rfl⟩ : syracuseStep 7134169 = 5350627) B5350627
theorem B9512225 : Blo 2083435 9512225 := bstep (se 2 (by rfl) ⟨3567084, by rfl⟩ : syracuseStep 9512225 = 7134169) B7134169
theorem B6341483 : Blo 2083435 6341483 := bstep (se 1 (by rfl) ⟨4756112, by rfl⟩ : syracuseStep 6341483 = 9512225) B9512225
theorem B4227655 : Blo 2083435 4227655 := bstep (se 1 (by rfl) ⟨3170741, by rfl⟩ : syracuseStep 4227655 = 6341483) B6341483
theorem B5636873 : Blo 2083435 5636873 := bstep (se 2 (by rfl) ⟨2113827, by rfl⟩ : syracuseStep 5636873 = 4227655) B4227655
theorem B15031661 : Blo 2083435 15031661 := bstep (se 3 (by rfl) ⟨2818436, by rfl⟩ : syracuseStep 15031661 = 5636873) B5636873
theorem B40084429 : Blo 2083435 40084429 := bstep (se 3 (by rfl) ⟨7515830, by rfl⟩ : syracuseStep 40084429 = 15031661) B15031661
theorem B53445905 : Blo 2083435 53445905 := bstep (se 2 (by rfl) ⟨20042214, by rfl⟩ : syracuseStep 53445905 = 40084429) B40084429
theorem B35630603 : Blo 2083435 35630603 := bstep (se 1 (by rfl) ⟨26722952, by rfl⟩ : syracuseStep 35630603 = 53445905) B53445905
theorem B23753735 : Blo 2083435 23753735 := bstep (se 1 (by rfl) ⟨17815301, by rfl⟩ : syracuseStep 23753735 = 35630603) B35630603
theorem B15835823 : Blo 2083435 15835823 := bstep (se 1 (by rfl) ⟨11876867, by rfl⟩ : syracuseStep 15835823 = 23753735) B23753735
theorem B10557215 : Blo 2083435 10557215 := bstep (se 1 (by rfl) ⟨7917911, by rfl⟩ : syracuseStep 10557215 = 15835823) B15835823
theorem B7038143 : Blo 2083435 7038143 := bstep (se 1 (by rfl) ⟨5278607, by rfl⟩ : syracuseStep 7038143 = 10557215) B10557215
theorem B4692095 : Blo 2083435 4692095 := bstep (se 1 (by rfl) ⟨3519071, by rfl⟩ : syracuseStep 4692095 = 7038143) B7038143
theorem B3128063 : Blo 2083435 3128063 := bstep (se 1 (by rfl) ⟨2346047, by rfl⟩ : syracuseStep 3128063 = 4692095) B4692095
theorem B2085375 : Blo 2083435 2085375 := bstep (se 1 (by rfl) ⟨1564031, by rfl⟩ : syracuseStep 2085375 = 3128063) B3128063
theorem B3128069 : Blo 2083435 3128069 := bbase (se 4 (by rfl) ⟨293256, by rfl⟩ : syracuseStep 3128069 = 586513) (by norm_num)
theorem B2085379 : Blo 2083435 2085379 := bstep (se 1 (by rfl) ⟨1564034, by rfl⟩ : syracuseStep 2085379 = 3128069) B3128069
theorem B3519085 : Blo 2083435 3519085 := bbase (se 3 (by rfl) ⟨659828, by rfl⟩ : syracuseStep 3519085 = 1319657) (by norm_num)
theorem B4692113 : Blo 2083435 4692113 := bstep (se 2 (by rfl) ⟨1759542, by rfl⟩ : syracuseStep 4692113 = 3519085) B3519085
theorem B3128075 : Blo 2083435 3128075 := bstep (se 1 (by rfl) ⟨2346056, by rfl⟩ : syracuseStep 3128075 = 4692113) B4692113
theorem B2085383 : Blo 2083435 2085383 := bstep (se 1 (by rfl) ⟨1564037, by rfl⟩ : syracuseStep 2085383 = 3128075) B3128075
theorem B2346061 : Blo 2083435 2346061 := bbase (se 3 (by rfl) ⟨439886, by rfl⟩ : syracuseStep 2346061 = 879773) (by norm_num)
theorem B3128081 : Blo 2083435 3128081 := bstep (se 2 (by rfl) ⟨1173030, by rfl⟩ : syracuseStep 3128081 = 2346061) B2346061
theorem B2085387 : Blo 2083435 2085387 := bstep (se 1 (by rfl) ⟨1564040, by rfl⟩ : syracuseStep 2085387 = 3128081) B3128081
theorem B7038197 : Blo 2083435 7038197 := bbase (se 5 (by rfl) ⟨329915, by rfl⟩ : syracuseStep 7038197 = 659831) (by norm_num)
theorem B4692131 : Blo 2083435 4692131 := bstep (se 1 (by rfl) ⟨3519098, by rfl⟩ : syracuseStep 4692131 = 7038197) B7038197
theorem B3128087 : Blo 2083435 3128087 := bstep (se 1 (by rfl) ⟨2346065, by rfl⟩ : syracuseStep 3128087 = 4692131) B4692131
theorem B2085391 : Blo 2083435 2085391 := bstep (se 1 (by rfl) ⟨1564043, by rfl⟩ : syracuseStep 2085391 = 3128087) B3128087
theorem B3128093 : Blo 2083435 3128093 := bbase (se 3 (by rfl) ⟨586517, by rfl⟩ : syracuseStep 3128093 = 1173035) (by norm_num)
theorem B2085395 : Blo 2083435 2085395 := bstep (se 1 (by rfl) ⟨1564046, by rfl⟩ : syracuseStep 2085395 = 3128093) B3128093
theorem B4692149 : Blo 2083435 4692149 := bbase (se 5 (by rfl) ⟨219944, by rfl⟩ : syracuseStep 4692149 = 439889) (by norm_num)
theorem B3128099 : Blo 2083435 3128099 := bstep (se 1 (by rfl) ⟨2346074, by rfl⟩ : syracuseStep 3128099 = 4692149) B4692149
theorem B2085399 : Blo 2083435 2085399 := bstep (se 1 (by rfl) ⟨1564049, by rfl⟩ : syracuseStep 2085399 = 3128099) B3128099
theorem B5713861 : Blo 2083435 5713861 := bbase (se 4 (by rfl) ⟨535674, by rfl⟩ : syracuseStep 5713861 = 1071349) (by norm_num)
theorem B7618481 : Blo 2083435 7618481 := bstep (se 2 (by rfl) ⟨2856930, by rfl⟩ : syracuseStep 7618481 = 5713861) B5713861
theorem B5078987 : Blo 2083435 5078987 := bstep (se 1 (by rfl) ⟨3809240, by rfl⟩ : syracuseStep 5078987 = 7618481) B7618481
theorem B3385991 : Blo 2083435 3385991 := bstep (se 1 (by rfl) ⟨2539493, by rfl⟩ : syracuseStep 3385991 = 5078987) B5078987
theorem B2257327 : Blo 2083435 2257327 := bstep (se 1 (by rfl) ⟨1692995, by rfl⟩ : syracuseStep 2257327 = 3385991) B3385991
theorem B12039077 : Blo 2083435 12039077 := bstep (se 4 (by rfl) ⟨1128663, by rfl⟩ : syracuseStep 12039077 = 2257327) B2257327
theorem B8026051 : Blo 2083435 8026051 := bstep (se 1 (by rfl) ⟨6019538, by rfl⟩ : syracuseStep 8026051 = 12039077) B12039077
theorem B10701401 : Blo 2083435 10701401 := bstep (se 2 (by rfl) ⟨4013025, by rfl⟩ : syracuseStep 10701401 = 8026051) B8026051
theorem B28537069 : Blo 2083435 28537069 := bstep (se 3 (by rfl) ⟨5350700, by rfl⟩ : syracuseStep 28537069 = 10701401) B10701401
theorem B38049425 : Blo 2083435 38049425 := bstep (se 2 (by rfl) ⟨14268534, by rfl⟩ : syracuseStep 38049425 = 28537069) B28537069
theorem B25366283 : Blo 2083435 25366283 := bstep (se 1 (by rfl) ⟨19024712, by rfl⟩ : syracuseStep 25366283 = 38049425) B38049425
theorem B16910855 : Blo 2083435 16910855 := bstep (se 1 (by rfl) ⟨12683141, by rfl⟩ : syracuseStep 16910855 = 25366283) B25366283
theorem B11273903 : Blo 2083435 11273903 := bstep (se 1 (by rfl) ⟨8455427, by rfl⟩ : syracuseStep 11273903 = 16910855) B16910855
theorem B7515935 : Blo 2083435 7515935 := bstep (se 1 (by rfl) ⟨5636951, by rfl⟩ : syracuseStep 7515935 = 11273903) B11273903
theorem B5010623 : Blo 2083435 5010623 := bstep (se 1 (by rfl) ⟨3757967, by rfl⟩ : syracuseStep 5010623 = 7515935) B7515935
theorem B3340415 : Blo 2083435 3340415 := bstep (se 1 (by rfl) ⟨2505311, by rfl⟩ : syracuseStep 3340415 = 5010623) B5010623
theorem B2226943 : Blo 2083435 2226943 := bstep (se 1 (by rfl) ⟨1670207, by rfl⟩ : syracuseStep 2226943 = 3340415) B3340415
theorem B11877029 : Blo 2083435 11877029 := bstep (se 4 (by rfl) ⟨1113471, by rfl⟩ : syracuseStep 11877029 = 2226943) B2226943
theorem B7918019 : Blo 2083435 7918019 := bstep (se 1 (by rfl) ⟨5938514, by rfl⟩ : syracuseStep 7918019 = 11877029) B11877029
theorem B5278679 : Blo 2083435 5278679 := bstep (se 1 (by rfl) ⟨3959009, by rfl⟩ : syracuseStep 5278679 = 7918019) B7918019
theorem B3519119 : Blo 2083435 3519119 := bstep (se 1 (by rfl) ⟨2639339, by rfl⟩ : syracuseStep 3519119 = 5278679) B5278679
theorem B2346079 : Blo 2083435 2346079 := bstep (se 1 (by rfl) ⟨1759559, by rfl⟩ : syracuseStep 2346079 = 3519119) B3519119
theorem B3128105 : Blo 2083435 3128105 := bstep (se 2 (by rfl) ⟨1173039, by rfl⟩ : syracuseStep 3128105 = 2346079) B2346079
theorem B2085403 : Blo 2083435 2085403 := bstep (se 1 (by rfl) ⟨1564052, by rfl⟩ : syracuseStep 2085403 = 3128105) B3128105
theorem B3340421 : Blo 2083435 3340421 := bbase (se 4 (by rfl) ⟨313164, by rfl⟩ : syracuseStep 3340421 = 626329) (by norm_num)
theorem B2226947 : Blo 2083435 2226947 := bstep (se 1 (by rfl) ⟨1670210, by rfl⟩ : syracuseStep 2226947 = 3340421) B3340421
theorem B5938525 : Blo 2083435 5938525 := bstep (se 3 (by rfl) ⟨1113473, by rfl⟩ : syracuseStep 5938525 = 2226947) B2226947
theorem B7918033 : Blo 2083435 7918033 := bstep (se 2 (by rfl) ⟨2969262, by rfl⟩ : syracuseStep 7918033 = 5938525) B5938525
theorem B10557377 : Blo 2083435 10557377 := bstep (se 2 (by rfl) ⟨3959016, by rfl⟩ : syracuseStep 10557377 = 7918033) B7918033
theorem B7038251 : Blo 2083435 7038251 := bstep (se 1 (by rfl) ⟨5278688, by rfl⟩ : syracuseStep 7038251 = 10557377) B10557377
theorem B4692167 : Blo 2083435 4692167 := bstep (se 1 (by rfl) ⟨3519125, by rfl⟩ : syracuseStep 4692167 = 7038251) B7038251
theorem B3128111 : Blo 2083435 3128111 := bstep (se 1 (by rfl) ⟨2346083, by rfl⟩ : syracuseStep 3128111 = 4692167) B4692167
theorem B2085407 : Blo 2083435 2085407 := bstep (se 1 (by rfl) ⟨1564055, by rfl⟩ : syracuseStep 2085407 = 3128111) B3128111
theorem B3128117 : Blo 2083435 3128117 := bbase (se 5 (by rfl) ⟨146630, by rfl⟩ : syracuseStep 3128117 = 293261) (by norm_num)
theorem B2085411 : Blo 2083435 2085411 := bstep (se 1 (by rfl) ⟨1564058, by rfl⟩ : syracuseStep 2085411 = 3128117) B3128117
theorem B5278709 : Blo 2083435 5278709 := bbase (se 5 (by rfl) ⟨247439, by rfl⟩ : syracuseStep 5278709 = 494879) (by norm_num)
theorem B3519139 : Blo 2083435 3519139 := bstep (se 1 (by rfl) ⟨2639354, by rfl⟩ : syracuseStep 3519139 = 5278709) B5278709
theorem B4692185 : Blo 2083435 4692185 := bstep (se 2 (by rfl) ⟨1759569, by rfl⟩ : syracuseStep 4692185 = 3519139) B3519139
theorem B3128123 : Blo 2083435 3128123 := bstep (se 1 (by rfl) ⟨2346092, by rfl⟩ : syracuseStep 3128123 = 4692185) B4692185
theorem B2085415 : Blo 2083435 2085415 := bstep (se 1 (by rfl) ⟨1564061, by rfl⟩ : syracuseStep 2085415 = 3128123) B3128123
theorem B2346097 : Blo 2083435 2346097 := bbase (se 2 (by rfl) ⟨879786, by rfl⟩ : syracuseStep 2346097 = 1759573) (by norm_num)
theorem B3128129 : Blo 2083435 3128129 := bstep (se 2 (by rfl) ⟨1173048, by rfl⟩ : syracuseStep 3128129 = 2346097) B2346097
theorem B2085419 : Blo 2083435 2085419 := bstep (se 1 (by rfl) ⟨1564064, by rfl⟩ : syracuseStep 2085419 = 3128129) B3128129
theorem B2113877 : Blo 2083435 2113877 := bbase (se 10 (by rfl) ⟨3096, by rfl⟩ : syracuseStep 2113877 = 6193) (by norm_num)
theorem B5637005 : Blo 2083435 5637005 := bstep (se 3 (by rfl) ⟨1056938, by rfl⟩ : syracuseStep 5637005 = 2113877) B2113877
theorem B3758003 : Blo 2083435 3758003 := bstep (se 1 (by rfl) ⟨2818502, by rfl⟩ : syracuseStep 3758003 = 5637005) B5637005
theorem B2505335 : Blo 2083435 2505335 := bstep (se 1 (by rfl) ⟨1879001, by rfl⟩ : syracuseStep 2505335 = 3758003) B3758003
theorem B6680893 : Blo 2083435 6680893 := bstep (se 3 (by rfl) ⟨1252667, by rfl⟩ : syracuseStep 6680893 = 2505335) B2505335
theorem B8907857 : Blo 2083435 8907857 := bstep (se 2 (by rfl) ⟨3340446, by rfl⟩ : syracuseStep 8907857 = 6680893) B6680893
theorem B5938571 : Blo 2083435 5938571 := bstep (se 1 (by rfl) ⟨4453928, by rfl⟩ : syracuseStep 5938571 = 8907857) B8907857
theorem B3959047 : Blo 2083435 3959047 := bstep (se 1 (by rfl) ⟨2969285, by rfl⟩ : syracuseStep 3959047 = 5938571) B5938571
theorem B5278729 : Blo 2083435 5278729 := bstep (se 2 (by rfl) ⟨1979523, by rfl⟩ : syracuseStep 5278729 = 3959047) B3959047
theorem B7038305 : Blo 2083435 7038305 := bstep (se 2 (by rfl) ⟨2639364, by rfl⟩ : syracuseStep 7038305 = 5278729) B5278729
theorem B4692203 : Blo 2083435 4692203 := bstep (se 1 (by rfl) ⟨3519152, by rfl⟩ : syracuseStep 4692203 = 7038305) B7038305
theorem B3128135 : Blo 2083435 3128135 := bstep (se 1 (by rfl) ⟨2346101, by rfl⟩ : syracuseStep 3128135 = 4692203) B4692203
theorem B2085423 : Blo 2083435 2085423 := bstep (se 1 (by rfl) ⟨1564067, by rfl⟩ : syracuseStep 2085423 = 3128135) B3128135
theorem B3128141 : Blo 2083435 3128141 := bbase (se 3 (by rfl) ⟨586526, by rfl⟩ : syracuseStep 3128141 = 1173053) (by norm_num)
theorem B2085427 : Blo 2083435 2085427 := bstep (se 1 (by rfl) ⟨1564070, by rfl⟩ : syracuseStep 2085427 = 3128141) B3128141
theorem B4692221 : Blo 2083435 4692221 := bbase (se 3 (by rfl) ⟨879791, by rfl⟩ : syracuseStep 4692221 = 1759583) (by norm_num)
theorem B3128147 : Blo 2083435 3128147 := bstep (se 1 (by rfl) ⟨2346110, by rfl⟩ : syracuseStep 3128147 = 4692221) B4692221
theorem B2085431 : Blo 2083435 2085431 := bstep (se 1 (by rfl) ⟨1564073, by rfl⟩ : syracuseStep 2085431 = 3128147) B3128147
theorem B3519173 : Blo 2083435 3519173 := bbase (se 4 (by rfl) ⟨329922, by rfl⟩ : syracuseStep 3519173 = 659845) (by norm_num)
theorem B2346115 : Blo 2083435 2346115 := bstep (se 1 (by rfl) ⟨1759586, by rfl⟩ : syracuseStep 2346115 = 3519173) B3519173
theorem B3128153 : Blo 2083435 3128153 := bstep (se 2 (by rfl) ⟨1173057, by rfl⟩ : syracuseStep 3128153 = 2346115) B2346115
theorem B2085435 : Blo 2083435 2085435 := bstep (se 1 (by rfl) ⟨1564076, by rfl⟩ : syracuseStep 2085435 = 3128153) B3128153
theorem C0 (j : ℕ) (h1 : 520858 ≤ j) (h2 : j ≤ 521358) : Blo 2083435 (4 * j + 3) := by
  interval_cases j
  · exact B2083435
  · exact B2083439
  · exact B2083443
  · exact B2083447
  · exact B2083451
  · exact B2083455
  · exact B2083459
  · exact B2083463
  · exact B2083467
  · exact B2083471
  · exact B2083475
  · exact B2083479
  · exact B2083483
  · exact B2083487
  · exact B2083491
  · exact B2083495
  · exact B2083499
  · exact B2083503
  · exact B2083507
  · exact B2083511
  · exact B2083515
  · exact B2083519
  · exact B2083523
  · exact B2083527
  · exact B2083531
  · exact B2083535
  · exact B2083539
  · exact B2083543
  · exact B2083547
  · exact B2083551
  · exact B2083555
  · exact B2083559
  · exact B2083563
  · exact B2083567
  · exact B2083571
  · exact B2083575
  · exact B2083579
  · exact B2083583
  · exact B2083587
  · exact B2083591
  · exact B2083595
  · exact B2083599
  · exact B2083603
  · exact B2083607
  · exact B2083611
  · exact B2083615
  · exact B2083619
  · exact B2083623
  · exact B2083627
  · exact B2083631
  · exact B2083635
  · exact B2083639
  · exact B2083643
  · exact B2083647
  · exact B2083651
  · exact B2083655
  · exact B2083659
  · exact B2083663
  · exact B2083667
  · exact B2083671
  · exact B2083675
  · exact B2083679
  · exact B2083683
  · exact B2083687
  · exact B2083691
  · exact B2083695
  · exact B2083699
  · exact B2083703
  · exact B2083707
  · exact B2083711
  · exact B2083715
  · exact B2083719
  · exact B2083723
  · exact B2083727
  · exact B2083731
  · exact B2083735
  · exact B2083739
  · exact B2083743
  · exact B2083747
  · exact B2083751
  · exact B2083755
  · exact B2083759
  · exact B2083763
  · exact B2083767
  · exact B2083771
  · exact B2083775
  · exact B2083779
  · exact B2083783
  · exact B2083787
  · exact B2083791
  · exact B2083795
  · exact B2083799
  · exact B2083803
  · exact B2083807
  · exact B2083811
  · exact B2083815
  · exact B2083819
  · exact B2083823
  · exact B2083827
  · exact B2083831
  · exact B2083835
  · exact B2083839
  · exact B2083843
  · exact B2083847
  · exact B2083851
  · exact B2083855
  · exact B2083859
  · exact B2083863
  · exact B2083867
  · exact B2083871
  · exact B2083875
  · exact B2083879
  · exact B2083883
  · exact B2083887
  · exact B2083891
  · exact B2083895
  · exact B2083899
  · exact B2083903
  · exact B2083907
  · exact B2083911
  · exact B2083915
  · exact B2083919
  · exact B2083923
  · exact B2083927
  · exact B2083931
  · exact B2083935
  · exact B2083939
  · exact B2083943
  · exact B2083947
  · exact B2083951
  · exact B2083955
  · exact B2083959
  · exact B2083963
  · exact B2083967
  · exact B2083971
  · exact B2083975
  · exact B2083979
  · exact B2083983
  · exact B2083987
  · exact B2083991
  · exact B2083995
  · exact B2083999
  · exact B2084003
  · exact B2084007
  · exact B2084011
  · exact B2084015
  · exact B2084019
  · exact B2084023
  · exact B2084027
  · exact B2084031
  · exact B2084035
  · exact B2084039
  · exact B2084043
  · exact B2084047
  · exact B2084051
  · exact B2084055
  · exact B2084059
  · exact B2084063
  · exact B2084067
  · exact B2084071
  · exact B2084075
  · exact B2084079
  · exact B2084083
  · exact B2084087
  · exact B2084091
  · exact B2084095
  · exact B2084099
  · exact B2084103
  · exact B2084107
  · exact B2084111
  · exact B2084115
  · exact B2084119
  · exact B2084123
  · exact B2084127
  · exact B2084131
  · exact B2084135
  · exact B2084139
  · exact B2084143
  · exact B2084147
  · exact B2084151
  · exact B2084155
  · exact B2084159
  · exact B2084163
  · exact B2084167
  · exact B2084171
  · exact B2084175
  · exact B2084179
  · exact B2084183
  · exact B2084187
  · exact B2084191
  · exact B2084195
  · exact B2084199
  · exact B2084203
  · exact B2084207
  · exact B2084211
  · exact B2084215
  · exact B2084219
  · exact B2084223
  · exact B2084227
  · exact B2084231
  · exact B2084235
  · exact B2084239
  · exact B2084243
  · exact B2084247
  · exact B2084251
  · exact B2084255
  · exact B2084259
  · exact B2084263
  · exact B2084267
  · exact B2084271
  · exact B2084275
  · exact B2084279
  · exact B2084283
  · exact B2084287
  · exact B2084291
  · exact B2084295
  · exact B2084299
  · exact B2084303
  · exact B2084307
  · exact B2084311
  · exact B2084315
  · exact B2084319
  · exact B2084323
  · exact B2084327
  · exact B2084331
  · exact B2084335
  · exact B2084339
  · exact B2084343
  · exact B2084347
  · exact B2084351
  · exact B2084355
  · exact B2084359
  · exact B2084363
  · exact B2084367
  · exact B2084371
  · exact B2084375
  · exact B2084379
  · exact B2084383
  · exact B2084387
  · exact B2084391
  · exact B2084395
  · exact B2084399
  · exact B2084403
  · exact B2084407
  · exact B2084411
  · exact B2084415
  · exact B2084419
  · exact B2084423
  · exact B2084427
  · exact B2084431
  · exact B2084435
  · exact B2084439
  · exact B2084443
  · exact B2084447
  · exact B2084451
  · exact B2084455
  · exact B2084459
  · exact B2084463
  · exact B2084467
  · exact B2084471
  · exact B2084475
  · exact B2084479
  · exact B2084483
  · exact B2084487
  · exact B2084491
  · exact B2084495
  · exact B2084499
  · exact B2084503
  · exact B2084507
  · exact B2084511
  · exact B2084515
  · exact B2084519
  · exact B2084523
  · exact B2084527
  · exact B2084531
  · exact B2084535
  · exact B2084539
  · exact B2084543
  · exact B2084547
  · exact B2084551
  · exact B2084555
  · exact B2084559
  · exact B2084563
  · exact B2084567
  · exact B2084571
  · exact B2084575
  · exact B2084579
  · exact B2084583
  · exact B2084587
  · exact B2084591
  · exact B2084595
  · exact B2084599
  · exact B2084603
  · exact B2084607
  · exact B2084611
  · exact B2084615
  · exact B2084619
  · exact B2084623
  · exact B2084627
  · exact B2084631
  · exact B2084635
  · exact B2084639
  · exact B2084643
  · exact B2084647
  · exact B2084651
  · exact B2084655
  · exact B2084659
  · exact B2084663
  · exact B2084667
  · exact B2084671
  · exact B2084675
  · exact B2084679
  · exact B2084683
  · exact B2084687
  · exact B2084691
  · exact B2084695
  · exact B2084699
  · exact B2084703
  · exact B2084707
  · exact B2084711
  · exact B2084715
  · exact B2084719
  · exact B2084723
  · exact B2084727
  · exact B2084731
  · exact B2084735
  · exact B2084739
  · exact B2084743
  · exact B2084747
  · exact B2084751
  · exact B2084755
  · exact B2084759
  · exact B2084763
  · exact B2084767
  · exact B2084771
  · exact B2084775
  · exact B2084779
  · exact B2084783
  · exact B2084787
  · exact B2084791
  · exact B2084795
  · exact B2084799
  · exact B2084803
  · exact B2084807
  · exact B2084811
  · exact B2084815
  · exact B2084819
  · exact B2084823
  · exact B2084827
  · exact B2084831
  · exact B2084835
  · exact B2084839
  · exact B2084843
  · exact B2084847
  · exact B2084851
  · exact B2084855
  · exact B2084859
  · exact B2084863
  · exact B2084867
  · exact B2084871
  · exact B2084875
  · exact B2084879
  · exact B2084883
  · exact B2084887
  · exact B2084891
  · exact B2084895
  · exact B2084899
  · exact B2084903
  · exact B2084907
  · exact B2084911
  · exact B2084915
  · exact B2084919
  · exact B2084923
  · exact B2084927
  · exact B2084931
  · exact B2084935
  · exact B2084939
  · exact B2084943
  · exact B2084947
  · exact B2084951
  · exact B2084955
  · exact B2084959
  · exact B2084963
  · exact B2084967
  · exact B2084971
  · exact B2084975
  · exact B2084979
  · exact B2084983
  · exact B2084987
  · exact B2084991
  · exact B2084995
  · exact B2084999
  · exact B2085003
  · exact B2085007
  · exact B2085011
  · exact B2085015
  · exact B2085019
  · exact B2085023
  · exact B2085027
  · exact B2085031
  · exact B2085035
  · exact B2085039
  · exact B2085043
  · exact B2085047
  · exact B2085051
  · exact B2085055
  · exact B2085059
  · exact B2085063
  · exact B2085067
  · exact B2085071
  · exact B2085075
  · exact B2085079
  · exact B2085083
  · exact B2085087
  · exact B2085091
  · exact B2085095
  · exact B2085099
  · exact B2085103
  · exact B2085107
  · exact B2085111
  · exact B2085115
  · exact B2085119
  · exact B2085123
  · exact B2085127
  · exact B2085131
  · exact B2085135
  · exact B2085139
  · exact B2085143
  · exact B2085147
  · exact B2085151
  · exact B2085155
  · exact B2085159
  · exact B2085163
  · exact B2085167
  · exact B2085171
  · exact B2085175
  · exact B2085179
  · exact B2085183
  · exact B2085187
  · exact B2085191
  · exact B2085195
  · exact B2085199
  · exact B2085203
  · exact B2085207
  · exact B2085211
  · exact B2085215
  · exact B2085219
  · exact B2085223
  · exact B2085227
  · exact B2085231
  · exact B2085235
  · exact B2085239
  · exact B2085243
  · exact B2085247
  · exact B2085251
  · exact B2085255
  · exact B2085259
  · exact B2085263
  · exact B2085267
  · exact B2085271
  · exact B2085275
  · exact B2085279
  · exact B2085283
  · exact B2085287
  · exact B2085291
  · exact B2085295
  · exact B2085299
  · exact B2085303
  · exact B2085307
  · exact B2085311
  · exact B2085315
  · exact B2085319
  · exact B2085323
  · exact B2085327
  · exact B2085331
  · exact B2085335
  · exact B2085339
  · exact B2085343
  · exact B2085347
  · exact B2085351
  · exact B2085355
  · exact B2085359
  · exact B2085363
  · exact B2085367
  · exact B2085371
  · exact B2085375
  · exact B2085379
  · exact B2085383
  · exact B2085387
  · exact B2085391
  · exact B2085395
  · exact B2085399
  · exact B2085403
  · exact B2085407
  · exact B2085411
  · exact B2085415
  · exact B2085419
  · exact B2085423
  · exact B2085427
  · exact B2085431
  · exact B2085435
theorem solution (m : ℕ) (hlo : 2083435 ≤ m) (hhi : m ≤ 2085435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 520858 ≤ j := by omega
    have hj2 : j ≤ 521358 := by omega
    have hb : Blo 2083435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
