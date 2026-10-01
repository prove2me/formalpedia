-- Prove2me | solution 1 for syracuse_descends_range_2119435_2121435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:55.671029+00:00
-- url     : https://prove2.me/submissions/a2b7854e-c4ce-4e55-a1af-acf20dcfe322

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

theorem B2384365 : Blo 2119435 2384365 := bbase (se 3 (by rfl) ⟨447068, by rfl⟩ : syracuseStep 2384365 = 894137) (by norm_num)
theorem B3179153 : Blo 2119435 3179153 := bstep (se 2 (by rfl) ⟨1192182, by rfl⟩ : syracuseStep 3179153 = 2384365) B2384365
theorem B2119435 : Blo 2119435 2119435 := bstep (se 1 (by rfl) ⟨1589576, by rfl⟩ : syracuseStep 2119435 = 3179153) B3179153
theorem B7153109 : Blo 2119435 7153109 := bbase (se 7 (by rfl) ⟨83825, by rfl⟩ : syracuseStep 7153109 = 167651) (by norm_num)
theorem B4768739 : Blo 2119435 4768739 := bstep (se 1 (by rfl) ⟨3576554, by rfl⟩ : syracuseStep 4768739 = 7153109) B7153109
theorem B3179159 : Blo 2119435 3179159 := bstep (se 1 (by rfl) ⟨2384369, by rfl⟩ : syracuseStep 3179159 = 4768739) B4768739
theorem B2119439 : Blo 2119435 2119439 := bstep (se 1 (by rfl) ⟨1589579, by rfl⟩ : syracuseStep 2119439 = 3179159) B3179159
theorem B3179165 : Blo 2119435 3179165 := bbase (se 3 (by rfl) ⟨596093, by rfl⟩ : syracuseStep 3179165 = 1192187) (by norm_num)
theorem B2119443 : Blo 2119435 2119443 := bstep (se 1 (by rfl) ⟨1589582, by rfl⟩ : syracuseStep 2119443 = 3179165) B3179165
theorem B4768757 : Blo 2119435 4768757 := bbase (se 5 (by rfl) ⟨223535, by rfl⟩ : syracuseStep 4768757 = 447071) (by norm_num)
theorem B3179171 : Blo 2119435 3179171 := bstep (se 1 (by rfl) ⟨2384378, by rfl⟩ : syracuseStep 3179171 = 4768757) B4768757
theorem B2119447 : Blo 2119435 2119447 := bstep (se 1 (by rfl) ⟨1589585, by rfl⟩ : syracuseStep 2119447 = 3179171) B3179171
theorem B10876117 : Blo 2119435 10876117 := bbase (se 7 (by rfl) ⟨127454, by rfl⟩ : syracuseStep 10876117 = 254909) (by norm_num)
theorem B14501489 : Blo 2119435 14501489 := bstep (se 2 (by rfl) ⟨5438058, by rfl⟩ : syracuseStep 14501489 = 10876117) B10876117
theorem B38670637 : Blo 2119435 38670637 := bstep (se 3 (by rfl) ⟨7250744, by rfl⟩ : syracuseStep 38670637 = 14501489) B14501489
theorem B51560849 : Blo 2119435 51560849 := bstep (se 2 (by rfl) ⟨19335318, by rfl⟩ : syracuseStep 51560849 = 38670637) B38670637
theorem B34373899 : Blo 2119435 34373899 := bstep (se 1 (by rfl) ⟨25780424, by rfl⟩ : syracuseStep 34373899 = 51560849) B51560849
theorem B45831865 : Blo 2119435 45831865 := bstep (se 2 (by rfl) ⟨17186949, by rfl⟩ : syracuseStep 45831865 = 34373899) B34373899
theorem B61109153 : Blo 2119435 61109153 := bstep (se 2 (by rfl) ⟨22915932, by rfl⟩ : syracuseStep 61109153 = 45831865) B45831865
theorem B40739435 : Blo 2119435 40739435 := bstep (se 1 (by rfl) ⟨30554576, by rfl⟩ : syracuseStep 40739435 = 61109153) B61109153
theorem B27159623 : Blo 2119435 27159623 := bstep (se 1 (by rfl) ⟨20369717, by rfl⟩ : syracuseStep 27159623 = 40739435) B40739435
theorem B18106415 : Blo 2119435 18106415 := bstep (se 1 (by rfl) ⟨13579811, by rfl⟩ : syracuseStep 18106415 = 27159623) B27159623
theorem B12070943 : Blo 2119435 12070943 := bstep (se 1 (by rfl) ⟨9053207, by rfl⟩ : syracuseStep 12070943 = 18106415) B18106415
theorem B8047295 : Blo 2119435 8047295 := bstep (se 1 (by rfl) ⟨6035471, by rfl⟩ : syracuseStep 8047295 = 12070943) B12070943
theorem B5364863 : Blo 2119435 5364863 := bstep (se 1 (by rfl) ⟨4023647, by rfl⟩ : syracuseStep 5364863 = 8047295) B8047295
theorem B3576575 : Blo 2119435 3576575 := bstep (se 1 (by rfl) ⟨2682431, by rfl⟩ : syracuseStep 3576575 = 5364863) B5364863
theorem B2384383 : Blo 2119435 2384383 := bstep (se 1 (by rfl) ⟨1788287, by rfl⟩ : syracuseStep 2384383 = 3576575) B3576575
theorem B3179177 : Blo 2119435 3179177 := bstep (se 2 (by rfl) ⟨1192191, by rfl⟩ : syracuseStep 3179177 = 2384383) B2384383
theorem B2119451 : Blo 2119435 2119451 := bstep (se 1 (by rfl) ⟨1589588, by rfl⟩ : syracuseStep 2119451 = 3179177) B3179177
theorem B3017741 : Blo 2119435 3017741 := bbase (se 3 (by rfl) ⟨565826, by rfl⟩ : syracuseStep 3017741 = 1131653) (by norm_num)
theorem B8047309 : Blo 2119435 8047309 := bstep (se 3 (by rfl) ⟨1508870, by rfl⟩ : syracuseStep 8047309 = 3017741) B3017741
theorem B10729745 : Blo 2119435 10729745 := bstep (se 2 (by rfl) ⟨4023654, by rfl⟩ : syracuseStep 10729745 = 8047309) B8047309
theorem B7153163 : Blo 2119435 7153163 := bstep (se 1 (by rfl) ⟨5364872, by rfl⟩ : syracuseStep 7153163 = 10729745) B10729745
theorem B4768775 : Blo 2119435 4768775 := bstep (se 1 (by rfl) ⟨3576581, by rfl⟩ : syracuseStep 4768775 = 7153163) B7153163
theorem B3179183 : Blo 2119435 3179183 := bstep (se 1 (by rfl) ⟨2384387, by rfl⟩ : syracuseStep 3179183 = 4768775) B4768775
theorem B2119455 : Blo 2119435 2119455 := bstep (se 1 (by rfl) ⟨1589591, by rfl⟩ : syracuseStep 2119455 = 3179183) B3179183
theorem B3179189 : Blo 2119435 3179189 := bbase (se 5 (by rfl) ⟨149024, by rfl⟩ : syracuseStep 3179189 = 298049) (by norm_num)
theorem B2119459 : Blo 2119435 2119459 := bstep (se 1 (by rfl) ⟨1589594, by rfl⟩ : syracuseStep 2119459 = 3179189) B3179189
theorem B5364893 : Blo 2119435 5364893 := bbase (se 3 (by rfl) ⟨1005917, by rfl⟩ : syracuseStep 5364893 = 2011835) (by norm_num)
theorem B3576595 : Blo 2119435 3576595 := bstep (se 1 (by rfl) ⟨2682446, by rfl⟩ : syracuseStep 3576595 = 5364893) B5364893
theorem B4768793 : Blo 2119435 4768793 := bstep (se 2 (by rfl) ⟨1788297, by rfl⟩ : syracuseStep 4768793 = 3576595) B3576595
theorem B3179195 : Blo 2119435 3179195 := bstep (se 1 (by rfl) ⟨2384396, by rfl⟩ : syracuseStep 3179195 = 4768793) B4768793
theorem B2119463 : Blo 2119435 2119463 := bstep (se 1 (by rfl) ⟨1589597, by rfl⟩ : syracuseStep 2119463 = 3179195) B3179195
theorem B2384401 : Blo 2119435 2384401 := bbase (se 2 (by rfl) ⟨894150, by rfl⟩ : syracuseStep 2384401 = 1788301) (by norm_num)
theorem B3179201 : Blo 2119435 3179201 := bstep (se 2 (by rfl) ⟨1192200, by rfl⟩ : syracuseStep 3179201 = 2384401) B2384401
theorem B2119467 : Blo 2119435 2119467 := bstep (se 1 (by rfl) ⟨1589600, by rfl⟩ : syracuseStep 2119467 = 3179201) B3179201
theorem B4023685 : Blo 2119435 4023685 := bbase (se 4 (by rfl) ⟨377220, by rfl⟩ : syracuseStep 4023685 = 754441) (by norm_num)
theorem B5364913 : Blo 2119435 5364913 := bstep (se 2 (by rfl) ⟨2011842, by rfl⟩ : syracuseStep 5364913 = 4023685) B4023685
theorem B7153217 : Blo 2119435 7153217 := bstep (se 2 (by rfl) ⟨2682456, by rfl⟩ : syracuseStep 7153217 = 5364913) B5364913
theorem B4768811 : Blo 2119435 4768811 := bstep (se 1 (by rfl) ⟨3576608, by rfl⟩ : syracuseStep 4768811 = 7153217) B7153217
theorem B3179207 : Blo 2119435 3179207 := bstep (se 1 (by rfl) ⟨2384405, by rfl⟩ : syracuseStep 3179207 = 4768811) B4768811
theorem B2119471 : Blo 2119435 2119471 := bstep (se 1 (by rfl) ⟨1589603, by rfl⟩ : syracuseStep 2119471 = 3179207) B3179207
theorem B3179213 : Blo 2119435 3179213 := bbase (se 3 (by rfl) ⟨596102, by rfl⟩ : syracuseStep 3179213 = 1192205) (by norm_num)
theorem B2119475 : Blo 2119435 2119475 := bstep (se 1 (by rfl) ⟨1589606, by rfl⟩ : syracuseStep 2119475 = 3179213) B3179213
theorem B4768829 : Blo 2119435 4768829 := bbase (se 3 (by rfl) ⟨894155, by rfl⟩ : syracuseStep 4768829 = 1788311) (by norm_num)
theorem B3179219 : Blo 2119435 3179219 := bstep (se 1 (by rfl) ⟨2384414, by rfl⟩ : syracuseStep 3179219 = 4768829) B4768829
theorem B2119479 : Blo 2119435 2119479 := bstep (se 1 (by rfl) ⟨1589609, by rfl⟩ : syracuseStep 2119479 = 3179219) B3179219
theorem B3576629 : Blo 2119435 3576629 := bbase (se 5 (by rfl) ⟨167654, by rfl⟩ : syracuseStep 3576629 = 335309) (by norm_num)
theorem B2384419 : Blo 2119435 2384419 := bstep (se 1 (by rfl) ⟨1788314, by rfl⟩ : syracuseStep 2384419 = 3576629) B3576629
theorem B3179225 : Blo 2119435 3179225 := bstep (se 2 (by rfl) ⟨1192209, by rfl⟩ : syracuseStep 3179225 = 2384419) B2384419
theorem B2119483 : Blo 2119435 2119483 := bstep (se 1 (by rfl) ⟨1589612, by rfl⟩ : syracuseStep 2119483 = 3179225) B3179225
theorem B6035573 : Blo 2119435 6035573 := bbase (se 5 (by rfl) ⟨282917, by rfl⟩ : syracuseStep 6035573 = 565835) (by norm_num)
theorem B16094861 : Blo 2119435 16094861 := bstep (se 3 (by rfl) ⟨3017786, by rfl⟩ : syracuseStep 16094861 = 6035573) B6035573
theorem B10729907 : Blo 2119435 10729907 := bstep (se 1 (by rfl) ⟨8047430, by rfl⟩ : syracuseStep 10729907 = 16094861) B16094861
theorem B7153271 : Blo 2119435 7153271 := bstep (se 1 (by rfl) ⟨5364953, by rfl⟩ : syracuseStep 7153271 = 10729907) B10729907
theorem B4768847 : Blo 2119435 4768847 := bstep (se 1 (by rfl) ⟨3576635, by rfl⟩ : syracuseStep 4768847 = 7153271) B7153271
theorem B3179231 : Blo 2119435 3179231 := bstep (se 1 (by rfl) ⟨2384423, by rfl⟩ : syracuseStep 3179231 = 4768847) B4768847
theorem B2119487 : Blo 2119435 2119487 := bstep (se 1 (by rfl) ⟨1589615, by rfl⟩ : syracuseStep 2119487 = 3179231) B3179231
theorem B3179237 : Blo 2119435 3179237 := bbase (se 4 (by rfl) ⟨298053, by rfl⟩ : syracuseStep 3179237 = 596107) (by norm_num)
theorem B2119491 : Blo 2119435 2119491 := bstep (se 1 (by rfl) ⟨1589618, by rfl⟩ : syracuseStep 2119491 = 3179237) B3179237
theorem B2263349 : Blo 2119435 2263349 := bbase (se 5 (by rfl) ⟨106094, by rfl⟩ : syracuseStep 2263349 = 212189) (by norm_num)
theorem B6035597 : Blo 2119435 6035597 := bstep (se 3 (by rfl) ⟨1131674, by rfl⟩ : syracuseStep 6035597 = 2263349) B2263349
theorem B4023731 : Blo 2119435 4023731 := bstep (se 1 (by rfl) ⟨3017798, by rfl⟩ : syracuseStep 4023731 = 6035597) B6035597
theorem B2682487 : Blo 2119435 2682487 := bstep (se 1 (by rfl) ⟨2011865, by rfl⟩ : syracuseStep 2682487 = 4023731) B4023731
theorem B3576649 : Blo 2119435 3576649 := bstep (se 2 (by rfl) ⟨1341243, by rfl⟩ : syracuseStep 3576649 = 2682487) B2682487
theorem B4768865 : Blo 2119435 4768865 := bstep (se 2 (by rfl) ⟨1788324, by rfl⟩ : syracuseStep 4768865 = 3576649) B3576649
theorem B3179243 : Blo 2119435 3179243 := bstep (se 1 (by rfl) ⟨2384432, by rfl⟩ : syracuseStep 3179243 = 4768865) B4768865
theorem B2119495 : Blo 2119435 2119495 := bstep (se 1 (by rfl) ⟨1589621, by rfl⟩ : syracuseStep 2119495 = 3179243) B3179243
theorem B2384437 : Blo 2119435 2384437 := bbase (se 5 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 2384437 = 223541) (by norm_num)
theorem B3179249 : Blo 2119435 3179249 := bstep (se 2 (by rfl) ⟨1192218, by rfl⟩ : syracuseStep 3179249 = 2384437) B2384437
theorem B2119499 : Blo 2119435 2119499 := bstep (se 1 (by rfl) ⟨1589624, by rfl⟩ : syracuseStep 2119499 = 3179249) B3179249
theorem B2682497 : Blo 2119435 2682497 := bbase (se 2 (by rfl) ⟨1005936, by rfl⟩ : syracuseStep 2682497 = 2011873) (by norm_num)
theorem B7153325 : Blo 2119435 7153325 := bstep (se 3 (by rfl) ⟨1341248, by rfl⟩ : syracuseStep 7153325 = 2682497) B2682497
theorem B4768883 : Blo 2119435 4768883 := bstep (se 1 (by rfl) ⟨3576662, by rfl⟩ : syracuseStep 4768883 = 7153325) B7153325
theorem B3179255 : Blo 2119435 3179255 := bstep (se 1 (by rfl) ⟨2384441, by rfl⟩ : syracuseStep 3179255 = 4768883) B4768883
theorem B2119503 : Blo 2119435 2119503 := bstep (se 1 (by rfl) ⟨1589627, by rfl⟩ : syracuseStep 2119503 = 3179255) B3179255
theorem B3179261 : Blo 2119435 3179261 := bbase (se 3 (by rfl) ⟨596111, by rfl⟩ : syracuseStep 3179261 = 1192223) (by norm_num)
theorem B2119507 : Blo 2119435 2119507 := bstep (se 1 (by rfl) ⟨1589630, by rfl⟩ : syracuseStep 2119507 = 3179261) B3179261
theorem B4768901 : Blo 2119435 4768901 := bbase (se 4 (by rfl) ⟨447084, by rfl⟩ : syracuseStep 4768901 = 894169) (by norm_num)
theorem B3179267 : Blo 2119435 3179267 := bstep (se 1 (by rfl) ⟨2384450, by rfl⟩ : syracuseStep 3179267 = 4768901) B4768901
theorem B2119511 : Blo 2119435 2119511 := bstep (se 1 (by rfl) ⟨1589633, by rfl⟩ : syracuseStep 2119511 = 3179267) B3179267
theorem B4526741 : Blo 2119435 4526741 := bbase (se 6 (by rfl) ⟨106095, by rfl⟩ : syracuseStep 4526741 = 212191) (by norm_num)
theorem B3017827 : Blo 2119435 3017827 := bstep (se 1 (by rfl) ⟨2263370, by rfl⟩ : syracuseStep 3017827 = 4526741) B4526741
theorem B4023769 : Blo 2119435 4023769 := bstep (se 2 (by rfl) ⟨1508913, by rfl⟩ : syracuseStep 4023769 = 3017827) B3017827
theorem B5365025 : Blo 2119435 5365025 := bstep (se 2 (by rfl) ⟨2011884, by rfl⟩ : syracuseStep 5365025 = 4023769) B4023769
theorem B3576683 : Blo 2119435 3576683 := bstep (se 1 (by rfl) ⟨2682512, by rfl⟩ : syracuseStep 3576683 = 5365025) B5365025
theorem B2384455 : Blo 2119435 2384455 := bstep (se 1 (by rfl) ⟨1788341, by rfl⟩ : syracuseStep 2384455 = 3576683) B3576683
theorem B3179273 : Blo 2119435 3179273 := bstep (se 2 (by rfl) ⟨1192227, by rfl⟩ : syracuseStep 3179273 = 2384455) B2384455
theorem B2119515 : Blo 2119435 2119515 := bstep (se 1 (by rfl) ⟨1589636, by rfl⟩ : syracuseStep 2119515 = 3179273) B3179273
theorem B10730069 : Blo 2119435 10730069 := bbase (se 8 (by rfl) ⟨62871, by rfl⟩ : syracuseStep 10730069 = 125743) (by norm_num)
theorem B7153379 : Blo 2119435 7153379 := bstep (se 1 (by rfl) ⟨5365034, by rfl⟩ : syracuseStep 7153379 = 10730069) B10730069
theorem B4768919 : Blo 2119435 4768919 := bstep (se 1 (by rfl) ⟨3576689, by rfl⟩ : syracuseStep 4768919 = 7153379) B7153379
theorem B3179279 : Blo 2119435 3179279 := bstep (se 1 (by rfl) ⟨2384459, by rfl⟩ : syracuseStep 3179279 = 4768919) B4768919
theorem B2119519 : Blo 2119435 2119519 := bstep (se 1 (by rfl) ⟨1589639, by rfl⟩ : syracuseStep 2119519 = 3179279) B3179279
theorem B3179285 : Blo 2119435 3179285 := bbase (se 6 (by rfl) ⟨74514, by rfl⟩ : syracuseStep 3179285 = 149029) (by norm_num)
theorem B2119523 : Blo 2119435 2119523 := bstep (se 1 (by rfl) ⟨1589642, by rfl⟩ : syracuseStep 2119523 = 3179285) B3179285
theorem B6118037 : Blo 2119435 6118037 := bbase (se 6 (by rfl) ⟨143391, by rfl⟩ : syracuseStep 6118037 = 286783) (by norm_num)
theorem B4078691 : Blo 2119435 4078691 := bstep (se 1 (by rfl) ⟨3059018, by rfl⟩ : syracuseStep 4078691 = 6118037) B6118037
theorem B2719127 : Blo 2119435 2719127 := bstep (se 1 (by rfl) ⟨2039345, by rfl⟩ : syracuseStep 2719127 = 4078691) B4078691
theorem B7251005 : Blo 2119435 7251005 := bstep (se 3 (by rfl) ⟨1359563, by rfl⟩ : syracuseStep 7251005 = 2719127) B2719127
theorem B4834003 : Blo 2119435 4834003 := bstep (se 1 (by rfl) ⟨3625502, by rfl⟩ : syracuseStep 4834003 = 7251005) B7251005
theorem B6445337 : Blo 2119435 6445337 := bstep (se 2 (by rfl) ⟨2417001, by rfl⟩ : syracuseStep 6445337 = 4834003) B4834003
theorem B17187565 : Blo 2119435 17187565 := bstep (se 3 (by rfl) ⟨3222668, by rfl⟩ : syracuseStep 17187565 = 6445337) B6445337
theorem B22916753 : Blo 2119435 22916753 := bstep (se 2 (by rfl) ⟨8593782, by rfl⟩ : syracuseStep 22916753 = 17187565) B17187565
theorem B15277835 : Blo 2119435 15277835 := bstep (se 1 (by rfl) ⟨11458376, by rfl⟩ : syracuseStep 15277835 = 22916753) B22916753
theorem B40740893 : Blo 2119435 40740893 := bstep (se 3 (by rfl) ⟨7638917, by rfl⟩ : syracuseStep 40740893 = 15277835) B15277835
theorem B27160595 : Blo 2119435 27160595 := bstep (se 1 (by rfl) ⟨20370446, by rfl⟩ : syracuseStep 27160595 = 40740893) B40740893
theorem B18107063 : Blo 2119435 18107063 := bstep (se 1 (by rfl) ⟨13580297, by rfl⟩ : syracuseStep 18107063 = 27160595) B27160595
theorem B12071375 : Blo 2119435 12071375 := bstep (se 1 (by rfl) ⟨9053531, by rfl⟩ : syracuseStep 12071375 = 18107063) B18107063
theorem B8047583 : Blo 2119435 8047583 := bstep (se 1 (by rfl) ⟨6035687, by rfl⟩ : syracuseStep 8047583 = 12071375) B12071375
theorem B5365055 : Blo 2119435 5365055 := bstep (se 1 (by rfl) ⟨4023791, by rfl⟩ : syracuseStep 5365055 = 8047583) B8047583
theorem B3576703 : Blo 2119435 3576703 := bstep (se 1 (by rfl) ⟨2682527, by rfl⟩ : syracuseStep 3576703 = 5365055) B5365055
theorem B4768937 : Blo 2119435 4768937 := bstep (se 2 (by rfl) ⟨1788351, by rfl⟩ : syracuseStep 4768937 = 3576703) B3576703
theorem B3179291 : Blo 2119435 3179291 := bstep (se 1 (by rfl) ⟨2384468, by rfl⟩ : syracuseStep 3179291 = 4768937) B4768937
theorem B2119527 : Blo 2119435 2119527 := bstep (se 1 (by rfl) ⟨1589645, by rfl⟩ : syracuseStep 2119527 = 3179291) B3179291
theorem B2384473 : Blo 2119435 2384473 := bbase (se 2 (by rfl) ⟨894177, by rfl⟩ : syracuseStep 2384473 = 1788355) (by norm_num)
theorem B3179297 : Blo 2119435 3179297 := bstep (se 2 (by rfl) ⟨1192236, by rfl⟩ : syracuseStep 3179297 = 2384473) B2384473
theorem B2119531 : Blo 2119435 2119531 := bstep (se 1 (by rfl) ⟨1589648, by rfl⟩ : syracuseStep 2119531 = 3179297) B3179297
theorem B43506197 : Blo 2119435 43506197 := bbase (se 6 (by rfl) ⟨1019676, by rfl⟩ : syracuseStep 43506197 = 2039353) (by norm_num)
theorem B29004131 : Blo 2119435 29004131 := bstep (se 1 (by rfl) ⟨21753098, by rfl⟩ : syracuseStep 29004131 = 43506197) B43506197
theorem B19336087 : Blo 2119435 19336087 := bstep (se 1 (by rfl) ⟨14502065, by rfl⟩ : syracuseStep 19336087 = 29004131) B29004131
theorem B25781449 : Blo 2119435 25781449 := bstep (se 2 (by rfl) ⟨9668043, by rfl⟩ : syracuseStep 25781449 = 19336087) B19336087
theorem B34375265 : Blo 2119435 34375265 := bstep (se 2 (by rfl) ⟨12890724, by rfl⟩ : syracuseStep 34375265 = 25781449) B25781449
theorem B22916843 : Blo 2119435 22916843 := bstep (se 1 (by rfl) ⟨17187632, by rfl⟩ : syracuseStep 22916843 = 34375265) B34375265
theorem B15277895 : Blo 2119435 15277895 := bstep (se 1 (by rfl) ⟨11458421, by rfl⟩ : syracuseStep 15277895 = 22916843) B22916843
theorem B10185263 : Blo 2119435 10185263 := bstep (se 1 (by rfl) ⟨7638947, by rfl⟩ : syracuseStep 10185263 = 15277895) B15277895
theorem B6790175 : Blo 2119435 6790175 := bstep (se 1 (by rfl) ⟨5092631, by rfl⟩ : syracuseStep 6790175 = 10185263) B10185263
theorem B4526783 : Blo 2119435 4526783 := bstep (se 1 (by rfl) ⟨3395087, by rfl⟩ : syracuseStep 4526783 = 6790175) B6790175
theorem B3017855 : Blo 2119435 3017855 := bstep (se 1 (by rfl) ⟨2263391, by rfl⟩ : syracuseStep 3017855 = 4526783) B4526783
theorem B8047613 : Blo 2119435 8047613 := bstep (se 3 (by rfl) ⟨1508927, by rfl⟩ : syracuseStep 8047613 = 3017855) B3017855
theorem B5365075 : Blo 2119435 5365075 := bstep (se 1 (by rfl) ⟨4023806, by rfl⟩ : syracuseStep 5365075 = 8047613) B8047613
theorem B7153433 : Blo 2119435 7153433 := bstep (se 2 (by rfl) ⟨2682537, by rfl⟩ : syracuseStep 7153433 = 5365075) B5365075
theorem B4768955 : Blo 2119435 4768955 := bstep (se 1 (by rfl) ⟨3576716, by rfl⟩ : syracuseStep 4768955 = 7153433) B7153433
theorem B3179303 : Blo 2119435 3179303 := bstep (se 1 (by rfl) ⟨2384477, by rfl⟩ : syracuseStep 3179303 = 4768955) B4768955
theorem B2119535 : Blo 2119435 2119535 := bstep (se 1 (by rfl) ⟨1589651, by rfl⟩ : syracuseStep 2119535 = 3179303) B3179303
theorem B3179309 : Blo 2119435 3179309 := bbase (se 3 (by rfl) ⟨596120, by rfl⟩ : syracuseStep 3179309 = 1192241) (by norm_num)
theorem B2119539 : Blo 2119435 2119539 := bstep (se 1 (by rfl) ⟨1589654, by rfl⟩ : syracuseStep 2119539 = 3179309) B3179309
theorem B4768973 : Blo 2119435 4768973 := bbase (se 3 (by rfl) ⟨894182, by rfl⟩ : syracuseStep 4768973 = 1788365) (by norm_num)
theorem B3179315 : Blo 2119435 3179315 := bstep (se 1 (by rfl) ⟨2384486, by rfl⟩ : syracuseStep 3179315 = 4768973) B4768973
theorem B2119543 : Blo 2119435 2119543 := bstep (se 1 (by rfl) ⟨1589657, by rfl⟩ : syracuseStep 2119543 = 3179315) B3179315
theorem B2682553 : Blo 2119435 2682553 := bbase (se 2 (by rfl) ⟨1005957, by rfl⟩ : syracuseStep 2682553 = 2011915) (by norm_num)
theorem B3576737 : Blo 2119435 3576737 := bstep (se 2 (by rfl) ⟨1341276, by rfl⟩ : syracuseStep 3576737 = 2682553) B2682553
theorem B2384491 : Blo 2119435 2384491 := bstep (se 1 (by rfl) ⟨1788368, by rfl⟩ : syracuseStep 2384491 = 3576737) B3576737
theorem B3179321 : Blo 2119435 3179321 := bstep (se 2 (by rfl) ⟨1192245, by rfl⟩ : syracuseStep 3179321 = 2384491) B2384491
theorem B2119547 : Blo 2119435 2119547 := bstep (se 1 (by rfl) ⟨1589660, by rfl⟩ : syracuseStep 2119547 = 3179321) B3179321
theorem B5092669 : Blo 2119435 5092669 := bbase (se 3 (by rfl) ⟨954875, by rfl⟩ : syracuseStep 5092669 = 1909751) (by norm_num)
theorem B6790225 : Blo 2119435 6790225 := bstep (se 2 (by rfl) ⟨2546334, by rfl⟩ : syracuseStep 6790225 = 5092669) B5092669
theorem B9053633 : Blo 2119435 9053633 := bstep (se 2 (by rfl) ⟨3395112, by rfl⟩ : syracuseStep 9053633 = 6790225) B6790225
theorem B24143021 : Blo 2119435 24143021 := bstep (se 3 (by rfl) ⟨4526816, by rfl⟩ : syracuseStep 24143021 = 9053633) B9053633
theorem B16095347 : Blo 2119435 16095347 := bstep (se 1 (by rfl) ⟨12071510, by rfl⟩ : syracuseStep 16095347 = 24143021) B24143021
theorem B10730231 : Blo 2119435 10730231 := bstep (se 1 (by rfl) ⟨8047673, by rfl⟩ : syracuseStep 10730231 = 16095347) B16095347
theorem B7153487 : Blo 2119435 7153487 := bstep (se 1 (by rfl) ⟨5365115, by rfl⟩ : syracuseStep 7153487 = 10730231) B10730231
theorem B4768991 : Blo 2119435 4768991 := bstep (se 1 (by rfl) ⟨3576743, by rfl⟩ : syracuseStep 4768991 = 7153487) B7153487
theorem B3179327 : Blo 2119435 3179327 := bstep (se 1 (by rfl) ⟨2384495, by rfl⟩ : syracuseStep 3179327 = 4768991) B4768991
theorem B2119551 : Blo 2119435 2119551 := bstep (se 1 (by rfl) ⟨1589663, by rfl⟩ : syracuseStep 2119551 = 3179327) B3179327
theorem B3179333 : Blo 2119435 3179333 := bbase (se 4 (by rfl) ⟨298062, by rfl⟩ : syracuseStep 3179333 = 596125) (by norm_num)
theorem B2119555 : Blo 2119435 2119555 := bstep (se 1 (by rfl) ⟨1589666, by rfl⟩ : syracuseStep 2119555 = 3179333) B3179333
theorem B3576757 : Blo 2119435 3576757 := bbase (se 5 (by rfl) ⟨167660, by rfl⟩ : syracuseStep 3576757 = 335321) (by norm_num)
theorem B4769009 : Blo 2119435 4769009 := bstep (se 2 (by rfl) ⟨1788378, by rfl⟩ : syracuseStep 4769009 = 3576757) B3576757
theorem B3179339 : Blo 2119435 3179339 := bstep (se 1 (by rfl) ⟨2384504, by rfl⟩ : syracuseStep 3179339 = 4769009) B4769009
theorem B2119559 : Blo 2119435 2119559 := bstep (se 1 (by rfl) ⟨1589669, by rfl⟩ : syracuseStep 2119559 = 3179339) B3179339
theorem B2384509 : Blo 2119435 2384509 := bbase (se 3 (by rfl) ⟨447095, by rfl⟩ : syracuseStep 2384509 = 894191) (by norm_num)
theorem B3179345 : Blo 2119435 3179345 := bstep (se 2 (by rfl) ⟨1192254, by rfl⟩ : syracuseStep 3179345 = 2384509) B2384509
theorem B2119563 : Blo 2119435 2119563 := bstep (se 1 (by rfl) ⟨1589672, by rfl⟩ : syracuseStep 2119563 = 3179345) B3179345
theorem B7153541 : Blo 2119435 7153541 := bbase (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) (by norm_num)
theorem B4769027 : Blo 2119435 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B3179351 : Blo 2119435 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B2119567 : Blo 2119435 2119567 := bstep (se 1 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 2119567 = 3179351) B3179351
theorem B3179357 : Blo 2119435 3179357 := bbase (se 3 (by rfl) ⟨596129, by rfl⟩ : syracuseStep 3179357 = 1192259) (by norm_num)
theorem B2119571 : Blo 2119435 2119571 := bstep (se 1 (by rfl) ⟨1589678, by rfl⟩ : syracuseStep 2119571 = 3179357) B3179357
theorem B4769045 : Blo 2119435 4769045 := bbase (se 6 (by rfl) ⟨111774, by rfl⟩ : syracuseStep 4769045 = 223549) (by norm_num)
theorem B3179363 : Blo 2119435 3179363 := bstep (se 1 (by rfl) ⟨2384522, by rfl⟩ : syracuseStep 3179363 = 4769045) B4769045
theorem B2119575 : Blo 2119435 2119575 := bstep (se 1 (by rfl) ⟨1589681, by rfl⟩ : syracuseStep 2119575 = 3179363) B3179363
theorem B8047781 : Blo 2119435 8047781 := bbase (se 4 (by rfl) ⟨754479, by rfl⟩ : syracuseStep 8047781 = 1508959) (by norm_num)
theorem B5365187 : Blo 2119435 5365187 := bstep (se 1 (by rfl) ⟨4023890, by rfl⟩ : syracuseStep 5365187 = 8047781) B8047781
theorem B3576791 : Blo 2119435 3576791 := bstep (se 1 (by rfl) ⟨2682593, by rfl⟩ : syracuseStep 3576791 = 5365187) B5365187
theorem B2384527 : Blo 2119435 2384527 := bstep (se 1 (by rfl) ⟨1788395, by rfl⟩ : syracuseStep 2384527 = 3576791) B3576791
theorem B3179369 : Blo 2119435 3179369 := bstep (se 2 (by rfl) ⟨1192263, by rfl⟩ : syracuseStep 3179369 = 2384527) B2384527
theorem B2119579 : Blo 2119435 2119579 := bstep (se 1 (by rfl) ⟨1589684, by rfl⟩ : syracuseStep 2119579 = 3179369) B3179369
theorem B4526885 : Blo 2119435 4526885 := bbase (se 4 (by rfl) ⟨424395, by rfl⟩ : syracuseStep 4526885 = 848791) (by norm_num)
theorem B12071693 : Blo 2119435 12071693 := bstep (se 3 (by rfl) ⟨2263442, by rfl⟩ : syracuseStep 12071693 = 4526885) B4526885
theorem B8047795 : Blo 2119435 8047795 := bstep (se 1 (by rfl) ⟨6035846, by rfl⟩ : syracuseStep 8047795 = 12071693) B12071693
theorem B10730393 : Blo 2119435 10730393 := bstep (se 2 (by rfl) ⟨4023897, by rfl⟩ : syracuseStep 10730393 = 8047795) B8047795
theorem B7153595 : Blo 2119435 7153595 := bstep (se 1 (by rfl) ⟨5365196, by rfl⟩ : syracuseStep 7153595 = 10730393) B10730393
theorem B4769063 : Blo 2119435 4769063 := bstep (se 1 (by rfl) ⟨3576797, by rfl⟩ : syracuseStep 4769063 = 7153595) B7153595
theorem B3179375 : Blo 2119435 3179375 := bstep (se 1 (by rfl) ⟨2384531, by rfl⟩ : syracuseStep 3179375 = 4769063) B4769063
theorem B2119583 : Blo 2119435 2119583 := bstep (se 1 (by rfl) ⟨1589687, by rfl⟩ : syracuseStep 2119583 = 3179375) B3179375
theorem B3179381 : Blo 2119435 3179381 := bbase (se 5 (by rfl) ⟨149033, by rfl⟩ : syracuseStep 3179381 = 298067) (by norm_num)
theorem B2119587 : Blo 2119435 2119587 := bstep (se 1 (by rfl) ⟨1589690, by rfl⟩ : syracuseStep 2119587 = 3179381) B3179381
theorem B2983541 : Blo 2119435 2983541 := bbase (se 5 (by rfl) ⟨139853, by rfl⟩ : syracuseStep 2983541 = 279707) (by norm_num)
theorem B7956109 : Blo 2119435 7956109 := bstep (se 3 (by rfl) ⟨1491770, by rfl⟩ : syracuseStep 7956109 = 2983541) B2983541
theorem B42432581 : Blo 2119435 42432581 := bstep (se 4 (by rfl) ⟨3978054, by rfl⟩ : syracuseStep 42432581 = 7956109) B7956109
theorem B28288387 : Blo 2119435 28288387 := bstep (se 1 (by rfl) ⟨21216290, by rfl⟩ : syracuseStep 28288387 = 42432581) B42432581
theorem B37717849 : Blo 2119435 37717849 := bstep (se 2 (by rfl) ⟨14144193, by rfl⟩ : syracuseStep 37717849 = 28288387) B28288387
theorem B50290465 : Blo 2119435 50290465 := bstep (se 2 (by rfl) ⟨18858924, by rfl⟩ : syracuseStep 50290465 = 37717849) B37717849
theorem B67053953 : Blo 2119435 67053953 := bstep (se 2 (by rfl) ⟨25145232, by rfl⟩ : syracuseStep 67053953 = 50290465) B50290465
theorem B178810541 : Blo 2119435 178810541 := bstep (se 3 (by rfl) ⟨33526976, by rfl⟩ : syracuseStep 178810541 = 67053953) B67053953
theorem B119207027 : Blo 2119435 119207027 := bstep (se 1 (by rfl) ⟨89405270, by rfl⟩ : syracuseStep 119207027 = 178810541) B178810541
theorem B317885405 : Blo 2119435 317885405 := bstep (se 3 (by rfl) ⟨59603513, by rfl⟩ : syracuseStep 317885405 = 119207027) B119207027
theorem B847694413 : Blo 2119435 847694413 := bstep (se 3 (by rfl) ⟨158942702, by rfl⟩ : syracuseStep 847694413 = 317885405) B317885405
theorem B1130259217 : Blo 2119435 1130259217 := bstep (se 2 (by rfl) ⟨423847206, by rfl⟩ : syracuseStep 1130259217 = 847694413) B847694413
theorem B1507012289 : Blo 2119435 1507012289 := bstep (se 2 (by rfl) ⟨565129608, by rfl⟩ : syracuseStep 1507012289 = 1130259217) B1130259217
theorem B1004674859 : Blo 2119435 1004674859 := bstep (se 1 (by rfl) ⟨753506144, by rfl⟩ : syracuseStep 1004674859 = 1507012289) B1507012289
theorem B669783239 : Blo 2119435 669783239 := bstep (se 1 (by rfl) ⟨502337429, by rfl⟩ : syracuseStep 669783239 = 1004674859) B1004674859
theorem B446522159 : Blo 2119435 446522159 := bstep (se 1 (by rfl) ⟨334891619, by rfl⟩ : syracuseStep 446522159 = 669783239) B669783239
theorem B297681439 : Blo 2119435 297681439 := bstep (se 1 (by rfl) ⟨223261079, by rfl⟩ : syracuseStep 297681439 = 446522159) B446522159
theorem B396908585 : Blo 2119435 396908585 := bstep (se 2 (by rfl) ⟨148840719, by rfl⟩ : syracuseStep 396908585 = 297681439) B297681439
theorem B264605723 : Blo 2119435 264605723 := bstep (se 1 (by rfl) ⟨198454292, by rfl⟩ : syracuseStep 264605723 = 396908585) B396908585
theorem B176403815 : Blo 2119435 176403815 := bstep (se 1 (by rfl) ⟨132302861, by rfl⟩ : syracuseStep 176403815 = 264605723) B264605723
theorem B117602543 : Blo 2119435 117602543 := bstep (se 1 (by rfl) ⟨88201907, by rfl⟩ : syracuseStep 117602543 = 176403815) B176403815
theorem B78401695 : Blo 2119435 78401695 := bstep (se 1 (by rfl) ⟨58801271, by rfl⟩ : syracuseStep 78401695 = 117602543) B117602543
theorem B104535593 : Blo 2119435 104535593 := bstep (se 2 (by rfl) ⟨39200847, by rfl⟩ : syracuseStep 104535593 = 78401695) B78401695
theorem B69690395 : Blo 2119435 69690395 := bstep (se 1 (by rfl) ⟨52267796, by rfl⟩ : syracuseStep 69690395 = 104535593) B104535593
theorem B46460263 : Blo 2119435 46460263 := bstep (se 1 (by rfl) ⟨34845197, by rfl⟩ : syracuseStep 46460263 = 69690395) B69690395
theorem B61947017 : Blo 2119435 61947017 := bstep (se 2 (by rfl) ⟨23230131, by rfl⟩ : syracuseStep 61947017 = 46460263) B46460263
theorem B41298011 : Blo 2119435 41298011 := bstep (se 1 (by rfl) ⟨30973508, by rfl⟩ : syracuseStep 41298011 = 61947017) B61947017
theorem B27532007 : Blo 2119435 27532007 := bstep (se 1 (by rfl) ⟨20649005, by rfl⟩ : syracuseStep 27532007 = 41298011) B41298011
theorem B18354671 : Blo 2119435 18354671 := bstep (se 1 (by rfl) ⟨13766003, by rfl⟩ : syracuseStep 18354671 = 27532007) B27532007
theorem B12236447 : Blo 2119435 12236447 := bstep (se 1 (by rfl) ⟨9177335, by rfl⟩ : syracuseStep 12236447 = 18354671) B18354671
theorem B8157631 : Blo 2119435 8157631 := bstep (se 1 (by rfl) ⟨6118223, by rfl⟩ : syracuseStep 8157631 = 12236447) B12236447
theorem B10876841 : Blo 2119435 10876841 := bstep (se 2 (by rfl) ⟨4078815, by rfl⟩ : syracuseStep 10876841 = 8157631) B8157631
theorem B7251227 : Blo 2119435 7251227 := bstep (se 1 (by rfl) ⟨5438420, by rfl⟩ : syracuseStep 7251227 = 10876841) B10876841
theorem B4834151 : Blo 2119435 4834151 := bstep (se 1 (by rfl) ⟨3625613, by rfl⟩ : syracuseStep 4834151 = 7251227) B7251227
theorem B3222767 : Blo 2119435 3222767 := bstep (se 1 (by rfl) ⟨2417075, by rfl⟩ : syracuseStep 3222767 = 4834151) B4834151
theorem B8594045 : Blo 2119435 8594045 := bstep (se 3 (by rfl) ⟨1611383, by rfl⟩ : syracuseStep 8594045 = 3222767) B3222767
theorem B5729363 : Blo 2119435 5729363 := bstep (se 1 (by rfl) ⟨4297022, by rfl⟩ : syracuseStep 5729363 = 8594045) B8594045
theorem B3819575 : Blo 2119435 3819575 := bstep (se 1 (by rfl) ⟨2864681, by rfl⟩ : syracuseStep 3819575 = 5729363) B5729363
theorem B10185533 : Blo 2119435 10185533 := bstep (se 3 (by rfl) ⟨1909787, by rfl⟩ : syracuseStep 10185533 = 3819575) B3819575
theorem B6790355 : Blo 2119435 6790355 := bstep (se 1 (by rfl) ⟨5092766, by rfl⟩ : syracuseStep 6790355 = 10185533) B10185533
theorem B4526903 : Blo 2119435 4526903 := bstep (se 1 (by rfl) ⟨3395177, by rfl⟩ : syracuseStep 4526903 = 6790355) B6790355
theorem B3017935 : Blo 2119435 3017935 := bstep (se 1 (by rfl) ⟨2263451, by rfl⟩ : syracuseStep 3017935 = 4526903) B4526903
theorem B4023913 : Blo 2119435 4023913 := bstep (se 2 (by rfl) ⟨1508967, by rfl⟩ : syracuseStep 4023913 = 3017935) B3017935
theorem B5365217 : Blo 2119435 5365217 := bstep (se 2 (by rfl) ⟨2011956, by rfl⟩ : syracuseStep 5365217 = 4023913) B4023913
theorem B3576811 : Blo 2119435 3576811 := bstep (se 1 (by rfl) ⟨2682608, by rfl⟩ : syracuseStep 3576811 = 5365217) B5365217
theorem B4769081 : Blo 2119435 4769081 := bstep (se 2 (by rfl) ⟨1788405, by rfl⟩ : syracuseStep 4769081 = 3576811) B3576811
theorem B3179387 : Blo 2119435 3179387 := bstep (se 1 (by rfl) ⟨2384540, by rfl⟩ : syracuseStep 3179387 = 4769081) B4769081
theorem B2119591 : Blo 2119435 2119591 := bstep (se 1 (by rfl) ⟨1589693, by rfl⟩ : syracuseStep 2119591 = 3179387) B3179387
theorem B2384545 : Blo 2119435 2384545 := bbase (se 2 (by rfl) ⟨894204, by rfl⟩ : syracuseStep 2384545 = 1788409) (by norm_num)
theorem B3179393 : Blo 2119435 3179393 := bstep (se 2 (by rfl) ⟨1192272, by rfl⟩ : syracuseStep 3179393 = 2384545) B2384545
theorem B2119595 : Blo 2119435 2119595 := bstep (se 1 (by rfl) ⟨1589696, by rfl⟩ : syracuseStep 2119595 = 3179393) B3179393
theorem B5365237 : Blo 2119435 5365237 := bbase (se 5 (by rfl) ⟨251495, by rfl⟩ : syracuseStep 5365237 = 502991) (by norm_num)
theorem B7153649 : Blo 2119435 7153649 := bstep (se 2 (by rfl) ⟨2682618, by rfl⟩ : syracuseStep 7153649 = 5365237) B5365237
theorem B4769099 : Blo 2119435 4769099 := bstep (se 1 (by rfl) ⟨3576824, by rfl⟩ : syracuseStep 4769099 = 7153649) B7153649
theorem B3179399 : Blo 2119435 3179399 := bstep (se 1 (by rfl) ⟨2384549, by rfl⟩ : syracuseStep 3179399 = 4769099) B4769099
theorem B2119599 : Blo 2119435 2119599 := bstep (se 1 (by rfl) ⟨1589699, by rfl⟩ : syracuseStep 2119599 = 3179399) B3179399
theorem B3179405 : Blo 2119435 3179405 := bbase (se 3 (by rfl) ⟨596138, by rfl⟩ : syracuseStep 3179405 = 1192277) (by norm_num)
theorem B2119603 : Blo 2119435 2119603 := bstep (se 1 (by rfl) ⟨1589702, by rfl⟩ : syracuseStep 2119603 = 3179405) B3179405
theorem B4769117 : Blo 2119435 4769117 := bbase (se 3 (by rfl) ⟨894209, by rfl⟩ : syracuseStep 4769117 = 1788419) (by norm_num)
theorem B3179411 : Blo 2119435 3179411 := bstep (se 1 (by rfl) ⟨2384558, by rfl⟩ : syracuseStep 3179411 = 4769117) B4769117
theorem B2119607 : Blo 2119435 2119607 := bstep (se 1 (by rfl) ⟨1589705, by rfl⟩ : syracuseStep 2119607 = 3179411) B3179411
theorem B3576845 : Blo 2119435 3576845 := bbase (se 3 (by rfl) ⟨670658, by rfl⟩ : syracuseStep 3576845 = 1341317) (by norm_num)
theorem B2384563 : Blo 2119435 2384563 := bstep (se 1 (by rfl) ⟨1788422, by rfl⟩ : syracuseStep 2384563 = 3576845) B3576845
theorem B3179417 : Blo 2119435 3179417 := bstep (se 2 (by rfl) ⟨1192281, by rfl⟩ : syracuseStep 3179417 = 2384563) B2384563
theorem B2119611 : Blo 2119435 2119611 := bstep (se 1 (by rfl) ⟨1589708, by rfl⟩ : syracuseStep 2119611 = 3179417) B3179417
theorem B4834205 : Blo 2119435 4834205 := bbase (se 3 (by rfl) ⟨906413, by rfl⟩ : syracuseStep 4834205 = 1812827) (by norm_num)
theorem B3222803 : Blo 2119435 3222803 := bstep (se 1 (by rfl) ⟨2417102, by rfl⟩ : syracuseStep 3222803 = 4834205) B4834205
theorem B2148535 : Blo 2119435 2148535 := bstep (se 1 (by rfl) ⟨1611401, by rfl⟩ : syracuseStep 2148535 = 3222803) B3222803
theorem B11458853 : Blo 2119435 11458853 := bstep (se 4 (by rfl) ⟨1074267, by rfl⟩ : syracuseStep 11458853 = 2148535) B2148535
theorem B7639235 : Blo 2119435 7639235 := bstep (se 1 (by rfl) ⟨5729426, by rfl⟩ : syracuseStep 7639235 = 11458853) B11458853
theorem B5092823 : Blo 2119435 5092823 := bstep (se 1 (by rfl) ⟨3819617, by rfl⟩ : syracuseStep 5092823 = 7639235) B7639235
theorem B3395215 : Blo 2119435 3395215 := bstep (se 1 (by rfl) ⟨2546411, by rfl⟩ : syracuseStep 3395215 = 5092823) B5092823
theorem B18107813 : Blo 2119435 18107813 := bstep (se 4 (by rfl) ⟨1697607, by rfl⟩ : syracuseStep 18107813 = 3395215) B3395215
theorem B12071875 : Blo 2119435 12071875 := bstep (se 1 (by rfl) ⟨9053906, by rfl⟩ : syracuseStep 12071875 = 18107813) B18107813
theorem B16095833 : Blo 2119435 16095833 := bstep (se 2 (by rfl) ⟨6035937, by rfl⟩ : syracuseStep 16095833 = 12071875) B12071875
theorem B10730555 : Blo 2119435 10730555 := bstep (se 1 (by rfl) ⟨8047916, by rfl⟩ : syracuseStep 10730555 = 16095833) B16095833
theorem B7153703 : Blo 2119435 7153703 := bstep (se 1 (by rfl) ⟨5365277, by rfl⟩ : syracuseStep 7153703 = 10730555) B10730555
theorem B4769135 : Blo 2119435 4769135 := bstep (se 1 (by rfl) ⟨3576851, by rfl⟩ : syracuseStep 4769135 = 7153703) B7153703
theorem B3179423 : Blo 2119435 3179423 := bstep (se 1 (by rfl) ⟨2384567, by rfl⟩ : syracuseStep 3179423 = 4769135) B4769135
theorem B2119615 : Blo 2119435 2119615 := bstep (se 1 (by rfl) ⟨1589711, by rfl⟩ : syracuseStep 2119615 = 3179423) B3179423
theorem B3179429 : Blo 2119435 3179429 := bbase (se 4 (by rfl) ⟨298071, by rfl⟩ : syracuseStep 3179429 = 596143) (by norm_num)
theorem B2119619 : Blo 2119435 2119619 := bstep (se 1 (by rfl) ⟨1589714, by rfl⟩ : syracuseStep 2119619 = 3179429) B3179429
theorem B2682649 : Blo 2119435 2682649 := bbase (se 2 (by rfl) ⟨1005993, by rfl⟩ : syracuseStep 2682649 = 2011987) (by norm_num)
theorem B3576865 : Blo 2119435 3576865 := bstep (se 2 (by rfl) ⟨1341324, by rfl⟩ : syracuseStep 3576865 = 2682649) B2682649
theorem B4769153 : Blo 2119435 4769153 := bstep (se 2 (by rfl) ⟨1788432, by rfl⟩ : syracuseStep 4769153 = 3576865) B3576865
theorem B3179435 : Blo 2119435 3179435 := bstep (se 1 (by rfl) ⟨2384576, by rfl⟩ : syracuseStep 3179435 = 4769153) B4769153
theorem B2119623 : Blo 2119435 2119623 := bstep (se 1 (by rfl) ⟨1589717, by rfl⟩ : syracuseStep 2119623 = 3179435) B3179435
theorem B2384581 : Blo 2119435 2384581 := bbase (se 4 (by rfl) ⟨223554, by rfl⟩ : syracuseStep 2384581 = 447109) (by norm_num)
theorem B3179441 : Blo 2119435 3179441 := bstep (se 2 (by rfl) ⟨1192290, by rfl⟩ : syracuseStep 3179441 = 2384581) B2384581
theorem B2119627 : Blo 2119435 2119627 := bstep (se 1 (by rfl) ⟨1589720, by rfl⟩ : syracuseStep 2119627 = 3179441) B3179441
theorem B4023989 : Blo 2119435 4023989 := bbase (se 5 (by rfl) ⟨188624, by rfl⟩ : syracuseStep 4023989 = 377249) (by norm_num)
theorem B2682659 : Blo 2119435 2682659 := bstep (se 1 (by rfl) ⟨2011994, by rfl⟩ : syracuseStep 2682659 = 4023989) B4023989
theorem B7153757 : Blo 2119435 7153757 := bstep (se 3 (by rfl) ⟨1341329, by rfl⟩ : syracuseStep 7153757 = 2682659) B2682659
theorem B4769171 : Blo 2119435 4769171 := bstep (se 1 (by rfl) ⟨3576878, by rfl⟩ : syracuseStep 4769171 = 7153757) B7153757
theorem B3179447 : Blo 2119435 3179447 := bstep (se 1 (by rfl) ⟨2384585, by rfl⟩ : syracuseStep 3179447 = 4769171) B4769171
theorem B2119631 : Blo 2119435 2119631 := bstep (se 1 (by rfl) ⟨1589723, by rfl⟩ : syracuseStep 2119631 = 3179447) B3179447
theorem B3179453 : Blo 2119435 3179453 := bbase (se 3 (by rfl) ⟨596147, by rfl⟩ : syracuseStep 3179453 = 1192295) (by norm_num)
theorem B2119635 : Blo 2119435 2119635 := bstep (se 1 (by rfl) ⟨1589726, by rfl⟩ : syracuseStep 2119635 = 3179453) B3179453
theorem B4769189 : Blo 2119435 4769189 := bbase (se 4 (by rfl) ⟨447111, by rfl⟩ : syracuseStep 4769189 = 894223) (by norm_num)
theorem B3179459 : Blo 2119435 3179459 := bstep (se 1 (by rfl) ⟨2384594, by rfl⟩ : syracuseStep 3179459 = 4769189) B4769189
theorem B2119639 : Blo 2119435 2119639 := bstep (se 1 (by rfl) ⟨1589729, by rfl⟩ : syracuseStep 2119639 = 3179459) B3179459
theorem B5365349 : Blo 2119435 5365349 := bbase (se 4 (by rfl) ⟨503001, by rfl⟩ : syracuseStep 5365349 = 1006003) (by norm_num)
theorem B3576899 : Blo 2119435 3576899 := bstep (se 1 (by rfl) ⟨2682674, by rfl⟩ : syracuseStep 3576899 = 5365349) B5365349
theorem B2384599 : Blo 2119435 2384599 := bstep (se 1 (by rfl) ⟨1788449, by rfl⟩ : syracuseStep 2384599 = 3576899) B3576899
theorem B3179465 : Blo 2119435 3179465 := bstep (se 2 (by rfl) ⟨1192299, by rfl⟩ : syracuseStep 3179465 = 2384599) B2384599
theorem B2119643 : Blo 2119435 2119643 := bstep (se 1 (by rfl) ⟨1589732, by rfl⟩ : syracuseStep 2119643 = 3179465) B3179465
theorem B5092901 : Blo 2119435 5092901 := bbase (se 4 (by rfl) ⟨477459, by rfl⟩ : syracuseStep 5092901 = 954919) (by norm_num)
theorem B3395267 : Blo 2119435 3395267 := bstep (se 1 (by rfl) ⟨2546450, by rfl⟩ : syracuseStep 3395267 = 5092901) B5092901
theorem B2263511 : Blo 2119435 2263511 := bstep (se 1 (by rfl) ⟨1697633, by rfl⟩ : syracuseStep 2263511 = 3395267) B3395267
theorem B6036029 : Blo 2119435 6036029 := bstep (se 3 (by rfl) ⟨1131755, by rfl⟩ : syracuseStep 6036029 = 2263511) B2263511
theorem B4024019 : Blo 2119435 4024019 := bstep (se 1 (by rfl) ⟨3018014, by rfl⟩ : syracuseStep 4024019 = 6036029) B6036029
theorem B10730717 : Blo 2119435 10730717 := bstep (se 3 (by rfl) ⟨2012009, by rfl⟩ : syracuseStep 10730717 = 4024019) B4024019
theorem B7153811 : Blo 2119435 7153811 := bstep (se 1 (by rfl) ⟨5365358, by rfl⟩ : syracuseStep 7153811 = 10730717) B10730717
theorem B4769207 : Blo 2119435 4769207 := bstep (se 1 (by rfl) ⟨3576905, by rfl⟩ : syracuseStep 4769207 = 7153811) B7153811
theorem B3179471 : Blo 2119435 3179471 := bstep (se 1 (by rfl) ⟨2384603, by rfl⟩ : syracuseStep 3179471 = 4769207) B4769207
theorem B2119647 : Blo 2119435 2119647 := bstep (se 1 (by rfl) ⟨1589735, by rfl⟩ : syracuseStep 2119647 = 3179471) B3179471
theorem B3179477 : Blo 2119435 3179477 := bbase (se 7 (by rfl) ⟨37259, by rfl⟩ : syracuseStep 3179477 = 74519) (by norm_num)
theorem B2119651 : Blo 2119435 2119651 := bstep (se 1 (by rfl) ⟨1589738, by rfl⟩ : syracuseStep 2119651 = 3179477) B3179477
theorem B8048069 : Blo 2119435 8048069 := bbase (se 4 (by rfl) ⟨754506, by rfl⟩ : syracuseStep 8048069 = 1509013) (by norm_num)
theorem B5365379 : Blo 2119435 5365379 := bstep (se 1 (by rfl) ⟨4024034, by rfl⟩ : syracuseStep 5365379 = 8048069) B8048069
theorem B3576919 : Blo 2119435 3576919 := bstep (se 1 (by rfl) ⟨2682689, by rfl⟩ : syracuseStep 3576919 = 5365379) B5365379
theorem B4769225 : Blo 2119435 4769225 := bstep (se 2 (by rfl) ⟨1788459, by rfl⟩ : syracuseStep 4769225 = 3576919) B3576919
theorem B3179483 : Blo 2119435 3179483 := bstep (se 1 (by rfl) ⟨2384612, by rfl⟩ : syracuseStep 3179483 = 4769225) B4769225
theorem B2119655 : Blo 2119435 2119655 := bstep (se 1 (by rfl) ⟨1589741, by rfl⟩ : syracuseStep 2119655 = 3179483) B3179483
theorem B2384617 : Blo 2119435 2384617 := bbase (se 2 (by rfl) ⟨894231, by rfl⟩ : syracuseStep 2384617 = 1788463) (by norm_num)
theorem B3179489 : Blo 2119435 3179489 := bstep (se 2 (by rfl) ⟨1192308, by rfl⟩ : syracuseStep 3179489 = 2384617) B2384617
theorem B2119659 : Blo 2119435 2119659 := bstep (se 1 (by rfl) ⟨1589744, by rfl⟩ : syracuseStep 2119659 = 3179489) B3179489
theorem B12072149 : Blo 2119435 12072149 := bbase (se 7 (by rfl) ⟨141470, by rfl⟩ : syracuseStep 12072149 = 282941) (by norm_num)
theorem B8048099 : Blo 2119435 8048099 := bstep (se 1 (by rfl) ⟨6036074, by rfl⟩ : syracuseStep 8048099 = 12072149) B12072149
theorem B5365399 : Blo 2119435 5365399 := bstep (se 1 (by rfl) ⟨4024049, by rfl⟩ : syracuseStep 5365399 = 8048099) B8048099
theorem B7153865 : Blo 2119435 7153865 := bstep (se 2 (by rfl) ⟨2682699, by rfl⟩ : syracuseStep 7153865 = 5365399) B5365399
theorem B4769243 : Blo 2119435 4769243 := bstep (se 1 (by rfl) ⟨3576932, by rfl⟩ : syracuseStep 4769243 = 7153865) B7153865
theorem B3179495 : Blo 2119435 3179495 := bstep (se 1 (by rfl) ⟨2384621, by rfl⟩ : syracuseStep 3179495 = 4769243) B4769243
theorem B2119663 : Blo 2119435 2119663 := bstep (se 1 (by rfl) ⟨1589747, by rfl⟩ : syracuseStep 2119663 = 3179495) B3179495
theorem B3179501 : Blo 2119435 3179501 := bbase (se 3 (by rfl) ⟨596156, by rfl⟩ : syracuseStep 3179501 = 1192313) (by norm_num)
theorem B2119667 : Blo 2119435 2119667 := bstep (se 1 (by rfl) ⟨1589750, by rfl⟩ : syracuseStep 2119667 = 3179501) B3179501
theorem B4769261 : Blo 2119435 4769261 := bbase (se 3 (by rfl) ⟨894236, by rfl⟩ : syracuseStep 4769261 = 1788473) (by norm_num)
theorem B3179507 : Blo 2119435 3179507 := bstep (se 1 (by rfl) ⟨2384630, by rfl⟩ : syracuseStep 3179507 = 4769261) B4769261
theorem B2119671 : Blo 2119435 2119671 := bstep (se 1 (by rfl) ⟨1589753, by rfl⟩ : syracuseStep 2119671 = 3179507) B3179507
theorem B2294425 : Blo 2119435 2294425 := bbase (se 2 (by rfl) ⟨860409, by rfl⟩ : syracuseStep 2294425 = 1720819) (by norm_num)
theorem B12236933 : Blo 2119435 12236933 := bstep (se 4 (by rfl) ⟨1147212, by rfl⟩ : syracuseStep 12236933 = 2294425) B2294425
theorem B8157955 : Blo 2119435 8157955 := bstep (se 1 (by rfl) ⟨6118466, by rfl⟩ : syracuseStep 8157955 = 12236933) B12236933
theorem B10877273 : Blo 2119435 10877273 := bstep (se 2 (by rfl) ⟨4078977, by rfl⟩ : syracuseStep 10877273 = 8157955) B8157955
theorem B7251515 : Blo 2119435 7251515 := bstep (se 1 (by rfl) ⟨5438636, by rfl⟩ : syracuseStep 7251515 = 10877273) B10877273
theorem B4834343 : Blo 2119435 4834343 := bstep (se 1 (by rfl) ⟨3625757, by rfl⟩ : syracuseStep 4834343 = 7251515) B7251515
theorem B12891581 : Blo 2119435 12891581 := bstep (se 3 (by rfl) ⟨2417171, by rfl⟩ : syracuseStep 12891581 = 4834343) B4834343
theorem B8594387 : Blo 2119435 8594387 := bstep (se 1 (by rfl) ⟨6445790, by rfl⟩ : syracuseStep 8594387 = 12891581) B12891581
theorem B5729591 : Blo 2119435 5729591 := bstep (se 1 (by rfl) ⟨4297193, by rfl⟩ : syracuseStep 5729591 = 8594387) B8594387
theorem B3819727 : Blo 2119435 3819727 := bstep (se 1 (by rfl) ⟨2864795, by rfl⟩ : syracuseStep 3819727 = 5729591) B5729591
theorem B5092969 : Blo 2119435 5092969 := bstep (se 2 (by rfl) ⟨1909863, by rfl⟩ : syracuseStep 5092969 = 3819727) B3819727
theorem B6790625 : Blo 2119435 6790625 := bstep (se 2 (by rfl) ⟨2546484, by rfl⟩ : syracuseStep 6790625 = 5092969) B5092969
theorem B4527083 : Blo 2119435 4527083 := bstep (se 1 (by rfl) ⟨3395312, by rfl⟩ : syracuseStep 4527083 = 6790625) B6790625
theorem B3018055 : Blo 2119435 3018055 := bstep (se 1 (by rfl) ⟨2263541, by rfl⟩ : syracuseStep 3018055 = 4527083) B4527083
theorem B4024073 : Blo 2119435 4024073 := bstep (se 2 (by rfl) ⟨1509027, by rfl⟩ : syracuseStep 4024073 = 3018055) B3018055
theorem B2682715 : Blo 2119435 2682715 := bstep (se 1 (by rfl) ⟨2012036, by rfl⟩ : syracuseStep 2682715 = 4024073) B4024073
theorem B3576953 : Blo 2119435 3576953 := bstep (se 2 (by rfl) ⟨1341357, by rfl⟩ : syracuseStep 3576953 = 2682715) B2682715
theorem B2384635 : Blo 2119435 2384635 := bstep (se 1 (by rfl) ⟨1788476, by rfl⟩ : syracuseStep 2384635 = 3576953) B3576953
theorem B3179513 : Blo 2119435 3179513 := bstep (se 2 (by rfl) ⟨1192317, by rfl⟩ : syracuseStep 3179513 = 2384635) B2384635
theorem B2119675 : Blo 2119435 2119675 := bstep (se 1 (by rfl) ⟨1589756, by rfl⟩ : syracuseStep 2119675 = 3179513) B3179513
theorem B10877285 : Blo 2119435 10877285 := bbase (se 4 (by rfl) ⟨1019745, by rfl⟩ : syracuseStep 10877285 = 2039491) (by norm_num)
theorem B29006093 : Blo 2119435 29006093 := bstep (se 3 (by rfl) ⟨5438642, by rfl⟩ : syracuseStep 29006093 = 10877285) B10877285
theorem B19337395 : Blo 2119435 19337395 := bstep (se 1 (by rfl) ⟨14503046, by rfl⟩ : syracuseStep 19337395 = 29006093) B29006093
theorem B25783193 : Blo 2119435 25783193 := bstep (se 2 (by rfl) ⟨9668697, by rfl⟩ : syracuseStep 25783193 = 19337395) B19337395
theorem B17188795 : Blo 2119435 17188795 := bstep (se 1 (by rfl) ⟨12891596, by rfl⟩ : syracuseStep 17188795 = 25783193) B25783193
theorem B22918393 : Blo 2119435 22918393 := bstep (se 2 (by rfl) ⟨8594397, by rfl⟩ : syracuseStep 22918393 = 17188795) B17188795
theorem B122231429 : Blo 2119435 122231429 := bstep (se 4 (by rfl) ⟨11459196, by rfl⟩ : syracuseStep 122231429 = 22918393) B22918393
theorem B81487619 : Blo 2119435 81487619 := bstep (se 1 (by rfl) ⟨61115714, by rfl⟩ : syracuseStep 81487619 = 122231429) B122231429
theorem B54325079 : Blo 2119435 54325079 := bstep (se 1 (by rfl) ⟨40743809, by rfl⟩ : syracuseStep 54325079 = 81487619) B81487619
theorem B36216719 : Blo 2119435 36216719 := bstep (se 1 (by rfl) ⟨27162539, by rfl⟩ : syracuseStep 36216719 = 54325079) B54325079
theorem B24144479 : Blo 2119435 24144479 := bstep (se 1 (by rfl) ⟨18108359, by rfl⟩ : syracuseStep 24144479 = 36216719) B36216719
theorem B16096319 : Blo 2119435 16096319 := bstep (se 1 (by rfl) ⟨12072239, by rfl⟩ : syracuseStep 16096319 = 24144479) B24144479
theorem B10730879 : Blo 2119435 10730879 := bstep (se 1 (by rfl) ⟨8048159, by rfl⟩ : syracuseStep 10730879 = 16096319) B16096319
theorem B7153919 : Blo 2119435 7153919 := bstep (se 1 (by rfl) ⟨5365439, by rfl⟩ : syracuseStep 7153919 = 10730879) B10730879
theorem B4769279 : Blo 2119435 4769279 := bstep (se 1 (by rfl) ⟨3576959, by rfl⟩ : syracuseStep 4769279 = 7153919) B7153919
theorem B3179519 : Blo 2119435 3179519 := bstep (se 1 (by rfl) ⟨2384639, by rfl⟩ : syracuseStep 3179519 = 4769279) B4769279
theorem B2119679 : Blo 2119435 2119679 := bstep (se 1 (by rfl) ⟨1589759, by rfl⟩ : syracuseStep 2119679 = 3179519) B3179519
theorem B3179525 : Blo 2119435 3179525 := bbase (se 4 (by rfl) ⟨298080, by rfl⟩ : syracuseStep 3179525 = 596161) (by norm_num)
theorem B2119683 : Blo 2119435 2119683 := bstep (se 1 (by rfl) ⟨1589762, by rfl⟩ : syracuseStep 2119683 = 3179525) B3179525
theorem B3576973 : Blo 2119435 3576973 := bbase (se 3 (by rfl) ⟨670682, by rfl⟩ : syracuseStep 3576973 = 1341365) (by norm_num)
theorem B4769297 : Blo 2119435 4769297 := bstep (se 2 (by rfl) ⟨1788486, by rfl⟩ : syracuseStep 4769297 = 3576973) B3576973
theorem B3179531 : Blo 2119435 3179531 := bstep (se 1 (by rfl) ⟨2384648, by rfl⟩ : syracuseStep 3179531 = 4769297) B4769297
theorem B2119687 : Blo 2119435 2119687 := bstep (se 1 (by rfl) ⟨1589765, by rfl⟩ : syracuseStep 2119687 = 3179531) B3179531
theorem B2384653 : Blo 2119435 2384653 := bbase (se 3 (by rfl) ⟨447122, by rfl⟩ : syracuseStep 2384653 = 894245) (by norm_num)
theorem B3179537 : Blo 2119435 3179537 := bstep (se 2 (by rfl) ⟨1192326, by rfl⟩ : syracuseStep 3179537 = 2384653) B2384653
theorem B2119691 : Blo 2119435 2119691 := bstep (se 1 (by rfl) ⟨1589768, by rfl⟩ : syracuseStep 2119691 = 3179537) B3179537
theorem B7153973 : Blo 2119435 7153973 := bbase (se 5 (by rfl) ⟨335342, by rfl⟩ : syracuseStep 7153973 = 670685) (by norm_num)
theorem B4769315 : Blo 2119435 4769315 := bstep (se 1 (by rfl) ⟨3576986, by rfl⟩ : syracuseStep 4769315 = 7153973) B7153973
theorem B3179543 : Blo 2119435 3179543 := bstep (se 1 (by rfl) ⟨2384657, by rfl⟩ : syracuseStep 3179543 = 4769315) B4769315
theorem B2119695 : Blo 2119435 2119695 := bstep (se 1 (by rfl) ⟨1589771, by rfl⟩ : syracuseStep 2119695 = 3179543) B3179543
theorem B3179549 : Blo 2119435 3179549 := bbase (se 3 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 3179549 = 1192331) (by norm_num)
theorem B2119699 : Blo 2119435 2119699 := bstep (se 1 (by rfl) ⟨1589774, by rfl⟩ : syracuseStep 2119699 = 3179549) B3179549
theorem B4769333 : Blo 2119435 4769333 := bbase (se 5 (by rfl) ⟨223562, by rfl⟩ : syracuseStep 4769333 = 447125) (by norm_num)
theorem B3179555 : Blo 2119435 3179555 := bstep (se 1 (by rfl) ⟨2384666, by rfl⟩ : syracuseStep 3179555 = 4769333) B4769333
theorem B2119703 : Blo 2119435 2119703 := bstep (se 1 (by rfl) ⟨1589777, by rfl⟩ : syracuseStep 2119703 = 3179555) B3179555
theorem B5093045 : Blo 2119435 5093045 := bbase (se 5 (by rfl) ⟨238736, by rfl⟩ : syracuseStep 5093045 = 477473) (by norm_num)
theorem B3395363 : Blo 2119435 3395363 := bstep (se 1 (by rfl) ⟨2546522, by rfl⟩ : syracuseStep 3395363 = 5093045) B5093045
theorem B9054301 : Blo 2119435 9054301 := bstep (se 3 (by rfl) ⟨1697681, by rfl⟩ : syracuseStep 9054301 = 3395363) B3395363
theorem B12072401 : Blo 2119435 12072401 := bstep (se 2 (by rfl) ⟨4527150, by rfl⟩ : syracuseStep 12072401 = 9054301) B9054301
theorem B8048267 : Blo 2119435 8048267 := bstep (se 1 (by rfl) ⟨6036200, by rfl⟩ : syracuseStep 8048267 = 12072401) B12072401
theorem B5365511 : Blo 2119435 5365511 := bstep (se 1 (by rfl) ⟨4024133, by rfl⟩ : syracuseStep 5365511 = 8048267) B8048267
theorem B3577007 : Blo 2119435 3577007 := bstep (se 1 (by rfl) ⟨2682755, by rfl⟩ : syracuseStep 3577007 = 5365511) B5365511
theorem B2384671 : Blo 2119435 2384671 := bstep (se 1 (by rfl) ⟨1788503, by rfl⟩ : syracuseStep 2384671 = 3577007) B3577007
theorem B3179561 : Blo 2119435 3179561 := bstep (se 2 (by rfl) ⟨1192335, by rfl⟩ : syracuseStep 3179561 = 2384671) B2384671
theorem B2119707 : Blo 2119435 2119707 := bstep (se 1 (by rfl) ⟨1589780, by rfl⟩ : syracuseStep 2119707 = 3179561) B3179561
theorem B12891797 : Blo 2119435 12891797 := bbase (se 6 (by rfl) ⟨302151, by rfl⟩ : syracuseStep 12891797 = 604303) (by norm_num)
theorem B8594531 : Blo 2119435 8594531 := bstep (se 1 (by rfl) ⟨6445898, by rfl⟩ : syracuseStep 8594531 = 12891797) B12891797
theorem B5729687 : Blo 2119435 5729687 := bstep (se 1 (by rfl) ⟨4297265, by rfl⟩ : syracuseStep 5729687 = 8594531) B8594531
theorem B3819791 : Blo 2119435 3819791 := bstep (se 1 (by rfl) ⟨2864843, by rfl⟩ : syracuseStep 3819791 = 5729687) B5729687
theorem B2546527 : Blo 2119435 2546527 := bstep (se 1 (by rfl) ⟨1909895, by rfl⟩ : syracuseStep 2546527 = 3819791) B3819791
theorem B3395369 : Blo 2119435 3395369 := bstep (se 2 (by rfl) ⟨1273263, by rfl⟩ : syracuseStep 3395369 = 2546527) B2546527
theorem B9054317 : Blo 2119435 9054317 := bstep (se 3 (by rfl) ⟨1697684, by rfl⟩ : syracuseStep 9054317 = 3395369) B3395369
theorem B6036211 : Blo 2119435 6036211 := bstep (se 1 (by rfl) ⟨4527158, by rfl⟩ : syracuseStep 6036211 = 9054317) B9054317
theorem B8048281 : Blo 2119435 8048281 := bstep (se 2 (by rfl) ⟨3018105, by rfl⟩ : syracuseStep 8048281 = 6036211) B6036211
theorem B10731041 : Blo 2119435 10731041 := bstep (se 2 (by rfl) ⟨4024140, by rfl⟩ : syracuseStep 10731041 = 8048281) B8048281
theorem B7154027 : Blo 2119435 7154027 := bstep (se 1 (by rfl) ⟨5365520, by rfl⟩ : syracuseStep 7154027 = 10731041) B10731041
theorem B4769351 : Blo 2119435 4769351 := bstep (se 1 (by rfl) ⟨3577013, by rfl⟩ : syracuseStep 4769351 = 7154027) B7154027
theorem B3179567 : Blo 2119435 3179567 := bstep (se 1 (by rfl) ⟨2384675, by rfl⟩ : syracuseStep 3179567 = 4769351) B4769351
theorem B2119711 : Blo 2119435 2119711 := bstep (se 1 (by rfl) ⟨1589783, by rfl⟩ : syracuseStep 2119711 = 3179567) B3179567
theorem B3179573 : Blo 2119435 3179573 := bbase (se 5 (by rfl) ⟨149042, by rfl⟩ : syracuseStep 3179573 = 298085) (by norm_num)
theorem B2119715 : Blo 2119435 2119715 := bstep (se 1 (by rfl) ⟨1589786, by rfl⟩ : syracuseStep 2119715 = 3179573) B3179573
theorem B5365541 : Blo 2119435 5365541 := bbase (se 4 (by rfl) ⟨503019, by rfl⟩ : syracuseStep 5365541 = 1006039) (by norm_num)
theorem B3577027 : Blo 2119435 3577027 := bstep (se 1 (by rfl) ⟨2682770, by rfl⟩ : syracuseStep 3577027 = 5365541) B5365541
theorem B4769369 : Blo 2119435 4769369 := bstep (se 2 (by rfl) ⟨1788513, by rfl⟩ : syracuseStep 4769369 = 3577027) B3577027
theorem B3179579 : Blo 2119435 3179579 := bstep (se 1 (by rfl) ⟨2384684, by rfl⟩ : syracuseStep 3179579 = 4769369) B4769369
theorem B2119719 : Blo 2119435 2119719 := bstep (se 1 (by rfl) ⟨1589789, by rfl⟩ : syracuseStep 2119719 = 3179579) B3179579
theorem B2384689 : Blo 2119435 2384689 := bbase (se 2 (by rfl) ⟨894258, by rfl⟩ : syracuseStep 2384689 = 1788517) (by norm_num)
theorem B3179585 : Blo 2119435 3179585 := bstep (se 2 (by rfl) ⟨1192344, by rfl⟩ : syracuseStep 3179585 = 2384689) B2384689
theorem B2119723 : Blo 2119435 2119723 := bstep (se 1 (by rfl) ⟨1589792, by rfl⟩ : syracuseStep 2119723 = 3179585) B3179585
theorem B5093093 : Blo 2119435 5093093 := bbase (se 4 (by rfl) ⟨477477, by rfl⟩ : syracuseStep 5093093 = 954955) (by norm_num)
theorem B3395395 : Blo 2119435 3395395 := bstep (se 1 (by rfl) ⟨2546546, by rfl⟩ : syracuseStep 3395395 = 5093093) B5093093
theorem B4527193 : Blo 2119435 4527193 := bstep (se 2 (by rfl) ⟨1697697, by rfl⟩ : syracuseStep 4527193 = 3395395) B3395395
theorem B6036257 : Blo 2119435 6036257 := bstep (se 2 (by rfl) ⟨2263596, by rfl⟩ : syracuseStep 6036257 = 4527193) B4527193
theorem B4024171 : Blo 2119435 4024171 := bstep (se 1 (by rfl) ⟨3018128, by rfl⟩ : syracuseStep 4024171 = 6036257) B6036257
theorem B5365561 : Blo 2119435 5365561 := bstep (se 2 (by rfl) ⟨2012085, by rfl⟩ : syracuseStep 5365561 = 4024171) B4024171
theorem B7154081 : Blo 2119435 7154081 := bstep (se 2 (by rfl) ⟨2682780, by rfl⟩ : syracuseStep 7154081 = 5365561) B5365561
theorem B4769387 : Blo 2119435 4769387 := bstep (se 1 (by rfl) ⟨3577040, by rfl⟩ : syracuseStep 4769387 = 7154081) B7154081
theorem B3179591 : Blo 2119435 3179591 := bstep (se 1 (by rfl) ⟨2384693, by rfl⟩ : syracuseStep 3179591 = 4769387) B4769387
theorem B2119727 : Blo 2119435 2119727 := bstep (se 1 (by rfl) ⟨1589795, by rfl⟩ : syracuseStep 2119727 = 3179591) B3179591
theorem B3179597 : Blo 2119435 3179597 := bbase (se 3 (by rfl) ⟨596174, by rfl⟩ : syracuseStep 3179597 = 1192349) (by norm_num)
theorem B2119731 : Blo 2119435 2119731 := bstep (se 1 (by rfl) ⟨1589798, by rfl⟩ : syracuseStep 2119731 = 3179597) B3179597
theorem B4769405 : Blo 2119435 4769405 := bbase (se 3 (by rfl) ⟨894263, by rfl⟩ : syracuseStep 4769405 = 1788527) (by norm_num)
theorem B3179603 : Blo 2119435 3179603 := bstep (se 1 (by rfl) ⟨2384702, by rfl⟩ : syracuseStep 3179603 = 4769405) B4769405
theorem B2119735 : Blo 2119435 2119735 := bstep (se 1 (by rfl) ⟨1589801, by rfl⟩ : syracuseStep 2119735 = 3179603) B3179603
theorem B3577061 : Blo 2119435 3577061 := bbase (se 4 (by rfl) ⟨335349, by rfl⟩ : syracuseStep 3577061 = 670699) (by norm_num)
theorem B2384707 : Blo 2119435 2384707 := bstep (se 1 (by rfl) ⟨1788530, by rfl⟩ : syracuseStep 2384707 = 3577061) B3577061
theorem B3179609 : Blo 2119435 3179609 := bstep (se 2 (by rfl) ⟨1192353, by rfl⟩ : syracuseStep 3179609 = 2384707) B2384707
theorem B2119739 : Blo 2119435 2119739 := bstep (se 1 (by rfl) ⟨1589804, by rfl⟩ : syracuseStep 2119739 = 3179609) B3179609
theorem B2148665 : Blo 2119435 2148665 := bbase (se 2 (by rfl) ⟨805749, by rfl⟩ : syracuseStep 2148665 = 1611499) (by norm_num)
theorem B5729773 : Blo 2119435 5729773 := bstep (se 3 (by rfl) ⟨1074332, by rfl⟩ : syracuseStep 5729773 = 2148665) B2148665
theorem B7639697 : Blo 2119435 7639697 := bstep (se 2 (by rfl) ⟨2864886, by rfl⟩ : syracuseStep 7639697 = 5729773) B5729773
theorem B5093131 : Blo 2119435 5093131 := bstep (se 1 (by rfl) ⟨3819848, by rfl⟩ : syracuseStep 5093131 = 7639697) B7639697
theorem B6790841 : Blo 2119435 6790841 := bstep (se 2 (by rfl) ⟨2546565, by rfl⟩ : syracuseStep 6790841 = 5093131) B5093131
theorem B4527227 : Blo 2119435 4527227 := bstep (se 1 (by rfl) ⟨3395420, by rfl⟩ : syracuseStep 4527227 = 6790841) B6790841
theorem B3018151 : Blo 2119435 3018151 := bstep (se 1 (by rfl) ⟨2263613, by rfl⟩ : syracuseStep 3018151 = 4527227) B4527227
theorem B16096805 : Blo 2119435 16096805 := bstep (se 4 (by rfl) ⟨1509075, by rfl⟩ : syracuseStep 16096805 = 3018151) B3018151
theorem B10731203 : Blo 2119435 10731203 := bstep (se 1 (by rfl) ⟨8048402, by rfl⟩ : syracuseStep 10731203 = 16096805) B16096805
theorem B7154135 : Blo 2119435 7154135 := bstep (se 1 (by rfl) ⟨5365601, by rfl⟩ : syracuseStep 7154135 = 10731203) B10731203
theorem B4769423 : Blo 2119435 4769423 := bstep (se 1 (by rfl) ⟨3577067, by rfl⟩ : syracuseStep 4769423 = 7154135) B7154135
theorem B3179615 : Blo 2119435 3179615 := bstep (se 1 (by rfl) ⟨2384711, by rfl⟩ : syracuseStep 3179615 = 4769423) B4769423
theorem B2119743 : Blo 2119435 2119743 := bstep (se 1 (by rfl) ⟨1589807, by rfl⟩ : syracuseStep 2119743 = 3179615) B3179615
theorem B3179621 : Blo 2119435 3179621 := bbase (se 4 (by rfl) ⟨298089, by rfl⟩ : syracuseStep 3179621 = 596179) (by norm_num)
theorem B2119747 : Blo 2119435 2119747 := bstep (se 1 (by rfl) ⟨1589810, by rfl⟩ : syracuseStep 2119747 = 3179621) B3179621
theorem B4527245 : Blo 2119435 4527245 := bbase (se 3 (by rfl) ⟨848858, by rfl⟩ : syracuseStep 4527245 = 1697717) (by norm_num)
theorem B3018163 : Blo 2119435 3018163 := bstep (se 1 (by rfl) ⟨2263622, by rfl⟩ : syracuseStep 3018163 = 4527245) B4527245
theorem B4024217 : Blo 2119435 4024217 := bstep (se 2 (by rfl) ⟨1509081, by rfl⟩ : syracuseStep 4024217 = 3018163) B3018163
theorem B2682811 : Blo 2119435 2682811 := bstep (se 1 (by rfl) ⟨2012108, by rfl⟩ : syracuseStep 2682811 = 4024217) B4024217
theorem B3577081 : Blo 2119435 3577081 := bstep (se 2 (by rfl) ⟨1341405, by rfl⟩ : syracuseStep 3577081 = 2682811) B2682811
theorem B4769441 : Blo 2119435 4769441 := bstep (se 2 (by rfl) ⟨1788540, by rfl⟩ : syracuseStep 4769441 = 3577081) B3577081
theorem B3179627 : Blo 2119435 3179627 := bstep (se 1 (by rfl) ⟨2384720, by rfl⟩ : syracuseStep 3179627 = 4769441) B4769441
theorem B2119751 : Blo 2119435 2119751 := bstep (se 1 (by rfl) ⟨1589813, by rfl⟩ : syracuseStep 2119751 = 3179627) B3179627
theorem B2384725 : Blo 2119435 2384725 := bbase (se 9 (by rfl) ⟨6986, by rfl⟩ : syracuseStep 2384725 = 13973) (by norm_num)
theorem B3179633 : Blo 2119435 3179633 := bstep (se 2 (by rfl) ⟨1192362, by rfl⟩ : syracuseStep 3179633 = 2384725) B2384725
theorem B2119755 : Blo 2119435 2119755 := bstep (se 1 (by rfl) ⟨1589816, by rfl⟩ : syracuseStep 2119755 = 3179633) B3179633
theorem B2682821 : Blo 2119435 2682821 := bbase (se 4 (by rfl) ⟨251514, by rfl⟩ : syracuseStep 2682821 = 503029) (by norm_num)
theorem B7154189 : Blo 2119435 7154189 := bstep (se 3 (by rfl) ⟨1341410, by rfl⟩ : syracuseStep 7154189 = 2682821) B2682821
theorem B4769459 : Blo 2119435 4769459 := bstep (se 1 (by rfl) ⟨3577094, by rfl⟩ : syracuseStep 4769459 = 7154189) B7154189
theorem B3179639 : Blo 2119435 3179639 := bstep (se 1 (by rfl) ⟨2384729, by rfl⟩ : syracuseStep 3179639 = 4769459) B4769459
theorem B2119759 : Blo 2119435 2119759 := bstep (se 1 (by rfl) ⟨1589819, by rfl⟩ : syracuseStep 2119759 = 3179639) B3179639
theorem B3179645 : Blo 2119435 3179645 := bbase (se 3 (by rfl) ⟨596183, by rfl⟩ : syracuseStep 3179645 = 1192367) (by norm_num)
theorem B2119763 : Blo 2119435 2119763 := bstep (se 1 (by rfl) ⟨1589822, by rfl⟩ : syracuseStep 2119763 = 3179645) B3179645
theorem B4769477 : Blo 2119435 4769477 := bbase (se 4 (by rfl) ⟨447138, by rfl⟩ : syracuseStep 4769477 = 894277) (by norm_num)
theorem B3179651 : Blo 2119435 3179651 := bstep (se 1 (by rfl) ⟨2384738, by rfl⟩ : syracuseStep 3179651 = 4769477) B4769477
theorem B2119767 : Blo 2119435 2119767 := bstep (se 1 (by rfl) ⟨1589825, by rfl⟩ : syracuseStep 2119767 = 3179651) B3179651
theorem B34379093 : Blo 2119435 34379093 := bbase (se 14 (by rfl) ⟨3147, by rfl⟩ : syracuseStep 34379093 = 6295) (by norm_num)
theorem B22919395 : Blo 2119435 22919395 := bstep (se 1 (by rfl) ⟨17189546, by rfl⟩ : syracuseStep 22919395 = 34379093) B34379093
theorem B30559193 : Blo 2119435 30559193 := bstep (se 2 (by rfl) ⟨11459697, by rfl⟩ : syracuseStep 30559193 = 22919395) B22919395
theorem B20372795 : Blo 2119435 20372795 := bstep (se 1 (by rfl) ⟨15279596, by rfl⟩ : syracuseStep 20372795 = 30559193) B30559193
theorem B13581863 : Blo 2119435 13581863 := bstep (se 1 (by rfl) ⟨10186397, by rfl⟩ : syracuseStep 13581863 = 20372795) B20372795
theorem B9054575 : Blo 2119435 9054575 := bstep (se 1 (by rfl) ⟨6790931, by rfl⟩ : syracuseStep 9054575 = 13581863) B13581863
theorem B6036383 : Blo 2119435 6036383 := bstep (se 1 (by rfl) ⟨4527287, by rfl⟩ : syracuseStep 6036383 = 9054575) B9054575
theorem B4024255 : Blo 2119435 4024255 := bstep (se 1 (by rfl) ⟨3018191, by rfl⟩ : syracuseStep 4024255 = 6036383) B6036383
theorem B5365673 : Blo 2119435 5365673 := bstep (se 2 (by rfl) ⟨2012127, by rfl⟩ : syracuseStep 5365673 = 4024255) B4024255
theorem B3577115 : Blo 2119435 3577115 := bstep (se 1 (by rfl) ⟨2682836, by rfl⟩ : syracuseStep 3577115 = 5365673) B5365673
theorem B2384743 : Blo 2119435 2384743 := bstep (se 1 (by rfl) ⟨1788557, by rfl⟩ : syracuseStep 2384743 = 3577115) B3577115
theorem B3179657 : Blo 2119435 3179657 := bstep (se 2 (by rfl) ⟨1192371, by rfl⟩ : syracuseStep 3179657 = 2384743) B2384743
theorem B2119771 : Blo 2119435 2119771 := bstep (se 1 (by rfl) ⟨1589828, by rfl⟩ : syracuseStep 2119771 = 3179657) B3179657
theorem B10731365 : Blo 2119435 10731365 := bbase (se 4 (by rfl) ⟨1006065, by rfl⟩ : syracuseStep 10731365 = 2012131) (by norm_num)
theorem B7154243 : Blo 2119435 7154243 := bstep (se 1 (by rfl) ⟨5365682, by rfl⟩ : syracuseStep 7154243 = 10731365) B10731365
theorem B4769495 : Blo 2119435 4769495 := bstep (se 1 (by rfl) ⟨3577121, by rfl⟩ : syracuseStep 4769495 = 7154243) B7154243
theorem B3179663 : Blo 2119435 3179663 := bstep (se 1 (by rfl) ⟨2384747, by rfl⟩ : syracuseStep 3179663 = 4769495) B4769495
theorem B2119775 : Blo 2119435 2119775 := bstep (se 1 (by rfl) ⟨1589831, by rfl⟩ : syracuseStep 2119775 = 3179663) B3179663
theorem B3179669 : Blo 2119435 3179669 := bbase (se 6 (by rfl) ⟨74523, by rfl⟩ : syracuseStep 3179669 = 149047) (by norm_num)
theorem B2119779 : Blo 2119435 2119779 := bstep (se 1 (by rfl) ⟨1589834, by rfl⟩ : syracuseStep 2119779 = 3179669) B3179669
theorem B6446117 : Blo 2119435 6446117 := bbase (se 4 (by rfl) ⟨604323, by rfl⟩ : syracuseStep 6446117 = 1208647) (by norm_num)
theorem B4297411 : Blo 2119435 4297411 := bstep (se 1 (by rfl) ⟨3223058, by rfl⟩ : syracuseStep 4297411 = 6446117) B6446117
theorem B5729881 : Blo 2119435 5729881 := bstep (se 2 (by rfl) ⟨2148705, by rfl⟩ : syracuseStep 5729881 = 4297411) B4297411
theorem B7639841 : Blo 2119435 7639841 := bstep (se 2 (by rfl) ⟨2864940, by rfl⟩ : syracuseStep 7639841 = 5729881) B5729881
theorem B5093227 : Blo 2119435 5093227 := bstep (se 1 (by rfl) ⟨3819920, by rfl⟩ : syracuseStep 5093227 = 7639841) B7639841
theorem B6790969 : Blo 2119435 6790969 := bstep (se 2 (by rfl) ⟨2546613, by rfl⟩ : syracuseStep 6790969 = 5093227) B5093227
theorem B9054625 : Blo 2119435 9054625 := bstep (se 2 (by rfl) ⟨3395484, by rfl⟩ : syracuseStep 9054625 = 6790969) B6790969
theorem B12072833 : Blo 2119435 12072833 := bstep (se 2 (by rfl) ⟨4527312, by rfl⟩ : syracuseStep 12072833 = 9054625) B9054625
theorem B8048555 : Blo 2119435 8048555 := bstep (se 1 (by rfl) ⟨6036416, by rfl⟩ : syracuseStep 8048555 = 12072833) B12072833
theorem B5365703 : Blo 2119435 5365703 := bstep (se 1 (by rfl) ⟨4024277, by rfl⟩ : syracuseStep 5365703 = 8048555) B8048555
theorem B3577135 : Blo 2119435 3577135 := bstep (se 1 (by rfl) ⟨2682851, by rfl⟩ : syracuseStep 3577135 = 5365703) B5365703
theorem B4769513 : Blo 2119435 4769513 := bstep (se 2 (by rfl) ⟨1788567, by rfl⟩ : syracuseStep 4769513 = 3577135) B3577135
theorem B3179675 : Blo 2119435 3179675 := bstep (se 1 (by rfl) ⟨2384756, by rfl⟩ : syracuseStep 3179675 = 4769513) B4769513
theorem B2119783 : Blo 2119435 2119783 := bstep (se 1 (by rfl) ⟨1589837, by rfl⟩ : syracuseStep 2119783 = 3179675) B3179675
theorem B2384761 : Blo 2119435 2384761 := bbase (se 2 (by rfl) ⟨894285, by rfl⟩ : syracuseStep 2384761 = 1788571) (by norm_num)
theorem B3179681 : Blo 2119435 3179681 := bstep (se 2 (by rfl) ⟨1192380, by rfl⟩ : syracuseStep 3179681 = 2384761) B2384761
theorem B2119787 : Blo 2119435 2119787 := bstep (se 1 (by rfl) ⟨1589840, by rfl⟩ : syracuseStep 2119787 = 3179681) B3179681
theorem B3872053 : Blo 2119435 3872053 := bbase (se 5 (by rfl) ⟨181502, by rfl⟩ : syracuseStep 3872053 = 363005) (by norm_num)
theorem B20650949 : Blo 2119435 20650949 := bstep (se 4 (by rfl) ⟨1936026, by rfl⟩ : syracuseStep 20650949 = 3872053) B3872053
theorem B13767299 : Blo 2119435 13767299 := bstep (se 1 (by rfl) ⟨10325474, by rfl⟩ : syracuseStep 13767299 = 20650949) B20650949
theorem B9178199 : Blo 2119435 9178199 := bstep (se 1 (by rfl) ⟨6883649, by rfl⟩ : syracuseStep 9178199 = 13767299) B13767299
theorem B6118799 : Blo 2119435 6118799 := bstep (se 1 (by rfl) ⟨4589099, by rfl⟩ : syracuseStep 6118799 = 9178199) B9178199
theorem B16316797 : Blo 2119435 16316797 := bstep (se 3 (by rfl) ⟨3059399, by rfl⟩ : syracuseStep 16316797 = 6118799) B6118799
theorem B21755729 : Blo 2119435 21755729 := bstep (se 2 (by rfl) ⟨8158398, by rfl⟩ : syracuseStep 21755729 = 16316797) B16316797
theorem B14503819 : Blo 2119435 14503819 := bstep (se 1 (by rfl) ⟨10877864, by rfl⟩ : syracuseStep 14503819 = 21755729) B21755729
theorem B19338425 : Blo 2119435 19338425 := bstep (se 2 (by rfl) ⟨7251909, by rfl⟩ : syracuseStep 19338425 = 14503819) B14503819
theorem B12892283 : Blo 2119435 12892283 := bstep (se 1 (by rfl) ⟨9669212, by rfl⟩ : syracuseStep 12892283 = 19338425) B19338425
theorem B8594855 : Blo 2119435 8594855 := bstep (se 1 (by rfl) ⟨6446141, by rfl⟩ : syracuseStep 8594855 = 12892283) B12892283
theorem B5729903 : Blo 2119435 5729903 := bstep (se 1 (by rfl) ⟨4297427, by rfl⟩ : syracuseStep 5729903 = 8594855) B8594855
theorem B3819935 : Blo 2119435 3819935 := bstep (se 1 (by rfl) ⟨2864951, by rfl⟩ : syracuseStep 3819935 = 5729903) B5729903
theorem B2546623 : Blo 2119435 2546623 := bstep (se 1 (by rfl) ⟨1909967, by rfl⟩ : syracuseStep 2546623 = 3819935) B3819935
theorem B13581989 : Blo 2119435 13581989 := bstep (se 4 (by rfl) ⟨1273311, by rfl⟩ : syracuseStep 13581989 = 2546623) B2546623
theorem B9054659 : Blo 2119435 9054659 := bstep (se 1 (by rfl) ⟨6790994, by rfl⟩ : syracuseStep 9054659 = 13581989) B13581989
theorem B6036439 : Blo 2119435 6036439 := bstep (se 1 (by rfl) ⟨4527329, by rfl⟩ : syracuseStep 6036439 = 9054659) B9054659
theorem B8048585 : Blo 2119435 8048585 := bstep (se 2 (by rfl) ⟨3018219, by rfl⟩ : syracuseStep 8048585 = 6036439) B6036439
theorem B5365723 : Blo 2119435 5365723 := bstep (se 1 (by rfl) ⟨4024292, by rfl⟩ : syracuseStep 5365723 = 8048585) B8048585
theorem B7154297 : Blo 2119435 7154297 := bstep (se 2 (by rfl) ⟨2682861, by rfl⟩ : syracuseStep 7154297 = 5365723) B5365723
theorem B4769531 : Blo 2119435 4769531 := bstep (se 1 (by rfl) ⟨3577148, by rfl⟩ : syracuseStep 4769531 = 7154297) B7154297
theorem B3179687 : Blo 2119435 3179687 := bstep (se 1 (by rfl) ⟨2384765, by rfl⟩ : syracuseStep 3179687 = 4769531) B4769531
theorem B2119791 : Blo 2119435 2119791 := bstep (se 1 (by rfl) ⟨1589843, by rfl⟩ : syracuseStep 2119791 = 3179687) B3179687
theorem B3179693 : Blo 2119435 3179693 := bbase (se 3 (by rfl) ⟨596192, by rfl⟩ : syracuseStep 3179693 = 1192385) (by norm_num)
theorem B2119795 : Blo 2119435 2119795 := bstep (se 1 (by rfl) ⟨1589846, by rfl⟩ : syracuseStep 2119795 = 3179693) B3179693
theorem B4769549 : Blo 2119435 4769549 := bbase (se 3 (by rfl) ⟨894290, by rfl⟩ : syracuseStep 4769549 = 1788581) (by norm_num)
theorem B3179699 : Blo 2119435 3179699 := bstep (se 1 (by rfl) ⟨2384774, by rfl⟩ : syracuseStep 3179699 = 4769549) B4769549
theorem B2119799 : Blo 2119435 2119799 := bstep (se 1 (by rfl) ⟨1589849, by rfl⟩ : syracuseStep 2119799 = 3179699) B3179699
theorem B2682877 : Blo 2119435 2682877 := bbase (se 3 (by rfl) ⟨503039, by rfl⟩ : syracuseStep 2682877 = 1006079) (by norm_num)
theorem B3577169 : Blo 2119435 3577169 := bstep (se 2 (by rfl) ⟨1341438, by rfl⟩ : syracuseStep 3577169 = 2682877) B2682877
theorem B2384779 : Blo 2119435 2384779 := bstep (se 1 (by rfl) ⟨1788584, by rfl⟩ : syracuseStep 2384779 = 3577169) B3577169
theorem B3179705 : Blo 2119435 3179705 := bstep (se 2 (by rfl) ⟨1192389, by rfl⟩ : syracuseStep 3179705 = 2384779) B2384779
theorem B2119803 : Blo 2119435 2119803 := bstep (se 1 (by rfl) ⟨1589852, by rfl⟩ : syracuseStep 2119803 = 3179705) B3179705
theorem B6791045 : Blo 2119435 6791045 := bbase (se 4 (by rfl) ⟨636660, by rfl⟩ : syracuseStep 6791045 = 1273321) (by norm_num)
theorem B18109453 : Blo 2119435 18109453 := bstep (se 3 (by rfl) ⟨3395522, by rfl⟩ : syracuseStep 18109453 = 6791045) B6791045
theorem B24145937 : Blo 2119435 24145937 := bstep (se 2 (by rfl) ⟨9054726, by rfl⟩ : syracuseStep 24145937 = 18109453) B18109453
theorem B16097291 : Blo 2119435 16097291 := bstep (se 1 (by rfl) ⟨12072968, by rfl⟩ : syracuseStep 16097291 = 24145937) B24145937
theorem B10731527 : Blo 2119435 10731527 := bstep (se 1 (by rfl) ⟨8048645, by rfl⟩ : syracuseStep 10731527 = 16097291) B16097291
theorem B7154351 : Blo 2119435 7154351 := bstep (se 1 (by rfl) ⟨5365763, by rfl⟩ : syracuseStep 7154351 = 10731527) B10731527
theorem B4769567 : Blo 2119435 4769567 := bstep (se 1 (by rfl) ⟨3577175, by rfl⟩ : syracuseStep 4769567 = 7154351) B7154351
theorem B3179711 : Blo 2119435 3179711 := bstep (se 1 (by rfl) ⟨2384783, by rfl⟩ : syracuseStep 3179711 = 4769567) B4769567
theorem B2119807 : Blo 2119435 2119807 := bstep (se 1 (by rfl) ⟨1589855, by rfl⟩ : syracuseStep 2119807 = 3179711) B3179711
theorem B3179717 : Blo 2119435 3179717 := bbase (se 4 (by rfl) ⟨298098, by rfl⟩ : syracuseStep 3179717 = 596197) (by norm_num)
theorem B2119811 : Blo 2119435 2119811 := bstep (se 1 (by rfl) ⟨1589858, by rfl⟩ : syracuseStep 2119811 = 3179717) B3179717
theorem B3577189 : Blo 2119435 3577189 := bbase (se 4 (by rfl) ⟨335361, by rfl⟩ : syracuseStep 3577189 = 670723) (by norm_num)
theorem B4769585 : Blo 2119435 4769585 := bstep (se 2 (by rfl) ⟨1788594, by rfl⟩ : syracuseStep 4769585 = 3577189) B3577189
theorem B3179723 : Blo 2119435 3179723 := bstep (se 1 (by rfl) ⟨2384792, by rfl⟩ : syracuseStep 3179723 = 4769585) B4769585
theorem B2119815 : Blo 2119435 2119815 := bstep (se 1 (by rfl) ⟨1589861, by rfl⟩ : syracuseStep 2119815 = 3179723) B3179723
theorem B2384797 : Blo 2119435 2384797 := bbase (se 3 (by rfl) ⟨447149, by rfl⟩ : syracuseStep 2384797 = 894299) (by norm_num)
theorem B3179729 : Blo 2119435 3179729 := bstep (se 2 (by rfl) ⟨1192398, by rfl⟩ : syracuseStep 3179729 = 2384797) B2384797
theorem B2119819 : Blo 2119435 2119819 := bstep (se 1 (by rfl) ⟨1589864, by rfl⟩ : syracuseStep 2119819 = 3179729) B3179729
theorem B7154405 : Blo 2119435 7154405 := bbase (se 4 (by rfl) ⟨670725, by rfl⟩ : syracuseStep 7154405 = 1341451) (by norm_num)
theorem B4769603 : Blo 2119435 4769603 := bstep (se 1 (by rfl) ⟨3577202, by rfl⟩ : syracuseStep 4769603 = 7154405) B7154405
theorem B3179735 : Blo 2119435 3179735 := bstep (se 1 (by rfl) ⟨2384801, by rfl⟩ : syracuseStep 3179735 = 4769603) B4769603
theorem B2119823 : Blo 2119435 2119823 := bstep (se 1 (by rfl) ⟨1589867, by rfl⟩ : syracuseStep 2119823 = 3179735) B3179735
theorem B3179741 : Blo 2119435 3179741 := bbase (se 3 (by rfl) ⟨596201, by rfl⟩ : syracuseStep 3179741 = 1192403) (by norm_num)
theorem B2119827 : Blo 2119435 2119827 := bstep (se 1 (by rfl) ⟨1589870, by rfl⟩ : syracuseStep 2119827 = 3179741) B3179741
theorem B4769621 : Blo 2119435 4769621 := bbase (se 9 (by rfl) ⟨13973, by rfl⟩ : syracuseStep 4769621 = 27947) (by norm_num)
theorem B3179747 : Blo 2119435 3179747 := bstep (se 1 (by rfl) ⟨2384810, by rfl⟩ : syracuseStep 3179747 = 4769621) B4769621
theorem B2119831 : Blo 2119435 2119831 := bstep (se 1 (by rfl) ⟨1589873, by rfl⟩ : syracuseStep 2119831 = 3179747) B3179747
theorem B6036565 : Blo 2119435 6036565 := bbase (se 8 (by rfl) ⟨35370, by rfl⟩ : syracuseStep 6036565 = 70741) (by norm_num)
theorem B8048753 : Blo 2119435 8048753 := bstep (se 2 (by rfl) ⟨3018282, by rfl⟩ : syracuseStep 8048753 = 6036565) B6036565
theorem B5365835 : Blo 2119435 5365835 := bstep (se 1 (by rfl) ⟨4024376, by rfl⟩ : syracuseStep 5365835 = 8048753) B8048753
theorem B3577223 : Blo 2119435 3577223 := bstep (se 1 (by rfl) ⟨2682917, by rfl⟩ : syracuseStep 3577223 = 5365835) B5365835
theorem B2384815 : Blo 2119435 2384815 := bstep (se 1 (by rfl) ⟨1788611, by rfl⟩ : syracuseStep 2384815 = 3577223) B3577223
theorem B3179753 : Blo 2119435 3179753 := bstep (se 2 (by rfl) ⟨1192407, by rfl⟩ : syracuseStep 3179753 = 2384815) B2384815
theorem B2119835 : Blo 2119435 2119835 := bstep (se 1 (by rfl) ⟨1589876, by rfl⟩ : syracuseStep 2119835 = 3179753) B3179753
theorem B2417357 : Blo 2119435 2417357 := bbase (se 3 (by rfl) ⟨453254, by rfl⟩ : syracuseStep 2417357 = 906509) (by norm_num)
theorem B6446285 : Blo 2119435 6446285 := bstep (se 3 (by rfl) ⟨1208678, by rfl⟩ : syracuseStep 6446285 = 2417357) B2417357
theorem B68760373 : Blo 2119435 68760373 := bstep (se 5 (by rfl) ⟨3223142, by rfl⟩ : syracuseStep 68760373 = 6446285) B6446285
theorem B91680497 : Blo 2119435 91680497 := bstep (se 2 (by rfl) ⟨34380186, by rfl⟩ : syracuseStep 91680497 = 68760373) B68760373
theorem B61120331 : Blo 2119435 61120331 := bstep (se 1 (by rfl) ⟨45840248, by rfl⟩ : syracuseStep 61120331 = 91680497) B91680497
theorem B40746887 : Blo 2119435 40746887 := bstep (se 1 (by rfl) ⟨30560165, by rfl⟩ : syracuseStep 40746887 = 61120331) B61120331
theorem B27164591 : Blo 2119435 27164591 := bstep (se 1 (by rfl) ⟨20373443, by rfl⟩ : syracuseStep 27164591 = 40746887) B40746887
theorem B18109727 : Blo 2119435 18109727 := bstep (se 1 (by rfl) ⟨13582295, by rfl⟩ : syracuseStep 18109727 = 27164591) B27164591
theorem B12073151 : Blo 2119435 12073151 := bstep (se 1 (by rfl) ⟨9054863, by rfl⟩ : syracuseStep 12073151 = 18109727) B18109727
theorem B8048767 : Blo 2119435 8048767 := bstep (se 1 (by rfl) ⟨6036575, by rfl⟩ : syracuseStep 8048767 = 12073151) B12073151
theorem B10731689 : Blo 2119435 10731689 := bstep (se 2 (by rfl) ⟨4024383, by rfl⟩ : syracuseStep 10731689 = 8048767) B8048767
theorem B7154459 : Blo 2119435 7154459 := bstep (se 1 (by rfl) ⟨5365844, by rfl⟩ : syracuseStep 7154459 = 10731689) B10731689
theorem B4769639 : Blo 2119435 4769639 := bstep (se 1 (by rfl) ⟨3577229, by rfl⟩ : syracuseStep 4769639 = 7154459) B7154459
theorem B3179759 : Blo 2119435 3179759 := bstep (se 1 (by rfl) ⟨2384819, by rfl⟩ : syracuseStep 3179759 = 4769639) B4769639
theorem B2119839 : Blo 2119435 2119839 := bstep (se 1 (by rfl) ⟨1589879, by rfl⟩ : syracuseStep 2119839 = 3179759) B3179759
theorem B3179765 : Blo 2119435 3179765 := bbase (se 5 (by rfl) ⟨149051, by rfl⟩ : syracuseStep 3179765 = 298103) (by norm_num)
theorem B2119843 : Blo 2119435 2119843 := bstep (se 1 (by rfl) ⟨1589882, by rfl⟩ : syracuseStep 2119843 = 3179765) B3179765
theorem B5093381 : Blo 2119435 5093381 := bbase (se 4 (by rfl) ⟨477504, by rfl⟩ : syracuseStep 5093381 = 955009) (by norm_num)
theorem B13582349 : Blo 2119435 13582349 := bstep (se 3 (by rfl) ⟨2546690, by rfl⟩ : syracuseStep 13582349 = 5093381) B5093381
theorem B9054899 : Blo 2119435 9054899 := bstep (se 1 (by rfl) ⟨6791174, by rfl⟩ : syracuseStep 9054899 = 13582349) B13582349
theorem B6036599 : Blo 2119435 6036599 := bstep (se 1 (by rfl) ⟨4527449, by rfl⟩ : syracuseStep 6036599 = 9054899) B9054899
theorem B4024399 : Blo 2119435 4024399 := bstep (se 1 (by rfl) ⟨3018299, by rfl⟩ : syracuseStep 4024399 = 6036599) B6036599
theorem B5365865 : Blo 2119435 5365865 := bstep (se 2 (by rfl) ⟨2012199, by rfl⟩ : syracuseStep 5365865 = 4024399) B4024399
theorem B3577243 : Blo 2119435 3577243 := bstep (se 1 (by rfl) ⟨2682932, by rfl⟩ : syracuseStep 3577243 = 5365865) B5365865
theorem B4769657 : Blo 2119435 4769657 := bstep (se 2 (by rfl) ⟨1788621, by rfl⟩ : syracuseStep 4769657 = 3577243) B3577243
theorem B3179771 : Blo 2119435 3179771 := bstep (se 1 (by rfl) ⟨2384828, by rfl⟩ : syracuseStep 3179771 = 4769657) B4769657
theorem B2119847 : Blo 2119435 2119847 := bstep (se 1 (by rfl) ⟨1589885, by rfl⟩ : syracuseStep 2119847 = 3179771) B3179771
theorem B2384833 : Blo 2119435 2384833 := bbase (se 2 (by rfl) ⟨894312, by rfl⟩ : syracuseStep 2384833 = 1788625) (by norm_num)
theorem B3179777 : Blo 2119435 3179777 := bstep (se 2 (by rfl) ⟨1192416, by rfl⟩ : syracuseStep 3179777 = 2384833) B2384833
theorem B2119851 : Blo 2119435 2119851 := bstep (se 1 (by rfl) ⟨1589888, by rfl⟩ : syracuseStep 2119851 = 3179777) B3179777
theorem B5365885 : Blo 2119435 5365885 := bbase (se 3 (by rfl) ⟨1006103, by rfl⟩ : syracuseStep 5365885 = 2012207) (by norm_num)
theorem B7154513 : Blo 2119435 7154513 := bstep (se 2 (by rfl) ⟨2682942, by rfl⟩ : syracuseStep 7154513 = 5365885) B5365885
theorem B4769675 : Blo 2119435 4769675 := bstep (se 1 (by rfl) ⟨3577256, by rfl⟩ : syracuseStep 4769675 = 7154513) B7154513
theorem B3179783 : Blo 2119435 3179783 := bstep (se 1 (by rfl) ⟨2384837, by rfl⟩ : syracuseStep 3179783 = 4769675) B4769675
theorem B2119855 : Blo 2119435 2119855 := bstep (se 1 (by rfl) ⟨1589891, by rfl⟩ : syracuseStep 2119855 = 3179783) B3179783
theorem B3179789 : Blo 2119435 3179789 := bbase (se 3 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 3179789 = 1192421) (by norm_num)
theorem B2119859 : Blo 2119435 2119859 := bstep (se 1 (by rfl) ⟨1589894, by rfl⟩ : syracuseStep 2119859 = 3179789) B3179789
theorem B4769693 : Blo 2119435 4769693 := bbase (se 3 (by rfl) ⟨894317, by rfl⟩ : syracuseStep 4769693 = 1788635) (by norm_num)
theorem B3179795 : Blo 2119435 3179795 := bstep (se 1 (by rfl) ⟨2384846, by rfl⟩ : syracuseStep 3179795 = 4769693) B4769693
theorem B2119863 : Blo 2119435 2119863 := bstep (se 1 (by rfl) ⟨1589897, by rfl⟩ : syracuseStep 2119863 = 3179795) B3179795
theorem B3577277 : Blo 2119435 3577277 := bbase (se 3 (by rfl) ⟨670739, by rfl⟩ : syracuseStep 3577277 = 1341479) (by norm_num)
theorem B2384851 : Blo 2119435 2384851 := bstep (se 1 (by rfl) ⟨1788638, by rfl⟩ : syracuseStep 2384851 = 3577277) B3577277
theorem B3179801 : Blo 2119435 3179801 := bstep (se 2 (by rfl) ⟨1192425, by rfl⟩ : syracuseStep 3179801 = 2384851) B2384851
theorem B2119867 : Blo 2119435 2119867 := bstep (se 1 (by rfl) ⟨1589900, by rfl⟩ : syracuseStep 2119867 = 3179801) B3179801
theorem B12073333 : Blo 2119435 12073333 := bbase (se 5 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 12073333 = 1131875) (by norm_num)
theorem B16097777 : Blo 2119435 16097777 := bstep (se 2 (by rfl) ⟨6036666, by rfl⟩ : syracuseStep 16097777 = 12073333) B12073333
theorem B10731851 : Blo 2119435 10731851 := bstep (se 1 (by rfl) ⟨8048888, by rfl⟩ : syracuseStep 10731851 = 16097777) B16097777
theorem B7154567 : Blo 2119435 7154567 := bstep (se 1 (by rfl) ⟨5365925, by rfl⟩ : syracuseStep 7154567 = 10731851) B10731851
theorem B4769711 : Blo 2119435 4769711 := bstep (se 1 (by rfl) ⟨3577283, by rfl⟩ : syracuseStep 4769711 = 7154567) B7154567
theorem B3179807 : Blo 2119435 3179807 := bstep (se 1 (by rfl) ⟨2384855, by rfl⟩ : syracuseStep 3179807 = 4769711) B4769711
theorem B2119871 : Blo 2119435 2119871 := bstep (se 1 (by rfl) ⟨1589903, by rfl⟩ : syracuseStep 2119871 = 3179807) B3179807
theorem B3179813 : Blo 2119435 3179813 := bbase (se 4 (by rfl) ⟨298107, by rfl⟩ : syracuseStep 3179813 = 596215) (by norm_num)
theorem B2119875 : Blo 2119435 2119875 := bstep (se 1 (by rfl) ⟨1589906, by rfl⟩ : syracuseStep 2119875 = 3179813) B3179813
theorem B2682973 : Blo 2119435 2682973 := bbase (se 3 (by rfl) ⟨503057, by rfl⟩ : syracuseStep 2682973 = 1006115) (by norm_num)
theorem B3577297 : Blo 2119435 3577297 := bstep (se 2 (by rfl) ⟨1341486, by rfl⟩ : syracuseStep 3577297 = 2682973) B2682973
theorem B4769729 : Blo 2119435 4769729 := bstep (se 2 (by rfl) ⟨1788648, by rfl⟩ : syracuseStep 4769729 = 3577297) B3577297
theorem B3179819 : Blo 2119435 3179819 := bstep (se 1 (by rfl) ⟨2384864, by rfl⟩ : syracuseStep 3179819 = 4769729) B4769729
theorem B2119879 : Blo 2119435 2119879 := bstep (se 1 (by rfl) ⟨1589909, by rfl⟩ : syracuseStep 2119879 = 3179819) B3179819
theorem B2384869 : Blo 2119435 2384869 := bbase (se 4 (by rfl) ⟨223581, by rfl⟩ : syracuseStep 2384869 = 447163) (by norm_num)
theorem B3179825 : Blo 2119435 3179825 := bstep (se 2 (by rfl) ⟨1192434, by rfl⟩ : syracuseStep 3179825 = 2384869) B2384869
theorem B2119883 : Blo 2119435 2119883 := bstep (se 1 (by rfl) ⟨1589912, by rfl⟩ : syracuseStep 2119883 = 3179825) B3179825
theorem B2417413 : Blo 2119435 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B3223217 : Blo 2119435 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B2148811 : Blo 2119435 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B11460325 : Blo 2119435 11460325 := bstep (se 4 (by rfl) ⟨1074405, by rfl⟩ : syracuseStep 11460325 = 2148811) B2148811
theorem B15280433 : Blo 2119435 15280433 := bstep (se 2 (by rfl) ⟨5730162, by rfl⟩ : syracuseStep 15280433 = 11460325) B11460325
theorem B10186955 : Blo 2119435 10186955 := bstep (se 1 (by rfl) ⟨7640216, by rfl⟩ : syracuseStep 10186955 = 15280433) B15280433
theorem B6791303 : Blo 2119435 6791303 := bstep (se 1 (by rfl) ⟨5093477, by rfl⟩ : syracuseStep 6791303 = 10186955) B10186955
theorem B4527535 : Blo 2119435 4527535 := bstep (se 1 (by rfl) ⟨3395651, by rfl⟩ : syracuseStep 4527535 = 6791303) B6791303
theorem B6036713 : Blo 2119435 6036713 := bstep (se 2 (by rfl) ⟨2263767, by rfl⟩ : syracuseStep 6036713 = 4527535) B4527535
theorem B4024475 : Blo 2119435 4024475 := bstep (se 1 (by rfl) ⟨3018356, by rfl⟩ : syracuseStep 4024475 = 6036713) B6036713
theorem B2682983 : Blo 2119435 2682983 := bstep (se 1 (by rfl) ⟨2012237, by rfl⟩ : syracuseStep 2682983 = 4024475) B4024475
theorem B7154621 : Blo 2119435 7154621 := bstep (se 3 (by rfl) ⟨1341491, by rfl⟩ : syracuseStep 7154621 = 2682983) B2682983
theorem B4769747 : Blo 2119435 4769747 := bstep (se 1 (by rfl) ⟨3577310, by rfl⟩ : syracuseStep 4769747 = 7154621) B7154621
theorem B3179831 : Blo 2119435 3179831 := bstep (se 1 (by rfl) ⟨2384873, by rfl⟩ : syracuseStep 3179831 = 4769747) B4769747
theorem B2119887 : Blo 2119435 2119887 := bstep (se 1 (by rfl) ⟨1589915, by rfl⟩ : syracuseStep 2119887 = 3179831) B3179831
theorem B3179837 : Blo 2119435 3179837 := bbase (se 3 (by rfl) ⟨596219, by rfl⟩ : syracuseStep 3179837 = 1192439) (by norm_num)
theorem B2119891 : Blo 2119435 2119891 := bstep (se 1 (by rfl) ⟨1589918, by rfl⟩ : syracuseStep 2119891 = 3179837) B3179837
theorem B4769765 : Blo 2119435 4769765 := bbase (se 4 (by rfl) ⟨447165, by rfl⟩ : syracuseStep 4769765 = 894331) (by norm_num)
theorem B3179843 : Blo 2119435 3179843 := bstep (se 1 (by rfl) ⟨2384882, by rfl⟩ : syracuseStep 3179843 = 4769765) B4769765
theorem B2119895 : Blo 2119435 2119895 := bstep (se 1 (by rfl) ⟨1589921, by rfl⟩ : syracuseStep 2119895 = 3179843) B3179843
theorem B5365997 : Blo 2119435 5365997 := bbase (se 3 (by rfl) ⟨1006124, by rfl⟩ : syracuseStep 5365997 = 2012249) (by norm_num)
theorem B3577331 : Blo 2119435 3577331 := bstep (se 1 (by rfl) ⟨2682998, by rfl⟩ : syracuseStep 3577331 = 5365997) B5365997
theorem B2384887 : Blo 2119435 2384887 := bstep (se 1 (by rfl) ⟨1788665, by rfl⟩ : syracuseStep 2384887 = 3577331) B3577331
theorem B3179849 : Blo 2119435 3179849 := bstep (se 2 (by rfl) ⟨1192443, by rfl⟩ : syracuseStep 3179849 = 2384887) B2384887
theorem B2119899 : Blo 2119435 2119899 := bstep (se 1 (by rfl) ⟨1589924, by rfl⟩ : syracuseStep 2119899 = 3179849) B3179849
theorem B3395677 : Blo 2119435 3395677 := bbase (se 3 (by rfl) ⟨636689, by rfl⟩ : syracuseStep 3395677 = 1273379) (by norm_num)
theorem B4527569 : Blo 2119435 4527569 := bstep (se 2 (by rfl) ⟨1697838, by rfl⟩ : syracuseStep 4527569 = 3395677) B3395677
theorem B3018379 : Blo 2119435 3018379 := bstep (se 1 (by rfl) ⟨2263784, by rfl⟩ : syracuseStep 3018379 = 4527569) B4527569
theorem B4024505 : Blo 2119435 4024505 := bstep (se 2 (by rfl) ⟨1509189, by rfl⟩ : syracuseStep 4024505 = 3018379) B3018379
theorem B10732013 : Blo 2119435 10732013 := bstep (se 3 (by rfl) ⟨2012252, by rfl⟩ : syracuseStep 10732013 = 4024505) B4024505
theorem B7154675 : Blo 2119435 7154675 := bstep (se 1 (by rfl) ⟨5366006, by rfl⟩ : syracuseStep 7154675 = 10732013) B10732013
theorem B4769783 : Blo 2119435 4769783 := bstep (se 1 (by rfl) ⟨3577337, by rfl⟩ : syracuseStep 4769783 = 7154675) B7154675
theorem B3179855 : Blo 2119435 3179855 := bstep (se 1 (by rfl) ⟨2384891, by rfl⟩ : syracuseStep 3179855 = 4769783) B4769783
theorem B2119903 : Blo 2119435 2119903 := bstep (se 1 (by rfl) ⟨1589927, by rfl⟩ : syracuseStep 2119903 = 3179855) B3179855
theorem B3179861 : Blo 2119435 3179861 := bbase (se 12 (by rfl) ⟨1164, by rfl⟩ : syracuseStep 3179861 = 2329) (by norm_num)
theorem B2119907 : Blo 2119435 2119907 := bstep (se 1 (by rfl) ⟨1589930, by rfl⟩ : syracuseStep 2119907 = 3179861) B3179861
theorem B2263793 : Blo 2119435 2263793 := bbase (se 2 (by rfl) ⟨848922, by rfl⟩ : syracuseStep 2263793 = 1697845) (by norm_num)
theorem B6036781 : Blo 2119435 6036781 := bstep (se 3 (by rfl) ⟨1131896, by rfl⟩ : syracuseStep 6036781 = 2263793) B2263793
theorem B8049041 : Blo 2119435 8049041 := bstep (se 2 (by rfl) ⟨3018390, by rfl⟩ : syracuseStep 8049041 = 6036781) B6036781
theorem B5366027 : Blo 2119435 5366027 := bstep (se 1 (by rfl) ⟨4024520, by rfl⟩ : syracuseStep 5366027 = 8049041) B8049041
theorem B3577351 : Blo 2119435 3577351 := bstep (se 1 (by rfl) ⟨2683013, by rfl⟩ : syracuseStep 3577351 = 5366027) B5366027
theorem B4769801 : Blo 2119435 4769801 := bstep (se 2 (by rfl) ⟨1788675, by rfl⟩ : syracuseStep 4769801 = 3577351) B3577351
theorem B3179867 : Blo 2119435 3179867 := bstep (se 1 (by rfl) ⟨2384900, by rfl⟩ : syracuseStep 3179867 = 4769801) B4769801
theorem B2119911 : Blo 2119435 2119911 := bstep (se 1 (by rfl) ⟨1589933, by rfl⟩ : syracuseStep 2119911 = 3179867) B3179867
theorem B2384905 : Blo 2119435 2384905 := bbase (se 2 (by rfl) ⟨894339, by rfl⟩ : syracuseStep 2384905 = 1788679) (by norm_num)
theorem B3179873 : Blo 2119435 3179873 := bstep (se 2 (by rfl) ⟨1192452, by rfl⟩ : syracuseStep 3179873 = 2384905) B2384905
theorem B2119915 : Blo 2119435 2119915 := bstep (se 1 (by rfl) ⟨1589936, by rfl⟩ : syracuseStep 2119915 = 3179873) B3179873
theorem B3820165 : Blo 2119435 3820165 := bbase (se 4 (by rfl) ⟨358140, by rfl⟩ : syracuseStep 3820165 = 716281) (by norm_num)
theorem B20374213 : Blo 2119435 20374213 := bstep (se 4 (by rfl) ⟨1910082, by rfl⟩ : syracuseStep 20374213 = 3820165) B3820165
theorem B27165617 : Blo 2119435 27165617 := bstep (se 2 (by rfl) ⟨10187106, by rfl⟩ : syracuseStep 27165617 = 20374213) B20374213
theorem B18110411 : Blo 2119435 18110411 := bstep (se 1 (by rfl) ⟨13582808, by rfl⟩ : syracuseStep 18110411 = 27165617) B27165617
theorem B12073607 : Blo 2119435 12073607 := bstep (se 1 (by rfl) ⟨9055205, by rfl⟩ : syracuseStep 12073607 = 18110411) B18110411
theorem B8049071 : Blo 2119435 8049071 := bstep (se 1 (by rfl) ⟨6036803, by rfl⟩ : syracuseStep 8049071 = 12073607) B12073607
theorem B5366047 : Blo 2119435 5366047 := bstep (se 1 (by rfl) ⟨4024535, by rfl⟩ : syracuseStep 5366047 = 8049071) B8049071
theorem B7154729 : Blo 2119435 7154729 := bstep (se 2 (by rfl) ⟨2683023, by rfl⟩ : syracuseStep 7154729 = 5366047) B5366047
theorem B4769819 : Blo 2119435 4769819 := bstep (se 1 (by rfl) ⟨3577364, by rfl⟩ : syracuseStep 4769819 = 7154729) B7154729
theorem B3179879 : Blo 2119435 3179879 := bstep (se 1 (by rfl) ⟨2384909, by rfl⟩ : syracuseStep 3179879 = 4769819) B4769819
theorem B2119919 : Blo 2119435 2119919 := bstep (se 1 (by rfl) ⟨1589939, by rfl⟩ : syracuseStep 2119919 = 3179879) B3179879
theorem B3179885 : Blo 2119435 3179885 := bbase (se 3 (by rfl) ⟨596228, by rfl⟩ : syracuseStep 3179885 = 1192457) (by norm_num)
theorem B2119923 : Blo 2119435 2119923 := bstep (se 1 (by rfl) ⟨1589942, by rfl⟩ : syracuseStep 2119923 = 3179885) B3179885
theorem B4769837 : Blo 2119435 4769837 := bbase (se 3 (by rfl) ⟨894344, by rfl⟩ : syracuseStep 4769837 = 1788689) (by norm_num)
theorem B3179891 : Blo 2119435 3179891 := bstep (se 1 (by rfl) ⟨2384918, by rfl⟩ : syracuseStep 3179891 = 4769837) B4769837
theorem B2119927 : Blo 2119435 2119927 := bstep (se 1 (by rfl) ⟨1589945, by rfl⟩ : syracuseStep 2119927 = 3179891) B3179891
theorem B2294701 : Blo 2119435 2294701 := bbase (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) (by norm_num)
theorem B48953621 : Blo 2119435 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B32635747 : Blo 2119435 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B43514329 : Blo 2119435 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B58019105 : Blo 2119435 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B38679403 : Blo 2119435 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B51572537 : Blo 2119435 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B34381691 : Blo 2119435 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B22921127 : Blo 2119435 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B15280751 : Blo 2119435 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B10187167 : Blo 2119435 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B13582889 : Blo 2119435 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B9055259 : Blo 2119435 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B6036839 : Blo 2119435 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B4024559 : Blo 2119435 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B2683039 : Blo 2119435 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B3577385 : Blo 2119435 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B2384923 : Blo 2119435 2384923 := bstep (se 1 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 2384923 = 3577385) B3577385
theorem B3179897 : Blo 2119435 3179897 := bstep (se 2 (by rfl) ⟨1192461, by rfl⟩ : syracuseStep 3179897 = 2384923) B2384923
theorem B2119931 : Blo 2119435 2119931 := bstep (se 1 (by rfl) ⟨1589948, by rfl⟩ : syracuseStep 2119931 = 3179897) B3179897
theorem B4834933 : Blo 2119435 4834933 := bbase (se 5 (by rfl) ⟨226637, by rfl⟩ : syracuseStep 4834933 = 453275) (by norm_num)
theorem B25786309 : Blo 2119435 25786309 := bstep (se 4 (by rfl) ⟨2417466, by rfl⟩ : syracuseStep 25786309 = 4834933) B4834933
theorem B34381745 : Blo 2119435 34381745 := bstep (se 2 (by rfl) ⟨12893154, by rfl⟩ : syracuseStep 34381745 = 25786309) B25786309
theorem B22921163 : Blo 2119435 22921163 := bstep (se 1 (by rfl) ⟨17190872, by rfl⟩ : syracuseStep 22921163 = 34381745) B34381745
theorem B15280775 : Blo 2119435 15280775 := bstep (se 1 (by rfl) ⟨11460581, by rfl⟩ : syracuseStep 15280775 = 22921163) B22921163
theorem B10187183 : Blo 2119435 10187183 := bstep (se 1 (by rfl) ⟨7640387, by rfl⟩ : syracuseStep 10187183 = 15280775) B15280775
theorem B6791455 : Blo 2119435 6791455 := bstep (se 1 (by rfl) ⟨5093591, by rfl⟩ : syracuseStep 6791455 = 10187183) B10187183
theorem B36221093 : Blo 2119435 36221093 := bstep (se 4 (by rfl) ⟨3395727, by rfl⟩ : syracuseStep 36221093 = 6791455) B6791455
theorem B24147395 : Blo 2119435 24147395 := bstep (se 1 (by rfl) ⟨18110546, by rfl⟩ : syracuseStep 24147395 = 36221093) B36221093
theorem B16098263 : Blo 2119435 16098263 := bstep (se 1 (by rfl) ⟨12073697, by rfl⟩ : syracuseStep 16098263 = 24147395) B24147395
theorem B10732175 : Blo 2119435 10732175 := bstep (se 1 (by rfl) ⟨8049131, by rfl⟩ : syracuseStep 10732175 = 16098263) B16098263
theorem B7154783 : Blo 2119435 7154783 := bstep (se 1 (by rfl) ⟨5366087, by rfl⟩ : syracuseStep 7154783 = 10732175) B10732175
theorem B4769855 : Blo 2119435 4769855 := bstep (se 1 (by rfl) ⟨3577391, by rfl⟩ : syracuseStep 4769855 = 7154783) B7154783
theorem B3179903 : Blo 2119435 3179903 := bstep (se 1 (by rfl) ⟨2384927, by rfl⟩ : syracuseStep 3179903 = 4769855) B4769855
theorem B2119935 : Blo 2119435 2119935 := bstep (se 1 (by rfl) ⟨1589951, by rfl⟩ : syracuseStep 2119935 = 3179903) B3179903
theorem B3179909 : Blo 2119435 3179909 := bbase (se 4 (by rfl) ⟨298116, by rfl⟩ : syracuseStep 3179909 = 596233) (by norm_num)
theorem B2119939 : Blo 2119435 2119939 := bstep (se 1 (by rfl) ⟨1589954, by rfl⟩ : syracuseStep 2119939 = 3179909) B3179909
theorem B3577405 : Blo 2119435 3577405 := bbase (se 3 (by rfl) ⟨670763, by rfl⟩ : syracuseStep 3577405 = 1341527) (by norm_num)
theorem B4769873 : Blo 2119435 4769873 := bstep (se 2 (by rfl) ⟨1788702, by rfl⟩ : syracuseStep 4769873 = 3577405) B3577405
theorem B3179915 : Blo 2119435 3179915 := bstep (se 1 (by rfl) ⟨2384936, by rfl⟩ : syracuseStep 3179915 = 4769873) B4769873
theorem B2119943 : Blo 2119435 2119943 := bstep (se 1 (by rfl) ⟨1589957, by rfl⟩ : syracuseStep 2119943 = 3179915) B3179915
theorem B2384941 : Blo 2119435 2384941 := bbase (se 3 (by rfl) ⟨447176, by rfl⟩ : syracuseStep 2384941 = 894353) (by norm_num)
theorem B3179921 : Blo 2119435 3179921 := bstep (se 2 (by rfl) ⟨1192470, by rfl⟩ : syracuseStep 3179921 = 2384941) B2384941
theorem B2119947 : Blo 2119435 2119947 := bstep (se 1 (by rfl) ⟨1589960, by rfl⟩ : syracuseStep 2119947 = 3179921) B3179921
theorem B7154837 : Blo 2119435 7154837 := bbase (se 6 (by rfl) ⟨167691, by rfl⟩ : syracuseStep 7154837 = 335383) (by norm_num)
theorem B4769891 : Blo 2119435 4769891 := bstep (se 1 (by rfl) ⟨3577418, by rfl⟩ : syracuseStep 4769891 = 7154837) B7154837
theorem B3179927 : Blo 2119435 3179927 := bstep (se 1 (by rfl) ⟨2384945, by rfl⟩ : syracuseStep 3179927 = 4769891) B4769891
theorem B2119951 : Blo 2119435 2119951 := bstep (se 1 (by rfl) ⟨1589963, by rfl⟩ : syracuseStep 2119951 = 3179927) B3179927
theorem B3179933 : Blo 2119435 3179933 := bbase (se 3 (by rfl) ⟨596237, by rfl⟩ : syracuseStep 3179933 = 1192475) (by norm_num)
theorem B2119955 : Blo 2119435 2119955 := bstep (se 1 (by rfl) ⟨1589966, by rfl⟩ : syracuseStep 2119955 = 3179933) B3179933
theorem B4769909 : Blo 2119435 4769909 := bbase (se 5 (by rfl) ⟨223589, by rfl⟩ : syracuseStep 4769909 = 447179) (by norm_num)
theorem B3179939 : Blo 2119435 3179939 := bstep (se 1 (by rfl) ⟨2384954, by rfl⟩ : syracuseStep 3179939 = 4769909) B4769909
theorem B2119959 : Blo 2119435 2119959 := bstep (se 1 (by rfl) ⟨1589969, by rfl⟩ : syracuseStep 2119959 = 3179939) B3179939
theorem B3395773 : Blo 2119435 3395773 := bbase (se 3 (by rfl) ⟨636707, by rfl⟩ : syracuseStep 3395773 = 1273415) (by norm_num)
theorem B18110789 : Blo 2119435 18110789 := bstep (se 4 (by rfl) ⟨1697886, by rfl⟩ : syracuseStep 18110789 = 3395773) B3395773
theorem B12073859 : Blo 2119435 12073859 := bstep (se 1 (by rfl) ⟨9055394, by rfl⟩ : syracuseStep 12073859 = 18110789) B18110789
theorem B8049239 : Blo 2119435 8049239 := bstep (se 1 (by rfl) ⟨6036929, by rfl⟩ : syracuseStep 8049239 = 12073859) B12073859
theorem B5366159 : Blo 2119435 5366159 := bstep (se 1 (by rfl) ⟨4024619, by rfl⟩ : syracuseStep 5366159 = 8049239) B8049239
theorem B3577439 : Blo 2119435 3577439 := bstep (se 1 (by rfl) ⟨2683079, by rfl⟩ : syracuseStep 3577439 = 5366159) B5366159
theorem B2384959 : Blo 2119435 2384959 := bstep (se 1 (by rfl) ⟨1788719, by rfl⟩ : syracuseStep 2384959 = 3577439) B3577439
theorem B3179945 : Blo 2119435 3179945 := bstep (se 2 (by rfl) ⟨1192479, by rfl⟩ : syracuseStep 3179945 = 2384959) B2384959
theorem B2119963 : Blo 2119435 2119963 := bstep (se 1 (by rfl) ⟨1589972, by rfl⟩ : syracuseStep 2119963 = 3179945) B3179945
theorem B8049253 : Blo 2119435 8049253 := bbase (se 4 (by rfl) ⟨754617, by rfl⟩ : syracuseStep 8049253 = 1509235) (by norm_num)
theorem B10732337 : Blo 2119435 10732337 := bstep (se 2 (by rfl) ⟨4024626, by rfl⟩ : syracuseStep 10732337 = 8049253) B8049253
theorem B7154891 : Blo 2119435 7154891 := bstep (se 1 (by rfl) ⟨5366168, by rfl⟩ : syracuseStep 7154891 = 10732337) B10732337
theorem B4769927 : Blo 2119435 4769927 := bstep (se 1 (by rfl) ⟨3577445, by rfl⟩ : syracuseStep 4769927 = 7154891) B7154891
theorem B3179951 : Blo 2119435 3179951 := bstep (se 1 (by rfl) ⟨2384963, by rfl⟩ : syracuseStep 3179951 = 4769927) B4769927
theorem B2119967 : Blo 2119435 2119967 := bstep (se 1 (by rfl) ⟨1589975, by rfl⟩ : syracuseStep 2119967 = 3179951) B3179951
theorem B3179957 : Blo 2119435 3179957 := bbase (se 5 (by rfl) ⟨149060, by rfl⟩ : syracuseStep 3179957 = 298121) (by norm_num)
theorem B2119971 : Blo 2119435 2119971 := bstep (se 1 (by rfl) ⟨1589978, by rfl⟩ : syracuseStep 2119971 = 3179957) B3179957
theorem B5366189 : Blo 2119435 5366189 := bbase (se 3 (by rfl) ⟨1006160, by rfl⟩ : syracuseStep 5366189 = 2012321) (by norm_num)
theorem B3577459 : Blo 2119435 3577459 := bstep (se 1 (by rfl) ⟨2683094, by rfl⟩ : syracuseStep 3577459 = 5366189) B5366189
theorem B4769945 : Blo 2119435 4769945 := bstep (se 2 (by rfl) ⟨1788729, by rfl⟩ : syracuseStep 4769945 = 3577459) B3577459
theorem B3179963 : Blo 2119435 3179963 := bstep (se 1 (by rfl) ⟨2384972, by rfl⟩ : syracuseStep 3179963 = 4769945) B4769945
theorem B2119975 : Blo 2119435 2119975 := bstep (se 1 (by rfl) ⟨1589981, by rfl⟩ : syracuseStep 2119975 = 3179963) B3179963
theorem B2384977 : Blo 2119435 2384977 := bbase (se 2 (by rfl) ⟨894366, by rfl⟩ : syracuseStep 2384977 = 1788733) (by norm_num)
theorem B3179969 : Blo 2119435 3179969 := bstep (se 2 (by rfl) ⟨1192488, by rfl⟩ : syracuseStep 3179969 = 2384977) B2384977
theorem B2119979 : Blo 2119435 2119979 := bstep (se 1 (by rfl) ⟨1589984, by rfl⟩ : syracuseStep 2119979 = 3179969) B3179969
theorem B3018493 : Blo 2119435 3018493 := bbase (se 3 (by rfl) ⟨565967, by rfl⟩ : syracuseStep 3018493 = 1131935) (by norm_num)
theorem B4024657 : Blo 2119435 4024657 := bstep (se 2 (by rfl) ⟨1509246, by rfl⟩ : syracuseStep 4024657 = 3018493) B3018493
theorem B5366209 : Blo 2119435 5366209 := bstep (se 2 (by rfl) ⟨2012328, by rfl⟩ : syracuseStep 5366209 = 4024657) B4024657
theorem B7154945 : Blo 2119435 7154945 := bstep (se 2 (by rfl) ⟨2683104, by rfl⟩ : syracuseStep 7154945 = 5366209) B5366209
theorem B4769963 : Blo 2119435 4769963 := bstep (se 1 (by rfl) ⟨3577472, by rfl⟩ : syracuseStep 4769963 = 7154945) B7154945
theorem B3179975 : Blo 2119435 3179975 := bstep (se 1 (by rfl) ⟨2384981, by rfl⟩ : syracuseStep 3179975 = 4769963) B4769963
theorem B2119983 : Blo 2119435 2119983 := bstep (se 1 (by rfl) ⟨1589987, by rfl⟩ : syracuseStep 2119983 = 3179975) B3179975
theorem B3179981 : Blo 2119435 3179981 := bbase (se 3 (by rfl) ⟨596246, by rfl⟩ : syracuseStep 3179981 = 1192493) (by norm_num)
theorem B2119987 : Blo 2119435 2119987 := bstep (se 1 (by rfl) ⟨1589990, by rfl⟩ : syracuseStep 2119987 = 3179981) B3179981
theorem B4769981 : Blo 2119435 4769981 := bbase (se 3 (by rfl) ⟨894371, by rfl⟩ : syracuseStep 4769981 = 1788743) (by norm_num)
theorem B3179987 : Blo 2119435 3179987 := bstep (se 1 (by rfl) ⟨2384990, by rfl⟩ : syracuseStep 3179987 = 4769981) B4769981
theorem B2119991 : Blo 2119435 2119991 := bstep (se 1 (by rfl) ⟨1589993, by rfl⟩ : syracuseStep 2119991 = 3179987) B3179987
theorem B3577493 : Blo 2119435 3577493 := bbase (se 6 (by rfl) ⟨83847, by rfl⟩ : syracuseStep 3577493 = 167695) (by norm_num)
theorem B2384995 : Blo 2119435 2384995 := bstep (se 1 (by rfl) ⟨1788746, by rfl⟩ : syracuseStep 2384995 = 3577493) B3577493
theorem B3179993 : Blo 2119435 3179993 := bstep (se 2 (by rfl) ⟨1192497, by rfl⟩ : syracuseStep 3179993 = 2384995) B2384995
theorem B2119995 : Blo 2119435 2119995 := bstep (se 1 (by rfl) ⟨1589996, by rfl⟩ : syracuseStep 2119995 = 3179993) B3179993
theorem B15281237 : Blo 2119435 15281237 := bbase (se 8 (by rfl) ⟨89538, by rfl⟩ : syracuseStep 15281237 = 179077) (by norm_num)
theorem B10187491 : Blo 2119435 10187491 := bstep (se 1 (by rfl) ⟨7640618, by rfl⟩ : syracuseStep 10187491 = 15281237) B15281237
theorem B13583321 : Blo 2119435 13583321 := bstep (se 2 (by rfl) ⟨5093745, by rfl⟩ : syracuseStep 13583321 = 10187491) B10187491
theorem B9055547 : Blo 2119435 9055547 := bstep (se 1 (by rfl) ⟨6791660, by rfl⟩ : syracuseStep 9055547 = 13583321) B13583321
theorem B6037031 : Blo 2119435 6037031 := bstep (se 1 (by rfl) ⟨4527773, by rfl⟩ : syracuseStep 6037031 = 9055547) B9055547
theorem B16098749 : Blo 2119435 16098749 := bstep (se 3 (by rfl) ⟨3018515, by rfl⟩ : syracuseStep 16098749 = 6037031) B6037031
theorem B10732499 : Blo 2119435 10732499 := bstep (se 1 (by rfl) ⟨8049374, by rfl⟩ : syracuseStep 10732499 = 16098749) B16098749
theorem B7154999 : Blo 2119435 7154999 := bstep (se 1 (by rfl) ⟨5366249, by rfl⟩ : syracuseStep 7154999 = 10732499) B10732499
theorem B4769999 : Blo 2119435 4769999 := bstep (se 1 (by rfl) ⟨3577499, by rfl⟩ : syracuseStep 4769999 = 7154999) B7154999
theorem B3179999 : Blo 2119435 3179999 := bstep (se 1 (by rfl) ⟨2384999, by rfl⟩ : syracuseStep 3179999 = 4769999) B4769999
theorem B2119999 : Blo 2119435 2119999 := bstep (se 1 (by rfl) ⟨1589999, by rfl⟩ : syracuseStep 2119999 = 3179999) B3179999
theorem B3180005 : Blo 2119435 3180005 := bbase (se 4 (by rfl) ⟨298125, by rfl⟩ : syracuseStep 3180005 = 596251) (by norm_num)
theorem B2120003 : Blo 2119435 2120003 := bstep (se 1 (by rfl) ⟨1590002, by rfl⟩ : syracuseStep 2120003 = 3180005) B3180005
theorem B4306853 : Blo 2119435 4306853 := bbase (se 4 (by rfl) ⟨403767, by rfl⟩ : syracuseStep 4306853 = 807535) (by norm_num)
theorem B2871235 : Blo 2119435 2871235 := bstep (se 1 (by rfl) ⟨2153426, by rfl⟩ : syracuseStep 2871235 = 4306853) B4306853
theorem B3828313 : Blo 2119435 3828313 := bstep (se 2 (by rfl) ⟨1435617, by rfl⟩ : syracuseStep 3828313 = 2871235) B2871235
theorem B5104417 : Blo 2119435 5104417 := bstep (se 2 (by rfl) ⟨1914156, by rfl⟩ : syracuseStep 5104417 = 3828313) B3828313
theorem B6805889 : Blo 2119435 6805889 := bstep (se 2 (by rfl) ⟨2552208, by rfl⟩ : syracuseStep 6805889 = 5104417) B5104417
theorem B4537259 : Blo 2119435 4537259 := bstep (se 1 (by rfl) ⟨3402944, by rfl⟩ : syracuseStep 4537259 = 6805889) B6805889
theorem B48397429 : Blo 2119435 48397429 := bstep (se 5 (by rfl) ⟨2268629, by rfl⟩ : syracuseStep 48397429 = 4537259) B4537259
theorem B64529905 : Blo 2119435 64529905 := bstep (se 2 (by rfl) ⟨24198714, by rfl⟩ : syracuseStep 64529905 = 48397429) B48397429
theorem B86039873 : Blo 2119435 86039873 := bstep (se 2 (by rfl) ⟨32264952, by rfl⟩ : syracuseStep 86039873 = 64529905) B64529905
theorem B57359915 : Blo 2119435 57359915 := bstep (se 1 (by rfl) ⟨43019936, by rfl⟩ : syracuseStep 57359915 = 86039873) B86039873
theorem B38239943 : Blo 2119435 38239943 := bstep (se 1 (by rfl) ⟨28679957, by rfl⟩ : syracuseStep 38239943 = 57359915) B57359915
theorem B101973181 : Blo 2119435 101973181 := bstep (se 3 (by rfl) ⟨19119971, by rfl⟩ : syracuseStep 101973181 = 38239943) B38239943
theorem B135964241 : Blo 2119435 135964241 := bstep (se 2 (by rfl) ⟨50986590, by rfl⟩ : syracuseStep 135964241 = 101973181) B101973181
theorem B90642827 : Blo 2119435 90642827 := bstep (se 1 (by rfl) ⟨67982120, by rfl⟩ : syracuseStep 90642827 = 135964241) B135964241
theorem B60428551 : Blo 2119435 60428551 := bstep (se 1 (by rfl) ⟨45321413, by rfl⟩ : syracuseStep 60428551 = 90642827) B90642827
theorem B80571401 : Blo 2119435 80571401 := bstep (se 2 (by rfl) ⟨30214275, by rfl⟩ : syracuseStep 80571401 = 60428551) B60428551
theorem B53714267 : Blo 2119435 53714267 := bstep (se 1 (by rfl) ⟨40285700, by rfl⟩ : syracuseStep 53714267 = 80571401) B80571401
theorem B35809511 : Blo 2119435 35809511 := bstep (se 1 (by rfl) ⟨26857133, by rfl⟩ : syracuseStep 35809511 = 53714267) B53714267
theorem B95492029 : Blo 2119435 95492029 := bstep (se 3 (by rfl) ⟨17904755, by rfl⟩ : syracuseStep 95492029 = 35809511) B35809511
theorem B127322705 : Blo 2119435 127322705 := bstep (se 2 (by rfl) ⟨47746014, by rfl⟩ : syracuseStep 127322705 = 95492029) B95492029
theorem B84881803 : Blo 2119435 84881803 := bstep (se 1 (by rfl) ⟨63661352, by rfl⟩ : syracuseStep 84881803 = 127322705) B127322705
theorem B113175737 : Blo 2119435 113175737 := bstep (se 2 (by rfl) ⟨42440901, by rfl⟩ : syracuseStep 113175737 = 84881803) B84881803
theorem B75450491 : Blo 2119435 75450491 := bstep (se 1 (by rfl) ⟨56587868, by rfl⟩ : syracuseStep 75450491 = 113175737) B113175737
theorem B804805237 : Blo 2119435 804805237 := bstep (se 5 (by rfl) ⟨37725245, by rfl⟩ : syracuseStep 804805237 = 75450491) B75450491
theorem B4292294597 : Blo 2119435 4292294597 := bstep (se 4 (by rfl) ⟨402402618, by rfl⟩ : syracuseStep 4292294597 = 804805237) B804805237
theorem B2861529731 : Blo 2119435 2861529731 := bstep (se 1 (by rfl) ⟨2146147298, by rfl⟩ : syracuseStep 2861529731 = 4292294597) B4292294597
theorem B1907686487 : Blo 2119435 1907686487 := bstep (se 1 (by rfl) ⟨1430764865, by rfl⟩ : syracuseStep 1907686487 = 2861529731) B2861529731
theorem B1271790991 : Blo 2119435 1271790991 := bstep (se 1 (by rfl) ⟨953843243, by rfl⟩ : syracuseStep 1271790991 = 1907686487) B1907686487
theorem B1695721321 : Blo 2119435 1695721321 := bstep (se 2 (by rfl) ⟨635895495, by rfl⟩ : syracuseStep 1695721321 = 1271790991) B1271790991
theorem B2260961761 : Blo 2119435 2260961761 := bstep (se 2 (by rfl) ⟨847860660, by rfl⟩ : syracuseStep 2260961761 = 1695721321) B1695721321
theorem B3014615681 : Blo 2119435 3014615681 := bstep (se 2 (by rfl) ⟨1130480880, by rfl⟩ : syracuseStep 3014615681 = 2260961761) B2260961761
theorem B2009743787 : Blo 2119435 2009743787 := bstep (se 1 (by rfl) ⟨1507307840, by rfl⟩ : syracuseStep 2009743787 = 3014615681) B3014615681
theorem B1339829191 : Blo 2119435 1339829191 := bstep (se 1 (by rfl) ⟨1004871893, by rfl⟩ : syracuseStep 1339829191 = 2009743787) B2009743787
theorem B1786438921 : Blo 2119435 1786438921 := bstep (se 2 (by rfl) ⟨669914595, by rfl⟩ : syracuseStep 1786438921 = 1339829191) B1339829191
theorem B2381918561 : Blo 2119435 2381918561 := bstep (se 2 (by rfl) ⟨893219460, by rfl⟩ : syracuseStep 2381918561 = 1786438921) B1786438921
theorem B1587945707 : Blo 2119435 1587945707 := bstep (se 1 (by rfl) ⟨1190959280, by rfl⟩ : syracuseStep 1587945707 = 2381918561) B2381918561
theorem B1058630471 : Blo 2119435 1058630471 := bstep (se 1 (by rfl) ⟨793972853, by rfl⟩ : syracuseStep 1058630471 = 1587945707) B1587945707
theorem B705753647 : Blo 2119435 705753647 := bstep (se 1 (by rfl) ⟨529315235, by rfl⟩ : syracuseStep 705753647 = 1058630471) B1058630471
theorem B470502431 : Blo 2119435 470502431 := bstep (se 1 (by rfl) ⟨352876823, by rfl⟩ : syracuseStep 470502431 = 705753647) B705753647
theorem B313668287 : Blo 2119435 313668287 := bstep (se 1 (by rfl) ⟨235251215, by rfl⟩ : syracuseStep 313668287 = 470502431) B470502431
theorem B209112191 : Blo 2119435 209112191 := bstep (se 1 (by rfl) ⟨156834143, by rfl⟩ : syracuseStep 209112191 = 313668287) B313668287
theorem B139408127 : Blo 2119435 139408127 := bstep (se 1 (by rfl) ⟨104556095, by rfl⟩ : syracuseStep 139408127 = 209112191) B209112191
theorem B92938751 : Blo 2119435 92938751 := bstep (se 1 (by rfl) ⟨69704063, by rfl⟩ : syracuseStep 92938751 = 139408127) B139408127
theorem B61959167 : Blo 2119435 61959167 := bstep (se 1 (by rfl) ⟨46469375, by rfl⟩ : syracuseStep 61959167 = 92938751) B92938751
theorem B41306111 : Blo 2119435 41306111 := bstep (se 1 (by rfl) ⟨30979583, by rfl⟩ : syracuseStep 41306111 = 61959167) B61959167
theorem B27537407 : Blo 2119435 27537407 := bstep (se 1 (by rfl) ⟨20653055, by rfl⟩ : syracuseStep 27537407 = 41306111) B41306111
theorem B18358271 : Blo 2119435 18358271 := bstep (se 1 (by rfl) ⟨13768703, by rfl⟩ : syracuseStep 18358271 = 27537407) B27537407
theorem B12238847 : Blo 2119435 12238847 := bstep (se 1 (by rfl) ⟨9179135, by rfl⟩ : syracuseStep 12238847 = 18358271) B18358271
theorem B8159231 : Blo 2119435 8159231 := bstep (se 1 (by rfl) ⟨6119423, by rfl⟩ : syracuseStep 8159231 = 12238847) B12238847
theorem B5439487 : Blo 2119435 5439487 := bstep (se 1 (by rfl) ⟨4079615, by rfl⟩ : syracuseStep 5439487 = 8159231) B8159231
theorem B7252649 : Blo 2119435 7252649 := bstep (se 2 (by rfl) ⟨2719743, by rfl⟩ : syracuseStep 7252649 = 5439487) B5439487
theorem B4835099 : Blo 2119435 4835099 := bstep (se 1 (by rfl) ⟨3626324, by rfl⟩ : syracuseStep 4835099 = 7252649) B7252649
theorem B3223399 : Blo 2119435 3223399 := bstep (se 1 (by rfl) ⟨2417549, by rfl⟩ : syracuseStep 3223399 = 4835099) B4835099
theorem B4297865 : Blo 2119435 4297865 := bstep (se 2 (by rfl) ⟨1611699, by rfl⟩ : syracuseStep 4297865 = 3223399) B3223399
theorem B45843893 : Blo 2119435 45843893 := bstep (se 5 (by rfl) ⟨2148932, by rfl⟩ : syracuseStep 45843893 = 4297865) B4297865
theorem B30562595 : Blo 2119435 30562595 := bstep (se 1 (by rfl) ⟨22921946, by rfl⟩ : syracuseStep 30562595 = 45843893) B45843893
theorem B20375063 : Blo 2119435 20375063 := bstep (se 1 (by rfl) ⟨15281297, by rfl⟩ : syracuseStep 20375063 = 30562595) B30562595
theorem B13583375 : Blo 2119435 13583375 := bstep (se 1 (by rfl) ⟨10187531, by rfl⟩ : syracuseStep 13583375 = 20375063) B20375063
theorem B9055583 : Blo 2119435 9055583 := bstep (se 1 (by rfl) ⟨6791687, by rfl⟩ : syracuseStep 9055583 = 13583375) B13583375
theorem B6037055 : Blo 2119435 6037055 := bstep (se 1 (by rfl) ⟨4527791, by rfl⟩ : syracuseStep 6037055 = 9055583) B9055583
theorem B4024703 : Blo 2119435 4024703 := bstep (se 1 (by rfl) ⟨3018527, by rfl⟩ : syracuseStep 4024703 = 6037055) B6037055
theorem B2683135 : Blo 2119435 2683135 := bstep (se 1 (by rfl) ⟨2012351, by rfl⟩ : syracuseStep 2683135 = 4024703) B4024703
theorem B3577513 : Blo 2119435 3577513 := bstep (se 2 (by rfl) ⟨1341567, by rfl⟩ : syracuseStep 3577513 = 2683135) B2683135
theorem B4770017 : Blo 2119435 4770017 := bstep (se 2 (by rfl) ⟨1788756, by rfl⟩ : syracuseStep 4770017 = 3577513) B3577513
theorem B3180011 : Blo 2119435 3180011 := bstep (se 1 (by rfl) ⟨2385008, by rfl⟩ : syracuseStep 3180011 = 4770017) B4770017
theorem B2120007 : Blo 2119435 2120007 := bstep (se 1 (by rfl) ⟨1590005, by rfl⟩ : syracuseStep 2120007 = 3180011) B3180011
theorem B2385013 : Blo 2119435 2385013 := bbase (se 5 (by rfl) ⟨111797, by rfl⟩ : syracuseStep 2385013 = 223595) (by norm_num)
theorem B3180017 : Blo 2119435 3180017 := bstep (se 2 (by rfl) ⟨1192506, by rfl⟩ : syracuseStep 3180017 = 2385013) B2385013
theorem B2120011 : Blo 2119435 2120011 := bstep (se 1 (by rfl) ⟨1590008, by rfl⟩ : syracuseStep 2120011 = 3180017) B3180017
theorem B2683145 : Blo 2119435 2683145 := bbase (se 2 (by rfl) ⟨1006179, by rfl⟩ : syracuseStep 2683145 = 2012359) (by norm_num)
theorem B7155053 : Blo 2119435 7155053 := bstep (se 3 (by rfl) ⟨1341572, by rfl⟩ : syracuseStep 7155053 = 2683145) B2683145
theorem B4770035 : Blo 2119435 4770035 := bstep (se 1 (by rfl) ⟨3577526, by rfl⟩ : syracuseStep 4770035 = 7155053) B7155053
theorem B3180023 : Blo 2119435 3180023 := bstep (se 1 (by rfl) ⟨2385017, by rfl⟩ : syracuseStep 3180023 = 4770035) B4770035
theorem B2120015 : Blo 2119435 2120015 := bstep (se 1 (by rfl) ⟨1590011, by rfl⟩ : syracuseStep 2120015 = 3180023) B3180023
theorem B3180029 : Blo 2119435 3180029 := bbase (se 3 (by rfl) ⟨596255, by rfl⟩ : syracuseStep 3180029 = 1192511) (by norm_num)
theorem B2120019 : Blo 2119435 2120019 := bstep (se 1 (by rfl) ⟨1590014, by rfl⟩ : syracuseStep 2120019 = 3180029) B3180029
theorem B4770053 : Blo 2119435 4770053 := bbase (se 4 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 4770053 = 894385) (by norm_num)
theorem B3180035 : Blo 2119435 3180035 := bstep (se 1 (by rfl) ⟨2385026, by rfl⟩ : syracuseStep 3180035 = 4770053) B4770053
theorem B2120023 : Blo 2119435 2120023 := bstep (se 1 (by rfl) ⟨1590017, by rfl⟩ : syracuseStep 2120023 = 3180035) B3180035
theorem B4024741 : Blo 2119435 4024741 := bbase (se 4 (by rfl) ⟨377319, by rfl⟩ : syracuseStep 4024741 = 754639) (by norm_num)
theorem B5366321 : Blo 2119435 5366321 := bstep (se 2 (by rfl) ⟨2012370, by rfl⟩ : syracuseStep 5366321 = 4024741) B4024741
theorem B3577547 : Blo 2119435 3577547 := bstep (se 1 (by rfl) ⟨2683160, by rfl⟩ : syracuseStep 3577547 = 5366321) B5366321
theorem B2385031 : Blo 2119435 2385031 := bstep (se 1 (by rfl) ⟨1788773, by rfl⟩ : syracuseStep 2385031 = 3577547) B3577547
theorem B3180041 : Blo 2119435 3180041 := bstep (se 2 (by rfl) ⟨1192515, by rfl⟩ : syracuseStep 3180041 = 2385031) B2385031
theorem B2120027 : Blo 2119435 2120027 := bstep (se 1 (by rfl) ⟨1590020, by rfl⟩ : syracuseStep 2120027 = 3180041) B3180041
theorem B10732661 : Blo 2119435 10732661 := bbase (se 5 (by rfl) ⟨503093, by rfl⟩ : syracuseStep 10732661 = 1006187) (by norm_num)
theorem B7155107 : Blo 2119435 7155107 := bstep (se 1 (by rfl) ⟨5366330, by rfl⟩ : syracuseStep 7155107 = 10732661) B10732661
theorem B4770071 : Blo 2119435 4770071 := bstep (se 1 (by rfl) ⟨3577553, by rfl⟩ : syracuseStep 4770071 = 7155107) B7155107
theorem B3180047 : Blo 2119435 3180047 := bstep (se 1 (by rfl) ⟨2385035, by rfl⟩ : syracuseStep 3180047 = 4770071) B4770071
theorem B2120031 : Blo 2119435 2120031 := bstep (se 1 (by rfl) ⟨1590023, by rfl⟩ : syracuseStep 2120031 = 3180047) B3180047
theorem B3180053 : Blo 2119435 3180053 := bbase (se 6 (by rfl) ⟨74532, by rfl⟩ : syracuseStep 3180053 = 149065) (by norm_num)
theorem B2120035 : Blo 2119435 2120035 := bstep (se 1 (by rfl) ⟨1590026, by rfl⟩ : syracuseStep 2120035 = 3180053) B3180053
theorem B2546921 : Blo 2119435 2546921 := bbase (se 2 (by rfl) ⟨955095, by rfl⟩ : syracuseStep 2546921 = 1910191) (by norm_num)
theorem B6791789 : Blo 2119435 6791789 := bstep (se 3 (by rfl) ⟨1273460, by rfl⟩ : syracuseStep 6791789 = 2546921) B2546921
theorem B18111437 : Blo 2119435 18111437 := bstep (se 3 (by rfl) ⟨3395894, by rfl⟩ : syracuseStep 18111437 = 6791789) B6791789
theorem B12074291 : Blo 2119435 12074291 := bstep (se 1 (by rfl) ⟨9055718, by rfl⟩ : syracuseStep 12074291 = 18111437) B18111437
theorem B8049527 : Blo 2119435 8049527 := bstep (se 1 (by rfl) ⟨6037145, by rfl⟩ : syracuseStep 8049527 = 12074291) B12074291
theorem B5366351 : Blo 2119435 5366351 := bstep (se 1 (by rfl) ⟨4024763, by rfl⟩ : syracuseStep 5366351 = 8049527) B8049527
theorem B3577567 : Blo 2119435 3577567 := bstep (se 1 (by rfl) ⟨2683175, by rfl⟩ : syracuseStep 3577567 = 5366351) B5366351
theorem B4770089 : Blo 2119435 4770089 := bstep (se 2 (by rfl) ⟨1788783, by rfl⟩ : syracuseStep 4770089 = 3577567) B3577567
theorem B3180059 : Blo 2119435 3180059 := bstep (se 1 (by rfl) ⟨2385044, by rfl⟩ : syracuseStep 3180059 = 4770089) B4770089
theorem B2120039 : Blo 2119435 2120039 := bstep (se 1 (by rfl) ⟨1590029, by rfl⟩ : syracuseStep 2120039 = 3180059) B3180059
theorem B2385049 : Blo 2119435 2385049 := bbase (se 2 (by rfl) ⟨894393, by rfl⟩ : syracuseStep 2385049 = 1788787) (by norm_num)
theorem B3180065 : Blo 2119435 3180065 := bstep (se 2 (by rfl) ⟨1192524, by rfl⟩ : syracuseStep 3180065 = 2385049) B2385049
theorem B2120043 : Blo 2119435 2120043 := bstep (se 1 (by rfl) ⟨1590032, by rfl⟩ : syracuseStep 2120043 = 3180065) B3180065
theorem B8049557 : Blo 2119435 8049557 := bbase (se 6 (by rfl) ⟨188661, by rfl⟩ : syracuseStep 8049557 = 377323) (by norm_num)
theorem B5366371 : Blo 2119435 5366371 := bstep (se 1 (by rfl) ⟨4024778, by rfl⟩ : syracuseStep 5366371 = 8049557) B8049557
theorem B7155161 : Blo 2119435 7155161 := bstep (se 2 (by rfl) ⟨2683185, by rfl⟩ : syracuseStep 7155161 = 5366371) B5366371
theorem B4770107 : Blo 2119435 4770107 := bstep (se 1 (by rfl) ⟨3577580, by rfl⟩ : syracuseStep 4770107 = 7155161) B7155161
theorem B3180071 : Blo 2119435 3180071 := bstep (se 1 (by rfl) ⟨2385053, by rfl⟩ : syracuseStep 3180071 = 4770107) B4770107
theorem B2120047 : Blo 2119435 2120047 := bstep (se 1 (by rfl) ⟨1590035, by rfl⟩ : syracuseStep 2120047 = 3180071) B3180071
theorem B3180077 : Blo 2119435 3180077 := bbase (se 3 (by rfl) ⟨596264, by rfl⟩ : syracuseStep 3180077 = 1192529) (by norm_num)
theorem B2120051 : Blo 2119435 2120051 := bstep (se 1 (by rfl) ⟨1590038, by rfl⟩ : syracuseStep 2120051 = 3180077) B3180077
theorem B4770125 : Blo 2119435 4770125 := bbase (se 3 (by rfl) ⟨894398, by rfl⟩ : syracuseStep 4770125 = 1788797) (by norm_num)
theorem B3180083 : Blo 2119435 3180083 := bstep (se 1 (by rfl) ⟨2385062, by rfl⟩ : syracuseStep 3180083 = 4770125) B4770125
theorem B2120055 : Blo 2119435 2120055 := bstep (se 1 (by rfl) ⟨1590041, by rfl⟩ : syracuseStep 2120055 = 3180083) B3180083
theorem B2683201 : Blo 2119435 2683201 := bbase (se 2 (by rfl) ⟨1006200, by rfl⟩ : syracuseStep 2683201 = 2012401) (by norm_num)
theorem B3577601 : Blo 2119435 3577601 := bstep (se 2 (by rfl) ⟨1341600, by rfl⟩ : syracuseStep 3577601 = 2683201) B2683201
theorem B2385067 : Blo 2119435 2385067 := bstep (se 1 (by rfl) ⟨1788800, by rfl⟩ : syracuseStep 2385067 = 3577601) B3577601
theorem B3180089 : Blo 2119435 3180089 := bstep (se 2 (by rfl) ⟨1192533, by rfl⟩ : syracuseStep 3180089 = 2385067) B2385067
theorem B2120059 : Blo 2119435 2120059 := bstep (se 1 (by rfl) ⟨1590044, by rfl⟩ : syracuseStep 2120059 = 3180089) B3180089
theorem B3395933 : Blo 2119435 3395933 := bbase (se 3 (by rfl) ⟨636737, by rfl⟩ : syracuseStep 3395933 = 1273475) (by norm_num)
theorem B2263955 : Blo 2119435 2263955 := bstep (se 1 (by rfl) ⟨1697966, by rfl⟩ : syracuseStep 2263955 = 3395933) B3395933
theorem B24148853 : Blo 2119435 24148853 := bstep (se 5 (by rfl) ⟨1131977, by rfl⟩ : syracuseStep 24148853 = 2263955) B2263955
theorem B16099235 : Blo 2119435 16099235 := bstep (se 1 (by rfl) ⟨12074426, by rfl⟩ : syracuseStep 16099235 = 24148853) B24148853
theorem B10732823 : Blo 2119435 10732823 := bstep (se 1 (by rfl) ⟨8049617, by rfl⟩ : syracuseStep 10732823 = 16099235) B16099235
theorem B7155215 : Blo 2119435 7155215 := bstep (se 1 (by rfl) ⟨5366411, by rfl⟩ : syracuseStep 7155215 = 10732823) B10732823
theorem B4770143 : Blo 2119435 4770143 := bstep (se 1 (by rfl) ⟨3577607, by rfl⟩ : syracuseStep 4770143 = 7155215) B7155215
theorem B3180095 : Blo 2119435 3180095 := bstep (se 1 (by rfl) ⟨2385071, by rfl⟩ : syracuseStep 3180095 = 4770143) B4770143
theorem B2120063 : Blo 2119435 2120063 := bstep (se 1 (by rfl) ⟨1590047, by rfl⟩ : syracuseStep 2120063 = 3180095) B3180095
theorem B3180101 : Blo 2119435 3180101 := bbase (se 4 (by rfl) ⟨298134, by rfl⟩ : syracuseStep 3180101 = 596269) (by norm_num)
theorem B2120067 : Blo 2119435 2120067 := bstep (se 1 (by rfl) ⟨1590050, by rfl⟩ : syracuseStep 2120067 = 3180101) B3180101
theorem B3577621 : Blo 2119435 3577621 := bbase (se 6 (by rfl) ⟨83850, by rfl⟩ : syracuseStep 3577621 = 167701) (by norm_num)
theorem B4770161 : Blo 2119435 4770161 := bstep (se 2 (by rfl) ⟨1788810, by rfl⟩ : syracuseStep 4770161 = 3577621) B3577621
theorem B3180107 : Blo 2119435 3180107 := bstep (se 1 (by rfl) ⟨2385080, by rfl⟩ : syracuseStep 3180107 = 4770161) B4770161
theorem B2120071 : Blo 2119435 2120071 := bstep (se 1 (by rfl) ⟨1590053, by rfl⟩ : syracuseStep 2120071 = 3180107) B3180107
theorem B2385085 : Blo 2119435 2385085 := bbase (se 3 (by rfl) ⟨447203, by rfl⟩ : syracuseStep 2385085 = 894407) (by norm_num)
theorem B3180113 : Blo 2119435 3180113 := bstep (se 2 (by rfl) ⟨1192542, by rfl⟩ : syracuseStep 3180113 = 2385085) B2385085
theorem B2120075 : Blo 2119435 2120075 := bstep (se 1 (by rfl) ⟨1590056, by rfl⟩ : syracuseStep 2120075 = 3180113) B3180113
theorem B7155269 : Blo 2119435 7155269 := bbase (se 4 (by rfl) ⟨670806, by rfl⟩ : syracuseStep 7155269 = 1341613) (by norm_num)
theorem B4770179 : Blo 2119435 4770179 := bstep (se 1 (by rfl) ⟨3577634, by rfl⟩ : syracuseStep 4770179 = 7155269) B7155269
theorem B3180119 : Blo 2119435 3180119 := bstep (se 1 (by rfl) ⟨2385089, by rfl⟩ : syracuseStep 3180119 = 4770179) B4770179
theorem B2120079 : Blo 2119435 2120079 := bstep (se 1 (by rfl) ⟨1590059, by rfl⟩ : syracuseStep 2120079 = 3180119) B3180119
theorem B3180125 : Blo 2119435 3180125 := bbase (se 3 (by rfl) ⟨596273, by rfl⟩ : syracuseStep 3180125 = 1192547) (by norm_num)
theorem B2120083 : Blo 2119435 2120083 := bstep (se 1 (by rfl) ⟨1590062, by rfl⟩ : syracuseStep 2120083 = 3180125) B3180125
theorem B4770197 : Blo 2119435 4770197 := bbase (se 6 (by rfl) ⟨111801, by rfl⟩ : syracuseStep 4770197 = 223603) (by norm_num)
theorem B3180131 : Blo 2119435 3180131 := bstep (se 1 (by rfl) ⟨2385098, by rfl⟩ : syracuseStep 3180131 = 4770197) B4770197
theorem B2120087 : Blo 2119435 2120087 := bstep (se 1 (by rfl) ⟨1590065, by rfl⟩ : syracuseStep 2120087 = 3180131) B3180131
theorem B6791957 : Blo 2119435 6791957 := bbase (se 6 (by rfl) ⟨159186, by rfl⟩ : syracuseStep 6791957 = 318373) (by norm_num)
theorem B4527971 : Blo 2119435 4527971 := bstep (se 1 (by rfl) ⟨3395978, by rfl⟩ : syracuseStep 4527971 = 6791957) B6791957
theorem B3018647 : Blo 2119435 3018647 := bstep (se 1 (by rfl) ⟨2263985, by rfl⟩ : syracuseStep 3018647 = 4527971) B4527971
theorem B8049725 : Blo 2119435 8049725 := bstep (se 3 (by rfl) ⟨1509323, by rfl⟩ : syracuseStep 8049725 = 3018647) B3018647
theorem B5366483 : Blo 2119435 5366483 := bstep (se 1 (by rfl) ⟨4024862, by rfl⟩ : syracuseStep 5366483 = 8049725) B8049725
theorem B3577655 : Blo 2119435 3577655 := bstep (se 1 (by rfl) ⟨2683241, by rfl⟩ : syracuseStep 3577655 = 5366483) B5366483
theorem B2385103 : Blo 2119435 2385103 := bstep (se 1 (by rfl) ⟨1788827, by rfl⟩ : syracuseStep 2385103 = 3577655) B3577655
theorem B3180137 : Blo 2119435 3180137 := bstep (se 2 (by rfl) ⟨1192551, by rfl⟩ : syracuseStep 3180137 = 2385103) B2385103
theorem B2120091 : Blo 2119435 2120091 := bstep (se 1 (by rfl) ⟨1590068, by rfl⟩ : syracuseStep 2120091 = 3180137) B3180137
theorem B9055957 : Blo 2119435 9055957 := bbase (se 7 (by rfl) ⟨106124, by rfl⟩ : syracuseStep 9055957 = 212249) (by norm_num)
theorem B12074609 : Blo 2119435 12074609 := bstep (se 2 (by rfl) ⟨4527978, by rfl⟩ : syracuseStep 12074609 = 9055957) B9055957
theorem B8049739 : Blo 2119435 8049739 := bstep (se 1 (by rfl) ⟨6037304, by rfl⟩ : syracuseStep 8049739 = 12074609) B12074609
theorem B10732985 : Blo 2119435 10732985 := bstep (se 2 (by rfl) ⟨4024869, by rfl⟩ : syracuseStep 10732985 = 8049739) B8049739
theorem B7155323 : Blo 2119435 7155323 := bstep (se 1 (by rfl) ⟨5366492, by rfl⟩ : syracuseStep 7155323 = 10732985) B10732985
theorem B4770215 : Blo 2119435 4770215 := bstep (se 1 (by rfl) ⟨3577661, by rfl⟩ : syracuseStep 4770215 = 7155323) B7155323
theorem B3180143 : Blo 2119435 3180143 := bstep (se 1 (by rfl) ⟨2385107, by rfl⟩ : syracuseStep 3180143 = 4770215) B4770215
theorem B2120095 : Blo 2119435 2120095 := bstep (se 1 (by rfl) ⟨1590071, by rfl⟩ : syracuseStep 2120095 = 3180143) B3180143
theorem B3180149 : Blo 2119435 3180149 := bbase (se 5 (by rfl) ⟨149069, by rfl⟩ : syracuseStep 3180149 = 298139) (by norm_num)
theorem B2120099 : Blo 2119435 2120099 := bstep (se 1 (by rfl) ⟨1590074, by rfl⟩ : syracuseStep 2120099 = 3180149) B3180149
theorem B4024885 : Blo 2119435 4024885 := bbase (se 5 (by rfl) ⟨188666, by rfl⟩ : syracuseStep 4024885 = 377333) (by norm_num)
theorem B5366513 : Blo 2119435 5366513 := bstep (se 2 (by rfl) ⟨2012442, by rfl⟩ : syracuseStep 5366513 = 4024885) B4024885
theorem B3577675 : Blo 2119435 3577675 := bstep (se 1 (by rfl) ⟨2683256, by rfl⟩ : syracuseStep 3577675 = 5366513) B5366513
theorem B4770233 : Blo 2119435 4770233 := bstep (se 2 (by rfl) ⟨1788837, by rfl⟩ : syracuseStep 4770233 = 3577675) B3577675
theorem B3180155 : Blo 2119435 3180155 := bstep (se 1 (by rfl) ⟨2385116, by rfl⟩ : syracuseStep 3180155 = 4770233) B4770233
theorem B2120103 : Blo 2119435 2120103 := bstep (se 1 (by rfl) ⟨1590077, by rfl⟩ : syracuseStep 2120103 = 3180155) B3180155
theorem B2385121 : Blo 2119435 2385121 := bbase (se 2 (by rfl) ⟨894420, by rfl⟩ : syracuseStep 2385121 = 1788841) (by norm_num)
theorem B3180161 : Blo 2119435 3180161 := bstep (se 2 (by rfl) ⟨1192560, by rfl⟩ : syracuseStep 3180161 = 2385121) B2385121
theorem B2120107 : Blo 2119435 2120107 := bstep (se 1 (by rfl) ⟨1590080, by rfl⟩ : syracuseStep 2120107 = 3180161) B3180161
theorem B5366533 : Blo 2119435 5366533 := bbase (se 4 (by rfl) ⟨503112, by rfl⟩ : syracuseStep 5366533 = 1006225) (by norm_num)
theorem B7155377 : Blo 2119435 7155377 := bstep (se 2 (by rfl) ⟨2683266, by rfl⟩ : syracuseStep 7155377 = 5366533) B5366533
theorem B4770251 : Blo 2119435 4770251 := bstep (se 1 (by rfl) ⟨3577688, by rfl⟩ : syracuseStep 4770251 = 7155377) B7155377
theorem B3180167 : Blo 2119435 3180167 := bstep (se 1 (by rfl) ⟨2385125, by rfl⟩ : syracuseStep 3180167 = 4770251) B4770251
theorem B2120111 : Blo 2119435 2120111 := bstep (se 1 (by rfl) ⟨1590083, by rfl⟩ : syracuseStep 2120111 = 3180167) B3180167
theorem B3180173 : Blo 2119435 3180173 := bbase (se 3 (by rfl) ⟨596282, by rfl⟩ : syracuseStep 3180173 = 1192565) (by norm_num)
theorem B2120115 : Blo 2119435 2120115 := bstep (se 1 (by rfl) ⟨1590086, by rfl⟩ : syracuseStep 2120115 = 3180173) B3180173
theorem B4770269 : Blo 2119435 4770269 := bbase (se 3 (by rfl) ⟨894425, by rfl⟩ : syracuseStep 4770269 = 1788851) (by norm_num)
theorem B3180179 : Blo 2119435 3180179 := bstep (se 1 (by rfl) ⟨2385134, by rfl⟩ : syracuseStep 3180179 = 4770269) B4770269
theorem B2120119 : Blo 2119435 2120119 := bstep (se 1 (by rfl) ⟨1590089, by rfl⟩ : syracuseStep 2120119 = 3180179) B3180179
theorem B3577709 : Blo 2119435 3577709 := bbase (se 3 (by rfl) ⟨670820, by rfl⟩ : syracuseStep 3577709 = 1341641) (by norm_num)
theorem B2385139 : Blo 2119435 2385139 := bstep (se 1 (by rfl) ⟨1788854, by rfl⟩ : syracuseStep 2385139 = 3577709) B3577709
theorem B3180185 : Blo 2119435 3180185 := bstep (se 2 (by rfl) ⟨1192569, by rfl⟩ : syracuseStep 3180185 = 2385139) B2385139
theorem B2120123 : Blo 2119435 2120123 := bstep (se 1 (by rfl) ⟨1590092, by rfl⟩ : syracuseStep 2120123 = 3180185) B3180185
theorem B4079845 : Blo 2119435 4079845 := bbase (se 4 (by rfl) ⟨382485, by rfl⟩ : syracuseStep 4079845 = 764971) (by norm_num)
theorem B5439793 : Blo 2119435 5439793 := bstep (se 2 (by rfl) ⟨2039922, by rfl⟩ : syracuseStep 5439793 = 4079845) B4079845
theorem B7253057 : Blo 2119435 7253057 := bstep (se 2 (by rfl) ⟨2719896, by rfl⟩ : syracuseStep 7253057 = 5439793) B5439793
theorem B4835371 : Blo 2119435 4835371 := bstep (se 1 (by rfl) ⟨3626528, by rfl⟩ : syracuseStep 4835371 = 7253057) B7253057
theorem B6447161 : Blo 2119435 6447161 := bstep (se 2 (by rfl) ⟨2417685, by rfl⟩ : syracuseStep 6447161 = 4835371) B4835371
theorem B17192429 : Blo 2119435 17192429 := bstep (se 3 (by rfl) ⟨3223580, by rfl⟩ : syracuseStep 17192429 = 6447161) B6447161
theorem B11461619 : Blo 2119435 11461619 := bstep (se 1 (by rfl) ⟨8596214, by rfl⟩ : syracuseStep 11461619 = 17192429) B17192429
theorem B30564317 : Blo 2119435 30564317 := bstep (se 3 (by rfl) ⟨5730809, by rfl⟩ : syracuseStep 30564317 = 11461619) B11461619
theorem B20376211 : Blo 2119435 20376211 := bstep (se 1 (by rfl) ⟨15282158, by rfl⟩ : syracuseStep 20376211 = 30564317) B30564317
theorem B27168281 : Blo 2119435 27168281 := bstep (se 2 (by rfl) ⟨10188105, by rfl⟩ : syracuseStep 27168281 = 20376211) B20376211
theorem B18112187 : Blo 2119435 18112187 := bstep (se 1 (by rfl) ⟨13584140, by rfl⟩ : syracuseStep 18112187 = 27168281) B27168281
theorem B12074791 : Blo 2119435 12074791 := bstep (se 1 (by rfl) ⟨9056093, by rfl⟩ : syracuseStep 12074791 = 18112187) B18112187
theorem B16099721 : Blo 2119435 16099721 := bstep (se 2 (by rfl) ⟨6037395, by rfl⟩ : syracuseStep 16099721 = 12074791) B12074791
theorem B10733147 : Blo 2119435 10733147 := bstep (se 1 (by rfl) ⟨8049860, by rfl⟩ : syracuseStep 10733147 = 16099721) B16099721
theorem B7155431 : Blo 2119435 7155431 := bstep (se 1 (by rfl) ⟨5366573, by rfl⟩ : syracuseStep 7155431 = 10733147) B10733147
theorem B4770287 : Blo 2119435 4770287 := bstep (se 1 (by rfl) ⟨3577715, by rfl⟩ : syracuseStep 4770287 = 7155431) B7155431
theorem B3180191 : Blo 2119435 3180191 := bstep (se 1 (by rfl) ⟨2385143, by rfl⟩ : syracuseStep 3180191 = 4770287) B4770287
theorem B2120127 : Blo 2119435 2120127 := bstep (se 1 (by rfl) ⟨1590095, by rfl⟩ : syracuseStep 2120127 = 3180191) B3180191
theorem B3180197 : Blo 2119435 3180197 := bbase (se 4 (by rfl) ⟨298143, by rfl⟩ : syracuseStep 3180197 = 596287) (by norm_num)
theorem B2120131 : Blo 2119435 2120131 := bstep (se 1 (by rfl) ⟨1590098, by rfl⟩ : syracuseStep 2120131 = 3180197) B3180197
theorem B2683297 : Blo 2119435 2683297 := bbase (se 2 (by rfl) ⟨1006236, by rfl⟩ : syracuseStep 2683297 = 2012473) (by norm_num)
theorem B3577729 : Blo 2119435 3577729 := bstep (se 2 (by rfl) ⟨1341648, by rfl⟩ : syracuseStep 3577729 = 2683297) B2683297
theorem B4770305 : Blo 2119435 4770305 := bstep (se 2 (by rfl) ⟨1788864, by rfl⟩ : syracuseStep 4770305 = 3577729) B3577729
theorem B3180203 : Blo 2119435 3180203 := bstep (se 1 (by rfl) ⟨2385152, by rfl⟩ : syracuseStep 3180203 = 4770305) B4770305
theorem B2120135 : Blo 2119435 2120135 := bstep (se 1 (by rfl) ⟨1590101, by rfl⟩ : syracuseStep 2120135 = 3180203) B3180203
theorem B2385157 : Blo 2119435 2385157 := bbase (se 4 (by rfl) ⟨223608, by rfl⟩ : syracuseStep 2385157 = 447217) (by norm_num)
theorem B3180209 : Blo 2119435 3180209 := bstep (se 2 (by rfl) ⟨1192578, by rfl⟩ : syracuseStep 3180209 = 2385157) B2385157
theorem B2120139 : Blo 2119435 2120139 := bstep (se 1 (by rfl) ⟨1590104, by rfl⟩ : syracuseStep 2120139 = 3180209) B3180209
theorem B2264041 : Blo 2119435 2264041 := bbase (se 2 (by rfl) ⟨849015, by rfl⟩ : syracuseStep 2264041 = 1698031) (by norm_num)
theorem B3018721 : Blo 2119435 3018721 := bstep (se 2 (by rfl) ⟨1132020, by rfl⟩ : syracuseStep 3018721 = 2264041) B2264041
theorem B4024961 : Blo 2119435 4024961 := bstep (se 2 (by rfl) ⟨1509360, by rfl⟩ : syracuseStep 4024961 = 3018721) B3018721
theorem B2683307 : Blo 2119435 2683307 := bstep (se 1 (by rfl) ⟨2012480, by rfl⟩ : syracuseStep 2683307 = 4024961) B4024961
theorem B7155485 : Blo 2119435 7155485 := bstep (se 3 (by rfl) ⟨1341653, by rfl⟩ : syracuseStep 7155485 = 2683307) B2683307
theorem B4770323 : Blo 2119435 4770323 := bstep (se 1 (by rfl) ⟨3577742, by rfl⟩ : syracuseStep 4770323 = 7155485) B7155485
theorem B3180215 : Blo 2119435 3180215 := bstep (se 1 (by rfl) ⟨2385161, by rfl⟩ : syracuseStep 3180215 = 4770323) B4770323
theorem B2120143 : Blo 2119435 2120143 := bstep (se 1 (by rfl) ⟨1590107, by rfl⟩ : syracuseStep 2120143 = 3180215) B3180215
theorem B3180221 : Blo 2119435 3180221 := bbase (se 3 (by rfl) ⟨596291, by rfl⟩ : syracuseStep 3180221 = 1192583) (by norm_num)
theorem B2120147 : Blo 2119435 2120147 := bstep (se 1 (by rfl) ⟨1590110, by rfl⟩ : syracuseStep 2120147 = 3180221) B3180221
theorem B4770341 : Blo 2119435 4770341 := bbase (se 4 (by rfl) ⟨447219, by rfl⟩ : syracuseStep 4770341 = 894439) (by norm_num)
theorem B3180227 : Blo 2119435 3180227 := bstep (se 1 (by rfl) ⟨2385170, by rfl⟩ : syracuseStep 3180227 = 4770341) B4770341
theorem B2120151 : Blo 2119435 2120151 := bstep (se 1 (by rfl) ⟨1590113, by rfl⟩ : syracuseStep 2120151 = 3180227) B3180227
theorem B5366645 : Blo 2119435 5366645 := bbase (se 5 (by rfl) ⟨251561, by rfl⟩ : syracuseStep 5366645 = 503123) (by norm_num)
theorem B3577763 : Blo 2119435 3577763 := bstep (se 1 (by rfl) ⟨2683322, by rfl⟩ : syracuseStep 3577763 = 5366645) B5366645
theorem B2385175 : Blo 2119435 2385175 := bstep (se 1 (by rfl) ⟨1788881, by rfl⟩ : syracuseStep 2385175 = 3577763) B3577763
theorem B3180233 : Blo 2119435 3180233 := bstep (se 2 (by rfl) ⟨1192587, by rfl⟩ : syracuseStep 3180233 = 2385175) B2385175
theorem B2120155 : Blo 2119435 2120155 := bstep (se 1 (by rfl) ⟨1590116, by rfl⟩ : syracuseStep 2120155 = 3180233) B3180233
theorem B2484145 : Blo 2119435 2484145 := bbase (se 2 (by rfl) ⟨931554, by rfl⟩ : syracuseStep 2484145 = 1863109) (by norm_num)
theorem B3312193 : Blo 2119435 3312193 := bstep (se 2 (by rfl) ⟨1242072, by rfl⟩ : syracuseStep 3312193 = 2484145) B2484145
theorem B70660117 : Blo 2119435 70660117 := bstep (se 6 (by rfl) ⟨1656096, by rfl⟩ : syracuseStep 70660117 = 3312193) B3312193
theorem B94213489 : Blo 2119435 94213489 := bstep (se 2 (by rfl) ⟨35330058, by rfl⟩ : syracuseStep 94213489 = 70660117) B70660117
theorem B125617985 : Blo 2119435 125617985 := bstep (se 2 (by rfl) ⟨47106744, by rfl⟩ : syracuseStep 125617985 = 94213489) B94213489
theorem B83745323 : Blo 2119435 83745323 := bstep (se 1 (by rfl) ⟨62808992, by rfl⟩ : syracuseStep 83745323 = 125617985) B125617985
theorem B55830215 : Blo 2119435 55830215 := bstep (se 1 (by rfl) ⟨41872661, by rfl⟩ : syracuseStep 55830215 = 83745323) B83745323
theorem B37220143 : Blo 2119435 37220143 := bstep (se 1 (by rfl) ⟨27915107, by rfl⟩ : syracuseStep 37220143 = 55830215) B55830215
theorem B49626857 : Blo 2119435 49626857 := bstep (se 2 (by rfl) ⟨18610071, by rfl⟩ : syracuseStep 49626857 = 37220143) B37220143
theorem B33084571 : Blo 2119435 33084571 := bstep (se 1 (by rfl) ⟨24813428, by rfl⟩ : syracuseStep 33084571 = 49626857) B49626857
theorem B44112761 : Blo 2119435 44112761 := bstep (se 2 (by rfl) ⟨16542285, by rfl⟩ : syracuseStep 44112761 = 33084571) B33084571
theorem B29408507 : Blo 2119435 29408507 := bstep (se 1 (by rfl) ⟨22056380, by rfl⟩ : syracuseStep 29408507 = 44112761) B44112761
theorem B19605671 : Blo 2119435 19605671 := bstep (se 1 (by rfl) ⟨14704253, by rfl⟩ : syracuseStep 19605671 = 29408507) B29408507
theorem B13070447 : Blo 2119435 13070447 := bstep (se 1 (by rfl) ⟨9802835, by rfl⟩ : syracuseStep 13070447 = 19605671) B19605671
theorem B8713631 : Blo 2119435 8713631 := bstep (se 1 (by rfl) ⟨6535223, by rfl⟩ : syracuseStep 8713631 = 13070447) B13070447
theorem B5809087 : Blo 2119435 5809087 := bstep (se 1 (by rfl) ⟨4356815, by rfl⟩ : syracuseStep 5809087 = 8713631) B8713631
theorem B7745449 : Blo 2119435 7745449 := bstep (se 2 (by rfl) ⟨2904543, by rfl⟩ : syracuseStep 7745449 = 5809087) B5809087
theorem B10327265 : Blo 2119435 10327265 := bstep (se 2 (by rfl) ⟨3872724, by rfl⟩ : syracuseStep 10327265 = 7745449) B7745449
theorem B6884843 : Blo 2119435 6884843 := bstep (se 1 (by rfl) ⟨5163632, by rfl⟩ : syracuseStep 6884843 = 10327265) B10327265
theorem B18359581 : Blo 2119435 18359581 := bstep (se 3 (by rfl) ⟨3442421, by rfl⟩ : syracuseStep 18359581 = 6884843) B6884843
theorem B24479441 : Blo 2119435 24479441 := bstep (se 2 (by rfl) ⟨9179790, by rfl⟩ : syracuseStep 24479441 = 18359581) B18359581
theorem B16319627 : Blo 2119435 16319627 := bstep (se 1 (by rfl) ⟨12239720, by rfl⟩ : syracuseStep 16319627 = 24479441) B24479441
theorem B10879751 : Blo 2119435 10879751 := bstep (se 1 (by rfl) ⟨8159813, by rfl⟩ : syracuseStep 10879751 = 16319627) B16319627
theorem B7253167 : Blo 2119435 7253167 := bstep (se 1 (by rfl) ⟨5439875, by rfl⟩ : syracuseStep 7253167 = 10879751) B10879751
theorem B9670889 : Blo 2119435 9670889 := bstep (se 2 (by rfl) ⟨3626583, by rfl⟩ : syracuseStep 9670889 = 7253167) B7253167
theorem B6447259 : Blo 2119435 6447259 := bstep (se 1 (by rfl) ⟨4835444, by rfl⟩ : syracuseStep 6447259 = 9670889) B9670889
theorem B34385381 : Blo 2119435 34385381 := bstep (se 4 (by rfl) ⟨3223629, by rfl⟩ : syracuseStep 34385381 = 6447259) B6447259
theorem B22923587 : Blo 2119435 22923587 := bstep (se 1 (by rfl) ⟨17192690, by rfl⟩ : syracuseStep 22923587 = 34385381) B34385381
theorem B15282391 : Blo 2119435 15282391 := bstep (se 1 (by rfl) ⟨11461793, by rfl⟩ : syracuseStep 15282391 = 22923587) B22923587
theorem B20376521 : Blo 2119435 20376521 := bstep (se 2 (by rfl) ⟨7641195, by rfl⟩ : syracuseStep 20376521 = 15282391) B15282391
theorem B13584347 : Blo 2119435 13584347 := bstep (se 1 (by rfl) ⟨10188260, by rfl⟩ : syracuseStep 13584347 = 20376521) B20376521
theorem B9056231 : Blo 2119435 9056231 := bstep (se 1 (by rfl) ⟨6792173, by rfl⟩ : syracuseStep 9056231 = 13584347) B13584347
theorem B6037487 : Blo 2119435 6037487 := bstep (se 1 (by rfl) ⟨4528115, by rfl⟩ : syracuseStep 6037487 = 9056231) B9056231
theorem B4024991 : Blo 2119435 4024991 := bstep (se 1 (by rfl) ⟨3018743, by rfl⟩ : syracuseStep 4024991 = 6037487) B6037487
theorem B10733309 : Blo 2119435 10733309 := bstep (se 3 (by rfl) ⟨2012495, by rfl⟩ : syracuseStep 10733309 = 4024991) B4024991
theorem B7155539 : Blo 2119435 7155539 := bstep (se 1 (by rfl) ⟨5366654, by rfl⟩ : syracuseStep 7155539 = 10733309) B10733309
theorem B4770359 : Blo 2119435 4770359 := bstep (se 1 (by rfl) ⟨3577769, by rfl⟩ : syracuseStep 4770359 = 7155539) B7155539
theorem B3180239 : Blo 2119435 3180239 := bstep (se 1 (by rfl) ⟨2385179, by rfl⟩ : syracuseStep 3180239 = 4770359) B4770359
theorem B2120159 : Blo 2119435 2120159 := bstep (se 1 (by rfl) ⟨1590119, by rfl⟩ : syracuseStep 2120159 = 3180239) B3180239
theorem B3180245 : Blo 2119435 3180245 := bbase (se 7 (by rfl) ⟨37268, by rfl⟩ : syracuseStep 3180245 = 74537) (by norm_num)
theorem B2120163 : Blo 2119435 2120163 := bstep (se 1 (by rfl) ⟨1590122, by rfl⟩ : syracuseStep 2120163 = 3180245) B3180245
theorem B4528133 : Blo 2119435 4528133 := bbase (se 4 (by rfl) ⟨424512, by rfl⟩ : syracuseStep 4528133 = 849025) (by norm_num)
theorem B3018755 : Blo 2119435 3018755 := bstep (se 1 (by rfl) ⟨2264066, by rfl⟩ : syracuseStep 3018755 = 4528133) B4528133
theorem B8050013 : Blo 2119435 8050013 := bstep (se 3 (by rfl) ⟨1509377, by rfl⟩ : syracuseStep 8050013 = 3018755) B3018755
theorem B5366675 : Blo 2119435 5366675 := bstep (se 1 (by rfl) ⟨4025006, by rfl⟩ : syracuseStep 5366675 = 8050013) B8050013
theorem B3577783 : Blo 2119435 3577783 := bstep (se 1 (by rfl) ⟨2683337, by rfl⟩ : syracuseStep 3577783 = 5366675) B5366675
theorem B4770377 : Blo 2119435 4770377 := bstep (se 2 (by rfl) ⟨1788891, by rfl⟩ : syracuseStep 4770377 = 3577783) B3577783
theorem B3180251 : Blo 2119435 3180251 := bstep (se 1 (by rfl) ⟨2385188, by rfl⟩ : syracuseStep 3180251 = 4770377) B4770377
theorem B2120167 : Blo 2119435 2120167 := bstep (se 1 (by rfl) ⟨1590125, by rfl⟩ : syracuseStep 2120167 = 3180251) B3180251
theorem B2385193 : Blo 2119435 2385193 := bbase (se 2 (by rfl) ⟨894447, by rfl⟩ : syracuseStep 2385193 = 1788895) (by norm_num)
theorem B3180257 : Blo 2119435 3180257 := bstep (se 2 (by rfl) ⟨1192596, by rfl⟩ : syracuseStep 3180257 = 2385193) B2385193
theorem B2120171 : Blo 2119435 2120171 := bstep (se 1 (by rfl) ⟨1590128, by rfl⟩ : syracuseStep 2120171 = 3180257) B3180257
theorem B7641253 : Blo 2119435 7641253 := bbase (se 4 (by rfl) ⟨716367, by rfl⟩ : syracuseStep 7641253 = 1432735) (by norm_num)
theorem B10188337 : Blo 2119435 10188337 := bstep (se 2 (by rfl) ⟨3820626, by rfl⟩ : syracuseStep 10188337 = 7641253) B7641253
theorem B13584449 : Blo 2119435 13584449 := bstep (se 2 (by rfl) ⟨5094168, by rfl⟩ : syracuseStep 13584449 = 10188337) B10188337
theorem B9056299 : Blo 2119435 9056299 := bstep (se 1 (by rfl) ⟨6792224, by rfl⟩ : syracuseStep 9056299 = 13584449) B13584449
theorem B12075065 : Blo 2119435 12075065 := bstep (se 2 (by rfl) ⟨4528149, by rfl⟩ : syracuseStep 12075065 = 9056299) B9056299
theorem B8050043 : Blo 2119435 8050043 := bstep (se 1 (by rfl) ⟨6037532, by rfl⟩ : syracuseStep 8050043 = 12075065) B12075065
theorem B5366695 : Blo 2119435 5366695 := bstep (se 1 (by rfl) ⟨4025021, by rfl⟩ : syracuseStep 5366695 = 8050043) B8050043
theorem B7155593 : Blo 2119435 7155593 := bstep (se 2 (by rfl) ⟨2683347, by rfl⟩ : syracuseStep 7155593 = 5366695) B5366695
theorem B4770395 : Blo 2119435 4770395 := bstep (se 1 (by rfl) ⟨3577796, by rfl⟩ : syracuseStep 4770395 = 7155593) B7155593
theorem B3180263 : Blo 2119435 3180263 := bstep (se 1 (by rfl) ⟨2385197, by rfl⟩ : syracuseStep 3180263 = 4770395) B4770395
theorem B2120175 : Blo 2119435 2120175 := bstep (se 1 (by rfl) ⟨1590131, by rfl⟩ : syracuseStep 2120175 = 3180263) B3180263
theorem B3180269 : Blo 2119435 3180269 := bbase (se 3 (by rfl) ⟨596300, by rfl⟩ : syracuseStep 3180269 = 1192601) (by norm_num)
theorem B2120179 : Blo 2119435 2120179 := bstep (se 1 (by rfl) ⟨1590134, by rfl⟩ : syracuseStep 2120179 = 3180269) B3180269
theorem B4770413 : Blo 2119435 4770413 := bbase (se 3 (by rfl) ⟨894452, by rfl⟩ : syracuseStep 4770413 = 1788905) (by norm_num)
theorem B3180275 : Blo 2119435 3180275 := bstep (se 1 (by rfl) ⟨2385206, by rfl⟩ : syracuseStep 3180275 = 4770413) B4770413
theorem B2120183 : Blo 2119435 2120183 := bstep (se 1 (by rfl) ⟨1590137, by rfl⟩ : syracuseStep 2120183 = 3180275) B3180275
theorem B4025045 : Blo 2119435 4025045 := bbase (se 7 (by rfl) ⟨47168, by rfl⟩ : syracuseStep 4025045 = 94337) (by norm_num)
theorem B2683363 : Blo 2119435 2683363 := bstep (se 1 (by rfl) ⟨2012522, by rfl⟩ : syracuseStep 2683363 = 4025045) B4025045
theorem B3577817 : Blo 2119435 3577817 := bstep (se 2 (by rfl) ⟨1341681, by rfl⟩ : syracuseStep 3577817 = 2683363) B2683363
theorem B2385211 : Blo 2119435 2385211 := bstep (se 1 (by rfl) ⟨1788908, by rfl⟩ : syracuseStep 2385211 = 3577817) B3577817
theorem B3180281 : Blo 2119435 3180281 := bstep (se 2 (by rfl) ⟨1192605, by rfl⟩ : syracuseStep 3180281 = 2385211) B2385211
theorem B2120187 : Blo 2119435 2120187 := bstep (se 1 (by rfl) ⟨1590140, by rfl⟩ : syracuseStep 2120187 = 3180281) B3180281
theorem B4033469 : Blo 2119435 4033469 := bbase (se 3 (by rfl) ⟨756275, by rfl⟩ : syracuseStep 4033469 = 1512551) (by norm_num)
theorem B10755917 : Blo 2119435 10755917 := bstep (se 3 (by rfl) ⟨2016734, by rfl⟩ : syracuseStep 10755917 = 4033469) B4033469
theorem B7170611 : Blo 2119435 7170611 := bstep (se 1 (by rfl) ⟨5377958, by rfl⟩ : syracuseStep 7170611 = 10755917) B10755917
theorem B19121629 : Blo 2119435 19121629 := bstep (se 3 (by rfl) ⟨3585305, by rfl⟩ : syracuseStep 19121629 = 7170611) B7170611
theorem B25495505 : Blo 2119435 25495505 := bstep (se 2 (by rfl) ⟨9560814, by rfl⟩ : syracuseStep 25495505 = 19121629) B19121629
theorem B16997003 : Blo 2119435 16997003 := bstep (se 1 (by rfl) ⟨12747752, by rfl⟩ : syracuseStep 16997003 = 25495505) B25495505
theorem B11331335 : Blo 2119435 11331335 := bstep (se 1 (by rfl) ⟨8498501, by rfl⟩ : syracuseStep 11331335 = 16997003) B16997003
theorem B7554223 : Blo 2119435 7554223 := bstep (se 1 (by rfl) ⟨5665667, by rfl⟩ : syracuseStep 7554223 = 11331335) B11331335
theorem B10072297 : Blo 2119435 10072297 := bstep (se 2 (by rfl) ⟨3777111, by rfl⟩ : syracuseStep 10072297 = 7554223) B7554223
theorem B13429729 : Blo 2119435 13429729 := bstep (se 2 (by rfl) ⟨5036148, by rfl⟩ : syracuseStep 13429729 = 10072297) B10072297
theorem B71625221 : Blo 2119435 71625221 := bstep (se 4 (by rfl) ⟨6714864, by rfl⟩ : syracuseStep 71625221 = 13429729) B13429729
theorem B47750147 : Blo 2119435 47750147 := bstep (se 1 (by rfl) ⟨35812610, by rfl⟩ : syracuseStep 47750147 = 71625221) B71625221
theorem B31833431 : Blo 2119435 31833431 := bstep (se 1 (by rfl) ⟨23875073, by rfl⟩ : syracuseStep 31833431 = 47750147) B47750147
theorem B21222287 : Blo 2119435 21222287 := bstep (se 1 (by rfl) ⟨15916715, by rfl⟩ : syracuseStep 21222287 = 31833431) B31833431
theorem B14148191 : Blo 2119435 14148191 := bstep (se 1 (by rfl) ⟨10611143, by rfl⟩ : syracuseStep 14148191 = 21222287) B21222287
theorem B9432127 : Blo 2119435 9432127 := bstep (se 1 (by rfl) ⟨7074095, by rfl⟩ : syracuseStep 9432127 = 14148191) B14148191
theorem B12576169 : Blo 2119435 12576169 := bstep (se 2 (by rfl) ⟨4716063, by rfl⟩ : syracuseStep 12576169 = 9432127) B9432127
theorem B16768225 : Blo 2119435 16768225 := bstep (se 2 (by rfl) ⟨6288084, by rfl⟩ : syracuseStep 16768225 = 12576169) B12576169
theorem B22357633 : Blo 2119435 22357633 := bstep (se 2 (by rfl) ⟨8384112, by rfl⟩ : syracuseStep 22357633 = 16768225) B16768225
theorem B29810177 : Blo 2119435 29810177 := bstep (se 2 (by rfl) ⟨11178816, by rfl⟩ : syracuseStep 29810177 = 22357633) B22357633
theorem B19873451 : Blo 2119435 19873451 := bstep (se 1 (by rfl) ⟨14905088, by rfl⟩ : syracuseStep 19873451 = 29810177) B29810177
theorem B52995869 : Blo 2119435 52995869 := bstep (se 3 (by rfl) ⟨9936725, by rfl⟩ : syracuseStep 52995869 = 19873451) B19873451
theorem B35330579 : Blo 2119435 35330579 := bstep (se 1 (by rfl) ⟨26497934, by rfl⟩ : syracuseStep 35330579 = 52995869) B52995869
theorem B23553719 : Blo 2119435 23553719 := bstep (se 1 (by rfl) ⟨17665289, by rfl⟩ : syracuseStep 23553719 = 35330579) B35330579
theorem B15702479 : Blo 2119435 15702479 := bstep (se 1 (by rfl) ⟨11776859, by rfl⟩ : syracuseStep 15702479 = 23553719) B23553719
theorem B10468319 : Blo 2119435 10468319 := bstep (se 1 (by rfl) ⟨7851239, by rfl⟩ : syracuseStep 10468319 = 15702479) B15702479
theorem B111662069 : Blo 2119435 111662069 := bstep (se 5 (by rfl) ⟨5234159, by rfl⟩ : syracuseStep 111662069 = 10468319) B10468319
theorem B297765517 : Blo 2119435 297765517 := bstep (se 3 (by rfl) ⟨55831034, by rfl⟩ : syracuseStep 297765517 = 111662069) B111662069
theorem B397020689 : Blo 2119435 397020689 := bstep (se 2 (by rfl) ⟨148882758, by rfl⟩ : syracuseStep 397020689 = 297765517) B297765517
theorem B264680459 : Blo 2119435 264680459 := bstep (se 1 (by rfl) ⟨198510344, by rfl⟩ : syracuseStep 264680459 = 397020689) B397020689
theorem B176453639 : Blo 2119435 176453639 := bstep (se 1 (by rfl) ⟨132340229, by rfl⟩ : syracuseStep 176453639 = 264680459) B264680459
theorem B117635759 : Blo 2119435 117635759 := bstep (se 1 (by rfl) ⟨88226819, by rfl⟩ : syracuseStep 117635759 = 176453639) B176453639
theorem B78423839 : Blo 2119435 78423839 := bstep (se 1 (by rfl) ⟨58817879, by rfl⟩ : syracuseStep 78423839 = 117635759) B117635759
theorem B52282559 : Blo 2119435 52282559 := bstep (se 1 (by rfl) ⟨39211919, by rfl⟩ : syracuseStep 52282559 = 78423839) B78423839
theorem B34855039 : Blo 2119435 34855039 := bstep (se 1 (by rfl) ⟨26141279, by rfl⟩ : syracuseStep 34855039 = 52282559) B52282559
theorem B46473385 : Blo 2119435 46473385 := bstep (se 2 (by rfl) ⟨17427519, by rfl⟩ : syracuseStep 46473385 = 34855039) B34855039
theorem B61964513 : Blo 2119435 61964513 := bstep (se 2 (by rfl) ⟨23236692, by rfl⟩ : syracuseStep 61964513 = 46473385) B46473385
theorem B41309675 : Blo 2119435 41309675 := bstep (se 1 (by rfl) ⟨30982256, by rfl⟩ : syracuseStep 41309675 = 61964513) B61964513
theorem B27539783 : Blo 2119435 27539783 := bstep (se 1 (by rfl) ⟨20654837, by rfl⟩ : syracuseStep 27539783 = 41309675) B41309675
theorem B18359855 : Blo 2119435 18359855 := bstep (se 1 (by rfl) ⟨13769891, by rfl⟩ : syracuseStep 18359855 = 27539783) B27539783
theorem B12239903 : Blo 2119435 12239903 := bstep (se 1 (by rfl) ⟨9179927, by rfl⟩ : syracuseStep 12239903 = 18359855) B18359855
theorem B8159935 : Blo 2119435 8159935 := bstep (se 1 (by rfl) ⟨6119951, by rfl⟩ : syracuseStep 8159935 = 12239903) B12239903
theorem B10879913 : Blo 2119435 10879913 := bstep (se 2 (by rfl) ⟨4079967, by rfl⟩ : syracuseStep 10879913 = 8159935) B8159935
theorem B7253275 : Blo 2119435 7253275 := bstep (se 1 (by rfl) ⟨5439956, by rfl⟩ : syracuseStep 7253275 = 10879913) B10879913
theorem B9671033 : Blo 2119435 9671033 := bstep (se 2 (by rfl) ⟨3626637, by rfl⟩ : syracuseStep 9671033 = 7253275) B7253275
theorem B25789421 : Blo 2119435 25789421 := bstep (se 3 (by rfl) ⟨4835516, by rfl⟩ : syracuseStep 25789421 = 9671033) B9671033
theorem B17192947 : Blo 2119435 17192947 := bstep (se 1 (by rfl) ⟨12894710, by rfl⟩ : syracuseStep 17192947 = 25789421) B25789421
theorem B22923929 : Blo 2119435 22923929 := bstep (se 2 (by rfl) ⟨8596473, by rfl⟩ : syracuseStep 22923929 = 17192947) B17192947
theorem B61130477 : Blo 2119435 61130477 := bstep (se 3 (by rfl) ⟨11461964, by rfl⟩ : syracuseStep 61130477 = 22923929) B22923929
theorem B40753651 : Blo 2119435 40753651 := bstep (se 1 (by rfl) ⟨30565238, by rfl⟩ : syracuseStep 40753651 = 61130477) B61130477
theorem B54338201 : Blo 2119435 54338201 := bstep (se 2 (by rfl) ⟨20376825, by rfl⟩ : syracuseStep 54338201 = 40753651) B40753651
theorem B36225467 : Blo 2119435 36225467 := bstep (se 1 (by rfl) ⟨27169100, by rfl⟩ : syracuseStep 36225467 = 54338201) B54338201
theorem B24150311 : Blo 2119435 24150311 := bstep (se 1 (by rfl) ⟨18112733, by rfl⟩ : syracuseStep 24150311 = 36225467) B36225467
theorem B16100207 : Blo 2119435 16100207 := bstep (se 1 (by rfl) ⟨12075155, by rfl⟩ : syracuseStep 16100207 = 24150311) B24150311
theorem B10733471 : Blo 2119435 10733471 := bstep (se 1 (by rfl) ⟨8050103, by rfl⟩ : syracuseStep 10733471 = 16100207) B16100207
theorem B7155647 : Blo 2119435 7155647 := bstep (se 1 (by rfl) ⟨5366735, by rfl⟩ : syracuseStep 7155647 = 10733471) B10733471
theorem B4770431 : Blo 2119435 4770431 := bstep (se 1 (by rfl) ⟨3577823, by rfl⟩ : syracuseStep 4770431 = 7155647) B7155647
theorem B3180287 : Blo 2119435 3180287 := bstep (se 1 (by rfl) ⟨2385215, by rfl⟩ : syracuseStep 3180287 = 4770431) B4770431
theorem B2120191 : Blo 2119435 2120191 := bstep (se 1 (by rfl) ⟨1590143, by rfl⟩ : syracuseStep 2120191 = 3180287) B3180287
theorem B3180293 : Blo 2119435 3180293 := bbase (se 4 (by rfl) ⟨298152, by rfl⟩ : syracuseStep 3180293 = 596305) (by norm_num)
theorem B2120195 : Blo 2119435 2120195 := bstep (se 1 (by rfl) ⟨1590146, by rfl⟩ : syracuseStep 2120195 = 3180293) B3180293
theorem B3577837 : Blo 2119435 3577837 := bbase (se 3 (by rfl) ⟨670844, by rfl⟩ : syracuseStep 3577837 = 1341689) (by norm_num)
theorem B4770449 : Blo 2119435 4770449 := bstep (se 2 (by rfl) ⟨1788918, by rfl⟩ : syracuseStep 4770449 = 3577837) B3577837
theorem B3180299 : Blo 2119435 3180299 := bstep (se 1 (by rfl) ⟨2385224, by rfl⟩ : syracuseStep 3180299 = 4770449) B4770449
theorem B2120199 : Blo 2119435 2120199 := bstep (se 1 (by rfl) ⟨1590149, by rfl⟩ : syracuseStep 2120199 = 3180299) B3180299
theorem B2385229 : Blo 2119435 2385229 := bbase (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) (by norm_num)
theorem B3180305 : Blo 2119435 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B2120203 : Blo 2119435 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B7155701 : Blo 2119435 7155701 := bbase (se 5 (by rfl) ⟨335423, by rfl⟩ : syracuseStep 7155701 = 670847) (by norm_num)
theorem B4770467 : Blo 2119435 4770467 := bstep (se 1 (by rfl) ⟨3577850, by rfl⟩ : syracuseStep 4770467 = 7155701) B7155701
theorem B3180311 : Blo 2119435 3180311 := bstep (se 1 (by rfl) ⟨2385233, by rfl⟩ : syracuseStep 3180311 = 4770467) B4770467
theorem B2120207 : Blo 2119435 2120207 := bstep (se 1 (by rfl) ⟨1590155, by rfl⟩ : syracuseStep 2120207 = 3180311) B3180311
theorem B3180317 : Blo 2119435 3180317 := bbase (se 3 (by rfl) ⟨596309, by rfl⟩ : syracuseStep 3180317 = 1192619) (by norm_num)
theorem B2120211 : Blo 2119435 2120211 := bstep (se 1 (by rfl) ⟨1590158, by rfl⟩ : syracuseStep 2120211 = 3180317) B3180317
theorem B4770485 : Blo 2119435 4770485 := bbase (se 5 (by rfl) ⟨223616, by rfl⟩ : syracuseStep 4770485 = 447233) (by norm_num)
theorem B3180323 : Blo 2119435 3180323 := bstep (se 1 (by rfl) ⟨2385242, by rfl⟩ : syracuseStep 3180323 = 4770485) B4770485
theorem B2120215 : Blo 2119435 2120215 := bstep (se 1 (by rfl) ⟨1590161, by rfl⟩ : syracuseStep 2120215 = 3180323) B3180323
theorem B12075317 : Blo 2119435 12075317 := bbase (se 5 (by rfl) ⟨566030, by rfl⟩ : syracuseStep 12075317 = 1132061) (by norm_num)
theorem B8050211 : Blo 2119435 8050211 := bstep (se 1 (by rfl) ⟨6037658, by rfl⟩ : syracuseStep 8050211 = 12075317) B12075317
theorem B5366807 : Blo 2119435 5366807 := bstep (se 1 (by rfl) ⟨4025105, by rfl⟩ : syracuseStep 5366807 = 8050211) B8050211
theorem B3577871 : Blo 2119435 3577871 := bstep (se 1 (by rfl) ⟨2683403, by rfl⟩ : syracuseStep 3577871 = 5366807) B5366807
theorem B2385247 : Blo 2119435 2385247 := bstep (se 1 (by rfl) ⟨1788935, by rfl⟩ : syracuseStep 2385247 = 3577871) B3577871
theorem B3180329 : Blo 2119435 3180329 := bstep (se 2 (by rfl) ⟨1192623, by rfl⟩ : syracuseStep 3180329 = 2385247) B2385247
theorem B2120219 : Blo 2119435 2120219 := bstep (se 1 (by rfl) ⟨1590164, by rfl⟩ : syracuseStep 2120219 = 3180329) B3180329
theorem B6037669 : Blo 2119435 6037669 := bbase (se 4 (by rfl) ⟨566031, by rfl⟩ : syracuseStep 6037669 = 1132063) (by norm_num)
theorem B8050225 : Blo 2119435 8050225 := bstep (se 2 (by rfl) ⟨3018834, by rfl⟩ : syracuseStep 8050225 = 6037669) B6037669
theorem B10733633 : Blo 2119435 10733633 := bstep (se 2 (by rfl) ⟨4025112, by rfl⟩ : syracuseStep 10733633 = 8050225) B8050225
theorem B7155755 : Blo 2119435 7155755 := bstep (se 1 (by rfl) ⟨5366816, by rfl⟩ : syracuseStep 7155755 = 10733633) B10733633
theorem B4770503 : Blo 2119435 4770503 := bstep (se 1 (by rfl) ⟨3577877, by rfl⟩ : syracuseStep 4770503 = 7155755) B7155755
theorem B3180335 : Blo 2119435 3180335 := bstep (se 1 (by rfl) ⟨2385251, by rfl⟩ : syracuseStep 3180335 = 4770503) B4770503
theorem B2120223 : Blo 2119435 2120223 := bstep (se 1 (by rfl) ⟨1590167, by rfl⟩ : syracuseStep 2120223 = 3180335) B3180335
theorem B3180341 : Blo 2119435 3180341 := bbase (se 5 (by rfl) ⟨149078, by rfl⟩ : syracuseStep 3180341 = 298157) (by norm_num)
theorem B2120227 : Blo 2119435 2120227 := bstep (se 1 (by rfl) ⟨1590170, by rfl⟩ : syracuseStep 2120227 = 3180341) B3180341
theorem B5366837 : Blo 2119435 5366837 := bbase (se 5 (by rfl) ⟨251570, by rfl⟩ : syracuseStep 5366837 = 503141) (by norm_num)
theorem B3577891 : Blo 2119435 3577891 := bstep (se 1 (by rfl) ⟨2683418, by rfl⟩ : syracuseStep 3577891 = 5366837) B5366837
theorem B4770521 : Blo 2119435 4770521 := bstep (se 2 (by rfl) ⟨1788945, by rfl⟩ : syracuseStep 4770521 = 3577891) B3577891
theorem B3180347 : Blo 2119435 3180347 := bstep (se 1 (by rfl) ⟨2385260, by rfl⟩ : syracuseStep 3180347 = 4770521) B4770521
theorem B2120231 : Blo 2119435 2120231 := bstep (se 1 (by rfl) ⟨1590173, by rfl⟩ : syracuseStep 2120231 = 3180347) B3180347
theorem B2385265 : Blo 2119435 2385265 := bbase (se 2 (by rfl) ⟨894474, by rfl⟩ : syracuseStep 2385265 = 1788949) (by norm_num)
theorem B3180353 : Blo 2119435 3180353 := bstep (se 2 (by rfl) ⟨1192632, by rfl⟩ : syracuseStep 3180353 = 2385265) B2385265
theorem B2120235 : Blo 2119435 2120235 := bstep (se 1 (by rfl) ⟨1590176, by rfl⟩ : syracuseStep 2120235 = 3180353) B3180353
theorem B2865557 : Blo 2119435 2865557 := bbase (se 6 (by rfl) ⟨67161, by rfl⟩ : syracuseStep 2865557 = 134323) (by norm_num)
theorem B7641485 : Blo 2119435 7641485 := bstep (se 3 (by rfl) ⟨1432778, by rfl⟩ : syracuseStep 7641485 = 2865557) B2865557
theorem B5094323 : Blo 2119435 5094323 := bstep (se 1 (by rfl) ⟨3820742, by rfl⟩ : syracuseStep 5094323 = 7641485) B7641485
theorem B3396215 : Blo 2119435 3396215 := bstep (se 1 (by rfl) ⟨2547161, by rfl⟩ : syracuseStep 3396215 = 5094323) B5094323
theorem B9056573 : Blo 2119435 9056573 := bstep (se 3 (by rfl) ⟨1698107, by rfl⟩ : syracuseStep 9056573 = 3396215) B3396215
theorem B6037715 : Blo 2119435 6037715 := bstep (se 1 (by rfl) ⟨4528286, by rfl⟩ : syracuseStep 6037715 = 9056573) B9056573
theorem B4025143 : Blo 2119435 4025143 := bstep (se 1 (by rfl) ⟨3018857, by rfl⟩ : syracuseStep 4025143 = 6037715) B6037715
theorem B5366857 : Blo 2119435 5366857 := bstep (se 2 (by rfl) ⟨2012571, by rfl⟩ : syracuseStep 5366857 = 4025143) B4025143
theorem B7155809 : Blo 2119435 7155809 := bstep (se 2 (by rfl) ⟨2683428, by rfl⟩ : syracuseStep 7155809 = 5366857) B5366857
theorem B4770539 : Blo 2119435 4770539 := bstep (se 1 (by rfl) ⟨3577904, by rfl⟩ : syracuseStep 4770539 = 7155809) B7155809
theorem B3180359 : Blo 2119435 3180359 := bstep (se 1 (by rfl) ⟨2385269, by rfl⟩ : syracuseStep 3180359 = 4770539) B4770539
theorem B2120239 : Blo 2119435 2120239 := bstep (se 1 (by rfl) ⟨1590179, by rfl⟩ : syracuseStep 2120239 = 3180359) B3180359
theorem B3180365 : Blo 2119435 3180365 := bbase (se 3 (by rfl) ⟨596318, by rfl⟩ : syracuseStep 3180365 = 1192637) (by norm_num)
theorem B2120243 : Blo 2119435 2120243 := bstep (se 1 (by rfl) ⟨1590182, by rfl⟩ : syracuseStep 2120243 = 3180365) B3180365
theorem B4770557 : Blo 2119435 4770557 := bbase (se 3 (by rfl) ⟨894479, by rfl⟩ : syracuseStep 4770557 = 1788959) (by norm_num)
theorem B3180371 : Blo 2119435 3180371 := bstep (se 1 (by rfl) ⟨2385278, by rfl⟩ : syracuseStep 3180371 = 4770557) B4770557
theorem B2120247 : Blo 2119435 2120247 := bstep (se 1 (by rfl) ⟨1590185, by rfl⟩ : syracuseStep 2120247 = 3180371) B3180371
theorem B3577925 : Blo 2119435 3577925 := bbase (se 4 (by rfl) ⟨335430, by rfl⟩ : syracuseStep 3577925 = 670861) (by norm_num)
theorem B2385283 : Blo 2119435 2385283 := bstep (se 1 (by rfl) ⟨1788962, by rfl⟩ : syracuseStep 2385283 = 3577925) B3577925
theorem B3180377 : Blo 2119435 3180377 := bstep (se 2 (by rfl) ⟨1192641, by rfl⟩ : syracuseStep 3180377 = 2385283) B2385283
theorem B2120251 : Blo 2119435 2120251 := bstep (se 1 (by rfl) ⟨1590188, by rfl⟩ : syracuseStep 2120251 = 3180377) B3180377
theorem B16100693 : Blo 2119435 16100693 := bbase (se 11 (by rfl) ⟨11792, by rfl⟩ : syracuseStep 16100693 = 23585) (by norm_num)
theorem B10733795 : Blo 2119435 10733795 := bstep (se 1 (by rfl) ⟨8050346, by rfl⟩ : syracuseStep 10733795 = 16100693) B16100693
theorem B7155863 : Blo 2119435 7155863 := bstep (se 1 (by rfl) ⟨5366897, by rfl⟩ : syracuseStep 7155863 = 10733795) B10733795
theorem B4770575 : Blo 2119435 4770575 := bstep (se 1 (by rfl) ⟨3577931, by rfl⟩ : syracuseStep 4770575 = 7155863) B7155863
theorem B3180383 : Blo 2119435 3180383 := bstep (se 1 (by rfl) ⟨2385287, by rfl⟩ : syracuseStep 3180383 = 4770575) B4770575
theorem B2120255 : Blo 2119435 2120255 := bstep (se 1 (by rfl) ⟨1590191, by rfl⟩ : syracuseStep 2120255 = 3180383) B3180383
theorem B3180389 : Blo 2119435 3180389 := bbase (se 4 (by rfl) ⟨298161, by rfl⟩ : syracuseStep 3180389 = 596323) (by norm_num)
theorem B2120259 : Blo 2119435 2120259 := bstep (se 1 (by rfl) ⟨1590194, by rfl⟩ : syracuseStep 2120259 = 3180389) B3180389
theorem B4025189 : Blo 2119435 4025189 := bbase (se 4 (by rfl) ⟨377361, by rfl⟩ : syracuseStep 4025189 = 754723) (by norm_num)
theorem B2683459 : Blo 2119435 2683459 := bstep (se 1 (by rfl) ⟨2012594, by rfl⟩ : syracuseStep 2683459 = 4025189) B4025189
theorem B3577945 : Blo 2119435 3577945 := bstep (se 2 (by rfl) ⟨1341729, by rfl⟩ : syracuseStep 3577945 = 2683459) B2683459
theorem B4770593 : Blo 2119435 4770593 := bstep (se 2 (by rfl) ⟨1788972, by rfl⟩ : syracuseStep 4770593 = 3577945) B3577945
theorem B3180395 : Blo 2119435 3180395 := bstep (se 1 (by rfl) ⟨2385296, by rfl⟩ : syracuseStep 3180395 = 4770593) B4770593
theorem B2120263 : Blo 2119435 2120263 := bstep (se 1 (by rfl) ⟨1590197, by rfl⟩ : syracuseStep 2120263 = 3180395) B3180395
theorem B2385301 : Blo 2119435 2385301 := bbase (se 6 (by rfl) ⟨55905, by rfl⟩ : syracuseStep 2385301 = 111811) (by norm_num)
theorem B3180401 : Blo 2119435 3180401 := bstep (se 2 (by rfl) ⟨1192650, by rfl⟩ : syracuseStep 3180401 = 2385301) B2385301
theorem B2120267 : Blo 2119435 2120267 := bstep (se 1 (by rfl) ⟨1590200, by rfl⟩ : syracuseStep 2120267 = 3180401) B3180401
theorem B2683469 : Blo 2119435 2683469 := bbase (se 3 (by rfl) ⟨503150, by rfl⟩ : syracuseStep 2683469 = 1006301) (by norm_num)
theorem B7155917 : Blo 2119435 7155917 := bstep (se 3 (by rfl) ⟨1341734, by rfl⟩ : syracuseStep 7155917 = 2683469) B2683469
theorem B4770611 : Blo 2119435 4770611 := bstep (se 1 (by rfl) ⟨3577958, by rfl⟩ : syracuseStep 4770611 = 7155917) B7155917
theorem B3180407 : Blo 2119435 3180407 := bstep (se 1 (by rfl) ⟨2385305, by rfl⟩ : syracuseStep 3180407 = 4770611) B4770611
theorem B2120271 : Blo 2119435 2120271 := bstep (se 1 (by rfl) ⟨1590203, by rfl⟩ : syracuseStep 2120271 = 3180407) B3180407
theorem B3180413 : Blo 2119435 3180413 := bbase (se 3 (by rfl) ⟨596327, by rfl⟩ : syracuseStep 3180413 = 1192655) (by norm_num)
theorem B2120275 : Blo 2119435 2120275 := bstep (se 1 (by rfl) ⟨1590206, by rfl⟩ : syracuseStep 2120275 = 3180413) B3180413
theorem B4770629 : Blo 2119435 4770629 := bbase (se 4 (by rfl) ⟨447246, by rfl⟩ : syracuseStep 4770629 = 894493) (by norm_num)
theorem B3180419 : Blo 2119435 3180419 := bstep (se 1 (by rfl) ⟨2385314, by rfl⟩ : syracuseStep 3180419 = 4770629) B4770629
theorem B2120279 : Blo 2119435 2120279 := bstep (se 1 (by rfl) ⟨1590209, by rfl⟩ : syracuseStep 2120279 = 3180419) B3180419
theorem B4528381 : Blo 2119435 4528381 := bbase (se 3 (by rfl) ⟨849071, by rfl⟩ : syracuseStep 4528381 = 1698143) (by norm_num)
theorem B6037841 : Blo 2119435 6037841 := bstep (se 2 (by rfl) ⟨2264190, by rfl⟩ : syracuseStep 6037841 = 4528381) B4528381
theorem B4025227 : Blo 2119435 4025227 := bstep (se 1 (by rfl) ⟨3018920, by rfl⟩ : syracuseStep 4025227 = 6037841) B6037841
theorem B5366969 : Blo 2119435 5366969 := bstep (se 2 (by rfl) ⟨2012613, by rfl⟩ : syracuseStep 5366969 = 4025227) B4025227
theorem B3577979 : Blo 2119435 3577979 := bstep (se 1 (by rfl) ⟨2683484, by rfl⟩ : syracuseStep 3577979 = 5366969) B5366969
theorem B2385319 : Blo 2119435 2385319 := bstep (se 1 (by rfl) ⟨1788989, by rfl⟩ : syracuseStep 2385319 = 3577979) B3577979
theorem B3180425 : Blo 2119435 3180425 := bstep (se 2 (by rfl) ⟨1192659, by rfl⟩ : syracuseStep 3180425 = 2385319) B2385319
theorem B2120283 : Blo 2119435 2120283 := bstep (se 1 (by rfl) ⟨1590212, by rfl⟩ : syracuseStep 2120283 = 3180425) B3180425
theorem B10733957 : Blo 2119435 10733957 := bbase (se 4 (by rfl) ⟨1006308, by rfl⟩ : syracuseStep 10733957 = 2012617) (by norm_num)
theorem B7155971 : Blo 2119435 7155971 := bstep (se 1 (by rfl) ⟨5366978, by rfl⟩ : syracuseStep 7155971 = 10733957) B10733957
theorem B4770647 : Blo 2119435 4770647 := bstep (se 1 (by rfl) ⟨3577985, by rfl⟩ : syracuseStep 4770647 = 7155971) B7155971
theorem B3180431 : Blo 2119435 3180431 := bstep (se 1 (by rfl) ⟨2385323, by rfl⟩ : syracuseStep 3180431 = 4770647) B4770647
theorem B2120287 : Blo 2119435 2120287 := bstep (se 1 (by rfl) ⟨1590215, by rfl⟩ : syracuseStep 2120287 = 3180431) B3180431
theorem B3180437 : Blo 2119435 3180437 := bbase (se 6 (by rfl) ⟨74541, by rfl⟩ : syracuseStep 3180437 = 149083) (by norm_num)
theorem B2120291 : Blo 2119435 2120291 := bstep (se 1 (by rfl) ⟨1590218, by rfl⟩ : syracuseStep 2120291 = 3180437) B3180437
theorem B2547229 : Blo 2119435 2547229 := bbase (se 3 (by rfl) ⟨477605, by rfl⟩ : syracuseStep 2547229 = 955211) (by norm_num)
theorem B3396305 : Blo 2119435 3396305 := bstep (se 2 (by rfl) ⟨1273614, by rfl⟩ : syracuseStep 3396305 = 2547229) B2547229
theorem B2264203 : Blo 2119435 2264203 := bstep (se 1 (by rfl) ⟨1698152, by rfl⟩ : syracuseStep 2264203 = 3396305) B3396305
theorem B12075749 : Blo 2119435 12075749 := bstep (se 4 (by rfl) ⟨1132101, by rfl⟩ : syracuseStep 12075749 = 2264203) B2264203
theorem B8050499 : Blo 2119435 8050499 := bstep (se 1 (by rfl) ⟨6037874, by rfl⟩ : syracuseStep 8050499 = 12075749) B12075749
theorem B5366999 : Blo 2119435 5366999 := bstep (se 1 (by rfl) ⟨4025249, by rfl⟩ : syracuseStep 5366999 = 8050499) B8050499
theorem B3577999 : Blo 2119435 3577999 := bstep (se 1 (by rfl) ⟨2683499, by rfl⟩ : syracuseStep 3577999 = 5366999) B5366999
theorem B4770665 : Blo 2119435 4770665 := bstep (se 2 (by rfl) ⟨1788999, by rfl⟩ : syracuseStep 4770665 = 3577999) B3577999
theorem B3180443 : Blo 2119435 3180443 := bstep (se 1 (by rfl) ⟨2385332, by rfl⟩ : syracuseStep 3180443 = 4770665) B4770665
theorem B2120295 : Blo 2119435 2120295 := bstep (se 1 (by rfl) ⟨1590221, by rfl⟩ : syracuseStep 2120295 = 3180443) B3180443
theorem B2385337 : Blo 2119435 2385337 := bbase (se 2 (by rfl) ⟨894501, by rfl⟩ : syracuseStep 2385337 = 1789003) (by norm_num)
theorem B3180449 : Blo 2119435 3180449 := bstep (se 2 (by rfl) ⟨1192668, by rfl⟩ : syracuseStep 3180449 = 2385337) B2385337
theorem B2120299 : Blo 2119435 2120299 := bstep (se 1 (by rfl) ⟨1590224, by rfl⟩ : syracuseStep 2120299 = 3180449) B3180449
theorem B2581993 : Blo 2119435 2581993 := bbase (se 2 (by rfl) ⟨968247, by rfl⟩ : syracuseStep 2581993 = 1936495) (by norm_num)
theorem B3442657 : Blo 2119435 3442657 := bstep (se 2 (by rfl) ⟨1290996, by rfl⟩ : syracuseStep 3442657 = 2581993) B2581993
theorem B4590209 : Blo 2119435 4590209 := bstep (se 2 (by rfl) ⟨1721328, by rfl⟩ : syracuseStep 4590209 = 3442657) B3442657
theorem B12240557 : Blo 2119435 12240557 := bstep (se 3 (by rfl) ⟨2295104, by rfl⟩ : syracuseStep 12240557 = 4590209) B4590209
theorem B8160371 : Blo 2119435 8160371 := bstep (se 1 (by rfl) ⟨6120278, by rfl⟩ : syracuseStep 8160371 = 12240557) B12240557
theorem B5440247 : Blo 2119435 5440247 := bstep (se 1 (by rfl) ⟨4080185, by rfl⟩ : syracuseStep 5440247 = 8160371) B8160371
theorem B3626831 : Blo 2119435 3626831 := bstep (se 1 (by rfl) ⟨2720123, by rfl⟩ : syracuseStep 3626831 = 5440247) B5440247
theorem B2417887 : Blo 2119435 2417887 := bstep (se 1 (by rfl) ⟨1813415, by rfl⟩ : syracuseStep 2417887 = 3626831) B3626831
theorem B3223849 : Blo 2119435 3223849 := bstep (se 2 (by rfl) ⟨1208943, by rfl⟩ : syracuseStep 3223849 = 2417887) B2417887
theorem B4298465 : Blo 2119435 4298465 := bstep (se 2 (by rfl) ⟨1611924, by rfl⟩ : syracuseStep 4298465 = 3223849) B3223849
theorem B11462573 : Blo 2119435 11462573 := bstep (se 3 (by rfl) ⟨2149232, by rfl⟩ : syracuseStep 11462573 = 4298465) B4298465
theorem B7641715 : Blo 2119435 7641715 := bstep (se 1 (by rfl) ⟨5731286, by rfl⟩ : syracuseStep 7641715 = 11462573) B11462573
theorem B10188953 : Blo 2119435 10188953 := bstep (se 2 (by rfl) ⟨3820857, by rfl⟩ : syracuseStep 10188953 = 7641715) B7641715
theorem B6792635 : Blo 2119435 6792635 := bstep (se 1 (by rfl) ⟨5094476, by rfl⟩ : syracuseStep 6792635 = 10188953) B10188953
theorem B4528423 : Blo 2119435 4528423 := bstep (se 1 (by rfl) ⟨3396317, by rfl⟩ : syracuseStep 4528423 = 6792635) B6792635
theorem B6037897 : Blo 2119435 6037897 := bstep (se 2 (by rfl) ⟨2264211, by rfl⟩ : syracuseStep 6037897 = 4528423) B4528423
theorem B8050529 : Blo 2119435 8050529 := bstep (se 2 (by rfl) ⟨3018948, by rfl⟩ : syracuseStep 8050529 = 6037897) B6037897
theorem B5367019 : Blo 2119435 5367019 := bstep (se 1 (by rfl) ⟨4025264, by rfl⟩ : syracuseStep 5367019 = 8050529) B8050529
theorem B7156025 : Blo 2119435 7156025 := bstep (se 2 (by rfl) ⟨2683509, by rfl⟩ : syracuseStep 7156025 = 5367019) B5367019
theorem B4770683 : Blo 2119435 4770683 := bstep (se 1 (by rfl) ⟨3578012, by rfl⟩ : syracuseStep 4770683 = 7156025) B7156025
theorem B3180455 : Blo 2119435 3180455 := bstep (se 1 (by rfl) ⟨2385341, by rfl⟩ : syracuseStep 3180455 = 4770683) B4770683
theorem B2120303 : Blo 2119435 2120303 := bstep (se 1 (by rfl) ⟨1590227, by rfl⟩ : syracuseStep 2120303 = 3180455) B3180455
theorem B3180461 : Blo 2119435 3180461 := bbase (se 3 (by rfl) ⟨596336, by rfl⟩ : syracuseStep 3180461 = 1192673) (by norm_num)
theorem B2120307 : Blo 2119435 2120307 := bstep (se 1 (by rfl) ⟨1590230, by rfl⟩ : syracuseStep 2120307 = 3180461) B3180461
theorem B4770701 : Blo 2119435 4770701 := bbase (se 3 (by rfl) ⟨894506, by rfl⟩ : syracuseStep 4770701 = 1789013) (by norm_num)
theorem B3180467 : Blo 2119435 3180467 := bstep (se 1 (by rfl) ⟨2385350, by rfl⟩ : syracuseStep 3180467 = 4770701) B4770701
theorem B2120311 : Blo 2119435 2120311 := bstep (se 1 (by rfl) ⟨1590233, by rfl⟩ : syracuseStep 2120311 = 3180467) B3180467
theorem B2683525 : Blo 2119435 2683525 := bbase (se 4 (by rfl) ⟨251580, by rfl⟩ : syracuseStep 2683525 = 503161) (by norm_num)
theorem B3578033 : Blo 2119435 3578033 := bstep (se 2 (by rfl) ⟨1341762, by rfl⟩ : syracuseStep 3578033 = 2683525) B2683525
theorem B2385355 : Blo 2119435 2385355 := bstep (se 1 (by rfl) ⟨1789016, by rfl⟩ : syracuseStep 2385355 = 3578033) B3578033
theorem B3180473 : Blo 2119435 3180473 := bstep (se 2 (by rfl) ⟨1192677, by rfl⟩ : syracuseStep 3180473 = 2385355) B2385355
theorem B2120315 : Blo 2119435 2120315 := bstep (se 1 (by rfl) ⟨1590236, by rfl⟩ : syracuseStep 2120315 = 3180473) B3180473
theorem B2547257 : Blo 2119435 2547257 := bbase (se 2 (by rfl) ⟨955221, by rfl⟩ : syracuseStep 2547257 = 1910443) (by norm_num)
theorem B27170741 : Blo 2119435 27170741 := bstep (se 5 (by rfl) ⟨1273628, by rfl⟩ : syracuseStep 27170741 = 2547257) B2547257
theorem B18113827 : Blo 2119435 18113827 := bstep (se 1 (by rfl) ⟨13585370, by rfl⟩ : syracuseStep 18113827 = 27170741) B27170741
theorem B24151769 : Blo 2119435 24151769 := bstep (se 2 (by rfl) ⟨9056913, by rfl⟩ : syracuseStep 24151769 = 18113827) B18113827
theorem B16101179 : Blo 2119435 16101179 := bstep (se 1 (by rfl) ⟨12075884, by rfl⟩ : syracuseStep 16101179 = 24151769) B24151769
theorem B10734119 : Blo 2119435 10734119 := bstep (se 1 (by rfl) ⟨8050589, by rfl⟩ : syracuseStep 10734119 = 16101179) B16101179
theorem B7156079 : Blo 2119435 7156079 := bstep (se 1 (by rfl) ⟨5367059, by rfl⟩ : syracuseStep 7156079 = 10734119) B10734119
theorem B4770719 : Blo 2119435 4770719 := bstep (se 1 (by rfl) ⟨3578039, by rfl⟩ : syracuseStep 4770719 = 7156079) B7156079
theorem B3180479 : Blo 2119435 3180479 := bstep (se 1 (by rfl) ⟨2385359, by rfl⟩ : syracuseStep 3180479 = 4770719) B4770719
theorem B2120319 : Blo 2119435 2120319 := bstep (se 1 (by rfl) ⟨1590239, by rfl⟩ : syracuseStep 2120319 = 3180479) B3180479
theorem B3180485 : Blo 2119435 3180485 := bbase (se 4 (by rfl) ⟨298170, by rfl⟩ : syracuseStep 3180485 = 596341) (by norm_num)
theorem B2120323 : Blo 2119435 2120323 := bstep (se 1 (by rfl) ⟨1590242, by rfl⟩ : syracuseStep 2120323 = 3180485) B3180485
theorem B3578053 : Blo 2119435 3578053 := bbase (se 4 (by rfl) ⟨335442, by rfl⟩ : syracuseStep 3578053 = 670885) (by norm_num)
theorem B4770737 : Blo 2119435 4770737 := bstep (se 2 (by rfl) ⟨1789026, by rfl⟩ : syracuseStep 4770737 = 3578053) B3578053
theorem B3180491 : Blo 2119435 3180491 := bstep (se 1 (by rfl) ⟨2385368, by rfl⟩ : syracuseStep 3180491 = 4770737) B4770737
theorem B2120327 : Blo 2119435 2120327 := bstep (se 1 (by rfl) ⟨1590245, by rfl⟩ : syracuseStep 2120327 = 3180491) B3180491
theorem B2385373 : Blo 2119435 2385373 := bbase (se 3 (by rfl) ⟨447257, by rfl⟩ : syracuseStep 2385373 = 894515) (by norm_num)
theorem B3180497 : Blo 2119435 3180497 := bstep (se 2 (by rfl) ⟨1192686, by rfl⟩ : syracuseStep 3180497 = 2385373) B2385373
theorem B2120331 : Blo 2119435 2120331 := bstep (se 1 (by rfl) ⟨1590248, by rfl⟩ : syracuseStep 2120331 = 3180497) B3180497
theorem B7156133 : Blo 2119435 7156133 := bbase (se 4 (by rfl) ⟨670887, by rfl⟩ : syracuseStep 7156133 = 1341775) (by norm_num)
theorem B4770755 : Blo 2119435 4770755 := bstep (se 1 (by rfl) ⟨3578066, by rfl⟩ : syracuseStep 4770755 = 7156133) B7156133
theorem B3180503 : Blo 2119435 3180503 := bstep (se 1 (by rfl) ⟨2385377, by rfl⟩ : syracuseStep 3180503 = 4770755) B4770755
theorem B2120335 : Blo 2119435 2120335 := bstep (se 1 (by rfl) ⟨1590251, by rfl⟩ : syracuseStep 2120335 = 3180503) B3180503
theorem B3180509 : Blo 2119435 3180509 := bbase (se 3 (by rfl) ⟨596345, by rfl⟩ : syracuseStep 3180509 = 1192691) (by norm_num)
theorem B2120339 : Blo 2119435 2120339 := bstep (se 1 (by rfl) ⟨1590254, by rfl⟩ : syracuseStep 2120339 = 3180509) B3180509
theorem B4770773 : Blo 2119435 4770773 := bbase (se 7 (by rfl) ⟨55907, by rfl⟩ : syracuseStep 4770773 = 111815) (by norm_num)
theorem B3180515 : Blo 2119435 3180515 := bstep (se 1 (by rfl) ⟨2385386, by rfl⟩ : syracuseStep 3180515 = 4770773) B4770773
theorem B2120343 : Blo 2119435 2120343 := bstep (se 1 (by rfl) ⟨1590257, by rfl⟩ : syracuseStep 2120343 = 3180515) B3180515
theorem B7253813 : Blo 2119435 7253813 := bbase (se 5 (by rfl) ⟨340022, by rfl⟩ : syracuseStep 7253813 = 680045) (by norm_num)
theorem B4835875 : Blo 2119435 4835875 := bstep (se 1 (by rfl) ⟨3626906, by rfl⟩ : syracuseStep 4835875 = 7253813) B7253813
theorem B6447833 : Blo 2119435 6447833 := bstep (se 2 (by rfl) ⟨2417937, by rfl⟩ : syracuseStep 6447833 = 4835875) B4835875
theorem B4298555 : Blo 2119435 4298555 := bstep (se 1 (by rfl) ⟨3223916, by rfl⟩ : syracuseStep 4298555 = 6447833) B6447833
theorem B2865703 : Blo 2119435 2865703 := bstep (se 1 (by rfl) ⟨2149277, by rfl⟩ : syracuseStep 2865703 = 4298555) B4298555
theorem B3820937 : Blo 2119435 3820937 := bstep (se 2 (by rfl) ⟨1432851, by rfl⟩ : syracuseStep 3820937 = 2865703) B2865703
theorem B10189165 : Blo 2119435 10189165 := bstep (se 3 (by rfl) ⟨1910468, by rfl⟩ : syracuseStep 10189165 = 3820937) B3820937
theorem B13585553 : Blo 2119435 13585553 := bstep (se 2 (by rfl) ⟨5094582, by rfl⟩ : syracuseStep 13585553 = 10189165) B10189165
theorem B9057035 : Blo 2119435 9057035 := bstep (se 1 (by rfl) ⟨6792776, by rfl⟩ : syracuseStep 9057035 = 13585553) B13585553
theorem B6038023 : Blo 2119435 6038023 := bstep (se 1 (by rfl) ⟨4528517, by rfl⟩ : syracuseStep 6038023 = 9057035) B9057035
theorem B8050697 : Blo 2119435 8050697 := bstep (se 2 (by rfl) ⟨3019011, by rfl⟩ : syracuseStep 8050697 = 6038023) B6038023
theorem B5367131 : Blo 2119435 5367131 := bstep (se 1 (by rfl) ⟨4025348, by rfl⟩ : syracuseStep 5367131 = 8050697) B8050697
theorem B3578087 : Blo 2119435 3578087 := bstep (se 1 (by rfl) ⟨2683565, by rfl⟩ : syracuseStep 3578087 = 5367131) B5367131
theorem B2385391 : Blo 2119435 2385391 := bstep (se 1 (by rfl) ⟨1789043, by rfl⟩ : syracuseStep 2385391 = 3578087) B3578087
theorem B3180521 : Blo 2119435 3180521 := bstep (se 2 (by rfl) ⟨1192695, by rfl⟩ : syracuseStep 3180521 = 2385391) B2385391
theorem B2120347 : Blo 2119435 2120347 := bstep (se 1 (by rfl) ⟨1590260, by rfl⟩ : syracuseStep 2120347 = 3180521) B3180521
theorem B18114101 : Blo 2119435 18114101 := bbase (se 5 (by rfl) ⟨849098, by rfl⟩ : syracuseStep 18114101 = 1698197) (by norm_num)
theorem B12076067 : Blo 2119435 12076067 := bstep (se 1 (by rfl) ⟨9057050, by rfl⟩ : syracuseStep 12076067 = 18114101) B18114101
theorem B8050711 : Blo 2119435 8050711 := bstep (se 1 (by rfl) ⟨6038033, by rfl⟩ : syracuseStep 8050711 = 12076067) B12076067
theorem B10734281 : Blo 2119435 10734281 := bstep (se 2 (by rfl) ⟨4025355, by rfl⟩ : syracuseStep 10734281 = 8050711) B8050711
theorem B7156187 : Blo 2119435 7156187 := bstep (se 1 (by rfl) ⟨5367140, by rfl⟩ : syracuseStep 7156187 = 10734281) B10734281
theorem B4770791 : Blo 2119435 4770791 := bstep (se 1 (by rfl) ⟨3578093, by rfl⟩ : syracuseStep 4770791 = 7156187) B7156187
theorem B3180527 : Blo 2119435 3180527 := bstep (se 1 (by rfl) ⟨2385395, by rfl⟩ : syracuseStep 3180527 = 4770791) B4770791
theorem B2120351 : Blo 2119435 2120351 := bstep (se 1 (by rfl) ⟨1590263, by rfl⟩ : syracuseStep 2120351 = 3180527) B3180527
theorem B3180533 : Blo 2119435 3180533 := bbase (se 5 (by rfl) ⟨149087, by rfl⟩ : syracuseStep 3180533 = 298175) (by norm_num)
theorem B2120355 : Blo 2119435 2120355 := bstep (se 1 (by rfl) ⟨1590266, by rfl⟩ : syracuseStep 2120355 = 3180533) B3180533
theorem B19343605 : Blo 2119435 19343605 := bbase (se 5 (by rfl) ⟨906731, by rfl⟩ : syracuseStep 19343605 = 1813463) (by norm_num)
theorem B25791473 : Blo 2119435 25791473 := bstep (se 2 (by rfl) ⟨9671802, by rfl⟩ : syracuseStep 25791473 = 19343605) B19343605
theorem B17194315 : Blo 2119435 17194315 := bstep (se 1 (by rfl) ⟨12895736, by rfl⟩ : syracuseStep 17194315 = 25791473) B25791473
theorem B22925753 : Blo 2119435 22925753 := bstep (se 2 (by rfl) ⟨8597157, by rfl⟩ : syracuseStep 22925753 = 17194315) B17194315
theorem B15283835 : Blo 2119435 15283835 := bstep (se 1 (by rfl) ⟨11462876, by rfl⟩ : syracuseStep 15283835 = 22925753) B22925753
theorem B10189223 : Blo 2119435 10189223 := bstep (se 1 (by rfl) ⟨7641917, by rfl⟩ : syracuseStep 10189223 = 15283835) B15283835
theorem B6792815 : Blo 2119435 6792815 := bstep (se 1 (by rfl) ⟨5094611, by rfl⟩ : syracuseStep 6792815 = 10189223) B10189223
theorem B4528543 : Blo 2119435 4528543 := bstep (se 1 (by rfl) ⟨3396407, by rfl⟩ : syracuseStep 4528543 = 6792815) B6792815
theorem B6038057 : Blo 2119435 6038057 := bstep (se 2 (by rfl) ⟨2264271, by rfl⟩ : syracuseStep 6038057 = 4528543) B4528543
theorem B4025371 : Blo 2119435 4025371 := bstep (se 1 (by rfl) ⟨3019028, by rfl⟩ : syracuseStep 4025371 = 6038057) B6038057
theorem B5367161 : Blo 2119435 5367161 := bstep (se 2 (by rfl) ⟨2012685, by rfl⟩ : syracuseStep 5367161 = 4025371) B4025371
theorem B3578107 : Blo 2119435 3578107 := bstep (se 1 (by rfl) ⟨2683580, by rfl⟩ : syracuseStep 3578107 = 5367161) B5367161
theorem B4770809 : Blo 2119435 4770809 := bstep (se 2 (by rfl) ⟨1789053, by rfl⟩ : syracuseStep 4770809 = 3578107) B3578107
theorem B3180539 : Blo 2119435 3180539 := bstep (se 1 (by rfl) ⟨2385404, by rfl⟩ : syracuseStep 3180539 = 4770809) B4770809
theorem B2120359 : Blo 2119435 2120359 := bstep (se 1 (by rfl) ⟨1590269, by rfl⟩ : syracuseStep 2120359 = 3180539) B3180539
theorem B2385409 : Blo 2119435 2385409 := bbase (se 2 (by rfl) ⟨894528, by rfl⟩ : syracuseStep 2385409 = 1789057) (by norm_num)
theorem B3180545 : Blo 2119435 3180545 := bstep (se 2 (by rfl) ⟨1192704, by rfl⟩ : syracuseStep 3180545 = 2385409) B2385409
theorem B2120363 : Blo 2119435 2120363 := bstep (se 1 (by rfl) ⟨1590272, by rfl⟩ : syracuseStep 2120363 = 3180545) B3180545
theorem B5367181 : Blo 2119435 5367181 := bbase (se 3 (by rfl) ⟨1006346, by rfl⟩ : syracuseStep 5367181 = 2012693) (by norm_num)
theorem B7156241 : Blo 2119435 7156241 := bstep (se 2 (by rfl) ⟨2683590, by rfl⟩ : syracuseStep 7156241 = 5367181) B5367181
theorem B4770827 : Blo 2119435 4770827 := bstep (se 1 (by rfl) ⟨3578120, by rfl⟩ : syracuseStep 4770827 = 7156241) B7156241
theorem B3180551 : Blo 2119435 3180551 := bstep (se 1 (by rfl) ⟨2385413, by rfl⟩ : syracuseStep 3180551 = 4770827) B4770827
theorem B2120367 : Blo 2119435 2120367 := bstep (se 1 (by rfl) ⟨1590275, by rfl⟩ : syracuseStep 2120367 = 3180551) B3180551
theorem B3180557 : Blo 2119435 3180557 := bbase (se 3 (by rfl) ⟨596354, by rfl⟩ : syracuseStep 3180557 = 1192709) (by norm_num)
theorem B2120371 : Blo 2119435 2120371 := bstep (se 1 (by rfl) ⟨1590278, by rfl⟩ : syracuseStep 2120371 = 3180557) B3180557
theorem B4770845 : Blo 2119435 4770845 := bbase (se 3 (by rfl) ⟨894533, by rfl⟩ : syracuseStep 4770845 = 1789067) (by norm_num)
theorem B3180563 : Blo 2119435 3180563 := bstep (se 1 (by rfl) ⟨2385422, by rfl⟩ : syracuseStep 3180563 = 4770845) B4770845
theorem B2120375 : Blo 2119435 2120375 := bstep (se 1 (by rfl) ⟨1590281, by rfl⟩ : syracuseStep 2120375 = 3180563) B3180563
theorem B3578141 : Blo 2119435 3578141 := bbase (se 3 (by rfl) ⟨670901, by rfl⟩ : syracuseStep 3578141 = 1341803) (by norm_num)
theorem B2385427 : Blo 2119435 2385427 := bstep (se 1 (by rfl) ⟨1789070, by rfl⟩ : syracuseStep 2385427 = 3578141) B3578141
theorem B3180569 : Blo 2119435 3180569 := bstep (se 2 (by rfl) ⟨1192713, by rfl⟩ : syracuseStep 3180569 = 2385427) B2385427
theorem B2120379 : Blo 2119435 2120379 := bstep (se 1 (by rfl) ⟨1590284, by rfl⟩ : syracuseStep 2120379 = 3180569) B3180569
theorem B13585781 : Blo 2119435 13585781 := bbase (se 5 (by rfl) ⟨636833, by rfl⟩ : syracuseStep 13585781 = 1273667) (by norm_num)
theorem B9057187 : Blo 2119435 9057187 := bstep (se 1 (by rfl) ⟨6792890, by rfl⟩ : syracuseStep 9057187 = 13585781) B13585781
theorem B12076249 : Blo 2119435 12076249 := bstep (se 2 (by rfl) ⟨4528593, by rfl⟩ : syracuseStep 12076249 = 9057187) B9057187
theorem B16101665 : Blo 2119435 16101665 := bstep (se 2 (by rfl) ⟨6038124, by rfl⟩ : syracuseStep 16101665 = 12076249) B12076249
theorem B10734443 : Blo 2119435 10734443 := bstep (se 1 (by rfl) ⟨8050832, by rfl⟩ : syracuseStep 10734443 = 16101665) B16101665
theorem B7156295 : Blo 2119435 7156295 := bstep (se 1 (by rfl) ⟨5367221, by rfl⟩ : syracuseStep 7156295 = 10734443) B10734443
theorem B4770863 : Blo 2119435 4770863 := bstep (se 1 (by rfl) ⟨3578147, by rfl⟩ : syracuseStep 4770863 = 7156295) B7156295
theorem B3180575 : Blo 2119435 3180575 := bstep (se 1 (by rfl) ⟨2385431, by rfl⟩ : syracuseStep 3180575 = 4770863) B4770863
theorem B2120383 : Blo 2119435 2120383 := bstep (se 1 (by rfl) ⟨1590287, by rfl⟩ : syracuseStep 2120383 = 3180575) B3180575
theorem B3180581 : Blo 2119435 3180581 := bbase (se 4 (by rfl) ⟨298179, by rfl⟩ : syracuseStep 3180581 = 596359) (by norm_num)
theorem B2120387 : Blo 2119435 2120387 := bstep (se 1 (by rfl) ⟨1590290, by rfl⟩ : syracuseStep 2120387 = 3180581) B3180581
theorem B2683621 : Blo 2119435 2683621 := bbase (se 4 (by rfl) ⟨251589, by rfl⟩ : syracuseStep 2683621 = 503179) (by norm_num)
theorem B3578161 : Blo 2119435 3578161 := bstep (se 2 (by rfl) ⟨1341810, by rfl⟩ : syracuseStep 3578161 = 2683621) B2683621
theorem B4770881 : Blo 2119435 4770881 := bstep (se 2 (by rfl) ⟨1789080, by rfl⟩ : syracuseStep 4770881 = 3578161) B3578161
theorem B3180587 : Blo 2119435 3180587 := bstep (se 1 (by rfl) ⟨2385440, by rfl⟩ : syracuseStep 3180587 = 4770881) B4770881
theorem B2120391 : Blo 2119435 2120391 := bstep (se 1 (by rfl) ⟨1590293, by rfl⟩ : syracuseStep 2120391 = 3180587) B3180587
theorem B2385445 : Blo 2119435 2385445 := bbase (se 4 (by rfl) ⟨223635, by rfl⟩ : syracuseStep 2385445 = 447271) (by norm_num)
theorem B3180593 : Blo 2119435 3180593 := bstep (se 2 (by rfl) ⟨1192722, by rfl⟩ : syracuseStep 3180593 = 2385445) B2385445
theorem B2120395 : Blo 2119435 2120395 := bstep (se 1 (by rfl) ⟨1590296, by rfl⟩ : syracuseStep 2120395 = 3180593) B3180593
theorem B4357309 : Blo 2119435 4357309 := bbase (se 3 (by rfl) ⟨816995, by rfl⟩ : syracuseStep 4357309 = 1633991) (by norm_num)
theorem B5809745 : Blo 2119435 5809745 := bstep (se 2 (by rfl) ⟨2178654, by rfl⟩ : syracuseStep 5809745 = 4357309) B4357309
theorem B15492653 : Blo 2119435 15492653 := bstep (se 3 (by rfl) ⟨2904872, by rfl⟩ : syracuseStep 15492653 = 5809745) B5809745
theorem B10328435 : Blo 2119435 10328435 := bstep (se 1 (by rfl) ⟨7746326, by rfl⟩ : syracuseStep 10328435 = 15492653) B15492653
theorem B6885623 : Blo 2119435 6885623 := bstep (se 1 (by rfl) ⟨5164217, by rfl⟩ : syracuseStep 6885623 = 10328435) B10328435
theorem B4590415 : Blo 2119435 4590415 := bstep (se 1 (by rfl) ⟨3442811, by rfl⟩ : syracuseStep 4590415 = 6885623) B6885623
theorem B24482213 : Blo 2119435 24482213 := bstep (se 4 (by rfl) ⟨2295207, by rfl⟩ : syracuseStep 24482213 = 4590415) B4590415
theorem B16321475 : Blo 2119435 16321475 := bstep (se 1 (by rfl) ⟨12241106, by rfl⟩ : syracuseStep 16321475 = 24482213) B24482213
theorem B10880983 : Blo 2119435 10880983 := bstep (se 1 (by rfl) ⟨8160737, by rfl⟩ : syracuseStep 10880983 = 16321475) B16321475
theorem B58031909 : Blo 2119435 58031909 := bstep (se 4 (by rfl) ⟨5440491, by rfl⟩ : syracuseStep 58031909 = 10880983) B10880983
theorem B38687939 : Blo 2119435 38687939 := bstep (se 1 (by rfl) ⟨29015954, by rfl⟩ : syracuseStep 38687939 = 58031909) B58031909
theorem B25791959 : Blo 2119435 25791959 := bstep (se 1 (by rfl) ⟨19343969, by rfl⟩ : syracuseStep 25791959 = 38687939) B38687939
theorem B17194639 : Blo 2119435 17194639 := bstep (se 1 (by rfl) ⟨12895979, by rfl⟩ : syracuseStep 17194639 = 25791959) B25791959
theorem B22926185 : Blo 2119435 22926185 := bstep (se 2 (by rfl) ⟨8597319, by rfl⟩ : syracuseStep 22926185 = 17194639) B17194639
theorem B15284123 : Blo 2119435 15284123 := bstep (se 1 (by rfl) ⟨11463092, by rfl⟩ : syracuseStep 15284123 = 22926185) B22926185
theorem B10189415 : Blo 2119435 10189415 := bstep (se 1 (by rfl) ⟨7642061, by rfl⟩ : syracuseStep 10189415 = 15284123) B15284123
theorem B6792943 : Blo 2119435 6792943 := bstep (se 1 (by rfl) ⟨5094707, by rfl⟩ : syracuseStep 6792943 = 10189415) B10189415
theorem B9057257 : Blo 2119435 9057257 := bstep (se 2 (by rfl) ⟨3396471, by rfl⟩ : syracuseStep 9057257 = 6792943) B6792943
theorem B6038171 : Blo 2119435 6038171 := bstep (se 1 (by rfl) ⟨4528628, by rfl⟩ : syracuseStep 6038171 = 9057257) B9057257
theorem B4025447 : Blo 2119435 4025447 := bstep (se 1 (by rfl) ⟨3019085, by rfl⟩ : syracuseStep 4025447 = 6038171) B6038171
theorem B2683631 : Blo 2119435 2683631 := bstep (se 1 (by rfl) ⟨2012723, by rfl⟩ : syracuseStep 2683631 = 4025447) B4025447
theorem B7156349 : Blo 2119435 7156349 := bstep (se 3 (by rfl) ⟨1341815, by rfl⟩ : syracuseStep 7156349 = 2683631) B2683631
theorem B4770899 : Blo 2119435 4770899 := bstep (se 1 (by rfl) ⟨3578174, by rfl⟩ : syracuseStep 4770899 = 7156349) B7156349
theorem B3180599 : Blo 2119435 3180599 := bstep (se 1 (by rfl) ⟨2385449, by rfl⟩ : syracuseStep 3180599 = 4770899) B4770899
theorem B2120399 : Blo 2119435 2120399 := bstep (se 1 (by rfl) ⟨1590299, by rfl⟩ : syracuseStep 2120399 = 3180599) B3180599
theorem B3180605 : Blo 2119435 3180605 := bbase (se 3 (by rfl) ⟨596363, by rfl⟩ : syracuseStep 3180605 = 1192727) (by norm_num)
theorem B2120403 : Blo 2119435 2120403 := bstep (se 1 (by rfl) ⟨1590302, by rfl⟩ : syracuseStep 2120403 = 3180605) B3180605
theorem B4770917 : Blo 2119435 4770917 := bbase (se 4 (by rfl) ⟨447273, by rfl⟩ : syracuseStep 4770917 = 894547) (by norm_num)
theorem B3180611 : Blo 2119435 3180611 := bstep (se 1 (by rfl) ⟨2385458, by rfl⟩ : syracuseStep 3180611 = 4770917) B4770917
theorem B2120407 : Blo 2119435 2120407 := bstep (se 1 (by rfl) ⟨1590305, by rfl⟩ : syracuseStep 2120407 = 3180611) B3180611
theorem B5367293 : Blo 2119435 5367293 := bbase (se 3 (by rfl) ⟨1006367, by rfl⟩ : syracuseStep 5367293 = 2012735) (by norm_num)
theorem B3578195 : Blo 2119435 3578195 := bstep (se 1 (by rfl) ⟨2683646, by rfl⟩ : syracuseStep 3578195 = 5367293) B5367293
theorem B2385463 : Blo 2119435 2385463 := bstep (se 1 (by rfl) ⟨1789097, by rfl⟩ : syracuseStep 2385463 = 3578195) B3578195
theorem B3180617 : Blo 2119435 3180617 := bstep (se 2 (by rfl) ⟨1192731, by rfl⟩ : syracuseStep 3180617 = 2385463) B2385463
theorem B2120411 : Blo 2119435 2120411 := bstep (se 1 (by rfl) ⟨1590308, by rfl⟩ : syracuseStep 2120411 = 3180617) B3180617
theorem B4025477 : Blo 2119435 4025477 := bbase (se 4 (by rfl) ⟨377388, by rfl⟩ : syracuseStep 4025477 = 754777) (by norm_num)
theorem B10734605 : Blo 2119435 10734605 := bstep (se 3 (by rfl) ⟨2012738, by rfl⟩ : syracuseStep 10734605 = 4025477) B4025477
theorem B7156403 : Blo 2119435 7156403 := bstep (se 1 (by rfl) ⟨5367302, by rfl⟩ : syracuseStep 7156403 = 10734605) B10734605
theorem B4770935 : Blo 2119435 4770935 := bstep (se 1 (by rfl) ⟨3578201, by rfl⟩ : syracuseStep 4770935 = 7156403) B7156403
theorem B3180623 : Blo 2119435 3180623 := bstep (se 1 (by rfl) ⟨2385467, by rfl⟩ : syracuseStep 3180623 = 4770935) B4770935
theorem B2120415 : Blo 2119435 2120415 := bstep (se 1 (by rfl) ⟨1590311, by rfl⟩ : syracuseStep 2120415 = 3180623) B3180623
theorem B3180629 : Blo 2119435 3180629 := bbase (se 8 (by rfl) ⟨18636, by rfl⟩ : syracuseStep 3180629 = 37273) (by norm_num)
theorem B2120419 : Blo 2119435 2120419 := bstep (se 1 (by rfl) ⟨1590314, by rfl⟩ : syracuseStep 2120419 = 3180629) B3180629
theorem B11463221 : Blo 2119435 11463221 := bbase (se 5 (by rfl) ⟨537338, by rfl⟩ : syracuseStep 11463221 = 1074677) (by norm_num)
theorem B30568589 : Blo 2119435 30568589 := bstep (se 3 (by rfl) ⟨5731610, by rfl⟩ : syracuseStep 30568589 = 11463221) B11463221
theorem B20379059 : Blo 2119435 20379059 := bstep (se 1 (by rfl) ⟨15284294, by rfl⟩ : syracuseStep 20379059 = 30568589) B30568589
theorem B13586039 : Blo 2119435 13586039 := bstep (se 1 (by rfl) ⟨10189529, by rfl⟩ : syracuseStep 13586039 = 20379059) B20379059
theorem B9057359 : Blo 2119435 9057359 := bstep (se 1 (by rfl) ⟨6793019, by rfl⟩ : syracuseStep 9057359 = 13586039) B13586039
theorem B6038239 : Blo 2119435 6038239 := bstep (se 1 (by rfl) ⟨4528679, by rfl⟩ : syracuseStep 6038239 = 9057359) B9057359
theorem B8050985 : Blo 2119435 8050985 := bstep (se 2 (by rfl) ⟨3019119, by rfl⟩ : syracuseStep 8050985 = 6038239) B6038239
theorem B5367323 : Blo 2119435 5367323 := bstep (se 1 (by rfl) ⟨4025492, by rfl⟩ : syracuseStep 5367323 = 8050985) B8050985
theorem B3578215 : Blo 2119435 3578215 := bstep (se 1 (by rfl) ⟨2683661, by rfl⟩ : syracuseStep 3578215 = 5367323) B5367323
theorem B4770953 : Blo 2119435 4770953 := bstep (se 2 (by rfl) ⟨1789107, by rfl⟩ : syracuseStep 4770953 = 3578215) B3578215
theorem B3180635 : Blo 2119435 3180635 := bstep (se 1 (by rfl) ⟨2385476, by rfl⟩ : syracuseStep 3180635 = 4770953) B4770953
theorem B2120423 : Blo 2119435 2120423 := bstep (se 1 (by rfl) ⟨1590317, by rfl⟩ : syracuseStep 2120423 = 3180635) B3180635
theorem B2385481 : Blo 2119435 2385481 := bbase (se 2 (by rfl) ⟨894555, by rfl⟩ : syracuseStep 2385481 = 1789111) (by norm_num)
theorem B3180641 : Blo 2119435 3180641 := bstep (se 2 (by rfl) ⟨1192740, by rfl⟩ : syracuseStep 3180641 = 2385481) B2385481
theorem B2120427 : Blo 2119435 2120427 := bstep (se 1 (by rfl) ⟨1590320, by rfl⟩ : syracuseStep 2120427 = 3180641) B3180641
theorem B4357373 : Blo 2119435 4357373 := bbase (se 3 (by rfl) ⟨817007, by rfl⟩ : syracuseStep 4357373 = 1634015) (by norm_num)
theorem B11619661 : Blo 2119435 11619661 := bstep (se 3 (by rfl) ⟨2178686, by rfl⟩ : syracuseStep 11619661 = 4357373) B4357373
theorem B15492881 : Blo 2119435 15492881 := bstep (se 2 (by rfl) ⟨5809830, by rfl⟩ : syracuseStep 15492881 = 11619661) B11619661
theorem B41314349 : Blo 2119435 41314349 := bstep (se 3 (by rfl) ⟨7746440, by rfl⟩ : syracuseStep 41314349 = 15492881) B15492881
theorem B27542899 : Blo 2119435 27542899 := bstep (se 1 (by rfl) ⟨20657174, by rfl⟩ : syracuseStep 27542899 = 41314349) B41314349
theorem B36723865 : Blo 2119435 36723865 := bstep (se 2 (by rfl) ⟨13771449, by rfl⟩ : syracuseStep 36723865 = 27542899) B27542899
theorem B48965153 : Blo 2119435 48965153 := bstep (se 2 (by rfl) ⟨18361932, by rfl⟩ : syracuseStep 48965153 = 36723865) B36723865
theorem B130573741 : Blo 2119435 130573741 := bstep (se 3 (by rfl) ⟨24482576, by rfl⟩ : syracuseStep 130573741 = 48965153) B48965153
theorem B174098321 : Blo 2119435 174098321 := bstep (se 2 (by rfl) ⟨65286870, by rfl⟩ : syracuseStep 174098321 = 130573741) B130573741
theorem B116065547 : Blo 2119435 116065547 := bstep (se 1 (by rfl) ⟨87049160, by rfl⟩ : syracuseStep 116065547 = 174098321) B174098321
theorem B77377031 : Blo 2119435 77377031 := bstep (se 1 (by rfl) ⟨58032773, by rfl⟩ : syracuseStep 77377031 = 116065547) B116065547
theorem B51584687 : Blo 2119435 51584687 := bstep (se 1 (by rfl) ⟨38688515, by rfl⟩ : syracuseStep 51584687 = 77377031) B77377031
theorem B34389791 : Blo 2119435 34389791 := bstep (se 1 (by rfl) ⟨25792343, by rfl⟩ : syracuseStep 34389791 = 51584687) B51584687
theorem B22926527 : Blo 2119435 22926527 := bstep (se 1 (by rfl) ⟨17194895, by rfl⟩ : syracuseStep 22926527 = 34389791) B34389791
theorem B15284351 : Blo 2119435 15284351 := bstep (se 1 (by rfl) ⟨11463263, by rfl⟩ : syracuseStep 15284351 = 22926527) B22926527
theorem B10189567 : Blo 2119435 10189567 := bstep (se 1 (by rfl) ⟨7642175, by rfl⟩ : syracuseStep 10189567 = 15284351) B15284351
theorem B13586089 : Blo 2119435 13586089 := bstep (se 2 (by rfl) ⟨5094783, by rfl⟩ : syracuseStep 13586089 = 10189567) B10189567
theorem B18114785 : Blo 2119435 18114785 := bstep (se 2 (by rfl) ⟨6793044, by rfl⟩ : syracuseStep 18114785 = 13586089) B13586089
theorem B12076523 : Blo 2119435 12076523 := bstep (se 1 (by rfl) ⟨9057392, by rfl⟩ : syracuseStep 12076523 = 18114785) B18114785
theorem B8051015 : Blo 2119435 8051015 := bstep (se 1 (by rfl) ⟨6038261, by rfl⟩ : syracuseStep 8051015 = 12076523) B12076523
theorem B5367343 : Blo 2119435 5367343 := bstep (se 1 (by rfl) ⟨4025507, by rfl⟩ : syracuseStep 5367343 = 8051015) B8051015
theorem B7156457 : Blo 2119435 7156457 := bstep (se 2 (by rfl) ⟨2683671, by rfl⟩ : syracuseStep 7156457 = 5367343) B5367343
theorem B4770971 : Blo 2119435 4770971 := bstep (se 1 (by rfl) ⟨3578228, by rfl⟩ : syracuseStep 4770971 = 7156457) B7156457
theorem B3180647 : Blo 2119435 3180647 := bstep (se 1 (by rfl) ⟨2385485, by rfl⟩ : syracuseStep 3180647 = 4770971) B4770971
theorem B2120431 : Blo 2119435 2120431 := bstep (se 1 (by rfl) ⟨1590323, by rfl⟩ : syracuseStep 2120431 = 3180647) B3180647
theorem B3180653 : Blo 2119435 3180653 := bbase (se 3 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 3180653 = 1192745) (by norm_num)
theorem B2120435 : Blo 2119435 2120435 := bstep (se 1 (by rfl) ⟨1590326, by rfl⟩ : syracuseStep 2120435 = 3180653) B3180653
theorem B4770989 : Blo 2119435 4770989 := bbase (se 3 (by rfl) ⟨894560, by rfl⟩ : syracuseStep 4770989 = 1789121) (by norm_num)
theorem B3180659 : Blo 2119435 3180659 := bstep (se 1 (by rfl) ⟨2385494, by rfl⟩ : syracuseStep 3180659 = 4770989) B4770989
theorem B2120439 : Blo 2119435 2120439 := bstep (se 1 (by rfl) ⟨1590329, by rfl⟩ : syracuseStep 2120439 = 3180659) B3180659
theorem B61971925 : Blo 2119435 61971925 := bbase (se 7 (by rfl) ⟨726233, by rfl⟩ : syracuseStep 61971925 = 1452467) (by norm_num)
theorem B82629233 : Blo 2119435 82629233 := bstep (se 2 (by rfl) ⟨30985962, by rfl⟩ : syracuseStep 82629233 = 61971925) B61971925
theorem B55086155 : Blo 2119435 55086155 := bstep (se 1 (by rfl) ⟨41314616, by rfl⟩ : syracuseStep 55086155 = 82629233) B82629233
theorem B36724103 : Blo 2119435 36724103 := bstep (se 1 (by rfl) ⟨27543077, by rfl⟩ : syracuseStep 36724103 = 55086155) B55086155
theorem B24482735 : Blo 2119435 24482735 := bstep (se 1 (by rfl) ⟨18362051, by rfl⟩ : syracuseStep 24482735 = 36724103) B36724103
theorem B16321823 : Blo 2119435 16321823 := bstep (se 1 (by rfl) ⟨12241367, by rfl⟩ : syracuseStep 16321823 = 24482735) B24482735
theorem B10881215 : Blo 2119435 10881215 := bstep (se 1 (by rfl) ⟨8160911, by rfl⟩ : syracuseStep 10881215 = 16321823) B16321823
theorem B7254143 : Blo 2119435 7254143 := bstep (se 1 (by rfl) ⟨5440607, by rfl⟩ : syracuseStep 7254143 = 10881215) B10881215
theorem B4836095 : Blo 2119435 4836095 := bstep (se 1 (by rfl) ⟨3627071, by rfl⟩ : syracuseStep 4836095 = 7254143) B7254143
theorem B3224063 : Blo 2119435 3224063 := bstep (se 1 (by rfl) ⟨2418047, by rfl⟩ : syracuseStep 3224063 = 4836095) B4836095
theorem B8597501 : Blo 2119435 8597501 := bstep (se 3 (by rfl) ⟨1612031, by rfl⟩ : syracuseStep 8597501 = 3224063) B3224063
theorem B5731667 : Blo 2119435 5731667 := bstep (se 1 (by rfl) ⟨4298750, by rfl⟩ : syracuseStep 5731667 = 8597501) B8597501
theorem B3821111 : Blo 2119435 3821111 := bstep (se 1 (by rfl) ⟨2865833, by rfl⟩ : syracuseStep 3821111 = 5731667) B5731667
theorem B2547407 : Blo 2119435 2547407 := bstep (se 1 (by rfl) ⟨1910555, by rfl⟩ : syracuseStep 2547407 = 3821111) B3821111
theorem B6793085 : Blo 2119435 6793085 := bstep (se 3 (by rfl) ⟨1273703, by rfl⟩ : syracuseStep 6793085 = 2547407) B2547407
theorem B4528723 : Blo 2119435 4528723 := bstep (se 1 (by rfl) ⟨3396542, by rfl⟩ : syracuseStep 4528723 = 6793085) B6793085
theorem B6038297 : Blo 2119435 6038297 := bstep (se 2 (by rfl) ⟨2264361, by rfl⟩ : syracuseStep 6038297 = 4528723) B4528723
theorem B4025531 : Blo 2119435 4025531 := bstep (se 1 (by rfl) ⟨3019148, by rfl⟩ : syracuseStep 4025531 = 6038297) B6038297
theorem B2683687 : Blo 2119435 2683687 := bstep (se 1 (by rfl) ⟨2012765, by rfl⟩ : syracuseStep 2683687 = 4025531) B4025531
theorem B3578249 : Blo 2119435 3578249 := bstep (se 2 (by rfl) ⟨1341843, by rfl⟩ : syracuseStep 3578249 = 2683687) B2683687
theorem B2385499 : Blo 2119435 2385499 := bstep (se 1 (by rfl) ⟨1789124, by rfl⟩ : syracuseStep 2385499 = 3578249) B3578249
theorem B3180665 : Blo 2119435 3180665 := bstep (se 2 (by rfl) ⟨1192749, by rfl⟩ : syracuseStep 3180665 = 2385499) B2385499
theorem B2120443 : Blo 2119435 2120443 := bstep (se 1 (by rfl) ⟨1590332, by rfl⟩ : syracuseStep 2120443 = 3180665) B3180665
theorem B11463349 : Blo 2119435 11463349 := bbase (se 5 (by rfl) ⟨537344, by rfl⟩ : syracuseStep 11463349 = 1074689) (by norm_num)
theorem B15284465 : Blo 2119435 15284465 := bstep (se 2 (by rfl) ⟨5731674, by rfl⟩ : syracuseStep 15284465 = 11463349) B11463349
theorem B10189643 : Blo 2119435 10189643 := bstep (se 1 (by rfl) ⟨7642232, by rfl⟩ : syracuseStep 10189643 = 15284465) B15284465
theorem B27172381 : Blo 2119435 27172381 := bstep (se 3 (by rfl) ⟨5094821, by rfl⟩ : syracuseStep 27172381 = 10189643) B10189643
theorem B36229841 : Blo 2119435 36229841 := bstep (se 2 (by rfl) ⟨13586190, by rfl⟩ : syracuseStep 36229841 = 27172381) B27172381
theorem B24153227 : Blo 2119435 24153227 := bstep (se 1 (by rfl) ⟨18114920, by rfl⟩ : syracuseStep 24153227 = 36229841) B36229841
theorem B16102151 : Blo 2119435 16102151 := bstep (se 1 (by rfl) ⟨12076613, by rfl⟩ : syracuseStep 16102151 = 24153227) B24153227
theorem B10734767 : Blo 2119435 10734767 := bstep (se 1 (by rfl) ⟨8051075, by rfl⟩ : syracuseStep 10734767 = 16102151) B16102151
theorem B7156511 : Blo 2119435 7156511 := bstep (se 1 (by rfl) ⟨5367383, by rfl⟩ : syracuseStep 7156511 = 10734767) B10734767
theorem B4771007 : Blo 2119435 4771007 := bstep (se 1 (by rfl) ⟨3578255, by rfl⟩ : syracuseStep 4771007 = 7156511) B7156511
theorem B3180671 : Blo 2119435 3180671 := bstep (se 1 (by rfl) ⟨2385503, by rfl⟩ : syracuseStep 3180671 = 4771007) B4771007
theorem B2120447 : Blo 2119435 2120447 := bstep (se 1 (by rfl) ⟨1590335, by rfl⟩ : syracuseStep 2120447 = 3180671) B3180671
theorem B3180677 : Blo 2119435 3180677 := bbase (se 4 (by rfl) ⟨298188, by rfl⟩ : syracuseStep 3180677 = 596377) (by norm_num)
theorem B2120451 : Blo 2119435 2120451 := bstep (se 1 (by rfl) ⟨1590338, by rfl⟩ : syracuseStep 2120451 = 3180677) B3180677
theorem B3578269 : Blo 2119435 3578269 := bbase (se 3 (by rfl) ⟨670925, by rfl⟩ : syracuseStep 3578269 = 1341851) (by norm_num)
theorem B4771025 : Blo 2119435 4771025 := bstep (se 2 (by rfl) ⟨1789134, by rfl⟩ : syracuseStep 4771025 = 3578269) B3578269
theorem B3180683 : Blo 2119435 3180683 := bstep (se 1 (by rfl) ⟨2385512, by rfl⟩ : syracuseStep 3180683 = 4771025) B4771025
theorem B2120455 : Blo 2119435 2120455 := bstep (se 1 (by rfl) ⟨1590341, by rfl⟩ : syracuseStep 2120455 = 3180683) B3180683
theorem B2385517 : Blo 2119435 2385517 := bbase (se 3 (by rfl) ⟨447284, by rfl⟩ : syracuseStep 2385517 = 894569) (by norm_num)
theorem B3180689 : Blo 2119435 3180689 := bstep (se 2 (by rfl) ⟨1192758, by rfl⟩ : syracuseStep 3180689 = 2385517) B2385517
theorem B2120459 : Blo 2119435 2120459 := bstep (se 1 (by rfl) ⟨1590344, by rfl⟩ : syracuseStep 2120459 = 3180689) B3180689
theorem B7156565 : Blo 2119435 7156565 := bbase (se 9 (by rfl) ⟨20966, by rfl⟩ : syracuseStep 7156565 = 41933) (by norm_num)
theorem B4771043 : Blo 2119435 4771043 := bstep (se 1 (by rfl) ⟨3578282, by rfl⟩ : syracuseStep 4771043 = 7156565) B7156565
theorem B3180695 : Blo 2119435 3180695 := bstep (se 1 (by rfl) ⟨2385521, by rfl⟩ : syracuseStep 3180695 = 4771043) B4771043
theorem B2120463 : Blo 2119435 2120463 := bstep (se 1 (by rfl) ⟨1590347, by rfl⟩ : syracuseStep 2120463 = 3180695) B3180695
theorem B3180701 : Blo 2119435 3180701 := bbase (se 3 (by rfl) ⟨596381, by rfl⟩ : syracuseStep 3180701 = 1192763) (by norm_num)
theorem B2120467 : Blo 2119435 2120467 := bstep (se 1 (by rfl) ⟨1590350, by rfl⟩ : syracuseStep 2120467 = 3180701) B3180701
theorem B4771061 : Blo 2119435 4771061 := bbase (se 5 (by rfl) ⟨223643, by rfl⟩ : syracuseStep 4771061 = 447287) (by norm_num)
theorem B3180707 : Blo 2119435 3180707 := bstep (se 1 (by rfl) ⟨2385530, by rfl⟩ : syracuseStep 3180707 = 4771061) B4771061
theorem B2120471 : Blo 2119435 2120471 := bstep (se 1 (by rfl) ⟨1590353, by rfl⟩ : syracuseStep 2120471 = 3180707) B3180707
theorem B10612565 : Blo 2119435 10612565 := bbase (se 9 (by rfl) ⟨31091, by rfl⟩ : syracuseStep 10612565 = 62183) (by norm_num)
theorem B7075043 : Blo 2119435 7075043 := bstep (se 1 (by rfl) ⟨5306282, by rfl⟩ : syracuseStep 7075043 = 10612565) B10612565
theorem B4716695 : Blo 2119435 4716695 := bstep (se 1 (by rfl) ⟨3537521, by rfl⟩ : syracuseStep 4716695 = 7075043) B7075043
theorem B12577853 : Blo 2119435 12577853 := bstep (se 3 (by rfl) ⟨2358347, by rfl⟩ : syracuseStep 12577853 = 4716695) B4716695
theorem B33540941 : Blo 2119435 33540941 := bstep (se 3 (by rfl) ⟨6288926, by rfl⟩ : syracuseStep 33540941 = 12577853) B12577853
theorem B22360627 : Blo 2119435 22360627 := bstep (se 1 (by rfl) ⟨16770470, by rfl⟩ : syracuseStep 22360627 = 33540941) B33540941
theorem B29814169 : Blo 2119435 29814169 := bstep (se 2 (by rfl) ⟨11180313, by rfl⟩ : syracuseStep 29814169 = 22360627) B22360627
theorem B39752225 : Blo 2119435 39752225 := bstep (se 2 (by rfl) ⟨14907084, by rfl⟩ : syracuseStep 39752225 = 29814169) B29814169
theorem B26501483 : Blo 2119435 26501483 := bstep (se 1 (by rfl) ⟨19876112, by rfl⟩ : syracuseStep 26501483 = 39752225) B39752225
theorem B17667655 : Blo 2119435 17667655 := bstep (se 1 (by rfl) ⟨13250741, by rfl⟩ : syracuseStep 17667655 = 26501483) B26501483
theorem B376909973 : Blo 2119435 376909973 := bstep (se 6 (by rfl) ⟨8833827, by rfl⟩ : syracuseStep 376909973 = 17667655) B17667655
theorem B251273315 : Blo 2119435 251273315 := bstep (se 1 (by rfl) ⟨188454986, by rfl⟩ : syracuseStep 251273315 = 376909973) B376909973
theorem B167515543 : Blo 2119435 167515543 := bstep (se 1 (by rfl) ⟨125636657, by rfl⟩ : syracuseStep 167515543 = 251273315) B251273315
theorem B223354057 : Blo 2119435 223354057 := bstep (se 2 (by rfl) ⟨83757771, by rfl⟩ : syracuseStep 223354057 = 167515543) B167515543
theorem B297805409 : Blo 2119435 297805409 := bstep (se 2 (by rfl) ⟨111677028, by rfl⟩ : syracuseStep 297805409 = 223354057) B223354057
theorem B198536939 : Blo 2119435 198536939 := bstep (se 1 (by rfl) ⟨148902704, by rfl⟩ : syracuseStep 198536939 = 297805409) B297805409
theorem B132357959 : Blo 2119435 132357959 := bstep (se 1 (by rfl) ⟨99268469, by rfl⟩ : syracuseStep 132357959 = 198536939) B198536939
theorem B88238639 : Blo 2119435 88238639 := bstep (se 1 (by rfl) ⟨66178979, by rfl⟩ : syracuseStep 88238639 = 132357959) B132357959
theorem B58825759 : Blo 2119435 58825759 := bstep (se 1 (by rfl) ⟨44119319, by rfl⟩ : syracuseStep 58825759 = 88238639) B88238639
theorem B78434345 : Blo 2119435 78434345 := bstep (se 2 (by rfl) ⟨29412879, by rfl⟩ : syracuseStep 78434345 = 58825759) B58825759
theorem B52289563 : Blo 2119435 52289563 := bstep (se 1 (by rfl) ⟨39217172, by rfl⟩ : syracuseStep 52289563 = 78434345) B78434345
theorem B69719417 : Blo 2119435 69719417 := bstep (se 2 (by rfl) ⟨26144781, by rfl⟩ : syracuseStep 69719417 = 52289563) B52289563
theorem B46479611 : Blo 2119435 46479611 := bstep (se 1 (by rfl) ⟨34859708, by rfl⟩ : syracuseStep 46479611 = 69719417) B69719417
theorem B30986407 : Blo 2119435 30986407 := bstep (se 1 (by rfl) ⟨23239805, by rfl⟩ : syracuseStep 30986407 = 46479611) B46479611
theorem B165260837 : Blo 2119435 165260837 := bstep (se 4 (by rfl) ⟨15493203, by rfl⟩ : syracuseStep 165260837 = 30986407) B30986407
theorem B110173891 : Blo 2119435 110173891 := bstep (se 1 (by rfl) ⟨82630418, by rfl⟩ : syracuseStep 110173891 = 165260837) B165260837
theorem B146898521 : Blo 2119435 146898521 := bstep (se 2 (by rfl) ⟨55086945, by rfl⟩ : syracuseStep 146898521 = 110173891) B110173891
theorem B97932347 : Blo 2119435 97932347 := bstep (se 1 (by rfl) ⟨73449260, by rfl⟩ : syracuseStep 97932347 = 146898521) B146898521
theorem B65288231 : Blo 2119435 65288231 := bstep (se 1 (by rfl) ⟨48966173, by rfl⟩ : syracuseStep 65288231 = 97932347) B97932347
theorem B43525487 : Blo 2119435 43525487 := bstep (se 1 (by rfl) ⟨32644115, by rfl⟩ : syracuseStep 43525487 = 65288231) B65288231
theorem B29016991 : Blo 2119435 29016991 := bstep (se 1 (by rfl) ⟨21762743, by rfl⟩ : syracuseStep 29016991 = 43525487) B43525487
theorem B38689321 : Blo 2119435 38689321 := bstep (se 2 (by rfl) ⟨14508495, by rfl⟩ : syracuseStep 38689321 = 29016991) B29016991
theorem B51585761 : Blo 2119435 51585761 := bstep (se 2 (by rfl) ⟨19344660, by rfl⟩ : syracuseStep 51585761 = 38689321) B38689321
theorem B34390507 : Blo 2119435 34390507 := bstep (se 1 (by rfl) ⟨25792880, by rfl⟩ : syracuseStep 34390507 = 51585761) B51585761
theorem B45854009 : Blo 2119435 45854009 := bstep (se 2 (by rfl) ⟨17195253, by rfl⟩ : syracuseStep 45854009 = 34390507) B34390507
theorem B30569339 : Blo 2119435 30569339 := bstep (se 1 (by rfl) ⟨22927004, by rfl⟩ : syracuseStep 30569339 = 45854009) B45854009
theorem B20379559 : Blo 2119435 20379559 := bstep (se 1 (by rfl) ⟨15284669, by rfl⟩ : syracuseStep 20379559 = 30569339) B30569339
theorem B27172745 : Blo 2119435 27172745 := bstep (se 2 (by rfl) ⟨10189779, by rfl⟩ : syracuseStep 27172745 = 20379559) B20379559
theorem B18115163 : Blo 2119435 18115163 := bstep (se 1 (by rfl) ⟨13586372, by rfl⟩ : syracuseStep 18115163 = 27172745) B27172745
theorem B12076775 : Blo 2119435 12076775 := bstep (se 1 (by rfl) ⟨9057581, by rfl⟩ : syracuseStep 12076775 = 18115163) B18115163
theorem B8051183 : Blo 2119435 8051183 := bstep (se 1 (by rfl) ⟨6038387, by rfl⟩ : syracuseStep 8051183 = 12076775) B12076775
theorem B5367455 : Blo 2119435 5367455 := bstep (se 1 (by rfl) ⟨4025591, by rfl⟩ : syracuseStep 5367455 = 8051183) B8051183
theorem B3578303 : Blo 2119435 3578303 := bstep (se 1 (by rfl) ⟨2683727, by rfl⟩ : syracuseStep 3578303 = 5367455) B5367455
theorem B2385535 : Blo 2119435 2385535 := bstep (se 1 (by rfl) ⟨1789151, by rfl⟩ : syracuseStep 2385535 = 3578303) B3578303
theorem B3180713 : Blo 2119435 3180713 := bstep (se 2 (by rfl) ⟨1192767, by rfl⟩ : syracuseStep 3180713 = 2385535) B2385535
theorem B2120475 : Blo 2119435 2120475 := bstep (se 1 (by rfl) ⟨1590356, by rfl⟩ : syracuseStep 2120475 = 3180713) B3180713
theorem B4590589 : Blo 2119435 4590589 := bbase (se 3 (by rfl) ⟨860735, by rfl⟩ : syracuseStep 4590589 = 1721471) (by norm_num)
theorem B6120785 : Blo 2119435 6120785 := bstep (se 2 (by rfl) ⟨2295294, by rfl⟩ : syracuseStep 6120785 = 4590589) B4590589
theorem B4080523 : Blo 2119435 4080523 := bstep (se 1 (by rfl) ⟨3060392, by rfl⟩ : syracuseStep 4080523 = 6120785) B6120785
theorem B5440697 : Blo 2119435 5440697 := bstep (se 2 (by rfl) ⟨2040261, by rfl⟩ : syracuseStep 5440697 = 4080523) B4080523
theorem B3627131 : Blo 2119435 3627131 := bstep (se 1 (by rfl) ⟨2720348, by rfl⟩ : syracuseStep 3627131 = 5440697) B5440697
theorem B38689397 : Blo 2119435 38689397 := bstep (se 5 (by rfl) ⟨1813565, by rfl⟩ : syracuseStep 38689397 = 3627131) B3627131
theorem B25792931 : Blo 2119435 25792931 := bstep (se 1 (by rfl) ⟨19344698, by rfl⟩ : syracuseStep 25792931 = 38689397) B38689397
theorem B17195287 : Blo 2119435 17195287 := bstep (se 1 (by rfl) ⟨12896465, by rfl⟩ : syracuseStep 17195287 = 25792931) B25792931
theorem B22927049 : Blo 2119435 22927049 := bstep (se 2 (by rfl) ⟨8597643, by rfl⟩ : syracuseStep 22927049 = 17195287) B17195287
theorem B15284699 : Blo 2119435 15284699 := bstep (se 1 (by rfl) ⟨11463524, by rfl⟩ : syracuseStep 15284699 = 22927049) B22927049
theorem B10189799 : Blo 2119435 10189799 := bstep (se 1 (by rfl) ⟨7642349, by rfl⟩ : syracuseStep 10189799 = 15284699) B15284699
theorem B6793199 : Blo 2119435 6793199 := bstep (se 1 (by rfl) ⟨5094899, by rfl⟩ : syracuseStep 6793199 = 10189799) B10189799
theorem B4528799 : Blo 2119435 4528799 := bstep (se 1 (by rfl) ⟨3396599, by rfl⟩ : syracuseStep 4528799 = 6793199) B6793199
theorem B3019199 : Blo 2119435 3019199 := bstep (se 1 (by rfl) ⟨2264399, by rfl⟩ : syracuseStep 3019199 = 4528799) B4528799
theorem B8051197 : Blo 2119435 8051197 := bstep (se 3 (by rfl) ⟨1509599, by rfl⟩ : syracuseStep 8051197 = 3019199) B3019199
theorem B10734929 : Blo 2119435 10734929 := bstep (se 2 (by rfl) ⟨4025598, by rfl⟩ : syracuseStep 10734929 = 8051197) B8051197
theorem B7156619 : Blo 2119435 7156619 := bstep (se 1 (by rfl) ⟨5367464, by rfl⟩ : syracuseStep 7156619 = 10734929) B10734929
theorem B4771079 : Blo 2119435 4771079 := bstep (se 1 (by rfl) ⟨3578309, by rfl⟩ : syracuseStep 4771079 = 7156619) B7156619
theorem B3180719 : Blo 2119435 3180719 := bstep (se 1 (by rfl) ⟨2385539, by rfl⟩ : syracuseStep 3180719 = 4771079) B4771079
theorem B2120479 : Blo 2119435 2120479 := bstep (se 1 (by rfl) ⟨1590359, by rfl⟩ : syracuseStep 2120479 = 3180719) B3180719
theorem B3180725 : Blo 2119435 3180725 := bbase (se 5 (by rfl) ⟨149096, by rfl⟩ : syracuseStep 3180725 = 298193) (by norm_num)
theorem B2120483 : Blo 2119435 2120483 := bstep (se 1 (by rfl) ⟨1590362, by rfl⟩ : syracuseStep 2120483 = 3180725) B3180725
theorem B5367485 : Blo 2119435 5367485 := bbase (se 3 (by rfl) ⟨1006403, by rfl⟩ : syracuseStep 5367485 = 2012807) (by norm_num)
theorem B3578323 : Blo 2119435 3578323 := bstep (se 1 (by rfl) ⟨2683742, by rfl⟩ : syracuseStep 3578323 = 5367485) B5367485
theorem B4771097 : Blo 2119435 4771097 := bstep (se 2 (by rfl) ⟨1789161, by rfl⟩ : syracuseStep 4771097 = 3578323) B3578323
theorem B3180731 : Blo 2119435 3180731 := bstep (se 1 (by rfl) ⟨2385548, by rfl⟩ : syracuseStep 3180731 = 4771097) B4771097
theorem B2120487 : Blo 2119435 2120487 := bstep (se 1 (by rfl) ⟨1590365, by rfl⟩ : syracuseStep 2120487 = 3180731) B3180731
theorem B2385553 : Blo 2119435 2385553 := bbase (se 2 (by rfl) ⟨894582, by rfl⟩ : syracuseStep 2385553 = 1789165) (by norm_num)
theorem B3180737 : Blo 2119435 3180737 := bstep (se 2 (by rfl) ⟨1192776, by rfl⟩ : syracuseStep 3180737 = 2385553) B2385553
theorem B2120491 : Blo 2119435 2120491 := bstep (se 1 (by rfl) ⟨1590368, by rfl⟩ : syracuseStep 2120491 = 3180737) B3180737
theorem B4025629 : Blo 2119435 4025629 := bbase (se 3 (by rfl) ⟨754805, by rfl⟩ : syracuseStep 4025629 = 1509611) (by norm_num)
theorem B5367505 : Blo 2119435 5367505 := bstep (se 2 (by rfl) ⟨2012814, by rfl⟩ : syracuseStep 5367505 = 4025629) B4025629
theorem B7156673 : Blo 2119435 7156673 := bstep (se 2 (by rfl) ⟨2683752, by rfl⟩ : syracuseStep 7156673 = 5367505) B5367505
theorem B4771115 : Blo 2119435 4771115 := bstep (se 1 (by rfl) ⟨3578336, by rfl⟩ : syracuseStep 4771115 = 7156673) B7156673
theorem B3180743 : Blo 2119435 3180743 := bstep (se 1 (by rfl) ⟨2385557, by rfl⟩ : syracuseStep 3180743 = 4771115) B4771115
theorem B2120495 : Blo 2119435 2120495 := bstep (se 1 (by rfl) ⟨1590371, by rfl⟩ : syracuseStep 2120495 = 3180743) B3180743
theorem B3180749 : Blo 2119435 3180749 := bbase (se 3 (by rfl) ⟨596390, by rfl⟩ : syracuseStep 3180749 = 1192781) (by norm_num)
theorem B2120499 : Blo 2119435 2120499 := bstep (se 1 (by rfl) ⟨1590374, by rfl⟩ : syracuseStep 2120499 = 3180749) B3180749
theorem B4771133 : Blo 2119435 4771133 := bbase (se 3 (by rfl) ⟨894587, by rfl⟩ : syracuseStep 4771133 = 1789175) (by norm_num)
theorem B3180755 : Blo 2119435 3180755 := bstep (se 1 (by rfl) ⟨2385566, by rfl⟩ : syracuseStep 3180755 = 4771133) B4771133
theorem B2120503 : Blo 2119435 2120503 := bstep (se 1 (by rfl) ⟨1590377, by rfl⟩ : syracuseStep 2120503 = 3180755) B3180755
theorem B3578357 : Blo 2119435 3578357 := bbase (se 5 (by rfl) ⟨167735, by rfl⟩ : syracuseStep 3578357 = 335471) (by norm_num)
theorem B2385571 : Blo 2119435 2385571 := bstep (se 1 (by rfl) ⟨1789178, by rfl⟩ : syracuseStep 2385571 = 3578357) B3578357
theorem B3180761 : Blo 2119435 3180761 := bstep (se 2 (by rfl) ⟨1192785, by rfl⟩ : syracuseStep 3180761 = 2385571) B2385571
theorem B2120507 : Blo 2119435 2120507 := bstep (se 1 (by rfl) ⟨1590380, by rfl⟩ : syracuseStep 2120507 = 3180761) B3180761
theorem B6793301 : Blo 2119435 6793301 := bbase (se 8 (by rfl) ⟨39804, by rfl⟩ : syracuseStep 6793301 = 79609) (by norm_num)
theorem B4528867 : Blo 2119435 4528867 := bstep (se 1 (by rfl) ⟨3396650, by rfl⟩ : syracuseStep 4528867 = 6793301) B6793301
theorem B6038489 : Blo 2119435 6038489 := bstep (se 2 (by rfl) ⟨2264433, by rfl⟩ : syracuseStep 6038489 = 4528867) B4528867
theorem B16102637 : Blo 2119435 16102637 := bstep (se 3 (by rfl) ⟨3019244, by rfl⟩ : syracuseStep 16102637 = 6038489) B6038489
theorem B10735091 : Blo 2119435 10735091 := bstep (se 1 (by rfl) ⟨8051318, by rfl⟩ : syracuseStep 10735091 = 16102637) B16102637
theorem B7156727 : Blo 2119435 7156727 := bstep (se 1 (by rfl) ⟨5367545, by rfl⟩ : syracuseStep 7156727 = 10735091) B10735091
theorem B4771151 : Blo 2119435 4771151 := bstep (se 1 (by rfl) ⟨3578363, by rfl⟩ : syracuseStep 4771151 = 7156727) B7156727
theorem B3180767 : Blo 2119435 3180767 := bstep (se 1 (by rfl) ⟨2385575, by rfl⟩ : syracuseStep 3180767 = 4771151) B4771151
theorem B2120511 : Blo 2119435 2120511 := bstep (se 1 (by rfl) ⟨1590383, by rfl⟩ : syracuseStep 2120511 = 3180767) B3180767
theorem B3180773 : Blo 2119435 3180773 := bbase (se 4 (by rfl) ⟨298197, by rfl⟩ : syracuseStep 3180773 = 596395) (by norm_num)
theorem B2120515 : Blo 2119435 2120515 := bstep (se 1 (by rfl) ⟨1590386, by rfl⟩ : syracuseStep 2120515 = 3180773) B3180773
theorem B4528885 : Blo 2119435 4528885 := bbase (se 5 (by rfl) ⟨212291, by rfl⟩ : syracuseStep 4528885 = 424583) (by norm_num)
theorem B6038513 : Blo 2119435 6038513 := bstep (se 2 (by rfl) ⟨2264442, by rfl⟩ : syracuseStep 6038513 = 4528885) B4528885
theorem B4025675 : Blo 2119435 4025675 := bstep (se 1 (by rfl) ⟨3019256, by rfl⟩ : syracuseStep 4025675 = 6038513) B6038513
theorem B2683783 : Blo 2119435 2683783 := bstep (se 1 (by rfl) ⟨2012837, by rfl⟩ : syracuseStep 2683783 = 4025675) B4025675
theorem B3578377 : Blo 2119435 3578377 := bstep (se 2 (by rfl) ⟨1341891, by rfl⟩ : syracuseStep 3578377 = 2683783) B2683783
theorem B4771169 : Blo 2119435 4771169 := bstep (se 2 (by rfl) ⟨1789188, by rfl⟩ : syracuseStep 4771169 = 3578377) B3578377
theorem B3180779 : Blo 2119435 3180779 := bstep (se 1 (by rfl) ⟨2385584, by rfl⟩ : syracuseStep 3180779 = 4771169) B4771169
theorem B2120519 : Blo 2119435 2120519 := bstep (se 1 (by rfl) ⟨1590389, by rfl⟩ : syracuseStep 2120519 = 3180779) B3180779
theorem B2385589 : Blo 2119435 2385589 := bbase (se 5 (by rfl) ⟨111824, by rfl⟩ : syracuseStep 2385589 = 223649) (by norm_num)
theorem B3180785 : Blo 2119435 3180785 := bstep (se 2 (by rfl) ⟨1192794, by rfl⟩ : syracuseStep 3180785 = 2385589) B2385589
theorem B2120523 : Blo 2119435 2120523 := bstep (se 1 (by rfl) ⟨1590392, by rfl⟩ : syracuseStep 2120523 = 3180785) B3180785
theorem B2683793 : Blo 2119435 2683793 := bbase (se 2 (by rfl) ⟨1006422, by rfl⟩ : syracuseStep 2683793 = 2012845) (by norm_num)
theorem B7156781 : Blo 2119435 7156781 := bstep (se 3 (by rfl) ⟨1341896, by rfl⟩ : syracuseStep 7156781 = 2683793) B2683793
theorem B4771187 : Blo 2119435 4771187 := bstep (se 1 (by rfl) ⟨3578390, by rfl⟩ : syracuseStep 4771187 = 7156781) B7156781
theorem B3180791 : Blo 2119435 3180791 := bstep (se 1 (by rfl) ⟨2385593, by rfl⟩ : syracuseStep 3180791 = 4771187) B4771187
theorem B2120527 : Blo 2119435 2120527 := bstep (se 1 (by rfl) ⟨1590395, by rfl⟩ : syracuseStep 2120527 = 3180791) B3180791
theorem B3180797 : Blo 2119435 3180797 := bbase (se 3 (by rfl) ⟨596399, by rfl⟩ : syracuseStep 3180797 = 1192799) (by norm_num)
theorem B2120531 : Blo 2119435 2120531 := bstep (se 1 (by rfl) ⟨1590398, by rfl⟩ : syracuseStep 2120531 = 3180797) B3180797
theorem B4771205 : Blo 2119435 4771205 := bbase (se 4 (by rfl) ⟨447300, by rfl⟩ : syracuseStep 4771205 = 894601) (by norm_num)
theorem B3180803 : Blo 2119435 3180803 := bstep (se 1 (by rfl) ⟨2385602, by rfl⟩ : syracuseStep 3180803 = 4771205) B4771205
theorem B2120535 : Blo 2119435 2120535 := bstep (se 1 (by rfl) ⟨1590401, by rfl⟩ : syracuseStep 2120535 = 3180803) B3180803
theorem B3019285 : Blo 2119435 3019285 := bbase (se 6 (by rfl) ⟨70764, by rfl⟩ : syracuseStep 3019285 = 141529) (by norm_num)
theorem B4025713 : Blo 2119435 4025713 := bstep (se 2 (by rfl) ⟨1509642, by rfl⟩ : syracuseStep 4025713 = 3019285) B3019285
theorem B5367617 : Blo 2119435 5367617 := bstep (se 2 (by rfl) ⟨2012856, by rfl⟩ : syracuseStep 5367617 = 4025713) B4025713
theorem B3578411 : Blo 2119435 3578411 := bstep (se 1 (by rfl) ⟨2683808, by rfl⟩ : syracuseStep 3578411 = 5367617) B5367617
theorem B2385607 : Blo 2119435 2385607 := bstep (se 1 (by rfl) ⟨1789205, by rfl⟩ : syracuseStep 2385607 = 3578411) B3578411
theorem B3180809 : Blo 2119435 3180809 := bstep (se 2 (by rfl) ⟨1192803, by rfl⟩ : syracuseStep 3180809 = 2385607) B2385607
theorem B2120539 : Blo 2119435 2120539 := bstep (se 1 (by rfl) ⟨1590404, by rfl⟩ : syracuseStep 2120539 = 3180809) B3180809
theorem B10735253 : Blo 2119435 10735253 := bbase (se 6 (by rfl) ⟨251607, by rfl⟩ : syracuseStep 10735253 = 503215) (by norm_num)
theorem B7156835 : Blo 2119435 7156835 := bstep (se 1 (by rfl) ⟨5367626, by rfl⟩ : syracuseStep 7156835 = 10735253) B10735253
theorem B4771223 : Blo 2119435 4771223 := bstep (se 1 (by rfl) ⟨3578417, by rfl⟩ : syracuseStep 4771223 = 7156835) B7156835
theorem B3180815 : Blo 2119435 3180815 := bstep (se 1 (by rfl) ⟨2385611, by rfl⟩ : syracuseStep 3180815 = 4771223) B4771223
theorem B2120543 : Blo 2119435 2120543 := bstep (se 1 (by rfl) ⟨1590407, by rfl⟩ : syracuseStep 2120543 = 3180815) B3180815
theorem B3180821 : Blo 2119435 3180821 := bbase (se 6 (by rfl) ⟨74550, by rfl⟩ : syracuseStep 3180821 = 149101) (by norm_num)
theorem B2120547 : Blo 2119435 2120547 := bstep (se 1 (by rfl) ⟨1590410, by rfl⟩ : syracuseStep 2120547 = 3180821) B3180821
theorem B27173717 : Blo 2119435 27173717 := bbase (se 9 (by rfl) ⟨79610, by rfl⟩ : syracuseStep 27173717 = 159221) (by norm_num)
theorem B18115811 : Blo 2119435 18115811 := bstep (se 1 (by rfl) ⟨13586858, by rfl⟩ : syracuseStep 18115811 = 27173717) B27173717
theorem B12077207 : Blo 2119435 12077207 := bstep (se 1 (by rfl) ⟨9057905, by rfl⟩ : syracuseStep 12077207 = 18115811) B18115811
theorem B8051471 : Blo 2119435 8051471 := bstep (se 1 (by rfl) ⟨6038603, by rfl⟩ : syracuseStep 8051471 = 12077207) B12077207
theorem B5367647 : Blo 2119435 5367647 := bstep (se 1 (by rfl) ⟨4025735, by rfl⟩ : syracuseStep 5367647 = 8051471) B8051471
theorem B3578431 : Blo 2119435 3578431 := bstep (se 1 (by rfl) ⟨2683823, by rfl⟩ : syracuseStep 3578431 = 5367647) B5367647
theorem B4771241 : Blo 2119435 4771241 := bstep (se 2 (by rfl) ⟨1789215, by rfl⟩ : syracuseStep 4771241 = 3578431) B3578431
theorem B3180827 : Blo 2119435 3180827 := bstep (se 1 (by rfl) ⟨2385620, by rfl⟩ : syracuseStep 3180827 = 4771241) B4771241
theorem B2120551 : Blo 2119435 2120551 := bstep (se 1 (by rfl) ⟨1590413, by rfl⟩ : syracuseStep 2120551 = 3180827) B3180827
theorem B2385625 : Blo 2119435 2385625 := bbase (se 2 (by rfl) ⟨894609, by rfl⟩ : syracuseStep 2385625 = 1789219) (by norm_num)
theorem B3180833 : Blo 2119435 3180833 := bstep (se 2 (by rfl) ⟨1192812, by rfl⟩ : syracuseStep 3180833 = 2385625) B2385625
theorem B2120555 : Blo 2119435 2120555 := bstep (se 1 (by rfl) ⟨1590416, by rfl⟩ : syracuseStep 2120555 = 3180833) B3180833
theorem B2264485 : Blo 2119435 2264485 := bbase (se 4 (by rfl) ⟨212295, by rfl⟩ : syracuseStep 2264485 = 424591) (by norm_num)
theorem B3019313 : Blo 2119435 3019313 := bstep (se 2 (by rfl) ⟨1132242, by rfl⟩ : syracuseStep 3019313 = 2264485) B2264485
theorem B8051501 : Blo 2119435 8051501 := bstep (se 3 (by rfl) ⟨1509656, by rfl⟩ : syracuseStep 8051501 = 3019313) B3019313
theorem B5367667 : Blo 2119435 5367667 := bstep (se 1 (by rfl) ⟨4025750, by rfl⟩ : syracuseStep 5367667 = 8051501) B8051501
theorem B7156889 : Blo 2119435 7156889 := bstep (se 2 (by rfl) ⟨2683833, by rfl⟩ : syracuseStep 7156889 = 5367667) B5367667
theorem B4771259 : Blo 2119435 4771259 := bstep (se 1 (by rfl) ⟨3578444, by rfl⟩ : syracuseStep 4771259 = 7156889) B7156889
theorem B3180839 : Blo 2119435 3180839 := bstep (se 1 (by rfl) ⟨2385629, by rfl⟩ : syracuseStep 3180839 = 4771259) B4771259
theorem B2120559 : Blo 2119435 2120559 := bstep (se 1 (by rfl) ⟨1590419, by rfl⟩ : syracuseStep 2120559 = 3180839) B3180839
theorem B3180845 : Blo 2119435 3180845 := bbase (se 3 (by rfl) ⟨596408, by rfl⟩ : syracuseStep 3180845 = 1192817) (by norm_num)
theorem B2120563 : Blo 2119435 2120563 := bstep (se 1 (by rfl) ⟨1590422, by rfl⟩ : syracuseStep 2120563 = 3180845) B3180845
theorem B4771277 : Blo 2119435 4771277 := bbase (se 3 (by rfl) ⟨894614, by rfl⟩ : syracuseStep 4771277 = 1789229) (by norm_num)
theorem B3180851 : Blo 2119435 3180851 := bstep (se 1 (by rfl) ⟨2385638, by rfl⟩ : syracuseStep 3180851 = 4771277) B4771277
theorem B2120567 : Blo 2119435 2120567 := bstep (se 1 (by rfl) ⟨1590425, by rfl⟩ : syracuseStep 2120567 = 3180851) B3180851
theorem B2683849 : Blo 2119435 2683849 := bbase (se 2 (by rfl) ⟨1006443, by rfl⟩ : syracuseStep 2683849 = 2012887) (by norm_num)
theorem B3578465 : Blo 2119435 3578465 := bstep (se 2 (by rfl) ⟨1341924, by rfl⟩ : syracuseStep 3578465 = 2683849) B2683849
theorem B2385643 : Blo 2119435 2385643 := bstep (se 1 (by rfl) ⟨1789232, by rfl⟩ : syracuseStep 2385643 = 3578465) B3578465
theorem B3180857 : Blo 2119435 3180857 := bstep (se 2 (by rfl) ⟨1192821, by rfl⟩ : syracuseStep 3180857 = 2385643) B2385643
theorem B2120571 : Blo 2119435 2120571 := bstep (se 1 (by rfl) ⟨1590428, by rfl⟩ : syracuseStep 2120571 = 3180857) B3180857
theorem B5732021 : Blo 2119435 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B3821347 : Blo 2119435 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B20380517 : Blo 2119435 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B13587011 : Blo 2119435 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B9058007 : Blo 2119435 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B24154685 : Blo 2119435 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B16103123 : Blo 2119435 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B10735415 : Blo 2119435 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B7156943 : Blo 2119435 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B4771295 : Blo 2119435 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B3180863 : Blo 2119435 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B2120575 : Blo 2119435 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B3180869 : Blo 2119435 3180869 := bbase (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) (by norm_num)
theorem B2120579 : Blo 2119435 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B3578485 : Blo 2119435 3578485 := bbase (se 5 (by rfl) ⟨167741, by rfl⟩ : syracuseStep 3578485 = 335483) (by norm_num)
theorem B4771313 : Blo 2119435 4771313 := bstep (se 2 (by rfl) ⟨1789242, by rfl⟩ : syracuseStep 4771313 = 3578485) B3578485
theorem B3180875 : Blo 2119435 3180875 := bstep (se 1 (by rfl) ⟨2385656, by rfl⟩ : syracuseStep 3180875 = 4771313) B4771313
theorem B2120583 : Blo 2119435 2120583 := bstep (se 1 (by rfl) ⟨1590437, by rfl⟩ : syracuseStep 2120583 = 3180875) B3180875
theorem B2385661 : Blo 2119435 2385661 := bbase (se 3 (by rfl) ⟨447311, by rfl⟩ : syracuseStep 2385661 = 894623) (by norm_num)
theorem B3180881 : Blo 2119435 3180881 := bstep (se 2 (by rfl) ⟨1192830, by rfl⟩ : syracuseStep 3180881 = 2385661) B2385661
theorem B2120587 : Blo 2119435 2120587 := bstep (se 1 (by rfl) ⟨1590440, by rfl⟩ : syracuseStep 2120587 = 3180881) B3180881
theorem B7156997 : Blo 2119435 7156997 := bbase (se 4 (by rfl) ⟨670968, by rfl⟩ : syracuseStep 7156997 = 1341937) (by norm_num)
theorem B4771331 : Blo 2119435 4771331 := bstep (se 1 (by rfl) ⟨3578498, by rfl⟩ : syracuseStep 4771331 = 7156997) B7156997
theorem B3180887 : Blo 2119435 3180887 := bstep (se 1 (by rfl) ⟨2385665, by rfl⟩ : syracuseStep 3180887 = 4771331) B4771331
theorem B2120591 : Blo 2119435 2120591 := bstep (se 1 (by rfl) ⟨1590443, by rfl⟩ : syracuseStep 2120591 = 3180887) B3180887
theorem B3180893 : Blo 2119435 3180893 := bbase (se 3 (by rfl) ⟨596417, by rfl⟩ : syracuseStep 3180893 = 1192835) (by norm_num)
theorem B2120595 : Blo 2119435 2120595 := bstep (se 1 (by rfl) ⟨1590446, by rfl⟩ : syracuseStep 2120595 = 3180893) B3180893
theorem B4771349 : Blo 2119435 4771349 := bbase (se 6 (by rfl) ⟨111828, by rfl⟩ : syracuseStep 4771349 = 223657) (by norm_num)
theorem B3180899 : Blo 2119435 3180899 := bstep (se 1 (by rfl) ⟨2385674, by rfl⟩ : syracuseStep 3180899 = 4771349) B4771349
theorem B2120599 : Blo 2119435 2120599 := bstep (se 1 (by rfl) ⟨1590449, by rfl⟩ : syracuseStep 2120599 = 3180899) B3180899
theorem B8051669 : Blo 2119435 8051669 := bbase (se 7 (by rfl) ⟨94355, by rfl⟩ : syracuseStep 8051669 = 188711) (by norm_num)
theorem B5367779 : Blo 2119435 5367779 := bstep (se 1 (by rfl) ⟨4025834, by rfl⟩ : syracuseStep 5367779 = 8051669) B8051669
theorem B3578519 : Blo 2119435 3578519 := bstep (se 1 (by rfl) ⟨2683889, by rfl⟩ : syracuseStep 3578519 = 5367779) B5367779
theorem B2385679 : Blo 2119435 2385679 := bstep (se 1 (by rfl) ⟨1789259, by rfl⟩ : syracuseStep 2385679 = 3578519) B3578519
theorem B3180905 : Blo 2119435 3180905 := bstep (se 2 (by rfl) ⟨1192839, by rfl⟩ : syracuseStep 3180905 = 2385679) B2385679
theorem B2120603 : Blo 2119435 2120603 := bstep (se 1 (by rfl) ⟨1590452, by rfl⟩ : syracuseStep 2120603 = 3180905) B3180905
theorem B12077525 : Blo 2119435 12077525 := bbase (se 7 (by rfl) ⟨141533, by rfl⟩ : syracuseStep 12077525 = 283067) (by norm_num)
theorem B8051683 : Blo 2119435 8051683 := bstep (se 1 (by rfl) ⟨6038762, by rfl⟩ : syracuseStep 8051683 = 12077525) B12077525
theorem B10735577 : Blo 2119435 10735577 := bstep (se 2 (by rfl) ⟨4025841, by rfl⟩ : syracuseStep 10735577 = 8051683) B8051683
theorem B7157051 : Blo 2119435 7157051 := bstep (se 1 (by rfl) ⟨5367788, by rfl⟩ : syracuseStep 7157051 = 10735577) B10735577
theorem B4771367 : Blo 2119435 4771367 := bstep (se 1 (by rfl) ⟨3578525, by rfl⟩ : syracuseStep 4771367 = 7157051) B7157051
theorem B3180911 : Blo 2119435 3180911 := bstep (se 1 (by rfl) ⟨2385683, by rfl⟩ : syracuseStep 3180911 = 4771367) B4771367
theorem B2120607 : Blo 2119435 2120607 := bstep (se 1 (by rfl) ⟨1590455, by rfl⟩ : syracuseStep 2120607 = 3180911) B3180911
theorem B3180917 : Blo 2119435 3180917 := bbase (se 5 (by rfl) ⟨149105, by rfl⟩ : syracuseStep 3180917 = 298211) (by norm_num)
theorem B2120611 : Blo 2119435 2120611 := bstep (se 1 (by rfl) ⟨1590458, by rfl⟩ : syracuseStep 2120611 = 3180917) B3180917
theorem B2264545 : Blo 2119435 2264545 := bbase (se 2 (by rfl) ⟨849204, by rfl⟩ : syracuseStep 2264545 = 1698409) (by norm_num)
theorem B3019393 : Blo 2119435 3019393 := bstep (se 2 (by rfl) ⟨1132272, by rfl⟩ : syracuseStep 3019393 = 2264545) B2264545
theorem B4025857 : Blo 2119435 4025857 := bstep (se 2 (by rfl) ⟨1509696, by rfl⟩ : syracuseStep 4025857 = 3019393) B3019393
theorem B5367809 : Blo 2119435 5367809 := bstep (se 2 (by rfl) ⟨2012928, by rfl⟩ : syracuseStep 5367809 = 4025857) B4025857
theorem B3578539 : Blo 2119435 3578539 := bstep (se 1 (by rfl) ⟨2683904, by rfl⟩ : syracuseStep 3578539 = 5367809) B5367809
theorem B4771385 : Blo 2119435 4771385 := bstep (se 2 (by rfl) ⟨1789269, by rfl⟩ : syracuseStep 4771385 = 3578539) B3578539
theorem B3180923 : Blo 2119435 3180923 := bstep (se 1 (by rfl) ⟨2385692, by rfl⟩ : syracuseStep 3180923 = 4771385) B4771385
theorem B2120615 : Blo 2119435 2120615 := bstep (se 1 (by rfl) ⟨1590461, by rfl⟩ : syracuseStep 2120615 = 3180923) B3180923
theorem B2385697 : Blo 2119435 2385697 := bbase (se 2 (by rfl) ⟨894636, by rfl⟩ : syracuseStep 2385697 = 1789273) (by norm_num)
theorem B3180929 : Blo 2119435 3180929 := bstep (se 2 (by rfl) ⟨1192848, by rfl⟩ : syracuseStep 3180929 = 2385697) B2385697
theorem B2120619 : Blo 2119435 2120619 := bstep (se 1 (by rfl) ⟨1590464, by rfl⟩ : syracuseStep 2120619 = 3180929) B3180929
theorem B5367829 : Blo 2119435 5367829 := bbase (se 6 (by rfl) ⟨125808, by rfl⟩ : syracuseStep 5367829 = 251617) (by norm_num)
theorem B7157105 : Blo 2119435 7157105 := bstep (se 2 (by rfl) ⟨2683914, by rfl⟩ : syracuseStep 7157105 = 5367829) B5367829
theorem B4771403 : Blo 2119435 4771403 := bstep (se 1 (by rfl) ⟨3578552, by rfl⟩ : syracuseStep 4771403 = 7157105) B7157105
theorem B3180935 : Blo 2119435 3180935 := bstep (se 1 (by rfl) ⟨2385701, by rfl⟩ : syracuseStep 3180935 = 4771403) B4771403
theorem B2120623 : Blo 2119435 2120623 := bstep (se 1 (by rfl) ⟨1590467, by rfl⟩ : syracuseStep 2120623 = 3180935) B3180935
theorem B3180941 : Blo 2119435 3180941 := bbase (se 3 (by rfl) ⟨596426, by rfl⟩ : syracuseStep 3180941 = 1192853) (by norm_num)
theorem B2120627 : Blo 2119435 2120627 := bstep (se 1 (by rfl) ⟨1590470, by rfl⟩ : syracuseStep 2120627 = 3180941) B3180941
theorem B4771421 : Blo 2119435 4771421 := bbase (se 3 (by rfl) ⟨894641, by rfl⟩ : syracuseStep 4771421 = 1789283) (by norm_num)
theorem B3180947 : Blo 2119435 3180947 := bstep (se 1 (by rfl) ⟨2385710, by rfl⟩ : syracuseStep 3180947 = 4771421) B4771421
theorem B2120631 : Blo 2119435 2120631 := bstep (se 1 (by rfl) ⟨1590473, by rfl⟩ : syracuseStep 2120631 = 3180947) B3180947
theorem B3578573 : Blo 2119435 3578573 := bbase (se 3 (by rfl) ⟨670982, by rfl⟩ : syracuseStep 3578573 = 1341965) (by norm_num)
theorem B2385715 : Blo 2119435 2385715 := bstep (se 1 (by rfl) ⟨1789286, by rfl⟩ : syracuseStep 2385715 = 3578573) B3578573
theorem B3180953 : Blo 2119435 3180953 := bstep (se 2 (by rfl) ⟨1192857, by rfl⟩ : syracuseStep 3180953 = 2385715) B2385715
theorem B2120635 : Blo 2119435 2120635 := bstep (se 1 (by rfl) ⟨1590476, by rfl⟩ : syracuseStep 2120635 = 3180953) B3180953
theorem B2149573 : Blo 2119435 2149573 := bbase (se 4 (by rfl) ⟨201522, by rfl⟩ : syracuseStep 2149573 = 403045) (by norm_num)
theorem B2866097 : Blo 2119435 2866097 := bstep (se 2 (by rfl) ⟨1074786, by rfl⟩ : syracuseStep 2866097 = 2149573) B2149573
theorem B7642925 : Blo 2119435 7642925 := bstep (se 3 (by rfl) ⟨1433048, by rfl⟩ : syracuseStep 7642925 = 2866097) B2866097
theorem B5095283 : Blo 2119435 5095283 := bstep (se 1 (by rfl) ⟨3821462, by rfl⟩ : syracuseStep 5095283 = 7642925) B7642925
theorem B13587421 : Blo 2119435 13587421 := bstep (se 3 (by rfl) ⟨2547641, by rfl⟩ : syracuseStep 13587421 = 5095283) B5095283
theorem B18116561 : Blo 2119435 18116561 := bstep (se 2 (by rfl) ⟨6793710, by rfl⟩ : syracuseStep 18116561 = 13587421) B13587421
theorem B12077707 : Blo 2119435 12077707 := bstep (se 1 (by rfl) ⟨9058280, by rfl⟩ : syracuseStep 12077707 = 18116561) B18116561
theorem B16103609 : Blo 2119435 16103609 := bstep (se 2 (by rfl) ⟨6038853, by rfl⟩ : syracuseStep 16103609 = 12077707) B12077707
theorem B10735739 : Blo 2119435 10735739 := bstep (se 1 (by rfl) ⟨8051804, by rfl⟩ : syracuseStep 10735739 = 16103609) B16103609
theorem B7157159 : Blo 2119435 7157159 := bstep (se 1 (by rfl) ⟨5367869, by rfl⟩ : syracuseStep 7157159 = 10735739) B10735739
theorem B4771439 : Blo 2119435 4771439 := bstep (se 1 (by rfl) ⟨3578579, by rfl⟩ : syracuseStep 4771439 = 7157159) B7157159
theorem B3180959 : Blo 2119435 3180959 := bstep (se 1 (by rfl) ⟨2385719, by rfl⟩ : syracuseStep 3180959 = 4771439) B4771439
theorem B2120639 : Blo 2119435 2120639 := bstep (se 1 (by rfl) ⟨1590479, by rfl⟩ : syracuseStep 2120639 = 3180959) B3180959
theorem B3180965 : Blo 2119435 3180965 := bbase (se 4 (by rfl) ⟨298215, by rfl⟩ : syracuseStep 3180965 = 596431) (by norm_num)
theorem B2120643 : Blo 2119435 2120643 := bstep (se 1 (by rfl) ⟨1590482, by rfl⟩ : syracuseStep 2120643 = 3180965) B3180965
theorem B2683945 : Blo 2119435 2683945 := bbase (se 2 (by rfl) ⟨1006479, by rfl⟩ : syracuseStep 2683945 = 2012959) (by norm_num)
theorem B3578593 : Blo 2119435 3578593 := bstep (se 2 (by rfl) ⟨1341972, by rfl⟩ : syracuseStep 3578593 = 2683945) B2683945
theorem B4771457 : Blo 2119435 4771457 := bstep (se 2 (by rfl) ⟨1789296, by rfl⟩ : syracuseStep 4771457 = 3578593) B3578593
theorem B3180971 : Blo 2119435 3180971 := bstep (se 1 (by rfl) ⟨2385728, by rfl⟩ : syracuseStep 3180971 = 4771457) B4771457
theorem B2120647 : Blo 2119435 2120647 := bstep (se 1 (by rfl) ⟨1590485, by rfl⟩ : syracuseStep 2120647 = 3180971) B3180971
theorem B2385733 : Blo 2119435 2385733 := bbase (se 4 (by rfl) ⟨223662, by rfl⟩ : syracuseStep 2385733 = 447325) (by norm_num)
theorem B3180977 : Blo 2119435 3180977 := bstep (se 2 (by rfl) ⟨1192866, by rfl⟩ : syracuseStep 3180977 = 2385733) B2385733
theorem B2120651 : Blo 2119435 2120651 := bstep (se 1 (by rfl) ⟨1590488, by rfl⟩ : syracuseStep 2120651 = 3180977) B3180977
theorem B4025933 : Blo 2119435 4025933 := bbase (se 3 (by rfl) ⟨754862, by rfl⟩ : syracuseStep 4025933 = 1509725) (by norm_num)
theorem B2683955 : Blo 2119435 2683955 := bstep (se 1 (by rfl) ⟨2012966, by rfl⟩ : syracuseStep 2683955 = 4025933) B4025933
theorem B7157213 : Blo 2119435 7157213 := bstep (se 3 (by rfl) ⟨1341977, by rfl⟩ : syracuseStep 7157213 = 2683955) B2683955
theorem B4771475 : Blo 2119435 4771475 := bstep (se 1 (by rfl) ⟨3578606, by rfl⟩ : syracuseStep 4771475 = 7157213) B7157213
theorem B3180983 : Blo 2119435 3180983 := bstep (se 1 (by rfl) ⟨2385737, by rfl⟩ : syracuseStep 3180983 = 4771475) B4771475
theorem B2120655 : Blo 2119435 2120655 := bstep (se 1 (by rfl) ⟨1590491, by rfl⟩ : syracuseStep 2120655 = 3180983) B3180983
theorem B3180989 : Blo 2119435 3180989 := bbase (se 3 (by rfl) ⟨596435, by rfl⟩ : syracuseStep 3180989 = 1192871) (by norm_num)
theorem B2120659 : Blo 2119435 2120659 := bstep (se 1 (by rfl) ⟨1590494, by rfl⟩ : syracuseStep 2120659 = 3180989) B3180989
theorem B4771493 : Blo 2119435 4771493 := bbase (se 4 (by rfl) ⟨447327, by rfl⟩ : syracuseStep 4771493 = 894655) (by norm_num)
theorem B3180995 : Blo 2119435 3180995 := bstep (se 1 (by rfl) ⟨2385746, by rfl⟩ : syracuseStep 3180995 = 4771493) B4771493
theorem B2120663 : Blo 2119435 2120663 := bstep (se 1 (by rfl) ⟨1590497, by rfl⟩ : syracuseStep 2120663 = 3180995) B3180995
theorem B5367941 : Blo 2119435 5367941 := bbase (se 4 (by rfl) ⟨503244, by rfl⟩ : syracuseStep 5367941 = 1006489) (by norm_num)
theorem B3578627 : Blo 2119435 3578627 := bstep (se 1 (by rfl) ⟨2683970, by rfl⟩ : syracuseStep 3578627 = 5367941) B5367941
theorem B2385751 : Blo 2119435 2385751 := bstep (se 1 (by rfl) ⟨1789313, by rfl⟩ : syracuseStep 2385751 = 3578627) B3578627
theorem B3181001 : Blo 2119435 3181001 := bstep (se 2 (by rfl) ⟨1192875, by rfl⟩ : syracuseStep 3181001 = 2385751) B2385751
theorem B2120667 : Blo 2119435 2120667 := bstep (se 1 (by rfl) ⟨1590500, by rfl⟩ : syracuseStep 2120667 = 3181001) B3181001
theorem B2866141 : Blo 2119435 2866141 := bbase (se 3 (by rfl) ⟨537401, by rfl⟩ : syracuseStep 2866141 = 1074803) (by norm_num)
theorem B3821521 : Blo 2119435 3821521 := bstep (se 2 (by rfl) ⟨1433070, by rfl⟩ : syracuseStep 3821521 = 2866141) B2866141
theorem B5095361 : Blo 2119435 5095361 := bstep (se 2 (by rfl) ⟨1910760, by rfl⟩ : syracuseStep 5095361 = 3821521) B3821521
theorem B3396907 : Blo 2119435 3396907 := bstep (se 1 (by rfl) ⟨2547680, by rfl⟩ : syracuseStep 3396907 = 5095361) B5095361
theorem B4529209 : Blo 2119435 4529209 := bstep (se 2 (by rfl) ⟨1698453, by rfl⟩ : syracuseStep 4529209 = 3396907) B3396907
theorem B6038945 : Blo 2119435 6038945 := bstep (se 2 (by rfl) ⟨2264604, by rfl⟩ : syracuseStep 6038945 = 4529209) B4529209
theorem B4025963 : Blo 2119435 4025963 := bstep (se 1 (by rfl) ⟨3019472, by rfl⟩ : syracuseStep 4025963 = 6038945) B6038945
theorem B10735901 : Blo 2119435 10735901 := bstep (se 3 (by rfl) ⟨2012981, by rfl⟩ : syracuseStep 10735901 = 4025963) B4025963
theorem B7157267 : Blo 2119435 7157267 := bstep (se 1 (by rfl) ⟨5367950, by rfl⟩ : syracuseStep 7157267 = 10735901) B10735901
theorem B4771511 : Blo 2119435 4771511 := bstep (se 1 (by rfl) ⟨3578633, by rfl⟩ : syracuseStep 4771511 = 7157267) B7157267
theorem B3181007 : Blo 2119435 3181007 := bstep (se 1 (by rfl) ⟨2385755, by rfl⟩ : syracuseStep 3181007 = 4771511) B4771511
theorem B2120671 : Blo 2119435 2120671 := bstep (se 1 (by rfl) ⟨1590503, by rfl⟩ : syracuseStep 2120671 = 3181007) B3181007
theorem B3181013 : Blo 2119435 3181013 := bbase (se 7 (by rfl) ⟨37277, by rfl⟩ : syracuseStep 3181013 = 74555) (by norm_num)
theorem B2120675 : Blo 2119435 2120675 := bstep (se 1 (by rfl) ⟨1590506, by rfl⟩ : syracuseStep 2120675 = 3181013) B3181013
theorem B8051957 : Blo 2119435 8051957 := bbase (se 5 (by rfl) ⟨377435, by rfl⟩ : syracuseStep 8051957 = 754871) (by norm_num)
theorem B5367971 : Blo 2119435 5367971 := bstep (se 1 (by rfl) ⟨4025978, by rfl⟩ : syracuseStep 5367971 = 8051957) B8051957
theorem B3578647 : Blo 2119435 3578647 := bstep (se 1 (by rfl) ⟨2683985, by rfl⟩ : syracuseStep 3578647 = 5367971) B5367971
theorem B4771529 : Blo 2119435 4771529 := bstep (se 2 (by rfl) ⟨1789323, by rfl⟩ : syracuseStep 4771529 = 3578647) B3578647
theorem B3181019 : Blo 2119435 3181019 := bstep (se 1 (by rfl) ⟨2385764, by rfl⟩ : syracuseStep 3181019 = 4771529) B4771529
theorem B2120679 : Blo 2119435 2120679 := bstep (se 1 (by rfl) ⟨1590509, by rfl⟩ : syracuseStep 2120679 = 3181019) B3181019
theorem B2385769 : Blo 2119435 2385769 := bbase (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) (by norm_num)
theorem B3181025 : Blo 2119435 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B2120683 : Blo 2119435 2120683 := bstep (se 1 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 2120683 = 3181025) B3181025
theorem B4653677 : Blo 2119435 4653677 := bbase (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) (by norm_num)
theorem B12409805 : Blo 2119435 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B33092813 : Blo 2119435 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B88247501 : Blo 2119435 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B58831667 : Blo 2119435 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B39221111 : Blo 2119435 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B26147407 : Blo 2119435 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B34863209 : Blo 2119435 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B23242139 : Blo 2119435 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B15494759 : Blo 2119435 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B10329839 : Blo 2119435 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B6886559 : Blo 2119435 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B18364157 : Blo 2119435 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B12242771 : Blo 2119435 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B8161847 : Blo 2119435 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B5441231 : Blo 2119435 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B3627487 : Blo 2119435 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B19346597 : Blo 2119435 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B12897731 : Blo 2119435 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B8598487 : Blo 2119435 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B11464649 : Blo 2119435 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B7643099 : Blo 2119435 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B5095399 : Blo 2119435 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B6793865 : Blo 2119435 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B4529243 : Blo 2119435 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B12077981 : Blo 2119435 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B8051987 : Blo 2119435 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B5367991 : Blo 2119435 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B7157321 : Blo 2119435 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B4771547 : Blo 2119435 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B3181031 : Blo 2119435 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B2120687 : Blo 2119435 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B3181037 : Blo 2119435 3181037 := bbase (se 3 (by rfl) ⟨596444, by rfl⟩ : syracuseStep 3181037 = 1192889) (by norm_num)
theorem B2120691 : Blo 2119435 2120691 := bstep (se 1 (by rfl) ⟨1590518, by rfl⟩ : syracuseStep 2120691 = 3181037) B3181037
theorem B4771565 : Blo 2119435 4771565 := bbase (se 3 (by rfl) ⟨894668, by rfl⟩ : syracuseStep 4771565 = 1789337) (by norm_num)
theorem B3181043 : Blo 2119435 3181043 := bstep (se 1 (by rfl) ⟨2385782, by rfl⟩ : syracuseStep 3181043 = 4771565) B4771565
theorem B2120695 : Blo 2119435 2120695 := bstep (se 1 (by rfl) ⟨1590521, by rfl⟩ : syracuseStep 2120695 = 3181043) B3181043
theorem B3821573 : Blo 2119435 3821573 := bbase (se 4 (by rfl) ⟨358272, by rfl⟩ : syracuseStep 3821573 = 716545) (by norm_num)
theorem B2547715 : Blo 2119435 2547715 := bstep (se 1 (by rfl) ⟨1910786, by rfl⟩ : syracuseStep 2547715 = 3821573) B3821573
theorem B3396953 : Blo 2119435 3396953 := bstep (se 2 (by rfl) ⟨1273857, by rfl⟩ : syracuseStep 3396953 = 2547715) B2547715
theorem B2264635 : Blo 2119435 2264635 := bstep (se 1 (by rfl) ⟨1698476, by rfl⟩ : syracuseStep 2264635 = 3396953) B3396953
theorem B3019513 : Blo 2119435 3019513 := bstep (se 2 (by rfl) ⟨1132317, by rfl⟩ : syracuseStep 3019513 = 2264635) B2264635
theorem B4026017 : Blo 2119435 4026017 := bstep (se 2 (by rfl) ⟨1509756, by rfl⟩ : syracuseStep 4026017 = 3019513) B3019513
theorem B2684011 : Blo 2119435 2684011 := bstep (se 1 (by rfl) ⟨2013008, by rfl⟩ : syracuseStep 2684011 = 4026017) B4026017
theorem B3578681 : Blo 2119435 3578681 := bstep (se 2 (by rfl) ⟨1342005, by rfl⟩ : syracuseStep 3578681 = 2684011) B2684011
theorem B2385787 : Blo 2119435 2385787 := bstep (se 1 (by rfl) ⟨1789340, by rfl⟩ : syracuseStep 2385787 = 3578681) B3578681
theorem B3181049 : Blo 2119435 3181049 := bstep (se 2 (by rfl) ⟨1192893, by rfl⟩ : syracuseStep 3181049 = 2385787) B2385787
theorem B2120699 : Blo 2119435 2120699 := bstep (se 1 (by rfl) ⟨1590524, by rfl⟩ : syracuseStep 2120699 = 3181049) B3181049
theorem B137576789 : Blo 2119435 137576789 := bbase (se 10 (by rfl) ⟨201528, by rfl⟩ : syracuseStep 137576789 = 403057) (by norm_num)
theorem B91717859 : Blo 2119435 91717859 := bstep (se 1 (by rfl) ⟨68788394, by rfl⟩ : syracuseStep 91717859 = 137576789) B137576789
theorem B61145239 : Blo 2119435 61145239 := bstep (se 1 (by rfl) ⟨45858929, by rfl⟩ : syracuseStep 61145239 = 91717859) B91717859
theorem B81526985 : Blo 2119435 81526985 := bstep (se 2 (by rfl) ⟨30572619, by rfl⟩ : syracuseStep 81526985 = 61145239) B61145239
theorem B54351323 : Blo 2119435 54351323 := bstep (se 1 (by rfl) ⟨40763492, by rfl⟩ : syracuseStep 54351323 = 81526985) B81526985
theorem B36234215 : Blo 2119435 36234215 := bstep (se 1 (by rfl) ⟨27175661, by rfl⟩ : syracuseStep 36234215 = 54351323) B54351323
theorem B24156143 : Blo 2119435 24156143 := bstep (se 1 (by rfl) ⟨18117107, by rfl⟩ : syracuseStep 24156143 = 36234215) B36234215
theorem B16104095 : Blo 2119435 16104095 := bstep (se 1 (by rfl) ⟨12078071, by rfl⟩ : syracuseStep 16104095 = 24156143) B24156143
theorem B10736063 : Blo 2119435 10736063 := bstep (se 1 (by rfl) ⟨8052047, by rfl⟩ : syracuseStep 10736063 = 16104095) B16104095
theorem B7157375 : Blo 2119435 7157375 := bstep (se 1 (by rfl) ⟨5368031, by rfl⟩ : syracuseStep 7157375 = 10736063) B10736063
theorem B4771583 : Blo 2119435 4771583 := bstep (se 1 (by rfl) ⟨3578687, by rfl⟩ : syracuseStep 4771583 = 7157375) B7157375
theorem B3181055 : Blo 2119435 3181055 := bstep (se 1 (by rfl) ⟨2385791, by rfl⟩ : syracuseStep 3181055 = 4771583) B4771583
theorem B2120703 : Blo 2119435 2120703 := bstep (se 1 (by rfl) ⟨1590527, by rfl⟩ : syracuseStep 2120703 = 3181055) B3181055
theorem B3181061 : Blo 2119435 3181061 := bbase (se 4 (by rfl) ⟨298224, by rfl⟩ : syracuseStep 3181061 = 596449) (by norm_num)
theorem B2120707 : Blo 2119435 2120707 := bstep (se 1 (by rfl) ⟨1590530, by rfl⟩ : syracuseStep 2120707 = 3181061) B3181061
theorem B3578701 : Blo 2119435 3578701 := bbase (se 3 (by rfl) ⟨671006, by rfl⟩ : syracuseStep 3578701 = 1342013) (by norm_num)
theorem B4771601 : Blo 2119435 4771601 := bstep (se 2 (by rfl) ⟨1789350, by rfl⟩ : syracuseStep 4771601 = 3578701) B3578701
theorem B3181067 : Blo 2119435 3181067 := bstep (se 1 (by rfl) ⟨2385800, by rfl⟩ : syracuseStep 3181067 = 4771601) B4771601
theorem B2120711 : Blo 2119435 2120711 := bstep (se 1 (by rfl) ⟨1590533, by rfl⟩ : syracuseStep 2120711 = 3181067) B3181067
theorem B2385805 : Blo 2119435 2385805 := bbase (se 3 (by rfl) ⟨447338, by rfl⟩ : syracuseStep 2385805 = 894677) (by norm_num)
theorem B3181073 : Blo 2119435 3181073 := bstep (se 2 (by rfl) ⟨1192902, by rfl⟩ : syracuseStep 3181073 = 2385805) B2385805
theorem B2120715 : Blo 2119435 2120715 := bstep (se 1 (by rfl) ⟨1590536, by rfl⟩ : syracuseStep 2120715 = 3181073) B3181073
theorem B7157429 : Blo 2119435 7157429 := bbase (se 5 (by rfl) ⟨335504, by rfl⟩ : syracuseStep 7157429 = 671009) (by norm_num)
theorem B4771619 : Blo 2119435 4771619 := bstep (se 1 (by rfl) ⟨3578714, by rfl⟩ : syracuseStep 4771619 = 7157429) B7157429
theorem B3181079 : Blo 2119435 3181079 := bstep (se 1 (by rfl) ⟨2385809, by rfl⟩ : syracuseStep 3181079 = 4771619) B4771619
theorem B2120719 : Blo 2119435 2120719 := bstep (se 1 (by rfl) ⟨1590539, by rfl⟩ : syracuseStep 2120719 = 3181079) B3181079
theorem B3181085 : Blo 2119435 3181085 := bbase (se 3 (by rfl) ⟨596453, by rfl⟩ : syracuseStep 3181085 = 1192907) (by norm_num)
theorem B2120723 : Blo 2119435 2120723 := bstep (se 1 (by rfl) ⟨1590542, by rfl⟩ : syracuseStep 2120723 = 3181085) B3181085
theorem B4771637 : Blo 2119435 4771637 := bbase (se 5 (by rfl) ⟨223670, by rfl⟩ : syracuseStep 4771637 = 447341) (by norm_num)
theorem B3181091 : Blo 2119435 3181091 := bstep (se 1 (by rfl) ⟨2385818, by rfl⟩ : syracuseStep 3181091 = 4771637) B4771637
theorem B2120727 : Blo 2119435 2120727 := bstep (se 1 (by rfl) ⟨1590545, by rfl⟩ : syracuseStep 2120727 = 3181091) B3181091
theorem B3821629 : Blo 2119435 3821629 := bbase (se 3 (by rfl) ⟨716555, by rfl⟩ : syracuseStep 3821629 = 1433111) (by norm_num)
theorem B5095505 : Blo 2119435 5095505 := bstep (se 2 (by rfl) ⟨1910814, by rfl⟩ : syracuseStep 5095505 = 3821629) B3821629
theorem B13588013 : Blo 2119435 13588013 := bstep (se 3 (by rfl) ⟨2547752, by rfl⟩ : syracuseStep 13588013 = 5095505) B5095505
theorem B9058675 : Blo 2119435 9058675 := bstep (se 1 (by rfl) ⟨6794006, by rfl⟩ : syracuseStep 9058675 = 13588013) B13588013
theorem B12078233 : Blo 2119435 12078233 := bstep (se 2 (by rfl) ⟨4529337, by rfl⟩ : syracuseStep 12078233 = 9058675) B9058675
theorem B8052155 : Blo 2119435 8052155 := bstep (se 1 (by rfl) ⟨6039116, by rfl⟩ : syracuseStep 8052155 = 12078233) B12078233
theorem B5368103 : Blo 2119435 5368103 := bstep (se 1 (by rfl) ⟨4026077, by rfl⟩ : syracuseStep 5368103 = 8052155) B8052155
theorem B3578735 : Blo 2119435 3578735 := bstep (se 1 (by rfl) ⟨2684051, by rfl⟩ : syracuseStep 3578735 = 5368103) B5368103
theorem B2385823 : Blo 2119435 2385823 := bstep (se 1 (by rfl) ⟨1789367, by rfl⟩ : syracuseStep 2385823 = 3578735) B3578735
theorem B3181097 : Blo 2119435 3181097 := bstep (se 2 (by rfl) ⟨1192911, by rfl⟩ : syracuseStep 3181097 = 2385823) B2385823
theorem B2120731 : Blo 2119435 2120731 := bstep (se 1 (by rfl) ⟨1590548, by rfl⟩ : syracuseStep 2120731 = 3181097) B3181097
theorem B2547757 : Blo 2119435 2547757 := bbase (se 3 (by rfl) ⟨477704, by rfl⟩ : syracuseStep 2547757 = 955409) (by norm_num)
theorem B13588037 : Blo 2119435 13588037 := bstep (se 4 (by rfl) ⟨1273878, by rfl⟩ : syracuseStep 13588037 = 2547757) B2547757
theorem B9058691 : Blo 2119435 9058691 := bstep (se 1 (by rfl) ⟨6794018, by rfl⟩ : syracuseStep 9058691 = 13588037) B13588037
theorem B6039127 : Blo 2119435 6039127 := bstep (se 1 (by rfl) ⟨4529345, by rfl⟩ : syracuseStep 6039127 = 9058691) B9058691
theorem B8052169 : Blo 2119435 8052169 := bstep (se 2 (by rfl) ⟨3019563, by rfl⟩ : syracuseStep 8052169 = 6039127) B6039127
theorem B10736225 : Blo 2119435 10736225 := bstep (se 2 (by rfl) ⟨4026084, by rfl⟩ : syracuseStep 10736225 = 8052169) B8052169
theorem B7157483 : Blo 2119435 7157483 := bstep (se 1 (by rfl) ⟨5368112, by rfl⟩ : syracuseStep 7157483 = 10736225) B10736225
theorem B4771655 : Blo 2119435 4771655 := bstep (se 1 (by rfl) ⟨3578741, by rfl⟩ : syracuseStep 4771655 = 7157483) B7157483
theorem B3181103 : Blo 2119435 3181103 := bstep (se 1 (by rfl) ⟨2385827, by rfl⟩ : syracuseStep 3181103 = 4771655) B4771655
theorem B2120735 : Blo 2119435 2120735 := bstep (se 1 (by rfl) ⟨1590551, by rfl⟩ : syracuseStep 2120735 = 3181103) B3181103
theorem B3181109 : Blo 2119435 3181109 := bbase (se 5 (by rfl) ⟨149114, by rfl⟩ : syracuseStep 3181109 = 298229) (by norm_num)
theorem B2120739 : Blo 2119435 2120739 := bstep (se 1 (by rfl) ⟨1590554, by rfl⟩ : syracuseStep 2120739 = 3181109) B3181109
theorem B5368133 : Blo 2119435 5368133 := bbase (se 4 (by rfl) ⟨503262, by rfl⟩ : syracuseStep 5368133 = 1006525) (by norm_num)
theorem B3578755 : Blo 2119435 3578755 := bstep (se 1 (by rfl) ⟨2684066, by rfl⟩ : syracuseStep 3578755 = 5368133) B5368133
theorem B4771673 : Blo 2119435 4771673 := bstep (se 2 (by rfl) ⟨1789377, by rfl⟩ : syracuseStep 4771673 = 3578755) B3578755
theorem B3181115 : Blo 2119435 3181115 := bstep (se 1 (by rfl) ⟨2385836, by rfl⟩ : syracuseStep 3181115 = 4771673) B4771673
theorem B2120743 : Blo 2119435 2120743 := bstep (se 1 (by rfl) ⟨1590557, by rfl⟩ : syracuseStep 2120743 = 3181115) B3181115
theorem B2385841 : Blo 2119435 2385841 := bbase (se 2 (by rfl) ⟨894690, by rfl⟩ : syracuseStep 2385841 = 1789381) (by norm_num)
theorem B3181121 : Blo 2119435 3181121 := bstep (se 2 (by rfl) ⟨1192920, by rfl⟩ : syracuseStep 3181121 = 2385841) B2385841
theorem B2120747 : Blo 2119435 2120747 := bstep (se 1 (by rfl) ⟨1590560, by rfl⟩ : syracuseStep 2120747 = 3181121) B3181121
theorem B6039173 : Blo 2119435 6039173 := bbase (se 4 (by rfl) ⟨566172, by rfl⟩ : syracuseStep 6039173 = 1132345) (by norm_num)
theorem B4026115 : Blo 2119435 4026115 := bstep (se 1 (by rfl) ⟨3019586, by rfl⟩ : syracuseStep 4026115 = 6039173) B6039173
theorem B5368153 : Blo 2119435 5368153 := bstep (se 2 (by rfl) ⟨2013057, by rfl⟩ : syracuseStep 5368153 = 4026115) B4026115
theorem B7157537 : Blo 2119435 7157537 := bstep (se 2 (by rfl) ⟨2684076, by rfl⟩ : syracuseStep 7157537 = 5368153) B5368153
theorem B4771691 : Blo 2119435 4771691 := bstep (se 1 (by rfl) ⟨3578768, by rfl⟩ : syracuseStep 4771691 = 7157537) B7157537
theorem B3181127 : Blo 2119435 3181127 := bstep (se 1 (by rfl) ⟨2385845, by rfl⟩ : syracuseStep 3181127 = 4771691) B4771691
theorem B2120751 : Blo 2119435 2120751 := bstep (se 1 (by rfl) ⟨1590563, by rfl⟩ : syracuseStep 2120751 = 3181127) B3181127
theorem B3181133 : Blo 2119435 3181133 := bbase (se 3 (by rfl) ⟨596462, by rfl⟩ : syracuseStep 3181133 = 1192925) (by norm_num)
theorem B2120755 : Blo 2119435 2120755 := bstep (se 1 (by rfl) ⟨1590566, by rfl⟩ : syracuseStep 2120755 = 3181133) B3181133
theorem B4771709 : Blo 2119435 4771709 := bbase (se 3 (by rfl) ⟨894695, by rfl⟩ : syracuseStep 4771709 = 1789391) (by norm_num)
theorem B3181139 : Blo 2119435 3181139 := bstep (se 1 (by rfl) ⟨2385854, by rfl⟩ : syracuseStep 3181139 = 4771709) B4771709
theorem B2120759 : Blo 2119435 2120759 := bstep (se 1 (by rfl) ⟨1590569, by rfl⟩ : syracuseStep 2120759 = 3181139) B3181139
theorem B3578789 : Blo 2119435 3578789 := bbase (se 4 (by rfl) ⟨335511, by rfl⟩ : syracuseStep 3578789 = 671023) (by norm_num)
theorem B2385859 : Blo 2119435 2385859 := bstep (se 1 (by rfl) ⟨1789394, by rfl⟩ : syracuseStep 2385859 = 3578789) B3578789
theorem B3181145 : Blo 2119435 3181145 := bstep (se 2 (by rfl) ⟨1192929, by rfl⟩ : syracuseStep 3181145 = 2385859) B2385859
theorem B2120763 : Blo 2119435 2120763 := bstep (se 1 (by rfl) ⟨1590572, by rfl⟩ : syracuseStep 2120763 = 3181145) B3181145
theorem B3397061 : Blo 2119435 3397061 := bbase (se 4 (by rfl) ⟨318474, by rfl⟩ : syracuseStep 3397061 = 636949) (by norm_num)
theorem B2264707 : Blo 2119435 2264707 := bstep (se 1 (by rfl) ⟨1698530, by rfl⟩ : syracuseStep 2264707 = 3397061) B3397061
theorem B3019609 : Blo 2119435 3019609 := bstep (se 2 (by rfl) ⟨1132353, by rfl⟩ : syracuseStep 3019609 = 2264707) B2264707
theorem B16104581 : Blo 2119435 16104581 := bstep (se 4 (by rfl) ⟨1509804, by rfl⟩ : syracuseStep 16104581 = 3019609) B3019609
theorem B10736387 : Blo 2119435 10736387 := bstep (se 1 (by rfl) ⟨8052290, by rfl⟩ : syracuseStep 10736387 = 16104581) B16104581
theorem B7157591 : Blo 2119435 7157591 := bstep (se 1 (by rfl) ⟨5368193, by rfl⟩ : syracuseStep 7157591 = 10736387) B10736387
theorem B4771727 : Blo 2119435 4771727 := bstep (se 1 (by rfl) ⟨3578795, by rfl⟩ : syracuseStep 4771727 = 7157591) B7157591
theorem B3181151 : Blo 2119435 3181151 := bstep (se 1 (by rfl) ⟨2385863, by rfl⟩ : syracuseStep 3181151 = 4771727) B4771727
theorem B2120767 : Blo 2119435 2120767 := bstep (se 1 (by rfl) ⟨1590575, by rfl⟩ : syracuseStep 2120767 = 3181151) B3181151
theorem B3181157 : Blo 2119435 3181157 := bbase (se 4 (by rfl) ⟨298233, by rfl⟩ : syracuseStep 3181157 = 596467) (by norm_num)
theorem B2120771 : Blo 2119435 2120771 := bstep (se 1 (by rfl) ⟨1590578, by rfl⟩ : syracuseStep 2120771 = 3181157) B3181157
theorem B3019621 : Blo 2119435 3019621 := bbase (se 4 (by rfl) ⟨283089, by rfl⟩ : syracuseStep 3019621 = 566179) (by norm_num)
theorem B4026161 : Blo 2119435 4026161 := bstep (se 2 (by rfl) ⟨1509810, by rfl⟩ : syracuseStep 4026161 = 3019621) B3019621
theorem B2684107 : Blo 2119435 2684107 := bstep (se 1 (by rfl) ⟨2013080, by rfl⟩ : syracuseStep 2684107 = 4026161) B4026161
theorem B3578809 : Blo 2119435 3578809 := bstep (se 2 (by rfl) ⟨1342053, by rfl⟩ : syracuseStep 3578809 = 2684107) B2684107
theorem B4771745 : Blo 2119435 4771745 := bstep (se 2 (by rfl) ⟨1789404, by rfl⟩ : syracuseStep 4771745 = 3578809) B3578809
theorem B3181163 : Blo 2119435 3181163 := bstep (se 1 (by rfl) ⟨2385872, by rfl⟩ : syracuseStep 3181163 = 4771745) B4771745
theorem B2120775 : Blo 2119435 2120775 := bstep (se 1 (by rfl) ⟨1590581, by rfl⟩ : syracuseStep 2120775 = 3181163) B3181163
theorem B2385877 : Blo 2119435 2385877 := bbase (se 7 (by rfl) ⟨27959, by rfl⟩ : syracuseStep 2385877 = 55919) (by norm_num)
theorem B3181169 : Blo 2119435 3181169 := bstep (se 2 (by rfl) ⟨1192938, by rfl⟩ : syracuseStep 3181169 = 2385877) B2385877
theorem B2120779 : Blo 2119435 2120779 := bstep (se 1 (by rfl) ⟨1590584, by rfl⟩ : syracuseStep 2120779 = 3181169) B3181169
theorem B2684117 : Blo 2119435 2684117 := bbase (se 7 (by rfl) ⟨31454, by rfl⟩ : syracuseStep 2684117 = 62909) (by norm_num)
theorem B7157645 : Blo 2119435 7157645 := bstep (se 3 (by rfl) ⟨1342058, by rfl⟩ : syracuseStep 7157645 = 2684117) B2684117
theorem B4771763 : Blo 2119435 4771763 := bstep (se 1 (by rfl) ⟨3578822, by rfl⟩ : syracuseStep 4771763 = 7157645) B7157645
theorem B3181175 : Blo 2119435 3181175 := bstep (se 1 (by rfl) ⟨2385881, by rfl⟩ : syracuseStep 3181175 = 4771763) B4771763
theorem B2120783 : Blo 2119435 2120783 := bstep (se 1 (by rfl) ⟨1590587, by rfl⟩ : syracuseStep 2120783 = 3181175) B3181175
theorem B3181181 : Blo 2119435 3181181 := bbase (se 3 (by rfl) ⟨596471, by rfl⟩ : syracuseStep 3181181 = 1192943) (by norm_num)
theorem B2120787 : Blo 2119435 2120787 := bstep (se 1 (by rfl) ⟨1590590, by rfl⟩ : syracuseStep 2120787 = 3181181) B3181181
theorem B4771781 : Blo 2119435 4771781 := bbase (se 4 (by rfl) ⟨447354, by rfl⟩ : syracuseStep 4771781 = 894709) (by norm_num)
theorem B3181187 : Blo 2119435 3181187 := bstep (se 1 (by rfl) ⟨2385890, by rfl⟩ : syracuseStep 3181187 = 4771781) B4771781
theorem B2120791 : Blo 2119435 2120791 := bstep (se 1 (by rfl) ⟨1590593, by rfl⟩ : syracuseStep 2120791 = 3181187) B3181187
theorem B9058949 : Blo 2119435 9058949 := bbase (se 4 (by rfl) ⟨849276, by rfl⟩ : syracuseStep 9058949 = 1698553) (by norm_num)
theorem B6039299 : Blo 2119435 6039299 := bstep (se 1 (by rfl) ⟨4529474, by rfl⟩ : syracuseStep 6039299 = 9058949) B9058949
theorem B4026199 : Blo 2119435 4026199 := bstep (se 1 (by rfl) ⟨3019649, by rfl⟩ : syracuseStep 4026199 = 6039299) B6039299
theorem B5368265 : Blo 2119435 5368265 := bstep (se 2 (by rfl) ⟨2013099, by rfl⟩ : syracuseStep 5368265 = 4026199) B4026199
theorem B3578843 : Blo 2119435 3578843 := bstep (se 1 (by rfl) ⟨2684132, by rfl⟩ : syracuseStep 3578843 = 5368265) B5368265
theorem B2385895 : Blo 2119435 2385895 := bstep (se 1 (by rfl) ⟨1789421, by rfl⟩ : syracuseStep 2385895 = 3578843) B3578843
theorem B3181193 : Blo 2119435 3181193 := bstep (se 2 (by rfl) ⟨1192947, by rfl⟩ : syracuseStep 3181193 = 2385895) B2385895
theorem B2120795 : Blo 2119435 2120795 := bstep (se 1 (by rfl) ⟨1590596, by rfl⟩ : syracuseStep 2120795 = 3181193) B3181193
theorem B10736549 : Blo 2119435 10736549 := bbase (se 4 (by rfl) ⟨1006551, by rfl⟩ : syracuseStep 10736549 = 2013103) (by norm_num)
theorem B7157699 : Blo 2119435 7157699 := bstep (se 1 (by rfl) ⟨5368274, by rfl⟩ : syracuseStep 7157699 = 10736549) B10736549
theorem B4771799 : Blo 2119435 4771799 := bstep (se 1 (by rfl) ⟨3578849, by rfl⟩ : syracuseStep 4771799 = 7157699) B7157699
theorem B3181199 : Blo 2119435 3181199 := bstep (se 1 (by rfl) ⟨2385899, by rfl⟩ : syracuseStep 3181199 = 4771799) B4771799
theorem B2120799 : Blo 2119435 2120799 := bstep (se 1 (by rfl) ⟨1590599, by rfl⟩ : syracuseStep 2120799 = 3181199) B3181199
theorem B3181205 : Blo 2119435 3181205 := bbase (se 6 (by rfl) ⟨74559, by rfl⟩ : syracuseStep 3181205 = 149119) (by norm_num)
theorem B2120803 : Blo 2119435 2120803 := bstep (se 1 (by rfl) ⟨1590602, by rfl⟩ : syracuseStep 2120803 = 3181205) B3181205
theorem B8162309 : Blo 2119435 8162309 := bbase (se 4 (by rfl) ⟨765216, by rfl⟩ : syracuseStep 8162309 = 1530433) (by norm_num)
theorem B5441539 : Blo 2119435 5441539 := bstep (se 1 (by rfl) ⟨4081154, by rfl⟩ : syracuseStep 5441539 = 8162309) B8162309
theorem B7255385 : Blo 2119435 7255385 := bstep (se 2 (by rfl) ⟨2720769, by rfl⟩ : syracuseStep 7255385 = 5441539) B5441539
theorem B4836923 : Blo 2119435 4836923 := bstep (se 1 (by rfl) ⟨3627692, by rfl⟩ : syracuseStep 4836923 = 7255385) B7255385
theorem B3224615 : Blo 2119435 3224615 := bstep (se 1 (by rfl) ⟨2418461, by rfl⟩ : syracuseStep 3224615 = 4836923) B4836923
theorem B8598973 : Blo 2119435 8598973 := bstep (se 3 (by rfl) ⟨1612307, by rfl⟩ : syracuseStep 8598973 = 3224615) B3224615
theorem B11465297 : Blo 2119435 11465297 := bstep (se 2 (by rfl) ⟨4299486, by rfl⟩ : syracuseStep 11465297 = 8598973) B8598973
theorem B7643531 : Blo 2119435 7643531 := bstep (se 1 (by rfl) ⟨5732648, by rfl⟩ : syracuseStep 7643531 = 11465297) B11465297
theorem B20382749 : Blo 2119435 20382749 := bstep (se 3 (by rfl) ⟨3821765, by rfl⟩ : syracuseStep 20382749 = 7643531) B7643531
theorem B13588499 : Blo 2119435 13588499 := bstep (se 1 (by rfl) ⟨10191374, by rfl⟩ : syracuseStep 13588499 = 20382749) B20382749
theorem B9058999 : Blo 2119435 9058999 := bstep (se 1 (by rfl) ⟨6794249, by rfl⟩ : syracuseStep 9058999 = 13588499) B13588499
theorem B12078665 : Blo 2119435 12078665 := bstep (se 2 (by rfl) ⟨4529499, by rfl⟩ : syracuseStep 12078665 = 9058999) B9058999
theorem B8052443 : Blo 2119435 8052443 := bstep (se 1 (by rfl) ⟨6039332, by rfl⟩ : syracuseStep 8052443 = 12078665) B12078665
theorem B5368295 : Blo 2119435 5368295 := bstep (se 1 (by rfl) ⟨4026221, by rfl⟩ : syracuseStep 5368295 = 8052443) B8052443
theorem B3578863 : Blo 2119435 3578863 := bstep (se 1 (by rfl) ⟨2684147, by rfl⟩ : syracuseStep 3578863 = 5368295) B5368295
theorem B4771817 : Blo 2119435 4771817 := bstep (se 2 (by rfl) ⟨1789431, by rfl⟩ : syracuseStep 4771817 = 3578863) B3578863
theorem B3181211 : Blo 2119435 3181211 := bstep (se 1 (by rfl) ⟨2385908, by rfl⟩ : syracuseStep 3181211 = 4771817) B4771817
theorem B2120807 : Blo 2119435 2120807 := bstep (se 1 (by rfl) ⟨1590605, by rfl⟩ : syracuseStep 2120807 = 3181211) B3181211
theorem B2385913 : Blo 2119435 2385913 := bbase (se 2 (by rfl) ⟨894717, by rfl⟩ : syracuseStep 2385913 = 1789435) (by norm_num)
theorem B3181217 : Blo 2119435 3181217 := bstep (se 2 (by rfl) ⟨1192956, by rfl⟩ : syracuseStep 3181217 = 2385913) B2385913
theorem B2120811 : Blo 2119435 2120811 := bstep (se 1 (by rfl) ⟨1590608, by rfl⟩ : syracuseStep 2120811 = 3181217) B3181217
theorem B10191413 : Blo 2119435 10191413 := bbase (se 5 (by rfl) ⟨477722, by rfl⟩ : syracuseStep 10191413 = 955445) (by norm_num)
theorem B6794275 : Blo 2119435 6794275 := bstep (se 1 (by rfl) ⟨5095706, by rfl⟩ : syracuseStep 6794275 = 10191413) B10191413
theorem B9059033 : Blo 2119435 9059033 := bstep (se 2 (by rfl) ⟨3397137, by rfl⟩ : syracuseStep 9059033 = 6794275) B6794275
theorem B6039355 : Blo 2119435 6039355 := bstep (se 1 (by rfl) ⟨4529516, by rfl⟩ : syracuseStep 6039355 = 9059033) B9059033
theorem B8052473 : Blo 2119435 8052473 := bstep (se 2 (by rfl) ⟨3019677, by rfl⟩ : syracuseStep 8052473 = 6039355) B6039355
theorem B5368315 : Blo 2119435 5368315 := bstep (se 1 (by rfl) ⟨4026236, by rfl⟩ : syracuseStep 5368315 = 8052473) B8052473
theorem B7157753 : Blo 2119435 7157753 := bstep (se 2 (by rfl) ⟨2684157, by rfl⟩ : syracuseStep 7157753 = 5368315) B5368315
theorem B4771835 : Blo 2119435 4771835 := bstep (se 1 (by rfl) ⟨3578876, by rfl⟩ : syracuseStep 4771835 = 7157753) B7157753
theorem B3181223 : Blo 2119435 3181223 := bstep (se 1 (by rfl) ⟨2385917, by rfl⟩ : syracuseStep 3181223 = 4771835) B4771835
theorem B2120815 : Blo 2119435 2120815 := bstep (se 1 (by rfl) ⟨1590611, by rfl⟩ : syracuseStep 2120815 = 3181223) B3181223
theorem B3181229 : Blo 2119435 3181229 := bbase (se 3 (by rfl) ⟨596480, by rfl⟩ : syracuseStep 3181229 = 1192961) (by norm_num)
theorem B2120819 : Blo 2119435 2120819 := bstep (se 1 (by rfl) ⟨1590614, by rfl⟩ : syracuseStep 2120819 = 3181229) B3181229
theorem B4771853 : Blo 2119435 4771853 := bbase (se 3 (by rfl) ⟨894722, by rfl⟩ : syracuseStep 4771853 = 1789445) (by norm_num)
theorem B3181235 : Blo 2119435 3181235 := bstep (se 1 (by rfl) ⟨2385926, by rfl⟩ : syracuseStep 3181235 = 4771853) B4771853
theorem B2120823 : Blo 2119435 2120823 := bstep (se 1 (by rfl) ⟨1590617, by rfl⟩ : syracuseStep 2120823 = 3181235) B3181235
theorem B2684173 : Blo 2119435 2684173 := bbase (se 3 (by rfl) ⟨503282, by rfl⟩ : syracuseStep 2684173 = 1006565) (by norm_num)
theorem B3578897 : Blo 2119435 3578897 := bstep (se 2 (by rfl) ⟨1342086, by rfl⟩ : syracuseStep 3578897 = 2684173) B2684173
theorem B2385931 : Blo 2119435 2385931 := bstep (se 1 (by rfl) ⟨1789448, by rfl⟩ : syracuseStep 2385931 = 3578897) B3578897
theorem B3181241 : Blo 2119435 3181241 := bstep (se 2 (by rfl) ⟨1192965, by rfl⟩ : syracuseStep 3181241 = 2385931) B2385931
theorem B2120827 : Blo 2119435 2120827 := bstep (se 1 (by rfl) ⟨1590620, by rfl⟩ : syracuseStep 2120827 = 3181241) B3181241
theorem B3627733 : Blo 2119435 3627733 := bbase (se 7 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 3627733 = 85025) (by norm_num)
theorem B4836977 : Blo 2119435 4836977 := bstep (se 2 (by rfl) ⟨1813866, by rfl⟩ : syracuseStep 4836977 = 3627733) B3627733
theorem B3224651 : Blo 2119435 3224651 := bstep (se 1 (by rfl) ⟨2418488, by rfl⟩ : syracuseStep 3224651 = 4836977) B4836977
theorem B8599069 : Blo 2119435 8599069 := bstep (se 3 (by rfl) ⟨1612325, by rfl⟩ : syracuseStep 8599069 = 3224651) B3224651
theorem B11465425 : Blo 2119435 11465425 := bstep (se 2 (by rfl) ⟨4299534, by rfl⟩ : syracuseStep 11465425 = 8599069) B8599069
theorem B15287233 : Blo 2119435 15287233 := bstep (se 2 (by rfl) ⟨5732712, by rfl⟩ : syracuseStep 15287233 = 11465425) B11465425
theorem B20382977 : Blo 2119435 20382977 := bstep (se 2 (by rfl) ⟨7643616, by rfl⟩ : syracuseStep 20382977 = 15287233) B15287233
theorem B13588651 : Blo 2119435 13588651 := bstep (se 1 (by rfl) ⟨10191488, by rfl⟩ : syracuseStep 13588651 = 20382977) B20382977
theorem B18118201 : Blo 2119435 18118201 := bstep (se 2 (by rfl) ⟨6794325, by rfl⟩ : syracuseStep 18118201 = 13588651) B13588651
theorem B24157601 : Blo 2119435 24157601 := bstep (se 2 (by rfl) ⟨9059100, by rfl⟩ : syracuseStep 24157601 = 18118201) B18118201
theorem B16105067 : Blo 2119435 16105067 := bstep (se 1 (by rfl) ⟨12078800, by rfl⟩ : syracuseStep 16105067 = 24157601) B24157601
theorem B10736711 : Blo 2119435 10736711 := bstep (se 1 (by rfl) ⟨8052533, by rfl⟩ : syracuseStep 10736711 = 16105067) B16105067
theorem B7157807 : Blo 2119435 7157807 := bstep (se 1 (by rfl) ⟨5368355, by rfl⟩ : syracuseStep 7157807 = 10736711) B10736711
theorem B4771871 : Blo 2119435 4771871 := bstep (se 1 (by rfl) ⟨3578903, by rfl⟩ : syracuseStep 4771871 = 7157807) B7157807
theorem B3181247 : Blo 2119435 3181247 := bstep (se 1 (by rfl) ⟨2385935, by rfl⟩ : syracuseStep 3181247 = 4771871) B4771871
theorem B2120831 : Blo 2119435 2120831 := bstep (se 1 (by rfl) ⟨1590623, by rfl⟩ : syracuseStep 2120831 = 3181247) B3181247
theorem B3181253 : Blo 2119435 3181253 := bbase (se 4 (by rfl) ⟨298242, by rfl⟩ : syracuseStep 3181253 = 596485) (by norm_num)
theorem B2120835 : Blo 2119435 2120835 := bstep (se 1 (by rfl) ⟨1590626, by rfl⟩ : syracuseStep 2120835 = 3181253) B3181253
theorem B3578917 : Blo 2119435 3578917 := bbase (se 4 (by rfl) ⟨335523, by rfl⟩ : syracuseStep 3578917 = 671047) (by norm_num)
theorem B4771889 : Blo 2119435 4771889 := bstep (se 2 (by rfl) ⟨1789458, by rfl⟩ : syracuseStep 4771889 = 3578917) B3578917
theorem B3181259 : Blo 2119435 3181259 := bstep (se 1 (by rfl) ⟨2385944, by rfl⟩ : syracuseStep 3181259 = 4771889) B4771889
theorem B2120839 : Blo 2119435 2120839 := bstep (se 1 (by rfl) ⟨1590629, by rfl⟩ : syracuseStep 2120839 = 3181259) B3181259
theorem B2385949 : Blo 2119435 2385949 := bbase (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) (by norm_num)
theorem B3181265 : Blo 2119435 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B2120843 : Blo 2119435 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B7157861 : Blo 2119435 7157861 := bbase (se 4 (by rfl) ⟨671049, by rfl⟩ : syracuseStep 7157861 = 1342099) (by norm_num)
theorem B4771907 : Blo 2119435 4771907 := bstep (se 1 (by rfl) ⟨3578930, by rfl⟩ : syracuseStep 4771907 = 7157861) B7157861
theorem B3181271 : Blo 2119435 3181271 := bstep (se 1 (by rfl) ⟨2385953, by rfl⟩ : syracuseStep 3181271 = 4771907) B4771907
theorem B2120847 : Blo 2119435 2120847 := bstep (se 1 (by rfl) ⟨1590635, by rfl⟩ : syracuseStep 2120847 = 3181271) B3181271
theorem B3181277 : Blo 2119435 3181277 := bbase (se 3 (by rfl) ⟨596489, by rfl⟩ : syracuseStep 3181277 = 1192979) (by norm_num)
theorem B2120851 : Blo 2119435 2120851 := bstep (se 1 (by rfl) ⟨1590638, by rfl⟩ : syracuseStep 2120851 = 3181277) B3181277
theorem B4771925 : Blo 2119435 4771925 := bbase (se 8 (by rfl) ⟨27960, by rfl⟩ : syracuseStep 4771925 = 55921) (by norm_num)
theorem B3181283 : Blo 2119435 3181283 := bstep (se 1 (by rfl) ⟨2385962, by rfl⟩ : syracuseStep 3181283 = 4771925) B4771925
theorem B2120855 : Blo 2119435 2120855 := bstep (se 1 (by rfl) ⟨1590641, by rfl⟩ : syracuseStep 2120855 = 3181283) B3181283
theorem B5095813 : Blo 2119435 5095813 := bbase (se 4 (by rfl) ⟨477732, by rfl⟩ : syracuseStep 5095813 = 955465) (by norm_num)
theorem B6794417 : Blo 2119435 6794417 := bstep (se 2 (by rfl) ⟨2547906, by rfl⟩ : syracuseStep 6794417 = 5095813) B5095813
theorem B4529611 : Blo 2119435 4529611 := bstep (se 1 (by rfl) ⟨3397208, by rfl⟩ : syracuseStep 4529611 = 6794417) B6794417
theorem B6039481 : Blo 2119435 6039481 := bstep (se 2 (by rfl) ⟨2264805, by rfl⟩ : syracuseStep 6039481 = 4529611) B4529611
theorem B8052641 : Blo 2119435 8052641 := bstep (se 2 (by rfl) ⟨3019740, by rfl⟩ : syracuseStep 8052641 = 6039481) B6039481
theorem B5368427 : Blo 2119435 5368427 := bstep (se 1 (by rfl) ⟨4026320, by rfl⟩ : syracuseStep 5368427 = 8052641) B8052641
theorem B3578951 : Blo 2119435 3578951 := bstep (se 1 (by rfl) ⟨2684213, by rfl⟩ : syracuseStep 3578951 = 5368427) B5368427
theorem B2385967 : Blo 2119435 2385967 := bstep (se 1 (by rfl) ⟨1789475, by rfl⟩ : syracuseStep 2385967 = 3578951) B3578951
theorem B3181289 : Blo 2119435 3181289 := bstep (se 2 (by rfl) ⟨1192983, by rfl⟩ : syracuseStep 3181289 = 2385967) B2385967
theorem B2120859 : Blo 2119435 2120859 := bstep (se 1 (by rfl) ⟨1590644, by rfl⟩ : syracuseStep 2120859 = 3181289) B3181289
theorem B20383285 : Blo 2119435 20383285 := bbase (se 5 (by rfl) ⟨955466, by rfl⟩ : syracuseStep 20383285 = 1910933) (by norm_num)
theorem B27177713 : Blo 2119435 27177713 := bstep (se 2 (by rfl) ⟨10191642, by rfl⟩ : syracuseStep 27177713 = 20383285) B20383285
theorem B18118475 : Blo 2119435 18118475 := bstep (se 1 (by rfl) ⟨13588856, by rfl⟩ : syracuseStep 18118475 = 27177713) B27177713
theorem B12078983 : Blo 2119435 12078983 := bstep (se 1 (by rfl) ⟨9059237, by rfl⟩ : syracuseStep 12078983 = 18118475) B18118475
theorem B8052655 : Blo 2119435 8052655 := bstep (se 1 (by rfl) ⟨6039491, by rfl⟩ : syracuseStep 8052655 = 12078983) B12078983
theorem B10736873 : Blo 2119435 10736873 := bstep (se 2 (by rfl) ⟨4026327, by rfl⟩ : syracuseStep 10736873 = 8052655) B8052655
theorem B7157915 : Blo 2119435 7157915 := bstep (se 1 (by rfl) ⟨5368436, by rfl⟩ : syracuseStep 7157915 = 10736873) B10736873
theorem B4771943 : Blo 2119435 4771943 := bstep (se 1 (by rfl) ⟨3578957, by rfl⟩ : syracuseStep 4771943 = 7157915) B7157915
theorem B3181295 : Blo 2119435 3181295 := bstep (se 1 (by rfl) ⟨2385971, by rfl⟩ : syracuseStep 3181295 = 4771943) B4771943
theorem B2120863 : Blo 2119435 2120863 := bstep (se 1 (by rfl) ⟨1590647, by rfl⟩ : syracuseStep 2120863 = 3181295) B3181295
theorem B3181301 : Blo 2119435 3181301 := bbase (se 5 (by rfl) ⟨149123, by rfl⟩ : syracuseStep 3181301 = 298247) (by norm_num)
theorem B2120867 : Blo 2119435 2120867 := bstep (se 1 (by rfl) ⟨1590650, by rfl⟩ : syracuseStep 2120867 = 3181301) B3181301
theorem B8501237 : Blo 2119435 8501237 := bbase (se 5 (by rfl) ⟨398495, by rfl⟩ : syracuseStep 8501237 = 796991) (by norm_num)
theorem B5667491 : Blo 2119435 5667491 := bstep (se 1 (by rfl) ⟨4250618, by rfl⟩ : syracuseStep 5667491 = 8501237) B8501237
theorem B15113309 : Blo 2119435 15113309 := bstep (se 3 (by rfl) ⟨2833745, by rfl⟩ : syracuseStep 15113309 = 5667491) B5667491
theorem B40302157 : Blo 2119435 40302157 := bstep (se 3 (by rfl) ⟨7556654, by rfl⟩ : syracuseStep 40302157 = 15113309) B15113309
theorem B53736209 : Blo 2119435 53736209 := bstep (se 2 (by rfl) ⟨20151078, by rfl⟩ : syracuseStep 53736209 = 40302157) B40302157
theorem B35824139 : Blo 2119435 35824139 := bstep (se 1 (by rfl) ⟨26868104, by rfl⟩ : syracuseStep 35824139 = 53736209) B53736209
theorem B23882759 : Blo 2119435 23882759 := bstep (se 1 (by rfl) ⟨17912069, by rfl⟩ : syracuseStep 23882759 = 35824139) B35824139
theorem B15921839 : Blo 2119435 15921839 := bstep (se 1 (by rfl) ⟨11941379, by rfl⟩ : syracuseStep 15921839 = 23882759) B23882759
theorem B10614559 : Blo 2119435 10614559 := bstep (se 1 (by rfl) ⟨7960919, by rfl⟩ : syracuseStep 10614559 = 15921839) B15921839
theorem B14152745 : Blo 2119435 14152745 := bstep (se 2 (by rfl) ⟨5307279, by rfl⟩ : syracuseStep 14152745 = 10614559) B10614559
theorem B9435163 : Blo 2119435 9435163 := bstep (se 1 (by rfl) ⟨7076372, by rfl⟩ : syracuseStep 9435163 = 14152745) B14152745
theorem B12580217 : Blo 2119435 12580217 := bstep (se 2 (by rfl) ⟨4717581, by rfl⟩ : syracuseStep 12580217 = 9435163) B9435163
theorem B8386811 : Blo 2119435 8386811 := bstep (se 1 (by rfl) ⟨6290108, by rfl⟩ : syracuseStep 8386811 = 12580217) B12580217
theorem B5591207 : Blo 2119435 5591207 := bstep (se 1 (by rfl) ⟨4193405, by rfl⟩ : syracuseStep 5591207 = 8386811) B8386811
theorem B3727471 : Blo 2119435 3727471 := bstep (se 1 (by rfl) ⟨2795603, by rfl⟩ : syracuseStep 3727471 = 5591207) B5591207
theorem B4969961 : Blo 2119435 4969961 := bstep (se 2 (by rfl) ⟨1863735, by rfl⟩ : syracuseStep 4969961 = 3727471) B3727471
theorem B3313307 : Blo 2119435 3313307 := bstep (se 1 (by rfl) ⟨2484980, by rfl⟩ : syracuseStep 3313307 = 4969961) B4969961
theorem B8835485 : Blo 2119435 8835485 := bstep (se 3 (by rfl) ⟨1656653, by rfl⟩ : syracuseStep 8835485 = 3313307) B3313307
theorem B23561293 : Blo 2119435 23561293 := bstep (se 3 (by rfl) ⟨4417742, by rfl⟩ : syracuseStep 23561293 = 8835485) B8835485
theorem B31415057 : Blo 2119435 31415057 := bstep (se 2 (by rfl) ⟨11780646, by rfl⟩ : syracuseStep 31415057 = 23561293) B23561293
theorem B20943371 : Blo 2119435 20943371 := bstep (se 1 (by rfl) ⟨15707528, by rfl⟩ : syracuseStep 20943371 = 31415057) B31415057
theorem B55848989 : Blo 2119435 55848989 := bstep (se 3 (by rfl) ⟨10471685, by rfl⟩ : syracuseStep 55848989 = 20943371) B20943371
theorem B37232659 : Blo 2119435 37232659 := bstep (se 1 (by rfl) ⟨27924494, by rfl⟩ : syracuseStep 37232659 = 55848989) B55848989
theorem B49643545 : Blo 2119435 49643545 := bstep (se 2 (by rfl) ⟨18616329, by rfl⟩ : syracuseStep 49643545 = 37232659) B37232659
theorem B66191393 : Blo 2119435 66191393 := bstep (se 2 (by rfl) ⟨24821772, by rfl⟩ : syracuseStep 66191393 = 49643545) B49643545
theorem B44127595 : Blo 2119435 44127595 := bstep (se 1 (by rfl) ⟨33095696, by rfl⟩ : syracuseStep 44127595 = 66191393) B66191393
theorem B58836793 : Blo 2119435 58836793 := bstep (se 2 (by rfl) ⟨22063797, by rfl⟩ : syracuseStep 58836793 = 44127595) B44127595
theorem B78449057 : Blo 2119435 78449057 := bstep (se 2 (by rfl) ⟨29418396, by rfl⟩ : syracuseStep 78449057 = 58836793) B58836793
theorem B52299371 : Blo 2119435 52299371 := bstep (se 1 (by rfl) ⟨39224528, by rfl⟩ : syracuseStep 52299371 = 78449057) B78449057
theorem B34866247 : Blo 2119435 34866247 := bstep (se 1 (by rfl) ⟨26149685, by rfl⟩ : syracuseStep 34866247 = 52299371) B52299371
theorem B46488329 : Blo 2119435 46488329 := bstep (se 2 (by rfl) ⟨17433123, by rfl⟩ : syracuseStep 46488329 = 34866247) B34866247
theorem B30992219 : Blo 2119435 30992219 := bstep (se 1 (by rfl) ⟨23244164, by rfl⟩ : syracuseStep 30992219 = 46488329) B46488329
theorem B20661479 : Blo 2119435 20661479 := bstep (se 1 (by rfl) ⟨15496109, by rfl⟩ : syracuseStep 20661479 = 30992219) B30992219
theorem B13774319 : Blo 2119435 13774319 := bstep (se 1 (by rfl) ⟨10330739, by rfl⟩ : syracuseStep 13774319 = 20661479) B20661479
theorem B9182879 : Blo 2119435 9182879 := bstep (se 1 (by rfl) ⟨6887159, by rfl⟩ : syracuseStep 9182879 = 13774319) B13774319
theorem B6121919 : Blo 2119435 6121919 := bstep (se 1 (by rfl) ⟨4591439, by rfl⟩ : syracuseStep 6121919 = 9182879) B9182879
theorem B4081279 : Blo 2119435 4081279 := bstep (se 1 (by rfl) ⟨3060959, by rfl⟩ : syracuseStep 4081279 = 6121919) B6121919
theorem B5441705 : Blo 2119435 5441705 := bstep (se 2 (by rfl) ⟨2040639, by rfl⟩ : syracuseStep 5441705 = 4081279) B4081279
theorem B3627803 : Blo 2119435 3627803 := bstep (se 1 (by rfl) ⟨2720852, by rfl⟩ : syracuseStep 3627803 = 5441705) B5441705
theorem B2418535 : Blo 2119435 2418535 := bstep (se 1 (by rfl) ⟨1813901, by rfl⟩ : syracuseStep 2418535 = 3627803) B3627803
theorem B3224713 : Blo 2119435 3224713 := bstep (se 2 (by rfl) ⟨1209267, by rfl⟩ : syracuseStep 3224713 = 2418535) B2418535
theorem B4299617 : Blo 2119435 4299617 := bstep (se 2 (by rfl) ⟨1612356, by rfl⟩ : syracuseStep 4299617 = 3224713) B3224713
theorem B2866411 : Blo 2119435 2866411 := bstep (se 1 (by rfl) ⟨2149808, by rfl⟩ : syracuseStep 2866411 = 4299617) B4299617
theorem B15287525 : Blo 2119435 15287525 := bstep (se 4 (by rfl) ⟨1433205, by rfl⟩ : syracuseStep 15287525 = 2866411) B2866411
theorem B10191683 : Blo 2119435 10191683 := bstep (se 1 (by rfl) ⟨7643762, by rfl⟩ : syracuseStep 10191683 = 15287525) B15287525
theorem B6794455 : Blo 2119435 6794455 := bstep (se 1 (by rfl) ⟨5095841, by rfl⟩ : syracuseStep 6794455 = 10191683) B10191683
theorem B9059273 : Blo 2119435 9059273 := bstep (se 2 (by rfl) ⟨3397227, by rfl⟩ : syracuseStep 9059273 = 6794455) B6794455
theorem B6039515 : Blo 2119435 6039515 := bstep (se 1 (by rfl) ⟨4529636, by rfl⟩ : syracuseStep 6039515 = 9059273) B9059273
theorem B4026343 : Blo 2119435 4026343 := bstep (se 1 (by rfl) ⟨3019757, by rfl⟩ : syracuseStep 4026343 = 6039515) B6039515
theorem B5368457 : Blo 2119435 5368457 := bstep (se 2 (by rfl) ⟨2013171, by rfl⟩ : syracuseStep 5368457 = 4026343) B4026343
theorem B3578971 : Blo 2119435 3578971 := bstep (se 1 (by rfl) ⟨2684228, by rfl⟩ : syracuseStep 3578971 = 5368457) B5368457
theorem B4771961 : Blo 2119435 4771961 := bstep (se 2 (by rfl) ⟨1789485, by rfl⟩ : syracuseStep 4771961 = 3578971) B3578971
theorem B3181307 : Blo 2119435 3181307 := bstep (se 1 (by rfl) ⟨2385980, by rfl⟩ : syracuseStep 3181307 = 4771961) B4771961
theorem B2120871 : Blo 2119435 2120871 := bstep (se 1 (by rfl) ⟨1590653, by rfl⟩ : syracuseStep 2120871 = 3181307) B3181307
theorem B2385985 : Blo 2119435 2385985 := bbase (se 2 (by rfl) ⟨894744, by rfl⟩ : syracuseStep 2385985 = 1789489) (by norm_num)
theorem B3181313 : Blo 2119435 3181313 := bstep (se 2 (by rfl) ⟨1192992, by rfl⟩ : syracuseStep 3181313 = 2385985) B2385985
theorem B2120875 : Blo 2119435 2120875 := bstep (se 1 (by rfl) ⟨1590656, by rfl⟩ : syracuseStep 2120875 = 3181313) B3181313
theorem B5368477 : Blo 2119435 5368477 := bbase (se 3 (by rfl) ⟨1006589, by rfl⟩ : syracuseStep 5368477 = 2013179) (by norm_num)
theorem B7157969 : Blo 2119435 7157969 := bstep (se 2 (by rfl) ⟨2684238, by rfl⟩ : syracuseStep 7157969 = 5368477) B5368477
theorem B4771979 : Blo 2119435 4771979 := bstep (se 1 (by rfl) ⟨3578984, by rfl⟩ : syracuseStep 4771979 = 7157969) B7157969
theorem B3181319 : Blo 2119435 3181319 := bstep (se 1 (by rfl) ⟨2385989, by rfl⟩ : syracuseStep 3181319 = 4771979) B4771979
theorem B2120879 : Blo 2119435 2120879 := bstep (se 1 (by rfl) ⟨1590659, by rfl⟩ : syracuseStep 2120879 = 3181319) B3181319
theorem B3181325 : Blo 2119435 3181325 := bbase (se 3 (by rfl) ⟨596498, by rfl⟩ : syracuseStep 3181325 = 1192997) (by norm_num)
theorem B2120883 : Blo 2119435 2120883 := bstep (se 1 (by rfl) ⟨1590662, by rfl⟩ : syracuseStep 2120883 = 3181325) B3181325
theorem B4771997 : Blo 2119435 4771997 := bbase (se 3 (by rfl) ⟨894749, by rfl⟩ : syracuseStep 4771997 = 1789499) (by norm_num)
theorem B3181331 : Blo 2119435 3181331 := bstep (se 1 (by rfl) ⟨2385998, by rfl⟩ : syracuseStep 3181331 = 4771997) B4771997
theorem B2120887 : Blo 2119435 2120887 := bstep (se 1 (by rfl) ⟨1590665, by rfl⟩ : syracuseStep 2120887 = 3181331) B3181331
theorem B3579005 : Blo 2119435 3579005 := bbase (se 3 (by rfl) ⟨671063, by rfl⟩ : syracuseStep 3579005 = 1342127) (by norm_num)
theorem B2386003 : Blo 2119435 2386003 := bstep (se 1 (by rfl) ⟨1789502, by rfl⟩ : syracuseStep 2386003 = 3579005) B3579005
theorem B3181337 : Blo 2119435 3181337 := bstep (se 2 (by rfl) ⟨1193001, by rfl⟩ : syracuseStep 3181337 = 2386003) B2386003
theorem B2120891 : Blo 2119435 2120891 := bstep (se 1 (by rfl) ⟨1590668, by rfl⟩ : syracuseStep 2120891 = 3181337) B3181337
theorem B10191797 : Blo 2119435 10191797 := bbase (se 5 (by rfl) ⟨477740, by rfl⟩ : syracuseStep 10191797 = 955481) (by norm_num)
theorem B6794531 : Blo 2119435 6794531 := bstep (se 1 (by rfl) ⟨5095898, by rfl⟩ : syracuseStep 6794531 = 10191797) B10191797
theorem B4529687 : Blo 2119435 4529687 := bstep (se 1 (by rfl) ⟨3397265, by rfl⟩ : syracuseStep 4529687 = 6794531) B6794531
theorem B12079165 : Blo 2119435 12079165 := bstep (se 3 (by rfl) ⟨2264843, by rfl⟩ : syracuseStep 12079165 = 4529687) B4529687
theorem B16105553 : Blo 2119435 16105553 := bstep (se 2 (by rfl) ⟨6039582, by rfl⟩ : syracuseStep 16105553 = 12079165) B12079165
theorem B10737035 : Blo 2119435 10737035 := bstep (se 1 (by rfl) ⟨8052776, by rfl⟩ : syracuseStep 10737035 = 16105553) B16105553
theorem B7158023 : Blo 2119435 7158023 := bstep (se 1 (by rfl) ⟨5368517, by rfl⟩ : syracuseStep 7158023 = 10737035) B10737035
theorem B4772015 : Blo 2119435 4772015 := bstep (se 1 (by rfl) ⟨3579011, by rfl⟩ : syracuseStep 4772015 = 7158023) B7158023
theorem B3181343 : Blo 2119435 3181343 := bstep (se 1 (by rfl) ⟨2386007, by rfl⟩ : syracuseStep 3181343 = 4772015) B4772015
theorem B2120895 : Blo 2119435 2120895 := bstep (se 1 (by rfl) ⟨1590671, by rfl⟩ : syracuseStep 2120895 = 3181343) B3181343
theorem B3181349 : Blo 2119435 3181349 := bbase (se 4 (by rfl) ⟨298251, by rfl⟩ : syracuseStep 3181349 = 596503) (by norm_num)
theorem B2120899 : Blo 2119435 2120899 := bstep (se 1 (by rfl) ⟨1590674, by rfl⟩ : syracuseStep 2120899 = 3181349) B3181349
theorem B2684269 : Blo 2119435 2684269 := bbase (se 3 (by rfl) ⟨503300, by rfl⟩ : syracuseStep 2684269 = 1006601) (by norm_num)
theorem B3579025 : Blo 2119435 3579025 := bstep (se 2 (by rfl) ⟨1342134, by rfl⟩ : syracuseStep 3579025 = 2684269) B2684269
theorem B4772033 : Blo 2119435 4772033 := bstep (se 2 (by rfl) ⟨1789512, by rfl⟩ : syracuseStep 4772033 = 3579025) B3579025
theorem B3181355 : Blo 2119435 3181355 := bstep (se 1 (by rfl) ⟨2386016, by rfl⟩ : syracuseStep 3181355 = 4772033) B4772033
theorem B2120903 : Blo 2119435 2120903 := bstep (se 1 (by rfl) ⟨1590677, by rfl⟩ : syracuseStep 2120903 = 3181355) B3181355
theorem B2386021 : Blo 2119435 2386021 := bbase (se 4 (by rfl) ⟨223689, by rfl⟩ : syracuseStep 2386021 = 447379) (by norm_num)
theorem B3181361 : Blo 2119435 3181361 := bstep (se 2 (by rfl) ⟨1193010, by rfl⟩ : syracuseStep 3181361 = 2386021) B2386021
theorem B2120907 : Blo 2119435 2120907 := bstep (se 1 (by rfl) ⟨1590680, by rfl⟩ : syracuseStep 2120907 = 3181361) B3181361
theorem B2264861 : Blo 2119435 2264861 := bbase (se 3 (by rfl) ⟨424661, by rfl⟩ : syracuseStep 2264861 = 849323) (by norm_num)
theorem B6039629 : Blo 2119435 6039629 := bstep (se 3 (by rfl) ⟨1132430, by rfl⟩ : syracuseStep 6039629 = 2264861) B2264861
theorem B4026419 : Blo 2119435 4026419 := bstep (se 1 (by rfl) ⟨3019814, by rfl⟩ : syracuseStep 4026419 = 6039629) B6039629
theorem B2684279 : Blo 2119435 2684279 := bstep (se 1 (by rfl) ⟨2013209, by rfl⟩ : syracuseStep 2684279 = 4026419) B4026419
theorem B7158077 : Blo 2119435 7158077 := bstep (se 3 (by rfl) ⟨1342139, by rfl⟩ : syracuseStep 7158077 = 2684279) B2684279
theorem B4772051 : Blo 2119435 4772051 := bstep (se 1 (by rfl) ⟨3579038, by rfl⟩ : syracuseStep 4772051 = 7158077) B7158077
theorem B3181367 : Blo 2119435 3181367 := bstep (se 1 (by rfl) ⟨2386025, by rfl⟩ : syracuseStep 3181367 = 4772051) B4772051
theorem B2120911 : Blo 2119435 2120911 := bstep (se 1 (by rfl) ⟨1590683, by rfl⟩ : syracuseStep 2120911 = 3181367) B3181367
theorem B3181373 : Blo 2119435 3181373 := bbase (se 3 (by rfl) ⟨596507, by rfl⟩ : syracuseStep 3181373 = 1193015) (by norm_num)
theorem B2120915 : Blo 2119435 2120915 := bstep (se 1 (by rfl) ⟨1590686, by rfl⟩ : syracuseStep 2120915 = 3181373) B3181373
theorem B4772069 : Blo 2119435 4772069 := bbase (se 4 (by rfl) ⟨447381, by rfl⟩ : syracuseStep 4772069 = 894763) (by norm_num)
theorem B3181379 : Blo 2119435 3181379 := bstep (se 1 (by rfl) ⟨2386034, by rfl⟩ : syracuseStep 3181379 = 4772069) B4772069
theorem B2120919 : Blo 2119435 2120919 := bstep (se 1 (by rfl) ⟨1590689, by rfl⟩ : syracuseStep 2120919 = 3181379) B3181379
theorem B5368589 : Blo 2119435 5368589 := bbase (se 3 (by rfl) ⟨1006610, by rfl⟩ : syracuseStep 5368589 = 2013221) (by norm_num)
theorem B3579059 : Blo 2119435 3579059 := bstep (se 1 (by rfl) ⟨2684294, by rfl⟩ : syracuseStep 3579059 = 5368589) B5368589
theorem B2386039 : Blo 2119435 2386039 := bstep (se 1 (by rfl) ⟨1789529, by rfl⟩ : syracuseStep 2386039 = 3579059) B3579059
theorem B3181385 : Blo 2119435 3181385 := bstep (se 2 (by rfl) ⟨1193019, by rfl⟩ : syracuseStep 3181385 = 2386039) B2386039
theorem B2120923 : Blo 2119435 2120923 := bstep (se 1 (by rfl) ⟨1590692, by rfl⟩ : syracuseStep 2120923 = 3181385) B3181385
theorem B3019837 : Blo 2119435 3019837 := bbase (se 3 (by rfl) ⟨566219, by rfl⟩ : syracuseStep 3019837 = 1132439) (by norm_num)
theorem B4026449 : Blo 2119435 4026449 := bstep (se 2 (by rfl) ⟨1509918, by rfl⟩ : syracuseStep 4026449 = 3019837) B3019837
theorem B10737197 : Blo 2119435 10737197 := bstep (se 3 (by rfl) ⟨2013224, by rfl⟩ : syracuseStep 10737197 = 4026449) B4026449
theorem B7158131 : Blo 2119435 7158131 := bstep (se 1 (by rfl) ⟨5368598, by rfl⟩ : syracuseStep 7158131 = 10737197) B10737197
theorem B4772087 : Blo 2119435 4772087 := bstep (se 1 (by rfl) ⟨3579065, by rfl⟩ : syracuseStep 4772087 = 7158131) B7158131
theorem B3181391 : Blo 2119435 3181391 := bstep (se 1 (by rfl) ⟨2386043, by rfl⟩ : syracuseStep 3181391 = 4772087) B4772087
theorem B2120927 : Blo 2119435 2120927 := bstep (se 1 (by rfl) ⟨1590695, by rfl⟩ : syracuseStep 2120927 = 3181391) B3181391
theorem B3181397 : Blo 2119435 3181397 := bbase (se 9 (by rfl) ⟨9320, by rfl⟩ : syracuseStep 3181397 = 18641) (by norm_num)
theorem B2120931 : Blo 2119435 2120931 := bstep (se 1 (by rfl) ⟨1590698, by rfl⟩ : syracuseStep 2120931 = 3181397) B3181397
theorem B4529773 : Blo 2119435 4529773 := bbase (se 3 (by rfl) ⟨849332, by rfl⟩ : syracuseStep 4529773 = 1698665) (by norm_num)
theorem B6039697 : Blo 2119435 6039697 := bstep (se 2 (by rfl) ⟨2264886, by rfl⟩ : syracuseStep 6039697 = 4529773) B4529773
theorem B8052929 : Blo 2119435 8052929 := bstep (se 2 (by rfl) ⟨3019848, by rfl⟩ : syracuseStep 8052929 = 6039697) B6039697
theorem B5368619 : Blo 2119435 5368619 := bstep (se 1 (by rfl) ⟨4026464, by rfl⟩ : syracuseStep 5368619 = 8052929) B8052929
theorem B3579079 : Blo 2119435 3579079 := bstep (se 1 (by rfl) ⟨2684309, by rfl⟩ : syracuseStep 3579079 = 5368619) B5368619
theorem B4772105 : Blo 2119435 4772105 := bstep (se 2 (by rfl) ⟨1789539, by rfl⟩ : syracuseStep 4772105 = 3579079) B3579079
theorem B3181403 : Blo 2119435 3181403 := bstep (se 1 (by rfl) ⟨2386052, by rfl⟩ : syracuseStep 3181403 = 4772105) B4772105
theorem B2120935 : Blo 2119435 2120935 := bstep (se 1 (by rfl) ⟨1590701, by rfl⟩ : syracuseStep 2120935 = 3181403) B3181403
theorem B2386057 : Blo 2119435 2386057 := bbase (se 2 (by rfl) ⟨894771, by rfl⟩ : syracuseStep 2386057 = 1789543) (by norm_num)
theorem B3181409 : Blo 2119435 3181409 := bstep (se 2 (by rfl) ⟨1193028, by rfl⟩ : syracuseStep 3181409 = 2386057) B2386057
theorem B2120939 : Blo 2119435 2120939 := bstep (se 1 (by rfl) ⟨1590704, by rfl⟩ : syracuseStep 2120939 = 3181409) B3181409
theorem B58838741 : Blo 2119435 58838741 := bbase (se 7 (by rfl) ⟨689516, by rfl⟩ : syracuseStep 58838741 = 1379033) (by norm_num)
theorem B39225827 : Blo 2119435 39225827 := bstep (se 1 (by rfl) ⟨29419370, by rfl⟩ : syracuseStep 39225827 = 58838741) B58838741
theorem B104602205 : Blo 2119435 104602205 := bstep (se 3 (by rfl) ⟨19612913, by rfl⟩ : syracuseStep 104602205 = 39225827) B39225827
theorem B69734803 : Blo 2119435 69734803 := bstep (se 1 (by rfl) ⟨52301102, by rfl⟩ : syracuseStep 69734803 = 104602205) B104602205
theorem B92979737 : Blo 2119435 92979737 := bstep (se 2 (by rfl) ⟨34867401, by rfl⟩ : syracuseStep 92979737 = 69734803) B69734803
theorem B61986491 : Blo 2119435 61986491 := bstep (se 1 (by rfl) ⟨46489868, by rfl⟩ : syracuseStep 61986491 = 92979737) B92979737
theorem B41324327 : Blo 2119435 41324327 := bstep (se 1 (by rfl) ⟨30993245, by rfl⟩ : syracuseStep 41324327 = 61986491) B61986491
theorem B27549551 : Blo 2119435 27549551 := bstep (se 1 (by rfl) ⟨20662163, by rfl⟩ : syracuseStep 27549551 = 41324327) B41324327
theorem B18366367 : Blo 2119435 18366367 := bstep (se 1 (by rfl) ⟨13774775, by rfl⟩ : syracuseStep 18366367 = 27549551) B27549551
theorem B24488489 : Blo 2119435 24488489 := bstep (se 2 (by rfl) ⟨9183183, by rfl⟩ : syracuseStep 24488489 = 18366367) B18366367
theorem B16325659 : Blo 2119435 16325659 := bstep (se 1 (by rfl) ⟨12244244, by rfl⟩ : syracuseStep 16325659 = 24488489) B24488489
theorem B21767545 : Blo 2119435 21767545 := bstep (se 2 (by rfl) ⟨8162829, by rfl⟩ : syracuseStep 21767545 = 16325659) B16325659
theorem B29023393 : Blo 2119435 29023393 := bstep (se 2 (by rfl) ⟨10883772, by rfl⟩ : syracuseStep 29023393 = 21767545) B21767545
theorem B38697857 : Blo 2119435 38697857 := bstep (se 2 (by rfl) ⟨14511696, by rfl⟩ : syracuseStep 38697857 = 29023393) B29023393
theorem B25798571 : Blo 2119435 25798571 := bstep (se 1 (by rfl) ⟨19348928, by rfl⟩ : syracuseStep 25798571 = 38697857) B38697857
theorem B17199047 : Blo 2119435 17199047 := bstep (se 1 (by rfl) ⟨12899285, by rfl⟩ : syracuseStep 17199047 = 25798571) B25798571
theorem B11466031 : Blo 2119435 11466031 := bstep (se 1 (by rfl) ⟨8599523, by rfl⟩ : syracuseStep 11466031 = 17199047) B17199047
theorem B15288041 : Blo 2119435 15288041 := bstep (se 2 (by rfl) ⟨5733015, by rfl⟩ : syracuseStep 15288041 = 11466031) B11466031
theorem B40768109 : Blo 2119435 40768109 := bstep (se 3 (by rfl) ⟨7644020, by rfl⟩ : syracuseStep 40768109 = 15288041) B15288041
theorem B27178739 : Blo 2119435 27178739 := bstep (se 1 (by rfl) ⟨20384054, by rfl⟩ : syracuseStep 27178739 = 40768109) B40768109
theorem B18119159 : Blo 2119435 18119159 := bstep (se 1 (by rfl) ⟨13589369, by rfl⟩ : syracuseStep 18119159 = 27178739) B27178739
theorem B12079439 : Blo 2119435 12079439 := bstep (se 1 (by rfl) ⟨9059579, by rfl⟩ : syracuseStep 12079439 = 18119159) B18119159
theorem B8052959 : Blo 2119435 8052959 := bstep (se 1 (by rfl) ⟨6039719, by rfl⟩ : syracuseStep 8052959 = 12079439) B12079439
theorem B5368639 : Blo 2119435 5368639 := bstep (se 1 (by rfl) ⟨4026479, by rfl⟩ : syracuseStep 5368639 = 8052959) B8052959
theorem B7158185 : Blo 2119435 7158185 := bstep (se 2 (by rfl) ⟨2684319, by rfl⟩ : syracuseStep 7158185 = 5368639) B5368639
theorem B4772123 : Blo 2119435 4772123 := bstep (se 1 (by rfl) ⟨3579092, by rfl⟩ : syracuseStep 4772123 = 7158185) B7158185
theorem B3181415 : Blo 2119435 3181415 := bstep (se 1 (by rfl) ⟨2386061, by rfl⟩ : syracuseStep 3181415 = 4772123) B4772123
theorem B2120943 : Blo 2119435 2120943 := bstep (se 1 (by rfl) ⟨1590707, by rfl⟩ : syracuseStep 2120943 = 3181415) B3181415
theorem B3181421 : Blo 2119435 3181421 := bbase (se 3 (by rfl) ⟨596516, by rfl⟩ : syracuseStep 3181421 = 1193033) (by norm_num)
theorem B2120947 : Blo 2119435 2120947 := bstep (se 1 (by rfl) ⟨1590710, by rfl⟩ : syracuseStep 2120947 = 3181421) B3181421
theorem B4772141 : Blo 2119435 4772141 := bbase (se 3 (by rfl) ⟨894776, by rfl⟩ : syracuseStep 4772141 = 1789553) (by norm_num)
theorem B3181427 : Blo 2119435 3181427 := bstep (se 1 (by rfl) ⟨2386070, by rfl⟩ : syracuseStep 3181427 = 4772141) B4772141
theorem B2120951 : Blo 2119435 2120951 := bstep (se 1 (by rfl) ⟨1590713, by rfl⟩ : syracuseStep 2120951 = 3181427) B3181427
theorem B6794725 : Blo 2119435 6794725 := bbase (se 4 (by rfl) ⟨637005, by rfl⟩ : syracuseStep 6794725 = 1274011) (by norm_num)
theorem B9059633 : Blo 2119435 9059633 := bstep (se 2 (by rfl) ⟨3397362, by rfl⟩ : syracuseStep 9059633 = 6794725) B6794725
theorem B6039755 : Blo 2119435 6039755 := bstep (se 1 (by rfl) ⟨4529816, by rfl⟩ : syracuseStep 6039755 = 9059633) B9059633
theorem B4026503 : Blo 2119435 4026503 := bstep (se 1 (by rfl) ⟨3019877, by rfl⟩ : syracuseStep 4026503 = 6039755) B6039755
theorem B2684335 : Blo 2119435 2684335 := bstep (se 1 (by rfl) ⟨2013251, by rfl⟩ : syracuseStep 2684335 = 4026503) B4026503
theorem B3579113 : Blo 2119435 3579113 := bstep (se 2 (by rfl) ⟨1342167, by rfl⟩ : syracuseStep 3579113 = 2684335) B2684335
theorem B2386075 : Blo 2119435 2386075 := bstep (se 1 (by rfl) ⟨1789556, by rfl⟩ : syracuseStep 2386075 = 3579113) B3579113
theorem B3181433 : Blo 2119435 3181433 := bstep (se 2 (by rfl) ⟨1193037, by rfl⟩ : syracuseStep 3181433 = 2386075) B2386075
theorem B2120955 : Blo 2119435 2120955 := bstep (se 1 (by rfl) ⟨1590716, by rfl⟩ : syracuseStep 2120955 = 3181433) B3181433
theorem B2618029 : Blo 2119435 2618029 := bbase (se 3 (by rfl) ⟨490880, by rfl⟩ : syracuseStep 2618029 = 981761) (by norm_num)
theorem B3490705 : Blo 2119435 3490705 := bstep (se 2 (by rfl) ⟨1309014, by rfl⟩ : syracuseStep 3490705 = 2618029) B2618029
theorem B4654273 : Blo 2119435 4654273 := bstep (se 2 (by rfl) ⟨1745352, by rfl⟩ : syracuseStep 4654273 = 3490705) B3490705
theorem B6205697 : Blo 2119435 6205697 := bstep (se 2 (by rfl) ⟨2327136, by rfl⟩ : syracuseStep 6205697 = 4654273) B4654273
theorem B4137131 : Blo 2119435 4137131 := bstep (se 1 (by rfl) ⟨3102848, by rfl⟩ : syracuseStep 4137131 = 6205697) B6205697
theorem B2758087 : Blo 2119435 2758087 := bstep (se 1 (by rfl) ⟨2068565, by rfl⟩ : syracuseStep 2758087 = 4137131) B4137131
theorem B3677449 : Blo 2119435 3677449 := bstep (se 2 (by rfl) ⟨1379043, by rfl⟩ : syracuseStep 3677449 = 2758087) B2758087
theorem B4903265 : Blo 2119435 4903265 := bstep (se 2 (by rfl) ⟨1838724, by rfl⟩ : syracuseStep 4903265 = 3677449) B3677449
theorem B13075373 : Blo 2119435 13075373 := bstep (se 3 (by rfl) ⟨2451632, by rfl⟩ : syracuseStep 13075373 = 4903265) B4903265
theorem B8716915 : Blo 2119435 8716915 := bstep (se 1 (by rfl) ⟨6537686, by rfl⟩ : syracuseStep 8716915 = 13075373) B13075373
theorem B46490213 : Blo 2119435 46490213 := bstep (se 4 (by rfl) ⟨4358457, by rfl⟩ : syracuseStep 46490213 = 8716915) B8716915
theorem B123973901 : Blo 2119435 123973901 := bstep (se 3 (by rfl) ⟨23245106, by rfl⟩ : syracuseStep 123973901 = 46490213) B46490213
theorem B82649267 : Blo 2119435 82649267 := bstep (se 1 (by rfl) ⟨61986950, by rfl⟩ : syracuseStep 82649267 = 123973901) B123973901
theorem B55099511 : Blo 2119435 55099511 := bstep (se 1 (by rfl) ⟨41324633, by rfl⟩ : syracuseStep 55099511 = 82649267) B82649267
theorem B36733007 : Blo 2119435 36733007 := bstep (se 1 (by rfl) ⟨27549755, by rfl⟩ : syracuseStep 36733007 = 55099511) B55099511
theorem B24488671 : Blo 2119435 24488671 := bstep (se 1 (by rfl) ⟨18366503, by rfl⟩ : syracuseStep 24488671 = 36733007) B36733007
theorem B32651561 : Blo 2119435 32651561 := bstep (se 2 (by rfl) ⟨12244335, by rfl⟩ : syracuseStep 32651561 = 24488671) B24488671
theorem B21767707 : Blo 2119435 21767707 := bstep (se 1 (by rfl) ⟨16325780, by rfl⟩ : syracuseStep 21767707 = 32651561) B32651561
theorem B29023609 : Blo 2119435 29023609 := bstep (se 2 (by rfl) ⟨10883853, by rfl⟩ : syracuseStep 29023609 = 21767707) B21767707
theorem B38698145 : Blo 2119435 38698145 := bstep (se 2 (by rfl) ⟨14511804, by rfl⟩ : syracuseStep 38698145 = 29023609) B29023609
theorem B25798763 : Blo 2119435 25798763 := bstep (se 1 (by rfl) ⟨19349072, by rfl⟩ : syracuseStep 25798763 = 38698145) B38698145
theorem B68796701 : Blo 2119435 68796701 := bstep (se 3 (by rfl) ⟨12899381, by rfl⟩ : syracuseStep 68796701 = 25798763) B25798763
theorem B45864467 : Blo 2119435 45864467 := bstep (se 1 (by rfl) ⟨34398350, by rfl⟩ : syracuseStep 45864467 = 68796701) B68796701
theorem B30576311 : Blo 2119435 30576311 := bstep (se 1 (by rfl) ⟨22932233, by rfl⟩ : syracuseStep 30576311 = 45864467) B45864467
theorem B20384207 : Blo 2119435 20384207 := bstep (se 1 (by rfl) ⟨15288155, by rfl⟩ : syracuseStep 20384207 = 30576311) B30576311
theorem B13589471 : Blo 2119435 13589471 := bstep (se 1 (by rfl) ⟨10192103, by rfl⟩ : syracuseStep 13589471 = 20384207) B20384207
theorem B36238589 : Blo 2119435 36238589 := bstep (se 3 (by rfl) ⟨6794735, by rfl⟩ : syracuseStep 36238589 = 13589471) B13589471
theorem B24159059 : Blo 2119435 24159059 := bstep (se 1 (by rfl) ⟨18119294, by rfl⟩ : syracuseStep 24159059 = 36238589) B36238589
theorem B16106039 : Blo 2119435 16106039 := bstep (se 1 (by rfl) ⟨12079529, by rfl⟩ : syracuseStep 16106039 = 24159059) B24159059
theorem B10737359 : Blo 2119435 10737359 := bstep (se 1 (by rfl) ⟨8053019, by rfl⟩ : syracuseStep 10737359 = 16106039) B16106039
theorem B7158239 : Blo 2119435 7158239 := bstep (se 1 (by rfl) ⟨5368679, by rfl⟩ : syracuseStep 7158239 = 10737359) B10737359
theorem B4772159 : Blo 2119435 4772159 := bstep (se 1 (by rfl) ⟨3579119, by rfl⟩ : syracuseStep 4772159 = 7158239) B7158239
theorem B3181439 : Blo 2119435 3181439 := bstep (se 1 (by rfl) ⟨2386079, by rfl⟩ : syracuseStep 3181439 = 4772159) B4772159
theorem B2120959 : Blo 2119435 2120959 := bstep (se 1 (by rfl) ⟨1590719, by rfl⟩ : syracuseStep 2120959 = 3181439) B3181439
theorem B3181445 : Blo 2119435 3181445 := bbase (se 4 (by rfl) ⟨298260, by rfl⟩ : syracuseStep 3181445 = 596521) (by norm_num)
theorem B2120963 : Blo 2119435 2120963 := bstep (se 1 (by rfl) ⟨1590722, by rfl⟩ : syracuseStep 2120963 = 3181445) B3181445
theorem B3579133 : Blo 2119435 3579133 := bbase (se 3 (by rfl) ⟨671087, by rfl⟩ : syracuseStep 3579133 = 1342175) (by norm_num)
theorem B4772177 : Blo 2119435 4772177 := bstep (se 2 (by rfl) ⟨1789566, by rfl⟩ : syracuseStep 4772177 = 3579133) B3579133
theorem B3181451 : Blo 2119435 3181451 := bstep (se 1 (by rfl) ⟨2386088, by rfl⟩ : syracuseStep 3181451 = 4772177) B4772177
theorem B2120967 : Blo 2119435 2120967 := bstep (se 1 (by rfl) ⟨1590725, by rfl⟩ : syracuseStep 2120967 = 3181451) B3181451
theorem B2386093 : Blo 2119435 2386093 := bbase (se 3 (by rfl) ⟨447392, by rfl⟩ : syracuseStep 2386093 = 894785) (by norm_num)
theorem B3181457 : Blo 2119435 3181457 := bstep (se 2 (by rfl) ⟨1193046, by rfl⟩ : syracuseStep 3181457 = 2386093) B2386093
theorem B2120971 : Blo 2119435 2120971 := bstep (se 1 (by rfl) ⟨1590728, by rfl⟩ : syracuseStep 2120971 = 3181457) B3181457
theorem B7158293 : Blo 2119435 7158293 := bbase (se 6 (by rfl) ⟨167772, by rfl⟩ : syracuseStep 7158293 = 335545) (by norm_num)
theorem B4772195 : Blo 2119435 4772195 := bstep (se 1 (by rfl) ⟨3579146, by rfl⟩ : syracuseStep 4772195 = 7158293) B7158293
theorem B3181463 : Blo 2119435 3181463 := bstep (se 1 (by rfl) ⟨2386097, by rfl⟩ : syracuseStep 3181463 = 4772195) B4772195
theorem B2120975 : Blo 2119435 2120975 := bstep (se 1 (by rfl) ⟨1590731, by rfl⟩ : syracuseStep 2120975 = 3181463) B3181463
theorem B3181469 : Blo 2119435 3181469 := bbase (se 3 (by rfl) ⟨596525, by rfl⟩ : syracuseStep 3181469 = 1193051) (by norm_num)
theorem B2120979 : Blo 2119435 2120979 := bstep (se 1 (by rfl) ⟨1590734, by rfl⟩ : syracuseStep 2120979 = 3181469) B3181469
theorem B4772213 : Blo 2119435 4772213 := bbase (se 5 (by rfl) ⟨223697, by rfl⟩ : syracuseStep 4772213 = 447395) (by norm_num)
theorem B3181475 : Blo 2119435 3181475 := bstep (se 1 (by rfl) ⟨2386106, by rfl⟩ : syracuseStep 3181475 = 4772213) B4772213
theorem B2120983 : Blo 2119435 2120983 := bstep (se 1 (by rfl) ⟨1590737, by rfl⟩ : syracuseStep 2120983 = 3181475) B3181475
theorem B13589653 : Blo 2119435 13589653 := bbase (se 6 (by rfl) ⟨318507, by rfl⟩ : syracuseStep 13589653 = 637015) (by norm_num)
theorem B18119537 : Blo 2119435 18119537 := bstep (se 2 (by rfl) ⟨6794826, by rfl⟩ : syracuseStep 18119537 = 13589653) B13589653
theorem B12079691 : Blo 2119435 12079691 := bstep (se 1 (by rfl) ⟨9059768, by rfl⟩ : syracuseStep 12079691 = 18119537) B18119537
theorem B8053127 : Blo 2119435 8053127 := bstep (se 1 (by rfl) ⟨6039845, by rfl⟩ : syracuseStep 8053127 = 12079691) B12079691
theorem B5368751 : Blo 2119435 5368751 := bstep (se 1 (by rfl) ⟨4026563, by rfl⟩ : syracuseStep 5368751 = 8053127) B8053127
theorem B3579167 : Blo 2119435 3579167 := bstep (se 1 (by rfl) ⟨2684375, by rfl⟩ : syracuseStep 3579167 = 5368751) B5368751
theorem B2386111 : Blo 2119435 2386111 := bstep (se 1 (by rfl) ⟨1789583, by rfl⟩ : syracuseStep 2386111 = 3579167) B3579167
theorem B3181481 : Blo 2119435 3181481 := bstep (se 2 (by rfl) ⟨1193055, by rfl⟩ : syracuseStep 3181481 = 2386111) B2386111
theorem B2120987 : Blo 2119435 2120987 := bstep (se 1 (by rfl) ⟨1590740, by rfl⟩ : syracuseStep 2120987 = 3181481) B3181481
theorem B8053141 : Blo 2119435 8053141 := bbase (se 6 (by rfl) ⟨188745, by rfl⟩ : syracuseStep 8053141 = 377491) (by norm_num)
theorem B10737521 : Blo 2119435 10737521 := bstep (se 2 (by rfl) ⟨4026570, by rfl⟩ : syracuseStep 10737521 = 8053141) B8053141
theorem B7158347 : Blo 2119435 7158347 := bstep (se 1 (by rfl) ⟨5368760, by rfl⟩ : syracuseStep 7158347 = 10737521) B10737521
theorem B4772231 : Blo 2119435 4772231 := bstep (se 1 (by rfl) ⟨3579173, by rfl⟩ : syracuseStep 4772231 = 7158347) B7158347
theorem B3181487 : Blo 2119435 3181487 := bstep (se 1 (by rfl) ⟨2386115, by rfl⟩ : syracuseStep 3181487 = 4772231) B4772231
theorem B2120991 : Blo 2119435 2120991 := bstep (se 1 (by rfl) ⟨1590743, by rfl⟩ : syracuseStep 2120991 = 3181487) B3181487
theorem B3181493 : Blo 2119435 3181493 := bbase (se 5 (by rfl) ⟨149132, by rfl⟩ : syracuseStep 3181493 = 298265) (by norm_num)
theorem B2120995 : Blo 2119435 2120995 := bstep (se 1 (by rfl) ⟨1590746, by rfl⟩ : syracuseStep 2120995 = 3181493) B3181493
theorem B5368781 : Blo 2119435 5368781 := bbase (se 3 (by rfl) ⟨1006646, by rfl⟩ : syracuseStep 5368781 = 2013293) (by norm_num)
theorem B3579187 : Blo 2119435 3579187 := bstep (se 1 (by rfl) ⟨2684390, by rfl⟩ : syracuseStep 3579187 = 5368781) B5368781
theorem B4772249 : Blo 2119435 4772249 := bstep (se 2 (by rfl) ⟨1789593, by rfl⟩ : syracuseStep 4772249 = 3579187) B3579187
theorem B3181499 : Blo 2119435 3181499 := bstep (se 1 (by rfl) ⟨2386124, by rfl⟩ : syracuseStep 3181499 = 4772249) B4772249
theorem B2120999 : Blo 2119435 2120999 := bstep (se 1 (by rfl) ⟨1590749, by rfl⟩ : syracuseStep 2120999 = 3181499) B3181499
theorem B2386129 : Blo 2119435 2386129 := bbase (se 2 (by rfl) ⟨894798, by rfl⟩ : syracuseStep 2386129 = 1789597) (by norm_num)
theorem B3181505 : Blo 2119435 3181505 := bstep (se 2 (by rfl) ⟨1193064, by rfl⟩ : syracuseStep 3181505 = 2386129) B2386129
theorem B2121003 : Blo 2119435 2121003 := bstep (se 1 (by rfl) ⟨1590752, by rfl⟩ : syracuseStep 2121003 = 3181505) B3181505
theorem B4299893 : Blo 2119435 4299893 := bbase (se 5 (by rfl) ⟨201557, by rfl⟩ : syracuseStep 4299893 = 403115) (by norm_num)
theorem B2866595 : Blo 2119435 2866595 := bstep (se 1 (by rfl) ⟨2149946, by rfl⟩ : syracuseStep 2866595 = 4299893) B4299893
theorem B7644253 : Blo 2119435 7644253 := bstep (se 3 (by rfl) ⟨1433297, by rfl⟩ : syracuseStep 7644253 = 2866595) B2866595
theorem B10192337 : Blo 2119435 10192337 := bstep (se 2 (by rfl) ⟨3822126, by rfl⟩ : syracuseStep 10192337 = 7644253) B7644253
theorem B6794891 : Blo 2119435 6794891 := bstep (se 1 (by rfl) ⟨5096168, by rfl⟩ : syracuseStep 6794891 = 10192337) B10192337
theorem B4529927 : Blo 2119435 4529927 := bstep (se 1 (by rfl) ⟨3397445, by rfl⟩ : syracuseStep 4529927 = 6794891) B6794891
theorem B3019951 : Blo 2119435 3019951 := bstep (se 1 (by rfl) ⟨2264963, by rfl⟩ : syracuseStep 3019951 = 4529927) B4529927
theorem B4026601 : Blo 2119435 4026601 := bstep (se 2 (by rfl) ⟨1509975, by rfl⟩ : syracuseStep 4026601 = 3019951) B3019951
theorem B5368801 : Blo 2119435 5368801 := bstep (se 2 (by rfl) ⟨2013300, by rfl⟩ : syracuseStep 5368801 = 4026601) B4026601
theorem B7158401 : Blo 2119435 7158401 := bstep (se 2 (by rfl) ⟨2684400, by rfl⟩ : syracuseStep 7158401 = 5368801) B5368801
theorem B4772267 : Blo 2119435 4772267 := bstep (se 1 (by rfl) ⟨3579200, by rfl⟩ : syracuseStep 4772267 = 7158401) B7158401
theorem B3181511 : Blo 2119435 3181511 := bstep (se 1 (by rfl) ⟨2386133, by rfl⟩ : syracuseStep 3181511 = 4772267) B4772267
theorem B2121007 : Blo 2119435 2121007 := bstep (se 1 (by rfl) ⟨1590755, by rfl⟩ : syracuseStep 2121007 = 3181511) B3181511
theorem B3181517 : Blo 2119435 3181517 := bbase (se 3 (by rfl) ⟨596534, by rfl⟩ : syracuseStep 3181517 = 1193069) (by norm_num)
theorem B2121011 : Blo 2119435 2121011 := bstep (se 1 (by rfl) ⟨1590758, by rfl⟩ : syracuseStep 2121011 = 3181517) B3181517
theorem B4772285 : Blo 2119435 4772285 := bbase (se 3 (by rfl) ⟨894803, by rfl⟩ : syracuseStep 4772285 = 1789607) (by norm_num)
theorem B3181523 : Blo 2119435 3181523 := bstep (se 1 (by rfl) ⟨2386142, by rfl⟩ : syracuseStep 3181523 = 4772285) B4772285
theorem B2121015 : Blo 2119435 2121015 := bstep (se 1 (by rfl) ⟨1590761, by rfl⟩ : syracuseStep 2121015 = 3181523) B3181523
theorem B3579221 : Blo 2119435 3579221 := bbase (se 11 (by rfl) ⟨2621, by rfl⟩ : syracuseStep 3579221 = 5243) (by norm_num)
theorem B2386147 : Blo 2119435 2386147 := bstep (se 1 (by rfl) ⟨1789610, by rfl⟩ : syracuseStep 2386147 = 3579221) B3579221
theorem B3181529 : Blo 2119435 3181529 := bstep (se 2 (by rfl) ⟨1193073, by rfl⟩ : syracuseStep 3181529 = 2386147) B2386147
theorem B2121019 : Blo 2119435 2121019 := bstep (se 1 (by rfl) ⟨1590764, by rfl⟩ : syracuseStep 2121019 = 3181529) B3181529
theorem B4299925 : Blo 2119435 4299925 := bbase (se 6 (by rfl) ⟨100779, by rfl⟩ : syracuseStep 4299925 = 201559) (by norm_num)
theorem B5733233 : Blo 2119435 5733233 := bstep (se 2 (by rfl) ⟨2149962, by rfl⟩ : syracuseStep 5733233 = 4299925) B4299925
theorem B3822155 : Blo 2119435 3822155 := bstep (se 1 (by rfl) ⟨2866616, by rfl⟩ : syracuseStep 3822155 = 5733233) B5733233
theorem B2548103 : Blo 2119435 2548103 := bstep (se 1 (by rfl) ⟨1911077, by rfl⟩ : syracuseStep 2548103 = 3822155) B3822155
theorem B6794941 : Blo 2119435 6794941 := bstep (se 3 (by rfl) ⟨1274051, by rfl⟩ : syracuseStep 6794941 = 2548103) B2548103
theorem B9059921 : Blo 2119435 9059921 := bstep (se 2 (by rfl) ⟨3397470, by rfl⟩ : syracuseStep 9059921 = 6794941) B6794941
theorem B6039947 : Blo 2119435 6039947 := bstep (se 1 (by rfl) ⟨4529960, by rfl⟩ : syracuseStep 6039947 = 9059921) B9059921
theorem B16106525 : Blo 2119435 16106525 := bstep (se 3 (by rfl) ⟨3019973, by rfl⟩ : syracuseStep 16106525 = 6039947) B6039947
theorem B10737683 : Blo 2119435 10737683 := bstep (se 1 (by rfl) ⟨8053262, by rfl⟩ : syracuseStep 10737683 = 16106525) B16106525
theorem B7158455 : Blo 2119435 7158455 := bstep (se 1 (by rfl) ⟨5368841, by rfl⟩ : syracuseStep 7158455 = 10737683) B10737683
theorem B4772303 : Blo 2119435 4772303 := bstep (se 1 (by rfl) ⟨3579227, by rfl⟩ : syracuseStep 4772303 = 7158455) B7158455
theorem B3181535 : Blo 2119435 3181535 := bstep (se 1 (by rfl) ⟨2386151, by rfl⟩ : syracuseStep 3181535 = 4772303) B4772303
theorem B2121023 : Blo 2119435 2121023 := bstep (se 1 (by rfl) ⟨1590767, by rfl⟩ : syracuseStep 2121023 = 3181535) B3181535
theorem B3181541 : Blo 2119435 3181541 := bbase (se 4 (by rfl) ⟨298269, by rfl⟩ : syracuseStep 3181541 = 596539) (by norm_num)
theorem B2121027 : Blo 2119435 2121027 := bstep (se 1 (by rfl) ⟨1590770, by rfl⟩ : syracuseStep 2121027 = 3181541) B3181541
theorem B9059957 : Blo 2119435 9059957 := bbase (se 5 (by rfl) ⟨424685, by rfl⟩ : syracuseStep 9059957 = 849371) (by norm_num)
theorem B6039971 : Blo 2119435 6039971 := bstep (se 1 (by rfl) ⟨4529978, by rfl⟩ : syracuseStep 6039971 = 9059957) B9059957
theorem B4026647 : Blo 2119435 4026647 := bstep (se 1 (by rfl) ⟨3019985, by rfl⟩ : syracuseStep 4026647 = 6039971) B6039971
theorem B2684431 : Blo 2119435 2684431 := bstep (se 1 (by rfl) ⟨2013323, by rfl⟩ : syracuseStep 2684431 = 4026647) B4026647
theorem B3579241 : Blo 2119435 3579241 := bstep (se 2 (by rfl) ⟨1342215, by rfl⟩ : syracuseStep 3579241 = 2684431) B2684431
theorem B4772321 : Blo 2119435 4772321 := bstep (se 2 (by rfl) ⟨1789620, by rfl⟩ : syracuseStep 4772321 = 3579241) B3579241
theorem B3181547 : Blo 2119435 3181547 := bstep (se 1 (by rfl) ⟨2386160, by rfl⟩ : syracuseStep 3181547 = 4772321) B4772321
theorem B2121031 : Blo 2119435 2121031 := bstep (se 1 (by rfl) ⟨1590773, by rfl⟩ : syracuseStep 2121031 = 3181547) B3181547
theorem B2386165 : Blo 2119435 2386165 := bbase (se 5 (by rfl) ⟨111851, by rfl⟩ : syracuseStep 2386165 = 223703) (by norm_num)
theorem B3181553 : Blo 2119435 3181553 := bstep (se 2 (by rfl) ⟨1193082, by rfl⟩ : syracuseStep 3181553 = 2386165) B2386165
theorem B2121035 : Blo 2119435 2121035 := bstep (se 1 (by rfl) ⟨1590776, by rfl⟩ : syracuseStep 2121035 = 3181553) B3181553
theorem B2684441 : Blo 2119435 2684441 := bbase (se 2 (by rfl) ⟨1006665, by rfl⟩ : syracuseStep 2684441 = 2013331) (by norm_num)
theorem B7158509 : Blo 2119435 7158509 := bstep (se 3 (by rfl) ⟨1342220, by rfl⟩ : syracuseStep 7158509 = 2684441) B2684441
theorem B4772339 : Blo 2119435 4772339 := bstep (se 1 (by rfl) ⟨3579254, by rfl⟩ : syracuseStep 4772339 = 7158509) B7158509
theorem B3181559 : Blo 2119435 3181559 := bstep (se 1 (by rfl) ⟨2386169, by rfl⟩ : syracuseStep 3181559 = 4772339) B4772339
theorem B2121039 : Blo 2119435 2121039 := bstep (se 1 (by rfl) ⟨1590779, by rfl⟩ : syracuseStep 2121039 = 3181559) B3181559
theorem B3181565 : Blo 2119435 3181565 := bbase (se 3 (by rfl) ⟨596543, by rfl⟩ : syracuseStep 3181565 = 1193087) (by norm_num)
theorem B2121043 : Blo 2119435 2121043 := bstep (se 1 (by rfl) ⟨1590782, by rfl⟩ : syracuseStep 2121043 = 3181565) B3181565
theorem B4772357 : Blo 2119435 4772357 := bbase (se 4 (by rfl) ⟨447408, by rfl⟩ : syracuseStep 4772357 = 894817) (by norm_num)
theorem B3181571 : Blo 2119435 3181571 := bstep (se 1 (by rfl) ⟨2386178, by rfl⟩ : syracuseStep 3181571 = 4772357) B4772357
theorem B2121047 : Blo 2119435 2121047 := bstep (se 1 (by rfl) ⟨1590785, by rfl⟩ : syracuseStep 2121047 = 3181571) B3181571
theorem B4026685 : Blo 2119435 4026685 := bbase (se 3 (by rfl) ⟨755003, by rfl⟩ : syracuseStep 4026685 = 1510007) (by norm_num)
theorem B5368913 : Blo 2119435 5368913 := bstep (se 2 (by rfl) ⟨2013342, by rfl⟩ : syracuseStep 5368913 = 4026685) B4026685
theorem B3579275 : Blo 2119435 3579275 := bstep (se 1 (by rfl) ⟨2684456, by rfl⟩ : syracuseStep 3579275 = 5368913) B5368913
theorem B2386183 : Blo 2119435 2386183 := bstep (se 1 (by rfl) ⟨1789637, by rfl⟩ : syracuseStep 2386183 = 3579275) B3579275
theorem B3181577 : Blo 2119435 3181577 := bstep (se 2 (by rfl) ⟨1193091, by rfl⟩ : syracuseStep 3181577 = 2386183) B2386183
theorem B2121051 : Blo 2119435 2121051 := bstep (se 1 (by rfl) ⟨1590788, by rfl⟩ : syracuseStep 2121051 = 3181577) B3181577
theorem B10737845 : Blo 2119435 10737845 := bbase (se 5 (by rfl) ⟨503336, by rfl⟩ : syracuseStep 10737845 = 1006673) (by norm_num)
theorem B7158563 : Blo 2119435 7158563 := bstep (se 1 (by rfl) ⟨5368922, by rfl⟩ : syracuseStep 7158563 = 10737845) B10737845
theorem B4772375 : Blo 2119435 4772375 := bstep (se 1 (by rfl) ⟨3579281, by rfl⟩ : syracuseStep 4772375 = 7158563) B7158563
theorem B3181583 : Blo 2119435 3181583 := bstep (se 1 (by rfl) ⟨2386187, by rfl⟩ : syracuseStep 3181583 = 4772375) B4772375
theorem B2121055 : Blo 2119435 2121055 := bstep (se 1 (by rfl) ⟨1590791, by rfl⟩ : syracuseStep 2121055 = 3181583) B3181583
theorem B3181589 : Blo 2119435 3181589 := bbase (se 6 (by rfl) ⟨74568, by rfl⟩ : syracuseStep 3181589 = 149137) (by norm_num)
theorem B2121059 : Blo 2119435 2121059 := bstep (se 1 (by rfl) ⟨1590794, by rfl⟩ : syracuseStep 2121059 = 3181589) B3181589
theorem B17200021 : Blo 2119435 17200021 := bbase (se 6 (by rfl) ⟨403125, by rfl⟩ : syracuseStep 17200021 = 806251) (by norm_num)
theorem B22933361 : Blo 2119435 22933361 := bstep (se 2 (by rfl) ⟨8600010, by rfl⟩ : syracuseStep 22933361 = 17200021) B17200021
theorem B15288907 : Blo 2119435 15288907 := bstep (se 1 (by rfl) ⟨11466680, by rfl⟩ : syracuseStep 15288907 = 22933361) B22933361
theorem B20385209 : Blo 2119435 20385209 := bstep (se 2 (by rfl) ⟨7644453, by rfl⟩ : syracuseStep 20385209 = 15288907) B15288907
theorem B13590139 : Blo 2119435 13590139 := bstep (se 1 (by rfl) ⟨10192604, by rfl⟩ : syracuseStep 13590139 = 20385209) B20385209
theorem B18120185 : Blo 2119435 18120185 := bstep (se 2 (by rfl) ⟨6795069, by rfl⟩ : syracuseStep 18120185 = 13590139) B13590139
theorem B12080123 : Blo 2119435 12080123 := bstep (se 1 (by rfl) ⟨9060092, by rfl⟩ : syracuseStep 12080123 = 18120185) B18120185
theorem B8053415 : Blo 2119435 8053415 := bstep (se 1 (by rfl) ⟨6040061, by rfl⟩ : syracuseStep 8053415 = 12080123) B12080123
theorem B5368943 : Blo 2119435 5368943 := bstep (se 1 (by rfl) ⟨4026707, by rfl⟩ : syracuseStep 5368943 = 8053415) B8053415
theorem B3579295 : Blo 2119435 3579295 := bstep (se 1 (by rfl) ⟨2684471, by rfl⟩ : syracuseStep 3579295 = 5368943) B5368943
theorem B4772393 : Blo 2119435 4772393 := bstep (se 2 (by rfl) ⟨1789647, by rfl⟩ : syracuseStep 4772393 = 3579295) B3579295
theorem B3181595 : Blo 2119435 3181595 := bstep (se 1 (by rfl) ⟨2386196, by rfl⟩ : syracuseStep 3181595 = 4772393) B4772393
theorem B2121063 : Blo 2119435 2121063 := bstep (se 1 (by rfl) ⟨1590797, by rfl⟩ : syracuseStep 2121063 = 3181595) B3181595
theorem B2386201 : Blo 2119435 2386201 := bbase (se 2 (by rfl) ⟨894825, by rfl⟩ : syracuseStep 2386201 = 1789651) (by norm_num)
theorem B3181601 : Blo 2119435 3181601 := bstep (se 2 (by rfl) ⟨1193100, by rfl⟩ : syracuseStep 3181601 = 2386201) B2386201
theorem B2121067 : Blo 2119435 2121067 := bstep (se 1 (by rfl) ⟨1590800, by rfl⟩ : syracuseStep 2121067 = 3181601) B3181601
theorem B8053445 : Blo 2119435 8053445 := bbase (se 4 (by rfl) ⟨755010, by rfl⟩ : syracuseStep 8053445 = 1510021) (by norm_num)
theorem B5368963 : Blo 2119435 5368963 := bstep (se 1 (by rfl) ⟨4026722, by rfl⟩ : syracuseStep 5368963 = 8053445) B8053445
theorem B7158617 : Blo 2119435 7158617 := bstep (se 2 (by rfl) ⟨2684481, by rfl⟩ : syracuseStep 7158617 = 5368963) B5368963
theorem B4772411 : Blo 2119435 4772411 := bstep (se 1 (by rfl) ⟨3579308, by rfl⟩ : syracuseStep 4772411 = 7158617) B7158617
theorem B3181607 : Blo 2119435 3181607 := bstep (se 1 (by rfl) ⟨2386205, by rfl⟩ : syracuseStep 3181607 = 4772411) B4772411
theorem B2121071 : Blo 2119435 2121071 := bstep (se 1 (by rfl) ⟨1590803, by rfl⟩ : syracuseStep 2121071 = 3181607) B3181607
theorem B3181613 : Blo 2119435 3181613 := bbase (se 3 (by rfl) ⟨596552, by rfl⟩ : syracuseStep 3181613 = 1193105) (by norm_num)
theorem B2121075 : Blo 2119435 2121075 := bstep (se 1 (by rfl) ⟨1590806, by rfl⟩ : syracuseStep 2121075 = 3181613) B3181613
theorem B4772429 : Blo 2119435 4772429 := bbase (se 3 (by rfl) ⟨894830, by rfl⟩ : syracuseStep 4772429 = 1789661) (by norm_num)
theorem B3181619 : Blo 2119435 3181619 := bstep (se 1 (by rfl) ⟨2386214, by rfl⟩ : syracuseStep 3181619 = 4772429) B4772429
theorem B2121079 : Blo 2119435 2121079 := bstep (se 1 (by rfl) ⟨1590809, by rfl⟩ : syracuseStep 2121079 = 3181619) B3181619
theorem B2684497 : Blo 2119435 2684497 := bbase (se 2 (by rfl) ⟨1006686, by rfl⟩ : syracuseStep 2684497 = 2013373) (by norm_num)
theorem B3579329 : Blo 2119435 3579329 := bstep (se 2 (by rfl) ⟨1342248, by rfl⟩ : syracuseStep 3579329 = 2684497) B2684497
theorem B2386219 : Blo 2119435 2386219 := bstep (se 1 (by rfl) ⟨1789664, by rfl⟩ : syracuseStep 2386219 = 3579329) B3579329
theorem B3181625 : Blo 2119435 3181625 := bstep (se 2 (by rfl) ⟨1193109, by rfl⟩ : syracuseStep 3181625 = 2386219) B2386219
theorem B2121083 : Blo 2119435 2121083 := bstep (se 1 (by rfl) ⟨1590812, by rfl⟩ : syracuseStep 2121083 = 3181625) B3181625
theorem B3397573 : Blo 2119435 3397573 := bbase (se 4 (by rfl) ⟨318522, by rfl⟩ : syracuseStep 3397573 = 637045) (by norm_num)
theorem B4530097 : Blo 2119435 4530097 := bstep (se 2 (by rfl) ⟨1698786, by rfl⟩ : syracuseStep 4530097 = 3397573) B3397573
theorem B24160517 : Blo 2119435 24160517 := bstep (se 4 (by rfl) ⟨2265048, by rfl⟩ : syracuseStep 24160517 = 4530097) B4530097
theorem B16107011 : Blo 2119435 16107011 := bstep (se 1 (by rfl) ⟨12080258, by rfl⟩ : syracuseStep 16107011 = 24160517) B24160517
theorem B10738007 : Blo 2119435 10738007 := bstep (se 1 (by rfl) ⟨8053505, by rfl⟩ : syracuseStep 10738007 = 16107011) B16107011
theorem B7158671 : Blo 2119435 7158671 := bstep (se 1 (by rfl) ⟨5369003, by rfl⟩ : syracuseStep 7158671 = 10738007) B10738007
theorem B4772447 : Blo 2119435 4772447 := bstep (se 1 (by rfl) ⟨3579335, by rfl⟩ : syracuseStep 4772447 = 7158671) B7158671
theorem B3181631 : Blo 2119435 3181631 := bstep (se 1 (by rfl) ⟨2386223, by rfl⟩ : syracuseStep 3181631 = 4772447) B4772447
theorem B2121087 : Blo 2119435 2121087 := bstep (se 1 (by rfl) ⟨1590815, by rfl⟩ : syracuseStep 2121087 = 3181631) B3181631
theorem B3181637 : Blo 2119435 3181637 := bbase (se 4 (by rfl) ⟨298278, by rfl⟩ : syracuseStep 3181637 = 596557) (by norm_num)
theorem B2121091 : Blo 2119435 2121091 := bstep (se 1 (by rfl) ⟨1590818, by rfl⟩ : syracuseStep 2121091 = 3181637) B3181637
theorem B3579349 : Blo 2119435 3579349 := bbase (se 7 (by rfl) ⟨41945, by rfl⟩ : syracuseStep 3579349 = 83891) (by norm_num)
theorem B4772465 : Blo 2119435 4772465 := bstep (se 2 (by rfl) ⟨1789674, by rfl⟩ : syracuseStep 4772465 = 3579349) B3579349
theorem B3181643 : Blo 2119435 3181643 := bstep (se 1 (by rfl) ⟨2386232, by rfl⟩ : syracuseStep 3181643 = 4772465) B4772465
theorem B2121095 : Blo 2119435 2121095 := bstep (se 1 (by rfl) ⟨1590821, by rfl⟩ : syracuseStep 2121095 = 3181643) B3181643
theorem B2386237 : Blo 2119435 2386237 := bbase (se 3 (by rfl) ⟨447419, by rfl⟩ : syracuseStep 2386237 = 894839) (by norm_num)
theorem B3181649 : Blo 2119435 3181649 := bstep (se 2 (by rfl) ⟨1193118, by rfl⟩ : syracuseStep 3181649 = 2386237) B2386237
theorem B2121099 : Blo 2119435 2121099 := bstep (se 1 (by rfl) ⟨1590824, by rfl⟩ : syracuseStep 2121099 = 3181649) B3181649
theorem B7158725 : Blo 2119435 7158725 := bbase (se 4 (by rfl) ⟨671130, by rfl⟩ : syracuseStep 7158725 = 1342261) (by norm_num)
theorem B4772483 : Blo 2119435 4772483 := bstep (se 1 (by rfl) ⟨3579362, by rfl⟩ : syracuseStep 4772483 = 7158725) B7158725
theorem B3181655 : Blo 2119435 3181655 := bstep (se 1 (by rfl) ⟨2386241, by rfl⟩ : syracuseStep 3181655 = 4772483) B4772483
theorem B2121103 : Blo 2119435 2121103 := bstep (se 1 (by rfl) ⟨1590827, by rfl⟩ : syracuseStep 2121103 = 3181655) B3181655
theorem B3181661 : Blo 2119435 3181661 := bbase (se 3 (by rfl) ⟨596561, by rfl⟩ : syracuseStep 3181661 = 1193123) (by norm_num)
theorem B2121107 : Blo 2119435 2121107 := bstep (se 1 (by rfl) ⟨1590830, by rfl⟩ : syracuseStep 2121107 = 3181661) B3181661
theorem B4772501 : Blo 2119435 4772501 := bbase (se 6 (by rfl) ⟨111855, by rfl⟩ : syracuseStep 4772501 = 223711) (by norm_num)
theorem B3181667 : Blo 2119435 3181667 := bstep (se 1 (by rfl) ⟨2386250, by rfl⟩ : syracuseStep 3181667 = 4772501) B4772501
theorem B2121111 : Blo 2119435 2121111 := bstep (se 1 (by rfl) ⟨1590833, by rfl⟩ : syracuseStep 2121111 = 3181667) B3181667
theorem B5096429 : Blo 2119435 5096429 := bbase (se 3 (by rfl) ⟨955580, by rfl⟩ : syracuseStep 5096429 = 1911161) (by norm_num)
theorem B3397619 : Blo 2119435 3397619 := bstep (se 1 (by rfl) ⟨2548214, by rfl⟩ : syracuseStep 3397619 = 5096429) B5096429
theorem B2265079 : Blo 2119435 2265079 := bstep (se 1 (by rfl) ⟨1698809, by rfl⟩ : syracuseStep 2265079 = 3397619) B3397619
theorem B3020105 : Blo 2119435 3020105 := bstep (se 2 (by rfl) ⟨1132539, by rfl⟩ : syracuseStep 3020105 = 2265079) B2265079
theorem B8053613 : Blo 2119435 8053613 := bstep (se 3 (by rfl) ⟨1510052, by rfl⟩ : syracuseStep 8053613 = 3020105) B3020105
theorem B5369075 : Blo 2119435 5369075 := bstep (se 1 (by rfl) ⟨4026806, by rfl⟩ : syracuseStep 5369075 = 8053613) B8053613
theorem B3579383 : Blo 2119435 3579383 := bstep (se 1 (by rfl) ⟨2684537, by rfl⟩ : syracuseStep 3579383 = 5369075) B5369075
theorem B2386255 : Blo 2119435 2386255 := bstep (se 1 (by rfl) ⟨1789691, by rfl⟩ : syracuseStep 2386255 = 3579383) B3579383
theorem B3181673 : Blo 2119435 3181673 := bstep (se 2 (by rfl) ⟨1193127, by rfl⟩ : syracuseStep 3181673 = 2386255) B2386255
theorem B2121115 : Blo 2119435 2121115 := bstep (se 1 (by rfl) ⟨1590836, by rfl⟩ : syracuseStep 2121115 = 3181673) B3181673
theorem B4591973 : Blo 2119435 4591973 := bbase (se 4 (by rfl) ⟨430497, by rfl⟩ : syracuseStep 4591973 = 860995) (by norm_num)
theorem B12245261 : Blo 2119435 12245261 := bstep (se 3 (by rfl) ⟨2295986, by rfl⟩ : syracuseStep 12245261 = 4591973) B4591973
theorem B32654029 : Blo 2119435 32654029 := bstep (se 3 (by rfl) ⟨6122630, by rfl⟩ : syracuseStep 32654029 = 12245261) B12245261
theorem B43538705 : Blo 2119435 43538705 := bstep (se 2 (by rfl) ⟨16327014, by rfl⟩ : syracuseStep 43538705 = 32654029) B32654029
theorem B29025803 : Blo 2119435 29025803 := bstep (se 1 (by rfl) ⟨21769352, by rfl⟩ : syracuseStep 29025803 = 43538705) B43538705
theorem B19350535 : Blo 2119435 19350535 := bstep (se 1 (by rfl) ⟨14512901, by rfl⟩ : syracuseStep 19350535 = 29025803) B29025803
theorem B25800713 : Blo 2119435 25800713 := bstep (se 2 (by rfl) ⟨9675267, by rfl⟩ : syracuseStep 25800713 = 19350535) B19350535
theorem B17200475 : Blo 2119435 17200475 := bstep (se 1 (by rfl) ⟨12900356, by rfl⟩ : syracuseStep 17200475 = 25800713) B25800713
theorem B11466983 : Blo 2119435 11466983 := bstep (se 1 (by rfl) ⟨8600237, by rfl⟩ : syracuseStep 11466983 = 17200475) B17200475
theorem B7644655 : Blo 2119435 7644655 := bstep (se 1 (by rfl) ⟨5733491, by rfl⟩ : syracuseStep 7644655 = 11466983) B11466983
theorem B10192873 : Blo 2119435 10192873 := bstep (se 2 (by rfl) ⟨3822327, by rfl⟩ : syracuseStep 10192873 = 7644655) B7644655
theorem B13590497 : Blo 2119435 13590497 := bstep (se 2 (by rfl) ⟨5096436, by rfl⟩ : syracuseStep 13590497 = 10192873) B10192873
theorem B9060331 : Blo 2119435 9060331 := bstep (se 1 (by rfl) ⟨6795248, by rfl⟩ : syracuseStep 9060331 = 13590497) B13590497
theorem B12080441 : Blo 2119435 12080441 := bstep (se 2 (by rfl) ⟨4530165, by rfl⟩ : syracuseStep 12080441 = 9060331) B9060331
theorem B8053627 : Blo 2119435 8053627 := bstep (se 1 (by rfl) ⟨6040220, by rfl⟩ : syracuseStep 8053627 = 12080441) B12080441
theorem B10738169 : Blo 2119435 10738169 := bstep (se 2 (by rfl) ⟨4026813, by rfl⟩ : syracuseStep 10738169 = 8053627) B8053627
theorem B7158779 : Blo 2119435 7158779 := bstep (se 1 (by rfl) ⟨5369084, by rfl⟩ : syracuseStep 7158779 = 10738169) B10738169
theorem B4772519 : Blo 2119435 4772519 := bstep (se 1 (by rfl) ⟨3579389, by rfl⟩ : syracuseStep 4772519 = 7158779) B7158779
theorem B3181679 : Blo 2119435 3181679 := bstep (se 1 (by rfl) ⟨2386259, by rfl⟩ : syracuseStep 3181679 = 4772519) B4772519
theorem B2121119 : Blo 2119435 2121119 := bstep (se 1 (by rfl) ⟨1590839, by rfl⟩ : syracuseStep 2121119 = 3181679) B3181679
theorem B3181685 : Blo 2119435 3181685 := bbase (se 5 (by rfl) ⟨149141, by rfl⟩ : syracuseStep 3181685 = 298283) (by norm_num)
theorem B2121123 : Blo 2119435 2121123 := bstep (se 1 (by rfl) ⟨1590842, by rfl⟩ : syracuseStep 2121123 = 3181685) B3181685
theorem B4026829 : Blo 2119435 4026829 := bbase (se 3 (by rfl) ⟨755030, by rfl⟩ : syracuseStep 4026829 = 1510061) (by norm_num)
theorem B5369105 : Blo 2119435 5369105 := bstep (se 2 (by rfl) ⟨2013414, by rfl⟩ : syracuseStep 5369105 = 4026829) B4026829
theorem B3579403 : Blo 2119435 3579403 := bstep (se 1 (by rfl) ⟨2684552, by rfl⟩ : syracuseStep 3579403 = 5369105) B5369105
theorem B4772537 : Blo 2119435 4772537 := bstep (se 2 (by rfl) ⟨1789701, by rfl⟩ : syracuseStep 4772537 = 3579403) B3579403
theorem B3181691 : Blo 2119435 3181691 := bstep (se 1 (by rfl) ⟨2386268, by rfl⟩ : syracuseStep 3181691 = 4772537) B4772537
theorem B2121127 : Blo 2119435 2121127 := bstep (se 1 (by rfl) ⟨1590845, by rfl⟩ : syracuseStep 2121127 = 3181691) B3181691
theorem B2386273 : Blo 2119435 2386273 := bbase (se 2 (by rfl) ⟨894852, by rfl⟩ : syracuseStep 2386273 = 1789705) (by norm_num)
theorem B3181697 : Blo 2119435 3181697 := bstep (se 2 (by rfl) ⟨1193136, by rfl⟩ : syracuseStep 3181697 = 2386273) B2386273
theorem B2121131 : Blo 2119435 2121131 := bstep (se 1 (by rfl) ⟨1590848, by rfl⟩ : syracuseStep 2121131 = 3181697) B3181697
theorem B5369125 : Blo 2119435 5369125 := bbase (se 4 (by rfl) ⟨503355, by rfl⟩ : syracuseStep 5369125 = 1006711) (by norm_num)
theorem B7158833 : Blo 2119435 7158833 := bstep (se 2 (by rfl) ⟨2684562, by rfl⟩ : syracuseStep 7158833 = 5369125) B5369125
theorem B4772555 : Blo 2119435 4772555 := bstep (se 1 (by rfl) ⟨3579416, by rfl⟩ : syracuseStep 4772555 = 7158833) B7158833
theorem B3181703 : Blo 2119435 3181703 := bstep (se 1 (by rfl) ⟨2386277, by rfl⟩ : syracuseStep 3181703 = 4772555) B4772555
theorem B2121135 : Blo 2119435 2121135 := bstep (se 1 (by rfl) ⟨1590851, by rfl⟩ : syracuseStep 2121135 = 3181703) B3181703
theorem B3181709 : Blo 2119435 3181709 := bbase (se 3 (by rfl) ⟨596570, by rfl⟩ : syracuseStep 3181709 = 1193141) (by norm_num)
theorem B2121139 : Blo 2119435 2121139 := bstep (se 1 (by rfl) ⟨1590854, by rfl⟩ : syracuseStep 2121139 = 3181709) B3181709
theorem B4772573 : Blo 2119435 4772573 := bbase (se 3 (by rfl) ⟨894857, by rfl⟩ : syracuseStep 4772573 = 1789715) (by norm_num)
theorem B3181715 : Blo 2119435 3181715 := bstep (se 1 (by rfl) ⟨2386286, by rfl⟩ : syracuseStep 3181715 = 4772573) B4772573
theorem B2121143 : Blo 2119435 2121143 := bstep (se 1 (by rfl) ⟨1590857, by rfl⟩ : syracuseStep 2121143 = 3181715) B3181715
theorem B3579437 : Blo 2119435 3579437 := bbase (se 3 (by rfl) ⟨671144, by rfl⟩ : syracuseStep 3579437 = 1342289) (by norm_num)
theorem B2386291 : Blo 2119435 2386291 := bstep (se 1 (by rfl) ⟨1789718, by rfl⟩ : syracuseStep 2386291 = 3579437) B3579437
theorem B3181721 : Blo 2119435 3181721 := bstep (se 2 (by rfl) ⟨1193145, by rfl⟩ : syracuseStep 3181721 = 2386291) B2386291
theorem B2121147 : Blo 2119435 2121147 := bstep (se 1 (by rfl) ⟨1590860, by rfl⟩ : syracuseStep 2121147 = 3181721) B3181721
theorem B2418853 : Blo 2119435 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B51602197 : Blo 2119435 51602197 := bstep (se 6 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 51602197 = 2418853) B2418853
theorem B68802929 : Blo 2119435 68802929 := bstep (se 2 (by rfl) ⟨25801098, by rfl⟩ : syracuseStep 68802929 = 51602197) B51602197
theorem B45868619 : Blo 2119435 45868619 := bstep (se 1 (by rfl) ⟨34401464, by rfl⟩ : syracuseStep 45868619 = 68802929) B68802929
theorem B30579079 : Blo 2119435 30579079 := bstep (se 1 (by rfl) ⟨22934309, by rfl⟩ : syracuseStep 30579079 = 45868619) B45868619
theorem B40772105 : Blo 2119435 40772105 := bstep (se 2 (by rfl) ⟨15289539, by rfl⟩ : syracuseStep 40772105 = 30579079) B30579079
theorem B27181403 : Blo 2119435 27181403 := bstep (se 1 (by rfl) ⟨20386052, by rfl⟩ : syracuseStep 27181403 = 40772105) B40772105
theorem B18120935 : Blo 2119435 18120935 := bstep (se 1 (by rfl) ⟨13590701, by rfl⟩ : syracuseStep 18120935 = 27181403) B27181403
theorem B12080623 : Blo 2119435 12080623 := bstep (se 1 (by rfl) ⟨9060467, by rfl⟩ : syracuseStep 12080623 = 18120935) B18120935
theorem B16107497 : Blo 2119435 16107497 := bstep (se 2 (by rfl) ⟨6040311, by rfl⟩ : syracuseStep 16107497 = 12080623) B12080623
theorem B10738331 : Blo 2119435 10738331 := bstep (se 1 (by rfl) ⟨8053748, by rfl⟩ : syracuseStep 10738331 = 16107497) B16107497
theorem B7158887 : Blo 2119435 7158887 := bstep (se 1 (by rfl) ⟨5369165, by rfl⟩ : syracuseStep 7158887 = 10738331) B10738331
theorem B4772591 : Blo 2119435 4772591 := bstep (se 1 (by rfl) ⟨3579443, by rfl⟩ : syracuseStep 4772591 = 7158887) B7158887
theorem B3181727 : Blo 2119435 3181727 := bstep (se 1 (by rfl) ⟨2386295, by rfl⟩ : syracuseStep 3181727 = 4772591) B4772591
theorem B2121151 : Blo 2119435 2121151 := bstep (se 1 (by rfl) ⟨1590863, by rfl⟩ : syracuseStep 2121151 = 3181727) B3181727
theorem B3181733 : Blo 2119435 3181733 := bbase (se 4 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 3181733 = 596575) (by norm_num)
theorem B2121155 : Blo 2119435 2121155 := bstep (se 1 (by rfl) ⟨1590866, by rfl⟩ : syracuseStep 2121155 = 3181733) B3181733
theorem B2684593 : Blo 2119435 2684593 := bbase (se 2 (by rfl) ⟨1006722, by rfl⟩ : syracuseStep 2684593 = 2013445) (by norm_num)
theorem B3579457 : Blo 2119435 3579457 := bstep (se 2 (by rfl) ⟨1342296, by rfl⟩ : syracuseStep 3579457 = 2684593) B2684593
theorem B4772609 : Blo 2119435 4772609 := bstep (se 2 (by rfl) ⟨1789728, by rfl⟩ : syracuseStep 4772609 = 3579457) B3579457
theorem B3181739 : Blo 2119435 3181739 := bstep (se 1 (by rfl) ⟨2386304, by rfl⟩ : syracuseStep 3181739 = 4772609) B4772609
theorem B2121159 : Blo 2119435 2121159 := bstep (se 1 (by rfl) ⟨1590869, by rfl⟩ : syracuseStep 2121159 = 3181739) B3181739
theorem B2386309 : Blo 2119435 2386309 := bbase (se 4 (by rfl) ⟨223716, by rfl⟩ : syracuseStep 2386309 = 447433) (by norm_num)
theorem B3181745 : Blo 2119435 3181745 := bstep (se 2 (by rfl) ⟨1193154, by rfl⟩ : syracuseStep 3181745 = 2386309) B2386309
theorem B2121163 : Blo 2119435 2121163 := bstep (se 1 (by rfl) ⟨1590872, by rfl⟩ : syracuseStep 2121163 = 3181745) B3181745
theorem B4530269 : Blo 2119435 4530269 := bbase (se 3 (by rfl) ⟨849425, by rfl⟩ : syracuseStep 4530269 = 1698851) (by norm_num)
theorem B3020179 : Blo 2119435 3020179 := bstep (se 1 (by rfl) ⟨2265134, by rfl⟩ : syracuseStep 3020179 = 4530269) B4530269
theorem B4026905 : Blo 2119435 4026905 := bstep (se 2 (by rfl) ⟨1510089, by rfl⟩ : syracuseStep 4026905 = 3020179) B3020179
theorem B2684603 : Blo 2119435 2684603 := bstep (se 1 (by rfl) ⟨2013452, by rfl⟩ : syracuseStep 2684603 = 4026905) B4026905
theorem B7158941 : Blo 2119435 7158941 := bstep (se 3 (by rfl) ⟨1342301, by rfl⟩ : syracuseStep 7158941 = 2684603) B2684603
theorem B4772627 : Blo 2119435 4772627 := bstep (se 1 (by rfl) ⟨3579470, by rfl⟩ : syracuseStep 4772627 = 7158941) B7158941
theorem B3181751 : Blo 2119435 3181751 := bstep (se 1 (by rfl) ⟨2386313, by rfl⟩ : syracuseStep 3181751 = 4772627) B4772627
theorem B2121167 : Blo 2119435 2121167 := bstep (se 1 (by rfl) ⟨1590875, by rfl⟩ : syracuseStep 2121167 = 3181751) B3181751
theorem B3181757 : Blo 2119435 3181757 := bbase (se 3 (by rfl) ⟨596579, by rfl⟩ : syracuseStep 3181757 = 1193159) (by norm_num)
theorem B2121171 : Blo 2119435 2121171 := bstep (se 1 (by rfl) ⟨1590878, by rfl⟩ : syracuseStep 2121171 = 3181757) B3181757
theorem B4772645 : Blo 2119435 4772645 := bbase (se 4 (by rfl) ⟨447435, by rfl⟩ : syracuseStep 4772645 = 894871) (by norm_num)
theorem B3181763 : Blo 2119435 3181763 := bstep (se 1 (by rfl) ⟨2386322, by rfl⟩ : syracuseStep 3181763 = 4772645) B4772645
theorem B2121175 : Blo 2119435 2121175 := bstep (se 1 (by rfl) ⟨1590881, by rfl⟩ : syracuseStep 2121175 = 3181763) B3181763
theorem B5369237 : Blo 2119435 5369237 := bbase (se 6 (by rfl) ⟨125841, by rfl⟩ : syracuseStep 5369237 = 251683) (by norm_num)
theorem B3579491 : Blo 2119435 3579491 := bstep (se 1 (by rfl) ⟨2684618, by rfl⟩ : syracuseStep 3579491 = 5369237) B5369237
theorem B2386327 : Blo 2119435 2386327 := bstep (se 1 (by rfl) ⟨1789745, by rfl⟩ : syracuseStep 2386327 = 3579491) B3579491
theorem B3181769 : Blo 2119435 3181769 := bstep (se 2 (by rfl) ⟨1193163, by rfl⟩ : syracuseStep 3181769 = 2386327) B2386327
theorem B2121179 : Blo 2119435 2121179 := bstep (se 1 (by rfl) ⟨1590884, by rfl⟩ : syracuseStep 2121179 = 3181769) B3181769
theorem B4837781 : Blo 2119435 4837781 := bbase (se 6 (by rfl) ⟨113385, by rfl⟩ : syracuseStep 4837781 = 226771) (by norm_num)
theorem B3225187 : Blo 2119435 3225187 := bstep (se 1 (by rfl) ⟨2418890, by rfl⟩ : syracuseStep 3225187 = 4837781) B4837781
theorem B17200997 : Blo 2119435 17200997 := bstep (se 4 (by rfl) ⟨1612593, by rfl⟩ : syracuseStep 17200997 = 3225187) B3225187
theorem B11467331 : Blo 2119435 11467331 := bstep (se 1 (by rfl) ⟨8600498, by rfl⟩ : syracuseStep 11467331 = 17200997) B17200997
theorem B7644887 : Blo 2119435 7644887 := bstep (se 1 (by rfl) ⟨5733665, by rfl⟩ : syracuseStep 7644887 = 11467331) B11467331
theorem B5096591 : Blo 2119435 5096591 := bstep (se 1 (by rfl) ⟨3822443, by rfl⟩ : syracuseStep 5096591 = 7644887) B7644887
theorem B3397727 : Blo 2119435 3397727 := bstep (se 1 (by rfl) ⟨2548295, by rfl⟩ : syracuseStep 3397727 = 5096591) B5096591
theorem B9060605 : Blo 2119435 9060605 := bstep (se 3 (by rfl) ⟨1698863, by rfl⟩ : syracuseStep 9060605 = 3397727) B3397727
theorem B6040403 : Blo 2119435 6040403 := bstep (se 1 (by rfl) ⟨4530302, by rfl⟩ : syracuseStep 6040403 = 9060605) B9060605
theorem B4026935 : Blo 2119435 4026935 := bstep (se 1 (by rfl) ⟨3020201, by rfl⟩ : syracuseStep 4026935 = 6040403) B6040403
theorem B10738493 : Blo 2119435 10738493 := bstep (se 3 (by rfl) ⟨2013467, by rfl⟩ : syracuseStep 10738493 = 4026935) B4026935
theorem B7158995 : Blo 2119435 7158995 := bstep (se 1 (by rfl) ⟨5369246, by rfl⟩ : syracuseStep 7158995 = 10738493) B10738493
theorem B4772663 : Blo 2119435 4772663 := bstep (se 1 (by rfl) ⟨3579497, by rfl⟩ : syracuseStep 4772663 = 7158995) B7158995
theorem B3181775 : Blo 2119435 3181775 := bstep (se 1 (by rfl) ⟨2386331, by rfl⟩ : syracuseStep 3181775 = 4772663) B4772663
theorem B2121183 : Blo 2119435 2121183 := bstep (se 1 (by rfl) ⟨1590887, by rfl⟩ : syracuseStep 2121183 = 3181775) B3181775
theorem B3181781 : Blo 2119435 3181781 := bbase (se 7 (by rfl) ⟨37286, by rfl⟩ : syracuseStep 3181781 = 74573) (by norm_num)
theorem B2121187 : Blo 2119435 2121187 := bstep (se 1 (by rfl) ⟨1590890, by rfl⟩ : syracuseStep 2121187 = 3181781) B3181781
theorem B3020213 : Blo 2119435 3020213 := bbase (se 5 (by rfl) ⟨141572, by rfl⟩ : syracuseStep 3020213 = 283145) (by norm_num)
theorem B8053901 : Blo 2119435 8053901 := bstep (se 3 (by rfl) ⟨1510106, by rfl⟩ : syracuseStep 8053901 = 3020213) B3020213
theorem B5369267 : Blo 2119435 5369267 := bstep (se 1 (by rfl) ⟨4026950, by rfl⟩ : syracuseStep 5369267 = 8053901) B8053901
theorem B3579511 : Blo 2119435 3579511 := bstep (se 1 (by rfl) ⟨2684633, by rfl⟩ : syracuseStep 3579511 = 5369267) B5369267
theorem B4772681 : Blo 2119435 4772681 := bstep (se 2 (by rfl) ⟨1789755, by rfl⟩ : syracuseStep 4772681 = 3579511) B3579511
theorem B3181787 : Blo 2119435 3181787 := bstep (se 1 (by rfl) ⟨2386340, by rfl⟩ : syracuseStep 3181787 = 4772681) B4772681
theorem B2121191 : Blo 2119435 2121191 := bstep (se 1 (by rfl) ⟨1590893, by rfl⟩ : syracuseStep 2121191 = 3181787) B3181787
theorem B2386345 : Blo 2119435 2386345 := bbase (se 2 (by rfl) ⟨894879, by rfl⟩ : syracuseStep 2386345 = 1789759) (by norm_num)
theorem B3181793 : Blo 2119435 3181793 := bstep (se 2 (by rfl) ⟨1193172, by rfl⟩ : syracuseStep 3181793 = 2386345) B2386345
theorem B2121195 : Blo 2119435 2121195 := bstep (se 1 (by rfl) ⟨1590896, by rfl⟩ : syracuseStep 2121195 = 3181793) B3181793
theorem B5096629 : Blo 2119435 5096629 := bbase (se 5 (by rfl) ⟨238904, by rfl⟩ : syracuseStep 5096629 = 477809) (by norm_num)
theorem B6795505 : Blo 2119435 6795505 := bstep (se 2 (by rfl) ⟨2548314, by rfl⟩ : syracuseStep 6795505 = 5096629) B5096629
theorem B9060673 : Blo 2119435 9060673 := bstep (se 2 (by rfl) ⟨3397752, by rfl⟩ : syracuseStep 9060673 = 6795505) B6795505
theorem B12080897 : Blo 2119435 12080897 := bstep (se 2 (by rfl) ⟨4530336, by rfl⟩ : syracuseStep 12080897 = 9060673) B9060673
theorem B8053931 : Blo 2119435 8053931 := bstep (se 1 (by rfl) ⟨6040448, by rfl⟩ : syracuseStep 8053931 = 12080897) B12080897
theorem B5369287 : Blo 2119435 5369287 := bstep (se 1 (by rfl) ⟨4026965, by rfl⟩ : syracuseStep 5369287 = 8053931) B8053931
theorem B7159049 : Blo 2119435 7159049 := bstep (se 2 (by rfl) ⟨2684643, by rfl⟩ : syracuseStep 7159049 = 5369287) B5369287
theorem B4772699 : Blo 2119435 4772699 := bstep (se 1 (by rfl) ⟨3579524, by rfl⟩ : syracuseStep 4772699 = 7159049) B7159049
theorem B3181799 : Blo 2119435 3181799 := bstep (se 1 (by rfl) ⟨2386349, by rfl⟩ : syracuseStep 3181799 = 4772699) B4772699
theorem B2121199 : Blo 2119435 2121199 := bstep (se 1 (by rfl) ⟨1590899, by rfl⟩ : syracuseStep 2121199 = 3181799) B3181799
theorem B3181805 : Blo 2119435 3181805 := bbase (se 3 (by rfl) ⟨596588, by rfl⟩ : syracuseStep 3181805 = 1193177) (by norm_num)
theorem B2121203 : Blo 2119435 2121203 := bstep (se 1 (by rfl) ⟨1590902, by rfl⟩ : syracuseStep 2121203 = 3181805) B3181805
theorem B4772717 : Blo 2119435 4772717 := bbase (se 3 (by rfl) ⟨894884, by rfl⟩ : syracuseStep 4772717 = 1789769) (by norm_num)
theorem B3181811 : Blo 2119435 3181811 := bstep (se 1 (by rfl) ⟨2386358, by rfl⟩ : syracuseStep 3181811 = 4772717) B4772717
theorem B2121207 : Blo 2119435 2121207 := bstep (se 1 (by rfl) ⟨1590905, by rfl⟩ : syracuseStep 2121207 = 3181811) B3181811
theorem B4026989 : Blo 2119435 4026989 := bbase (se 3 (by rfl) ⟨755060, by rfl⟩ : syracuseStep 4026989 = 1510121) (by norm_num)
theorem B2684659 : Blo 2119435 2684659 := bstep (se 1 (by rfl) ⟨2013494, by rfl⟩ : syracuseStep 2684659 = 4026989) B4026989
theorem B3579545 : Blo 2119435 3579545 := bstep (se 2 (by rfl) ⟨1342329, by rfl⟩ : syracuseStep 3579545 = 2684659) B2684659
theorem B2386363 : Blo 2119435 2386363 := bstep (se 1 (by rfl) ⟨1789772, by rfl⟩ : syracuseStep 2386363 = 3579545) B3579545
theorem B3181817 : Blo 2119435 3181817 := bstep (se 2 (by rfl) ⟨1193181, by rfl⟩ : syracuseStep 3181817 = 2386363) B2386363
theorem B2121211 : Blo 2119435 2121211 := bstep (se 1 (by rfl) ⟨1590908, by rfl⟩ : syracuseStep 2121211 = 3181817) B3181817
theorem B25801877 : Blo 2119435 25801877 := bbase (se 6 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 25801877 = 1209463) (by norm_num)
theorem B17201251 : Blo 2119435 17201251 := bstep (se 1 (by rfl) ⟨12900938, by rfl⟩ : syracuseStep 17201251 = 25801877) B25801877
theorem B22935001 : Blo 2119435 22935001 := bstep (se 2 (by rfl) ⟨8600625, by rfl⟩ : syracuseStep 22935001 = 17201251) B17201251
theorem B30580001 : Blo 2119435 30580001 := bstep (se 2 (by rfl) ⟨11467500, by rfl⟩ : syracuseStep 30580001 = 22935001) B22935001
theorem B20386667 : Blo 2119435 20386667 := bstep (se 1 (by rfl) ⟨15290000, by rfl⟩ : syracuseStep 20386667 = 30580001) B30580001
theorem B54364445 : Blo 2119435 54364445 := bstep (se 3 (by rfl) ⟨10193333, by rfl⟩ : syracuseStep 54364445 = 20386667) B20386667
theorem B36242963 : Blo 2119435 36242963 := bstep (se 1 (by rfl) ⟨27182222, by rfl⟩ : syracuseStep 36242963 = 54364445) B54364445
theorem B24161975 : Blo 2119435 24161975 := bstep (se 1 (by rfl) ⟨18121481, by rfl⟩ : syracuseStep 24161975 = 36242963) B36242963
theorem B16107983 : Blo 2119435 16107983 := bstep (se 1 (by rfl) ⟨12080987, by rfl⟩ : syracuseStep 16107983 = 24161975) B24161975
theorem B10738655 : Blo 2119435 10738655 := bstep (se 1 (by rfl) ⟨8053991, by rfl⟩ : syracuseStep 10738655 = 16107983) B16107983
theorem B7159103 : Blo 2119435 7159103 := bstep (se 1 (by rfl) ⟨5369327, by rfl⟩ : syracuseStep 7159103 = 10738655) B10738655
theorem B4772735 : Blo 2119435 4772735 := bstep (se 1 (by rfl) ⟨3579551, by rfl⟩ : syracuseStep 4772735 = 7159103) B7159103
theorem B3181823 : Blo 2119435 3181823 := bstep (se 1 (by rfl) ⟨2386367, by rfl⟩ : syracuseStep 3181823 = 4772735) B4772735
theorem B2121215 : Blo 2119435 2121215 := bstep (se 1 (by rfl) ⟨1590911, by rfl⟩ : syracuseStep 2121215 = 3181823) B3181823
theorem B3181829 : Blo 2119435 3181829 := bbase (se 4 (by rfl) ⟨298296, by rfl⟩ : syracuseStep 3181829 = 596593) (by norm_num)
theorem B2121219 : Blo 2119435 2121219 := bstep (se 1 (by rfl) ⟨1590914, by rfl⟩ : syracuseStep 2121219 = 3181829) B3181829
theorem B3579565 : Blo 2119435 3579565 := bbase (se 3 (by rfl) ⟨671168, by rfl⟩ : syracuseStep 3579565 = 1342337) (by norm_num)
theorem B4772753 : Blo 2119435 4772753 := bstep (se 2 (by rfl) ⟨1789782, by rfl⟩ : syracuseStep 4772753 = 3579565) B3579565
theorem B3181835 : Blo 2119435 3181835 := bstep (se 1 (by rfl) ⟨2386376, by rfl⟩ : syracuseStep 3181835 = 4772753) B4772753
theorem B2121223 : Blo 2119435 2121223 := bstep (se 1 (by rfl) ⟨1590917, by rfl⟩ : syracuseStep 2121223 = 3181835) B3181835
theorem B2386381 : Blo 2119435 2386381 := bbase (se 3 (by rfl) ⟨447446, by rfl⟩ : syracuseStep 2386381 = 894893) (by norm_num)
theorem B3181841 : Blo 2119435 3181841 := bstep (se 2 (by rfl) ⟨1193190, by rfl⟩ : syracuseStep 3181841 = 2386381) B2386381
theorem B2121227 : Blo 2119435 2121227 := bstep (se 1 (by rfl) ⟨1590920, by rfl⟩ : syracuseStep 2121227 = 3181841) B3181841
theorem B7159157 : Blo 2119435 7159157 := bbase (se 5 (by rfl) ⟨335585, by rfl⟩ : syracuseStep 7159157 = 671171) (by norm_num)
theorem B4772771 : Blo 2119435 4772771 := bstep (se 1 (by rfl) ⟨3579578, by rfl⟩ : syracuseStep 4772771 = 7159157) B7159157
theorem B3181847 : Blo 2119435 3181847 := bstep (se 1 (by rfl) ⟨2386385, by rfl⟩ : syracuseStep 3181847 = 4772771) B4772771
theorem B2121231 : Blo 2119435 2121231 := bstep (se 1 (by rfl) ⟨1590923, by rfl⟩ : syracuseStep 2121231 = 3181847) B3181847
theorem B3181853 : Blo 2119435 3181853 := bbase (se 3 (by rfl) ⟨596597, by rfl⟩ : syracuseStep 3181853 = 1193195) (by norm_num)
theorem B2121235 : Blo 2119435 2121235 := bstep (se 1 (by rfl) ⟨1590926, by rfl⟩ : syracuseStep 2121235 = 3181853) B3181853
theorem B4772789 : Blo 2119435 4772789 := bbase (se 5 (by rfl) ⟨223724, by rfl⟩ : syracuseStep 4772789 = 447449) (by norm_num)
theorem B3181859 : Blo 2119435 3181859 := bstep (se 1 (by rfl) ⟨2386394, by rfl⟩ : syracuseStep 3181859 = 4772789) B4772789
theorem B2121239 : Blo 2119435 2121239 := bstep (se 1 (by rfl) ⟨1590929, by rfl⟩ : syracuseStep 2121239 = 3181859) B3181859
theorem B77406677 : Blo 2119435 77406677 := bbase (se 7 (by rfl) ⟨907109, by rfl⟩ : syracuseStep 77406677 = 1814219) (by norm_num)
theorem B51604451 : Blo 2119435 51604451 := bstep (se 1 (by rfl) ⟨38703338, by rfl⟩ : syracuseStep 51604451 = 77406677) B77406677
theorem B34402967 : Blo 2119435 34402967 := bstep (se 1 (by rfl) ⟨25802225, by rfl⟩ : syracuseStep 34402967 = 51604451) B51604451
theorem B22935311 : Blo 2119435 22935311 := bstep (se 1 (by rfl) ⟨17201483, by rfl⟩ : syracuseStep 22935311 = 34402967) B34402967
theorem B15290207 : Blo 2119435 15290207 := bstep (se 1 (by rfl) ⟨11467655, by rfl⟩ : syracuseStep 15290207 = 22935311) B22935311
theorem B10193471 : Blo 2119435 10193471 := bstep (se 1 (by rfl) ⟨7645103, by rfl⟩ : syracuseStep 10193471 = 15290207) B15290207
theorem B6795647 : Blo 2119435 6795647 := bstep (se 1 (by rfl) ⟨5096735, by rfl⟩ : syracuseStep 6795647 = 10193471) B10193471
theorem B4530431 : Blo 2119435 4530431 := bstep (se 1 (by rfl) ⟨3397823, by rfl⟩ : syracuseStep 4530431 = 6795647) B6795647
theorem B12081149 : Blo 2119435 12081149 := bstep (se 3 (by rfl) ⟨2265215, by rfl⟩ : syracuseStep 12081149 = 4530431) B4530431
theorem B8054099 : Blo 2119435 8054099 := bstep (se 1 (by rfl) ⟨6040574, by rfl⟩ : syracuseStep 8054099 = 12081149) B12081149
theorem B5369399 : Blo 2119435 5369399 := bstep (se 1 (by rfl) ⟨4027049, by rfl⟩ : syracuseStep 5369399 = 8054099) B8054099
theorem B3579599 : Blo 2119435 3579599 := bstep (se 1 (by rfl) ⟨2684699, by rfl⟩ : syracuseStep 3579599 = 5369399) B5369399
theorem B2386399 : Blo 2119435 2386399 := bstep (se 1 (by rfl) ⟨1789799, by rfl⟩ : syracuseStep 2386399 = 3579599) B3579599
theorem B3181865 : Blo 2119435 3181865 := bstep (se 2 (by rfl) ⟨1193199, by rfl⟩ : syracuseStep 3181865 = 2386399) B2386399
theorem B2121243 : Blo 2119435 2121243 := bstep (se 1 (by rfl) ⟨1590932, by rfl⟩ : syracuseStep 2121243 = 3181865) B3181865
theorem B12246005 : Blo 2119435 12246005 := bbase (se 5 (by rfl) ⟨574031, by rfl⟩ : syracuseStep 12246005 = 1148063) (by norm_num)
theorem B8164003 : Blo 2119435 8164003 := bstep (se 1 (by rfl) ⟨6123002, by rfl⟩ : syracuseStep 8164003 = 12246005) B12246005
theorem B10885337 : Blo 2119435 10885337 := bstep (se 2 (by rfl) ⟨4082001, by rfl⟩ : syracuseStep 10885337 = 8164003) B8164003
theorem B7256891 : Blo 2119435 7256891 := bstep (se 1 (by rfl) ⟨5442668, by rfl⟩ : syracuseStep 7256891 = 10885337) B10885337
theorem B4837927 : Blo 2119435 4837927 := bstep (se 1 (by rfl) ⟨3628445, by rfl⟩ : syracuseStep 4837927 = 7256891) B7256891
theorem B6450569 : Blo 2119435 6450569 := bstep (se 2 (by rfl) ⟨2418963, by rfl⟩ : syracuseStep 6450569 = 4837927) B4837927
theorem B4300379 : Blo 2119435 4300379 := bstep (se 1 (by rfl) ⟨3225284, by rfl⟩ : syracuseStep 4300379 = 6450569) B6450569
theorem B2866919 : Blo 2119435 2866919 := bstep (se 1 (by rfl) ⟨2150189, by rfl⟩ : syracuseStep 2866919 = 4300379) B4300379
theorem B7645117 : Blo 2119435 7645117 := bstep (se 3 (by rfl) ⟨1433459, by rfl⟩ : syracuseStep 7645117 = 2866919) B2866919
theorem B10193489 : Blo 2119435 10193489 := bstep (se 2 (by rfl) ⟨3822558, by rfl⟩ : syracuseStep 10193489 = 7645117) B7645117
theorem B6795659 : Blo 2119435 6795659 := bstep (se 1 (by rfl) ⟨5096744, by rfl⟩ : syracuseStep 6795659 = 10193489) B10193489
theorem B4530439 : Blo 2119435 4530439 := bstep (se 1 (by rfl) ⟨3397829, by rfl⟩ : syracuseStep 4530439 = 6795659) B6795659
theorem B6040585 : Blo 2119435 6040585 := bstep (se 2 (by rfl) ⟨2265219, by rfl⟩ : syracuseStep 6040585 = 4530439) B4530439
theorem B8054113 : Blo 2119435 8054113 := bstep (se 2 (by rfl) ⟨3020292, by rfl⟩ : syracuseStep 8054113 = 6040585) B6040585
theorem B10738817 : Blo 2119435 10738817 := bstep (se 2 (by rfl) ⟨4027056, by rfl⟩ : syracuseStep 10738817 = 8054113) B8054113
theorem B7159211 : Blo 2119435 7159211 := bstep (se 1 (by rfl) ⟨5369408, by rfl⟩ : syracuseStep 7159211 = 10738817) B10738817
theorem B4772807 : Blo 2119435 4772807 := bstep (se 1 (by rfl) ⟨3579605, by rfl⟩ : syracuseStep 4772807 = 7159211) B7159211
theorem B3181871 : Blo 2119435 3181871 := bstep (se 1 (by rfl) ⟨2386403, by rfl⟩ : syracuseStep 3181871 = 4772807) B4772807
theorem B2121247 : Blo 2119435 2121247 := bstep (se 1 (by rfl) ⟨1590935, by rfl⟩ : syracuseStep 2121247 = 3181871) B3181871
theorem B3181877 : Blo 2119435 3181877 := bbase (se 5 (by rfl) ⟨149150, by rfl⟩ : syracuseStep 3181877 = 298301) (by norm_num)
theorem B2121251 : Blo 2119435 2121251 := bstep (se 1 (by rfl) ⟨1590938, by rfl⟩ : syracuseStep 2121251 = 3181877) B3181877
theorem B5369429 : Blo 2119435 5369429 := bbase (se 8 (by rfl) ⟨31461, by rfl⟩ : syracuseStep 5369429 = 62923) (by norm_num)
theorem B3579619 : Blo 2119435 3579619 := bstep (se 1 (by rfl) ⟨2684714, by rfl⟩ : syracuseStep 3579619 = 5369429) B5369429
theorem B4772825 : Blo 2119435 4772825 := bstep (se 2 (by rfl) ⟨1789809, by rfl⟩ : syracuseStep 4772825 = 3579619) B3579619
theorem B3181883 : Blo 2119435 3181883 := bstep (se 1 (by rfl) ⟨2386412, by rfl⟩ : syracuseStep 3181883 = 4772825) B4772825
theorem B2121255 : Blo 2119435 2121255 := bstep (se 1 (by rfl) ⟨1590941, by rfl⟩ : syracuseStep 2121255 = 3181883) B3181883
theorem B2386417 : Blo 2119435 2386417 := bbase (se 2 (by rfl) ⟨894906, by rfl⟩ : syracuseStep 2386417 = 1789813) (by norm_num)
theorem B3181889 : Blo 2119435 3181889 := bstep (se 2 (by rfl) ⟨1193208, by rfl⟩ : syracuseStep 3181889 = 2386417) B2386417
theorem B2121259 : Blo 2119435 2121259 := bstep (se 1 (by rfl) ⟨1590944, by rfl⟩ : syracuseStep 2121259 = 3181889) B3181889
theorem B5442709 : Blo 2119435 5442709 := bbase (se 6 (by rfl) ⟨127563, by rfl⟩ : syracuseStep 5442709 = 255127) (by norm_num)
theorem B7256945 : Blo 2119435 7256945 := bstep (se 2 (by rfl) ⟨2721354, by rfl⟩ : syracuseStep 7256945 = 5442709) B5442709
theorem B4837963 : Blo 2119435 4837963 := bstep (se 1 (by rfl) ⟨3628472, by rfl⟩ : syracuseStep 4837963 = 7256945) B7256945
theorem B6450617 : Blo 2119435 6450617 := bstep (se 2 (by rfl) ⟨2418981, by rfl⟩ : syracuseStep 6450617 = 4837963) B4837963
theorem B17201645 : Blo 2119435 17201645 := bstep (se 3 (by rfl) ⟨3225308, by rfl⟩ : syracuseStep 17201645 = 6450617) B6450617
theorem B11467763 : Blo 2119435 11467763 := bstep (se 1 (by rfl) ⟨8600822, by rfl⟩ : syracuseStep 11467763 = 17201645) B17201645
theorem B7645175 : Blo 2119435 7645175 := bstep (se 1 (by rfl) ⟨5733881, by rfl⟩ : syracuseStep 7645175 = 11467763) B11467763
theorem B5096783 : Blo 2119435 5096783 := bstep (se 1 (by rfl) ⟨3822587, by rfl⟩ : syracuseStep 5096783 = 7645175) B7645175
theorem B13591421 : Blo 2119435 13591421 := bstep (se 3 (by rfl) ⟨2548391, by rfl⟩ : syracuseStep 13591421 = 5096783) B5096783
theorem B9060947 : Blo 2119435 9060947 := bstep (se 1 (by rfl) ⟨6795710, by rfl⟩ : syracuseStep 9060947 = 13591421) B13591421
theorem B6040631 : Blo 2119435 6040631 := bstep (se 1 (by rfl) ⟨4530473, by rfl⟩ : syracuseStep 6040631 = 9060947) B9060947
theorem B4027087 : Blo 2119435 4027087 := bstep (se 1 (by rfl) ⟨3020315, by rfl⟩ : syracuseStep 4027087 = 6040631) B6040631
theorem B5369449 : Blo 2119435 5369449 := bstep (se 2 (by rfl) ⟨2013543, by rfl⟩ : syracuseStep 5369449 = 4027087) B4027087
theorem B7159265 : Blo 2119435 7159265 := bstep (se 2 (by rfl) ⟨2684724, by rfl⟩ : syracuseStep 7159265 = 5369449) B5369449
theorem B4772843 : Blo 2119435 4772843 := bstep (se 1 (by rfl) ⟨3579632, by rfl⟩ : syracuseStep 4772843 = 7159265) B7159265
theorem B3181895 : Blo 2119435 3181895 := bstep (se 1 (by rfl) ⟨2386421, by rfl⟩ : syracuseStep 3181895 = 4772843) B4772843
theorem B2121263 : Blo 2119435 2121263 := bstep (se 1 (by rfl) ⟨1590947, by rfl⟩ : syracuseStep 2121263 = 3181895) B3181895
theorem B3181901 : Blo 2119435 3181901 := bbase (se 3 (by rfl) ⟨596606, by rfl⟩ : syracuseStep 3181901 = 1193213) (by norm_num)
theorem B2121267 : Blo 2119435 2121267 := bstep (se 1 (by rfl) ⟨1590950, by rfl⟩ : syracuseStep 2121267 = 3181901) B3181901
theorem B4772861 : Blo 2119435 4772861 := bbase (se 3 (by rfl) ⟨894911, by rfl⟩ : syracuseStep 4772861 = 1789823) (by norm_num)
theorem B3181907 : Blo 2119435 3181907 := bstep (se 1 (by rfl) ⟨2386430, by rfl⟩ : syracuseStep 3181907 = 4772861) B4772861
theorem B2121271 : Blo 2119435 2121271 := bstep (se 1 (by rfl) ⟨1590953, by rfl⟩ : syracuseStep 2121271 = 3181907) B3181907
theorem B3579653 : Blo 2119435 3579653 := bbase (se 4 (by rfl) ⟨335592, by rfl⟩ : syracuseStep 3579653 = 671185) (by norm_num)
theorem B2386435 : Blo 2119435 2386435 := bstep (se 1 (by rfl) ⟨1789826, by rfl⟩ : syracuseStep 2386435 = 3579653) B3579653
theorem B3181913 : Blo 2119435 3181913 := bstep (se 2 (by rfl) ⟨1193217, by rfl⟩ : syracuseStep 3181913 = 2386435) B2386435
theorem B2121275 : Blo 2119435 2121275 := bstep (se 1 (by rfl) ⟨1590956, by rfl⟩ : syracuseStep 2121275 = 3181913) B3181913
theorem B16108469 : Blo 2119435 16108469 := bbase (se 5 (by rfl) ⟨755084, by rfl⟩ : syracuseStep 16108469 = 1510169) (by norm_num)
theorem B10738979 : Blo 2119435 10738979 := bstep (se 1 (by rfl) ⟨8054234, by rfl⟩ : syracuseStep 10738979 = 16108469) B16108469
theorem B7159319 : Blo 2119435 7159319 := bstep (se 1 (by rfl) ⟨5369489, by rfl⟩ : syracuseStep 7159319 = 10738979) B10738979
theorem B4772879 : Blo 2119435 4772879 := bstep (se 1 (by rfl) ⟨3579659, by rfl⟩ : syracuseStep 4772879 = 7159319) B7159319
theorem B3181919 : Blo 2119435 3181919 := bstep (se 1 (by rfl) ⟨2386439, by rfl⟩ : syracuseStep 3181919 = 4772879) B4772879
theorem B2121279 : Blo 2119435 2121279 := bstep (se 1 (by rfl) ⟨1590959, by rfl⟩ : syracuseStep 2121279 = 3181919) B3181919
theorem B3181925 : Blo 2119435 3181925 := bbase (se 4 (by rfl) ⟨298305, by rfl⟩ : syracuseStep 3181925 = 596611) (by norm_num)
theorem B2121283 : Blo 2119435 2121283 := bstep (se 1 (by rfl) ⟨1590962, by rfl⟩ : syracuseStep 2121283 = 3181925) B3181925
theorem B4027133 : Blo 2119435 4027133 := bbase (se 3 (by rfl) ⟨755087, by rfl⟩ : syracuseStep 4027133 = 1510175) (by norm_num)
theorem B2684755 : Blo 2119435 2684755 := bstep (se 1 (by rfl) ⟨2013566, by rfl⟩ : syracuseStep 2684755 = 4027133) B4027133
theorem B3579673 : Blo 2119435 3579673 := bstep (se 2 (by rfl) ⟨1342377, by rfl⟩ : syracuseStep 3579673 = 2684755) B2684755
theorem B4772897 : Blo 2119435 4772897 := bstep (se 2 (by rfl) ⟨1789836, by rfl⟩ : syracuseStep 4772897 = 3579673) B3579673
theorem B3181931 : Blo 2119435 3181931 := bstep (se 1 (by rfl) ⟨2386448, by rfl⟩ : syracuseStep 3181931 = 4772897) B4772897
theorem B2121287 : Blo 2119435 2121287 := bstep (se 1 (by rfl) ⟨1590965, by rfl⟩ : syracuseStep 2121287 = 3181931) B3181931
theorem B2386453 : Blo 2119435 2386453 := bbase (se 6 (by rfl) ⟨55932, by rfl⟩ : syracuseStep 2386453 = 111865) (by norm_num)
theorem B3181937 : Blo 2119435 3181937 := bstep (se 2 (by rfl) ⟨1193226, by rfl⟩ : syracuseStep 3181937 = 2386453) B2386453
theorem B2121291 : Blo 2119435 2121291 := bstep (se 1 (by rfl) ⟨1590968, by rfl⟩ : syracuseStep 2121291 = 3181937) B3181937
theorem B2684765 : Blo 2119435 2684765 := bbase (se 3 (by rfl) ⟨503393, by rfl⟩ : syracuseStep 2684765 = 1006787) (by norm_num)
theorem B7159373 : Blo 2119435 7159373 := bstep (se 3 (by rfl) ⟨1342382, by rfl⟩ : syracuseStep 7159373 = 2684765) B2684765
theorem B4772915 : Blo 2119435 4772915 := bstep (se 1 (by rfl) ⟨3579686, by rfl⟩ : syracuseStep 4772915 = 7159373) B7159373
theorem B3181943 : Blo 2119435 3181943 := bstep (se 1 (by rfl) ⟨2386457, by rfl⟩ : syracuseStep 3181943 = 4772915) B4772915
theorem B2121295 : Blo 2119435 2121295 := bstep (se 1 (by rfl) ⟨1590971, by rfl⟩ : syracuseStep 2121295 = 3181943) B3181943
theorem B3181949 : Blo 2119435 3181949 := bbase (se 3 (by rfl) ⟨596615, by rfl⟩ : syracuseStep 3181949 = 1193231) (by norm_num)
theorem B2121299 : Blo 2119435 2121299 := bstep (se 1 (by rfl) ⟨1590974, by rfl⟩ : syracuseStep 2121299 = 3181949) B3181949
theorem B4772933 : Blo 2119435 4772933 := bbase (se 4 (by rfl) ⟨447462, by rfl⟩ : syracuseStep 4772933 = 894925) (by norm_num)
theorem B3181955 : Blo 2119435 3181955 := bstep (se 1 (by rfl) ⟨2386466, by rfl⟩ : syracuseStep 3181955 = 4772933) B4772933
theorem B2121303 : Blo 2119435 2121303 := bstep (se 1 (by rfl) ⟨1590977, by rfl⟩ : syracuseStep 2121303 = 3181955) B3181955
theorem B6040757 : Blo 2119435 6040757 := bbase (se 5 (by rfl) ⟨283160, by rfl⟩ : syracuseStep 6040757 = 566321) (by norm_num)
theorem B4027171 : Blo 2119435 4027171 := bstep (se 1 (by rfl) ⟨3020378, by rfl⟩ : syracuseStep 4027171 = 6040757) B6040757
theorem B5369561 : Blo 2119435 5369561 := bstep (se 2 (by rfl) ⟨2013585, by rfl⟩ : syracuseStep 5369561 = 4027171) B4027171
theorem B3579707 : Blo 2119435 3579707 := bstep (se 1 (by rfl) ⟨2684780, by rfl⟩ : syracuseStep 3579707 = 5369561) B5369561
theorem B2386471 : Blo 2119435 2386471 := bstep (se 1 (by rfl) ⟨1789853, by rfl⟩ : syracuseStep 2386471 = 3579707) B3579707
theorem B3181961 : Blo 2119435 3181961 := bstep (se 2 (by rfl) ⟨1193235, by rfl⟩ : syracuseStep 3181961 = 2386471) B2386471
theorem B2121307 : Blo 2119435 2121307 := bstep (se 1 (by rfl) ⟨1590980, by rfl⟩ : syracuseStep 2121307 = 3181961) B3181961
theorem B10739141 : Blo 2119435 10739141 := bbase (se 4 (by rfl) ⟨1006794, by rfl⟩ : syracuseStep 10739141 = 2013589) (by norm_num)
theorem B7159427 : Blo 2119435 7159427 := bstep (se 1 (by rfl) ⟨5369570, by rfl⟩ : syracuseStep 7159427 = 10739141) B10739141
theorem B4772951 : Blo 2119435 4772951 := bstep (se 1 (by rfl) ⟨3579713, by rfl⟩ : syracuseStep 4772951 = 7159427) B7159427
theorem B3181967 : Blo 2119435 3181967 := bstep (se 1 (by rfl) ⟨2386475, by rfl⟩ : syracuseStep 3181967 = 4772951) B4772951
theorem B2121311 : Blo 2119435 2121311 := bstep (se 1 (by rfl) ⟨1590983, by rfl⟩ : syracuseStep 2121311 = 3181967) B3181967
theorem B3181973 : Blo 2119435 3181973 := bbase (se 6 (by rfl) ⟨74577, by rfl⟩ : syracuseStep 3181973 = 149155) (by norm_num)
theorem B2121315 : Blo 2119435 2121315 := bstep (se 1 (by rfl) ⟨1590986, by rfl⟩ : syracuseStep 2121315 = 3181973) B3181973
theorem B4838093 : Blo 2119435 4838093 := bbase (se 3 (by rfl) ⟨907142, by rfl⟩ : syracuseStep 4838093 = 1814285) (by norm_num)
theorem B3225395 : Blo 2119435 3225395 := bstep (se 1 (by rfl) ⟨2419046, by rfl⟩ : syracuseStep 3225395 = 4838093) B4838093
theorem B2150263 : Blo 2119435 2150263 := bstep (se 1 (by rfl) ⟨1612697, by rfl⟩ : syracuseStep 2150263 = 3225395) B3225395
theorem B2867017 : Blo 2119435 2867017 := bstep (se 2 (by rfl) ⟨1075131, by rfl⟩ : syracuseStep 2867017 = 2150263) B2150263
theorem B3822689 : Blo 2119435 3822689 := bstep (se 2 (by rfl) ⟨1433508, by rfl⟩ : syracuseStep 3822689 = 2867017) B2867017
theorem B2548459 : Blo 2119435 2548459 := bstep (se 1 (by rfl) ⟨1911344, by rfl⟩ : syracuseStep 2548459 = 3822689) B3822689
theorem B3397945 : Blo 2119435 3397945 := bstep (se 2 (by rfl) ⟨1274229, by rfl⟩ : syracuseStep 3397945 = 2548459) B2548459
theorem B4530593 : Blo 2119435 4530593 := bstep (se 2 (by rfl) ⟨1698972, by rfl⟩ : syracuseStep 4530593 = 3397945) B3397945
theorem B12081581 : Blo 2119435 12081581 := bstep (se 3 (by rfl) ⟨2265296, by rfl⟩ : syracuseStep 12081581 = 4530593) B4530593
theorem B8054387 : Blo 2119435 8054387 := bstep (se 1 (by rfl) ⟨6040790, by rfl⟩ : syracuseStep 8054387 = 12081581) B12081581
theorem B5369591 : Blo 2119435 5369591 := bstep (se 1 (by rfl) ⟨4027193, by rfl⟩ : syracuseStep 5369591 = 8054387) B8054387
theorem B3579727 : Blo 2119435 3579727 := bstep (se 1 (by rfl) ⟨2684795, by rfl⟩ : syracuseStep 3579727 = 5369591) B5369591
theorem B4772969 : Blo 2119435 4772969 := bstep (se 2 (by rfl) ⟨1789863, by rfl⟩ : syracuseStep 4772969 = 3579727) B3579727
theorem B3181979 : Blo 2119435 3181979 := bstep (se 1 (by rfl) ⟨2386484, by rfl⟩ : syracuseStep 3181979 = 4772969) B4772969
theorem B2121319 : Blo 2119435 2121319 := bstep (se 1 (by rfl) ⟨1590989, by rfl⟩ : syracuseStep 2121319 = 3181979) B3181979
theorem B2386489 : Blo 2119435 2386489 := bbase (se 2 (by rfl) ⟨894933, by rfl⟩ : syracuseStep 2386489 = 1789867) (by norm_num)
theorem B3181985 : Blo 2119435 3181985 := bstep (se 2 (by rfl) ⟨1193244, by rfl⟩ : syracuseStep 3181985 = 2386489) B2386489
theorem B2121323 : Blo 2119435 2121323 := bstep (se 1 (by rfl) ⟨1590992, by rfl⟩ : syracuseStep 2121323 = 3181985) B3181985
theorem B2265305 : Blo 2119435 2265305 := bbase (se 2 (by rfl) ⟨849489, by rfl⟩ : syracuseStep 2265305 = 1698979) (by norm_num)
theorem B6040813 : Blo 2119435 6040813 := bstep (se 3 (by rfl) ⟨1132652, by rfl⟩ : syracuseStep 6040813 = 2265305) B2265305
theorem B8054417 : Blo 2119435 8054417 := bstep (se 2 (by rfl) ⟨3020406, by rfl⟩ : syracuseStep 8054417 = 6040813) B6040813
theorem B5369611 : Blo 2119435 5369611 := bstep (se 1 (by rfl) ⟨4027208, by rfl⟩ : syracuseStep 5369611 = 8054417) B8054417
theorem B7159481 : Blo 2119435 7159481 := bstep (se 2 (by rfl) ⟨2684805, by rfl⟩ : syracuseStep 7159481 = 5369611) B5369611
theorem B4772987 : Blo 2119435 4772987 := bstep (se 1 (by rfl) ⟨3579740, by rfl⟩ : syracuseStep 4772987 = 7159481) B7159481
theorem B3181991 : Blo 2119435 3181991 := bstep (se 1 (by rfl) ⟨2386493, by rfl⟩ : syracuseStep 3181991 = 4772987) B4772987
theorem B2121327 : Blo 2119435 2121327 := bstep (se 1 (by rfl) ⟨1590995, by rfl⟩ : syracuseStep 2121327 = 3181991) B3181991
theorem B3181997 : Blo 2119435 3181997 := bbase (se 3 (by rfl) ⟨596624, by rfl⟩ : syracuseStep 3181997 = 1193249) (by norm_num)
theorem B2121331 : Blo 2119435 2121331 := bstep (se 1 (by rfl) ⟨1590998, by rfl⟩ : syracuseStep 2121331 = 3181997) B3181997
theorem B4773005 : Blo 2119435 4773005 := bbase (se 3 (by rfl) ⟨894938, by rfl⟩ : syracuseStep 4773005 = 1789877) (by norm_num)
theorem B3182003 : Blo 2119435 3182003 := bstep (se 1 (by rfl) ⟨2386502, by rfl⟩ : syracuseStep 3182003 = 4773005) B4773005
theorem B2121335 : Blo 2119435 2121335 := bstep (se 1 (by rfl) ⟨1591001, by rfl⟩ : syracuseStep 2121335 = 3182003) B3182003
theorem B2684821 : Blo 2119435 2684821 := bbase (se 6 (by rfl) ⟨62925, by rfl⟩ : syracuseStep 2684821 = 125851) (by norm_num)
theorem B3579761 : Blo 2119435 3579761 := bstep (se 2 (by rfl) ⟨1342410, by rfl⟩ : syracuseStep 3579761 = 2684821) B2684821
theorem B2386507 : Blo 2119435 2386507 := bstep (se 1 (by rfl) ⟨1789880, by rfl⟩ : syracuseStep 2386507 = 3579761) B3579761
theorem B3182009 : Blo 2119435 3182009 := bstep (se 2 (by rfl) ⟨1193253, by rfl⟩ : syracuseStep 3182009 = 2386507) B2386507
theorem B2121339 : Blo 2119435 2121339 := bstep (se 1 (by rfl) ⟨1591004, by rfl⟩ : syracuseStep 2121339 = 3182009) B3182009
theorem B12901717 : Blo 2119435 12901717 := bbase (se 11 (by rfl) ⟨9449, by rfl⟩ : syracuseStep 12901717 = 18899) (by norm_num)
theorem B17202289 : Blo 2119435 17202289 := bstep (se 2 (by rfl) ⟨6450858, by rfl⟩ : syracuseStep 17202289 = 12901717) B12901717
theorem B22936385 : Blo 2119435 22936385 := bstep (se 2 (by rfl) ⟨8601144, by rfl⟩ : syracuseStep 22936385 = 17202289) B17202289
theorem B61163693 : Blo 2119435 61163693 := bstep (se 3 (by rfl) ⟨11468192, by rfl⟩ : syracuseStep 61163693 = 22936385) B22936385
theorem B40775795 : Blo 2119435 40775795 := bstep (se 1 (by rfl) ⟨30581846, by rfl⟩ : syracuseStep 40775795 = 61163693) B61163693
theorem B27183863 : Blo 2119435 27183863 := bstep (se 1 (by rfl) ⟨20387897, by rfl⟩ : syracuseStep 27183863 = 40775795) B40775795
theorem B18122575 : Blo 2119435 18122575 := bstep (se 1 (by rfl) ⟨13591931, by rfl⟩ : syracuseStep 18122575 = 27183863) B27183863
theorem B24163433 : Blo 2119435 24163433 := bstep (se 2 (by rfl) ⟨9061287, by rfl⟩ : syracuseStep 24163433 = 18122575) B18122575
theorem B16108955 : Blo 2119435 16108955 := bstep (se 1 (by rfl) ⟨12081716, by rfl⟩ : syracuseStep 16108955 = 24163433) B24163433
theorem B10739303 : Blo 2119435 10739303 := bstep (se 1 (by rfl) ⟨8054477, by rfl⟩ : syracuseStep 10739303 = 16108955) B16108955
theorem B7159535 : Blo 2119435 7159535 := bstep (se 1 (by rfl) ⟨5369651, by rfl⟩ : syracuseStep 7159535 = 10739303) B10739303
theorem B4773023 : Blo 2119435 4773023 := bstep (se 1 (by rfl) ⟨3579767, by rfl⟩ : syracuseStep 4773023 = 7159535) B7159535
theorem B3182015 : Blo 2119435 3182015 := bstep (se 1 (by rfl) ⟨2386511, by rfl⟩ : syracuseStep 3182015 = 4773023) B4773023
theorem B2121343 : Blo 2119435 2121343 := bstep (se 1 (by rfl) ⟨1591007, by rfl⟩ : syracuseStep 2121343 = 3182015) B3182015
theorem B3182021 : Blo 2119435 3182021 := bbase (se 4 (by rfl) ⟨298314, by rfl⟩ : syracuseStep 3182021 = 596629) (by norm_num)
theorem B2121347 : Blo 2119435 2121347 := bstep (se 1 (by rfl) ⟨1591010, by rfl⟩ : syracuseStep 2121347 = 3182021) B3182021
theorem B3579781 : Blo 2119435 3579781 := bbase (se 4 (by rfl) ⟨335604, by rfl⟩ : syracuseStep 3579781 = 671209) (by norm_num)
theorem B4773041 : Blo 2119435 4773041 := bstep (se 2 (by rfl) ⟨1789890, by rfl⟩ : syracuseStep 4773041 = 3579781) B3579781
theorem B3182027 : Blo 2119435 3182027 := bstep (se 1 (by rfl) ⟨2386520, by rfl⟩ : syracuseStep 3182027 = 4773041) B4773041
theorem B2121351 : Blo 2119435 2121351 := bstep (se 1 (by rfl) ⟨1591013, by rfl⟩ : syracuseStep 2121351 = 3182027) B3182027
theorem B2386525 : Blo 2119435 2386525 := bbase (se 3 (by rfl) ⟨447473, by rfl⟩ : syracuseStep 2386525 = 894947) (by norm_num)
theorem B3182033 : Blo 2119435 3182033 := bstep (se 2 (by rfl) ⟨1193262, by rfl⟩ : syracuseStep 3182033 = 2386525) B2386525
theorem B2121355 : Blo 2119435 2121355 := bstep (se 1 (by rfl) ⟨1591016, by rfl⟩ : syracuseStep 2121355 = 3182033) B3182033
theorem B7159589 : Blo 2119435 7159589 := bbase (se 4 (by rfl) ⟨671211, by rfl⟩ : syracuseStep 7159589 = 1342423) (by norm_num)
theorem B4773059 : Blo 2119435 4773059 := bstep (se 1 (by rfl) ⟨3579794, by rfl⟩ : syracuseStep 4773059 = 7159589) B7159589
theorem B3182039 : Blo 2119435 3182039 := bstep (se 1 (by rfl) ⟨2386529, by rfl⟩ : syracuseStep 3182039 = 4773059) B4773059
theorem B2121359 : Blo 2119435 2121359 := bstep (se 1 (by rfl) ⟨1591019, by rfl⟩ : syracuseStep 2121359 = 3182039) B3182039
theorem B3182045 : Blo 2119435 3182045 := bbase (se 3 (by rfl) ⟨596633, by rfl⟩ : syracuseStep 3182045 = 1193267) (by norm_num)
theorem B2121363 : Blo 2119435 2121363 := bstep (se 1 (by rfl) ⟨1591022, by rfl⟩ : syracuseStep 2121363 = 3182045) B3182045
theorem B4773077 : Blo 2119435 4773077 := bbase (se 7 (by rfl) ⟨55934, by rfl⟩ : syracuseStep 4773077 = 111869) (by norm_num)
theorem B3182051 : Blo 2119435 3182051 := bstep (se 1 (by rfl) ⟨2386538, by rfl⟩ : syracuseStep 3182051 = 4773077) B4773077
theorem B2121367 : Blo 2119435 2121367 := bstep (se 1 (by rfl) ⟨1591025, by rfl⟩ : syracuseStep 2121367 = 3182051) B3182051
theorem B9676421 : Blo 2119435 9676421 := bbase (se 4 (by rfl) ⟨907164, by rfl⟩ : syracuseStep 9676421 = 1814329) (by norm_num)
theorem B6450947 : Blo 2119435 6450947 := bstep (se 1 (by rfl) ⟨4838210, by rfl⟩ : syracuseStep 6450947 = 9676421) B9676421
theorem B4300631 : Blo 2119435 4300631 := bstep (se 1 (by rfl) ⟨3225473, by rfl⟩ : syracuseStep 4300631 = 6450947) B6450947
theorem B2867087 : Blo 2119435 2867087 := bstep (se 1 (by rfl) ⟨2150315, by rfl⟩ : syracuseStep 2867087 = 4300631) B4300631
theorem B7645565 : Blo 2119435 7645565 := bstep (se 3 (by rfl) ⟨1433543, by rfl⟩ : syracuseStep 7645565 = 2867087) B2867087
theorem B5097043 : Blo 2119435 5097043 := bstep (se 1 (by rfl) ⟨3822782, by rfl⟩ : syracuseStep 5097043 = 7645565) B7645565
theorem B6796057 : Blo 2119435 6796057 := bstep (se 2 (by rfl) ⟨2548521, by rfl⟩ : syracuseStep 6796057 = 5097043) B5097043
theorem B9061409 : Blo 2119435 9061409 := bstep (se 2 (by rfl) ⟨3398028, by rfl⟩ : syracuseStep 9061409 = 6796057) B6796057
theorem B6040939 : Blo 2119435 6040939 := bstep (se 1 (by rfl) ⟨4530704, by rfl⟩ : syracuseStep 6040939 = 9061409) B9061409
theorem B8054585 : Blo 2119435 8054585 := bstep (se 2 (by rfl) ⟨3020469, by rfl⟩ : syracuseStep 8054585 = 6040939) B6040939
theorem B5369723 : Blo 2119435 5369723 := bstep (se 1 (by rfl) ⟨4027292, by rfl⟩ : syracuseStep 5369723 = 8054585) B8054585
theorem B3579815 : Blo 2119435 3579815 := bstep (se 1 (by rfl) ⟨2684861, by rfl⟩ : syracuseStep 3579815 = 5369723) B5369723
theorem B2386543 : Blo 2119435 2386543 := bstep (se 1 (by rfl) ⟨1789907, by rfl⟩ : syracuseStep 2386543 = 3579815) B3579815
theorem B3182057 : Blo 2119435 3182057 := bstep (se 2 (by rfl) ⟨1193271, by rfl⟩ : syracuseStep 3182057 = 2386543) B2386543
theorem B2121371 : Blo 2119435 2121371 := bstep (se 1 (by rfl) ⟨1591028, by rfl⟩ : syracuseStep 2121371 = 3182057) B3182057
theorem B3061685 : Blo 2119435 3061685 := bbase (se 5 (by rfl) ⟨143516, by rfl⟩ : syracuseStep 3061685 = 287033) (by norm_num)
theorem B8164493 : Blo 2119435 8164493 := bstep (se 3 (by rfl) ⟨1530842, by rfl⟩ : syracuseStep 8164493 = 3061685) B3061685
theorem B5442995 : Blo 2119435 5442995 := bstep (se 1 (by rfl) ⟨4082246, by rfl⟩ : syracuseStep 5442995 = 8164493) B8164493
theorem B14514653 : Blo 2119435 14514653 := bstep (se 3 (by rfl) ⟨2721497, by rfl⟩ : syracuseStep 14514653 = 5442995) B5442995
theorem B9676435 : Blo 2119435 9676435 := bstep (se 1 (by rfl) ⟨7257326, by rfl⟩ : syracuseStep 9676435 = 14514653) B14514653
theorem B12901913 : Blo 2119435 12901913 := bstep (se 2 (by rfl) ⟨4838217, by rfl⟩ : syracuseStep 12901913 = 9676435) B9676435
theorem B8601275 : Blo 2119435 8601275 := bstep (se 1 (by rfl) ⟨6450956, by rfl⟩ : syracuseStep 8601275 = 12901913) B12901913
theorem B22936733 : Blo 2119435 22936733 := bstep (se 3 (by rfl) ⟨4300637, by rfl⟩ : syracuseStep 22936733 = 8601275) B8601275
theorem B15291155 : Blo 2119435 15291155 := bstep (se 1 (by rfl) ⟨11468366, by rfl⟩ : syracuseStep 15291155 = 22936733) B22936733
theorem B10194103 : Blo 2119435 10194103 := bstep (se 1 (by rfl) ⟨7645577, by rfl⟩ : syracuseStep 10194103 = 15291155) B15291155
theorem B13592137 : Blo 2119435 13592137 := bstep (se 2 (by rfl) ⟨5097051, by rfl⟩ : syracuseStep 13592137 = 10194103) B10194103
theorem B18122849 : Blo 2119435 18122849 := bstep (se 2 (by rfl) ⟨6796068, by rfl⟩ : syracuseStep 18122849 = 13592137) B13592137
theorem B12081899 : Blo 2119435 12081899 := bstep (se 1 (by rfl) ⟨9061424, by rfl⟩ : syracuseStep 12081899 = 18122849) B18122849
theorem B8054599 : Blo 2119435 8054599 := bstep (se 1 (by rfl) ⟨6040949, by rfl⟩ : syracuseStep 8054599 = 12081899) B12081899
theorem B10739465 : Blo 2119435 10739465 := bstep (se 2 (by rfl) ⟨4027299, by rfl⟩ : syracuseStep 10739465 = 8054599) B8054599
theorem B7159643 : Blo 2119435 7159643 := bstep (se 1 (by rfl) ⟨5369732, by rfl⟩ : syracuseStep 7159643 = 10739465) B10739465
theorem B4773095 : Blo 2119435 4773095 := bstep (se 1 (by rfl) ⟨3579821, by rfl⟩ : syracuseStep 4773095 = 7159643) B7159643
theorem B3182063 : Blo 2119435 3182063 := bstep (se 1 (by rfl) ⟨2386547, by rfl⟩ : syracuseStep 3182063 = 4773095) B4773095
theorem B2121375 : Blo 2119435 2121375 := bstep (se 1 (by rfl) ⟨1591031, by rfl⟩ : syracuseStep 2121375 = 3182063) B3182063
theorem B3182069 : Blo 2119435 3182069 := bbase (se 5 (by rfl) ⟨149159, by rfl⟩ : syracuseStep 3182069 = 298319) (by norm_num)
theorem B2121379 : Blo 2119435 2121379 := bstep (se 1 (by rfl) ⟨1591034, by rfl⟩ : syracuseStep 2121379 = 3182069) B3182069
theorem B2265365 : Blo 2119435 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B6040973 : Blo 2119435 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B4027315 : Blo 2119435 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B5369753 : Blo 2119435 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B3579835 : Blo 2119435 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B4773113 : Blo 2119435 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B3182075 : Blo 2119435 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B2121383 : Blo 2119435 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B2386561 : Blo 2119435 2386561 := bbase (se 2 (by rfl) ⟨894960, by rfl⟩ : syracuseStep 2386561 = 1789921) (by norm_num)
theorem B3182081 : Blo 2119435 3182081 := bstep (se 2 (by rfl) ⟨1193280, by rfl⟩ : syracuseStep 3182081 = 2386561) B2386561
theorem B2121387 : Blo 2119435 2121387 := bstep (se 1 (by rfl) ⟨1591040, by rfl⟩ : syracuseStep 2121387 = 3182081) B3182081
theorem B5369773 : Blo 2119435 5369773 := bbase (se 3 (by rfl) ⟨1006832, by rfl⟩ : syracuseStep 5369773 = 2013665) (by norm_num)
theorem B7159697 : Blo 2119435 7159697 := bstep (se 2 (by rfl) ⟨2684886, by rfl⟩ : syracuseStep 7159697 = 5369773) B5369773
theorem B4773131 : Blo 2119435 4773131 := bstep (se 1 (by rfl) ⟨3579848, by rfl⟩ : syracuseStep 4773131 = 7159697) B7159697
theorem B3182087 : Blo 2119435 3182087 := bstep (se 1 (by rfl) ⟨2386565, by rfl⟩ : syracuseStep 3182087 = 4773131) B4773131
theorem B2121391 : Blo 2119435 2121391 := bstep (se 1 (by rfl) ⟨1591043, by rfl⟩ : syracuseStep 2121391 = 3182087) B3182087
theorem B3182093 : Blo 2119435 3182093 := bbase (se 3 (by rfl) ⟨596642, by rfl⟩ : syracuseStep 3182093 = 1193285) (by norm_num)
theorem B2121395 : Blo 2119435 2121395 := bstep (se 1 (by rfl) ⟨1591046, by rfl⟩ : syracuseStep 2121395 = 3182093) B3182093
theorem B4773149 : Blo 2119435 4773149 := bbase (se 3 (by rfl) ⟨894965, by rfl⟩ : syracuseStep 4773149 = 1789931) (by norm_num)
theorem B3182099 : Blo 2119435 3182099 := bstep (se 1 (by rfl) ⟨2386574, by rfl⟩ : syracuseStep 3182099 = 4773149) B4773149
theorem B2121399 : Blo 2119435 2121399 := bstep (se 1 (by rfl) ⟨1591049, by rfl⟩ : syracuseStep 2121399 = 3182099) B3182099
theorem B3579869 : Blo 2119435 3579869 := bbase (se 3 (by rfl) ⟨671225, by rfl⟩ : syracuseStep 3579869 = 1342451) (by norm_num)
theorem B2386579 : Blo 2119435 2386579 := bstep (se 1 (by rfl) ⟨1789934, by rfl⟩ : syracuseStep 2386579 = 3579869) B3579869
theorem B3182105 : Blo 2119435 3182105 := bstep (se 2 (by rfl) ⟨1193289, by rfl⟩ : syracuseStep 3182105 = 2386579) B2386579
theorem B2121403 : Blo 2119435 2121403 := bstep (se 1 (by rfl) ⟨1591052, by rfl⟩ : syracuseStep 2121403 = 3182105) B3182105
theorem B5237165 : Blo 2119435 5237165 := bbase (se 3 (by rfl) ⟨981968, by rfl⟩ : syracuseStep 5237165 = 1963937) (by norm_num)
theorem B3491443 : Blo 2119435 3491443 := bstep (se 1 (by rfl) ⟨2618582, by rfl⟩ : syracuseStep 3491443 = 5237165) B5237165
theorem B18621029 : Blo 2119435 18621029 := bstep (se 4 (by rfl) ⟨1745721, by rfl⟩ : syracuseStep 18621029 = 3491443) B3491443
theorem B49656077 : Blo 2119435 49656077 := bstep (se 3 (by rfl) ⟨9310514, by rfl⟩ : syracuseStep 49656077 = 18621029) B18621029
theorem B33104051 : Blo 2119435 33104051 := bstep (se 1 (by rfl) ⟨24828038, by rfl⟩ : syracuseStep 33104051 = 49656077) B49656077
theorem B22069367 : Blo 2119435 22069367 := bstep (se 1 (by rfl) ⟨16552025, by rfl⟩ : syracuseStep 22069367 = 33104051) B33104051
theorem B14712911 : Blo 2119435 14712911 := bstep (se 1 (by rfl) ⟨11034683, by rfl⟩ : syracuseStep 14712911 = 22069367) B22069367
theorem B9808607 : Blo 2119435 9808607 := bstep (se 1 (by rfl) ⟨7356455, by rfl⟩ : syracuseStep 9808607 = 14712911) B14712911
theorem B6539071 : Blo 2119435 6539071 := bstep (se 1 (by rfl) ⟨4904303, by rfl⟩ : syracuseStep 6539071 = 9808607) B9808607
theorem B8718761 : Blo 2119435 8718761 := bstep (se 2 (by rfl) ⟨3269535, by rfl⟩ : syracuseStep 8718761 = 6539071) B6539071
theorem B5812507 : Blo 2119435 5812507 := bstep (se 1 (by rfl) ⟨4359380, by rfl⟩ : syracuseStep 5812507 = 8718761) B8718761
theorem B7750009 : Blo 2119435 7750009 := bstep (se 2 (by rfl) ⟨2906253, by rfl⟩ : syracuseStep 7750009 = 5812507) B5812507
theorem B10333345 : Blo 2119435 10333345 := bstep (se 2 (by rfl) ⟨3875004, by rfl⟩ : syracuseStep 10333345 = 7750009) B7750009
theorem B13777793 : Blo 2119435 13777793 := bstep (se 2 (by rfl) ⟨5166672, by rfl⟩ : syracuseStep 13777793 = 10333345) B10333345
theorem B9185195 : Blo 2119435 9185195 := bstep (se 1 (by rfl) ⟨6888896, by rfl⟩ : syracuseStep 9185195 = 13777793) B13777793
theorem B24493853 : Blo 2119435 24493853 := bstep (se 3 (by rfl) ⟨4592597, by rfl⟩ : syracuseStep 24493853 = 9185195) B9185195
theorem B16329235 : Blo 2119435 16329235 := bstep (se 1 (by rfl) ⟨12246926, by rfl⟩ : syracuseStep 16329235 = 24493853) B24493853
theorem B21772313 : Blo 2119435 21772313 := bstep (se 2 (by rfl) ⟨8164617, by rfl⟩ : syracuseStep 21772313 = 16329235) B16329235
theorem B14514875 : Blo 2119435 14514875 := bstep (se 1 (by rfl) ⟨10886156, by rfl⟩ : syracuseStep 14514875 = 21772313) B21772313
theorem B9676583 : Blo 2119435 9676583 := bstep (se 1 (by rfl) ⟨7257437, by rfl⟩ : syracuseStep 9676583 = 14514875) B14514875
theorem B6451055 : Blo 2119435 6451055 := bstep (se 1 (by rfl) ⟨4838291, by rfl⟩ : syracuseStep 6451055 = 9676583) B9676583
theorem B4300703 : Blo 2119435 4300703 := bstep (se 1 (by rfl) ⟨3225527, by rfl⟩ : syracuseStep 4300703 = 6451055) B6451055
theorem B2867135 : Blo 2119435 2867135 := bstep (se 1 (by rfl) ⟨2150351, by rfl⟩ : syracuseStep 2867135 = 4300703) B4300703
theorem B7645693 : Blo 2119435 7645693 := bstep (se 3 (by rfl) ⟨1433567, by rfl⟩ : syracuseStep 7645693 = 2867135) B2867135
theorem B10194257 : Blo 2119435 10194257 := bstep (se 2 (by rfl) ⟨3822846, by rfl⟩ : syracuseStep 10194257 = 7645693) B7645693
theorem B6796171 : Blo 2119435 6796171 := bstep (se 1 (by rfl) ⟨5097128, by rfl⟩ : syracuseStep 6796171 = 10194257) B10194257
theorem B9061561 : Blo 2119435 9061561 := bstep (se 2 (by rfl) ⟨3398085, by rfl⟩ : syracuseStep 9061561 = 6796171) B6796171
theorem B12082081 : Blo 2119435 12082081 := bstep (se 2 (by rfl) ⟨4530780, by rfl⟩ : syracuseStep 12082081 = 9061561) B9061561
theorem B16109441 : Blo 2119435 16109441 := bstep (se 2 (by rfl) ⟨6041040, by rfl⟩ : syracuseStep 16109441 = 12082081) B12082081
theorem B10739627 : Blo 2119435 10739627 := bstep (se 1 (by rfl) ⟨8054720, by rfl⟩ : syracuseStep 10739627 = 16109441) B16109441
theorem B7159751 : Blo 2119435 7159751 := bstep (se 1 (by rfl) ⟨5369813, by rfl⟩ : syracuseStep 7159751 = 10739627) B10739627
theorem B4773167 : Blo 2119435 4773167 := bstep (se 1 (by rfl) ⟨3579875, by rfl⟩ : syracuseStep 4773167 = 7159751) B7159751
theorem B3182111 : Blo 2119435 3182111 := bstep (se 1 (by rfl) ⟨2386583, by rfl⟩ : syracuseStep 3182111 = 4773167) B4773167
theorem B2121407 : Blo 2119435 2121407 := bstep (se 1 (by rfl) ⟨1591055, by rfl⟩ : syracuseStep 2121407 = 3182111) B3182111
theorem B3182117 : Blo 2119435 3182117 := bbase (se 4 (by rfl) ⟨298323, by rfl⟩ : syracuseStep 3182117 = 596647) (by norm_num)
theorem B2121411 : Blo 2119435 2121411 := bstep (se 1 (by rfl) ⟨1591058, by rfl⟩ : syracuseStep 2121411 = 3182117) B3182117
theorem B2684917 : Blo 2119435 2684917 := bbase (se 5 (by rfl) ⟨125855, by rfl⟩ : syracuseStep 2684917 = 251711) (by norm_num)
theorem B3579889 : Blo 2119435 3579889 := bstep (se 2 (by rfl) ⟨1342458, by rfl⟩ : syracuseStep 3579889 = 2684917) B2684917
theorem B4773185 : Blo 2119435 4773185 := bstep (se 2 (by rfl) ⟨1789944, by rfl⟩ : syracuseStep 4773185 = 3579889) B3579889
theorem B3182123 : Blo 2119435 3182123 := bstep (se 1 (by rfl) ⟨2386592, by rfl⟩ : syracuseStep 3182123 = 4773185) B4773185
theorem B2121415 : Blo 2119435 2121415 := bstep (se 1 (by rfl) ⟨1591061, by rfl⟩ : syracuseStep 2121415 = 3182123) B3182123
theorem B2386597 : Blo 2119435 2386597 := bbase (se 4 (by rfl) ⟨223743, by rfl⟩ : syracuseStep 2386597 = 447487) (by norm_num)
theorem B3182129 : Blo 2119435 3182129 := bstep (se 2 (by rfl) ⟨1193298, by rfl⟩ : syracuseStep 3182129 = 2386597) B2386597
theorem B2121419 : Blo 2119435 2121419 := bstep (se 1 (by rfl) ⟨1591064, by rfl⟩ : syracuseStep 2121419 = 3182129) B3182129
theorem B4359413 : Blo 2119435 4359413 := bbase (se 5 (by rfl) ⟨204347, by rfl⟩ : syracuseStep 4359413 = 408695) (by norm_num)
theorem B2906275 : Blo 2119435 2906275 := bstep (se 1 (by rfl) ⟨2179706, by rfl⟩ : syracuseStep 2906275 = 4359413) B4359413
theorem B3875033 : Blo 2119435 3875033 := bstep (se 2 (by rfl) ⟨1453137, by rfl⟩ : syracuseStep 3875033 = 2906275) B2906275
theorem B10333421 : Blo 2119435 10333421 := bstep (se 3 (by rfl) ⟨1937516, by rfl⟩ : syracuseStep 10333421 = 3875033) B3875033
theorem B6888947 : Blo 2119435 6888947 := bstep (se 1 (by rfl) ⟨5166710, by rfl⟩ : syracuseStep 6888947 = 10333421) B10333421
theorem B18370525 : Blo 2119435 18370525 := bstep (se 3 (by rfl) ⟨3444473, by rfl⟩ : syracuseStep 18370525 = 6888947) B6888947
theorem B24494033 : Blo 2119435 24494033 := bstep (se 2 (by rfl) ⟨9185262, by rfl⟩ : syracuseStep 24494033 = 18370525) B18370525
theorem B65317421 : Blo 2119435 65317421 := bstep (se 3 (by rfl) ⟨12247016, by rfl⟩ : syracuseStep 65317421 = 24494033) B24494033
theorem B43544947 : Blo 2119435 43544947 := bstep (se 1 (by rfl) ⟨32658710, by rfl⟩ : syracuseStep 43544947 = 65317421) B65317421
theorem B58059929 : Blo 2119435 58059929 := bstep (se 2 (by rfl) ⟨21772473, by rfl⟩ : syracuseStep 58059929 = 43544947) B43544947
theorem B154826477 : Blo 2119435 154826477 := bstep (se 3 (by rfl) ⟨29029964, by rfl⟩ : syracuseStep 154826477 = 58059929) B58059929
theorem B103217651 : Blo 2119435 103217651 := bstep (se 1 (by rfl) ⟨77413238, by rfl⟩ : syracuseStep 103217651 = 154826477) B154826477
theorem B68811767 : Blo 2119435 68811767 := bstep (se 1 (by rfl) ⟨51608825, by rfl⟩ : syracuseStep 68811767 = 103217651) B103217651
theorem B45874511 : Blo 2119435 45874511 := bstep (se 1 (by rfl) ⟨34405883, by rfl⟩ : syracuseStep 45874511 = 68811767) B68811767
theorem B30583007 : Blo 2119435 30583007 := bstep (se 1 (by rfl) ⟨22937255, by rfl⟩ : syracuseStep 30583007 = 45874511) B45874511
theorem B20388671 : Blo 2119435 20388671 := bstep (se 1 (by rfl) ⟨15291503, by rfl⟩ : syracuseStep 20388671 = 30583007) B30583007
theorem B13592447 : Blo 2119435 13592447 := bstep (se 1 (by rfl) ⟨10194335, by rfl⟩ : syracuseStep 13592447 = 20388671) B20388671
theorem B9061631 : Blo 2119435 9061631 := bstep (se 1 (by rfl) ⟨6796223, by rfl⟩ : syracuseStep 9061631 = 13592447) B13592447
theorem B6041087 : Blo 2119435 6041087 := bstep (se 1 (by rfl) ⟨4530815, by rfl⟩ : syracuseStep 6041087 = 9061631) B9061631
theorem B4027391 : Blo 2119435 4027391 := bstep (se 1 (by rfl) ⟨3020543, by rfl⟩ : syracuseStep 4027391 = 6041087) B6041087
theorem B2684927 : Blo 2119435 2684927 := bstep (se 1 (by rfl) ⟨2013695, by rfl⟩ : syracuseStep 2684927 = 4027391) B4027391
theorem B7159805 : Blo 2119435 7159805 := bstep (se 3 (by rfl) ⟨1342463, by rfl⟩ : syracuseStep 7159805 = 2684927) B2684927
theorem B4773203 : Blo 2119435 4773203 := bstep (se 1 (by rfl) ⟨3579902, by rfl⟩ : syracuseStep 4773203 = 7159805) B7159805
theorem B3182135 : Blo 2119435 3182135 := bstep (se 1 (by rfl) ⟨2386601, by rfl⟩ : syracuseStep 3182135 = 4773203) B4773203
theorem B2121423 : Blo 2119435 2121423 := bstep (se 1 (by rfl) ⟨1591067, by rfl⟩ : syracuseStep 2121423 = 3182135) B3182135
theorem B3182141 : Blo 2119435 3182141 := bbase (se 3 (by rfl) ⟨596651, by rfl⟩ : syracuseStep 3182141 = 1193303) (by norm_num)
theorem B2121427 : Blo 2119435 2121427 := bstep (se 1 (by rfl) ⟨1591070, by rfl⟩ : syracuseStep 2121427 = 3182141) B3182141
theorem B4773221 : Blo 2119435 4773221 := bbase (se 4 (by rfl) ⟨447489, by rfl⟩ : syracuseStep 4773221 = 894979) (by norm_num)
theorem B3182147 : Blo 2119435 3182147 := bstep (se 1 (by rfl) ⟨2386610, by rfl⟩ : syracuseStep 3182147 = 4773221) B4773221
theorem B2121431 : Blo 2119435 2121431 := bstep (se 1 (by rfl) ⟨1591073, by rfl⟩ : syracuseStep 2121431 = 3182147) B3182147
theorem B5369885 : Blo 2119435 5369885 := bbase (se 3 (by rfl) ⟨1006853, by rfl⟩ : syracuseStep 5369885 = 2013707) (by norm_num)
theorem B3579923 : Blo 2119435 3579923 := bstep (se 1 (by rfl) ⟨2684942, by rfl⟩ : syracuseStep 3579923 = 5369885) B5369885
theorem B2386615 : Blo 2119435 2386615 := bstep (se 1 (by rfl) ⟨1789961, by rfl⟩ : syracuseStep 2386615 = 3579923) B3579923
theorem B3182153 : Blo 2119435 3182153 := bstep (se 2 (by rfl) ⟨1193307, by rfl⟩ : syracuseStep 3182153 = 2386615) B2386615
theorem B2121435 : Blo 2119435 2121435 := bstep (se 1 (by rfl) ⟨1591076, by rfl⟩ : syracuseStep 2121435 = 3182153) B3182153
theorem C0 (j : ℕ) (h1 : 529858 ≤ j) (h2 : j ≤ 530358) : Blo 2119435 (4 * j + 3) := by
  interval_cases j
  · exact B2119435
  · exact B2119439
  · exact B2119443
  · exact B2119447
  · exact B2119451
  · exact B2119455
  · exact B2119459
  · exact B2119463
  · exact B2119467
  · exact B2119471
  · exact B2119475
  · exact B2119479
  · exact B2119483
  · exact B2119487
  · exact B2119491
  · exact B2119495
  · exact B2119499
  · exact B2119503
  · exact B2119507
  · exact B2119511
  · exact B2119515
  · exact B2119519
  · exact B2119523
  · exact B2119527
  · exact B2119531
  · exact B2119535
  · exact B2119539
  · exact B2119543
  · exact B2119547
  · exact B2119551
  · exact B2119555
  · exact B2119559
  · exact B2119563
  · exact B2119567
  · exact B2119571
  · exact B2119575
  · exact B2119579
  · exact B2119583
  · exact B2119587
  · exact B2119591
  · exact B2119595
  · exact B2119599
  · exact B2119603
  · exact B2119607
  · exact B2119611
  · exact B2119615
  · exact B2119619
  · exact B2119623
  · exact B2119627
  · exact B2119631
  · exact B2119635
  · exact B2119639
  · exact B2119643
  · exact B2119647
  · exact B2119651
  · exact B2119655
  · exact B2119659
  · exact B2119663
  · exact B2119667
  · exact B2119671
  · exact B2119675
  · exact B2119679
  · exact B2119683
  · exact B2119687
  · exact B2119691
  · exact B2119695
  · exact B2119699
  · exact B2119703
  · exact B2119707
  · exact B2119711
  · exact B2119715
  · exact B2119719
  · exact B2119723
  · exact B2119727
  · exact B2119731
  · exact B2119735
  · exact B2119739
  · exact B2119743
  · exact B2119747
  · exact B2119751
  · exact B2119755
  · exact B2119759
  · exact B2119763
  · exact B2119767
  · exact B2119771
  · exact B2119775
  · exact B2119779
  · exact B2119783
  · exact B2119787
  · exact B2119791
  · exact B2119795
  · exact B2119799
  · exact B2119803
  · exact B2119807
  · exact B2119811
  · exact B2119815
  · exact B2119819
  · exact B2119823
  · exact B2119827
  · exact B2119831
  · exact B2119835
  · exact B2119839
  · exact B2119843
  · exact B2119847
  · exact B2119851
  · exact B2119855
  · exact B2119859
  · exact B2119863
  · exact B2119867
  · exact B2119871
  · exact B2119875
  · exact B2119879
  · exact B2119883
  · exact B2119887
  · exact B2119891
  · exact B2119895
  · exact B2119899
  · exact B2119903
  · exact B2119907
  · exact B2119911
  · exact B2119915
  · exact B2119919
  · exact B2119923
  · exact B2119927
  · exact B2119931
  · exact B2119935
  · exact B2119939
  · exact B2119943
  · exact B2119947
  · exact B2119951
  · exact B2119955
  · exact B2119959
  · exact B2119963
  · exact B2119967
  · exact B2119971
  · exact B2119975
  · exact B2119979
  · exact B2119983
  · exact B2119987
  · exact B2119991
  · exact B2119995
  · exact B2119999
  · exact B2120003
  · exact B2120007
  · exact B2120011
  · exact B2120015
  · exact B2120019
  · exact B2120023
  · exact B2120027
  · exact B2120031
  · exact B2120035
  · exact B2120039
  · exact B2120043
  · exact B2120047
  · exact B2120051
  · exact B2120055
  · exact B2120059
  · exact B2120063
  · exact B2120067
  · exact B2120071
  · exact B2120075
  · exact B2120079
  · exact B2120083
  · exact B2120087
  · exact B2120091
  · exact B2120095
  · exact B2120099
  · exact B2120103
  · exact B2120107
  · exact B2120111
  · exact B2120115
  · exact B2120119
  · exact B2120123
  · exact B2120127
  · exact B2120131
  · exact B2120135
  · exact B2120139
  · exact B2120143
  · exact B2120147
  · exact B2120151
  · exact B2120155
  · exact B2120159
  · exact B2120163
  · exact B2120167
  · exact B2120171
  · exact B2120175
  · exact B2120179
  · exact B2120183
  · exact B2120187
  · exact B2120191
  · exact B2120195
  · exact B2120199
  · exact B2120203
  · exact B2120207
  · exact B2120211
  · exact B2120215
  · exact B2120219
  · exact B2120223
  · exact B2120227
  · exact B2120231
  · exact B2120235
  · exact B2120239
  · exact B2120243
  · exact B2120247
  · exact B2120251
  · exact B2120255
  · exact B2120259
  · exact B2120263
  · exact B2120267
  · exact B2120271
  · exact B2120275
  · exact B2120279
  · exact B2120283
  · exact B2120287
  · exact B2120291
  · exact B2120295
  · exact B2120299
  · exact B2120303
  · exact B2120307
  · exact B2120311
  · exact B2120315
  · exact B2120319
  · exact B2120323
  · exact B2120327
  · exact B2120331
  · exact B2120335
  · exact B2120339
  · exact B2120343
  · exact B2120347
  · exact B2120351
  · exact B2120355
  · exact B2120359
  · exact B2120363
  · exact B2120367
  · exact B2120371
  · exact B2120375
  · exact B2120379
  · exact B2120383
  · exact B2120387
  · exact B2120391
  · exact B2120395
  · exact B2120399
  · exact B2120403
  · exact B2120407
  · exact B2120411
  · exact B2120415
  · exact B2120419
  · exact B2120423
  · exact B2120427
  · exact B2120431
  · exact B2120435
  · exact B2120439
  · exact B2120443
  · exact B2120447
  · exact B2120451
  · exact B2120455
  · exact B2120459
  · exact B2120463
  · exact B2120467
  · exact B2120471
  · exact B2120475
  · exact B2120479
  · exact B2120483
  · exact B2120487
  · exact B2120491
  · exact B2120495
  · exact B2120499
  · exact B2120503
  · exact B2120507
  · exact B2120511
  · exact B2120515
  · exact B2120519
  · exact B2120523
  · exact B2120527
  · exact B2120531
  · exact B2120535
  · exact B2120539
  · exact B2120543
  · exact B2120547
  · exact B2120551
  · exact B2120555
  · exact B2120559
  · exact B2120563
  · exact B2120567
  · exact B2120571
  · exact B2120575
  · exact B2120579
  · exact B2120583
  · exact B2120587
  · exact B2120591
  · exact B2120595
  · exact B2120599
  · exact B2120603
  · exact B2120607
  · exact B2120611
  · exact B2120615
  · exact B2120619
  · exact B2120623
  · exact B2120627
  · exact B2120631
  · exact B2120635
  · exact B2120639
  · exact B2120643
  · exact B2120647
  · exact B2120651
  · exact B2120655
  · exact B2120659
  · exact B2120663
  · exact B2120667
  · exact B2120671
  · exact B2120675
  · exact B2120679
  · exact B2120683
  · exact B2120687
  · exact B2120691
  · exact B2120695
  · exact B2120699
  · exact B2120703
  · exact B2120707
  · exact B2120711
  · exact B2120715
  · exact B2120719
  · exact B2120723
  · exact B2120727
  · exact B2120731
  · exact B2120735
  · exact B2120739
  · exact B2120743
  · exact B2120747
  · exact B2120751
  · exact B2120755
  · exact B2120759
  · exact B2120763
  · exact B2120767
  · exact B2120771
  · exact B2120775
  · exact B2120779
  · exact B2120783
  · exact B2120787
  · exact B2120791
  · exact B2120795
  · exact B2120799
  · exact B2120803
  · exact B2120807
  · exact B2120811
  · exact B2120815
  · exact B2120819
  · exact B2120823
  · exact B2120827
  · exact B2120831
  · exact B2120835
  · exact B2120839
  · exact B2120843
  · exact B2120847
  · exact B2120851
  · exact B2120855
  · exact B2120859
  · exact B2120863
  · exact B2120867
  · exact B2120871
  · exact B2120875
  · exact B2120879
  · exact B2120883
  · exact B2120887
  · exact B2120891
  · exact B2120895
  · exact B2120899
  · exact B2120903
  · exact B2120907
  · exact B2120911
  · exact B2120915
  · exact B2120919
  · exact B2120923
  · exact B2120927
  · exact B2120931
  · exact B2120935
  · exact B2120939
  · exact B2120943
  · exact B2120947
  · exact B2120951
  · exact B2120955
  · exact B2120959
  · exact B2120963
  · exact B2120967
  · exact B2120971
  · exact B2120975
  · exact B2120979
  · exact B2120983
  · exact B2120987
  · exact B2120991
  · exact B2120995
  · exact B2120999
  · exact B2121003
  · exact B2121007
  · exact B2121011
  · exact B2121015
  · exact B2121019
  · exact B2121023
  · exact B2121027
  · exact B2121031
  · exact B2121035
  · exact B2121039
  · exact B2121043
  · exact B2121047
  · exact B2121051
  · exact B2121055
  · exact B2121059
  · exact B2121063
  · exact B2121067
  · exact B2121071
  · exact B2121075
  · exact B2121079
  · exact B2121083
  · exact B2121087
  · exact B2121091
  · exact B2121095
  · exact B2121099
  · exact B2121103
  · exact B2121107
  · exact B2121111
  · exact B2121115
  · exact B2121119
  · exact B2121123
  · exact B2121127
  · exact B2121131
  · exact B2121135
  · exact B2121139
  · exact B2121143
  · exact B2121147
  · exact B2121151
  · exact B2121155
  · exact B2121159
  · exact B2121163
  · exact B2121167
  · exact B2121171
  · exact B2121175
  · exact B2121179
  · exact B2121183
  · exact B2121187
  · exact B2121191
  · exact B2121195
  · exact B2121199
  · exact B2121203
  · exact B2121207
  · exact B2121211
  · exact B2121215
  · exact B2121219
  · exact B2121223
  · exact B2121227
  · exact B2121231
  · exact B2121235
  · exact B2121239
  · exact B2121243
  · exact B2121247
  · exact B2121251
  · exact B2121255
  · exact B2121259
  · exact B2121263
  · exact B2121267
  · exact B2121271
  · exact B2121275
  · exact B2121279
  · exact B2121283
  · exact B2121287
  · exact B2121291
  · exact B2121295
  · exact B2121299
  · exact B2121303
  · exact B2121307
  · exact B2121311
  · exact B2121315
  · exact B2121319
  · exact B2121323
  · exact B2121327
  · exact B2121331
  · exact B2121335
  · exact B2121339
  · exact B2121343
  · exact B2121347
  · exact B2121351
  · exact B2121355
  · exact B2121359
  · exact B2121363
  · exact B2121367
  · exact B2121371
  · exact B2121375
  · exact B2121379
  · exact B2121383
  · exact B2121387
  · exact B2121391
  · exact B2121395
  · exact B2121399
  · exact B2121403
  · exact B2121407
  · exact B2121411
  · exact B2121415
  · exact B2121419
  · exact B2121423
  · exact B2121427
  · exact B2121431
  · exact B2121435
theorem solution (m : ℕ) (hlo : 2119435 ≤ m) (hhi : m ≤ 2121435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 529858 ≤ j := by omega
    have hj2 : j ≤ 530358 := by omega
    have hb : Blo 2119435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
