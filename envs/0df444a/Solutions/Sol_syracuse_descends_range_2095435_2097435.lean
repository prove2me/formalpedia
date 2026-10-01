-- Prove2me | solution 1 for syracuse_descends_range_2095435_2097435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:30.166764+00:00
-- url     : https://prove2.me/submissions/00ec9bb9-1a15-4cbe-9a78-77881fe379e8

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

theorem B2357365 : Blo 2095435 2357365 := bbase (se 5 (by rfl) ⟨110501, by rfl⟩ : syracuseStep 2357365 = 221003) (by norm_num)
theorem B3143153 : Blo 2095435 3143153 := bstep (se 2 (by rfl) ⟨1178682, by rfl⟩ : syracuseStep 3143153 = 2357365) B2357365
theorem B2095435 : Blo 2095435 2095435 := bstep (se 1 (by rfl) ⟨1571576, by rfl⟩ : syracuseStep 2095435 = 3143153) B3143153
theorem B2652041 : Blo 2095435 2652041 := bbase (se 2 (by rfl) ⟨994515, by rfl⟩ : syracuseStep 2652041 = 1989031) (by norm_num)
theorem B7072109 : Blo 2095435 7072109 := bstep (se 3 (by rfl) ⟨1326020, by rfl⟩ : syracuseStep 7072109 = 2652041) B2652041
theorem B4714739 : Blo 2095435 4714739 := bstep (se 1 (by rfl) ⟨3536054, by rfl⟩ : syracuseStep 4714739 = 7072109) B7072109
theorem B3143159 : Blo 2095435 3143159 := bstep (se 1 (by rfl) ⟨2357369, by rfl⟩ : syracuseStep 3143159 = 4714739) B4714739
theorem B2095439 : Blo 2095435 2095439 := bstep (se 1 (by rfl) ⟨1571579, by rfl⟩ : syracuseStep 2095439 = 3143159) B3143159
theorem B3143165 : Blo 2095435 3143165 := bbase (se 3 (by rfl) ⟨589343, by rfl⟩ : syracuseStep 3143165 = 1178687) (by norm_num)
theorem B2095443 : Blo 2095435 2095443 := bstep (se 1 (by rfl) ⟨1571582, by rfl⟩ : syracuseStep 2095443 = 3143165) B3143165
theorem B4714757 : Blo 2095435 4714757 := bbase (se 4 (by rfl) ⟨442008, by rfl⟩ : syracuseStep 4714757 = 884017) (by norm_num)
theorem B3143171 : Blo 2095435 3143171 := bstep (se 1 (by rfl) ⟨2357378, by rfl⟩ : syracuseStep 3143171 = 4714757) B4714757
theorem B2095447 : Blo 2095435 2095447 := bstep (se 1 (by rfl) ⟨1571585, by rfl⟩ : syracuseStep 2095447 = 3143171) B3143171
theorem B3978085 : Blo 2095435 3978085 := bbase (se 4 (by rfl) ⟨372945, by rfl⟩ : syracuseStep 3978085 = 745891) (by norm_num)
theorem B5304113 : Blo 2095435 5304113 := bstep (se 2 (by rfl) ⟨1989042, by rfl⟩ : syracuseStep 5304113 = 3978085) B3978085
theorem B3536075 : Blo 2095435 3536075 := bstep (se 1 (by rfl) ⟨2652056, by rfl⟩ : syracuseStep 3536075 = 5304113) B5304113
theorem B2357383 : Blo 2095435 2357383 := bstep (se 1 (by rfl) ⟨1768037, by rfl⟩ : syracuseStep 2357383 = 3536075) B3536075
theorem B3143177 : Blo 2095435 3143177 := bstep (se 2 (by rfl) ⟨1178691, by rfl⟩ : syracuseStep 3143177 = 2357383) B2357383
theorem B2095451 : Blo 2095435 2095451 := bstep (se 1 (by rfl) ⟨1571588, by rfl⟩ : syracuseStep 2095451 = 3143177) B3143177
theorem B10608245 : Blo 2095435 10608245 := bbase (se 5 (by rfl) ⟨497261, by rfl⟩ : syracuseStep 10608245 = 994523) (by norm_num)
theorem B7072163 : Blo 2095435 7072163 := bstep (se 1 (by rfl) ⟨5304122, by rfl⟩ : syracuseStep 7072163 = 10608245) B10608245
theorem B4714775 : Blo 2095435 4714775 := bstep (se 1 (by rfl) ⟨3536081, by rfl⟩ : syracuseStep 4714775 = 7072163) B7072163
theorem B3143183 : Blo 2095435 3143183 := bstep (se 1 (by rfl) ⟨2357387, by rfl⟩ : syracuseStep 3143183 = 4714775) B4714775
theorem B2095455 : Blo 2095435 2095455 := bstep (se 1 (by rfl) ⟨1571591, by rfl⟩ : syracuseStep 2095455 = 3143183) B3143183
theorem B3143189 : Blo 2095435 3143189 := bbase (se 6 (by rfl) ⟨73668, by rfl⟩ : syracuseStep 3143189 = 147337) (by norm_num)
theorem B2095459 : Blo 2095435 2095459 := bstep (se 1 (by rfl) ⟨1571594, by rfl⟩ : syracuseStep 2095459 = 3143189) B3143189
theorem B3584341 : Blo 2095435 3584341 := bbase (se 10 (by rfl) ⟨5250, by rfl⟩ : syracuseStep 3584341 = 10501) (by norm_num)
theorem B19116485 : Blo 2095435 19116485 := bstep (se 4 (by rfl) ⟨1792170, by rfl⟩ : syracuseStep 19116485 = 3584341) B3584341
theorem B12744323 : Blo 2095435 12744323 := bstep (se 1 (by rfl) ⟨9558242, by rfl⟩ : syracuseStep 12744323 = 19116485) B19116485
theorem B8496215 : Blo 2095435 8496215 := bstep (se 1 (by rfl) ⟨6372161, by rfl⟩ : syracuseStep 8496215 = 12744323) B12744323
theorem B5664143 : Blo 2095435 5664143 := bstep (se 1 (by rfl) ⟨4248107, by rfl⟩ : syracuseStep 5664143 = 8496215) B8496215
theorem B3776095 : Blo 2095435 3776095 := bstep (se 1 (by rfl) ⟨2832071, by rfl⟩ : syracuseStep 3776095 = 5664143) B5664143
theorem B5034793 : Blo 2095435 5034793 := bstep (se 2 (by rfl) ⟨1888047, by rfl⟩ : syracuseStep 5034793 = 3776095) B3776095
theorem B6713057 : Blo 2095435 6713057 := bstep (se 2 (by rfl) ⟨2517396, by rfl⟩ : syracuseStep 6713057 = 5034793) B5034793
theorem B17901485 : Blo 2095435 17901485 := bstep (se 3 (by rfl) ⟨3356528, by rfl⟩ : syracuseStep 17901485 = 6713057) B6713057
theorem B11934323 : Blo 2095435 11934323 := bstep (se 1 (by rfl) ⟨8950742, by rfl⟩ : syracuseStep 11934323 = 17901485) B17901485
theorem B7956215 : Blo 2095435 7956215 := bstep (se 1 (by rfl) ⟨5967161, by rfl⟩ : syracuseStep 7956215 = 11934323) B11934323
theorem B5304143 : Blo 2095435 5304143 := bstep (se 1 (by rfl) ⟨3978107, by rfl⟩ : syracuseStep 5304143 = 7956215) B7956215
theorem B3536095 : Blo 2095435 3536095 := bstep (se 1 (by rfl) ⟨2652071, by rfl⟩ : syracuseStep 3536095 = 5304143) B5304143
theorem B4714793 : Blo 2095435 4714793 := bstep (se 2 (by rfl) ⟨1768047, by rfl⟩ : syracuseStep 4714793 = 3536095) B3536095
theorem B3143195 : Blo 2095435 3143195 := bstep (se 1 (by rfl) ⟨2357396, by rfl⟩ : syracuseStep 3143195 = 4714793) B4714793
theorem B2095463 : Blo 2095435 2095463 := bstep (se 1 (by rfl) ⟨1571597, by rfl⟩ : syracuseStep 2095463 = 3143195) B3143195
theorem B2357401 : Blo 2095435 2357401 := bbase (se 2 (by rfl) ⟨884025, by rfl⟩ : syracuseStep 2357401 = 1768051) (by norm_num)
theorem B3143201 : Blo 2095435 3143201 := bstep (se 2 (by rfl) ⟨1178700, by rfl⟩ : syracuseStep 3143201 = 2357401) B2357401
theorem B2095467 : Blo 2095435 2095467 := bstep (se 1 (by rfl) ⟨1571600, by rfl⟩ : syracuseStep 2095467 = 3143201) B3143201
theorem B7956245 : Blo 2095435 7956245 := bbase (se 6 (by rfl) ⟨186474, by rfl⟩ : syracuseStep 7956245 = 372949) (by norm_num)
theorem B5304163 : Blo 2095435 5304163 := bstep (se 1 (by rfl) ⟨3978122, by rfl⟩ : syracuseStep 5304163 = 7956245) B7956245
theorem B7072217 : Blo 2095435 7072217 := bstep (se 2 (by rfl) ⟨2652081, by rfl⟩ : syracuseStep 7072217 = 5304163) B5304163
theorem B4714811 : Blo 2095435 4714811 := bstep (se 1 (by rfl) ⟨3536108, by rfl⟩ : syracuseStep 4714811 = 7072217) B7072217
theorem B3143207 : Blo 2095435 3143207 := bstep (se 1 (by rfl) ⟨2357405, by rfl⟩ : syracuseStep 3143207 = 4714811) B4714811
theorem B2095471 : Blo 2095435 2095471 := bstep (se 1 (by rfl) ⟨1571603, by rfl⟩ : syracuseStep 2095471 = 3143207) B3143207
theorem B3143213 : Blo 2095435 3143213 := bbase (se 3 (by rfl) ⟨589352, by rfl⟩ : syracuseStep 3143213 = 1178705) (by norm_num)
theorem B2095475 : Blo 2095435 2095475 := bstep (se 1 (by rfl) ⟨1571606, by rfl⟩ : syracuseStep 2095475 = 3143213) B3143213
theorem B4714829 : Blo 2095435 4714829 := bbase (se 3 (by rfl) ⟨884030, by rfl⟩ : syracuseStep 4714829 = 1768061) (by norm_num)
theorem B3143219 : Blo 2095435 3143219 := bstep (se 1 (by rfl) ⟨2357414, by rfl⟩ : syracuseStep 3143219 = 4714829) B4714829
theorem B2095479 : Blo 2095435 2095479 := bstep (se 1 (by rfl) ⟨1571609, by rfl⟩ : syracuseStep 2095479 = 3143219) B3143219
theorem B2652097 : Blo 2095435 2652097 := bbase (se 2 (by rfl) ⟨994536, by rfl⟩ : syracuseStep 2652097 = 1989073) (by norm_num)
theorem B3536129 : Blo 2095435 3536129 := bstep (se 2 (by rfl) ⟨1326048, by rfl⟩ : syracuseStep 3536129 = 2652097) B2652097
theorem B2357419 : Blo 2095435 2357419 := bstep (se 1 (by rfl) ⟨1768064, by rfl⟩ : syracuseStep 2357419 = 3536129) B3536129
theorem B3143225 : Blo 2095435 3143225 := bstep (se 2 (by rfl) ⟨1178709, by rfl⟩ : syracuseStep 3143225 = 2357419) B2357419
theorem B2095483 : Blo 2095435 2095483 := bstep (se 1 (by rfl) ⟨1571612, by rfl⟩ : syracuseStep 2095483 = 3143225) B3143225
theorem B7552277 : Blo 2095435 7552277 := bbase (se 6 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 7552277 = 354013) (by norm_num)
theorem B5034851 : Blo 2095435 5034851 := bstep (se 1 (by rfl) ⟨3776138, by rfl⟩ : syracuseStep 5034851 = 7552277) B7552277
theorem B3356567 : Blo 2095435 3356567 := bstep (se 1 (by rfl) ⟨2517425, by rfl⟩ : syracuseStep 3356567 = 5034851) B5034851
theorem B2237711 : Blo 2095435 2237711 := bstep (se 1 (by rfl) ⟨1678283, by rfl⟩ : syracuseStep 2237711 = 3356567) B3356567
theorem B23868917 : Blo 2095435 23868917 := bstep (se 5 (by rfl) ⟨1118855, by rfl⟩ : syracuseStep 23868917 = 2237711) B2237711
theorem B15912611 : Blo 2095435 15912611 := bstep (se 1 (by rfl) ⟨11934458, by rfl⟩ : syracuseStep 15912611 = 23868917) B23868917
theorem B10608407 : Blo 2095435 10608407 := bstep (se 1 (by rfl) ⟨7956305, by rfl⟩ : syracuseStep 10608407 = 15912611) B15912611
theorem B7072271 : Blo 2095435 7072271 := bstep (se 1 (by rfl) ⟨5304203, by rfl⟩ : syracuseStep 7072271 = 10608407) B10608407
theorem B4714847 : Blo 2095435 4714847 := bstep (se 1 (by rfl) ⟨3536135, by rfl⟩ : syracuseStep 4714847 = 7072271) B7072271
theorem B3143231 : Blo 2095435 3143231 := bstep (se 1 (by rfl) ⟨2357423, by rfl⟩ : syracuseStep 3143231 = 4714847) B4714847
theorem B2095487 : Blo 2095435 2095487 := bstep (se 1 (by rfl) ⟨1571615, by rfl⟩ : syracuseStep 2095487 = 3143231) B3143231
theorem B3143237 : Blo 2095435 3143237 := bbase (se 4 (by rfl) ⟨294678, by rfl⟩ : syracuseStep 3143237 = 589357) (by norm_num)
theorem B2095491 : Blo 2095435 2095491 := bstep (se 1 (by rfl) ⟨1571618, by rfl⟩ : syracuseStep 2095491 = 3143237) B3143237
theorem B3536149 : Blo 2095435 3536149 := bbase (se 6 (by rfl) ⟨82878, by rfl⟩ : syracuseStep 3536149 = 165757) (by norm_num)
theorem B4714865 : Blo 2095435 4714865 := bstep (se 2 (by rfl) ⟨1768074, by rfl⟩ : syracuseStep 4714865 = 3536149) B3536149
theorem B3143243 : Blo 2095435 3143243 := bstep (se 1 (by rfl) ⟨2357432, by rfl⟩ : syracuseStep 3143243 = 4714865) B4714865
theorem B2095495 : Blo 2095435 2095495 := bstep (se 1 (by rfl) ⟨1571621, by rfl⟩ : syracuseStep 2095495 = 3143243) B3143243
theorem B2357437 : Blo 2095435 2357437 := bbase (se 3 (by rfl) ⟨442019, by rfl⟩ : syracuseStep 2357437 = 884039) (by norm_num)
theorem B3143249 : Blo 2095435 3143249 := bstep (se 2 (by rfl) ⟨1178718, by rfl⟩ : syracuseStep 3143249 = 2357437) B2357437
theorem B2095499 : Blo 2095435 2095499 := bstep (se 1 (by rfl) ⟨1571624, by rfl⟩ : syracuseStep 2095499 = 3143249) B3143249
theorem B7072325 : Blo 2095435 7072325 := bbase (se 4 (by rfl) ⟨663030, by rfl⟩ : syracuseStep 7072325 = 1326061) (by norm_num)
theorem B4714883 : Blo 2095435 4714883 := bstep (se 1 (by rfl) ⟨3536162, by rfl⟩ : syracuseStep 4714883 = 7072325) B7072325
theorem B3143255 : Blo 2095435 3143255 := bstep (se 1 (by rfl) ⟨2357441, by rfl⟩ : syracuseStep 3143255 = 4714883) B4714883
theorem B2095503 : Blo 2095435 2095503 := bstep (se 1 (by rfl) ⟨1571627, by rfl⟩ : syracuseStep 2095503 = 3143255) B3143255
theorem B3143261 : Blo 2095435 3143261 := bbase (se 3 (by rfl) ⟨589361, by rfl⟩ : syracuseStep 3143261 = 1178723) (by norm_num)
theorem B2095507 : Blo 2095435 2095507 := bstep (se 1 (by rfl) ⟨1571630, by rfl⟩ : syracuseStep 2095507 = 3143261) B3143261
theorem B4714901 : Blo 2095435 4714901 := bbase (se 6 (by rfl) ⟨110505, by rfl⟩ : syracuseStep 4714901 = 221011) (by norm_num)
theorem B3143267 : Blo 2095435 3143267 := bstep (se 1 (by rfl) ⟨2357450, by rfl⟩ : syracuseStep 3143267 = 4714901) B4714901
theorem B2095511 : Blo 2095435 2095511 := bstep (se 1 (by rfl) ⟨1571633, by rfl⟩ : syracuseStep 2095511 = 3143267) B3143267
theorem B4032485 : Blo 2095435 4032485 := bbase (se 4 (by rfl) ⟨378045, by rfl⟩ : syracuseStep 4032485 = 756091) (by norm_num)
theorem B2688323 : Blo 2095435 2688323 := bstep (se 1 (by rfl) ⟨2016242, by rfl⟩ : syracuseStep 2688323 = 4032485) B4032485
theorem B7168861 : Blo 2095435 7168861 := bstep (se 3 (by rfl) ⟨1344161, by rfl⟩ : syracuseStep 7168861 = 2688323) B2688323
theorem B9558481 : Blo 2095435 9558481 := bstep (se 2 (by rfl) ⟨3584430, by rfl⟩ : syracuseStep 9558481 = 7168861) B7168861
theorem B12744641 : Blo 2095435 12744641 := bstep (se 2 (by rfl) ⟨4779240, by rfl⟩ : syracuseStep 12744641 = 9558481) B9558481
theorem B8496427 : Blo 2095435 8496427 := bstep (se 1 (by rfl) ⟨6372320, by rfl⟩ : syracuseStep 8496427 = 12744641) B12744641
theorem B11328569 : Blo 2095435 11328569 := bstep (se 2 (by rfl) ⟨4248213, by rfl⟩ : syracuseStep 11328569 = 8496427) B8496427
theorem B7552379 : Blo 2095435 7552379 := bstep (se 1 (by rfl) ⟨5664284, by rfl⟩ : syracuseStep 7552379 = 11328569) B11328569
theorem B5034919 : Blo 2095435 5034919 := bstep (se 1 (by rfl) ⟨3776189, by rfl⟩ : syracuseStep 5034919 = 7552379) B7552379
theorem B6713225 : Blo 2095435 6713225 := bstep (se 2 (by rfl) ⟨2517459, by rfl⟩ : syracuseStep 6713225 = 5034919) B5034919
theorem B4475483 : Blo 2095435 4475483 := bstep (se 1 (by rfl) ⟨3356612, by rfl⟩ : syracuseStep 4475483 = 6713225) B6713225
theorem B2983655 : Blo 2095435 2983655 := bstep (se 1 (by rfl) ⟨2237741, by rfl⟩ : syracuseStep 2983655 = 4475483) B4475483
theorem B7956413 : Blo 2095435 7956413 := bstep (se 3 (by rfl) ⟨1491827, by rfl⟩ : syracuseStep 7956413 = 2983655) B2983655
theorem B5304275 : Blo 2095435 5304275 := bstep (se 1 (by rfl) ⟨3978206, by rfl⟩ : syracuseStep 5304275 = 7956413) B7956413
theorem B3536183 : Blo 2095435 3536183 := bstep (se 1 (by rfl) ⟨2652137, by rfl⟩ : syracuseStep 3536183 = 5304275) B5304275
theorem B2357455 : Blo 2095435 2357455 := bstep (se 1 (by rfl) ⟨1768091, by rfl⟩ : syracuseStep 2357455 = 3536183) B3536183
theorem B3143273 : Blo 2095435 3143273 := bstep (se 2 (by rfl) ⟨1178727, by rfl⟩ : syracuseStep 3143273 = 2357455) B2357455
theorem B2095515 : Blo 2095435 2095515 := bstep (se 1 (by rfl) ⟨1571636, by rfl⟩ : syracuseStep 2095515 = 3143273) B3143273
theorem B8950981 : Blo 2095435 8950981 := bbase (se 4 (by rfl) ⟨839154, by rfl⟩ : syracuseStep 8950981 = 1678309) (by norm_num)
theorem B11934641 : Blo 2095435 11934641 := bstep (se 2 (by rfl) ⟨4475490, by rfl⟩ : syracuseStep 11934641 = 8950981) B8950981
theorem B7956427 : Blo 2095435 7956427 := bstep (se 1 (by rfl) ⟨5967320, by rfl⟩ : syracuseStep 7956427 = 11934641) B11934641
theorem B10608569 : Blo 2095435 10608569 := bstep (se 2 (by rfl) ⟨3978213, by rfl⟩ : syracuseStep 10608569 = 7956427) B7956427
theorem B7072379 : Blo 2095435 7072379 := bstep (se 1 (by rfl) ⟨5304284, by rfl⟩ : syracuseStep 7072379 = 10608569) B10608569
theorem B4714919 : Blo 2095435 4714919 := bstep (se 1 (by rfl) ⟨3536189, by rfl⟩ : syracuseStep 4714919 = 7072379) B7072379
theorem B3143279 : Blo 2095435 3143279 := bstep (se 1 (by rfl) ⟨2357459, by rfl⟩ : syracuseStep 3143279 = 4714919) B4714919
theorem B2095519 : Blo 2095435 2095519 := bstep (se 1 (by rfl) ⟨1571639, by rfl⟩ : syracuseStep 2095519 = 3143279) B3143279
theorem B3143285 : Blo 2095435 3143285 := bbase (se 5 (by rfl) ⟨147341, by rfl⟩ : syracuseStep 3143285 = 294683) (by norm_num)
theorem B2095523 : Blo 2095435 2095523 := bstep (se 1 (by rfl) ⟨1571642, by rfl⟩ : syracuseStep 2095523 = 3143285) B3143285
theorem B3978229 : Blo 2095435 3978229 := bbase (se 5 (by rfl) ⟨186479, by rfl⟩ : syracuseStep 3978229 = 372959) (by norm_num)
theorem B5304305 : Blo 2095435 5304305 := bstep (se 2 (by rfl) ⟨1989114, by rfl⟩ : syracuseStep 5304305 = 3978229) B3978229
theorem B3536203 : Blo 2095435 3536203 := bstep (se 1 (by rfl) ⟨2652152, by rfl⟩ : syracuseStep 3536203 = 5304305) B5304305
theorem B4714937 : Blo 2095435 4714937 := bstep (se 2 (by rfl) ⟨1768101, by rfl⟩ : syracuseStep 4714937 = 3536203) B3536203
theorem B3143291 : Blo 2095435 3143291 := bstep (se 1 (by rfl) ⟨2357468, by rfl⟩ : syracuseStep 3143291 = 4714937) B4714937
theorem B2095527 : Blo 2095435 2095527 := bstep (se 1 (by rfl) ⟨1571645, by rfl⟩ : syracuseStep 2095527 = 3143291) B3143291
theorem B2357473 : Blo 2095435 2357473 := bbase (se 2 (by rfl) ⟨884052, by rfl⟩ : syracuseStep 2357473 = 1768105) (by norm_num)
theorem B3143297 : Blo 2095435 3143297 := bstep (se 2 (by rfl) ⟨1178736, by rfl⟩ : syracuseStep 3143297 = 2357473) B2357473
theorem B2095531 : Blo 2095435 2095531 := bstep (se 1 (by rfl) ⟨1571648, by rfl⟩ : syracuseStep 2095531 = 3143297) B3143297
theorem B5304325 : Blo 2095435 5304325 := bbase (se 4 (by rfl) ⟨497280, by rfl⟩ : syracuseStep 5304325 = 994561) (by norm_num)
theorem B7072433 : Blo 2095435 7072433 := bstep (se 2 (by rfl) ⟨2652162, by rfl⟩ : syracuseStep 7072433 = 5304325) B5304325
theorem B4714955 : Blo 2095435 4714955 := bstep (se 1 (by rfl) ⟨3536216, by rfl⟩ : syracuseStep 4714955 = 7072433) B7072433
theorem B3143303 : Blo 2095435 3143303 := bstep (se 1 (by rfl) ⟨2357477, by rfl⟩ : syracuseStep 3143303 = 4714955) B4714955
theorem B2095535 : Blo 2095435 2095535 := bstep (se 1 (by rfl) ⟨1571651, by rfl⟩ : syracuseStep 2095535 = 3143303) B3143303
theorem B3143309 : Blo 2095435 3143309 := bbase (se 3 (by rfl) ⟨589370, by rfl⟩ : syracuseStep 3143309 = 1178741) (by norm_num)
theorem B2095539 : Blo 2095435 2095539 := bstep (se 1 (by rfl) ⟨1571654, by rfl⟩ : syracuseStep 2095539 = 3143309) B3143309
theorem B4714973 : Blo 2095435 4714973 := bbase (se 3 (by rfl) ⟨884057, by rfl⟩ : syracuseStep 4714973 = 1768115) (by norm_num)
theorem B3143315 : Blo 2095435 3143315 := bstep (se 1 (by rfl) ⟨2357486, by rfl⟩ : syracuseStep 3143315 = 4714973) B4714973
theorem B2095543 : Blo 2095435 2095543 := bstep (se 1 (by rfl) ⟨1571657, by rfl⟩ : syracuseStep 2095543 = 3143315) B3143315
theorem B3536237 : Blo 2095435 3536237 := bbase (se 3 (by rfl) ⟨663044, by rfl⟩ : syracuseStep 3536237 = 1326089) (by norm_num)
theorem B2357491 : Blo 2095435 2357491 := bstep (se 1 (by rfl) ⟨1768118, by rfl⟩ : syracuseStep 2357491 = 3536237) B3536237
theorem B3143321 : Blo 2095435 3143321 := bstep (se 2 (by rfl) ⟨1178745, by rfl⟩ : syracuseStep 3143321 = 2357491) B2357491
theorem B2095547 : Blo 2095435 2095547 := bstep (se 1 (by rfl) ⟨1571660, by rfl⟩ : syracuseStep 2095547 = 3143321) B3143321
theorem B10207397 : Blo 2095435 10207397 := bbase (se 4 (by rfl) ⟨956943, by rfl⟩ : syracuseStep 10207397 = 1913887) (by norm_num)
theorem B27219725 : Blo 2095435 27219725 := bstep (se 3 (by rfl) ⟨5103698, by rfl⟩ : syracuseStep 27219725 = 10207397) B10207397
theorem B18146483 : Blo 2095435 18146483 := bstep (se 1 (by rfl) ⟨13609862, by rfl⟩ : syracuseStep 18146483 = 27219725) B27219725
theorem B12097655 : Blo 2095435 12097655 := bstep (se 1 (by rfl) ⟨9073241, by rfl⟩ : syracuseStep 12097655 = 18146483) B18146483
theorem B8065103 : Blo 2095435 8065103 := bstep (se 1 (by rfl) ⟨6048827, by rfl⟩ : syracuseStep 8065103 = 12097655) B12097655
theorem B21506941 : Blo 2095435 21506941 := bstep (se 3 (by rfl) ⟨4032551, by rfl⟩ : syracuseStep 21506941 = 8065103) B8065103
theorem B114703685 : Blo 2095435 114703685 := bstep (se 4 (by rfl) ⟨10753470, by rfl⟩ : syracuseStep 114703685 = 21506941) B21506941
theorem B76469123 : Blo 2095435 76469123 := bstep (se 1 (by rfl) ⟨57351842, by rfl⟩ : syracuseStep 76469123 = 114703685) B114703685
theorem B50979415 : Blo 2095435 50979415 := bstep (se 1 (by rfl) ⟨38234561, by rfl⟩ : syracuseStep 50979415 = 76469123) B76469123
theorem B67972553 : Blo 2095435 67972553 := bstep (se 2 (by rfl) ⟨25489707, by rfl⟩ : syracuseStep 67972553 = 50979415) B50979415
theorem B45315035 : Blo 2095435 45315035 := bstep (se 1 (by rfl) ⟨33986276, by rfl⟩ : syracuseStep 45315035 = 67972553) B67972553
theorem B30210023 : Blo 2095435 30210023 := bstep (se 1 (by rfl) ⟨22657517, by rfl⟩ : syracuseStep 30210023 = 45315035) B45315035
theorem B20140015 : Blo 2095435 20140015 := bstep (se 1 (by rfl) ⟨15105011, by rfl⟩ : syracuseStep 20140015 = 30210023) B30210023
theorem B26853353 : Blo 2095435 26853353 := bstep (se 2 (by rfl) ⟨10070007, by rfl⟩ : syracuseStep 26853353 = 20140015) B20140015
theorem B17902235 : Blo 2095435 17902235 := bstep (se 1 (by rfl) ⟨13426676, by rfl⟩ : syracuseStep 17902235 = 26853353) B26853353
theorem B11934823 : Blo 2095435 11934823 := bstep (se 1 (by rfl) ⟨8951117, by rfl⟩ : syracuseStep 11934823 = 17902235) B17902235
theorem B15913097 : Blo 2095435 15913097 := bstep (se 2 (by rfl) ⟨5967411, by rfl⟩ : syracuseStep 15913097 = 11934823) B11934823
theorem B10608731 : Blo 2095435 10608731 := bstep (se 1 (by rfl) ⟨7956548, by rfl⟩ : syracuseStep 10608731 = 15913097) B15913097
theorem B7072487 : Blo 2095435 7072487 := bstep (se 1 (by rfl) ⟨5304365, by rfl⟩ : syracuseStep 7072487 = 10608731) B10608731
theorem B4714991 : Blo 2095435 4714991 := bstep (se 1 (by rfl) ⟨3536243, by rfl⟩ : syracuseStep 4714991 = 7072487) B7072487
theorem B3143327 : Blo 2095435 3143327 := bstep (se 1 (by rfl) ⟨2357495, by rfl⟩ : syracuseStep 3143327 = 4714991) B4714991
theorem B2095551 : Blo 2095435 2095551 := bstep (se 1 (by rfl) ⟨1571663, by rfl⟩ : syracuseStep 2095551 = 3143327) B3143327
theorem B3143333 : Blo 2095435 3143333 := bbase (se 4 (by rfl) ⟨294687, by rfl⟩ : syracuseStep 3143333 = 589375) (by norm_num)
theorem B2095555 : Blo 2095435 2095555 := bstep (se 1 (by rfl) ⟨1571666, by rfl⟩ : syracuseStep 2095555 = 3143333) B3143333
theorem B2652193 : Blo 2095435 2652193 := bbase (se 2 (by rfl) ⟨994572, by rfl⟩ : syracuseStep 2652193 = 1989145) (by norm_num)
theorem B3536257 : Blo 2095435 3536257 := bstep (se 2 (by rfl) ⟨1326096, by rfl⟩ : syracuseStep 3536257 = 2652193) B2652193
theorem B4715009 : Blo 2095435 4715009 := bstep (se 2 (by rfl) ⟨1768128, by rfl⟩ : syracuseStep 4715009 = 3536257) B3536257
theorem B3143339 : Blo 2095435 3143339 := bstep (se 1 (by rfl) ⟨2357504, by rfl⟩ : syracuseStep 3143339 = 4715009) B4715009
theorem B2095559 : Blo 2095435 2095559 := bstep (se 1 (by rfl) ⟨1571669, by rfl⟩ : syracuseStep 2095559 = 3143339) B3143339
theorem B2357509 : Blo 2095435 2357509 := bbase (se 4 (by rfl) ⟨221016, by rfl⟩ : syracuseStep 2357509 = 442033) (by norm_num)
theorem B3143345 : Blo 2095435 3143345 := bstep (se 2 (by rfl) ⟨1178754, by rfl⟩ : syracuseStep 3143345 = 2357509) B2357509
theorem B2095563 : Blo 2095435 2095563 := bstep (se 1 (by rfl) ⟨1571672, by rfl⟩ : syracuseStep 2095563 = 3143345) B3143345
theorem B2237797 : Blo 2095435 2237797 := bbase (se 4 (by rfl) ⟨209793, by rfl⟩ : syracuseStep 2237797 = 419587) (by norm_num)
theorem B2983729 : Blo 2095435 2983729 := bstep (se 2 (by rfl) ⟨1118898, by rfl⟩ : syracuseStep 2983729 = 2237797) B2237797
theorem B3978305 : Blo 2095435 3978305 := bstep (se 2 (by rfl) ⟨1491864, by rfl⟩ : syracuseStep 3978305 = 2983729) B2983729
theorem B2652203 : Blo 2095435 2652203 := bstep (se 1 (by rfl) ⟨1989152, by rfl⟩ : syracuseStep 2652203 = 3978305) B3978305
theorem B7072541 : Blo 2095435 7072541 := bstep (se 3 (by rfl) ⟨1326101, by rfl⟩ : syracuseStep 7072541 = 2652203) B2652203
theorem B4715027 : Blo 2095435 4715027 := bstep (se 1 (by rfl) ⟨3536270, by rfl⟩ : syracuseStep 4715027 = 7072541) B7072541
theorem B3143351 : Blo 2095435 3143351 := bstep (se 1 (by rfl) ⟨2357513, by rfl⟩ : syracuseStep 3143351 = 4715027) B4715027
theorem B2095567 : Blo 2095435 2095567 := bstep (se 1 (by rfl) ⟨1571675, by rfl⟩ : syracuseStep 2095567 = 3143351) B3143351
theorem B3143357 : Blo 2095435 3143357 := bbase (se 3 (by rfl) ⟨589379, by rfl⟩ : syracuseStep 3143357 = 1178759) (by norm_num)
theorem B2095571 : Blo 2095435 2095571 := bstep (se 1 (by rfl) ⟨1571678, by rfl⟩ : syracuseStep 2095571 = 3143357) B3143357
theorem B4715045 : Blo 2095435 4715045 := bbase (se 4 (by rfl) ⟨442035, by rfl⟩ : syracuseStep 4715045 = 884071) (by norm_num)
theorem B3143363 : Blo 2095435 3143363 := bstep (se 1 (by rfl) ⟨2357522, by rfl⟩ : syracuseStep 3143363 = 4715045) B4715045
theorem B2095575 : Blo 2095435 2095575 := bstep (se 1 (by rfl) ⟨1571681, by rfl⟩ : syracuseStep 2095575 = 3143363) B3143363
theorem B5304437 : Blo 2095435 5304437 := bbase (se 5 (by rfl) ⟨248645, by rfl⟩ : syracuseStep 5304437 = 497291) (by norm_num)
theorem B3536291 : Blo 2095435 3536291 := bstep (se 1 (by rfl) ⟨2652218, by rfl⟩ : syracuseStep 3536291 = 5304437) B5304437
theorem B2357527 : Blo 2095435 2357527 := bstep (se 1 (by rfl) ⟨1768145, by rfl⟩ : syracuseStep 2357527 = 3536291) B3536291
theorem B3143369 : Blo 2095435 3143369 := bstep (se 2 (by rfl) ⟨1178763, by rfl⟩ : syracuseStep 3143369 = 2357527) B2357527
theorem B2095579 : Blo 2095435 2095579 := bstep (se 1 (by rfl) ⟨1571684, by rfl⟩ : syracuseStep 2095579 = 3143369) B3143369
theorem B7169093 : Blo 2095435 7169093 := bbase (se 4 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 7169093 = 1344205) (by norm_num)
theorem B4779395 : Blo 2095435 4779395 := bstep (se 1 (by rfl) ⟨3584546, by rfl⟩ : syracuseStep 4779395 = 7169093) B7169093
theorem B3186263 : Blo 2095435 3186263 := bstep (se 1 (by rfl) ⟨2389697, by rfl⟩ : syracuseStep 3186263 = 4779395) B4779395
theorem B8496701 : Blo 2095435 8496701 := bstep (se 3 (by rfl) ⟨1593131, by rfl⟩ : syracuseStep 8496701 = 3186263) B3186263
theorem B5664467 : Blo 2095435 5664467 := bstep (se 1 (by rfl) ⟨4248350, by rfl⟩ : syracuseStep 5664467 = 8496701) B8496701
theorem B3776311 : Blo 2095435 3776311 := bstep (se 1 (by rfl) ⟨2832233, by rfl⟩ : syracuseStep 3776311 = 5664467) B5664467
theorem B20140325 : Blo 2095435 20140325 := bstep (se 4 (by rfl) ⟨1888155, by rfl⟩ : syracuseStep 20140325 = 3776311) B3776311
theorem B13426883 : Blo 2095435 13426883 := bstep (se 1 (by rfl) ⟨10070162, by rfl⟩ : syracuseStep 13426883 = 20140325) B20140325
theorem B8951255 : Blo 2095435 8951255 := bstep (se 1 (by rfl) ⟨6713441, by rfl⟩ : syracuseStep 8951255 = 13426883) B13426883
theorem B5967503 : Blo 2095435 5967503 := bstep (se 1 (by rfl) ⟨4475627, by rfl⟩ : syracuseStep 5967503 = 8951255) B8951255
theorem B3978335 : Blo 2095435 3978335 := bstep (se 1 (by rfl) ⟨2983751, by rfl⟩ : syracuseStep 3978335 = 5967503) B5967503
theorem B10608893 : Blo 2095435 10608893 := bstep (se 3 (by rfl) ⟨1989167, by rfl⟩ : syracuseStep 10608893 = 3978335) B3978335
theorem B7072595 : Blo 2095435 7072595 := bstep (se 1 (by rfl) ⟨5304446, by rfl⟩ : syracuseStep 7072595 = 10608893) B10608893
theorem B4715063 : Blo 2095435 4715063 := bstep (se 1 (by rfl) ⟨3536297, by rfl⟩ : syracuseStep 4715063 = 7072595) B7072595
theorem B3143375 : Blo 2095435 3143375 := bstep (se 1 (by rfl) ⟨2357531, by rfl⟩ : syracuseStep 3143375 = 4715063) B4715063
theorem B2095583 : Blo 2095435 2095583 := bstep (se 1 (by rfl) ⟨1571687, by rfl⟩ : syracuseStep 2095583 = 3143375) B3143375
theorem B3143381 : Blo 2095435 3143381 := bbase (se 7 (by rfl) ⟨36836, by rfl⟩ : syracuseStep 3143381 = 73673) (by norm_num)
theorem B2095587 : Blo 2095435 2095587 := bstep (se 1 (by rfl) ⟨1571690, by rfl⟩ : syracuseStep 2095587 = 3143381) B3143381
theorem B4475645 : Blo 2095435 4475645 := bbase (se 3 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 4475645 = 1678367) (by norm_num)
theorem B2983763 : Blo 2095435 2983763 := bstep (se 1 (by rfl) ⟨2237822, by rfl⟩ : syracuseStep 2983763 = 4475645) B4475645
theorem B7956701 : Blo 2095435 7956701 := bstep (se 3 (by rfl) ⟨1491881, by rfl⟩ : syracuseStep 7956701 = 2983763) B2983763
theorem B5304467 : Blo 2095435 5304467 := bstep (se 1 (by rfl) ⟨3978350, by rfl⟩ : syracuseStep 5304467 = 7956701) B7956701
theorem B3536311 : Blo 2095435 3536311 := bstep (se 1 (by rfl) ⟨2652233, by rfl⟩ : syracuseStep 3536311 = 5304467) B5304467
theorem B4715081 : Blo 2095435 4715081 := bstep (se 2 (by rfl) ⟨1768155, by rfl⟩ : syracuseStep 4715081 = 3536311) B3536311
theorem B3143387 : Blo 2095435 3143387 := bstep (se 1 (by rfl) ⟨2357540, by rfl⟩ : syracuseStep 3143387 = 4715081) B4715081
theorem B2095591 : Blo 2095435 2095591 := bstep (se 1 (by rfl) ⟨1571693, by rfl⟩ : syracuseStep 2095591 = 3143387) B3143387
theorem B2357545 : Blo 2095435 2357545 := bbase (se 2 (by rfl) ⟨884079, by rfl⟩ : syracuseStep 2357545 = 1768159) (by norm_num)
theorem B3143393 : Blo 2095435 3143393 := bstep (se 2 (by rfl) ⟨1178772, by rfl⟩ : syracuseStep 3143393 = 2357545) B2357545
theorem B2095595 : Blo 2095435 2095595 := bstep (se 1 (by rfl) ⟨1571696, by rfl⟩ : syracuseStep 2095595 = 3143393) B3143393
theorem B2153173 : Blo 2095435 2153173 := bbase (se 7 (by rfl) ⟨25232, by rfl⟩ : syracuseStep 2153173 = 50465) (by norm_num)
theorem B2870897 : Blo 2095435 2870897 := bstep (se 2 (by rfl) ⟨1076586, by rfl⟩ : syracuseStep 2870897 = 2153173) B2153173
theorem B7655725 : Blo 2095435 7655725 := bstep (se 3 (by rfl) ⟨1435448, by rfl⟩ : syracuseStep 7655725 = 2870897) B2870897
theorem B10207633 : Blo 2095435 10207633 := bstep (se 2 (by rfl) ⟨3827862, by rfl⟩ : syracuseStep 10207633 = 7655725) B7655725
theorem B13610177 : Blo 2095435 13610177 := bstep (se 2 (by rfl) ⟨5103816, by rfl⟩ : syracuseStep 13610177 = 10207633) B10207633
theorem B9073451 : Blo 2095435 9073451 := bstep (se 1 (by rfl) ⟨6805088, by rfl⟩ : syracuseStep 9073451 = 13610177) B13610177
theorem B6048967 : Blo 2095435 6048967 := bstep (se 1 (by rfl) ⟨4536725, by rfl⟩ : syracuseStep 6048967 = 9073451) B9073451
theorem B8065289 : Blo 2095435 8065289 := bstep (se 2 (by rfl) ⟨3024483, by rfl⟩ : syracuseStep 8065289 = 6048967) B6048967
theorem B21507437 : Blo 2095435 21507437 := bstep (se 3 (by rfl) ⟨4032644, by rfl⟩ : syracuseStep 21507437 = 8065289) B8065289
theorem B14338291 : Blo 2095435 14338291 := bstep (se 1 (by rfl) ⟨10753718, by rfl⟩ : syracuseStep 14338291 = 21507437) B21507437
theorem B19117721 : Blo 2095435 19117721 := bstep (se 2 (by rfl) ⟨7169145, by rfl⟩ : syracuseStep 19117721 = 14338291) B14338291
theorem B50980589 : Blo 2095435 50980589 := bstep (se 3 (by rfl) ⟨9558860, by rfl⟩ : syracuseStep 50980589 = 19117721) B19117721
theorem B33987059 : Blo 2095435 33987059 := bstep (se 1 (by rfl) ⟨25490294, by rfl⟩ : syracuseStep 33987059 = 50980589) B50980589
theorem B22658039 : Blo 2095435 22658039 := bstep (se 1 (by rfl) ⟨16993529, by rfl⟩ : syracuseStep 22658039 = 33987059) B33987059
theorem B15105359 : Blo 2095435 15105359 := bstep (se 1 (by rfl) ⟨11329019, by rfl⟩ : syracuseStep 15105359 = 22658039) B22658039
theorem B10070239 : Blo 2095435 10070239 := bstep (se 1 (by rfl) ⟨7552679, by rfl⟩ : syracuseStep 10070239 = 15105359) B15105359
theorem B13426985 : Blo 2095435 13426985 := bstep (se 2 (by rfl) ⟨5035119, by rfl⟩ : syracuseStep 13426985 = 10070239) B10070239
theorem B8951323 : Blo 2095435 8951323 := bstep (se 1 (by rfl) ⟨6713492, by rfl⟩ : syracuseStep 8951323 = 13426985) B13426985
theorem B11935097 : Blo 2095435 11935097 := bstep (se 2 (by rfl) ⟨4475661, by rfl⟩ : syracuseStep 11935097 = 8951323) B8951323
theorem B7956731 : Blo 2095435 7956731 := bstep (se 1 (by rfl) ⟨5967548, by rfl⟩ : syracuseStep 7956731 = 11935097) B11935097
theorem B5304487 : Blo 2095435 5304487 := bstep (se 1 (by rfl) ⟨3978365, by rfl⟩ : syracuseStep 5304487 = 7956731) B7956731
theorem B7072649 : Blo 2095435 7072649 := bstep (se 2 (by rfl) ⟨2652243, by rfl⟩ : syracuseStep 7072649 = 5304487) B5304487
theorem B4715099 : Blo 2095435 4715099 := bstep (se 1 (by rfl) ⟨3536324, by rfl⟩ : syracuseStep 4715099 = 7072649) B7072649
theorem B3143399 : Blo 2095435 3143399 := bstep (se 1 (by rfl) ⟨2357549, by rfl⟩ : syracuseStep 3143399 = 4715099) B4715099
theorem B2095599 : Blo 2095435 2095599 := bstep (se 1 (by rfl) ⟨1571699, by rfl⟩ : syracuseStep 2095599 = 3143399) B3143399
theorem B3143405 : Blo 2095435 3143405 := bbase (se 3 (by rfl) ⟨589388, by rfl⟩ : syracuseStep 3143405 = 1178777) (by norm_num)
theorem B2095603 : Blo 2095435 2095603 := bstep (se 1 (by rfl) ⟨1571702, by rfl⟩ : syracuseStep 2095603 = 3143405) B3143405
theorem B4715117 : Blo 2095435 4715117 := bbase (se 3 (by rfl) ⟨884084, by rfl⟩ : syracuseStep 4715117 = 1768169) (by norm_num)
theorem B3143411 : Blo 2095435 3143411 := bstep (se 1 (by rfl) ⟨2357558, by rfl⟩ : syracuseStep 3143411 = 4715117) B4715117
theorem B2095607 : Blo 2095435 2095607 := bstep (se 1 (by rfl) ⟨1571705, by rfl⟩ : syracuseStep 2095607 = 3143411) B3143411
theorem B3978389 : Blo 2095435 3978389 := bbase (se 6 (by rfl) ⟨93243, by rfl⟩ : syracuseStep 3978389 = 186487) (by norm_num)
theorem B2652259 : Blo 2095435 2652259 := bstep (se 1 (by rfl) ⟨1989194, by rfl⟩ : syracuseStep 2652259 = 3978389) B3978389
theorem B3536345 : Blo 2095435 3536345 := bstep (se 2 (by rfl) ⟨1326129, by rfl⟩ : syracuseStep 3536345 = 2652259) B2652259
theorem B2357563 : Blo 2095435 2357563 := bstep (se 1 (by rfl) ⟨1768172, by rfl⟩ : syracuseStep 2357563 = 3536345) B3536345
theorem B3143417 : Blo 2095435 3143417 := bstep (se 2 (by rfl) ⟨1178781, by rfl⟩ : syracuseStep 3143417 = 2357563) B2357563
theorem B2095611 : Blo 2095435 2095611 := bstep (se 1 (by rfl) ⟨1571708, by rfl⟩ : syracuseStep 2095611 = 3143417) B3143417
theorem B2389733 : Blo 2095435 2389733 := bbase (se 4 (by rfl) ⟨224037, by rfl⟩ : syracuseStep 2389733 = 448075) (by norm_num)
theorem B25490485 : Blo 2095435 25490485 := bstep (se 5 (by rfl) ⟨1194866, by rfl⟩ : syracuseStep 25490485 = 2389733) B2389733
theorem B33987313 : Blo 2095435 33987313 := bstep (se 2 (by rfl) ⟨12745242, by rfl⟩ : syracuseStep 33987313 = 25490485) B25490485
theorem B45316417 : Blo 2095435 45316417 := bstep (se 2 (by rfl) ⟨16993656, by rfl⟩ : syracuseStep 45316417 = 33987313) B33987313
theorem B60421889 : Blo 2095435 60421889 := bstep (se 2 (by rfl) ⟨22658208, by rfl⟩ : syracuseStep 60421889 = 45316417) B45316417
theorem B40281259 : Blo 2095435 40281259 := bstep (se 1 (by rfl) ⟨30210944, by rfl⟩ : syracuseStep 40281259 = 60421889) B60421889
theorem B53708345 : Blo 2095435 53708345 := bstep (se 2 (by rfl) ⟨20140629, by rfl⟩ : syracuseStep 53708345 = 40281259) B40281259
theorem B35805563 : Blo 2095435 35805563 := bstep (se 1 (by rfl) ⟨26854172, by rfl⟩ : syracuseStep 35805563 = 53708345) B53708345
theorem B23870375 : Blo 2095435 23870375 := bstep (se 1 (by rfl) ⟨17902781, by rfl⟩ : syracuseStep 23870375 = 35805563) B35805563
theorem B15913583 : Blo 2095435 15913583 := bstep (se 1 (by rfl) ⟨11935187, by rfl⟩ : syracuseStep 15913583 = 23870375) B23870375
theorem B10609055 : Blo 2095435 10609055 := bstep (se 1 (by rfl) ⟨7956791, by rfl⟩ : syracuseStep 10609055 = 15913583) B15913583
theorem B7072703 : Blo 2095435 7072703 := bstep (se 1 (by rfl) ⟨5304527, by rfl⟩ : syracuseStep 7072703 = 10609055) B10609055
theorem B4715135 : Blo 2095435 4715135 := bstep (se 1 (by rfl) ⟨3536351, by rfl⟩ : syracuseStep 4715135 = 7072703) B7072703
theorem B3143423 : Blo 2095435 3143423 := bstep (se 1 (by rfl) ⟨2357567, by rfl⟩ : syracuseStep 3143423 = 4715135) B4715135
theorem B2095615 : Blo 2095435 2095615 := bstep (se 1 (by rfl) ⟨1571711, by rfl⟩ : syracuseStep 2095615 = 3143423) B3143423
theorem B3143429 : Blo 2095435 3143429 := bbase (se 4 (by rfl) ⟨294696, by rfl⟩ : syracuseStep 3143429 = 589393) (by norm_num)
theorem B2095619 : Blo 2095435 2095619 := bstep (se 1 (by rfl) ⟨1571714, by rfl⟩ : syracuseStep 2095619 = 3143429) B3143429
theorem B3536365 : Blo 2095435 3536365 := bbase (se 3 (by rfl) ⟨663068, by rfl⟩ : syracuseStep 3536365 = 1326137) (by norm_num)
theorem B4715153 : Blo 2095435 4715153 := bstep (se 2 (by rfl) ⟨1768182, by rfl⟩ : syracuseStep 4715153 = 3536365) B3536365
theorem B3143435 : Blo 2095435 3143435 := bstep (se 1 (by rfl) ⟨2357576, by rfl⟩ : syracuseStep 3143435 = 4715153) B4715153
theorem B2095623 : Blo 2095435 2095623 := bstep (se 1 (by rfl) ⟨1571717, by rfl⟩ : syracuseStep 2095623 = 3143435) B3143435
theorem B2357581 : Blo 2095435 2357581 := bbase (se 3 (by rfl) ⟨442046, by rfl⟩ : syracuseStep 2357581 = 884093) (by norm_num)
theorem B3143441 : Blo 2095435 3143441 := bstep (se 2 (by rfl) ⟨1178790, by rfl⟩ : syracuseStep 3143441 = 2357581) B2357581
theorem B2095627 : Blo 2095435 2095627 := bstep (se 1 (by rfl) ⟨1571720, by rfl⟩ : syracuseStep 2095627 = 3143441) B3143441
theorem B7072757 : Blo 2095435 7072757 := bbase (se 5 (by rfl) ⟨331535, by rfl⟩ : syracuseStep 7072757 = 663071) (by norm_num)
theorem B4715171 : Blo 2095435 4715171 := bstep (se 1 (by rfl) ⟨3536378, by rfl⟩ : syracuseStep 4715171 = 7072757) B7072757
theorem B3143447 : Blo 2095435 3143447 := bstep (se 1 (by rfl) ⟨2357585, by rfl⟩ : syracuseStep 3143447 = 4715171) B4715171
theorem B2095631 : Blo 2095435 2095631 := bstep (se 1 (by rfl) ⟨1571723, by rfl⟩ : syracuseStep 2095631 = 3143447) B3143447
theorem B3143453 : Blo 2095435 3143453 := bbase (se 3 (by rfl) ⟨589397, by rfl⟩ : syracuseStep 3143453 = 1178795) (by norm_num)
theorem B2095635 : Blo 2095435 2095635 := bstep (se 1 (by rfl) ⟨1571726, by rfl⟩ : syracuseStep 2095635 = 3143453) B3143453
theorem B4715189 : Blo 2095435 4715189 := bbase (se 5 (by rfl) ⟨221024, by rfl⟩ : syracuseStep 4715189 = 442049) (by norm_num)
theorem B3143459 : Blo 2095435 3143459 := bstep (se 1 (by rfl) ⟨2357594, by rfl⟩ : syracuseStep 3143459 = 4715189) B4715189
theorem B2095639 : Blo 2095435 2095639 := bstep (se 1 (by rfl) ⟨1571729, by rfl⟩ : syracuseStep 2095639 = 3143459) B3143459
theorem B11935349 : Blo 2095435 11935349 := bbase (se 5 (by rfl) ⟨559469, by rfl⟩ : syracuseStep 11935349 = 1118939) (by norm_num)
theorem B7956899 : Blo 2095435 7956899 := bstep (se 1 (by rfl) ⟨5967674, by rfl⟩ : syracuseStep 7956899 = 11935349) B11935349
theorem B5304599 : Blo 2095435 5304599 := bstep (se 1 (by rfl) ⟨3978449, by rfl⟩ : syracuseStep 5304599 = 7956899) B7956899
theorem B3536399 : Blo 2095435 3536399 := bstep (se 1 (by rfl) ⟨2652299, by rfl⟩ : syracuseStep 3536399 = 5304599) B5304599
theorem B2357599 : Blo 2095435 2357599 := bstep (se 1 (by rfl) ⟨1768199, by rfl⟩ : syracuseStep 2357599 = 3536399) B3536399
theorem B3143465 : Blo 2095435 3143465 := bstep (se 2 (by rfl) ⟨1178799, by rfl⟩ : syracuseStep 3143465 = 2357599) B2357599
theorem B2095643 : Blo 2095435 2095643 := bstep (se 1 (by rfl) ⟨1571732, by rfl⟩ : syracuseStep 2095643 = 3143465) B3143465
theorem B5967685 : Blo 2095435 5967685 := bbase (se 4 (by rfl) ⟨559470, by rfl⟩ : syracuseStep 5967685 = 1118941) (by norm_num)
theorem B7956913 : Blo 2095435 7956913 := bstep (se 2 (by rfl) ⟨2983842, by rfl⟩ : syracuseStep 7956913 = 5967685) B5967685
theorem B10609217 : Blo 2095435 10609217 := bstep (se 2 (by rfl) ⟨3978456, by rfl⟩ : syracuseStep 10609217 = 7956913) B7956913
theorem B7072811 : Blo 2095435 7072811 := bstep (se 1 (by rfl) ⟨5304608, by rfl⟩ : syracuseStep 7072811 = 10609217) B10609217
theorem B4715207 : Blo 2095435 4715207 := bstep (se 1 (by rfl) ⟨3536405, by rfl⟩ : syracuseStep 4715207 = 7072811) B7072811
theorem B3143471 : Blo 2095435 3143471 := bstep (se 1 (by rfl) ⟨2357603, by rfl⟩ : syracuseStep 3143471 = 4715207) B4715207
theorem B2095647 : Blo 2095435 2095647 := bstep (se 1 (by rfl) ⟨1571735, by rfl⟩ : syracuseStep 2095647 = 3143471) B3143471
theorem B3143477 : Blo 2095435 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B2095651 : Blo 2095435 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B5304629 : Blo 2095435 5304629 := bbase (se 5 (by rfl) ⟨248654, by rfl⟩ : syracuseStep 5304629 = 497309) (by norm_num)
theorem B3536419 : Blo 2095435 3536419 := bstep (se 1 (by rfl) ⟨2652314, by rfl⟩ : syracuseStep 3536419 = 5304629) B5304629
theorem B4715225 : Blo 2095435 4715225 := bstep (se 2 (by rfl) ⟨1768209, by rfl⟩ : syracuseStep 4715225 = 3536419) B3536419
theorem B3143483 : Blo 2095435 3143483 := bstep (se 1 (by rfl) ⟨2357612, by rfl⟩ : syracuseStep 3143483 = 4715225) B4715225
theorem B2095655 : Blo 2095435 2095655 := bstep (se 1 (by rfl) ⟨1571741, by rfl⟩ : syracuseStep 2095655 = 3143483) B3143483
theorem B2357617 : Blo 2095435 2357617 := bbase (se 2 (by rfl) ⟨884106, by rfl⟩ : syracuseStep 2357617 = 1768213) (by norm_num)
theorem B3143489 : Blo 2095435 3143489 := bstep (se 2 (by rfl) ⟨1178808, by rfl⟩ : syracuseStep 3143489 = 2357617) B2357617
theorem B2095659 : Blo 2095435 2095659 := bstep (se 1 (by rfl) ⟨1571744, by rfl⟩ : syracuseStep 2095659 = 3143489) B3143489
theorem B2517637 : Blo 2095435 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B3356849 : Blo 2095435 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B8951597 : Blo 2095435 8951597 := bstep (se 3 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 8951597 = 3356849) B3356849
theorem B5967731 : Blo 2095435 5967731 := bstep (se 1 (by rfl) ⟨4475798, by rfl⟩ : syracuseStep 5967731 = 8951597) B8951597
theorem B3978487 : Blo 2095435 3978487 := bstep (se 1 (by rfl) ⟨2983865, by rfl⟩ : syracuseStep 3978487 = 5967731) B5967731
theorem B5304649 : Blo 2095435 5304649 := bstep (se 2 (by rfl) ⟨1989243, by rfl⟩ : syracuseStep 5304649 = 3978487) B3978487
theorem B7072865 : Blo 2095435 7072865 := bstep (se 2 (by rfl) ⟨2652324, by rfl⟩ : syracuseStep 7072865 = 5304649) B5304649
theorem B4715243 : Blo 2095435 4715243 := bstep (se 1 (by rfl) ⟨3536432, by rfl⟩ : syracuseStep 4715243 = 7072865) B7072865
theorem B3143495 : Blo 2095435 3143495 := bstep (se 1 (by rfl) ⟨2357621, by rfl⟩ : syracuseStep 3143495 = 4715243) B4715243
theorem B2095663 : Blo 2095435 2095663 := bstep (se 1 (by rfl) ⟨1571747, by rfl⟩ : syracuseStep 2095663 = 3143495) B3143495
theorem B3143501 : Blo 2095435 3143501 := bbase (se 3 (by rfl) ⟨589406, by rfl⟩ : syracuseStep 3143501 = 1178813) (by norm_num)
theorem B2095667 : Blo 2095435 2095667 := bstep (se 1 (by rfl) ⟨1571750, by rfl⟩ : syracuseStep 2095667 = 3143501) B3143501
theorem B4715261 : Blo 2095435 4715261 := bbase (se 3 (by rfl) ⟨884111, by rfl⟩ : syracuseStep 4715261 = 1768223) (by norm_num)
theorem B3143507 : Blo 2095435 3143507 := bstep (se 1 (by rfl) ⟨2357630, by rfl⟩ : syracuseStep 3143507 = 4715261) B4715261
theorem B2095671 : Blo 2095435 2095671 := bstep (se 1 (by rfl) ⟨1571753, by rfl⟩ : syracuseStep 2095671 = 3143507) B3143507
theorem B3536453 : Blo 2095435 3536453 := bbase (se 4 (by rfl) ⟨331542, by rfl⟩ : syracuseStep 3536453 = 663085) (by norm_num)
theorem B2357635 : Blo 2095435 2357635 := bstep (se 1 (by rfl) ⟨1768226, by rfl⟩ : syracuseStep 2357635 = 3536453) B3536453
theorem B3143513 : Blo 2095435 3143513 := bstep (se 2 (by rfl) ⟨1178817, by rfl⟩ : syracuseStep 3143513 = 2357635) B2357635
theorem B2095675 : Blo 2095435 2095675 := bstep (se 1 (by rfl) ⟨1571756, by rfl⟩ : syracuseStep 2095675 = 3143513) B3143513
theorem B15914069 : Blo 2095435 15914069 := bbase (se 8 (by rfl) ⟨93246, by rfl⟩ : syracuseStep 15914069 = 186493) (by norm_num)
theorem B10609379 : Blo 2095435 10609379 := bstep (se 1 (by rfl) ⟨7957034, by rfl⟩ : syracuseStep 10609379 = 15914069) B15914069
theorem B7072919 : Blo 2095435 7072919 := bstep (se 1 (by rfl) ⟨5304689, by rfl⟩ : syracuseStep 7072919 = 10609379) B10609379
theorem B4715279 : Blo 2095435 4715279 := bstep (se 1 (by rfl) ⟨3536459, by rfl⟩ : syracuseStep 4715279 = 7072919) B7072919
theorem B3143519 : Blo 2095435 3143519 := bstep (se 1 (by rfl) ⟨2357639, by rfl⟩ : syracuseStep 3143519 = 4715279) B4715279
theorem B2095679 : Blo 2095435 2095679 := bstep (se 1 (by rfl) ⟨1571759, by rfl⟩ : syracuseStep 2095679 = 3143519) B3143519
theorem B3143525 : Blo 2095435 3143525 := bbase (se 4 (by rfl) ⟨294705, by rfl⟩ : syracuseStep 3143525 = 589411) (by norm_num)
theorem B2095683 : Blo 2095435 2095683 := bstep (se 1 (by rfl) ⟨1571762, by rfl⟩ : syracuseStep 2095683 = 3143525) B3143525
theorem B3978533 : Blo 2095435 3978533 := bbase (se 4 (by rfl) ⟨372987, by rfl⟩ : syracuseStep 3978533 = 745975) (by norm_num)
theorem B2652355 : Blo 2095435 2652355 := bstep (se 1 (by rfl) ⟨1989266, by rfl⟩ : syracuseStep 2652355 = 3978533) B3978533
theorem B3536473 : Blo 2095435 3536473 := bstep (se 2 (by rfl) ⟨1326177, by rfl⟩ : syracuseStep 3536473 = 2652355) B2652355
theorem B4715297 : Blo 2095435 4715297 := bstep (se 2 (by rfl) ⟨1768236, by rfl⟩ : syracuseStep 4715297 = 3536473) B3536473
theorem B3143531 : Blo 2095435 3143531 := bstep (se 1 (by rfl) ⟨2357648, by rfl⟩ : syracuseStep 3143531 = 4715297) B4715297
theorem B2095687 : Blo 2095435 2095687 := bstep (se 1 (by rfl) ⟨1571765, by rfl⟩ : syracuseStep 2095687 = 3143531) B3143531
theorem B2357653 : Blo 2095435 2357653 := bbase (se 6 (by rfl) ⟨55257, by rfl⟩ : syracuseStep 2357653 = 110515) (by norm_num)
theorem B3143537 : Blo 2095435 3143537 := bstep (se 2 (by rfl) ⟨1178826, by rfl⟩ : syracuseStep 3143537 = 2357653) B2357653
theorem B2095691 : Blo 2095435 2095691 := bstep (se 1 (by rfl) ⟨1571768, by rfl⟩ : syracuseStep 2095691 = 3143537) B3143537
theorem B2652365 : Blo 2095435 2652365 := bbase (se 3 (by rfl) ⟨497318, by rfl⟩ : syracuseStep 2652365 = 994637) (by norm_num)
theorem B7072973 : Blo 2095435 7072973 := bstep (se 3 (by rfl) ⟨1326182, by rfl⟩ : syracuseStep 7072973 = 2652365) B2652365
theorem B4715315 : Blo 2095435 4715315 := bstep (se 1 (by rfl) ⟨3536486, by rfl⟩ : syracuseStep 4715315 = 7072973) B7072973
theorem B3143543 : Blo 2095435 3143543 := bstep (se 1 (by rfl) ⟨2357657, by rfl⟩ : syracuseStep 3143543 = 4715315) B4715315
theorem B2095695 : Blo 2095435 2095695 := bstep (se 1 (by rfl) ⟨1571771, by rfl⟩ : syracuseStep 2095695 = 3143543) B3143543
theorem B3143549 : Blo 2095435 3143549 := bbase (se 3 (by rfl) ⟨589415, by rfl⟩ : syracuseStep 3143549 = 1178831) (by norm_num)
theorem B2095699 : Blo 2095435 2095699 := bstep (se 1 (by rfl) ⟨1571774, by rfl⟩ : syracuseStep 2095699 = 3143549) B3143549
theorem B4715333 : Blo 2095435 4715333 := bbase (se 4 (by rfl) ⟨442062, by rfl⟩ : syracuseStep 4715333 = 884125) (by norm_num)
theorem B3143555 : Blo 2095435 3143555 := bstep (se 1 (by rfl) ⟨2357666, by rfl⟩ : syracuseStep 3143555 = 4715333) B4715333
theorem B2095703 : Blo 2095435 2095703 := bstep (se 1 (by rfl) ⟨1571777, by rfl⟩ : syracuseStep 2095703 = 3143555) B3143555
theorem B4475893 : Blo 2095435 4475893 := bbase (se 5 (by rfl) ⟨209807, by rfl⟩ : syracuseStep 4475893 = 419615) (by norm_num)
theorem B5967857 : Blo 2095435 5967857 := bstep (se 2 (by rfl) ⟨2237946, by rfl⟩ : syracuseStep 5967857 = 4475893) B4475893
theorem B3978571 : Blo 2095435 3978571 := bstep (se 1 (by rfl) ⟨2983928, by rfl⟩ : syracuseStep 3978571 = 5967857) B5967857
theorem B5304761 : Blo 2095435 5304761 := bstep (se 2 (by rfl) ⟨1989285, by rfl⟩ : syracuseStep 5304761 = 3978571) B3978571
theorem B3536507 : Blo 2095435 3536507 := bstep (se 1 (by rfl) ⟨2652380, by rfl⟩ : syracuseStep 3536507 = 5304761) B5304761
theorem B2357671 : Blo 2095435 2357671 := bstep (se 1 (by rfl) ⟨1768253, by rfl⟩ : syracuseStep 2357671 = 3536507) B3536507
theorem B3143561 : Blo 2095435 3143561 := bstep (se 2 (by rfl) ⟨1178835, by rfl⟩ : syracuseStep 3143561 = 2357671) B2357671
theorem B2095707 : Blo 2095435 2095707 := bstep (se 1 (by rfl) ⟨1571780, by rfl⟩ : syracuseStep 2095707 = 3143561) B3143561
theorem B10609541 : Blo 2095435 10609541 := bbase (se 4 (by rfl) ⟨994644, by rfl⟩ : syracuseStep 10609541 = 1989289) (by norm_num)
theorem B7073027 : Blo 2095435 7073027 := bstep (se 1 (by rfl) ⟨5304770, by rfl⟩ : syracuseStep 7073027 = 10609541) B10609541
theorem B4715351 : Blo 2095435 4715351 := bstep (se 1 (by rfl) ⟨3536513, by rfl⟩ : syracuseStep 4715351 = 7073027) B7073027
theorem B3143567 : Blo 2095435 3143567 := bstep (se 1 (by rfl) ⟨2357675, by rfl⟩ : syracuseStep 3143567 = 4715351) B4715351
theorem B2095711 : Blo 2095435 2095711 := bstep (se 1 (by rfl) ⟨1571783, by rfl⟩ : syracuseStep 2095711 = 3143567) B3143567
theorem B3143573 : Blo 2095435 3143573 := bbase (se 6 (by rfl) ⟨73677, by rfl⟩ : syracuseStep 3143573 = 147355) (by norm_num)
theorem B2095715 : Blo 2095435 2095715 := bstep (se 1 (by rfl) ⟨1571786, by rfl⟩ : syracuseStep 2095715 = 3143573) B3143573
theorem B3776557 : Blo 2095435 3776557 := bbase (se 3 (by rfl) ⟨708104, by rfl⟩ : syracuseStep 3776557 = 1416209) (by norm_num)
theorem B5035409 : Blo 2095435 5035409 := bstep (se 2 (by rfl) ⟨1888278, by rfl⟩ : syracuseStep 5035409 = 3776557) B3776557
theorem B3356939 : Blo 2095435 3356939 := bstep (se 1 (by rfl) ⟨2517704, by rfl⟩ : syracuseStep 3356939 = 5035409) B5035409
theorem B2237959 : Blo 2095435 2237959 := bstep (se 1 (by rfl) ⟨1678469, by rfl⟩ : syracuseStep 2237959 = 3356939) B3356939
theorem B11935781 : Blo 2095435 11935781 := bstep (se 4 (by rfl) ⟨1118979, by rfl⟩ : syracuseStep 11935781 = 2237959) B2237959
theorem B7957187 : Blo 2095435 7957187 := bstep (se 1 (by rfl) ⟨5967890, by rfl⟩ : syracuseStep 7957187 = 11935781) B11935781
theorem B5304791 : Blo 2095435 5304791 := bstep (se 1 (by rfl) ⟨3978593, by rfl⟩ : syracuseStep 5304791 = 7957187) B7957187
theorem B3536527 : Blo 2095435 3536527 := bstep (se 1 (by rfl) ⟨2652395, by rfl⟩ : syracuseStep 3536527 = 5304791) B5304791
theorem B4715369 : Blo 2095435 4715369 := bstep (se 2 (by rfl) ⟨1768263, by rfl⟩ : syracuseStep 4715369 = 3536527) B3536527
theorem B3143579 : Blo 2095435 3143579 := bstep (se 1 (by rfl) ⟨2357684, by rfl⟩ : syracuseStep 3143579 = 4715369) B4715369
theorem B2095719 : Blo 2095435 2095719 := bstep (se 1 (by rfl) ⟨1571789, by rfl⟩ : syracuseStep 2095719 = 3143579) B3143579
theorem B2357689 : Blo 2095435 2357689 := bbase (se 2 (by rfl) ⟨884133, by rfl⟩ : syracuseStep 2357689 = 1768267) (by norm_num)
theorem B3143585 : Blo 2095435 3143585 := bstep (se 2 (by rfl) ⟨1178844, by rfl⟩ : syracuseStep 3143585 = 2357689) B2357689
theorem B2095723 : Blo 2095435 2095723 := bstep (se 1 (by rfl) ⟨1571792, by rfl⟩ : syracuseStep 2095723 = 3143585) B3143585
theorem B2153305 : Blo 2095435 2153305 := bbase (se 2 (by rfl) ⟨807489, by rfl⟩ : syracuseStep 2153305 = 1614979) (by norm_num)
theorem B2871073 : Blo 2095435 2871073 := bstep (se 2 (by rfl) ⟨1076652, by rfl⟩ : syracuseStep 2871073 = 2153305) B2153305
theorem B3828097 : Blo 2095435 3828097 := bstep (se 2 (by rfl) ⟨1435536, by rfl⟩ : syracuseStep 3828097 = 2871073) B2871073
theorem B5104129 : Blo 2095435 5104129 := bstep (se 2 (by rfl) ⟨1914048, by rfl⟩ : syracuseStep 5104129 = 3828097) B3828097
theorem B6805505 : Blo 2095435 6805505 := bstep (se 2 (by rfl) ⟨2552064, by rfl⟩ : syracuseStep 6805505 = 5104129) B5104129
theorem B4537003 : Blo 2095435 4537003 := bstep (se 1 (by rfl) ⟨3402752, by rfl⟩ : syracuseStep 4537003 = 6805505) B6805505
theorem B6049337 : Blo 2095435 6049337 := bstep (se 2 (by rfl) ⟨2268501, by rfl⟩ : syracuseStep 6049337 = 4537003) B4537003
theorem B16131565 : Blo 2095435 16131565 := bstep (se 3 (by rfl) ⟨3024668, by rfl⟩ : syracuseStep 16131565 = 6049337) B6049337
theorem B21508753 : Blo 2095435 21508753 := bstep (se 2 (by rfl) ⟨8065782, by rfl⟩ : syracuseStep 21508753 = 16131565) B16131565
theorem B28678337 : Blo 2095435 28678337 := bstep (se 2 (by rfl) ⟨10754376, by rfl⟩ : syracuseStep 28678337 = 21508753) B21508753
theorem B19118891 : Blo 2095435 19118891 := bstep (se 1 (by rfl) ⟨14339168, by rfl⟩ : syracuseStep 19118891 = 28678337) B28678337
theorem B12745927 : Blo 2095435 12745927 := bstep (se 1 (by rfl) ⟨9559445, by rfl⟩ : syracuseStep 12745927 = 19118891) B19118891
theorem B16994569 : Blo 2095435 16994569 := bstep (se 2 (by rfl) ⟨6372963, by rfl⟩ : syracuseStep 16994569 = 12745927) B12745927
theorem B22659425 : Blo 2095435 22659425 := bstep (se 2 (by rfl) ⟨8497284, by rfl⟩ : syracuseStep 22659425 = 16994569) B16994569
theorem B15106283 : Blo 2095435 15106283 := bstep (se 1 (by rfl) ⟨11329712, by rfl⟩ : syracuseStep 15106283 = 22659425) B22659425
theorem B10070855 : Blo 2095435 10070855 := bstep (se 1 (by rfl) ⟨7553141, by rfl⟩ : syracuseStep 10070855 = 15106283) B15106283
theorem B6713903 : Blo 2095435 6713903 := bstep (se 1 (by rfl) ⟨5035427, by rfl⟩ : syracuseStep 6713903 = 10070855) B10070855
theorem B4475935 : Blo 2095435 4475935 := bstep (se 1 (by rfl) ⟨3356951, by rfl⟩ : syracuseStep 4475935 = 6713903) B6713903
theorem B5967913 : Blo 2095435 5967913 := bstep (se 2 (by rfl) ⟨2237967, by rfl⟩ : syracuseStep 5967913 = 4475935) B4475935
theorem B7957217 : Blo 2095435 7957217 := bstep (se 2 (by rfl) ⟨2983956, by rfl⟩ : syracuseStep 7957217 = 5967913) B5967913
theorem B5304811 : Blo 2095435 5304811 := bstep (se 1 (by rfl) ⟨3978608, by rfl⟩ : syracuseStep 5304811 = 7957217) B7957217
theorem B7073081 : Blo 2095435 7073081 := bstep (se 2 (by rfl) ⟨2652405, by rfl⟩ : syracuseStep 7073081 = 5304811) B5304811
theorem B4715387 : Blo 2095435 4715387 := bstep (se 1 (by rfl) ⟨3536540, by rfl⟩ : syracuseStep 4715387 = 7073081) B7073081
theorem B3143591 : Blo 2095435 3143591 := bstep (se 1 (by rfl) ⟨2357693, by rfl⟩ : syracuseStep 3143591 = 4715387) B4715387
theorem B2095727 : Blo 2095435 2095727 := bstep (se 1 (by rfl) ⟨1571795, by rfl⟩ : syracuseStep 2095727 = 3143591) B3143591
theorem B3143597 : Blo 2095435 3143597 := bbase (se 3 (by rfl) ⟨589424, by rfl⟩ : syracuseStep 3143597 = 1178849) (by norm_num)
theorem B2095731 : Blo 2095435 2095731 := bstep (se 1 (by rfl) ⟨1571798, by rfl⟩ : syracuseStep 2095731 = 3143597) B3143597
theorem B4715405 : Blo 2095435 4715405 := bbase (se 3 (by rfl) ⟨884138, by rfl⟩ : syracuseStep 4715405 = 1768277) (by norm_num)
theorem B3143603 : Blo 2095435 3143603 := bstep (se 1 (by rfl) ⟨2357702, by rfl⟩ : syracuseStep 3143603 = 4715405) B4715405
theorem B2095735 : Blo 2095435 2095735 := bstep (se 1 (by rfl) ⟨1571801, by rfl⟩ : syracuseStep 2095735 = 3143603) B3143603
theorem B2652421 : Blo 2095435 2652421 := bbase (se 4 (by rfl) ⟨248664, by rfl⟩ : syracuseStep 2652421 = 497329) (by norm_num)
theorem B3536561 : Blo 2095435 3536561 := bstep (se 2 (by rfl) ⟨1326210, by rfl⟩ : syracuseStep 3536561 = 2652421) B2652421
theorem B2357707 : Blo 2095435 2357707 := bstep (se 1 (by rfl) ⟨1768280, by rfl⟩ : syracuseStep 2357707 = 3536561) B3536561
theorem B3143609 : Blo 2095435 3143609 := bstep (se 2 (by rfl) ⟨1178853, by rfl⟩ : syracuseStep 3143609 = 2357707) B2357707
theorem B2095739 : Blo 2095435 2095739 := bstep (se 1 (by rfl) ⟨1571804, by rfl⟩ : syracuseStep 2095739 = 3143609) B3143609
theorem B8497349 : Blo 2095435 8497349 := bbase (se 4 (by rfl) ⟨796626, by rfl⟩ : syracuseStep 8497349 = 1593253) (by norm_num)
theorem B5664899 : Blo 2095435 5664899 := bstep (se 1 (by rfl) ⟨4248674, by rfl⟩ : syracuseStep 5664899 = 8497349) B8497349
theorem B3776599 : Blo 2095435 3776599 := bstep (se 1 (by rfl) ⟨2832449, by rfl⟩ : syracuseStep 3776599 = 5664899) B5664899
theorem B5035465 : Blo 2095435 5035465 := bstep (se 2 (by rfl) ⟨1888299, by rfl⟩ : syracuseStep 5035465 = 3776599) B3776599
theorem B26855813 : Blo 2095435 26855813 := bstep (se 4 (by rfl) ⟨2517732, by rfl⟩ : syracuseStep 26855813 = 5035465) B5035465
theorem B17903875 : Blo 2095435 17903875 := bstep (se 1 (by rfl) ⟨13427906, by rfl⟩ : syracuseStep 17903875 = 26855813) B26855813
theorem B23871833 : Blo 2095435 23871833 := bstep (se 2 (by rfl) ⟨8951937, by rfl⟩ : syracuseStep 23871833 = 17903875) B17903875
theorem B15914555 : Blo 2095435 15914555 := bstep (se 1 (by rfl) ⟨11935916, by rfl⟩ : syracuseStep 15914555 = 23871833) B23871833
theorem B10609703 : Blo 2095435 10609703 := bstep (se 1 (by rfl) ⟨7957277, by rfl⟩ : syracuseStep 10609703 = 15914555) B15914555
theorem B7073135 : Blo 2095435 7073135 := bstep (se 1 (by rfl) ⟨5304851, by rfl⟩ : syracuseStep 7073135 = 10609703) B10609703
theorem B4715423 : Blo 2095435 4715423 := bstep (se 1 (by rfl) ⟨3536567, by rfl⟩ : syracuseStep 4715423 = 7073135) B7073135
theorem B3143615 : Blo 2095435 3143615 := bstep (se 1 (by rfl) ⟨2357711, by rfl⟩ : syracuseStep 3143615 = 4715423) B4715423
theorem B2095743 : Blo 2095435 2095743 := bstep (se 1 (by rfl) ⟨1571807, by rfl⟩ : syracuseStep 2095743 = 3143615) B3143615
theorem B3143621 : Blo 2095435 3143621 := bbase (se 4 (by rfl) ⟨294714, by rfl⟩ : syracuseStep 3143621 = 589429) (by norm_num)
theorem B2095747 : Blo 2095435 2095747 := bstep (se 1 (by rfl) ⟨1571810, by rfl⟩ : syracuseStep 2095747 = 3143621) B3143621
theorem B3536581 : Blo 2095435 3536581 := bbase (se 4 (by rfl) ⟨331554, by rfl⟩ : syracuseStep 3536581 = 663109) (by norm_num)
theorem B4715441 : Blo 2095435 4715441 := bstep (se 2 (by rfl) ⟨1768290, by rfl⟩ : syracuseStep 4715441 = 3536581) B3536581
theorem B3143627 : Blo 2095435 3143627 := bstep (se 1 (by rfl) ⟨2357720, by rfl⟩ : syracuseStep 3143627 = 4715441) B4715441
theorem B2095751 : Blo 2095435 2095751 := bstep (se 1 (by rfl) ⟨1571813, by rfl⟩ : syracuseStep 2095751 = 3143627) B3143627
theorem B2357725 : Blo 2095435 2357725 := bbase (se 3 (by rfl) ⟨442073, by rfl⟩ : syracuseStep 2357725 = 884147) (by norm_num)
theorem B3143633 : Blo 2095435 3143633 := bstep (se 2 (by rfl) ⟨1178862, by rfl⟩ : syracuseStep 3143633 = 2357725) B2357725
theorem B2095755 : Blo 2095435 2095755 := bstep (se 1 (by rfl) ⟨1571816, by rfl⟩ : syracuseStep 2095755 = 3143633) B3143633
theorem B7073189 : Blo 2095435 7073189 := bbase (se 4 (by rfl) ⟨663111, by rfl⟩ : syracuseStep 7073189 = 1326223) (by norm_num)
theorem B4715459 : Blo 2095435 4715459 := bstep (se 1 (by rfl) ⟨3536594, by rfl⟩ : syracuseStep 4715459 = 7073189) B7073189
theorem B3143639 : Blo 2095435 3143639 := bstep (se 1 (by rfl) ⟨2357729, by rfl⟩ : syracuseStep 3143639 = 4715459) B4715459
theorem B2095759 : Blo 2095435 2095759 := bstep (se 1 (by rfl) ⟨1571819, by rfl⟩ : syracuseStep 2095759 = 3143639) B3143639
theorem B3143645 : Blo 2095435 3143645 := bbase (se 3 (by rfl) ⟨589433, by rfl⟩ : syracuseStep 3143645 = 1178867) (by norm_num)
theorem B2095763 : Blo 2095435 2095763 := bstep (se 1 (by rfl) ⟨1571822, by rfl⟩ : syracuseStep 2095763 = 3143645) B3143645
theorem B4715477 : Blo 2095435 4715477 := bbase (se 7 (by rfl) ⟨55259, by rfl⟩ : syracuseStep 4715477 = 110519) (by norm_num)
theorem B3143651 : Blo 2095435 3143651 := bstep (se 1 (by rfl) ⟨2357738, by rfl⟩ : syracuseStep 3143651 = 4715477) B4715477
theorem B2095767 : Blo 2095435 2095767 := bstep (se 1 (by rfl) ⟨1571825, by rfl⟩ : syracuseStep 2095767 = 3143651) B3143651
theorem B4845037 : Blo 2095435 4845037 := bbase (se 3 (by rfl) ⟨908444, by rfl⟩ : syracuseStep 4845037 = 1816889) (by norm_num)
theorem B6460049 : Blo 2095435 6460049 := bstep (se 2 (by rfl) ⟨2422518, by rfl⟩ : syracuseStep 6460049 = 4845037) B4845037
theorem B4306699 : Blo 2095435 4306699 := bstep (se 1 (by rfl) ⟨3230024, by rfl⟩ : syracuseStep 4306699 = 6460049) B6460049
theorem B22969061 : Blo 2095435 22969061 := bstep (se 4 (by rfl) ⟨2153349, by rfl⟩ : syracuseStep 22969061 = 4306699) B4306699
theorem B15312707 : Blo 2095435 15312707 := bstep (se 1 (by rfl) ⟨11484530, by rfl⟩ : syracuseStep 15312707 = 22969061) B22969061
theorem B10208471 : Blo 2095435 10208471 := bstep (se 1 (by rfl) ⟨7656353, by rfl⟩ : syracuseStep 10208471 = 15312707) B15312707
theorem B27222589 : Blo 2095435 27222589 := bstep (se 3 (by rfl) ⟨5104235, by rfl⟩ : syracuseStep 27222589 = 10208471) B10208471
theorem B36296785 : Blo 2095435 36296785 := bstep (se 2 (by rfl) ⟨13611294, by rfl⟩ : syracuseStep 36296785 = 27222589) B27222589
theorem B48395713 : Blo 2095435 48395713 := bstep (se 2 (by rfl) ⟨18148392, by rfl⟩ : syracuseStep 48395713 = 36296785) B36296785
theorem B64527617 : Blo 2095435 64527617 := bstep (se 2 (by rfl) ⟨24197856, by rfl⟩ : syracuseStep 64527617 = 48395713) B48395713
theorem B43018411 : Blo 2095435 43018411 := bstep (se 1 (by rfl) ⟨32263808, by rfl⟩ : syracuseStep 43018411 = 64527617) B64527617
theorem B57357881 : Blo 2095435 57357881 := bstep (se 2 (by rfl) ⟨21509205, by rfl⟩ : syracuseStep 57357881 = 43018411) B43018411
theorem B38238587 : Blo 2095435 38238587 := bstep (se 1 (by rfl) ⟨28678940, by rfl⟩ : syracuseStep 38238587 = 57357881) B57357881
theorem B25492391 : Blo 2095435 25492391 := bstep (se 1 (by rfl) ⟨19119293, by rfl⟩ : syracuseStep 25492391 = 38238587) B38238587
theorem B16994927 : Blo 2095435 16994927 := bstep (se 1 (by rfl) ⟨12746195, by rfl⟩ : syracuseStep 16994927 = 25492391) B25492391
theorem B11329951 : Blo 2095435 11329951 := bstep (se 1 (by rfl) ⟨8497463, by rfl⟩ : syracuseStep 11329951 = 16994927) B16994927
theorem B15106601 : Blo 2095435 15106601 := bstep (se 2 (by rfl) ⟨5664975, by rfl⟩ : syracuseStep 15106601 = 11329951) B11329951
theorem B10071067 : Blo 2095435 10071067 := bstep (se 1 (by rfl) ⟨7553300, by rfl⟩ : syracuseStep 10071067 = 15106601) B15106601
theorem B13428089 : Blo 2095435 13428089 := bstep (se 2 (by rfl) ⟨5035533, by rfl⟩ : syracuseStep 13428089 = 10071067) B10071067
theorem B8952059 : Blo 2095435 8952059 := bstep (se 1 (by rfl) ⟨6714044, by rfl⟩ : syracuseStep 8952059 = 13428089) B13428089
theorem B5968039 : Blo 2095435 5968039 := bstep (se 1 (by rfl) ⟨4476029, by rfl⟩ : syracuseStep 5968039 = 8952059) B8952059
theorem B7957385 : Blo 2095435 7957385 := bstep (se 2 (by rfl) ⟨2984019, by rfl⟩ : syracuseStep 7957385 = 5968039) B5968039
theorem B5304923 : Blo 2095435 5304923 := bstep (se 1 (by rfl) ⟨3978692, by rfl⟩ : syracuseStep 5304923 = 7957385) B7957385
theorem B3536615 : Blo 2095435 3536615 := bstep (se 1 (by rfl) ⟨2652461, by rfl⟩ : syracuseStep 3536615 = 5304923) B5304923
theorem B2357743 : Blo 2095435 2357743 := bstep (se 1 (by rfl) ⟨1768307, by rfl⟩ : syracuseStep 2357743 = 3536615) B3536615
theorem B3143657 : Blo 2095435 3143657 := bstep (se 2 (by rfl) ⟨1178871, by rfl⟩ : syracuseStep 3143657 = 2357743) B2357743
theorem B2095771 : Blo 2095435 2095771 := bstep (se 1 (by rfl) ⟨1571828, by rfl⟩ : syracuseStep 2095771 = 3143657) B3143657
theorem B17904149 : Blo 2095435 17904149 := bbase (se 6 (by rfl) ⟨419628, by rfl⟩ : syracuseStep 17904149 = 839257) (by norm_num)
theorem B11936099 : Blo 2095435 11936099 := bstep (se 1 (by rfl) ⟨8952074, by rfl⟩ : syracuseStep 11936099 = 17904149) B17904149
theorem B7957399 : Blo 2095435 7957399 := bstep (se 1 (by rfl) ⟨5968049, by rfl⟩ : syracuseStep 7957399 = 11936099) B11936099
theorem B10609865 : Blo 2095435 10609865 := bstep (se 2 (by rfl) ⟨3978699, by rfl⟩ : syracuseStep 10609865 = 7957399) B7957399
theorem B7073243 : Blo 2095435 7073243 := bstep (se 1 (by rfl) ⟨5304932, by rfl⟩ : syracuseStep 7073243 = 10609865) B10609865
theorem B4715495 : Blo 2095435 4715495 := bstep (se 1 (by rfl) ⟨3536621, by rfl⟩ : syracuseStep 4715495 = 7073243) B7073243
theorem B3143663 : Blo 2095435 3143663 := bstep (se 1 (by rfl) ⟨2357747, by rfl⟩ : syracuseStep 3143663 = 4715495) B4715495
theorem B2095775 : Blo 2095435 2095775 := bstep (se 1 (by rfl) ⟨1571831, by rfl⟩ : syracuseStep 2095775 = 3143663) B3143663
theorem B3143669 : Blo 2095435 3143669 := bbase (se 5 (by rfl) ⟨147359, by rfl⟩ : syracuseStep 3143669 = 294719) (by norm_num)
theorem B2095779 : Blo 2095435 2095779 := bstep (se 1 (by rfl) ⟨1571834, by rfl⟩ : syracuseStep 2095779 = 3143669) B3143669
theorem B10071125 : Blo 2095435 10071125 := bbase (se 8 (by rfl) ⟨59010, by rfl⟩ : syracuseStep 10071125 = 118021) (by norm_num)
theorem B6714083 : Blo 2095435 6714083 := bstep (se 1 (by rfl) ⟨5035562, by rfl⟩ : syracuseStep 6714083 = 10071125) B10071125
theorem B4476055 : Blo 2095435 4476055 := bstep (se 1 (by rfl) ⟨3357041, by rfl⟩ : syracuseStep 4476055 = 6714083) B6714083
theorem B5968073 : Blo 2095435 5968073 := bstep (se 2 (by rfl) ⟨2238027, by rfl⟩ : syracuseStep 5968073 = 4476055) B4476055
theorem B3978715 : Blo 2095435 3978715 := bstep (se 1 (by rfl) ⟨2984036, by rfl⟩ : syracuseStep 3978715 = 5968073) B5968073
theorem B5304953 : Blo 2095435 5304953 := bstep (se 2 (by rfl) ⟨1989357, by rfl⟩ : syracuseStep 5304953 = 3978715) B3978715
theorem B3536635 : Blo 2095435 3536635 := bstep (se 1 (by rfl) ⟨2652476, by rfl⟩ : syracuseStep 3536635 = 5304953) B5304953
theorem B4715513 : Blo 2095435 4715513 := bstep (se 2 (by rfl) ⟨1768317, by rfl⟩ : syracuseStep 4715513 = 3536635) B3536635
theorem B3143675 : Blo 2095435 3143675 := bstep (se 1 (by rfl) ⟨2357756, by rfl⟩ : syracuseStep 3143675 = 4715513) B4715513
theorem B2095783 : Blo 2095435 2095783 := bstep (se 1 (by rfl) ⟨1571837, by rfl⟩ : syracuseStep 2095783 = 3143675) B3143675
theorem B2357761 : Blo 2095435 2357761 := bbase (se 2 (by rfl) ⟨884160, by rfl⟩ : syracuseStep 2357761 = 1768321) (by norm_num)
theorem B3143681 : Blo 2095435 3143681 := bstep (se 2 (by rfl) ⟨1178880, by rfl⟩ : syracuseStep 3143681 = 2357761) B2357761
theorem B2095787 : Blo 2095435 2095787 := bstep (se 1 (by rfl) ⟨1571840, by rfl⟩ : syracuseStep 2095787 = 3143681) B3143681
theorem B5304973 : Blo 2095435 5304973 := bbase (se 3 (by rfl) ⟨994682, by rfl⟩ : syracuseStep 5304973 = 1989365) (by norm_num)
theorem B7073297 : Blo 2095435 7073297 := bstep (se 2 (by rfl) ⟨2652486, by rfl⟩ : syracuseStep 7073297 = 5304973) B5304973
theorem B4715531 : Blo 2095435 4715531 := bstep (se 1 (by rfl) ⟨3536648, by rfl⟩ : syracuseStep 4715531 = 7073297) B7073297
theorem B3143687 : Blo 2095435 3143687 := bstep (se 1 (by rfl) ⟨2357765, by rfl⟩ : syracuseStep 3143687 = 4715531) B4715531
theorem B2095791 : Blo 2095435 2095791 := bstep (se 1 (by rfl) ⟨1571843, by rfl⟩ : syracuseStep 2095791 = 3143687) B3143687
theorem B3143693 : Blo 2095435 3143693 := bbase (se 3 (by rfl) ⟨589442, by rfl⟩ : syracuseStep 3143693 = 1178885) (by norm_num)
theorem B2095795 : Blo 2095435 2095795 := bstep (se 1 (by rfl) ⟨1571846, by rfl⟩ : syracuseStep 2095795 = 3143693) B3143693
theorem B4715549 : Blo 2095435 4715549 := bbase (se 3 (by rfl) ⟨884165, by rfl⟩ : syracuseStep 4715549 = 1768331) (by norm_num)
theorem B3143699 : Blo 2095435 3143699 := bstep (se 1 (by rfl) ⟨2357774, by rfl⟩ : syracuseStep 3143699 = 4715549) B4715549
theorem B2095799 : Blo 2095435 2095799 := bstep (se 1 (by rfl) ⟨1571849, by rfl⟩ : syracuseStep 2095799 = 3143699) B3143699
theorem B3536669 : Blo 2095435 3536669 := bbase (se 3 (by rfl) ⟨663125, by rfl⟩ : syracuseStep 3536669 = 1326251) (by norm_num)
theorem B2357779 : Blo 2095435 2357779 := bstep (se 1 (by rfl) ⟨1768334, by rfl⟩ : syracuseStep 2357779 = 3536669) B3536669
theorem B3143705 : Blo 2095435 3143705 := bstep (se 2 (by rfl) ⟨1178889, by rfl⟩ : syracuseStep 3143705 = 2357779) B2357779
theorem B2095803 : Blo 2095435 2095803 := bstep (se 1 (by rfl) ⟨1571852, by rfl⟩ : syracuseStep 2095803 = 3143705) B3143705
theorem B7553429 : Blo 2095435 7553429 := bbase (se 6 (by rfl) ⟨177033, by rfl⟩ : syracuseStep 7553429 = 354067) (by norm_num)
theorem B5035619 : Blo 2095435 5035619 := bstep (se 1 (by rfl) ⟨3776714, by rfl⟩ : syracuseStep 5035619 = 7553429) B7553429
theorem B13428317 : Blo 2095435 13428317 := bstep (se 3 (by rfl) ⟨2517809, by rfl⟩ : syracuseStep 13428317 = 5035619) B5035619
theorem B8952211 : Blo 2095435 8952211 := bstep (se 1 (by rfl) ⟨6714158, by rfl⟩ : syracuseStep 8952211 = 13428317) B13428317
theorem B11936281 : Blo 2095435 11936281 := bstep (se 2 (by rfl) ⟨4476105, by rfl⟩ : syracuseStep 11936281 = 8952211) B8952211
theorem B15915041 : Blo 2095435 15915041 := bstep (se 2 (by rfl) ⟨5968140, by rfl⟩ : syracuseStep 15915041 = 11936281) B11936281
theorem B10610027 : Blo 2095435 10610027 := bstep (se 1 (by rfl) ⟨7957520, by rfl⟩ : syracuseStep 10610027 = 15915041) B15915041
theorem B7073351 : Blo 2095435 7073351 := bstep (se 1 (by rfl) ⟨5305013, by rfl⟩ : syracuseStep 7073351 = 10610027) B10610027
theorem B4715567 : Blo 2095435 4715567 := bstep (se 1 (by rfl) ⟨3536675, by rfl⟩ : syracuseStep 4715567 = 7073351) B7073351
theorem B3143711 : Blo 2095435 3143711 := bstep (se 1 (by rfl) ⟨2357783, by rfl⟩ : syracuseStep 3143711 = 4715567) B4715567
theorem B2095807 : Blo 2095435 2095807 := bstep (se 1 (by rfl) ⟨1571855, by rfl⟩ : syracuseStep 2095807 = 3143711) B3143711
theorem B3143717 : Blo 2095435 3143717 := bbase (se 4 (by rfl) ⟨294723, by rfl⟩ : syracuseStep 3143717 = 589447) (by norm_num)
theorem B2095811 : Blo 2095435 2095811 := bstep (se 1 (by rfl) ⟨1571858, by rfl⟩ : syracuseStep 2095811 = 3143717) B3143717
theorem B2652517 : Blo 2095435 2652517 := bbase (se 4 (by rfl) ⟨248673, by rfl⟩ : syracuseStep 2652517 = 497347) (by norm_num)
theorem B3536689 : Blo 2095435 3536689 := bstep (se 2 (by rfl) ⟨1326258, by rfl⟩ : syracuseStep 3536689 = 2652517) B2652517
theorem B4715585 : Blo 2095435 4715585 := bstep (se 2 (by rfl) ⟨1768344, by rfl⟩ : syracuseStep 4715585 = 3536689) B3536689
theorem B3143723 : Blo 2095435 3143723 := bstep (se 1 (by rfl) ⟨2357792, by rfl⟩ : syracuseStep 3143723 = 4715585) B4715585
theorem B2095815 : Blo 2095435 2095815 := bstep (se 1 (by rfl) ⟨1571861, by rfl⟩ : syracuseStep 2095815 = 3143723) B3143723
theorem B2357797 : Blo 2095435 2357797 := bbase (se 4 (by rfl) ⟨221043, by rfl⟩ : syracuseStep 2357797 = 442087) (by norm_num)
theorem B3143729 : Blo 2095435 3143729 := bstep (se 2 (by rfl) ⟨1178898, by rfl⟩ : syracuseStep 3143729 = 2357797) B2357797
theorem B2095819 : Blo 2095435 2095819 := bstep (se 1 (by rfl) ⟨1571864, by rfl⟩ : syracuseStep 2095819 = 3143729) B3143729
theorem B10071317 : Blo 2095435 10071317 := bbase (se 6 (by rfl) ⟨236046, by rfl⟩ : syracuseStep 10071317 = 472093) (by norm_num)
theorem B6714211 : Blo 2095435 6714211 := bstep (se 1 (by rfl) ⟨5035658, by rfl⟩ : syracuseStep 6714211 = 10071317) B10071317
theorem B8952281 : Blo 2095435 8952281 := bstep (se 2 (by rfl) ⟨3357105, by rfl⟩ : syracuseStep 8952281 = 6714211) B6714211
theorem B5968187 : Blo 2095435 5968187 := bstep (se 1 (by rfl) ⟨4476140, by rfl⟩ : syracuseStep 5968187 = 8952281) B8952281
theorem B3978791 : Blo 2095435 3978791 := bstep (se 1 (by rfl) ⟨2984093, by rfl⟩ : syracuseStep 3978791 = 5968187) B5968187
theorem B2652527 : Blo 2095435 2652527 := bstep (se 1 (by rfl) ⟨1989395, by rfl⟩ : syracuseStep 2652527 = 3978791) B3978791
theorem B7073405 : Blo 2095435 7073405 := bstep (se 3 (by rfl) ⟨1326263, by rfl⟩ : syracuseStep 7073405 = 2652527) B2652527
theorem B4715603 : Blo 2095435 4715603 := bstep (se 1 (by rfl) ⟨3536702, by rfl⟩ : syracuseStep 4715603 = 7073405) B7073405
theorem B3143735 : Blo 2095435 3143735 := bstep (se 1 (by rfl) ⟨2357801, by rfl⟩ : syracuseStep 3143735 = 4715603) B4715603
theorem B2095823 : Blo 2095435 2095823 := bstep (se 1 (by rfl) ⟨1571867, by rfl⟩ : syracuseStep 2095823 = 3143735) B3143735
theorem B3143741 : Blo 2095435 3143741 := bbase (se 3 (by rfl) ⟨589451, by rfl⟩ : syracuseStep 3143741 = 1178903) (by norm_num)
theorem B2095827 : Blo 2095435 2095827 := bstep (se 1 (by rfl) ⟨1571870, by rfl⟩ : syracuseStep 2095827 = 3143741) B3143741
theorem B4715621 : Blo 2095435 4715621 := bbase (se 4 (by rfl) ⟨442089, by rfl⟩ : syracuseStep 4715621 = 884179) (by norm_num)
theorem B3143747 : Blo 2095435 3143747 := bstep (se 1 (by rfl) ⟨2357810, by rfl⟩ : syracuseStep 3143747 = 4715621) B4715621
theorem B2095831 : Blo 2095435 2095831 := bstep (se 1 (by rfl) ⟨1571873, by rfl⟩ : syracuseStep 2095831 = 3143747) B3143747
theorem B5305085 : Blo 2095435 5305085 := bbase (se 3 (by rfl) ⟨994703, by rfl⟩ : syracuseStep 5305085 = 1989407) (by norm_num)
theorem B3536723 : Blo 2095435 3536723 := bstep (se 1 (by rfl) ⟨2652542, by rfl⟩ : syracuseStep 3536723 = 5305085) B5305085
theorem B2357815 : Blo 2095435 2357815 := bstep (se 1 (by rfl) ⟨1768361, by rfl⟩ : syracuseStep 2357815 = 3536723) B3536723
theorem B3143753 : Blo 2095435 3143753 := bstep (se 2 (by rfl) ⟨1178907, by rfl⟩ : syracuseStep 3143753 = 2357815) B2357815
theorem B2095835 : Blo 2095435 2095835 := bstep (se 1 (by rfl) ⟨1571876, by rfl⟩ : syracuseStep 2095835 = 3143753) B3143753
theorem B3978821 : Blo 2095435 3978821 := bbase (se 4 (by rfl) ⟨373014, by rfl⟩ : syracuseStep 3978821 = 746029) (by norm_num)
theorem B10610189 : Blo 2095435 10610189 := bstep (se 3 (by rfl) ⟨1989410, by rfl⟩ : syracuseStep 10610189 = 3978821) B3978821
theorem B7073459 : Blo 2095435 7073459 := bstep (se 1 (by rfl) ⟨5305094, by rfl⟩ : syracuseStep 7073459 = 10610189) B10610189
theorem B4715639 : Blo 2095435 4715639 := bstep (se 1 (by rfl) ⟨3536729, by rfl⟩ : syracuseStep 4715639 = 7073459) B7073459
theorem B3143759 : Blo 2095435 3143759 := bstep (se 1 (by rfl) ⟨2357819, by rfl⟩ : syracuseStep 3143759 = 4715639) B4715639
theorem B2095839 : Blo 2095435 2095839 := bstep (se 1 (by rfl) ⟨1571879, by rfl⟩ : syracuseStep 2095839 = 3143759) B3143759
theorem B3143765 : Blo 2095435 3143765 := bbase (se 8 (by rfl) ⟨18420, by rfl⟩ : syracuseStep 3143765 = 36841) (by norm_num)
theorem B2095843 : Blo 2095435 2095843 := bstep (se 1 (by rfl) ⟨1571882, by rfl⟩ : syracuseStep 2095843 = 3143765) B3143765
theorem B67982165 : Blo 2095435 67982165 := bbase (se 9 (by rfl) ⟨199166, by rfl⟩ : syracuseStep 67982165 = 398333) (by norm_num)
theorem B45321443 : Blo 2095435 45321443 := bstep (se 1 (by rfl) ⟨33991082, by rfl⟩ : syracuseStep 45321443 = 67982165) B67982165
theorem B30214295 : Blo 2095435 30214295 := bstep (se 1 (by rfl) ⟨22660721, by rfl⟩ : syracuseStep 30214295 = 45321443) B45321443
theorem B20142863 : Blo 2095435 20142863 := bstep (se 1 (by rfl) ⟨15107147, by rfl⟩ : syracuseStep 20142863 = 30214295) B30214295
theorem B13428575 : Blo 2095435 13428575 := bstep (se 1 (by rfl) ⟨10071431, by rfl⟩ : syracuseStep 13428575 = 20142863) B20142863
theorem B8952383 : Blo 2095435 8952383 := bstep (se 1 (by rfl) ⟨6714287, by rfl⟩ : syracuseStep 8952383 = 13428575) B13428575
theorem B5968255 : Blo 2095435 5968255 := bstep (se 1 (by rfl) ⟨4476191, by rfl⟩ : syracuseStep 5968255 = 8952383) B8952383
theorem B7957673 : Blo 2095435 7957673 := bstep (se 2 (by rfl) ⟨2984127, by rfl⟩ : syracuseStep 7957673 = 5968255) B5968255
theorem B5305115 : Blo 2095435 5305115 := bstep (se 1 (by rfl) ⟨3978836, by rfl⟩ : syracuseStep 5305115 = 7957673) B7957673
theorem B3536743 : Blo 2095435 3536743 := bstep (se 1 (by rfl) ⟨2652557, by rfl⟩ : syracuseStep 3536743 = 5305115) B5305115
theorem B4715657 : Blo 2095435 4715657 := bstep (se 2 (by rfl) ⟨1768371, by rfl⟩ : syracuseStep 4715657 = 3536743) B3536743
theorem B3143771 : Blo 2095435 3143771 := bstep (se 1 (by rfl) ⟨2357828, by rfl⟩ : syracuseStep 3143771 = 4715657) B4715657
theorem B2095847 : Blo 2095435 2095847 := bstep (se 1 (by rfl) ⟨1571885, by rfl⟩ : syracuseStep 2095847 = 3143771) B3143771
theorem B2357833 : Blo 2095435 2357833 := bbase (se 2 (by rfl) ⟨884187, by rfl⟩ : syracuseStep 2357833 = 1768375) (by norm_num)
theorem B3143777 : Blo 2095435 3143777 := bstep (se 2 (by rfl) ⟨1178916, by rfl⟩ : syracuseStep 3143777 = 2357833) B2357833
theorem B2095851 : Blo 2095435 2095851 := bstep (se 1 (by rfl) ⟨1571888, by rfl⟩ : syracuseStep 2095851 = 3143777) B3143777
theorem B3186677 : Blo 2095435 3186677 := bbase (se 5 (by rfl) ⟨149375, by rfl⟩ : syracuseStep 3186677 = 298751) (by norm_num)
theorem B2124451 : Blo 2095435 2124451 := bstep (se 1 (by rfl) ⟨1593338, by rfl⟩ : syracuseStep 2124451 = 3186677) B3186677
theorem B2832601 : Blo 2095435 2832601 := bstep (se 2 (by rfl) ⟨1062225, by rfl⟩ : syracuseStep 2832601 = 2124451) B2124451
theorem B3776801 : Blo 2095435 3776801 := bstep (se 2 (by rfl) ⟨1416300, by rfl⟩ : syracuseStep 3776801 = 2832601) B2832601
theorem B10071469 : Blo 2095435 10071469 := bstep (se 3 (by rfl) ⟨1888400, by rfl⟩ : syracuseStep 10071469 = 3776801) B3776801
theorem B13428625 : Blo 2095435 13428625 := bstep (se 2 (by rfl) ⟨5035734, by rfl⟩ : syracuseStep 13428625 = 10071469) B10071469
theorem B17904833 : Blo 2095435 17904833 := bstep (se 2 (by rfl) ⟨6714312, by rfl⟩ : syracuseStep 17904833 = 13428625) B13428625
theorem B11936555 : Blo 2095435 11936555 := bstep (se 1 (by rfl) ⟨8952416, by rfl⟩ : syracuseStep 11936555 = 17904833) B17904833
theorem B7957703 : Blo 2095435 7957703 := bstep (se 1 (by rfl) ⟨5968277, by rfl⟩ : syracuseStep 7957703 = 11936555) B11936555
theorem B5305135 : Blo 2095435 5305135 := bstep (se 1 (by rfl) ⟨3978851, by rfl⟩ : syracuseStep 5305135 = 7957703) B7957703
theorem B7073513 : Blo 2095435 7073513 := bstep (se 2 (by rfl) ⟨2652567, by rfl⟩ : syracuseStep 7073513 = 5305135) B5305135
theorem B4715675 : Blo 2095435 4715675 := bstep (se 1 (by rfl) ⟨3536756, by rfl⟩ : syracuseStep 4715675 = 7073513) B7073513
theorem B3143783 : Blo 2095435 3143783 := bstep (se 1 (by rfl) ⟨2357837, by rfl⟩ : syracuseStep 3143783 = 4715675) B4715675
theorem B2095855 : Blo 2095435 2095855 := bstep (se 1 (by rfl) ⟨1571891, by rfl⟩ : syracuseStep 2095855 = 3143783) B3143783
theorem B3143789 : Blo 2095435 3143789 := bbase (se 3 (by rfl) ⟨589460, by rfl⟩ : syracuseStep 3143789 = 1178921) (by norm_num)
theorem B2095859 : Blo 2095435 2095859 := bstep (se 1 (by rfl) ⟨1571894, by rfl⟩ : syracuseStep 2095859 = 3143789) B3143789
theorem B4715693 : Blo 2095435 4715693 := bbase (se 3 (by rfl) ⟨884192, by rfl⟩ : syracuseStep 4715693 = 1768385) (by norm_num)
theorem B3143795 : Blo 2095435 3143795 := bstep (se 1 (by rfl) ⟨2357846, by rfl⟩ : syracuseStep 3143795 = 4715693) B4715693
theorem B2095863 : Blo 2095435 2095863 := bstep (se 1 (by rfl) ⟨1571897, by rfl⟩ : syracuseStep 2095863 = 3143795) B3143795
theorem B5035765 : Blo 2095435 5035765 := bbase (se 5 (by rfl) ⟨236051, by rfl⟩ : syracuseStep 5035765 = 472103) (by norm_num)
theorem B6714353 : Blo 2095435 6714353 := bstep (se 2 (by rfl) ⟨2517882, by rfl⟩ : syracuseStep 6714353 = 5035765) B5035765
theorem B4476235 : Blo 2095435 4476235 := bstep (se 1 (by rfl) ⟨3357176, by rfl⟩ : syracuseStep 4476235 = 6714353) B6714353
theorem B5968313 : Blo 2095435 5968313 := bstep (se 2 (by rfl) ⟨2238117, by rfl⟩ : syracuseStep 5968313 = 4476235) B4476235
theorem B3978875 : Blo 2095435 3978875 := bstep (se 1 (by rfl) ⟨2984156, by rfl⟩ : syracuseStep 3978875 = 5968313) B5968313
theorem B2652583 : Blo 2095435 2652583 := bstep (se 1 (by rfl) ⟨1989437, by rfl⟩ : syracuseStep 2652583 = 3978875) B3978875
theorem B3536777 : Blo 2095435 3536777 := bstep (se 2 (by rfl) ⟨1326291, by rfl⟩ : syracuseStep 3536777 = 2652583) B2652583
theorem B2357851 : Blo 2095435 2357851 := bstep (se 1 (by rfl) ⟨1768388, by rfl⟩ : syracuseStep 2357851 = 3536777) B3536777
theorem B3143801 : Blo 2095435 3143801 := bstep (se 2 (by rfl) ⟨1178925, by rfl⟩ : syracuseStep 3143801 = 2357851) B2357851
theorem B2095867 : Blo 2095435 2095867 := bstep (se 1 (by rfl) ⟨1571900, by rfl⟩ : syracuseStep 2095867 = 3143801) B3143801
theorem B9560101 : Blo 2095435 9560101 := bbase (se 4 (by rfl) ⟨896259, by rfl⟩ : syracuseStep 9560101 = 1792519) (by norm_num)
theorem B12746801 : Blo 2095435 12746801 := bstep (se 2 (by rfl) ⟨4780050, by rfl⟩ : syracuseStep 12746801 = 9560101) B9560101
theorem B8497867 : Blo 2095435 8497867 := bstep (se 1 (by rfl) ⟨6373400, by rfl⟩ : syracuseStep 8497867 = 12746801) B12746801
theorem B11330489 : Blo 2095435 11330489 := bstep (se 2 (by rfl) ⟨4248933, by rfl⟩ : syracuseStep 11330489 = 8497867) B8497867
theorem B7553659 : Blo 2095435 7553659 := bstep (se 1 (by rfl) ⟨5665244, by rfl⟩ : syracuseStep 7553659 = 11330489) B11330489
theorem B10071545 : Blo 2095435 10071545 := bstep (se 2 (by rfl) ⟨3776829, by rfl⟩ : syracuseStep 10071545 = 7553659) B7553659
theorem B26857453 : Blo 2095435 26857453 := bstep (se 3 (by rfl) ⟨5035772, by rfl⟩ : syracuseStep 26857453 = 10071545) B10071545
theorem B35809937 : Blo 2095435 35809937 := bstep (se 2 (by rfl) ⟨13428726, by rfl⟩ : syracuseStep 35809937 = 26857453) B26857453
theorem B23873291 : Blo 2095435 23873291 := bstep (se 1 (by rfl) ⟨17904968, by rfl⟩ : syracuseStep 23873291 = 35809937) B35809937
theorem B15915527 : Blo 2095435 15915527 := bstep (se 1 (by rfl) ⟨11936645, by rfl⟩ : syracuseStep 15915527 = 23873291) B23873291
theorem B10610351 : Blo 2095435 10610351 := bstep (se 1 (by rfl) ⟨7957763, by rfl⟩ : syracuseStep 10610351 = 15915527) B15915527
theorem B7073567 : Blo 2095435 7073567 := bstep (se 1 (by rfl) ⟨5305175, by rfl⟩ : syracuseStep 7073567 = 10610351) B10610351
theorem B4715711 : Blo 2095435 4715711 := bstep (se 1 (by rfl) ⟨3536783, by rfl⟩ : syracuseStep 4715711 = 7073567) B7073567
theorem B3143807 : Blo 2095435 3143807 := bstep (se 1 (by rfl) ⟨2357855, by rfl⟩ : syracuseStep 3143807 = 4715711) B4715711
theorem B2095871 : Blo 2095435 2095871 := bstep (se 1 (by rfl) ⟨1571903, by rfl⟩ : syracuseStep 2095871 = 3143807) B3143807
theorem B3143813 : Blo 2095435 3143813 := bbase (se 4 (by rfl) ⟨294732, by rfl⟩ : syracuseStep 3143813 = 589465) (by norm_num)
theorem B2095875 : Blo 2095435 2095875 := bstep (se 1 (by rfl) ⟨1571906, by rfl⟩ : syracuseStep 2095875 = 3143813) B3143813
theorem B3536797 : Blo 2095435 3536797 := bbase (se 3 (by rfl) ⟨663149, by rfl⟩ : syracuseStep 3536797 = 1326299) (by norm_num)
theorem B4715729 : Blo 2095435 4715729 := bstep (se 2 (by rfl) ⟨1768398, by rfl⟩ : syracuseStep 4715729 = 3536797) B3536797
theorem B3143819 : Blo 2095435 3143819 := bstep (se 1 (by rfl) ⟨2357864, by rfl⟩ : syracuseStep 3143819 = 4715729) B4715729
theorem B2095879 : Blo 2095435 2095879 := bstep (se 1 (by rfl) ⟨1571909, by rfl⟩ : syracuseStep 2095879 = 3143819) B3143819
theorem B2357869 : Blo 2095435 2357869 := bbase (se 3 (by rfl) ⟨442100, by rfl⟩ : syracuseStep 2357869 = 884201) (by norm_num)
theorem B3143825 : Blo 2095435 3143825 := bstep (se 2 (by rfl) ⟨1178934, by rfl⟩ : syracuseStep 3143825 = 2357869) B2357869
theorem B2095883 : Blo 2095435 2095883 := bstep (se 1 (by rfl) ⟨1571912, by rfl⟩ : syracuseStep 2095883 = 3143825) B3143825
theorem B7073621 : Blo 2095435 7073621 := bbase (se 9 (by rfl) ⟨20723, by rfl⟩ : syracuseStep 7073621 = 41447) (by norm_num)
theorem B4715747 : Blo 2095435 4715747 := bstep (se 1 (by rfl) ⟨3536810, by rfl⟩ : syracuseStep 4715747 = 7073621) B7073621
theorem B3143831 : Blo 2095435 3143831 := bstep (se 1 (by rfl) ⟨2357873, by rfl⟩ : syracuseStep 3143831 = 4715747) B4715747
theorem B2095887 : Blo 2095435 2095887 := bstep (se 1 (by rfl) ⟨1571915, by rfl⟩ : syracuseStep 2095887 = 3143831) B3143831
theorem B3143837 : Blo 2095435 3143837 := bbase (se 3 (by rfl) ⟨589469, by rfl⟩ : syracuseStep 3143837 = 1178939) (by norm_num)
theorem B2095891 : Blo 2095435 2095891 := bstep (se 1 (by rfl) ⟨1571918, by rfl⟩ : syracuseStep 2095891 = 3143837) B3143837
theorem B4715765 : Blo 2095435 4715765 := bbase (se 5 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 4715765 = 442103) (by norm_num)
theorem B3143843 : Blo 2095435 3143843 := bstep (se 1 (by rfl) ⟨2357882, by rfl⟩ : syracuseStep 3143843 = 4715765) B4715765
theorem B2095895 : Blo 2095435 2095895 := bstep (se 1 (by rfl) ⟨1571921, by rfl⟩ : syracuseStep 2095895 = 3143843) B3143843
theorem B3544229 : Blo 2095435 3544229 := bbase (se 4 (by rfl) ⟨332271, by rfl⟩ : syracuseStep 3544229 = 664543) (by norm_num)
theorem B2362819 : Blo 2095435 2362819 := bstep (se 1 (by rfl) ⟨1772114, by rfl⟩ : syracuseStep 2362819 = 3544229) B3544229
theorem B3150425 : Blo 2095435 3150425 := bstep (se 2 (by rfl) ⟨1181409, by rfl⟩ : syracuseStep 3150425 = 2362819) B2362819
theorem B8401133 : Blo 2095435 8401133 := bstep (se 3 (by rfl) ⟨1575212, by rfl⟩ : syracuseStep 8401133 = 3150425) B3150425
theorem B5600755 : Blo 2095435 5600755 := bstep (se 1 (by rfl) ⟨4200566, by rfl⟩ : syracuseStep 5600755 = 8401133) B8401133
theorem B29870693 : Blo 2095435 29870693 := bstep (se 4 (by rfl) ⟨2800377, by rfl⟩ : syracuseStep 29870693 = 5600755) B5600755
theorem B19913795 : Blo 2095435 19913795 := bstep (se 1 (by rfl) ⟨14935346, by rfl⟩ : syracuseStep 19913795 = 29870693) B29870693
theorem B13275863 : Blo 2095435 13275863 := bstep (se 1 (by rfl) ⟨9956897, by rfl⟩ : syracuseStep 13275863 = 19913795) B19913795
theorem B8850575 : Blo 2095435 8850575 := bstep (se 1 (by rfl) ⟨6637931, by rfl⟩ : syracuseStep 8850575 = 13275863) B13275863
theorem B5900383 : Blo 2095435 5900383 := bstep (se 1 (by rfl) ⟨4425287, by rfl⟩ : syracuseStep 5900383 = 8850575) B8850575
theorem B31468709 : Blo 2095435 31468709 := bstep (se 4 (by rfl) ⟨2950191, by rfl⟩ : syracuseStep 31468709 = 5900383) B5900383
theorem B83916557 : Blo 2095435 83916557 := bstep (se 3 (by rfl) ⟨15734354, by rfl⟩ : syracuseStep 83916557 = 31468709) B31468709
theorem B55944371 : Blo 2095435 55944371 := bstep (se 1 (by rfl) ⟨41958278, by rfl⟩ : syracuseStep 55944371 = 83916557) B83916557
theorem B37296247 : Blo 2095435 37296247 := bstep (se 1 (by rfl) ⟨27972185, by rfl⟩ : syracuseStep 37296247 = 55944371) B55944371
theorem B49728329 : Blo 2095435 49728329 := bstep (se 2 (by rfl) ⟨18648123, by rfl⟩ : syracuseStep 49728329 = 37296247) B37296247
theorem B33152219 : Blo 2095435 33152219 := bstep (se 1 (by rfl) ⟨24864164, by rfl⟩ : syracuseStep 33152219 = 49728329) B49728329
theorem B22101479 : Blo 2095435 22101479 := bstep (se 1 (by rfl) ⟨16576109, by rfl⟩ : syracuseStep 22101479 = 33152219) B33152219
theorem B14734319 : Blo 2095435 14734319 := bstep (se 1 (by rfl) ⟨11050739, by rfl⟩ : syracuseStep 14734319 = 22101479) B22101479
theorem B39291517 : Blo 2095435 39291517 := bstep (se 3 (by rfl) ⟨7367159, by rfl⟩ : syracuseStep 39291517 = 14734319) B14734319
theorem B52388689 : Blo 2095435 52388689 := bstep (se 2 (by rfl) ⟨19645758, by rfl⟩ : syracuseStep 52388689 = 39291517) B39291517
theorem B69851585 : Blo 2095435 69851585 := bstep (se 2 (by rfl) ⟨26194344, by rfl⟩ : syracuseStep 69851585 = 52388689) B52388689
theorem B46567723 : Blo 2095435 46567723 := bstep (se 1 (by rfl) ⟨34925792, by rfl⟩ : syracuseStep 46567723 = 69851585) B69851585
theorem B62090297 : Blo 2095435 62090297 := bstep (se 2 (by rfl) ⟨23283861, by rfl⟩ : syracuseStep 62090297 = 46567723) B46567723
theorem B41393531 : Blo 2095435 41393531 := bstep (se 1 (by rfl) ⟨31045148, by rfl⟩ : syracuseStep 41393531 = 62090297) B62090297
theorem B27595687 : Blo 2095435 27595687 := bstep (se 1 (by rfl) ⟨20696765, by rfl⟩ : syracuseStep 27595687 = 41393531) B41393531
theorem B36794249 : Blo 2095435 36794249 := bstep (se 2 (by rfl) ⟨13797843, by rfl⟩ : syracuseStep 36794249 = 27595687) B27595687
theorem B24529499 : Blo 2095435 24529499 := bstep (se 1 (by rfl) ⟨18397124, by rfl⟩ : syracuseStep 24529499 = 36794249) B36794249
theorem B16352999 : Blo 2095435 16352999 := bstep (se 1 (by rfl) ⟨12264749, by rfl⟩ : syracuseStep 16352999 = 24529499) B24529499
theorem B10901999 : Blo 2095435 10901999 := bstep (se 1 (by rfl) ⟨8176499, by rfl⟩ : syracuseStep 10901999 = 16352999) B16352999
theorem B7267999 : Blo 2095435 7267999 := bstep (se 1 (by rfl) ⟨5450999, by rfl⟩ : syracuseStep 7267999 = 10901999) B10901999
theorem B155050645 : Blo 2095435 155050645 := bstep (se 6 (by rfl) ⟨3633999, by rfl⟩ : syracuseStep 155050645 = 7267999) B7267999
theorem B206734193 : Blo 2095435 206734193 := bstep (se 2 (by rfl) ⟨77525322, by rfl⟩ : syracuseStep 206734193 = 155050645) B155050645
theorem B137822795 : Blo 2095435 137822795 := bstep (se 1 (by rfl) ⟨103367096, by rfl⟩ : syracuseStep 137822795 = 206734193) B206734193
theorem B91881863 : Blo 2095435 91881863 := bstep (se 1 (by rfl) ⟨68911397, by rfl⟩ : syracuseStep 91881863 = 137822795) B137822795
theorem B61254575 : Blo 2095435 61254575 := bstep (se 1 (by rfl) ⟨45940931, by rfl⟩ : syracuseStep 61254575 = 91881863) B91881863
theorem B40836383 : Blo 2095435 40836383 := bstep (se 1 (by rfl) ⟨30627287, by rfl⟩ : syracuseStep 40836383 = 61254575) B61254575
theorem B27224255 : Blo 2095435 27224255 := bstep (se 1 (by rfl) ⟨20418191, by rfl⟩ : syracuseStep 27224255 = 40836383) B40836383
theorem B18149503 : Blo 2095435 18149503 := bstep (se 1 (by rfl) ⟨13612127, by rfl⟩ : syracuseStep 18149503 = 27224255) B27224255
theorem B24199337 : Blo 2095435 24199337 := bstep (se 2 (by rfl) ⟨9074751, by rfl⟩ : syracuseStep 24199337 = 18149503) B18149503
theorem B16132891 : Blo 2095435 16132891 := bstep (se 1 (by rfl) ⟨12099668, by rfl⟩ : syracuseStep 16132891 = 24199337) B24199337
theorem B21510521 : Blo 2095435 21510521 := bstep (se 2 (by rfl) ⟨8066445, by rfl⟩ : syracuseStep 21510521 = 16132891) B16132891
theorem B14340347 : Blo 2095435 14340347 := bstep (se 1 (by rfl) ⟨10755260, by rfl⟩ : syracuseStep 14340347 = 21510521) B21510521
theorem B9560231 : Blo 2095435 9560231 := bstep (se 1 (by rfl) ⟨7170173, by rfl⟩ : syracuseStep 9560231 = 14340347) B14340347
theorem B6373487 : Blo 2095435 6373487 := bstep (se 1 (by rfl) ⟨4780115, by rfl⟩ : syracuseStep 6373487 = 9560231) B9560231
theorem B4248991 : Blo 2095435 4248991 := bstep (se 1 (by rfl) ⟨3186743, by rfl⟩ : syracuseStep 4248991 = 6373487) B6373487
theorem B5665321 : Blo 2095435 5665321 := bstep (se 2 (by rfl) ⟨2124495, by rfl⟩ : syracuseStep 5665321 = 4248991) B4248991
theorem B30215045 : Blo 2095435 30215045 := bstep (se 4 (by rfl) ⟨2832660, by rfl⟩ : syracuseStep 30215045 = 5665321) B5665321
theorem B20143363 : Blo 2095435 20143363 := bstep (se 1 (by rfl) ⟨15107522, by rfl⟩ : syracuseStep 20143363 = 30215045) B30215045
theorem B26857817 : Blo 2095435 26857817 := bstep (se 2 (by rfl) ⟨10071681, by rfl⟩ : syracuseStep 26857817 = 20143363) B20143363
theorem B17905211 : Blo 2095435 17905211 := bstep (se 1 (by rfl) ⟨13428908, by rfl⟩ : syracuseStep 17905211 = 26857817) B26857817
theorem B11936807 : Blo 2095435 11936807 := bstep (se 1 (by rfl) ⟨8952605, by rfl⟩ : syracuseStep 11936807 = 17905211) B17905211
theorem B7957871 : Blo 2095435 7957871 := bstep (se 1 (by rfl) ⟨5968403, by rfl⟩ : syracuseStep 7957871 = 11936807) B11936807
theorem B5305247 : Blo 2095435 5305247 := bstep (se 1 (by rfl) ⟨3978935, by rfl⟩ : syracuseStep 5305247 = 7957871) B7957871
theorem B3536831 : Blo 2095435 3536831 := bstep (se 1 (by rfl) ⟨2652623, by rfl⟩ : syracuseStep 3536831 = 5305247) B5305247
theorem B2357887 : Blo 2095435 2357887 := bstep (se 1 (by rfl) ⟨1768415, by rfl⟩ : syracuseStep 2357887 = 3536831) B3536831
theorem B3143849 : Blo 2095435 3143849 := bstep (se 2 (by rfl) ⟨1178943, by rfl⟩ : syracuseStep 3143849 = 2357887) B2357887
theorem B2095899 : Blo 2095435 2095899 := bstep (se 1 (by rfl) ⟨1571924, by rfl⟩ : syracuseStep 2095899 = 3143849) B3143849
theorem B10071701 : Blo 2095435 10071701 := bbase (se 6 (by rfl) ⟨236055, by rfl⟩ : syracuseStep 10071701 = 472111) (by norm_num)
theorem B6714467 : Blo 2095435 6714467 := bstep (se 1 (by rfl) ⟨5035850, by rfl⟩ : syracuseStep 6714467 = 10071701) B10071701
theorem B4476311 : Blo 2095435 4476311 := bstep (se 1 (by rfl) ⟨3357233, by rfl⟩ : syracuseStep 4476311 = 6714467) B6714467
theorem B2984207 : Blo 2095435 2984207 := bstep (se 1 (by rfl) ⟨2238155, by rfl⟩ : syracuseStep 2984207 = 4476311) B4476311
theorem B7957885 : Blo 2095435 7957885 := bstep (se 3 (by rfl) ⟨1492103, by rfl⟩ : syracuseStep 7957885 = 2984207) B2984207
theorem B10610513 : Blo 2095435 10610513 := bstep (se 2 (by rfl) ⟨3978942, by rfl⟩ : syracuseStep 10610513 = 7957885) B7957885
theorem B7073675 : Blo 2095435 7073675 := bstep (se 1 (by rfl) ⟨5305256, by rfl⟩ : syracuseStep 7073675 = 10610513) B10610513
theorem B4715783 : Blo 2095435 4715783 := bstep (se 1 (by rfl) ⟨3536837, by rfl⟩ : syracuseStep 4715783 = 7073675) B7073675
theorem B3143855 : Blo 2095435 3143855 := bstep (se 1 (by rfl) ⟨2357891, by rfl⟩ : syracuseStep 3143855 = 4715783) B4715783
theorem B2095903 : Blo 2095435 2095903 := bstep (se 1 (by rfl) ⟨1571927, by rfl⟩ : syracuseStep 2095903 = 3143855) B3143855
theorem B3143861 : Blo 2095435 3143861 := bbase (se 5 (by rfl) ⟨147368, by rfl⟩ : syracuseStep 3143861 = 294737) (by norm_num)
theorem B2095907 : Blo 2095435 2095907 := bstep (se 1 (by rfl) ⟨1571930, by rfl⟩ : syracuseStep 2095907 = 3143861) B3143861
theorem B5305277 : Blo 2095435 5305277 := bbase (se 3 (by rfl) ⟨994739, by rfl⟩ : syracuseStep 5305277 = 1989479) (by norm_num)
theorem B3536851 : Blo 2095435 3536851 := bstep (se 1 (by rfl) ⟨2652638, by rfl⟩ : syracuseStep 3536851 = 5305277) B5305277
theorem B4715801 : Blo 2095435 4715801 := bstep (se 2 (by rfl) ⟨1768425, by rfl⟩ : syracuseStep 4715801 = 3536851) B3536851
theorem B3143867 : Blo 2095435 3143867 := bstep (se 1 (by rfl) ⟨2357900, by rfl⟩ : syracuseStep 3143867 = 4715801) B4715801
theorem B2095911 : Blo 2095435 2095911 := bstep (se 1 (by rfl) ⟨1571933, by rfl⟩ : syracuseStep 2095911 = 3143867) B3143867
theorem B2357905 : Blo 2095435 2357905 := bbase (se 2 (by rfl) ⟨884214, by rfl⟩ : syracuseStep 2357905 = 1768429) (by norm_num)
theorem B3143873 : Blo 2095435 3143873 := bstep (se 2 (by rfl) ⟨1178952, by rfl⟩ : syracuseStep 3143873 = 2357905) B2357905
theorem B2095915 : Blo 2095435 2095915 := bstep (se 1 (by rfl) ⟨1571936, by rfl⟩ : syracuseStep 2095915 = 3143873) B3143873
theorem B3978973 : Blo 2095435 3978973 := bbase (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) (by norm_num)
theorem B5305297 : Blo 2095435 5305297 := bstep (se 2 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 5305297 = 3978973) B3978973
theorem B7073729 : Blo 2095435 7073729 := bstep (se 2 (by rfl) ⟨2652648, by rfl⟩ : syracuseStep 7073729 = 5305297) B5305297
theorem B4715819 : Blo 2095435 4715819 := bstep (se 1 (by rfl) ⟨3536864, by rfl⟩ : syracuseStep 4715819 = 7073729) B7073729
theorem B3143879 : Blo 2095435 3143879 := bstep (se 1 (by rfl) ⟨2357909, by rfl⟩ : syracuseStep 3143879 = 4715819) B4715819
theorem B2095919 : Blo 2095435 2095919 := bstep (se 1 (by rfl) ⟨1571939, by rfl⟩ : syracuseStep 2095919 = 3143879) B3143879
theorem B3143885 : Blo 2095435 3143885 := bbase (se 3 (by rfl) ⟨589478, by rfl⟩ : syracuseStep 3143885 = 1178957) (by norm_num)
theorem B2095923 : Blo 2095435 2095923 := bstep (se 1 (by rfl) ⟨1571942, by rfl⟩ : syracuseStep 2095923 = 3143885) B3143885
theorem B4715837 : Blo 2095435 4715837 := bbase (se 3 (by rfl) ⟨884219, by rfl⟩ : syracuseStep 4715837 = 1768439) (by norm_num)
theorem B3143891 : Blo 2095435 3143891 := bstep (se 1 (by rfl) ⟨2357918, by rfl⟩ : syracuseStep 3143891 = 4715837) B4715837
theorem B2095927 : Blo 2095435 2095927 := bstep (se 1 (by rfl) ⟨1571945, by rfl⟩ : syracuseStep 2095927 = 3143891) B3143891
theorem B3536885 : Blo 2095435 3536885 := bbase (se 5 (by rfl) ⟨165791, by rfl⟩ : syracuseStep 3536885 = 331583) (by norm_num)
theorem B2357923 : Blo 2095435 2357923 := bstep (se 1 (by rfl) ⟨1768442, by rfl⟩ : syracuseStep 2357923 = 3536885) B3536885
theorem B3143897 : Blo 2095435 3143897 := bstep (se 2 (by rfl) ⟨1178961, by rfl⟩ : syracuseStep 3143897 = 2357923) B2357923
theorem B2095931 : Blo 2095435 2095931 := bstep (se 1 (by rfl) ⟨1571948, by rfl⟩ : syracuseStep 2095931 = 3143897) B3143897
theorem B11330837 : Blo 2095435 11330837 := bbase (se 6 (by rfl) ⟨265566, by rfl⟩ : syracuseStep 11330837 = 531133) (by norm_num)
theorem B7553891 : Blo 2095435 7553891 := bstep (se 1 (by rfl) ⟨5665418, by rfl⟩ : syracuseStep 7553891 = 11330837) B11330837
theorem B5035927 : Blo 2095435 5035927 := bstep (se 1 (by rfl) ⟨3776945, by rfl⟩ : syracuseStep 5035927 = 7553891) B7553891
theorem B6714569 : Blo 2095435 6714569 := bstep (se 2 (by rfl) ⟨2517963, by rfl⟩ : syracuseStep 6714569 = 5035927) B5035927
theorem B4476379 : Blo 2095435 4476379 := bstep (se 1 (by rfl) ⟨3357284, by rfl⟩ : syracuseStep 4476379 = 6714569) B6714569
theorem B5968505 : Blo 2095435 5968505 := bstep (se 2 (by rfl) ⟨2238189, by rfl⟩ : syracuseStep 5968505 = 4476379) B4476379
theorem B15916013 : Blo 2095435 15916013 := bstep (se 3 (by rfl) ⟨2984252, by rfl⟩ : syracuseStep 15916013 = 5968505) B5968505
theorem B10610675 : Blo 2095435 10610675 := bstep (se 1 (by rfl) ⟨7958006, by rfl⟩ : syracuseStep 10610675 = 15916013) B15916013
theorem B7073783 : Blo 2095435 7073783 := bstep (se 1 (by rfl) ⟨5305337, by rfl⟩ : syracuseStep 7073783 = 10610675) B10610675
theorem B4715855 : Blo 2095435 4715855 := bstep (se 1 (by rfl) ⟨3536891, by rfl⟩ : syracuseStep 4715855 = 7073783) B7073783
theorem B3143903 : Blo 2095435 3143903 := bstep (se 1 (by rfl) ⟨2357927, by rfl⟩ : syracuseStep 3143903 = 4715855) B4715855
theorem B2095935 : Blo 2095435 2095935 := bstep (se 1 (by rfl) ⟨1571951, by rfl⟩ : syracuseStep 2095935 = 3143903) B3143903
theorem B3143909 : Blo 2095435 3143909 := bbase (se 4 (by rfl) ⟨294741, by rfl⟩ : syracuseStep 3143909 = 589483) (by norm_num)
theorem B2095939 : Blo 2095435 2095939 := bstep (se 1 (by rfl) ⟨1571954, by rfl⟩ : syracuseStep 2095939 = 3143909) B3143909
theorem B4476397 : Blo 2095435 4476397 := bbase (se 3 (by rfl) ⟨839324, by rfl⟩ : syracuseStep 4476397 = 1678649) (by norm_num)
theorem B5968529 : Blo 2095435 5968529 := bstep (se 2 (by rfl) ⟨2238198, by rfl⟩ : syracuseStep 5968529 = 4476397) B4476397
theorem B3979019 : Blo 2095435 3979019 := bstep (se 1 (by rfl) ⟨2984264, by rfl⟩ : syracuseStep 3979019 = 5968529) B5968529
theorem B2652679 : Blo 2095435 2652679 := bstep (se 1 (by rfl) ⟨1989509, by rfl⟩ : syracuseStep 2652679 = 3979019) B3979019
theorem B3536905 : Blo 2095435 3536905 := bstep (se 2 (by rfl) ⟨1326339, by rfl⟩ : syracuseStep 3536905 = 2652679) B2652679
theorem B4715873 : Blo 2095435 4715873 := bstep (se 2 (by rfl) ⟨1768452, by rfl⟩ : syracuseStep 4715873 = 3536905) B3536905
theorem B3143915 : Blo 2095435 3143915 := bstep (se 1 (by rfl) ⟨2357936, by rfl⟩ : syracuseStep 3143915 = 4715873) B4715873
theorem B2095943 : Blo 2095435 2095943 := bstep (se 1 (by rfl) ⟨1571957, by rfl⟩ : syracuseStep 2095943 = 3143915) B3143915
theorem B2357941 : Blo 2095435 2357941 := bbase (se 5 (by rfl) ⟨110528, by rfl⟩ : syracuseStep 2357941 = 221057) (by norm_num)
theorem B3143921 : Blo 2095435 3143921 := bstep (se 2 (by rfl) ⟨1178970, by rfl⟩ : syracuseStep 3143921 = 2357941) B2357941
theorem B2095947 : Blo 2095435 2095947 := bstep (se 1 (by rfl) ⟨1571960, by rfl⟩ : syracuseStep 2095947 = 3143921) B3143921
theorem B2652689 : Blo 2095435 2652689 := bbase (se 2 (by rfl) ⟨994758, by rfl⟩ : syracuseStep 2652689 = 1989517) (by norm_num)
theorem B7073837 : Blo 2095435 7073837 := bstep (se 3 (by rfl) ⟨1326344, by rfl⟩ : syracuseStep 7073837 = 2652689) B2652689
theorem B4715891 : Blo 2095435 4715891 := bstep (se 1 (by rfl) ⟨3536918, by rfl⟩ : syracuseStep 4715891 = 7073837) B7073837
theorem B3143927 : Blo 2095435 3143927 := bstep (se 1 (by rfl) ⟨2357945, by rfl⟩ : syracuseStep 3143927 = 4715891) B4715891
theorem B2095951 : Blo 2095435 2095951 := bstep (se 1 (by rfl) ⟨1571963, by rfl⟩ : syracuseStep 2095951 = 3143927) B3143927
theorem B3143933 : Blo 2095435 3143933 := bbase (se 3 (by rfl) ⟨589487, by rfl⟩ : syracuseStep 3143933 = 1178975) (by norm_num)
theorem B2095955 : Blo 2095435 2095955 := bstep (se 1 (by rfl) ⟨1571966, by rfl⟩ : syracuseStep 2095955 = 3143933) B3143933
theorem B4715909 : Blo 2095435 4715909 := bbase (se 4 (by rfl) ⟨442116, by rfl⟩ : syracuseStep 4715909 = 884233) (by norm_num)
theorem B3143939 : Blo 2095435 3143939 := bstep (se 1 (by rfl) ⟨2357954, by rfl⟩ : syracuseStep 3143939 = 4715909) B4715909
theorem B2095959 : Blo 2095435 2095959 := bstep (se 1 (by rfl) ⟨1571969, by rfl⟩ : syracuseStep 2095959 = 3143939) B3143939
theorem B2984293 : Blo 2095435 2984293 := bbase (se 4 (by rfl) ⟨279777, by rfl⟩ : syracuseStep 2984293 = 559555) (by norm_num)
theorem B3979057 : Blo 2095435 3979057 := bstep (se 2 (by rfl) ⟨1492146, by rfl⟩ : syracuseStep 3979057 = 2984293) B2984293
theorem B5305409 : Blo 2095435 5305409 := bstep (se 2 (by rfl) ⟨1989528, by rfl⟩ : syracuseStep 5305409 = 3979057) B3979057
theorem B3536939 : Blo 2095435 3536939 := bstep (se 1 (by rfl) ⟨2652704, by rfl⟩ : syracuseStep 3536939 = 5305409) B5305409
theorem B2357959 : Blo 2095435 2357959 := bstep (se 1 (by rfl) ⟨1768469, by rfl⟩ : syracuseStep 2357959 = 3536939) B3536939
theorem B3143945 : Blo 2095435 3143945 := bstep (se 2 (by rfl) ⟨1178979, by rfl⟩ : syracuseStep 3143945 = 2357959) B2357959
theorem B2095963 : Blo 2095435 2095963 := bstep (se 1 (by rfl) ⟨1571972, by rfl⟩ : syracuseStep 2095963 = 3143945) B3143945
theorem B10610837 : Blo 2095435 10610837 := bbase (se 6 (by rfl) ⟨248691, by rfl⟩ : syracuseStep 10610837 = 497383) (by norm_num)
theorem B7073891 : Blo 2095435 7073891 := bstep (se 1 (by rfl) ⟨5305418, by rfl⟩ : syracuseStep 7073891 = 10610837) B10610837
theorem B4715927 : Blo 2095435 4715927 := bstep (se 1 (by rfl) ⟨3536945, by rfl⟩ : syracuseStep 4715927 = 7073891) B7073891
theorem B3143951 : Blo 2095435 3143951 := bstep (se 1 (by rfl) ⟨2357963, by rfl⟩ : syracuseStep 3143951 = 4715927) B4715927
theorem B2095967 : Blo 2095435 2095967 := bstep (se 1 (by rfl) ⟨1571975, by rfl⟩ : syracuseStep 2095967 = 3143951) B3143951
theorem B3143957 : Blo 2095435 3143957 := bbase (se 6 (by rfl) ⟨73686, by rfl⟩ : syracuseStep 3143957 = 147373) (by norm_num)
theorem B2095971 : Blo 2095435 2095971 := bstep (se 1 (by rfl) ⟨1571978, by rfl⟩ : syracuseStep 2095971 = 3143957) B3143957
theorem B2688913 : Blo 2095435 2688913 := bbase (se 2 (by rfl) ⟨1008342, by rfl⟩ : syracuseStep 2688913 = 2016685) (by norm_num)
theorem B3585217 : Blo 2095435 3585217 := bstep (se 2 (by rfl) ⟨1344456, by rfl⟩ : syracuseStep 3585217 = 2688913) B2688913
theorem B4780289 : Blo 2095435 4780289 := bstep (se 2 (by rfl) ⟨1792608, by rfl⟩ : syracuseStep 4780289 = 3585217) B3585217
theorem B3186859 : Blo 2095435 3186859 := bstep (se 1 (by rfl) ⟨2390144, by rfl⟩ : syracuseStep 3186859 = 4780289) B4780289
theorem B4249145 : Blo 2095435 4249145 := bstep (se 2 (by rfl) ⟨1593429, by rfl⟩ : syracuseStep 4249145 = 3186859) B3186859
theorem B11331053 : Blo 2095435 11331053 := bstep (se 3 (by rfl) ⟨2124572, by rfl⟩ : syracuseStep 11331053 = 4249145) B4249145
theorem B7554035 : Blo 2095435 7554035 := bstep (se 1 (by rfl) ⟨5665526, by rfl⟩ : syracuseStep 7554035 = 11331053) B11331053
theorem B5036023 : Blo 2095435 5036023 := bstep (se 1 (by rfl) ⟨3777017, by rfl⟩ : syracuseStep 5036023 = 7554035) B7554035
theorem B26858789 : Blo 2095435 26858789 := bstep (se 4 (by rfl) ⟨2518011, by rfl⟩ : syracuseStep 26858789 = 5036023) B5036023
theorem B17905859 : Blo 2095435 17905859 := bstep (se 1 (by rfl) ⟨13429394, by rfl⟩ : syracuseStep 17905859 = 26858789) B26858789
theorem B11937239 : Blo 2095435 11937239 := bstep (se 1 (by rfl) ⟨8952929, by rfl⟩ : syracuseStep 11937239 = 17905859) B17905859
theorem B7958159 : Blo 2095435 7958159 := bstep (se 1 (by rfl) ⟨5968619, by rfl⟩ : syracuseStep 7958159 = 11937239) B11937239
theorem B5305439 : Blo 2095435 5305439 := bstep (se 1 (by rfl) ⟨3979079, by rfl⟩ : syracuseStep 5305439 = 7958159) B7958159
theorem B3536959 : Blo 2095435 3536959 := bstep (se 1 (by rfl) ⟨2652719, by rfl⟩ : syracuseStep 3536959 = 5305439) B5305439
theorem B4715945 : Blo 2095435 4715945 := bstep (se 2 (by rfl) ⟨1768479, by rfl⟩ : syracuseStep 4715945 = 3536959) B3536959
theorem B3143963 : Blo 2095435 3143963 := bstep (se 1 (by rfl) ⟨2357972, by rfl⟩ : syracuseStep 3143963 = 4715945) B4715945
theorem B2095975 : Blo 2095435 2095975 := bstep (se 1 (by rfl) ⟨1571981, by rfl⟩ : syracuseStep 2095975 = 3143963) B3143963
theorem B2357977 : Blo 2095435 2357977 := bbase (se 2 (by rfl) ⟨884241, by rfl⟩ : syracuseStep 2357977 = 1768483) (by norm_num)
theorem B3143969 : Blo 2095435 3143969 := bstep (se 2 (by rfl) ⟨1178988, by rfl⟩ : syracuseStep 3143969 = 2357977) B2357977
theorem B2095979 : Blo 2095435 2095979 := bstep (se 1 (by rfl) ⟨1571984, by rfl⟩ : syracuseStep 2095979 = 3143969) B3143969
theorem B2238241 : Blo 2095435 2238241 := bbase (se 2 (by rfl) ⟨839340, by rfl⟩ : syracuseStep 2238241 = 1678681) (by norm_num)
theorem B2984321 : Blo 2095435 2984321 := bstep (se 2 (by rfl) ⟨1119120, by rfl⟩ : syracuseStep 2984321 = 2238241) B2238241
theorem B7958189 : Blo 2095435 7958189 := bstep (se 3 (by rfl) ⟨1492160, by rfl⟩ : syracuseStep 7958189 = 2984321) B2984321
theorem B5305459 : Blo 2095435 5305459 := bstep (se 1 (by rfl) ⟨3979094, by rfl⟩ : syracuseStep 5305459 = 7958189) B7958189
theorem B7073945 : Blo 2095435 7073945 := bstep (se 2 (by rfl) ⟨2652729, by rfl⟩ : syracuseStep 7073945 = 5305459) B5305459
theorem B4715963 : Blo 2095435 4715963 := bstep (se 1 (by rfl) ⟨3536972, by rfl⟩ : syracuseStep 4715963 = 7073945) B7073945
theorem B3143975 : Blo 2095435 3143975 := bstep (se 1 (by rfl) ⟨2357981, by rfl⟩ : syracuseStep 3143975 = 4715963) B4715963
theorem B2095983 : Blo 2095435 2095983 := bstep (se 1 (by rfl) ⟨1571987, by rfl⟩ : syracuseStep 2095983 = 3143975) B3143975
theorem B3143981 : Blo 2095435 3143981 := bbase (se 3 (by rfl) ⟨589496, by rfl⟩ : syracuseStep 3143981 = 1178993) (by norm_num)
theorem B2095987 : Blo 2095435 2095987 := bstep (se 1 (by rfl) ⟨1571990, by rfl⟩ : syracuseStep 2095987 = 3143981) B3143981
theorem B4715981 : Blo 2095435 4715981 := bbase (se 3 (by rfl) ⟨884246, by rfl⟩ : syracuseStep 4715981 = 1768493) (by norm_num)
theorem B3143987 : Blo 2095435 3143987 := bstep (se 1 (by rfl) ⟨2357990, by rfl⟩ : syracuseStep 3143987 = 4715981) B4715981
theorem B2095991 : Blo 2095435 2095991 := bstep (se 1 (by rfl) ⟨1571993, by rfl⟩ : syracuseStep 2095991 = 3143987) B3143987
theorem B2652745 : Blo 2095435 2652745 := bbase (se 2 (by rfl) ⟨994779, by rfl⟩ : syracuseStep 2652745 = 1989559) (by norm_num)
theorem B3536993 : Blo 2095435 3536993 := bstep (se 2 (by rfl) ⟨1326372, by rfl⟩ : syracuseStep 3536993 = 2652745) B2652745
theorem B2357995 : Blo 2095435 2357995 := bstep (se 1 (by rfl) ⟨1768496, by rfl⟩ : syracuseStep 2357995 = 3536993) B3536993
theorem B3143993 : Blo 2095435 3143993 := bstep (se 2 (by rfl) ⟨1178997, by rfl⟩ : syracuseStep 3143993 = 2357995) B2357995
theorem B2095995 : Blo 2095435 2095995 := bstep (se 1 (by rfl) ⟨1571996, by rfl⟩ : syracuseStep 2095995 = 3143993) B3143993
theorem B6806389 : Blo 2095435 6806389 := bbase (se 5 (by rfl) ⟨319049, by rfl⟩ : syracuseStep 6806389 = 638099) (by norm_num)
theorem B9075185 : Blo 2095435 9075185 := bstep (se 2 (by rfl) ⟨3403194, by rfl⟩ : syracuseStep 9075185 = 6806389) B6806389
theorem B6050123 : Blo 2095435 6050123 := bstep (se 1 (by rfl) ⟨4537592, by rfl⟩ : syracuseStep 6050123 = 9075185) B9075185
theorem B4033415 : Blo 2095435 4033415 := bstep (se 1 (by rfl) ⟨3025061, by rfl⟩ : syracuseStep 4033415 = 6050123) B6050123
theorem B10755773 : Blo 2095435 10755773 := bstep (se 3 (by rfl) ⟨2016707, by rfl⟩ : syracuseStep 10755773 = 4033415) B4033415
theorem B7170515 : Blo 2095435 7170515 := bstep (se 1 (by rfl) ⟨5377886, by rfl⟩ : syracuseStep 7170515 = 10755773) B10755773
theorem B4780343 : Blo 2095435 4780343 := bstep (se 1 (by rfl) ⟨3585257, by rfl⟩ : syracuseStep 4780343 = 7170515) B7170515
theorem B3186895 : Blo 2095435 3186895 := bstep (se 1 (by rfl) ⟨2390171, by rfl⟩ : syracuseStep 3186895 = 4780343) B4780343
theorem B4249193 : Blo 2095435 4249193 := bstep (se 2 (by rfl) ⟨1593447, by rfl⟩ : syracuseStep 4249193 = 3186895) B3186895
theorem B11331181 : Blo 2095435 11331181 := bstep (se 3 (by rfl) ⟨2124596, by rfl⟩ : syracuseStep 11331181 = 4249193) B4249193
theorem B15108241 : Blo 2095435 15108241 := bstep (se 2 (by rfl) ⟨5665590, by rfl⟩ : syracuseStep 15108241 = 11331181) B11331181
theorem B20144321 : Blo 2095435 20144321 := bstep (se 2 (by rfl) ⟨7554120, by rfl⟩ : syracuseStep 20144321 = 15108241) B15108241
theorem B13429547 : Blo 2095435 13429547 := bstep (se 1 (by rfl) ⟨10072160, by rfl⟩ : syracuseStep 13429547 = 20144321) B20144321
theorem B8953031 : Blo 2095435 8953031 := bstep (se 1 (by rfl) ⟨6714773, by rfl⟩ : syracuseStep 8953031 = 13429547) B13429547
theorem B23874749 : Blo 2095435 23874749 := bstep (se 3 (by rfl) ⟨4476515, by rfl⟩ : syracuseStep 23874749 = 8953031) B8953031
theorem B15916499 : Blo 2095435 15916499 := bstep (se 1 (by rfl) ⟨11937374, by rfl⟩ : syracuseStep 15916499 = 23874749) B23874749
theorem B10610999 : Blo 2095435 10610999 := bstep (se 1 (by rfl) ⟨7958249, by rfl⟩ : syracuseStep 10610999 = 15916499) B15916499
theorem B7073999 : Blo 2095435 7073999 := bstep (se 1 (by rfl) ⟨5305499, by rfl⟩ : syracuseStep 7073999 = 10610999) B10610999
theorem B4715999 : Blo 2095435 4715999 := bstep (se 1 (by rfl) ⟨3536999, by rfl⟩ : syracuseStep 4715999 = 7073999) B7073999
theorem B3143999 : Blo 2095435 3143999 := bstep (se 1 (by rfl) ⟨2357999, by rfl⟩ : syracuseStep 3143999 = 4715999) B4715999
theorem B2095999 : Blo 2095435 2095999 := bstep (se 1 (by rfl) ⟨1571999, by rfl⟩ : syracuseStep 2095999 = 3143999) B3143999
theorem B3144005 : Blo 2095435 3144005 := bbase (se 4 (by rfl) ⟨294750, by rfl⟩ : syracuseStep 3144005 = 589501) (by norm_num)
theorem B2096003 : Blo 2095435 2096003 := bstep (se 1 (by rfl) ⟨1572002, by rfl⟩ : syracuseStep 2096003 = 3144005) B3144005
theorem B3537013 : Blo 2095435 3537013 := bbase (se 5 (by rfl) ⟨165797, by rfl⟩ : syracuseStep 3537013 = 331595) (by norm_num)
theorem B4716017 : Blo 2095435 4716017 := bstep (se 2 (by rfl) ⟨1768506, by rfl⟩ : syracuseStep 4716017 = 3537013) B3537013
theorem B3144011 : Blo 2095435 3144011 := bstep (se 1 (by rfl) ⟨2358008, by rfl⟩ : syracuseStep 3144011 = 4716017) B4716017
theorem B2096007 : Blo 2095435 2096007 := bstep (se 1 (by rfl) ⟨1572005, by rfl⟩ : syracuseStep 2096007 = 3144011) B3144011
theorem B2358013 : Blo 2095435 2358013 := bbase (se 3 (by rfl) ⟨442127, by rfl⟩ : syracuseStep 2358013 = 884255) (by norm_num)
theorem B3144017 : Blo 2095435 3144017 := bstep (se 2 (by rfl) ⟨1179006, by rfl⟩ : syracuseStep 3144017 = 2358013) B2358013
theorem B2096011 : Blo 2095435 2096011 := bstep (se 1 (by rfl) ⟨1572008, by rfl⟩ : syracuseStep 2096011 = 3144017) B3144017
theorem B7074053 : Blo 2095435 7074053 := bbase (se 4 (by rfl) ⟨663192, by rfl⟩ : syracuseStep 7074053 = 1326385) (by norm_num)
theorem B4716035 : Blo 2095435 4716035 := bstep (se 1 (by rfl) ⟨3537026, by rfl⟩ : syracuseStep 4716035 = 7074053) B7074053
theorem B3144023 : Blo 2095435 3144023 := bstep (se 1 (by rfl) ⟨2358017, by rfl⟩ : syracuseStep 3144023 = 4716035) B4716035
theorem B2096015 : Blo 2095435 2096015 := bstep (se 1 (by rfl) ⟨1572011, by rfl⟩ : syracuseStep 2096015 = 3144023) B3144023
theorem B3144029 : Blo 2095435 3144029 := bbase (se 3 (by rfl) ⟨589505, by rfl⟩ : syracuseStep 3144029 = 1179011) (by norm_num)
theorem B2096019 : Blo 2095435 2096019 := bstep (se 1 (by rfl) ⟨1572014, by rfl⟩ : syracuseStep 2096019 = 3144029) B3144029
theorem B4716053 : Blo 2095435 4716053 := bbase (se 6 (by rfl) ⟨110532, by rfl⟩ : syracuseStep 4716053 = 221065) (by norm_num)
theorem B3144035 : Blo 2095435 3144035 := bstep (se 1 (by rfl) ⟨2358026, by rfl⟩ : syracuseStep 3144035 = 4716053) B4716053
theorem B2096023 : Blo 2095435 2096023 := bstep (se 1 (by rfl) ⟨1572017, by rfl⟩ : syracuseStep 2096023 = 3144035) B3144035
theorem B7958357 : Blo 2095435 7958357 := bbase (se 9 (by rfl) ⟨23315, by rfl⟩ : syracuseStep 7958357 = 46631) (by norm_num)
theorem B5305571 : Blo 2095435 5305571 := bstep (se 1 (by rfl) ⟨3979178, by rfl⟩ : syracuseStep 5305571 = 7958357) B7958357
theorem B3537047 : Blo 2095435 3537047 := bstep (se 1 (by rfl) ⟨2652785, by rfl⟩ : syracuseStep 3537047 = 5305571) B5305571
theorem B2358031 : Blo 2095435 2358031 := bstep (se 1 (by rfl) ⟨1768523, by rfl⟩ : syracuseStep 2358031 = 3537047) B3537047
theorem B3144041 : Blo 2095435 3144041 := bstep (se 2 (by rfl) ⟨1179015, by rfl⟩ : syracuseStep 3144041 = 2358031) B2358031
theorem B2096027 : Blo 2095435 2096027 := bstep (se 1 (by rfl) ⟨1572020, by rfl⟩ : syracuseStep 2096027 = 3144041) B3144041
theorem B11937557 : Blo 2095435 11937557 := bbase (se 6 (by rfl) ⟨279786, by rfl⟩ : syracuseStep 11937557 = 559573) (by norm_num)
theorem B7958371 : Blo 2095435 7958371 := bstep (se 1 (by rfl) ⟨5968778, by rfl⟩ : syracuseStep 7958371 = 11937557) B11937557
theorem B10611161 : Blo 2095435 10611161 := bstep (se 2 (by rfl) ⟨3979185, by rfl⟩ : syracuseStep 10611161 = 7958371) B7958371
theorem B7074107 : Blo 2095435 7074107 := bstep (se 1 (by rfl) ⟨5305580, by rfl⟩ : syracuseStep 7074107 = 10611161) B10611161
theorem B4716071 : Blo 2095435 4716071 := bstep (se 1 (by rfl) ⟨3537053, by rfl⟩ : syracuseStep 4716071 = 7074107) B7074107
theorem B3144047 : Blo 2095435 3144047 := bstep (se 1 (by rfl) ⟨2358035, by rfl⟩ : syracuseStep 3144047 = 4716071) B4716071
theorem B2096031 : Blo 2095435 2096031 := bstep (se 1 (by rfl) ⟨1572023, by rfl⟩ : syracuseStep 2096031 = 3144047) B3144047
theorem B3144053 : Blo 2095435 3144053 := bbase (se 5 (by rfl) ⟨147377, by rfl⟩ : syracuseStep 3144053 = 294755) (by norm_num)
theorem B2096035 : Blo 2095435 2096035 := bstep (se 1 (by rfl) ⟨1572026, by rfl⟩ : syracuseStep 2096035 = 3144053) B3144053
theorem B2238301 : Blo 2095435 2238301 := bbase (se 3 (by rfl) ⟨419681, by rfl⟩ : syracuseStep 2238301 = 839363) (by norm_num)
theorem B2984401 : Blo 2095435 2984401 := bstep (se 2 (by rfl) ⟨1119150, by rfl⟩ : syracuseStep 2984401 = 2238301) B2238301
theorem B3979201 : Blo 2095435 3979201 := bstep (se 2 (by rfl) ⟨1492200, by rfl⟩ : syracuseStep 3979201 = 2984401) B2984401
theorem B5305601 : Blo 2095435 5305601 := bstep (se 2 (by rfl) ⟨1989600, by rfl⟩ : syracuseStep 5305601 = 3979201) B3979201
theorem B3537067 : Blo 2095435 3537067 := bstep (se 1 (by rfl) ⟨2652800, by rfl⟩ : syracuseStep 3537067 = 5305601) B5305601
theorem B4716089 : Blo 2095435 4716089 := bstep (se 2 (by rfl) ⟨1768533, by rfl⟩ : syracuseStep 4716089 = 3537067) B3537067
theorem B3144059 : Blo 2095435 3144059 := bstep (se 1 (by rfl) ⟨2358044, by rfl⟩ : syracuseStep 3144059 = 4716089) B4716089
theorem B2096039 : Blo 2095435 2096039 := bstep (se 1 (by rfl) ⟨1572029, by rfl⟩ : syracuseStep 2096039 = 3144059) B3144059
theorem B2358049 : Blo 2095435 2358049 := bbase (se 2 (by rfl) ⟨884268, by rfl⟩ : syracuseStep 2358049 = 1768537) (by norm_num)
theorem B3144065 : Blo 2095435 3144065 := bstep (se 2 (by rfl) ⟨1179024, by rfl⟩ : syracuseStep 3144065 = 2358049) B2358049
theorem B2096043 : Blo 2095435 2096043 := bstep (se 1 (by rfl) ⟨1572032, by rfl⟩ : syracuseStep 2096043 = 3144065) B3144065
theorem B5305621 : Blo 2095435 5305621 := bbase (se 6 (by rfl) ⟨124350, by rfl⟩ : syracuseStep 5305621 = 248701) (by norm_num)
theorem B7074161 : Blo 2095435 7074161 := bstep (se 2 (by rfl) ⟨2652810, by rfl⟩ : syracuseStep 7074161 = 5305621) B5305621
theorem B4716107 : Blo 2095435 4716107 := bstep (se 1 (by rfl) ⟨3537080, by rfl⟩ : syracuseStep 4716107 = 7074161) B7074161
theorem B3144071 : Blo 2095435 3144071 := bstep (se 1 (by rfl) ⟨2358053, by rfl⟩ : syracuseStep 3144071 = 4716107) B4716107
theorem B2096047 : Blo 2095435 2096047 := bstep (se 1 (by rfl) ⟨1572035, by rfl⟩ : syracuseStep 2096047 = 3144071) B3144071
theorem B3144077 : Blo 2095435 3144077 := bbase (se 3 (by rfl) ⟨589514, by rfl⟩ : syracuseStep 3144077 = 1179029) (by norm_num)
theorem B2096051 : Blo 2095435 2096051 := bstep (se 1 (by rfl) ⟨1572038, by rfl⟩ : syracuseStep 2096051 = 3144077) B3144077
theorem B4716125 : Blo 2095435 4716125 := bbase (se 3 (by rfl) ⟨884273, by rfl⟩ : syracuseStep 4716125 = 1768547) (by norm_num)
theorem B3144083 : Blo 2095435 3144083 := bstep (se 1 (by rfl) ⟨2358062, by rfl⟩ : syracuseStep 3144083 = 4716125) B4716125
theorem B2096055 : Blo 2095435 2096055 := bstep (se 1 (by rfl) ⟨1572041, by rfl⟩ : syracuseStep 2096055 = 3144083) B3144083
theorem B3537101 : Blo 2095435 3537101 := bbase (se 3 (by rfl) ⟨663206, by rfl⟩ : syracuseStep 3537101 = 1326413) (by norm_num)
theorem B2358067 : Blo 2095435 2358067 := bstep (se 1 (by rfl) ⟨1768550, by rfl⟩ : syracuseStep 2358067 = 3537101) B3537101
theorem B3144089 : Blo 2095435 3144089 := bstep (se 2 (by rfl) ⟨1179033, by rfl⟩ : syracuseStep 3144089 = 2358067) B2358067
theorem B2096059 : Blo 2095435 2096059 := bstep (se 1 (by rfl) ⟨1572044, by rfl⟩ : syracuseStep 2096059 = 3144089) B3144089
theorem B2518117 : Blo 2095435 2518117 := bbase (se 4 (by rfl) ⟨236073, by rfl⟩ : syracuseStep 2518117 = 472147) (by norm_num)
theorem B13429957 : Blo 2095435 13429957 := bstep (se 4 (by rfl) ⟨1259058, by rfl⟩ : syracuseStep 13429957 = 2518117) B2518117
theorem B17906609 : Blo 2095435 17906609 := bstep (se 2 (by rfl) ⟨6714978, by rfl⟩ : syracuseStep 17906609 = 13429957) B13429957
theorem B11937739 : Blo 2095435 11937739 := bstep (se 1 (by rfl) ⟨8953304, by rfl⟩ : syracuseStep 11937739 = 17906609) B17906609
theorem B15916985 : Blo 2095435 15916985 := bstep (se 2 (by rfl) ⟨5968869, by rfl⟩ : syracuseStep 15916985 = 11937739) B11937739
theorem B10611323 : Blo 2095435 10611323 := bstep (se 1 (by rfl) ⟨7958492, by rfl⟩ : syracuseStep 10611323 = 15916985) B15916985
theorem B7074215 : Blo 2095435 7074215 := bstep (se 1 (by rfl) ⟨5305661, by rfl⟩ : syracuseStep 7074215 = 10611323) B10611323
theorem B4716143 : Blo 2095435 4716143 := bstep (se 1 (by rfl) ⟨3537107, by rfl⟩ : syracuseStep 4716143 = 7074215) B7074215
theorem B3144095 : Blo 2095435 3144095 := bstep (se 1 (by rfl) ⟨2358071, by rfl⟩ : syracuseStep 3144095 = 4716143) B4716143
theorem B2096063 : Blo 2095435 2096063 := bstep (se 1 (by rfl) ⟨1572047, by rfl⟩ : syracuseStep 2096063 = 3144095) B3144095
theorem B3144101 : Blo 2095435 3144101 := bbase (se 4 (by rfl) ⟨294759, by rfl⟩ : syracuseStep 3144101 = 589519) (by norm_num)
theorem B2096067 : Blo 2095435 2096067 := bstep (se 1 (by rfl) ⟨1572050, by rfl⟩ : syracuseStep 2096067 = 3144101) B3144101
theorem B2652841 : Blo 2095435 2652841 := bbase (se 2 (by rfl) ⟨994815, by rfl⟩ : syracuseStep 2652841 = 1989631) (by norm_num)
theorem B3537121 : Blo 2095435 3537121 := bstep (se 2 (by rfl) ⟨1326420, by rfl⟩ : syracuseStep 3537121 = 2652841) B2652841
theorem B4716161 : Blo 2095435 4716161 := bstep (se 2 (by rfl) ⟨1768560, by rfl⟩ : syracuseStep 4716161 = 3537121) B3537121
theorem B3144107 : Blo 2095435 3144107 := bstep (se 1 (by rfl) ⟨2358080, by rfl⟩ : syracuseStep 3144107 = 4716161) B4716161
theorem B2096071 : Blo 2095435 2096071 := bstep (se 1 (by rfl) ⟨1572053, by rfl⟩ : syracuseStep 2096071 = 3144107) B3144107
theorem B2358085 : Blo 2095435 2358085 := bbase (se 4 (by rfl) ⟨221070, by rfl⟩ : syracuseStep 2358085 = 442141) (by norm_num)
theorem B3144113 : Blo 2095435 3144113 := bstep (se 2 (by rfl) ⟨1179042, by rfl⟩ : syracuseStep 3144113 = 2358085) B2358085
theorem B2096075 : Blo 2095435 2096075 := bstep (se 1 (by rfl) ⟨1572056, by rfl⟩ : syracuseStep 2096075 = 3144113) B3144113
theorem B3979277 : Blo 2095435 3979277 := bbase (se 3 (by rfl) ⟨746114, by rfl⟩ : syracuseStep 3979277 = 1492229) (by norm_num)
theorem B2652851 : Blo 2095435 2652851 := bstep (se 1 (by rfl) ⟨1989638, by rfl⟩ : syracuseStep 2652851 = 3979277) B3979277
theorem B7074269 : Blo 2095435 7074269 := bstep (se 3 (by rfl) ⟨1326425, by rfl⟩ : syracuseStep 7074269 = 2652851) B2652851
theorem B4716179 : Blo 2095435 4716179 := bstep (se 1 (by rfl) ⟨3537134, by rfl⟩ : syracuseStep 4716179 = 7074269) B7074269
theorem B3144119 : Blo 2095435 3144119 := bstep (se 1 (by rfl) ⟨2358089, by rfl⟩ : syracuseStep 3144119 = 4716179) B4716179
theorem B2096079 : Blo 2095435 2096079 := bstep (se 1 (by rfl) ⟨1572059, by rfl⟩ : syracuseStep 2096079 = 3144119) B3144119
theorem B3144125 : Blo 2095435 3144125 := bbase (se 3 (by rfl) ⟨589523, by rfl⟩ : syracuseStep 3144125 = 1179047) (by norm_num)
theorem B2096083 : Blo 2095435 2096083 := bstep (se 1 (by rfl) ⟨1572062, by rfl⟩ : syracuseStep 2096083 = 3144125) B3144125
theorem B4716197 : Blo 2095435 4716197 := bbase (se 4 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 4716197 = 884287) (by norm_num)
theorem B3144131 : Blo 2095435 3144131 := bstep (se 1 (by rfl) ⟨2358098, by rfl⟩ : syracuseStep 3144131 = 4716197) B4716197
theorem B2096087 : Blo 2095435 2096087 := bstep (se 1 (by rfl) ⟨1572065, by rfl⟩ : syracuseStep 2096087 = 3144131) B3144131
theorem B5305733 : Blo 2095435 5305733 := bbase (se 4 (by rfl) ⟨497412, by rfl⟩ : syracuseStep 5305733 = 994825) (by norm_num)
theorem B3537155 : Blo 2095435 3537155 := bstep (se 1 (by rfl) ⟨2652866, by rfl⟩ : syracuseStep 3537155 = 5305733) B5305733
theorem B2358103 : Blo 2095435 2358103 := bstep (se 1 (by rfl) ⟨1768577, by rfl⟩ : syracuseStep 2358103 = 3537155) B3537155
theorem B3144137 : Blo 2095435 3144137 := bstep (se 2 (by rfl) ⟨1179051, by rfl⟩ : syracuseStep 3144137 = 2358103) B2358103
theorem B2096091 : Blo 2095435 2096091 := bstep (se 1 (by rfl) ⟨1572068, by rfl⟩ : syracuseStep 2096091 = 3144137) B3144137
theorem B3357541 : Blo 2095435 3357541 := bbase (se 4 (by rfl) ⟨314769, by rfl⟩ : syracuseStep 3357541 = 629539) (by norm_num)
theorem B4476721 : Blo 2095435 4476721 := bstep (se 2 (by rfl) ⟨1678770, by rfl⟩ : syracuseStep 4476721 = 3357541) B3357541
theorem B5968961 : Blo 2095435 5968961 := bstep (se 2 (by rfl) ⟨2238360, by rfl⟩ : syracuseStep 5968961 = 4476721) B4476721
theorem B3979307 : Blo 2095435 3979307 := bstep (se 1 (by rfl) ⟨2984480, by rfl⟩ : syracuseStep 3979307 = 5968961) B5968961
theorem B10611485 : Blo 2095435 10611485 := bstep (se 3 (by rfl) ⟨1989653, by rfl⟩ : syracuseStep 10611485 = 3979307) B3979307
theorem B7074323 : Blo 2095435 7074323 := bstep (se 1 (by rfl) ⟨5305742, by rfl⟩ : syracuseStep 7074323 = 10611485) B10611485
theorem B4716215 : Blo 2095435 4716215 := bstep (se 1 (by rfl) ⟨3537161, by rfl⟩ : syracuseStep 4716215 = 7074323) B7074323
theorem B3144143 : Blo 2095435 3144143 := bstep (se 1 (by rfl) ⟨2358107, by rfl⟩ : syracuseStep 3144143 = 4716215) B4716215
theorem B2096095 : Blo 2095435 2096095 := bstep (se 1 (by rfl) ⟨1572071, by rfl⟩ : syracuseStep 2096095 = 3144143) B3144143
theorem B3144149 : Blo 2095435 3144149 := bbase (se 7 (by rfl) ⟨36845, by rfl⟩ : syracuseStep 3144149 = 73691) (by norm_num)
theorem B2096099 : Blo 2095435 2096099 := bstep (se 1 (by rfl) ⟨1572074, by rfl⟩ : syracuseStep 2096099 = 3144149) B3144149
theorem B7958645 : Blo 2095435 7958645 := bbase (se 5 (by rfl) ⟨373061, by rfl⟩ : syracuseStep 7958645 = 746123) (by norm_num)
theorem B5305763 : Blo 2095435 5305763 := bstep (se 1 (by rfl) ⟨3979322, by rfl⟩ : syracuseStep 5305763 = 7958645) B7958645
theorem B3537175 : Blo 2095435 3537175 := bstep (se 1 (by rfl) ⟨2652881, by rfl⟩ : syracuseStep 3537175 = 5305763) B5305763
theorem B4716233 : Blo 2095435 4716233 := bstep (se 2 (by rfl) ⟨1768587, by rfl⟩ : syracuseStep 4716233 = 3537175) B3537175
theorem B3144155 : Blo 2095435 3144155 := bstep (se 1 (by rfl) ⟨2358116, by rfl⟩ : syracuseStep 3144155 = 4716233) B4716233
theorem B2096103 : Blo 2095435 2096103 := bstep (se 1 (by rfl) ⟨1572077, by rfl⟩ : syracuseStep 2096103 = 3144155) B3144155
theorem B2358121 : Blo 2095435 2358121 := bbase (se 2 (by rfl) ⟨884295, by rfl⟩ : syracuseStep 2358121 = 1768591) (by norm_num)
theorem B3144161 : Blo 2095435 3144161 := bstep (se 2 (by rfl) ⟨1179060, by rfl⟩ : syracuseStep 3144161 = 2358121) B2358121
theorem B2096107 : Blo 2095435 2096107 := bstep (se 1 (by rfl) ⟨1572080, by rfl⟩ : syracuseStep 2096107 = 3144161) B3144161
theorem B4599749 : Blo 2095435 4599749 := bbase (se 4 (by rfl) ⟨431226, by rfl⟩ : syracuseStep 4599749 = 862453) (by norm_num)
theorem B3066499 : Blo 2095435 3066499 := bstep (se 1 (by rfl) ⟨2299874, by rfl⟩ : syracuseStep 3066499 = 4599749) B4599749
theorem B4088665 : Blo 2095435 4088665 := bstep (se 2 (by rfl) ⟨1533249, by rfl⟩ : syracuseStep 4088665 = 3066499) B3066499
theorem B5451553 : Blo 2095435 5451553 := bstep (se 2 (by rfl) ⟨2044332, by rfl⟩ : syracuseStep 5451553 = 4088665) B4088665
theorem B7268737 : Blo 2095435 7268737 := bstep (se 2 (by rfl) ⟨2725776, by rfl⟩ : syracuseStep 7268737 = 5451553) B5451553
theorem B9691649 : Blo 2095435 9691649 := bstep (se 2 (by rfl) ⟨3634368, by rfl⟩ : syracuseStep 9691649 = 7268737) B7268737
theorem B6461099 : Blo 2095435 6461099 := bstep (se 1 (by rfl) ⟨4845824, by rfl⟩ : syracuseStep 6461099 = 9691649) B9691649
theorem B4307399 : Blo 2095435 4307399 := bstep (se 1 (by rfl) ⟨3230549, by rfl⟩ : syracuseStep 4307399 = 6461099) B6461099
theorem B2871599 : Blo 2095435 2871599 := bstep (se 1 (by rfl) ⟨2153699, by rfl⟩ : syracuseStep 2871599 = 4307399) B4307399
theorem B7657597 : Blo 2095435 7657597 := bstep (se 3 (by rfl) ⟨1435799, by rfl⟩ : syracuseStep 7657597 = 2871599) B2871599
theorem B40840517 : Blo 2095435 40840517 := bstep (se 4 (by rfl) ⟨3828798, by rfl⟩ : syracuseStep 40840517 = 7657597) B7657597
theorem B27227011 : Blo 2095435 27227011 := bstep (se 1 (by rfl) ⟨20420258, by rfl⟩ : syracuseStep 27227011 = 40840517) B40840517
theorem B36302681 : Blo 2095435 36302681 := bstep (se 2 (by rfl) ⟨13613505, by rfl⟩ : syracuseStep 36302681 = 27227011) B27227011
theorem B24201787 : Blo 2095435 24201787 := bstep (se 1 (by rfl) ⟨18151340, by rfl⟩ : syracuseStep 24201787 = 36302681) B36302681
theorem B32269049 : Blo 2095435 32269049 := bstep (se 2 (by rfl) ⟨12100893, by rfl⟩ : syracuseStep 32269049 = 24201787) B24201787
theorem B21512699 : Blo 2095435 21512699 := bstep (se 1 (by rfl) ⟨16134524, by rfl⟩ : syracuseStep 21512699 = 32269049) B32269049
theorem B14341799 : Blo 2095435 14341799 := bstep (se 1 (by rfl) ⟨10756349, by rfl⟩ : syracuseStep 14341799 = 21512699) B21512699
theorem B9561199 : Blo 2095435 9561199 := bstep (se 1 (by rfl) ⟨7170899, by rfl⟩ : syracuseStep 9561199 = 14341799) B14341799
theorem B12748265 : Blo 2095435 12748265 := bstep (se 2 (by rfl) ⟨4780599, by rfl⟩ : syracuseStep 12748265 = 9561199) B9561199
theorem B8498843 : Blo 2095435 8498843 := bstep (se 1 (by rfl) ⟨6374132, by rfl⟩ : syracuseStep 8498843 = 12748265) B12748265
theorem B5665895 : Blo 2095435 5665895 := bstep (se 1 (by rfl) ⟨4249421, by rfl⟩ : syracuseStep 5665895 = 8498843) B8498843
theorem B3777263 : Blo 2095435 3777263 := bstep (se 1 (by rfl) ⟨2832947, by rfl⟩ : syracuseStep 3777263 = 5665895) B5665895
theorem B2518175 : Blo 2095435 2518175 := bstep (se 1 (by rfl) ⟨1888631, by rfl⟩ : syracuseStep 2518175 = 3777263) B3777263
theorem B6715133 : Blo 2095435 6715133 := bstep (se 3 (by rfl) ⟨1259087, by rfl⟩ : syracuseStep 6715133 = 2518175) B2518175
theorem B4476755 : Blo 2095435 4476755 := bstep (se 1 (by rfl) ⟨3357566, by rfl⟩ : syracuseStep 4476755 = 6715133) B6715133
theorem B11938013 : Blo 2095435 11938013 := bstep (se 3 (by rfl) ⟨2238377, by rfl⟩ : syracuseStep 11938013 = 4476755) B4476755
theorem B7958675 : Blo 2095435 7958675 := bstep (se 1 (by rfl) ⟨5969006, by rfl⟩ : syracuseStep 7958675 = 11938013) B11938013
theorem B5305783 : Blo 2095435 5305783 := bstep (se 1 (by rfl) ⟨3979337, by rfl⟩ : syracuseStep 5305783 = 7958675) B7958675
theorem B7074377 : Blo 2095435 7074377 := bstep (se 2 (by rfl) ⟨2652891, by rfl⟩ : syracuseStep 7074377 = 5305783) B5305783
theorem B4716251 : Blo 2095435 4716251 := bstep (se 1 (by rfl) ⟨3537188, by rfl⟩ : syracuseStep 4716251 = 7074377) B7074377
theorem B3144167 : Blo 2095435 3144167 := bstep (se 1 (by rfl) ⟨2358125, by rfl⟩ : syracuseStep 3144167 = 4716251) B4716251
theorem B2096111 : Blo 2095435 2096111 := bstep (se 1 (by rfl) ⟨1572083, by rfl⟩ : syracuseStep 2096111 = 3144167) B3144167
theorem B3144173 : Blo 2095435 3144173 := bbase (se 3 (by rfl) ⟨589532, by rfl⟩ : syracuseStep 3144173 = 1179065) (by norm_num)
theorem B2096115 : Blo 2095435 2096115 := bstep (se 1 (by rfl) ⟨1572086, by rfl⟩ : syracuseStep 2096115 = 3144173) B3144173
theorem B4716269 : Blo 2095435 4716269 := bbase (se 3 (by rfl) ⟨884300, by rfl⟩ : syracuseStep 4716269 = 1768601) (by norm_num)
theorem B3144179 : Blo 2095435 3144179 := bstep (se 1 (by rfl) ⟨2358134, by rfl⟩ : syracuseStep 3144179 = 4716269) B4716269
theorem B2096119 : Blo 2095435 2096119 := bstep (se 1 (by rfl) ⟨1572089, by rfl⟩ : syracuseStep 2096119 = 3144179) B3144179
theorem B5036381 : Blo 2095435 5036381 := bbase (se 3 (by rfl) ⟨944321, by rfl⟩ : syracuseStep 5036381 = 1888643) (by norm_num)
theorem B3357587 : Blo 2095435 3357587 := bstep (se 1 (by rfl) ⟨2518190, by rfl⟩ : syracuseStep 3357587 = 5036381) B5036381
theorem B2238391 : Blo 2095435 2238391 := bstep (se 1 (by rfl) ⟨1678793, by rfl⟩ : syracuseStep 2238391 = 3357587) B3357587
theorem B2984521 : Blo 2095435 2984521 := bstep (se 2 (by rfl) ⟨1119195, by rfl⟩ : syracuseStep 2984521 = 2238391) B2238391
theorem B3979361 : Blo 2095435 3979361 := bstep (se 2 (by rfl) ⟨1492260, by rfl⟩ : syracuseStep 3979361 = 2984521) B2984521
theorem B2652907 : Blo 2095435 2652907 := bstep (se 1 (by rfl) ⟨1989680, by rfl⟩ : syracuseStep 2652907 = 3979361) B3979361
theorem B3537209 : Blo 2095435 3537209 := bstep (se 2 (by rfl) ⟨1326453, by rfl⟩ : syracuseStep 3537209 = 2652907) B2652907
theorem B2358139 : Blo 2095435 2358139 := bstep (se 1 (by rfl) ⟨1768604, by rfl⟩ : syracuseStep 2358139 = 3537209) B3537209
theorem B3144185 : Blo 2095435 3144185 := bstep (se 2 (by rfl) ⟨1179069, by rfl⟩ : syracuseStep 3144185 = 2358139) B2358139
theorem B2096123 : Blo 2095435 2096123 := bstep (se 1 (by rfl) ⟨1572092, by rfl⟩ : syracuseStep 2096123 = 3144185) B3144185
theorem B5378213 : Blo 2095435 5378213 := bbase (se 4 (by rfl) ⟨504207, by rfl⟩ : syracuseStep 5378213 = 1008415) (by norm_num)
theorem B14341901 : Blo 2095435 14341901 := bstep (se 3 (by rfl) ⟨2689106, by rfl⟩ : syracuseStep 14341901 = 5378213) B5378213
theorem B38245069 : Blo 2095435 38245069 := bstep (se 3 (by rfl) ⟨7170950, by rfl⟩ : syracuseStep 38245069 = 14341901) B14341901
theorem B50993425 : Blo 2095435 50993425 := bstep (se 2 (by rfl) ⟨19122534, by rfl⟩ : syracuseStep 50993425 = 38245069) B38245069
theorem B67991233 : Blo 2095435 67991233 := bstep (se 2 (by rfl) ⟨25496712, by rfl⟩ : syracuseStep 67991233 = 50993425) B50993425
theorem B90654977 : Blo 2095435 90654977 := bstep (se 2 (by rfl) ⟨33995616, by rfl⟩ : syracuseStep 90654977 = 67991233) B67991233
theorem B60436651 : Blo 2095435 60436651 := bstep (se 1 (by rfl) ⟨45327488, by rfl⟩ : syracuseStep 60436651 = 90654977) B90654977
theorem B80582201 : Blo 2095435 80582201 := bstep (se 2 (by rfl) ⟨30218325, by rfl⟩ : syracuseStep 80582201 = 60436651) B60436651
theorem B53721467 : Blo 2095435 53721467 := bstep (se 1 (by rfl) ⟨40291100, by rfl⟩ : syracuseStep 53721467 = 80582201) B80582201
theorem B35814311 : Blo 2095435 35814311 := bstep (se 1 (by rfl) ⟨26860733, by rfl⟩ : syracuseStep 35814311 = 53721467) B53721467
theorem B23876207 : Blo 2095435 23876207 := bstep (se 1 (by rfl) ⟨17907155, by rfl⟩ : syracuseStep 23876207 = 35814311) B35814311
theorem B15917471 : Blo 2095435 15917471 := bstep (se 1 (by rfl) ⟨11938103, by rfl⟩ : syracuseStep 15917471 = 23876207) B23876207
theorem B10611647 : Blo 2095435 10611647 := bstep (se 1 (by rfl) ⟨7958735, by rfl⟩ : syracuseStep 10611647 = 15917471) B15917471
theorem B7074431 : Blo 2095435 7074431 := bstep (se 1 (by rfl) ⟨5305823, by rfl⟩ : syracuseStep 7074431 = 10611647) B10611647
theorem B4716287 : Blo 2095435 4716287 := bstep (se 1 (by rfl) ⟨3537215, by rfl⟩ : syracuseStep 4716287 = 7074431) B7074431
theorem B3144191 : Blo 2095435 3144191 := bstep (se 1 (by rfl) ⟨2358143, by rfl⟩ : syracuseStep 3144191 = 4716287) B4716287
theorem B2096127 : Blo 2095435 2096127 := bstep (se 1 (by rfl) ⟨1572095, by rfl⟩ : syracuseStep 2096127 = 3144191) B3144191
theorem B3144197 : Blo 2095435 3144197 := bbase (se 4 (by rfl) ⟨294768, by rfl⟩ : syracuseStep 3144197 = 589537) (by norm_num)
theorem B2096131 : Blo 2095435 2096131 := bstep (se 1 (by rfl) ⟨1572098, by rfl⟩ : syracuseStep 2096131 = 3144197) B3144197
theorem B3537229 : Blo 2095435 3537229 := bbase (se 3 (by rfl) ⟨663230, by rfl⟩ : syracuseStep 3537229 = 1326461) (by norm_num)
theorem B4716305 : Blo 2095435 4716305 := bstep (se 2 (by rfl) ⟨1768614, by rfl⟩ : syracuseStep 4716305 = 3537229) B3537229
theorem B3144203 : Blo 2095435 3144203 := bstep (se 1 (by rfl) ⟨2358152, by rfl⟩ : syracuseStep 3144203 = 4716305) B4716305
theorem B2096135 : Blo 2095435 2096135 := bstep (se 1 (by rfl) ⟨1572101, by rfl⟩ : syracuseStep 2096135 = 3144203) B3144203
theorem B2358157 : Blo 2095435 2358157 := bbase (se 3 (by rfl) ⟨442154, by rfl⟩ : syracuseStep 2358157 = 884309) (by norm_num)
theorem B3144209 : Blo 2095435 3144209 := bstep (se 2 (by rfl) ⟨1179078, by rfl⟩ : syracuseStep 3144209 = 2358157) B2358157
theorem B2096139 : Blo 2095435 2096139 := bstep (se 1 (by rfl) ⟨1572104, by rfl⟩ : syracuseStep 2096139 = 3144209) B3144209
theorem B7074485 : Blo 2095435 7074485 := bbase (se 5 (by rfl) ⟨331616, by rfl⟩ : syracuseStep 7074485 = 663233) (by norm_num)
theorem B4716323 : Blo 2095435 4716323 := bstep (se 1 (by rfl) ⟨3537242, by rfl⟩ : syracuseStep 4716323 = 7074485) B7074485
theorem B3144215 : Blo 2095435 3144215 := bstep (se 1 (by rfl) ⟨2358161, by rfl⟩ : syracuseStep 3144215 = 4716323) B4716323
theorem B2096143 : Blo 2095435 2096143 := bstep (se 1 (by rfl) ⟨1572107, by rfl⟩ : syracuseStep 2096143 = 3144215) B3144215
theorem B3144221 : Blo 2095435 3144221 := bbase (se 3 (by rfl) ⟨589541, by rfl⟩ : syracuseStep 3144221 = 1179083) (by norm_num)
theorem B2096147 : Blo 2095435 2096147 := bstep (se 1 (by rfl) ⟨1572110, by rfl⟩ : syracuseStep 2096147 = 3144221) B3144221
theorem B4716341 : Blo 2095435 4716341 := bbase (se 5 (by rfl) ⟨221078, by rfl⟩ : syracuseStep 4716341 = 442157) (by norm_num)
theorem B3144227 : Blo 2095435 3144227 := bstep (se 1 (by rfl) ⟨2358170, by rfl⟩ : syracuseStep 3144227 = 4716341) B4716341
theorem B2096151 : Blo 2095435 2096151 := bstep (se 1 (by rfl) ⟨1572113, by rfl⟩ : syracuseStep 2096151 = 3144227) B3144227
theorem B13430549 : Blo 2095435 13430549 := bbase (se 6 (by rfl) ⟨314778, by rfl⟩ : syracuseStep 13430549 = 629557) (by norm_num)
theorem B8953699 : Blo 2095435 8953699 := bstep (se 1 (by rfl) ⟨6715274, by rfl⟩ : syracuseStep 8953699 = 13430549) B13430549
theorem B11938265 : Blo 2095435 11938265 := bstep (se 2 (by rfl) ⟨4476849, by rfl⟩ : syracuseStep 11938265 = 8953699) B8953699
theorem B7958843 : Blo 2095435 7958843 := bstep (se 1 (by rfl) ⟨5969132, by rfl⟩ : syracuseStep 7958843 = 11938265) B11938265
theorem B5305895 : Blo 2095435 5305895 := bstep (se 1 (by rfl) ⟨3979421, by rfl⟩ : syracuseStep 5305895 = 7958843) B7958843
theorem B3537263 : Blo 2095435 3537263 := bstep (se 1 (by rfl) ⟨2652947, by rfl⟩ : syracuseStep 3537263 = 5305895) B5305895
theorem B2358175 : Blo 2095435 2358175 := bstep (se 1 (by rfl) ⟨1768631, by rfl⟩ : syracuseStep 2358175 = 3537263) B3537263
theorem B3144233 : Blo 2095435 3144233 := bstep (se 2 (by rfl) ⟨1179087, by rfl⟩ : syracuseStep 3144233 = 2358175) B2358175
theorem B2096155 : Blo 2095435 2096155 := bstep (se 1 (by rfl) ⟨1572116, by rfl⟩ : syracuseStep 2096155 = 3144233) B3144233
theorem B3777349 : Blo 2095435 3777349 := bbase (se 4 (by rfl) ⟨354126, by rfl⟩ : syracuseStep 3777349 = 708253) (by norm_num)
theorem B5036465 : Blo 2095435 5036465 := bstep (se 2 (by rfl) ⟨1888674, by rfl⟩ : syracuseStep 5036465 = 3777349) B3777349
theorem B13430573 : Blo 2095435 13430573 := bstep (se 3 (by rfl) ⟨2518232, by rfl⟩ : syracuseStep 13430573 = 5036465) B5036465
theorem B8953715 : Blo 2095435 8953715 := bstep (se 1 (by rfl) ⟨6715286, by rfl⟩ : syracuseStep 8953715 = 13430573) B13430573
theorem B5969143 : Blo 2095435 5969143 := bstep (se 1 (by rfl) ⟨4476857, by rfl⟩ : syracuseStep 5969143 = 8953715) B8953715
theorem B7958857 : Blo 2095435 7958857 := bstep (se 2 (by rfl) ⟨2984571, by rfl⟩ : syracuseStep 7958857 = 5969143) B5969143
theorem B10611809 : Blo 2095435 10611809 := bstep (se 2 (by rfl) ⟨3979428, by rfl⟩ : syracuseStep 10611809 = 7958857) B7958857
theorem B7074539 : Blo 2095435 7074539 := bstep (se 1 (by rfl) ⟨5305904, by rfl⟩ : syracuseStep 7074539 = 10611809) B10611809
theorem B4716359 : Blo 2095435 4716359 := bstep (se 1 (by rfl) ⟨3537269, by rfl⟩ : syracuseStep 4716359 = 7074539) B7074539
theorem B3144239 : Blo 2095435 3144239 := bstep (se 1 (by rfl) ⟨2358179, by rfl⟩ : syracuseStep 3144239 = 4716359) B4716359
theorem B2096159 : Blo 2095435 2096159 := bstep (se 1 (by rfl) ⟨1572119, by rfl⟩ : syracuseStep 2096159 = 3144239) B3144239
theorem B3144245 : Blo 2095435 3144245 := bbase (se 5 (by rfl) ⟨147386, by rfl⟩ : syracuseStep 3144245 = 294773) (by norm_num)
theorem B2096163 : Blo 2095435 2096163 := bstep (se 1 (by rfl) ⟨1572122, by rfl⟩ : syracuseStep 2096163 = 3144245) B3144245
theorem B5305925 : Blo 2095435 5305925 := bbase (se 4 (by rfl) ⟨497430, by rfl⟩ : syracuseStep 5305925 = 994861) (by norm_num)
theorem B3537283 : Blo 2095435 3537283 := bstep (se 1 (by rfl) ⟨2652962, by rfl⟩ : syracuseStep 3537283 = 5305925) B5305925
theorem B4716377 : Blo 2095435 4716377 := bstep (se 2 (by rfl) ⟨1768641, by rfl⟩ : syracuseStep 4716377 = 3537283) B3537283
theorem B3144251 : Blo 2095435 3144251 := bstep (se 1 (by rfl) ⟨2358188, by rfl⟩ : syracuseStep 3144251 = 4716377) B4716377
theorem B2096167 : Blo 2095435 2096167 := bstep (se 1 (by rfl) ⟨1572125, by rfl⟩ : syracuseStep 2096167 = 3144251) B3144251
theorem B2358193 : Blo 2095435 2358193 := bbase (se 2 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 2358193 = 1768645) (by norm_num)
theorem B3144257 : Blo 2095435 3144257 := bstep (se 2 (by rfl) ⟨1179096, by rfl⟩ : syracuseStep 3144257 = 2358193) B2358193
theorem B2096171 : Blo 2095435 2096171 := bstep (se 1 (by rfl) ⟨1572128, by rfl⟩ : syracuseStep 2096171 = 3144257) B3144257
theorem B5969189 : Blo 2095435 5969189 := bbase (se 4 (by rfl) ⟨559611, by rfl⟩ : syracuseStep 5969189 = 1119223) (by norm_num)
theorem B3979459 : Blo 2095435 3979459 := bstep (se 1 (by rfl) ⟨2984594, by rfl⟩ : syracuseStep 3979459 = 5969189) B5969189
theorem B5305945 : Blo 2095435 5305945 := bstep (se 2 (by rfl) ⟨1989729, by rfl⟩ : syracuseStep 5305945 = 3979459) B3979459
theorem B7074593 : Blo 2095435 7074593 := bstep (se 2 (by rfl) ⟨2652972, by rfl⟩ : syracuseStep 7074593 = 5305945) B5305945
theorem B4716395 : Blo 2095435 4716395 := bstep (se 1 (by rfl) ⟨3537296, by rfl⟩ : syracuseStep 4716395 = 7074593) B7074593
theorem B3144263 : Blo 2095435 3144263 := bstep (se 1 (by rfl) ⟨2358197, by rfl⟩ : syracuseStep 3144263 = 4716395) B4716395
theorem B2096175 : Blo 2095435 2096175 := bstep (se 1 (by rfl) ⟨1572131, by rfl⟩ : syracuseStep 2096175 = 3144263) B3144263
theorem B3144269 : Blo 2095435 3144269 := bbase (se 3 (by rfl) ⟨589550, by rfl⟩ : syracuseStep 3144269 = 1179101) (by norm_num)
theorem B2096179 : Blo 2095435 2096179 := bstep (se 1 (by rfl) ⟨1572134, by rfl⟩ : syracuseStep 2096179 = 3144269) B3144269
theorem B4716413 : Blo 2095435 4716413 := bbase (se 3 (by rfl) ⟨884327, by rfl⟩ : syracuseStep 4716413 = 1768655) (by norm_num)
theorem B3144275 : Blo 2095435 3144275 := bstep (se 1 (by rfl) ⟨2358206, by rfl⟩ : syracuseStep 3144275 = 4716413) B4716413
theorem B2096183 : Blo 2095435 2096183 := bstep (se 1 (by rfl) ⟨1572137, by rfl⟩ : syracuseStep 2096183 = 3144275) B3144275
theorem B3537317 : Blo 2095435 3537317 := bbase (se 4 (by rfl) ⟨331623, by rfl⟩ : syracuseStep 3537317 = 663247) (by norm_num)
theorem B2358211 : Blo 2095435 2358211 := bstep (se 1 (by rfl) ⟨1768658, by rfl⟩ : syracuseStep 2358211 = 3537317) B3537317
theorem B3144281 : Blo 2095435 3144281 := bstep (se 2 (by rfl) ⟨1179105, by rfl⟩ : syracuseStep 3144281 = 2358211) B2358211
theorem B2096187 : Blo 2095435 2096187 := bstep (se 1 (by rfl) ⟨1572140, by rfl⟩ : syracuseStep 2096187 = 3144281) B3144281
theorem B7570613 : Blo 2095435 7570613 := bbase (se 5 (by rfl) ⟨354872, by rfl⟩ : syracuseStep 7570613 = 709745) (by norm_num)
theorem B5047075 : Blo 2095435 5047075 := bstep (se 1 (by rfl) ⟨3785306, by rfl⟩ : syracuseStep 5047075 = 7570613) B7570613
theorem B26917733 : Blo 2095435 26917733 := bstep (se 4 (by rfl) ⟨2523537, by rfl⟩ : syracuseStep 26917733 = 5047075) B5047075
theorem B17945155 : Blo 2095435 17945155 := bstep (se 1 (by rfl) ⟨13458866, by rfl⟩ : syracuseStep 17945155 = 26917733) B26917733
theorem B23926873 : Blo 2095435 23926873 := bstep (se 2 (by rfl) ⟨8972577, by rfl⟩ : syracuseStep 23926873 = 17945155) B17945155
theorem B31902497 : Blo 2095435 31902497 := bstep (se 2 (by rfl) ⟨11963436, by rfl⟩ : syracuseStep 31902497 = 23926873) B23926873
theorem B21268331 : Blo 2095435 21268331 := bstep (se 1 (by rfl) ⟨15951248, by rfl⟩ : syracuseStep 21268331 = 31902497) B31902497
theorem B14178887 : Blo 2095435 14178887 := bstep (se 1 (by rfl) ⟨10634165, by rfl⟩ : syracuseStep 14178887 = 21268331) B21268331
theorem B9452591 : Blo 2095435 9452591 := bstep (se 1 (by rfl) ⟨7089443, by rfl⟩ : syracuseStep 9452591 = 14178887) B14178887
theorem B6301727 : Blo 2095435 6301727 := bstep (se 1 (by rfl) ⟨4726295, by rfl⟩ : syracuseStep 6301727 = 9452591) B9452591
theorem B4201151 : Blo 2095435 4201151 := bstep (se 1 (by rfl) ⟨3150863, by rfl⟩ : syracuseStep 4201151 = 6301727) B6301727
theorem B11203069 : Blo 2095435 11203069 := bstep (se 3 (by rfl) ⟨2100575, by rfl⟩ : syracuseStep 11203069 = 4201151) B4201151
theorem B14937425 : Blo 2095435 14937425 := bstep (se 2 (by rfl) ⟨5601534, by rfl⟩ : syracuseStep 14937425 = 11203069) B11203069
theorem B9958283 : Blo 2095435 9958283 := bstep (se 1 (by rfl) ⟨7468712, by rfl⟩ : syracuseStep 9958283 = 14937425) B14937425
theorem B6638855 : Blo 2095435 6638855 := bstep (se 1 (by rfl) ⟨4979141, by rfl⟩ : syracuseStep 6638855 = 9958283) B9958283
theorem B17703613 : Blo 2095435 17703613 := bstep (se 3 (by rfl) ⟨3319427, by rfl⟩ : syracuseStep 17703613 = 6638855) B6638855
theorem B94419269 : Blo 2095435 94419269 := bstep (se 4 (by rfl) ⟨8851806, by rfl⟩ : syracuseStep 94419269 = 17703613) B17703613
theorem B62946179 : Blo 2095435 62946179 := bstep (se 1 (by rfl) ⟨47209634, by rfl⟩ : syracuseStep 62946179 = 94419269) B94419269
theorem B41964119 : Blo 2095435 41964119 := bstep (se 1 (by rfl) ⟨31473089, by rfl⟩ : syracuseStep 41964119 = 62946179) B62946179
theorem B27976079 : Blo 2095435 27976079 := bstep (se 1 (by rfl) ⟨20982059, by rfl⟩ : syracuseStep 27976079 = 41964119) B41964119
theorem B18650719 : Blo 2095435 18650719 := bstep (se 1 (by rfl) ⟨13988039, by rfl⟩ : syracuseStep 18650719 = 27976079) B27976079
theorem B99470501 : Blo 2095435 99470501 := bstep (se 4 (by rfl) ⟨9325359, by rfl⟩ : syracuseStep 99470501 = 18650719) B18650719
theorem B66313667 : Blo 2095435 66313667 := bstep (se 1 (by rfl) ⟨49735250, by rfl⟩ : syracuseStep 66313667 = 99470501) B99470501
theorem B44209111 : Blo 2095435 44209111 := bstep (se 1 (by rfl) ⟨33156833, by rfl⟩ : syracuseStep 44209111 = 66313667) B66313667
theorem B58945481 : Blo 2095435 58945481 := bstep (se 2 (by rfl) ⟨22104555, by rfl⟩ : syracuseStep 58945481 = 44209111) B44209111
theorem B39296987 : Blo 2095435 39296987 := bstep (se 1 (by rfl) ⟨29472740, by rfl⟩ : syracuseStep 39296987 = 58945481) B58945481
theorem B26197991 : Blo 2095435 26197991 := bstep (se 1 (by rfl) ⟨19648493, by rfl⟩ : syracuseStep 26197991 = 39296987) B39296987
theorem B17465327 : Blo 2095435 17465327 := bstep (se 1 (by rfl) ⟨13098995, by rfl⟩ : syracuseStep 17465327 = 26197991) B26197991
theorem B11643551 : Blo 2095435 11643551 := bstep (se 1 (by rfl) ⟨8732663, by rfl⟩ : syracuseStep 11643551 = 17465327) B17465327
theorem B124197877 : Blo 2095435 124197877 := bstep (se 5 (by rfl) ⟨5821775, by rfl⟩ : syracuseStep 124197877 = 11643551) B11643551
theorem B165597169 : Blo 2095435 165597169 := bstep (se 2 (by rfl) ⟨62098938, by rfl⟩ : syracuseStep 165597169 = 124197877) B124197877
theorem B220796225 : Blo 2095435 220796225 := bstep (se 2 (by rfl) ⟨82798584, by rfl⟩ : syracuseStep 220796225 = 165597169) B165597169
theorem B147197483 : Blo 2095435 147197483 := bstep (se 1 (by rfl) ⟨110398112, by rfl⟩ : syracuseStep 147197483 = 220796225) B220796225
theorem B98131655 : Blo 2095435 98131655 := bstep (se 1 (by rfl) ⟨73598741, by rfl⟩ : syracuseStep 98131655 = 147197483) B147197483
theorem B65421103 : Blo 2095435 65421103 := bstep (se 1 (by rfl) ⟨49065827, by rfl⟩ : syracuseStep 65421103 = 98131655) B98131655
theorem B87228137 : Blo 2095435 87228137 := bstep (se 2 (by rfl) ⟨32710551, by rfl⟩ : syracuseStep 87228137 = 65421103) B65421103
theorem B58152091 : Blo 2095435 58152091 := bstep (se 1 (by rfl) ⟨43614068, by rfl⟩ : syracuseStep 58152091 = 87228137) B87228137
theorem B77536121 : Blo 2095435 77536121 := bstep (se 2 (by rfl) ⟨29076045, by rfl⟩ : syracuseStep 77536121 = 58152091) B58152091
theorem B206762989 : Blo 2095435 206762989 := bstep (se 3 (by rfl) ⟨38768060, by rfl⟩ : syracuseStep 206762989 = 77536121) B77536121
theorem B275683985 : Blo 2095435 275683985 := bstep (se 2 (by rfl) ⟨103381494, by rfl⟩ : syracuseStep 275683985 = 206762989) B206762989
theorem B183789323 : Blo 2095435 183789323 := bstep (se 1 (by rfl) ⟨137841992, by rfl⟩ : syracuseStep 183789323 = 275683985) B275683985
theorem B122526215 : Blo 2095435 122526215 := bstep (se 1 (by rfl) ⟨91894661, by rfl⟩ : syracuseStep 122526215 = 183789323) B183789323
theorem B81684143 : Blo 2095435 81684143 := bstep (se 1 (by rfl) ⟨61263107, by rfl⟩ : syracuseStep 81684143 = 122526215) B122526215
theorem B54456095 : Blo 2095435 54456095 := bstep (se 1 (by rfl) ⟨40842071, by rfl⟩ : syracuseStep 54456095 = 81684143) B81684143
theorem B145216253 : Blo 2095435 145216253 := bstep (se 3 (by rfl) ⟨27228047, by rfl⟩ : syracuseStep 145216253 = 54456095) B54456095
theorem B96810835 : Blo 2095435 96810835 := bstep (se 1 (by rfl) ⟨72608126, by rfl⟩ : syracuseStep 96810835 = 145216253) B145216253
theorem B129081113 : Blo 2095435 129081113 := bstep (se 2 (by rfl) ⟨48405417, by rfl⟩ : syracuseStep 129081113 = 96810835) B96810835
theorem B86054075 : Blo 2095435 86054075 := bstep (se 1 (by rfl) ⟨64540556, by rfl⟩ : syracuseStep 86054075 = 129081113) B129081113
theorem B57369383 : Blo 2095435 57369383 := bstep (se 1 (by rfl) ⟨43027037, by rfl⟩ : syracuseStep 57369383 = 86054075) B86054075
theorem B38246255 : Blo 2095435 38246255 := bstep (se 1 (by rfl) ⟨28684691, by rfl⟩ : syracuseStep 38246255 = 57369383) B57369383
theorem B25497503 : Blo 2095435 25497503 := bstep (se 1 (by rfl) ⟨19123127, by rfl⟩ : syracuseStep 25497503 = 38246255) B38246255
theorem B16998335 : Blo 2095435 16998335 := bstep (se 1 (by rfl) ⟨12748751, by rfl⟩ : syracuseStep 16998335 = 25497503) B25497503
theorem B11332223 : Blo 2095435 11332223 := bstep (se 1 (by rfl) ⟨8499167, by rfl⟩ : syracuseStep 11332223 = 16998335) B16998335
theorem B7554815 : Blo 2095435 7554815 := bstep (se 1 (by rfl) ⟨5666111, by rfl⟩ : syracuseStep 7554815 = 11332223) B11332223
theorem B5036543 : Blo 2095435 5036543 := bstep (se 1 (by rfl) ⟨3777407, by rfl⟩ : syracuseStep 5036543 = 7554815) B7554815
theorem B3357695 : Blo 2095435 3357695 := bstep (se 1 (by rfl) ⟨2518271, by rfl⟩ : syracuseStep 3357695 = 5036543) B5036543
theorem B2238463 : Blo 2095435 2238463 := bstep (se 1 (by rfl) ⟨1678847, by rfl⟩ : syracuseStep 2238463 = 3357695) B3357695
theorem B2984617 : Blo 2095435 2984617 := bstep (se 2 (by rfl) ⟨1119231, by rfl⟩ : syracuseStep 2984617 = 2238463) B2238463
theorem B15917957 : Blo 2095435 15917957 := bstep (se 4 (by rfl) ⟨1492308, by rfl⟩ : syracuseStep 15917957 = 2984617) B2984617
theorem B10611971 : Blo 2095435 10611971 := bstep (se 1 (by rfl) ⟨7958978, by rfl⟩ : syracuseStep 10611971 = 15917957) B15917957
theorem B7074647 : Blo 2095435 7074647 := bstep (se 1 (by rfl) ⟨5305985, by rfl⟩ : syracuseStep 7074647 = 10611971) B10611971
theorem B4716431 : Blo 2095435 4716431 := bstep (se 1 (by rfl) ⟨3537323, by rfl⟩ : syracuseStep 4716431 = 7074647) B7074647
theorem B3144287 : Blo 2095435 3144287 := bstep (se 1 (by rfl) ⟨2358215, by rfl⟩ : syracuseStep 3144287 = 4716431) B4716431
theorem B2096191 : Blo 2095435 2096191 := bstep (se 1 (by rfl) ⟨1572143, by rfl⟩ : syracuseStep 2096191 = 3144287) B3144287
theorem B3144293 : Blo 2095435 3144293 := bbase (se 4 (by rfl) ⟨294777, by rfl⟩ : syracuseStep 3144293 = 589555) (by norm_num)
theorem B2096195 : Blo 2095435 2096195 := bstep (se 1 (by rfl) ⟨1572146, by rfl⟩ : syracuseStep 2096195 = 3144293) B3144293
theorem B2984629 : Blo 2095435 2984629 := bbase (se 5 (by rfl) ⟨139904, by rfl⟩ : syracuseStep 2984629 = 279809) (by norm_num)
theorem B3979505 : Blo 2095435 3979505 := bstep (se 2 (by rfl) ⟨1492314, by rfl⟩ : syracuseStep 3979505 = 2984629) B2984629
theorem B2653003 : Blo 2095435 2653003 := bstep (se 1 (by rfl) ⟨1989752, by rfl⟩ : syracuseStep 2653003 = 3979505) B3979505
theorem B3537337 : Blo 2095435 3537337 := bstep (se 2 (by rfl) ⟨1326501, by rfl⟩ : syracuseStep 3537337 = 2653003) B2653003
theorem B4716449 : Blo 2095435 4716449 := bstep (se 2 (by rfl) ⟨1768668, by rfl⟩ : syracuseStep 4716449 = 3537337) B3537337
theorem B3144299 : Blo 2095435 3144299 := bstep (se 1 (by rfl) ⟨2358224, by rfl⟩ : syracuseStep 3144299 = 4716449) B4716449
theorem B2096199 : Blo 2095435 2096199 := bstep (se 1 (by rfl) ⟨1572149, by rfl⟩ : syracuseStep 2096199 = 3144299) B3144299
theorem B2358229 : Blo 2095435 2358229 := bbase (se 7 (by rfl) ⟨27635, by rfl⟩ : syracuseStep 2358229 = 55271) (by norm_num)
theorem B3144305 : Blo 2095435 3144305 := bstep (se 2 (by rfl) ⟨1179114, by rfl⟩ : syracuseStep 3144305 = 2358229) B2358229
theorem B2096203 : Blo 2095435 2096203 := bstep (se 1 (by rfl) ⟨1572152, by rfl⟩ : syracuseStep 2096203 = 3144305) B3144305
theorem B2653013 : Blo 2095435 2653013 := bbase (se 9 (by rfl) ⟨7772, by rfl⟩ : syracuseStep 2653013 = 15545) (by norm_num)
theorem B7074701 : Blo 2095435 7074701 := bstep (se 3 (by rfl) ⟨1326506, by rfl⟩ : syracuseStep 7074701 = 2653013) B2653013
theorem B4716467 : Blo 2095435 4716467 := bstep (se 1 (by rfl) ⟨3537350, by rfl⟩ : syracuseStep 4716467 = 7074701) B7074701
theorem B3144311 : Blo 2095435 3144311 := bstep (se 1 (by rfl) ⟨2358233, by rfl⟩ : syracuseStep 3144311 = 4716467) B4716467
theorem B2096207 : Blo 2095435 2096207 := bstep (se 1 (by rfl) ⟨1572155, by rfl⟩ : syracuseStep 2096207 = 3144311) B3144311
theorem B3144317 : Blo 2095435 3144317 := bbase (se 3 (by rfl) ⟨589559, by rfl⟩ : syracuseStep 3144317 = 1179119) (by norm_num)
theorem B2096211 : Blo 2095435 2096211 := bstep (se 1 (by rfl) ⟨1572158, by rfl⟩ : syracuseStep 2096211 = 3144317) B3144317
theorem B4716485 : Blo 2095435 4716485 := bbase (se 4 (by rfl) ⟨442170, by rfl⟩ : syracuseStep 4716485 = 884341) (by norm_num)
theorem B3144323 : Blo 2095435 3144323 := bstep (se 1 (by rfl) ⟨2358242, by rfl⟩ : syracuseStep 3144323 = 4716485) B4716485
theorem B2096215 : Blo 2095435 2096215 := bstep (se 1 (by rfl) ⟨1572161, by rfl⟩ : syracuseStep 2096215 = 3144323) B3144323
theorem B8953973 : Blo 2095435 8953973 := bbase (se 5 (by rfl) ⟨419717, by rfl⟩ : syracuseStep 8953973 = 839435) (by norm_num)
theorem B5969315 : Blo 2095435 5969315 := bstep (se 1 (by rfl) ⟨4476986, by rfl⟩ : syracuseStep 5969315 = 8953973) B8953973
theorem B3979543 : Blo 2095435 3979543 := bstep (se 1 (by rfl) ⟨2984657, by rfl⟩ : syracuseStep 3979543 = 5969315) B5969315
theorem B5306057 : Blo 2095435 5306057 := bstep (se 2 (by rfl) ⟨1989771, by rfl⟩ : syracuseStep 5306057 = 3979543) B3979543
theorem B3537371 : Blo 2095435 3537371 := bstep (se 1 (by rfl) ⟨2653028, by rfl⟩ : syracuseStep 3537371 = 5306057) B5306057
theorem B2358247 : Blo 2095435 2358247 := bstep (se 1 (by rfl) ⟨1768685, by rfl⟩ : syracuseStep 2358247 = 3537371) B3537371
theorem B3144329 : Blo 2095435 3144329 := bstep (se 2 (by rfl) ⟨1179123, by rfl⟩ : syracuseStep 3144329 = 2358247) B2358247
theorem B2096219 : Blo 2095435 2096219 := bstep (se 1 (by rfl) ⟨1572164, by rfl⟩ : syracuseStep 2096219 = 3144329) B3144329
theorem B10612133 : Blo 2095435 10612133 := bbase (se 4 (by rfl) ⟨994887, by rfl⟩ : syracuseStep 10612133 = 1989775) (by norm_num)
theorem B7074755 : Blo 2095435 7074755 := bstep (se 1 (by rfl) ⟨5306066, by rfl⟩ : syracuseStep 7074755 = 10612133) B10612133
theorem B4716503 : Blo 2095435 4716503 := bstep (se 1 (by rfl) ⟨3537377, by rfl⟩ : syracuseStep 4716503 = 7074755) B7074755
theorem B3144335 : Blo 2095435 3144335 := bstep (se 1 (by rfl) ⟨2358251, by rfl⟩ : syracuseStep 3144335 = 4716503) B4716503
theorem B2096223 : Blo 2095435 2096223 := bstep (se 1 (by rfl) ⟨1572167, by rfl⟩ : syracuseStep 2096223 = 3144335) B3144335
theorem B3144341 : Blo 2095435 3144341 := bbase (se 6 (by rfl) ⟨73695, by rfl⟩ : syracuseStep 3144341 = 147391) (by norm_num)
theorem B2096227 : Blo 2095435 2096227 := bstep (se 1 (by rfl) ⟨1572170, by rfl⟩ : syracuseStep 2096227 = 3144341) B3144341
theorem B290437973 : Blo 2095435 290437973 := bbase (se 9 (by rfl) ⟨850892, by rfl⟩ : syracuseStep 290437973 = 1701785) (by norm_num)
theorem B193625315 : Blo 2095435 193625315 := bstep (se 1 (by rfl) ⟨145218986, by rfl⟩ : syracuseStep 193625315 = 290437973) B290437973
theorem B129083543 : Blo 2095435 129083543 := bstep (se 1 (by rfl) ⟨96812657, by rfl⟩ : syracuseStep 129083543 = 193625315) B193625315
theorem B86055695 : Blo 2095435 86055695 := bstep (se 1 (by rfl) ⟨64541771, by rfl⟩ : syracuseStep 86055695 = 129083543) B129083543
theorem B57370463 : Blo 2095435 57370463 := bstep (se 1 (by rfl) ⟨43027847, by rfl⟩ : syracuseStep 57370463 = 86055695) B86055695
theorem B38246975 : Blo 2095435 38246975 := bstep (se 1 (by rfl) ⟨28685231, by rfl⟩ : syracuseStep 38246975 = 57370463) B57370463
theorem B25497983 : Blo 2095435 25497983 := bstep (se 1 (by rfl) ⟨19123487, by rfl⟩ : syracuseStep 25497983 = 38246975) B38246975
theorem B16998655 : Blo 2095435 16998655 := bstep (se 1 (by rfl) ⟨12748991, by rfl⟩ : syracuseStep 16998655 = 25497983) B25497983
theorem B22664873 : Blo 2095435 22664873 := bstep (se 2 (by rfl) ⟨8499327, by rfl⟩ : syracuseStep 22664873 = 16998655) B16998655
theorem B15109915 : Blo 2095435 15109915 := bstep (se 1 (by rfl) ⟨11332436, by rfl⟩ : syracuseStep 15109915 = 22664873) B22664873
theorem B20146553 : Blo 2095435 20146553 := bstep (se 2 (by rfl) ⟨7554957, by rfl⟩ : syracuseStep 20146553 = 15109915) B15109915
theorem B13431035 : Blo 2095435 13431035 := bstep (se 1 (by rfl) ⟨10073276, by rfl⟩ : syracuseStep 13431035 = 20146553) B20146553
theorem B8954023 : Blo 2095435 8954023 := bstep (se 1 (by rfl) ⟨6715517, by rfl⟩ : syracuseStep 8954023 = 13431035) B13431035
theorem B11938697 : Blo 2095435 11938697 := bstep (se 2 (by rfl) ⟨4477011, by rfl⟩ : syracuseStep 11938697 = 8954023) B8954023
theorem B7959131 : Blo 2095435 7959131 := bstep (se 1 (by rfl) ⟨5969348, by rfl⟩ : syracuseStep 7959131 = 11938697) B11938697
theorem B5306087 : Blo 2095435 5306087 := bstep (se 1 (by rfl) ⟨3979565, by rfl⟩ : syracuseStep 5306087 = 7959131) B7959131
theorem B3537391 : Blo 2095435 3537391 := bstep (se 1 (by rfl) ⟨2653043, by rfl⟩ : syracuseStep 3537391 = 5306087) B5306087
theorem B4716521 : Blo 2095435 4716521 := bstep (se 2 (by rfl) ⟨1768695, by rfl⟩ : syracuseStep 4716521 = 3537391) B3537391
theorem B3144347 : Blo 2095435 3144347 := bstep (se 1 (by rfl) ⟨2358260, by rfl⟩ : syracuseStep 3144347 = 4716521) B4716521
theorem B2096231 : Blo 2095435 2096231 := bstep (se 1 (by rfl) ⟨1572173, by rfl⟩ : syracuseStep 2096231 = 3144347) B3144347
theorem B2358265 : Blo 2095435 2358265 := bbase (se 2 (by rfl) ⟨884349, by rfl⟩ : syracuseStep 2358265 = 1768699) (by norm_num)
theorem B3144353 : Blo 2095435 3144353 := bstep (se 2 (by rfl) ⟨1179132, by rfl⟩ : syracuseStep 3144353 = 2358265) B2358265
theorem B2096235 : Blo 2095435 2096235 := bstep (se 1 (by rfl) ⟨1572176, by rfl⟩ : syracuseStep 2096235 = 3144353) B3144353
theorem B15109973 : Blo 2095435 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B10073315 : Blo 2095435 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B6715543 : Blo 2095435 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B8954057 : Blo 2095435 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B5969371 : Blo 2095435 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B7959161 : Blo 2095435 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B5306107 : Blo 2095435 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B7074809 : Blo 2095435 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B4716539 : Blo 2095435 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B3144359 : Blo 2095435 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B2096239 : Blo 2095435 2096239 := bstep (se 1 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 2096239 = 3144359) B3144359
theorem B3144365 : Blo 2095435 3144365 := bbase (se 3 (by rfl) ⟨589568, by rfl⟩ : syracuseStep 3144365 = 1179137) (by norm_num)
theorem B2096243 : Blo 2095435 2096243 := bstep (se 1 (by rfl) ⟨1572182, by rfl⟩ : syracuseStep 2096243 = 3144365) B3144365
theorem B4716557 : Blo 2095435 4716557 := bbase (se 3 (by rfl) ⟨884354, by rfl⟩ : syracuseStep 4716557 = 1768709) (by norm_num)
theorem B3144371 : Blo 2095435 3144371 := bstep (se 1 (by rfl) ⟨2358278, by rfl⟩ : syracuseStep 3144371 = 4716557) B4716557
theorem B2096247 : Blo 2095435 2096247 := bstep (se 1 (by rfl) ⟨1572185, by rfl⟩ : syracuseStep 2096247 = 3144371) B3144371
theorem B2653069 : Blo 2095435 2653069 := bbase (se 3 (by rfl) ⟨497450, by rfl⟩ : syracuseStep 2653069 = 994901) (by norm_num)
theorem B3537425 : Blo 2095435 3537425 := bstep (se 2 (by rfl) ⟨1326534, by rfl⟩ : syracuseStep 3537425 = 2653069) B2653069
theorem B2358283 : Blo 2095435 2358283 := bstep (se 1 (by rfl) ⟨1768712, by rfl⟩ : syracuseStep 2358283 = 3537425) B3537425
theorem B3144377 : Blo 2095435 3144377 := bstep (se 2 (by rfl) ⟨1179141, by rfl⟩ : syracuseStep 3144377 = 2358283) B2358283
theorem B2096251 : Blo 2095435 2096251 := bstep (se 1 (by rfl) ⟨1572188, by rfl⟩ : syracuseStep 2096251 = 3144377) B3144377
theorem B11332565 : Blo 2095435 11332565 := bbase (se 7 (by rfl) ⟨132803, by rfl⟩ : syracuseStep 11332565 = 265607) (by norm_num)
theorem B7555043 : Blo 2095435 7555043 := bstep (se 1 (by rfl) ⟨5666282, by rfl⟩ : syracuseStep 7555043 = 11332565) B11332565
theorem B20146781 : Blo 2095435 20146781 := bstep (se 3 (by rfl) ⟨3777521, by rfl⟩ : syracuseStep 20146781 = 7555043) B7555043
theorem B13431187 : Blo 2095435 13431187 := bstep (se 1 (by rfl) ⟨10073390, by rfl⟩ : syracuseStep 13431187 = 20146781) B20146781
theorem B17908249 : Blo 2095435 17908249 := bstep (se 2 (by rfl) ⟨6715593, by rfl⟩ : syracuseStep 17908249 = 13431187) B13431187
theorem B23877665 : Blo 2095435 23877665 := bstep (se 2 (by rfl) ⟨8954124, by rfl⟩ : syracuseStep 23877665 = 17908249) B17908249
theorem B15918443 : Blo 2095435 15918443 := bstep (se 1 (by rfl) ⟨11938832, by rfl⟩ : syracuseStep 15918443 = 23877665) B23877665
theorem B10612295 : Blo 2095435 10612295 := bstep (se 1 (by rfl) ⟨7959221, by rfl⟩ : syracuseStep 10612295 = 15918443) B15918443
theorem B7074863 : Blo 2095435 7074863 := bstep (se 1 (by rfl) ⟨5306147, by rfl⟩ : syracuseStep 7074863 = 10612295) B10612295
theorem B4716575 : Blo 2095435 4716575 := bstep (se 1 (by rfl) ⟨3537431, by rfl⟩ : syracuseStep 4716575 = 7074863) B7074863
theorem B3144383 : Blo 2095435 3144383 := bstep (se 1 (by rfl) ⟨2358287, by rfl⟩ : syracuseStep 3144383 = 4716575) B4716575
theorem B2096255 : Blo 2095435 2096255 := bstep (se 1 (by rfl) ⟨1572191, by rfl⟩ : syracuseStep 2096255 = 3144383) B3144383
theorem B3144389 : Blo 2095435 3144389 := bbase (se 4 (by rfl) ⟨294786, by rfl⟩ : syracuseStep 3144389 = 589573) (by norm_num)
theorem B2096259 : Blo 2095435 2096259 := bstep (se 1 (by rfl) ⟨1572194, by rfl⟩ : syracuseStep 2096259 = 3144389) B3144389
theorem B3537445 : Blo 2095435 3537445 := bbase (se 4 (by rfl) ⟨331635, by rfl⟩ : syracuseStep 3537445 = 663271) (by norm_num)
theorem B4716593 : Blo 2095435 4716593 := bstep (se 2 (by rfl) ⟨1768722, by rfl⟩ : syracuseStep 4716593 = 3537445) B3537445
theorem B3144395 : Blo 2095435 3144395 := bstep (se 1 (by rfl) ⟨2358296, by rfl⟩ : syracuseStep 3144395 = 4716593) B4716593
theorem B2096263 : Blo 2095435 2096263 := bstep (se 1 (by rfl) ⟨1572197, by rfl⟩ : syracuseStep 2096263 = 3144395) B3144395
theorem B2358301 : Blo 2095435 2358301 := bbase (se 3 (by rfl) ⟨442181, by rfl⟩ : syracuseStep 2358301 = 884363) (by norm_num)
theorem B3144401 : Blo 2095435 3144401 := bstep (se 2 (by rfl) ⟨1179150, by rfl⟩ : syracuseStep 3144401 = 2358301) B2358301
theorem B2096267 : Blo 2095435 2096267 := bstep (se 1 (by rfl) ⟨1572200, by rfl⟩ : syracuseStep 2096267 = 3144401) B3144401
theorem B7074917 : Blo 2095435 7074917 := bbase (se 4 (by rfl) ⟨663273, by rfl⟩ : syracuseStep 7074917 = 1326547) (by norm_num)
theorem B4716611 : Blo 2095435 4716611 := bstep (se 1 (by rfl) ⟨3537458, by rfl⟩ : syracuseStep 4716611 = 7074917) B7074917
theorem B3144407 : Blo 2095435 3144407 := bstep (se 1 (by rfl) ⟨2358305, by rfl⟩ : syracuseStep 3144407 = 4716611) B4716611
theorem B2096271 : Blo 2095435 2096271 := bstep (se 1 (by rfl) ⟨1572203, by rfl⟩ : syracuseStep 2096271 = 3144407) B3144407
theorem B3144413 : Blo 2095435 3144413 := bbase (se 3 (by rfl) ⟨589577, by rfl⟩ : syracuseStep 3144413 = 1179155) (by norm_num)
theorem B2096275 : Blo 2095435 2096275 := bstep (se 1 (by rfl) ⟨1572206, by rfl⟩ : syracuseStep 2096275 = 3144413) B3144413
theorem B4716629 : Blo 2095435 4716629 := bbase (se 8 (by rfl) ⟨27636, by rfl⟩ : syracuseStep 4716629 = 55273) (by norm_num)
theorem B3144419 : Blo 2095435 3144419 := bstep (se 1 (by rfl) ⟨2358314, by rfl⟩ : syracuseStep 3144419 = 4716629) B4716629
theorem B2096279 : Blo 2095435 2096279 := bstep (se 1 (by rfl) ⟨1572209, by rfl⟩ : syracuseStep 2096279 = 3144419) B3144419
theorem B6715685 : Blo 2095435 6715685 := bbase (se 4 (by rfl) ⟨629595, by rfl⟩ : syracuseStep 6715685 = 1259191) (by norm_num)
theorem B4477123 : Blo 2095435 4477123 := bstep (se 1 (by rfl) ⟨3357842, by rfl⟩ : syracuseStep 4477123 = 6715685) B6715685
theorem B5969497 : Blo 2095435 5969497 := bstep (se 2 (by rfl) ⟨2238561, by rfl⟩ : syracuseStep 5969497 = 4477123) B4477123
theorem B7959329 : Blo 2095435 7959329 := bstep (se 2 (by rfl) ⟨2984748, by rfl⟩ : syracuseStep 7959329 = 5969497) B5969497
theorem B5306219 : Blo 2095435 5306219 := bstep (se 1 (by rfl) ⟨3979664, by rfl⟩ : syracuseStep 5306219 = 7959329) B7959329
theorem B3537479 : Blo 2095435 3537479 := bstep (se 1 (by rfl) ⟨2653109, by rfl⟩ : syracuseStep 3537479 = 5306219) B5306219
theorem B2358319 : Blo 2095435 2358319 := bstep (se 1 (by rfl) ⟨1768739, by rfl⟩ : syracuseStep 2358319 = 3537479) B3537479
theorem B3144425 : Blo 2095435 3144425 := bstep (se 2 (by rfl) ⟨1179159, by rfl⟩ : syracuseStep 3144425 = 2358319) B2358319
theorem B2096283 : Blo 2095435 2096283 := bstep (se 1 (by rfl) ⟨1572212, by rfl⟩ : syracuseStep 2096283 = 3144425) B3144425
theorem B3187333 : Blo 2095435 3187333 := bbase (se 4 (by rfl) ⟨298812, by rfl⟩ : syracuseStep 3187333 = 597625) (by norm_num)
theorem B4249777 : Blo 2095435 4249777 := bstep (se 2 (by rfl) ⟨1593666, by rfl⟩ : syracuseStep 4249777 = 3187333) B3187333
theorem B5666369 : Blo 2095435 5666369 := bstep (se 2 (by rfl) ⟨2124888, by rfl⟩ : syracuseStep 5666369 = 4249777) B4249777
theorem B15110317 : Blo 2095435 15110317 := bstep (se 3 (by rfl) ⟨2833184, by rfl⟩ : syracuseStep 15110317 = 5666369) B5666369
theorem B20147089 : Blo 2095435 20147089 := bstep (se 2 (by rfl) ⟨7555158, by rfl⟩ : syracuseStep 20147089 = 15110317) B15110317
theorem B26862785 : Blo 2095435 26862785 := bstep (se 2 (by rfl) ⟨10073544, by rfl⟩ : syracuseStep 26862785 = 20147089) B20147089
theorem B17908523 : Blo 2095435 17908523 := bstep (se 1 (by rfl) ⟨13431392, by rfl⟩ : syracuseStep 17908523 = 26862785) B26862785
theorem B11939015 : Blo 2095435 11939015 := bstep (se 1 (by rfl) ⟨8954261, by rfl⟩ : syracuseStep 11939015 = 17908523) B17908523
theorem B7959343 : Blo 2095435 7959343 := bstep (se 1 (by rfl) ⟨5969507, by rfl⟩ : syracuseStep 7959343 = 11939015) B11939015
theorem B10612457 : Blo 2095435 10612457 := bstep (se 2 (by rfl) ⟨3979671, by rfl⟩ : syracuseStep 10612457 = 7959343) B7959343
theorem B7074971 : Blo 2095435 7074971 := bstep (se 1 (by rfl) ⟨5306228, by rfl⟩ : syracuseStep 7074971 = 10612457) B10612457
theorem B4716647 : Blo 2095435 4716647 := bstep (se 1 (by rfl) ⟨3537485, by rfl⟩ : syracuseStep 4716647 = 7074971) B7074971
theorem B3144431 : Blo 2095435 3144431 := bstep (se 1 (by rfl) ⟨2358323, by rfl⟩ : syracuseStep 3144431 = 4716647) B4716647
theorem B2096287 : Blo 2095435 2096287 := bstep (se 1 (by rfl) ⟨1572215, by rfl⟩ : syracuseStep 2096287 = 3144431) B3144431
theorem B3144437 : Blo 2095435 3144437 := bbase (se 5 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 3144437 = 294791) (by norm_num)
theorem B2096291 : Blo 2095435 2096291 := bstep (se 1 (by rfl) ⟨1572218, by rfl⟩ : syracuseStep 2096291 = 3144437) B3144437
theorem B7555189 : Blo 2095435 7555189 := bbase (se 5 (by rfl) ⟨354149, by rfl⟩ : syracuseStep 7555189 = 708299) (by norm_num)
theorem B10073585 : Blo 2095435 10073585 := bstep (se 2 (by rfl) ⟨3777594, by rfl⟩ : syracuseStep 10073585 = 7555189) B7555189
theorem B6715723 : Blo 2095435 6715723 := bstep (se 1 (by rfl) ⟨5036792, by rfl⟩ : syracuseStep 6715723 = 10073585) B10073585
theorem B8954297 : Blo 2095435 8954297 := bstep (se 2 (by rfl) ⟨3357861, by rfl⟩ : syracuseStep 8954297 = 6715723) B6715723
theorem B5969531 : Blo 2095435 5969531 := bstep (se 1 (by rfl) ⟨4477148, by rfl⟩ : syracuseStep 5969531 = 8954297) B8954297
theorem B3979687 : Blo 2095435 3979687 := bstep (se 1 (by rfl) ⟨2984765, by rfl⟩ : syracuseStep 3979687 = 5969531) B5969531
theorem B5306249 : Blo 2095435 5306249 := bstep (se 2 (by rfl) ⟨1989843, by rfl⟩ : syracuseStep 5306249 = 3979687) B3979687
theorem B3537499 : Blo 2095435 3537499 := bstep (se 1 (by rfl) ⟨2653124, by rfl⟩ : syracuseStep 3537499 = 5306249) B5306249
theorem B4716665 : Blo 2095435 4716665 := bstep (se 2 (by rfl) ⟨1768749, by rfl⟩ : syracuseStep 4716665 = 3537499) B3537499
theorem B3144443 : Blo 2095435 3144443 := bstep (se 1 (by rfl) ⟨2358332, by rfl⟩ : syracuseStep 3144443 = 4716665) B4716665
theorem B2096295 : Blo 2095435 2096295 := bstep (se 1 (by rfl) ⟨1572221, by rfl⟩ : syracuseStep 2096295 = 3144443) B3144443
theorem B2358337 : Blo 2095435 2358337 := bbase (se 2 (by rfl) ⟨884376, by rfl⟩ : syracuseStep 2358337 = 1768753) (by norm_num)
theorem B3144449 : Blo 2095435 3144449 := bstep (se 2 (by rfl) ⟨1179168, by rfl⟩ : syracuseStep 3144449 = 2358337) B2358337
theorem B2096299 : Blo 2095435 2096299 := bstep (se 1 (by rfl) ⟨1572224, by rfl⟩ : syracuseStep 2096299 = 3144449) B3144449
theorem B5306269 : Blo 2095435 5306269 := bbase (se 3 (by rfl) ⟨994925, by rfl⟩ : syracuseStep 5306269 = 1989851) (by norm_num)
theorem B7075025 : Blo 2095435 7075025 := bstep (se 2 (by rfl) ⟨2653134, by rfl⟩ : syracuseStep 7075025 = 5306269) B5306269
theorem B4716683 : Blo 2095435 4716683 := bstep (se 1 (by rfl) ⟨3537512, by rfl⟩ : syracuseStep 4716683 = 7075025) B7075025
theorem B3144455 : Blo 2095435 3144455 := bstep (se 1 (by rfl) ⟨2358341, by rfl⟩ : syracuseStep 3144455 = 4716683) B4716683
theorem B2096303 : Blo 2095435 2096303 := bstep (se 1 (by rfl) ⟨1572227, by rfl⟩ : syracuseStep 2096303 = 3144455) B3144455
theorem B3144461 : Blo 2095435 3144461 := bbase (se 3 (by rfl) ⟨589586, by rfl⟩ : syracuseStep 3144461 = 1179173) (by norm_num)
theorem B2096307 : Blo 2095435 2096307 := bstep (se 1 (by rfl) ⟨1572230, by rfl⟩ : syracuseStep 2096307 = 3144461) B3144461
theorem B4716701 : Blo 2095435 4716701 := bbase (se 3 (by rfl) ⟨884381, by rfl⟩ : syracuseStep 4716701 = 1768763) (by norm_num)
theorem B3144467 : Blo 2095435 3144467 := bstep (se 1 (by rfl) ⟨2358350, by rfl⟩ : syracuseStep 3144467 = 4716701) B4716701
theorem B2096311 : Blo 2095435 2096311 := bstep (se 1 (by rfl) ⟨1572233, by rfl⟩ : syracuseStep 2096311 = 3144467) B3144467
theorem B3537533 : Blo 2095435 3537533 := bbase (se 3 (by rfl) ⟨663287, by rfl⟩ : syracuseStep 3537533 = 1326575) (by norm_num)
theorem B2358355 : Blo 2095435 2358355 := bstep (se 1 (by rfl) ⟨1768766, by rfl⟩ : syracuseStep 2358355 = 3537533) B3537533
theorem B3144473 : Blo 2095435 3144473 := bstep (se 2 (by rfl) ⟨1179177, by rfl⟩ : syracuseStep 3144473 = 2358355) B2358355
theorem B2096315 : Blo 2095435 2096315 := bstep (se 1 (by rfl) ⟨1572236, by rfl⟩ : syracuseStep 2096315 = 3144473) B3144473
theorem B15110549 : Blo 2095435 15110549 := bbase (se 6 (by rfl) ⟨354153, by rfl⟩ : syracuseStep 15110549 = 708307) (by norm_num)
theorem B10073699 : Blo 2095435 10073699 := bstep (se 1 (by rfl) ⟨7555274, by rfl⟩ : syracuseStep 10073699 = 15110549) B15110549
theorem B6715799 : Blo 2095435 6715799 := bstep (se 1 (by rfl) ⟨5036849, by rfl⟩ : syracuseStep 6715799 = 10073699) B10073699
theorem B4477199 : Blo 2095435 4477199 := bstep (se 1 (by rfl) ⟨3357899, by rfl⟩ : syracuseStep 4477199 = 6715799) B6715799
theorem B11939197 : Blo 2095435 11939197 := bstep (se 3 (by rfl) ⟨2238599, by rfl⟩ : syracuseStep 11939197 = 4477199) B4477199
theorem B15918929 : Blo 2095435 15918929 := bstep (se 2 (by rfl) ⟨5969598, by rfl⟩ : syracuseStep 15918929 = 11939197) B11939197
theorem B10612619 : Blo 2095435 10612619 := bstep (se 1 (by rfl) ⟨7959464, by rfl⟩ : syracuseStep 10612619 = 15918929) B15918929
theorem B7075079 : Blo 2095435 7075079 := bstep (se 1 (by rfl) ⟨5306309, by rfl⟩ : syracuseStep 7075079 = 10612619) B10612619
theorem B4716719 : Blo 2095435 4716719 := bstep (se 1 (by rfl) ⟨3537539, by rfl⟩ : syracuseStep 4716719 = 7075079) B7075079
theorem B3144479 : Blo 2095435 3144479 := bstep (se 1 (by rfl) ⟨2358359, by rfl⟩ : syracuseStep 3144479 = 4716719) B4716719
theorem B2096319 : Blo 2095435 2096319 := bstep (se 1 (by rfl) ⟨1572239, by rfl⟩ : syracuseStep 2096319 = 3144479) B3144479
theorem B3144485 : Blo 2095435 3144485 := bbase (se 4 (by rfl) ⟨294795, by rfl⟩ : syracuseStep 3144485 = 589591) (by norm_num)
theorem B2096323 : Blo 2095435 2096323 := bstep (se 1 (by rfl) ⟨1572242, by rfl⟩ : syracuseStep 2096323 = 3144485) B3144485
theorem B2653165 : Blo 2095435 2653165 := bbase (se 3 (by rfl) ⟨497468, by rfl⟩ : syracuseStep 2653165 = 994937) (by norm_num)
theorem B3537553 : Blo 2095435 3537553 := bstep (se 2 (by rfl) ⟨1326582, by rfl⟩ : syracuseStep 3537553 = 2653165) B2653165
theorem B4716737 : Blo 2095435 4716737 := bstep (se 2 (by rfl) ⟨1768776, by rfl⟩ : syracuseStep 4716737 = 3537553) B3537553
theorem B3144491 : Blo 2095435 3144491 := bstep (se 1 (by rfl) ⟨2358368, by rfl⟩ : syracuseStep 3144491 = 4716737) B4716737
theorem B2096327 : Blo 2095435 2096327 := bstep (se 1 (by rfl) ⟨1572245, by rfl⟩ : syracuseStep 2096327 = 3144491) B3144491
theorem B2358373 : Blo 2095435 2358373 := bbase (se 4 (by rfl) ⟨221097, by rfl⟩ : syracuseStep 2358373 = 442195) (by norm_num)
theorem B3144497 : Blo 2095435 3144497 := bstep (se 2 (by rfl) ⟨1179186, by rfl⟩ : syracuseStep 3144497 = 2358373) B2358373
theorem B2096331 : Blo 2095435 2096331 := bstep (se 1 (by rfl) ⟨1572248, by rfl⟩ : syracuseStep 2096331 = 3144497) B3144497
theorem B2238617 : Blo 2095435 2238617 := bbase (se 2 (by rfl) ⟨839481, by rfl⟩ : syracuseStep 2238617 = 1678963) (by norm_num)
theorem B5969645 : Blo 2095435 5969645 := bstep (se 3 (by rfl) ⟨1119308, by rfl⟩ : syracuseStep 5969645 = 2238617) B2238617
theorem B3979763 : Blo 2095435 3979763 := bstep (se 1 (by rfl) ⟨2984822, by rfl⟩ : syracuseStep 3979763 = 5969645) B5969645
theorem B2653175 : Blo 2095435 2653175 := bstep (se 1 (by rfl) ⟨1989881, by rfl⟩ : syracuseStep 2653175 = 3979763) B3979763
theorem B7075133 : Blo 2095435 7075133 := bstep (se 3 (by rfl) ⟨1326587, by rfl⟩ : syracuseStep 7075133 = 2653175) B2653175
theorem B4716755 : Blo 2095435 4716755 := bstep (se 1 (by rfl) ⟨3537566, by rfl⟩ : syracuseStep 4716755 = 7075133) B7075133
theorem B3144503 : Blo 2095435 3144503 := bstep (se 1 (by rfl) ⟨2358377, by rfl⟩ : syracuseStep 3144503 = 4716755) B4716755
theorem B2096335 : Blo 2095435 2096335 := bstep (se 1 (by rfl) ⟨1572251, by rfl⟩ : syracuseStep 2096335 = 3144503) B3144503
theorem B3144509 : Blo 2095435 3144509 := bbase (se 3 (by rfl) ⟨589595, by rfl⟩ : syracuseStep 3144509 = 1179191) (by norm_num)
theorem B2096339 : Blo 2095435 2096339 := bstep (se 1 (by rfl) ⟨1572254, by rfl⟩ : syracuseStep 2096339 = 3144509) B3144509
theorem B4716773 : Blo 2095435 4716773 := bbase (se 4 (by rfl) ⟨442197, by rfl⟩ : syracuseStep 4716773 = 884395) (by norm_num)
theorem B3144515 : Blo 2095435 3144515 := bstep (se 1 (by rfl) ⟨2358386, by rfl⟩ : syracuseStep 3144515 = 4716773) B4716773
theorem B2096343 : Blo 2095435 2096343 := bstep (se 1 (by rfl) ⟨1572257, by rfl⟩ : syracuseStep 2096343 = 3144515) B3144515
theorem B5306381 : Blo 2095435 5306381 := bbase (se 3 (by rfl) ⟨994946, by rfl⟩ : syracuseStep 5306381 = 1989893) (by norm_num)
theorem B3537587 : Blo 2095435 3537587 := bstep (se 1 (by rfl) ⟨2653190, by rfl⟩ : syracuseStep 3537587 = 5306381) B5306381
theorem B2358391 : Blo 2095435 2358391 := bstep (se 1 (by rfl) ⟨1768793, by rfl⟩ : syracuseStep 2358391 = 3537587) B3537587
theorem B3144521 : Blo 2095435 3144521 := bstep (se 2 (by rfl) ⟨1179195, by rfl⟩ : syracuseStep 3144521 = 2358391) B2358391
theorem B2096347 : Blo 2095435 2096347 := bstep (se 1 (by rfl) ⟨1572260, by rfl⟩ : syracuseStep 2096347 = 3144521) B3144521
theorem B2984845 : Blo 2095435 2984845 := bbase (se 3 (by rfl) ⟨559658, by rfl⟩ : syracuseStep 2984845 = 1119317) (by norm_num)
theorem B3979793 : Blo 2095435 3979793 := bstep (se 2 (by rfl) ⟨1492422, by rfl⟩ : syracuseStep 3979793 = 2984845) B2984845
theorem B10612781 : Blo 2095435 10612781 := bstep (se 3 (by rfl) ⟨1989896, by rfl⟩ : syracuseStep 10612781 = 3979793) B3979793
theorem B7075187 : Blo 2095435 7075187 := bstep (se 1 (by rfl) ⟨5306390, by rfl⟩ : syracuseStep 7075187 = 10612781) B10612781
theorem B4716791 : Blo 2095435 4716791 := bstep (se 1 (by rfl) ⟨3537593, by rfl⟩ : syracuseStep 4716791 = 7075187) B7075187
theorem B3144527 : Blo 2095435 3144527 := bstep (se 1 (by rfl) ⟨2358395, by rfl⟩ : syracuseStep 3144527 = 4716791) B4716791
theorem B2096351 : Blo 2095435 2096351 := bstep (se 1 (by rfl) ⟨1572263, by rfl⟩ : syracuseStep 2096351 = 3144527) B3144527
theorem B3144533 : Blo 2095435 3144533 := bbase (se 9 (by rfl) ⟨9212, by rfl⟩ : syracuseStep 3144533 = 18425) (by norm_num)
theorem B2096355 : Blo 2095435 2096355 := bstep (se 1 (by rfl) ⟨1572266, by rfl⟩ : syracuseStep 2096355 = 3144533) B3144533
theorem B4477285 : Blo 2095435 4477285 := bbase (se 4 (by rfl) ⟨419745, by rfl⟩ : syracuseStep 4477285 = 839491) (by norm_num)
theorem B5969713 : Blo 2095435 5969713 := bstep (se 2 (by rfl) ⟨2238642, by rfl⟩ : syracuseStep 5969713 = 4477285) B4477285
theorem B7959617 : Blo 2095435 7959617 := bstep (se 2 (by rfl) ⟨2984856, by rfl⟩ : syracuseStep 7959617 = 5969713) B5969713
theorem B5306411 : Blo 2095435 5306411 := bstep (se 1 (by rfl) ⟨3979808, by rfl⟩ : syracuseStep 5306411 = 7959617) B7959617
theorem B3537607 : Blo 2095435 3537607 := bstep (se 1 (by rfl) ⟨2653205, by rfl⟩ : syracuseStep 3537607 = 5306411) B5306411
theorem B4716809 : Blo 2095435 4716809 := bstep (se 2 (by rfl) ⟨1768803, by rfl⟩ : syracuseStep 4716809 = 3537607) B3537607
theorem B3144539 : Blo 2095435 3144539 := bstep (se 1 (by rfl) ⟨2358404, by rfl⟩ : syracuseStep 3144539 = 4716809) B4716809
theorem B2096359 : Blo 2095435 2096359 := bstep (se 1 (by rfl) ⟨1572269, by rfl⟩ : syracuseStep 2096359 = 3144539) B3144539
theorem B2358409 : Blo 2095435 2358409 := bbase (se 2 (by rfl) ⟨884403, by rfl⟩ : syracuseStep 2358409 = 1768807) (by norm_num)
theorem B3144545 : Blo 2095435 3144545 := bstep (se 2 (by rfl) ⟨1179204, by rfl⟩ : syracuseStep 3144545 = 2358409) B2358409
theorem B2096363 : Blo 2095435 2096363 := bstep (se 1 (by rfl) ⟨1572272, by rfl⟩ : syracuseStep 2096363 = 3144545) B3144545
theorem B18153557 : Blo 2095435 18153557 := bbase (se 8 (by rfl) ⟨106368, by rfl⟩ : syracuseStep 18153557 = 212737) (by norm_num)
theorem B12102371 : Blo 2095435 12102371 := bstep (se 1 (by rfl) ⟨9076778, by rfl⟩ : syracuseStep 12102371 = 18153557) B18153557
theorem B8068247 : Blo 2095435 8068247 := bstep (se 1 (by rfl) ⟨6051185, by rfl⟩ : syracuseStep 8068247 = 12102371) B12102371
theorem B5378831 : Blo 2095435 5378831 := bstep (se 1 (by rfl) ⟨4034123, by rfl⟩ : syracuseStep 5378831 = 8068247) B8068247
theorem B3585887 : Blo 2095435 3585887 := bstep (se 1 (by rfl) ⟨2689415, by rfl⟩ : syracuseStep 3585887 = 5378831) B5378831
theorem B2390591 : Blo 2095435 2390591 := bstep (se 1 (by rfl) ⟨1792943, by rfl⟩ : syracuseStep 2390591 = 3585887) B3585887
theorem B6374909 : Blo 2095435 6374909 := bstep (se 3 (by rfl) ⟨1195295, by rfl⟩ : syracuseStep 6374909 = 2390591) B2390591
theorem B16999757 : Blo 2095435 16999757 := bstep (se 3 (by rfl) ⟨3187454, by rfl⟩ : syracuseStep 16999757 = 6374909) B6374909
theorem B11333171 : Blo 2095435 11333171 := bstep (se 1 (by rfl) ⟨8499878, by rfl⟩ : syracuseStep 11333171 = 16999757) B16999757
theorem B7555447 : Blo 2095435 7555447 := bstep (se 1 (by rfl) ⟨5666585, by rfl⟩ : syracuseStep 7555447 = 11333171) B11333171
theorem B40295717 : Blo 2095435 40295717 := bstep (se 4 (by rfl) ⟨3777723, by rfl⟩ : syracuseStep 40295717 = 7555447) B7555447
theorem B26863811 : Blo 2095435 26863811 := bstep (se 1 (by rfl) ⟨20147858, by rfl⟩ : syracuseStep 26863811 = 40295717) B40295717
theorem B17909207 : Blo 2095435 17909207 := bstep (se 1 (by rfl) ⟨13431905, by rfl⟩ : syracuseStep 17909207 = 26863811) B26863811
theorem B11939471 : Blo 2095435 11939471 := bstep (se 1 (by rfl) ⟨8954603, by rfl⟩ : syracuseStep 11939471 = 17909207) B17909207
theorem B7959647 : Blo 2095435 7959647 := bstep (se 1 (by rfl) ⟨5969735, by rfl⟩ : syracuseStep 7959647 = 11939471) B11939471
theorem B5306431 : Blo 2095435 5306431 := bstep (se 1 (by rfl) ⟨3979823, by rfl⟩ : syracuseStep 5306431 = 7959647) B7959647
theorem B7075241 : Blo 2095435 7075241 := bstep (se 2 (by rfl) ⟨2653215, by rfl⟩ : syracuseStep 7075241 = 5306431) B5306431
theorem B4716827 : Blo 2095435 4716827 := bstep (se 1 (by rfl) ⟨3537620, by rfl⟩ : syracuseStep 4716827 = 7075241) B7075241
theorem B3144551 : Blo 2095435 3144551 := bstep (se 1 (by rfl) ⟨2358413, by rfl⟩ : syracuseStep 3144551 = 4716827) B4716827
theorem B2096367 : Blo 2095435 2096367 := bstep (se 1 (by rfl) ⟨1572275, by rfl⟩ : syracuseStep 2096367 = 3144551) B3144551
theorem B3144557 : Blo 2095435 3144557 := bbase (se 3 (by rfl) ⟨589604, by rfl⟩ : syracuseStep 3144557 = 1179209) (by norm_num)
theorem B2096371 : Blo 2095435 2096371 := bstep (se 1 (by rfl) ⟨1572278, by rfl⟩ : syracuseStep 2096371 = 3144557) B3144557
theorem B4716845 : Blo 2095435 4716845 := bbase (se 3 (by rfl) ⟨884408, by rfl⟩ : syracuseStep 4716845 = 1768817) (by norm_num)
theorem B3144563 : Blo 2095435 3144563 := bstep (se 1 (by rfl) ⟨2358422, by rfl⟩ : syracuseStep 3144563 = 4716845) B4716845
theorem B2096375 : Blo 2095435 2096375 := bstep (se 1 (by rfl) ⟨1572281, by rfl⟩ : syracuseStep 2096375 = 3144563) B3144563
theorem B7555493 : Blo 2095435 7555493 := bbase (se 4 (by rfl) ⟨708327, by rfl⟩ : syracuseStep 7555493 = 1416655) (by norm_num)
theorem B5036995 : Blo 2095435 5036995 := bstep (se 1 (by rfl) ⟨3777746, by rfl⟩ : syracuseStep 5036995 = 7555493) B7555493
theorem B6715993 : Blo 2095435 6715993 := bstep (se 2 (by rfl) ⟨2518497, by rfl⟩ : syracuseStep 6715993 = 5036995) B5036995
theorem B8954657 : Blo 2095435 8954657 := bstep (se 2 (by rfl) ⟨3357996, by rfl⟩ : syracuseStep 8954657 = 6715993) B6715993
theorem B5969771 : Blo 2095435 5969771 := bstep (se 1 (by rfl) ⟨4477328, by rfl⟩ : syracuseStep 5969771 = 8954657) B8954657
theorem B3979847 : Blo 2095435 3979847 := bstep (se 1 (by rfl) ⟨2984885, by rfl⟩ : syracuseStep 3979847 = 5969771) B5969771
theorem B2653231 : Blo 2095435 2653231 := bstep (se 1 (by rfl) ⟨1989923, by rfl⟩ : syracuseStep 2653231 = 3979847) B3979847
theorem B3537641 : Blo 2095435 3537641 := bstep (se 2 (by rfl) ⟨1326615, by rfl⟩ : syracuseStep 3537641 = 2653231) B2653231
theorem B2358427 : Blo 2095435 2358427 := bstep (se 1 (by rfl) ⟨1768820, by rfl⟩ : syracuseStep 2358427 = 3537641) B3537641
theorem B3144569 : Blo 2095435 3144569 := bstep (se 2 (by rfl) ⟨1179213, by rfl⟩ : syracuseStep 3144569 = 2358427) B2358427
theorem B2096379 : Blo 2095435 2096379 := bstep (se 1 (by rfl) ⟨1572284, by rfl⟩ : syracuseStep 2096379 = 3144569) B3144569
theorem B2390609 : Blo 2095435 2390609 := bbase (se 2 (by rfl) ⟨896478, by rfl⟩ : syracuseStep 2390609 = 1792957) (by norm_num)
theorem B6374957 : Blo 2095435 6374957 := bstep (se 3 (by rfl) ⟨1195304, by rfl⟩ : syracuseStep 6374957 = 2390609) B2390609
theorem B16999885 : Blo 2095435 16999885 := bstep (se 3 (by rfl) ⟨3187478, by rfl⟩ : syracuseStep 16999885 = 6374957) B6374957
theorem B22666513 : Blo 2095435 22666513 := bstep (se 2 (by rfl) ⟨8499942, by rfl⟩ : syracuseStep 22666513 = 16999885) B16999885
theorem B30222017 : Blo 2095435 30222017 := bstep (se 2 (by rfl) ⟨11333256, by rfl⟩ : syracuseStep 30222017 = 22666513) B22666513
theorem B20148011 : Blo 2095435 20148011 := bstep (se 1 (by rfl) ⟨15111008, by rfl⟩ : syracuseStep 20148011 = 30222017) B30222017
theorem B13432007 : Blo 2095435 13432007 := bstep (se 1 (by rfl) ⟨10074005, by rfl⟩ : syracuseStep 13432007 = 20148011) B20148011
theorem B35818685 : Blo 2095435 35818685 := bstep (se 3 (by rfl) ⟨6716003, by rfl⟩ : syracuseStep 35818685 = 13432007) B13432007
theorem B23879123 : Blo 2095435 23879123 := bstep (se 1 (by rfl) ⟨17909342, by rfl⟩ : syracuseStep 23879123 = 35818685) B35818685
theorem B15919415 : Blo 2095435 15919415 := bstep (se 1 (by rfl) ⟨11939561, by rfl⟩ : syracuseStep 15919415 = 23879123) B23879123
theorem B10612943 : Blo 2095435 10612943 := bstep (se 1 (by rfl) ⟨7959707, by rfl⟩ : syracuseStep 10612943 = 15919415) B15919415
theorem B7075295 : Blo 2095435 7075295 := bstep (se 1 (by rfl) ⟨5306471, by rfl⟩ : syracuseStep 7075295 = 10612943) B10612943
theorem B4716863 : Blo 2095435 4716863 := bstep (se 1 (by rfl) ⟨3537647, by rfl⟩ : syracuseStep 4716863 = 7075295) B7075295
theorem B3144575 : Blo 2095435 3144575 := bstep (se 1 (by rfl) ⟨2358431, by rfl⟩ : syracuseStep 3144575 = 4716863) B4716863
theorem B2096383 : Blo 2095435 2096383 := bstep (se 1 (by rfl) ⟨1572287, by rfl⟩ : syracuseStep 2096383 = 3144575) B3144575
theorem B3144581 : Blo 2095435 3144581 := bbase (se 4 (by rfl) ⟨294804, by rfl⟩ : syracuseStep 3144581 = 589609) (by norm_num)
theorem B2096387 : Blo 2095435 2096387 := bstep (se 1 (by rfl) ⟨1572290, by rfl⟩ : syracuseStep 2096387 = 3144581) B3144581
theorem B3537661 : Blo 2095435 3537661 := bbase (se 3 (by rfl) ⟨663311, by rfl⟩ : syracuseStep 3537661 = 1326623) (by norm_num)
theorem B4716881 : Blo 2095435 4716881 := bstep (se 2 (by rfl) ⟨1768830, by rfl⟩ : syracuseStep 4716881 = 3537661) B3537661
theorem B3144587 : Blo 2095435 3144587 := bstep (se 1 (by rfl) ⟨2358440, by rfl⟩ : syracuseStep 3144587 = 4716881) B4716881
theorem B2096391 : Blo 2095435 2096391 := bstep (se 1 (by rfl) ⟨1572293, by rfl⟩ : syracuseStep 2096391 = 3144587) B3144587
theorem B2358445 : Blo 2095435 2358445 := bbase (se 3 (by rfl) ⟨442208, by rfl⟩ : syracuseStep 2358445 = 884417) (by norm_num)
theorem B3144593 : Blo 2095435 3144593 := bstep (se 2 (by rfl) ⟨1179222, by rfl⟩ : syracuseStep 3144593 = 2358445) B2358445
theorem B2096395 : Blo 2095435 2096395 := bstep (se 1 (by rfl) ⟨1572296, by rfl⟩ : syracuseStep 2096395 = 3144593) B3144593
theorem B7075349 : Blo 2095435 7075349 := bbase (se 6 (by rfl) ⟨165828, by rfl⟩ : syracuseStep 7075349 = 331657) (by norm_num)
theorem B4716899 : Blo 2095435 4716899 := bstep (se 1 (by rfl) ⟨3537674, by rfl⟩ : syracuseStep 4716899 = 7075349) B7075349
theorem B3144599 : Blo 2095435 3144599 := bstep (se 1 (by rfl) ⟨2358449, by rfl⟩ : syracuseStep 3144599 = 4716899) B4716899
theorem B2096399 : Blo 2095435 2096399 := bstep (se 1 (by rfl) ⟨1572299, by rfl⟩ : syracuseStep 2096399 = 3144599) B3144599
theorem B3144605 : Blo 2095435 3144605 := bbase (se 3 (by rfl) ⟨589613, by rfl⟩ : syracuseStep 3144605 = 1179227) (by norm_num)
theorem B2096403 : Blo 2095435 2096403 := bstep (se 1 (by rfl) ⟨1572302, by rfl⟩ : syracuseStep 2096403 = 3144605) B3144605
theorem B4716917 : Blo 2095435 4716917 := bbase (se 5 (by rfl) ⟨221105, by rfl⟩ : syracuseStep 4716917 = 442211) (by norm_num)
theorem B3144611 : Blo 2095435 3144611 := bstep (se 1 (by rfl) ⟨2358458, by rfl⟩ : syracuseStep 3144611 = 4716917) B4716917
theorem B2096407 : Blo 2095435 2096407 := bstep (se 1 (by rfl) ⟨1572305, by rfl⟩ : syracuseStep 2096407 = 3144611) B3144611
theorem B17000117 : Blo 2095435 17000117 := bbase (se 5 (by rfl) ⟨796880, by rfl⟩ : syracuseStep 17000117 = 1593761) (by norm_num)
theorem B11333411 : Blo 2095435 11333411 := bstep (se 1 (by rfl) ⟨8500058, by rfl⟩ : syracuseStep 11333411 = 17000117) B17000117
theorem B7555607 : Blo 2095435 7555607 := bstep (se 1 (by rfl) ⟨5666705, by rfl⟩ : syracuseStep 7555607 = 11333411) B11333411
theorem B5037071 : Blo 2095435 5037071 := bstep (se 1 (by rfl) ⟨3777803, by rfl⟩ : syracuseStep 5037071 = 7555607) B7555607
theorem B13432189 : Blo 2095435 13432189 := bstep (se 3 (by rfl) ⟨2518535, by rfl⟩ : syracuseStep 13432189 = 5037071) B5037071
theorem B17909585 : Blo 2095435 17909585 := bstep (se 2 (by rfl) ⟨6716094, by rfl⟩ : syracuseStep 17909585 = 13432189) B13432189
theorem B11939723 : Blo 2095435 11939723 := bstep (se 1 (by rfl) ⟨8954792, by rfl⟩ : syracuseStep 11939723 = 17909585) B17909585
theorem B7959815 : Blo 2095435 7959815 := bstep (se 1 (by rfl) ⟨5969861, by rfl⟩ : syracuseStep 7959815 = 11939723) B11939723
theorem B5306543 : Blo 2095435 5306543 := bstep (se 1 (by rfl) ⟨3979907, by rfl⟩ : syracuseStep 5306543 = 7959815) B7959815
theorem B3537695 : Blo 2095435 3537695 := bstep (se 1 (by rfl) ⟨2653271, by rfl⟩ : syracuseStep 3537695 = 5306543) B5306543
theorem B2358463 : Blo 2095435 2358463 := bstep (se 1 (by rfl) ⟨1768847, by rfl⟩ : syracuseStep 2358463 = 3537695) B3537695
theorem B3144617 : Blo 2095435 3144617 := bstep (se 2 (by rfl) ⟨1179231, by rfl⟩ : syracuseStep 3144617 = 2358463) B2358463
theorem B2096411 : Blo 2095435 2096411 := bstep (se 1 (by rfl) ⟨1572308, by rfl⟩ : syracuseStep 2096411 = 3144617) B3144617
theorem B7959829 : Blo 2095435 7959829 := bbase (se 6 (by rfl) ⟨186558, by rfl⟩ : syracuseStep 7959829 = 373117) (by norm_num)
theorem B10613105 : Blo 2095435 10613105 := bstep (se 2 (by rfl) ⟨3979914, by rfl⟩ : syracuseStep 10613105 = 7959829) B7959829
theorem B7075403 : Blo 2095435 7075403 := bstep (se 1 (by rfl) ⟨5306552, by rfl⟩ : syracuseStep 7075403 = 10613105) B10613105
theorem B4716935 : Blo 2095435 4716935 := bstep (se 1 (by rfl) ⟨3537701, by rfl⟩ : syracuseStep 4716935 = 7075403) B7075403
theorem B3144623 : Blo 2095435 3144623 := bstep (se 1 (by rfl) ⟨2358467, by rfl⟩ : syracuseStep 3144623 = 4716935) B4716935
theorem B2096415 : Blo 2095435 2096415 := bstep (se 1 (by rfl) ⟨1572311, by rfl⟩ : syracuseStep 2096415 = 3144623) B3144623
theorem B3144629 : Blo 2095435 3144629 := bbase (se 5 (by rfl) ⟨147404, by rfl⟩ : syracuseStep 3144629 = 294809) (by norm_num)
theorem B2096419 : Blo 2095435 2096419 := bstep (se 1 (by rfl) ⟨1572314, by rfl⟩ : syracuseStep 2096419 = 3144629) B3144629
theorem B5306573 : Blo 2095435 5306573 := bbase (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) (by norm_num)
theorem B3537715 : Blo 2095435 3537715 := bstep (se 1 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 3537715 = 5306573) B5306573
theorem B4716953 : Blo 2095435 4716953 := bstep (se 2 (by rfl) ⟨1768857, by rfl⟩ : syracuseStep 4716953 = 3537715) B3537715
theorem B3144635 : Blo 2095435 3144635 := bstep (se 1 (by rfl) ⟨2358476, by rfl⟩ : syracuseStep 3144635 = 4716953) B4716953
theorem B2096423 : Blo 2095435 2096423 := bstep (se 1 (by rfl) ⟨1572317, by rfl⟩ : syracuseStep 2096423 = 3144635) B3144635
theorem B2358481 : Blo 2095435 2358481 := bbase (se 2 (by rfl) ⟨884430, by rfl⟩ : syracuseStep 2358481 = 1768861) (by norm_num)
theorem B3144641 : Blo 2095435 3144641 := bstep (se 2 (by rfl) ⟨1179240, by rfl⟩ : syracuseStep 3144641 = 2358481) B2358481
theorem B2096427 : Blo 2095435 2096427 := bstep (se 1 (by rfl) ⟨1572320, by rfl⟩ : syracuseStep 2096427 = 3144641) B3144641
theorem B3881629 : Blo 2095435 3881629 := bbase (se 3 (by rfl) ⟨727805, by rfl⟩ : syracuseStep 3881629 = 1455611) (by norm_num)
theorem B5175505 : Blo 2095435 5175505 := bstep (se 2 (by rfl) ⟨1940814, by rfl⟩ : syracuseStep 5175505 = 3881629) B3881629
theorem B27602693 : Blo 2095435 27602693 := bstep (se 4 (by rfl) ⟨2587752, by rfl⟩ : syracuseStep 27602693 = 5175505) B5175505
theorem B18401795 : Blo 2095435 18401795 := bstep (se 1 (by rfl) ⟨13801346, by rfl⟩ : syracuseStep 18401795 = 27602693) B27602693
theorem B12267863 : Blo 2095435 12267863 := bstep (se 1 (by rfl) ⟨9200897, by rfl⟩ : syracuseStep 12267863 = 18401795) B18401795
theorem B8178575 : Blo 2095435 8178575 := bstep (se 1 (by rfl) ⟨6133931, by rfl⟩ : syracuseStep 8178575 = 12267863) B12267863
theorem B87238133 : Blo 2095435 87238133 := bstep (se 5 (by rfl) ⟨4089287, by rfl⟩ : syracuseStep 87238133 = 8178575) B8178575
theorem B58158755 : Blo 2095435 58158755 := bstep (se 1 (by rfl) ⟨43619066, by rfl⟩ : syracuseStep 58158755 = 87238133) B87238133
theorem B38772503 : Blo 2095435 38772503 := bstep (se 1 (by rfl) ⟨29079377, by rfl⟩ : syracuseStep 38772503 = 58158755) B58158755
theorem B25848335 : Blo 2095435 25848335 := bstep (se 1 (by rfl) ⟨19386251, by rfl⟩ : syracuseStep 25848335 = 38772503) B38772503
theorem B17232223 : Blo 2095435 17232223 := bstep (se 1 (by rfl) ⟨12924167, by rfl⟩ : syracuseStep 17232223 = 25848335) B25848335
theorem B22976297 : Blo 2095435 22976297 := bstep (se 2 (by rfl) ⟨8616111, by rfl⟩ : syracuseStep 22976297 = 17232223) B17232223
theorem B15317531 : Blo 2095435 15317531 := bstep (se 1 (by rfl) ⟨11488148, by rfl⟩ : syracuseStep 15317531 = 22976297) B22976297
theorem B10211687 : Blo 2095435 10211687 := bstep (se 1 (by rfl) ⟨7658765, by rfl⟩ : syracuseStep 10211687 = 15317531) B15317531
theorem B6807791 : Blo 2095435 6807791 := bstep (se 1 (by rfl) ⟨5105843, by rfl⟩ : syracuseStep 6807791 = 10211687) B10211687
theorem B4538527 : Blo 2095435 4538527 := bstep (se 1 (by rfl) ⟨3403895, by rfl⟩ : syracuseStep 4538527 = 6807791) B6807791
theorem B24205477 : Blo 2095435 24205477 := bstep (se 4 (by rfl) ⟨2269263, by rfl⟩ : syracuseStep 24205477 = 4538527) B4538527
theorem B32273969 : Blo 2095435 32273969 := bstep (se 2 (by rfl) ⟨12102738, by rfl⟩ : syracuseStep 32273969 = 24205477) B24205477
theorem B86063917 : Blo 2095435 86063917 := bstep (se 3 (by rfl) ⟨16136984, by rfl⟩ : syracuseStep 86063917 = 32273969) B32273969
theorem B114751889 : Blo 2095435 114751889 := bstep (se 2 (by rfl) ⟨43031958, by rfl⟩ : syracuseStep 114751889 = 86063917) B86063917
theorem B76501259 : Blo 2095435 76501259 := bstep (se 1 (by rfl) ⟨57375944, by rfl⟩ : syracuseStep 76501259 = 114751889) B114751889
theorem B51000839 : Blo 2095435 51000839 := bstep (se 1 (by rfl) ⟨38250629, by rfl⟩ : syracuseStep 51000839 = 76501259) B76501259
theorem B34000559 : Blo 2095435 34000559 := bstep (se 1 (by rfl) ⟨25500419, by rfl⟩ : syracuseStep 34000559 = 51000839) B51000839
theorem B22667039 : Blo 2095435 22667039 := bstep (se 1 (by rfl) ⟨17000279, by rfl⟩ : syracuseStep 22667039 = 34000559) B34000559
theorem B15111359 : Blo 2095435 15111359 := bstep (se 1 (by rfl) ⟨11333519, by rfl⟩ : syracuseStep 15111359 = 22667039) B22667039
theorem B10074239 : Blo 2095435 10074239 := bstep (se 1 (by rfl) ⟨7555679, by rfl⟩ : syracuseStep 10074239 = 15111359) B15111359
theorem B6716159 : Blo 2095435 6716159 := bstep (se 1 (by rfl) ⟨5037119, by rfl⟩ : syracuseStep 6716159 = 10074239) B10074239
theorem B4477439 : Blo 2095435 4477439 := bstep (se 1 (by rfl) ⟨3358079, by rfl⟩ : syracuseStep 4477439 = 6716159) B6716159
theorem B2984959 : Blo 2095435 2984959 := bstep (se 1 (by rfl) ⟨2238719, by rfl⟩ : syracuseStep 2984959 = 4477439) B4477439
theorem B3979945 : Blo 2095435 3979945 := bstep (se 2 (by rfl) ⟨1492479, by rfl⟩ : syracuseStep 3979945 = 2984959) B2984959
theorem B5306593 : Blo 2095435 5306593 := bstep (se 2 (by rfl) ⟨1989972, by rfl⟩ : syracuseStep 5306593 = 3979945) B3979945
theorem B7075457 : Blo 2095435 7075457 := bstep (se 2 (by rfl) ⟨2653296, by rfl⟩ : syracuseStep 7075457 = 5306593) B5306593
theorem B4716971 : Blo 2095435 4716971 := bstep (se 1 (by rfl) ⟨3537728, by rfl⟩ : syracuseStep 4716971 = 7075457) B7075457
theorem B3144647 : Blo 2095435 3144647 := bstep (se 1 (by rfl) ⟨2358485, by rfl⟩ : syracuseStep 3144647 = 4716971) B4716971
theorem B2096431 : Blo 2095435 2096431 := bstep (se 1 (by rfl) ⟨1572323, by rfl⟩ : syracuseStep 2096431 = 3144647) B3144647
theorem B3144653 : Blo 2095435 3144653 := bbase (se 3 (by rfl) ⟨589622, by rfl⟩ : syracuseStep 3144653 = 1179245) (by norm_num)
theorem B2096435 : Blo 2095435 2096435 := bstep (se 1 (by rfl) ⟨1572326, by rfl⟩ : syracuseStep 2096435 = 3144653) B3144653
theorem B4716989 : Blo 2095435 4716989 := bbase (se 3 (by rfl) ⟨884435, by rfl⟩ : syracuseStep 4716989 = 1768871) (by norm_num)
theorem B3144659 : Blo 2095435 3144659 := bstep (se 1 (by rfl) ⟨2358494, by rfl⟩ : syracuseStep 3144659 = 4716989) B4716989
theorem B2096439 : Blo 2095435 2096439 := bstep (se 1 (by rfl) ⟨1572329, by rfl⟩ : syracuseStep 2096439 = 3144659) B3144659
theorem B3537749 : Blo 2095435 3537749 := bbase (se 9 (by rfl) ⟨10364, by rfl⟩ : syracuseStep 3537749 = 20729) (by norm_num)
theorem B2358499 : Blo 2095435 2358499 := bstep (se 1 (by rfl) ⟨1768874, by rfl⟩ : syracuseStep 2358499 = 3537749) B3537749
theorem B3144665 : Blo 2095435 3144665 := bstep (se 2 (by rfl) ⟨1179249, by rfl⟩ : syracuseStep 3144665 = 2358499) B2358499
theorem B2096443 : Blo 2095435 2096443 := bstep (se 1 (by rfl) ⟨1572332, by rfl⟩ : syracuseStep 2096443 = 3144665) B3144665
theorem B5037157 : Blo 2095435 5037157 := bbase (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) (by norm_num)
theorem B6716209 : Blo 2095435 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B8954945 : Blo 2095435 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B5969963 : Blo 2095435 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B15919901 : Blo 2095435 15919901 := bstep (se 3 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 15919901 = 5969963) B5969963
theorem B10613267 : Blo 2095435 10613267 := bstep (se 1 (by rfl) ⟨7959950, by rfl⟩ : syracuseStep 10613267 = 15919901) B15919901
theorem B7075511 : Blo 2095435 7075511 := bstep (se 1 (by rfl) ⟨5306633, by rfl⟩ : syracuseStep 7075511 = 10613267) B10613267
theorem B4717007 : Blo 2095435 4717007 := bstep (se 1 (by rfl) ⟨3537755, by rfl⟩ : syracuseStep 4717007 = 7075511) B7075511
theorem B3144671 : Blo 2095435 3144671 := bstep (se 1 (by rfl) ⟨2358503, by rfl⟩ : syracuseStep 3144671 = 4717007) B4717007
theorem B2096447 : Blo 2095435 2096447 := bstep (se 1 (by rfl) ⟨1572335, by rfl⟩ : syracuseStep 2096447 = 3144671) B3144671
theorem B3144677 : Blo 2095435 3144677 := bbase (se 4 (by rfl) ⟨294813, by rfl⟩ : syracuseStep 3144677 = 589627) (by norm_num)
theorem B2096451 : Blo 2095435 2096451 := bstep (se 1 (by rfl) ⟨1572338, by rfl⟩ : syracuseStep 2096451 = 3144677) B3144677
theorem B8954981 : Blo 2095435 8954981 := bbase (se 4 (by rfl) ⟨839529, by rfl⟩ : syracuseStep 8954981 = 1679059) (by norm_num)
theorem B5969987 : Blo 2095435 5969987 := bstep (se 1 (by rfl) ⟨4477490, by rfl⟩ : syracuseStep 5969987 = 8954981) B8954981
theorem B3979991 : Blo 2095435 3979991 := bstep (se 1 (by rfl) ⟨2984993, by rfl⟩ : syracuseStep 3979991 = 5969987) B5969987
theorem B2653327 : Blo 2095435 2653327 := bstep (se 1 (by rfl) ⟨1989995, by rfl⟩ : syracuseStep 2653327 = 3979991) B3979991
theorem B3537769 : Blo 2095435 3537769 := bstep (se 2 (by rfl) ⟨1326663, by rfl⟩ : syracuseStep 3537769 = 2653327) B2653327
theorem B4717025 : Blo 2095435 4717025 := bstep (se 2 (by rfl) ⟨1768884, by rfl⟩ : syracuseStep 4717025 = 3537769) B3537769
theorem B3144683 : Blo 2095435 3144683 := bstep (se 1 (by rfl) ⟨2358512, by rfl⟩ : syracuseStep 3144683 = 4717025) B4717025
theorem B2096455 : Blo 2095435 2096455 := bstep (se 1 (by rfl) ⟨1572341, by rfl⟩ : syracuseStep 2096455 = 3144683) B3144683
theorem B2358517 : Blo 2095435 2358517 := bbase (se 5 (by rfl) ⟨110555, by rfl⟩ : syracuseStep 2358517 = 221111) (by norm_num)
theorem B3144689 : Blo 2095435 3144689 := bstep (se 2 (by rfl) ⟨1179258, by rfl⟩ : syracuseStep 3144689 = 2358517) B2358517
theorem B2096459 : Blo 2095435 2096459 := bstep (se 1 (by rfl) ⟨1572344, by rfl⟩ : syracuseStep 2096459 = 3144689) B3144689
theorem B2653337 : Blo 2095435 2653337 := bbase (se 2 (by rfl) ⟨995001, by rfl⟩ : syracuseStep 2653337 = 1990003) (by norm_num)
theorem B7075565 : Blo 2095435 7075565 := bstep (se 3 (by rfl) ⟨1326668, by rfl⟩ : syracuseStep 7075565 = 2653337) B2653337
theorem B4717043 : Blo 2095435 4717043 := bstep (se 1 (by rfl) ⟨3537782, by rfl⟩ : syracuseStep 4717043 = 7075565) B7075565
theorem B3144695 : Blo 2095435 3144695 := bstep (se 1 (by rfl) ⟨2358521, by rfl⟩ : syracuseStep 3144695 = 4717043) B4717043
theorem B2096463 : Blo 2095435 2096463 := bstep (se 1 (by rfl) ⟨1572347, by rfl⟩ : syracuseStep 2096463 = 3144695) B3144695
theorem B3144701 : Blo 2095435 3144701 := bbase (se 3 (by rfl) ⟨589631, by rfl⟩ : syracuseStep 3144701 = 1179263) (by norm_num)
theorem B2096467 : Blo 2095435 2096467 := bstep (se 1 (by rfl) ⟨1572350, by rfl⟩ : syracuseStep 2096467 = 3144701) B3144701
theorem B4717061 : Blo 2095435 4717061 := bbase (se 4 (by rfl) ⟨442224, by rfl⟩ : syracuseStep 4717061 = 884449) (by norm_num)
theorem B3144707 : Blo 2095435 3144707 := bstep (se 1 (by rfl) ⟨2358530, by rfl⟩ : syracuseStep 3144707 = 4717061) B4717061
theorem B2096471 : Blo 2095435 2096471 := bstep (se 1 (by rfl) ⟨1572353, by rfl⟩ : syracuseStep 2096471 = 3144707) B3144707
theorem B3980029 : Blo 2095435 3980029 := bbase (se 3 (by rfl) ⟨746255, by rfl⟩ : syracuseStep 3980029 = 1492511) (by norm_num)
theorem B5306705 : Blo 2095435 5306705 := bstep (se 2 (by rfl) ⟨1990014, by rfl⟩ : syracuseStep 5306705 = 3980029) B3980029
theorem B3537803 : Blo 2095435 3537803 := bstep (se 1 (by rfl) ⟨2653352, by rfl⟩ : syracuseStep 3537803 = 5306705) B5306705
theorem B2358535 : Blo 2095435 2358535 := bstep (se 1 (by rfl) ⟨1768901, by rfl⟩ : syracuseStep 2358535 = 3537803) B3537803
theorem B3144713 : Blo 2095435 3144713 := bstep (se 2 (by rfl) ⟨1179267, by rfl⟩ : syracuseStep 3144713 = 2358535) B2358535
theorem B2096475 : Blo 2095435 2096475 := bstep (se 1 (by rfl) ⟨1572356, by rfl⟩ : syracuseStep 2096475 = 3144713) B3144713
theorem B10613429 : Blo 2095435 10613429 := bbase (se 5 (by rfl) ⟨497504, by rfl⟩ : syracuseStep 10613429 = 995009) (by norm_num)
theorem B7075619 : Blo 2095435 7075619 := bstep (se 1 (by rfl) ⟨5306714, by rfl⟩ : syracuseStep 7075619 = 10613429) B10613429
theorem B4717079 : Blo 2095435 4717079 := bstep (se 1 (by rfl) ⟨3537809, by rfl⟩ : syracuseStep 4717079 = 7075619) B7075619
theorem B3144719 : Blo 2095435 3144719 := bstep (se 1 (by rfl) ⟨2358539, by rfl⟩ : syracuseStep 3144719 = 4717079) B4717079
theorem B2096479 : Blo 2095435 2096479 := bstep (se 1 (by rfl) ⟨1572359, by rfl⟩ : syracuseStep 2096479 = 3144719) B3144719
theorem B3144725 : Blo 2095435 3144725 := bbase (se 6 (by rfl) ⟨73704, by rfl⟩ : syracuseStep 3144725 = 147409) (by norm_num)
theorem B2096483 : Blo 2095435 2096483 := bstep (se 1 (by rfl) ⟨1572362, by rfl⟩ : syracuseStep 2096483 = 3144725) B3144725
theorem B20149013 : Blo 2095435 20149013 := bbase (se 6 (by rfl) ⟨472242, by rfl⟩ : syracuseStep 20149013 = 944485) (by norm_num)
theorem B13432675 : Blo 2095435 13432675 := bstep (se 1 (by rfl) ⟨10074506, by rfl⟩ : syracuseStep 13432675 = 20149013) B20149013
theorem B17910233 : Blo 2095435 17910233 := bstep (se 2 (by rfl) ⟨6716337, by rfl⟩ : syracuseStep 17910233 = 13432675) B13432675
theorem B11940155 : Blo 2095435 11940155 := bstep (se 1 (by rfl) ⟨8955116, by rfl⟩ : syracuseStep 11940155 = 17910233) B17910233
theorem B7960103 : Blo 2095435 7960103 := bstep (se 1 (by rfl) ⟨5970077, by rfl⟩ : syracuseStep 7960103 = 11940155) B11940155
theorem B5306735 : Blo 2095435 5306735 := bstep (se 1 (by rfl) ⟨3980051, by rfl⟩ : syracuseStep 5306735 = 7960103) B7960103
theorem B3537823 : Blo 2095435 3537823 := bstep (se 1 (by rfl) ⟨2653367, by rfl⟩ : syracuseStep 3537823 = 5306735) B5306735
theorem B4717097 : Blo 2095435 4717097 := bstep (se 2 (by rfl) ⟨1768911, by rfl⟩ : syracuseStep 4717097 = 3537823) B3537823
theorem B3144731 : Blo 2095435 3144731 := bstep (se 1 (by rfl) ⟨2358548, by rfl⟩ : syracuseStep 3144731 = 4717097) B4717097
theorem B2096487 : Blo 2095435 2096487 := bstep (se 1 (by rfl) ⟨1572365, by rfl⟩ : syracuseStep 2096487 = 3144731) B3144731
theorem B2358553 : Blo 2095435 2358553 := bbase (se 2 (by rfl) ⟨884457, by rfl⟩ : syracuseStep 2358553 = 1768915) (by norm_num)
theorem B3144737 : Blo 2095435 3144737 := bstep (se 2 (by rfl) ⟨1179276, by rfl⟩ : syracuseStep 3144737 = 2358553) B2358553
theorem B2096491 : Blo 2095435 2096491 := bstep (se 1 (by rfl) ⟨1572368, by rfl⟩ : syracuseStep 2096491 = 3144737) B3144737
theorem B7960133 : Blo 2095435 7960133 := bbase (se 4 (by rfl) ⟨746262, by rfl⟩ : syracuseStep 7960133 = 1492525) (by norm_num)
theorem B5306755 : Blo 2095435 5306755 := bstep (se 1 (by rfl) ⟨3980066, by rfl⟩ : syracuseStep 5306755 = 7960133) B7960133
theorem B7075673 : Blo 2095435 7075673 := bstep (se 2 (by rfl) ⟨2653377, by rfl⟩ : syracuseStep 7075673 = 5306755) B5306755
theorem B4717115 : Blo 2095435 4717115 := bstep (se 1 (by rfl) ⟨3537836, by rfl⟩ : syracuseStep 4717115 = 7075673) B7075673
theorem B3144743 : Blo 2095435 3144743 := bstep (se 1 (by rfl) ⟨2358557, by rfl⟩ : syracuseStep 3144743 = 4717115) B4717115
theorem B2096495 : Blo 2095435 2096495 := bstep (se 1 (by rfl) ⟨1572371, by rfl⟩ : syracuseStep 2096495 = 3144743) B3144743
theorem B3144749 : Blo 2095435 3144749 := bbase (se 3 (by rfl) ⟨589640, by rfl⟩ : syracuseStep 3144749 = 1179281) (by norm_num)
theorem B2096499 : Blo 2095435 2096499 := bstep (se 1 (by rfl) ⟨1572374, by rfl⟩ : syracuseStep 2096499 = 3144749) B3144749
theorem B4717133 : Blo 2095435 4717133 := bbase (se 3 (by rfl) ⟨884462, by rfl⟩ : syracuseStep 4717133 = 1768925) (by norm_num)
theorem B3144755 : Blo 2095435 3144755 := bstep (se 1 (by rfl) ⟨2358566, by rfl⟩ : syracuseStep 3144755 = 4717133) B4717133
theorem B2096503 : Blo 2095435 2096503 := bstep (se 1 (by rfl) ⟨1572377, by rfl⟩ : syracuseStep 2096503 = 3144755) B3144755
theorem B2653393 : Blo 2095435 2653393 := bbase (se 2 (by rfl) ⟨995022, by rfl⟩ : syracuseStep 2653393 = 1990045) (by norm_num)
theorem B3537857 : Blo 2095435 3537857 := bstep (se 2 (by rfl) ⟨1326696, by rfl⟩ : syracuseStep 3537857 = 2653393) B2653393
theorem B2358571 : Blo 2095435 2358571 := bstep (se 1 (by rfl) ⟨1768928, by rfl⟩ : syracuseStep 2358571 = 3537857) B3537857
theorem B3144761 : Blo 2095435 3144761 := bstep (se 2 (by rfl) ⟨1179285, by rfl⟩ : syracuseStep 3144761 = 2358571) B2358571
theorem B2096507 : Blo 2095435 2096507 := bstep (se 1 (by rfl) ⟨1572380, by rfl⟩ : syracuseStep 2096507 = 3144761) B3144761
theorem B4145237 : Blo 2095435 4145237 := bbase (se 8 (by rfl) ⟨24288, by rfl⟩ : syracuseStep 4145237 = 48577) (by norm_num)
theorem B2763491 : Blo 2095435 2763491 := bstep (se 1 (by rfl) ⟨2072618, by rfl⟩ : syracuseStep 2763491 = 4145237) B4145237
theorem B7369309 : Blo 2095435 7369309 := bstep (se 3 (by rfl) ⟨1381745, by rfl⟩ : syracuseStep 7369309 = 2763491) B2763491
theorem B39302981 : Blo 2095435 39302981 := bstep (se 4 (by rfl) ⟨3684654, by rfl⟩ : syracuseStep 39302981 = 7369309) B7369309
theorem B26201987 : Blo 2095435 26201987 := bstep (se 1 (by rfl) ⟨19651490, by rfl⟩ : syracuseStep 26201987 = 39302981) B39302981
theorem B17467991 : Blo 2095435 17467991 := bstep (se 1 (by rfl) ⟨13100993, by rfl⟩ : syracuseStep 17467991 = 26201987) B26201987
theorem B11645327 : Blo 2095435 11645327 := bstep (se 1 (by rfl) ⟨8733995, by rfl⟩ : syracuseStep 11645327 = 17467991) B17467991
theorem B7763551 : Blo 2095435 7763551 := bstep (se 1 (by rfl) ⟨5822663, by rfl⟩ : syracuseStep 7763551 = 11645327) B11645327
theorem B165622421 : Blo 2095435 165622421 := bstep (se 6 (by rfl) ⟨3881775, by rfl⟩ : syracuseStep 165622421 = 7763551) B7763551
theorem B110414947 : Blo 2095435 110414947 := bstep (se 1 (by rfl) ⟨82811210, by rfl⟩ : syracuseStep 110414947 = 165622421) B165622421
theorem B147219929 : Blo 2095435 147219929 := bstep (se 2 (by rfl) ⟨55207473, by rfl⟩ : syracuseStep 147219929 = 110414947) B110414947
theorem B98146619 : Blo 2095435 98146619 := bstep (se 1 (by rfl) ⟨73609964, by rfl⟩ : syracuseStep 98146619 = 147219929) B147219929
theorem B65431079 : Blo 2095435 65431079 := bstep (se 1 (by rfl) ⟨49073309, by rfl⟩ : syracuseStep 65431079 = 98146619) B98146619
theorem B43620719 : Blo 2095435 43620719 := bstep (se 1 (by rfl) ⟨32715539, by rfl⟩ : syracuseStep 43620719 = 65431079) B65431079
theorem B116321917 : Blo 2095435 116321917 := bstep (se 3 (by rfl) ⟨21810359, by rfl⟩ : syracuseStep 116321917 = 43620719) B43620719
theorem B155095889 : Blo 2095435 155095889 := bstep (se 2 (by rfl) ⟨58160958, by rfl⟩ : syracuseStep 155095889 = 116321917) B116321917
theorem B413589037 : Blo 2095435 413589037 := bstep (se 3 (by rfl) ⟨77547944, by rfl⟩ : syracuseStep 413589037 = 155095889) B155095889
theorem B551452049 : Blo 2095435 551452049 := bstep (se 2 (by rfl) ⟨206794518, by rfl⟩ : syracuseStep 551452049 = 413589037) B413589037
theorem B367634699 : Blo 2095435 367634699 := bstep (se 1 (by rfl) ⟨275726024, by rfl⟩ : syracuseStep 367634699 = 551452049) B551452049
theorem B245089799 : Blo 2095435 245089799 := bstep (se 1 (by rfl) ⟨183817349, by rfl⟩ : syracuseStep 245089799 = 367634699) B367634699
theorem B163393199 : Blo 2095435 163393199 := bstep (se 1 (by rfl) ⟨122544899, by rfl⟩ : syracuseStep 163393199 = 245089799) B245089799
theorem B108928799 : Blo 2095435 108928799 := bstep (se 1 (by rfl) ⟨81696599, by rfl⟩ : syracuseStep 108928799 = 163393199) B163393199
theorem B72619199 : Blo 2095435 72619199 := bstep (se 1 (by rfl) ⟨54464399, by rfl⟩ : syracuseStep 72619199 = 108928799) B108928799
theorem B48412799 : Blo 2095435 48412799 := bstep (se 1 (by rfl) ⟨36309599, by rfl⟩ : syracuseStep 48412799 = 72619199) B72619199
theorem B32275199 : Blo 2095435 32275199 := bstep (se 1 (by rfl) ⟨24206399, by rfl⟩ : syracuseStep 32275199 = 48412799) B48412799
theorem B86067197 : Blo 2095435 86067197 := bstep (se 3 (by rfl) ⟨16137599, by rfl⟩ : syracuseStep 86067197 = 32275199) B32275199
theorem B57378131 : Blo 2095435 57378131 := bstep (se 1 (by rfl) ⟨43033598, by rfl⟩ : syracuseStep 57378131 = 86067197) B86067197
theorem B38252087 : Blo 2095435 38252087 := bstep (se 1 (by rfl) ⟨28689065, by rfl⟩ : syracuseStep 38252087 = 57378131) B57378131
theorem B25501391 : Blo 2095435 25501391 := bstep (se 1 (by rfl) ⟨19126043, by rfl⟩ : syracuseStep 25501391 = 38252087) B38252087
theorem B17000927 : Blo 2095435 17000927 := bstep (se 1 (by rfl) ⟨12750695, by rfl⟩ : syracuseStep 17000927 = 25501391) B25501391
theorem B11333951 : Blo 2095435 11333951 := bstep (se 1 (by rfl) ⟨8500463, by rfl⟩ : syracuseStep 11333951 = 17000927) B17000927
theorem B7555967 : Blo 2095435 7555967 := bstep (se 1 (by rfl) ⟨5666975, by rfl⟩ : syracuseStep 7555967 = 11333951) B11333951
theorem B5037311 : Blo 2095435 5037311 := bstep (se 1 (by rfl) ⟨3777983, by rfl⟩ : syracuseStep 5037311 = 7555967) B7555967
theorem B3358207 : Blo 2095435 3358207 := bstep (se 1 (by rfl) ⟨2518655, by rfl⟩ : syracuseStep 3358207 = 5037311) B5037311
theorem B4477609 : Blo 2095435 4477609 := bstep (se 2 (by rfl) ⟨1679103, by rfl⟩ : syracuseStep 4477609 = 3358207) B3358207
theorem B23880581 : Blo 2095435 23880581 := bstep (se 4 (by rfl) ⟨2238804, by rfl⟩ : syracuseStep 23880581 = 4477609) B4477609
theorem B15920387 : Blo 2095435 15920387 := bstep (se 1 (by rfl) ⟨11940290, by rfl⟩ : syracuseStep 15920387 = 23880581) B23880581
theorem B10613591 : Blo 2095435 10613591 := bstep (se 1 (by rfl) ⟨7960193, by rfl⟩ : syracuseStep 10613591 = 15920387) B15920387
theorem B7075727 : Blo 2095435 7075727 := bstep (se 1 (by rfl) ⟨5306795, by rfl⟩ : syracuseStep 7075727 = 10613591) B10613591
theorem B4717151 : Blo 2095435 4717151 := bstep (se 1 (by rfl) ⟨3537863, by rfl⟩ : syracuseStep 4717151 = 7075727) B7075727
theorem B3144767 : Blo 2095435 3144767 := bstep (se 1 (by rfl) ⟨2358575, by rfl⟩ : syracuseStep 3144767 = 4717151) B4717151
theorem B2096511 : Blo 2095435 2096511 := bstep (se 1 (by rfl) ⟨1572383, by rfl⟩ : syracuseStep 2096511 = 3144767) B3144767
theorem B3144773 : Blo 2095435 3144773 := bbase (se 4 (by rfl) ⟨294822, by rfl⟩ : syracuseStep 3144773 = 589645) (by norm_num)
theorem B2096515 : Blo 2095435 2096515 := bstep (se 1 (by rfl) ⟨1572386, by rfl⟩ : syracuseStep 2096515 = 3144773) B3144773
theorem B3537877 : Blo 2095435 3537877 := bbase (se 7 (by rfl) ⟨41459, by rfl⟩ : syracuseStep 3537877 = 82919) (by norm_num)
theorem B4717169 : Blo 2095435 4717169 := bstep (se 2 (by rfl) ⟨1768938, by rfl⟩ : syracuseStep 4717169 = 3537877) B3537877
theorem B3144779 : Blo 2095435 3144779 := bstep (se 1 (by rfl) ⟨2358584, by rfl⟩ : syracuseStep 3144779 = 4717169) B4717169
theorem B2096519 : Blo 2095435 2096519 := bstep (se 1 (by rfl) ⟨1572389, by rfl⟩ : syracuseStep 2096519 = 3144779) B3144779
theorem B2358589 : Blo 2095435 2358589 := bbase (se 3 (by rfl) ⟨442235, by rfl⟩ : syracuseStep 2358589 = 884471) (by norm_num)
theorem B3144785 : Blo 2095435 3144785 := bstep (se 2 (by rfl) ⟨1179294, by rfl⟩ : syracuseStep 3144785 = 2358589) B2358589
theorem B2096523 : Blo 2095435 2096523 := bstep (se 1 (by rfl) ⟨1572392, by rfl⟩ : syracuseStep 2096523 = 3144785) B3144785
theorem B7075781 : Blo 2095435 7075781 := bbase (se 4 (by rfl) ⟨663354, by rfl⟩ : syracuseStep 7075781 = 1326709) (by norm_num)
theorem B4717187 : Blo 2095435 4717187 := bstep (se 1 (by rfl) ⟨3537890, by rfl⟩ : syracuseStep 4717187 = 7075781) B7075781
theorem B3144791 : Blo 2095435 3144791 := bstep (se 1 (by rfl) ⟨2358593, by rfl⟩ : syracuseStep 3144791 = 4717187) B4717187
theorem B2096527 : Blo 2095435 2096527 := bstep (se 1 (by rfl) ⟨1572395, by rfl⟩ : syracuseStep 2096527 = 3144791) B3144791
theorem B3144797 : Blo 2095435 3144797 := bbase (se 3 (by rfl) ⟨589649, by rfl⟩ : syracuseStep 3144797 = 1179299) (by norm_num)
theorem B2096531 : Blo 2095435 2096531 := bstep (se 1 (by rfl) ⟨1572398, by rfl⟩ : syracuseStep 2096531 = 3144797) B3144797
theorem B4717205 : Blo 2095435 4717205 := bbase (se 6 (by rfl) ⟨110559, by rfl⟩ : syracuseStep 4717205 = 221119) (by norm_num)
theorem B3144803 : Blo 2095435 3144803 := bstep (se 1 (by rfl) ⟨2358602, by rfl⟩ : syracuseStep 3144803 = 4717205) B4717205
theorem B2096535 : Blo 2095435 2096535 := bstep (se 1 (by rfl) ⟨1572401, by rfl⟩ : syracuseStep 2096535 = 3144803) B3144803
theorem B3358253 : Blo 2095435 3358253 := bbase (se 3 (by rfl) ⟨629672, by rfl⟩ : syracuseStep 3358253 = 1259345) (by norm_num)
theorem B2238835 : Blo 2095435 2238835 := bstep (se 1 (by rfl) ⟨1679126, by rfl⟩ : syracuseStep 2238835 = 3358253) B3358253
theorem B2985113 : Blo 2095435 2985113 := bstep (se 2 (by rfl) ⟨1119417, by rfl⟩ : syracuseStep 2985113 = 2238835) B2238835
theorem B7960301 : Blo 2095435 7960301 := bstep (se 3 (by rfl) ⟨1492556, by rfl⟩ : syracuseStep 7960301 = 2985113) B2985113
theorem B5306867 : Blo 2095435 5306867 := bstep (se 1 (by rfl) ⟨3980150, by rfl⟩ : syracuseStep 5306867 = 7960301) B7960301
theorem B3537911 : Blo 2095435 3537911 := bstep (se 1 (by rfl) ⟨2653433, by rfl⟩ : syracuseStep 3537911 = 5306867) B5306867
theorem B2358607 : Blo 2095435 2358607 := bstep (se 1 (by rfl) ⟨1768955, by rfl⟩ : syracuseStep 2358607 = 3537911) B3537911
theorem B3144809 : Blo 2095435 3144809 := bstep (se 2 (by rfl) ⟨1179303, by rfl⟩ : syracuseStep 3144809 = 2358607) B2358607
theorem B2096539 : Blo 2095435 2096539 := bstep (se 1 (by rfl) ⟨1572404, by rfl⟩ : syracuseStep 2096539 = 3144809) B3144809
theorem B22668245 : Blo 2095435 22668245 := bbase (se 7 (by rfl) ⟨265643, by rfl⟩ : syracuseStep 22668245 = 531287) (by norm_num)
theorem B15112163 : Blo 2095435 15112163 := bstep (se 1 (by rfl) ⟨11334122, by rfl⟩ : syracuseStep 15112163 = 22668245) B22668245
theorem B10074775 : Blo 2095435 10074775 := bstep (se 1 (by rfl) ⟨7556081, by rfl⟩ : syracuseStep 10074775 = 15112163) B15112163
theorem B13433033 : Blo 2095435 13433033 := bstep (se 2 (by rfl) ⟨5037387, by rfl⟩ : syracuseStep 13433033 = 10074775) B10074775
theorem B8955355 : Blo 2095435 8955355 := bstep (se 1 (by rfl) ⟨6716516, by rfl⟩ : syracuseStep 8955355 = 13433033) B13433033
theorem B11940473 : Blo 2095435 11940473 := bstep (se 2 (by rfl) ⟨4477677, by rfl⟩ : syracuseStep 11940473 = 8955355) B8955355
theorem B7960315 : Blo 2095435 7960315 := bstep (se 1 (by rfl) ⟨5970236, by rfl⟩ : syracuseStep 7960315 = 11940473) B11940473
theorem B10613753 : Blo 2095435 10613753 := bstep (se 2 (by rfl) ⟨3980157, by rfl⟩ : syracuseStep 10613753 = 7960315) B7960315
theorem B7075835 : Blo 2095435 7075835 := bstep (se 1 (by rfl) ⟨5306876, by rfl⟩ : syracuseStep 7075835 = 10613753) B10613753
theorem B4717223 : Blo 2095435 4717223 := bstep (se 1 (by rfl) ⟨3537917, by rfl⟩ : syracuseStep 4717223 = 7075835) B7075835
theorem B3144815 : Blo 2095435 3144815 := bstep (se 1 (by rfl) ⟨2358611, by rfl⟩ : syracuseStep 3144815 = 4717223) B4717223
theorem B2096543 : Blo 2095435 2096543 := bstep (se 1 (by rfl) ⟨1572407, by rfl⟩ : syracuseStep 2096543 = 3144815) B3144815
theorem B3144821 : Blo 2095435 3144821 := bbase (se 5 (by rfl) ⟨147413, by rfl⟩ : syracuseStep 3144821 = 294827) (by norm_num)
theorem B2096547 : Blo 2095435 2096547 := bstep (se 1 (by rfl) ⟨1572410, by rfl⟩ : syracuseStep 2096547 = 3144821) B3144821
theorem B3980173 : Blo 2095435 3980173 := bbase (se 3 (by rfl) ⟨746282, by rfl⟩ : syracuseStep 3980173 = 1492565) (by norm_num)
theorem B5306897 : Blo 2095435 5306897 := bstep (se 2 (by rfl) ⟨1990086, by rfl⟩ : syracuseStep 5306897 = 3980173) B3980173
theorem B3537931 : Blo 2095435 3537931 := bstep (se 1 (by rfl) ⟨2653448, by rfl⟩ : syracuseStep 3537931 = 5306897) B5306897
theorem B4717241 : Blo 2095435 4717241 := bstep (se 2 (by rfl) ⟨1768965, by rfl⟩ : syracuseStep 4717241 = 3537931) B3537931
theorem B3144827 : Blo 2095435 3144827 := bstep (se 1 (by rfl) ⟨2358620, by rfl⟩ : syracuseStep 3144827 = 4717241) B4717241
theorem B2096551 : Blo 2095435 2096551 := bstep (se 1 (by rfl) ⟨1572413, by rfl⟩ : syracuseStep 2096551 = 3144827) B3144827
theorem B2358625 : Blo 2095435 2358625 := bbase (se 2 (by rfl) ⟨884484, by rfl⟩ : syracuseStep 2358625 = 1768969) (by norm_num)
theorem B3144833 : Blo 2095435 3144833 := bstep (se 2 (by rfl) ⟨1179312, by rfl⟩ : syracuseStep 3144833 = 2358625) B2358625
theorem B2096555 : Blo 2095435 2096555 := bstep (se 1 (by rfl) ⟨1572416, by rfl⟩ : syracuseStep 2096555 = 3144833) B3144833
theorem B5306917 : Blo 2095435 5306917 := bbase (se 4 (by rfl) ⟨497523, by rfl⟩ : syracuseStep 5306917 = 995047) (by norm_num)
theorem B7075889 : Blo 2095435 7075889 := bstep (se 2 (by rfl) ⟨2653458, by rfl⟩ : syracuseStep 7075889 = 5306917) B5306917
theorem B4717259 : Blo 2095435 4717259 := bstep (se 1 (by rfl) ⟨3537944, by rfl⟩ : syracuseStep 4717259 = 7075889) B7075889
theorem B3144839 : Blo 2095435 3144839 := bstep (se 1 (by rfl) ⟨2358629, by rfl⟩ : syracuseStep 3144839 = 4717259) B4717259
theorem B2096559 : Blo 2095435 2096559 := bstep (se 1 (by rfl) ⟨1572419, by rfl⟩ : syracuseStep 2096559 = 3144839) B3144839
theorem B3144845 : Blo 2095435 3144845 := bbase (se 3 (by rfl) ⟨589658, by rfl⟩ : syracuseStep 3144845 = 1179317) (by norm_num)
theorem B2096563 : Blo 2095435 2096563 := bstep (se 1 (by rfl) ⟨1572422, by rfl⟩ : syracuseStep 2096563 = 3144845) B3144845
theorem B4717277 : Blo 2095435 4717277 := bbase (se 3 (by rfl) ⟨884489, by rfl⟩ : syracuseStep 4717277 = 1768979) (by norm_num)
theorem B3144851 : Blo 2095435 3144851 := bstep (se 1 (by rfl) ⟨2358638, by rfl⟩ : syracuseStep 3144851 = 4717277) B4717277
theorem B2096567 : Blo 2095435 2096567 := bstep (se 1 (by rfl) ⟨1572425, by rfl⟩ : syracuseStep 2096567 = 3144851) B3144851
theorem B3537965 : Blo 2095435 3537965 := bbase (se 3 (by rfl) ⟨663368, by rfl⟩ : syracuseStep 3537965 = 1326737) (by norm_num)
theorem B2358643 : Blo 2095435 2358643 := bstep (se 1 (by rfl) ⟨1768982, by rfl⟩ : syracuseStep 2358643 = 3537965) B3537965
theorem B3144857 : Blo 2095435 3144857 := bstep (se 2 (by rfl) ⟨1179321, by rfl⟩ : syracuseStep 3144857 = 2358643) B2358643
theorem B2096571 : Blo 2095435 2096571 := bstep (se 1 (by rfl) ⟨1572428, by rfl⟩ : syracuseStep 2096571 = 3144857) B3144857
theorem B6375541 : Blo 2095435 6375541 := bbase (se 5 (by rfl) ⟨298853, by rfl⟩ : syracuseStep 6375541 = 597707) (by norm_num)
theorem B8500721 : Blo 2095435 8500721 := bstep (se 2 (by rfl) ⟨3187770, by rfl⟩ : syracuseStep 8500721 = 6375541) B6375541
theorem B22668589 : Blo 2095435 22668589 := bstep (se 3 (by rfl) ⟨4250360, by rfl⟩ : syracuseStep 22668589 = 8500721) B8500721
theorem B30224785 : Blo 2095435 30224785 := bstep (se 2 (by rfl) ⟨11334294, by rfl⟩ : syracuseStep 30224785 = 22668589) B22668589
theorem B40299713 : Blo 2095435 40299713 := bstep (se 2 (by rfl) ⟨15112392, by rfl⟩ : syracuseStep 40299713 = 30224785) B30224785
theorem B26866475 : Blo 2095435 26866475 := bstep (se 1 (by rfl) ⟨20149856, by rfl⟩ : syracuseStep 26866475 = 40299713) B40299713
theorem B17910983 : Blo 2095435 17910983 := bstep (se 1 (by rfl) ⟨13433237, by rfl⟩ : syracuseStep 17910983 = 26866475) B26866475
theorem B11940655 : Blo 2095435 11940655 := bstep (se 1 (by rfl) ⟨8955491, by rfl⟩ : syracuseStep 11940655 = 17910983) B17910983
theorem B15920873 : Blo 2095435 15920873 := bstep (se 2 (by rfl) ⟨5970327, by rfl⟩ : syracuseStep 15920873 = 11940655) B11940655
theorem B10613915 : Blo 2095435 10613915 := bstep (se 1 (by rfl) ⟨7960436, by rfl⟩ : syracuseStep 10613915 = 15920873) B15920873
theorem B7075943 : Blo 2095435 7075943 := bstep (se 1 (by rfl) ⟨5306957, by rfl⟩ : syracuseStep 7075943 = 10613915) B10613915
theorem B4717295 : Blo 2095435 4717295 := bstep (se 1 (by rfl) ⟨3537971, by rfl⟩ : syracuseStep 4717295 = 7075943) B7075943
theorem B3144863 : Blo 2095435 3144863 := bstep (se 1 (by rfl) ⟨2358647, by rfl⟩ : syracuseStep 3144863 = 4717295) B4717295
theorem B2096575 : Blo 2095435 2096575 := bstep (se 1 (by rfl) ⟨1572431, by rfl⟩ : syracuseStep 2096575 = 3144863) B3144863
theorem B3144869 : Blo 2095435 3144869 := bbase (se 4 (by rfl) ⟨294831, by rfl⟩ : syracuseStep 3144869 = 589663) (by norm_num)
theorem B2096579 : Blo 2095435 2096579 := bstep (se 1 (by rfl) ⟨1572434, by rfl⟩ : syracuseStep 2096579 = 3144869) B3144869
theorem B2653489 : Blo 2095435 2653489 := bbase (se 2 (by rfl) ⟨995058, by rfl⟩ : syracuseStep 2653489 = 1990117) (by norm_num)
theorem B3537985 : Blo 2095435 3537985 := bstep (se 2 (by rfl) ⟨1326744, by rfl⟩ : syracuseStep 3537985 = 2653489) B2653489
theorem B4717313 : Blo 2095435 4717313 := bstep (se 2 (by rfl) ⟨1768992, by rfl⟩ : syracuseStep 4717313 = 3537985) B3537985
theorem B3144875 : Blo 2095435 3144875 := bstep (se 1 (by rfl) ⟨2358656, by rfl⟩ : syracuseStep 3144875 = 4717313) B4717313
theorem B2096583 : Blo 2095435 2096583 := bstep (se 1 (by rfl) ⟨1572437, by rfl⟩ : syracuseStep 2096583 = 3144875) B3144875
theorem B2358661 : Blo 2095435 2358661 := bbase (se 4 (by rfl) ⟨221124, by rfl⟩ : syracuseStep 2358661 = 442249) (by norm_num)
theorem B3144881 : Blo 2095435 3144881 := bstep (se 2 (by rfl) ⟨1179330, by rfl⟩ : syracuseStep 3144881 = 2358661) B2358661
theorem B2096587 : Blo 2095435 2096587 := bstep (se 1 (by rfl) ⟨1572440, by rfl⟩ : syracuseStep 2096587 = 3144881) B3144881
theorem B4477781 : Blo 2095435 4477781 := bbase (se 9 (by rfl) ⟨13118, by rfl⟩ : syracuseStep 4477781 = 26237) (by norm_num)
theorem B2985187 : Blo 2095435 2985187 := bstep (se 1 (by rfl) ⟨2238890, by rfl⟩ : syracuseStep 2985187 = 4477781) B4477781
theorem B3980249 : Blo 2095435 3980249 := bstep (se 2 (by rfl) ⟨1492593, by rfl⟩ : syracuseStep 3980249 = 2985187) B2985187
theorem B2653499 : Blo 2095435 2653499 := bstep (se 1 (by rfl) ⟨1990124, by rfl⟩ : syracuseStep 2653499 = 3980249) B3980249
theorem B7075997 : Blo 2095435 7075997 := bstep (se 3 (by rfl) ⟨1326749, by rfl⟩ : syracuseStep 7075997 = 2653499) B2653499
theorem B4717331 : Blo 2095435 4717331 := bstep (se 1 (by rfl) ⟨3537998, by rfl⟩ : syracuseStep 4717331 = 7075997) B7075997
theorem B3144887 : Blo 2095435 3144887 := bstep (se 1 (by rfl) ⟨2358665, by rfl⟩ : syracuseStep 3144887 = 4717331) B4717331
theorem B2096591 : Blo 2095435 2096591 := bstep (se 1 (by rfl) ⟨1572443, by rfl⟩ : syracuseStep 2096591 = 3144887) B3144887
theorem B3144893 : Blo 2095435 3144893 := bbase (se 3 (by rfl) ⟨589667, by rfl⟩ : syracuseStep 3144893 = 1179335) (by norm_num)
theorem B2096595 : Blo 2095435 2096595 := bstep (se 1 (by rfl) ⟨1572446, by rfl⟩ : syracuseStep 2096595 = 3144893) B3144893
theorem B4717349 : Blo 2095435 4717349 := bbase (se 4 (by rfl) ⟨442251, by rfl⟩ : syracuseStep 4717349 = 884503) (by norm_num)
theorem B3144899 : Blo 2095435 3144899 := bstep (se 1 (by rfl) ⟨2358674, by rfl⟩ : syracuseStep 3144899 = 4717349) B4717349
theorem B2096599 : Blo 2095435 2096599 := bstep (se 1 (by rfl) ⟨1572449, by rfl⟩ : syracuseStep 2096599 = 3144899) B3144899
theorem B5307029 : Blo 2095435 5307029 := bbase (se 6 (by rfl) ⟨124383, by rfl⟩ : syracuseStep 5307029 = 248767) (by norm_num)
theorem B3538019 : Blo 2095435 3538019 := bstep (se 1 (by rfl) ⟨2653514, by rfl⟩ : syracuseStep 3538019 = 5307029) B5307029
theorem B2358679 : Blo 2095435 2358679 := bstep (se 1 (by rfl) ⟨1769009, by rfl⟩ : syracuseStep 2358679 = 3538019) B3538019
theorem B3144905 : Blo 2095435 3144905 := bstep (se 2 (by rfl) ⟨1179339, by rfl⟩ : syracuseStep 3144905 = 2358679) B2358679
theorem B2096603 : Blo 2095435 2096603 := bstep (se 1 (by rfl) ⟨1572452, by rfl⟩ : syracuseStep 2096603 = 3144905) B3144905
theorem B3778157 : Blo 2095435 3778157 := bbase (se 3 (by rfl) ⟨708404, by rfl⟩ : syracuseStep 3778157 = 1416809) (by norm_num)
theorem B2518771 : Blo 2095435 2518771 := bstep (se 1 (by rfl) ⟨1889078, by rfl⟩ : syracuseStep 2518771 = 3778157) B3778157
theorem B3358361 : Blo 2095435 3358361 := bstep (se 2 (by rfl) ⟨1259385, by rfl⟩ : syracuseStep 3358361 = 2518771) B2518771
theorem B8955629 : Blo 2095435 8955629 := bstep (se 3 (by rfl) ⟨1679180, by rfl⟩ : syracuseStep 8955629 = 3358361) B3358361
theorem B5970419 : Blo 2095435 5970419 := bstep (se 1 (by rfl) ⟨4477814, by rfl⟩ : syracuseStep 5970419 = 8955629) B8955629
theorem B3980279 : Blo 2095435 3980279 := bstep (se 1 (by rfl) ⟨2985209, by rfl⟩ : syracuseStep 3980279 = 5970419) B5970419
theorem B10614077 : Blo 2095435 10614077 := bstep (se 3 (by rfl) ⟨1990139, by rfl⟩ : syracuseStep 10614077 = 3980279) B3980279
theorem B7076051 : Blo 2095435 7076051 := bstep (se 1 (by rfl) ⟨5307038, by rfl⟩ : syracuseStep 7076051 = 10614077) B10614077
theorem B4717367 : Blo 2095435 4717367 := bstep (se 1 (by rfl) ⟨3538025, by rfl⟩ : syracuseStep 4717367 = 7076051) B7076051
theorem B3144911 : Blo 2095435 3144911 := bstep (se 1 (by rfl) ⟨2358683, by rfl⟩ : syracuseStep 3144911 = 4717367) B4717367
theorem B2096607 : Blo 2095435 2096607 := bstep (se 1 (by rfl) ⟨1572455, by rfl⟩ : syracuseStep 2096607 = 3144911) B3144911
theorem B3144917 : Blo 2095435 3144917 := bbase (se 7 (by rfl) ⟨36854, by rfl⟩ : syracuseStep 3144917 = 73709) (by norm_num)
theorem B2096611 : Blo 2095435 2096611 := bstep (se 1 (by rfl) ⟨1572458, by rfl⟩ : syracuseStep 2096611 = 3144917) B3144917
theorem B2985221 : Blo 2095435 2985221 := bbase (se 4 (by rfl) ⟨279864, by rfl⟩ : syracuseStep 2985221 = 559729) (by norm_num)
theorem B7960589 : Blo 2095435 7960589 := bstep (se 3 (by rfl) ⟨1492610, by rfl⟩ : syracuseStep 7960589 = 2985221) B2985221
theorem B5307059 : Blo 2095435 5307059 := bstep (se 1 (by rfl) ⟨3980294, by rfl⟩ : syracuseStep 5307059 = 7960589) B7960589
theorem B3538039 : Blo 2095435 3538039 := bstep (se 1 (by rfl) ⟨2653529, by rfl⟩ : syracuseStep 3538039 = 5307059) B5307059
theorem B4717385 : Blo 2095435 4717385 := bstep (se 2 (by rfl) ⟨1769019, by rfl⟩ : syracuseStep 4717385 = 3538039) B3538039
theorem B3144923 : Blo 2095435 3144923 := bstep (se 1 (by rfl) ⟨2358692, by rfl⟩ : syracuseStep 3144923 = 4717385) B4717385
theorem B2096615 : Blo 2095435 2096615 := bstep (se 1 (by rfl) ⟨1572461, by rfl⟩ : syracuseStep 2096615 = 3144923) B3144923
theorem B2358697 : Blo 2095435 2358697 := bbase (se 2 (by rfl) ⟨884511, by rfl⟩ : syracuseStep 2358697 = 1769023) (by norm_num)
theorem B3144929 : Blo 2095435 3144929 := bstep (se 2 (by rfl) ⟨1179348, by rfl⟩ : syracuseStep 3144929 = 2358697) B2358697
theorem B2096619 : Blo 2095435 2096619 := bstep (se 1 (by rfl) ⟨1572464, by rfl⟩ : syracuseStep 2096619 = 3144929) B3144929
theorem B6716773 : Blo 2095435 6716773 := bbase (se 4 (by rfl) ⟨629697, by rfl⟩ : syracuseStep 6716773 = 1259395) (by norm_num)
theorem B8955697 : Blo 2095435 8955697 := bstep (se 2 (by rfl) ⟨3358386, by rfl⟩ : syracuseStep 8955697 = 6716773) B6716773
theorem B11940929 : Blo 2095435 11940929 := bstep (se 2 (by rfl) ⟨4477848, by rfl⟩ : syracuseStep 11940929 = 8955697) B8955697
theorem B7960619 : Blo 2095435 7960619 := bstep (se 1 (by rfl) ⟨5970464, by rfl⟩ : syracuseStep 7960619 = 11940929) B11940929
theorem B5307079 : Blo 2095435 5307079 := bstep (se 1 (by rfl) ⟨3980309, by rfl⟩ : syracuseStep 5307079 = 7960619) B7960619
theorem B7076105 : Blo 2095435 7076105 := bstep (se 2 (by rfl) ⟨2653539, by rfl⟩ : syracuseStep 7076105 = 5307079) B5307079
theorem B4717403 : Blo 2095435 4717403 := bstep (se 1 (by rfl) ⟨3538052, by rfl⟩ : syracuseStep 4717403 = 7076105) B7076105
theorem B3144935 : Blo 2095435 3144935 := bstep (se 1 (by rfl) ⟨2358701, by rfl⟩ : syracuseStep 3144935 = 4717403) B4717403
theorem B2096623 : Blo 2095435 2096623 := bstep (se 1 (by rfl) ⟨1572467, by rfl⟩ : syracuseStep 2096623 = 3144935) B3144935
theorem B3144941 : Blo 2095435 3144941 := bbase (se 3 (by rfl) ⟨589676, by rfl⟩ : syracuseStep 3144941 = 1179353) (by norm_num)
theorem B2096627 : Blo 2095435 2096627 := bstep (se 1 (by rfl) ⟨1572470, by rfl⟩ : syracuseStep 2096627 = 3144941) B3144941
theorem B4717421 : Blo 2095435 4717421 := bbase (se 3 (by rfl) ⟨884516, by rfl⟩ : syracuseStep 4717421 = 1769033) (by norm_num)
theorem B3144947 : Blo 2095435 3144947 := bstep (se 1 (by rfl) ⟨2358710, by rfl⟩ : syracuseStep 3144947 = 4717421) B4717421
theorem B2096631 : Blo 2095435 2096631 := bstep (se 1 (by rfl) ⟨1572473, by rfl⟩ : syracuseStep 2096631 = 3144947) B3144947
theorem B3980333 : Blo 2095435 3980333 := bbase (se 3 (by rfl) ⟨746312, by rfl⟩ : syracuseStep 3980333 = 1492625) (by norm_num)
theorem B2653555 : Blo 2095435 2653555 := bstep (se 1 (by rfl) ⟨1990166, by rfl⟩ : syracuseStep 2653555 = 3980333) B3980333
theorem B3538073 : Blo 2095435 3538073 := bstep (se 2 (by rfl) ⟨1326777, by rfl⟩ : syracuseStep 3538073 = 2653555) B2653555
theorem B2358715 : Blo 2095435 2358715 := bstep (se 1 (by rfl) ⟨1769036, by rfl⟩ : syracuseStep 2358715 = 3538073) B3538073
theorem B3144953 : Blo 2095435 3144953 := bstep (se 2 (by rfl) ⟨1179357, by rfl⟩ : syracuseStep 3144953 = 2358715) B2358715
theorem B2096635 : Blo 2095435 2096635 := bstep (se 1 (by rfl) ⟨1572476, by rfl⟩ : syracuseStep 2096635 = 3144953) B3144953
theorem B5106349 : Blo 2095435 5106349 := bbase (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) (by norm_num)
theorem B6808465 : Blo 2095435 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B9077953 : Blo 2095435 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B12103937 : Blo 2095435 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B8069291 : Blo 2095435 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B5379527 : Blo 2095435 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B14345405 : Blo 2095435 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B9563603 : Blo 2095435 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B25502941 : Blo 2095435 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B34003921 : Blo 2095435 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B45338561 : Blo 2095435 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B30225707 : Blo 2095435 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B20150471 : Blo 2095435 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B53734589 : Blo 2095435 53734589 := bstep (se 3 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 53734589 = 20150471) B20150471
theorem B35823059 : Blo 2095435 35823059 := bstep (se 1 (by rfl) ⟨26867294, by rfl⟩ : syracuseStep 35823059 = 53734589) B53734589
theorem B23882039 : Blo 2095435 23882039 := bstep (se 1 (by rfl) ⟨17911529, by rfl⟩ : syracuseStep 23882039 = 35823059) B35823059
theorem B15921359 : Blo 2095435 15921359 := bstep (se 1 (by rfl) ⟨11941019, by rfl⟩ : syracuseStep 15921359 = 23882039) B23882039
theorem B10614239 : Blo 2095435 10614239 := bstep (se 1 (by rfl) ⟨7960679, by rfl⟩ : syracuseStep 10614239 = 15921359) B15921359
theorem B7076159 : Blo 2095435 7076159 := bstep (se 1 (by rfl) ⟨5307119, by rfl⟩ : syracuseStep 7076159 = 10614239) B10614239
theorem B4717439 : Blo 2095435 4717439 := bstep (se 1 (by rfl) ⟨3538079, by rfl⟩ : syracuseStep 4717439 = 7076159) B7076159
theorem B3144959 : Blo 2095435 3144959 := bstep (se 1 (by rfl) ⟨2358719, by rfl⟩ : syracuseStep 3144959 = 4717439) B4717439
theorem B2096639 : Blo 2095435 2096639 := bstep (se 1 (by rfl) ⟨1572479, by rfl⟩ : syracuseStep 2096639 = 3144959) B3144959
theorem B3144965 : Blo 2095435 3144965 := bbase (se 4 (by rfl) ⟨294840, by rfl⟩ : syracuseStep 3144965 = 589681) (by norm_num)
theorem B2096643 : Blo 2095435 2096643 := bstep (se 1 (by rfl) ⟨1572482, by rfl⟩ : syracuseStep 2096643 = 3144965) B3144965
theorem B3538093 : Blo 2095435 3538093 := bbase (se 3 (by rfl) ⟨663392, by rfl⟩ : syracuseStep 3538093 = 1326785) (by norm_num)
theorem B4717457 : Blo 2095435 4717457 := bstep (se 2 (by rfl) ⟨1769046, by rfl⟩ : syracuseStep 4717457 = 3538093) B3538093
theorem B3144971 : Blo 2095435 3144971 := bstep (se 1 (by rfl) ⟨2358728, by rfl⟩ : syracuseStep 3144971 = 4717457) B4717457
theorem B2096647 : Blo 2095435 2096647 := bstep (se 1 (by rfl) ⟨1572485, by rfl⟩ : syracuseStep 2096647 = 3144971) B3144971
theorem B2358733 : Blo 2095435 2358733 := bbase (se 3 (by rfl) ⟨442262, by rfl⟩ : syracuseStep 2358733 = 884525) (by norm_num)
theorem B3144977 : Blo 2095435 3144977 := bstep (se 2 (by rfl) ⟨1179366, by rfl⟩ : syracuseStep 3144977 = 2358733) B2358733
theorem B2096651 : Blo 2095435 2096651 := bstep (se 1 (by rfl) ⟨1572488, by rfl⟩ : syracuseStep 2096651 = 3144977) B3144977
theorem B7076213 : Blo 2095435 7076213 := bbase (se 5 (by rfl) ⟨331697, by rfl⟩ : syracuseStep 7076213 = 663395) (by norm_num)
theorem B4717475 : Blo 2095435 4717475 := bstep (se 1 (by rfl) ⟨3538106, by rfl⟩ : syracuseStep 4717475 = 7076213) B7076213
theorem B3144983 : Blo 2095435 3144983 := bstep (se 1 (by rfl) ⟨2358737, by rfl⟩ : syracuseStep 3144983 = 4717475) B4717475
theorem B2096655 : Blo 2095435 2096655 := bstep (se 1 (by rfl) ⟨1572491, by rfl⟩ : syracuseStep 2096655 = 3144983) B3144983
theorem B3144989 : Blo 2095435 3144989 := bbase (se 3 (by rfl) ⟨589685, by rfl⟩ : syracuseStep 3144989 = 1179371) (by norm_num)
theorem B2096659 : Blo 2095435 2096659 := bstep (se 1 (by rfl) ⟨1572494, by rfl⟩ : syracuseStep 2096659 = 3144989) B3144989
theorem B4717493 : Blo 2095435 4717493 := bbase (se 5 (by rfl) ⟨221132, by rfl⟩ : syracuseStep 4717493 = 442265) (by norm_num)
theorem B3144995 : Blo 2095435 3144995 := bstep (se 1 (by rfl) ⟨2358746, by rfl⟩ : syracuseStep 3144995 = 4717493) B4717493
theorem B2096663 : Blo 2095435 2096663 := bstep (se 1 (by rfl) ⟨1572497, by rfl⟩ : syracuseStep 2096663 = 3144995) B3144995
theorem B4250549 : Blo 2095435 4250549 := bbase (se 5 (by rfl) ⟨199244, by rfl⟩ : syracuseStep 4250549 = 398489) (by norm_num)
theorem B2833699 : Blo 2095435 2833699 := bstep (se 1 (by rfl) ⟨2125274, by rfl⟩ : syracuseStep 2833699 = 4250549) B4250549
theorem B3778265 : Blo 2095435 3778265 := bstep (se 2 (by rfl) ⟨1416849, by rfl⟩ : syracuseStep 3778265 = 2833699) B2833699
theorem B10075373 : Blo 2095435 10075373 := bstep (se 3 (by rfl) ⟨1889132, by rfl⟩ : syracuseStep 10075373 = 3778265) B3778265
theorem B6716915 : Blo 2095435 6716915 := bstep (se 1 (by rfl) ⟨5037686, by rfl⟩ : syracuseStep 6716915 = 10075373) B10075373
theorem B4477943 : Blo 2095435 4477943 := bstep (se 1 (by rfl) ⟨3358457, by rfl⟩ : syracuseStep 4477943 = 6716915) B6716915
theorem B11941181 : Blo 2095435 11941181 := bstep (se 3 (by rfl) ⟨2238971, by rfl⟩ : syracuseStep 11941181 = 4477943) B4477943
theorem B7960787 : Blo 2095435 7960787 := bstep (se 1 (by rfl) ⟨5970590, by rfl⟩ : syracuseStep 7960787 = 11941181) B11941181
theorem B5307191 : Blo 2095435 5307191 := bstep (se 1 (by rfl) ⟨3980393, by rfl⟩ : syracuseStep 5307191 = 7960787) B7960787
theorem B3538127 : Blo 2095435 3538127 := bstep (se 1 (by rfl) ⟨2653595, by rfl⟩ : syracuseStep 3538127 = 5307191) B5307191
theorem B2358751 : Blo 2095435 2358751 := bstep (se 1 (by rfl) ⟨1769063, by rfl⟩ : syracuseStep 2358751 = 3538127) B3538127
theorem B3145001 : Blo 2095435 3145001 := bstep (se 2 (by rfl) ⟨1179375, by rfl⟩ : syracuseStep 3145001 = 2358751) B2358751
theorem B2096667 : Blo 2095435 2096667 := bstep (se 1 (by rfl) ⟨1572500, by rfl⟩ : syracuseStep 2096667 = 3145001) B3145001
theorem B6995621 : Blo 2095435 6995621 := bbase (se 4 (by rfl) ⟨655839, by rfl⟩ : syracuseStep 6995621 = 1311679) (by norm_num)
theorem B4663747 : Blo 2095435 4663747 := bstep (se 1 (by rfl) ⟨3497810, by rfl⟩ : syracuseStep 4663747 = 6995621) B6995621
theorem B24873317 : Blo 2095435 24873317 := bstep (se 4 (by rfl) ⟨2331873, by rfl⟩ : syracuseStep 24873317 = 4663747) B4663747
theorem B16582211 : Blo 2095435 16582211 := bstep (se 1 (by rfl) ⟨12436658, by rfl⟩ : syracuseStep 16582211 = 24873317) B24873317
theorem B11054807 : Blo 2095435 11054807 := bstep (se 1 (by rfl) ⟨8291105, by rfl⟩ : syracuseStep 11054807 = 16582211) B16582211
theorem B7369871 : Blo 2095435 7369871 := bstep (se 1 (by rfl) ⟨5527403, by rfl⟩ : syracuseStep 7369871 = 11054807) B11054807
theorem B78611957 : Blo 2095435 78611957 := bstep (se 5 (by rfl) ⟨3684935, by rfl⟩ : syracuseStep 78611957 = 7369871) B7369871
theorem B52407971 : Blo 2095435 52407971 := bstep (se 1 (by rfl) ⟨39305978, by rfl⟩ : syracuseStep 52407971 = 78611957) B78611957
theorem B34938647 : Blo 2095435 34938647 := bstep (se 1 (by rfl) ⟨26203985, by rfl⟩ : syracuseStep 34938647 = 52407971) B52407971
theorem B23292431 : Blo 2095435 23292431 := bstep (se 1 (by rfl) ⟨17469323, by rfl⟩ : syracuseStep 23292431 = 34938647) B34938647
theorem B15528287 : Blo 2095435 15528287 := bstep (se 1 (by rfl) ⟨11646215, by rfl⟩ : syracuseStep 15528287 = 23292431) B23292431
theorem B41408765 : Blo 2095435 41408765 := bstep (se 3 (by rfl) ⟨7764143, by rfl⟩ : syracuseStep 41408765 = 15528287) B15528287
theorem B27605843 : Blo 2095435 27605843 := bstep (se 1 (by rfl) ⟨20704382, by rfl⟩ : syracuseStep 27605843 = 41408765) B41408765
theorem B18403895 : Blo 2095435 18403895 := bstep (se 1 (by rfl) ⟨13802921, by rfl⟩ : syracuseStep 18403895 = 27605843) B27605843
theorem B12269263 : Blo 2095435 12269263 := bstep (se 1 (by rfl) ⟨9201947, by rfl⟩ : syracuseStep 12269263 = 18403895) B18403895
theorem B16359017 : Blo 2095435 16359017 := bstep (se 2 (by rfl) ⟨6134631, by rfl⟩ : syracuseStep 16359017 = 12269263) B12269263
theorem B43624045 : Blo 2095435 43624045 := bstep (se 3 (by rfl) ⟨8179508, by rfl⟩ : syracuseStep 43624045 = 16359017) B16359017
theorem B58165393 : Blo 2095435 58165393 := bstep (se 2 (by rfl) ⟨21812022, by rfl⟩ : syracuseStep 58165393 = 43624045) B43624045
theorem B77553857 : Blo 2095435 77553857 := bstep (se 2 (by rfl) ⟨29082696, by rfl⟩ : syracuseStep 77553857 = 58165393) B58165393
theorem B51702571 : Blo 2095435 51702571 := bstep (se 1 (by rfl) ⟨38776928, by rfl⟩ : syracuseStep 51702571 = 77553857) B77553857
theorem B68936761 : Blo 2095435 68936761 := bstep (se 2 (by rfl) ⟨25851285, by rfl⟩ : syracuseStep 68936761 = 51702571) B51702571
theorem B91915681 : Blo 2095435 91915681 := bstep (se 2 (by rfl) ⟨34468380, by rfl⟩ : syracuseStep 91915681 = 68936761) B68936761
theorem B122554241 : Blo 2095435 122554241 := bstep (se 2 (by rfl) ⟨45957840, by rfl⟩ : syracuseStep 122554241 = 91915681) B91915681
theorem B81702827 : Blo 2095435 81702827 := bstep (se 1 (by rfl) ⟨61277120, by rfl⟩ : syracuseStep 81702827 = 122554241) B122554241
theorem B54468551 : Blo 2095435 54468551 := bstep (se 1 (by rfl) ⟨40851413, by rfl⟩ : syracuseStep 54468551 = 81702827) B81702827
theorem B145249469 : Blo 2095435 145249469 := bstep (se 3 (by rfl) ⟨27234275, by rfl⟩ : syracuseStep 145249469 = 54468551) B54468551
theorem B96832979 : Blo 2095435 96832979 := bstep (se 1 (by rfl) ⟨72624734, by rfl⟩ : syracuseStep 96832979 = 145249469) B145249469
theorem B64555319 : Blo 2095435 64555319 := bstep (se 1 (by rfl) ⟨48416489, by rfl⟩ : syracuseStep 64555319 = 96832979) B96832979
theorem B172147517 : Blo 2095435 172147517 := bstep (se 3 (by rfl) ⟨32277659, by rfl⟩ : syracuseStep 172147517 = 64555319) B64555319
theorem B114765011 : Blo 2095435 114765011 := bstep (se 1 (by rfl) ⟨86073758, by rfl⟩ : syracuseStep 114765011 = 172147517) B172147517
theorem B76510007 : Blo 2095435 76510007 := bstep (se 1 (by rfl) ⟨57382505, by rfl⟩ : syracuseStep 76510007 = 114765011) B114765011
theorem B51006671 : Blo 2095435 51006671 := bstep (se 1 (by rfl) ⟨38255003, by rfl⟩ : syracuseStep 51006671 = 76510007) B76510007
theorem B34004447 : Blo 2095435 34004447 := bstep (se 1 (by rfl) ⟨25503335, by rfl⟩ : syracuseStep 34004447 = 51006671) B51006671
theorem B22669631 : Blo 2095435 22669631 := bstep (se 1 (by rfl) ⟨17002223, by rfl⟩ : syracuseStep 22669631 = 34004447) B34004447
theorem B15113087 : Blo 2095435 15113087 := bstep (se 1 (by rfl) ⟨11334815, by rfl⟩ : syracuseStep 15113087 = 22669631) B22669631
theorem B10075391 : Blo 2095435 10075391 := bstep (se 1 (by rfl) ⟨7556543, by rfl⟩ : syracuseStep 10075391 = 15113087) B15113087
theorem B6716927 : Blo 2095435 6716927 := bstep (se 1 (by rfl) ⟨5037695, by rfl⟩ : syracuseStep 6716927 = 10075391) B10075391
theorem B4477951 : Blo 2095435 4477951 := bstep (se 1 (by rfl) ⟨3358463, by rfl⟩ : syracuseStep 4477951 = 6716927) B6716927
theorem B5970601 : Blo 2095435 5970601 := bstep (se 2 (by rfl) ⟨2238975, by rfl⟩ : syracuseStep 5970601 = 4477951) B4477951
theorem B7960801 : Blo 2095435 7960801 := bstep (se 2 (by rfl) ⟨2985300, by rfl⟩ : syracuseStep 7960801 = 5970601) B5970601
theorem B10614401 : Blo 2095435 10614401 := bstep (se 2 (by rfl) ⟨3980400, by rfl⟩ : syracuseStep 10614401 = 7960801) B7960801
theorem B7076267 : Blo 2095435 7076267 := bstep (se 1 (by rfl) ⟨5307200, by rfl⟩ : syracuseStep 7076267 = 10614401) B10614401
theorem B4717511 : Blo 2095435 4717511 := bstep (se 1 (by rfl) ⟨3538133, by rfl⟩ : syracuseStep 4717511 = 7076267) B7076267
theorem B3145007 : Blo 2095435 3145007 := bstep (se 1 (by rfl) ⟨2358755, by rfl⟩ : syracuseStep 3145007 = 4717511) B4717511
theorem B2096671 : Blo 2095435 2096671 := bstep (se 1 (by rfl) ⟨1572503, by rfl⟩ : syracuseStep 2096671 = 3145007) B3145007
theorem B3145013 : Blo 2095435 3145013 := bbase (se 5 (by rfl) ⟨147422, by rfl⟩ : syracuseStep 3145013 = 294845) (by norm_num)
theorem B2096675 : Blo 2095435 2096675 := bstep (se 1 (by rfl) ⟨1572506, by rfl⟩ : syracuseStep 2096675 = 3145013) B3145013
theorem B5307221 : Blo 2095435 5307221 := bbase (se 9 (by rfl) ⟨15548, by rfl⟩ : syracuseStep 5307221 = 31097) (by norm_num)
theorem B3538147 : Blo 2095435 3538147 := bstep (se 1 (by rfl) ⟨2653610, by rfl⟩ : syracuseStep 3538147 = 5307221) B5307221
theorem B4717529 : Blo 2095435 4717529 := bstep (se 2 (by rfl) ⟨1769073, by rfl⟩ : syracuseStep 4717529 = 3538147) B3538147
theorem B3145019 : Blo 2095435 3145019 := bstep (se 1 (by rfl) ⟨2358764, by rfl⟩ : syracuseStep 3145019 = 4717529) B4717529
theorem B2096679 : Blo 2095435 2096679 := bstep (se 1 (by rfl) ⟨1572509, by rfl⟩ : syracuseStep 2096679 = 3145019) B3145019
theorem B2358769 : Blo 2095435 2358769 := bbase (se 2 (by rfl) ⟨884538, by rfl⟩ : syracuseStep 2358769 = 1769077) (by norm_num)
theorem B3145025 : Blo 2095435 3145025 := bstep (se 2 (by rfl) ⟨1179384, by rfl⟩ : syracuseStep 3145025 = 2358769) B2358769
theorem B2096683 : Blo 2095435 2096683 := bstep (se 1 (by rfl) ⟨1572512, by rfl⟩ : syracuseStep 2096683 = 3145025) B3145025
theorem B3778301 : Blo 2095435 3778301 := bbase (se 3 (by rfl) ⟨708431, by rfl⟩ : syracuseStep 3778301 = 1416863) (by norm_num)
theorem B2518867 : Blo 2095435 2518867 := bstep (se 1 (by rfl) ⟨1889150, by rfl⟩ : syracuseStep 2518867 = 3778301) B3778301
theorem B13433957 : Blo 2095435 13433957 := bstep (se 4 (by rfl) ⟨1259433, by rfl⟩ : syracuseStep 13433957 = 2518867) B2518867
theorem B8955971 : Blo 2095435 8955971 := bstep (se 1 (by rfl) ⟨6716978, by rfl⟩ : syracuseStep 8955971 = 13433957) B13433957
theorem B5970647 : Blo 2095435 5970647 := bstep (se 1 (by rfl) ⟨4477985, by rfl⟩ : syracuseStep 5970647 = 8955971) B8955971
theorem B3980431 : Blo 2095435 3980431 := bstep (se 1 (by rfl) ⟨2985323, by rfl⟩ : syracuseStep 3980431 = 5970647) B5970647
theorem B5307241 : Blo 2095435 5307241 := bstep (se 2 (by rfl) ⟨1990215, by rfl⟩ : syracuseStep 5307241 = 3980431) B3980431
theorem B7076321 : Blo 2095435 7076321 := bstep (se 2 (by rfl) ⟨2653620, by rfl⟩ : syracuseStep 7076321 = 5307241) B5307241
theorem B4717547 : Blo 2095435 4717547 := bstep (se 1 (by rfl) ⟨3538160, by rfl⟩ : syracuseStep 4717547 = 7076321) B7076321
theorem B3145031 : Blo 2095435 3145031 := bstep (se 1 (by rfl) ⟨2358773, by rfl⟩ : syracuseStep 3145031 = 4717547) B4717547
theorem B2096687 : Blo 2095435 2096687 := bstep (se 1 (by rfl) ⟨1572515, by rfl⟩ : syracuseStep 2096687 = 3145031) B3145031
theorem B3145037 : Blo 2095435 3145037 := bbase (se 3 (by rfl) ⟨589694, by rfl⟩ : syracuseStep 3145037 = 1179389) (by norm_num)
theorem B2096691 : Blo 2095435 2096691 := bstep (se 1 (by rfl) ⟨1572518, by rfl⟩ : syracuseStep 2096691 = 3145037) B3145037
theorem B4717565 : Blo 2095435 4717565 := bbase (se 3 (by rfl) ⟨884543, by rfl⟩ : syracuseStep 4717565 = 1769087) (by norm_num)
theorem B3145043 : Blo 2095435 3145043 := bstep (se 1 (by rfl) ⟨2358782, by rfl⟩ : syracuseStep 3145043 = 4717565) B4717565
theorem B2096695 : Blo 2095435 2096695 := bstep (se 1 (by rfl) ⟨1572521, by rfl⟩ : syracuseStep 2096695 = 3145043) B3145043
theorem B3538181 : Blo 2095435 3538181 := bbase (se 4 (by rfl) ⟨331704, by rfl⟩ : syracuseStep 3538181 = 663409) (by norm_num)
theorem B2358787 : Blo 2095435 2358787 := bstep (se 1 (by rfl) ⟨1769090, by rfl⟩ : syracuseStep 2358787 = 3538181) B3538181
theorem B3145049 : Blo 2095435 3145049 := bstep (se 2 (by rfl) ⟨1179393, by rfl⟩ : syracuseStep 3145049 = 2358787) B2358787
theorem B2096699 : Blo 2095435 2096699 := bstep (se 1 (by rfl) ⟨1572524, by rfl⟩ : syracuseStep 2096699 = 3145049) B3145049
theorem B15921845 : Blo 2095435 15921845 := bbase (se 5 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 15921845 = 1492673) (by norm_num)
theorem B10614563 : Blo 2095435 10614563 := bstep (se 1 (by rfl) ⟨7960922, by rfl⟩ : syracuseStep 10614563 = 15921845) B15921845
theorem B7076375 : Blo 2095435 7076375 := bstep (se 1 (by rfl) ⟨5307281, by rfl⟩ : syracuseStep 7076375 = 10614563) B10614563
theorem B4717583 : Blo 2095435 4717583 := bstep (se 1 (by rfl) ⟨3538187, by rfl⟩ : syracuseStep 4717583 = 7076375) B7076375
theorem B3145055 : Blo 2095435 3145055 := bstep (se 1 (by rfl) ⟨2358791, by rfl⟩ : syracuseStep 3145055 = 4717583) B4717583
theorem B2096703 : Blo 2095435 2096703 := bstep (se 1 (by rfl) ⟨1572527, by rfl⟩ : syracuseStep 2096703 = 3145055) B3145055
theorem B3145061 : Blo 2095435 3145061 := bbase (se 4 (by rfl) ⟨294849, by rfl⟩ : syracuseStep 3145061 = 589699) (by norm_num)
theorem B2096707 : Blo 2095435 2096707 := bstep (se 1 (by rfl) ⟨1572530, by rfl⟩ : syracuseStep 2096707 = 3145061) B3145061
theorem B3980477 : Blo 2095435 3980477 := bbase (se 3 (by rfl) ⟨746339, by rfl⟩ : syracuseStep 3980477 = 1492679) (by norm_num)
theorem B2653651 : Blo 2095435 2653651 := bstep (se 1 (by rfl) ⟨1990238, by rfl⟩ : syracuseStep 2653651 = 3980477) B3980477
theorem B3538201 : Blo 2095435 3538201 := bstep (se 2 (by rfl) ⟨1326825, by rfl⟩ : syracuseStep 3538201 = 2653651) B2653651
theorem B4717601 : Blo 2095435 4717601 := bstep (se 2 (by rfl) ⟨1769100, by rfl⟩ : syracuseStep 4717601 = 3538201) B3538201
theorem B3145067 : Blo 2095435 3145067 := bstep (se 1 (by rfl) ⟨2358800, by rfl⟩ : syracuseStep 3145067 = 4717601) B4717601
theorem B2096711 : Blo 2095435 2096711 := bstep (se 1 (by rfl) ⟨1572533, by rfl⟩ : syracuseStep 2096711 = 3145067) B3145067
theorem B2358805 : Blo 2095435 2358805 := bbase (se 6 (by rfl) ⟨55284, by rfl⟩ : syracuseStep 2358805 = 110569) (by norm_num)
theorem B3145073 : Blo 2095435 3145073 := bstep (se 2 (by rfl) ⟨1179402, by rfl⟩ : syracuseStep 3145073 = 2358805) B2358805
theorem B2096715 : Blo 2095435 2096715 := bstep (se 1 (by rfl) ⟨1572536, by rfl⟩ : syracuseStep 2096715 = 3145073) B3145073
theorem B2653661 : Blo 2095435 2653661 := bbase (se 3 (by rfl) ⟨497561, by rfl⟩ : syracuseStep 2653661 = 995123) (by norm_num)
theorem B7076429 : Blo 2095435 7076429 := bstep (se 3 (by rfl) ⟨1326830, by rfl⟩ : syracuseStep 7076429 = 2653661) B2653661
theorem B4717619 : Blo 2095435 4717619 := bstep (se 1 (by rfl) ⟨3538214, by rfl⟩ : syracuseStep 4717619 = 7076429) B7076429
theorem B3145079 : Blo 2095435 3145079 := bstep (se 1 (by rfl) ⟨2358809, by rfl⟩ : syracuseStep 3145079 = 4717619) B4717619
theorem B2096719 : Blo 2095435 2096719 := bstep (se 1 (by rfl) ⟨1572539, by rfl⟩ : syracuseStep 2096719 = 3145079) B3145079
theorem B3145085 : Blo 2095435 3145085 := bbase (se 3 (by rfl) ⟨589703, by rfl⟩ : syracuseStep 3145085 = 1179407) (by norm_num)
theorem B2096723 : Blo 2095435 2096723 := bstep (se 1 (by rfl) ⟨1572542, by rfl⟩ : syracuseStep 2096723 = 3145085) B3145085
theorem B4717637 : Blo 2095435 4717637 := bbase (se 4 (by rfl) ⟨442278, by rfl⟩ : syracuseStep 4717637 = 884557) (by norm_num)
theorem B3145091 : Blo 2095435 3145091 := bstep (se 1 (by rfl) ⟨2358818, by rfl⟩ : syracuseStep 3145091 = 4717637) B4717637
theorem B2096727 : Blo 2095435 2096727 := bstep (se 1 (by rfl) ⟨1572545, by rfl⟩ : syracuseStep 2096727 = 3145091) B3145091
theorem B5970773 : Blo 2095435 5970773 := bbase (se 9 (by rfl) ⟨17492, by rfl⟩ : syracuseStep 5970773 = 34985) (by norm_num)
theorem B3980515 : Blo 2095435 3980515 := bstep (se 1 (by rfl) ⟨2985386, by rfl⟩ : syracuseStep 3980515 = 5970773) B5970773
theorem B5307353 : Blo 2095435 5307353 := bstep (se 2 (by rfl) ⟨1990257, by rfl⟩ : syracuseStep 5307353 = 3980515) B3980515
theorem B3538235 : Blo 2095435 3538235 := bstep (se 1 (by rfl) ⟨2653676, by rfl⟩ : syracuseStep 3538235 = 5307353) B5307353
theorem B2358823 : Blo 2095435 2358823 := bstep (se 1 (by rfl) ⟨1769117, by rfl⟩ : syracuseStep 2358823 = 3538235) B3538235
theorem B3145097 : Blo 2095435 3145097 := bstep (se 2 (by rfl) ⟨1179411, by rfl⟩ : syracuseStep 3145097 = 2358823) B2358823
theorem B2096731 : Blo 2095435 2096731 := bstep (se 1 (by rfl) ⟨1572548, by rfl⟩ : syracuseStep 2096731 = 3145097) B3145097
theorem B10614725 : Blo 2095435 10614725 := bbase (se 4 (by rfl) ⟨995130, by rfl⟩ : syracuseStep 10614725 = 1990261) (by norm_num)
theorem B7076483 : Blo 2095435 7076483 := bstep (se 1 (by rfl) ⟨5307362, by rfl⟩ : syracuseStep 7076483 = 10614725) B10614725
theorem B4717655 : Blo 2095435 4717655 := bstep (se 1 (by rfl) ⟨3538241, by rfl⟩ : syracuseStep 4717655 = 7076483) B7076483
theorem B3145103 : Blo 2095435 3145103 := bstep (se 1 (by rfl) ⟨2358827, by rfl⟩ : syracuseStep 3145103 = 4717655) B4717655
theorem B2096735 : Blo 2095435 2096735 := bstep (se 1 (by rfl) ⟨1572551, by rfl⟩ : syracuseStep 2096735 = 3145103) B3145103
theorem B3145109 : Blo 2095435 3145109 := bbase (se 6 (by rfl) ⟨73713, by rfl⟩ : syracuseStep 3145109 = 147427) (by norm_num)
theorem B2096739 : Blo 2095435 2096739 := bstep (se 1 (by rfl) ⟨1572554, by rfl⟩ : syracuseStep 2096739 = 3145109) B3145109
theorem B5037869 : Blo 2095435 5037869 := bbase (se 3 (by rfl) ⟨944600, by rfl⟩ : syracuseStep 5037869 = 1889201) (by norm_num)
theorem B3358579 : Blo 2095435 3358579 := bstep (se 1 (by rfl) ⟨2518934, by rfl⟩ : syracuseStep 3358579 = 5037869) B5037869
theorem B4478105 : Blo 2095435 4478105 := bstep (se 2 (by rfl) ⟨1679289, by rfl⟩ : syracuseStep 4478105 = 3358579) B3358579
theorem B11941613 : Blo 2095435 11941613 := bstep (se 3 (by rfl) ⟨2239052, by rfl⟩ : syracuseStep 11941613 = 4478105) B4478105
theorem B7961075 : Blo 2095435 7961075 := bstep (se 1 (by rfl) ⟨5970806, by rfl⟩ : syracuseStep 7961075 = 11941613) B11941613
theorem B5307383 : Blo 2095435 5307383 := bstep (se 1 (by rfl) ⟨3980537, by rfl⟩ : syracuseStep 5307383 = 7961075) B7961075
theorem B3538255 : Blo 2095435 3538255 := bstep (se 1 (by rfl) ⟨2653691, by rfl⟩ : syracuseStep 3538255 = 5307383) B5307383
theorem B4717673 : Blo 2095435 4717673 := bstep (se 2 (by rfl) ⟨1769127, by rfl⟩ : syracuseStep 4717673 = 3538255) B3538255
theorem B3145115 : Blo 2095435 3145115 := bstep (se 1 (by rfl) ⟨2358836, by rfl⟩ : syracuseStep 3145115 = 4717673) B4717673
theorem B2096743 : Blo 2095435 2096743 := bstep (se 1 (by rfl) ⟨1572557, by rfl⟩ : syracuseStep 2096743 = 3145115) B3145115
theorem B2358841 : Blo 2095435 2358841 := bbase (se 2 (by rfl) ⟨884565, by rfl⟩ : syracuseStep 2358841 = 1769131) (by norm_num)
theorem B3145121 : Blo 2095435 3145121 := bstep (se 2 (by rfl) ⟨1179420, by rfl⟩ : syracuseStep 3145121 = 2358841) B2358841
theorem B2096747 : Blo 2095435 2096747 := bstep (se 1 (by rfl) ⟨1572560, by rfl⟩ : syracuseStep 2096747 = 3145121) B3145121
theorem B2239061 : Blo 2095435 2239061 := bbase (se 8 (by rfl) ⟨13119, by rfl⟩ : syracuseStep 2239061 = 26239) (by norm_num)
theorem B5970829 : Blo 2095435 5970829 := bstep (se 3 (by rfl) ⟨1119530, by rfl⟩ : syracuseStep 5970829 = 2239061) B2239061
theorem B7961105 : Blo 2095435 7961105 := bstep (se 2 (by rfl) ⟨2985414, by rfl⟩ : syracuseStep 7961105 = 5970829) B5970829
theorem B5307403 : Blo 2095435 5307403 := bstep (se 1 (by rfl) ⟨3980552, by rfl⟩ : syracuseStep 5307403 = 7961105) B7961105
theorem B7076537 : Blo 2095435 7076537 := bstep (se 2 (by rfl) ⟨2653701, by rfl⟩ : syracuseStep 7076537 = 5307403) B5307403
theorem B4717691 : Blo 2095435 4717691 := bstep (se 1 (by rfl) ⟨3538268, by rfl⟩ : syracuseStep 4717691 = 7076537) B7076537
theorem B3145127 : Blo 2095435 3145127 := bstep (se 1 (by rfl) ⟨2358845, by rfl⟩ : syracuseStep 3145127 = 4717691) B4717691
theorem B2096751 : Blo 2095435 2096751 := bstep (se 1 (by rfl) ⟨1572563, by rfl⟩ : syracuseStep 2096751 = 3145127) B3145127
theorem B3145133 : Blo 2095435 3145133 := bbase (se 3 (by rfl) ⟨589712, by rfl⟩ : syracuseStep 3145133 = 1179425) (by norm_num)
theorem B2096755 : Blo 2095435 2096755 := bstep (se 1 (by rfl) ⟨1572566, by rfl⟩ : syracuseStep 2096755 = 3145133) B3145133
theorem B4717709 : Blo 2095435 4717709 := bbase (se 3 (by rfl) ⟨884570, by rfl⟩ : syracuseStep 4717709 = 1769141) (by norm_num)
theorem B3145139 : Blo 2095435 3145139 := bstep (se 1 (by rfl) ⟨2358854, by rfl⟩ : syracuseStep 3145139 = 4717709) B4717709
theorem B2096759 : Blo 2095435 2096759 := bstep (se 1 (by rfl) ⟨1572569, by rfl⟩ : syracuseStep 2096759 = 3145139) B3145139
theorem B2653717 : Blo 2095435 2653717 := bbase (se 6 (by rfl) ⟨62196, by rfl⟩ : syracuseStep 2653717 = 124393) (by norm_num)
theorem B3538289 : Blo 2095435 3538289 := bstep (se 2 (by rfl) ⟨1326858, by rfl⟩ : syracuseStep 3538289 = 2653717) B2653717
theorem B2358859 : Blo 2095435 2358859 := bstep (se 1 (by rfl) ⟨1769144, by rfl⟩ : syracuseStep 2358859 = 3538289) B3538289
theorem B3145145 : Blo 2095435 3145145 := bstep (se 2 (by rfl) ⟨1179429, by rfl⟩ : syracuseStep 3145145 = 2358859) B2358859
theorem B2096763 : Blo 2095435 2096763 := bstep (se 1 (by rfl) ⟨1572572, by rfl⟩ : syracuseStep 2096763 = 3145145) B3145145
theorem B2423669 : Blo 2095435 2423669 := bbase (se 5 (by rfl) ⟨113609, by rfl⟩ : syracuseStep 2423669 = 227219) (by norm_num)
theorem B6463117 : Blo 2095435 6463117 := bstep (se 3 (by rfl) ⟨1211834, by rfl⟩ : syracuseStep 6463117 = 2423669) B2423669
theorem B34469957 : Blo 2095435 34469957 := bstep (se 4 (by rfl) ⟨3231558, by rfl⟩ : syracuseStep 34469957 = 6463117) B6463117
theorem B22979971 : Blo 2095435 22979971 := bstep (se 1 (by rfl) ⟨17234978, by rfl⟩ : syracuseStep 22979971 = 34469957) B34469957
theorem B30639961 : Blo 2095435 30639961 := bstep (se 2 (by rfl) ⟨11489985, by rfl⟩ : syracuseStep 30639961 = 22979971) B22979971
theorem B40853281 : Blo 2095435 40853281 := bstep (se 2 (by rfl) ⟨15319980, by rfl⟩ : syracuseStep 40853281 = 30639961) B30639961
theorem B54471041 : Blo 2095435 54471041 := bstep (se 2 (by rfl) ⟨20426640, by rfl⟩ : syracuseStep 54471041 = 40853281) B40853281
theorem B36314027 : Blo 2095435 36314027 := bstep (se 1 (by rfl) ⟨27235520, by rfl⟩ : syracuseStep 36314027 = 54471041) B54471041
theorem B24209351 : Blo 2095435 24209351 := bstep (se 1 (by rfl) ⟨18157013, by rfl⟩ : syracuseStep 24209351 = 36314027) B36314027
theorem B16139567 : Blo 2095435 16139567 := bstep (se 1 (by rfl) ⟨12104675, by rfl⟩ : syracuseStep 16139567 = 24209351) B24209351
theorem B10759711 : Blo 2095435 10759711 := bstep (se 1 (by rfl) ⟨8069783, by rfl⟩ : syracuseStep 10759711 = 16139567) B16139567
theorem B14346281 : Blo 2095435 14346281 := bstep (se 2 (by rfl) ⟨5379855, by rfl⟩ : syracuseStep 14346281 = 10759711) B10759711
theorem B9564187 : Blo 2095435 9564187 := bstep (se 1 (by rfl) ⟨7173140, by rfl⟩ : syracuseStep 9564187 = 14346281) B14346281
theorem B12752249 : Blo 2095435 12752249 := bstep (se 2 (by rfl) ⟨4782093, by rfl⟩ : syracuseStep 12752249 = 9564187) B9564187
theorem B34005997 : Blo 2095435 34005997 := bstep (se 3 (by rfl) ⟨6376124, by rfl⟩ : syracuseStep 34005997 = 12752249) B12752249
theorem B45341329 : Blo 2095435 45341329 := bstep (se 2 (by rfl) ⟨17002998, by rfl⟩ : syracuseStep 45341329 = 34005997) B34005997
theorem B60455105 : Blo 2095435 60455105 := bstep (se 2 (by rfl) ⟨22670664, by rfl⟩ : syracuseStep 60455105 = 45341329) B45341329
theorem B40303403 : Blo 2095435 40303403 := bstep (se 1 (by rfl) ⟨30227552, by rfl⟩ : syracuseStep 40303403 = 60455105) B60455105
theorem B26868935 : Blo 2095435 26868935 := bstep (se 1 (by rfl) ⟨20151701, by rfl⟩ : syracuseStep 26868935 = 40303403) B40303403
theorem B17912623 : Blo 2095435 17912623 := bstep (se 1 (by rfl) ⟨13434467, by rfl⟩ : syracuseStep 17912623 = 26868935) B26868935
theorem B23883497 : Blo 2095435 23883497 := bstep (se 2 (by rfl) ⟨8956311, by rfl⟩ : syracuseStep 23883497 = 17912623) B17912623
theorem B15922331 : Blo 2095435 15922331 := bstep (se 1 (by rfl) ⟨11941748, by rfl⟩ : syracuseStep 15922331 = 23883497) B23883497
theorem B10614887 : Blo 2095435 10614887 := bstep (se 1 (by rfl) ⟨7961165, by rfl⟩ : syracuseStep 10614887 = 15922331) B15922331
theorem B7076591 : Blo 2095435 7076591 := bstep (se 1 (by rfl) ⟨5307443, by rfl⟩ : syracuseStep 7076591 = 10614887) B10614887
theorem B4717727 : Blo 2095435 4717727 := bstep (se 1 (by rfl) ⟨3538295, by rfl⟩ : syracuseStep 4717727 = 7076591) B7076591
theorem B3145151 : Blo 2095435 3145151 := bstep (se 1 (by rfl) ⟨2358863, by rfl⟩ : syracuseStep 3145151 = 4717727) B4717727
theorem B2096767 : Blo 2095435 2096767 := bstep (se 1 (by rfl) ⟨1572575, by rfl⟩ : syracuseStep 2096767 = 3145151) B3145151
theorem B3145157 : Blo 2095435 3145157 := bbase (se 4 (by rfl) ⟨294858, by rfl⟩ : syracuseStep 3145157 = 589717) (by norm_num)
theorem B2096771 : Blo 2095435 2096771 := bstep (se 1 (by rfl) ⟨1572578, by rfl⟩ : syracuseStep 2096771 = 3145157) B3145157
theorem B3538309 : Blo 2095435 3538309 := bbase (se 4 (by rfl) ⟨331716, by rfl⟩ : syracuseStep 3538309 = 663433) (by norm_num)
theorem B4717745 : Blo 2095435 4717745 := bstep (se 2 (by rfl) ⟨1769154, by rfl⟩ : syracuseStep 4717745 = 3538309) B3538309
theorem B3145163 : Blo 2095435 3145163 := bstep (se 1 (by rfl) ⟨2358872, by rfl⟩ : syracuseStep 3145163 = 4717745) B4717745
theorem B2096775 : Blo 2095435 2096775 := bstep (se 1 (by rfl) ⟨1572581, by rfl⟩ : syracuseStep 2096775 = 3145163) B3145163
theorem B2358877 : Blo 2095435 2358877 := bbase (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) (by norm_num)
theorem B3145169 : Blo 2095435 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B2096779 : Blo 2095435 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B7076645 : Blo 2095435 7076645 := bbase (se 4 (by rfl) ⟨663435, by rfl⟩ : syracuseStep 7076645 = 1326871) (by norm_num)
theorem B4717763 : Blo 2095435 4717763 := bstep (se 1 (by rfl) ⟨3538322, by rfl⟩ : syracuseStep 4717763 = 7076645) B7076645
theorem B3145175 : Blo 2095435 3145175 := bstep (se 1 (by rfl) ⟨2358881, by rfl⟩ : syracuseStep 3145175 = 4717763) B4717763
theorem B2096783 : Blo 2095435 2096783 := bstep (se 1 (by rfl) ⟨1572587, by rfl⟩ : syracuseStep 2096783 = 3145175) B3145175
theorem B3145181 : Blo 2095435 3145181 := bbase (se 3 (by rfl) ⟨589721, by rfl⟩ : syracuseStep 3145181 = 1179443) (by norm_num)
theorem B2096787 : Blo 2095435 2096787 := bstep (se 1 (by rfl) ⟨1572590, by rfl⟩ : syracuseStep 2096787 = 3145181) B3145181
theorem B4717781 : Blo 2095435 4717781 := bbase (se 7 (by rfl) ⟨55286, by rfl⟩ : syracuseStep 4717781 = 110573) (by norm_num)
theorem B3145187 : Blo 2095435 3145187 := bstep (se 1 (by rfl) ⟨2358890, by rfl⟩ : syracuseStep 3145187 = 4717781) B4717781
theorem B2096791 : Blo 2095435 2096791 := bstep (se 1 (by rfl) ⟨1572593, by rfl⟩ : syracuseStep 2096791 = 3145187) B3145187
theorem B2518997 : Blo 2095435 2518997 := bbase (se 7 (by rfl) ⟨29519, by rfl⟩ : syracuseStep 2518997 = 59039) (by norm_num)
theorem B6717325 : Blo 2095435 6717325 := bstep (se 3 (by rfl) ⟨1259498, by rfl⟩ : syracuseStep 6717325 = 2518997) B2518997
theorem B8956433 : Blo 2095435 8956433 := bstep (se 2 (by rfl) ⟨3358662, by rfl⟩ : syracuseStep 8956433 = 6717325) B6717325
theorem B5970955 : Blo 2095435 5970955 := bstep (se 1 (by rfl) ⟨4478216, by rfl⟩ : syracuseStep 5970955 = 8956433) B8956433
theorem B7961273 : Blo 2095435 7961273 := bstep (se 2 (by rfl) ⟨2985477, by rfl⟩ : syracuseStep 7961273 = 5970955) B5970955
theorem B5307515 : Blo 2095435 5307515 := bstep (se 1 (by rfl) ⟨3980636, by rfl⟩ : syracuseStep 5307515 = 7961273) B7961273
theorem B3538343 : Blo 2095435 3538343 := bstep (se 1 (by rfl) ⟨2653757, by rfl⟩ : syracuseStep 3538343 = 5307515) B5307515
theorem B2358895 : Blo 2095435 2358895 := bstep (se 1 (by rfl) ⟨1769171, by rfl⟩ : syracuseStep 2358895 = 3538343) B3538343
theorem B3145193 : Blo 2095435 3145193 := bstep (se 2 (by rfl) ⟨1179447, by rfl⟩ : syracuseStep 3145193 = 2358895) B2358895
theorem B2096795 : Blo 2095435 2096795 := bstep (se 1 (by rfl) ⟨1572596, by rfl⟩ : syracuseStep 2096795 = 3145193) B3145193
theorem B10076005 : Blo 2095435 10076005 := bbase (se 4 (by rfl) ⟨944625, by rfl⟩ : syracuseStep 10076005 = 1889251) (by norm_num)
theorem B13434673 : Blo 2095435 13434673 := bstep (se 2 (by rfl) ⟨5038002, by rfl⟩ : syracuseStep 13434673 = 10076005) B10076005
theorem B17912897 : Blo 2095435 17912897 := bstep (se 2 (by rfl) ⟨6717336, by rfl⟩ : syracuseStep 17912897 = 13434673) B13434673
theorem B11941931 : Blo 2095435 11941931 := bstep (se 1 (by rfl) ⟨8956448, by rfl⟩ : syracuseStep 11941931 = 17912897) B17912897
theorem B7961287 : Blo 2095435 7961287 := bstep (se 1 (by rfl) ⟨5970965, by rfl⟩ : syracuseStep 7961287 = 11941931) B11941931
theorem B10615049 : Blo 2095435 10615049 := bstep (se 2 (by rfl) ⟨3980643, by rfl⟩ : syracuseStep 10615049 = 7961287) B7961287
theorem B7076699 : Blo 2095435 7076699 := bstep (se 1 (by rfl) ⟨5307524, by rfl⟩ : syracuseStep 7076699 = 10615049) B10615049
theorem B4717799 : Blo 2095435 4717799 := bstep (se 1 (by rfl) ⟨3538349, by rfl⟩ : syracuseStep 4717799 = 7076699) B7076699
theorem B3145199 : Blo 2095435 3145199 := bstep (se 1 (by rfl) ⟨2358899, by rfl⟩ : syracuseStep 3145199 = 4717799) B4717799
theorem B2096799 : Blo 2095435 2096799 := bstep (se 1 (by rfl) ⟨1572599, by rfl⟩ : syracuseStep 2096799 = 3145199) B3145199
theorem B3145205 : Blo 2095435 3145205 := bbase (se 5 (by rfl) ⟨147431, by rfl⟩ : syracuseStep 3145205 = 294863) (by norm_num)
theorem B2096803 : Blo 2095435 2096803 := bstep (se 1 (by rfl) ⟨1572602, by rfl⟩ : syracuseStep 2096803 = 3145205) B3145205
theorem B2239121 : Blo 2095435 2239121 := bbase (se 2 (by rfl) ⟨839670, by rfl⟩ : syracuseStep 2239121 = 1679341) (by norm_num)
theorem B5970989 : Blo 2095435 5970989 := bstep (se 3 (by rfl) ⟨1119560, by rfl⟩ : syracuseStep 5970989 = 2239121) B2239121
theorem B3980659 : Blo 2095435 3980659 := bstep (se 1 (by rfl) ⟨2985494, by rfl⟩ : syracuseStep 3980659 = 5970989) B5970989
theorem B5307545 : Blo 2095435 5307545 := bstep (se 2 (by rfl) ⟨1990329, by rfl⟩ : syracuseStep 5307545 = 3980659) B3980659
theorem B3538363 : Blo 2095435 3538363 := bstep (se 1 (by rfl) ⟨2653772, by rfl⟩ : syracuseStep 3538363 = 5307545) B5307545
theorem B4717817 : Blo 2095435 4717817 := bstep (se 2 (by rfl) ⟨1769181, by rfl⟩ : syracuseStep 4717817 = 3538363) B3538363
theorem B3145211 : Blo 2095435 3145211 := bstep (se 1 (by rfl) ⟨2358908, by rfl⟩ : syracuseStep 3145211 = 4717817) B4717817
theorem B2096807 : Blo 2095435 2096807 := bstep (se 1 (by rfl) ⟨1572605, by rfl⟩ : syracuseStep 2096807 = 3145211) B3145211
theorem B2358913 : Blo 2095435 2358913 := bbase (se 2 (by rfl) ⟨884592, by rfl⟩ : syracuseStep 2358913 = 1769185) (by norm_num)
theorem B3145217 : Blo 2095435 3145217 := bstep (se 2 (by rfl) ⟨1179456, by rfl⟩ : syracuseStep 3145217 = 2358913) B2358913
theorem B2096811 : Blo 2095435 2096811 := bstep (se 1 (by rfl) ⟨1572608, by rfl⟩ : syracuseStep 2096811 = 3145217) B3145217
theorem B5307565 : Blo 2095435 5307565 := bbase (se 3 (by rfl) ⟨995168, by rfl⟩ : syracuseStep 5307565 = 1990337) (by norm_num)
theorem B7076753 : Blo 2095435 7076753 := bstep (se 2 (by rfl) ⟨2653782, by rfl⟩ : syracuseStep 7076753 = 5307565) B5307565
theorem B4717835 : Blo 2095435 4717835 := bstep (se 1 (by rfl) ⟨3538376, by rfl⟩ : syracuseStep 4717835 = 7076753) B7076753
theorem B3145223 : Blo 2095435 3145223 := bstep (se 1 (by rfl) ⟨2358917, by rfl⟩ : syracuseStep 3145223 = 4717835) B4717835
theorem B2096815 : Blo 2095435 2096815 := bstep (se 1 (by rfl) ⟨1572611, by rfl⟩ : syracuseStep 2096815 = 3145223) B3145223
theorem B3145229 : Blo 2095435 3145229 := bbase (se 3 (by rfl) ⟨589730, by rfl⟩ : syracuseStep 3145229 = 1179461) (by norm_num)
theorem B2096819 : Blo 2095435 2096819 := bstep (se 1 (by rfl) ⟨1572614, by rfl⟩ : syracuseStep 2096819 = 3145229) B3145229
theorem B4717853 : Blo 2095435 4717853 := bbase (se 3 (by rfl) ⟨884597, by rfl⟩ : syracuseStep 4717853 = 1769195) (by norm_num)
theorem B3145235 : Blo 2095435 3145235 := bstep (se 1 (by rfl) ⟨2358926, by rfl⟩ : syracuseStep 3145235 = 4717853) B4717853
theorem B2096823 : Blo 2095435 2096823 := bstep (se 1 (by rfl) ⟨1572617, by rfl⟩ : syracuseStep 2096823 = 3145235) B3145235
theorem B3538397 : Blo 2095435 3538397 := bbase (se 3 (by rfl) ⟨663449, by rfl⟩ : syracuseStep 3538397 = 1326899) (by norm_num)
theorem B2358931 : Blo 2095435 2358931 := bstep (se 1 (by rfl) ⟨1769198, by rfl⟩ : syracuseStep 2358931 = 3538397) B3538397
theorem B3145241 : Blo 2095435 3145241 := bstep (se 2 (by rfl) ⟨1179465, by rfl⟩ : syracuseStep 3145241 = 2358931) B2358931
theorem B2096827 : Blo 2095435 2096827 := bstep (se 1 (by rfl) ⟨1572620, by rfl⟩ : syracuseStep 2096827 = 3145241) B3145241
theorem B2801621 : Blo 2095435 2801621 := bbase (se 7 (by rfl) ⟨32831, by rfl⟩ : syracuseStep 2801621 = 65663) (by norm_num)
theorem B7470989 : Blo 2095435 7470989 := bstep (se 3 (by rfl) ⟨1400810, by rfl⟩ : syracuseStep 7470989 = 2801621) B2801621
theorem B4980659 : Blo 2095435 4980659 := bstep (se 1 (by rfl) ⟨3735494, by rfl⟩ : syracuseStep 4980659 = 7470989) B7470989
theorem B53127029 : Blo 2095435 53127029 := bstep (se 5 (by rfl) ⟨2490329, by rfl⟩ : syracuseStep 53127029 = 4980659) B4980659
theorem B141672077 : Blo 2095435 141672077 := bstep (se 3 (by rfl) ⟨26563514, by rfl⟩ : syracuseStep 141672077 = 53127029) B53127029
theorem B94448051 : Blo 2095435 94448051 := bstep (se 1 (by rfl) ⟨70836038, by rfl⟩ : syracuseStep 94448051 = 141672077) B141672077
theorem B62965367 : Blo 2095435 62965367 := bstep (se 1 (by rfl) ⟨47224025, by rfl⟩ : syracuseStep 62965367 = 94448051) B94448051
theorem B41976911 : Blo 2095435 41976911 := bstep (se 1 (by rfl) ⟨31482683, by rfl⟩ : syracuseStep 41976911 = 62965367) B62965367
theorem B111938429 : Blo 2095435 111938429 := bstep (se 3 (by rfl) ⟨20988455, by rfl⟩ : syracuseStep 111938429 = 41976911) B41976911
theorem B74625619 : Blo 2095435 74625619 := bstep (se 1 (by rfl) ⟨55969214, by rfl⟩ : syracuseStep 74625619 = 111938429) B111938429
theorem B99500825 : Blo 2095435 99500825 := bstep (se 2 (by rfl) ⟨37312809, by rfl⟩ : syracuseStep 99500825 = 74625619) B74625619
theorem B265335533 : Blo 2095435 265335533 := bstep (se 3 (by rfl) ⟨49750412, by rfl⟩ : syracuseStep 265335533 = 99500825) B99500825
theorem B176890355 : Blo 2095435 176890355 := bstep (se 1 (by rfl) ⟨132667766, by rfl⟩ : syracuseStep 176890355 = 265335533) B265335533
theorem B117926903 : Blo 2095435 117926903 := bstep (se 1 (by rfl) ⟨88445177, by rfl⟩ : syracuseStep 117926903 = 176890355) B176890355
theorem B78617935 : Blo 2095435 78617935 := bstep (se 1 (by rfl) ⟨58963451, by rfl⟩ : syracuseStep 78617935 = 117926903) B117926903
theorem B419295653 : Blo 2095435 419295653 := bstep (se 4 (by rfl) ⟨39308967, by rfl⟩ : syracuseStep 419295653 = 78617935) B78617935
theorem B279530435 : Blo 2095435 279530435 := bstep (se 1 (by rfl) ⟨209647826, by rfl⟩ : syracuseStep 279530435 = 419295653) B419295653
theorem B186353623 : Blo 2095435 186353623 := bstep (se 1 (by rfl) ⟨139765217, by rfl⟩ : syracuseStep 186353623 = 279530435) B279530435
theorem B248471497 : Blo 2095435 248471497 := bstep (se 2 (by rfl) ⟨93176811, by rfl⟩ : syracuseStep 248471497 = 186353623) B186353623
theorem B331295329 : Blo 2095435 331295329 := bstep (se 2 (by rfl) ⟨124235748, by rfl⟩ : syracuseStep 331295329 = 248471497) B248471497
theorem B441727105 : Blo 2095435 441727105 := bstep (se 2 (by rfl) ⟨165647664, by rfl⟩ : syracuseStep 441727105 = 331295329) B331295329
theorem B588969473 : Blo 2095435 588969473 := bstep (se 2 (by rfl) ⟨220863552, by rfl⟩ : syracuseStep 588969473 = 441727105) B441727105
theorem B1570585261 : Blo 2095435 1570585261 := bstep (se 3 (by rfl) ⟨294484736, by rfl⟩ : syracuseStep 1570585261 = 588969473) B588969473
theorem B2094113681 : Blo 2095435 2094113681 := bstep (se 2 (by rfl) ⟨785292630, by rfl⟩ : syracuseStep 2094113681 = 1570585261) B1570585261
theorem B1396075787 : Blo 2095435 1396075787 := bstep (se 1 (by rfl) ⟨1047056840, by rfl⟩ : syracuseStep 1396075787 = 2094113681) B2094113681
theorem B930717191 : Blo 2095435 930717191 := bstep (se 1 (by rfl) ⟨698037893, by rfl⟩ : syracuseStep 930717191 = 1396075787) B1396075787
theorem B620478127 : Blo 2095435 620478127 := bstep (se 1 (by rfl) ⟨465358595, by rfl⟩ : syracuseStep 620478127 = 930717191) B930717191
theorem B3309216677 : Blo 2095435 3309216677 := bstep (se 4 (by rfl) ⟨310239063, by rfl⟩ : syracuseStep 3309216677 = 620478127) B620478127
theorem B2206144451 : Blo 2095435 2206144451 := bstep (se 1 (by rfl) ⟨1654608338, by rfl⟩ : syracuseStep 2206144451 = 3309216677) B3309216677
theorem B1470762967 : Blo 2095435 1470762967 := bstep (se 1 (by rfl) ⟨1103072225, by rfl⟩ : syracuseStep 1470762967 = 2206144451) B2206144451
theorem B1961017289 : Blo 2095435 1961017289 := bstep (se 2 (by rfl) ⟨735381483, by rfl⟩ : syracuseStep 1961017289 = 1470762967) B1470762967
theorem B1307344859 : Blo 2095435 1307344859 := bstep (se 1 (by rfl) ⟨980508644, by rfl⟩ : syracuseStep 1307344859 = 1961017289) B1961017289
theorem B871563239 : Blo 2095435 871563239 := bstep (se 1 (by rfl) ⟨653672429, by rfl⟩ : syracuseStep 871563239 = 1307344859) B1307344859
theorem B581042159 : Blo 2095435 581042159 := bstep (se 1 (by rfl) ⟨435781619, by rfl⟩ : syracuseStep 581042159 = 871563239) B871563239
theorem B387361439 : Blo 2095435 387361439 := bstep (se 1 (by rfl) ⟨290521079, by rfl⟩ : syracuseStep 387361439 = 581042159) B581042159
theorem B258240959 : Blo 2095435 258240959 := bstep (se 1 (by rfl) ⟨193680719, by rfl⟩ : syracuseStep 258240959 = 387361439) B387361439
theorem B172160639 : Blo 2095435 172160639 := bstep (se 1 (by rfl) ⟨129120479, by rfl⟩ : syracuseStep 172160639 = 258240959) B258240959
theorem B114773759 : Blo 2095435 114773759 := bstep (se 1 (by rfl) ⟨86080319, by rfl⟩ : syracuseStep 114773759 = 172160639) B172160639
theorem B76515839 : Blo 2095435 76515839 := bstep (se 1 (by rfl) ⟨57386879, by rfl⟩ : syracuseStep 76515839 = 114773759) B114773759
theorem B51010559 : Blo 2095435 51010559 := bstep (se 1 (by rfl) ⟨38257919, by rfl⟩ : syracuseStep 51010559 = 76515839) B76515839
theorem B34007039 : Blo 2095435 34007039 := bstep (se 1 (by rfl) ⟨25505279, by rfl⟩ : syracuseStep 34007039 = 51010559) B51010559
theorem B22671359 : Blo 2095435 22671359 := bstep (se 1 (by rfl) ⟨17003519, by rfl⟩ : syracuseStep 22671359 = 34007039) B34007039
theorem B15114239 : Blo 2095435 15114239 := bstep (se 1 (by rfl) ⟨11335679, by rfl⟩ : syracuseStep 15114239 = 22671359) B22671359
theorem B10076159 : Blo 2095435 10076159 := bstep (se 1 (by rfl) ⟨7557119, by rfl⟩ : syracuseStep 10076159 = 15114239) B15114239
theorem B6717439 : Blo 2095435 6717439 := bstep (se 1 (by rfl) ⟨5038079, by rfl⟩ : syracuseStep 6717439 = 10076159) B10076159
theorem B8956585 : Blo 2095435 8956585 := bstep (se 2 (by rfl) ⟨3358719, by rfl⟩ : syracuseStep 8956585 = 6717439) B6717439
theorem B11942113 : Blo 2095435 11942113 := bstep (se 2 (by rfl) ⟨4478292, by rfl⟩ : syracuseStep 11942113 = 8956585) B8956585
theorem B15922817 : Blo 2095435 15922817 := bstep (se 2 (by rfl) ⟨5971056, by rfl⟩ : syracuseStep 15922817 = 11942113) B11942113
theorem B10615211 : Blo 2095435 10615211 := bstep (se 1 (by rfl) ⟨7961408, by rfl⟩ : syracuseStep 10615211 = 15922817) B15922817
theorem B7076807 : Blo 2095435 7076807 := bstep (se 1 (by rfl) ⟨5307605, by rfl⟩ : syracuseStep 7076807 = 10615211) B10615211
theorem B4717871 : Blo 2095435 4717871 := bstep (se 1 (by rfl) ⟨3538403, by rfl⟩ : syracuseStep 4717871 = 7076807) B7076807
theorem B3145247 : Blo 2095435 3145247 := bstep (se 1 (by rfl) ⟨2358935, by rfl⟩ : syracuseStep 3145247 = 4717871) B4717871
theorem B2096831 : Blo 2095435 2096831 := bstep (se 1 (by rfl) ⟨1572623, by rfl⟩ : syracuseStep 2096831 = 3145247) B3145247
theorem B3145253 : Blo 2095435 3145253 := bbase (se 4 (by rfl) ⟨294867, by rfl⟩ : syracuseStep 3145253 = 589735) (by norm_num)
theorem B2096835 : Blo 2095435 2096835 := bstep (se 1 (by rfl) ⟨1572626, by rfl⟩ : syracuseStep 2096835 = 3145253) B3145253
theorem B2653813 : Blo 2095435 2653813 := bbase (se 5 (by rfl) ⟨124397, by rfl⟩ : syracuseStep 2653813 = 248795) (by norm_num)
theorem B3538417 : Blo 2095435 3538417 := bstep (se 2 (by rfl) ⟨1326906, by rfl⟩ : syracuseStep 3538417 = 2653813) B2653813
theorem B4717889 : Blo 2095435 4717889 := bstep (se 2 (by rfl) ⟨1769208, by rfl⟩ : syracuseStep 4717889 = 3538417) B3538417
theorem B3145259 : Blo 2095435 3145259 := bstep (se 1 (by rfl) ⟨2358944, by rfl⟩ : syracuseStep 3145259 = 4717889) B4717889
theorem B2096839 : Blo 2095435 2096839 := bstep (se 1 (by rfl) ⟨1572629, by rfl⟩ : syracuseStep 2096839 = 3145259) B3145259
theorem B2358949 : Blo 2095435 2358949 := bbase (se 4 (by rfl) ⟨221151, by rfl⟩ : syracuseStep 2358949 = 442303) (by norm_num)
theorem B3145265 : Blo 2095435 3145265 := bstep (se 2 (by rfl) ⟨1179474, by rfl⟩ : syracuseStep 3145265 = 2358949) B2358949
theorem B2096843 : Blo 2095435 2096843 := bstep (se 1 (by rfl) ⟨1572632, by rfl⟩ : syracuseStep 2096843 = 3145265) B3145265
theorem B6809141 : Blo 2095435 6809141 := bbase (se 5 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 6809141 = 638357) (by norm_num)
theorem B18157709 : Blo 2095435 18157709 := bstep (se 3 (by rfl) ⟨3404570, by rfl⟩ : syracuseStep 18157709 = 6809141) B6809141
theorem B48420557 : Blo 2095435 48420557 := bstep (se 3 (by rfl) ⟨9078854, by rfl⟩ : syracuseStep 48420557 = 18157709) B18157709
theorem B32280371 : Blo 2095435 32280371 := bstep (se 1 (by rfl) ⟨24210278, by rfl⟩ : syracuseStep 32280371 = 48420557) B48420557
theorem B21520247 : Blo 2095435 21520247 := bstep (se 1 (by rfl) ⟨16140185, by rfl⟩ : syracuseStep 21520247 = 32280371) B32280371
theorem B57387325 : Blo 2095435 57387325 := bstep (se 3 (by rfl) ⟨10760123, by rfl⟩ : syracuseStep 57387325 = 21520247) B21520247
theorem B76516433 : Blo 2095435 76516433 := bstep (se 2 (by rfl) ⟨28693662, by rfl⟩ : syracuseStep 76516433 = 57387325) B57387325
theorem B51010955 : Blo 2095435 51010955 := bstep (se 1 (by rfl) ⟨38258216, by rfl⟩ : syracuseStep 51010955 = 76516433) B76516433
theorem B34007303 : Blo 2095435 34007303 := bstep (se 1 (by rfl) ⟨25505477, by rfl⟩ : syracuseStep 34007303 = 51010955) B51010955
theorem B22671535 : Blo 2095435 22671535 := bstep (se 1 (by rfl) ⟨17003651, by rfl⟩ : syracuseStep 22671535 = 34007303) B34007303
theorem B30228713 : Blo 2095435 30228713 := bstep (se 2 (by rfl) ⟨11335767, by rfl⟩ : syracuseStep 30228713 = 22671535) B22671535
theorem B20152475 : Blo 2095435 20152475 := bstep (se 1 (by rfl) ⟨15114356, by rfl⟩ : syracuseStep 20152475 = 30228713) B30228713
theorem B13434983 : Blo 2095435 13434983 := bstep (se 1 (by rfl) ⟨10076237, by rfl⟩ : syracuseStep 13434983 = 20152475) B20152475
theorem B8956655 : Blo 2095435 8956655 := bstep (se 1 (by rfl) ⟨6717491, by rfl⟩ : syracuseStep 8956655 = 13434983) B13434983
theorem B5971103 : Blo 2095435 5971103 := bstep (se 1 (by rfl) ⟨4478327, by rfl⟩ : syracuseStep 5971103 = 8956655) B8956655
theorem B3980735 : Blo 2095435 3980735 := bstep (se 1 (by rfl) ⟨2985551, by rfl⟩ : syracuseStep 3980735 = 5971103) B5971103
theorem B2653823 : Blo 2095435 2653823 := bstep (se 1 (by rfl) ⟨1990367, by rfl⟩ : syracuseStep 2653823 = 3980735) B3980735
theorem B7076861 : Blo 2095435 7076861 := bstep (se 3 (by rfl) ⟨1326911, by rfl⟩ : syracuseStep 7076861 = 2653823) B2653823
theorem B4717907 : Blo 2095435 4717907 := bstep (se 1 (by rfl) ⟨3538430, by rfl⟩ : syracuseStep 4717907 = 7076861) B7076861
theorem B3145271 : Blo 2095435 3145271 := bstep (se 1 (by rfl) ⟨2358953, by rfl⟩ : syracuseStep 3145271 = 4717907) B4717907
theorem B2096847 : Blo 2095435 2096847 := bstep (se 1 (by rfl) ⟨1572635, by rfl⟩ : syracuseStep 2096847 = 3145271) B3145271
theorem B3145277 : Blo 2095435 3145277 := bbase (se 3 (by rfl) ⟨589739, by rfl⟩ : syracuseStep 3145277 = 1179479) (by norm_num)
theorem B2096851 : Blo 2095435 2096851 := bstep (se 1 (by rfl) ⟨1572638, by rfl⟩ : syracuseStep 2096851 = 3145277) B3145277
theorem B4717925 : Blo 2095435 4717925 := bbase (se 4 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 4717925 = 884611) (by norm_num)
theorem B3145283 : Blo 2095435 3145283 := bstep (se 1 (by rfl) ⟨2358962, by rfl⟩ : syracuseStep 3145283 = 4717925) B4717925
theorem B2096855 : Blo 2095435 2096855 := bstep (se 1 (by rfl) ⟨1572641, by rfl⟩ : syracuseStep 2096855 = 3145283) B3145283
theorem B5307677 : Blo 2095435 5307677 := bbase (se 3 (by rfl) ⟨995189, by rfl⟩ : syracuseStep 5307677 = 1990379) (by norm_num)
theorem B3538451 : Blo 2095435 3538451 := bstep (se 1 (by rfl) ⟨2653838, by rfl⟩ : syracuseStep 3538451 = 5307677) B5307677
theorem B2358967 : Blo 2095435 2358967 := bstep (se 1 (by rfl) ⟨1769225, by rfl⟩ : syracuseStep 2358967 = 3538451) B3538451
theorem B3145289 : Blo 2095435 3145289 := bstep (se 2 (by rfl) ⟨1179483, by rfl⟩ : syracuseStep 3145289 = 2358967) B2358967
theorem B2096859 : Blo 2095435 2096859 := bstep (se 1 (by rfl) ⟨1572644, by rfl⟩ : syracuseStep 2096859 = 3145289) B3145289
theorem B3980765 : Blo 2095435 3980765 := bbase (se 3 (by rfl) ⟨746393, by rfl⟩ : syracuseStep 3980765 = 1492787) (by norm_num)
theorem B10615373 : Blo 2095435 10615373 := bstep (se 3 (by rfl) ⟨1990382, by rfl⟩ : syracuseStep 10615373 = 3980765) B3980765
theorem B7076915 : Blo 2095435 7076915 := bstep (se 1 (by rfl) ⟨5307686, by rfl⟩ : syracuseStep 7076915 = 10615373) B10615373
theorem B4717943 : Blo 2095435 4717943 := bstep (se 1 (by rfl) ⟨3538457, by rfl⟩ : syracuseStep 4717943 = 7076915) B7076915
theorem B3145295 : Blo 2095435 3145295 := bstep (se 1 (by rfl) ⟨2358971, by rfl⟩ : syracuseStep 3145295 = 4717943) B4717943
theorem B2096863 : Blo 2095435 2096863 := bstep (se 1 (by rfl) ⟨1572647, by rfl⟩ : syracuseStep 2096863 = 3145295) B3145295
theorem B3145301 : Blo 2095435 3145301 := bbase (se 8 (by rfl) ⟨18429, by rfl⟩ : syracuseStep 3145301 = 36859) (by norm_num)
theorem B2096867 : Blo 2095435 2096867 := bstep (se 1 (by rfl) ⟨1572650, by rfl⟩ : syracuseStep 2096867 = 3145301) B3145301
theorem B8956757 : Blo 2095435 8956757 := bbase (se 9 (by rfl) ⟨26240, by rfl⟩ : syracuseStep 8956757 = 52481) (by norm_num)
theorem B5971171 : Blo 2095435 5971171 := bstep (se 1 (by rfl) ⟨4478378, by rfl⟩ : syracuseStep 5971171 = 8956757) B8956757
theorem B7961561 : Blo 2095435 7961561 := bstep (se 2 (by rfl) ⟨2985585, by rfl⟩ : syracuseStep 7961561 = 5971171) B5971171
theorem B5307707 : Blo 2095435 5307707 := bstep (se 1 (by rfl) ⟨3980780, by rfl⟩ : syracuseStep 5307707 = 7961561) B7961561
theorem B3538471 : Blo 2095435 3538471 := bstep (se 1 (by rfl) ⟨2653853, by rfl⟩ : syracuseStep 3538471 = 5307707) B5307707
theorem B4717961 : Blo 2095435 4717961 := bstep (se 2 (by rfl) ⟨1769235, by rfl⟩ : syracuseStep 4717961 = 3538471) B3538471
theorem B3145307 : Blo 2095435 3145307 := bstep (se 1 (by rfl) ⟨2358980, by rfl⟩ : syracuseStep 3145307 = 4717961) B4717961
theorem B2096871 : Blo 2095435 2096871 := bstep (se 1 (by rfl) ⟨1572653, by rfl⟩ : syracuseStep 2096871 = 3145307) B3145307
theorem B2358985 : Blo 2095435 2358985 := bbase (se 2 (by rfl) ⟨884619, by rfl⟩ : syracuseStep 2358985 = 1769239) (by norm_num)
theorem B3145313 : Blo 2095435 3145313 := bstep (se 2 (by rfl) ⟨1179492, by rfl⟩ : syracuseStep 3145313 = 2358985) B2358985
theorem B2096875 : Blo 2095435 2096875 := bstep (se 1 (by rfl) ⟨1572656, by rfl⟩ : syracuseStep 2096875 = 3145313) B3145313
theorem B2125489 : Blo 2095435 2125489 := bbase (se 2 (by rfl) ⟨797058, by rfl⟩ : syracuseStep 2125489 = 1594117) (by norm_num)
theorem B2833985 : Blo 2095435 2833985 := bstep (se 2 (by rfl) ⟨1062744, by rfl⟩ : syracuseStep 2833985 = 2125489) B2125489
theorem B7557293 : Blo 2095435 7557293 := bstep (se 3 (by rfl) ⟨1416992, by rfl⟩ : syracuseStep 7557293 = 2833985) B2833985
theorem B5038195 : Blo 2095435 5038195 := bstep (se 1 (by rfl) ⟨3778646, by rfl⟩ : syracuseStep 5038195 = 7557293) B7557293
theorem B6717593 : Blo 2095435 6717593 := bstep (se 2 (by rfl) ⟨2519097, by rfl⟩ : syracuseStep 6717593 = 5038195) B5038195
theorem B17913581 : Blo 2095435 17913581 := bstep (se 3 (by rfl) ⟨3358796, by rfl⟩ : syracuseStep 17913581 = 6717593) B6717593
theorem B11942387 : Blo 2095435 11942387 := bstep (se 1 (by rfl) ⟨8956790, by rfl⟩ : syracuseStep 11942387 = 17913581) B17913581
theorem B7961591 : Blo 2095435 7961591 := bstep (se 1 (by rfl) ⟨5971193, by rfl⟩ : syracuseStep 7961591 = 11942387) B11942387
theorem B5307727 : Blo 2095435 5307727 := bstep (se 1 (by rfl) ⟨3980795, by rfl⟩ : syracuseStep 5307727 = 7961591) B7961591
theorem B7076969 : Blo 2095435 7076969 := bstep (se 2 (by rfl) ⟨2653863, by rfl⟩ : syracuseStep 7076969 = 5307727) B5307727
theorem B4717979 : Blo 2095435 4717979 := bstep (se 1 (by rfl) ⟨3538484, by rfl⟩ : syracuseStep 4717979 = 7076969) B7076969
theorem B3145319 : Blo 2095435 3145319 := bstep (se 1 (by rfl) ⟨2358989, by rfl⟩ : syracuseStep 3145319 = 4717979) B4717979
theorem B2096879 : Blo 2095435 2096879 := bstep (se 1 (by rfl) ⟨1572659, by rfl⟩ : syracuseStep 2096879 = 3145319) B3145319
theorem B3145325 : Blo 2095435 3145325 := bbase (se 3 (by rfl) ⟨589748, by rfl⟩ : syracuseStep 3145325 = 1179497) (by norm_num)
theorem B2096883 : Blo 2095435 2096883 := bstep (se 1 (by rfl) ⟨1572662, by rfl⟩ : syracuseStep 2096883 = 3145325) B3145325
theorem B4717997 : Blo 2095435 4717997 := bbase (se 3 (by rfl) ⟨884624, by rfl⟩ : syracuseStep 4717997 = 1769249) (by norm_num)
theorem B3145331 : Blo 2095435 3145331 := bstep (se 1 (by rfl) ⟨2358998, by rfl⟩ : syracuseStep 3145331 = 4717997) B4717997
theorem B2096887 : Blo 2095435 2096887 := bstep (se 1 (by rfl) ⟨1572665, by rfl⟩ : syracuseStep 2096887 = 3145331) B3145331
theorem B2519113 : Blo 2095435 2519113 := bbase (se 2 (by rfl) ⟨944667, by rfl⟩ : syracuseStep 2519113 = 1889335) (by norm_num)
theorem B3358817 : Blo 2095435 3358817 := bstep (se 2 (by rfl) ⟨1259556, by rfl⟩ : syracuseStep 3358817 = 2519113) B2519113
theorem B2239211 : Blo 2095435 2239211 := bstep (se 1 (by rfl) ⟨1679408, by rfl⟩ : syracuseStep 2239211 = 3358817) B3358817
theorem B5971229 : Blo 2095435 5971229 := bstep (se 3 (by rfl) ⟨1119605, by rfl⟩ : syracuseStep 5971229 = 2239211) B2239211
theorem B3980819 : Blo 2095435 3980819 := bstep (se 1 (by rfl) ⟨2985614, by rfl⟩ : syracuseStep 3980819 = 5971229) B5971229
theorem B2653879 : Blo 2095435 2653879 := bstep (se 1 (by rfl) ⟨1990409, by rfl⟩ : syracuseStep 2653879 = 3980819) B3980819
theorem B3538505 : Blo 2095435 3538505 := bstep (se 2 (by rfl) ⟨1326939, by rfl⟩ : syracuseStep 3538505 = 2653879) B2653879
theorem B2359003 : Blo 2095435 2359003 := bstep (se 1 (by rfl) ⟨1769252, by rfl⟩ : syracuseStep 2359003 = 3538505) B3538505
theorem B3145337 : Blo 2095435 3145337 := bstep (se 2 (by rfl) ⟨1179501, by rfl⟩ : syracuseStep 3145337 = 2359003) B2359003
theorem B2096891 : Blo 2095435 2096891 := bstep (se 1 (by rfl) ⟨1572668, by rfl⟩ : syracuseStep 2096891 = 3145337) B3145337
theorem B3586789 : Blo 2095435 3586789 := bbase (se 4 (by rfl) ⟨336261, by rfl⟩ : syracuseStep 3586789 = 672523) (by norm_num)
theorem B19129541 : Blo 2095435 19129541 := bstep (se 4 (by rfl) ⟨1793394, by rfl⟩ : syracuseStep 19129541 = 3586789) B3586789
theorem B51012109 : Blo 2095435 51012109 := bstep (se 3 (by rfl) ⟨9564770, by rfl⟩ : syracuseStep 51012109 = 19129541) B19129541
theorem B68016145 : Blo 2095435 68016145 := bstep (se 2 (by rfl) ⟨25506054, by rfl⟩ : syracuseStep 68016145 = 51012109) B51012109
theorem B90688193 : Blo 2095435 90688193 := bstep (se 2 (by rfl) ⟨34008072, by rfl⟩ : syracuseStep 90688193 = 68016145) B68016145
theorem B60458795 : Blo 2095435 60458795 := bstep (se 1 (by rfl) ⟨45344096, by rfl⟩ : syracuseStep 60458795 = 90688193) B90688193
theorem B40305863 : Blo 2095435 40305863 := bstep (se 1 (by rfl) ⟨30229397, by rfl⟩ : syracuseStep 40305863 = 60458795) B60458795
theorem B26870575 : Blo 2095435 26870575 := bstep (se 1 (by rfl) ⟨20152931, by rfl⟩ : syracuseStep 26870575 = 40305863) B40305863
theorem B35827433 : Blo 2095435 35827433 := bstep (se 2 (by rfl) ⟨13435287, by rfl⟩ : syracuseStep 35827433 = 26870575) B26870575
theorem B23884955 : Blo 2095435 23884955 := bstep (se 1 (by rfl) ⟨17913716, by rfl⟩ : syracuseStep 23884955 = 35827433) B35827433
theorem B15923303 : Blo 2095435 15923303 := bstep (se 1 (by rfl) ⟨11942477, by rfl⟩ : syracuseStep 15923303 = 23884955) B23884955
theorem B10615535 : Blo 2095435 10615535 := bstep (se 1 (by rfl) ⟨7961651, by rfl⟩ : syracuseStep 10615535 = 15923303) B15923303
theorem B7077023 : Blo 2095435 7077023 := bstep (se 1 (by rfl) ⟨5307767, by rfl⟩ : syracuseStep 7077023 = 10615535) B10615535
theorem B4718015 : Blo 2095435 4718015 := bstep (se 1 (by rfl) ⟨3538511, by rfl⟩ : syracuseStep 4718015 = 7077023) B7077023
theorem B3145343 : Blo 2095435 3145343 := bstep (se 1 (by rfl) ⟨2359007, by rfl⟩ : syracuseStep 3145343 = 4718015) B4718015
theorem B2096895 : Blo 2095435 2096895 := bstep (se 1 (by rfl) ⟨1572671, by rfl⟩ : syracuseStep 2096895 = 3145343) B3145343
theorem B3145349 : Blo 2095435 3145349 := bbase (se 4 (by rfl) ⟨294876, by rfl⟩ : syracuseStep 3145349 = 589753) (by norm_num)
theorem B2096899 : Blo 2095435 2096899 := bstep (se 1 (by rfl) ⟨1572674, by rfl⟩ : syracuseStep 2096899 = 3145349) B3145349
theorem B3538525 : Blo 2095435 3538525 := bbase (se 3 (by rfl) ⟨663473, by rfl⟩ : syracuseStep 3538525 = 1326947) (by norm_num)
theorem B4718033 : Blo 2095435 4718033 := bstep (se 2 (by rfl) ⟨1769262, by rfl⟩ : syracuseStep 4718033 = 3538525) B3538525
theorem B3145355 : Blo 2095435 3145355 := bstep (se 1 (by rfl) ⟨2359016, by rfl⟩ : syracuseStep 3145355 = 4718033) B4718033
theorem B2096903 : Blo 2095435 2096903 := bstep (se 1 (by rfl) ⟨1572677, by rfl⟩ : syracuseStep 2096903 = 3145355) B3145355
theorem B2359021 : Blo 2095435 2359021 := bbase (se 3 (by rfl) ⟨442316, by rfl⟩ : syracuseStep 2359021 = 884633) (by norm_num)
theorem B3145361 : Blo 2095435 3145361 := bstep (se 2 (by rfl) ⟨1179510, by rfl⟩ : syracuseStep 3145361 = 2359021) B2359021
theorem B2096907 : Blo 2095435 2096907 := bstep (se 1 (by rfl) ⟨1572680, by rfl⟩ : syracuseStep 2096907 = 3145361) B3145361
theorem B7077077 : Blo 2095435 7077077 := bbase (se 7 (by rfl) ⟨82934, by rfl⟩ : syracuseStep 7077077 = 165869) (by norm_num)
theorem B4718051 : Blo 2095435 4718051 := bstep (se 1 (by rfl) ⟨3538538, by rfl⟩ : syracuseStep 4718051 = 7077077) B7077077
theorem B3145367 : Blo 2095435 3145367 := bstep (se 1 (by rfl) ⟨2359025, by rfl⟩ : syracuseStep 3145367 = 4718051) B4718051
theorem B2096911 : Blo 2095435 2096911 := bstep (se 1 (by rfl) ⟨1572683, by rfl⟩ : syracuseStep 2096911 = 3145367) B3145367
theorem B3145373 : Blo 2095435 3145373 := bbase (se 3 (by rfl) ⟨589757, by rfl⟩ : syracuseStep 3145373 = 1179515) (by norm_num)
theorem B2096915 : Blo 2095435 2096915 := bstep (se 1 (by rfl) ⟨1572686, by rfl⟩ : syracuseStep 2096915 = 3145373) B3145373
theorem B4718069 : Blo 2095435 4718069 := bbase (se 5 (by rfl) ⟨221159, by rfl⟩ : syracuseStep 4718069 = 442319) (by norm_num)
theorem B3145379 : Blo 2095435 3145379 := bstep (se 1 (by rfl) ⟨2359034, by rfl⟩ : syracuseStep 3145379 = 4718069) B4718069
theorem B2096919 : Blo 2095435 2096919 := bstep (se 1 (by rfl) ⟨1572689, by rfl⟩ : syracuseStep 2096919 = 3145379) B3145379
theorem B2154533 : Blo 2095435 2154533 := bbase (se 4 (by rfl) ⟨201987, by rfl⟩ : syracuseStep 2154533 = 403975) (by norm_num)
theorem B5745421 : Blo 2095435 5745421 := bstep (se 3 (by rfl) ⟨1077266, by rfl⟩ : syracuseStep 5745421 = 2154533) B2154533
theorem B30642245 : Blo 2095435 30642245 := bstep (se 4 (by rfl) ⟨2872710, by rfl⟩ : syracuseStep 30642245 = 5745421) B5745421
theorem B20428163 : Blo 2095435 20428163 := bstep (se 1 (by rfl) ⟨15321122, by rfl⟩ : syracuseStep 20428163 = 30642245) B30642245
theorem B13618775 : Blo 2095435 13618775 := bstep (se 1 (by rfl) ⟨10214081, by rfl⟩ : syracuseStep 13618775 = 20428163) B20428163
theorem B9079183 : Blo 2095435 9079183 := bstep (se 1 (by rfl) ⟨6809387, by rfl⟩ : syracuseStep 9079183 = 13618775) B13618775
theorem B12105577 : Blo 2095435 12105577 := bstep (se 2 (by rfl) ⟨4539591, by rfl⟩ : syracuseStep 12105577 = 9079183) B9079183
theorem B64563077 : Blo 2095435 64563077 := bstep (se 4 (by rfl) ⟨6052788, by rfl⟩ : syracuseStep 64563077 = 12105577) B12105577
theorem B43042051 : Blo 2095435 43042051 := bstep (se 1 (by rfl) ⟨32281538, by rfl⟩ : syracuseStep 43042051 = 64563077) B64563077
theorem B57389401 : Blo 2095435 57389401 := bstep (se 2 (by rfl) ⟨21521025, by rfl⟩ : syracuseStep 57389401 = 43042051) B43042051
theorem B76519201 : Blo 2095435 76519201 := bstep (se 2 (by rfl) ⟨28694700, by rfl⟩ : syracuseStep 76519201 = 57389401) B57389401
theorem B102025601 : Blo 2095435 102025601 := bstep (se 2 (by rfl) ⟨38259600, by rfl⟩ : syracuseStep 102025601 = 76519201) B76519201
theorem B68017067 : Blo 2095435 68017067 := bstep (se 1 (by rfl) ⟨51012800, by rfl⟩ : syracuseStep 68017067 = 102025601) B102025601
theorem B45344711 : Blo 2095435 45344711 := bstep (se 1 (by rfl) ⟨34008533, by rfl⟩ : syracuseStep 45344711 = 68017067) B68017067
theorem B30229807 : Blo 2095435 30229807 := bstep (se 1 (by rfl) ⟨22672355, by rfl⟩ : syracuseStep 30229807 = 45344711) B45344711
theorem B40306409 : Blo 2095435 40306409 := bstep (se 2 (by rfl) ⟨15114903, by rfl⟩ : syracuseStep 40306409 = 30229807) B30229807
theorem B26870939 : Blo 2095435 26870939 := bstep (se 1 (by rfl) ⟨20153204, by rfl⟩ : syracuseStep 26870939 = 40306409) B40306409
theorem B17913959 : Blo 2095435 17913959 := bstep (se 1 (by rfl) ⟨13435469, by rfl⟩ : syracuseStep 17913959 = 26870939) B26870939
theorem B11942639 : Blo 2095435 11942639 := bstep (se 1 (by rfl) ⟨8956979, by rfl⟩ : syracuseStep 11942639 = 17913959) B17913959
theorem B7961759 : Blo 2095435 7961759 := bstep (se 1 (by rfl) ⟨5971319, by rfl⟩ : syracuseStep 7961759 = 11942639) B11942639
theorem B5307839 : Blo 2095435 5307839 := bstep (se 1 (by rfl) ⟨3980879, by rfl⟩ : syracuseStep 5307839 = 7961759) B7961759
theorem B3538559 : Blo 2095435 3538559 := bstep (se 1 (by rfl) ⟨2653919, by rfl⟩ : syracuseStep 3538559 = 5307839) B5307839
theorem B2359039 : Blo 2095435 2359039 := bstep (se 1 (by rfl) ⟨1769279, by rfl⟩ : syracuseStep 2359039 = 3538559) B3538559
theorem B3145385 : Blo 2095435 3145385 := bstep (se 2 (by rfl) ⟨1179519, by rfl⟩ : syracuseStep 3145385 = 2359039) B2359039
theorem B2096923 : Blo 2095435 2096923 := bstep (se 1 (by rfl) ⟨1572692, by rfl⟩ : syracuseStep 2096923 = 3145385) B3145385
theorem B2239249 : Blo 2095435 2239249 := bbase (se 2 (by rfl) ⟨839718, by rfl⟩ : syracuseStep 2239249 = 1679437) (by norm_num)
theorem B2985665 : Blo 2095435 2985665 := bstep (se 2 (by rfl) ⟨1119624, by rfl⟩ : syracuseStep 2985665 = 2239249) B2239249
theorem B7961773 : Blo 2095435 7961773 := bstep (se 3 (by rfl) ⟨1492832, by rfl⟩ : syracuseStep 7961773 = 2985665) B2985665
theorem B10615697 : Blo 2095435 10615697 := bstep (se 2 (by rfl) ⟨3980886, by rfl⟩ : syracuseStep 10615697 = 7961773) B7961773
theorem B7077131 : Blo 2095435 7077131 := bstep (se 1 (by rfl) ⟨5307848, by rfl⟩ : syracuseStep 7077131 = 10615697) B10615697
theorem B4718087 : Blo 2095435 4718087 := bstep (se 1 (by rfl) ⟨3538565, by rfl⟩ : syracuseStep 4718087 = 7077131) B7077131
theorem B3145391 : Blo 2095435 3145391 := bstep (se 1 (by rfl) ⟨2359043, by rfl⟩ : syracuseStep 3145391 = 4718087) B4718087
theorem B2096927 : Blo 2095435 2096927 := bstep (se 1 (by rfl) ⟨1572695, by rfl⟩ : syracuseStep 2096927 = 3145391) B3145391
theorem B3145397 : Blo 2095435 3145397 := bbase (se 5 (by rfl) ⟨147440, by rfl⟩ : syracuseStep 3145397 = 294881) (by norm_num)
theorem B2096931 : Blo 2095435 2096931 := bstep (se 1 (by rfl) ⟨1572698, by rfl⟩ : syracuseStep 2096931 = 3145397) B3145397
theorem B5307869 : Blo 2095435 5307869 := bbase (se 3 (by rfl) ⟨995225, by rfl⟩ : syracuseStep 5307869 = 1990451) (by norm_num)
theorem B3538579 : Blo 2095435 3538579 := bstep (se 1 (by rfl) ⟨2653934, by rfl⟩ : syracuseStep 3538579 = 5307869) B5307869
theorem B4718105 : Blo 2095435 4718105 := bstep (se 2 (by rfl) ⟨1769289, by rfl⟩ : syracuseStep 4718105 = 3538579) B3538579
theorem B3145403 : Blo 2095435 3145403 := bstep (se 1 (by rfl) ⟨2359052, by rfl⟩ : syracuseStep 3145403 = 4718105) B4718105
theorem B2096935 : Blo 2095435 2096935 := bstep (se 1 (by rfl) ⟨1572701, by rfl⟩ : syracuseStep 2096935 = 3145403) B3145403
theorem B2359057 : Blo 2095435 2359057 := bbase (se 2 (by rfl) ⟨884646, by rfl⟩ : syracuseStep 2359057 = 1769293) (by norm_num)
theorem B3145409 : Blo 2095435 3145409 := bstep (se 2 (by rfl) ⟨1179528, by rfl⟩ : syracuseStep 3145409 = 2359057) B2359057
theorem B2096939 : Blo 2095435 2096939 := bstep (se 1 (by rfl) ⟨1572704, by rfl⟩ : syracuseStep 2096939 = 3145409) B3145409
theorem B3980917 : Blo 2095435 3980917 := bbase (se 5 (by rfl) ⟨186605, by rfl⟩ : syracuseStep 3980917 = 373211) (by norm_num)
theorem B5307889 : Blo 2095435 5307889 := bstep (se 2 (by rfl) ⟨1990458, by rfl⟩ : syracuseStep 5307889 = 3980917) B3980917
theorem B7077185 : Blo 2095435 7077185 := bstep (se 2 (by rfl) ⟨2653944, by rfl⟩ : syracuseStep 7077185 = 5307889) B5307889
theorem B4718123 : Blo 2095435 4718123 := bstep (se 1 (by rfl) ⟨3538592, by rfl⟩ : syracuseStep 4718123 = 7077185) B7077185
theorem B3145415 : Blo 2095435 3145415 := bstep (se 1 (by rfl) ⟨2359061, by rfl⟩ : syracuseStep 3145415 = 4718123) B4718123
theorem B2096943 : Blo 2095435 2096943 := bstep (se 1 (by rfl) ⟨1572707, by rfl⟩ : syracuseStep 2096943 = 3145415) B3145415
theorem B3145421 : Blo 2095435 3145421 := bbase (se 3 (by rfl) ⟨589766, by rfl⟩ : syracuseStep 3145421 = 1179533) (by norm_num)
theorem B2096947 : Blo 2095435 2096947 := bstep (se 1 (by rfl) ⟨1572710, by rfl⟩ : syracuseStep 2096947 = 3145421) B3145421
theorem B4718141 : Blo 2095435 4718141 := bbase (se 3 (by rfl) ⟨884651, by rfl⟩ : syracuseStep 4718141 = 1769303) (by norm_num)
theorem B3145427 : Blo 2095435 3145427 := bstep (se 1 (by rfl) ⟨2359070, by rfl⟩ : syracuseStep 3145427 = 4718141) B4718141
theorem B2096951 : Blo 2095435 2096951 := bstep (se 1 (by rfl) ⟨1572713, by rfl⟩ : syracuseStep 2096951 = 3145427) B3145427
theorem B3538613 : Blo 2095435 3538613 := bbase (se 5 (by rfl) ⟨165872, by rfl⟩ : syracuseStep 3538613 = 331745) (by norm_num)
theorem B2359075 : Blo 2095435 2359075 := bstep (se 1 (by rfl) ⟨1769306, by rfl⟩ : syracuseStep 2359075 = 3538613) B3538613
theorem B3145433 : Blo 2095435 3145433 := bstep (se 2 (by rfl) ⟨1179537, by rfl⟩ : syracuseStep 3145433 = 2359075) B2359075
theorem B2096955 : Blo 2095435 2096955 := bstep (se 1 (by rfl) ⟨1572716, by rfl⟩ : syracuseStep 2096955 = 3145433) B3145433
theorem B3358925 : Blo 2095435 3358925 := bbase (se 3 (by rfl) ⟨629798, by rfl⟩ : syracuseStep 3358925 = 1259597) (by norm_num)
theorem B2239283 : Blo 2095435 2239283 := bstep (se 1 (by rfl) ⟨1679462, by rfl⟩ : syracuseStep 2239283 = 3358925) B3358925
theorem B5971421 : Blo 2095435 5971421 := bstep (se 3 (by rfl) ⟨1119641, by rfl⟩ : syracuseStep 5971421 = 2239283) B2239283
theorem B15923789 : Blo 2095435 15923789 := bstep (se 3 (by rfl) ⟨2985710, by rfl⟩ : syracuseStep 15923789 = 5971421) B5971421
theorem B10615859 : Blo 2095435 10615859 := bstep (se 1 (by rfl) ⟨7961894, by rfl⟩ : syracuseStep 10615859 = 15923789) B15923789
theorem B7077239 : Blo 2095435 7077239 := bstep (se 1 (by rfl) ⟨5307929, by rfl⟩ : syracuseStep 7077239 = 10615859) B10615859
theorem B4718159 : Blo 2095435 4718159 := bstep (se 1 (by rfl) ⟨3538619, by rfl⟩ : syracuseStep 4718159 = 7077239) B7077239
theorem B3145439 : Blo 2095435 3145439 := bstep (se 1 (by rfl) ⟨2359079, by rfl⟩ : syracuseStep 3145439 = 4718159) B4718159
theorem B2096959 : Blo 2095435 2096959 := bstep (se 1 (by rfl) ⟨1572719, by rfl⟩ : syracuseStep 2096959 = 3145439) B3145439
theorem B3145445 : Blo 2095435 3145445 := bbase (se 4 (by rfl) ⟨294885, by rfl⟩ : syracuseStep 3145445 = 589771) (by norm_num)
theorem B2096963 : Blo 2095435 2096963 := bstep (se 1 (by rfl) ⟨1572722, by rfl⟩ : syracuseStep 2096963 = 3145445) B3145445
theorem B5971445 : Blo 2095435 5971445 := bbase (se 5 (by rfl) ⟨279911, by rfl⟩ : syracuseStep 5971445 = 559823) (by norm_num)
theorem B3980963 : Blo 2095435 3980963 := bstep (se 1 (by rfl) ⟨2985722, by rfl⟩ : syracuseStep 3980963 = 5971445) B5971445
theorem B2653975 : Blo 2095435 2653975 := bstep (se 1 (by rfl) ⟨1990481, by rfl⟩ : syracuseStep 2653975 = 3980963) B3980963
theorem B3538633 : Blo 2095435 3538633 := bstep (se 2 (by rfl) ⟨1326987, by rfl⟩ : syracuseStep 3538633 = 2653975) B2653975
theorem B4718177 : Blo 2095435 4718177 := bstep (se 2 (by rfl) ⟨1769316, by rfl⟩ : syracuseStep 4718177 = 3538633) B3538633
theorem B3145451 : Blo 2095435 3145451 := bstep (se 1 (by rfl) ⟨2359088, by rfl⟩ : syracuseStep 3145451 = 4718177) B4718177
theorem B2096967 : Blo 2095435 2096967 := bstep (se 1 (by rfl) ⟨1572725, by rfl⟩ : syracuseStep 2096967 = 3145451) B3145451
theorem B2359093 : Blo 2095435 2359093 := bbase (se 5 (by rfl) ⟨110582, by rfl⟩ : syracuseStep 2359093 = 221165) (by norm_num)
theorem B3145457 : Blo 2095435 3145457 := bstep (se 2 (by rfl) ⟨1179546, by rfl⟩ : syracuseStep 3145457 = 2359093) B2359093
theorem B2096971 : Blo 2095435 2096971 := bstep (se 1 (by rfl) ⟨1572728, by rfl⟩ : syracuseStep 2096971 = 3145457) B3145457
theorem B2653985 : Blo 2095435 2653985 := bbase (se 2 (by rfl) ⟨995244, by rfl⟩ : syracuseStep 2653985 = 1990489) (by norm_num)
theorem B7077293 : Blo 2095435 7077293 := bstep (se 3 (by rfl) ⟨1326992, by rfl⟩ : syracuseStep 7077293 = 2653985) B2653985
theorem B4718195 : Blo 2095435 4718195 := bstep (se 1 (by rfl) ⟨3538646, by rfl⟩ : syracuseStep 4718195 = 7077293) B7077293
theorem B3145463 : Blo 2095435 3145463 := bstep (se 1 (by rfl) ⟨2359097, by rfl⟩ : syracuseStep 3145463 = 4718195) B4718195
theorem B2096975 : Blo 2095435 2096975 := bstep (se 1 (by rfl) ⟨1572731, by rfl⟩ : syracuseStep 2096975 = 3145463) B3145463
theorem B3145469 : Blo 2095435 3145469 := bbase (se 3 (by rfl) ⟨589775, by rfl⟩ : syracuseStep 3145469 = 1179551) (by norm_num)
theorem B2096979 : Blo 2095435 2096979 := bstep (se 1 (by rfl) ⟨1572734, by rfl⟩ : syracuseStep 2096979 = 3145469) B3145469
theorem B4718213 : Blo 2095435 4718213 := bbase (se 4 (by rfl) ⟨442332, by rfl⟩ : syracuseStep 4718213 = 884665) (by norm_num)
theorem B3145475 : Blo 2095435 3145475 := bstep (se 1 (by rfl) ⟨2359106, by rfl⟩ : syracuseStep 3145475 = 4718213) B4718213
theorem B2096983 : Blo 2095435 2096983 := bstep (se 1 (by rfl) ⟨1572737, by rfl⟩ : syracuseStep 2096983 = 3145475) B3145475
theorem B6717941 : Blo 2095435 6717941 := bbase (se 5 (by rfl) ⟨314903, by rfl⟩ : syracuseStep 6717941 = 629807) (by norm_num)
theorem B4478627 : Blo 2095435 4478627 := bstep (se 1 (by rfl) ⟨3358970, by rfl⟩ : syracuseStep 4478627 = 6717941) B6717941
theorem B2985751 : Blo 2095435 2985751 := bstep (se 1 (by rfl) ⟨2239313, by rfl⟩ : syracuseStep 2985751 = 4478627) B4478627
theorem B3981001 : Blo 2095435 3981001 := bstep (se 2 (by rfl) ⟨1492875, by rfl⟩ : syracuseStep 3981001 = 2985751) B2985751
theorem B5308001 : Blo 2095435 5308001 := bstep (se 2 (by rfl) ⟨1990500, by rfl⟩ : syracuseStep 5308001 = 3981001) B3981001
theorem B3538667 : Blo 2095435 3538667 := bstep (se 1 (by rfl) ⟨2654000, by rfl⟩ : syracuseStep 3538667 = 5308001) B5308001
theorem B2359111 : Blo 2095435 2359111 := bstep (se 1 (by rfl) ⟨1769333, by rfl⟩ : syracuseStep 2359111 = 3538667) B3538667
theorem B3145481 : Blo 2095435 3145481 := bstep (se 2 (by rfl) ⟨1179555, by rfl⟩ : syracuseStep 3145481 = 2359111) B2359111
theorem B2096987 : Blo 2095435 2096987 := bstep (se 1 (by rfl) ⟨1572740, by rfl⟩ : syracuseStep 2096987 = 3145481) B3145481
theorem B10616021 : Blo 2095435 10616021 := bbase (se 7 (by rfl) ⟨124406, by rfl⟩ : syracuseStep 10616021 = 248813) (by norm_num)
theorem B7077347 : Blo 2095435 7077347 := bstep (se 1 (by rfl) ⟨5308010, by rfl⟩ : syracuseStep 7077347 = 10616021) B10616021
theorem B4718231 : Blo 2095435 4718231 := bstep (se 1 (by rfl) ⟨3538673, by rfl⟩ : syracuseStep 4718231 = 7077347) B7077347
theorem B3145487 : Blo 2095435 3145487 := bstep (se 1 (by rfl) ⟨2359115, by rfl⟩ : syracuseStep 3145487 = 4718231) B4718231
theorem B2096991 : Blo 2095435 2096991 := bstep (se 1 (by rfl) ⟨1572743, by rfl⟩ : syracuseStep 2096991 = 3145487) B3145487
theorem B3145493 : Blo 2095435 3145493 := bbase (se 6 (by rfl) ⟨73722, by rfl⟩ : syracuseStep 3145493 = 147445) (by norm_num)
theorem B2096995 : Blo 2095435 2096995 := bstep (se 1 (by rfl) ⟨1572746, by rfl⟩ : syracuseStep 2096995 = 3145493) B3145493
theorem B4368013 : Blo 2095435 4368013 := bbase (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) (by norm_num)
theorem B93184277 : Blo 2095435 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B248491405 : Blo 2095435 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B331321873 : Blo 2095435 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B441762497 : Blo 2095435 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B294508331 : Blo 2095435 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B196338887 : Blo 2095435 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B130892591 : Blo 2095435 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B349046909 : Blo 2095435 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B232697939 : Blo 2095435 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B620527837 : Blo 2095435 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B827370449 : Blo 2095435 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B551580299 : Blo 2095435 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B367720199 : Blo 2095435 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B245146799 : Blo 2095435 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B163431199 : Blo 2095435 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B217908265 : Blo 2095435 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B290544353 : Blo 2095435 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B193696235 : Blo 2095435 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B129130823 : Blo 2095435 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B86087215 : Blo 2095435 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B114782953 : Blo 2095435 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B153043937 : Blo 2095435 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B102029291 : Blo 2095435 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B68019527 : Blo 2095435 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B45346351 : Blo 2095435 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B60461801 : Blo 2095435 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B40307867 : Blo 2095435 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B26871911 : Blo 2095435 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B17914607 : Blo 2095435 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B11943071 : Blo 2095435 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B7962047 : Blo 2095435 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B5308031 : Blo 2095435 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B3538687 : Blo 2095435 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B4718249 : Blo 2095435 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B3145499 : Blo 2095435 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B2096999 : Blo 2095435 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B2359129 : Blo 2095435 2359129 := bbase (se 2 (by rfl) ⟨884673, by rfl⟩ : syracuseStep 2359129 = 1769347) (by norm_num)
theorem B3145505 : Blo 2095435 3145505 := bstep (se 2 (by rfl) ⟨1179564, by rfl⟩ : syracuseStep 3145505 = 2359129) B2359129
theorem B2097003 : Blo 2095435 2097003 := bstep (se 1 (by rfl) ⟨1572752, by rfl⟩ : syracuseStep 2097003 = 3145505) B3145505
theorem B4478669 : Blo 2095435 4478669 := bbase (se 3 (by rfl) ⟨839750, by rfl⟩ : syracuseStep 4478669 = 1679501) (by norm_num)
theorem B2985779 : Blo 2095435 2985779 := bstep (se 1 (by rfl) ⟨2239334, by rfl⟩ : syracuseStep 2985779 = 4478669) B4478669
theorem B7962077 : Blo 2095435 7962077 := bstep (se 3 (by rfl) ⟨1492889, by rfl⟩ : syracuseStep 7962077 = 2985779) B2985779
theorem B5308051 : Blo 2095435 5308051 := bstep (se 1 (by rfl) ⟨3981038, by rfl⟩ : syracuseStep 5308051 = 7962077) B7962077
theorem B7077401 : Blo 2095435 7077401 := bstep (se 2 (by rfl) ⟨2654025, by rfl⟩ : syracuseStep 7077401 = 5308051) B5308051
theorem B4718267 : Blo 2095435 4718267 := bstep (se 1 (by rfl) ⟨3538700, by rfl⟩ : syracuseStep 4718267 = 7077401) B7077401
theorem B3145511 : Blo 2095435 3145511 := bstep (se 1 (by rfl) ⟨2359133, by rfl⟩ : syracuseStep 3145511 = 4718267) B4718267
theorem B2097007 : Blo 2095435 2097007 := bstep (se 1 (by rfl) ⟨1572755, by rfl⟩ : syracuseStep 2097007 = 3145511) B3145511
theorem B3145517 : Blo 2095435 3145517 := bbase (se 3 (by rfl) ⟨589784, by rfl⟩ : syracuseStep 3145517 = 1179569) (by norm_num)
theorem B2097011 : Blo 2095435 2097011 := bstep (se 1 (by rfl) ⟨1572758, by rfl⟩ : syracuseStep 2097011 = 3145517) B3145517
theorem B4718285 : Blo 2095435 4718285 := bbase (se 3 (by rfl) ⟨884678, by rfl⟩ : syracuseStep 4718285 = 1769357) (by norm_num)
theorem B3145523 : Blo 2095435 3145523 := bstep (se 1 (by rfl) ⟨2359142, by rfl⟩ : syracuseStep 3145523 = 4718285) B4718285
theorem B2097015 : Blo 2095435 2097015 := bstep (se 1 (by rfl) ⟨1572761, by rfl⟩ : syracuseStep 2097015 = 3145523) B3145523
theorem B2654041 : Blo 2095435 2654041 := bbase (se 2 (by rfl) ⟨995265, by rfl⟩ : syracuseStep 2654041 = 1990531) (by norm_num)
theorem B3538721 : Blo 2095435 3538721 := bstep (se 2 (by rfl) ⟨1327020, by rfl⟩ : syracuseStep 3538721 = 2654041) B2654041
theorem B2359147 : Blo 2095435 2359147 := bstep (se 1 (by rfl) ⟨1769360, by rfl⟩ : syracuseStep 2359147 = 3538721) B3538721
theorem B3145529 : Blo 2095435 3145529 := bstep (se 2 (by rfl) ⟨1179573, by rfl⟩ : syracuseStep 3145529 = 2359147) B2359147
theorem B2097019 : Blo 2095435 2097019 := bstep (se 1 (by rfl) ⟨1572764, by rfl⟩ : syracuseStep 2097019 = 3145529) B3145529
theorem B5038541 : Blo 2095435 5038541 := bbase (se 3 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 5038541 = 1889453) (by norm_num)
theorem B3359027 : Blo 2095435 3359027 := bstep (se 1 (by rfl) ⟨2519270, by rfl⟩ : syracuseStep 3359027 = 5038541) B5038541
theorem B8957405 : Blo 2095435 8957405 := bstep (se 3 (by rfl) ⟨1679513, by rfl⟩ : syracuseStep 8957405 = 3359027) B3359027
theorem B23886413 : Blo 2095435 23886413 := bstep (se 3 (by rfl) ⟨4478702, by rfl⟩ : syracuseStep 23886413 = 8957405) B8957405
theorem B15924275 : Blo 2095435 15924275 := bstep (se 1 (by rfl) ⟨11943206, by rfl⟩ : syracuseStep 15924275 = 23886413) B23886413
theorem B10616183 : Blo 2095435 10616183 := bstep (se 1 (by rfl) ⟨7962137, by rfl⟩ : syracuseStep 10616183 = 15924275) B15924275
theorem B7077455 : Blo 2095435 7077455 := bstep (se 1 (by rfl) ⟨5308091, by rfl⟩ : syracuseStep 7077455 = 10616183) B10616183
theorem B4718303 : Blo 2095435 4718303 := bstep (se 1 (by rfl) ⟨3538727, by rfl⟩ : syracuseStep 4718303 = 7077455) B7077455
theorem B3145535 : Blo 2095435 3145535 := bstep (se 1 (by rfl) ⟨2359151, by rfl⟩ : syracuseStep 3145535 = 4718303) B4718303
theorem B2097023 : Blo 2095435 2097023 := bstep (se 1 (by rfl) ⟨1572767, by rfl⟩ : syracuseStep 2097023 = 3145535) B3145535
theorem B3145541 : Blo 2095435 3145541 := bbase (se 4 (by rfl) ⟨294894, by rfl⟩ : syracuseStep 3145541 = 589789) (by norm_num)
theorem B2097027 : Blo 2095435 2097027 := bstep (se 1 (by rfl) ⟨1572770, by rfl⟩ : syracuseStep 2097027 = 3145541) B3145541
theorem B3538741 : Blo 2095435 3538741 := bbase (se 5 (by rfl) ⟨165878, by rfl⟩ : syracuseStep 3538741 = 331757) (by norm_num)
theorem B4718321 : Blo 2095435 4718321 := bstep (se 2 (by rfl) ⟨1769370, by rfl⟩ : syracuseStep 4718321 = 3538741) B3538741
theorem B3145547 : Blo 2095435 3145547 := bstep (se 1 (by rfl) ⟨2359160, by rfl⟩ : syracuseStep 3145547 = 4718321) B4718321
theorem B2097031 : Blo 2095435 2097031 := bstep (se 1 (by rfl) ⟨1572773, by rfl⟩ : syracuseStep 2097031 = 3145547) B3145547
theorem B2359165 : Blo 2095435 2359165 := bbase (se 3 (by rfl) ⟨442343, by rfl⟩ : syracuseStep 2359165 = 884687) (by norm_num)
theorem B3145553 : Blo 2095435 3145553 := bstep (se 2 (by rfl) ⟨1179582, by rfl⟩ : syracuseStep 3145553 = 2359165) B2359165
theorem B2097035 : Blo 2095435 2097035 := bstep (se 1 (by rfl) ⟨1572776, by rfl⟩ : syracuseStep 2097035 = 3145553) B3145553
theorem B7077509 : Blo 2095435 7077509 := bbase (se 4 (by rfl) ⟨663516, by rfl⟩ : syracuseStep 7077509 = 1327033) (by norm_num)
theorem B4718339 : Blo 2095435 4718339 := bstep (se 1 (by rfl) ⟨3538754, by rfl⟩ : syracuseStep 4718339 = 7077509) B7077509
theorem B3145559 : Blo 2095435 3145559 := bstep (se 1 (by rfl) ⟨2359169, by rfl⟩ : syracuseStep 3145559 = 4718339) B4718339
theorem B2097039 : Blo 2095435 2097039 := bstep (se 1 (by rfl) ⟨1572779, by rfl⟩ : syracuseStep 2097039 = 3145559) B3145559
theorem B3145565 : Blo 2095435 3145565 := bbase (se 3 (by rfl) ⟨589793, by rfl⟩ : syracuseStep 3145565 = 1179587) (by norm_num)
theorem B2097043 : Blo 2095435 2097043 := bstep (se 1 (by rfl) ⟨1572782, by rfl⟩ : syracuseStep 2097043 = 3145565) B3145565
theorem B4718357 : Blo 2095435 4718357 := bbase (se 6 (by rfl) ⟨110586, by rfl⟩ : syracuseStep 4718357 = 221173) (by norm_num)
theorem B3145571 : Blo 2095435 3145571 := bstep (se 1 (by rfl) ⟨2359178, by rfl⟩ : syracuseStep 3145571 = 4718357) B4718357
theorem B2097047 : Blo 2095435 2097047 := bstep (se 1 (by rfl) ⟨1572785, by rfl⟩ : syracuseStep 2097047 = 3145571) B3145571
theorem B7962245 : Blo 2095435 7962245 := bbase (se 4 (by rfl) ⟨746460, by rfl⟩ : syracuseStep 7962245 = 1492921) (by norm_num)
theorem B5308163 : Blo 2095435 5308163 := bstep (se 1 (by rfl) ⟨3981122, by rfl⟩ : syracuseStep 5308163 = 7962245) B7962245
theorem B3538775 : Blo 2095435 3538775 := bstep (se 1 (by rfl) ⟨2654081, by rfl⟩ : syracuseStep 3538775 = 5308163) B5308163
theorem B2359183 : Blo 2095435 2359183 := bstep (se 1 (by rfl) ⟨1769387, by rfl⟩ : syracuseStep 2359183 = 3538775) B3538775
theorem B3145577 : Blo 2095435 3145577 := bstep (se 2 (by rfl) ⟨1179591, by rfl⟩ : syracuseStep 3145577 = 2359183) B2359183
theorem B2097051 : Blo 2095435 2097051 := bstep (se 1 (by rfl) ⟨1572788, by rfl⟩ : syracuseStep 2097051 = 3145577) B3145577
theorem B2519309 : Blo 2095435 2519309 := bbase (se 3 (by rfl) ⟨472370, by rfl⟩ : syracuseStep 2519309 = 944741) (by norm_num)
theorem B6718157 : Blo 2095435 6718157 := bstep (se 3 (by rfl) ⟨1259654, by rfl⟩ : syracuseStep 6718157 = 2519309) B2519309
theorem B4478771 : Blo 2095435 4478771 := bstep (se 1 (by rfl) ⟨3359078, by rfl⟩ : syracuseStep 4478771 = 6718157) B6718157
theorem B11943389 : Blo 2095435 11943389 := bstep (se 3 (by rfl) ⟨2239385, by rfl⟩ : syracuseStep 11943389 = 4478771) B4478771
theorem B7962259 : Blo 2095435 7962259 := bstep (se 1 (by rfl) ⟨5971694, by rfl⟩ : syracuseStep 7962259 = 11943389) B11943389
theorem B10616345 : Blo 2095435 10616345 := bstep (se 2 (by rfl) ⟨3981129, by rfl⟩ : syracuseStep 10616345 = 7962259) B7962259
theorem B7077563 : Blo 2095435 7077563 := bstep (se 1 (by rfl) ⟨5308172, by rfl⟩ : syracuseStep 7077563 = 10616345) B10616345
theorem B4718375 : Blo 2095435 4718375 := bstep (se 1 (by rfl) ⟨3538781, by rfl⟩ : syracuseStep 4718375 = 7077563) B7077563
theorem B3145583 : Blo 2095435 3145583 := bstep (se 1 (by rfl) ⟨2359187, by rfl⟩ : syracuseStep 3145583 = 4718375) B4718375
theorem B2097055 : Blo 2095435 2097055 := bstep (se 1 (by rfl) ⟨1572791, by rfl⟩ : syracuseStep 2097055 = 3145583) B3145583
theorem B3145589 : Blo 2095435 3145589 := bbase (se 5 (by rfl) ⟨147449, by rfl⟩ : syracuseStep 3145589 = 294899) (by norm_num)
theorem B2097059 : Blo 2095435 2097059 := bstep (se 1 (by rfl) ⟨1572794, by rfl⟩ : syracuseStep 2097059 = 3145589) B3145589
theorem B4478789 : Blo 2095435 4478789 := bbase (se 4 (by rfl) ⟨419886, by rfl⟩ : syracuseStep 4478789 = 839773) (by norm_num)
theorem B2985859 : Blo 2095435 2985859 := bstep (se 1 (by rfl) ⟨2239394, by rfl⟩ : syracuseStep 2985859 = 4478789) B4478789
theorem B3981145 : Blo 2095435 3981145 := bstep (se 2 (by rfl) ⟨1492929, by rfl⟩ : syracuseStep 3981145 = 2985859) B2985859
theorem B5308193 : Blo 2095435 5308193 := bstep (se 2 (by rfl) ⟨1990572, by rfl⟩ : syracuseStep 5308193 = 3981145) B3981145
theorem B3538795 : Blo 2095435 3538795 := bstep (se 1 (by rfl) ⟨2654096, by rfl⟩ : syracuseStep 3538795 = 5308193) B5308193
theorem B4718393 : Blo 2095435 4718393 := bstep (se 2 (by rfl) ⟨1769397, by rfl⟩ : syracuseStep 4718393 = 3538795) B3538795
theorem B3145595 : Blo 2095435 3145595 := bstep (se 1 (by rfl) ⟨2359196, by rfl⟩ : syracuseStep 3145595 = 4718393) B4718393
theorem B2097063 : Blo 2095435 2097063 := bstep (se 1 (by rfl) ⟨1572797, by rfl⟩ : syracuseStep 2097063 = 3145595) B3145595
theorem B2359201 : Blo 2095435 2359201 := bbase (se 2 (by rfl) ⟨884700, by rfl⟩ : syracuseStep 2359201 = 1769401) (by norm_num)
theorem B3145601 : Blo 2095435 3145601 := bstep (se 2 (by rfl) ⟨1179600, by rfl⟩ : syracuseStep 3145601 = 2359201) B2359201
theorem B2097067 : Blo 2095435 2097067 := bstep (se 1 (by rfl) ⟨1572800, by rfl⟩ : syracuseStep 2097067 = 3145601) B3145601
theorem B5308213 : Blo 2095435 5308213 := bbase (se 5 (by rfl) ⟨248822, by rfl⟩ : syracuseStep 5308213 = 497645) (by norm_num)
theorem B7077617 : Blo 2095435 7077617 := bstep (se 2 (by rfl) ⟨2654106, by rfl⟩ : syracuseStep 7077617 = 5308213) B5308213
theorem B4718411 : Blo 2095435 4718411 := bstep (se 1 (by rfl) ⟨3538808, by rfl⟩ : syracuseStep 4718411 = 7077617) B7077617
theorem B3145607 : Blo 2095435 3145607 := bstep (se 1 (by rfl) ⟨2359205, by rfl⟩ : syracuseStep 3145607 = 4718411) B4718411
theorem B2097071 : Blo 2095435 2097071 := bstep (se 1 (by rfl) ⟨1572803, by rfl⟩ : syracuseStep 2097071 = 3145607) B3145607
theorem B3145613 : Blo 2095435 3145613 := bbase (se 3 (by rfl) ⟨589802, by rfl⟩ : syracuseStep 3145613 = 1179605) (by norm_num)
theorem B2097075 : Blo 2095435 2097075 := bstep (se 1 (by rfl) ⟨1572806, by rfl⟩ : syracuseStep 2097075 = 3145613) B3145613
theorem B4718429 : Blo 2095435 4718429 := bbase (se 3 (by rfl) ⟨884705, by rfl⟩ : syracuseStep 4718429 = 1769411) (by norm_num)
theorem B3145619 : Blo 2095435 3145619 := bstep (se 1 (by rfl) ⟨2359214, by rfl⟩ : syracuseStep 3145619 = 4718429) B4718429
theorem B2097079 : Blo 2095435 2097079 := bstep (se 1 (by rfl) ⟨1572809, by rfl⟩ : syracuseStep 2097079 = 3145619) B3145619
theorem B3538829 : Blo 2095435 3538829 := bbase (se 3 (by rfl) ⟨663530, by rfl⟩ : syracuseStep 3538829 = 1327061) (by norm_num)
theorem B2359219 : Blo 2095435 2359219 := bstep (se 1 (by rfl) ⟨1769414, by rfl⟩ : syracuseStep 2359219 = 3538829) B3538829
theorem B3145625 : Blo 2095435 3145625 := bstep (se 2 (by rfl) ⟨1179609, by rfl⟩ : syracuseStep 3145625 = 2359219) B2359219
theorem B2097083 : Blo 2095435 2097083 := bstep (se 1 (by rfl) ⟨1572812, by rfl⟩ : syracuseStep 2097083 = 3145625) B3145625
theorem B3779021 : Blo 2095435 3779021 := bbase (se 3 (by rfl) ⟨708566, by rfl⟩ : syracuseStep 3779021 = 1417133) (by norm_num)
theorem B10077389 : Blo 2095435 10077389 := bstep (se 3 (by rfl) ⟨1889510, by rfl⟩ : syracuseStep 10077389 = 3779021) B3779021
theorem B6718259 : Blo 2095435 6718259 := bstep (se 1 (by rfl) ⟨5038694, by rfl⟩ : syracuseStep 6718259 = 10077389) B10077389
theorem B17915357 : Blo 2095435 17915357 := bstep (se 3 (by rfl) ⟨3359129, by rfl⟩ : syracuseStep 17915357 = 6718259) B6718259
theorem B11943571 : Blo 2095435 11943571 := bstep (se 1 (by rfl) ⟨8957678, by rfl⟩ : syracuseStep 11943571 = 17915357) B17915357
theorem B15924761 : Blo 2095435 15924761 := bstep (se 2 (by rfl) ⟨5971785, by rfl⟩ : syracuseStep 15924761 = 11943571) B11943571
theorem B10616507 : Blo 2095435 10616507 := bstep (se 1 (by rfl) ⟨7962380, by rfl⟩ : syracuseStep 10616507 = 15924761) B15924761
theorem B7077671 : Blo 2095435 7077671 := bstep (se 1 (by rfl) ⟨5308253, by rfl⟩ : syracuseStep 7077671 = 10616507) B10616507
theorem B4718447 : Blo 2095435 4718447 := bstep (se 1 (by rfl) ⟨3538835, by rfl⟩ : syracuseStep 4718447 = 7077671) B7077671
theorem B3145631 : Blo 2095435 3145631 := bstep (se 1 (by rfl) ⟨2359223, by rfl⟩ : syracuseStep 3145631 = 4718447) B4718447
theorem B2097087 : Blo 2095435 2097087 := bstep (se 1 (by rfl) ⟨1572815, by rfl⟩ : syracuseStep 2097087 = 3145631) B3145631
theorem B3145637 : Blo 2095435 3145637 := bbase (se 4 (by rfl) ⟨294903, by rfl⟩ : syracuseStep 3145637 = 589807) (by norm_num)
theorem B2097091 : Blo 2095435 2097091 := bstep (se 1 (by rfl) ⟨1572818, by rfl⟩ : syracuseStep 2097091 = 3145637) B3145637
theorem B2654137 : Blo 2095435 2654137 := bbase (se 2 (by rfl) ⟨995301, by rfl⟩ : syracuseStep 2654137 = 1990603) (by norm_num)
theorem B3538849 : Blo 2095435 3538849 := bstep (se 2 (by rfl) ⟨1327068, by rfl⟩ : syracuseStep 3538849 = 2654137) B2654137
theorem B4718465 : Blo 2095435 4718465 := bstep (se 2 (by rfl) ⟨1769424, by rfl⟩ : syracuseStep 4718465 = 3538849) B3538849
theorem B3145643 : Blo 2095435 3145643 := bstep (se 1 (by rfl) ⟨2359232, by rfl⟩ : syracuseStep 3145643 = 4718465) B4718465
theorem B2097095 : Blo 2095435 2097095 := bstep (se 1 (by rfl) ⟨1572821, by rfl⟩ : syracuseStep 2097095 = 3145643) B3145643
theorem B2359237 : Blo 2095435 2359237 := bbase (se 4 (by rfl) ⟨221178, by rfl⟩ : syracuseStep 2359237 = 442357) (by norm_num)
theorem B3145649 : Blo 2095435 3145649 := bstep (se 2 (by rfl) ⟨1179618, by rfl⟩ : syracuseStep 3145649 = 2359237) B2359237
theorem B2097099 : Blo 2095435 2097099 := bstep (se 1 (by rfl) ⟨1572824, by rfl⟩ : syracuseStep 2097099 = 3145649) B3145649
theorem B3981221 : Blo 2095435 3981221 := bbase (se 4 (by rfl) ⟨373239, by rfl⟩ : syracuseStep 3981221 = 746479) (by norm_num)
theorem B2654147 : Blo 2095435 2654147 := bstep (se 1 (by rfl) ⟨1990610, by rfl⟩ : syracuseStep 2654147 = 3981221) B3981221
theorem B7077725 : Blo 2095435 7077725 := bstep (se 3 (by rfl) ⟨1327073, by rfl⟩ : syracuseStep 7077725 = 2654147) B2654147
theorem B4718483 : Blo 2095435 4718483 := bstep (se 1 (by rfl) ⟨3538862, by rfl⟩ : syracuseStep 4718483 = 7077725) B7077725
theorem B3145655 : Blo 2095435 3145655 := bstep (se 1 (by rfl) ⟨2359241, by rfl⟩ : syracuseStep 3145655 = 4718483) B4718483
theorem B2097103 : Blo 2095435 2097103 := bstep (se 1 (by rfl) ⟨1572827, by rfl⟩ : syracuseStep 2097103 = 3145655) B3145655
theorem B3145661 : Blo 2095435 3145661 := bbase (se 3 (by rfl) ⟨589811, by rfl⟩ : syracuseStep 3145661 = 1179623) (by norm_num)
theorem B2097107 : Blo 2095435 2097107 := bstep (se 1 (by rfl) ⟨1572830, by rfl⟩ : syracuseStep 2097107 = 3145661) B3145661
theorem B4718501 : Blo 2095435 4718501 := bbase (se 4 (by rfl) ⟨442359, by rfl⟩ : syracuseStep 4718501 = 884719) (by norm_num)
theorem B3145667 : Blo 2095435 3145667 := bstep (se 1 (by rfl) ⟨2359250, by rfl⟩ : syracuseStep 3145667 = 4718501) B4718501
theorem B2097111 : Blo 2095435 2097111 := bstep (se 1 (by rfl) ⟨1572833, by rfl⟩ : syracuseStep 2097111 = 3145667) B3145667
theorem B5308325 : Blo 2095435 5308325 := bbase (se 4 (by rfl) ⟨497655, by rfl⟩ : syracuseStep 5308325 = 995311) (by norm_num)
theorem B3538883 : Blo 2095435 3538883 := bstep (se 1 (by rfl) ⟨2654162, by rfl⟩ : syracuseStep 3538883 = 5308325) B5308325
theorem B2359255 : Blo 2095435 2359255 := bstep (se 1 (by rfl) ⟨1769441, by rfl⟩ : syracuseStep 2359255 = 3538883) B3538883
theorem B3145673 : Blo 2095435 3145673 := bstep (se 2 (by rfl) ⟨1179627, by rfl⟩ : syracuseStep 3145673 = 2359255) B2359255
theorem B2097115 : Blo 2095435 2097115 := bstep (se 1 (by rfl) ⟨1572836, by rfl⟩ : syracuseStep 2097115 = 3145673) B3145673
theorem B5971877 : Blo 2095435 5971877 := bbase (se 4 (by rfl) ⟨559863, by rfl⟩ : syracuseStep 5971877 = 1119727) (by norm_num)
theorem B3981251 : Blo 2095435 3981251 := bstep (se 1 (by rfl) ⟨2985938, by rfl⟩ : syracuseStep 3981251 = 5971877) B5971877
theorem B10616669 : Blo 2095435 10616669 := bstep (se 3 (by rfl) ⟨1990625, by rfl⟩ : syracuseStep 10616669 = 3981251) B3981251
theorem B7077779 : Blo 2095435 7077779 := bstep (se 1 (by rfl) ⟨5308334, by rfl⟩ : syracuseStep 7077779 = 10616669) B10616669
theorem B4718519 : Blo 2095435 4718519 := bstep (se 1 (by rfl) ⟨3538889, by rfl⟩ : syracuseStep 4718519 = 7077779) B7077779
theorem B3145679 : Blo 2095435 3145679 := bstep (se 1 (by rfl) ⟨2359259, by rfl⟩ : syracuseStep 3145679 = 4718519) B4718519
theorem B2097119 : Blo 2095435 2097119 := bstep (se 1 (by rfl) ⟨1572839, by rfl⟩ : syracuseStep 2097119 = 3145679) B3145679
theorem B3145685 : Blo 2095435 3145685 := bbase (se 7 (by rfl) ⟨36863, by rfl⟩ : syracuseStep 3145685 = 73727) (by norm_num)
theorem B2097123 : Blo 2095435 2097123 := bstep (se 1 (by rfl) ⟨1572842, by rfl⟩ : syracuseStep 2097123 = 3145685) B3145685
theorem B7962533 : Blo 2095435 7962533 := bbase (se 4 (by rfl) ⟨746487, by rfl⟩ : syracuseStep 7962533 = 1492975) (by norm_num)
theorem B5308355 : Blo 2095435 5308355 := bstep (se 1 (by rfl) ⟨3981266, by rfl⟩ : syracuseStep 5308355 = 7962533) B7962533
theorem B3538903 : Blo 2095435 3538903 := bstep (se 1 (by rfl) ⟨2654177, by rfl⟩ : syracuseStep 3538903 = 5308355) B5308355
theorem B4718537 : Blo 2095435 4718537 := bstep (se 2 (by rfl) ⟨1769451, by rfl⟩ : syracuseStep 4718537 = 3538903) B3538903
theorem B3145691 : Blo 2095435 3145691 := bstep (se 1 (by rfl) ⟨2359268, by rfl⟩ : syracuseStep 3145691 = 4718537) B4718537
theorem B2097127 : Blo 2095435 2097127 := bstep (se 1 (by rfl) ⟨1572845, by rfl⟩ : syracuseStep 2097127 = 3145691) B3145691
theorem B2359273 : Blo 2095435 2359273 := bbase (se 2 (by rfl) ⟨884727, by rfl⟩ : syracuseStep 2359273 = 1769455) (by norm_num)
theorem B3145697 : Blo 2095435 3145697 := bstep (se 2 (by rfl) ⟨1179636, by rfl⟩ : syracuseStep 3145697 = 2359273) B2359273
theorem B2097131 : Blo 2095435 2097131 := bstep (se 1 (by rfl) ⟨1572848, by rfl⟩ : syracuseStep 2097131 = 3145697) B3145697
theorem B10761605 : Blo 2095435 10761605 := bbase (se 4 (by rfl) ⟨1008900, by rfl⟩ : syracuseStep 10761605 = 2017801) (by norm_num)
theorem B7174403 : Blo 2095435 7174403 := bstep (se 1 (by rfl) ⟨5380802, by rfl⟩ : syracuseStep 7174403 = 10761605) B10761605
theorem B4782935 : Blo 2095435 4782935 := bstep (se 1 (by rfl) ⟨3587201, by rfl⟩ : syracuseStep 4782935 = 7174403) B7174403
theorem B12754493 : Blo 2095435 12754493 := bstep (se 3 (by rfl) ⟨2391467, by rfl⟩ : syracuseStep 12754493 = 4782935) B4782935
theorem B8502995 : Blo 2095435 8502995 := bstep (se 1 (by rfl) ⟨6377246, by rfl⟩ : syracuseStep 8502995 = 12754493) B12754493
theorem B5668663 : Blo 2095435 5668663 := bstep (se 1 (by rfl) ⟨4251497, by rfl⟩ : syracuseStep 5668663 = 8502995) B8502995
theorem B7558217 : Blo 2095435 7558217 := bstep (se 2 (by rfl) ⟨2834331, by rfl⟩ : syracuseStep 7558217 = 5668663) B5668663
theorem B5038811 : Blo 2095435 5038811 := bstep (se 1 (by rfl) ⟨3779108, by rfl⟩ : syracuseStep 5038811 = 7558217) B7558217
theorem B3359207 : Blo 2095435 3359207 := bstep (se 1 (by rfl) ⟨2519405, by rfl⟩ : syracuseStep 3359207 = 5038811) B5038811
theorem B2239471 : Blo 2095435 2239471 := bstep (se 1 (by rfl) ⟨1679603, by rfl⟩ : syracuseStep 2239471 = 3359207) B3359207
theorem B11943845 : Blo 2095435 11943845 := bstep (se 4 (by rfl) ⟨1119735, by rfl⟩ : syracuseStep 11943845 = 2239471) B2239471
theorem B7962563 : Blo 2095435 7962563 := bstep (se 1 (by rfl) ⟨5971922, by rfl⟩ : syracuseStep 7962563 = 11943845) B11943845
theorem B5308375 : Blo 2095435 5308375 := bstep (se 1 (by rfl) ⟨3981281, by rfl⟩ : syracuseStep 5308375 = 7962563) B7962563
theorem B7077833 : Blo 2095435 7077833 := bstep (se 2 (by rfl) ⟨2654187, by rfl⟩ : syracuseStep 7077833 = 5308375) B5308375
theorem B4718555 : Blo 2095435 4718555 := bstep (se 1 (by rfl) ⟨3538916, by rfl⟩ : syracuseStep 4718555 = 7077833) B7077833
theorem B3145703 : Blo 2095435 3145703 := bstep (se 1 (by rfl) ⟨2359277, by rfl⟩ : syracuseStep 3145703 = 4718555) B4718555
theorem B2097135 : Blo 2095435 2097135 := bstep (se 1 (by rfl) ⟨1572851, by rfl⟩ : syracuseStep 2097135 = 3145703) B3145703
theorem B3145709 : Blo 2095435 3145709 := bbase (se 3 (by rfl) ⟨589820, by rfl⟩ : syracuseStep 3145709 = 1179641) (by norm_num)
theorem B2097139 : Blo 2095435 2097139 := bstep (se 1 (by rfl) ⟨1572854, by rfl⟩ : syracuseStep 2097139 = 3145709) B3145709
theorem B4718573 : Blo 2095435 4718573 := bbase (se 3 (by rfl) ⟨884732, by rfl⟩ : syracuseStep 4718573 = 1769465) (by norm_num)
theorem B3145715 : Blo 2095435 3145715 := bstep (se 1 (by rfl) ⟨2359286, by rfl⟩ : syracuseStep 3145715 = 4718573) B4718573
theorem B2097143 : Blo 2095435 2097143 := bstep (se 1 (by rfl) ⟨1572857, by rfl⟩ : syracuseStep 2097143 = 3145715) B3145715
theorem B6377285 : Blo 2095435 6377285 := bbase (se 4 (by rfl) ⟨597870, by rfl⟩ : syracuseStep 6377285 = 1195741) (by norm_num)
theorem B4251523 : Blo 2095435 4251523 := bstep (se 1 (by rfl) ⟨3188642, by rfl⟩ : syracuseStep 4251523 = 6377285) B6377285
theorem B5668697 : Blo 2095435 5668697 := bstep (se 2 (by rfl) ⟨2125761, by rfl⟩ : syracuseStep 5668697 = 4251523) B4251523
theorem B3779131 : Blo 2095435 3779131 := bstep (se 1 (by rfl) ⟨2834348, by rfl⟩ : syracuseStep 3779131 = 5668697) B5668697
theorem B5038841 : Blo 2095435 5038841 := bstep (se 2 (by rfl) ⟨1889565, by rfl⟩ : syracuseStep 5038841 = 3779131) B3779131
theorem B3359227 : Blo 2095435 3359227 := bstep (se 1 (by rfl) ⟨2519420, by rfl⟩ : syracuseStep 3359227 = 5038841) B5038841
theorem B4478969 : Blo 2095435 4478969 := bstep (se 2 (by rfl) ⟨1679613, by rfl⟩ : syracuseStep 4478969 = 3359227) B3359227
theorem B2985979 : Blo 2095435 2985979 := bstep (se 1 (by rfl) ⟨2239484, by rfl⟩ : syracuseStep 2985979 = 4478969) B4478969
theorem B3981305 : Blo 2095435 3981305 := bstep (se 2 (by rfl) ⟨1492989, by rfl⟩ : syracuseStep 3981305 = 2985979) B2985979
theorem B2654203 : Blo 2095435 2654203 := bstep (se 1 (by rfl) ⟨1990652, by rfl⟩ : syracuseStep 2654203 = 3981305) B3981305
theorem B3538937 : Blo 2095435 3538937 := bstep (se 2 (by rfl) ⟨1327101, by rfl⟩ : syracuseStep 3538937 = 2654203) B2654203
theorem B2359291 : Blo 2095435 2359291 := bstep (se 1 (by rfl) ⟨1769468, by rfl⟩ : syracuseStep 2359291 = 3538937) B3538937
theorem B3145721 : Blo 2095435 3145721 := bstep (se 2 (by rfl) ⟨1179645, by rfl⟩ : syracuseStep 3145721 = 2359291) B2359291
theorem B2097147 : Blo 2095435 2097147 := bstep (se 1 (by rfl) ⟨1572860, by rfl⟩ : syracuseStep 2097147 = 3145721) B3145721
theorem B7371557 : Blo 2095435 7371557 := bbase (se 4 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 7371557 = 1382167) (by norm_num)
theorem B4914371 : Blo 2095435 4914371 := bstep (se 1 (by rfl) ⟨3685778, by rfl⟩ : syracuseStep 4914371 = 7371557) B7371557
theorem B13104989 : Blo 2095435 13104989 := bstep (se 3 (by rfl) ⟨2457185, by rfl⟩ : syracuseStep 13104989 = 4914371) B4914371
theorem B8736659 : Blo 2095435 8736659 := bstep (se 1 (by rfl) ⟨6552494, by rfl⟩ : syracuseStep 8736659 = 13104989) B13104989
theorem B5824439 : Blo 2095435 5824439 := bstep (se 1 (by rfl) ⟨4368329, by rfl⟩ : syracuseStep 5824439 = 8736659) B8736659
theorem B3882959 : Blo 2095435 3882959 := bstep (se 1 (by rfl) ⟨2912219, by rfl⟩ : syracuseStep 3882959 = 5824439) B5824439
theorem B165672917 : Blo 2095435 165672917 := bstep (se 7 (by rfl) ⟨1941479, by rfl⟩ : syracuseStep 165672917 = 3882959) B3882959
theorem B110448611 : Blo 2095435 110448611 := bstep (se 1 (by rfl) ⟨82836458, by rfl⟩ : syracuseStep 110448611 = 165672917) B165672917
theorem B73632407 : Blo 2095435 73632407 := bstep (se 1 (by rfl) ⟨55224305, by rfl⟩ : syracuseStep 73632407 = 110448611) B110448611
theorem B785412341 : Blo 2095435 785412341 := bstep (se 5 (by rfl) ⟨36816203, by rfl⟩ : syracuseStep 785412341 = 73632407) B73632407
theorem B523608227 : Blo 2095435 523608227 := bstep (se 1 (by rfl) ⟨392706170, by rfl⟩ : syracuseStep 523608227 = 785412341) B785412341
theorem B349072151 : Blo 2095435 349072151 := bstep (se 1 (by rfl) ⟨261804113, by rfl⟩ : syracuseStep 349072151 = 523608227) B523608227
theorem B930859069 : Blo 2095435 930859069 := bstep (se 3 (by rfl) ⟨174536075, by rfl⟩ : syracuseStep 930859069 = 349072151) B349072151
theorem B1241145425 : Blo 2095435 1241145425 := bstep (se 2 (by rfl) ⟨465429534, by rfl⟩ : syracuseStep 1241145425 = 930859069) B930859069
theorem B827430283 : Blo 2095435 827430283 := bstep (se 1 (by rfl) ⟨620572712, by rfl⟩ : syracuseStep 827430283 = 1241145425) B1241145425
theorem B1103240377 : Blo 2095435 1103240377 := bstep (se 2 (by rfl) ⟨413715141, by rfl⟩ : syracuseStep 1103240377 = 827430283) B827430283
theorem B5883948677 : Blo 2095435 5883948677 := bstep (se 4 (by rfl) ⟨551620188, by rfl⟩ : syracuseStep 5883948677 = 1103240377) B1103240377
theorem B3922632451 : Blo 2095435 3922632451 := bstep (se 1 (by rfl) ⟨2941974338, by rfl⟩ : syracuseStep 3922632451 = 5883948677) B5883948677
theorem B5230176601 : Blo 2095435 5230176601 := bstep (se 2 (by rfl) ⟨1961316225, by rfl⟩ : syracuseStep 5230176601 = 3922632451) B3922632451
theorem B6973568801 : Blo 2095435 6973568801 := bstep (se 2 (by rfl) ⟨2615088300, by rfl⟩ : syracuseStep 6973568801 = 5230176601) B5230176601
theorem B4649045867 : Blo 2095435 4649045867 := bstep (se 1 (by rfl) ⟨3486784400, by rfl⟩ : syracuseStep 4649045867 = 6973568801) B6973568801
theorem B3099363911 : Blo 2095435 3099363911 := bstep (se 1 (by rfl) ⟨2324522933, by rfl⟩ : syracuseStep 3099363911 = 4649045867) B4649045867
theorem B2066242607 : Blo 2095435 2066242607 := bstep (se 1 (by rfl) ⟨1549681955, by rfl⟩ : syracuseStep 2066242607 = 3099363911) B3099363911
theorem B1377495071 : Blo 2095435 1377495071 := bstep (se 1 (by rfl) ⟨1033121303, by rfl⟩ : syracuseStep 1377495071 = 2066242607) B2066242607
theorem B918330047 : Blo 2095435 918330047 := bstep (se 1 (by rfl) ⟨688747535, by rfl⟩ : syracuseStep 918330047 = 1377495071) B1377495071
theorem B612220031 : Blo 2095435 612220031 := bstep (se 1 (by rfl) ⟨459165023, by rfl⟩ : syracuseStep 612220031 = 918330047) B918330047
theorem B408146687 : Blo 2095435 408146687 := bstep (se 1 (by rfl) ⟨306110015, by rfl⟩ : syracuseStep 408146687 = 612220031) B612220031
theorem B272097791 : Blo 2095435 272097791 := bstep (se 1 (by rfl) ⟨204073343, by rfl⟩ : syracuseStep 272097791 = 408146687) B408146687
theorem B181398527 : Blo 2095435 181398527 := bstep (se 1 (by rfl) ⟨136048895, by rfl⟩ : syracuseStep 181398527 = 272097791) B272097791
theorem B120932351 : Blo 2095435 120932351 := bstep (se 1 (by rfl) ⟨90699263, by rfl⟩ : syracuseStep 120932351 = 181398527) B181398527
theorem B80621567 : Blo 2095435 80621567 := bstep (se 1 (by rfl) ⟨60466175, by rfl⟩ : syracuseStep 80621567 = 120932351) B120932351
theorem B53747711 : Blo 2095435 53747711 := bstep (se 1 (by rfl) ⟨40310783, by rfl⟩ : syracuseStep 53747711 = 80621567) B80621567
theorem B35831807 : Blo 2095435 35831807 := bstep (se 1 (by rfl) ⟨26873855, by rfl⟩ : syracuseStep 35831807 = 53747711) B53747711
theorem B23887871 : Blo 2095435 23887871 := bstep (se 1 (by rfl) ⟨17915903, by rfl⟩ : syracuseStep 23887871 = 35831807) B35831807
theorem B15925247 : Blo 2095435 15925247 := bstep (se 1 (by rfl) ⟨11943935, by rfl⟩ : syracuseStep 15925247 = 23887871) B23887871
theorem B10616831 : Blo 2095435 10616831 := bstep (se 1 (by rfl) ⟨7962623, by rfl⟩ : syracuseStep 10616831 = 15925247) B15925247
theorem B7077887 : Blo 2095435 7077887 := bstep (se 1 (by rfl) ⟨5308415, by rfl⟩ : syracuseStep 7077887 = 10616831) B10616831
theorem B4718591 : Blo 2095435 4718591 := bstep (se 1 (by rfl) ⟨3538943, by rfl⟩ : syracuseStep 4718591 = 7077887) B7077887
theorem B3145727 : Blo 2095435 3145727 := bstep (se 1 (by rfl) ⟨2359295, by rfl⟩ : syracuseStep 3145727 = 4718591) B4718591
theorem B2097151 : Blo 2095435 2097151 := bstep (se 1 (by rfl) ⟨1572863, by rfl⟩ : syracuseStep 2097151 = 3145727) B3145727
theorem B3145733 : Blo 2095435 3145733 := bbase (se 4 (by rfl) ⟨294912, by rfl⟩ : syracuseStep 3145733 = 589825) (by norm_num)
theorem B2097155 : Blo 2095435 2097155 := bstep (se 1 (by rfl) ⟨1572866, by rfl⟩ : syracuseStep 2097155 = 3145733) B3145733
theorem B3538957 : Blo 2095435 3538957 := bbase (se 3 (by rfl) ⟨663554, by rfl⟩ : syracuseStep 3538957 = 1327109) (by norm_num)
theorem B4718609 : Blo 2095435 4718609 := bstep (se 2 (by rfl) ⟨1769478, by rfl⟩ : syracuseStep 4718609 = 3538957) B3538957
theorem B3145739 : Blo 2095435 3145739 := bstep (se 1 (by rfl) ⟨2359304, by rfl⟩ : syracuseStep 3145739 = 4718609) B4718609
theorem B2097159 : Blo 2095435 2097159 := bstep (se 1 (by rfl) ⟨1572869, by rfl⟩ : syracuseStep 2097159 = 3145739) B3145739
theorem B2359309 : Blo 2095435 2359309 := bbase (se 3 (by rfl) ⟨442370, by rfl⟩ : syracuseStep 2359309 = 884741) (by norm_num)
theorem B3145745 : Blo 2095435 3145745 := bstep (se 2 (by rfl) ⟨1179654, by rfl⟩ : syracuseStep 3145745 = 2359309) B2359309
theorem B2097163 : Blo 2095435 2097163 := bstep (se 1 (by rfl) ⟨1572872, by rfl⟩ : syracuseStep 2097163 = 3145745) B3145745
theorem B7077941 : Blo 2095435 7077941 := bbase (se 5 (by rfl) ⟨331778, by rfl⟩ : syracuseStep 7077941 = 663557) (by norm_num)
theorem B4718627 : Blo 2095435 4718627 := bstep (se 1 (by rfl) ⟨3538970, by rfl⟩ : syracuseStep 4718627 = 7077941) B7077941
theorem B3145751 : Blo 2095435 3145751 := bstep (se 1 (by rfl) ⟨2359313, by rfl⟩ : syracuseStep 3145751 = 4718627) B4718627
theorem B2097167 : Blo 2095435 2097167 := bstep (se 1 (by rfl) ⟨1572875, by rfl⟩ : syracuseStep 2097167 = 3145751) B3145751
theorem B3145757 : Blo 2095435 3145757 := bbase (se 3 (by rfl) ⟨589829, by rfl⟩ : syracuseStep 3145757 = 1179659) (by norm_num)
theorem B2097171 : Blo 2095435 2097171 := bstep (se 1 (by rfl) ⟨1572878, by rfl⟩ : syracuseStep 2097171 = 3145757) B3145757
theorem B4718645 : Blo 2095435 4718645 := bbase (se 5 (by rfl) ⟨221186, by rfl⟩ : syracuseStep 4718645 = 442373) (by norm_num)
theorem B3145763 : Blo 2095435 3145763 := bstep (se 1 (by rfl) ⟨2359322, by rfl⟩ : syracuseStep 3145763 = 4718645) B4718645
theorem B2097175 : Blo 2095435 2097175 := bstep (se 1 (by rfl) ⟨1572881, by rfl⟩ : syracuseStep 2097175 = 3145763) B3145763
theorem B36321173 : Blo 2095435 36321173 := bbase (se 6 (by rfl) ⟨851277, by rfl⟩ : syracuseStep 36321173 = 1702555) (by norm_num)
theorem B24214115 : Blo 2095435 24214115 := bstep (se 1 (by rfl) ⟨18160586, by rfl⟩ : syracuseStep 24214115 = 36321173) B36321173
theorem B16142743 : Blo 2095435 16142743 := bstep (se 1 (by rfl) ⟨12107057, by rfl⟩ : syracuseStep 16142743 = 24214115) B24214115
theorem B21523657 : Blo 2095435 21523657 := bstep (se 2 (by rfl) ⟨8071371, by rfl⟩ : syracuseStep 21523657 = 16142743) B16142743
theorem B28698209 : Blo 2095435 28698209 := bstep (se 2 (by rfl) ⟨10761828, by rfl⟩ : syracuseStep 28698209 = 21523657) B21523657
theorem B19132139 : Blo 2095435 19132139 := bstep (se 1 (by rfl) ⟨14349104, by rfl⟩ : syracuseStep 19132139 = 28698209) B28698209
theorem B12754759 : Blo 2095435 12754759 := bstep (se 1 (by rfl) ⟨9566069, by rfl⟩ : syracuseStep 12754759 = 19132139) B19132139
theorem B17006345 : Blo 2095435 17006345 := bstep (se 2 (by rfl) ⟨6377379, by rfl⟩ : syracuseStep 17006345 = 12754759) B12754759
theorem B11337563 : Blo 2095435 11337563 := bstep (se 1 (by rfl) ⟨8503172, by rfl⟩ : syracuseStep 11337563 = 17006345) B17006345
theorem B7558375 : Blo 2095435 7558375 := bstep (se 1 (by rfl) ⟨5668781, by rfl⟩ : syracuseStep 7558375 = 11337563) B11337563
theorem B10077833 : Blo 2095435 10077833 := bstep (se 2 (by rfl) ⟨3779187, by rfl⟩ : syracuseStep 10077833 = 7558375) B7558375
theorem B6718555 : Blo 2095435 6718555 := bstep (se 1 (by rfl) ⟨5038916, by rfl⟩ : syracuseStep 6718555 = 10077833) B10077833
theorem B8958073 : Blo 2095435 8958073 := bstep (se 2 (by rfl) ⟨3359277, by rfl⟩ : syracuseStep 8958073 = 6718555) B6718555
theorem B11944097 : Blo 2095435 11944097 := bstep (se 2 (by rfl) ⟨4479036, by rfl⟩ : syracuseStep 11944097 = 8958073) B8958073
theorem B7962731 : Blo 2095435 7962731 := bstep (se 1 (by rfl) ⟨5972048, by rfl⟩ : syracuseStep 7962731 = 11944097) B11944097
theorem B5308487 : Blo 2095435 5308487 := bstep (se 1 (by rfl) ⟨3981365, by rfl⟩ : syracuseStep 5308487 = 7962731) B7962731
theorem B3538991 : Blo 2095435 3538991 := bstep (se 1 (by rfl) ⟨2654243, by rfl⟩ : syracuseStep 3538991 = 5308487) B5308487
theorem B2359327 : Blo 2095435 2359327 := bstep (se 1 (by rfl) ⟨1769495, by rfl⟩ : syracuseStep 2359327 = 3538991) B3538991
theorem B3145769 : Blo 2095435 3145769 := bstep (se 2 (by rfl) ⟨1179663, by rfl⟩ : syracuseStep 3145769 = 2359327) B2359327
theorem B2097179 : Blo 2095435 2097179 := bstep (se 1 (by rfl) ⟨1572884, by rfl⟩ : syracuseStep 2097179 = 3145769) B3145769
theorem B9080309 : Blo 2095435 9080309 := bbase (se 5 (by rfl) ⟨425639, by rfl⟩ : syracuseStep 9080309 = 851279) (by norm_num)
theorem B24214157 : Blo 2095435 24214157 := bstep (se 3 (by rfl) ⟨4540154, by rfl⟩ : syracuseStep 24214157 = 9080309) B9080309
theorem B16142771 : Blo 2095435 16142771 := bstep (se 1 (by rfl) ⟨12107078, by rfl⟩ : syracuseStep 16142771 = 24214157) B24214157
theorem B43047389 : Blo 2095435 43047389 := bstep (se 3 (by rfl) ⟨8071385, by rfl⟩ : syracuseStep 43047389 = 16142771) B16142771
theorem B28698259 : Blo 2095435 28698259 := bstep (se 1 (by rfl) ⟨21523694, by rfl⟩ : syracuseStep 28698259 = 43047389) B43047389
theorem B38264345 : Blo 2095435 38264345 := bstep (se 2 (by rfl) ⟨14349129, by rfl⟩ : syracuseStep 38264345 = 28698259) B28698259
theorem B25509563 : Blo 2095435 25509563 := bstep (se 1 (by rfl) ⟨19132172, by rfl⟩ : syracuseStep 25509563 = 38264345) B38264345
theorem B17006375 : Blo 2095435 17006375 := bstep (se 1 (by rfl) ⟨12754781, by rfl⟩ : syracuseStep 17006375 = 25509563) B25509563
theorem B11337583 : Blo 2095435 11337583 := bstep (se 1 (by rfl) ⟨8503187, by rfl⟩ : syracuseStep 11337583 = 17006375) B17006375
theorem B15116777 : Blo 2095435 15116777 := bstep (se 2 (by rfl) ⟨5668791, by rfl⟩ : syracuseStep 15116777 = 11337583) B11337583
theorem B10077851 : Blo 2095435 10077851 := bstep (se 1 (by rfl) ⟨7558388, by rfl⟩ : syracuseStep 10077851 = 15116777) B15116777
theorem B6718567 : Blo 2095435 6718567 := bstep (se 1 (by rfl) ⟨5038925, by rfl⟩ : syracuseStep 6718567 = 10077851) B10077851
theorem B8958089 : Blo 2095435 8958089 := bstep (se 2 (by rfl) ⟨3359283, by rfl⟩ : syracuseStep 8958089 = 6718567) B6718567
theorem B5972059 : Blo 2095435 5972059 := bstep (se 1 (by rfl) ⟨4479044, by rfl⟩ : syracuseStep 5972059 = 8958089) B8958089
theorem B7962745 : Blo 2095435 7962745 := bstep (se 2 (by rfl) ⟨2986029, by rfl⟩ : syracuseStep 7962745 = 5972059) B5972059
theorem B10616993 : Blo 2095435 10616993 := bstep (se 2 (by rfl) ⟨3981372, by rfl⟩ : syracuseStep 10616993 = 7962745) B7962745
theorem B7077995 : Blo 2095435 7077995 := bstep (se 1 (by rfl) ⟨5308496, by rfl⟩ : syracuseStep 7077995 = 10616993) B10616993
theorem B4718663 : Blo 2095435 4718663 := bstep (se 1 (by rfl) ⟨3538997, by rfl⟩ : syracuseStep 4718663 = 7077995) B7077995
theorem B3145775 : Blo 2095435 3145775 := bstep (se 1 (by rfl) ⟨2359331, by rfl⟩ : syracuseStep 3145775 = 4718663) B4718663
theorem B2097183 : Blo 2095435 2097183 := bstep (se 1 (by rfl) ⟨1572887, by rfl⟩ : syracuseStep 2097183 = 3145775) B3145775
theorem B3145781 : Blo 2095435 3145781 := bbase (se 5 (by rfl) ⟨147458, by rfl⟩ : syracuseStep 3145781 = 294917) (by norm_num)
theorem B2097187 : Blo 2095435 2097187 := bstep (se 1 (by rfl) ⟨1572890, by rfl⟩ : syracuseStep 2097187 = 3145781) B3145781
theorem B5308517 : Blo 2095435 5308517 := bbase (se 4 (by rfl) ⟨497673, by rfl⟩ : syracuseStep 5308517 = 995347) (by norm_num)
theorem B3539011 : Blo 2095435 3539011 := bstep (se 1 (by rfl) ⟨2654258, by rfl⟩ : syracuseStep 3539011 = 5308517) B5308517
theorem B4718681 : Blo 2095435 4718681 := bstep (se 2 (by rfl) ⟨1769505, by rfl⟩ : syracuseStep 4718681 = 3539011) B3539011
theorem B3145787 : Blo 2095435 3145787 := bstep (se 1 (by rfl) ⟨2359340, by rfl⟩ : syracuseStep 3145787 = 4718681) B4718681
theorem B2097191 : Blo 2095435 2097191 := bstep (se 1 (by rfl) ⟨1572893, by rfl⟩ : syracuseStep 2097191 = 3145787) B3145787
theorem B2359345 : Blo 2095435 2359345 := bbase (se 2 (by rfl) ⟨884754, by rfl⟩ : syracuseStep 2359345 = 1769509) (by norm_num)
theorem B3145793 : Blo 2095435 3145793 := bstep (se 2 (by rfl) ⟨1179672, by rfl⟩ : syracuseStep 3145793 = 2359345) B2359345
theorem B2097195 : Blo 2095435 2097195 := bstep (se 1 (by rfl) ⟨1572896, by rfl⟩ : syracuseStep 2097195 = 3145793) B3145793
theorem B7661573 : Blo 2095435 7661573 := bbase (se 4 (by rfl) ⟨718272, by rfl⟩ : syracuseStep 7661573 = 1436545) (by norm_num)
theorem B5107715 : Blo 2095435 5107715 := bstep (se 1 (by rfl) ⟨3830786, by rfl⟩ : syracuseStep 5107715 = 7661573) B7661573
theorem B3405143 : Blo 2095435 3405143 := bstep (se 1 (by rfl) ⟨2553857, by rfl⟩ : syracuseStep 3405143 = 5107715) B5107715
theorem B2270095 : Blo 2095435 2270095 := bstep (se 1 (by rfl) ⟨1702571, by rfl⟩ : syracuseStep 2270095 = 3405143) B3405143
theorem B12107173 : Blo 2095435 12107173 := bstep (se 4 (by rfl) ⟨1135047, by rfl⟩ : syracuseStep 12107173 = 2270095) B2270095
theorem B16142897 : Blo 2095435 16142897 := bstep (se 2 (by rfl) ⟨6053586, by rfl⟩ : syracuseStep 16142897 = 12107173) B12107173
theorem B10761931 : Blo 2095435 10761931 := bstep (se 1 (by rfl) ⟨8071448, by rfl⟩ : syracuseStep 10761931 = 16142897) B16142897
theorem B14349241 : Blo 2095435 14349241 := bstep (se 2 (by rfl) ⟨5380965, by rfl⟩ : syracuseStep 14349241 = 10761931) B10761931
theorem B19132321 : Blo 2095435 19132321 := bstep (se 2 (by rfl) ⟨7174620, by rfl⟩ : syracuseStep 19132321 = 14349241) B14349241
theorem B25509761 : Blo 2095435 25509761 := bstep (se 2 (by rfl) ⟨9566160, by rfl⟩ : syracuseStep 25509761 = 19132321) B19132321
theorem B17006507 : Blo 2095435 17006507 := bstep (se 1 (by rfl) ⟨12754880, by rfl⟩ : syracuseStep 17006507 = 25509761) B25509761
theorem B11337671 : Blo 2095435 11337671 := bstep (se 1 (by rfl) ⟨8503253, by rfl⟩ : syracuseStep 11337671 = 17006507) B17006507
theorem B7558447 : Blo 2095435 7558447 := bstep (se 1 (by rfl) ⟨5668835, by rfl⟩ : syracuseStep 7558447 = 11337671) B11337671
theorem B10077929 : Blo 2095435 10077929 := bstep (se 2 (by rfl) ⟨3779223, by rfl⟩ : syracuseStep 10077929 = 7558447) B7558447
theorem B6718619 : Blo 2095435 6718619 := bstep (se 1 (by rfl) ⟨5038964, by rfl⟩ : syracuseStep 6718619 = 10077929) B10077929
theorem B4479079 : Blo 2095435 4479079 := bstep (se 1 (by rfl) ⟨3359309, by rfl⟩ : syracuseStep 4479079 = 6718619) B6718619
theorem B5972105 : Blo 2095435 5972105 := bstep (se 2 (by rfl) ⟨2239539, by rfl⟩ : syracuseStep 5972105 = 4479079) B4479079
theorem B3981403 : Blo 2095435 3981403 := bstep (se 1 (by rfl) ⟨2986052, by rfl⟩ : syracuseStep 3981403 = 5972105) B5972105
theorem B5308537 : Blo 2095435 5308537 := bstep (se 2 (by rfl) ⟨1990701, by rfl⟩ : syracuseStep 5308537 = 3981403) B3981403
theorem B7078049 : Blo 2095435 7078049 := bstep (se 2 (by rfl) ⟨2654268, by rfl⟩ : syracuseStep 7078049 = 5308537) B5308537
theorem B4718699 : Blo 2095435 4718699 := bstep (se 1 (by rfl) ⟨3539024, by rfl⟩ : syracuseStep 4718699 = 7078049) B7078049
theorem B3145799 : Blo 2095435 3145799 := bstep (se 1 (by rfl) ⟨2359349, by rfl⟩ : syracuseStep 3145799 = 4718699) B4718699
theorem B2097199 : Blo 2095435 2097199 := bstep (se 1 (by rfl) ⟨1572899, by rfl⟩ : syracuseStep 2097199 = 3145799) B3145799
theorem B3145805 : Blo 2095435 3145805 := bbase (se 3 (by rfl) ⟨589838, by rfl⟩ : syracuseStep 3145805 = 1179677) (by norm_num)
theorem B2097203 : Blo 2095435 2097203 := bstep (se 1 (by rfl) ⟨1572902, by rfl⟩ : syracuseStep 2097203 = 3145805) B3145805
theorem B4718717 : Blo 2095435 4718717 := bbase (se 3 (by rfl) ⟨884759, by rfl⟩ : syracuseStep 4718717 = 1769519) (by norm_num)
theorem B3145811 : Blo 2095435 3145811 := bstep (se 1 (by rfl) ⟨2359358, by rfl⟩ : syracuseStep 3145811 = 4718717) B4718717
theorem B2097207 : Blo 2095435 2097207 := bstep (se 1 (by rfl) ⟨1572905, by rfl⟩ : syracuseStep 2097207 = 3145811) B3145811
theorem B3539045 : Blo 2095435 3539045 := bbase (se 4 (by rfl) ⟨331785, by rfl⟩ : syracuseStep 3539045 = 663571) (by norm_num)
theorem B2359363 : Blo 2095435 2359363 := bstep (se 1 (by rfl) ⟨1769522, by rfl⟩ : syracuseStep 2359363 = 3539045) B3539045
theorem B3145817 : Blo 2095435 3145817 := bstep (se 2 (by rfl) ⟨1179681, by rfl⟩ : syracuseStep 3145817 = 2359363) B2359363
theorem B2097211 : Blo 2095435 2097211 := bstep (se 1 (by rfl) ⟨1572908, by rfl⟩ : syracuseStep 2097211 = 3145817) B3145817
theorem B19132469 : Blo 2095435 19132469 := bbase (se 5 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 19132469 = 1793669) (by norm_num)
theorem B12754979 : Blo 2095435 12754979 := bstep (se 1 (by rfl) ⟨9566234, by rfl⟩ : syracuseStep 12754979 = 19132469) B19132469
theorem B8503319 : Blo 2095435 8503319 := bstep (se 1 (by rfl) ⟨6377489, by rfl⟩ : syracuseStep 8503319 = 12754979) B12754979
theorem B5668879 : Blo 2095435 5668879 := bstep (se 1 (by rfl) ⟨4251659, by rfl⟩ : syracuseStep 5668879 = 8503319) B8503319
theorem B7558505 : Blo 2095435 7558505 := bstep (se 2 (by rfl) ⟨2834439, by rfl⟩ : syracuseStep 7558505 = 5668879) B5668879
theorem B5039003 : Blo 2095435 5039003 := bstep (se 1 (by rfl) ⟨3779252, by rfl⟩ : syracuseStep 5039003 = 7558505) B7558505
theorem B3359335 : Blo 2095435 3359335 := bstep (se 1 (by rfl) ⟨2519501, by rfl⟩ : syracuseStep 3359335 = 5039003) B5039003
theorem B4479113 : Blo 2095435 4479113 := bstep (se 2 (by rfl) ⟨1679667, by rfl⟩ : syracuseStep 4479113 = 3359335) B3359335
theorem B2986075 : Blo 2095435 2986075 := bstep (se 1 (by rfl) ⟨2239556, by rfl⟩ : syracuseStep 2986075 = 4479113) B4479113
theorem B15925733 : Blo 2095435 15925733 := bstep (se 4 (by rfl) ⟨1493037, by rfl⟩ : syracuseStep 15925733 = 2986075) B2986075
theorem B10617155 : Blo 2095435 10617155 := bstep (se 1 (by rfl) ⟨7962866, by rfl⟩ : syracuseStep 10617155 = 15925733) B15925733
theorem B7078103 : Blo 2095435 7078103 := bstep (se 1 (by rfl) ⟨5308577, by rfl⟩ : syracuseStep 7078103 = 10617155) B10617155
theorem B4718735 : Blo 2095435 4718735 := bstep (se 1 (by rfl) ⟨3539051, by rfl⟩ : syracuseStep 4718735 = 7078103) B7078103
theorem B3145823 : Blo 2095435 3145823 := bstep (se 1 (by rfl) ⟨2359367, by rfl⟩ : syracuseStep 3145823 = 4718735) B4718735
theorem B2097215 : Blo 2095435 2097215 := bstep (se 1 (by rfl) ⟨1572911, by rfl⟩ : syracuseStep 2097215 = 3145823) B3145823
theorem B3145829 : Blo 2095435 3145829 := bbase (se 4 (by rfl) ⟨294921, by rfl⟩ : syracuseStep 3145829 = 589843) (by norm_num)
theorem B2097219 : Blo 2095435 2097219 := bstep (se 1 (by rfl) ⟨1572914, by rfl⟩ : syracuseStep 2097219 = 3145829) B3145829
theorem B12755029 : Blo 2095435 12755029 := bbase (se 8 (by rfl) ⟨74736, by rfl⟩ : syracuseStep 12755029 = 149473) (by norm_num)
theorem B17006705 : Blo 2095435 17006705 := bstep (se 2 (by rfl) ⟨6377514, by rfl⟩ : syracuseStep 17006705 = 12755029) B12755029
theorem B11337803 : Blo 2095435 11337803 := bstep (se 1 (by rfl) ⟨8503352, by rfl⟩ : syracuseStep 11337803 = 17006705) B17006705
theorem B7558535 : Blo 2095435 7558535 := bstep (se 1 (by rfl) ⟨5668901, by rfl⟩ : syracuseStep 7558535 = 11337803) B11337803
theorem B5039023 : Blo 2095435 5039023 := bstep (se 1 (by rfl) ⟨3779267, by rfl⟩ : syracuseStep 5039023 = 7558535) B7558535
theorem B6718697 : Blo 2095435 6718697 := bstep (se 2 (by rfl) ⟨2519511, by rfl⟩ : syracuseStep 6718697 = 5039023) B5039023
theorem B4479131 : Blo 2095435 4479131 := bstep (se 1 (by rfl) ⟨3359348, by rfl⟩ : syracuseStep 4479131 = 6718697) B6718697
theorem B2986087 : Blo 2095435 2986087 := bstep (se 1 (by rfl) ⟨2239565, by rfl⟩ : syracuseStep 2986087 = 4479131) B4479131
theorem B3981449 : Blo 2095435 3981449 := bstep (se 2 (by rfl) ⟨1493043, by rfl⟩ : syracuseStep 3981449 = 2986087) B2986087
theorem B2654299 : Blo 2095435 2654299 := bstep (se 1 (by rfl) ⟨1990724, by rfl⟩ : syracuseStep 2654299 = 3981449) B3981449
theorem B3539065 : Blo 2095435 3539065 := bstep (se 2 (by rfl) ⟨1327149, by rfl⟩ : syracuseStep 3539065 = 2654299) B2654299
theorem B4718753 : Blo 2095435 4718753 := bstep (se 2 (by rfl) ⟨1769532, by rfl⟩ : syracuseStep 4718753 = 3539065) B3539065
theorem B3145835 : Blo 2095435 3145835 := bstep (se 1 (by rfl) ⟨2359376, by rfl⟩ : syracuseStep 3145835 = 4718753) B4718753
theorem B2097223 : Blo 2095435 2097223 := bstep (se 1 (by rfl) ⟨1572917, by rfl⟩ : syracuseStep 2097223 = 3145835) B3145835
theorem B2359381 : Blo 2095435 2359381 := bbase (se 8 (by rfl) ⟨13824, by rfl⟩ : syracuseStep 2359381 = 27649) (by norm_num)
theorem B3145841 : Blo 2095435 3145841 := bstep (se 2 (by rfl) ⟨1179690, by rfl⟩ : syracuseStep 3145841 = 2359381) B2359381
theorem B2097227 : Blo 2095435 2097227 := bstep (se 1 (by rfl) ⟨1572920, by rfl⟩ : syracuseStep 2097227 = 3145841) B3145841
theorem B2654309 : Blo 2095435 2654309 := bbase (se 4 (by rfl) ⟨248841, by rfl⟩ : syracuseStep 2654309 = 497683) (by norm_num)
theorem B7078157 : Blo 2095435 7078157 := bstep (se 3 (by rfl) ⟨1327154, by rfl⟩ : syracuseStep 7078157 = 2654309) B2654309
theorem B4718771 : Blo 2095435 4718771 := bstep (se 1 (by rfl) ⟨3539078, by rfl⟩ : syracuseStep 4718771 = 7078157) B7078157
theorem B3145847 : Blo 2095435 3145847 := bstep (se 1 (by rfl) ⟨2359385, by rfl⟩ : syracuseStep 3145847 = 4718771) B4718771
theorem B2097231 : Blo 2095435 2097231 := bstep (se 1 (by rfl) ⟨1572923, by rfl⟩ : syracuseStep 2097231 = 3145847) B3145847
theorem B3145853 : Blo 2095435 3145853 := bbase (se 3 (by rfl) ⟨589847, by rfl⟩ : syracuseStep 3145853 = 1179695) (by norm_num)
theorem B2097235 : Blo 2095435 2097235 := bstep (se 1 (by rfl) ⟨1572926, by rfl⟩ : syracuseStep 2097235 = 3145853) B3145853
theorem B4718789 : Blo 2095435 4718789 := bbase (se 4 (by rfl) ⟨442386, by rfl⟩ : syracuseStep 4718789 = 884773) (by norm_num)
theorem B3145859 : Blo 2095435 3145859 := bstep (se 1 (by rfl) ⟨2359394, by rfl⟩ : syracuseStep 3145859 = 4718789) B4718789
theorem B2097239 : Blo 2095435 2097239 := bstep (se 1 (by rfl) ⟨1572929, by rfl⟩ : syracuseStep 2097239 = 3145859) B3145859
theorem B8181749 : Blo 2095435 8181749 := bbase (se 5 (by rfl) ⟨383519, by rfl⟩ : syracuseStep 8181749 = 767039) (by norm_num)
theorem B5454499 : Blo 2095435 5454499 := bstep (se 1 (by rfl) ⟨4090874, by rfl⟩ : syracuseStep 5454499 = 8181749) B8181749
theorem B7272665 : Blo 2095435 7272665 := bstep (se 2 (by rfl) ⟨2727249, by rfl⟩ : syracuseStep 7272665 = 5454499) B5454499
theorem B4848443 : Blo 2095435 4848443 := bstep (se 1 (by rfl) ⟨3636332, by rfl⟩ : syracuseStep 4848443 = 7272665) B7272665
theorem B3232295 : Blo 2095435 3232295 := bstep (se 1 (by rfl) ⟨2424221, by rfl⟩ : syracuseStep 3232295 = 4848443) B4848443
theorem B2154863 : Blo 2095435 2154863 := bstep (se 1 (by rfl) ⟨1616147, by rfl⟩ : syracuseStep 2154863 = 3232295) B3232295
theorem B5746301 : Blo 2095435 5746301 := bstep (se 3 (by rfl) ⟨1077431, by rfl⟩ : syracuseStep 5746301 = 2154863) B2154863
theorem B3830867 : Blo 2095435 3830867 := bstep (se 1 (by rfl) ⟨2873150, by rfl⟩ : syracuseStep 3830867 = 5746301) B5746301
theorem B2553911 : Blo 2095435 2553911 := bstep (se 1 (by rfl) ⟨1915433, by rfl⟩ : syracuseStep 2553911 = 3830867) B3830867
theorem B27241717 : Blo 2095435 27241717 := bstep (se 5 (by rfl) ⟨1276955, by rfl⟩ : syracuseStep 27241717 = 2553911) B2553911
theorem B36322289 : Blo 2095435 36322289 := bstep (se 2 (by rfl) ⟨13620858, by rfl⟩ : syracuseStep 36322289 = 27241717) B27241717
theorem B24214859 : Blo 2095435 24214859 := bstep (se 1 (by rfl) ⟨18161144, by rfl⟩ : syracuseStep 24214859 = 36322289) B36322289
theorem B16143239 : Blo 2095435 16143239 := bstep (se 1 (by rfl) ⟨12107429, by rfl⟩ : syracuseStep 16143239 = 24214859) B24214859
theorem B10762159 : Blo 2095435 10762159 := bstep (se 1 (by rfl) ⟨8071619, by rfl⟩ : syracuseStep 10762159 = 16143239) B16143239
theorem B14349545 : Blo 2095435 14349545 := bstep (se 2 (by rfl) ⟨5381079, by rfl⟩ : syracuseStep 14349545 = 10762159) B10762159
theorem B9566363 : Blo 2095435 9566363 := bstep (se 1 (by rfl) ⟨7174772, by rfl⟩ : syracuseStep 9566363 = 14349545) B14349545
theorem B6377575 : Blo 2095435 6377575 := bstep (se 1 (by rfl) ⟨4783181, by rfl⟩ : syracuseStep 6377575 = 9566363) B9566363
theorem B8503433 : Blo 2095435 8503433 := bstep (se 2 (by rfl) ⟨3188787, by rfl⟩ : syracuseStep 8503433 = 6377575) B6377575
theorem B5668955 : Blo 2095435 5668955 := bstep (se 1 (by rfl) ⟨4251716, by rfl⟩ : syracuseStep 5668955 = 8503433) B8503433
theorem B3779303 : Blo 2095435 3779303 := bstep (se 1 (by rfl) ⟨2834477, by rfl⟩ : syracuseStep 3779303 = 5668955) B5668955
theorem B10078141 : Blo 2095435 10078141 := bstep (se 3 (by rfl) ⟨1889651, by rfl⟩ : syracuseStep 10078141 = 3779303) B3779303
theorem B13437521 : Blo 2095435 13437521 := bstep (se 2 (by rfl) ⟨5039070, by rfl⟩ : syracuseStep 13437521 = 10078141) B10078141
theorem B8958347 : Blo 2095435 8958347 := bstep (se 1 (by rfl) ⟨6718760, by rfl⟩ : syracuseStep 8958347 = 13437521) B13437521
theorem B5972231 : Blo 2095435 5972231 := bstep (se 1 (by rfl) ⟨4479173, by rfl⟩ : syracuseStep 5972231 = 8958347) B8958347
theorem B3981487 : Blo 2095435 3981487 := bstep (se 1 (by rfl) ⟨2986115, by rfl⟩ : syracuseStep 3981487 = 5972231) B5972231
theorem B5308649 : Blo 2095435 5308649 := bstep (se 2 (by rfl) ⟨1990743, by rfl⟩ : syracuseStep 5308649 = 3981487) B3981487
theorem B3539099 : Blo 2095435 3539099 := bstep (se 1 (by rfl) ⟨2654324, by rfl⟩ : syracuseStep 3539099 = 5308649) B5308649
theorem B2359399 : Blo 2095435 2359399 := bstep (se 1 (by rfl) ⟨1769549, by rfl⟩ : syracuseStep 2359399 = 3539099) B3539099
theorem B3145865 : Blo 2095435 3145865 := bstep (se 2 (by rfl) ⟨1179699, by rfl⟩ : syracuseStep 3145865 = 2359399) B2359399
theorem B2097243 : Blo 2095435 2097243 := bstep (se 1 (by rfl) ⟨1572932, by rfl⟩ : syracuseStep 2097243 = 3145865) B3145865
theorem B10617317 : Blo 2095435 10617317 := bbase (se 4 (by rfl) ⟨995373, by rfl⟩ : syracuseStep 10617317 = 1990747) (by norm_num)
theorem B7078211 : Blo 2095435 7078211 := bstep (se 1 (by rfl) ⟨5308658, by rfl⟩ : syracuseStep 7078211 = 10617317) B10617317
theorem B4718807 : Blo 2095435 4718807 := bstep (se 1 (by rfl) ⟨3539105, by rfl⟩ : syracuseStep 4718807 = 7078211) B7078211
theorem B3145871 : Blo 2095435 3145871 := bstep (se 1 (by rfl) ⟨2359403, by rfl⟩ : syracuseStep 3145871 = 4718807) B4718807
theorem B2097247 : Blo 2095435 2097247 := bstep (se 1 (by rfl) ⟨1572935, by rfl⟩ : syracuseStep 2097247 = 3145871) B3145871
theorem B3145877 : Blo 2095435 3145877 := bbase (se 6 (by rfl) ⟨73731, by rfl⟩ : syracuseStep 3145877 = 147463) (by norm_num)
theorem B2097251 : Blo 2095435 2097251 := bstep (se 1 (by rfl) ⟨1572938, by rfl⟩ : syracuseStep 2097251 = 3145877) B3145877
theorem B5107853 : Blo 2095435 5107853 := bbase (se 3 (by rfl) ⟨957722, by rfl⟩ : syracuseStep 5107853 = 1915445) (by norm_num)
theorem B3405235 : Blo 2095435 3405235 := bstep (se 1 (by rfl) ⟨2553926, by rfl⟩ : syracuseStep 3405235 = 5107853) B5107853
theorem B4540313 : Blo 2095435 4540313 := bstep (se 2 (by rfl) ⟨1702617, by rfl⟩ : syracuseStep 4540313 = 3405235) B3405235
theorem B3026875 : Blo 2095435 3026875 := bstep (se 1 (by rfl) ⟨2270156, by rfl⟩ : syracuseStep 3026875 = 4540313) B4540313
theorem B4035833 : Blo 2095435 4035833 := bstep (se 2 (by rfl) ⟨1513437, by rfl⟩ : syracuseStep 4035833 = 3026875) B3026875
theorem B2690555 : Blo 2095435 2690555 := bstep (se 1 (by rfl) ⟨2017916, by rfl⟩ : syracuseStep 2690555 = 4035833) B4035833
theorem B7174813 : Blo 2095435 7174813 := bstep (se 3 (by rfl) ⟨1345277, by rfl⟩ : syracuseStep 7174813 = 2690555) B2690555
theorem B9566417 : Blo 2095435 9566417 := bstep (se 2 (by rfl) ⟨3587406, by rfl⟩ : syracuseStep 9566417 = 7174813) B7174813
theorem B6377611 : Blo 2095435 6377611 := bstep (se 1 (by rfl) ⟨4783208, by rfl⟩ : syracuseStep 6377611 = 9566417) B9566417
theorem B8503481 : Blo 2095435 8503481 := bstep (se 2 (by rfl) ⟨3188805, by rfl⟩ : syracuseStep 8503481 = 6377611) B6377611
theorem B5668987 : Blo 2095435 5668987 := bstep (se 1 (by rfl) ⟨4251740, by rfl⟩ : syracuseStep 5668987 = 8503481) B8503481
theorem B7558649 : Blo 2095435 7558649 := bstep (se 2 (by rfl) ⟨2834493, by rfl⟩ : syracuseStep 7558649 = 5668987) B5668987
theorem B5039099 : Blo 2095435 5039099 := bstep (se 1 (by rfl) ⟨3779324, by rfl⟩ : syracuseStep 5039099 = 7558649) B7558649
theorem B3359399 : Blo 2095435 3359399 := bstep (se 1 (by rfl) ⟨2519549, by rfl⟩ : syracuseStep 3359399 = 5039099) B5039099
theorem B8958397 : Blo 2095435 8958397 := bstep (se 3 (by rfl) ⟨1679699, by rfl⟩ : syracuseStep 8958397 = 3359399) B3359399
theorem B11944529 : Blo 2095435 11944529 := bstep (se 2 (by rfl) ⟨4479198, by rfl⟩ : syracuseStep 11944529 = 8958397) B8958397
theorem B7963019 : Blo 2095435 7963019 := bstep (se 1 (by rfl) ⟨5972264, by rfl⟩ : syracuseStep 7963019 = 11944529) B11944529
theorem B5308679 : Blo 2095435 5308679 := bstep (se 1 (by rfl) ⟨3981509, by rfl⟩ : syracuseStep 5308679 = 7963019) B7963019
theorem B3539119 : Blo 2095435 3539119 := bstep (se 1 (by rfl) ⟨2654339, by rfl⟩ : syracuseStep 3539119 = 5308679) B5308679
theorem B4718825 : Blo 2095435 4718825 := bstep (se 2 (by rfl) ⟨1769559, by rfl⟩ : syracuseStep 4718825 = 3539119) B3539119
theorem B3145883 : Blo 2095435 3145883 := bstep (se 1 (by rfl) ⟨2359412, by rfl⟩ : syracuseStep 3145883 = 4718825) B4718825
theorem B2097255 : Blo 2095435 2097255 := bstep (se 1 (by rfl) ⟨1572941, by rfl⟩ : syracuseStep 2097255 = 3145883) B3145883
theorem B2359417 : Blo 2095435 2359417 := bbase (se 2 (by rfl) ⟨884781, by rfl⟩ : syracuseStep 2359417 = 1769563) (by norm_num)
theorem B3145889 : Blo 2095435 3145889 := bstep (se 2 (by rfl) ⟨1179708, by rfl⟩ : syracuseStep 3145889 = 2359417) B2359417
theorem B2097259 : Blo 2095435 2097259 := bstep (se 1 (by rfl) ⟨1572944, by rfl⟩ : syracuseStep 2097259 = 3145889) B3145889
theorem B3026885 : Blo 2095435 3026885 := bbase (se 4 (by rfl) ⟨283770, by rfl⟩ : syracuseStep 3026885 = 567541) (by norm_num)
theorem B8071693 : Blo 2095435 8071693 := bstep (se 3 (by rfl) ⟨1513442, by rfl⟩ : syracuseStep 8071693 = 3026885) B3026885
theorem B43049029 : Blo 2095435 43049029 := bstep (se 4 (by rfl) ⟨4035846, by rfl⟩ : syracuseStep 43049029 = 8071693) B8071693
theorem B57398705 : Blo 2095435 57398705 := bstep (se 2 (by rfl) ⟨21524514, by rfl⟩ : syracuseStep 57398705 = 43049029) B43049029
theorem B38265803 : Blo 2095435 38265803 := bstep (se 1 (by rfl) ⟨28699352, by rfl⟩ : syracuseStep 38265803 = 57398705) B57398705
theorem B25510535 : Blo 2095435 25510535 := bstep (se 1 (by rfl) ⟨19132901, by rfl⟩ : syracuseStep 25510535 = 38265803) B38265803
theorem B17007023 : Blo 2095435 17007023 := bstep (se 1 (by rfl) ⟨12755267, by rfl⟩ : syracuseStep 17007023 = 25510535) B25510535
theorem B45352061 : Blo 2095435 45352061 := bstep (se 3 (by rfl) ⟨8503511, by rfl⟩ : syracuseStep 45352061 = 17007023) B17007023
theorem B30234707 : Blo 2095435 30234707 := bstep (se 1 (by rfl) ⟨22676030, by rfl⟩ : syracuseStep 30234707 = 45352061) B45352061
theorem B20156471 : Blo 2095435 20156471 := bstep (se 1 (by rfl) ⟨15117353, by rfl⟩ : syracuseStep 20156471 = 30234707) B30234707
theorem B13437647 : Blo 2095435 13437647 := bstep (se 1 (by rfl) ⟨10078235, by rfl⟩ : syracuseStep 13437647 = 20156471) B20156471
theorem B8958431 : Blo 2095435 8958431 := bstep (se 1 (by rfl) ⟨6718823, by rfl⟩ : syracuseStep 8958431 = 13437647) B13437647
theorem B5972287 : Blo 2095435 5972287 := bstep (se 1 (by rfl) ⟨4479215, by rfl⟩ : syracuseStep 5972287 = 8958431) B8958431
theorem B7963049 : Blo 2095435 7963049 := bstep (se 2 (by rfl) ⟨2986143, by rfl⟩ : syracuseStep 7963049 = 5972287) B5972287
theorem B5308699 : Blo 2095435 5308699 := bstep (se 1 (by rfl) ⟨3981524, by rfl⟩ : syracuseStep 5308699 = 7963049) B7963049
theorem B7078265 : Blo 2095435 7078265 := bstep (se 2 (by rfl) ⟨2654349, by rfl⟩ : syracuseStep 7078265 = 5308699) B5308699
theorem B4718843 : Blo 2095435 4718843 := bstep (se 1 (by rfl) ⟨3539132, by rfl⟩ : syracuseStep 4718843 = 7078265) B7078265
theorem B3145895 : Blo 2095435 3145895 := bstep (se 1 (by rfl) ⟨2359421, by rfl⟩ : syracuseStep 3145895 = 4718843) B4718843
theorem B2097263 : Blo 2095435 2097263 := bstep (se 1 (by rfl) ⟨1572947, by rfl⟩ : syracuseStep 2097263 = 3145895) B3145895
theorem B3145901 : Blo 2095435 3145901 := bbase (se 3 (by rfl) ⟨589856, by rfl⟩ : syracuseStep 3145901 = 1179713) (by norm_num)
theorem B2097267 : Blo 2095435 2097267 := bstep (se 1 (by rfl) ⟨1572950, by rfl⟩ : syracuseStep 2097267 = 3145901) B3145901
theorem B4718861 : Blo 2095435 4718861 := bbase (se 3 (by rfl) ⟨884786, by rfl⟩ : syracuseStep 4718861 = 1769573) (by norm_num)
theorem B3145907 : Blo 2095435 3145907 := bstep (se 1 (by rfl) ⟨2359430, by rfl⟩ : syracuseStep 3145907 = 4718861) B4718861
theorem B2097271 : Blo 2095435 2097271 := bstep (se 1 (by rfl) ⟨1572953, by rfl⟩ : syracuseStep 2097271 = 3145907) B3145907
theorem B2654365 : Blo 2095435 2654365 := bbase (se 3 (by rfl) ⟨497693, by rfl⟩ : syracuseStep 2654365 = 995387) (by norm_num)
theorem B3539153 : Blo 2095435 3539153 := bstep (se 2 (by rfl) ⟨1327182, by rfl⟩ : syracuseStep 3539153 = 2654365) B2654365
theorem B2359435 : Blo 2095435 2359435 := bstep (se 1 (by rfl) ⟨1769576, by rfl⟩ : syracuseStep 2359435 = 3539153) B3539153
theorem B3145913 : Blo 2095435 3145913 := bstep (se 2 (by rfl) ⟨1179717, by rfl⟩ : syracuseStep 3145913 = 2359435) B2359435
theorem B2097275 : Blo 2095435 2097275 := bstep (se 1 (by rfl) ⟨1572956, by rfl⟩ : syracuseStep 2097275 = 3145913) B3145913
theorem B3359437 : Blo 2095435 3359437 := bbase (se 3 (by rfl) ⟨629894, by rfl⟩ : syracuseStep 3359437 = 1259789) (by norm_num)
theorem B17916997 : Blo 2095435 17916997 := bstep (se 4 (by rfl) ⟨1679718, by rfl⟩ : syracuseStep 17916997 = 3359437) B3359437
theorem B23889329 : Blo 2095435 23889329 := bstep (se 2 (by rfl) ⟨8958498, by rfl⟩ : syracuseStep 23889329 = 17916997) B17916997
theorem B15926219 : Blo 2095435 15926219 := bstep (se 1 (by rfl) ⟨11944664, by rfl⟩ : syracuseStep 15926219 = 23889329) B23889329
theorem B10617479 : Blo 2095435 10617479 := bstep (se 1 (by rfl) ⟨7963109, by rfl⟩ : syracuseStep 10617479 = 15926219) B15926219
theorem B7078319 : Blo 2095435 7078319 := bstep (se 1 (by rfl) ⟨5308739, by rfl⟩ : syracuseStep 7078319 = 10617479) B10617479
theorem B4718879 : Blo 2095435 4718879 := bstep (se 1 (by rfl) ⟨3539159, by rfl⟩ : syracuseStep 4718879 = 7078319) B7078319
theorem B3145919 : Blo 2095435 3145919 := bstep (se 1 (by rfl) ⟨2359439, by rfl⟩ : syracuseStep 3145919 = 4718879) B4718879
theorem B2097279 : Blo 2095435 2097279 := bstep (se 1 (by rfl) ⟨1572959, by rfl⟩ : syracuseStep 2097279 = 3145919) B3145919
theorem B3145925 : Blo 2095435 3145925 := bbase (se 4 (by rfl) ⟨294930, by rfl⟩ : syracuseStep 3145925 = 589861) (by norm_num)
theorem B2097283 : Blo 2095435 2097283 := bstep (se 1 (by rfl) ⟨1572962, by rfl⟩ : syracuseStep 2097283 = 3145925) B3145925
theorem B3539173 : Blo 2095435 3539173 := bbase (se 4 (by rfl) ⟨331797, by rfl⟩ : syracuseStep 3539173 = 663595) (by norm_num)
theorem B4718897 : Blo 2095435 4718897 := bstep (se 2 (by rfl) ⟨1769586, by rfl⟩ : syracuseStep 4718897 = 3539173) B3539173
theorem B3145931 : Blo 2095435 3145931 := bstep (se 1 (by rfl) ⟨2359448, by rfl⟩ : syracuseStep 3145931 = 4718897) B4718897
theorem B2097287 : Blo 2095435 2097287 := bstep (se 1 (by rfl) ⟨1572965, by rfl⟩ : syracuseStep 2097287 = 3145931) B3145931
theorem B2359453 : Blo 2095435 2359453 := bbase (se 3 (by rfl) ⟨442397, by rfl⟩ : syracuseStep 2359453 = 884795) (by norm_num)
theorem B3145937 : Blo 2095435 3145937 := bstep (se 2 (by rfl) ⟨1179726, by rfl⟩ : syracuseStep 3145937 = 2359453) B2359453
theorem B2097291 : Blo 2095435 2097291 := bstep (se 1 (by rfl) ⟨1572968, by rfl⟩ : syracuseStep 2097291 = 3145937) B3145937
theorem B7078373 : Blo 2095435 7078373 := bbase (se 4 (by rfl) ⟨663597, by rfl⟩ : syracuseStep 7078373 = 1327195) (by norm_num)
theorem B4718915 : Blo 2095435 4718915 := bstep (se 1 (by rfl) ⟨3539186, by rfl⟩ : syracuseStep 4718915 = 7078373) B7078373
theorem B3145943 : Blo 2095435 3145943 := bstep (se 1 (by rfl) ⟨2359457, by rfl⟩ : syracuseStep 3145943 = 4718915) B4718915
theorem B2097295 : Blo 2095435 2097295 := bstep (se 1 (by rfl) ⟨1572971, by rfl⟩ : syracuseStep 2097295 = 3145943) B3145943
theorem B3145949 : Blo 2095435 3145949 := bbase (se 3 (by rfl) ⟨589865, by rfl⟩ : syracuseStep 3145949 = 1179731) (by norm_num)
theorem B2097299 : Blo 2095435 2097299 := bstep (se 1 (by rfl) ⟨1572974, by rfl⟩ : syracuseStep 2097299 = 3145949) B3145949
theorem B4718933 : Blo 2095435 4718933 := bbase (se 10 (by rfl) ⟨6912, by rfl⟩ : syracuseStep 4718933 = 13825) (by norm_num)
theorem B3145955 : Blo 2095435 3145955 := bstep (se 1 (by rfl) ⟨2359466, by rfl⟩ : syracuseStep 3145955 = 4718933) B4718933
theorem B2097303 : Blo 2095435 2097303 := bstep (se 1 (by rfl) ⟨1572977, by rfl⟩ : syracuseStep 2097303 = 3145955) B3145955
theorem B5381245 : Blo 2095435 5381245 := bbase (se 3 (by rfl) ⟨1008983, by rfl⟩ : syracuseStep 5381245 = 2017967) (by norm_num)
theorem B7174993 : Blo 2095435 7174993 := bstep (se 2 (by rfl) ⟨2690622, by rfl⟩ : syracuseStep 7174993 = 5381245) B5381245
theorem B9566657 : Blo 2095435 9566657 := bstep (se 2 (by rfl) ⟨3587496, by rfl⟩ : syracuseStep 9566657 = 7174993) B7174993
theorem B6377771 : Blo 2095435 6377771 := bstep (se 1 (by rfl) ⟨4783328, by rfl⟩ : syracuseStep 6377771 = 9566657) B9566657
theorem B4251847 : Blo 2095435 4251847 := bstep (se 1 (by rfl) ⟨3188885, by rfl⟩ : syracuseStep 4251847 = 6377771) B6377771
theorem B5669129 : Blo 2095435 5669129 := bstep (se 2 (by rfl) ⟨2125923, by rfl⟩ : syracuseStep 5669129 = 4251847) B4251847
theorem B3779419 : Blo 2095435 3779419 := bstep (se 1 (by rfl) ⟨2834564, by rfl⟩ : syracuseStep 3779419 = 5669129) B5669129
theorem B5039225 : Blo 2095435 5039225 := bstep (se 2 (by rfl) ⟨1889709, by rfl⟩ : syracuseStep 5039225 = 3779419) B3779419
theorem B3359483 : Blo 2095435 3359483 := bstep (se 1 (by rfl) ⟨2519612, by rfl⟩ : syracuseStep 3359483 = 5039225) B5039225
theorem B2239655 : Blo 2095435 2239655 := bstep (se 1 (by rfl) ⟨1679741, by rfl⟩ : syracuseStep 2239655 = 3359483) B3359483
theorem B5972413 : Blo 2095435 5972413 := bstep (se 3 (by rfl) ⟨1119827, by rfl⟩ : syracuseStep 5972413 = 2239655) B2239655
theorem B7963217 : Blo 2095435 7963217 := bstep (se 2 (by rfl) ⟨2986206, by rfl⟩ : syracuseStep 7963217 = 5972413) B5972413
theorem B5308811 : Blo 2095435 5308811 := bstep (se 1 (by rfl) ⟨3981608, by rfl⟩ : syracuseStep 5308811 = 7963217) B7963217
theorem B3539207 : Blo 2095435 3539207 := bstep (se 1 (by rfl) ⟨2654405, by rfl⟩ : syracuseStep 3539207 = 5308811) B5308811
theorem B2359471 : Blo 2095435 2359471 := bstep (se 1 (by rfl) ⟨1769603, by rfl⟩ : syracuseStep 2359471 = 3539207) B3539207
theorem B3145961 : Blo 2095435 3145961 := bstep (se 2 (by rfl) ⟨1179735, by rfl⟩ : syracuseStep 3145961 = 2359471) B2359471
theorem B2097307 : Blo 2095435 2097307 := bstep (se 1 (by rfl) ⟨1572980, by rfl⟩ : syracuseStep 2097307 = 3145961) B3145961
theorem B4251853 : Blo 2095435 4251853 := bbase (se 3 (by rfl) ⟨797222, by rfl⟩ : syracuseStep 4251853 = 1594445) (by norm_num)
theorem B5669137 : Blo 2095435 5669137 := bstep (se 2 (by rfl) ⟨2125926, by rfl⟩ : syracuseStep 5669137 = 4251853) B4251853
theorem B7558849 : Blo 2095435 7558849 := bstep (se 2 (by rfl) ⟨2834568, by rfl⟩ : syracuseStep 7558849 = 5669137) B5669137
theorem B40313861 : Blo 2095435 40313861 := bstep (se 4 (by rfl) ⟨3779424, by rfl⟩ : syracuseStep 40313861 = 7558849) B7558849
theorem B26875907 : Blo 2095435 26875907 := bstep (se 1 (by rfl) ⟨20156930, by rfl⟩ : syracuseStep 26875907 = 40313861) B40313861
theorem B17917271 : Blo 2095435 17917271 := bstep (se 1 (by rfl) ⟨13437953, by rfl⟩ : syracuseStep 17917271 = 26875907) B26875907
theorem B11944847 : Blo 2095435 11944847 := bstep (se 1 (by rfl) ⟨8958635, by rfl⟩ : syracuseStep 11944847 = 17917271) B17917271
theorem B7963231 : Blo 2095435 7963231 := bstep (se 1 (by rfl) ⟨5972423, by rfl⟩ : syracuseStep 7963231 = 11944847) B11944847
theorem B10617641 : Blo 2095435 10617641 := bstep (se 2 (by rfl) ⟨3981615, by rfl⟩ : syracuseStep 10617641 = 7963231) B7963231
theorem B7078427 : Blo 2095435 7078427 := bstep (se 1 (by rfl) ⟨5308820, by rfl⟩ : syracuseStep 7078427 = 10617641) B10617641
theorem B4718951 : Blo 2095435 4718951 := bstep (se 1 (by rfl) ⟨3539213, by rfl⟩ : syracuseStep 4718951 = 7078427) B7078427
theorem B3145967 : Blo 2095435 3145967 := bstep (se 1 (by rfl) ⟨2359475, by rfl⟩ : syracuseStep 3145967 = 4718951) B4718951
theorem B2097311 : Blo 2095435 2097311 := bstep (se 1 (by rfl) ⟨1572983, by rfl⟩ : syracuseStep 2097311 = 3145967) B3145967
theorem B3145973 : Blo 2095435 3145973 := bbase (se 5 (by rfl) ⟨147467, by rfl⟩ : syracuseStep 3145973 = 294935) (by norm_num)
theorem B2097315 : Blo 2095435 2097315 := bstep (se 1 (by rfl) ⟨1572986, by rfl⟩ : syracuseStep 2097315 = 3145973) B3145973
theorem B2270225 : Blo 2095435 2270225 := bbase (se 2 (by rfl) ⟨851334, by rfl⟩ : syracuseStep 2270225 = 1702669) (by norm_num)
theorem B6053933 : Blo 2095435 6053933 := bstep (se 3 (by rfl) ⟨1135112, by rfl⟩ : syracuseStep 6053933 = 2270225) B2270225
theorem B4035955 : Blo 2095435 4035955 := bstep (se 1 (by rfl) ⟨3026966, by rfl⟩ : syracuseStep 4035955 = 6053933) B6053933
theorem B5381273 : Blo 2095435 5381273 := bstep (se 2 (by rfl) ⟨2017977, by rfl⟩ : syracuseStep 5381273 = 4035955) B4035955
theorem B14350061 : Blo 2095435 14350061 := bstep (se 3 (by rfl) ⟨2690636, by rfl⟩ : syracuseStep 14350061 = 5381273) B5381273
theorem B38266829 : Blo 2095435 38266829 := bstep (se 3 (by rfl) ⟨7175030, by rfl⟩ : syracuseStep 38266829 = 14350061) B14350061
theorem B25511219 : Blo 2095435 25511219 := bstep (se 1 (by rfl) ⟨19133414, by rfl⟩ : syracuseStep 25511219 = 38266829) B38266829
theorem B17007479 : Blo 2095435 17007479 := bstep (se 1 (by rfl) ⟨12755609, by rfl⟩ : syracuseStep 17007479 = 25511219) B25511219
theorem B11338319 : Blo 2095435 11338319 := bstep (se 1 (by rfl) ⟨8503739, by rfl⟩ : syracuseStep 11338319 = 17007479) B17007479
theorem B30235517 : Blo 2095435 30235517 := bstep (se 3 (by rfl) ⟨5669159, by rfl⟩ : syracuseStep 30235517 = 11338319) B11338319
theorem B20157011 : Blo 2095435 20157011 := bstep (se 1 (by rfl) ⟨15117758, by rfl⟩ : syracuseStep 20157011 = 30235517) B30235517
theorem B13438007 : Blo 2095435 13438007 := bstep (se 1 (by rfl) ⟨10078505, by rfl⟩ : syracuseStep 13438007 = 20157011) B20157011
theorem B8958671 : Blo 2095435 8958671 := bstep (se 1 (by rfl) ⟨6719003, by rfl⟩ : syracuseStep 8958671 = 13438007) B13438007
theorem B5972447 : Blo 2095435 5972447 := bstep (se 1 (by rfl) ⟨4479335, by rfl⟩ : syracuseStep 5972447 = 8958671) B8958671
theorem B3981631 : Blo 2095435 3981631 := bstep (se 1 (by rfl) ⟨2986223, by rfl⟩ : syracuseStep 3981631 = 5972447) B5972447
theorem B5308841 : Blo 2095435 5308841 := bstep (se 2 (by rfl) ⟨1990815, by rfl⟩ : syracuseStep 5308841 = 3981631) B3981631
theorem B3539227 : Blo 2095435 3539227 := bstep (se 1 (by rfl) ⟨2654420, by rfl⟩ : syracuseStep 3539227 = 5308841) B5308841
theorem B4718969 : Blo 2095435 4718969 := bstep (se 2 (by rfl) ⟨1769613, by rfl⟩ : syracuseStep 4718969 = 3539227) B3539227
theorem B3145979 : Blo 2095435 3145979 := bstep (se 1 (by rfl) ⟨2359484, by rfl⟩ : syracuseStep 3145979 = 4718969) B4718969
theorem B2097319 : Blo 2095435 2097319 := bstep (se 1 (by rfl) ⟨1572989, by rfl⟩ : syracuseStep 2097319 = 3145979) B3145979
theorem B2359489 : Blo 2095435 2359489 := bbase (se 2 (by rfl) ⟨884808, by rfl⟩ : syracuseStep 2359489 = 1769617) (by norm_num)
theorem B3145985 : Blo 2095435 3145985 := bstep (se 2 (by rfl) ⟨1179744, by rfl⟩ : syracuseStep 3145985 = 2359489) B2359489
theorem B2097323 : Blo 2095435 2097323 := bstep (se 1 (by rfl) ⟨1572992, by rfl⟩ : syracuseStep 2097323 = 3145985) B3145985
theorem B5308861 : Blo 2095435 5308861 := bbase (se 3 (by rfl) ⟨995411, by rfl⟩ : syracuseStep 5308861 = 1990823) (by norm_num)
theorem B7078481 : Blo 2095435 7078481 := bstep (se 2 (by rfl) ⟨2654430, by rfl⟩ : syracuseStep 7078481 = 5308861) B5308861
theorem B4718987 : Blo 2095435 4718987 := bstep (se 1 (by rfl) ⟨3539240, by rfl⟩ : syracuseStep 4718987 = 7078481) B7078481
theorem B3145991 : Blo 2095435 3145991 := bstep (se 1 (by rfl) ⟨2359493, by rfl⟩ : syracuseStep 3145991 = 4718987) B4718987
theorem B2097327 : Blo 2095435 2097327 := bstep (se 1 (by rfl) ⟨1572995, by rfl⟩ : syracuseStep 2097327 = 3145991) B3145991
theorem B3145997 : Blo 2095435 3145997 := bbase (se 3 (by rfl) ⟨589874, by rfl⟩ : syracuseStep 3145997 = 1179749) (by norm_num)
theorem B2097331 : Blo 2095435 2097331 := bstep (se 1 (by rfl) ⟨1572998, by rfl⟩ : syracuseStep 2097331 = 3145997) B3145997
theorem B4719005 : Blo 2095435 4719005 := bbase (se 3 (by rfl) ⟨884813, by rfl⟩ : syracuseStep 4719005 = 1769627) (by norm_num)
theorem B3146003 : Blo 2095435 3146003 := bstep (se 1 (by rfl) ⟨2359502, by rfl⟩ : syracuseStep 3146003 = 4719005) B4719005
theorem B2097335 : Blo 2095435 2097335 := bstep (se 1 (by rfl) ⟨1573001, by rfl⟩ : syracuseStep 2097335 = 3146003) B3146003
theorem B3539261 : Blo 2095435 3539261 := bbase (se 3 (by rfl) ⟨663611, by rfl⟩ : syracuseStep 3539261 = 1327223) (by norm_num)
theorem B2359507 : Blo 2095435 2359507 := bstep (se 1 (by rfl) ⟨1769630, by rfl⟩ : syracuseStep 2359507 = 3539261) B3539261
theorem B3146009 : Blo 2095435 3146009 := bstep (se 2 (by rfl) ⟨1179753, by rfl⟩ : syracuseStep 3146009 = 2359507) B2359507
theorem B2097339 : Blo 2095435 2097339 := bstep (se 1 (by rfl) ⟨1573004, by rfl⟩ : syracuseStep 2097339 = 3146009) B3146009
theorem B2239693 : Blo 2095435 2239693 := bbase (se 3 (by rfl) ⟨419942, by rfl⟩ : syracuseStep 2239693 = 839885) (by norm_num)
theorem B11945029 : Blo 2095435 11945029 := bstep (se 4 (by rfl) ⟨1119846, by rfl⟩ : syracuseStep 11945029 = 2239693) B2239693
theorem B15926705 : Blo 2095435 15926705 := bstep (se 2 (by rfl) ⟨5972514, by rfl⟩ : syracuseStep 15926705 = 11945029) B11945029
theorem B10617803 : Blo 2095435 10617803 := bstep (se 1 (by rfl) ⟨7963352, by rfl⟩ : syracuseStep 10617803 = 15926705) B15926705
theorem B7078535 : Blo 2095435 7078535 := bstep (se 1 (by rfl) ⟨5308901, by rfl⟩ : syracuseStep 7078535 = 10617803) B10617803
theorem B4719023 : Blo 2095435 4719023 := bstep (se 1 (by rfl) ⟨3539267, by rfl⟩ : syracuseStep 4719023 = 7078535) B7078535
theorem B3146015 : Blo 2095435 3146015 := bstep (se 1 (by rfl) ⟨2359511, by rfl⟩ : syracuseStep 3146015 = 4719023) B4719023
theorem B2097343 : Blo 2095435 2097343 := bstep (se 1 (by rfl) ⟨1573007, by rfl⟩ : syracuseStep 2097343 = 3146015) B3146015
theorem B3146021 : Blo 2095435 3146021 := bbase (se 4 (by rfl) ⟨294939, by rfl⟩ : syracuseStep 3146021 = 589879) (by norm_num)
theorem B2097347 : Blo 2095435 2097347 := bstep (se 1 (by rfl) ⟨1573010, by rfl⟩ : syracuseStep 2097347 = 3146021) B3146021
theorem B2654461 : Blo 2095435 2654461 := bbase (se 3 (by rfl) ⟨497711, by rfl⟩ : syracuseStep 2654461 = 995423) (by norm_num)
theorem B3539281 : Blo 2095435 3539281 := bstep (se 2 (by rfl) ⟨1327230, by rfl⟩ : syracuseStep 3539281 = 2654461) B2654461
theorem B4719041 : Blo 2095435 4719041 := bstep (se 2 (by rfl) ⟨1769640, by rfl⟩ : syracuseStep 4719041 = 3539281) B3539281
theorem B3146027 : Blo 2095435 3146027 := bstep (se 1 (by rfl) ⟨2359520, by rfl⟩ : syracuseStep 3146027 = 4719041) B4719041
theorem B2097351 : Blo 2095435 2097351 := bstep (se 1 (by rfl) ⟨1573013, by rfl⟩ : syracuseStep 2097351 = 3146027) B3146027
theorem B2359525 : Blo 2095435 2359525 := bbase (se 4 (by rfl) ⟨221205, by rfl⟩ : syracuseStep 2359525 = 442411) (by norm_num)
theorem B3146033 : Blo 2095435 3146033 := bstep (se 2 (by rfl) ⟨1179762, by rfl⟩ : syracuseStep 3146033 = 2359525) B2359525
theorem B2097355 : Blo 2095435 2097355 := bstep (se 1 (by rfl) ⟨1573016, by rfl⟩ : syracuseStep 2097355 = 3146033) B3146033
theorem B4479421 : Blo 2095435 4479421 := bbase (se 3 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 4479421 = 1679783) (by norm_num)
theorem B5972561 : Blo 2095435 5972561 := bstep (se 2 (by rfl) ⟨2239710, by rfl⟩ : syracuseStep 5972561 = 4479421) B4479421
theorem B3981707 : Blo 2095435 3981707 := bstep (se 1 (by rfl) ⟨2986280, by rfl⟩ : syracuseStep 3981707 = 5972561) B5972561
theorem B2654471 : Blo 2095435 2654471 := bstep (se 1 (by rfl) ⟨1990853, by rfl⟩ : syracuseStep 2654471 = 3981707) B3981707
theorem B7078589 : Blo 2095435 7078589 := bstep (se 3 (by rfl) ⟨1327235, by rfl⟩ : syracuseStep 7078589 = 2654471) B2654471
theorem B4719059 : Blo 2095435 4719059 := bstep (se 1 (by rfl) ⟨3539294, by rfl⟩ : syracuseStep 4719059 = 7078589) B7078589
theorem B3146039 : Blo 2095435 3146039 := bstep (se 1 (by rfl) ⟨2359529, by rfl⟩ : syracuseStep 3146039 = 4719059) B4719059
theorem B2097359 : Blo 2095435 2097359 := bstep (se 1 (by rfl) ⟨1573019, by rfl⟩ : syracuseStep 2097359 = 3146039) B3146039
theorem B3146045 : Blo 2095435 3146045 := bbase (se 3 (by rfl) ⟨589883, by rfl⟩ : syracuseStep 3146045 = 1179767) (by norm_num)
theorem B2097363 : Blo 2095435 2097363 := bstep (se 1 (by rfl) ⟨1573022, by rfl⟩ : syracuseStep 2097363 = 3146045) B3146045
theorem B4719077 : Blo 2095435 4719077 := bbase (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) (by norm_num)
theorem B3146051 : Blo 2095435 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B2097367 : Blo 2095435 2097367 := bstep (se 1 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 2097367 = 3146051) B3146051
theorem B5308973 : Blo 2095435 5308973 := bbase (se 3 (by rfl) ⟨995432, by rfl⟩ : syracuseStep 5308973 = 1990865) (by norm_num)
theorem B3539315 : Blo 2095435 3539315 := bstep (se 1 (by rfl) ⟨2654486, by rfl⟩ : syracuseStep 3539315 = 5308973) B5308973
theorem B2359543 : Blo 2095435 2359543 := bstep (se 1 (by rfl) ⟨1769657, by rfl⟩ : syracuseStep 2359543 = 3539315) B3539315
theorem B3146057 : Blo 2095435 3146057 := bstep (se 2 (by rfl) ⟨1179771, by rfl⟩ : syracuseStep 3146057 = 2359543) B2359543
theorem B2097371 : Blo 2095435 2097371 := bstep (se 1 (by rfl) ⟨1573028, by rfl⟩ : syracuseStep 2097371 = 3146057) B3146057
theorem B5177837 : Blo 2095435 5177837 := bbase (se 3 (by rfl) ⟨970844, by rfl⟩ : syracuseStep 5177837 = 1941689) (by norm_num)
theorem B3451891 : Blo 2095435 3451891 := bstep (se 1 (by rfl) ⟨2588918, by rfl⟩ : syracuseStep 3451891 = 5177837) B5177837
theorem B4602521 : Blo 2095435 4602521 := bstep (se 2 (by rfl) ⟨1725945, by rfl⟩ : syracuseStep 4602521 = 3451891) B3451891
theorem B12273389 : Blo 2095435 12273389 := bstep (se 3 (by rfl) ⟨2301260, by rfl⟩ : syracuseStep 12273389 = 4602521) B4602521
theorem B8182259 : Blo 2095435 8182259 := bstep (se 1 (by rfl) ⟨6136694, by rfl⟩ : syracuseStep 8182259 = 12273389) B12273389
theorem B5454839 : Blo 2095435 5454839 := bstep (se 1 (by rfl) ⟨4091129, by rfl⟩ : syracuseStep 5454839 = 8182259) B8182259
theorem B3636559 : Blo 2095435 3636559 := bstep (se 1 (by rfl) ⟨2727419, by rfl⟩ : syracuseStep 3636559 = 5454839) B5454839
theorem B4848745 : Blo 2095435 4848745 := bstep (se 2 (by rfl) ⟨1818279, by rfl⟩ : syracuseStep 4848745 = 3636559) B3636559
theorem B6464993 : Blo 2095435 6464993 := bstep (se 2 (by rfl) ⟨2424372, by rfl⟩ : syracuseStep 6464993 = 4848745) B4848745
theorem B17239981 : Blo 2095435 17239981 := bstep (se 3 (by rfl) ⟨3232496, by rfl⟩ : syracuseStep 17239981 = 6464993) B6464993
theorem B22986641 : Blo 2095435 22986641 := bstep (se 2 (by rfl) ⟨8619990, by rfl⟩ : syracuseStep 22986641 = 17239981) B17239981
theorem B15324427 : Blo 2095435 15324427 := bstep (se 1 (by rfl) ⟨11493320, by rfl⟩ : syracuseStep 15324427 = 22986641) B22986641
theorem B20432569 : Blo 2095435 20432569 := bstep (se 2 (by rfl) ⟨7662213, by rfl⟩ : syracuseStep 20432569 = 15324427) B15324427
theorem B27243425 : Blo 2095435 27243425 := bstep (se 2 (by rfl) ⟨10216284, by rfl⟩ : syracuseStep 27243425 = 20432569) B20432569
theorem B72649133 : Blo 2095435 72649133 := bstep (se 3 (by rfl) ⟨13621712, by rfl⟩ : syracuseStep 72649133 = 27243425) B27243425
theorem B48432755 : Blo 2095435 48432755 := bstep (se 1 (by rfl) ⟨36324566, by rfl⟩ : syracuseStep 48432755 = 72649133) B72649133
theorem B32288503 : Blo 2095435 32288503 := bstep (se 1 (by rfl) ⟨24216377, by rfl⟩ : syracuseStep 32288503 = 48432755) B48432755
theorem B43051337 : Blo 2095435 43051337 := bstep (se 2 (by rfl) ⟨16144251, by rfl⟩ : syracuseStep 43051337 = 32288503) B32288503
theorem B28700891 : Blo 2095435 28700891 := bstep (se 1 (by rfl) ⟨21525668, by rfl⟩ : syracuseStep 28700891 = 43051337) B43051337
theorem B19133927 : Blo 2095435 19133927 := bstep (se 1 (by rfl) ⟨14350445, by rfl⟩ : syracuseStep 19133927 = 28700891) B28700891
theorem B12755951 : Blo 2095435 12755951 := bstep (se 1 (by rfl) ⟨9566963, by rfl⟩ : syracuseStep 12755951 = 19133927) B19133927
theorem B8503967 : Blo 2095435 8503967 := bstep (se 1 (by rfl) ⟨6377975, by rfl⟩ : syracuseStep 8503967 = 12755951) B12755951
theorem B22677245 : Blo 2095435 22677245 := bstep (se 3 (by rfl) ⟨4251983, by rfl⟩ : syracuseStep 22677245 = 8503967) B8503967
theorem B15118163 : Blo 2095435 15118163 := bstep (se 1 (by rfl) ⟨11338622, by rfl⟩ : syracuseStep 15118163 = 22677245) B22677245
theorem B10078775 : Blo 2095435 10078775 := bstep (se 1 (by rfl) ⟨7559081, by rfl⟩ : syracuseStep 10078775 = 15118163) B15118163
theorem B6719183 : Blo 2095435 6719183 := bstep (se 1 (by rfl) ⟨5039387, by rfl⟩ : syracuseStep 6719183 = 10078775) B10078775
theorem B4479455 : Blo 2095435 4479455 := bstep (se 1 (by rfl) ⟨3359591, by rfl⟩ : syracuseStep 4479455 = 6719183) B6719183
theorem B2986303 : Blo 2095435 2986303 := bstep (se 1 (by rfl) ⟨2239727, by rfl⟩ : syracuseStep 2986303 = 4479455) B4479455
theorem B3981737 : Blo 2095435 3981737 := bstep (se 2 (by rfl) ⟨1493151, by rfl⟩ : syracuseStep 3981737 = 2986303) B2986303
theorem B10617965 : Blo 2095435 10617965 := bstep (se 3 (by rfl) ⟨1990868, by rfl⟩ : syracuseStep 10617965 = 3981737) B3981737
theorem B7078643 : Blo 2095435 7078643 := bstep (se 1 (by rfl) ⟨5308982, by rfl⟩ : syracuseStep 7078643 = 10617965) B10617965
theorem B4719095 : Blo 2095435 4719095 := bstep (se 1 (by rfl) ⟨3539321, by rfl⟩ : syracuseStep 4719095 = 7078643) B7078643
theorem B3146063 : Blo 2095435 3146063 := bstep (se 1 (by rfl) ⟨2359547, by rfl⟩ : syracuseStep 3146063 = 4719095) B4719095
theorem B2097375 : Blo 2095435 2097375 := bstep (se 1 (by rfl) ⟨1573031, by rfl⟩ : syracuseStep 2097375 = 3146063) B3146063
theorem B3146069 : Blo 2095435 3146069 := bbase (se 10 (by rfl) ⟨4608, by rfl⟩ : syracuseStep 3146069 = 9217) (by norm_num)
theorem B2097379 : Blo 2095435 2097379 := bstep (se 1 (by rfl) ⟨1573034, by rfl⟩ : syracuseStep 2097379 = 3146069) B3146069
theorem B5972629 : Blo 2095435 5972629 := bbase (se 6 (by rfl) ⟨139983, by rfl⟩ : syracuseStep 5972629 = 279967) (by norm_num)
theorem B7963505 : Blo 2095435 7963505 := bstep (se 2 (by rfl) ⟨2986314, by rfl⟩ : syracuseStep 7963505 = 5972629) B5972629
theorem B5309003 : Blo 2095435 5309003 := bstep (se 1 (by rfl) ⟨3981752, by rfl⟩ : syracuseStep 5309003 = 7963505) B7963505
theorem B3539335 : Blo 2095435 3539335 := bstep (se 1 (by rfl) ⟨2654501, by rfl⟩ : syracuseStep 3539335 = 5309003) B5309003
theorem B4719113 : Blo 2095435 4719113 := bstep (se 2 (by rfl) ⟨1769667, by rfl⟩ : syracuseStep 4719113 = 3539335) B3539335
theorem B3146075 : Blo 2095435 3146075 := bstep (se 1 (by rfl) ⟨2359556, by rfl⟩ : syracuseStep 3146075 = 4719113) B4719113
theorem B2097383 : Blo 2095435 2097383 := bstep (se 1 (by rfl) ⟨1573037, by rfl⟩ : syracuseStep 2097383 = 3146075) B3146075
theorem B2359561 : Blo 2095435 2359561 := bbase (se 2 (by rfl) ⟨884835, by rfl⟩ : syracuseStep 2359561 = 1769671) (by norm_num)
theorem B3146081 : Blo 2095435 3146081 := bstep (se 2 (by rfl) ⟨1179780, by rfl⟩ : syracuseStep 3146081 = 2359561) B2359561
theorem B2097387 : Blo 2095435 2097387 := bstep (se 1 (by rfl) ⟨1573040, by rfl⟩ : syracuseStep 2097387 = 3146081) B3146081
theorem B2834677 : Blo 2095435 2834677 := bbase (se 5 (by rfl) ⟨132875, by rfl⟩ : syracuseStep 2834677 = 265751) (by norm_num)
theorem B3779569 : Blo 2095435 3779569 := bstep (se 2 (by rfl) ⟨1417338, by rfl⟩ : syracuseStep 3779569 = 2834677) B2834677
theorem B5039425 : Blo 2095435 5039425 := bstep (se 2 (by rfl) ⟨1889784, by rfl⟩ : syracuseStep 5039425 = 3779569) B3779569
theorem B26876933 : Blo 2095435 26876933 := bstep (se 4 (by rfl) ⟨2519712, by rfl⟩ : syracuseStep 26876933 = 5039425) B5039425
theorem B17917955 : Blo 2095435 17917955 := bstep (se 1 (by rfl) ⟨13438466, by rfl⟩ : syracuseStep 17917955 = 26876933) B26876933
theorem B11945303 : Blo 2095435 11945303 := bstep (se 1 (by rfl) ⟨8958977, by rfl⟩ : syracuseStep 11945303 = 17917955) B17917955
theorem B7963535 : Blo 2095435 7963535 := bstep (se 1 (by rfl) ⟨5972651, by rfl⟩ : syracuseStep 7963535 = 11945303) B11945303
theorem B5309023 : Blo 2095435 5309023 := bstep (se 1 (by rfl) ⟨3981767, by rfl⟩ : syracuseStep 5309023 = 7963535) B7963535
theorem B7078697 : Blo 2095435 7078697 := bstep (se 2 (by rfl) ⟨2654511, by rfl⟩ : syracuseStep 7078697 = 5309023) B5309023
theorem B4719131 : Blo 2095435 4719131 := bstep (se 1 (by rfl) ⟨3539348, by rfl⟩ : syracuseStep 4719131 = 7078697) B7078697
theorem B3146087 : Blo 2095435 3146087 := bstep (se 1 (by rfl) ⟨2359565, by rfl⟩ : syracuseStep 3146087 = 4719131) B4719131
theorem B2097391 : Blo 2095435 2097391 := bstep (se 1 (by rfl) ⟨1573043, by rfl⟩ : syracuseStep 2097391 = 3146087) B3146087
theorem B3146093 : Blo 2095435 3146093 := bbase (se 3 (by rfl) ⟨589892, by rfl⟩ : syracuseStep 3146093 = 1179785) (by norm_num)
theorem B2097395 : Blo 2095435 2097395 := bstep (se 1 (by rfl) ⟨1573046, by rfl⟩ : syracuseStep 2097395 = 3146093) B3146093
theorem B4719149 : Blo 2095435 4719149 := bbase (se 3 (by rfl) ⟨884840, by rfl⟩ : syracuseStep 4719149 = 1769681) (by norm_num)
theorem B3146099 : Blo 2095435 3146099 := bstep (se 1 (by rfl) ⟨2359574, by rfl⟩ : syracuseStep 3146099 = 4719149) B4719149
theorem B2097399 : Blo 2095435 2097399 := bstep (se 1 (by rfl) ⟨1573049, by rfl⟩ : syracuseStep 2097399 = 3146099) B3146099
theorem B2391773 : Blo 2095435 2391773 := bbase (se 3 (by rfl) ⟨448457, by rfl⟩ : syracuseStep 2391773 = 896915) (by norm_num)
theorem B25512245 : Blo 2095435 25512245 := bstep (se 5 (by rfl) ⟨1195886, by rfl⟩ : syracuseStep 25512245 = 2391773) B2391773
theorem B17008163 : Blo 2095435 17008163 := bstep (se 1 (by rfl) ⟨12756122, by rfl⟩ : syracuseStep 17008163 = 25512245) B25512245
theorem B11338775 : Blo 2095435 11338775 := bstep (se 1 (by rfl) ⟨8504081, by rfl⟩ : syracuseStep 11338775 = 17008163) B17008163
theorem B7559183 : Blo 2095435 7559183 := bstep (se 1 (by rfl) ⟨5669387, by rfl⟩ : syracuseStep 7559183 = 11338775) B11338775
theorem B20157821 : Blo 2095435 20157821 := bstep (se 3 (by rfl) ⟨3779591, by rfl⟩ : syracuseStep 20157821 = 7559183) B7559183
theorem B13438547 : Blo 2095435 13438547 := bstep (se 1 (by rfl) ⟨10078910, by rfl⟩ : syracuseStep 13438547 = 20157821) B20157821
theorem B8959031 : Blo 2095435 8959031 := bstep (se 1 (by rfl) ⟨6719273, by rfl⟩ : syracuseStep 8959031 = 13438547) B13438547
theorem B5972687 : Blo 2095435 5972687 := bstep (se 1 (by rfl) ⟨4479515, by rfl⟩ : syracuseStep 5972687 = 8959031) B8959031
theorem B3981791 : Blo 2095435 3981791 := bstep (se 1 (by rfl) ⟨2986343, by rfl⟩ : syracuseStep 3981791 = 5972687) B5972687
theorem B2654527 : Blo 2095435 2654527 := bstep (se 1 (by rfl) ⟨1990895, by rfl⟩ : syracuseStep 2654527 = 3981791) B3981791
theorem B3539369 : Blo 2095435 3539369 := bstep (se 2 (by rfl) ⟨1327263, by rfl⟩ : syracuseStep 3539369 = 2654527) B2654527
theorem B2359579 : Blo 2095435 2359579 := bstep (se 1 (by rfl) ⟨1769684, by rfl⟩ : syracuseStep 2359579 = 3539369) B3539369
theorem B3146105 : Blo 2095435 3146105 := bstep (se 2 (by rfl) ⟨1179789, by rfl⟩ : syracuseStep 3146105 = 2359579) B2359579
theorem B2097403 : Blo 2095435 2097403 := bstep (se 1 (by rfl) ⟨1573052, by rfl⟩ : syracuseStep 2097403 = 3146105) B3146105
theorem B35836181 : Blo 2095435 35836181 := bbase (se 6 (by rfl) ⟨839910, by rfl⟩ : syracuseStep 35836181 = 1679821) (by norm_num)
theorem B23890787 : Blo 2095435 23890787 := bstep (se 1 (by rfl) ⟨17918090, by rfl⟩ : syracuseStep 23890787 = 35836181) B35836181
theorem B15927191 : Blo 2095435 15927191 := bstep (se 1 (by rfl) ⟨11945393, by rfl⟩ : syracuseStep 15927191 = 23890787) B23890787
theorem B10618127 : Blo 2095435 10618127 := bstep (se 1 (by rfl) ⟨7963595, by rfl⟩ : syracuseStep 10618127 = 15927191) B15927191
theorem B7078751 : Blo 2095435 7078751 := bstep (se 1 (by rfl) ⟨5309063, by rfl⟩ : syracuseStep 7078751 = 10618127) B10618127
theorem B4719167 : Blo 2095435 4719167 := bstep (se 1 (by rfl) ⟨3539375, by rfl⟩ : syracuseStep 4719167 = 7078751) B7078751
theorem B3146111 : Blo 2095435 3146111 := bstep (se 1 (by rfl) ⟨2359583, by rfl⟩ : syracuseStep 3146111 = 4719167) B4719167
theorem B2097407 : Blo 2095435 2097407 := bstep (se 1 (by rfl) ⟨1573055, by rfl⟩ : syracuseStep 2097407 = 3146111) B3146111
theorem B3146117 : Blo 2095435 3146117 := bbase (se 4 (by rfl) ⟨294948, by rfl⟩ : syracuseStep 3146117 = 589897) (by norm_num)
theorem B2097411 : Blo 2095435 2097411 := bstep (se 1 (by rfl) ⟨1573058, by rfl⟩ : syracuseStep 2097411 = 3146117) B3146117
theorem B3539389 : Blo 2095435 3539389 := bbase (se 3 (by rfl) ⟨663635, by rfl⟩ : syracuseStep 3539389 = 1327271) (by norm_num)
theorem B4719185 : Blo 2095435 4719185 := bstep (se 2 (by rfl) ⟨1769694, by rfl⟩ : syracuseStep 4719185 = 3539389) B3539389
theorem B3146123 : Blo 2095435 3146123 := bstep (se 1 (by rfl) ⟨2359592, by rfl⟩ : syracuseStep 3146123 = 4719185) B4719185
theorem B2097415 : Blo 2095435 2097415 := bstep (se 1 (by rfl) ⟨1573061, by rfl⟩ : syracuseStep 2097415 = 3146123) B3146123
theorem B2359597 : Blo 2095435 2359597 := bbase (se 3 (by rfl) ⟨442424, by rfl⟩ : syracuseStep 2359597 = 884849) (by norm_num)
theorem B3146129 : Blo 2095435 3146129 := bstep (se 2 (by rfl) ⟨1179798, by rfl⟩ : syracuseStep 3146129 = 2359597) B2359597
theorem B2097419 : Blo 2095435 2097419 := bstep (se 1 (by rfl) ⟨1573064, by rfl⟩ : syracuseStep 2097419 = 3146129) B3146129
theorem B7078805 : Blo 2095435 7078805 := bbase (se 6 (by rfl) ⟨165909, by rfl⟩ : syracuseStep 7078805 = 331819) (by norm_num)
theorem B4719203 : Blo 2095435 4719203 := bstep (se 1 (by rfl) ⟨3539402, by rfl⟩ : syracuseStep 4719203 = 7078805) B7078805
theorem B3146135 : Blo 2095435 3146135 := bstep (se 1 (by rfl) ⟨2359601, by rfl⟩ : syracuseStep 3146135 = 4719203) B4719203
theorem B2097423 : Blo 2095435 2097423 := bstep (se 1 (by rfl) ⟨1573067, by rfl⟩ : syracuseStep 2097423 = 3146135) B3146135
theorem B3146141 : Blo 2095435 3146141 := bbase (se 3 (by rfl) ⟨589901, by rfl⟩ : syracuseStep 3146141 = 1179803) (by norm_num)
theorem B2097427 : Blo 2095435 2097427 := bstep (se 1 (by rfl) ⟨1573070, by rfl⟩ : syracuseStep 2097427 = 3146141) B3146141
theorem B4719221 : Blo 2095435 4719221 := bbase (se 5 (by rfl) ⟨221213, by rfl⟩ : syracuseStep 4719221 = 442427) (by norm_num)
theorem B3146147 : Blo 2095435 3146147 := bstep (se 1 (by rfl) ⟨2359610, by rfl⟩ : syracuseStep 3146147 = 4719221) B4719221
theorem B2097431 : Blo 2095435 2097431 := bstep (se 1 (by rfl) ⟨1573073, by rfl⟩ : syracuseStep 2097431 = 3146147) B3146147
theorem B7175429 : Blo 2095435 7175429 := bbase (se 4 (by rfl) ⟨672696, by rfl⟩ : syracuseStep 7175429 = 1345393) (by norm_num)
theorem B4783619 : Blo 2095435 4783619 := bstep (se 1 (by rfl) ⟨3587714, by rfl⟩ : syracuseStep 4783619 = 7175429) B7175429
theorem B3189079 : Blo 2095435 3189079 := bstep (se 1 (by rfl) ⟨2391809, by rfl⟩ : syracuseStep 3189079 = 4783619) B4783619
theorem B4252105 : Blo 2095435 4252105 := bstep (se 2 (by rfl) ⟨1594539, by rfl⟩ : syracuseStep 4252105 = 3189079) B3189079
theorem B22677893 : Blo 2095435 22677893 := bstep (se 4 (by rfl) ⟨2126052, by rfl⟩ : syracuseStep 22677893 = 4252105) B4252105
theorem B15118595 : Blo 2095435 15118595 := bstep (se 1 (by rfl) ⟨11338946, by rfl⟩ : syracuseStep 15118595 = 22677893) B22677893
theorem B10079063 : Blo 2095435 10079063 := bstep (se 1 (by rfl) ⟨7559297, by rfl⟩ : syracuseStep 10079063 = 15118595) B15118595
theorem B6719375 : Blo 2095435 6719375 := bstep (se 1 (by rfl) ⟨5039531, by rfl⟩ : syracuseStep 6719375 = 10079063) B10079063
theorem B17918333 : Blo 2095435 17918333 := bstep (se 3 (by rfl) ⟨3359687, by rfl⟩ : syracuseStep 17918333 = 6719375) B6719375
theorem B11945555 : Blo 2095435 11945555 := bstep (se 1 (by rfl) ⟨8959166, by rfl⟩ : syracuseStep 11945555 = 17918333) B17918333
theorem B7963703 : Blo 2095435 7963703 := bstep (se 1 (by rfl) ⟨5972777, by rfl⟩ : syracuseStep 7963703 = 11945555) B11945555
theorem B5309135 : Blo 2095435 5309135 := bstep (se 1 (by rfl) ⟨3981851, by rfl⟩ : syracuseStep 5309135 = 7963703) B7963703
theorem B3539423 : Blo 2095435 3539423 := bstep (se 1 (by rfl) ⟨2654567, by rfl⟩ : syracuseStep 3539423 = 5309135) B5309135
theorem B2359615 : Blo 2095435 2359615 := bstep (se 1 (by rfl) ⟨1769711, by rfl⟩ : syracuseStep 2359615 = 3539423) B3539423
theorem B3146153 : Blo 2095435 3146153 := bstep (se 2 (by rfl) ⟨1179807, by rfl⟩ : syracuseStep 3146153 = 2359615) B2359615
theorem B2097435 : Blo 2095435 2097435 := bstep (se 1 (by rfl) ⟨1573076, by rfl⟩ : syracuseStep 2097435 = 3146153) B3146153
theorem C0 (j : ℕ) (h1 : 523858 ≤ j) (h2 : j ≤ 524358) : Blo 2095435 (4 * j + 3) := by
  interval_cases j
  · exact B2095435
  · exact B2095439
  · exact B2095443
  · exact B2095447
  · exact B2095451
  · exact B2095455
  · exact B2095459
  · exact B2095463
  · exact B2095467
  · exact B2095471
  · exact B2095475
  · exact B2095479
  · exact B2095483
  · exact B2095487
  · exact B2095491
  · exact B2095495
  · exact B2095499
  · exact B2095503
  · exact B2095507
  · exact B2095511
  · exact B2095515
  · exact B2095519
  · exact B2095523
  · exact B2095527
  · exact B2095531
  · exact B2095535
  · exact B2095539
  · exact B2095543
  · exact B2095547
  · exact B2095551
  · exact B2095555
  · exact B2095559
  · exact B2095563
  · exact B2095567
  · exact B2095571
  · exact B2095575
  · exact B2095579
  · exact B2095583
  · exact B2095587
  · exact B2095591
  · exact B2095595
  · exact B2095599
  · exact B2095603
  · exact B2095607
  · exact B2095611
  · exact B2095615
  · exact B2095619
  · exact B2095623
  · exact B2095627
  · exact B2095631
  · exact B2095635
  · exact B2095639
  · exact B2095643
  · exact B2095647
  · exact B2095651
  · exact B2095655
  · exact B2095659
  · exact B2095663
  · exact B2095667
  · exact B2095671
  · exact B2095675
  · exact B2095679
  · exact B2095683
  · exact B2095687
  · exact B2095691
  · exact B2095695
  · exact B2095699
  · exact B2095703
  · exact B2095707
  · exact B2095711
  · exact B2095715
  · exact B2095719
  · exact B2095723
  · exact B2095727
  · exact B2095731
  · exact B2095735
  · exact B2095739
  · exact B2095743
  · exact B2095747
  · exact B2095751
  · exact B2095755
  · exact B2095759
  · exact B2095763
  · exact B2095767
  · exact B2095771
  · exact B2095775
  · exact B2095779
  · exact B2095783
  · exact B2095787
  · exact B2095791
  · exact B2095795
  · exact B2095799
  · exact B2095803
  · exact B2095807
  · exact B2095811
  · exact B2095815
  · exact B2095819
  · exact B2095823
  · exact B2095827
  · exact B2095831
  · exact B2095835
  · exact B2095839
  · exact B2095843
  · exact B2095847
  · exact B2095851
  · exact B2095855
  · exact B2095859
  · exact B2095863
  · exact B2095867
  · exact B2095871
  · exact B2095875
  · exact B2095879
  · exact B2095883
  · exact B2095887
  · exact B2095891
  · exact B2095895
  · exact B2095899
  · exact B2095903
  · exact B2095907
  · exact B2095911
  · exact B2095915
  · exact B2095919
  · exact B2095923
  · exact B2095927
  · exact B2095931
  · exact B2095935
  · exact B2095939
  · exact B2095943
  · exact B2095947
  · exact B2095951
  · exact B2095955
  · exact B2095959
  · exact B2095963
  · exact B2095967
  · exact B2095971
  · exact B2095975
  · exact B2095979
  · exact B2095983
  · exact B2095987
  · exact B2095991
  · exact B2095995
  · exact B2095999
  · exact B2096003
  · exact B2096007
  · exact B2096011
  · exact B2096015
  · exact B2096019
  · exact B2096023
  · exact B2096027
  · exact B2096031
  · exact B2096035
  · exact B2096039
  · exact B2096043
  · exact B2096047
  · exact B2096051
  · exact B2096055
  · exact B2096059
  · exact B2096063
  · exact B2096067
  · exact B2096071
  · exact B2096075
  · exact B2096079
  · exact B2096083
  · exact B2096087
  · exact B2096091
  · exact B2096095
  · exact B2096099
  · exact B2096103
  · exact B2096107
  · exact B2096111
  · exact B2096115
  · exact B2096119
  · exact B2096123
  · exact B2096127
  · exact B2096131
  · exact B2096135
  · exact B2096139
  · exact B2096143
  · exact B2096147
  · exact B2096151
  · exact B2096155
  · exact B2096159
  · exact B2096163
  · exact B2096167
  · exact B2096171
  · exact B2096175
  · exact B2096179
  · exact B2096183
  · exact B2096187
  · exact B2096191
  · exact B2096195
  · exact B2096199
  · exact B2096203
  · exact B2096207
  · exact B2096211
  · exact B2096215
  · exact B2096219
  · exact B2096223
  · exact B2096227
  · exact B2096231
  · exact B2096235
  · exact B2096239
  · exact B2096243
  · exact B2096247
  · exact B2096251
  · exact B2096255
  · exact B2096259
  · exact B2096263
  · exact B2096267
  · exact B2096271
  · exact B2096275
  · exact B2096279
  · exact B2096283
  · exact B2096287
  · exact B2096291
  · exact B2096295
  · exact B2096299
  · exact B2096303
  · exact B2096307
  · exact B2096311
  · exact B2096315
  · exact B2096319
  · exact B2096323
  · exact B2096327
  · exact B2096331
  · exact B2096335
  · exact B2096339
  · exact B2096343
  · exact B2096347
  · exact B2096351
  · exact B2096355
  · exact B2096359
  · exact B2096363
  · exact B2096367
  · exact B2096371
  · exact B2096375
  · exact B2096379
  · exact B2096383
  · exact B2096387
  · exact B2096391
  · exact B2096395
  · exact B2096399
  · exact B2096403
  · exact B2096407
  · exact B2096411
  · exact B2096415
  · exact B2096419
  · exact B2096423
  · exact B2096427
  · exact B2096431
  · exact B2096435
  · exact B2096439
  · exact B2096443
  · exact B2096447
  · exact B2096451
  · exact B2096455
  · exact B2096459
  · exact B2096463
  · exact B2096467
  · exact B2096471
  · exact B2096475
  · exact B2096479
  · exact B2096483
  · exact B2096487
  · exact B2096491
  · exact B2096495
  · exact B2096499
  · exact B2096503
  · exact B2096507
  · exact B2096511
  · exact B2096515
  · exact B2096519
  · exact B2096523
  · exact B2096527
  · exact B2096531
  · exact B2096535
  · exact B2096539
  · exact B2096543
  · exact B2096547
  · exact B2096551
  · exact B2096555
  · exact B2096559
  · exact B2096563
  · exact B2096567
  · exact B2096571
  · exact B2096575
  · exact B2096579
  · exact B2096583
  · exact B2096587
  · exact B2096591
  · exact B2096595
  · exact B2096599
  · exact B2096603
  · exact B2096607
  · exact B2096611
  · exact B2096615
  · exact B2096619
  · exact B2096623
  · exact B2096627
  · exact B2096631
  · exact B2096635
  · exact B2096639
  · exact B2096643
  · exact B2096647
  · exact B2096651
  · exact B2096655
  · exact B2096659
  · exact B2096663
  · exact B2096667
  · exact B2096671
  · exact B2096675
  · exact B2096679
  · exact B2096683
  · exact B2096687
  · exact B2096691
  · exact B2096695
  · exact B2096699
  · exact B2096703
  · exact B2096707
  · exact B2096711
  · exact B2096715
  · exact B2096719
  · exact B2096723
  · exact B2096727
  · exact B2096731
  · exact B2096735
  · exact B2096739
  · exact B2096743
  · exact B2096747
  · exact B2096751
  · exact B2096755
  · exact B2096759
  · exact B2096763
  · exact B2096767
  · exact B2096771
  · exact B2096775
  · exact B2096779
  · exact B2096783
  · exact B2096787
  · exact B2096791
  · exact B2096795
  · exact B2096799
  · exact B2096803
  · exact B2096807
  · exact B2096811
  · exact B2096815
  · exact B2096819
  · exact B2096823
  · exact B2096827
  · exact B2096831
  · exact B2096835
  · exact B2096839
  · exact B2096843
  · exact B2096847
  · exact B2096851
  · exact B2096855
  · exact B2096859
  · exact B2096863
  · exact B2096867
  · exact B2096871
  · exact B2096875
  · exact B2096879
  · exact B2096883
  · exact B2096887
  · exact B2096891
  · exact B2096895
  · exact B2096899
  · exact B2096903
  · exact B2096907
  · exact B2096911
  · exact B2096915
  · exact B2096919
  · exact B2096923
  · exact B2096927
  · exact B2096931
  · exact B2096935
  · exact B2096939
  · exact B2096943
  · exact B2096947
  · exact B2096951
  · exact B2096955
  · exact B2096959
  · exact B2096963
  · exact B2096967
  · exact B2096971
  · exact B2096975
  · exact B2096979
  · exact B2096983
  · exact B2096987
  · exact B2096991
  · exact B2096995
  · exact B2096999
  · exact B2097003
  · exact B2097007
  · exact B2097011
  · exact B2097015
  · exact B2097019
  · exact B2097023
  · exact B2097027
  · exact B2097031
  · exact B2097035
  · exact B2097039
  · exact B2097043
  · exact B2097047
  · exact B2097051
  · exact B2097055
  · exact B2097059
  · exact B2097063
  · exact B2097067
  · exact B2097071
  · exact B2097075
  · exact B2097079
  · exact B2097083
  · exact B2097087
  · exact B2097091
  · exact B2097095
  · exact B2097099
  · exact B2097103
  · exact B2097107
  · exact B2097111
  · exact B2097115
  · exact B2097119
  · exact B2097123
  · exact B2097127
  · exact B2097131
  · exact B2097135
  · exact B2097139
  · exact B2097143
  · exact B2097147
  · exact B2097151
  · exact B2097155
  · exact B2097159
  · exact B2097163
  · exact B2097167
  · exact B2097171
  · exact B2097175
  · exact B2097179
  · exact B2097183
  · exact B2097187
  · exact B2097191
  · exact B2097195
  · exact B2097199
  · exact B2097203
  · exact B2097207
  · exact B2097211
  · exact B2097215
  · exact B2097219
  · exact B2097223
  · exact B2097227
  · exact B2097231
  · exact B2097235
  · exact B2097239
  · exact B2097243
  · exact B2097247
  · exact B2097251
  · exact B2097255
  · exact B2097259
  · exact B2097263
  · exact B2097267
  · exact B2097271
  · exact B2097275
  · exact B2097279
  · exact B2097283
  · exact B2097287
  · exact B2097291
  · exact B2097295
  · exact B2097299
  · exact B2097303
  · exact B2097307
  · exact B2097311
  · exact B2097315
  · exact B2097319
  · exact B2097323
  · exact B2097327
  · exact B2097331
  · exact B2097335
  · exact B2097339
  · exact B2097343
  · exact B2097347
  · exact B2097351
  · exact B2097355
  · exact B2097359
  · exact B2097363
  · exact B2097367
  · exact B2097371
  · exact B2097375
  · exact B2097379
  · exact B2097383
  · exact B2097387
  · exact B2097391
  · exact B2097395
  · exact B2097399
  · exact B2097403
  · exact B2097407
  · exact B2097411
  · exact B2097415
  · exact B2097419
  · exact B2097423
  · exact B2097427
  · exact B2097431
  · exact B2097435
theorem solution (m : ℕ) (hlo : 2095435 ≤ m) (hhi : m ≤ 2097435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 523858 ≤ j := by omega
    have hj2 : j ≤ 524358 := by omega
    have hb : Blo 2095435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
