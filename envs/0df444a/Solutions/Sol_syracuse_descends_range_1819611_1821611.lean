-- Prove2me | solution 1 for syracuse_descends_range_1819611_1821611
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:56:12.260287+00:00
-- url     : https://prove2.me/submissions/52f581b0-2f04-40ce-8610-48c2e8d71164

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


theorem B2048017 : Blo 1819611 2048017 := bbase (se 2 (by rfl) ⟨768006, by rfl⟩ : syracuseStep 2048017 = 1536013) (by norm_num)
theorem B3072053 : Blo 1819611 3072053 := bbase (se 5 (by rfl) ⟨144002, by rfl⟩ : syracuseStep 3072053 = 288005) (by norm_num)
theorem B2048053 : Blo 1819611 2048053 := bbase (se 5 (by rfl) ⟨96002, by rfl⟩ : syracuseStep 2048053 = 192005) (by norm_num)
theorem B4096061 : Blo 1819611 4096061 := bbase (se 3 (by rfl) ⟨768011, by rfl⟩ : syracuseStep 4096061 = 1536023) (by norm_num)
theorem B3457093 : Blo 1819611 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B2048089 : Blo 1819611 2048089 := bbase (se 2 (by rfl) ⟨768033, by rfl⟩ : syracuseStep 2048089 = 1536067) (by norm_num)
theorem B2187361 : Blo 1819611 2187361 := bbase (se 2 (by rfl) ⟨820260, by rfl⟩ : syracuseStep 2187361 = 1640521) (by norm_num)
theorem B2048125 : Blo 1819611 2048125 := bbase (se 3 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 2048125 = 768047) (by norm_num)
theorem B4096133 : Blo 1819611 4096133 := bbase (se 4 (by rfl) ⟨384012, by rfl⟩ : syracuseStep 4096133 = 768025) (by norm_num)
theorem B2048161 : Blo 1819611 2048161 := bbase (se 2 (by rfl) ⟨768060, by rfl⟩ : syracuseStep 2048161 = 1536121) (by norm_num)
theorem B3072181 : Blo 1819611 3072181 := bbase (se 5 (by rfl) ⟨144008, by rfl⟩ : syracuseStep 3072181 = 288017) (by norm_num)
theorem B2048197 : Blo 1819611 2048197 := bbase (se 4 (by rfl) ⟨192018, by rfl⟩ : syracuseStep 2048197 = 384037) (by norm_num)
theorem B4096205 : Blo 1819611 4096205 := bbase (se 3 (by rfl) ⟨768038, by rfl⟩ : syracuseStep 4096205 = 1536077) (by norm_num)
theorem B6914261 : Blo 1819611 6914261 := bbase (se 7 (by rfl) ⟨81026, by rfl⟩ : syracuseStep 6914261 = 162053) (by norm_num)
theorem B3457237 : Blo 1819611 3457237 := bbase (se 7 (by rfl) ⟨40514, by rfl⟩ : syracuseStep 3457237 = 81029) (by norm_num)
theorem B2048233 : Blo 1819611 2048233 := bbase (se 2 (by rfl) ⟨768087, by rfl⟩ : syracuseStep 2048233 = 1536175) (by norm_num)
theorem B3072269 : Blo 1819611 3072269 := bbase (se 3 (by rfl) ⟨576050, by rfl⟩ : syracuseStep 3072269 = 1152101) (by norm_num)
theorem B2048269 : Blo 1819611 2048269 := bbase (se 3 (by rfl) ⟨384050, by rfl⟩ : syracuseStep 2048269 = 768101) (by norm_num)
theorem B4096277 : Blo 1819611 4096277 := bbase (se 6 (by rfl) ⟨96006, by rfl⟩ : syracuseStep 4096277 = 192013) (by norm_num)
theorem B2187553 : Blo 1819611 2187553 := bbase (se 2 (by rfl) ⟨820332, by rfl⟩ : syracuseStep 2187553 = 1640665) (by norm_num)
theorem B2048305 : Blo 1819611 2048305 := bbase (se 2 (by rfl) ⟨768114, by rfl⟩ : syracuseStep 2048305 = 1536229) (by norm_num)
theorem B2187577 : Blo 1819611 2187577 := bbase (se 2 (by rfl) ⟨820341, by rfl⟩ : syracuseStep 2187577 = 1640683) (by norm_num)
theorem B2187581 : Blo 1819611 2187581 := bbase (se 3 (by rfl) ⟨410171, by rfl⟩ : syracuseStep 2187581 = 820343) (by norm_num)
theorem B9216341 : Blo 1819611 9216341 := bbase (se 10 (by rfl) ⟨13500, by rfl⟩ : syracuseStep 9216341 = 27001) (by norm_num)
theorem B2048341 : Blo 1819611 2048341 := bbase (se 10 (by rfl) ⟨3000, by rfl⟩ : syracuseStep 2048341 = 6001) (by norm_num)
theorem B4096349 : Blo 1819611 4096349 := bbase (se 3 (by rfl) ⟨768065, by rfl⟩ : syracuseStep 4096349 = 1536131) (by norm_num)
theorem B3457397 : Blo 1819611 3457397 := bbase (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) (by norm_num)
theorem B2048377 : Blo 1819611 2048377 := bbase (se 2 (by rfl) ⟨768141, by rfl⟩ : syracuseStep 2048377 = 1536283) (by norm_num)
theorem B6144389 : Blo 1819611 6144389 := bbase (se 4 (by rfl) ⟨576036, by rfl⟩ : syracuseStep 6144389 = 1152073) (by norm_num)
theorem B3072397 : Blo 1819611 3072397 := bbase (se 3 (by rfl) ⟨576074, by rfl⟩ : syracuseStep 3072397 = 1152149) (by norm_num)
theorem B2048413 : Blo 1819611 2048413 := bbase (se 3 (by rfl) ⟨384077, by rfl⟩ : syracuseStep 2048413 = 768155) (by norm_num)
theorem B4096421 : Blo 1819611 4096421 := bbase (se 4 (by rfl) ⟨384039, by rfl⟩ : syracuseStep 4096421 = 768079) (by norm_num)
theorem B2048449 : Blo 1819611 2048449 := bbase (se 2 (by rfl) ⟨768168, by rfl⟩ : syracuseStep 2048449 = 1536337) (by norm_num)
theorem B2769365 : Blo 1819611 2769365 := bbase (se 7 (by rfl) ⟨32453, by rfl⟩ : syracuseStep 2769365 = 64907) (by norm_num)
theorem B3072485 : Blo 1819611 3072485 := bbase (se 4 (by rfl) ⟨288045, by rfl⟩ : syracuseStep 3072485 = 576091) (by norm_num)
theorem B2048485 : Blo 1819611 2048485 := bbase (se 4 (by rfl) ⟨192045, by rfl⟩ : syracuseStep 2048485 = 384091) (by norm_num)
theorem B4096493 : Blo 1819611 4096493 := bbase (se 3 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 4096493 = 1536185) (by norm_num)
theorem B8864261 : Blo 1819611 8864261 := bbase (se 4 (by rfl) ⟨831024, by rfl⟩ : syracuseStep 8864261 = 1662049) (by norm_num)
theorem B3457541 : Blo 1819611 3457541 := bbase (se 4 (by rfl) ⟨324144, by rfl⟩ : syracuseStep 3457541 = 648289) (by norm_num)
theorem B2048521 : Blo 1819611 2048521 := bbase (se 2 (by rfl) ⟨768195, by rfl⟩ : syracuseStep 2048521 = 1536391) (by norm_num)
theorem B2048557 : Blo 1819611 2048557 := bbase (se 3 (by rfl) ⟨384104, by rfl⟩ : syracuseStep 2048557 = 768209) (by norm_num)
theorem B4096565 : Blo 1819611 4096565 := bbase (se 5 (by rfl) ⟨192026, by rfl⟩ : syracuseStep 4096565 = 384053) (by norm_num)
theorem B2048593 : Blo 1819611 2048593 := bbase (se 2 (by rfl) ⟨768222, by rfl⟩ : syracuseStep 2048593 = 1536445) (by norm_num)
theorem B3072613 : Blo 1819611 3072613 := bbase (se 4 (by rfl) ⟨288057, by rfl⟩ : syracuseStep 3072613 = 576115) (by norm_num)
theorem B2048629 : Blo 1819611 2048629 := bbase (se 5 (by rfl) ⟨96029, by rfl⟩ : syracuseStep 2048629 = 192059) (by norm_num)
theorem B3326581 : Blo 1819611 3326581 := bbase (se 5 (by rfl) ⟨155933, by rfl⟩ : syracuseStep 3326581 = 311867) (by norm_num)
theorem B4096637 : Blo 1819611 4096637 := bbase (se 3 (by rfl) ⟨768119, by rfl⟩ : syracuseStep 4096637 = 1536239) (by norm_num)
theorem B9347717 : Blo 1819611 9347717 := bbase (se 4 (by rfl) ⟨876348, by rfl⟩ : syracuseStep 9347717 = 1752697) (by norm_num)
theorem B5186197 : Blo 1819611 5186197 := bbase (se 6 (by rfl) ⟨121551, by rfl⟩ : syracuseStep 5186197 = 243103) (by norm_num)
theorem B2048665 : Blo 1819611 2048665 := bbase (se 2 (by rfl) ⟨768249, by rfl⟩ : syracuseStep 2048665 = 1536499) (by norm_num)
theorem B3113645 : Blo 1819611 3113645 := bbase (se 3 (by rfl) ⟨583808, by rfl⟩ : syracuseStep 3113645 = 1167617) (by norm_num)
theorem B5833397 : Blo 1819611 5833397 := bbase (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) (by norm_num)
theorem B3072701 : Blo 1819611 3072701 := bbase (se 3 (by rfl) ⟨576131, by rfl⟩ : syracuseStep 3072701 = 1152263) (by norm_num)
theorem B2048701 : Blo 1819611 2048701 := bbase (se 3 (by rfl) ⟨384131, by rfl⟩ : syracuseStep 2048701 = 768263) (by norm_num)
theorem B4096709 : Blo 1819611 4096709 := bbase (se 4 (by rfl) ⟨384066, by rfl⟩ : syracuseStep 4096709 = 768133) (by norm_num)
theorem B5767877 : Blo 1819611 5767877 := bbase (se 4 (by rfl) ⟨540738, by rfl⟩ : syracuseStep 5767877 = 1081477) (by norm_num)
theorem B2048737 : Blo 1819611 2048737 := bbase (se 2 (by rfl) ⟨768276, by rfl⟩ : syracuseStep 2048737 = 1536553) (by norm_num)
theorem B2917109 : Blo 1819611 2917109 := bbase (se 5 (by rfl) ⟨136739, by rfl⟩ : syracuseStep 2917109 = 273479) (by norm_num)
theorem B2048773 : Blo 1819611 2048773 := bbase (se 4 (by rfl) ⟨192072, by rfl⟩ : syracuseStep 2048773 = 384145) (by norm_num)
theorem B4096781 : Blo 1819611 4096781 := bbase (se 3 (by rfl) ⟨768146, by rfl⟩ : syracuseStep 4096781 = 1536293) (by norm_num)
theorem B15770389 : Blo 1819611 15770389 := bbase (se 6 (by rfl) ⟨369618, by rfl⟩ : syracuseStep 15770389 = 739237) (by norm_num)
theorem B3457829 : Blo 1819611 3457829 := bbase (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) (by norm_num)
theorem B2048809 : Blo 1819611 2048809 := bbase (se 2 (by rfl) ⟨768303, by rfl⟩ : syracuseStep 2048809 = 1536607) (by norm_num)
theorem B2188081 : Blo 1819611 2188081 := bbase (se 2 (by rfl) ⟨820530, by rfl⟩ : syracuseStep 2188081 = 1641061) (by norm_num)
theorem B6144821 : Blo 1819611 6144821 := bbase (se 5 (by rfl) ⟨288038, by rfl⟩ : syracuseStep 6144821 = 576077) (by norm_num)
theorem B3072829 : Blo 1819611 3072829 := bbase (se 3 (by rfl) ⟨576155, by rfl⟩ : syracuseStep 3072829 = 1152311) (by norm_num)
theorem B2048845 : Blo 1819611 2048845 := bbase (se 3 (by rfl) ⟨384158, by rfl⟩ : syracuseStep 2048845 = 768317) (by norm_num)
theorem B59024213 : Blo 1819611 59024213 := bbase (se 9 (by rfl) ⟨172922, by rfl⟩ : syracuseStep 59024213 = 345845) (by norm_num)
theorem B4096853 : Blo 1819611 4096853 := bbase (se 9 (by rfl) ⟨12002, by rfl⟩ : syracuseStep 4096853 = 24005) (by norm_num)
theorem B2048881 : Blo 1819611 2048881 := bbase (se 2 (by rfl) ⟨768330, by rfl⟩ : syracuseStep 2048881 = 1536661) (by norm_num)
theorem B2188177 : Blo 1819611 2188177 := bbase (se 2 (by rfl) ⟨820566, by rfl⟩ : syracuseStep 2188177 = 1641133) (by norm_num)
theorem B3072917 : Blo 1819611 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B2048917 : Blo 1819611 2048917 := bbase (se 6 (by rfl) ⟨48021, by rfl⟩ : syracuseStep 2048917 = 96043) (by norm_num)
theorem B4096925 : Blo 1819611 4096925 := bbase (se 3 (by rfl) ⟨768173, by rfl⟩ : syracuseStep 4096925 = 1536347) (by norm_num)
theorem B2048953 : Blo 1819611 2048953 := bbase (se 2 (by rfl) ⟨768357, by rfl⟩ : syracuseStep 2048953 = 1536715) (by norm_num)
theorem B3457981 : Blo 1819611 3457981 := bbase (se 3 (by rfl) ⟨648371, by rfl⟩ : syracuseStep 3457981 = 1296743) (by norm_num)
theorem B2917333 : Blo 1819611 2917333 := bbase (se 7 (by rfl) ⟨34187, by rfl⟩ : syracuseStep 2917333 = 68375) (by norm_num)
theorem B2048989 : Blo 1819611 2048989 := bbase (se 3 (by rfl) ⟨384185, by rfl⟩ : syracuseStep 2048989 = 768371) (by norm_num)
theorem B4096997 : Blo 1819611 4096997 := bbase (se 4 (by rfl) ⟨384093, by rfl⟩ : syracuseStep 4096997 = 768187) (by norm_num)
theorem B2049025 : Blo 1819611 2049025 := bbase (se 2 (by rfl) ⟨768384, by rfl⟩ : syracuseStep 2049025 = 1536769) (by norm_num)
theorem B3073045 : Blo 1819611 3073045 := bbase (se 6 (by rfl) ⟨72024, by rfl⟩ : syracuseStep 3073045 = 144049) (by norm_num)
theorem B2049061 : Blo 1819611 2049061 := bbase (se 4 (by rfl) ⟨192099, by rfl⟩ : syracuseStep 2049061 = 384199) (by norm_num)
theorem B4097069 : Blo 1819611 4097069 := bbase (se 3 (by rfl) ⟨768200, by rfl⟩ : syracuseStep 4097069 = 1536401) (by norm_num)
theorem B2049097 : Blo 1819611 2049097 := bbase (se 2 (by rfl) ⟨768411, by rfl⟩ : syracuseStep 2049097 = 1536823) (by norm_num)
theorem B3073133 : Blo 1819611 3073133 := bbase (se 3 (by rfl) ⟨576212, by rfl⟩ : syracuseStep 3073133 = 1152425) (by norm_num)
theorem B2049133 : Blo 1819611 2049133 := bbase (se 3 (by rfl) ⟨384212, by rfl⟩ : syracuseStep 2049133 = 768425) (by norm_num)
theorem B2303093 : Blo 1819611 2303093 := bbase (se 5 (by rfl) ⟨107957, by rfl⟩ : syracuseStep 2303093 = 215915) (by norm_num)
theorem B4097141 : Blo 1819611 4097141 := bbase (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) (by norm_num)
theorem B9978997 : Blo 1819611 9978997 := bbase (se 5 (by rfl) ⟨467765, by rfl⟩ : syracuseStep 9978997 = 935531) (by norm_num)
theorem B2049169 : Blo 1819611 2049169 := bbase (se 2 (by rfl) ⟨768438, by rfl⟩ : syracuseStep 2049169 = 1536877) (by norm_num)
theorem B2303149 : Blo 1819611 2303149 := bbase (se 3 (by rfl) ⟨431840, by rfl⟩ : syracuseStep 2303149 = 863681) (by norm_num)
theorem B2049205 : Blo 1819611 2049205 := bbase (se 5 (by rfl) ⟨96056, by rfl⟩ : syracuseStep 2049205 = 192113) (by norm_num)
theorem B4097213 : Blo 1819611 4097213 := bbase (se 3 (by rfl) ⟨768227, by rfl⟩ : syracuseStep 4097213 = 1536455) (by norm_num)
theorem B37897429 : Blo 1819611 37897429 := bbase (se 7 (by rfl) ⟨444110, by rfl⟩ : syracuseStep 37897429 = 888221) (by norm_num)
theorem B2049241 : Blo 1819611 2049241 := bbase (se 2 (by rfl) ⟨768465, by rfl⟩ : syracuseStep 2049241 = 1536931) (by norm_num)
theorem B6145253 : Blo 1819611 6145253 := bbase (se 4 (by rfl) ⟨576117, by rfl⟩ : syracuseStep 6145253 = 1152235) (by norm_num)
theorem B3073261 : Blo 1819611 3073261 := bbase (se 3 (by rfl) ⟨576236, by rfl⟩ : syracuseStep 3073261 = 1152473) (by norm_num)
theorem B2049277 : Blo 1819611 2049277 := bbase (se 3 (by rfl) ⟨384239, by rfl⟩ : syracuseStep 2049277 = 768479) (by norm_num)
theorem B4097285 : Blo 1819611 4097285 := bbase (se 4 (by rfl) ⟨384120, by rfl⟩ : syracuseStep 4097285 = 768241) (by norm_num)
theorem B2303245 : Blo 1819611 2303245 := bbase (se 3 (by rfl) ⟨431858, by rfl⟩ : syracuseStep 2303245 = 863717) (by norm_num)
theorem B10372373 : Blo 1819611 10372373 := bbase (se 6 (by rfl) ⟨243102, by rfl⟩ : syracuseStep 10372373 = 486205) (by norm_num)
theorem B2049313 : Blo 1819611 2049313 := bbase (se 2 (by rfl) ⟨768492, by rfl⟩ : syracuseStep 2049313 = 1536985) (by norm_num)
theorem B3073349 : Blo 1819611 3073349 := bbase (se 4 (by rfl) ⟨288126, by rfl⟩ : syracuseStep 3073349 = 576253) (by norm_num)
theorem B4670797 : Blo 1819611 4670797 := bbase (se 3 (by rfl) ⟨875774, by rfl⟩ : syracuseStep 4670797 = 1751549) (by norm_num)
theorem B4097357 : Blo 1819611 4097357 := bbase (se 3 (by rfl) ⟨768254, by rfl⟩ : syracuseStep 4097357 = 1536509) (by norm_num)
theorem B7775605 : Blo 1819611 7775605 := bbase (se 5 (by rfl) ⟨364481, by rfl⟩ : syracuseStep 7775605 = 728963) (by norm_num)
theorem B3941765 : Blo 1819611 3941765 := bbase (se 4 (by rfl) ⟨369540, by rfl⟩ : syracuseStep 3941765 = 739081) (by norm_num)
theorem B4097429 : Blo 1819611 4097429 := bbase (se 6 (by rfl) ⟨96033, by rfl⟩ : syracuseStep 4097429 = 192067) (by norm_num)
theorem B2303417 : Blo 1819611 2303417 := bbase (se 2 (by rfl) ⟨863781, by rfl⟩ : syracuseStep 2303417 = 1727563) (by norm_num)
theorem B3073477 : Blo 1819611 3073477 := bbase (se 4 (by rfl) ⟨288138, by rfl⟩ : syracuseStep 3073477 = 576277) (by norm_num)
theorem B2729429 : Blo 1819611 2729429 := bbase (se 7 (by rfl) ⟨31985, by rfl⟩ : syracuseStep 2729429 = 63971) (by norm_num)
theorem B4097501 : Blo 1819611 4097501 := bbase (se 3 (by rfl) ⟨768281, by rfl⟩ : syracuseStep 4097501 = 1536563) (by norm_num)
theorem B2729453 : Blo 1819611 2729453 := bbase (se 3 (by rfl) ⟨511772, by rfl⟩ : syracuseStep 2729453 = 1023545) (by norm_num)
theorem B2303473 : Blo 1819611 2303473 := bbase (se 2 (by rfl) ⟨863802, by rfl⟩ : syracuseStep 2303473 = 1727605) (by norm_num)
theorem B2729477 : Blo 1819611 2729477 := bbase (se 4 (by rfl) ⟨255888, by rfl⟩ : syracuseStep 2729477 = 511777) (by norm_num)
theorem B2336261 : Blo 1819611 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B2729501 : Blo 1819611 2729501 := bbase (se 3 (by rfl) ⟨511781, by rfl⟩ : syracuseStep 2729501 = 1023563) (by norm_num)
theorem B3073565 : Blo 1819611 3073565 := bbase (se 3 (by rfl) ⟨576293, by rfl⟩ : syracuseStep 3073565 = 1152587) (by norm_num)
theorem B4097573 : Blo 1819611 4097573 := bbase (se 4 (by rfl) ⟨384147, by rfl⟩ : syracuseStep 4097573 = 768295) (by norm_num)
theorem B2729525 : Blo 1819611 2729525 := bbase (se 5 (by rfl) ⟨127946, by rfl⟩ : syracuseStep 2729525 = 255893) (by norm_num)
theorem B2729549 : Blo 1819611 2729549 := bbase (se 3 (by rfl) ⟨511790, by rfl⟩ : syracuseStep 2729549 = 1023581) (by norm_num)
theorem B2303569 : Blo 1819611 2303569 := bbase (se 2 (by rfl) ⟨863838, by rfl⟩ : syracuseStep 2303569 = 1727677) (by norm_num)
theorem B26240597 : Blo 1819611 26240597 := bbase (se 8 (by rfl) ⟨153753, by rfl⟩ : syracuseStep 26240597 = 307507) (by norm_num)
theorem B2729573 : Blo 1819611 2729573 := bbase (se 4 (by rfl) ⟨255897, by rfl⟩ : syracuseStep 2729573 = 511795) (by norm_num)
theorem B9217637 : Blo 1819611 9217637 := bbase (se 4 (by rfl) ⟨864153, by rfl⟩ : syracuseStep 9217637 = 1728307) (by norm_num)
theorem B4097645 : Blo 1819611 4097645 := bbase (se 3 (by rfl) ⟨768308, by rfl⟩ : syracuseStep 4097645 = 1536617) (by norm_num)
theorem B2729597 : Blo 1819611 2729597 := bbase (se 3 (by rfl) ⟨511799, by rfl⟩ : syracuseStep 2729597 = 1023599) (by norm_num)
theorem B2729621 : Blo 1819611 2729621 := bbase (se 6 (by rfl) ⟨63975, by rfl⟩ : syracuseStep 2729621 = 127951) (by norm_num)
theorem B6145685 : Blo 1819611 6145685 := bbase (se 6 (by rfl) ⟨144039, by rfl⟩ : syracuseStep 6145685 = 288079) (by norm_num)
theorem B3073693 : Blo 1819611 3073693 := bbase (se 3 (by rfl) ⟨576317, by rfl⟩ : syracuseStep 3073693 = 1152635) (by norm_num)
theorem B1943201 : Blo 1819611 1943201 := bbase (se 2 (by rfl) ⟨728700, by rfl⟩ : syracuseStep 1943201 = 1457401) (by norm_num)
theorem B2729645 : Blo 1819611 2729645 := bbase (se 3 (by rfl) ⟨511808, by rfl⟩ : syracuseStep 2729645 = 1023617) (by norm_num)
theorem B4097717 : Blo 1819611 4097717 := bbase (se 5 (by rfl) ⟨192080, by rfl⟩ : syracuseStep 4097717 = 384161) (by norm_num)
theorem B2729669 : Blo 1819611 2729669 := bbase (se 4 (by rfl) ⟨255906, by rfl⟩ : syracuseStep 2729669 = 511813) (by norm_num)
theorem B23340757 : Blo 1819611 23340757 := bbase (se 7 (by rfl) ⟨273524, by rfl⟩ : syracuseStep 23340757 = 547049) (by norm_num)
theorem B2729693 : Blo 1819611 2729693 := bbase (se 3 (by rfl) ⟨511817, by rfl⟩ : syracuseStep 2729693 = 1023635) (by norm_num)
theorem B2729717 : Blo 1819611 2729717 := bbase (se 5 (by rfl) ⟨127955, by rfl⟩ : syracuseStep 2729717 = 255911) (by norm_num)
theorem B3073781 : Blo 1819611 3073781 := bbase (se 5 (by rfl) ⟨144083, by rfl⟩ : syracuseStep 3073781 = 288167) (by norm_num)
theorem B2303741 : Blo 1819611 2303741 := bbase (se 3 (by rfl) ⟨431951, by rfl⟩ : syracuseStep 2303741 = 863903) (by norm_num)
theorem B4097789 : Blo 1819611 4097789 := bbase (se 3 (by rfl) ⟨768335, by rfl⟩ : syracuseStep 4097789 = 1536671) (by norm_num)
theorem B2729741 : Blo 1819611 2729741 := bbase (se 3 (by rfl) ⟨511826, by rfl⟩ : syracuseStep 2729741 = 1023653) (by norm_num)
theorem B2729765 : Blo 1819611 2729765 := bbase (se 4 (by rfl) ⟨255915, by rfl⟩ : syracuseStep 2729765 = 511831) (by norm_num)
theorem B2303797 : Blo 1819611 2303797 := bbase (se 5 (by rfl) ⟨107990, by rfl⟩ : syracuseStep 2303797 = 215981) (by norm_num)
theorem B2729789 : Blo 1819611 2729789 := bbase (se 3 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 2729789 = 1023671) (by norm_num)
theorem B4097861 : Blo 1819611 4097861 := bbase (se 4 (by rfl) ⟨384174, by rfl⟩ : syracuseStep 4097861 = 768349) (by norm_num)
theorem B2729813 : Blo 1819611 2729813 := bbase (se 9 (by rfl) ⟨7997, by rfl⟩ : syracuseStep 2729813 = 15995) (by norm_num)
theorem B1943389 : Blo 1819611 1943389 := bbase (se 3 (by rfl) ⟨364385, by rfl⟩ : syracuseStep 1943389 = 728771) (by norm_num)
theorem B2729837 : Blo 1819611 2729837 := bbase (se 3 (by rfl) ⟨511844, by rfl⟩ : syracuseStep 2729837 = 1023689) (by norm_num)
theorem B3073909 : Blo 1819611 3073909 := bbase (se 5 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 3073909 = 288179) (by norm_num)
theorem B2729861 : Blo 1819611 2729861 := bbase (se 4 (by rfl) ⟨255924, by rfl⟩ : syracuseStep 2729861 = 511849) (by norm_num)
theorem B4097933 : Blo 1819611 4097933 := bbase (se 3 (by rfl) ⟨768362, by rfl⟩ : syracuseStep 4097933 = 1536725) (by norm_num)
theorem B2303893 : Blo 1819611 2303893 := bbase (se 6 (by rfl) ⟨53997, by rfl⟩ : syracuseStep 2303893 = 107995) (by norm_num)
theorem B2729885 : Blo 1819611 2729885 := bbase (se 3 (by rfl) ⟨511853, by rfl⟩ : syracuseStep 2729885 = 1023707) (by norm_num)
theorem B2729909 : Blo 1819611 2729909 := bbase (se 5 (by rfl) ⟨127964, by rfl⟩ : syracuseStep 2729909 = 255929) (by norm_num)
theorem B4605893 : Blo 1819611 4605893 := bbase (se 4 (by rfl) ⟨431802, by rfl⟩ : syracuseStep 4605893 = 863605) (by norm_num)
theorem B2729933 : Blo 1819611 2729933 := bbase (se 3 (by rfl) ⟨511862, by rfl⟩ : syracuseStep 2729933 = 1023725) (by norm_num)
theorem B13830101 : Blo 1819611 13830101 := bbase (se 7 (by rfl) ⟨162071, by rfl⟩ : syracuseStep 13830101 = 324143) (by norm_num)
theorem B4098005 : Blo 1819611 4098005 := bbase (se 7 (by rfl) ⟨48023, by rfl⟩ : syracuseStep 4098005 = 96047) (by norm_num)
theorem B2729957 : Blo 1819611 2729957 := bbase (se 4 (by rfl) ⟨255933, by rfl⟩ : syracuseStep 2729957 = 511867) (by norm_num)
theorem B8751077 : Blo 1819611 8751077 := bbase (se 4 (by rfl) ⟨820413, by rfl⟩ : syracuseStep 8751077 = 1640827) (by norm_num)
theorem B1845229 : Blo 1819611 1845229 := bbase (se 3 (by rfl) ⟨345980, by rfl⟩ : syracuseStep 1845229 = 691961) (by norm_num)
theorem B2729981 : Blo 1819611 2729981 := bbase (se 3 (by rfl) ⟨511871, by rfl⟩ : syracuseStep 2729981 = 1023743) (by norm_num)
theorem B2730005 : Blo 1819611 2730005 := bbase (se 6 (by rfl) ⟨63984, by rfl⟩ : syracuseStep 2730005 = 127969) (by norm_num)
theorem B4098077 : Blo 1819611 4098077 := bbase (se 3 (by rfl) ⟨768389, by rfl⟩ : syracuseStep 4098077 = 1536779) (by norm_num)
theorem B2730029 : Blo 1819611 2730029 := bbase (se 3 (by rfl) ⟨511880, by rfl⟩ : syracuseStep 2730029 = 1023761) (by norm_num)
theorem B11667509 : Blo 1819611 11667509 := bbase (se 5 (by rfl) ⟨546914, by rfl⟩ : syracuseStep 11667509 = 1093829) (by norm_num)
theorem B2304065 : Blo 1819611 2304065 := bbase (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) (by norm_num)
theorem B2730053 : Blo 1819611 2730053 := bbase (se 4 (by rfl) ⟨255942, by rfl⟩ : syracuseStep 2730053 = 511885) (by norm_num)
theorem B6146117 : Blo 1819611 6146117 := bbase (se 4 (by rfl) ⟨576198, by rfl⟩ : syracuseStep 6146117 = 1152397) (by norm_num)
theorem B2730077 : Blo 1819611 2730077 := bbase (se 3 (by rfl) ⟨511889, by rfl⟩ : syracuseStep 2730077 = 1023779) (by norm_num)
theorem B8865893 : Blo 1819611 8865893 := bbase (se 4 (by rfl) ⟨831177, by rfl⟩ : syracuseStep 8865893 = 1662355) (by norm_num)
theorem B4098149 : Blo 1819611 4098149 := bbase (se 4 (by rfl) ⟨384201, by rfl⟩ : syracuseStep 4098149 = 768403) (by norm_num)
theorem B2730101 : Blo 1819611 2730101 := bbase (se 5 (by rfl) ⟨127973, by rfl⟩ : syracuseStep 2730101 = 255947) (by norm_num)
theorem B6228085 : Blo 1819611 6228085 := bbase (se 5 (by rfl) ⟨291941, by rfl⟩ : syracuseStep 6228085 = 583883) (by norm_num)
theorem B2304121 : Blo 1819611 2304121 := bbase (se 2 (by rfl) ⟨864045, by rfl⟩ : syracuseStep 2304121 = 1728091) (by norm_num)
theorem B4606085 : Blo 1819611 4606085 := bbase (se 4 (by rfl) ⟨431820, by rfl⟩ : syracuseStep 4606085 = 863641) (by norm_num)
theorem B2590861 : Blo 1819611 2590861 := bbase (se 3 (by rfl) ⟨485786, by rfl⟩ : syracuseStep 2590861 = 971573) (by norm_num)
theorem B2730125 : Blo 1819611 2730125 := bbase (se 3 (by rfl) ⟨511898, by rfl⟩ : syracuseStep 2730125 = 1023797) (by norm_num)
theorem B2730149 : Blo 1819611 2730149 := bbase (se 4 (by rfl) ⟨255951, by rfl⟩ : syracuseStep 2730149 = 511903) (by norm_num)
theorem B4098221 : Blo 1819611 4098221 := bbase (se 3 (by rfl) ⟨768416, by rfl⟩ : syracuseStep 4098221 = 1536833) (by norm_num)
theorem B3279037 : Blo 1819611 3279037 := bbase (se 3 (by rfl) ⟨614819, by rfl⟩ : syracuseStep 3279037 = 1229639) (by norm_num)
theorem B2730173 : Blo 1819611 2730173 := bbase (se 3 (by rfl) ⟨511907, by rfl⟩ : syracuseStep 2730173 = 1023815) (by norm_num)
theorem B2730197 : Blo 1819611 2730197 := bbase (se 7 (by rfl) ⟨31994, by rfl⟩ : syracuseStep 2730197 = 63989) (by norm_num)
theorem B2304217 : Blo 1819611 2304217 := bbase (se 2 (by rfl) ⟨864081, by rfl⟩ : syracuseStep 2304217 = 1728163) (by norm_num)
theorem B2590957 : Blo 1819611 2590957 := bbase (se 3 (by rfl) ⟨485804, by rfl⟩ : syracuseStep 2590957 = 971609) (by norm_num)
theorem B2730221 : Blo 1819611 2730221 := bbase (se 3 (by rfl) ⟨511916, by rfl⟩ : syracuseStep 2730221 = 1023833) (by norm_num)
theorem B6310133 : Blo 1819611 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B4098293 : Blo 1819611 4098293 := bbase (se 5 (by rfl) ⟨192107, by rfl⟩ : syracuseStep 4098293 = 384215) (by norm_num)
theorem B2730245 : Blo 1819611 2730245 := bbase (se 4 (by rfl) ⟨255960, by rfl⟩ : syracuseStep 2730245 = 511921) (by norm_num)
theorem B1845509 : Blo 1819611 1845509 := bbase (se 4 (by rfl) ⟨173016, by rfl⟩ : syracuseStep 1845509 = 346033) (by norm_num)
theorem B6916373 : Blo 1819611 6916373 := bbase (se 6 (by rfl) ⟨162102, by rfl⟩ : syracuseStep 6916373 = 324205) (by norm_num)
theorem B2730269 : Blo 1819611 2730269 := bbase (se 3 (by rfl) ⟨511925, by rfl⟩ : syracuseStep 2730269 = 1023851) (by norm_num)
theorem B2730293 : Blo 1819611 2730293 := bbase (se 5 (by rfl) ⟨127982, by rfl⟩ : syracuseStep 2730293 = 255965) (by norm_num)
theorem B4098365 : Blo 1819611 4098365 := bbase (se 3 (by rfl) ⟨768443, by rfl⟩ : syracuseStep 4098365 = 1536887) (by norm_num)
theorem B2730317 : Blo 1819611 2730317 := bbase (se 3 (by rfl) ⟨511934, by rfl⟩ : syracuseStep 2730317 = 1023869) (by norm_num)
theorem B3279197 : Blo 1819611 3279197 := bbase (se 3 (by rfl) ⟨614849, by rfl⟩ : syracuseStep 3279197 = 1229699) (by norm_num)
theorem B2730341 : Blo 1819611 2730341 := bbase (se 4 (by rfl) ⟨255969, by rfl⟩ : syracuseStep 2730341 = 511939) (by norm_num)
theorem B13822325 : Blo 1819611 13822325 := bbase (se 5 (by rfl) ⟨647921, by rfl⟩ : syracuseStep 13822325 = 1295843) (by norm_num)
theorem B2730365 : Blo 1819611 2730365 := bbase (se 3 (by rfl) ⟨511943, by rfl⟩ : syracuseStep 2730365 = 1023887) (by norm_num)
theorem B2304389 : Blo 1819611 2304389 := bbase (se 4 (by rfl) ⟨216036, by rfl⟩ : syracuseStep 2304389 = 432073) (by norm_num)
theorem B4098437 : Blo 1819611 4098437 := bbase (se 4 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 4098437 = 768457) (by norm_num)
theorem B3279253 : Blo 1819611 3279253 := bbase (se 6 (by rfl) ⟨76857, by rfl⟩ : syracuseStep 3279253 = 153715) (by norm_num)
theorem B2730389 : Blo 1819611 2730389 := bbase (se 6 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 2730389 = 127987) (by norm_num)
theorem B2730413 : Blo 1819611 2730413 := bbase (se 3 (by rfl) ⟨511952, by rfl⟩ : syracuseStep 2730413 = 1023905) (by norm_num)
theorem B2304445 : Blo 1819611 2304445 := bbase (se 3 (by rfl) ⟨432083, by rfl⟩ : syracuseStep 2304445 = 864167) (by norm_num)
theorem B2730437 : Blo 1819611 2730437 := bbase (se 4 (by rfl) ⟨255978, by rfl⟩ : syracuseStep 2730437 = 511957) (by norm_num)
theorem B4098509 : Blo 1819611 4098509 := bbase (se 3 (by rfl) ⟨768470, by rfl⟩ : syracuseStep 4098509 = 1536941) (by norm_num)
theorem B4606429 : Blo 1819611 4606429 := bbase (se 3 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 4606429 = 1727411) (by norm_num)
theorem B2730461 : Blo 1819611 2730461 := bbase (se 3 (by rfl) ⟨511961, by rfl⟩ : syracuseStep 2730461 = 1023923) (by norm_num)
theorem B2730485 : Blo 1819611 2730485 := bbase (se 5 (by rfl) ⟨127991, by rfl⟩ : syracuseStep 2730485 = 255983) (by norm_num)
theorem B6146549 : Blo 1819611 6146549 := bbase (se 5 (by rfl) ⟨288119, by rfl⟩ : syracuseStep 6146549 = 576239) (by norm_num)
theorem B2730509 : Blo 1819611 2730509 := bbase (se 3 (by rfl) ⟨511970, by rfl⟩ : syracuseStep 2730509 = 1023941) (by norm_num)
theorem B4098581 : Blo 1819611 4098581 := bbase (se 6 (by rfl) ⟨96060, by rfl⟩ : syracuseStep 4098581 = 192121) (by norm_num)
theorem B2304541 : Blo 1819611 2304541 := bbase (se 3 (by rfl) ⟨432101, by rfl⟩ : syracuseStep 2304541 = 864203) (by norm_num)
theorem B2730533 : Blo 1819611 2730533 := bbase (se 4 (by rfl) ⟨255987, by rfl⟩ : syracuseStep 2730533 = 511975) (by norm_num)
theorem B2730557 : Blo 1819611 2730557 := bbase (se 3 (by rfl) ⟨511979, by rfl⟩ : syracuseStep 2730557 = 1023959) (by norm_num)
theorem B4606541 : Blo 1819611 4606541 := bbase (se 3 (by rfl) ⟨863726, by rfl⟩ : syracuseStep 4606541 = 1727453) (by norm_num)
theorem B2730581 : Blo 1819611 2730581 := bbase (se 8 (by rfl) ⟨15999, by rfl⟩ : syracuseStep 2730581 = 31999) (by norm_num)
theorem B2730605 : Blo 1819611 2730605 := bbase (se 3 (by rfl) ⟨511988, by rfl⟩ : syracuseStep 2730605 = 1023977) (by norm_num)
theorem B2730629 : Blo 1819611 2730629 := bbase (se 4 (by rfl) ⟨255996, by rfl⟩ : syracuseStep 2730629 = 511993) (by norm_num)
theorem B1944209 : Blo 1819611 1944209 := bbase (se 2 (by rfl) ⟨729078, by rfl⟩ : syracuseStep 1944209 = 1458157) (by norm_num)
theorem B2730653 : Blo 1819611 2730653 := bbase (se 3 (by rfl) ⟨511997, by rfl⟩ : syracuseStep 2730653 = 1023995) (by norm_num)
theorem B2730677 : Blo 1819611 2730677 := bbase (se 5 (by rfl) ⟨128000, by rfl⟩ : syracuseStep 2730677 = 256001) (by norm_num)
theorem B2304713 : Blo 1819611 2304713 := bbase (se 2 (by rfl) ⟨864267, by rfl⟩ : syracuseStep 2304713 = 1728535) (by norm_num)
theorem B2730701 : Blo 1819611 2730701 := bbase (se 3 (by rfl) ⟨512006, by rfl⟩ : syracuseStep 2730701 = 1024013) (by norm_num)
theorem B2591453 : Blo 1819611 2591453 := bbase (se 3 (by rfl) ⟨485897, by rfl⟩ : syracuseStep 2591453 = 971795) (by norm_num)
theorem B3115741 : Blo 1819611 3115741 := bbase (se 3 (by rfl) ⟨584201, by rfl⟩ : syracuseStep 3115741 = 1168403) (by norm_num)
theorem B2730725 : Blo 1819611 2730725 := bbase (se 4 (by rfl) ⟨256005, by rfl⟩ : syracuseStep 2730725 = 512011) (by norm_num)
theorem B2730749 : Blo 1819611 2730749 := bbase (se 3 (by rfl) ⟨512015, by rfl⟩ : syracuseStep 2730749 = 1024031) (by norm_num)
theorem B2304769 : Blo 1819611 2304769 := bbase (se 2 (by rfl) ⟨864288, by rfl⟩ : syracuseStep 2304769 = 1728577) (by norm_num)
theorem B4606733 : Blo 1819611 4606733 := bbase (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) (by norm_num)
theorem B2730773 : Blo 1819611 2730773 := bbase (se 6 (by rfl) ⟨64002, by rfl⟩ : syracuseStep 2730773 = 128005) (by norm_num)
theorem B2730797 : Blo 1819611 2730797 := bbase (se 3 (by rfl) ⟨512024, by rfl⟩ : syracuseStep 2730797 = 1024049) (by norm_num)
theorem B2730821 : Blo 1819611 2730821 := bbase (se 4 (by rfl) ⟨256014, by rfl⟩ : syracuseStep 2730821 = 512029) (by norm_num)
theorem B7777093 : Blo 1819611 7777093 := bbase (se 4 (by rfl) ⟨729102, by rfl⟩ : syracuseStep 7777093 = 1458205) (by norm_num)
theorem B7777109 : Blo 1819611 7777109 := bbase (se 9 (by rfl) ⟨22784, by rfl⟩ : syracuseStep 7777109 = 45569) (by norm_num)
theorem B2730845 : Blo 1819611 2730845 := bbase (se 3 (by rfl) ⟨512033, by rfl⟩ : syracuseStep 2730845 = 1024067) (by norm_num)
theorem B2304865 : Blo 1819611 2304865 := bbase (se 2 (by rfl) ⟨864324, by rfl⟩ : syracuseStep 2304865 = 1728649) (by norm_num)
theorem B2730869 : Blo 1819611 2730869 := bbase (se 5 (by rfl) ⟨128009, by rfl⟩ : syracuseStep 2730869 = 256019) (by norm_num)
theorem B9218933 : Blo 1819611 9218933 := bbase (se 5 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 9218933 = 864275) (by norm_num)
theorem B2730893 : Blo 1819611 2730893 := bbase (se 3 (by rfl) ⟨512042, by rfl⟩ : syracuseStep 2730893 = 1024085) (by norm_num)
theorem B2460565 : Blo 1819611 2460565 := bbase (se 6 (by rfl) ⟨57669, by rfl⟩ : syracuseStep 2460565 = 115339) (by norm_num)
theorem B2730917 : Blo 1819611 2730917 := bbase (se 4 (by rfl) ⟨256023, by rfl⟩ : syracuseStep 2730917 = 512047) (by norm_num)
theorem B6146981 : Blo 1819611 6146981 := bbase (se 4 (by rfl) ⟨576279, by rfl⟩ : syracuseStep 6146981 = 1152559) (by norm_num)
theorem B2730941 : Blo 1819611 2730941 := bbase (se 3 (by rfl) ⟨512051, by rfl⟩ : syracuseStep 2730941 = 1024103) (by norm_num)
theorem B6908885 : Blo 1819611 6908885 := bbase (se 7 (by rfl) ⟨80963, by rfl⟩ : syracuseStep 6908885 = 161927) (by norm_num)
theorem B2730965 : Blo 1819611 2730965 := bbase (se 7 (by rfl) ⟨32003, by rfl⟩ : syracuseStep 2730965 = 64007) (by norm_num)
theorem B2730989 : Blo 1819611 2730989 := bbase (se 3 (by rfl) ⟨512060, by rfl⟩ : syracuseStep 2730989 = 1024121) (by norm_num)
theorem B2731013 : Blo 1819611 2731013 := bbase (se 4 (by rfl) ⟨256032, by rfl⟩ : syracuseStep 2731013 = 512065) (by norm_num)
theorem B2305037 : Blo 1819611 2305037 := bbase (se 3 (by rfl) ⟨432194, by rfl⟩ : syracuseStep 2305037 = 864389) (by norm_num)
theorem B2731037 : Blo 1819611 2731037 := bbase (se 3 (by rfl) ⟨512069, by rfl⟩ : syracuseStep 2731037 = 1024139) (by norm_num)
theorem B2731061 : Blo 1819611 2731061 := bbase (se 5 (by rfl) ⟨128018, by rfl⟩ : syracuseStep 2731061 = 256037) (by norm_num)
theorem B2305093 : Blo 1819611 2305093 := bbase (se 4 (by rfl) ⟨216102, by rfl⟩ : syracuseStep 2305093 = 432205) (by norm_num)
theorem B2731085 : Blo 1819611 2731085 := bbase (se 3 (by rfl) ⟨512078, by rfl⟩ : syracuseStep 2731085 = 1024157) (by norm_num)
theorem B1944653 : Blo 1819611 1944653 := bbase (se 3 (by rfl) ⟨364622, by rfl⟩ : syracuseStep 1944653 = 729245) (by norm_num)
theorem B8744021 : Blo 1819611 8744021 := bbase (se 8 (by rfl) ⟨51234, by rfl⟩ : syracuseStep 8744021 = 102469) (by norm_num)
theorem B4607077 : Blo 1819611 4607077 := bbase (se 4 (by rfl) ⟨431913, by rfl⟩ : syracuseStep 4607077 = 863827) (by norm_num)
theorem B2731109 : Blo 1819611 2731109 := bbase (se 4 (by rfl) ⟨256041, by rfl⟩ : syracuseStep 2731109 = 512083) (by norm_num)
theorem B2731133 : Blo 1819611 2731133 := bbase (se 3 (by rfl) ⟨512087, by rfl⟩ : syracuseStep 2731133 = 1024175) (by norm_num)
theorem B1846405 : Blo 1819611 1846405 := bbase (se 4 (by rfl) ⟨173100, by rfl⟩ : syracuseStep 1846405 = 346201) (by norm_num)
theorem B2731157 : Blo 1819611 2731157 := bbase (se 6 (by rfl) ⟨64011, by rfl⟩ : syracuseStep 2731157 = 128023) (by norm_num)
theorem B2305189 : Blo 1819611 2305189 := bbase (se 4 (by rfl) ⟨216111, by rfl⟩ : syracuseStep 2305189 = 432223) (by norm_num)
theorem B2731181 : Blo 1819611 2731181 := bbase (se 3 (by rfl) ⟨512096, by rfl⟩ : syracuseStep 2731181 = 1024193) (by norm_num)
theorem B4672685 : Blo 1819611 4672685 := bbase (se 3 (by rfl) ⟨876128, by rfl⟩ : syracuseStep 4672685 = 1752257) (by norm_num)
theorem B2731205 : Blo 1819611 2731205 := bbase (se 4 (by rfl) ⟨256050, by rfl⟩ : syracuseStep 2731205 = 512101) (by norm_num)
theorem B4607189 : Blo 1819611 4607189 := bbase (se 7 (by rfl) ⟨53990, by rfl⟩ : syracuseStep 4607189 = 107981) (by norm_num)
theorem B2731229 : Blo 1819611 2731229 := bbase (se 3 (by rfl) ⟨512105, by rfl⟩ : syracuseStep 2731229 = 1024211) (by norm_num)
theorem B2731253 : Blo 1819611 2731253 := bbase (se 5 (by rfl) ⟨128027, by rfl⟩ : syracuseStep 2731253 = 256055) (by norm_num)
theorem B2592005 : Blo 1819611 2592005 := bbase (se 4 (by rfl) ⟨243000, by rfl⟩ : syracuseStep 2592005 = 486001) (by norm_num)
theorem B2731277 : Blo 1819611 2731277 := bbase (se 3 (by rfl) ⟨512114, by rfl⟩ : syracuseStep 2731277 = 1024229) (by norm_num)
theorem B2731301 : Blo 1819611 2731301 := bbase (se 4 (by rfl) ⟨256059, by rfl⟩ : syracuseStep 2731301 = 512119) (by norm_num)
theorem B2731325 : Blo 1819611 2731325 := bbase (se 3 (by rfl) ⟨512123, by rfl⟩ : syracuseStep 2731325 = 1024247) (by norm_num)
theorem B1944901 : Blo 1819611 1944901 := bbase (se 4 (by rfl) ⟨182334, by rfl⟩ : syracuseStep 1944901 = 364669) (by norm_num)
theorem B2305361 : Blo 1819611 2305361 := bbase (se 2 (by rfl) ⟨864510, by rfl⟩ : syracuseStep 2305361 = 1729021) (by norm_num)
theorem B2731349 : Blo 1819611 2731349 := bbase (se 11 (by rfl) ⟨2000, by rfl⟩ : syracuseStep 2731349 = 4001) (by norm_num)
theorem B6147413 : Blo 1819611 6147413 := bbase (se 11 (by rfl) ⟨4502, by rfl⟩ : syracuseStep 6147413 = 9005) (by norm_num)
theorem B2805101 : Blo 1819611 2805101 := bbase (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) (by norm_num)
theorem B2731373 : Blo 1819611 2731373 := bbase (se 3 (by rfl) ⟨512132, by rfl⟩ : syracuseStep 2731373 = 1024265) (by norm_num)
theorem B2731397 : Blo 1819611 2731397 := bbase (se 4 (by rfl) ⟨256068, by rfl⟩ : syracuseStep 2731397 = 512137) (by norm_num)
theorem B2305417 : Blo 1819611 2305417 := bbase (se 2 (by rfl) ⟨864531, by rfl⟩ : syracuseStep 2305417 = 1729063) (by norm_num)
theorem B4607381 : Blo 1819611 4607381 := bbase (se 6 (by rfl) ⟨107985, by rfl⟩ : syracuseStep 4607381 = 215971) (by norm_num)
theorem B2731421 : Blo 1819611 2731421 := bbase (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) (by norm_num)
theorem B2731445 : Blo 1819611 2731445 := bbase (se 5 (by rfl) ⟨128036, by rfl⟩ : syracuseStep 2731445 = 256073) (by norm_num)
theorem B10374581 : Blo 1819611 10374581 := bbase (se 5 (by rfl) ⟨486308, by rfl⟩ : syracuseStep 10374581 = 972617) (by norm_num)
theorem B2731469 : Blo 1819611 2731469 := bbase (se 3 (by rfl) ⟨512150, by rfl⟩ : syracuseStep 2731469 = 1024301) (by norm_num)
theorem B2731493 : Blo 1819611 2731493 := bbase (se 4 (by rfl) ⟨256077, by rfl⟩ : syracuseStep 2731493 = 512155) (by norm_num)
theorem B2731517 : Blo 1819611 2731517 := bbase (se 3 (by rfl) ⟨512159, by rfl⟩ : syracuseStep 2731517 = 1024319) (by norm_num)
theorem B2731541 : Blo 1819611 2731541 := bbase (se 6 (by rfl) ⟨64020, by rfl⟩ : syracuseStep 2731541 = 128041) (by norm_num)
theorem B3280421 : Blo 1819611 3280421 := bbase (se 4 (by rfl) ⟨307539, by rfl⟩ : syracuseStep 3280421 = 615079) (by norm_num)
theorem B2731565 : Blo 1819611 2731565 := bbase (se 3 (by rfl) ⟨512168, by rfl⟩ : syracuseStep 2731565 = 1024337) (by norm_num)
theorem B13119029 : Blo 1819611 13119029 := bbase (se 5 (by rfl) ⟨614954, by rfl⟩ : syracuseStep 13119029 = 1229909) (by norm_num)
theorem B2731589 : Blo 1819611 2731589 := bbase (se 4 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 2731589 = 512173) (by norm_num)
theorem B2731613 : Blo 1819611 2731613 := bbase (se 3 (by rfl) ⟨512177, by rfl⟩ : syracuseStep 2731613 = 1024355) (by norm_num)
theorem B3886709 : Blo 1819611 3886709 := bbase (se 5 (by rfl) ⟨182189, by rfl⟩ : syracuseStep 3886709 = 364379) (by norm_num)
theorem B2731637 : Blo 1819611 2731637 := bbase (se 5 (by rfl) ⟨128045, by rfl⟩ : syracuseStep 2731637 = 256091) (by norm_num)
theorem B2731661 : Blo 1819611 2731661 := bbase (se 3 (by rfl) ⟨512186, by rfl⟩ : syracuseStep 2731661 = 1024373) (by norm_num)
theorem B2731685 : Blo 1819611 2731685 := bbase (se 4 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 2731685 = 512191) (by norm_num)
theorem B2731709 : Blo 1819611 2731709 := bbase (se 3 (by rfl) ⟨512195, by rfl⟩ : syracuseStep 2731709 = 1024391) (by norm_num)
theorem B2731733 : Blo 1819611 2731733 := bbase (se 7 (by rfl) ⟨32012, by rfl⟩ : syracuseStep 2731733 = 64025) (by norm_num)
theorem B4607725 : Blo 1819611 4607725 := bbase (se 3 (by rfl) ⟨863948, by rfl⟩ : syracuseStep 4607725 = 1727897) (by norm_num)
theorem B2731757 : Blo 1819611 2731757 := bbase (se 3 (by rfl) ⟨512204, by rfl⟩ : syracuseStep 2731757 = 1024409) (by norm_num)
theorem B1969921 : Blo 1819611 1969921 := bbase (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) (by norm_num)
theorem B2731781 : Blo 1819611 2731781 := bbase (se 4 (by rfl) ⟨256104, by rfl⟩ : syracuseStep 2731781 = 512209) (by norm_num)
theorem B6147845 : Blo 1819611 6147845 := bbase (se 4 (by rfl) ⟨576360, by rfl⟩ : syracuseStep 6147845 = 1152721) (by norm_num)
theorem B2731805 : Blo 1819611 2731805 := bbase (se 3 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 2731805 = 1024427) (by norm_num)
theorem B1969969 : Blo 1819611 1969969 := bbase (se 2 (by rfl) ⟨738738, by rfl⟩ : syracuseStep 1969969 = 1477477) (by norm_num)
theorem B2731829 : Blo 1819611 2731829 := bbase (se 5 (by rfl) ⟨128054, by rfl⟩ : syracuseStep 2731829 = 256109) (by norm_num)
theorem B2731853 : Blo 1819611 2731853 := bbase (se 3 (by rfl) ⟨512222, by rfl⟩ : syracuseStep 2731853 = 1024445) (by norm_num)
theorem B4607837 : Blo 1819611 4607837 := bbase (se 3 (by rfl) ⟨863969, by rfl⟩ : syracuseStep 4607837 = 1727939) (by norm_num)
theorem B3886949 : Blo 1819611 3886949 := bbase (se 4 (by rfl) ⟨364401, by rfl⟩ : syracuseStep 3886949 = 728803) (by norm_num)
theorem B2731877 : Blo 1819611 2731877 := bbase (se 4 (by rfl) ⟨256113, by rfl⟩ : syracuseStep 2731877 = 512227) (by norm_num)
theorem B2731901 : Blo 1819611 2731901 := bbase (se 3 (by rfl) ⟨512231, by rfl⟩ : syracuseStep 2731901 = 1024463) (by norm_num)
theorem B11661205 : Blo 1819611 11661205 := bbase (se 6 (by rfl) ⟨273309, by rfl⟩ : syracuseStep 11661205 = 546619) (by norm_num)
theorem B2731925 : Blo 1819611 2731925 := bbase (se 6 (by rfl) ⟨64029, by rfl⟩ : syracuseStep 2731925 = 128059) (by norm_num)
theorem B2731949 : Blo 1819611 2731949 := bbase (se 3 (by rfl) ⟨512240, by rfl⟩ : syracuseStep 2731949 = 1024481) (by norm_num)
theorem B6074309 : Blo 1819611 6074309 := bbase (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) (by norm_num)
theorem B2731973 : Blo 1819611 2731973 := bbase (se 4 (by rfl) ⟨256122, by rfl⟩ : syracuseStep 2731973 = 512245) (by norm_num)
theorem B8753093 : Blo 1819611 8753093 := bbase (se 4 (by rfl) ⟨820602, by rfl⟩ : syracuseStep 8753093 = 1641205) (by norm_num)
theorem B2731997 : Blo 1819611 2731997 := bbase (se 3 (by rfl) ⟨512249, by rfl⟩ : syracuseStep 2731997 = 1024499) (by norm_num)
theorem B2592757 : Blo 1819611 2592757 := bbase (se 5 (by rfl) ⟨121535, by rfl⟩ : syracuseStep 2592757 = 243071) (by norm_num)
theorem B2732021 : Blo 1819611 2732021 := bbase (se 5 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 2732021 = 256127) (by norm_num)
theorem B2732045 : Blo 1819611 2732045 := bbase (se 3 (by rfl) ⟨512258, by rfl⟩ : syracuseStep 2732045 = 1024517) (by norm_num)
theorem B12455957 : Blo 1819611 12455957 := bbase (se 6 (by rfl) ⟨291936, by rfl⟩ : syracuseStep 12455957 = 583873) (by norm_num)
theorem B3502109 : Blo 1819611 3502109 := bbase (se 3 (by rfl) ⟨656645, by rfl⟩ : syracuseStep 3502109 = 1313291) (by norm_num)
theorem B4608029 : Blo 1819611 4608029 := bbase (se 3 (by rfl) ⟨864005, by rfl⟩ : syracuseStep 4608029 = 1728011) (by norm_num)
theorem B2732069 : Blo 1819611 2732069 := bbase (se 4 (by rfl) ⟨256131, by rfl⟩ : syracuseStep 2732069 = 512263) (by norm_num)
theorem B2732093 : Blo 1819611 2732093 := bbase (se 3 (by rfl) ⟨512267, by rfl⟩ : syracuseStep 2732093 = 1024535) (by norm_num)
theorem B2461765 : Blo 1819611 2461765 := bbase (se 4 (by rfl) ⟨230790, by rfl⟩ : syracuseStep 2461765 = 461581) (by norm_num)
theorem B2732117 : Blo 1819611 2732117 := bbase (se 8 (by rfl) ⟨16008, by rfl⟩ : syracuseStep 2732117 = 32017) (by norm_num)
theorem B2732141 : Blo 1819611 2732141 := bbase (se 3 (by rfl) ⟨512276, by rfl⟩ : syracuseStep 2732141 = 1024553) (by norm_num)
theorem B6910069 : Blo 1819611 6910069 := bbase (se 5 (by rfl) ⟨323909, by rfl⟩ : syracuseStep 6910069 = 647819) (by norm_num)
theorem B9220229 : Blo 1819611 9220229 := bbase (se 4 (by rfl) ⟨864396, by rfl⟩ : syracuseStep 9220229 = 1728793) (by norm_num)
theorem B2732165 : Blo 1819611 2732165 := bbase (se 4 (by rfl) ⟨256140, by rfl⟩ : syracuseStep 2732165 = 512281) (by norm_num)
theorem B8753285 : Blo 1819611 8753285 := bbase (se 4 (by rfl) ⟨820620, by rfl⟩ : syracuseStep 8753285 = 1641241) (by norm_num)
theorem B2732189 : Blo 1819611 2732189 := bbase (se 3 (by rfl) ⟨512285, by rfl⟩ : syracuseStep 2732189 = 1024571) (by norm_num)
theorem B3281077 : Blo 1819611 3281077 := bbase (se 5 (by rfl) ⟨153800, by rfl⟩ : syracuseStep 3281077 = 307601) (by norm_num)
theorem B2732213 : Blo 1819611 2732213 := bbase (se 5 (by rfl) ⟨128072, by rfl⟩ : syracuseStep 2732213 = 256145) (by norm_num)
theorem B2732237 : Blo 1819611 2732237 := bbase (se 3 (by rfl) ⟨512294, by rfl⟩ : syracuseStep 2732237 = 1024589) (by norm_num)
theorem B2732261 : Blo 1819611 2732261 := bbase (se 4 (by rfl) ⟨256149, by rfl⟩ : syracuseStep 2732261 = 512299) (by norm_num)
theorem B3281141 : Blo 1819611 3281141 := bbase (se 5 (by rfl) ⟨153803, by rfl⟩ : syracuseStep 3281141 = 307607) (by norm_num)
theorem B2732285 : Blo 1819611 2732285 := bbase (se 3 (by rfl) ⟨512303, by rfl⟩ : syracuseStep 2732285 = 1024607) (by norm_num)
theorem B2806037 : Blo 1819611 2806037 := bbase (se 6 (by rfl) ⟨65766, by rfl⟩ : syracuseStep 2806037 = 131533) (by norm_num)
theorem B2732309 : Blo 1819611 2732309 := bbase (se 6 (by rfl) ⟨64038, by rfl⟩ : syracuseStep 2732309 = 128077) (by norm_num)
theorem B2732333 : Blo 1819611 2732333 := bbase (se 3 (by rfl) ⟨512312, by rfl⟩ : syracuseStep 2732333 = 1024625) (by norm_num)
theorem B2732357 : Blo 1819611 2732357 := bbase (se 4 (by rfl) ⟨256158, by rfl⟩ : syracuseStep 2732357 = 512317) (by norm_num)
theorem B3887453 : Blo 1819611 3887453 := bbase (se 3 (by rfl) ⟨728897, by rfl⟩ : syracuseStep 3887453 = 1457795) (by norm_num)
theorem B2732381 : Blo 1819611 2732381 := bbase (se 3 (by rfl) ⟨512321, by rfl⟩ : syracuseStep 2732381 = 1024643) (by norm_num)
theorem B3887461 : Blo 1819611 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B4608373 : Blo 1819611 4608373 := bbase (se 5 (by rfl) ⟨216017, by rfl⟩ : syracuseStep 4608373 = 432035) (by norm_num)
theorem B2732405 : Blo 1819611 2732405 := bbase (se 5 (by rfl) ⟨128081, by rfl⟩ : syracuseStep 2732405 = 256163) (by norm_num)
theorem B6910373 : Blo 1819611 6910373 := bbase (se 4 (by rfl) ⟨647847, by rfl⟩ : syracuseStep 6910373 = 1295695) (by norm_num)
theorem B4608485 : Blo 1819611 4608485 := bbase (se 4 (by rfl) ⟨432045, by rfl⟩ : syracuseStep 4608485 = 864091) (by norm_num)
theorem B9212453 : Blo 1819611 9212453 := bbase (se 4 (by rfl) ⟨863667, by rfl⟩ : syracuseStep 9212453 = 1727335) (by norm_num)
theorem B4608677 : Blo 1819611 4608677 := bbase (se 4 (by rfl) ⟨432063, by rfl⟩ : syracuseStep 4608677 = 864127) (by norm_num)
theorem B2593549 : Blo 1819611 2593549 := bbase (se 3 (by rfl) ⟨486290, by rfl⟩ : syracuseStep 2593549 = 972581) (by norm_num)
theorem B17494805 : Blo 1819611 17494805 := bbase (se 6 (by rfl) ⟨410034, by rfl⟩ : syracuseStep 17494805 = 820069) (by norm_num)
theorem B5182325 : Blo 1819611 5182325 := bbase (se 5 (by rfl) ⟨242921, by rfl⟩ : syracuseStep 5182325 = 485843) (by norm_num)
theorem B15553397 : Blo 1819611 15553397 := bbase (se 5 (by rfl) ⟨729065, by rfl⟩ : syracuseStep 15553397 = 1458131) (by norm_num)
theorem B16610197 : Blo 1819611 16610197 := bbase (se 6 (by rfl) ⟨389301, by rfl⟩ : syracuseStep 16610197 = 778603) (by norm_num)
theorem B4609021 : Blo 1819611 4609021 := bbase (se 3 (by rfl) ⟨864191, by rfl⟩ : syracuseStep 4609021 = 1728383) (by norm_num)
theorem B7779365 : Blo 1819611 7779365 := bbase (se 4 (by rfl) ⟨729315, by rfl⟩ : syracuseStep 7779365 = 1458631) (by norm_num)
theorem B4609133 : Blo 1819611 4609133 := bbase (se 3 (by rfl) ⟨864212, by rfl⟩ : syracuseStep 4609133 = 1728425) (by norm_num)
theorem B5534837 : Blo 1819611 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B3372205 : Blo 1819611 3372205 := bbase (se 3 (by rfl) ⟨632288, by rfl⟩ : syracuseStep 3372205 = 1264577) (by norm_num)
theorem B10507445 : Blo 1819611 10507445 := bbase (se 5 (by rfl) ⟨492536, by rfl⟩ : syracuseStep 10507445 = 985073) (by norm_num)
theorem B19674389 : Blo 1819611 19674389 := bbase (se 6 (by rfl) ⟨461118, by rfl⟩ : syracuseStep 19674389 = 922237) (by norm_num)
theorem B4609325 : Blo 1819611 4609325 := bbase (se 3 (by rfl) ⟨864248, by rfl⟩ : syracuseStep 4609325 = 1728497) (by norm_num)
theorem B9221525 : Blo 1819611 9221525 := bbase (se 6 (by rfl) ⟨216129, by rfl⟩ : syracuseStep 9221525 = 432259) (by norm_num)
theorem B6141365 : Blo 1819611 6141365 := bbase (se 5 (by rfl) ⟨287876, by rfl⟩ : syracuseStep 6141365 = 575753) (by norm_num)
theorem B3888589 : Blo 1819611 3888589 := bbase (se 3 (by rfl) ⟨729110, by rfl⟩ : syracuseStep 3888589 = 1458221) (by norm_num)
theorem B5994053 : Blo 1819611 5994053 := bbase (se 4 (by rfl) ⟨561942, by rfl⟩ : syracuseStep 5994053 = 1123885) (by norm_num)
theorem B92272213 : Blo 1819611 92272213 := bbase (se 8 (by rfl) ⟨540657, by rfl⟩ : syracuseStep 92272213 = 1081315) (by norm_num)
theorem B4609669 : Blo 1819611 4609669 := bbase (se 4 (by rfl) ⟨432156, by rfl⟩ : syracuseStep 4609669 = 864313) (by norm_num)
theorem B4609781 : Blo 1819611 4609781 := bbase (se 5 (by rfl) ⟨216083, by rfl⟩ : syracuseStep 4609781 = 432167) (by norm_num)
theorem B9213749 : Blo 1819611 9213749 := bbase (se 5 (by rfl) ⟨431894, by rfl⟩ : syracuseStep 9213749 = 863789) (by norm_num)
theorem B3888965 : Blo 1819611 3888965 := bbase (se 4 (by rfl) ⟨364590, by rfl⟩ : syracuseStep 3888965 = 729181) (by norm_num)
theorem B4372309 : Blo 1819611 4372309 := bbase (se 9 (by rfl) ⟨12809, by rfl⟩ : syracuseStep 4372309 = 25619) (by norm_num)
theorem B6141797 : Blo 1819611 6141797 := bbase (se 4 (by rfl) ⟨575793, by rfl⟩ : syracuseStep 6141797 = 1151587) (by norm_num)
theorem B5830501 : Blo 1819611 5830501 := bbase (se 4 (by rfl) ⟨546609, by rfl⟩ : syracuseStep 5830501 = 1093219) (by norm_num)
theorem B3692405 : Blo 1819611 3692405 := bbase (se 5 (by rfl) ⟨173081, by rfl⟩ : syracuseStep 3692405 = 346163) (by norm_num)
theorem B4609973 : Blo 1819611 4609973 := bbase (se 5 (by rfl) ⟨216092, by rfl⟩ : syracuseStep 4609973 = 432185) (by norm_num)
theorem B5183509 : Blo 1819611 5183509 := bbase (se 6 (by rfl) ⟨121488, by rfl⟩ : syracuseStep 5183509 = 242977) (by norm_num)
theorem B6559861 : Blo 1819611 6559861 := bbase (se 5 (by rfl) ⟨307493, by rfl⟩ : syracuseStep 6559861 = 614987) (by norm_num)
theorem B4372645 : Blo 1819611 4372645 := bbase (se 4 (by rfl) ⟨409935, by rfl⟩ : syracuseStep 4372645 = 819871) (by norm_num)
theorem B3455149 : Blo 1819611 3455149 := bbase (se 3 (by rfl) ⟨647840, by rfl⟩ : syracuseStep 3455149 = 1295681) (by norm_num)
theorem B5183669 : Blo 1819611 5183669 := bbase (se 5 (by rfl) ⟨242984, by rfl⟩ : syracuseStep 5183669 = 485969) (by norm_num)
theorem B10369205 : Blo 1819611 10369205 := bbase (se 5 (by rfl) ⟨486056, by rfl⟩ : syracuseStep 10369205 = 972113) (by norm_num)
theorem B4987109 : Blo 1819611 4987109 := bbase (se 4 (by rfl) ⟨467541, by rfl⟩ : syracuseStep 4987109 = 935083) (by norm_num)
theorem B4094189 : Blo 1819611 4094189 := bbase (se 3 (by rfl) ⟨767660, by rfl⟩ : syracuseStep 4094189 = 1535321) (by norm_num)
theorem B4610317 : Blo 1819611 4610317 := bbase (se 3 (by rfl) ⟨864434, by rfl⟩ : syracuseStep 4610317 = 1728869) (by norm_num)
theorem B6142229 : Blo 1819611 6142229 := bbase (se 6 (by rfl) ⟨143958, by rfl⟩ : syracuseStep 6142229 = 287917) (by norm_num)
theorem B4094261 : Blo 1819611 4094261 := bbase (se 5 (by rfl) ⟨191918, by rfl⟩ : syracuseStep 4094261 = 383837) (by norm_num)
theorem B3455293 : Blo 1819611 3455293 := bbase (se 3 (by rfl) ⟨647867, by rfl⟩ : syracuseStep 3455293 = 1295735) (by norm_num)
theorem B4921669 : Blo 1819611 4921669 := bbase (se 4 (by rfl) ⟨461406, by rfl⟩ : syracuseStep 4921669 = 922813) (by norm_num)
theorem B17733973 : Blo 1819611 17733973 := bbase (se 10 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 17733973 = 51955) (by norm_num)
theorem B4094333 : Blo 1819611 4094333 := bbase (se 3 (by rfl) ⟨767687, by rfl⟩ : syracuseStep 4094333 = 1535375) (by norm_num)
theorem B4610429 : Blo 1819611 4610429 := bbase (se 3 (by rfl) ⟨864455, by rfl⟩ : syracuseStep 4610429 = 1728911) (by norm_num)
theorem B5183909 : Blo 1819611 5183909 := bbase (se 4 (by rfl) ⟨485991, by rfl⟩ : syracuseStep 5183909 = 971983) (by norm_num)
theorem B4094405 : Blo 1819611 4094405 := bbase (se 4 (by rfl) ⟨383850, by rfl⟩ : syracuseStep 4094405 = 767701) (by norm_num)
theorem B3037637 : Blo 1819611 3037637 := bbase (se 4 (by rfl) ⟨284778, by rfl⟩ : syracuseStep 3037637 = 569557) (by norm_num)
theorem B5257685 : Blo 1819611 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B3455453 : Blo 1819611 3455453 := bbase (se 3 (by rfl) ⟨647897, by rfl⟩ : syracuseStep 3455453 = 1295795) (by norm_num)
theorem B6912485 : Blo 1819611 6912485 := bbase (se 4 (by rfl) ⟨648045, by rfl⟩ : syracuseStep 6912485 = 1296091) (by norm_num)
theorem B4094477 : Blo 1819611 4094477 := bbase (se 3 (by rfl) ⟨767714, by rfl⟩ : syracuseStep 4094477 = 1535429) (by norm_num)
theorem B4610621 : Blo 1819611 4610621 := bbase (se 3 (by rfl) ⟨864491, by rfl⟩ : syracuseStep 4610621 = 1728983) (by norm_num)
theorem B4094549 : Blo 1819611 4094549 := bbase (se 8 (by rfl) ⟨23991, by rfl⟩ : syracuseStep 4094549 = 47983) (by norm_num)
theorem B5184101 : Blo 1819611 5184101 := bbase (se 4 (by rfl) ⟨486009, by rfl⟩ : syracuseStep 5184101 = 972019) (by norm_num)
theorem B3455597 : Blo 1819611 3455597 := bbase (se 3 (by rfl) ⟨647924, by rfl⟩ : syracuseStep 3455597 = 1295849) (by norm_num)
theorem B4094621 : Blo 1819611 4094621 := bbase (se 3 (by rfl) ⟨767741, by rfl⟩ : syracuseStep 4094621 = 1535483) (by norm_num)
theorem B6142661 : Blo 1819611 6142661 := bbase (se 4 (by rfl) ⟨575874, by rfl⟩ : syracuseStep 6142661 = 1151749) (by norm_num)
theorem B3070669 : Blo 1819611 3070669 := bbase (se 3 (by rfl) ⟨575750, by rfl⟩ : syracuseStep 3070669 = 1151501) (by norm_num)
theorem B4094693 : Blo 1819611 4094693 := bbase (se 4 (by rfl) ⟨383877, by rfl⟩ : syracuseStep 4094693 = 767755) (by norm_num)
theorem B6912773 : Blo 1819611 6912773 := bbase (se 4 (by rfl) ⟨648072, by rfl⟩ : syracuseStep 6912773 = 1296145) (by norm_num)
theorem B4373261 : Blo 1819611 4373261 := bbase (se 3 (by rfl) ⟨819986, by rfl⟩ : syracuseStep 4373261 = 1639973) (by norm_num)
theorem B3070757 : Blo 1819611 3070757 := bbase (se 4 (by rfl) ⟨287883, by rfl⟩ : syracuseStep 3070757 = 575767) (by norm_num)
theorem B4094765 : Blo 1819611 4094765 := bbase (se 3 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 4094765 = 1535537) (by norm_num)
theorem B4094837 : Blo 1819611 4094837 := bbase (se 5 (by rfl) ⟨191945, by rfl⟩ : syracuseStep 4094837 = 383891) (by norm_num)
theorem B3455885 : Blo 1819611 3455885 := bbase (se 3 (by rfl) ⟨647978, by rfl⟩ : syracuseStep 3455885 = 1295957) (by norm_num)
theorem B7773077 : Blo 1819611 7773077 := bbase (se 6 (by rfl) ⟨182181, by rfl⟩ : syracuseStep 7773077 = 364363) (by norm_num)
theorem B24902549 : Blo 1819611 24902549 := bbase (se 6 (by rfl) ⟨583653, by rfl⟩ : syracuseStep 24902549 = 1167307) (by norm_num)
theorem B3070885 : Blo 1819611 3070885 := bbase (se 4 (by rfl) ⟨287895, by rfl⟩ : syracuseStep 3070885 = 575791) (by norm_num)
theorem B2915237 : Blo 1819611 2915237 := bbase (se 4 (by rfl) ⟨273303, by rfl⟩ : syracuseStep 2915237 = 546607) (by norm_num)
theorem B8305573 : Blo 1819611 8305573 := bbase (se 4 (by rfl) ⟨778647, by rfl⟩ : syracuseStep 8305573 = 1557295) (by norm_num)
theorem B4094909 : Blo 1819611 4094909 := bbase (se 3 (by rfl) ⟨767795, by rfl⟩ : syracuseStep 4094909 = 1535591) (by norm_num)
theorem B2186197 : Blo 1819611 2186197 := bbase (se 7 (by rfl) ⟨25619, by rfl⟩ : syracuseStep 2186197 = 51239) (by norm_num)
theorem B3070973 : Blo 1819611 3070973 := bbase (se 3 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 3070973 = 1151615) (by norm_num)
theorem B4094981 : Blo 1819611 4094981 := bbase (se 4 (by rfl) ⟨383904, by rfl⟩ : syracuseStep 4094981 = 767809) (by norm_num)
theorem B3456037 : Blo 1819611 3456037 := bbase (se 4 (by rfl) ⟨324003, by rfl⟩ : syracuseStep 3456037 = 648007) (by norm_num)
theorem B9215045 : Blo 1819611 9215045 := bbase (se 4 (by rfl) ⟨863910, by rfl⟩ : syracuseStep 9215045 = 1727821) (by norm_num)
theorem B4095053 : Blo 1819611 4095053 := bbase (se 3 (by rfl) ⟨767822, by rfl⟩ : syracuseStep 4095053 = 1535645) (by norm_num)
theorem B2047081 : Blo 1819611 2047081 := bbase (se 2 (by rfl) ⟨767655, by rfl⟩ : syracuseStep 2047081 = 1535311) (by norm_num)
theorem B6143093 : Blo 1819611 6143093 := bbase (se 5 (by rfl) ⟨287957, by rfl⟩ : syracuseStep 6143093 = 575915) (by norm_num)
theorem B3071101 : Blo 1819611 3071101 := bbase (se 3 (by rfl) ⟨575831, by rfl⟩ : syracuseStep 3071101 = 1151663) (by norm_num)
theorem B7773317 : Blo 1819611 7773317 := bbase (se 4 (by rfl) ⟨728748, by rfl⟩ : syracuseStep 7773317 = 1457497) (by norm_num)
theorem B2047117 : Blo 1819611 2047117 := bbase (se 3 (by rfl) ⟨383834, by rfl⟩ : syracuseStep 2047117 = 767669) (by norm_num)
theorem B4095125 : Blo 1819611 4095125 := bbase (se 6 (by rfl) ⟨95979, by rfl⟩ : syracuseStep 4095125 = 191959) (by norm_num)
theorem B2768021 : Blo 1819611 2768021 := bbase (se 6 (by rfl) ⟨64875, by rfl⟩ : syracuseStep 2768021 = 129751) (by norm_num)
theorem B2047153 : Blo 1819611 2047153 := bbase (se 2 (by rfl) ⟨767682, by rfl⟩ : syracuseStep 2047153 = 1535365) (by norm_num)
theorem B13327541 : Blo 1819611 13327541 := bbase (se 5 (by rfl) ⟨624728, by rfl⟩ : syracuseStep 13327541 = 1249457) (by norm_num)
theorem B4373693 : Blo 1819611 4373693 := bbase (se 3 (by rfl) ⟨820067, by rfl⟩ : syracuseStep 4373693 = 1640135) (by norm_num)
theorem B2047189 : Blo 1819611 2047189 := bbase (se 7 (by rfl) ⟨23990, by rfl⟩ : syracuseStep 2047189 = 47981) (by norm_num)
theorem B3071189 : Blo 1819611 3071189 := bbase (se 7 (by rfl) ⟨35990, by rfl⟩ : syracuseStep 3071189 = 71981) (by norm_num)
theorem B4095197 : Blo 1819611 4095197 := bbase (se 3 (by rfl) ⟨767849, by rfl⟩ : syracuseStep 4095197 = 1535699) (by norm_num)
theorem B2047225 : Blo 1819611 2047225 := bbase (se 2 (by rfl) ⟨767709, by rfl⟩ : syracuseStep 2047225 = 1535419) (by norm_num)
theorem B9469189 : Blo 1819611 9469189 := bbase (se 4 (by rfl) ⟨887736, by rfl⟩ : syracuseStep 9469189 = 1775473) (by norm_num)
theorem B2047261 : Blo 1819611 2047261 := bbase (se 3 (by rfl) ⟨383861, by rfl⟩ : syracuseStep 2047261 = 767723) (by norm_num)
theorem B4095269 : Blo 1819611 4095269 := bbase (se 4 (by rfl) ⟨383931, by rfl⟩ : syracuseStep 4095269 = 767863) (by norm_num)
theorem B2047297 : Blo 1819611 2047297 := bbase (se 2 (by rfl) ⟨767736, by rfl⟩ : syracuseStep 2047297 = 1535473) (by norm_num)
theorem B3071317 : Blo 1819611 3071317 := bbase (se 11 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 3071317 = 4499) (by norm_num)
theorem B3456341 : Blo 1819611 3456341 := bbase (se 11 (by rfl) ⟨2531, by rfl⟩ : syracuseStep 3456341 = 5063) (by norm_num)
theorem B10370389 : Blo 1819611 10370389 := bbase (se 11 (by rfl) ⟨7595, by rfl⟩ : syracuseStep 10370389 = 15191) (by norm_num)
theorem B2047333 : Blo 1819611 2047333 := bbase (se 4 (by rfl) ⟨191937, by rfl⟩ : syracuseStep 2047333 = 383875) (by norm_num)
theorem B4095341 : Blo 1819611 4095341 := bbase (se 3 (by rfl) ⟨767876, by rfl⟩ : syracuseStep 4095341 = 1535753) (by norm_num)
theorem B2915693 : Blo 1819611 2915693 := bbase (se 3 (by rfl) ⟨546692, by rfl⟩ : syracuseStep 2915693 = 1093385) (by norm_num)
theorem B2047369 : Blo 1819611 2047369 := bbase (se 2 (by rfl) ⟨767763, by rfl⟩ : syracuseStep 2047369 = 1535527) (by norm_num)
theorem B2047405 : Blo 1819611 2047405 := bbase (se 3 (by rfl) ⟨383888, by rfl⟩ : syracuseStep 2047405 = 767777) (by norm_num)
theorem B3071405 : Blo 1819611 3071405 := bbase (se 3 (by rfl) ⟨575888, by rfl⟩ : syracuseStep 3071405 = 1151777) (by norm_num)
theorem B4210093 : Blo 1819611 4210093 := bbase (se 3 (by rfl) ⟨789392, by rfl⟩ : syracuseStep 4210093 = 1578785) (by norm_num)
theorem B4095413 : Blo 1819611 4095413 := bbase (se 5 (by rfl) ⟨191972, by rfl⟩ : syracuseStep 4095413 = 383945) (by norm_num)
theorem B2047441 : Blo 1819611 2047441 := bbase (se 2 (by rfl) ⟨767790, by rfl⟩ : syracuseStep 2047441 = 1535581) (by norm_num)
theorem B2047477 : Blo 1819611 2047477 := bbase (se 5 (by rfl) ⟨95975, by rfl⟩ : syracuseStep 2047477 = 191951) (by norm_num)
theorem B4095485 : Blo 1819611 4095485 := bbase (se 3 (by rfl) ⟨767903, by rfl⟩ : syracuseStep 4095485 = 1535807) (by norm_num)
theorem B2047513 : Blo 1819611 2047513 := bbase (se 2 (by rfl) ⟨767817, by rfl⟩ : syracuseStep 2047513 = 1535635) (by norm_num)
theorem B1998361 : Blo 1819611 1998361 := bbase (se 2 (by rfl) ⟨749385, by rfl⟩ : syracuseStep 1998361 = 1498771) (by norm_num)
theorem B3939877 : Blo 1819611 3939877 := bbase (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) (by norm_num)
theorem B6143525 : Blo 1819611 6143525 := bbase (se 4 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 6143525 = 1151911) (by norm_num)
theorem B3071533 : Blo 1819611 3071533 := bbase (se 3 (by rfl) ⟨575912, by rfl⟩ : syracuseStep 3071533 = 1151825) (by norm_num)
theorem B4496941 : Blo 1819611 4496941 := bbase (se 3 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 4496941 = 1686353) (by norm_num)
theorem B2047549 : Blo 1819611 2047549 := bbase (se 3 (by rfl) ⟨383915, by rfl⟩ : syracuseStep 2047549 = 767831) (by norm_num)
theorem B4095557 : Blo 1819611 4095557 := bbase (se 4 (by rfl) ⟨383958, by rfl⟩ : syracuseStep 4095557 = 767917) (by norm_num)
theorem B5185093 : Blo 1819611 5185093 := bbase (se 4 (by rfl) ⟨486102, by rfl⟩ : syracuseStep 5185093 = 972205) (by norm_num)
theorem B2047585 : Blo 1819611 2047585 := bbase (se 2 (by rfl) ⟨767844, by rfl⟩ : syracuseStep 2047585 = 1535689) (by norm_num)
theorem B2047621 : Blo 1819611 2047621 := bbase (se 4 (by rfl) ⟨191964, by rfl⟩ : syracuseStep 2047621 = 383929) (by norm_num)
theorem B3071621 : Blo 1819611 3071621 := bbase (se 4 (by rfl) ⟨287964, by rfl⟩ : syracuseStep 3071621 = 575929) (by norm_num)
theorem B4095629 : Blo 1819611 4095629 := bbase (se 3 (by rfl) ⟨767930, by rfl⟩ : syracuseStep 4095629 = 1535861) (by norm_num)
theorem B2047657 : Blo 1819611 2047657 := bbase (se 2 (by rfl) ⟨767871, by rfl⟩ : syracuseStep 2047657 = 1535743) (by norm_num)
theorem B2047693 : Blo 1819611 2047693 := bbase (se 3 (by rfl) ⟨383942, by rfl⟩ : syracuseStep 2047693 = 767885) (by norm_num)
theorem B4095701 : Blo 1819611 4095701 := bbase (se 7 (by rfl) ⟨47996, by rfl⟩ : syracuseStep 4095701 = 95993) (by norm_num)
theorem B2047729 : Blo 1819611 2047729 := bbase (se 2 (by rfl) ⟨767898, by rfl⟩ : syracuseStep 2047729 = 1535797) (by norm_num)
theorem B3071749 : Blo 1819611 3071749 := bbase (se 4 (by rfl) ⟨287976, by rfl⟩ : syracuseStep 3071749 = 575953) (by norm_num)
theorem B2047765 : Blo 1819611 2047765 := bbase (se 6 (by rfl) ⟨47994, by rfl⟩ : syracuseStep 2047765 = 95989) (by norm_num)
theorem B15556373 : Blo 1819611 15556373 := bbase (se 6 (by rfl) ⟨364602, by rfl⟩ : syracuseStep 15556373 = 729205) (by norm_num)
theorem B4095773 : Blo 1819611 4095773 := bbase (se 3 (by rfl) ⟨767957, by rfl⟩ : syracuseStep 4095773 = 1535915) (by norm_num)
theorem B4923173 : Blo 1819611 4923173 := bbase (se 4 (by rfl) ⟨461547, by rfl⟩ : syracuseStep 4923173 = 923095) (by norm_num)
theorem B4374317 : Blo 1819611 4374317 := bbase (se 3 (by rfl) ⟨820184, by rfl⟩ : syracuseStep 4374317 = 1640369) (by norm_num)
theorem B2047801 : Blo 1819611 2047801 := bbase (se 2 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 2047801 = 1535851) (by norm_num)
theorem B2047837 : Blo 1819611 2047837 := bbase (se 3 (by rfl) ⟨383969, by rfl⟩ : syracuseStep 2047837 = 767939) (by norm_num)
theorem B3071837 : Blo 1819611 3071837 := bbase (se 3 (by rfl) ⟨575969, by rfl⟩ : syracuseStep 3071837 = 1151939) (by norm_num)
theorem B2187101 : Blo 1819611 2187101 := bbase (se 3 (by rfl) ⟨410081, by rfl⟩ : syracuseStep 2187101 = 820163) (by norm_num)
theorem B4095845 : Blo 1819611 4095845 := bbase (se 4 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 4095845 = 767971) (by norm_num)
theorem B2047873 : Blo 1819611 2047873 := bbase (se 2 (by rfl) ⟨767952, by rfl⟩ : syracuseStep 2047873 = 1535905) (by norm_num)
theorem B4923269 : Blo 1819611 4923269 := bbase (se 4 (by rfl) ⟨461556, by rfl⟩ : syracuseStep 4923269 = 923113) (by norm_num)
theorem B2047909 : Blo 1819611 2047909 := bbase (se 4 (by rfl) ⟨191991, by rfl⟩ : syracuseStep 2047909 = 383983) (by norm_num)
theorem B6913957 : Blo 1819611 6913957 := bbase (se 4 (by rfl) ⟨648183, by rfl⟩ : syracuseStep 6913957 = 1296367) (by norm_num)
theorem B4095917 : Blo 1819611 4095917 := bbase (se 3 (by rfl) ⟨767984, by rfl⟩ : syracuseStep 4095917 = 1535969) (by norm_num)
theorem B2047945 : Blo 1819611 2047945 := bbase (se 2 (by rfl) ⟨767979, by rfl⟩ : syracuseStep 2047945 = 1535959) (by norm_num)
theorem B6143957 : Blo 1819611 6143957 := bbase (se 7 (by rfl) ⟨71999, by rfl⟩ : syracuseStep 6143957 = 143999) (by norm_num)
theorem B14770133 : Blo 1819611 14770133 := bbase (se 7 (by rfl) ⟨173087, by rfl⟩ : syracuseStep 14770133 = 346175) (by norm_num)
theorem B3071965 : Blo 1819611 3071965 := bbase (se 3 (by rfl) ⟨575993, by rfl⟩ : syracuseStep 3071965 = 1151987) (by norm_num)
theorem B2047981 : Blo 1819611 2047981 := bbase (se 3 (by rfl) ⟨383996, by rfl⟩ : syracuseStep 2047981 = 767993) (by norm_num)
theorem B4095989 : Blo 1819611 4095989 := bbase (se 5 (by rfl) ⟨191999, by rfl⟩ : syracuseStep 4095989 = 383999) (by norm_num)
theorem B2334739 : Blo 1819611 2334739 := bstep (se 1 (by rfl) ⟨1751054, by rfl⟩ : syracuseStep 2334739 = 3502109) B3502109
theorem B3072019 : Blo 1819611 3072019 := bstep (se 1 (by rfl) ⟨2304014, by rfl⟩ : syracuseStep 3072019 = 4608029) B4608029
theorem B2048035 : Blo 1819611 2048035 := bstep (se 1 (by rfl) ⟨1536026, by rfl⟩ : syracuseStep 2048035 = 3072053) B3072053
theorem B19685429 : Blo 1819611 19685429 := bstep (se 5 (by rfl) ⟨922754, by rfl⟩ : syracuseStep 19685429 = 1845509) B1845509
theorem B2916481 : Blo 1819611 2916481 := bstep (se 2 (by rfl) ⟨1093680, by rfl⟩ : syracuseStep 2916481 = 2187361) B2187361
theorem B10657925 : Blo 1819611 10657925 := bstep (se 4 (by rfl) ⟨999180, by rfl⟩ : syracuseStep 10657925 = 1998361) B1998361
theorem B3072161 : Blo 1819611 3072161 := bstep (se 2 (by rfl) ⟨1152060, by rfl⟩ : syracuseStep 3072161 = 2304121) B2304121
theorem B6144173 : Blo 1819611 6144173 := bstep (se 3 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 6144173 = 2304065) B2304065
theorem B2048179 : Blo 1819611 2048179 := bstep (se 1 (by rfl) ⟨1536134, by rfl⟩ : syracuseStep 2048179 = 3072269) B3072269
theorem B6144227 : Blo 1819611 6144227 := bstep (se 1 (by rfl) ⟨4608170, by rfl⟩ : syracuseStep 6144227 = 9216341) B9216341
theorem B4096241 : Blo 1819611 4096241 := bstep (se 2 (by rfl) ⟨1536090, by rfl⟩ : syracuseStep 4096241 = 3072181) B3072181
theorem B4096259 : Blo 1819611 4096259 := bstep (se 1 (by rfl) ⟨3072194, by rfl⟩ : syracuseStep 4096259 = 6144389) B6144389
theorem B23642381 : Blo 1819611 23642381 := bstep (se 3 (by rfl) ⟨4432946, by rfl⟩ : syracuseStep 23642381 = 8865893) B8865893
theorem B3072289 : Blo 1819611 3072289 := bstep (se 2 (by rfl) ⟨1152108, by rfl⟩ : syracuseStep 3072289 = 2304217) B2304217
theorem B3072323 : Blo 1819611 3072323 := bstep (se 1 (by rfl) ⟨2304242, by rfl⟩ : syracuseStep 3072323 = 4608485) B4608485
theorem B2048323 : Blo 1819611 2048323 := bstep (se 1 (by rfl) ⟨1536242, by rfl⟩ : syracuseStep 2048323 = 3072485) B3072485
theorem B2916737 : Blo 1819611 2916737 := bstep (se 2 (by rfl) ⟨1093776, by rfl⟩ : syracuseStep 2916737 = 2187553) B2187553
theorem B6562225 : Blo 1819611 6562225 := bstep (se 2 (by rfl) ⟨2460834, by rfl⟩ : syracuseStep 6562225 = 4921669) B4921669
theorem B3072451 : Blo 1819611 3072451 := bstep (se 1 (by rfl) ⟨2304338, by rfl⟩ : syracuseStep 3072451 = 4608677) B4608677
theorem B12460493 : Blo 1819611 12460493 := bstep (se 3 (by rfl) ⟨2336342, by rfl⟩ : syracuseStep 12460493 = 4672685) B4672685
theorem B2048467 : Blo 1819611 2048467 := bstep (se 1 (by rfl) ⟨1536350, by rfl⟩ : syracuseStep 2048467 = 3072701) B3072701
theorem B6144497 : Blo 1819611 6144497 := bstep (se 2 (by rfl) ⟨2304186, by rfl⟩ : syracuseStep 6144497 = 4608373) B4608373
theorem B4096529 : Blo 1819611 4096529 := bstep (se 2 (by rfl) ⟨1536198, by rfl⟩ : syracuseStep 4096529 = 3072397) B3072397
theorem B4096547 : Blo 1819611 4096547 := bstep (se 1 (by rfl) ⟨3072410, by rfl⟩ : syracuseStep 4096547 = 6144821) B6144821
theorem B3072593 : Blo 1819611 3072593 := bstep (se 2 (by rfl) ⟨1152222, by rfl⟩ : syracuseStep 3072593 = 2304445) B2304445
theorem B2048611 : Blo 1819611 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B8749709 : Blo 1819611 8749709 := bstep (se 3 (by rfl) ⟨1640570, by rfl⟩ : syracuseStep 8749709 = 3281141) B3281141
theorem B5186243 : Blo 1819611 5186243 := bstep (se 1 (by rfl) ⟨3889682, by rfl⟩ : syracuseStep 5186243 = 7779365) B7779365
theorem B9847493 : Blo 1819611 9847493 := bstep (se 4 (by rfl) ⟨923202, by rfl⟩ : syracuseStep 9847493 = 1846405) B1846405
theorem B3072721 : Blo 1819611 3072721 := bstep (se 2 (by rfl) ⟨1152270, by rfl⟩ : syracuseStep 3072721 = 2304541) B2304541
theorem B3072755 : Blo 1819611 3072755 := bstep (se 1 (by rfl) ⟨2304566, by rfl⟩ : syracuseStep 3072755 = 4609133) B4609133
theorem B2048755 : Blo 1819611 2048755 := bstep (se 1 (by rfl) ⟨1536566, by rfl⟩ : syracuseStep 2048755 = 3073133) B3073133
theorem B7004963 : Blo 1819611 7004963 := bstep (se 1 (by rfl) ⟨5253722, by rfl⟩ : syracuseStep 7004963 = 10507445) B10507445
theorem B4096817 : Blo 1819611 4096817 := bstep (se 2 (by rfl) ⟨1536306, by rfl⟩ : syracuseStep 4096817 = 3072613) B3072613
theorem B20742965 : Blo 1819611 20742965 := bstep (se 5 (by rfl) ⟨972326, by rfl⟩ : syracuseStep 20742965 = 1944653) B1944653
theorem B4096835 : Blo 1819611 4096835 := bstep (se 1 (by rfl) ⟨3072626, by rfl⟩ : syracuseStep 4096835 = 6145253) B6145253
theorem B5833549 : Blo 1819611 5833549 := bstep (se 3 (by rfl) ⟨1093790, by rfl⟩ : syracuseStep 5833549 = 2187581) B2187581
theorem B13116259 : Blo 1819611 13116259 := bstep (se 1 (by rfl) ⟨9837194, by rfl⟩ : syracuseStep 13116259 = 19674389) B19674389
theorem B6914915 : Blo 1819611 6914915 := bstep (se 1 (by rfl) ⟨5186186, by rfl⟩ : syracuseStep 6914915 = 10372373) B10372373
theorem B6914929 : Blo 1819611 6914929 := bstep (se 2 (by rfl) ⟨2593098, by rfl⟩ : syracuseStep 6914929 = 5186197) B5186197
theorem B3072883 : Blo 1819611 3072883 := bstep (se 1 (by rfl) ⟨2304662, by rfl⟩ : syracuseStep 3072883 = 4609325) B4609325
theorem B2048899 : Blo 1819611 2048899 := bstep (se 1 (by rfl) ⟨1536674, by rfl⟩ : syracuseStep 2048899 = 3073349) B3073349
theorem B17499077 : Blo 1819611 17499077 := bstep (se 4 (by rfl) ⟨1640538, by rfl⟩ : syracuseStep 17499077 = 3281077) B3281077
theorem B4154321 : Blo 1819611 4154321 := bstep (se 2 (by rfl) ⟨1557870, by rfl⟩ : syracuseStep 4154321 = 3115741) B3115741
theorem B1819619 : Blo 1819611 1819619 := bstep (se 1 (by rfl) ⟨1364714, by rfl⟩ : syracuseStep 1819619 = 2729429) B2729429
theorem B1819635 : Blo 1819611 1819635 := bstep (se 1 (by rfl) ⟨1364726, by rfl⟩ : syracuseStep 1819635 = 2729453) B2729453
theorem B3073025 : Blo 1819611 3073025 := bstep (se 2 (by rfl) ⟨1152384, by rfl⟩ : syracuseStep 3073025 = 2304769) B2304769
theorem B1819651 : Blo 1819611 1819651 := bstep (se 1 (by rfl) ⟨1364738, by rfl⟩ : syracuseStep 1819651 = 2729477) B2729477
theorem B6145037 : Blo 1819611 6145037 := bstep (se 3 (by rfl) ⟨1152194, by rfl⟩ : syracuseStep 6145037 = 2304389) B2304389
theorem B3458065 : Blo 1819611 3458065 := bstep (se 2 (by rfl) ⟨1296774, by rfl⟩ : syracuseStep 3458065 = 2593549) B2593549
theorem B1819667 : Blo 1819611 1819667 := bstep (se 1 (by rfl) ⟨1364750, by rfl⟩ : syracuseStep 1819667 = 2729501) B2729501
theorem B2049043 : Blo 1819611 2049043 := bstep (se 1 (by rfl) ⟨1536782, by rfl⟩ : syracuseStep 2049043 = 3073565) B3073565
theorem B1819683 : Blo 1819611 1819683 := bstep (se 1 (by rfl) ⟨1364762, by rfl⟩ : syracuseStep 1819683 = 2729525) B2729525
theorem B1819699 : Blo 1819611 1819699 := bstep (se 1 (by rfl) ⟨1364774, by rfl⟩ : syracuseStep 1819699 = 2729549) B2729549
theorem B2917441 : Blo 1819611 2917441 := bstep (se 2 (by rfl) ⟨1094040, by rfl⟩ : syracuseStep 2917441 = 2188081) B2188081
theorem B1819715 : Blo 1819611 1819715 := bstep (se 1 (by rfl) ⟨1364786, by rfl⟩ : syracuseStep 1819715 = 2729573) B2729573
theorem B6145091 : Blo 1819611 6145091 := bstep (se 1 (by rfl) ⟨4608818, by rfl⟩ : syracuseStep 6145091 = 9217637) B9217637
theorem B4097105 : Blo 1819611 4097105 := bstep (se 2 (by rfl) ⟨1536414, by rfl⟩ : syracuseStep 4097105 = 3072829) B3072829
theorem B1819731 : Blo 1819611 1819731 := bstep (se 1 (by rfl) ⟨1364798, by rfl⟩ : syracuseStep 1819731 = 2729597) B2729597
theorem B1819747 : Blo 1819611 1819747 := bstep (se 1 (by rfl) ⟨1364810, by rfl⟩ : syracuseStep 1819747 = 2729621) B2729621
theorem B4097123 : Blo 1819611 4097123 := bstep (se 1 (by rfl) ⟨3072842, by rfl⟩ : syracuseStep 4097123 = 6145685) B6145685
theorem B1819763 : Blo 1819611 1819763 := bstep (se 1 (by rfl) ⟨1364822, by rfl⟩ : syracuseStep 1819763 = 2729645) B2729645
theorem B3073153 : Blo 1819611 3073153 := bstep (se 2 (by rfl) ⟨1152432, by rfl⟩ : syracuseStep 3073153 = 2304865) B2304865
theorem B1819779 : Blo 1819611 1819779 := bstep (se 1 (by rfl) ⟨1364834, by rfl⟩ : syracuseStep 1819779 = 2729669) B2729669
theorem B1819795 : Blo 1819611 1819795 := bstep (se 1 (by rfl) ⟨1364846, by rfl⟩ : syracuseStep 1819795 = 2729693) B2729693
theorem B1819811 : Blo 1819611 1819811 := bstep (se 1 (by rfl) ⟨1364858, by rfl⟩ : syracuseStep 1819811 = 2729717) B2729717
theorem B3073187 : Blo 1819611 3073187 := bstep (se 1 (by rfl) ⟨2304890, by rfl⟩ : syracuseStep 3073187 = 4609781) B4609781
theorem B2049187 : Blo 1819611 2049187 := bstep (se 1 (by rfl) ⟨1536890, by rfl⟩ : syracuseStep 2049187 = 3073781) B3073781
theorem B1819827 : Blo 1819611 1819827 := bstep (se 1 (by rfl) ⟨1364870, by rfl⟩ : syracuseStep 1819827 = 2729741) B2729741
theorem B1819843 : Blo 1819611 1819843 := bstep (se 1 (by rfl) ⟨1364882, by rfl⟩ : syracuseStep 1819843 = 2729765) B2729765
theorem B1819859 : Blo 1819611 1819859 := bstep (se 1 (by rfl) ⟨1364894, by rfl⟩ : syracuseStep 1819859 = 2729789) B2729789
theorem B1819875 : Blo 1819611 1819875 := bstep (se 1 (by rfl) ⟨1364906, by rfl⟩ : syracuseStep 1819875 = 2729813) B2729813
theorem B1819891 : Blo 1819611 1819891 := bstep (se 1 (by rfl) ⟨1364918, by rfl⟩ : syracuseStep 1819891 = 2729837) B2729837
theorem B1819907 : Blo 1819611 1819907 := bstep (se 1 (by rfl) ⟨1364930, by rfl⟩ : syracuseStep 1819907 = 2729861) B2729861
theorem B1819923 : Blo 1819611 1819923 := bstep (se 1 (by rfl) ⟨1364942, by rfl⟩ : syracuseStep 1819923 = 2729885) B2729885
theorem B1819939 : Blo 1819611 1819939 := bstep (se 1 (by rfl) ⟨1364954, by rfl⟩ : syracuseStep 1819939 = 2729909) B2729909
theorem B3073315 : Blo 1819611 3073315 := bstep (se 1 (by rfl) ⟨2304986, by rfl⟩ : syracuseStep 3073315 = 4609973) B4609973
theorem B1819955 : Blo 1819611 1819955 := bstep (se 1 (by rfl) ⟨1364966, by rfl⟩ : syracuseStep 1819955 = 2729933) B2729933
theorem B1819971 : Blo 1819611 1819971 := bstep (se 1 (by rfl) ⟨1364978, by rfl⟩ : syracuseStep 1819971 = 2729957) B2729957
theorem B5834051 : Blo 1819611 5834051 := bstep (se 1 (by rfl) ⟨4375538, by rfl⟩ : syracuseStep 5834051 = 8751077) B8751077
theorem B6145361 : Blo 1819611 6145361 := bstep (se 2 (by rfl) ⟨2304510, by rfl⟩ : syracuseStep 6145361 = 4609021) B4609021
theorem B1819987 : Blo 1819611 1819987 := bstep (se 1 (by rfl) ⟨1364990, by rfl⟩ : syracuseStep 1819987 = 2729981) B2729981
theorem B1820003 : Blo 1819611 1820003 := bstep (se 1 (by rfl) ⟨1365002, by rfl⟩ : syracuseStep 1820003 = 2730005) B2730005
theorem B4097393 : Blo 1819611 4097393 := bstep (se 2 (by rfl) ⟨1536522, by rfl⟩ : syracuseStep 4097393 = 3073045) B3073045
theorem B1820019 : Blo 1819611 1820019 := bstep (se 1 (by rfl) ⟨1365014, by rfl⟩ : syracuseStep 1820019 = 2730029) B2730029
theorem B1820035 : Blo 1819611 1820035 := bstep (se 1 (by rfl) ⟨1365026, by rfl⟩ : syracuseStep 1820035 = 2730053) B2730053
theorem B4097411 : Blo 1819611 4097411 := bstep (se 1 (by rfl) ⟨3073058, by rfl⟩ : syracuseStep 4097411 = 6146117) B6146117
theorem B1820051 : Blo 1819611 1820051 := bstep (se 1 (by rfl) ⟨1365038, by rfl⟩ : syracuseStep 1820051 = 2730077) B2730077
theorem B1820067 : Blo 1819611 1820067 := bstep (se 1 (by rfl) ⟨1365050, by rfl⟩ : syracuseStep 1820067 = 2730101) B2730101
theorem B3073457 : Blo 1819611 3073457 := bstep (se 2 (by rfl) ⟨1152546, by rfl⟩ : syracuseStep 3073457 = 2305093) B2305093
theorem B1820083 : Blo 1819611 1820083 := bstep (se 1 (by rfl) ⟨1365062, by rfl⟩ : syracuseStep 1820083 = 2730125) B2730125
theorem B1820099 : Blo 1819611 1820099 := bstep (se 1 (by rfl) ⟨1365074, by rfl⟩ : syracuseStep 1820099 = 2730149) B2730149
theorem B1820115 : Blo 1819611 1820115 := bstep (se 1 (by rfl) ⟨1365086, by rfl⟩ : syracuseStep 1820115 = 2730173) B2730173
theorem B2729441 : Blo 1819611 2729441 := bstep (se 2 (by rfl) ⟨1023540, by rfl⟩ : syracuseStep 2729441 = 2047081) B2047081
theorem B1820131 : Blo 1819611 1820131 := bstep (se 1 (by rfl) ⟨1365098, by rfl⟩ : syracuseStep 1820131 = 2730197) B2730197
theorem B13305329 : Blo 1819611 13305329 := bstep (se 2 (by rfl) ⟨4989498, by rfl⟩ : syracuseStep 13305329 = 9978997) B9978997
theorem B2729459 : Blo 1819611 2729459 := bstep (se 1 (by rfl) ⟨2047094, by rfl⟩ : syracuseStep 2729459 = 4094189) B4094189
theorem B1820147 : Blo 1819611 1820147 := bstep (se 1 (by rfl) ⟨1365110, by rfl⟩ : syracuseStep 1820147 = 2730221) B2730221
theorem B1820163 : Blo 1819611 1820163 := bstep (se 1 (by rfl) ⟨1365122, by rfl⟩ : syracuseStep 1820163 = 2730245) B2730245
theorem B2729489 : Blo 1819611 2729489 := bstep (se 2 (by rfl) ⟨1023558, by rfl⟩ : syracuseStep 2729489 = 2047117) B2047117
theorem B1820179 : Blo 1819611 1820179 := bstep (se 1 (by rfl) ⟨1365134, by rfl⟩ : syracuseStep 1820179 = 2730269) B2730269
theorem B2729507 : Blo 1819611 2729507 := bstep (se 1 (by rfl) ⟨2047130, by rfl⟩ : syracuseStep 2729507 = 4094261) B4094261
theorem B1820195 : Blo 1819611 1820195 := bstep (se 1 (by rfl) ⟨1365146, by rfl⟩ : syracuseStep 1820195 = 2730293) B2730293
theorem B3073585 : Blo 1819611 3073585 := bstep (se 2 (by rfl) ⟨1152594, by rfl⟩ : syracuseStep 3073585 = 2305189) B2305189
theorem B1820211 : Blo 1819611 1820211 := bstep (se 1 (by rfl) ⟨1365158, by rfl⟩ : syracuseStep 1820211 = 2730317) B2730317
theorem B2729537 : Blo 1819611 2729537 := bstep (se 2 (by rfl) ⟨1023576, by rfl⟩ : syracuseStep 2729537 = 2047153) B2047153
theorem B1820227 : Blo 1819611 1820227 := bstep (se 1 (by rfl) ⟨1365170, by rfl⟩ : syracuseStep 1820227 = 2730341) B2730341
theorem B2729555 : Blo 1819611 2729555 := bstep (se 1 (by rfl) ⟨2047166, by rfl⟩ : syracuseStep 2729555 = 4094333) B4094333
theorem B1820243 : Blo 1819611 1820243 := bstep (se 1 (by rfl) ⟨1365182, by rfl⟩ : syracuseStep 1820243 = 2730365) B2730365
theorem B3073619 : Blo 1819611 3073619 := bstep (se 1 (by rfl) ⟨2305214, by rfl⟩ : syracuseStep 3073619 = 4610429) B4610429
theorem B1820259 : Blo 1819611 1820259 := bstep (se 1 (by rfl) ⟨1365194, by rfl⟩ : syracuseStep 1820259 = 2730389) B2730389
theorem B2729585 : Blo 1819611 2729585 := bstep (se 2 (by rfl) ⟨1023594, by rfl⟩ : syracuseStep 2729585 = 2047189) B2047189
theorem B50529905 : Blo 1819611 50529905 := bstep (se 2 (by rfl) ⟨18948714, by rfl⟩ : syracuseStep 50529905 = 37897429) B37897429
theorem B1820275 : Blo 1819611 1820275 := bstep (se 1 (by rfl) ⟨1365206, by rfl⟩ : syracuseStep 1820275 = 2730413) B2730413
theorem B2729603 : Blo 1819611 2729603 := bstep (se 1 (by rfl) ⟨2047202, by rfl⟩ : syracuseStep 2729603 = 4094405) B4094405
theorem B1820291 : Blo 1819611 1820291 := bstep (se 1 (by rfl) ⟨1365218, by rfl⟩ : syracuseStep 1820291 = 2730437) B2730437
theorem B2025091 : Blo 1819611 2025091 := bstep (se 1 (by rfl) ⟨1518818, by rfl⟩ : syracuseStep 2025091 = 3037637) B3037637
theorem B11667077 : Blo 1819611 11667077 := bstep (se 4 (by rfl) ⟨1093788, by rfl⟩ : syracuseStep 11667077 = 2187577) B2187577
theorem B10364557 : Blo 1819611 10364557 := bstep (se 3 (by rfl) ⟨1943354, by rfl⟩ : syracuseStep 10364557 = 3886709) B3886709
theorem B4097681 : Blo 1819611 4097681 := bstep (se 2 (by rfl) ⟨1536630, by rfl⟩ : syracuseStep 4097681 = 3073261) B3073261
theorem B2303635 : Blo 1819611 2303635 := bstep (se 1 (by rfl) ⟨1727726, by rfl⟩ : syracuseStep 2303635 = 3455453) B3455453
theorem B1820307 : Blo 1819611 1820307 := bstep (se 1 (by rfl) ⟨1365230, by rfl⟩ : syracuseStep 1820307 = 2730461) B2730461
theorem B2729633 : Blo 1819611 2729633 := bstep (se 2 (by rfl) ⟨1023612, by rfl⟩ : syracuseStep 2729633 = 2047225) B2047225
theorem B1820323 : Blo 1819611 1820323 := bstep (se 1 (by rfl) ⟨1365242, by rfl⟩ : syracuseStep 1820323 = 2730485) B2730485
theorem B4097699 : Blo 1819611 4097699 := bstep (se 1 (by rfl) ⟨3073274, by rfl⟩ : syracuseStep 4097699 = 6146549) B6146549
theorem B2729651 : Blo 1819611 2729651 := bstep (se 1 (by rfl) ⟨2047238, by rfl⟩ : syracuseStep 2729651 = 4094477) B4094477
theorem B1820339 : Blo 1819611 1820339 := bstep (se 1 (by rfl) ⟨1365254, by rfl⟩ : syracuseStep 1820339 = 2730509) B2730509
theorem B1820355 : Blo 1819611 1820355 := bstep (se 1 (by rfl) ⟨1365266, by rfl⟩ : syracuseStep 1820355 = 2730533) B2730533
theorem B10372805 : Blo 1819611 10372805 := bstep (se 4 (by rfl) ⟨972450, by rfl⟩ : syracuseStep 10372805 = 1944901) B1944901
theorem B2729681 : Blo 1819611 2729681 := bstep (se 2 (by rfl) ⟨1023630, by rfl⟩ : syracuseStep 2729681 = 2047261) B2047261
theorem B1820371 : Blo 1819611 1820371 := bstep (se 1 (by rfl) ⟨1365278, by rfl⟩ : syracuseStep 1820371 = 2730557) B2730557
theorem B3073747 : Blo 1819611 3073747 := bstep (se 1 (by rfl) ⟨2305310, by rfl⟩ : syracuseStep 3073747 = 4610621) B4610621
theorem B2729699 : Blo 1819611 2729699 := bstep (se 1 (by rfl) ⟨2047274, by rfl⟩ : syracuseStep 2729699 = 4094549) B4094549
theorem B1820387 : Blo 1819611 1820387 := bstep (se 1 (by rfl) ⟨1365290, by rfl⟩ : syracuseStep 1820387 = 2730581) B2730581
theorem B2303731 : Blo 1819611 2303731 := bstep (se 1 (by rfl) ⟨1727798, by rfl⟩ : syracuseStep 2303731 = 3455597) B3455597
theorem B1820403 : Blo 1819611 1820403 := bstep (se 1 (by rfl) ⟨1365302, by rfl⟩ : syracuseStep 1820403 = 2730605) B2730605
theorem B2729729 : Blo 1819611 2729729 := bstep (se 2 (by rfl) ⟨1023648, by rfl⟩ : syracuseStep 2729729 = 2047297) B2047297
theorem B1820419 : Blo 1819611 1820419 := bstep (se 1 (by rfl) ⟨1365314, by rfl⟩ : syracuseStep 1820419 = 2730629) B2730629
theorem B6227729 : Blo 1819611 6227729 := bstep (se 2 (by rfl) ⟨2335398, by rfl⟩ : syracuseStep 6227729 = 4670797) B4670797
theorem B2729747 : Blo 1819611 2729747 := bstep (se 1 (by rfl) ⟨2047310, by rfl⟩ : syracuseStep 2729747 = 4094621) B4094621
theorem B1820435 : Blo 1819611 1820435 := bstep (se 1 (by rfl) ⟨1365326, by rfl⟩ : syracuseStep 1820435 = 2730653) B2730653
theorem B1820451 : Blo 1819611 1820451 := bstep (se 1 (by rfl) ⟨1365338, by rfl⟩ : syracuseStep 1820451 = 2730677) B2730677
theorem B2729777 : Blo 1819611 2729777 := bstep (se 2 (by rfl) ⟨1023666, by rfl⟩ : syracuseStep 2729777 = 2047333) B2047333
theorem B1820467 : Blo 1819611 1820467 := bstep (se 1 (by rfl) ⟨1365350, by rfl⟩ : syracuseStep 1820467 = 2730701) B2730701
theorem B2729795 : Blo 1819611 2729795 := bstep (se 1 (by rfl) ⟨2047346, by rfl⟩ : syracuseStep 2729795 = 4094693) B4094693
theorem B1820483 : Blo 1819611 1820483 := bstep (se 1 (by rfl) ⟨1365362, by rfl⟩ : syracuseStep 1820483 = 2730725) B2730725
theorem B1820499 : Blo 1819611 1820499 := bstep (se 1 (by rfl) ⟨1365374, by rfl⟩ : syracuseStep 1820499 = 2730749) B2730749
theorem B2729825 : Blo 1819611 2729825 := bstep (se 2 (by rfl) ⟨1023684, by rfl⟩ : syracuseStep 2729825 = 2047369) B2047369
theorem B1820515 : Blo 1819611 1820515 := bstep (se 1 (by rfl) ⟨1365386, by rfl⟩ : syracuseStep 1820515 = 2730773) B2730773
theorem B3073889 : Blo 1819611 3073889 := bstep (se 2 (by rfl) ⟨1152708, by rfl⟩ : syracuseStep 3073889 = 2305417) B2305417
theorem B6145901 : Blo 1819611 6145901 := bstep (se 3 (by rfl) ⟨1152356, by rfl⟩ : syracuseStep 6145901 = 2304713) B2304713
theorem B2729843 : Blo 1819611 2729843 := bstep (se 1 (by rfl) ⟨2047382, by rfl⟩ : syracuseStep 2729843 = 4094765) B4094765
theorem B1820531 : Blo 1819611 1820531 := bstep (se 1 (by rfl) ⟨1365398, by rfl⟩ : syracuseStep 1820531 = 2730797) B2730797
theorem B1820547 : Blo 1819611 1820547 := bstep (se 1 (by rfl) ⟨1365410, by rfl⟩ : syracuseStep 1820547 = 2730821) B2730821
theorem B2729873 : Blo 1819611 2729873 := bstep (se 2 (by rfl) ⟨1023702, by rfl⟩ : syracuseStep 2729873 = 2047405) B2047405
theorem B5613457 : Blo 1819611 5613457 := bstep (se 2 (by rfl) ⟨2105046, by rfl⟩ : syracuseStep 5613457 = 4210093) B4210093
theorem B1820563 : Blo 1819611 1820563 := bstep (se 1 (by rfl) ⟨1365422, by rfl⟩ : syracuseStep 1820563 = 2730845) B2730845
theorem B2729891 : Blo 1819611 2729891 := bstep (se 1 (by rfl) ⟨2047418, by rfl⟩ : syracuseStep 2729891 = 4094837) B4094837
theorem B1820579 : Blo 1819611 1820579 := bstep (se 1 (by rfl) ⟨1365434, by rfl⟩ : syracuseStep 1820579 = 2730869) B2730869
theorem B6145955 : Blo 1819611 6145955 := bstep (se 1 (by rfl) ⟨4609466, by rfl⟩ : syracuseStep 6145955 = 9218933) B9218933
theorem B4097969 : Blo 1819611 4097969 := bstep (se 2 (by rfl) ⟨1536738, by rfl⟩ : syracuseStep 4097969 = 3073477) B3073477
theorem B1820595 : Blo 1819611 1820595 := bstep (se 1 (by rfl) ⟨1365446, by rfl⟩ : syracuseStep 1820595 = 2730893) B2730893
theorem B2729921 : Blo 1819611 2729921 := bstep (se 2 (by rfl) ⟨1023720, by rfl⟩ : syracuseStep 2729921 = 2047441) B2047441
theorem B1820611 : Blo 1819611 1820611 := bstep (se 1 (by rfl) ⟨1365458, by rfl⟩ : syracuseStep 1820611 = 2730917) B2730917
theorem B4097987 : Blo 1819611 4097987 := bstep (se 1 (by rfl) ⟨3073490, by rfl⟩ : syracuseStep 4097987 = 6146981) B6146981
theorem B2729939 : Blo 1819611 2729939 := bstep (se 1 (by rfl) ⟨2047454, by rfl⟩ : syracuseStep 2729939 = 4094909) B4094909
theorem B1820627 : Blo 1819611 1820627 := bstep (se 1 (by rfl) ⟨1365470, by rfl⟩ : syracuseStep 1820627 = 2730941) B2730941
theorem B4605923 : Blo 1819611 4605923 := bstep (se 1 (by rfl) ⟨3454442, by rfl⟩ : syracuseStep 4605923 = 6908885) B6908885
theorem B1820643 : Blo 1819611 1820643 := bstep (se 1 (by rfl) ⟨1365482, by rfl⟩ : syracuseStep 1820643 = 2730965) B2730965
theorem B2729969 : Blo 1819611 2729969 := bstep (se 2 (by rfl) ⟨1023738, by rfl⟩ : syracuseStep 2729969 = 2047477) B2047477
theorem B1820659 : Blo 1819611 1820659 := bstep (se 1 (by rfl) ⟨1365494, by rfl⟩ : syracuseStep 1820659 = 2730989) B2730989
theorem B2729987 : Blo 1819611 2729987 := bstep (se 1 (by rfl) ⟨2047490, by rfl⟩ : syracuseStep 2729987 = 4094981) B4094981
theorem B1820675 : Blo 1819611 1820675 := bstep (se 1 (by rfl) ⟨1365506, by rfl⟩ : syracuseStep 1820675 = 2731013) B2731013
theorem B1820691 : Blo 1819611 1820691 := bstep (se 1 (by rfl) ⟨1365518, by rfl⟩ : syracuseStep 1820691 = 2731037) B2731037
theorem B2730017 : Blo 1819611 2730017 := bstep (se 2 (by rfl) ⟨1023756, by rfl⟩ : syracuseStep 2730017 = 2047513) B2047513
theorem B1820707 : Blo 1819611 1820707 := bstep (se 1 (by rfl) ⟨1365530, by rfl⟩ : syracuseStep 1820707 = 2731061) B2731061
theorem B5253169 : Blo 1819611 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B2730035 : Blo 1819611 2730035 := bstep (se 1 (by rfl) ⟨2047526, by rfl⟩ : syracuseStep 2730035 = 4095053) B4095053
theorem B1820723 : Blo 1819611 1820723 := bstep (se 1 (by rfl) ⟨1365542, by rfl⟩ : syracuseStep 1820723 = 2731085) B2731085
theorem B1820739 : Blo 1819611 1820739 := bstep (se 1 (by rfl) ⟨1365554, by rfl⟩ : syracuseStep 1820739 = 2731109) B2731109
theorem B2730065 : Blo 1819611 2730065 := bstep (se 2 (by rfl) ⟨1023774, by rfl⟩ : syracuseStep 2730065 = 2047549) B2047549
theorem B1820755 : Blo 1819611 1820755 := bstep (se 1 (by rfl) ⟨1365566, by rfl⟩ : syracuseStep 1820755 = 2731133) B2731133
theorem B2730083 : Blo 1819611 2730083 := bstep (se 1 (by rfl) ⟨2047562, by rfl⟩ : syracuseStep 2730083 = 4095125) B4095125
theorem B1845347 : Blo 1819611 1845347 := bstep (se 1 (by rfl) ⟨1384010, by rfl⟩ : syracuseStep 1845347 = 2768021) B2768021
theorem B1820771 : Blo 1819611 1820771 := bstep (se 1 (by rfl) ⟨1365578, by rfl⟩ : syracuseStep 1820771 = 2731157) B2731157
theorem B123029617 : Blo 1819611 123029617 := bstep (se 2 (by rfl) ⟨46136106, by rfl⟩ : syracuseStep 123029617 = 92272213) B92272213
theorem B1820787 : Blo 1819611 1820787 := bstep (se 1 (by rfl) ⟨1365590, by rfl⟩ : syracuseStep 1820787 = 2731181) B2731181
theorem B2730113 : Blo 1819611 2730113 := bstep (se 2 (by rfl) ⟨1023792, by rfl⟩ : syracuseStep 2730113 = 2047585) B2047585
theorem B1820803 : Blo 1819611 1820803 := bstep (se 1 (by rfl) ⟨1365602, by rfl⟩ : syracuseStep 1820803 = 2731205) B2731205
theorem B2730131 : Blo 1819611 2730131 := bstep (se 1 (by rfl) ⟨2047598, by rfl⟩ : syracuseStep 2730131 = 4095197) B4095197
theorem B1820819 : Blo 1819611 1820819 := bstep (se 1 (by rfl) ⟨1365614, by rfl⟩ : syracuseStep 1820819 = 2731229) B2731229
theorem B1820835 : Blo 1819611 1820835 := bstep (se 1 (by rfl) ⟨1365626, by rfl⟩ : syracuseStep 1820835 = 2731253) B2731253
theorem B2730161 : Blo 1819611 2730161 := bstep (se 2 (by rfl) ⟨1023810, by rfl⟩ : syracuseStep 2730161 = 2047621) B2047621
theorem B6146225 : Blo 1819611 6146225 := bstep (se 2 (by rfl) ⟨2304834, by rfl⟩ : syracuseStep 6146225 = 4609669) B4609669
theorem B1820851 : Blo 1819611 1820851 := bstep (se 1 (by rfl) ⟨1365638, by rfl⟩ : syracuseStep 1820851 = 2731277) B2731277
theorem B2730179 : Blo 1819611 2730179 := bstep (se 1 (by rfl) ⟨2047634, by rfl⟩ : syracuseStep 2730179 = 4095269) B4095269
theorem B1820867 : Blo 1819611 1820867 := bstep (se 1 (by rfl) ⟨1365650, by rfl⟩ : syracuseStep 1820867 = 2731301) B2731301
theorem B4098257 : Blo 1819611 4098257 := bstep (se 2 (by rfl) ⟨1536846, by rfl⟩ : syracuseStep 4098257 = 3073693) B3073693
theorem B1820883 : Blo 1819611 1820883 := bstep (se 1 (by rfl) ⟨1365662, by rfl⟩ : syracuseStep 1820883 = 2731325) B2731325
theorem B2730209 : Blo 1819611 2730209 := bstep (se 2 (by rfl) ⟨1023828, by rfl⟩ : syracuseStep 2730209 = 2047657) B2047657
theorem B2304227 : Blo 1819611 2304227 := bstep (se 1 (by rfl) ⟨1728170, by rfl⟩ : syracuseStep 2304227 = 3456341) B3456341
theorem B1820899 : Blo 1819611 1820899 := bstep (se 1 (by rfl) ⟨1365674, by rfl⟩ : syracuseStep 1820899 = 2731349) B2731349
theorem B4098275 : Blo 1819611 4098275 := bstep (se 1 (by rfl) ⟨3073706, by rfl⟩ : syracuseStep 4098275 = 6147413) B6147413
theorem B1870067 : Blo 1819611 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B2730227 : Blo 1819611 2730227 := bstep (se 1 (by rfl) ⟨2047670, by rfl⟩ : syracuseStep 2730227 = 4095341) B4095341
theorem B1943795 : Blo 1819611 1943795 := bstep (se 1 (by rfl) ⟨1457846, by rfl⟩ : syracuseStep 1943795 = 2915693) B2915693
theorem B1820915 : Blo 1819611 1820915 := bstep (se 1 (by rfl) ⟨1365686, by rfl⟩ : syracuseStep 1820915 = 2731373) B2731373
theorem B1820931 : Blo 1819611 1820931 := bstep (se 1 (by rfl) ⟨1365698, by rfl⟩ : syracuseStep 1820931 = 2731397) B2731397
theorem B2730257 : Blo 1819611 2730257 := bstep (se 2 (by rfl) ⟨1023846, by rfl⟩ : syracuseStep 2730257 = 2047693) B2047693
theorem B1820947 : Blo 1819611 1820947 := bstep (se 1 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 1820947 = 2731421) B2731421
theorem B2730275 : Blo 1819611 2730275 := bstep (se 1 (by rfl) ⟨2047706, by rfl⟩ : syracuseStep 2730275 = 4095413) B4095413
theorem B1820963 : Blo 1819611 1820963 := bstep (se 1 (by rfl) ⟨1365722, by rfl⟩ : syracuseStep 1820963 = 2731445) B2731445
theorem B6916387 : Blo 1819611 6916387 := bstep (se 1 (by rfl) ⟨5187290, by rfl⟩ : syracuseStep 6916387 = 10374581) B10374581
theorem B1820979 : Blo 1819611 1820979 := bstep (se 1 (by rfl) ⟨1365734, by rfl⟩ : syracuseStep 1820979 = 2731469) B2731469
theorem B2730305 : Blo 1819611 2730305 := bstep (se 2 (by rfl) ⟨1023864, by rfl⟩ : syracuseStep 2730305 = 2047729) B2047729
theorem B1820995 : Blo 1819611 1820995 := bstep (se 1 (by rfl) ⟨1365746, by rfl⟩ : syracuseStep 1820995 = 2731493) B2731493
theorem B2730323 : Blo 1819611 2730323 := bstep (se 1 (by rfl) ⟨2047742, by rfl⟩ : syracuseStep 2730323 = 4095485) B4095485
theorem B1821011 : Blo 1819611 1821011 := bstep (se 1 (by rfl) ⟨1365758, by rfl⟩ : syracuseStep 1821011 = 2731517) B2731517
theorem B1821027 : Blo 1819611 1821027 := bstep (se 1 (by rfl) ⟨1365770, by rfl⟩ : syracuseStep 1821027 = 2731541) B2731541
theorem B2730353 : Blo 1819611 2730353 := bstep (se 2 (by rfl) ⟨1023882, by rfl⟩ : syracuseStep 2730353 = 2047765) B2047765
theorem B1821043 : Blo 1819611 1821043 := bstep (se 1 (by rfl) ⟨1365782, by rfl⟩ : syracuseStep 1821043 = 2731565) B2731565
theorem B2730371 : Blo 1819611 2730371 := bstep (se 1 (by rfl) ⟨2047778, by rfl⟩ : syracuseStep 2730371 = 4095557) B4095557
theorem B1821059 : Blo 1819611 1821059 := bstep (se 1 (by rfl) ⟨1365794, by rfl⟩ : syracuseStep 1821059 = 2731589) B2731589
theorem B1821075 : Blo 1819611 1821075 := bstep (se 1 (by rfl) ⟨1365806, by rfl⟩ : syracuseStep 1821075 = 2731613) B2731613
theorem B2730401 : Blo 1819611 2730401 := bstep (se 2 (by rfl) ⟨1023900, by rfl⟩ : syracuseStep 2730401 = 2047801) B2047801
theorem B1821091 : Blo 1819611 1821091 := bstep (se 1 (by rfl) ⟨1365818, by rfl⟩ : syracuseStep 1821091 = 2731637) B2731637
theorem B2730419 : Blo 1819611 2730419 := bstep (se 1 (by rfl) ⟨2047814, by rfl⟩ : syracuseStep 2730419 = 4095629) B4095629
theorem B1821107 : Blo 1819611 1821107 := bstep (se 1 (by rfl) ⟨1365830, by rfl⟩ : syracuseStep 1821107 = 2731661) B2731661
theorem B1821123 : Blo 1819611 1821123 := bstep (se 1 (by rfl) ⟨1365842, by rfl⟩ : syracuseStep 1821123 = 2731685) B2731685
theorem B11659717 : Blo 1819611 11659717 := bstep (se 4 (by rfl) ⟨1093098, by rfl⟩ : syracuseStep 11659717 = 2186197) B2186197
theorem B2591185 : Blo 1819611 2591185 := bstep (se 2 (by rfl) ⟨971694, by rfl⟩ : syracuseStep 2591185 = 1943389) B1943389
theorem B2730449 : Blo 1819611 2730449 := bstep (se 2 (by rfl) ⟨1023918, by rfl⟩ : syracuseStep 2730449 = 2047837) B2047837
theorem B1821139 : Blo 1819611 1821139 := bstep (se 1 (by rfl) ⟨1365854, by rfl⟩ : syracuseStep 1821139 = 2731709) B2731709
theorem B2730467 : Blo 1819611 2730467 := bstep (se 1 (by rfl) ⟨2047850, by rfl⟩ : syracuseStep 2730467 = 4095701) B4095701
theorem B1821155 : Blo 1819611 1821155 := bstep (se 1 (by rfl) ⟨1365866, by rfl⟩ : syracuseStep 1821155 = 2731733) B2731733
theorem B4098545 : Blo 1819611 4098545 := bstep (se 2 (by rfl) ⟨1536954, by rfl⟩ : syracuseStep 4098545 = 3073909) B3073909
theorem B1821171 : Blo 1819611 1821171 := bstep (se 1 (by rfl) ⟨1365878, by rfl⟩ : syracuseStep 1821171 = 2731757) B2731757
theorem B2730497 : Blo 1819611 2730497 := bstep (se 2 (by rfl) ⟨1023936, by rfl⟩ : syracuseStep 2730497 = 2047873) B2047873
theorem B1821187 : Blo 1819611 1821187 := bstep (se 1 (by rfl) ⟨1365890, by rfl⟩ : syracuseStep 1821187 = 2731781) B2731781
theorem B4098563 : Blo 1819611 4098563 := bstep (se 1 (by rfl) ⟨3073922, by rfl⟩ : syracuseStep 4098563 = 6147845) B6147845
theorem B16198157 : Blo 1819611 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B2730515 : Blo 1819611 2730515 := bstep (se 1 (by rfl) ⟨2047886, by rfl⟩ : syracuseStep 2730515 = 4095773) B4095773
theorem B1821203 : Blo 1819611 1821203 := bstep (se 1 (by rfl) ⟨1365902, by rfl⟩ : syracuseStep 1821203 = 2731805) B2731805
theorem B1821219 : Blo 1819611 1821219 := bstep (se 1 (by rfl) ⟨1365914, by rfl⟩ : syracuseStep 1821219 = 2731829) B2731829
theorem B2730545 : Blo 1819611 2730545 := bstep (se 2 (by rfl) ⟨1023954, by rfl⟩ : syracuseStep 2730545 = 2047909) B2047909
theorem B9218609 : Blo 1819611 9218609 := bstep (se 2 (by rfl) ⟨3456978, by rfl⟩ : syracuseStep 9218609 = 6913957) B6913957
theorem B1821235 : Blo 1819611 1821235 := bstep (se 1 (by rfl) ⟨1365926, by rfl⟩ : syracuseStep 1821235 = 2731853) B2731853
theorem B2591299 : Blo 1819611 2591299 := bstep (se 1 (by rfl) ⟨1943474, by rfl⟩ : syracuseStep 2591299 = 3886949) B3886949
theorem B2730563 : Blo 1819611 2730563 := bstep (se 1 (by rfl) ⟨2047922, by rfl⟩ : syracuseStep 2730563 = 4095845) B4095845
theorem B1821251 : Blo 1819611 1821251 := bstep (se 1 (by rfl) ⟨1365938, by rfl⟩ : syracuseStep 1821251 = 2731877) B2731877
theorem B1821267 : Blo 1819611 1821267 := bstep (se 1 (by rfl) ⟨1365950, by rfl⟩ : syracuseStep 1821267 = 2731901) B2731901
theorem B2730593 : Blo 1819611 2730593 := bstep (se 2 (by rfl) ⟨1023972, by rfl⟩ : syracuseStep 2730593 = 2047945) B2047945
theorem B1821283 : Blo 1819611 1821283 := bstep (se 1 (by rfl) ⟨1365962, by rfl⟩ : syracuseStep 1821283 = 2731925) B2731925
theorem B2730611 : Blo 1819611 2730611 := bstep (se 1 (by rfl) ⟨2047958, by rfl⟩ : syracuseStep 2730611 = 4095917) B4095917
theorem B1821299 : Blo 1819611 1821299 := bstep (se 1 (by rfl) ⟨1365974, by rfl⟩ : syracuseStep 1821299 = 2731949) B2731949
theorem B1821315 : Blo 1819611 1821315 := bstep (se 1 (by rfl) ⟨1365986, by rfl⟩ : syracuseStep 1821315 = 2731973) B2731973
theorem B5835395 : Blo 1819611 5835395 := bstep (se 1 (by rfl) ⟨4376546, by rfl⟩ : syracuseStep 5835395 = 8753093) B8753093
theorem B2460305 : Blo 1819611 2460305 := bstep (se 2 (by rfl) ⟨922614, by rfl⟩ : syracuseStep 2460305 = 1845229) B1845229
theorem B2730641 : Blo 1819611 2730641 := bstep (se 2 (by rfl) ⟨1023990, by rfl⟩ : syracuseStep 2730641 = 2047981) B2047981
theorem B1821331 : Blo 1819611 1821331 := bstep (se 1 (by rfl) ⟨1365998, by rfl⟩ : syracuseStep 1821331 = 2731997) B2731997
theorem B2730659 : Blo 1819611 2730659 := bstep (se 1 (by rfl) ⟨2047994, by rfl⟩ : syracuseStep 2730659 = 4095989) B4095989
theorem B1821347 : Blo 1819611 1821347 := bstep (se 1 (by rfl) ⟨1366010, by rfl⟩ : syracuseStep 1821347 = 2732021) B2732021
theorem B1821363 : Blo 1819611 1821363 := bstep (se 1 (by rfl) ⟨1366022, by rfl⟩ : syracuseStep 1821363 = 2732045) B2732045
theorem B2730689 : Blo 1819611 2730689 := bstep (se 2 (by rfl) ⟨1024008, by rfl⟩ : syracuseStep 2730689 = 2048017) B2048017
theorem B1821379 : Blo 1819611 1821379 := bstep (se 1 (by rfl) ⟨1366034, by rfl⟩ : syracuseStep 1821379 = 2732069) B2732069
theorem B6146765 : Blo 1819611 6146765 := bstep (se 3 (by rfl) ⟨1152518, by rfl⟩ : syracuseStep 6146765 = 2305037) B2305037
theorem B2730707 : Blo 1819611 2730707 := bstep (se 1 (by rfl) ⟨2048030, by rfl⟩ : syracuseStep 2730707 = 4096061) B4096061
theorem B1821395 : Blo 1819611 1821395 := bstep (se 1 (by rfl) ⟨1366046, by rfl⟩ : syracuseStep 1821395 = 2732093) B2732093
theorem B1821411 : Blo 1819611 1821411 := bstep (se 1 (by rfl) ⟨1366058, by rfl⟩ : syracuseStep 1821411 = 2732117) B2732117
theorem B2730737 : Blo 1819611 2730737 := bstep (se 2 (by rfl) ⟨1024026, by rfl⟩ : syracuseStep 2730737 = 2048053) B2048053
theorem B1821427 : Blo 1819611 1821427 := bstep (se 1 (by rfl) ⟨1366070, by rfl⟩ : syracuseStep 1821427 = 2732141) B2732141
theorem B2730755 : Blo 1819611 2730755 := bstep (se 1 (by rfl) ⟨2048066, by rfl⟩ : syracuseStep 2730755 = 4096133) B4096133
theorem B6146819 : Blo 1819611 6146819 := bstep (se 1 (by rfl) ⟨4610114, by rfl⟩ : syracuseStep 6146819 = 9220229) B9220229
theorem B1821443 : Blo 1819611 1821443 := bstep (se 1 (by rfl) ⟨1366082, by rfl⟩ : syracuseStep 1821443 = 2732165) B2732165
theorem B1821459 : Blo 1819611 1821459 := bstep (se 1 (by rfl) ⟨1366094, by rfl⟩ : syracuseStep 1821459 = 2732189) B2732189
theorem B2730785 : Blo 1819611 2730785 := bstep (se 2 (by rfl) ⟨1024044, by rfl⟩ : syracuseStep 2730785 = 2048089) B2048089
theorem B1821475 : Blo 1819611 1821475 := bstep (se 1 (by rfl) ⟨1366106, by rfl⟩ : syracuseStep 1821475 = 2732213) B2732213
theorem B2730803 : Blo 1819611 2730803 := bstep (se 1 (by rfl) ⟨2048102, by rfl⟩ : syracuseStep 2730803 = 4096205) B4096205
theorem B1821491 : Blo 1819611 1821491 := bstep (se 1 (by rfl) ⟨1366118, by rfl⟩ : syracuseStep 1821491 = 2732237) B2732237
theorem B1821507 : Blo 1819611 1821507 := bstep (se 1 (by rfl) ⟨1366130, by rfl⟩ : syracuseStep 1821507 = 2732261) B2732261
theorem B2730833 : Blo 1819611 2730833 := bstep (se 2 (by rfl) ⟨1024062, by rfl⟩ : syracuseStep 2730833 = 2048125) B2048125
theorem B1821523 : Blo 1819611 1821523 := bstep (se 1 (by rfl) ⟨1366142, by rfl⟩ : syracuseStep 1821523 = 2732285) B2732285
theorem B2730851 : Blo 1819611 2730851 := bstep (se 1 (by rfl) ⟨2048138, by rfl⟩ : syracuseStep 2730851 = 4096277) B4096277
theorem B1870691 : Blo 1819611 1870691 := bstep (se 1 (by rfl) ⟨1403018, by rfl⟩ : syracuseStep 1870691 = 2806037) B2806037
theorem B1821539 : Blo 1819611 1821539 := bstep (se 1 (by rfl) ⟨1366154, by rfl⟩ : syracuseStep 1821539 = 2732309) B2732309
theorem B1821555 : Blo 1819611 1821555 := bstep (se 1 (by rfl) ⟨1366166, by rfl⟩ : syracuseStep 1821555 = 2732333) B2732333
theorem B2730881 : Blo 1819611 2730881 := bstep (se 2 (by rfl) ⟨1024080, by rfl⟩ : syracuseStep 2730881 = 2048161) B2048161
theorem B1821571 : Blo 1819611 1821571 := bstep (se 1 (by rfl) ⟨1366178, by rfl⟩ : syracuseStep 1821571 = 2732357) B2732357
theorem B4606865 : Blo 1819611 4606865 := bstep (se 2 (by rfl) ⟨1727574, by rfl⟩ : syracuseStep 4606865 = 3455149) B3455149
theorem B2730899 : Blo 1819611 2730899 := bstep (se 1 (by rfl) ⟨2048174, by rfl⟩ : syracuseStep 2730899 = 4096349) B4096349
theorem B1821587 : Blo 1819611 1821587 := bstep (se 1 (by rfl) ⟨1366190, by rfl⟩ : syracuseStep 1821587 = 2732381) B2732381
theorem B2304931 : Blo 1819611 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B1821603 : Blo 1819611 1821603 := bstep (se 1 (by rfl) ⟨1366202, by rfl⟩ : syracuseStep 1821603 = 2732405) B2732405
theorem B2730929 : Blo 1819611 2730929 := bstep (se 2 (by rfl) ⟨1024098, by rfl⟩ : syracuseStep 2730929 = 2048197) B2048197
theorem B4606915 : Blo 1819611 4606915 := bstep (se 1 (by rfl) ⟨3455186, by rfl⟩ : syracuseStep 4606915 = 6910373) B6910373
theorem B2730947 : Blo 1819611 2730947 := bstep (se 1 (by rfl) ⟨2048210, by rfl⟩ : syracuseStep 2730947 = 4096421) B4096421
theorem B2730977 : Blo 1819611 2730977 := bstep (se 2 (by rfl) ⟨1024116, by rfl⟩ : syracuseStep 2730977 = 2048233) B2048233
theorem B1846243 : Blo 1819611 1846243 := bstep (se 1 (by rfl) ⟨1384682, by rfl⟩ : syracuseStep 1846243 = 2769365) B2769365
theorem B2730995 : Blo 1819611 2730995 := bstep (se 1 (by rfl) ⟨2048246, by rfl⟩ : syracuseStep 2730995 = 4096493) B4096493
theorem B5909507 : Blo 1819611 5909507 := bstep (se 1 (by rfl) ⟨4432130, by rfl⟩ : syracuseStep 5909507 = 8864261) B8864261
theorem B2305027 : Blo 1819611 2305027 := bstep (se 1 (by rfl) ⟨1728770, by rfl⟩ : syracuseStep 2305027 = 3457541) B3457541
theorem B23342093 : Blo 1819611 23342093 := bstep (se 3 (by rfl) ⟨4376642, by rfl⟩ : syracuseStep 23342093 = 8753285) B8753285
theorem B2731025 : Blo 1819611 2731025 := bstep (se 2 (by rfl) ⟨1024134, by rfl⟩ : syracuseStep 2731025 = 2048269) B2048269
theorem B6147089 : Blo 1819611 6147089 := bstep (se 2 (by rfl) ⟨2305158, by rfl⟩ : syracuseStep 6147089 = 4610317) B4610317
theorem B2731043 : Blo 1819611 2731043 := bstep (se 1 (by rfl) ⟨2048282, by rfl⟩ : syracuseStep 2731043 = 4096565) B4096565
theorem B2731073 : Blo 1819611 2731073 := bstep (se 2 (by rfl) ⟨1024152, by rfl⟩ : syracuseStep 2731073 = 2048305) B2048305
theorem B4607057 : Blo 1819611 4607057 := bstep (se 2 (by rfl) ⟨1727646, by rfl⟩ : syracuseStep 4607057 = 3455293) B3455293
theorem B2731091 : Blo 1819611 2731091 := bstep (se 1 (by rfl) ⟨2048318, by rfl⟩ : syracuseStep 2731091 = 4096637) B4096637
theorem B23645297 : Blo 1819611 23645297 := bstep (se 2 (by rfl) ⟨8866986, by rfl⟩ : syracuseStep 23645297 = 17733973) B17733973
theorem B2731121 : Blo 1819611 2731121 := bstep (se 2 (by rfl) ⟨1024170, by rfl⟩ : syracuseStep 2731121 = 2048341) B2048341
theorem B2731139 : Blo 1819611 2731139 := bstep (se 1 (by rfl) ⟨2048354, by rfl⟩ : syracuseStep 2731139 = 4096709) B4096709
theorem B3845251 : Blo 1819611 3845251 := bstep (se 1 (by rfl) ⟨2883938, by rfl⟩ : syracuseStep 3845251 = 5767877) B5767877
theorem B2731169 : Blo 1819611 2731169 := bstep (se 2 (by rfl) ⟨1024188, by rfl⟩ : syracuseStep 2731169 = 2048377) B2048377
theorem B1944739 : Blo 1819611 1944739 := bstep (se 1 (by rfl) ⟨1458554, by rfl⟩ : syracuseStep 1944739 = 2917109) B2917109
theorem B2731187 : Blo 1819611 2731187 := bstep (se 1 (by rfl) ⟨2048390, by rfl⟩ : syracuseStep 2731187 = 4096781) B4096781
theorem B2731217 : Blo 1819611 2731217 := bstep (se 2 (by rfl) ⟨1024206, by rfl⟩ : syracuseStep 2731217 = 2048413) B2048413
theorem B39349475 : Blo 1819611 39349475 := bstep (se 1 (by rfl) ⟨29512106, by rfl⟩ : syracuseStep 39349475 = 59024213) B59024213
theorem B2731235 : Blo 1819611 2731235 := bstep (se 1 (by rfl) ⟨2048426, by rfl⟩ : syracuseStep 2731235 = 4096853) B4096853
theorem B2731265 : Blo 1819611 2731265 := bstep (se 2 (by rfl) ⟨1024224, by rfl⟩ : syracuseStep 2731265 = 2048449) B2048449
theorem B2731283 : Blo 1819611 2731283 := bstep (se 1 (by rfl) ⟨2048462, by rfl⟩ : syracuseStep 2731283 = 4096925) B4096925
theorem B2731313 : Blo 1819611 2731313 := bstep (se 2 (by rfl) ⟨1024242, by rfl⟩ : syracuseStep 2731313 = 2048485) B2048485
theorem B2731331 : Blo 1819611 2731331 := bstep (se 1 (by rfl) ⟨2048498, by rfl⟩ : syracuseStep 2731331 = 4096997) B4096997
theorem B2731361 : Blo 1819611 2731361 := bstep (se 2 (by rfl) ⟨1024260, by rfl⟩ : syracuseStep 2731361 = 2048521) B2048521
theorem B2731379 : Blo 1819611 2731379 := bstep (se 1 (by rfl) ⟨2048534, by rfl⟩ : syracuseStep 2731379 = 4097069) B4097069
theorem B2731409 : Blo 1819611 2731409 := bstep (se 2 (by rfl) ⟨1024278, by rfl⟩ : syracuseStep 2731409 = 2048557) B2048557
theorem B3689891 : Blo 1819611 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B2731427 : Blo 1819611 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B2731457 : Blo 1819611 2731457 := bstep (se 2 (by rfl) ⟨1024296, by rfl⟩ : syracuseStep 2731457 = 2048593) B2048593
theorem B2731475 : Blo 1819611 2731475 := bstep (se 1 (by rfl) ⟨2048606, by rfl⟩ : syracuseStep 2731475 = 4097213) B4097213
theorem B2731505 : Blo 1819611 2731505 := bstep (se 2 (by rfl) ⟨1024314, by rfl⟩ : syracuseStep 2731505 = 2048629) B2048629
theorem B4435441 : Blo 1819611 4435441 := bstep (se 2 (by rfl) ⟨1663290, by rfl⟩ : syracuseStep 4435441 = 3326581) B3326581
theorem B2731523 : Blo 1819611 2731523 := bstep (se 1 (by rfl) ⟨2048642, by rfl⟩ : syracuseStep 2731523 = 4097285) B4097285
theorem B2731553 : Blo 1819611 2731553 := bstep (se 2 (by rfl) ⟨1024332, by rfl⟩ : syracuseStep 2731553 = 2048665) B2048665
theorem B6147629 : Blo 1819611 6147629 := bstep (se 3 (by rfl) ⟨1152680, by rfl⟩ : syracuseStep 6147629 = 2305361) B2305361
theorem B2731571 : Blo 1819611 2731571 := bstep (se 1 (by rfl) ⟨2048678, by rfl⟩ : syracuseStep 2731571 = 4097357) B4097357
theorem B10366541 : Blo 1819611 10366541 := bstep (se 3 (by rfl) ⟨1943726, by rfl⟩ : syracuseStep 10366541 = 3887453) B3887453
theorem B2731601 : Blo 1819611 2731601 := bstep (se 2 (by rfl) ⟨1024350, by rfl⟩ : syracuseStep 2731601 = 2048701) B2048701
theorem B2731619 : Blo 1819611 2731619 := bstep (se 1 (by rfl) ⟨2048714, by rfl⟩ : syracuseStep 2731619 = 4097429) B4097429
theorem B6147683 : Blo 1819611 6147683 := bstep (se 1 (by rfl) ⟨4610762, by rfl⟩ : syracuseStep 6147683 = 9221525) B9221525
theorem B2731649 : Blo 1819611 2731649 := bstep (se 2 (by rfl) ⟨1024368, by rfl⟩ : syracuseStep 2731649 = 2048737) B2048737
theorem B2731667 : Blo 1819611 2731667 := bstep (se 1 (by rfl) ⟨2048750, by rfl⟩ : syracuseStep 2731667 = 4097501) B4097501
theorem B2731697 : Blo 1819611 2731697 := bstep (se 2 (by rfl) ⟨1024386, by rfl⟩ : syracuseStep 2731697 = 2048773) B2048773
theorem B2731715 : Blo 1819611 2731715 := bstep (se 1 (by rfl) ⟨2048786, by rfl⟩ : syracuseStep 2731715 = 4097573) B4097573
theorem B2731745 : Blo 1819611 2731745 := bstep (se 2 (by rfl) ⟨1024404, by rfl⟩ : syracuseStep 2731745 = 2048809) B2048809
theorem B17493731 : Blo 1819611 17493731 := bstep (se 1 (by rfl) ⟨13120298, by rfl⟩ : syracuseStep 17493731 = 26240597) B26240597
theorem B2731763 : Blo 1819611 2731763 := bstep (se 1 (by rfl) ⟨2048822, by rfl⟩ : syracuseStep 2731763 = 4097645) B4097645
theorem B2731793 : Blo 1819611 2731793 := bstep (se 2 (by rfl) ⟨1024422, by rfl⟩ : syracuseStep 2731793 = 2048845) B2048845
theorem B2731811 : Blo 1819611 2731811 := bstep (se 1 (by rfl) ⟨2048858, by rfl⟩ : syracuseStep 2731811 = 4097717) B4097717
theorem B2731841 : Blo 1819611 2731841 := bstep (se 2 (by rfl) ⟨1024440, by rfl⟩ : syracuseStep 2731841 = 2048881) B2048881
theorem B2731859 : Blo 1819611 2731859 := bstep (se 1 (by rfl) ⟨2048894, by rfl⟩ : syracuseStep 2731859 = 4097789) B4097789
theorem B3280753 : Blo 1819611 3280753 := bstep (se 2 (by rfl) ⟨1230282, by rfl⟩ : syracuseStep 3280753 = 2460565) B2460565
theorem B22146929 : Blo 1819611 22146929 := bstep (se 2 (by rfl) ⟨8305098, by rfl⟩ : syracuseStep 22146929 = 16610197) B16610197
theorem B2731889 : Blo 1819611 2731889 := bstep (se 2 (by rfl) ⟨1024458, by rfl⟩ : syracuseStep 2731889 = 2048917) B2048917
theorem B2592643 : Blo 1819611 2592643 := bstep (se 1 (by rfl) ⟨1944482, by rfl⟩ : syracuseStep 2592643 = 3888965) B3888965
theorem B2731907 : Blo 1819611 2731907 := bstep (se 1 (by rfl) ⟨2048930, by rfl⟩ : syracuseStep 2731907 = 4097861) B4097861
theorem B2731937 : Blo 1819611 2731937 := bstep (se 2 (by rfl) ⟨1024476, by rfl⟩ : syracuseStep 2731937 = 2048953) B2048953
theorem B2461603 : Blo 1819611 2461603 := bstep (se 1 (by rfl) ⟨1846202, by rfl⟩ : syracuseStep 2461603 = 3692405) B3692405
theorem B2731955 : Blo 1819611 2731955 := bstep (se 1 (by rfl) ⟨2048966, by rfl⟩ : syracuseStep 2731955 = 4097933) B4097933
theorem B2731985 : Blo 1819611 2731985 := bstep (se 2 (by rfl) ⟨1024494, by rfl⟩ : syracuseStep 2731985 = 2048989) B2048989
theorem B9220067 : Blo 1819611 9220067 := bstep (se 1 (by rfl) ⟨6915050, by rfl⟩ : syracuseStep 9220067 = 13830101) B13830101
theorem B2732003 : Blo 1819611 2732003 := bstep (se 1 (by rfl) ⟨2049002, by rfl⟩ : syracuseStep 2732003 = 4098005) B4098005
theorem B2732033 : Blo 1819611 2732033 := bstep (se 2 (by rfl) ⟨1024512, by rfl⟩ : syracuseStep 2732033 = 2049025) B2049025
theorem B6230029 : Blo 1819611 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B2732051 : Blo 1819611 2732051 := bstep (se 1 (by rfl) ⟨2049038, by rfl⟩ : syracuseStep 2732051 = 4098077) B4098077
theorem B7778339 : Blo 1819611 7778339 := bstep (se 1 (by rfl) ⟨5833754, by rfl⟩ : syracuseStep 7778339 = 11667509) B11667509
theorem B4608049 : Blo 1819611 4608049 := bstep (se 2 (by rfl) ⟨1728018, by rfl⟩ : syracuseStep 4608049 = 3456037) B3456037
theorem B2732081 : Blo 1819611 2732081 := bstep (se 2 (by rfl) ⟨1024530, by rfl⟩ : syracuseStep 2732081 = 2049061) B2049061
theorem B2732099 : Blo 1819611 2732099 := bstep (se 1 (by rfl) ⟨2049074, by rfl⟩ : syracuseStep 2732099 = 4098149) B4098149
theorem B2732129 : Blo 1819611 2732129 := bstep (se 2 (by rfl) ⟨1024548, by rfl⟩ : syracuseStep 2732129 = 2049097) B2049097
theorem B2732147 : Blo 1819611 2732147 := bstep (se 1 (by rfl) ⟨2049110, by rfl⟩ : syracuseStep 2732147 = 4098221) B4098221
theorem B2732177 : Blo 1819611 2732177 := bstep (se 2 (by rfl) ⟨1024566, by rfl⟩ : syracuseStep 2732177 = 2049133) B2049133
theorem B4206755 : Blo 1819611 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B2732195 : Blo 1819611 2732195 := bstep (se 1 (by rfl) ⟨2049146, by rfl⟩ : syracuseStep 2732195 = 4098293) B4098293
theorem B2732225 : Blo 1819611 2732225 := bstep (se 2 (by rfl) ⟨1024584, by rfl⟩ : syracuseStep 2732225 = 2049169) B2049169
theorem B2732243 : Blo 1819611 2732243 := bstep (se 1 (by rfl) ⟨2049182, by rfl⟩ : syracuseStep 2732243 = 4098365) B4098365
theorem B2732273 : Blo 1819611 2732273 := bstep (se 2 (by rfl) ⟨1024602, by rfl⟩ : syracuseStep 2732273 = 2049205) B2049205
theorem B2732291 : Blo 1819611 2732291 := bstep (se 1 (by rfl) ⟨2049218, by rfl⟩ : syracuseStep 2732291 = 4098437) B4098437
theorem B13824269 : Blo 1819611 13824269 := bstep (se 3 (by rfl) ⟨2592050, by rfl⟩ : syracuseStep 13824269 = 5184101) B5184101
theorem B2732321 : Blo 1819611 2732321 := bstep (se 2 (by rfl) ⟨1024620, by rfl⟩ : syracuseStep 2732321 = 2049241) B2049241
theorem B2732339 : Blo 1819611 2732339 := bstep (se 1 (by rfl) ⟨2049254, by rfl⟩ : syracuseStep 2732339 = 4098509) B4098509
theorem B4608323 : Blo 1819611 4608323 := bstep (se 1 (by rfl) ⟨3456242, by rfl⟩ : syracuseStep 4608323 = 6912485) B6912485
theorem B2732369 : Blo 1819611 2732369 := bstep (se 2 (by rfl) ⟨1024638, by rfl⟩ : syracuseStep 2732369 = 2049277) B2049277
theorem B2732387 : Blo 1819611 2732387 := bstep (se 1 (by rfl) ⟨2049290, by rfl⟩ : syracuseStep 2732387 = 4098581) B4098581
theorem B2732417 : Blo 1819611 2732417 := bstep (se 2 (by rfl) ⟨1024656, by rfl⟩ : syracuseStep 2732417 = 2049313) B2049313
theorem B5181869 : Blo 1819611 5181869 := bstep (se 3 (by rfl) ⟨971600, by rfl⟩ : syracuseStep 5181869 = 1943201) B1943201
theorem B8303053 : Blo 1819611 8303053 := bstep (se 3 (by rfl) ⟨1556822, by rfl⟩ : syracuseStep 8303053 = 3113645) B3113645
theorem B10367473 : Blo 1819611 10367473 := bstep (se 2 (by rfl) ⟨3887802, by rfl⟩ : syracuseStep 10367473 = 7775605) B7775605
theorem B4608515 : Blo 1819611 4608515 := bstep (se 1 (by rfl) ⟨3456386, by rfl⟩ : syracuseStep 4608515 = 6912773) B6912773
theorem B6910541 : Blo 1819611 6910541 := bstep (se 3 (by rfl) ⟨1295726, by rfl⟩ : syracuseStep 6910541 = 2591453) B2591453
theorem B5182051 : Blo 1819611 5182051 := bstep (se 1 (by rfl) ⟨3886538, by rfl⟩ : syracuseStep 5182051 = 7773077) B7773077
theorem B16601699 : Blo 1819611 16601699 := bstep (se 1 (by rfl) ⟨12451274, by rfl⟩ : syracuseStep 16601699 = 24902549) B24902549
theorem B5829347 : Blo 1819611 5829347 := bstep (se 1 (by rfl) ⟨4372010, by rfl⟩ : syracuseStep 5829347 = 8744021) B8744021
theorem B5182211 : Blo 1819611 5182211 := bstep (se 1 (by rfl) ⟨3886658, by rfl⟩ : syracuseStep 5182211 = 7773317) B7773317
theorem B11670277 : Blo 1819611 11670277 := bstep (se 4 (by rfl) ⟨1094088, by rfl⟩ : syracuseStep 11670277 = 2188177) B2188177
theorem B9220877 : Blo 1819611 9220877 := bstep (se 3 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 9220877 = 3457829) B3457829
theorem B8885027 : Blo 1819611 8885027 := bstep (se 1 (by rfl) ⟨6663770, by rfl⟩ : syracuseStep 8885027 = 13327541) B13327541
theorem B2626561 : Blo 1819611 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B8746019 : Blo 1819611 8746019 := bstep (se 1 (by rfl) ⟨6559514, by rfl⟩ : syracuseStep 8746019 = 13119029) B13119029
theorem B2626625 : Blo 1819611 2626625 := bstep (se 2 (by rfl) ⟨984984, by rfl⟩ : syracuseStep 2626625 = 1969969) B1969969
theorem B5829745 : Blo 1819611 5829745 := bstep (se 2 (by rfl) ⟨2186154, by rfl⟩ : syracuseStep 5829745 = 4372309) B4372309
theorem B3282115 : Blo 1819611 3282115 := bstep (se 1 (by rfl) ⟨2461586, by rfl⟩ : syracuseStep 3282115 = 4923173) B4923173
theorem B3282179 : Blo 1819611 3282179 := bstep (se 1 (by rfl) ⟨2461634, by rfl⟩ : syracuseStep 3282179 = 4923269) B4923269
theorem B8303971 : Blo 1819611 8303971 := bstep (se 1 (by rfl) ⟨6227978, by rfl⟩ : syracuseStep 8303971 = 12455957) B12455957
theorem B6911345 : Blo 1819611 6911345 := bstep (se 2 (by rfl) ⟨2591754, by rfl⟩ : syracuseStep 6911345 = 5183509) B5183509
theorem B4609457 : Blo 1819611 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B3282353 : Blo 1819611 3282353 := bstep (se 2 (by rfl) ⟨1230882, by rfl⟩ : syracuseStep 3282353 = 2461765) B2461765
theorem B4609507 : Blo 1819611 4609507 := bstep (se 1 (by rfl) ⟨3457130, by rfl⟩ : syracuseStep 4609507 = 6914261) B6914261
theorem B9213425 : Blo 1819611 9213425 := bstep (se 2 (by rfl) ⟨3455034, by rfl⟩ : syracuseStep 9213425 = 6910069) B6910069
theorem B8746481 : Blo 1819611 8746481 := bstep (se 2 (by rfl) ⟨3279930, by rfl⟩ : syracuseStep 8746481 = 6559861) B6559861
theorem B8304113 : Blo 1819611 8304113 := bstep (se 2 (by rfl) ⟨3114042, by rfl⟩ : syracuseStep 8304113 = 6228085) B6228085
theorem B3454481 : Blo 1819611 3454481 := bstep (se 2 (by rfl) ⟨1295430, by rfl⟩ : syracuseStep 3454481 = 2590861) B2590861
theorem B5830193 : Blo 1819611 5830193 := bstep (se 2 (by rfl) ⟨2186322, by rfl⟩ : syracuseStep 5830193 = 4372645) B4372645
theorem B23983685 : Blo 1819611 23983685 := bstep (se 4 (by rfl) ⟨2248470, by rfl⟩ : syracuseStep 23983685 = 4496941) B4496941
theorem B4372049 : Blo 1819611 4372049 := bstep (se 2 (by rfl) ⟨1639518, by rfl⟩ : syracuseStep 4372049 = 3279037) B3279037
theorem B4609649 : Blo 1819611 4609649 := bstep (se 2 (by rfl) ⟨1728618, by rfl⟩ : syracuseStep 4609649 = 3457237) B3457237
theorem B6141581 : Blo 1819611 6141581 := bstep (se 3 (by rfl) ⟨1151546, by rfl⟩ : syracuseStep 6141581 = 2303093) B2303093
theorem B6141635 : Blo 1819611 6141635 := bstep (se 1 (by rfl) ⟨4606226, by rfl⟩ : syracuseStep 6141635 = 9212453) B9212453
theorem B6231811 : Blo 1819611 6231811 := bstep (se 1 (by rfl) ⟨4673858, by rfl⟩ : syracuseStep 6231811 = 9347717) B9347717
theorem B3888931 : Blo 1819611 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B5183281 : Blo 1819611 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B11663203 : Blo 1819611 11663203 := bstep (se 1 (by rfl) ⟨8747402, by rfl⟩ : syracuseStep 11663203 = 17494805) B17494805
theorem B4372337 : Blo 1819611 4372337 := bstep (se 2 (by rfl) ⟨1639626, by rfl⟩ : syracuseStep 4372337 = 3279253) B3279253
theorem B3454883 : Blo 1819611 3454883 := bstep (se 1 (by rfl) ⟨2591162, by rfl⟩ : syracuseStep 3454883 = 5182325) B5182325
theorem B10368931 : Blo 1819611 10368931 := bstep (se 1 (by rfl) ⟨7776698, by rfl⟩ : syracuseStep 10368931 = 15553397) B15553397
theorem B6141905 : Blo 1819611 6141905 := bstep (se 2 (by rfl) ⟨2303214, by rfl⟩ : syracuseStep 6141905 = 4606429) B4606429
theorem B6912013 : Blo 1819611 6912013 := bstep (se 3 (by rfl) ⟨1296002, by rfl⟩ : syracuseStep 6912013 = 2592005) B2592005
theorem B2627843 : Blo 1819611 2627843 := bstep (se 1 (by rfl) ⟨1970882, by rfl⟩ : syracuseStep 2627843 = 3941765) B3941765
theorem B4094225 : Blo 1819611 4094225 := bstep (se 2 (by rfl) ⟨1535334, by rfl⟩ : syracuseStep 4094225 = 3070669) B3070669
theorem B4094243 : Blo 1819611 4094243 := bstep (se 1 (by rfl) ⟨3070682, by rfl⟩ : syracuseStep 4094243 = 6141365) B6141365
theorem B21027185 : Blo 1819611 21027185 := bstep (se 2 (by rfl) ⟨7885194, by rfl⟩ : syracuseStep 21027185 = 15770389) B15770389
theorem B3996035 : Blo 1819611 3996035 := bstep (se 1 (by rfl) ⟨2997026, by rfl⟩ : syracuseStep 3996035 = 5994053) B5994053
theorem B10369457 : Blo 1819611 10369457 := bstep (se 2 (by rfl) ⟨3888546, by rfl⟩ : syracuseStep 10369457 = 7777093) B7777093
theorem B6142445 : Blo 1819611 6142445 := bstep (se 3 (by rfl) ⟨1151708, by rfl⟩ : syracuseStep 6142445 = 2303417) B2303417
theorem B6142499 : Blo 1819611 6142499 := bstep (se 1 (by rfl) ⟨4606874, by rfl⟩ : syracuseStep 6142499 = 9213749) B9213749
theorem B4094513 : Blo 1819611 4094513 := bstep (se 2 (by rfl) ⟨1535442, by rfl⟩ : syracuseStep 4094513 = 3070885) B3070885
theorem B11074097 : Blo 1819611 11074097 := bstep (se 2 (by rfl) ⟨4152786, by rfl⟩ : syracuseStep 11074097 = 8305573) B8305573
theorem B4094531 : Blo 1819611 4094531 := bstep (se 1 (by rfl) ⟨3070898, by rfl⟩ : syracuseStep 4094531 = 6141797) B6141797
theorem B13818437 : Blo 1819611 13818437 := bstep (se 4 (by rfl) ⟨1295478, by rfl⟩ : syracuseStep 13818437 = 2590957) B2590957
theorem B4610641 : Blo 1819611 4610641 := bstep (se 2 (by rfl) ⟨1728990, by rfl⟩ : syracuseStep 4610641 = 3457981) B3457981
theorem B3889777 : Blo 1819611 3889777 := bstep (se 2 (by rfl) ⟨1458666, by rfl⟩ : syracuseStep 3889777 = 2917333) B2917333
theorem B3070595 : Blo 1819611 3070595 := bstep (se 1 (by rfl) ⟨2302946, by rfl⟩ : syracuseStep 3070595 = 4605893) B4605893
theorem B50502341 : Blo 1819611 50502341 := bstep (se 4 (by rfl) ⟨4734594, by rfl⟩ : syracuseStep 50502341 = 9469189) B9469189
theorem B3070723 : Blo 1819611 3070723 := bstep (se 1 (by rfl) ⟨2303042, by rfl⟩ : syracuseStep 3070723 = 4606085) B4606085
theorem B3455779 : Blo 1819611 3455779 := bstep (se 1 (by rfl) ⟨2591834, by rfl⟩ : syracuseStep 3455779 = 5183669) B5183669
theorem B6912803 : Blo 1819611 6912803 := bstep (se 1 (by rfl) ⟨5184602, by rfl⟩ : syracuseStep 6912803 = 10369205) B10369205
theorem B6142769 : Blo 1819611 6142769 := bstep (se 2 (by rfl) ⟨2303538, by rfl⟩ : syracuseStep 6142769 = 4607077) B4607077
theorem B3324739 : Blo 1819611 3324739 := bstep (se 1 (by rfl) ⟨2493554, by rfl⟩ : syracuseStep 3324739 = 4987109) B4987109
theorem B4094801 : Blo 1819611 4094801 := bstep (se 2 (by rfl) ⟨1535550, by rfl⟩ : syracuseStep 4094801 = 3071101) B3071101
theorem B4094819 : Blo 1819611 4094819 := bstep (se 1 (by rfl) ⟨3071114, by rfl⟩ : syracuseStep 4094819 = 6142229) B6142229
theorem B4610915 : Blo 1819611 4610915 := bstep (se 1 (by rfl) ⟨3458186, by rfl⟩ : syracuseStep 4610915 = 6916373) B6916373
theorem B3070865 : Blo 1819611 3070865 := bstep (se 2 (by rfl) ⟨1151574, by rfl⟩ : syracuseStep 3070865 = 2303149) B2303149
theorem B4496273 : Blo 1819611 4496273 := bstep (se 2 (by rfl) ⟨1686102, by rfl⟩ : syracuseStep 4496273 = 3372205) B3372205
theorem B2186131 : Blo 1819611 2186131 := bstep (se 1 (by rfl) ⟨1639598, by rfl⟩ : syracuseStep 2186131 = 3279197) B3279197
theorem B9214883 : Blo 1819611 9214883 := bstep (se 1 (by rfl) ⟨6911162, by rfl⟩ : syracuseStep 9214883 = 13822325) B13822325
theorem B3455939 : Blo 1819611 3455939 := bstep (se 1 (by rfl) ⟨2591954, by rfl⟩ : syracuseStep 3455939 = 5183909) B5183909
theorem B3505123 : Blo 1819611 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B3070993 : Blo 1819611 3070993 := bstep (se 2 (by rfl) ⟨1151622, by rfl⟩ : syracuseStep 3070993 = 2303245) B2303245
theorem B5184557 : Blo 1819611 5184557 := bstep (se 3 (by rfl) ⟨972104, by rfl⟩ : syracuseStep 5184557 = 1944209) B1944209
theorem B3071027 : Blo 1819611 3071027 := bstep (se 1 (by rfl) ⟨2303270, by rfl⟩ : syracuseStep 3071027 = 4606541) B4606541
theorem B4095089 : Blo 1819611 4095089 := bstep (se 2 (by rfl) ⟨1535658, by rfl⟩ : syracuseStep 4095089 = 3071317) B3071317
theorem B13827185 : Blo 1819611 13827185 := bstep (se 2 (by rfl) ⟨5185194, by rfl⟩ : syracuseStep 13827185 = 10370389) B10370389
theorem B4095107 : Blo 1819611 4095107 := bstep (se 1 (by rfl) ⟨3071330, by rfl⟩ : syracuseStep 4095107 = 6142661) B6142661
theorem B3071155 : Blo 1819611 3071155 := bstep (se 1 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 3071155 = 4606733) B4606733
theorem B2915507 : Blo 1819611 2915507 := bstep (se 1 (by rfl) ⟨2186630, by rfl⟩ : syracuseStep 2915507 = 4373261) B4373261
theorem B2047171 : Blo 1819611 2047171 := bstep (se 1 (by rfl) ⟨1535378, by rfl⟩ : syracuseStep 2047171 = 3070757) B3070757
theorem B5184739 : Blo 1819611 5184739 := bstep (se 1 (by rfl) ⟨3888554, by rfl⟩ : syracuseStep 5184739 = 7777109) B7777109
theorem B5184785 : Blo 1819611 5184785 := bstep (se 2 (by rfl) ⟨1944294, by rfl⟩ : syracuseStep 5184785 = 3888589) B3888589
theorem B3071297 : Blo 1819611 3071297 := bstep (se 2 (by rfl) ⟨1151736, by rfl⟩ : syracuseStep 3071297 = 2303473) B2303473
theorem B6143309 : Blo 1819611 6143309 := bstep (se 3 (by rfl) ⟨1151870, by rfl⟩ : syracuseStep 6143309 = 2303741) B2303741
theorem B2047315 : Blo 1819611 2047315 := bstep (se 1 (by rfl) ⟨1535486, by rfl⟩ : syracuseStep 2047315 = 3070973) B3070973
theorem B6143363 : Blo 1819611 6143363 := bstep (se 1 (by rfl) ⟨4607522, by rfl⟩ : syracuseStep 6143363 = 9215045) B9215045
theorem B4095377 : Blo 1819611 4095377 := bstep (se 2 (by rfl) ⟨1535766, by rfl⟩ : syracuseStep 4095377 = 3071533) B3071533
theorem B4095395 : Blo 1819611 4095395 := bstep (se 1 (by rfl) ⟨3071546, by rfl⟩ : syracuseStep 4095395 = 6143093) B6143093
theorem B6913457 : Blo 1819611 6913457 := bstep (se 2 (by rfl) ⟨2592546, by rfl⟩ : syracuseStep 6913457 = 5185093) B5185093
theorem B3071425 : Blo 1819611 3071425 := bstep (se 2 (by rfl) ⟨1151784, by rfl⟩ : syracuseStep 3071425 = 2303569) B2303569
theorem B2915795 : Blo 1819611 2915795 := bstep (se 1 (by rfl) ⟨2186846, by rfl⟩ : syracuseStep 2915795 = 4373693) B4373693
theorem B2047459 : Blo 1819611 2047459 := bstep (se 1 (by rfl) ⟨1535594, by rfl⟩ : syracuseStep 2047459 = 3071189) B3071189
theorem B3071459 : Blo 1819611 3071459 := bstep (se 1 (by rfl) ⟨2303594, by rfl⟩ : syracuseStep 3071459 = 4607189) B4607189
theorem B5832269 : Blo 1819611 5832269 := bstep (se 3 (by rfl) ⟨1093550, by rfl⟩ : syracuseStep 5832269 = 2187101) B2187101
theorem B3071587 : Blo 1819611 3071587 := bstep (se 1 (by rfl) ⟨2303690, by rfl⟩ : syracuseStep 3071587 = 4607381) B4607381
theorem B31121009 : Blo 1819611 31121009 := bstep (se 2 (by rfl) ⟨11670378, by rfl⟩ : syracuseStep 31121009 = 23340757) B23340757
theorem B2047603 : Blo 1819611 2047603 := bstep (se 1 (by rfl) ⟨1535702, by rfl⟩ : syracuseStep 2047603 = 3071405) B3071405
theorem B6143633 : Blo 1819611 6143633 := bstep (se 2 (by rfl) ⟨2303862, by rfl⟩ : syracuseStep 6143633 = 4607725) B4607725
theorem B4095665 : Blo 1819611 4095665 := bstep (se 2 (by rfl) ⟨1535874, by rfl⟩ : syracuseStep 4095665 = 3071749) B3071749
theorem B2186947 : Blo 1819611 2186947 := bstep (se 1 (by rfl) ⟨1640210, by rfl⟩ : syracuseStep 2186947 = 3280421) B3280421
theorem B4095683 : Blo 1819611 4095683 := bstep (se 1 (by rfl) ⟨3071762, by rfl⟩ : syracuseStep 4095683 = 6143525) B6143525
theorem B9215693 : Blo 1819611 9215693 := bstep (se 3 (by rfl) ⟨1727942, by rfl⟩ : syracuseStep 9215693 = 3455885) B3455885
theorem B3071729 : Blo 1819611 3071729 := bstep (se 2 (by rfl) ⟨1151898, by rfl⟩ : syracuseStep 3071729 = 2303797) B2303797
theorem B2047747 : Blo 1819611 2047747 := bstep (se 1 (by rfl) ⟨1535810, by rfl⟩ : syracuseStep 2047747 = 3071621) B3071621
theorem B7773965 : Blo 1819611 7773965 := bstep (se 3 (by rfl) ⟨1457618, by rfl⟩ : syracuseStep 7773965 = 2915237) B2915237
theorem B7774001 : Blo 1819611 7774001 := bstep (se 2 (by rfl) ⟨2915250, by rfl⟩ : syracuseStep 7774001 = 5830501) B5830501
theorem B10370915 : Blo 1819611 10370915 := bstep (se 1 (by rfl) ⟨7778186, by rfl⟩ : syracuseStep 10370915 = 15556373) B15556373
theorem B15548273 : Blo 1819611 15548273 := bstep (se 2 (by rfl) ⟨5830602, by rfl⟩ : syracuseStep 15548273 = 11661205) B11661205
theorem B3071857 : Blo 1819611 3071857 := bstep (se 2 (by rfl) ⟨1151946, by rfl⟩ : syracuseStep 3071857 = 2303893) B2303893
theorem B2916211 : Blo 1819611 2916211 := bstep (se 1 (by rfl) ⟨2187158, by rfl⟩ : syracuseStep 2916211 = 4374317) B4374317
theorem B2047891 : Blo 1819611 2047891 := bstep (se 1 (by rfl) ⟨1535918, by rfl⟩ : syracuseStep 2047891 = 3071837) B3071837
theorem B3071891 : Blo 1819611 3071891 := bstep (se 1 (by rfl) ⟨2303918, by rfl⟩ : syracuseStep 3071891 = 4607837) B4607837
theorem B4095953 : Blo 1819611 4095953 := bstep (se 2 (by rfl) ⟨1535982, by rfl⟩ : syracuseStep 4095953 = 3071965) B3071965
theorem B4095971 : Blo 1819611 4095971 := bstep (se 1 (by rfl) ⟨3071978, by rfl⟩ : syracuseStep 4095971 = 6143957) B6143957
theorem B9846755 : Blo 1819611 9846755 := bstep (se 1 (by rfl) ⟨7385066, by rfl⟩ : syracuseStep 9846755 = 14770133) B14770133
theorem B3457009 : Blo 1819611 3457009 := bstep (se 2 (by rfl) ⟨1296378, by rfl⟩ : syracuseStep 3457009 = 2592757) B2592757
theorem B9216017 : Blo 1819611 9216017 := bstep (se 2 (by rfl) ⟨3456006, by rfl⟩ : syracuseStep 9216017 = 6912013) B6912013
theorem B8306705 : Blo 1819611 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B3112985 : Blo 1819611 3112985 := bstep (se 2 (by rfl) ⟨1167369, by rfl⟩ : syracuseStep 3112985 = 2334739) B2334739
theorem B4096025 : Blo 1819611 4096025 := bstep (se 2 (by rfl) ⟨1536009, by rfl⟩ : syracuseStep 4096025 = 3072019) B3072019
theorem B5185559 : Blo 1819611 5185559 := bstep (se 1 (by rfl) ⟨3889169, by rfl⟩ : syracuseStep 5185559 = 7778339) B7778339
theorem B13123619 : Blo 1819611 13123619 := bstep (se 1 (by rfl) ⟨9842714, by rfl⟩ : syracuseStep 13123619 = 19685429) B19685429
theorem B7004225 : Blo 1819611 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B6144065 : Blo 1819611 6144065 := bstep (se 2 (by rfl) ⟨2304024, by rfl⟩ : syracuseStep 6144065 = 4608049) B4608049
theorem B2048107 : Blo 1819611 2048107 := bstep (se 1 (by rfl) ⟨1536080, by rfl⟩ : syracuseStep 2048107 = 3072161) B3072161
theorem B4096115 : Blo 1819611 4096115 := bstep (se 1 (by rfl) ⟨3072086, by rfl⟩ : syracuseStep 4096115 = 6144173) B6144173
theorem B4096151 : Blo 1819611 4096151 := bstep (se 1 (by rfl) ⟨3072113, by rfl⟩ : syracuseStep 4096151 = 6144227) B6144227
theorem B7004333 : Blo 1819611 7004333 := bstep (se 3 (by rfl) ⟨1313312, by rfl⟩ : syracuseStep 7004333 = 2626625) B2626625
theorem B15761587 : Blo 1819611 15761587 := bstep (se 1 (by rfl) ⟨11821190, by rfl⟩ : syracuseStep 15761587 = 23642381) B23642381
theorem B9216179 : Blo 1819611 9216179 := bstep (se 1 (by rfl) ⟨6912134, by rfl⟩ : syracuseStep 9216179 = 13824269) B13824269
theorem B3072215 : Blo 1819611 3072215 := bstep (se 1 (by rfl) ⟨2304161, by rfl⟩ : syracuseStep 3072215 = 4608323) B4608323
theorem B2048215 : Blo 1819611 2048215 := bstep (se 1 (by rfl) ⟨1536161, by rfl⟩ : syracuseStep 2048215 = 3072323) B3072323
theorem B4096331 : Blo 1819611 4096331 := bstep (se 1 (by rfl) ⟨3072248, by rfl⟩ : syracuseStep 4096331 = 6144497) B6144497
theorem B3072343 : Blo 1819611 3072343 := bstep (se 1 (by rfl) ⟨2304257, by rfl⟩ : syracuseStep 3072343 = 4608515) B4608515
theorem B4096385 : Blo 1819611 4096385 := bstep (se 2 (by rfl) ⟨1536144, by rfl⟩ : syracuseStep 4096385 = 3072289) B3072289
theorem B2048395 : Blo 1819611 2048395 := bstep (se 1 (by rfl) ⟨1536296, by rfl⟩ : syracuseStep 2048395 = 3072593) B3072593
theorem B11067799 : Blo 1819611 11067799 := bstep (se 1 (by rfl) ⟨8300849, by rfl⟩ : syracuseStep 11067799 = 16601699) B16601699
theorem B5833139 : Blo 1819611 5833139 := bstep (se 1 (by rfl) ⟨4374854, by rfl⟩ : syracuseStep 5833139 = 8749709) B8749709
theorem B3457495 : Blo 1819611 3457495 := bstep (se 1 (by rfl) ⟨2593121, by rfl⟩ : syracuseStep 3457495 = 5186243) B5186243
theorem B2048503 : Blo 1819611 2048503 := bstep (se 1 (by rfl) ⟨1536377, by rfl⟩ : syracuseStep 2048503 = 3072755) B3072755
theorem B4669975 : Blo 1819611 4669975 := bstep (se 1 (by rfl) ⟨3502481, by rfl⟩ : syracuseStep 4669975 = 7004963) B7004963
theorem B5923351 : Blo 1819611 5923351 := bstep (se 1 (by rfl) ⟨4442513, by rfl⟩ : syracuseStep 5923351 = 8885027) B8885027
theorem B13828643 : Blo 1819611 13828643 := bstep (se 1 (by rfl) ⟨10371482, by rfl⟩ : syracuseStep 13828643 = 20742965) B20742965
theorem B8749633 : Blo 1819611 8749633 := bstep (se 2 (by rfl) ⟨3281112, by rfl⟩ : syracuseStep 8749633 = 6562225) B6562225
theorem B4096601 : Blo 1819611 4096601 := bstep (se 2 (by rfl) ⟨1536225, by rfl⟩ : syracuseStep 4096601 = 3072451) B3072451
theorem B6144605 : Blo 1819611 6144605 := bstep (se 3 (by rfl) ⟨1152113, by rfl⟩ : syracuseStep 6144605 = 2304227) B2304227
theorem B11666051 : Blo 1819611 11666051 := bstep (se 1 (by rfl) ⟨8749538, by rfl⟩ : syracuseStep 11666051 = 17499077) B17499077
theorem B2769547 : Blo 1819611 2769547 := bstep (se 1 (by rfl) ⟨2077160, by rfl⟩ : syracuseStep 2769547 = 4154321) B4154321
theorem B2048683 : Blo 1819611 2048683 := bstep (se 1 (by rfl) ⟨1536512, by rfl⟩ : syracuseStep 2048683 = 3073025) B3073025
theorem B4096691 : Blo 1819611 4096691 := bstep (se 1 (by rfl) ⟨3072518, by rfl⟩ : syracuseStep 4096691 = 6145037) B6145037
theorem B4096727 : Blo 1819611 4096727 := bstep (se 1 (by rfl) ⟨3072545, by rfl⟩ : syracuseStep 4096727 = 6145091) B6145091
theorem B2048791 : Blo 1819611 2048791 := bstep (se 1 (by rfl) ⟨1536593, by rfl⟩ : syracuseStep 2048791 = 3073187) B3073187
theorem B5186369 : Blo 1819611 5186369 := bstep (se 2 (by rfl) ⟨1944888, by rfl⟩ : syracuseStep 5186369 = 3889777) B3889777
theorem B4096907 : Blo 1819611 4096907 := bstep (se 1 (by rfl) ⟨3072680, by rfl⟩ : syracuseStep 4096907 = 6145361) B6145361
theorem B4096961 : Blo 1819611 4096961 := bstep (se 2 (by rfl) ⟨1536360, by rfl⟩ : syracuseStep 4096961 = 3072721) B3072721
theorem B3072971 : Blo 1819611 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B2048971 : Blo 1819611 2048971 := bstep (se 1 (by rfl) ⟨1536728, by rfl⟩ : syracuseStep 2048971 = 3073457) B3073457
theorem B2188235 : Blo 1819611 2188235 := bstep (se 1 (by rfl) ⟨1641176, by rfl⟩ : syracuseStep 2188235 = 3282353) B3282353
theorem B1819627 : Blo 1819611 1819627 := bstep (se 1 (by rfl) ⟨1364720, by rfl⟩ : syracuseStep 1819627 = 2729441) B2729441
theorem B1819639 : Blo 1819611 1819639 := bstep (se 1 (by rfl) ⟨1364729, by rfl⟩ : syracuseStep 1819639 = 2729459) B2729459
theorem B2302987 : Blo 1819611 2302987 := bstep (se 1 (by rfl) ⟨1727240, by rfl⟩ : syracuseStep 2302987 = 3454481) B3454481
theorem B1819659 : Blo 1819611 1819659 := bstep (se 1 (by rfl) ⟨1364744, by rfl⟩ : syracuseStep 1819659 = 2729489) B2729489
theorem B1819671 : Blo 1819611 1819671 := bstep (se 1 (by rfl) ⟨1364753, by rfl⟩ : syracuseStep 1819671 = 2729507) B2729507
theorem B1819691 : Blo 1819611 1819691 := bstep (se 1 (by rfl) ⟨1364768, by rfl⟩ : syracuseStep 1819691 = 2729537) B2729537
theorem B1819703 : Blo 1819611 1819703 := bstep (se 1 (by rfl) ⟨1364777, by rfl⟩ : syracuseStep 1819703 = 2729555) B2729555
theorem B2049079 : Blo 1819611 2049079 := bstep (se 1 (by rfl) ⟨1536809, by rfl⟩ : syracuseStep 2049079 = 3073619) B3073619
theorem B1819723 : Blo 1819611 1819723 := bstep (se 1 (by rfl) ⟨1364792, by rfl⟩ : syracuseStep 1819723 = 2729585) B2729585
theorem B3073099 : Blo 1819611 3073099 := bstep (se 1 (by rfl) ⟨2304824, by rfl⟩ : syracuseStep 3073099 = 4609649) B4609649
theorem B33686603 : Blo 1819611 33686603 := bstep (se 1 (by rfl) ⟨25264952, by rfl⟩ : syracuseStep 33686603 = 50529905) B50529905
theorem B1819735 : Blo 1819611 1819735 := bstep (se 1 (by rfl) ⟨1364801, by rfl⟩ : syracuseStep 1819735 = 2729603) B2729603
theorem B4432985 : Blo 1819611 4432985 := bstep (se 2 (by rfl) ⟨1662369, by rfl⟩ : syracuseStep 4432985 = 3324739) B3324739
theorem B1819755 : Blo 1819611 1819755 := bstep (se 1 (by rfl) ⟨1364816, by rfl⟩ : syracuseStep 1819755 = 2729633) B2729633
theorem B1819767 : Blo 1819611 1819767 := bstep (se 1 (by rfl) ⟨1364825, by rfl⟩ : syracuseStep 1819767 = 2729651) B2729651
theorem B6915203 : Blo 1819611 6915203 := bstep (se 1 (by rfl) ⟨5186402, by rfl⟩ : syracuseStep 6915203 = 10372805) B10372805
theorem B1819787 : Blo 1819611 1819787 := bstep (se 1 (by rfl) ⟨1364840, by rfl⟩ : syracuseStep 1819787 = 2729681) B2729681
theorem B1819799 : Blo 1819611 1819799 := bstep (se 1 (by rfl) ⟨1364849, by rfl⟩ : syracuseStep 1819799 = 2729699) B2729699
theorem B4097177 : Blo 1819611 4097177 := bstep (se 2 (by rfl) ⟨1536441, by rfl⟩ : syracuseStep 4097177 = 3072883) B3072883
theorem B1819819 : Blo 1819611 1819819 := bstep (se 1 (by rfl) ⟨1364864, by rfl⟩ : syracuseStep 1819819 = 2729729) B2729729
theorem B1819831 : Blo 1819611 1819831 := bstep (se 1 (by rfl) ⟨1364873, by rfl⟩ : syracuseStep 1819831 = 2729747) B2729747
theorem B1819851 : Blo 1819611 1819851 := bstep (se 1 (by rfl) ⟨1364888, by rfl⟩ : syracuseStep 1819851 = 2729777) B2729777
theorem B33227981 : Blo 1819611 33227981 := bstep (se 3 (by rfl) ⟨6230246, by rfl⟩ : syracuseStep 33227981 = 12460493) B12460493
theorem B1819863 : Blo 1819611 1819863 := bstep (se 1 (by rfl) ⟨1364897, by rfl⟩ : syracuseStep 1819863 = 2729795) B2729795
theorem B3073241 : Blo 1819611 3073241 := bstep (se 2 (by rfl) ⟨1152465, by rfl⟩ : syracuseStep 3073241 = 2304931) B2304931
theorem B7775453 : Blo 1819611 7775453 := bstep (se 3 (by rfl) ⟨1457897, by rfl⟩ : syracuseStep 7775453 = 2915795) B2915795
theorem B1819883 : Blo 1819611 1819883 := bstep (se 1 (by rfl) ⟨1364912, by rfl⟩ : syracuseStep 1819883 = 2729825) B2729825
theorem B2049259 : Blo 1819611 2049259 := bstep (se 1 (by rfl) ⟨1536944, by rfl⟩ : syracuseStep 2049259 = 3073889) B3073889
theorem B4097267 : Blo 1819611 4097267 := bstep (se 1 (by rfl) ⟨3072950, by rfl⟩ : syracuseStep 4097267 = 6145901) B6145901
theorem B1819895 : Blo 1819611 1819895 := bstep (se 1 (by rfl) ⟨1364921, by rfl⟩ : syracuseStep 1819895 = 2729843) B2729843
theorem B1819915 : Blo 1819611 1819915 := bstep (se 1 (by rfl) ⟨1364936, by rfl⟩ : syracuseStep 1819915 = 2729873) B2729873
theorem B2303255 : Blo 1819611 2303255 := bstep (se 1 (by rfl) ⟨1727441, by rfl⟩ : syracuseStep 2303255 = 3454883) B3454883
theorem B1819927 : Blo 1819611 1819927 := bstep (se 1 (by rfl) ⟨1364945, by rfl⟩ : syracuseStep 1819927 = 2729891) B2729891
theorem B4097303 : Blo 1819611 4097303 := bstep (se 1 (by rfl) ⟨3072977, by rfl⟩ : syracuseStep 4097303 = 6145955) B6145955
theorem B1819947 : Blo 1819611 1819947 := bstep (se 1 (by rfl) ⟨1364960, by rfl⟩ : syracuseStep 1819947 = 2729921) B2729921
theorem B1819959 : Blo 1819611 1819959 := bstep (se 1 (by rfl) ⟨1364969, by rfl⟩ : syracuseStep 1819959 = 2729939) B2729939
theorem B1819979 : Blo 1819611 1819979 := bstep (se 1 (by rfl) ⟨1364984, by rfl⟩ : syracuseStep 1819979 = 2729969) B2729969
theorem B1819991 : Blo 1819611 1819991 := bstep (se 1 (by rfl) ⟨1364993, by rfl⟩ : syracuseStep 1819991 = 2729987) B2729987
theorem B3073369 : Blo 1819611 3073369 := bstep (se 2 (by rfl) ⟨1152513, by rfl⟩ : syracuseStep 3073369 = 2305027) B2305027
theorem B1820011 : Blo 1819611 1820011 := bstep (se 1 (by rfl) ⟨1365008, by rfl⟩ : syracuseStep 1820011 = 2730017) B2730017
theorem B1820023 : Blo 1819611 1820023 := bstep (se 1 (by rfl) ⟨1365017, by rfl⟩ : syracuseStep 1820023 = 2730035) B2730035
theorem B1820043 : Blo 1819611 1820043 := bstep (se 1 (by rfl) ⟨1365032, by rfl⟩ : syracuseStep 1820043 = 2730065) B2730065
theorem B1820055 : Blo 1819611 1820055 := bstep (se 1 (by rfl) ⟨1365041, by rfl⟩ : syracuseStep 1820055 = 2730083) B2730083
theorem B1820075 : Blo 1819611 1820075 := bstep (se 1 (by rfl) ⟨1365056, by rfl⟩ : syracuseStep 1820075 = 2730113) B2730113
theorem B1820087 : Blo 1819611 1820087 := bstep (se 1 (by rfl) ⟨1365065, by rfl⟩ : syracuseStep 1820087 = 2730131) B2730131
theorem B1820107 : Blo 1819611 1820107 := bstep (se 1 (by rfl) ⟨1365080, by rfl⟩ : syracuseStep 1820107 = 2730161) B2730161
theorem B4097483 : Blo 1819611 4097483 := bstep (se 1 (by rfl) ⟨3073112, by rfl⟩ : syracuseStep 4097483 = 6146225) B6146225
theorem B1820119 : Blo 1819611 1820119 := bstep (se 1 (by rfl) ⟨1365089, by rfl⟩ : syracuseStep 1820119 = 2730179) B2730179
theorem B1820139 : Blo 1819611 1820139 := bstep (se 1 (by rfl) ⟨1365104, by rfl⟩ : syracuseStep 1820139 = 2730209) B2730209
theorem B1820151 : Blo 1819611 1820151 := bstep (se 1 (by rfl) ⟨1365113, by rfl⟩ : syracuseStep 1820151 = 2730227) B2730227
theorem B4097537 : Blo 1819611 4097537 := bstep (se 2 (by rfl) ⟨1536576, by rfl⟩ : syracuseStep 4097537 = 3073153) B3073153
theorem B2729483 : Blo 1819611 2729483 := bstep (se 1 (by rfl) ⟨2047112, by rfl⟩ : syracuseStep 2729483 = 4094225) B4094225
theorem B1820171 : Blo 1819611 1820171 := bstep (se 1 (by rfl) ⟨1365128, by rfl⟩ : syracuseStep 1820171 = 2730257) B2730257
theorem B2729495 : Blo 1819611 2729495 := bstep (se 1 (by rfl) ⟨2047121, by rfl⟩ : syracuseStep 2729495 = 4094243) B4094243
theorem B1820183 : Blo 1819611 1820183 := bstep (se 1 (by rfl) ⟨1365137, by rfl⟩ : syracuseStep 1820183 = 2730275) B2730275
theorem B1820203 : Blo 1819611 1820203 := bstep (se 1 (by rfl) ⟨1365152, by rfl⟩ : syracuseStep 1820203 = 2730305) B2730305
theorem B1820215 : Blo 1819611 1820215 := bstep (se 1 (by rfl) ⟨1365161, by rfl⟩ : syracuseStep 1820215 = 2730323) B2730323
theorem B1820235 : Blo 1819611 1820235 := bstep (se 1 (by rfl) ⟨1365176, by rfl⟩ : syracuseStep 1820235 = 2730353) B2730353
theorem B14018123 : Blo 1819611 14018123 := bstep (se 1 (by rfl) ⟨10513592, by rfl⟩ : syracuseStep 14018123 = 21027185) B21027185
theorem B1820247 : Blo 1819611 1820247 := bstep (se 1 (by rfl) ⟨1365185, by rfl⟩ : syracuseStep 1820247 = 2730371) B2730371
theorem B2729561 : Blo 1819611 2729561 := bstep (se 2 (by rfl) ⟨1023585, by rfl⟩ : syracuseStep 2729561 = 2047171) B2047171
theorem B4376153 : Blo 1819611 4376153 := bstep (se 2 (by rfl) ⟨1641057, by rfl⟩ : syracuseStep 4376153 = 3282115) B3282115
theorem B1820267 : Blo 1819611 1820267 := bstep (se 1 (by rfl) ⟨1365200, by rfl⟩ : syracuseStep 1820267 = 2730401) B2730401
theorem B1820279 : Blo 1819611 1820279 := bstep (se 1 (by rfl) ⟨1365209, by rfl⟩ : syracuseStep 1820279 = 2730419) B2730419
theorem B1820299 : Blo 1819611 1820299 := bstep (se 1 (by rfl) ⟨1365224, by rfl⟩ : syracuseStep 1820299 = 2730449) B2730449
theorem B1820311 : Blo 1819611 1820311 := bstep (se 1 (by rfl) ⟨1365233, by rfl⟩ : syracuseStep 1820311 = 2730467) B2730467
theorem B1820331 : Blo 1819611 1820331 := bstep (se 1 (by rfl) ⟨1365248, by rfl⟩ : syracuseStep 1820331 = 2730497) B2730497
theorem B10798771 : Blo 1819611 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B1820343 : Blo 1819611 1820343 := bstep (se 1 (by rfl) ⟨1365257, by rfl⟩ : syracuseStep 1820343 = 2730515) B2730515
theorem B2729675 : Blo 1819611 2729675 := bstep (se 1 (by rfl) ⟨2047256, by rfl⟩ : syracuseStep 2729675 = 4094513) B4094513
theorem B1820363 : Blo 1819611 1820363 := bstep (se 1 (by rfl) ⟨1365272, by rfl⟩ : syracuseStep 1820363 = 2730545) B2730545
theorem B6145739 : Blo 1819611 6145739 := bstep (se 1 (by rfl) ⟨4609304, by rfl⟩ : syracuseStep 6145739 = 9218609) B9218609
theorem B2729687 : Blo 1819611 2729687 := bstep (se 1 (by rfl) ⟨2047265, by rfl⟩ : syracuseStep 2729687 = 4094531) B4094531
theorem B1820375 : Blo 1819611 1820375 := bstep (se 1 (by rfl) ⟨1365281, by rfl⟩ : syracuseStep 1820375 = 2730563) B2730563
theorem B4097753 : Blo 1819611 4097753 := bstep (se 2 (by rfl) ⟨1536657, by rfl⟩ : syracuseStep 4097753 = 3073315) B3073315
theorem B1820395 : Blo 1819611 1820395 := bstep (se 1 (by rfl) ⟨1365296, by rfl⟩ : syracuseStep 1820395 = 2730593) B2730593
theorem B1820407 : Blo 1819611 1820407 := bstep (se 1 (by rfl) ⟨1365305, by rfl⟩ : syracuseStep 1820407 = 2730611) B2730611
theorem B1820427 : Blo 1819611 1820427 := bstep (se 1 (by rfl) ⟨1365320, by rfl⟩ : syracuseStep 1820427 = 2730641) B2730641
theorem B1820439 : Blo 1819611 1820439 := bstep (se 1 (by rfl) ⟨1365329, by rfl⟩ : syracuseStep 1820439 = 2730659) B2730659
theorem B2729753 : Blo 1819611 2729753 := bstep (se 2 (by rfl) ⟨1023657, by rfl⟩ : syracuseStep 2729753 = 2047315) B2047315
theorem B1820459 : Blo 1819611 1820459 := bstep (se 1 (by rfl) ⟨1365344, by rfl⟩ : syracuseStep 1820459 = 2730689) B2730689
theorem B4097843 : Blo 1819611 4097843 := bstep (se 1 (by rfl) ⟨3073382, by rfl⟩ : syracuseStep 4097843 = 6146765) B6146765
theorem B1820471 : Blo 1819611 1820471 := bstep (se 1 (by rfl) ⟨1365353, by rfl⟩ : syracuseStep 1820471 = 2730707) B2730707
theorem B1820491 : Blo 1819611 1820491 := bstep (se 1 (by rfl) ⟨1365368, by rfl⟩ : syracuseStep 1820491 = 2730737) B2730737
theorem B1820503 : Blo 1819611 1820503 := bstep (se 1 (by rfl) ⟨1365377, by rfl⟩ : syracuseStep 1820503 = 2730755) B2730755
theorem B4097879 : Blo 1819611 4097879 := bstep (se 1 (by rfl) ⟨3073409, by rfl⟩ : syracuseStep 4097879 = 6146819) B6146819
theorem B69953381 : Blo 1819611 69953381 := bstep (se 4 (by rfl) ⟨6558129, by rfl⟩ : syracuseStep 69953381 = 13116259) B13116259
theorem B1820523 : Blo 1819611 1820523 := bstep (se 1 (by rfl) ⟨1365392, by rfl⟩ : syracuseStep 1820523 = 2730785) B2730785
theorem B1820535 : Blo 1819611 1820535 := bstep (se 1 (by rfl) ⟨1365401, by rfl⟩ : syracuseStep 1820535 = 2730803) B2730803
theorem B2729867 : Blo 1819611 2729867 := bstep (se 1 (by rfl) ⟨2047400, by rfl⟩ : syracuseStep 2729867 = 4094801) B4094801
theorem B1820555 : Blo 1819611 1820555 := bstep (se 1 (by rfl) ⟨1365416, by rfl⟩ : syracuseStep 1820555 = 2730833) B2730833
theorem B2729879 : Blo 1819611 2729879 := bstep (se 1 (by rfl) ⟨2047409, by rfl⟩ : syracuseStep 2729879 = 4094819) B4094819
theorem B1820567 : Blo 1819611 1820567 := bstep (se 1 (by rfl) ⟨1365425, by rfl⟩ : syracuseStep 1820567 = 2730851) B2730851
theorem B3073943 : Blo 1819611 3073943 := bstep (se 1 (by rfl) ⟨2305457, by rfl⟩ : syracuseStep 3073943 = 4610915) B4610915
theorem B1820587 : Blo 1819611 1820587 := bstep (se 1 (by rfl) ⟨1365440, by rfl⟩ : syracuseStep 1820587 = 2730881) B2730881
theorem B1820599 : Blo 1819611 1820599 := bstep (se 1 (by rfl) ⟨1365449, by rfl⟩ : syracuseStep 1820599 = 2730899) B2730899
theorem B1820619 : Blo 1819611 1820619 := bstep (se 1 (by rfl) ⟨1365464, by rfl⟩ : syracuseStep 1820619 = 2730929) B2730929
theorem B2303959 : Blo 1819611 2303959 := bstep (se 1 (by rfl) ⟨1727969, by rfl⟩ : syracuseStep 2303959 = 3455939) B3455939
theorem B1820631 : Blo 1819611 1820631 := bstep (se 1 (by rfl) ⟨1365473, by rfl⟩ : syracuseStep 1820631 = 2730947) B2730947
theorem B2729945 : Blo 1819611 2729945 := bstep (se 2 (by rfl) ⟨1023729, by rfl⟩ : syracuseStep 2729945 = 2047459) B2047459
theorem B6146009 : Blo 1819611 6146009 := bstep (se 2 (by rfl) ⟨2304753, by rfl⟩ : syracuseStep 6146009 = 4609507) B4609507
theorem B1820651 : Blo 1819611 1820651 := bstep (se 1 (by rfl) ⟨1365488, by rfl⟩ : syracuseStep 1820651 = 2730977) B2730977
theorem B1820663 : Blo 1819611 1820663 := bstep (se 1 (by rfl) ⟨1365497, by rfl⟩ : syracuseStep 1820663 = 2730995) B2730995
theorem B1820683 : Blo 1819611 1820683 := bstep (se 1 (by rfl) ⟨1365512, by rfl⟩ : syracuseStep 1820683 = 2731025) B2731025
theorem B4098059 : Blo 1819611 4098059 := bstep (se 1 (by rfl) ⟨3073544, by rfl⟩ : syracuseStep 4098059 = 6147089) B6147089
theorem B1820695 : Blo 1819611 1820695 := bstep (se 1 (by rfl) ⟨1365521, by rfl⟩ : syracuseStep 1820695 = 2731043) B2731043
theorem B1820715 : Blo 1819611 1820715 := bstep (se 1 (by rfl) ⟨1365536, by rfl⟩ : syracuseStep 1820715 = 2731073) B2731073
theorem B1820727 : Blo 1819611 1820727 := bstep (se 1 (by rfl) ⟨1365545, by rfl⟩ : syracuseStep 1820727 = 2731091) B2731091
theorem B4098113 : Blo 1819611 4098113 := bstep (se 2 (by rfl) ⟨1536792, by rfl⟩ : syracuseStep 4098113 = 3073585) B3073585
theorem B2730059 : Blo 1819611 2730059 := bstep (se 1 (by rfl) ⟨2047544, by rfl⟩ : syracuseStep 2730059 = 4095089) B4095089
theorem B15763531 : Blo 1819611 15763531 := bstep (se 1 (by rfl) ⟨11822648, by rfl⟩ : syracuseStep 15763531 = 23645297) B23645297
theorem B1820747 : Blo 1819611 1820747 := bstep (se 1 (by rfl) ⟨1365560, by rfl⟩ : syracuseStep 1820747 = 2731121) B2731121
theorem B9218123 : Blo 1819611 9218123 := bstep (se 1 (by rfl) ⟨6913592, by rfl⟩ : syracuseStep 9218123 = 13827185) B13827185
theorem B2730071 : Blo 1819611 2730071 := bstep (se 1 (by rfl) ⟨2047553, by rfl⟩ : syracuseStep 2730071 = 4095107) B4095107
theorem B1820759 : Blo 1819611 1820759 := bstep (se 1 (by rfl) ⟨1365569, by rfl⟩ : syracuseStep 1820759 = 2731139) B2731139
theorem B1820779 : Blo 1819611 1820779 := bstep (se 1 (by rfl) ⟨1365584, by rfl⟩ : syracuseStep 1820779 = 2731169) B2731169
theorem B1943671 : Blo 1819611 1943671 := bstep (se 1 (by rfl) ⟨1457753, by rfl⟩ : syracuseStep 1943671 = 2915507) B2915507
theorem B1820791 : Blo 1819611 1820791 := bstep (se 1 (by rfl) ⟨1365593, by rfl⟩ : syracuseStep 1820791 = 2731187) B2731187
theorem B1820811 : Blo 1819611 1820811 := bstep (se 1 (by rfl) ⟨1365608, by rfl⟩ : syracuseStep 1820811 = 2731217) B2731217
theorem B26232983 : Blo 1819611 26232983 := bstep (se 1 (by rfl) ⟨19674737, by rfl⟩ : syracuseStep 26232983 = 39349475) B39349475
theorem B1820823 : Blo 1819611 1820823 := bstep (se 1 (by rfl) ⟨1365617, by rfl⟩ : syracuseStep 1820823 = 2731235) B2731235
theorem B2730137 : Blo 1819611 2730137 := bstep (se 2 (by rfl) ⟨1023801, by rfl⟩ : syracuseStep 2730137 = 2047603) B2047603
theorem B1820843 : Blo 1819611 1820843 := bstep (se 1 (by rfl) ⟨1365632, by rfl⟩ : syracuseStep 1820843 = 2731265) B2731265
theorem B1820855 : Blo 1819611 1820855 := bstep (se 1 (by rfl) ⟨1365641, by rfl⟩ : syracuseStep 1820855 = 2731283) B2731283
theorem B1820875 : Blo 1819611 1820875 := bstep (se 1 (by rfl) ⟨1365656, by rfl⟩ : syracuseStep 1820875 = 2731313) B2731313
theorem B1820887 : Blo 1819611 1820887 := bstep (se 1 (by rfl) ⟨1365665, by rfl⟩ : syracuseStep 1820887 = 2731331) B2731331
theorem B1820907 : Blo 1819611 1820907 := bstep (se 1 (by rfl) ⟨1365680, by rfl⟩ : syracuseStep 1820907 = 2731361) B2731361
theorem B1820919 : Blo 1819611 1820919 := bstep (se 1 (by rfl) ⟨1365689, by rfl⟩ : syracuseStep 1820919 = 2731379) B2731379
theorem B2730251 : Blo 1819611 2730251 := bstep (se 1 (by rfl) ⟨2047688, by rfl⟩ : syracuseStep 2730251 = 4095377) B4095377
theorem B1820939 : Blo 1819611 1820939 := bstep (se 1 (by rfl) ⟨1365704, by rfl⟩ : syracuseStep 1820939 = 2731409) B2731409
theorem B2459927 : Blo 1819611 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B2730263 : Blo 1819611 2730263 := bstep (se 1 (by rfl) ⟨2047697, by rfl⟩ : syracuseStep 2730263 = 4095395) B4095395
theorem B1820951 : Blo 1819611 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B4098329 : Blo 1819611 4098329 := bstep (se 2 (by rfl) ⟨1536873, by rfl⟩ : syracuseStep 4098329 = 3073747) B3073747
theorem B1820971 : Blo 1819611 1820971 := bstep (se 1 (by rfl) ⟨1365728, by rfl⟩ : syracuseStep 1820971 = 2731457) B2731457
theorem B11659565 : Blo 1819611 11659565 := bstep (se 3 (by rfl) ⟨2186168, by rfl⟩ : syracuseStep 11659565 = 4372337) B4372337
theorem B1820983 : Blo 1819611 1820983 := bstep (se 1 (by rfl) ⟨1365737, by rfl⟩ : syracuseStep 1820983 = 2731475) B2731475
theorem B1821003 : Blo 1819611 1821003 := bstep (se 1 (by rfl) ⟨1365752, by rfl⟩ : syracuseStep 1821003 = 2731505) B2731505
theorem B1821015 : Blo 1819611 1821015 := bstep (se 1 (by rfl) ⟨1365761, by rfl⟩ : syracuseStep 1821015 = 2731523) B2731523
theorem B2730329 : Blo 1819611 2730329 := bstep (se 2 (by rfl) ⟨1023873, by rfl⟩ : syracuseStep 2730329 = 2047747) B2047747
theorem B8309081 : Blo 1819611 8309081 := bstep (se 2 (by rfl) ⟨3115905, by rfl⟩ : syracuseStep 8309081 = 6231811) B6231811
theorem B1821035 : Blo 1819611 1821035 := bstep (se 1 (by rfl) ⟨1365776, by rfl⟩ : syracuseStep 1821035 = 2731553) B2731553
theorem B4098419 : Blo 1819611 4098419 := bstep (se 1 (by rfl) ⟨3073814, by rfl⟩ : syracuseStep 4098419 = 6147629) B6147629
theorem B1821047 : Blo 1819611 1821047 := bstep (se 1 (by rfl) ⟨1365785, by rfl⟩ : syracuseStep 1821047 = 2731571) B2731571
theorem B1821067 : Blo 1819611 1821067 := bstep (se 1 (by rfl) ⟨1365800, by rfl⟩ : syracuseStep 1821067 = 2731601) B2731601
theorem B1821079 : Blo 1819611 1821079 := bstep (se 1 (by rfl) ⟨1365809, by rfl⟩ : syracuseStep 1821079 = 2731619) B2731619
theorem B4098455 : Blo 1819611 4098455 := bstep (se 1 (by rfl) ⟨3073841, by rfl⟩ : syracuseStep 4098455 = 6147683) B6147683
theorem B1821099 : Blo 1819611 1821099 := bstep (se 1 (by rfl) ⟨1365824, by rfl⟩ : syracuseStep 1821099 = 2731649) B2731649
theorem B1821111 : Blo 1819611 1821111 := bstep (se 1 (by rfl) ⟨1365833, by rfl⟩ : syracuseStep 1821111 = 2731667) B2731667
theorem B2730443 : Blo 1819611 2730443 := bstep (se 1 (by rfl) ⟨2047832, by rfl⟩ : syracuseStep 2730443 = 4095665) B4095665
theorem B1821131 : Blo 1819611 1821131 := bstep (se 1 (by rfl) ⟨1365848, by rfl⟩ : syracuseStep 1821131 = 2731697) B2731697
theorem B2730455 : Blo 1819611 2730455 := bstep (se 1 (by rfl) ⟨2047841, by rfl⟩ : syracuseStep 2730455 = 4095683) B4095683
theorem B1821143 : Blo 1819611 1821143 := bstep (se 1 (by rfl) ⟨1365857, by rfl⟩ : syracuseStep 1821143 = 2731715) B2731715
theorem B15550937 : Blo 1819611 15550937 := bstep (se 2 (by rfl) ⟨5831601, by rfl⟩ : syracuseStep 15550937 = 11663203) B11663203
theorem B1821163 : Blo 1819611 1821163 := bstep (se 1 (by rfl) ⟨1365872, by rfl⟩ : syracuseStep 1821163 = 2731745) B2731745
theorem B1821175 : Blo 1819611 1821175 := bstep (se 1 (by rfl) ⟨1365881, by rfl⟩ : syracuseStep 1821175 = 2731763) B2731763
theorem B1821195 : Blo 1819611 1821195 := bstep (se 1 (by rfl) ⟨1365896, by rfl⟩ : syracuseStep 1821195 = 2731793) B2731793
theorem B1821207 : Blo 1819611 1821207 := bstep (se 1 (by rfl) ⟨1365905, by rfl⟩ : syracuseStep 1821207 = 2731811) B2731811
theorem B2730521 : Blo 1819611 2730521 := bstep (se 2 (by rfl) ⟨1023945, by rfl⟩ : syracuseStep 2730521 = 2047891) B2047891
theorem B1821227 : Blo 1819611 1821227 := bstep (se 1 (by rfl) ⟨1365920, by rfl⟩ : syracuseStep 1821227 = 2731841) B2731841
theorem B1821239 : Blo 1819611 1821239 := bstep (se 1 (by rfl) ⟨1365929, by rfl⟩ : syracuseStep 1821239 = 2731859) B2731859
theorem B10365515 : Blo 1819611 10365515 := bstep (se 1 (by rfl) ⟨7774136, by rfl⟩ : syracuseStep 10365515 = 15548273) B15548273
theorem B14764619 : Blo 1819611 14764619 := bstep (se 1 (by rfl) ⟨11073464, by rfl⟩ : syracuseStep 14764619 = 22146929) B22146929
theorem B1821259 : Blo 1819611 1821259 := bstep (se 1 (by rfl) ⟨1365944, by rfl⟩ : syracuseStep 1821259 = 2731889) B2731889
theorem B1821271 : Blo 1819611 1821271 := bstep (se 1 (by rfl) ⟨1365953, by rfl⟩ : syracuseStep 1821271 = 2731907) B2731907
theorem B1821291 : Blo 1819611 1821291 := bstep (se 1 (by rfl) ⟨1365968, by rfl⟩ : syracuseStep 1821291 = 2731937) B2731937
theorem B1821303 : Blo 1819611 1821303 := bstep (se 1 (by rfl) ⟨1365977, by rfl⟩ : syracuseStep 1821303 = 2731955) B2731955
theorem B2730635 : Blo 1819611 2730635 := bstep (se 1 (by rfl) ⟨2047976, by rfl⟩ : syracuseStep 2730635 = 4095953) B4095953
theorem B1821323 : Blo 1819611 1821323 := bstep (se 1 (by rfl) ⟨1365992, by rfl⟩ : syracuseStep 1821323 = 2731985) B2731985
theorem B2730647 : Blo 1819611 2730647 := bstep (se 1 (by rfl) ⟨2047985, by rfl⟩ : syracuseStep 2730647 = 4095971) B4095971
theorem B6146711 : Blo 1819611 6146711 := bstep (se 1 (by rfl) ⟨4610033, by rfl⟩ : syracuseStep 6146711 = 9220067) B9220067
theorem B1821335 : Blo 1819611 1821335 := bstep (se 1 (by rfl) ⟨1366001, by rfl⟩ : syracuseStep 1821335 = 2732003) B2732003
theorem B6564503 : Blo 1819611 6564503 := bstep (se 1 (by rfl) ⟨4923377, by rfl⟩ : syracuseStep 6564503 = 9846755) B9846755
theorem B1821355 : Blo 1819611 1821355 := bstep (se 1 (by rfl) ⟨1366016, by rfl⟩ : syracuseStep 1821355 = 2732033) B2732033
theorem B1821367 : Blo 1819611 1821367 := bstep (se 1 (by rfl) ⟨1366025, by rfl⟩ : syracuseStep 1821367 = 2732051) B2732051
theorem B1821387 : Blo 1819611 1821387 := bstep (se 1 (by rfl) ⟨1366040, by rfl⟩ : syracuseStep 1821387 = 2732081) B2732081
theorem B1821399 : Blo 1819611 1821399 := bstep (se 1 (by rfl) ⟨1366049, by rfl⟩ : syracuseStep 1821399 = 2732099) B2732099
theorem B2730713 : Blo 1819611 2730713 := bstep (se 2 (by rfl) ⟨1024017, by rfl⟩ : syracuseStep 2730713 = 2048035) B2048035
theorem B1821419 : Blo 1819611 1821419 := bstep (se 1 (by rfl) ⟨1366064, by rfl⟩ : syracuseStep 1821419 = 2732129) B2732129
theorem B1821431 : Blo 1819611 1821431 := bstep (se 1 (by rfl) ⟨1366073, by rfl⟩ : syracuseStep 1821431 = 2732147) B2732147
theorem B7105283 : Blo 1819611 7105283 := bstep (se 1 (by rfl) ⟨5328962, by rfl⟩ : syracuseStep 7105283 = 10657925) B10657925
theorem B1821451 : Blo 1819611 1821451 := bstep (se 1 (by rfl) ⟨1366088, by rfl⟩ : syracuseStep 1821451 = 2732177) B2732177
theorem B2804503 : Blo 1819611 2804503 := bstep (se 1 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 2804503 = 4206755) B4206755
theorem B1821463 : Blo 1819611 1821463 := bstep (se 1 (by rfl) ⟨1366097, by rfl⟩ : syracuseStep 1821463 = 2732195) B2732195
theorem B1821483 : Blo 1819611 1821483 := bstep (se 1 (by rfl) ⟨1366112, by rfl⟩ : syracuseStep 1821483 = 2732225) B2732225
theorem B1821495 : Blo 1819611 1821495 := bstep (se 1 (by rfl) ⟨1366121, by rfl⟩ : syracuseStep 1821495 = 2732243) B2732243
theorem B164039489 : Blo 1819611 164039489 := bstep (se 2 (by rfl) ⟨61514808, by rfl⟩ : syracuseStep 164039489 = 123029617) B123029617
theorem B2730827 : Blo 1819611 2730827 := bstep (se 1 (by rfl) ⟨2048120, by rfl⟩ : syracuseStep 2730827 = 4096241) B4096241
theorem B1821515 : Blo 1819611 1821515 := bstep (se 1 (by rfl) ⟨1366136, by rfl⟩ : syracuseStep 1821515 = 2732273) B2732273
theorem B2730839 : Blo 1819611 2730839 := bstep (se 1 (by rfl) ⟨2048129, by rfl⟩ : syracuseStep 2730839 = 4096259) B4096259
theorem B1821527 : Blo 1819611 1821527 := bstep (se 1 (by rfl) ⟨1366145, by rfl⟩ : syracuseStep 1821527 = 2732291) B2732291
theorem B1821547 : Blo 1819611 1821547 := bstep (se 1 (by rfl) ⟨1366160, by rfl⟩ : syracuseStep 1821547 = 2732321) B2732321
theorem B1821559 : Blo 1819611 1821559 := bstep (se 1 (by rfl) ⟨1366169, by rfl⟩ : syracuseStep 1821559 = 2732339) B2732339
theorem B1821579 : Blo 1819611 1821579 := bstep (se 1 (by rfl) ⟨1366184, by rfl⟩ : syracuseStep 1821579 = 2732369) B2732369
theorem B1821591 : Blo 1819611 1821591 := bstep (se 1 (by rfl) ⟨1366193, by rfl⟩ : syracuseStep 1821591 = 2732387) B2732387
theorem B2730905 : Blo 1819611 2730905 := bstep (se 2 (by rfl) ⟨1024089, by rfl⟩ : syracuseStep 2730905 = 2048179) B2048179
theorem B1944491 : Blo 1819611 1944491 := bstep (se 1 (by rfl) ⟨1458368, by rfl⟩ : syracuseStep 1944491 = 2916737) B2916737
theorem B1821611 : Blo 1819611 1821611 := bstep (se 1 (by rfl) ⟨1366208, by rfl⟩ : syracuseStep 1821611 = 2732417) B2732417
theorem B15559685 : Blo 1819611 15559685 := bstep (se 4 (by rfl) ⟨1458720, by rfl⟩ : syracuseStep 15559685 = 2917441) B2917441
theorem B2731019 : Blo 1819611 2731019 := bstep (se 1 (by rfl) ⟨2048264, by rfl⟩ : syracuseStep 2731019 = 4096529) B4096529
theorem B2731031 : Blo 1819611 2731031 := bstep (se 1 (by rfl) ⟨2048273, by rfl⟩ : syracuseStep 2731031 = 4096547) B4096547
theorem B4607027 : Blo 1819611 4607027 := bstep (se 1 (by rfl) ⟨3455270, by rfl⟩ : syracuseStep 4607027 = 6910541) B6910541
theorem B2731097 : Blo 1819611 2731097 := bstep (se 2 (by rfl) ⟨1024161, by rfl⟩ : syracuseStep 2731097 = 2048323) B2048323
theorem B6564995 : Blo 1819611 6564995 := bstep (se 1 (by rfl) ⟨4923746, by rfl⟩ : syracuseStep 6564995 = 9847493) B9847493
theorem B3886231 : Blo 1819611 3886231 := bstep (se 1 (by rfl) ⟨2914673, by rfl⟩ : syracuseStep 3886231 = 5829347) B5829347
theorem B6147251 : Blo 1819611 6147251 := bstep (se 1 (by rfl) ⟨4610438, by rfl⟩ : syracuseStep 6147251 = 9220877) B9220877
theorem B2731211 : Blo 1819611 2731211 := bstep (se 1 (by rfl) ⟨2048408, by rfl⟩ : syracuseStep 2731211 = 4096817) B4096817
theorem B2731223 : Blo 1819611 2731223 := bstep (se 1 (by rfl) ⟨2048417, by rfl⟩ : syracuseStep 2731223 = 4096835) B4096835
theorem B11070737 : Blo 1819611 11070737 := bstep (se 2 (by rfl) ⟨4151526, by rfl⟩ : syracuseStep 11070737 = 8303053) B8303053
theorem B2731289 : Blo 1819611 2731289 := bstep (se 2 (by rfl) ⟨1024233, by rfl⟩ : syracuseStep 2731289 = 2048467) B2048467
theorem B13823297 : Blo 1819611 13823297 := bstep (se 2 (by rfl) ⟨5183736, by rfl⟩ : syracuseStep 13823297 = 10367473) B10367473
theorem B7007581 : Blo 1819611 7007581 := bstep (se 3 (by rfl) ⟨1313921, by rfl⟩ : syracuseStep 7007581 = 2627843) B2627843
theorem B8752477 : Blo 1819611 8752477 := bstep (se 3 (by rfl) ⟨1641089, by rfl⟩ : syracuseStep 8752477 = 3282179) B3282179
theorem B10800485 : Blo 1819611 10800485 := bstep (se 4 (by rfl) ⟨1012545, by rfl⟩ : syracuseStep 10800485 = 2025091) B2025091
theorem B20508005 : Blo 1819611 20508005 := bstep (se 4 (by rfl) ⟨1922625, by rfl⟩ : syracuseStep 20508005 = 3845251) B3845251
theorem B2731403 : Blo 1819611 2731403 := bstep (se 1 (by rfl) ⟨2048552, by rfl⟩ : syracuseStep 2731403 = 4097105) B4097105
theorem B2731415 : Blo 1819611 2731415 := bstep (se 1 (by rfl) ⟨2048561, by rfl⟩ : syracuseStep 2731415 = 4097123) B4097123
theorem B6147521 : Blo 1819611 6147521 := bstep (se 2 (by rfl) ⟨2305320, by rfl⟩ : syracuseStep 6147521 = 4610641) B4610641
theorem B6909401 : Blo 1819611 6909401 := bstep (se 2 (by rfl) ⟨2591025, by rfl⟩ : syracuseStep 6909401 = 5182051) B5182051
theorem B2731481 : Blo 1819611 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B4607563 : Blo 1819611 4607563 := bstep (se 1 (by rfl) ⟨3455672, by rfl⟩ : syracuseStep 4607563 = 6911345) B6911345
theorem B2731595 : Blo 1819611 2731595 := bstep (se 1 (by rfl) ⟨2048696, by rfl⟩ : syracuseStep 2731595 = 4097393) B4097393
theorem B2731607 : Blo 1819611 2731607 := bstep (se 1 (by rfl) ⟨2048705, by rfl⟩ : syracuseStep 2731607 = 4097411) B4097411
theorem B2731673 : Blo 1819611 2731673 := bstep (se 2 (by rfl) ⟨1024377, by rfl⟩ : syracuseStep 2731673 = 2048755) B2048755
theorem B15560369 : Blo 1819611 15560369 := bstep (se 2 (by rfl) ⟨5835138, by rfl⟩ : syracuseStep 15560369 = 11670277) B11670277
theorem B3886795 : Blo 1819611 3886795 := bstep (se 1 (by rfl) ⟨2915096, by rfl⟩ : syracuseStep 3886795 = 5830193) B5830193
theorem B4607705 : Blo 1819611 4607705 := bstep (se 2 (by rfl) ⟨1727889, by rfl⟩ : syracuseStep 4607705 = 3455779) B3455779
theorem B7778051 : Blo 1819611 7778051 := bstep (se 1 (by rfl) ⟨5833538, by rfl⟩ : syracuseStep 7778051 = 11667077) B11667077
theorem B2731787 : Blo 1819611 2731787 := bstep (se 1 (by rfl) ⟨2048840, by rfl⟩ : syracuseStep 2731787 = 4097681) B4097681
theorem B2731799 : Blo 1819611 2731799 := bstep (se 1 (by rfl) ⟨2048849, by rfl⟩ : syracuseStep 2731799 = 4097699) B4097699
theorem B9219905 : Blo 1819611 9219905 := bstep (se 2 (by rfl) ⟨3457464, by rfl⟩ : syracuseStep 9219905 = 6914929) B6914929
theorem B2731865 : Blo 1819611 2731865 := bstep (se 2 (by rfl) ⟨1024449, by rfl⟩ : syracuseStep 2731865 = 2048899) B2048899
theorem B2731979 : Blo 1819611 2731979 := bstep (se 1 (by rfl) ⟨2048984, by rfl⟩ : syracuseStep 2731979 = 4097969) B4097969
theorem B2731991 : Blo 1819611 2731991 := bstep (se 1 (by rfl) ⟨2048993, by rfl⟩ : syracuseStep 2731991 = 4097987) B4097987
theorem B2461657 : Blo 1819611 2461657 := bstep (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) B1846243
theorem B3502081 : Blo 1819611 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B2732057 : Blo 1819611 2732057 := bstep (se 2 (by rfl) ⟨1024521, by rfl⟩ : syracuseStep 2732057 = 2049043) B2049043
theorem B2732171 : Blo 1819611 2732171 := bstep (se 1 (by rfl) ⟨2049128, by rfl⟩ : syracuseStep 2732171 = 4098257) B4098257
theorem B2732183 : Blo 1819611 2732183 := bstep (se 1 (by rfl) ⟨2049137, by rfl⟩ : syracuseStep 2732183 = 4098275) B4098275
theorem B2592985 : Blo 1819611 2592985 := bstep (se 2 (by rfl) ⟨972369, by rfl⟩ : syracuseStep 2592985 = 1944739) B1944739
theorem B2732249 : Blo 1819611 2732249 := bstep (se 2 (by rfl) ⟨1024593, by rfl⟩ : syracuseStep 2732249 = 2049187) B2049187
theorem B2732363 : Blo 1819611 2732363 := bstep (se 1 (by rfl) ⟨2049272, by rfl⟩ : syracuseStep 2732363 = 4098545) B4098545
theorem B2732375 : Blo 1819611 2732375 := bstep (se 1 (by rfl) ⟨2049281, by rfl⟩ : syracuseStep 2732375 = 4098563) B4098563
theorem B9212291 : Blo 1819611 9212291 := bstep (se 1 (by rfl) ⟨6909218, by rfl⟩ : syracuseStep 9212291 = 13818437) B13818437
theorem B11071961 : Blo 1819611 11071961 := bstep (se 2 (by rfl) ⟨4151985, by rfl⟩ : syracuseStep 11071961 = 8303971) B8303971
theorem B4608535 : Blo 1819611 4608535 := bstep (se 1 (by rfl) ⟨3456401, by rfl⟩ : syracuseStep 4608535 = 6912803) B6912803
theorem B15561395 : Blo 1819611 15561395 := bstep (se 1 (by rfl) ⟨11671046, by rfl⟩ : syracuseStep 15561395 = 23342093) B23342093
theorem B4608971 : Blo 1819611 4608971 := bstep (se 1 (by rfl) ⟨3456728, by rfl⟩ : syracuseStep 4608971 = 6913457) B6913457
theorem B6911027 : Blo 1819611 6911027 := bstep (se 1 (by rfl) ⟨5183270, by rfl⟩ : syracuseStep 6911027 = 10366541) B10366541
theorem B3888179 : Blo 1819611 3888179 := bstep (se 1 (by rfl) ⟨2916134, by rfl⟩ : syracuseStep 3888179 = 5832269) B5832269
theorem B6911041 : Blo 1819611 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B20747339 : Blo 1819611 20747339 := bstep (se 1 (by rfl) ⟨15560504, by rfl⟩ : syracuseStep 20747339 = 31121009) B31121009
theorem B11662487 : Blo 1819611 11662487 := bstep (se 1 (by rfl) ⟨8746865, by rfl⟩ : syracuseStep 11662487 = 17493731) B17493731
theorem B3888281 : Blo 1819611 3888281 := bstep (se 2 (by rfl) ⟨1458105, by rfl⟩ : syracuseStep 3888281 = 2916211) B2916211
theorem B5182643 : Blo 1819611 5182643 := bstep (se 1 (by rfl) ⟨3886982, by rfl⟩ : syracuseStep 5182643 = 7773965) B7773965
theorem B7484609 : Blo 1819611 7484609 := bstep (se 2 (by rfl) ⟨2806728, by rfl⟩ : syracuseStep 7484609 = 5613457) B5613457
theorem B5182667 : Blo 1819611 5182667 := bstep (se 1 (by rfl) ⟨3887000, by rfl⟩ : syracuseStep 5182667 = 7774001) B7774001
theorem B13825241 : Blo 1819611 13825241 := bstep (se 2 (by rfl) ⟨5184465, by rfl⟩ : syracuseStep 13825241 = 10368931) B10368931
theorem B3282137 : Blo 1819611 3282137 := bstep (se 2 (by rfl) ⟨1230801, by rfl⟩ : syracuseStep 3282137 = 2461603) B2461603
theorem B23655685 : Blo 1819611 23655685 := bstep (se 4 (by rfl) ⟨2217720, by rfl⟩ : syracuseStep 23655685 = 4435441) B4435441
theorem B4609345 : Blo 1819611 4609345 := bstep (se 2 (by rfl) ⟨1728504, by rfl⟩ : syracuseStep 4609345 = 3457009) B3457009
theorem B170497493 : Blo 1819611 170497493 := bstep (se 7 (by rfl) ⟨1998017, by rfl⟩ : syracuseStep 170497493 = 3996035) B3996035
theorem B3888641 : Blo 1819611 3888641 := bstep (se 2 (by rfl) ⟨1458240, by rfl⟩ : syracuseStep 3888641 = 2916481) B2916481
theorem B4920925 : Blo 1819611 4920925 := bstep (se 3 (by rfl) ⟨922673, by rfl⟩ : syracuseStep 4920925 = 1845347) B1845347
theorem B3454579 : Blo 1819611 3454579 := bstep (se 1 (by rfl) ⟨2590934, by rfl⟩ : syracuseStep 3454579 = 5181869) B5181869
theorem B9221849 : Blo 1819611 9221849 := bstep (se 2 (by rfl) ⟨3458193, by rfl⟩ : syracuseStep 9221849 = 6916387) B6916387
theorem B3454807 : Blo 1819611 3454807 := bstep (se 1 (by rfl) ⟨2591105, by rfl⟩ : syracuseStep 3454807 = 5182211) B5182211
theorem B4609943 : Blo 1819611 4609943 := bstep (se 1 (by rfl) ⟨3457457, by rfl⟩ : syracuseStep 4609943 = 6914915) B6914915
theorem B15546289 : Blo 1819611 15546289 := bstep (se 2 (by rfl) ⟨5829858, by rfl⟩ : syracuseStep 15546289 = 11659717) B11659717
theorem B3454913 : Blo 1819611 3454913 := bstep (se 2 (by rfl) ⟨1295592, by rfl⟩ : syracuseStep 3454913 = 2591185) B2591185
theorem B4986845 : Blo 1819611 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B5183453 : Blo 1819611 5183453 := bstep (se 3 (by rfl) ⟨971897, by rfl⟩ : syracuseStep 5183453 = 1943795) B1943795
theorem B5830679 : Blo 1819611 5830679 := bstep (se 1 (by rfl) ⟨4373009, by rfl⟩ : syracuseStep 5830679 = 8746019) B8746019
theorem B3455065 : Blo 1819611 3455065 := bstep (se 2 (by rfl) ⟨1295649, by rfl⟩ : syracuseStep 3455065 = 2591299) B2591299
theorem B3889367 : Blo 1819611 3889367 := bstep (se 1 (by rfl) ⟨2917025, by rfl⟩ : syracuseStep 3889367 = 5834051) B5834051
theorem B6142283 : Blo 1819611 6142283 := bstep (se 1 (by rfl) ⟨4606712, by rfl⟩ : syracuseStep 6142283 = 9213425) B9213425
theorem B5830987 : Blo 1819611 5830987 := bstep (se 1 (by rfl) ⟨4373240, by rfl⟩ : syracuseStep 5830987 = 8746481) B8746481
theorem B5536075 : Blo 1819611 5536075 := bstep (se 1 (by rfl) ⟨4152056, by rfl⟩ : syracuseStep 5536075 = 8304113) B8304113
theorem B8870219 : Blo 1819611 8870219 := bstep (se 1 (by rfl) ⟨6652664, by rfl⟩ : syracuseStep 8870219 = 13305329) B13305329
theorem B4094297 : Blo 1819611 4094297 := bstep (se 2 (by rfl) ⟨1535361, by rfl⟩ : syracuseStep 4094297 = 3070723) B3070723
theorem B15989123 : Blo 1819611 15989123 := bstep (se 1 (by rfl) ⟨11991842, by rfl⟩ : syracuseStep 15989123 = 23983685) B23983685
theorem B2914699 : Blo 1819611 2914699 := bstep (se 1 (by rfl) ⟨2186024, by rfl⟩ : syracuseStep 2914699 = 4372049) B4372049
theorem B4094387 : Blo 1819611 4094387 := bstep (se 1 (by rfl) ⟨3070790, by rfl⟩ : syracuseStep 4094387 = 6141581) B6141581
theorem B4094423 : Blo 1819611 4094423 := bstep (se 1 (by rfl) ⟨3070817, by rfl⟩ : syracuseStep 4094423 = 6141635) B6141635
theorem B4151819 : Blo 1819611 4151819 := bstep (se 1 (by rfl) ⟨3113864, by rfl⟩ : syracuseStep 4151819 = 6227729) B6227729
theorem B2914841 : Blo 1819611 2914841 := bstep (se 2 (by rfl) ⟨1093065, by rfl⟩ : syracuseStep 2914841 = 2186131) B2186131
theorem B6142553 : Blo 1819611 6142553 := bstep (se 2 (by rfl) ⟨2303457, by rfl⟩ : syracuseStep 6142553 = 4606915) B4606915
theorem B4094603 : Blo 1819611 4094603 := bstep (se 1 (by rfl) ⟨3070952, by rfl⟩ : syracuseStep 4094603 = 6141905) B6141905
theorem B3070615 : Blo 1819611 3070615 := bstep (se 1 (by rfl) ⟨2302961, by rfl⟩ : syracuseStep 3070615 = 4605923) B4605923
theorem B4094657 : Blo 1819611 4094657 := bstep (se 2 (by rfl) ⟨1535496, by rfl⟩ : syracuseStep 4094657 = 3070993) B3070993
theorem B4610753 : Blo 1819611 4610753 := bstep (se 2 (by rfl) ⟨1729032, by rfl⟩ : syracuseStep 4610753 = 3458065) B3458065
theorem B29530925 : Blo 1819611 29530925 := bstep (se 3 (by rfl) ⟨5537048, by rfl⟩ : syracuseStep 29530925 = 11074097) B11074097
theorem B7772993 : Blo 1819611 7772993 := bstep (se 2 (by rfl) ⟨2914872, by rfl⟩ : syracuseStep 7772993 = 5829745) B5829745
theorem B4094873 : Blo 1819611 4094873 := bstep (se 2 (by rfl) ⟨1535577, by rfl⟩ : syracuseStep 4094873 = 3071155) B3071155
theorem B6912971 : Blo 1819611 6912971 := bstep (se 1 (by rfl) ⟨5184728, by rfl⟩ : syracuseStep 6912971 = 10369457) B10369457
theorem B6912985 : Blo 1819611 6912985 := bstep (se 2 (by rfl) ⟨2592369, by rfl⟩ : syracuseStep 6912985 = 5184739) B5184739
theorem B4094963 : Blo 1819611 4094963 := bstep (se 1 (by rfl) ⟨3071222, by rfl⟩ : syracuseStep 4094963 = 6142445) B6142445
theorem B4094999 : Blo 1819611 4094999 := bstep (se 1 (by rfl) ⟨3071249, by rfl⟩ : syracuseStep 4094999 = 6142499) B6142499
theorem B6560813 : Blo 1819611 6560813 := bstep (se 3 (by rfl) ⟨1230152, by rfl⟩ : syracuseStep 6560813 = 2460305) B2460305
theorem B31112261 : Blo 1819611 31112261 := bstep (se 4 (by rfl) ⟨2916774, by rfl⟩ : syracuseStep 31112261 = 5833549) B5833549
theorem B2047063 : Blo 1819611 2047063 := bstep (se 1 (by rfl) ⟨1535297, by rfl⟩ : syracuseStep 2047063 = 3070595) B3070595
theorem B3890263 : Blo 1819611 3890263 := bstep (se 1 (by rfl) ⟨2917697, by rfl⟩ : syracuseStep 3890263 = 5835395) B5835395
theorem B33668227 : Blo 1819611 33668227 := bstep (se 1 (by rfl) ⟨25251170, by rfl⟩ : syracuseStep 33668227 = 50502341) B50502341
theorem B4095179 : Blo 1819611 4095179 := bstep (se 1 (by rfl) ⟨3071384, by rfl⟩ : syracuseStep 4095179 = 6142769) B6142769
theorem B4095233 : Blo 1819611 4095233 := bstep (se 2 (by rfl) ⟨1535712, by rfl⟩ : syracuseStep 4095233 = 3071425) B3071425
theorem B2047243 : Blo 1819611 2047243 := bstep (se 1 (by rfl) ⟨1535432, by rfl⟩ : syracuseStep 2047243 = 3070865) B3070865
theorem B3071243 : Blo 1819611 3071243 := bstep (se 1 (by rfl) ⟨2303432, by rfl⟩ : syracuseStep 3071243 = 4606865) B4606865
theorem B2997515 : Blo 1819611 2997515 := bstep (se 1 (by rfl) ⟨2248136, by rfl⟩ : syracuseStep 2997515 = 4496273) B4496273
theorem B6143255 : Blo 1819611 6143255 := bstep (se 1 (by rfl) ⟨4607441, by rfl⟩ : syracuseStep 6143255 = 9214883) B9214883
theorem B3939671 : Blo 1819611 3939671 := bstep (se 1 (by rfl) ⟨2954753, by rfl⟩ : syracuseStep 3939671 = 5909507) B5909507
theorem B3456371 : Blo 1819611 3456371 := bstep (se 1 (by rfl) ⟨2592278, by rfl⟩ : syracuseStep 3456371 = 5184557) B5184557
theorem B2047351 : Blo 1819611 2047351 := bstep (se 1 (by rfl) ⟨1535513, by rfl⟩ : syracuseStep 2047351 = 3071027) B3071027
theorem B3071371 : Blo 1819611 3071371 := bstep (se 1 (by rfl) ⟨2303528, by rfl⟩ : syracuseStep 3071371 = 4607057) B4607057
theorem B4095449 : Blo 1819611 4095449 := bstep (se 2 (by rfl) ⟨1535793, by rfl⟩ : syracuseStep 4095449 = 3071587) B3071587
theorem B3456523 : Blo 1819611 3456523 := bstep (se 1 (by rfl) ⟨2592392, by rfl⟩ : syracuseStep 3456523 = 5184785) B5184785
theorem B13819409 : Blo 1819611 13819409 := bstep (se 2 (by rfl) ⟨5182278, by rfl⟩ : syracuseStep 13819409 = 10364557) B10364557
theorem B3071513 : Blo 1819611 3071513 := bstep (se 2 (by rfl) ⟨1151817, by rfl⟩ : syracuseStep 3071513 = 2303635) B2303635
theorem B2047531 : Blo 1819611 2047531 := bstep (se 1 (by rfl) ⟨1535648, by rfl⟩ : syracuseStep 2047531 = 3071297) B3071297
theorem B4095539 : Blo 1819611 4095539 := bstep (se 1 (by rfl) ⟨3071654, by rfl⟩ : syracuseStep 4095539 = 6143309) B6143309
theorem B4095575 : Blo 1819611 4095575 := bstep (se 1 (by rfl) ⟨3071681, by rfl⟩ : syracuseStep 4095575 = 6143363) B6143363
theorem B2915929 : Blo 1819611 2915929 := bstep (se 2 (by rfl) ⟨1093473, by rfl⟩ : syracuseStep 2915929 = 2186947) B2186947
theorem B4988509 : Blo 1819611 4988509 := bstep (se 3 (by rfl) ⟨935345, by rfl⟩ : syracuseStep 4988509 = 1870691) B1870691
theorem B2047639 : Blo 1819611 2047639 := bstep (se 1 (by rfl) ⟨1535729, by rfl⟩ : syracuseStep 2047639 = 3071459) B3071459
theorem B3071641 : Blo 1819611 3071641 := bstep (se 2 (by rfl) ⟨1151865, by rfl⟩ : syracuseStep 3071641 = 2303731) B2303731
theorem B5185241 : Blo 1819611 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B4095755 : Blo 1819611 4095755 := bstep (se 1 (by rfl) ⟨3071816, by rfl⟩ : syracuseStep 4095755 = 6143633) B6143633
theorem B6143795 : Blo 1819611 6143795 := bstep (se 1 (by rfl) ⟨4607846, by rfl⟩ : syracuseStep 6143795 = 9215693) B9215693
theorem B4095809 : Blo 1819611 4095809 := bstep (se 2 (by rfl) ⟨1535928, by rfl⟩ : syracuseStep 4095809 = 3071857) B3071857
theorem B4374337 : Blo 1819611 4374337 := bstep (se 2 (by rfl) ⟨1640376, by rfl⟩ : syracuseStep 4374337 = 3280753) B3280753
theorem B2047819 : Blo 1819611 2047819 := bstep (se 1 (by rfl) ⟨1535864, by rfl⟩ : syracuseStep 2047819 = 3071729) B3071729
theorem B3456857 : Blo 1819611 3456857 := bstep (se 2 (by rfl) ⟨1296321, by rfl⟩ : syracuseStep 3456857 = 2592643) B2592643
theorem B18693989 : Blo 1819611 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B6913943 : Blo 1819611 6913943 := bstep (se 1 (by rfl) ⟨5185457, by rfl⟩ : syracuseStep 6913943 = 10370915) B10370915
theorem B2047927 : Blo 1819611 2047927 := bstep (se 1 (by rfl) ⟨1535945, by rfl⟩ : syracuseStep 2047927 = 3071891) B3071891
theorem B18677765 : Blo 1819611 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B6144011 : Blo 1819611 6144011 := bstep (se 1 (by rfl) ⟨4608008, by rfl⟩ : syracuseStep 6144011 = 9216017) B9216017
theorem B5537803 : Blo 1819611 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B8749079 : Blo 1819611 8749079 := bstep (se 1 (by rfl) ⟨6561809, by rfl⟩ : syracuseStep 8749079 = 13123619) B13123619
theorem B4669483 : Blo 1819611 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B4096043 : Blo 1819611 4096043 := bstep (se 1 (by rfl) ⟨3072032, by rfl⟩ : syracuseStep 4096043 = 6144065) B6144065
theorem B13828157 : Blo 1819611 13828157 := bstep (se 3 (by rfl) ⟨2592779, by rfl⟩ : syracuseStep 13828157 = 5185559) B5185559
theorem B6144119 : Blo 1819611 6144119 := bstep (se 1 (by rfl) ⟨4608089, by rfl⟩ : syracuseStep 6144119 = 9216179) B9216179
theorem B2048143 : Blo 1819611 2048143 := bstep (se 1 (by rfl) ⟨1536107, by rfl⟩ : syracuseStep 2048143 = 3072215) B3072215
theorem B3457313 : Blo 1819611 3457313 := bstep (se 2 (by rfl) ⟨1296492, by rfl⟩ : syracuseStep 3457313 = 2592985) B2592985
theorem B7381307 : Blo 1819611 7381307 := bstep (se 1 (by rfl) ⟨5535980, by rfl⟩ : syracuseStep 7381307 = 11071961) B11071961
theorem B4096403 : Blo 1819611 4096403 := bstep (se 1 (by rfl) ⟨3072302, by rfl⟩ : syracuseStep 4096403 = 6144605) B6144605
theorem B7774649 : Blo 1819611 7774649 := bstep (se 2 (by rfl) ⟨2915493, by rfl⟩ : syracuseStep 7774649 = 5830987) B5830987
theorem B7381433 : Blo 1819611 7381433 := bstep (se 2 (by rfl) ⟨2768037, by rfl⟩ : syracuseStep 7381433 = 5536075) B5536075
theorem B4096457 : Blo 1819611 4096457 := bstep (se 2 (by rfl) ⟨1536171, by rfl⟩ : syracuseStep 4096457 = 3072343) B3072343
theorem B18678221 : Blo 1819611 18678221 := bstep (se 3 (by rfl) ⟨3502166, by rfl⟩ : syracuseStep 18678221 = 7004333) B7004333
theorem B13820381 : Blo 1819611 13820381 := bstep (se 3 (by rfl) ⟨2591321, by rfl⟩ : syracuseStep 13820381 = 5182643) B5182643
theorem B3457579 : Blo 1819611 3457579 := bstep (se 1 (by rfl) ⟨2593184, by rfl⟩ : syracuseStep 3457579 = 5186369) B5186369
theorem B3072647 : Blo 1819611 3072647 := bstep (se 1 (by rfl) ⟨2304485, by rfl⟩ : syracuseStep 3072647 = 4608971) B4608971
theorem B2048647 : Blo 1819611 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B6226633 : Blo 1819611 6226633 := bstep (se 2 (by rfl) ⟨2334987, by rfl⟩ : syracuseStep 6226633 = 4669975) B4669975
theorem B6144713 : Blo 1819611 6144713 := bstep (se 2 (by rfl) ⟨2304267, by rfl⟩ : syracuseStep 6144713 = 4608535) B4608535
theorem B11666177 : Blo 1819611 11666177 := bstep (se 2 (by rfl) ⟨4374816, by rfl⟩ : syracuseStep 11666177 = 8749633) B8749633
theorem B7774991 : Blo 1819611 7774991 := bstep (se 1 (by rfl) ⟨5831243, by rfl⟩ : syracuseStep 7774991 = 11662487) B11662487
theorem B22151987 : Blo 1819611 22151987 := bstep (se 1 (by rfl) ⟨16613990, by rfl⟩ : syracuseStep 22151987 = 33227981) B33227981
theorem B9216827 : Blo 1819611 9216827 := bstep (se 1 (by rfl) ⟨6912620, by rfl⟩ : syracuseStep 9216827 = 13825241) B13825241
theorem B2048827 : Blo 1819611 2048827 := bstep (se 1 (by rfl) ⟨1536620, by rfl⟩ : syracuseStep 2048827 = 3073241) B3073241
theorem B2188091 : Blo 1819611 2188091 := bstep (se 1 (by rfl) ⟨1641068, by rfl⟩ : syracuseStep 2188091 = 3282137) B3282137
theorem B9216989 : Blo 1819611 9216989 := bstep (se 3 (by rfl) ⟨1728185, by rfl⟩ : syracuseStep 9216989 = 3456371) B3456371
theorem B113664995 : Blo 1819611 113664995 := bstep (se 1 (by rfl) ⟨85248746, by rfl⟩ : syracuseStep 113664995 = 170497493) B170497493
theorem B1819655 : Blo 1819611 1819655 := bstep (se 1 (by rfl) ⟨1364741, by rfl⟩ : syracuseStep 1819655 = 2729483) B2729483
theorem B1819663 : Blo 1819611 1819663 := bstep (se 1 (by rfl) ⟨1364747, by rfl⟩ : syracuseStep 1819663 = 2729495) B2729495
theorem B1819707 : Blo 1819611 1819707 := bstep (se 1 (by rfl) ⟨1364780, by rfl⟩ : syracuseStep 1819707 = 2729561) B2729561
theorem B1819783 : Blo 1819611 1819783 := bstep (se 1 (by rfl) ⟨1364837, by rfl⟩ : syracuseStep 1819783 = 2729675) B2729675
theorem B4097159 : Blo 1819611 4097159 := bstep (se 1 (by rfl) ⟨3072869, by rfl⟩ : syracuseStep 4097159 = 6145739) B6145739
theorem B1819791 : Blo 1819611 1819791 := bstep (se 1 (by rfl) ⟨1364843, by rfl⟩ : syracuseStep 1819791 = 2729687) B2729687
theorem B1819835 : Blo 1819611 1819835 := bstep (se 1 (by rfl) ⟨1364876, by rfl⟩ : syracuseStep 1819835 = 2729753) B2729753
theorem B1819911 : Blo 1819611 1819911 := bstep (se 1 (by rfl) ⟨1364933, by rfl⟩ : syracuseStep 1819911 = 2729867) B2729867
theorem B1819919 : Blo 1819611 1819919 := bstep (se 1 (by rfl) ⟨1364939, by rfl⟩ : syracuseStep 1819919 = 2729879) B2729879
theorem B3073295 : Blo 1819611 3073295 := bstep (se 1 (by rfl) ⟨2304971, by rfl⟩ : syracuseStep 3073295 = 4609943) B4609943
theorem B2049295 : Blo 1819611 2049295 := bstep (se 1 (by rfl) ⟨1536971, by rfl⟩ : syracuseStep 2049295 = 3073943) B3073943
theorem B9217313 : Blo 1819611 9217313 := bstep (se 2 (by rfl) ⟨3456492, by rfl⟩ : syracuseStep 9217313 = 6912985) B6912985
theorem B1819963 : Blo 1819611 1819963 := bstep (se 1 (by rfl) ⟨1364972, by rfl⟩ : syracuseStep 1819963 = 2729945) B2729945
theorem B4097339 : Blo 1819611 4097339 := bstep (se 1 (by rfl) ⟨3073004, by rfl⟩ : syracuseStep 4097339 = 6146009) B6146009
theorem B1820039 : Blo 1819611 1820039 := bstep (se 1 (by rfl) ⟨1365029, by rfl⟩ : syracuseStep 1820039 = 2730059) B2730059
theorem B6145415 : Blo 1819611 6145415 := bstep (se 1 (by rfl) ⟨4609061, by rfl⟩ : syracuseStep 6145415 = 9218123) B9218123
theorem B1820047 : Blo 1819611 1820047 := bstep (se 1 (by rfl) ⟨1365035, by rfl⟩ : syracuseStep 1820047 = 2730071) B2730071
theorem B4097465 : Blo 1819611 4097465 := bstep (se 2 (by rfl) ⟨1536549, by rfl⟩ : syracuseStep 4097465 = 3073099) B3073099
theorem B1820091 : Blo 1819611 1820091 := bstep (se 1 (by rfl) ⟨1365068, by rfl⟩ : syracuseStep 1820091 = 2730137) B2730137
theorem B2729417 : Blo 1819611 2729417 := bstep (se 2 (by rfl) ⟨1023531, by rfl⟩ : syracuseStep 2729417 = 2047063) B2047063
theorem B5187017 : Blo 1819611 5187017 := bstep (se 2 (by rfl) ⟨1945131, by rfl⟩ : syracuseStep 5187017 = 3890263) B3890263
theorem B1820167 : Blo 1819611 1820167 := bstep (se 1 (by rfl) ⟨1365125, by rfl⟩ : syracuseStep 1820167 = 2730251) B2730251
theorem B1820175 : Blo 1819611 1820175 := bstep (se 1 (by rfl) ⟨1365131, by rfl⟩ : syracuseStep 1820175 = 2730263) B2730263
theorem B37381661 : Blo 1819611 37381661 := bstep (se 3 (by rfl) ⟨7009061, by rfl⟩ : syracuseStep 37381661 = 14018123) B14018123
theorem B2729531 : Blo 1819611 2729531 := bstep (se 1 (by rfl) ⟨2047148, by rfl⟩ : syracuseStep 2729531 = 4094297) B4094297
theorem B1820219 : Blo 1819611 1820219 := bstep (se 1 (by rfl) ⟨1365164, by rfl⟩ : syracuseStep 1820219 = 2730329) B2730329
theorem B5539387 : Blo 1819611 5539387 := bstep (se 1 (by rfl) ⟨4154540, by rfl⟩ : syracuseStep 5539387 = 8309081) B8309081
theorem B2729591 : Blo 1819611 2729591 := bstep (se 1 (by rfl) ⟨2047193, by rfl⟩ : syracuseStep 2729591 = 4094387) B4094387
theorem B1820295 : Blo 1819611 1820295 := bstep (se 1 (by rfl) ⟨1365221, by rfl⟩ : syracuseStep 1820295 = 2730443) B2730443
theorem B2729615 : Blo 1819611 2729615 := bstep (se 1 (by rfl) ⟨2047211, by rfl⟩ : syracuseStep 2729615 = 4094423) B4094423
theorem B1820303 : Blo 1819611 1820303 := bstep (se 1 (by rfl) ⟨1365227, by rfl⟩ : syracuseStep 1820303 = 2730455) B2730455
theorem B31540913 : Blo 1819611 31540913 := bstep (se 2 (by rfl) ⟨11827842, by rfl⟩ : syracuseStep 31540913 = 23655685) B23655685
theorem B2729657 : Blo 1819611 2729657 := bstep (se 2 (by rfl) ⟨1023621, by rfl⟩ : syracuseStep 2729657 = 2047243) B2047243
theorem B1943227 : Blo 1819611 1943227 := bstep (se 1 (by rfl) ⟨1457420, by rfl⟩ : syracuseStep 1943227 = 2914841) B2914841
theorem B1820347 : Blo 1819611 1820347 := bstep (se 1 (by rfl) ⟨1365260, by rfl⟩ : syracuseStep 1820347 = 2730521) B2730521
theorem B6145793 : Blo 1819611 6145793 := bstep (se 2 (by rfl) ⟨2304672, by rfl⟩ : syracuseStep 6145793 = 4609345) B4609345
theorem B2729735 : Blo 1819611 2729735 := bstep (se 1 (by rfl) ⟨2047301, by rfl⟩ : syracuseStep 2729735 = 4094603) B4094603
theorem B1820423 : Blo 1819611 1820423 := bstep (se 1 (by rfl) ⟨1365317, by rfl⟩ : syracuseStep 1820423 = 2730635) B2730635
theorem B1820431 : Blo 1819611 1820431 := bstep (se 1 (by rfl) ⟨1365323, by rfl⟩ : syracuseStep 1820431 = 2730647) B2730647
theorem B4097807 : Blo 1819611 4097807 := bstep (se 1 (by rfl) ⟨3073355, by rfl⟩ : syracuseStep 4097807 = 6146711) B6146711
theorem B4097825 : Blo 1819611 4097825 := bstep (se 2 (by rfl) ⟨1536684, by rfl⟩ : syracuseStep 4097825 = 3073369) B3073369
theorem B2729771 : Blo 1819611 2729771 := bstep (se 1 (by rfl) ⟨2047328, by rfl⟩ : syracuseStep 2729771 = 4094657) B4094657
theorem B3073835 : Blo 1819611 3073835 := bstep (se 1 (by rfl) ⟨2305376, by rfl⟩ : syracuseStep 3073835 = 4610753) B4610753
theorem B1820475 : Blo 1819611 1820475 := bstep (se 1 (by rfl) ⟨1365356, by rfl⟩ : syracuseStep 1820475 = 2730713) B2730713
theorem B2729801 : Blo 1819611 2729801 := bstep (se 2 (by rfl) ⟨1023675, by rfl⟩ : syracuseStep 2729801 = 2047351) B2047351
theorem B4736855 : Blo 1819611 4736855 := bstep (se 1 (by rfl) ⟨3552641, by rfl⟩ : syracuseStep 4736855 = 7105283) B7105283
theorem B19687283 : Blo 1819611 19687283 := bstep (se 1 (by rfl) ⟨14765462, by rfl⟩ : syracuseStep 19687283 = 29530925) B29530925
theorem B1820551 : Blo 1819611 1820551 := bstep (se 1 (by rfl) ⟨1365413, by rfl⟩ : syracuseStep 1820551 = 2730827) B2730827
theorem B1820559 : Blo 1819611 1820559 := bstep (se 1 (by rfl) ⟨1365419, by rfl⟩ : syracuseStep 1820559 = 2730839) B2730839
theorem B2729915 : Blo 1819611 2729915 := bstep (se 1 (by rfl) ⟨2047436, by rfl⟩ : syracuseStep 2729915 = 4094873) B4094873
theorem B1820603 : Blo 1819611 1820603 := bstep (se 1 (by rfl) ⟨1365452, by rfl⟩ : syracuseStep 1820603 = 2730905) B2730905
theorem B2729975 : Blo 1819611 2729975 := bstep (se 1 (by rfl) ⟨2047481, by rfl⟩ : syracuseStep 2729975 = 4094963) B4094963
theorem B10373123 : Blo 1819611 10373123 := bstep (se 1 (by rfl) ⟨7779842, by rfl⟩ : syracuseStep 10373123 = 15559685) B15559685
theorem B1820679 : Blo 1819611 1820679 := bstep (se 1 (by rfl) ⟨1365509, by rfl⟩ : syracuseStep 1820679 = 2731019) B2731019
theorem B2729999 : Blo 1819611 2729999 := bstep (se 1 (by rfl) ⟨2047499, by rfl⟩ : syracuseStep 2729999 = 4094999) B4094999
theorem B1820687 : Blo 1819611 1820687 := bstep (se 1 (by rfl) ⟨1365515, by rfl⟩ : syracuseStep 1820687 = 2731031) B2731031
theorem B2730041 : Blo 1819611 2730041 := bstep (se 2 (by rfl) ⟨1023765, by rfl⟩ : syracuseStep 2730041 = 2047531) B2047531
theorem B1820731 : Blo 1819611 1820731 := bstep (se 1 (by rfl) ⟨1365548, by rfl⟩ : syracuseStep 1820731 = 2731097) B2731097
theorem B4376663 : Blo 1819611 4376663 := bstep (se 1 (by rfl) ⟨3282497, by rfl⟩ : syracuseStep 4376663 = 6564995) B6564995
theorem B4098167 : Blo 1819611 4098167 := bstep (se 1 (by rfl) ⟨3073625, by rfl⟩ : syracuseStep 4098167 = 6147251) B6147251
theorem B2730119 : Blo 1819611 2730119 := bstep (se 1 (by rfl) ⟨2047589, by rfl⟩ : syracuseStep 2730119 = 4095179) B4095179
theorem B1820807 : Blo 1819611 1820807 := bstep (se 1 (by rfl) ⟨1365605, by rfl⟩ : syracuseStep 1820807 = 2731211) B2731211
theorem B1820815 : Blo 1819611 1820815 := bstep (se 1 (by rfl) ⟨1365611, by rfl⟩ : syracuseStep 1820815 = 2731223) B2731223
theorem B4606105 : Blo 1819611 4606105 := bstep (se 2 (by rfl) ⟨1727289, by rfl⟩ : syracuseStep 4606105 = 3454579) B3454579
theorem B2730155 : Blo 1819611 2730155 := bstep (se 1 (by rfl) ⟨2047616, by rfl⟩ : syracuseStep 2730155 = 4095233) B4095233
theorem B1820859 : Blo 1819611 1820859 := bstep (se 1 (by rfl) ⟨1365644, by rfl⟩ : syracuseStep 1820859 = 2731289) B2731289
theorem B2730185 : Blo 1819611 2730185 := bstep (se 2 (by rfl) ⟨1023819, by rfl⟩ : syracuseStep 2730185 = 2047639) B2047639
theorem B9218285 : Blo 1819611 9218285 := bstep (se 3 (by rfl) ⟨1728428, by rfl⟩ : syracuseStep 9218285 = 3456857) B3456857
theorem B1820935 : Blo 1819611 1820935 := bstep (se 1 (by rfl) ⟨1365701, by rfl⟩ : syracuseStep 1820935 = 2731403) B2731403
theorem B1820943 : Blo 1819611 1820943 := bstep (se 1 (by rfl) ⟨1365707, by rfl⟩ : syracuseStep 1820943 = 2731415) B2731415
theorem B4098347 : Blo 1819611 4098347 := bstep (se 1 (by rfl) ⟨3073760, by rfl⟩ : syracuseStep 4098347 = 6147521) B6147521
theorem B4606267 : Blo 1819611 4606267 := bstep (se 1 (by rfl) ⟨3454700, by rfl⟩ : syracuseStep 4606267 = 6909401) B6909401
theorem B2730299 : Blo 1819611 2730299 := bstep (se 1 (by rfl) ⟨2047724, by rfl⟩ : syracuseStep 2730299 = 4095449) B4095449
theorem B1820987 : Blo 1819611 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B2730359 : Blo 1819611 2730359 := bstep (se 1 (by rfl) ⟨2047769, by rfl⟩ : syracuseStep 2730359 = 4095539) B4095539
theorem B1821063 : Blo 1819611 1821063 := bstep (se 1 (by rfl) ⟨1365797, by rfl⟩ : syracuseStep 1821063 = 2731595) B2731595
theorem B2730383 : Blo 1819611 2730383 := bstep (se 1 (by rfl) ⟨2047787, by rfl⟩ : syracuseStep 2730383 = 4095575) B4095575
theorem B1821071 : Blo 1819611 1821071 := bstep (se 1 (by rfl) ⟨1365803, by rfl⟩ : syracuseStep 1821071 = 2731607) B2731607
theorem B2730425 : Blo 1819611 2730425 := bstep (se 2 (by rfl) ⟨1023909, by rfl⟩ : syracuseStep 2730425 = 2047819) B2047819
theorem B1821115 : Blo 1819611 1821115 := bstep (se 1 (by rfl) ⟨1365836, by rfl⟩ : syracuseStep 1821115 = 2731673) B2731673
theorem B4606409 : Blo 1819611 4606409 := bstep (se 2 (by rfl) ⟨1727403, by rfl⟩ : syracuseStep 4606409 = 3454807) B3454807
theorem B10373579 : Blo 1819611 10373579 := bstep (se 1 (by rfl) ⟨7780184, by rfl⟩ : syracuseStep 10373579 = 15560369) B15560369
theorem B2730503 : Blo 1819611 2730503 := bstep (se 1 (by rfl) ⟨2047877, by rfl⟩ : syracuseStep 2730503 = 4095755) B4095755
theorem B1821191 : Blo 1819611 1821191 := bstep (se 1 (by rfl) ⟨1365893, by rfl⟩ : syracuseStep 1821191 = 2731787) B2731787
theorem B1821199 : Blo 1819611 1821199 := bstep (se 1 (by rfl) ⟨1365899, by rfl⟩ : syracuseStep 1821199 = 2731799) B2731799
theorem B5835293 : Blo 1819611 5835293 := bstep (se 3 (by rfl) ⟨1094117, by rfl⟩ : syracuseStep 5835293 = 2188235) B2188235
theorem B2730539 : Blo 1819611 2730539 := bstep (se 1 (by rfl) ⟨2047904, by rfl⟩ : syracuseStep 2730539 = 4095809) B4095809
theorem B6146603 : Blo 1819611 6146603 := bstep (se 1 (by rfl) ⟨4609952, by rfl⟩ : syracuseStep 6146603 = 9219905) B9219905
theorem B1821243 : Blo 1819611 1821243 := bstep (se 1 (by rfl) ⟨1365932, by rfl⟩ : syracuseStep 1821243 = 2731865) B2731865
theorem B20728385 : Blo 1819611 20728385 := bstep (se 2 (by rfl) ⟨7773144, by rfl⟩ : syracuseStep 20728385 = 15546289) B15546289
theorem B12462659 : Blo 1819611 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B2730569 : Blo 1819611 2730569 := bstep (se 2 (by rfl) ⟨1023963, by rfl⟩ : syracuseStep 2730569 = 2047927) B2047927
theorem B1821319 : Blo 1819611 1821319 := bstep (se 1 (by rfl) ⟨1365989, by rfl⟩ : syracuseStep 1821319 = 2731979) B2731979
theorem B1821327 : Blo 1819611 1821327 := bstep (se 1 (by rfl) ⟨1365995, by rfl⟩ : syracuseStep 1821327 = 2731991) B2731991
theorem B2075323 : Blo 1819611 2075323 := bstep (se 1 (by rfl) ⟨1556492, by rfl⟩ : syracuseStep 2075323 = 3112985) B3112985
theorem B2730683 : Blo 1819611 2730683 := bstep (se 1 (by rfl) ⟨2048012, by rfl⟩ : syracuseStep 2730683 = 4096025) B4096025
theorem B1821371 : Blo 1819611 1821371 := bstep (se 1 (by rfl) ⟨1366028, by rfl⟩ : syracuseStep 1821371 = 2732057) B2732057
theorem B2730743 : Blo 1819611 2730743 := bstep (se 1 (by rfl) ⟨2048057, by rfl⟩ : syracuseStep 2730743 = 4096115) B4096115
theorem B1821447 : Blo 1819611 1821447 := bstep (se 1 (by rfl) ⟨1366085, by rfl⟩ : syracuseStep 1821447 = 2732171) B2732171
theorem B2730767 : Blo 1819611 2730767 := bstep (se 1 (by rfl) ⟨2048075, by rfl⟩ : syracuseStep 2730767 = 4096151) B4096151
theorem B1821455 : Blo 1819611 1821455 := bstep (se 1 (by rfl) ⟨1366091, by rfl⟩ : syracuseStep 1821455 = 2732183) B2732183
theorem B4606753 : Blo 1819611 4606753 := bstep (se 2 (by rfl) ⟨1727532, by rfl⟩ : syracuseStep 4606753 = 3455065) B3455065
theorem B31591205 : Blo 1819611 31591205 := bstep (se 4 (by rfl) ⟨2961675, by rfl⟩ : syracuseStep 31591205 = 5923351) B5923351
theorem B2730809 : Blo 1819611 2730809 := bstep (se 2 (by rfl) ⟨1024053, by rfl⟩ : syracuseStep 2730809 = 2048107) B2048107
theorem B1821499 : Blo 1819611 1821499 := bstep (se 1 (by rfl) ⟨1366124, by rfl⟩ : syracuseStep 1821499 = 2732249) B2732249
theorem B2591561 : Blo 1819611 2591561 := bstep (se 2 (by rfl) ⟨971835, by rfl⟩ : syracuseStep 2591561 = 1943671) B1943671
theorem B2730887 : Blo 1819611 2730887 := bstep (se 1 (by rfl) ⟨2048165, by rfl⟩ : syracuseStep 2730887 = 4096331) B4096331
theorem B1821575 : Blo 1819611 1821575 := bstep (se 1 (by rfl) ⟨1366181, by rfl⟩ : syracuseStep 1821575 = 2732363) B2732363
theorem B1821583 : Blo 1819611 1821583 := bstep (se 1 (by rfl) ⟨1366187, by rfl⟩ : syracuseStep 1821583 = 2732375) B2732375
theorem B21015449 : Blo 1819611 21015449 := bstep (se 2 (by rfl) ⟨7880793, by rfl⟩ : syracuseStep 21015449 = 15761587) B15761587
theorem B2730923 : Blo 1819611 2730923 := bstep (se 1 (by rfl) ⟨2048192, by rfl⟩ : syracuseStep 2730923 = 4096385) B4096385
theorem B2730953 : Blo 1819611 2730953 := bstep (se 2 (by rfl) ⟨1024107, by rfl⟩ : syracuseStep 2730953 = 2048215) B2048215
theorem B9219095 : Blo 1819611 9219095 := bstep (se 1 (by rfl) ⟨6914321, by rfl⟩ : syracuseStep 9219095 = 13828643) B13828643
theorem B2731067 : Blo 1819611 2731067 := bstep (se 1 (by rfl) ⟨2048300, by rfl⟩ : syracuseStep 2731067 = 4096601) B4096601
theorem B7777367 : Blo 1819611 7777367 := bstep (se 1 (by rfl) ⟨5833025, by rfl⟩ : syracuseStep 7777367 = 11666051) B11666051
theorem B2731127 : Blo 1819611 2731127 := bstep (se 1 (by rfl) ⟨2048345, by rfl⟩ : syracuseStep 2731127 = 4096691) B4096691
theorem B10374263 : Blo 1819611 10374263 := bstep (se 1 (by rfl) ⟨7780697, by rfl⟩ : syracuseStep 10374263 = 15561395) B15561395
theorem B15551621 : Blo 1819611 15551621 := bstep (se 4 (by rfl) ⟨1457964, by rfl⟩ : syracuseStep 15551621 = 2915929) B2915929
theorem B2731151 : Blo 1819611 2731151 := bstep (se 1 (by rfl) ⟨2048363, by rfl⟩ : syracuseStep 2731151 = 4096727) B4096727
theorem B19958957 : Blo 1819611 19958957 := bstep (se 3 (by rfl) ⟨3742304, by rfl⟩ : syracuseStep 19958957 = 7484609) B7484609
theorem B3886265 : Blo 1819611 3886265 := bstep (se 2 (by rfl) ⟨1457349, by rfl⟩ : syracuseStep 3886265 = 2914699) B2914699
theorem B2731193 : Blo 1819611 2731193 := bstep (se 2 (by rfl) ⟨1024197, by rfl⟩ : syracuseStep 2731193 = 2048395) B2048395
theorem B14757065 : Blo 1819611 14757065 := bstep (se 2 (by rfl) ⟨5533899, by rfl⟩ : syracuseStep 14757065 = 11067799) B11067799
theorem B2731271 : Blo 1819611 2731271 := bstep (se 1 (by rfl) ⟨2048453, by rfl⟩ : syracuseStep 2731271 = 4096907) B4096907
theorem B2731307 : Blo 1819611 2731307 := bstep (se 1 (by rfl) ⟨2048480, by rfl⟩ : syracuseStep 2731307 = 4096961) B4096961
theorem B2731337 : Blo 1819611 2731337 := bstep (se 2 (by rfl) ⟨1024251, by rfl⟩ : syracuseStep 2731337 = 2048503) B2048503
theorem B179563877 : Blo 1819611 179563877 := bstep (se 4 (by rfl) ⟨16834113, by rfl⟩ : syracuseStep 179563877 = 33668227) B33668227
theorem B4607351 : Blo 1819611 4607351 := bstep (se 1 (by rfl) ⟨3455513, by rfl⟩ : syracuseStep 4607351 = 6911027) B6911027
theorem B2592119 : Blo 1819611 2592119 := bstep (se 1 (by rfl) ⟨1944089, by rfl⟩ : syracuseStep 2592119 = 3888179) B3888179
theorem B22457735 : Blo 1819611 22457735 := bstep (se 1 (by rfl) ⟨16843301, by rfl⟩ : syracuseStep 22457735 = 33686603) B33686603
theorem B13831559 : Blo 1819611 13831559 := bstep (se 1 (by rfl) ⟨10373669, by rfl⟩ : syracuseStep 13831559 = 20747339) B20747339
theorem B2731451 : Blo 1819611 2731451 := bstep (se 1 (by rfl) ⟨2048588, by rfl⟩ : syracuseStep 2731451 = 4097177) B4097177
theorem B2731511 : Blo 1819611 2731511 := bstep (se 1 (by rfl) ⟨2048633, by rfl⟩ : syracuseStep 2731511 = 4097267) B4097267
theorem B2731535 : Blo 1819611 2731535 := bstep (se 1 (by rfl) ⟨2048651, by rfl⟩ : syracuseStep 2731535 = 4097303) B4097303
theorem B2731577 : Blo 1819611 2731577 := bstep (se 2 (by rfl) ⟨1024341, by rfl⟩ : syracuseStep 2731577 = 2048683) B2048683
theorem B2731655 : Blo 1819611 2731655 := bstep (se 1 (by rfl) ⟨2048741, by rfl⟩ : syracuseStep 2731655 = 4097483) B4097483
theorem B2592427 : Blo 1819611 2592427 := bstep (se 1 (by rfl) ⟨1944320, by rfl⟩ : syracuseStep 2592427 = 3888641) B3888641
theorem B2731691 : Blo 1819611 2731691 := bstep (se 1 (by rfl) ⟨2048768, by rfl⟩ : syracuseStep 2731691 = 4097537) B4097537
theorem B3739337 : Blo 1819611 3739337 := bstep (se 2 (by rfl) ⟨1402251, by rfl⟩ : syracuseStep 3739337 = 2804503) B2804503
theorem B2731721 : Blo 1819611 2731721 := bstep (se 2 (by rfl) ⟨1024395, by rfl⟩ : syracuseStep 2731721 = 2048791) B2048791
theorem B2731835 : Blo 1819611 2731835 := bstep (se 1 (by rfl) ⟨2048876, by rfl⟩ : syracuseStep 2731835 = 4097753) B4097753
theorem B6147899 : Blo 1819611 6147899 := bstep (se 1 (by rfl) ⟨4610924, by rfl⟩ : syracuseStep 6147899 = 9221849) B9221849
theorem B2731895 : Blo 1819611 2731895 := bstep (se 1 (by rfl) ⟨2048921, by rfl⟩ : syracuseStep 2731895 = 4097843) B4097843
theorem B2731919 : Blo 1819611 2731919 := bstep (se 1 (by rfl) ⟨2048939, by rfl⟩ : syracuseStep 2731919 = 4097879) B4097879
theorem B2731961 : Blo 1819611 2731961 := bstep (se 2 (by rfl) ⟨1024485, by rfl⟩ : syracuseStep 2731961 = 2048971) B2048971
theorem B2732039 : Blo 1819611 2732039 := bstep (se 1 (by rfl) ⟨2049029, by rfl⟩ : syracuseStep 2732039 = 4098059) B4098059
theorem B3887119 : Blo 1819611 3887119 := bstep (se 1 (by rfl) ⟨2915339, by rfl⟩ : syracuseStep 3887119 = 5830679) B5830679
theorem B2732075 : Blo 1819611 2732075 := bstep (se 1 (by rfl) ⟨2049056, by rfl⟩ : syracuseStep 2732075 = 4098113) B4098113
theorem B2732105 : Blo 1819611 2732105 := bstep (se 2 (by rfl) ⟨1024539, by rfl⟩ : syracuseStep 2732105 = 2049079) B2049079
theorem B2592911 : Blo 1819611 2592911 := bstep (se 1 (by rfl) ⟨1944683, by rfl⟩ : syracuseStep 2592911 = 3889367) B3889367
theorem B2732219 : Blo 1819611 2732219 := bstep (se 1 (by rfl) ⟨2049164, by rfl⟩ : syracuseStep 2732219 = 4098329) B4098329
theorem B5181641 : Blo 1819611 5181641 := bstep (se 2 (by rfl) ⟨1943115, by rfl⟩ : syracuseStep 5181641 = 3886231) B3886231
theorem B11669741 : Blo 1819611 11669741 := bstep (se 3 (by rfl) ⟨2188076, by rfl⟩ : syracuseStep 11669741 = 4376153) B4376153
theorem B2732279 : Blo 1819611 2732279 := bstep (se 1 (by rfl) ⟨2049209, by rfl⟩ : syracuseStep 2732279 = 4098419) B4098419
theorem B2732303 : Blo 1819611 2732303 := bstep (se 1 (by rfl) ⟨2049227, by rfl⟩ : syracuseStep 2732303 = 4098455) B4098455
theorem B2732345 : Blo 1819611 2732345 := bstep (se 2 (by rfl) ⟨1024629, by rfl⟩ : syracuseStep 2732345 = 2049259) B2049259
theorem B10367291 : Blo 1819611 10367291 := bstep (se 1 (by rfl) ⟨7775468, by rfl⟩ : syracuseStep 10367291 = 15550937) B15550937
theorem B6910343 : Blo 1819611 6910343 := bstep (se 1 (by rfl) ⟨5182757, by rfl⟩ : syracuseStep 6910343 = 10365515) B10365515
theorem B9843079 : Blo 1819611 9843079 := bstep (se 1 (by rfl) ⟨7382309, by rfl⟩ : syracuseStep 9843079 = 14764619) B14764619
theorem B9343441 : Blo 1819611 9343441 := bstep (se 2 (by rfl) ⟨3503790, by rfl⟩ : syracuseStep 9343441 = 7007581) B7007581
theorem B11669969 : Blo 1819611 11669969 := bstep (se 2 (by rfl) ⟨4376238, by rfl⟩ : syracuseStep 11669969 = 8752477) B8752477
theorem B5181995 : Blo 1819611 5181995 := bstep (se 1 (by rfl) ⟨3886496, by rfl⟩ : syracuseStep 5181995 = 7772993) B7772993
theorem B109359659 : Blo 1819611 109359659 := bstep (se 1 (by rfl) ⟨82019744, by rfl⟩ : syracuseStep 109359659 = 164039489) B164039489
theorem B4608647 : Blo 1819611 4608647 := bstep (se 1 (by rfl) ⟨3456485, by rfl⟩ : syracuseStep 4608647 = 6912971) B6912971
theorem B4608697 : Blo 1819611 4608697 := bstep (se 2 (by rfl) ⟨1728261, by rfl⟩ : syracuseStep 4608697 = 3456523) B3456523
theorem B2626447 : Blo 1819611 2626447 := bstep (se 1 (by rfl) ⟨1969835, by rfl⟩ : syracuseStep 2626447 = 3939671) B3939671
theorem B14398361 : Blo 1819611 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B5182393 : Blo 1819611 5182393 := bstep (se 2 (by rfl) ⟨1943397, by rfl⟩ : syracuseStep 5182393 = 3886795) B3886795
theorem B9212939 : Blo 1819611 9212939 := bstep (se 1 (by rfl) ⟨6909704, by rfl⟩ : syracuseStep 9212939 = 13819409) B13819409
theorem B9213101 : Blo 1819611 9213101 := bstep (se 3 (by rfl) ⟨1727456, by rfl⟩ : syracuseStep 9213101 = 3454913) B3454913
theorem B4609295 : Blo 1819611 4609295 := bstep (se 1 (by rfl) ⟨3456971, by rfl⟩ : syracuseStep 4609295 = 6913943) B6913943
theorem B3282209 : Blo 1819611 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B21018041 : Blo 1819611 21018041 := bstep (se 2 (by rfl) ⟨7881765, by rfl⟩ : syracuseStep 21018041 = 15763531) B15763531
theorem B6141527 : Blo 1819611 6141527 := bstep (se 1 (by rfl) ⟨4606145, by rfl⟩ : syracuseStep 6141527 = 9212291) B9212291
theorem B10368749 : Blo 1819611 10368749 := bstep (se 3 (by rfl) ⟨1944140, by rfl⟩ : syracuseStep 10368749 = 3888281) B3888281
theorem B4609993 : Blo 1819611 4609993 := bstep (se 2 (by rfl) ⟨1728747, by rfl⟩ : syracuseStep 4609993 = 3457495) B3457495
theorem B2955323 : Blo 1819611 2955323 := bstep (se 1 (by rfl) ⟨2216492, by rfl⟩ : syracuseStep 2955323 = 4432985) B4432985
theorem B6142013 : Blo 1819611 6142013 := bstep (se 3 (by rfl) ⟨1151627, by rfl⟩ : syracuseStep 6142013 = 2303255) B2303255
theorem B6559805 : Blo 1819611 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B4610135 : Blo 1819611 4610135 := bstep (se 1 (by rfl) ⟨3457601, by rfl⟩ : syracuseStep 4610135 = 6915203) B6915203
theorem B3455111 : Blo 1819611 3455111 := bstep (se 1 (by rfl) ⟨2591333, by rfl⟩ : syracuseStep 3455111 = 5182667) B5182667
theorem B5183635 : Blo 1819611 5183635 := bstep (se 1 (by rfl) ⟨3887726, by rfl⟩ : syracuseStep 5183635 = 7775453) B7775453
theorem B3692729 : Blo 1819611 3692729 := bstep (se 2 (by rfl) ⟨1384773, by rfl⟩ : syracuseStep 3692729 = 2769547) B2769547
theorem B4094153 : Blo 1819611 4094153 := bstep (se 2 (by rfl) ⟨1535307, by rfl⟩ : syracuseStep 4094153 = 3070615) B3070615
theorem B42637661 : Blo 1819611 42637661 := bstep (se 3 (by rfl) ⟨7994561, by rfl⟩ : syracuseStep 42637661 = 15989123) B15989123
theorem B15555037 : Blo 1819611 15555037 := bstep (se 3 (by rfl) ⟨2916569, by rfl⟩ : syracuseStep 15555037 = 5833139) B5833139
theorem B46635587 : Blo 1819611 46635587 := bstep (se 1 (by rfl) ⟨34976690, by rfl⟩ : syracuseStep 46635587 = 69953381) B69953381
theorem B3324563 : Blo 1819611 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B3455635 : Blo 1819611 3455635 := bstep (se 1 (by rfl) ⟨2591726, by rfl⟩ : syracuseStep 3455635 = 5183453) B5183453
theorem B3070649 : Blo 1819611 3070649 := bstep (se 2 (by rfl) ⟨1151493, by rfl⟩ : syracuseStep 3070649 = 2302987) B2302987
theorem B9214721 : Blo 1819611 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B17488655 : Blo 1819611 17488655 := bstep (se 1 (by rfl) ⟨13116491, by rfl⟩ : syracuseStep 17488655 = 26232983) B26232983
theorem B7773043 : Blo 1819611 7773043 := bstep (se 1 (by rfl) ⟨5829782, by rfl⟩ : syracuseStep 7773043 = 11659565) B11659565
theorem B4094855 : Blo 1819611 4094855 := bstep (se 1 (by rfl) ⟨3071141, by rfl⟩ : syracuseStep 4094855 = 6142283) B6142283
theorem B5913479 : Blo 1819611 5913479 := bstep (se 1 (by rfl) ⟨4435109, by rfl⟩ : syracuseStep 5913479 = 8870219) B8870219
theorem B2767879 : Blo 1819611 2767879 := bstep (se 1 (by rfl) ⟨2075909, by rfl⟩ : syracuseStep 2767879 = 4151819) B4151819
theorem B4095035 : Blo 1819611 4095035 := bstep (se 1 (by rfl) ⟨3071276, by rfl⟩ : syracuseStep 4095035 = 6142553) B6142553
theorem B17505341 : Blo 1819611 17505341 := bstep (se 3 (by rfl) ⟨3282251, by rfl⟩ : syracuseStep 17505341 = 6564503) B6564503
theorem B4095161 : Blo 1819611 4095161 := bstep (se 2 (by rfl) ⟨1535685, by rfl⟩ : syracuseStep 4095161 = 3071371) B3071371
theorem B106421525 : Blo 1819611 106421525 := bstep (se 6 (by rfl) ⟨2494254, by rfl⟩ : syracuseStep 106421525 = 4988509) B4988509
theorem B4373875 : Blo 1819611 4373875 := bstep (se 1 (by rfl) ⟨3280406, by rfl⟩ : syracuseStep 4373875 = 6560813) B6560813
theorem B3071351 : Blo 1819611 3071351 := bstep (se 1 (by rfl) ⟨2303513, by rfl⟩ : syracuseStep 3071351 = 4607027) B4607027
theorem B20741507 : Blo 1819611 20741507 := bstep (se 1 (by rfl) ⟨15556130, by rfl⟩ : syracuseStep 20741507 = 31112261) B31112261
theorem B6143417 : Blo 1819611 6143417 := bstep (se 2 (by rfl) ⟨2303781, by rfl⟩ : syracuseStep 6143417 = 4607563) B4607563
theorem B6561233 : Blo 1819611 6561233 := bstep (se 2 (by rfl) ⟨2460462, by rfl⟩ : syracuseStep 6561233 = 4920925) B4920925
theorem B2047495 : Blo 1819611 2047495 := bstep (se 1 (by rfl) ⟨1535621, by rfl⟩ : syracuseStep 2047495 = 3071243) B3071243
theorem B1998343 : Blo 1819611 1998343 := bstep (se 1 (by rfl) ⟨1498757, by rfl⟩ : syracuseStep 1998343 = 2997515) B2997515
theorem B7380491 : Blo 1819611 7380491 := bstep (se 1 (by rfl) ⟨5535368, by rfl⟩ : syracuseStep 7380491 = 11070737) B11070737
theorem B4095503 : Blo 1819611 4095503 := bstep (se 1 (by rfl) ⟨3071627, by rfl⟩ : syracuseStep 4095503 = 6143255) B6143255
theorem B4095521 : Blo 1819611 4095521 := bstep (se 2 (by rfl) ⟨1535820, by rfl⟩ : syracuseStep 4095521 = 3071641) B3071641
theorem B9215531 : Blo 1819611 9215531 := bstep (se 1 (by rfl) ⟨6911648, by rfl⟩ : syracuseStep 9215531 = 13823297) B13823297
theorem B7200323 : Blo 1819611 7200323 := bstep (se 1 (by rfl) ⟨5400242, by rfl⟩ : syracuseStep 7200323 = 10800485) B10800485
theorem B13672003 : Blo 1819611 13672003 := bstep (se 1 (by rfl) ⟨10254002, by rfl⟩ : syracuseStep 13672003 = 20508005) B20508005
theorem B2047675 : Blo 1819611 2047675 := bstep (se 1 (by rfl) ⟨1535756, by rfl⟩ : syracuseStep 2047675 = 3071513) B3071513
theorem B5832449 : Blo 1819611 5832449 := bstep (se 2 (by rfl) ⟨2187168, by rfl⟩ : syracuseStep 5832449 = 4374337) B4374337
theorem B5185309 : Blo 1819611 5185309 := bstep (se 3 (by rfl) ⟨972245, by rfl⟩ : syracuseStep 5185309 = 1944491) B1944491
theorem B3071803 : Blo 1819611 3071803 := bstep (se 1 (by rfl) ⟨2303852, by rfl⟩ : syracuseStep 3071803 = 4607705) B4607705
theorem B3456827 : Blo 1819611 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B5185367 : Blo 1819611 5185367 := bstep (se 1 (by rfl) ⟨3889025, by rfl⟩ : syracuseStep 5185367 = 7778051) B7778051
theorem B4095863 : Blo 1819611 4095863 := bstep (se 1 (by rfl) ⟨3071897, by rfl⟩ : syracuseStep 4095863 = 6143795) B6143795
theorem B3071945 : Blo 1819611 3071945 := bstep (se 2 (by rfl) ⟨1151979, by rfl⟩ : syracuseStep 3071945 = 2303959) B2303959
theorem B12451843 : Blo 1819611 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B4096007 : Blo 1819611 4096007 := bstep (se 1 (by rfl) ⟨3072005, by rfl⟩ : syracuseStep 4096007 = 6144011) B6144011
theorem B5832719 : Blo 1819611 5832719 := bstep (se 1 (by rfl) ⟨4374539, by rfl⟩ : syracuseStep 5832719 = 8749079) B8749079
theorem B6225977 : Blo 1819611 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B4096079 : Blo 1819611 4096079 := bstep (se 1 (by rfl) ⟨3072059, by rfl⟩ : syracuseStep 4096079 = 6144119) B6144119
theorem B7880861 : Blo 1819611 7880861 := bstep (se 3 (by rfl) ⟨1477661, by rfl⟩ : syracuseStep 7880861 = 2955323) B2955323
theorem B12452147 : Blo 1819611 12452147 := bstep (se 1 (by rfl) ⟨9339110, by rfl⟩ : syracuseStep 12452147 = 18678221) B18678221
theorem B6914429 : Blo 1819611 6914429 := bstep (se 3 (by rfl) ⟨1296455, by rfl⟩ : syracuseStep 6914429 = 2592911) B2592911
theorem B3072431 : Blo 1819611 3072431 := bstep (se 1 (by rfl) ⟨2304323, by rfl⟩ : syracuseStep 3072431 = 4608647) B4608647
theorem B2048431 : Blo 1819611 2048431 := bstep (se 1 (by rfl) ⟨1536323, by rfl⟩ : syracuseStep 2048431 = 3072647) B3072647
theorem B4096475 : Blo 1819611 4096475 := bstep (se 1 (by rfl) ⟨3072356, by rfl⟩ : syracuseStep 4096475 = 6144713) B6144713
theorem B10363373 : Blo 1819611 10363373 := bstep (se 3 (by rfl) ⟨1943132, by rfl⟩ : syracuseStep 10363373 = 3886265) B3886265
theorem B9847277 : Blo 1819611 9847277 := bstep (se 3 (by rfl) ⟨1846364, by rfl⟩ : syracuseStep 9847277 = 3692729) B3692729
theorem B13124105 : Blo 1819611 13124105 := bstep (se 2 (by rfl) ⟨4921539, by rfl⟩ : syracuseStep 13124105 = 9843079) B9843079
theorem B6144551 : Blo 1819611 6144551 := bstep (se 1 (by rfl) ⟨4608413, by rfl⟩ : syracuseStep 6144551 = 9216827) B9216827
theorem B6144659 : Blo 1819611 6144659 := bstep (se 1 (by rfl) ⟨4608494, by rfl⟩ : syracuseStep 6144659 = 9216989) B9216989
theorem B75776663 : Blo 1819611 75776663 := bstep (se 1 (by rfl) ⟨56832497, by rfl⟩ : syracuseStep 75776663 = 113664995) B113664995
theorem B3072863 : Blo 1819611 3072863 := bstep (se 1 (by rfl) ⟨2304647, by rfl⟩ : syracuseStep 3072863 = 4609295) B4609295
theorem B2048863 : Blo 1819611 2048863 := bstep (se 1 (by rfl) ⟨1536647, by rfl⟩ : syracuseStep 2048863 = 3073295) B3073295
theorem B6144875 : Blo 1819611 6144875 := bstep (se 1 (by rfl) ⟨4608656, by rfl⟩ : syracuseStep 6144875 = 9217313) B9217313
theorem B2188139 : Blo 1819611 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B6144929 : Blo 1819611 6144929 := bstep (se 2 (by rfl) ⟨2304348, by rfl⟩ : syracuseStep 6144929 = 4608697) B4608697
theorem B4096943 : Blo 1819611 4096943 := bstep (se 1 (by rfl) ⟨3072707, by rfl⟩ : syracuseStep 4096943 = 6145415) B6145415
theorem B1819611 : Blo 1819611 1819611 := bstep (se 1 (by rfl) ⟨1364708, by rfl⟩ : syracuseStep 1819611 = 2729417) B2729417
theorem B24921107 : Blo 1819611 24921107 := bstep (se 1 (by rfl) ⟨18690830, by rfl⟩ : syracuseStep 24921107 = 37381661) B37381661
theorem B1819687 : Blo 1819611 1819687 := bstep (se 1 (by rfl) ⟨1364765, by rfl⟩ : syracuseStep 1819687 = 2729531) B2729531
theorem B1819727 : Blo 1819611 1819727 := bstep (se 1 (by rfl) ⟨1364795, by rfl⟩ : syracuseStep 1819727 = 2729591) B2729591
theorem B1819743 : Blo 1819611 1819743 := bstep (se 1 (by rfl) ⟨1364807, by rfl⟩ : syracuseStep 1819743 = 2729615) B2729615
theorem B1819771 : Blo 1819611 1819771 := bstep (se 1 (by rfl) ⟨1364828, by rfl⟩ : syracuseStep 1819771 = 2729657) B2729657
theorem B10364057 : Blo 1819611 10364057 := bstep (se 2 (by rfl) ⟨3886521, by rfl⟩ : syracuseStep 10364057 = 7773043) B7773043
theorem B4097195 : Blo 1819611 4097195 := bstep (se 1 (by rfl) ⟨3072896, by rfl⟩ : syracuseStep 4097195 = 6145793) B6145793
theorem B1819823 : Blo 1819611 1819823 := bstep (se 1 (by rfl) ⟨1364867, by rfl⟩ : syracuseStep 1819823 = 2729735) B2729735
theorem B1819847 : Blo 1819611 1819847 := bstep (se 1 (by rfl) ⟨1364885, by rfl⟩ : syracuseStep 1819847 = 2729771) B2729771
theorem B2049223 : Blo 1819611 2049223 := bstep (se 1 (by rfl) ⟨1536917, by rfl⟩ : syracuseStep 2049223 = 3073835) B3073835
theorem B1819867 : Blo 1819611 1819867 := bstep (se 1 (by rfl) ⟨1364900, by rfl⟩ : syracuseStep 1819867 = 2729801) B2729801
theorem B13124855 : Blo 1819611 13124855 := bstep (se 1 (by rfl) ⟨9843641, by rfl⟩ : syracuseStep 13124855 = 19687283) B19687283
theorem B1819943 : Blo 1819611 1819943 := bstep (se 1 (by rfl) ⟨1364957, by rfl⟩ : syracuseStep 1819943 = 2729915) B2729915
theorem B1819983 : Blo 1819611 1819983 := bstep (se 1 (by rfl) ⟨1364987, by rfl⟩ : syracuseStep 1819983 = 2729975) B2729975
theorem B6915415 : Blo 1819611 6915415 := bstep (se 1 (by rfl) ⟨5186561, by rfl⟩ : syracuseStep 6915415 = 10373123) B10373123
theorem B1819999 : Blo 1819611 1819999 := bstep (se 1 (by rfl) ⟨1364999, by rfl⟩ : syracuseStep 1819999 = 2729999) B2729999
theorem B1820027 : Blo 1819611 1820027 := bstep (se 1 (by rfl) ⟨1365020, by rfl⟩ : syracuseStep 1820027 = 2730041) B2730041
theorem B3073423 : Blo 1819611 3073423 := bstep (se 1 (by rfl) ⟨2305067, by rfl⟩ : syracuseStep 3073423 = 4610135) B4610135
theorem B2917775 : Blo 1819611 2917775 := bstep (se 1 (by rfl) ⟨2188331, by rfl⟩ : syracuseStep 2917775 = 4376663) B4376663
theorem B2303407 : Blo 1819611 2303407 := bstep (se 1 (by rfl) ⟨1727555, by rfl⟩ : syracuseStep 2303407 = 3455111) B3455111
theorem B1820079 : Blo 1819611 1820079 := bstep (se 1 (by rfl) ⟨1365059, by rfl⟩ : syracuseStep 1820079 = 2730119) B2730119
theorem B1820103 : Blo 1819611 1820103 := bstep (se 1 (by rfl) ⟨1365077, by rfl⟩ : syracuseStep 1820103 = 2730155) B2730155
theorem B2729435 : Blo 1819611 2729435 := bstep (se 1 (by rfl) ⟨2047076, by rfl⟩ : syracuseStep 2729435 = 4094153) B4094153
theorem B1820123 : Blo 1819611 1820123 := bstep (se 1 (by rfl) ⟨1365092, by rfl⟩ : syracuseStep 1820123 = 2730185) B2730185
theorem B6145523 : Blo 1819611 6145523 := bstep (se 1 (by rfl) ⟨4609142, by rfl⟩ : syracuseStep 6145523 = 9218285) B9218285
theorem B1820199 : Blo 1819611 1820199 := bstep (se 1 (by rfl) ⟨1365149, by rfl⟩ : syracuseStep 1820199 = 2730299) B2730299
theorem B1820239 : Blo 1819611 1820239 := bstep (se 1 (by rfl) ⟨1365179, by rfl⟩ : syracuseStep 1820239 = 2730359) B2730359
theorem B1820255 : Blo 1819611 1820255 := bstep (se 1 (by rfl) ⟨1365191, by rfl⟩ : syracuseStep 1820255 = 2730383) B2730383
theorem B1820283 : Blo 1819611 1820283 := bstep (se 1 (by rfl) ⟨1365212, by rfl⟩ : syracuseStep 1820283 = 2730425) B2730425
theorem B6915719 : Blo 1819611 6915719 := bstep (se 1 (by rfl) ⟨5186789, by rfl⟩ : syracuseStep 6915719 = 10373579) B10373579
theorem B1820335 : Blo 1819611 1820335 := bstep (se 1 (by rfl) ⟨1365251, by rfl⟩ : syracuseStep 1820335 = 2730503) B2730503
theorem B1820359 : Blo 1819611 1820359 := bstep (se 1 (by rfl) ⟨1365269, by rfl⟩ : syracuseStep 1820359 = 2730539) B2730539
theorem B4097735 : Blo 1819611 4097735 := bstep (se 1 (by rfl) ⟨3073301, by rfl⟩ : syracuseStep 4097735 = 6146603) B6146603
theorem B31090391 : Blo 1819611 31090391 := bstep (se 1 (by rfl) ⟨23317793, by rfl⟩ : syracuseStep 31090391 = 46635587) B46635587
theorem B1820379 : Blo 1819611 1820379 := bstep (se 1 (by rfl) ⟨1365284, by rfl⟩ : syracuseStep 1820379 = 2730569) B2730569
theorem B8308439 : Blo 1819611 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B1820455 : Blo 1819611 1820455 := bstep (se 1 (by rfl) ⟨1365341, by rfl⟩ : syracuseStep 1820455 = 2730683) B2730683
theorem B1820495 : Blo 1819611 1820495 := bstep (se 1 (by rfl) ⟨1365371, by rfl⟩ : syracuseStep 1820495 = 2730743) B2730743
theorem B11659103 : Blo 1819611 11659103 := bstep (se 1 (by rfl) ⟨8744327, by rfl⟩ : syracuseStep 11659103 = 17488655) B17488655
theorem B1820511 : Blo 1819611 1820511 := bstep (se 1 (by rfl) ⟨1365383, by rfl⟩ : syracuseStep 1820511 = 2730767) B2730767
theorem B1820539 : Blo 1819611 1820539 := bstep (se 1 (by rfl) ⟨1365404, by rfl⟩ : syracuseStep 1820539 = 2730809) B2730809
theorem B2729903 : Blo 1819611 2729903 := bstep (se 1 (by rfl) ⟨2047427, by rfl⟩ : syracuseStep 2729903 = 4094855) B4094855
theorem B1820591 : Blo 1819611 1820591 := bstep (se 1 (by rfl) ⟨1365443, by rfl⟩ : syracuseStep 1820591 = 2730887) B2730887
theorem B3942319 : Blo 1819611 3942319 := bstep (se 1 (by rfl) ⟨2956739, by rfl⟩ : syracuseStep 3942319 = 5913479) B5913479
theorem B14010299 : Blo 1819611 14010299 := bstep (se 1 (by rfl) ⟨10507724, by rfl⟩ : syracuseStep 14010299 = 21015449) B21015449
theorem B1820615 : Blo 1819611 1820615 := bstep (se 1 (by rfl) ⟨1365461, by rfl⟩ : syracuseStep 1820615 = 2730923) B2730923
theorem B1820635 : Blo 1819611 1820635 := bstep (se 1 (by rfl) ⟨1365476, by rfl⟩ : syracuseStep 1820635 = 2730953) B2730953
theorem B2729993 : Blo 1819611 2729993 := bstep (se 2 (by rfl) ⟨1023747, by rfl⟩ : syracuseStep 2729993 = 2047495) B2047495
theorem B2664457 : Blo 1819611 2664457 := bstep (se 2 (by rfl) ⟨999171, by rfl⟩ : syracuseStep 2664457 = 1998343) B1998343
theorem B6146063 : Blo 1819611 6146063 := bstep (se 1 (by rfl) ⟨4609547, by rfl⟩ : syracuseStep 6146063 = 9219095) B9219095
theorem B2730023 : Blo 1819611 2730023 := bstep (se 1 (by rfl) ⟨2047517, by rfl⟩ : syracuseStep 2730023 = 4095035) B4095035
theorem B1820711 : Blo 1819611 1820711 := bstep (se 1 (by rfl) ⟨1365533, by rfl⟩ : syracuseStep 1820711 = 2731067) B2731067
theorem B1820751 : Blo 1819611 1820751 := bstep (se 1 (by rfl) ⟨1365563, by rfl⟩ : syracuseStep 1820751 = 2731127) B2731127
theorem B6916175 : Blo 1819611 6916175 := bstep (se 1 (by rfl) ⟨5187131, by rfl⟩ : syracuseStep 6916175 = 10374263) B10374263
theorem B18229337 : Blo 1819611 18229337 := bstep (se 2 (by rfl) ⟨6836001, by rfl⟩ : syracuseStep 18229337 = 13672003) B13672003
theorem B1820767 : Blo 1819611 1820767 := bstep (se 1 (by rfl) ⟨1365575, by rfl⟩ : syracuseStep 1820767 = 2731151) B2731151
theorem B13305971 : Blo 1819611 13305971 := bstep (se 1 (by rfl) ⟨9979478, by rfl⟩ : syracuseStep 13305971 = 19958957) B19958957
theorem B2730107 : Blo 1819611 2730107 := bstep (se 1 (by rfl) ⟨2047580, by rfl⟩ : syracuseStep 2730107 = 4095161) B4095161
theorem B1820795 : Blo 1819611 1820795 := bstep (se 1 (by rfl) ⟨1365596, by rfl⟩ : syracuseStep 1820795 = 2731193) B2731193
theorem B5834909 : Blo 1819611 5834909 := bstep (se 3 (by rfl) ⟨1094045, by rfl⟩ : syracuseStep 5834909 = 2188091) B2188091
theorem B1820847 : Blo 1819611 1820847 := bstep (se 1 (by rfl) ⟨1365635, by rfl⟩ : syracuseStep 1820847 = 2731271) B2731271
theorem B1820871 : Blo 1819611 1820871 := bstep (se 1 (by rfl) ⟨1365653, by rfl⟩ : syracuseStep 1820871 = 2731307) B2731307
theorem B1820891 : Blo 1819611 1820891 := bstep (se 1 (by rfl) ⟨1365668, by rfl⟩ : syracuseStep 1820891 = 2731337) B2731337
theorem B2590969 : Blo 1819611 2590969 := bstep (se 2 (by rfl) ⟨971613, by rfl⟩ : syracuseStep 2590969 = 1943227) B1943227
theorem B2730233 : Blo 1819611 2730233 := bstep (se 2 (by rfl) ⟨1023837, by rfl⟩ : syracuseStep 2730233 = 2047675) B2047675
theorem B1820967 : Blo 1819611 1820967 := bstep (se 1 (by rfl) ⟨1365725, by rfl⟩ : syracuseStep 1820967 = 2731451) B2731451
theorem B1821007 : Blo 1819611 1821007 := bstep (se 1 (by rfl) ⟨1365755, by rfl⟩ : syracuseStep 1821007 = 2731511) B2731511
theorem B2730335 : Blo 1819611 2730335 := bstep (se 1 (by rfl) ⟨2047751, by rfl⟩ : syracuseStep 2730335 = 4095503) B4095503
theorem B1821023 : Blo 1819611 1821023 := bstep (se 1 (by rfl) ⟨1365767, by rfl⟩ : syracuseStep 1821023 = 2731535) B2731535
theorem B2730347 : Blo 1819611 2730347 := bstep (se 1 (by rfl) ⟨2047760, by rfl⟩ : syracuseStep 2730347 = 4095521) B4095521
theorem B1821051 : Blo 1819611 1821051 := bstep (se 1 (by rfl) ⟨1365788, by rfl⟩ : syracuseStep 1821051 = 2731577) B2731577
theorem B1821103 : Blo 1819611 1821103 := bstep (se 1 (by rfl) ⟨1365827, by rfl⟩ : syracuseStep 1821103 = 2731655) B2731655
theorem B1821127 : Blo 1819611 1821127 := bstep (se 1 (by rfl) ⟨1365845, by rfl⟩ : syracuseStep 1821127 = 2731691) B2731691
theorem B2492891 : Blo 1819611 2492891 := bstep (se 1 (by rfl) ⟨1869668, by rfl⟩ : syracuseStep 2492891 = 3739337) B3739337
theorem B1821147 : Blo 1819611 1821147 := bstep (se 1 (by rfl) ⟨1365860, by rfl⟩ : syracuseStep 1821147 = 2731721) B2731721
theorem B2304551 : Blo 1819611 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B1821223 : Blo 1819611 1821223 := bstep (se 1 (by rfl) ⟨1365917, by rfl⟩ : syracuseStep 1821223 = 2731835) B2731835
theorem B4098599 : Blo 1819611 4098599 := bstep (se 1 (by rfl) ⟨3073949, by rfl⟩ : syracuseStep 4098599 = 6147899) B6147899
theorem B2730575 : Blo 1819611 2730575 := bstep (se 1 (by rfl) ⟨2047931, by rfl⟩ : syracuseStep 2730575 = 4095863) B4095863
theorem B1821263 : Blo 1819611 1821263 := bstep (se 1 (by rfl) ⟨1365947, by rfl⟩ : syracuseStep 1821263 = 2731895) B2731895
theorem B1821279 : Blo 1819611 1821279 := bstep (se 1 (by rfl) ⟨1365959, by rfl⟩ : syracuseStep 1821279 = 2731919) B2731919
theorem B6146657 : Blo 1819611 6146657 := bstep (se 2 (by rfl) ⟨2304996, by rfl⟩ : syracuseStep 6146657 = 4609993) B4609993
theorem B1821307 : Blo 1819611 1821307 := bstep (se 1 (by rfl) ⟨1365980, by rfl⟩ : syracuseStep 1821307 = 2731961) B2731961
theorem B1821359 : Blo 1819611 1821359 := bstep (se 1 (by rfl) ⟨1366019, by rfl⟩ : syracuseStep 1821359 = 2732039) B2732039
theorem B7383737 : Blo 1819611 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B2730695 : Blo 1819611 2730695 := bstep (se 1 (by rfl) ⟨2048021, by rfl⟩ : syracuseStep 2730695 = 4096043) B4096043
theorem B1821383 : Blo 1819611 1821383 := bstep (se 1 (by rfl) ⟨1366037, by rfl⟩ : syracuseStep 1821383 = 2732075) B2732075
theorem B9218771 : Blo 1819611 9218771 := bstep (se 1 (by rfl) ⟨6914078, by rfl⟩ : syracuseStep 9218771 = 13828157) B13828157
theorem B1821403 : Blo 1819611 1821403 := bstep (se 1 (by rfl) ⟨1366052, by rfl⟩ : syracuseStep 1821403 = 2732105) B2732105
theorem B1821479 : Blo 1819611 1821479 := bstep (se 1 (by rfl) ⟨1366109, by rfl⟩ : syracuseStep 1821479 = 2732219) B2732219
theorem B1821519 : Blo 1819611 1821519 := bstep (se 1 (by rfl) ⟨1366139, by rfl⟩ : syracuseStep 1821519 = 2732279) B2732279
theorem B1821535 : Blo 1819611 1821535 := bstep (se 1 (by rfl) ⟨1366151, by rfl⟩ : syracuseStep 1821535 = 2732303) B2732303
theorem B2730857 : Blo 1819611 2730857 := bstep (se 2 (by rfl) ⟨1024071, by rfl⟩ : syracuseStep 2730857 = 2048143) B2048143
theorem B2304875 : Blo 1819611 2304875 := bstep (se 1 (by rfl) ⟨1728656, by rfl⟩ : syracuseStep 2304875 = 3457313) B3457313
theorem B1821563 : Blo 1819611 1821563 := bstep (se 1 (by rfl) ⟨1366172, by rfl⟩ : syracuseStep 1821563 = 2732345) B2732345
theorem B4606895 : Blo 1819611 4606895 := bstep (se 1 (by rfl) ⟨3455171, by rfl⟩ : syracuseStep 4606895 = 6910343) B6910343
theorem B2730935 : Blo 1819611 2730935 := bstep (se 1 (by rfl) ⟨2048201, by rfl⟩ : syracuseStep 2730935 = 4096403) B4096403
theorem B2730971 : Blo 1819611 2730971 := bstep (se 1 (by rfl) ⟨2048228, by rfl⟩ : syracuseStep 2730971 = 4096457) B4096457
theorem B7777451 : Blo 1819611 7777451 := bstep (se 1 (by rfl) ⟨5833088, by rfl⟩ : syracuseStep 7777451 = 11666177) B11666177
theorem B2731439 : Blo 1819611 2731439 := bstep (se 1 (by rfl) ⟨2048579, by rfl⟩ : syracuseStep 2731439 = 4097159) B4097159
theorem B2731529 : Blo 1819611 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B4607513 : Blo 1819611 4607513 := bstep (se 2 (by rfl) ⟨1727817, by rfl⟩ : syracuseStep 4607513 = 3455635) B3455635
theorem B2731559 : Blo 1819611 2731559 := bstep (se 1 (by rfl) ⟨2048669, by rfl⟩ : syracuseStep 2731559 = 4097339) B4097339
theorem B8302177 : Blo 1819611 8302177 := bstep (se 2 (by rfl) ⟨3113316, by rfl⟩ : syracuseStep 8302177 = 6226633) B6226633
theorem B14012027 : Blo 1819611 14012027 := bstep (se 1 (by rfl) ⟨10509020, by rfl⟩ : syracuseStep 14012027 = 21018041) B21018041
theorem B2731643 : Blo 1819611 2731643 := bstep (se 1 (by rfl) ⟨2048732, by rfl⟩ : syracuseStep 2731643 = 4097465) B4097465
theorem B2731769 : Blo 1819611 2731769 := bstep (se 2 (by rfl) ⟨1024413, by rfl⟩ : syracuseStep 2731769 = 2048827) B2048827
theorem B2731871 : Blo 1819611 2731871 := bstep (se 1 (by rfl) ⟨2048903, by rfl⟩ : syracuseStep 2731871 = 4097807) B4097807
theorem B3501929 : Blo 1819611 3501929 := bstep (se 2 (by rfl) ⟨1313223, by rfl⟩ : syracuseStep 3501929 = 2626447) B2626447
theorem B2731883 : Blo 1819611 2731883 := bstep (se 1 (by rfl) ⟨2048912, by rfl⟩ : syracuseStep 2731883 = 4097825) B4097825
theorem B13832045 : Blo 1819611 13832045 := bstep (se 3 (by rfl) ⟨2593508, by rfl⟩ : syracuseStep 13832045 = 5187017) B5187017
theorem B3157903 : Blo 1819611 3157903 := bstep (se 1 (by rfl) ⟨2368427, by rfl⟩ : syracuseStep 3157903 = 4736855) B4736855
theorem B6909857 : Blo 1819611 6909857 := bstep (se 2 (by rfl) ⟨2591196, by rfl⟩ : syracuseStep 6909857 = 5182393) B5182393
theorem B3690505 : Blo 1819611 3690505 := bstep (se 2 (by rfl) ⟨1383939, by rfl⟩ : syracuseStep 3690505 = 2767879) B2767879
theorem B19681309 : Blo 1819611 19681309 := bstep (se 3 (by rfl) ⟨3690245, by rfl⟩ : syracuseStep 19681309 = 7380491) B7380491
theorem B2732111 : Blo 1819611 2732111 := bstep (se 1 (by rfl) ⟨2049083, by rfl⟩ : syracuseStep 2732111 = 4098167) B4098167
theorem B2732231 : Blo 1819611 2732231 := bstep (se 1 (by rfl) ⟨2049173, by rfl⟩ : syracuseStep 2732231 = 4098347) B4098347
theorem B2732393 : Blo 1819611 2732393 := bstep (se 2 (by rfl) ⟨1024647, by rfl⟩ : syracuseStep 2732393 = 2049295) B2049295
theorem B2216375 : Blo 1819611 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B11670227 : Blo 1819611 11670227 := bstep (se 1 (by rfl) ⟨8752670, by rfl⟩ : syracuseStep 11670227 = 17505341) B17505341
theorem B7385849 : Blo 1819611 7385849 := bstep (se 2 (by rfl) ⟨2769693, by rfl⟩ : syracuseStep 7385849 = 5539387) B5539387
theorem B10367747 : Blo 1819611 10367747 := bstep (se 1 (by rfl) ⟨7775810, by rfl⟩ : syracuseStep 10367747 = 15551621) B15551621
theorem B70947683 : Blo 1819611 70947683 := bstep (se 1 (by rfl) ⟨53210762, by rfl⟩ : syracuseStep 70947683 = 106421525) B106421525
theorem B6910829 : Blo 1819611 6910829 := bstep (se 3 (by rfl) ⟨1295780, by rfl⟩ : syracuseStep 6910829 = 2591561) B2591561
theorem B14971823 : Blo 1819611 14971823 := bstep (se 1 (by rfl) ⟨11228867, by rfl⟩ : syracuseStep 14971823 = 22457735) B22457735
theorem B9221039 : Blo 1819611 9221039 := bstep (se 1 (by rfl) ⟨6915779, by rfl⟩ : syracuseStep 9221039 = 13831559) B13831559
theorem B3888299 : Blo 1819611 3888299 := bstep (se 1 (by rfl) ⟨2916224, by rfl⟩ : syracuseStep 3888299 = 5832449) B5832449
theorem B20731301 : Blo 1819611 20731301 := bstep (se 4 (by rfl) ⟨1943559, by rfl⟩ : syracuseStep 20731301 = 3887119) B3887119
theorem B3454427 : Blo 1819611 3454427 := bstep (se 1 (by rfl) ⟨2590820, by rfl⟩ : syracuseStep 3454427 = 5181641) B5181641
theorem B7779827 : Blo 1819611 7779827 := bstep (se 1 (by rfl) ⟨5834870, by rfl⟩ : syracuseStep 7779827 = 11669741) B11669741
theorem B6911513 : Blo 1819611 6911513 := bstep (se 2 (by rfl) ⟨2591817, by rfl⟩ : syracuseStep 6911513 = 5183635) B5183635
theorem B6141473 : Blo 1819611 6141473 := bstep (se 2 (by rfl) ⟨2303052, by rfl⟩ : syracuseStep 6141473 = 4606105) B4606105
theorem B6911527 : Blo 1819611 6911527 := bstep (se 1 (by rfl) ⟨5183645, by rfl⟩ : syracuseStep 6911527 = 10367291) B10367291
theorem B4920871 : Blo 1819611 4920871 := bstep (se 1 (by rfl) ⟨3690653, by rfl⟩ : syracuseStep 4920871 = 7381307) B7381307
theorem B5183099 : Blo 1819611 5183099 := bstep (se 1 (by rfl) ⟨3887324, by rfl⟩ : syracuseStep 5183099 = 7774649) B7774649
theorem B4920955 : Blo 1819611 4920955 := bstep (se 1 (by rfl) ⟨3690716, by rfl⟩ : syracuseStep 4920955 = 7381433) B7381433
theorem B7779979 : Blo 1819611 7779979 := bstep (se 1 (by rfl) ⟨5834984, by rfl⟩ : syracuseStep 7779979 = 11669969) B11669969
theorem B9213587 : Blo 1819611 9213587 := bstep (se 1 (by rfl) ⟨6910190, by rfl⟩ : syracuseStep 9213587 = 13820381) B13820381
theorem B3454663 : Blo 1819611 3454663 := bstep (se 1 (by rfl) ⟨2590997, by rfl⟩ : syracuseStep 3454663 = 5181995) B5181995
theorem B6141689 : Blo 1819611 6141689 := bstep (se 2 (by rfl) ⟨2303133, by rfl⟩ : syracuseStep 6141689 = 4606267) B4606267
theorem B5183327 : Blo 1819611 5183327 := bstep (se 1 (by rfl) ⟨3887495, by rfl⟩ : syracuseStep 5183327 = 7774991) B7774991
theorem B14767991 : Blo 1819611 14767991 := bstep (se 1 (by rfl) ⟨11075993, by rfl⟩ : syracuseStep 14767991 = 22151987) B22151987
theorem B9598907 : Blo 1819611 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B20740049 : Blo 1819611 20740049 := bstep (se 2 (by rfl) ⟨7777518, by rfl⟩ : syracuseStep 20740049 = 15555037) B15555037
theorem B6141959 : Blo 1819611 6141959 := bstep (se 1 (by rfl) ⟨4606469, by rfl⟩ : syracuseStep 6141959 = 9212939) B9212939
theorem B4610105 : Blo 1819611 4610105 := bstep (se 2 (by rfl) ⟨1728789, by rfl⟩ : syracuseStep 4610105 = 3457579) B3457579
theorem B6142067 : Blo 1819611 6142067 := bstep (se 1 (by rfl) ⟨4606550, by rfl⟩ : syracuseStep 6142067 = 9213101) B9213101
theorem B2767097 : Blo 1819611 2767097 := bstep (se 2 (by rfl) ⟨1037661, by rfl⟩ : syracuseStep 2767097 = 2075323) B2075323
theorem B6912317 : Blo 1819611 6912317 := bstep (se 3 (by rfl) ⟨1296059, by rfl⟩ : syracuseStep 6912317 = 2592119) B2592119
theorem B6142337 : Blo 1819611 6142337 := bstep (se 2 (by rfl) ⟨2303376, by rfl⟩ : syracuseStep 6142337 = 4606753) B4606753
theorem B4094351 : Blo 1819611 4094351 := bstep (se 1 (by rfl) ⟨3070763, by rfl⟩ : syracuseStep 4094351 = 6141527) B6141527
theorem B21027275 : Blo 1819611 21027275 := bstep (se 1 (by rfl) ⟨15770456, by rfl⟩ : syracuseStep 21027275 = 31540913) B31540913
theorem B6912499 : Blo 1819611 6912499 := bstep (se 1 (by rfl) ⟨5184374, by rfl⟩ : syracuseStep 6912499 = 10368749) B10368749
theorem B4094675 : Blo 1819611 4094675 := bstep (se 1 (by rfl) ⟨3071006, by rfl⟩ : syracuseStep 4094675 = 6142013) B6142013
theorem B4373203 : Blo 1819611 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B291625757 : Blo 1819611 291625757 := bstep (se 3 (by rfl) ⟨54679829, by rfl⟩ : syracuseStep 291625757 = 109359659) B109359659
theorem B28425107 : Blo 1819611 28425107 := bstep (se 1 (by rfl) ⟨21318830, by rfl⟩ : syracuseStep 28425107 = 42637661) B42637661
theorem B3070939 : Blo 1819611 3070939 := bstep (se 1 (by rfl) ⟨2303204, by rfl⟩ : syracuseStep 3070939 = 4606409) B4606409
theorem B3890195 : Blo 1819611 3890195 := bstep (se 1 (by rfl) ⟨2917646, by rfl⟩ : syracuseStep 3890195 = 5835293) B5835293
theorem B13818923 : Blo 1819611 13818923 := bstep (se 1 (by rfl) ⟨10364192, by rfl⟩ : syracuseStep 13818923 = 20728385) B20728385
theorem B2047099 : Blo 1819611 2047099 := bstep (se 1 (by rfl) ⟨1535324, by rfl⟩ : syracuseStep 2047099 = 3070649) B3070649
theorem B5831833 : Blo 1819611 5831833 := bstep (se 2 (by rfl) ⟨2186937, by rfl⟩ : syracuseStep 5831833 = 4373875) B4373875
theorem B6143147 : Blo 1819611 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B21060803 : Blo 1819611 21060803 := bstep (se 1 (by rfl) ⟨15795602, by rfl⟩ : syracuseStep 21060803 = 31591205) B31591205
theorem B5184911 : Blo 1819611 5184911 := bstep (se 1 (by rfl) ⟨3888683, by rfl⟩ : syracuseStep 5184911 = 7777367) B7777367
theorem B9838043 : Blo 1819611 9838043 := bstep (se 1 (by rfl) ⟨7378532, by rfl⟩ : syracuseStep 9838043 = 14757065) B14757065
theorem B3456569 : Blo 1819611 3456569 := bstep (se 2 (by rfl) ⟨1296213, by rfl⟩ : syracuseStep 3456569 = 2592427) B2592427
theorem B119709251 : Blo 1819611 119709251 := bstep (se 1 (by rfl) ⟨89781938, by rfl⟩ : syracuseStep 119709251 = 179563877) B179563877
theorem B2047567 : Blo 1819611 2047567 := bstep (se 1 (by rfl) ⟨1535675, by rfl⟩ : syracuseStep 2047567 = 3071351) B3071351
theorem B3071567 : Blo 1819611 3071567 := bstep (se 1 (by rfl) ⟨2303675, by rfl⟩ : syracuseStep 3071567 = 4607351) B4607351
theorem B13827671 : Blo 1819611 13827671 := bstep (se 1 (by rfl) ⟨10370753, by rfl⟩ : syracuseStep 13827671 = 20741507) B20741507
theorem B4095611 : Blo 1819611 4095611 := bstep (se 1 (by rfl) ⟨3071708, by rfl⟩ : syracuseStep 4095611 = 6143417) B6143417
theorem B4374155 : Blo 1819611 4374155 := bstep (se 1 (by rfl) ⟨3280616, by rfl⟩ : syracuseStep 4374155 = 6561233) B6561233
theorem B6143687 : Blo 1819611 6143687 := bstep (se 1 (by rfl) ⟨4607765, by rfl⟩ : syracuseStep 6143687 = 9215531) B9215531
theorem B6913745 : Blo 1819611 6913745 := bstep (se 2 (by rfl) ⟨2592654, by rfl⟩ : syracuseStep 6913745 = 5185309) B5185309
theorem B4800215 : Blo 1819611 4800215 := bstep (se 1 (by rfl) ⟨3600161, by rfl⟩ : syracuseStep 4800215 = 7200323) B7200323
theorem B4095737 : Blo 1819611 4095737 := bstep (se 2 (by rfl) ⟨1535901, by rfl⟩ : syracuseStep 4095737 = 3071803) B3071803
theorem B49831685 : Blo 1819611 49831685 := bstep (se 4 (by rfl) ⟨4671720, by rfl⟩ : syracuseStep 49831685 = 9343441) B9343441
theorem B3456911 : Blo 1819611 3456911 := bstep (se 1 (by rfl) ⟨2592683, by rfl⟩ : syracuseStep 3456911 = 5185367) B5185367
theorem B2047963 : Blo 1819611 2047963 := bstep (se 1 (by rfl) ⟨1535972, by rfl⟩ : syracuseStep 2047963 = 3071945) B3071945
theorem B2048287 : Blo 1819611 2048287 := bstep (se 1 (by rfl) ⟨1536215, by rfl⟩ : syracuseStep 2048287 = 3072431) B3072431
theorem B8749403 : Blo 1819611 8749403 := bstep (se 1 (by rfl) ⟨6562052, by rfl⟩ : syracuseStep 8749403 = 13124105) B13124105
theorem B4096367 : Blo 1819611 4096367 := bstep (se 1 (by rfl) ⟨3072275, by rfl⟩ : syracuseStep 4096367 = 6144551) B6144551
theorem B4096439 : Blo 1819611 4096439 := bstep (se 1 (by rfl) ⟨3072329, by rfl⟩ : syracuseStep 4096439 = 6144659) B6144659
theorem B4923899 : Blo 1819611 4923899 := bstep (se 1 (by rfl) ⟨3692924, by rfl⟩ : syracuseStep 4923899 = 7385849) B7385849
theorem B2048575 : Blo 1819611 2048575 := bstep (se 1 (by rfl) ⟨1536431, by rfl⟩ : syracuseStep 2048575 = 3072863) B3072863
theorem B4096583 : Blo 1819611 4096583 := bstep (se 1 (by rfl) ⟨3072437, by rfl⟩ : syracuseStep 4096583 = 6144875) B6144875
theorem B4096619 : Blo 1819611 4096619 := bstep (se 1 (by rfl) ⟨3072464, by rfl⟩ : syracuseStep 4096619 = 6144929) B6144929
theorem B9216665 : Blo 1819611 9216665 := bstep (se 2 (by rfl) ⟨3456249, by rfl⟩ : syracuseStep 9216665 = 6912499) B6912499
theorem B16614071 : Blo 1819611 16614071 := bstep (se 1 (by rfl) ⟨12460553, by rfl⟩ : syracuseStep 16614071 = 24921107) B24921107
theorem B8749903 : Blo 1819611 8749903 := bstep (se 1 (by rfl) ⟨6562427, by rfl⟩ : syracuseStep 8749903 = 13124855) B13124855
theorem B13820867 : Blo 1819611 13820867 := bstep (se 1 (by rfl) ⟨10365650, by rfl⟩ : syracuseStep 13820867 = 20731301) B20731301
theorem B1819623 : Blo 1819611 1819623 := bstep (se 1 (by rfl) ⟨1364717, by rfl⟩ : syracuseStep 1819623 = 2729435) B2729435
theorem B4097015 : Blo 1819611 4097015 := bstep (se 1 (by rfl) ⟨3072761, by rfl⟩ : syracuseStep 4097015 = 6145523) B6145523
theorem B5186551 : Blo 1819611 5186551 := bstep (se 1 (by rfl) ⟨3889913, by rfl⟩ : syracuseStep 5186551 = 7779827) B7779827
theorem B20726927 : Blo 1819611 20726927 := bstep (se 1 (by rfl) ⟨15545195, by rfl⟩ : syracuseStep 20726927 = 31090391) B31090391
theorem B5538959 : Blo 1819611 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B1819935 : Blo 1819611 1819935 := bstep (se 1 (by rfl) ⟨1364951, by rfl⟩ : syracuseStep 1819935 = 2729903) B2729903
theorem B9340199 : Blo 1819611 9340199 := bstep (se 1 (by rfl) ⟨7005149, by rfl⟩ : syracuseStep 9340199 = 14010299) B14010299
theorem B6399271 : Blo 1819611 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B1819995 : Blo 1819611 1819995 := bstep (se 1 (by rfl) ⟨1364996, by rfl⟩ : syracuseStep 1819995 = 2729993) B2729993
theorem B4097375 : Blo 1819611 4097375 := bstep (se 1 (by rfl) ⟨3073031, by rfl⟩ : syracuseStep 4097375 = 6146063) B6146063
theorem B1820015 : Blo 1819611 1820015 := bstep (se 1 (by rfl) ⟨1365011, by rfl⟩ : syracuseStep 1820015 = 2730023) B2730023
theorem B3073403 : Blo 1819611 3073403 := bstep (se 1 (by rfl) ⟨2305052, by rfl⟩ : syracuseStep 3073403 = 4610105) B4610105
theorem B1820071 : Blo 1819611 1820071 := bstep (se 1 (by rfl) ⟨1365053, by rfl⟩ : syracuseStep 1820071 = 2730107) B2730107
theorem B6145469 : Blo 1819611 6145469 := bstep (se 3 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 6145469 = 2304551) B2304551
theorem B2729465 : Blo 1819611 2729465 := bstep (se 2 (by rfl) ⟨1023549, by rfl⟩ : syracuseStep 2729465 = 2047099) B2047099
theorem B1844731 : Blo 1819611 1844731 := bstep (se 1 (by rfl) ⟨1383548, by rfl⟩ : syracuseStep 1844731 = 2767097) B2767097
theorem B1820155 : Blo 1819611 1820155 := bstep (se 1 (by rfl) ⟨1365116, by rfl⟩ : syracuseStep 1820155 = 2730233) B2730233
theorem B7775777 : Blo 1819611 7775777 := bstep (se 2 (by rfl) ⟨2915916, by rfl⟩ : syracuseStep 7775777 = 5831833) B5831833
theorem B1820223 : Blo 1819611 1820223 := bstep (se 1 (by rfl) ⟨1365167, by rfl⟩ : syracuseStep 1820223 = 2730335) B2730335
theorem B1820231 : Blo 1819611 1820231 := bstep (se 1 (by rfl) ⟨1365173, by rfl⟩ : syracuseStep 1820231 = 2730347) B2730347
theorem B2729567 : Blo 1819611 2729567 := bstep (se 1 (by rfl) ⟨2047175, by rfl⟩ : syracuseStep 2729567 = 4094351) B4094351
theorem B14018183 : Blo 1819611 14018183 := bstep (se 1 (by rfl) ⟨10513637, by rfl⟩ : syracuseStep 14018183 = 21027275) B21027275
theorem B1820383 : Blo 1819611 1820383 := bstep (se 1 (by rfl) ⟨1365287, by rfl⟩ : syracuseStep 1820383 = 2730575) B2730575
theorem B4097771 : Blo 1819611 4097771 := bstep (se 1 (by rfl) ⟨3073328, by rfl⟩ : syracuseStep 4097771 = 6146657) B6146657
theorem B1820463 : Blo 1819611 1820463 := bstep (se 1 (by rfl) ⟨1365347, by rfl⟩ : syracuseStep 1820463 = 2730695) B2730695
theorem B2729783 : Blo 1819611 2729783 := bstep (se 1 (by rfl) ⟨2047337, by rfl⟩ : syracuseStep 2729783 = 4094675) B4094675
theorem B6145847 : Blo 1819611 6145847 := bstep (se 1 (by rfl) ⟨4609385, by rfl⟩ : syracuseStep 6145847 = 9218771) B9218771
theorem B4097897 : Blo 1819611 4097897 := bstep (se 2 (by rfl) ⟨1536711, by rfl⟩ : syracuseStep 4097897 = 3073423) B3073423
theorem B1820571 : Blo 1819611 1820571 := bstep (se 1 (by rfl) ⟨1365428, by rfl⟩ : syracuseStep 1820571 = 2730857) B2730857
theorem B18950071 : Blo 1819611 18950071 := bstep (se 1 (by rfl) ⟨14212553, by rfl⟩ : syracuseStep 18950071 = 28425107) B28425107
theorem B1820623 : Blo 1819611 1820623 := bstep (se 1 (by rfl) ⟨1365467, by rfl⟩ : syracuseStep 1820623 = 2730935) B2730935
theorem B1820647 : Blo 1819611 1820647 := bstep (se 1 (by rfl) ⟨1365485, by rfl⟩ : syracuseStep 1820647 = 2730971) B2730971
theorem B2730089 : Blo 1819611 2730089 := bstep (se 2 (by rfl) ⟨1023783, by rfl⟩ : syracuseStep 2730089 = 2047567) B2047567
theorem B11069569 : Blo 1819611 11069569 := bstep (se 2 (by rfl) ⟨4151088, by rfl⟩ : syracuseStep 11069569 = 8302177) B8302177
theorem B10373305 : Blo 1819611 10373305 := bstep (se 2 (by rfl) ⟨3889989, by rfl⟩ : syracuseStep 10373305 = 7779979) B7779979
theorem B4606217 : Blo 1819611 4606217 := bstep (se 2 (by rfl) ⟨1727331, by rfl⟩ : syracuseStep 4606217 = 3454663) B3454663
theorem B6146333 : Blo 1819611 6146333 := bstep (se 3 (by rfl) ⟨1152437, by rfl⟩ : syracuseStep 6146333 = 2304875) B2304875
theorem B1820959 : Blo 1819611 1820959 := bstep (se 1 (by rfl) ⟨1365719, by rfl⟩ : syracuseStep 1820959 = 2731439) B2731439
theorem B5835037 : Blo 1819611 5835037 := bstep (se 3 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 5835037 = 2188139) B2188139
theorem B1821019 : Blo 1819611 1821019 := bstep (se 1 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 1821019 = 2731529) B2731529
theorem B1821039 : Blo 1819611 1821039 := bstep (se 1 (by rfl) ⟨1365779, by rfl⟩ : syracuseStep 1821039 = 2731559) B2731559
theorem B2304379 : Blo 1819611 2304379 := bstep (se 1 (by rfl) ⟨1728284, by rfl⟩ : syracuseStep 2304379 = 3456569) B3456569
theorem B9218447 : Blo 1819611 9218447 := bstep (se 1 (by rfl) ⟨6913835, by rfl⟩ : syracuseStep 9218447 = 13827671) B13827671
theorem B2730407 : Blo 1819611 2730407 := bstep (se 1 (by rfl) ⟨2047805, by rfl⟩ : syracuseStep 2730407 = 4095611) B4095611
theorem B9341351 : Blo 1819611 9341351 := bstep (se 1 (by rfl) ⟨7006013, by rfl⟩ : syracuseStep 9341351 = 14012027) B14012027
theorem B1821095 : Blo 1819611 1821095 := bstep (se 1 (by rfl) ⟨1365821, by rfl⟩ : syracuseStep 1821095 = 2731643) B2731643
theorem B2730491 : Blo 1819611 2730491 := bstep (se 1 (by rfl) ⟨2047868, by rfl⟩ : syracuseStep 2730491 = 4095737) B4095737
theorem B1821179 : Blo 1819611 1821179 := bstep (se 1 (by rfl) ⟨1365884, by rfl⟩ : syracuseStep 1821179 = 2731769) B2731769
theorem B33221123 : Blo 1819611 33221123 := bstep (se 1 (by rfl) ⟨24915842, by rfl⟩ : syracuseStep 33221123 = 49831685) B49831685
theorem B1821247 : Blo 1819611 1821247 := bstep (se 1 (by rfl) ⟨1365935, by rfl⟩ : syracuseStep 1821247 = 2731871) B2731871
theorem B1821255 : Blo 1819611 1821255 := bstep (se 1 (by rfl) ⟨1365941, by rfl⟩ : syracuseStep 1821255 = 2731883) B2731883
theorem B2304607 : Blo 1819611 2304607 := bstep (se 1 (by rfl) ⟨1728455, by rfl⟩ : syracuseStep 2304607 = 3456911) B3456911
theorem B4606571 : Blo 1819611 4606571 := bstep (se 1 (by rfl) ⟨3454928, by rfl⟩ : syracuseStep 4606571 = 6909857) B6909857
theorem B2730617 : Blo 1819611 2730617 := bstep (se 2 (by rfl) ⟨1023981, by rfl⟩ : syracuseStep 2730617 = 2047963) B2047963
theorem B2730671 : Blo 1819611 2730671 := bstep (se 1 (by rfl) ⟨2048003, by rfl⟩ : syracuseStep 2730671 = 4096007) B4096007
theorem B26241745 : Blo 1819611 26241745 := bstep (se 2 (by rfl) ⟨9840654, by rfl⟩ : syracuseStep 26241745 = 19681309) B19681309
theorem B2730719 : Blo 1819611 2730719 := bstep (se 1 (by rfl) ⟨2048039, by rfl⟩ : syracuseStep 2730719 = 4096079) B4096079
theorem B1821407 : Blo 1819611 1821407 := bstep (se 1 (by rfl) ⟨1366055, by rfl⟩ : syracuseStep 1821407 = 2732111) B2732111
theorem B5253907 : Blo 1819611 5253907 := bstep (se 1 (by rfl) ⟨3940430, by rfl⟩ : syracuseStep 5253907 = 7880861) B7880861
theorem B1821487 : Blo 1819611 1821487 := bstep (se 1 (by rfl) ⟨1366115, by rfl⟩ : syracuseStep 1821487 = 2732231) B2732231
theorem B8301431 : Blo 1819611 8301431 := bstep (se 1 (by rfl) ⟨6226073, by rfl⟩ : syracuseStep 8301431 = 12452147) B12452147
theorem B1821595 : Blo 1819611 1821595 := bstep (se 1 (by rfl) ⟨1366196, by rfl⟩ : syracuseStep 1821595 = 2732393) B2732393
theorem B2730983 : Blo 1819611 2730983 := bstep (se 1 (by rfl) ⟨2048237, by rfl⟩ : syracuseStep 2730983 = 4096475) B4096475
theorem B6908915 : Blo 1819611 6908915 := bstep (se 1 (by rfl) ⟨5181686, by rfl⟩ : syracuseStep 6908915 = 10363373) B10363373
theorem B6564851 : Blo 1819611 6564851 := bstep (se 1 (by rfl) ⟨4923638, by rfl⟩ : syracuseStep 6564851 = 9847277) B9847277
theorem B2731241 : Blo 1819611 2731241 := bstep (se 2 (by rfl) ⟨1024215, by rfl⟩ : syracuseStep 2731241 = 2048431) B2048431
theorem B4607219 : Blo 1819611 4607219 := bstep (se 1 (by rfl) ⟨3455414, by rfl⟩ : syracuseStep 4607219 = 6910829) B6910829
theorem B2731295 : Blo 1819611 2731295 := bstep (se 1 (by rfl) ⟨2048471, by rfl⟩ : syracuseStep 2731295 = 4096943) B4096943
theorem B9981215 : Blo 1819611 9981215 := bstep (se 1 (by rfl) ⟨7485911, by rfl⟩ : syracuseStep 9981215 = 14971823) B14971823
theorem B6147359 : Blo 1819611 6147359 := bstep (se 1 (by rfl) ⟨4610519, by rfl⟩ : syracuseStep 6147359 = 9221039) B9221039
theorem B6909371 : Blo 1819611 6909371 := bstep (se 1 (by rfl) ⟨5182028, by rfl⟩ : syracuseStep 6909371 = 10364057) B10364057
theorem B2592199 : Blo 1819611 2592199 := bstep (se 1 (by rfl) ⟨1944149, by rfl⟩ : syracuseStep 2592199 = 3888299) B3888299
theorem B2731463 : Blo 1819611 2731463 := bstep (se 1 (by rfl) ⟨2048597, by rfl⟩ : syracuseStep 2731463 = 4097195) B4097195
theorem B1945183 : Blo 1819611 1945183 := bstep (se 1 (by rfl) ⟨1458887, by rfl⟩ : syracuseStep 1945183 = 2917775) B2917775
theorem B4607675 : Blo 1819611 4607675 := bstep (se 1 (by rfl) ⟨3455756, by rfl⟩ : syracuseStep 4607675 = 6911513) B6911513
theorem B2731817 : Blo 1819611 2731817 := bstep (se 2 (by rfl) ⟨1024431, by rfl⟩ : syracuseStep 2731817 = 2048863) B2048863
theorem B2731823 : Blo 1819611 2731823 := bstep (se 1 (by rfl) ⟨2048867, by rfl⟩ : syracuseStep 2731823 = 4097735) B4097735
theorem B9211805 : Blo 1819611 9211805 := bstep (se 3 (by rfl) ⟨1727213, by rfl⟩ : syracuseStep 9211805 = 3454427) B3454427
theorem B12152891 : Blo 1819611 12152891 := bstep (se 1 (by rfl) ⟨9114668, by rfl⟩ : syracuseStep 12152891 = 18229337) B18229337
theorem B4608211 : Blo 1819611 4608211 := bstep (se 1 (by rfl) ⟨3456158, by rfl⟩ : syracuseStep 4608211 = 6912317) B6912317
theorem B2732297 : Blo 1819611 2732297 := bstep (se 2 (by rfl) ⟨1024611, by rfl⟩ : syracuseStep 2732297 = 2049223) B2049223
theorem B2732399 : Blo 1819611 2732399 := bstep (se 1 (by rfl) ⟨2049299, by rfl⟩ : syracuseStep 2732399 = 4098599) B4098599
theorem B9220553 : Blo 1819611 9220553 := bstep (se 2 (by rfl) ⟨3457707, by rfl⟩ : syracuseStep 9220553 = 6915415) B6915415
theorem B194417171 : Blo 1819611 194417171 := bstep (se 1 (by rfl) ⟨145812878, by rfl⟩ : syracuseStep 194417171 = 291625757) B291625757
theorem B2593463 : Blo 1819611 2593463 := bstep (se 1 (by rfl) ⟨1945097, by rfl⟩ : syracuseStep 2593463 = 3890195) B3890195
theorem B9212615 : Blo 1819611 9212615 := bstep (se 1 (by rfl) ⟨6909461, by rfl⟩ : syracuseStep 9212615 = 13818923) B13818923
theorem B94565333 : Blo 1819611 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B6558695 : Blo 1819611 6558695 := bstep (se 1 (by rfl) ⟨4919021, by rfl⟩ : syracuseStep 6558695 = 9838043) B9838043
theorem B4609163 : Blo 1819611 4609163 := bstep (se 1 (by rfl) ⟨3456872, by rfl⟩ : syracuseStep 4609163 = 6913745) B6913745
theorem B3200143 : Blo 1819611 3200143 := bstep (se 1 (by rfl) ⟨2400107, by rfl⟩ : syracuseStep 3200143 = 4800215) B4800215
theorem B5256425 : Blo 1819611 5256425 := bstep (se 2 (by rfl) ⟨1971159, by rfl⟩ : syracuseStep 5256425 = 3942319) B3942319
theorem B9221363 : Blo 1819611 9221363 := bstep (se 1 (by rfl) ⟨6916022, by rfl⟩ : syracuseStep 9221363 = 13832045) B13832045
theorem B16602457 : Blo 1819611 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B3888479 : Blo 1819611 3888479 := bstep (se 1 (by rfl) ⟨2916359, by rfl⟩ : syracuseStep 3888479 = 5832719) B5832719
theorem B4150651 : Blo 1819611 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B19682693 : Blo 1819611 19682693 := bstep (se 4 (by rfl) ⟨1845252, by rfl⟩ : syracuseStep 19682693 = 3690505) B3690505
theorem B56841749 : Blo 1819611 56841749 := bstep (se 6 (by rfl) ⟨1332228, by rfl⟩ : syracuseStep 56841749 = 2664457) B2664457
theorem B4609619 : Blo 1819611 4609619 := bstep (se 1 (by rfl) ⟨3457214, by rfl⟩ : syracuseStep 4609619 = 6914429) B6914429
theorem B3454625 : Blo 1819611 3454625 := bstep (se 2 (by rfl) ⟨1295484, by rfl⟩ : syracuseStep 3454625 = 2590969) B2590969
theorem B50517775 : Blo 1819611 50517775 := bstep (se 1 (by rfl) ⟨37888331, by rfl⟩ : syracuseStep 50517775 = 75776663) B75776663
theorem B7780151 : Blo 1819611 7780151 := bstep (se 1 (by rfl) ⟨5835113, by rfl⟩ : syracuseStep 7780151 = 11670227) B11670227
theorem B6911831 : Blo 1819611 6911831 := bstep (se 1 (by rfl) ⟨5183873, by rfl⟩ : syracuseStep 6911831 = 10367747) B10367747
theorem B47298455 : Blo 1819611 47298455 := bstep (se 1 (by rfl) ⟨35473841, by rfl⟩ : syracuseStep 47298455 = 70947683) B70947683
theorem B26245093 : Blo 1819611 26245093 := bstep (se 4 (by rfl) ⟨2460477, by rfl⟩ : syracuseStep 26245093 = 4920955) B4920955
theorem B5830937 : Blo 1819611 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B4094315 : Blo 1819611 4094315 := bstep (se 1 (by rfl) ⟨3070736, by rfl⟩ : syracuseStep 4094315 = 6141473) B6141473
theorem B3455399 : Blo 1819611 3455399 := bstep (se 1 (by rfl) ⟨2591549, by rfl⟩ : syracuseStep 3455399 = 5183099) B5183099
theorem B4610479 : Blo 1819611 4610479 := bstep (se 1 (by rfl) ⟨3457859, by rfl⟩ : syracuseStep 4610479 = 6915719) B6915719
theorem B6142391 : Blo 1819611 6142391 := bstep (se 1 (by rfl) ⟨4606793, by rfl⟩ : syracuseStep 6142391 = 9213587) B9213587
theorem B4094459 : Blo 1819611 4094459 := bstep (se 1 (by rfl) ⟨3070844, by rfl⟩ : syracuseStep 4094459 = 6141689) B6141689
theorem B7772735 : Blo 1819611 7772735 := bstep (se 1 (by rfl) ⟨5829551, by rfl⟩ : syracuseStep 7772735 = 11659103) B11659103
theorem B3455551 : Blo 1819611 3455551 := bstep (se 1 (by rfl) ⟨2591663, by rfl⟩ : syracuseStep 3455551 = 5183327) B5183327
theorem B9845327 : Blo 1819611 9845327 := bstep (se 1 (by rfl) ⟨7383995, by rfl⟩ : syracuseStep 9845327 = 14767991) B14767991
theorem B4094585 : Blo 1819611 4094585 := bstep (se 2 (by rfl) ⟨1535469, by rfl⟩ : syracuseStep 4094585 = 3070939) B3070939
theorem B13826699 : Blo 1819611 13826699 := bstep (se 1 (by rfl) ⟨10370024, by rfl⟩ : syracuseStep 13826699 = 20740049) B20740049
theorem B4094639 : Blo 1819611 4094639 := bstep (se 1 (by rfl) ⟨3070979, by rfl⟩ : syracuseStep 4094639 = 6141959) B6141959
theorem B4610783 : Blo 1819611 4610783 := bstep (se 1 (by rfl) ⟨3458087, by rfl⟩ : syracuseStep 4610783 = 6916175) B6916175
theorem B4094711 : Blo 1819611 4094711 := bstep (se 1 (by rfl) ⟨3071033, by rfl⟩ : syracuseStep 4094711 = 6142067) B6142067
theorem B8870647 : Blo 1819611 8870647 := bstep (se 1 (by rfl) ⟨6652985, by rfl⟩ : syracuseStep 8870647 = 13305971) B13305971
theorem B3889939 : Blo 1819611 3889939 := bstep (se 1 (by rfl) ⟨2917454, by rfl⟩ : syracuseStep 3889939 = 5834909) B5834909
theorem B4094891 : Blo 1819611 4094891 := bstep (se 1 (by rfl) ⟨3071168, by rfl⟩ : syracuseStep 4094891 = 6142337) B6142337
theorem B4922491 : Blo 1819611 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B3071209 : Blo 1819611 3071209 := bstep (se 2 (by rfl) ⟨1151703, by rfl⟩ : syracuseStep 3071209 = 2303407) B2303407
theorem B3071263 : Blo 1819611 3071263 := bstep (se 1 (by rfl) ⟨2303447, by rfl⟩ : syracuseStep 3071263 = 4606895) B4606895
theorem B9215369 : Blo 1819611 9215369 := bstep (se 2 (by rfl) ⟨3455763, by rfl⟩ : syracuseStep 9215369 = 6911527) B6911527
theorem B6561161 : Blo 1819611 6561161 := bstep (se 2 (by rfl) ⟨2460435, by rfl⟩ : syracuseStep 6561161 = 4920871) B4920871
theorem B4095431 : Blo 1819611 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B5184967 : Blo 1819611 5184967 := bstep (se 1 (by rfl) ⟨3888725, by rfl⟩ : syracuseStep 5184967 = 7777451) B7777451
theorem B14040535 : Blo 1819611 14040535 := bstep (se 1 (by rfl) ⟨10530401, by rfl⟩ : syracuseStep 14040535 = 21060803) B21060803
theorem B3456607 : Blo 1819611 3456607 := bstep (se 1 (by rfl) ⟨2592455, by rfl⟩ : syracuseStep 3456607 = 5184911) B5184911
theorem B26590837 : Blo 1819611 26590837 := bstep (se 5 (by rfl) ⟨1246445, by rfl⟩ : syracuseStep 26590837 = 2492891) B2492891
theorem B3071675 : Blo 1819611 3071675 := bstep (se 1 (by rfl) ⟨2303756, by rfl⟩ : syracuseStep 3071675 = 4607513) B4607513
theorem B79806167 : Blo 1819611 79806167 := bstep (se 1 (by rfl) ⟨59854625, by rfl⟩ : syracuseStep 79806167 = 119709251) B119709251
theorem B2047711 : Blo 1819611 2047711 := bstep (se 1 (by rfl) ⟨1535783, by rfl⟩ : syracuseStep 2047711 = 3071567) B3071567
theorem B2916103 : Blo 1819611 2916103 := bstep (se 1 (by rfl) ⟨2187077, by rfl⟩ : syracuseStep 2916103 = 4374155) B4374155
theorem B4095791 : Blo 1819611 4095791 := bstep (se 1 (by rfl) ⟨3071843, by rfl⟩ : syracuseStep 4095791 = 6143687) B6143687
theorem B4210537 : Blo 1819611 4210537 := bstep (se 2 (by rfl) ⟨1578951, by rfl⟩ : syracuseStep 4210537 = 3157903) B3157903
theorem B2334619 : Blo 1819611 2334619 := bstep (se 1 (by rfl) ⟨1750964, by rfl⟩ : syracuseStep 2334619 = 3501929) B3501929
theorem B8101927 : Blo 1819611 8101927 := bstep (se 1 (by rfl) ⟨6076445, by rfl⟩ : syracuseStep 8101927 = 12152891) B12152891
theorem B5832935 : Blo 1819611 5832935 := bstep (se 1 (by rfl) ⟨4374701, by rfl⟩ : syracuseStep 5832935 = 8749403) B8749403
theorem B6144281 : Blo 1819611 6144281 := bstep (se 2 (by rfl) ⟨2304105, by rfl⟩ : syracuseStep 6144281 = 4608211) B4608211
theorem B6144443 : Blo 1819611 6144443 := bstep (se 1 (by rfl) ⟨4608332, by rfl⟩ : syracuseStep 6144443 = 9216665) B9216665
theorem B11076047 : Blo 1819611 11076047 := bstep (se 1 (by rfl) ⟨8307035, by rfl⟩ : syracuseStep 11076047 = 16614071) B16614071
theorem B3072505 : Blo 1819611 3072505 := bstep (se 2 (by rfl) ⟨1152189, by rfl⟩ : syracuseStep 3072505 = 2304379) B2304379
theorem B14017133 : Blo 1819611 14017133 := bstep (se 3 (by rfl) ⟨2628212, by rfl⟩ : syracuseStep 14017133 = 5256425) B5256425
theorem B3072775 : Blo 1819611 3072775 := bstep (se 1 (by rfl) ⟨2304581, by rfl⟩ : syracuseStep 3072775 = 4609163) B4609163
theorem B3072809 : Blo 1819611 3072809 := bstep (se 2 (by rfl) ⟨1152303, by rfl⟩ : syracuseStep 3072809 = 2304607) B2304607
theorem B6226799 : Blo 1819611 6226799 := bstep (se 1 (by rfl) ⟨4670099, by rfl⟩ : syracuseStep 6226799 = 9340199) B9340199
theorem B2048935 : Blo 1819611 2048935 := bstep (se 1 (by rfl) ⟨1536701, by rfl⟩ : syracuseStep 2048935 = 3073403) B3073403
theorem B34988993 : Blo 1819611 34988993 := bstep (se 2 (by rfl) ⟨13120872, by rfl⟩ : syracuseStep 34988993 = 26241745) B26241745
theorem B4096979 : Blo 1819611 4096979 := bstep (se 1 (by rfl) ⟨3072734, by rfl⟩ : syracuseStep 4096979 = 6145469) B6145469
theorem B1819643 : Blo 1819611 1819643 := bstep (se 1 (by rfl) ⟨1364732, by rfl⟩ : syracuseStep 1819643 = 2729465) B2729465
theorem B7005209 : Blo 1819611 7005209 := bstep (se 2 (by rfl) ⟨2626953, by rfl⟩ : syracuseStep 7005209 = 5253907) B5253907
theorem B5186585 : Blo 1819611 5186585 := bstep (se 2 (by rfl) ⟨1944969, by rfl⟩ : syracuseStep 5186585 = 3889939) B3889939
theorem B3073079 : Blo 1819611 3073079 := bstep (se 1 (by rfl) ⟨2304809, by rfl⟩ : syracuseStep 3073079 = 4609619) B4609619
theorem B1819711 : Blo 1819611 1819711 := bstep (se 1 (by rfl) ⟨1364783, by rfl⟩ : syracuseStep 1819711 = 2729567) B2729567
theorem B11666537 : Blo 1819611 11666537 := bstep (se 2 (by rfl) ⟨4374951, by rfl⟩ : syracuseStep 11666537 = 8749903) B8749903
theorem B2303083 : Blo 1819611 2303083 := bstep (se 1 (by rfl) ⟨1727312, by rfl⟩ : syracuseStep 2303083 = 3454625) B3454625
theorem B1819855 : Blo 1819611 1819855 := bstep (se 1 (by rfl) ⟨1364891, by rfl⟩ : syracuseStep 1819855 = 2729783) B2729783
theorem B4097231 : Blo 1819611 4097231 := bstep (se 1 (by rfl) ⟨3072923, by rfl⟩ : syracuseStep 4097231 = 6145847) B6145847
theorem B5186767 : Blo 1819611 5186767 := bstep (se 1 (by rfl) ⟨3890075, by rfl⟩ : syracuseStep 5186767 = 7780151) B7780151
theorem B31532303 : Blo 1819611 31532303 := bstep (se 1 (by rfl) ⟨23649227, by rfl⟩ : syracuseStep 31532303 = 47298455) B47298455
theorem B6915401 : Blo 1819611 6915401 := bstep (se 2 (by rfl) ⟨2593275, by rfl⟩ : syracuseStep 6915401 = 5186551) B5186551
theorem B1820059 : Blo 1819611 1820059 := bstep (se 1 (by rfl) ⟨1365044, by rfl⟩ : syracuseStep 1820059 = 2730089) B2730089
theorem B269428133 : Blo 1819611 269428133 := bstep (se 4 (by rfl) ⟨25258887, by rfl⟩ : syracuseStep 269428133 = 50517775) B50517775
theorem B6563321 : Blo 1819611 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B4097555 : Blo 1819611 4097555 := bstep (se 1 (by rfl) ⟨3073166, by rfl⟩ : syracuseStep 4097555 = 6146333) B6146333
theorem B2729543 : Blo 1819611 2729543 := bstep (se 1 (by rfl) ⟨2047157, by rfl⟩ : syracuseStep 2729543 = 4094315) B4094315
theorem B6145631 : Blo 1819611 6145631 := bstep (se 1 (by rfl) ⟨4609223, by rfl⟩ : syracuseStep 6145631 = 9218447) B9218447
theorem B1820271 : Blo 1819611 1820271 := bstep (se 1 (by rfl) ⟨1365203, by rfl⟩ : syracuseStep 1820271 = 2730407) B2730407
theorem B6227567 : Blo 1819611 6227567 := bstep (se 1 (by rfl) ⟨4670675, by rfl⟩ : syracuseStep 6227567 = 9341351) B9341351
theorem B2729639 : Blo 1819611 2729639 := bstep (se 1 (by rfl) ⟨2047229, by rfl⟩ : syracuseStep 2729639 = 4094459) B4094459
theorem B1820327 : Blo 1819611 1820327 := bstep (se 1 (by rfl) ⟨1365245, by rfl⟩ : syracuseStep 1820327 = 2730491) B2730491
theorem B2729723 : Blo 1819611 2729723 := bstep (se 1 (by rfl) ⟨2047292, by rfl⟩ : syracuseStep 2729723 = 4094585) B4094585
theorem B1820411 : Blo 1819611 1820411 := bstep (se 1 (by rfl) ⟨1365308, by rfl⟩ : syracuseStep 1820411 = 2730617) B2730617
theorem B9217799 : Blo 1819611 9217799 := bstep (se 1 (by rfl) ⟨6913349, by rfl⟩ : syracuseStep 9217799 = 13826699) B13826699
theorem B2729759 : Blo 1819611 2729759 := bstep (se 1 (by rfl) ⟨2047319, by rfl⟩ : syracuseStep 2729759 = 4094639) B4094639
theorem B1820447 : Blo 1819611 1820447 := bstep (se 1 (by rfl) ⟨1365335, by rfl⟩ : syracuseStep 1820447 = 2730671) B2730671
theorem B22136609 : Blo 1819611 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B6915901 : Blo 1819611 6915901 := bstep (se 3 (by rfl) ⟨1296731, by rfl⟩ : syracuseStep 6915901 = 2593463) B2593463
theorem B1820479 : Blo 1819611 1820479 := bstep (se 1 (by rfl) ⟨1365359, by rfl⟩ : syracuseStep 1820479 = 2730719) B2730719
theorem B3073855 : Blo 1819611 3073855 := bstep (se 1 (by rfl) ⟨2305391, by rfl⟩ : syracuseStep 3073855 = 4610783) B4610783
theorem B2729807 : Blo 1819611 2729807 := bstep (se 1 (by rfl) ⟨2047355, by rfl⟩ : syracuseStep 2729807 = 4094711) B4094711
theorem B2729927 : Blo 1819611 2729927 := bstep (se 1 (by rfl) ⟨2047445, by rfl⟩ : syracuseStep 2729927 = 4094891) B4094891
theorem B18720713 : Blo 1819611 18720713 := bstep (se 2 (by rfl) ⟨7020267, by rfl⟩ : syracuseStep 18720713 = 14040535) B14040535
theorem B1820655 : Blo 1819611 1820655 := bstep (se 1 (by rfl) ⟨1365491, by rfl⟩ : syracuseStep 1820655 = 2730983) B2730983
theorem B4605943 : Blo 1819611 4605943 := bstep (se 1 (by rfl) ⟨3454457, by rfl⟩ : syracuseStep 4605943 = 6908915) B6908915
theorem B2459641 : Blo 1819611 2459641 := bstep (se 2 (by rfl) ⟨922365, by rfl⟩ : syracuseStep 2459641 = 1844731) B1844731
theorem B4376567 : Blo 1819611 4376567 := bstep (se 1 (by rfl) ⟨3282425, by rfl⟩ : syracuseStep 4376567 = 6564851) B6564851
theorem B1820827 : Blo 1819611 1820827 := bstep (se 1 (by rfl) ⟨1365620, by rfl⟩ : syracuseStep 1820827 = 2731241) B2731241
theorem B1820863 : Blo 1819611 1820863 := bstep (se 1 (by rfl) ⟨1365647, by rfl⟩ : syracuseStep 1820863 = 2731295) B2731295
theorem B6654143 : Blo 1819611 6654143 := bstep (se 1 (by rfl) ⟨4990607, by rfl⟩ : syracuseStep 6654143 = 9981215) B9981215
theorem B4098239 : Blo 1819611 4098239 := bstep (se 1 (by rfl) ⟨3073679, by rfl⟩ : syracuseStep 4098239 = 6147359) B6147359
theorem B4606247 : Blo 1819611 4606247 := bstep (se 1 (by rfl) ⟨3454685, by rfl⟩ : syracuseStep 4606247 = 6909371) B6909371
theorem B2730281 : Blo 1819611 2730281 := bstep (se 2 (by rfl) ⟨1023855, by rfl⟩ : syracuseStep 2730281 = 2047711) B2047711
theorem B2730287 : Blo 1819611 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B1820975 : Blo 1819611 1820975 := bstep (se 1 (by rfl) ⟨1365731, by rfl⟩ : syracuseStep 1820975 = 2731463) B2731463
theorem B5614049 : Blo 1819611 5614049 := bstep (se 2 (by rfl) ⟨2105268, by rfl⟩ : syracuseStep 5614049 = 4210537) B4210537
theorem B1821211 : Blo 1819611 1821211 := bstep (se 1 (by rfl) ⟨1365908, by rfl⟩ : syracuseStep 1821211 = 2731817) B2731817
theorem B2730527 : Blo 1819611 2730527 := bstep (se 1 (by rfl) ⟨2047895, by rfl⟩ : syracuseStep 2730527 = 4095791) B4095791
theorem B1821215 : Blo 1819611 1821215 := bstep (se 1 (by rfl) ⟨1365911, by rfl⟩ : syracuseStep 1821215 = 2731823) B2731823
theorem B25266761 : Blo 1819611 25266761 := bstep (se 2 (by rfl) ⟨9475035, by rfl⟩ : syracuseStep 25266761 = 18950071) B18950071
theorem B1821531 : Blo 1819611 1821531 := bstep (se 1 (by rfl) ⟨1366148, by rfl⟩ : syracuseStep 1821531 = 2732297) B2732297
theorem B2730911 : Blo 1819611 2730911 := bstep (se 1 (by rfl) ⟨2048183, by rfl⟩ : syracuseStep 2730911 = 4096367) B4096367
theorem B1821599 : Blo 1819611 1821599 := bstep (se 1 (by rfl) ⟨1366199, by rfl⟩ : syracuseStep 1821599 = 2732399) B2732399
theorem B13831073 : Blo 1819611 13831073 := bstep (se 2 (by rfl) ⟨5186652, by rfl⟩ : syracuseStep 13831073 = 10373305) B10373305
theorem B2730959 : Blo 1819611 2730959 := bstep (se 1 (by rfl) ⟨2048219, by rfl⟩ : syracuseStep 2730959 = 4096439) B4096439
theorem B6147035 : Blo 1819611 6147035 := bstep (se 1 (by rfl) ⟨4610276, by rfl⟩ : syracuseStep 6147035 = 9220553) B9220553
theorem B2731049 : Blo 1819611 2731049 := bstep (se 2 (by rfl) ⟨1024143, by rfl⟩ : syracuseStep 2731049 = 2048287) B2048287
theorem B2731055 : Blo 1819611 2731055 := bstep (se 1 (by rfl) ⟨2048291, by rfl⟩ : syracuseStep 2731055 = 4096583) B4096583
theorem B2731079 : Blo 1819611 2731079 := bstep (se 1 (by rfl) ⟨2048309, by rfl⟩ : syracuseStep 2731079 = 4096619) B4096619
theorem B6147305 : Blo 1819611 6147305 := bstep (se 2 (by rfl) ⟨2305239, by rfl⟩ : syracuseStep 6147305 = 4610479) B4610479
theorem B2731343 : Blo 1819611 2731343 := bstep (se 1 (by rfl) ⟨2048507, by rfl⟩ : syracuseStep 2731343 = 4097015) B4097015
theorem B4607401 : Blo 1819611 4607401 := bstep (se 2 (by rfl) ⟨1727775, by rfl⟩ : syracuseStep 4607401 = 3455551) B3455551
theorem B2731433 : Blo 1819611 2731433 := bstep (se 2 (by rfl) ⟨1024287, by rfl⟩ : syracuseStep 2731433 = 2048575) B2048575
theorem B6147575 : Blo 1819611 6147575 := bstep (se 1 (by rfl) ⟨4610681, by rfl⟩ : syracuseStep 6147575 = 9221363) B9221363
theorem B2592319 : Blo 1819611 2592319 := bstep (se 1 (by rfl) ⟨1944239, by rfl⟩ : syracuseStep 2592319 = 3888479) B3888479
theorem B2731583 : Blo 1819611 2731583 := bstep (se 1 (by rfl) ⟨2048687, by rfl⟩ : syracuseStep 2731583 = 4097375) B4097375
theorem B2731847 : Blo 1819611 2731847 := bstep (se 1 (by rfl) ⟨2048885, by rfl⟩ : syracuseStep 2731847 = 4097771) B4097771
theorem B4607887 : Blo 1819611 4607887 := bstep (se 1 (by rfl) ⟨3455915, by rfl⟩ : syracuseStep 4607887 = 6911831) B6911831
theorem B2731931 : Blo 1819611 2731931 := bstep (se 1 (by rfl) ⟨2048948, by rfl⟩ : syracuseStep 2731931 = 4097897) B4097897
theorem B3887291 : Blo 1819611 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B22147415 : Blo 1819611 22147415 := bstep (se 1 (by rfl) ⟨16610561, by rfl⟩ : syracuseStep 22147415 = 33221123) B33221123
theorem B5181823 : Blo 1819611 5181823 := bstep (se 1 (by rfl) ⟨3886367, by rfl⟩ : syracuseStep 5181823 = 7772735) B7772735
theorem B8532361 : Blo 1819611 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B5534201 : Blo 1819611 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B5534287 : Blo 1819611 5534287 := bstep (se 1 (by rfl) ⟨4150715, by rfl⟩ : syracuseStep 5534287 = 8301431) B8301431
theorem B4608809 : Blo 1819611 4608809 := bstep (se 2 (by rfl) ⟨1728303, by rfl⟩ : syracuseStep 4608809 = 3456607) B3456607
theorem B2593577 : Blo 1819611 2593577 := bstep (se 2 (by rfl) ⟨972591, by rfl⟩ : syracuseStep 2593577 = 1945183) B1945183
theorem B3888137 : Blo 1819611 3888137 := bstep (se 2 (by rfl) ⟨1458051, by rfl⟩ : syracuseStep 3888137 = 2916103) B2916103
theorem B53204111 : Blo 1819611 53204111 := bstep (se 1 (by rfl) ⟨39903083, by rfl⟩ : syracuseStep 53204111 = 79806167) B79806167
theorem B6141203 : Blo 1819611 6141203 := bstep (se 1 (by rfl) ⟨4605902, by rfl⟩ : syracuseStep 6141203 = 9211805) B9211805
theorem B34993457 : Blo 1819611 34993457 := bstep (se 2 (by rfl) ⟨13122546, by rfl⟩ : syracuseStep 34993457 = 26245093) B26245093
theorem B14759425 : Blo 1819611 14759425 := bstep (se 2 (by rfl) ⟨5534784, by rfl⟩ : syracuseStep 14759425 = 11069569) B11069569
theorem B3282599 : Blo 1819611 3282599 := bstep (se 1 (by rfl) ⟨2461949, by rfl⟩ : syracuseStep 3282599 = 4923899) B4923899
theorem B129611447 : Blo 1819611 129611447 := bstep (se 1 (by rfl) ⟨97208585, by rfl⟩ : syracuseStep 129611447 = 194417171) B194417171
theorem B7780049 : Blo 1819611 7780049 := bstep (se 2 (by rfl) ⟨2917518, by rfl⟩ : syracuseStep 7780049 = 5835037) B5835037
theorem B6141743 : Blo 1819611 6141743 := bstep (se 1 (by rfl) ⟨4606307, by rfl⟩ : syracuseStep 6141743 = 9212615) B9212615
theorem B9213911 : Blo 1819611 9213911 := bstep (se 1 (by rfl) ⟨6910433, by rfl⟩ : syracuseStep 9213911 = 13820867) B13820867
theorem B4372463 : Blo 1819611 4372463 := bstep (se 1 (by rfl) ⟨3279347, by rfl⟩ : syracuseStep 4372463 = 6558695) B6558695
theorem B13817951 : Blo 1819611 13817951 := bstep (se 1 (by rfl) ⟨10363463, by rfl⟩ : syracuseStep 13817951 = 20726927) B20726927
theorem B3692639 : Blo 1819611 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B13121795 : Blo 1819611 13121795 := bstep (se 1 (by rfl) ⟨9841346, by rfl⟩ : syracuseStep 13121795 = 19682693) B19682693
theorem B11827529 : Blo 1819611 11827529 := bstep (se 2 (by rfl) ⟨4435323, by rfl⟩ : syracuseStep 11827529 = 8870647) B8870647
theorem B37894499 : Blo 1819611 37894499 := bstep (se 1 (by rfl) ⟨28420874, by rfl⟩ : syracuseStep 37894499 = 56841749) B56841749
theorem B5183851 : Blo 1819611 5183851 := bstep (se 1 (by rfl) ⟨3887888, by rfl⟩ : syracuseStep 5183851 = 7775777) B7775777
theorem B9345455 : Blo 1819611 9345455 := bstep (se 1 (by rfl) ⟨7009091, by rfl⟩ : syracuseStep 9345455 = 14018183) B14018183
theorem B9214397 : Blo 1819611 9214397 := bstep (se 3 (by rfl) ⟨1727699, by rfl⟩ : syracuseStep 9214397 = 3455399) B3455399
theorem B3070811 : Blo 1819611 3070811 := bstep (se 1 (by rfl) ⟨2303108, by rfl⟩ : syracuseStep 3070811 = 4606217) B4606217
theorem B4266857 : Blo 1819611 4266857 := bstep (se 2 (by rfl) ⟨1600071, by rfl⟩ : syracuseStep 4266857 = 3200143) B3200143
theorem B26254205 : Blo 1819611 26254205 := bstep (se 3 (by rfl) ⟨4922663, by rfl⟩ : syracuseStep 26254205 = 9845327) B9845327
theorem B4094927 : Blo 1819611 4094927 := bstep (se 1 (by rfl) ⟨3071195, by rfl⟩ : syracuseStep 4094927 = 6142391) B6142391
theorem B4094945 : Blo 1819611 4094945 := bstep (se 2 (by rfl) ⟨1535604, by rfl⟩ : syracuseStep 4094945 = 3071209) B3071209
theorem B4095017 : Blo 1819611 4095017 := bstep (se 2 (by rfl) ⟨1535631, by rfl⟩ : syracuseStep 4095017 = 3071263) B3071263
theorem B3071047 : Blo 1819611 3071047 := bstep (se 1 (by rfl) ⟨2303285, by rfl⟩ : syracuseStep 3071047 = 4606571) B4606571
theorem B3456265 : Blo 1819611 3456265 := bstep (se 2 (by rfl) ⟨1296099, by rfl⟩ : syracuseStep 3456265 = 2592199) B2592199
theorem B6913289 : Blo 1819611 6913289 := bstep (se 2 (by rfl) ⟨2592483, by rfl⟩ : syracuseStep 6913289 = 5184967) B5184967
theorem B35454449 : Blo 1819611 35454449 := bstep (se 2 (by rfl) ⟨13295418, by rfl⟩ : syracuseStep 35454449 = 26590837) B26590837
theorem B3071479 : Blo 1819611 3071479 := bstep (se 1 (by rfl) ⟨2303609, by rfl⟩ : syracuseStep 3071479 = 4607219) B4607219
theorem B6143579 : Blo 1819611 6143579 := bstep (se 1 (by rfl) ⟨4607684, by rfl⟩ : syracuseStep 6143579 = 9215369) B9215369
theorem B4374107 : Blo 1819611 4374107 := bstep (se 1 (by rfl) ⟨3280580, by rfl⟩ : syracuseStep 4374107 = 6561161) B6561161
theorem B2047783 : Blo 1819611 2047783 := bstep (se 1 (by rfl) ⟨1535837, by rfl⟩ : syracuseStep 2047783 = 3071675) B3071675
theorem B3071783 : Blo 1819611 3071783 := bstep (se 1 (by rfl) ⟨2303837, by rfl⟩ : syracuseStep 3071783 = 4607675) B4607675
theorem B3112825 : Blo 1819611 3112825 := bstep (se 2 (by rfl) ⟨1167309, by rfl⟩ : syracuseStep 3112825 = 2334619) B2334619
theorem B252174221 : Blo 1819611 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B78716933 : Blo 1819611 78716933 := bstep (se 4 (by rfl) ⟨7379712, by rfl⟩ : syracuseStep 78716933 = 14759425) B14759425
theorem B4096187 : Blo 1819611 4096187 := bstep (se 1 (by rfl) ⟨3072140, by rfl⟩ : syracuseStep 4096187 = 6144281) B6144281
theorem B4096295 : Blo 1819611 4096295 := bstep (se 1 (by rfl) ⟨3072221, by rfl⟩ : syracuseStep 4096295 = 6144443) B6144443
theorem B29516197 : Blo 1819611 29516197 := bstep (se 4 (by rfl) ⟨2767143, by rfl⟩ : syracuseStep 29516197 = 5534287) B5534287
theorem B3072539 : Blo 1819611 3072539 := bstep (se 1 (by rfl) ⟨2304404, by rfl⟩ : syracuseStep 3072539 = 4608809) B4608809
theorem B2048539 : Blo 1819611 2048539 := bstep (se 1 (by rfl) ⟨1536404, by rfl⟩ : syracuseStep 2048539 = 3072809) B3072809
theorem B4096673 : Blo 1819611 4096673 := bstep (se 2 (by rfl) ⟨1536252, by rfl⟩ : syracuseStep 4096673 = 3072505) B3072505
theorem B3457723 : Blo 1819611 3457723 := bstep (se 1 (by rfl) ⟨2593292, by rfl⟩ : syracuseStep 3457723 = 5186585) B5186585
theorem B2048719 : Blo 1819611 2048719 := bstep (se 1 (by rfl) ⟨1536539, by rfl⟩ : syracuseStep 2048719 = 3073079) B3073079
theorem B21021535 : Blo 1819611 21021535 := bstep (se 1 (by rfl) ⟨15766151, by rfl⟩ : syracuseStep 21021535 = 31532303) B31532303
theorem B179618755 : Blo 1819611 179618755 := bstep (se 1 (by rfl) ⟨134714066, by rfl⟩ : syracuseStep 179618755 = 269428133) B269428133
theorem B4375547 : Blo 1819611 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B4097033 : Blo 1819611 4097033 := bstep (se 2 (by rfl) ⟨1536387, by rfl⟩ : syracuseStep 4097033 = 3072775) B3072775
theorem B1819695 : Blo 1819611 1819695 := bstep (se 1 (by rfl) ⟨1364771, by rfl⟩ : syracuseStep 1819695 = 2729543) B2729543
theorem B4097087 : Blo 1819611 4097087 := bstep (se 1 (by rfl) ⟨3072815, by rfl⟩ : syracuseStep 4097087 = 6145631) B6145631
theorem B1819759 : Blo 1819611 1819759 := bstep (se 1 (by rfl) ⟨1364819, by rfl⟩ : syracuseStep 1819759 = 2729639) B2729639
theorem B2188399 : Blo 1819611 2188399 := bstep (se 1 (by rfl) ⟨1641299, by rfl⟩ : syracuseStep 2188399 = 3282599) B3282599
theorem B5186699 : Blo 1819611 5186699 := bstep (se 1 (by rfl) ⟨3890024, by rfl⟩ : syracuseStep 5186699 = 7780049) B7780049
theorem B1819815 : Blo 1819611 1819815 := bstep (se 1 (by rfl) ⟨1364861, by rfl⟩ : syracuseStep 1819815 = 2729723) B2729723
theorem B6145199 : Blo 1819611 6145199 := bstep (se 1 (by rfl) ⟨4608899, by rfl⟩ : syracuseStep 6145199 = 9217799) B9217799
theorem B1819839 : Blo 1819611 1819839 := bstep (se 1 (by rfl) ⟨1364879, by rfl⟩ : syracuseStep 1819839 = 2729759) B2729759
theorem B1819871 : Blo 1819611 1819871 := bstep (se 1 (by rfl) ⟨1364903, by rfl⟩ : syracuseStep 1819871 = 2729807) B2729807
theorem B1819951 : Blo 1819611 1819951 := bstep (se 1 (by rfl) ⟨1364963, by rfl⟩ : syracuseStep 1819951 = 2729927) B2729927
theorem B2917711 : Blo 1819611 2917711 := bstep (se 1 (by rfl) ⟨2188283, by rfl⟩ : syracuseStep 2917711 = 4376567) B4376567
theorem B1820187 : Blo 1819611 1820187 := bstep (se 1 (by rfl) ⟨1365140, by rfl⟩ : syracuseStep 1820187 = 2730281) B2730281
theorem B1820191 : Blo 1819611 1820191 := bstep (se 1 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 1820191 = 2730287) B2730287
theorem B6915689 : Blo 1819611 6915689 := bstep (se 2 (by rfl) ⟨2593383, by rfl⟩ : syracuseStep 6915689 = 5186767) B5186767
theorem B1820351 : Blo 1819611 1820351 := bstep (se 1 (by rfl) ⟨1365263, by rfl⟩ : syracuseStep 1820351 = 2730527) B2730527
theorem B16844507 : Blo 1819611 16844507 := bstep (se 1 (by rfl) ⟨12633380, by rfl⟩ : syracuseStep 16844507 = 25266761) B25266761
theorem B2844571 : Blo 1819611 2844571 := bstep (se 1 (by rfl) ⟨2133428, by rfl⟩ : syracuseStep 2844571 = 4266857) B4266857
theorem B1820607 : Blo 1819611 1820607 := bstep (se 1 (by rfl) ⟨1365455, by rfl⟩ : syracuseStep 1820607 = 2730911) B2730911
theorem B2729951 : Blo 1819611 2729951 := bstep (se 1 (by rfl) ⟨2047463, by rfl⟩ : syracuseStep 2729951 = 4094927) B4094927
theorem B1820639 : Blo 1819611 1820639 := bstep (se 1 (by rfl) ⟨1365479, by rfl⟩ : syracuseStep 1820639 = 2730959) B2730959
theorem B4098023 : Blo 1819611 4098023 := bstep (se 1 (by rfl) ⟨3073517, by rfl⟩ : syracuseStep 4098023 = 6147035) B6147035
theorem B2729963 : Blo 1819611 2729963 := bstep (se 1 (by rfl) ⟨2047472, by rfl⟩ : syracuseStep 2729963 = 4094945) B4094945
theorem B2730011 : Blo 1819611 2730011 := bstep (se 1 (by rfl) ⟨2047508, by rfl⟩ : syracuseStep 2730011 = 4095017) B4095017
theorem B1820699 : Blo 1819611 1820699 := bstep (se 1 (by rfl) ⟨1365524, by rfl⟩ : syracuseStep 1820699 = 2731049) B2731049
theorem B1820703 : Blo 1819611 1820703 := bstep (se 1 (by rfl) ⟨1365527, by rfl⟩ : syracuseStep 1820703 = 2731055) B2731055
theorem B1820719 : Blo 1819611 1820719 := bstep (se 1 (by rfl) ⟨1365539, by rfl⟩ : syracuseStep 1820719 = 2731079) B2731079
theorem B6916205 : Blo 1819611 6916205 := bstep (se 3 (by rfl) ⟨1296788, by rfl⟩ : syracuseStep 6916205 = 2593577) B2593577
theorem B4098203 : Blo 1819611 4098203 := bstep (se 1 (by rfl) ⟨3073652, by rfl⟩ : syracuseStep 4098203 = 6147305) B6147305
theorem B1820895 : Blo 1819611 1820895 := bstep (se 1 (by rfl) ⟨1365671, by rfl⟩ : syracuseStep 1820895 = 2731343) B2731343
theorem B1820955 : Blo 1819611 1820955 := bstep (se 1 (by rfl) ⟨1365716, by rfl⟩ : syracuseStep 1820955 = 2731433) B2731433
theorem B23636299 : Blo 1819611 23636299 := bstep (se 1 (by rfl) ⟨17727224, by rfl⟩ : syracuseStep 23636299 = 35454449) B35454449
theorem B4098383 : Blo 1819611 4098383 := bstep (se 1 (by rfl) ⟨3073787, by rfl⟩ : syracuseStep 4098383 = 6147575) B6147575
theorem B1821055 : Blo 1819611 1821055 := bstep (se 1 (by rfl) ⟨1365791, by rfl⟩ : syracuseStep 1821055 = 2731583) B2731583
theorem B2730377 : Blo 1819611 2730377 := bstep (se 2 (by rfl) ⟨1023891, by rfl⟩ : syracuseStep 2730377 = 2047783) B2047783
theorem B4098473 : Blo 1819611 4098473 := bstep (se 2 (by rfl) ⟨1536927, by rfl⟩ : syracuseStep 4098473 = 3073855) B3073855
theorem B1821231 : Blo 1819611 1821231 := bstep (se 1 (by rfl) ⟨1365923, by rfl⟩ : syracuseStep 1821231 = 2731847) B2731847
theorem B1821287 : Blo 1819611 1821287 := bstep (se 1 (by rfl) ⟨1365965, by rfl⟩ : syracuseStep 1821287 = 2731931) B2731931
theorem B3279521 : Blo 1819611 3279521 := bstep (se 2 (by rfl) ⟨1229820, by rfl⟩ : syracuseStep 3279521 = 2459641) B2459641
theorem B18680557 : Blo 1819611 18680557 := bstep (se 3 (by rfl) ⟨3502604, by rfl⟩ : syracuseStep 18680557 = 7005209) B7005209
theorem B2591527 : Blo 1819611 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B14764943 : Blo 1819611 14764943 := bstep (se 1 (by rfl) ⟨11073707, by rfl⟩ : syracuseStep 14764943 = 22147415) B22147415
theorem B7384031 : Blo 1819611 7384031 := bstep (se 1 (by rfl) ⟨5538023, by rfl⟩ : syracuseStep 7384031 = 11076047) B11076047
theorem B6909097 : Blo 1819611 6909097 := bstep (se 2 (by rfl) ⟨2590911, by rfl⟩ : syracuseStep 6909097 = 5181823) B5181823
theorem B23325995 : Blo 1819611 23325995 := bstep (se 1 (by rfl) ⟨17494496, by rfl⟩ : syracuseStep 23325995 = 34988993) B34988993
theorem B2731319 : Blo 1819611 2731319 := bstep (se 1 (by rfl) ⟨2048489, by rfl⟩ : syracuseStep 2731319 = 4096979) B4096979
theorem B2592091 : Blo 1819611 2592091 := bstep (se 1 (by rfl) ⟨1944068, by rfl⟩ : syracuseStep 2592091 = 3888137) B3888137
theorem B34991453 : Blo 1819611 34991453 := bstep (se 3 (by rfl) ⟨6560897, by rfl⟩ : syracuseStep 34991453 = 13121795) B13121795
theorem B7777691 : Blo 1819611 7777691 := bstep (se 1 (by rfl) ⟨5833268, by rfl⟩ : syracuseStep 7777691 = 11666537) B11666537
theorem B2731487 : Blo 1819611 2731487 := bstep (se 1 (by rfl) ⟨2048615, by rfl⟩ : syracuseStep 2731487 = 4097231) B4097231
theorem B2731703 : Blo 1819611 2731703 := bstep (se 1 (by rfl) ⟨2048777, by rfl⟩ : syracuseStep 2731703 = 4097555) B4097555
theorem B2731913 : Blo 1819611 2731913 := bstep (se 2 (by rfl) ⟨1024467, by rfl⟩ : syracuseStep 2731913 = 2048935) B2048935
theorem B12480475 : Blo 1819611 12480475 := bstep (se 1 (by rfl) ⟨9360356, by rfl⟩ : syracuseStep 12480475 = 18720713) B18720713
theorem B14757869 : Blo 1819611 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B9211967 : Blo 1819611 9211967 := bstep (se 1 (by rfl) ⟨6908975, by rfl⟩ : syracuseStep 9211967 = 13817951) B13817951
theorem B2461759 : Blo 1819611 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B4436095 : Blo 1819611 4436095 := bstep (se 1 (by rfl) ⟨3327071, by rfl⟩ : syracuseStep 4436095 = 6654143) B6654143
theorem B2732159 : Blo 1819611 2732159 := bstep (se 1 (by rfl) ⟨2049119, by rfl⟩ : syracuseStep 2732159 = 4098239) B4098239
theorem B7885019 : Blo 1819611 7885019 := bstep (se 1 (by rfl) ⟨5913764, by rfl⟩ : syracuseStep 7885019 = 11827529) B11827529
theorem B6230303 : Blo 1819611 6230303 := bstep (se 1 (by rfl) ⟨4672727, by rfl⟩ : syracuseStep 6230303 = 9345455) B9345455
theorem B4608353 : Blo 1819611 4608353 := bstep (se 2 (by rfl) ⟨1728132, by rfl⟩ : syracuseStep 4608353 = 3456265) B3456265
theorem B17502803 : Blo 1819611 17502803 := bstep (se 1 (by rfl) ⟨13127102, by rfl⟩ : syracuseStep 17502803 = 26254205) B26254205
theorem B9220715 : Blo 1819611 9220715 := bstep (se 1 (by rfl) ⟨6915536, by rfl⟩ : syracuseStep 9220715 = 13831073) B13831073
theorem B4608859 : Blo 1819611 4608859 := bstep (se 1 (by rfl) ⟨3456644, by rfl⟩ : syracuseStep 4608859 = 6913289) B6913289
theorem B9221201 : Blo 1819611 9221201 := bstep (se 2 (by rfl) ⟨3457950, by rfl⟩ : syracuseStep 9221201 = 6915901) B6915901
theorem B4150433 : Blo 1819611 4150433 := bstep (se 2 (by rfl) ⟨1556412, by rfl⟩ : syracuseStep 4150433 = 3112825) B3112825
theorem B6141257 : Blo 1819611 6141257 := bstep (se 2 (by rfl) ⟨2302971, by rfl⟩ : syracuseStep 6141257 = 4605943) B4605943
theorem B10802569 : Blo 1819611 10802569 := bstep (se 2 (by rfl) ⟨4050963, by rfl⟩ : syracuseStep 10802569 = 8101927) B8101927
theorem B3888623 : Blo 1819611 3888623 := bstep (se 1 (by rfl) ⟨2916467, by rfl⟩ : syracuseStep 3888623 = 5832935) B5832935
theorem B9344755 : Blo 1819611 9344755 := bstep (se 1 (by rfl) ⟨7008566, by rfl⟩ : syracuseStep 9344755 = 14017133) B14017133
theorem B6911801 : Blo 1819611 6911801 := bstep (se 2 (by rfl) ⟨2591925, by rfl⟩ : syracuseStep 6911801 = 5183851) B5183851
theorem B35469407 : Blo 1819611 35469407 := bstep (se 1 (by rfl) ⟨26602055, by rfl⟩ : syracuseStep 35469407 = 53204111) B53204111
theorem B4094135 : Blo 1819611 4094135 := bstep (se 1 (by rfl) ⟨3070601, by rfl⟩ : syracuseStep 4094135 = 6141203) B6141203
theorem B23328971 : Blo 1819611 23328971 := bstep (se 1 (by rfl) ⟨17496728, by rfl⟩ : syracuseStep 23328971 = 34993457) B34993457
theorem B4610267 : Blo 1819611 4610267 := bstep (se 1 (by rfl) ⟨3457700, by rfl⟩ : syracuseStep 4610267 = 6915401) B6915401
theorem B4151711 : Blo 1819611 4151711 := bstep (se 1 (by rfl) ⟨3113783, by rfl⟩ : syracuseStep 4151711 = 6227567) B6227567
theorem B86407631 : Blo 1819611 86407631 := bstep (se 1 (by rfl) ⟨64805723, by rfl⟩ : syracuseStep 86407631 = 129611447) B129611447
theorem B4094495 : Blo 1819611 4094495 := bstep (se 1 (by rfl) ⟨3070871, by rfl⟩ : syracuseStep 4094495 = 6141743) B6141743
theorem B6142607 : Blo 1819611 6142607 := bstep (se 1 (by rfl) ⟨4606955, by rfl⟩ : syracuseStep 6142607 = 9213911) B9213911
theorem B2914975 : Blo 1819611 2914975 := bstep (se 1 (by rfl) ⟨2186231, by rfl⟩ : syracuseStep 2914975 = 4372463) B4372463
theorem B4094729 : Blo 1819611 4094729 := bstep (se 2 (by rfl) ⟨1535523, by rfl⟩ : syracuseStep 4094729 = 3071047) B3071047
theorem B3070777 : Blo 1819611 3070777 := bstep (se 2 (by rfl) ⟨1151541, by rfl⟩ : syracuseStep 3070777 = 2303083) B2303083
theorem B3070831 : Blo 1819611 3070831 := bstep (se 1 (by rfl) ⟨2303123, by rfl⟩ : syracuseStep 3070831 = 4606247) B4606247
theorem B25262999 : Blo 1819611 25262999 := bstep (se 1 (by rfl) ⟨18947249, by rfl⟩ : syracuseStep 25262999 = 37894499) B37894499
theorem B6142931 : Blo 1819611 6142931 := bstep (se 1 (by rfl) ⟨4607198, by rfl⟩ : syracuseStep 6142931 = 9214397) B9214397
theorem B3742699 : Blo 1819611 3742699 := bstep (se 1 (by rfl) ⟨2807024, by rfl⟩ : syracuseStep 3742699 = 5614049) B5614049
theorem B6143201 : Blo 1819611 6143201 := bstep (se 2 (by rfl) ⟨2303700, by rfl⟩ : syracuseStep 6143201 = 4607401) B4607401
theorem B2047207 : Blo 1819611 2047207 := bstep (se 1 (by rfl) ⟨1535405, by rfl⟩ : syracuseStep 2047207 = 3070811) B3070811
theorem B4095305 : Blo 1819611 4095305 := bstep (se 2 (by rfl) ⟨1535739, by rfl⟩ : syracuseStep 4095305 = 3071479) B3071479
theorem B45505925 : Blo 1819611 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B3456425 : Blo 1819611 3456425 := bstep (se 2 (by rfl) ⟨1296159, by rfl⟩ : syracuseStep 3456425 = 2592319) B2592319
theorem B59030957 : Blo 1819611 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B16604797 : Blo 1819611 16604797 := bstep (se 3 (by rfl) ⟨3113399, by rfl⟩ : syracuseStep 16604797 = 6226799) B6226799
theorem B4095719 : Blo 1819611 4095719 := bstep (se 1 (by rfl) ⟨3071789, by rfl⟩ : syracuseStep 4095719 = 6143579) B6143579
theorem B2916071 : Blo 1819611 2916071 := bstep (se 1 (by rfl) ⟨2187053, by rfl⟩ : syracuseStep 2916071 = 4374107) B4374107
theorem B6143849 : Blo 1819611 6143849 := bstep (se 2 (by rfl) ⟨2303943, by rfl⟩ : syracuseStep 6143849 = 4607887) B4607887
theorem B2047855 : Blo 1819611 2047855 := bstep (se 1 (by rfl) ⟨1535891, by rfl⟩ : syracuseStep 2047855 = 3071783) B3071783
theorem B168116147 : Blo 1819611 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B52477955 : Blo 1819611 52477955 := bstep (se 1 (by rfl) ⟨39358466, by rfl⟩ : syracuseStep 52477955 = 78716933) B78716933
theorem B5914793 : Blo 1819611 5914793 := bstep (se 2 (by rfl) ⟨2218047, by rfl⟩ : syracuseStep 5914793 = 4436095) B4436095
theorem B4153535 : Blo 1819611 4153535 := bstep (se 1 (by rfl) ⟨3115151, by rfl⟩ : syracuseStep 4153535 = 6230303) B6230303
theorem B3072235 : Blo 1819611 3072235 := bstep (se 1 (by rfl) ⟨2304176, by rfl⟩ : syracuseStep 3072235 = 4608353) B4608353
theorem B2048359 : Blo 1819611 2048359 := bstep (se 1 (by rfl) ⟨1536269, by rfl⟩ : syracuseStep 2048359 = 3072539) B3072539
theorem B31515065 : Blo 1819611 31515065 := bstep (se 2 (by rfl) ⟨11818149, by rfl⟩ : syracuseStep 31515065 = 23636299) B23636299
theorem B39354929 : Blo 1819611 39354929 := bstep (se 2 (by rfl) ⟨14758098, by rfl⟩ : syracuseStep 39354929 = 29516197) B29516197
theorem B2917031 : Blo 1819611 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B3457799 : Blo 1819611 3457799 := bstep (se 1 (by rfl) ⟨2593349, by rfl⟩ : syracuseStep 3457799 = 5186699) B5186699
theorem B4096799 : Blo 1819611 4096799 := bstep (se 1 (by rfl) ⟨3072599, by rfl⟩ : syracuseStep 4096799 = 6145199) B6145199
theorem B6145145 : Blo 1819611 6145145 := bstep (se 2 (by rfl) ⟨2304429, by rfl⟩ : syracuseStep 6145145 = 4608859) B4608859
theorem B4990265 : Blo 1819611 4990265 := bstep (se 2 (by rfl) ⟨1871349, by rfl⟩ : syracuseStep 4990265 = 3742699) B3742699
theorem B1819967 : Blo 1819611 1819967 := bstep (se 1 (by rfl) ⟨1364975, by rfl⟩ : syracuseStep 1819967 = 2729951) B2729951
theorem B1819975 : Blo 1819611 1819975 := bstep (se 1 (by rfl) ⟨1364981, by rfl⟩ : syracuseStep 1819975 = 2729963) B2729963
theorem B1820007 : Blo 1819611 1820007 := bstep (se 1 (by rfl) ⟨1365005, by rfl⟩ : syracuseStep 1820007 = 2730011) B2730011
theorem B2729423 : Blo 1819611 2729423 := bstep (se 1 (by rfl) ⟨2047067, by rfl⟩ : syracuseStep 2729423 = 4094135) B4094135
theorem B3073511 : Blo 1819611 3073511 := bstep (se 1 (by rfl) ⟨2305133, by rfl⟩ : syracuseStep 3073511 = 4610267) B4610267
theorem B2917865 : Blo 1819611 2917865 := bstep (se 2 (by rfl) ⟨1094199, by rfl⟩ : syracuseStep 2917865 = 2188399) B2188399
theorem B1820251 : Blo 1819611 1820251 := bstep (se 1 (by rfl) ⟨1365188, by rfl⟩ : syracuseStep 1820251 = 2730377) B2730377
theorem B2729609 : Blo 1819611 2729609 := bstep (se 2 (by rfl) ⟨1023603, by rfl⟩ : syracuseStep 2729609 = 2047207) B2047207
theorem B2729663 : Blo 1819611 2729663 := bstep (se 1 (by rfl) ⟨2047247, by rfl⟩ : syracuseStep 2729663 = 4094495) B4094495
theorem B2729819 : Blo 1819611 2729819 := bstep (se 1 (by rfl) ⟨2047364, by rfl⟩ : syracuseStep 2729819 = 4094729) B4094729
theorem B14403425 : Blo 1819611 14403425 := bstep (se 2 (by rfl) ⟨5401284, by rfl⟩ : syracuseStep 14403425 = 10802569) B10802569
theorem B15550663 : Blo 1819611 15550663 := bstep (se 1 (by rfl) ⟨11662997, by rfl⟩ : syracuseStep 15550663 = 23325995) B23325995
theorem B1820879 : Blo 1819611 1820879 := bstep (se 1 (by rfl) ⟨1365659, by rfl⟩ : syracuseStep 1820879 = 2731319) B2731319
theorem B2730203 : Blo 1819611 2730203 := bstep (se 1 (by rfl) ⟨2047652, by rfl⟩ : syracuseStep 2730203 = 4095305) B4095305
theorem B30337283 : Blo 1819611 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B2304283 : Blo 1819611 2304283 := bstep (se 1 (by rfl) ⟨1728212, by rfl⟩ : syracuseStep 2304283 = 3456425) B3456425
theorem B1820991 : Blo 1819611 1820991 := bstep (se 1 (by rfl) ⟨1365743, by rfl⟩ : syracuseStep 1820991 = 2731487) B2731487
theorem B1821135 : Blo 1819611 1821135 := bstep (se 1 (by rfl) ⟨1365851, by rfl⟩ : syracuseStep 1821135 = 2731703) B2731703
theorem B2730473 : Blo 1819611 2730473 := bstep (se 2 (by rfl) ⟨1023927, by rfl⟩ : syracuseStep 2730473 = 2047855) B2047855
theorem B2730479 : Blo 1819611 2730479 := bstep (se 1 (by rfl) ⟨2047859, by rfl⟩ : syracuseStep 2730479 = 4095719) B4095719
theorem B1944047 : Blo 1819611 1944047 := bstep (se 1 (by rfl) ⟨1458035, by rfl⟩ : syracuseStep 1944047 = 2916071) B2916071
theorem B1821275 : Blo 1819611 1821275 := bstep (se 1 (by rfl) ⟨1365956, by rfl⟩ : syracuseStep 1821275 = 2731913) B2731913
theorem B112077431 : Blo 1819611 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B16640633 : Blo 1819611 16640633 := bstep (se 2 (by rfl) ⟨6240237, by rfl⟩ : syracuseStep 16640633 = 12480475) B12480475
theorem B1821439 : Blo 1819611 1821439 := bstep (se 1 (by rfl) ⟨1366079, by rfl⟩ : syracuseStep 1821439 = 2732159) B2732159
theorem B2730791 : Blo 1819611 2730791 := bstep (se 1 (by rfl) ⟨2048093, by rfl⟩ : syracuseStep 2730791 = 4096187) B4096187
theorem B2730863 : Blo 1819611 2730863 := bstep (se 1 (by rfl) ⟨2048147, by rfl⟩ : syracuseStep 2730863 = 4096295) B4096295
theorem B11668535 : Blo 1819611 11668535 := bstep (se 1 (by rfl) ⟨8751401, by rfl⟩ : syracuseStep 11668535 = 17502803) B17502803
theorem B6147143 : Blo 1819611 6147143 := bstep (se 1 (by rfl) ⟨4610357, by rfl⟩ : syracuseStep 6147143 = 9220715) B9220715
theorem B2731115 : Blo 1819611 2731115 := bstep (se 1 (by rfl) ⟨2048336, by rfl⟩ : syracuseStep 2731115 = 4096673) B4096673
theorem B2731355 : Blo 1819611 2731355 := bstep (se 1 (by rfl) ⟨2048516, by rfl⟩ : syracuseStep 2731355 = 4097033) B4097033
theorem B2731385 : Blo 1819611 2731385 := bstep (se 2 (by rfl) ⟨1024269, by rfl⟩ : syracuseStep 2731385 = 2048539) B2048539
theorem B2731391 : Blo 1819611 2731391 := bstep (se 1 (by rfl) ⟨2048543, by rfl⟩ : syracuseStep 2731391 = 4097087) B4097087
theorem B6147467 : Blo 1819611 6147467 := bstep (se 1 (by rfl) ⟨4610600, by rfl⟩ : syracuseStep 6147467 = 9221201) B9221201
theorem B3886633 : Blo 1819611 3886633 := bstep (se 2 (by rfl) ⟨1457487, by rfl⟩ : syracuseStep 3886633 = 2914975) B2914975
theorem B2731625 : Blo 1819611 2731625 := bstep (se 2 (by rfl) ⟨1024359, by rfl⟩ : syracuseStep 2731625 = 2048719) B2048719
theorem B24907409 : Blo 1819611 24907409 := bstep (se 2 (by rfl) ⟨9340278, by rfl⟩ : syracuseStep 24907409 = 18680557) B18680557
theorem B2592415 : Blo 1819611 2592415 := bstep (se 1 (by rfl) ⟨1944311, by rfl⟩ : syracuseStep 2592415 = 3888623) B3888623
theorem B4607867 : Blo 1819611 4607867 := bstep (se 1 (by rfl) ⟨3455900, by rfl⟩ : syracuseStep 4607867 = 6911801) B6911801
theorem B2732015 : Blo 1819611 2732015 := bstep (se 1 (by rfl) ⟨2049011, by rfl⟩ : syracuseStep 2732015 = 4098023) B4098023
theorem B23646271 : Blo 1819611 23646271 := bstep (se 1 (by rfl) ⟨17734703, by rfl⟩ : syracuseStep 23646271 = 35469407) B35469407
theorem B2732135 : Blo 1819611 2732135 := bstep (se 1 (by rfl) ⟨2049101, by rfl⟩ : syracuseStep 2732135 = 4098203) B4098203
theorem B15552647 : Blo 1819611 15552647 := bstep (se 1 (by rfl) ⟨11664485, by rfl⟩ : syracuseStep 15552647 = 23328971) B23328971
theorem B2732255 : Blo 1819611 2732255 := bstep (se 1 (by rfl) ⟨2049191, by rfl⟩ : syracuseStep 2732255 = 4098383) B4098383
theorem B9212129 : Blo 1819611 9212129 := bstep (se 2 (by rfl) ⟨3454548, by rfl⟩ : syracuseStep 9212129 = 6909097) B6909097
theorem B2732315 : Blo 1819611 2732315 := bstep (se 1 (by rfl) ⟨2049236, by rfl⟩ : syracuseStep 2732315 = 4098473) B4098473
theorem B9843295 : Blo 1819611 9843295 := bstep (se 1 (by rfl) ⟨7382471, by rfl⟩ : syracuseStep 9843295 = 14764943) B14764943
theorem B22139729 : Blo 1819611 22139729 := bstep (se 2 (by rfl) ⟨8302398, by rfl⟩ : syracuseStep 22139729 = 16604797) B16604797
theorem B23327635 : Blo 1819611 23327635 := bstep (se 1 (by rfl) ⟨17495726, by rfl⟩ : syracuseStep 23327635 = 34991453) B34991453
theorem B6141311 : Blo 1819611 6141311 := bstep (se 1 (by rfl) ⟨4605983, by rfl⟩ : syracuseStep 6141311 = 9211967) B9211967
theorem B5256679 : Blo 1819611 5256679 := bstep (se 1 (by rfl) ⟨3942509, by rfl⟩ : syracuseStep 5256679 = 7885019) B7885019
theorem B13129381 : Blo 1819611 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B2766955 : Blo 1819611 2766955 := bstep (se 1 (by rfl) ⟨2075216, by rfl⟩ : syracuseStep 2766955 = 4150433) B4150433
theorem B4094171 : Blo 1819611 4094171 := bstep (se 1 (by rfl) ⟨3070628, by rfl⟩ : syracuseStep 4094171 = 6141257) B6141257
theorem B4610297 : Blo 1819611 4610297 := bstep (se 2 (by rfl) ⟨1728861, by rfl⟩ : syracuseStep 4610297 = 3457723) B3457723
theorem B3455369 : Blo 1819611 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B4610459 : Blo 1819611 4610459 := bstep (se 1 (by rfl) ⟨3457844, by rfl⟩ : syracuseStep 4610459 = 6915689) B6915689
theorem B4094369 : Blo 1819611 4094369 := bstep (se 2 (by rfl) ⟨1535388, by rfl⟩ : syracuseStep 4094369 = 3070777) B3070777
theorem B11229671 : Blo 1819611 11229671 := bstep (se 1 (by rfl) ⟨8422253, by rfl⟩ : syracuseStep 11229671 = 16844507) B16844507
theorem B4094441 : Blo 1819611 4094441 := bstep (se 2 (by rfl) ⟨1535415, by rfl⟩ : syracuseStep 4094441 = 3070831) B3070831
theorem B239491673 : Blo 1819611 239491673 := bstep (se 2 (by rfl) ⟨89809377, by rfl⟩ : syracuseStep 239491673 = 179618755) B179618755
theorem B4610803 : Blo 1819611 4610803 := bstep (se 1 (by rfl) ⟨3458102, by rfl⟩ : syracuseStep 4610803 = 6916205) B6916205
theorem B2767807 : Blo 1819611 2767807 := bstep (se 1 (by rfl) ⟨2075855, by rfl⟩ : syracuseStep 2767807 = 4151711) B4151711
theorem B57605087 : Blo 1819611 57605087 := bstep (se 1 (by rfl) ⟨43203815, by rfl⟩ : syracuseStep 57605087 = 86407631) B86407631
theorem B4095071 : Blo 1819611 4095071 := bstep (se 1 (by rfl) ⟨3071303, by rfl⟩ : syracuseStep 4095071 = 6142607) B6142607
theorem B2186347 : Blo 1819611 2186347 := bstep (se 1 (by rfl) ⟨1639760, by rfl⟩ : syracuseStep 2186347 = 3279521) B3279521
theorem B3890281 : Blo 1819611 3890281 := bstep (se 2 (by rfl) ⟨1458855, by rfl⟩ : syracuseStep 3890281 = 2917711) B2917711
theorem B3456121 : Blo 1819611 3456121 := bstep (se 2 (by rfl) ⟨1296045, by rfl⟩ : syracuseStep 3456121 = 2592091) B2592091
theorem B112114853 : Blo 1819611 112114853 := bstep (se 4 (by rfl) ⟨10510767, by rfl⟩ : syracuseStep 112114853 = 21021535) B21021535
theorem B16841999 : Blo 1819611 16841999 := bstep (se 1 (by rfl) ⟨12631499, by rfl⟩ : syracuseStep 16841999 = 25262999) B25262999
theorem B4095287 : Blo 1819611 4095287 := bstep (se 1 (by rfl) ⟨3071465, by rfl⟩ : syracuseStep 4095287 = 6142931) B6142931
theorem B4922687 : Blo 1819611 4922687 := bstep (se 1 (by rfl) ⟨3692015, by rfl⟩ : syracuseStep 4922687 = 7384031) B7384031
theorem B4095467 : Blo 1819611 4095467 := bstep (se 1 (by rfl) ⟨3071600, by rfl⟩ : syracuseStep 4095467 = 6143201) B6143201
theorem B5185127 : Blo 1819611 5185127 := bstep (se 1 (by rfl) ⟨3888845, by rfl⟩ : syracuseStep 5185127 = 7777691) B7777691
theorem B39353971 : Blo 1819611 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B12459673 : Blo 1819611 12459673 := bstep (se 2 (by rfl) ⟨4672377, by rfl⟩ : syracuseStep 12459673 = 9344755) B9344755
theorem B3792761 : Blo 1819611 3792761 := bstep (se 2 (by rfl) ⟨1422285, by rfl⟩ : syracuseStep 3792761 = 2844571) B2844571
theorem B4095899 : Blo 1819611 4095899 := bstep (se 1 (by rfl) ⟨3071924, by rfl⟩ : syracuseStep 4095899 = 6143849) B6143849
theorem B9838579 : Blo 1819611 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B2769023 : Blo 1819611 2769023 := bstep (se 1 (by rfl) ⟨2076767, by rfl⟩ : syracuseStep 2769023 = 4153535) B4153535
theorem B20734217 : Blo 1819611 20734217 := bstep (se 2 (by rfl) ⟨7775331, by rfl⟩ : syracuseStep 20734217 = 15550663) B15550663
theorem B4096313 : Blo 1819611 4096313 := bstep (se 2 (by rfl) ⟨1536117, by rfl⟩ : syracuseStep 4096313 = 3072235) B3072235
theorem B3072377 : Blo 1819611 3072377 := bstep (se 2 (by rfl) ⟨1152141, by rfl⟩ : syracuseStep 3072377 = 2304283) B2304283
theorem B4096763 : Blo 1819611 4096763 := bstep (se 1 (by rfl) ⟨3072572, by rfl⟩ : syracuseStep 4096763 = 6145145) B6145145
theorem B13124393 : Blo 1819611 13124393 := bstep (se 2 (by rfl) ⟨4921647, by rfl⟩ : syracuseStep 13124393 = 9843295) B9843295
theorem B3326843 : Blo 1819611 3326843 := bstep (se 1 (by rfl) ⟨2495132, by rfl⟩ : syracuseStep 3326843 = 4990265) B4990265
theorem B1819615 : Blo 1819611 1819615 := bstep (se 1 (by rfl) ⟨1364711, by rfl⟩ : syracuseStep 1819615 = 2729423) B2729423
theorem B2049007 : Blo 1819611 2049007 := bstep (se 1 (by rfl) ⟨1536755, by rfl⟩ : syracuseStep 2049007 = 3073511) B3073511
theorem B1819739 : Blo 1819611 1819739 := bstep (se 1 (by rfl) ⟨1364804, by rfl⟩ : syracuseStep 1819739 = 2729609) B2729609
theorem B1819775 : Blo 1819611 1819775 := bstep (se 1 (by rfl) ⟨1364831, by rfl⟩ : syracuseStep 1819775 = 2729663) B2729663
theorem B1819879 : Blo 1819611 1819879 := bstep (se 1 (by rfl) ⟨1364909, by rfl⟩ : syracuseStep 1819879 = 2729819) B2729819
theorem B5187041 : Blo 1819611 5187041 := bstep (se 2 (by rfl) ⟨1945140, by rfl⟩ : syracuseStep 5187041 = 3890281) B3890281
theorem B2729447 : Blo 1819611 2729447 := bstep (se 1 (by rfl) ⟨2047085, by rfl⟩ : syracuseStep 2729447 = 4094171) B4094171
theorem B1820135 : Blo 1819611 1820135 := bstep (se 1 (by rfl) ⟨1365101, by rfl⟩ : syracuseStep 1820135 = 2730203) B2730203
theorem B3073531 : Blo 1819611 3073531 := bstep (se 1 (by rfl) ⟨2305148, by rfl⟩ : syracuseStep 3073531 = 4610297) B4610297
theorem B2303579 : Blo 1819611 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B3073639 : Blo 1819611 3073639 := bstep (se 1 (by rfl) ⟨2305229, by rfl⟩ : syracuseStep 3073639 = 4610459) B4610459
theorem B2729579 : Blo 1819611 2729579 := bstep (se 1 (by rfl) ⟨2047184, by rfl⟩ : syracuseStep 2729579 = 4094369) B4094369
theorem B2729627 : Blo 1819611 2729627 := bstep (se 1 (by rfl) ⟨2047220, by rfl⟩ : syracuseStep 2729627 = 4094441) B4094441
theorem B1820315 : Blo 1819611 1820315 := bstep (se 1 (by rfl) ⟨1365236, by rfl⟩ : syracuseStep 1820315 = 2730473) B2730473
theorem B1820319 : Blo 1819611 1820319 := bstep (se 1 (by rfl) ⟨1365239, by rfl⟩ : syracuseStep 1820319 = 2730479) B2730479
theorem B11093755 : Blo 1819611 11093755 := bstep (se 1 (by rfl) ⟨8320316, by rfl⟩ : syracuseStep 11093755 = 16640633) B16640633
theorem B1820527 : Blo 1819611 1820527 := bstep (se 1 (by rfl) ⟨1365395, by rfl⟩ : syracuseStep 1820527 = 2730791) B2730791
theorem B1820575 : Blo 1819611 1820575 := bstep (se 1 (by rfl) ⟨1365431, by rfl⟩ : syracuseStep 1820575 = 2730863) B2730863
theorem B4098095 : Blo 1819611 4098095 := bstep (se 1 (by rfl) ⟨3073571, by rfl⟩ : syracuseStep 4098095 = 6147143) B6147143
theorem B2730047 : Blo 1819611 2730047 := bstep (se 1 (by rfl) ⟨2047535, by rfl⟩ : syracuseStep 2730047 = 4095071) B4095071
theorem B1820743 : Blo 1819611 1820743 := bstep (se 1 (by rfl) ⟨1365557, by rfl⟩ : syracuseStep 1820743 = 2731115) B2731115
theorem B52471961 : Blo 1819611 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B2730191 : Blo 1819611 2730191 := bstep (se 1 (by rfl) ⟨2047643, by rfl⟩ : syracuseStep 2730191 = 4095287) B4095287
theorem B1820903 : Blo 1819611 1820903 := bstep (se 1 (by rfl) ⟨1365677, by rfl⟩ : syracuseStep 1820903 = 2731355) B2731355
theorem B1820923 : Blo 1819611 1820923 := bstep (se 1 (by rfl) ⟨1365692, by rfl⟩ : syracuseStep 1820923 = 2731385) B2731385
theorem B1820927 : Blo 1819611 1820927 := bstep (se 1 (by rfl) ⟨1365695, by rfl⟩ : syracuseStep 1820927 = 2731391) B2731391
theorem B4098311 : Blo 1819611 4098311 := bstep (se 1 (by rfl) ⟨3073733, by rfl⟩ : syracuseStep 4098311 = 6147467) B6147467
theorem B2730311 : Blo 1819611 2730311 := bstep (se 1 (by rfl) ⟨2047733, by rfl⟩ : syracuseStep 2730311 = 4095467) B4095467
theorem B1821083 : Blo 1819611 1821083 := bstep (se 1 (by rfl) ⟨1365812, by rfl⟩ : syracuseStep 1821083 = 2731625) B2731625
theorem B2730599 : Blo 1819611 2730599 := bstep (se 1 (by rfl) ⟨2047949, by rfl⟩ : syracuseStep 2730599 = 4095899) B4095899
theorem B13118105 : Blo 1819611 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B1821343 : Blo 1819611 1821343 := bstep (se 1 (by rfl) ⟨1366007, by rfl⟩ : syracuseStep 1821343 = 2732015) B2732015
theorem B1821423 : Blo 1819611 1821423 := bstep (se 1 (by rfl) ⟨1366067, by rfl⟩ : syracuseStep 1821423 = 2732135) B2732135
theorem B3689273 : Blo 1819611 3689273 := bstep (se 2 (by rfl) ⟨1383477, by rfl⟩ : syracuseStep 3689273 = 2766955) B2766955
theorem B1821503 : Blo 1819611 1821503 := bstep (se 1 (by rfl) ⟨1366127, by rfl⟩ : syracuseStep 1821503 = 2732255) B2732255
theorem B1821543 : Blo 1819611 1821543 := bstep (se 1 (by rfl) ⟨1366157, by rfl⟩ : syracuseStep 1821543 = 2732315) B2732315
theorem B15772781 : Blo 1819611 15772781 := bstep (se 3 (by rfl) ⟨2957396, by rfl⟩ : syracuseStep 15772781 = 5914793) B5914793
theorem B2731145 : Blo 1819611 2731145 := bstep (se 2 (by rfl) ⟨1024179, by rfl⟩ : syracuseStep 2731145 = 2048359) B2048359
theorem B2305199 : Blo 1819611 2305199 := bstep (se 1 (by rfl) ⟨1728899, by rfl⟩ : syracuseStep 2305199 = 3457799) B3457799
theorem B2731199 : Blo 1819611 2731199 := bstep (se 1 (by rfl) ⟨2048399, by rfl⟩ : syracuseStep 2731199 = 4096799) B4096799
theorem B6147737 : Blo 1819611 6147737 := bstep (se 2 (by rfl) ⟨2305401, by rfl⟩ : syracuseStep 6147737 = 4610803) B4610803
theorem B1945243 : Blo 1819611 1945243 := bstep (se 1 (by rfl) ⟨1458932, by rfl⟩ : syracuseStep 1945243 = 2917865) B2917865
theorem B153636533 : Blo 1819611 153636533 := bstep (se 5 (by rfl) ⟨7201712, by rfl⟩ : syracuseStep 153636533 = 14403425) B14403425
theorem B3690409 : Blo 1819611 3690409 := bstep (se 2 (by rfl) ⟨1383903, by rfl⟩ : syracuseStep 3690409 = 2767807) B2767807
theorem B4608161 : Blo 1819611 4608161 := bstep (se 2 (by rfl) ⟨1728060, by rfl⟩ : syracuseStep 4608161 = 3456121) B3456121
theorem B7778749 : Blo 1819611 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B7008905 : Blo 1819611 7008905 := bstep (se 2 (by rfl) ⟨2628339, by rfl⟩ : syracuseStep 7008905 = 5256679) B5256679
theorem B7779023 : Blo 1819611 7779023 := bstep (se 1 (by rfl) ⟨5834267, by rfl⟩ : syracuseStep 7779023 = 11668535) B11668535
theorem B5182177 : Blo 1819611 5182177 := bstep (se 2 (by rfl) ⟨1943316, by rfl⟩ : syracuseStep 5182177 = 3886633) B3886633
theorem B11227999 : Blo 1819611 11227999 := bstep (se 1 (by rfl) ⟨8420999, by rfl⟩ : syracuseStep 11227999 = 16841999) B16841999
theorem B3281791 : Blo 1819611 3281791 := bstep (se 1 (by rfl) ⟨2461343, by rfl⟩ : syracuseStep 3281791 = 4922687) B4922687
theorem B2528507 : Blo 1819611 2528507 := bstep (se 1 (by rfl) ⟨1896380, by rfl⟩ : syracuseStep 2528507 = 3792761) B3792761
theorem B34985303 : Blo 1819611 34985303 := bstep (se 1 (by rfl) ⟨26238977, by rfl⟩ : syracuseStep 34985303 = 52477955) B52477955
theorem B31528361 : Blo 1819611 31528361 := bstep (se 2 (by rfl) ⟨11823135, by rfl⟩ : syracuseStep 31528361 = 23646271) B23646271
theorem B10368431 : Blo 1819611 10368431 := bstep (se 1 (by rfl) ⟨7776323, by rfl⟩ : syracuseStep 10368431 = 15552647) B15552647
theorem B6141419 : Blo 1819611 6141419 := bstep (se 1 (by rfl) ⟨4606064, by rfl⟩ : syracuseStep 6141419 = 9212129) B9212129
theorem B21010043 : Blo 1819611 21010043 := bstep (se 1 (by rfl) ⟨15757532, by rfl⟩ : syracuseStep 21010043 = 31515065) B31515065
theorem B26236619 : Blo 1819611 26236619 := bstep (se 1 (by rfl) ⟨19677464, by rfl⟩ : syracuseStep 26236619 = 39354929) B39354929
theorem B14759819 : Blo 1819611 14759819 := bstep (se 1 (by rfl) ⟨11069864, by rfl⟩ : syracuseStep 14759819 = 22139729) B22139729
theorem B13826213 : Blo 1819611 13826213 := bstep (se 4 (by rfl) ⟨1296207, by rfl⟩ : syracuseStep 13826213 = 2592415) B2592415
theorem B4094207 : Blo 1819611 4094207 := bstep (se 1 (by rfl) ⟨3070655, by rfl⟩ : syracuseStep 4094207 = 6141311) B6141311
theorem B31103513 : Blo 1819611 31103513 := bstep (se 2 (by rfl) ⟨11663817, by rfl⟩ : syracuseStep 31103513 = 23327635) B23327635
theorem B5184125 : Blo 1819611 5184125 := bstep (se 3 (by rfl) ⟨972023, by rfl⟩ : syracuseStep 5184125 = 1944047) B1944047
theorem B2915129 : Blo 1819611 2915129 := bstep (se 2 (by rfl) ⟨1093173, by rfl⟩ : syracuseStep 2915129 = 2186347) B2186347
theorem B20224855 : Blo 1819611 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B7486447 : Blo 1819611 7486447 := bstep (se 1 (by rfl) ⟨5614835, by rfl⟩ : syracuseStep 7486447 = 11229671) B11229671
theorem B159661115 : Blo 1819611 159661115 := bstep (se 1 (by rfl) ⟨119745836, by rfl⟩ : syracuseStep 159661115 = 239491673) B239491673
theorem B74718287 : Blo 1819611 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B38403391 : Blo 1819611 38403391 := bstep (se 1 (by rfl) ⟨28802543, by rfl⟩ : syracuseStep 38403391 = 57605087) B57605087
theorem B74743235 : Blo 1819611 74743235 := bstep (se 1 (by rfl) ⟨56057426, by rfl⟩ : syracuseStep 74743235 = 112114853) B112114853
theorem B16612897 : Blo 1819611 16612897 := bstep (se 2 (by rfl) ⟨6229836, by rfl⟩ : syracuseStep 16612897 = 12459673) B12459673
theorem B17505841 : Blo 1819611 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B3456751 : Blo 1819611 3456751 := bstep (se 1 (by rfl) ⟨2592563, by rfl⟩ : syracuseStep 3456751 = 5185127) B5185127
theorem B16604939 : Blo 1819611 16604939 := bstep (se 1 (by rfl) ⟨12453704, by rfl⟩ : syracuseStep 16604939 = 24907409) B24907409
theorem B3071911 : Blo 1819611 3071911 := bstep (se 1 (by rfl) ⟨2303933, by rfl⟩ : syracuseStep 3071911 = 4607867) B4607867
theorem B3072107 : Blo 1819611 3072107 := bstep (se 1 (by rfl) ⟨2304080, by rfl⟩ : syracuseStep 3072107 = 4608161) B4608161
theorem B2048251 : Blo 1819611 2048251 := bstep (se 1 (by rfl) ⟨1536188, by rfl⟩ : syracuseStep 2048251 = 3072377) B3072377
theorem B5186015 : Blo 1819611 5186015 := bstep (se 1 (by rfl) ⟨3889511, by rfl⟩ : syracuseStep 5186015 = 7779023) B7779023
theorem B8749595 : Blo 1819611 8749595 := bstep (se 1 (by rfl) ⟨6562196, by rfl⟩ : syracuseStep 8749595 = 13124393) B13124393
theorem B10371665 : Blo 1819611 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B6742685 : Blo 1819611 6742685 := bstep (se 3 (by rfl) ⟨1264253, by rfl⟩ : syracuseStep 6742685 = 2528507) B2528507
theorem B23323535 : Blo 1819611 23323535 := bstep (se 1 (by rfl) ⟨17492651, by rfl⟩ : syracuseStep 23323535 = 34985303) B34985303
theorem B3458027 : Blo 1819611 3458027 := bstep (se 1 (by rfl) ⟨2593520, by rfl⟩ : syracuseStep 3458027 = 5187041) B5187041
theorem B1819631 : Blo 1819611 1819631 := bstep (se 1 (by rfl) ⟨1364723, by rfl⟩ : syracuseStep 1819631 = 2729447) B2729447
theorem B1819719 : Blo 1819611 1819719 := bstep (se 1 (by rfl) ⟨1364789, by rfl⟩ : syracuseStep 1819719 = 2729579) B2729579
theorem B1819751 : Blo 1819611 1819751 := bstep (se 1 (by rfl) ⟨1364813, by rfl⟩ : syracuseStep 1819751 = 2729627) B2729627
theorem B17491079 : Blo 1819611 17491079 := bstep (se 1 (by rfl) ⟨13118309, by rfl⟩ : syracuseStep 17491079 = 26236619) B26236619
theorem B4375721 : Blo 1819611 4375721 := bstep (se 2 (by rfl) ⟨1640895, by rfl⟩ : syracuseStep 4375721 = 3281791) B3281791
theorem B9839879 : Blo 1819611 9839879 := bstep (se 1 (by rfl) ⟨7379909, by rfl⟩ : syracuseStep 9839879 = 14759819) B14759819
theorem B1820031 : Blo 1819611 1820031 := bstep (se 1 (by rfl) ⟨1365023, by rfl⟩ : syracuseStep 1820031 = 2730047) B2730047
theorem B34981307 : Blo 1819611 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B9217475 : Blo 1819611 9217475 := bstep (se 1 (by rfl) ⟨6913106, by rfl⟩ : syracuseStep 9217475 = 13826213) B13826213
theorem B1820127 : Blo 1819611 1820127 := bstep (se 1 (by rfl) ⟨1365095, by rfl⟩ : syracuseStep 1820127 = 2730191) B2730191
theorem B2729471 : Blo 1819611 2729471 := bstep (se 1 (by rfl) ⟨2047103, by rfl⟩ : syracuseStep 2729471 = 4094207) B4094207
theorem B1820207 : Blo 1819611 1820207 := bstep (se 1 (by rfl) ⟨1365155, by rfl⟩ : syracuseStep 1820207 = 2730311) B2730311
theorem B20735675 : Blo 1819611 20735675 := bstep (se 1 (by rfl) ⟨15551756, by rfl⟩ : syracuseStep 20735675 = 31103513) B31103513
theorem B1820399 : Blo 1819611 1820399 := bstep (se 1 (by rfl) ⟨1365299, by rfl⟩ : syracuseStep 1820399 = 2730599) B2730599
theorem B107865893 : Blo 1819611 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B4098041 : Blo 1819611 4098041 := bstep (se 2 (by rfl) ⟨1536765, by rfl⟩ : syracuseStep 4098041 = 3073531) B3073531
theorem B106440743 : Blo 1819611 106440743 := bstep (se 1 (by rfl) ⟨79830557, by rfl⟩ : syracuseStep 106440743 = 159661115) B159661115
theorem B23341121 : Blo 1819611 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B1820763 : Blo 1819611 1820763 := bstep (se 1 (by rfl) ⟨1365572, by rfl⟩ : syracuseStep 1820763 = 2731145) B2731145
theorem B1820799 : Blo 1819611 1820799 := bstep (se 1 (by rfl) ⟨1365599, by rfl⟩ : syracuseStep 1820799 = 2731199) B2731199
theorem B4098185 : Blo 1819611 4098185 := bstep (se 2 (by rfl) ⟨1536819, by rfl⟩ : syracuseStep 4098185 = 3073639) B3073639
theorem B4098491 : Blo 1819611 4098491 := bstep (se 1 (by rfl) ⟨3073868, by rfl⟩ : syracuseStep 4098491 = 6147737) B6147737
theorem B11069959 : Blo 1819611 11069959 := bstep (se 1 (by rfl) ⟨8302469, by rfl⟩ : syracuseStep 11069959 = 16604939) B16604939
theorem B13822811 : Blo 1819611 13822811 := bstep (se 1 (by rfl) ⟨10367108, by rfl⟩ : syracuseStep 13822811 = 20734217) B20734217
theorem B2730875 : Blo 1819611 2730875 := bstep (se 1 (by rfl) ⟨2048156, by rfl⟩ : syracuseStep 2730875 = 4096313) B4096313
theorem B7384061 : Blo 1819611 7384061 := bstep (se 3 (by rfl) ⟨1384511, by rfl⟩ : syracuseStep 7384061 = 2769023) B2769023
theorem B4672603 : Blo 1819611 4672603 := bstep (se 1 (by rfl) ⟨3504452, by rfl⟩ : syracuseStep 4672603 = 7008905) B7008905
theorem B6147197 : Blo 1819611 6147197 := bstep (se 3 (by rfl) ⟨1152599, by rfl⟩ : syracuseStep 6147197 = 2305199) B2305199
theorem B2731175 : Blo 1819611 2731175 := bstep (se 1 (by rfl) ⟨2048381, by rfl⟩ : syracuseStep 2731175 = 4096763) B4096763
theorem B6909569 : Blo 1819611 6909569 := bstep (se 2 (by rfl) ⟨2591088, by rfl⟩ : syracuseStep 6909569 = 5182177) B5182177
theorem B14970665 : Blo 1819611 14970665 := bstep (se 2 (by rfl) ⟨5613999, by rfl⟩ : syracuseStep 14970665 = 11227999) B11227999
theorem B2732009 : Blo 1819611 2732009 := bstep (se 2 (by rfl) ⟨1024503, by rfl⟩ : syracuseStep 2732009 = 2049007) B2049007
theorem B9981929 : Blo 1819611 9981929 := bstep (se 2 (by rfl) ⟨3743223, by rfl⟩ : syracuseStep 9981929 = 7486447) B7486447
theorem B2732063 : Blo 1819611 2732063 := bstep (se 1 (by rfl) ⟨2049047, by rfl⟩ : syracuseStep 2732063 = 4098095) B4098095
theorem B2732207 : Blo 1819611 2732207 := bstep (se 1 (by rfl) ⟨2049155, by rfl⟩ : syracuseStep 2732207 = 4098311) B4098311
theorem B51204521 : Blo 1819611 51204521 := bstep (se 2 (by rfl) ⟨19201695, by rfl⟩ : syracuseStep 51204521 = 38403391) B38403391
theorem B8745403 : Blo 1819611 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B49812191 : Blo 1819611 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B10515187 : Blo 1819611 10515187 := bstep (se 1 (by rfl) ⟨7886390, by rfl⟩ : syracuseStep 10515187 = 15772781) B15772781
theorem B2593657 : Blo 1819611 2593657 := bstep (se 2 (by rfl) ⟨972621, by rfl⟩ : syracuseStep 2593657 = 1945243) B1945243
theorem B49828823 : Blo 1819611 49828823 := bstep (se 1 (by rfl) ⟨37371617, by rfl⟩ : syracuseStep 49828823 = 74743235) B74743235
theorem B4609001 : Blo 1819611 4609001 := bstep (se 2 (by rfl) ⟨1728375, by rfl⟩ : syracuseStep 4609001 = 3456751) B3456751
theorem B14791673 : Blo 1819611 14791673 := bstep (se 2 (by rfl) ⟨5546877, by rfl⟩ : syracuseStep 14791673 = 11093755) B11093755
theorem B4920545 : Blo 1819611 4920545 := bstep (se 2 (by rfl) ⟨1845204, by rfl⟩ : syracuseStep 4920545 = 3690409) B3690409
theorem B21018907 : Blo 1819611 21018907 := bstep (se 1 (by rfl) ⟨15764180, by rfl⟩ : syracuseStep 21018907 = 31528361) B31528361
theorem B6912287 : Blo 1819611 6912287 := bstep (se 1 (by rfl) ⟨5184215, by rfl⟩ : syracuseStep 6912287 = 10368431) B10368431
theorem B4094279 : Blo 1819611 4094279 := bstep (se 1 (by rfl) ⟨3070709, by rfl⟩ : syracuseStep 4094279 = 6141419) B6141419
theorem B14006695 : Blo 1819611 14006695 := bstep (se 1 (by rfl) ⟨10505021, by rfl⟩ : syracuseStep 14006695 = 21010043) B21010043
theorem B6142877 : Blo 1819611 6142877 := bstep (se 3 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 6142877 = 2303579) B2303579
theorem B3456083 : Blo 1819611 3456083 := bstep (se 1 (by rfl) ⟨2592062, by rfl⟩ : syracuseStep 3456083 = 5184125) B5184125
theorem B22150529 : Blo 1819611 22150529 := bstep (se 2 (by rfl) ⟨8306448, by rfl⟩ : syracuseStep 22150529 = 16612897) B16612897
theorem B9838061 : Blo 1819611 9838061 := bstep (se 3 (by rfl) ⟨1844636, by rfl⟩ : syracuseStep 9838061 = 3689273) B3689273
theorem B7773677 : Blo 1819611 7773677 := bstep (se 3 (by rfl) ⟨1457564, by rfl⟩ : syracuseStep 7773677 = 2915129) B2915129
theorem B8871581 : Blo 1819611 8871581 := bstep (se 3 (by rfl) ⟨1663421, by rfl⟩ : syracuseStep 8871581 = 3326843) B3326843
theorem B102424355 : Blo 1819611 102424355 := bstep (se 1 (by rfl) ⟨76818266, by rfl⟩ : syracuseStep 102424355 = 153636533) B153636533
theorem B4095881 : Blo 1819611 4095881 := bstep (se 2 (by rfl) ⟨1535955, by rfl⟩ : syracuseStep 4095881 = 3071911) B3071911
theorem B2048071 : Blo 1819611 2048071 := bstep (se 1 (by rfl) ⟨1536053, by rfl⟩ : syracuseStep 2048071 = 3072107) B3072107
theorem B3457343 : Blo 1819611 3457343 := bstep (se 1 (by rfl) ⟨2593007, by rfl⟩ : syracuseStep 3457343 = 5186015) B5186015
theorem B5833063 : Blo 1819611 5833063 := bstep (se 1 (by rfl) ⟨4374797, by rfl⟩ : syracuseStep 5833063 = 8749595) B8749595
theorem B28025209 : Blo 1819611 28025209 := bstep (se 2 (by rfl) ⟨10509453, by rfl⟩ : syracuseStep 28025209 = 21018907) B21018907
theorem B6914443 : Blo 1819611 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B15549023 : Blo 1819611 15549023 := bstep (se 1 (by rfl) ⟨11661767, by rfl⟩ : syracuseStep 15549023 = 23323535) B23323535
theorem B33219215 : Blo 1819611 33219215 := bstep (se 1 (by rfl) ⟨24914411, by rfl⟩ : syracuseStep 33219215 = 49828823) B49828823
theorem B3072667 : Blo 1819611 3072667 := bstep (se 1 (by rfl) ⟨2304500, by rfl⟩ : syracuseStep 3072667 = 4609001) B4609001
theorem B2917147 : Blo 1819611 2917147 := bstep (se 1 (by rfl) ⟨2187860, by rfl⟩ : syracuseStep 2917147 = 4375721) B4375721
theorem B6144983 : Blo 1819611 6144983 := bstep (se 1 (by rfl) ⟨4608737, by rfl⟩ : syracuseStep 6144983 = 9217475) B9217475
theorem B1819647 : Blo 1819611 1819647 := bstep (se 1 (by rfl) ⟨1364735, by rfl⟩ : syracuseStep 1819647 = 2729471) B2729471
theorem B136545389 : Blo 1819611 136545389 := bstep (se 3 (by rfl) ⟨25602260, by rfl⟩ : syracuseStep 136545389 = 51204521) B51204521
theorem B3458209 : Blo 1819611 3458209 := bstep (se 2 (by rfl) ⟨1296828, by rfl⟩ : syracuseStep 3458209 = 2593657) B2593657
theorem B71910595 : Blo 1819611 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B2729519 : Blo 1819611 2729519 := bstep (se 1 (by rfl) ⟨2047139, by rfl⟩ : syracuseStep 2729519 = 4094279) B4094279
theorem B1820583 : Blo 1819611 1820583 := bstep (se 1 (by rfl) ⟨1365437, by rfl⟩ : syracuseStep 1820583 = 2730875) B2730875
theorem B2304055 : Blo 1819611 2304055 := bstep (se 1 (by rfl) ⟨1728041, by rfl⟩ : syracuseStep 2304055 = 3456083) B3456083
theorem B4098131 : Blo 1819611 4098131 := bstep (se 1 (by rfl) ⟨3073598, by rfl⟩ : syracuseStep 4098131 = 6147197) B6147197
theorem B1820783 : Blo 1819611 1820783 := bstep (se 1 (by rfl) ⟨1365587, by rfl⟩ : syracuseStep 1820783 = 2731175) B2731175
theorem B4606379 : Blo 1819611 4606379 := bstep (se 1 (by rfl) ⟨3454784, by rfl⟩ : syracuseStep 4606379 = 6909569) B6909569
theorem B68282903 : Blo 1819611 68282903 := bstep (se 1 (by rfl) ⟨51212177, by rfl⟩ : syracuseStep 68282903 = 102424355) B102424355
theorem B9980443 : Blo 1819611 9980443 := bstep (se 1 (by rfl) ⟨7485332, by rfl⟩ : syracuseStep 9980443 = 14970665) B14970665
theorem B2730587 : Blo 1819611 2730587 := bstep (se 1 (by rfl) ⟨2047940, by rfl⟩ : syracuseStep 2730587 = 4095881) B4095881
theorem B1821339 : Blo 1819611 1821339 := bstep (se 1 (by rfl) ⟨1366004, by rfl⟩ : syracuseStep 1821339 = 2732009) B2732009
theorem B6654619 : Blo 1819611 6654619 := bstep (se 1 (by rfl) ⟨4990964, by rfl⟩ : syracuseStep 6654619 = 9981929) B9981929
theorem B1821375 : Blo 1819611 1821375 := bstep (se 1 (by rfl) ⟨1366031, by rfl⟩ : syracuseStep 1821375 = 2732063) B2732063
theorem B1821471 : Blo 1819611 1821471 := bstep (se 1 (by rfl) ⟨1366103, by rfl⟩ : syracuseStep 1821471 = 2732207) B2732207
theorem B2731001 : Blo 1819611 2731001 := bstep (se 2 (by rfl) ⟨1024125, by rfl⟩ : syracuseStep 2731001 = 2048251) B2048251
theorem B11660537 : Blo 1819611 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B2305351 : Blo 1819611 2305351 := bstep (se 1 (by rfl) ⟨1729013, by rfl⟩ : syracuseStep 2305351 = 3458027) B3458027
theorem B11660719 : Blo 1819611 11660719 := bstep (se 1 (by rfl) ⟨8745539, by rfl⟩ : syracuseStep 11660719 = 17491079) B17491079
theorem B14020249 : Blo 1819611 14020249 := bstep (se 2 (by rfl) ⟨5257593, by rfl⟩ : syracuseStep 14020249 = 10515187) B10515187
theorem B13823783 : Blo 1819611 13823783 := bstep (se 1 (by rfl) ⟨10367837, by rfl⟩ : syracuseStep 13823783 = 20735675) B20735675
theorem B2732027 : Blo 1819611 2732027 := bstep (se 1 (by rfl) ⟨2049020, by rfl⟩ : syracuseStep 2732027 = 4098041) B4098041
theorem B15560747 : Blo 1819611 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B2732123 : Blo 1819611 2732123 := bstep (se 1 (by rfl) ⟨2049092, by rfl⟩ : syracuseStep 2732123 = 4098185) B4098185
theorem B6230137 : Blo 1819611 6230137 := bstep (se 2 (by rfl) ⟨2336301, by rfl⟩ : syracuseStep 6230137 = 4672603) B4672603
theorem B4608191 : Blo 1819611 4608191 := bstep (se 1 (by rfl) ⟨3456143, by rfl⟩ : syracuseStep 4608191 = 6912287) B6912287
theorem B2732327 : Blo 1819611 2732327 := bstep (se 1 (by rfl) ⟨2049245, by rfl⟩ : syracuseStep 2732327 = 4098491) B4098491
theorem B14767019 : Blo 1819611 14767019 := bstep (se 1 (by rfl) ⟨11075264, by rfl⟩ : syracuseStep 14767019 = 22150529) B22150529
theorem B6558707 : Blo 1819611 6558707 := bstep (se 1 (by rfl) ⟨4919030, by rfl⟩ : syracuseStep 6558707 = 9838061) B9838061
theorem B5182451 : Blo 1819611 5182451 := bstep (se 1 (by rfl) ⟨3886838, by rfl⟩ : syracuseStep 5182451 = 7773677) B7773677
theorem B283841981 : Blo 1819611 283841981 := bstep (se 3 (by rfl) ⟨53220371, by rfl⟩ : syracuseStep 283841981 = 106440743) B106440743
theorem B4495123 : Blo 1819611 4495123 := bstep (se 1 (by rfl) ⟨3371342, by rfl⟩ : syracuseStep 4495123 = 6742685) B6742685
theorem B33208127 : Blo 1819611 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B18675593 : Blo 1819611 18675593 := bstep (se 2 (by rfl) ⟨7003347, by rfl⟩ : syracuseStep 18675593 = 14006695) B14006695
theorem B13121453 : Blo 1819611 13121453 := bstep (se 3 (by rfl) ⟨2460272, by rfl⟩ : syracuseStep 13121453 = 4920545) B4920545
theorem B9861115 : Blo 1819611 9861115 := bstep (se 1 (by rfl) ⟨7395836, by rfl⟩ : syracuseStep 9861115 = 14791673) B14791673
theorem B14759945 : Blo 1819611 14759945 := bstep (se 2 (by rfl) ⟨5534979, by rfl⟩ : syracuseStep 14759945 = 11069959) B11069959
theorem B6559919 : Blo 1819611 6559919 := bstep (se 1 (by rfl) ⟨4919939, by rfl⟩ : syracuseStep 6559919 = 9839879) B9839879
theorem B23320871 : Blo 1819611 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B9215207 : Blo 1819611 9215207 := bstep (se 1 (by rfl) ⟨6911405, by rfl⟩ : syracuseStep 9215207 = 13822811) B13822811
theorem B4095251 : Blo 1819611 4095251 := bstep (se 1 (by rfl) ⟨3071438, by rfl⟩ : syracuseStep 4095251 = 6142877) B6142877
theorem B4922707 : Blo 1819611 4922707 := bstep (se 1 (by rfl) ⟨3692030, by rfl⟩ : syracuseStep 4922707 = 7384061) B7384061
theorem B5914387 : Blo 1819611 5914387 := bstep (se 1 (by rfl) ⟨4435790, by rfl⟩ : syracuseStep 5914387 = 8871581) B8871581
theorem B3072073 : Blo 1819611 3072073 := bstep (se 2 (by rfl) ⟨1152027, by rfl⟩ : syracuseStep 3072073 = 2304055) B2304055
theorem B3072127 : Blo 1819611 3072127 := bstep (se 1 (by rfl) ⟨2304095, by rfl⟩ : syracuseStep 3072127 = 4608191) B4608191
theorem B8306849 : Blo 1819611 8306849 := bstep (se 2 (by rfl) ⟨3115068, by rfl⟩ : syracuseStep 8306849 = 6230137) B6230137
theorem B4096655 : Blo 1819611 4096655 := bstep (se 1 (by rfl) ⟨3072491, by rfl⟩ : syracuseStep 4096655 = 6144983) B6144983
theorem B91030259 : Blo 1819611 91030259 := bstep (se 1 (by rfl) ⟨68272694, by rfl⟩ : syracuseStep 91030259 = 136545389) B136545389
theorem B4096889 : Blo 1819611 4096889 := bstep (se 2 (by rfl) ⟨1536333, by rfl⟩ : syracuseStep 4096889 = 3072667) B3072667
theorem B189227987 : Blo 1819611 189227987 := bstep (se 1 (by rfl) ⟨141920990, by rfl⟩ : syracuseStep 189227987 = 283841981) B283841981
theorem B1819679 : Blo 1819611 1819679 := bstep (se 1 (by rfl) ⟨1364759, by rfl⟩ : syracuseStep 1819679 = 2729519) B2729519
theorem B9839963 : Blo 1819611 9839963 := bstep (se 1 (by rfl) ⟨7379972, by rfl⟩ : syracuseStep 9839963 = 14759945) B14759945
theorem B1820391 : Blo 1819611 1820391 := bstep (se 1 (by rfl) ⟨1365293, by rfl⟩ : syracuseStep 1820391 = 2730587) B2730587
theorem B3073801 : Blo 1819611 3073801 := bstep (se 2 (by rfl) ⟨1152675, by rfl⟩ : syracuseStep 3073801 = 2305351) B2305351
theorem B6563609 : Blo 1819611 6563609 := bstep (se 2 (by rfl) ⟨2461353, by rfl⟩ : syracuseStep 6563609 = 4922707) B4922707
theorem B1820667 : Blo 1819611 1820667 := bstep (se 1 (by rfl) ⟨1365500, by rfl⟩ : syracuseStep 1820667 = 2731001) B2731001
theorem B2730167 : Blo 1819611 2730167 := bstep (se 1 (by rfl) ⟨2047625, by rfl⟩ : syracuseStep 2730167 = 4095251) B4095251
theorem B1821351 : Blo 1819611 1821351 := bstep (se 1 (by rfl) ⟨1366013, by rfl⟩ : syracuseStep 1821351 = 2732027) B2732027
theorem B10373831 : Blo 1819611 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B1821415 : Blo 1819611 1821415 := bstep (se 1 (by rfl) ⟨1366061, by rfl⟩ : syracuseStep 1821415 = 2732123) B2732123
theorem B2730761 : Blo 1819611 2730761 := bstep (se 2 (by rfl) ⟨1024035, by rfl⟩ : syracuseStep 2730761 = 2048071) B2048071
theorem B1821551 : Blo 1819611 1821551 := bstep (se 1 (by rfl) ⟨1366163, by rfl⟩ : syracuseStep 1821551 = 2732327) B2732327
theorem B10366015 : Blo 1819611 10366015 := bstep (se 1 (by rfl) ⟨7774511, by rfl⟩ : syracuseStep 10366015 = 15549023) B15549023
theorem B22146143 : Blo 1819611 22146143 := bstep (se 1 (by rfl) ⟨16609607, by rfl⟩ : syracuseStep 22146143 = 33219215) B33219215
theorem B7777417 : Blo 1819611 7777417 := bstep (se 2 (by rfl) ⟨2916531, by rfl⟩ : syracuseStep 7777417 = 5833063) B5833063
theorem B9219257 : Blo 1819611 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B13307257 : Blo 1819611 13307257 := bstep (se 2 (by rfl) ⟨4990221, by rfl⟩ : syracuseStep 13307257 = 9980443) B9980443
theorem B35491301 : Blo 1819611 35491301 := bstep (se 4 (by rfl) ⟨3327309, by rfl⟩ : syracuseStep 35491301 = 6654619) B6654619
theorem B9219581 : Blo 1819611 9219581 := bstep (se 3 (by rfl) ⟨1728671, by rfl⟩ : syracuseStep 9219581 = 3457343) B3457343
theorem B22138751 : Blo 1819611 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B2732087 : Blo 1819611 2732087 := bstep (se 1 (by rfl) ⟨2049065, by rfl⟩ : syracuseStep 2732087 = 4098131) B4098131
theorem B182087741 : Blo 1819611 182087741 := bstep (se 3 (by rfl) ⟨34141451, by rfl⟩ : syracuseStep 182087741 = 68282903) B68282903
theorem B149467781 : Blo 1819611 149467781 := bstep (se 4 (by rfl) ⟨14012604, by rfl⟩ : syracuseStep 149467781 = 28025209) B28025209
theorem B5993497 : Blo 1819611 5993497 := bstep (se 2 (by rfl) ⟨2247561, by rfl⟩ : syracuseStep 5993497 = 4495123) B4495123
theorem B7885849 : Blo 1819611 7885849 := bstep (se 2 (by rfl) ⟨2957193, by rfl⟩ : syracuseStep 7885849 = 5914387) B5914387
theorem B9844679 : Blo 1819611 9844679 := bstep (se 1 (by rfl) ⟨7383509, by rfl⟩ : syracuseStep 9844679 = 14767019) B14767019
theorem B31094765 : Blo 1819611 31094765 := bstep (se 3 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 31094765 = 11660537) B11660537
theorem B4372471 : Blo 1819611 4372471 := bstep (se 1 (by rfl) ⟨3279353, by rfl⟩ : syracuseStep 4372471 = 6558707) B6558707
theorem B3454967 : Blo 1819611 3454967 := bstep (se 1 (by rfl) ⟨2591225, by rfl⟩ : syracuseStep 3454967 = 5182451) B5182451
theorem B383523173 : Blo 1819611 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B3889529 : Blo 1819611 3889529 := bstep (se 2 (by rfl) ⟨1458573, by rfl⟩ : syracuseStep 3889529 = 2917147) B2917147
theorem B12450395 : Blo 1819611 12450395 := bstep (se 1 (by rfl) ⟨9337796, by rfl⟩ : syracuseStep 12450395 = 18675593) B18675593
theorem B8747635 : Blo 1819611 8747635 := bstep (se 1 (by rfl) ⟨6560726, by rfl⟩ : syracuseStep 8747635 = 13121453) B13121453
theorem B4373279 : Blo 1819611 4373279 := bstep (se 1 (by rfl) ⟨3279959, by rfl⟩ : syracuseStep 4373279 = 6559919) B6559919
theorem B15547247 : Blo 1819611 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B4610945 : Blo 1819611 4610945 := bstep (se 2 (by rfl) ⟨1729104, by rfl⟩ : syracuseStep 4610945 = 3458209) B3458209
theorem B3070919 : Blo 1819611 3070919 := bstep (se 1 (by rfl) ⟨2303189, by rfl⟩ : syracuseStep 3070919 = 4606379) B4606379
theorem B15547625 : Blo 1819611 15547625 := bstep (se 2 (by rfl) ⟨5830359, by rfl⟩ : syracuseStep 15547625 = 11660719) B11660719
theorem B6143471 : Blo 1819611 6143471 := bstep (se 1 (by rfl) ⟨4607603, by rfl⟩ : syracuseStep 6143471 = 9215207) B9215207
theorem B18693665 : Blo 1819611 18693665 := bstep (se 2 (by rfl) ⟨7010124, by rfl⟩ : syracuseStep 18693665 = 14020249) B14020249
theorem B9215855 : Blo 1819611 9215855 := bstep (se 1 (by rfl) ⟨6911891, by rfl⟩ : syracuseStep 9215855 = 13823783) B13823783
theorem B13148153 : Blo 1819611 13148153 := bstep (se 2 (by rfl) ⟨4930557, by rfl⟩ : syracuseStep 13148153 = 9861115) B9861115
theorem B4096097 : Blo 1819611 4096097 := bstep (se 2 (by rfl) ⟨1536036, by rfl⟩ : syracuseStep 4096097 = 3072073) B3072073
theorem B5537899 : Blo 1819611 5537899 := bstep (se 1 (by rfl) ⟨4153424, by rfl⟩ : syracuseStep 5537899 = 8306849) B8306849
theorem B31965317 : Blo 1819611 31965317 := bstep (se 4 (by rfl) ⟨2996748, by rfl⟩ : syracuseStep 31965317 = 5993497) B5993497
theorem B4096169 : Blo 1819611 4096169 := bstep (se 2 (by rfl) ⟨1536063, by rfl⟩ : syracuseStep 4096169 = 3072127) B3072127
theorem B59056381 : Blo 1819611 59056381 := bstep (se 3 (by rfl) ⟨11073071, by rfl⟩ : syracuseStep 59056381 = 22146143) B22146143
theorem B60686839 : Blo 1819611 60686839 := bstep (se 1 (by rfl) ⟨45515129, by rfl⟩ : syracuseStep 60686839 = 91030259) B91030259
theorem B4375739 : Blo 1819611 4375739 := bstep (se 1 (by rfl) ⟨3281804, by rfl⟩ : syracuseStep 4375739 = 6563609) B6563609
theorem B6563119 : Blo 1819611 6563119 := bstep (se 1 (by rfl) ⟨4922339, by rfl⟩ : syracuseStep 6563119 = 9844679) B9844679
theorem B2303311 : Blo 1819611 2303311 := bstep (se 1 (by rfl) ⟨1727483, by rfl⟩ : syracuseStep 2303311 = 3454967) B3454967
theorem B13821353 : Blo 1819611 13821353 := bstep (se 2 (by rfl) ⟨5183007, by rfl⟩ : syracuseStep 13821353 = 10366015) B10366015
theorem B1820111 : Blo 1819611 1820111 := bstep (se 1 (by rfl) ⟨1365083, by rfl⟩ : syracuseStep 1820111 = 2730167) B2730167
theorem B255682115 : Blo 1819611 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B6915887 : Blo 1819611 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B1820507 : Blo 1819611 1820507 := bstep (se 1 (by rfl) ⟨1365380, by rfl⟩ : syracuseStep 1820507 = 2730761) B2730761
theorem B10364831 : Blo 1819611 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B3073963 : Blo 1819611 3073963 := bstep (se 1 (by rfl) ⟨2305472, by rfl⟩ : syracuseStep 3073963 = 4610945) B4610945
theorem B6146171 : Blo 1819611 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B10365083 : Blo 1819611 10365083 := bstep (se 1 (by rfl) ⟨7773812, by rfl⟩ : syracuseStep 10365083 = 15547625) B15547625
theorem B23660867 : Blo 1819611 23660867 := bstep (se 1 (by rfl) ⟨17745650, by rfl⟩ : syracuseStep 23660867 = 35491301) B35491301
theorem B6146387 : Blo 1819611 6146387 := bstep (se 1 (by rfl) ⟨4609790, by rfl⟩ : syracuseStep 6146387 = 9219581) B9219581
theorem B4098401 : Blo 1819611 4098401 := bstep (se 2 (by rfl) ⟨1536900, by rfl⟩ : syracuseStep 4098401 = 3073801) B3073801
theorem B12462443 : Blo 1819611 12462443 := bstep (se 1 (by rfl) ⟨9346832, by rfl⟩ : syracuseStep 12462443 = 18693665) B18693665
theorem B1821391 : Blo 1819611 1821391 := bstep (se 1 (by rfl) ⟨1366043, by rfl⟩ : syracuseStep 1821391 = 2732087) B2732087
theorem B121391827 : Blo 1819611 121391827 := bstep (se 1 (by rfl) ⟨91043870, by rfl⟩ : syracuseStep 121391827 = 182087741) B182087741
theorem B2731103 : Blo 1819611 2731103 := bstep (se 1 (by rfl) ⟨2048327, by rfl⟩ : syracuseStep 2731103 = 4096655) B4096655
theorem B2731259 : Blo 1819611 2731259 := bstep (se 1 (by rfl) ⟨2048444, by rfl⟩ : syracuseStep 2731259 = 4096889) B4096889
theorem B126151991 : Blo 1819611 126151991 := bstep (se 1 (by rfl) ⟨94613993, by rfl⟩ : syracuseStep 126151991 = 189227987) B189227987
theorem B20729843 : Blo 1819611 20729843 := bstep (se 1 (by rfl) ⟨15547382, by rfl⟩ : syracuseStep 20729843 = 31094765) B31094765
theorem B10514465 : Blo 1819611 10514465 := bstep (se 2 (by rfl) ⟨3942924, by rfl⟩ : syracuseStep 10514465 = 7885849) B7885849
theorem B2593019 : Blo 1819611 2593019 := bstep (se 1 (by rfl) ⟨1944764, by rfl⟩ : syracuseStep 2593019 = 3889529) B3889529
theorem B14759167 : Blo 1819611 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B23319845 : Blo 1819611 23319845 := bstep (se 4 (by rfl) ⟨2186235, by rfl⟩ : syracuseStep 23319845 = 4372471) B4372471
theorem B11663513 : Blo 1819611 11663513 := bstep (se 2 (by rfl) ⟨4373817, by rfl⟩ : syracuseStep 11663513 = 8747635) B8747635
theorem B6559975 : Blo 1819611 6559975 := bstep (se 1 (by rfl) ⟨4919981, by rfl⟩ : syracuseStep 6559975 = 9839963) B9839963
theorem B10369889 : Blo 1819611 10369889 := bstep (se 2 (by rfl) ⟨3888708, by rfl⟩ : syracuseStep 10369889 = 7777417) B7777417
theorem B33201053 : Blo 1819611 33201053 := bstep (se 3 (by rfl) ⟨6225197, by rfl⟩ : syracuseStep 33201053 = 12450395) B12450395
theorem B398580749 : Blo 1819611 398580749 := bstep (se 3 (by rfl) ⟨74733890, by rfl⟩ : syracuseStep 398580749 = 149467781) B149467781
theorem B17743009 : Blo 1819611 17743009 := bstep (se 2 (by rfl) ⟨6653628, by rfl⟩ : syracuseStep 17743009 = 13307257) B13307257
theorem B2915519 : Blo 1819611 2915519 := bstep (se 1 (by rfl) ⟨2186639, by rfl⟩ : syracuseStep 2915519 = 4373279) B4373279
theorem B2047279 : Blo 1819611 2047279 := bstep (se 1 (by rfl) ⟨1535459, by rfl⟩ : syracuseStep 2047279 = 3070919) B3070919
theorem B4095647 : Blo 1819611 4095647 := bstep (se 1 (by rfl) ⟨3071735, by rfl⟩ : syracuseStep 4095647 = 6143471) B6143471
theorem B6143903 : Blo 1819611 6143903 := bstep (se 1 (by rfl) ⟨4607927, by rfl⟩ : syracuseStep 6143903 = 9215855) B9215855
theorem B8765435 : Blo 1819611 8765435 := bstep (se 1 (by rfl) ⟨6574076, by rfl⟩ : syracuseStep 8765435 = 13148153) B13148153
theorem B78741841 : Blo 1819611 78741841 := bstep (se 2 (by rfl) ⟨29528190, by rfl⟩ : syracuseStep 78741841 = 59056381) B59056381
theorem B7774717 : Blo 1819611 7774717 := bstep (se 3 (by rfl) ⟨1457759, by rfl⟩ : syracuseStep 7774717 = 2915519) B2915519
theorem B6914717 : Blo 1819611 6914717 := bstep (se 3 (by rfl) ⟨1296509, by rfl⟩ : syracuseStep 6914717 = 2593019) B2593019
theorem B63095645 : Blo 1819611 63095645 := bstep (se 3 (by rfl) ⟨11830433, by rfl⟩ : syracuseStep 63095645 = 23660867) B23660867
theorem B647423077 : Blo 1819611 647423077 := bstep (se 4 (by rfl) ⟨60695913, by rfl⟩ : syracuseStep 647423077 = 121391827) B121391827
theorem B4097447 : Blo 1819611 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B7775675 : Blo 1819611 7775675 := bstep (se 1 (by rfl) ⟨5831756, by rfl⟩ : syracuseStep 7775675 = 11663513) B11663513
theorem B4097591 : Blo 1819611 4097591 := bstep (se 1 (by rfl) ⟨3073193, by rfl⟩ : syracuseStep 4097591 = 6146387) B6146387
theorem B8308295 : Blo 1819611 8308295 := bstep (se 1 (by rfl) ⟨6231221, by rfl⟩ : syracuseStep 8308295 = 12462443) B12462443
theorem B19678889 : Blo 1819611 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B2729705 : Blo 1819611 2729705 := bstep (se 2 (by rfl) ⟨1023639, by rfl⟩ : syracuseStep 2729705 = 2047279) B2047279
theorem B8750825 : Blo 1819611 8750825 := bstep (se 2 (by rfl) ⟨3281559, by rfl⟩ : syracuseStep 8750825 = 6563119) B6563119
theorem B1820735 : Blo 1819611 1820735 := bstep (se 1 (by rfl) ⟨1365551, by rfl⟩ : syracuseStep 1820735 = 2731103) B2731103
theorem B1820839 : Blo 1819611 1820839 := bstep (se 1 (by rfl) ⟨1365629, by rfl⟩ : syracuseStep 1820839 = 2731259) B2731259
theorem B84101327 : Blo 1819611 84101327 := bstep (se 1 (by rfl) ⟨63075995, by rfl⟩ : syracuseStep 84101327 = 126151991) B126151991
theorem B2730431 : Blo 1819611 2730431 := bstep (se 1 (by rfl) ⟨2047823, by rfl⟩ : syracuseStep 2730431 = 4095647) B4095647
theorem B4098617 : Blo 1819611 4098617 := bstep (se 2 (by rfl) ⟨1536981, by rfl⟩ : syracuseStep 4098617 = 3073963) B3073963
theorem B5843623 : Blo 1819611 5843623 := bstep (se 1 (by rfl) ⟨4382717, by rfl⟩ : syracuseStep 5843623 = 8765435) B8765435
theorem B2730731 : Blo 1819611 2730731 := bstep (se 1 (by rfl) ⟨2048048, by rfl⟩ : syracuseStep 2730731 = 4096097) B4096097
theorem B2730779 : Blo 1819611 2730779 := bstep (se 1 (by rfl) ⟨2048084, by rfl⟩ : syracuseStep 2730779 = 4096169) B4096169
theorem B7383865 : Blo 1819611 7383865 := bstep (se 2 (by rfl) ⟨2768949, by rfl⟩ : syracuseStep 7383865 = 5537899) B5537899
theorem B11668637 : Blo 1819611 11668637 := bstep (se 3 (by rfl) ⟨2187869, by rfl⟩ : syracuseStep 11668637 = 4375739) B4375739
theorem B170454743 : Blo 1819611 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B6909887 : Blo 1819611 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B340963381 : Blo 1819611 340963381 := bstep (se 5 (by rfl) ⟨15982658, by rfl⟩ : syracuseStep 340963381 = 31965317) B31965317
theorem B6910055 : Blo 1819611 6910055 := bstep (se 1 (by rfl) ⟨5182541, by rfl⟩ : syracuseStep 6910055 = 10365083) B10365083
theorem B2732267 : Blo 1819611 2732267 := bstep (se 1 (by rfl) ⟨2049200, by rfl⟩ : syracuseStep 2732267 = 4098401) B4098401
theorem B265720499 : Blo 1819611 265720499 := bstep (se 1 (by rfl) ⟨199290374, by rfl⟩ : syracuseStep 265720499 = 398580749) B398580749
theorem B323663141 : Blo 1819611 323663141 := bstep (se 4 (by rfl) ⟨30343419, by rfl⟩ : syracuseStep 323663141 = 60686839) B60686839
theorem B7009643 : Blo 1819611 7009643 := bstep (se 1 (by rfl) ⟨5257232, by rfl⟩ : syracuseStep 7009643 = 10514465) B10514465
theorem B8746633 : Blo 1819611 8746633 := bstep (se 2 (by rfl) ⟨3279987, by rfl⟩ : syracuseStep 8746633 = 6559975) B6559975
theorem B15546563 : Blo 1819611 15546563 := bstep (se 1 (by rfl) ⟨11659922, by rfl⟩ : syracuseStep 15546563 = 23319845) B23319845
theorem B9214235 : Blo 1819611 9214235 := bstep (se 1 (by rfl) ⟨6910676, by rfl⟩ : syracuseStep 9214235 = 13821353) B13821353
theorem B4610591 : Blo 1819611 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B23657345 : Blo 1819611 23657345 := bstep (se 2 (by rfl) ⟨8871504, by rfl⟩ : syracuseStep 23657345 = 17743009) B17743009
theorem B3071081 : Blo 1819611 3071081 := bstep (se 2 (by rfl) ⟨1151655, by rfl⟩ : syracuseStep 3071081 = 2303311) B2303311
theorem B6913259 : Blo 1819611 6913259 := bstep (se 1 (by rfl) ⟨5184944, by rfl⟩ : syracuseStep 6913259 = 10369889) B10369889
theorem B22134035 : Blo 1819611 22134035 := bstep (se 1 (by rfl) ⟨16600526, by rfl⟩ : syracuseStep 22134035 = 33201053) B33201053
theorem B4095935 : Blo 1819611 4095935 := bstep (se 1 (by rfl) ⟨3071951, by rfl⟩ : syracuseStep 4095935 = 6143903) B6143903
theorem B13819895 : Blo 1819611 13819895 := bstep (se 1 (by rfl) ⟨10364921, by rfl⟩ : syracuseStep 13819895 = 20729843) B20729843
theorem B104989121 : Blo 1819611 104989121 := bstep (se 2 (by rfl) ⟨39370920, by rfl⟩ : syracuseStep 104989121 = 78741841) B78741841
theorem B7791497 : Blo 1819611 7791497 := bstep (se 2 (by rfl) ⟨2921811, by rfl⟩ : syracuseStep 7791497 = 5843623) B5843623
theorem B5538863 : Blo 1819611 5538863 := bstep (se 1 (by rfl) ⟨4154147, by rfl⟩ : syracuseStep 5538863 = 8308295) B8308295
theorem B1819803 : Blo 1819611 1819803 := bstep (se 1 (by rfl) ⟨1364852, by rfl⟩ : syracuseStep 1819803 = 2729705) B2729705
theorem B5833883 : Blo 1819611 5833883 := bstep (se 1 (by rfl) ⟨4375412, by rfl⟩ : syracuseStep 5833883 = 8750825) B8750825
theorem B10364375 : Blo 1819611 10364375 := bstep (se 1 (by rfl) ⟨7773281, by rfl⟩ : syracuseStep 10364375 = 15546563) B15546563
theorem B56067551 : Blo 1819611 56067551 := bstep (se 1 (by rfl) ⟨42050663, by rfl⟩ : syracuseStep 56067551 = 84101327) B84101327
theorem B1820287 : Blo 1819611 1820287 := bstep (se 1 (by rfl) ⟨1365215, by rfl⟩ : syracuseStep 1820287 = 2730431) B2730431
theorem B3073727 : Blo 1819611 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B1820487 : Blo 1819611 1820487 := bstep (se 1 (by rfl) ⟨1365365, by rfl⟩ : syracuseStep 1820487 = 2730731) B2730731
theorem B1820519 : Blo 1819611 1820519 := bstep (se 1 (by rfl) ⟨1365389, by rfl⟩ : syracuseStep 1820519 = 2730779) B2730779
theorem B15771563 : Blo 1819611 15771563 := bstep (se 1 (by rfl) ⟨11828672, by rfl⟩ : syracuseStep 15771563 = 23657345) B23657345
theorem B14756023 : Blo 1819611 14756023 := bstep (se 1 (by rfl) ⟨11067017, by rfl⟩ : syracuseStep 14756023 = 22134035) B22134035
theorem B4606591 : Blo 1819611 4606591 := bstep (se 1 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 4606591 = 6909887) B6909887
theorem B2730623 : Blo 1819611 2730623 := bstep (se 1 (by rfl) ⟨2047967, by rfl⟩ : syracuseStep 2730623 = 4095935) B4095935
theorem B4606703 : Blo 1819611 4606703 := bstep (se 1 (by rfl) ⟨3455027, by rfl⟩ : syracuseStep 4606703 = 6910055) B6910055
theorem B454617841 : Blo 1819611 454617841 := bstep (se 2 (by rfl) ⟨170481690, by rfl⟩ : syracuseStep 454617841 = 340963381) B340963381
theorem B1821511 : Blo 1819611 1821511 := bstep (se 1 (by rfl) ⟨1366133, by rfl⟩ : syracuseStep 1821511 = 2732267) B2732267
theorem B177146999 : Blo 1819611 177146999 := bstep (se 1 (by rfl) ⟨132860249, by rfl⟩ : syracuseStep 177146999 = 265720499) B265720499
theorem B10366289 : Blo 1819611 10366289 := bstep (se 2 (by rfl) ⟨3887358, by rfl⟩ : syracuseStep 10366289 = 7774717) B7774717
theorem B46648709 : Blo 1819611 46648709 := bstep (se 4 (by rfl) ⟨4373316, by rfl⟩ : syracuseStep 46648709 = 8746633) B8746633
theorem B4673095 : Blo 1819611 4673095 := bstep (se 1 (by rfl) ⟨3504821, by rfl⟩ : syracuseStep 4673095 = 7009643) B7009643
theorem B2731631 : Blo 1819611 2731631 := bstep (se 1 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 2731631 = 4097447) B4097447
theorem B2731727 : Blo 1819611 2731727 := bstep (se 1 (by rfl) ⟨2048795, by rfl⟩ : syracuseStep 2731727 = 4097591) B4097591
theorem B13119259 : Blo 1819611 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B2732411 : Blo 1819611 2732411 := bstep (se 1 (by rfl) ⟨2049308, by rfl⟩ : syracuseStep 2732411 = 4098617) B4098617
theorem B7779091 : Blo 1819611 7779091 := bstep (se 1 (by rfl) ⟨5834318, by rfl⟩ : syracuseStep 7779091 = 11668637) B11668637
theorem B4608839 : Blo 1819611 4608839 := bstep (se 1 (by rfl) ⟨3456629, by rfl⟩ : syracuseStep 4608839 = 6913259) B6913259
theorem B113636495 : Blo 1819611 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B9213263 : Blo 1819611 9213263 := bstep (se 1 (by rfl) ⟨6909947, by rfl⟩ : syracuseStep 9213263 = 13819895) B13819895
theorem B4609811 : Blo 1819611 4609811 := bstep (se 1 (by rfl) ⟨3457358, by rfl⟩ : syracuseStep 4609811 = 6914717) B6914717
theorem B215775427 : Blo 1819611 215775427 := bstep (se 1 (by rfl) ⟨161831570, by rfl⟩ : syracuseStep 215775427 = 323663141) B323663141
theorem B5183783 : Blo 1819611 5183783 := bstep (se 1 (by rfl) ⟨3887837, by rfl⟩ : syracuseStep 5183783 = 7775675) B7775675
theorem B9845153 : Blo 1819611 9845153 := bstep (se 2 (by rfl) ⟨3691932, by rfl⟩ : syracuseStep 9845153 = 7383865) B7383865
theorem B863230769 : Blo 1819611 863230769 := bstep (se 2 (by rfl) ⟨323711538, by rfl⟩ : syracuseStep 863230769 = 647423077) B647423077
theorem B6142823 : Blo 1819611 6142823 := bstep (se 1 (by rfl) ⟨4607117, by rfl⟩ : syracuseStep 6142823 = 9214235) B9214235
theorem B2047387 : Blo 1819611 2047387 := bstep (se 1 (by rfl) ⟨1535540, by rfl⟩ : syracuseStep 2047387 = 3071081) B3071081
theorem B168255053 : Blo 1819611 168255053 := bstep (se 3 (by rfl) ⟨31547822, by rfl⟩ : syracuseStep 168255053 = 63095645) B63095645
theorem B69992747 : Blo 1819611 69992747 := bstep (se 1 (by rfl) ⟨52494560, by rfl⟩ : syracuseStep 69992747 = 104989121) B104989121
theorem B15557021 : Blo 1819611 15557021 := bstep (se 3 (by rfl) ⟨2916941, by rfl⟩ : syracuseStep 15557021 = 5833883) B5833883
theorem B3072559 : Blo 1819611 3072559 := bstep (se 1 (by rfl) ⟨2304419, by rfl⟩ : syracuseStep 3072559 = 4608839) B4608839
theorem B5194331 : Blo 1819611 5194331 := bstep (se 1 (by rfl) ⟨3895748, by rfl⟩ : syracuseStep 5194331 = 7791497) B7791497
theorem B10372121 : Blo 1819611 10372121 := bstep (se 2 (by rfl) ⟨3889545, by rfl⟩ : syracuseStep 10372121 = 7779091) B7779091
theorem B2049151 : Blo 1819611 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B3073207 : Blo 1819611 3073207 := bstep (se 1 (by rfl) ⟨2304905, by rfl⟩ : syracuseStep 3073207 = 4609811) B4609811
theorem B6563435 : Blo 1819611 6563435 := bstep (se 1 (by rfl) ⟨4922576, by rfl⟩ : syracuseStep 6563435 = 9845153) B9845153
theorem B1820415 : Blo 1819611 1820415 := bstep (se 1 (by rfl) ⟨1365311, by rfl⟩ : syracuseStep 1820415 = 2730623) B2730623
theorem B2729849 : Blo 1819611 2729849 := bstep (se 2 (by rfl) ⟨1023693, by rfl⟩ : syracuseStep 2729849 = 2047387) B2047387
theorem B118097999 : Blo 1819611 118097999 := bstep (se 1 (by rfl) ⟨88573499, by rfl⟩ : syracuseStep 118097999 = 177146999) B177146999
theorem B31099139 : Blo 1819611 31099139 := bstep (se 1 (by rfl) ⟨23324354, by rfl⟩ : syracuseStep 31099139 = 46648709) B46648709
theorem B17492345 : Blo 1819611 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B1821087 : Blo 1819611 1821087 := bstep (se 1 (by rfl) ⟨1365815, by rfl⟩ : syracuseStep 1821087 = 2731631) B2731631
theorem B1821151 : Blo 1819611 1821151 := bstep (se 1 (by rfl) ⟨1365863, by rfl⟩ : syracuseStep 1821151 = 2731727) B2731727
theorem B1821607 : Blo 1819611 1821607 := bstep (se 1 (by rfl) ⟨1366205, by rfl⟩ : syracuseStep 1821607 = 2732411) B2732411
theorem B24923173 : Blo 1819611 24923173 := bstep (se 4 (by rfl) ⟨2336547, by rfl⟩ : syracuseStep 24923173 = 4673095) B4673095
theorem B6909583 : Blo 1819611 6909583 := bstep (se 1 (by rfl) ⟨5182187, by rfl⟩ : syracuseStep 6909583 = 10364375) B10364375
theorem B10514375 : Blo 1819611 10514375 := bstep (se 1 (by rfl) ⟨7885781, by rfl⟩ : syracuseStep 10514375 = 15771563) B15771563
theorem B6910859 : Blo 1819611 6910859 := bstep (se 1 (by rfl) ⟨5183144, by rfl⟩ : syracuseStep 6910859 = 10366289) B10366289
theorem B112170035 : Blo 1819611 112170035 := bstep (se 1 (by rfl) ⟨84127526, by rfl⟩ : syracuseStep 112170035 = 168255053) B168255053
theorem B19674697 : Blo 1819611 19674697 := bstep (se 2 (by rfl) ⟨7378011, by rfl⟩ : syracuseStep 19674697 = 14756023) B14756023
theorem B287700569 : Blo 1819611 287700569 := bstep (se 2 (by rfl) ⟨107887713, by rfl⟩ : syracuseStep 287700569 = 215775427) B215775427
theorem B3692575 : Blo 1819611 3692575 := bstep (se 1 (by rfl) ⟨2769431, by rfl⟩ : syracuseStep 3692575 = 5538863) B5538863
theorem B75757663 : Blo 1819611 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B6142121 : Blo 1819611 6142121 := bstep (se 2 (by rfl) ⟨2303295, by rfl⟩ : syracuseStep 6142121 = 4606591) B4606591
theorem B6142175 : Blo 1819611 6142175 := bstep (se 1 (by rfl) ⟨4606631, by rfl⟩ : syracuseStep 6142175 = 9213263) B9213263
theorem B37378367 : Blo 1819611 37378367 := bstep (se 1 (by rfl) ⟨28033775, by rfl⟩ : syracuseStep 37378367 = 56067551) B56067551
theorem B606157121 : Blo 1819611 606157121 := bstep (se 2 (by rfl) ⟨227308920, by rfl⟩ : syracuseStep 606157121 = 454617841) B454617841
theorem B3455855 : Blo 1819611 3455855 := bstep (se 1 (by rfl) ⟨2591891, by rfl⟩ : syracuseStep 3455855 = 5183783) B5183783
theorem B3071135 : Blo 1819611 3071135 := bstep (se 1 (by rfl) ⟨2303351, by rfl⟩ : syracuseStep 3071135 = 4606703) B4606703
theorem B575487179 : Blo 1819611 575487179 := bstep (se 1 (by rfl) ⟨431615384, by rfl⟩ : syracuseStep 575487179 = 863230769) B863230769
theorem B4095215 : Blo 1819611 4095215 := bstep (se 1 (by rfl) ⟨3071411, by rfl⟩ : syracuseStep 4095215 = 6142823) B6142823
theorem B4923433 : Blo 1819611 4923433 := bstep (se 2 (by rfl) ⟨1846287, by rfl⟩ : syracuseStep 4923433 = 3692575) B3692575
theorem B46661831 : Blo 1819611 46661831 := bstep (se 1 (by rfl) ⟨34996373, by rfl⟩ : syracuseStep 46661831 = 69992747) B69992747
theorem B10371347 : Blo 1819611 10371347 := bstep (se 1 (by rfl) ⟨7778510, by rfl⟩ : syracuseStep 10371347 = 15557021) B15557021
theorem B6914747 : Blo 1819611 6914747 := bstep (se 1 (by rfl) ⟨5186060, by rfl⟩ : syracuseStep 6914747 = 10372121) B10372121
theorem B4096745 : Blo 1819611 4096745 := bstep (se 2 (by rfl) ⟨1536279, by rfl⟩ : syracuseStep 4096745 = 3072559) B3072559
theorem B191800379 : Blo 1819611 191800379 := bstep (se 1 (by rfl) ⟨143850284, by rfl⟩ : syracuseStep 191800379 = 287700569) B287700569
theorem B1819899 : Blo 1819611 1819899 := bstep (se 1 (by rfl) ⟨1364924, by rfl⟩ : syracuseStep 1819899 = 2729849) B2729849
theorem B404104747 : Blo 1819611 404104747 := bstep (se 1 (by rfl) ⟨303078560, by rfl⟩ : syracuseStep 404104747 = 606157121) B606157121
theorem B4097609 : Blo 1819611 4097609 := bstep (se 2 (by rfl) ⟨1536603, by rfl⟩ : syracuseStep 4097609 = 3073207) B3073207
theorem B2303903 : Blo 1819611 2303903 := bstep (se 1 (by rfl) ⟨1727927, by rfl⟩ : syracuseStep 2303903 = 3455855) B3455855
theorem B26232929 : Blo 1819611 26232929 := bstep (se 2 (by rfl) ⟨9837348, by rfl⟩ : syracuseStep 26232929 = 19674697) B19674697
theorem B383658119 : Blo 1819611 383658119 := bstep (se 1 (by rfl) ⟨287743589, by rfl⟩ : syracuseStep 383658119 = 575487179) B575487179
theorem B2730143 : Blo 1819611 2730143 := bstep (se 1 (by rfl) ⟨2047607, by rfl⟩ : syracuseStep 2730143 = 4095215) B4095215
theorem B404040869 : Blo 1819611 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B4607239 : Blo 1819611 4607239 := bstep (se 1 (by rfl) ⟨3455429, by rfl⟩ : syracuseStep 4607239 = 6910859) B6910859
theorem B74780023 : Blo 1819611 74780023 := bstep (se 1 (by rfl) ⟨56085017, by rfl⟩ : syracuseStep 74780023 = 112170035) B112170035
theorem B33230897 : Blo 1819611 33230897 := bstep (se 2 (by rfl) ⟨12461586, by rfl⟩ : syracuseStep 33230897 = 24923173) B24923173
theorem B2732201 : Blo 1819611 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B11661563 : Blo 1819611 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B17502493 : Blo 1819611 17502493 := bstep (se 3 (by rfl) ⟨3281717, by rfl⟩ : syracuseStep 17502493 = 6563435) B6563435
theorem B9212777 : Blo 1819611 9212777 := bstep (se 2 (by rfl) ⟨3454791, by rfl⟩ : syracuseStep 9212777 = 6909583) B6909583
theorem B7009583 : Blo 1819611 7009583 := bstep (se 1 (by rfl) ⟨5257187, by rfl⟩ : syracuseStep 7009583 = 10514375) B10514375
theorem B3462887 : Blo 1819611 3462887 := bstep (se 1 (by rfl) ⟨2597165, by rfl⟩ : syracuseStep 3462887 = 5194331) B5194331
theorem B78731999 : Blo 1819611 78731999 := bstep (se 1 (by rfl) ⟨59048999, by rfl⟩ : syracuseStep 78731999 = 118097999) B118097999
theorem B4094747 : Blo 1819611 4094747 := bstep (se 1 (by rfl) ⟨3071060, by rfl⟩ : syracuseStep 4094747 = 6142121) B6142121
theorem B4094783 : Blo 1819611 4094783 := bstep (se 1 (by rfl) ⟨3071087, by rfl⟩ : syracuseStep 4094783 = 6142175) B6142175
theorem B20732759 : Blo 1819611 20732759 := bstep (se 1 (by rfl) ⟨15549569, by rfl⟩ : syracuseStep 20732759 = 31099139) B31099139
theorem B24918911 : Blo 1819611 24918911 := bstep (se 1 (by rfl) ⟨18689183, by rfl⟩ : syracuseStep 24918911 = 37378367) B37378367
theorem B2047423 : Blo 1819611 2047423 := bstep (se 1 (by rfl) ⟨1535567, by rfl⟩ : syracuseStep 2047423 = 3071135) B3071135
theorem B7774375 : Blo 1819611 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B6914231 : Blo 1819611 6914231 := bstep (se 1 (by rfl) ⟨5185673, by rfl⟩ : syracuseStep 6914231 = 10371347) B10371347
theorem B255772079 : Blo 1819611 255772079 := bstep (se 1 (by rfl) ⟨191829059, by rfl⟩ : syracuseStep 255772079 = 383658119) B383658119
theorem B1820095 : Blo 1819611 1820095 := bstep (se 1 (by rfl) ⟨1365071, by rfl⟩ : syracuseStep 1820095 = 2730143) B2730143
theorem B52487999 : Blo 1819611 52487999 := bstep (se 1 (by rfl) ⟨39365999, by rfl⟩ : syracuseStep 52487999 = 78731999) B78731999
theorem B99706697 : Blo 1819611 99706697 := bstep (se 2 (by rfl) ⟨37390011, by rfl⟩ : syracuseStep 99706697 = 74780023) B74780023
theorem B2729831 : Blo 1819611 2729831 := bstep (se 1 (by rfl) ⟨2047373, by rfl⟩ : syracuseStep 2729831 = 4094747) B4094747
theorem B2729855 : Blo 1819611 2729855 := bstep (se 1 (by rfl) ⟨2047391, by rfl⟩ : syracuseStep 2729855 = 4094783) B4094783
theorem B13821839 : Blo 1819611 13821839 := bstep (se 1 (by rfl) ⟨10366379, by rfl⟩ : syracuseStep 13821839 = 20732759) B20732759
theorem B2729897 : Blo 1819611 2729897 := bstep (se 2 (by rfl) ⟨1023711, by rfl⟩ : syracuseStep 2729897 = 2047423) B2047423
theorem B538806329 : Blo 1819611 538806329 := bstep (se 2 (by rfl) ⟨202052373, by rfl⟩ : syracuseStep 538806329 = 404104747) B404104747
theorem B22153931 : Blo 1819611 22153931 := bstep (se 1 (by rfl) ⟨16615448, by rfl⟩ : syracuseStep 22153931 = 33230897) B33230897
theorem B6564577 : Blo 1819611 6564577 := bstep (se 2 (by rfl) ⟨2461716, by rfl⟩ : syracuseStep 6564577 = 4923433) B4923433
theorem B1821467 : Blo 1819611 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B31107887 : Blo 1819611 31107887 := bstep (se 1 (by rfl) ⟨23330915, by rfl⟩ : syracuseStep 31107887 = 46661831) B46661831
theorem B2731163 : Blo 1819611 2731163 := bstep (se 1 (by rfl) ⟨2048372, by rfl⟩ : syracuseStep 2731163 = 4096745) B4096745
theorem B2731739 : Blo 1819611 2731739 := bstep (se 1 (by rfl) ⟨2048804, by rfl⟩ : syracuseStep 2731739 = 4097609) B4097609
theorem B23336657 : Blo 1819611 23336657 := bstep (se 2 (by rfl) ⟨8751246, by rfl⟩ : syracuseStep 23336657 = 17502493) B17502493
theorem B4609831 : Blo 1819611 4609831 := bstep (se 1 (by rfl) ⟨3457373, by rfl⟩ : syracuseStep 4609831 = 6914747) B6914747
theorem B6141851 : Blo 1819611 6141851 := bstep (se 1 (by rfl) ⟨4606388, by rfl⟩ : syracuseStep 6141851 = 9212777) B9212777
theorem B127866919 : Blo 1819611 127866919 := bstep (se 1 (by rfl) ⟨95900189, by rfl⟩ : syracuseStep 127866919 = 191800379) B191800379
theorem B18692221 : Blo 1819611 18692221 := bstep (se 3 (by rfl) ⟨3504791, by rfl⟩ : syracuseStep 18692221 = 7009583) B7009583
theorem B2308591 : Blo 1819611 2308591 := bstep (se 1 (by rfl) ⟨1731443, by rfl⟩ : syracuseStep 2308591 = 3462887) B3462887
theorem B17488619 : Blo 1819611 17488619 := bstep (se 1 (by rfl) ⟨13116464, by rfl⟩ : syracuseStep 17488619 = 26232929) B26232929
theorem B6142985 : Blo 1819611 6142985 := bstep (se 2 (by rfl) ⟨2303619, by rfl⟩ : syracuseStep 6142985 = 4607239) B4607239
theorem B16612607 : Blo 1819611 16612607 := bstep (se 1 (by rfl) ⟨12459455, by rfl⟩ : syracuseStep 16612607 = 24918911) B24918911
theorem B269360579 : Blo 1819611 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B6143741 : Blo 1819611 6143741 := bstep (se 3 (by rfl) ⟨1151951, by rfl⟩ : syracuseStep 6143741 = 2303903) B2303903
theorem B15557771 : Blo 1819611 15557771 := bstep (se 1 (by rfl) ⟨11668328, by rfl⟩ : syracuseStep 15557771 = 23336657) B23336657
theorem B66471131 : Blo 1819611 66471131 := bstep (se 1 (by rfl) ⟨49853348, by rfl⟩ : syracuseStep 66471131 = 99706697) B99706697
theorem B1819887 : Blo 1819611 1819887 := bstep (se 1 (by rfl) ⟨1364915, by rfl⟩ : syracuseStep 1819887 = 2729831) B2729831
theorem B1819903 : Blo 1819611 1819903 := bstep (se 1 (by rfl) ⟨1364927, by rfl⟩ : syracuseStep 1819903 = 2729855) B2729855
theorem B1819931 : Blo 1819611 1819931 := bstep (se 1 (by rfl) ⟨1364948, by rfl⟩ : syracuseStep 1819931 = 2729897) B2729897
theorem B359204219 : Blo 1819611 359204219 := bstep (se 1 (by rfl) ⟨269403164, by rfl⟩ : syracuseStep 359204219 = 538806329) B538806329
theorem B11659079 : Blo 1819611 11659079 := bstep (se 1 (by rfl) ⟨8744309, by rfl⟩ : syracuseStep 11659079 = 17488619) B17488619
theorem B1820775 : Blo 1819611 1820775 := bstep (se 1 (by rfl) ⟨1365581, by rfl⟩ : syracuseStep 1820775 = 2731163) B2731163
theorem B6146441 : Blo 1819611 6146441 := bstep (se 2 (by rfl) ⟨2304915, by rfl⟩ : syracuseStep 6146441 = 4609831) B4609831
theorem B1821159 : Blo 1819611 1821159 := bstep (se 1 (by rfl) ⟨1365869, by rfl⟩ : syracuseStep 1821159 = 2731739) B2731739
theorem B24922961 : Blo 1819611 24922961 := bstep (se 2 (by rfl) ⟨9346110, by rfl⟩ : syracuseStep 24922961 = 18692221) B18692221
theorem B10365833 : Blo 1819611 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B8752769 : Blo 1819611 8752769 := bstep (se 2 (by rfl) ⟨3282288, by rfl⟩ : syracuseStep 8752769 = 6564577) B6564577
theorem B718294877 : Blo 1819611 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B34991999 : Blo 1819611 34991999 := bstep (se 1 (by rfl) ⟨26243999, by rfl⟩ : syracuseStep 34991999 = 52487999) B52487999
theorem B20738591 : Blo 1819611 20738591 := bstep (se 1 (by rfl) ⟨15553943, by rfl⟩ : syracuseStep 20738591 = 31107887) B31107887
theorem B170489225 : Blo 1819611 170489225 := bstep (se 2 (by rfl) ⟨63933459, by rfl⟩ : syracuseStep 170489225 = 127866919) B127866919
theorem B4609487 : Blo 1819611 4609487 := bstep (se 1 (by rfl) ⟨3457115, by rfl⟩ : syracuseStep 4609487 = 6914231) B6914231
theorem B170514719 : Blo 1819611 170514719 := bstep (se 1 (by rfl) ⟨127886039, by rfl⟩ : syracuseStep 170514719 = 255772079) B255772079
theorem B9214559 : Blo 1819611 9214559 := bstep (se 1 (by rfl) ⟨6910919, by rfl⟩ : syracuseStep 9214559 = 13821839) B13821839
theorem B4094567 : Blo 1819611 4094567 := bstep (se 1 (by rfl) ⟨3070925, by rfl⟩ : syracuseStep 4094567 = 6141851) B6141851
theorem B14769287 : Blo 1819611 14769287 := bstep (se 1 (by rfl) ⟨11076965, by rfl⟩ : syracuseStep 14769287 = 22153931) B22153931
theorem B4095323 : Blo 1819611 4095323 := bstep (se 1 (by rfl) ⟨3071492, by rfl⟩ : syracuseStep 4095323 = 6142985) B6142985
theorem B11075071 : Blo 1819611 11075071 := bstep (se 1 (by rfl) ⟨8306303, by rfl⟩ : syracuseStep 11075071 = 16612607) B16612607
theorem B4095827 : Blo 1819611 4095827 := bstep (se 1 (by rfl) ⟨3071870, by rfl⟩ : syracuseStep 4095827 = 6143741) B6143741
theorem B12312485 : Blo 1819611 12312485 := bstep (se 4 (by rfl) ⟨1154295, by rfl⟩ : syracuseStep 12312485 = 2308591) B2308591
theorem B10371847 : Blo 1819611 10371847 := bstep (se 1 (by rfl) ⟨7778885, by rfl⟩ : syracuseStep 10371847 = 15557771) B15557771
theorem B239469479 : Blo 1819611 239469479 := bstep (se 1 (by rfl) ⟨179602109, by rfl⟩ : syracuseStep 239469479 = 359204219) B359204219
theorem B3072991 : Blo 1819611 3072991 := bstep (se 1 (by rfl) ⟨2304743, by rfl⟩ : syracuseStep 3072991 = 4609487) B4609487
theorem B4097627 : Blo 1819611 4097627 := bstep (se 1 (by rfl) ⟨3073220, by rfl⟩ : syracuseStep 4097627 = 6146441) B6146441
theorem B2729711 : Blo 1819611 2729711 := bstep (se 1 (by rfl) ⟨2047283, by rfl⟩ : syracuseStep 2729711 = 4094567) B4094567
theorem B16615307 : Blo 1819611 16615307 := bstep (se 1 (by rfl) ⟨12461480, by rfl⟩ : syracuseStep 16615307 = 24922961) B24922961
theorem B2730215 : Blo 1819611 2730215 := bstep (se 1 (by rfl) ⟨2047661, by rfl⟩ : syracuseStep 2730215 = 4095323) B4095323
theorem B5835179 : Blo 1819611 5835179 := bstep (se 1 (by rfl) ⟨4376384, by rfl⟩ : syracuseStep 5835179 = 8752769) B8752769
theorem B2730551 : Blo 1819611 2730551 := bstep (se 1 (by rfl) ⟨2047913, by rfl⟩ : syracuseStep 2730551 = 4095827) B4095827
theorem B44314087 : Blo 1819611 44314087 := bstep (se 1 (by rfl) ⟨33235565, by rfl⟩ : syracuseStep 44314087 = 66471131) B66471131
theorem B113676479 : Blo 1819611 113676479 := bstep (se 1 (by rfl) ⟨85257359, by rfl⟩ : syracuseStep 113676479 = 170514719) B170514719
theorem B6910555 : Blo 1819611 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B14766761 : Blo 1819611 14766761 := bstep (se 2 (by rfl) ⟨5537535, by rfl⟩ : syracuseStep 14766761 = 11075071) B11075071
theorem B23327999 : Blo 1819611 23327999 := bstep (se 1 (by rfl) ⟨17495999, by rfl⟩ : syracuseStep 23327999 = 34991999) B34991999
theorem B13825727 : Blo 1819611 13825727 := bstep (se 1 (by rfl) ⟨10369295, by rfl⟩ : syracuseStep 13825727 = 20738591) B20738591
theorem B454637933 : Blo 1819611 454637933 := bstep (se 3 (by rfl) ⟨85244612, by rfl⟩ : syracuseStep 454637933 = 170489225) B170489225
theorem B7772719 : Blo 1819611 7772719 := bstep (se 1 (by rfl) ⟨5829539, by rfl⟩ : syracuseStep 7772719 = 11659079) B11659079
theorem B6143039 : Blo 1819611 6143039 := bstep (se 1 (by rfl) ⟨4607279, by rfl⟩ : syracuseStep 6143039 = 9214559) B9214559
theorem B9846191 : Blo 1819611 9846191 := bstep (se 1 (by rfl) ⟨7384643, by rfl⟩ : syracuseStep 9846191 = 14769287) B14769287
theorem B478863251 : Blo 1819611 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B8208323 : Blo 1819611 8208323 := bstep (se 1 (by rfl) ⟨6156242, by rfl⟩ : syracuseStep 8208323 = 12312485) B12312485
theorem B75784319 : Blo 1819611 75784319 := bstep (se 1 (by rfl) ⟨56838239, by rfl⟩ : syracuseStep 75784319 = 113676479) B113676479
theorem B159646319 : Blo 1819611 159646319 := bstep (se 1 (by rfl) ⟨119734739, by rfl⟩ : syracuseStep 159646319 = 239469479) B239469479
theorem B10363625 : Blo 1819611 10363625 := bstep (se 2 (by rfl) ⟨3886359, by rfl⟩ : syracuseStep 10363625 = 7772719) B7772719
theorem B13829129 : Blo 1819611 13829129 := bstep (se 2 (by rfl) ⟨5185923, by rfl⟩ : syracuseStep 13829129 = 10371847) B10371847
theorem B9217151 : Blo 1819611 9217151 := bstep (se 1 (by rfl) ⟨6912863, by rfl⟩ : syracuseStep 9217151 = 13825727) B13825727
theorem B1819807 : Blo 1819611 1819807 := bstep (se 1 (by rfl) ⟨1364855, by rfl⟩ : syracuseStep 1819807 = 2729711) B2729711
theorem B11076871 : Blo 1819611 11076871 := bstep (se 1 (by rfl) ⟨8307653, by rfl⟩ : syracuseStep 11076871 = 16615307) B16615307
theorem B4097321 : Blo 1819611 4097321 := bstep (se 2 (by rfl) ⟨1536495, by rfl⟩ : syracuseStep 4097321 = 3072991) B3072991
theorem B1820143 : Blo 1819611 1820143 := bstep (se 1 (by rfl) ⟨1365107, by rfl⟩ : syracuseStep 1820143 = 2730215) B2730215
theorem B1820367 : Blo 1819611 1820367 := bstep (se 1 (by rfl) ⟨1365275, by rfl⟩ : syracuseStep 1820367 = 2730551) B2730551
theorem B6564127 : Blo 1819611 6564127 := bstep (se 1 (by rfl) ⟨4923095, by rfl⟩ : syracuseStep 6564127 = 9846191) B9846191
theorem B15551999 : Blo 1819611 15551999 := bstep (se 1 (by rfl) ⟨11663999, by rfl⟩ : syracuseStep 15551999 = 23327999) B23327999
theorem B2731751 : Blo 1819611 2731751 := bstep (se 1 (by rfl) ⟨2048813, by rfl⟩ : syracuseStep 2731751 = 4097627) B4097627
theorem B303091955 : Blo 1819611 303091955 := bstep (se 1 (by rfl) ⟨227318966, by rfl⟩ : syracuseStep 303091955 = 454637933) B454637933
theorem B59085449 : Blo 1819611 59085449 := bstep (se 2 (by rfl) ⟨22157043, by rfl⟩ : syracuseStep 59085449 = 44314087) B44314087
theorem B9844507 : Blo 1819611 9844507 := bstep (se 1 (by rfl) ⟨7383380, by rfl⟩ : syracuseStep 9844507 = 14766761) B14766761
theorem B9214073 : Blo 1819611 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B3890119 : Blo 1819611 3890119 := bstep (se 1 (by rfl) ⟨2917589, by rfl⟩ : syracuseStep 3890119 = 5835179) B5835179
theorem B4095359 : Blo 1819611 4095359 := bstep (se 1 (by rfl) ⟨3071519, by rfl⟩ : syracuseStep 4095359 = 6143039) B6143039
theorem B319242167 : Blo 1819611 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B5472215 : Blo 1819611 5472215 := bstep (se 1 (by rfl) ⟨4104161, by rfl⟩ : syracuseStep 5472215 = 8208323) B8208323
theorem B106430879 : Blo 1819611 106430879 := bstep (se 1 (by rfl) ⟨79823159, by rfl⟩ : syracuseStep 106430879 = 159646319) B159646319
theorem B6144767 : Blo 1819611 6144767 := bstep (se 1 (by rfl) ⟨4608575, by rfl⟩ : syracuseStep 6144767 = 9217151) B9217151
theorem B5186825 : Blo 1819611 5186825 := bstep (se 2 (by rfl) ⟨1945059, by rfl⟩ : syracuseStep 5186825 = 3890119) B3890119
theorem B2730239 : Blo 1819611 2730239 := bstep (se 1 (by rfl) ⟨2047679, by rfl⟩ : syracuseStep 2730239 = 4095359) B4095359
theorem B13126009 : Blo 1819611 13126009 := bstep (se 2 (by rfl) ⟨4922253, by rfl⟩ : syracuseStep 13126009 = 9844507) B9844507
theorem B1821167 : Blo 1819611 1821167 := bstep (se 1 (by rfl) ⟨1365875, by rfl⟩ : syracuseStep 1821167 = 2731751) B2731751
theorem B3648143 : Blo 1819611 3648143 := bstep (se 1 (by rfl) ⟨2736107, by rfl⟩ : syracuseStep 3648143 = 5472215) B5472215
theorem B50522879 : Blo 1819611 50522879 := bstep (se 1 (by rfl) ⟨37892159, by rfl⟩ : syracuseStep 50522879 = 75784319) B75784319
theorem B8752169 : Blo 1819611 8752169 := bstep (se 2 (by rfl) ⟨3282063, by rfl⟩ : syracuseStep 8752169 = 6564127) B6564127
theorem B39390299 : Blo 1819611 39390299 := bstep (se 1 (by rfl) ⟨29542724, by rfl⟩ : syracuseStep 39390299 = 59085449) B59085449
theorem B6909083 : Blo 1819611 6909083 := bstep (se 1 (by rfl) ⟨5181812, by rfl⟩ : syracuseStep 6909083 = 10363625) B10363625
theorem B9219419 : Blo 1819611 9219419 := bstep (se 1 (by rfl) ⟨6914564, by rfl⟩ : syracuseStep 9219419 = 13829129) B13829129
theorem B2731547 : Blo 1819611 2731547 := bstep (se 1 (by rfl) ⟨2048660, by rfl⟩ : syracuseStep 2731547 = 4097321) B4097321
theorem B10367999 : Blo 1819611 10367999 := bstep (se 1 (by rfl) ⟨7775999, by rfl⟩ : syracuseStep 10367999 = 15551999) B15551999
theorem B202061303 : Blo 1819611 202061303 := bstep (se 1 (by rfl) ⟨151545977, by rfl⟩ : syracuseStep 202061303 = 303091955) B303091955
theorem B6142715 : Blo 1819611 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B14769161 : Blo 1819611 14769161 := bstep (se 2 (by rfl) ⟨5538435, by rfl⟩ : syracuseStep 14769161 = 11076871) B11076871
theorem B212828111 : Blo 1819611 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B23339117 : Blo 1819611 23339117 := bstep (se 3 (by rfl) ⟨4376084, by rfl⟩ : syracuseStep 23339117 = 8752169) B8752169
theorem B4096511 : Blo 1819611 4096511 := bstep (se 1 (by rfl) ⟨3072383, by rfl⟩ : syracuseStep 4096511 = 6144767) B6144767
theorem B3457883 : Blo 1819611 3457883 := bstep (se 1 (by rfl) ⟨2593412, by rfl⟩ : syracuseStep 3457883 = 5186825) B5186825
theorem B1820159 : Blo 1819611 1820159 := bstep (se 1 (by rfl) ⟨1365119, by rfl⟩ : syracuseStep 1820159 = 2730239) B2730239
theorem B4606055 : Blo 1819611 4606055 := bstep (se 1 (by rfl) ⟨3454541, by rfl⟩ : syracuseStep 4606055 = 6909083) B6909083
theorem B6146279 : Blo 1819611 6146279 := bstep (se 1 (by rfl) ⟨4609709, by rfl⟩ : syracuseStep 6146279 = 9219419) B9219419
theorem B1821031 : Blo 1819611 1821031 := bstep (se 1 (by rfl) ⟨1365773, by rfl⟩ : syracuseStep 1821031 = 2731547) B2731547
theorem B17501345 : Blo 1819611 17501345 := bstep (se 2 (by rfl) ⟨6563004, by rfl⟩ : syracuseStep 17501345 = 13126009) B13126009
theorem B283815677 : Blo 1819611 283815677 := bstep (se 3 (by rfl) ⟨53215439, by rfl⟩ : syracuseStep 283815677 = 106430879) B106430879
theorem B9728381 : Blo 1819611 9728381 := bstep (se 3 (by rfl) ⟨1824071, by rfl⟩ : syracuseStep 9728381 = 3648143) B3648143
theorem B33681919 : Blo 1819611 33681919 := bstep (se 1 (by rfl) ⟨25261439, by rfl⟩ : syracuseStep 33681919 = 50522879) B50522879
theorem B26260199 : Blo 1819611 26260199 := bstep (se 1 (by rfl) ⟨19695149, by rfl⟩ : syracuseStep 26260199 = 39390299) B39390299
theorem B6911999 : Blo 1819611 6911999 := bstep (se 1 (by rfl) ⟨5183999, by rfl⟩ : syracuseStep 6911999 = 10367999) B10367999
theorem B134707535 : Blo 1819611 134707535 := bstep (se 1 (by rfl) ⟨101030651, by rfl⟩ : syracuseStep 134707535 = 202061303) B202061303
theorem B4095143 : Blo 1819611 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B9846107 : Blo 1819611 9846107 := bstep (se 1 (by rfl) ⟨7384580, by rfl⟩ : syracuseStep 9846107 = 14769161) B14769161
theorem B141885407 : Blo 1819611 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B17506799 : Blo 1819611 17506799 := bstep (se 1 (by rfl) ⟨13130099, by rfl⟩ : syracuseStep 17506799 = 26260199) B26260199
theorem B44909225 : Blo 1819611 44909225 := bstep (se 2 (by rfl) ⟨16840959, by rfl⟩ : syracuseStep 44909225 = 33681919) B33681919
theorem B4097519 : Blo 1819611 4097519 := bstep (se 1 (by rfl) ⟨3073139, by rfl⟩ : syracuseStep 4097519 = 6146279) B6146279
theorem B11667563 : Blo 1819611 11667563 := bstep (se 1 (by rfl) ⟨8750672, by rfl⟩ : syracuseStep 11667563 = 17501345) B17501345
theorem B2730095 : Blo 1819611 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B6564071 : Blo 1819611 6564071 := bstep (se 1 (by rfl) ⟨4923053, by rfl⟩ : syracuseStep 6564071 = 9846107) B9846107
theorem B15559411 : Blo 1819611 15559411 := bstep (se 1 (by rfl) ⟨11669558, by rfl⟩ : syracuseStep 15559411 = 23339117) B23339117
theorem B2731007 : Blo 1819611 2731007 := bstep (se 1 (by rfl) ⟨2048255, by rfl⟩ : syracuseStep 2731007 = 4096511) B4096511
theorem B2305255 : Blo 1819611 2305255 := bstep (se 1 (by rfl) ⟨1728941, by rfl⟩ : syracuseStep 2305255 = 3457883) B3457883
theorem B4607999 : Blo 1819611 4607999 := bstep (se 1 (by rfl) ⟨3455999, by rfl⟩ : syracuseStep 4607999 = 6911999) B6911999
theorem B89805023 : Blo 1819611 89805023 := bstep (se 1 (by rfl) ⟨67353767, by rfl⟩ : syracuseStep 89805023 = 134707535) B134707535
theorem B94590271 : Blo 1819611 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B25942349 : Blo 1819611 25942349 := bstep (se 3 (by rfl) ⟨4864190, by rfl⟩ : syracuseStep 25942349 = 9728381) B9728381
theorem B3070703 : Blo 1819611 3070703 := bstep (se 1 (by rfl) ⟨2303027, by rfl⟩ : syracuseStep 3070703 = 4606055) B4606055
theorem B189210451 : Blo 1819611 189210451 := bstep (se 1 (by rfl) ⟨141907838, by rfl⟩ : syracuseStep 189210451 = 283815677) B283815677
theorem B1820063 : Blo 1819611 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B4376047 : Blo 1819611 4376047 := bstep (se 1 (by rfl) ⟨3282035, by rfl⟩ : syracuseStep 4376047 = 6564071) B6564071
theorem B17294899 : Blo 1819611 17294899 := bstep (se 1 (by rfl) ⟨12971174, by rfl⟩ : syracuseStep 17294899 = 25942349) B25942349
theorem B3073673 : Blo 1819611 3073673 := bstep (se 2 (by rfl) ⟨1152627, by rfl⟩ : syracuseStep 3073673 = 2305255) B2305255
theorem B1820671 : Blo 1819611 1820671 := bstep (se 1 (by rfl) ⟨1365503, by rfl⟩ : syracuseStep 1820671 = 2731007) B2731007
theorem B59870015 : Blo 1819611 59870015 := bstep (se 1 (by rfl) ⟨44902511, by rfl⟩ : syracuseStep 59870015 = 89805023) B89805023
theorem B20745881 : Blo 1819611 20745881 := bstep (se 2 (by rfl) ⟨7779705, by rfl⟩ : syracuseStep 20745881 = 15559411) B15559411
theorem B2731679 : Blo 1819611 2731679 := bstep (se 1 (by rfl) ⟨2048759, by rfl⟩ : syracuseStep 2731679 = 4097519) B4097519
theorem B7778375 : Blo 1819611 7778375 := bstep (se 1 (by rfl) ⟨5833781, by rfl⟩ : syracuseStep 7778375 = 11667563) B11667563
theorem B126120361 : Blo 1819611 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B11671199 : Blo 1819611 11671199 := bstep (se 1 (by rfl) ⟨8753399, by rfl⟩ : syracuseStep 11671199 = 17506799) B17506799
theorem B3071999 : Blo 1819611 3071999 := bstep (se 1 (by rfl) ⟨2303999, by rfl⟩ : syracuseStep 3071999 = 4607999) B4607999
theorem B29939483 : Blo 1819611 29939483 := bstep (se 1 (by rfl) ⟨22454612, by rfl⟩ : syracuseStep 29939483 = 44909225) B44909225
theorem B2047135 : Blo 1819611 2047135 := bstep (se 1 (by rfl) ⟨1535351, by rfl⟩ : syracuseStep 2047135 = 3070703) B3070703
theorem B252280601 : Blo 1819611 252280601 := bstep (se 2 (by rfl) ⟨94605225, by rfl⟩ : syracuseStep 252280601 = 189210451) B189210451
theorem B5185583 : Blo 1819611 5185583 := bstep (se 1 (by rfl) ⟨3889187, by rfl⟩ : syracuseStep 5185583 = 7778375) B7778375
theorem B2049115 : Blo 1819611 2049115 := bstep (se 1 (by rfl) ⟨1536836, by rfl⟩ : syracuseStep 2049115 = 3073673) B3073673
theorem B2729513 : Blo 1819611 2729513 := bstep (se 2 (by rfl) ⟨1023567, by rfl⟩ : syracuseStep 2729513 = 2047135) B2047135
theorem B39913343 : Blo 1819611 39913343 := bstep (se 1 (by rfl) ⟨29935007, by rfl⟩ : syracuseStep 39913343 = 59870015) B59870015
theorem B5834729 : Blo 1819611 5834729 := bstep (se 2 (by rfl) ⟨2188023, by rfl⟩ : syracuseStep 5834729 = 4376047) B4376047
theorem B13830587 : Blo 1819611 13830587 := bstep (se 1 (by rfl) ⟨10372940, by rfl⟩ : syracuseStep 13830587 = 20745881) B20745881
theorem B1821119 : Blo 1819611 1821119 := bstep (se 1 (by rfl) ⟨1365839, by rfl⟩ : syracuseStep 1821119 = 2731679) B2731679
theorem B168160481 : Blo 1819611 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B19959655 : Blo 1819611 19959655 := bstep (se 1 (by rfl) ⟨14969741, by rfl⟩ : syracuseStep 19959655 = 29939483) B29939483
theorem B168187067 : Blo 1819611 168187067 := bstep (se 1 (by rfl) ⟨126140300, by rfl⟩ : syracuseStep 168187067 = 252280601) B252280601
theorem B7780799 : Blo 1819611 7780799 := bstep (se 1 (by rfl) ⟨5835599, by rfl⟩ : syracuseStep 7780799 = 11671199) B11671199
theorem B23059865 : Blo 1819611 23059865 := bstep (se 2 (by rfl) ⟨8647449, by rfl⟩ : syracuseStep 23059865 = 17294899) B17294899
theorem B2047999 : Blo 1819611 2047999 := bstep (se 1 (by rfl) ⟨1535999, by rfl⟩ : syracuseStep 2047999 = 3071999) B3071999
theorem B3457055 : Blo 1819611 3457055 := bstep (se 1 (by rfl) ⟨2592791, by rfl⟩ : syracuseStep 3457055 = 5185583) B5185583
theorem B112124711 : Blo 1819611 112124711 := bstep (se 1 (by rfl) ⟨84093533, by rfl⟩ : syracuseStep 112124711 = 168187067) B168187067
theorem B1819675 : Blo 1819611 1819675 := bstep (se 1 (by rfl) ⟨1364756, by rfl⟩ : syracuseStep 1819675 = 2729513) B2729513
theorem B26608895 : Blo 1819611 26608895 := bstep (se 1 (by rfl) ⟨19956671, by rfl⟩ : syracuseStep 26608895 = 39913343) B39913343
theorem B2730665 : Blo 1819611 2730665 := bstep (se 2 (by rfl) ⟨1023999, by rfl⟩ : syracuseStep 2730665 = 2047999) B2047999
theorem B2732153 : Blo 1819611 2732153 := bstep (se 2 (by rfl) ⟨1024557, by rfl⟩ : syracuseStep 2732153 = 2049115) B2049115
theorem B9220391 : Blo 1819611 9220391 := bstep (se 1 (by rfl) ⟨6915293, by rfl⟩ : syracuseStep 9220391 = 13830587) B13830587
theorem B15373243 : Blo 1819611 15373243 := bstep (se 1 (by rfl) ⟨11529932, by rfl⟩ : syracuseStep 15373243 = 23059865) B23059865
theorem B26612873 : Blo 1819611 26612873 := bstep (se 2 (by rfl) ⟨9979827, by rfl⟩ : syracuseStep 26612873 = 19959655) B19959655
theorem B20748797 : Blo 1819611 20748797 := bstep (se 3 (by rfl) ⟨3890399, by rfl⟩ : syracuseStep 20748797 = 7780799) B7780799
theorem B3889819 : Blo 1819611 3889819 := bstep (se 1 (by rfl) ⟨2917364, by rfl⟩ : syracuseStep 3889819 = 5834729) B5834729
theorem B112106987 : Blo 1819611 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B5186425 : Blo 1819611 5186425 := bstep (se 2 (by rfl) ⟨1944909, by rfl⟩ : syracuseStep 5186425 = 3889819) B3889819
theorem B20497657 : Blo 1819611 20497657 := bstep (se 2 (by rfl) ⟨7686621, by rfl⟩ : syracuseStep 20497657 = 15373243) B15373243
theorem B1820443 : Blo 1819611 1820443 := bstep (se 1 (by rfl) ⟨1365332, by rfl⟩ : syracuseStep 1820443 = 2730665) B2730665
theorem B74737991 : Blo 1819611 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B2304703 : Blo 1819611 2304703 := bstep (se 1 (by rfl) ⟨1728527, by rfl⟩ : syracuseStep 2304703 = 3457055) B3457055
theorem B1821435 : Blo 1819611 1821435 := bstep (se 1 (by rfl) ⟨1366076, by rfl⟩ : syracuseStep 1821435 = 2732153) B2732153
theorem B6146927 : Blo 1819611 6146927 := bstep (se 1 (by rfl) ⟨4610195, by rfl⟩ : syracuseStep 6146927 = 9220391) B9220391
theorem B17739263 : Blo 1819611 17739263 := bstep (se 1 (by rfl) ⟨13304447, by rfl⟩ : syracuseStep 17739263 = 26608895) B26608895
theorem B13832531 : Blo 1819611 13832531 := bstep (se 1 (by rfl) ⟨10374398, by rfl⟩ : syracuseStep 13832531 = 20748797) B20748797
theorem B74749807 : Blo 1819611 74749807 := bstep (se 1 (by rfl) ⟨56062355, by rfl⟩ : syracuseStep 74749807 = 112124711) B112124711
theorem B17741915 : Blo 1819611 17741915 := bstep (se 1 (by rfl) ⟨13306436, by rfl⟩ : syracuseStep 17741915 = 26612873) B26612873
theorem B3072937 : Blo 1819611 3072937 := bstep (se 2 (by rfl) ⟨1152351, by rfl⟩ : syracuseStep 3072937 = 2304703) B2304703
theorem B6915233 : Blo 1819611 6915233 := bstep (se 2 (by rfl) ⟨2593212, by rfl⟩ : syracuseStep 6915233 = 5186425) B5186425
theorem B49825327 : Blo 1819611 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B27330209 : Blo 1819611 27330209 := bstep (se 2 (by rfl) ⟨10248828, by rfl⟩ : syracuseStep 27330209 = 20497657) B20497657
theorem B4097951 : Blo 1819611 4097951 := bstep (se 1 (by rfl) ⟨3073463, by rfl⟩ : syracuseStep 4097951 = 6146927) B6146927
theorem B99666409 : Blo 1819611 99666409 := bstep (se 2 (by rfl) ⟨37374903, by rfl⟩ : syracuseStep 99666409 = 74749807) B74749807
theorem B11826175 : Blo 1819611 11826175 := bstep (se 1 (by rfl) ⟨8869631, by rfl⟩ : syracuseStep 11826175 = 17739263) B17739263
theorem B9221687 : Blo 1819611 9221687 := bstep (se 1 (by rfl) ⟨6916265, by rfl⟩ : syracuseStep 9221687 = 13832531) B13832531
theorem B11827943 : Blo 1819611 11827943 := bstep (se 1 (by rfl) ⟨8870957, by rfl⟩ : syracuseStep 11827943 = 17741915) B17741915
theorem B18220139 : Blo 1819611 18220139 := bstep (se 1 (by rfl) ⟨13665104, by rfl⟩ : syracuseStep 18220139 = 27330209) B27330209
theorem B4097249 : Blo 1819611 4097249 := bstep (se 2 (by rfl) ⟨1536468, by rfl⟩ : syracuseStep 4097249 = 3072937) B3072937
theorem B6147791 : Blo 1819611 6147791 := bstep (se 1 (by rfl) ⟨4610843, by rfl⟩ : syracuseStep 6147791 = 9221687) B9221687
theorem B2731967 : Blo 1819611 2731967 := bstep (se 1 (by rfl) ⟨2048975, by rfl⟩ : syracuseStep 2731967 = 4097951) B4097951
theorem B7885295 : Blo 1819611 7885295 := bstep (se 1 (by rfl) ⟨5913971, by rfl⟩ : syracuseStep 7885295 = 11827943) B11827943
theorem B66433769 : Blo 1819611 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B132888545 : Blo 1819611 132888545 := bstep (se 2 (by rfl) ⟨49833204, by rfl⟩ : syracuseStep 132888545 = 99666409) B99666409
theorem B4610155 : Blo 1819611 4610155 := bstep (se 1 (by rfl) ⟨3457616, by rfl⟩ : syracuseStep 4610155 = 6915233) B6915233
theorem B15768233 : Blo 1819611 15768233 := bstep (se 2 (by rfl) ⟨5913087, by rfl⟩ : syracuseStep 15768233 = 11826175) B11826175
theorem B10512155 : Blo 1819611 10512155 := bstep (se 1 (by rfl) ⟨7884116, by rfl⟩ : syracuseStep 10512155 = 15768233) B15768233
theorem B4098527 : Blo 1819611 4098527 := bstep (se 1 (by rfl) ⟨3073895, by rfl⟩ : syracuseStep 4098527 = 6147791) B6147791
theorem B1821311 : Blo 1819611 1821311 := bstep (se 1 (by rfl) ⟨1365983, by rfl⟩ : syracuseStep 1821311 = 2731967) B2731967
theorem B6146873 : Blo 1819611 6146873 := bstep (se 2 (by rfl) ⟨2305077, by rfl⟩ : syracuseStep 6146873 = 4610155) B4610155
theorem B44289179 : Blo 1819611 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B2731499 : Blo 1819611 2731499 := bstep (se 1 (by rfl) ⟨2048624, by rfl⟩ : syracuseStep 2731499 = 4097249) B4097249
theorem B88592363 : Blo 1819611 88592363 := bstep (se 1 (by rfl) ⟨66444272, by rfl⟩ : syracuseStep 88592363 = 132888545) B132888545
theorem B5256863 : Blo 1819611 5256863 := bstep (se 1 (by rfl) ⟨3942647, by rfl⟩ : syracuseStep 5256863 = 7885295) B7885295
theorem B12146759 : Blo 1819611 12146759 := bstep (se 1 (by rfl) ⟨9110069, by rfl⟩ : syracuseStep 12146759 = 18220139) B18220139
theorem B4097915 : Blo 1819611 4097915 := bstep (se 1 (by rfl) ⟨3073436, by rfl⟩ : syracuseStep 4097915 = 6146873) B6146873
theorem B29526119 : Blo 1819611 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B1820999 : Blo 1819611 1820999 := bstep (se 1 (by rfl) ⟨1365749, by rfl⟩ : syracuseStep 1820999 = 2731499) B2731499
theorem B7008103 : Blo 1819611 7008103 := bstep (se 1 (by rfl) ⟨5256077, by rfl⟩ : syracuseStep 7008103 = 10512155) B10512155
theorem B8097839 : Blo 1819611 8097839 := bstep (se 1 (by rfl) ⟨6073379, by rfl⟩ : syracuseStep 8097839 = 12146759) B12146759
theorem B2732351 : Blo 1819611 2732351 := bstep (se 1 (by rfl) ⟨2049263, by rfl⟩ : syracuseStep 2732351 = 4098527) B4098527
theorem B59061575 : Blo 1819611 59061575 := bstep (se 1 (by rfl) ⟨44296181, by rfl⟩ : syracuseStep 59061575 = 88592363) B88592363
theorem B3504575 : Blo 1819611 3504575 := bstep (se 1 (by rfl) ⟨2628431, by rfl⟩ : syracuseStep 3504575 = 5256863) B5256863
theorem B5398559 : Blo 1819611 5398559 := bstep (se 1 (by rfl) ⟨4048919, by rfl⟩ : syracuseStep 5398559 = 8097839) B8097839
theorem B2336383 : Blo 1819611 2336383 := bstep (se 1 (by rfl) ⟨1752287, by rfl⟩ : syracuseStep 2336383 = 3504575) B3504575
theorem B1821567 : Blo 1819611 1821567 := bstep (se 1 (by rfl) ⟨1366175, by rfl⟩ : syracuseStep 1821567 = 2732351) B2732351
theorem B39374383 : Blo 1819611 39374383 := bstep (se 1 (by rfl) ⟨29530787, by rfl⟩ : syracuseStep 39374383 = 59061575) B59061575
theorem B2731943 : Blo 1819611 2731943 := bstep (se 1 (by rfl) ⟨2048957, by rfl⟩ : syracuseStep 2731943 = 4097915) B4097915
theorem B37376549 : Blo 1819611 37376549 := bstep (se 4 (by rfl) ⟨3504051, by rfl⟩ : syracuseStep 37376549 = 7008103) B7008103
theorem B19684079 : Blo 1819611 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B12460709 : Blo 1819611 12460709 := bstep (se 4 (by rfl) ⟨1168191, by rfl⟩ : syracuseStep 12460709 = 2336383) B2336383
theorem B1821295 : Blo 1819611 1821295 := bstep (se 1 (by rfl) ⟨1365971, by rfl⟩ : syracuseStep 1821295 = 2731943) B2731943
theorem B3599039 : Blo 1819611 3599039 := bstep (se 1 (by rfl) ⟨2699279, by rfl⟩ : syracuseStep 3599039 = 5398559) B5398559
theorem B52499177 : Blo 1819611 52499177 := bstep (se 2 (by rfl) ⟨19687191, by rfl⟩ : syracuseStep 52499177 = 39374383) B39374383
theorem B24917699 : Blo 1819611 24917699 := bstep (se 1 (by rfl) ⟨18688274, by rfl⟩ : syracuseStep 24917699 = 37376549) B37376549
theorem B13122719 : Blo 1819611 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B33228557 : Blo 1819611 33228557 := bstep (se 3 (by rfl) ⟨6230354, by rfl⟩ : syracuseStep 33228557 = 12460709) B12460709
theorem B34999451 : Blo 1819611 34999451 := bstep (se 1 (by rfl) ⟨26249588, by rfl⟩ : syracuseStep 34999451 = 52499177) B52499177
theorem B9597437 : Blo 1819611 9597437 := bstep (se 3 (by rfl) ⟨1799519, by rfl⟩ : syracuseStep 9597437 = 3599039) B3599039
theorem B16611799 : Blo 1819611 16611799 := bstep (se 1 (by rfl) ⟨12458849, by rfl⟩ : syracuseStep 16611799 = 24917699) B24917699
theorem B8748479 : Blo 1819611 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B6398291 : Blo 1819611 6398291 := bstep (se 1 (by rfl) ⟨4798718, by rfl⟩ : syracuseStep 6398291 = 9597437) B9597437
theorem B22152371 : Blo 1819611 22152371 := bstep (se 1 (by rfl) ⟨16614278, by rfl⟩ : syracuseStep 22152371 = 33228557) B33228557
theorem B23332967 : Blo 1819611 23332967 := bstep (se 1 (by rfl) ⟨17499725, by rfl⟩ : syracuseStep 23332967 = 34999451) B34999451
theorem B22149065 : Blo 1819611 22149065 := bstep (se 2 (by rfl) ⟨8305899, by rfl⟩ : syracuseStep 22149065 = 16611799) B16611799
theorem B5832319 : Blo 1819611 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B59072989 : Blo 1819611 59072989 := bstep (se 3 (by rfl) ⟨11076185, by rfl⟩ : syracuseStep 59072989 = 22152371) B22152371
theorem B7776425 : Blo 1819611 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B17062109 : Blo 1819611 17062109 := bstep (se 3 (by rfl) ⟨3199145, by rfl⟩ : syracuseStep 17062109 = 6398291) B6398291
theorem B15555311 : Blo 1819611 15555311 := bstep (se 1 (by rfl) ⟨11666483, by rfl⟩ : syracuseStep 15555311 = 23332967) B23332967
theorem B59064173 : Blo 1819611 59064173 := bstep (se 3 (by rfl) ⟨11074532, by rfl⟩ : syracuseStep 59064173 = 22149065) B22149065
theorem B20737133 : Blo 1819611 20737133 := bstep (se 3 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 20737133 = 7776425) B7776425
theorem B11374739 : Blo 1819611 11374739 := bstep (se 1 (by rfl) ⟨8531054, by rfl⟩ : syracuseStep 11374739 = 17062109) B17062109
theorem B39376115 : Blo 1819611 39376115 := bstep (se 1 (by rfl) ⟨29532086, by rfl⟩ : syracuseStep 39376115 = 59064173) B59064173
theorem B78763985 : Blo 1819611 78763985 := bstep (se 2 (by rfl) ⟨29536494, by rfl⟩ : syracuseStep 78763985 = 59072989) B59072989
theorem B10370207 : Blo 1819611 10370207 := bstep (se 1 (by rfl) ⟨7777655, by rfl⟩ : syracuseStep 10370207 = 15555311) B15555311
theorem B26250743 : Blo 1819611 26250743 := bstep (se 1 (by rfl) ⟨19688057, by rfl⟩ : syracuseStep 26250743 = 39376115) B39376115
theorem B13824755 : Blo 1819611 13824755 := bstep (se 1 (by rfl) ⟨10368566, by rfl⟩ : syracuseStep 13824755 = 20737133) B20737133
theorem B7583159 : Blo 1819611 7583159 := bstep (se 1 (by rfl) ⟨5687369, by rfl⟩ : syracuseStep 7583159 = 11374739) B11374739
theorem B52509323 : Blo 1819611 52509323 := bstep (se 1 (by rfl) ⟨39381992, by rfl⟩ : syracuseStep 52509323 = 78763985) B78763985
theorem B6913471 : Blo 1819611 6913471 := bstep (se 1 (by rfl) ⟨5185103, by rfl⟩ : syracuseStep 6913471 = 10370207) B10370207
theorem B9216503 : Blo 1819611 9216503 := bstep (se 1 (by rfl) ⟨6912377, by rfl⟩ : syracuseStep 9216503 = 13824755) B13824755
theorem B5055439 : Blo 1819611 5055439 := bstep (se 1 (by rfl) ⟨3791579, by rfl⟩ : syracuseStep 5055439 = 7583159) B7583159
theorem B35006215 : Blo 1819611 35006215 := bstep (se 1 (by rfl) ⟨26254661, by rfl⟩ : syracuseStep 35006215 = 52509323) B52509323
theorem B9217961 : Blo 1819611 9217961 := bstep (se 2 (by rfl) ⟨3456735, by rfl⟩ : syracuseStep 9217961 = 6913471) B6913471
theorem B17500495 : Blo 1819611 17500495 := bstep (se 1 (by rfl) ⟨13125371, by rfl⟩ : syracuseStep 17500495 = 26250743) B26250743
theorem B6144335 : Blo 1819611 6144335 := bstep (se 1 (by rfl) ⟨4608251, by rfl⟩ : syracuseStep 6144335 = 9216503) B9216503
theorem B6145307 : Blo 1819611 6145307 := bstep (se 1 (by rfl) ⟨4608980, by rfl⟩ : syracuseStep 6145307 = 9217961) B9217961
theorem B23333993 : Blo 1819611 23333993 := bstep (se 2 (by rfl) ⟨8750247, by rfl⟩ : syracuseStep 23333993 = 17500495) B17500495
theorem B46674953 : Blo 1819611 46674953 := bstep (se 2 (by rfl) ⟨17503107, by rfl⟩ : syracuseStep 46674953 = 35006215) B35006215
theorem B6740585 : Blo 1819611 6740585 := bstep (se 2 (by rfl) ⟨2527719, by rfl⟩ : syracuseStep 6740585 = 5055439) B5055439
theorem B4096223 : Blo 1819611 4096223 := bstep (se 1 (by rfl) ⟨3072167, by rfl⟩ : syracuseStep 4096223 = 6144335) B6144335
theorem B4096871 : Blo 1819611 4096871 := bstep (se 1 (by rfl) ⟨3072653, by rfl⟩ : syracuseStep 4096871 = 6145307) B6145307
theorem B31116635 : Blo 1819611 31116635 := bstep (se 1 (by rfl) ⟨23337476, by rfl⟩ : syracuseStep 31116635 = 46674953) B46674953
theorem B4493723 : Blo 1819611 4493723 := bstep (se 1 (by rfl) ⟨3370292, by rfl⟩ : syracuseStep 4493723 = 6740585) B6740585
theorem B15555995 : Blo 1819611 15555995 := bstep (se 1 (by rfl) ⟨11666996, by rfl⟩ : syracuseStep 15555995 = 23333993) B23333993
theorem B20744423 : Blo 1819611 20744423 := bstep (se 1 (by rfl) ⟨15558317, by rfl⟩ : syracuseStep 20744423 = 31116635) B31116635
theorem B2730815 : Blo 1819611 2730815 := bstep (se 1 (by rfl) ⟨2048111, by rfl⟩ : syracuseStep 2730815 = 4096223) B4096223
theorem B2731247 : Blo 1819611 2731247 := bstep (se 1 (by rfl) ⟨2048435, by rfl⟩ : syracuseStep 2731247 = 4096871) B4096871
theorem B11983261 : Blo 1819611 11983261 := bstep (se 3 (by rfl) ⟨2246861, by rfl⟩ : syracuseStep 11983261 = 4493723) B4493723
theorem B10370663 : Blo 1819611 10370663 := bstep (se 1 (by rfl) ⟨7777997, by rfl⟩ : syracuseStep 10370663 = 15555995) B15555995
theorem B13829615 : Blo 1819611 13829615 := bstep (se 1 (by rfl) ⟨10372211, by rfl⟩ : syracuseStep 13829615 = 20744423) B20744423
theorem B1820543 : Blo 1819611 1820543 := bstep (se 1 (by rfl) ⟨1365407, by rfl⟩ : syracuseStep 1820543 = 2730815) B2730815
theorem B1820831 : Blo 1819611 1820831 := bstep (se 1 (by rfl) ⟨1365623, by rfl⟩ : syracuseStep 1820831 = 2731247) B2731247
theorem B15977681 : Blo 1819611 15977681 := bstep (se 2 (by rfl) ⟨5991630, by rfl⟩ : syracuseStep 15977681 = 11983261) B11983261
theorem B6913775 : Blo 1819611 6913775 := bstep (se 1 (by rfl) ⟨5185331, by rfl⟩ : syracuseStep 6913775 = 10370663) B10370663
theorem B10651787 : Blo 1819611 10651787 := bstep (se 1 (by rfl) ⟨7988840, by rfl⟩ : syracuseStep 10651787 = 15977681) B15977681
theorem B9219743 : Blo 1819611 9219743 := bstep (se 1 (by rfl) ⟨6914807, by rfl⟩ : syracuseStep 9219743 = 13829615) B13829615
theorem B4609183 : Blo 1819611 4609183 := bstep (se 1 (by rfl) ⟨3456887, by rfl⟩ : syracuseStep 4609183 = 6913775) B6913775
theorem B6145577 : Blo 1819611 6145577 := bstep (se 2 (by rfl) ⟨2304591, by rfl⟩ : syracuseStep 6145577 = 4609183) B4609183
theorem B6146495 : Blo 1819611 6146495 := bstep (se 1 (by rfl) ⟨4609871, by rfl⟩ : syracuseStep 6146495 = 9219743) B9219743
theorem B7101191 : Blo 1819611 7101191 := bstep (se 1 (by rfl) ⟨5325893, by rfl⟩ : syracuseStep 7101191 = 10651787) B10651787
theorem B4097051 : Blo 1819611 4097051 := bstep (se 1 (by rfl) ⟨3072788, by rfl⟩ : syracuseStep 4097051 = 6145577) B6145577
theorem B4097663 : Blo 1819611 4097663 := bstep (se 1 (by rfl) ⟨3073247, by rfl⟩ : syracuseStep 4097663 = 6146495) B6146495
theorem B4734127 : Blo 1819611 4734127 := bstep (se 1 (by rfl) ⟨3550595, by rfl⟩ : syracuseStep 4734127 = 7101191) B7101191
theorem B2731367 : Blo 1819611 2731367 := bstep (se 1 (by rfl) ⟨2048525, by rfl⟩ : syracuseStep 2731367 = 4097051) B4097051
theorem B2731775 : Blo 1819611 2731775 := bstep (se 1 (by rfl) ⟨2048831, by rfl⟩ : syracuseStep 2731775 = 4097663) B4097663
theorem B6312169 : Blo 1819611 6312169 := bstep (se 2 (by rfl) ⟨2367063, by rfl⟩ : syracuseStep 6312169 = 4734127) B4734127
theorem B1820911 : Blo 1819611 1820911 := bstep (se 1 (by rfl) ⟨1365683, by rfl⟩ : syracuseStep 1820911 = 2731367) B2731367
theorem B1821183 : Blo 1819611 1821183 := bstep (se 1 (by rfl) ⟨1365887, by rfl⟩ : syracuseStep 1821183 = 2731775) B2731775
theorem B33664901 : Blo 1819611 33664901 := bstep (se 4 (by rfl) ⟨3156084, by rfl⟩ : syracuseStep 33664901 = 6312169) B6312169
theorem B359092277 : Blo 1819611 359092277 := bstep (se 5 (by rfl) ⟨16832450, by rfl⟩ : syracuseStep 359092277 = 33664901) B33664901
theorem B239394851 : Blo 1819611 239394851 := bstep (se 1 (by rfl) ⟨179546138, by rfl⟩ : syracuseStep 239394851 = 359092277) B359092277
theorem B159596567 : Blo 1819611 159596567 := bstep (se 1 (by rfl) ⟨119697425, by rfl⟩ : syracuseStep 159596567 = 239394851) B239394851
theorem B106397711 : Blo 1819611 106397711 := bstep (se 1 (by rfl) ⟨79798283, by rfl⟩ : syracuseStep 106397711 = 159596567) B159596567
theorem B70931807 : Blo 1819611 70931807 := bstep (se 1 (by rfl) ⟨53198855, by rfl⟩ : syracuseStep 70931807 = 106397711) B106397711
theorem B47287871 : Blo 1819611 47287871 := bstep (se 1 (by rfl) ⟨35465903, by rfl⟩ : syracuseStep 47287871 = 70931807) B70931807
theorem B31525247 : Blo 1819611 31525247 := bstep (se 1 (by rfl) ⟨23643935, by rfl⟩ : syracuseStep 31525247 = 47287871) B47287871
theorem B21016831 : Blo 1819611 21016831 := bstep (se 1 (by rfl) ⟨15762623, by rfl⟩ : syracuseStep 21016831 = 31525247) B31525247
theorem B28022441 : Blo 1819611 28022441 := bstep (se 2 (by rfl) ⟨10508415, by rfl⟩ : syracuseStep 28022441 = 21016831) B21016831
theorem B74726509 : Blo 1819611 74726509 := bstep (se 3 (by rfl) ⟨14011220, by rfl⟩ : syracuseStep 74726509 = 28022441) B28022441
theorem B99635345 : Blo 1819611 99635345 := bstep (se 2 (by rfl) ⟨37363254, by rfl⟩ : syracuseStep 99635345 = 74726509) B74726509
theorem B66423563 : Blo 1819611 66423563 := bstep (se 1 (by rfl) ⟨49817672, by rfl⟩ : syracuseStep 66423563 = 99635345) B99635345
theorem B44282375 : Blo 1819611 44282375 := bstep (se 1 (by rfl) ⟨33211781, by rfl⟩ : syracuseStep 44282375 = 66423563) B66423563
theorem B29521583 : Blo 1819611 29521583 := bstep (se 1 (by rfl) ⟨22141187, by rfl⟩ : syracuseStep 29521583 = 44282375) B44282375
theorem B19681055 : Blo 1819611 19681055 := bstep (se 1 (by rfl) ⟨14760791, by rfl⟩ : syracuseStep 19681055 = 29521583) B29521583
theorem B13120703 : Blo 1819611 13120703 := bstep (se 1 (by rfl) ⟨9840527, by rfl⟩ : syracuseStep 13120703 = 19681055) B19681055
theorem B8747135 : Blo 1819611 8747135 := bstep (se 1 (by rfl) ⟨6560351, by rfl⟩ : syracuseStep 8747135 = 13120703) B13120703
theorem B5831423 : Blo 1819611 5831423 := bstep (se 1 (by rfl) ⟨4373567, by rfl⟩ : syracuseStep 5831423 = 8747135) B8747135
theorem B3887615 : Blo 1819611 3887615 := bstep (se 1 (by rfl) ⟨2915711, by rfl⟩ : syracuseStep 3887615 = 5831423) B5831423
theorem B10366973 : Blo 1819611 10366973 := bstep (se 3 (by rfl) ⟨1943807, by rfl⟩ : syracuseStep 10366973 = 3887615) B3887615
theorem B6911315 : Blo 1819611 6911315 := bstep (se 1 (by rfl) ⟨5183486, by rfl⟩ : syracuseStep 6911315 = 10366973) B10366973
theorem B4607543 : Blo 1819611 4607543 := bstep (se 1 (by rfl) ⟨3455657, by rfl⟩ : syracuseStep 4607543 = 6911315) B6911315
theorem B3071695 : Blo 1819611 3071695 := bstep (se 1 (by rfl) ⟨2303771, by rfl⟩ : syracuseStep 3071695 = 4607543) B4607543
theorem B4095593 : Blo 1819611 4095593 := bstep (se 2 (by rfl) ⟨1535847, by rfl⟩ : syracuseStep 4095593 = 3071695) B3071695
theorem B2730395 : Blo 1819611 2730395 := bstep (se 1 (by rfl) ⟨2047796, by rfl⟩ : syracuseStep 2730395 = 4095593) B4095593
theorem B1820263 : Blo 1819611 1820263 := bstep (se 1 (by rfl) ⟨1365197, by rfl⟩ : syracuseStep 1820263 = 2730395) B2730395

theorem C0 (j : ℕ) (h1 : 454902 ≤ j) (h2 : j ≤ 455402) : Blo 1819611 (4 * j + 3) := by
  interval_cases j
  · exact B1819611
  · exact B1819615
  · exact B1819619
  · exact B1819623
  · exact B1819627
  · exact B1819631
  · exact B1819635
  · exact B1819639
  · exact B1819643
  · exact B1819647
  · exact B1819651
  · exact B1819655
  · exact B1819659
  · exact B1819663
  · exact B1819667
  · exact B1819671
  · exact B1819675
  · exact B1819679
  · exact B1819683
  · exact B1819687
  · exact B1819691
  · exact B1819695
  · exact B1819699
  · exact B1819703
  · exact B1819707
  · exact B1819711
  · exact B1819715
  · exact B1819719
  · exact B1819723
  · exact B1819727
  · exact B1819731
  · exact B1819735
  · exact B1819739
  · exact B1819743
  · exact B1819747
  · exact B1819751
  · exact B1819755
  · exact B1819759
  · exact B1819763
  · exact B1819767
  · exact B1819771
  · exact B1819775
  · exact B1819779
  · exact B1819783
  · exact B1819787
  · exact B1819791
  · exact B1819795
  · exact B1819799
  · exact B1819803
  · exact B1819807
  · exact B1819811
  · exact B1819815
  · exact B1819819
  · exact B1819823
  · exact B1819827
  · exact B1819831
  · exact B1819835
  · exact B1819839
  · exact B1819843
  · exact B1819847
  · exact B1819851
  · exact B1819855
  · exact B1819859
  · exact B1819863
  · exact B1819867
  · exact B1819871
  · exact B1819875
  · exact B1819879
  · exact B1819883
  · exact B1819887
  · exact B1819891
  · exact B1819895
  · exact B1819899
  · exact B1819903
  · exact B1819907
  · exact B1819911
  · exact B1819915
  · exact B1819919
  · exact B1819923
  · exact B1819927
  · exact B1819931
  · exact B1819935
  · exact B1819939
  · exact B1819943
  · exact B1819947
  · exact B1819951
  · exact B1819955
  · exact B1819959
  · exact B1819963
  · exact B1819967
  · exact B1819971
  · exact B1819975
  · exact B1819979
  · exact B1819983
  · exact B1819987
  · exact B1819991
  · exact B1819995
  · exact B1819999
  · exact B1820003
  · exact B1820007
  · exact B1820011
  · exact B1820015
  · exact B1820019
  · exact B1820023
  · exact B1820027
  · exact B1820031
  · exact B1820035
  · exact B1820039
  · exact B1820043
  · exact B1820047
  · exact B1820051
  · exact B1820055
  · exact B1820059
  · exact B1820063
  · exact B1820067
  · exact B1820071
  · exact B1820075
  · exact B1820079
  · exact B1820083
  · exact B1820087
  · exact B1820091
  · exact B1820095
  · exact B1820099
  · exact B1820103
  · exact B1820107
  · exact B1820111
  · exact B1820115
  · exact B1820119
  · exact B1820123
  · exact B1820127
  · exact B1820131
  · exact B1820135
  · exact B1820139
  · exact B1820143
  · exact B1820147
  · exact B1820151
  · exact B1820155
  · exact B1820159
  · exact B1820163
  · exact B1820167
  · exact B1820171
  · exact B1820175
  · exact B1820179
  · exact B1820183
  · exact B1820187
  · exact B1820191
  · exact B1820195
  · exact B1820199
  · exact B1820203
  · exact B1820207
  · exact B1820211
  · exact B1820215
  · exact B1820219
  · exact B1820223
  · exact B1820227
  · exact B1820231
  · exact B1820235
  · exact B1820239
  · exact B1820243
  · exact B1820247
  · exact B1820251
  · exact B1820255
  · exact B1820259
  · exact B1820263
  · exact B1820267
  · exact B1820271
  · exact B1820275
  · exact B1820279
  · exact B1820283
  · exact B1820287
  · exact B1820291
  · exact B1820295
  · exact B1820299
  · exact B1820303
  · exact B1820307
  · exact B1820311
  · exact B1820315
  · exact B1820319
  · exact B1820323
  · exact B1820327
  · exact B1820331
  · exact B1820335
  · exact B1820339
  · exact B1820343
  · exact B1820347
  · exact B1820351
  · exact B1820355
  · exact B1820359
  · exact B1820363
  · exact B1820367
  · exact B1820371
  · exact B1820375
  · exact B1820379
  · exact B1820383
  · exact B1820387
  · exact B1820391
  · exact B1820395
  · exact B1820399
  · exact B1820403
  · exact B1820407
  · exact B1820411
  · exact B1820415
  · exact B1820419
  · exact B1820423
  · exact B1820427
  · exact B1820431
  · exact B1820435
  · exact B1820439
  · exact B1820443
  · exact B1820447
  · exact B1820451
  · exact B1820455
  · exact B1820459
  · exact B1820463
  · exact B1820467
  · exact B1820471
  · exact B1820475
  · exact B1820479
  · exact B1820483
  · exact B1820487
  · exact B1820491
  · exact B1820495
  · exact B1820499
  · exact B1820503
  · exact B1820507
  · exact B1820511
  · exact B1820515
  · exact B1820519
  · exact B1820523
  · exact B1820527
  · exact B1820531
  · exact B1820535
  · exact B1820539
  · exact B1820543
  · exact B1820547
  · exact B1820551
  · exact B1820555
  · exact B1820559
  · exact B1820563
  · exact B1820567
  · exact B1820571
  · exact B1820575
  · exact B1820579
  · exact B1820583
  · exact B1820587
  · exact B1820591
  · exact B1820595
  · exact B1820599
  · exact B1820603
  · exact B1820607
  · exact B1820611
  · exact B1820615
  · exact B1820619
  · exact B1820623
  · exact B1820627
  · exact B1820631
  · exact B1820635
  · exact B1820639
  · exact B1820643
  · exact B1820647
  · exact B1820651
  · exact B1820655
  · exact B1820659
  · exact B1820663
  · exact B1820667
  · exact B1820671
  · exact B1820675
  · exact B1820679
  · exact B1820683
  · exact B1820687
  · exact B1820691
  · exact B1820695
  · exact B1820699
  · exact B1820703
  · exact B1820707
  · exact B1820711
  · exact B1820715
  · exact B1820719
  · exact B1820723
  · exact B1820727
  · exact B1820731
  · exact B1820735
  · exact B1820739
  · exact B1820743
  · exact B1820747
  · exact B1820751
  · exact B1820755
  · exact B1820759
  · exact B1820763
  · exact B1820767
  · exact B1820771
  · exact B1820775
  · exact B1820779
  · exact B1820783
  · exact B1820787
  · exact B1820791
  · exact B1820795
  · exact B1820799
  · exact B1820803
  · exact B1820807
  · exact B1820811
  · exact B1820815
  · exact B1820819
  · exact B1820823
  · exact B1820827
  · exact B1820831
  · exact B1820835
  · exact B1820839
  · exact B1820843
  · exact B1820847
  · exact B1820851
  · exact B1820855
  · exact B1820859
  · exact B1820863
  · exact B1820867
  · exact B1820871
  · exact B1820875
  · exact B1820879
  · exact B1820883
  · exact B1820887
  · exact B1820891
  · exact B1820895
  · exact B1820899
  · exact B1820903
  · exact B1820907
  · exact B1820911
  · exact B1820915
  · exact B1820919
  · exact B1820923
  · exact B1820927
  · exact B1820931
  · exact B1820935
  · exact B1820939
  · exact B1820943
  · exact B1820947
  · exact B1820951
  · exact B1820955
  · exact B1820959
  · exact B1820963
  · exact B1820967
  · exact B1820971
  · exact B1820975
  · exact B1820979
  · exact B1820983
  · exact B1820987
  · exact B1820991
  · exact B1820995
  · exact B1820999
  · exact B1821003
  · exact B1821007
  · exact B1821011
  · exact B1821015
  · exact B1821019
  · exact B1821023
  · exact B1821027
  · exact B1821031
  · exact B1821035
  · exact B1821039
  · exact B1821043
  · exact B1821047
  · exact B1821051
  · exact B1821055
  · exact B1821059
  · exact B1821063
  · exact B1821067
  · exact B1821071
  · exact B1821075
  · exact B1821079
  · exact B1821083
  · exact B1821087
  · exact B1821091
  · exact B1821095
  · exact B1821099
  · exact B1821103
  · exact B1821107
  · exact B1821111
  · exact B1821115
  · exact B1821119
  · exact B1821123
  · exact B1821127
  · exact B1821131
  · exact B1821135
  · exact B1821139
  · exact B1821143
  · exact B1821147
  · exact B1821151
  · exact B1821155
  · exact B1821159
  · exact B1821163
  · exact B1821167
  · exact B1821171
  · exact B1821175
  · exact B1821179
  · exact B1821183
  · exact B1821187
  · exact B1821191
  · exact B1821195
  · exact B1821199
  · exact B1821203
  · exact B1821207
  · exact B1821211
  · exact B1821215
  · exact B1821219
  · exact B1821223
  · exact B1821227
  · exact B1821231
  · exact B1821235
  · exact B1821239
  · exact B1821243
  · exact B1821247
  · exact B1821251
  · exact B1821255
  · exact B1821259
  · exact B1821263
  · exact B1821267
  · exact B1821271
  · exact B1821275
  · exact B1821279
  · exact B1821283
  · exact B1821287
  · exact B1821291
  · exact B1821295
  · exact B1821299
  · exact B1821303
  · exact B1821307
  · exact B1821311
  · exact B1821315
  · exact B1821319
  · exact B1821323
  · exact B1821327
  · exact B1821331
  · exact B1821335
  · exact B1821339
  · exact B1821343
  · exact B1821347
  · exact B1821351
  · exact B1821355
  · exact B1821359
  · exact B1821363
  · exact B1821367
  · exact B1821371
  · exact B1821375
  · exact B1821379
  · exact B1821383
  · exact B1821387
  · exact B1821391
  · exact B1821395
  · exact B1821399
  · exact B1821403
  · exact B1821407
  · exact B1821411
  · exact B1821415
  · exact B1821419
  · exact B1821423
  · exact B1821427
  · exact B1821431
  · exact B1821435
  · exact B1821439
  · exact B1821443
  · exact B1821447
  · exact B1821451
  · exact B1821455
  · exact B1821459
  · exact B1821463
  · exact B1821467
  · exact B1821471
  · exact B1821475
  · exact B1821479
  · exact B1821483
  · exact B1821487
  · exact B1821491
  · exact B1821495
  · exact B1821499
  · exact B1821503
  · exact B1821507
  · exact B1821511
  · exact B1821515
  · exact B1821519
  · exact B1821523
  · exact B1821527
  · exact B1821531
  · exact B1821535
  · exact B1821539
  · exact B1821543
  · exact B1821547
  · exact B1821551
  · exact B1821555
  · exact B1821559
  · exact B1821563
  · exact B1821567
  · exact B1821571
  · exact B1821575
  · exact B1821579
  · exact B1821583
  · exact B1821587
  · exact B1821591
  · exact B1821595
  · exact B1821599
  · exact B1821603
  · exact B1821607
  · exact B1821611

theorem solution (m : ℕ) (hlo : 1819611 ≤ m) (hhi : m ≤ 1821611) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 454902 ≤ j := by omega
    have hj2 : j ≤ 455402 := by omega
    have hb : Blo 1819611 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
